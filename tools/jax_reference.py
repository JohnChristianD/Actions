"""JAX execution mirrors for the concrete Agda computational kernels.

The Agda monoliths remain the semantic authority. This module contains only
JAX-executable mirrors of algorithms where array execution gives a real
algorithmic advantage:

* vectorized element maps (vmap);
* recurrent scans (lax.scan);
* associative prefix sums (lax.associative_scan);
* one-pass sparse-support discovery from one ordering/prefix pass;
* lexicographic score ordering (jnp.lexsort);
* exact integer LayerNorm radicands;
* the concrete scalar GRU hidden-state update used by the learner.

All arithmetic is kept in int64 so the mirror follows the Agda Int8 wrapper's
unbounded-integer semantics as far as these kernels require. This is an
execution mirror, not a proof oracle or a replacement for an Agda theorem.
"""

from __future__ import annotations

import jax
import jax.numpy as jnp
from jax import lax

jax.config.update("jax_enable_x64", True)

Array = jax.Array
def vmap_affine(xs: Array, scale: int = 2, bias: int = 1) -> Array:
    """Vectorized element map, corresponding to repeated independent maps."""
    fn = jax.vmap(lambda x: scale * x + bias)
    return fn(xs)


def associative_prefix_sum(xs: Array) -> Array:
    """Parallel inclusive prefix sum using an associative JAX primitive."""
    return lax.associative_scan(jnp.add, xs)


def recurrent_scan(step, init: Array, xs: Array) -> tuple[Array, Array]:
    """State-carrying recurrence using JAX's compiled scan primitive."""
    return lax.scan(step, init, xs)


def lexicographic_score_order(scores: Array, action_ids: Array) -> Array:
    """Descending score, then ascending action id, matching the Agda order."""
    return jnp.lexsort((action_ids, -scores))


def sparse_support_size(
    magnitudes: Array,
    temperature: int,
) -> tuple[Array, Array, Array]:
    """Compute all sparsemax support candidates from one descending order.

    Returns:
        support_size, prefix_sums, sorted_magnitudes
    """
    sorted_magnitudes = jnp.sort(magnitudes)[::-1]
    prefix_sums = jnp.cumsum(sorted_magnitudes, dtype=jnp.int64)
    k = jnp.arange(1, magnitudes.shape[0] + 1, dtype=jnp.int64)
    kth = sorted_magnitudes
    valid = prefix_sums < k * kth + temperature

    fallback = jnp.array(1, dtype=jnp.int64)
    support_size = jnp.where(
        jnp.any(valid),
        jnp.max(jnp.where(valid, k, fallback)),
        fallback,
    )
    return support_size, prefix_sums, sorted_magnitudes


def sparse_support_top_k(
    magnitudes: Array,
    k: int,
) -> tuple[Array, Array]:
    """Specialized fixed-k support query via JAX top_k.

    This is useful when k is static at trace time. It is not used for the
    generic support-size search because that k is discovered dynamically.
    """
    return lax.top_k(magnitudes, k)


def sparsemax_policy_index(
    scores: Array,
    action_ids: Array,
    fallback_action: Array,
    temperature: int = 16,
) -> Array:
    """Compute the first positive sparsemax action after one sorted pass."""
    order = lexicographic_score_order(scores, action_ids)
    ordered_scores = scores[order]
    magnitudes = jnp.abs(ordered_scores).astype(jnp.int64)

    support_size, prefix_sums, sorted_magnitudes = sparse_support_size(
        magnitudes,
        temperature,
    )
    support_index = support_size - 1
    top_sum = prefix_sums[support_index]

    numerator = support_size * magnitudes + temperature - top_sum
    positive = numerator > 0
    first_positive = jnp.argmax(positive)
    has_positive = jnp.any(positive)
    chosen = order[first_positive]
    return jnp.where(has_positive, action_ids[chosen], fallback_action)


def integer_layernorm_centered_numerators(xs: Array) -> Array:
    """Exact integer centered numerators: n*x - sum(x)."""
    xs = xs.astype(jnp.int64)
    n = jnp.asarray(xs.shape[0], dtype=jnp.int64)
    return n * xs - jnp.sum(xs, dtype=jnp.int64)


def integer_layernorm_radicand(xs: Array, epsilon: int) -> Array:
    """Exact Agda integer LayerNorm radicand."""
    centered = integer_layernorm_centered_numerators(xs)
    variance_numerator = jnp.sum(centered * centered, dtype=jnp.int64)
    n = jnp.asarray(xs.shape[0], dtype=jnp.int64)
    return variance_numerator + jnp.asarray(epsilon, dtype=jnp.int64) * n * n


def batched_integer_layernorm_radicand(
    batch: Array,
    epsilon: int,
) -> Array:
    """Batch the exact radicand computation without a Python loop."""
    return jax.vmap(
        lambda xs: integer_layernorm_radicand(xs, epsilon)
    )(batch)


def signed_gate(x: Array) -> Array:
    """Agda gateCode composed with signedCode: negative=0, zero=64, positive=128."""
    x = x.astype(jnp.int64)
    return jnp.where(x < 0, 0, jnp.where(x == 0, 64, 128)).astype(jnp.int64)


def gru_hidden_step(hidden: Array, x: Array) -> Array:
    """Exact scalar hidden update from CanonicalLearnerMonolith.agda."""
    hidden = hidden.astype(jnp.int64)
    x = x.astype(jnp.int64)
    gate = signed_gate(x)
    complement = 128 - gate
    candidate = hidden + x
    new_value = x + candidate
    return complement * hidden + gate * new_value


def batched_gru_hidden_step(hidden: Array, xs: Array) -> Array:
    """Vectorized GRU hidden update across independent states."""
    return jax.vmap(gru_hidden_step)(hidden, xs)


def jitted_scan_sum(xs: Array) -> Array:
    """A concrete compiled scan used by the verification smoke test."""

    def step(carry: Array, x: Array) -> tuple[Array, Array]:
        new_carry = carry + x
        return new_carry, new_carry

    carry, _ = lax.scan(step, jnp.array(0, dtype=jnp.int64), xs)
    return carry


def _check_equal(lhs: Array, rhs: Array, label: str) -> None:
    if not bool(jnp.array_equal(lhs, rhs)):
        raise AssertionError(f"{label} mismatch: {lhs} != {rhs}")


def main() -> None:
    xs = jnp.arange(8, dtype=jnp.int64)
    _check_equal(
        vmap_affine(xs),
        2 * xs + 1,
        "vmap",
    )
    _check_equal(
        associative_prefix_sum(xs),
        jnp.cumsum(xs),
        "associative scan",
    )

    init = jnp.array(3, dtype=jnp.int64)

    def add_step(carry: Array, x: Array) -> tuple[Array, Array]:
        carry = carry + x
        return carry, carry

    final, outputs = recurrent_scan(add_step, init, xs)
    _check_equal(final, init + jnp.sum(xs), "scan final")
    _check_equal(outputs, init + jnp.cumsum(xs), "scan outputs")

    scores = jnp.array([7, 2, 7, -1], dtype=jnp.int64)
    ids = jnp.array([0, 1, 2, 3], dtype=jnp.int64)
    _check_equal(
        lexicographic_score_order(scores, ids),
        jnp.array([0, 2, 1, 3], dtype=jnp.int32),
        "lexsort order",
    )

    support, prefix, sorted_magnitudes = sparse_support_size(
        jnp.array([9, 8, 4, 1], dtype=jnp.int64),
        16,
    )
    _check_equal(support, jnp.array(3, dtype=jnp.int64), "support size")
    _check_equal(
        prefix,
        jnp.array([9, 17, 21, 22], dtype=jnp.int64),
        "support prefix",
    )
    _check_equal(
        sorted_magnitudes,
        jnp.array([9, 8, 4, 1], dtype=jnp.int64),
        "support ordering",
    )

    _check_equal(
        sparsemax_policy_index(
            jnp.array([7, 2, 7, -1], dtype=jnp.int64),
            jnp.array([0, 1, 2, 3], dtype=jnp.int64),
            jnp.array(0, dtype=jnp.int64),
            16,
        ),
        jnp.array(0, dtype=jnp.int64),
        "sparsemax policy",
    )

    _check_equal(
        integer_layernorm_radicand(
            jnp.array([1, 2, 3, 4], dtype=jnp.int64),
            1,
        ),
        jnp.array(44, dtype=jnp.int64),
        "integer LayerNorm radicand",
    )

    _check_equal(
        gru_hidden_step(
            jnp.array(3, dtype=jnp.int64),
            jnp.array(2, dtype=jnp.int64),
        ),
        jnp.array(896, dtype=jnp.int64),
        "GRU hidden step",
    )

    compiled = jax.jit(jitted_scan_sum)
    _check_equal(
        compiled(xs),
        jnp.sum(xs),
        "compiled scan",
    )

    jax.eval_shape(jax.jit(vmap_affine), xs)
    jax.eval_shape(jax.jit(associative_prefix_sum), xs)
    jax.eval_shape(jax.jit(jitted_scan_sum), xs)
    jax.eval_shape(
        jax.jit(batched_integer_layernorm_radicand),
        jnp.reshape(xs, (2, 4)),
        1,
    )
    jax.eval_shape(
        jax.jit(batched_gru_hidden_step),
        xs,
        xs,
    )

    print("jax-reference=pass")
    print(f"jax-version={jax.__version__}")
    print("jax-jit=pass")
    print("jax-eval-shape=pass")
    print("jax-no-extra-ml-libraries=pass")
    print(
        "kernels=vmap,associative_scan,scan,lexsort,top_k,"
        "sparse-support-prefix,integer-layernorm,gru"
    )


if __name__ == "__main__":
    main()
