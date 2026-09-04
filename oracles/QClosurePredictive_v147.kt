import java.math.BigInteger

data class Q(val n: BigInteger, val d: BigInteger = BigInteger.ONE) : Comparable<Q> {
    init { require(d != BigInteger.ZERO) }
    private fun norm(): Q { val sign = if (d.signum() < 0) BigInteger.valueOf(-1) else BigInteger.ONE; val nn = n.multiply(sign); val dd = d.multiply(sign); val g = nn.abs().gcd(dd.abs()); return Q(nn.divide(g), dd.divide(g)) }
    fun plus(o: Q) = Q(n.multiply(o.d).add(o.n.multiply(d)), d.multiply(o.d)).norm()
    fun neg() = Q(n.negate(), d)
    fun minus(o: Q) = plus(o.neg())
    fun times(o: Q) = Q(n.multiply(o.n), d.multiply(o.d)).norm()
    fun div(o: Q) = Q(n.multiply(o.d), d.multiply(o.n)).norm()
    override fun compareTo(other: Q) = n.multiply(other.d).compareTo(other.n.multiply(d))
    companion object { val Z = Q(BigInteger.ZERO); val O = Q(BigInteger.ONE) }
}

data class Step(val before: Q, val after: Q, val n: Q, val d: Q, val y: Q, val z: Q, val n2: Q, val d2: Q)
data class Result(val mu: Q, val mask: List<Int>, val steps: List<Step>)
fun sq(x: Q)=x.times(x)
fun fourth(x: Q)=sq(sq(x))
fun sum(xs: List<Q>): Q = if (xs.isEmpty()) Q.Z else xs.first().plus(sum(xs.drop(1)))
fun numerator(mask: List<Int>, a: List<Q>, x: List<Q>, b: Q)=sum(mask.map{a[it].times(sq(x[it]))}).minus(b)
fun denominator(mask: List<Int>, x: List<Q>)=sum(mask.map{fourth(x[it])})
fun firstNegative(mask: List<Int>, a: List<Q>, x: List<Q>, mu: Q): Int? { if (mask.isEmpty()) return null; val i=mask.first(); return if (a[i].minus(mu.times(sq(x[i]))) < Q.Z) i else firstNegative(mask.drop(1),a,x,mu) }
fun removeMask(mask: List<Int>, i: Int): List<Int> = if (mask.isEmpty()) emptyList() else if (mask.first()==i) mask.drop(1) else listOf(mask.first()) + removeMask(mask.drop(1),i)
fun run(mask: List<Int>, a: List<Q>, x: List<Q>, b: Q, trace: List<Step>): Result { val n=numerator(mask,a,x,b); val d=denominator(mask,x); val mu=if(n>Q.Z && d>Q.Z)n.div(d) else Q.Z; val bad=firstNegative(mask,a,x,mu) ?: return Result(mu,mask,trace); val r=removeMask(mask,bad); val n2=numerator(r,a,x,b); val d2=denominator(r,x); val y=a[bad].times(sq(x[bad])); val z=fourth(x[bad]); require(n>Q.Z && d>Q.Z && d2>Q.Z && n2>Q.Z && y.times(d) < n.times(z)); val mu2=n2.div(d2); require(mu<mu2); return run(r,a,x,b,trace + Step(mu,mu2,n,d,y,z,n2,d2)) }
fun vectors(alphabet: List<Q>, n: Int): List<List<Q>> = if(n==0) listOf(emptyList()) else vectors(alphabet,n-1).flatMap{p->alphabet.map{p+listOf(it)}}
fun budgets(i:Int,last:Int):List<Q> = if(i>last) emptyList() else listOf(Q(BigInteger.valueOf(i.toLong())))+budgets(i+1,last)
fun verifyDimension(n:Int){ val vs=vectors(listOf(Q.Z,Q.O,Q(BigInteger.valueOf(2))),n); vs.forEach{a->vs.forEach{x->budgets(0,4).forEach{b-> val r=run((0 until n).toList(),a,x,b,emptyList()); require(r.steps.size<=n); val active=r.mask.toSet(); active.forEach{i->require(a[i].minus(r.mu.times(sq(x[i])))>=Q.Z)}; (0 until n).filter{it !in active}.forEach{i->require(a[i].minus(r.mu.times(sq(x[i])))<=Q.Z)} }}} }
fun main(){ verifyDimension(1); verifyDimension(2); verifyDimension(3); verifyDimension(4); println("qRun-terminal-kkt-prescriptive=PASS"); println("qRun-reduced-denominator-numerator-positive=PASS"); println("qRun-multiplier-monotonicity=PASS"); println("qRun-finite-fuel=PASS"); println("qRun-terminal-signs=PASS") }
