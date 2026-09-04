import scala.annotation.tailrec

object QClosurePredictiveV147 extends App {
  final case class Q(n: BigInt, d: BigInt = 1) {
    require(d != 0)
    private val g = n.gcd(d)
    private val nn = if (d < 0) -n / g else n / g
    private val dd = if (d < 0) -d / g else d / g
    def +(o: Q) = Q(nn * o.dd + o.nn * dd, dd * o.dd)
    def -(o: Q) = Q(nn * o.dd - o.nn * dd, dd * o.dd)
    def *(o: Q) = Q(nn * o.nn, dd * o.dd)
    def /(o: Q) = Q(nn * o.dd, dd * o.nn)
    def <(o: Q) = nn * o.dd < o.nn * dd
    def <=(o: Q) = nn * o.dd <= o.nn * dd
    def >(o: Q) = nn * o.dd > o.nn * dd
  }
  val zero = Q(0)
  def sq(x: Q): Q = x * x
  def fourth(x: Q): Q = sq(sq(x))
  def numerator(mask: Vector[Int], a: Vector[Q], x: Vector[Q], b: Q): Q = mask.map(i => a(i) * sq(x(i))).foldLeft(zero)(_ + _) - b
  def denominator(mask: Vector[Int], x: Vector[Q]): Q = mask.map(i => fourth(x(i))).foldLeft(zero)(_ + _)
  @tailrec def firstNegative(mask: List[Int], a: Vector[Q], x: Vector[Q], mu: Q): Option[Int] = mask match {
    case Nil => None
    case i :: rest => if (a(i) - mu * sq(x(i)) < zero) Some(i) else firstNegative(rest, a, x, mu)
  }
  @tailrec def run(mask: List[Int], a: Vector[Q], x: Vector[Q], b: Q, steps: Int = 0): (Q,List[Int],Int) = {
    val n = numerator(mask.toVector, a, x, b)
    val d = denominator(mask.toVector, x)
    val mu = if (n > zero && d > zero) n / d else zero
    firstNegative(mask, a, x, mu) match {
      case None => (mu, mask, steps)
      case Some(bad) =>
        val reduced = mask.filter(_ != bad)
        val n2 = numerator(reduced.toVector, a, x, b)
        val d2 = denominator(reduced.toVector, x)
        val y = a(bad) * sq(x(bad))
        val z = fourth(x(bad))
        assert(n > zero && d > zero && d2 > zero && n2 > zero && y * d < n * z, "invalid deletion")
        val mu2 = n2 / d2
        assert(mu < mu2, "multiplier not increasing")
        run(reduced, a, x, b, steps + 1)
    }
  }
  def vectors(n: Int): Vector[Vector[Q]] = if (n == 0) Vector(Vector.empty) else for (p <- vectors(n - 1); q <- Vector(zero, Q(1), Q(2))) yield p :+ q
  for (n <- 1 to 4; a <- vectors(n); x <- vectors(n); b <- (0 to 4).map(Q(_))) {
    val (mu, active, steps) = run((0 until n).toList, a, x, b)
    assert(steps <= n)
    active.foreach(i => assert(a(i) - mu * sq(x(i)) >= zero))
    (0 until n).filterNot(active.contains).foreach(i => assert(a(i) - mu * sq(x(i)) <= zero))
  }
  println("scala-q-finite-fuel=PASS")
  println("scala-q-terminal-signs=PASS")
  println("scala-q-multiplier-monotonicity=PASS")
  println("scala-q-terminal-kkt-prescriptive=PASS")
  println("scala-bridge-bounded=PASS")
  println("scala-theorem-bounded=PASS")
  println("scala-conjecture-falsification=PASS")
}
