import kotlin.math.exp
import kotlin.math.tanh

fun sig(z: Double) = 1.0 / (1.0 + exp(-z))
fun lstm(x: Double, h: Double, c: Double): Pair<Double, Double> {
    val z = x + h
    val f = sig(z); val i = sig(z); val o = sig(z); val g = tanh(z)
    val c2 = f * c + i * g
    return Pair(o * tanh(c2), c2)
}
fun gru(x: Double, h: Double): Double {
    val z = sig(x + h); val r = sig(x + h)
    val n = tanh(x + r * h)
    return (1.0 - z) * n + z * h
}
fun main() {
    listOf(Triple(0.2,-0.1,0.3), Triple(1.0,0.2,-0.4), Triple(-0.7,0.5,0.1)).forEach { (x,h,c) ->
        val (lh,lc) = lstm(x,h,c); val gh = gru(x,h)
        println("%.10f,%.10f,%.10f,%.10f,%.10f,%.10f".format(x,h,c,lh,lc,gh))
    }
}
