import Foundation

func sig(_ z: Double) -> Double { 1.0 / (1.0 + exp(-z)) }
func lstm(_ x: Double, _ h: Double, _ c: Double) -> (Double, Double) {
    let z = x + h
    let f = sig(z), i = sig(z), o = sig(z), g = tanh(z)
    let c2 = f * c + i * g
    return (o * tanh(c2), c2)
}
func gru(_ x: Double, _ h: Double) -> Double {
    let z = sig(x + h), r = sig(x + h)
    let n = tanh(x + r * h)
    return (1.0 - z) * n + z * h
}

[(0.2,-0.1,0.3),(1.0,0.2,-0.4),(-0.7,0.5,0.1)].forEach { x,h,c in
    let (lh,lc) = lstm(x,h,c); let gh = gru(x,h)
    print(String(format: "%.10f,%.10f,%.10f,%.10f,%.10f,%.10f", x,h,c,lh,lc,gh))
}
