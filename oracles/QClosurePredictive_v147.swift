import Foundation

struct Q: Comparable, Equatable, CustomStringConvertible {
    let n: Int64
    let d: Int64
    init(_ n: Int64, _ d: Int64 = 1) {
        precondition(d != 0)
        let s: Int64 = d < 0 ? -1 : 1
        let nn = n * s
        let dd = d * s
        let g = Q.gcd(abs(nn), abs(dd))
        self.n = nn / g
        self.d = dd / g
    }
    static func gcd(_ a: Int64, _ b: Int64) -> Int64 { if b == 0 { return a == 0 ? 1 : a }; return gcd(b, a % b) }
    static let zero = Q(0)
    static let one = Q(1)
    static prefix func - (x: Q) -> Q { Q(-x.n, x.d) }
    static func + (a: Q, b: Q) -> Q { Q(a.n * b.d + b.n * a.d, a.d * b.d) }
    static func - (a: Q, b: Q) -> Q { a + (-b) }
    static func * (a: Q, b: Q) -> Q { Q(a.n * b.n, a.d * b.d) }
    static func / (a: Q, b: Q) -> Q { precondition(b.n != 0); return Q(a.n * b.d, a.d * b.n) }
    static func < (a: Q, b: Q) -> Bool { a.n * b.d < b.n * a.d }
    var description: String { "\(n)/\(d)" }
}

struct Step { let beforeMu: Q; let afterMu: Q; let n: Q; let d: Q; let y: Q; let z: Q; let nAfter: Q; let dAfter: Q }
struct Result { let multiplier: Q; let mask: [Int]; let steps: [Step] }
func square(_ x: Q) -> Q { x * x }
func fourth(_ x: Q) -> Q { square(square(x)) }
func sum(_ xs: [Q]) -> Q { switch xs.first { case .none: return .zero; case let .some(h): return h + sum(Array(xs.dropFirst())) } }
func numerator(_ mask: [Int], _ alpha: [Q], _ x: [Q], _ budget: Q) -> Q { sum(mask.map { alpha[$0] * square(x[$0]) }) - budget }
func denominator(_ mask: [Int], _ x: [Q]) -> Q { sum(mask.map { fourth(x[$0]) }) }
func firstNegative(_ mask: [Int], _ alpha: [Q], _ x: [Q], _ mu: Q) -> Int? { switch mask.first { case .none: return nil; case let .some(i): let r = alpha[i] - mu * square(x[i]); return r < .zero ? i : firstNegative(Array(mask.dropFirst()), alpha, x, mu) } }
func remove(_ mask: [Int], _ i: Int) -> [Int] { switch mask.first { case .none: return []; case let .some(h): return h == i ? Array(mask.dropFirst()) : [h] + remove(Array(mask.dropFirst()), i) } }
func run(_ mask: [Int], _ alpha: [Q], _ x: [Q], _ budget: Q, _ trace: [Step]) -> Result { let n = numerator(mask, alpha, x, budget); let d = denominator(mask, x); let mu = (n > .zero && d > .zero) ? n / d : .zero; guard let bad = firstNegative(mask, alpha, x, mu) else { return Result(multiplier: mu, mask: mask, steps: trace) }; let reduced = remove(mask, bad); let n2 = numerator(reduced, alpha, x, budget); let d2 = denominator(reduced, x); let y = alpha[bad] * square(x[bad]); let z = fourth(x[bad]); precondition(n > .zero && d > .zero && d2 > .zero && n2 > .zero && y * d < n * z); let mu2 = n2 / d2; precondition(mu < mu2); let step = Step(beforeMu: mu, afterMu: mu2, n: n, d: d, y: y, z: z, nAfter: n2, dAfter: d2); return run(reduced, alpha, x, budget, trace + [step]) }
func verifyTerminal(_ r: Result, _ alpha: [Q], _ x: [Q]) { precondition(r.steps.count <= alpha.count); let active = Set(r.mask); r.mask.forEach { i in precondition(alpha[i] - r.multiplier * square(x[i]) >= .zero) }; let inactive = (0..<alpha.count).filter { !active.contains($0) }; inactive.forEach { i in precondition(alpha[i] - r.multiplier * square(x[i]) <= .zero) }; let kkt = alpha.indices.map { i in active.contains(i) ? max(.zero, alpha[i] - r.multiplier * square(x[i])) : .zero }; kkt.indices.forEach { i in let residual = alpha[i] - r.multiplier * square(x[i]); precondition(kkt[i] == max(.zero, residual)) } }
func allVectors(_ alphabet: [Q], _ n: Int) -> [[Q]] { if n == 0 { return [[]] }; return allVectors(alphabet, n - 1).flatMap { prefix in alphabet.map { prefix + [$0] } } }
func budgets(_ i: Int, _ end: Int) -> [Q] { if i > end { return [] }; return [Q(Int64(i))] + budgets(i + 1, end) }
func checkDimension(_ n: Int) { let vectors = allVectors([.zero, .one, Q(2)], n); let budgetsToTest = budgets(0, 4); vectors.forEach { alpha in vectors.forEach { x in budgetsToTest.forEach { b in if alpha.contains(where: { $0 < .zero }) { return }; let r = run(Array(0..<n), alpha, x, b, []); verifyTerminal(r, alpha, x) } } } }
func main(_ n: Int) { if n == 0 { return }; checkDimension(n); main(n - 1) }
main(4)
print("qRun-terminal-kkt-prescriptive=PASS")
print("qRun-reduced-denominator-numerator-positive=PASS")
print("qRun-multiplier-monotonicity=PASS")
print("qRun-finite-fuel=PASS")
print("qRun-terminal-signs=PASS")
