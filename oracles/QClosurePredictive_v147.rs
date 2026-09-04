#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Q { n: i128, d: i128 }
fn gcd(mut a: i128, mut b: i128) -> i128 { a = a.abs(); b = b.abs(); while b != 0 { let r = a % b; a = b; b = r; } a.max(1) }
impl Q {
    fn new(n: i128, d: i128) -> Self { assert!(d != 0); let g = gcd(n, d); let s = if d < 0 { -1 } else { 1 }; Self { n: s*n/g, d: s*d/g } }
    fn add(self, o: Self) -> Self { Q::new(self.n*o.d + o.n*self.d, self.d*o.d) }
    fn sub(self, o: Self) -> Self { Q::new(self.n*o.d - o.n*self.d, self.d*o.d) }
    fn mul(self, o: Self) -> Self { Q::new(self.n*o.n, self.d*o.d) }
    fn div(self, o: Self) -> Self { Q::new(self.n*o.d, self.d*o.n) }
}
fn sq(x: Q) -> Q { x.mul(x) }
fn fourth(x: Q) -> Q { sq(sq(x)) }
fn num(mask: &[usize], a: &[Q], x: &[Q], b: Q) -> Q { mask.iter().fold(Q::new(0,1), |s,&i| s.add(a[i].mul(sq(x[i])))).sub(b) }
fn den(mask: &[usize], x: &[Q]) -> Q { mask.iter().fold(Q::new(0,1), |s,&i| s.add(fourth(x[i]))) }
fn lt(a: Q,b:Q)->bool { a.n*b.d < b.n*a.d }
fn le(a: Q,b:Q)->bool { a.n*b.d <= b.n*a.d }
fn gt(a: Q,b:Q)->bool { a.n*b.d > b.n*a.d }
fn run(mask: Vec<usize>, a:&[Q], x:&[Q], b:Q, steps:usize)->(Q,Vec<usize>,usize){
    let n=num(&mask,a,x,b); let d=den(&mask,x); let mu=if gt(n,Q::new(0,1))&&gt(d,Q::new(0,1)){n.div(d)}else{Q::new(0,1)};
    let bad=mask.iter().copied().find(|&i|lt(a[i].sub(mu.mul(sq(x[i]))),Q::new(0,1)));
    match bad { None=>(mu,mask,steps), Some(i)=>{
        let reduced:Vec<usize>=mask.into_iter().filter(|&j|j!=i).collect(); let n2=num(&reduced,a,x,b); let d2=den(&reduced,x);
        let y=a[i].mul(sq(x[i])); let z=fourth(x[i]); assert!(gt(n,Q::new(0,1))&&gt(d,Q::new(0,1))&&gt(d2,Q::new(0,1))&&gt(n2,Q::new(0,1))&&lt(y.mul(d),n.mul(z)));
        let mu2=n2.div(d2); assert!(lt(mu,mu2)); run(reduced,a,x,b,steps+1)
    }}
}
fn vectors(n:usize)->Vec<Vec<Q>>{if n==0{vec![vec![]]}else{let mut out=Vec::new();for p in vectors(n-1){for q in [Q::new(0,1),Q::new(1,1),Q::new(2,1)]{let mut v=p.clone();v.push(q);out.push(v)}}out}}
fn main(){for n in 1..=4{for a in vectors(n){for x in vectors(n){for bi in 0..=4{let b=Q::new(bi,1);let mask:(Vec<usize>)=(0..n).collect();let (mu,active,steps)=run(mask,&a,&x,b,0);assert!(steps<=n);for &i in &active{assert!(le(Q::new(0,1),a[i].sub(mu.mul(sq(x[i])))));}for i in 0..n{if !active.contains(&i){assert!(le(a[i].sub(mu.mul(sq(x[i]))),Q::new(0,1)));}}}}}}
println!("rust-q-finite-fuel=PASS");println!("rust-q-terminal-signs=PASS");println!("rust-q-multiplier-monotonicity=PASS");println!("rust-q-terminal-kkt-prescriptive=PASS");println!("rust-bridge-bounded=PASS");println!("rust-theorem-bounded=PASS");println!("rust-conjecture-falsification=PASS");}
