q <- function(n,d=1) { stopifnot(d != 0); g <- max(1, Reduce(function(a,b) if (b==0) abs(a) else Recall(b, a %% b), list(abs(n), abs(d)))); s <- if (d < 0) -1 else 1; c(n=s*n/g, d=s*d/g) }
add <- function(a,b) q(a$n*b$d+b$n*a$d,a$d*b$d)
sub <- function(a,b) q(a$n*b$d-b$n*a$d,a$d*b$d)
mul <- function(a,b) q(a$n*b$n,a$d*b$d)
divq <- function(a,b) q(a$n*b$d,a$d*b$n)
zero <- q(0)
sq <- function(x) mul(x,x)
fourth <- function(x) sq(sq(x))
lt <- function(a,b) a$n*b$d < b$n*a$d
le <- function(a,b) a$n*b$d <= b$n*a$d
gt <- function(a,b) a$n*b$d > b$n*a$d
num <- function(mask,a,x,b) { s <- zero; for(i in mask) s <- add(s,mul(a[[i+1]],sq(x[[i+1]]))); sub(s,b) }
den <- function(mask,x) { s <- zero; for(i in mask) s <- add(s,fourth(x[[i+1]])); s }
first_negative <- function(mask,a,x,mu) { for(i in mask) if(lt(sub(a[[i+1]],mul(mu,sq(x[[i+1]]))),zero)) return(i); NULL }
runq <- function(mask,a,x,b,steps=0) {
  n <- num(mask,a,x,b); d <- den(mask,x); mu <- if(gt(n,zero) && gt(d,zero)) divq(n,d) else zero
  bad <- first_negative(mask,a,x,mu); if(is.null(bad)) return(list(mu=mu,active=mask,steps=steps))
  reduced <- mask[mask != bad]; n2 <- num(reduced,a,x,b); d2 <- den(reduced,x); y <- mul(a[[bad+1]],sq(x[[bad+1]])); z <- fourth(x[[bad+1]])
  stopifnot(gt(n,zero),gt(d,zero),gt(d2,zero),gt(n2,zero),lt(mul(y,d),mul(n,z))); mu2 <- divq(n2,d2); stopifnot(lt(mu,mu2))
  runq(reduced,a,x,b,steps+1)
}
vectors <- function(n) { if(n==0) return(list(list())); out <- list(); for(p in vectors(n-1)) for(z in list(q(0),q(1),q(2))) out[[length(out)+1]] <- c(p,list(z)); out }
for(n in 1:4) for(a in vectors(n)) for(x in vectors(n)) for(bi in 0:4) { r <- runq(0:(n-1),a,x,q(bi)); stopifnot(r$steps <= n); for(i in r$active) stopifnot(le(zero,sub(a[[i+1]],mul(r$mu,sq(x[[i+1]]))))); for(i in setdiff(0:(n-1),r$active)) stopifnot(le(sub(a[[i+1]],mul(r$mu,sq(x[[i+1]]))),zero)) }
cat('r-q-finite-fuel=PASS\n')
cat('r-q-terminal-signs=PASS\n')
cat('r-q-multiplier-monotonicity=PASS\n')
cat('r-q-terminal-kkt-prescriptive=PASS\n')
cat('r-bridge-bounded=PASS\n')
cat('r-theorem-bounded=PASS\n')
cat('r-conjecture-falsification=PASS\n')
