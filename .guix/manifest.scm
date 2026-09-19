(use-modules
 (guix packages)
 (guix profiles))

(define lane (or (getenv "CI_LANE") "surface"))

(define (pkg spec)
  (specification->package spec))

(define lane-packages
  (cond
   ((string=? lane "agda-safe")
    (list
     (pkg "agda")
     (pkg "agda-stdlib")
     (pkg "guile@3.0")))
   ((or (string=? lane "mercury")
        (string=? lane "discovery"))
    (list
     (pkg "mercury-minimal")
     (pkg "guile@3.0")))
   ((string=? lane "surface")
    (list
     (pkg "guile@3.0")))
   (else
    (error (format #f "unknown CI_LANE: ~a" lane)))))

(packages->manifest lane-packages)
