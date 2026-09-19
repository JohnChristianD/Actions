(use-modules
 (guix packages)
 (guix profiles)
 (gnu packages agda)
 (srfi srfi-1))

;; The prepared GitHub Guix action supplies a current Guix package set.
;; Keep the proof lane on that package set so Agda and agda-stdlib advance
;; together instead of pinning an obsolete compiler/library pair.
(define lane (or (getenv "CI_LANE") "surface"))

(define lane-packages
  (cond
   ((string=? lane "agda-safe")
    (list
     agda
     agda-stdlib
     (specification->package "guile@3.0")))
   ((or (string=? lane "mercury")
        (string=? lane "discovery"))
    (list
     (specification->package "mercury-minimal")
     (specification->package "guile@3.0")))
   ((string=? lane "surface")
    (list
     (specification->package "guile@3.0")))
   (else
    (error (format #f "unknown CI_LANE: ~a" lane)))))

(packages->manifest lane-packages)
