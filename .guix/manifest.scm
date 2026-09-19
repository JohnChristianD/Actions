(use-modules
 (guix packages)
 (guix profiles)
  (srfi srfi-1))

;; Guix supplies the pure proof-driver runtime. The pinned official Agda
;; setup action supplies Agda 2.8.0.2 and stdlib 2.4 outside this manifest.
(define lane (or (getenv "CI_LANE") "surface"))

(define lane-packages
  (cond
   ((string=? lane "agda-safe")
    (list
     (specification->package "guile@3.0")))
   ((or (string=? lane "mercury")
        (string=? lane "discovery"))
    (list
     (specification->package "guile@3.0")))
   ((string=? lane "surface")
    (list
     (specification->package "guile@3.0")))
   (else
    (error (format #f "unknown CI_LANE: ~a" lane)))))

(packages->manifest lane-packages)
