;; Guix-native CI driver.
;; All repository orchestration is expressed in Guile.  The proof and
;; verifier tools are supplied only by the pinned manifest below.

(use-modules
 (ice-9 format)
 (ice-9 rdelim)
 (srfi srfi-1)
 (srfi srfi-13))

(define channels-file ".guix/channels.scm")
(define manifest-file ".guix/manifest.scm")
(define self-file ".guix/ci.scm")

(define (run! label . argv)
  (format #t "==> ~a: ~s~%" label argv)
  (let ((status (apply system* argv)))
    (if (= status 0)
        status
        (error (format #f "~a failed with status ~a" label status)))))

(define (in-directory directory thunk)
  (let ((old (getcwd)))
    (dynamic-wind
      (lambda () (chdir directory))
      thunk
      (lambda () (chdir old)))))

(define (agda-safe-files)
  '("Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda"
    "Exotic/ERL/FullCoupled/TheoremsMonolith.agda"
    "Exotic/ERL/FullCoupled/CanonicalLearnerMonolith_test.agda"
    "Exotic/ERL/FullCoupled/CanonicalClosedLoopInterface.agda"
    "Exotic/ERL/FullCoupled/CanonicalGamePorts.agda"
    "Exotic/ERL/FullCoupled/CanonicalFaithfulGameVariants.agda"
    "Exotic/ERL/FullCoupled/CanonicalClosedLoopBench.agda"
    "Exotic/ERL/FullCoupled/GeneralClosedLoopBenchV2.agda"
    "Exotic/ERL/FullCoupled/AdditionalBenchmarkPorts.agda"
    "Exotic/econlib/GameTheory.agda"
    "Exotic/econlib/Equilibrium.agda"
    "Exotic/econlib/MatchingPennies.agda"
    "Exotic/ERL/FullCoupled/CanonicalLearnerGameExecution_test.agda"))

(define (run-agda-safe)
  (for-each
   (lambda (file)
     (run! (string-append "Agda --safe " file)
           "agda" "--safe" file))
   (agda-safe-files)))

(define (run-mercury)
  (in-directory ".ci"
    (lambda ()
      (run! "build forbidden-theorem scanner"
            "mmc" "--make" "check_forbidden_theorems")
      (run! "run forbidden-theorem scanner"
            "./check_forbidden_theorems")))
  (in-directory ".ci/discovery"
    (lambda ()
      (run! "build Mercury A/Q discovery"
            "mmc" "--make" "jaxtar_aq_discovery")
      (run! "run Mercury A/Q discovery"
            "./jaxtar_aq_discovery")
      (run! "build Mercury involution verifier"
            "mmc" "--make" "clojure_involution_compat")
      (run! "run Mercury involution verifier"
            "./clojure_involution_compat")))
  (in-directory "oracle"
    (lambda ()
      (run! "build Mercury rational oracle"
            "mmc" "--make" "mercury_oracle")
      (run! "run Mercury rational oracle"
            "./mercury_oracle"))))

(define (run-discovery)
  ;; The finite A/Q discovery path is now Mercury-native.  The report is
  ;; emitted directly as deterministic JSON by jaxtar_aq_discovery.m.
  (in-directory ".ci/discovery"
    (lambda ()
      (run! "build Mercury finite discovery"
            "mmc" "--make" "jaxtar_aq_discovery")
      (run! "run Mercury finite discovery"
            "./jaxtar_aq_discovery"))))

(define (git-files)
  (let ((port (open-pipe* OPEN_READ "git" "ls-files")))
    (let loop ((result '()))
      (let ((line (read-line port)))
        (if (eof-object? line)
            (begin
              (close-pipe port)
              (reverse result))
            (loop (cons line result)))))))

(define (suffix? suffix file)
  (string-suffix? suffix file))

(define (bad-surface-files)
  (filter
   (lambda (file)
     (or (suffix? ".hs" file)
         (suffix? ".cabal" file)
         (suffix? ".sh" file)
         (suffix? ".cmd" file)
         (suffix? ".bat" file)
         (suffix? ".ps1" file)
         (suffix? ".py" file)
         (suffix? ".js" file)
         (suffix? ".mjs" file)
         (suffix? ".ts" file)
         (suffix? ".tsx" file)
         (suffix? ".java" file)
         (suffix? ".kt" file)
         (suffix? ".scala" file)
         (suffix? ".elm" file)
         (suffix? ".purs" file)))
   (git-files)))

(define (run-surface-audit)
  (let ((bad (bad-surface-files)))
    (if (null? bad)
        (format #t "surface=clean; noncanonical language/script files=absent~%")
        (begin
          (format #t "ERROR: forbidden legacy/noncanonical source files remain:~%")
          (for-each (lambda (file) (format #t "  ~a~%" file)) bad)
          (exit 1)))))

(define (run-lane lane)
  (cond
   ((string=? lane "agda-safe") (run-agda-safe))
   ((string=? lane "mercury") (run-mercury))
   ((string=? lane "discovery") (run-discovery))
   ((string=? lane "surface") (run-surface-audit))
   (else (error (format #f "unknown CI_LANE: ~a" lane)))))

(define lane (or (getenv "CI_LANE") "surface"))
(define inside-pinned-env? (getenv "GUIX_ENVIRONMENT"))

(if inside-pinned-env?
    (begin
      (format #t "guix-pinned-environment=active~%")
      (run-lane lane))
    (begin
      (format #t "guix-pinned-environment=entering~%")
      (run! "enter pinned Guix environment"
            "guix" "time-machine"
            "-C" channels-file
            "--"
            "shell" "--pure"
            "-m" manifest-file
            "--"
            "guile" self-file))))
