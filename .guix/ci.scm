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

(define (read-file-string file)
  (call-with-input-file
      file
    (lambda (port)
      (get-string-all port))))

(define (run-discovery-artifact-audit)
  (let* ((generated
          "Exotic/ERL/FullCoupled/GeneratedNovelLearnerTheorems.agda")
         (text (read-file-string generated)))
    (if (string-contains text "= refl\n")
        (begin
          (format #t
                  "ERROR: generated discovery module contains a bare refl proof~%")
          (exit 1))
        (format #t
                "discovery-proof-shape=nontrivial; bare-refl=absent~%"))))

(define (agda-safe-files)
  '("Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda"
    "Exotic/ERL/FullCoupled/TheoremsMonolith.agda"
    "Exotic/ERL/FullCoupled/AlgebraLawRegistry.agda"
    "Exotic/ERL/FullCoupled/AlgebraLawRegistry_test.agda"
    "Exotic/ERL/FullCoupled/CanonicalLearnerMonolith_test.agda"
    "Exotic/ERL/FullCoupled/TSTS_Connected_test.agda"
    "Exotic/ERL/FullCoupled/Attention_Mediator_Connected_test.agda"
    "Exotic/ERL/FullCoupled/NovelLearnerTheoremDiscovery_test.agda"
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
  ;; Regenerate only novel learner-law candidates before the proof lane.
  (run-novel-learner-theorem-discovery)
  (run-discovery-artifact-audit)
  (for-each
   (lambda (file)
     (run! (string-append "Agda --safe " file)
           "agda" "--safe" file))
   (agda-safe-files))
  (run! "Agda --safe generated novel learner theorem module"
        "agda" "--safe"
        "Exotic/ERL/FullCoupled/GeneratedNovelLearnerTheorems.agda"))

(define (run-novel-learner-theorem-discovery)
  (in-directory ".ci/discovery"
    (lambda ()
      (run! "build Mercury generic e-graph regression"
            "mmc" "--make" "symbolic_egraph_test")
      (run! "run Mercury generic e-graph regression"
            "./symbolic_egraph_test")
      (run! "build Mercury theorem e-graph regression"
            "mmc" "--make" "learner_theorem_egraph_test")
      (run! "run Mercury theorem e-graph regression"
            "./learner_theorem_egraph_test")
      (run! "build Mercury interpolated theorem e-graph regression"
            "mmc" "--make" "interpolated_theorem_egraph_test")
      (run! "run Mercury interpolated theorem e-graph regression"
            "./interpolated_theorem_egraph_test")
      (run! "build Mercury novel learner theorem discovery"
            "mmc" "--make" "novel_learner_theorem_discovery")
      (run! "run Mercury novel learner theorem discovery"
            "./novel_learner_theorem_discovery"))))

(define (run-mercury)
  (in-directory ".ci"
    (lambda ()
      (run! "build forbidden-theorem scanner"
            "mmc" "--make" "check_forbidden_theorems")
      (run! "run forbidden-theorem scanner"
            "./check_forbidden_theorems")))
  (run-novel-learner-theorem-discovery))

(define (run-discovery)
  ;; The canonical discovery lane enumerates only novel, nontrivial
  ;; learner-law basis candidates. Agda remains authoritative for theorem
  ;; acceptance.
  (run-novel-learner-theorem-discovery)
  (run-discovery-artifact-audit))

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
