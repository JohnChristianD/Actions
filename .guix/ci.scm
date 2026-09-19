;; Guix-native CI driver.
;; All repository orchestration is expressed in Guile.  The proof and
;; verifier tools are supplied only by the pinned manifest below.

(use-modules
 (ice-9 format)
 (ice-9 rdelim)
 (ice-9 ftw)
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
    "Exotic/ERL/FullCoupled/NovelLearnerTheoremDiscovery_test.agda"))

(define (run-agda-safe)
  ;; The Agda lane is deliberately proof-check-only.  Mercury discovery
  ;; owns generation/e-graph work in its separate lane.
  (run! "Guix-installed Agda version"
        "agda" "--version")
  ;; CanonicalLearnerMonolith_test imports Data.Empty and other Agda
  ;; standard-library modules, so this is the stdlib import smoke check
  ;; under the actual Guix-installed Agda executable.
  (run! "Agda --safe stdlib import smoke"
        "agda" "--safe"
        "Exotic/ERL/FullCoupled/CanonicalLearnerMonolith_test.agda")
  (for-each
   (lambda (file)
     (run! (string-append "Agda --safe " file)
           "agda" "--safe" file))
   (agda-safe-files))
  (run! "Agda --safe generated novel learner theorem module"
        "agda" "--safe"
        "Exotic/ERL/FullCoupled/GeneratedNovelLearnerTheorems.agda"))

(define (run-automated-semantic-egraph)
  (in-directory ".ci/discovery"
    (lambda ()
      (run! "build Mercury learner semantic theorem discovery"
            "mmc" "--make" "novel_learner_theorem_discovery")
      (run! "run Mercury learner semantic theorem discovery"
            "./novel_learner_theorem_discovery")
      (run! "build Mercury generic e-graph regression"
            "mmc" "--make" "symbolic_egraph_test")
      (run! "run Mercury generic e-graph regression"
            "./symbolic_egraph_test")
      (run! "build Mercury interpolated theorem e-graph regression"
            "mmc" "--make" "interpolated_theorem_egraph_test")
      (run! "run Mercury interpolated theorem e-graph regression"
            "./interpolated_theorem_egraph_test"))))

(define (run-mercury)
  (in-directory ".ci"
    (lambda ()
      (run! "build forbidden-theorem scanner"
            "mmc" "--make" "check_forbidden_theorems")
      (run! "run forbidden-theorem scanner"
            "./check_forbidden_theorems")))
  (run-automated-semantic-egraph))

(define (run-discovery)
  ;; Extract executable learner/theorem declarations, then build and quotient
  ;; the generic e-graph from that source-derived dependency graph.
  (run-automated-semantic-egraph))

(define (repository-files directory)
  (append-map
   (lambda (name)
     (let ((path (string-append directory "/" name)))
       (if (file-is-directory? path)
           (repository-files path)
           (list path))))
   (scandir
    directory
    (lambda (name)
      (and (not (string=? name "."))
           (not (string=? name ".."))
           (not (string=? name ".git")))))))

(define (git-files)
  ;; The CI checkout is supplied by actions/checkout.  The pinned Guix
  ;; environment therefore does not need to build Git just to audit files.
  (repository-files (getcwd)))

(define (suffix? suffix file)
  (string-suffix? suffix file))

(define (bad-surface-files)
  (filter
   (lambda (file)
     (or
      ;; Shell / command / remote-execution surfaces.
      (suffix? ".sh" file)
      (suffix? ".bash" file)
      (suffix? ".zsh" file)
      (suffix? ".fish" file)
      (suffix? ".cmd" file)
      (suffix? ".bat" file)
      (suffix? ".ps1" file)
      (suffix? ".command" file)
      (string=? file "ssh")
      (string=? file "scp")
      (string-suffix? "/ssh" file)
      (string-suffix? "/scp" file)
      (string=? file "python")
      (string=? file "bash")
      (string=? file "sh")
      (string=? file "cmd")
      (string=? file "powershell")
      ;; Python / JVM / JS / alternate language surfaces.
      (suffix? ".py" file)
      (suffix? ".java" file)
      (suffix? ".kt" file)
      (suffix? ".scala" file)
      (suffix? ".groovy" file)
      (suffix? ".clj" file)
      (suffix? ".cljs" file)
      (suffix? ".js" file)
      (suffix? ".mjs" file)
      (suffix? ".cjs" file)
      (suffix? ".ts" file)
      (suffix? ".tsx" file)
      (suffix? ".elm" file)
      (suffix? ".purs" file)
      (suffix? ".hs" file)
      (suffix? ".lhs" file)
      (suffix? ".cabal" file)
      ;; C / C++.
      (suffix? ".c" file)
      (suffix? ".h" file)
      (suffix? ".cc" file)
      (suffix? ".cpp" file)
      (suffix? ".cxx" file)
      (suffix? ".hpp" file)
      (suffix? ".hxx" file)
      ;; .NET / CLR project surfaces.
      (suffix? ".cs" file)
      (suffix? ".fs" file)
      (suffix? ".fsx" file)
      (suffix? ".vb" file)
      (suffix? ".csproj" file)
      (suffix? ".fsproj" file)
      (suffix? ".vbproj" file)
      (suffix? ".sln" file)
      ;; Web/markup source surfaces.
      (suffix? ".html" file)
      (suffix? ".htm" file)
      (suffix? ".css" file)
      ;; TeX / LaTeX-family files.
      (suffix? ".tex" file)
      (suffix? ".ltx" file)
      (suffix? ".sty" file)
      (suffix? ".cls" file)
      (suffix? ".bib" file)
      ;; Markdown is permitted only for a README.
      (and (or (suffix? ".md" file) (suffix? ".markdown" file))
           (not (string-suffix? "/README.md" file))
           (not (string=? file "README.md")))))
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
