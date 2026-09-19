;; Guix-native CI driver.
;; Guix installation, daemon setup, and host bootstrap are delegated to the
;; prepared GitHub Action. This file only selects and runs the repository lane
;; inside the manifest-defined environment.

(use-modules
 (ice-9 format)
 (ice-9 rdelim)
 (ice-9 ftw)
 (srfi srfi-1)
 (srfi srfi-13))

(define manifest-file ".guix/manifest.scm")

(define agda-command
  (or (getenv "AGDA_COMMAND") "agda"))

(define mercury-command
  (or (getenv "MERCURY_COMMAND") "mmc"))

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
  '("Exotic/ERL/FullCoupled/TheoremsMonolith.agda"
    "Exotic/ERL/FullCoupled/CanonicalLearnerMonolith_test.agda"
    "Exotic/ERL/FullCoupled/NovelLearnerTheoremDiscovery_test.agda"))

(define (run-agda-safe)
  ;; The Agda lane is deliberately proof-check-only. The theorem monolith is
  ;; the only connected theorem source; Mercury only discovers and validates
  ;; its dependency graph.
  (run! "Pinned Agda version"
        agda-command "--version")
  (run! "Agda --safe stdlib import smoke"
        agda-command "--safe"
        "Exotic/ERL/FullCoupled/CanonicalLearnerMonolith_test.agda")
  (for-each
   (lambda (file)
     (run! (string-append "Agda --safe " file)
           agda-command "--safe" file))
   (agda-safe-files)))

(define (run-automated-semantic-egraph)
  (in-directory ".ci/discovery"
    (lambda ()
      (run! "build Mercury theorem-monolith e-graph sync"
            mercury-command "--make" "theorem_monolith_egraph_sync")
      (run! "run Mercury theorem-monolith e-graph sync"
            "./theorem_monolith_egraph_sync")
      (run! "build Mercury generic e-graph regression"
            mercury-command "--make" "symbolic_egraph_test")
      (run! "run Mercury generic e-graph regression"
            "./symbolic_egraph_test")
      (run! "build Mercury interpolated theorem e-graph regression"
            mercury-command "--make" "interpolated_theorem_egraph_test")
      (run! "run Mercury interpolated theorem e-graph regression"
            "./interpolated_theorem_egraph_test"))))

(define (run-mercury)
  (in-directory ".ci"
    (lambda ()
      (run! "build forbidden-theorem scanner"
            mercury-command "--make" "check_forbidden_theorems")
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
  ;; The GitHub checkout action supplies the source tree. The pure Guix profile
  ;; therefore does not need to build Git just to audit repository files.
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
      ;; Markdown is permitted only for the root README.
      (and (or (suffix? ".md" file) (suffix? ".markdown" file))
           (not (string-suffix? "/README.md" file))
           (not (string=? file "README.md")))))
   (git-files)))

(define (run-single-theorem-source-audit)
  (let ((monoliths
         (filter
          (lambda (file)
            (string-suffix? "/Exotic/ERL/FullCoupled/TheoremsMonolith.agda" file))
          (git-files))))
    (if (and (= (length monoliths) 1)
             (not (file-exists? "wiki"))
             (not (file-exists? "Exotic/ERL/FullCoupled/GeneratedNovelLearnerTheorems.agda")))
        (format #t "single-theorem-source=TheoremsMonolith.agda; generated-Agda=absent; wiki=absent~%")
        (begin
          (format #t "ERROR: theorem surface is not single-file canonical: ~s~%" monoliths)
          (exit 1)))))

(define (run-surface-audit)
  (run-single-theorem-source-audit)
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

(if (getenv "GUIX_ENVIRONMENT")
    (begin
      (format #t "prepared-guix-action=active~%")
      (format #t "guix-manifest=~a~%" manifest-file)
      (run-lane lane))
    (error "CI driver must run inside guix shell; prepared action owns Guix bootstrap"))
