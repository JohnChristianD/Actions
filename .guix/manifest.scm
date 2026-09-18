(use-modules (guix profiles))

(specifications->manifest
 '("agda@2.7.0.1"
   "agda-stdlib@2.3"
   "mercury@22.01.4"
   "python@3.11"
   "guile@3.0"
   "git"))
