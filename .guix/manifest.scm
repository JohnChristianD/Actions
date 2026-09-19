(use-modules
 (guix packages)
 (guix profiles)
 (guix git-download)
 (gnu packages agda)
 (gnu packages mercury))

;; The CI container pins Guix itself. The stock channel in that image is
;; Agda 2.7.0.1-era but carries agda-stdlib 2.1.1, while this repository
;; deliberately checks against agda-stdlib 2.3. Reuse the channel's Agda
;; package recipe and pin only the standard-library source to its 2.3 tag.
;; This avoids a full guix time-machine channel update on every CI lane.
(define agda-stdlib-2.3
  (package
    (inherit agda-stdlib)
    (version "2.3")
    (source
     (origin
       (method git-fetch)
       (uri (git-reference
             (url "https://github.com/agda/agda-stdlib")
             (commit "v2.3")))
       (file-name (git-file-name "agda-stdlib" version))
       (sha256
        (base32
         "17w5vfn5pb2cgfs22zph3jfqnki52ja8y4zwyqj24zwf9rxairr4"))))))

(packages->manifest
 (list
  (specification->package "agda@2.7.0.1")
  agda-stdlib-2.3
  mercury-minimal
  (specification->package "guile@3.0")))
