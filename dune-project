(lang dune 3.20)

(name pass_strategy_synthesis)

(generate_opam_files true)

(source
 (github username/reponame))

(authors "Author Name <author@example.com>")

(maintainers "Maintainer Name <maintainer@example.com>")

(license LICENSE)

(documentation https://url/to/documentation)

(package
 (name pass_strategy_synthesis)
 (synopsis "A short synopsis")
 (description "A longer description")
 (depends
  (ocaml
   (= 4.14.2))
  GT
  (OCanren
   (>= 0.3.0~))
  (OCanren-ppx
   (>= 0.3.0~)))
 (tags
  ("add topics" "to describe" your project)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html
