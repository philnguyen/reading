#lang racket/base
(provide (all-defined-out))
(require redex/reduction-semantics)

(define-language empty-lang)

;; extend environment
(define-metafunction empty-lang
  ++ : {[any any any] ...} [any any any] -> {[any any any] ...}
  [(++ {any ...} [any_k any_↦ any_v]) {any ... [any_k any_↦ any_v]}])

;; update environment
(define-metafunction empty-lang
  !! : {[any any any] ...} [any any any] -> {[any any any] ...}
  [(!! {any_1 ... [any_k any_↦ _] any_2 ...} [any_k any_↦ any_v])
   {any_1 ... [any_k any_↦ any_v] any_2 ...}])