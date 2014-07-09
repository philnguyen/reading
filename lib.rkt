#lang racket/base
(provide (all-defined-out))
(require redex/reduction-semantics)

(define-language empty-lang)

;; extend environment
(define-metafunction empty-lang
  ++ : {[any any any] ...} [any any any] ... -> {[any any any] ...}
  [(++ any) any]
  [(++ any any_1 any_i ...) (++ (++/1 any any_1) any_i ...)])
(define-metafunction empty-lang
  ++/1 : {[any any any] ...} [any any any] -> {[any any any] ...}
  [(++/1 {any ...} [any_k any_↦ any_v]) {any ... [any_k any_↦ any_v]}])

;; update environment
(define-metafunction empty-lang
  !! : {[any any any] ...} [any any any] -> {[any any any] ...}
  [(!! {any_1 ... [any_k any_↦ _] any_2 ...} [any_k any_↦ any_v])
   {any_1 ... [any_k any_↦ any_v] any_2 ...}])

;; look up environment
(define-metafunction empty-lang
  lookup : {[any _ any] ...} any -> any
  [(lookup {_ ... [any_k _ any_v] _ ...} any_k) any_v])