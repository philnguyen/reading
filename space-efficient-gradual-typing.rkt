#lang racket/base
(require redex/reduction-semantics)

;; gradually typed λ-calculus
(define-language L
  
  ;; source language
  ; term
  [e k x (λ (x : T) e) (e e) (ref e) (! e) (e := e)]
  [k real]
  ; type
  [(S S′ T T′) B (T → T) ? (Ref T)]
  [B Int Float]
  ; environment
  [E {[x : T] ...}]
  ; coercion
  [(c d) I Fail (D !) (D ?) IntFloat (Fun c c) (Ref c c) (& c c)]
  ; dynamic tag
  [D B Fun Ref]
  
  ;; target language
  ; term
  [(s t) x u (t t) (ref t) (! t) (t := t) (c ◃ t)]
  ; value
  [v u (c ◃ u)]
  ; uncoerced value
  [u (λ (x : T) t) k a]
  ; store + store typings
  [σ {[a = v] ...}]
  [Σ {[a : T] ...}]
  [a integer]
  ; evaluation context
  [C hole (C t) (v C) (ref C) (! C) (C := t) (v := C) (c ◃ N)]
  [N hole (C t) (v C) (ref C) (! C) (C := t) (v := C)])

;; exend environment
(define-metafunction L
  ++ : E [x any T] -> E
  [(++ {any ...} [x any_: T]) {any ... [x any_: T]}]) ; add at end for readability

;; type consistency rules
(define-relation L
  ~ ⊆ T × T
  [(~ T T)] ; C-Refl
  [(~ _ ?)] ; C-DynR
  [(~ ? _)] ; C-DynL
  [(~ Int Float)] ; C-Float
  [(~ (S_1 → S_2) (T_1 T_2)) ; C-Fun
   (~ T_1 S_1)
   (~ S_2 T_2)]
  [(~ (Ref S) (Ref T)) ; C-Ref
   (~ T S)
   (~ S T)])

;; type rules
(define-judgment-form L
  #:contract (: E e T)
  #:mode     (: I I O)
  [------------------------------- T-Var
   (: {_ ... [x : T] _ ...} x T)]
  [(: (++ E [x : S]) e T)
   ------------------------------- T-Fun
   (: E (λ (x : S) e) (S → T))]
  [------------------------------- T-Const
   (: _ k (ty k))]
  [(: E e_1 (S → T))
   (: E e_2 S′)
   (side-condition (~ S′ S))
   ------------------------------- T-App1
   (: E (e_1 e_2) T)]
  [(: E e_1 ?)
   (: E e_2 _)
   ------------------------------- T-App2
   (: E (e_1 e_2) ?)]
  [(: E e T)
   ------------------------------- T-Ref
   (: E (ref e) (Ref T))]
  [(: E e (Ref T))
   ------------------------------- T-Deref1
   (: E (! e) T)]
  [(: E e ?)
   ------------------------------- T-Deref2
   (: E (! e) ?)]
  [(: E e_1 (Ref T))
   (: E e_2 S)
   (side-condition (~ S T))
   ------------------------------- T-Assign1
   (: E (e_1 := e_2) S)]
  [(: E e_1 ?)
   (: E e_2 _)
   ------------------------------- T-Assign2
   (: E (e_1 := e_2) ?)])

;; base types
(define-metafunction L
  ty : k -> B
  [(ty integer) Int]
  [(ty real) Float]) ; sloppy

;; coersion rules
; written as relation instead of judgment form because C-Fail is not algorithmic
(define-relation L
  ~> ⊆ c × S × T
  ; C-Id
  [(~> I T T)]
  ; C-Fail
  [(~> Fail _ _)]
  ; C-B!, C-B?
  [(~> (B !) B ?)]
  [(~> (B ?) ? B)]
  ; C-Fun!, C-Fun?, C-Fun
  [(~> (Fun !) (? → ?) ?)]
  [(~> (Fun ?) ? (? → ?))]
  [(~> (Fun c_1 c_2) (T_1 → T_2) (T′_1 T′_2))
   (~> c_1 T′_1 T_1)
   (~> c_2 T_2 T′_2)]
  ; C-Ref!, C-Ref?, C-Ref
  [(~> (Ref !) (Ref ?) ?)
   (~> (Ref ?) ? (Ref ?))]
  [(~> (Ref c d) (Ref S) (Ref T))
   (~> c T S)
   (~> d S T)]
  ; C-Compose
  [(~> (& c_1 c_2) T T_2)
   (~> c_1 T T_1)
   (~> c_2 T_1 T_2)]
  ; C-Float
  [(~> IntFloat Int Float)])

;; compute appropriate coercion betweentypes
(define-metafunction L
  coerce : T T -> c
  [(coerce T T) I]
  [(coerce B ?) (B !)]
  [(coerce ? B) (B ?)]
  [(coerce Int Float) IntFloat]
  [(coerce (S_1 → S_2) (T_1 → T_2)) (Fun (coerce T_1 S_1) (coerce (S_2 T_2)))]
  [(coerce ? (T_1 → T_2)) (& (Fun ?) (coerce (? → ?) (T_1 → T_2)))]
  [(coerce (T_1 → T_2) ?) (& (coerce (T_1 → T_2) (? → ?)) (Fun !))]
  [(coerce (Ref S) (Ref T)) (Ref (coerce T S) (coerce S T))]
  [(coerce ? (Ref T)) (& (Ref ?) (coerce (Ref ?) (Ref T)))]
  [(coerce (Ref T) ?) (& (coerce (Ref T) (Ref ?)) (Ref !))])

;; target language type rules
#;(define-judgment-form L
  #:contract (T: E Σ t T)
  #:mode     (T: I I I O)
  [------------------------------- T-Var
   (T: {_ ... [x : T] _ ...} _ x T)]
  [(T: (++ E [x : S]) Σ t T)
   ------------------------------- T-Fun
   (T: E Σ (λ (x : S) t) (S → T))]
  [(T: E Σ t_1 (S → T))
   (T: E Σ t_2 S)
   ------------------------------- T-App
   (T: E Σ (t_1 t_2) T)]
  [(T: E Σ t T)
   ------------------------------- T-Ref
   (T: E Σ (ref t) (Ref T))]
  [(T: E Σ t (Ref T))
   ------------------------------- T-Deref
   (T: E Σ (! t) T)]
  [(T: E Σ t_1 (Ref T))
   (T: E Σ t_2 T)
   ------------------------------- T-Assign
   (T: E Σ (t_1 := t_2) T)]
  [------------------------------- T-Const
   (T: _ _ k (ty k))]
  [(T: E Σ t S)
   (side-condition (~> c S T))
   ------------------------------- T-Cast ; oops non-algorithmic
   (T: E Σ (c ◃ t) T)]
  )

;; cast insertion
(define-judgment-form L
  #:contract (⇒ E e t T)
  #:mode     (⇒ I I O O)
  [------------------------------- C-Var
   (⇒ {_ ... [x : T] _ ...} x x T)]
  [------------------------------- C-Const
   (⇒ _ k k (ty k))]
  [(⇒ (++ E [x : S]) e t T)
   ------------------------------- C-Fun
   (⇒ E (λ (x : S) e) (λ (x : S) t) (S → T))]
  [(⇒ E e_1 t_1 (S → T))
   (⇒ E e_2 t_2 S′)
   ------------------------------- C-App1
   (⇒ E (e_1 e_2) (t_1 ((coerce S′ S) t_2)) T)]
  [(⇒ E e_1 t_1 ?)
   (⇒ E e_2 t_2 S′)
   ------------------------------- C-App2
   (⇒ E (e_1 e_2) (((Fun ?) ◃ t_1) ((coerce S′ ?) ◃ t_2)) ?)]
  [(⇒ E e t T)
   ------------------------------- C-Ref
   (⇒ E (ref e) (ref t) (Ref T))]
  [(⇒ E e t (Ref T))
   ------------------------------- C-Deref1
   (⇒ E (! e) (! t) T)]
  [(⇒ E e t ?)
   ------------------------------- C-Deref2
   (⇒ E (! e) (! ((Ref ?) ◃ t)) ?)]
  [(⇒ E e_1 t_1 (Ref S))
   (⇒ E e_2 t_2 T)
   ------------------------------- C-Assign1
   (⇒ E (e_1 := e_2) (t_1 := ((coerce T S) ◃ t_2)) S)]
  [(⇒ E e_1 t_1 ?)
   (⇒ E e_2 t_2 T)
   ------------------------------- C-Assign2
   (⇒ E (e_1 := e_2) (((Ref ?) ◃ t_1) := ((coerce T ?) t_2)) ?)])

;; normalize coercion
(define-metafunction L
  &↓ : c c -> c
  [(&↓ I c) c]
  [(&↓ c I) c]
  [(&↓ Fail c) Fail]
  [(&↓ c Fail) Fail]
  [(&↓ (D !) (D ?)) I]
  [(&↓ (_ !) (_ ?)) Fail]
  [(&↓ (Fun c_1 c_2) (Fun d_1 d_2)) (Fun (&↓ d_1 c_1) (&↓ c_2 d_2))]
  [(&↓ (Ref c_1 c_2) (Ref d_1 d_2)) (Ref (&↓ d_1 c_1) (&↓ c_2 d_2))]
  [(&↓ c d) (& c d)])

;; operational semantics
(define ->
  (reduction-relation
   L #:domain (t σ)
   [--> {(in-hole C [(λ (x : _) t) v]) σ}
        {(in-hole C [// t x v]) σ}
        E-Beta]
   [--> {(in-hole C [ref v]) σ}
        {(in-hole C a) (++ σ [a = v])}
        E-New
        (where a (alloc σ))]
   [--> {(in-hole C [a := v]) σ}
        {(in-hole C [lookup σ a]) σ}
        E-Deref]
   [--> {(in-hole C [a := v]) σ}
        {(in-hole C v) (!! σ [a = v])}
        E-Assign]
   [--> {(in-hole C [k v]) σ}
        {(in-hole C [δ k v]) σ}
        E-Prim]
   [--> {(in-hole C [((Fun c d) ◃ u) v]) σ}
        {(in-hole C [d ◃ (u (c ◃ v))]) σ}
        E-CApp]
   [--> {(in-hole C [! ((Ref c d) ◃ a)]) σ}
        {(in-hole C [d ◃ (! a)]) σ}
        E-CDeref]
   [--> {(in-hole C [((Ref c d) ◃ a) := v]) σ}
        {(in-hole C [d ◃ (a := (c ◃ v))]) σ}
        E-CAssign]
   [--> {(in-hole C [I ◃ u]) σ}
        {(in-hole C u)}
        (side-condition (not (redex-match? L (in-hole C_1 [c ◃ hole]) (term C))))]
   [--> {(in-hole C [IntFloat ◃ n]) σ}
        {(in-hole C [nearest-float n]) σ}
        (side-condition (not (redex-match? L (in-hole C_1 [c ◃ hole]) (term C))))]
   [--> {(in-hole C [c ◃ (d ◃ t)]) σ}
        {(in-hole C [(&↓ d c) ◃ t]) σ}
        E-CCast]))

;; convert int -> float in target language
(define-metafunction L
  nearest-float : int -> real
  [(nearest-float n) ,(exact->inexact (term n))])

;; sloppy substitution
(define-metafunction L
  // : t x v -> t
  [(// x x v) v]
  [(// x _ _) x]
  [(// (name u (λ (x : _) _)) x _) u]
  [(// (λ (z : T) t) x v) (λ (z : T) (// t x v))]
  [(// v _ _) v]
  [(// (t ...) x v) ((// t x v) ...)]
  [(// (ref t) x v) (ref (// t x v))]
  [(// (! t) x v) (! (// t x v))]
  [(// (s := t) x v) ((// s x v) := (// t x v))]
  [(// (c ◃ t) x v) (c ◃ (// t x v))])