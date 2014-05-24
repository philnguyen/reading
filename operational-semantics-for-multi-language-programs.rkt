#lang racket/base
(require redex/reduction-semantics "utils.rkt")

(define-language λMS
  [(x y z) variable-not-otherwise-mentioned]
  [n integer]
  ; ML
  [m x v (m m) (o/m m m) (if0 m m m)]
  [v (λ (x : τ) m) n]
  [o/m + -]
  [τ ι (τ → τ)]
  [M hole (M m) (v M) (op M m) (op v M) (if M m m)]
  [Γ {[x : τ] ...}]
  ; Scheme
  [s x u (s s) (o/s s s) (if0 s s s) (pr s) (wrong str)]
  [u (λ (x) s) n]
  [o/s + -]
  [pr proc? nat?]
  [S hole (S s) (u S) (o/s S s) (o/s u S) (if0 S s s) (pr S)]
  [str string])

;; ML typing
(define-judgment-form λMS
  #:contract (: Γ m τ)
  #:mode     (: I I O)
  [(: {_ ... [x : τ] _ ...} x τ)]
  [(: Γ (λ (x : τ_1) e) (τ_1 → τ_2))
   (: (++ Γ [x : τ_1]) e τ_2)]
  [(: _ n ι)]
  [(: Γ (m_1 m_2) τ_2)
   (: Γ m_1 (τ_1 → τ_2))
   (: Γ m_2 τ_1)]
  [(: Γ (o/m m_1 m_2) ι)
   (: Γ m_1 ι)
   (: Γ m_2 ι)]
  [(: Γ (if0 m_1 m_2 m_3) τ)
   (: Γ m_1 ι)
   (: Γ m_2 τ)
   (: Γ m_3 τ)])

;; ML's operational semantics
(define ->_m
  (reduction-relation
   λMS #:domain m
   [==> ((λ (x : _) m) v) (// m x v)]
   [==> (+ n_1 n_2) ,(+ (term n_1) (term n_2))]
   [==> (- n_1 n_2) ,(max 0 (- (term n_1) (term n_2)))]
   [==> (if0 0 m _) m]
   [==> (if0 n _ m) m (side-condition (not (zero? (term n))))]
   with
   [(--> (in-hole M m_1) (in-hole M m_2)) (==> m_1 m_2)]))

;; Scheme/s operational semantics
(define ->_s
  (reduction-relation
   λMS #:domain s
   [==> ((λ (x) s) u) (// s x u)]
   [==> (u_1 u_2) (wrong "non-proc")
        (side-condition (not (redex-match? λMS (λ (_) _) (term u_1))))]
   [==> (+ n_1 n_2) ,(+ (term n_1) (term n_2))]
   [==> (- n_1 n_2) ,(max 0 (- (term n_1) (term n_2)))]
   [==> (o/s u_1 u_2) (wrong "non-num")
        (side-condition (not (redex-match? λMS (n_1 n_2) (term (u_1 u_2)))))]
   [==> (if0 0 e _) e]
   [==> (if0 u _ e) e (side-condition (not (equal? 0 (term u))))]
   [==> (proc? (λ (_) _)) 0]
   [==> (proc? u) 1 (side-condition (not (redex-match? λMS (λ _ _) (term u))))]
   [==> (nat? n) 0]
   [==> (nat? u) 1 (side-condition (not (equal? 0 (term u))))]
   [--> (in-hole S (wrong str)) (wrong str)
        (side-condition (not (redex-match? λMS hole (term S))))]
   with
   [(--> (in-hole S s_1) (in-hole S s_2)) (==> s_1 s_2)]))

;; extend languages with interoperability using lump embedding
(define-extended-language λMS+ λMS
  ; ML
  [m .... (τ M←S s)]
  [v .... (L M←S u)]
  [τ .... L]
  [M .... (τ M←S S)]
  ; Scheme
  [s .... (S←M τ m)]
  [u .... (S←M τ v)]
  [S .... (S←M τ M)])

;; extend ML's operational semantics with Scheme interoperation using lump embedding
(define ->_m/L
  (extend-reduction-relation
   ->_m λMS+ #:domain m
   [==> (τ M←S (S←M τ v)) v]
   [==> (τ M←S u) (τ M←S (wrong "Bad value"))
        (side-condition (and (not (redex-match? λMS+ (S←M τ v) (term u)))
                             (not (redex-match? λMS+ L (term τ)))))]
   [==> (S←M L (L M←S u)) u]
   [==> (τ M←S s_1) (τ M←S s_2)
        (where {_ ... s_2 _ ...} ,(apply-reduction-relation ->_s (term s_1)))]
   with
   [(--> (in-hole M m_1) (in-hole M m_2)) (==> m_1 m_2)]))


;; extend languages with interoperability using natural embedding
(define-extended-language λMS* λMS
  ; ML
  [m .... (M←S/G τ s)]
  [M .... (M←S/G τ S)]
  ; Scheme
  [s .... (G/S←M τ m)]
  [S .... (G/S←M τ M)])

;; extend ML's operational semantics with Scheme interoperation using natural embedding
(define ->_m/N
  (extend-reduction-relation
   ->_m λMS* #:domain m
   [==> (M←S/G ι n) n]
   [==> (M←S/G ι u) (wrong "Non-number")
        (side-condition (not (redex-match? λMS* n (term u))))]
   [==> (M←S/G (τ_1 → τ_2) (λ (x) s))
        (λ (x : τ_1) (M←S/G τ_2 ((λ (x) s) (G/S←M τ_1 x))))]
   [==> (M←S/G (τ_1 → τ_2) u)
        (M←S/G (τ_1 → τ_2) (wrong "Non-procedure"))
        (side-condition (not (redex-match? λMS* (λ _ _) (term u))))]
   [==> (G/S←M ι n) n]
   [==> (G/S←M (τ_1 → τ_2) v)
        (λ (x) (G/S←M τ_2 (v (M←S/G τ_1 x))))]
   with
   [(--> (in-hole M m_1) (in-hole M m_2)) (==> m_1 m_2)]))