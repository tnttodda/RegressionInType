Todd Waugh Ambridge, 7th December 2021

Search over uniformly continuous decidable predicates on infinite collections of types.
Part 2

Related reading: "Infinite sets that admit fast exhaustive search" (Escardó, LICS 2007)

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT hiding (decidable)
open import NaturalsOrder
open import Two-Properties hiding (_≥₂_;zero-is-not-one)
open import GenericConvergentSequence hiding (ℕ∞;∞;_≼_;∞-maximal)

module InfiniteSearch2 (fe : {𝓤 𝓥 : Universe} → {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {f g : Π Y} → f ∼ g → f ≡ g) where

open import InfiniteSearch1 fe

sequence-of-codistance-types : 𝓤₁ ̇ 
sequence-of-codistance-types = Σ T ꞉ (ℕ → 𝓤₀ ̇ ) , Π n ꞉ ℕ , (T n × T n → ℕ∞)

Π-codistance' : ((T , cs) : sequence-of-codistance-types) → Π T × Π T → (ℕ → 𝟚)
Π-codistance' (T , cs) (A , B) 0 = pr₁ (cs 0 (A 0 , B 0)) 0
Π-codistance' (T , cs) (A , B) (succ n)
 = min𝟚 (pr₁ (cs 0 (A 0 , B 0)) (succ n))
        (Π-codistance' (T ∘ succ , cs ∘ succ) ((A ∘ succ) , (B ∘ succ)) n)

Π-codistance'-dec : ((T , cs) : sequence-of-codistance-types)
                  → ((A , B) : Π T × Π T)
                  → decreasing (Π-codistance' (T , cs) (A , B))
Π-codistance'-dec (T , cs) (A , B) 0        r =
 pr₂ (cs 0 (A 0 , B 0)) 0 (Lemma[min𝟚ab≡₁→a≡₁] r)
Π-codistance'-dec (T , cs) (A , B) (succ n) r
 = Lemma[a≡₁→b≡₁→min𝟚ab≡₁]
     (pr₂ (cs 0 (A 0 , B 0)) (succ n) (Lemma[min𝟚ab≡₁→a≡₁] r))
     (Π-codistance'-dec (T ∘ succ , cs ∘ succ) (A ∘ succ , B ∘ succ) n
       (Lemma[min𝟚ab≡₁→b≡₁] {pr₁ (cs 0 (A 0 , B 0)) (succ (succ n))} r))

Π-codistance : ((T , cs) : sequence-of-codistance-types) → Π T × Π T → ℕ∞
Π-codistance (T , cs) (A , B) = Π-codistance'     (T , cs) (A , B)
                              , Π-codistance'-dec (T , cs) (A , B)

Π-codistance'-eic : ((T , cs) : sequence-of-codistance-types)
                  → ((n : ℕ) (α : T n) → cs n (α , α) ≡ ∞)
                  → (A : Π T) → Π-codistance (T , cs) (A , A) ≡ ∞
Π-codistance'-eic (T , cs) eics A = ℕ∞-equals (γ (T , cs) eics A)
 where
   γ : ((T , cs) : sequence-of-codistance-types)
     → ((n : ℕ) (α : T n) → cs n (α , α) ≡ ∞)
     → (A : Π T) → Π-codistance' (T , cs) (A , A) ∼ (λ _ → ₁)
   γ (T , cs) eics A = γ' where
     γ' : (i : ℕ) → Π-codistance' (T , cs) (A , A) i ≡ ₁
     γ' 0        = ap (λ - → pr₁ - 0) (eics 0 (A 0))
     γ' (succ i) = Lemma[a≡₁→b≡₁→min𝟚ab≡₁]
                     (ap (λ - → pr₁ - (succ i)) (eics 0 (A 0)))
                       (γ (T ∘ succ , cs ∘ succ) (eics ∘ succ) (A ∘ succ) i)

Π-codistance'-all : ((T , cs) : sequence-of-codistance-types)
                  → ((A , B) : Π T × Π T)
                  → Π-codistance (T , cs) (A , B) ≡ ∞
                  → (n : ℕ) → cs n (A n , B n) ≡ ∞
Π-codistance'-all (T , cs) (A , B) cAB≡∞ n
 = ℕ∞-equals (γ (T , cs) (A , B) (λ i → ap (λ - → pr₁ - i) cAB≡∞) n) where
  γ : ((T , cs) : sequence-of-codistance-types)
    → ((A , B) : Π T × Π T)
    → Π-codistance' (T , cs) (A , B) ∼ (pr₁ ∞)
    → (n : ℕ) → pr₁ (cs n (A n , B n)) ∼ pr₁ ∞
  γ (T , cs) (A , B) cAB∼∞ 0    0        = cAB∼∞ 0
  γ (T , cs) (A , B) cAB∼∞ 0    (succ i) = Lemma[min𝟚ab≡₁→a≡₁] (cAB∼∞ (succ i))
  γ (T , cs) (A , B) cAB∼∞ (succ n)
   = γ (T ∘ succ , cs ∘ succ) (A ∘ succ , B ∘ succ)
       (λ i → Lemma[min𝟚ab≡₁→b≡₁] (cAB∼∞ (succ i)))
       n

Π-codistance'-ice : ((T , cs) : sequence-of-codistance-types)
                  → ((n : ℕ) ((α , β) : T n × T n) → cs n (α , β) ≡ ∞ → α ≡ β)
                  → ((A , B) : Π T × Π T)
                  → Π-codistance (T , cs) (A , B) ≡ ∞
                  → A ≡ B
Π-codistance'-ice (T , cs) ices (A , B) cAB∼∞
 = fe (λ i → ices i (A i , B i) (Π-codistance'-all (T , cs) (A , B) cAB∼∞ i))

Π-codistance'-sym : ((T , cs) : sequence-of-codistance-types)
                  → ((n : ℕ) ((α , β) : T n × T n) → cs n (α , β) ≡ cs n (β , α))
                  → ((A , B) : Π T × Π T)
                  → Π-codistance (T , cs) (A , B) ≡ Π-codistance (T , cs) (B , A)
Π-codistance'-sym (T , cs) syms (A , B)
 = ℕ∞-equals (γ (T , cs) (λ n (α , β) i → ap (λ - → pr₁ - i) (syms n (α , β))) (A , B)) where
  γ : ((T , cs) : sequence-of-codistance-types)
    → ((n : ℕ) ((α , β) : T n × T n) → pr₁ (cs n (α , β)) ∼ pr₁ (cs n (β , α)))
    → ((A , B) : Π T × Π T)
    → Π-codistance' (T , cs) (A , B) ∼ Π-codistance' (T , cs) (B , A)
  γ (T , cs) syms (A , B) 0 = syms 0 (A 0 , B 0) 0
  γ (T , cs) syms (A , B) (succ i)
   = ap (λ - → min𝟚 - (Π-codistance' (T ∘ succ , cs ∘ succ) (A ∘ succ , B ∘ succ) i))
       (syms 0 (A 0 , B 0) (succ i))
   ∙ ap (λ - → min𝟚 (pr₁ (cs 0 (B 0 , A 0)) (succ i)) -)
       (γ (T ∘ succ , cs ∘ succ) (syms ∘ succ) (A ∘ succ , B ∘ succ) i)

Lemma[min𝟚abcd≡₁→min𝟚ac≡₁] : {a b c d : 𝟚}
                           → min𝟚 (min𝟚 a b) (min𝟚 c d) ≡ ₁
                           → min𝟚 a c ≡ ₁
Lemma[min𝟚abcd≡₁→min𝟚ac≡₁] {₁} {₁} {₁} {₁} e = refl

Lemma[min𝟚abcd≡₁→min𝟚bd≡₁] : {a b c d : 𝟚}
                           → min𝟚 (min𝟚 a b) (min𝟚 c d) ≡ ₁
                           → min𝟚 b d ≡ ₁
Lemma[min𝟚abcd≡₁→min𝟚bd≡₁] {₁} {₁} {₁} {₁} e = refl

Π-codistance'-ult : ((T , cs) : sequence-of-codistance-types)
                  → ((n : ℕ) ((α , β , ζ) : T n × T n × T n)
                    → min (cs n (α , β)) (cs n (β , ζ)) ≼ cs n (α , ζ))
                  → ((A , B , C) : Π T × Π T × Π T)
                  → min (Π-codistance (T , cs) (A , B)) (Π-codistance (T , cs) (B , C))
                      ≼ Π-codistance (T , cs) (A , C)
Π-codistance'-ult (T , cs) ults (A , B , C) 0        r
 = ults 0 (A 0 , B 0 , C 0) 0 r
Π-codistance'-ult (T , cs) ults (A , B , C) (succ n) r
 = Lemma[a≡₁→b≡₁→min𝟚ab≡₁]
     (ults 0 (A 0 , B 0 , C 0) (succ n)
     (Lemma[min𝟚abcd≡₁→min𝟚ac≡₁]
                           {pr₁ (cs 0 (A 0 , B 0)) (succ n)}
                           {Π-codistance' (T ∘ succ , cs ∘ succ) (A ∘ succ , B ∘ succ) n}
                           {pr₁ (cs 0 (B 0 , C 0)) (succ n)}
                           {Π-codistance' (T ∘ succ , cs ∘ succ) (B ∘ succ , C ∘ succ) n}
     r))
     (Π-codistance'-ult (T ∘ succ , cs ∘ succ) (ults ∘ succ)
        (A ∘ succ , B ∘ succ , C ∘ succ) n
     ((Lemma[min𝟚abcd≡₁→min𝟚bd≡₁] 
                           {pr₁ (cs 0 (A 0 , B 0)) (succ n)}
                           {Π-codistance' (T ∘ succ , cs ∘ succ) (A ∘ succ , B ∘ succ) n}
                           {pr₁ (cs 0 (B 0 , C 0)) (succ n)}
                           {Π-codistance' (T ∘ succ , cs ∘ succ) (B ∘ succ , C ∘ succ) n}
     r)))

Π-codistance-is-codistance : ((T , cs) : sequence-of-codistance-types)
                           → (ss : (n : ℕ) → is-clofun (cs n))
                           → is-clofun (Π-codistance (T , cs))
                           
is-clofun.equal→inf-close
 (Π-codistance-is-codistance (T , cs) ss)
 = Π-codistance'-eic (T , cs)
     (λ n → is-clofun.equal→inf-close (ss n))
     
is-clofun.inf-close→equal
 (Π-codistance-is-codistance (T , cs) ss)
 = λ A B f → Π-codistance'-ice (T , cs)
     (λ n (α , β) → is-clofun.inf-close→equal (ss n) α β)
     (A , B) f
 
is-clofun.symmetricity
 (Π-codistance-is-codistance (T , cs) ss)
 = λ A B → Π-codistance'-sym (T , cs)
     (λ n (α , β) → is-clofun.symmetricity (ss n) α β)
     (A , B)

is-clofun.ultrametric
 (Π-codistance-is-codistance (T , cs) ss)
 = λ A B C → Π-codistance'-ult (T , cs)
     (λ n (α , β , ζ) → is-clofun.ultrametric (ss n) α β ζ)
     (A , B , C)

_∷_ : {T : ℕ → 𝓤₀ ̇ } → T 0 → Π (T ∘ succ) → Π T
(x ∷ xs) 0 = x
(x ∷ xs) (succ n) = xs n

head2 : {T : ℕ → 𝓤₀ ̇ } → Π T → T 0
head2 α = α 0

tail2 : {T : ℕ → 𝓤₀ ̇ } → Π T → Π (T ∘ succ)
tail2 α = α ∘ succ

head-tail-eta2 : {T : ℕ → 𝓤₀ ̇ } → (α : Π T) → α ≡ head2 α ∷ tail2 α
head-tail-eta2 α = fe γ where
  γ : α ∼ (head2 α ∷ tail2 α)
  γ 0 = refl
  γ (succ n) = refl

_is-u-mod-of_on_and_ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → ℕ → (X → Y) → (X × X → ℕ∞) → (Y × Y → ℕ∞) → 𝓤 ̇ 
δ is-u-mod-of f on cx and cy
 = Π ε ꞉ ℕ , ∀ x₁ x₂ → (δ ↑) ≼ cx (x₁ , x₂) → (ε ↑) ≼ cy (f(x₁) , f(x₂))

continuous-c-searcher : {Y : 𝓤 ̇ } → (cy : Y × Y → ℕ∞) → c-searchable Y cy → (𝓤 ⁺) ̇ 
continuous-c-searcher {𝓤} {Y} cy Sy
 = {X : 𝓤 ̇ } → (cx : X × X → ℕ∞) → (pds : (x : X) → d-predicate Y)
 → (δ : ℕ) (ϕ : (x : X) → δ is-u-mod-of pr₁ (pds x) on cy)
 → δ is-u-mod-of (λ x → pr₁ (Sy (pr₁ (pds x) , pr₂ (pds x) , δ , ϕ x))) on cx and cy

tychonoff : ((T , cs) : sequence-of-codistance-types)
          → ((n : ℕ) → is-clofun (cs n))
          → (Ss : (n : ℕ) → c-searchable (T n) (cs n))
          → ((n : ℕ) → continuous-c-searcher (cs n) (Ss n))
          → c-searchable (Π T) (Π-codistance (T , cs))

tychonoff' : ((T , cs) : sequence-of-codistance-types)
           → ((n : ℕ) → is-clofun (cs n))
           → (Ss : (n : ℕ) → c-searchable (T n) (cs n))
           → ((n : ℕ) → continuous-c-searcher (cs n) (Ss n))
           → ((p , d) : d-predicate (Π T))
           → (δ : ℕ) → δ is-u-mod-of p on (Π-codistance (T , cs))
           → Σ x₀ ꞉ Π T , (Σ p → p x₀)

tychonoff (T , cs) ss Ss ccs (p , d , δ , ϕ) = tychonoff' (T , cs) ss Ss ccs (p , d) δ ϕ

tail-predicate2 : {T : ℕ → 𝓤₀ ̇ }
                → ((p , d) : d-predicate (Π T))
                → (x : T 0) → d-predicate (Π (T ∘ succ))
tail-predicate2 (p , d) x = (λ xs → p (x ∷ xs)) , (λ xs → d (x ∷ xs))

build-up2 : ((T , cs) : sequence-of-codistance-types)
          → ((n : ℕ) → is-clofun (cs n))
          → (xs ys : Π (T ∘ succ)) → (δ : ℕ)
          → (δ ↑) ≼ Π-codistance (T ∘ succ , cs ∘ succ) (xs , ys)
          → (x : T 0)
          → (succ δ ↑) ≼ Π-codistance (T , cs) (x ∷ xs , x ∷ ys)
build-up2 (T , cs) ss xs ys δ δ≼cxsys x 0 refl
 = ap (λ - → pr₁ - 0) (is-clofun.equal→inf-close (ss 0) x)
build-up2 (T , cs) ss xs ys δ δ≼cxsys x (succ n) r
 = Lemma[a≡₁→b≡₁→min𝟚ab≡₁]
    (ap (λ - → pr₁ - (succ n)) (is-clofun.equal→inf-close (ss 0) x))
    (δ≼cxsys n r)

tail-predicate2-reduce-mod : ((T , cs) : sequence-of-codistance-types)
                           → (ss : (n : ℕ) → is-clofun (cs n))
                           → ((p , d) : d-predicate (Π T))
                           → (x : T 0) → (δ : ℕ)
                           → (succ δ) is-u-mod-of p on Π-codistance (T , cs)
                           →       δ  is-u-mod-of pr₁ (tail-predicate2 (p , d) x)
                                                  on Π-codistance ((T ∘ succ) , (cs ∘ succ))
tail-predicate2-reduce-mod (T , cs) ss (p , d) x δ ϕ (xs , ys) δ≼cxsys
 = ϕ (x ∷ xs , x ∷ ys) (build-up2 (T , cs) ss xs ys δ δ≼cxsys x)

its-continuous : ((T , cs) : sequence-of-codistance-types)
               → (ss : (n : ℕ) → is-clofun (cs n))
               → (Ss : (n : ℕ) → c-searchable (T n) (cs n))
               → (ccs : (n : ℕ) → continuous-c-searcher (cs n) (Ss n))
               → continuous-c-searcher (Π-codistance (T , cs)) (tychonoff (T , cs) ss Ss ccs)
its-continuous (T , cs) ss Ss ccs cx pds 0 ϕ ε x₁ x₂ δ≼cx₁x₂
 = {!!} -- transport ((ε ↑) ≼_) (is-clofun.equal→inf-close (Π-codistance-is-codistance (T , cs) ss) ? ⁻¹) (∞-maximal (ε ↑))
its-continuous (T , cs) ss Ss ccs cx pds (succ δ) ϕ ε x₁ x₂ δ≼cx₁x₂ = {!!}

head-predicate2 : ((T , cs) : sequence-of-codistance-types)
                → ((n : ℕ) → is-clofun (cs n))
                → (Ss : (n : ℕ) → c-searchable (T n) (cs n))
                → ((n : ℕ) → continuous-c-searcher (cs n) (Ss n))
                → ((p , d) : d-predicate (Π T))
                → (δ : ℕ) → succ δ is-u-mod-of p on (Π-codistance (T , cs))
                → uc-d-predicate (T 0) (cs 0)
head-predicate2 (T , cs) ss Ss ccs (p , d) δ ϕ = pₕ , dₕ , succ δ , ϕₕ
 where
   𝓔xs : T 0 → Π (T ∘ succ)
   𝓔xs x = pr₁ (tychonoff' (T ∘ succ , cs ∘ succ) (ss ∘ succ) (Ss ∘ succ) (ccs ∘ succ)
            (tail-predicate2 (p , d) x) δ
            (tail-predicate2-reduce-mod (T , cs) ss (p , d) x δ ϕ))
   pₕ = λ x → p (x ∷ 𝓔xs x)
   dₕ = λ x → d (x ∷ 𝓔xs x)
   ϕₕ : succ δ is-u-mod-of pₕ on cs 0
   ϕₕ (x , y) δ≼cxy pₕxs = ϕ (x ∷ 𝓔xs x , y ∷ 𝓔xs y) γ pₕxs where
     ζ : (     δ ↑) ≼ Π-codistance (T ∘ succ , cs ∘ succ) (𝓔xs x , 𝓔xs y)
     ζ = its-continuous (T ∘ succ , cs ∘ succ) (ss ∘ succ) (Ss ∘ succ) (ccs ∘ succ)
           (cs 0)
           (tail-predicate2 (p , d)) δ
           (λ x' → tail-predicate2-reduce-mod (T , cs) ss (p , d) x' δ ϕ)
           δ x y ζ'' where
       ζ'' : (δ ↑) ≼ cs 0 (x , y)
       ζ'' 0 r = δ≼cxy 0 refl
       ζ'' (succ n) r = δ≼cxy (succ n) (pr₂ (δ ↑) n r)
     γ : (succ δ ↑) ≼ Π-codistance (T , cs) ((x ∷ 𝓔xs x) , (y ∷ 𝓔xs y))
     γ 0 r = δ≼cxy 0 r
     γ (succ n) r = Lemma[a≡₁→b≡₁→min𝟚ab≡₁] (δ≼cxy (succ n) r) (ζ n r)
     
tychonoff' (T , cs) ss Ss ccs (p , d) 0 ϕ = α , (λ (x₀ , px₀) → γ (x₀ , px₀) α)
 where
   α = λ n → c-searchable-types-are-inhabited (cs n) (Ss n)
   γ : Σ p → Π p
   γ = 0-mod-always-satisfied (Π-codistance (T , cs)) (p , d) ϕ

tychonoff' (T , cs) ss Ss ccs (p , d) (succ δ) ϕ = α , γ where
  pₕ = pr₁ (head-predicate2 (T , cs) ss Ss ccs (p , d) δ ϕ)
  pₜ = λ x' → pr₁ (tail-predicate2 (p , d) x')

  S-head = Ss 0 (head-predicate2 (T , cs) ss Ss ccs (p , d) δ ϕ)

  IH-tail = λ x' → tychonoff' (T ∘ succ , cs ∘ succ) (ss ∘ succ) (Ss ∘ succ) (ccs ∘ succ)
                     (tail-predicate2 (p , d) x') δ
                       (tail-predicate2-reduce-mod (T , cs) ss (p , d) x' δ ϕ)

  x : T 0
  x = pr₁ S-head

  γₕ : Σ pₕ → pₕ x
  γₕ = pr₂ S-head -- pr₂ S-head

  𝓔xs : T 0 → Π (T ∘ succ)
  𝓔xs x' = pr₁ (IH-tail x')

  γₜ : (x' : T 0) → Σ (pₜ x') → (pₜ x') (𝓔xs x')
  γₜ x' = pr₂ (IH-tail x')

  α = x ∷ 𝓔xs x

  γ : Σ p → p α
  γ (α₀ , pα₀) = step₆ where

    x₀  = α₀ 0
    xs₀ = α₀ ∘ succ

    step₁ : p (x₀ ∷ xs₀)
    step₁ = transport p (head-tail-eta2 α₀) pα₀

    step₂ : (pₜ x₀) xs₀
    step₂ = step₁

    step₃ : (pₜ x₀) (𝓔xs x₀)
    step₃ = γₜ x₀ (xs₀ , step₂)

    step₄ : pₕ x₀
    step₄ = step₃

    step₅ : pₕ x
    step₅ = γₕ (x₀ , step₄)

    step₆ : p (x ∷ 𝓔xs x)
    step₆ = step₅
