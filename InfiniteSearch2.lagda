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
                           → (ss : (n : ℕ) → satisfies-codistance-properties (cs n))
                           → satisfies-codistance-properties (Π-codistance (T , cs))
                           
satisfies-codistance-properties.equal-are-infinitely-close
 (Π-codistance-is-codistance (T , cs) ss)
 = Π-codistance'-eic (T , cs)
     (λ n → satisfies-codistance-properties.equal-are-infinitely-close (ss n))
     
satisfies-codistance-properties.infinitely-close-are-equal
 (Π-codistance-is-codistance (T , cs) ss)
 = λ A B f → Π-codistance'-ice (T , cs)
     (λ n (α , β) → satisfies-codistance-properties.infinitely-close-are-equal (ss n) α β)
     (A , B) f
 
satisfies-codistance-properties.symmetricity
 (Π-codistance-is-codistance (T , cs) ss)
 = λ A B → Π-codistance'-sym (T , cs)
     (λ n (α , β) → satisfies-codistance-properties.symmetricity (ss n) α β)
     (A , B)

satisfies-codistance-properties.ultrametric
 (Π-codistance-is-codistance (T , cs) ss)
 = λ A B C → Π-codistance'-ult (T , cs)
     (λ n (α , β , ζ) → satisfies-codistance-properties.ultrametric (ss n) α β ζ)
     (A , B , C)

tychonoff : ((T , cs) : sequence-of-codistance-types)
          → ((n : ℕ) → c-searchable (T n) (cs n))
          → c-searchable (Π T) (Π-codistance (T , cs))
tychonoff = {!!}
