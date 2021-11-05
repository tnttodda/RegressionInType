{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

open import Prelude
open import UF-FunExt
open import SignedDigit
open import GenericConvergentSequence
open import DiscreteAndSeparated
open import NaturalsOrder
open import Two-Properties

module Codistances (fe : FunExt) where

open import Codistance fe
open sequences

×-codistance : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
             → (X → X → ℕ∞) → (Y → Y → ℕ∞)
             → (X × Y → X × Y → ℕ∞)
×-codistance cx cy (x₁ , y₁) (x₂ , y₂) = min (cx x₁ x₂) (cy y₁ y₂)

×ⁿ-codistance : {X : 𝓤 ̇ } → (X → X → ℕ∞)
              → (n : ℕ) → (X ^⟨succ n ⟩ → X ^⟨succ n ⟩ → ℕ∞)
×ⁿ-codistance cx 0 = cx
×ⁿ-codistance cx (succ n)
  = ×-codistance cx (×ⁿ-codistance cx n)
  
data Vec (A : 𝓤 ̇ ) : ℕ → 𝓤 ̇ where
  [] : Vec A 0
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (succ n)

first-_ : {A : 𝓥 ̇ } (n : ℕ) → (ℕ → A) → Vec A n
(first- 0) a = []
(first- succ n) a = head a ∷ (first- n) (tail a)

min-of-Vec : {n : ℕ} → Vec 𝟚 (succ n) → 𝟚
min-of-Vec (x ∷ []) = x
min-of-Vec (x ∷ (x' ∷ xs)) = min𝟚 x (min-of-Vec (x' ∷ xs))

vec-of-seq : (n i : ℕ) → i ≤ n → Vec (ℕ × ℕ) (succ i)
vec-of-seq n        0        x = (n , 0) ∷ []
vec-of-seq (succ n) (succ i) x = (n , succ i)
                               ∷ vec-of-seq (succ n) i (≤-trans i n (succ n) x (≤-succ n))

map-vec : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {n : ℕ} → (A → B) → Vec A n → Vec B n
map-vec f [] = []
map-vec f (x ∷ xs) = (f x) ∷ (map-vec f xs)

Π-codistance' : {T : ℕ → 𝓤 ̇ }
              → ((n : ℕ) → T n → T n → (ℕ → 𝟚))
              → Π T → Π T → (ℕ → 𝟚)
Π-codistance' cs F G n = min-of-Vec (map-vec (uncurry α) β)
 where
   α = λ n i → cs n (F n) (G n) i
   β = vec-of-seq n n (≤-refl n)

Π-codistance'' : {T : ℕ → 𝓤 ̇ }
               → ((n : ℕ) → T n → T n → (ℕ → 𝟚))
               → Π T → Π T → (ℕ → 𝟚)
Π-codistance'' cs F G 0 = cs 0 (F 0) (G 0) 0
Π-codistance'' {𝓤} {T} cs F G (succ n)
 = min𝟚 (cs 0 (F 0) (G 0) (succ n))
        (Π-codistance'' (cs ∘ succ) (F ∘ succ) (G ∘ succ) n)

-- Π-codistance' Tc (F , G) n = (α n 0) (α (n - 1) 1) (α (n - 2) 2) ...

Π-decreasing : {T : ℕ → 𝓤 ̇ }
             → (cs : (n : ℕ) → T n → T n → (ℕ → 𝟚))
             → (ds : (n : ℕ) (x y : T n) → decreasing (cs n x y))
             → (F G : Π T) → decreasing (Π-codistance'' cs F G)
Π-decreasing cs ds F G zero r = ds 0 (F 0) (G 0) 0 (Lemma[min𝟚ab≡₁→a≡₁] r)
Π-decreasing cs ds F G (succ n) r
 = Lemma[a≡₁→b≡₁→min𝟚ab≡₁]
     (ds 0 (F 0) (G 0) (succ n)
       (Lemma[min𝟚ab≡₁→a≡₁] r))
     (Π-decreasing (cs ∘ succ) (ds ∘ succ) (F ∘ succ) (G ∘ succ) n
       (Lemma[min𝟚ab≡₁→b≡₁] {cs 0 (F 0) (G 0) (succ (succ n))} {_} r))

Π-codistance : {T : ℕ → 𝓤 ̇ }
             → ((n : ℕ) → T n → T n → ℕ∞)
             → Π T → Π T → ℕ∞
Π-codistance cs F G = Π-codistance'' (λ n x y → pr₁ (cs n x y)) F G
                    , Π-decreasing (λ n x y → pr₁ (cs n x y)) (λ n x y → pr₂ (cs n x y)) F G

_::_ : {T : ℕ → 𝓤 ̇ } → T 0 → Π (λ n → T (succ n)) → Π T
(x :: xs) 0 = x 
(x :: xs) (succ n) = xs n

Π-identical : {T : ℕ → 𝓤 ̇ }
            → (cs : (n : ℕ) → T n → T n → ℕ∞)
            → ((n : ℕ) (x : T n) (i : ℕ) → pr₁ (cs n x x) i ≡ ₁)
            → (xs : Π T)
            → (m : ℕ)
            → under m ≼ Π-codistance cs xs xs
Π-identical cs es xs m zero r = es 0 (xs 0) 0
Π-identical cs es xs (succ m) (succ n) r
 = Lemma[a≡₁→b≡₁→min𝟚ab≡₁]
     (es 0 (xs 0) (succ n))
     (Π-identical (cs ∘ succ) (es ∘ succ) (xs ∘ succ) m n r)

Π-equivalent : {T : ℕ → 𝓤 ̇ }
             → (cs : (n : ℕ) → T n → T n → ℕ∞)
             → ((n : ℕ) (x : T n) (i : ℕ) → pr₁ (cs n x x) i ≡ ₁)
             → (xs : Π T)
             → (m : ℕ)
             → under m ≼ Π-codistance cs xs ((xs 0) :: (xs ∘ succ))
Π-equivalent cs es xs m zero r = es 0 (xs 0) 0
Π-equivalent cs es xs (succ m) (succ n) r = Π-identical cs es xs (succ m) (succ n) r

Π-codistance-Succ : {T : ℕ → 𝓤 ̇ }
                  → (cs : (n : ℕ) → T n → T n → ℕ∞)
                  → ((x : T 0) (i : ℕ) → pr₁ (cs 0 x x) i ≡ ₁)
                  → (x : T 0) (xs₁ xs₂ : (n : ℕ) → T (succ n)) (m : ℕ)
                  → under m ≼ Π-codistance (cs ∘ succ) xs₁ xs₂
                  → Succ (under m) ≼ Π-codistance cs (x :: xs₁) (x :: xs₂)
Π-codistance-Succ cs e x xs₁ xs₂ m m≼cxs zero refl = e x 0
Π-codistance-Succ cs e x xs₁ xs₂ m m≼cxs (succ n) r = Lemma[a≡₁→b≡₁→min𝟚ab≡₁] (e x (succ n)) (m≼cxs n r)

≈→≼ : {X : 𝓤 ̇ } (d≡ : is-discrete X) (x y : ℕ → X) (ε : ℕ)
    → (x ≈ y) ε → under ε ≼ codistance X d≡ x y
≈→≼ {𝓤} {X} d≡ x y ε x≈y n n⊏ε
 = codistance-conceptually₁ X d≡ x y n
     (λ k k≤n → Cases (<-split k n k≤n)
       (λ k<n → x≈y k (<-trans k n ε k<n
         (⊏-gives-< n ε n⊏ε)))
       (λ k≡n → x≈y k (transport (λ - → succ - ≤ ε) (k≡n ⁻¹)
         (⊏-gives-< n ε n⊏ε))))

≼→≈ : {X : 𝓤 ̇ } (d≡ : is-discrete X) (x y : ℕ → X) (ε : ℕ)
    → under ε ≼ codistance X d≡ x y → (x ≈ y) ε
≼→≈ {𝓤} {X} d≡ x y (succ ε) ε≼cxy
 = codistance-conceptually₂ X d≡ x y ε (ε≼cxy ε (under-diagonal₁ ε))

uc-mod-of² : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
           → (X → X → ℕ∞) → (Y → Y → ℕ∞)
           → (X → Y) → ℕ → ℕ → 𝓤 ̇
uc-mod-of² cx cy f ε δ
 = ∀ x y → (under δ) ≼ (cx x y) → (under ε) ≼ (cy (f x) (f y))

continuous² : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
            → (X → X → ℕ∞) → (Y → Y → ℕ∞)
            → (X → Y) → 𝓤 ̇
continuous² cx cy f = ∀ ε → Σ (uc-mod-of² cx cy f ε)

uc-mod-of : {X : 𝓤 ̇ } → (X → X → ℕ∞) → (X → 𝓥 ̇ ) → ℕ → 𝓤 ⊔ 𝓥 ̇
uc-mod-of c p δ = ∀ x y → (under δ) ≼ (c x y) → p x → p y

continuous : {X : 𝓤 ̇ } → (X → X → ℕ∞) → (X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
continuous c p = Σ (uc-mod-of c p)

everywhere-sin : {Y : 𝓤 ̇ } → (Y → Y → ℕ∞) → 𝓤 ̇
everywhere-sin cy = ∀ x → Π (_⊏ cy x x)

right-continuous : {Y : 𝓤 ̇ } → (Y → Y → ℕ∞) → 𝓤 ̇
right-continuous {𝓤} {Y} c
 = (ε : ℕ) → ((z x y : Y)
           → under ε ≼ c x y
           → (incl (c z x) ≈ incl (c z y)) ε)

×-codistance-min : {X : 𝓤 ̇ } {Y : 𝓤' ̇ }
                 → (cx : X → X → ℕ∞) → (cy : Y → Y → ℕ∞)
                 → (m : ℕ∞) (x₁ x₂ : X) (y₁ y₂ : Y)
                 → m ≼ cx x₁ x₂ → m ≼ cy y₁ y₂
                 → m ≼ (×-codistance cx cy) (x₁ , y₁) (x₂ , y₂)
×-codistance-min cx cy m x₁ x₂ y₁ y₂ m≼cx m≼cy n p
 = Lemma[a≡₁→b≡₁→min𝟚ab≡₁] (m≼cx n p) (m≼cy n p)

×-codistance-min' : {X : 𝓤 ̇ } {Y : 𝓤' ̇ }
                  → (cx : X → X → ℕ∞) (cy : Y → Y → ℕ∞)
                  → (m : ℕ∞) (x₁ x₂ : X) (y₁ y₂ : Y)
                  → m ≼ (×-codistance cx cy) (x₁ , y₁) (x₂ , y₂)
                  → m ≼ cx x₁ x₂ × m ≼ cy y₁ y₂
×-codistance-min' cx cy m x₁ x₂ y₁ y₂ m≼cxy
 = (λ n r → Lemma[min𝟚ab≡₁→a≡₁] (m≼cxy n r))
 , (λ n r → Lemma[min𝟚ab≡₁→b≡₁] (m≼cxy n r))

→-everywhere-sin : {X : 𝓤 ̇ } (d≡ : is-discrete X)
                 → everywhere-sin (codistance X d≡)
→-everywhere-sin {𝓤} {X} d≡ x n
 = transport (n ⊏_) (γ ⁻¹) (∞-⊏-maximal n)
 where
  γ : codistance X d≡ x x ≡ ∞
  γ = pr₁ (pr₂ (ℕ→D-has-codistance X d≡)) x

→-right-continuous : {X : 𝓤 ̇ } (d≡ : is-discrete X)
                   → right-continuous (codistance X d≡)
→-right-continuous {𝓤} {X} d≡ ε z x y ε≼cxy 0 0<ε
 = Cases (d≡ (head z) (head x))
    (λ h → ap (λ - → incl - 0) (codistance-eq₁ X d≡ z x h)
         ∙ ap (λ - → incl - 0) (codistance-eq₁ X d≡ z y
             (h ∙ hx≡hy) ⁻¹))
   (λ ¬h → ap (λ - → incl - 0) (codistance-eq₀ X d≡ z x ¬h)
         ∙ ap (λ - → incl - 0) (codistance-eq₀ X d≡ z y
             (λ z≡y → ¬h (z≡y ∙ hx≡hy ⁻¹)) ⁻¹))
 where
  hx≡hy : head x ≡ head y
  hx≡hy = ≼→≈ d≡ x y ε ε≼cxy 0 0<ε
→-right-continuous {𝓤} {X} d≡ (succ ε) z x y ε≼cxy (succ k) k<ε
 = Cases (d≡ (head z) (head x))
     (λ h → ap (λ - → incl - (succ k)) (codistance-eq₁ X d≡ z x h)
          ∙ IH
          ∙ ap (λ - → incl - (succ k)) (codistance-eq₁ X d≡ z y
              (h ∙ hx≡hy) ⁻¹))
    (λ ¬h → ap (λ - → incl - (succ k)) (codistance-eq₀ X d≡ z x ¬h)
          ∙ ap (λ - → incl - (succ k)) (codistance-eq₀ X d≡ z y
              (λ z≡y → ¬h (z≡y ∙ hx≡hy ⁻¹)) ⁻¹))
 where
  x≈y : (x ≈ y) (succ ε)
  x≈y = ≼→≈ d≡ x y (succ ε) ε≼cxy
  hx≡hy : head x ≡ head y
  hx≡hy = x≈y 0 *
  IH = →-right-continuous d≡ ε (tail z) (tail x) (tail y)
         (≈→≼ d≡ (tail x) (tail y) ε (λ n n<ε → x≈y (succ n) n<ε))
         k k<ε

×-everywhere-sin : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                 → (cx : X → X → ℕ∞) (cy : Y → Y → ℕ∞)
                 → everywhere-sin cx
                 → everywhere-sin cy
                 → everywhere-sin (×-codistance cx cy)
×-everywhere-sin cx cy cx→ cy→ (x , y) n
 = Lemma[a≡₁→b≡₁→min𝟚ab≡₁] (cx→ x n) (cy→ y n)

×ⁿ-everywhere-sin : {X : 𝓤 ̇ }
                 → (cx : X → X → ℕ∞) (n : ℕ)
                 → everywhere-sin cx
                 → everywhere-sin (×ⁿ-codistance cx n)
×ⁿ-everywhere-sin cx 0 = id
×ⁿ-everywhere-sin cx (succ n) cx→
 = ×-everywhere-sin cx (×ⁿ-codistance cx n) cx→
     (×ⁿ-everywhere-sin cx n cx→)

×-right-continuous
               : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
               → (cx : X → X → ℕ∞) (cy : Y → Y → ℕ∞)
               → right-continuous cx
               → right-continuous cy
               → right-continuous (×-codistance cx cy)
×-right-continuous cx cy cx-r cy-r ε
 (z₁ , z₂) (x₁ , x₂) (y₁ , y₂) ε≼cxy k k<ε
 = min𝟚-abcd (cx-r ε z₁ x₁ y₁ (pr₁ γ) k k<ε)
             (cy-r ε z₂ x₂ y₂ (pr₂ γ) k k<ε)
 where
   γ = ×-codistance-min' cx cy (under ε) x₁ y₁ x₂ y₂ ε≼cxy

×ⁿ-right-continuous : {X : 𝓤 ̇ } 
                    → (cx : X → X → ℕ∞) (n : ℕ)
                    → right-continuous cx
                    → right-continuous (×ⁿ-codistance cx n)
×ⁿ-right-continuous cx 0 = id
×ⁿ-right-continuous cx (succ n) cx-r
 = ×-right-continuous cx (×ⁿ-codistance cx n)
     cx-r (×ⁿ-right-continuous cx n cx-r)
