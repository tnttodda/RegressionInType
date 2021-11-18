{-# OPTIONS --without-K --exact-split --safe #-}

module Interval where

open import Prelude
open import NaturalsOrder
open import DecidableAndDetachable

[_,_] : ℕ → ℕ → 𝓤₀ ̇
[ a , b ] = Σ n ꞉ ℕ , (a ≤ b) × (a ≤ n) × (n ≤ b)

a b : [ 1 , 2 ]
a = 1 , _
b = 2 , _

+-split : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → decidable Y → X → X → X
+-split (inl _) a _ = a
+-split (inr _) _ b = b

𝓔' : (p : ℕ → 𝓤 ̇) (d : detachable p) (a b : ℕ) → (d₁ : (a < b) + (a ≡ b)) (d₂ : decidable (p b))
   → ℕ
𝓔' p d a 0 _ _ = 0
𝓔' p d a (succ b) (inr _) _ = succ b
𝓔' p d a (succ b) (inl _) (inl _) = succ b
𝓔' p d a (succ b) (inl a≤b) (inr _) = 𝓔' p d a b (<-split a b a≤b) (d b)

γ' : (p : ℕ → 𝓤 ̇) (d : detachable p) (a b : ℕ) → (d₁ : (a < b) + (a ≡ b)) (d₂ : decidable (p b))
   → ((n , _) : [ a , b ]) → p n
  → p (𝓔' p d a b d₁ d₂)
γ' p d a 0 d₁ d₂ (0 , _) = id
γ' p d a (succ b) (inl _) (inl pb) _ _ = pb
γ' p d a (succ b) (inl a≤b) (inr ¬psb) (n , a≤sb , a≤n , n≤sb) pn
 = γ' p d a b (<-split a b a≤b) (d b) (n , a≤b , a≤n , ≤-down n b n≤sb n≢sb) pn
 where
   n≢sb : n ≢ succ b
   n≢sb n≡sb = ¬psb (transport p n≡sb pn)
γ' p d .(succ b) (succ b) (inr refl) d₂ (succ n , _ , b≤n , n≤b)
 = transport p (ap succ (≤-anti n b n≤b b≤n))

𝓔 : (p : ℕ → 𝓤 ̇ ) → detachable p → (a b : ℕ) → a ≤ b → ℕ
𝓔 p d a b a≤b = 𝓔' p d a b (<-split a b a≤b) (d b)

γ : (p : ℕ → 𝓤 ̇ ) (d : detachable p) (a b : ℕ) → (a≤b : a ≤ b)
  → ((x₀ , _) : [ a , b ]) → p x₀
  → p (𝓔 p d a b a≤b)
γ p d a 0 _ (0 , _) = id
γ p d a (succ b) a≤b = γ' p d a (succ b) (≤-split a b a≤b) (d (succ b))

open import NaturalsAddition renaming (_+_ to _+ℕ_)

data ℤ : 𝓤₀ ̇ where
  +_ : ℕ → ℤ
  −1−_ : ℕ → ℤ

data ℤprint : 𝓤₀ ̇ where
  +_ : ℕ → ℤprint
  −_ : ℕ → ℤprint

print : ℤ → ℤprint
print (+ n) = + n
print (−1− n) = − (succ n)

to : ℤprint → ℤ
to (+ n) = + n
to (− 0) = + 0
to (− succ n) = −1− n

succℤ : ℤ → ℤ
succℤ (+ n) = + succ n
succℤ (−1− 0) = + 0
succℤ (−1− succ n) = −1− n

doubleℕ : ℕ → ℕ
doubleℕ n = n +ℕ n

double : ℤ → ℤ
double (+ n) = + (doubleℕ n)
double (−1− n) = −1− (doubleℕ n +ℕ 1)

Interval : 𝓤₀ ̇ 
Interval = ℤ × ℤ

downLeft downRight : Interval → Interval
downLeft (c , p) = (double c , succℤ p) -- incorrect
downRight (c , p) = (succℤ (succℤ (double c)) , succℤ p) -- incorrect

Real : 𝓤₀ ̇
Real = ℕ → Interval

IntToReal : ℤ → Real
IntToReal z 0 = (double z , + 0)
IntToReal z (succ p) = downLeft (IntToReal z p)
