Todd Waugh Ambridge, 17th November 2021

Search over uniformly continuous decidable predicates on infinite collections of types.

Related reading: "Infinite sets that admit fast exhaustive search" (Escardó, LICS 2007)

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Prelude hiding (decidable)
open import NaturalsOrder
open import DecidableAndDetachable
open import GenericConvergentSequence
open import Two-Properties
open import UF-Subsingletons
open import DiscreteAndSeparated

module InfiniteSearch where

\end{code}

In LICS 2007, a type X is called searchable if, given any predicate p : X → {tt,ff},
we have some x₀ : X such that p(x₀) ≡ tt if and only if p is satisfied by at least
one such x : X.

This definition can be written in constructive type theory by using a boolean type
or, as we do here, using decidable predicates.

A type X is decidable if we can decide whether we have a construction of X or ¬ X.

A predicate p : X → 𝓤₀ on a type X is decidable if it is everywhere decidable.

\begin{code}

decidable : 𝓤 ̇ → 𝓤 ̇
decidable X = X + ¬ X

d-predicate : 𝓤 ̇ → (𝓤₀ ⁺) ⊔ 𝓤 ̇
d-predicate X = Σ p ꞉ (X → 𝓤₀ ̇ ) , (Π x ꞉ X , decidable (p x))

\end{code}

A type is therefore searchable if, given any decidable predicate, we can construct
x₀ : X such that, if there is some x : X such that p(x), then p(x₀).

\begin{code}

searchable : 𝓤 ̇ → (𝓤₀ ⁺) ⊔ 𝓤 ̇
searchable X = Π (p , _) ꞉ d-predicate X , Σ x₀ ꞉ X , (Σ p → p x₀)

\end{code}

From any searchable type we can construct its 'searcher' 𝓔, a functional that
returns the construction x₀ : X, which satisfies the above condition.

\begin{code}

𝓔⟨_⟩ : {X : 𝓤 ̇ } → searchable X → d-predicate X → X
𝓔⟨ S ⟩ (p , d) = pr₁ (S (p , d))

γ⟨_⟩ : {X : 𝓤 ̇ } (S : searchable X) ((p , d) : d-predicate X)
     → Σ p → p (𝓔⟨ S ⟩ (p , d))
γ⟨ S ⟩ (p , d) = pr₂ (S (p , d))

\end{code}

The notion of searchability coincides with that of compactness. This can be seen
fully in the file "CompactTypes.lagda" by Escardó, where the above construction is
equivalent to that named 'compact∙' in that file.

Any finite type is trivially searchable, as are finite products and co-products of
searchable types.

Searchability of the natural numbers, however, is a constructive taboo and is
equivalent to the limited principle of omniscience.

\begin{code}

LPO  : 𝓤₀ ̇
LPO  = Π f ꞉ (ℕ → 𝟚)             , (Σ n ꞉ ℕ , f n ≡ ₁) + (Π n ꞉ ℕ , f n ≡ ₀)

LPO' : 𝓤₁ ̇
LPO' = Π (p , d) ꞉ d-predicate ℕ , (Σ n ꞉ ℕ , p n)     + (Π n ꞉ ℕ , ¬ (p n))

ℕ-searchable-implies-LPO : searchable ℕ → LPO'
ℕ-searchable-implies-LPO S (p , d) = Cases (d x₀) (inl ∘ left) (inr ∘ right)
 where
  x₀ : ℕ
  x₀ = 𝓔⟨ S ⟩ (p , d)
  γ₀ : Σ p → p (𝓔⟨ S ⟩ (p , d))
  γ₀ = γ⟨ S ⟩ (p , d)
  left  :    p x₀  → Σ x ꞉ ℕ ,   p x
  left   px₀      = x₀ , px₀
  right : ¬ (p x₀) → Π x ꞉ ℕ , ¬ p x
  right ¬px₀ x px = ¬px₀ (γ₀ (x , px))
  
LPO-implies-ℕ-searchable : LPO' → searchable ℕ
LPO-implies-ℕ-searchable L (p , d) = Cases (L (p , d)) left right
 where
  left  : Σ x ꞉ ℕ ,   p x → Σ x₀ ꞉ ℕ , (Σ p → p x₀)
  left  (x₀ , px₀) = x₀ , λ _ → px₀
  right : Π x ꞉ ℕ , ¬ p x → Σ x₀ ꞉ ℕ , (Σ p → p x₀)
  right f = 0 , (λ (x , px) → 𝟘-elim (f x px))
  

\end{code}

Perhaps surprisingly however, there are some infinite types that are searchable.
The "seemingly impossible functional program", written in Haskell, searches
predicates on the Cantor type ℕ → 𝟚.

The magic here is in fact performed by continuity! In System T (?), every
predicate p over ℕ → 𝟚 is uniformly continuous, and therefore only a finite
prefix of ??? is required to construct a finite
prefix of α₀ : ℕ → 𝟚 satisfying Σ p → p α₀. 

However, although the Haskell program presumably terminates given any predicate,
formalising this program in Agda is more subtle. By implicitly assuming the
predicate to be searched is uniformly continuous, Agda's termination checker
fails on the proof that ℕ → 𝟚 is continuous. This can be seen in the file
'CountableTychonoff', which has the termination checker turned off, and hence
is an 'unsafe' module.

We instead require a specific definition of a 'continuous predicate' over ℕ → 𝟚.
This is relatively straightforward:

\begin{code}

_≡⟦_⟧_ : {X : 𝓤 ̇ } → (ℕ → X) → ℕ → (ℕ → X) → 𝓤 ̇
α ≡⟦ m ⟧ β = Π k ꞉ ℕ , (k ≤ m → α ≡ β)

is-continuous-𝟚ᴺ : ((ℕ → 𝟚) → 𝓤₀ ̇ ) → 𝓤₀ ̇
is-continuous-𝟚ᴺ p = Σ m ꞉ ℕ , ((α β : ℕ → 𝟚) → α ≡⟦ m ⟧ β → p α → p β)

\end{code}

The file "CantorSearch" uses this explicit definition of uniform continuity
to prove that ℕ → 𝟚 is searchable on such explicitly-defined uniformly
continuous predicates. 

Using the definition of uniform continuity as above, this can be easily
extended to any type of infinite sequences ℕ → D where D is a discrete type.

However, as searchable types coincide with the concept of compactness, we want
a full-blown constructive formalisation of the Tychonoff theorem:

Theorem (Tychonoff).
   Given T : ℕ → 𝓤 is a family of types indexed by the natural numbers, such
   that every (T n) : 𝓤 is searchable, the type (Π T) : 𝓤 is searchable.

This theorem of course implies that types ℕ → D are searchable; but in order
to prove the Tychonoff theorem we need a much more general definition of
uniform continuity that does not require the types (T n) to be disrete.

We now introduce the idea of a coultrametric type. This is a type X equipped
with a binary function c : X × X → ℕ∞.

ℕ∞ is the type of extended natural numbers (i.e. ℕ extended with a point at
infinity), encoded as decreasing infinitary binary sequences.

\begin{code}

ℕ∞̇ : 𝓤₀ ̇ 
ℕ∞̇ = Σ α ꞉ (ℕ → 𝟚) , (Π n ꞉ ℕ , α n ≥₂ α (succ n))

\end{code}

Any natural number n : ℕ can be mapped to an extended natural k ↑ : ℕ∞,
which is the sequence with k-many 1s followed by infinitely-many 0s.

  e.g. 5 ↑ ≡ 111110000000...

∞ : ℕ∞ is represented as the sequence with infinitely-many 1s.

  i.e. ∞   ≡ 111111111111...

\begin{code}

_::_ : {X : 𝓤 ̇ } → X → (ℕ → X) → (ℕ → X)
(x :: xs) 0        = x
(x :: xs) (succ n) = xs n

_↑ : ℕ → ℕ∞̇
0      ↑ = (λ _ → ₀)
         , (λ _ → id)
succ n ↑ = (₁ :: pr₁ (n ↑))
         , induction (λ _ → refl) (λ i _ → pr₂ (n ↑) i)

∞̇ : ℕ∞̇
∞̇ = (λ _ → ₁) , (λ _ _ → refl)

\end{code}

Given two extended naturals α , β : ℕ∞̇,
α ≼̇ β if everywhere α has 1s β also has 1s.

\begin{code}

_≼̇_ : ℕ∞̇ → ℕ∞̇ → 𝓤₀ ̇
(α , _) ≼̇ (β , _) = Π n ꞉ ℕ , (α n ≡ ₁ → β n ≡ ₁)

\end{code}

A binary function c : X × X → ℕ∞ is a codistance function
if it satisfies the below.

\begin{code}

is-codistance : {X : 𝓤 ̇ } → (X × X → ℕ∞̇) → 𝓤 ̇
is-codistance {𝓤} {X} c
  = ((x     : X) → c (x , x) ≡ ∞̇)
  × ((x y   : X) → c (x , y) ≡ ∞̇ → x ≡ y)
  × ((x y   : X) → c (x , y) ≡ c (y , x))
  × ((x y z : X) → min (c (x , y)) (c (y , z)) ≼̇ c (x , z))

\end{code}

This function measures the 'closeness' of the two provided
constructions of X. In this sense, it is the dual of a metric.

Such a function is a codistance function if it satisfies:
 (1) A construction is infinitely close to itself
      ∀ x → c (x , x) ≡ ∞

 (2) Constructions that are infinite close are equal
      ∀ x y → c (x , y) ≡ ∞ → x ≡ y

 (3) Symmetricity
      ∀ x y → c (x , y) ≡ c (y , x)

 (4) Triangle ultrametric property
      ∀ x y z → min (c (x , y)) (c (y , z)) ≼ c (x , z)

From these properties, we can see clearly the relationship with a metric.
In fact, an ultrametric (a metric with a generalised triangle equality
property) can be defined from a coultrametric easily:

  m : X × X → ℝ
  m (x , y) ≡ 2̂^{ − c(x , y) }

Where, as usual, 2^{−∞} ≡ 0.

More detail on codistances is given in the file "Codistance.lagda";
for now, we briely introduce the discrete codistance and the
discrete-sequence codistance.

The codistance function for a discrete type is defined easily by cases:
                  
  c (x , y) ≡   ∞    if x ≡ y
                0 ↑  otherwise

\begin{code}

discrete-c' : {X : 𝓤 ̇ } → ((x , y) : X × X) → decidable (x ≡ y) → ℕ∞̇
discrete-c' (x , y) (inl _) = ∞̇
discrete-c' (x , y) (inr _) = 0 ↑

discrete-codistance : {X : 𝓤 ̇ } → is-discrete X → (X × X → ℕ∞̇)
discrete-codistance d (x , y) = discrete-c' (x , y) (d x y)

discrete-is-codistance : {X : 𝓤 ̇ } → (d : is-discrete X)
                       → is-codistance (discrete-codistance d)
pr₁ (discrete-is-codistance {𝓤} {X} d) x
 = γ x     (d x x)
  where
    γ : ∀ x d → discrete-c' (x , x) d ≡ ∞̇
    γ x (inl  _ ) = refl
    γ x (inr x≢x) = 𝟘-elim (x≢x refl)
pr₁ (pr₂ (discrete-is-codistance {𝓤} {X} d)) x y
 = γ x y   (d x y) 
  where
    γ : ∀ x y d → discrete-c' (x , y) d ≡ ∞̇ → x ≡ y
    γ x .x (inl refl) _      = refl
    γ x  y (inr  _  ) Zero≡∞ = 𝟘-elim (zero-is-not-one
                                 (ap (λ - → pr₁ - 0) Zero≡∞))
pr₁ (pr₂ (pr₂ (discrete-is-codistance {𝓤} {X} d))) x y
 = γ x y   (d x y) (d y x)
  where
    γ : ∀ x y d₁ d₂ → discrete-c' (x , y) d₁ ≡ discrete-c' (y , x) d₂
    γ x  y (inl  _  ) (inl  _  ) = refl
    γ x  y (inr  _  ) (inr  _  ) = refl
    γ x .x (inl refl) (inr x≢x ) = 𝟘-elim (x≢x refl)
    γ x .x (inr x≢x ) (inl refl) = 𝟘-elim (x≢x refl)
pr₂ (pr₂ (pr₂ (discrete-is-codistance {𝓤} {X} d))) x y z
 = γ x y z (d x y) (d y z) (d x z)
  where
    γ : ∀ x y z d₁ d₂ d₃ → min (discrete-c' (x , y) d₁) (discrete-c' (y , z) d₂)
                              ≼̇ discrete-c' (x , z) d₃
    γ x  y  z       _           _     (inl  _  ) _ _ = refl
    γ x  y  z (inl  _   ) (inr  _   ) (inr  _  ) _   = id
    γ x  y  z (inr  _   )       _     (inr  _  ) _   = id
    γ x .x .x (inl refl ) (inl refl ) (inr x≢x )     = 𝟘-elim (x≢x refl)

\end{code}

The codistance function for a type (ℕ → D) where D is discrete is defined
by induction as follows:

  c (α , β) n ≡ ₁    if x ≡⟦ n ⟧ y
                ₀    otherwise

\begin{code}

discrete-seq-c'' : {X : 𝓤 ̇ } → (α β : ℕ → X) → (n : ℕ) → decidable (α ≡⟦ n ⟧ β) → 𝟚
discrete-seq-c'' α β n (inl _) = ₁
discrete-seq-c'' α β n (inr _) = ₀

discrete-decidable-seq : {X : 𝓤 ̇ } → is-discrete X → (α β : ℕ → X) → (n : ℕ) → decidable (α ≡⟦ n ⟧ β)
discrete-decidable-seq d α β zero = {!!}
discrete-decidable-seq d α β (succ n) = {!!}

discrete-seq-c' : {X : 𝓤 ̇ } → is-discrete X → (α β : ℕ → X) → (ℕ → 𝟚)
discrete-seq-c' d α β n = discrete-seq-c'' α β n (discrete-decidable-seq d α β n)

discrete-seq-codistance : {X : 𝓤 ̇ } → is-discrete X → ((ℕ → X) × (ℕ → X) → ℕ∞̇)
discrete-seq-codistance d (α , β) = δ , γ where
  δ : ℕ → 𝟚
  δ = discrete-seq-c' d α β
  γ : Π n ꞉ ℕ , (δ n ≥₂ δ (succ n))
  γ n δsn≡₁ = {!!}
