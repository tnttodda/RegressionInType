Todd Waugh Ambridge, 17th November 2021

Search over uniformly continuous decidable predicates on infinite collections of types.

Related reading: "Infinite sets that admit fast exhaustive search" (Escardó, LICS 2007)

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Prelude hiding (decidable)
open import NaturalsOrder
open import DecidableAndDetachable
open import GenericConvergentSequence
open import Two-Properties hiding (_≥₂_)
open import UF-Subsingletons
open import DiscreteAndSeparated
open import UF-Base
open import UF-FunExt
open import UF-Subsingletons
open import UF-Subsingletons-FunExt

module InfiniteSearch1 (fe : {𝓤 𝓥 : Universe} → {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {f g : Π Y} → f ∼ g → f ≡ g) where

\end{code}

In LICS 2007, a type X is called searchable if, given any predicate p : X → {tt,ff},
we have some x₀ : X such that p(x₀) ≡ tt if and only if p is satisfied by at least
one such x : X.

This definition can be written in constructive type theory by using a boolean type
or, as we do here, using decidable predicates.

A type X is decidable if we can decide whether we have a construction of X or ¬ X.

A type family p : X → 𝓤₀ on a type X is decidable if it is everywhere decidable.
In univalent foundations, we often call a truncated type family a predicate.
For the purposes of this work, we do not use truncation, and refer to any type
family as a predicate as they play the role of Boolean-valued predicates in
LICS 2007.

\begin{code}

predicate : (X : 𝓤 ̇ ) → (𝓤₀ ⁺) ⊔ 𝓤 ̇
predicate X = X → 𝓤₀ ̇ 

decidable : 𝓤 ̇ → 𝓤 ̇
decidable X = X + ¬ X

everywhere-decidable : {X : 𝓤 ̇} → predicate X → 𝓤 ̇
everywhere-decidable {𝓤} {X} p = Π x ꞉ X , decidable (p x)

d-predicate : 𝓤 ̇ → (𝓤₀ ⁺) ⊔ 𝓤 ̇
d-predicate X = Σ p ꞉ (X → 𝓤₀ ̇ ) , everywhere-decidable p

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

The type of Boolean values 𝟚 ≔ {₀,₁} is searchable by the following argument:
 * Using decidability, we ask if ₁ satisfies the predicate p being searched,
   i.e. we ask if (p ₁) is inhabited.
 * If (p ₁) is inhabited, then we return ₁ -- thus, trivially, if there is some
   x₀ : 𝟚 such that (p x₀) then also (p ₁).
 * If (p ₁) is uninhabited (i.e. we have a function of type ¬ (p ₁) ≔ (p ₁) → 𝟘)
   then we return ₀ -- given some x₀ : 𝟚 such that (p x₀) we prove that
   (p ₀) by case analysis of x₀.
   *  If x₀ = ₀ then (p ₀) is inhabited.
   *  If x₀ = ₁ then (p ₁) is inhabited. This case is absurd, however, as we
      already showed that (p ₁) is uninhabited. We discard this case using the
      elimination rule of the empty type 𝟘.

\begin{code}

𝟚-is-searchable : searchable 𝟚
𝟚-is-searchable (p , d) = γ (d ₁) where
  γ : decidable (p ₁) → Σ x₀ ꞉ 𝟚 , (Σ p → p x₀)
  γ (inl p₁) = ₁ , (λ _ → p₁)
  γ (inr f ) = ₀ , δ where
    δ : Σ p → p ₀
    δ (₀ , p₀) = p₀
    δ (₁ , p₁) = 𝟘-elim (f p₁)

\end{code}

Searchability of the natural numbers, however, is a constructive taboo and is
equivalent to the limited principle of omniscience (LPO).

LPO states that, given any infinite sequence of binary numbers, either all
are ₀ or we have some n : ℕ such that (f n) ≡ ₁.

We define LPO' below, which implies LPO.

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
⦅ TODO : Finish ⦆

However, although the Haskell program presumably terminates given any predicate,
formalising this program in Agda is more subtle. By implicitly assuming the
predicate to be searched is uniformly continuous, Agda's termination checker
fails on the proof that ℕ → 𝟚 is uniformly continuous. This can be seen in the
file 'CountableTychonoff', which has the termination checker turned off, and
hence is an 'unsafe' module.

We instead require a specific definition of a 'uniformly continuous predicate'
over ℕ → 𝟚. This is relatively straightforward:

\begin{code}

_≡⟦_⟧_ : {X : 𝓤 ̇ } → (ℕ → X) → ℕ → (ℕ → X) → 𝓤 ̇
α ≡⟦ m ⟧ β = Π k ꞉ ℕ , (k ≤ m → α k ≡ β k)

is-u-continuous-𝟚ᴺ : ((ℕ → 𝟚) → 𝓤₀ ̇ ) → 𝓤₀ ̇
is-u-continuous-𝟚ᴺ p = Σ m ꞉ ℕ , ((α β : ℕ → 𝟚) → α ≡⟦ m ⟧ β → p α → p β)

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

_≥₂_ : 𝟚 → 𝟚 → 𝓤₀ ̇
a ≥₂ b = b ≡ ₁ → a ≡ ₁

decreasing-binary-seq : (ℕ → 𝟚) → 𝓤₀ ̇
decreasing-binary-seq α = Π n ꞉ ℕ , α n ≥₂ α (succ n)

ℕ∞̇ : 𝓤₀ ̇ 
ℕ∞̇ = Σ decreasing-binary-seq

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

repeat : {X : 𝓤 ̇ } → X → (ℕ → X)
repeat x = λ n → x

_↑ : ℕ → ℕ∞̇
0      ↑ = repeat ₀       , (λ n ₀≡₁ → ₀≡₁)
succ n ↑ = ₁ :: pr₁ (n ↑) , γ
 where
   γ : decreasing-binary-seq (₁ :: pr₁ (n ↑))
   γ 0 _ = refl
   γ (succ k) = pr₂ (n ↑) k
   
∞̇ : ℕ∞̇
∞̇ = repeat ₁ , (λ n ₁≡₁ → ₁≡₁)

\end{code}

Given two extended naturals α , β : ℕ∞̇,
α ≼̇ β if everywhere α has 1s β also has 1s.

Given any α : ℕ∞, clearly (0 ↑) ≼ α and α ≼ ∞.

\begin{code}

_≼̇_ : ℕ∞̇ → ℕ∞̇ → 𝓤₀ ̇
(α , _) ≼̇ (β , _) = Π n ꞉ ℕ , (α n ≡ ₁ → β n ≡ ₁)

0-minimal : (α : ℕ∞̇) → (0 ↑) ≼̇ α
0-minimal α k ()

∞̇-maximal : (α : ℕ∞̇) → α ≼̇ ∞̇  
∞̇-maximal α k αₖ≡₁ = refl

\end{code}

A binary function c : X × X → ℕ∞ is a codistance function
if it satisfies the below.

\begin{code}

record has-codistance (X : 𝓤 ̇ ) : 𝓤 ̇ where
  field
    c : X × X → ℕ∞̇ 
    equal-are-infinitely-close : (x     : X) → c (x , x) ≡ ∞̇
    infinitely-close-are-equal : (x y   : X) → c (x , y) ≡ ∞̇ → x ≡ y
    symmetricity : (x y   : X) → c (x , y) ≡ c (y , x)
    ultrametric : (x y z : X) → min (c (x , y)) (c (y , z)) ≼̇ c (x , z)

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
discrete-c' (x , y) (inl x≡y) = ∞̇
discrete-c' (x , y) (inr x≢y) = 0 ↑

discrete-c'-eic : {X : 𝓤 ̇ } → (x : X)
                → (dxx : decidable (x ≡ x))
                → discrete-c' (x , x) dxx ≡ ∞̇
discrete-c'-eic x (inl x≡x) = refl
discrete-c'-eic x (inr x≢x) = 𝟘-elim (x≢x refl)

discrete-c'-ice : {X : 𝓤 ̇ } → (x y : X)
                      → (dxy : decidable (x ≡ y))
                      → discrete-c' (x , y) dxy ≡ ∞̇ → x ≡ y
discrete-c'-ice x y (inl x≡y) cxy≡∞ = x≡y
discrete-c'-ice x y (inr x≢y) cxy≡∞ = 𝟘-elim (Zero-not-∞ cxy≡∞)
 where
   Zero-not-∞ : (0 ↑) ≢ ∞̇
   Zero-not-∞ 0≡∞ = 𝟘-elim (zero-is-not-one (ap (λ - → pr₁ - 0) 0≡∞))
                                 
discrete-c'-sym : {X : 𝓤 ̇ } → (x y : X)
                → (dxy : decidable (x ≡ y))
                → (dyx : decidable (y ≡ x))
                → discrete-c' (x , y) dxy ≡ discrete-c' (y , x) dyx
discrete-c'-sym x y (inl x≡y) (inl y≡x) = refl
discrete-c'-sym x y (inr x≢y) (inr y≢x) = refl
discrete-c'-sym x y (inl x≡y) (inr y≢x) = 𝟘-elim (y≢x (x≡y ⁻¹))
discrete-c'-sym x y (inr x≢y) (inl y≡x) = 𝟘-elim (x≢y (y≡x ⁻¹))
                                           
discrete-c'-ult : {X : 𝓤 ̇ } → (x y z : X)
                → (dxy : decidable (x ≡ y))
                → (dyz : decidable (y ≡ z))
                → (dxz : decidable (x ≡ z))
                → min (discrete-c' (x , y) dxy) (discrete-c' (y , z) dyz)
                     ≼̇ discrete-c' (x , z) dxz
discrete-c'-ult x  y  z       _          _    (inl  _ ) _ _ = refl
discrete-c'-ult x  y  z (inl  _  ) (inr  _  ) (inr  _ ) _   = id
discrete-c'-ult x  y  z (inr  _  )       _    (inr  _ ) _   = id
discrete-c'-ult x .x .x (inl refl) (inl refl) (inr x≢x)     = 𝟘-elim (x≢x refl)

discrete-codistance : {X : 𝓤 ̇ } → is-discrete X → (X × X → ℕ∞̇)
discrete-codistance d (x , y) = discrete-c' (x , y) (d x y)

discrete-is-codistance : {X : 𝓤 ̇ } → is-discrete X → has-codistance X
has-codistance.c   (discrete-is-codistance ds)
 = discrete-codistance ds
has-codistance.equal-are-infinitely-close (discrete-is-codistance ds) x
 = discrete-c'-eic x     (ds x x)
has-codistance.infinitely-close-are-equal (discrete-is-codistance ds) x y
 = discrete-c'-ice x y   (ds x y)
has-codistance.symmetricity               (discrete-is-codistance ds) x y
 = discrete-c'-sym x y   (ds x y) (ds y x)
has-codistance.ultrametric                (discrete-is-codistance ds) x y z
 = discrete-c'-ult x y z (ds x y) (ds y z) (ds x z)

\end{code}

The codistance function for a type (ℕ → D) where D is discrete is defined
by induction as follows:

  c (α , β) n ≡ ₁,    if x ≡⟦ n ⟧ y,
                ₀,    otherwise.

Its definition, and the proof that it is a codistance, can be seen in the
file "Codistance.lagda".

\begin{code}

discrete-seq-c'' : {X : 𝓤 ̇ } → ((α , β) : (ℕ → X) × (ℕ → X))
                 → (n : ℕ) → decidable (α ≡⟦ n ⟧ β) → 𝟚
discrete-seq-c'' (α , β) n (inl α≡⟦n⟧β) = ₁
discrete-seq-c'' (α , β) n (inr α≡⟦n⟧β) = ₀

discrete-decidable-seq : {X : 𝓤 ̇ } → is-discrete X
                       → (α β : ℕ → X) → (n : ℕ) → decidable (α ≡⟦ n ⟧ β)
discrete-decidable-seq d α β 0 = Cases (d (α 0) (β 0)) (inl ∘ γₗ) (inr ∘ γᵣ)
 where
   γₗ : α 0 ≡ β 0 → α ≡⟦ 0 ⟧ β
   γₗ e 0 _ = e
   γᵣ : ¬ (α 0 ≡ β 0) → ¬ (α ≡⟦ 0 ⟧ β)
   γᵣ f α≡⟦0⟧β = 𝟘-elim (f (α≡⟦0⟧β 0 *))
discrete-decidable-seq d α β (succ n)
 = Cases (discrete-decidable-seq d α β n) γ₁ (inr ∘ γ₂)
 where
   γ₁ : α ≡⟦ n ⟧ β → decidable (α ≡⟦ succ n ⟧ β)
   γ₁ α≈β = Cases (d (α (succ n)) (β (succ n))) (inl ∘ γₗ) (inr ∘ γᵣ)
    where
      γₗ : α (succ n) ≡ β (succ n) → α ≡⟦ succ n ⟧ β
      γₗ e k k≤n = Cases (≤-split k n k≤n)
                     (λ k≤n  → α≈β k k≤n)
                     (λ k≡sn → transport (λ - → α - ≡ β -) (k≡sn ⁻¹) e)
      γᵣ : ¬ (α (succ n) ≡ β (succ n)) → ¬ (α ≡⟦ succ n ⟧ β)
      γᵣ g α≡⟦sn⟧β = g (α≡⟦sn⟧β (succ n) (≤-refl n))
   γ₂ : ¬ (α ≡⟦ n ⟧ β) → ¬ (α ≡⟦ succ n ⟧ β)
   γ₂ f = f ∘ (λ α≈β k k≤n → α≈β k (≤-trans k n (succ n) k≤n (≤-succ n)))

discrete-seq-c' : {X : 𝓤 ̇ } → is-discrete X → (α β : ℕ → X) → (ℕ → 𝟚)
discrete-seq-c' d α β n = discrete-seq-c'' (α , β) n (discrete-decidable-seq d α β n)

decreasing1 : {X : 𝓤 ̇ } → (α β : ℕ → X) → ∀ n d₁ d₂
            → (discrete-seq-c'' (α , β) n d₁ ≥₂ discrete-seq-c'' (α , β) (succ n) d₂)
decreasing1 α β n (inl _) (inl _) _ = refl
decreasing1 α β n (inl _) (inr _) _ = refl
decreasing1 α β n (inr x) (inl x₁) refl
 = 𝟘-elim (x (λ k k<n → x₁ k (≤-trans k n (succ n) k<n (≤-succ n))))
decreasing1 α β n (inr _) (inr _) = 𝟘-elim ∘ zero-is-not-one

discrete-seq-codistance : {X : 𝓤 ̇ } → is-discrete X → ((ℕ → X) × (ℕ → X) → ℕ∞̇)
discrete-seq-codistance d (α , β)
 = discrete-seq-c' d α β 
 , λ n → decreasing1 α β n (discrete-decidable-seq d α β n)
                           (discrete-decidable-seq d α β (succ n))

codistance→stream : {X : 𝓤 ̇ } → (ds : is-discrete X)
                  → (α β : ℕ → X) → (n : ℕ)
                  → (succ n ↑) ≼̇ discrete-seq-codistance ds (α , β)
                  → α ≡⟦ n ⟧ β
codistance→stream ds α β n cαβ≼n = γ (discrete-decidable-seq ds α β n) (cαβ≼n n (all-n n))
 where
   γ : (d : decidable (α ≡⟦ n ⟧ β)) → discrete-seq-c'' (α , β) n d ≡ ₁ → α ≡⟦ n ⟧ β
   γ (inl α≡⟦n⟧β) _ = α≡⟦n⟧β
   all-n : (n : ℕ) → pr₁ (succ n ↑) n ≡ ₁
   all-n 0        = refl
   all-n (succ n) = all-n n

stream→codistance : {X : 𝓤 ̇ } → (ds : is-discrete X)
                  → (α β : ℕ → X) → (n : ℕ)
                  → α ≡⟦ n ⟧ β
                  → (succ n ↑) ≼̇ discrete-seq-codistance ds (α , β)
stream→codistance ds α β n α≡⟦n⟧β k nₖ≡₁ = γ (discrete-decidable-seq ds α β k)
 where
   n≼ : (k n : ℕ) → pr₁ (n ↑) k ≡ ₁ → k < n
   n≼ 0        (succ n) nₖ≡₁ = *
   n≼ (succ k) (succ n) nₖ≡₁ = n≼ k n nₖ≡₁
   γ : (d : decidable (α ≡⟦ k ⟧ β)) → discrete-seq-c'' (α , β) k d ≡ ₁
   γ (inl  α≡⟦k⟧β) = refl
   γ (inr ¬α≡⟦k⟧β)
    = 𝟘-elim (¬α≡⟦k⟧β (λ i i≤k → α≡⟦n⟧β i (≤-trans i k n i≤k (n≼ k (succ n) nₖ≡₁))))
   
\end{code}

⦅ TODO: Now we show this is a codistance (substitute proofs in from Codistance.lagda) ⦆

\begin{code}

𝟚-is-set : (a b : 𝟚) → is-prop (a ≡ b)
𝟚-is-set ₀ ₀ refl refl = refl
𝟚-is-set ₁ ₁ refl refl = refl

Π-is-prop2 : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } → ((x : X) → is-prop (Y x)) → is-prop (Π Y)
Π-is-prop2 Y-is-prop f g = fe (λ x → Y-is-prop x (f x) (g x))

≥₂-is-prop : (a b : 𝟚) → is-prop (a ≥₂ b)
≥₂-is-prop a b = Π-is-prop2 (λ _ → 𝟚-is-set a ₁)

decreasing-prop : (α : ℕ → 𝟚) → is-prop (decreasing-binary-seq α)
decreasing-prop α = Π-is-prop2 (λ n → ≥₂-is-prop (α n) (α (succ n)))

seq-equals : {X : 𝓤 ̇ } {α β : ℕ → X} → α ∼ β → α ≡ β
seq-equals α∼β = fe α∼β

sigma-prop-equals : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
             → {(x₁ , y₁) (x₂ , y₂) : Σ x ꞉ X , Y x}
             → x₁ ≡ x₂
             → ((x : X) → is-prop (Y x))
             → (x₁ , y₁) ≡ (x₂ , y₂)
sigma-prop-equals {𝓤} {𝓥} {X} {Y} {(x₁ , Yx₁)} {(.x₁ , Yx₂)} refl Y-is-prop
 = ap (x₁ ,_) (Y-is-prop x₁ Yx₁ Yx₂)

ℕ∞-equals : {(α , α-dec) (β , β-dec) : ℕ∞̇} → α ∼ β → (α , α-dec) ≡ (β , β-dec)
ℕ∞-equals α∼β = sigma-prop-equals (seq-equals α∼β) decreasing-prop

\end{code}

\begin{code}

discrete-seq-c''-eic : {X : 𝓤 ̇ } → (α : ℕ → X)
                     → (n : ℕ) → (d : decidable (α ≡⟦ n ⟧ α))
                     → discrete-seq-c'' (α , α) n d ≡ ₁
discrete-seq-c''-eic α n (inl  α≡⟦n⟧α) = refl
discrete-seq-c''-eic α n (inr ¬α≡⟦n⟧α) = 𝟘-elim (¬α≡⟦n⟧α (λ k k≤n → refl))

discrete-seq-c''-ice : {X : 𝓤 ̇ } → (α β : ℕ → X)
                     → (n : ℕ) → (d : decidable (α ≡⟦ n ⟧ β))
                     → discrete-seq-c'' (α , β) n d ≡ ₁
                     → α n ≡ β n
discrete-seq-c''-ice α β n (inl  α≡⟦n⟧β) cαβn≡₁ = α≡⟦n⟧β n (≤-refl n)
discrete-seq-c''-ice α β n (inr ¬α≡⟦n⟧β) ()

discrete-seq-c''-sym : {X : 𝓤 ̇ } (α β : ℕ → X)
                     → (n : ℕ) → (d₁ : decidable (α ≡⟦ n ⟧ β))
                                 (d₂ : decidable (β ≡⟦ n ⟧ α))
                     → discrete-seq-c'' (α , β) n d₁ ≡ discrete-seq-c'' (β , α) n d₂
discrete-seq-c''-sym x y n (inl  α≡⟦n⟧β) (inl  β≡⟦n⟧α) = refl
discrete-seq-c''-sym x y n (inr ¬α≡⟦n⟧β) (inr ¬β≡⟦n⟧α) = refl
discrete-seq-c''-sym x y n (inl  α≡⟦n⟧β) (inr ¬β≡⟦n⟧α)
 = 𝟘-elim (¬β≡⟦n⟧α (λ k k<n → α≡⟦n⟧β k k<n ⁻¹))
discrete-seq-c''-sym x y n (inr ¬α≡⟦n⟧β) (inl  β≡⟦n⟧α)
 = 𝟘-elim (¬α≡⟦n⟧β (λ k k<n → β≡⟦n⟧α k k<n ⁻¹))

discrete-seq-c''-ult : {X : 𝓤 ̇ } (α β η : ℕ → X)
                     → (n : ℕ) → (d₁ : decidable (α ≡⟦ n ⟧ β))
                               → (d₂ : decidable (β ≡⟦ n ⟧ η))
                               → (d₃ : decidable (α ≡⟦ n ⟧ η))
                     → min𝟚 (discrete-seq-c'' (α , β) n d₁)
                            (discrete-seq-c'' (β , η) n d₂) ≡ ₁
                     → discrete-seq-c'' (α , η) n d₃ ≡ ₁
discrete-seq-c''-ult α β η n _             _             (inl  α≡⟦n⟧η) _ = refl
discrete-seq-c''-ult α β η n (inl α≡⟦n⟧β)  (inl  β≡⟦n⟧η) (inr ¬α≡⟦n⟧η) min≡₁
 = 𝟘-elim (¬α≡⟦n⟧η (λ k k<n → α≡⟦n⟧β k k<n ∙ β≡⟦n⟧η k k<n))
discrete-seq-c''-ult α β η n (inl  α≡⟦n⟧β) (inr ¬β≡⟦n⟧α) (inr ¬α≡⟦n⟧η) min₁₀≡₁
 = 𝟘-elim (zero-is-not-one min₁₀≡₁)
discrete-seq-c''-ult α β η n (inr ¬α≡⟦n⟧β) (inl  β≡⟦n⟧α) (inr ¬α≡⟦n⟧η) min₀₁≡₁
 = 𝟘-elim (zero-is-not-one min₀₁≡₁)
discrete-seq-c''-ult α β η n (inr ¬α≡⟦n⟧β) (inr ¬β≡⟦n⟧α) (inr ¬α≡⟦n⟧η) min₀₀≡₁
 = 𝟘-elim (zero-is-not-one min₀₀≡₁)

discrete-seq-has-codistance : {X : 𝓤 ̇ } → is-discrete X → has-codistance (ℕ → X)
has-codistance.c (discrete-seq-has-codistance ds) = discrete-seq-codistance ds
has-codistance.equal-are-infinitely-close (discrete-seq-has-codistance ds) α
 = ℕ∞-equals (λ n → discrete-seq-c''-eic α n (discrete-decidable-seq ds α α n))
has-codistance.infinitely-close-are-equal (discrete-seq-has-codistance ds) α β cαβ≡∞
 = fe (λ n → discrete-seq-c''-ice α β n (discrete-decidable-seq ds α β n) (γ n))
 where
   γ : (n : ℕ) → discrete-seq-c'' (α , β) n (discrete-decidable-seq ds α β n) ≡ ₁
   γ n = ap (λ - → pr₁ - n) cαβ≡∞
has-codistance.symmetricity (discrete-seq-has-codistance ds) α β
 = ℕ∞-equals (λ n → discrete-seq-c''-sym α β n (discrete-decidable-seq ds α β n)
                                               (discrete-decidable-seq ds β α n))
has-codistance.ultrametric (discrete-seq-has-codistance ds) α β η
 = λ n → discrete-seq-c''-ult α β η n (discrete-decidable-seq ds α β n)
                                      (discrete-decidable-seq ds β η n)
                                      (discrete-decidable-seq ds α η n)

important : {X : 𝓤 ̇  } → (ds : is-discrete X)
          → (α : ℕ → X) → discrete-seq-codistance ds (α , (α 0 :: (α ∘ succ))) ≡ ∞̇
important ds α = ap (λ - → discrete-seq-codistance ds (α , -)) (fe γ)
               ∙ has-codistance.equal-are-infinitely-close (discrete-seq-has-codistance ds) α
 where
   γ : (α 0 :: (α ∘ succ)) ∼ α
   γ 0 = refl
   γ (succ n) = refl

\end{code}

* 2 searchable
* searchable -> continuous searchable
* ? continuously searchable + discrete = searchable
* discrete searchable sequence searchable

\begin{code}

_is-u-mod-of_on_ : {X : 𝓤 ̇ } → ℕ → predicate X → (X × X → ℕ∞) → 𝓤 ̇ 
_is-u-mod-of_on_ {𝓤} {X} δ p c = Π (x , y) ꞉ (X × X) , ((δ ↑) ≼ c (x , y) → p x → p y)

u-continuous : {X : 𝓤 ̇ } → (X × X → ℕ∞) → predicate X → 𝓤 ̇
u-continuous {𝓤} {X} c p = Σ δ ꞉ ℕ , δ is-u-mod-of p on c 

uc-d-predicate : (X : 𝓤 ̇ ) → (X × X → ℕ∞) → (𝓤₀ ⁺) ⊔ 𝓤 ̇
uc-d-predicate X c = Σ p ꞉ predicate X , everywhere-decidable p × u-continuous c p

c-searchable : (X : 𝓤 ̇ ) → (X × X → ℕ∞) → (𝓤₀ ⁺) ⊔ 𝓤 ̇
c-searchable X c = Π (p  , _) ꞉ uc-d-predicate X c , Σ x₀ ꞉ X , (Σ p → p x₀)

searchable→c-searchable : {X : 𝓤 ̇ } → (c : X × X → ℕ∞) → searchable X → c-searchable X c
searchable→c-searchable c S (p , d , ϕ) = S (p , d)

all-discrete-predicates-are-continuous : {X : 𝓤 ̇ } → (ds : is-discrete X) → d-predicate X
                                       → uc-d-predicate X (discrete-codistance ds)
all-discrete-predicates-are-continuous {𝓤} {X} ds (p , d)
 = p , d , (1 , λ (x , y) → γ x y (ds x y))
 where
   γ : (x y : X) → (q : decidable (x ≡ y)) → (1 ↑) ≼̇ discrete-c' (x , y) q → p x → p y
   γ x .x (inl refl) 1≼∞ px = px
   γ x  y (inr  _  ) 1≼0 _  = 𝟘-elim (zero-is-not-one (1≼0 0 refl))

c-searchable-discrete→searchable : {X : 𝓤 ̇ } → (ds : is-discrete X)
                                 → c-searchable X (discrete-codistance ds) → searchable X
c-searchable-discrete→searchable ds S (p , d)
 = S (all-discrete-predicates-are-continuous ds (p , d))

→c-searchable : {X : 𝓤 ̇ } → (ds : is-discrete X) → c-searchable X (discrete-codistance ds)
              → c-searchable (ℕ → X) (discrete-seq-codistance ds)

→c-searchable' : {X : 𝓤 ̇ } → (ds : is-discrete X) → c-searchable X (discrete-codistance ds)
               → ((p , d) : d-predicate (ℕ → X))
               → (δ : ℕ) → δ is-u-mod-of p on (discrete-seq-codistance ds)
               → Σ x₀ ꞉ (ℕ → X) , (Σ p → p x₀) 
→c-searchable ds S (p , d , δ , ϕ) = →c-searchable' ds S (p , d) δ ϕ

trivial-predicate : {X : 𝓤 ̇ } → (c : X × X → ℕ∞) → uc-d-predicate X c
trivial-predicate c = (λ _ → 𝟙) , (λ _ → inl *) , (0 , λ x y 0≼cxy → *)

build-up : {X : 𝓤 ̇ } → (ds : is-discrete X) → (xs ys : ℕ → X) → (δ : ℕ)
         → (δ ↑) ≼̇ discrete-seq-codistance ds (xs , ys)
         → (x : X)
         → (succ δ ↑) ≼̇ discrete-seq-codistance ds (x :: xs , x :: ys)
build-up {𝓤} {X} ds xs ys δ δ≼cxsys x
 = stream→codistance ds (x :: xs) (x :: ys) δ (γ δ δ≼cxsys)
 where
   γ : (δ : ℕ) → (δ ↑) ≼̇ discrete-seq-codistance ds (xs , ys)
     → (x :: xs) ≡⟦ δ ⟧ (x :: ys)
   γ δ δ≼cxsys 0        *   = refl
   γ (succ δ) δ≼cxsys (succ k) k≤n = codistance→stream ds xs ys δ δ≼cxsys k k≤n
  
head-tail-eta : {X : 𝓤 ̇ } → (xs : ℕ → X) → xs ≡ xs 0 :: (xs ∘ succ)
head-tail-eta xs = fe γ where
  γ : xs ∼ xs 0 :: (xs ∘ succ)
  γ 0 = refl
  γ (succ n) = refl

tail-predicate : {X : 𝓤 ̇ } → (ds : is-discrete X) → c-searchable X (discrete-codistance ds)
               → ((p , d) : d-predicate (ℕ → X))
               → (δ : ℕ) → (succ δ) is-u-mod-of p on (discrete-seq-codistance ds)
               → (x : X)
               → Σ (pₜ , dₜ) ꞉ d-predicate (ℕ → X)
                             , δ is-u-mod-of pₜ on (discrete-seq-codistance ds)
tail-predicate {𝓤} {X} ds S (p , d) δ ϕ x = ((λ xs → p (x :: xs)) , (λ xs → d (x :: xs)))
                                          , λ (xs , ys) δ≼cxsys → ϕ (x :: xs , x :: ys)
                                             (build-up ds xs ys δ δ≼cxsys x)

head-predicate : {X : 𝓤 ̇ } → (ds : is-discrete X) → c-searchable X (discrete-codistance ds)
               → ((p , d) : d-predicate (ℕ → X))
               → (δ : ℕ) → (succ δ) is-u-mod-of p on (discrete-seq-codistance ds)
               → uc-d-predicate X (discrete-codistance ds)
head-predicate {𝓤} {X} ds S (p , d) δ ϕ
 = all-discrete-predicates-are-continuous ds ((λ x → p (x :: xs x)) , (λ x → d (x :: xs x)))
 where
   xs : X → ℕ → X
   xs x = pr₁ (→c-searchable' ds S (pr₁ (tail-predicate ds S (p , d) δ ϕ x))
           δ (pr₂ (tail-predicate ds S (p , d) δ ϕ x)))

→c-searchable' ds S (p , d) zero ϕ = xs , λ (ys , pys) → ϕ (ys , xs) (λ _ ()) pys where
  xs = λ n → pr₁ (S (trivial-predicate (discrete-codistance ds)))

→c-searchable' ds S (p , d) (succ δ) ϕ = (x :: xs) , γ where
  x = pr₁ (S (head-predicate ds S (p , d) δ ϕ))
  IH = λ y → tail-predicate ds S (p , d) δ ϕ y
  xs = pr₁ (→c-searchable' ds S (pr₁ (IH x)) δ (pr₂ (IH x)))
  γ : Σ p → p (x :: xs)
  γ (ys , pys) = pr₂ (S (head-predicate ds S (p , d) δ ϕ))
                (ys 0 , pr₂ (→c-searchable' ds S (pr₁ (IH (ys 0))) δ (pr₂ (IH (ys 0))))
                (ys ∘ succ , transport p (head-tail-eta ys) pys))

ℕ→𝟚-is-searchable : c-searchable (ℕ → 𝟚) (discrete-seq-codistance 𝟚-is-discrete)
ℕ→𝟚-is-searchable
 = →c-searchable 𝟚-is-discrete
     (searchable→c-searchable (discrete-codistance 𝟚-is-discrete) 𝟚-is-searchable)

\end{code}
