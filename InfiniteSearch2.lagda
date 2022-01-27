Search over uniformly continuous decidable predicates on infinite collections of types. (Part 2)

Todd Waugh Ambridge, 17th January 2022

\begin{code}

{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

open import SpartanMLTT hiding (decidable)
open import NaturalsOrder
open import Two-Properties hiding (_≥₂_;zero-is-not-one)
open import GenericConvergentSequence hiding (ℕ∞;∞;_≼_;∞-maximal)

module InfiniteSearch2 (fe : {𝓤 𝓥 : Universe} → {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {f g : Π Y} → f ∼ g → f ≡ g) where

open import InfiniteSearch1 fe
  hiding ( head ; tail
         ; _::_ ; head-tail-eta
         ; tail-predicate
         ; tail-predicate-reduce-mod
         ; head-predicate
         ; build-up
         ; 𝟚-is-c-searchable)

\end{code}

Table of Contents:
 1. Introduce Π and Π-clofun
 . Reintroduce concepts from previous and (Exercise for reader?)
    show this is the same as previous discrete-seq-clofun
 3. Show Π-clofun satisfies all the properties
 4. First attempt and continuity condition
 5. Tychonoff theorem
 6. Corollaries

**Overview:**

In my previous blog post, I layed the groundwork necessary to safely formalise
the Tychonoff theorem in constructive type theory.

I re-introduced the notion of searchable types -- types X that exhibit a selection
function that, given any predicate, return an element of X satisfying the predicate
if at least one such element exists. I also introduced the notion of closeness
functions; our version of metrics that allow us to define uniformly continuous
decidable predicates. A type is continuously searchable if we can exhibit a selection
function that works on all uniformly continuous predicates.

We now turn our attention to formalising the Tyconoff theorem for searchable types that
have a closeness function. Another version of the Tychonoff theorem for searchable types
has been previously formalised by Martín Escardó with Agda’s termination checker turned off;
the addition of closeness functions allows the proof to terminate, but adds extra
steps to it as we must prove that everything is continuous.

**A closeness function for Π-types**

In topology, the Tychonoff theorem states that arbitrary products of compact spaces
are themselves compact. As searchable types coincide with the concept of compactness,
and infinite products are constructed using the Π-type, we restate the Tychonoff theorem
using our two key notions of continuous searchability and closeness functions:

Theorem (Tychonoff). Given a family of types indexed by the natural numbers T : ℕ → 𝓤,
such that every (T n) : 𝓤 is continuously searchable and is equipped with a closeness
function of type T n × T n → ℕ∞, the type Π T : 𝓤 ̇ is continuously searchable.

Of course, in order to prove Π T can be continuously searchable, we must first
provide a closeness function for that type.

An infinite sequence of types, each with a closeness function, is defined
as follows.

\begin{code}

sequence-of-clofun-types : 𝓤₁ ̇ 
sequence-of-clofun-types = Σ T ꞉ (ℕ → 𝓤₀ ̇ ) , Π n ꞉ ℕ , (T n × T n → ℕ∞)

\end{code}

We generalise the composition, head and tail operations to infinite sequence of types.

\begin{code}

_::_ : {T : ℕ → 𝓤 ̇ } → T 0 → Π (T ∘ succ) → Π T
(x :: xs) 0 = x
(x :: xs) (succ n) = xs n

head : {T : ℕ → 𝓤₀ ̇ } → Π T → T 0
head α = α 0

tail : {T : ℕ → 𝓤 ̇ } → Π T → Π (T ∘ succ)
tail α = α ∘ succ

head-tail-eta : {T : ℕ → 𝓤₀ ̇ } → (α : Π T) → α ≡ head α :: tail α
head-tail-eta α = fe γ where
  γ : α ∼ (head α :: tail α)
  γ 0 = refl
  γ (succ n) = refl

\end{code}

We want to determine the closeness c(α , β) : ℕ∞ of two infinite sequences α,β : Π T.

It is straightforward to define this where each type (T n) : 𝓤 is discrete
(i.e. each closeness function cₙ : T n × T n → ℕ∞ is the discrete closeness function).

  c (α , β) n ≡ ₁,    if x ≡⟦ n ⟧ y,
                ₀,    otherwise.

This is the "discrete-sequence" closeness function defined in the previous blog post.

But how can we determine c(α , β) : ℕ∞ when nothing is assumed about each cₙ, apart
from that they satisfy the four properties of closeness functions?

First, note that we can compute cₙ(α n , β n) : ℕ∞ for every n : ℕ.
The following illustrates some potential values of a prefix of these
closeness functions.

For example, the asterisk * : 𝟚 is defined * ≔ c₂ (α  2 , β 2) 3.
Of course, * ≡ ₀, because the previous value in the sequence is ₀, and
every ℕ∞ is decreasing.

    0  1  2  3  4  5  ⋯
c₀  ₁  ₁  ₁  ₁  ₁  ₀  ⋯
c₁  ₁  ₁  ₁  ₁  ₁  ₁  ⋯
c₂  ₁  ₁  ₀  *  ₀  ₀  ⋯
c₃  ₀  ₀  ₀  ₀  ₀  ₀  ⋯
⋯   ⋯  ⋯  ⋯  ⋯  ⋯  ⋯

This 'square' of binary values is infinite in both directions; and we in
fact use the minimum values of this square's diagonals to determine the
value c (α , β) : ℕ∞.

Using this illustration, c (α , β) 0 ≡ ₁ as it is the single element of
the first diagonal. c (α , β) 1 and c (α , β) 2 are also ₁ because the
second and third diagonals only feature ₁s. However, c (α , β) 3 is
₀, because the fourth diagonal features a ₀ -- we take the minimum value
of each diagonal. We know that c (α , β) n ≡ ₀ for all n > 3, because
c₃ (α 3 , β 3) will appear in every following diagonal, always contributing
a ₀. This means that our determined closeness value is decreasing.

Therefore, we can express the closeness value as follows.

  c (α , β) 0 ≡       c₀ (α 0 , β 0) 0
  c (α , β) 1 ≡ min𝟚 (c₀ (α 0 , β 0) 1)       (c₁ (α 1 , β 1) 0)
  c (α , β) 2 ≡ min𝟚 (c₀ (α 0 , β 0) 2) (min𝟚 (c₁ (α 1 , β 1) 1) (c₂ (α  , β ) 0))
  ⋯

This can be expressed recursively:

  c (α , β) 0        ≡ c₀ (α 0 , β 0) 0
  c (α , β) (succ n)
   ≡ min𝟚 (c₀ (α 0 , β 0) (succ n))
          (c  (tail α , tail β) n)

\begin{code}

Π-clofun' : ((T , cs) : sequence-of-clofun-types) → Π T × Π T → (ℕ → 𝟚)
Π-clofun' (T , cs) (A , B) 0 = pr₁ (cs 0 (A 0 , B 0)) 0
Π-clofun' (T , cs) (A , B) (succ n)
 = min𝟚 (pr₁ (cs 0 (A 0 , B 0)) (succ n))
        (Π-clofun' (T ∘ succ , cs ∘ succ) (tail A , tail B) n)

\end{code}

We prove this is decreasing by induction.

(1) In the base case, we wish to show that,

     `min𝟚 (c₀ (α 0 , β 0) 1)
          (c  (tail α , tail β) 0) ≡ ₁
      ⇒
      c₀ (α 0 , β 0) 0 ≡ ₁`.

     Assume we have r : min𝟚 (c₀ (α 0 , β 0) 1)
                             (c  (tail α , tail β) 0) ≡ ₁.

     From the fact c₀ is decreasing, we construct,

     `f : c₀ (α 0 , β 0) 1 ≡ ₁ ⇒ c₀ (α 0 , β 0) 0 ≡ ₁`.

     We use the following lemma,

     `Lemma[min𝟚ab≡₁→a≡₁] : (a b : 𝟚) → min𝟚 a b ≡ ₁ → a ≡ ₁`,

     where a ≔ c₀ (α 0 , β 0) 1,
       and b ≔ c  (tail α , tail β) 0.
           
     By applying this lemma to r : min𝟚 a b ≡ ₁, we
     construct s : c₀ (α 0 , β 0) 1 ≡ ₁.

     We apply f to s to complete the proof.

(2) In the inductive case we wish to show that,

     `min𝟚 (c₀ (α 0 , β 0) (succ (succ n))
           (c (tail α , tail β) (succ n)) ≡ ₁
      ⇒
      min𝟚 (c₀ (α 0 , β 0) (succ n))
           (c  (tail α , tail β) n)  ≡ ₁`

     From the fact c₀ is decreasing, we construct,

     `f : c₀ (α 0 , β 0) (succ (succ n)) ≡ ₁ ⇒ c₀ (α 0 , β 0) (succ n) ≡ ₁`.

     By the inductive hypothesis, we construct,
     `g : c (tail α , tail β) (succ n) ⇒ c (tail α , tail β) n`

     Assume we have r : min𝟚 (c₀ (α 0 , β 0) (succ (succ n))
                             (c (tail α , tail β) (succ n)) ≡ ₁

     We use the following lemmas,

     `Lemma[min𝟚ab≡₁→a≡₁] : (a b : 𝟚) → min𝟚 a b ≡ ₁ → a ≡ ₁`
     `Lemma[min𝟚ab≡₁→b≡₁] : (a b : 𝟚) → min𝟚 a b ≡ ₁ → b ≡ ₁`

     By applying these to r, we construct,
         s : c₀ (α 0 , β 0) (succ (succ n)) ≡ ₁
     and t : c (tail α , tail β) (succ n)   ≡ ₁.

     We apply f to s and g to t to construct,
         u : c₀ (α 0 , β 0) (succ n) ≡ ₁
     and v : c (tail α , tail β) n   ≡ ₁.

     We use the following lemma,

     `Lemma[a≡₁→b≡₁→min𝟚ab≡₁] : (a b : 𝟚) → a ≡ ₁ → b ≡ ₁ → min𝟚 a b ≡ ₁`

     where a ≔ c₀ (α 0 , β 0) (succ n),
       and b ≔ c (tail α , tail β) n.

     By applying this lemma to u and v, we complete the proof.  

\begin{code}

Π-clofun'-dec : ((T , cs) : sequence-of-clofun-types)
              → ((A , B) : Π T × Π T)
              → decreasing (Π-clofun' (T , cs) (A , B))
Π-clofun'-dec (T , cs) (A , B) 0        r =
 pr₂ (cs 0 (A 0 , B 0)) 0 (Lemma[min𝟚ab≡₁→a≡₁] r)
Π-clofun'-dec (T , cs) (A , B) (succ n) r
 = Lemma[a≡₁→b≡₁→min𝟚ab≡₁]
     (pr₂ (cs 0 (A 0 , B 0)) (succ n) (Lemma[min𝟚ab≡₁→a≡₁] r))
     (Π-clofun'-dec (T ∘ succ , cs ∘ succ) (A ∘ succ , B ∘ succ) n
       (Lemma[min𝟚ab≡₁→b≡₁] {pr₁ (cs 0 (A 0 , B 0)) (succ (succ n))} r))

Π-clofun : ((T , cs) : sequence-of-clofun-types) → Π T × Π T → ℕ∞
Π-clofun (T , cs) (A , B) = Π-clofun'     (T , cs) (A , B)
                          , Π-clofun'-dec (T , cs) (A , B)

\end{code}

When every cₙ used is the discrete closeness function, the value of Π-clofun
is equivalent to that of discrete-seq-clofun defined in the previous blog post.

Furthermore, we can show that, if every underlying cₙ satisfies the four properties
of a closeness function, then so does Π-clofun.

The details of these are left as an exercise for the reader, but the can be
found in **this** separate modulefile.

\begin{code}

module hidden-module where

 Π-clofun'-eic : ((T , cs) : sequence-of-clofun-types)
               → ((n : ℕ) (α : T n) → cs n (α , α) ≡ ∞)
               → (A : Π T) → Π-clofun (T , cs) (A , A) ≡ ∞
 Π-clofun'-eic (T , cs) eics A = ℕ∞-equals (γ (T , cs) eics A)
  where
    γ : ((T , cs) : sequence-of-clofun-types)
      → ((n : ℕ) (α : T n) → cs n (α , α) ≡ ∞)
      → (A : Π T) → Π-clofun' (T , cs) (A , A) ∼ (λ _ → ₁)
    γ (T , cs) eics A 0 = ap (λ - → pr₁ - 0) (eics 0 (A 0))
    γ (T , cs) eics A (succ i)
     = Lemma[a≡₁→b≡₁→min𝟚ab≡₁]
         (ap (λ - → pr₁ - (succ i)) (eics 0 (A 0)))
         (γ (T ∘ succ , cs ∘ succ) (eics ∘ succ) (A ∘ succ) i)

 Π-clofun'-all : ((T , cs) : sequence-of-clofun-types)
               → ((A , B) : Π T × Π T)
               → Π-clofun (T , cs) (A , B) ≡ ∞
               → (n : ℕ) → cs n (A n , B n) ≡ ∞
 Π-clofun'-all (T , cs) (A , B) cAB≡∞ n
  = ℕ∞-equals (γ (T , cs) (A , B) (λ i → ap (λ - → pr₁ - i) cAB≡∞) n) where
   γ : ((T , cs) : sequence-of-clofun-types)
     → ((A , B) : Π T × Π T)
     → Π-clofun' (T , cs) (A , B) ∼ (pr₁ ∞)
     → (n : ℕ) → pr₁ (cs n (A n , B n)) ∼ pr₁ ∞
   γ (T , cs) (A , B) cAB∼∞ 0    0        = cAB∼∞ 0
   γ (T , cs) (A , B) cAB∼∞ 0    (succ i) = Lemma[min𝟚ab≡₁→a≡₁] (cAB∼∞ (succ i))
   γ (T , cs) (A , B) cAB∼∞ (succ n)
    = γ (T ∘ succ , cs ∘ succ) (A ∘ succ , B ∘ succ)
        (λ i → Lemma[min𝟚ab≡₁→b≡₁] (cAB∼∞ (succ i)))
        n

 Π-clofun'-ice : ((T , cs) : sequence-of-clofun-types)
               → ((n : ℕ) ((α , β) : T n × T n) → cs n (α , β) ≡ ∞ → α ≡ β)
               → ((A , B) : Π T × Π T)
               → Π-clofun (T , cs) (A , B) ≡ ∞
               → A ≡ B
 Π-clofun'-ice (T , cs) ices (A , B) cAB∼∞
  = fe (λ i → ices i (A i , B i) (Π-clofun'-all (T , cs) (A , B) cAB∼∞ i))

 Π-clofun'-sym : ((T , cs) : sequence-of-clofun-types)
               → ((n : ℕ) ((α , β) : T n × T n) → cs n (α , β) ≡ cs n (β , α))
               → ((A , B) : Π T × Π T)
               → Π-clofun (T , cs) (A , B) ≡ Π-clofun (T , cs) (B , A)
 Π-clofun'-sym (T , cs) syms (A , B)
  = ℕ∞-equals (γ (T , cs) (λ n (α , β) i → ap (λ - → pr₁ - i) (syms n (α , β))) (A , B)) where
   γ : ((T , cs) : sequence-of-clofun-types)
     → ((n : ℕ) ((α , β) : T n × T n) → pr₁ (cs n (α , β)) ∼ pr₁ (cs n (β , α)))
     → ((A , B) : Π T × Π T)
     → Π-clofun' (T , cs) (A , B) ∼ Π-clofun' (T , cs) (B , A)
   γ (T , cs) syms (A , B) 0 = syms 0 (A 0 , B 0) 0
   γ (T , cs) syms (A , B) (succ i)
    = ap (λ - → min𝟚 - (Π-clofun' (T ∘ succ , cs ∘ succ) (A ∘ succ , B ∘ succ) i))
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

 Π-clofun'-ult : ((T , cs) : sequence-of-clofun-types)
               → ((n : ℕ) ((α , β , ζ) : T n × T n × T n)
               → min (cs n (α , β)) (cs n (β , ζ)) ≼ cs n (α , ζ))
               → ((A , B , C) : Π T × Π T × Π T)
               → min (Π-clofun (T , cs) (A , B)) (Π-clofun (T , cs) (B , C))
                   ≼ Π-clofun (T , cs) (A , C)
 Π-clofun'-ult (T , cs) ults (A , B , C) 0        r
  = ults 0 (A 0 , B 0 , C 0) 0 r
 Π-clofun'-ult (T , cs) ults (A , B , C) (succ n) r
  = Lemma[a≡₁→b≡₁→min𝟚ab≡₁]
      (ults 0 (A 0 , B 0 , C 0) (succ n)
      (Lemma[min𝟚abcd≡₁→min𝟚ac≡₁]
                            {pr₁ (cs 0 (A 0 , B 0)) (succ n)}
                            {Π-clofun' (T ∘ succ , cs ∘ succ) (A ∘ succ , B ∘ succ) n}
                            {pr₁ (cs 0 (B 0 , C 0)) (succ n)}
                            {Π-clofun' (T ∘ succ , cs ∘ succ) (B ∘ succ , C ∘ succ) n}
      r))
      (Π-clofun'-ult (T ∘ succ , cs ∘ succ) (ults ∘ succ)
         (A ∘ succ , B ∘ succ , C ∘ succ) n
      ((Lemma[min𝟚abcd≡₁→min𝟚bd≡₁] 
                            {pr₁ (cs 0 (A 0 , B 0)) (succ n)}
                            {Π-clofun' (T ∘ succ , cs ∘ succ) (A ∘ succ , B ∘ succ) n}
                            {pr₁ (cs 0 (B 0 , C 0)) (succ n)}
                            {Π-clofun' (T ∘ succ , cs ∘ succ) (B ∘ succ , C ∘ succ) n}
      r)))

 Π-is-clofun : ((T , cs) : sequence-of-clofun-types)
             → (is : (n : ℕ) → is-clofun (cs n))
             → is-clofun (Π-clofun (T , cs))                           
 is-clofun.equal→inf-close
  (Π-is-clofun (T , cs) is)
  = Π-clofun'-eic (T , cs)
      (λ n → is-clofun.equal→inf-close (is n))
     
 is-clofun.inf-close→equal
  (Π-is-clofun (T , cs) is)
  = λ A B f → Π-clofun'-ice (T , cs)
      (λ n (α , β) → is-clofun.inf-close→equal (is n) α β)
      (A , B) f
 
 is-clofun.symmetricity
  (Π-is-clofun (T , cs) is)
  = λ A B → Π-clofun'-sym (T , cs)
      (λ n (α , β) → is-clofun.symmetricity (is n) α β)
      (A , B)

 is-clofun.ultrametric
  (Π-is-clofun (T , cs) is)
  = λ A B C → Π-clofun'-ult (T , cs)
      (λ n (α , β , ζ) → is-clofun.ultrametric (is n) α β ζ)
      (A , B , C)

Π-is-clofun : ((T , cs) : sequence-of-clofun-types)
            → (is : (n : ℕ) → is-clofun (cs n))
            → is-clofun (Π-clofun (T , cs))                           
Π-is-clofun = hidden-module.Π-is-clofun

\end{code}

**Tychonff Theorem**

We can now state the Tychonoff theorem.

We develop the searcher and the proof that the searcher
satisfies the search condition separately via
mutual recursion.

\begin{code}

tychonoff-attempt : ((T , cs) : sequence-of-clofun-types)
                  → ((n : ℕ) → is-clofun (cs n))
                  → (Is : (n : ℕ) → c-searchable (T n) (cs n))
                  → c-searchable (Π T) (Π-clofun (T , cs))

Searcher-attempt : ((T , cs) : sequence-of-clofun-types)
                 → ((n : ℕ) → is-clofun (cs n))
                 → (Is : (n : ℕ) → c-searchable (T n) (cs n))
                 → ((p , d) : d-predicate (Π T))
                 → (δ : ℕ)
                 → δ is-u-mod-of p on Π-clofun (T , cs)
                 → Π T

Condition-attempt : ((T , cs) : sequence-of-clofun-types)
                  → (is : (n : ℕ) → is-clofun (cs n))
                  → (Is : (n : ℕ) → c-searchable (T n) (cs n))
                  → ((p , d) : d-predicate (Π T))
                  → (δ : ℕ)
                  → (ϕ : δ is-u-mod-of p on Π-clofun (T , cs))
                  → Σ p → p (Searcher-attempt (T , cs) is Is (p , d) δ ϕ)

tychonoff-attempt (T , cs) is Is ((p , d) , δ , ϕ)
 = Searcher-attempt  (T , cs) is Is (p , d) δ ϕ
 , Condition-attempt (T , cs) is Is (p , d) δ ϕ

\end{code}

Mod 0 stuff (lemma 1)

\begin{code}
{-
Searcher-attempt  (T , cs) is Is (p , d) 0  ϕ
 = λ n → c-searchable-types-are-inhabited (cs n) (Is n)

Condition-attempt (T , cs) is Is (p , d) 0 ϕ (α , pα)
 = 0-mod-always-satisfied (Π-clofun (T , cs)) (p , d) ϕ (α , pα)
     (Searcher-attempt (T , cs) is Is (p , d) 0 ϕ)
-}
\end{code}

Tail stuff (lemma 2)

\begin{code}

≼-clofun-refl : {X : 𝓤 ̇ } → (c : X × X → ℕ∞) → is-clofun c
              → (δ : ℕ) → (x : X) → (δ ↑) ≼ c (x , x)
≼-clofun-refl c i δ x = transport ((δ ↑) ≼_) (is-clofun.equal→inf-close i x ⁻¹) (∞-maximal (δ ↑))

≼-clofun-sym : {X : 𝓤 ̇ } → (c : X × X → ℕ∞) → is-clofun c
             → (δ : ℕ) → (x y : X) → (δ ↑) ≼ c (x , y) → (δ ↑) ≼ c (y , x)
≼-clofun-sym c i δ x y = transport ((δ ↑) ≼_) (is-clofun.symmetricity i x y)

tail-predicate : {T : ℕ → 𝓤₀ ̇ }
               → ((p , d) : d-predicate (Π T))
               → (x : T 0) → d-predicate (Π (T ∘ succ))
tail-predicate (p , d) x
 = (λ xs → p (x :: xs)) , (λ xs → d (x :: xs))

build-up : ((T , cs) : sequence-of-clofun-types)
         → ((n : ℕ) → is-clofun (cs n))
         → (x y : T 0)
         → (xs ys : Π (T ∘ succ))
         → (δ : ℕ)
         → (succ δ ↑) ≼ cs 0 (x , y)
         → (     δ ↑) ≼ Π-clofun (T ∘ succ , cs ∘ succ) (xs , ys)
         → (succ δ ↑) ≼ Π-clofun (T , cs) (x :: xs , y :: ys)
build-up (T , cs) is x y xs ys δ δ≼cxy δ≼cxsys 0 refl
 = δ≼cxy 0 refl
build-up (T , cs) is x y xs ys δ δ≼cxy δ≼cxsys (succ n) r
 = Lemma[a≡₁→b≡₁→min𝟚ab≡₁] (δ≼cxy (succ n) r) (δ≼cxsys n r)

tail-predicate-reduce-mod : ((T , cs) : sequence-of-clofun-types)
                          → (is : (n : ℕ) → is-clofun (cs n))
                          → ((p , d) : d-predicate (Π T))
                          → (x : T 0) → (δ : ℕ)
                          → (succ δ) is-u-mod-of p on Π-clofun (T , cs)
                          →       δ  is-u-mod-of (pr₁ (tail-predicate (p , d) x))
                                                 on Π-clofun ((T ∘ succ) , (cs ∘ succ))
tail-predicate-reduce-mod (T , cs) is p x δ ϕ (xs , ys) δ≼cxsys
 = ϕ (x :: xs , x :: ys) (build-up (T , cs) is x x xs ys δ (≼-clofun-refl (cs 0) (is 0) (succ δ) x) δ≼cxsys)

\end{code}

Head stuff

\begin{code}

head-predicate-attempt : ((T , cs) : sequence-of-clofun-types)
                       → ((n : ℕ) → is-clofun (cs n))
                       → (Is : (n : ℕ) → c-searchable (T n) (cs n))
                       → ((p , d) : d-predicate (Π T))
                       → (δ : ℕ) → succ δ is-u-mod-of p on (Π-clofun (T , cs))
                       → uc-d-predicate (T 0) (cs 0)
head-predicate-attempt (T , cs) is Is (p , d) δ ϕ
 = (pₕ , dₕ) , succ δ , ϕₕ
 where
   𝓔xs : T 0 → Π (T ∘ succ)
   𝓔xs x = Searcher-attempt (T ∘ succ , cs ∘ succ) (is ∘ succ) (Is ∘ succ)
               (tail-predicate (p , d) x)
               δ (tail-predicate-reduce-mod (T , cs) is (p , d) x δ ϕ)
   pₕ = λ x → p (x :: 𝓔xs x)
   dₕ = λ x → d (x :: 𝓔xs x)
   ϕₕ : succ δ is-u-mod-of pₕ on (cs 0)
   ϕₕ (x , y) δ≼cxy
    = ϕ (x :: 𝓔xs x , y :: 𝓔xs y)
        (build-up (T , cs) is x y (𝓔xs x) (𝓔xs y) δ δ≼cxy TODO)
     where
       TODO : (δ ↑) ≼ Π-clofun (T ∘ succ , cs ∘ succ) (𝓔xs x , 𝓔xs y)
       TODO = {!!}

Searcher-attempt  (T , cs) is Is (p , d) 0        ϕ
 = λ n → c-searchable-types-are-inhabited (cs n) (Is n)

Searcher-attempt  (T , cs) is Is (p , d) (succ δ) ϕ
 = x :: 𝓔xs x
 where
   pₕ = pr₁ (pr₁ (head-predicate-attempt (T , cs) is Is (p , d) δ ϕ))

   S-head : Σ x₀ ꞉ T 0 , (Σ pₕ → pₕ x₀)
   S-head = Is 0 (head-predicate-attempt (T , cs) is Is (p , d) δ ϕ)

   x : T 0
   x = pr₁ S-head

   𝓔xs : T 0 → Π (T ∘ succ)
   𝓔xs x = Searcher-attempt (T ∘ succ , cs ∘ succ) (is ∘ succ) (Is ∘ succ)
               (tail-predicate (p , d) x)
               δ (tail-predicate-reduce-mod (T , cs) is (p , d) x δ ϕ)

Condition-attempt (T , cs) is Is (p , d) 0        ϕ (α , pα)
 = 0-mod-always-satisfied (Π-clofun (T , cs)) (p , d) ϕ (α , pα)
     (Searcher-attempt (T , cs) is Is (p , d) 0 ϕ)
     
Condition-attempt (T , cs) is Is (p , d) (succ δ) ϕ (α , pα)
 = γ (α , pα)
 where
   pₕ = pr₁ (pr₁ (head-predicate-attempt (T , cs) is Is (p , d) δ ϕ))
   pₜ = λ x' → pr₁ (tail-predicate (p , d) x')

   S-head : Σ x₀ ꞉ T 0 , (Σ pₕ → pₕ x₀)
   S-head = Is 0 (head-predicate-attempt (T , cs) is Is (p , d) δ ϕ)

   x : T 0
   x = pr₁ S-head

   γₕ : Σ pₕ → pₕ x
   γₕ = pr₂ S-head

   𝓔xs : T 0 → Π (T ∘ succ)
   𝓔xs x = Searcher-attempt (T ∘ succ , cs ∘ succ) (is ∘ succ) (Is ∘ succ)
               (tail-predicate (p , d) x)
               δ (tail-predicate-reduce-mod (T , cs) is (p , d) x δ ϕ)
               
   γₜ : (x' : T 0) → Σ (pₜ x') → pₜ x' (𝓔xs x')
   γₜ = λ x → Condition-attempt (T ∘ succ , cs ∘ succ) (is ∘ succ) (Is ∘ succ)
               (tail-predicate (p , d) x)
               δ (tail-predicate-reduce-mod (T , cs) is (p , d) x δ ϕ)

   γ : Σ p → p (x :: 𝓔xs x)
   γ (α₀ , pα₀) = step₆ where
     x₀  = head α₀
     xs₀ = tail α₀

     step₁ : p (x₀ :: xs₀)
     step₁ = transport p (head-tail-eta α₀) pα₀

     step₂ : (pₜ x₀) xs₀
     step₂ = step₁
    
     step₃ : (pₜ x₀) (𝓔xs x₀)
     step₃ = γₜ x₀ (xs₀ , step₂)
 
     step₄ : pₕ x₀
     step₄ = step₃
    
     step₅ : pₕ x
     step₅ = γₕ (x₀ , step₄)

     step₆ : p (x :: 𝓔xs x)
     step₆ = step₅

\end{code}

So our overall proof works exactly the same for sequences of continuously
searchable as it did for discrete-sequence types in the last blog post.

However, there is one key difference -- the hole marked 'TODO'. The
key difference between the two proofs is that, this time, we have to
prove that the head predicate is continuous. We avoided this last time
by using the fact that every predicate on a discrete type is trivially
continuous.

The hole asks us to prove that (𝓔xs x) , (𝓔xs y) : Π (T ∘ succ)
-- i.e. the results of the searcher applied to (i) the tail-predicate
for p via x and (ii) the tail-predicate for p via y -- are at least
δ-close.

Intuitively, our searchers follow some form of search strategy
-- given 'the same' predicate, we expect them to return the same answer.
Furthermore, given 'close' predicates, we expect them to return close answers.

Two predicates are 'the same' if they agree on the same arguments.
Two predicates are therefore 'close' if they agree on close arguments.

Two decidable predicates p₁,p₂ : d-predicate X are 'close' up to
precision δ : ℕ on closeness function c : X × X → ℕ∞ if, for any two
arguments x,y : X that are δ-close, both p₁(x) ⇒ p₂(y) and p₂(x) ⇒ p₁(y).

\begin{code}

agree-everywhere : {X : 𝓤 ̇ } → d-predicate X → d-predicate X → 𝓤 ̇
agree-everywhere {𝓤} {X} (p₁ , d₁) (p₂ , d₂) = ((x : X) → p₁ x → p₂ x)
                                             × ((x : X) → p₂ x → p₁ x)

close : {X : 𝓤 ̇ } → d-predicate X → d-predicate X → ℕ → (X × X → ℕ∞) → 𝓤 ̇
close {𝓤} {X} (p₁ , d₁) (p₂ , d₂) δ c
 = (((x , y) : X × X) → (δ ↑) ≼ c (x , y) → p₁ x → p₂ y)
 × (((x , y) : X × X) → (δ ↑) ≼ c (x , y) → p₂ x → p₁ y)

\end{code}

Of course, any uniformly continuous decidable predicate is δ-close to itself,
where δ : ℕ is the modulus of continuity. 

Also, predicates that are close to any degree of precision are trivially
'the same' in the sense that they agree on identical arguments.

\begin{code}

close-predicate-itself : {X : 𝓤 ̇ } → (c : X × X → ℕ∞)
                       → (((p , d) , δ , ϕ) : uc-d-predicate X c)
                       → close (p , d) (p , d) δ c
close-predicate-itself c ((p , d) , δ , ϕ) = ϕ , ϕ

close-predicates-agree : {X : 𝓤 ̇ } → (c : X × X → ℕ∞) → (i : is-clofun c)
                       → ((p₁ , d₁) (p₂ , d₂) : d-predicate X)
                       → (δ : ℕ)
                       → close (p₁ , d₁) (p₂ , d₂) δ c
                       → agree-everywhere (p₁ , d₁) (p₂ , d₂)
close-predicates-agree c i (p₁ , d₁) (p₂ , d₂) δ (f , g)
 = (λ x p₁x → f (x , x) (≼-clofun-refl c i δ x) p₁x)
 , (λ x p₂x → g (x , x) (≼-clofun-refl c i δ x) p₂x)

\end{code}

A searcher is called 'agreeable' if the results of searching two
δ-close predicates are themselves δ-close.

\begin{code}

agreeable : {X : 𝓤 ̇ } → (c : X × X → ℕ∞) → c-searchable X c → (𝓤₀ ⁺) ⊔ 𝓤 ̇ 
agreeable {𝓤} {X} c S = ((p₁ , d₁) (p₂ , d₂) : d-predicate X)
                      → (δ : ℕ)
                      → close (p₁ , d₁) (p₂ , d₂) δ c
                      → (ϕ₁ : δ is-u-mod-of p₁ on c)
                      → (ϕ₂ : δ is-u-mod-of p₂ on c)
                      → (δ ↑) ≼ c (pr₁ (S ((p₁ , d₁) , δ , ϕ₁))
                                 , pr₁ (S ((p₂ , d₂) , δ , ϕ₂)))

\end{code}

The searcher for 𝟚 is agreeable. In order to prove this clearly,
we reformulate the proof that 𝟚 is continuously searchable.

First, we show that given any predicate on 𝟚 such that p(₁) is
decidable, we can find an answer x₀ : 𝟚 such that Σ p implies p(x₀).

If p(₁) holds, then x₀ ≔ ₁ and p(x₀) is trivially satisfied.
If p(₁) doesn't hold, then x₀ ≔ ₀.
   Assuming Σ p gives us some x : 𝟚 such that p(x).
      If x ≡ ₀, then p(x₀) is trivially satisfied.
      If x ≡ ₁, then there is a contradiction.

This gives us the fact that 𝟚 is continuously searchable.

\begin{code}

𝟚-is-c-searchable' : (p : 𝟚 → 𝓤 ̇ )
                   → decidable (p ₁)
                   → Σ x₀ ꞉ 𝟚 , (Σ p → p x₀)
𝟚-is-c-searchable' p (inl  p₁)
 = ₁ , λ _ → p₁
𝟚-is-c-searchable' p (inr ¬p₁)
 = ₀ , λ (x₀ , px₀) → 𝟚-equality-cases
                          (λ e → transport p e px₀)
                          (λ e → 𝟘-elim (¬p₁ (transport p e px₀)))

𝟚-is-c-searchable : c-searchable 𝟚 (discrete-clofun 𝟚-is-discrete)
𝟚-is-c-searchable ((p , d) , _) = 𝟚-is-c-searchable' p (d ₁)

\end{code}

We then show that the searcher as defined above, when given
two predicates that are δ-close for any δ : ℕ,
always returns the same answer for x₀.

This is because the two predicates agree everywhere.

\begin{code}

𝟚-is-c-searchable'-agree-eq : ((p₁ , d₁) (p₂ , d₂) : d-predicate 𝟚)
                            → agree-everywhere (p₁ , d₁) (p₂ , d₂)
                            → pr₁ (𝟚-is-c-searchable' p₁ (d₁ ₁))
                            ≡ pr₁ (𝟚-is-c-searchable' p₂ (d₂ ₁))
𝟚-is-c-searchable'-agree-eq (p₁ , d₁) (p₂ , d₂) (f , g) = γ (d₁ ₁) (d₂ ₁)
 where
   γ : (d₁₁ : decidable (p₁ ₁)) (d₂₁ : decidable (p₂ ₁))
     → pr₁ (𝟚-is-c-searchable' p₁ d₁₁) ≡ pr₁ (𝟚-is-c-searchable' p₂ d₂₁)
   γ (inl  _ ) (inl  _ ) = refl
   γ (inr  _ ) (inr  _ ) = refl
   γ (inl  p₁) (inr ¬p₁) = 𝟘-elim (¬p₁ (f ₁ p₁))
   γ (inr ¬p₁) (inl  p₁) = 𝟘-elim (¬p₁ (g ₁ p₁))

𝟚-is-c-searchable'-close-eq : ((p₁ , d₁) (p₂ , d₂) : d-predicate 𝟚)
                            → (δ : ℕ)
                            → close (p₁ , d₁) (p₂ , d₂) δ (discrete-clofun 𝟚-is-discrete)
                            → pr₁ (𝟚-is-c-searchable' p₁ (d₁ ₁))
                            ≡ pr₁ (𝟚-is-c-searchable' p₂ (d₂ ₁))
𝟚-is-c-searchable'-close-eq (p₁ , d₁) (p₂ , d₂) δ (f , g)
 = 𝟚-is-c-searchable'-agree-eq (p₁ , d₁) (p₂ , d₂)
     (close-predicates-agree (discrete-clofun 𝟚-is-discrete) (discrete-is-clofun 𝟚-is-discrete)
       (p₁ , d₁) (p₂ , d₂) δ (f , g))

\end{code}

From this, we get that 𝟚's searcher is agreeable.

\begin{code}

𝟚-is-agreeable : agreeable (discrete-clofun 𝟚-is-discrete) 𝟚-is-c-searchable
𝟚-is-agreeable (p₁ , d₁) (p₂ , d₂) δ (f , g) ϕ₁ ϕ₂
 = transport (λ - → (δ ↑) ≼ discrete-clofun 𝟚-is-discrete
               (pr₁ (𝟚-is-c-searchable' p₁ (d₁ ₁)) , -))
     (𝟚-is-c-searchable'-close-eq (p₁ , d₁) (p₂ , d₂) δ (f , g))
     (≼-clofun-refl (discrete-clofun 𝟚-is-discrete)
       (discrete-is-clofun 𝟚-is-discrete)
       δ (pr₁ (𝟚-is-c-searchable' p₁ (d₁ ₁))))

\end{code}

**Tychonoff Attempt 2**

We now restate our Tychonoff theorem, with the assumption
that each of the continuously searchable types that make up
T yields an agreeable searcher.

\begin{code}

tychonoff : ((T , cs) : sequence-of-clofun-types)
          → ((n : ℕ) → is-clofun (cs n))
          → (Is : (n : ℕ) → c-searchable (T n) (cs n))
          → ((n : ℕ) → agreeable (cs n) (Is n))
          → c-searchable (Π T) (Π-clofun (T , cs))    

Searcher : ((T , cs) : sequence-of-clofun-types)
         → ((n : ℕ) → is-clofun (cs n))
         → (Is : (n : ℕ) → c-searchable (T n) (cs n))
         → ((n : ℕ) → agreeable (cs n) (Is n))
         → ((p , d) : d-predicate (Π T))
         → (δ : ℕ)
         → δ is-u-mod-of p on Π-clofun (T , cs)
         → Π T

Condition : ((T , cs) : sequence-of-clofun-types)
          → (is : (n : ℕ) → is-clofun (cs n))
          → (Is : (n : ℕ) → c-searchable (T n) (cs n))
          → (ccs : (n : ℕ) → agreeable (cs n) (Is n))  
          → ((p , d) : d-predicate (Π T))
          → (δ : ℕ)
          → (ϕ : δ is-u-mod-of p on Π-clofun (T , cs))
          → Σ p → p (Searcher (T , cs) is Is ccs (p , d) δ ϕ)

\end{code}

\begin{code}

tail-predicate-agree : ((T , cs) : sequence-of-clofun-types)
                     → (is : (n : ℕ) → is-clofun (cs n))
                     → ((p₁ , d₁) (p₂ , d₂) : d-predicate (Π T))
                     → (δ : ℕ)
                     → (x y : T 0)
                     → (succ δ ↑) ≼ cs 0 (x , y)
                     → close (p₁ , d₁) (p₂ , d₂) (succ δ) (Π-clofun (T , cs))
                     → (ϕ₁ : succ δ is-u-mod-of p₁ on (Π-clofun (T , cs)))
                     → (ϕ₂ : succ δ is-u-mod-of p₂ on (Π-clofun (T , cs)))
                     → close (tail-predicate (p₁ , d₁) x) (tail-predicate (p₂ , d₂) y)
                             δ (Π-clofun (T ∘ succ , cs ∘ succ))
tail-predicate-agree (T , cs) is (p₁ , d₁) (p₂ , d₂) δ x y δ≼cxy (f , g) ϕ₁ ϕ₂
 = (λ (xs , ys) δ≼cxsys → f (x :: xs , y :: ys) (build-up (T , cs) is x y xs ys δ δ≼cxy δ≼cxsys))
 , (λ (xs , ys) δ≼cxsys → g (y :: xs , x :: ys) (build-up (T , cs) is y x xs ys δ δ≼cyx δ≼cxsys))
 where
   δ≼cyx = ≼-clofun-sym (cs 0) (is 0) (succ δ) x y δ≼cxy
   
agreeabley2 : ((T , cs) : sequence-of-clofun-types)
      → (is : (n : ℕ) → is-clofun (cs n))
      → (Is : (n : ℕ) → c-searchable (T n) (cs n))
      → (ccs : (n : ℕ) → agreeable (cs n) (Is n))
      → ((p₁ , d₁) (p₂ , d₂) : d-predicate (Π T))
      → (δ : ℕ)
      → close (p₁ , d₁) (p₂ , d₂) δ (Π-clofun (T , cs))
      → (ϕ₁ : δ is-u-mod-of p₁ on (Π-clofun (T , cs)))
      → (ϕ₂ : δ is-u-mod-of p₂ on (Π-clofun (T , cs)))
      → (δ ↑) ≼ Π-clofun (T , cs)
                  (Searcher (T , cs) is Is ccs (p₁ , d₁) δ ϕ₁
                 , Searcher (T , cs) is Is ccs (p₂ , d₂) δ ϕ₂)

\end{code}



\begin{code}


head-predicate : ((T , cs) : sequence-of-clofun-types)
               → ((n : ℕ) → is-clofun (cs n))
               → (Is : (n : ℕ) → c-searchable (T n) (cs n))
               → ((n : ℕ) → agreeable (cs n) (Is n))
               → ((p , d) : d-predicate (Π T))
               → (δ : ℕ) → succ δ is-u-mod-of p on (Π-clofun (T , cs))
               → uc-d-predicate (T 0) (cs 0)
head-predicate (T , cs) is Is ccs (p , d) δ ϕ
 = (pₕ , dₕ) , succ δ , ϕₕ
 where
   𝓔xs : T 0 → Π (T ∘ succ)
   𝓔xs x = Searcher (T ∘ succ , cs ∘ succ) (is ∘ succ) (Is ∘ succ) (ccs ∘ succ)
               (tail-predicate (p , d) x)
               δ (tail-predicate-reduce-mod (T , cs) is (p , d) x δ ϕ)
   pₕ = λ x → p (x :: 𝓔xs x)
   dₕ = λ x → d (x :: 𝓔xs x)
   ϕₕ : succ δ is-u-mod-of pₕ on cs 0
   ϕₕ (x , y) δ≼cxy
    = ϕ ((x :: 𝓔xs x) , (y :: 𝓔xs y))
        (build-up (T , cs) is x y (𝓔xs x) (𝓔xs y) δ δ≼cxy
          (agreeabley2 (T ∘ succ , cs ∘ succ) (is ∘ succ) (Is ∘ succ) (ccs ∘ succ)
            (tail-predicate (p , d) x)
            (tail-predicate (p , d) y)
            δ
            (tail-predicate-agree (T , cs) is (p , d) (p , d) δ x y δ≼cxy (close-predicate-itself (Π-clofun (T , cs)) ((p , d) , succ δ , ϕ)) ϕ ϕ)
            (tail-predicate-reduce-mod (T , cs) is (p , d) x δ ϕ)
            (tail-predicate-reduce-mod (T , cs) is (p , d) y δ ϕ)))

head-predicate-agree : ((T , cs) : sequence-of-clofun-types)
                     → (is : (n : ℕ) → is-clofun (cs n))
                     → (Is : (n : ℕ) → c-searchable (T n) (cs n))
                     → (ccs : (n : ℕ) → agreeable (cs n) (Is n))
                     → ((p₁ , d₁) (p₂ , d₂) : d-predicate (Π T))
                     → (δ : ℕ)
                     → close (p₁ , d₁) (p₂ , d₂) (succ δ) (Π-clofun (T , cs))
                     → (ϕ₁ : succ δ is-u-mod-of p₁ on (Π-clofun (T , cs)))
                     → (ϕ₂ : succ δ is-u-mod-of p₂ on (Π-clofun (T , cs)))
                     → let ph1 = head-predicate (T , cs) is Is ccs (p₁ , d₁) δ ϕ₁ in
                       let ph2 = head-predicate (T , cs) is Is ccs (p₂ , d₂) δ ϕ₂ in
                       close (pr₁ ph1) (pr₁ ph2) (succ δ) (cs 0)
head-predicate-agree (T , cs) is Is ccs (p₁ , d₁) (p₂ , d₂) δ (f , g) ϕ₁ ϕ₂
 = (λ (x , y) δ≼cxy → f (x :: 𝓔xs₁ x , y :: 𝓔xs₂ y) (γ  x y δ≼cxy))
 , (λ (x , y) δ≼cxy → g (x :: 𝓔xs₂ x , y :: 𝓔xs₁ y) (γ' x y δ≼cxy))
 where
   𝓔xs₁ 𝓔xs₂ : T 0 → Π (T ∘ succ)
   𝓔xs₁ x = Searcher (T ∘ succ , cs ∘ succ) (is ∘ succ) (Is ∘ succ) (ccs ∘ succ)
               (tail-predicate (p₁ , d₁) x)
               δ (tail-predicate-reduce-mod (T , cs) is (p₁ , d₁) x δ ϕ₁)
   𝓔xs₂ x = Searcher (T ∘ succ , cs ∘ succ) (is ∘ succ) (Is ∘ succ) (ccs ∘ succ)
               (tail-predicate (p₂ , d₂) x)
               δ (tail-predicate-reduce-mod (T , cs) is (p₂ , d₂) x δ ϕ₂)    
   ph1 = head-predicate (T , cs) is Is ccs (p₁ , d₁) δ ϕ₁
   ph2 = head-predicate (T , cs) is Is ccs (p₂ , d₂) δ ϕ₂
   γ : (x y : T 0)
     → (succ δ ↑) ≼ cs 0 (x , y)
     → (succ δ ↑) ≼ Π-clofun (T , cs) (x :: 𝓔xs₁ x , y :: 𝓔xs₂ y)
   γ x y δ≼cxy = build-up (T , cs) is x y (𝓔xs₁ x) (𝓔xs₂ y) δ δ≼cxy
                   (agreeabley2 (T ∘ succ , cs ∘ succ) (is ∘ succ) (Is ∘ succ) (ccs ∘ succ)
                     (tail-predicate (p₁ , d₁) x)
                     (tail-predicate (p₂ , d₂) y)
                     δ
                     (tail-predicate-agree (T , cs) is (p₁ , d₁) (p₂ , d₂) δ x y δ≼cxy (f , g) ϕ₁ ϕ₂)
                     (tail-predicate-reduce-mod (T , cs) is (p₁ , d₁) x δ ϕ₁)
                     (tail-predicate-reduce-mod (T , cs) is (p₂ , d₂) y δ ϕ₂))
   γ' : (x y : T 0)
      → (succ δ ↑) ≼ cs 0 (x , y)
      → (succ δ ↑) ≼ Π-clofun (T , cs) (x :: 𝓔xs₂ x , y :: 𝓔xs₁ y)
   γ' x y δ≼cxy = ≼-clofun-sym (Π-clofun (T , cs)) (Π-is-clofun (T , cs) is)
                    (succ δ) (y :: 𝓔xs₁ y) (x :: 𝓔xs₂ x)
                    (γ y x (≼-clofun-sym (cs 0) (is 0) (succ δ) x y δ≼cxy))

\end{code}



\begin{code}

tychonoff (T , cs) is Is ccs ((p , d) , δ , ϕ)
 = Searcher  (T , cs) is Is ccs (p , d) δ ϕ
 , Condition (T , cs) is Is ccs (p , d) δ ϕ

\end{code}



\begin{code}

Searcher (T , cs) is Is ccs (p , d) 0        ϕ
 = λ n → c-searchable-types-are-inhabited (cs n) (Is n)
 
Searcher (T , cs) is Is ccs (p , d) (succ δ) ϕ
 = pr₁ (Is 0 (head-predicate (T , cs) is Is ccs (p , d) δ ϕ))
 :: Searcher (T ∘ succ , cs ∘ succ) (is ∘ succ) (Is ∘ succ) (ccs ∘ succ)
      (tail-predicate (p , d) (pr₁ (Is 0 (head-predicate (T , cs) is Is ccs (p , d) δ ϕ))))
      δ (tail-predicate-reduce-mod (T , cs) is (p , d) (pr₁ (Is 0 (head-predicate (T , cs) is Is ccs (p , d) δ ϕ))) δ ϕ)

\end{code}



\begin{code}

Condition (T , cs) is Is ccs (p , d) 0        ϕ (α , pα)
 = 0-mod-always-satisfied (Π-clofun (T , cs)) (p , d) ϕ (α , pα)
     (Searcher (T , cs) is Is ccs (p , d) 0 ϕ)

Condition (T , cs) is Is ccs (p , d) (succ δ) ϕ (α , pα)
 = pr₂ (Is 0 (head-predicate (T , cs) is Is ccs (p , d) δ ϕ))
   (head α
  , Condition (T ∘ succ , cs ∘ succ) (is ∘ succ) (Is ∘ succ) (ccs ∘ succ)
    (tail-predicate (p , d) (α 0))
    δ (tail-predicate-reduce-mod (T , cs) is (p , d) (α 0) δ ϕ)
  (tail α , transport p (head-tail-eta α) pα))

\end{code}



\begin{code}

agreeabley2 (T , cs) is Is ccs (p₁ , d₁) (p₂ , d₂) 0        (f , g) ϕ₁ ϕ₂
 = 0-minimal _

agreeabley2 (T , cs) is Is ccs (p₁ , d₁) (p₂ , d₂) (succ δ) (f , g) ϕ₁ ϕ₂ 0        r
 = ccs 0 (pr₁ ph1) (pr₁ ph2) (succ δ)
     (head-predicate-agree (T , cs) is Is ccs (p₁ , d₁) (p₂ , d₂) δ (f , g) ϕ₁ ϕ₂)
     (pr₂ (pr₂ ph1))
     (pr₂ (pr₂ ph2))
     0 r
 where
   ph1 = head-predicate (T , cs) is Is ccs (p₁ , d₁) δ ϕ₁
   ph2 = head-predicate (T , cs) is Is ccs (p₂ , d₂) δ ϕ₂
agreeabley2 (T , cs) is Is ccs (p₁ , d₁) (p₂ , d₂) (succ δ) (f , g) ϕ₁ ϕ₂ (succ n) r
 = Lemma[a≡₁→b≡₁→min𝟚ab≡₁] (γ₁ (succ n) r) (γ₂ n r)
 where
   ph1 = head-predicate (T , cs) is Is ccs (p₁ , d₁) δ ϕ₁
   ph2 = head-predicate (T , cs) is Is ccs (p₂ , d₂) δ ϕ₂
   x y : T 0
   x  = pr₁ (Is 0 ph1)
   y  = pr₁ (Is 0 ph2)
   γ₁ = ccs 0 (pr₁ ph1) (pr₁ ph2) (succ δ)
          (head-predicate-agree (T , cs) is Is ccs (p₁ , d₁) (p₂ , d₂) δ (f , g) ϕ₁ ϕ₂)
          (pr₂ (pr₂ ph1))
          (pr₂ (pr₂ ph2))
   γ₂ = agreeabley2 (T ∘ succ , cs ∘ succ) (is ∘ succ) (Is ∘ succ) (ccs ∘ succ)
          (tail-predicate (p₁ , d₁) x)
          (tail-predicate (p₂ , d₂) y)
          δ
          (tail-predicate-agree (T , cs) is (p₁ , d₁) (p₂ , d₂) δ x y γ₁ (f , g) ϕ₁ ϕ₂)
          (tail-predicate-reduce-mod (T , cs) is (p₁ , d₁) x δ ϕ₁)
          (tail-predicate-reduce-mod (T , cs) is (p₂ , d₂) y δ ϕ₂)

\end{code}

**Corollaries:**

\begin{code}

ℕ→𝟚-is-c-searchable' : c-searchable (ℕ → 𝟚)
                         (Π-clofun ((λ _ → 𝟚) , (λ _ → discrete-clofun 𝟚-is-discrete)))
ℕ→𝟚-is-c-searchable' = tychonoff
                         ((λ _ → 𝟚) , (λ _ → discrete-clofun 𝟚-is-discrete))
                         (λ _ → discrete-is-clofun 𝟚-is-discrete)
                         (λ _ → 𝟚-is-c-searchable)
                         (λ _ → 𝟚-is-agreeable)

ℕ→ℕ→𝟚-is-c-searchable' : c-searchable (ℕ → (ℕ → 𝟚))
                           (Π-clofun ((λ _ → ℕ → 𝟚)
                           , (λ _ → Π-clofun ((λ _ → 𝟚) , (λ _ → discrete-clofun 𝟚-is-discrete)))))
ℕ→ℕ→𝟚-is-c-searchable' = tychonoff
                           ((λ _ → ℕ → 𝟚)
                           , (λ _ → Π-clofun ((λ _ → 𝟚) , (λ _ → discrete-clofun 𝟚-is-discrete))))
                           (λ _ → Π-is-clofun ((λ _ → 𝟚) , (λ _ → discrete-clofun 𝟚-is-discrete))
                                    (λ _ → discrete-is-clofun 𝟚-is-discrete))
                           (λ _ → ℕ→𝟚-is-c-searchable')
                           (λ _
                            → agreeabley2 ((λ _ → 𝟚) , (λ _ → discrete-clofun 𝟚-is-discrete))
                                          (λ _ → discrete-is-clofun 𝟚-is-discrete)
                                          (λ _ → 𝟚-is-c-searchable)
                                          (λ _ → 𝟚-is-agreeable))

\end{code}
