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
         ; build-up)

\end{code}

Table of Contents:
 1. Introduce Π and Π-clofun
 . Reintroduce concepts from previous and
    show this is the same as previous discrete-seq-clofun
 3. Show Π-clofun satisfies all the properties
 4. First attempt and continuity condition
    (Could the condition be weaker?
    Perhaps, but for now it suits
    the purposes we wish for it;
    notably:.)
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

sequence-of-codistance-types : 𝓤₁ ̇ 
sequence-of-codistance-types = Σ T ꞉ (ℕ → 𝓤₀ ̇ ) , Π n ꞉ ℕ , (T n × T n → ℕ∞)

_::_ : {T : ℕ → 𝓤 ̇ } → T 0 → Π (T ∘ succ) → Π T
(x :: xs) 0 = x
(x :: xs) (succ n) = xs n

head : {T : ℕ → 𝓤₀ ̇ } → Π T → T 0
head α = α 0

-- tail' : (T : ℕ → 𝓤 ̂̇ ) → 

tail : {T : ℕ → 𝓤 ̇ } → Π T → Π (T ∘ succ)
tail α = α ∘ succ

head-tail-eta : {T : ℕ → 𝓤₀ ̇ } → (α : Π T) → α ≡ head α :: tail α
head-tail-eta α = fe γ where
  γ : α ∼ (head α :: tail α)
  γ 0 = refl
  γ (succ n) = refl

\end{code}

We want to determine the closeness c(α , β) : ℕ∞ of two infinite sequences α,β : Π T.

It is straightforward to define this where each T n is discrete (i.e. each
closeness function cₙ : T n × T n → ℕ∞ is the discrete closeness function).

  c (α , β) n ≡ ₁,    if x ≡⟦ n ⟧ y,
                ₀,    otherwise.

But how can we determine c(α , β) : ℕ∞ when nothing is assumed about each cₙ, apart
from that they satisfy the four properties of closeness functions.

First, note that we can compute cₙ(α n , β n) : ℕ∞ for every n : ℕ.
The following illustrates some potential values of a prefix of these
closeness functions.

For example, the asterisk * : 𝟚 is defined * ≔ c₂ (α  , β ) 3.
Of course, * ≡ ₀, because the previous value in the sequence is ₀, and
every ℕ∞ is decreasing.

    0  1    3  4  5  ⋯
c₀  ₁  ₁  ₁  ₁  ₁  ₀  ⋯
c₁  ₁  ₁  ₁  ₁  ₁  ₁  ⋯
c₂  ₁  ₁  ₀  *  ₀  ₀  ⋯
c₃  ₀  ₀  ₀  ₀  ₀  ₀  ⋯
⋯   ⋯  ⋯  ⋯  ⋯  ⋯  ⋯

This square of binary values is infinite in both directions; we in fact
use this square's diagonals to determine the value c (α , β) : ℕ∞.

Using this illustration, c (α , β) 0 ≡ ₁ as it is the single element of
the first diagonal. c (α , β) 1 and c (α , β)  are also ₁ because the
second and third diagonals only feature ones. However, c (α , β) 3 is
₀, because the fourth diagonal features a ₀ -- we always take the
minimum value of each diagonal. We know that c (α , β) n ≡ ₀ for all
n > 3, because c₃ (α 3 , β 3) will appear in every following diagonal,
always contributing a ₀. This means that our determined closeness value
is decreasing.

Therefore, we can express the closeness value as follows.

  c (α , β) 0 ≡       c₀ (α 0 , β 0) 0
  c (α , β) 1 ≡ min𝟚 (c₀ (α 0 , β 0) 1 ,       c₁ (α 1 , β 1) 0)
  c (α , β)  ≡ min𝟚 (c₀ (α 0 , β 0)  , min𝟚 (c₁ (α 1 , β 1) 1 , c₂ (α  , β ) 0))
  ⋯

This can be expressed recursively:

  c (α , β) 0        ≡ c₀ (α 0 , β 0) 0
  c (α , β) (succ n) ≡ min𝟚 (c₀ (α 0 , β 0) (succ n) , c (tail α , tail β) n)

\begin{code}

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

\end{code}

When every cₙ used is the discrete closeness function, the value of Π-clofun
is equivalent to that of discrete-seq-clofun defined in the previous blog post.

\begin{code}

SAME : {X : 𝓤₀ ̇ } → (ds : is-discrete X) → (S : c-searchable X (discrete-clofun ds))
     → (α β : ℕ → X)
     → (n : ℕ)
     → (d : decidable (α ≡⟦ n ⟧ β))
     → Π-codistance' ((λ _ → X) , (λ _ (x , y) → discrete-clofun (λ a b → {!d!}) (x , y))) (α , β) n
     ≡ discrete-seq-c' (α , β) n d
SAME ds S α β n = {!!}

{-
Π-codistance-build : ((T , cs) : sequence-of-codistance-types)
                   → (P : (ℕ → 𝟚) → 𝓤₀ ̂̇ )
                   → ((A , B) : Π T × Π T)
                   → P (pr₁ (cs 0 (A 0 , B 0)) 0)
                   → ((n : ℕ) → P (pr₁ (cs 0 (A 0 , B 0)) (succ n)))
                   → ((n : ℕ) → P (Π-codistance' (T , cs) (A , B) n))
-}

\end{code}

We now show that, if every underlying cₙ satisfies the four properties of a
closeness function, then so does Π-codistance.

\begin{code}

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

\end{code}

**Tychonff Theorem: First Attempt**

We can now state the Tychonoff theorem.

\begin{code}

tychonoff-attempt : ((T , cs) : sequence-of-codistance-types)
                  → ((n : ℕ) → is-clofun (cs n))
                  → ((n : ℕ) → c-searchable (T n) (cs n))
                  → c-searchable (Π T) (Π-codistance (T , cs))

tychonoff'-attempt : ((T , cs) : sequence-of-codistance-types)
                   → ((n : ℕ) → is-clofun (cs n))
                   → ((n : ℕ) → c-searchable (T n) (cs n))
                   → ((p , d) : d-predicate (Π T))
                   → (δ : ℕ) → δ is-u-mod-of p on (Π-codistance (T , cs))
                   → Σ x₀ ꞉ Π T , (Σ p → p x₀)
                   
tychonoff-attempt (T , cs) ss Ss (p , d , δ , ϕ)
 = tychonoff'-attempt (T , cs) ss Ss (p , d) δ ϕ

tychonoff'-attempt = {!!}

tail-predicate : {T : ℕ → 𝓤₀ ̇ }
               → ((p , d) : d-predicate (Π T))
               → (x : T 0) → d-predicate (Π (T ∘ succ))
tail-predicate (p , d) x = (λ xs → p (x :: xs)) , (λ xs → d (x :: xs))

build-up : ((T , cs) : sequence-of-codistance-types)
          → ((n : ℕ) → is-clofun (cs n))
          → (xs ys : Π (T ∘ succ)) → (δ : ℕ)
          → (δ ↑) ≼ Π-codistance (T ∘ succ , cs ∘ succ) (xs , ys)
          → (x : T 0)
          → (succ δ ↑) ≼ Π-codistance (T , cs) (x :: xs , x :: ys)
build-up (T , cs) ss xs ys δ δ≼cxsys x 0 refl
 = ap (λ - → pr₁ - 0) (is-clofun.equal→inf-close (ss 0) x)
build-up (T , cs) ss xs ys δ δ≼cxsys x (succ n) r
 = Lemma[a≡₁→b≡₁→min𝟚ab≡₁]
    (ap (λ - → pr₁ - (succ n)) (is-clofun.equal→inf-close (ss 0) x))
    (δ≼cxsys n r)

tail-predicate-reduce-mod : ((T , cs) : sequence-of-codistance-types)
                           → (ss : (n : ℕ) → is-clofun (cs n))
                           → ((p , d) : d-predicate (Π T))
                           → (x : T 0) → (δ : ℕ)
                           → (succ δ) is-u-mod-of p on Π-codistance (T , cs)
                           →       δ  is-u-mod-of (pr₁ (tail-predicate (p , d) x))
                                                  on Π-codistance ((T ∘ succ) , (cs ∘ succ))
tail-predicate-reduce-mod (T , cs) ss p x δ ϕ (xs , ys) δ≼cxsys
 = ϕ (x :: xs , x :: ys) (build-up (T , cs) ss xs ys δ δ≼cxsys x)

head-predicate-attempt : ((T , cs) : sequence-of-codistance-types)
                       → ((n : ℕ) → is-clofun (cs n))
                       → ((n : ℕ) → c-searchable (T n) (cs n))
                       → ((p , d) : d-predicate (Π T))
                       → (δ : ℕ) → succ δ is-u-mod-of p on (Π-codistance (T , cs))
                       → uc-d-predicate (T 0) (cs 0)
head-predicate-attempt (T , cs) ss Ss (p , d) δ ϕ = pₕ , dₕ , succ δ , ϕₕ
 where
   𝓔xs : T 0 → Π (T ∘ succ)
   𝓔xs x
    = pr₁ (tychonoff'-attempt (T ∘ succ , cs ∘ succ) (ss ∘ succ) (Ss ∘ succ)
                 (tail-predicate (p , d) x)
                 δ (tail-predicate-reduce-mod (T , cs) ss (p , d) x δ ϕ))
   pₕ = λ x → p (x :: 𝓔xs x)
   dₕ = λ x → d (x :: 𝓔xs x)
   ϕₕ : succ δ is-u-mod-of pₕ on cs 0
   ϕₕ (x , y) δ≼cxy = ϕ (x :: 𝓔xs x , y :: 𝓔xs y) γ
    where
      γ : (succ δ ↑) ≼ Π-codistance (T , cs) ((x :: 𝓔xs x) , (y :: 𝓔xs y))
      γ 0 r = δ≼cxy 0 r
      γ (succ n) r = Lemma[a≡₁→b≡₁→min𝟚ab≡₁]
                         (δ≼cxy (succ n) r)
                         γ'
       where
         γ' : Π-codistance' (T ∘ succ , cs ∘ succ) (𝓔xs x , 𝓔xs y) n ≡ ₁
         γ' = {!!}

\end{code}

The difference is that, this time, we have to prove that the head predicate
is continuous. We avoided this last time by using the fact that every
predicate on a discrete type is trivially continuous.

The hole that we cannot fill asks us to prove that (𝓔xs x) and (𝓔xs y),
both of type Π (T ∘ succ) and both candidates for the tail-predicate,
are close.

Intuitively, our selection functionals should follow a specific search
strategy -- given the same predicate, they should return the same answer.
Furthermore, given 'similar' predicates, they should return close answers.

**Continuous condition**

\begin{code}

_is-constant-u-mod-of_on_and_
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → ℕ → (X → Y) → (X × X → ℕ∞) → (Y × Y → ℕ∞) → 𝓤 ̇ 
δ is-constant-u-mod-of f on cx and cy
 = ∀ x₁ x₂ → (δ ↑) ≼ cx (x₁ , x₂) → (δ ↑) ≼ cy (f(x₁) , f(x₂))

continuous-c-searcher : {Y : 𝓤 ̇ } → (cy : Y × Y → ℕ∞) → c-searchable Y cy → (𝓤 ⁺) ̇ 
continuous-c-searcher {𝓤} {Y} cy Sy
 = {X : 𝓤 ̇ } → (cx : X × X → ℕ∞) → (ps : (x : X) → d-predicate Y)
 → (δ : ℕ) (ϕs : (x : X) → δ is-u-mod-of pr₁ (ps x) on cy)
 → δ is-constant-u-mod-of (λ x → pr₁ (Sy (pr₁ (ps x) , pr₂ (ps x) , δ , ϕs x))) on cx and cy

𝟚-is-searchable' : ((p , d) : d-predicate 𝟚) → decidable (p ₁) → Σ x₀ ꞉ 𝟚 , (Σ p → p x₀)
𝟚-is-searchable' (p , d) (inl p₁) = ₁ , (λ _ → p₁)
𝟚-is-searchable' (p , d) (inr f ) = ₀ , δ where
    δ : Σ p → p ₀
    δ (₀ , p₀) = p₀
    δ (₁ , p₁) = 𝟘-elim (f p₁)

𝟚-is-continuous-c-searcher : continuous-c-searcher
                               (discrete-clofun 𝟚-is-discrete)
                               λ (p , d , _) → 𝟚-is-searchable' (p , d) (d ₁)
𝟚-is-continuous-c-searcher cx ps δ ϕs x₁ x₂ δ≼ n r = {!!}
{-
  γ : (d₁ : decidable (pr₁ (ps x₁) ₁))
    → (d₂ : decidable (pr₁ (ps x₂) ₁))
    → pr₁ (discrete-clofun 𝟚-is-discrete
          ((pr₁ (𝟚-is-searchable' (ps x₁) d₁))
          , (pr₁ (𝟚-is-searchable' (ps x₂) d₂)))) n ≡ ₁
  γ (inl _) (inl _) = refl
  γ (inr _) (inr _) = refl
  γ (inl e) (inr f) = 𝟘-elim (f {!!})
  γ (inr f) (inl e) = {!!}
-}
\end{code}

**Tychonoff Theorem: Second Attempt**

\begin{code}

tychonoff : ((T , cs) : sequence-of-codistance-types)
          → ((n : ℕ) → is-clofun (cs n))
          → (Ss : (n : ℕ) → c-searchable (T n) (cs n))
          → ((n : ℕ) → continuous-c-searcher (cs n) (Ss n))
          → Σ S ꞉ c-searchable (Π T) (Π-codistance (T , cs))
          , continuous-c-searcher (Π-codistance (T , cs)) S

tychonoff' : ((T , cs) : sequence-of-codistance-types)
            → ((n : ℕ) → is-clofun (cs n))
            → (Ss : (n : ℕ) → c-searchable (T n) (cs n))
            → ((n : ℕ) → continuous-c-searcher (cs n) (Ss n))
            → (δ : ℕ)
            → Σ S1 ꞉ (((p , d) : d-predicate (Π T))
                   → δ is-u-mod-of p on (Π-codistance (T , cs))
                   → Π T)
            , (((p , d) : d-predicate (Π T))
                   → (ϕ : δ is-u-mod-of p on (Π-codistance (T , cs)))
                   → Σ p → p (S1 (p , d) ϕ))
            × ({X : 𝓤₀ ̇ } (cx : X × X → ℕ∞) → (ps : (x : X) → d-predicate (Π T))
                   → (ϕs : (x : X) → δ is-u-mod-of pr₁ (ps x) on (Π-codistance (T , cs)))
                   → δ is-constant-u-mod-of (λ x → S1 (ps x) (ϕs x)) on cx and (Π-codistance (T , cs)))

tychonoff (T , cs) ss Ss ccs = (λ (p , d , δ , ϕ) → pr₁ (γ δ) (p , d) ϕ
                                                  , pr₁ (pr₂ (γ δ)) (p , d) ϕ)
                                    , λ cx ps δ ϕ → pr₂ (pr₂ (γ δ)) cx ps ϕ
 where γ = λ δ → tychonoff' (T , cs) ss Ss ccs δ

head-predicate : ((T , cs) : sequence-of-codistance-types)
                → ((n : ℕ) → is-clofun (cs n))
                → (Ss : (n : ℕ) → c-searchable (T n) (cs n))
                → ((n : ℕ) → continuous-c-searcher (cs n) (Ss n))
                → ((p , d) : d-predicate (Π T))
                → (δ : ℕ) → succ δ is-u-mod-of p on (Π-codistance (T , cs))
                → uc-d-predicate (T 0) (cs 0)
head-predicate (T , cs) ss Ss ccs (p , d) δ ϕ = pₕ , dₕ , succ δ , ϕₕ
 where
   𝓔xs : T 0 → Π (T ∘ succ)
   𝓔xs x = pr₁ (tychonoff' (T ∘ succ , cs ∘ succ) (ss ∘ succ) (Ss ∘ succ) (ccs ∘ succ) δ)
               (tail-predicate (p , d) x)
               (tail-predicate-reduce-mod (T , cs) ss (p , d) x δ ϕ)
   pₕ = λ x → p (x :: 𝓔xs x)
   dₕ = λ x → d (x :: 𝓔xs x)
   ϕₕ : succ δ is-u-mod-of pₕ on cs 0
   ϕₕ (x , y) δ≼cxy pₕxs = ϕ (x :: 𝓔xs x , y :: 𝓔xs y) γ pₕxs where
     γ : (succ δ ↑) ≼ Π-codistance (T , cs) ((x :: 𝓔xs x) , (y :: 𝓔xs y))
     γ 0 r = δ≼cxy 0 r -- δ≼cxy 0 r
     γ (succ n) r = Lemma[a≡₁→b≡₁→min𝟚ab≡₁] (δ≼cxy (succ n) r)
                      (pr₂ (pr₂ (tychonoff' (T ∘ succ , cs ∘ succ) (ss ∘ succ) (Ss ∘ succ) (ccs ∘ succ) δ))
                         (cs 0)
                         (tail-predicate (p , d))
                         (λ x' → tail-predicate-reduce-mod (T , cs) ss (p , d) x' δ ϕ)
                         x y ζ n r)
      where
        ζ : (δ ↑) ≼ cs 0 (x , y)
        ζ 0 r = δ≼cxy 0 refl
        ζ (succ n) r = δ≼cxy (succ n) (pr₂ (δ ↑) n r)

trivial-seq : ((T , cs) : sequence-of-codistance-types)
            → ((n : ℕ) → c-searchable (T n) (cs n))
            → Π T
trivial-seq (T , cs) Ss n = c-searchable-types-are-inhabited (cs n) (Ss n)

tychonoff' (T , cs) ss Ss ccs 0 = Searcher , Condition , Continuous where
  Searcher : ((p , d) : d-predicate (Π T))
           → 0 is-u-mod-of p on Π-codistance (T , cs)
           → Π T
  Searcher p ϕ n = c-searchable-types-are-inhabited (cs n) (Ss n)

  Condition : ((p , d) : d-predicate (Π T))
            → (ϕ : 0 is-u-mod-of p on Π-codistance (T , cs))
            → Σ p → p (Searcher (p , d) ϕ)
  Condition p ϕ (α , pα) = 0-mod-always-satisfied (Π-codistance (T , cs)) p ϕ (α , pα) (Searcher p ϕ)

  Continuous : {X : 𝓤₀ ̇ } (cx : X × X → ℕ∞) → (ps : (x : X) → d-predicate (Π T))
             → (ϕs : (x : X) → 0 is-u-mod-of pr₁ (ps x) on (Π-codistance (T , cs)))
             → 0 is-constant-u-mod-of (λ x → Searcher (ps x) (ϕs x)) on cx and (Π-codistance (T , cs))
  Continuous _ ps ϕs x y _ = Zero-minimal (Π-codistance (T , cs) (Searcher (ps x) (ϕs x) , Searcher (ps y) (ϕs y)))

tychonoff' (T , cs) ss Ss ccs (succ δ) = Searcher , Condition , Continuous where
  IH = tychonoff' (T ∘ succ , cs ∘ succ) (ss ∘ succ) (Ss ∘ succ) (ccs ∘ succ) δ

  S-head = λ p ϕ → Ss 0 (head-predicate (T , cs) ss Ss ccs p δ ϕ)
  
  x   = λ p ϕ → pr₁ (S-head p ϕ)
  𝓔xs = λ p ϕ x' → pr₁ IH (tail-predicate p x')
                          (tail-predicate-reduce-mod (T , cs) ss p x' δ ϕ)

  Searcher : ((p , d) : d-predicate (Π T))
           → succ δ is-u-mod-of p on Π-codistance (T , cs)
           → Π T
  Searcher p ϕ = x p ϕ :: 𝓔xs p ϕ (x p ϕ)

  Condition : ((p , d) : d-predicate (Π T))
            → (ϕ : succ δ is-u-mod-of p on Π-codistance (T , cs))
            → Σ p → p (Searcher (p , d) ϕ)
  Condition (p , d) ϕ (α₀ , pα₀)
   = γₕ (x₀ , γₜ x₀ (xs₀ , transport p (head-tail-eta α₀) pα₀)) where
    γₕ = pr₂ (S-head (p , d) ϕ)
    γₜ = λ x' → pr₁ (pr₂ IH) (tail-predicate (p , d) x')
                             (tail-predicate-reduce-mod (T , cs) ss (p , d) x' δ ϕ)
    x₀  = α₀ 0
    xs₀ = α₀ ∘ succ

  Continuous : {X : 𝓤₀ ̇ } (cx : X × X → ℕ∞) → (ps : (x : X) → d-predicate (Π T))
             → (ϕs : (x : X) → (succ δ) is-u-mod-of pr₁ (ps x) on (Π-codistance (T , cs)))
             → (succ δ) is-constant-u-mod-of (λ x → Searcher (ps x) (ϕs x)) on cx and (Π-codistance (T , cs))
  Continuous cx ps ϕs a b δ≼cxy zero r = A 0 refl where
    A : (succ δ ↑) ≼ (cs 0) (x (ps a) (ϕs a) , x (ps b) (ϕs b))
    A = ccs 0 cx (λ x' → (pr₁ (pH x')) , (pr₁ (pr₂ (pH x')))) (succ δ) (λ x' → pr₂ (pr₂ (pr₂ (pH x'))))
          a b δ≼cxy
     where
       pH : ∀ x' → uc-d-predicate (T 0) (cs 0)
       pH = λ x' → head-predicate (T , cs) ss Ss ccs (ps x') δ (ϕs x')
  Continuous cx pds ϕs a b δ≼cxy (succ n) r = Lemma[a≡₁→b≡₁→min𝟚ab≡₁] (A (succ n) r) (B n r) where
    A : (succ δ ↑) ≼ (cs 0) (x (pds a) (ϕs a) , x (pds b) (ϕs b))
    A = ccs 0 cx (λ x' → (pr₁ (pH x')) , pr₁ (pr₂ (pH x'))) (succ δ) (λ x' → pr₂ (pr₂ (pr₂ (pH x'))))
          a b δ≼cxy
     where
       pH : ∀ x' → uc-d-predicate (T 0) (cs 0)
       pH = λ x' → head-predicate (T , cs) ss Ss ccs (pds x') δ (ϕs x')
    B : (     δ ↑) ≼ Π-codistance (T ∘ succ , cs ∘ succ) (𝓔xs (pds a) (ϕs a) (x (pds a) (ϕs a))
                                                        , 𝓔xs (pds b) (ϕs b) (x (pds b) (ϕs b)))
    B = pr₂ (pr₂ IH) cx (λ x' → tail-predicate (pds x') (x (pds x') (ϕs x')))
          (λ x' → tail-predicate-reduce-mod (T , cs) ss (pds x') (x (pds x') (ϕs x')) δ (ϕs x')) a b ζ
     where
       ζ : (δ ↑) ≼ cx (a , b)
       ζ 0 r = δ≼cxy 0 refl
       ζ (succ n) r = pr₂ (cx (a , b)) (succ n) (δ≼cxy (succ (succ n)) r)

YES : {X : 𝓤₀ ̇ } → (ds : is-discrete X) → (S : c-searchable X (discrete-clofun ds))
    → continuous-c-searcher (discrete-clofun ds) S
YES ds S cx pds δ ϕs x y δ≼cxy n r = {!!}

\end{code}

→c-searchable : {X : 𝓤₀ ̇ } → (ds : is-discrete X) → c-searchable X (discrete-clofun ds)
               → Σ (continuous-c-searcher (discrete-seq-clofun ds))
→c-searchable {X} ds S = transport (λ - → Σ (continuous-c-searcher -))
                            (fe (λ (α , β) → ℕ∞-equals λ n → SAME ds S α β n
                                               (discrete-decidable-seq ds α β n)))
                            (tychonoff ((λ _ → X) , (λ _ → discrete-clofun ds))
                                       (λ _ → discrete-is-clofun ds)
                                       (λ _ → S)
                                       (λ _ → YES ds S))

ℕ→𝟚-c-searchable : Σ (continuous-c-searcher (discrete-seq-clofun 𝟚-is-discrete))
ℕ→𝟚-c-searchable = →c-searchable 𝟚-is-discrete (searchable→c-searchable (discrete-clofun 𝟚-is-discrete) 𝟚-is-searchable)

ℕ→ℕ→X-c-searchable : {X : 𝓤₀ ̇ } → (ds : is-discrete X) → c-searchable X (discrete-clofun ds)
                    → Σ (continuous-c-searcher (Π-codistance ((λ _ → ℕ → X) , (λ _ → discrete-seq-clofun ds))))
ℕ→ℕ→X-c-searchable {X} ds S = tychonoff ((λ _ → ℕ → X) , (λ _ → discrete-seq-clofun ds))
                                          (λ _ → discrete-seq-is-clofun ds)
                                          (λ _ → pr₁ (→c-searchable ds S))
                                          (λ _ → pr₂ (→c-searchable ds S))

ℕ→ℕ→𝟚-c-searchable : c-searchable (ℕ → (ℕ → 𝟚)) (Π-codistance ((λ _ → ℕ → 𝟚) , (λ _ → discrete-seq-clofun 𝟚-is-discrete)))
ℕ→ℕ→𝟚-c-searchable = {!!}

𝔽 : ℕ → 𝓤₀ ̇
𝔽 0 = 𝟙
𝔽 (succ n) = 𝔽 n + 𝟙

{-
Π 𝔽 is the type of sequences
{x₁ , x₂ , x₃ , x₄ , ...}
where
x₁ : 𝟙
x₂ : 𝟙 + 𝟙
x₃ : 𝟙 + 𝟙 + 𝟙
x₄ : 𝟙 + 𝟙 + 𝟙 + 𝟙
...
-}

Codistance : (n : ℕ) → 𝔽 n × 𝔽 n → ℕ∞
Codistance 0 (* , *) = ∞
Codistance (succ n) (inl x , inl y) = Codistance n (x , y)
Codistance (succ n) (inl _ , inr _) = 0 ↑
Codistance (succ n) (inr _ , inl _) = 0 ↑
Codistance (succ n) (inr * , inr *) = ∞
{-
Predicate : uc-d-predicate (Π 𝔽) (Π-codistance (𝔽 , Codistance))
Predicate = p , {!!} , {!!} where
  (p , d) : d-predicate (Π 𝔽)
  p α = (n : ℕ) → p* n (α n) where
    p* : (n : ℕ) → predicate (𝔽 n)
    p* zero * = 𝟙
    p* (succ n) (inl _) = 𝟘
    p* (succ n) (inr *) = 𝟙
  ϕ : {!!}
  ϕ = {!!}
-}
