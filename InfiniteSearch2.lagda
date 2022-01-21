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

sequence-of-clofun-types : 𝓤₁ ̇ 
sequence-of-clofun-types = Σ T ꞉ (ℕ → 𝓤₀ ̇ ) , Π n ꞉ ℕ , (T n × T n → ℕ∞)

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

    0  1    3  4  5   ⋯
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

Π-clofun' : ((T , cs) : sequence-of-clofun-types) → Π T × Π T → (ℕ → 𝟚)
Π-clofun' (T , cs) (A , B) 0 = pr₁ (cs 0 (A 0 , B 0)) 0
Π-clofun' (T , cs) (A , B) (succ n)
 = min𝟚 (pr₁ (cs 0 (A 0 , B 0)) (succ n))
        (Π-clofun' (T ∘ succ , cs ∘ succ) ((A ∘ succ) , (B ∘ succ)) n)

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

\begin{code}


\end{code}

We now show that, if every underlying cₙ satisfies the four properties of a
closeness function, then so does Π-clofun.

\begin{code}

Π-clofun'-eic : ((T , cs) : sequence-of-clofun-types)
                  → ((n : ℕ) (α : T n) → cs n (α , α) ≡ ∞)
                  → (A : Π T) → Π-clofun (T , cs) (A , A) ≡ ∞
Π-clofun'-eic (T , cs) eics A = ℕ∞-equals (γ (T , cs) eics A)
 where
   γ : ((T , cs) : sequence-of-clofun-types)
     → ((n : ℕ) (α : T n) → cs n (α , α) ≡ ∞)
     → (A : Π T) → Π-clofun' (T , cs) (A , A) ∼ (λ _ → ₁)
   γ (T , cs) eics A = γ' where
     γ' : (i : ℕ) → Π-clofun' (T , cs) (A , A) i ≡ ₁
     γ' 0        = ap (λ - → pr₁ - 0) (eics 0 (A 0))
     γ' (succ i) = Lemma[a≡₁→b≡₁→min𝟚ab≡₁]
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
                           → (ss : (n : ℕ) → is-clofun (cs n))
                           → is-clofun (Π-clofun (T , cs))
                           
is-clofun.equal→inf-close
 (Π-is-clofun (T , cs) ss)
 = Π-clofun'-eic (T , cs)
     (λ n → is-clofun.equal→inf-close (ss n))
     
is-clofun.inf-close→equal
 (Π-is-clofun (T , cs) ss)
 = λ A B f → Π-clofun'-ice (T , cs)
     (λ n (α , β) → is-clofun.inf-close→equal (ss n) α β)
     (A , B) f
 
is-clofun.symmetricity
 (Π-is-clofun (T , cs) ss)
 = λ A B → Π-clofun'-sym (T , cs)
     (λ n (α , β) → is-clofun.symmetricity (ss n) α β)
     (A , B)

is-clofun.ultrametric
 (Π-is-clofun (T , cs) ss)
 = λ A B C → Π-clofun'-ult (T , cs)
     (λ n (α , β , ζ) → is-clofun.ultrametric (ss n) α β ζ)
     (A , B , C)

\end{code}

**Tychonff Theorem**

We can now state the Tychonoff theorem.

\begin{code}

they-agree : {X : 𝓤 ̇ } → d-predicate X → d-predicate X → 𝓤 ̇ 
they-agree {𝓤} {X} (p₁ , d₁) (p₂ , d₂)
  = ((x : X) → p₁ x → p₂ x) × ((x : X) → p₂ x → p₁ x)

Cont : {X : 𝓤 ̇ } → (c : X × X → ℕ∞) → c-searchable X c → (𝓤₀ ⁺) ⊔ 𝓤 ̇ 
Cont {𝓤} {X} c S = ((p₁ , d₁) (p₂ , d₂) : d-predicate X)
                 → (δ : ℕ)
                 → (ϕ₁ : δ is-u-mod-of p₁ on c)
                 → (ϕ₂ : δ is-u-mod-of p₂ on c)
                 → they-agree (p₁ , d₁) (p₂ , d₂)
                 → (δ ↑) ≼ c (pr₁ (S (p₁ , d₁ , δ , ϕ₁))
                            , pr₁ (S (p₂ , d₂ , δ , ϕ₂)))

tychonoff : ((T , cs) : sequence-of-clofun-types)
          → ((n : ℕ) → is-clofun (cs n))
          → (Ss : (n : ℕ) → c-searchable (T n) (cs n))
          → ((n : ℕ) → Cont (cs n) (Ss n))
          → c-searchable (Π T) (Π-clofun (T , cs))    

Searcher : ((T , cs) : sequence-of-clofun-types)
         → ((n : ℕ) → is-clofun (cs n))
         → (Ss : (n : ℕ) → c-searchable (T n) (cs n))
         → ((n : ℕ) → Cont (cs n) (Ss n))
         → ((p , d) : d-predicate (Π T))
         → (δ : ℕ)
         → δ is-u-mod-of p on Π-clofun (T , cs)
         → Π T

Condition : ((T , cs) : sequence-of-clofun-types)
          → (ss : (n : ℕ) → is-clofun (cs n))
          → (Ss : (n : ℕ) → c-searchable (T n) (cs n))
          → (ccs : (n : ℕ) → Cont (cs n) (Ss n))  
          → ((p , d) : d-predicate (Π T))
          → (δ : ℕ)
          → (ϕ : δ is-u-mod-of p on Π-clofun (T , cs))
          → Σ p → p (Searcher (T , cs) ss Ss ccs (p , d) δ ϕ)

tail-predicate : {T : ℕ → 𝓤₀ ̇ }
               → ((p , d) : d-predicate (Π T))
               → (x : T 0) → d-predicate (Π (T ∘ succ))
tail-predicate (p , d) x = (λ xs → p (x :: xs)) , (λ xs → d (x :: xs))

build-up : ((T , cs) : sequence-of-clofun-types)
          → ((n : ℕ) → is-clofun (cs n))
          → (xs ys : Π (T ∘ succ)) → (δ : ℕ)
          → (δ ↑) ≼ Π-clofun (T ∘ succ , cs ∘ succ) (xs , ys)
          → (x : T 0)
          → (succ δ ↑) ≼ Π-clofun (T , cs) (x :: xs , x :: ys)
build-up (T , cs) ss xs ys δ δ≼cxsys x 0 refl
 = ap (λ - → pr₁ - 0) (is-clofun.equal→inf-close (ss 0) x)
build-up (T , cs) ss xs ys δ δ≼cxsys x (succ n) r
 = Lemma[a≡₁→b≡₁→min𝟚ab≡₁]
    (ap (λ - → pr₁ - (succ n)) (is-clofun.equal→inf-close (ss 0) x))
    (δ≼cxsys n r)

build-up-hd : ((T , cs) : sequence-of-clofun-types)
            → ((n : ℕ) → is-clofun (cs n))
            → (x y : T 0) → (δ : ℕ)
            → (succ δ ↑) ≼ cs 0 (x , y)
            → (xs : Π (T ∘ succ))
            → (succ δ ↑) ≼ Π-clofun (T , cs) (x :: xs , y :: xs)
build-up-hd (T , cs) ss x y δ δ≼cxy xs 0 refl
 = δ≼cxy 0 refl
build-up-hd (T , cs) ss x y δ δ≼cxy xs (succ n) r
 = Lemma[a≡₁→b≡₁→min𝟚ab≡₁]
    (δ≼cxy (succ n) r)
    (ap (λ - → pr₁ - n)
      (is-clofun.equal→inf-close (Π-is-clofun (T ∘ succ , cs ∘ succ) (ss ∘ succ)) xs))

tail-predicate-reduce-mod : ((T , cs) : sequence-of-clofun-types)
                          → (ss : (n : ℕ) → is-clofun (cs n))
                          → ((p , d) : d-predicate (Π T))
                          → (x : T 0) → (δ : ℕ)
                          → (succ δ) is-u-mod-of p on Π-clofun (T , cs)
                          →       δ  is-u-mod-of (pr₁ (tail-predicate (p , d) x))
                                                 on Π-clofun ((T ∘ succ) , (cs ∘ succ))
tail-predicate-reduce-mod (T , cs) ss p x δ ϕ (xs , ys) δ≼cxsys
 = ϕ (x :: xs , x :: ys) (build-up (T , cs) ss xs ys δ δ≼cxsys x)

tail-predicate-agree : ((T , cs) : sequence-of-clofun-types)
                     → (ss : (n : ℕ) → is-clofun (cs n))
                     → ((p₁ , d₁) (p₂ , d₂) : d-predicate (Π T))
                     → they-agree (p₁ , d₁) (p₂ , d₂)
                     → (x y : T 0) → (δ : ℕ)
                     → (succ δ ↑) ≼ cs 0 (x , y)
                     → (succ δ) is-u-mod-of p₁ on Π-clofun (T , cs)
                     → (succ δ) is-u-mod-of p₂ on Π-clofun (T , cs)
                     → they-agree (tail-predicate (p₁ , d₁) x) (tail-predicate (p₂ , d₂) y)
tail-predicate-agree (T , cs) ss (p₁ , d₁) (p₂ , d₂) ag x y δ δ≼cxy ϕ₁ ϕ₂
 = (λ xs p₁xxs → pr₁ ag (y :: xs) (ϕ₁ _ (γ xs)  p₁xxs))
 , (λ xs p₂xxs → pr₂ ag (x :: xs) (ϕ₂ _ (γ' xs) p₂xxs))
 where
   γ : (xs : Π (T ∘ succ)) → (succ δ ↑) ≼ Π-clofun (T , cs) (x :: xs , y :: xs)
   γ xs = build-up-hd (T , cs) ss x y δ δ≼cxy xs
   γ' : (xs : Π (T ∘ succ)) → (succ δ ↑) ≼ Π-clofun (T , cs) (y :: xs , x :: xs)
   γ' xs = transport ((succ δ ↑) ≼_)
             (is-clofun.symmetricity (Π-is-clofun (T , cs) ss) (y :: xs) (x :: xs) ⁻¹) (γ xs)

Conty : ((T , cs) : sequence-of-clofun-types)
      → (ss : (n : ℕ) → is-clofun (cs n))
      → (Ss : (n : ℕ) → c-searchable (T n) (cs n))
      → (ccs : (n : ℕ) → Cont (cs n) (Ss n))
      → ((p₁ , d₁) (p₂ , d₂) : d-predicate (Π T))
      → they-agree (p₁ , d₁) (p₂ , d₂)
      → (δ : ℕ)
      → (ϕ₁ : δ is-u-mod-of p₁ on Π-clofun (T , cs))
      → (ϕ₂ : δ is-u-mod-of p₂ on Π-clofun (T , cs))
      → (δ ↑) ≼ Π-clofun (T , cs)
                  (Searcher (T , cs) ss Ss ccs (p₁ , d₁) δ ϕ₁
                 , Searcher (T , cs) ss Ss ccs (p₂ , d₂) δ ϕ₂)

𝟚-is-c-searchable'' : (p : 𝟚 → 𝓤 ̇ )
                    → decidable (p ₁)
                    → Σ x ꞉ 𝟚 , (Σ p → p x)
𝟚-is-c-searchable'' p (inl  p₁)
 = ₁ , λ _ → p₁
𝟚-is-c-searchable'' p (inr ¬p₁)
 = ₀ , λ (x₀ , px₀) → 𝟚-equality-cases
                          (λ e → transport p e px₀)
                          (λ e → 𝟘-elim (¬p₁ (transport p e px₀)))

𝟚-is-c-searchable' : c-searchable 𝟚 (discrete-clofun 𝟚-is-discrete)
𝟚-is-c-searchable' (p , d , _ , _) = 𝟚-is-c-searchable'' p (d ₁)

dec-agree : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → decidable X → decidable Y → 𝓤₀ ̇
dec-agree (inl _) (inl _) = 𝟙
dec-agree (inr _) (inr _) = 𝟙
dec-agree (inl _) (inr _) = 𝟘
dec-agree (inr _) (inl _) = 𝟘

𝟚-is-Cont : Cont (discrete-clofun 𝟚-is-discrete) 𝟚-is-c-searchable'
𝟚-is-Cont (p₁ , d₁) (p₂ , d₂) δ ϕ₁ ϕ₂ ag
 = transport (λ - → (δ ↑) ≼ discrete-clofun 𝟚-is-discrete (pr₁ (𝟚-is-c-searchable'' p₁ (d₁ ₁)) , -))
     (e _ _ (f (d₁ ₁) (d₂ ₁)))
     (transport ((δ ↑) ≼_)
       ((is-clofun.equal→inf-close (discrete-is-clofun 𝟚-is-discrete)
         (pr₁ (𝟚-is-c-searchable'' p₁ (d₁ ₁)))) ⁻¹)
       (∞-maximal (δ ↑)))
 where
   f : ∀ a b → dec-agree a b
   f (inl _) (inl _) = *
   f (inl a) (inr f) = f (pr₁ ag ₁ a)
   f (inr f) (inl b) = f (pr₂ ag ₁ b)
   f (inr _) (inr _) = *
   e : ∀ a b → dec-agree a b → pr₁ (𝟚-is-c-searchable'' p₁ a) ≡ pr₁ (𝟚-is-c-searchable'' p₂ b)
   e (inl _) (inl _) decag = refl
   e (inr _) (inr _) decag = refl

head-predicate : ((T , cs) : sequence-of-clofun-types)
               → ((n : ℕ) → is-clofun (cs n))
               → (Ss : (n : ℕ) → c-searchable (T n) (cs n))
               → ((n : ℕ) → Cont (cs n) (Ss n))
               → ((p , d) : d-predicate (Π T))
               → (δ : ℕ) → succ δ is-u-mod-of p on (Π-clofun (T , cs))
               → uc-d-predicate (T 0) (cs 0)
head-predicate (T , cs) ss Ss ccs (p , d) δ ϕ = pₕ , dₕ , succ δ , ϕₕ
 where
   𝓔xs : T 0 → Π (T ∘ succ)
   𝓔xs x = Searcher (T ∘ succ , cs ∘ succ) (ss ∘ succ) (Ss ∘ succ) (ccs ∘ succ)
               (tail-predicate (p , d) x)
               δ (tail-predicate-reduce-mod (T , cs) ss (p , d) x δ ϕ)
   pₕ = λ x → p (x :: 𝓔xs x)
   dₕ = λ x → d (x :: 𝓔xs x)
   ϕₕ : succ δ is-u-mod-of pₕ on cs 0
   ϕₕ (x , y) δ≼cxy pₕxs = ϕ (x :: 𝓔xs x , y :: 𝓔xs y) γ pₕxs where
     γ : (succ δ ↑) ≼ Π-clofun (T , cs) ((x :: 𝓔xs x) , (y :: 𝓔xs y))
     γ 0 r = δ≼cxy 0 r
     γ (succ n) r = Lemma[a≡₁→b≡₁→min𝟚ab≡₁] (δ≼cxy (succ n) r)
                      (Conty (T ∘ succ , cs ∘ succ) (ss ∘ succ) (Ss ∘ succ) (ccs ∘ succ)
                        (tail-predicate (p , d) x) (tail-predicate (p , d) y)
                        (tail-predicate-agree (T , cs) ss (p , d) (p , d)
                          ((λ _ → id) , (λ _ → id)) x y δ δ≼cxy ϕ ϕ)
                        δ
                        (tail-predicate-reduce-mod (T , cs) ss (p , d) x δ ϕ)
                        (tail-predicate-reduce-mod (T , cs) ss (p , d) y δ ϕ)
                        n r)

head-predicate-agree : ((T , cs) : sequence-of-clofun-types)
                     → (ss : (n : ℕ) → is-clofun (cs n))
                     → (Ss : (n : ℕ) → c-searchable (T n) (cs n))
                     → (ccs : (n : ℕ) → Cont (cs n) (Ss n))
                     → ((p₁ , d₁) (p₂ , d₂) : d-predicate (Π T))
                     → they-agree (p₁ , d₁) (p₂ , d₂)
                     → (δ : ℕ)
                     → (ϕ₁ : (succ δ) is-u-mod-of p₁ on Π-clofun (T , cs))
                     → (ϕ₂ : (succ δ) is-u-mod-of p₂ on Π-clofun (T , cs))
                     → let ph1 = head-predicate (T , cs) ss Ss ccs (p₁ , d₁) δ ϕ₁ in
                       let ph2 = head-predicate (T , cs) ss Ss ccs (p₂ , d₂) δ ϕ₂ in
                       they-agree (pr₁ ph1 , pr₁ (pr₂ ph1)) (pr₁ ph2 , pr₁ (pr₂ ph2))
head-predicate-agree (T , cs) ss Ss ccs (p₁ , d₁) (p₂ , d₂) ag δ ϕ₁ ϕ₂
 = (λ x phx → pr₁ ag _ (ϕ₁ _ (γ  x) phx))
 , (λ x phx → pr₂ ag _ (ϕ₂ _ (γ' x) phx))
  where
    𝓔xs₁ 𝓔xs₂ : T 0 → Π (T ∘ succ)
    𝓔xs₁ x = Searcher (T ∘ succ , cs ∘ succ) (ss ∘ succ) (Ss ∘ succ) (ccs ∘ succ)
               (tail-predicate (p₁ , d₁) x)
               δ (tail-predicate-reduce-mod (T , cs) ss (p₁ , d₁) x δ ϕ₁)
    𝓔xs₂ x = Searcher (T ∘ succ , cs ∘ succ) (ss ∘ succ) (Ss ∘ succ) (ccs ∘ succ)
               (tail-predicate (p₂ , d₂) x)
               δ (tail-predicate-reduce-mod (T , cs) ss (p₂ , d₂) x δ ϕ₂)    
    δ≼cxx : (x : T 0) → (succ δ ↑) ≼ cs 0 (x , x)
    δ≼cxx x = transport ((succ δ ↑) ≼_)
                (is-clofun.equal→inf-close (ss 0) x ⁻¹)
                (∞-maximal (succ δ ↑))
    γ : (x : T 0) → (succ δ ↑) ≼ Π-clofun (T , cs) (x :: 𝓔xs₁ x , x :: 𝓔xs₂ x)
    γ x 0 r = δ≼cxx x 0 r
    γ x (succ n) r = Lemma[a≡₁→b≡₁→min𝟚ab≡₁]
                       (δ≼cxx x (succ n) r)
                       (Conty (T ∘ succ , cs ∘ succ) (ss ∘ succ) (Ss ∘ succ) (ccs ∘ succ)
                        (tail-predicate (p₁ , d₁) x) (tail-predicate (p₂ , d₂) x)
                        (tail-predicate-agree (T , cs) ss (p₁ , d₁) (p₂ , d₂)
                          ag x x δ (δ≼cxx x) ϕ₁ ϕ₂)
                        δ
                        (tail-predicate-reduce-mod (T , cs) ss (p₁ , d₁) x δ ϕ₁)
                        (tail-predicate-reduce-mod (T , cs) ss (p₂ , d₂) x δ ϕ₂)
                        n r)
    γ' : (x : T 0) → (succ δ ↑) ≼ Π-clofun (T , cs) (x :: 𝓔xs₂ x , x :: 𝓔xs₁ x)
    γ' x = transport ((succ δ ↑) ≼_)
              (is-clofun.symmetricity (Π-is-clofun (T , cs) ss) (x :: 𝓔xs₂ x) (x :: 𝓔xs₁ x) ⁻¹)
              (γ x)

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

\begin{code}

tychonoff (T , cs) ss Ss ccs (p , d , δ , ϕ) = (Searcher  (T , cs) ss Ss ccs (p , d) δ ϕ)
                                             , (Condition (T , cs) ss Ss ccs (p , d) δ ϕ)

trivial-seq : ((T , cs) : sequence-of-clofun-types)
            → ((n : ℕ) → c-searchable (T n) (cs n))
            → Π T
trivial-seq (T , cs) Ss n = c-searchable-types-are-inhabited (cs n) (Ss n)

Searcher (T , cs) ss Ss ccs (p , d) 0        ϕ
 = λ n → c-searchable-types-are-inhabited (cs n) (Ss n)
Searcher (T , cs) ss Ss ccs (p , d) (succ δ) ϕ
 = pr₁ (Ss 0 (head-predicate (T , cs) ss Ss ccs (p , d) δ ϕ))
 :: Searcher (T ∘ succ , cs ∘ succ) (ss ∘ succ) (Ss ∘ succ) (ccs ∘ succ)
      (tail-predicate (p , d) (pr₁ (Ss 0 (head-predicate (T , cs) ss Ss ccs (p , d) δ ϕ))))
      δ (tail-predicate-reduce-mod (T , cs) ss (p , d) (pr₁ (Ss 0 (head-predicate (T , cs) ss Ss ccs (p , d) δ ϕ))) δ ϕ)

Condition (T , cs) ss Ss ccs (p , d) 0        ϕ (α , pα)
 = 0-mod-always-satisfied (Π-clofun (T , cs)) (p , d) ϕ (α , pα) (Searcher (T , cs) ss Ss ccs (p , d) 0 ϕ)
Condition (T , cs) ss Ss ccs (p , d) (succ δ) ϕ (α , pα)
 = pr₂ (Ss 0 (head-predicate (T , cs) ss Ss ccs (p , d) δ ϕ))
   (head α
  , Condition (T ∘ succ , cs ∘ succ) (ss ∘ succ) (Ss ∘ succ) (ccs ∘ succ)
    (tail-predicate (p , d) (α 0))
    δ (tail-predicate-reduce-mod (T , cs) ss (p , d) (α 0) δ ϕ)
  (tail α , transport p (head-tail-eta α) pα))

Conty (T , cs) ss Ss ccs (p₁ , d₁) (p₂ , d₂) ag 0        ϕ₁ ϕ₂
 = Zero-minimal (Π-clofun (T , cs)
                     (Searcher (T , cs) ss Ss ccs (p₁ , d₁) 0 ϕ₁
                    , Searcher (T , cs) ss Ss ccs (p₂ , d₂) 0 ϕ₂))
Conty (T , cs) ss Ss ccs (p₁ , d₁) (p₂ , d₂) ag (succ δ) ϕ₁ ϕ₂ 0 r
 = ccs 0 (pr₁ ph1 , pr₁ (pr₂ ph1)) (pr₁ ph2 , pr₁ (pr₂ ph2))
         (succ δ)
         (pr₂ (pr₂ (pr₂ ph1)))
         (pr₂ (pr₂ (pr₂ ph2)))
         (head-predicate-agree (T , cs) ss Ss ccs (p₁ , d₁) (p₂ , d₂) ag δ ϕ₁ ϕ₂)
         0 r
 where
   ph1 = head-predicate (T , cs) ss Ss ccs (p₁ , d₁) δ ϕ₁
   ph2 = head-predicate (T , cs) ss Ss ccs (p₂ , d₂) δ ϕ₂
Conty (T , cs) ss Ss ccs (p₁ , d₁) (p₂ , d₂) ag (succ δ) ϕ₁ ϕ₂ (succ n) r
 = Lemma[a≡₁→b≡₁→min𝟚ab≡₁] (γ₁ (succ n) r) (γ₂ n r)
 where
   ph1 = head-predicate (T , cs) ss Ss ccs (p₁ , d₁) δ ϕ₁
   ph2 = head-predicate (T , cs) ss Ss ccs (p₂ , d₂) δ ϕ₂
   x y : T 0
   x  = pr₁ (Ss 0 ph1)
   y  = pr₁ (Ss 0 ph2)
   γ₁ = ccs 0 (pr₁ ph1 , pr₁ (pr₂ ph1))
              (pr₁ ph2 , pr₁ (pr₂ ph2))
              (succ δ)
              (pr₂ (pr₂ (pr₂ ph1)))
              (pr₂ (pr₂ (pr₂ ph2)))
              (head-predicate-agree (T , cs) ss Ss ccs (p₁ , d₁) (p₂ , d₂) ag δ ϕ₁ ϕ₂)
   γ₂ = Conty (T ∘ succ , cs ∘ succ) (ss ∘ succ) (Ss ∘ succ) (ccs ∘ succ)
          (tail-predicate (p₁ , d₁) x)
          (tail-predicate (p₂ , d₂) y)
          (tail-predicate-agree (T , cs) ss (p₁ , d₁) (p₂ , d₂) ag x y δ γ₁ ϕ₁ ϕ₂)
          δ
          (tail-predicate-reduce-mod (T , cs) ss (p₁ , d₁) x δ ϕ₁)
          (tail-predicate-reduce-mod (T , cs) ss (p₂ , d₂) y δ ϕ₂)

ℕ→𝟚-is-c-searchable' : c-searchable (ℕ → 𝟚)
                         (Π-clofun ((λ _ → 𝟚) , (λ _ → discrete-clofun 𝟚-is-discrete)))
ℕ→𝟚-is-c-searchable' = tychonoff
                         ((λ _ → 𝟚) , (λ _ → discrete-clofun 𝟚-is-discrete))
                         (λ _ → discrete-is-clofun 𝟚-is-discrete)
                         (λ _ → 𝟚-is-c-searchable')
                         (λ _ → 𝟚-is-Cont)

ℕ→ℕ→𝟚-is-c-searchable' : c-searchable (ℕ → (ℕ → 𝟚))
                           (Π-clofun ((λ _ → ℕ → 𝟚)
                           , (λ _ → Π-clofun ((λ _ → 𝟚) , (λ _ → discrete-clofun 𝟚-is-discrete)))))
ℕ→ℕ→𝟚-is-c-searchable' = tychonoff
                           ((λ _ → ℕ → 𝟚)
                           , (λ _ → Π-clofun ((λ _ → 𝟚) , (λ _ → discrete-clofun 𝟚-is-discrete))))
                           (λ n → Π-is-clofun ((λ _ → 𝟚) , (λ _ → discrete-clofun 𝟚-is-discrete))
                                    (λ _ → discrete-is-clofun 𝟚-is-discrete))
                           (λ n → ℕ→𝟚-is-c-searchable')
                           (λ δ (p₁ , d₁) (p₂ , d₂) δ ϕ₁ ϕ₂ ag
                            → Conty ((λ _ → 𝟚) , (λ _ → discrete-clofun 𝟚-is-discrete))
                                    (λ _ → discrete-is-clofun 𝟚-is-discrete)
                                    (λ _ → 𝟚-is-c-searchable')
                                    (λ _ → 𝟚-is-Cont)
                                    (p₁ , d₁)
                                    (p₂ , d₂)
                                    ag
                                    δ
                                    ϕ₁
                                    ϕ₂)

\end{code}
