{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

open import Prelude
open import NaturalsOrder
open import DecidableAndDetachable
open import UF-FunExt
open import GenericConvergentSequence
open import Two-Properties
open import UF-Subsingletons
open import DiscreteAndSeparated

module SearchableTypes (fe : FunExt) where

open import Codistance fe
open import Codistances fe
open sequences

searchable : {𝓥 : Universe} → (X : 𝓤 ̇ ) → Set (𝓤 ⊔ (𝓥 ⁺))
searchable {𝓤} {𝓥} X
 = (p : X → 𝓥 ̇ ) → detachable p
 → Σ x₀ ꞉ X , (Σ p → p x₀)

c-searchable : {𝓥 : Universe} {X : 𝓤 ̇ } → (X → X → ℕ∞) → Set (𝓤 ⊔ (𝓥 ⁺))
c-searchable {𝓤} {𝓥} {X} c
 = (p : X → 𝓥 ̇ ) → detachable p → continuous c p
 → Σ x₀ ꞉ X , (Σ p → p x₀)

searchable→c-searchable : {𝓥 : Universe} {X : 𝓤 ̇ } → (cx : X → X → ℕ∞)
                        → searchable {𝓤} {𝓥} X → c-searchable cx
searchable→c-searchable {𝓤} {𝓥} cx 𝓔Sx p d _ = 𝓔Sx p d

𝓔⟨_,_⟩ : {X : 𝓤 ̇ }
       → (c : X → X → ℕ∞) (𝓔S : c-searchable c)
       → (p : X → 𝓥 ̇ ) → detachable p → continuous c p → X
S⟨_,_⟩ : {X : 𝓤 ̇ }
       → (c : X → X → ℕ∞) (𝓔S : c-searchable c)
       → (p : X → 𝓥 ̇ ) (d : detachable p) (ϕ : continuous c p)
       → Σ p → p (𝓔⟨ c , 𝓔S ⟩ p d ϕ)

𝓔⟨ _ , 𝓔S ⟩ p d ϕ = pr₁ (𝓔S p d ϕ)
S⟨ _ , 𝓔S ⟩ p d ϕ = pr₂ (𝓔S p d ϕ)

𝓔S-dec : {X : 𝓤 ̇ } (c : X → X → ℕ∞)
      → (𝓔S : c-searchable c)
      → (p : X → 𝓥 ̇ ) → detachable p → continuous c p
      → Σ p + ((x : X) → ¬ p x)
𝓔S-dec {𝓤} {𝓥} {X} c 𝓔S p d ϕ
 = Cases (d x₀)
     (λ  px₀ → inl (x₀ , px₀)) 
     (λ ¬px₀ → inr λ x px → ¬px₀ (γ₀ (x , px)))
 where
  x₀ : X
  x₀ = pr₁ (𝓔S p d ϕ)
  γ₀ : Σ p → p x₀
  γ₀ = pr₂ (𝓔S p d ϕ)

∶∶-indistinguishable : {X : 𝓤 ̇ } (d≡ : is-discrete X)
                     → (α : ℕ → X) (m : ℕ∞)
                     → m ≼ (codistance X d≡) α (head α ∶∶ tail α)
∶∶-indistinguishable {𝓤} {X} d≡ α m n p
  = codistance-conceptually₁ X d≡
      α (head α ∶∶ tail α)
      n (λ k _ → head-tail-sim α k)

increase-distance : {X : 𝓤 ̇ } (d : is-discrete X)
                  → let c = codistance X d in
                    (xs ys : ℕ → X) (m : ℕ) → under m ≼ c xs ys
                  → (x : X) → Succ (under m) ≼ c (x ∶∶ xs) (x ∶∶ ys)
increase-distance {𝓤} {X} d xs ys m m≼cxsys x n n<sm
 = codistance-conceptually₁ X d (x ∶∶ xs) (x ∶∶ ys) n (γ n n<sm)
 where
   γ : (n : ℕ) → n ⊏ Succ (under m)
     → (k : ℕ) → k ≤ n → (x ∶∶ xs) k ≡ (x ∶∶ ys) k
   γ n x zero k≤n = refl
   γ (succ n) x (succ k) k≤n
     = codistance-conceptually₂ X d xs ys n (m≼cxsys n x) k k≤n

--- c0   c1    c2    c3 ....
--- 1    1
--- 1    0
--- 1    0
--- 0    0

-- c = 1 0 0 0 0 0
-- ms 0 = 2
-- ms 1 = 1

trivial-p : {X : 𝓤 ̇ } → X → 𝓥 ̇
trivial-p _ = 𝟙

trivial-d : {X : 𝓤 ̇ } → detachable (trivial-p {_} {𝓥} {X})
trivial-d _ = inl *

trivial-ϕ : {X : 𝓤 ̇ } → (c : X → X → ℕ∞) → continuous c (trivial-p {_} {𝓥} {X})
trivial-ϕ _ = 0 , λ _ _ _ _ → *

continuous-c-searcher : {𝓤 𝓥 𝓦 : Universe} {Y : 𝓤 ̇ }
                      → (cy : Y → Y → ℕ∞)
                      → c-searchable cy → Set (𝓤 ⊔ (𝓥 ⁺) ⊔ (𝓦 ⁺))
continuous-c-searcher {𝓤} {𝓥} {𝓦} {Y} cy 𝓔Sy
 = {X : 𝓦 ̇ }
 → (cx : X → X → ℕ∞)
 → (p : X → Y → 𝓥 ̇ )
 → (d : (x : X) → detachable (p x))
 → (m : ℕ) (ϕ : (x : X) → uc-mod-of cy (p x) m)
 → uc-mod-of² cx cy (λ x → 𝓔⟨ cy , 𝓔Sy ⟩ (p x) (d x) (m , ϕ x)) m m

≼-pred : (a b : ℕ∞) → Succ a ≼ b → a ≼ b
≼-pred a b sa≼b n = pr₂ b n ∘ (sa≼b (succ n))

→→-c-searchable : {𝓥 𝓦 : Universe} (T : ℕ → 𝓤 ̇ )
                → (cs : ((n : ℕ) → T n → T n → ℕ∞))
                → (es : ((n : ℕ) (x : T n) → Π (_⊏ cs n x x)))
                → ((n : ℕ) → c-searchable {𝓤} {𝓥} (cs n))
                → Σ (continuous-c-searcher {𝓤} {𝓥} {𝓦} (Π-codistance cs))
→→-c-searchable {𝓤} {𝓥} {𝓦} T cs es ss
 = (λ p d (m , ϕ) → η cs es ss m p d ϕ) , λ cx p d m ϕ → μ cs es ss m p d ϕ cx where
  η : {T : ℕ → 𝓤 ̇ }
    → (cs : Π n ꞉ ℕ , (T n → T n → ℕ∞))
    → (es : ((n : ℕ) (x : T n) → Π (_⊏ cs n x x)))
    → ((n : ℕ) → c-searchable (cs n))
    → (m : ℕ) → (p : Π T → 𝓥 ̇ ) → detachable p
    → uc-mod-of (Π-codistance cs) p m
    → Σ xs₀ ꞉ Π T , (Σ p → p xs₀)
  μ : {T : ℕ → 𝓤 ̇ } {X : 𝓦 ̇ }
    → (cs : Π n ꞉ ℕ , (T n → T n → ℕ∞))
    → (es : ((n : ℕ) (x : T n) → Π (_⊏ cs n x x)))
    → (ss : (n : ℕ) → c-searchable {𝓤} {𝓥} (cs n))
    → (m : ℕ) → (p : X → Π T → 𝓥 ̇ ) → (d : ∀ x → detachable (p x))
    → (ϕ : ∀ x → uc-mod-of (Π-codistance cs) (p x) m)
    → (cx : X → X → ℕ∞)
    → uc-mod-of² cx (Π-codistance cs) (λ x → pr₁ (η cs es ss m (p x) (d x) (ϕ x))) m m
  𝓔HD : {T : ℕ → 𝓤 ̇ } → (cs : ((n : ℕ) → T n → T n → ℕ∞))
      → (es : ((n : ℕ) (x : T n) → Π (_⊏ cs n x x)))
      → (ss  : ((n : ℕ) → c-searchable (cs n)))
      → (p : Π T → 𝓥 ̇ ) (d : detachable p) (m : ℕ) (ϕ : uc-mod-of (Π-codistance cs) p m)
      → T 0
  𝓔TL : {T : ℕ → 𝓤 ̇ } → (cs : ((n : ℕ) → T n → T n → ℕ∞))
      → (es : ((n : ℕ) (x : T n) → Π (_⊏ cs n x x)))
      → (ss  : ((n : ℕ) → c-searchable (cs n)))
      → (p : Π T → 𝓥 ̇ ) (d : detachable p) (m : ℕ) (ϕ : uc-mod-of (Π-codistance cs) p m)
      → T 0 → Π (T ∘ succ)
  pH : {T : ℕ → 𝓤 ̇ } → (cs : ((n : ℕ) → T n → T n → ℕ∞))
     → (es : ((n : ℕ) (x : T n) → Π (_⊏ cs n x x)))
     → (ss  : ((n : ℕ) → c-searchable (cs n)))
     → (p : Π T → 𝓥 ̇ ) (d : detachable p) (m : ℕ) (ϕ : uc-mod-of (Π-codistance cs) p m)
     → T 0 → 𝓥 ̇
  pH cs es ss p d 0 ϕ x = trivial-p T
  pH cs es ss p d (succ m) ϕ x = p (x :: 𝓔TL cs es ss p d (succ m) ϕ x)
  dH : {T : ℕ → 𝓤 ̇ } → (cs : ((n : ℕ) → T n → T n → ℕ∞))
     → (es : ((n : ℕ) (x : T n) → Π (_⊏ cs n x x)))
     → (ss  : ((n : ℕ) → c-searchable (cs n)))
     → (p : Π T → 𝓥 ̇ ) (d : detachable p) (m : ℕ) (ϕ : uc-mod-of (Π-codistance cs) p m)
     → detachable (pH cs es ss p d m ϕ)
  dH cs es ss p d 0 ϕ x = trivial-d T
  dH cs es ss p d (succ m) ϕ x = d (x :: 𝓔TL cs es ss p d (succ m) ϕ x)
  ϕH : {T : ℕ → 𝓤 ̇ } → (cs : ((n : ℕ) → T n → T n → ℕ∞))
     → (es : ((n : ℕ) (x : T n) → Π (_⊏ cs n x x)))
     → (ss  : ((n : ℕ) → c-searchable (cs n)))
     → (p : Π T → 𝓥 ̇ ) (d : detachable p) (m : ℕ) (ϕ : uc-mod-of (Π-codistance cs) p m)
     → continuous (cs 0) (pH cs es ss p d m ϕ)
  ϕH cs es ss p d 0 ϕ = trivial-ϕ (cs 0)
  ϕH cs es ss p d (succ m) ϕ = {!!}
  pT : {T : ℕ → 𝓤 ̇ } → (cs : ((n : ℕ) → T n → T n → ℕ∞))
     → (es : ((n : ℕ) (x : T n) → Π (_⊏ cs n x x)))
     → (ss  : ((n : ℕ) → c-searchable {𝓤} {𝓥} (cs n)))
     → (p : Π T → 𝓥 ̇ ) (d : detachable p) (m : ℕ) (ϕ : uc-mod-of (Π-codistance cs) p (succ m))
     → T 0 → Π (T ∘ succ) → 𝓥 ̇
  pT cs es ss p d m ϕ x xs = p (x :: xs)
  dT : {T : ℕ → 𝓤 ̇ } → (cs : ((n : ℕ) → T n → T n → ℕ∞))
     → (es : ((n : ℕ) (x : T n) → Π (_⊏ cs n x x)))
     → (ss  : ((n : ℕ) → c-searchable {𝓤} {𝓥} (cs n)))
     → (p : Π T → 𝓥 ̇ ) (d : detachable p) (m : ℕ) (ϕ : uc-mod-of (Π-codistance cs) p (succ m))
     → (x : T 0) → detachable (pT cs es ss p d m ϕ x)
  dT cs es ss p d m ϕ x xs = d (x :: xs)
  ϕT : {T : ℕ → 𝓤 ̇ } → (cs : ((n : ℕ) → T n → T n → ℕ∞))
     → (es : ((n : ℕ) (x : T n) → Π (_⊏ cs n x x)))
     → (ss  : ((n : ℕ) → c-searchable {𝓤} {𝓥} (cs n)))
     → (p : Π T → 𝓥 ̇ ) (d : detachable p) (m : ℕ) (ϕ : uc-mod-of (Π-codistance cs) p (succ m))
     → (x : T 0)
     → uc-mod-of (Π-codistance (cs ∘ succ)) (pT cs es ss p d m ϕ x) m
  ϕT cs es ss p d m ϕ x xs = {!!}
  

  𝓔HD cs es ss p d m ϕ
   = pr₁ (ss 0 (pH cs es ss p d m ϕ) (dH cs es ss p d m ϕ) (ϕH cs es ss p d m ϕ))
  𝓔TL cs es ss p d 0        ϕ x n = {!!}
  𝓔TL cs es ss p d (succ m) ϕ x = pr₁ (η (cs ∘ succ) (es ∘ succ) (λ n → ss (succ n)) m
                                      (pT cs es ss p d m ϕ x)
                                      (dT cs es ss p d m ϕ x)
                                      (ϕT cs es ss p d m ϕ x))
  η {T} cs es 𝓔S m p d ϕ
   = 𝓔HD cs es 𝓔S p d m ϕ :: 𝓔TL cs es 𝓔S p d m ϕ (𝓔HD cs es 𝓔S p d m ϕ)
   , {!!}
   {- where
     px→xs = λ x xs → p (x :: xs)
     dx→xs = λ x xs → d (x :: xs)
     ϕx→xs : (x : T 0) → uc-mod-of (Π-codistance (cs ∘ succ)) (px→xs x) m
     ϕx→xs x xs₁ xs₂ m≼cxs
      = ϕ (x :: xs₁) (x :: xs₂) (Π-codistance-Succ cs (es 0) x xs₁ xs₂ m m≼cxs)
     x→xs = λ x → pr₁ (η (cs ∘ succ) (es ∘ succ) (λ n → 𝓔S (succ n)) m
                       (px→xs x) (dx→xs x) (ϕx→xs x))
     px = λ x → px→xs x (x→xs x)
     dx = λ x → dx→xs x (x→xs x)
     ϕx : uc-mod-of (cs 0) px (succ m)
     ϕx x y m≼cxy = ϕ (x :: x→xs x) (y :: x→xs y)
                      (Π-codistance-Build cs x y (x→xs x) (x→xs y) m
                        m≼cxy
                        {!!}) -- (μ (cs ∘ succ) (es ∘ succ) (λ n → 𝓔S (succ n)) m px→xs dx→xs ϕx→xs
                          -- (cs 0) x y (≼-pred (under m) (cs 0 x y) m≼cxy)))
     IH₀ = 𝓔S 0 px dx (succ m , ϕx)
     x = pr₁ IH₀
     γ : Σ p → p (x :: x→xs x)
     γ (xs₀ , pxs₀)
      = pr₂ IH₀
          (xs₀h , pr₂ (η (cs ∘ succ) (es ∘ succ) (λ n → 𝓔S (succ n)) m
                       (px→xs xs₀h) (dx→xs xs₀h) (ϕx→xs xs₀h))
            (xs₀t , (ϕ xs₀ (xs₀h :: xs₀t) (Π-equivalent cs es xs₀ (succ m)) pxs₀)))
       where
        xs₀h = xs₀ 0
        xs₀t = xs₀ ∘ succ -}
  μ {T} {X} cs es 𝓔S (succ m) p d ϕ cx x y m≼cxy
   = Π-codistance-Build cs (𝓔→ x) (𝓔→ y) (𝓔→→ x) (𝓔→→ y) m
      {!!}
      (μ (cs ∘ succ) (es ∘ succ) (λ n → 𝓔S (succ n)) m
        (λ a → pT cs es 𝓔S (p a) (d a) m (ϕ a) (𝓔→ a))
        (λ a → dT cs es 𝓔S (p a) (d a) m (ϕ a) (𝓔→ a)) 
        (λ a → ϕT cs es 𝓔S (p a) (d a) m (ϕ a) (𝓔→ a))
        cx x y (≼-pred (under m) (cx x y) m≼cxy)) where
    𝓔→ : (a : X) → T 0
    𝓔→ a = 𝓔HD cs es 𝓔S (p a) (d a) (succ m) (ϕ a)
    𝓔→→ : (a : X) → Π (T ∘ succ)
    𝓔→→ a = 𝓔TL cs es 𝓔S (p a) (d a) (succ m) (ϕ a) (𝓔→ a)
    
{-
→-c-searchable : {X : 𝓤 ̇ } (d≡ : is-discrete X)
              → searchable X
              → c-searchable (codistance X d≡)
→-c-searchable {𝓤} {X} d≡ 𝓔Sx = λ p d (m , ϕ) → η m p d ϕ where
  Xᴺ = ℕ → X
  cixs = codistance X d≡
  η : (m : ℕ) → (p : Xᴺ → 𝓥 ̇ ) → detachable p → uc-mod-of cixs p m
    → Σ xs₀ ꞉ Xᴺ , (Σ p → p xs₀)
  η 0 p d ϕ = (λ _ → pr₁ (𝓔Sx {𝓤} (λ _ → 𝟙) (λ _ → inl *)))
            , (λ (xs₀ , pxs₀)
            → ϕ xs₀ (λ _ → pr₁ (𝓔Sx (λ _ → 𝟙) (λ _ → inl *))) (λ _ ()) pxs₀)
  η (succ m) p d ϕ = (x ∶∶ x→xs x) , γ
   where
     px→xs = λ x xs → p (x ∶∶ xs)
     dx→xs = λ x xs → d (x ∶∶ xs)
     ϕx→xs : (x : X) → uc-mod-of (codistance X d≡) (px→xs x) m
     ϕx→xs x xs₁ xs₂ m≼cxs
      = ϕ (x ∶∶ xs₁) (x ∶∶ xs₂) (increase-distance d≡ xs₁ xs₂ m m≼cxs x)
     x→xs : X → (ℕ → X)
     x→xs x = pr₁ (η m (px→xs x) (dx→xs x) (ϕx→xs x))
     px = λ x → p (x ∶∶ x→xs x)
     dx = λ x → d (x ∶∶ x→xs x)
     x : X
     x = pr₁ (𝓔Sx px dx)
     γ : Σ p → p (x ∶∶ x→xs x)
     γ (xs₀ , pxs₀)
      = pr₂ (𝓔Sx px dx)
          (head xs₀ , pr₂ (η m (px→xs (head xs₀))
                               (dx→xs (head xs₀)) (ϕx→xs (head xs₀)))
          (tail xs₀ , ϕ xs₀ (head xs₀ ∶∶ tail xs₀)
          (∶∶-indistinguishable d≡ xs₀ (under (succ m))) pxs₀))
-}
{-
×-c-searchable : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
              → (cx : X → X → ℕ∞) → (cy : Y → Y → ℕ∞)
              → c-searchable cx
              → (𝓔Sy : c-searchable cy)
              → ((x : X) → Π (_⊏ cx x x))
              → continuous-c-searcher cy cx 𝓔Sy 
              → c-searchable (×-codistance cx cy)
×-c-searchable {𝓤} {𝓥} {X} {Y} cx cy 𝓔Sx 𝓔Sy f Cy p d (m , ϕ)
 = (x , x→y x) , γ
  where
   px→y = λ x y → p (x , y)
   dx→y = λ x y → d (x , y)
   ϕx→y : (x : X) → uc-mod-of cy (px→y x) m
   ϕx→y x y₁ y₂ m≼cy
    = ϕ (x , y₁) (x , y₂)
        (×-codistance-min cx cy (under m) x x y₁ y₂ (λ n _ → f x n) m≼cy)
   x→y : X → Y
   x→y x = 𝓔⟨ cy , 𝓔Sy ⟩ (px→y x) (dx→y x) (m , ϕx→y x)
   px = λ x → p (x , x→y x)
   dx = λ x → d (x , x→y x)
   ϕx : continuous cx px
   ϕx = m , λ x₁ x₂ m≼cx
          → ϕ (x₁ , x→y x₁) (x₂ , x→y x₂)
              (×-codistance-min cx cy (under m) x₁ x₂ (x→y x₁) (x→y x₂)
                m≼cx (Cy px→y dx→y m ϕx→y x₁ x₂ m≼cx))
   x : X
   x = 𝓔⟨ cx , 𝓔Sx ⟩ px dx ϕx
   γ : Σ p → p (x , x→y x)
   γ ((x₀ , y₀) , px₀y₀)
    = S⟨ cx , 𝓔Sx ⟩ px dx ϕx
        (x₀ , S⟨ cy , 𝓔Sy ⟩ (px→y x₀) (dx→y x₀) (m , ϕx→y x₀)
        (y₀ , px₀y₀))

-}
