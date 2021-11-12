{-# OPTIONS --without-K --exact-split --allow-unsolved-metas --experimental-lossy-unification #-}

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

continuous-c-searcher : {𝓤 𝓥 : Universe} {Y : 𝓤 ̇ }
                      → (cy : Y → Y → ℕ∞)
                      → c-searchable cy → Set (𝓤 ⁺ ⊔ 𝓥 ⁺)
continuous-c-searcher {𝓤} {𝓥} {Y} cy 𝓔Sy
 = {X : 𝓤 ̇ }
 → (cx : X → X → ℕ∞)
 → (p : X → Y → 𝓥 ̇ )
 → (d : (x : X) → detachable (p x))
 → (m : ℕ) (ϕ : (x : X) → uc-mod-of cy (p x) m)
 → uc-mod-of² cx cy (λ x → 𝓔⟨ cy , 𝓔Sy ⟩ (p x) (d x) (m , ϕ x)) m m

≼-pred : (a b : ℕ∞) → Succ a ≼ b → a ≼ b
≼-pred a b sa≼b n = pr₂ b n ∘ (sa≼b (succ n))

→→-c-searchable : {𝓥 : Universe} (T : ℕ → 𝓤 ̇ )
                → (cs : ((n : ℕ) → T n → T n → ℕ∞))
                → (es : ((n : ℕ) (x : T n) → Π (_⊏ cs n x x)))
                → (ss : (n : ℕ) → c-searchable {𝓤} {𝓥} (cs n))
                → (rs : (n : ℕ) → continuous-c-searcher {𝓤} {𝓥} (cs n) (ss n)) 
                → Σ (continuous-c-searcher {𝓤} {𝓥} (Π-codistance cs))
→→-c-searchable {𝓤} {𝓥} T cs es ss rs
 = (λ p d (m , ϕ) → η cs es ss rs m p d ϕ) , λ cx p d m ϕ → μ cs es ss rs m p d ϕ cx where
 
  η : {T : ℕ → 𝓤 ̇ }
    → (cs : Π n ꞉ ℕ , (T n → T n → ℕ∞))
    → (es : ((n : ℕ) (x : T n) → Π (_⊏ cs n x x)))
    → (ss : (n : ℕ) → c-searchable (cs n))
    → (rs : (n : ℕ) → continuous-c-searcher {𝓤} {𝓥} (cs n) (ss n)) 
    → (m : ℕ) → (p : Π T → 𝓥 ̇ ) → detachable p
    → uc-mod-of (Π-codistance cs) p m
    → Σ xs₀ ꞉ Π T , (Σ p → p xs₀)
    
  μ : {T : ℕ → 𝓤 ̇ } {X : 𝓤 ̇ }
    → (cs : Π n ꞉ ℕ , (T n → T n → ℕ∞))
    → (es : ((n : ℕ) (x : T n) → Π (_⊏ cs n x x)))
    → (ss : (n : ℕ) → c-searchable (cs n))
    → (rs : (n : ℕ) → continuous-c-searcher {𝓤} {𝓥} (cs n) (ss n)) 
    → (m : ℕ) → (p : X → Π T → 𝓥 ̇ ) → (d : ∀ x → detachable (p x))
    → (ϕ : ∀ x → uc-mod-of (Π-codistance cs) (p x) m)
    → (cx : X → X → ℕ∞)
    → uc-mod-of² cx (Π-codistance cs) (λ x → pr₁ (η cs es ss rs m (p x) (d x) (ϕ x))) m m
    
  𝓔HD : {T : ℕ → 𝓤 ̇ } → (cs : ((n : ℕ) → T n → T n → ℕ∞))
      → (es : ((n : ℕ) (x : T n) → Π (_⊏ cs n x x)))
      → (ss : (n : ℕ) → c-searchable (cs n))
      → (rs : (n : ℕ) → continuous-c-searcher {𝓤} {𝓥} (cs n) (ss n)) 
      → (p : Π T → 𝓥 ̇ ) (d : detachable p) (m : ℕ) (ϕ : uc-mod-of (Π-codistance cs) p (succ m))
      → T 0
      
  𝓔TL : {T : ℕ → 𝓤 ̇ } → (cs : ((n : ℕ) → T n → T n → ℕ∞))
      → (es : ((n : ℕ) (x : T n) → Π (_⊏ cs n x x)))
      → (ss : (n : ℕ) → c-searchable (cs n))
      → (rs : (n : ℕ) → continuous-c-searcher {𝓤} {𝓥} (cs n) (ss n)) 
      → (p : Π T → 𝓥 ̇ ) (d : detachable p) (m : ℕ) (ϕ : uc-mod-of (Π-codistance cs) p (succ m))
      → T 0 → Π (T ∘ succ)
      
  pH : {T : ℕ → 𝓤 ̇ } → (cs : ((n : ℕ) → T n → T n → ℕ∞))
     → (es : ((n : ℕ) (x : T n) → Π (_⊏ cs n x x)))
     → (ss : (n : ℕ) → c-searchable (cs n))
     → (rs : (n : ℕ) → continuous-c-searcher {𝓤} {𝓥} (cs n) (ss n)) 
     → (p : Π T → 𝓥 ̇ ) (d : detachable p) (m : ℕ) (ϕ : uc-mod-of (Π-codistance cs) p (succ m))
     → T 0 → 𝓥 ̇

  dH : {T : ℕ → 𝓤 ̇ } → (cs : ((n : ℕ) → T n → T n → ℕ∞))
     → (es : ((n : ℕ) (x : T n) → Π (_⊏ cs n x x)))
     → (ss : (n : ℕ) → c-searchable (cs n))
     → (rs : (n : ℕ) → continuous-c-searcher {𝓤} {𝓥} (cs n) (ss n)) 
     → (p : Π T → 𝓥 ̇ ) (d : detachable p) (m : ℕ) (ϕ : uc-mod-of (Π-codistance cs) p (succ m))
     → detachable (pH cs es ss rs p d m ϕ)

  ϕH : {T : ℕ → 𝓤 ̇ } → (cs : ((n : ℕ) → T n → T n → ℕ∞))
     → (es : ((n : ℕ) (x : T n) → Π (_⊏ cs n x x)))
     → (ss : (n : ℕ) → c-searchable (cs n))
     → (rs : (n : ℕ) → continuous-c-searcher {𝓤} {𝓥} (cs n) (ss n)) 
     → (p : Π T → 𝓥 ̇ ) (d : detachable p) (m : ℕ) (ϕ : uc-mod-of (Π-codistance cs) p (succ m))
     → uc-mod-of (cs 0) (pH cs es ss rs p d m ϕ) (succ m)

  pT : {T : ℕ → 𝓤 ̇ } → (cs : ((n : ℕ) → T n → T n → ℕ∞))
     → (es : ((n : ℕ) (x : T n) → Π (_⊏ cs n x x)))
     → (ss : (n : ℕ) → c-searchable (cs n))
     → (rs : (n : ℕ) → continuous-c-searcher {𝓤} {𝓥} (cs n) (ss n)) 
     → (p : Π T → 𝓥 ̇ ) (d : detachable p) (m : ℕ) (ϕ : uc-mod-of (Π-codistance cs) p (succ m))
     → T 0 → Π (T ∘ succ) → 𝓥 ̇

  dT : {T : ℕ → 𝓤 ̇ } → (cs : ((n : ℕ) → T n → T n → ℕ∞))
     → (es : ((n : ℕ) (x : T n) → Π (_⊏ cs n x x)))
     → (ss : (n : ℕ) → c-searchable (cs n))
     → (rs : (n : ℕ) → continuous-c-searcher {𝓤} {𝓥} (cs n) (ss n)) 
     → (p : Π T → 𝓥 ̇ ) (d : detachable p) (m : ℕ) (ϕ : uc-mod-of (Π-codistance cs) p (succ m))
     → (x : T 0) → detachable (pT cs es ss rs p d m ϕ x)

  ϕT : {T : ℕ → 𝓤 ̇ } → (cs : ((n : ℕ) → T n → T n → ℕ∞))
     → (es : ((n : ℕ) (x : T n) → Π (_⊏ cs n x x)))
     → (ss : (n : ℕ) → c-searchable (cs n))
     → (rs : (n : ℕ) → continuous-c-searcher {𝓤} {𝓥} (cs n) (ss n)) 
     → (p : Π T → 𝓥 ̇ ) (d : detachable p) (m : ℕ) (ϕ : uc-mod-of (Π-codistance cs) p (succ m))
     → (x : T 0)
     → uc-mod-of (Π-codistance (cs ∘ succ)) (pT cs es ss rs p d m ϕ x) m

  pH {T} cs es ss rs p d m ϕ x = p (x :: pr₁ (η (cs ∘ succ) (es ∘ succ) (λ n → ss (succ n)) (λ n → rs (succ n)) m
                                               (pT cs es ss rs p d m ϕ x)
                                               (dT cs es ss rs p d m ϕ x)
                                               (ϕT cs es ss rs p d m ϕ x)))
                                               
  dH cs es ss rs p d m ϕ x = d (x :: pr₁ (η (cs ∘ succ) (es ∘ succ) (λ n → ss (succ n)) (λ n → rs (succ n)) m
                                               (pT cs es ss rs p d m ϕ x)
                                               (dT cs es ss rs p d m ϕ x)
                                               (ϕT cs es ss rs p d m ϕ x)))

  ϕH {T} cs es ss rs p d m ϕ x y m≼cxy
   =  ϕ (x :: pr₁ (η (cs ∘ succ) (es ∘ succ) (λ n → ss (succ n)) (λ n → rs (succ n)) m
                                  (pT cs es ss rs p d m ϕ x)
                                  (dT cs es ss rs p d m ϕ x)
                                  (ϕT cs es ss rs p d m ϕ x)))
                      (y :: pr₁ (η (cs ∘ succ) (es ∘ succ) (λ n → ss (succ n)) (λ n → rs (succ n)) m
                                  (pT cs es ss rs p d m ϕ y)
                                  (dT cs es ss rs p d m ϕ y)
                                  (ϕT cs es ss rs p d m ϕ y)))
                      (Π-codistance-Build cs x y
                           (pr₁ (η (cs ∘ succ) (es ∘ succ) (λ n → ss (succ n)) (λ n → rs (succ n)) m
                                  (pT cs es ss rs p d m ϕ x)
                                  (dT cs es ss rs p d m ϕ x)
                                  (ϕT cs es ss rs p d m ϕ x)))
                           (pr₁ (η (cs ∘ succ) (es ∘ succ) (λ n → ss (succ n)) (λ n → rs (succ n)) m
                                  (pT cs es ss rs p d m ϕ y)
                                  (dT cs es ss rs p d m ϕ y)
                                  (ϕT cs es ss rs p d m ϕ y)))
                      m m≼cxy
                      (μ (cs ∘ succ) (es ∘ succ) (λ n → ss (succ n)) (λ n → rs (succ n)) m
                        (pT cs es ss rs p d m ϕ)
                        (dT cs es ss rs p d m ϕ)
                        (ϕT cs es ss rs p d m ϕ)
                        (cs 0) x y (≼-pred (under m) (cs 0 x y) m≼cxy)))
                        
  pT cs es ss rs p d m ϕ x xs = p (x :: xs)
  dT cs es ss rs p d m ϕ x xs = d (x :: xs)
  ϕT cs es ss rs p d m ϕ x xs₁ xs₂ m≼cxs = ϕ (x :: xs₁) (x :: xs₂) (Π-codistance-Succ cs (es 0) x xs₁ xs₂ m m≼cxs)

  𝓔HD cs es ss rs p d m ϕ = pr₁ (ss 0 (pH cs es ss rs p d m ϕ) (dH cs es ss rs p d m ϕ) (succ m , ϕH cs es ss rs p d m ϕ))

  𝓔TL {T} cs es ss rs p d m ϕ x = pr₁ (η {T ∘ succ} (cs ∘ succ) (es ∘ succ) (λ n → ss (succ n)) (λ n → rs (succ n)) m
                                      (pT cs es ss rs p d m ϕ x)
                                      (dT cs es ss rs p d m ϕ x)
                                      (ϕT cs es ss rs p d m ϕ x))
                                      
  η cs es 𝓔S rs 0        p d ϕ
   = (λ n → pr₁ (𝓔S n trivial-p trivial-d (trivial-ϕ (cs n))))
   , λ (α , pα) → ϕ α (λ n → pr₁ (𝓔S n trivial-p trivial-d (trivial-ϕ (cs n))))
       (Zero-minimal (Π-codistance cs α (λ n → pr₁ (𝓔S n trivial-p trivial-d (trivial-ϕ (cs n)))))) pα

  η cs es 𝓔S rs (succ m) p d ϕ
   = 𝓔HD cs es 𝓔S rs p d m ϕ
   :: pr₁ (η (cs ∘ succ) (es ∘ succ) (λ n → 𝓔S (succ n)) (λ n → rs (succ n))
           m
           (pT cs es 𝓔S rs p d m ϕ (𝓔HD cs es 𝓔S rs p d m ϕ))
           (dT cs es 𝓔S rs p d m ϕ (𝓔HD cs es 𝓔S rs p d m ϕ))
           (ϕT cs es 𝓔S rs p d m ϕ (𝓔HD cs es 𝓔S rs p d m ϕ)))
   , λ (α , pα)
   → pr₂ (𝓔S 0 (pH cs es 𝓔S rs p d m ϕ)
               (dH cs es 𝓔S rs p d m ϕ)
               (succ m , ϕH cs es 𝓔S rs p d m ϕ))
     (α 0 , pr₂ (η (cs ∘ succ) (es ∘ succ) (λ n → 𝓔S (succ n)) (λ n → rs (succ n))
           m
           (pT cs es 𝓔S rs p d m ϕ (α 0))
           (dT cs es 𝓔S rs p d m ϕ (α 0))
           (ϕT cs es 𝓔S rs p d m ϕ (α 0)))
     (α ∘ succ , ϕ α (α 0 :: (λ n → α (succ n))) (Π-equivalent cs es α (succ m)) pα))

  μ {T} {X} cs es 𝓔S rs (succ m) p d ϕ cx x y m≼cxy
   = Π-codistance-Build cs (𝓔→ x) (𝓔→ y) (𝓔→→ x) (𝓔→→ y) m
      (rs 0 cx (λ a h → pH cs es 𝓔S rs (p a) (d a) m (ϕ a) h)
               (λ a h → dH cs es 𝓔S rs (p a) (d a) m (ϕ a) h)
               (succ m)
               (λ a  → ϕH cs es 𝓔S rs (p a) (d a) m (ϕ a))
        x y m≼cxy)
      (μ (cs ∘ succ) (es ∘ succ) (λ n → 𝓔S (succ n)) (λ n → rs (succ n)) m
        (λ a → pT cs es 𝓔S rs (p a) (d a) m (ϕ a) (𝓔→ a))
        (λ a → dT cs es 𝓔S rs (p a) (d a) m (ϕ a) (𝓔→ a)) 
        (λ a → ϕT cs es 𝓔S rs (p a) (d a) m (ϕ a) (𝓔→ a))
        cx x y (≼-pred (under m) (cx x y) m≼cxy)) where
    𝓔→ : (a : X) → T 0
    𝓔→ a = 𝓔HD cs es 𝓔S rs (p a) (d a) m (ϕ a)
    𝓔→→ : (a : X) → Π (T ∘ succ)
    𝓔→→ a = 𝓔TL cs es 𝓔S rs (p a) (d a) m (ϕ a) (𝓔→ a)
    
×-c-searchable : {𝓦 : Universe} {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
              → (cx : X → X → ℕ∞) → (cy : Y → Y → ℕ∞)
              → c-searchable {𝓤} {𝓦} cx
              → (𝓔Sy : c-searchable {𝓥} {𝓦} cy)
              → ((x : X) → Π (_⊏ cx x x))
              → continuous-c-searcher cy 𝓔Sy 
              → c-searchable {𝓤 ⊔ 𝓥} {𝓦} (×-codistance cx cy)
×-c-searchable {𝓤} {𝓥} {𝓦} {X} {Y} cx cy 𝓔Sx 𝓔Sy f Cy p d (m , ϕ)
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
                m≼cx {!!}) -- (Cy px→y dx→y m ϕx→y x₁ x₂ m≼cx))
   x : X
   x = 𝓔⟨ cx , 𝓔Sx ⟩ px dx ϕx
   γ : Σ p → p (x , x→y x)
   γ ((x₀ , y₀) , px₀y₀)
    = S⟨ cx , 𝓔Sx ⟩ px dx ϕx
        (x₀ , S⟨ cy , 𝓔Sy ⟩ (px→y x₀) (dx→y x₀) (m , ϕx→y x₀)
        (y₀ , px₀y₀))
