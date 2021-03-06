{-# OPTIONS --without-K --exact-split --safe #-}

open import Prelude
open import UF-FunExt
open import ESIntervalObject
open import NaturalsAddition renaming (_+_ to _+β_)
open import UF-Base

module IntervalObjectApproximation (fe : FunExt)
 (io : Interval-object fe π€') (hd : has-double fe π€' io) where

open basic-interval-object-development fe io hd hiding (β1 ; O ; +1)

data Vec (A : π₯ Μ) : β β π₯ Μ where
  [] : Vec A 0
  _β·_ : β {n} β A β Vec A n β Vec A (succ n)

first-_ : {A : π₯ Μ } (n : β) β (β β A) β Vec A n
(first- 0) a = []
(first- succ n) a = head a β· (first- n) (tail a)

append-one : {X : π₯ Μ } {n : β} β X β Vec X n β Vec X (succ n)
append-one {π₯} {X} {0} y [] = y β· []
append-one {π₯} {X} {succ n} y (x β· xs) = x β· append-one y xs

m : {n : β} β Vec π (succ n) β π
m {0} (x β· []) = x
m {succ n} (x β· xs) = x β m xs

n-approx : (x y : β β π) (n : β) β π€' Μ
n-approx x y n = Ξ£ (z , w) κ π Γ π
               , m (append-one z ((first- n) x))
               β‘ m (append-one w ((first- n) y))

approximation : π€' Μ
approximation = (x y : β β π) β Ξ  (n-approx x y) β M x β‘ M y

multi-canc : (w z : π) (y : β β π) (n : β)
           β m (append-one w ((first- n) y))
           β‘ m (append-one z ((first- n) y))
           β w β‘ z
multi-canc w .w y zero refl = refl
multi-canc w z y (succ n) e
 = multi-canc w z (y β succ) n (β-canc _ _ _ (β-comm β e β β-comm))

one-sided-approx : (x : π) (y : β β π)
                 β ((n : β) β Ξ£ w κ π , x β‘ m (append-one w ((first- n) y)))
                 β x β‘ M y
one-sided-approx x y f = M-propβ ws y Ξ³ where
  ws : β β π
  ws 0 = x
  ws (succ i) = prβ (f (succ i))
  Ξ³ : (i : β) β ws i β‘ (y i β ws (succ i))
  Ξ³ zero = prβ (f 1)
  Ξ³ (succ i) = multi-canc (ws (succ i)) (y (succ i) β ws (succ (succ i)))
               y (succ i) (prβ (f (succ i)) β»ΒΉ  β (prβ (f (succ (succ i)))
             β Ξ΄'' y (ws (succ (succ i))) i))
   where
    Ξ΄'' : (y : β β π) (z : π) (i : β)
        β m (append-one z ((first- (succ (succ i))) y))
        β‘ m (append-one (y (succ i) β z) ((first- (succ i)) y))
    Ξ΄'' y z zero = refl
    Ξ΄'' y z (succ i) = ap (y 0 β_) (Ξ΄'' (y β succ) z i)
    
_++_ : {n i : β} {X : π€ Μ } β Vec X n β Vec X i β Vec X (n +β i)
_++_ {_} {zero} {zero} {X} [] vβ = vβ
_++_ {_} {zero} {succ i} {X} [] vβ
 = transport (Vec X) (ap succ (zero-left-neutral i β»ΒΉ)) vβ
_++_ {_} {succ n} {zero} {X} vβ [] = vβ
_++_ {_} {succ n} {succ i} {X} (v β· vβ) vβ
 = transport (Vec X) (ap succ (Ξ΄ n i)) (v β· (vβ ++ vβ))
 where
  Ξ΄ : β n i β succ (n +β i) β‘ succ n +β i
  Ξ΄ n zero = refl
  Ξ΄ n (succ i) = ap succ (Ξ΄ n i)

_++'_ : {n : β} {X : π€ Μ } β Vec X n β (β β X) β (β β X)
[] ++' y = y
((x β· _) ++' _) zero = x
((_ β· vβ) ++' y) (succ n) = (vβ ++' y) n

five : (n : β) (a b c : β β π) (e : π)
     β m (append-one e ((first- succ n) a))
       β M ((first- n) b ++' Ξ» i β (c (succ (i +β n))))
     β‘ M ((append-one (a n β e) ((first- n) Ξ» i β a i β b i))
         ++' (Ξ» i β c (succ (i +β n))))
five zero a b c e = M-propβ _ β»ΒΉ
five (succ n) a b c e
 = ap ((a 0 β (a 1 β m (append-one e ((first- n) (a β succ β succ))))) β_)
     (M-propβ ((first- succ n) b ++' (Ξ» i β c (succ (i +β succ n)))))
     β β-tran β ap ((a 0 β b 0) β_) (five n (tail a) (tail b) (tail c) e)
     β M-propβ (append-one (a (succ n) β e)
         ((first- succ n) (Ξ» i β a i β b i))
         ++' (Ξ» i β c (succ (i +β succ n)))) β»ΒΉ

equals : (x : β β π) (n : β)
       β M x
       β‘ M (append-one (x n) ((first- n) x) ++' (Ξ» i β x (succ (i +β n))))
equals x zero = M-propβ x
              β M-propβ (append-one (x zero) ((first- zero) x) ++'
                          (Ξ» i β x (succ (i +β zero)))) β»ΒΉ
equals x (succ n) = M-propβ x
                  β ap (x 0 β_) (equals (tail x) n)
                  β M-propβ (append-one (x (succ n)) ((first- succ n) x) ++'
                              (Ξ» i β x (succ (i +β succ n)))) β»ΒΉ

next : (x y : β β π) (n : β)
     β M (Ξ» i β x i β y i)
     β‘ m (append-one (y n) ((first- succ n) x))
         β M (((first- n) y) ++' (Ξ» i β (x (succ (i +β n)))
                                      β (y (succ (i +β n)))))
next x y n = equals (Ξ» i β x i β y i) n
           β five n x y (Ξ» i β x i β y i) (y n) β»ΒΉ

equals2 : (x y : β β π) (w : π) (n : β)
        β (append-one w ((first- n) x)) ++' y
        β‘ ((first- n) x) ++' (w βΆβΆ y)
equals2 x y w zero = dfunext (fe π€β π€') (induction refl Ξ» _ _ β refl)
equals2 x y w (succ n) = dfunext (fe π€β π€') (induction refl
                           (Ξ» k _ β happly (equals2 (tail x) y w n) k))

tail-_ : {X : π€ Μ } β β β (β β X) β (β β X)
(tail- 0) Ξ± = Ξ±
(tail- succ n) Ξ± = tail ((tail- n) Ξ±)

Mβm : (Ξ± : β β π) (n : β)
    β M Ξ± β‘ m (append-one (M ((tail- n) Ξ±)) ((first- n) Ξ±))
Mβm Ξ± zero = refl
Mβm Ξ± (succ n) = M-propβ Ξ±
               β ap (Ξ± 0 β_)
               (transport
                    (Ξ» - β M (tail Ξ±)
                         β‘ m (append-one (M -) ((first- n) (tail Ξ±))))
                    (Ξ³ Ξ± n) (Mβm (tail Ξ±) n))
  where
    Ξ³ : (Ξ± : β β π) (n : β) β ((tail- n) (tail Ξ±)) β‘ ((tail- succ n) Ξ±)
    Ξ³ Ξ± 0 = refl
    Ξ³ Ξ± (succ n) = ap tail (Ξ³ Ξ± n)

tl : {X : π€ Μ} {m : β} β Vec X (succ m) β Vec X m
tl (_ β· xs) = xs

tail-first' : {X : π€ Μ } {m : β}
            β (a : Vec X (succ m)) (Ξ² : β β X) (n : β)
            β (tail- succ n) (a ++' Ξ²) β‘ (tail- n) (tl a ++' Ξ²)
tail-first' {X} {m} (_ β· xs) Ξ² 0 = refl
tail-first' {X} {m} (_ β· xs) Ξ² (succ n)
 = ap tail (tail-first' {X} {m} (_ β· xs) Ξ² n)

tail-first : {X : π€ Μ }
           β (Ξ± Ξ² : β β X) (n : β)
           β (tail- n) (((first- n) Ξ±) ++' Ξ²) β‘ Ξ²
tail-first Ξ± Ξ² zero = refl
tail-first Ξ± Ξ² (succ n)
 = tail-first' ((first- (succ n)) Ξ±) Ξ² n β tail-first (tail Ξ±) Ξ² n

first-first : {X : π€ Μ }
            β (Ξ± Ξ² : β β X) (n : β)
            β ((first- n) ((first- n) Ξ± ++' Ξ²)) β‘ (first- n) Ξ±
first-first Ξ± Ξ² 0 = refl
first-first Ξ± Ξ² (succ n) = ap (Ξ± 0 β·_) (first-first (tail Ξ±) Ξ² n)

approx-holds : approximation
approx-holds x y f = β-canc (M x) (M y) (M (tail z)) seven
 where
  z w : β β π
  z n = prβ (prβ (f n))
  w n = prβ (prβ (f n))
  w'' : (n : β) β (β β π)
  w'' n = (y n β prβ (prβ (f (succ n))))
       βΆβΆ (Ξ» i β x (succ (i +β n)) β prβ (prβ (f (succ (succ (i +β n))))))
  six : (n : β) β m (append-one (z n) ((first- n) x))
                β‘ m (append-one (w n) ((first- n) y))
  six n = prβ (f n)
  Ξ³' : (n : β) β Ξ£ w* κ π , M (Ξ» i β x i β (tail z) i)
     β‘ m (append-one w* ((first- n) (Ξ» i β y i β (tail z) i)))
  Ξ³' n = M (w'' n)
       , (next x (tail z) n
       β ap (_β M ((first- n) (tail z) ++' (Ξ» i β x (succ (i +β n))
                                                β tail z (succ (i +β n)))))
            (six (succ n))
       β five n y (tail z) (Ξ» i β x i β (tail z) i) (w (succ n))
       β ap M (equals2 (Ξ» i β y i β (tail z) i) ((Ξ» i β x (succ (i +β n))
                                                β (tail z) (succ (i +β n))))
            (w'' n 0) n)
       β Mβm (((first- n) (Ξ» i β y i β (tail z) i) ++' (w'' n))) n
       β (ap (Ξ» - β m (append-one (M -)
           ((first- n) ((first- n) (Ξ» i β y i β (tail z) i) ++' (w'' n)))))
             (tail-first (Ξ» i β y i β (tail z) i) (w'' n) n)
        β ap (Ξ» - β m (append-one (M (w'' n)) -))
           (first-first (Ξ» i β y i β (tail z) i) (w'' n) n)))
  seven : M x β M (z β succ) β‘ M y β M (z β succ)
  seven = M-hom x (z β succ)
        β one-sided-approx
            (M (Ξ» i β x i β prβ (prβ (f (succ i)))))
            (Ξ» i β y i β z (succ i))
            Ξ³'
        β M-hom y (z β succ) β»ΒΉ

n-approx' : (β β π) β (β β π) β β β π€' Μ
n-approx' x y n = Ξ£ (z , w) κ π Γ π
                , m (append-one z ((first- (succ n)) x))
                β‘ m (append-one w ((first- (succ n)) y))

n-approx'βn-approx : (x y : β β π) β Ξ  (n-approx' x y) β Ξ  (n-approx x y)
n-approx'βn-approx x y f zero = (u , u) , refl
n-approx'βn-approx x y f (succ n) = f n

fg-n-approx' : {X : π₯ Μ } β (f g : X β β β π) β β β π€' β π₯ Μ
fg-n-approx' f g n
 = (β x β n-approx' (f x) (g x) n) 
 β (β x β n-approx' (f x) (g x) (succ n)) 

fg-approx-holds : {X : π₯ Μ } (f g : X β β β π)
                β Ξ  (fg-n-approx' f g)
                β β x β M (f x) β‘ M (g x)
fg-approx-holds {_} {X} f g h x
 = approx-holds (f x) (g x) (n-approx'βn-approx (f x) (g x) (Ξ³ x))
 where
  Ξ³ : (x : X) β Ξ  (n-approx' (f x) (g x))
  Ξ³ x 0 = (g x 0 , f x 0) , β-comm
  Ξ³ x (succ n) = h n (Ξ» y β Ξ³ y n) x
