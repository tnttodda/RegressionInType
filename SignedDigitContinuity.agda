{-# OPTIONS --without-K --exact-split --safe #-}

open import UF-FunExt 
open import Prelude
open import NaturalsOrder
open import SignedDigit
open import DiscreteAndSeparated
open import GenericConvergentSequence hiding (max)

module SignedDigitContinuity (fe : FunExt) where

open import Codistances fe
open import Codistance fe
open import SearchableTypes fe
open sequences

_β*_ : {X : π€ Μ } {d : β}
     β ((β β X) ^β¨succ d β©) β ((β β X) ^β¨succ d β©)
     β (β ^β¨succ d β©) β π€ Μ
_β*_ {π€} {X} {zero} = _β_
_β*_ {π€} {X} {succ d} (Ξ± , Ξ±s) (Ξ² , Ξ²s) (n , ns) = (Ξ± β Ξ²) n Γ (Ξ±s β* Ξ²s) ns

_β**_ : {X : π€ Μ } β (β β (β β X)) β (β β (β β X)) β β β β β π€ Μ
_β**_ {π€} {X} Ξ±s Ξ²s m n = (k : β) β k < n β (Ξ±s k β Ξ²s k) m

β-uc-mod-ofΒ² : {X : π€ Μ } {Y : π₯ Μ } {d e : β}
             β ((β β X) ^β¨succ d β© β (β β Y) ^β¨succ e β©)
             β β ^β¨succ e β© β β ^β¨succ d β© β π€ β π₯ Μ
β-uc-mod-ofΒ² f Ξ΅ Ξ΄ = β Ξ± Ξ² β (Ξ± β* Ξ²) Ξ΄ β (f Ξ± β* f Ξ²) Ξ΅

β-continuousΒ² : {X : π€ Μ } {Y : π₯ Μ } {d e : β}
              β ((β β X) ^β¨succ d β© β (β β Y) ^β¨succ e β© ) β π€ β π₯ Μ
β-continuousΒ² f = β Ξ΅ β Ξ£ (β-uc-mod-ofΒ² f Ξ΅)

β-uc-mod-of : {X : π€ Μ } {d : β}
            β ((β β X) ^β¨succ d β© β π₯ Μ )
            β β ^β¨succ d β© β π€ β π₯ Μ
β-uc-mod-of p Ξ΄ = β Ξ± Ξ² β (Ξ± β* Ξ²) Ξ΄ β p Ξ± β p Ξ²

β-continuous : {X : π€ Μ } {d : β}
             β ((β β X) ^β¨succ d β© β π₯ Μ ) β π€ β π₯ Μ
β-continuous p = Ξ£ (β-uc-mod-of p)

β**-uc-mod-ofΒ² : {X : π€ Μ } {Y : π₯ Μ } {d : β}
              β ((β β (β β X)) β (β β Y) ^β¨succ d β©)
              β β ^β¨succ d β© β β β β β π€ β π₯ Μ
β**-uc-mod-ofΒ² f Ξ΅ Ξ΄β Ξ΄β = β Ξ±s Ξ²s β (Ξ±s β** Ξ²s) Ξ΄β Ξ΄β β (f Ξ±s β* f Ξ²s) Ξ΅

β**-continuousΒ² : {X : π€ Μ } {Y : π₯ Μ } {d : β}
               β ((β β (β β X)) β (β β Y) ^β¨succ d β©) β π€ β π₯ Μ 
β**-continuousΒ² f = β Ξ΅ β Ξ£ (Ξ΄s , Ξ΄) κ (β Γ β) , (β**-uc-mod-ofΒ² f Ξ΅ Ξ΄s Ξ΄)

vec-repeat : {X : π€ Μ } {n : β} β X β X ^β¨succ n β©
vec-repeat {π€} {X} {0} x = x
vec-repeat {π€} {X} {succ n} x = x , vec-repeat x

vec-max : {n : β} β β ^β¨succ n β© β β
vec-max {0} x = x
vec-max {succ n} (x , xs) = max x (vec-max xs)

maxβ : (k n m : β) β k β under n β k β under (max n m)
maxβ k (succ n) zero kβn = kβn
maxβ zero (succ n) (succ m) kβn = refl
maxβ (succ k) (succ n) (succ m) kβn = maxβ k n m kβn

maxβΌ : (n m : β) (v : ββ)
     β under (max n m) βΌ v
     β under n βΌ v
     Γ under m βΌ v
maxβΌ n m v maxnmβΌv
 = (Ξ» k p β maxnmβΌv k (maxβ k n m p))
 , (Ξ» k q β maxnmβΌv k
     (transport (Ξ» - β k β under -)
       (max-comm m n) (maxβ k m n q)))

β*ββΌ : {X : π€ Μ } (dΛ£ : is-discrete X)
     β (n : β) (x y : (β β X) ^β¨succ n β©)
     β (Ξ΅ : β) β (x β* y) (vec-repeat Ξ΅)
     β under Ξ΅ βΌ ΓβΏ-codistance (codistance X dΛ£) n x y
β*ββΌ dΛ£ 0 = βββΌ dΛ£
β*ββΌ {π€} {X} dΛ£ (succ n) (x , xs) (y , ys) Ξ΅ (xβy , xsβys)
 = Γ-codistance-min
     (codistance X dΛ£)
     (ΓβΏ-codistance (codistance X dΛ£) n)
     (under Ξ΅) x y xs ys
     (βββΌ dΛ£ x y Ξ΅ xβy)
     (β*ββΌ dΛ£ n xs ys Ξ΅ xsβys)

βΌββ* : {X : π€ Μ } (dΛ£ : is-discrete X)
     β (n : β) (x y : (β β X) ^β¨succ n β©)
     β (Ξ΅ : β)
     β under Ξ΅ βΌ ΓβΏ-codistance
                   (codistance X dΛ£) n x y
     β (x β* y) (vec-repeat Ξ΅)
βΌββ* dΛ£ 0 = βΌββ dΛ£
βΌββ* {π€} {X} dΛ£ (succ n) (x , xs) (y , ys) Ξ΅ Ξ΅βΌcxy
 = βΌββ dΛ£ x y Ξ΅ (prβ Ξ³)
 , βΌββ* dΛ£ n xs ys Ξ΅ (prβ Ξ³)
 where
   Ξ³ = Γ-codistance-min'
         (codistance X dΛ£)
         (ΓβΏ-codistance (codistance X dΛ£) n)
         (under Ξ΅) x y xs ys
         Ξ΅βΌcxy

βΌββ*' : {X : π€ Μ } (dΛ£ : is-discrete X)
      β (d n : β) (x y : (β β X) ^β¨succ n β©)
      β (Ξ΅ : β) (f : β ^β¨succ d β© β β ^β¨succ n β©)
      β under (vec-max (f (vec-repeat Ξ΅)))
                βΌ ΓβΏ-codistance
                    (codistance X dΛ£) n x y
      β (x β* y) (f (vec-repeat Ξ΅))
βΌββ*' dΛ£ d 0 x y Ξ΅ f = βΌββ dΛ£ x y (f (vec-repeat Ξ΅))
βΌββ*' {π€} {X} dΛ£ d (succ n) (x , xs) (y , ys) Ξ΅ f Ξ΄βΌcxy
 = βΌββ dΛ£ x y (prβ (f (vec-repeat Ξ΅)))
     (prβ (maxβΌ Ξ΄β Ξ΄β (codistance X dΛ£ x y) (prβ Ξ³)))
 , βΌββ*' dΛ£ d n xs ys Ξ΅ (prβ β f)
     (prβ (maxβΌ Ξ΄β Ξ΄β (ΓβΏ-codistance (codistance X dΛ£) n xs ys) (prβ Ξ³)))
 where
   Ξ΄β = prβ (f (vec-repeat Ξ΅))
   Ξ΄β = vec-max (prβ (f (vec-repeat Ξ΅)))
   Ξ΄ = max Ξ΄β Ξ΄β
   Ξ³ = Γ-codistance-min'
         (codistance X dΛ£)
         (ΓβΏ-codistance (codistance X dΛ£) n)
         (under Ξ΄) x y xs ys
         Ξ΄βΌcxy

β-continuousββΌ-continuous
              : {X : π€ Μ } {Y : π₯ Μ }
              β (dΛ£ : is-discrete X) (dΚΈ : is-discrete Y)
              β (d e : β)
              β (f : (β β X) ^β¨succ d β© β (β β Y) ^β¨succ e β©)
              β β-continuousΒ² f
              β continuousΒ²
                  (ΓβΏ-codistance (codistance X dΛ£) d)
                  (ΓβΏ-codistance (codistance Y dΚΈ) e)
                  f
β-continuousββΌ-continuous {π€} {X} dΛ£ dΚΈ d e f Ο Ξ΅
 = vec-max (prβ (Ο (vec-repeat Ξ΅)))
 , (Ξ» x y Ξ΄βΌcxy β β*ββΌ dΚΈ e (f x) (f y) Ξ΅
     (prβ (Ο (vec-repeat Ξ΅)) x y
       (βΌββ*' dΛ£ e d x y Ξ΅ (Ξ» x β prβ (Ο x)) Ξ΄βΌcxy)))

div2-continuous : β-continuousΒ² div2
div2-continuous zero = 0 , Ξ» Ξ± Ξ² _ k ()
div2-continuous (succ Ξ΅) = succ (succ Ξ΅) , Ξ³ Ξ΅ where
  Ξ³ : (Ξ΅ : β) β β-uc-mod-ofΒ² div2 (succ Ξ΅) (succ (succ Ξ΅))
  Ξ³ Ξ΅ Ξ± Ξ² Ξ±βΞ² 0 * = ap (Ξ» - β prβ (div2-aux - (Ξ± 1))) (Ξ±βΞ² 0 *)
                  β ap (Ξ» - β prβ (div2-aux (Ξ² 0) -)) (Ξ±βΞ² 1 *)
  Ξ³ (succ Ξ΅) Ξ± Ξ² Ξ±βΞ² (succ k) = Ξ³ Ξ΅ Ξ±' Ξ²' Ξ±βΞ²' k
   where
    Ξ±' = prβ (div2-aux (Ξ± 0) (Ξ± 1)) βΆβΆ (tail (tail Ξ±))
    Ξ²' = prβ (div2-aux (Ξ² 0) (Ξ² 1)) βΆβΆ (tail (tail Ξ²))
    Ξ±βΞ²' : (Ξ±' β Ξ²') (succ (succ Ξ΅))
    Ξ±βΞ²' 0 * = ap (Ξ» - β prβ (div2-aux - (Ξ± 1))) (Ξ±βΞ² 0 *)
             β ap (Ξ» - β prβ (div2-aux (Ξ² 0) -)) (Ξ±βΞ² 1 *)
    Ξ±βΞ²' (succ j) = Ξ±βΞ² (succ (succ j))

map-continuous : {X : π€ Μ } {Y : π₯ Μ } 
               β (f : X β Y) β β-continuousΒ² (map f)
map-continuous f Ξ΅ = Ξ΅ , Ξ» Ξ± Ξ² Ξ±βΞ² k k<Ξ΅ β ap f (Ξ±βΞ² k k<Ξ΅)

map2-continuous : {X : π€ Μ } {Y : π₯ Μ }
                β (f : X β X β Y) β β-continuousΒ² (uncurry (map2 f))
map2-continuous f Ξ΅ = (Ξ΅ , Ξ΅) , Ξ» Ξ± Ξ² Ξ±βΞ² k k<Ξ΅
                    β ap (Ξ» - β f - (prβ Ξ± k)) (prβ Ξ±βΞ² k k<Ξ΅)
                    β ap (f (prβ Ξ² k)) (prβ Ξ±βΞ² k k<Ξ΅)

continuouβ-β : {X : π€ Μ } {Y : π₯ Μ } {Z : π¦ Μ } {dβ dβ dβ : β}
             β (f : (β β Y) ^β¨succ dβ β© β (β β Z) ^β¨succ dβ β©)
             β (g : (β β X) ^β¨succ dβ β© β (β β Y) ^β¨succ dβ β©)
             β β-continuousΒ² f  β β-continuousΒ² g
             β β-continuousΒ² (f β g)
continuouβ-β f g Οf Οg Ξ΅
 = prβ (Οg (prβ (Οf Ξ΅)))
 , Ξ» Ξ± Ξ² Ξ±βΞ²
 β prβ (Οf Ξ΅) (g Ξ±) (g Ξ²)
    (prβ (Οg (prβ (Οf Ξ΅))) Ξ± Ξ² Ξ±βΞ²)

neg-continuous : β-continuousΒ² neg
neg-continuous = map-continuous compl

mid-continuous : β-continuousΒ² (uncurry mid)
mid-continuous = continuouβ-β div2 (uncurry add2)
                   div2-continuous (map2-continuous _+π_)

bigMid-continuous : β**-continuousΒ² bigMid'
bigMid-continuous Ξ΅ = Ξ΄s Ξ΅ , Ξ³ Ξ΅ where
  Ξ΄sβ : β β β
  Ξ΄sβ 0 = 0
  Ξ΄sβ (succ Ξ΅) = succ (succ (succ (Ξ΄sβ Ξ΅)))
  Ξ΄sβ : β β β
  Ξ΄sβ 0 = 0
  Ξ΄sβ (succ Ξ΅) = succ (succ Ξ΅)
  Ξ΄s : β β β Γ β
  Ξ΄s Ξ΅ = Ξ΄sβ Ξ΅ , Ξ΄sβ Ξ΅
  prβΞ΄s< : (n : β) β prβ (Ξ΄s n) < prβ (Ξ΄s (succ n))
  prβΞ΄s< zero = *
  prβΞ΄s< (succ n) = prβΞ΄s< n
  Ξ³ : (Ξ΅ : β) β β**-uc-mod-ofΒ² bigMid' Ξ΅ (prβ (Ξ΄s Ξ΅)) (prβ (Ξ΄s Ξ΅))
  Ξ³ (succ Ξ΅) Ξ±s Ξ²s Ξ±sβΞ²s 0 k<Ξ΅
    = ap (Ξ» - β (- +π -) +π (Ξ±s 0 1 +π Ξ±s 1 0)) (Ξ±sβΞ²s 0 * 0 *)
    β ap (Ξ» - β (Ξ²s 0 0 +π Ξ²s 0 0) +π (- +π Ξ±s 1 0)) (Ξ±sβΞ²s 0 * 1 *)
    β ap (Ξ» - β (Ξ²s 0 0 +π Ξ²s 0 0) +π (Ξ²s 0 1 +π -)) (Ξ±sβΞ²s 1 * 0 *)
  Ξ³ 1 Ξ±s Ξ²s Ξ±sβΞ²s (succ k) ()
  Ξ³ (succ (succ Ξ΅)) Ξ±s Ξ²s Ξ±sβΞ²s (succ k) xβ
   = Ξ³ (succ Ξ΅) Ξ±s' Ξ²s' Ξ±sβΞ²s' k xβ
   where
    Ξ±s' = mid (tail (tail (Ξ±s 0))) (tail (Ξ±s 1)) βΆβΆ tail (tail Ξ±s) 
    Ξ²s' = mid (tail (tail (Ξ²s 0))) (tail (Ξ²s 1)) βΆβΆ tail (tail Ξ²s)
    Ξ±sβΞ²s' : (Ξ±s' β** Ξ²s') (prβ (Ξ΄s (succ Ξ΅))) (prβ (Ξ΄s (succ Ξ΅)))
    Ξ±sβΞ²s' zero x i xβ
     = prβ (mid-continuous (prβ (Ξ΄s (succ Ξ΅))))
         (tail (tail (Ξ±s 0)) , tail (Ξ±s 1))
         (tail (tail (Ξ²s 0)) , tail (Ξ²s 1))
         ((Ξ» kβ xβ β Ξ±sβΞ²s 0 * (succ (succ kβ)) xβ) ,
          (Ξ» kβ xβ β Ξ±sβΞ²s 1 * (succ kβ) (<-trans (succ kβ) (succ (succ kβ)) (prβ (Ξ΄s (succ (succ Ξ΅)))) (<-succ kβ) xβ))) i xβ
    Ξ±sβΞ²s' (succ k) x i xβ = Ξ±sβΞ²s (succ (succ k)) x i
                               (<-trans i (prβ (Ξ΄s (succ Ξ΅))) (prβ (Ξ΄s (succ (succ Ξ΅)))) xβ (prβΞ΄s< (succ Ξ΅)))

div4-continuous : β-continuousΒ² div4
div4-continuous zero = 0 , Ξ» Ξ± Ξ² _ k ()
div4-continuous (succ Ξ΅) = succ (succ Ξ΅) , Ξ³ Ξ΅ where
  Ξ³ : (Ξ΅ : β) β β-uc-mod-ofΒ² div4 (succ Ξ΅) (succ (succ Ξ΅))
  Ξ³ Ξ΅ Ξ± Ξ² Ξ±βΞ² 0 * = ap (Ξ» - β prβ (div4-aux - (Ξ± 1))) (Ξ±βΞ² 0 *)
                  β ap (Ξ» - β prβ (div4-aux (Ξ² 0) -)) (Ξ±βΞ² 1 *)
  Ξ³ (succ Ξ΅) Ξ± Ξ² Ξ±βΞ² (succ k) = Ξ³ Ξ΅ Ξ±' Ξ²' Ξ±βΞ²' k
   where
    Ξ±' = prβ (div4-aux (Ξ± 0) (Ξ± 1)) βΆβΆ (tail (tail Ξ±))
    Ξ²' = prβ (div4-aux (Ξ² 0) (Ξ² 1)) βΆβΆ (tail (tail Ξ²))
    Ξ±βΞ²' : (Ξ±' β Ξ²') (succ (succ Ξ΅))
    Ξ±βΞ²' 0 * = ap (Ξ» - β prβ (div4-aux - (Ξ± 1))) (Ξ±βΞ² 0 *)
             β ap (Ξ» - β prβ (div4-aux (Ξ² 0) -)) (Ξ±βΞ² 1 *)
    Ξ±βΞ²' (succ j) = Ξ±βΞ² (succ (succ j))  

bigMid''-continuous : β**-continuousΒ² bigMid
bigMid''-continuous Ξ΅ = Ξ΄ , Ξ³ where
  Ξ΄ : β Γ β
  Ξ΄ = prβ (bigMid-continuous (prβ (div4-continuous Ξ΅)))
  Ξ³ : β**-uc-mod-ofΒ² bigMid Ξ΅ (prβ Ξ΄) (prβ Ξ΄)
  Ξ³ Ξ±s Ξ²s Ξ±sβΞ²s
   = prβ (div4-continuous Ξ΅)
       (bigMid' Ξ±s) (bigMid' Ξ²s)
       (prβ (bigMid-continuous (prβ (div4-continuous Ξ΅)))
         Ξ±s Ξ²s Ξ±sβΞ²s)

mul-continuous : β-continuousΒ² (uncurry mul)
mul-continuous Ξ΅ = Ξ΄ Ξ΅ , Ξ³ Ξ΅ where
  Ξ΄ : β β β Γ β
  Ξ΄ Ξ΅ = prβ (prβ (bigMid''-continuous Ξ΅))
      , prβ (prβ (bigMid''-continuous Ξ΅))
  Ξ³ : (Ξ΅ : β) β β-uc-mod-ofΒ² (uncurry mul) Ξ΅ (Ξ΄ Ξ΅)
  Ξ³ Ξ΅ (Ξ±β , Ξ±β) (Ξ²β , Ξ²β) (Ξ±βΞ²β , Ξ±βΞ²β)
   = prβ (bigMid''-continuous Ξ΅)
       (map2 digitMul Ξ±β (repeat Ξ±β))
       (map2 digitMul Ξ²β (repeat Ξ²β))
         (Ξ» n n<x k k<y
         β ap (_*π Ξ±β k) (Ξ±βΞ²β n n<x)
         β ap (Ξ²β n *π_) (Ξ±βΞ²β k k<y))

max-< : (n m k : β) β k < n + k < m β k < max n m
max-< zero (succ m) k (inr x) = x
max-< (succ n) zero k (inl x) = x
max-< (succ n) (succ m) 0 _ = *
max-< (succ n) (succ m) (succ k) = max-< n m k

<β-max : {P : β β π€ Μ } (n m : β) β <β P (max n m) β <β P n Γ <β P m
<β-max n m f = (Ξ» k k<n β f k (max-< n m k (inl k<n)))
             , (Ξ» k k<m β f k (max-< n m k (inr k<m)))

_**β¨succ_β© : πα΄Ί β β β πα΄Ί
Ξ± **β¨succ 0 β© = Ξ±
Ξ± **β¨succ succ n β© = mul Ξ± (Ξ± **β¨succ n β©)

pow-continuous : (n : β) β β-continuousΒ² _**β¨succ n β©
pow-continuous 0 = map-continuous id
pow-continuous (succ n) Ξ΅
 = max a b
 , Ξ» Ξ± Ξ² Ξ±βΞ² k k<Ξ΅
 β prβ (mul-continuous Ξ΅)
     (Ξ± , Ξ± **β¨succ n β©) (Ξ² , Ξ² **β¨succ n β©)
     (prβ (<β-max a b Ξ±βΞ²)
     , prβ (pow-continuous n (prβ (prβ (mul-continuous Ξ΅))))
         Ξ± Ξ² (prβ (<β-max a b Ξ±βΞ²))) k k<Ξ΅
 where
   a = prβ (prβ (mul-continuous Ξ΅))
   b = prβ (pow-continuous n (prβ (prβ (mul-continuous Ξ΅))))

cπα΄Ί : πα΄Ί β πα΄Ί β ββ
cπα΄Ί = codistance π π-is-discrete

cπα΄ΊΓπα΄Ί : (πα΄Ί Γ πα΄Ί) β (πα΄Ί Γ πα΄Ί) β ββ 
cπα΄ΊΓπα΄Ί = Γ-codistance cπα΄Ί cπα΄Ί

βββΌ-continuous-πα΄Ί = β-continuousββΌ-continuous π-is-discrete π-is-discrete

neg-continuousβΌ : continuousΒ² cπα΄Ί cπα΄Ί neg
neg-continuousβΌ = βββΌ-continuous-πα΄Ί 0 0 neg neg-continuous

mid-continuousβΌ : continuousΒ² cπα΄ΊΓπα΄Ί cπα΄Ί (uncurry mid)
mid-continuousβΌ = βββΌ-continuous-πα΄Ί 1 0 (uncurry mid) mid-continuous

mul-continuousβΌ : continuousΒ² cπα΄ΊΓπα΄Ί cπα΄Ί (uncurry mul)
mul-continuousβΌ = βββΌ-continuous-πα΄Ί 1 0 (uncurry mul) mul-continuous
