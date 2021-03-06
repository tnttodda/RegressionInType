{-# OPTIONS --without-K --exact-split --safe #-}

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

searchable : (X : π€ Μ ) β π€Ο 
searchable {π€} X 
 = {π₯ : Universe}
 β (p : X β π₯ Μ ) β detachable p
 β Ξ£ xβ κ X , (Ξ£ p β p xβ)

c-searchable : {X : π€ Μ } β (X β X β ββ) β π€Ο 
c-searchable {π€} {X} c
 = {π₯ : Universe} (p : X β π₯ Μ ) β detachable p β continuous c p
 β Ξ£ xβ κ X , (Ξ£ p β p xβ)

searchableβc-searchable : {X : π€ Μ } β (cx : X β X β ββ)
                        β searchable X β c-searchable cx
searchableβc-searchable {π€} {π₯} cx πSx p d _ = πSx p d

πβ¨_,_β© : {X : π€ Μ }
       β (c : X β X β ββ) (πS : c-searchable c)
       β (p : X β π₯ Μ ) β detachable p β continuous c p β X
Sβ¨_,_β© : {X : π€ Μ }
       β (c : X β X β ββ) (πS : c-searchable c)
       β (p : X β π₯ Μ ) (d : detachable p) (Ο : continuous c p)
       β Ξ£ p β p (πβ¨ c , πS β© p d Ο)

πβ¨ _ , πS β© p d Ο = prβ (πS p d Ο)
Sβ¨ _ , πS β© p d Ο = prβ (πS p d Ο)

πS-dec : {X : π€ Μ } (c : X β X β ββ)
      β (πS : c-searchable c)
      β (p : X β π₯ Μ ) β detachable p β continuous c p
      β Ξ£ p + ((x : X) β Β¬ p x)
πS-dec {π€} {π₯} {X} c πS p d Ο
 = Cases (d xβ)
     (Ξ»  pxβ β inl (xβ , pxβ)) 
     (Ξ» Β¬pxβ β inr Ξ» x px β Β¬pxβ (Ξ³β (x , px)))
 where
  xβ : X
  xβ = prβ (πS p d Ο)
  Ξ³β : Ξ£ p β p xβ
  Ξ³β = prβ (πS p d Ο)

βΆβΆ-indistinguishable : {X : π€ Μ } (dβ‘ : is-discrete X)
                     β (Ξ± : β β X) (m : ββ)
                     β m βΌ (codistance X dβ‘) Ξ± (head Ξ± βΆβΆ tail Ξ±)
βΆβΆ-indistinguishable {π€} {X} dβ‘ Ξ± m n p
  = codistance-conceptuallyβ X dβ‘
      Ξ± (head Ξ± βΆβΆ tail Ξ±)
      n (Ξ» k _ β head-tail-sim Ξ± k)

increase-distance : {X : π€ Μ } (d : is-discrete X)
                  β let c = codistance X d in
                    (xs ys : β β X) (m : β) β under m βΌ c xs ys
                  β (x : X) β Succ (under m) βΌ c (x βΆβΆ xs) (x βΆβΆ ys)
increase-distance {π€} {X} d xs ys m mβΌcxsys x n n<sm
 = codistance-conceptuallyβ X d (x βΆβΆ xs) (x βΆβΆ ys) n (Ξ³ n n<sm)
 where
   Ξ³ : (n : β) β n β Succ (under m)
     β (k : β) β k β€ n β (x βΆβΆ xs) k β‘ (x βΆβΆ ys) k
   Ξ³ n x zero kβ€n = refl
   Ξ³ (succ n) x (succ k) kβ€n
     = codistance-conceptuallyβ X d xs ys n (mβΌcxsys n x) k kβ€n

β-c-searchable : {X : π€ Μ } (dβ‘ : is-discrete X)
              β searchable X
              β c-searchable (codistance X dβ‘)
β-c-searchable {π€} {X} dβ‘ πSx = Ξ» p d (m , Ο) β Ξ· m p d Ο where
  Xα΄Ί = β β X
  cixs = codistance X dβ‘
  Ξ· : (m : β) β (p : Xα΄Ί β π₯ Μ ) β detachable p β uc-mod-of cixs p m
    β Ξ£ xsβ κ Xα΄Ί , (Ξ£ p β p xsβ)
  Ξ· 0 p d Ο = (Ξ» _ β prβ (πSx {π€} (Ξ» _ β π) (Ξ» _ β inl *)))
            , (Ξ» (xsβ , pxsβ)
            β Ο xsβ (Ξ» _ β prβ (πSx (Ξ» _ β π) (Ξ» _ β inl *))) (Ξ» _ ()) pxsβ)
  Ξ· (succ m) p d Ο = (x βΆβΆ xβxs x) , Ξ³
   where
     pxβxs = Ξ» x xs β p (x βΆβΆ xs)
     dxβxs = Ξ» x xs β d (x βΆβΆ xs)
     Οxβxs : (x : X) β uc-mod-of (codistance X dβ‘) (pxβxs x) m
     Οxβxs x xsβ xsβ mβΌcxs
      = Ο (x βΆβΆ xsβ) (x βΆβΆ xsβ) (increase-distance dβ‘ xsβ xsβ m mβΌcxs x)
     xβxs : X β (β β X)
     xβxs x = prβ (Ξ· m (pxβxs x) (dxβxs x) (Οxβxs x))
     px = Ξ» x β p (x βΆβΆ xβxs x)
     dx = Ξ» x β d (x βΆβΆ xβxs x)
     x : X
     x = prβ (πSx px dx)
     Ξ³ : Ξ£ p β p (x βΆβΆ xβxs x)
     Ξ³ (xsβ , pxsβ)
      = prβ (πSx px dx)
          (head xsβ , prβ (Ξ· m (pxβxs (head xsβ))
                               (dxβxs (head xsβ)) (Οxβxs (head xsβ)))
          (tail xsβ , Ο xsβ (head xsβ βΆβΆ tail xsβ)
          (βΆβΆ-indistinguishable dβ‘ xsβ (under (succ m))) pxsβ))

continuous-c-searcher : {X : π€ Μ } {Y : π₯ Μ }
                      β (cy : Y β Y β ββ)
                      β (cx : X β X β ββ)
                      β c-searchable cy β π€Ο
continuous-c-searcher {π€} {π₯} {X} {Y} cy cx πSy
 = {π¦ : Universe}
 β (p : X β Y β π¦ Μ )
 β (d : (x : X) β detachable (p x))
 β (m : β) (Ο : (x : X) β uc-mod-of cy (p x) m)
 β uc-mod-ofΒ² cx cy (Ξ» x β πβ¨ cy , πSy β© (p x) (d x) (m , Ο x)) m m

Γ-c-searchable : {X : π€ Μ } {Y : π₯ Μ }
              β (cx : X β X β ββ) β (cy : Y β Y β ββ)
              β c-searchable cx
              β (πSy : c-searchable cy)
              β ((x : X) β Ξ  (_β cx x x))
              β continuous-c-searcher cy cx πSy 
              β c-searchable (Γ-codistance cx cy)
Γ-c-searchable {π€} {π₯} {X} {Y} cx cy πSx πSy f Cy p d (m , Ο)
 = (x , xβy x) , Ξ³
  where
   pxβy = Ξ» x y β p (x , y)
   dxβy = Ξ» x y β d (x , y)
   Οxβy : (x : X) β uc-mod-of cy (pxβy x) m
   Οxβy x yβ yβ mβΌcy
    = Ο (x , yβ) (x , yβ)
        (Γ-codistance-min cx cy (under m) x x yβ yβ (Ξ» n _ β f x n) mβΌcy)
   xβy : X β Y
   xβy x = πβ¨ cy , πSy β© (pxβy x) (dxβy x) (m , Οxβy x)
   px = Ξ» x β p (x , xβy x)
   dx = Ξ» x β d (x , xβy x)
   Οx : continuous cx px
   Οx = m , Ξ» xβ xβ mβΌcx
          β Ο (xβ , xβy xβ) (xβ , xβy xβ)
              (Γ-codistance-min cx cy (under m) xβ xβ (xβy xβ) (xβy xβ)
                mβΌcx (Cy pxβy dxβy m Οxβy xβ xβ mβΌcx))
   x : X
   x = πβ¨ cx , πSx β© px dx Οx
   Ξ³ : Ξ£ p β p (x , xβy x)
   Ξ³ ((xβ , yβ) , pxβyβ)
    = Sβ¨ cx , πSx β© px dx Οx
        (xβ , Sβ¨ cy , πSy β© (pxβy xβ) (dxβy xβ) (m , Οxβy xβ)
        (yβ , pxβyβ))
