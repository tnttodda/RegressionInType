{-# OPTIONS --without-K --exact-split --safe #-}

module Prelude where

open import SpartanMLTT public hiding (_^_)
open import NaturalsOrder
open import Two-Properties

map : {X : π€ Μ } {Y : π₯ Μ }
    β (X β Y) β (β β X) β (β β Y)
map f Ξ± n = f (Ξ± n)

map2 : {X : π€ Μ } {Y : π₯ Μ } {Z : π¦ Μ }
     β (X β Y β Z) β (β β X) β (β β Y) β (β β Z)
map2 f Ξ± Ξ² n = f (Ξ± n) (Ξ² n)

_^β¨succ_β© : (X : π€ Μ ) β β β π€ Μ 
_^β¨succ_β© X 0 = X
_^β¨succ_β© X (succ n) = X Γ X ^β¨succ n β©

vec-map : {X : π€ Μ } {Y : π₯ Μ } {n : β}
        β (X β Y) β X ^β¨succ n β© β Y ^β¨succ n β©
vec-map {π€} {π₯} {X} {Y} {0} f v = f v
vec-map {π€} {π₯} {X} {Y} {succ n} f (v , vs) = f v , vec-map f vs

head : {X : π€ Μ } β (β β X) β X
head Ξ± = Ξ± 0

tail : {X : π€ Μ } β (β β X) β (β β X)
tail Ξ± = Ξ± β succ

_βΆβΆ_ : {X : π€ Μ } β X β (β β X) β (β β X)
(h βΆβΆ Ξ±) 0 = h
(h βΆβΆ Ξ±) (succ n) = Ξ± n

head-tail-sim : {X : π€ Μ } β (Ξ± : β β X) β Ξ± βΌ (head Ξ± βΆβΆ tail Ξ±)
head-tail-sim Ξ± 0 = refl
head-tail-sim Ξ± (succ _) = refl

<β : (β β π€ Μ ) β β β π€ Μ
<β P n = β k β k < n β P k

<β-succ : {P : β β π€ Μ } (n : β) β <β P n β P n β <β P (succ n)
<β-succ 0 f Pn 0 k<n = Pn
<β-succ {π€} {P} (succ n) f Pn k k<n
 = Cases (<-split k (succ n) k<n)
     (Ξ» k<sn β f k k<sn)
     (Ξ» t β transport P (t β»ΒΉ) Pn)

_β_ : {X : π€ Μ } β (β β X) β (β β X) β β β π€ Μ 
(Ξ± β Ξ²) = <β (Ξ» k β Ξ± k β‘ Ξ² k)

minπ-abcd : {a b c d : π} β a β‘ c β b β‘ d β minπ a b β‘ minπ c d
minπ-abcd {a} {b} {.a} {.b} refl refl = refl

Γ-β‘ : {X : π€ Μ } {Y : π₯ Μ } β {xβ xβ : X} {yβ yβ : Y}
    β xβ β‘ xβ β yβ β‘ yβ β (xβ , yβ) β‘ (xβ , yβ)
Γ-β‘ {π€} {X} {π₯} {Y} {xβ} {.xβ} {yβ} {.yβ} refl refl = refl
