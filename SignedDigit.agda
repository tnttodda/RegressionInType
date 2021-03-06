{-# OPTIONS --without-K --exact-split --safe #-}

module SignedDigit where

open import Prelude
open import DiscreteAndSeparated

data π : π€β Μ where
  β1 O +1 : π

π-is-discrete : is-discrete π
π-is-discrete β1 β1 = inl refl
π-is-discrete β1  O = inr (Ξ» ())
π-is-discrete β1 +1 = inr (Ξ» ())
π-is-discrete  O β1 = inr (Ξ» ())
π-is-discrete  O  O = inl refl
π-is-discrete  O +1 = inr (Ξ» ())
π-is-discrete +1 β1 = inr (Ξ» ())
π-is-discrete +1  O = inr (Ξ» ())
π-is-discrete +1 +1 = inl refl

πα΄Ί = β β π

compl : π β π
compl β1 = +1
compl  O =  O
compl +1 = β1

neg : πα΄Ί β πα΄Ί
neg = map compl

data π : π€β Μ where
  β2 β1 O +1 +2 : π

πα΄Ί = β β π

_+π_ : π β π β π
(β1 +π β1) = β2
(β1 +π  O) = β1
(β1 +π +1) =  O
( O +π β1) = β1
( O +π  O) =  O
( O +π +1) = +1
(+1 +π β1) =  O
(+1 +π  O) = +1
(+1 +π +1) = +2

add2 : πα΄Ί β πα΄Ί β πα΄Ί
add2 = map2 _+π_

div2-aux : π β π β π Γ π
div2-aux β2  b = β1 ,  b
div2-aux  O  b =  O ,  b
div2-aux +2  b = +1 ,  b
div2-aux β1 β2 = β1 ,  O
div2-aux β1 β1 = β1 , +1
div2-aux β1  O =  O , β2
div2-aux β1 +1 =  O , β1
div2-aux β1 +2 =  O ,  O
div2-aux +1 β2 =  O ,  O
div2-aux +1 β1 =  O , +1
div2-aux +1  O =  O , +2
div2-aux +1 +1 = +1 , β1
div2-aux +1 +2 = +1 ,  O

div2 : πα΄Ί β πα΄Ί
div2 Ξ± 0 = a
 where
  a = prβ (div2-aux (Ξ± 0) (Ξ± 1))
div2 Ξ± (succ n) = div2 (b βΆβΆ x) n
 where
  b = prβ (div2-aux (Ξ± 0) (Ξ± 1))
  x = tail (tail Ξ±)

mid : πα΄Ί β πα΄Ί β πα΄Ί
mid Ξ± Ξ² = div2 (add2 Ξ± Ξ²)

_*π_ : π β π β π
(β1 *π x) = compl x
( O *π x) = O
(+1 *π x) = x

digitMul : π β πα΄Ί β πα΄Ί
digitMul a = map (a *π_)

data π‘ : π€β Μ where
  β4 β3 β2 β1 O +1 +2 +3 +4 : π‘

π‘α΄Ί = β β π‘

div4-aux : π‘ β π‘ β π Γ π‘
div4-aux β4    = β1 ,_
div4-aux  O    =  O ,_
div4-aux +4    = +1 ,_
div4-aux β3 β4 = β1 , β2
div4-aux β3 β3 = β1 , β1
div4-aux β3 β2 = β1 ,  O
div4-aux β3 β1 = β1 , +1
div4-aux β3  O = β1 , +2
div4-aux β3 +1 = β1 , +3
div4-aux β3 +2 =  O , β4
div4-aux β3 +3 =  O , β3
div4-aux β3 +4 =  O , β2
div4-aux β2 β4 = β1 ,  O
div4-aux β2 β3 = β1 , +1
div4-aux β2 β2 = β1 , +2
div4-aux β2 β1 = β1 , +3
div4-aux β2  O =  O , β4
div4-aux β2 +1 =  O , β3
div4-aux β2 +2 =  O , β2
div4-aux β2 +3 =  O , β1
div4-aux β2 +4 =  O ,  O
div4-aux β1 β4 = β1 , +2
div4-aux β1 β3 = β1 , +3
div4-aux β1 β2 =  O , β4
div4-aux β1 β1 =  O , β3
div4-aux β1  O =  O , β2
div4-aux β1 +1 =  O , β1
div4-aux β1 +2 =  O , O
div4-aux β1 +3 =  O , +1
div4-aux β1 +4 =  O , +2
div4-aux +1 β4 =  O , β2
div4-aux +1 β3 =  O , β1 
div4-aux +1 β2 =  O ,  O
div4-aux +1 β1 =  O , +1
div4-aux +1  O =  O , +2
div4-aux +1 +1 =  O , +3
div4-aux +1 +2 =  O , +4
div4-aux +1 +3 = +1 , β3
div4-aux +1 +4 = +1 , β2
div4-aux +2 β4 =  O ,  O
div4-aux +2 β3 =  O , +1
div4-aux +2 β2 =  O , +2
div4-aux +2 β1 =  O , +3
div4-aux +2  O =  O , +4
div4-aux +2 +1 = +1 , β3
div4-aux +2 +2 = +1 , β2
div4-aux +2 +3 = +1 , β1
div4-aux +2 +4 = +1 ,  O
div4-aux +3 β4 =  O , +2
div4-aux +3 β3 =  O , +3
div4-aux +3 β2 =  O , +4
div4-aux +3 β1 = +1 , β3
div4-aux +3  O = +1 , β2
div4-aux +3 +1 = +1 , β1
div4-aux +3 +2 = +1  , O
div4-aux +3 +3 = +1 , +1
div4-aux +3 +4 = +1 , +2

div4 : π‘α΄Ί β πα΄Ί
div4 Ξ± 0 = a
 where
  a = prβ (div4-aux (Ξ± 0) (Ξ± 1))
div4 Ξ± (succ n) = div4 (b βΆβΆ x) n
 where
  b = prβ (div4-aux (Ξ± 0) (Ξ± 1))
  x = tail (tail Ξ±)

_+π_ : π β π β π‘
(β2 +π β2) = β4
(β2 +π β1) = β3
(β2 +π  O) = β2
(β2 +π +1) = β1
(β2 +π +2) = O
(β1 +π β2) = β3
(β1 +π β1) = β2
(β1 +π  O) = β1
(β1 +π +1) = O
(β1 +π +2) = +1
( O +π β2) = β2
( O +π β1) = β1
( O +π  O) = O
( O +π +1) = +1
( O +π +2) = +2
(+1 +π β2) = β1
(+1 +π β1) = O
(+1 +π  O) = +1
(+1 +π +1) = +2
(+1 +π +2) = +3
(+2 +π β2) = O
(+2 +π β1) = +1
(+2 +π  O) = +2
(+2 +π +1) = +3
(+2 +π +2) = +4

bigMid' : (β β πα΄Ί) β π‘α΄Ί
bigMid' zs 0 = (x 0 +π x 0) +π (x 1 +π y 0)
 where x  = zs 0
       y  = zs 1
bigMid' zs (succ n) = bigMid' (mid (tail (tail x)) (tail y) βΆβΆ tail (tail zs)) n
 where x = zs 0
       y = zs 1

bigMid : (β β πα΄Ί) β πα΄Ί
bigMid = div4 β bigMid'

repeat : {X : π€ Μ } β X β β β X
repeat Ξ± _ = Ξ±

mul : πα΄Ί β πα΄Ί β πα΄Ί
mul x y = bigMid (map2 digitMul x (repeat y))

znorm : πα΄Ί β πα΄Ί

znorm' : π β π β πα΄Ί β πα΄Ί
znorm' O b Ξ± zero = O
znorm' O b Ξ± (succ n) = znorm' b (head Ξ±) (tail Ξ±) n
znorm' β1 +1 Ξ± zero = O
znorm' β1 +1 Ξ± (succ n) = znorm' β1 (head Ξ±) (tail Ξ±) n
znorm' +1 β1 Ξ± zero = O
znorm' +1 β1 Ξ± (succ n) = znorm' +1 (head Ξ±) (tail Ξ±) n
znorm' β1 β1 Ξ± = β1 βΆβΆ (β1 βΆβΆ Ξ±)
znorm' β1  O Ξ± = β1 βΆβΆ ( O βΆβΆ Ξ±)
znorm' +1  O Ξ± = +1 βΆβΆ ( O βΆβΆ Ξ±)
znorm' +1 +1 Ξ± = +1 βΆβΆ (+1 βΆβΆ Ξ±)

znorm Ξ± = znorm' (head Ξ±) (head (tail Ξ±)) (tail (tail Ξ±))

_ββ_ : β β β β β
0 ββ _ = 0
succ a ββ 0 = succ a
succ a ββ succ b = a ββ b

negative' : π β πα΄Ί β β β β β π€β Μ
negative' β1 _ _ _ = π
negative' +1 _ _ _ = π
negative'  O _ 0 _ = π
negative'  O Ξ± (succ k) n = negative' (Ξ± (n ββ succ k)) Ξ± k n

negative : πα΄Ί β β β π€β Μ
negative Ξ± n = negative' (head (znorm Ξ±)) (znorm Ξ±) n n

smaller : β β πα΄Ί β πα΄Ί β π€β Μ
smaller n Ξ± Ξ² = negative (mid Ξ± (neg Ξ²)) (succ n)
