{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module _ where

data I : Type lzero where
  I0 : I
  I1 : I

postulate
  Iseg : I0 == I1

I-elim : ∀ {l} {C : I → Type l}
  (I0* : C I0) (I1* : C I1)
  (Iseg* : I0* == I1* [ C ↓ Iseg ])
  → (x : I) → C x
I-elim I0* I1* Iseg* I0 = I0*
I-elim I0* I1* Iseg* I1 = I1*

¬Iseg : (I0 == I1) → ⊥
¬Iseg ()
