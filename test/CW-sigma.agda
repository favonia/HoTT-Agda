{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module _ {i} where

Skeleton : ℕ → Type (lsucc i)
Realizer : {n : ℕ} → Skeleton n → Type i

Skeleton O = Σ (Type i) is-set
Skeleton (S n) =
  Σ (Skeleton n) λ skel →
    Σ (Σ (Type i) is-set) λ cells →
      fst cells → Sphere n → Realizer {n} skel

Realizer {n = O} A = fst A
Realizer {n = S n} (skel , cells , α) =
  Pushout (span
    (Realizer {n} skel) (fst cells) (fst cells × Sphere n)
    (uncurry α) fst)

cw-init : ∀ {n} → Skeleton (S n) → Skeleton n
cw-init (skel , _ , _) = skel

cw-incl-last : ∀ {n} (skel : Skeleton (S n))
  → (Realizer {n} (cw-init {n} skel) → Realizer {S n} skel)
cw-incl-last _ = left
