{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module _ {i} where

data AttachedSkeleton n (Skel : Type (lsucc i))
  (Real : Skel → Type i) : Type (lsucc i) where
  attached-skeleton :
      (skel : Skel)
    → (cells : hSet i)
    → (fst cells → Sphere n → Real skel)
    → AttachedSkeleton n Skel Real

Skeleton : ℕ → Type (lsucc i)
Realizer : {n : ℕ} → Skeleton n → Type i

Skeleton O = Σ (Type i) is-set
Skeleton (S n) = AttachedSkeleton n (Skeleton n) Realizer

Realizer {n = O} A = fst A
Realizer {n = S n} (attached-skeleton skel cells α) =
  Pushout (span
    (Realizer skel) (fst cells) (fst cells × Sphere n)
    (uncurry α) fst)

cw-init : ∀ {n} → Skeleton (S n) → Skeleton n
cw-init (attached-skeleton skel _ _) = skel

cw-incl-last : ∀ {n} (skel : Skeleton (S n))
  → (Realizer (cw-init skel) → Realizer skel)
cw-incl-last (attached-skeleton _ _ _) = left
