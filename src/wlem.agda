{-
  Weak excluded middle states that for every propostiion P, either ¬¬P or ¬P holds.

  We give a proof of weak excluded middle, relying just on basic facts about real numbers,
  which we carefully state, in order to make the dependence on them transparent.

  Some people might doubt the formalization. To convince yourself that there is no cheating, you should:

  * Carefully read the facts listed in the RealFacts below to see that these are all
    just familiar facts about the real numbers.

  * Verify that there are no postulates or holes (unproved statements).

  * Carefully read the statement of WLEM to see that it matches the informal statement.

  * Run the file with Agda.

  © 1 April 2023 -- Andrej Bauer

  Code slightly modified to add the proof that the converse also holds.
  
  © 16 June 2025 -- Luna Strah
-}

{-# OPTIONS -W noDuplicateInterfaceFiles #-}

open import Agda.Primitive
open import Data.Empty
open import Data.Unit hiding (_≤_)
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Sum
open import Relation.Nullary

module wlem where

  open Σ

  record Reals : Set₁ where
    field
      ℝ : Set

      𝟘 : ℝ
      𝟙 : ℝ
      𝟚 : ℝ
      𝟛 : ℝ

      _<_ : ℝ → ℝ → Set

      𝟘<𝟙 : 𝟘 < 𝟙
      𝟙<𝟚 : 𝟙 < 𝟚
      𝟚<𝟛 : 𝟚 < 𝟛

      <-irref : ∀ {x} → ¬ (x < x)
      <-trans : ∀ {x y z} → x < y → y < z → x < z

      𝟘<x : ∀ {x} → (Σ[ s ∈ ℝ ] (𝟘 < s × (¬(x < s)))) → 𝟘 < x
      x<𝟛 : ∀ {x} → (Σ[ r ∈ ℝ ] (r < 𝟛 × (¬(r < x)))) → x < 𝟛

      _≤_ : ℝ → ℝ → Set

      ≤-refl : ∀ {x} → x ≤ x
      ≤-trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z

      <⇒≤ : ∀ {x y} → x < y → x ≤ y

      <-≤⇒< : ∀ {x y z} → x < y → y ≤ z → x < z
      ≤-<⇒< : ∀ {x y z} → x ≤ y → y < z → x < z

    is-bound : ∀ (S : ℝ → Set) (x : ℝ) → Set
    is-bound S x = ∀ y → S y → y ≤ x

    is-inhabited : ∀ (S : ℝ → Set) → Set
    is-inhabited S = Σ[ x ∈ ℝ ] S x

    is-bounded : ∀ (S : ℝ → Set) → Set
    is-bounded S = Σ[ x ∈ ℝ ] is-bound S x

    is-supremum : ∀ (S : ℝ → Set) (x : ℝ) → Set
    is-supremum S x = is-bound S x × (∀ y → is-bound S y → x ≤ y)

    -- A bounded inhabited subset of reals has a supremum, see
    -- https://ncatlab.org/nlab/show/diff/MacNeille+real+number#completeness
    field
      sup : ∀ (S : ℝ → Set) → is-inhabited S → is-bounded S → ℝ
      sup-supremum : ∀ (S : ℝ → Set) (i : is-inhabited S) (b : is-bounded S) → is-supremum S (sup S i b)

    -- Some derived facts

    <-asymm : ∀ {x y} → x < y → ¬ (y < x)
    <-asymm p q = <-irref (<-trans p q)

    𝟘<𝟛 : 𝟘 < 𝟛
    𝟘<𝟛 = <-trans 𝟘<𝟙 (<-trans 𝟙<𝟚 𝟚<𝟛)
    𝟘≤𝟛 : 𝟘 ≤ 𝟛
    𝟘≤𝟛 = <⇒≤ 𝟘<𝟛

  WLEM : Set₁
  WLEM = ∀ (P : Set) → ¬ ¬ P ⊎ ¬ P

  -- Here we require 0 < x ∨ x < 3 to hold. This is equivalent to locatedness
  Cover : Reals → Set
  Cover ℛ = (x : Reals.ℝ ℛ) → (Reals._<_ ℛ) (Reals.𝟘 ℛ) x ⊎ (Reals._<_ ℛ) x (Reals.𝟛 ℛ)

  module _ (ℛ : Reals) (wlem : WLEM) where
    open Reals ℛ

    -- DeMorgan is equivalent to WLEM, but is more appropriate for the proof
    DeMorgan : ∀ {P Q : Set} → ¬ (P × Q) → (¬ P) ⊎ (¬ Q)
    DeMorgan {P} {Q} ¬p∧q = DM
      where
        DM : (¬ P) ⊎ (¬ Q)
        DM with (wlem P) | (wlem Q)
        ... | inj₁ nnp   | inj₁ nnq = ⊥-elim (nnq (λ q → nnp (λ p → ¬p∧q (p , q))))
        ... | inj₁ nnp   | inj₂ nq  = inj₂ nq
        ... | inj₂  np   | inj₁ nnq = inj₁ np
        ... | inj₂  np   | inj₂ nq  = inj₁ np

    cover : Cover ℛ
    cover x = cover-proof
      where
        ¬x<𝟙∧𝟚<x : ¬ ((x < 𝟙) × (𝟚 < x))
        ¬x<𝟙∧𝟚<x (p , q) = <-asymm 𝟙<𝟚 (<-trans q p)

        -- Use DeMorgan on above to derive ¬(x < 1) ∨ ¬(2 < x)
        x≮𝟙∨𝟚≮x = DeMorgan ¬x<𝟙∧𝟚<x

        -- Use tightness of MacNeille reals for each of the disjuncts
        x≮𝟙⇒𝟘<x : ¬ (x < 𝟙) → 𝟘 < x
        x≮𝟙⇒𝟘<x p = 𝟘<x (𝟙 , 𝟘<𝟙 , p)

        𝟚≮x⇒x<𝟛 : ¬ (𝟚 < x) → x < 𝟛
        𝟚≮x⇒x<𝟛 q = x<𝟛 (𝟚 , 𝟚<𝟛 , q)

        -- Proof of covering
        cover-proof : (𝟘 < x) ⊎ (x < 𝟛)
        cover-proof = map x≮𝟙⇒𝟘<x 𝟚≮x⇒x<𝟛 x≮𝟙∨𝟚≮x


  module _ (ℛ : Reals) (cover : Cover ℛ) where
    open Reals ℛ

    wlem : WLEM
    wlem P = wlem-proof
      where
        -- Consider a proposition P.

        -- Let S := {x ∈ ℝ | x ≤ 0 ∨ (x ≤ 3 ∧ P) }
        S : ℝ → Set
        S x = (x ≤ 𝟘) ⊎ ((x ≤ 𝟛) × P)

        -- S is inhabited by 0
        S-inhabited : is-inhabited S
        S-inhabited = 𝟘 , inj₁ ≤-refl

        -- S is bunded by 3
        S-bounded : is-bounded S
        S-bounded = 𝟛 , λ { _ (inj₁ x≤𝟘) → ≤-trans x≤𝟘 𝟘≤𝟛 ; _ (inj₂ (y≤𝟛 , _)) → y≤𝟛}

        -- if ¬P holds then 0 is an upper bound for S
        ¬P⇒S≤𝟘 : ¬ P → is-bound S 𝟘
        ¬P⇒S≤𝟘 _ _ (inj₁ y≤𝟘) = y≤𝟘
        ¬P⇒S≤𝟘 ¬p _ (inj₂ (y≤𝟛 , p)) = ⊥-elim (¬p p)

        -- S is inhabited and bounded, so it has a supremum u
        u : ℝ
        u = sup S S-inhabited S-bounded

        -- If P holds then 3 ≤ u
        P⇒𝟛≤u : P → 𝟛 ≤ u
        P⇒𝟛≤u p = proj₁ (sup-supremum S S-inhabited S-bounded) 𝟛 (inj₂ (≤-refl , p))

        -- If ¬p holds then u ≤ 0
        ¬P⇒u≤𝟘 : ¬ P → u ≤ 𝟘
        ¬P⇒u≤𝟘 ¬p = proj₂ (sup-supremum S S-inhabited S-bounded) 𝟘 (¬P⇒S≤𝟘 ¬p)

        -- Proof of WLEM
        wlem-proof : ¬ ¬ P ⊎ ¬ P
        wlem-proof with cover u
        -- either 0 < u or u < 3
        ... | inj₁ 𝟘<u =
           -- if 0 < u then ¬¬P: if ¬P were the case, we would get u ≤ 0 < u
           inj₁ (λ ¬p → <-irref {x = u} (≤-<⇒< (¬P⇒u≤𝟘 ¬p) 𝟘<u))
        ... | inj₂ u<𝟛 =
           -- if u < 3 then ¬P: if P were the case, we woudl get u < 3 ≤ u
           inj₂ λ p → <-irref (<-≤⇒< u<𝟛 (P⇒𝟛≤u p))
