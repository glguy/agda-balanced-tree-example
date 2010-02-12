module BalancedProperty where

open import Relation.Binary.PropositionalEquality
open import Data.Nat

open import Tree

data Full {A} : Tree A → Set where
  leaf : Full leaf
  branch : ∀ a t₁ t₂
         → Full t₁
         → Full t₂
         → height t₁ ≡ height t₂
         → Full (branch right a t₁ t₂)

data Balanced {A} : Tree A → Set where
  leaf : Balanced leaf

  branchˡ : ∀ a t₁ t₂
          → Balanced t₁
          → Full t₂
          → height t₁ ≡ 1 + height t₂
          → Balanced (branch left a t₁ t₂)

  branchʳ : ∀ a t₁ t₂
          → Full t₁
          → Balanced t₂
          → height t₁ ≡ height t₂
          → Balanced (branch right a t₁ t₂)

