module Tree where

open import Data.Nat
open import Data.Maybe
open import Data.Product
open import Data.Bool

data Direction : Set where
  left : Direction
  right : Direction

data Tree a : Set where
  leaf   :                                   Tree a
  branch : Direction → a → Tree a → Tree a → Tree a

height : ∀ {a} → Tree a → ℕ
height leaf               = 0
height (branch _ _ t₁ t₂) = 1 + (height t₁ ⊔ height t₂)

insertFullTree : ∀ {a} → a → Tree a → Tree a
insertFullTree x leaf               = branch right x leaf leaf
insertFullTree x (branch _ a t₁ t₂) = branch left a (insertFullTree x t₁) t₂

insertTree : ∀ {a} → a → Tree a → Maybe (Tree a)
insertTree _ leaf = nothing
insertTree x (branch left a t₁ t₂) with insertTree x t₁
... | nothing  = just (branch right a t₁ (insertFullTree x t₂))
... | just t₁′ = just (branch left a t₁′ t₂)
insertTree x (branch right a t₁ t₂) with insertTree x t₂
... | nothing  = nothing
... | just t₂′ = just (branch right a t₁ t₂′)

insert : ∀ {a} → a → Tree a → Tree a
insert x t with insertTree x t
... | nothing = insertFullTree x t
... | just t′ = t′

fullToBalanced : ∀ {a} → Tree a → Tree a
fullToBalanced leaf = leaf
fullToBalanced (branch _ a l r) = branch right a l (fullToBalanced r)

delete₁ : ∀ {a} → Direction → a → Tree a → Tree a → Bool × Tree a
delete₁ right _ _ leaf = true , leaf
delete₁ right a l (branch d' a' l' r') with delete₁ d' a' l' r'
... | false , r = false , branch right a l r
... | true  , r = false , branch left  a (fullToBalanced l) r
delete₁ left  a (branch d' a' l' r') r with delete₁ d' a' l' r'
... | false , l = false , branch left  a l r
... | true  , l = true  , branch right a l r
delete₁ _ _ _ _ = true , leaf -- this never happens on good inputs

delete : ∀ {a} → Tree a → Maybe (Tree a)
delete leaf = nothing
delete (branch d a l r) = just (proj₂ (delete₁ d a l r))