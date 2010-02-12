module DeleteProperties where

open import Data.Bool
open import Data.Maybe
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Unit
open import Tree
open import BalancedProperty

data Delete {A} : Bool × Tree A → Set where
  del-ful : ∀ {t} → Full t     → Delete (true  , t)
  del-bal : ∀ {t} → Balanced t → Delete (false , t)

suc⊔self : ∀ b → suc b ⊔ b ≡ suc b ⊔ suc b
suc⊔self zero    = refl
suc⊔self (suc n) = cong suc (suc⊔self n)

fullToBalanced-height : {A : Set} {t : Tree A} → Full t → height t ≡ height (fullToBalanced t)
fullToBalanced-height leaf = refl
fullToBalanced-height (branch a t₁ t₂ y y' y0) with fullToBalanced-height y'
... | h rewrite h = refl

fullToBalanced-balanced : {A : Set} {t : Tree A} → Full t → Balanced (fullToBalanced t)
fullToBalanced-balanced leaf = leaf
fullToBalanced-balanced (branch a t₁ t₂ y y' y0) = branchʳ a t₁ (fullToBalanced t₂) y (fullToBalanced-balanced y') (trans y0 (fullToBalanced-height y'))

height-prop : {A : Set} → Tree A → Bool × Tree A → Set
height-prop t (true , t′) = height t ≡ 1 + height t′
height-prop t (false , t′) = height t ≡ height t′

delete₁-height
  : {A : Set} {d : Direction} {a : A} {l r : Tree A}
  → Balanced (branch d a l r) → height-prop (branch d a l r)
                                   (delete₁ d a l r)
delete₁-height (branchˡ a leaf r y y' ())
delete₁-height (branchˡ a (branch y y' y0 y1) r y2 y3 y4) with delete₁ y y' y0 y1 | delete₁-height y2
... | false , q | p rewrite p = refl
... | true , q | p rewrite p | cong pred y4 = cong suc (suc⊔self (height r))
delete₁-height (branchʳ a l leaf y y' y0) rewrite y0 = refl
delete₁-height (branchʳ a l (branch y y' y0 y1) y2 y3 y4)
  with delete₁ y y' y0 y1 | delete₁-height y3 | fullToBalanced-height y2
... | false , q | p | s rewrite sym y4 | p = cong suc refl
... | true , q | p  | s rewrite sym y4 | p | sym s = cong suc (sym (suc⊔self (height q)))

delete₁-balanced : {A : Set} {d : Direction} {a : A} {l r : Tree A}
   → Balanced (branch d a l r) → Delete (delete₁ d a l r)
delete₁-balanced (branchˡ a leaf r y y' ())
delete₁-balanced (branchˡ a (branch y y' y0 y1) r y2 y3 y4)
 with delete₁ y y' y0 y1 | delete₁-balanced y2 | delete₁-height y2
... | false , q | del-bal b | h rewrite h = del-bal (branchˡ a q r b y3 y4)
... | true  , q | del-ful f | h rewrite h = del-ful (branch a q r f y3 (cong pred y4))
delete₁-balanced (branchʳ a l leaf y y' y0) = del-ful leaf
delete₁-balanced (branchʳ a l (branch y y' y0 y1) y2 y3 y4)
 with delete₁ y y' y0 y1 | delete₁-balanced y3 | delete₁-height y3
... | false , q | del-bal b | h rewrite h = del-bal (branchʳ a l q y2 b y4)
... | true , q | del-ful b | h rewrite h = del-bal (branchˡ a (fullToBalanced l) q (fullToBalanced-balanced y2) b (trans (sym (fullToBalanced-height y2)) y4))

full-is-balanced : {A : Set} {t : Tree A} → Full t → Balanced t
full-is-balanced leaf = leaf
full-is-balanced (branch a t₁ t₂ full₁ full₂ height-≡) = branchʳ a t₁ t₂ full₁ (full-is-balanced full₂) height-≡

delete-balanced : {A : Set} {t : Tree A} → Balanced t → maybe Balanced ⊤ (delete t)
delete-balanced leaf = _
delete-balanced (branchˡ a t₁ t₂ y y' y0) with delete₁ left a t₁ t₂ | delete₁-balanced (branchˡ a t₁ t₂ y y' y0)
... | false , t | del-bal b = b
... | true  , t | del-ful f = full-is-balanced f

delete-balanced (branchʳ a t₁ t₂ y y' y0) with delete₁ right a t₁ t₂ | delete₁-balanced (branchʳ a t₁ t₂ y y' y0)
... | false , t | del-bal b = b
... | true , t | del-ful b = full-is-balanced b