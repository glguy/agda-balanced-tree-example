module HeightProperties where

open import Tree
open import BalancedProperty
open import Data.Unit

open import Data.Nat
open import Data.Maybe
open import Data.Function
open import Relation.Binary.PropositionalEquality
open import Relation.Unary


suc⊔self : ∀ b → suc b ⊔ b ≡ suc b ⊔ suc b
suc⊔self zero    = refl
suc⊔self (suc n) = cong suc (suc⊔self n)



insertFullTree-height : {A : Set} (a : A) {t : Tree A}
                      → Full t → 1 + height t ≡ height (insertFullTree a t)
insertFullTree-height _ leaf = refl
insertFullTree-height a (branch _ _ t₂ full₁ _ height-≡)
  with insertFullTree-height a full₁
... | eq rewrite sym eq | height-≡ = sym (suc⊔self (suc (height t₂)))




insertTree-height : {A : Set} (a : A) {t : Tree A} → Balanced t
                  → maybe (λ t′ → height t ≡ height t′) ⊤ (insertTree a t)

insertTree-height _ leaf = _

insertTree-height a (branchˡ a' t₁ t₂ bal₁ full₂ height-≡)
  with insertTree a t₁ | insertTree-height a bal₁ | insertFullTree-height a full₂
...  | just t₁′        | t₁′-height               | _
  rewrite t₁′-height = refl
...  | nothing         | _                        | t₂′-height
  rewrite sym t₂′-height | height-≡ = cong suc (suc⊔self (height t₂))

insertTree-height a (branchʳ a' t₁ t₂ _ bal₂ _)
  with insertTree a t₂ | insertTree-height a bal₂
... | nothing          | _                             = _
... | just _           | t₂′-height rewrite t₂′-height = refl



open ≡-Reasoning

insertFullTree-balanced : {A : Set} (a : A) {t : Tree A} → Full t
                        → Balanced (insertFullTree a t)
insertFullTree-balanced a leaf = branchʳ a leaf leaf leaf leaf refl
insertFullTree-balanced a (branch a' t₁ t₂ full₁ full₂ height-≡)
  = branchˡ a' (insertFullTree a t₁) t₂ (insertFullTree-balanced a full₁) full₂ h
  where
   h = begin
      height (insertFullTree a t₁) ≡⟨ sym (insertFullTree-height a full₁) ⟩
      1 + height t₁                ≡⟨ cong suc height-≡ ⟩
      1 + height t₂                ∎




insertTree-balanced : {A : Set} (a : A) {t : Tree A} → Balanced t
                    → maybe Balanced (Full t) (insertTree a t)

insertTree-balanced _ leaf = leaf

insertTree-balanced a (branchˡ a' t₁ t₂ bal₁ full₂ height-≡)
  with insertTree a t₁ | insertTree-balanced a bal₁ | insertTree-height a bal₁
...  | just t₁′ | bt₁′ | ht′ = branchˡ a' t₁′ t₂ bt₁′ full₂ height-≡′
  where
   height-≡′ = begin
     height t₁′    ≡⟨ sym ht′ ⟩
     height t₁     ≡⟨ height-≡ ⟩
     1 + height t₂ ∎

...  | nothing | full₁ | _   
  = branchʳ a' t₁ (insertFullTree a t₂) full₁ (insertFullTree-balanced a full₂) h
  where
   h = begin
     height t₁                    ≡⟨ height-≡ ⟩
     1 + height t₂                ≡⟨ insertFullTree-height a full₂ ⟩
     height (insertFullTree a t₂) ∎

insertTree-balanced a (branchʳ a' t₁ t₂ full₁ bal₂ height-≡)
  with insertTree a t₂ | insertTree-balanced a bal₂ | insertTree-height a bal₂
...  | nothing  | full₂ | _   = branch a' t₁ t₂ full₁ full₂ height-≡ 
...  | just t₂′ | bt₂   | ht₂ = branchʳ a' t₁ t₂′ full₁ bt₂ height-≡′
  where
    height-≡′ = begin
       height t₁  ≡⟨ height-≡ ⟩
       height t₂  ≡⟨ ht₂      ⟩
       height t₂′ ∎
                         



insert-balanced : {A : Set} (a : A) → Balanced ⊆ (Balanced ∘ insert a)
insert-balanced a {t} b
  with insertTree a t | insertTree-balanced a b
...   | just x        | y                         = y
...   | nothing       | y                         = insertFullTree-balanced a y