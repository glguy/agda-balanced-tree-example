module TreeProofs where

data Full {A : Set} : Tree A → Set where
  leaf : Full leaf
  branch : {a : A} {t₁ t₂ : Tree A} (full₁ : Full t₁) (full₂ : Full t₂)
           (height-≡ : height t₁ ≡ height t₂)
         → Full (branch right a t₁ t₂)

data Balanced {A : Set} : Tree A → Set where
  leaf : Balanced leaf
  branchˡ : {a : A} {t₁ t₂ : Tree A} → Balanced t₁ → Full t₂ → height t₁ ≡ 1 + height t₂ → Balanced (branch left a t₁ t₂)
  branchʳ : {a : A} {t₁ t₂ : Tree A} → Full t₁ → Balanced t₂ → height t₁ ≡ height t₂ → Balanced (branch right a t₁ t₂)

full-is-balanced : {A : Set} {t : Tree A} → Full t → Balanced t
full-is-balanced leaf = leaf
full-is-balanced (branch full₁ full₂ height-≡) = branchʳ full₁ (full-is-balanced full₂) height-≡


conflicting-maybe : {A B : Set} {a : A} {b : Maybe A} → just a ≡ b → nothing ≡ b → B
conflicting-maybe refl ()

nested-failure : {A : Set} {a x : A} {t₁ t₂ : Tree A}
                 → nothing ≡ insertTree a t₂
                 → nothing ≡ insertTree a (branch right x t₁ t₂)
nested-failure {_}{a}{_}{_}{t₂} eq with insertTree a t₂
nested-failure () | just _
nested-failure _  | nothing = refl



full-insert-fails : {A : Set} {a : A} {t : Tree A} → Full t → nothing ≡ insertTree a t

full-insert-fails leaf = refl

full-insert-fails {_}{a} (branch {_}{_}{t₂} _ _ _) with inspect (insertTree a t₂)
full-insert-fails (branch _ _ _) | nothing with-≡ eq = nested-failure eq

full-insert-fails (branch _ full₂ _) | just _ with-≡ eq = conflicting-maybe eq (full-insert-fails full₂)

ins-left-ok : {A : Set} {a b : A} {t₁ t₂ : Tree A} → ¬ nothing ≡ insertTree a (branch left b t₁ t₂)
ins-left-ok {_}{a}{_}{t₁} _ with insertTree a t₁
ins-left-ok () | nothing
ins-left-ok () | just _

ins-left-ok' : {A : Set} {a b : A} {t₁ t₂ : Tree A} → ∃ λ t → just t ≡ insertTree a (branch left b t₁ t₂)
ins-left-ok' {A}{a}{b}{t₁}{t₂} with insertTree a t₁
... | just t = branch left b t t₂ , refl
... | nothing = branch right b t₁ (insertFullTree a t₂) , refl

insert-balanced : {A : Set} {a : A} {t : Tree A} → nothing ≡ insertTree a t → Balanced t → Full t
insert-balanced _ leaf = leaf
insert-balanced {A} {a} {branch left b t₁ t₂} eq (branchˡ balanced₁ full₂ height-≡)
  = ⊥-elim (ins-left-ok {A}{a}{b}{t₁}{t₂} eq)
insert-balanced {A}{a} _ (branchʳ {_}{_}{t₂} _ _ _) with inspect (insertTree a t₂)
insert-balanced _ (branchʳ full₁ balanced₂ height-≡) | nothing with-≡ res
  = branch full₁ (insert-balanced res balanced₂) height-≡
insert-balanced {_}{a} _ (branchʳ {_}{_}{t₂} _ _ _) | just _ with-≡ _ with insertTree a t₂
insert-balanced refl (branchʳ _ _ _) | just _ with-≡ () | nothing
insert-balanced () (branchʳ _ _ _) | just _ with-≡ _ | just _

open ≡-Reasoning

lem : (a b c : ℕ)
    → a ≡ b
    → suc a ≡ c
    → suc (suc a ⊔ b) ≡ suc c ⊔ b
lem .b b .(suc b) refl refl = {!!}

insert-fulltree-height : {A : Set} (a : A) (t : Tree A) → Full t → (suc (height t) ≡ height (insertFullTree a t))
insert-fulltree-height a leaf f = refl
insert-fulltree-height {A} a (branch .right a' t₁ t₂) (branch full₁ full₂ height-≡)
  = lem (height t₁) (height t₂) (height (insertFullTree a t₁)) height-≡ (insert-fulltree-height {A} a t₁ full₁)
{-   begin
    suc (suc (height t₁) ⊔ height t₂) ≡⟨ {!!} ⟩
    {!suc (suc (height t₁)) ⊔ suc (height t₂)!} ≡⟨ {!!} ⟩
    {!!} ≡⟨ {!!} ⟩
    suc (height (insertFullTree a t₁)) ⊔ height t₂ ∎
-}
insert-height : {A : Set} (a : A) (t t′ : Tree A) → Balanced t → just t′ ≡ insertTree a t → height t ≡ height t′
insert-height a leaf t′ b ()
insert-height a (branch left a' t₁ t₂) t′ b eq with insertTree a t₁
insert-height a (branch left a' t₁ t₂) t′ (branchˡ y y' y0) eq | nothing = {!!}
... | just t₁′ = {!!}
insert-height a (branch right a' t₁ t₂) t′ b eq = {!!}
insert-success : {A : Set} (a : A) {t : Tree A} (t′ : Tree A) → Balanced t → just t′ ≡ insertTree a t → Balanced t′
insert-success _ _ leaf ()
insert-success a leaf (branchˡ {_}{t₁} y y' y0) eq with insertTree a t₁
insert-success _ leaf (branchˡ _ _ _) () | nothing
insert-success _ leaf (branchˡ _ _ _) () | just _
insert-success a (branch left a' t₁ t₂) (branchˡ {_}{t₁'} y y' y0) eq = {!!}
insert-success a (branch right a' t₁ t₂) (branchˡ y y' y0) eq = {!!}
insert-success a t′ (branchʳ {_}{_}{t₂} y y' y0) eq with insertTree a t₂
insert-success a t′ (branchʳ {_}{_}{t₂} y y' y0) () | nothing
insert-success _ leaf (branchʳ y y' y0) () | just _
insert-success a (branch .right .a' .t₁ .k) (branchʳ {a'} {t₁} {t₂} y y' y0) refl | just k with inspect (insertTree a t₂)
... | nothing with-≡ eq' = branchʳ y {!!} {!!}
... | just x with-≡ eq' = {!!}
