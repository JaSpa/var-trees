module Tree where

open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; [_])
open import Data.Product using (_×_; _,_; -,_; ∃-syntax)
open import Function
open import Level renaming (suc to ℓsuc)
open import Relation.Binary.PropositionalEquality as Eq hiding ([_])
open import Relation.Unary using (Pred)

private variable
  a b c ℓ : Level
  A : Set a
  B : Set b
  C : Set c

data Tree (A : Set a) : Set a where
  leaf : A → Tree A
  node : Tree A → Tree A → Tree A

module Relation where
  module _ {A : Set a} (P : Pred A ℓ) where
    data Any : Pred (Tree A) (a ⊔ ℓ) where
      here : ∀ {x} → P x → Any (leaf x)
      left : ∀ {l r} → Any l → Any (node l r)
      right : ∀ {l r} → Any r → Any (node l r)
                                            
    data All : Pred (Tree A) (a ⊔ ℓ) where
      leaf : ∀ {x} → P x → All (leaf x)
      node : ∀ {l r} → All l → All r → All (node l r)

open Relation.Any

_∈_ : A → Tree A → Set _
a ∈ T = Relation.Any (a ≡_) T

bind∈ : (t : Tree A) → (∀ {x} → x ∈ t → Tree B) → Tree B
bind∈ (leaf x)    f = f (here refl)
bind∈ (node l r)  f = node (bind∈ l (f ∘ left)) (bind∈ r (f ∘ right))

map∈ : (t : Tree A) → (∀ {x} → x ∈ t → B) → Tree B
map∈ t f = bind∈ t (leaf ∘ f)

map : (t : Tree A) → (A → B) → Tree B
map t f = map∈ t λ {x} _ → f x

map-id : {f : A → A} → f ≗ id → flip map f ≗ id
map-id f≗id (leaf x)    = cong leaf (f≗id x)
map-id f≗id (node l r)  = cong₂ node (map-id f≗id l) (map-id f≗id r)

bind∈-cong : (t : Tree A) {f : ∀ {x} → x ∈ t → Tree B} {g : ∀ {x} → x ∈ t → Tree B}
  → (∀ {x} (p : x ∈ t) → f p ≡ g p)
  → bind∈ t f ≡ bind∈ t g
bind∈-cong (leaf x) {f = f} f≗g with f (here refl) | f≗g (here refl)
... | fx | fx≡gx = fx≡gx
bind∈-cong (node l r) f≗g = cong₂ node
  (bind∈-cong l (f≗g ∘ left))
  (bind∈-cong r (f≗g ∘ right))

map-cong : {f : A → B}{g : A → B} → f ≗ g → flip map f ≗ flip map g
map-cong {f = f} f≗g (leaf x) with f x | f≗g x
... | fx | refl = refl
map-cong f≗g (node l r) = cong₂ node (map-cong f≗g l) (map-cong f≗g r)

f∈map·t→∈t : ∀ t {fx}{f : A → B} → fx ∈ map t f → ∃[ x ] x ∈ t × f x ≡ fx
f∈map·t→∈t (leaf x) (here refl) = -, here refl , refl
f∈map·t→∈t (node l r) (left p) with f∈map·t→∈t l p
... | x , p , eq = x , left p , eq
f∈map·t→∈t (node l r) (right p) with f∈map·t→∈t r p
... | x , p , eq = x , right p , eq

map∈-pres-∈ : ∀ {t}{a : A}{f : ∀ {x} → x ∈ t → B} (p : a ∈ t) → f p ∈ map∈ t f
map∈-pres-∈ (here refl) = here refl
map∈-pres-∈ (left  p)   = left (map∈-pres-∈ p)
map∈-pres-∈ (right p)   = right (map∈-pres-∈ p)

map-pres-∈ : ∀ {t}{a : A}{f : A → B} → a ∈ t → f a ∈ map t f
map-pres-∈ = map∈-pres-∈

map-bind∈-compose
  : ∀ {a b c}{A : Set a}{B : Set b}{C : Set c}
      (t : Tree A) {f : ∀ {x} → x ∈ t → Tree B}{g : B → C}
  → map (bind∈ t f) g ≡ bind∈ t (flip map g ∘ f)
map-bind∈-compose (leaf x)   = refl
map-bind∈-compose (node l r) = cong₂ node (map-bind∈-compose l) (map-bind∈-compose r)

bind∈-map-compose
  : ∀ {a b c}{A : Set a}{B : Set b}{C : Set c}
      (t : Tree A) {f : A → B}{g : ∀ {x} → x ∈ map t f → Tree C}
  → bind∈ (map t f) g ≡ bind∈ t (g ∘ map-pres-∈)
bind∈-map-compose (leaf x)   = refl
bind∈-map-compose (node l r) = cong₂ node (bind∈-map-compose l) (bind∈-map-compose r)

map-∘ : ∀ {a b c}{A : Set a}{B : Set b}{C : Set c}{g : B → C}{f : A → B} →
  flip map g ∘ flip map f ≗ flip map (g ∘ f)
map-∘ t = map-bind∈-compose t

module Zip where
  open import Relation.Binary
  open import Data.List.Relation.Unary.Any using (here; there)
  
  import Data.List.Membership.Propositional as L

  data Split {A : Set ℓ} : List A → List A → List A → Set ℓ where
    []     : Split [] [] []
    left   : ∀ {a as xs ys} → Split as xs ys → Split (a ∷ as) (a ∷ xs) ys
    right  : ∀ {a as xs ys} → Split as xs ys → Split (a ∷ as) xs (a ∷ ys)

  ∈·splitˡ⇒∈ : ∀ {a : A} {as xs ys} → Split as xs ys → a L.∈ xs → a L.∈ as
  ∈·splitˡ⇒∈ (left _) (here p) = here p
  ∈·splitˡ⇒∈ (left s) (there p) = there (∈·splitˡ⇒∈ s p)
  ∈·splitˡ⇒∈ (right s) p = there (∈·splitˡ⇒∈ s p)

  ∈·splitʳ⇒∈ : ∀ {a : A} {as xs ys} → Split as xs ys → a L.∈ ys → a L.∈ as
  ∈·splitʳ⇒∈ (right _) (here p) = here p
  ∈·splitʳ⇒∈ (right s) (there p) = there (∈·splitʳ⇒∈ s p)
  ∈·splitʳ⇒∈ (left s) p = there (∈·splitʳ⇒∈ s p)

  module _ {r⁻ r⁺}{A : Set a}{B : Set b}{C : Set ℓ} (R⁻ : REL A B r⁻) (R⁺ : C → REL A B r⁺) where
    private
      ℓ… : Level
      ℓ… = a ⊔ b ⊔ r⁻ ⊔ r⁺ ⊔ ℓ

    private variable
      x : A
      y : B
      z : C
      cs xs ys : List C
      l₁ r₁ : Tree A
      l₂ r₂ : Tree B

    data AllOf : List C → REL (Tree A) (Tree B) ℓ… where
      leaf₋  : R⁻    x y → AllOf []     (leaf x) (leaf y)
      leafₐ  : R⁺ z  x y → AllOf [ z ]  (leaf x) (leaf y)
      node   : Split cs xs ys
             → AllOf xs l₁ l₂
             → AllOf ys r₁ r₂
             → AllOf cs (node l₁ r₁) (node l₂ r₂)

  All : REL A B ℓ → REL (Tree A) (Tree B) _
  All R = AllOf {r⁺ = 0ℓ}{C = ⊥} R (λ()) []

  allOf[]·map∈ : ∀ {R⁻ : REL A B ℓ}{R⁺ : C → REL A B c}{t : Tree A}
    → (f : ∀ {x} → x ∈ t → B)
    → (∀ {x} (p : x ∈ t) → R⁻ x (f p))
    → AllOf R⁻ R⁺ [] t (map∈ t f)
  allOf[]·map∈ {t = leaf x} f R-refl = leaf₋ (R-refl (here refl))
  allOf[]·map∈ {t = node t t₁} f R-refl = node []
    (allOf[]·map∈ (f ∘ left) (R-refl ∘ left))
    (allOf[]·map∈ (f ∘ right) (R-refl ∘ right))

  allOf[] : ∀ {R⁻ : Rel A a}{R⁺ : C → Rel A c}{t : Tree A}
    → Reflexive R⁻
    → AllOf R⁻ R⁺ [] t t
  allOf[] {R⁻ = R⁻}{R⁺ = R⁺}{t = t} R-refl = subst (AllOf R⁻ R⁺ [] t)
    (map-id (λ x → refl) _)
    (allOf[]·map∈ (λ {x} _ → x) λ _ → R-refl)
