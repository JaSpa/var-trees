module Syntax where

open import Axiom.Extensionality.Propositional
open import Data.List using (List; []; _∷_; [_])
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe as M using (Maybe; just; nothing; Is-nothing)
open import Data.Maybe.Relation.Unary.All using (just; nothing)
open import Data.Product using (Σ; Σ-syntax; ∃-syntax; _×_; proj₁; proj₂; -,_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function
open import Level renaming (suc to ℓsuc)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as Eq hiding ([_])
open import Relation.Unary using (Pred)

import Data.List.Membership.Propositional as L
import Data.Maybe.Properties as M
import Data.Maybe.Relation.Binary.Pointwise as M

open import Tree as T using (Tree; leaf; node; _∈_)
open T.Zip hiding (All)
open T.Relation

postulate
  fun-ext : ∀ {a b} → Extensionality a b
  fun-ext⦃⦄ : ∀ {a b} → ExtensionalityImplicit a b

infixr 7 _`→_
infix  8 _`×_

infix  5 λ[_]_ μ[_,_]_ `case_`zero⇒_`suc[_]⇒_
infixl 6 _⨟_
infix  7 _`,_
infixl 8 _·_
infix  9 `suc_

infix  4 _⊢_

data Mul : Set where
  lin unr : Mul

_⊔ᶜ_ : Mul → Mul → Mul
lin ⊔ᶜ lin = lin
_   ⊔ᶜ _   = unr

private variable
  ℓ : Level
  m m₁ m₂ : Mul

data 𝕋 : Set where
  ⋆     : 𝕋
  `ℕ    : 𝕋
  _`×_  : 𝕋 → 𝕋 → 𝕋
  _`→_  : 𝕋 → 𝕋 → 𝕋

record FV : Set where
  constructor var
  field
    ty : 𝕋
    ctxt : Mul

VarTree : Set
VarTree = Tree (Maybe FV)

unrContext : FV → FV
unrContext fv = record fv { ctxt = unr }

𝓥-unrContext : VarTree → VarTree
𝓥-unrContext 𝓥 = T.map 𝓥 $ M.map unrContext

presUnrCtxt : Mul → FV → FV
presUnrCtxt m fv = record fv { ctxt = FV.ctxt fv ⊔ᶜ m }

𝓥-presUnrCtxt : Mul → VarTree → VarTree
𝓥-presUnrCtxt m 𝓥 = T.map 𝓥 $ M.map $ presUnrCtxt m

presUnrCtxt·unr : presUnrCtxt unr ≗ unrContext
presUnrCtxt·unr (var ty lin) = refl
presUnrCtxt·unr (var ty unr) = refl

presUnrCtxt·lin : presUnrCtxt lin ≗ id
presUnrCtxt·lin (var ty lin) = refl
presUnrCtxt·lin (var ty unr) = refl

𝓥-presUnrCtxt·lin : 𝓥-presUnrCtxt lin ≗ id
𝓥-presUnrCtxt·lin = T.map-id λ x → trans (M.map-cong presUnrCtxt·lin x) (M.map-id x)

unrContext-identityˡ : ∀ m → presUnrCtxt m ∘ unrContext ≗ unrContext
unrContext-identityˡ m (var ty ctxt) = refl

unrContext-identityʳ : ∀ m → unrContext ∘ presUnrCtxt m ≗ unrContext
unrContext-identityʳ m (var ty ctxt) = refl

𝓥-unrContext-identityˡ : ∀ m → 𝓥-presUnrCtxt m ∘ 𝓥-unrContext ≗ 𝓥-unrContext
𝓥-unrContext-identityˡ m 𝓥 = let open Eq.≡-Reasoning in
  begin
    (𝓥-presUnrCtxt m ∘ 𝓥-unrContext) 𝓥
  ≡⟨ T.map-∘ 𝓥 ⟩
    T.map 𝓥 (M.map (presUnrCtxt m) ∘ M.map unrContext)
  ≡⟨ T.map-cong (sym ∘ M.map-∘) 𝓥 ⟩
    T.map 𝓥 (M.map (presUnrCtxt m ∘ unrContext))
  ≡⟨ T.map-cong (M.map-cong (unrContext-identityˡ m)) 𝓥 ⟩
    𝓥-unrContext 𝓥
  ∎

𝓥-unrContext-identityʳ : ∀ m → 𝓥-unrContext ∘ 𝓥-presUnrCtxt m ≗ 𝓥-unrContext
𝓥-unrContext-identityʳ m 𝓥 = let open Eq.≡-Reasoning in
  begin
    (𝓥-unrContext ∘ 𝓥-presUnrCtxt m) 𝓥
  ≡⟨ T.map-∘ 𝓥 ⟩
    T.map 𝓥 (M.map unrContext ∘ M.map (presUnrCtxt m))
  ≡⟨ T.map-cong (sym ∘ M.map-∘) 𝓥 ⟩
    T.map 𝓥 (M.map (unrContext ∘ presUnrCtxt m))
  ≡⟨ T.map-cong (M.map-cong (unrContext-identityʳ m)) 𝓥 ⟩
    𝓥-unrContext 𝓥
  ∎

private variable
  t t₁ t₂ u u₁ u₂ : 𝕋
  𝓤 𝓤′ 𝓥 𝓥′ 𝓥₁ 𝓥₂ 𝓤₁ 𝓤₂ : VarTree

pattern ∅        = leaf nothing
pattern free t m = just (var t m)

bindLin_∈_—→_ : List 𝕋 → Rel VarTree 0ℓ
bindLin ts ∈ 𝓤 —→ 𝓥 = T.Zip.AllOf _≡_ (λ t x y → x ≡ free t lin × y ≡ nothing) ts 𝓤 𝓥

data bindUnr`FV (t : 𝕋) : Rel (Maybe FV) 0ℓ where
  bind : bindUnr`FV t (just (var t m)) nothing
  skip : ∀ {x} → bindUnr`FV t x x

bindUnr_∈_—→_ : 𝕋 → Rel VarTree _
bindUnr t ∈ 𝓤 —→ 𝓥 = T.Zip.All (bindUnr`FV t) 𝓤 𝓥

data _⊢_ : VarTree → 𝕋 → Set where
  var
     -----------------------
    : leaf (free t lin) ⊢ t

  λ[_]_
    : bindLin [ t ] ∈ 𝓤 —→ 𝓥
    → 𝓤 ⊢ u
     -------------------------
    → 𝓥 ⊢ t `→ u

  μ[_,_]_
    : bindUnr t `→ u ∈ 𝓤 —→ 𝓥′
    → 𝓥-unrContext 𝓥′ ≡ 𝓥
    → 𝓤 ⊢ t `→ u
     --------------------------
    → 𝓥 ⊢ t `→ u

  _·_
    : 𝓤 ⊢ t `→ u
    → 𝓥 ⊢ t
     --------------
    → node 𝓤 𝓥 ⊢ u

  `unit
     -------
    : ∅ ⊢ ⋆

  _⨟_
    : 𝓤 ⊢ ⋆
    → 𝓥 ⊢ t
     --------------
    → node 𝓤 𝓥 ⊢ t

  `zero
     --------
    : ∅ ⊢ `ℕ

  `suc_
    : 𝓥 ⊢ `ℕ
     --------
    → 𝓥 ⊢ `ℕ

  `case_`zero⇒_`suc[_]⇒_
    : 𝓤 ⊢ `ℕ
    → 𝓥 ⊢ t
    → bindUnr `ℕ ∈ 𝓥′ —→ 𝓥
    → 𝓥′ ⊢ t
     -----------------------
    → node 𝓤 𝓥 ⊢ t

  _`,_
    : 𝓤 ⊢ t
    → 𝓥 ⊢ u
     -------------------
    → node 𝓤 𝓥 ⊢ t `× u

  `let[_]=_`in_
    : bindLin t₁ ∷ [ t₂ ] ∈ 𝓥′ —→ 𝓥
    → 𝓤 ⊢ t₁ `× t₂
    → 𝓥′ ⊢ u
     -------------------------------
    → node 𝓤 𝓥 ⊢ u

Empty : Pred VarTree _
Empty = All Is-nothing

Closed : Pred (𝓥 ⊢ t) _
Closed {𝓥 = 𝓥} _ = Empty 𝓥

presUnrCtxt-preserves-Empty : ∀ m → Empty 𝓥 → Empty (𝓥-presUnrCtxt m 𝓥)
presUnrCtxt-preserves-Empty _ ∅ = ∅
presUnrCtxt-preserves-Empty m (node l r) =
  node (presUnrCtxt-preserves-Empty m l)
       (presUnrCtxt-preserves-Empty m r)

presUnrCtxt-Empty-⇒-Empty : ∀ m → Empty (𝓥-presUnrCtxt m 𝓥) → Empty 𝓥
presUnrCtxt-Empty-⇒-Empty {𝓥 = leaf nothing} m ∅ = ∅
presUnrCtxt-Empty-⇒-Empty {𝓥 = leaf (just x)} m (leaf (just ()))
presUnrCtxt-Empty-⇒-Empty {𝓥 = node 𝓥ₗ 𝓥ᵣ} m (node eₗ eᵣ) =
  node (presUnrCtxt-Empty-⇒-Empty m eₗ) (presUnrCtxt-Empty-⇒-Empty m eᵣ)

map·Empty≡Empty : ∀ {f} → Empty (T.map 𝓥 (M.map f)) → Empty 𝓥
map·Empty≡Empty {𝓥 = leaf (just x)} (leaf (just ()))
map·Empty≡Empty {𝓥 = leaf nothing} (leaf x) = leaf nothing
map·Empty≡Empty {𝓥 = node 𝓥ₗ 𝓥ᵣ} (node eₗ eᵣ) = node (map·Empty≡Empty eₗ) (map·Empty≡Empty eᵣ)

record SubTerm (t : 𝕋) : Set where
  constructor [↦_]
  field
    {freeVars} : VarTree
    subTerm : freeVars ⊢ t

open SubTerm

Sub : VarTree → Set _
Sub 𝓥 = ∀ {v} → just v ∈ 𝓥 → SubTerm (FV.ty v)

id-sub : (𝓥 : VarTree) → Sub 𝓥
id-sub _ p = [↦ var ]

Sub→Bind : Sub 𝓥 → ∀ {x} → x ∈ 𝓥 → VarTree
Sub→Bind σ {nothing}    p = leaf nothing
Sub→Bind σ {free ty m}  p = 𝓥-presUnrCtxt m $ freeVars $ σ p

bind∈-cong-→Bind-dist : (f : ∀ {x} → x ∈ 𝓤 → x ∈ 𝓥) (σ : Sub 𝓥) →
  T.bind∈ 𝓤 (Sub→Bind (σ ∘ f)) ≡ T.bind∈ 𝓤 (Sub→Bind σ ∘ f)
bind∈-cong-→Bind-dist {𝓤 = 𝓤} f σ = T.bind∈-cong 𝓤 λ where
  {just x}   _ → refl
  {nothing}  _ → refl

𝓥[_] : Sub 𝓥 → VarTree
𝓥[_] {𝓥 = 𝓥} σ = T.bind∈ 𝓥 (Sub→Bind σ)

id-sub-pres-𝓥 : 𝓥[ id-sub 𝓥 ] ≡ 𝓥
id-sub-pres-𝓥 {𝓥 = 𝓥} = let open Eq.≡-Reasoning in
  begin
    𝓥[ id-sub 𝓥 ]
  ≡⟨⟩
    T.bind∈ 𝓥 (Sub→Bind (λ p → [↦ var ]))
  ≡⟨ T.bind∈-cong 𝓥 (λ{ {free ty lin} p → refl ; {free ty unr} p → refl ; {nothing} p → refl }) ⟩
    T.map 𝓥 id
  ≡⟨ T.map-id (λ _ → refl) _ ⟩
    𝓥
  ∎

belowUnrContext : Sub (𝓥-unrContext 𝓥) → Sub 𝓥
belowUnrContext σ = σ ∘ T.map-pres-∈

belowUnrContext-elim′ : {fv : FV} (σ : Sub (𝓥-unrContext 𝓥)) (p : just fv ∈ 𝓥)
  → 𝓥-unrContext (𝓥-presUnrCtxt (FV.ctxt fv) (freeVars (belowUnrContext σ p)))
      ≡
    𝓥-presUnrCtxt unr (freeVars (σ (T.map-pres-∈ p)))
belowUnrContext-elim′ {fv = var _ c} σ p =
  let open Eq.≡-Reasoning in
  let baseTree = freeVars (belowUnrContext σ p) in
  begin
    𝓥-unrContext (𝓥-presUnrCtxt c baseTree)
  ≡⟨ T.map-∘ (freeVars (belowUnrContext σ p)) ⟩
    T.map baseTree (M.map unrContext ∘ M.map (presUnrCtxt c))
  ≡⟨ T.map-cong (sym ∘ M.map-∘) baseTree ⟩
    T.map baseTree (M.map (unrContext ∘ presUnrCtxt c))
  ≡⟨ T.map-cong (M.map-cong (unrContext-identityʳ c)) baseTree ⟩
    T.map baseTree (M.map unrContext)
  ≡⟨⟩
    𝓥-unrContext baseTree
  ≡⟨ T.map-cong (M.map-cong (sym ∘ presUnrCtxt·unr)) baseTree ⟩
    𝓥-presUnrCtxt unr (freeVars (σ (T.map-pres-∈ p)))
  ∎

belowUnrContext-elim : ∀ 𝓥 (σ : Sub (𝓥-unrContext 𝓥)) → 𝓥-unrContext 𝓥[ belowUnrContext {𝓥 = 𝓥} σ ] ≡ 𝓥[ σ ]
belowUnrContext-elim 𝓥 σ = let open Eq.≡-Reasoning in
  begin
    𝓥-unrContext 𝓥[ belowUnrContext {𝓥 = 𝓥} σ ]
  ≡⟨ T.map-bind∈-compose 𝓥 ⟩
    T.bind∈ 𝓥 (λ p →
      T.map (Sub→Bind (belowUnrContext σ) p) (M.map unrContext))
  ≡⟨ T.bind∈-cong 𝓥 (λ{ {just fv} p → belowUnrContext-elim′ σ p ; {nothing} p → refl }) ⟩
    T.bind∈ 𝓥 (Sub→Bind σ ∘ T.map-pres-∈)
  ≡⟨ sym (T.bind∈-map-compose 𝓥) ⟩
    𝓥[ σ ]
  ∎

-- Construct a substitution from an unr binding.
bindUnr→Sub : bindUnr t ∈ 𝓥 —→ 𝓥′ → 𝓤 ⊢ t → Sub 𝓥
bindUnr→Sub (leaf₋ bind)  ⊢t (here refl) = [↦ ⊢t ]
bindUnr→Sub (leaf₋ skip)  ⊢t (here refl) = [↦ var ]
bindUnr→Sub (node [] l r) ⊢t (left p)  = bindUnr→Sub l ⊢t p
bindUnr→Sub (node [] l r) ⊢t (right p) = bindUnr→Sub r ⊢t p

-- Extend a substitution using an unr binding.
ext-bindUnr : Sub 𝓥 → bindUnr t ∈ 𝓤 —→ 𝓥 → Sub 𝓤
ext-bindUnr σ (leaf₋ bind) (here refl) = [↦ var ]
ext-bindUnr σ (leaf₋ skip) (here refl) = σ (here refl)
ext-bindUnr σ (node [] l r) (left p) = ext-bindUnr (σ ∘ left) l p
ext-bindUnr σ (node [] l r) (right p) = ext-bindUnr (σ ∘ right) r p

-- Apply a substitution to an unr binding.
sub·bindUnr : (σ : Sub 𝓥) (b : bindUnr t ∈ 𝓤 —→ 𝓥) →
  bindUnr t ∈ 𝓥[ ext-bindUnr σ b ] —→ 𝓥[ σ ]
sub·bindUnr σ (leaf₋ (bind {m = lin})) = leaf₋ bind
sub·bindUnr σ (leaf₋ (bind {m = unr})) = leaf₋ bind
sub·bindUnr σ (leaf₋ {x = nothing} skip) = leaf₋ skip
sub·bindUnr σ (leaf₋ {x = free t c} skip) = allOf[] λ where
  {just x} → skip
  {nothing} → skip
sub·bindUnr {t = t}{𝓤 = node 𝓤ₗ 𝓤ᵣ} σ (node [] l r) = node []
  (subst₂ (bindUnr t ∈_—→_)
    (T.bind∈-cong 𝓤ₗ λ{ {just x} p → refl ; {nothing} p → refl })
    (bind∈-cong-→Bind-dist left σ)
    (sub·bindUnr (σ ∘ left) l))
  (subst₂ (bindUnr t ∈_—→_)
    (T.bind∈-cong 𝓤ᵣ λ{ {just x} p → refl ; {nothing} p → refl })
    (bind∈-cong-→Bind-dist right σ)
    (sub·bindUnr (σ ∘ right) r))

bindUnr→Sub-distˡ : {M : 𝓥 ⊢ t}
  → (l : bindUnr t ∈ 𝓤₁ —→ 𝓤₂) (r : bindUnr t ∈ 𝓥₁ —→ 𝓥₂)
  → T.bind∈ 𝓤₁ (Sub→Bind (bindUnr→Sub l M))
      ≡
    T.bind∈ 𝓤₁ (Sub→Bind (bindUnr→Sub (node [] l r) M) ∘ left)
bindUnr→Sub-distˡ (leaf₋ bind) r = refl
bindUnr→Sub-distˡ (leaf₋ {just x}  skip) r = refl
bindUnr→Sub-distˡ (leaf₋ {nothing} skip) r = refl
bindUnr→Sub-distˡ {𝓤₁ = node 𝓤ₗ 𝓤ᵣ} (node [] l r) _ = cong₂ node
  (T.bind∈-cong 𝓤ₗ λ{ {just x} p → refl ; {nothing} p → refl })
  (T.bind∈-cong 𝓤ᵣ λ{ {just x} p → refl ; {nothing} p → refl })

bindUnr→Sub-distʳ : {M : 𝓥 ⊢ t}
  → (l : bindUnr t ∈ 𝓤₁ —→ 𝓤₂) (r : bindUnr t ∈ 𝓥₁ —→ 𝓥₂)
  → T.bind∈ 𝓥₁ (Sub→Bind (bindUnr→Sub r M))
      ≡
    T.bind∈ 𝓥₁ (Sub→Bind (bindUnr→Sub (node [] l r) M) ∘ right)
bindUnr→Sub-distʳ l (leaf₋ bind) = refl
bindUnr→Sub-distʳ l (leaf₋ {just x} skip) = refl
bindUnr→Sub-distʳ l (leaf₋ {nothing} skip) = refl
bindUnr→Sub-distʳ {𝓥₁ = node 𝓥ₗ 𝓥ᵣ} _ (node [] l r) = cong₂ node
  (T.bind∈-cong 𝓥ₗ λ{ {just x} p → refl ; {nothing} p → refl })
  (T.bind∈-cong 𝓥ᵣ λ{ {just x} p → refl ; {nothing} p → refl })

closing-bindUnr : (b : bindUnr t ∈ 𝓥 —→ 𝓥′)
  → Empty 𝓥′
  → (M : 𝓤 ⊢ t)
  → Closed M
  → Empty 𝓥[ bindUnr→Sub b M ]
closing-bindUnr (leaf₋ (bind {m = m})) ∅ _ cM = presUnrCtxt-preserves-Empty m cM
closing-bindUnr (leaf₋ skip) ∅ _ cM = ∅
closing-bindUnr (node [] bl br) (node el er) M cM = node
  (subst Empty (bindUnr→Sub-distˡ bl br) (closing-bindUnr bl el M cM))
  (subst Empty (bindUnr→Sub-distʳ bl br) (closing-bindUnr br er M cM))

-- Build a substitution for a linear binder.
bindLin→Sub : ∀ {ts} → bindLin ts ∈ 𝓥 —→ 𝓥′ → (∀ {t} → t L.∈ ts → SubTerm t) → Sub 𝓥
bindLin→Sub (leaf₋ x) f (here refl) = [↦ var ]
bindLin→Sub (leafₐ (refl , _)) f (here refl) = f (here refl)
bindLin→Sub (node s l r) f (left p) = bindLin→Sub l (f ∘ ∈·splitˡ⇒∈ s) p
bindLin→Sub (node s l r) f (right p) = bindLin→Sub r (f ∘ ∈·splitʳ⇒∈ s) p

-- Extend a substitution to work under a linear binder.
ext-bindLin : ∀ {ts} → Sub 𝓥 → bindLin ts ∈ 𝓤 —→ 𝓥 → Sub 𝓤
ext-bindLin σ (leaf₋ refl) = σ
ext-bindLin σ (leafₐ x)    = id-sub _
ext-bindLin σ (node s l r) (left p)  = ext-bindLin (σ ∘ left) l p
ext-bindLin σ (node s l r) (right p) = ext-bindLin (σ ∘ right) r p

-- Apply a substitution to a lin binder. (?)
sub·bindLin : ∀ {ts} (σ : Sub 𝓥) (b : bindLin ts ∈ 𝓤 —→ 𝓥) →
  bindLin ts ∈ 𝓥[ ext-bindLin σ b ] —→ 𝓥[ σ ] 
sub·bindLin σ (leaf₋ refl) = allOf[] refl
sub·bindLin σ (leafₐ (refl , refl)) = leafₐ (refl , refl)
sub·bindLin {𝓤 = node 𝓤ₗ 𝓤ᵣ} σ (node s l r) = node s
  (subst₂ (bindLin _ ∈_—→_)
    (T.bind∈-cong 𝓤ₗ λ{ {just x} p → refl ; {nothing} p → refl })
    (bind∈-cong-→Bind-dist left σ)
    (sub·bindLin (σ ∘ left) l))
  (subst₂ (bindLin _ ∈_—→_)
    (T.bind∈-cong 𝓤ᵣ λ{ {just x} p → refl ; {nothing} p → refl })
    (bind∈-cong-→Bind-dist right σ)
    (sub·bindLin (σ ∘ right) r))

bindLin¹-sub : 𝓥 ⊢ t → ∀ {u} → u L.∈ [ t ] → SubTerm u
bindLin¹-sub M (here refl) = [↦ M ]

bindLin²-sub : 𝓥₁ ⊢ t₁ → 𝓥₂ ⊢ t₂ → ∀ {u} → u L.∈ t₁ ∷ [ t₂ ] → SubTerm u
bindLin²-sub M N (here refl) = [↦ M ]
bindLin²-sub M N (there (here refl)) = [↦ N ]

bindLin¹→Sub : bindLin [ t ] ∈ 𝓥 —→ 𝓥′ → 𝓤 ⊢ t → Sub 𝓥
bindLin¹→Sub b = bindLin→Sub b ∘ bindLin¹-sub

bindLin²→Sub : bindLin t ∷ [ u ] ∈ 𝓥 —→ 𝓥′ → 𝓤₁ ⊢ t → 𝓤₂ ⊢ u → Sub 𝓥
bindLin²→Sub b M N = bindLin→Sub b $ bindLin²-sub M N

bindLin→Sub-distˡ : ∀ {ts xs ys}{f : ∀ {t} → t L.∈ ts → SubTerm t}
  (s : Split ts xs ys) (l : bindLin xs ∈ 𝓤₁ —→ 𝓤₂) (r : bindLin ys ∈ 𝓥₁ —→ 𝓥₂) →
  T.bind∈ 𝓤₁ (Sub→Bind (bindLin→Sub l (f ∘ ∈·splitˡ⇒∈ s)))
    ≡
  T.bind∈ 𝓤₁ (Sub→Bind (bindLin→Sub (node s l r) f) ∘ left)
bindLin→Sub-distˡ s (leaf₋ {just x} refl) r = refl
bindLin→Sub-distˡ s (leaf₋ {nothing} refl) r = refl
bindLin→Sub-distˡ s (leafₐ (refl , _)) r = refl
bindLin→Sub-distˡ {𝓤₁ = node 𝓤ₗ 𝓤ᵣ} s (node s′ l r) _ = cong₂ node
  (T.bind∈-cong 𝓤ₗ λ{ {just x} p → refl ; {nothing} p → refl })
  (T.bind∈-cong 𝓤ᵣ λ{ {just x} p → refl ; {nothing} p → refl })

bindLin→Sub-distʳ : ∀ {ts xs ys}{f : ∀ {t} → t L.∈ ts → SubTerm t}
  (s : Split ts xs ys) (l : bindLin xs ∈ 𝓤₁ —→ 𝓤₂) (r : bindLin ys ∈ 𝓥₁ —→ 𝓥₂) →
  T.bind∈ 𝓥₁ (Sub→Bind (bindLin→Sub r (f ∘ ∈·splitʳ⇒∈ s)))
    ≡
  T.bind∈ 𝓥₁ (Sub→Bind (bindLin→Sub (node s l r) f) ∘ right)
bindLin→Sub-distʳ s l (leaf₋ {just x} refl) = refl
bindLin→Sub-distʳ s l (leaf₋ {nothing} refl) = refl
bindLin→Sub-distʳ s l (leafₐ (refl , _)) = refl
bindLin→Sub-distʳ {𝓥₁ = node 𝓥ₗ 𝓥ᵣ} s _ (node s′ l r) = cong₂ node
  (T.bind∈-cong 𝓥ₗ λ{ {just x} p → refl ; {nothing} p → refl })
  (T.bind∈-cong 𝓥ᵣ λ{ {just x} p → refl ; {nothing} p → refl })

closing-bindLin : ∀ {ts} (b : bindLin ts ∈ 𝓥 —→ 𝓥′)
  → Empty 𝓥′
  → (f : ∀ {t} → t L.∈ ts → SubTerm t)
  → (g : ∀ {t} → (p : t L.∈ ts) → Closed (subTerm (f p)))
  → Empty 𝓥[ bindLin→Sub b f ]
closing-bindLin (leaf₋ refl) ∅ f g = ∅
closing-bindLin (leafₐ (refl , _)) ∅ f g with f (here refl) | g (here refl)
... | s | cs = subst Empty (sym $ 𝓥-presUnrCtxt·lin _) cs
closing-bindLin (node s bl br) (node el er) f g = node
  (subst Empty (bindLin→Sub-distˡ s bl br) (closing-bindLin bl el (f ∘ ∈·splitˡ⇒∈ s) (g ∘ ∈·splitˡ⇒∈ s)))
  (subst Empty (bindLin→Sub-distʳ s bl br) (closing-bindLin br er (f ∘ ∈·splitʳ⇒∈ s) (g ∘ ∈·splitʳ⇒∈ s)))

closing-bindLin¹ : (b : bindLin [ t ] ∈ 𝓥 —→ 𝓥′)
  → Empty 𝓥′
  → (M : 𝓤 ⊢ t)
  → Closed M
  → Empty 𝓥[ bindLin¹→Sub b M ]
closing-bindLin¹ b e M cM = closing-bindLin b e (bindLin¹-sub M) λ{ (here refl) → cM }

sub : (σ : Sub 𝓥) → 𝓥 ⊢ t → 𝓥[ σ ] ⊢ t
subˡ : (σ : Sub (node 𝓥₁ 𝓥₂)) → 𝓥₁ ⊢ t → T.bind∈ 𝓥₁ (Sub→Bind σ ∘ left) ⊢ t
subʳ : (σ : Sub (node 𝓥₁ 𝓥₂)) → 𝓥₂ ⊢ t → T.bind∈ 𝓥₂ (Sub→Bind σ ∘ right) ⊢ t

subˡ σ = subst (_⊢ _) (bind∈-cong-→Bind-dist left σ) ∘ sub (σ ∘ left)
subʳ σ = subst (_⊢ _) (bind∈-cong-→Bind-dist right σ) ∘ sub (σ ∘ right)

sub {t = t} σ var = subst (_⊢ t) (sym $ 𝓥-presUnrCtxt·lin _) (subTerm (σ (here refl)))
sub σ (λ[ b ] M) =
  λ[ sub·bindLin σ b ]
    sub (ext-bindLin σ b) M
sub σ (μ[_,_]_ {𝓥′ = 𝓥′} b refl M) =
  μ[ sub·bindUnr (belowUnrContext σ) b , belowUnrContext-elim 𝓥′ σ ]
    sub (ext-bindUnr (belowUnrContext σ) b) M
sub σ (M · N) = subˡ σ M · subʳ σ N
sub σ `unit = `unit
sub σ (M ⨟ N) = subˡ σ M ⨟ subʳ σ N
sub σ `zero = `zero
sub σ (`suc M) = `suc (sub σ M)
sub σ (`case M `zero⇒ N₁ `suc[ b ]⇒ N₂) =
  let b′ = subst
             (bindUnr `ℕ ∈ 𝓥[ ext-bindUnr (σ ∘ right) b ] —→_)
             (bind∈-cong-→Bind-dist right σ)
             (sub·bindUnr (σ ∘ right) b)
  in
  `case subˡ σ M
    `zero⇒ subʳ σ N₁
    `suc[ b′ ]⇒ sub (ext-bindUnr (σ ∘ right) b) N₂
sub σ (M `, N) = subˡ σ M `, subʳ σ N
sub σ (`let[ b ]= M `in N) =
  let b′ = subst
             (bindLin _ ∈ 𝓥[ ext-bindLin (σ ∘ right) b ] —→_)
             (bind∈-cong-→Bind-dist right σ)
             (sub·bindLin (σ ∘ right) b)
  in
  `let[ b′ ]= subˡ σ M
    `in sub (ext-bindLin (σ ∘ right) b) N

data Value : 𝓥 ⊢ t → Set where
  V-λ : ∀ {b : bindLin [ t ] ∈ 𝓤 —→ 𝓥}{M : 𝓤 ⊢ u}
    → Empty 𝓥
    → Value (λ[ b ] M)
  V-unit : Value `unit
  V-zero : Value `zero
  V-suc  : ∀ {V : 𝓥 ⊢ `ℕ} → Value V → Value (`suc V)
  V-× : ∀ {V₁ : 𝓤 ⊢ t}{V₂ : 𝓥 ⊢ u} → Value V₁ → Value V₂ → Value (V₁ `, V₂)

valueTerm : ∀ {V : 𝓥 ⊢ t} → Value V → 𝓥 ⊢ t
valueTerm {V = V} _ = V

Value⇒Closed : {V : 𝓥 ⊢ t} → Value V → Closed V
Value⇒Closed V-unit = leaf nothing
Value⇒Closed V-zero = leaf nothing
Value⇒Closed (V-suc v) = Value⇒Closed v
Value⇒Closed (V-λ c) = c
Value⇒Closed (V-× v₁ v₂) = node (Value⇒Closed v₁) (Value⇒Closed v₂)


infix 3 _—→_

data _—→_ : 𝓤 ⊢ t → 𝓥 ⊢ t → Set where
  ξ-·₁ : {M₁ : 𝓤₁ ⊢ t `→ u}{M₂ : 𝓤₂ ⊢ t `→ u}{N : 𝓥 ⊢ t}
    → M₁ —→ M₂
     ------------------
    → M₁ · N —→ M₂ · N

  ξ-·₂ : {M : 𝓤 ⊢ t `→ u}{N₁ : 𝓥₁ ⊢ t}{N₂ : 𝓥₂ ⊢ t}
    → Value M
    → N₁ —→ N₂
     ------------------
    → M · N₁ —→ M · N₂

  β-λ : {M : 𝓤 ⊢ u}{V : 𝓥 ⊢ t}
    → (b : bindLin [ t ] ∈ 𝓤 —→ 𝓤′)
    → Value V
     --------------------------------------------
    → (λ[ b ] M) · V —→ sub (bindLin¹→Sub b V) M

  β-μ : {M : 𝓤 ⊢ t `→ u}
    → (b : bindUnr t `→ u ∈ 𝓤 —→ 𝓥′)
    → (𝓥-unr : 𝓥-unrContext 𝓥′ ≡ 𝓥)
     --------------------------------------------------------------
    → μ[ b , 𝓥-unr ] M —→ sub (bindUnr→Sub b (μ[ b , 𝓥-unr ] M)) M

  ξ-⨟ : {M₁ : 𝓤₁ ⊢ ⋆}{M₂ : 𝓤₂ ⊢ ⋆}{N : 𝓥 ⊢ t}
    → M₁ —→ M₂
     ------------------
    → M₁ ⨟ N —→ M₂ ⨟ N

  β-⋆ : ∀ {M : 𝓥 ⊢ t}
     ----------------
    → `unit ⨟ M —→ M

  ξ-suc : {M : 𝓥₁ ⊢ `ℕ}{N : 𝓥₂ ⊢ `ℕ}
    → M —→ N
     ------------------
    → `suc M —→ `suc N

  ξ-case : {M₁ : 𝓤₁ ⊢ `ℕ}{M₂ : 𝓤₂ ⊢ `ℕ}{N₁ : 𝓥 ⊢ t}{N₂ : 𝓥′ ⊢ t}
    → (b : bindUnr `ℕ ∈ 𝓥′ —→ 𝓥)
    → M₁ —→ M₂
    → `case M₁ `zero⇒ N₁ `suc[ b ]⇒ N₂ —→
      `case M₂ `zero⇒ N₁ `suc[ b ]⇒ N₂

  β-zero : ∀ {b}{M : 𝓤 ⊢ t}{N : 𝓥 ⊢ t}
    → `case `zero `zero⇒ M `suc[ b ]⇒ N —→ M

  β-suc : ∀ {V : 𝓤 ⊢ `ℕ}{M : 𝓥₁ ⊢ t}{N : 𝓥₂ ⊢ t}
    → (b : bindUnr `ℕ ∈ 𝓥₂ —→ 𝓥₁)
    → Value V
     ---------------------------------------------------------------
    → `case `suc V `zero⇒ M `suc[ b ]⇒ N —→ sub (bindUnr→Sub b V) N

  ξ-×₁ : {M₁ : 𝓤₁ ⊢ t}{M₂ : 𝓤₂ ⊢ t}{N : 𝓥 ⊢ u}
    → M₁ —→ M₂
     --------------------
    → M₁ `, N —→ M₂ `, N

  ξ-×₂ : {M : 𝓤 ⊢ t}{N₁ : 𝓥₁ ⊢ u}{N₂ : 𝓥₂ ⊢ u}
    → Value M
    → N₁ —→ N₂
     --------------------
    → M `, N₁ —→ M `, N₂

  ξ-let : {M₁ : 𝓤₁ ⊢ t₁ `× t₂}{M₂ : 𝓤₂ ⊢ t₁ `× t₂}{N : 𝓥′ ⊢ u}
    → (b : bindLin t₁ ∷ [ t₂ ] ∈ 𝓥′ —→ 𝓥)
    → M₁ —→ M₂
    → `let[ b ]= M₁ `in N —→ `let[ b ]= M₂ `in N

  β-× : {V₁ : 𝓤₁ ⊢ t₁}{V₂ : 𝓤₂ ⊢ t₂}{M : 𝓥′ ⊢ u}
    → (b : bindLin t₁ ∷ [ t₂ ] ∈ 𝓥′ —→ 𝓥)
    → Value V₁
    → Value V₂
     -----------------------------------------------------------
    → `let[ b ]= V₁ `, V₂ `in M —→ sub (bindLin²→Sub b V₁ V₂) M

Closed—→Closed : {M : 𝓤 ⊢ t}{N : 𝓥 ⊢ t} → M —→ N → Closed M → Closed N
Closed—→Closed (ξ-·₁ s) (node cl cr) = node (Closed—→Closed s cl) cr
Closed—→Closed (ξ-·₂ v s) (node cl cr) = node cl (Closed—→Closed s cr)
Closed—→Closed (β-λ b v) (node cl cr) =
  closing-bindLin b cl (bindLin¹-sub _) λ where
    (here refl) → Value⇒Closed v
Closed—→Closed (β-μ {M = M} b refl) cM =
  closing-bindUnr b
    (map·Empty≡Empty cM)
    (μ[ b , refl ] M) cM
Closed—→Closed (ξ-⨟ s) (node cl cr) = node (Closed—→Closed s cl) cr
Closed—→Closed β-⋆ (node cl cr) = cr
Closed—→Closed (ξ-suc s) c = Closed—→Closed s c
Closed—→Closed (ξ-case b s) (node cl cr) = node (Closed—→Closed s cl) cr
Closed—→Closed β-zero (node cl cr) = cr
Closed—→Closed (β-suc b v) (node cl cr) = closing-bindUnr b cr (valueTerm v) (Value⇒Closed v)
Closed—→Closed (ξ-×₁ s) (node cl cr) = node (Closed—→Closed s cl) cr
Closed—→Closed (ξ-×₂ v s) (node cl cr) = node cl (Closed—→Closed s cr)
Closed—→Closed (ξ-let b s) (node cl cr) = node (Closed—→Closed s cl) cr
Closed—→Closed (β-× b v₁ v₂) (node cl cr) =
  closing-bindLin b cr (bindLin²-sub _ _) λ where
    (here refl) → Value⇒Closed v₁
    (there (here refl)) → Value⇒Closed v₂

progress : (M : 𝓥 ⊢ t) → Closed M → (∃[ 𝓥′ ] Σ[ M′ ∈ 𝓥′ ⊢ t ] M —→ M′) ⊎ Value M
progress var (leaf (just ()))
progress (λ[ b ] M)        c = inj₂ (V-λ c)
progress (μ[ b , refl ] M) c = inj₁ (-, -, β-μ b refl)
progress (M · N) (node cM cN) with progress M cM
... | inj₁ (_ , _ , M→) = inj₁ (-, -, ξ-·₁ M→)
... | inj₂ (V-λ c) with progress N cN
... | inj₁ (_ , _ , N→) = inj₁ (-, -, ξ-·₂ (V-λ c) N→)
... | inj₂ VN = inj₁ (-, -, β-λ _ VN)
progress `unit c = inj₂ V-unit
progress (M ⨟ N) (node cM cN) with progress M cM
... | inj₁ (_ , _ , M→) = inj₁ (-, -, ξ-⨟ M→)
... | inj₂ V-unit = inj₁ (-, -, β-⋆)
progress `zero c = inj₂ V-zero
progress (`suc M) cM with progress M cM
... | inj₁ (_ , _ , M→) = inj₁ (-, -, ξ-suc M→)
... | inj₂ V = inj₂ (V-suc V)
progress (`case M `zero⇒ N₁ `suc[ b ]⇒ N₂) (node cM cN) with progress M cM
... | inj₁ (_ , _ , M→) = inj₁ (-, -, ξ-case b M→)
... | inj₂ V-zero       = inj₁ (-, -, β-zero)
... | inj₂ (V-suc V)    = inj₁ (-, -, β-suc b V)
progress (M `, N) (node cM cN) with progress M cM
... | inj₁ (_ , _ , M→) = inj₁ (-, -, ξ-×₁ M→)
... | inj₂ VM with progress N cN
... | inj₁ (_ , _ , N→) = inj₁ (-, -, ξ-×₂ VM N→)
... | inj₂ VN           = inj₂ (V-× VM VN)
progress (`let[ b ]= M `in N) (node cM cN) with progress M cM
... | inj₁ (_ , _ , M→) = inj₁ (-, -, ξ-let b M→)
... | inj₂ (V-× V₁ V₂)  = inj₁ (-, -, β-× b V₁ V₂)
