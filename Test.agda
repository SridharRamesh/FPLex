{-# OPTIONS --safe --prop #-}
open import Agda.Builtin.Sigma
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

Type = Set
Type1 = Set1

data Squash {ℓ} (A : Set ℓ) : Prop ℓ where
  squash : A → Squash A

squash-elim : ∀ {ℓ₁ ℓ₂} (A : Set ℓ₁) (P : Prop ℓ₂) → (A → P) → Squash A → P
squash-elim A P f (squash x) = f x

isProp' : Type → Type
isProp' s = (s1 : s) → (s2 : s) → s1 ≡ s2

isProp : Type → Prop
isProp s = Squash (isProp' s)

_×_ : Type → Type → Type
A × B = Σ A (λ _ → B)

record Category : Type1 where
  field
    Ob : Type
    Hom : Ob → Ob → Type
    id : ∀ {A} → Hom A A
    _*_ : ∀ {A B C} → (Hom A B) → (Hom B C) → (Hom A C)
    leftUnit : ∀ {A B} (m : Hom A B) → id * m ≡ m
    rightUnit : ∀ {A B} (m : Hom A B) → m * id ≡ m
    assoc : ∀ {A B C D} (m : Hom A B) (n : Hom B C) (p : Hom C D) → (m * n) * p ≡ m * (n * p)
  dom : {d : Ob} {c : Ob} → Hom d c → Ob
  dom {d} {c} m = d
  cod : {d : Ob} {c : Ob} → Hom d c → Ob
  cod {d} {c} m = c
  areInverse : ∀ {A B} → Hom A B → Hom B A → Type
  areInverse m n = (m * n ≡ id) × (n * m ≡ id)
  Iso : Ob → Ob → Type
  Iso A B = Σ (Hom A B) (\m → Σ (Hom B A) (\n → areInverse {A} {B} m n))
  isoAsHom : ∀ {A B} → Iso A B → Hom A B
  isoAsHom (m , _) = m
  isIso : ∀ {A B} → Hom A B → Type
  isIso m = Σ _ (\n → areInverse m n)
  flipIso : ∀ {A B} {m : Hom A B} {n} → areInverse m n → areInverse n m
  flipIso (x , y) = (y , x)
  uniqueInverses : ∀ {A B} {m : Hom A B} {n1 n2} → areInverse m n1 → areInverse m n2 → n1 ≡ n2
  uniqueInverses {A} {B} {m} {n1} {n2} (mn1 , n1m) (mn2 , n2m) = 
    begin
    n1 
      ≡⟨ sym (leftUnit n1) ⟩
    id * n1
      ≡⟨ cong (\x → x * n1) (sym n2m) ⟩
    (n2 * m) * n1
      ≡⟨ assoc n2 m n1 ⟩
    n2 * (m * n1)
      ≡⟨ cong (\x → n2 * x) mn1 ⟩
    n2 * id
      ≡⟨ rightUnit n2 ⟩
    n2
    ∎
  -- isoIsProp : ∀ {A B m} → isProp (isIso {A} {B} m)

record CategoryWithTerminal : Type1 where
  open Category{{...}} public
  field
    {{category}} : Category
    terminal : Ob
    -- I'm not sure why I can't use ∀ {A} in the following:
    ! : {A : Ob} → Hom A terminal
    subTerminal : {A : Ob} → isProp (Hom A terminal)

record CategoryWithDisplay : Type1 where
  open CategoryWithTerminal{{...}} public
  field
    {{categoryWithTerminal}} : CategoryWithTerminal
    isDisplay : {A : Ob} {B : Ob} → Hom A B → Prop
    isosAreDisplay : ∀ {A B} → (m : Iso A B) → isDisplay {A} {B} (isoAsHom m)
    mapsToTerminalAreDisplay : ∀ {A} → isDisplay {A} {terminal} (!)
    displayComposition : ∀ {A B C d e} → isDisplay {A} {B} d → isDisplay {B} {C} e → isDisplay {A} {C} (d * e)
    -- Add the following conditions:
    -- Display maps are closed under pullback.

record LexCat : Type1 where
  open CategoryWithDisplay{{...}} public
  field
    {{categoryWithDisplay}} : CategoryWithDisplay
    -- Add the following conditions:
    -- Diagonal maps are display.
    -- Note the following consequence:
    -- All maps are display.


-- The following is, well, just test stuff.
record Test : Set1 where
  field
    carrier : Set
    foo : (c : carrier) → Set
    bar : (c : _) → foo c

record Test2 : Set1 where
  open Test{{...}} public
  field
    {{test}} : Test
    -- If "carrier" is replaced with an underscore in the following, we get an error.
    -- Even though the same definition of bar in Test worked fine.
    baz : (c : carrier) → foo c