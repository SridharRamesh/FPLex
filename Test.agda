{-# OPTIONS --safe --no-prop #-}
open import Agda.Builtin.Sigma
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

Type = Set
Type1 = Set1

data TestType : Type where
  testConstructor : TestType

isContr : Type → Type
isContr T = Σ T (\t₁ → forall t₂ → t₁ ≡ t₂)

isProp : Type → Type
isProp T = (t₁ : T) → (t₂ : T) → t₁ ≡ t₂

_×_ : Type → Type → Type
A × B = Σ A (λ _ → B)

_and_ : Type → Type → Type
_and_ = _×_

areBijectionPair : ∀ {A B} → (A → B) → (B → A) → Type
areBijectionPair {A} {B} f g = ((a : A) → g(f(a)) ≡ a) and ((b : B) → f(g(b)) ≡ b)

isBijection : ∀ {A B} → (A → B) → Type
isBijection {A} {B} f = Σ (B → A) (\g → areBijectionPair f g)

--isBijectionToCondition : ∀ {A B} → (A → B) → (B → Type) → Type
--isBijectionToCondition

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
  {-
  isPullbackSquare : ∀ {TL TR BL BR} →
    (bottom : Hom BR BL) → 
    (right : Hom TR BR) → 
    (top : Hom TL TR) → 
    (left : Hom TL BL) → 
    Type
  isPullbackSquare {TL} {TR} {BL} {BR} bottom right top left =
    (source : Ob) → isBijection compositor where
      compositorDom = Hom source TL
      compositorCod = (b : Hom Source BL) → (r : Hom Source TR) → (b * bottom) ≡ (r * right)
      compositor : compositorDom → compositorCod
      compositor s = 
      -}

record CategoryWithTerminal : Type1 where
  field
    category : Category
  open Category category public
  field
    terminal : Ob
    -- I'm not sure why I can't use ∀ {A} in the following:
    ! : {A : Ob} → Hom A terminal
    subTerminal : {A : Ob} → isProp (Hom A terminal)

record CategoryWithDisplay : Type1 where
  field
    categoryWithTerminal : CategoryWithTerminal
  open CategoryWithTerminal categoryWithTerminal public
  field
    isDisplay : {A : Ob} {B : Ob} → Hom A B → Type
    isDisplayIsProp : ∀ {A B} (m : Hom A B) → isProp (isDisplay {A} {B} m)
    isosAreDisplay : ∀ {A B} (m : Iso A B) → isDisplay {A} {B} (isoAsHom m)
    mapsToTerminalAreDisplay : ∀ {A} → isDisplay {A} {terminal} (!)
    displayComposition : ∀ {A B C d e} → isDisplay {A} {B} d → isDisplay {B} {C} e → isDisplay {A} {C} (d * e)
    -- Add the following conditions:
    -- Display maps are closed under pullback.

record LexCat : Type1 where
  field
    categoryWithDisplay : CategoryWithDisplay
  open CategoryWithDisplay categoryWithDisplay public
  -- Add the following conditions:
  -- Diagonal maps are display.
  -- Note the following consequence:
  -- All maps are display.


-- The following is, well, just test stuff.

record Parent : Set1 where
  field
    carrier : Set
    foo : (c : carrier) → Set
    parentBar : (c : _) → foo c

record Child : Set1 where
  field
    parent : Parent
  open Parent parent public
  field
    parentBar : (c : _) → foo c

record Grandchild : Set1 where
  field
    child : Child
  open Child child public
  field
    x : carrier