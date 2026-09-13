
-- These instructions are from AgdaPad
{-
  Welcome to Agda! :-)

  If you are new to Agda, you could play The HoTT Game, a tutorial for learning
  Agda and homotopy type theory. You can start the game using the "Help" menu
  and then navigating to a file such as 1FundamentalGroup/Quest0.agda. You
  will also need to open the accompanying guide in your browser:
  https://thehottgameguide.readthedocs.io/

  This editor runs on agdapad.quasicoherent.io. Your Agda code is stored on
  this server and should be available when you revisit the same Agdapad session.
  However, absolutely no guarantees are made. You should make backups by
  downloading (see the clipboard icon in the lower right corner).

  C-c C-l          check file
  C-c C-SPC        check hole
  C-c C-,          display goal and context
  C-c C-c          split cases
  C-c C-r          fill in boilerplate from goal
  C-c C-d          display type of expression
  C-c C-v          evaluate expression (normally this is C-c C-n)
  C-c C-a          try to find proof automatically
  C-z              enable Vi keybindings
  C-x C-+          increase font size
  \bN \alpha \to   math symbols

  "C-c" means "<Ctrl key> + c". In case your browser is intercepting C-c,
  you can also use C-o. In case your browser in intercepting C-SPC, you can
  also use C-p. For pasting code into the Agdapad, see the clipboard
  icon in the lower right corner.

  In text mode, use <F10> to access the menu bar, not the mouse.
-}
module Discussion1 where

open import Agda.Primitive using () renaming (Set to Type)

open import Agda.Builtin.Bool     using (Bool; true; false)
open import Agda.Builtin.String   using (String)
  renaming (primStringEquality to infix 4 _=?_)
open import Agda.Builtin.List     using (List; _∷_) renaming ([] to ∅)
open import Agda.Builtin.Equality using (_≡_; refl)

-- Falsehood: a type with no constructors.
data ⊥ : Type where

infixr 5 _∪_
infixl 6 _∖_
infix  4 _≈α_ _∈_ _∉_
infixl 6 _·_
infixr 3 ƛ_⇒_
infix  7 _[_↔_] _[_↔_]ₙ

Var : Type
Var = String

-- Set-like notation backed by lists; duplicates are retained.
-- Full-width braces distinguish these from Agda's implicit arguments.
｛_｝ : {A : Type} → A → List A
｛ x ｝ = x ∷ ∅

｛_,_｝ : {A : Type} → A → A → List A
｛ x , y ｝ = x ∷ y ∷ ∅

_∪_ : {A : Type} → List A → List A → List A
∅        ∪ ys = ys
(x ∷ xs) ∪ ys = x ∷ (xs ∪ ys)

_∈_ : Var → List Var → Bool
x ∈ ∅ = false
x ∈ (y ∷ ys) with x =? y
... | true  = true
... | false = x ∈ ys

_∉_ : Var → List Var → Type
x ∉ xs = (x ∈ xs) ≡ false

-- Remove every name that belongs to ys.
_∖_ : List Var → List Var → List Var
∅        ∖ ys = ∅
(x ∷ xs) ∖ ys with x ∈ ys
... | true  = xs ∖ ys
... | false = x ∷ (xs ∖ ys)

---------------------------------------------------------

-- Unicode input in Agda mode: type the backslash sequence after each symbol.
--   ⟨ \langle   ⟩ \rangle   · \cdot      ƛ \Gl-      ⇒ \=>
--   ｛ \F{      ｝ \F}      ∅ \emptyset  ∷ \::
--   ∪ \cup      ∖ \setminus ∈ \in        ∉ \notin
--   → \->       ≡ \equiv   ∀ \forall    ⊥ \bot
--   λ \Gl       ≈ \approx  α \alpha     ↔ \<->      ₙ \_n
--   ₁ \_1       ₂ \_2      ′ \prime
--   ≔ \:=       ↝ \leadsto ⟶ \-->       β \beta
-- Use ƛ for term abstractions; λ is Agda's own lambda syntax.
-- Use full-width ｛ ｝ for the list notation; ordinary { } mark implicit arguments.

data Term : Type where
  ⟨_⟩ : Var → Term
  _·_ : Term → Term → Term
  ƛ_⇒_ : Var → Term → Term

-- Identity: λx.x.
example1 : Term
example1 = ƛ "x" ⇒ ⟨ "x" ⟩

-- Constant function: λx.λy.x.
example2 : Term
example2 = ƛ "x" ⇒ ƛ "y" ⇒ ⟨ "x" ⟩

-- Application: (λx.x) y. The name y is free.
example3 : Term
example3 = (ƛ "x" ⇒ ⟨ "x" ⟩) · ⟨ "y" ⟩

-- Self-application: λx.x x.
example4 : Term
example4 = ƛ "x" ⇒ ⟨ "x" ⟩ · ⟨ "x" ⟩

-- All variable names, including binders; repetitions are retained.
Vars : Term → List Var
Vars ⟨ x ⟩     = ｛ x ｝
Vars (e · f)   = Vars e ∪ Vars f
Vars (ƛ x ⇒ e) = ｛ x ｝ ∪ Vars e

-- Vars(x) = [x].
example5 : Vars ⟨ "x" ⟩ ≡ ｛ "x" ｝
example5 = refl

-- The binder and its occurrence are both included.
-- Vars(λx.x) = [x, x] (as a set: {x}).
example6 : Vars (ƛ "x" ⇒ ⟨ "x" ⟩) ≡ ｛ "x" , "x" ｝
example6 = refl

-- Both bound and free names are included, in traversal order.
-- Vars(λx.x y) = [x, x, y] (as a set: {x, y}).
example7 :
  Vars (ƛ "x" ⇒ ⟨ "x" ⟩ · ⟨ "y" ⟩) ≡ ｛ "x" , "x" ｝ ∪ ｛ "y" ｝
example7 = refl

-- Free variable names; repetitions are retained.
FV : Term → List Var
FV ⟨ x ⟩     = ｛ x ｝
FV (e · f)   = FV e ∪ FV f
FV (ƛ x ⇒ e) = FV e ∖ ｛ x ｝

-- The identity has no free variables.
-- FV(λx.x) = ∅.
example8 : FV (ƛ "x" ⇒ ⟨ "x" ⟩) ≡ ∅
example8 = refl

-- FV(λx.x y) = {y}.
example9 : FV (ƛ "x" ⇒ ⟨ "x" ⟩ · ⟨ "y" ⟩) ≡ ｛ "y" ｝
example9 = refl

-- The argument x is outside the binder's scope, so it remains free.
-- FV((λx.x) x) = {x}.
example10 : FV ((ƛ "x" ⇒ ⟨ "x" ⟩) · ⟨ "x" ⟩) ≡ ｛ "x" ｝
example10 = refl

_[_↔_]ₙ : Var → Var → Var → Var
z [ x ↔ y ]ₙ with z =? x | z =? y
... | true  | _     = y
... | false | true  = x
... | false | false = z

-- x[x ↔ y]ₙ = y.
example11 : "x" [ "x" ↔ "y" ]ₙ ≡ "y"
example11 = refl

-- y[x ↔ y]ₙ = x.
example12 : "y" [ "x" ↔ "y" ]ₙ ≡ "x"
example12 = refl

-- z[x ↔ y]ₙ = z.
example13 : "z" [ "x" ↔ "y" ]ₙ ≡ "z"
example13 = refl

-- e [ x ↔ y ] swaps both binders and occurrences.
_[_↔_] : Term → Var → Var → Term
⟨ z ⟩     [ x ↔ y ] = ⟨ z [ x ↔ y ]ₙ ⟩
(e · f)   [ x ↔ y ] = (e [ x ↔ y ]) · (f [ x ↔ y ])
(ƛ z ⇒ e) [ x ↔ y ] = ƛ (z [ x ↔ y ]ₙ) ⇒ (e [ x ↔ y ])

-- (x y)[x ↔ y] = y x.
example14 :
  (⟨ "x" ⟩ · ⟨ "y" ⟩) [ "x" ↔ "y" ] ≡ ⟨ "y" ⟩ · ⟨ "x" ⟩
example14 = refl

-- (λx.x)[x ↔ y] = λy.y.
example15 :
  (ƛ "x" ⇒ ⟨ "x" ⟩) [ "x" ↔ "y" ] ≡ (ƛ "y" ⇒ ⟨ "y" ⟩)
example15 = refl

-- (λx.x y)[x ↔ y] = λy.y x.
example16 :
  (ƛ "x" ⇒ ⟨ "x" ⟩ · ⟨ "y" ⟩) [ "x" ↔ "y" ]
    ≡ (ƛ "y" ⇒ ⟨ "y" ⟩ · ⟨ "x" ⟩)
example16 = refl

-- (λx.λy.x y)[x ↔ y] = λy.λx.y x.
example17 :
  (ƛ "x" ⇒ ƛ "y" ⇒ ⟨ "x" ⟩ · ⟨ "y" ⟩) [ "x" ↔ "y" ]
    ≡ (ƛ "y" ⇒ ƛ "x" ⇒ ⟨ "y" ⟩ · ⟨ "x" ⟩)
example17 = refl

-- The binder x changes to y; the unrelated free z is unchanged.
-- (λx.x z)[x ↔ y] = λy.y z.
example18 :
  (ƛ "x" ⇒ ⟨ "x" ⟩ · ⟨ "z" ⟩) [ "x" ↔ "y" ]
    ≡ (ƛ "y" ⇒ ⟨ "y" ⟩ · ⟨ "z" ⟩)
example18 = refl

-- The unrelated binder z and its bound occurrence are unchanged.
-- (λz.x z)[x ↔ y] = λz.y z.
example19 :
  (ƛ "z" ⇒ ⟨ "x" ⟩ · ⟨ "z" ⟩) [ "x" ↔ "y" ]
    ≡ (ƛ "z" ⇒ ⟨ "y" ⟩ · ⟨ "z" ⟩)
example19 = refl

-- ((λx.x y)[x ↔ y])[x ↔ y] = λx.x y.
example20 :
  ((ƛ "x" ⇒ ⟨ "x" ⟩ · ⟨ "y" ⟩) [ "x" ↔ "y" ]) [ "x" ↔ "y" ]
    ≡ (ƛ "x" ⇒ ⟨ "x" ⟩ · ⟨ "y" ⟩)
example20 = refl

-- ((λx.x y)[x ↔ y])[y ↔ z] = λz.z x.
example21 :
  ((ƛ "x" ⇒ ⟨ "x" ⟩ · ⟨ "y" ⟩) [ "x" ↔ "y" ]) [ "y" ↔ "z" ]
    ≡ (ƛ "z" ⇒ ⟨ "z" ⟩ · ⟨ "x" ⟩)
example21 = refl

-- ((λx.λz.(x y)(x z)(w y)(z w))[x ↔ y])[z ↔ w] = λy.λw.(y x)(y w)(z x)(w z).
example22 :
  ((ƛ "x" ⇒ ƛ "z" ⇒
      (⟨ "x" ⟩ · ⟨ "y" ⟩) · (⟨ "x" ⟩ · ⟨ "z" ⟩) ·
      (⟨ "w" ⟩ · ⟨ "y" ⟩) · (⟨ "z" ⟩ · ⟨ "w" ⟩))
    [ "x" ↔ "y" ]) [ "z" ↔ "w" ]
    ≡ (ƛ "y" ⇒ ƛ "w" ⇒
        (⟨ "y" ⟩ · ⟨ "x" ⟩) · (⟨ "y" ⟩ · ⟨ "w" ⟩) ·
        (⟨ "z" ⟩ · ⟨ "x" ⟩) · (⟨ "w" ⟩ · ⟨ "z" ⟩))
example22 = refl

data _≈α_ : Term → Term → Type where
  α-vareq : ∀ {x}

    --------------------  Var
    → ⟨ x ⟩ ≈α ⟨ x ⟩

  α-app : ∀ {e₁ e₂ f₁ f₂}
    → e₁ ≈α f₁
    → e₂ ≈α f₂
    ----------------------- App
    → e₁ · e₂ ≈α f₁ · f₂

  α-lam : ∀ {x y e f} (z : Var)
    → z ∉ (Vars (ƛ x ⇒ e) ∪ Vars (ƛ y ⇒ f))
    → e [ x ↔ z ] ≈α f [ y ↔ z ]
    -------------------------------- Abs
    → (ƛ x ⇒ e) ≈α (ƛ y ⇒ f)

-- A variable is alpha-equivalent to itself.
-- x ≈α x.
example23 : ⟨ "x" ⟩ ≈α ⟨ "x" ⟩
example23 = α-vareq

-- Distinct free variables are not alpha-equivalent.
-- ¬ (x ≈α y).
example24 : (⟨ "x" ⟩ ≈α ⟨ "y" ⟩) → ⊥
example24 ()

-- λx.x ≈α λy.y, using the common fresh name "z".
example25 : (ƛ "x" ⇒ ⟨ "x" ⟩) ≈α (ƛ "y" ⇒ ⟨ "y" ⟩)
example25 = α-lam "z" refl α-vareq

-- x y ≈α x y.
example26 : ⟨ "x" ⟩ · ⟨ "y" ⟩ ≈α ⟨ "x" ⟩ · ⟨ "y" ⟩
example26 = α-app α-vareq α-vareq

-- Non-example: the distinct free variables cannot be renamed.
-- ¬ (x y ≈α w z).
example27 : (⟨ "x" ⟩ · ⟨ "y" ⟩ ≈α ⟨ "w" ⟩ · ⟨ "z" ⟩) → ⊥
example27 (α-app () _)

-- λx.λy.x y ≈α λa.λb.a b: rename both binders.
example28 :
  (ƛ "x" ⇒ ƛ "y" ⇒ ⟨ "x" ⟩ · ⟨ "y" ⟩)
    ≈α (ƛ "a" ⇒ ƛ "b" ⇒ ⟨ "a" ⟩ · ⟨ "b" ⟩)
example28 =
  α-lam "u" refl
    (α-lam "v" refl
      (α-app α-vareq α-vareq))

-- Non-example: x is bound on the left but free on the right.
-- The hole requires ⟨ "z" ⟩ ≈α ⟨ "x" ⟩, which has no constructor.
-- Attempted: (λx.x) ≈α (λy.x) (false).
-- example29 : (ƛ "x" ⇒ ⟨ "x" ⟩) ≈α (ƛ "y" ⇒ ⟨ "x" ⟩)
-- example29 = α-lam "z" refl {!!}

-- Any proof of the claim in example29 would yield a contradiction.
-- ¬ ((λx.x) ≈α (λy.x)).
example30 : ((ƛ "x" ⇒ ⟨ "x" ⟩) ≈α (ƛ "y" ⇒ ⟨ "x" ⟩)) → ⊥
example30 (α-lam z fresh p) with "x" =? z
... | true with p | fresh
... | α-vareq | ()
example30 (α-lam z fresh p) | false with p | fresh
... | α-vareq | ()

-- Navier Stokes Lean
-- https://github.com/openai/NavierStokesAndEuler
