def algebraic (I : Type) (J : I → Type) (K : Π i : I, J i → Type) :=
Σ i : I, Π j : J i, K i j

inductive F₁
| e₀ : F₁

inductive F₂
| e₀ : F₂
| e₁ : F₂

namespace Bool
def I := F₂
def J (i : I) := F₁
def K (i : I) (j : J i) := F₁
def Bool := algebraic I J K
def False : Bool := ⟨F₂.e₀, id⟩
def True  : Bool := ⟨F₂.e₁, id⟩
end Bool

namespace Maybe
def I := F₂
def J (i : I) := F₁
def K (A : Type) : Π i : I, J i → Type
| F₂.e₀ F₁.e₀ := F₁
| F₂.e₁ F₁.e₀ := A
def Maybe (A) := algebraic I J (K A)
def Nothing {A} : Maybe A := ⟨F₂.e₀, begin intro, cases j, exact F₁.e₀ end⟩
def Just {A} (a : A) : Maybe A := ⟨F₂.e₁, begin intro, cases j, exact a end⟩
end Maybe

namespace Prod
def I := F₁
def J (i : I) := F₂
def K (A B : Type) : Π i : I, J i → Type
| F₁.e₀ F₂.e₀ := A
| F₁.e₀ F₂.e₁ := B
def Prod (A B) := algebraic I J (K A B)
def Mk {A B} (a : A) (b : B) : Prod A B := ⟨F₁.e₀, begin intro, cases j, exact a, exact b end⟩
end Prod

namespace Sum
def I := F₂
def J (i : I) := F₁
def K (A B : Type) : Π i : I, J i → Type
| F₂.e₀ F₁.e₀ := A
| F₂.e₁ F₁.e₀ := B
def Sum (A B) := algebraic I J (K A B)
def Inl {A B} (a : A) : Sum A B := ⟨F₂.e₀, begin intro, cases j, exact a end⟩
def Inr {A B} (b : B) : Sum A B := ⟨F₂.e₁, begin intro, cases j, exact b end⟩
end Sum

-- TODO: Figure out how well_founded.fix recursion works in Lean
axiom fix {A} (f : A → A) : A  -- := f (fix f)
def wtf : false := fix id

namespace List
def I := F₂
def J : I → Type
| F₂.e₀ := F₁
| F₂.e₁ := F₂
def K (A B) : Π i : I, J i → Type
| F₂.e₀ F₁.e₀ := F₁
| F₂.e₁ F₂.e₀ := A
| F₂.e₁ F₂.e₁ := B
def List (A) := fix $ λ B, algebraic I J (K A B)
-- TODO: Define Nil and Cons
end List
