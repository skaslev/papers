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
def K (α : Type) : Π i : I, J i → Type
| F₂.e₀ F₁.e₀ := F₁
| F₂.e₁ F₁.e₀ := α
def Maybe α := algebraic I J (K α)
def Nothing {α} : Maybe α := ⟨F₂.e₀, begin intro, cases j, exact F₁.e₀ end⟩
def Just {α} (a : α) : Maybe α := ⟨F₂.e₁, begin intro, cases j, exact a end⟩
end Maybe

namespace Prod
def I := F₁
def J (i : I) := F₂
def K (α β : Type) : Π i : I, J i → Type
| F₁.e₀ F₂.e₀ := α
| F₁.e₀ F₂.e₁ := β
def Prod (α β) := algebraic I J (K α β)
def Mk {α β} (a : α) (b : β) : Prod α β := ⟨F₁.e₀, begin intro, cases j, exact a, exact b end⟩
end Prod

namespace Sum
def I := F₂
def J (i : I) := F₁
def K (α β : Type) : Π i : I, J i → Type
| F₂.e₀ F₁.e₀ := α
| F₂.e₁ F₁.e₀ := β
def Sum (α β) := algebraic I J (K α β)
def Inl {α β} (a : α) : Sum α β := ⟨F₂.e₀, begin intro, cases j, exact a end⟩
def Inr {α β} (b : β) : Sum α β := ⟨F₂.e₁, begin intro, cases j, exact b end⟩
end Sum

-- TODO: Figure out how well_founded.fix recursion works in Lean
axiom fix {α} (f : α → α) : α  -- := f (fix f)
def wtf : false := fix id

namespace List
def I := F₂
def J : I → Type
| F₂.e₀ := F₁
| F₂.e₁ := F₂
def K (α β) : Π i : I, J i → Type
| F₂.e₀ F₁.e₀ := F₁
| F₂.e₁ F₂.e₀ := α
| F₂.e₁ F₂.e₁ := β
def List α := fix $ λ β, algebraic I J (K α β)
-- TODO: Define Nil and Cons
end List