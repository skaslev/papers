def U := Type
def UU := Type → Type

def fiber {α β : U} (f : α → β) (y : β) := Σ' x, f(x) = y

def iscontr (α : U) := Σ' x : α, Π y : α, x = y
def isprop (α : U) := Π x y : α, x = y

@[simp] lemma sigma.mk.eta {α} {β : α → Type} : Π {p : Σ α, β α}, sigma.mk p.1 p.2 = p
| ⟨a, b⟩ := rfl

notation f `⋆` g := g ∘ f
attribute [simp] function.comp

namespace function
@[simp]
def sum {α β γ δ} (f : α → β) (g : γ → δ) (x : α ⊕ γ) : β ⊕ δ :=
sum.rec (f ⋆ sum.inl) (g ⋆ sum.inr) x

@[simp]
def prod {α β γ δ} (f : α → β) (g : γ → δ) (x : α × γ) : β × δ :=
(f x.1, g x.2)

@[simp]
def dimap {α β γ δ} (f : α → β) (g : γ → δ) (x : β → γ) : α → δ :=
f ⋆ x ⋆ g
end function

structure {u v} iso (α : Type u) (β : Type v) :=
(f : α → β) (g : β → α) (gf : Π x, g (f x) = x) (fg : Π x, f (g x) = x)

namespace iso
def id {α} : iso α α :=
⟨id, id, by simp [id], by simp [id]⟩

def inv {α β} (i : iso α β) : iso β α :=
⟨i.g, i.f, i.fg, i.gf⟩

def comp {α β γ} (i : iso α β) (j : iso β γ) : iso α γ :=
⟨i.f ⋆ j.f, j.g ⋆ i.g, by simp [j.gf, i.gf], by simp [i.fg, j.fg]⟩

def sum {α β γ δ} (i : iso α β) (j : iso γ δ) : iso (α ⊕ γ) (β ⊕ δ) :=
⟨function.sum i.f j.f,
 function.sum i.g j.g,
 λ x, sum.rec (by simp [i.gf]) (by simp [j.gf]) x,
 λ x, sum.rec (by simp [i.fg]) (by simp [j.fg]) x⟩

def prod {α β γ δ} (i : iso α β) (j : iso γ δ) : iso (α × γ) (β × δ) :=
⟨function.prod i.f j.f,
 function.prod i.g j.g,
 by simp [i.gf, j.gf],
 by simp [i.fg, j.fg]⟩

def dimap {α β γ δ} (i : iso α β) (j : iso γ δ) : iso (β → γ) (α → δ) :=
⟨function.dimap i.f j.f,
 function.dimap i.g j.g,
 λ x, funext (by simp [i.fg, j.gf]),
 λ x, funext (by simp [i.gf, j.fg])⟩

def func {α β γ δ} (i : iso α β) (j : iso γ δ) : iso (α → γ) (β → δ) :=
dimap i.inv j

def sigma_sub {α} {β γ : α → Type} (i : Π a:α, iso (β a) (γ a)) : iso (Σ a:α, β a) (Σ a:α, γ a) :=
⟨λ x, ⟨x.1, (i x.1).f x.2⟩,
 λ x, ⟨x.1, (i x.1).g x.2⟩,
 λ x, by simp [(i x.1).gf],
 λ x, by simp [(i x.1).fg]⟩

def sigma_sum {α} {β γ : α → Type} : iso ((Σ a : α, β a) ⊕ (Σ a : α, γ a)) (Σ a : α, β a ⊕ γ a) :=
⟨λ x, sum.rec (λ y, ⟨y.1, sum.inl y.2⟩) (λ y, ⟨y.1, sum.inr y.2⟩) x,
 λ x, sum.rec (λ y, sum.inl ⟨x.1, y⟩) (λ y, sum.inr ⟨x.1, y⟩) x.2,
 λ x, by induction x; repeat { dsimp, rw sigma.mk.eta },
 λ x, by induction x with x1 x2; induction x2; repeat { refl }⟩

def distr_right {α β γ} : iso ((α ⊕ β) × γ) (α × γ ⊕ β × γ) :=
⟨λ x, sum.rec (λ y, sum.inl (y, x.2)) (λ y, sum.inr (y, x.2)) x.1,
 λ x, sum.rec (λ y, (sum.inl y.1, y.2)) (λ y, (sum.inr y.1, y.2)) x,
 λ x, by induction x with x1 x2; induction x1; repeat { simp },
 λ x, by induction x; repeat { simp }⟩
end iso

axiom deriv : UU → UU

-- The generating function of `zipper f` is T(x) = x f'(x)
def zipper (f : UU) (α) := α × deriv f α

-- The logarithmic derivative of f(x) is g(x) such that f'(x) = f(x) g(x)
-- that is g(x) = (ln f(x))' = f'(x)/f(x)
def logderiv (f : UU) := Σ g : UU, Π α, iso (deriv f α) (f α × g α)

-- Given f(x) and it's logarithmic derivative g(x) we can construct alternative zipper
def logderiv_zipper (f : UU) (g : logderiv f) (α) := α × f α × g.1 α

-- .. that is isomorphic to the usual one
def logderiv_zipper_iso (f : UU) (g : logderiv f) (α) : iso (zipper f α) (logderiv_zipper f g α) :=
iso.id.prod (g.2 α)

class comonad (m : Type → Type) extends functor m :=
(extract : Π {α}, m α → α)
(dup : Π {α}, m α → m (m α))
(map_extract_over_dup : Π {α} {x : m α}, extract <$> dup x = x)

namespace comonad
def cobind {m α β} [comonad m] (x: m α) (f : m α -> β) : m β := f <$> dup x
notation x `=>>` g := cobind x g
end comonad

def bind {m α β} [monad m] (x : m α) (f : α -> m β) : m β := monad.join $ f <$> x

namespace zipper
variables {f : UU} [functor (deriv f)]

def map {α β} (g : α → β) (x : zipper f α) : zipper f β :=
(g x.1, g <$> x.2)

instance : functor (zipper f) :=
{ map := @map _ _ }

def extract {α} (z : zipper f α) : α := z.1
-- def dup {α} (z : zipper f α) : zipper f (zipper f α) :=
end zipper
