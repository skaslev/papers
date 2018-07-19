-- Yoneda lemma can be stated in terms of the right and left Kan extensions
-- along the id functor
-- If f is a functor then for all types α
-- f α ↪ Π β, (α → β) → f β = ran id f α
-- f α ↪ Σ β, (β → α) × f β = lan id f α
-- and similarly for contravariant functors using contravariant Kan extensions.
-- The proofs in the contravariant case are (as expected) identical to the
-- covariant ones.

def ran (g h : Type → Type) (α : Type) := Π β, (α → g β) → h β
def lan (g h : Type → Type) (α : Type) := Σ β, (g β → α) × h β

def mapr {g h} {α β} (s : α → β) (x : ran g h α) : ran g h β :=
λ b t, x b (t ∘ s)

def mapl {g h} {α β} (s : α → β) (x : lan g h α) : lan g h β :=
⟨x.1, ⟨s ∘ x.2.1, x.2.2⟩⟩

namespace co
def ran (g h : Type → Type) (α : Type) := Π β, (g β → α) → h β
def lan (g h : Type → Type) (α : Type) := Σ β, (α → g β) × h β

def mapr {g h} {α β} (s : α → β) (x : ran g h β) : ran g h α :=
λ b t, x b (s ∘ t)

def mapl {g h} {α β} (s : α → β) (x : lan g h β) : lan g h α :=
⟨x.1, ⟨x.2.1 ∘ s, x.2.2⟩⟩
end co

attribute [reducible] id
attribute [simp] function.comp

-- @[simp] lemma prod.mk.eta {α β} : Π {p : α × β}, (p.1, p.2) = p
-- | (a, b) := rfl

@[simp] lemma sigma.mk.eta {α} {β : α → Type} : Π {p : Σ α, β α}, sigma.mk p.1 p.2 = p
| ⟨a, b⟩ := rfl

instance {g h} : functor (ran g h) :=
{ map := @mapr g h }

instance {g h} : is_lawful_functor (ran g h) :=
{ id_map := by intros; simp [functor.map, mapr],
  comp_map := by intros; simp [functor.map, mapr] }

instance {g h} : functor (lan g h) :=
{ map := @mapl g h }

instance {g h} : is_lawful_functor (lan g h) :=
{ id_map := by intros; simp [functor.map, mapl],
  comp_map := by intros; simp [functor.map, mapl] }

class {u v} cofunctor (f : Type u → Type v) : Type (max (u+1) v) :=
(comap : Π {α β : Type u}, (α → β) → f β → f α)

infixr ` <€> `:100 := cofunctor.comap

class {u v} is_lawful_cofunctor (f : Type u → Type v) [cofunctor f] : Prop :=
(id_comap     : Π {α : Type u} (x : f α), id <€> x = x)
(comp_comap   : Π {α β γ : Type u} (g : α → β) (h : β → γ) (x : f γ), (h ∘ g) <€> x = g <€> h <€> x)

instance {g h} : cofunctor (co.ran g h) :=
{ comap := @co.mapr g h }

instance {g h} : is_lawful_cofunctor (co.ran g h) :=
{ id_comap := by intros; simp [cofunctor.comap, co.mapr],
  comp_comap := by intros; simp [cofunctor.comap, co.mapr] }

instance {g h} : cofunctor (co.lan g h) :=
{ comap := @co.mapl g h }

instance {g h} : is_lawful_cofunctor (co.lan g h) :=
{ id_comap := by intros; simp [cofunctor.comap, co.mapl],
  comp_comap := by intros; simp [cofunctor.comap, co.mapl] }

def natural {f g} [functor f] [functor g] (t : Π {α}, f α → g α) :=
Π {α β} (x : f α) (s : α → β), s <$> (t x) = t (s <$> x)

axiom free_theorem {f g} [functor f] [functor g] (t : Π α, f α → g α) : natural t

namespace co
def natural {f g} [cofunctor f] [cofunctor g] (t : Π {α}, f α → g α) :=
Π {α β} (x : f β) (s : α → β), s <€> (t x) = t (s <€> x)

axiom free_theorem {f g} [cofunctor f] [cofunctor g] (t : Π α, f α → g α) : natural t
end co

section yoneda
variables {f : Type → Type} [functor f] [is_lawful_functor f] {α : Type}

@[reducible] def yonedar := ran id

def checkr (x : f α) : yonedar f α :=
λ b s, s <$> x

def uncheckr (x : yonedar f α) : f α :=
x α id

def uncheckr_checkr (x : f α) : uncheckr (checkr x) = x :=
begin
  simp [checkr, uncheckr, is_lawful_functor.id_map]
end

def checkr_uncheckr (x : yonedar f α) : checkr (uncheckr x) = x :=
begin
  simp [checkr, uncheckr],
  funext,
  apply free_theorem (@uncheckr f _ _)
end

@[reducible] def yonedal := lan id

def checkl (x : f α) : yonedal f α :=
⟨α, ⟨id, x⟩⟩

def uncheckl (x : yonedal f α) : f α :=
x.2.1 <$> x.2.2

def uncheckl_checkl (x : f α) : uncheckl (checkl x) = x :=
begin
  simp [checkl, uncheckl, is_lawful_functor.id_map]
end

def checkl_uncheckl (x : yonedal f α) : checkl (uncheckl x) = x :=
begin
  simp [uncheckl],
  rw ←free_theorem (@checkl f _ _),
  simp [checkl, functor.map, mapl]
end
end yoneda

namespace co
variables {f : Type → Type} [cofunctor f] [is_lawful_cofunctor f] {α : Type}

@[reducible] def yonedar := ran id

def checkr (x : f α) : yonedar f α :=
λ b s, s <€> x

def uncheckr (x : yonedar f α) : f α :=
x α id

def uncheckr_checkr (x : f α) : uncheckr (checkr x) = x :=
begin
  simp [checkr, uncheckr, is_lawful_cofunctor.id_comap]
end

def checkr_uncheckr (x : yonedar f α) : checkr (uncheckr x) = x :=
begin
  simp [checkr, uncheckr],
  funext,
  apply free_theorem (@uncheckr f _ _)
end

@[reducible] def yonedal := lan id

def checkl (x : f α) : yonedal f α :=
⟨α, ⟨id, x⟩⟩

def uncheckl (x : yonedal f α) : f α :=
x.2.1 <€> x.2.2

def uncheckl_checkl (x : f α) : uncheckl (checkl x) = x :=
begin
  simp [checkl, uncheckl, is_lawful_cofunctor.id_comap]
end

def checkl_uncheckl (x : yonedal f α) : checkl (uncheckl x) = x :=
begin
  simp [uncheckl],
  rw ←free_theorem (@checkl f _ _),
  simp [checkl, cofunctor.comap, co.mapl]
end
end co

structure {u v} emb (α : Type u) (β : Type v) :=
(f : α → β) (g : β → α) (gf : Π x, g (f x) = x)

namespace emb
def comp {α β γ} (i : emb α β) (j : emb β γ) : emb α γ :=
⟨j.f ∘ i.f, i.g ∘ j.g, by simp [j.gf, i.gf]⟩
end emb

section yoneda_emb
variables (f : Type → Type) [functor f] [is_lawful_functor f] ⦃α : Type⦄

def yonedar_emb : emb (f α) (yonedar f α) :=
⟨checkr, uncheckr, uncheckr_checkr⟩

def yonedal_emb : emb (f α) (yonedal f α) :=
⟨checkl, uncheckl, uncheckl_checkl⟩
end yoneda_emb

namespace co
variables (f : Type → Type) [cofunctor f] [is_lawful_cofunctor f] ⦃α : Type⦄

def coyonedar_emb : emb (f α) (yonedar f α) :=
⟨checkr, uncheckr, uncheckr_checkr⟩

def yonedal_emb : emb (f α) (yonedal f α) :=
⟨checkl, uncheckl, uncheckl_checkl⟩
end co

structure {u v} iso (α : Type u) (β : Type v) :=
(f : α → β) (g : β → α) (gf : Π x, g (f x) = x) (fg : Π x, f (g x) = x)

namespace iso
def inv {α β} (i : iso α β) : iso β α :=
⟨i.g, i.f, i.fg, i.gf⟩

def comp {α β γ} (i : iso α β) (j : iso β γ) : iso α γ :=
⟨j.f ∘ i.f, i.g ∘ j.g, by simp [j.gf, i.gf], by simp [i.fg, j.fg]⟩

universes u v w
variables {f : Type u → Type v} {g : Type u → Type w} (i : Π {α}, iso (f α) (g α))

def imap [functor f] {α β : Type u} (s : α → β) (x : g α) : g β :=
i.f $ s <$> i.g x

def ipure [applicative f] {α : Type u} (x : α) : g α :=
i.f $ pure x

def iseq [applicative f] {α β : Type u} (s : g (α → β)) (x : g α) : g β :=
i.f $ i.g s <*> i.g x

def ibind [monad f] {α β : Type u} (x : g α) (s : α → g β) : g β :=
i.f $ i.g x >>= i.g ∘ s

@[priority std.priority.default-1]
instance functor [functor f] : functor g :=
{ map := @imap f g @i _ }

-- @[priority std.priority.default-1]
-- instance is_lawful_functor [functor f] : is_lawful_functor g :=
-- { id_map :=
--   begin
--     intros,
--     simp [imap, is_lawful_functor.id_map, i.fg]
--   end,
--   comp_map :=
--   begin
--     intros,
--     simp [imap, i.gf],
--     rw is_lawful_functor.comp_map
--   end }

@[priority std.priority.default-1]
instance applicative [applicative f] : applicative g :=
{ pure := @ipure f g @i _,
  seq := @iseq f g @i _ }

-- @[priority std.priority.default-1]
-- instance is_lawful_applicative [is_lawful_applicative f] : is_lawful_applicative g :=
-- { pure_seq_eq_map := by intros; simp,
--   id_map :=
--   begin
--     intros,
--     simp [ipure, iseq, i.gf],
--     simp [is_lawful_applicative.pure_seq_eq_map, is_lawful_functor.id_map, i.fg]
--   end,
--   map_pure :=
--   begin
--     intros,
--     simp [ipure, iseq, i.gf],
--     simp [is_lawful_applicative.pure_seq_eq_map, is_lawful_applicative.map_pure]
--   end,
--   seq_pure :=
--   begin
--     intros,
--     simp [ipure, iseq, i.gf],
--     simp [is_lawful_applicative.pure_seq_eq_map, is_lawful_applicative.seq_pure]
--   end,
--   seq_assoc :=
--   begin
--     intros,
--     simp [ipure, iseq, i.gf],
--     simp [is_lawful_applicative.pure_seq_eq_map, is_lawful_applicative.seq_assoc]
--   end }

@[priority std.priority.default-1]
instance monad [monad f] : monad g :=
{ pure := @ipure f g @i _,
  bind := @ibind f g @i _ }

-- @[priority std.priority.default-1]
-- instance is_lawful_monad [is_lawful_monad f] : is_lawful_monad g :=
-- { id_map :=
--   begin
--     intros,
--     simp [ipure, ibind, i.gf],
--     rw monad.bind_pure_comp_eq_map,
--     simp [is_lawful_functor.id_map, i.fg]
--   end,
--   pure_bind :=
--   begin
--     intros,
--     simp [ipure, ibind, i.gf],
--     simp [is_lawful_monad.pure_bind, i.fg]
--   end,
--   bind_assoc :=
--   begin
--     intros,
--     simp [ibind, i.gf],
--     simp [is_lawful_monad.bind_assoc]
--   end }
end iso

section yoneda_iso
variables (f : Type → Type) [functor f] [is_lawful_functor f] ⦃α : Type⦄

def yonedar_iso : iso (f α) (yonedar f α) :=
⟨checkr, uncheckr, uncheckr_checkr, checkr_uncheckr⟩

def yonedal_iso : iso (f α) (yonedal f α) :=
⟨checkl, uncheckl, uncheckl_checkl, checkl_uncheckl⟩

def yonedarl_iso : iso (yonedar f α) (yonedal f α) :=
(@yonedar_iso f _ _ α).inv.comp (@yonedal_iso f _ _ α)
end yoneda_iso

namespace co
variables (f : Type → Type) [cofunctor f] [is_lawful_cofunctor f] ⦃α : Type⦄

def yonedar_iso : iso (f α) (yonedar f α) :=
⟨checkr, uncheckr, uncheckr_checkr, checkr_uncheckr⟩

def yonedal_iso : iso (f α) (yonedal f α) :=
⟨checkl, uncheckl, uncheckl_checkl, checkl_uncheckl⟩

def yonedarl_iso : iso (yonedar f α) (yonedal f α) :=
(@yonedar_iso f _ _ α).inv.comp (@yonedal_iso f _ _ α)
end co

-- instance {f} [applicative f] : applicative (yonedar f) := iso.applicative (yonedar_iso f)
-- instance {f} [applicative f] : applicative (yonedal f) := iso.applicative (yonedal_iso f)
-- instance {f} [monad f]       : monad (yonedar f)       := iso.monad (yonedar_iso f)
-- instance {f} [monad f]       : monad (yonedal f)       := iso.monad (yonedal_iso f)

def isprop (α : Type) := ∀ x y : α, x = y

def isprop_unit : isprop unit
| () () := rfl

def notprop_bool : ¬isprop bool :=
λ h, bool.no_confusion (h bool.ff bool.tt)

def unit_ne_bool : unit ≠ bool :=
λ h, notprop_bool (h ▸ isprop_unit)

section naturality_proofs
variables {f : Type → Type} [functor f] [is_lawful_functor f]

def natural_checkr : natural (@checkr f _ _) :=
begin
  unfold natural, intros,
  dsimp [checkr, functor.map, mapr],
  funext,
  rw is_lawful_functor.comp_map
end

def natural_uncheckr : natural (@uncheckr f _ _) :=
begin
  unfold natural, intros,
  dsimp [uncheckr, functor.map, mapr],
  admit  -- ← stuck here
end

def natural_checkl : natural (@checkl f _ _) :=
begin
  unfold natural, intros,
  dsimp [checkl, functor.map, mapl],
  admit  -- ← stuck here
end

def not_natural_checkl [inhabited (f unit)] : ¬natural (@checkl f _ _) :=
λ h, unit_ne_bool (congr_arg sigma.fst (h (default (f unit)) (λ x, bool.tt)))

def natural_uncheckl : natural (@uncheckl f _ _) :=
begin
  unfold natural, intros,
  dsimp [uncheckl, functor.map, mapl],
  rw ←is_lawful_functor.comp_map
end
end naturality_proofs

def mdup {f : Type → Type} [monad f] {α} (x : f α) : f (f α) :=
pure <$> x

def mbind {f : Type → Type} [monad f] {α β} (x : f α) (s : α → f β) : f β :=
mjoin (s <$> x)

def mjoin_mdup {f : Type → Type} [monad f] [is_lawful_monad f] {α} (x : f α) : mjoin (mdup x) = x :=
begin
  simp [mjoin, mdup],
  sorry
end

section myonedar
@[reducible] def myonedar (f : Type → Type) := ran f f

variables {f : Type → Type} [monad f] [is_lawful_monad f] {α : Type}

def mcheckr (x : f α) : myonedar f α :=
λ b s, mjoin (s <$> x)

def muncheckr (x : myonedar f α) : f α :=
x α pure

def mouncheckr_mocheckr (x : f α) : muncheckr (mcheckr x) = x :=
mjoin_mdup x
end myonedar

class comonad (m : Type → Type) extends functor m :=
(extract : Π {α}, m α → α)
(dup : Π {α}, m α → m (m α))
(map_extract_over_dup : Π {α} {x : m α}, extract <$> dup x = x)

section cyonedal
@[reducible] def cyonedal (f : Type → Type) := lan f f

variables {f : Type → Type} [comonad f] {α : Type}

def ccheckl (x : f α) : cyonedal f α :=
⟨α, ⟨comonad.extract, x⟩⟩

def cuncheckl (x : cyonedal f α) : f α :=
x.2.1 <$> comonad.dup x.2.2

def cuncheckl_ccheckl (x : f α) : cuncheckl (ccheckl x) = x :=
comonad.map_extract_over_dup f
end cyonedal

def cyonedal_emb {f} [h : comonad f] {α} : emb (f α) (cyonedal f α) :=
⟨ccheckl, cuncheckl, cuncheckl_ccheckl⟩
