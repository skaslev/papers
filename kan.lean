def ran (g h : Type → Type) (α : Type) := Π β, (α → g β) → h β
def lan (g h : Type → Type) (α : Type) := Σ β, (g β → α) × h β

def mapr {g h} {α β} (s : α → β) (x : ran g h α) : ran g h β :=
λ b t, x b (t ∘ s)

def mapl {g h} {α β} (s : α → β) (x : lan g h α) : lan g h β :=
⟨x.1, ⟨s ∘ x.2.1, x.2.2⟩⟩

attribute [reducible] id
attribute [simp] function.comp

@[simp] lemma prod.mk.eta {α β} : Π {p : α × β}, (p.1, p.2) = p
| (a, b) := rfl

@[simp] lemma sigma.mk.eta {α} {β : α → Type} : Π {p : Σ α, β α}, sigma.mk p.1 p.2 = p
| ⟨a, b⟩ := rfl

instance {g h} : functor (ran g h) :=
{ map := @mapr g h,
  id_map := by intros; simp [mapr],
  map_comp := by intros; simp [mapr] }

instance {g h} : functor (lan g h) :=
{ map := @mapl g h,
  id_map := by intros; simp [mapl],
  map_comp := by intros; simp [mapl] }

def natural {f g} [functor f] [functor g] (t : Π {α}, f α → g α) :=
Π {α β} {x : f α} (s : α → β), s <$> (t x) = t (s <$> x)

axiom free_theorem {f g} [functor f] [functor g] (t : Π α, f α → g α) : natural t

@[reducible] def yoneda := ran id

def check {f} [functor f] {α} (x : f α) : yoneda f α :=
λ b s, s <$> x

def uncheck {f} [functor f] {α} (x : yoneda f α) : f α :=
x α id

def uncheck_check {f} [functor f] {α} (x : f α) : uncheck (check x) = x :=
begin
  simp [check, uncheck, functor.id_map]
end

def check_uncheck {f} [functor f] {α} (x : yoneda f α) : check (uncheck x) = x :=
begin
  simp [check],
  repeat { apply funext, intro },
  apply free_theorem (@uncheck f _)
end

@[reducible] def coyoneda := lan id

def cocheck {f} [functor f] {α} (x : f α) : coyoneda f α :=
⟨α, ⟨id, x⟩⟩

def councheck {f} [functor f] {α} (x : coyoneda f α) : f α :=
x.2.1 <$> x.2.2

def councheck_cocheck {f} [functor f] {α} (x : f α) : councheck (cocheck x) = x :=
begin
  simp [cocheck, councheck, functor.id_map]
end

def cocheck_councheck {f} [functor f] {α} (x : coyoneda f α) : cocheck (councheck x) = x :=
begin
  simp [councheck],
  rw ←free_theorem (@cocheck f _),
  simp [cocheck, has_map.map, mapl]
end

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
{ map := @imap f g @i _,
  id_map :=
  begin
    intros,
    simp [imap, functor.id_map, i.fg]
  end,
  map_comp :=
  begin
    intros,
    simp [imap, i.gf],
    rw functor.map_comp
  end }

@[priority std.priority.default-1]
instance applicative [applicative f] : applicative g :=
{ pure := @ipure f g @i _,
  seq := @iseq f g @i _,
  pure_seq_eq_map := by intros; simp,
  id_map :=
  begin
    intros,
    simp [ipure, iseq, i.gf],
    simp [applicative.pure_seq_eq_map, functor.id_map, i.fg]
  end,
  map_pure :=
  begin
    intros,
    simp [ipure, iseq, i.gf],
    simp [applicative.pure_seq_eq_map, applicative.map_pure]
  end,
  seq_pure :=
  begin
    intros,
    simp [ipure, iseq, i.gf],
    simp [applicative.pure_seq_eq_map, applicative.seq_pure]
  end,
  seq_assoc :=
  begin
    intros,
    simp [ipure, iseq, i.gf],
    simp [applicative.pure_seq_eq_map, applicative.seq_assoc]
  end }

@[priority std.priority.default-1]
instance monad [monad f] : monad g :=
{ pure := @ipure f g @i _,
  bind := @ibind f g @i _,
  id_map :=
  begin
    intros,
    simp [ipure, ibind, i.gf],
    rw monad.bind_pure_comp_eq_map,
    simp [functor.id_map, i.fg]
  end,
  pure_bind :=
  begin
    intros,
    simp [ipure, ibind, i.gf],
    simp [monad.pure_bind, i.fg]
  end,
  bind_assoc :=
  begin
    intros,
    simp [ibind, i.gf],
    simp [monad.bind_assoc]
  end }
end iso

def yoneda_iso f [functor f] ⦃α⦄ : iso (f α) (yoneda f α) :=
⟨check, uncheck, uncheck_check, check_uncheck⟩

def coyoneda_iso f [functor f] ⦃α⦄ : iso (f α) (coyoneda f α) :=
⟨cocheck, councheck, councheck_cocheck, cocheck_councheck⟩

instance {f} [applicative f] : applicative (yoneda f)   := iso.applicative (yoneda_iso f)
instance {f} [applicative f] : applicative (coyoneda f) := iso.applicative (coyoneda_iso f)
instance {f} [monad f]       : monad (yoneda f)         := iso.monad (yoneda_iso f)
instance {f} [monad f]       : monad (coyoneda f)       := iso.monad (coyoneda_iso f)

def yoco_iso f [functor f] ⦃α⦄ : iso (yoneda f α) (coyoneda f α) :=
⟨cocheck ∘ uncheck, check ∘ councheck,
by simp [councheck_cocheck, check_uncheck],
by simp [uncheck_check, cocheck_councheck]⟩

def natural_check {f} [functor f] : natural (@check f _) :=
begin
  unfold natural, intros,
  simp [check, has_map.map, mapr],
  repeat { apply funext, intro },
  rw functor.map_comp
end

def natural_uncheck {f} [functor f] : natural (@uncheck f _) :=
begin
  unfold natural, intros,
  dsimp [uncheck, has_map.map, mapr],
  admit  -- ← stuck here
end

def natural_cocheck {f} [functor f] : natural (@cocheck f _) :=
begin
  unfold natural, intros,
  dsimp [cocheck, has_map.map, mapl],
  admit  -- ← stuck here
end

def natural_councheck {f} [functor f] : natural (@councheck f _) :=
begin
  unfold natural, intros,
  simp [councheck, has_map.map, mapl],
  rw ←functor.map_comp
end