import data.iso
import category.cofunctor
import category.comonad

-- Yoneda lemma can be stated in terms of the right and left Kan extensions
-- along the id functor
-- If f is a functor then for all types A
-- f A ↪ Π B, (A → B) → f B = ran id f A
-- f A ↪ Σ B, (B → A) × f B = lan id f A
-- and similarly for contravariant functors using contravariant Kan extensions.
-- The proofs in the contravariant case are (as expected) identical to the
-- covariant ones.

def ran (g h : Type → Type) (A : Type) := Π B, (A → g B) → h B
def lan (g h : Type → Type) (A : Type) := Σ B, (g B → A) × h B

def mapr {g h} {A B} (s : A → B) (x : ran g h A) : ran g h B :=
λ b t, x b (t ∘ s)

def mapl {g h} {A B} (s : A → B) (x : lan g h A) : lan g h B :=
⟨x.1, ⟨s ∘ x.2.1, x.2.2⟩⟩

namespace co
def ran (g h : Type → Type) (A : Type) := Π B, (g B → A) → h B
def lan (g h : Type → Type) (A : Type) := Σ B, (A → g B) × h B

def mapr {g h} {A B} (s : A → B) (x : ran g h B) : ran g h A :=
λ b t, x b (s ∘ t)

def mapl {g h} {A B} (s : A → B) (x : lan g h B) : lan g h A :=
⟨x.1, ⟨x.2.1 ∘ s, x.2.2⟩⟩
end co

attribute [reducible] id
attribute [simp] function.comp

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

def natural {f g} [functor f] [functor g] (t : Π {A}, f A → g A) :=
Π {A B} (x : f A) (s : A → B), s <$> (t x) = t (s <$> x)

axiom free_theorem {f g} [functor f] [functor g] (t : Π A, f A → g A) : natural t

namespace co
def natural {f g} [cofunctor f] [cofunctor g] (t : Π {A}, f A → g A) :=
Π {A B} (x : f B) (s : A → B), s <€> (t x) = t (s <€> x)

axiom free_theorem {f g} [cofunctor f] [cofunctor g] (t : Π A, f A → g A) : natural t
end co

section yoneda
variables {f : Type → Type} [functor f] [is_lawful_functor f] {A : Type}

@[reducible] def yonedar := ran id

def checkr (x : f A) : yonedar f A :=
λ b s, s <$> x

def uncheckr (x : yonedar f A) : f A :=
x A id

def uncheckr_checkr (x : f A) : uncheckr (checkr x) = x :=
begin
  simp [checkr, uncheckr, is_lawful_functor.id_map]
end

def checkr_uncheckr (x : yonedar f A) : checkr (uncheckr x) = x :=
begin
  simp [checkr, uncheckr],
  funext,
  apply free_theorem (@uncheckr f _ _)
end

@[reducible] def yonedal := lan id

def checkl (x : f A) : yonedal f A :=
⟨A, ⟨id, x⟩⟩

def uncheckl (x : yonedal f A) : f A :=
x.2.1 <$> x.2.2

def uncheckl_checkl (x : f A) : uncheckl (checkl x) = x :=
begin
  simp [checkl, uncheckl, is_lawful_functor.id_map]
end

def checkl_uncheckl (x : yonedal f A) : checkl (uncheckl x) = x :=
begin
  simp [uncheckl],
  rw ←free_theorem (@checkl f _ _),
  simp [checkl, functor.map, mapl]
end
end yoneda

namespace co
variables {f : Type → Type} [cofunctor f] [is_lawful_cofunctor f] {A : Type}

@[reducible] def yonedar := ran id

def checkr (x : f A) : yonedar f A :=
λ b s, s <€> x

def uncheckr (x : yonedar f A) : f A :=
x A id

def uncheckr_checkr (x : f A) : uncheckr (checkr x) = x :=
begin
  simp [checkr, uncheckr, is_lawful_cofunctor.id_comap]
end

def checkr_uncheckr (x : yonedar f A) : checkr (uncheckr x) = x :=
begin
  simp [checkr, uncheckr],
  funext,
  apply free_theorem (@uncheckr f _ _)
end

@[reducible] def yonedal := lan id

def checkl (x : f A) : yonedal f A :=
⟨A, ⟨id, x⟩⟩

def uncheckl (x : yonedal f A) : f A :=
x.2.1 <€> x.2.2

def uncheckl_checkl (x : f A) : uncheckl (checkl x) = x :=
begin
  simp [checkl, uncheckl, is_lawful_cofunctor.id_comap]
end

def checkl_uncheckl (x : yonedal f A) : checkl (uncheckl x) = x :=
begin
  simp [uncheckl],
  rw ←free_theorem (@checkl f _ _),
  simp [checkl, cofunctor.comap, co.mapl]
end
end co

structure {u v} emb (A : Type u) (B : Type v) :=
(f : A → B) (g : B → A) (gf : Π x, g (f x) = x)

namespace emb
def comp {A B C} (i : emb A B) (j : emb B C) : emb A C :=
⟨j.f ∘ i.f, i.g ∘ j.g, by simp [j.gf, i.gf]⟩
end emb

section yoneda_emb
variables (f : Type → Type) [functor f] [is_lawful_functor f] ⦃A : Type⦄

def yonedar_emb : emb (f A) (yonedar f A) :=
⟨checkr, uncheckr, uncheckr_checkr⟩

def yonedal_emb : emb (f A) (yonedal f A) :=
⟨checkl, uncheckl, uncheckl_checkl⟩
end yoneda_emb

namespace co
variables (f : Type → Type) [cofunctor f] [is_lawful_cofunctor f] ⦃A : Type⦄

def coyonedar_emb : emb (f A) (yonedar f A) :=
⟨checkr, uncheckr, uncheckr_checkr⟩

def yonedal_emb : emb (f A) (yonedal f A) :=
⟨checkl, uncheckl, uncheckl_checkl⟩
end co

section yoneda_iso
variables (f : Type → Type) [functor f] [is_lawful_functor f] ⦃A : Type⦄

def yonedar_iso : iso (f A) (yonedar f A) :=
⟨checkr, uncheckr, uncheckr_checkr, checkr_uncheckr⟩

def yonedal_iso : iso (f A) (yonedal f A) :=
⟨checkl, uncheckl, uncheckl_checkl, checkl_uncheckl⟩

def yonedarl_iso : iso (yonedar f A) (yonedal f A) :=
(@yonedar_iso f _ _ A).inv.comp (@yonedal_iso f _ _ A)
end yoneda_iso

namespace co
variables (f : Type → Type) [cofunctor f] [is_lawful_cofunctor f] ⦃A : Type⦄

def yonedar_iso : iso (f A) (yonedar f A) :=
⟨checkr, uncheckr, uncheckr_checkr, checkr_uncheckr⟩

def yonedal_iso : iso (f A) (yonedal f A) :=
⟨checkl, uncheckl, uncheckl_checkl, checkl_uncheckl⟩

def yonedarl_iso : iso (yonedar f A) (yonedal f A) :=
(@yonedar_iso f _ _ A).inv.comp (@yonedal_iso f _ _ A)
end co

-- instance {f} [applicative f] : applicative (yonedar f) := iso.applicative (yonedar_iso f)
-- instance {f} [applicative f] : applicative (yonedal f) := iso.applicative (yonedal_iso f)
-- instance {f} [monad f]       : monad (yonedar f)       := iso.monad (yonedar_iso f)
-- instance {f} [monad f]       : monad (yonedal f)       := iso.monad (yonedal_iso f)

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

def mdup {f : Type → Type} [monad f] {A} (x : f A) : f (f A) :=
pure <$> x

def mbind {f : Type → Type} [monad f] {A B} (x : f A) (s : A → f B) : f B :=
mjoin (s <$> x)

def mjoin_mdup {f : Type → Type} [monad f] [is_lawful_monad f] {A} (x : f A) : mjoin (mdup x) = x :=
begin
  simp [mjoin, mdup],
  sorry
end

section myonedar
@[reducible] def myonedar (f : Type → Type) := ran f f

variables {f : Type → Type} [monad f] [is_lawful_monad f] {A : Type}

def mcheckr (x : f A) : myonedar f A :=
λ b s, mjoin (s <$> x)

def muncheckr (x : myonedar f A) : f A :=
x A pure

def mouncheckr_mocheckr (x : f A) : muncheckr (mcheckr x) = x :=
mjoin_mdup x
end myonedar

section cyonedal
@[reducible] def cyonedal (f : Type → Type) := lan f f

variables {f : Type → Type} [comonad f] {A : Type}

def ccheckl (x : f A) : cyonedal f A :=
⟨A, ⟨comonad.extract, x⟩⟩

def cuncheckl (x : cyonedal f A) : f A :=
x.2.1 <$> comonad.dup x.2.2

def cuncheckl_ccheckl (x : f A) : cuncheckl (ccheckl x) = x :=
comonad.map_extract_over_dup

def not_natural_ccheckl [inhabited (f unit)] : ¬natural (@ccheckl f _) :=
λ h, unit_ne_bool (congr_arg sigma.fst (h (default (f unit)) (λ x, bool.tt)))
end cyonedal

def cyonedal_emb {f} [h : comonad f] {A} : emb (f A) (cyonedal f A) :=
⟨ccheckl, cuncheckl, cuncheckl_ccheckl⟩
