import system.io
import .functors.generating

class sampler (A : Type) :=
(gen : io A)

def gen (A) [sampler A] := @sampler.gen A
def genₛ {A} (s : sampler A) := @sampler.gen A s

instance : functor sampler :=
{map := λ A B f s, ⟨do x <- genₛ s, return $ f x⟩}

instance {n} : sampler (fin n) :=
{gen := do
  i <- io.rand 0 n,
  dite (i < n)
    (λ h, return ⟨i, h⟩)
    (λ h, failure)}

def gen_fseq (n A) [sampler A] : io (fseq n A) :=
nat.rec_on n
  (return fin.elim0)
  (λ n ih, do
    x <- gen A,
    xs <- ih,
    return $ fseq.cons_iso.f (x, xs))

def gen_fseqₛ (n) {A} (s : sampler A) : io (fseq n A) :=
@gen_fseq n A s

instance {n A} [sampler A] : sampler (fseq n A) :=
{gen := gen_fseq n A}

instance zero_sampler : sampler 0 :=
{gen := failure}

instance one_sampler : sampler 1 :=
{gen := return ()}

instance : sampler bool :=
{gen := do
  x <- io.rand 0 2,
  return $ x ≠ 0}

namespace sample
def sized_ogf (c A) [sampler A] (size : ℕ) : sampler (ogf c A) :=
{gen := do
  shape <- gen (fin (c size)),
  data <- gen (fseq size A),
  return ⟨size, (shape, data)⟩}

def sized_ogf_iso {f : Type → Type} {c A} [sampler A] (i : f A ≃ ogf c A) (size : ℕ) : sampler (f A) :=
i.g <$> sized_ogf c A size

def sized_ogf₁ (c) (size : ℕ) : sampler (ogf c 1) :=
sized_ogf c 1 size

def sized_ogf_iso₁ {A c} (i : A ≃ ogf c 1) (size : ℕ) : sampler A :=
sized_ogf_iso (iso.const_iso.inv ⋆ i) size

def sized_shape (c) (size : ℕ) : sampler (shape c) :=
ogf.shape_iso.f <$> sized_ogf₁ c size

def reverse_impl {A} : list A → list A → list A
| acc [] := acc
| acc (x::xs) := reverse_impl (x::acc) xs

def reverse {A} : list A → list A :=
reverse_impl []

def prefix_sum_impl (c : ℕ → ℕ) : ℕ → list ℕ
| 0 := [c 0]
| (n+1) :=
  let ih := prefix_sum_impl n in
  (c (n+1) + ih.head) :: ih

def prefix_sum  (c : ℕ → ℕ) (n : ℕ) : ℕ × list ℕ :=
let ps := prefix_sum_impl c n in
(ps.head, reverse ps)

def bounded_ogf (c A) [sampler A] (max_size : ℕ) : sampler (ogf c A) :=
let (num_shapes, ps) := prefix_sum c max_size in
{gen := do
  shape <- gen (fin num_shapes),
  let size := list.find_index (λ x, shape.1 < x) ps,
  genₛ (sized_ogf c A size)}

def bounded_ogf_iso {f : Type → Type} {c A} [sampler A] (i : f A ≃ ogf c A) (max_size : ℕ): sampler (f A) :=
i.g <$> bounded_ogf c A max_size

def bounded_ogf₁ (c) (max_size : ℕ) : sampler (ogf c 1) :=
bounded_ogf c 1 max_size

def bounded_ogf_iso₁ {A c} (i : A ≃ ogf c 1) (max_size : ℕ) : sampler A :=
bounded_ogf_iso (iso.const_iso.inv ⋆ i) max_size

def bounded_shape (c) (max_size : ℕ) : sampler (shape c) :=
ogf.shape_iso.f <$> bounded_ogf₁ c max_size
end sample

namespace X
def sized_ogf (f A) [has_ogf f] [sampler A] (size : ℕ) : sampler (f A) :=
(@has_ogf.iso f _ _).g <$> sample.sized_ogf (has_ogf.cf f) A size

def sized_ogf₁ (A) [has_ogf₁ A] (size : ℕ): sampler A :=
(@has_ogf₁.iso A _).g <$> sample.sized_ogf₁ (has_ogf₁.cf A) size

def bounded_ogf (f A) [has_ogf f] [sampler A] (max_size : ℕ) : sampler (f A) :=
(@has_ogf.iso f _ _).g <$> sample.bounded_ogf (has_ogf.cf f) A max_size

def bounded_ogf₁ (A) [has_ogf₁ A] (max_size : ℕ) : sampler A :=
(@has_ogf₁.iso A _).g <$> sample.bounded_ogf₁ (has_ogf₁.cf A) max_size
end X
