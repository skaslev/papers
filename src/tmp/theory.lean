import ..data.cseq

@[reducible, simp]
def statement (M : Type*) := M → Type*

@[reducible, simp]
def statements (M) := cseq (statement M)

def proof {M} (c : statements M) := Π (m : M) (i : c), c i m

def theorems (M) := Σ c : statements M, proof c

def theory (M) := theorems M → theorems M

def is_complete {M} (c : theorems M) := c.1.is_full
