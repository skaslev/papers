import isos.bool
import isos.option
import isos.list
import sampler

def out {A} [has_repr A] (a : io A) : io unit :=
do
  x <- a,
  io.put_str_ln $ repr x

open sample

#eval out $ gen_fseq 50 $ fin 40000
#eval out $ gen_fseqₛ 50 $ bounded_ogf_iso₁ bool.ogf_iso 0

#eval out $ gen_fseqₛ 50 $ X.sized_ogf list bool 3
#eval out $ gen_fseqₛ 50 $ X.bounded_ogf list bool 3

#eval out $ gen_fseqₛ 50 $ X.sized_ogf₁ nat 10
#eval out $ gen_fseqₛ 50 $ X.bounded_ogf₁ nat 10

#eval out $ gen_fseqₛ 50 $ sized_ogf_iso (@option.ogf_iso bool) 1
#eval out $ gen_fseqₛ 50 $ bounded_ogf_iso (@option.ogf_iso bool) 1

#eval out $ gen_fseqₛ 50 $ @sized_ogf_iso _ _ _ (bounded_ogf_iso option.ogf_iso 1) (@list.ogf_iso (option bool)) 3
#eval out $ gen_fseqₛ 50 $ @bounded_ogf_iso _ _ _ (bounded_ogf_iso option.ogf_iso 1) (@list.ogf_iso (option bool)) 3

#eval out $ gen_fseqₛ 50 $ bounded_ogf (delta 2) bool 20
#eval out $ genₛ $ bounded_ogf (const 500) bool 10
#eval out $ genₛ $ bounded_ogf (const 500) bool 10
#eval out $ genₛ $ bounded_ogf (const 500) bool 10
#eval out $ gen_fseqₛ 50 $ bounded_ogf (const 2) bool 10

#eval take 50 $ delta 10
#eval take 50 $ option.cf
#eval take 50 $ ogf.cmul (delta 10) option.cf
#eval out $ genₛ $ sized_ogf (ogf.cmul (delta 10) option.cf) bool 10
#eval out $ genₛ $ sized_ogf (ogf.cmul (delta 10) option.cf) bool 11
#eval out $ genₛ $ sized_ogf (ogf.cmul (delta 10) option.cf) bool 12
