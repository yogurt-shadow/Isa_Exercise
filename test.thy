theory test
imports Main

begin
type_synonym val = int
type_synonym vname = string
type_synonym state = "vname \<Rightarrow> val"

datatype aexp2 = N2 int | V2 vname | Plus2 aexp2 aexp2 | PostInc vname 
                        |  Times2 aexp2 aexp2 | Div2 aexp2 aexp2 
fun aval2 :: "aexp2 \<Rightarrow> state \<Rightarrow> (val \<times> state)" where
  "aval2 (N2 a) s = (a,s)" |
  "aval2 (V2 x) s = (s x,s)" |
  "aval2 (Plus2 a b) s = (fst (aval2 a s) + fst (aval2 b s), (\<lambda> x. (snd (aval2 a s) x) 
  + (snd (aval2 b s) x) - (s x)))" |
  "aval2 (PostInc x) s = (s x, s(x:= 1 + s x))" |
  "aval2 (Times2 a b) s = (fst (aval2 a s) * fst (aval2 b s),(\<lambda> x. (snd (aval2 a s) x) 
  + (snd (aval2 b s) x) - (s x)))" |  
  "aval2 (Div2 a b) s = (fst (aval2 a s) div fst (aval2 b s),(\<lambda> x. (snd (aval2 a s) x) 
  + (snd (aval2 b s) x) - (s x)))"
  
value "aval2 (Plus2 (PostInc x) (PostInc x)) (\<lambda> x. 0)"
value "aval2 (Div2 (N2 9) (N2 3))  (\<lambda> x. 0) "
value "aval2 (PostInc u)  (\<lambda> x. 0) "

end