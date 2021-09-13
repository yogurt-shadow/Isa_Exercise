(* author:wzh *)

(* then = from this *)
(* hence = from his have *)
(* thus = from this show *)
theory Exercise5
  imports Main
begin
(* Exercise 5.1 *)
lemma assumes T: "\<forall> x y. T x y \<or> T y x"
   and A: "\<forall> x y. A x y \<and> A y x \<longrightarrow> x = y"
   and TA: "\<forall> x y. T x y \<longrightarrow> A x y" 
   and Axy: "A x y"
 shows "T x y"
proof (rule ccontr)
  assume pre: "\<not> T x y"
  hence "T y x" using T by blast
  hence "A y x" using TA by blast
  hence equal: "x=y" using Axy and A by blast
  hence self: "T x x" using T by blast
  have "\<not> T x x" using equal and pre by blast
  thus "False" using self by blast
qed

(* Exercise 5.2 *)
lemma "\<exists> ys zs. xs = ys @ zs \<and> (length ys = length zs \<or> length ys = length zs + 1)"
proof cases
  assume "2 dvd length xs"
  hence "\<exists> k. length xs = 2 * k" by auto
  then obtain k where len: "length xs = 2 * k" by auto
  obtain ys where y: "ys = take k xs" by auto
  hence leny: "length ys = k" using len by auto
  obtain zs where z: "zs = drop k xs" by auto
  hence lenz: "length zs = k" using len by auto
  hence l: "length ys = length zs" using leny by auto
  moreover have "xs = ys @ zs" using y and z by auto
  ultimately show ?thesis by auto
next
  assume "\<not> 2 dvd length xs"
  hence "\<exists> k. length xs = 2*k + 1" by arith
  then obtain k where len: "length xs = 2*k + 1" by auto
  obtain ys where y: "ys = take (k+1) xs" by auto
  hence leny: "length ys = k+1" using len by auto
  obtain zs where z: "zs = drop (k+1) xs" by auto
  hence lenz: "length zs = k" using len by auto
  have "xs = ys @ zs" using y and z by auto
  moreover have "length ys = length zs + 1" using leny and lenz by auto
  ultimately show ?thesis by auto
qed

(* Exercise 5.3 *)
inductive ev :: "nat \<Rightarrow> bool" where
ev0: "ev 0"
| evSS: "ev n \<Longrightarrow> ev (Suc (Suc n))"

lemma assumes a: "ev (Suc (Suc n))" shows "ev n"
proof - 
  show "ev n" using a
  proof cases
    case evSS thus ?thesis by auto
  qed
qed

(* Exercise 5.4 *)
lemma "\<not> ev (Suc (Suc (Suc 0)))" 
proof
  assume "ev (Suc (Suc (Suc 0)))"
  then have "ev (Suc 0)" by cases
  thus False by cases
qed

(* Exercise 5.5 *)
inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl: "star r x x"
| step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl_iter: "iter r n x x"
| step_iter: "r x y \<Longrightarrow> iter r n y z \<Longrightarrow> iter r (n+1) x z"

lemma "iter r n x y \<Longrightarrow> star r x y"
proof (induction rule: iter.induct)
  case refl_iter
  show ?case by (auto intro: star.refl)
next
  case step_iter
  thus ?case by (auto intro: star.step)
qed

(* Exercise 5.6 *)
fun elems :: "'a list \<Rightarrow> 'a set" where
"elems [] = {}"
| "elems (x#xs) = {x} \<union> elems xs"

lemma fixes x shows "x \<in> elems xs \<Longrightarrow> \<exists> ys zs. xs = ys @ (x # zs) \<and> x \<notin> elems ys"
proof (induction xs)
  case Nil
  thus ?case by auto
next
  case (Cons a ks)
  show ?case
  proof cases
    assume eq: "a = x"
    obtain ys where y: "ys = ([]:: 'a list)" by auto
    obtain zs where z: "zs = ks" by auto
    have nin: "x \<notin> elems ys" using y by auto
    moreover have "(a # ks) = ys @ (x # zs)" using eq and y and z by auto
    ultimately show ?thesis by auto
  next
    assume neq: "\<not> a = x"
    hence "x \<in> elems ks" using Cons.prems by auto
    then obtain yss zs where nin: "ks = yss @ (x#zs) \<and> x \<notin> elems yss" using Cons.IH by auto
    obtain ys where y: "ys = a # yss" by auto
    hence "x \<notin> elems ys" using nin and neq by auto
    moreover have "a # ks = ys @ (x # zs)" using nin and y by auto
    ultimately show ?thesis by auto
  qed
qed

end