(* author: wzh *)

theory Chapter4
  imports Main

begin

lemma "\<forall> x. \<exists> y. x = y"
  apply(auto)
  done

lemma "A \<subseteq> (B \<inter> C) \<Longrightarrow> A \<subseteq> (B \<union> C)"
  apply(auto)
  done

lemma "(a::nat) \<le> x + b \<and> 2*x < c \<Longrightarrow> 2*a + 1 \<le> 2*b + c"
  by arith

lemma "(a::nat)\<le> b \<and> b \<le> c \<and> c \<le> d \<and> d \<le> e
\<Longrightarrow> a \<le> e"
  by (blast intro: le_trans)

thm conjI[of a b]
thm conjI[OF refl[of "a"] refl[of "b"]]

lemma "Suc(Suc(Suc a)) \<le> b \<Longrightarrow> a \<le> b"
  by (blast dest: Suc_leD)

inductive ev :: "nat \<Rightarrow> bool" where
ev0: "ev 0"
| evSS: "ev n \<Longrightarrow> ev (n+2)"

fun evn :: "nat \<Rightarrow> bool" where
"evn 0 = True" |
"evn (Suc 0) = False"
| "evn (Suc (Suc n)) = evn n"

lemma [simp]: "ev m \<Longrightarrow> evn m" 
  apply(induction rule: ev.induct)
  by(simp_all)

lemma [simp]: "evn m \<Longrightarrow> ev m"
  apply(induction m rule: evn.induct)
  by(simp_all add: ev.induct)

lemma "evn m = ev m"
  apply(auto)
  done

declare ev.intros [simp, intro]

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl: "star r x x"
| step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

lemma star_trans: "star r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"
  apply(induction rule: star.induct)
   apply(assumption)
  apply(metis step)
  done

end