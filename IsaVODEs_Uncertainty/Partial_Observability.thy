theory Partial_Observability        
  imports "Hybrid-Verification.Hybrid_Verification"
begin

declare [[literal_variables=false]]

lemma diffInvariant:
  assumes "H{I} g_orbital_on a f (G)\<^sub>e (U)\<^sub>e S t\<^sub>0 {I}" "`P \<longrightarrow> I`"
          "H{P} g_orbital_on a f (G \<and> I)\<^sub>e (U)\<^sub>e S t\<^sub>0 {Q}"
  shows "H{P} g_orbital_on a f (G)\<^sub>e (U)\<^sub>e S t\<^sub>0 {Q}"
  apply (rule diff_cut_on_rule[where C=I])
  using assms weaken apply fastforce
  using assms by simp

method dInv for I :: "'s \<Rightarrow> bool" uses facts =
  (rule diffInvariant[where I="I"],
   (dInduct_mega facts: facts)[1],
   (expr_auto)[1])

method wlp_hoare uses simp =
  (intro_loops?; (simp add: wlp simp)?)

lemma new_varI:
  "(\<And>k. (@P \<and> $x = \<guillemotleft>k\<guillemotright>)\<^sub>e \<le> |X] (@Q)) \<Longrightarrow> (@P)\<^sub>e \<le> |X] (@Q)"
  "(\<And>k. (@P \<and> $x = \<guillemotleft>k\<guillemotright>)\<^sub>e \<le> |X] (@Q)) \<Longrightarrow> (\<lambda>s. P s) \<le> |X] (@Q)"
  "(\<And>k. (@P \<and> @Y = \<guillemotleft>k\<guillemotright>)\<^sub>e \<le> |X] (@Q)) \<Longrightarrow> (\<lambda>s. P s) \<le> |X] (@Q)"
  by (expr_auto add: fbox_def)+

lemma hoare_choice_disj_post:
  "H{P} F {Q} \<Longrightarrow> H{P} G {R} \<Longrightarrow> H{P} (F \<sqinter> G) {Q \<or> R}"
  unfolding fbox_def nondet_choice_def by auto

lemma hoare_disj_split:
  "H{P} F {R} \<Longrightarrow> H{Q} F {R} \<Longrightarrow> H{P \<or> Q} F {R}"
  unfolding fbox_def by (simp add: le_fun_def)

lemma hoare_conj_disj_split:
  "H{P \<and> S} F {R} \<Longrightarrow> H{Q \<and> S} F {R} \<Longrightarrow> H{S \<and> (P \<or> Q)} F {R}"
  by expr_auto

lemma H_nondet_assign_floyd_hoare:
  assumes "vwb_lens x"
  shows "H{p} x ::= ? {\<exists> v . p\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk>}"
  apply wlp_full
  by (metis assms vwb_lens.put_eq)

declare [[literal_variables]]

section \<open> Water tank \<close>

dataspace water_tank =
  constants
    m :: real
    \<epsilon> :: real
  assumes
  \<epsilon>_pos: "\<epsilon> > 0"
  variables
    f :: real
    l :: real
    c :: real
  
context water_tank
begin

definition "ctrl \<equiv> f ::= ? ; \<questiondown>-1 \<le> f \<and> f \<le> ((m - l) / \<epsilon>)? ; c ::= 0"

definition "plant \<equiv>  { l` = f, c` = 1 | (0 \<le> l \<and> c \<le> \<epsilon>)}"

lemma water_tank_safe: "H{0 \<le> $l \<and> $l \<le> m} (ctrl ; plant)\<^sup>* {0 \<le> $l \<and> $l \<le> m}"
  apply (rule hoare_kstar_inv)
  unfolding ctrl_def plant_def
  apply (wlp_solve "\<lambda>t. [l \<leadsto> $f * t + l, c \<leadsto> t + c]")
  apply expr_simp
  by (smt (verit) mult_left_mono pos_le_divide_eq zero_less_mult_iff)

end

dataspace disturbed_water_tank =
  constants
    m :: real
    \<epsilon> :: real
    d :: real
   assumes
    d_bounds: "0 \<le> d \<and> d \<le> 1/10" and
    epsilon_bounds: "0 \<le> \<epsilon>"
   variables
    f :: real
    l :: real
    c :: real
    fd :: real

context disturbed_water_tank
begin

definition "ctrl \<equiv> f ::= ? ; \<questiondown>-1 \<le> f \<and> f \<le> ((m - l) / \<epsilon>) - d? ; c ::= 0"

definition "act \<equiv> fd ::= ?; \<questiondown>f - d \<le> fd \<and> fd \<le> f + d?"

definition "plant \<equiv> {l` = fd, c` = 1 | 0 \<le> l \<and> c \<le> \<epsilon>}"

lemma disturbed_water_tank_safe:
  "H{0 \<le> l \<and> l \<le> m} (ctrl; act; plant)\<^sup>* {0\<le>l \<and> l \<le> m}"
  apply (rule hoare_kstar_inv)
  unfolding ctrl_def act_def plant_def
  (* find_local_flow *)
  apply (wlp_solve "\<lambda>t. [l \<leadsto> $fd * t + l, c \<leadsto> t + c]")
  apply expr_simp
  by (smt (z3) mult_left_mono pos_le_divide_eq zero_less_mult_iff)
end

dataspace uncertain_water_tank =
  constants
    m :: real
    \<epsilon> ::real
    U :: real
  assumes
    epsilon_nonneg: "0 \<le> \<epsilon>" and
    U_nonneg: "0 \<le> U"
  variables
    f :: real
    l :: real
    lu :: real
    c :: real

context uncertain_water_tank
begin

definition "tank_measure \<equiv> lu ::= ?; \<questiondown>l - U \<le> lu \<and> lu \<le> l + U?"

definition "ctrl \<equiv> f ::= ?; \<questiondown>-1 \<le> f \<and> f \<le> (m - (lu + U)) / \<epsilon>?; c ::= 0"

definition "plant \<equiv> {l` = f, c` = 1 | 0 \<le> l \<and> c \<le> \<epsilon>}"

lemma uncertain_water_tank_one_step:
  "H{0 \<le> l \<and> l \<le> m \<and> l - U \<le> lu \<and> lu \<le> l + U} ctrl; plant; tank_measure {0 \<le> l \<and> l \<le> m \<and> l - U \<le> lu \<and> lu \<le> l + U}"
  unfolding tank_measure_def ctrl_def plant_def
  apply (wlp_solve "\<lambda>t. [l \<leadsto> $f * t + l, c \<leadsto> t + c]")
  apply expr_simp
  by (smt (verit, best) mult_left_mono pos_le_divide_eq zero_less_mult_iff)

lemma uncertain_water_tank_safe: 
 "H{0 \<le> l \<and> l \<le> m \<and> l - U \<le> lu \<and> lu \<le> l + U} (ctrl; plant; tank_measure)\<^sup>* {0 \<le> l \<and> l \<le> m}"
  using hoare_kstar_inv uncertain_water_tank_one_step
  by (smt (verit, best) fbox_iso order_trans predicate1I)

end

dataspace uncertain_water_tank_control =
  constants
    m :: real
    \<epsilon> ::real
    U :: real
  assumes
    epsilon_nonneg: "0 \<le> \<epsilon>" and
    U_nonneg: "0 \<le> U"
  variables
    f :: real
    l :: real
    lu :: real
    c :: real

context uncertain_water_tank_control
begin

definition "tank_measure \<equiv> lu ::= ?; \<questiondown>l - U \<le> lu \<and> lu \<le> l + U?"

definition "ctrl \<equiv> f ::= ?; \<questiondown>-1 \<le> f \<and> f \<le> max 0 ((m - (lu + U)) / \<epsilon>)?; c ::= 0"

definition "plant \<equiv> {l` = f, c` = 1 | 0 \<le> l \<and> c \<le> \<epsilon>}"

lemma uncertain_water_tank_one_step:
  "H{0 \<le> l \<and> l \<le> m \<and> l - U \<le> lu \<and> lu \<le> l + U} ctrl; plant; tank_measure {0 \<le> l \<and> l \<le> m \<and> l - U \<le> lu \<and> lu \<le> l + U}"
  unfolding tank_measure_def ctrl_def plant_def
  apply (wlp_solve "\<lambda>t. [l \<leadsto> $f * t + l, c \<leadsto> t + c]")
  apply expr_simp
  by (smt (verit, best) mult_left_mono pos_le_divide_eq zero_less_mult_iff)

lemma uncertain_water_tank_safe: 
 "H{0 \<le> l \<and> l \<le> m \<and> l - U \<le> lu \<and> lu \<le> l + U} (ctrl; plant; tank_measure)\<^sup>* {0 \<le> l \<and> l \<le> m}"
  using hoare_kstar_inv uncertain_water_tank_one_step
  by (smt (verit, best) fbox_iso order_trans predicate1I)

end

end