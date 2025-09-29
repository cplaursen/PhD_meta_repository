theory Planar_Flight
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

lemma hoare_disj_split:
  "H{P} F {R} \<Longrightarrow> H{Q} F {R} \<Longrightarrow> H{P \<or> Q} F {R}"
  unfolding fbox_def by (simp add: le_fun_def)

declare [[literal_variables]]

dataspace planar_flight =
  constants
    v\<^sub>o :: real (* own_velocity *)
    v\<^sub>i :: real (* intruder velocity *)
  assumes
    v\<^sub>o_pos: "v\<^sub>o > 0" and
    v\<^sub>i_pos: "v\<^sub>i > 0"
  variables (* Coordinates in reference frame of own ship *)
    x :: real (* Intruder x *)
    y :: real (* Intruder y *)
    \<theta> :: real (* Intruder angle *)
    \<omega> :: real (* Angular velocity *)

context planar_flight
begin

abbreviation "I \<equiv> (v\<^sub>i * sin \<theta> * x - (v\<^sub>i * cos \<theta> - v\<^sub>o) * y
                   > v\<^sub>o + v\<^sub>i)\<^sup>e"

abbreviation "J \<equiv> (v\<^sub>i * \<omega> * sin \<theta> * x - v\<^sub>i * \<omega> * cos \<theta> * y 
                  + v\<^sub>o * v\<^sub>i * cos \<theta> 
                  > v\<^sub>o * v\<^sub>i + v\<^sub>i * \<omega>)\<^sup>e"

definition "ctrl \<equiv> (\<omega> ::= 0; \<questiondown>@I?) \<sqinter> (\<omega> ::= 1; \<questiondown>@J?)"

definition "plant \<equiv> {x` = v\<^sub>i * cos \<theta> - v\<^sub>o + \<omega> * y,
                     y` = v\<^sub>i * sin \<theta> - \<omega> * x,
                     \<theta>` = -\<omega>}"

definition "flight \<equiv> (ctrl; plant)\<^sup>*"

lemma flight_safe: "H{x\<^sup>2 + y\<^sup>2 > 0} flight {x\<^sup>2 + y\<^sup>2 > 0}"
proof -
  have ctrl_post: "H{x\<^sup>2 + y\<^sup>2 > 0} ctrl {(\<omega> = 0 \<and> @I) \<or> (\<omega> = 1 \<and> @J)}"
    unfolding ctrl_def by wlp_full

  have plant_safe_I: "H{\<omega> = 0 \<and> @I} plant {x\<^sup>2 + y\<^sup>2 > 0}"
    unfolding plant_def apply (dInv "($\<omega> = 0 \<and> @I)\<^sup>e", dWeaken)
    using v\<^sub>o_pos v\<^sub>i_pos sum_squares_gt_zero_iff by fastforce

  have plant_safe_J: "H{\<omega> = 1 \<and> @J} plant {x\<^sup>2 + y\<^sup>2 > 0}"
    unfolding plant_def apply (dInv "(\<omega>=1 \<and> @J)\<^sup>e")
    apply (rule_tac diff_weak_on_rule, simp)
    apply expr_auto
    by (smt (verit, ccfv_SIG) cos_le_one mult_cancel_right mult_left_le
            mult_less_0_iff sum_power2_gt_zero_iff v\<^sub>i_pos v\<^sub>o_pos)

  show ?thesis
    unfolding flight_def apply (intro hoare_kstar_inv hoare_kcomp[OF ctrl_post])
    by (rule hoare_disj_split[OF plant_safe_I plant_safe_J])
qed

end
end
