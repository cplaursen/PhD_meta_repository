theory Brownian_Motion
  imports "Kolmogorov_Chentsov.Kolmogorov_Chentsov" Kernel_Product
begin

locale brownian_motion =
fixes W :: "(real, 'a, real) stochastic_process"
assumes init_0[simp]: "\<P>(x in proc_source W. W 0 x = 0) = 1"
    and indep_increments: "indep_increments W"
    and normal_increments: "\<And>s t. 0 \<le> s \<and> s < t \<Longrightarrow>
            distributed (proc_source W) borel (\<lambda>v. W t v - W s v)
             (normal_density 0 (sqrt (t-s)))"
    and AE_continuous: "AE x in proc_source W. continuous_on {0..} (\<lambda>t. W t x)"

text \<open> The following kernel gives rise to the Wiener process \<close>

definition Wiener_kernel :: "real \<Rightarrow> real hkernel" where
"Wiener_kernel i \<equiv> if i = 0 then hkernel (return_kernel borel)
   else hkernel_of borel (\<lambda>x dy. (return borel x \<star> density lborel (normal_density 0 i)) dy)"

lemma Wiener_kernel_0: "Wiener_kernel 0 = return_kernel borel"
  unfolding Wiener_kernel_def by (simp add: from_hkernel_inverse)

lemma transition_kernel_Wiener:
  assumes "i > 0"
  shows "transition_kernel borel borel (\<lambda>x dy. (return borel x \<star> density lborel (normal_density 0 i)) dy)"
  apply (rule transition_kernel.intro)
   apply (subst convolution_emeasure)
          apply auto
  using prob_space.finite_measure prob_space_normal_density assms apply blast
   apply (subst measurable_cong[OF nn_integral_return])
     apply measurable
    apply (simp_all add: measurable_cong[OF emeasure_density])
  by (metis measure_space sets_convolution space_borel space_convolution)

lemma kernel_Wiener:
  assumes "i \<ge>  0" "A \<in> sets borel"
  shows "kernel (Wiener_kernel i) \<omega> A = 
      (if i = 0 then return borel \<omega> A
       else (return borel \<omega> \<star> density lborel (normal_density 0 i)) A)"
  using assms unfolding Wiener_kernel_def apply (simp add: transition_kernel_Wiener)
  apply (transfer, auto)
  by (auto simp: transition_kernel_Wiener return_kernel_def from_hkernel_inverse)

end
