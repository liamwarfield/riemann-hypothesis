module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.FourierProjections.PaUContinuous

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.FourierProjections.PaPolyTranslate
namespace ReciprocityTheory.ChartRestriction.G.I2.FPw

open MeasureTheory Complex

noncomputable section

variable {ι : Type} [Fintype ι]

open Classical

theorem paMono_eq (α : ι →₀ ℕ) (v : EuclideanSpace ℂ ι) : paMono α v = ∏ i, v i ^ α i := by
  simp [paMono, paPF, MvPolynomial.eval_monomial, Finsupp.prod_pow]

def jRot (j : ι) (u : Circle) : EuclideanSpace ℂ ι ≃ₗᵢ[ℝ] EuclideanSpace ℂ ι :=
  LinearIsometryEquiv.piLpCongrRight 2
    (fun i => if i = j then rotation u else LinearIsometryEquiv.refl ℝ ℂ)

theorem jRot_apply (j : ι) (u : Circle) (z : EuclideanSpace ℂ ι) (i : ι) :
    jRot j u z i = (if i = j then (u : ℂ) else 1) * z i := by
  by_cases h : i = j <;> simp [jRot, h, rotation_apply]

theorem paMono_rot (α : ι →₀ ℕ) (j : ι) (u : Circle) (z : EuclideanSpace ℂ ι) :
    paMono α (jRot j u z) = (u : ℂ) ^ (α j) * paMono α z := by
  rw [paMono_eq, paMono_eq]
  simp only [jRot_apply, mul_pow, Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_eq_single j]
  · simp
  · intro b _ hb
    simp [hb]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

theorem gaussianInner_monomial_orthogonal (q : ℕ) {α β : ι →₀ ℕ} (h : α ≠ β) : paIP q (paMono α) (paMono β) = 0 := by
  obtain ⟨j, hj⟩ : ∃ j, α j ≠ β j := by
    by_contra hc
    push_neg at hc
    exact h (Finsupp.ext hc)
  have hab : ((α j : ℝ) - β j) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hj)
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, ((α j : ℝ) - β j) * θ = Real.pi :=
    ⟨Real.pi / ((α j : ℝ) - β j), by field_simp⟩
  have hc : ((α j : ℂ) - β j) * θ = Real.pi := by exact_mod_cast hθ
  have hfac : ((Circle.exp θ : Circle) : ℂ) ^ (α j) *
      (starRingEnd ℂ) (((Circle.exp θ : Circle) : ℂ) ^ (β j)) = -1 := by
    rw [Circle.coe_exp, map_pow, ← Complex.exp_conj, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul,
      ← Complex.exp_add, ← Complex.exp_pi_mul_I]
    congr 1
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    linear_combination I * hc
  have hw : ∀ v, paW q (jRot j (Circle.exp θ) v) = paW q v := by
    intro v
    simp only [paW, LinearIsometryEquiv.norm_map]
  have key : ∀ v, paMono α (jRot j (Circle.exp θ) v) * (starRingEnd ℂ) (paMono β (jRot j (Circle.exp θ) v)) *
      (paW q (jRot j (Circle.exp θ) v) : ℂ) = -(paMono α v * (starRingEnd ℂ) (paMono β v) * (paW q v : ℂ)) := by
    intro v
    rw [paMono_rot, paMono_rot, hw, map_mul]
    linear_combination (paMono α v * (starRingEnd ℂ) (paMono β v) * (paW q v : ℂ)) * hfac
  have hI : paIP q (paMono α) (paMono β) = -paIP q (paMono α) (paMono β) := by
    unfold paIP
    rw [← integral_neg]
    conv_lhs =>
      rw [← ((jRot j (Circle.exp θ)).measurePreserving).integral_comp
        (jRot j (Circle.exp θ)).toHomeomorph.measurableEmbedding]
    congr 1
    funext v
    exact key v
  linear_combination hI / 2

private lemma finsupp_apply_le_degree (α : ι →₀ ℕ) (i : ι) : α i ≤ α.degree := by
  unfold Finsupp.degree
  by_cases h : i ∈ α.support
  · exact Finset.single_le_sum (fun j _ => Nat.zero_le (α j)) h
  · have h0 : α i = 0 := by simpa [Finsupp.mem_support_iff] using h
    rw [h0]
    exact Nat.zero_le _

private lemma mem_paS' {c : ℕ} {α : ι →₀ ℕ} : α ∈ paS (ι := ι) c ↔ α.degree ≤ c := by
  simp only [paS, Finset.mem_filter, Finset.mem_map, Fintype.mem_piFinset, Finset.mem_range,
    Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨_, h⟩
    exact h
  · intro h
    refine ⟨⟨α, fun i => ?_, ?_⟩, h⟩
    · have := finsupp_apply_le_degree α i
      omega
    · simp

private lemma finsupp_degree_eq_sum (α : ι →₀ ℕ) : α.degree = ∑ i, α i := by
  unfold Finsupp.degree
  exact Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => by simpa using hi)

private lemma paMono_mem_paPoly_of_degree_le {c : ℕ} {α : ι →₀ ℕ} (h : α.degree ≤ c) :
    paMono α ∈ paPoly (ι := ι) c := by
  unfold paPoly
  exact Submodule.subset_span ⟨α, mem_paS'.mpr h, rfl⟩

theorem paPoly_mono {c d : ℕ} (h : c ≤ d) : paPoly (ι := ι) c ≤ paPoly d := by
  unfold paPoly
  apply Submodule.span_mono
  apply Set.image_mono
  intro γ hγ
  exact mem_paS'.mpr (le_trans (mem_paS'.mp hγ) (by exact_mod_cast h))

theorem paPoly_contDiff {c : ℕ} {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c) :
    ContDiff ℂ (⊤ : ℕ∞) F := by
  unfold paPoly at hF
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨α, _, rfl⟩ := hx
    have he : paMono α = fun v : EuclideanSpace ℂ ι => ∏ i, v i ^ α i := funext (paMono_eq α)
    rw [he]
    exact contDiff_prod fun i _ =>
      ((EuclideanSpace.proj i : EuclideanSpace ℂ ι →L[ℂ] ℂ).contDiff).pow (α i)
  | zero => exact contDiff_const
  | add x y _ _ hx hy => exact hx.add hy
  | smul a x _ hx => exact hx.const_smul a

private lemma paMono_mul (α β : ι →₀ ℕ) :
    paMono α * paMono β = paMono (ι := ι) (α + β) := by
  funext v
  simp only [Pi.mul_apply, paMono_eq, Finsupp.add_apply, pow_add, Finset.prod_mul_distrib]

theorem paPoly_mul {c d : ℕ} {F G : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c) (hG : G ∈ paPoly d) :
    F * G ∈ paPoly (c + d) := by
  unfold paPoly at hF hG ⊢
  have hm := Submodule.mul_mem_mul hF hG
  rw [Submodule.span_mul_span] at hm
  refine Submodule.span_le.mpr (Set.mul_subset_iff.mpr ?_) hm
  rintro _ ⟨α, hα, rfl⟩ _ ⟨β, hβ, rfl⟩
  rw [paMono_mul]
  refine Submodule.subset_span ⟨α + β, mem_paS'.mpr ?_, rfl⟩
  rw [map_add (f := _)]
  exact add_le_add (mem_paS'.mp hα) (mem_paS'.mp hβ)

theorem paPoly_const (a : ℂ) : (fun _ : EuclideanSpace ℂ ι => a) ∈ paPoly 0 := by
  have h1 : paMono (0 : ι →₀ ℕ) = fun _ : EuclideanSpace ℂ ι => (1 : ℂ) := by
    funext v
    simp [paMono_eq]
  have h2 : (fun _ : EuclideanSpace ℂ ι => a) = a • paMono (0 : ι →₀ ℕ) := by
    rw [h1]
    funext v
    simp
  rw [h2]
  exact Submodule.smul_mem _ a (paMono_mem_paPoly_of_degree_le (by simp))

theorem paPoly_coord (i : ι) : (fun v : EuclideanSpace ℂ ι => v i) ∈ paPoly 1 := by
  have h1 : (fun v : EuclideanSpace ℂ ι => v i) = paMono (Finsupp.single i 1) := by
    funext v
    rw [paMono_eq, Finset.prod_eq_single i]
    · simp
    · intro b _ hb
      simp [Finsupp.single_apply, hb, Ne.symm hb]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  rw [h1]
  exact paMono_mem_paPoly_of_degree_le (le_of_eq (by rw [finsupp_degree_eq_sum]; simp [Finsupp.single_apply]))

theorem paPoly_pow {c : ℕ} {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c) (n : ℕ) :
    F ^ n ∈ paPoly (n * c) := by
  induction n with
  | zero =>
    rw [pow_zero, zero_mul]
    exact paPoly_const 1
  | succ n ih =>
    rw [pow_succ, add_mul, one_mul]
    exact paPoly_mul ih hF

private lemma prod_mem_paPoly (s : Finset ι) (f : ι → EuclideanSpace ℂ ι → ℂ) (d : ι → ℕ)
    (h : ∀ i ∈ s, f i ∈ paPoly (ι := ι) (d i)) : (∏ i ∈ s, f i) ∈ paPoly (∑ i ∈ s, d i) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    exact paPoly_const (ι := ι) 1
  | @insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    exact paPoly_mul (h j (Finset.mem_insert_self j s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem paPoly_translate {c : ℕ} {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c)
    (a : EuclideanSpace ℂ ι) : (fun v => F (v - a)) ∈ paPoly c := by
  unfold paPoly at hF
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨α, hα, rfl⟩ := hx
    have hdeg := mem_paS'.mp hα
    have he : (fun v => paMono α (v - a)) =
        ∏ i, ((fun v : EuclideanSpace ℂ ι => v i) - fun _ => a i) ^ (α i) := by
      funext v
      simp [paMono_eq, Finset.prod_apply]
    rw [he]
    have hi : ∀ i, ((fun v : EuclideanSpace ℂ ι => v i) - fun _ => a i) ∈ paPoly (ι := ι) 1 :=
      fun i => Submodule.sub_mem _ (paPoly_coord i) (paPoly_mono (Nat.zero_le 1) (paPoly_const (a i)))
    have hle : ∑ i, α i * 1 ≤ c := by
      rw [finsupp_degree_eq_sum] at hdeg
      simpa using hdeg
    exact paPoly_mono hle (prod_mem_paPoly Finset.univ _ (fun i => α i * 1)
      fun i _ => paPoly_pow (hi i) (α i))
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul b x _ hx => exact Submodule.smul_mem _ b hx

theorem paPoly_Hf (a : EuclideanSpace ℂ ι) : (fun v : EuclideanSpace ℂ ι => Hf v a) ∈ paPoly 1 := by
  have h1 : (fun v : EuclideanSpace ℂ ι => Hf v a) =
      ∑ i, (starRingEnd ℂ) (a i) • (fun v : EuclideanSpace ℂ ι => v i) := by
    funext v
    rw [Finset.sum_apply]
    simp only [Hf, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [h1]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (paPoly_coord i)

end

end ReciprocityTheory.ChartRestriction.G.I2.FPw
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.FourierProjections.IteratedFDerivTailZero
namespace ReciprocityTheory.ChartRestriction.G.I2.FPw

open MeasureTheory Complex

noncomputable section

variable {ι : Type} [Fintype ι]

open Classical

def expN (N : ℕ) (z : ℂ) : ℂ := ∑ n ∈ Finset.range (N + 1), z ^ n / (n.factorial : ℂ)

def gN (N : ℕ) (z : ℂ) : ℂ := cexp z - expN N z

theorem expN_hasDerivAt (N : ℕ) (z : ℂ) : HasDerivAt (expN (N + 1)) (expN N z) z := by
  induction N with
  | zero =>
    show HasDerivAt (expN 1) (expN 0 z) z
    have h0 : expN 1 = fun w => 1 + w := by
      funext w; simp [expN, Finset.sum_range_succ]
    have h1 : expN 0 z = 1 := by simp [expN]
    rw [h0, h1]
    exact (hasDerivAt_id z).const_add 1
  | succ N ih =>
    have hf : expN (N + 1 + 1) = fun w => expN (N + 1) w + w ^ (N + 1 + 1) / ((N + 1 + 1).factorial : ℂ) := by
      funext w; simp only [expN]; exact Finset.sum_range_succ _ (N + 1 + 1)
    rw [hf]
    have h2 := ih.add ((hasDerivAt_pow (N + 1 + 1) z).div_const ((N + 1 + 1).factorial : ℂ))
    refine h2.congr_deriv ?_
    have hf1 : ((N + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (N + 1)
    have hne : ((N + 1 + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (N + 1)
    simp only [expN, Finset.sum_range_succ _ (N + 1), Nat.factorial_succ (N + 1), Nat.add_sub_cancel]
    first
      | (congr 1; rw [Nat.cast_mul]; exact mul_div_mul_left _ _ hne)
      | (push_cast; field_simp; ring)
      | (push_cast; field_simp)

theorem contDiff_expN (N : ℕ) : ContDiff ℂ (⊤ : ℕ∞) (expN N) := by
  unfold expN
  first
    | exact ContDiff.sum fun n _ => (contDiff_id.pow n).div_const _
    | fun_prop

theorem contDiff_gN (N : ℕ) : ContDiff ℂ (⊤ : ℕ∞) (gN N) := by
  unfold gN
  exact Complex.contDiff_exp.sub (contDiff_expN N)

theorem deriv_gN (N : ℕ) : deriv (gN (N + 1)) = gN N := by
  funext z
  have h : HasDerivAt (gN (N + 1)) (cexp z - expN N z) z := by
    unfold gN
    exact (Complex.hasDerivAt_exp z).sub (expN_hasDerivAt N z)
  rw [h.deriv]
  rfl

theorem gN_zero (N : ℕ) : gN N 0 = 0 := by
  simp [gN, expN, Finset.sum_range_succ']

theorem iteratedDeriv_gN : ∀ i N : ℕ, i ≤ N → iteratedDeriv i (gN N) 0 = 0 := by
  intro i
  induction i with
  | zero => intro N _; rw [iteratedDeriv_zero]; exact gN_zero N
  | succ i ih =>
    intro N hN
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    rw [iteratedDeriv_succ', deriv_gN]
    exact ih M (by omega)

def ellL (q : ℕ) (a : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι →L[ℂ] ℂ :=
  ((q : ℂ) * (Real.pi : ℂ)) • innerSL ℂ a

theorem ellL_apply (q : ℕ) (a v : EuclideanSpace ℂ ι) : ellL q a v = q * Real.pi * Hf v a := by
  simp [ellL, Hf]
  left
  first
    | (rw [PiLp.inner_apply]; exact Finset.sum_congr rfl fun x _ => by simp [mul_comm])
    | (simp [PiLp.inner_apply, mul_comm]; done)
    | (simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]; done)

theorem iteratedFDeriv_tail_zero (q : ℕ) (a : EuclideanSpace ℂ ι) (N : ℕ) {P : EuclideanSpace ℂ ι → ℂ}
    (hP : ContDiff ℂ (⊤ : ℕ∞) P) {k : ℕ} (hk : k ≤ N) :
    iteratedFDeriv ℂ k (fun v => gN N (ellL q a v) * P v) 0 = 0 := by
  have hg : ContDiff ℂ (⊤ : ℕ∞) (fun v => gN N (ellL q a v)) := (contDiff_gN N).comp (ellL q a).contDiff
  have hz : ∀ i, i ≤ N → ‖iteratedFDeriv ℂ i (fun v => gN N (ellL q a v)) 0‖ = 0 := by
    intro i hi
    have h1 := (ellL q a).iteratedFDeriv_comp_right (contDiff_gN N) (0 : EuclideanSpace ℂ ι)
      (i := i) (by first | exact le_top | exact WithTop.coe_le_coe.mpr le_top | exact_mod_cast (le_top : (i : ℕ∞) ≤ ⊤) | simp)
    have h2 : iteratedFDeriv ℂ i (gN N) 0 = 0 := by
      rw [← norm_eq_zero, norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_gN i N hi, norm_zero]
    rw [map_zero, h2] at h1
    rw [show (fun v => gN N (ellL q a v)) = gN N ∘ ellL q a from rfl, h1, norm_eq_zero]
    ext m
    simp
  refine norm_le_zero_iff.mp ((norm_iteratedFDeriv_mul_le hg hP 0
    (by first | exact le_top | simp | exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))).trans_eq ?_)
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [hz i (by have := Finset.mem_range.mp hi; omega)]
  simp

theorem paD_tail_zero (q : ℕ) (a : EuclideanSpace ℂ ι) (N : ℕ) {P : EuclideanSpace ℂ ι → ℂ}
    (hP : ContDiff ℂ (⊤ : ℕ∞) P) {α : ι →₀ ℕ} (hα : α.degree ≤ N) :
    paD α (fun v => gN N (ellL q a v) * P v) = 0 := by
  unfold paD polyDeriv
  refine Finset.sum_eq_zero fun m hm => ?_
  have hmα : m = α := by
    first
      | (simp [MvPolynomial.support_monomial] at hm; exact hm)
      | (rw [MvPolynomial.support_monomial] at hm; split_ifs at hm with h
         · simp at hm
         · simpa using hm)
  subst hmα
  have hk : Multiset.card (Finsupp.toMultiset m) ≤ N := by
    rw [Finsupp.card_toMultiset]
    first
      | exact hα
      | simpa [Finsupp.degree, Finsupp.sum] using hα
  rw [iteratedFDeriv_tail_zero q a N hP hk]
  simp

end

end ReciprocityTheory.ChartRestriction.G.I2.FPw
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.FourierProjections.PaIPZeroRight
namespace ReciprocityTheory.ChartRestriction.G.I2.FPw

open MeasureTheory Complex

noncomputable section

variable {ι : Type} [Fintype ι]

open Classical

theorem paD_add (α : ι →₀ ℕ) {H1 H2 : EuclideanSpace ℂ ι → ℂ} (h1 : ContDiff ℂ (⊤ : ℕ∞) H1)
    (h2 : ContDiff ℂ (⊤ : ℕ∞) H2) : paD α (H1 + H2) = paD α H1 + paD α H2 := by
  unfold paD polyDeriv
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [iteratedFDeriv_add_apply (h1.contDiffAt.of_le (by exact_mod_cast le_top))
    (h2.contDiffAt.of_le (by exact_mod_cast le_top))]
  simp [mul_add]

theorem paD_smul (α : ι →₀ ℕ) (a : ℂ) {H : EuclideanSpace ℂ ι → ℂ}
    (h : ContDiff ℂ (⊤ : ℕ∞) H) : paD α (a • H) = a * paD α H := by
  unfold paD polyDeriv
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [iteratedFDeriv_const_smul_apply (h.contDiffAt.of_le (by exact_mod_cast le_top))]
  simp only [ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  ring

theorem paD_zero (α : ι →₀ ℕ) : paD α (0 : EuclideanSpace ℂ ι → ℂ) = 0 := by
  simp [paD, polyDeriv, iteratedFDeriv_fun_zero]

theorem paFact_ne (α : ι →₀ ℕ) : (paFact α : ℂ) ≠ 0 := by
  unfold paFact
  exact Nat.cast_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => Nat.factorial_ne_zero _)

theorem paJet_add (c : ℕ) {H1 H2 : EuclideanSpace ℂ ι → ℂ} (h1 : ContDiff ℂ (⊤ : ℕ∞) H1)
    (h2 : ContDiff ℂ (⊤ : ℕ∞) H2) : paJet c (H1 + H2) = paJet c H1 + paJet c H2 := by
  unfold paJet
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [paD_add α h1 h2, add_div, add_smul]

theorem paJet_smul (c : ℕ) (r : ℂ) {H : EuclideanSpace ℂ ι → ℂ} (h : ContDiff ℂ (⊤ : ℕ∞) H) :
    paJet c (r • H) = r • paJet c H := by
  unfold paJet
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [paD_smul α r h, mul_div_assoc, smul_smul]

theorem paJet_zero (c : ℕ) : paJet c (0 : EuclideanSpace ℂ ι → ℂ) = 0 := by
  unfold paJet
  simp [paD_zero]

theorem paJet_mono (c : ℕ) (m : ι →₀ ℕ) :
    paJet c (paMono m) = if m ∈ paS c then paMono m else 0 := by
  unfold paJet
  simp only [paD_mono]
  have e : ∀ α, ((if α = m then (paFact α : ℂ) else 0) / paFact α) • paMono α =
      if α = m then paMono m else 0 := fun α => by
    split_ifs with h
    · subst h
      rw [div_self (paFact_ne α), one_smul]
    · rw [zero_div, zero_smul]
  simp only [e]
  rw [Finset.sum_ite_eq']

theorem gaussianInner_zero_left (q : ℕ) (G : EuclideanSpace ℂ ι → ℂ) : paIP q 0 G = 0 := by
  simp [paIP]

theorem gaussianInner_zero_right (q : ℕ) (F : EuclideanSpace ℂ ι → ℂ) : paIP q F 0 = 0 := by
  simp [paIP]

theorem gaussianInner_monomial_high {q c : ℕ} (hq : 1 ≤ q) {m : ι →₀ ℕ} (hm : m ∉ paS c)
    {G : EuclideanSpace ℂ ι → ℂ} (hG : G ∈ paPoly c) : paIP q (paMono m) G = 0 := by
  have hmm : paMono m ∈ paPoly (ι := ι) (max c m.degree) :=
    paMono_mem (mem_paS.2 (le_max_right _ _))
  have hup : paPoly (ι := ι) c ≤ paPoly (max c m.degree) := paPoly_mono (le_max_left _ _)
  induction hG using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨β, hβ, rfl⟩ := hx
    exact gaussianInner_monomial_orthogonal q (by rintro rfl; exact hm hβ)
  | zero => exact gaussianInner_zero_right q _
  | add x y hx hy ihx ihy =>
    rw [gaussianInner_conj_symm q (x + y) (paMono m), gaussianInner_add_left hq (hup hx) (hup hy) hmm, map_add (f := _),
      ← gaussianInner_conj_symm, ← gaussianInner_conj_symm, ihx, ihy, add_zero]
  | smul r x hx ihx =>
    rw [gaussianInner_conj_symm q (r • x) (paMono m), gaussianInner_smul_left, map_mul, ← gaussianInner_conj_symm, ihx, mul_zero]

theorem gaussianInner_polynomial_jet {q c d : ℕ} (hq : 1 ≤ q) {S G : EuclideanSpace ℂ ι → ℂ} (hS : S ∈ paPoly d)
    (hG : G ∈ paPoly c) : paIP q S G = paIP q (paJet c S) G := by
  have hupd : paPoly (ι := ι) d ≤ paPoly (max d c) := paPoly_mono (le_max_left _ _)
  have hupc : paPoly (ι := ι) c ≤ paPoly (max d c) := paPoly_mono (le_max_right _ _)
  induction hS using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    rw [paJet_mono]
    split_ifs with h
    · rfl
    · rw [gaussianInner_monomial_high hq h hG, gaussianInner_zero_left]
  | zero => rw [paJet_zero]
  | add x y hx hy ihx ihy =>
    rw [paJet_add c (paPoly_contDiff hx) (paPoly_contDiff hy),
      gaussianInner_add_left hq (hupd hx) (hupd hy) (hupc hG),
      gaussianInner_add_left hq (hupc (paJet_mem c x)) (hupc (paJet_mem c y)) (hupc hG), ihx, ihy]
  | smul r x hx ihx =>
    rw [paJet_smul c r (paPoly_contDiff hx), gaussianInner_smul_left, gaussianInner_smul_left, ihx]

end

end ReciprocityTheory.ChartRestriction.G.I2.FPw
end

namespace ReciprocityTheory.ChartRestriction.G.I2.FPw

open MeasureTheory Complex Filter Topology

noncomputable section

variable {ι : Type} [Fintype ι]

open Classical

def Pf (q : ℕ) (a : EuclideanSpace ℂ ι) (F : EuclideanSpace ℂ ι → ℂ) (v : EuclideanSpace ℂ ι) : ℂ :=
  F (v - a) / cexp (q * Real.pi * Hf a a / 2)

theorem paU_eq (q : ℕ) (a : EuclideanSpace ℂ ι) (F : EuclideanSpace ℂ ι → ℂ) (v : EuclideanSpace ℂ ι) :
    paU q a F v = expN 0 0 * 0 + (expN 0 0 - 1) * 0 + cexp (ellL q a v) * Pf q a F v := by
  have h0 : expN 0 0 = 1 := by simp [expN]
  rw [h0, paU, Pf, ellL_apply, Complex.exp_sub]; ring

theorem paU_split (q : ℕ) (a : EuclideanSpace ℂ ι) (F : EuclideanSpace ℂ ι → ℂ) (N : ℕ) (v : EuclideanSpace ℂ ι) :
    paU q a F v = expN N (ellL q a v) * Pf q a F v + gN N (ellL q a v) * Pf q a F v := by
  rw [paU_eq]
  unfold gN
  ring

theorem Pf_mem {q c : ℕ} (a : EuclideanSpace ℂ ι) {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c) :
    Pf q a F ∈ paPoly c := by
  have : Pf q a F = (cexp (q * Real.pi * Hf a a / 2))⁻¹ • (fun v => F (v - a)) := by
    funext v; simp [Pf, div_eq_inv_mul]
  rw [this]; exact Submodule.smul_mem _ _ (paPoly_translate hF a)

theorem ell_mem (q : ℕ) (a : EuclideanSpace ℂ ι) : (fun v => ellL q a v) ∈ paPoly 1 := by
  have : (fun v => ellL q a v) = ((q : ℂ) * (Real.pi : ℂ)) • (fun v : EuclideanSpace ℂ ι => Hf v a) := by
    funext v; simp [ellL_apply, mul_assoc]
  rw [this]; exact Submodule.smul_mem _ _ (paPoly_Hf a)

theorem expN_ell_mem (q : ℕ) (a : EuclideanSpace ℂ ι) (N : ℕ) :
    (fun v => expN N (ellL q a v)) ∈ paPoly N := by
  have : (fun v => expN N (ellL q a v)) = ∑ n ∈ Finset.range (N + 1),
      ((n.factorial : ℂ))⁻¹ • (fun v => ellL q a v) ^ n := by
    funext v; simp [expN, Finset.sum_apply, div_eq_inv_mul]
  rw [this]
  refine Submodule.sum_mem _ fun n hn => Submodule.smul_mem _ _ ?_
  have h := paPoly_pow (ell_mem q a) n
  rw [mul_one] at h
  exact paPoly_mono (by have := Finset.mem_range.1 hn; omega) h

theorem S_mem {q c : ℕ} (a : EuclideanSpace ℂ ι) {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c) (N : ℕ) :
    (fun v => expN N (ellL q a v) * Pf q a F v) ∈ paPoly (N + c) :=
  paPoly_mul (expN_ell_mem q a N) (Pf_mem a hF)

theorem Pf_contDiff {q c : ℕ} (a : EuclideanSpace ℂ ι) {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c) :
    ContDiff ℂ (⊤ : ℕ∞) (Pf q a F) := paPoly_contDiff (Pf_mem a hF)

theorem T_contDiff {q c : ℕ} (a : EuclideanSpace ℂ ι) {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c) (N : ℕ) :
    ContDiff ℂ (⊤ : ℕ∞) (fun v => gN N (ellL q a v) * Pf q a F v) :=
  ((contDiff_gN N).comp (ellL q a).contDiff).mul (Pf_contDiff a hF)

theorem jet_eq {q c : ℕ} (a : EuclideanSpace ℂ ι) {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c) {N : ℕ}
    (hN : c ≤ N) : paJet c (paU q a F) = paJet c (fun v => expN N (ellL q a v) * Pf q a F v) := by
  have hs : paU q a F = (fun v => expN N (ellL q a v) * Pf q a F v) +
      (fun v => gN N (ellL q a v) * Pf q a F v) := by
    funext v; rw [paU_split q a F N v]; rfl
  rw [hs, paJet_add c (paPoly_contDiff (S_mem a hF N)) (T_contDiff a hF N)]
  have hT : paJet c (fun v => gN N (ellL q a v) * Pf q a F v) = 0 := by
    unfold paJet
    refine Finset.sum_eq_zero fun α hα => ?_
    rw [paD_tail_zero q a N (Pf_contDiff a hF) ((paS_deg hα).trans hN), zero_div, zero_smul]
  rw [hT, add_zero]

theorem gN_norm_le (N : ℕ) (z : ℂ) : ‖gN N z‖ ≤ Real.exp ‖z‖ := by
  have h := Complex.norm_exp_sub_sum_le_exp_norm_sub_sum z (N + 1)
  have h2 : 0 ≤ ∑ i ∈ Finset.range (N + 1), ‖z‖ ^ i / (i.factorial : ℝ) :=
    Finset.sum_nonneg fun i _ => by positivity
  unfold gN expN
  linarith

theorem gN_tendsto (z : ℂ) : Tendsto (fun N => gN N z) atTop (𝓝 0) := by
  unfold gN
  have h := (NormedSpace.expSeries_div_hasSum_exp z).tendsto_sum_nat
  rw [← Complex.exp_eq_exp_ℂ] at h
  have h2 : Tendsto (fun N => expN N z) atTop (𝓝 (cexp z)) := by
    unfold expN
    exact h.comp (tendsto_add_atTop_nat 1)
  have h3 := (tendsto_const_nhds (x := cexp z)).sub h2
  rw [sub_self] at h3
  exact h3

theorem ell_norm_le (q : ℕ) (a v : EuclideanSpace ℂ ι) : ‖ellL q a v‖ ≤ q * Real.pi * (‖a‖ * ‖v‖) := by
  unfold ellL
  rw [ContinuousLinearMap.smul_apply, norm_smul]
  have h1 : ‖((innerSL ℂ) a) v‖ ≤ ‖a‖ * ‖v‖ := norm_inner_le_norm (𝕜 := ℂ) a v
  have h2 : ‖((q : ℂ) * (Real.pi : ℂ))‖ = q * Real.pi := by
    rw [norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [h2]
  exact mul_le_mul_of_nonneg_left h1 (by positivity)

theorem tail_tendsto {q c : ℕ} (hq : 1 ≤ q) (a : EuclideanSpace ℂ ι) {F G : EuclideanSpace ℂ ι → ℂ}
    (hF : F ∈ paPoly c) (hG : G ∈ paPoly c) :
    (∀ N, Integrable (fun v => gN N (ellL q a v) * Pf q a F v * (starRingEnd ℂ) (G v) * (paW q v : ℂ))) ∧
    Tendsto (fun N => paIP q (fun v => gN N (ellL q a v) * Pf q a F v) G) atTop (𝓝 0) := by
  obtain ⟨C1, hC1, h1⟩ := paPoly_growth hF
  obtain ⟨C2, hC2, h2⟩ := paPoly_growth hG
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hb : 0 < (q : ℝ) * Real.pi / 2 := by positivity
  set κ : ℝ := ‖cexp (q * Real.pi * Hf a a / 2)‖⁻¹ with hκ
  have hκ0 : 0 ≤ κ := by positivity
  set K : ℝ := κ * C1 * C2 * (1 + ‖a‖) ^ c * Real.exp (q * Real.pi * ‖a‖ ^ 2 / 2) with hK
  have hK0 : 0 ≤ K := by positivity
  set B : EuclideanSpace ℂ ι → ℝ := fun v => K * ((1 + ‖v‖) ^ (2 * c) *
    Real.exp (-((q : ℝ) * Real.pi / 2) * ‖v‖ ^ 2)) with hB
  have hBi : Integrable B := by
    refine Integrable.const_mul (pa_integrable_of_le (by fun_prop) (2 * c) hb zero_le_one (fun v => ?_)) K
    rw [one_mul, Real.norm_of_nonneg (by positivity)]
  set Fn : ℕ → EuclideanSpace ℂ ι → ℂ := fun N v =>
    gN N (ellL q a v) * Pf q a F v * (starRingEnd ℂ) (G v) * (paW q v : ℂ) with hFn
  have hcont : ∀ N, Continuous (Fn N) := by
    intro N
    have := (T_contDiff (q := q) a hF N).continuous
    have := paPoly_continuous hG
    have := paW_continuous (ι := ι) q
    simp only [hFn]
    fun_prop
  have hbound : ∀ N v, ‖Fn N v‖ ≤ B v := by
    intro N v
    have hg := (gN_norm_le N (ellL q a v)).trans (Real.exp_le_exp.2 (ell_norm_le q a v))
    have hP : ‖Pf q a F v‖ ≤ κ * (C1 * ((1 + ‖v‖) ^ c * (1 + ‖a‖) ^ c)) := by
      rw [Pf, norm_div, div_eq_mul_inv, mul_comm, hκ]
      refine mul_le_mul_of_nonneg_left ((h1 _).trans (mul_le_mul_of_nonneg_left ?_ hC1)) hκ0
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity)
        (by nlinarith [norm_sub_le v a, norm_nonneg v, norm_nonneg a,
          mul_nonneg (norm_nonneg v) (norm_nonneg a)]) c
    have hGv := h2 v
    have hw : Real.exp (q * Real.pi * (‖a‖ * ‖v‖)) * paW q v ≤
        Real.exp (q * Real.pi * ‖a‖ ^ 2 / 2) * Real.exp (-((q : ℝ) * Real.pi / 2) * ‖v‖ ^ 2) := by
      rw [paW, ← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.2
      have : 0 ≤ (q : ℝ) * Real.pi * (‖v‖ - ‖a‖) ^ 2 := by positivity
      nlinarith
    simp only [hFn, hB, hK, norm_mul, RCLike.norm_conj, Complex.norm_real,
      Real.norm_of_nonneg (paW_pos q v).le]
    have e0 := norm_nonneg (gN N (ellL q a v))
    have e1 := norm_nonneg (Pf q a F v)
    have e2 := norm_nonneg (G v)
    have e3 := (paW_pos q v).le
    have e4 := Real.exp_pos (q * Real.pi * (‖a‖ * ‖v‖))
    calc ‖gN N (ellL q a v)‖ * ‖Pf q a F v‖ * ‖G v‖ * paW q v
        ≤ Real.exp (q * Real.pi * (‖a‖ * ‖v‖)) * (κ * (C1 * ((1 + ‖v‖) ^ c * (1 + ‖a‖) ^ c))) *
            (C2 * (1 + ‖v‖) ^ c) * paW q v := by gcongr
      _ = κ * C1 * C2 * (1 + ‖a‖) ^ c * ((1 + ‖v‖) ^ c * (1 + ‖v‖) ^ c) *
            (Real.exp (q * Real.pi * (‖a‖ * ‖v‖)) * paW q v) := by ring
      _ ≤ κ * C1 * C2 * (1 + ‖a‖) ^ c * ((1 + ‖v‖) ^ c * (1 + ‖v‖) ^ c) *
            (Real.exp (q * Real.pi * ‖a‖ ^ 2 / 2) * Real.exp (-((q : ℝ) * Real.pi / 2) * ‖v‖ ^ 2)) := by
          gcongr
      _ = _ := by rw [two_mul, pow_add]; ring
  have hint : ∀ N, Integrable (Fn N) := fun N =>
    hBi.mono' (hcont N).aestronglyMeasurable (Filter.Eventually.of_forall (hbound N))
  refine ⟨hint, ?_⟩
  have hlim : ∀ v, Tendsto (fun N => Fn N v) atTop (𝓝 0) := by
    intro v
    have := (((gN_tendsto (ellL q a v)).mul_const (Pf q a F v)).mul_const ((starRingEnd ℂ) (G v))).mul_const
      ((paW q v : ℝ) : ℂ)
    simpa only [zero_mul] using this
  have := tendsto_integral_of_dominated_convergence B (fun N => (hcont N).aestronglyMeasurable) hBi
    (fun N => Filter.Eventually.of_forall (hbound N)) (Filter.Eventually.of_forall hlim)
  rw [integral_zero] at this
  exact this

theorem gaussianInner_jet' {q c : ℕ} (hq : 1 ≤ q) (a : EuclideanSpace ℂ ι) {F G : EuclideanSpace ℂ ι → ℂ}
    (hF : F ∈ paPoly c) (hG : G ∈ paPoly c) :
    paIP q (paU q a F) G = paIP q (paJet c (paU q a F)) G := by
  obtain ⟨hTi, hT⟩ := tail_tendsto hq a hF hG
  have hD : ∀ N, c ≤ N → paIP q (paU q a F) G - paIP q (paJet c (paU q a F)) G =
      paIP q (fun v => gN N (ellL q a v) * Pf q a F v) G := by
    intro N hN
    have hS := S_mem (q := q) a hF N
    have hGS : G ∈ paPoly (N + c) := paPoly_mono (by omega) hG
    have hSi := gaussianInner_integrable hq hS hGS
    have e1 : paIP q (paU q a F) G = paIP q (fun v => expN N (ellL q a v) * Pf q a F v) G +
        paIP q (fun v => gN N (ellL q a v) * Pf q a F v) G := by
      unfold paIP
      rw [← integral_add hSi (hTi N)]
      congr 1; funext v
      rw [paU_split q a F N v]; ring
    rw [e1, jet_eq a hF hN, ← gaussianInner_polynomial_jet hq hS hG]
    ring
  have hev : (fun N => paIP q (fun v => gN N (ellL q a v) * Pf q a F v) G) =ᶠ[atTop]
      (fun _ => paIP q (paU q a F) G - paIP q (paJet c (paU q a F)) G) :=
    Filter.eventually_atTop.2 ⟨c, fun N hN => (hD N hN).symm⟩
  have h0 := tendsto_nhds_unique (hT.congr' hev) tendsto_const_nhds
  exact sub_eq_zero.1 h0.symm

end

end ReciprocityTheory.ChartRestriction.G.I2.FPw
