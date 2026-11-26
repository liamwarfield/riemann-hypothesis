module

public import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.ClosedGraph

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.PKerSwap
open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix Filter Topology
open scoped ContDiff ComplexConjugate

noncomputable section

namespace MainStatements.WeightKernel

theorem kerSwap : KerUnif → KerSwap := by
  intro hU H _ _ _ _ _ _ _ _ n ι hι μ _ Ω I _ _ m _ c q hk P _ _ _ W p K C hW hp hK hC hWC
  obtain ⟨B, hB⟩ := hU H n ι hι Ω I m c q hk P W p K C hW hp hK hC hWC
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have : IsFiniteMeasure (μ.restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  have hmc : Continuous (matCoord ι) := hι.continuous
  set G : H × H → ℂ := fun z => W (matCoord ι z.1, p z.2) with hG
  have hGc : Continuous G := hW.continuous.comp ((hmc.comp continuous_fst).prodMk (hp.comp continuous_snd))
  set F : H → Ω → ℂ := fun k x => ker c q (fun y => W (matCoord ι y, p k)) x with hF

  have hvan : ∀ x, ∀ k ∈ K, ∀ i, i ∉ (hk.fin x C hC).toFinset → c i x * W (matCoord ι (q i x), p k) = 0 := by
    intro x k hkK i hi
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_and_or, not_not] at hi
    rcases hi with h | h
    · simp [h]
    · simp [hWC k hkK _ h]

  have hmeas : AEStronglyMeasurable (Function.uncurry F) ((μ.restrict K).prod m) := by
    obtain ⟨u, hu⟩ := (atTop : Filter (Finset I)).exists_seq_tendsto
    refine aestronglyMeasurable_of_tendsto_ae (u := atTop)
      (f := fun N (z : H × Ω) => ∑ i ∈ u N, c i z.2 * W (matCoord ι (q i z.2), p z.1)) ?_ ?_
    · intro N
      refine (Finset.measurable_sum _ fun i _ => ?_).aestronglyMeasurable
      refine ((hk.mc i).comp measurable_snd).mul ?_
      have : Measurable fun z : H × Ω => ((q i z.2, z.1) : H × H) :=
        ((hk.mq i).comp measurable_snd).prodMk measurable_fst
      exact hGc.measurable.comp this
    · have hae : ∀ᵐ z ∂((μ.restrict K).prod m), z.1 ∈ K :=
        Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst (ae_restrict_mem hKm)
      filter_upwards [hae] with z hz
      have hs : HasSum (fun i => c i z.2 * W (matCoord ι (q i z.2), p z.1))
          (∑' i, c i z.2 * W (matCoord ι (q i z.2), p z.1)) :=
        (summable_of_ne_finset_zero (s := (hk.fin z.2 C hC).toFinset) (hvan z.2 z.1 hz)).hasSum
      exact hs.comp hu
  have hint : Integrable (Function.uncurry F) ((μ.restrict K).prod m) := by
    rw [integrable_prod_iff hmeas]
    refine ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem hKm] with k hkK
      exact (hB k hkK).1
    · refine Integrable.mono' (integrable_const B) hmeas.norm.integral_prod_right' ?_
      filter_upwards [ae_restrict_mem hKm] with k hkK
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      exact (hB k hkK).2
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [hF, ker]
  have hT := hvan x
  set T := (hk.fin x C hC).toFinset
  rw [setIntegral_congr_fun hKm (fun k hkK => tsum_eq_sum (s := T) (hT k hkK))]
  rw [integral_finsetSum]
  · rw [tsum_eq_sum (s := T)]
    · refine Finset.sum_congr rfl fun i _ => ?_
      exact integral_const_mul _ _
    · intro i hi
      simp only [T, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_and_or, not_not] at hi
      rcases hi with h | h
      · simp [h]
      · rw [setIntegral_eq_zero_of_forall_eq_zero (fun k hkK => hWC k hkK _ h), mul_zero]
  · intro i _
    exact (ContinuousOn.integrableOn_compact hK
      (continuous_const.mul (hW.continuous.comp (continuous_const.prodMk hp))).continuousOn)

end MainStatements.WeightKernel
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.PIdentTwo
open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix
open scoped ContDiff ComplexConjugate

noncomputable section

namespace MainStatements.WeightKernel

theorem identTwo : IdentTwo := by
  intro H _ _ _ _ _ _ _ _ n ι hc s B hB μ _ _ dt _ _ φ hφc hφs hO h
  have : μ.IsInvInvariant := GlobalTheory.SqIntRep.isInvInvariant_of_unimodular μ
  set f : H → ℂ := fun z => φ (z⁻¹ * s * z) * (B (matCoord ι (z⁻¹ * s * z), matCoord ι (z⁻¹ * h)) : ℂ) with hfdef
  set F : H → ℂ := fun k => φ (k * (h⁻¹ * s * h) * k⁻¹) *
    (B (matCoord ι (k * (h⁻¹ * s * h) * k⁻¹), matCoord ι k) : ℂ) with hFdef
  have hsub : ∫ k, F k ∂μ = ∫ z, f z ∂μ := by
    have h1 := integral_mul_right_eq_self (μ := μ) (fun k => F k) h
    have h2 := integral_inv_eq_self (fun k => F (k * h)) μ
    rw [← h1, ← h2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    have e : z⁻¹ * h * (h⁻¹ * s * h) * (z⁻¹ * h)⁻¹ = z⁻¹ * s * z := by group
    simp only [hFdef, hfdef, e]
  have hBc : Continuous B := hB.smooth.continuous
  have hfc : Continuous f := by
    have h1 : Continuous fun z : H => z⁻¹ * s * z := by fun_prop
    have h2 : Continuous fun z : H => z⁻¹ * h := by fun_prop
    exact (hφc.comp h1).mul (Complex.continuous_ofReal.comp (hBc.comp ((hc.comp h1).prodMk (hc.comp h2))))
  obtain ⟨K, hK, hKp⟩ := hB.proper (tsupport φ) {h⁻¹ * s * h} hφs isCompact_singleton
  have hfs : HasCompactSupport f := by
    refine HasCompactSupport.intro (hK.image (f := fun k => h * k⁻¹) (by fun_prop)) fun z hz => ?_
    by_contra hne
    apply hz
    have hne' : φ (z⁻¹ * s * z) * (B (matCoord ι (z⁻¹ * s * z), matCoord ι (z⁻¹ * h)) : ℂ) ≠ 0 := hne
    have m1 : z⁻¹ * s * z ∈ tsupport φ := subset_tsupport _ (left_ne_zero_of_mul hne')
    have m2 : B (matCoord ι (z⁻¹ * s * z), matCoord ι (z⁻¹ * h)) ≠ 0 := by
      intro h0; apply hne'; rw [h0]; simp
    have m3 : (z * (z⁻¹ * h))⁻¹ * s * (z * (z⁻¹ * h)) ∈ ({h⁻¹ * s * h} : Set H) := by
      rw [mul_inv_cancel_left]; exact Set.mem_singleton _
    exact ⟨z⁻¹ * h, hKp z (z⁻¹ * h) m1 m3 m2, by group⟩
  have hfi : Integrable f μ := hfc.integrable_of_hasCompactSupport hfs
  have hW := (weil_integral (T := cent s) (dt := dt) (dh := μ) (isClosed_cent s) hfi).2.2
  set κ : ℂ := ∫ t : cent s, (B (matCoord ι s, matCoord ι ((t : H)⁻¹)) : ℂ) ∂dt with hκ
  have hfib : ∀ x, ∫ t : cent s, f (t * x) ∂dt = φ (x⁻¹ * s * x) * κ := by
    intro x
    obtain ⟨t₀, ht₀, hsh⟩ := hB.shift x h 1 1
    have e1 : ∀ t : cent s, ((t : H) * x)⁻¹ * s * ((t : H) * x) = x⁻¹ * s * x := by
      intro t
      have hts := mem_cent.1 t.2
      have : (t : H)⁻¹ * s * t = s := by rw [mul_assoc, ← hts, inv_mul_cancel_left]
      calc ((t : H) * x)⁻¹ * s * ((t : H) * x) = x⁻¹ * ((t : H)⁻¹ * s * t) * x := by group
        _ = x⁻¹ * s * x := by rw [this]
    have e2 : ∀ t : cent s, f (t * x) = φ (x⁻¹ * s * x) *
        (B (matCoord ι s, matCoord ι ((((⟨t₀, ht₀⟩ : cent s)⁻¹ * t : cent s) : H)⁻¹)) : ℂ) := by
      intro t
      have hs' := hsh (t : H)⁻¹ (inv_mem t.2)
      simp only [inv_one, one_mul, mul_one] at hs'
      have hco : (t : H)⁻¹ * t₀ = ((((⟨t₀, ht₀⟩ : cent s)⁻¹ * t : cent s) : H))⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, _root_.mul_inv_rev, inv_inv]
      simp only [hfdef, e1]
      rw [show ((t : H) * x)⁻¹ * h = x⁻¹ * (t : H)⁻¹ * h by group, hs', hco]
    simp_rw [e2]
    rw [integral_const_mul]
    congr 1
    exact integral_mul_left_eq_self (fun t : cent s => (B (matCoord ι s, matCoord ι ((t : H))⁻¹) : ℂ)) _
  have hfun : (fun x => ∫ t : cent s, f (t * x) ∂dt) = fun x => conjFn s φ x * κ := funext fun x => hfib x
  show ∫ k, F k ∂μ = 0
  rw [hsub, ← hW, hfun]
  have h0 := hO.2
  unfold quotInt descend at h0 ⊢
  show ∫ q, conjFn s φ q.out * κ ∂quotMeas (cent s) dt μ = 0
  rw [integral_mul_const, h0, zero_mul]

end MainStatements.WeightKernel

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.PBoundT
open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix
open scoped ContDiff ComplexConjugate

noncomputable section

namespace MainStatements.WeightKernel.PBoundT

lemma entry {n : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) (l : Fin n → ℂ)
    (h : (diagonal l)ᴴ * J * diagonal l = J) (i j : Fin n) (hJ : J i j ≠ 0) :
    star (l i) * l j = 1 := by
  have e := congrFun (congrFun h i) j
  rw [diagonal_conjTranspose, mul_diagonal, diagonal_mul] at e
  have e2 : (star (l i) * l j - 1) * J i j = 0 := by
    simp only [Pi.star_apply] at e
    linear_combination e
  exact sub_eq_zero.mp ((mul_eq_zero.mp e2).resolve_right hJ)

lemma norm_entry {n : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) (l : Fin n → ℂ)
    (h : (diagonal l)ᴴ * J * diagonal l = J) (i j : Fin n) (hJ : J i j ≠ 0) :
    ‖l i‖ * ‖l j‖ = 1 := by
  have e := congrArg (fun x : ℂ => ‖x‖) (entry J l h i j hJ)
  simpa [norm_mul, norm_star] using e

end MainStatements.WeightKernel.PBoundT

namespace MainStatements.WeightKernel

open PBoundT in
theorem boundT : BoundT := by
  intro n J l hdet hinj hl a b ha
  refine ⟨max b (max (1 / a) 1), ?_⟩
  intro τ hτ hbd j
  have col : ∃ i, J i j ≠ 0 := by
    by_contra hc
    push_neg at hc
    have : J.det = 0 := Matrix.det_eq_zero_of_column_eq_zero j hc
    rw [this] at hdet
    exact not_isUnit_zero hdet
  obtain ⟨i, hij⟩ := col
  have hl2 := norm_entry J l hl i j hij
  have hτ2 := norm_entry J τ hτ i j hij
  rcases lt_trichotomy ‖l j‖ 1 with hlt | heq | hgt
  · have hli : 1 < ‖l i‖ := by
      by_contra hc
      push_neg at hc
      have h0 : 0 ≤ ‖l j‖ := norm_nonneg _
      nlinarith
    have ha' := (hbd i hli).1
    have hτj : ‖τ j‖ ≤ 1 / a := by
      rw [le_div_iff₀ ha]
      have h0 : 0 ≤ ‖τ j‖ := norm_nonneg _
      nlinarith
    exact le_trans hτj (le_trans (le_max_left _ _) (le_max_right _ _))
  · have hli : ‖l i‖ = 1 := by
      rw [heq, mul_one] at hl2
      exact hl2
    have ent := entry J l hl i j hij
    have hsq : l i * star (l i) = 1 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hli]
      simp
    have hij' : l i = l j := by
      have : l i * (star (l i) * l j) = l i := by rw [ent, mul_one]
      rw [← mul_assoc, hsq, one_mul] at this
      exact this.symm
    have hieq : i = j := hinj hij'
    subst hieq
    have h0 : 0 ≤ ‖τ i‖ := norm_nonneg _
    have h1 : ‖τ i‖ = 1 := by nlinarith
    rw [h1]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  · exact le_trans (hbd j hgt).2 (le_max_left _ _)

end MainStatements.WeightKernel

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.PSmoothSum
open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix
open scoped ContDiff ComplexConjugate

noncomputable section

namespace MainStatements.WeightKernel.PSmoothSum

lemma le_infty (k : ℕ) : (k : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top

end MainStatements.WeightKernel.PSmoothSum

namespace MainStatements.WeightKernel

open PSmoothSum in
theorem smoothSum : SmoothSum := by
  intro X P _ _ _ _ _ _ W hW K B hK hB I p hp a ha
  obtain ⟨R, hR⟩ := hB.isBounded.subset_closedBall (0 : X)
  let φ : ContDiffBump (0 : X) :=
    ⟨max R 0 + 1, max R 0 + 2, by positivity, by linarith⟩
  let G : X × P → ℂ := fun q => ((φ q.1 : ℝ) : ℂ) * W q
  have hG : ContDiff ℝ ∞ G :=
    (Complex.ofRealCLM.contDiff.comp (φ.contDiff.comp contDiff_fst)).mul hW
  have hsupp : tsupport G ⊆ tsupport φ ×ˢ univ := by
    refine closure_minimal ?_ ((isClosed_tsupport _).prod isClosed_univ)
    intro q hq
    refine ⟨subset_tsupport _ ?_, mem_univ _⟩
    intro h0
    apply hq
    simp [G, h0]
  have hcpt : IsCompact (tsupport φ ×ˢ K) := φ.hasCompactSupport.isCompact.prod hK
  have hbound : ∀ k : ℕ, ∃ M : ℝ, ∀ x : X, ∀ y ∈ K, ‖iteratedFDeriv ℝ k G (x, y)‖ ≤ M := by
    intro k
    obtain ⟨M, hM⟩ := hcpt.exists_bound_of_continuousOn
      (hG.continuous_iteratedFDeriv (le_infty k)).continuousOn
    refine ⟨max M 0, fun x y hy => ?_⟩
    by_cases hx : x ∈ tsupport φ
    · exact (by simpa using hM (x, y) ⟨hx, hy⟩ : _ ≤ M).trans (le_max_left _ _)
    · have : (x, y) ∉ tsupport G := fun h => hx (hsupp h).1
      have h0 : iteratedFDeriv ℝ k G (x, y) = 0 := by
        by_contra hne
        exact this (support_iteratedFDeriv_subset k hne)
      simp [h0]
  choose M hM using hbound
  let L : X →L[ℝ] X × P := ContinuousLinearMap.inl ℝ X P
  have hpart : ∀ (y : P) (k : ℕ) (x : X), y ∈ K →
      ‖iteratedFDeriv ℝ k (fun z => G (z, y)) x‖ ≤ M k * ‖L‖ ^ k := by
    intro y k x hy
    have heq : (fun z => G (z, y)) = (fun q => G (q + (0, y))) ∘ L := by
      funext z
      simp [L]
    have hGt : ContDiff ℝ ∞ (fun q => G (q + (0, y))) := hG.comp (contDiff_id.add contDiff_const)
    rw [heq, L.iteratedFDeriv_comp_right hGt x (le_infty k)]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    rw [iteratedFDeriv_comp_add_right, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hxy : L x + (0, y) = (x, y) := by simp [L]
    rw [hxy]
    exact mul_le_mul_of_nonneg_right (hM k x y hy) (pow_nonneg (norm_nonneg _) _)
  refine ⟨fun x => ∑' i, a i * G (x, p i), ?_, ?_⟩
  · refine contDiff_tsum (N := (⊤ : ℕ∞)) (v := fun k i => ‖a i‖ * (M k * ‖L‖ ^ k)) ?_ ?_ ?_
    · intro i
      exact contDiff_const.mul (hG.comp (contDiff_id.prodMk contDiff_const))
    · intro k _
      exact ha.mul_right _
    · intro k i x _
      have hci : ContDiffAt ℝ k (fun z => G (z, p i)) x :=
        ((hG.comp (contDiff_id.prodMk contDiff_const)).of_le (le_infty k)).contDiffAt
      have := iteratedFDeriv_const_smul_apply' (a := a i) hci
      simp only [smul_eq_mul] at this
      rw [this]
      exact (norm_smul_le _ _).trans
        (mul_le_mul_of_nonneg_left (hpart (p i) k x (hp i)) (norm_nonneg _))
  · intro x hx
    have hx' : dist x 0 ≤ R := hR hx
    have h1 : φ x = 1 := φ.one_of_mem_closedBall (by
      show dist x 0 ≤ max R 0 + 1
      linarith [le_max_left R 0])
    simp [G, h1]

end MainStatements.WeightKernel
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.PKerUnif
open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix
open scoped ContDiff ComplexConjugate

noncomputable section

namespace MainStatements.WeightKernel.PKerUnif

theorem ker_eq_sum {H Ω I : Type} (c : I → Ω → ℂ) (q : I → Ω → H) (φ : H → ℂ) (C : Set H) (x : Ω)
    (hf : {i | c i x ≠ 0 ∧ q i x ∈ C}.Finite) (hφ : ∀ y ∉ C, φ y = 0) :
    MainStatements.WeightKernel.ker c q φ x = ∑ i ∈ hf.toFinset, c i x * φ (q i x) := by
  unfold MainStatements.WeightKernel.ker
  apply tsum_eq_sum
  intro i hi
  rw [Set.Finite.mem_toFinset] at hi
  by_cases h1 : c i x = 0
  · simp [h1]
  · have h2 : q i x ∉ C := fun h => hi ⟨h1, h⟩
    simp [hφ _ h2]

end MainStatements.WeightKernel.PKerUnif

open MainStatements.WeightKernel.PKerUnif in
theorem MainStatements.WeightKernel.kerUnif : SmoothSum → ClosedGraph → KerUnif := by
  intro hS hCG H _ _ _ _ _ _ _ _ n ι hι Ω I _ _ m _ c q hker P _ _ _ W p K C hW hp hK hC hvan
  obtain ⟨M, hM⟩ := ((hC.image hι.continuous).prod (hK.image hp)).exists_bound_of_continuousOn
    hW.continuous.continuousOn
  have hMb : ∀ y ∈ C, ∀ k ∈ K, ‖W (matCoord ι y, p k)‖ ≤ M := fun y hy k hk =>
    hM _ (Set.mk_mem_prod ⟨y, hy, rfl⟩ ⟨k, hk, rfl⟩)
  obtain ⟨R, hR⟩ := (hC.image hι.continuous).isBounded.subset_closedBall (0 : Mx n)
  obtain ⟨Bd, hBd⟩ := hCG Ω K m (fun (k : K) x => ker c q (fun y => W (matCoord ι y, p k)) x) (by
    intro x
    refine ⟨∑ i ∈ (hker.fin x C hC).toFinset, ‖c i x‖ * M, fun k => ?_⟩
    rw [ker_eq_sum c q _ C x (hker.fin x C hC) (fun y hy => hvan k k.2 y hy)]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hMb _ ((Set.Finite.mem_toFinset _).1 hi).2 _ k.2) (norm_nonneg _)) (by
    intro a ha
    have hz : ∀ y ∉ C, ∑' k : K, a k * W (matCoord ι y, p k) = 0 := by
      intro y hy
      have : ∀ k : K, a k * W (matCoord ι y, p k) = 0 := fun k => by rw [hvan k.1 k.2 y hy, mul_zero]
      simp [this]
    let bump : ContDiffBump (0 : Mx n) :=
      ⟨max R 0 + 1, max R 0 + 2, add_pos_of_nonneg_of_pos (le_max_right _ _) one_pos, by linarith⟩
    obtain ⟨Φ, hΦs, hΦ⟩ := hS (Mx n) P W hW (p '' K) (Metric.closedBall 0 (max R 0 + 2)) (hK.image hp)
      (isCompact_closedBall _ _) K (fun k => p k.1) (fun k => ⟨k.1, k.2, rfl⟩) a ha
    have hψ : (fun y => ∑' k : K, a k * W (matCoord ι y, p k)) ∈ CcMat ι := by
      refine ⟨HasCompactSupport.intro hC fun y hy => hz y hy, fun z => Complex.ofRealCLM (bump z) * Φ z,
        (Complex.ofRealCLM.contDiff.comp bump.contDiff).mul hΦs, fun y => ?_⟩
      simp only [Complex.ofRealCLM_apply]
      by_cases hy : y ∈ C
      · have hin : matCoord ι y ∈ Metric.closedBall (0 : Mx n) (max R 0 + 1) :=
          Metric.closedBall_subset_closedBall (by linarith [le_max_left R 0]) (hR ⟨y, hy, rfl⟩)
        have hin2 : matCoord ι y ∈ Metric.closedBall (0 : Mx n) (max R 0 + 2) :=
          Metric.closedBall_subset_closedBall (by linarith [le_max_left R 0]) (hR ⟨y, hy, rfl⟩)
        have h1 : bump (matCoord ι y) = 1 := bump.one_of_mem_closedBall hin
        rw [h1, hΦ _ hin2]
        simp
      · by_cases hb : matCoord ι y ∈ Metric.closedBall (0 : Mx n) (max R 0 + 2)
        · rw [hΦ _ hb]
          simp [hz y hy]
        · have h0 : bump (matCoord ι y) = 0 :=
            image_eq_zero_of_notMem_tsupport (by rw [bump.tsupport_eq]; exact hb)
          simp [h0, hz y hy]
    refine (hker.int _ hψ).congr (ae_of_all m fun x => ?_)
    have hf := hker.fin x C hC
    have hs : ∀ i ∈ hf.toFinset, Summable (fun k : K => a k * W (matCoord ι (q i x), p k)) := by
      intro i hi
      have hq := ((Set.Finite.mem_toFinset _).1 hi).2
      refine Summable.of_norm (Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_) (ha.mul_right M))
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hMb _ hq _ k.2) (norm_nonneg _)
    have hu : ∀ k : K, ker c q (fun y => W (matCoord ι y, p k)) x
        = ∑ i ∈ hf.toFinset, c i x * W (matCoord ι (q i x), p k) :=
      fun k => ker_eq_sum c q _ C x hf (fun y hy => hvan k k.2 y hy)
    symm
    calc ∑' k : K, a k * ker c q (fun y => W (matCoord ι y, p k)) x
        = ∑' k : K, ∑ i ∈ hf.toFinset, c i x * (a k * W (matCoord ι (q i x), p k)) := by
          congr 1; ext k; rw [hu k, Finset.mul_sum]; congr 1; ext i; ring
      _ = ∑ i ∈ hf.toFinset, ∑' k : K, c i x * (a k * W (matCoord ι (q i x), p k)) :=
          Summable.tsum_finsetSum fun i hi => (hs i hi).mul_left _
      _ = ∑ i ∈ hf.toFinset, c i x * ∑' k : K, a k * W (matCoord ι (q i x), p k) := by
          congr 1; ext i; rw [tsum_mul_left]
      _ = ker c q (fun y => ∑' k : K, a k * W (matCoord ι y, p k)) x :=
          (ker_eq_sum c q _ C x hf hz).symm)
  exact ⟨Bd, fun k hk => hBd ⟨k, hk⟩⟩

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.PWeight
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqOfNearOfCharpolyEq
open MeasureTheory Set Filter Matrix
open scoped ENNReal NNReal Topology

namespace GlobalTheory.CompanionTheory.WeylNear

theorem exists_diag (n : ℕ) (s : Matrix (Fin n) (Fin n) ℂ) (hs : s.charpoly.Separable) :
    ∃ (P Q : Matrix (Fin n) (Fin n) ℂ) (l : Fin n → ℂ), Function.Injective l ∧
      P * Q = 1 ∧ Q * P = 1 ∧ Q * s * P = diagonal l := by
  have hnd : s.charpoly.roots.Nodup := Polynomial.nodup_roots hs
  have hcard : s.charpoly.roots.card = n := by
    have h1 := (IsAlgClosed.splits s.charpoly).natDegree_eq_card_roots
    rw [Matrix.charpoly_natDegree_eq_dim] at h1
    simpa using h1.symm
  have hc2 : s.charpoly.roots.toFinset.card = n := by
    rw [Multiset.toFinset_card_of_nodup hnd, hcard]
  let e := Finset.equivFinOfCardEq hc2
  let l : Fin n → ℂ := fun i => (e.symm i : ℂ)
  have hl : Function.Injective l := fun i j h =>
    e.symm.injective (Subtype.ext h)
  have hroot : ∀ i, s.charpoly.IsRoot (l i) := fun i => by
    have := (e.symm i).2
    rw [Multiset.mem_toFinset] at this
    exact Polynomial.isRoot_of_mem_roots this
  have hev : ∀ i, ∃ v : Fin n → ℂ, v ≠ 0 ∧ s *ᵥ v = l i • v := by
    intro i
    have h0 : Module.End.HasEigenvalue (Matrix.toLin' s : Module.End ℂ (Fin n → ℂ)) (l i) := by
      rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin']
      exact hroot i
    obtain ⟨v, hv⟩ := h0.exists_hasEigenvector
    refine ⟨v, hv.2, ?_⟩
    have := hv.apply_eq_smul
    simpa using this
  choose v hv0 hv using hev
  have hli : LinearIndependent ℂ v :=
    Module.End.eigenvectors_linearIndependent' (Matrix.toLin' s : Module.End ℂ (Fin n → ℂ)) l hl v
      (fun i => ⟨by
        rw [Module.End.mem_eigenspace_iff]; simpa using hv i, hv0 i⟩)
  let P : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => v j i
  have hcol : P.col = v := by
    ext j i; rfl
  have hP : IsUnit P := Matrix.linearIndependent_cols_iff_isUnit.mp (by rw [hcol]; exact hli)
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).1 hP
  have hsP : s * P = P * diagonal l := by
    ext i j
    have := congrFun (hv j) i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    rw [Matrix.mul_diagonal]
    simp only [Matrix.mul_apply, P, Matrix.of_apply]
    rw [this, mul_comm]
  refine ⟨P, P⁻¹, l, hl, Matrix.mul_nonsing_inv _ hdet, Matrix.nonsing_inv_mul _ hdet, ?_⟩
  rw [Matrix.mul_assoc, hsP, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]

end GlobalTheory.CompanionTheory.WeylNear
end

open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix
open scoped ContDiff ComplexConjugate

noncomputable section

namespace MainStatements.WeightKernel.PWeight

variable {n : ℕ}

theorem cancel_l {A B : Matrix (Fin n) (Fin n) ℂ} (h : A * B = 1) (X : Matrix (Fin n) (Fin n) ℂ) :
    A * (B * X) = X := by
  rw [← Matrix.mul_assoc, h, Matrix.one_mul]

def conjHom {H : Type} [Group H] (ι : H →* Matrix (Fin n) (Fin n) ℂ) (Q P : Matrix (Fin n) (Fin n) ℂ)
    (hPQ : P * Q = 1) (hQP : Q * P = 1) : H →* Matrix (Fin n) (Fin n) ℂ where
  toFun h := Q * ι h * P
  map_one' := by simp [hQP]
  map_mul' a b := by simp only [map_mul, Matrix.mul_assoc, cancel_l hPQ]

theorem conjHom_apply {H : Type} [Group H] (ι : H →* Matrix (Fin n) (Fin n) ℂ) (Q P : Matrix (Fin n) (Fin n) ℂ)
    (hPQ : P * Q = 1) (hQP : Q * P = 1) (g : H) : conjHom ι Q P hPQ hQP g = Q * ι g * P := rfl

def conjHomeo (Q P : Matrix (Fin n) (Fin n) ℂ) (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    Matrix (Fin n) (Fin n) ℂ ≃ₜ Matrix (Fin n) (Fin n) ℂ where
  toFun Y := Q * Y * P
  invFun Y := P * Y * Q
  left_inv Y := by simp only [Matrix.mul_assoc, cancel_l hPQ, hPQ, Matrix.mul_one]
  right_inv Y := by simp only [Matrix.mul_assoc, cancel_l hQP, hQP, Matrix.mul_one]
  continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

theorem isUGroup_conj {H : Type} [Group H] [TopologicalSpace H] (ι : H →* Matrix (Fin n) (Fin n) ℂ)
    (J Q P : Matrix (Fin n) (Fin n) ℂ) (hPQ : P * Q = 1) (hQP : Q * P = 1) (hU : IsUGroup ι J) :
    IsUGroup (conjHom ι Q P hPQ hQP) (Pᴴ * J * P) := by
  have hPQh : Qᴴ * Pᴴ = 1 := by rw [← conjTranspose_mul, hPQ, conjTranspose_one]
  have hQPh : Pᴴ * Qᴴ = 1 := by rw [← conjTranspose_mul, hQP, conjTranspose_one]
  have hP : IsUnit P.det := isUnit_iff_exists_inv.2 ⟨Q.det, by rw [← det_mul, hPQ, det_one]⟩
  have hPh : IsUnit Pᴴ.det := isUnit_iff_exists_inv.2 ⟨Qᴴ.det, by rw [← det_mul, hQPh, det_one]⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [det_mul, det_mul]
    exact (hPh.mul hU.1).mul hP
  · exact (conjHomeo Q P hPQ hQP).isClosedEmbedding.comp hU.2.1
  · have key1 : ∀ X : Matrix (Fin n) (Fin n) ℂ,
        (Q * X * P)ᴴ * (Pᴴ * J * P) * (Q * X * P) = Pᴴ * (Xᴴ * J * X) * P := by
      intro X
      simp only [conjTranspose_mul, Matrix.mul_assoc, cancel_l hPQh, cancel_l hPQ]
    have key2 : ∀ X : Matrix (Fin n) (Fin n) ℂ,
        (P * X * Q)ᴴ * J * (P * X * Q) = Qᴴ * (Xᴴ * (Pᴴ * J * P) * X) * Q := by
      intro X
      simp only [conjTranspose_mul, Matrix.mul_assoc]
    have key3 : Qᴴ * (Pᴴ * J * P) * Q = J := by
      simp only [Matrix.mul_assoc, cancel_l hPQh, hPQ, Matrix.mul_one]
    intro M
    constructor
    · rintro ⟨h, rfl⟩
      have hA := (hU.2.2 (ι h)).1 ⟨h, rfl⟩
      rw [conjHom_apply, key1, hA]
    · intro hM
      have hN : (P * M * Q)ᴴ * J * (P * M * Q) = J := by rw [key2, hM, key3]
      obtain ⟨h, hh⟩ := (hU.2.2 _).2 hN
      refine ⟨h, ?_⟩
      rw [conjHom_apply, hh]
      simp only [Matrix.mul_assoc, cancel_l hQP, hQP, Matrix.mul_one]

def conjMx (Q P : Matrix (Fin n) (Fin n) ℂ) (Y : MainStatements.WeightKernel.Mx n) : MainStatements.WeightKernel.Mx n :=
  fun i j => (Q * Matrix.of Y * P) i j

theorem contDiff_conjMx (Q P : Matrix (Fin n) (Fin n) ℂ) : ContDiff ℝ ∞ (conjMx Q P) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  simp only [conjMx, Matrix.mul_apply, Matrix.of_apply]
  exact ContDiff.sum fun x _ => ContDiff.mul (ContDiff.sum fun y _ =>
    contDiff_const.mul ((contDiff_apply ℝ (fun _ => ℂ) x).comp (contDiff_apply ℝ (fun _ => (Fin n → ℂ)) y))) contDiff_const

end MainStatements.WeightKernel.PWeight

namespace MainStatements.WeightKernel

open PWeight in
theorem weight : WeightDiag → Weight := by
  intro hWD H _ _ _ _ _ _ _ _ n ι J hU s hreg hprop
  obtain ⟨P, Q, l, hl, hPQ, hQP, hd⟩ := GlobalTheory.CompanionTheory.WeylNear.exists_diag n (ι s) hreg
  obtain ⟨B', hB'⟩ := hWD H n (conjHom ι Q P hPQ hQP) (Pᴴ * J * P) (isUGroup_conj ι J Q P hPQ hQP hU) s l hl
    hd hprop
  refine ⟨fun z => B' (conjMx Q P z.1, conjMx Q P z.2), ?_, fun z => hB'.nonneg _, hB'.pos, hB'.shift, hB'.proper⟩
  exact hB'.smooth.comp (((contDiff_conjMx Q P).comp contDiff_fst).prodMk ((contDiff_conjMx Q P).comp contDiff_snd))

end MainStatements.WeightKernel

end
end
