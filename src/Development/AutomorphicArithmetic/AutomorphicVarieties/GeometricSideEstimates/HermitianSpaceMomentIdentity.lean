module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.HermitianSpaceGeometricEstimate
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.EllFacts

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.HermitianSpaceMomentIdentity
open UpperTheory.V.Lit.Geo
open GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor

theorem UpperTheory.hermitian_space_moment_identity :
    MomQuad := by
  intro E _ _ _ a ha L hL g p
  obtain ⟨-, h2⟩ := UpperTheory.hermitian_space_geometric_estimate E a ha L hL
  have hP : ∀ (i j : Fin a) (w : NumberField.InfinitePlace E),
      (fun x : Fin a → Cinf E => star (x i w) * x j w) ∈ poly E a := by
    intro i j w
    have h1 : (fun x : Fin a → Cinf E => star (x i w)) ∈ poly E a :=
      Algebra.subset_adjoin ⟨
        { toFun := fun x => star (x i w)
          map_add' := fun x y => by simp
          map_smul' := fun c x => by simp }, rfl⟩
    have h2 : (fun x : Fin a → Cinf E => x j w) ∈ poly E a :=
      Algebra.subset_adjoin ⟨
        { toFun := fun x => x j w
          map_add' := fun x y => rfl
          map_smul' := fun c x => rfl }, rfl⟩
    exact (poly E a).mul_mem h1 h2
  have hS : ∀ (w : NumberField.InfinitePlace E) (i j : Fin a), HasSum
      (fun v : lat L g => (pg (fun x : Fin a → Cinf E => star (x i w) * x j w) (pt (rt g) v.1) * p j i w).re)
      (gsum L (pg (fun x : Fin a → Cinf E => star (x i w) * x j w)) g * p j i w).re := by
    intro w i j
    exact Complex.hasSum_re ((((h2 _ (hP i j w)).1 g).hasSum).mul_right (p j i w))
  have hT := hasSum_sum (s := Finset.univ) fun w _ => hasSum_sum (s := Finset.univ) fun i _ =>
    hasSum_sum (s := Finset.univ) fun j _ => hS w i j
  have hq : ∀ x : Fin a → Cinf E, quad p x * gauss x = ∑ w : NumberField.InfinitePlace E, ∑ i, ∑ j,
      (pg (fun x : Fin a → Cinf E => star (x i w) * x j w) x * p j i w).re := by
    intro x
    simp only [quad, Finset.sum_mul, pg, dotProduct, Matrix.vecMul, Finset.sum_apply, Complex.re_sum, Pi.mul_apply, Pi.star_apply]
    refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← Complex.re_mul_ofReal]
    congr 1
    ring
  simp only [hq]
  rw [hT.tsum_eq]
  simp only [UpperTheory.V.Lit.Bor.trF, Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_apply, Complex.re_sum, Finset.sum_div, Pi.mul_apply]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← Complex.div_ofReal_re]
  congr 1
  change mean L _ g * _ = _
  rw [mean]
  ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.HermitianTraceFormEstimate
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open UpperTheory.V.Lit.Geo

section
variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private theorem ell_toL' (X : Matrix (Fin a) (Fin a) (Cinf E)) :
    ell E a (toL X) = (∑ w : InfinitePlace E, (X.trace w).re) / ((a : ℝ) * Fintype.card (InfinitePlace E)) := by
  simp [ell, Matrix.trace, Finset.sum_apply]

private theorem mono_mem (i j : Fin a) (w : InfinitePlace E) :
    (fun x : Fin a → Cinf E => star (x i w) * x j w) ∈ poly E a := by
  have h1 : (fun x : Fin a → Cinf E => star (x i w)) ∈ poly E a :=
    Algebra.subset_adjoin ⟨{ toFun := fun x => star (x i w), map_add' := fun x y => by simp, map_smul' := fun c x => by simp }, rfl⟩
  have h2 : (fun x : Fin a → Cinf E => x j w) ∈ poly E a :=
    Algebra.subset_adjoin ⟨{ toFun := fun x => x j w, map_add' := fun x y => rfl, map_smul' := fun c x => rfl }, rfl⟩
  exact mul_mem h1 h2

private theorem herm_trace (M : Herm E a) (w : InfinitePlace E) : (((M.1.trace w).re : ℝ) : ℂ) = ∑ i, M.1 i i w := by
  have h : star M.1 = M.1 := M.2
  have h2 : ∀ i, ((M.1 i i w).re : ℂ) = M.1 i i w := fun i => by
    have := congrFun (congrFun (congrFun h i) i) w
    exact Complex.conj_eq_iff_re.1 this
  simp only [Matrix.trace, Matrix.diag, Finset.sum_apply, Complex.re_sum, Complex.ofReal_sum, h2]

private theorem trF_bd (X : Matrix (Fin a) (Fin a) (Cinf E)) :
    |trF X X| ≤ (Fintype.card (InfinitePlace E) : ℝ) * (a * (a * (‖toL X‖ * ‖toL X‖))) := by
  have hX : ∀ i j w, ‖X i j w‖ ≤ ‖toL X‖ := fun i j w =>
    ((norm_le_pi_norm (toL X i j) w).trans (norm_le_pi_norm (toL X i) j)).trans (norm_le_pi_norm (toL X) i)
  unfold trF
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ (a * (a * (‖toL X‖ * ‖toL X‖))) fun w _ => ?_).trans (by simp)
  refine (Complex.abs_re_le_norm _).trans ?_
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_apply, Pi.mul_apply]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ (a * (‖toL X‖ * ‖toL X‖)) fun i _ => ?_).trans (by simp)
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ ((‖toL X‖ * ‖toL X‖)) fun j _ => ?_).trans (by simp)
  rw [norm_mul]
  exact mul_le_mul (hX _ _ _) (hX _ _ _) (norm_nonneg _) (norm_nonneg _)

end

theorem UpperTheory.hermitian_trace_form_estimate :
    DevFacts := by
  intro E _ _ _ a ha L hL
  obtain ⟨-, hM⟩ := UpperTheory.hermitian_space_geometric_estimate E a ha L hL
  have h1 : (a : ℝ) ≠ 0 := by exact_mod_cast (by omega : a ≠ 0)
  have h2 : (Fintype.card (InfinitePlace E) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hone : ell E a (toL (1 : Matrix (Fin a) (Fin a) (Cinf E))) = 1 := (UpperTheory.V.Lit.Bor.ellFacts E a).1 ha
  have hdev : ∀ g, (dev L g).1 = (mom L g).1 - ell E a (toL (mom L g).1) • (1 : Matrix (Fin a) (Fin a) (Cinf E)) := fun g => rfl
  have hdevL : ∀ g, toL (dev L g).1 = toL (mom L g).1 - ell E a (toL (mom L g).1) • toL (1 : Matrix (Fin a) (Fin a) (Cinf E)) := fun g => rfl
  have hmom : ∀ i j w, (fun g => (mom L g).1 i j w) ∈ meanAlg L := fun i j w =>
    Algebra.subset_adjoin ⟨_, mono_mem i j w, rfl⟩
  have hell : ∀ g, ell E a (toL (dev L g).1) = 0 := fun g => by
    rw [hdevL, map_sub, map_smul, hone, smul_eq_mul, mul_one, sub_self]
  refine ⟨fun i j w => ?_, ?_, fun g => ⟨hell g, ?_⟩⟩
  · have e : (fun g => (dev L g).1 i j w) = (fun g => (mom L g).1 i j w) -
        ((1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w / ((a : ℂ) * Fintype.card (InfinitePlace E))) •
          ∑ w' : InfinitePlace E, ∑ k, fun g => (mom L g).1 k k w' := by
      funext g
      simp only [hdev, ell_toL', Matrix.sub_apply, Matrix.smul_apply, Pi.sub_apply, Pi.smul_apply, Finset.sum_apply,
        ← herm_trace, Complex.real_smul, smul_eq_mul]
      push_cast
      ring
    rw [e]
    exact sub_mem (hmom i j w) (Subalgebra.smul_mem _ (sum_mem fun w' _ => sum_mem fun k _ => hmom k k w') _)
  · choose C hC using fun (p : Fin a × Fin a × InfinitePlace E) => (hM _ (mono_mem p.1 p.2.1 p.2.2)).2
    obtain ⟨B₀, hB₀⟩ := (Set.finite_range C).bddAbove
    have hB : ∀ g, ‖toL (mom L g).1‖ ≤ |B₀| := fun g => by
      refine (pi_norm_le_iff_of_nonneg (abs_nonneg _)).2 fun i => (pi_norm_le_iff_of_nonneg (abs_nonneg _)).2 fun j =>
        (pi_norm_le_iff_of_nonneg (abs_nonneg _)).2 fun w => ?_
      exact ((hC (i, j, w) g).trans (hB₀ ⟨_, rfl⟩)).trans (le_abs_self _)
    obtain ⟨K, hK, hKb⟩ := (LinearMap.toContinuousLinearMap (ell E a)).bound
    set B₁ : ℝ := |B₀| + K * |B₀| * ‖toL (1 : Matrix (Fin a) (Fin a) (Cinf E))‖ with hB₁
    have hD : ∀ g, ‖toL (dev L g).1‖ ≤ B₁ := fun g => by
      rw [hdevL]
      refine (norm_sub_le _ _).trans (add_le_add (hB g) ?_)
      rw [norm_smul]
      refine mul_le_mul_of_nonneg_right ((hKb _).trans ?_) (norm_nonneg _)
      exact mul_le_mul_of_nonneg_left (hB g) hK.le
    have hB1 : 0 ≤ B₁ := by positivity
    set B₂ : ℝ := (Fintype.card (InfinitePlace E) : ℝ) * (a * (a * (B₁ * B₁))) with hB₂
    have hB2 : 0 ≤ B₂ := by positivity
    have hB0 := abs_nonneg B₀
    refine ⟨|B₀| + B₁ + B₂ + 1, by positivity, fun g => ⟨by linarith [hB g], by linarith [hD g], ?_⟩⟩
    have : |trF (dev L g).1 (dev L g).1| ≤ B₂ := by
      refine (trF_bd _).trans ?_
      have := hD g
      rw [hB₂]
      gcongr
    linarith
  · have h0 := hell g
    rw [ell_toL', div_eq_zero_iff] at h0
    have h0' := h0.resolve_right (mul_ne_zero h1 h2)
    have e : (dev L g).1 * (dev L g).1 = (mom L g).1 * (dev L g).1 - ell E a (toL (mom L g).1) • (dev L g).1 := by
      conv_lhs => rw [hdev g]
      rw [sub_mul, smul_mul_assoc, one_mul, ← hdev]
    unfold trF
    rw [e]
    simp only [Matrix.trace_sub, Matrix.trace_smul, Pi.sub_apply, Pi.smul_apply, Complex.sub_re, Complex.smul_re,
      smul_eq_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, h0', mul_zero, sub_zero]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.HermitianSpaceLogEstimate
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.GeometricSideUpperBound
open UpperTheory.V.Lit.Geo

theorem UpperTheory.geometric_side_upper_bound :
    ThetaUp := by
  classical
  intro N
  obtain ⟨⟨K, hK, hK1⟩⟩ : Nonempty {K : ℝ // K ^ N * Real.exp (-K) < 1 / (2 * Real.exp Real.pi) ∧ 1 ≤ K} := by
    obtain ⟨K, hK⟩ := (((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero N).eventually
      (gt_mem_nhds (show (0 : ℝ) < 1 / (2 * Real.exp Real.pi) by positivity))).and
      (Filter.eventually_ge_atTop (1 : ℝ))).exists
    exact ⟨⟨K, hK⟩⟩
  have hK0 : 0 ≤ K := by linarith
  have ha : Real.exp (-Real.pi * (K - 1)) * K ^ N ≤ 1 / 2 := by
    have e1 : Real.exp (-Real.pi * (K - 1)) = Real.exp Real.pi * Real.exp (-(Real.pi * K)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have e2 : Real.exp (-(Real.pi * K)) ≤ Real.exp (-K) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_gt_three])
    have hKN : 0 ≤ K ^ N := by positivity
    calc Real.exp (-Real.pi * (K - 1)) * K ^ N
        = Real.exp Real.pi * (K ^ N * Real.exp (-(Real.pi * K))) := by rw [e1]; ring
      _ ≤ Real.exp Real.pi * (K ^ N * Real.exp (-K)) := by gcongr
      _ ≤ Real.exp Real.pi * (1 / (2 * Real.exp Real.pi)) := by gcongr
      _ = 1 / 2 := by field_simp
  refine ⟨2 * K ^ N, by positivity, ?_⟩
  intro ι q i₀ μ hS hμ hμ1 hgap
  have hKμ : 1 / μ ≤ K / μ := by gcongr
  obtain ⟨hsY, hY⟩ := hS.2 (1 / μ) (K / μ) (by positivity) hKμ
  have hsX : Summable fun i => Real.exp (-Real.pi * (K / μ * q i)) :=
    (hS.2 (K / μ) (K / μ) (by positivity) le_rfl).1
  have hsI : Summable (fun i => if i = i₀ then (1 : ℝ) else 0) := (hasSum_ite_eq i₀ (1 : ℝ)).summable
  have hX2 : ∑' i, Real.exp (-Real.pi * (K / μ * q i)) ≤
      1 + Real.exp (-Real.pi * (K - 1)) * ∑' i, Real.exp (-Real.pi * (1 / μ * q i)) := by
    calc ∑' i, Real.exp (-Real.pi * (K / μ * q i))
        ≤ ∑' i, ((if i = i₀ then (1 : ℝ) else 0) +
            Real.exp (-Real.pi * (K - 1)) * Real.exp (-Real.pi * (1 / μ * q i))) := by
          refine Summable.tsum_le_tsum (fun i => ?_) hsX (hsI.add (hsY.mul_left _))
          by_cases h : i = i₀
          · have hq := hS.1 i
            have h0 : -Real.pi * (K / μ * q i) ≤ 0 := by
              have : 0 ≤ K / μ * q i := by positivity
              nlinarith [Real.pi_pos]
            have h1 := Real.exp_le_one_iff.mpr h0
            have h2 : 0 ≤ Real.exp (-Real.pi * (K - 1)) * Real.exp (-Real.pi * (1 / μ * q i)) := by positivity
            rw [if_pos h]
            linarith
          · have hr : 1 ≤ q i / μ := by
              rw [le_div_iff₀ hμ]
              linarith [hgap i h]
            rw [if_neg h, zero_add, ← Real.exp_add]
            apply Real.exp_le_exp.mpr
            have e3 : K / μ * q i = K * (q i / μ) := by ring
            have e4 : 1 / μ * q i = q i / μ := by ring
            rw [e3, e4]
            nlinarith [mul_nonneg (sub_nonneg.2 hK1) (sub_nonneg.2 hr), Real.pi_pos]
      _ = 1 + Real.exp (-Real.pi * (K - 1)) * ∑' i, Real.exp (-Real.pi * (1 / μ * q i)) := by
          rw [Summable.tsum_add hsI (hsY.mul_left _), tsum_mul_left]
          congr 1
          exact tsum_ite_eq i₀ (fun _ => (1 : ℝ))
  have eK : K / μ / (1 / μ) = K := by field_simp
  rw [eK] at hY
  have hX0 : 0 ≤ ∑' i, Real.exp (-Real.pi * (K / μ * q i)) := tsum_nonneg fun i => (Real.exp_pos _).le
  have hX : ∑' i, Real.exp (-Real.pi * (K / μ * q i)) ≤ 2 := by
    have ha0 : 0 ≤ Real.exp (-Real.pi * (K - 1)) := (Real.exp_pos _).le
    have := mul_le_mul_of_nonneg_left hY ha0
    nlinarith
  have h1K : 1 ≤ K / μ := by
    rw [le_div_iff₀ hμ]
    linarith
  obtain ⟨-, hS1⟩ := hS.2 1 (K / μ) one_pos h1K
  simp only [one_mul, div_one] at hS1
  have hpow : 0 ≤ (K / μ) ^ N := by positivity
  calc ∑' i, Real.exp (-Real.pi * q i) ≤ (K / μ) ^ N * ∑' i, Real.exp (-Real.pi * (K / μ * q i)) := hS1
    _ ≤ (K / μ) ^ N * 2 := by gcongr
    _ = 2 * K ^ N / μ ^ N := by rw [div_pow]; ring
end

open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Automorphic

private theorem log_bound {T D C H q : ℝ} {N M : ℕ} (hT : 1 ≤ T) (hC : 1 ≤ C) (hH : 1 ≤ H) (hq : 1 ≤ q)
    (hHq : H ≤ 2 * q) (h : T ≤ D / ((C * H ^ N)⁻¹) ^ M) :
    Real.log T ≤ (|Real.log D| + M * Real.log C + M * N) * (1 + Real.log q) := by
  have hC0 : 0 < C := one_pos.trans_le hC
  have hH0 : 0 < H := one_pos.trans_le hH
  have hq0 : 0 < q := one_pos.trans_le hq
  rw [inv_pow, div_inv_eq_mul] at h
  have hp : 0 < (C * H ^ N) ^ M := by positivity
  have hD : 0 < D := (mul_pos_iff_of_pos_right hp).1 (one_pos.trans_le (hT.trans h))
  have h1 : Real.log T ≤ Real.log D + M * (Real.log C + N * Real.log H) := by
    have := Real.log_le_log (one_pos.trans_le hT) h
    rwa [Real.log_mul hD.ne' hp.ne', Real.log_pow, Real.log_mul hC0.ne' (by positivity), Real.log_pow] at this
  have h2 : Real.log H ≤ 1 + Real.log q := by
    have := Real.log_le_log hH0 hHq
    rw [Real.log_mul two_ne_zero hq0.ne'] at this
    have h3 := Real.log_le_sub_one_of_pos (two_pos (α := ℝ))
    linarith
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hq
  have hlC : 0 ≤ Real.log C := Real.log_nonneg hC
  have h4 : (M : ℝ) * N * Real.log H ≤ M * N * (1 + Real.log q) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have h5 : 0 ≤ (|Real.log D| + M * Real.log C) * Real.log q := by positivity
  have h6 := le_abs_self (Real.log D)
  nlinarith

theorem UpperTheory.hermitian_space_log_estimate :
    FnLe := by
  intro E _ _ _ a ha L hL
  obtain ⟨C, N, hC, hmin⟩ := UpperTheory.global_geometric_estimate_of_local E a ha L hL
  obtain ⟨M, hsc⟩ := UpperTheory.geometry_of_numbers_lattice_estimate E a ha L hL
  obtain ⟨D, -, hup⟩ := UpperTheory.geometric_side_upper_bound M
  obtain ⟨-, hrt, hγ, -⟩ := UpperTheory.rationalPoint_retraction_exists_cmDatum E a ha
  obtain ⟨hTh, -⟩ := UpperTheory.hermitian_space_geometric_estimate E a ha L hL
  refine ⟨|Real.log D| + M * Real.log C + M * N, fun g => ?_⟩
  have hq : 1 ≤ qht g := (UpperTheory.V.Lit.Geo.qhtFacts E a).1 g
  obtain ⟨γ, hlt⟩ := exists_lt_of_ciInf_lt (show qht g < 2 * qht g by linarith)
  change AutomorphicForm.height (K := E) (ratGL E a γ * rt g) < _ at hlt
  have hH := AutomorphicForm.one_le_height (K := E) (ratGL E a γ * rt g)
  have hCH : 1 ≤ C * AutomorphicForm.height (K := E) (ratGL E a γ * rt g) ^ N :=
    one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ hH)
  refine log_bound (hTh g).1 hC hH hq hlt.le ?_
  refine hup _ _ (0 : lat L g) _ (hsc g) (inv_pos.2 (one_pos.trans_le hCH)) (inv_le_one_of_one_le₀ hCH) fun v hv => ?_
  have e : (v.1 ᵥ* (γ⁻¹).val) ᵥ* γ.val = v.1 := by
    rw [Matrix.vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.vecMul_one]
  have hw := hγ γ (rt g) (v.1 ᵥ* (γ⁻¹).val)
  rw [e, (hrt g).2.2] at hw
  have h1 := hmin (ratGL E a γ * rt g) (v.1 ᵥ* (γ⁻¹).val)
    (by
      change ptF _ _ ∈ L
      rw [hw.1]
      exact v.2)
    (fun h0 => hv (Subtype.ext (by
      rw [← e, h0, Matrix.zero_vecMul]
      rfl)))
  rw [hw.2] at h1
  rw [inv_le_iff_one_le_mul₀' (one_pos.trans_le hCH)]
  exact h1
end
