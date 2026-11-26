module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.HermitianTraceFormEntryEstimate
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.HermitianSpacePointLogEstimate
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.TraceFormPosDefOfTotallyReal

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.LatticePointCountBound
open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum

private theorem gauss_sum_determines_value_and_deviation {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    (L : AddSubgroup (Fin a → Af E)) (g g' : GA E a)
    (hR : gsum L gauss g' = gsum L gauss g)
    (hC : ∀ F : (Fin a → Cinf E) → ℂ, gsum L F g' = gsum L F g) :
    fn L g' = fn L g ∧ dev L g' = dev L g := by
  have hT : Th L g' = Th L g := hR
  have hm : ∀ P, mean L P g' = mean L P g := fun P => by
    unfold mean
    rw [hT, hC]
  have hmom : mom L g' = mom L g := by
    apply Subtype.ext
    ext i j w
    exact hm _
  refine ⟨?_, ?_⟩
  · unfold fn
    rw [hT]
  · unfold dev
    rw [hmom]

theorem UpperTheory.lattice_point_count_bound :
    FnInv := by
  intro E _ _ _ a ha L
  refine ⟨fun γ t g => gauss_sum_determines_value_and_deviation L _ _ ((UpperTheory.point_evaluation_multiplicative_tsum E a ha L ℝ gauss).1 γ t g)
      (fun F => (UpperTheory.point_evaluation_multiplicative_tsum E a ha L ℂ F).1 γ t g),
    fun U hU hL u hu g => gauss_sum_determines_value_and_deviation L _ _ ((UpperTheory.point_evaluation_multiplicative_tsum E a ha L ℝ gauss).2.2 U hU hL u hu g)
      (fun F => (UpperTheory.point_evaluation_multiplicative_tsum E a ha L ℂ F).2.2 U hU hL u hu g), fun k g => ?_⟩
  have h1 := (UpperTheory.point_evaluation_multiplicative_tsum E a ha L ℝ gauss).2.1 g (Unitary.toUnits k)
  have hk : (Unitary.toUnits k : GL (Fin a) (Cinf E)).val = k.1 := rfl
  have hs : sc k.1 = 1 := (UpperTheory.deriv_similitudeChar_at_one_eq_trace E a).2.2.2.2 k
  have hq := UpperTheory.geometric_side_quadraticForm_identity E a
  unfold Th
  rw [h1]
  unfold gsum
  refine tsum_congr fun v => ?_
  rw [hk, hs, one_smul]
  unfold gauss
  rw [hq.2.2.1, (Unitary.mem_iff.1 k.2).2, hq.1]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.HermitianGaussianMomentBound
open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor

private theorem entry_mem {E : Type} [Field E] [NumberField E] {a : ℕ} (l m : Fin a) (w : InfinitePlace E) :
    (fun x : Fin a → Cinf E => star (x l w) * x m w) ∈ poly E a := by
  have h1 : (fun x : Fin a → Cinf E => star (x l w)) ∈ poly E a :=
    Algebra.subset_adjoin ⟨⟨⟨fun x => star (x l w), fun x y => by simp⟩, fun c x => by simp⟩, rfl⟩
  have h2 : (fun x : Fin a → Cinf E => x m w) ∈ poly E a :=
    Algebra.subset_adjoin ⟨⟨⟨fun x => x m w, fun x y => by simp⟩, fun c x => by simp⟩, rfl⟩
  exact Subalgebra.mul_mem _ h1 h2

private theorem gauss_unit {E : Type} [Field E] [NumberField E] {a : ℕ} (k : Kinf E a) (x : Fin a → Cinf E) :
    gauss (x ᵥ* k.1) = gauss x := by
  obtain ⟨h1, -, h3, -⟩ := UpperTheory.geometric_side_quadraticForm_identity E a
  unfold gauss
  rw [h3, k.2.2, h1]

private theorem mom_cpt {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (ha : 1 ≤ a)
    (L : AddSubgroup (Fin a → Af E)) (hL : IsLat L) (k : Kinf E a) (g : GA E a) :
    (mom L (g * infGL E a (Unitary.toUnits k))).1 = star k.1 * (mom L g).1 * k.1 := by
  ext i j w
  have hs := fun l m => ((UpperTheory.hermitian_space_geometric_estimate E a ha L hL).2 _ (entry_mem l m w)).1 g
  have hT := (UpperTheory.lattice_point_count_bound E a ha L).2.2 k g
  have hg := (UpperTheory.point_evaluation_multiplicative_tsum E a ha L ℂ (pg fun x => star (x i w) * x j w)).2.1 g (Unitary.toUnits k)
  have hk : sc (Unitary.toUnits k).val = 1 := (UpperTheory.deriv_similitudeChar_at_one_eq_trace E a).2.2.2.2 k
  have hv : (Unitary.toUnits k).val = k.1 := rfl
  have hp : ∀ x : Fin a → Cinf E, pg (fun x => star (x i w) * x j w) (x ᵥ* k.1) =
      ∑ m, ∑ l, star (k.1 l i w) * pg (fun x => star (x l w) * x m w) x * k.1 m j w := fun x => by
    simp only [pg, gauss_unit, Matrix.vecMul, dotProduct, Finset.sum_apply, Pi.mul_apply, star_sum, star_mul',
      Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [hk, hv] at hg
  simp only [one_smul, hp] at hg
  rw [Summable.tsum_finsetSum fun m _ => summable_sum fun l _ => ((hs l m).mul_left _).mul_right _] at hg
  change mean L (fun x => star (x i w) * x j w) _ = _
  rw [mean, hT, hg]
  simp only [Matrix.mul_apply, Finset.sum_apply, Pi.mul_apply, Finset.sum_mul, Finset.sum_div, Matrix.star_apply,
    Pi.star_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Summable.tsum_finsetSum fun l _ => ((hs l m).mul_left _).mul_right _, Finset.sum_div]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [tsum_mul_right, tsum_mul_left]
  change _ = _ * (gsum L (pg fun x => star (x l w) * x m w) g / _) * _
  rw [gsum]
  ring

private theorem ell_toL {E : Type} [Field E] [NumberField E] {a : ℕ} (X : Matrix (Fin a) (Fin a) (Cinf E)) :
    ell E a (toL X) = (∑ w : InfinitePlace E, (X.trace w).re) / ((a : ℝ) * Fintype.card (InfinitePlace E)) := by
  simp [ell, Matrix.trace, Finset.sum_apply]

theorem UpperTheory.hermitian_gaussian_moment_bound :
    DevCpt := by
  intro E _ _ _ a ha L hL k g
  have hm := mom_cpt ha L hL k g
  have hk : k.1 * star k.1 = 1 := k.2.2
  have he : ell E a (toL (mom L (g * infGL E a (Unitary.toUnits k))).1) = ell E a (toL (mom L g).1) := by
    rw [hm, ell_toL, ell_toL, Matrix.trace_mul_cycle, hk, one_mul]
  apply Subtype.ext
  change k.1 * ((mom L _).1 - _ • (1 : Matrix (Fin a) (Fin a) (Cinf E))) * star k.1 =
    (mom L g).1 - _ • (1 : Matrix (Fin a) (Fin a) (Cinf E))
  rw [he, hm, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, hk, ← mul_assoc, ← mul_assoc, hk, one_mul,
    mul_assoc, hk, mul_one]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.RealLieGroupChartsSmooth
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.QuadraticFormGradientFormula
open UpperTheory.V.Lit.Geo
open NumberField GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open scoped ContDiff

section
variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private theorem qf_mem : (fun x : Fin a → Cinf E => ((qf x : ℝ) : ℂ)) ∈ poly E a := by
  have h : (fun x : Fin a → Cinf E => ((qf x : ℝ) : ℂ)) =
      ∑ i : Fin a, ∑ w : InfinitePlace E,
        ((fun x : Fin a → Cinf E => x i w) * (fun x : Fin a → Cinf E => (starRingEnd ℂ) (x i w))) := by
    funext x
    simp only [qf, Finset.sum_apply, Pi.mul_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  rw [h]
  refine Subalgebra.sum_mem _ fun i _ => Subalgebra.sum_mem _ fun w _ => Subalgebra.mul_mem _ ?_ ?_
  · exact Algebra.subset_adjoin ⟨⟨⟨fun x => x i w, fun _ _ => rfl⟩, fun _ _ => rfl⟩, rfl⟩
  · refine Algebra.subset_adjoin ⟨⟨⟨fun x => (starRingEnd ℂ) (x i w), fun _ _ => ?_⟩, fun c x => ?_⟩, rfl⟩
    · simp
    · simp

private theorem pg_eq (P : (Fin a → Cinf E) → ℂ) :
    pg P = fun x => P x * Complex.exp (-(Real.pi : ℂ) * ((qf x : ℝ) : ℂ)) := by
  funext x
  simp only [pg, gauss]
  push_cast
  rfl

private theorem fderiv_pg {P : (Fin a → Cinf E) → ℂ} (hP : P ∈ poly E a) (x u : Fin a → Cinf E) :
    fderiv ℝ (pg P) x u = (fderiv ℝ P x u - (Real.pi : ℂ) * (P x *
      fderiv ℝ (fun y : Fin a → Cinf E => ((qf y : ℝ) : ℂ)) x u)) * (gauss x : ℝ) := by
  have h1 : HasFDerivAt P (fderiv ℝ P x) x :=
    (((UpperTheory.admissibleFunctionClass_closure_properties E a P hP).1.differentiable (by simp)) x).hasFDerivAt
  have h2 := (((UpperTheory.admissibleFunctionClass_closure_properties E a _ qf_mem).1.differentiable (by simp)) x).hasFDerivAt
  have h3 := h1.mul ((h2.const_mul (-(Real.pi : ℂ))).cexp)
  have hg : ((gauss x : ℝ) : ℂ) = Complex.exp (-(Real.pi : ℂ) * ((qf x : ℝ) : ℂ)) := by
    simp only [gauss]
    push_cast
    rfl
  have h4 := h3.fderiv
  rw [pg_eq, hg]
  erw [h4]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

end

theorem UpperTheory.quadratic_form_gradient_formula :
    PolyD := by
  intro E _ _ a P hP
  obtain ⟨hP1, -, hP3⟩ := UpperTheory.admissibleFunctionClass_closure_properties E a P hP
  obtain ⟨hR1, -, hR3⟩ := UpperTheory.admissibleFunctionClass_closure_properties E a _ qf_mem
  refine ⟨?_, ?_, fun T => ?_⟩
  · rw [pg_eq]
    exact hP1.mul (contDiff_const.mul hR1).cexp
  · let b := Module.finBasis ℝ (Fin a → Cinf E)
    obtain ⟨C₀, hC₀, hb⟩ := b.exists_opNorm_le (F := ℂ)
    have hQ : ∀ u : Fin a → Cinf E, ∃ (C : ℝ) (k : ℕ), ∀ x, ‖fderiv ℝ P x u - (Real.pi : ℂ) * (P x *
        fderiv ℝ (fun y : Fin a → Cinf E => ((qf y : ℝ) : ℂ)) x u)‖ ≤ C * (1 + qf x) ^ k := fun u =>
      (UpperTheory.admissibleFunctionClass_closure_properties E a _ (Subalgebra.sub_mem _ ((hP3 0).2.2 u)
        (Subalgebra.smul_mem _ (Subalgebra.mul_mem _ hP ((hR3 0).2.2 u)) (Real.pi : ℂ)))).2.1
    choose C k hCk using hQ
    refine ⟨C₀ * ∑ i, |C (b i)|, ∑ i, k (b i), fun x => ?_⟩
    have hq : 1 ≤ 1 + qf x := by linarith [qf_nonneg x]
    have hg : 0 < gauss x := Real.exp_pos _
    have hS : 0 ≤ ∑ i, |C (b i)| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have key := hb (u := fderiv ℝ (pg P) x) (M := (∑ i, |C (b i)|) * (1 + qf x) ^ (∑ i, k (b i)) * gauss x)
      (by positivity) (fun i => by
        rw [fderiv_pg hP, norm_mul, Complex.norm_real, Real.norm_of_nonneg hg.le]
        refine mul_le_mul_of_nonneg_right ((hCk (b i) x).trans ?_) hg.le
        refine (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)).trans ?_
        refine mul_le_mul ?_ (pow_le_pow_right₀ hq ?_) (by positivity) hS
        · exact Finset.single_le_sum (f := fun i => |C (b i)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
        · exact Finset.single_le_sum (f := fun i => k (b i)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
    calc _ ≤ _ := key
      _ = _ := by ring
  · exact ⟨_, Subalgebra.sub_mem _ (hP3 T).1
      (Subalgebra.smul_mem _ (Subalgebra.mul_mem _ hP (hR3 T).1) (Real.pi : ℂ)), fun x => fderiv_pg hP x (T x)⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.SumDer
open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor

section
variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private theorem vm_le (v : Fin a → Cinf E) (Z : Lie E a) : ‖v ᵥ* Matrix.of Z‖ ≤ a * ‖v‖ * ‖Z‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  have h : (v ᵥ* Matrix.of Z) j = ∑ i, v i * Z i j := rfl
  rw [h]
  refine (norm_sum_le _ _).trans ?_
  have h2 : ∀ i ∈ (Finset.univ : Finset (Fin a)), ‖v i * Z i j‖ ≤ ‖v‖ * ‖Z‖ := fun i _ =>
    (norm_mul_le _ _).trans (mul_le_mul (norm_le_pi_norm v i)
      ((norm_le_pi_norm (Z i) j).trans (norm_le_pi_norm Z i)) (norm_nonneg _) (norm_nonneg _))
  refine (Finset.sum_le_sum h2).trans (le_of_eq ?_)
  simp [mul_assoc]

private noncomputable def vmL (v : Fin a → Cinf E) : Lie E a →L[ℝ] (Fin a → Cinf E) :=
  LinearMap.mkContinuous
    { toFun := fun Z => v ᵥ* Matrix.of Z
      map_add' := fun Z W => Matrix.vecMul_add (Matrix.of Z) (Matrix.of W) v
      map_smul' := fun c Z => by
        ext j w
        simp [Matrix.vecMul, dotProduct, Finset.mul_sum, mul_left_comm] }
    (a * ‖v‖) (fun Z => vm_le v Z)

private theorem vmL_norm (v : Fin a → Cinf E) : ‖vmL v‖ ≤ a * ‖v‖ :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

private theorem low {y : Lie E a} (hy : y ∈ invSet E a) :
    ∃ r M : ℝ, 0 < r ∧ 0 ≤ M ∧ ∀ z ∈ Metric.ball y r, ∀ v : Fin a → Cinf E, ‖v‖ ≤ M * ‖v ᵥ* Matrix.of z‖ := by
  obtain ⟨u, hu⟩ := hy
  set B : ℝ := a * ‖toL (u⁻¹).val‖ with hB
  have hB0 : 0 ≤ B := by positivity
  have ha : (0:ℝ) ≤ a := Nat.cast_nonneg a
  have hp : 0 < 2 * (B * a + 1) := by positivity
  refine ⟨1 / (2 * (B * a + 1)), 2 * B, by positivity, by positivity, fun z hz v => ?_⟩
  have h1 : ‖v‖ ≤ B * ‖v ᵥ* Matrix.of y‖ := by
    have h := vm_le (v ᵥ* Matrix.of y) (toL (u⁻¹).val)
    have e : (v ᵥ* Matrix.of y) ᵥ* Matrix.of (toL (u⁻¹).val) = v := by
      rw [Matrix.vecMul_vecMul, ← hu]
      change v ᵥ* (u.val * (u⁻¹).val) = v
      rw [Units.mul_inv, Matrix.vecMul_one]
    rw [e] at h
    calc _ ≤ _ := h
      _ = _ := by rw [hB]; ring
  have h2 : v ᵥ* Matrix.of y = v ᵥ* Matrix.of z + v ᵥ* Matrix.of (y - z) := by
    have := (vmL v).map_add z (y - z)
    rw [add_sub_cancel] at this
    exact this
  have h3 : ‖y - z‖ * (2 * (B * a + 1)) ≤ 1 := by
    rw [Metric.mem_ball, dist_comm, dist_eq_norm, lt_div_iff₀ hp] at hz
    exact hz.le
  have h4 : ‖v ᵥ* Matrix.of y‖ ≤ ‖v ᵥ* Matrix.of z‖ + a * ‖v‖ * ‖y - z‖ := by
    rw [h2]
    exact (norm_add_le _ _).trans (by gcongr; exact vm_le v _)
  have h5 := mul_le_mul_of_nonneg_left h4 hB0
  have h6 := mul_le_mul_of_nonneg_left h3 (norm_nonneg v)
  have h7 : 0 ≤ ‖v‖ * ‖y - z‖ := by positivity
  nlinarith

private theorem expb (k : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 0 ≤ t →
    (1 + t) ^ k * Real.exp (-Real.pi * t) ≤ K * Real.exp (-Real.pi * (t / 2)) := by
  refine ⟨k.factorial * Real.exp 1, by positivity, fun t ht => ?_⟩
  have h := Real.pow_div_factorial_le_exp (1 + t) (by positivity) k
  rw [div_le_iff₀ (by positivity)] at h
  have h2 : Real.exp (1 + t) * Real.exp (-Real.pi * t) ≤ Real.exp 1 * Real.exp (-Real.pi * (t / 2)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith [Real.pi_gt_three]
  calc _ ≤ (Real.exp (1 + t) * k.factorial) * Real.exp (-Real.pi * t) := by gcongr
    _ = k.factorial * (Real.exp (1 + t) * Real.exp (-Real.pi * t)) := by ring
    _ ≤ k.factorial * (Real.exp 1 * Real.exp (-Real.pi * (t / 2))) := by gcongr
    _ = _ := by ring

private theorem dom {y : Lie E a} (hy : y ∈ invSet E a) :
    ∃ r M c : ℝ, 0 < r ∧ 0 ≤ M ∧ 0 < c ∧ ∀ k : ℕ, ∃ K : ℝ, ∀ z ∈ Metric.ball y r, ∀ v : Fin a → Cinf E,
      ‖v‖ ≤ M * (1 + qf (v ᵥ* Matrix.of z)) ∧
      (1 + qf (v ᵥ* Matrix.of z)) ^ k * gauss (v ᵥ* Matrix.of z) ≤ K * Real.exp (-Real.pi * (c * qf v)) := by
  obtain ⟨r, M, hr, hM, h⟩ := low hy
  have hq := (UpperTheory.geometric_side_quadraticForm_identity E a).2.2.2.2.2
  set D : ℝ := a * Fintype.card (InfinitePlace E) with hD
  have hD0 : 0 ≤ D := by positivity
  have hp : 0 < 2 * (D * M ^ 2 + 1) := by positivity
  refine ⟨r, M, 1 / (2 * (D * M ^ 2 + 1)), hr, hM, by positivity, fun k => ?_⟩
  obtain ⟨K, hK, hk⟩ := expb k
  refine ⟨K, fun z hz v => ?_⟩
  have h1 := h z hz v
  have h2 := (hq (v ᵥ* Matrix.of z)).1
  have h3 := (hq v).2
  have h0 := qf_nonneg (v ᵥ* Matrix.of z)
  refine ⟨h1.trans (mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (‖v ᵥ* Matrix.of z‖ - 1)]) hM), ?_⟩
  refine (hk _ h0).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hK)
  have h4 : ‖v‖ ^ 2 ≤ M ^ 2 * qf (v ᵥ* Matrix.of z) := by
    calc _ ≤ (M * ‖v ᵥ* Matrix.of z‖) ^ 2 := by gcongr
      _ = M ^ 2 * ‖v ᵥ* Matrix.of z‖ ^ 2 := by ring
      _ ≤ _ := by gcongr
  have h5 : 1 / (2 * (D * M ^ 2 + 1)) * qf v ≤ qf (v ᵥ* Matrix.of z) / 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hp]
    have := mul_le_mul_of_nonneg_left h4 hD0
    nlinarith
  have := mul_le_mul_of_nonneg_left h5 Real.pi_pos.le
  linarith

end

theorem UpperTheory.sum_der :
    SumDer := by
  intro E _ _ a ι x N hS P hP y hy
  obtain ⟨r, M, c, hr, hM, hc, hd⟩ := dom hy
  obtain ⟨-, ⟨C, k, hC⟩, -⟩ := UpperTheory.admissibleFunctionClass_closure_properties E a P hP
  obtain ⟨hsm, ⟨C', k', hC'⟩, -⟩ := UpperTheory.quadratic_form_gradient_formula E a P hP
  have hs := (hS.2 c c hc le_rfl).1
  have hy0 : y ∈ Metric.ball y r := Metric.mem_ball_self hr
  have hg : ∀ v : Fin a → Cinf E, 0 < gauss v := fun v => Real.exp_pos _
  have h0 : Summable fun i => pg P (x i ᵥ* Matrix.of y) := by
    obtain ⟨K, hK⟩ := hd k
    refine Summable.of_norm_bounded (hs.mul_left (|C| * K)) fun i => ?_
    have h1 := (hK y hy0 (x i)).2
    have h2 := qf_nonneg (x i ᵥ* Matrix.of y)
    have h3 := hg (x i ᵥ* Matrix.of y)
    rw [pg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h3]
    calc _ ≤ (|C| * (1 + qf (x i ᵥ* Matrix.of y)) ^ k) * gauss (x i ᵥ* Matrix.of y) := by
          gcongr
          exact (hC _).trans (by gcongr; exact le_abs_self C)
      _ = |C| * ((1 + qf (x i ᵥ* Matrix.of y)) ^ k * gauss (x i ᵥ* Matrix.of y)) := by ring
      _ ≤ |C| * (K * _) := by gcongr
      _ = _ := by ring
  obtain ⟨K, hK⟩ := hd (k' + 1)
  have hu := hs.mul_left (|C'| * (a * M) * K)
  have hb : ∀ i z, z ∈ Metric.ball y r → ‖(fderiv ℝ (pg P) (x i ᵥ* Matrix.of z)).comp (vmL (x i))‖ ≤
      |C'| * (a * M) * K * Real.exp (-Real.pi * (c * qf (x i))) := by
    intro i z hz
    obtain ⟨h1, h2⟩ := hK z hz (x i)
    have h3 := qf_nonneg (x i ᵥ* Matrix.of z)
    have h4 := hg (x i ᵥ* Matrix.of z)
    calc _ ≤ _ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (|C'| * (1 + qf (x i ᵥ* Matrix.of z)) ^ k' * gauss (x i ᵥ* Matrix.of z)) *
            (a * (M * (1 + qf (x i ᵥ* Matrix.of z)))) := by
          refine mul_le_mul ((hC' _).trans (by gcongr; exact le_abs_self C'))
            ((vmL_norm _).trans (by gcongr)) (norm_nonneg _) (by positivity)
      _ = |C'| * (a * M) * ((1 + qf (x i ᵥ* Matrix.of z)) ^ (k' + 1) * gauss (x i ᵥ* Matrix.of z)) := by ring
      _ ≤ |C'| * (a * M) * (K * _) := by gcongr
      _ = _ := by ring
  have hF := hasFDerivAt_tsum_of_isPreconnected (𝕜 := ℝ)
    (f := fun i (z : Lie E a) => pg P (x i ᵥ* Matrix.of z))
    (f' := fun i z => (fderiv ℝ (pg P) (x i ᵥ* Matrix.of z)).comp (vmL (x i)))
    hu Metric.isOpen_ball (convex_ball y r).isPreconnected
    (fun i z _ => ((hsm.differentiable (by simp)) _).hasFDerivAt.comp z (vmL (x i)).hasFDerivAt)
    hb hy0 h0 hy0
  have hF' : HasFDerivAt (msum x P) _ y := hF
  refine ⟨h0, hF'.differentiableAt, fun Z => ?_⟩
  rw [hF'.fderiv]
  exact (ContinuousLinearMap.apply ℝ ℂ Z).map_tsum (Summable.of_norm_bounded hu fun i => hb i y hy0)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.HermitianChartScalarInvariance
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.SmoothSumLeftRightMulOrder
open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep
open scoped ContDiff

noncomputable section

namespace UpperTheory.V.Geo.SmoothSumOrder

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

private theorem smooth_inv (l : Matrix (Fin a) (Fin a) (Cinf E) →ₗ[ℝ] ℝ) :
    ContDiffOn ℝ ∞ (fun y : Lie E a => l (Ring.inverse (Matrix.of y))) (invSet E a) := by
  haveI : CompleteSpace (Matrix (Fin a) (Fin a) (Cinf E)) := FiniteDimensional.complete ℝ _
  intro y hy
  let S : Lie E a →L[ℝ] Matrix (Fin a) (Fin a) (Cinf E) :=
    LinearMap.toContinuousLinearMap (Matrix.ofLinearEquiv ℝ).toLinearMap
  have hu : IsUnit (S y) := hy
  have h : ContDiffAt ℝ ∞ Ring.inverse (S y) := by
    simpa using contDiffAt_ringInverse ℝ (n := ∞) hu.unit
  exact ((LinearMap.toContinuousLinearMap l).contDiff.contDiffAt.comp y
    (h.comp y S.contDiff.contDiffAt)).contDiffWithinAt

end

private def rmul (M : Matrix (Fin a) (Fin a) (Cinf E)) : (Fin a → Cinf E) →ₗ[ℝ] (Fin a → Cinf E) where
  toFun v := v ᵥ* M
  map_add' v w := Matrix.add_vecMul _ _ _
  map_smul' c v := Matrix.smul_vecMul _ _ _

private def lmul (v : Fin a → Cinf E) : Matrix (Fin a) (Fin a) (Cinf E) →ₗ[ℝ] (Fin a → Cinf E) where
  toFun M := v ᵥ* M
  map_add' M M' := Matrix.vecMul_add _ _ _
  map_smul' c M := Matrix.vecMul_smul _ _ _

private theorem order (ι : Type) (x : ι → Fin a → Cinf E) (N : ℕ) (hx : Scale (fun i => qf (x i)) N) (n : ℕ) :
    ∀ P ∈ poly E a, ContDiffOn ℝ n (msum x P) (invSet E a) := by
  induction n with
  | zero =>
    intro P hP
    exact contDiffOn_zero.2 fun y hy =>
      (UpperTheory.sum_der E a ι x N hx P hP y hy).2.1.continuousAt.continuousWithinAt
  | succ n ih =>
    intro P hP
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen isOpen_invSet]
    refine ⟨fun y hy => (UpperTheory.sum_der E a ι x N hx P hP y hy).2.1.differentiableWithinAt, by simp, ?_⟩
    rw [contDiffOn_clm_apply]
    intro Z
    let b := Module.finBasis ℝ (Matrix (Fin a) (Fin a) (Cinf E))
    choose Q hQ hQ' using fun j => (UpperTheory.quadratic_form_gradient_formula E a P hP).2.2 (rmul (b j))
    let l := fun j => (b.coord j).comp (LinearMap.mulRight ℝ (Matrix.of Z))
    have hs : ContDiffOn ℝ n (fun y : Lie E a => ∑ j, l j (Ring.inverse (Matrix.of y)) • msum x (Q j) y)
        (invSet E a) :=
      ContDiffOn.sum fun j _ => ((smooth_inv (l j)).of_le (by exact_mod_cast le_top)).smul (ih _ (hQ j))
    refine hs.congr fun y hy => ?_
    have hu : IsUnit (Matrix.of y) := hy
    have hterm : ∀ i, fderiv ℝ (pg P) (x i ᵥ* Matrix.of y) (x i ᵥ* Matrix.of Z) =
        ∑ j, l j (Ring.inverse (Matrix.of y)) • pg (Q j) (x i ᵥ* Matrix.of y) := by
      intro i
      have e1 : x i ᵥ* Matrix.of Z = lmul (x i ᵥ* Matrix.of y) (Ring.inverse (Matrix.of y) * Matrix.of Z) := by
        change _ = (x i ᵥ* Matrix.of y) ᵥ* _
        rw [Matrix.vecMul_vecMul, ← mul_assoc, Ring.mul_inverse_cancel _ hu, one_mul]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [e1, ← b.sum_repr (Ring.inverse (Matrix.of y) * Matrix.of Z), map_sum, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, map_smul, ← hQ' j]
      rfl
    rw [(UpperTheory.sum_der E a ι x N hx P hP y hy).2.2 Z, tsum_congr hterm,
      Summable.tsum_finsetSum fun j _ => (UpperTheory.sum_der E a ι x N hx _ (hQ j) y hy).1.const_smul _]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact (UpperTheory.sum_der E a ι x N hx _ (hQ j) y hy).1.tsum_const_smul _

end UpperTheory.V.Geo.SmoothSumOrder

theorem UpperTheory.smooth_sum_left_right_mul_order :
    SumSm := fun _ _ _ _ ι x N hx P hP =>
  contDiffOn_infty.2 fun n => UpperTheory.V.Geo.SmoothSumOrder.order ι x N hx n P hP
end
end

open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Lit.Bor
open scoped ContDiff

private theorem scal_mem {E : Type} [Field E] [NumberField E] {a : ℕ} {y : Lie E a} (hy : y ∈ invSet E a) :
    sc (Matrix.of y) • y ∈ invSet E a := by
  have hc : sc (Matrix.of y) ≠ 0 := (Real.exp_pos _).ne'
  have hy' : IsUnit (Matrix.of y) := hy
  have h : IsUnit (sc (Matrix.of y) • Matrix.of y) := by
    rw [Algebra.smul_def]
    exact ((IsUnit.mk0 _ hc).map (algebraMap ℝ (Matrix (Fin a) (Fin a) (Cinf E)))).mul hy'
  exact h

private theorem chart_eq {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (ha : 1 ≤ a)
    (L : AddSubgroup (Fin a → Af E)) (P : (Fin a → Cinf E) → ℂ) (g : GA E a) {y : Lie E a} (hy : y ∈ invSet E a) :
    chart (gsum L (pg P)) g y = msum (fun v : lat L g => pt (rt g) v.1) P (sc (Matrix.of y) • y) := by
  obtain ⟨u, hu⟩ := hy
  obtain rfl : y = toL u.val := hu.symm
  rw [chart_val, (UpperTheory.point_evaluation_multiplicative_tsum E a ha L ℂ (pg P)).2.1 g u]
  refine tsum_congr fun v => congrArg (pg P) ?_
  exact (Matrix.vecMul_smul _ _ _).symm

theorem UpperTheory.hermitian_chart_scalar_invariance :
    ThSm := by
  intro E _ _ _ a ha L hL P hP
  obtain ⟨N, hN⟩ := UpperTheory.geometry_of_numbers_lattice_estimate E a ha L hL
  obtain ⟨hs, h1, hd, -⟩ := UpperTheory.deriv_similitudeChar_at_one_eq_trace E a
  have hS : ContDiffOn ℝ ∞ (fun y : Lie E a => sc (Matrix.of y) • y) (invSet E a) := hs.smul contDiffOn_id
  refine ⟨⟨gsum L (pg P), fun g => ?_⟩, rfl, fun X => ?_⟩
  · exact ((UpperTheory.smooth_sum_left_right_mul_order E a _ _ N (hN g) P hP).comp hS fun y hy => scal_mem hy).congr
      fun y hy => chart_eq ha L P g hy
  · have ho : oneL E a ∈ invSet E a := isUnit_one
    have hn : invSet E a ∈ nhds (oneL E a) := isOpen_invSet.mem_nhds ho
    have h1' : sc (Matrix.of (oneL E a)) = 1 := h1
    have hsd : DifferentiableAt ℝ (fun y : Lie E a => sc (Matrix.of y)) (oneL E a) :=
      (hs.contDiffAt hn).differentiableAt (by simp)
    have hSd := hsd.hasFDerivAt.smul (hasFDerivAt_id (oneL E a))
    let Z : Lie E a := X + (-ell E a X) • oneL E a
    let T : (Fin a → Cinf E) →ₗ[ℝ] (Fin a → Cinf E) := (Matrix.vecMulLinear (Matrix.of Z)).restrictScalars ℝ
    obtain ⟨Q, hQ, hT⟩ := (UpperTheory.quadratic_form_gradient_formula E a P hP).2.2 T
    refine ⟨Q, hQ, funext fun g => ?_⟩
    obtain ⟨-, hF, hF'⟩ := UpperTheory.sum_der E a _ _ N (hN g) P hP _ ho
    have e : chart (gsum L (pg P)) g =ᶠ[nhds (oneL E a)]
        msum (fun v : lat L g => pt (rt g) v.1) P ∘ fun y : Lie E a => sc (Matrix.of y) • y :=
      Filter.eventually_of_mem hn fun y hy => chart_eq ha L P g hy
    have hF1 : HasFDerivAt (msum (fun v : lat L g => pt (rt g) v.1) P)
        (fderiv ℝ (msum (fun v : lat L g => pt (rt g) v.1) P) (oneL E a)) (sc (Matrix.of (oneL E a)) • oneL E a) := by
      rw [h1', one_smul]
      exact hF.hasFDerivAt
    have hc := HasFDerivAt.comp (f := fun y : Lie E a => sc (Matrix.of y) • y) (oneL E a) hF1 hSd
    change fderiv ℝ (chart (gsum L (pg P)) g) (oneL E a) X = _
    rw [e.fderiv_eq, hc.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, h1', one_smul, hd, id]
    rw [hF']
    refine tsum_congr fun v => ?_
    rw [← hT]
    have e1 : pt (rt g) v.1 ᵥ* Matrix.of (oneL E a) = pt (rt g) v.1 := Matrix.vecMul_one _
    rw [e1]
    rfl
end

open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep
open scoped ContDiff

section

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem chart_ex (g : GA E a) {x : Lie E a} (hx : x ∈ invSet E a) :
    ∃ y : GA E a, ∀ f : GA E a → ℂ, chart f g x = f y := by
  refine ⟨g * infGL E a (show IsUnit (Matrix.of x) from hx).unit, fun f => ?_⟩
  exact chart_val f g (show IsUnit (Matrix.of x) from hx).unit

private theorem chart_at_one (u : GA E a → ℂ) (g : GA E a) : chart u g (oneL E a) = u g := by
  simpa using chart_val u g 1

private theorem ev_inv : ∀ᶠ x in nhds (oneL E a), x ∈ invSet E a :=
  isOpen_invSet.mem_nhds (show oneL E a ∈ invSet E a from isUnit_one)

private theorem comp_mem {h : ℂ → ℂ} {S : Set ℂ} (hh : ContDiffOn ℝ ∞ h S) {f : GA E a → ℂ} (hf : f ∈ Sm E a)
    (hS : ∀ g, f g ∈ S) : (fun g => h (f g)) ∈ Sm E a := by
  intro g
  refine (hh.comp (hf g) fun x hx => ?_).congr fun x hx => ?_
  · obtain ⟨y, hy⟩ := chart_ex g hx
    rw [hy]; exact hS y
  · obtain ⟨y, hy⟩ := chart_ex g hx
    simp only [Function.comp, hy]

private theorem comp_lie {h : ℂ → ℂ} {f : GA E a → ℂ} (hf : f ∈ Sm E a) (g : GA E a) {d : ℂ}
    (hd : HasDerivAt h d (f g)) (X : Lie E a) : lieD X (fun g => h (f g)) g = d * lieD X f g := by
  have e : chart (fun g => h (f g)) g =ᶠ[nhds (oneL E a)] h ∘ chart f g := by
    filter_upwards [ev_inv] with x hx
    obtain ⟨y, hy⟩ := chart_ex g hx
    simp only [Function.comp, hy]
  rw [← chart_at_one f g] at hd
  have h2 := (hd.hasFDerivAt.restrictScalars ℝ).comp (oneL E a) (differentiableAt_chart hf g).hasFDerivAt
  rw [lieD, lieD, e.fderiv_eq, h2.fderiv]
  simp [mul_comm]

private theorem prodSm_mem {f f' : GA E a → ℂ} (h : f ∈ Sm E a) (h' : f' ∈ Sm E a) :
    (fun g => f g * f' g) ∈ Sm E a := by
  intro g
  refine ((h g).mul (h' g)).congr fun x hx => ?_
  obtain ⟨y, hy⟩ := chart_ex g hx
  simp only [hy]

private theorem prod_lie {f f' : GA E a → ℂ} (h : f ∈ Sm E a) (h' : f' ∈ Sm E a) (g : GA E a) (X : Lie E a) :
    lieD X (fun g => f g * f' g) g = f g * lieD X f' g + lieD X f g * f' g := by
  have e : chart (fun g => f g * f' g) g =ᶠ[nhds (oneL E a)] chart f g * chart f' g := by
    filter_upwards [ev_inv] with x hx
    obtain ⟨y, hy⟩ := chart_ex g hx
    simp only [Pi.mul_apply, hy]
  rw [lieD, lieD, lieD, e.fderiv_eq, fderiv_mul (differentiableAt_chart h g) (differentiableAt_chart h' g),
    chart_at_one, chart_at_one]
  simp [mul_comm]

end

theorem UpperTheory.realLieGroup_charts_smooth :
    MeanSm := by
  intro E _ _ _ a ha L hL
  have hT := (UpperTheory.hermitian_space_geometric_estimate E a ha L hL).1
  have hS := UpperTheory.hermitian_chart_scalar_invariance E a ha L hL
  have mem : ∀ P ∈ poly E a, mean L P ∈ meanAlg L := fun P hP => Algebra.subset_adjoin ⟨P, hP, rfl⟩
  obtain ⟨θ, hθ, hθX⟩ := hS 1 (one_mem _)
  have hv : ∀ g, θ.1 g = (Th L g : ℝ) := fun g => by rw [hθ]; exact (hT g).2
  have hpos : ∀ g, 0 < Th L g := fun g => lt_of_lt_of_le one_pos (hT g).1
  have hne : ∀ g, θ.1 g ≠ 0 := fun g => by
    rw [hv]; exact_mod_cast (hpos g).ne'
  have hsl : ∀ g, θ.1 g ∈ Complex.slitPlane := fun g => by
    rw [hv]; exact Complex.ofReal_mem_slitPlane.2 (hpos g)
  refine ⟨fun P hP => ?_, ?_⟩
  · obtain ⟨φ, hφ, hφX⟩ := hS P hP
    have hi : (fun g => (θ.1 g)⁻¹) ∈ Sm E a :=
      comp_mem (S := {0}ᶜ) ((contDiffOn_inv ℂ).restrict_scalars ℝ) θ.2 hne
    refine ⟨⟨fun g => φ.1 g * (θ.1 g)⁻¹, prodSm_mem φ.2 hi⟩, ?_, fun X => ?_⟩
    · funext g
      simp only [mean, hφ, hv, div_eq_mul_inv]
    · obtain ⟨Q, hQ, eQ⟩ := hφX X
      obtain ⟨R, hR, eR⟩ := hθX X
      have e : (lie E a X ⟨fun g => φ.1 g * (θ.1 g)⁻¹, prodSm_mem φ.2 hi⟩).1 = mean L Q - mean L P * mean L R := by
        funext g
        have e1 : lieD X φ.1 g = gsum L (pg Q) g := congrFun eQ g
        have e2 : lieD X θ.1 g = gsum L (pg R) g := congrFun eR g
        rw [GlobalTheory.CuspRep.lie_apply]
        change lieD X (fun g => φ.1 g * (fun g => (θ.1 g)⁻¹) g) g = _
        rw [prod_lie φ.2 hi, comp_lie θ.2 g (hasDerivAt_inv (hne g)), e1, e2]
        simp only [Pi.sub_apply, Pi.mul_apply, mean, ← hv, hφ]
        have := hne g
        field_simp
        ring
      rw [e]
      exact sub_mem (mem Q hQ) (mul_mem (mem P hP) (mem R hR))
  · have hl : (fun g => Complex.log (θ.1 g)) ∈ Sm E a :=
      comp_mem (S := Complex.slitPlane)
        (fun z hz => ((Complex.contDiffAt_log hz).restrict_scalars ℝ).contDiffWithinAt) θ.2 hsl
    refine ⟨⟨_, hl⟩, fun g => ?_, fun X => ?_⟩
    · change Complex.log (θ.1 g) = _
      rw [hv, fn, Complex.ofReal_log (hpos g).le]
    · obtain ⟨R, hR, eR⟩ := hθX X
      have e : (lie E a X ⟨_, hl⟩).1 = mean L R := by
        funext g
        have e2 : lieD X θ.1 g = gsum L (pg R) g := congrFun eR g
        rw [GlobalTheory.CuspRep.lie_apply]
        change lieD X (fun g => Complex.log (θ.1 g)) g = _
        rw [comp_lie θ.2 g (Complex.hasDerivAt_log (hsl g)), e2, mean, hv, div_eq_inv_mul]
      rw [e]
      exact mem R hR
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.LieDerivativeIsDerivationSmoothFunctions
open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep

section

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem chart_prod (f f' : GA E a → ℂ) (g : GA E a) :
    chart (f * f') g = chart f g * chart f' g := by
  funext x
  simp only [Pi.mul_apply, chart]
  split_ifs <;> simp

private theorem sm_prod_mem {f f' : GA E a → ℂ} (h : f ∈ Sm E a) (h' : f' ∈ Sm E a) : f * f' ∈ Sm E a := by
  intro g
  rw [chart_prod]
  exact (h g).mul (h' g)

private theorem leibniz (X : Lie E a) {f f' : GA E a → ℂ} (h : f ∈ Sm E a) (h' : f' ∈ Sm E a) :
    lieD X (f * f') = f * lieD X f' + lieD X f * f' := by
  funext g
  have v : ∀ u : GA E a → ℂ, chart u g (oneL E a) = u g := fun u => by
    simpa using chart_val u g 1
  simp only [lieD, Pi.add_apply, Pi.mul_apply]
  rw [chart_prod, fderiv_mul (differentiableAt_chart h g) (differentiableAt_chart h' g), v, v]
  simp [mul_comm]

private theorem const_ev (c : ℂ) (g : GA E a) {x : Lie E a} (hx : x ∈ invSet E a) :
    chart (algebraMap ℂ (GA E a → ℂ) c) g x = c := by
  unfold chart
  rw [dite_eq_left (show IsUnit (Matrix.of x) from hx)]
  rfl

private theorem const_mem (c : ℂ) : algebraMap ℂ (GA E a → ℂ) c ∈ Sm E a := fun g =>
  contDiffOn_const.congr fun _ hx => const_ev c g hx

private theorem lie_const (X : Lie E a) (c : ℂ) : lieD X (algebraMap ℂ (GA E a → ℂ) c) = 0 := by
  funext g
  have e : chart (algebraMap ℂ (GA E a → ℂ) c) g =ᶠ[nhds (oneL E a)] fun _ => c := by
    have h1 : oneL E a ∈ invSet E a := isUnit_one
    filter_upwards [isOpen_invSet.mem_nhds h1] with x hx using const_ev c g hx
  rw [lieD, e.fderiv_eq]
  simp

end

theorem UpperTheory.lieDerivative_isDerivation_smoothFunctions :
    BddAlg := by
  intro E _ _ _ a S hS
  have key : ∀ f ∈ Algebra.adjoin ℂ S, (∃ C : ℝ, ∀ g, ‖f g‖ ≤ C) ∧ f ∈ Sm E a ∧
      ∀ X : Lie E a, lieD X f ∈ Algebra.adjoin ℂ S := by
    intro f hf
    induction hf using Algebra.adjoin_induction with
    | mem f hf =>
      obtain ⟨hb, φ, rfl, hX⟩ := hS f hf
      exact ⟨hb, φ.2, hX⟩
    | algebraMap c =>
      exact ⟨⟨‖c‖, fun g => by simp⟩, const_mem c, fun X => by rw [lie_const]; exact zero_mem _⟩
    | add f f' _ _ h h' =>
      obtain ⟨⟨C, hC⟩, hs, hX⟩ := h
      obtain ⟨⟨C', hC'⟩, hs', hX'⟩ := h'
      refine ⟨⟨C + C', fun g => (norm_add_le _ _).trans (add_le_add (hC g) (hC' g))⟩, add_mem hs hs', fun X => ?_⟩
      have e : lieD X (f + f') = lieD X f + lieD X f' :=
        congrArg Subtype.val ((lie E a X).map_add (⟨f, hs⟩ : Sm E a) (⟨f', hs'⟩ : Sm E a))
      rw [e]
      exact add_mem (hX X) (hX' X)
    | mul f f' hf hf' h h' =>
      obtain ⟨⟨C, hC⟩, hs, hX⟩ := h
      obtain ⟨⟨C', hC'⟩, hs', hX'⟩ := h'
      refine ⟨⟨C * C', fun g => (norm_mul_le _ _).trans
        (mul_le_mul (hC g) (hC' g) (norm_nonneg _) ((norm_nonneg _).trans (hC g)))⟩, sm_prod_mem hs hs', fun X => ?_⟩
      rw [leibniz X hs hs']
      exact add_mem (mul_mem hf (hX' X)) (mul_mem (hX X) hf')
  have main : ∀ ψ : Sm E a, (∀ X, (lie E a X ψ).1 ∈ Algebra.adjoin ℂ S) → BddDer ψ := by
    intro ψ hψ
    have h : ∀ (l : List (Lie E a)) (X : Lie E a),
        (((X :: l).map (lie E a)).prod ψ).1 ∈ Algebra.adjoin ℂ S := by
      intro l
      induction l with
      | nil => intro X; simpa using hψ X
      | cons Y l ih =>
        intro X
        rw [List.map_cons, List.prod_cons]
        exact (key _ (ih Y)).2.2 X
    exact fun X l => (key _ (h l X)).1
  exact ⟨fun f hf => ⟨⟨f, (key f hf).2.1⟩, rfl, main _ (key f hf).2.2⟩, main⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.UnitaryGroupLieAlgebraEqSkewHermitian
open UpperTheory.V.Lit.Geo NumberField Matrix GlobalTheory.CuspRep Topology Filter

theorem UpperTheory.unitaryGroup_lieAlgebra_eq_skewHermitian :
    LatEx := by
  intro E _ _ a U hU
  let O : Set (Af E) := GroundTheory.Global.integralFiniteAdeles (𝓞 E) E
  have hOo : IsOpen O := GroundTheory.Global.isOpen_integralFiniteAdeles (R := 𝓞 E) (K := E)
  have hOc : IsCompact O := GroundTheory.Global.isCompact_integralFiniteAdeles E
  let B : Set (Fin a → Af E) := Set.univ.pi fun _ => O
  have hBo : IsOpen B := isOpen_set_pi Set.finite_univ fun _ _ => hOo
  have hBc : IsCompact B := isCompact_univ_pi fun _ => hOc
  have hB0 : (0 : Fin a → Af E) ∈ B := fun _ _ => (GroundTheory.Global.integralFiniteAdeles (𝓞 E) E).zero_mem
  let L : AddSubgroup (Fin a → Af E) :=
    { carrier := {x | ∀ u ∈ U, x ᵥ* u.val ∈ B}
      zero_mem' := fun u _ => by rw [Matrix.zero_vecMul]; exact hB0
      add_mem' := fun {x y} hx hy u hu => by
        rw [Matrix.add_vecMul]
        exact fun i hi => (GroundTheory.Global.integralFiniteAdeles (𝓞 E) E).add_mem (hx u hu i hi) (hy u hu i hi)
      neg_mem' := fun {x} hx u hu => by
        rw [Matrix.neg_vecMul]
        exact fun i hi => (GroundTheory.Global.integralFiniteAdeles (𝓞 E) E).neg_mem (hx u hu i hi) }
  have hc : Continuous fun p : (Fin a → Af E) × GL (Fin a) (Af E) => p.1 ᵥ* p.2.val :=
    continuous_fst.matrix_vecMul (Units.continuous_val.comp continuous_snd)
  have hn : (L : Set (Fin a → Af E)) ∈ 𝓝 0 := by
    refine hU.eventually_forall_of_forall_eventually (x₀ := (0 : Fin a → Af E))
      (P := fun x (u : GL (Fin a) (Af E)) => x ᵥ* u.val ∈ B) fun u _ => ?_
    refine hc.continuousAt.eventually_mem (hBo.mem_nhds ?_)
    simpa only [Matrix.zero_vecMul] using hB0
  have ho : IsOpen (L : Set (Fin a → Af E)) := L.isOpen_of_mem_nhds hn
  refine ⟨L, ⟨ho, hBc.of_isClosed_subset (L.isClosed_of_isOpen ho) fun x hx => ?_⟩, fun u hu x hx v hv => ?_⟩
  · simpa only [Units.val_one, Matrix.vecMul_one] using hx 1 U.one_mem
  · rw [Matrix.vecMul_vecMul]
    exact hx (u * v) (U.mul_mem hu hv)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.UnitarySimilitudeGroupIsSmoothCmDatum
open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit.Dr

theorem UpperTheory.unitarySimilitudeGroup_isSmooth_cmDatum :
    RootEx := by
  intro E _ _ a
  obtain ⟨τ, -, hτ⟩ := locSec E a (hOne E a) hOne_mem_cone
  obtain ⟨ε, hε, hball⟩ := Metric.nhds_basis_closedBall.eventually_iff.1 hτ
  have hK : Metric.closedBall (hOne E a) ε ⊆ cone E a := fun p hp => ⟨τ p, hball hp⟩
  obtain ⟨C, hC⟩ := boundInf E a _ hK (isCompact_closedBall _ _)
  refine ⟨ε, C, hε, fun Y hY => ?_⟩
  have h1 : hOne E a ∈ Metric.closedBall (hOne E a) ε := Metric.mem_closedBall_self hε.le
  have hp : hOne E a + hv Y ∈ Metric.closedBall (hOne E a) ε := by
    rw [mem_closedBall_iff_norm, add_sub_cancel_left]
    exact hY
  have hs := hball hp
  refine ⟨τ (hOne E a + hv Y), ?_, hC _ _ h1 (by rw [hs]; exact hp), hC _ _ hp ?_⟩
  · have h2 := sand_val (τ (hOne E a + hv Y)) (hOne E a)
    rw [hs, hOne_val, mul_one] at h2
    exact h2.symm
  · have h3 : sand (τ (hOne E a + hv Y))⁻¹ (sand (τ (hOne E a + hv Y)) (hOne E a)) = hOne E a := by
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
    rw [hs] at h3
    rw [h3]; exact h1
end

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open UpperTheory.V.Lit.Geo

private theorem trF_smul {E : Type} [Field E] [NumberField E] {a : ℕ} (s : ℝ) (X Y : Matrix (Fin a) (Fin a) (Cinf E)) :
    trF X (s • Y) = s * trF X Y := by
  simp [trF, Finset.mul_sum]

theorem UpperTheory.V.Lit.Geo.stepEx :
    StepEx := by
  intro E _ _ _ a ha U hU
  obtain ⟨L, hL, hUL⟩ := UpperTheory.unitaryGroup_lieAlgebra_eq_skewHermitian E a U hU
  obtain ⟨ε₁, C₁, hε₁, hroot⟩ := UpperTheory.unitarySimilitudeGroup_isSmooth_cmDatum E a
  obtain ⟨hI1, hI2, hI3⟩ := UpperTheory.lattice_point_count_bound E a ha L
  have hK := UpperTheory.hermitian_gaussian_moment_bound E a ha L hL
  obtain ⟨hT, hM⟩ := UpperTheory.hermitian_space_geometric_estimate E a ha L hL
  obtain ⟨hS1, φ, hφ, hS2⟩ := UpperTheory.realLieGroup_charts_smooth E a ha L hL
  obtain ⟨hB1, hB2⟩ := UpperTheory.lieDerivative_isDerivation_smoothFunctions E a {f | ∃ P ∈ poly E a, f = mean L P} (by
    rintro _ ⟨P, hP, rfl⟩
    exact ⟨(hM P hP).2, hS1 P hP⟩)
  obtain ⟨hD1, ⟨B, hB, hD2⟩, hD3⟩ := UpperTheory.hermitian_trace_form_estimate E a ha L hL
  obtain ⟨C₂, ε₂, hC₂, hε₂, hTay⟩ := UpperTheory.hermitian_trace_form_entry_estimate E a ha L hL
  obtain ⟨C₃, hC₃⟩ := UpperTheory.hermitian_space_log_estimate E a ha L hL
  obtain ⟨C₄, hC₄⟩ := UpperTheory.hermitian_space_point_log_estimate E a ha L hL
  obtain ⟨c₀, f₀, hc₀, hG⟩ := UpperTheory.traceForm_posDef_of_totallyReal E a ha L hL
  obtain ⟨δ, hδ, hδ1, hδ2, hδ3⟩ : ∃ δ : ℝ, 0 < δ ∧ δ * B ≤ ε₁ ∧ δ * B ≤ ε₂ ∧ C₂ * (δ * B) ^ 2 ≤ δ * c₀ := by
    have hp : 0 < C₂ * B ^ 2 + 1 := by positivity
    refine ⟨min (min (ε₁ / B) (ε₂ / B)) (c₀ / (C₂ * B ^ 2 + 1)), by positivity, ?_, ?_, ?_⟩
    · exact (le_div_iff₀ hB).1 ((min_le_left _ _).trans (min_le_left _ _))
    · exact (le_div_iff₀ hB).1 ((min_le_left _ _).trans (min_le_right _ _))
    · set d := min (min (ε₁ / B) (ε₂ / B)) (c₀ / (C₂ * B ^ 2 + 1))
      have h0 : 0 < d := by positivity
      have h1 : d * (C₂ * B ^ 2 + 1) ≤ c₀ := (le_div_iff₀ hp).1 (min_le_right _ _)
      nlinarith
  have hf0 : ∀ g, 0 ≤ fn L g := fun g => Real.log_nonneg (hT g).1
  have hq0 : ∀ g : GA E a, 0 ≤ Real.log (qht g) := fun g => Real.log_nonneg
    (le_ciInf fun _ => GroundTheory.Automorphic.AutomorphicForm.one_le_height _)
  have hn : ∀ g (t : ℝ), |t| ≤ 1 → ‖toL (t • ((-δ) • dev L g).1)‖ ≤ δ * B := fun g t ht => by
    change ‖t • (-δ) • toL (dev L g).1‖ ≤ _
    rw [norm_smul, norm_smul, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hδ]
    have h1 := mul_le_mul_of_nonneg_left (hD2 g).2.1 hδ.le
    have h2 : 0 ≤ δ * ‖toL (dev L g).1‖ := by positivity
    nlinarith
  have key : ∀ g (t : ℝ) (h : GL (Fin a) (Cinf E)), |t| ≤ 1 → h.val * star h.val = 1 + t • ((-δ) • dev L g).1 →
      |fn L (g * infGL E a h) - fn L g - Real.pi * t * δ * trF (dev L g).1 (dev L g).1| ≤ δ * c₀ := fun g t h ht hh => by
    have h0 : ell E a (toL (t • ((-δ) • dev L g).1)) = 0 := by
      change ell E a (t • (-δ) • toL (dev L g).1) = 0
      rw [map_smul, map_smul, (hD3 g).1, smul_zero, smul_zero]
    have h1 := hTay g _ h h0 ((hn g t ht).trans hδ2) hh
    have h2 : trF (mom L g).1 (t • ((-δ) • dev L g).1) = -(t * δ * trF (dev L g).1 (dev L g).1) := by
      change trF (mom L g).1 (t • (-δ) • (dev L g).1) = _
      rw [trF_smul, trF_smul, (hD3 g).2]
      ring
    rw [h2] at h1
    have h3 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hn g t ht) 2) hC₂
    refine le_trans (le_of_eq ?_) (h1.trans (h3.trans hδ3))
    congr 1
    ring
  have hπ : 0 ≤ Real.pi - 2 := by linarith [Real.pi_gt_three]
  refine ⟨fn L, fun g => (-δ) • dev L g, max (max C₁ (Real.pi * δ * B + δ * c₀)) (max C₃ C₄), δ * c₀, f₀,
    ⟨mul_pos hδ hc₀, ⟨φ, hφ, hB2 φ hS2⟩, fun γ t g => (hI1 γ t g).1, fun k g => ?_, fun u hu g => (hI2 U hU hUL u hu g).1,
      hf0, fun g => ?_, fun g => ?_, fun i j w => ?_, fun γ t g => ?_, fun k g => ?_, fun u hu g => ?_, fun g t ht => ?_,
      fun g h hg hh => ?_, fun g h hg hh => ?_, fun g t h ht hh => ?_⟩⟩
  · rw [fn, hI3, fn]
  · exact (hC₃ g).trans (mul_le_mul_of_nonneg_right (le_max_of_le_right (le_max_left _ _)) (by linarith [hq0 g]))
  · exact (hC₄ g).trans (mul_le_mul_of_nonneg_right (le_max_of_le_right (le_max_right _ _)) (by linarith [hf0 g]))
  · obtain ⟨ψ, h1, h2⟩ := hB1 _ (Subalgebra.smul_mem _ (hD1 i j w) ((-δ : ℝ) : ℂ))
    exact ⟨ψ, fun g => by rw [h1]; rfl, h2⟩
  · rw [(hI1 γ t g).2]
  · rw [← hK k g]
    exact Subtype.ext (by simp [adHerm])
  · rw [(hI2 U hU hUL u hu g).2]
  · obtain ⟨h, h1, h2, h3⟩ := hroot (t • (-δ) • dev L g) ((hn g t ht).trans hδ1)
    exact ⟨h, h1, h2.trans (le_max_of_le_left (le_max_left _ _)), h3.trans (le_max_of_le_left (le_max_left _ _))⟩
  · have h1 := (abs_le.1 (key g 1 h (by simp) (by rwa [one_smul]))).1
    have h2 := mul_le_mul_of_nonneg_left (hG g hg) hδ.le
    have h3 := mul_pos hδ hc₀
    nlinarith
  · have h1 := (abs_le.1 (key g (-1) h (by simp) (by rwa [neg_one_smul, ← sub_eq_add_neg]))).2
    have h2 := mul_le_mul_of_nonneg_left (hG g hg) hδ.le
    have h3 := mul_pos hδ hc₀
    nlinarith
  · refine le_max_of_le_left (le_max_of_le_right ?_)
    have h1 := key g t h ht hh
    have h2 : |Real.pi * t * δ * trF (dev L g).1 (dev L g).1| ≤ Real.pi * δ * B := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hδ]
      have := (hD2 g).2.2
      calc Real.pi * |t| * δ * |trF (dev L g).1 (dev L g).1| ≤ Real.pi * 1 * δ * B := by
            have := Real.pi_pos
            gcongr
        _ = _ := by ring
    have h3 := abs_add_le (fn L (g * infGL E a h) - fn L g - Real.pi * t * δ * trF (dev L g).1 (dev L g).1)
      (Real.pi * t * δ * trF (dev L g).1 (dev L g).1)
    rw [sub_add_cancel] at h3
    linarith
