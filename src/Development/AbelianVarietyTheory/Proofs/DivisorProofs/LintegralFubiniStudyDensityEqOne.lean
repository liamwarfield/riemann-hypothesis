module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLinePartitionContinuousCoe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurConstantsExistOnChainOfCuspRapidDecay
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfSubsetCpt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalDegreeUpperC

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralFubiniStudyDensityEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralInvPowAddNormSqComplexSpace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralComplexInvPowAddNormSqStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralComplexInvPowAddNormSq
open Set Filter Topology MeasureTheory

namespace GlobalTheory.RadialIntegral

lemma hasDerivAt_prim (m : ℕ) (a : ℝ) (ha : 0 < a) (r : ℝ) :
    HasDerivAt (fun r : ℝ => -(((a + r ^ 2) ^ (m + 1))⁻¹ / (2 * (m + 1))))
      (r * ((a + r ^ 2) ^ (m + 2))⁻¹) r := by
  have hp : 0 < a + r ^ 2 := by positivity
  have h1 : HasDerivAt (fun r : ℝ => a + r ^ 2) (2 * r) r := by
    simpa using ((hasDerivAt_pow 2 r).const_add a)
  have h2 := ((((h1.pow (m + 1)).inv (pow_ne_zero _ hp.ne')).div_const (2 * ((m : ℝ) + 1))).neg)
  refine h2.congr_deriv ?_
  simp only [Pi.pow_apply, Nat.add_sub_cancel]
  have : (m : ℝ) + 1 ≠ 0 := by positivity
  push_cast
  field_simp
  ring

lemma tendsto_prim (m : ℕ) (a : ℝ) :
    Tendsto (fun r : ℝ => -(((a + r ^ 2) ^ (m + 1))⁻¹ / (2 * (m + 1)))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun r : ℝ => a + r ^ 2) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop two_ne_zero)
  have h2 : Tendsto (fun r : ℝ => (a + r ^ 2) ^ (m + 1)) atTop atTop :=
    (tendsto_pow_atTop (Nat.succ_ne_zero m)).comp h1
  simpa using ((h2.inv_tendsto_atTop).div_const (2 * ((m : ℝ) + 1))).neg

lemma radial (m : ℕ) (a : ℝ) (ha : 0 < a) :
    ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r * ((a + r ^ 2) ^ (m + 2))⁻¹)
      = ENNReal.ofReal ((a ^ (m + 1))⁻¹ / (2 * (m + 1))) := by
  have hpos : ∀ r ∈ Ioi (0 : ℝ), 0 ≤ r * ((a + r ^ 2) ^ (m + 2))⁻¹ := fun r hr => by
    have : (0 : ℝ) < r := hr
    positivity
  have hint := integrableOn_Ioi_deriv_of_nonneg' (a := 0)
    (fun r _ => hasDerivAt_prim m a ha r) hpos (tendsto_prim m a)
  have hval := integral_Ioi_of_hasDerivAt_of_nonneg' (a := 0)
    (fun r _ => hasDerivAt_prim m a ha r) hpos (tendsto_prim m a)
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hpos)), hval]
  simp

theorem lintegral_inv_pow_add_norm_sq (m : ℕ) (a : ℝ) (ha : 0 < a) :
    ∫⁻ z : ℂ, ENNReal.ofReal (((a + ‖z‖ ^ 2) ^ (m + 2))⁻¹)
      = ENNReal.ofReal (Real.pi / ((m + 1) * a ^ (m + 1))) := by
  rw [← Complex.lintegral_comp_polarCoord_symm]
  have h : ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 •
        ENNReal.ofReal (((a + ‖Complex.polarCoord.symm p‖ ^ 2) ^ (m + 2))⁻¹)
      = ∫⁻ p in polarCoord.target,
        ENNReal.ofReal (p.1 * ((a + p.1 ^ 2) ^ (m + 2))⁻¹) * (fun _ : ℝ => (1 : ENNReal)) p.2 := by
    refine setLIntegral_congr_fun polarCoord.open_target.measurableSet (fun p hp => ?_)
    have h0 : 0 < p.1 := hp.1
    simp only [Complex.norm_polarCoord_symm, sq_abs, smul_eq_mul, mul_one]
    rw [ENNReal.ofReal_mul h0.le]
  rw [h, polarCoord_target, Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod_mul (f := fun r : ℝ => ENNReal.ofReal (r * ((a + r ^ 2) ^ (m + 2))⁻¹))
      (g := fun _ : ℝ => (1 : ENNReal)) (by fun_prop) (by fun_prop), radial m a ha]
  simp only [lintegral_const, one_mul, MeasurableSet.univ, Measure.restrict_apply, univ_inter,
    Real.volume_Ioo]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp
  ring

end GlobalTheory.RadialIntegral
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_complex_inv_pow_add_norm_sq : ∀ (m : ℕ) (a : ℝ), 0 < a → ∫⁻ z : ℂ, ENNReal.ofReal (((a + ‖z‖ ^ 2) ^ (m + 2))⁻¹) = ENNReal.ofReal (Real.pi / ((m + 1) * a ^ (m + 1))) := by
  first | exact @GlobalTheory.RadialIntegral.lintegral_inv_pow_add_norm_sq | exact GlobalTheory.RadialIntegral.lintegral_inv_pow_add_norm_sq | (intros; apply GlobalTheory.RadialIntegral.lintegral_inv_pow_add_norm_sq <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralInvPowAddNormSqComplexSpace
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
namespace GlobalTheory.ComplexSpaceIntegral

theorem lintegral_inv_pow_add_sum_norm_sq :
    ∀ (n m : ℕ) (a : ℝ), 0 < a → ∫⁻ v : Fin n → ℂ, ENNReal.ofReal (((a + ∑ i, ‖v i‖ ^ 2) ^ (n + m + 1))⁻¹)
      = ENNReal.ofReal (Real.pi ^ n * m.factorial / ((n + m).factorial * a ^ (m + 1))) := by
  intro n
  induction n with
  | zero =>
    intro m a ha
    rw [lintegral_unique]
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, zero_add, pow_zero, one_mul]
    have : (volume : Measure (Fin 0 → ℂ)) univ = 1 := by
      rw [MeasureTheory.volume_pi, Measure.pi_univ]; simp
    rw [this, mul_one]
    congr 1
    have hf : (m.factorial : ℝ) ≠ 0 := by positivity
    field_simp
  | succ n ih =>
    intro m a ha
    have e := MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℂ) 0
    rw [← (e.symm).lintegral_comp_emb (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℂ) 0).symm.measurableEmbedding]
    rw [MeasureTheory.Measure.volume_eq_prod]
    rw [lintegral_prod]
    swap
    · apply Measurable.aemeasurable
      apply ENNReal.measurable_ofReal.comp
      apply Measurable.inv
      apply Measurable.pow_const
      apply Measurable.add measurable_const
      apply Finset.measurable_sum
      intro i _
      apply Measurable.pow_const
      apply Measurable.norm
      exact (measurable_pi_apply i).comp (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℂ) 0).symm.measurable
    have inner : ∀ z : ℂ, ∫⁻ w : Fin n → ℂ, ENNReal.ofReal (((a + ∑ i, ‖(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℂ) 0).symm (z, w) i‖ ^ 2) ^ (n + 1 + m + 1))⁻¹)
        = ENNReal.ofReal (Real.pi ^ n * (m+1).factorial / (n + (m+1)).factorial) * ENNReal.ofReal (((a + ‖z‖ ^ 2) ^ (m + 2))⁻¹) := by
      intro z
      have hz : 0 < a + ‖z‖ ^ 2 := by positivity
      have key := ih (m+1) (a + ‖z‖ ^ 2) hz
      have hsum : ∀ w : Fin n → ℂ, a + ∑ i, ‖(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℂ) 0).symm (z, w) i‖ ^ 2
          = a + ‖z‖ ^ 2 + ∑ i, ‖w i‖ ^ 2 := by
        intro w
        rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.sum_univ_succ]
        simp [Fin.insertNthEquiv, add_assoc]
      simp_rw [hsum]
      have hexp : n + 1 + m + 1 = n + (m + 1) + 1 := by ring
      rw [hexp, key, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [show m + 1 + 1 = m + 2 by ring]
      have hf : ((n + (m+1)).factorial : ℝ) ≠ 0 := by positivity
      have hp : (a + ‖z‖ ^ 2) ^ (m + 2) ≠ 0 := by positivity
      field_simp
    simp_rw [inner]
    rw [lintegral_const_mul _ (by
      apply ENNReal.measurable_ofReal.comp
      apply Measurable.inv
      apply Measurable.pow_const
      exact measurable_const.add (measurable_norm.pow_const 2))]
    rw [GlobalTheory.T.lintegral_complex_inv_pow_add_norm_sq m a ha, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have h1 : ((n + (m+1)).factorial : ℝ) ≠ 0 := by positivity
    have h2 : ((n + 1 + m).factorial : ℝ) ≠ 0 := by positivity
    have h3 : (n + (m+1)) = n + 1 + m := by ring
    rw [h3, Nat.factorial_succ m]
    push_cast
    have ha' : a ^ (m+1) ≠ 0 := by positivity
    field_simp
    ring

end GlobalTheory.ComplexSpaceIntegral
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralInvPowAddNormSqComplexSpaceStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_inv_pow_add_normSq_complexSpace : ∀ (n m : ℕ) (a : ℝ), 0 < a → ∫⁻ v : Fin n → ℂ, ENNReal.ofReal (((a + ∑ i, ‖v i‖ ^ 2) ^ (n + m + 1))⁻¹) = ENNReal.ofReal (Real.pi ^ n * m.factorial / ((n + m).factorial * a ^ (m + 1))) := by
  first | exact @GlobalTheory.ComplexSpaceIntegral.lintegral_inv_pow_add_sum_norm_sq | exact GlobalTheory.ComplexSpaceIntegral.lintegral_inv_pow_add_sum_norm_sq | (intros; apply GlobalTheory.ComplexSpaceIntegral.lintegral_inv_pow_add_sum_norm_sq <;> assumption)
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory

theorem lintegral_fubiniStudy_density_eq_one : ∀ n : ℕ, ∫⁻ v : ReciprocityTheory.L2DbarEstimates.V n,
    ENNReal.ofReal (n.factorial / Real.pi ^ n * ((1 + ‖v‖ ^ 2) ^ (n + 1))⁻¹) = 1 := by
  intro n
  have hc : (0 : ℝ) ≤ n.factorial / Real.pi ^ n := by positivity
  have hmeas : Measurable fun v : ReciprocityTheory.L2DbarEstimates.V n =>
      ENNReal.ofReal (((1 + ‖v‖ ^ 2) ^ (n + 1))⁻¹) := by fun_prop
  have hsplit : ∀ v : ReciprocityTheory.L2DbarEstimates.V n,
      ENNReal.ofReal (n.factorial / Real.pi ^ n * ((1 + ‖v‖ ^ 2) ^ (n + 1))⁻¹) =
        ENNReal.ofReal (n.factorial / Real.pi ^ n) *
          ENNReal.ofReal (((1 + ‖v‖ ^ 2) ^ (n + 1))⁻¹) := fun v => ENNReal.ofReal_mul hc
  simp_rw [hsplit]
  rw [lintegral_const_mul _ hmeas]
  have hV : ∫⁻ v : ReciprocityTheory.L2DbarEstimates.V n, ENNReal.ofReal (((1 + ‖v‖ ^ 2) ^ (n + 1))⁻¹) =
      ∫⁻ z : Fin n → ℂ, ENNReal.ofReal (((1 + ∑ i, ‖z i‖ ^ 2) ^ (n + 0 + 1))⁻¹) := by
    rw [← (FinChart.measurePreserving_toV (D := n)).lintegral_comp hmeas]
    congr 1
    funext z
    rw [EuclideanSpace.norm_sq_eq]
    rfl
  rw [hV, GlobalTheory.T.lintegral_inv_pow_add_normSq_complexSpace n 0 1 one_pos, ← ENNReal.ofReal_mul hc]
  have hpi : Real.pi ^ n ≠ 0 := pow_ne_zero _ Real.pi_ne_zero
  have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  rw [show (n.factorial : ℝ) / Real.pi ^ n * (Real.pi ^ n * (Nat.factorial 0 : ℝ) /
      (((n + 0).factorial : ℝ) * 1 ^ (0 + 1))) = 1 by
    simp only [Nat.factorial_zero, Nat.cast_one, add_zero, one_pow, mul_one]
    field_simp]
  exact ENNReal.ofReal_one

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalCongruenceLevelIffLatticeStable
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalCongruenceLevelIffLatticeStable
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.TwLat.Lv

open IsDedekindDomain.HeightOneSpectrum

variable {E : Type} [Field E] [NumberField E] {w : Pl E} {K : GlobalTheory.UnitLemma.UQ}
  (e : K.E ≃+* w.adicCompletion E) {B : GlobalTheory.UnitLemma.InvAlg K} {m : ℕ} (b : Module.Basis (Fin m) K.E B.A)

def col (Z : Matrix (Fin m) (Fin m) (w.adicCompletion E)) (j : Fin m) : B.A := ∑ i, e.symm (Z i j) • b i

theorem repr_col (Z : Matrix (Fin m) (Fin m) (w.adicCompletion E)) (j i : Fin m) :
    b.repr (col e b Z j) i = e.symm (Z i j) := by
  rw [col, Module.Basis.repr_sum_self]

theorem repr_sum_smul_col (Z : Matrix (Fin m) (Fin m) (w.adicCompletion E)) (c : Fin m → K.E) (i : Fin m) :
    b.repr (∑ l, c l • col e b Z l) i = e.symm ((Z *ᵥ fun l => e (c l)) i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, repr_col,
    smul_eq_mul, Matrix.mulVec, dotProduct, map_mul, RingEquiv.symm_apply_apply]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

theorem mul_col (a : B.A) (Z : Matrix (Fin m) (Fin m) (w.adicCompletion E)) (j : Fin m) :
    a * col e b Z j = col e b (GlobalTheory.TwLat.mulMat e b a * Z) j := by
  apply b.repr.injective
  ext i
  rw [repr_col]
  have h2 := congrFun (LinearMap.toMatrix_mulVec_repr b b (LinearMap.mulLeft K.E a) (col e b Z j)) i
  simp only [LinearMap.mulLeft_apply] at h2
  rw [← h2]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, GlobalTheory.TwLat.mulMat, Matrix.mul_apply, Matrix.map_apply, repr_col, map_sum,
    map_mul, RingEquiv.symm_apply_apply]

theorem mulMat_one_add (t : K.E) (x : B.A) :
    GlobalTheory.TwLat.mulMat e b (1 + algebraMap K.E B.A t * x) = 1 + e t • GlobalTheory.TwLat.mulMat e b x := by
  ext i j
  simp only [GlobalTheory.TwLat.mulMat, Matrix.map_apply, LinearMap.toMatrix_apply, LinearMap.mulLeft_apply, add_mul, one_mul,
    mul_assoc, ← Algebra.smul_def, map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, map_mul,
    Matrix.add_apply, Matrix.smul_apply, Module.Basis.repr_self, Matrix.one_apply, Finsupp.single_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

theorem sum_smul_col_inj (g : GLw m w) (c c' : Fin m → K.E)
    (h : ∑ l, c l • col e b g.val l = ∑ l, c' l • col e b g.val l) : c = c' := by
  have h1 : g.val *ᵥ (fun l => e (c l)) = g.val *ᵥ (fun l => e (c' l)) := by
    funext i
    have := congrArg (fun x => b.repr x i) h
    simp only [repr_sum_smul_col] at this
    exact e.symm.injective this
  have h2 := congrArg (fun v => (g⁻¹).val *ᵥ v) h1
  simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at h2
  funext l
  exact e.injective (congrFun h2 l)

theorem mul_le_self_iff (a b : WithZero (Multiplicative ℤ)) (ha : a ≠ 0) : a * b ≤ a ↔ b ≤ 1 := by
  constructor
  · intro h
    have : a⁻¹ * (a * b) ≤ a⁻¹ * a := by gcongr
    rwa [← mul_assoc, inv_mul_cancel₀ ha, one_mul] at this
  · intro h
    exact mul_le_of_le_one_right' h

end GlobalTheory.TwLat.Lv

namespace GlobalTheory.TwLat.Lv

open IsDedekindDomain.HeightOneSpectrum

theorem valued_uniformizerPower_completion_eq_exp_neg {E : Type} [Field E] [NumberField E] {w : Pl E} {K : GlobalTheory.UnitLemma.UQ}
    (e : K.E ≃+* w.adicCompletion E) (hval : ∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) (t : K.O) (k : ℕ)
    (ht : t ≠ 0) (hk : GlobalTheory.UnitLemma.val K.O (algebraMap K.O K.E t) = k) :
    Valued.v (e (algebraMap K.O K.E t)) = WithZero.exp (-(k : ℤ)) := by
  have hne : e (algebraMap K.O K.E t) ≠ 0 := by
    intro h
    apply ht
    have h1 : algebraMap K.O K.E t = 0 := e.injective (h.trans (map_zero e).symm)
    exact IsFractionRing.injective K.O K.E (h1.trans (map_zero _).symm)
  have hv : Valued.v (e (algebraMap K.O K.E t)) ≠ 0 := (Valuation.ne_zero_iff _).mpr hne
  rw [hval, ordL, dite_eq_right hv] at hk
  rw [← WithZero.coe_unzero hv, WithZero.exp]
  congr 1
  rw [← ofAdd_toAdd (WithZero.unzero hv)]
  congr 1
  omega

theorem level_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A), ∀ (t : K.O) (k : ℕ), K.Small t → GlobalTheory.UnitLemma.val K.O (algebraMap K.O K.E t) = k → ∀ g N : GLw m w, N.val = GlobalTheory.TwLat.mulMat e b (1 + algebraMap K.O B.A t * B.g) → ((g⁻¹ * N * g ∈ GlobalTheory.LFun.KGL w (n := m) ∧ ∀ i j, Valued.v ((g⁻¹ * N * g).val i j - (1 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))) ↔ ∀ y ∈ GlobalTheory.TwLat.lat e b g, B.g * y ∈ GlobalTheory.TwLat.lat e b g) := by
  intro E _ _ _ _ w _ K e he hint hval B m b t k hs hk g N hN
  have hv := valued_uniformizerPower_completion_eq_exp_neg e hval t k hs.1 hk
  obtain ⟨c, hc⟩ : ∃ c, c = e (algebraMap K.O K.E t) := ⟨_, rfl⟩
  rw [← hc] at hv
  obtain ⟨Y, hY⟩ : ∃ Y : Matrix (Fin m) (Fin m) (w.adicCompletion E),
      Y = (g⁻¹).val * GlobalTheory.TwLat.mulMat e b B.g * g.val := ⟨_, rfl⟩
  have hA : (g⁻¹ * N * g).val = 1 + c • Y := by
    rw [Units.val_mul, Units.val_mul, hN, IsScalarTower.algebraMap_apply K.O K.E B.A, mulMat_one_add, ← hc, hY,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul, ← Units.val_mul,
      inv_mul_cancel, Units.val_one]
  have hent : ∀ i j, (g⁻¹ * N * g).val i j - (1 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j = c * Y i j := by
    intro i j
    rw [hA]
    simp
  have hexp : WithZero.exp (-(k : ℤ)) ≠ 0 := WithZero.exp_ne_zero
  have hcoef : (∀ i j, Valued.v ((g⁻¹ * N * g).val i j - (1 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) ≤
      WithZero.exp (-(k : ℤ))) ↔ ∀ i j, Valued.v (Y i j) ≤ 1 := by
    simp only [hent, map_mul, hv]
    exact forall_congr' fun i => forall_congr' fun j => mul_le_self_iff _ _ hexp

  have hgY : g.val * Y = GlobalTheory.TwLat.mulMat e b B.g * g.val := by
    rw [hY, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  have hgcol : ∀ j, B.g * col e b g.val j = ∑ l, e.symm (Y l j) • col e b g.val l := by
    intro j
    rw [mul_col, ← hgY]
    apply b.repr.injective
    ext i
    rw [repr_sum_smul_col, repr_col]
    simp only [RingEquiv.apply_symm_apply, Matrix.mulVec, dotProduct, Matrix.mul_apply]
  have hlat : (∀ y ∈ GlobalTheory.TwLat.lat e b g, B.g * y ∈ GlobalTheory.TwLat.lat e b g) ↔ ∀ i j, Valued.v (Y i j) ≤ 1 := by
    constructor
    · intro hst i j
      have hmem : B.g * col e b g.val j ∈ GlobalTheory.TwLat.lat e b g :=
        hst _ (Submodule.subset_span ⟨j, rfl⟩)
      obtain ⟨o, ho⟩ := (Submodule.mem_span_range_iff_exists_fun K.O).mp hmem
      have ho' : ∑ l, algebraMap K.O K.E (o l) • col e b g.val l = ∑ l, e.symm (Y l j) • col e b g.val l := by
        rw [← hgcol j, ← ho]
        exact Finset.sum_congr rfl fun l _ => algebraMap_smul K.E (o l) _
      have := congrFun (sum_smul_col_inj e b g _ _ ho') i
      have hi := (hint (algebraMap K.O K.E (o i))).mp ⟨o i, rfl⟩
      rw [this, RingEquiv.apply_symm_apply] at hi
      exact hi
    · intro hYi y hy
      have hle : GlobalTheory.TwLat.lat e b g ≤ (GlobalTheory.TwLat.lat e b g).comap (LinearMap.mulLeft K.O B.g) := by
        rw [GlobalTheory.TwLat.lat, Submodule.span_le]
        rintro _ ⟨j, rfl⟩
        show B.g * col e b g.val j ∈ GlobalTheory.TwLat.lat e b g
        rw [hgcol j]
        refine Submodule.sum_mem _ fun l _ => ?_
        obtain ⟨o, ho⟩ := (hint (e.symm (Y l j))).mpr (by rw [RingEquiv.apply_symm_apply]; exact hYi l j)
        rw [← ho, algebraMap_smul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
      exact hle hy

  have hK : (∀ i j, Valued.v (Y i j) ≤ 1) → g⁻¹ * N * g ∈ GlobalTheory.LFun.KGL w (n := m) := by
    intro hYi
    haveI : IsLocalRing (Ov E w) := inferInstanceAs (IsLocalRing (w.adicCompletionIntegers E))
    have hcS : c ∈ Ov E w := by
      show c ∈ w.adicCompletionIntegers E
      rw [mem_adicCompletionIntegers, hv]
      rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega
    let c' : Ov E w := ⟨c, hcS⟩
    let Y' : Matrix (Fin m) (Fin m) (Ov E w) := fun i j =>
      ⟨Y i j, by show Y i j ∈ w.adicCompletionIntegers E; rw [mem_adicCompletionIntegers]; exact hYi i j⟩
    let A' : Matrix (Fin m) (Fin m) (Ov E w) := 1 + c' • Y'
    have hmap : A'.map (Ov E w).subtype = (g⁻¹ * N * g).val := by
      rw [hA]
      ext i j
      simp only [A', Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
        map_add, map_mul]
      split_ifs <;> simp [c', Y']
    have hc'nu : ¬ IsUnit c' := by
      rintro ⟨u, hu⟩
      have h1 : c * ((u⁻¹ : (Ov E w)ˣ) : Ov E w) = 1 := by
        have := congrArg Subtype.val (Units.mul_inv u)
        rw [hu] at this
        exact this
      obtain ⟨o, ho⟩ := (hint (e.symm ((u⁻¹ : (Ov E w)ˣ) : Ov E w))).mpr (by
        rw [RingEquiv.apply_symm_apply]
        exact (mem_adicCompletionIntegers _ _ _).mp ((u⁻¹ : (Ov E w)ˣ) : Ov E w).2)
      have h2 : algebraMap K.O K.E (t * o) = 1 := by
        apply e.injective
        rw [map_mul, map_mul, ho, RingEquiv.apply_symm_apply, ← hc, h1, map_one]
      have h3 : t * o = 1 := IsFractionRing.injective K.O K.E (h2.trans (map_one _).symm)
      exact (IsLocalRing.mem_maximalIdeal t).mp hs.2.1 ⟨⟨t, o, h3, by rw [mul_comm]; exact h3⟩, rfl⟩
    have hres0 : IsLocalRing.residue (Ov E w) c' = 0 :=
      (IsLocalRing.residue_eq_zero_iff c').mpr ((IsLocalRing.mem_maximalIdeal c').mpr hc'nu)
    have hdet : IsUnit A'.det := by
      apply (isUnit_map_iff (IsLocalRing.residue (Ov E w)) _).mp
      rw [RingHom.map_det]
      have : (IsLocalRing.residue (Ov E w)).mapMatrix A' = 1 := by
        ext i j
        simp [A', hres0, Matrix.one_apply]
      rw [this, Matrix.det_one]
      exact isUnit_one
    have hU : IsUnit A' := (Matrix.isUnit_iff_isUnit_det A').mpr hdet
    refine ⟨hU.unit, ?_⟩
    apply Units.ext
    rw [← hmap]
    rfl
  constructor
  · rintro ⟨-, h⟩
    exact hlat.2 (hcoef.1 h)
  · intro h
    have h' := hlat.1 h
    exact ⟨hK h', hcoef.2 h'⟩

end GlobalTheory.TwLat.Lv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalCongruenceLevelIffLatticeStableStatement
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalCongruenceLevel_iff_lattice_stable : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A), ∀ (t : K.O) (k : ℕ), K.Small t → GlobalTheory.UnitLemma.val K.O (algebraMap K.O K.E t) = k → ∀ g N : GLw m w, N.val = GlobalTheory.TwLat.mulMat e b (1 + algebraMap K.O B.A t * B.g) → ((g⁻¹ * N * g ∈ GlobalTheory.LFun.KGL w (n := m) ∧ ∀ i j, Valued.v ((g⁻¹ * N * g).val i j - (1 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))) ↔ ∀ y ∈ GlobalTheory.TwLat.lat e b g, B.g * y ∈ GlobalTheory.TwLat.lat e b g) := by
  first | exact @GlobalTheory.TwLat.Lv.level_iff | exact GlobalTheory.TwLat.Lv.level_iff | (intros; apply GlobalTheory.TwLat.Lv.level_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactSetTwistedCentralizerElliptic
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedEntriesIsCompact
namespace GlobalTheory.BoundedUnitsCompact

theorem boundedEntries_isCompact {F : Type} [NontriviallyNormedField F] [ProperSpace F] {n : ℕ}
    (M : ℝ) : IsCompact {A : Matrix (Fin n) (Fin n) F | ∀ i j, ‖A i j‖ ≤ M} := by
  have h : {A : Matrix (Fin n) (Fin n) F | ∀ i j, ‖A i j‖ ≤ M} =
      Set.univ.pi (fun _ => Set.univ.pi (fun _ => Metric.closedBall (0 : F) M)) := by
    ext A
    constructor
    · intro hA i _ j _
      simpa using hA i j
    · intro hA i j
      simpa using hA i trivial j trivial
  rw [h]
  exact isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_closedBall _ _))

theorem isCompact_bounded_units {F : Type} [NontriviallyNormedField F] [IsUltrametricDist F]
    [CompleteSpace F] {n : ℕ} [ProperSpace F] (M : ℝ) :
    IsCompact {g : GL (Fin n) F | (∀ (i j : Fin n), ‖(↑g : Matrix (Fin n) (Fin n) F) i j‖ ≤ M) ∧
      ∀ (i j : Fin n), ‖(↑g⁻¹ : Matrix (Fin n) (Fin n) F) i j‖ ≤ M} := by
  have hK1 := boundedEntries_isCompact (F := F) (n := n) M
  have hK : IsCompact ({A : Matrix (Fin n) (Fin n) F | ∀ i j, ‖A i j‖ ≤ M} ×ˢ
      (MulOpposite.op '' {A : Matrix (Fin n) (Fin n) F | ∀ i j, ‖A i j‖ ≤ M})) :=
    hK1.prod (hK1.image MulOpposite.continuous_op)
  have hce := Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) F)
  convert hce.isCompact_preimage hK using 1
  ext g
  simp [Units.embedProduct, -MulOpposite.op_inv]

end GlobalTheory.BoundedUnitsCompact
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactSetTwistedCentralizerElliptic
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct Pointwise

namespace GlobalTheory.CentCpt

section Closed
variable {L : Type} [NormedField L] [IsAlgClosed L] {n : ℕ}

theorem exists_eigenbasis (y : Matrix (Fin n) (Fin n) L) (hs : y.charpoly.Separable) :
    ∃ (ι : Type) (_ : Fintype ι) (v : ι → Fin n → L) (l : ι → L), LinearIndependent L v ∧
      Fintype.card ι = n ∧ ∀ i, Module.End.HasEigenvector (Matrix.toLin' y) (l i) (v i) := by
  classical
  have hnd : y.charpoly.roots.Nodup := nodup_roots hs
  have hcard : y.charpoly.roots.toFinset.card = n := by
    rw [Multiset.toFinset_card_of_nodup hnd, splits_iff_card_roots.1 (IsAlgClosed.splits _),
      charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hev : ∀ r : y.charpoly.roots.toFinset, ∃ v : Fin n → L,
      Module.End.HasEigenvector (Matrix.toLin' y) r.1 v := fun r =>
    ((Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).2 (by
      rw [Matrix.charpoly_toLin']
      exact isRoot_of_mem_roots (Multiset.mem_toFinset.1 r.2))).exists_hasEigenvector
  choose v hv using hev
  exact ⟨_, inferInstance, v, fun r => r.1,
    Module.End.eigenvectors_linearIndependent' _ _ Subtype.val_injective v hv,
    by rw [Fintype.card_coe, hcard], hv⟩

theorem aeval_mulVec_eigen (y : Matrix (Fin n) (Fin n) L) {μ : L} {x : Fin n → L}
    (h : Module.End.HasEigenvector (Matrix.toLin' y) μ x) (q : L[X]) :
    aeval y q *ᵥ x = q.eval μ • x := by
  rw [← Module.End.aeval_apply_of_hasEigenvector h]
  have h1 := aeval_algHom_apply (toLinAlgEquiv' (R := L) (n := Fin n)).toAlgHom y q
  exact (LinearMap.congr_fun h1 x).symm

theorem exists_bound (y : Matrix (Fin n) (Fin n) L) (hs : y.charpoly.Separable) :
    ∃ M : ℝ, ∀ t : Matrix (Fin n) (Fin n) L, t * y = y * t →
      (∃ B : ℝ, ∀ k : ℕ, ∀ i j, ‖(t ^ k) i j‖ ≤ B) → ∀ i j, ‖t i j‖ ≤ M := by
  classical
  obtain ⟨ι, _, v, l, hli, hcard, hv⟩ := exists_eigenbasis y hs
  let b : Module.Basis ι L (Fin n → L) :=
    basisOfLinearIndependentOfCardEqFinrank' v hli (by rw [hcard, Module.finrank_fin_fun])
  have hb : ⇑b = v := coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _
  let c : Fin n → ι → L := fun j i => b.repr (Pi.single j 1) i
  refine ⟨∑ a, ∑ j, ∑ i, ‖c j i‖ * ‖v i a‖, fun t ht ⟨B, hB⟩ a j => ?_⟩
  obtain ⟨p, hp⟩ := GlobalTheory.BCT.ClsFin.exists_aeval_of_comm y t hs ht.symm
  have hpow : ∀ k : ℕ, ∀ i, (t ^ k) *ᵥ v i = (p.eval (l i)) ^ k • v i := by
    intro k i
    rw [hp, ← map_pow, aeval_mulVec_eigen y (hv i), eval_pow]
  have hd : ∀ i, ‖p.eval (l i)‖ ≤ 1 := by
    intro i
    obtain ⟨a0, ha0⟩ : ∃ a0, v i a0 ≠ 0 := by
      by_contra h
      push_neg at h
      exact (hv i).2 (funext h)
    have hk : ∀ k : ℕ, ‖p.eval (l i)‖ ^ k ≤ (B * ∑ j, ‖v i j‖) / ‖v i a0‖ := by
      intro k
      rw [le_div_iff₀ (norm_pos_iff.2 ha0), ← norm_pow, ← norm_mul]
      have e := congrFun (hpow k i) a0
      rw [Pi.smul_apply, smul_eq_mul] at e
      rw [← e, Matrix.mulVec, dotProduct, Finset.mul_sum]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hB k a0 j) (norm_nonneg _)
    by_contra h1
    push_neg at h1
    obtain ⟨k, hk'⟩ := ((tendsto_pow_atTop_atTop_of_one_lt h1).eventually_gt_atTop
      ((B * ∑ j, ‖v i j‖) / ‖v i a0‖)).exists
    exact absurd (hk k) (not_le.2 hk')
  have hcol : t a j = (t *ᵥ Pi.single j 1) a := by
    rw [Matrix.mulVec_single_one]; rfl
  have hexp : (Pi.single j 1 : Fin n → L) = ∑ i, c j i • v i := by
    rw [← hb]; exact (b.sum_repr _).symm
  have hval : t a j = ∑ i, c j i * (p.eval (l i) * v i a) := by
    rw [hcol, hexp, Matrix.mulVec_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := hpow 1 i
    rw [pow_one, pow_one] at this
    rw [Matrix.mulVec_smul, this, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  rw [hval]
  refine (norm_sum_le _ _).trans ?_
  have h1 : ∑ i, ‖c j i * (p.eval (l i) * v i a)‖ ≤ ∑ i, ‖c j i‖ * ‖v i a‖ := by
    refine Finset.sum_le_sum fun i _ => ?_
    rw [norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (by
      simpa using mul_le_mul_of_nonneg_right (hd i) (norm_nonneg (v i a))) (norm_nonneg _)
  refine h1.trans ?_
  have hnn : ∀ a' j', 0 ≤ ∑ i, ‖c j' i‖ * ‖v i a'‖ := fun _ _ =>
    Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  calc ∑ i, ‖c j i‖ * ‖v i a‖ ≤ ∑ j', ∑ i, ‖c j' i‖ * ‖v i a‖ :=
        Finset.single_le_sum (f := fun j' => ∑ i, ‖c j' i‖ * ‖v i a‖) (fun j' _ => hnn a j') (Finset.mem_univ j)
    _ ≤ ∑ a', ∑ j', ∑ i, ‖c j' i‖ * ‖v i a'‖ :=
        Finset.single_le_sum (f := fun a' => ∑ j', ∑ i, ‖c j' i‖ * ‖v i a'‖)
          (fun a' _ => Finset.sum_nonneg fun j' _ => hnn a' j') (Finset.mem_univ a)

end Closed
end GlobalTheory.CentCpt

namespace GlobalTheory.CentCpt

section Local
variable {F : Type} [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F] {n : ℕ}

theorem exists_bound_local (y : Matrix (Fin n) (Fin n) F) (hs : y.charpoly.Separable) :
    ∃ M : ℝ, ∀ t : Matrix (Fin n) (Fin n) F, t * y = y * t →
      (∃ B : ℝ, ∀ k : ℕ, ∀ i j, ‖(t ^ k) i j‖ ≤ B) → ∀ i j, ‖t i j‖ ≤ M := by
  letI : NormedField (AlgebraicClosure F) := spectralNorm.normedField F (AlgebraicClosure F)
  let f : F →+* AlgebraicClosure F := algebraMap F _
  have hf : ∀ x : F, ‖f x‖ = ‖x‖ := fun x => spectralNorm_extends (L := AlgebraicClosure F) x
  obtain ⟨M, hM⟩ := exists_bound (y.map f) (by rw [Matrix.charpoly_map]; exact hs.map)
  refine ⟨M, fun t ht ⟨B, hB⟩ i j => ?_⟩
  have := hM (t.map f) (by rw [← Matrix.map_mul, ht, Matrix.map_mul]) ⟨B, fun k a b => by
      rw [← Matrix.map_pow, Matrix.map_apply, hf]; exact hB k a b⟩ i j
  rwa [Matrix.map_apply, hf] at this

theorem isCompact_bdd [ProperSpace F] (M : ℝ) :
    IsCompact {g : GL (Fin n) F | (∀ i j, ‖(g : Matrix (Fin n) (Fin n) F) i j‖ ≤ M) ∧
      ∀ i j, ‖((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j‖ ≤ M} := by
  first
  | exact @_root_.GlobalTheory.BoundedUnitsCompact.isCompact_bounded_units
  | exact _root_.GlobalTheory.BoundedUnitsCompact.isCompact_bounded_units
  | (apply _root_.GlobalTheory.BoundedUnitsCompact.isCompact_bounded_units <;> assumption)
  | (intros; apply _root_.GlobalTheory.BoundedUnitsCompact.isCompact_bounded_units <;> assumption)
  | (intros; apply @_root_.GlobalTheory.BoundedUnitsCompact.isCompact_bounded_units <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.BoundedUnitsCompact.isCompact_bounded_units ..)

end Local

theorem norm_le_sum {F : Type} [NormedField F] {n : ℕ} (A : Matrix (Fin n) (Fin n) F) (i j : Fin n) :
    ‖A i j‖ ≤ ∑ a, ∑ b, ‖A a b‖ :=
  (Finset.single_le_sum (f := fun b => ‖A i b‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (f := fun a => ∑ b, ‖A a b‖) (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
      (Finset.mem_univ i))

end GlobalTheory.CentCpt

namespace GlobalTheory.CentCpt

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (y : UL n w),
    y.1.val.charpoly.Separable → ∃ Ω : Set (UL n w), IsCompact Ω ∧ ∀ t ∈ twCent (MonoidHom.id (UL n w)) y,
      IsCompact (closure (Subgroup.zpowers t : Set (UL n w))) → t ∈ Ω := by
  intro E _ _ _ _ n w y hs
  letI : NontriviallyNormedField (w.adicCompletion E) := Valued.toNontriviallyNormedField _ _
  haveI : IsUltrametricDist (w.adicCompletion E) :=
    inferInstanceAs (@IsUltrametricDist (w.adicCompletion E)
      (Valued.toNormedField (w.adicCompletion E) (WithZero (Multiplicative ℤ))).toDist)
  haveI : CompleteSpace (w.adicCompletion E) := inferInstance
  haveI : ProperSpace (w.adicCompletion E) :=
    ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace (w.adicCompletion E)
  obtain ⟨M, hM⟩ := exists_bound_local (y.1.val) hs
  refine ⟨Subtype.val ⁻¹' {g : GLw n w | (∀ i j, ‖(g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j‖ ≤ M) ∧
      ∀ i j, ‖((g⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j‖ ≤ M},
    (GlobalTheory.LocFinU.isClosed_UL n w).isClosedEmbedding_subtypeVal.isCompact_preimage (isCompact_bdd (n := n) M), ?_⟩
  have hbd : ∀ s ∈ twCent (MonoidHom.id (UL n w)) y, IsCompact (closure (Subgroup.zpowers s : Set (UL n w))) →
      ∀ i j, ‖(s.1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j‖ ≤ M := by
    intro s hs' hcs
    have hcont : Continuous fun g : UL n w =>
        ∑ a, ∑ b, ‖(g.1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) a b‖ :=
      continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
        ((Units.continuous_val.comp continuous_subtype_val).matrix_elem a b).norm
    obtain ⟨B, hB⟩ := (hcs.image hcont).bddAbove
    refine hM _ ?_ ⟨B, fun k a b => ?_⟩
    · have h1 : s * y = y * s := hs'
      have h2 := congrArg (fun g : UL n w => (g.1 : Matrix (Fin n) (Fin n) (w.adicCompletion E))) h1
      simpa using h2
    · have hk : s ^ k ∈ closure (Subgroup.zpowers s : Set (UL n w)) :=
        subset_closure (Subgroup.npow_mem_zpowers s k)
      have e : ((s ^ k).1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
          (s.1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) ^ k := by
        simp [Subgroup.coe_pow, Units.val_pow_eq_pow_val]
      rw [← e]
      exact (norm_le_sum _ a b).trans (hB ⟨_, hk, rfl⟩)
  intro t ht hc
  refine ⟨hbd t ht hc, ?_⟩
  have := hbd t⁻¹ (inv_mem ht) (by rwa [Subgroup.zpowers_inv])
  simpa using this

end GlobalTheory.CentCpt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactSetTwistedCentralizerEllipticStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compact_set_twisted_centralizer_elliptic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (y : UL n w), y.1.val.charpoly.Separable → ∃ Ω : Set (UL n w), IsCompact Ω ∧ ∀ t ∈ twCent (MonoidHom.id (UL n w)) y, IsCompact (closure (Subgroup.zpowers t : Set (UL n w))) → t ∈ Ω := by
  first | exact @GlobalTheory.CentCpt.main | exact GlobalTheory.CentCpt.main | (intros; apply GlobalTheory.CentCpt.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParabolicMatrixFamilyDiagIsUnit
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParabolicMatrixFamilyDiagIsUnit
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

set_option autoImplicit false

namespace GlobalTheory.FlagPush

theorem mul_diag_of_par {ι : Type} {m : ι → ℕ} {K : Type} [Field K] {O O' : Subring K} {S T : Mat m K}
    (hS : Par m O S) (hT : Par m O' T) (τ : ι) (i : Fin (m τ)) :
    (S * T) τ i i = S τ i i * T τ i i := by
  rw [Pi.mul_apply, Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun l _ hl => ?_) (fun h => absurd (Finset.mem_univ i) h)
  rcases lt_or_gt_of_ne hl with h | h
  · rw [(hT τ).2.2.2 l i l.isLt h, mul_zero]
  · rw [(hS τ).2.2.2 i l i.isLt h, zero_mul]

theorem diag_of_par : ∀ (ι : Type) (m : ι → ℕ) (K : Type) [Field K] (O : Subring K) (S : Mat m K), Par m O S →
    ∀ x : Root m, S x.1 x.2 x.2 ≠ 0 ∧ (S x.1 x.2 x.2)⁻¹ ∈ O ∧ S⁻¹ x.1 x.2 x.2 = (S x.1 x.2 x.2)⁻¹ ∧
      ∀ T : Mat m K, Par m ⊤ T → (S * T) x.1 x.2 x.2 = S x.1 x.2 x.2 * T x.1 x.2 x.2 := by
  intro ι m K _ O S hS x
  have hSi : Par m O S⁻¹ := hS.inv
  have h1 : S x.1 x.2 x.2 * S⁻¹ x.1 x.2 x.2 = 1 := by
    rw [← mul_diag_of_par hS hSi, Mat.mul_inv hS.det_ne]
    exact Matrix.one_apply_eq _
  have hne : S x.1 x.2 x.2 ≠ 0 := left_ne_zero_of_mul_eq_one h1
  have hinv : S⁻¹ x.1 x.2 x.2 = (S x.1 x.2 x.2)⁻¹ := eq_inv_of_mul_eq_one_right h1
  refine ⟨hne, ?_, hinv, fun T hT => mul_diag_of_par hS hT x.1 x.2⟩
  rw [← hinv]
  exact (hSi x.1).1 x.2 x.2

end GlobalTheory.FlagPush
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParabolicMatrixFamilyDiagIsUnitStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolicMatrixFamily_diag_isUnit : ∀ (ι : Type) (m : ι → ℕ) (K : Type) [Field K] (O : Subring K) (S : Mat m K), Par m O S → ∀ x : Root m, S x.1 x.2 x.2 ≠ 0 ∧ (S x.1 x.2 x.2)⁻¹ ∈ O ∧ S⁻¹ x.1 x.2 x.2 = (S x.1 x.2 x.2)⁻¹ ∧ ∀ T : Mat m K, Par m ⊤ T → (S * T) x.1 x.2 x.2 = S x.1 x.2 x.2 * T x.1 x.2 x.2 := by
  first | exact @GlobalTheory.FlagPush.diag_of_par | exact GlobalTheory.FlagPush.diag_of_par | (intros; apply GlobalTheory.FlagPush.diag_of_par <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapsCompEqOfFunctionFieldMapsAgree
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapsCompEqOfFunctionFieldMapsAgree
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem Dbl.p_comp_eq_of_isHom : ∀ (F : Type) [Field F] (X Y : Var F) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), (ratOf X).IsHom (ratOf Y) φ f → ∀ W : Dbl Y, (∀ u : X.Fn, W.α₁ (φ u) = W.α₂ (φ u)) → W.p₁ ≫ f = W.p₂ ≫ f := by
  intro F _ X Y φ f hf W hW
  haveI : IsDominant (W.Z.fromSpecStalk (genericPoint W.Z)) := ⟨by
    rw [DenseRange, dense_iff_closure_eq]
    refine Set.eq_univ_of_univ_subset ?_
    rw [← (genericPoint_spec W.Z).def]
    exact closure_mono (Set.singleton_subset_iff.2 ⟨_, Scheme.fromSpecStalk_closedPoint⟩)⟩
  haveI : IsSeparated X.str := (ratOf X).sep
  have hs : f ≫ X.str = Y.str := hf.inducedModelMorphism_comp_structureMap
  refine ext_of_isDominant_of_isSeparated X.str ?_ (W.Z.fromSpecStalk (genericPoint W.Z)) ?_
  · change (W.p₁ ≫ f) ≫ X.str = (W.p₂ ≫ f) ≫ X.str
    rw [Category.assoc, Category.assoc, hs, W.str_eq]
  · have e₁ := specMap_functionFieldMap W.p₁
    have e₂ := specMap_functionFieldMap W.p₂
    have hφ : (functionFieldMap W.p₁).comp φ.toRingHom = (functionFieldMap W.p₂).comp φ.toRingHom :=
      RingHom.ext hW
    have key : ∀ (α : Y.Fn →+* W.Z.functionField),
        Spec.map (CommRingCat.ofHom α) ≫ genericFieldPoint Y.X ≫ f =
          Spec.map (CommRingCat.ofHom (α.comp φ.toRingHom)) ≫ (ratOf X).pt := by
      intro α
      have hf' : genericFieldPoint Y.X ≫ f = spMap φ.toRingHom ≫ (ratOf X).pt := hf
      rw [hf', CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
      rfl
    change genericFieldPoint W.Z ≫ W.p₁ ≫ f = genericFieldPoint W.Z ≫ W.p₂ ≫ f
    rw [← Category.assoc, ← e₁, Category.assoc, ← Category.assoc (genericFieldPoint W.Z), ← e₂, Category.assoc,
      key, key, hφ]

end GlobalTheory.FlagPush
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapsCompEqOfFunctionFieldMapsAgreeStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maps_comp_eq_of_functionField_maps_agree : ∀ (F : Type) [Field F] (X Y : Var F) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), (ratOf X).IsHom (ratOf Y) φ f → ∀ W : Dbl Y, (∀ u : X.Fn, W.α₁ (φ u) = W.α₂ (φ u)) → W.p₁ ≫ f = W.p₂ ≫ f := by
  first | exact @GlobalTheory.FlagPush.Dbl.p_comp_eq_of_isHom | exact GlobalTheory.FlagPush.Dbl.p_comp_eq_of_isHom | (intros; apply GlobalTheory.FlagPush.Dbl.p_comp_eq_of_isHom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixElementaryShearProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixElementaryShearProperties
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem shear_self {ι : Type} {m : ι → ℕ} (τ : ι) (a b : Fin (m τ)) {R : Type} [CommRing R] (t : R) :
    shear τ a b t τ = Matrix.transvection a b t := by
  ext i j
  simp only [shear, Matrix.transvection, Matrix.add_apply, Matrix.of_apply, Sigma.mk.inj_iff, heq_eq_eq, true_and]
  rw [Matrix.single_apply]
  simp only [@eq_comm _ a i, @eq_comm _ b j]

theorem shear_ne {ι : Type} {m : ι → ℕ} (τ : ι) (a b : Fin (m τ)) {R : Type} [CommRing R] (t : R) (σ : ι)
    (h : σ ≠ τ) : shear τ a b t σ = 1 := by
  ext i j
  simp [shear, Sigma.mk.inj_iff, h]

theorem shear_props : ∀ (ι : Type) (m : ι → ℕ) (τ : ι) (a b : Fin (m τ)), a < b → ∀ (R : Type) [CommRing R] (t : R), (∀ σ, (shear τ a b t σ).det = 1) ∧ shear τ a b t * shear τ a b (-t) = 1 ∧ shear τ a b (0 : R) = 1 ∧ ∀ (S : Type) [CommRing S] (g : R →+* S), (shear τ a b t).map g = shear τ a b (g t) := by
  intro ι m τ a b hab R _ t
  have hne : a ≠ b := hab.ne
  refine ⟨fun σ => ?_, ?_, ?_, fun S _ g => ?_⟩
  · by_cases h : σ = τ
    · subst h; rw [shear_self]; exact Matrix.det_transvection_of_ne a b hne t
    · rw [shear_ne τ a b t σ h, Matrix.det_one]
  · funext σ
    rw [Pi.mul_apply, Pi.one_apply]
    by_cases h : σ = τ
    · subst h; rw [shear_self, shear_self, Matrix.transvection_mul_transvection_same (h := hne), add_neg_cancel,
        Matrix.transvection_zero]
    · rw [shear_ne τ a b _ σ h, shear_ne τ a b _ σ h, mul_one]
  · funext σ
    rw [Pi.one_apply]
    by_cases h : σ = τ
    · subst h; rw [shear_self, Matrix.transvection_zero]
    · rw [shear_ne τ a b _ σ h]
  · funext σ i j
    simp only [Mat.map, shear, Matrix.map_apply, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply]
    split_ifs <;> simp

end GlobalTheory.FlagPush
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixElementaryShearPropertiesStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockMatrixElementaryShear_properties : ∀ (ι : Type) (m : ι → ℕ) (τ : ι) (a b : Fin (m τ)), a < b → ∀ (R : Type) [CommRing R] (t : R), (∀ σ, (shear τ a b t σ).det = 1) ∧ shear τ a b t * shear τ a b (-t) = 1 ∧ shear τ a b (0 : R) = 1 ∧ ∀ (S : Type) [CommRing S] (g : R →+* S), (shear τ a b t).map g = shear τ a b (g t) := by
  first | exact @GlobalTheory.FlagPush.shear_props | exact GlobalTheory.FlagPush.shear_props | (intros; apply GlobalTheory.FlagPush.shear_props <;> assumption)
end
end
