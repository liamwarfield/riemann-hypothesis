module

public import GroundTheory.HeightsAndTheta.Heights.FubiniStudy
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHilbertDimZero
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.OfSteps

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.BergmanProjective
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights
  GroundTheory.Heights₂.Heights.CP
open scoped ComplexConjugate ENNReal ContDiff Matrix

noncomputable section

variable {N : ℕ}

namespace ProjFS

lemma analyticAt_chartVec_apply (i m : Fin (N + 1)) (z : Fin N → ℂ) :
    AnalyticAt ℂ (fun w : Fin N → ℂ => chartVec i w m) z := by
  obtain rfl | ⟨k, rfl⟩ := Fin.eq_self_or_eq_succAbove i m
  · simp only [chartVec_self]; exact analyticAt_const
  · simp only [chartVec_succAbove]
    exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) k).analyticAt z

lemma eventually_chartVec_ne {i m : Fin (N + 1)} {z : Fin N → ℂ} (h : chartVec i z m ≠ 0) :
    ∀ᶠ w in 𝓝 z, chartVec i w m ≠ 0 :=
  (analyticAt_chartVec_apply i m z).continuousAt.eventually_ne h

lemma analyticAt_transition (i j : Fin (N + 1)) {z : Fin N → ℂ} (hz : chartVec i z j ≠ 0) :
    AnalyticAt ℂ (transition i j) z := by
  have : transition (N := N) i j = fun w k => chartVec i w (j.succAbove k) / chartVec i w j := by
    funext w k; rfl
  rw [this, analyticAt_pi_iff]
  intro k
  exact (analyticAt_chartVec_apply i _ z).div (analyticAt_chartVec_apply i j z) hz

lemma chartVec_chartCoord_chartInv {m j : Fin (N + 1)} {z : Fin N → ℂ} (hz : chartVec m z j ≠ 0) :
    chartVec j (chartCoord j (chartInv m z)) = (chartVec m z j)⁻¹ • chartVec m z :=
  chartVec_transition m j hz

end ProjFS

open ProjFS

def projAtlas (N : ℕ) : FinHolAtlas N (CP N) where
  n := N + 1
  chart := chart
  cover := exists_mem_chartDomain
  holo j k := fun _z hz => analyticAt_transition j k hz.2

def projMatrix : CP N → (Fin (N + 1) → Fin (N + 1) → ℂ) :=
  Projectivization.lift
    (fun v : {v : Fin (N + 1) → ℂ // v ≠ 0} => fun i j => v.1 i * conj (v.1 j) / ((normSq2 v.1 : ℝ) : ℂ))
    (by
      rintro ⟨a, ha⟩ ⟨b, hb⟩ t rfl
      have ht : t ≠ 0 := by rintro rfl; simp at ha
      have hb2 : ((normSq2 b : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (normSq2_pos hb).ne'
      have htc : conj t ≠ 0 := (map_ne_zero _).2 ht
      funext i j
      simp only [Pi.smul_apply, smul_eq_mul, normSq2_smul, map_mul]
      rw [show ((‖t‖ ^ 2 * normSq2 b : ℝ) : ℂ) = t * conj t * ((normSq2 b : ℝ) : ℂ) by
        rw [Complex.mul_conj']; push_cast; ring]
      field_simp)

lemma continuous_projMatrix : Continuous (projMatrix (N := N)) := by
  rw [ProjTopology.continuous_iff]
  have h : projMatrix (N := N) ∘ Projectivization.mk' ℂ = fun v : {v : Fin (N + 1) → ℂ // v ≠ 0} =>
      fun i j => v.1 i * conj (v.1 j) / ((normSq2 v.1 : ℝ) : ℂ) := by
    funext v; rfl
  rw [h]
  have hn : Continuous fun v : {v : Fin (N + 1) → ℂ // v ≠ 0} => ((normSq2 v.1 : ℝ) : ℂ) := by
    unfold normSq2
    exact Complex.continuous_ofReal.comp (continuous_finsetSum _ fun m _ =>
      (continuous_norm.comp ((continuous_apply m).comp continuous_subtype_val)).pow 2)
  refine continuous_pi fun i => continuous_pi fun j => ?_
  refine Continuous.div (((continuous_apply i).comp continuous_subtype_val).mul
    (Complex.continuous_conj.comp ((continuous_apply j).comp continuous_subtype_val))) hn fun v => ?_
  exact_mod_cast (normSq2_pos v.2).ne'

lemma projMatrix_injective : Function.Injective (projMatrix (N := N)) := by
  intro x y hxy
  induction x using Projectivization.ind with
  | h v hv =>
  induction y using Projectivization.ind with
  | h w hw =>
  have e : ∀ i j, v i * conj (v j) / ((normSq2 v : ℝ) : ℂ) =
      w i * conj (w j) / ((normSq2 w : ℝ) : ℂ) := fun i j => congr_fun (congr_fun hxy i) j
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
  have hv2 : ((normSq2 v : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (normSq2_pos hv).ne'
  have hw2 : ((normSq2 w : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (normSq2_pos hw).ne'
  have hvj : conj (v j) ≠ 0 := (map_ne_zero _).2 hj
  have hwj : w j ≠ 0 := by
    intro h0
    have h1 := e j j
    rw [h0, zero_mul, zero_div, div_eq_zero_iff] at h1
    rcases h1 with h1 | h1
    · exact hj (by simpa [hvj] using h1)
    · exact hv2 h1
  have hwjc : conj (w j) ≠ 0 := (map_ne_zero _).2 hwj
  rw [Projectivization.mk_eq_mk_iff]
  refine ⟨Units.mk0 ((conj (w j) * ((normSq2 v : ℝ) : ℂ)) / (conj (v j) * ((normSq2 w : ℝ) : ℂ)))
    (div_ne_zero (mul_ne_zero hwjc hv2) (mul_ne_zero hvj hw2)), ?_⟩
  funext i
  have ei := e i j
  rw [div_eq_div_iff hv2 hw2] at ei
  simp only [Units.smul_mk0, Pi.smul_apply, smul_eq_mul]
  rw [div_mul_eq_mul_div, div_eq_iff (mul_ne_zero hvj hw2)]
  linear_combination (-1 : ℂ) * ei

instance (N : ℕ) : T2Space (CP N) :=
  T2Space.of_injective_continuous projMatrix_injective continuous_projMatrix

namespace ProjFS

def logPot (z : Fin N → ℂ) : ℝ := Real.log (1 + normSqSum z)

lemma dNormSqSum_apply (a b : Fin N → ℂ) :
    dNormSqSum a b = ∑ m, 2 * (b m * conj (a m)).re := by
  simp [dNormSqSum, Complex.inner, mul_add]

def dNCLM : (Fin N → ℂ) →L[ℝ] ((Fin N → ℂ) →L[ℝ] ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := dNormSqSum
      map_add' := fun a b => by
        ext v
        simp only [dNormSqSum_apply, ContinuousLinearMap.add_apply, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun m _ => ?_
        simp only [Pi.add_apply, map_add (f := _), mul_add, Complex.add_re]
      map_smul' := fun c a => by
        ext v
        simp only [dNormSqSum_apply, ContinuousLinearMap.smul_apply, RingHom.id_apply,
          smul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        simp only [Pi.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal]
        rw [show v m * ((c : ℂ) * conj (a m)) = (c : ℂ) * (v m * conj (a m)) by ring,
          Complex.re_ofReal_mul]
        ring }

lemma coe_dNCLM : ⇑(dNCLM (N := N)) = dNormSqSum := rfl

lemma fderiv_logPot : fderiv ℝ (logPot (N := N)) = fun y => (1 + normSqSum y)⁻¹ • dNormSqSum y := by
  funext y
  exact (((hasFDerivAt_normSqSum y).const_add 1).log (one_add_normSqSum_pos y).ne').fderiv

lemma hasFDerivAt_inv_q (z : Fin N → ℂ) :
    HasFDerivAt (fun u : Fin N → ℂ => (1 + normSqSum u)⁻¹)
      ((-((1 + normSqSum z) ^ 2)⁻¹) • dNormSqSum z) z :=
  (hasDerivAt_inv (one_add_normSqSum_pos z).ne').comp_hasFDerivAt z
    ((hasFDerivAt_normSqSum z).const_add 1)

lemma fderiv2_logPot (z a b : Fin N → ℂ) :
    fderiv ℝ (fderiv ℝ logPot) z a b = (1 + normSqSum z)⁻¹ * dNormSqSum a b -
      ((1 + normSqSum z) ^ 2)⁻¹ * dNormSqSum z a * dNormSqSum z b := by
  rw [fderiv_logPot]
  have hd : HasFDerivAt (dNormSqSum (N := N)) dNCLM z := by
    rw [← coe_dNCLM]; exact dNCLM.hasFDerivAt
  have h2 : HasFDerivAt (fun y : Fin N → ℂ => (1 + normSqSum y)⁻¹ • dNormSqSum y)
      ((1 + normSqSum z)⁻¹ • dNCLM +
        ((-((1 + normSqSum z) ^ 2)⁻¹) • dNormSqSum z).smulRight (dNormSqSum z)) z :=
    (hasFDerivAt_inv_q z).smul hd
  rw [h2.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, coe_dNCLM, smul_eq_mul]
  ring

lemma I_smul_single (i : Fin N) : Complex.I • (Pi.single i 1 : Fin N → ℂ) = Pi.single i Complex.I := by
  ext m; by_cases h : m = i
  · subst h; simp
  · simp [h]

theorem hessC_logPot (z : Fin N → ℂ) :
    hessC logPot z = (((1 + normSqSum z)⁻¹ : ℝ) : ℂ) •
      (1 - (((1 + normSqSum z)⁻¹ : ℝ) : ℂ) • Matrix.vecMulVec (star z) z) := by
  ext i j
  simp only [hessC, fderiv2_logPot, I_smul_single, dNormSqSum_single, ← inv_pow]
  generalize (1 + normSqSum z)⁻¹ = r
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.vecMulVec_apply,
    Pi.star_apply, Complex.star_def, smul_eq_mul]
  by_cases h : i = j
  · subst h
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, sq] <;> ring
  · apply Complex.ext <;> simp [h, Complex.mul_re, Complex.mul_im, sq] <;> ring

theorem hessC_logPot_eq_chernCoeff (i : Fin (N + 1)) (z : Fin N → ℂ) :
    hessC logPot z = ((2 * Real.pi : ℝ) : ℂ) • chernCoeff i z := by
  rw [hessC_logPot, chernCoeff_eq_matrix, smul_smul]
  congr 1
  have hq := one_add_normSqSum_pos z
  have hpi := Real.pi_pos
  push_cast
  field_simp

theorem levi_logPot_nonneg (z w : Fin N → ℂ) : 0 ≤ levi logPot z w := by
  have h := re_star_dot_hessC (logPot (N := N)) z (star w)
  conv_rhs at h => rw [star_star]
  rw [← h, hessC_logPot_eq_chernCoeff 0, Matrix.smul_mulVec, dotProduct_smul,
    chernCoeff_quadForm, smul_eq_mul, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hq := one_add_normSqSum_pos z
  have hpi := Real.pi_pos
  have hCS := norm_dotProduct_sq_le z (star w)
  have hS0 := normSqSum_nonneg z
  have hX : 0 ≤ ∑ j, ‖(star w) j‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  refine mul_nonneg (by positivity) (mul_nonneg (by positivity) ?_)
  rw [sub_nonneg, inv_mul_le_iff₀ hq]
  nlinarith

end ProjFS

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithRes
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M MeasureTheory
open scoped ComplexConjugate

noncomputable section

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

structure AnRes (P J : Ideal (MRing ι)) (e : ℕ) where

  homog : IsMultiHomogIdeal J

  nondeg : ¬ J ≤ P

  X : Type
  [top : TopologicalSpace X]
  [compact : CompactSpace X]
  [t2 : T2Space X]

  A : FinHolAtlas e X

  U : X → Set X
  isOpen_U : ∀ x, IsOpen (U x)
  mem_U : ∀ x, x ∈ U x

  lift : X → X → (Σ k, ι k) → ℂ
  holo : ∀ x p, A.HoloOn (U x) (fun y => lift x y p)
  mem : ∀ x, ∀ y ∈ U x, lift x y ∈ mcPts P

  compat : ∀ x x', ∀ y ∈ U x ∩ U x', SameOrbit (lift x y) (lift x' y)

  surj : ∀ z ∈ mcPts P, z ∉ mcPts J → ∃ x, SameOrbit (lift x x) z

  inj : ∀ x x', lift x x ∉ mcPts J → SameOrbit (lift x x) (lift x' x') → x = x'

  null : ∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' {x | lift x x ∈ mcPts J}) = 0

attribute [instance] AnRes.top AnRes.compact AnRes.t2

def _root_.ReciprocityTheory.ChartRestriction.G.Geo.AnLogRes.toAnRes {P J : Ideal (MRing ι)} {e : ℕ} (R : AnLogRes P J e) :
    AnRes P J e where
  homog := R.homog
  nondeg := R.nondeg
  X := R.X
  A := R.A
  U := R.U
  isOpen_U := R.isOpen_U
  mem_U := R.mem_U
  lift := R.lift
  holo := R.holo
  mem := R.mem
  compat := R.compat
  surj := R.surj
  inj := R.inj
  null := R.null

def IsSmoothVolume {e : ℕ} {X : Type*} [TopologicalSpace X] [MeasurableSpace X] (A : FinHolAtlas e X)
    (dV : Measure X) : Prop :=
  IsProbabilityMeasure dV ∧ ∀ j, ∃ ν : (Fin e → ℂ) → ℝ,
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ν (A.chart j).target ∧ (∀ y ∈ (A.chart j).target, 0 < ν y) ∧
    ∀ S : Set X, MeasurableSet S → S ⊆ (A.chart j).source →
      dV S = ∫⁻ y in (A.chart j).target ∩ (A.chart j).symm ⁻¹' S, ENNReal.ofReal (ν y)

structure HSMDatum (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] where

  x : Ix κ → Ω

  m : ConeMetric ℂ (Ix κ)

  P0 : Ideal (MRing (GlobalTheory κ))

  J : Ideal (MRing (GlobalTheory κ))

  R : AnRes (ι := GlobalTheory κ) (coordIdeal ℤ x) J D
  [meas : MeasurableSpace R.X]
  [borel : BorelSpace R.X]

  dV : Measure R.X
  one_le : 1 ≤ D
  arith : IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1)
  indep : LinearIndependent ℤ x
  smooth : IsSmoothMetric m
  conjInv : IsConjInvariant m
  normalForm_baseLattice_le_dualSpan_sup_line : P0 ≤ coordIdeal ℤ x
  semipos : IsSemipositiveRel P0 (coordIdeal ℤ x) (HermLine.ofCone m)
  vol : IsSmoothVolume R.A dV

attribute [instance] HSMDatum.meas HSMDatum.borel

variable {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

def resPt (d : HSMDatum D Ω κ) (y : d.R.X) : Ix κ → ℂ := d.R.lift y y

def pairVal (m : ConeMetric ℂ (Ix κ)) (n : ℕ) (b b' : MvPolynomial (Ix κ) ℚ) (z : Ix κ → ℂ) : ℂ :=
  eval z (map (algebraMap ℚ ℂ) b) * conj (eval z (map (algebraMap ℚ ℂ) b')) / ((m.ρ z ^ (2 * n) : ℝ) : ℂ)

def resGram (d : HSMDatum D Ω κ) (n : ℕ) {r : ℕ} (b : Fin r → MvPolynomial (Ix κ) ℚ) :
    Matrix (Fin r) (Fin r) ℝ :=
  fun k l => (1 / 2) * ((∫ y, pairVal d.m n (b k) (b l) (resPt d y) ∂d.dV).re +
    (∫ y, pairVal d.m n (b k) (b l) (conjPt (resPt d y)) ∂d.dV).re)


open Classical in
def resChi (d : HSMDatum D Ω κ) (n : ℕ) : ℝ :=
  if h : ∃ p : (Σ r : ℕ, Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis d.x n p.2 then
    -(1 / 2) * Real.log (resGram d n h.choose.2).det
  else 0

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLatticeCount
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Metric Module ZSpan

noncomputable section

section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  (La : Submodule ℤ V) {c : ℝ}

theorem LatticeCount.exists_near (B : ShortLatticeBasis La c) (x : V) :
    ∃ μ ∈ La, ‖x + μ‖ ≤ finrank ℝ V * c := by
  let e := basisOfLinearIndependentOfCardEqFinrank' B.vec B.linearIndependent (Fintype.card_fin _)
  have he : ∀ i, e i = B.vec i := fun i ↦ by simp [e]
  refine ⟨-((floor e x : Submodule.span ℤ (Set.range e)) : V), ?_, ?_⟩
  · refine La.neg_mem ?_
    have hle : Submodule.span ℤ (Set.range e) ≤ La := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [he]
      exact B.mem i
    exact hle (floor e x).2
  · rw [← sub_eq_add_neg, ← fract_apply]
    calc ‖fract e x‖ ≤ ∑ i, ‖e i‖ := norm_fract_le e x
      _ ≤ ∑ _i : Fin (finrank ℝ V), c :=
          Finset.sum_le_sum fun i _ ↦ by rw [he]; exact B.norm_le i
      _ = _ := by simp

theorem LatticeCount.encard_le (B : ShortLatticeBasis La c) (b : ℝ) (x : V) :
    {y : V | y ∈ La ∧ ‖y‖ ≤ b}.encard ≤
      {g : La | g +ᵥ x ∈ closedBall (0 : V) (b + finrank ℝ V * c)}.encard := by
  classical
  obtain ⟨μ, hμ, hxμ⟩ := LatticeCount.exists_near La B x
  refine Set.encard_le_encard_of_injOn
    (f := fun y : V ↦ if h : y ∈ La then (⟨y + μ, La.add_mem h hμ⟩ : La) else 0) ?_ ?_
  · rintro y ⟨hy, hyb⟩
    simp only [Set.mem_ofPred_eq, hy, dif_pos, mem_closedBall, dist_zero_right,
      Submodule.vadd_def, vadd_eq_add]
    calc ‖y + μ + x‖ = ‖y + (x + μ)‖ := by congr 1; abel
      _ ≤ ‖y‖ + ‖x + μ‖ := norm_add_le _ _
      _ ≤ b + finrank ℝ V * c := add_le_add hyb hxμ
  · rintro y ⟨hy, -⟩ y' ⟨hy', -⟩ h
    simp only [hy, hy', dif_pos, Subtype.mk.injEq, add_left_inj] at h
    exact h

end

theorem LatticeCount.proof : LatticeCount.Statement := by
  intro V _ _ _ _ _ La _ _ c b B hb
  set R := finrank ℝ V with hRdef
  set S := {x : V | x ∈ La ∧ ‖x‖ ≤ b}
  have hfin : S.Finite := finite_lattice_closedBall La b
  refine ⟨hfin, ?_⟩
  have hRc : 0 ≤ (R : ℝ) * c := by
    rcases Nat.eq_zero_or_pos R with h | h
    · simp [h]
    · exact mul_nonneg (Nat.cast_nonneg _) ((norm_nonneg _).trans (B.norm_le ⟨0, h⟩))
  set r := b + R * c with hrdef
  have hr : 0 ≤ r := add_nonneg hb hRc
  have : MeasurableVAdd La V := (inferInstance : MeasurableVAdd La.toAddSubgroup V)
  have : VAddInvariantMeasure La V volume :=
    (inferInstance : VAddInvariantMeasure La.toAddSubgroup V volume)
  set bz := Free.chooseBasis ℤ La
  have hF := ZLattice.isAddFundamentalDomain bz volume
  set F := fundamentalDomain (bz.ofZLatticeBasis ℝ La)
  set A := closedBall (0 : V) r
  have hA : MeasurableSet A := measurableSet_closedBall
  have hmeas : ∀ g : La, Measurable fun x : V ↦ A.indicator (1 : V → ENNReal) (g +ᵥ x) :=
    fun g ↦ (measurable_one.indicator hA).comp (measurable_const_vadd g)
  have key : ∀ x : V,
      (S.encard : ENNReal) ≤ ∑' g : La, A.indicator (1 : V → ENNReal) (g +ᵥ x) := by
    intro x
    have hind : (fun g : La ↦ A.indicator (1 : V → ENNReal) (g +ᵥ x)) =
        {g : La | g +ᵥ x ∈ A}.indicator 1 := by
      funext g
      by_cases hg : g +ᵥ x ∈ A <;> simp [hg]
    rw [hind, ← tsum_subtype]
    simp only [Pi.one_apply]
    rw [ENNReal.tsum_set_one]
    exact_mod_cast LatticeCount.encard_le La B b x
  have hFfin : volume F ≠ ⊤ := (fundamentalDomain_isBounded _).measure_lt_top.ne
  have hvol : (S.encard : ENNReal) * ENNReal.ofReal (ZLattice.covolume La) ≤ volume A := by
    calc (S.encard : ENNReal) * ENNReal.ofReal (ZLattice.covolume La)
        = (S.encard : ENNReal) * volume F := by
          rw [ZLattice.covolume_eq_measure_fundamentalDomain La volume hF,
            ofReal_measureReal hFfin]
      _ = ∫⁻ _ in F, (S.encard : ENNReal) := (setLIntegral_const F _).symm
      _ ≤ ∫⁻ x in F, ∑' g : La, A.indicator 1 (g +ᵥ x) := lintegral_mono key
      _ = ∑' g : La, ∫⁻ x in F, A.indicator 1 (g +ᵥ x) :=
          lintegral_tsum fun g ↦ (hmeas g).aemeasurable
      _ = ∫⁻ x, A.indicator 1 x := (hF.lintegral_eq_tsum'' _).symm
      _ = volume A := lintegral_indicator_one hA
  have hunit : volume (ball (0 : V) 1) =
      volume (ball (0 : EuclideanSpace ℝ (Fin R)) 1) := by
    let f := (stdOrthonormalBasis ℝ V).repr
    rw [← f.measurePreserving.measure_preimage measurableSet_ball.nullMeasurableSet,
      f.preimage_ball, map_zero]
  have hunitfin : volume (ball (0 : EuclideanSpace ℝ (Fin R)) 1) ≠ ⊤ :=
    isBounded_ball.measure_lt_top.ne
  have hball : volume A = ENNReal.ofReal (unitBallVolume R * r ^ R) := by
    rw [Measure.addHaar_closedBall volume 0 hr, hunit, unitBallVolume,
      ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hunitfin, mul_comm]
  have hS : (S.encard : ENNReal) * ENNReal.ofReal (ZLattice.covolume La) =
      ENNReal.ofReal (S.ncard * ZLattice.covolume La) := by
    rw [← hfin.cast_ncard_eq, ENat.toENNReal_coe, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  have hpos : 0 ≤ unitBallVolume R * r ^ R :=
    mul_nonneg ENNReal.toReal_nonneg (pow_nonneg hr _)
  have := (hS ▸ hvol).trans_eq hball
  exact (ENNReal.ofReal_le_ofReal_iff hpos).1 this

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PDegreePositive
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

namespace DegreePositive

variable {F : Type} [Field F] {ι₀ : Type} [Fintype ι₀]

theorem ringKrullDim_of_mem_minimalPrimes (q W : Ideal (MRing (fun _ : Unit => ι₀) F)) [q.IsPrime]
    (x : MRing (fun _ : Unit => ι₀) F) (hx : x ∉ q) (e : ℕ)
    (hdim : ringKrullDim (MRing (fun _ : Unit => ι₀) F ⧸ q) = ((e + 1 : ℕ) : WithBot ℕ∞))
    (hmin : W ∈ (q ⊔ Ideal.span {x}).minimalPrimes) :
    ringKrullDim (MRing (fun _ : Unit => ι₀) F ⧸ W) = ((e : ℕ) : WithBot ℕ∞) := by
  have hWprime : W.IsPrime := hmin.1.1
  have hIW : q ≤ W := le_sup_left.trans hmin.1.2
  have hxW : x ∈ W := (le_sup_right.trans hmin.1.2) (Ideal.mem_span_singleton_self _)
  set B := MRing (fun _ : Unit => ι₀) F ⧸ q
  have _ : Algebra.FiniteType F B :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ F q) (Ideal.Quotient.mkₐ_surjective F q)
  set W' : Ideal B := W.map (Ideal.Quotient.mk q)
  have hW'prime : W'.IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have hW'ne : W' ≠ ⊥ := by
    intro h
    apply hx
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have : Ideal.Quotient.mk q x ∈ W' := Ideal.mem_map_of_mem _ hxW
    rw [h, Ideal.mem_bot] at this
    exact this
  have hht : W'.height ≤ 1 := Ideal.map_height_le_one_of_mem_minimalPrimes hmin
  have hquot : ringKrullDim (B ⧸ W') = ringKrullDim (MRing (fun _ : Unit => ι₀) F ⧸ W) :=
    ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hIW)
  have hform := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient (k := F) W'
  have hdrop := GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_quotient_add_one_le W' hW'ne
  rw [hquot] at hform hdrop
  change ringKrullDim B = _ at hdim
  rw [hdim] at hform hdrop
  obtain ⟨y, hy⟩ : ∃ y : ℕ∞, ringKrullDim (MRing (fun _ : Unit => ι₀) F ⧸ W) = y := by
    cases h : ringKrullDim (MRing (fun _ : Unit => ι₀) F ⧸ W) with
    | bot =>
      have := ringKrullDim_nonneg_of_nontrivial (R := MRing (fun _ : Unit => ι₀) F ⧸ W)
      rw [h] at this
      exact absurd this (by simp)
    | coe y => exact ⟨y, rfl⟩
  rw [hy] at hform hdrop ⊢
  have h1 : y + 1 ≤ ((e + 1 : ℕ) : ℕ∞) := by exact_mod_cast hdrop
  have h2 : W'.height + y = ((e + 1 : ℕ) : ℕ∞) := by exact_mod_cast hform
  have hyle : y ≤ e := by
    have : y + 1 ≤ (e : ℕ∞) + 1 := by exact_mod_cast h1
    exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp this
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, (m : ℕ∞) = y := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top
    (ENat.natCast_ne_top e) hyle)
  have h3 : ((e + 1 : ℕ) : ℕ∞) ≤ 1 + m := by rw [← h2]; gcongr
  have h4 : e + 1 ≤ 1 + m := by exact_mod_cast h3
  have h5 : m ≤ e := by exact_mod_cast hyle
  have : m = e := by omega
  subst this
  rfl


omit [Fintype ι₀] in
theorem isRelevant_of_ringKrullDim (W : Ideal (MRing (fun _ : Unit => ι₀) F)) [W.IsPrime] (e : ℕ)
    (hW : ringKrullDim (MRing (fun _ : Unit => ι₀) F ⧸ W) = ((e + 1 : ℕ) : WithBot ℕ∞)) :
    IsRelevant W := by
  intro k
  by_contra h
  simp only [not_exists, not_not] at h
  have hX : ∀ v : (Σ _ : Unit, ι₀), (X v : MRing (fun _ : Unit => ι₀) F) ∈ W := by
    rintro ⟨⟨⟩, i⟩
    cases k
    exact h i
  have hsurj : Function.Surjective (algebraMap F (MRing (fun _ : Unit => ι₀) F ⧸ W)) := by
    intro z
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
    induction p using MvPolynomial.induction_on with
    | C a =>
      exact ⟨a, by rw [← MvPolynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap]⟩
    | add p r hp hr =>
      obtain ⟨a, ha⟩ := hp
      obtain ⟨b, hb⟩ := hr
      exact ⟨a + b, by rw [map_add (f := _), ha, hb, map_add (f := _)]⟩
    | mul_X p v _ =>
      refine ⟨0, ?_⟩
      rw [map_zero, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr (hX v), mul_zero]
  have hle := ringKrullDim_le_of_surjective _ hsurj
  rw [hW, ringKrullDim_eq_zero_of_field] at hle
  have : e + 1 ≤ 0 := by exact_mod_cast hle
  omega


set_option synthInstance.maxHeartbeats 400000 in
theorem hilbFn_pos (q : Ideal (MRing (fun _ : Unit => ι₀) F)) (hq : IsMultiProjPrime q) (n : ℕ) :
    0 < hilbFn q (fun _ => (n : ℤ)) := by
  obtain ⟨i, hi⟩ := hq.relevant ()
  have hqp := hq.isPrime
  obtain ⟨hfin, heq⟩ :=
    GroundTheory.Heights₂.Heights.FieldNumbers.GradedFinite.full F Unit (fun _ => ι₀) q (fun _ => n)
  have heq' : hilbFn q (fun _ => (n : ℤ)) =
      (Module.finrank F (gradedPiece q (fun _ : Unit => n)) : ℤ) := heq
  rw [heq']
  have hmem : Ideal.Quotient.mk q ((X ⟨(), i⟩ : MRing (fun _ : Unit => ι₀) F) ^ n) ∈
      gradedPiece q (fun _ : Unit => n) := by
    refine ⟨(X ⟨(), i⟩ : MRing (fun _ : Unit => ι₀) F) ^ n, ?_, rfl⟩
    change _ ∈ weightedHomogeneousSubmodule F (blockWeight (fun _ : Unit => ι₀)) (fun _ : Unit => n)
    rw [mem_weightedHomogeneousSubmodule]
    have hp := (isWeightedHomogeneous_X F (blockWeight (fun _ : Unit => ι₀)) ⟨(), i⟩).pow n
    convert hp using 1
    funext k
    cases k
    simp [blockWeight]
  have hne : Ideal.Quotient.mk q ((X ⟨(), i⟩ : MRing (fun _ : Unit => ι₀) F) ^ n) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact fun h => hi (hqp.mem_of_pow_mem n h)
  have := hfin
  have : Nontrivial (gradedPiece q (fun _ : Unit => n)) :=
    ⟨⟨⟨_, hmem⟩, 0, fun h => hne (congrArg Subtype.val h)⟩⟩
  have hpos : 0 < Module.finrank F (gradedPiece q (fun _ : Unit => n)) := Module.finrank_pos
  exact_mod_cast hpos


omit [Fintype ι₀] in
theorem le_ker_constantCoeff (q : Ideal (MRing (fun _ : Unit => ι₀) F)) (hq : IsMultiProjPrime q) :
    q ≤ RingHom.ker (constantCoeff : MRing (fun _ : Unit => ι₀) F →+* F) := by
  intro p hp
  rw [RingHom.mem_ker]
  by_contra h
  have h0 := hq.multiHomog p hp 0
  rw [weightedHomogeneousComponent_zero p (fun v => by
    obtain ⟨⟨⟩, _⟩ := v
    intro h'
    have := congrFun h' ()
    simp [blockWeight] at this)] at h0
  have hu : IsUnit (C (AddMonoidAlgebra.coeff p 0) : MRing (fun _ : Unit => ι₀) F) :=
    (isUnit_iff_ne_zero.mpr (by rwa [← constantCoeff_eq])).map C
  exact hq.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h0 hu)

theorem pos (D : ℕ) : ∀ q : Ideal (MRing (fun _ : Unit => ι₀) F), IsMultiProjPrime q →
    ringKrullDim (MRing (fun _ : Unit => ι₀) F ⧸ q) = ((D + 1 : ℕ) : WithBot ℕ∞) →
    0 < intNum F q (fun _ : Fin D => fun _ => (1 : ℤ)) := by
  induction D with
  | zero =>
    intro q hq hd
    obtain ⟨a₀, ha⟩ := HilbertDimZero.proof F Unit (fun _ => ι₀) q hq
      (by rw [Fintype.card_unit]; exact hd)
    have h := ha (fun _ => a₀) (fun _ => le_rfl)
    have e : (fun _ : Fin 0 => fun _ : Unit => (1 : ℤ)) = (![] : Fin 0 → Unit → ℤ) :=
      funext fun j => j.elim0
    rw [e, ← h]
    exact hilbFn_pos q hq a₀
  | succ D ih =>
    intro q hq hd
    have hqp : q.IsPrime := hq.isPrime
    obtain ⟨i, hX⟩ := hq.relevant ()
    set x : MRing (fun _ : Unit => ι₀) F := X ⟨(), i⟩ with hxdef
    have hx : IsMultiHomog x (blockWeight (fun _ : Unit => ι₀) ⟨(), i⟩) :=
      isWeightedHomogeneous_X F _ _
    have hlt : ringKrullDim (MRing (fun _ : Unit => ι₀) F ⧸ q) <
        ((D + 2 + Fintype.card Unit : ℕ) : WithBot ℕ∞) := by
      rw [hd, Fintype.card_unit]
      exact_mod_cast (by omega : D + 1 + 1 < D + 2 + 1)
    have hcut := CutByForm.full F Unit (fun _ => ι₀) D q hqp hq.multiHomog hlt x _ hx hX
      (fun _ : Fin D => fun _ : Unit => (1 : ℤ))
    have e1 : Matrix.vecCons (fun k => ((blockWeight (fun _ : Unit => ι₀) ⟨(), i⟩ k : ℕ) : ℤ))
        (fun _ : Fin D => fun _ : Unit => (1 : ℤ)) = fun _ : Fin (D + 1) => fun _ : Unit => (1 : ℤ) := by
      funext j k
      cases k
      refine Fin.cases ?_ (fun j => ?_) j <;> simp [blockWeight]
    rw [e1] at hcut
    rw [hcut, cycEval]
    set J := q ⊔ Ideal.span {x} with hJdef
    have hJh : IsMultiHomogIdeal J := isMultiHomogIdeal_sup_span_of_form hq.multiHomog hx

    have hterm : ∀ W, divCycle q x W ≠ 0 →
        0 < divCycle q x W ∧ 0 < intNum F W (fun _ : Fin D => fun _ : Unit => (1 : ℤ)) := by
      intro W hW
      unfold divCycle at hW ⊢
      by_cases hc : W ∈ J.minimalPrimes ∧ IsRelevant W
      · rw [dite_eq_left hc] at hW ⊢
        have hWp : W.IsPrime := hc.1.1.1
        have hWd := ringKrullDim_of_mem_minimalPrimes q W x hX (D + 1) hd hc.1
        have hWq : IsMultiProjPrime W :=
          ⟨hWp, MinimalPrimeMultiHomog.full F Unit (fun _ => ι₀) J W hJh hc.1, hc.2⟩
        exact ⟨lt_of_le_of_ne (by positivity) (Ne.symm hW), ih W hWq hWd⟩
      · rw [dite_eq_right hc] at hW
        exact absurd rfl hW
    have hfin := DivCycleFiniteSupport.full F Unit (fun _ => ι₀) q x
    rw [finsum_eq_sum_of_support_subset _
      ((Function.support_mul_subset_left _ _).trans hfin.coe_toFinset.symm.subset)]
    refine Finset.sum_pos' (fun W _ => ?_) ?_
    · by_cases hW : divCycle q x W = 0
      · rw [hW, zero_mul]
      · exact (mul_pos (hterm W hW).1 (hterm W hW).2).le

    have hJm : J ≤ RingHom.ker (constantCoeff : MRing (fun _ : Unit => ι₀) F →+* F) := by
      refine sup_le (le_ker_constantCoeff q hq) ?_
      rw [Ideal.span_le, Set.singleton_subset_iff]
      change constantCoeff x = 0
      rw [hxdef, constantCoeff_X]
    have hmax : (RingHom.ker (constantCoeff : MRing (fun _ : Unit => ι₀) F →+* F)).IsPrime :=
      (RingHom.ker_isMaximal_of_surjective _ fun a => ⟨C a, by simp⟩).isPrime
    obtain ⟨W, hmin, -⟩ := Ideal.exists_minimalPrimes_le hJm
    have hWp : W.IsPrime := hmin.1.1
    have hWd := ringKrullDim_of_mem_minimalPrimes q W x hX (D + 1) hd hmin
    have hrel := isRelevant_of_ringKrullDim W D hWd
    have hne : divCycle q x W ≠ 0 := by
      unfold divCycle
      rw [dite_eq_left ⟨hmin, hrel⟩]
      have htop := length_localizedQuot_ne_top J W hmin
      have hzero : multAt J W ≠ 0 := by
        unfold multAt
        rw [Ne, Module.length_eq_zero_iff, LocalizedModule.subsingleton_iff]
        intro hs
        obtain ⟨r, hr, hr1⟩ := hs (1 : MRing (fun _ : Unit => ι₀) F ⧸ J)
        rw [Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem] at hr1
        exact hr (hmin.1.2 hr1)
      have : (multAt J W).toNat ≠ 0 := by
        rw [Ne, ENat.toNat_eq_zero]
        exact not_or.mpr ⟨hzero, htop⟩
      exact_mod_cast this
    refine ⟨W, hfin.mem_toFinset.mpr hne, mul_pos (hterm W hne).1 (hterm W hne).2⟩

end DegreePositive

theorem DegreePositive.proof : DegreePositive.Statement := by
  intro F _ ι₀ _ q D hq hd
  exact DegreePositive.pos D q hq hd

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
