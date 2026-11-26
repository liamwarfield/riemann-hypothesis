module

public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemOfForallRingEquivFixed
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFiniteMeasureQuotMeasure

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.PoissonCutoffAlgebra
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace PoissonCutoffAlgebra

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {k : ℕ}

theorem exists_pl : Nonempty (Pl E) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 E)
  exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField E)⟩⟩

theorem psi_nontriv {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) : ∃ a : Ad E, ψ a ≠ 1 := by
  obtain ⟨w⟩ := exists_pl (E := E)
  obtain ⟨y, hy⟩ := hψ.loc w
  exact ⟨_, hy⟩

theorem alg_inj {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) : Function.Injective (algebraMap E (Ad E)) := by
  obtain ⟨a, ha⟩ := psi_nontriv hψ
  haveI : Nontrivial (Ad E) := ⟨⟨a, 0, fun h => ha (by rw [h, AddChar.map_zero_eq_one])⟩⟩
  exact (algebraMap E (Ad E)).injective

noncomputable def eL (hi : Function.Injective (algebraMap E (Ad E))) : (Fin k → E) ≃ vecLattice E (Fin k) :=
  Equiv.ofBijective (fun ξ => ⟨fun i => algebraMap E (Ad E) (ξ i), ξ, rfl⟩)
    ⟨fun a b h => funext fun i => hi (congrFun (congrArg Subtype.val h) i),
     fun γ => by obtain ⟨ξ, hξ⟩ := γ.2; exact ⟨ξ, Subtype.ext hξ⟩⟩

theorem eL_val (hi : Function.Injective (algebraMap E (Ad E))) (ξ : Fin k → E) :
    ((eL hi ξ : vecLattice E (Fin k)) : Fin k → Ad E) = fun i => algebraMap E (Ad E) (ξ i) := rfl

def B (ψ : AddChar (Ad E) ℂ) (x y : Fin k → Ad E) : ℂ := ψ (∑ i, x i * y i)

theorem B_cont {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) (y : Fin k → Ad E) : Continuous fun x => B ψ x y :=
  hψ.cont.comp (continuous_finsetSum _ fun i _ => (continuous_apply i).mul continuous_const)

theorem B_symm (ψ : AddChar (Ad E) ℂ) (x y : Fin k → Ad E) : B ψ x y = B ψ y x := by
  simp only [B, mul_comm]

theorem B_add (ψ : AddChar (Ad E) ℂ) (x x' y : Fin k → Ad E) : B ψ (x + x') y = B ψ x y * B ψ x' y := by
  simp only [B, ← AddChar.map_add_eq_mul, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem B_ker {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) (x : Fin k → Ad E) :
    (∀ γ ∈ vecLattice E (Fin k), B ψ γ x = 1) ↔ x ∈ vecLattice E (Fin k) := by
  classical
  constructor
  · intro h
    have : ∀ i, ∃ d : E, x i = algebraMap E (Ad E) d := by
      intro i
      refine hψ.ann (x i) fun c => ?_
      have := h (fun j => algebraMap E (Ad E) ((Pi.single i c : Fin k → E) j)) (algebraMap_mem_vecLattice _)
      have e : (∑ j, (fun j => algebraMap E (Ad E) ((Pi.single i c : Fin k → E) j)) j * x j) =
          x i * algebraMap E (Ad E) c := by
        rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_apply, hj])
          (fun h => absurd (Finset.mem_univ i) h)]
        simp [mul_comm]
      simp only [B] at this
      rwa [e] at this
    choose d hd using this
    exact ⟨d, funext fun i => (hd i).symm⟩
  · rintro ⟨d, rfl⟩ γ ⟨ξ, rfl⟩
    have : (∑ i, (fun i => algebraMap E (Ad E) (ξ i)) i * (fun i => algebraMap E (Ad E) (d i)) i) =
        algebraMap E (Ad E) (∑ i, ξ i * d i) := by simp [map_sum, map_mul]
    simp only [B]
    exact this ▸ hψ.rat _

theorem B_inj {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) (γ : Fin k → Ad E) (hγ : γ ∈ vecLattice E (Fin k))
    (h : ∀ x, B ψ γ x = 1) : γ = 0 := by
  classical
  obtain ⟨ξ, hξ⟩ := hγ
  have hξ' : γ = fun i => algebraMap E (Ad E) (ξ i) := hξ.symm
  subst hξ'
  by_contra hne
  have : ∃ i, ξ i ≠ 0 := by
    by_contra h0
    push_neg at h0
    exact hne (funext fun i => by simp [h0 i])
  obtain ⟨i, hi⟩ := this
  obtain ⟨a, ha⟩ := psi_nontriv hψ
  apply ha
  have := h (Pi.single i (algebraMap E (Ad E) (ξ i)⁻¹ * a) : Fin k → Ad E)
  have e : (∑ j, (fun j => algebraMap E (Ad E) (ξ j)) j * (Pi.single i (algebraMap E (Ad E) (ξ i)⁻¹ * a) : Fin k → Ad E) j) = a := by
    simp only [Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hi, map_one, one_mul]
  simp only [B] at this
  rwa [e] at this

noncomputable def T (g : GA E k) : (Fin k → Ad E) ≃ₜ (Fin k → Ad E) where
  toFun x := x ᵥ* g.val
  invFun x := x ᵥ* g⁻¹.val
  left_inv x := by simp [Matrix.vecMul_vecMul]
  right_inv x := by simp [Matrix.vecMul_vecMul]
  continuous_toFun := Continuous.matrix_vecMul continuous_id continuous_const
  continuous_invFun := Continuous.matrix_vecMul continuous_id continuous_const

theorem cov (hD : D0) (hM : AdelicLinearChange) (g : GA E k) (h : (Fin k → Ad E) → ℂ) :
    ∫ x, h (x ᵥ* g.val) ∂vecMeasure E (Fin k) = ((Dt g)⁻¹ : ℝ) • ∫ y, h y ∂vecMeasure E (Fin k) := by
  have hpos : 0 < Dt g := (hD E k).1 g
  have hmap : Measure.map (T g) (vecMeasure E (Fin k)) = ENNReal.ofReal (Dt g)⁻¹ • vecMeasure E (Fin k) := by
    ext A hA
    rw [Measure.smul_apply, smul_eq_mul, ← lintegral_indicator_one hA, ← lintegral_indicator_one hA,
      lintegral_map (measurable_one.indicator hA) (T g).continuous.measurable]
    exact (hM E k g (A.indicator 1) (measurable_one.indicator hA)).2
  have := integral_map_equiv (T g).toMeasurableEquiv h (μ := vecMeasure E (Fin k))
  rw [Homeomorph.toMeasurableEquiv_coe, hmap, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.2 hpos.le)] at this
  exact this.symm

def eR : RowT E k k ≃ {ξ : Fin k → E // ξ ≠ 0} where
  toFun ξ := ⟨ξ.1, ξ.2.1⟩
  invFun ξ := ⟨ξ.1, ξ.2, fun i hi => absurd hi (not_le.2 i.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

def Ps (η : (Fin k → Ad E) → ℝ) (s : (Fin k → Ad E) → GA E k) (φ : XB E k) (g : GA E k) (y : Fin k → Ad E) : ℂ :=
  (η y : ℂ) * φ (g * (s y)⁻¹)

def Jf (ψ : AddChar (Ad E) ℂ) (η : (Fin k → Ad E) → ℝ) (s : (Fin k → Ad E) → GA E k) (φ : XB E k) (g : GA E k)
    (ξ : Fin k → E) : ℂ :=
  ∫ y, (η y : ℂ) * φ (g * (s y)⁻¹) * ψ (∑ i, y i * ((fun i => algebraMap E (Ad E) (ξ i)) ᵥ* (invT g).val) i)
    ∂vecMeasure E (Fin k)

theorem alg_zero : (fun i => algebraMap E (Ad E) ((0 : Fin k → E) i)) = 0 := by
  ext i; simp

theorem stepA (hD : D0) (hM : AdelicLinearChange) (ψ : AddChar (Ad E) ℂ) (η : (Fin k → Ad E) → ℝ) (s : (Fin k → Ad E) → GA E k)
    (φ : XB E k) (g : GA E k) (ξ : Fin k → E) :
    ∫ x, Ps η s φ g (x ᵥ* g.val) * B ψ x (fun i => algebraMap E (Ad E) (ξ i)) ∂vecMeasure E (Fin k) =
      ((Dt g)⁻¹ : ℝ) • Jf ψ η s φ g ξ := by
  have e := cov hD hM g (fun y => (η y : ℂ) * φ (g * (s y)⁻¹) *
    ψ (∑ i, y i * ((fun i => algebraMap E (Ad E) (ξ i)) ᵥ* (invT g).val) i))
  refine Eq.trans ?_ e
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [Ps, B]
  congr 2
  change x ⬝ᵥ _ = (x ᵥ* g.val) ⬝ᵥ (_ ᵥ* (g⁻¹.val)ᵀ)
  rw [Matrix.vecMul_transpose, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
  simp

end PoissonCutoffAlgebra

open PoissonCutoffAlgebra in
theorem poisson_cutoff_of : D0 → AdelicLinearChange → N0 → H0 → ThetaSeriesBound → K1 → PoissonCutoffFormula := by
  intro hD hM hN _hH hG hK E _ _ _ k hk ψ hψ S U φ η s hcut hinv g
  classical
  have hi := alg_inj hψ
  have hDpos : ∀ h : GA E k, 0 < Dt h := (hD E k).1
  have hΨc : Continuous (Ps η s φ g) := by
    have := (continuous_eval_const g).comp hcut.contV
    refine this.congr fun y => ?_
    simp [Rt_apply, Ps]
  have hΨs : HasCompactSupport (Ps η s φ g) := by
    have : HasCompactSupport fun y => (η y : ℂ) := hcut.cpt.comp_left Complex.ofReal_zero
    exact this.mul_right
  have hΨ0 : Ps η s φ g 0 = 0 := by simp [Ps, hcut.zero]
  have hfc : Continuous fun x : Fin k → Ad E => Ps η s φ g (x ᵥ* g.val) := hΨc.comp (T g).continuous
  have hfs : HasCompactSupport fun x : Fin k → Ad E => Ps η s φ g (x ᵥ* g.val) := hΨs.comp_homeomorph (T g)

  obtain ⟨Cf, hCf, hft⟩ := hcut.ft
  obtain ⟨M, C0, hG3⟩ := hG E k Cf hCf k le_rfl
  obtain ⟨C, hC⟩ := hft M
  obtain ⟨-, hdpos, hdle, -⟩ := hK E k hk
  have hp : 0 < Dt (invT g) ^ ((k : ℝ)⁻¹) := Real.rpow_pos_of_pos (hDpos _) _
  have hr : 0 < dmin (invT g) * Dt (invT g) ^ ((k : ℝ)⁻¹) := mul_pos (hdpos _) hp
  have hrle : ∀ ξ : Fin k → E, ξ ≠ 0 → dmin (invT g) * Dt (invT g) ^ ((k : ℝ)⁻¹) ≤ height (invT g) ξ := by
    intro ξ hξ
    have := hdle (invT g) ξ hξ
    rwa [ht, le_div_iff₀ hp] at this
  have hsumG := hG3 (invT g) _ hr hrle
  have hu0 : ∀ ξ : Fin k → E, 0 ≤ Cf.indicator (fun _ => ((1 + ‖fun i => pInf E
      (((fun i => algebraMap E (Ad E) (ξ i)) ᵥ* (invT g).val) i)‖) ^ M)⁻¹)
      (fun i => pFin E (((fun i => algebraMap E (Ad E) (ξ i)) ᵥ* (invT g).val) i)) := fun ξ =>
    Set.indicator_nonneg (fun _ _ => inv_nonneg.2 (pow_nonneg (by positivity) _)) _
  have hus : Summable fun ξ : Fin k → E => Cf.indicator (fun _ => ((1 + ‖fun i => pInf E
      (((fun i => algebraMap E (Ad E) (ξ i)) ᵥ* (invT g).val) i)‖) ^ M)⁻¹)
      (fun i => pFin E (((fun i => algebraMap E (Ad E) (ξ i)) ᵥ* (invT g).val) i)) := by
    have hne := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsumG
    have h1 := (ENNReal.summable_toReal hne).congr fun ξ => ENNReal.toReal_ofReal (hu0 ξ.1)
    exact (Set.finite_singleton (0 : Fin k → E)).summable_compl_iff.1 h1
  have hJs : Summable fun ξ => ‖Jf ψ η s φ g ξ‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ξ => (hC _ g).trans (le_of_eq ?_)) (hus.mul_left C)
    by_cases hx : (fun i => pFin E (((fun i => algebraMap E (Ad E) (ξ i)) ᵥ* (invT g).val) i)) ∈ Cf <;> simp [hx]
  have hsumΓ : Summable fun γ : vecLattice E (Fin k) =>
      ‖∫ x, Ps η s φ g (x ᵥ* g.val) * B ψ x γ ∂vecMeasure E (Fin k)‖ := by
    refine (eL hi).summable_iff.1 ((hJs.mul_left (Dt g)⁻¹).congr fun ξ => ?_)
    rw [Function.comp_apply, eL_val, stepA hD hM, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (hDpos g))]

  obtain ⟨hdisc, K, hK, hcov⟩ := isCoLat_ratV E (Fin k)
  haveI : DiscreteTopology (vecLattice E (Fin k)) := hdisc
  have hP := GlobalTheory.CovolumeOneSelfDual.poisson (vecLattice E (Fin k)) K hK hcov (B ψ) (B_cont hψ) (B_symm ψ)
    (B_add ψ) (fun x y => hψ.norm _) (B_ker hψ) (fun γ hγ h => B_inj hψ γ hγ h) (vecMeasure E (Fin k))
    (vecDomain E (Fin k)) isAddFundamentalDomain_vecDomain vecMeasure_vecDomain hfc hfs hsumΓ
  obtain ⟨-, -, -, -, -, -, -, -, -, hlast⟩ := hN E k k hk le_rfl
  have hL : sumF (fun h => (η (lastRow h) : ℂ) * φ (h * (s (lastRow h))⁻¹)) g =
      ∑' ξ : Fin k → E, Ps η s φ g ((fun i => algebraMap E (Ad E) (ξ i)) ᵥ* g.val) := by
    unfold sumF
    rw [← (eR (E := E) (k := k)).symm.tsum_eq]
    rw [← tsum_subtype_eq_of_support_subset (s := {ξ : Fin k → E | ξ ≠ 0})]
    · refine tsum_congr fun ξ => ?_
      beta_reduce
      rw [hlast, mul_assoc, hinv (gam (eR.symm ξ))]
      rfl
    · intro ξ hξ
      simp only [Set.mem_setOf_eq]
      rintro rfl
      apply hξ
      simp only [alg_zero, Matrix.zero_vecMul, hΨ0]
  have hR : ∑' ξ : Fin k → E, Ps η s φ g ((fun i => algebraMap E (Ad E) (ξ i)) ᵥ* g.val) =
      ∑' ξ : Fin k → E, ((Dt g)⁻¹ : ℝ) • Jf ψ η s φ g ξ := by
    have h1 := (eL hi).tsum_eq fun γ : vecLattice E (Fin k) => Ps η s φ g ((γ : Fin k → Ad E) ᵥ* g.val)
    have h2 := (eL hi).tsum_eq fun γ : vecLattice E (Fin k) =>
      ∫ x, Ps η s φ g (x ᵥ* g.val) * B ψ x γ ∂vecMeasure E (Fin k)
    simp only [eL_val] at h1 h2
    rw [h1, hP, ← h2]
    exact tsum_congr fun ξ => stepA hD hM ψ η s φ g ξ
  have hJsum : Summable (Jf ψ η s φ g) := hJs.of_norm
  have hJ0 : Jf ψ η s φ g 0 = ∫ y, (η y : ℂ) * φ (g * (s y)⁻¹) ∂vecMeasure E (Fin k) := by
    rw [Jf, alg_zero]
    simp
  rw [hL, hR]
  simp only [Complex.real_smul, tsum_mul_left, Complex.ofReal_inv]
  rw [mul_inv_cancel_left₀ (Complex.ofReal_ne_zero.2 (hDpos g).ne'),
    ← hJsum.tsum_subtype_add_tsum_subtype_compl {0}, tsum_singleton, hJ0]
  rfl

end PositivityTheory.AdelicQuotientData

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.FundamentalDomainCentre
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [local instance] GlobalTheory.CuspRep.CuspidalL2GL.discreteTopology_latticeGL

namespace PositivityTheory.AdelicQuotientData

namespace FundamentalDomainCentre

set_option synthInstance.maxHeartbeats 400000

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {k : ℕ}

abbrev fdL (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (k : ℕ) : Set (GA E k) :=
  GlobalTheory.AutomorphicL2Unitary.stdDom (latticeGL E k)

abbrev rhoZ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (k : ℕ) : Measure (GA E k) :=
  Measure.sum fun n : ℤ => Measure.dirac (splitCentre E k 1 ^ (-n))

instance rhoZ_sFinite : SFinite (rhoZ E k) := by
  unfold rhoZ
  infer_instance

theorem lint_rhoZ (F : GA E k → ℝ≥0∞) : ∫⁻ r, F r ∂rhoZ E k = ∑' n : ℤ, F (splitCentre E k 1 ^ (-n)) := by
  first
  | (rw [rhoZ, lintegral_sum_measure]; simp only [lintegral_dirac])
  | simp only [rhoZ, lintegral_sum_measure, lintegral_dirac]

theorem degree_rank_pos (hk : 1 ≤ k) : (0 : ℝ) < (k : ℝ) * (Module.finrank ℚ E : ℝ) := by
  have h1 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have h2 : (0 : ℝ) < Module.finrank ℚ E := by
    have : 0 < Module.finrank ℚ E := by
      first
      | exact Module.finrank_pos
      | exact Module.finrank_pos (R := ℚ) (M := E)
      | exact FiniteDimensional.finrank_pos
    exact_mod_cast this
  exact mul_pos h1 h2

theorem dt_one (hD : D0) : Dt (1 : GA E k) = 1 := by
  obtain ⟨hpos, hmul, -⟩ := hD E k
  have h := hmul 1 1
  rw [mul_one (1 : GA E k)] at h
  have hp := hpos 1
  have h' : Dt (1 : GA E k) * Dt (1 : GA E k) = Dt (1 : GA E k) * 1 := by rw [mul_one]; exact h.symm
  exact mul_left_cancel₀ hp.ne' h'

theorem dt_split_centre_zpow (hD : D0) (n : ℤ) :
    Dt (splitCentre E k 1 ^ n) = Real.exp ((k : ℝ) * (Module.finrank ℚ E : ℝ) * (n : ℝ)) := by
  rw [← GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_intCast]
  exact (hD E k).2.2.2.2.2.2.1 n

theorem split_centre_commute (n : ℤ) (g : GA E k) : splitCentre E k 1 ^ n * g = g * splitCentre E k 1 ^ n := by
  rw [← GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_intCast]
  exact GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm _ _

theorem adeles_nontrivial (hD : D0) (hk : 1 ≤ k) : Nontrivial (Ad E) := by
  refine ⟨⟨0, 1, fun h01 => ?_⟩⟩
  haveI : Subsingleton (Ad E) := subsingleton_of_zero_eq_one h01
  have h1 : splitCentre E k 1 = 1 := by
    first
    | exact Units.ext (Matrix.ext fun i j => Subsingleton.elim _ _)
    | exact Subsingleton.elim _ _
  have h2 : Dt (splitCentre E k 1) = Real.exp ((k : ℝ) * (Module.finrank ℚ E : ℝ) * 1) :=
    (hD E k).2.2.2.2.2.2.1 1
  rw [h1, dt_one (E := E) (k := k) hD] at h2
  have h3 := Real.exp_lt_exp.2
    (show (0 : ℝ) < (k : ℝ) * (Module.finrank ℚ E : ℝ) * 1 by rw [mul_one]; exact degree_rank_pos (E := E) hk)
  rw [Real.exp_zero] at h3
  linarith

theorem rational_GL_injective (hD : D0) (hk : 1 ≤ k) : Function.Injective (ratGL E k) := by
  haveI := adeles_nontrivial (E := E) hD hk
  intro γ γ' h
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h1 : (ratGL E k γ : Matrix (Fin k) (Fin k) (Ad E)) i j =
      (ratGL E k γ' : Matrix (Fin k) (Fin k) (Ad E)) i j := by rw [h]
  first
  | exact (algebraMap E (Ad E)).injective h1
  | exact RingHom.injective _ h1
  | (simp [ratGL] at h1; exact h1)

theorem rational_centre_injective (hD : D0) (hk : 1 ≤ k) {γ γ' : GL (Fin k) E} {n n' : ℤ}
    (h : ratGL E k γ * splitCentre E k 1 ^ n = ratGL E k γ' * splitCentre E k 1 ^ n') : γ = γ' ∧ n = n' := by
  obtain ⟨-, hmul, -, hrat, -⟩ := hD E k
  have h1 := congrArg Dt h
  rw [hmul, hmul, hrat, hrat, one_mul, one_mul, dt_split_centre_zpow (E := E) (k := k) hD,
    dt_split_centre_zpow (E := E) (k := k) hD] at h1
  have h2 : ((n : ℤ) : ℝ) = ((n' : ℤ) : ℝ) :=
    mul_left_cancel₀ (degree_rank_pos (E := E) hk).ne' (Real.exp_injective h1)
  have hn : n = n' := by exact_mod_cast h2
  subst hn
  exact ⟨rational_GL_injective hD hk (mul_right_cancel h), rfl⟩

theorem fundamental_domain_tsum (hD : D0) (hk : 1 ≤ k) (g : GA E k) :
    ∑' p : GL (Fin k) E × ℤ, (fdL E k).indicator (1 : GA E k → ℝ≥0∞)
      (ratGL E k p.1 * splitCentre E k 1 ^ p.2 * g) = 1 := by
  obtain ⟨⟨x, hx⟩, hxg, huniq⟩ := GlobalTheory.AutomorphicL2Unitary.existsUnique_stdDom (latticeGL E k) g
  obtain ⟨γ, n, rfl⟩ := GlobalTheory.CuspRep.CuspidalL2GL.mem_latticeGL_iff.1 hx
  have hmem : ratGL E k γ * splitCentre E k 1 ^ n * g ∈ fdL E k := hxg
  rw [tsum_eq_single (γ, n)]
  · exact Set.indicator_of_mem hmem _
  · rintro ⟨γ', n'⟩ hne
    have hnm : ratGL E k γ' * splitCentre E k 1 ^ n' * g ∉ fdL E k := by
      intro hm'
      have hm : ratGL E k γ' * splitCentre E k 1 ^ n' ∈ latticeGL E k :=
        GlobalTheory.CuspRep.CuspidalL2GL.mem_latticeGL_iff.2 ⟨γ', n', rfl⟩
      obtain ⟨e1, e2⟩ := rational_centre_injective hD hk (congrArg Subtype.val (huniq ⟨_, hm⟩ hm'))
      exact hne (by rw [e1, e2])
    first
    | exact Set.indicator_of_notMem hnm _
    | exact Set.indicator_of_not_mem hnm _

theorem exp_band_iff_floor {c L : ℝ} (hc : 0 < c) (n : ℤ) :
    (1 ≤ Real.exp (c * ((-n : ℤ) : ℝ)) * Real.exp L ∧
      Real.exp (c * ((-n : ℤ) : ℝ)) * Real.exp L < Real.exp (c * 1)) ↔ n = ⌊L / c⌋ := by
  constructor
  · rintro ⟨h1, h2⟩
    rw [← Real.exp_add, Real.one_le_exp_iff] at h1
    rw [← Real.exp_add, Real.exp_lt_exp] at h2
    rw [eq_comm, Int.floor_eq_iff, le_div_iff₀ hc, div_lt_iff₀ hc]
    push_cast at h1 h2
    constructor
    · first | linarith | nlinarith
    · first | linarith | nlinarith
  · intro h
    rw [eq_comm, Int.floor_eq_iff, le_div_iff₀ hc, div_lt_iff₀ hc] at h
    obtain ⟨h1, h2⟩ := h
    rw [← Real.exp_add, Real.one_le_exp_iff, Real.exp_lt_exp]
    push_cast
    constructor
    · first | linarith | nlinarith
    · first | linarith | nlinarith

theorem split_centre_band_iff (hD : D0) (hk : 1 ≤ k) (n : ℤ) (g : GA E k) :
    splitCentre E k 1 ^ (-n) * g ∈ band E k ↔
      n = ⌊Real.log (Dt g) / ((k : ℝ) * (Module.finrank ℚ E : ℝ))⌋ := by
  obtain ⟨hpos, hmul, -⟩ := hD E k
  have e2 : Dt (splitCentre E k 1) = Real.exp ((k : ℝ) * (Module.finrank ℚ E : ℝ) * 1) :=
    (hD E k).2.2.2.2.2.2.1 1
  show (1 ≤ Dt (splitCentre E k 1 ^ (-n) * g) ∧ Dt (splitCentre E k 1 ^ (-n) * g) < Dt (splitCentre E k 1)) ↔ _
  rw [hmul, dt_split_centre_zpow (E := E) (k := k) hD, e2]
  have h := exp_band_iff_floor (degree_rank_pos (E := E) hk) n (L := Real.log (Dt g))
  rw [Real.exp_log (hpos g)] at h
  exact h

end FundamentalDomainCentre

set_option synthInstance.maxHeartbeats 400000 in
theorem fundamental_domain_of : Q1 → D0 → N3 → W0 := by
  intro hQ1 hD hN3 E _ _ _ k μ _ hk
  obtain ⟨hpos, hmul, hcont, hrat, huu, -⟩ := hD E k
  obtain ⟨hsf, hinv, hae⟩ := (hN3 E k).2.1 k le_rfl
  have hlint := (hN3 E k).2.2.1
  have hF : MeasurableSet (FundamentalDomainCentre.fdL E k) := GlobalTheory.AutomorphicL2Unitary.measurableSet_stdDom (latticeGL E k)
  have hβ₁ : Measurable ((FundamentalDomainCentre.fdL E k).indicator (1 : GA E k → ℝ≥0∞)) := by
    first | exact measurable_one.indicator hF | exact measurable_const.indicator hF
  refine ⟨⟨fun g => ∑' n : ℤ, (FundamentalDomainCentre.fdL E k).indicator (1 : GA E k → ℝ≥0∞) (splitCentre E k 1 ^ n * g),
    Measurable.tsum fun n => hβ₁.comp (measurable_const_mul _), fun g => ?_⟩, fun β hβ => ?_⟩
  · have hm : Measurable fun h : GA E k =>
        ∑' n : ℤ, (FundamentalDomainCentre.fdL E k).indicator (1 : GA E k → ℝ≥0∞) (splitCentre E k 1 ^ n * (h * g)) :=
      Measurable.tsum fun n => hβ₁.comp ((measurable_const_mul _).comp (measurable_mul_const g))
    refine (hlint _ hm).trans ?_
    refine Eq.trans ?_ (FundamentalDomainCentre.fundamental_domain_tsum hD hk g)
    rw [ENNReal.tsum_prod']
    refine tsum_congr fun γ => tsum_congr fun n => ?_
    show (FundamentalDomainCentre.fdL E k).indicator (1 : GA E k → ℝ≥0∞) (splitCentre E k 1 ^ n * (ratGL E k γ * g)) =
      (FundamentalDomainCentre.fdL E k).indicator (1 : GA E k → ℝ≥0∞) (ratGL E k γ * splitCentre E k 1 ^ n * g)
    rw [← mul_assoc, FundamentalDomainCentre.split_centre_commute]
  · have hDm : Measurable (Dt : GA E k → ℝ) := hcont.measurable
    have hband : MeasurableSet (band E k) :=
      (measurableSet_le measurable_const hDm).inter (measurableSet_lt hDm measurable_const)
    have hΦ : Measurable ((band E k).indicator (1 : GA E k → ℝ≥0∞)) := by
      first | exact measurable_one.indicator hband | exact measurable_const.indicator hband
    have hH : ∀ᵐ h ∂nuB E k k, h ∈ {x : GA E k | Dt x = 1} := by
      filter_upwards [hae] with h hh0
      obtain ⟨γ, u, -, hu, hh⟩ := hh0
      show Dt h = 1
      rw [hh, hmul, hrat, huu k u hu, one_mul]
    have hΦH : ∀ h ∈ {x : GA E k | Dt x = 1}, ∀ g,
        (band E k).indicator (1 : GA E k → ℝ≥0∞) (h * g) = (band E k).indicator (1 : GA E k → ℝ≥0∞) g := by
      intro h hh g
      have hh' : Dt h = 1 := hh
      have hiff : h * g ∈ band E k ↔ g ∈ band E k := by
        show (1 ≤ Dt (h * g) ∧ Dt (h * g) < Dt (splitCentre E k 1)) ↔
          (1 ≤ Dt g ∧ Dt g < Dt (splitCentre E k 1))
        rw [hmul, hh', one_mul]
      by_cases hg : g ∈ band E k
      · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (hiff.2 hg)]
        first | rfl | simp
      · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (mt hiff.1 hg)]
    have hone : ∀ g, ∫⁻ r, ∫⁻ h, (FundamentalDomainCentre.fdL E k).indicator (1 : GA E k → ℝ≥0∞) (r⁻¹ * h * g)
        ∂nuB E k k ∂FundamentalDomainCentre.rhoZ E k = 1 := by
      intro g
      first | rw [FundamentalDomainCentre.lint_rhoZ] | simp only [FundamentalDomainCentre.lint_rhoZ]
      refine Eq.trans ?_ (FundamentalDomainCentre.fundamental_domain_tsum hD hk g)
      rw [ENNReal.tsum_prod', ENNReal.tsum_comm]
      refine tsum_congr fun n => ?_
      have hm : Measurable fun h : GA E k =>
          (FundamentalDomainCentre.fdL E k).indicator (1 : GA E k → ℝ≥0∞) ((splitCentre E k 1 ^ (-n))⁻¹ * h * g) :=
        hβ₁.comp ((measurable_mul_const g).comp (measurable_const_mul _))
      refine (hlint _ hm).trans (tsum_congr fun γ => ?_)
      show (FundamentalDomainCentre.fdL E k).indicator (1 : GA E k → ℝ≥0∞) ((splitCentre E k 1 ^ (-n))⁻¹ * ratGL E k γ * g) =
        (FundamentalDomainCentre.fdL E k).indicator (1 : GA E k → ℝ≥0∞) (ratGL E k γ * splitCentre E k 1 ^ n * g)
      rw [_root_.zpow_neg, inv_inv, FundamentalDomainCentre.split_centre_commute]
    have hin : ∀ g, ∫⁻ r, (band E k).indicator (1 : GA E k → ℝ≥0∞) (r * g) ∂FundamentalDomainCentre.rhoZ E k = 1 := by
      intro g
      first | rw [FundamentalDomainCentre.lint_rhoZ] | simp only [FundamentalDomainCentre.lint_rhoZ]
      rw [tsum_eq_single ⌊Real.log (Dt g) / ((k : ℝ) * (Module.finrank ℚ E : ℝ))⌋]
      · exact Set.indicator_of_mem ((FundamentalDomainCentre.split_centre_band_iff hD hk _ g).2 rfl) _
      · intro n hn
        exact Set.indicator_of_notMem (fun hb => hn ((FundamentalDomainCentre.split_centre_band_iff hD hk n g).1 hb)) _
    have hfin : IsFiniteMeasure (GlobalTheory.AutomorphicL2Unitary.quotMeasure (latticeGL E k) μ) := by
      first
      | exact GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E k μ
      | exact @GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E _ _ k _ μ ‹_›
      | exact (GlobalTheory.CovolGL.finvol E k μ).1
    have hfinF : μ (FundamentalDomainCentre.fdL E k) < ∞ :=
      lt_of_eq_of_lt (GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ (GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom (latticeGL E k) μ)).symm
        hfin.measure_univ_lt_top
    have hQ := hQ1 (GA E k) μ (nuB E k k) (FundamentalDomainCentre.rhoZ E k) {x : GA E k | Dt x = 1} β
      ((FundamentalDomainCentre.fdL E k).indicator (1 : GA E k → ℝ≥0∞)) hinv hH hβ hβ₁ hone
      ((band E k).indicator (1 : GA E k → ℝ≥0∞)) hΦ hΦH
    calc μ.withDensity β (band E k)
        = ∫⁻ g, (band E k).indicator (1 : GA E k → ℝ≥0∞) g ∂μ.withDensity β :=
          (lintegral_indicator_one hband).symm
      _ = ∫⁻ g, ∫⁻ r, (band E k).indicator (1 : GA E k → ℝ≥0∞) (r * g) ∂FundamentalDomainCentre.rhoZ E k
          ∂μ.withDensity ((FundamentalDomainCentre.fdL E k).indicator (1 : GA E k → ℝ≥0∞)) := hQ
      _ = ∫⁻ _, 1 ∂μ.withDensity ((FundamentalDomainCentre.fdL E k).indicator (1 : GA E k → ℝ≥0∞)) := lintegral_congr hin
      _ = μ (FundamentalDomainCentre.fdL E k) := by
          rw [lintegral_one, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
            lintegral_indicator_one hF]
      _ < ∞ := hfinF

end PositivityTheory.AdelicQuotientData

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ExponentialDecomposition
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace ExponentialDecomposition

section Loc

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ)

theorem torusPow_zero : Iwasawa.torusPow F n 0 = 1 := by
  apply Units.ext
  rw [Iwasawa.coe_torusPow]
  simp

theorem exp_one : Iwasawa.iwasawaExponent F n 1 = 0 := by
  have := Iwasawa.iwasawaExponent_torusPow F n 0
  rwa [torusPow_zero] at this

theorem exp_of_mem {κ : GL (Fin n) F} (hκ : κ ∈ GLnLocal.integralGL F n) :
    Iwasawa.iwasawaExponent F n κ = 0 := by
  have := Iwasawa.iwasawaExponent_mul_of_mem_integralGL F n 1 hκ
  rw [one_mul, exp_one] at this
  exact this

theorem isOpen_exp (A : Set (Fin n → ℤ)) :
    IsOpen {x : GL (Fin n) F | Iwasawa.iwasawaExponent F n x ∈ A} := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' (GLnLocal.integralGL F n : Set (GL (Fin n) F)), ?_, ?_, ?_⟩
  · intro y hy
    have e : y = x * (x⁻¹ * y) := by group
    show Iwasawa.iwasawaExponent F n y ∈ A
    rw [e, Iwasawa.iwasawaExponent_mul_of_mem_integralGL F n x hy]
    exact hx
  · exact (GLnLocal.isOpen_integralGL F n).preimage (continuous_const_mul _)
  · show x⁻¹ * x ∈ GLnLocal.integralGL F n
    rw [inv_mul_cancel]
    exact one_mem _

theorem isClopen_exp (l : Fin n → ℤ) : IsClopen {x : GL (Fin n) F | Iwasawa.iwasawaExponent F n x = l} :=
  ⟨isOpen_compl_iff.1 (isOpen_exp F n {l}ᶜ), isOpen_exp F n {l}⟩

end Loc

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem mem_int_iff (w : Pl E) (x : w.adicCompletion E) :
    x ∈ (ValuativeRel.valuation (w.adicCompletion E)).integer ↔ x ∈ w.adicCompletionIntegers E := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  rw [Valuation.mem_integer_iff, HeightOneSpectrum.mem_adicCompletionIntegers]
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation _) Valued.v).le_one_iff_le_one

theorem corner_entry {R S : Type} [CommRing R] [CommRing S] (s : R →ₙ+* S) (g : GL (Fin k) R) (i c : Fin k)
    (h : g.val i c = (1 : Matrix (Fin k) (Fin k) R) i c) :
    (cornerGL k s g).val i c = (1 : Matrix (Fin k) (Fin k) S) i c := by
  change (1 : Matrix (Fin k) (Fin k) S) i c - s ((1 : Matrix (Fin k) (Fin k) R) i c) + s (g.val i c) = _
  rw [h, sub_add_cancel]

theorem uu_one : UU 0 (1 : GA E k) :=
  ⟨fun i c h => by rw [Units.val_one, Matrix.one_apply_ne h.ne'], fun i => by rw [Units.val_one, Matrix.one_apply_eq],
    fun i c h => absurd h (Nat.not_lt_zero _)⟩

theorem uu_mul {g h : GA E k} (hg : UU 0 g) (hh : UU 0 h) : UU 0 (g * h) := by
  refine ⟨fun i c hci => ?_, fun i => ?_, fun i c h => absurd h (Nat.not_lt_zero _)⟩
  · rw [Units.val_mul, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rcases lt_or_ge j i with hj | hj
    · rw [hg.1 i j hj, zero_mul]
    · rw [hh.1 j c (lt_of_lt_of_le hci hj), mul_zero]
  · rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hg.2.1, hh.2.1, one_mul]
    · intro j _ hj
      rcases lt_or_gt_of_ne hj with hj | hj
      · rw [hg.1 i j hj, zero_mul]
      · rw [hh.1 j i hj, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h

theorem uu_fl (w : Pl E) {n : GL (Fin k) (w.adicCompletion E)} (hn : n ∈ Iwasawa.unipotent (w.adicCompletion E) k) :
    UU 0 (fl k w n) := by
  have key : ∀ i c : Fin k, c ≤ i → (fl k w n).val i c = (1 : Matrix (Fin k) (Fin k) (Ad E)) i c := by
    intro i c hci
    show (cornerGL k (sFin E) (cornerGL k (sLoc E w) n)).val i c = _
    refine corner_entry _ _ _ _ (corner_entry _ _ _ _ ?_)
    rcases hci.lt_or_eq with h | h
    · rw [hn.1 h, Matrix.one_apply_ne h.ne']
    · subst h
      rw [hn.2, Matrix.one_apply_eq]
  refine ⟨fun i c h => ?_, fun i => ?_, fun i c h => absurd h (Nat.not_lt_zero _)⟩
  · rw [key i c h.le, Matrix.one_apply_ne h.ne']
  · rw [key i i le_rfl, Matrix.one_apply_eq]

theorem cLoc_uu {u : GA E k} (hu : UU 0 u) (w : Pl E) : cLoc w u ∈ Iwasawa.unipotent (w.adicCompletion E) k := by
  refine ⟨fun i c h => ?_, fun i => ?_⟩
  · show ((pLoc E w).comp (pFin E)) (u.val i c) = 0
    rw [hu.1 i c h, map_zero]
  · show ((pLoc E w).comp (pFin E)) (u.val i i) = 1
    rw [hu.2.1 i, map_one]

def Gd (g : GA E k) (w : Pl E) : Prop :=
  ∀ i j, (pFin E (g.val i j)).1 w ∈ w.adicCompletionIntegers E ∧
    (pFin E ((g⁻¹ : GA E k).val i j)).1 w ∈ w.adicCompletionIntegers E

theorem gd_fin (g : GA E k) : {w | ¬ Gd g w}.Finite := by
  have h : ∀ᶠ w in cofinite, Gd g w := by
    unfold Gd
    simp only [Filter.eventually_all]
    intro i j
    exact (pFin E (g.val i j)).2.and (pFin E ((g⁻¹ : GA E k).val i j)).2
  exact Filter.eventually_cofinite.1 h

theorem gd_mem {g : GA E k} {w : Pl E} (h : Gd g w) : cLoc w g ∈ GLnLocal.integralGL (w.adicCompletion E) k := by
  rw [GLnLocal.mem_integralGL_iff]
  refine ⟨fun i j => (mem_int_iff w _).2 (h i j).1, fun i j => ?_⟩
  rw [← map_inv]
  exact (mem_int_iff w _).2 (h i j).2

theorem isOpen_gd (T : Set (Pl E)) : IsOpen {g : GA E k | ∀ w, w ∉ T → Gd g w} := by
  let V : Set (Af E) := {x | ∀ w, w ∉ T → x.1 w ∈ w.adicCompletionIntegers E}
  have hV : IsOpen V := RestrictedProduct.isOpen_forall_imp_mem (fun w => GroundTheory.Global.isOpen_adicCompletionIntegers w)
  have e : {g : GA E k | ∀ w, w ∉ T → Gd g w} = ⋂ i, ⋂ j,
      ((fun g : GA E k => pFin E (g.val i j)) ⁻¹' V ∩ (fun g : GA E k => pFin E ((g⁻¹ : GA E k).val i j)) ⁻¹' V) := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage, V, Gd]
    exact ⟨fun h i j => ⟨fun w hw => (h w hw i j).1, fun w hw => (h w hw i j).2⟩,
      fun h w hw i j => ⟨(h i j).1 w hw, (h i j).2 w hw⟩⟩
  rw [e]
  have hp : Continuous (pFin E) := continuous_snd
  have hv : Continuous (fun g : GA E k => (g.val : Matrix (Fin k) (Fin k) (Ad E))) := Units.continuous_val
  have hw : Continuous (fun g : GA E k => ((g⁻¹ : GA E k).val : Matrix (Fin k) (Fin k) (Ad E))) :=
    Units.continuous_coe_inv
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => IsOpen.inter ?_ ?_
  · exact hV.preimage (hp.comp (hv.matrix_elem i j))
  · exact hV.preimage (hp.comp (hw.matrix_elem i j))

theorem isOpen_G0 (hG : jumpWindows.G0) {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {k : ℕ}
    (S : Finset (Pl E)) : IsOpen (G0 (k := k) S) := by
  have hcont : ∀ w, Continuous (cLoc w : GA E k → _) := (hG E k).2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [isOpen_iff_forall_mem_open]
  intro g hg
  have hT : {w | ¬ Gd g w ∧ w ∉ S}.Finite := (gd_fin g).subset fun w hw => hw.1
  refine ⟨{h | ∀ w, w ∉ {w | ¬ Gd g w} → Gd h w} ∩
    ⋂ w ∈ {w | ¬ Gd g w ∧ w ∉ S}, (cLoc w) ⁻¹' {x | Iwasawa.iwasawaExponent _ k x = 0}, ?_, ?_, ?_⟩
  · rintro h ⟨h1, h2⟩ w hw
    by_cases hg' : Gd g w
    · exact exp_of_mem _ _ (gd_mem (h1 w fun h => h hg'))
    · exact Set.mem_iInter₂.1 h2 w ⟨hg', hw⟩
  · exact (isOpen_gd _).inter (hT.isOpen_biInter fun w _ => (isOpen_exp _ k {0}).preimage (hcont w))
  · refine ⟨fun w hw => not_not.1 hw, Set.mem_iInter₂.2 fun w hw => hg w hw.2⟩

theorem decomp (hG : jumpWindows.G0) {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {k : ℕ}
    (S T : Finset (Pl E)) : ∀ g : GA E k, (∀ w, w ∉ S → Iwasawa.iwasawaExponent _ k (cLoc w g) = 0) →
      (∀ w, w ∉ S → w ∉ T → cLoc w g ∈ GLnLocal.integralGL (w.adicCompletion E) k) →
      ∃ n g₀ κ : GA E k, UU 0 n ∧ InS S g₀ ∧ cInf κ = 1 ∧ (∀ w ∈ S, cLoc w κ = 1) ∧
        (∀ w, cLoc w κ ∈ GLnLocal.integralGL (w.adicCompletion E) k) ∧ g = n * g₀ * κ := by
  obtain ⟨-, -, -, hloc, hlocne, -, -, -, -, -, hsplit, -⟩ := hG E k
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro g _ hK
    obtain ⟨g₀, h1, h2, h3⟩ := hsplit S g
    refine ⟨1, g₀, g₀⁻¹ * g, uu_one, h3, ?_, ?_, ?_, ?_⟩
    · rw [map_mul, map_inv, h1, inv_mul_cancel]
    · intro w hw
      rw [map_mul, map_inv, h2 w hw, inv_mul_cancel]
    · intro w
      by_cases hw : w ∈ S
      · rw [map_mul, map_inv, h2 w hw, inv_mul_cancel]
        exact one_mem _
      · rw [map_mul, map_inv, h3 w hw, inv_one, one_mul]
        exact hK w hw (Finset.notMem_empty w)
    · group
  | insert v T hvT ih =>
    intro g hexp hK
    by_cases hvS : v ∈ S
    · refine ih g hexp fun w hw hwT => hK w hw fun h => ?_
      rcases Finset.mem_insert.1 h with h | h
      · exact hw (h ▸ hvS)
      · exact hwT h
    · obtain ⟨u, hu, κ, hκ, he⟩ := Iwasawa.exists_eq_mul_torusPow_iwasawaExponent _ k (cLoc v g)
      rw [hexp v hvS, torusPow_zero, mul_one] at he
      have hloc' : ∀ w, w ≠ v → cLoc w ((fl k v u)⁻¹ * g) = cLoc w g := by
        intro w hw
        rw [map_mul, map_inv, hlocne v w u hw, inv_one, one_mul]
      have hv' : cLoc v ((fl k v u)⁻¹ * g) = κ := by
        rw [map_mul, map_inv, hloc v u, he, inv_mul_cancel_left]
      obtain ⟨n, g₀, κ', hn, h1, h2, h3, h4, h5⟩ := ih ((fl k v u)⁻¹ * g)
        (fun w hw => by
          by_cases hwv : w = v
          · subst hwv
            rw [hv']
            exact exp_of_mem _ _ hκ
          · rw [hloc' w hwv]
            exact hexp w hw)
        (fun w hw hwT => by
          by_cases hwv : w = v
          · subst hwv
            rw [hv']
            exact hκ
          · rw [hloc' w hwv]
            exact hK w hw fun h => (Finset.mem_insert.1 h).elim hwv hwT)
      refine ⟨fl k v u * n, g₀, κ', uu_mul (uu_fl v hu) hn, h1, h2, h3, h4, ?_⟩
      rw [mul_assoc, mul_assoc, ← mul_assoc n, ← h5, ← mul_assoc, mul_inv_cancel, one_mul]

end ExponentialDecomposition

theorem open_decomposition_of_G0 : jumpWindows.G0 → C0 := by
  intro hG E _ _ _ k S
  have hGk := hG E k
  obtain ⟨-, -, hinf1, hloc, hlocne, -, -, -, -, -, -, -, hcont, -⟩ := hGk
  refine ⟨ExponentialDecomposition.isOpen_G0 hG S, fun w _ => by rw [map_one]; exact ExponentialDecomposition.exp_one _ _, ?_, ?_, ?_, ?_, ?_⟩
  · intro u g hu
    constructor
    · intro h w hw
      rw [← h w hw, map_mul, Iwasawa.iwasawaExponent_mul_of_mem_unipotent _ _ (ExponentialDecomposition.cLoc_uu hu w)]
    · intro h w hw
      rw [map_mul, Iwasawa.iwasawaExponent_mul_of_mem_unipotent _ _ (ExponentialDecomposition.cLoc_uu hu w)]
      exact h w hw
  · intro g hg
    classical
    exact ExponentialDecomposition.decomp hG S (ExponentialDecomposition.gd_fin g).toFinset g hg fun w _ hwT =>
      ExponentialDecomposition.gd_mem (not_not.1 fun h => hwT ((ExponentialDecomposition.gd_fin g).mem_toFinset.2 h))
  · intro g
    refine (ExponentialDecomposition.gd_fin g).subset fun w hw => ?_
    intro h
    exact hw (ExponentialDecomposition.exp_of_mem _ _ (ExponentialDecomposition.gd_mem h))
  · intro w l
    exact (ExponentialDecomposition.isClopen_exp _ k l).preimage (hcont w)
  · intro w g
    refine ⟨g * (fl k w (cLoc w g))⁻¹, ?_, ?_, ?_, ?_⟩
    · rw [map_mul, map_inv, hloc, mul_inv_cancel]
    · group
    · rw [map_mul, map_inv, hinf1, inv_one, mul_one]
    · intro v hv
      rw [map_mul, map_inv, hlocne w v _ hv, inv_one, mul_one]

end PositivityTheory.AdelicQuotientData

end
end
