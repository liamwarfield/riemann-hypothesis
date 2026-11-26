module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BXiAsm
public import Formalism.FlagUnipotentLattices.ValuationProductBound
public import Formalism.FlagUnipotentLattices.AlgebraicIdentityHigherDegree
public import Formalism.FlagUnipotentLattices.CardSubgroupsOfIndexLe

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaCutoffLimit
open MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.JCTx2

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section beta

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem JF_cutF (D : RealPlaceData k r Wp Wq) (χ : ℝ → ℝ) (F : Mat k r → (Wq →L[ℂ] Wp)) (ε : ℝ)
    (g : Mat k r) :
    JF D (Formalism.FourierDecayAlt.D.cutF D χ F ε) g = ((χ (Gf k r D.z D.z' g / ε) : ℝ) : ℂ) • JF D F g := by
  unfold JF besselJ
  rw [← integral_smul]
  refine integral_congr_ae ?_
  have hae : ∀ᵐ p ∂((D.μW.prod D.μN).prod (D.μW'.prod D.μN)), D.inSS p := Formalism.FourierDecayAlt.P.B5.ae_inSS D
  filter_upwards [hae] with p hp
  have e := Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs D hp g
  simp only [sgs] at e
  simp only [Formalism.FourierDecayAlt.D.cutF, e]
  rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_comm]

theorem hsVec_smul' [FiniteDimensional ℂ Wq] (a : ℂ) (A : Wq →L[ℂ] Wp) : hsVec (a • A) = a • hsVec A := by
  unfold hsVec; ext i; simp

theorem hsVec_cont' [FiniteDimensional ℂ Wq] : Continuous (hsVec : (Wq →L[ℂ] Wp) → _) := by
  unfold hsVec
  exact (PiLp.continuous_toLp 2 _).comp
    (continuous_pi fun i => (ContinuousLinearMap.apply ℂ Wp (stdOrthonormalBasis ℂ Wq i)).continuous)

theorem inner_self_real {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (x : E) :
    inner ℂ x x = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
  rw [inner_self_eq_norm_sq_to_K]; norm_cast

theorem bcWeight_nonneg' (T T' : ℝ) (q : (Fin r → ℂ) × ℂ) : 0 ≤ bcWeight k r T T' q := by
  unfold bcWeight
  split_ifs with h
  · exact mul_nonneg (Finset.prod_nonneg fun a _ => pow_nonneg (norm_nonneg _) _)
      (pow_nonneg (sub_nonneg.2 h) _)
  · exact le_rfl

theorem beta_cutF [FiniteDimensional ℂ Wq] (D : RealPlaceData k r Wp Wq) (χ : ℝ → ℝ)
    (F : Mat k r → (Wq →L[ℂ] Wp)) (ε : ℝ) :
    beta D (Formalism.FourierDecayAlt.D.cutF D χ F ε) (Formalism.FourierDecayAlt.D.cutF D χ F ε) =
      ∫ q, ((bcWeight k r (Tz k r D.z) (Tz k r D.z') q * χ (Gf k r D.z D.z' (gq D q) / ε) ^ 2 *
        ‖hsVec (JF D F (gq D q))‖ ^ 2 : ℝ) : ℂ) := by
  unfold beta betaBig
  refine integral_congr_ae (ae_of_all _ fun q => ?_)
  simp only [gq]
  rw [JF_cutF, hsVec_smul', inner_smul_left, inner_smul_right, inner_self_real, Complex.conj_ofReal]
  push_cast
  ring

theorem cut_bound {χ : ℝ → ℝ} (hχ : Formalism.FourierDecayAlt.C6.IsCut0 χ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |χ x| ≤ M := by
  obtain ⟨hs, ⟨δ, _, h0⟩, h1⟩ := hχ
  have hc : Continuous χ := hs.continuous
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := δ) (b := 1)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max M 1, le_trans zero_le_one (le_max_right _ _), fun x => ?_⟩
  by_cases hx : x < δ
  · rw [h0 x hx, abs_zero]; exact le_trans zero_le_one (le_max_right _ _)
  by_cases hx1 : 1 ≤ x
  · rw [h1 x hx1, abs_one]; exact le_max_right _ _
  · have := hM x ⟨not_lt.1 hx, le_of_not_ge hx1⟩
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)

end beta

section core

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem beta_cut_limit (D : RealPlaceData k r Wp Wq) (χ : ℝ → ℝ) (hχ : Formalism.FourierDecayAlt.C6.IsCut0 χ)
    (F : Mat k r → (Wq →L[ℂ] Wp)) (A : ℝ) (hA : AB k r ≤ A) (hF : ∀ m : ℕ, InCC A m F) :
    normSq D F ≠ ⊤ ∧
      Tendsto (fun ε => beta D (Formalism.FourierDecayAlt.D.cutF D χ F ε) (Formalism.FourierDecayAlt.D.cutF D χ F ε))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (((normSq D F).toReal : ℝ) : ℂ)) := by

  obtain ⟨_, _, _, hB1, _⟩ := Formalism.FourierDecayAlt.P.b_any_of_xi k r Wp Wq D A hA
  obtain ⟨C0, hC0⟩ := hB1
  obtain ⟨c4, hc4⟩ := hF 4
  have hfin : normSq D F ≠ ⊤ := (hC0 F F c4 c4 (hF 5) (hF 5) hc4 hc4).1
  refine ⟨hfin, ?_⟩
  set w : (Fin r → ℂ) × ℂ → ℝ := bcWeight k r (Tz k r D.z) (Tz k r D.z') with hw
  set J : (Fin r → ℂ) × ℂ → _ := fun q => hsVec (JF D F (gq D q)) with hJ
  set h : (Fin r → ℂ) × ℂ → ℝ := fun q => w q * ‖J q‖ ^ 2 with hh
  set μQ : Measure ((Fin r → ℂ) × ℂ) := volume.restrict (Qset D) with hμQ
  have hw0 : ∀ q, 0 ≤ w q := fun q => bcWeight_nonneg' _ _ q
  have hh0 : ∀ q, 0 ≤ h q := fun q => mul_nonneg (hw0 q) (sq_nonneg _)
  have hwQ : ∀ q, q ∉ Qset D → w q = 0 := by
    intro q hq
    have : ¬ 0 < w q := hq
    exact le_antisymm (not_lt.1 this) (hw0 q)

  have hcont : ContinuousOn F (GV k r) := Formalism.FourierDecayAlt.P.B7.jc_cont (hF 4)
  have hJm : AEStronglyMeasurable J μQ := by
    have h1 := Formalism.FourierDecayAlt.P.B7.jc_aesm_J D hcont (1, 1)
    have e : (fun q => Jtau D (1, 1) F (gq D q)) = fun q => JF D F (gq D q) :=
      funext fun q => Formalism.FourierDecayAlt.P.bessel_function_trivial_index k r Wp Wq D F (gq D q)
    rw [e] at h1
    exact hsVec_cont'.comp_aestronglyMeasurable h1
  have hwm : Measurable w := Formalism.FourierDecayAlt.P.B7.measurable_bcWeight _ _
  have hhm : AEStronglyMeasurable h μQ := hwm.aestronglyMeasurable.mul (hJm.norm.pow 2)

  have hlin : normSq D F = ∫⁻ q, ENNReal.ofReal (h q) ∂μQ := by
    show (∫⁻ q, ENNReal.ofReal (h q)) = _
    rw [hμQ, setLIntegral_eq_of_support_subset]
    intro q hq
    by_contra hn
    apply hq
    simp only [hh, hwQ q hn, zero_mul, ENNReal.ofReal_zero]
  have hhi : Integrable h μQ := by
    refine ⟨hhm, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hh0), ← hlin]
    exact lt_top_iff_ne_top.2 hfin
  have hlim : ∫ q, ((h q : ℝ) : ℂ) ∂μQ = (((normSq D F).toReal : ℝ) : ℂ) := by
    rw [integral_complex_ofReal, integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hh0) hhm, ← hlin]

  obtain ⟨M, hM0, hM⟩ := cut_bound hχ
  have hχc : Continuous χ := hχ.1.continuous
  have hGc : Continuous fun x : Mt k r => Gf k r D.z D.z' (Matrix.of x) :=
    (Formalism.FourierDecayAlt.P.DifferentialOperatorClasses.gf_cont k r D.z D.z').comp continuous_id
  set Fe : ℝ → (Fin r → ℂ) × ℂ → ℂ := fun ε q =>
    ((w q * χ (Gf k r D.z D.z' (gq D q) / ε) ^ 2 * ‖J q‖ ^ 2 : ℝ) : ℂ) with hFe
  have hbeta : ∀ ε, beta D (Formalism.FourierDecayAlt.D.cutF D χ F ε) (Formalism.FourierDecayAlt.D.cutF D χ F ε) = ∫ q, Fe ε q ∂μQ := by
    intro ε
    rw [beta_cutF, hμQ, setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro q hq
    simp only [hFe, hwQ q hq, zero_mul, Complex.ofReal_zero]
  simp_rw [hbeta]
  rw [← hlim]
  refine tendsto_integral_filter_of_dominated_convergence (fun q => M ^ 2 * h q) ?_ ?_ ?_ ?_
  · refine Eventually.of_forall fun ε => ?_
    have hχm : AEStronglyMeasurable (fun q => χ (Gf k r D.z D.z' (gq D q) / ε)) μQ := by
      refine (((hχc.comp (hGc.div_const ε)).measurable.comp
        (Formalism.FourierDecayAlt.P.B7.measurable_gqM D)).aestronglyMeasurable).congr ?_
      filter_upwards [Formalism.FourierDecayAlt.P.B7.ae_mem_good_set_restrict D] with q hq
      simp only [Function.comp_apply]
      rw [Formalism.FourierDecayAlt.P.B7.gqM_eq D hq]
      rfl
    exact Complex.continuous_ofReal.comp_aestronglyMeasurable
      ((hwm.aestronglyMeasurable.mul (hχm.pow 2)).mul (hJm.norm.pow 2))
  · refine Eventually.of_forall fun ε => ae_of_all _ fun q => ?_
    simp only [hFe, Complex.norm_real, Real.norm_eq_abs]
    have h2 : χ (Gf k r D.z D.z' (gq D q) / ε) ^ 2 ≤ M ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hM _) 2
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg (hw0 q) (sq_nonneg _)) (sq_nonneg _))]
    simp only [hh]
    nlinarith [hw0 q, sq_nonneg ‖J q‖, mul_nonneg (hw0 q) (sq_nonneg ‖J q‖)]
  · exact hhi.const_mul _
  · filter_upwards [Formalism.FourierDecayAlt.P.B7.ae_mem_good_set_restrict D] with q hq
    have hG : 0 < Gf k r D.z D.z' (gq D q) := (Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom D hq).2.2
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin, Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (eventually_le_nhds hG)] with ε hε hle
    simp only [hFe, hh]
    rw [hχ.2.2 _ ((one_le_div (Set.mem_Ioi.mp hε)).mpr hle)]
    push_cast
    ring

end core

theorem AB_le_of_thr (k r N : ℕ) (A₀ : ℝ) (hk : 2 ≤ k)
    (h : 1 * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) ≤ A₀) :
    AB k r ≤ A₀ := by
  unfold AB
  set n : ℝ := 2 * (r : ℝ) + k + 1 with hn
  set x : ℝ := (r : ℝ) + 1 with hx
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have h1 : (k : ℝ) + r ≤ n := by rw [hn]; linarith
  have h2 : 1 ≤ x := by rw [hx]; linarith
  have h3 : 3 ≤ n := by rw [hn]; linarith
  have h4 : x ≤ x ^ 4 := by
    have : 1 ≤ x ^ 3 := one_le_pow₀ h2
    nlinarith
  have h5 : 2 * n + 1 ≤ n ^ 3 := by nlinarith
  have h6 : 0 ≤ (N : ℝ) * n ^ 2 := mul_nonneg hN (sq_nonneg _)
  calc 2 * ((k : ℝ) + r) * x + 1 ≤ 2 * n * x + 1 := by nlinarith
    _ ≤ x * (2 * n + 1) := by nlinarith
    _ ≤ x * n ^ 3 := by nlinarith
    _ ≤ x ^ 4 * n ^ 3 := by nlinarith [pow_pos (show (0 : ℝ) < n by linarith) 3]
    _ ≤ 1 * x ^ 4 * ((N : ℝ) * n ^ 2 + n ^ 3) := by nlinarith [pow_pos (show (0 : ℝ) < x by linarith) 4]
    _ ≤ A₀ := h

end Formalism.FourierDecayAlt.P.JCTx2

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt

theorem beta_cutoff_limit : Formalism.FourierDecayAlt.JCT.BetaCutLimit := by
  refine ⟨1, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hP v
  obtain ⟨_, _, _, hB, _, _, _, _, _, _, hk, hA, _⟩ := hP
  exact Formalism.FourierDecayAlt.P.JCTx2.beta_cut_limit (T v).base χ hB.1 (f v) A₀
    (Formalism.FourierDecayAlt.P.JCTx2.AB_le_of_thr S.G.k S.G.r S.Ntop A₀ hk hA) (fun m => (hB.2 v).2.2.2.2.1 m)

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.NormChainLemmas
namespace Formalism.FourierDecayAlt.P.NormChainLemmas

open Formalism.FourierDecayAlt.PN Finset NumberField

open scoped ComplexOrder ComplexConjugate

open Classical

theorem exactCores : Formalism.FourierDecayAlt.PN.ExactCores :=
  ⟨Formalism.HermitianLatticeCounting.Final.S4.step4, Formalism.HermitianLatticeCounting.Final.S4.omCount, Formalism.HermitianLatticeCounting.Final.S4.weightedCS,
   Formalism.HermitianLatticeCounting.Final.ExpansionTerms.component_total_sixty_four⟩

theorem loopCores : Formalism.FourierDecayAlt.PN.LoopCores :=
  ⟨Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.nonDegSum, Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.degSum, Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.single_row_lattice_sum_bound,
   Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.gainSqrt, Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.lattice_exp_sum_upper_bound, Formalism.FourierDecayAlt.Final.pb_loopsJoint,
   Formalism.FourierDecayAlt.Final.pb_loopsGiveRows⟩

theorem nGChain : Formalism.FourierDecayAlt.PN.NGChain :=
  ⟨exactCores, Formalism.FourierDecayAlt.Final.pn_classSquaresSum, Formalism.FourierDecayAlt.Final.pn_rowFromClasses,
   Formalism.FourierDecayAlt.Final.pn_classCS, Formalism.FourierDecayAlt.Final.pn_firstBracket, Formalism.FourierDecayAlt.Final.pn_secondBracket,
   Formalism.FourierDecayAlt.Final.pn_meanAmpJoint, Formalism.FourierDecayAlt.Final.pn_rowNGAbstract, Formalism.FourierDecayAlt.Final.pn_normBound,
   Formalism.FourierDecayAlt.Final.pn_framePassage, Formalism.FourierDecayAlt.Final.pn_normRe, Formalism.FourierDecayAlt.Final.pn_exponentSum,
   Formalism.FourierDecayAlt.Final.pn_nGNumbers⟩

end Formalism.FourierDecayAlt.P.NormChainLemmas

namespace Formalism.FourierDecayAlt.P

theorem loop_kernels : Formalism.FourierDecayAlt.PN.LoopCores := NormChainLemmas.loopCores

theorem norm_chain : Formalism.FourierDecayAlt.PN.NGChain := NormChainLemmas.nGChain

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpPRad
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField Matrix

noncomputable section

section defs

variable (k r : ℕ)

def rowsN (l : Fin (r + 1)) (s : Fin (k + 1)) : Fin (r - l.val + k) → Fin (2 * r + k + 1) :=
  fun j => ⟨if j.val < r - l.val + s.val then l.val + j.val else l.val + j.val + 1, by
    have := j.isLt; have := s.isLt; have := l.isLt; split_ifs <;> omega⟩

def NL {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 1))
    (u : ℂ) (f : Q.Mx k r → E) : Q.Mx k r → E :=
  fun g => ∑ s : Fin (k + 1), ∑ t : Fin (k + 1),
    (((-1 : ℂ) ^ ((s : ℕ) + (t : ℕ))) * herm (Hpk k r) (bvec (wI k r s)) z' * (g⁻¹ *ᵥ z) (wI k r t)) •
      qminorOp (Q.EH k r) (rowsN k r l s) (rowsN k r l t) u f g

def FN {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (z z' : Fin (2 * r + k + 1) → ℂ) (Y : ℂ)
    (J : Q.Mx k r → E) (l : Fin (r + 1)) : Q.Fn k r E :=
  Q.resG k r (Fin.last r) (NL k r z z' l (Q.uC k r l Y) J)

end defs

def JDRBeta : Prop :=
  ∀ k r : ℕ, ∃ σ : ℂ, σ ≠ 0 ∧ ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (z z' : Fin (2 * r + k + 1) → ℂ)
    (Y : ℂ) (f : Q.Mx k r → E), inWb k r z → ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r),
      rhatOp k r z z' Y f (Q.wCell k r (Fin.last r) c * g) =
        (σ * starRingEnd ℂ (∏ a, c a)) • NL k r z z' 0 (Q.uC k r 0 Y) f (Q.wCell k r (Fin.last r) c * g)

def JDRTop : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq))
    (D : Set (Q.Mx k r)) (Y : ℂ), inWb k r z → inWb k r z' → Q.IsDom k r z z' 0 D →
    ∀ J ∈ Q.FFl k r z z' π π' 0 D, ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r), Q.wCell k r (Fin.last r) c * g ∈ D →
      FN k r z z' Y J (Fin.last r) c g = -Q.QL k r z z' (Fin.last r) Y 1 0 (Q.resG k r (Fin.last r) J) c g

def JDRStepA : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (hr : 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp))
    (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) (D : Set (Q.Mx k r)) (Y : ℂ), inWb k r z → inWb k r z' → Q.IsDom k r z z' 0 D →
    ∀ J ∈ Q.FFl k r z z' π π' 0 D, ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r), Q.wCell k r (Fin.last r) c * g ∈ D →
      FN k r z z' Y J ⟨r - 1, by omega⟩ c g =
        (Y • FN k r z z' Y J (Fin.last r) + Q.crd (Formalism.QuantumDeterminants.pOp ⟨r - 1, by omega⟩) (FN k r z z' Y J (Fin.last r)) -
          Q.crd (Formalism.QuantumDeterminants.ciOp ⟨r - 1, by omega⟩) (Q.QL k r z z' (Fin.last r) Y 1 1 (Q.resG k r (Fin.last r) J))) c g

def JDRStepB : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq))
    (D : Set (Q.Mx k r)) (Y : ℂ), inWb k r z → inWb k r z' → Q.IsDom k r z z' 0 D →
    ∀ J ∈ Q.FFl k r z z' π π' 0 D, ∀ (l : ℕ) (hl : l + 2 ≤ r),
    ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r), Q.wCell k r (Fin.last r) c * g ∈ D →
      FN k r z z' Y J ⟨l, by omega⟩ c g =
        (Y • FN k r z z' Y J ⟨l + 1, by omega⟩ + Q.crd (Formalism.QuantumDeterminants.pOp ⟨l, by omega⟩) (FN k r z z' Y J ⟨l + 1, by omega⟩) -
          Q.crd (Formalism.QuantumDeterminants.cOp ⟨l + 1, by omega⟩) (Q.crd (Formalism.QuantumDeterminants.ciOp ⟨l, by omega⟩) (FN k r z z' Y J ⟨l + 2, by omega⟩))) c g

def JDRChainP : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq))
    (D : Set (Q.Mx k r)) (Y : ℂ), inWb k r z → inWb k r z' → Q.IsDom k r z z' 0 D →
    ∀ J ∈ Q.FFl k r z z' π π' 0 D, ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r), Q.wCell k r (Fin.last r) c * g ∈ D →
      FN k r z z' Y J 0 c g =
        -(Q.QL k r z z' (Fin.last r) Y 1 0 (Q.crd (Q.cmp (Q.vAB r Y r) 0) (Q.resG k r (Fin.last r) J)) +
          Q.QL k r z z' (Fin.last r) Y 1 1 (Q.crd (Q.cmp (Q.vAB r Y r) 1) (Q.resG k r (Fin.last r) J))) c g

def JDRConseq : Prop := JDRTop → JDRStepA → JDRStepB → JDRChainP

theorem jDRRadP_of_parts (hB : JDRBeta) (hT : JDRTop) (hA : JDRStepA) (hS : JDRStepB) (hC : JDRConseq) :
    JDRRadP := by
  have hCh := hC hT hA hS
  intro k r
  obtain ⟨σ, hσ, hBσ⟩ := hB k r
  refine ⟨-σ⁻¹, ?_⟩
  intro Wp Wq _ _ _ _ z z' π π' D Y hz hz' hD J hJ c hc g hg hx
  have h1 := hBσ (Wq →L[ℂ] Wp) z z' Y J hz c hc g hg
  have h2 := congrArg Neg.neg (hCh Wp Wq k r z z' π π' D Y hz hz' hD J hJ c hc g hg hx)
  clear hBσ hCh hB hT hA hS hC
  simp only [Pi.neg_apply, neg_neg] at h2
  simp only [rhGrp, dMul, drbF, Pi.add_apply] at h2 ⊢
  rw [← h2]
  simp only [FN, Q.resG, h1]
  simp only [smul_smul, smul_neg, neg_smul]
  match_scalars <;> field_simp <;> ring

end

end Formalism.FourierDecayAlt.P.CutMP
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpM
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField Matrix

noncomputable section

section defs

variable (k r : ℕ)

def colsV (t : Fin (k + 1)) : Fin (r + k) → Fin (2 * r + k + 1) :=
  fun j => ⟨if j.val < t.val then r + j.val else r + j.val + 1, by have := j.isLt; have := t.isLt; split_ifs <;> omega⟩

def rowV (z : Fin (2 * r + k + 1) → ℂ) (g : Q.Mx k r) (J : Fin (r + k) → Fin (2 * r + k + 1))
    (p : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) → ℂ :=
  fun q =>
    if h : p.val < r then herm (Hpk k r) (g *ᵥ bvec q) (bvec (eI k r ⟨p.val, h⟩))
    else if h2 : p.val = r then herm (Hpk k r) (g *ᵥ bvec q) z
    else if q = J ⟨p.val - r - 1, by have := p.isLt; omega⟩ then 1 else 0

def alJ (z : Fin (2 * r + k + 1) → ℂ) (g : Q.Mx k r) (J : Fin (r + k) → Fin (2 * r + k + 1)) : ℂ :=
  (Matrix.of fun p q => rowV k r z g J p q).det

def rvhatOp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (z z' : Fin (2 * r + k + 1) → ℂ) (Y : ℂ)
    (f : Q.Mx k r → E) : Q.Mx k r → E :=
  fun g => ∑ t : Fin (k + 1), ∑ J ∈ jSetR k r,
    (((-1 : ℂ) ^ (t : ℕ)) * z' (wI k r t) * alJ k r z g J) •
      qminorOp (Q.EH k r) J (colsV k r t) (Q.uC k r (Fin.last r) Y - 1) f g

end defs

def JDRRadM : Prop :=
  ∀ k r : ℕ, ∃ ε : ℂ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
    [NormedSpace ℂ Wq] (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq))
    (D : Set (Q.Mx k r)) (Y : ℂ), inWb k r z → inWb k r z' → Q.IsDom k r z z' 0 D →
    ∀ J ∈ Q.FFl k r z z' π π' 0 D, ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r), Q.wCell k r (Fin.last r) c * g ∈ D →
      Q.resG k r (Fin.last r) (fun x => ε • rvhatOp k r z z' Y J x) c g =
        rhvGrp k r z z' Y (Q.resG k r (Fin.last r) J) c g

def JDRRealInvM : Prop :=
  ∀ (ε : ℂ) (Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ → ∀ v (y : ℝ),
      ∃ Θ : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)),
        PolyOp (2 * S.G.r + S.G.k + 1) ((S.G.r + 1) * (2 * S.G.r + S.G.k + 1)) Θ ∧
        B.Commutes (T v).base (B.GPos (T v).base) Θ ∧
        ∀ (U : Set (Q.Mx S.G.k S.G.r)) (F : Q.Mx S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), IsOpen U →
          Q.SmoothLev S.G.k S.G.r 0 U F → ∀ g ∈ Q.Glev S.G.k S.G.r 0 ∩ U,
            B.opApply Θ F g = ε • rvhatOp S.G.k S.G.r (T v).base.z (T v).base.z' (y : ℂ) F g

private theorem isDom_OmP_levTower_base {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))) (v : Fin S.f) :
    Q.IsDom S.G.k S.G.r (T v).base.z (T v).base.z' 0 (OmP S T v) := by
  refine ⟨?_, ?_⟩
  · have hD : ∀ l, Continuous fun g : Matrix (Fin (2 * S.G.r + S.G.k + 1)) (Fin (2 * S.G.r + S.G.k + 1)) ℂ =>
        Formalism.QuantumDeterminants.Dmin S.G.k S.G.r (T v).base.z (T v).base.z' g l := by
      intro l
      unfold Formalism.QuantumDeterminants.Dmin Formalism.QuantumDeterminants.Zhat Formalism.QuantumDeterminants.herm
      simp only [Matrix.mulVec, dotProduct]
      fun_prop
    have hG : Continuous fun g : Matrix (Fin (2 * S.G.r + S.G.k + 1)) (Fin (2 * S.G.r + S.G.k + 1)) ℂ =>
        Formalism.QuantumDeterminants.Gf S.G.k S.G.r (T v).base.z (T v).base.z' g := by
      unfold Formalism.QuantumDeterminants.Gf
      exact (Complex.continuous_normSq.comp (hD _)).sub
        (continuous_const.mul (Complex.continuous_normSq.comp (hD _)))
    unfold OmP
    rw [Set.setOf_and, Set.setOf_forall]
    exact (isOpen_lt continuous_const hG).inter
      (isOpen_iInter_of_finite fun a => isOpen_ne_fun (hD _) continuous_const)
  · rintro g ⟨-, hgD⟩ s ⟨h, hh, m, hm, rfl⟩ s' ⟨h', hh', m', hm', rfl⟩
    have hs : h * m ∈ Formalism.QuantumDeterminants.Sset S.G.k S.G.r (T v).base.z := ⟨h, hh, m, hm.1, rfl⟩
    have hs' : h' * m' ∈ Formalism.QuantumDeterminants.Sset S.G.k S.G.r (T v).base.z' := ⟨h', hh', m', hm'.1, rfl⟩
    refine ⟨?_, fun a => ?_⟩
    · rw [Formalism.QuantumDeterminants.gInv _ _ _ _ (T v).base.z_mem (T v).base.z'_mem _ hs _ hs']
      exact hgD.1
    · rw [Formalism.QuantumDeterminants.dInv _ _ _ _ (T v).base.z_mem (T v).base.z'_mem _ hs _ hs']
      exact hgD.2 a

private theorem w1_mem_UH_Hpk_of_ne_zero {k r : ℕ} (l : Fin r) (x : ℂ) (hx : x ≠ 0) :
    Q.w1 k r l x ∈ Formalism.QuantumDeterminants.UH (Hpk k r) := by
  have hl := l.isLt
  have hes : eI k r l ≠ esI k r l := by
    simp only [eI, esI, ne_eq, Fin.ext_iff]
    omega
  have hcol : ∀ j q, Q.w1 k r l x j q =
      if j = (if q = eI k r l then esI k r l else if q = esI k r l then eI k r l else q) then
        (if q = eI k r l then x else if q = esI k r l then (star x)⁻¹ else 1) else 0 := by
    intro j q
    simp only [Q.w1]
    by_cases hq1 : q = eI k r l <;> by_cases hq2 : q = esI k r l <;>
      by_cases hj1 : j = eI k r l <;> by_cases hj2 : j = esI k r l <;> simp_all <;>
      (intro h; first | exact absurd h.symm hq1 | exact absurd h.symm hq2)
  have hHe : ∀ p, p ≠ esI k r l → Hpk k r p (eI k r l) = 0 := by
    intro p hp
    rw [Ne, Fin.ext_iff] at hp
    simp only [esI] at hp
    simp only [Hpk, eI, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)
  have hHs : ∀ p, p ≠ eI k r l → Hpk k r p (esI k r l) = 0 := by
    intro p hp
    rw [Ne, Fin.ext_iff] at hp
    simp only [eI] at hp
    simp only [Hpk, esI, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)
  have hHe' : ∀ q, q ≠ esI k r l → Hpk k r (eI k r l) q = 0 := by
    intro q hq
    rw [Ne, Fin.ext_iff] at hq
    simp only [esI] at hq
    simp only [Hpk, eI, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)
  have hHs' : ∀ q, q ≠ eI k r l → Hpk k r (esI k r l) q = 0 := by
    intro q hq
    rw [Ne, Fin.ext_iff] at hq
    simp only [eI] at hq
    simp only [Hpk, esI, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)
  have hHes : Hpk k r (eI k r l) (esI k r l) = 1 := by
    have h1 : (l : ℕ) + (2 * r + k - l) = 2 * r + k := by omega
    simp [Hpk, eI, esI, hl, h1]
  have hHse : Hpk k r (esI k r l) (eI k r l) = 1 := by
    have h2 : ¬ (2 * r + k - (l : ℕ) < r) := by omega
    have h3 : 2 * r + k - (l : ℕ) + l = 2 * r + k := by omega
    simp [Hpk, eI, esI, hl, h2, h3]
  show (Q.w1 k r l x)ᴴ * Hpk k r * Q.w1 k r l x = Hpk k r
  ext p q
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hcol, apply_ite star, star_zero, ite_mul, mul_ite,
    zero_mul, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  by_cases hp1 : p = eI k r l <;> by_cases hp2 : p = esI k r l <;>
    by_cases hq1 : q = eI k r l <;> by_cases hq2 : q = esI k r l <;>
    first
    | exact absurd (hp1.symm.trans hp2) hes
    | exact absurd (hq1.symm.trans hq2) hes
    | simp [hp1, hp2, hq1, hq2, hes, hes.symm, hHe, hHs, hHe', hHs', hHes, hHse, hx]

private theorem mul_mem_UH_of_mem_of_mem {n : ℕ} {H g h : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH H)
    (hh : h ∈ Formalism.QuantumDeterminants.UH H) : g * h ∈ Formalism.QuantumDeterminants.UH H := by
  have hg' : gᴴ * H * g = H := hg
  have hh' : hᴴ * H * h = H := hh
  show (g * h)ᴴ * H * (g * h) = H
  rw [Matrix.conjTranspose_mul,
    show hᴴ * gᴴ * H * (g * h) = hᴴ * (gᴴ * H * g) * h by simp only [Matrix.mul_assoc], hg', hh']

private theorem wCell_mem_UH_Hpk_of_ne_zero {k r : ℕ} (c : Fin r → ℂ) (hc : ∀ a, c a ≠ 0) (i : Fin (r + 1)) :
    Q.wCell k r i c ∈ Formalism.QuantumDeterminants.UH (Hpk k r) := by
  unfold Q.wCell
  induction ((List.finRange r).filter fun a => a.val < i.val) with
  | nil =>
    show (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ᴴ * Hpk k r * 1 = Hpk k r
    simp
  | cons a L ih =>
    rw [List.map_cons, List.prod_cons]
    exact mul_mem_UH_of_mem_of_mem (w1_mem_UH_Hpk_of_ne_zero a (c a) (hc a)) ih

private theorem wCell_last_mul_mem_Glev_zero {k r : ℕ} (c : Fin r → ℂ) (hc : c ∈ OmX r) (g : Q.Mx k r)
    (hg : g ∈ Q.Glev k r (Fin.last r)) : Q.wCell k r (Fin.last r) c * g ∈ Q.Glev k r 0 :=
  ⟨mul_mem_UH_of_mem_of_mem (wCell_mem_UH_Hpk_of_ne_zero c hc _) hg.1, fun a ha => absurd ha (by simp)⟩

theorem jDRGrpM_of_parts (hR : JDRRadM) (hI : JDRRealInvM) : JDRGrpM := by
  intro Cc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v y
  obtain ⟨ε, hε⟩ := hR S.G.k S.G.r
  obtain ⟨Θ, hP, hC, hA⟩ := hI ε Cc E Wp Wq S T f χ ν' m₀ top A₀ hB v y
  refine ⟨Θ, hP, hC, ?_⟩
  intro J hJ c hc g hg hx
  have key := hε (Wp (S.pl v)) (Wq (S.pl v)) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π'
    (OmP S T v) (y : ℂ) (T v).base.z_mem (T v).base.z'_mem (isDom_OmP_levTower_base S T v) J hJ c hc g hg hx
  rw [← key]
  have hx0 := wCell_last_mul_mem_Glev_zero c hc g hg
  obtain ⟨U, F, hU, hxU, hF, hFJ⟩ := hJ.1 _ ⟨hx0, hx⟩
  have hS : Q.SmoothLev S.G.k S.G.r 0 U J := fun g₀ hg₀ => ⟨U, F, hU, hg₀.2, hF, hFJ⟩
  have := hA U J hU hS _ ⟨hx0, hxU⟩
  simp only [Q.resG, this]

end

end Formalism.FourierDecayAlt.P.CutMP
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRRotCut
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

def zc (k r : ℕ) (φ : ℝ) : Q.Mx k r :=
  B2.embWb k r (Complex.exp ((φ : ℂ) * Complex.I) • (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ))

def dOne (k : ℕ) (φ : ℝ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  Matrix.diagonal fun j => if j = Fin.last k then 1 else Complex.exp ((φ : ℂ) * Complex.I)

def dTwo (k : ℕ) (φ : ℝ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  Matrix.diagonal fun j => if j = 0 then Complex.exp ((φ : ℂ) * Complex.I) else 1

def hL (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (φ : ℝ) : Q.Mx k r :=
  B2.embWb k r (TheSec.gA k (wbPart k r z) (Tz k r z) * dOne k φ * (TheSec.gA k (wbPart k r z) (Tz k r z))⁻¹)

def hR (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (φ : ℝ) : Q.Mx k r :=
  B2.embWb k r ((TheSec.gB k (wbPart k r z') (Tz k r z'))⁻¹ * dTwo k φ * TheSec.gB k (wbPart k r z') (Tz k r z'))

def rotM {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ)
    (π : Q.Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Q.Mx P.k P.r → (Wq →L[ℂ] Wq)) (E : M.Ty P → (Wq →L[ℂ] Wp))
    (φ : ℝ) (ρ ρ' : M.Ty P) : ℂ :=
  inner ℂ (B.hsVec (E ρ)) (B.hsVec ((π (hL P.k P.r z φ)).comp ((E ρ').comp (π' (hR P.k P.r z' φ)))))

def GTRRotK : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → Bs.μsec = TheSec.theSection P.k P.r Bs.z Bs.z' →
    ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e → (∀ ρ (ζ ζ' : ℂ), e ρ ζ = e ρ ζ') →
    ∀ (Rt : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) (s : ℤ),
      (∀ (f : M.Ty P → ℂ) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), Rt ((d.κ f).1 Φ) = (d.κ f).1 (Rt Φ)) →
      (∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), ∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z',
        (Rt Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
          (∑ a : Fin (Q.mdim P.k P.r (Fin.last P.r)),
            Q.EH P.k P.r (Q.posL P.k P.r (Fin.last P.r) a) (Q.posL P.k P.r (Fin.last P.r) a)
              ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1) x.2) +
            ((s : ℂ)) • (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2) →
      ∀ ρ : M.Ty P, ∃ m : ℤ, ∀ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
        trR P Bs e (Rt Φ) ρ = fnZ P (fun w => w) * dzQ P (trR P Bs e Φ ρ) -
          fnZ P (fun w => star w) * dzbQ P (trR P Bs e Φ ρ) + ((m : ℂ)) • trR P Bs e Φ ρ

def GTRRCentre : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
    [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq))
    (Φ : Q.RadSp k r z z' π π'), ∀ x ∈ Q.DomR k r z z',
      HasDerivAt (fun φ : ℝ => (Φ : Q.Fn k r (Wq →L[ℂ] Wp)) x.1 (x.2 * zc k r φ))
        (Complex.I • ∑ a : Fin (Q.mdim k r (Fin.last r)),
          Q.EH k r (Q.posL k r (Fin.last r) a) (Q.posL k r (Fin.last r) a) ((Φ : Q.Fn k r (Wq →L[ℂ] Wp)) x.1) x.2) 0

def GTRRSec : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' →
    (∀ φ : ℝ, hL k r z φ ∈ UWset k r z ∧ hR k r z' φ ∈ UWset k r z') ∧
    (hL k r z 0 = 1 ∧ hR k r z' 0 = 1 ∧ hL k r z (2 * Real.pi) = 1 ∧ hR k r z' (2 * Real.pi) = 1) ∧
    (∀ φ ψ : ℝ, hL k r z (φ + ψ) = hL k r z φ * hL k r z ψ ∧ hR k r z' (φ + ψ) = hR k r z' φ * hR k r z' ψ) ∧
    (∀ φ : ℝ, ∀ g ∈ UWset k r z', zc k r φ * g = g * zc k r φ) ∧
    ∀ ζ : ℂ, Tz k r z * Tz k r z' < Complex.normSq ζ → ∀ φ : ℝ,
      NF.muZ k r (TheSec.theSection k r z z') ζ * zc k r φ =
        hL k r z φ * NF.muZ k r (TheSec.theSection k r z z') (ζ * Complex.exp ((φ : ℂ) * Complex.I)) * hR k r z' φ ∧
      ∀ c : Fin r → ℂ, c ∈ OmX r → (c, NF.muZ k r (TheSec.theSection k r z z') ζ * zc k r φ) ∈ Q.DomR k r z z'

def GTRRODE : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Mf : ℝ → Matrix ι ι ℂ) (Bm : Matrix ι ι ℂ),
    Mf 0 = 1 → (∀ φ ψ : ℝ, Mf (φ + ψ) = Mf φ * Mf ψ) → Mf (2 * Real.pi) = 1 →
    (∀ i j, HasDerivAt (fun φ => Mf φ i j) (Bm i j) 0) → (∀ i j, i ≠ j → Bm i j = 0) →
    ∃ n : ι → ℤ, ∀ (φ : ℝ) (i j : ι), Mf φ i j = if i = j then Complex.exp ((n i : ℂ) * (φ : ℂ) * Complex.I) else 0

def GTRRWirt : Prop :=
  ∀ (r : ℕ) (u : MA.E r → ℂ) (x : MA.E r), DifferentiableAt ℝ u x →
    HasDerivAt (fun φ : ℝ => u (x.1, x.2 * Complex.exp ((φ : ℂ) * Complex.I)))
      (Complex.I * (x.2 * MA.wirt M.vz u x - star x.2 * MA.wirt M.vzb u x)) 0

def GTRRMat : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → Bs.μsec = TheSec.theSection P.k P.r Bs.z Bs.z' →
    ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e → (∀ ρ (ζ ζ' : ℂ), e ρ ζ = e ρ ζ') →
    ∀ (Rt : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) (s : ℤ),
      (∀ (f : M.Ty P → ℂ) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), Rt ((d.κ f).1 Φ) = (d.κ f).1 (Rt Φ)) →
      (∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), ∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z',
        (Rt Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
          (∑ a : Fin (Q.mdim P.k P.r (Fin.last P.r)),
            Q.EH P.k P.r (Q.posL P.k P.r (Fin.last P.r) a) (Q.posL P.k P.r (Fin.last P.r) a)
              ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1) x.2) +
            ((s : ℂ)) • (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2) →
      ∃ n : M.Ty P → ℤ, ∀ (φ : ℝ) (ρ ρ' : M.Ty P),
        rotM P Bs.z Bs.z' Bs.π Bs.π' (fun σ => e σ 0) φ ρ ρ' =
          if ρ = ρ' then Complex.exp ((n ρ : ℂ) * (φ : ℂ) * Complex.I) else 0

def GTRRMatFrom : Prop := GTRRCentre → GTRRSec → GTRRODE → GTRRMat

def GTRRFin : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → Bs.μsec = TheSec.theSection P.k P.r Bs.z Bs.z' →
    ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → (∀ ρ (ζ ζ' : ℂ), e ρ ζ = e ρ ζ') →
    ∀ n : M.Ty P → ℤ, (∀ (φ : ℝ) (ρ ρ' : M.Ty P),
        rotM P Bs.z Bs.z' Bs.π Bs.π' (fun σ => e σ 0) φ ρ ρ' =
          if ρ = ρ' then Complex.exp ((n ρ : ℂ) * (φ : ℂ) * Complex.I) else 0) →
    ∀ (Rt : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) (s : ℤ),
      (∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), ∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z',
        (Rt Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
          (∑ a : Fin (Q.mdim P.k P.r (Fin.last P.r)),
            Q.EH P.k P.r (Q.posL P.k P.r (Fin.last P.r) a) (Q.posL P.k P.r (Fin.last P.r) a)
              ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1) x.2) +
            ((s : ℂ)) • (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2) →
      ∀ (ρ : M.Ty P) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'),
        trR P Bs e (Rt Φ) ρ = fnZ P (fun w => w) * dzQ P (trR P Bs e Φ ρ) -
          fnZ P (fun w => star w) * dzbQ P (trR P Bs e Φ ρ) + (((n ρ + s : ℤ) : ℂ)) • trR P Bs e Φ ρ

def GTRRFinFrom : Prop := GTRRCentre → GTRRSec → GTRRWirt → GTRRFin

theorem gTRRotK_of_mat_fin_centre_sec_ode_wirt (hM : GTRRMatFrom) (hF : GTRRFinFrom) (hC : GTRRCentre) (hS : GTRRSec) (hO : GTRRODE)
    (hW : GTRRWirt) : GTRRotK := by
  unfold GTRRotK
  intro Wp Wq _ _ _ _ _ _ P Bs X d hyp hsec e he hk hc Rt s hRK hRt ρ
  obtain ⟨n, hn⟩ := hM hC hS hO Wp Wq P Bs X d hyp hsec e he hk hc Rt s hRK hRt
  exact ⟨n ρ + s, fun Φ => hF hC hS hW Wp Wq P Bs hyp.1 hyp.2.1 hsec e he hc n hn Rt s hRt ρ Φ⟩

theorem thetaNF_commute_kap (P : M.Par) {𝒜 : Type} [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] (d : Q.NFData P 𝒜)
    (hR : d.Rel) (f : M.Ty P → ℂ) : Commute (d.κ f) (ThetaNF P d) := by
  have hfn : ∀ g ∈ d.L.fns, Commute (d.κ f) g := fun g hg => hR.2.1 f g (Or.inl hg)
  have hz : Commute (d.κ f) d.L.ζ := hfn _ (by simp [R.LevelData.fns])
  have hzb : Commute (d.κ f) d.L.ζb := hfn _ (by simp [R.LevelData.fns])
  have hGi : Commute (d.κ f) d.L.GGi := hfn _ (by simp [R.LevelData.fns])
  have hn : Commute (d.κ f) d.L.nab := hR.2.1 f _ (Or.inr (by simp))
  have hns : Commute (d.κ f) d.L.nabs := hR.2.1 f _ (Or.inr (by simp))
  have hkk : ∀ g : M.Ty P → ℂ, Commute (d.κ f) (d.κ g) := fun g => by
    show d.κ f * d.κ g = d.κ g * d.κ f
    rw [← map_mul, ← map_mul, mul_comm]
  unfold ThetaNF
  exact (((hz.mul_right hn).add_right (hzb.mul_right hns)).add_right (hkk _)).add_right
    (((Algebra.commute_algebraMap_right _ _).mul_right hGi).mul_right (hkk _))

def GTCRefTraceOfCutK : Prop :=
  GTRMove → GTRConst → GTRTopNF → GTRTopAct → GTRRotK → GTRInt → GTRTrans → GTCReal → GTCRefTrace

theorem gTCRefTrace_of_cutK : GTCRefTraceOfCutK := by
  intro hMove hConst hNF hAct hRot hInt hTrans hReal
  unfold GTCRefTrace
  intro Wp Wq _ _ _ _ _ _ P Bs X d hyp
  obtain ⟨hpl, hk, hcs, hL, hS, hR, hQ⟩ := hyp
  have hcs0 := Formalism.FourierDecayAlt.P.TheSecStab.theSection_csec (k := P.k) (r := P.r) (by omega) Bs.z_mem Bs.z'_mem
    Bs.T_pos Bs.T'_pos
  set Bs0 := BsAt P Bs (TheSec.theSection P.k P.r Bs.z Bs.z') hcs0.1 with hBs0
  have hyp0 : GTHyp P Bs0 X d := ⟨hpl, hk, hcs0, hL, hS, hR, hQ⟩
  obtain ⟨e0, he0, hk0, hc0⟩ := hConst Wp Wq P Bs0 X d hyp0
  obtain ⟨A, B, hAB, hC⟩ := gauge_locality_holds Wp Wq P Bs0 X d hyp0 e0 he0 hk0

  obtain ⟨cA, hcA, sA, hsA⟩ := hAct Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hpl hk X
  have hTT : d.L.TT = ((P.TT : ℝ) : ℂ) := by
    rw [hL.2.2.2.2.2.2.2.2.2.2.2.2, hpl.2.2.2.1, hpl.2.2.2.2.1]
    rfl
  obtain ⟨cN, hcN, sN, hsN⟩ := hNF P _ d hpl.1 hk hS hR hTT
  have hcoef : ∀ Y : ℂ, ∑ j ∈ Finset.range (P.k + 2), Y ^ j • cA j =
      ∑ j ∈ Finset.range (P.k + 2), Y ^ j • (cN j).1 := by
    intro Y
    rw [← hcA Y]
    have h1 : X.t Y 0 0 = (X.QQ Y 0 0).1 := rfl
    rw [h1, hQ Y, hcN Y, pr_fst_sum]
    exact Finset.sum_congr rfl fun j _ => pr_fst_smul _ _
  have hk' := poly_coeff_eq (P.k + 2) cA (fun j => (cN j).1) hcoef P.k (by omega)
  have hTh : (ThetaNF P d).1 = cA P.k - ((sN : ℂ)) • (1 : Module.End ℂ _) := by
    rw [hk']
    show (ThetaNF P d).1 = (cN P.k).1 - _
    rw [hsN, pr_fst_add, pr_fst_smul, pr_fst_one, add_sub_cancel_right]
  have hpt : ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), ∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z',
      (((ThetaNF P d).1 Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
        (∑ a : Fin (Q.mdim P.k P.r (Fin.last P.r)),
          Q.EH P.k P.r (Q.posL P.k P.r (Fin.last P.r) a) (Q.posL P.k P.r (Fin.last P.r) a)
            ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1) x.2) +
          (((sA - sN : ℤ) : ℂ)) • (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 := by
    intro Φ x hx
    rw [hTh, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, Submodule.coe_sub,
      Submodule.coe_smul, Pi.sub_apply, Pi.smul_apply, Pi.sub_apply, Pi.smul_apply, hsA Φ x hx]
    push_cast
    rw [sub_smul]
    abel
  obtain ⟨e, he, htr⟩ := hMove Wp Wq P Bs hpl hk _ hcs0.1 e0 he0
  have htrF : trR P Bs e = trR P Bs0 e0 := funext htr
  refine ⟨e, he, ?_, A, B, hAB, ?_, fun ρ => ?_⟩
  · intro f Φ
    rw [htrF]
    exact hk0 f Φ
  · intro Φ ρ
    rw [htrF]
    exact hC Φ ρ
  · obtain ⟨m, hm⟩ := hRot Wp Wq P Bs0 X d hyp0 rfl e0 he0 hk0 hc0 (ThetaNF P d).1 (sA - sN)
      (fun f Φ =>
        (congrArg (fun x : Q.Pr (Q.RadSp P.k P.r Bs0.z Bs0.z' Bs0.π Bs0.π') => x.1 Φ)
          (thetaNF_commute_kap P d hR f).eq).symm) hpt ρ
    obtain ⟨N, hN⟩ := hInt Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hpl hk ρ
    refine ⟨N - m, fun ζ hζ => ?_⟩
    have hT := hTrans Wp Wq P Bs0 X d hyp0 e0 he0 hk0 A B hAB hC ρ (m : ℂ) hm ζ hζ
    rw [hReal Wp Wq P Bs0 X d hyp0 e0 he0 hk0 A B hAB hC ρ ζ hζ] at hT
    exact final_arith P ρ (A ρ ζ) ζ hζ m N hN hT

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.IntMulOfCpt
open MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerB

section Wirt

theorem dZ_eq (f : ℂ → ℂ) (c : ℂ) : NF.dZ f c = (1 / 2 : ℂ) * (fderiv ℝ f c 1 - Complex.I * fderiv ℝ f c Complex.I) := rfl

theorem dZ_conj {φ : ℂ → ℂ} {c : ℂ} (h : DifferentiableAt ℝ φ c) :
    NF.dZ (fun w => conj (φ w)) c = conj (NF.dZb φ c) := by
  have hd : HasFDerivAt (fun w => conj (φ w)) ((Complex.conjCLE.toContinuousLinearMap).comp (fderiv ℝ φ c)) c :=
    Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp c h.hasFDerivAt
  unfold NF.dZ NF.dZb
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, map_mul,
    map_add, map_sub, Complex.conj_I, map_div₀, map_one, map_ofNat]
  ring

end Wirt

section IBP

end IBP

section Cpt

end Cpt

end Formalism.FourierDecayAlt.P5.HerB
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.PtSizePtG
namespace Formalism.FourierDecayAlt.P.FormNormSumIdentities

open Formalism.FourierDecayAlt

noncomputable section

def ptG (h' : C.LPt) (m : ℕ) : (ℂ × ℂ) ⊕ ℂ → C.LPt
  | Sum.inl q => h' ++ [(m + 1, q.1), (1, q.2)]
  | Sum.inr z => h' ++ [(m + 2, z)]

def yG {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (β : ℂ) (m : ℕ) (Φ : G.Mat (m + 2) → V) :
    (ℂ × ℂ) ⊕ ℂ → V
  | Sum.inl q => ((kapB m : ℝ) : ℂ) • G.OmBlock β (m + 1) Φ q.1 q.2
  | Sum.inr z => ((Real.pi ^ ((m + 2) * (m + 1) / 2) : ℝ) : ℂ) • G.OmLong β (m + 1) Φ z

def okG (m : ℕ) (Kc : Set ℂ) : (ℂ × ℂ) ⊕ ℂ → Prop
  | Sum.inl q => q.1 ≠ 0 ∧ q.2 * q.1 ^ (m + 1) ∈ Kc
  | Sum.inr z => ∃ D ∈ Kc, z ^ (m + 2) = (-1) ^ (m + 3) * D

theorem ptSize_ptG (h' : C.LPt) (m : ℕ) (q : (ℂ × ℂ) ⊕ ℂ) : D.ptSize (ptG h' m q) = D.ptSize h' + (m + 2) := by
  cases q <;> simp [ptG, D.ptSize, List.map_append, List.sum_append] <;> omega

def GermPlace : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P0 : M.Par)
    (T : D.LevTower P0.k P0.r Wp Wq) (sg : ℂ) (w : List C.Letter) (f : B.Mat P0.k P0.r → (Wq →L[ℂ] Wp))
    (χ : ℝ → ℝ) (ε : ℝ) (h' : C.LPt) (m i : ℕ) (hi : i ≤ P0.r) (hsz : D.ptSize h' + (m + 2) = i),
    B.CkOn ⊤ (B.GV P0.k P0.r) f → (∃ R : ℝ, ∀ g ∈ B.GV P0.k P0.r, f g ≠ 0 → B.gN g ≤ R) → C6.IsCut0 χ →
    0 < ε → 2 ≤ P0.k → D.IsLocPt h' (D.ptSize h') →
    ∀ Kc : Set ℂ, IsCompact Kc → (0 : ℂ) ∉ Kc →
    ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : NormedSpace ℂ V) (_ : CompleteSpace V)
      (Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (Φ : G.Mat (m + 2) → V) (Cp Cst : ℝ),
      0 ≤ Cp ∧ (∀ u, (Bf u u).re ≤ (Cp * ‖u‖) ^ 2) ∧
      (∀ q1 q2, okG m Kc q1 → okG m Kc q2 →
        D.formLev T sg ⟨i, by omega⟩ w
          (KB.slv T (D.cutF T.base χ f ε) i hi w (ptG h' m q1) (by rw [ptSize_ptG, hsz]))
          (KB.slv T (D.cutF T.base χ f ε) i hi w (ptG h' m q2) (by rw [ptSize_ptG, hsz])) =
        Bf (yG U.betaU m Φ q1) (yG U.betaU m Φ q2)) ∧
      ∀ t D : ℂ, t ≠ 0 → D ∈ Kc →
        ‖U.uD U.betaU m (U.Mlev P0.k (P0.r - i)) Φ t D - U.aD U.betaU m (U.Mlev P0.k (P0.r - i)) Φ t D‖ ≤
          Cst * ‖t‖

end

end Formalism.FourierDecayAlt.P.FormNormSumIdentities
end
