module

public import Formalism.HermitianCurvature.HerGenC
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PhiBoundPartsOfRadicalParametrisation
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SignedCoordinateEqSignSmul

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.OneParameterDifferentiable
open MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P

theorem one_parameter_differentiable : Formalism.FourierDecayAlt.Qr.OneParamDiff := by
  intro W _ _ _ φ h0 hadd hc
  have hmul : ∀ s t, φ (s + t) = φ s * φ t := fun s t => hadd s t
  obtain ⟨δ, hδ, hball⟩ : ∃ δ > 0, ∀ s : ℝ, |s| < δ → ‖φ s - 1‖ < 1 / 2 := by
    obtain ⟨δ, hδ, H⟩ := Metric.continuous_iff.1 hc 0 (1 / 2) (by norm_num)
    refine ⟨δ, hδ, fun s hs => ?_⟩
    have := H s (by rwa [Real.dist_eq, sub_zero])
    rwa [dist_eq_norm, h0] at this
  set h : ℝ := δ / 2 with hh
  have hpos : 0 < h := by positivity
  have hint : ∀ a b : ℝ, IntervalIntegrable φ MeasureTheory.volume a b := fun a b => hc.intervalIntegrable a b
  set M : W →L[ℂ] W := ∫ s in (0 : ℝ)..h, φ s with hM
  have hbound : ‖M - h • (1 : W →L[ℂ] W)‖ ≤ 1 / 2 * |h - 0| := by
    have e : M - h • (1 : W →L[ℂ] W) = ∫ s in (0 : ℝ)..h, (φ s - 1) := by
      rw [intervalIntegral.integral_sub (hint 0 h) intervalIntegrable_const, intervalIntegral.integral_const,
        sub_zero]
    rw [e]
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro s hs
    rw [Set.uIoc_of_le hpos.le] at hs
    refine (hball s ?_).le
    rw [abs_lt]
    constructor <;> linarith [hs.1, hs.2]
  set tt : W →L[ℂ] W := 1 - h⁻¹ • M with htt
  have hnorm : ‖tt‖ < 1 := by
    have e : tt = h⁻¹ • (h • (1 : W →L[ℂ] W) - M) := by
      rw [htt, smul_sub, smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]
    rw [e, norm_smul, norm_sub_rev, Real.norm_eq_abs, abs_inv, abs_of_pos hpos]
    calc h⁻¹ * ‖M - h • (1 : W →L[ℂ] W)‖ ≤ h⁻¹ * (1 / 2 * |h - 0|) := by gcongr
      _ = 1 / 2 := by
        rw [sub_zero, abs_of_pos hpos, ← mul_assoc, mul_comm h⁻¹, mul_assoc, inv_mul_cancel₀ hpos.ne', mul_one]
      _ < 1 := by norm_num
  let u0 := Units.oneSub tt hnorm
  have hu0 : (u0 : W →L[ℂ] W) = h⁻¹ • M := by
    show 1 - tt = h⁻¹ • M
    rw [htt, sub_sub_cancel]
  set G : ℝ → W →L[ℂ] W := fun t => (∫ s in (0 : ℝ)..t + h, φ s) - ∫ s in (0 : ℝ)..t, φ s with hG
  have hφM : ∀ t, φ t * M = G t := by
    intro t
    have e1 := (ContinuousLinearMap.mul ℂ (W →L[ℂ] W) (φ t)).intervalIntegral_comp_comm (hint 0 h)
    simp only [ContinuousLinearMap.mul_apply'] at e1
    rw [hM, ← e1]
    simp only [hG]
    rw [intervalIntegral.integral_interval_sub_left (hint 0 (t + h)) (hint 0 t)]
    rw [show (fun s => φ t * φ s) = fun s => φ (t + s) from funext fun s => (hmul t s).symm,
      intervalIntegral.integral_comp_add_left φ t, add_zero]
  have hφ : φ = fun t => (h⁻¹ • G t) * (↑u0⁻¹ : W →L[ℂ] W) := by
    funext t
    rw [← hφM t, ← mul_smul_comm, ← hu0, Units.mul_inv_cancel_right]
  have hF : ∀ x, HasDerivAt (fun u => ∫ s in (0 : ℝ)..u, φ s) (φ x) x :=
    fun x => (hc.integral_hasStrictDerivAt 0 x).hasDerivAt
  refine ⟨(h⁻¹ • (φ h - 1)) * (↑u0⁻¹ : W →L[ℂ] W), fun t => ?_⟩
  have hGd : HasDerivAt G (φ (t + h) - φ t) t := ((hF (t + h)).comp_add_const t h).sub (hF t)
  let R : (W →L[ℂ] W) →L[ℝ] (W →L[ℂ] W) :=
    (((ContinuousLinearMap.mul ℂ (W →L[ℂ] W)).flip (↑u0⁻¹ : W →L[ℂ] W)).restrictScalars ℝ)
  have hd := R.hasFDerivAt.comp_hasDerivAt t (hGd.const_smul h⁻¹)
  have e : ∀ x, φ x = (⇑R ∘ (h⁻¹ • G)) x := by
    intro x
    rw [hφ]
    rfl
  have e2 : φ t ∘SL ((h⁻¹ • (φ h - 1)) * (↑u0⁻¹ : W →L[ℂ] W)) = R (h⁻¹ • (φ (t + h) - φ t)) := by
    show φ t * ((h⁻¹ • (φ h - 1)) * (↑u0⁻¹ : W →L[ℂ] W)) = (h⁻¹ • (φ (t + h) - φ t)) * (↑u0⁻¹ : W →L[ℂ] W)
    rw [hmul t h, show φ t * φ h - φ t = φ t * (φ h - 1) by rw [mul_sub, mul_one], ← mul_smul_comm, mul_assoc]
  rw [e2]
  exact hd.congr_of_eventuallyEq (Filter.Eventually.of_forall e)

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.DerivativeRulesA1
open Matrix Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma one_le_gN {g : Mat k r} (hg : g ∈ GV k r) : 1 ≤ gN g := (Formalism.FourierDecayAlt.P.norm_of_inverse k r g hg).2

lemma gN_pos {g : Mat k r} (hg : g ∈ GV k r) : 0 < gN g := lt_of_lt_of_le one_pos (one_le_gN hg)

lemma top_ge_nat (m : ℕ) : (((m : ℕ) : ℕ∞) : WithTop ℕ∞) ≤ (((⊤ : ℕ∞)) : WithTop ℕ∞) :=
  WithTop.coe_le_coe.2 le_top

lemma ckOn_top_nat {f : Mat k r → E} (hf : CkOn (⊤ : ℕ∞) (GV k r) f) (m : ℕ) :
    CkOn ((m : ℕ) : ℕ∞) (GV k r) f := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hc, hff⟩ := hf g₀ hg₀
  exact ⟨U, f', hU, hgU, hc.of_le (top_ge_nat m), hff⟩

lemma top_ne_zero' : (((⊤ : ℕ∞)) : WithTop ℕ∞) ≠ 0 := by simp

lemma top_succ_le : (((⊤ : ℕ∞)) : WithTop ℕ∞) + 1 ≤ (((⊤ : ℕ∞)) : WithTop ℕ∞) := by
  exact_mod_cast (le_top : ((⊤ : ℕ∞) + 1 : ℕ∞) ≤ ⊤)

lemma ckOn_op_top {f : Mat k r → E} {X : Mat k r} (b : Bool) (hf : CkOn (⊤ : ℕ∞) (GV k r) f)
    (hX : inLie k r X) : CkOn (⊤ : ℕ∞) (GV k r) (op b X f) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hc, hff⟩ := hf g₀ hg₀
  refine ⟨U, op' b X f', hU, hgU, ?_, ?_⟩
  · exact (hc.fderiv_of_isOpen hU top_succ_le).clm_apply (vf b X).contDiff.contDiffOn
  · intro g hg hgG
    have hd : DifferentiableAt ℝ f' g :=
      (hc.differentiableOn top_ne_zero').differentiableAt (hU.mem_nhds hg)
    exact (hasDerivAt_ext b hU hg hgG hd hff hX).deriv

lemma chart_rho {g0 x : Mat k r} (hg0 : g0 ∈ GV k r) (hx : x ∈ Sr g0) (hxG : x ∈ GV k r) :
    chart g0 (rho g0 x) = x := by
  have hgu : IsUnit g0.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hg0
  have hh : x * g0⁻¹ ∈ GV k r := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul hxG (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_inv hg0)
  obtain ⟨hl, -, hk⟩ := iot_facts hh hx
  show kap (prj (Mv (co (iot (x * g0⁻¹))))) * g0 = x
  rw [Mv_co, prj_of_lie hl, hk, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hgu, Matrix.mul_one]

lemma rho_self {g0 : Mat k r} (hg0 : g0 ∈ GV k r) : rho g0 g0 = 0 := by
  have hgu : IsUnit g0.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hg0
  have hg1 : g0 * g0⁻¹ = 1 := Matrix.mul_nonsing_inv _ hgu
  funext i
  simp only [Ux10.rho, hg1, iot, sub_self, Matrix.zero_mul]
  exact co_zero i

lemma self_mem_Sr {g0 : Mat k r} (hg0 : g0 ∈ GV k r) : g0 ∈ Sr g0 := by
  have hgu : IsUnit g0.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hg0
  have hg1 : g0 * g0⁻¹ = 1 := Matrix.mul_nonsing_inv _ hgu
  have h2 : (1 + 1 : Mat k r) = (2 : ℂ) • (1 : Mat k r) := by rw [two_smul]
  show IsUnit (g0 * g0⁻¹ + 1).det
  rw [hg1, h2, Matrix.det_smul, Matrix.det_one, mul_one]
  exact (isUnit_iff_ne_zero.2 two_ne_zero).pow _

lemma chart_comp_cd {F : Mat k r → E} {g0 : Mat k r} (hg0 : g0 ∈ GV k r) (m : ℕ)
    (hF : CkOn ((m : ℕ) : ℕ∞) (GV k r) F) :
    ContDiffOn ℝ ((m : ℕ) : WithTop ℕ∞) (fun Y => F (chart g0 Y)) (Dom k r) := by
  intro Y hY
  apply ContDiffAt.contDiffWithinAt
  obtain ⟨U, f', hU, hcU, hcd, hff⟩ := hF _ (chart_mem hg0 hY)
  have hchc : ContinuousAt (chart g0) Y := (chart_diff g0 hY).continuousAt
  have h1 : ContDiffAt ℝ ((m : ℕ) : WithTop ℕ∞) (fun Y' => f' (chart g0 Y')) Y :=
    (hcd.contDiffAt (hU.mem_nhds hcU)).comp Y
      (((chart_cd g0).contDiffAt (dom_open.mem_nhds hY)).of_le (top_ge_nat m))
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [hchc.preimage_mem_nhds (hU.mem_nhds hcU), dom_open.mem_nhds hY] with Y' h1 h2
  exact hff _ h1 (chart_mem hg0 h2)

theorem ckOn_top_of_all {F : Mat k r → E} (hF : ∀ m : ℕ, CkOn ((m : ℕ) : ℕ∞) (GV k r) F) :
    CkOn (⊤ : ℕ∞) (GV k r) F := by
  intro g0 hg0
  have hAL : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun Y => F (chart g0 Y)) (Dom k r) :=
    contDiffOn_infty.2 fun m => chart_comp_cd hg0 m (hF m)
  set U := Sr g0 ∩ rho g0 ⁻¹' Dom k r with hUdef
  have hUo : IsOpen U := (rho_cd g0).continuousOn.isOpen_inter_preimage (sr_open g0) dom_open
  have hg0U : g0 ∈ U := ⟨self_mem_Sr hg0, by show rho g0 g0 ∈ Dom k r; rw [rho_self hg0]; exact zero_mem_dom⟩
  refine ⟨U, fun x => F (chart g0 (rho g0 x)), hUo, hg0U, ?_, ?_⟩
  · exact hAL.comp ((rho_cd g0).mono Set.inter_subset_left) (fun x hx => hx.2)
  · intro x hx hxG
    show F x = F (chart g0 (rho g0 x))
    rw [chart_rho hg0 hx.1 hxG]

end Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic

namespace Formalism.FourierDecayAlt.P

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.SumPairAtStarMul
open MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

section Gen

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]

theorem form_last (μ : Measure (Mt k r)) (x y : Ix S → RadSp k r z z' π π') (c : Fin r → ℂ) :
    form μ (Fin.last r) x y c = ∑ a, pairAt μ (x a) (y a) c := by
  have : IsEmpty {l : Fin r // (Fin.last r).val ≤ l.val} := ⟨fun l => absurd l.2 (not_le.mpr l.1.isLt)⟩
  have hg : ∀ c' : Cf r (Fin.last r), glue (Fin.last r) c c' = c :=
    fun c' => funext fun l => dif_neg (not_le.mpr l.isLt)
  have hp : ∀ c' : Cf r (Fin.last r), ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) = 1 := fun c' => by
    rw [Fintype.prod_empty, Complex.ofReal_one]
  have h1 : (volume : Measure (Cf r (Fin.last r))) Set.univ = 1 := by
    rw [MeasureTheory.volume_pi, Measure.pi_univ, Fintype.prod_empty]
  unfold form
  simp only [hg, hp, one_mul]
  rw [integral_const]
  simp [measureReal_def, h1]

def IntOn (μ : Measure (Mt k r)) (U : Submodule ℂ (RadSp k r z z' π π')) : Prop :=
  ∀ c ∈ OmX r, ∀ Φ ∈ U, ∀ Ψ ∈ U, Integrable (fun g : Mt k r =>
    B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))) μ

def AdjOn (μ : Measure (Mt k r)) (U : Submodule ℂ (RadSp k r z z' π π')) (a : Pr (RadSp k r z z' π π')) : Prop :=
  (∀ Φ ∈ U, a.1 Φ ∈ U) ∧ (∀ Φ ∈ U, a.2.unop Φ ∈ U) ∧
    ∀ c ∈ OmX r, ∀ Φ ∈ U, ∀ Ψ ∈ U, pairAt μ (a.1 Φ) Ψ c = pairAt μ Φ (a.2.unop Ψ) c

theorem hsInner_swap (A C : Wq →L[ℂ] Wp) : B.hsInner C A = conj (B.hsInner A C) := by
  simp only [B.hsInner]
  rw [inner_conj_symm]

private theorem hsVec_zero_hermitian_curvature : B.hsVec (0 : Wq →L[ℂ] Wp) = 0 := by
  ext i
  simp [B.hsVec]

theorem hsInner_zero_left (C : Wq →L[ℂ] Wp) : B.hsInner 0 C = 0 := by
  simp only [B.hsInner, hsVec_zero_hermitian_curvature, inner_zero_right]

private theorem hsVec_smul_hermitian_curvature' (a : ℂ) (A : Wq →L[ℂ] Wp) : B.hsVec (a • A) = a • B.hsVec A := by
  ext i
  simp [B.hsVec]

theorem hsInner_smul_left' (A C : Wq →L[ℂ] Wp) (a : ℂ) : B.hsInner (a • A) C = a * B.hsInner A C := by
  simp only [B.hsInner, hsVec_smul_hermitian_curvature', inner_smul_right]

theorem hsInner_smul_right' (A C : Wq →L[ℂ] Wp) (a : ℂ) : B.hsInner A (a • C) = conj a * B.hsInner A C := by
  simp only [B.hsInner, hsVec_smul_hermitian_curvature', inner_smul_left]

theorem pairAt_swap (μ : Measure (Mt k r)) (Φ Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) :
    pairAt μ Ψ Φ c = conj (pairAt μ Φ Ψ c) := by
  simp only [pairAt]
  rw [← integral_conj]
  congr 1
  funext g
  exact hsInner_swap _ _

theorem pairAt_smul_left (μ : Measure (Mt k r)) (Φ Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) (a : ℂ) :
    pairAt μ (a • Φ) Ψ c = a * pairAt μ Φ Ψ c := by
  simp only [pairAt, Submodule.coe_smul, Pi.smul_apply, hsInner_smul_left']
  exact integral_const_mul a _

theorem pairAt_smul_right (μ : Measure (Mt k r)) (Φ Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) (a : ℂ) :
    pairAt μ Φ (a • Ψ) c = conj a * pairAt μ Φ Ψ c := by
  simp only [pairAt, Submodule.coe_smul, Pi.smul_apply, hsInner_smul_right']
  exact integral_const_mul _ _

variable {μ : Measure (Mt k r)} {U : Submodule ℂ (RadSp k r z z' π π')}

private theorem hsInner_add_left' (A A' C : Wq →L[ℂ] Wp) :
    B.hsInner (A + A') C = B.hsInner A C + B.hsInner A' C := by
  have h : B.hsVec (A + A') = B.hsVec A + B.hsVec A' := by
    ext i
    simp [B.hsVec]
  simp only [B.hsInner, h, inner_add_right]

theorem pairAt_add_left (hU : IntOn μ U) {c : Fin r → ℂ} (hc : c ∈ OmX r) {Φ Φ' Ψ : RadSp k r z z' π π'}
    (hΦ : Φ ∈ U) (hΦ' : Φ' ∈ U) (hΨ : Ψ ∈ U) :
    pairAt μ (Φ + Φ') Ψ c = pairAt μ Φ Ψ c + pairAt μ Φ' Ψ c := by
  simp only [pairAt, Submodule.coe_add, Pi.add_apply, hsInner_add_left']
  exact integral_add (hU c hc Φ hΦ Ψ hΨ) (hU c hc Φ' hΦ' Ψ hΨ)

private theorem hsInner_add_right' (A C C' : Wq →L[ℂ] Wp) :
    B.hsInner A (C + C') = B.hsInner A C + B.hsInner A C' := by
  have h : B.hsVec (C + C') = B.hsVec C + B.hsVec C' := by
    ext i
    simp [B.hsVec]
  simp only [B.hsInner, h, inner_add_left]

theorem pairAt_add_right (hU : IntOn μ U) {c : Fin r → ℂ} (hc : c ∈ OmX r) {Φ Ψ Ψ' : RadSp k r z z' π π'}
    (hΦ : Φ ∈ U) (hΨ : Ψ ∈ U) (hΨ' : Ψ' ∈ U) :
    pairAt μ Φ (Ψ + Ψ') c = pairAt μ Φ Ψ c + pairAt μ Φ Ψ' c := by
  simp only [pairAt, Submodule.coe_add, Pi.add_apply, hsInner_add_right']
  exact integral_add (hU c hc Φ hΦ Ψ hΨ) (hU c hc Φ hΦ Ψ' hΨ')

private theorem pairAt_zero_left' (Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) : pairAt μ 0 Ψ c = 0 := by
  simp only [pairAt, Submodule.coe_zero, Pi.zero_apply, hsInner_zero_left, integral_zero]

theorem pairAt_sum_left (hU : IntOn μ U) {c : Fin r → ℂ} (hc : c ∈ OmX r) {ι : Type} (s : Finset ι)
    (Φ : ι → RadSp k r z z' π π') (hΦ : ∀ i, Φ i ∈ U) {Ψ : RadSp k r z z' π π'} (hΨ : Ψ ∈ U) :
    pairAt μ (∑ i ∈ s, Φ i) Ψ c = ∑ i ∈ s, pairAt μ (Φ i) Ψ c := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, pairAt_zero_left']
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj,
      pairAt_add_left hU hc (hΦ j) (U.sum_mem fun i _ => hΦ i) hΨ, ih]

private theorem pairAt_zero_right' (Φ : RadSp k r z z' π π') (c : Fin r → ℂ) : pairAt μ Φ 0 c = 0 := by
  rw [pairAt_swap, pairAt_zero_left', map_zero]

theorem pairAt_sum_right (hU : IntOn μ U) {c : Fin r → ℂ} (hc : c ∈ OmX r) {ι : Type} (s : Finset ι)
    {Φ : RadSp k r z z' π π'} (hΦ : Φ ∈ U) (Ψ : ι → RadSp k r z z' π π') (hΨ : ∀ i, Ψ i ∈ U) :
    pairAt μ Φ (∑ i ∈ s, Ψ i) c = ∑ i ∈ s, pairAt μ Φ (Ψ i) c := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, pairAt_zero_right']
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj,
      pairAt_add_right hU hc hΦ (hΨ j) (U.sum_mem fun i _ => hΨ i), ih]

theorem pr_alg_fst (a : ℂ) : (algebraMap ℂ (Pr (RadSp k r z z' π π')) a).1 = algebraMap ℂ _ a := rfl

theorem pr_alg_snd (a : ℂ) : (algebraMap ℂ (Pr (RadSp k r z z' π π')) a).2.unop = algebraMap ℂ _ (conj a) := rfl

def adjAlg (μ : Measure (Mt k r)) (U : Submodule ℂ (RadSp k r z z' π π')) (hU : IntOn μ U) :
    StarSubalgebra ℂ (Pr (RadSp k r z z' π π')) where
  carrier := {a | AdjOn μ U a}
  mul_mem' := by
    rintro a b ⟨ha1, ha2, ha⟩ ⟨hb1, hb2, hb⟩
    refine ⟨fun Φ hΦ => ha1 _ (hb1 Φ hΦ), fun Φ hΦ => hb2 _ (ha2 Φ hΦ), fun c hc Φ hΦ Ψ hΨ => ?_⟩
    change pairAt μ (a.1 (b.1 Φ)) Ψ c = pairAt μ Φ (b.2.unop (a.2.unop Ψ)) c
    rw [ha c hc _ (hb1 Φ hΦ) Ψ hΨ, hb c hc Φ hΦ _ (ha2 Ψ hΨ)]
  add_mem' := by
    rintro a b ⟨ha1, ha2, ha⟩ ⟨hb1, hb2, hb⟩
    refine ⟨fun Φ hΦ => U.add_mem (ha1 Φ hΦ) (hb1 Φ hΦ), fun Φ hΦ => U.add_mem (ha2 Φ hΦ) (hb2 Φ hΦ),
      fun c hc Φ hΦ Ψ hΨ => ?_⟩
    change pairAt μ (a.1 Φ + b.1 Φ) Ψ c = pairAt μ Φ (a.2.unop Ψ + b.2.unop Ψ) c
    rw [pairAt_add_left hU hc (ha1 Φ hΦ) (hb1 Φ hΦ) hΨ, pairAt_add_right hU hc hΦ (ha2 Ψ hΨ) (hb2 Ψ hΨ),
      ha c hc Φ hΦ Ψ hΨ, hb c hc Φ hΦ Ψ hΨ]
  algebraMap_mem' := by
    intro a
    refine ⟨fun Φ hΦ => ?_, fun Φ hΦ => ?_, fun c hc Φ hΦ Ψ hΨ => ?_⟩
    · rw [pr_alg_fst, Module.algebraMap_end_apply]; exact U.smul_mem a hΦ
    · rw [pr_alg_snd, Module.algebraMap_end_apply]; exact U.smul_mem _ hΦ
    · rw [pr_alg_fst, pr_alg_snd, Module.algebraMap_end_apply, Module.algebraMap_end_apply, pairAt_smul_left,
        pairAt_smul_right, Complex.conj_conj]
  star_mem' := by
    rintro a ⟨ha1, ha2, ha⟩
    refine ⟨ha2, ha1, fun c hc Φ hΦ Ψ hΨ => ?_⟩
    change pairAt μ (a.2.unop Φ) Ψ c = pairAt μ Φ (a.1 Ψ) c
    rw [pairAt_swap μ Ψ, ← ha c hc Ψ hΨ Φ hΦ, ← pairAt_swap]

theorem mem_adjAlg {hU : IntOn μ U} {a : Pr (RadSp k r z z' π π')} : a ∈ adjAlg μ U hU ↔ AdjOn μ U a := by
  exact Iff.rfl

theorem pairAt_snd_left {hU : IntOn μ U} {a : Pr (RadSp k r z z' π π')} (ha : a ∈ adjAlg μ U hU) {c : Fin r → ℂ}
    (hc : c ∈ OmX r) {Φ Ψ : RadSp k r z z' π π'} (hΦ : Φ ∈ U) (hΨ : Ψ ∈ U) :
    pairAt μ (a.2.unop Φ) Ψ c = pairAt μ Φ (a.1 Ψ) c := by
  have h := (mem_adjAlg.mp ha).2.2 c hc Ψ hΨ Φ hΦ
  rw [pairAt_swap μ Ψ (a.2.unop Φ) c, ← h]
  exact (pairAt_swap μ (a.1 Ψ) Φ c).symm

theorem act_mem {hU : IntOn μ U} (M : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) (hM : ∀ a b, M a b ∈ adjAlg μ U hU)
    (x : Ix S → RadSp k r z z' π π') (hx : ∀ a, x a ∈ U) (a : Ix S) : act M x a ∈ U := by
  show (∑ b, (M a b).1 (x b)) ∈ U
  exact U.sum_mem fun b _ => (mem_adjAlg.mp (hM a b)).1 _ (hx b)

theorem mul_mem_entries {hU : IntOn μ U} (M N : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) (hM : ∀ a b, M a b ∈ adjAlg μ U hU)
    (hN : ∀ a b, N a b ∈ adjAlg μ U hU) (a b : Ix S) : (M * N) a b ∈ adjAlg μ U hU := by
  rw [Matrix.mul_apply]
  exact sum_mem fun e _ => (adjAlg μ U hU).mul_mem (hM a e) (hN e b)

theorem sum_pairAt_star_mul {hU : IntOn μ U} (M N : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π')))
    (hM : ∀ a b, M a b ∈ adjAlg μ U hU) (hN : ∀ a b, N a b ∈ adjAlg μ U hU)
    (x y : Ix S → RadSp k r z z' π π') (hx : ∀ a, x a ∈ U) (hy : ∀ a, y a ∈ U) {c : Fin r → ℂ} (hc : c ∈ OmX r) :
    ∑ a, pairAt μ (act (star M * N) x a) (y a) c = ∑ e, pairAt μ (act N x e) (act M y e) c := by
  have hu : ∀ e, act N x e ∈ U := act_mem N hN x hx
  have hL : ∀ a, act (star M * N) x a = ∑ e, (M e a).2.unop (act N x e) := by
    intro a
    rw [act_mul]
    rfl
  calc ∑ a, pairAt μ (act (star M * N) x a) (y a) c
      = ∑ a, ∑ e, pairAt μ (act N x e) ((M e a).1 (y a)) c := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hL a, pairAt_sum_left hU hc _ _ (fun e => (mem_adjAlg.mp (hM e a)).2.1 _ (hu e)) (hy a)]
        exact Finset.sum_congr rfl fun e _ => pairAt_snd_left (hM e a) hc (hu e) (hy a)
    _ = ∑ e, ∑ a, pairAt μ (act N x e) ((M e a).1 (y a)) c := Finset.sum_comm
    _ = ∑ e, pairAt μ (act N x e) (act M y e) c := by
        refine Finset.sum_congr rfl fun e _ => ?_
        exact (pairAt_sum_right hU hc _ (hu e) _ (fun a => (mem_adjAlg.mp (hM e a)).1 _ (hy a))).symm

end Gen

section Top

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

theorem adjTop_of_adjAlg (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π')))
    (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')) (l0 : ℕ)
    (U : Submodule ℂ (RadSp P.k P.r z z' π π')) (hU : IntOn μ U) (hK : K (Fin.last P.r) ≤ U)
    (hF : ∀ w : List (Letter ℂ S), WordOK P z z' π π' st l0 w → ∀ e e',
      (Fr.ofWord L st w).F e e' ∈ adjAlg μ U hU ∧ (Fr.ofWord L st w).d L e e' ∈ adjAlg μ U hU) :
    AdjTop (S := S) P z z' π π' μ L st K l0 := by
  intro w hw x y hx hy c hc
  have hFF : ∀ e e', (Fr.ofWord L st w).F e e' ∈ adjAlg μ U hU := fun e e' => (hF w hw e e').1
  have hFd : ∀ e e', (Fr.ofWord L st w).d L e e' ∈ adjAlg μ U hU := fun e e' => (hF w hw e e').2
  have hxU : ∀ a, x a ∈ U := fun a => hK (hx a)
  have hyU : ∀ a, y a ∈ U := fun a => hK (hy a)
  have hDF := mul_mem_entries _ _ hFd hFF
  have hu := act_mem _ hDF x hxU
  have hv := act_mem _ hFF y hyU
  have hint := fun e => hU c hc _ (hu e) _ (hv e)
  refine ⟨?_, ?_⟩
  · simp only [topDens]
    exact integrable_finsetSum Finset.univ fun e _ => hint e
  · rw [form_last, mul_assoc, sum_pairAt_star_mul _ _ hFF hDF x y hxU hyU hc]
    simp only [topDens]
    rw [integral_finsetSum Finset.univ fun e _ => hint e]
    rfl

end Top

end Formalism.FourierDecayAlt.P5.HerA
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelIntegrandAestronglyMeasurable
open MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd

section Split

variable {r : ℕ}

def coordinateRestEquiv (l : Fin r) :
    {j : {j : Fin r // l.castSucc.val ≤ j.val} // ¬ (j.1 = l)} ≃ {j : Fin r // l.succ.val ≤ j.val} where
  toFun j := ⟨j.1.1, by
    have h1 := j.1.2; have h2 := j.2
    simp only [Fin.coe_castSucc, Fin.val_succ] at h1 ⊢
    rcases Nat.lt_or_ge l.val j.1.1.val with h | h
    · omega
    · exact absurd (Fin.ext (by omega)) h2⟩
  invFun j := ⟨⟨j.1, by have := j.2; simp only [Fin.coe_castSucc, Fin.val_succ] at *; omega⟩, by
    intro h; have := j.2; rw [h] at this; simp at this⟩
  left_inv j := rfl
  right_inv j := rfl

instance uniqueCoordinateAtLevel (l : Fin r) : Unique {j : {j : Fin r // l.castSucc.val ≤ j.val} // j.1 = l} where
  default := ⟨⟨l, by simp⟩, rfl⟩
  uniq j := Subtype.ext (Subtype.ext j.2)

def coordinateSplit (l : Fin r) : Cf r l.castSucc ≃ᵐ ℂ × Cf r l.succ :=
  (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : {j : Fin r // l.castSucc.val ≤ j.val} => ℂ)
      (fun j => j.1 = l)).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.piUnique _)
      (MeasurableEquiv.piCongrLeft (fun _ => ℂ) (coordinateRestEquiv l)))

theorem coordinate_split_measurePreserving (l : Fin r) : MeasurePreserving (coordinateSplit l) volume volume := by
  unfold coordinateSplit
  refine MeasurePreserving.trans (volume_preserving_piEquivPiSubtypeProd _ _) ?_
  exact MeasurePreserving.prod (measurePreserving_piUnique _)
    (volume_measurePreserving_piCongrLeft (fun _ => ℂ) (coordinateRestEquiv l))

theorem coordinate_split_fst (l : Fin r) (a : Cf r l.castSucc) : (coordinateSplit l a).1 = a ⟨l, by simp⟩ := by
  rfl

theorem coordinate_split_snd (l : Fin r) (a : Cf r l.castSucc) (j : {j : Fin r // l.succ.val ≤ j.val}) :
    (coordinateSplit l a).2 j = a ⟨j.1, by have := j.2; simp only [Fin.coe_castSucc, Fin.val_succ] at *; omega⟩ := by
  rfl

theorem glue_coordinate_split (l : Fin r) (c : Fin r → ℂ) (a : Cf r l.castSucc) :
    glue l.castSucc c a = glue l.succ (Function.update c l (coordinateSplit l a).1) (coordinateSplit l a).2 := by
  funext j
  rw [coordinate_split_fst]
  unfold glue
  rcases lt_trichotomy j.val l.val with h | h | h
  · have h1 : ¬ (l.castSucc.val ≤ j.val) := by simp only [Fin.val_castSucc]; omega
    have h2 : ¬ (l.succ.val ≤ j.val) := by simp only [Fin.val_succ]; omega
    have h3 : j ≠ l := fun e => by rw [e] at h; omega
    rw [dif_neg h1, dif_neg h2, Function.update_of_ne h3]
  · have hj : j = l := Fin.ext h
    subst hj
    have h2 : ¬ (j.succ.val ≤ j.val) := by simp
    rw [dif_pos (by simp), dif_neg h2, Function.update_self]
  · have h1 : l.castSucc.val ≤ j.val := by simp only [Fin.val_castSucc]; omega
    have h2 : l.succ.val ≤ j.val := by simp only [Fin.val_succ]; omega
    rw [dif_pos h1, dif_pos h2, coordinate_split_snd]

theorem weight_coordinate_split (l : Fin r) (a : Cf r l.castSucc) :
    (∏ j, ‖a j‖ ^ (-2 : ℤ)) = ‖(coordinateSplit l a).1‖ ^ (-2 : ℤ) * ∏ j, ‖(coordinateSplit l a).2 j‖ ^ (-2 : ℤ) := by
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun j : {j : Fin r // l.castSucc.val ≤ j.val} => j.1 = l)]
  congr 1
  · rw [Fintype.prod_unique, coordinate_split_fst]; rfl
  · rw [← (coordinateRestEquiv l).prod_comp]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [coordinate_split_snd]; rfl

def coordinateExtension (i : Fin (r + 1)) (c : Fin r → ℂ) (a : Cf r i) : Cf r 0 := fun j => glue i c a j.1

theorem coordinate_extension_glue (i : Fin (r + 1)) (c : Fin r → ℂ) (a : Cf r i) : glue 0 c (coordinateExtension i c a) = glue i c a := by
  funext j
  simp [glue, coordinateExtension]

theorem coordinate_extension_measurable (i : Fin (r + 1)) (c : Fin r → ℂ) : Measurable (coordinateExtension i c) := by
  refine Measurable.of_eval fun j => ?_
  by_cases h : i.val ≤ j.1.val
  · simp only [coordinateExtension, glue, dif_pos h]; exact measurable_pi_apply _
  · simp only [coordinateExtension, glue, dif_neg h]; exact measurable_const

theorem level_weight_measurable {β : Type} [MeasurableSpace β] (i : Fin (r + 1)) :
    Measurable (fun q : Cf r i × β => ((∏ l, ‖q.1 l‖ ^ (-2 : ℤ) : ℝ) : ℂ)) := by
  fun_prop

end Split

section Top

variable {r : ℕ}

instance isEmptyCoordinatesFromLastLevel : IsEmpty {l : Fin r // (Fin.last r).val ≤ l.val} :=
  ⟨fun j => by have h1 := j.2; have h2 := j.1.isLt; simp only [Fin.val_last] at h1; omega⟩

def lastLevelPoint (r : ℕ) : Cf r (Fin.last r) := isEmptyElim

theorem integral_top_level_point {β E : Type} [MeasurableSpace β] [NormedAddCommGroup E] [NormedSpace ℝ E] (ν : Measure β) [SFinite ν]
    (f : Cf r (Fin.last r) × β → E) :
    (Integrable f (volume.prod ν) ↔ Integrable (fun g => f (lastLevelPoint r, g)) ν) ∧
      ∫ q, f q ∂(volume.prod ν) = ∫ g, f (lastLevelPoint r, g) ∂ν := by
  have hv : (volume : Measure (Cf r (Fin.last r))) = Measure.dirac (lastLevelPoint r) := by
    rw [volume_pi]; exact Measure.pi_of_empty _ _
  rw [hv, Measure.dirac_prod]
  exact ⟨(measurableEmbedding_prodMk_left _).integrable_map_iff,
    (measurableEmbedding_prodMk_left _).integral_map _⟩

theorem glue_last_level (c : Fin r → ℂ) (a : Cf r (Fin.last r)) : glue (Fin.last r) c a = c := by
  funext j; have := j.isLt; simp only [glue, Fin.val_last]; rw [dif_neg (by omega)]

end Top

section Dens

theorem sesquilinear_polarization {V : Type} [AddCommGroup V] [Module ℂ V] (β : V → V → ℂ)
    (hl : ∀ (x x' y : V) (a : ℂ), β (x + a • x') y = β x y + a * β x' y)
    (hr : ∀ (x y y' : V) (a : ℂ), β x (y + a • y') = β x y + conj a * β x y') (x y : V) :
    4 * β x y = β (x + (1 : ℂ) • y) (x + (1 : ℂ) • y) + Complex.I * β (x + Complex.I • y) (x + Complex.I • y)
      - β (x + (-1 : ℂ) • y) (x + (-1 : ℂ) • y) - Complex.I * β (x + (-Complex.I) • y) (x + (-Complex.I) • y) := by
  simp only [hl, hr, map_one, map_neg, Complex.conj_I, neg_neg]
  linear_combination (2 * β x y - 2 * β y x) * Complex.I_mul_I

theorem sesquilinear_polarization_norm {V : Type} [AddCommGroup V] [Module ℂ V] (β : V → V → ℂ)
    (hl : ∀ (x x' y : V) (a : ℂ), β (x + a • x') y = β x y + a * β x' y)
    (hr : ∀ (x y y' : V) (a : ℂ), β x (y + a • y') = β x y + conj a * β x y') (x y : V) :
    ‖β x y‖ ≤ (‖β (x + (1 : ℂ) • y) (x + (1 : ℂ) • y)‖ + ‖β (x + Complex.I • y) (x + Complex.I • y)‖
      + ‖β (x + (-1 : ℂ) • y) (x + (-1 : ℂ) • y)‖ + ‖β (x + (-Complex.I) • y) (x + (-Complex.I) • y)‖) / 4 := by
  have h := sesquilinear_polarization β hl hr x y
  have h4 : ‖(4 : ℂ) * β x y‖ = 4 * ‖β x y‖ := by simp
  have : ‖(4 : ℂ) * β x y‖ ≤ ‖β (x + (1 : ℂ) • y) (x + (1 : ℂ) • y)‖ + ‖β (x + Complex.I • y) (x + Complex.I • y)‖
      + ‖β (x + (-1 : ℂ) • y) (x + (-1 : ℂ) • y)‖ + ‖β (x + (-Complex.I) • y) (x + (-Complex.I) • y)‖ := by
    rw [h]
    refine (norm_sub_le _ _).trans ?_
    refine add_le_add ((norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add le_rfl ?_)) le_rfl)) ?_
    · simp
    · simp
  linarith

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]
  (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (st : Fr.Start (Pr (RadSp k r z z' π π')))
  (w : List (Letter ℂ S))

theorem top_density_add_left (x x' y : Ix S → RadSp k r z z' π π') (a : ℂ) (c : Fin r → ℂ) (g : Mx k r) :
    topDens L st w (x + a • x') y c g = topDens L st w x y c g + a * topDens L st w x' y c g := by
  simp only [topDens, act_add_smul, Pi.add_apply, Pi.smul_apply, Submodule.coe_add, Submodule.coe_smul,
    hsInner_add_smul_left, Finset.sum_add_distrib, Finset.mul_sum]

theorem top_density_add_right (x y y' : Ix S → RadSp k r z z' π π') (a : ℂ) (c : Fin r → ℂ) (g : Mx k r) :
    topDens L st w x (y + a • y') c g = topDens L st w x y c g + conj a * topDens L st w x y' c g := by
  simp only [topDens, act_add_smul, Pi.add_apply, Pi.smul_apply, Submodule.coe_add, Submodule.coe_smul,
    hsInner_add_smul_right, Finset.sum_add_distrib, Finset.mul_sum]

theorem act_one_hermitian_curvature (x : Ix S → RadSp k r z z' π π') : act (1 : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) x = x := by
  funext a
  simp only [act, Matrix.one_apply]
  rw [Finset.sum_eq_single a]
  · simp; rfl
  · intro b _ hb; rw [if_neg (Ne.symm hb)]; rfl
  · simp

end Dens

section Meas

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]
  {P : M.Par} {z z' : Fin (2 * P.r + P.k + 1) → ℂ} {π : Mx P.k P.r → (Wp →L[ℂ] Wp)}
  {π' : Mx P.k P.r → (Wq →L[ℂ] Wq)} {μ : Measure (Mt P.k P.r)}
  {L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r} {st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))}
  {K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')}

theorem level_integrand_aestronglyMeasurable (hM : TopDensMeas S P z z' π π' μ L st K) (w : List (Letter ℂ S))
    (x y : Ix S → RadSp P.k P.r z z' π π') (hx : InK (K (Fin.last P.r)) x) (hy : InK (K (Fin.last P.r)) y)
    (i : Fin (P.r + 1)) (c : Fin P.r → ℂ) :
    AEStronglyMeasurable (fun q : Cf P.r i × Mt P.k P.r => ((∏ l, ‖q.1 l‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
      topDens L st w x y (glue i c q.1) (Matrix.of q.2)) (volume.prod μ) := by
  have h0 := hM w x y hx hy c
  have e : (fun q : Cf P.r i × Mt P.k P.r => topDens L st w x y (glue i c q.1) (Matrix.of q.2)) =
      (fun q : Cf P.r 0 × Mt P.k P.r => topDens L st w x y (glue 0 c q.1) (Matrix.of q.2)) ∘
        Prod.map (coordinateExtension i c) id := by
    funext q; simp only [Function.comp, Prod.map, coordinate_extension_glue]; rfl
  have h1 : StronglyMeasurable (fun q : Cf P.r i × Mt P.k P.r => topDens L st w x y (glue i c q.1) (Matrix.of q.2)) := by
    rw [e]; exact h0.comp_measurable ((coordinate_extension_measurable i c).prodMap measurable_id)
  exact (level_weight_measurable i).aestronglyMeasurable.mul h1.aestronglyMeasurable

end Meas

end Formalism.FourierDecayAlt.P5
end
end
