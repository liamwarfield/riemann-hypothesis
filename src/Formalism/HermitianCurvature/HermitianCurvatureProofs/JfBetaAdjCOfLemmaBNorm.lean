module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopOfLocal
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SigmaContOn
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalMeasurabilityWeakThreshold
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HasDerivAtEpart
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGLet
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddSSn

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.JfBetaAdjCOfLemmaBNorm
open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.JFxG

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

section gen

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem cptInCC_G {F : Mat k r → E} {C : Set (Mat k r)} (hF : CkOn ⊤ (GV k r) F) (hC : IsCompact C)
    (hz : ∀ g ∈ GV k r, g ∉ C → F g = 0) (A : ℝ) (m : ℕ) : InCC A m F := by
  classical
  set F₂ : Mat k r → E := fun g => if g ∈ GV k r then F g else 0 with hF₂
  have he : ∀ g ∈ GV k r, F₂ g = F g := fun g hg => by simp [hF₂, hg]
  have hF₂c : CkOn ⊤ (GV k r) F₂ := by
    intro g₀ hg₀
    obtain ⟨U, F', hU, hgU, hc, hff⟩ := hF g₀ hg₀
    exact ⟨U, F', hU, hgU, hc, fun g hg hgG => (he g hgG).trans (hff g hg hgG)⟩
  obtain ⟨c, hc1, hc2⟩ := Formalism.FourierDecayAlt.P.compact_support_finite_class k r E F₂ C hF₂c hC (fun g hg => by
    by_cases hgG : g ∈ GV k r
    · rw [he g hgG]; exact hz g hgG hg
    · simp [hF₂, hgG]) A m
  refine ⟨c, B5.ckOn_mono le_top hF, fun u v hu hv hl g hg => ?_⟩
  have := hc2 u v hu hv hl g hg
  rwa [dLR_eq, W_congr (lr u v) (fun y hy => by
      simp only [lr, List.mem_append, List.mem_map] at hy
      rcases hy with ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩
      · exact (hu X hX).1
      · exact (hv X hX).1) he g hg, ← dLR_eq] at this

theorem ckOn_Rw_top {f : Mat k r → E} (h : CkOn ⊤ (GV k r) f) :
    ∀ (w : List (Mat k r)), (∀ X ∈ w, inLie k r X) → CkOn ⊤ (GV k r) (Rw w f) := by
  intro w
  induction w with
  | nil => intro _; exact h
  | cons X w ih =>
    intro hw
    show CkOn ⊤ (GV k r) (RdV X (Rw w f))
    have h1 : CkOn (⊤ + 1) (GV k r) (Rw w f) := by
      rw [top_add]; exact ih fun Y hY => hw Y (List.mem_cons_of_mem _ hY)
    exact B5.ckOn_RdV (hw X List.mem_cons_self) h1

end gen

end Formalism.FourierDecayAlt.P.JFxG

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.JFxG

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.ReproducingFormulaReduction
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

set_option maxHeartbeats 1600000

namespace Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity

open Formalism.FourierDecayAlt.ThreeDimData

section Basic

variable {k r : ℕ}

theorem psi_norm (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (g : Mx k r) : ‖Formalism.QuantumDeterminants.psi k r z c g‖ = 1 := by
  simp [Formalism.QuantumDeterminants.psi, Complex.norm_exp]

theorem psi_cont (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) :
    Continuous (fun g : Mx k r => Formalism.QuantumDeterminants.psi k r z c g) := by
  unfold Formalism.QuantumDeterminants.psi Formalism.QuantumDeterminants.ell
  refine Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
    (Complex.continuous_re.comp (continuous_const.mul ?_))))
  refine continuous_finsetSum _ fun a _ => ?_
  by_cases h : a.val + 1 < r
  · simp only [dif_pos h]
    fun_prop
  · simp only [dif_neg h, Matrix.mulVec, dotProduct]
    fun_prop

theorem isClosed_UH : IsClosed (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) : Set (Mx k r)) := by
  show IsClosed {g : Mx k r | gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r}
  exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
    continuous_const

theorem isClosed_UW (z : Fin (2 * r + k + 1) → ℂ) : IsClosed (Formalism.QuantumDeterminants.UWset k r z : Set (Mx k r)) := by
  have h1 : IsClosed {g : Mx k r | g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} := isClosed_UH
  have h2 : IsClosed {g : Mx k r | ∀ a : Fin r, g *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a) =
      Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a) ∧ g *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.esI k r a) =
      Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.esI k r a)} := by
    simp only [Set.setOf_forall, Set.setOf_and]
    exact isClosed_iInter fun a =>
      (isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const).inter
        (isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const)
  have h3 : IsClosed {g : Mx k r | g *ᵥ z = z} :=
    isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const
  exact h1.inter (h2.inter h3)

theorem aesm_of_contOn {α E : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    [SecondCountableTopology α] [NormedAddCommGroup E] [SecondCountableTopology E]
    {μ : Measure α} {f : α → E} {s : Set α} (hf : ContinuousOn f s) (hs : MeasurableSet s)
    (hμ : ∀ᵐ x ∂μ, x ∈ s) : AEStronglyMeasurable f μ := by
  have h := hf.aestronglyMeasurable hs (μ := μ)
  rwa [Measure.restrict_eq_self_of_ae_mem hμ] at h

theorem key_bound {A S X Y a : ℝ} (hA : 1 ≤ A) (hX : 1 ≤ X) (hY : 1 ≤ Y) (hS0 : 0 < S) (ha : 0 < a)
    (hS : S ≤ A * X * Y) : Y ^ (-a) * A ^ (-a) ≤ X ^ (a / 2) * (Y ^ (-(a / 2)) * S ^ (-(a / 2))) := by
  have hA0 : 0 < A := by linarith
  have hX0 : 0 < X := by linarith
  have hY0 : 0 < Y := by linarith
  have y1 : 0 < Y ^ (-a) := Real.rpow_pos_of_pos hY0 _
  have a1 : 0 < A ^ (-a) := Real.rpow_pos_of_pos hA0 _
  have x2 : 0 < X ^ (a / 2) := Real.rpow_pos_of_pos hX0 _
  have y2 : 0 < Y ^ (-(a / 2)) := Real.rpow_pos_of_pos hY0 _
  have s2 : 0 < S ^ (-(a / 2)) := Real.rpow_pos_of_pos hS0 _
  have h1 : Real.log S ≤ Real.log A + Real.log X + Real.log Y := by
    have e1 : Real.log (A * X * Y) = Real.log A + Real.log X + Real.log Y := by
      rw [Real.log_mul (mul_pos hA0 hX0).ne' hY0.ne', Real.log_mul hA0.ne' hX0.ne']
    rw [← e1]
    exact Real.log_le_log hS0 hS
  have h2 : 0 ≤ Real.log A := Real.log_nonneg hA
  rw [← Real.log_le_log_iff (mul_pos y1 a1) (mul_pos x2 (mul_pos y2 s2)),
    Real.log_mul y1.ne' a1.ne', Real.log_mul x2.ne' (mul_pos y2 s2).ne', Real.log_mul y2.ne' s2.ne',
    Real.log_rpow hY0, Real.log_rpow hA0, Real.log_rpow hX0, Real.log_rpow hY0, Real.log_rpow hS0]
  nlinarith [mul_le_mul_of_nonneg_left h1 ha.le, mul_nonneg ha.le h2]

end Basic

section Repro

end Repro

end Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralIdentities
open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem thrW_of (k r o : ℕ) (A : ℝ)
    (h : 12 * ((r : ℝ) + 1) ^ 2 * ((o : ℝ) + r * ((2 * r + k + 1 : ℕ) : ℝ) + 1) ≤ A) :
    Formalism.FourierDecayAlt.P.WeakThresholdClauses.WeakDominationThreshold k r A o := by
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have ho : (0 : ℝ) ≤ o := Nat.cast_nonneg o
  push_cast at h
  constructor <;>
    nlinarith [mul_nonneg (mul_nonneg hr hr) (mul_nonneg hr hr), mul_nonneg (mul_nonneg hr hr) (mul_nonneg hr hk),
      mul_nonneg (mul_nonneg hr hr) hr, mul_nonneg hr hr, mul_nonneg (mul_nonneg hr hr) hk, mul_nonneg hr hk,
      mul_nonneg (mul_nonneg hr hr) ho, mul_nonneg hr ho]

section

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem glev0 {g : Mat k r} (hg : g ∈ GV k r) : g ∈ Q.Glev k r 0 := by
  refine ⟨hg, fun a ha => ?_⟩
  simp at ha

theorem psi_inv {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {n : Mat k r} (hn : n ∈ Nset k r) :
    psi k r z cStd n⁻¹ = (psi k r z cStd n)⁻¹ := by
  have h := Formalism.QuantumDeterminants.BesselUnipotentEquiv.star_psi_inv z cStd hz n hn
  rw [← h]
  unfold psi
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp [Complex.conj_ofReal]

theorem xiTau_eq (D : RealPlaceData k r Wp Wq) (p : SS k r) :
    xiTau D (1, 1) p = psi k r D.z cStd (Matrix.of p.1.2) * (psi k r D.z' cStd (Matrix.of p.2.2))⁻¹ := by
  unfold xiTau lam psi
  push_cast
  rw [← Complex.exp_neg, ← Complex.exp_add]
  congr 1
  ring

variable [FiniteDimensional ℂ Wp]

theorem jf_equiv (D : RealPlaceData k r Wp Wq) (F : Mat k r → (Wq →L[ℂ] Wp)) (p : SS k r) (hp : D.inSS p)
    (g : Mat k r) : rho D p (JF D F) g = (xiTau D (1, 1) p)⁻¹ • JF D F g := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  have := FiniteDimensional.complete ℂ Wp
  have := FiniteDimensional.complete ℂ Wq
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarN
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW'
  have hN := Formalism.FourierDecayAlt.P.unipotent_radical_closed k r
  have hW := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r D.z
  have hW' := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r D.z'
  have hU := Formalism.QuantumDeterminants.bessel_unitary_equiv_holds Wp Wq k r D.z D.z' cStd D.π D.π' D.μW D.μN D.μW' F
    D.z_mem D.z'_mem D.haarN.conc D.haarW.conc D.haarW'.conc D.haarW.left D.haarW'.left
    (Formalism.FourierDecayAlt.P.conjugation_invariance_every_setting k r Wp Wq D) D.π_rep D.π'_rep
  have hNe := Formalism.QuantumDeterminants.bessel_unipotent_equiv_holds Wp Wq k r D.z D.z' cStd D.π D.π' D.μW D.μN D.μW' F
    D.z_mem D.z'_mem D.haarN.conc D.haarN.left
  have key : JF D F (sgs p g) =
      (psi k r D.z cStd (Matrix.of p.1.2)⁻¹ * psi k r D.z' cStd (Matrix.of p.2.2)) •
        (D.π (Matrix.of p.1.1)⁻¹).comp ((JF D F g).comp (D.π' (Matrix.of p.2.1))) := by
    unfold Formalism.FourierDecayAlt.B.JF Formalism.FourierDecayAlt.B.sgs
    rw [show (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2 * Matrix.of p.2.1 =
        (Matrix.of p.1.1)⁻¹ * ((Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2) * Matrix.of p.2.1 by
      simp only [Matrix.mul_assoc]]
    rw [hU _ _ (hW.inv_mem _ h1) _ h3, hNe _ _ (hN.inv_mem _ h2) _ h4,
      ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  ext x
  simp only [rho, key, ContinuousLinearMap.comp_apply, _root_.smul_apply, map_smul]
  rw [Formalism.QuantumDeterminants.BesselUnitaryEquiv.rep_inv D.π'_rep h3 (hW'.inv_mem _ h3) (Matrix.mul_nonsing_inv _ (hW'.unit _ h3)) x,
    Formalism.QuantumDeterminants.BesselUnitaryEquiv.rep_inv D.π_rep h1 (hW.inv_mem _ h1) (Matrix.mul_nonsing_inv _ (hW.unit _ h1))]
  congr 1
  rw [xiTau_eq, psi_inv D.z_mem h2, mul_inv, inv_inv]

end

end Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.ThetaCompactSupport
namespace Formalism.FourierDecayAlt.P.PBJ

open MeasureTheory Filter Topology Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

section rw

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem rw_vanish_GV {O : Set (Mat k r)} (hO : IsOpen O) {f : Mat k r → E}
    (h : ∀ g ∈ O, g ∈ GV k r → f g = 0) :
    ∀ (w : List (Mat k r)), (∀ X ∈ w, inLie k r X) → ∀ g ∈ O, g ∈ GV k r → Rw w f g = 0
  | [], _ => h
  | X :: w, hw => by
    intro g hg hgG
    have ih := rw_vanish_GV hO h w (fun Y hY => hw Y (List.mem_cons_of_mem _ hY))
    have hX : inLie k r X := hw X List.mem_cons_self
    show RdV X (Rw w f) g = 0
    unfold RdV
    have hc : Continuous (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) :=
      (Formalism.FourierDecayAlt.P.B5.curve_contDiff g X).continuous
    have h0 : (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) 0 ∈ O := by
      simp only; rw [Formalism.FourierDecayAlt.P.B5.curve_zero]; exact hg
    have hev : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), g * NormedSpace.exp ((t : ℂ) • X) ∈ O :=
      hc.continuousAt.preimage_mem_nhds (hO.mem_nhds h0)
    have e : (fun t : ℝ => Rw w f (g * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[𝓝 0] fun _ => 0 := by
      filter_upwards [hev] with t ht
      exact ih _ ht (Formalism.FourierDecayAlt.P.B5.curve_mem hgG hX t)
    rw [e.deriv_eq]; simp

end rw

section op

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem opApply_eq_zero (Θ : DiffOp k r Wp Wq) (F : Mat k r → (Wq →L[ℂ] Wp)) (g : Mat k r)
    (h : ∀ T ∈ Θ, Rw T.word F g = 0) : opApply Θ F g = 0 := by
  unfold opApply
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hx
  rw [h T hT, map_zero]

theorem ckOn_opApply_list (UU : Set (Mat k r)) (F : Mat k r → (Wq →L[ℂ] Wp))
    (hF : CkOn ⊤ (GV k r) F) (hs : closure {g | g ∈ GV k r ∧ F g ≠ 0} ⊆ UU) :
    ∀ Θ : DiffOp k r Wp Wq, (∀ T ∈ Θ, CkOn ⊤ UU T.coef) →
      (∀ T ∈ Θ, closure {g | g ∈ GV k r ∧ Rw T.word F g ≠ 0} ⊆ UU) → CkOn ⊤ (GV k r) (opApply Θ F)
  | [], _, _ => by
    have e : opApply ([] : DiffOp k r Wp Wq) F = fun _ => 0 := by funext g; simp [opApply]
    rw [e]; exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_zero
  | T :: Θ, hc, hsu => by
    have e : opApply (T :: Θ) F = fun g => T.coef g (Rw T.word F g) + opApply Θ F g := by
      funext g; simp [opApply]
    rw [e]
    refine Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_add ?_ (ckOn_opApply_list UU F hF hs Θ (fun T' hT' => hc T' (List.mem_cons_of_mem _ hT'))
      (fun T' hT' => hsu T' (List.mem_cons_of_mem _ hT')))
    exact Formalism.FourierDecayAlt.P.B5.ckOn_coef (hc T List.mem_cons_self)
      (Formalism.FourierDecayAlt.P.MinorPolynomials.ckOn_Rw_top hF T.word_lie) (hsu T List.mem_cons_self)

end op

end Formalism.FourierDecayAlt.P.PBJ

namespace Formalism.FourierDecayAlt.P

open MeasureTheory Filter Topology Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

theorem theta_compact_support : Formalism.FourierDecayAlt.KB.ThetaCpt := by
  intro Wp Wq _ _ _ _ _ _ P p F w e Cb hDD hF hw
  obtain ⟨nf, fib, o, κ, Dop, _, hIn, _, _, hΘeq⟩ := hDD w hw e
  obtain ⟨hFs, ⟨R, hR⟩, ε, hε, hεF⟩ := hF
  have hGc : Continuous (Gf P.k P.r p.T.base.z p.T.base.z') := Formalism.FourierDecayAlt.P.Ux8.cont_Gf _ _ _ _

  have hv1 : ∀ T ∈ Dop, ∀ g ∈ {g : Mat P.k P.r | Gf P.k P.r p.T.base.z p.T.base.z' g < ε}, g ∈ GV P.k P.r →
      Rw T.word F g = 0 := fun T _ =>
    PBJ.rw_vanish_GV (isOpen_lt hGc continuous_const)
      (fun g hg hgG => by by_contra hne; exact absurd (hεF g hgG hne) (not_le.2 hg)) T.word T.word_lie
  have hv2 : ∀ T ∈ Dop, ∀ g ∈ {g : Mat P.k P.r | R < gN g}, g ∈ GV P.k P.r → Rw T.word F g = 0 := fun T _ =>
    PBJ.rw_vanish_GV (isOpen_lt continuous_const Formalism.FourierDecayAlt.P.B6.gN_continuous)
      (fun g hg hgG => by by_contra hne; exact absurd (hR g hgG hne) (not_le.2 hg)) T.word T.word_lie
  have hcl : IsClosed {g : Mat P.k P.r | g ∈ GV P.k P.r ∧ ε ≤ Gf P.k P.r p.T.base.z p.T.base.z' g} :=
    Formalism.FourierDecayAlt.P.B5.GV_closed.inter (isClosed_le continuous_const hGc)
  have hsub : {g : Mat P.k P.r | g ∈ GV P.k P.r ∧ ε ≤ Gf P.k P.r p.T.base.z p.T.base.z' g} ⊆
      C6.domL p.T.base ∅ := fun g hg => ⟨hg.1, lt_of_lt_of_le hε hg.2, by simp⟩
  have hsF : closure {g | g ∈ GV P.k P.r ∧ F g ≠ 0} ⊆ C6.domL p.T.base ∅ := by
    refine subset_trans (closure_minimal ?_ hcl) hsub
    intro g hg; exact ⟨hg.1, hεF g hg.1 hg.2⟩
  have hsT : ∀ T ∈ Dop, closure {g | g ∈ GV P.k P.r ∧ Rw T.word F g ≠ 0} ⊆ C6.domL p.T.base ∅ := by
    intro T hT
    refine subset_trans (closure_minimal ?_ hcl) hsub
    intro g hg
    refine ⟨hg.1, ?_⟩
    by_contra hlt
    exact hg.2 (hv1 T hT g (not_le.1 hlt) hg.1)
  refine ⟨opApply Dop F, ⟨?_, ⟨R, ?_⟩, ε, hε, ?_⟩, fun g hg => hΘeq F g hg, ?_⟩
  · exact PBJ.ckOn_opApply_list _ F hFs hsF Dop (fun T hT => (hIn.1 T hT).1) hsT
  · intro g hgG hne
    by_contra hlt
    exact hne (PBJ.opApply_eq_zero Dop F g fun T hT => hv2 T hT g (not_le.1 hlt) hgG)
  · intro g hgG hne
    by_contra hlt
    exact hne (PBJ.opApply_eq_zero Dop F g fun T hT => hv1 T hT g (not_le.1 hlt) hgG)
  · intro a
    show D.vecV p.T.base p.ν' p.m₀ _ a = D.vecV p.T.base p.ν' p.m₀ _ a
    unfold D.vecV
    split_ifs with h1 h2
    · have hγ := h2.choose_spec
      have hG : 0 < Gf P.k P.r p.T.base.z p.T.base.z' h2.choose := by
        rw [← Formalism.FourierDecayAlt.P.ptG_spec _ _ _ _ a _ h1.1 hγ.2.1]; exact h1.2
      rw [Formalism.FourierDecayAlt.P.JCx1.needs.orbJ_smul_of_ae p.T.base h2.choose _ (p.Θ.Θ w e F) (opApply Dop F) 1 ?_, one_smul]
      filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS p.T.base] with q hq
      rw [one_smul]
      simp only [D.orbIntegrand, rho]
      rw [hΘeq F _ ⟨Formalism.FourierDecayAlt.P.B7.sgs_mem p.T.base hq hγ.1,
        by rw [Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs p.T.base hq]; exact hG, by simp⟩]
    · rfl
    · rfl

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTConnGaugeA
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

theorem torus_parameter : GTCTT := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d hH
  have hOK : P.OK := hH.1.1
  show 0 ≤ P.T * P.T'
  exact (mul_pos hOK.T_pos hOK.T'_pos).le

section frame

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem hsVec_smul (c : ℂ) (A : Wq →L[ℂ] Wp) : B.hsVec (c • A) = c • B.hsVec A := by
  first
  | rfl
  | (simp [B.hsVec]; done)
  | (unfold B.hsVec; rw [← WithLp.toLp_smul]; rfl)

theorem star_mul_self_of_norm {z : ℂ} (h : ‖z‖ = 1) : star z * z = 1 := by
  calc star z * z = (starRingEnd ℂ) z * z := rfl
    _ = ((‖z‖ : ℝ) : ℂ) ^ 2 := Complex.conj_mul' _
    _ = 1 := by rw [h]; norm_num

theorem isFrameB_phase (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (u : M.Ty P → ℂ → ℂ) (he : IsFrameB P Bs e)
    (hu : ∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (u ρ) (Ann P) ∧ ∀ ζ ∈ Ann P, ‖u ρ ζ‖ = 1) :
    IsFrameB P Bs (fun ρ ζ => u ρ ζ • e ρ ζ) := by
  obtain ⟨hs, hf⟩ := he
  refine ⟨fun ρ => (hu ρ).1.smul (hs ρ), fun ζ hζ => ?_⟩
  obtain ⟨hF, hO, hX⟩ := hf ζ hζ
  have hn : ∀ ρ, star (u ρ ζ) * u ρ ζ = 1 := fun ρ => star_mul_self_of_norm ((hu ρ).2 ζ hζ)
  refine ⟨fun ρ => ?_, fun ρ ρ' => ?_, fun X hXF => ?_⟩
  · have h1 := hF ρ
    beta_reduce
    simp only [NF.Fib, Set.mem_setOf_eq] at h1 ⊢
    intro p hp
    rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, h1 p hp]
  · beta_reduce
    rw [hsVec_smul, hsVec_smul, inner_smul_left, inner_smul_right, hO ρ ρ']
    split_ifs with h
    · subst h
      rw [mul_one]
      exact hn ρ
    · rw [mul_zero, mul_zero]
  · conv_lhs => rw [hX X hXF]
    refine Finset.sum_congr rfl (fun ρ _ => ?_)
    beta_reduce
    rw [hsVec_smul, inner_smul_left, smul_smul]
    congr 1
    rw [show (starRingEnd ℂ) (u ρ ζ) = star (u ρ ζ) from rfl]
    linear_combination (-(inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec X))) * hn ρ

end frame

section trans

theorem comp_snd_mem_smSub (P : M.Par) {v : ℂ → ℂ} (hv : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v (Ann P)) :
    (fun q : MA.Qp P.r P.TT => v q.1.2) ∈ MA.smSub P.r P.TT := by
  show ContDiffOn ℝ MA.sm (MA.ext (fun q : MA.Qp P.r P.TT => v q.1.2)) (MA.Qset P.r P.TT)
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : MA.E P.r => v x.2) (MA.Qset P.r P.TT) :=
    hv.comp contDiff_snd.contDiffOn (fun x hx => show P.TT < Complex.normSq x.2 from hx.2)
  exact h1.congr (fun x hx => by simp [MA.ext, hx])

theorem fnZ_eq_mk (P : M.Par) {v : ℂ → ℂ} (hv : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v (Ann P)) :
    fnZ P v = ⟨fun q => v q.1.2, comp_snd_mem_smSub P hv⟩ := by
  unfold fnZ MA.toSm
  exact dif_pos (comp_snd_mem_smSub P hv)

theorem toSm_mulZ (P : M.Par) {v w : ℂ → ℂ} (hv : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v (Ann P))
    (hw : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w (Ann P)) (hvw : ∀ ζ ∈ Ann P, w ζ * v ζ = 1)
    (g : MA.Qp P.r P.TT → ℂ) :
    MA.toSm P (fun q => v q.1.2 * g q) = fnZ P v * MA.toSm P g := by
  by_cases hg : g ∈ MA.smSub P.r P.TT
  · have hvg : (fun q : MA.Qp P.r P.TT => v q.1.2 * g q) ∈ MA.smSub P.r P.TT :=
      (MA.smSub P.r P.TT).mul_mem (comp_snd_mem_smSub P hv) hg
    rw [fnZ_eq_mk P hv]
    unfold MA.toSm
    rw [dif_pos hvg, dif_pos hg]
    rfl
  · have hvg : (fun q : MA.Qp P.r P.TT => v q.1.2 * g q) ∉ MA.smSub P.r P.TT := by
      intro h
      apply hg
      have h2 := (MA.smSub P.r P.TT).mul_mem (comp_snd_mem_smSub P hw) h
      convert h2 using 1
      funext q
      have h3 : w q.1.2 * v q.1.2 = 1 := hvw q.1.2 q.2.2
      simp only [Pi.mul_apply]
      rw [← mul_assoc, h3, one_mul]
    unfold MA.toSm
    rw [dite_eq_right hvg, dite_eq_right hg, mul_zero]

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem rawR_phase (P : M.Par) (μsec : ℂ → Matrix (Fin (P.k + 1)) (Fin (P.k + 1)) ℂ)
    (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (u : M.Ty P → ℂ → ℂ) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (ρ : M.Ty P) :
    rawR P μsec (fun ρ ζ => u ρ ζ • e ρ ζ) Φ ρ = fun q => star (u ρ q.1.2) * rawR P μsec e Φ ρ q := by
  funext q
  simp only [rawR, hsVec_smul, inner_smul_left]
  rw [show star (u ρ q.1.2) = (starRingEnd ℂ) (u ρ q.1.2) from rfl]
  ring

theorem conj_smooth {v : ℂ → ℂ} {s : Set ℂ} (hv : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v s) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ζ => star (v ζ)) s := by
  have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ζ : ℂ => star ζ) := by
    first
    | exact contDiff_id.star
    | exact Complex.conjCLE.contDiff
    | simpa using (Complex.conjCLE.contDiff (n := ((⊤ : ℕ∞) : WithTop ℕ∞)))
  exact hs.comp_contDiffOn hv

theorem trR_phase (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (u : M.Ty P → ℂ → ℂ)
    (hu : ∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (u ρ) (Ann P) ∧ ∀ ζ ∈ Ann P, ‖u ρ ζ‖ = 1)
    (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (ρ : M.Ty P) :
    trR P Bs (fun ρ ζ => u ρ ζ • e ρ ζ) Φ ρ = fnZ P (fun ζ => star (u ρ ζ)) * trR P Bs e Φ ρ := by
  simp only [trR]
  rw [rawR_phase]
  exact toSm_mulZ P (conj_smooth (hu ρ).1) (hu ρ).1
    (fun ζ hζ => by
      show u ρ ζ * star (u ρ ζ) = 1
      rw [mul_comm]
      exact star_mul_self_of_norm ((hu ρ).2 ζ hζ)) _

end trans

section act

def mulQ (P : M.Par) (x : (MA.DQ P).Pr) (f : MA.SmQ P.r P.TT) : MA.SmQ P.r P.TT := x.1 f

theorem actA_diag (P : M.Par) (x : M.Ty P → (MA.DQ P).Pr) (g : M.Ty P → MA.SmQ P.r P.TT) (ρ : M.Ty P) :
    MA.actA P (Matrix.diagonal x : MA.A P (MA.DQ P)) g ρ = (x ρ).1 (g ρ) := by
  unfold MA.actA
  refine (Fintype.sum_eq_single ρ (fun b hb => ?_)).trans ?_
  · have h0 := congrArg (fun m : (MA.DQ P).Pr => m.1 (g b)) (Matrix.diagonal_apply_ne x (Ne.symm hb))
    exact h0.trans (by first | rfl | simp)
  · exact congrArg (fun m : (MA.DQ P).Pr => m.1 (g ρ)) (Matrix.diagonal_apply_eq x ρ)

theorem algebraMap_fst_apply (P : M.Par) (c : ℂ) (f : MA.SmQ P.r P.TT) :
    (algebraMap ℂ (MA.DQ P).Pr c).1 f = c • f := rfl

theorem actA_kap (P : M.Par) (f : M.Ty P → ℂ) (g : M.Ty P → MA.SmQ P.r P.TT) (ρ : M.Ty P) :
    MA.actA P (MA.kap P (MA.DQ P) f) g ρ = f ρ • g ρ := by
  have hk : (MA.kap P (MA.DQ P) f : MA.A P (MA.DQ P)) =
      Matrix.diagonal (fun π => algebraMap ℂ (MA.DQ P).Pr (f π)) := by
    first
    | rfl
    | (ext i j; simp [MA.kap, Matrix.diagonal_apply])
  rw [hk, actA_diag, algebraMap_fst_apply]

theorem actA_nabA (P : M.Par) (g : M.Ty P → MA.SmQ P.r P.TT) (ρ : M.Ty P) :
    MA.actA P (MA.nabA P (MA.DQ P)) g ρ =
      dzQ P (g ρ) + (M.aC P ρ : ℂ) • mulQ P (MA.DQ P).zbP (mulQ P ((MA.DQ P).ggiP P.TT) (g ρ)) := by
  unfold MA.nabA
  rw [actA_diag]
  rfl

theorem actA_nabsA (P : M.Par) (g : M.Ty P → MA.SmQ P.r P.TT) (ρ : M.Ty P) :
    MA.actA P (MA.nabsA P (MA.DQ P)) g ρ =
      -dzbQ P (g ρ) + (M.aC P ρ : ℂ) • mulQ P (MA.DQ P).zP (mulQ P ((MA.DQ P).ggiP P.TT) (g ρ)) := by
  unfold MA.nabsA
  rw [actA_diag]
  rfl

end act

section kap

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem kapF_phase (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (u : M.Ty P → ℂ → ℂ)
    (hu : ∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (u ρ) (Ann P) ∧ ∀ ζ ∈ Ann P, ‖u ρ ζ‖ = 1)
    (hk : KapF P Bs d e) : KapF P Bs d (fun ρ ζ => u ρ ζ • e ρ ζ) := by
  unfold KapF at hk ⊢
  intro f Φ
  funext ρ
  rw [actA_kap, trR_phase P Bs e u hu, trR_phase P Bs e u hu, hk f Φ, actA_kap, mul_smul_comm]

end kap

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSCut
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

section preds

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def SSLoc (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')))
    (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (s t : ℕ → M.Ty P → M.Ty P → ℂ → ℂ) : Prop :=
  ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (ρ' : M.Ty P),
    trR P Bs e ((d.SS l).1 Φ) ρ' = ∑ ρ, fnZ P (s l ρ' ρ) * trR P Bs e Φ ρ ∧
    trR P Bs e ((star (d.SS l)).1 Φ) ρ' = ∑ ρ, fnZ P (t l ρ' ρ) * trR P Bs e Φ ρ

def SmST (P : M.Par) (s t : ℕ → M.Ty P → M.Ty P → ℂ → ℂ) : Prop :=
  ∀ l ρ' ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (s l ρ' ρ) (Ann P) ∧
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (t l ρ' ρ) (Ann P)

end preds

def GTSSLocal : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e →
      ∃ s t : ℕ → M.Ty P → M.Ty P → ℂ → ℂ, SmST P s t ∧ SSLoc P Bs d e s t

def GTRadAdj : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ (Y : ℂ) (a b : Fin 2) (c : Fin P.r → ℂ), c ∈ OmX P.r →
    ∀ Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
      (∃ K : Set ℂ, IsCompact K ∧ K ⊆ Ann P ∧ ∀ ζ ∈ Ann P, ζ ∉ K →
        (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ) = 0 ∧
          (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ) = 0) →
      ∫ ζ in Ann P, (((wR P.k P.TT ζ) ^ 2 : ℝ) : ℂ) *
          inner ℂ (B.hsVec ((X.t Y a b Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ)))
            (B.hsVec ((Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ))) =
        ∫ ζ in Ann P, (((wR P.k P.TT ζ) ^ 2 : ℝ) : ℂ) *
          inner ℂ (B.hsVec ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ)))
            (B.hsVec ((X.t (star Y) b a Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ)))

def GTSSAdjPt : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e →
      ∀ s t : ℕ → M.Ty P → M.Ty P → ℂ → ℂ, SmST P s t → SSLoc P Bs d e s t →
        ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ ρ ρ' : M.Ty P, ∀ ζ ∈ Ann P, t l ρ ρ' ζ = star (s l ρ' ρ ζ)

def GTSSConst : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e → NabF P Bs d e →
      ∀ s t : ℕ → M.Ty P → M.Ty P → ℂ → ℂ, SmST P s t → SSLoc P Bs d e s t →
        ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ ρ' ρ : M.Ty P, ∃ C D : ℂ, ∀ ζ ∈ Ann P, s l ρ' ρ ζ = C ∧ t l ρ' ρ ζ = D

def GTSSPhase : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e → NabF P Bs d e →
      ∀ s t : ℕ → M.Ty P → M.Ty P → ℂ, SSLoc P Bs d e (fun l ρ' ρ _ => s l ρ' ρ) (fun l ρ' ρ _ => t l ρ' ρ) →
        (∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ ρ ρ' : M.Ty P, t l ρ ρ' = star (s l ρ' ρ)) →
        ∃ e' : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e' ∧ KapF P Bs d e' ∧ NabF P Bs d e' ∧ SSF P Bs d e'

theorem fnZ_congr (P : M.Par) {f g : ℂ → ℂ} (h : ∀ ζ ∈ Ann P, f ζ = g ζ) : fnZ P f = fnZ P g := by
  unfold fnZ
  congr 1
  funext q
  exact h _ q.2.2

theorem ann_pt (P : M.Par) (hTT : 0 < P.TT) : ((Real.sqrt P.TT + 1 : ℝ) : ℂ) ∈ Ann P := by
  show P.TT < Complex.normSq (((Real.sqrt P.TT + 1 : ℝ)) : ℂ)
  rw [Complex.normSq_ofReal]
  have h1 := Real.sq_sqrt hTT.le
  have h2 := Real.sqrt_nonneg P.TT
  nlinarith

def GTSSOfCut : Prop := GTSSLocal → GTSSAdjPt → GTSSConst → GTSSPhase → GTSS

theorem gTSS_of_cut : GTSSOfCut := by
  intro hL hA hC hP
  intro Wp Wq _ _ _ _ _ _ P Bs X d hH e he hk hn
  obtain ⟨s, t, hst, hSL⟩ := hL Wp Wq P Bs X d hH e he hk
  have hc := hC Wp Wq P Bs X d hH e he hk hn s t hst hSL
  choose! C D hCD using hc
  have hζ0 : (((|P.TT| + 1 : ℝ)) : ℂ) ∈ Ann P := by
    show P.TT < Complex.normSq (((|P.TT| + 1 : ℝ)) : ℂ)
    rw [Complex.normSq_ofReal]
    nlinarith [abs_nonneg P.TT, le_abs_self P.TT]
  apply hP Wp Wq P Bs X d hH e he hk hn C D
  · intro l hl Φ ρ'
    obtain ⟨h1, h2⟩ := hSL l hl Φ ρ'
    refine ⟨h1.trans ?_, h2.trans ?_⟩
    · refine Finset.sum_congr rfl fun ρ _ => ?_
      rw [fnZ_congr P (f := s l ρ' ρ) (g := fun _ => C l ρ' ρ) (fun ζ hζ => (hCD l hl ρ' ρ ζ hζ).1)]
    · refine Finset.sum_congr rfl fun ρ _ => ?_
      rw [fnZ_congr P (f := t l ρ' ρ) (g := fun _ => D l ρ' ρ) (fun ζ hζ => (hCD l hl ρ' ρ ζ hζ).2)]
  · intro l hl ρ ρ'
    have h := hA Wp Wq P Bs X d hH e he hk s t hst hSL l hl ρ ρ' _ hζ0
    rw [(hCD l hl ρ ρ' _ hζ0).2, (hCD l hl ρ' ρ _ hζ0).1] at h
    exact h

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.Imports
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBG

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def Kr (Bs : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (x : B.Mat k r) : Wq →L[ℂ] Wp :=
  ∫ p : Mt k r × Mt k r, star (psi k r Bs.z' cStd (Matrix.of p.2)) •
    (F (x * Matrix.of p.2 * Matrix.of p.1)).comp (Bs.π' (Matrix.of p.1)⁻¹) ∂(Bs.μW'.prod Bs.μN)

end Formalism.FourierDecayAlt.P.PBG
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCLocalCut
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

section preds

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def RadDZ (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (T : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) : Prop :=
  ∃ (n : ℕ) (A : (j : ℕ) → ℂ →
      (ContinuousMultilinearMap ℝ (fun _ : Fin j => ℂ) (Wq →L[ℂ] Wp) →L[ℝ] (Wq →L[ℂ] Wp))),
    (∀ j, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (A j)
      {ζ : ℂ | Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ}) ∧
    ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (q : (Fin P.r → ℂ) × ℂ), q ∈ NF.QR P.k P.r Bs.z Bs.z' →
      NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (T Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q =
        ∑ j ∈ Finset.range (n + 1), A j q.2
          (iteratedFDeriv ℝ j (fun ζ => NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (q.1, ζ)) q.2)

end preds

def GTCLRadT : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → CSec P.k P.r Bs.z Bs.z' Bs.μsec →
    ∀ (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (Y : ℂ) (a b : Fin 2), RadDZ P Bs (X.t Y a b)

def GTCLNab : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → (∀ (Y : ℂ) (a b : Fin 2), RadDZ P Bs (X.t Y a b)) →
    ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e →
      RadDZ P Bs d.L.nab.1 ∧ RadDZ P Bs d.L.nabs.1

def GTCLFrame : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e →
      RadDZ P Bs d.L.nab.1 → RadDZ P Bs d.L.nabs.1 →
      ∃ A B : M.Ty P → ℂ → ℂ, SmAB P A B ∧ ConnF P Bs d e A B

def GTCLocalOfCut : Prop := GTCLRadT → GTCLNab → GTCLFrame → GTCLocal

theorem gTCLocal_of_cut : GTCLocalOfCut := by
  intro hT hN hF Wp Wq _ _ _ _ _ _ P Bs X d hH e he hk
  have hRT := hT Wp Wq P Bs hH.1 hH.2.1 hH.2.2.1 X
  obtain ⟨h1, h2⟩ := hN Wp Wq P Bs X d hH hRT e he hk
  exact hF Wp Wq P Bs X d hH e he hk h1 h2

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRho
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.PRho

noncomputable section

def nrmW (k r : ℕ) (z a : Fin (2 * r + k + 1) → ℂ) : ℝ :=
  (herm (Hpk k r) (SSn.prWv k r z a) (SSn.prWv k r z a)).re

section spec

variable {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]

def PRhoSpec (P : M.Par) (z : Fin (2 * P.r + P.k + 1) → ℂ) (π : B.Mat P.k P.r → (Wp →L[ℂ] Wp))
    (Pr : M.Ty P → (Fin (2 * P.r + P.k + 1) → ℂ) → (Wp →L[ℂ] Wp)) : Prop :=
  (∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Pr ρ) {a | 1 / 4 < nrmW P.k P.r z a}) ∧
  (∀ h ∈ UWset P.k P.r z, ∀ ρ a, Pr ρ (h *ᵥ a) = (π h).comp ((Pr ρ a).comp (π h⁻¹))) ∧
  ∀ a, 0 < nrmW P.k P.r z a →
    (∀ ρ (c : ℂ), c ≠ 0 → Pr ρ (c • a) = Pr ρ a) ∧
    (∀ ρ x y, inner ℂ (Pr ρ a x) y = inner ℂ x (Pr ρ a y)) ∧
    (∀ ρ ρ', (Pr ρ a).comp (Pr ρ' a) = if ρ = ρ' then Pr ρ a else 0) ∧
    ∀ ρ (x : Wp), Pr ρ a x = x ↔
      ∀ Fr : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ, Q.IsFrameOf P.k P.r [z, SSn.prWv P.k P.r z a] Fr →
        ∀ w : ℂ, Q.capRep P.k P.r π Fr w x = M.xC P ρ (w - ((P.k : ℂ) - 2) / 2) • x

end spec

def PRhoExists : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → ∃ Pr, PRhoSpec P Bs.z Bs.π Pr

section ctx

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]

def Hyp (Cc : ℝ) (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ) (v : Fin S.f) (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) : Prop :=
  BuiltOW Cc S T f χ ν' m₀ top A₀ ∧ IsFrame S T v e ∧ IsGauge S T v e ∧ IsGaugeQQ S T v e

end ctx

def GaugeLines : Prop :=
  ∀ (Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ) (v : Fin S.f) (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))),
    Hyp Cc S T f χ ν' m₀ top A₀ v e → 2 ≤ S.G.k →
    ∀ ζ : ℂ, (D.parOf S v).TT < Complex.normSq ζ → ∀ (ρ : M.Ty (D.parOf S v))
      (Fr : Fin (S.G.k - 1) → Fin (2 * S.G.r + S.G.k + 1) → ℂ),
      Q.IsFrameOf S.G.k S.G.r [(T v).base.z, SSn.nu0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ] Fr →
      ∀ (w : ℂ) (x : Wq (S.pl v)),
        Q.capRep S.G.k S.G.r (T v).base.π Fr w (e ρ ζ x) =
          M.xC (D.parOf S v) ρ (w - ((S.G.k : ℂ) - 2) / 2) • e ρ ζ x

end

end Formalism.FourierDecayAlt.P.CutMP.JA.PRho
end
