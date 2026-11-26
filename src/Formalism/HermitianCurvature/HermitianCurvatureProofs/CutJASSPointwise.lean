module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSLMat
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyZeroNear
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutAsm

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSPointwise
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JA

noncomputable section

namespace SSPw

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def conjL (A : Wp →L[ℂ] Wp) (B : Wq →L[ℂ] Wq) : (Wq →L[ℂ] Wp) →ₗ[ℂ] (Wq →L[ℂ] Wp) where
  toFun X := A.comp (X.comp B)
  map_add' X Y := by
    rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
  map_smul' c X := by
    rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
    rfl

def sumL {ι : Type} [Fintype ι] (f : ι → (Wq →L[ℂ] Wp)) (V : ι → (Wq →L[ℂ] Wp)) :
    (Wq →L[ℂ] Wp) →ₗ[ℂ] (Wq →L[ℂ] Wp) :=
  ∑ ρ, (((innerₛₗ ℂ (B.hsVec (f ρ))).comp Formalism.FourierDecayAlt.P.JFxI.hsVecL).smulRight (V ρ))

theorem sumL_apply {ι : Type} [Fintype ι] (f : ι → (Wq →L[ℂ] Wp)) (V : ι → (Wq →L[ℂ] Wp)) (Y : Wq →L[ℂ] Wp) :
    sumL f V Y = ∑ ρ, inner ℂ (B.hsVec (f ρ)) (B.hsVec Y) • V ρ := by
  unfold sumL
  rw [LinearMap.sum_apply]
  rfl

end SSPw

open SSPw in
theorem second_shift_pointwise_holds : SSn.Rep.Core.SSPointwise := by
  intro Wp Wq _ _ _ _ _ _ P Bs hk X d hA l hl
  obtain ⟨hpl, hL, hS, hRel, hQQ⟩ := hA
  have hz := Bs.z_mem
  have hz' := Bs.z'_mem
  have hTz : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' = P.TT := Gauge.GC.tz_TT P Bs hpl

  have hcs0 := Formalism.FourierDecayAlt.P.TheSecStab.theSection_csec (k := P.k) (r := P.r) (by omega) Bs.z_mem Bs.z'_mem
    Bs.T_pos Bs.T'_pos
  set μ0 := TheSec.theSection P.k P.r Bs.z Bs.z' with hμ0
  let Bs0 : B.RealPlaceData P.k P.r Wp Wq := { Bs with μsec := μ0, sec := hcs0.1 }
  have hyp0 : Gauge.GC.GTHyp P Bs0 X d := ⟨hpl, hk, hcs0, hL, hS, hRel, hQQ⟩
  obtain ⟨e0, he0, -⟩ := Gauge.GC.gauge_kappa_holds Wp Wq P Bs0 X d hyp0

  have hRT := Gauge.GC.radial_torus_local_holds Wp Wq P Bs0 hpl hk hcs0 X
  have hSl : ∀ (Y : ℂ) (a b : Fin 2), Gauge.GC.SliceLoc P Bs0 (X.t Y a b) := fun Y a b =>
    Gauge.GC.second_shift_slice_derivative Wp Wq P Bs0 hpl _ (hRT Y a b)
  have hSL := (Gauge.GC.second_shift_slice_operator Wp Wq P Bs0 X d hyp0 hSl l hl).1

  have hC : ∀ f : ℂ → ℂ, ContDiffOn ℝ ∞ f {ζ | P.TT < Complex.normSq ζ} →
      ∀ W : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), NF.IsMulZ W f → Commute (d.SS l).1 W := by
    intro f hf W hW
    obtain ⟨W₁, hW₁⟩ := Formalism.FourierDecayAlt.P.multiplication_zeta_exists Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hpl (NF.dZ f)
      (Formalism.FourierDecayAlt.P.NFx4.NO.dZ_smooth (Formalism.FourierDecayAlt.P.NFx4.NO.isOpen_U _) hf)
    obtain ⟨W₂, hW₂⟩ := Formalism.FourierDecayAlt.P.multiplication_zeta_exists Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hpl (NF.dZb f)
      (Formalism.FourierDecayAlt.P.NFx4.NO.dZb_smooth (Formalism.FourierDecayAlt.P.NFx4.NO.isOpen_U _) hf)
    exact ((Formalism.FourierDecayAlt.P.normal_form_order_zero Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hpl X d hL hS hRel hQQ f hf W W₁ W₂
      hW hW₁ hW₂).2.1 l hl).1

  have hRB0 : NF.RadBase P.k P.r Bs.z Bs.z' μ0 Bs.π Bs.π' := Gauge.GC.radBase_of P Bs0 hpl
  let c0 : Fin P.r → ℂ := fun _ => 1
  have hc0 : c0 ∈ OmX P.r := fun _ => one_ne_zero
  have hsec : ∀ ρ, ((NF.QR P.k P.r Bs.z Bs.z').indicator fun q : (Fin P.r → ℂ) × ℂ => e0 ρ q.2) ∈
      NF.RadSec P.k P.r Bs.z Bs.z' μ0 Bs.π Bs.π' := by
    intro ρ
    refine ⟨((he0.1 ρ).comp contDiff_snd.contDiffOn fun q hq => ?_).congr fun q hq => ?_, fun q hq => ?_,
      fun q hq => ?_⟩
    · show P.TT < Complex.normSq q.2
      rw [← hTz]; exact hq.2
    · simp [Set.indicator_of_mem hq]
    · rw [Set.indicator_of_mem hq]
      exact (he0.2 q.2 (by rw [← hTz]; exact hq.2)).1 ρ
    · simp [Set.indicator_of_notMem hq]
  choose Ψ0 hΨ0 hΨr using fun ρ =>
    Formalism.FourierDecayAlt.P.radical_reduction_surjective Wp Wq P.k P.r Bs.z Bs.z' μ0 Bs.π Bs.π' hRB0 _ (hsec ρ)
  let Ψ : M.Ty P → Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' := fun ρ => ⟨Ψ0 ρ, hΨ0 ρ⟩
  have hΨ : ∀ ρ, ∀ c ∈ OmX P.r, ∀ ζ ∈ Gauge.GC.Ann P,
      (Ψ ρ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs0.μsec ζ) = e0 ρ ζ := by
    intro ρ c hc ζ hζ
    have hq : ((c, ζ) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨hc, by rw [hTz]; exact hζ⟩
    have h := congrFun (hΨr ρ) (c, ζ)
    simp only [NF.radR, Set.indicator_of_mem hq] at h
    exact h

  have hdec : ∀ ζ : ℂ, ∃ hh : Q.Mx P.k P.r × Q.Mx P.k P.r, ζ ∈ Gauge.GC.Ann P →
      hh.1 ∈ UWset P.k P.r Bs.z ∧ hh.2 ∈ UWset P.k P.r Bs.z' ∧
        NF.muZ P.k P.r Bs.μsec ζ = hh.1 * NF.muZ P.k P.r μ0 ζ * hh.2 := by
    intro ζ
    by_cases hζ : ζ ∈ Gauge.GC.Ann P
    · have hq : ((c0, ζ) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨hc0, by rw [hTz]; exact hζ⟩
      have hdom := Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' Bs.sec hq
      obtain ⟨h, hh, h', hh', he⟩ := Formalism.FourierDecayAlt.P.NFRadRedA.decomp Bs.k_pos hz hz' Bs.T_pos Bs.T'_pos hcs0.1
        hdom.2.1 hdom.2.2
      rw [Formalism.FourierDecayAlt.P.NFRadRedA.zeta_muZ hz hz' Bs.sec hq.2] at he
      exact ⟨(h, h'), fun _ => ⟨hh, hh', he⟩⟩
    · exact ⟨(1, 1), fun h => absurd h hζ⟩
  choose H hH using hdec
  let V : M.Ty P → ℂ → (Wq →L[ℂ] Wp) := fun ρ ζ =>
    ((d.SS l).1 (Ψ ρ) : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c0 (NF.muZ P.k P.r μ0 ζ)
  refine ⟨fun ζ => LinearMap.toContinuousLinearMap
    ((conjL (Bs.π (H ζ).1) (Bs.π' (H ζ).2)) ∘ₗ sumL (fun ρ => e0 ρ ζ) (fun ρ => V ρ ζ) ∘ₗ
      conjL (Bs.π (H ζ).1⁻¹) (Bs.π' (H ζ).2⁻¹)), ?_⟩
  intro Φ c hc ζ hζ
  obtain ⟨hh, hh', hd⟩ := hH ζ hζ
  set h := (H ζ).1
  set h' := (H ζ).2
  have hq : ((c, ζ) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨hc, by rw [hTz]; exact hζ⟩
  have hdom := Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' Bs.sec hq
  have hdom0 := Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' hcs0.1 hq
  have hhi := Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh
  have hhi' := Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh'

  have hback : NF.muZ P.k P.r μ0 ζ = h⁻¹ * NF.muZ P.k P.r Bs.μsec ζ * h'⁻¹ := by
    rw [hd, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Formalism.FourierDecayAlt.P.NFRadRedS.uw_inv_mul hh, Matrix.one_mul,
      Matrix.mul_assoc, Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul_inv hh', Matrix.mul_one]
  have hΦ0 : (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r μ0 ζ) =
      (Bs.π h⁻¹).comp (((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ)).comp (Bs.π' h'⁻¹)) := by
    rw [hback]
    exact Φ.2.2.2 (c, NF.muZ P.k P.r Bs.μsec ζ) hdom h⁻¹ hhi h'⁻¹ hhi'

  have hfwd : (((d.SS l).1 Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c
        (NF.muZ P.k P.r Bs.μsec ζ) =
      (Bs.π h).comp (((((d.SS l).1 Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c
        (NF.muZ P.k P.r μ0 ζ)).comp (Bs.π' h')) := by
    rw [hd]
    exact ((d.SS l).1 Φ).2.2.2 (c, NF.muZ P.k P.r μ0 ζ) hdom0 h hh h' hh'
  have hkey := Gauge.GC.key_slice P Bs0 hpl hk e0 he0 Ψ hΨ (d.SS l).1 hSL hC Φ hc hc0 hζ
  rw [hfwd]
  change _ = (Bs.π h).comp ((sumL (fun ρ => e0 ρ ζ) (fun ρ => V ρ ζ)
    ((Bs.π h⁻¹).comp (((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ)).comp (Bs.π' h'⁻¹)))).comp
      (Bs.π' h'))
  rw [← hΦ0, sumL_apply]
  congr 2

end

end Formalism.FourierDecayAlt.P.CutMP.JA
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceContOn
open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBM

section dom

variable {k r : ℕ}

theorem detM_zero (Z : G.Mat 0) : G.detM Z = 1 := by
  unfold G.detM; exact Matrix.det_isEmpty

theorem hMat_det_ne (σ : Equiv.Perm (Fin r)) (d : Fin r → ℂ) (hd : ∀ i, d i ≠ 0) : (U.hMat σ d).det ≠ 0 := by
  rw [U.hMat, Matrix.det_mul, Matrix.det_diagonal]
  exact mul_ne_zero (Dx2.SL.isUnit_wP σ).ne_zero (Finset.prod_ne_zero_iff.2 fun i _ => hd i)

theorem zjH_det (σ : Equiv.Perm (Fin r)) (d : Fin r → ℂ) (η : U.XiH r 0 σ) :
    (U.ZjH σ d η (fun a => a.elim0)).det = (U.hMat σ d).det := by
  rw [Formalism.FourierDecayAlt.P.level_determinant_z r 0 σ d η (fun a => a.elim0), detM_zero, mul_one]

theorem rn_mem_GV (x : U.RC k r 0) : U.Rn k r 0 x ∈ B.GV k (r + 0) := by
  have h := (Formalism.FourierDecayAlt.P.radical_parametrisation k r 0).2.1
  have : U.Rn k r 0 x ∈ U.Rset k r 0 := by rw [← h]; exact ⟨x, rfl⟩
  exact this.1

theorem gaXi_mem_GV (σ : Equiv.Perm (Fin r)) (d : Fin r → ℂ) (hd : ∀ i, d i ≠ 0) (ξ : U.Xi k r 0 0 σ)
    (γ : B.Mat k 0) (hγ : γ ∈ B.GV k 0) : U.gaXi k 0 σ d ξ (fun a => a.elim0) γ ∈ B.GV k r := by
  have hG := Formalism.FourierDecayAlt.P.unitary_group_closed k (r + 0)
  have hm := (Formalism.FourierDecayAlt.P.slice_membership k r 0).1 (U.ZjH σ d ξ.2 (fun a => a.elim0)) γ
    (by rw [zjH_det]; exact hMat_det_ne σ d hd) hγ
  unfold U.gaXi
  exact hG.mul_mem _ (hG.mul_mem _ (hG.inv_mem _ (rn_mem_GV _)) _ hm) _ (rn_mem_GV _)

theorem slice_dom (k r : ℕ) (hr : 1 ≤ r) (σ : Equiv.Perm (Fin r)) (d : Fin r → ℂ) (hd : ∀ i, d i ≠ 0)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (F : B.Mat k r → E)
    (hFc : ContinuousOn F (B.GV k r)) (R : ℝ) (hFs : ∀ g ∈ B.GV k r, F g ≠ 0 → B.gN g ≤ R) :
    ∃ (M : ℝ) (Bs : Set (U.Xi k r 0 0 σ)), MeasurableSet Bs ∧ U.muXi k r 0 0 σ Bs < ⊤ ∧
      ∀ (ξ : U.Xi k r 0 0 σ) (γ : B.Mat k 0), γ ∈ B.GV k 0 →
        ‖F (U.gaXi k 0 σ d ξ (fun a => a.elim0) γ)‖ ≤ Bs.indicator (fun _ => M) ξ := by

  have hK : IsCompact {g : B.Mat k r | g ∈ B.GV k r ∧ B.gN g ≤ R} := by
    have h1 := Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le k r R
    have h2 := (Formalism.FourierDecayAlt.P.unitary_group_closed k r).closed
    have : {g : B.Mat k r | g ∈ B.GV k r ∧ B.gN g ≤ R} = B.GV k r ∩ {g | B.gN g ≤ R} := rfl
    rw [this]; exact h1.inter_left h2
  obtain ⟨M0, hM0⟩ := hK.exists_bound_of_continuousOn (hFc.mono fun g hg => hg.1)

  obtain ⟨C1, hC1⟩ := Formalism.FourierDecayAlt.P.block3_apply_embedding k r 0 hr
  obtain ⟨C2, hC2⟩ := Formalism.FourierDecayAlt.P.aux_statement_17 r 0 σ d hd
  set δ := ‖(U.hMat σ d).det‖ with hδ
  have hδ0 : 0 < δ := norm_pos_iff.2 (hMat_det_ne σ d hd)
  set R0 := max R 0
  set C1' := max C1 0
  set C2' := max C2 0
  set K1 := C1' * R0 ^ r / min 1 δ
  set K2 := C2' * (C1' * R0) ^ r
  set K := max (max K1 K2) 0
  set B1 : Set (U.RC k (r + 0) 0) := Metric.closedBall (0 : Fin (2 * 0 + k + 1) → Fin (r + 0) → ℂ) K ×ˢ
    (Metric.closedBall (0 : G.UT (r + 0) → ℂ) K ×ˢ Metric.closedBall (0 : Fin (r + 0) → ℝ) K) with hB1
  set Bs : Set (U.Xi k r 0 0 σ) :=
    (B1 ×ˢ B1) ×ˢ
      ((Metric.closedBall (0 : Fin 0 → Fin r → ℂ) K ×ˢ Metric.closedBall (0 : Fin r → Fin 0 → ℂ) K) ×ˢ
        (Metric.closedBall (0 : U.LW σ → ℂ) K ×ˢ Metric.closedBall (0 : G.UT r → ℂ) K)) with hBs
  have hB1m : MeasurableSet B1 := Metric.isClosed_closedBall.measurableSet.prod
    (Metric.isClosed_closedBall.measurableSet.prod Metric.isClosed_closedBall.measurableSet)
  have hprod : ∀ {α β : Type} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (ν : Measure β) [SFinite ν]
      {s : Set α} {t : Set β}, μ s < ⊤ → ν t < ⊤ → (μ.prod ν) (s ×ˢ t) < ⊤ := by
    intro α β _ _ μ ν _ s t hs ht; rw [Measure.prod_prod]; exact ENNReal.mul_lt_top hs ht
  have hRC : U.muRC k (r + 0) 0 B1 < ⊤ := by
    unfold U.muRC
    exact hprod volume volume measure_closedBall_lt_top (hprod volume volume measure_closedBall_lt_top
      measure_closedBall_lt_top)
  refine ⟨max M0 0, Bs, ?_, ?_, ?_⟩
  · exact (hB1m.prod hB1m).prod
      ((Metric.isClosed_closedBall.measurableSet.prod Metric.isClosed_closedBall.measurableSet).prod
        (Metric.isClosed_closedBall.measurableSet.prod Metric.isClosed_closedBall.measurableSet))
  · unfold U.muXi U.muXiH
    have h1 : SFinite (volume : Measure ((G.UT (r + 0) → ℂ) × (Fin (r + 0) → ℝ))) :=
      (inferInstance : SFinite ((volume : Measure (G.UT (r + 0) → ℂ)).prod (volume : Measure (Fin (r + 0) → ℝ))))
    have : SFinite (U.muRC k (r + 0) 0) :=
      (inferInstance : SFinite ((volume : Measure (Fin (2 * 0 + k + 1) → Fin (r + 0) → ℂ)).prod
        (volume : Measure ((G.UT (r + 0) → ℂ) × (Fin (r + 0) → ℝ)))))
    exact hprod _ volume (hprod _ _ hRC hRC)
      (hprod volume volume (hprod volume volume measure_closedBall_lt_top measure_closedBall_lt_top)
        (hprod volume volume measure_closedBall_lt_top measure_closedBall_lt_top))
  · intro ξ γ hγ
    set g := U.gaXi k 0 σ d ξ (fun a => a.elim0) γ with hg
    by_cases hF : F g = 0
    · rw [hF, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => le_max_right _ _) ξ
    · have hgG : g ∈ B.GV k r := gaXi_mem_GV σ d hd ξ γ hγ
      have hgR := hFs g hgG hF
      have hgn : 0 ≤ B.gN g := Real.sqrt_nonneg _
      have hgR0 : B.gN g ≤ R0 := hgR.trans (le_max_left _ _)
      have hdet : (U.ZjH σ d ξ.2 (fun a => a.elim0)).det ≠ 0 := by rw [zjH_det]; exact hMat_det_ne σ d hd
      obtain ⟨h1, h2, h3, -, -⟩ := hC1 ξ.1.1 ξ.1.2 (U.ZjH σ d ξ.2 (fun a => a.elim0)) γ hdet hγ
      have hdetn : ‖(U.ZjH σ d ξ.2 (fun a => a.elim0)).det‖ = δ := by rw [zjH_det]
      rw [hdetn] at h1 h2
      have hmin : 0 < min 1 δ := lt_min one_pos hδ0
      have hC1n : 0 ≤ C1' := le_max_right _ _
      have hpow : B.gN g ^ r ≤ R0 ^ r := pow_le_pow_left₀ hgn hgR0 r
      have hpow0 : 0 ≤ B.gN g ^ r := pow_nonneg hgn r
      have hb1 : ‖ξ.1.1‖ ≤ K1 := by
        refine (Formalism.FourierDecayAlt.P.Ux6.norm_le_gN_Rn ξ.1.1).trans (h1.trans ?_)
        refine div_le_div_of_nonneg_right ?_ hmin.le
        exact (mul_le_mul_of_nonneg_right (le_max_left _ _) hpow0).trans (mul_le_mul_of_nonneg_left hpow hC1n)
      have hb2 : ‖ξ.1.2‖ ≤ K1 := by
        refine (Formalism.FourierDecayAlt.P.Ux6.norm_le_gN_Rn ξ.1.2).trans (h2.trans ?_)
        refine div_le_div_of_nonneg_right ?_ hmin.le
        exact (mul_le_mul_of_nonneg_right (le_max_left _ _) hpow0).trans (mul_le_mul_of_nonneg_left hpow hC1n)
      have hmx : U.mx (U.ZjH σ d ξ.2 (fun a => a.elim0)) ≤ C1' * R0 :=
        h3.trans ((mul_le_mul_of_nonneg_right (le_max_left _ _) hgn).trans (mul_le_mul_of_nonneg_left hgR0 hC1n))
      have hmx0 : 0 ≤ U.mx (U.ZjH σ d ξ.2 (fun a => a.elim0)) := norm_nonneg _
      obtain ⟨e1, e2, e3, e4, -, -⟩ := hC2 ξ.2 (fun a => a.elim0)
      have hC2n : 0 ≤ C2' := le_max_right _ _
      have hpm : U.mx (U.ZjH σ d ξ.2 (fun a => a.elim0)) ^ r ≤ (C1' * R0) ^ r := pow_le_pow_left₀ hmx0 hmx r
      have hpm0 : 0 ≤ U.mx (U.ZjH σ d ξ.2 (fun a => a.elim0)) ^ r := pow_nonneg hmx0 r
      have hK2 : ∀ t : ℝ, t ≤ C2 * U.mx (U.ZjH σ d ξ.2 (fun a => a.elim0)) ^ r → t ≤ K2 := fun t ht =>
        ht.trans ((mul_le_mul_of_nonneg_right (le_max_left _ _) hpm0).trans (mul_le_mul_of_nonneg_left hpm hC2n))
      have hξ : ‖ξ‖ ≤ K := by
        have k1 : K1 ≤ K := le_max_left _ _ |>.trans (le_max_left _ _)
        have k2 : K2 ≤ K := le_max_right _ _ |>.trans (le_max_left _ _)
        exact norm_prod_le_iff.2 ⟨norm_prod_le_iff.2 ⟨hb1.trans k1, hb2.trans k1⟩,
          norm_prod_le_iff.2 ⟨norm_prod_le_iff.2 ⟨(hK2 _ e1).trans k2, (hK2 _ e2).trans k2⟩,
            norm_prod_le_iff.2 ⟨(hK2 _ e3).trans k2, (hK2 _ e4).trans k2⟩⟩⟩
      have hmem : ξ ∈ Bs := by
        have hb := fun {α : Type} [SeminormedAddCommGroup α] (x : α) (h : ‖x‖ ≤ K) =>
          (show x ∈ Metric.closedBall (0 : α) K by rw [Metric.mem_closedBall, dist_zero_right]; exact h)
        obtain ⟨⟨h11, h12⟩, ⟨h21, h22⟩, h23, h24⟩ :
            (‖ξ.1.1‖ ≤ K ∧ ‖ξ.1.2‖ ≤ K) ∧ (‖ξ.2.1.1‖ ≤ K ∧ ‖ξ.2.1.2‖ ≤ K) ∧ ‖ξ.2.2.1‖ ≤ K ∧ ‖ξ.2.2.2‖ ≤ K := by
          obtain ⟨ha, hb'⟩ := norm_prod_le_iff.1 hξ
          obtain ⟨ha1, ha2⟩ := norm_prod_le_iff.1 ha
          obtain ⟨hb1', hb2'⟩ := norm_prod_le_iff.1 hb'
          exact ⟨⟨ha1, ha2⟩, norm_prod_le_iff.1 hb1', norm_prod_le_iff.1 hb2'⟩
        have hrc : ∀ x : U.RC k (r + 0) 0, ‖x‖ ≤ K → x ∈ B1 := by
          intro x hx
          obtain ⟨hx1, hx2⟩ := norm_prod_le_iff.1 hx
          obtain ⟨hx21, hx22⟩ := norm_prod_le_iff.1 hx2
          exact ⟨hb _ hx1, hb _ hx21, hb _ hx22⟩
        exact ⟨⟨hrc _ h11, hrc _ h12⟩, ⟨hb _ h21, hb _ h22⟩, hb _ h23, hb _ h24⟩
      rw [Set.indicator_of_mem hmem]
      exact (hM0 g ⟨hgG, hgR⟩).trans (le_max_left _ _)

theorem zjH_eq (σ : Equiv.Perm (Fin r)) (d : Fin r → ℂ) (η : U.XiH r 0 σ) :
    U.ZjH σ d η (fun a => a.elim0) = U.headH σ d η.2.1 η.2.2 := by
  unfold U.ZjH; exact Dx2.SL.zj_zero _ _ _ _

theorem headH_det (σ : Equiv.Perm (Fin r)) (d : Fin r → ℂ) (η : U.XiH r 0 σ) :
    (U.headH σ d η.2.1 η.2.2).det = (U.hMat σ d).det := by
  rw [← zjH_eq, zjH_det]

theorem headH_cont (σ : Equiv.Perm (Fin r)) (d : Fin r → ℂ) :
    Continuous (fun η : U.XiH r 0 σ => U.headH σ d η.2.1 η.2.2) := by
  unfold U.headH
  exact ((continuous_const.matrix_mul ((Dx2.SL.cont_lowW σ).comp (continuous_fst.comp continuous_snd))).matrix_mul
    continuous_const).matrix_mul (Dx2.SL.cont_upper.comp (continuous_snd.comp continuous_snd))

theorem gaXi_cont (σ : Equiv.Perm (Fin r)) (d : Fin r → ℂ) (hd : ∀ i, d i ≠ 0) :
    Continuous (fun p : U.Xi k r 0 0 σ × B.Mat k 0 => U.gaXi k 0 σ d p.1 (fun a => a.elim0) p.2) := by
  set c := (U.hMat σ d).det with hc
  have hc0 : star c ≠ 0 := star_ne_zero.2 (hMat_det_ne σ d hd)
  have hinv : ∀ η : U.XiH r 0 σ, (U.headH σ d η.2.1 η.2.2)ᴴ⁻¹ = (star c)⁻¹ • (U.headH σ d η.2.1 η.2.2)ᴴ.adjugate := by
    intro η
    rw [Formalism.FourierDecayAlt.P.B2x2.inv_eq, Matrix.det_conjTranspose, headH_det]
  have hH : Continuous (fun p : U.Xi k r 0 0 σ × B.Mat k 0 => U.headH σ d p.1.2.2.1 p.1.2.2.2) :=
    (headH_cont σ d).comp (continuous_snd.comp continuous_fst)
  have hm : Continuous (fun p : U.Xi k r 0 0 σ × B.Mat k 0 =>
      U.mMap k r 0 (U.headH σ d p.1.2.2.1 p.1.2.2.2) p.2) := by
    unfold U.mMap
    simp only [hinv]
    refine Dx2.SplitF.continuous_block3_matrix continuous_const continuous_const ?_ continuous_const continuous_snd continuous_const
      (continuous_const.matrix_mul hH) continuous_const continuous_const
    exact (hH.matrix_conjTranspose.matrix_adjugate.const_smul ((star c)⁻¹ : ℂ)).matrix_mul continuous_const
  have e : (fun p : U.Xi k r 0 0 σ × B.Mat k 0 => U.gaXi k 0 σ d p.1 (fun a => a.elim0) p.2) =
      fun p => U.Rn k r 0 (-p.1.1.1) * U.mMap k r 0 (U.headH σ d p.1.2.2.1 p.1.2.2.2) p.2 * U.Rn k r 0 p.1.1.2 := by
    funext p
    unfold U.gaXi
    rw [rn_inv, zjH_eq]
    rfl
  rw [e]
  exact (((Dx2.SplitF.rn_cont r 0).comp (continuous_fst.comp (continuous_fst.comp continuous_fst)).neg).matrix_mul hm).matrix_mul
    ((Dx2.SplitF.rn_cont r 0).comp (continuous_snd.comp (continuous_fst.comp continuous_fst)))

end dom

end Formalism.FourierDecayAlt.P.PBM
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDAsm
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt MeasureTheory

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField

noncomputable section

section gen

variable (P : M.Par)

theorem jd_actA_add (a b : MA.A P (MA.DQ P)) (x : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (a + b) x = MA.actA P a x + MA.actA P b x := by
  funext π
  show ∑ π', ((a + b) π π').1 (x π') = ∑ π', (a π π').1 (x π') + ∑ π', (b π π').1 (x π')
  rw [← Finset.sum_add_distrib]
  rfl

theorem jd_actA_zero (x : M.Ty P → MA.SmQ P.r P.TT) : MA.actA P 0 x = 0 := by
  funext π
  show ∑ π', ((0 : MA.A P (MA.DQ P)) π π').1 (x π') = 0
  exact Finset.sum_eq_zero fun _ _ => rfl

theorem jd_actA_addR (a : MA.A P (MA.DQ P)) (x y : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P a (x + y) = MA.actA P a x + MA.actA P a y := by
  funext π
  show ∑ π', (a π π').1 (x π' + y π') = ∑ π', (a π π').1 (x π') + ∑ π', (a π π').1 (y π')
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => map_add _ _ _

theorem jd_actA_smulR (a : MA.A P (MA.DQ P)) (c : ℂ) (x : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P a (c • x) = c • MA.actA P a x := by
  funext π
  show ∑ π', (a π π').1 (c • x π') = c • ∑ π', (a π π').1 (x π')
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun _ _ => map_smul _ _ _

theorem jd_actA_zeroR (a : MA.A P (MA.DQ P)) : MA.actA P a 0 = 0 := by
  have h := jd_actA_smulR P a 0 0
  rw [zero_smul, zero_smul] at h
  exact h

theorem jd_actA_listsum {ι : Type} (a : MA.A P (MA.DQ P)) (l : List ι) (g : ι → M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P a (l.map g).sum = (l.map fun i => MA.actA P a (g i)).sum := by
  induction l with
  | nil => simp only [List.map_nil, List.sum_nil]; exact jd_actA_zeroR P a
  | cons i l ih => rw [List.map_cons, List.sum_cons, jd_actA_addR, ih, List.map_cons, List.sum_cons]

variable {P}

theorem jd_word_span {Fn : Type} (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (Good : ℕ → Fn → Prop)
    (tr : Fn → M.Ty P → MA.SmQ P.r P.TT) (m : ℕ)
    (hBdd : ∀ X ∈ MA.hatSet P L, ∀ b ∈ Submonoid.closure (MA.bddSet P L), X * b ∈ Submodule.span ℂ (bddHat P L))
    (hStep : ∀ i, i < m → ∀ F, Good i F → ∀ X ∈ MA.hatSet P L,
      ∃ ts : List (MA.A P (MA.DQ P) × Fn), (∀ t ∈ ts, t.1 ∈ Submonoid.closure (MA.bddSet P L) ∧ Good (i + 1) t.2) ∧
        MA.actA P X (tr F) = (ts.map fun t => MA.actA P t.1 (tr t.2)).sum) :
    ∀ w : List (MA.A P (MA.DQ P)), w.length ≤ m → (∀ a ∈ w, a ∈ MA.hatSet P L) → ∀ F, Good 0 F →
      MA.actA P w.prod (tr F) ∈ Submodule.span ℂ
        {u | ∃ b ∈ Submonoid.closure (MA.bddSet P L), ∃ F', Good w.length F' ∧ u = MA.actA P b (tr F')} := by
  intro w
  induction w with
  | nil =>
    intro _ _ F hF
    refine Submodule.subset_span ⟨1, Submonoid.one_mem _, F, hF, ?_⟩
    rw [List.prod_nil, actA_one]
  | cons a w ih =>
    intro hlen hw F hF
    have ha : a ∈ MA.hatSet P L := hw a (List.mem_cons_self ..)
    have hlt : w.length < m := by simp only [List.length_cons] at hlen; omega
    have hIH := ih hlt.le (fun x hx => hw x (List.mem_cons_of_mem _ hx)) F hF
    rw [List.prod_cons, actA_mul]
    have hgen : ∀ c ∈ Submodule.span ℂ (bddHat P L), ∀ F', Good w.length F' →
        MA.actA P c (tr F') ∈ Submodule.span ℂ
          {u | ∃ b ∈ Submonoid.closure (MA.bddSet P L), ∃ F', Good (a :: w).length F' ∧ u = MA.actA P b (tr F')} := by
      intro c hc F' hF'
      induction hc using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨b', hb', X', hX', rfl⟩ := hx
        obtain ⟨ts, hts, he⟩ := hStep w.length hlt F' hF' X' hX'
        rw [actA_mul, he, jd_actA_listsum]
        refine list_sum_mem fun u hu => ?_
        obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hu
        rw [← actA_mul]
        exact Submodule.subset_span ⟨b' * t.1, Submonoid.mul_mem _ hb' (hts t ht).1, t.2, (hts t ht).2, rfl⟩
      | zero => rw [jd_actA_zero]; exact Submodule.zero_mem _
      | add x y _ _ h1 h2 => rw [jd_actA_add]; exact Submodule.add_mem _ h1 h2
      | smul c x _ h1 => rw [actA_smul]; exact Submodule.smul_mem _ c h1
    have key : ∀ x ∈ Submodule.span ℂ
        {u | ∃ b ∈ Submonoid.closure (MA.bddSet P L), ∃ F', Good w.length F' ∧ u = MA.actA P b (tr F')},
        MA.actA P a x ∈ Submodule.span ℂ
          {u | ∃ b ∈ Submonoid.closure (MA.bddSet P L), ∃ F', Good (a :: w).length F' ∧ u = MA.actA P b (tr F')} := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨b, hb, F', hF', rfl⟩ := hx
        rw [← actA_mul]
        exact hgen _ (hBdd a ha b hb) F' hF'
      | zero => rw [jd_actA_zeroR]; exact Submodule.zero_mem _
      | add x y _ _ h1 h2 => rw [jd_actA_addR]; exact Submodule.add_mem _ h1 h2
      | smul c x _ h1 => rw [jd_actA_smulR]; exact Submodule.smul_mem _ c h1
    exact key _ hIH

variable (P)

theorem jd_evQ_meas (g : MA.SmQ P.r P.TT) : AEStronglyMeasurable (MA.evQ P g) (MA.mu0 P.r P.TT) := by
  have hs : ContDiffOn ℝ MA.sm (MA.ext (g : MA.Qp P.r P.TT → ℂ)) (MA.Qset P.r P.TT) := g.2
  have h2 := hs.continuousOn.comp_continuous continuous_subtype_val (fun q => q.2)
  have hc : Continuous (MA.evQ P g) := h2.congr fun q => by
    simp only [Function.comp, MA.ext, dif_pos q.2]
    rfl
  exact hc.aestronglyMeasurable

def componentwiseL2 (u : M.Ty P → MA.SmQ P.r P.TT) : Prop := ∀ π, MemLp (MA.evQ P (u π)) 2 (MA.mu0 P.r P.TT)

theorem componentwiseL2_iff_integrable (u : M.Ty P → MA.SmQ P.r P.TT) :
    componentwiseL2 P u ↔ ∀ π, Integrable (fun q => ‖MA.evQ P (u π) q‖ ^ 2) (MA.mu0 P.r P.TT) :=
  forall_congr' fun π => memLp_two_iff_integrable_sq_norm (jd_evQ_meas P (u π))

theorem componentwiseL2_of_span (G : Set (M.Ty P → MA.SmQ P.r P.TT)) (h : ∀ u ∈ G, componentwiseL2 P u) :
    ∀ u ∈ Submodule.span ℂ G, componentwiseL2 P u := by
  intro u hu
  induction hu using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => intro π; exact MemLp.zero
  | add x y _ _ h1 h2 => intro π; exact (h1 π).add (h2 π)
  | smul c x _ h1 => intro π; exact (h1 π).const_smul c

end gen

theorem jd_arith (C2 C3 C5 R n N A₀ : ℝ) (hC2 : 0 ≤ C2) (hR : 0 ≤ R) (hn : 1 ≤ n) (hN : 0 ≤ N)
    (hA : (8 * C2 + |C3| + |C5|) * (R + 1) ^ 4 * (N * n ^ 2 + n ^ 3) ≤ A₀) :
    (∀ i o : ℝ, i + 1 ≤ 2 * N + 2 → o ≤ C2 * n →
      C3 * (R + 1) * n ^ 2 + 6 * R * o + C2 * (R + 1) * n ≤ A₀ - i * (C2 * (R + 1) * n)) ∧
      (∀ i : ℝ, i ≤ 2 * N + 2 → C5 * (R + 1) ^ 2 * n ≤ A₀ - i * (C2 * (R + 1) * n)) := by
  have hρ : 1 ≤ R + 1 := by linarith
  have hρ0 : 0 ≤ R + 1 := by linarith
  have hn0 : 0 ≤ n := by linarith
  have hρ4 : R + 1 ≤ (R + 1) ^ 4 := le_self_pow₀ hρ (by norm_num)
  have hR4 : R ≤ (R + 1) ^ 4 := by linarith
  have hρ24 : (R + 1) ^ 2 ≤ (R + 1) ^ 4 := pow_le_pow_right₀ hρ (by norm_num)
  have hn2 : n ≤ n ^ 2 := le_self_pow₀ hn (by norm_num)
  have hn3 : n ≤ n ^ 3 := le_self_pow₀ hn (by norm_num)
  have hn23 : n ^ 2 ≤ n ^ 3 := pow_le_pow_right₀ hn (by norm_num)
  have hNn : 0 ≤ N * n ^ 2 := by positivity
  set X : ℝ := (R + 1) ^ 4 * (N * n ^ 2 + n ^ 3) with hX
  have hX0 : 0 ≤ X := by positivity
  have hY : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a ≤ (R + 1) ^ 4 → b ≤ n ^ 3 → a * b ≤ X := by
    intro a b ha hb h1 h2
    calc a * b ≤ (R + 1) ^ 4 * n ^ 3 := mul_le_mul h1 h2 hb (by positivity)
      _ ≤ X := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hXa : (R + 1) * n ^ 2 ≤ X := hY _ _ hρ0 (by positivity) hρ4 hn23
  have hXa' : (R + 1) ^ 2 * n ≤ X := hY _ _ (by positivity) hn0 hρ24 hn3
  have hXc : R * n ≤ X := hY _ _ hR hn0 hR4 hn3
  have hXb : (2 * N + 2) * ((R + 1) * n) ≤ 2 * X := by
    have h1' : N * n ≤ N * n ^ 2 := mul_le_mul_of_nonneg_left hn2 hN
    have h2' : (R + 1) * (N * n + n) ≤ (R + 1) ^ 4 * (N * n ^ 2 + n ^ 3) :=
      mul_le_mul hρ4 (by linarith) (by positivity) (by positivity)
    have e : (2 * N + 2) * ((R + 1) * n) = 2 * ((R + 1) * (N * n + n)) := by ring
    rw [e, hX]; linarith
  have hdm0 : 0 ≤ C2 * (R + 1) * n := by positivity
  have e2 : (2 * N + 2) * (C2 * (R + 1) * n) ≤ 2 * C2 * X := by
    have := mul_le_mul_of_nonneg_left hXb hC2
    have e : (2 * N + 2) * (C2 * (R + 1) * n) = C2 * ((2 * N + 2) * ((R + 1) * n)) := by ring
    rw [e]; linarith
  have e3 : C3 * (R + 1) * n ^ 2 ≤ |C3| * X :=
    calc C3 * (R + 1) * n ^ 2 = C3 * ((R + 1) * n ^ 2) := by ring
      _ ≤ |C3| * ((R + 1) * n ^ 2) := mul_le_mul_of_nonneg_right (le_abs_self C3) (by positivity)
      _ ≤ |C3| * X := mul_le_mul_of_nonneg_left hXa (abs_nonneg C3)
  have e3' : C5 * (R + 1) ^ 2 * n ≤ |C5| * X :=
    calc C5 * (R + 1) ^ 2 * n = C5 * ((R + 1) ^ 2 * n) := by ring
      _ ≤ |C5| * ((R + 1) ^ 2 * n) := mul_le_mul_of_nonneg_right (le_abs_self C5) (by positivity)
      _ ≤ |C5| * X := mul_le_mul_of_nonneg_left hXa' (abs_nonneg C5)
  have e4 : 0 ≤ |C5| * X := mul_nonneg (abs_nonneg _) hX0
  have e4' : 0 ≤ |C3| * X := mul_nonneg (abs_nonneg _) hX0
  have hA2 : (8 * C2 + |C3| + |C5|) * X ≤ A₀ := by
    have e : (8 * C2 + |C3| + |C5|) * X = (8 * C2 + |C3| + |C5|) * (R + 1) ^ 4 * (N * n ^ 2 + n ^ 3) := by
      rw [hX]; ring
    rw [e]; exact hA
  have hsplit : (8 * C2 + |C3| + |C5|) * X = 2 * C2 * X + 6 * C2 * X + |C3| * X + |C5| * X := by ring
  have e6 : 0 ≤ 6 * C2 * X := by positivity
  constructor
  · intro i o hi ho
    have e1 : (i + 1) * (C2 * (R + 1) * n) ≤ (2 * N + 2) * (C2 * (R + 1) * n) := mul_le_mul_of_nonneg_right hi hdm0
    have e5 : 6 * R * o ≤ 6 * C2 * X := by
      have h1 : R * o ≤ R * (C2 * n) := mul_le_mul_of_nonneg_left ho hR
      have h2 : R * (C2 * n) = C2 * (R * n) := by ring
      have h3 : C2 * (R * n) ≤ C2 * X := mul_le_mul_of_nonneg_left hXc hC2
      linarith
    have e : C3 * (R + 1) * n ^ 2 + 6 * R * o + C2 * (R + 1) * n + i * (C2 * (R + 1) * n) =
        C3 * (R + 1) * n ^ 2 + 6 * R * o + (i + 1) * (C2 * (R + 1) * n) := by ring
    linarith
  · intro i hi
    have e1 : i * (C2 * (R + 1) * n) ≤ (2 * N + 2) * (C2 * (R + 1) * n) := mul_le_mul_of_nonneg_right hi hdm0
    linarith

end

end Formalism.FourierDecayAlt.P.CutMP
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAStarOp2
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

noncomputable section

def SAModelAdj : Prop :=
  ∀ (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r), 0 < P.TT → MA.IsModelLevel P (MA.DQ P) L →
    ∀ a ∈ Submonoid.closure (MA.hatSet P L ∪ MA.bddSet P L), ∀ u U : M.Ty P → MA.SmQ P.r P.TT,
      (∀ π, U π ∈ MA.Test P.r P.TT) → MA.ipA P (MA.actA P (star a) u) U = MA.ipA P u (MA.actA P a U)

def SASection : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), IsFrame S T v e →
      ∀ U : M.Ty (D.parOf S v) → MA.SmQ (D.parOf S v).r (D.parOf S v).TT,
        (∀ π, U π ∈ MA.Test (D.parOf S v).r (D.parOf S v).TT) → ∃ K ∈ smoothFormsPositiveCone S T v, trJ S T v e K = U

def SAPairL : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), IsFrame S T v e →
      ∀ Θs : List (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))), (∀ Θ ∈ Θs, IsAAOp S T v Θ) →
      ∀ K ∈ smoothFormsPositiveCone S T v, ∀ J ∈ smoothFormsPositiveCone S T v, (∀ π, trJ S T v e K π ∈ MA.Test (D.parOf S v).r (D.parOf S v).TT) →
        (∀ π, trJ S T v e (applyL S v Θs K) π ∈ MA.Test (D.parOf S v).r (D.parOf S v).TT) ∧
          MA.ipA (D.parOf S v) (trJ S T v e (applyL S v Θs K)) (trJ S T v e J) =
            MA.ipA (D.parOf S v) (trJ S T v e K) (trJ S T v e (adjL S v Θs J))

def SAFundQ : Prop :=
  ∀ (P : M.Par) (u w : M.Ty P → MA.SmQ P.r P.TT),
    (∀ U : M.Ty P → MA.SmQ P.r P.TT, (∀ π, U π ∈ MA.Test P.r P.TT) → MA.ipA P u U = MA.ipA P w U) → u = w

section lin

variable {P : M.Par}

open Formalism.FourierDecayAlt.P.MAx2.Adj

theorem ipA_add_left (u w U : M.Ty P → MA.SmQ P.r P.TT) (hU : ∀ π, U π ∈ MA.Test P.r P.TT) :
    MA.ipA P (u + w) U = MA.ipA P u U + MA.ipA P w U := by
  unfold MA.ipA
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun π _ => ?_
  calc MA.ip0 ((u + w) π) (U π) = conj (MA.ip0 (U π) (u π + w π)) := inner_conj_symm_alt _ _
    _ = conj (MA.ip0 (U π) (u π)) + conj (MA.ip0 (U π) (w π)) := by rw [inner_add_right_alt (hU π), map_add (f := _)]
    _ = MA.ip0 (u π) (U π) + MA.ip0 (w π) (U π) := by rw [← inner_conj_symm_alt, ← inner_conj_symm_alt]

theorem ipA_add_right (u X Y : M.Ty P → MA.SmQ P.r P.TT) (hX : ∀ π, X π ∈ MA.Test P.r P.TT)
    (hY : ∀ π, Y π ∈ MA.Test P.r P.TT) : MA.ipA P u (X + Y) = MA.ipA P u X + MA.ipA P u Y := by
  unfold MA.ipA
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun π _ => ?_
  calc MA.ip0 (u π) ((X + Y) π) = conj (MA.ip0 (X π + Y π) (u π)) := inner_conj_symm_alt _ _
    _ = conj (MA.ip0 (X π) (u π)) + conj (MA.ip0 (Y π) (u π)) := by rw [inner_add_left_alt (hX π) (hY π), map_add (f := _)]
    _ = MA.ip0 (u π) (X π) + MA.ip0 (u π) (Y π) := by rw [← inner_conj_symm_alt, ← inner_conj_symm_alt]

theorem ipA_smul_left (c : ℂ) (u U : M.Ty P → MA.SmQ P.r P.TT) : MA.ipA P (c • u) U = c * MA.ipA P u U := by
  unfold MA.ipA
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun π _ => inner_smul_left_alt c (u π) (U π)

theorem ipA_smul_right (c : ℂ) (u U : M.Ty P → MA.SmQ P.r P.TT) :
    MA.ipA P u (c • U) = conj c * MA.ipA P u U := by
  unfold MA.ipA
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun π _ => inner_smul_right_alt c (u π) (U π)

theorem ipA_conj (u U : M.Ty P → MA.SmQ P.r P.TT) : MA.ipA P u U = conj (MA.ipA P U u) := by
  unfold MA.ipA
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl fun π _ => inner_conj_symm_alt _ _

theorem sumAdj (u Ku : M.Ty P → MA.SmQ P.r P.TT) (hKu : ∀ π, Ku π ∈ MA.Test P.r P.TT) {α : Type*} (l : List α)
    (c : α → ℂ) (X Y : α → M.Ty P → MA.SmQ P.r P.TT)
    (h : ∀ x ∈ l, (∀ π, X x π ∈ MA.Test P.r P.TT) ∧ MA.ipA P (X x) u = MA.ipA P Ku (Y x)) :
    (∀ π, (l.map fun x => c x • X x).sum π ∈ MA.Test P.r P.TT) ∧
      MA.ipA P u (l.map fun x => c x • X x).sum = MA.ipA P (l.map fun x => conj (c x) • Y x).sum Ku := by
  induction l with
  | nil =>
    refine ⟨fun π => ?_, ?_⟩
    · simpa using (test_zero : (0 : MA.SmQ P.r P.TT) ∈ MA.Test P.r P.TT)
    · simp [MA.ipA, inner_zero_left_alt, inner_zero_right_alt]
  | cons x l ih =>
    obtain ⟨hX, hXe⟩ := h x (by simp)
    obtain ⟨ihT, ihE⟩ := ih (fun y hy => h y (by simp [hy]))
    simp only [List.map_cons, List.sum_cons]
    refine ⟨fun π => test_add (test_smul _ (hX π)) (ihT π), ?_⟩
    rw [ipA_add_right u (c x • X x) _ (fun π => test_smul (c x) (hX π)) ihT, ipA_add_left (conj (c x) • Y x) _ Ku hKu, ipA_smul_right,
      ipA_smul_left, ihE, ipA_conj u (X x), hXe, ← ipA_conj]

end lin

theorem jAStarOp_of_parts (hM : SAModelAdj) (hS : SASection) (hP : SAPairL) (hF : SAFundQ) : JAStarOp := by
  obtain ⟨C1, hS'⟩ := hS
  obtain ⟨C2, hP'⟩ := hP
  refine ⟨max C1 C2, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e L he _ hL a ha ts hts hrep J hJ
  have hB1 : BuiltOW C1 S T f χ ν' m₀ top A₀ := ⟨isBuiltPlace_mono (le_max_left _ _) hB.1, hB.2⟩
  have hB2 : BuiltOW C2 S T f χ ν' m₀ top A₀ := ⟨isBuiltPlace_mono (le_max_right _ _) hB.1, hB.2⟩
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hTT : (D.parOf S v).TT = Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z' := by
    rw [hPl.2.2.2.1, hPl.2.2.2.2.1]; rfl
  have hTTpos : 0 < (D.parOf S v).TT := by rw [hTT]; exact mul_pos (T v).base.T_pos (T v).base.T'_pos
  apply hF (D.parOf S v)
  intro U hU
  obtain ⟨K, hK, hKU⟩ := hS' E Wp Wq S T f χ ν' m₀ top A₀ hB1 v e he U hU
  subst hKU
  rw [hM _ L hTTpos hL a ha (trJ S T v e J) (trJ S T v e K) hU, (hrep K hK).2]
  exact (sumAdj (trJ S T v e J) (trJ S T v e K) hU ts (fun t => t.1) (fun t => trJ S T v e (applyL S v t.2 K))
    (fun t => trJ S T v e (adjL S v t.2 J))
    (fun t ht => hP' E Wp Wq S T f χ ν' m₀ top A₀ hB2 v e he t.2 (hts t ht) K hK J hJ hU)).2

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSLocal
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem gTSSLocal_of_radT : GTCLRadT → GTSSLocal := by
  intro hT Wp Wq _ _ _ _ _ _ P Bs X d hG e he _
  obtain ⟨hP, hk, hC, -⟩ := id hG
  have hX : ∀ (Y : ℂ) (a b : Fin 2), SliceLoc P Bs (X.t Y a b) := fun Y a b =>
    second_shift_slice_derivative Wp Wq P Bs hP _ (hT Wp Wq P Bs hP hk hC X Y a b)
  exact second_shift_matrix_form Wp Wq P Bs X d hG e he
    (second_shift_slice_operator Wp Wq P Bs X d hG hX)

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJfSmoothCut
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JfS

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section ellreg

variable {d : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

end ellreg

def lieOf {k r : ℕ} (Sx : Set (B.Mat k r)) : Set (B.Mat k r) :=
  {X | ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Sx}

def OmQ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : Set (B.Mat k r) :=
  {g | 0 < Gf k r z z' g ∧ ∀ a : Fin r, Dmin k r z z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0}

def SymbolNil : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' →
    ∀ g ∈ B.GV k r, g ∈ OmQ k r z z' → ∀ ξ : B.Mat k r, B.inLie k r ξ → IsNilpotent ξ →
      (∀ X ∈ lieOf (Sset k r z), (Matrix.trace (ξ * X)).re = 0) →
      (∀ X ∈ lieOf (Sset k r z'), (Matrix.trace (ξ * (g * X * g⁻¹))).re = 0) →
      ξ = 0

theorem lieOf_mono {k r : ℕ} {A B' : Set (B.Mat k r)} (h : A ⊆ B') : lieOf A ⊆ lieOf B' :=
  fun _ hX t => h (hX t)

theorem UWset_sub_Sset (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : UWset k r z ⊆ Sset k r z :=
  fun h hh => ⟨h, hh, 1, (nSubgroup k r).1, by simp⟩

end

end Formalism.FourierDecayAlt.P.CutMP.JfS
end
