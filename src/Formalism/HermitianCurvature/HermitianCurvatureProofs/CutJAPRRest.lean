module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFHypS
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRTWNe
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCPPSCalc
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LowerUnipotentHasRepresentation
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRPHPhaseInvOfCut

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCPCoreAsm
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q NumberField
open scoped ComplexConjugate Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP

noncomputable section

theorem glc_single (k r : ℕ) (a b : Fin (k + 1)) : GLc k r (Matrix.single (wI k r a) (wI k r b) 1) := by
  have hm : mdim k r (Fin.last r) = k + 1 := by simp [mdim]
  have h := Formalism.FourierDecayAlt.P.Qx2.hpart_lev (k := k) (r := r) (Fin.last r) (Fin.cast hm.symm a) (Fin.cast hm.symm b)
  have ea : posL k r (Fin.last r) (Fin.cast hm.symm a) = wI k r a := by
    ext; simp [posL, wI, Fin.val_last]; omega
  have eb : posL k r (Fin.last r) (Fin.cast hm.symm b) = wI k r b := by
    ext; simp [posL, wI, Fin.val_last]; omega
  rw [ea, eb] at h
  exact h

theorem radSp_smoothLev {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
    [NormedSpace ℂ Wq] {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Q.Mx k r → (Wp →L[ℂ] Wp)}
    {π' : Q.Mx k r → (Wq →L[ℂ] Wq)} (Φ : Q.RadSp k r z z' π π') {c : Fin r → ℂ} (hc : c ∈ OmX r) :
    Q.SmoothLev k r (Fin.last r) (Dp k r z z') ((Φ : Q.Fn k r (Wq →L[ℂ] Wp)) c) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hxU, hF, hΦ⟩ := Φ.2.2.1 (c, g₀) ⟨hc, hg₀.1, hg₀.2⟩
  refine ⟨{g | (c, g) ∈ U}, fun g => F (c, g), hU.preimage (continuous_const.prodMk continuous_id), hxU, ?_, ?_⟩
  · exact hF.comp (contDiffOn_const.prodMk contDiffOn_id) (fun g hg => hg)
  · intro g hg hgl
    exact hΦ (c, g) hg hgl

theorem psv_congr {TT : ℝ} {V : Type*} [AddCommGroup V] [Module ℂ V] {f g : ℂ → V} (hf : PSV TT f)
    (h : ∀ ζ : ℂ, TT < Complex.normSq ζ → g ζ = f ζ) : PSV TT g := by
  obtain ⟨n, a, v, ha, hfe⟩ := hf
  exact ⟨n, a, v, ha, fun ζ hζ => by rw [h ζ hζ]; exact hfe ζ hζ⟩

theorem psv_sum {TT : ℝ} {V : Type*} [AddCommGroup V] [Module ℂ V]
    (hadd : ∀ f g : ℂ → V, PSV TT f → PSV TT g → PSV TT (fun ζ => f ζ + g ζ)) (h0 : PSV TT (fun _ => (0 : V)))
    {ι : Type*} (s : Finset ι) (F : ι → ℂ → V) (hF : ∀ i ∈ s, PSV TT (F i)) :
    PSV TT (fun ζ => ∑ i ∈ s, F i ζ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | @insert a s ha ih =>
    have := hadd _ _ (hF a (Finset.mem_insert_self a s)) (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))
    refine psv_congr this fun ζ _ => ?_
    simp [Finset.sum_insert ha]

theorem radial_polynomial_of_truncation : CorePolyOfCut := by
  intro hT hW hC Wp Wq _ _ _ _ _ _ P Bs hpl hk hsec Φ X₀ hX c hc Y
  have hTz : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' = P.TT := Gauge.GC.tz_TT P Bs hpl
  obtain ⟨n, κ, w, hκ, hw, hid⟩ := hT P.k P.r Bs.z Bs.z' Bs.k_pos Bs.z_mem Bs.z'_mem Bs.T_pos Bs.T'_pos Y
  rw [hTz] at hκ
  have hsm := radSp_smoothLev Φ hc
  have hwords : ∀ i, PSV P.TT (fun ζ =>
      wordR (w i) ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c) (NF.muZ P.k P.r Bs.μsec ζ)) := by
    intro i
    refine hW Wp Wq P Bs hpl hk hsec Φ X₀ hX c hc (w i) (fun Z hZ => ?_)
    obtain ⟨a, b, rfl⟩ := hw i Z hZ
    exact glc_single P.k P.r a b
  have hTT : 0 < P.TT := by rw [← hTz]; exact mul_pos Bs.T_pos Bs.T'_pos
  obtain ⟨-, -, -, -, -, -, -, hV⟩ := hC P.TT hTT
  obtain ⟨hadd, hsmul, -, -, hconst⟩ := hV (Wq →L[ℂ] Wp) (Wq →L[ℂ] Wp)
  have hsum := psv_sum hadd (hconst 0) Finset.univ
    (fun i ζ => κ i ζ • wordR (w i) ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c) (NF.muZ P.k P.r Bs.μsec ζ))
    (fun i _ => hsmul _ _ (hκ i) (hwords i))
  refine psv_congr hsum fun ζ hζ => ?_
  have hζ' : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ := by rw [hTz]; exact hζ
  have := hid (Wq →L[ℂ] Wp) ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c) hsm ζ hζ'
  simp only [mu0] at this
  rw [hsec]
  exact this

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRKapLine
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR

noncomputable section

theorem kappa_line_holds : KapLine := by
  intro Wp Wq _ _ _ _ _ _ P Bs hμs hk X d hA Pr hPr
  obtain ⟨hpl, hL, hS, hRel, hQQ⟩ := id hA
  have hcs := Formalism.FourierDecayAlt.P.TheSecStab.theSection_csec (k := P.k) (r := P.r) (by omega) Bs.z_mem Bs.z'_mem
    Bs.T_pos Bs.T'_pos
  rw [← hμs] at hcs
  have hH : Gauge.GC.GTHyp P Bs X d := ⟨hpl, hk, hcs, hL, hS, hRel, hQQ⟩
  obtain ⟨Qs, hK⟩ := Gauge.GC.gauge_kappa_pointwise_holds Wp Wq P Bs X d hH
  refine ⟨Qs, hK, ?_⟩
  intro ζ hζ Xf hXf ρ
  have hζT : P.TT < Complex.normSq ζ := hζ
  obtain ⟨hOK, hz, hz', hTz, hTz', -, -⟩ := id hpl
  have hζ' : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ := by
    rw [hTz, hTz']; exact hζT
  have hT := Bs.T_pos
  have hT' := Bs.T'_pos
  obtain ⟨hνfix, hνν, -, -⟩ := DU.base hz hz' Bs.T_pos Bs.T'_pos Bs.sec hζ'
  set ν := SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ with hνdef
  set μ := NF.muZ P.k P.r Bs.μsec ζ with hμ
  have hm := NFRadRedA.muZ_uwb Bs.sec hζ'
  have hG := NFRadRedA.uwb_glev hm
  have hy : inWb P.k P.r (μ *ᵥ Bs.z') := Qx8.inWb_mulVec hG hz'
  have hνW : inWb P.k P.r ν := by
    show inWb P.k P.r (SSn.unitH P.k P.r (SSn.prWv P.k P.r Bs.z (μ *ᵥ Bs.z')))
    unfold SSn.unitH
    exact Qx8.inWb_smul (DU.prWv_inWb hz hy) _
  have hνz : herm (Hpk P.k P.r) ν Bs.z = 0 := by
    rw [← hνfix]; exact DU.prWv_perp hT hνW
  obtain ⟨Fr, hFr⟩ := Topx1.typ_frame_exists P.k P.r (by omega) Bs.z ν hz hT hνW hνz hνν
  obtain ⟨hFr', hpass⟩ := PRho.GL.gauge_left_line_holds Wp Wq P Bs hpl hk ζ hζT Fr hFr
  have hgl' := (Formalism.FourierDecayAlt.P.frame_general_linear Wq P.k P.r (P.k - 1) Bs.z' Bs.π'
    (fun a => μ⁻¹ *ᵥ Fr a) ⟨Bs.π'_rep, Bs.π'_cont⟩
    (Formalism.FourierDecayAlt.P.Qx8.frame_sub hFr' (by simp))).2
  have hπrep : Qr.IsRepW P.k P.r Bs.z Bs.π := ⟨Bs.π_rep, Bs.π_cont⟩
  have hpos : 0 < PRho.nrmW P.k P.r Bs.z ν := by
    unfold PRho.nrmW
    rw [hνfix, hνν]; simp

  set c0 : Fin P.r → ℂ := fun _ => 1 with hc0def
  have hq : ((c0, ζ) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨fun _ => one_ne_zero, hζ'⟩
  set φ : (Fin P.r → ℂ) × ℂ → (Wq →L[ℂ] Wp) := (NF.QR P.k P.r Bs.z Bs.z').indicator (fun _ => Xf) with hφdef
  have hφ : φ ∈ NF.RadSec P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' := by
    refine ⟨?_, ?_, ?_⟩
    · exact contDiffOn_const.congr (fun q hq' => Set.indicator_of_mem hq' _)
    · intro q hq'
      rw [hφdef, Set.indicator_of_mem hq']
      have hst := hcs.2 q.2 ζ hq'.2 hζ'
      intro p hp
      exact hXf p (hst ▸ hp)
    · intro q hq'
      exact Set.indicator_of_notMem hq' _
  have hbase : NF.RadBase P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' :=
    ⟨by omega, hz, hz', hT, hT', hcs.1, Bs.π_rep, Bs.π'_rep, Bs.π_cont, Bs.π'_cont⟩
  obtain ⟨Φ, hΦ, hΦr⟩ := Formalism.FourierDecayAlt.P.radical_reduction_surjective Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hbase φ hφ
  have hval : Φ c0 μ = Xf := by
    have h1 := congrFun hΦr (c0, ζ)
    simp only [NF.radR, Set.indicator_of_mem hq, hφdef] at h1
    exact h1
  have hx : (c0, μ) ∈ Q.DomR P.k P.r Bs.z Bs.z' := Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' hcs.1 hq
  set Φ' : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' := ⟨Φ, hΦ⟩ with hΦ'def
  let qq : MA.Qp P.r P.TT := ⟨(c0, ζ), ⟨fun _ => one_ne_zero, hζT⟩⟩

  have hfib : ∀ σ, Xf.comp (Qs σ) ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ := by
    intro σ
    have h1 := hK.2.2.2 (fun τ => if τ = σ then 1 else 0) Φ' qq
    have h2 : (∑ τ, (if τ = σ then (1 : ℂ) else 0) • Qs τ) = Qs σ := by
      simp [ite_smul]
    rw [h2] at h1
    change (((d.κ fun τ => if τ = σ then 1 else 0).1 Φ' : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
      Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c0 μ = (Φ c0 μ).comp (Qs σ) at h1
    rw [hval] at h1
    rw [← h1]
    intro p hp
    have h := ((d.κ fun τ => if τ = σ then 1 else 0).1 Φ').2.2.2 _ hx p.1 hp.1 p.2 hp.2.1
    simp only at h
    rw [hp.2.2] at h
    exact h.symm

  have hfix : ∀ σ, (Pr σ ν).comp (Xf.comp (Qs σ)) = Xf.comp (Qs σ) := by
    intro σ
    have hE : (Xf.comp (Qs σ)).comp (Qs σ) = Xf.comp (Qs σ) := by
      rw [ContinuousLinearMap.comp_assoc, hK.1 σ σ, if_pos rfl]
    have hEeig := (Gauge.GC.lie_eigenvalue_holds Wp Wq P Bs X d hH Qs hK ζ hζT _ hFr' σ _ (hfib σ)).1 hE
    ext v
    rw [ContinuousLinearMap.comp_apply]
    refine ((hPr.2.2 ν hpos).2.2.2 σ _).2 ?_
    intro Fr2 hFr2 w
    rw [hνfix] at hFr2
    rw [Topx1.typ_frame_change P.k P.r (by omega) Bs.z ν Bs.π Fr2 Fr hz hT hνW hνz hνν hπrep hFr2 hFr w
      ((Xf.comp (Qs σ)) v), hpass _ (hfib σ) w v, hgl']
    have hw : w = (w - ((P.k : ℂ) - 2) / 2) + ((P.k : ℂ) - 2) / 2 := by ring
    conv_lhs => rw [hw]
    exact hEeig _ v
  have hs : Xf = ∑ σ, Xf.comp (Qs σ) := by
    rw [← ContinuousLinearMap.comp_finsetSum, hK.2.1]
    rfl
  have hPP := (hPr.2.2 ν hpos).2.2.1
  conv_lhs => rw [hs]
  rw [ContinuousLinearMap.comp_finsetSum, Finset.sum_eq_single ρ]
  · exact hfix ρ
  · intro σ _ hσ
    rw [← hfix σ, ← ContinuousLinearMap.comp_assoc, hPP ρ σ, if_neg (Ne.symm hσ), ContinuousLinearMap.zero_comp]
  · intro h
    exact absurd (Finset.mem_univ ρ) h

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCPRightCov
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
open scoped Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP

noncomputable section

theorem rdV_rightCov {k r : ℕ} {z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
    [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    {π' : Q.Mx k r → (Wq →L[ℂ] Wq)} (hπ : IsCRepOn (UWset k r z') π') (hc : ContinuousOn π' (UWset k r z'))
    {D : Set (Q.Mx k r)} {F : Q.Mx k r → (Wq →L[ℂ] Wp)}
    (hF : ∀ h ∈ UWset k r z', ∀ g ∈ Q.Glev k r (Fin.last r) ∩ D, F (g * h) = (F g).comp (π' h))
    {g : Q.Mx k r} (hg : g ∈ Q.Glev k r (Fin.last r) ∩ D) {X : Q.Mx k r} (hX : P.QrD.InLieW k r z' X) :
    RdV X F g = (F g).comp (P.QrD.dOp π' X) := by
  have key : ∀ t : ℝ, F (g * NormedSpace.exp ((t : ℂ) • X)) = (F g).comp (π' (NormedSpace.exp ((t : ℂ) • X))) :=
    fun t => hF _ (Formalism.FourierDecayAlt.P.QrD.exp_uw hX t) g hg
  unfold Formalism.REAL.RdV
  simp only [key]
  let L : (Wq →L[ℂ] Wq) →L[ℝ] (Wq →L[ℂ] Wp) :=
    (ContinuousLinearMap.compL ℂ Wq Wq Wp (F g)).restrictScalars ℝ
  have hL : ∀ A, L A = (F g).comp A := fun A => rfl
  have hd : HasDerivAt (fun t : ℝ => L (π' (NormedSpace.exp ((t : ℂ) • X)))) (L (P.QrD.dOp π' X)) 0 :=
    L.hasFDerivAt.comp_hasDerivAt 0 (Formalism.FourierDecayAlt.P.QrD.dOp_hasDeriv hπ hc hX)
  simp only [hL] at hd
  exact hd.deriv

theorem right_covariance_holds : RightCov := by
  intro k r z' Wp Wq _ _ _ _ _ _ π' hπ hc _ D F _ _ _ hF g hg A hA
  refine ⟨⟨hA.1.1, hA.2.1⟩, ?_⟩
  unfold Rc P.QrD.ecOp
  rw [rdV_rightCov hπ hc hF hg hA.1, rdV_rightCov hπ hc hF hg hA.2]
  ext v
  simp

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCPLeftCov
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
open scoped Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP

noncomputable section

theorem rdV_leftCov {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
    [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] [FiniteDimensional ℂ Wp]
    {π : Q.Mx k r → (Wp →L[ℂ] Wp)} (hπ : IsCRepOn (UWset k r z) π) (hc : ContinuousOn π (UWset k r z))
    {D : Set (Q.Mx k r)} {F : Q.Mx k r → (Wq →L[ℂ] Wp)}
    (hF : ∀ h ∈ UWset k r z, ∀ g ∈ Q.Glev k r (Fin.last r) ∩ D, F (h * g) = (π h).comp (F g))
    {μ : Q.Mx k r} (hμ : μ ∈ Q.Glev k r (Fin.last r) ∩ D) {X : Q.Mx k r} (hX : P.QrD.InLieW k r z X) :
    RdV (μ⁻¹ * X * μ) F μ = (P.QrD.dOp π X).comp (F μ) := by
  have hU : μᴴ * Hpk k r * μ = Hpk k r := hμ.1.1
  have hdet : IsUnit μ.det := by
    apply Matrix.isUnit_det_of_left_inverse (B := Hpk k r * μᴴ * Hpk k r)
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc μᴴ, hU, Formalism.QuantumDeterminants.GBasic.Hpk_sq]
  have hμu : IsUnit μ := (Matrix.isUnit_iff_isUnit_det μ).mpr hdet
  have key : ∀ t : ℝ, F (μ * NormedSpace.exp ((t : ℂ) • (μ⁻¹ * X * μ))) =
      (π (NormedSpace.exp ((t : ℂ) • X))).comp (F μ) := by
    intro t
    rw [show (t : ℂ) • (μ⁻¹ * X * μ) = μ⁻¹ * ((t : ℂ) • X) * μ by rw [Matrix.mul_smul, Matrix.smul_mul],
      Matrix.exp_conj' μ _ hμu, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul]
    exact hF _ (Formalism.FourierDecayAlt.P.QrD.exp_uw hX t) μ hμ
  unfold Formalism.REAL.RdV
  simp only [key]
  let L : (Wp →L[ℂ] Wp) →L[ℝ] (Wq →L[ℂ] Wp) :=
    ((ContinuousLinearMap.compL ℂ Wq Wp Wp).flip (F μ)).restrictScalars ℝ
  have hL : ∀ A, L A = A.comp (F μ) := fun A => rfl
  have hd : HasDerivAt (fun t : ℝ => L (π (NormedSpace.exp ((t : ℂ) • X)))) (L (P.QrD.dOp π X)) 0 :=
    L.hasFDerivAt.comp_hasDerivAt 0 (Formalism.FourierDecayAlt.P.QrD.dOp_hasDeriv hπ hc hX)
  simp only [hL] at hd
  exact hd.deriv

theorem left_covariance_holds : LeftCov := by
  intro k r z Wp Wq _ _ _ _ _ _ π hπ hc _ D F _ _ _ hF μ hμ B hB
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [P.LeftDerivativeCurves.hpart1_conj hμ.1.1]
    exact P.LeftDerivativeCurves.lie_conj hμ.1 hB.1.1
  · rw [P.LeftDerivativeCurves.hpart2_conj hμ.1.1]
    exact P.LeftDerivativeCurves.lie_conj hμ.1 hB.2.1
  · unfold Rc P.QrD.ecOp
    rw [P.LeftDerivativeCurves.hpart1_conj hμ.1.1, P.LeftDerivativeCurves.hpart2_conj hμ.1.1, rdV_leftCov hπ hc hF hμ hB.1,
      rdV_leftCov hπ hc hF hμ hB.2]
    ext v
    simp

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCPRcSmooth
open Matrix
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem radial_coefficient_smoothness : RcSmooth := by
  intro k r E _ _ D f f' _ hf hf' Z hZ
  refine ⟨?_, ?_, ?_⟩
  · exact Qx2.smooth_add (Qx2.rd_smooth hf hZ.1) (Qx2.smooth_smul (Qx2.rd_smooth hf hZ.2) Complex.I)
  · intro a g hg
    have e : (fun x => a • f x + f' x) = fun x => f' x + a • f x := by
      funext x
      exact add_comm _ _
    show RdV _ (fun x => a • f x + f' x) g + Complex.I • RdV _ (fun x => a • f x + f' x) g =
      a • (RdV _ f g + Complex.I • RdV _ f g) + (RdV _ f' g + Complex.I • RdV _ f' g)
    rw [e, Qx2.rd_lin hf' hf a hg hZ.1, Qx2.rd_lin hf' hf a hg hZ.2, smul_add, smul_add, smul_comm Complex.I a]
    abel
  · intro E' _ _ L g hg
    show RdV _ (fun x => L (f x)) g + Complex.I • RdV _ (fun x => L (f x)) g = L (RdV _ f g + Complex.I • RdV _ f g)
    have e1 : RdV (hpart1 (Hpk k r) Z) (fun y => L (f y)) g = L (RdV _ f g) := Qx5.ntw_rd L hZ.1 f hf g hg
    have e2 : RdV (hpart2 (Hpk k r) Z) (fun y => L (f y)) g = L (RdV _ f g) := Qx5.ntw_rd L hZ.2 f hf g hg
    rw [e1, e2, map_add (f := _), map_smul]

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCPRcLin
open Matrix
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {i : Fin (r + 1)}

theorem lie_rsmul {X : Q.Mx k r} (hX : Q.inLieLev k r i X) (x : ℝ) : Q.inLieLev k r i (x • X) := by
  unfold Formalism.FourierDecayAlt.Q.inLieLev at hX ⊢
  obtain ⟨h1, h2⟩ := hX
  have hs : ∀ v : Fin (2 * r + k + 1) → ℂ, (x • X) *ᵥ v = x • (X *ᵥ v) := fun v => by
    ext j
    simp [Matrix.mulVec, dotProduct, Finset.smul_sum, smul_mul_assoc, mul_assoc]
  refine ⟨?_, fun a ha => ⟨?_, ?_⟩⟩
  · rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h1, smul_zero]
  · rw [hs, (h2 a ha).1, smul_zero]
  · rw [hs, (h2 a ha).2, smul_zero]

private theorem inLieLev_add {X Y : Q.Mx k r} (hX : Q.inLieLev k r i X) (hY : Q.inLieLev k r i Y) :
    Q.inLieLev k r i (X + Y) := by
  unfold Formalism.FourierDecayAlt.Q.inLieLev at hX hY ⊢
  refine ⟨?_, fun a ha => ⟨?_, ?_⟩⟩
  · rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add,
      show Xᴴ * Hpk k r + Yᴴ * Hpk k r + (Hpk k r * X + Hpk k r * Y) =
        (Xᴴ * Hpk k r + Hpk k r * X) + (Yᴴ * Hpk k r + Hpk k r * Y) by abel, hX.1, hY.1, add_zero]
  · rw [Matrix.add_mulVec, (hX.2 a ha).1, (hY.2 a ha).1, add_zero]
  · rw [Matrix.add_mulVec, (hX.2 a ha).2, (hY.2 a ha).2, add_zero]

theorem glc_lin {Z Z' : Q.Mx k r} (hZ : GLc k r Z) (hZ' : GLc k r Z') (a : ℂ) : GLc k r (a • Z + Z') := by
  unfold GLc at *
  obtain ⟨h1, h2⟩ := hZ
  obtain ⟨h1', h2'⟩ := hZ'
  have hI : (1 / (2 * Complex.I) : ℂ) = -Complex.I / 2 := by
    field_simp
    ring_nf
    simp only [Complex.I_sq]
    ring
  have hsa : star a = (a.re : ℂ) - (a.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  have ha : a = (a.re : ℂ) + (a.im : ℂ) * Complex.I := (Complex.re_add_im a).symm
  have e1 : hpart1 (Hpk k r) (a • Z + Z') =
      a.re • hpart1 (Hpk k r) Z + (-a.im) • hpart2 (Hpk k r) Z + hpart1 (Hpk k r) Z' := by
    unfold Formalism.QuantumDeterminants.hpart1 Formalism.QuantumDeterminants.hpart2
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hsa, hI,
      show a • Z = ((a.re : ℂ) + (a.im : ℂ) * Complex.I) • Z by rw [← ha]]
    ext i j
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.add_apply,
      Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
    push_cast
    first | ring | (ring_nf; simp only [Complex.I_sq]; ring)
  have e2 : hpart2 (Hpk k r) (a • Z + Z') =
      a.im • hpart1 (Hpk k r) Z + a.re • hpart2 (Hpk k r) Z + hpart2 (Hpk k r) Z' := by
    unfold Formalism.QuantumDeterminants.hpart1 Formalism.QuantumDeterminants.hpart2
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hsa, hI,
      show a • Z = ((a.re : ℂ) + (a.im : ℂ) * Complex.I) • Z by rw [← ha]]
    ext i j
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.add_apply,
      Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
    push_cast
    linear_combination (-(a.im : ℂ) * Z i j / 2 + (a.im : ℂ) * ((Hpk k r)⁻¹ * Zᴴ * Hpk k r) i j / 2) * Complex.I_sq
  rw [e1, e2]
  exact ⟨inLieLev_add (inLieLev_add (lie_rsmul h1 _) (lie_rsmul h2 _)) h1',
    inLieLev_add (inLieLev_add (lie_rsmul h1 _) (lie_rsmul h2 _)) h2'⟩

private theorem hermitian_halves_smul_add (Z Z' : Q.Mx k r) (a : ℂ) :
    hpart1 (Hpk k r) (a • Z + Z') =
      a.re • hpart1 (Hpk k r) Z + (-a.im) • hpart2 (Hpk k r) Z + hpart1 (Hpk k r) Z' ∧
    hpart2 (Hpk k r) (a • Z + Z') =
      a.im • hpart1 (Hpk k r) Z + a.re • hpart2 (Hpk k r) Z + hpart2 (Hpk k r) Z' := by
  have hI : (1 / (2 * Complex.I) : ℂ) = -Complex.I / 2 := by
    field_simp
    ring_nf
    simp only [Complex.I_sq]
    ring
  have hsa : star a = (a.re : ℂ) - (a.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  have ha : a = (a.re : ℂ) + (a.im : ℂ) * Complex.I := (Complex.re_add_im a).symm
  constructor
  · unfold Formalism.QuantumDeterminants.hpart1 Formalism.QuantumDeterminants.hpart2
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hsa, hI,
      show a • Z = ((a.re : ℂ) + (a.im : ℂ) * Complex.I) • Z by rw [← ha]]
    ext i j
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.add_apply,
      Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
    push_cast
    ring
  · unfold Formalism.QuantumDeterminants.hpart1 Formalism.QuantumDeterminants.hpart2
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hsa, hI,
      show a • Z = ((a.re : ℂ) + (a.im : ℂ) * Complex.I) • Z by rw [← ha]]
    ext i j
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.add_apply,
      Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
    push_cast
    linear_combination (-(a.im : ℂ) * Z i j / 2 + (a.im : ℂ) * ((Hpk k r)⁻¹ * Zᴴ * Hpk k r) i j / 2) * Complex.I_sq

private theorem rdV_real_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : Q.Mx k r → E)
    (X g : Q.Mx k r) (s : ℝ) : RdV (s • X) f g = (s : ℂ) • RdV X f g := by
  have hx : ∀ t : ℝ, (t : ℂ) • (s • X) = ((s * t : ℝ) : ℂ) • X := fun t => by
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, Complex.real_smul, Complex.ofReal_mul]
    ring
  unfold Formalism.REAL.RdV
  simp only [hx]
  have key := deriv_comp_mul_left s (fun u : ℝ => f (g * NormedSpace.exp ((u : ℂ) • X))) 0
  simp only [mul_zero] at key
  rw [key, Complex.coe_smul]

private theorem gLc_zero : GLc k r (0 : Q.Mx k r) := by
  unfold GLc Formalism.QuantumDeterminants.hpart1 Formalism.QuantumDeterminants.hpart2 Formalism.FourierDecayAlt.Q.inLieLev
  simp

private theorem rc_zero_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : Q.Mx k r → E) (g : Q.Mx k r) :
    Rc (0 : Q.Mx k r) f g = 0 := by
  unfold Rc Formalism.REAL.RdV Formalism.QuantumDeterminants.hpart1 Formalism.QuantumDeterminants.hpart2
  simp

private theorem rc_smul_add_of_smoothLev_of_gLc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Q.Mx k r)}
    {f : Q.Mx k r → E} (hf : Q.SmoothLev k r (Fin.last r) D f) {g : Q.Mx k r}
    (hg : g ∈ Q.Glev k r (Fin.last r) ∩ D) {Z Z' : Q.Mx k r} (hZ : GLc k r Z) (hZ' : GLc k r Z') (a : ℂ) :
    Rc (a • Z + Z') f g = a • Rc Z f g + Rc Z' f g := by
  obtain ⟨e1, e2⟩ := hermitian_halves_smul_add Z Z' a
  have hz := hZ
  have hz' := hZ'
  unfold GLc at hz hz'
  obtain ⟨h1, h2⟩ := hz
  obtain ⟨h1', h2'⟩ := hz'
  unfold Rc
  rw [e1, e2,
    Formalism.FourierDecayAlt.P.Qx5.rd_addX hf hg (inLieLev_add (lie_rsmul h1 _) (lie_rsmul h2 _)) h1',
    Formalism.FourierDecayAlt.P.Qx5.rd_addX hf hg (lie_rsmul h1 _) (lie_rsmul h2 _),
    Formalism.FourierDecayAlt.P.Qx5.rd_addX hf hg (inLieLev_add (lie_rsmul h1 _) (lie_rsmul h2 _)) h2',
    Formalism.FourierDecayAlt.P.Qx5.rd_addX hf hg (lie_rsmul h1 _) (lie_rsmul h2 _)]
  simp only [rdV_real_smul, Complex.ofReal_neg]
  have haI : a * Complex.I = (a.re : ℂ) * Complex.I - a.im := by
    apply Complex.ext <;> simp
  rw [smul_add a, smul_smul a Complex.I, haI,
    show a • RdV (hpart1 (Hpk k r) Z) f g = ((a.re : ℂ) + (a.im : ℂ) * Complex.I) • RdV (hpart1 (Hpk k r) Z) f g by
      rw [Complex.re_add_im]]
  module

theorem rc_linear {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Q.Mx k r)} {f : Q.Mx k r → E}
    (hf : Q.SmoothLev k r (Fin.last r) D f) {g : Q.Mx k r} (hg : g ∈ Q.Glev k r (Fin.last r) ∩ D) :
    ∃ L : Q.Mx k r →ₗ[ℂ] E, ∀ Z, GLc k r Z → Rc Z f g = L Z := by
  let S : Submodule ℂ (Q.Mx k r) :=
    { carrier := {Z | GLc k r Z}
      add_mem' := fun {Z Z'} hZ hZ' => by simpa using glc_lin hZ hZ' 1
      zero_mem' := gLc_zero
      smul_mem' := fun c Z hZ => by simpa using glc_lin hZ gLc_zero c }
  let f0 : S →ₗ[ℂ] E :=
    { toFun := fun Z => Rc (Z : Q.Mx k r) f g
      map_add' := fun Z Z' => by simpa using rc_smul_add_of_smoothLev_of_gLc hf hg Z.2 Z'.2 1
      map_smul' := fun c Z => by simpa [rc_zero_left] using rc_smul_add_of_smoothLev_of_gLc hf hg Z.2 gLc_zero c }
  obtain ⟨L, hL⟩ := LinearMap.exists_extend f0
  exact ⟨L, fun Z hZ => (LinearMap.congr_fun hL ⟨Z, hZ⟩).symm⟩

theorem radial_coefficient_linearity : RcLin := by
  unfold RcLin
  intro k r E _ _ D f _ hf g hg a Z Z' hZ hZ'
  obtain ⟨L, hL⟩ := rc_linear hf hg
  rw [hL _ (glc_lin hZ hZ' a), hL Z hZ, hL Z' hZ', map_add (f := _), map_smul]

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCPRcComm
open Matrix
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem radial_coefficient_commutation : RcComm := by
  intro k r E _ _ D f _ hf Z₁ Z₂ h₁ h₂ g hg
  exact Qx5.RZ_comm hf hg h₁ h₂

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCPSecDeriv
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
open Matrix Filter Topology
open scoped ComplexConjugate ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace SD

theorem hasDeriv_form {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) {γ : ℝ → Matrix (Fin n) (Fin n) ℂ}
    {g γ' : Matrix (Fin n) (Fin n) ℂ} (h0 : γ 0 = g) (h : ∀ a b, HasDerivAt (fun t => γ t a b) (γ' a b) 0)
    (i j : Fin n) :
    HasDerivAt (fun t => ((γ t)ᴴ * H * γ t) i j) ((γ'ᴴ * H * g + gᴴ * H * γ') i j) 0 := by
  have hγ : ∀ a b, γ 0 a b = g a b := fun a b => by rw [h0]
  have key : ∀ a b, HasDerivAt (fun t => star (γ t a i) * H a b * γ t b j)
      (star (γ' a i) * H a b * g b j + star (g a i) * H a b * γ' b j) 0 := by
    intro a b
    have h1 : HasDerivAt (fun t => star (γ t a i) * H a b * γ t b j)
        (star (γ' a i) * H a b * γ 0 b j + star (γ 0 a i) * H a b * γ' b j) 0 :=
      (((h a i).star).mul_const (H a b)).mul (h b j)
    rw [hγ a i, hγ b j] at h1
    exact h1
  have hs := HasDerivAt.sum (u := Finset.univ) fun b _ =>
    HasDerivAt.sum (u := Finset.univ) fun a _ => key a b
  simp only [Finset.sum_fn] at hs
  have e1 : (fun t => ((γ t)ᴴ * H * γ t) i j) =
      fun t => ∑ b, ∑ a, star (γ t a i) * H a b * γ t b j := by
    funext t
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  have e2 : (γ'ᴴ * H * g + gᴴ * H * γ') i j =
      ∑ b, ∑ a, (star (γ' a i) * H a b * g b j + star (g a i) * H a b * γ' b j) := by
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul,
      Finset.sum_add_distrib]
  rw [e1, e2]
  exact hs

variable {k r : ℕ}

theorem lie_of_curve {μ : ℂ → Q.Mx k r} {ζ : ℂ} {D : ℂ →L[ℝ] Q.Mx k r} (hD : HasFDerivAt μ D ζ)
    (hG : ∀ᶠ w in 𝓝 ζ, μ w ∈ Q.Glev k r (Fin.last r)) (v : ℂ) :
    Q.inLieLev k r (Fin.last r) ((μ ζ)⁻¹ * D v) := by
  have hℓ : HasDerivAt (fun t : ℝ => ζ + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add ζ
  have hγ : HasDerivAt (fun t : ℝ => μ (ζ + t • v)) (D v) 0 := by
    have hD' : HasFDerivAt μ D (ζ + (0 : ℝ) • v) := by simpa using hD
    exact hD'.comp_hasDerivAt (0 : ℝ) hℓ
  have hent : ∀ a b, HasDerivAt (fun t : ℝ => μ (ζ + t • v) a b) (D v a b) 0 := by
    intro a b
    exact hasDerivAt_pi.1 (hasDerivAt_pi.1 hγ a) b
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), μ (ζ + t • v) ∈ Q.Glev k r (Fin.last r) := by
    have ht : Tendsto (fun t : ℝ => ζ + t • v) (𝓝 0) (𝓝 ζ) := by
      simpa using hℓ.continuousAt.tendsto
    exact ht.eventually hG
  have hU : (μ ζ)ᴴ * Hpk k r * μ ζ = Hpk k r := hG.self_of_nhds.1
  have hder : (D v)ᴴ * Hpk k r * μ ζ + (μ ζ)ᴴ * Hpk k r * D v = 0 := by
    ext i j
    have h1 := hasDeriv_form (Hpk k r) (γ := fun t : ℝ => μ (ζ + t • v)) (g := μ ζ) (γ' := D v)
      (by simp) hent i j
    have h2 : HasDerivAt (fun t : ℝ => ((μ (ζ + t • v))ᴴ * Hpk k r * μ (ζ + t • v)) i j) 0 0 :=
      (hasDerivAt_const (0 : ℝ) (Hpk k r i j)).congr_of_eventuallyEq (hev.mono fun t ht => by
        show ((μ (ζ + t • v))ᴴ * Hpk k r * μ (ζ + t • v)) i j = Hpk k r i j
        rw [show (μ (ζ + t • v))ᴴ * Hpk k r * μ (ζ + t • v) = Hpk k r from ht.1])
    exact h1.unique h2
  have hH : (Hpk k r).det ≠ 0 := by
    have h1 := congrArg Matrix.det (Formalism.QuantumDeterminants.hpkFacts k r).2.1
    rw [Matrix.det_mul, Matrix.det_one] at h1
    intro h0
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  have hdet : IsUnit (μ ζ).det := by
    have h2 := congrArg Matrix.det hU
    rw [Matrix.det_mul, Matrix.det_mul] at h2
    refine isUnit_iff_ne_zero.2 fun h0 => hH ?_
    rw [h0, mul_zero] at h2
    exact h2.symm
  have hgi : μ ζ * (μ ζ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have e1 : ((μ ζ)⁻¹)ᴴ * Hpk k r = Hpk k r * μ ζ := by
    calc ((μ ζ)⁻¹)ᴴ * Hpk k r = ((μ ζ)⁻¹)ᴴ * ((μ ζ)ᴴ * Hpk k r * μ ζ) := by rw [hU]
      _ = (μ ζ * (μ ζ)⁻¹)ᴴ * Hpk k r * μ ζ := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = Hpk k r * μ ζ := by rw [hgi, Matrix.conjTranspose_one, Matrix.one_mul]
  have e2 : Hpk k r * (μ ζ)⁻¹ = (μ ζ)ᴴ * Hpk k r := by
    calc Hpk k r * (μ ζ)⁻¹ = (μ ζ)ᴴ * Hpk k r * μ ζ * (μ ζ)⁻¹ := by rw [hU]
      _ = (μ ζ)ᴴ * Hpk k r := by rw [Matrix.mul_assoc, hgi, Matrix.mul_one]
  have hvec : ∀ w : Fin (2 * r + k + 1) → ℂ, (∀ᶠ t in 𝓝 (0 : ℝ), μ (ζ + t • v) *ᵥ w = w) →
      D v *ᵥ w = 0 := by
    intro w hw
    funext q
    have hd : HasDerivAt (fun t : ℝ => (μ (ζ + t • v) *ᵥ w) q) ((D v *ᵥ w) q) 0 := by
      simp only [Matrix.mulVec, dotProduct]
      first
      | exact HasDerivAt.sum fun p _ => (hent q p).mul_const (w p)
      | exact HasDerivAt.fun_sum fun p _ => (hent q p).mul_const (w p)
    have hc : HasDerivAt (fun t : ℝ => (μ (ζ + t • v) *ᵥ w) q) 0 0 :=
      (hasDerivAt_const (0 : ℝ) (w q)).congr_of_eventuallyEq (hw.mono fun t ht => by
        show (μ (ζ + t • v) *ᵥ w) q = w q
        rw [ht])
    exact hd.unique hc
  unfold Q.inLieLev
  refine ⟨?_, fun a ha => ⟨?_, ?_⟩⟩
  · rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, e1, ← Matrix.mul_assoc (Hpk k r), e2,
      ← Matrix.mul_assoc]
    exact hder
  · rw [← Matrix.mulVec_mulVec, hvec _ (hev.mono fun t ht => (ht.2 a ha).1), Matrix.mulVec_zero]
  · rw [← Matrix.mulVec_mulVec, hvec _ (hev.mono fun t ht => (ht.2 a ha).2), Matrix.mulVec_zero]

end SD

theorem section_derivative_holds : SecDeriv := by
  intro k r z z' hk hz hz' hT hT' ζ hζ
  have hsec := TheSec.theSection_isSection k r z z' hk hz hz' hT hT'
  have hA : IsOpen {w : ℂ | Tz k r z * Tz k r z' < Complex.normSq w} :=
    isOpen_lt continuous_const Complex.continuous_normSq
  have hcd : ContDiffOn ℝ ∞ (mu0 k r z z') {w : ℂ | Tz k r z * Tz k r z' < Complex.normSq w} :=
    NFRadRedA.muZ_contDiffOn hsec
  have hdiff : DifferentiableAt ℝ (mu0 k r z z') ζ :=
    (hcd.differentiableOn (by simp)).differentiableAt (hA.mem_nhds hζ)
  obtain ⟨D, hD⟩ : ∃ D : ℂ →L[ℝ] Q.Mx k r, HasFDerivAt (mu0 k r z z') D ζ := ⟨_, hdiff.hasFDerivAt⟩
  have hG : ∀ᶠ w in 𝓝 ζ, mu0 k r z z' w ∈ Q.Glev k r (Fin.last r) := by
    filter_upwards [hA.mem_nhds hζ] with w hw
    exact NFRadRedA.uwb_glev (NFRadRedA.muZ_uwb hsec hw)
  have hg : mu0 k r z z' ζ ∈ Q.Glev k r (Fin.last r) := hG.self_of_nhds
  have hX := SD.lie_of_curve hD hG
  have hrow : ∀ i, HasFDerivAt (fun w => mu0 k r z z' w i) ((ContinuousLinearMap.proj i).comp D) ζ :=
    hasFDerivAt_pi'.1 hD
  have hent : ∀ i j v, fderiv ℝ (fun w => mu0 k r z z' w i j) ζ v = D v i j := by
    intro i j v
    have h := (hasFDerivAt_pi'.1 (hrow i)) j
    rw [h.fderiv]
    rfl
  have hs1 : D ((1 / 2 : ℝ) • (1 : ℂ)) = (1 / 2 : ℝ) • D 1 := map_smul D _ _
  have hs2 : D ((-(1 / 2) : ℝ) • Complex.I) = (-(1 / 2) : ℝ) • D Complex.I := map_smul D _ _
  have hs3 : D ((1 / 2 : ℝ) • Complex.I) = (1 / 2 : ℝ) • D Complex.I := map_smul D _ _
  have e1 : etaZ k r z z' ζ = (mu0 k r z z' ζ)⁻¹ * D ((1 / 2 : ℝ) • (1 : ℂ)) +
      Complex.I • ((mu0 k r z z' ζ)⁻¹ * D ((-(1 / 2) : ℝ) • Complex.I)) := by
    unfold etaZ
    rw [← Matrix.mul_smul, ← Matrix.mul_add, hs1, hs2]
    congr 1
    ext i j
    simp only [Matrix.of_apply, NF.dZ, hent, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
    push_cast
    ring
  have e2 : etaZb k r z z' ζ = (mu0 k r z z' ζ)⁻¹ * D ((1 / 2 : ℝ) • (1 : ℂ)) +
      Complex.I • ((mu0 k r z z' ζ)⁻¹ * D ((1 / 2 : ℝ) • Complex.I)) := by
    unfold etaZb
    rw [← Matrix.mul_smul, ← Matrix.mul_add, hs1, hs3]
    congr 1
    ext i j
    simp only [Matrix.of_apply, NF.dZb, hent, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
    push_cast
    ring
  obtain ⟨p1, p2⟩ := Qx5.hpart_unique (hX ((1 / 2 : ℝ) • (1 : ℂ))) (hX ((-(1 / 2) : ℝ) • Complex.I))
  obtain ⟨q1, q2⟩ := Qx5.hpart_unique (hX ((1 / 2 : ℝ) • (1 : ℂ))) (hX ((1 / 2 : ℝ) • Complex.I))
  rw [← e1] at p1 p2
  rw [← e2] at q1 q2
  have hmem : mu0 k r z z' ζ ∈ Q.Glev k r (Fin.last r) ∩ Dp k r z z' := by
    refine ⟨hg, ?_⟩
    show 0 < Complex.normSq (Q.zetaL k r z z' (Fin.last r) (NF.muZ k r (TheSec.theSection k r z z') ζ)) -
      Tz k r z * Tz k r z'
    rw [NFRadRedA.zeta_muZ hz hz' hsec hζ]
    linarith
  refine ⟨⟨by rw [p1]; exact hX _, by rw [p2]; exact hX _⟩, ⟨by rw [q1]; exact hX _, by rw [q2]; exact hX _⟩, hmem, ?_⟩
  intro E _ _ F hF
  obtain ⟨U, F', hU, hgU, hFc, he⟩ := hF _ hmem
  have hd : DifferentiableAt ℝ F' (mu0 k r z z' ζ) :=
    (hFc.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hgU)
  have hR : ∀ v, RdV ((mu0 k r z z' ζ)⁻¹ * D v) F (mu0 k r z z' ζ) = fderiv ℝ F' (mu0 k r z z' ζ) (D v) := by
    intro v
    have h := (Qx2.hasDeriv_ext hU hgU hg (hX v) hd he).deriv
    rw [← Matrix.mul_assoc, FrameEntries.mul_inv_uh hg.1, Matrix.one_mul] at h
    exact h
  have hC : HasFDerivAt (fun w => F (mu0 k r z z' w)) ((fderiv ℝ F' (mu0 k r z z' ζ)).comp D) ζ := by
    refine (hd.hasFDerivAt.comp ζ hD).congr_of_eventuallyEq ?_
    filter_upwards [hG, hD.continuousAt.preimage_mem_nhds (hU.mem_nhds hgU)] with w h1 h2
    exact he _ h2 h1
  constructor
  · unfold Rc dZV
    rw [p1, p2, hR, hR, hC.fderiv, hs1, hs2]
    simp only [ContinuousLinearMap.comp_apply, map_smul]
    rw [← Complex.coe_smul, ← Complex.coe_smul]
    push_cast
    module
  · unfold Rc dZbV
    rw [q1, q2, hR, hR, hC.fderiv, hs1, hs3]
    simp only [ContinuousLinearMap.comp_apply, map_smul]
    rw [← Complex.coe_smul, ← Complex.coe_smul]
    push_cast
    module

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRAlgSS
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR

theorem up_ne (P : M.Par) {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) {π ρ : M.Ty P} (h : M.Up P l π ρ) :
    ρ ≠ π := by
  rintro rfl
  rw [Finset.mem_Icc] at hl
  have h1 := h ⟨l - 1, by omega⟩
  have h2 : l - 1 + 1 = l := by omega
  simp [h2] at h1

theorem up_idx (P : M.Par) {j l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) {π ρ : M.Ty P} (h : M.Up P l π ρ)
    (h' : M.Up P j π ρ) : j = l := by
  rw [Finset.mem_Icc] at hl
  have h1 := h ⟨l - 1, by omega⟩
  have h3 := h' ⟨l - 1, by omega⟩
  have h2 : l - 1 + 1 = l := by omega
  by_contra hne
  have hne' : ¬ l = j := fun e => hne e.symm
  simp only [h2, if_true, hne', if_false] at h1 h3
  omega

theorem up_det (P : M.Par) {j : ℕ} {σ σ' ρ : M.Ty P} (h : M.Up P j σ σ') (h' : M.Up P j σ ρ) : σ' = ρ := by
  funext i
  apply Fin.ext
  rw [h i, h' i]

theorem algebraic_shift_holds : AlgSS := by
  intro P 𝒜 _ _ _ d hR l hl π ρ hUp Y
  obtain ⟨-, hκ, -, hSS, -, -⟩ := hR
  have hne := up_ne P hl hUp
  have hmul : ∀ f : M.Ty P → ℂ, d.κ f * d.κ (Pi.single π 1) = f π • d.κ (Pi.single π 1) := by
    intro f
    rw [← map_mul, ← map_smul]
    congr 1
    funext σ
    by_cases h : σ = π
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  have h0 : d.κ (Pi.single ρ 1) * d.κ (Pi.single π 1) = 0 := by
    rw [hmul, Pi.single_eq_of_ne hne.symm, zero_smul]
  have cGG : Commute (d.κ (Pi.single ρ 1)) d.L.GG := hκ _ _ (by simp [R.LevelData.fns])
  have cl0 : Commute (d.κ (Pi.single π 1)) (d.L.l0 Y) := by
    unfold R.LevelData.l0
    refine Commute.sub_right (Commute.neg_right (hκ _ _ (by simp))) (Commute.mul_right
      (Algebra.commute_algebraMap_right _ _) (Commute.mul_right (hκ _ _ (by simp [R.LevelData.fns]))
        (hκ _ _ (by simp [R.LevelData.fns]))))
  have t1 : d.κ (Pi.single ρ 1) * (d.L.GG * d.x Y * d.L.l0 Y) * d.κ (Pi.single π 1) = 0 := by
    have e : d.κ (Pi.single ρ 1) * (d.L.GG * d.x Y * d.L.l0 Y) * d.κ (Pi.single π 1) =
        d.L.GG * (d.κ (Pi.single ρ 1) * (d.x Y * d.κ (Pi.single π 1))) * d.L.l0 Y := by
      calc d.κ (Pi.single ρ 1) * (d.L.GG * d.x Y * d.L.l0 Y) * d.κ (Pi.single π 1)
          = (d.κ (Pi.single ρ 1) * d.L.GG) * d.x Y * (d.L.l0 Y * d.κ (Pi.single π 1)) := by
            simp only [mul_assoc]
        _ = (d.L.GG * d.κ (Pi.single ρ 1)) * d.x Y * (d.κ (Pi.single π 1) * d.L.l0 Y) := by
            rw [cGG.eq, cl0.eq]
        _ = _ := by simp only [mul_assoc]
    rw [e, Q.NFData.x, hmul, mul_smul_comm, h0, smul_zero, mul_zero, zero_mul]
  have t2 : ∀ j ∈ Finset.Icc 1 (P.k - 1),
      d.κ (Pi.single ρ 1) * (d.SS j * d.κ fun σ => M.xEx P {j} σ Y) * d.κ (Pi.single π 1) =
        if j = l then M.xEx P {j} π Y • (d.SS j * d.κ (Pi.single π 1)) else 0 := by
    intro j _
    have hs := hSS j (fun σ => if M.Up P j σ ρ then 1 else 0) (Pi.single ρ 1) (by
      intro σ σ' h
      by_cases hσ : σ' = ρ
      · subst hσ; simp [h]
      · rw [Pi.single_eq_of_ne hσ, if_neg]
        intro h'
        exact hσ (up_det P h h'))
    calc d.κ (Pi.single ρ 1) * (d.SS j * d.κ fun σ => M.xEx P {j} σ Y) * d.κ (Pi.single π 1)
        = (d.κ (Pi.single ρ 1) * d.SS j) * ((d.κ fun σ => M.xEx P {j} σ Y) * d.κ (Pi.single π 1)) := by
          simp only [mul_assoc]
      _ = M.xEx P {j} π Y • (d.SS j * ((d.κ fun σ => if M.Up P j σ ρ then 1 else 0) * d.κ (Pi.single π 1))) := by
          rw [hs, hmul, mul_smul_comm, mul_assoc]
      _ = M.xEx P {j} π Y • (d.SS j * ((if M.Up P j π ρ then (1 : ℂ) else 0) • d.κ (Pi.single π 1))) := by
          rw [hmul]
      _ = _ := by
          by_cases hjl : j = l
          · subst hjl; simp [hUp]
          · have hn : ¬ M.Up P j π ρ := fun h => hjl (up_idx P hl hUp h)
            simp [hn, hjl]
  have hQ : d.QQ Y 1 0 = d.L.GG * d.x Y * d.L.l0 Y + d.weightedSumBis Y := rfl
  rw [hQ, mul_add, add_mul, t1, zero_add, Q.NFData.weightedSumBis, Finset.mul_sum, Finset.sum_mul,
    Finset.sum_congr rfl t2, Finset.sum_ite_eq', if_pos hl]

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRPhaseExtract
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR

theorem evenPart_poly (c : ℂ) (p : MvPolynomial (Fin 3) ℂ) :
    ∃ q : Polynomial ℂ, ∀ t s : ℂ, t ^ 2 = s ^ 2 + c →
      MvPolynomial.eval ![t, t, s] p + MvPolynomial.eval ![-t, -t, s] p = q.eval s := by
  induction p using MvPolynomial.induction_on' with
  | monomial u a =>
    rcases Nat.even_or_odd' (u 0 + u 1) with ⟨j, hj | hj⟩
    · refine ⟨Polynomial.C (2 * a) * (Polynomial.X ^ 2 + Polynomial.C c) ^ j * Polynomial.X ^ (u 2), fun t s h => ?_⟩
      simp only [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_three,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
      rw [← pow_add, ← pow_add, hj, pow_mul, pow_mul, neg_sq, h]
      ring
    · refine ⟨0, fun t s h => ?_⟩
      simp only [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_three,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
        Polynomial.eval_zero]
      rw [← pow_add, ← pow_add, hj, Odd.neg_pow ⟨j, rfl⟩]
      ring
  | add p₁ p₂ h₁ h₂ =>
    obtain ⟨q₁, hq₁⟩ := h₁
    obtain ⟨q₂, hq₂⟩ := h₂
    refine ⟨q₁ + q₂, fun t s h => ?_⟩
    rw [map_add (f := _), map_add (f := _), Polynomial.eval_add, ← hq₁ t s h, ← hq₂ t s h]
    ring

theorem phase_extraction_holds : PhaseExtract := by
  intro TT f _ hPS hrot
  obtain ⟨m, p, hp⟩ := hPS
  obtain ⟨q, hq⟩ := evenPart_poly (TT : ℂ) p
  refine ⟨m, Polynomial.C (1 / 2) * q, fun ζ hζ => ?_⟩
  have hn : Complex.normSq ((‖ζ‖ : ℝ) : ℂ) = Complex.normSq ζ := by
    rw [Complex.normSq_ofReal, Complex.normSq_eq_norm_sq]; ring
  have hn' : Complex.normSq (-((‖ζ‖ : ℝ) : ℂ)) = Complex.normSq ζ := by
    rw [Complex.normSq_neg, hn]
  have h1 : f ζ = f ((‖ζ‖ : ℝ) : ℂ) := by
    have := hrot (Complex.arg ζ) ((‖ζ‖ : ℝ) : ℂ) (by rw [hn]; exact hζ)
    rw [← this]
    congr 1
    unfold rot
    rw [mul_comm, Complex.norm_mul_exp_arg_mul_I]
  have h2 : f ζ = f (-((‖ζ‖ : ℝ) : ℂ)) := by
    have := hrot Real.pi ((‖ζ‖ : ℝ) : ℂ) (by rw [hn]; exact hζ)
    rw [h1, ← this]
    congr 1
    unfold rot
    rw [Complex.exp_pi_mul_I]; ring
  have e1 := hp ((‖ζ‖ : ℝ) : ℂ) (by rw [hn]; exact hζ)
  have e2 := hp (-((‖ζ‖ : ℝ) : ℂ)) (by rw [hn']; exact hζ)
  have g1 : gg TT ((‖ζ‖ : ℝ) : ℂ) = gg TT ζ := by unfold gg; rw [hn]
  have g2 : gg TT (-((‖ζ‖ : ℝ) : ℂ)) = gg TT ζ := by unfold gg; rw [hn']
  have s1 : sig TT ((‖ζ‖ : ℝ) : ℂ) = sig TT ζ := by unfold sig; rw [hn]
  have s2 : sig TT (-((‖ζ‖ : ℝ) : ℂ)) = sig TT ζ := by unfold sig; rw [hn']
  rw [g1, s1, ← h1, Complex.conj_ofReal] at e1
  rw [g2, s2, ← h2, map_neg, Complex.conj_ofReal] at e2
  have hcurve : (((‖ζ‖ : ℝ) : ℂ)) ^ 2 = sig TT ζ ^ 2 + (TT : ℂ) := by
    unfold sig
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, Real.sq_sqrt (by linarith), ← Complex.ofReal_add,
      Complex.normSq_eq_norm_sq]
    congr 1; ring
  have := hq _ _ hcurve
  rw [← e1, ← e2] at this
  rw [Polynomial.eval_mul, Polynomial.eval_C, ← this]
  ring

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR
end

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR

theorem phase_invariance_holds : PhaseInv :=
  PH.phase_invariance_of_truncation PH.phase_section_holds PH.lower_unipotent_rotation_holds PH.rotation_radial_space_holds PH.theta_rotation_holds kappa_line_holds algebraic_shift_holds
    datum_constancy_holds fibre_stability_holds

theorem corePoly_of (hD : CP.Decomp) (hW : CP.WordPSVOfCut) : CorePoly :=
  CP.radial_polynomial_of_truncation CP.lower_unipotent_matrix_words
    (hW CP.radial_coefficient_linearity CP.radial_coefficient_smoothness CP.radial_coefficient_commutation CP.left_covariance_holds CP.right_covariance_holds CP.section_derivative_holds hD
      CP.polynomial_shift_calculation)
    CP.polynomial_shift_calculation

theorem polyRadialS_of (hD : CP.Decomp) (hW : CP.WordPSVOfCut) : PolyRadialS :=
  polynomialRadial_of_base polynomial_radial_base_holds SSn.Rep.theta_facts_hold transfer_holds datum_constancy_holds kappa_line_holds
    fibre_stability_holds algebraic_shift_holds (corePoly_of hD hW) phase_invariance_holds phase_extraction_holds word_nonvanishing_holds

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR
