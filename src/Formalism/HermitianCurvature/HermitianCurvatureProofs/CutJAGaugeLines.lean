module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSConst
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCHolPh
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSH2

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGaugeLines
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGaugeLinesRight
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.PRho.GL

noncomputable section

theorem gauge_right_line_holds : GLRight := by
  intro Wp Wq _ _ _ _ _ _ P Bs e hpl hk he hQQ ζ hζ Fr hFr X hX Y X' hX' ρ
  obtain ⟨hOK, hz, hz', hTz, hTz', -, -⟩ := id hpl
  have hT : 0 < Tz P.k P.r Bs.z := Bs.T_pos
  have hT' : 0 < Tz P.k P.r Bs.z' := Bs.T'_pos
  have hζ' : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ := by
    rw [hTz, hTz']; exact hζ
  set c0 : Fin P.r → ℂ := fun _ => 1 with hc0def
  have hq : ((c0, ζ) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨fun _ => one_ne_zero, hζ'⟩
  set g := NF.muZ P.k P.r Bs.μsec ζ with hgdef
  let qq : MA.Qp P.r P.TT := ⟨(c0, ζ), ⟨fun _ => one_ne_zero, hζ⟩⟩
  have hw : 0 < Gauge.wR P.k P.TT ζ := Gauge.GC.SSTr.wR_pos P hζ
  set a : M.Ty P → ℂ := fun σ => ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) * inner ℂ (B.hsVec (e σ ζ)) (B.hsVec X) with hadef
  obtain ⟨Φs, -, hΦv⟩ := Gauge.GC.SSTr.exists_tr P Bs hpl hk e he (fun σ => algebraMap ℂ (MA.SmQ P.r P.TT) (a σ))
  set Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp) := (Φs : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) with hΦdef
  have hΦ : Φ ∈ Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' := Φs.2
  have hval : Φ c0 g = X := by
    have h1 : Φ c0 g = _ := hΦv qq
    rw [h1]
    conv_rhs => rw [(he.2 ζ hζ).2.2 X hX]
    refine Finset.sum_congr rfl fun σ _ => ?_
    congr 1
    have hw' : ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hw.ne'
    show (((Gauge.wR P.k P.TT ζ)⁻¹ : ℝ) : ℂ) * ((algebraMap ℂ (MA.SmQ P.r P.TT) (a σ) : MA.SmQ P.r P.TT) :
      MA.Qp P.r P.TT → ℂ) qq = _
    simp only [hadef, Subalgebra.coe_algebraMap, Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    push_cast
    field_simp
  have hx : (c0, g) ∈ Q.DomR P.k P.r Bs.z Bs.z' := Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' Bs.sec hq

  set Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r) := fun _ => Formalism.FourierDecayAlt.P.Qx5.Dp P.k P.r Bs.z Bs.z' with hDc
  have hFam : Gauge.FamR P Bs Dc Φ := by
    refine ⟨?_, fun c _ => Formalism.FourierDecayAlt.P.Qx5.Dp_dom P.k P.r Bs.z Bs.z', fun q => ?_, ?_,
      fun c hc => Formalism.FourierDecayAlt.P.Qx5.slice_FF hz hz' hΦ hc⟩
    · have h1 : IsOpen {x : (Fin P.r → ℂ) × Q.Mx P.k P.r | x.1 ∈ OmX P.r} := by
        have : IsOpen (OmX P.r) := by
          have e : OmX P.r = ⋂ l, {x : Fin P.r → ℂ | x l ≠ 0} := by ext x; simp [OmX]
          rw [e]
          exact isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const
        exact this.preimage continuous_fst
      have h2 : IsOpen {x : (Fin P.r → ℂ) × Q.Mx P.k P.r | 0 < Q.GGl P.k P.r Bs.z Bs.z' x.2} :=
        isOpen_lt continuous_const ((Formalism.FourierDecayAlt.P.Qx5.GGl_continuous P.k P.r Bs.z Bs.z').comp continuous_snd)
      exact h1.inter h2
    · have hq' : ((q.1.1, q.1.2) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' :=
        ⟨q.2.1, by rw [hTz, hTz']; exact q.2.2⟩
      exact (Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' Bs.sec hq').2.2
    · intro x₀ hx₀ hgl
      exact hΦ.2.1 x₀ ⟨hx₀.1, hgl, hx₀.2⟩
  have hG := hQQ Dc Φ hFam Y 1 1 ρ
  have hs1 := Gauge.raw_gauge_smoothness_holds Wp Wq P Bs hpl hk e he Dc _
    (Gauge.quadratic_local_family_holds Wp Wq P Bs hpl hk Dc Φ hFam Y 1 1) ρ
  have hs0 := Gauge.raw_gauge_smoothness_holds Wp Wq P Bs hpl hk e he Dc Φ hFam ρ

  have hQ11 : MA.QQr P (MA.DQ P) (Y : ℂ) 1 1 = MA.ggA P (MA.DQ P) * MA.xA P (MA.DQ P) (Y : ℂ) := rfl
  rw [hQ11, Gauge.actA_mul, MA.ggA, Gauge.GC.SSC.actA_sc, MA.xA] at hG
  have hev := congrArg (fun s : MA.SmQ P.r P.TT => (s : MA.Qp P.r P.TT → ℂ) qq) hG
  rw [Gauge.GC.toSm_of_mem P hs1, Gauge.GC.actA_kap] at hev
  have hw' : ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hw.ne'
  have hGGv : Q.GGl P.k P.r Bs.z Bs.z' g = Complex.normSq ζ - P.TT := by
    unfold Q.GGl
    rw [Formalism.FourierDecayAlt.P.NFRadRedA.zeta_muZ hz hz' Bs.sec hζ', hTz, hTz']
    rfl
  have hGG0 : ((Complex.normSq ζ - P.TT : ℝ) : ℂ) ≠ 0 := by
    have : 0 < Complex.normSq ζ - P.TT := by linarith
    exact_mod_cast this.ne'
  have hsm : ∀ (c : ℂ) (A : Wq →L[ℂ] Wp), B.hsVec (c • A) = c • B.hsVec A := by
    intro c A; ext i; simp [B.hsVec]
  have hQLg : Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) 1 1 Φ c0 g =
      (((Complex.normSq ζ - P.TT : ℝ) : ℂ)) • X' := by
    ext v
    have ht := Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.top_level_pointwise_identity Formalism.FourierDecayAlt.P.capelli_two_by_two Formalism.FourierDecayAlt.P.right_type_action hz hz'
      (Formalism.FourierDecayAlt.P.Qx5.Dp_dom P.k P.r Bs.z Bs.z') Bs.π'_rep Bs.π'_cont
      (Formalism.FourierDecayAlt.P.Qx5.slice_FF hz hz' hΦ (fun _ => one_ne_zero)) ⟨hx.2.1, hx.2.2⟩ (ne_of_gt hx.2.2) Fr hFr (Y : ℂ) v
    show Q.tL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) 1 1 (Φ c0) g v = _
    rw [ht, hval, ← hX', hGGv, ContinuousLinearMap.smul_apply]
  have hL : Gauge.rawR P Bs.μsec e (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (↑Y) 1 1 Φ) ρ qq =
      ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) * (((Complex.normSq ζ - P.TT : ℝ) : ℂ) *
        inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec X')) := by
    show ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) * inner ℂ (B.hsVec (e ρ ζ))
      (B.hsVec (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (↑Y) 1 1 Φ c0 g)) = _
    rw [hQLg, hsm, inner_smul_right]
  have h0 : Gauge.rawR P Bs.μsec e Φ ρ qq = ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) * inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec X) := by
    show ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) * inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec (Φ c0 g)) = _
    rw [hval]
  let Gq : MA.SmQ P.r P.TT := (MA.DQ P).gg P.TT
  let sq : MA.SmQ P.r P.TT := M.xC P ρ ↑Y • MA.toSm P (Gauge.rawR P Bs.μsec e Φ ρ)
  change _ = ((Gq * sq : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) qq at hev
  rw [Subalgebra.coe_mul, Pi.mul_apply] at hev
  have hgg : (Gq : MA.Qp P.r P.TT → ℂ) qq = ((Complex.normSq ζ - P.TT : ℝ) : ℂ) := by
    show MA.coordE M.vz qq.1 * MA.coordE M.vzb qq.1 - (P.TT : ℂ) = _
    simp [MA.coordE, MA.zE, M.vz, M.vzb, Complex.mul_conj, qq]
  have hsq : (sq : MA.Qp P.r P.TT → ℂ) qq = M.xC P ρ ↑Y * Gauge.rawR P Bs.μsec e Φ ρ qq := by
    show ((M.xC P ρ ↑Y • MA.toSm P (Gauge.rawR P Bs.μsec e Φ ρ) : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) qq = _
    rw [Subalgebra.coe_smul, Pi.smul_apply, Gauge.GC.toSm_of_mem P hs0, smul_eq_mul]
  rw [hgg, hsq, hL, h0] at hev
  have h3 : ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) * (((Complex.normSq ζ - P.TT : ℝ) : ℂ) *
        inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec X')) =
      ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) * (((Complex.normSq ζ - P.TT : ℝ) : ℂ) *
        (M.xC P ρ ↑Y * inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec X))) := by
    rw [hev]; ring
  exact mul_left_cancel₀ hGG0 (mul_left_cancel₀ hw' h3)

end

end Formalism.FourierDecayAlt.P.CutMP.JA.PRho.GL
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGaugeLinesAsm
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.PRho.GL

noncomputable section

namespace AsmPf

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

variable [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem hsVec_smul (c : ℂ) (A : Wq →L[ℂ] Wp) : B.hsVec (c • A) = c • B.hsVec A := by
  ext i
  simp [B.hsVec]

theorem base (hR : GLRight) (hLf : GLLeft) (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k)
    (hF : Gauge.IsFrameB P Bs e)
    (hQQ : ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)), Gauge.FamR P Bs Dc Φ →
      ∀ (Y : ℝ) (a b : Fin 2) (ρ : M.Ty P),
        MA.toSm P (Gauge.rawR P Bs.μsec e (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) a b Φ) ρ) =
          MA.actA P (MA.QQr P (MA.DQ P) (Y : ℂ) a b) (fun ρ' => MA.toSm P (Gauge.rawR P Bs.μsec e Φ ρ')) ρ)
    (ζ : ℂ) (hζ : P.TT < Complex.normSq ζ) (ρ : M.Ty P) (Fr : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ)
    (hFr : Q.IsFrameOf P.k P.r [Bs.z, SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ] Fr) (w : ℂ) (x : Wq) :
    Q.capRep P.k P.r Bs.π Fr w (e ρ ζ x) = M.xC P ρ (w - ((P.k : ℂ) - 2) / 2) • e ρ ζ x := by
  obtain ⟨hOK, hz, hz', hTz, hTz', -, -⟩ := id hpl
  have hζ' : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ := by
    rw [hTz, hTz']; exact hζ
  obtain ⟨hFr', hpass⟩ := hLf Wp Wq P Bs hpl hk ζ hζ Fr hFr
  have hq : ((fun _ => (1 : ℂ)), ζ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨fun _ => one_ne_zero, hζ'⟩
  obtain ⟨-, hg, hG⟩ := Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' Bs.sec hq
  have hEx := Gauge.GC.lie_existence_of_iso_group Gauge.GC.KLIso.lie_algebra_isomorphism_holds Gauge.GC.lie_group_realization
  obtain ⟨E, hEfib, hEeig, hE0⟩ := hEx Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hpl hk _ hg hG.ne' _ hFr' ρ
  have hEF : E ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ :=
    fun p hp => hEfib p.1 hp.1 p.2 hp.2.1 hp.2.2
  have hgl' := (Formalism.FourierDecayAlt.P.frame_general_linear Wq P.k P.r (P.k - 1) Bs.z' Bs.π'
    (fun a => (NF.muZ P.k P.r Bs.μsec ζ)⁻¹ *ᵥ Fr a) ⟨Bs.π'_rep, Bs.π'_cont⟩
    (Formalism.FourierDecayAlt.P.Qx8.frame_sub hFr' (by simp))).2
  have hEc : ∀ (Y : ℂ) (v : Wq), E (Q.capRep P.k P.r Bs.π'
      (fun a => (NF.muZ P.k P.r Bs.μsec ζ)⁻¹ *ᵥ Fr a) (Y + ((P.k : ℂ) - 2) / 2) v) = M.xC P ρ Y • E v := by
    intro Y v
    rw [hgl']
    exact hEeig Y v
  obtain ⟨Y₀, hY₀⟩ := Formalism.FourierDecayAlt.P5.Kfp.sep_real hOK
  have horth : ∀ σ, σ ≠ ρ → inner ℂ (B.hsVec (e σ ζ)) (B.hsVec E) = 0 := by
    intro σ hσ
    have h := hR Wp Wq P Bs e hpl hk hF hQQ ζ hζ _ hFr' E hEF Y₀ (M.xC P ρ (Y₀ : ℂ) • E)
      (fun v => by rw [hEc, ContinuousLinearMap.smul_apply]) σ
    rw [hsVec_smul, inner_smul_right] at h
    have h2 : (M.xC P ρ (Y₀ : ℂ) - M.xC P σ (Y₀ : ℂ)) * inner ℂ (B.hsVec (e σ ζ)) (B.hsVec E) = 0 := by
      rw [sub_mul, h, sub_self]
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact absurd (hY₀ (sub_eq_zero.1 h3)).symm hσ
    · exact h3
  have hexp := (hF.2 ζ hζ).2.2 E hEF
  have hE1 : E = inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec E) • e ρ ζ := by
    conv_lhs => rw [hexp]
    rw [Finset.sum_eq_single ρ (fun σ _ hσ => by rw [horth σ hσ, zero_smul])
      (fun h => absurd (Finset.mem_univ ρ) h)]
  have hc0 : inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec E) ≠ 0 := by
    intro h0
    apply hE0
    rw [hE1, h0, zero_smul]
  have heig : ∀ (Y : ℂ) (v : Wq), e ρ ζ (Q.capRep P.k P.r Bs.π'
      (fun a => (NF.muZ P.k P.r Bs.μsec ζ)⁻¹ *ᵥ Fr a) (Y + ((P.k : ℂ) - 2) / 2) v) = M.xC P ρ Y • e ρ ζ v := by
    intro Y v
    have h := hEc Y v
    generalize hcdef : inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec E) = c at hE1 hc0
    rw [hE1] at h
    simp only [ContinuousLinearMap.smul_apply] at h
    rw [smul_comm (M.xC P ρ Y) c] at h
    exact smul_right_injective Wp hc0 h
  rw [hpass (e ρ ζ) ((hF.2 ζ hζ).1 ρ) w x]
  have hw : w = (w - ((P.k : ℂ) - 2) / 2) + ((P.k : ℂ) - 2) / 2 := by ring
  conv_lhs => rw [hw]
  exact heig _ x

end AsmPf

theorem gaugeLines_of_cut : GaugeLinesOfCut := by
  intro hR hL Cc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ v e hH hk ζ hζ ρ Fr hFr w x
  obtain ⟨hB, hFrame, -, hQQ⟩ := hH
  have hpl := (hB.1.2.2.2.1.2 v).2.2.2.1
  exact AsmPf.base hR hL (D.parOf S v) (T v).base e hpl hk hFrame hQQ ζ hζ ρ Fr hFr w x

end

end Formalism.FourierDecayAlt.P.CutMP.JA.PRho.GL
end

namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem gauge_lines_holds : PRho.GaugeLines :=
  PRho.GL.gaugeLines_of_cut PRho.GL.gauge_right_line_holds PRho.GL.gauge_left_line_holds

end Formalism.FourierDecayAlt.P.CutMP.JA
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCHolRest
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCHolConnUniq
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

theorem connection_uniqueness_holds : GTCConnUniq := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d hyp e he A B A' B' hAB hAB' hC hC' ρ ζ hζ
  obtain ⟨Φ, hΦ, -⟩ := SSTr.exists_tr P Bs hyp.1 hyp.2.1 e he (fun _ => (1 : MA.SmQ P.r P.TT))
  have h1 := (hC Φ ρ).1
  have h2 := (hC' Φ ρ).1
  rw [hΦ] at h1 h2
  simp only [mul_one] at h1 h2
  have h3 : fnZ P (A ρ) = fnZ P (A' ρ) := by
    have := h1.symm.trans h2
    exact add_left_cancel this
  rw [fnZ_eq_mk P (hAB ρ).1, fnZ_eq_mk P (hAB' ρ).1] at h3
  have hq : ((fun _ => (1 : ℂ), ζ) : (Fin P.r → ℂ) × ℂ) ∈ MA.Qset P.r P.TT :=
    ⟨fun _ => one_ne_zero, hζ⟩
  have := congrFun (congrArg Subtype.val h3) ⟨_, hq⟩
  exact this

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

theorem phase_holomorphy_holds : GTCPhHol := by
  intro TT u hu h1 R _ hR
  exact Ph.hol_unit (TT := TT) hu (fun ζ hζ => h1 ζ hζ) hR

theorem phase_curvature_holds : GTCPhCurv := by
  intro TT u hu h1 ζ hζ
  exact Ph.curv_unit (TT := TT) hu (fun ζ hζ => h1 ζ hζ) hζ

theorem connection_phase_holds : GTCConnPhase := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d hyp e A B u hAB hu hC
  exact connF_phase P (tt_nonneg_of_hyp hyp) Bs d e A B u hAB hC hu

theorem gTCHol_of_ref (hRef : GTCRef) : GTCHol :=
  gTCHol_of_cut hRef phase_relation_holds connection_uniqueness_holds connection_phase_holds phase_holomorphy_holds

theorem gTCCurv_of_ref (hRef : GTCRef) : GTCCurv :=
  gTCCurv_of_cut hRef phase_relation_holds connection_uniqueness_holds connection_phase_holds phase_curvature_holds

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end
