module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAlgebraFacts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositiveDensityModerateGrowth
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSLMat
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

theorem wRc_smooth (P : M.Par) : ContDiffOn ℝ ∞ (fun ζ : ℂ => ((wR P.k P.TT ζ : ℝ) : ℂ)) (Ann P) := by
  have h1 : ContDiffOn ℝ ∞ (fun ζ : ℂ => (Complex.normSq ζ - P.TT) ^ (P.k - 1)) (Ann P) := by
    have h2 : ContDiff ℝ ∞ (fun ζ : ℂ => Complex.normSq ζ) := by
      have h3 : (fun ζ : ℂ => Complex.normSq ζ) = fun ζ : ℂ => ‖ζ‖ ^ 2 := by
        funext ζ
        rw [Complex.normSq_eq_norm_sq]
      rw [h3]
      exact contDiff_norm_sq ℝ
    exact ((h2.sub contDiff_const).pow _).contDiffOn
  have h4 : ContDiffOn ℝ ∞ (fun ζ : ℂ => wR P.k P.TT ζ) (Ann P) := by
    unfold wR
    refine h1.sqrt fun ζ hζ => ?_
    have h5 : P.TT < Complex.normSq ζ := hζ
    exact (pow_pos (by linarith) _).ne'
  exact Complex.ofRealCLM.contDiff.comp_contDiffOn h4

theorem wRc_ne (P : M.Par) {ζ : ℂ} (hζ : ζ ∈ Ann P) : ((wR P.k P.TT ζ : ℝ) : ℂ) ≠ 0 := by
  have h5 : P.TT < Complex.normSq ζ := hζ
  have h6 : 0 < wR P.k P.TT ζ := by
    unfold wR
    exact Real.sqrt_pos.mpr (pow_pos (by linarith) _)
  exact_mod_cast h6.ne'

section mat

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem tz_TT (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') :
    Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' = P.TT := by
  rw [hpl.2.2.2.1, hpl.2.2.2.2.1]
  rfl

theorem radBase_of (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') :
    NF.RadBase P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' := by
  exact ⟨Bs.k_pos, Bs.z_mem, Bs.z'_mem, Bs.T_pos, Bs.T'_pos, Bs.sec, Bs.π_rep, Bs.π'_rep, Bs.π_cont,
    Bs.π'_cont⟩

theorem slice_smooth (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    (hk : 2 ≤ P.k) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (he : IsFrameB P Bs e)
    (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (ρ : M.Ty P) {c : Fin P.r → ℂ} (hc : c ∈ OmX P.r) :
    ContDiffOn ℝ ∞ (fun ζ => inner ℂ (B.hsVec (e ρ ζ))
      (B.hsVec ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ)))) (Ann P) := by
  have hm : ContDiffOn ℝ ∞ (MA.ext (rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ)) (MA.Qset P.r P.TT) :=
    radial_space_smoothness Wp Wq P Bs hpl hk e he Φ ρ
  have h1 : ContDiffOn ℝ ∞ (fun ζ : ℂ => MA.ext (rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ) (c, ζ))
      (Ann P) :=
    hm.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun ζ hζ => ⟨hc, hζ⟩)
  refine (Formalism.FourierDecayAlt.P.NFRadRedLocSec.cd_div h1 (wRc_smooth P) fun ζ hζ => wRc_ne P hζ).congr fun ζ hζ => ?_
  have hq : ((c, ζ) : MA.E P.r) ∈ MA.Qset P.r P.TT := ⟨hc, hζ⟩
  simp only [MA.ext, dif_pos hq, rawR]
  rw [mul_div_cancel_left₀ _ (wRc_ne P hζ)]

theorem key_slice (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    (hk : 2 ≤ P.k) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (he : IsFrameB P Bs e)
    (Ψ : M.Ty P → Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')
    (hΨ : ∀ ρ, ∀ c ∈ OmX P.r, ∀ ζ ∈ Ann P,
      (Ψ ρ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ) = e ρ ζ)
    (T : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) (hT : SliceLoc P Bs T)
    (hC : ∀ f : ℂ → ℂ, ContDiffOn ℝ ∞ f {ζ | P.TT < Complex.normSq ζ} →
      ∀ W : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), NF.IsMulZ W f → Commute T W)
    (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') {c c0 : Fin P.r → ℂ} (hc : c ∈ OmX P.r) (hc0 : c0 ∈ OmX P.r)
    {ζ : ℂ} (hζ : ζ ∈ Ann P) :
    (T Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ) =
      ∑ ρ, inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ))) •
        (T (Ψ ρ) : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c0 (NF.muZ P.k P.r Bs.μsec ζ) := by
  have hTz := tz_TT P Bs hpl
  have hRB := radBase_of P Bs hpl
  let F : M.Ty P → ℂ → ℂ := fun ρ ζ' => inner ℂ (B.hsVec (e ρ ζ'))
    (B.hsVec ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ')))
  have hFs : ∀ ρ, ContDiffOn ℝ ∞ (F ρ) {ζ | P.TT < Complex.normSq ζ} := fun ρ =>
    slice_smooth P Bs hpl hk e he Φ ρ hc
  choose W hW using fun ρ => Formalism.FourierDecayAlt.P.multiplication_zeta_exists Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hpl (F ρ) (hFs ρ)
  have hQR : ∀ c' ∈ OmX P.r, ∀ ζ' ∈ Ann P, ((c', ζ') : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' :=
    fun c' hc' ζ' hζ' => ⟨hc', by rw [hTz]; exact hζ'⟩
  have hmul : ∀ (ρ : M.Ty P) (Θ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), ∀ c' ∈ OmX P.r, ∀ ζ' ∈ Ann P,
      ((W ρ Θ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c' (NF.muZ P.k P.r Bs.μsec ζ') =
        F ρ ζ' • (Θ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c' (NF.muZ P.k P.r Bs.μsec ζ') := by
    intro ρ Θ c' hc' ζ' hζ'
    have hq := hQR c' hc' ζ' hζ'
    rw [hW ρ Θ]
    have h := Formalism.FourierDecayAlt.P.NFRO.radR_mulZ hRB (F ρ) Θ.2 hq
    simp only [NF.radR, Set.indicator_of_mem hq] at h
    exact h
  let Φc : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' := ∑ ρ, W ρ (Ψ ρ)
  have hsumv : ∀ (G : M.Ty P → Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (c' : Fin P.r → ℂ) (g : Q.Mx P.k P.r),
      ((∑ ρ, G ρ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c' g =
        ∑ ρ, (G ρ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c' g := by
    intro G c' g
    rw [Submodule.coe_sum, Finset.sum_apply, Finset.sum_apply]
  have hΦv : ∀ ζ' ∈ Ann P, (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ') =
      (Φc : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ') := by
    intro ζ' hζ'
    have hq := hQR c hc ζ' hζ'
    rw [hsumv]
    have hmem := (Formalism.FourierDecayAlt.P.radical_reduction_mem Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hRB _ Φ.2).2.1 (c, ζ') hq
    simp only [NF.radR, Set.indicator_of_mem hq] at hmem
    rw [(he.2 ζ' hζ').2.2 _ hmem]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [hmul ρ (Ψ ρ) c hc ζ' hζ', hΨ ρ c hc ζ' hζ']
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hT Φ Φc c c hc hc hΦv ζ hζ, map_sum, hsumv]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  have hcomm : T (W ρ (Ψ ρ)) = W ρ (T (Ψ ρ)) := by
    have h := (hC (F ρ) (hFs ρ) (W ρ) (hW ρ)).eq
    exact LinearMap.congr_fun h (Ψ ρ)
  rw [hcomm, hmul ρ (T (Ψ ρ)) c hc ζ hζ]
  congr 1
  exact hT (Ψ ρ) (Ψ ρ) c c0 hc hc0 (fun ζ' hζ' => by rw [hΨ ρ c hc ζ' hζ', hΨ ρ c0 hc0 ζ' hζ']) ζ hζ

end mat

theorem second_shift_matrix_form : GTSSLMat := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d hH e he hSL
  obtain ⟨hpl, hk, -, hL, hS, hRel, hQQ⟩ := hH
  have hTz := tz_TT P Bs hpl
  have hRB := radBase_of P Bs hpl
  let c0 : Fin P.r → ℂ := fun _ => 1
  have hc0 : c0 ∈ OmX P.r := fun _ => one_ne_zero
  have hsec : ∀ ρ, ((NF.QR P.k P.r Bs.z Bs.z').indicator fun q : (Fin P.r → ℂ) × ℂ => e ρ q.2) ∈
      NF.RadSec P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' := by
    intro ρ
    refine ⟨((he.1 ρ).comp contDiff_snd.contDiffOn fun q hq => ?_).congr fun q hq => ?_, fun q hq => ?_,
      fun q hq => ?_⟩
    · show P.TT < Complex.normSq q.2
      rw [← hTz]; exact hq.2
    · simp [Set.indicator_of_mem hq]
    · rw [Set.indicator_of_mem hq]
      exact (he.2 q.2 (by rw [← hTz]; exact hq.2)).1 ρ
    · simp [Set.indicator_of_notMem hq]
  choose Ψ0 hΨ0 hΨr using fun ρ =>
    Formalism.FourierDecayAlt.P.radical_reduction_surjective Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hRB _ (hsec ρ)
  let Ψ : M.Ty P → Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' := fun ρ => ⟨Ψ0 ρ, hΨ0 ρ⟩
  have hΨ : ∀ ρ, ∀ c ∈ OmX P.r, ∀ ζ ∈ Ann P,
      (Ψ ρ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ) = e ρ ζ := by
    intro ρ c hc ζ hζ
    have hq : ((c, ζ) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨hc, by rw [hTz]; exact hζ⟩
    have h := congrFun (hΨr ρ) (c, ζ)
    simp only [NF.radR, Set.indicator_of_mem hq] at h
    exact h
  have hCom : ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ f : ℂ → ℂ, ContDiffOn ℝ ∞ f {ζ | P.TT < Complex.normSq ζ} →
      ∀ W : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), NF.IsMulZ W f →
        Commute (d.SS l).1 W ∧ Commute (star (d.SS l)).1 W := by
    intro l hl f hf W hW
    obtain ⟨W₁, hW₁⟩ := Formalism.FourierDecayAlt.P.multiplication_zeta_exists Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hpl (NF.dZ f)
      (Formalism.FourierDecayAlt.P.NFx4.NO.dZ_smooth (Formalism.FourierDecayAlt.P.NFx4.NO.isOpen_U _) hf)
    obtain ⟨W₂, hW₂⟩ := Formalism.FourierDecayAlt.P.multiplication_zeta_exists Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hpl (NF.dZb f)
      (Formalism.FourierDecayAlt.P.NFx4.NO.dZb_smooth (Formalism.FourierDecayAlt.P.NFx4.NO.isOpen_U _) hf)
    exact (Formalism.FourierDecayAlt.P.normal_form_order_zero Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hpl X d hL hS hRel hQQ f hf W W₁ W₂
      hW hW₁ hW₂).2.1 l hl
  let ent : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') → M.Ty P → M.Ty P → ℂ → ℂ := fun T ρ' ρ ζ =>
    inner ℂ (B.hsVec (e ρ' ζ)) (B.hsVec ((T (Ψ ρ) : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c0 (NF.muZ P.k P.r Bs.μsec ζ)))
  have hent : ∀ T ρ' ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ent T ρ' ρ) (Ann P) := fun T ρ' ρ =>
    slice_smooth P Bs hpl hk e he (T (Ψ ρ)) ρ' hc0
  have hmain : ∀ (T : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')), SliceLoc P Bs T →
      (∀ f : ℂ → ℂ, ContDiffOn ℝ ∞ f {ζ | P.TT < Complex.normSq ζ} →
        ∀ W : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), NF.IsMulZ W f → Commute T W) →
      ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (ρ' : M.Ty P),
        trR P Bs e (T Φ) ρ' = ∑ ρ, fnZ P (ent T ρ' ρ) * trR P Bs e Φ ρ := by
    intro T hT hC Φ ρ'
    have hv : ∀ (Θ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (σ : M.Ty P),
        ((trR P Bs e Θ σ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) =
          rawR P Bs.μsec e (Θ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) σ := fun Θ σ =>
      Formalism.FourierDecayAlt.P.CutMP.En.toSm_val_of_mem P (radial_space_smoothness Wp Wq P Bs hpl hk e he Θ σ)
    apply Subtype.ext
    funext q
    rw [hv]
    rw [show (((∑ ρ, fnZ P (ent T ρ' ρ) * trR P Bs e Φ ρ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q) =
        ∑ ρ, ent T ρ' ρ q.1.2 * rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ q by
      rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun ρ _ => ?_
      rw [MulMemClass.coe_mul, Pi.mul_apply, hv, fnZ_eq_mk P (hent T ρ' ρ)]]
    have hc : q.1.1 ∈ OmX P.r := q.2.1
    have hζ : q.1.2 ∈ Ann P := q.2.2
    simp only [rawR]
    rw [key_slice P Bs hpl hk e he Ψ hΨ T hT hC Φ hc hc0 hζ, Formalism.FourierDecayAlt.P.CutMP.En.hsVec_sum_smul, inner_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [inner_smul_right]
    ring
  refine ⟨fun l => ent (d.SS l).1, fun l => ent (star (d.SS l)).1,
    fun l ρ' ρ => ⟨hent _ ρ' ρ, hent _ ρ' ρ⟩, ?_⟩
  intro l hl Φ ρ'
  exact ⟨hmain _ (hSL l hl).1 (fun f hf W hW => (hCom l hl f hf W hW).1) Φ ρ',
    hmain _ (hSL l hl).2 (fun f hf W hW => (hCom l hl f hf W hW).2) Φ ρ'⟩

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocToolsAgree
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.LT

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

section agree

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def agNN (p : B.SS k r) : B.SS k r :=
  ((Matrix.of.symm (1 : B.Mat k r), p.1.2), (Matrix.of.symm (1 : B.Mat k r), p.2.2))

def agN (p : B.SS k r) : B.SS k r :=
  ((Matrix.of.symm (1 : B.Mat k r), p.1.2), (Matrix.of.symm (1 : B.Mat k r), Matrix.of.symm (1 : B.Mat k r)))

theorem agNN_inSS (Bs : B.RealPlaceData k r Wp Wq) {p : B.SS k r} (hp : Bs.inSS p) : Bs.inSS (agNN p) := by
  obtain ⟨_, h2, _, h4⟩ := hp
  refine ⟨?_, h2, ?_, h4⟩
  · show Matrix.of (Matrix.of.symm (1 : B.Mat k r)) ∈ _
    rw [Equiv.apply_symm_apply]; exact Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _
  · show Matrix.of (Matrix.of.symm (1 : B.Mat k r)) ∈ _
    rw [Equiv.apply_symm_apply]; exact Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _

theorem agN_inSS (Bs : B.RealPlaceData k r Wp Wq) {p : B.SS k r} (hp : Bs.inSS p) : Bs.inSS (agN p) := by
  obtain ⟨_, h2, _, _⟩ := hp
  refine ⟨?_, h2, ?_, ?_⟩
  · show Matrix.of (Matrix.of.symm (1 : B.Mat k r)) ∈ _
    rw [Equiv.apply_symm_apply]; exact Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _
  · show Matrix.of (Matrix.of.symm (1 : B.Mat k r)) ∈ _
    rw [Equiv.apply_symm_apply]; exact Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _
  · show Matrix.of (Matrix.of.symm (1 : B.Mat k r)) ∈ _
    rw [Equiv.apply_symm_apply]; exact WeylGroupFacts.mem_n_one

theorem sgs_agNN (p : B.SS k r) (g : B.Mat k r) :
    B.sgs (agNN p) g = (Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2 := by
  simp only [B.sgs, agNN, Equiv.apply_symm_apply, inv_one, one_mul, mul_one]

theorem sgs_agN (p : B.SS k r) (g : B.Mat k r) :
    B.sgs (agN p) g = (Matrix.of p.1.2)⁻¹ * g := by
  simp only [B.sgs, agN, Equiv.apply_symm_apply, inv_one, one_mul, mul_one]

theorem sgs_split (p : B.SS k r) (g : B.Mat k r) :
    B.sgs p g = (Matrix.of p.1.1)⁻¹ * ((Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2) * Matrix.of p.2.1 := by
  simp only [B.sgs, mul_assoc]

theorem agree_sgs (Bs : B.RealPlaceData k r Wp Wq) (f₁ f₂ : B.Mat k r → (Wq →L[ℂ] Wp))
    (hL₁ : ∀ g ∈ JF.Om k r Bs.z Bs.z', ∀ n ∈ Nset k r, f₁ (n * g) = psi k r Bs.z cStd n • f₁ g)
    (hR₁ : ∀ g ∈ JF.Om k r Bs.z Bs.z', ∀ n ∈ Nset k r, f₁ (g * n) = psi k r Bs.z' cStd n • f₁ g)
    (hU₁ : ∀ g ∈ JF.Om k r Bs.z Bs.z', ∀ h ∈ UWset k r Bs.z, ∀ h' ∈ UWset k r Bs.z',
      f₁ (h * g * h') = (Bs.π h).comp ((f₁ g).comp (Bs.π' h')))
    (hL₂ : ∀ g ∈ JF.Om k r Bs.z Bs.z', ∀ n ∈ Nset k r, f₂ (n * g) = psi k r Bs.z cStd n • f₂ g)
    (hR₂ : ∀ g ∈ JF.Om k r Bs.z Bs.z', ∀ n ∈ Nset k r, f₂ (g * n) = psi k r Bs.z' cStd n • f₂ g)
    (hU₂ : ∀ g ∈ JF.Om k r Bs.z Bs.z', ∀ h ∈ UWset k r Bs.z, ∀ h' ∈ UWset k r Bs.z',
      f₂ (h * g * h') = (Bs.π h).comp ((f₂ g).comp (Bs.π' h')))
    {p : B.SS k r} (hp : Bs.inSS p) {x : B.Mat k r} (hx : x ∈ JF.Om k r Bs.z Bs.z') (he : f₁ x = f₂ x) :
    f₁ (B.sgs p x) = f₂ (B.sgs p x) := by
  have hp' := hp
  obtain ⟨h1, h2, h3, h4⟩ := hp'
  have hx1 : (Matrix.of p.1.2)⁻¹ * x ∈ JF.Om k r Bs.z Bs.z' := by
    rw [← sgs_agN p x]; exact Formalism.FourierDecayAlt.P.PositiveOrbitOpen.sgs_Om Bs (agN_inSS Bs hp) hx
  have hx2 : (Matrix.of p.1.2)⁻¹ * x * Matrix.of p.2.2 ∈ JF.Om k r Bs.z Bs.z' := by
    rw [← sgs_agNN p x]; exact Formalism.FourierDecayAlt.P.PositiveOrbitOpen.sgs_Om Bs (agNN_inSS Bs hp) hx
  have hn := WeylGroupFacts.mem_n_inv h2
  have hu := Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv h1
  rw [sgs_split, hU₁ _ hx2 _ hu _ h3, hU₂ _ hx2 _ hu _ h3, hR₁ _ hx1 _ h4, hR₂ _ hx1 _ h4,
    hL₁ _ hx _ hn, hL₂ _ hx _ hn, he]

variable [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem agreement_on_domain_holds : AgreeOm := by
  intro k r Wp Wq _ _ _ _ _ _ Bs J F U hJ hag g hg hgU
  obtain ⟨p, hp, q, hq, rfl⟩ := Formalism.FourierDecayAlt.P.psiOnto_true k r Wp Wq Bs g hg
  have hgq := Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom Bs hq
  have hGq : Gf k r Bs.z Bs.z' (B.gq Bs q) ∈ U := by
    have e : Gf k r Bs.z Bs.z' (B.sgs p (B.gq Bs q)) = Gf k r Bs.z Bs.z' (B.gq Bs q) := by
      unfold Gf
      rw [Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs Bs hp, Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs Bs hp]
    rw [← e]; exact hgU
  have hD : ∀ y ∈ JF.Om k r Bs.z Bs.z', y ∈ Q.Glev k r 0 ∩ {g | 0 < Gf k r Bs.z Bs.z' g ∧
      ∀ a : Fin r, Dmin k r Bs.z Bs.z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0} := fun y hy =>
    ⟨Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hy.1, Formalism.FourierDecayAlt.P.CutMP.jdc_of_om _ _ hy⟩
  have hNl : ∀ n ∈ Formalism.QuantumDeterminants.Nset k r, n ∈ Q.Nlev k r 0 := fun n hn => ⟨hn, Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hn.1⟩
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bs.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bs.haarN
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bs.haarW'
  have hN := bessel_unipotent_equiv_holds Wp Wq k r Bs.z Bs.z' cStd Bs.π Bs.π' Bs.μW Bs.μN Bs.μW' F Bs.z_mem Bs.z'_mem
    Bs.haarN.conc (fun n₀ h => Bs.haarN.left n₀ h)
  refine agree_sgs Bs J (B.JF Bs F)
    (fun y hy n hn => hJ.2.1 y (hD y hy) n (hNl n hn))
    (fun y hy n hn => hJ.2.2.1 y (hD y hy) n (hNl n hn))
    (fun y hy h hh h' hh' => hJ.2.2.2 y (hD y hy) h hh h' hh')
    (fun y _ n hn => ?_) (fun y _ n hn => ?_)
    (fun y _ h hh h' hh' => Formalism.FourierDecayAlt.P5.jf_uEquiv Bs F y hh hh')
    hp hgq (hag q hq hGq)
  · have e := hN y n hn 1 WeylGroupFacts.mem_n_one
    rw [Matrix.mul_one, Formalism.FourierDecayAlt.P.BesselCapelliCommutation.psi_one Bs.z'_mem, mul_one] at e
    exact e
  · have e := hN y 1 WeylGroupFacts.mem_n_one n hn
    rw [Matrix.one_mul, Formalism.FourierDecayAlt.P.BesselCapelliCommutation.psi_one Bs.z_mem, one_mul] at e
    exact e

end agree

end Formalism.FourierDecayAlt.P.CutMP.JA.LT

end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadContinuityAtZeroOfStandard
namespace Formalism.FourierDecayAlt.P.TBBx3

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate ENNReal

noncomputable section

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem vecCutAt_of_one (p : KB.Pl P Wp Wq) (χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (hχ : ∀ x, 1 ≤ x → χ x = 1) : TBB.VecCutAt p χ F := by
  intro ε hε γ hγ hle
  have hle0 : ε ≤ D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r γ := hle
  unfold KB.Pl.V D.vecV
  split_ifs with h h'
  · rw [Formalism.FourierDecayAlt.P.JCx1.needs.orbJ_cutF]
    have hG := Formalism.FourierDecayAlt.P.ptG_spec P.k P.r p.T.base.z p.T.base.z' γ h'.choose hγ h'.choose_spec.2.1
    have hle' : ε ≤ Gf P.k P.r p.T.base.z p.T.base.z' h'.choose := hG ▸ hle0
    rw [hχ _ ((one_le_div hε).mpr hle'), Complex.ofReal_one, one_smul]
  · rfl
  · rfl

theorem hsInner_self_re_nonneg (A : Wq →L[ℂ] Wp) : 0 ≤ (B.hsInner A A).re := by
  unfold B.hsInner
  have h := inner_self_nonneg (𝕜 := ℂ) (x := B.hsVec A)
  simpa using h

theorem rr_top_re_nonneg (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (i : ℕ) (w : List C.Letter)
    (h : C.LPt) (hi : P.r < i) : 0 ≤ (p.RR F i w h h).re := by
  unfold KB.Pl.RR D.RRplace
  by_cases h1 : D.IsLocPt h i ∧ D.IsLocPt h i
  · rw [dite_eq_left h1, dite_eq_right (by omega)]
    by_cases h2 : i = P.r + 1
    · rw [if_pos h2]
      by_cases h3 : w = []
      · rw [if_pos h3]
        exact hsInner_self_re_nonneg _
      · rw [if_neg h3]
        unfold Top.topOf
        rw [Complex.re_sum]
        refine Finset.sum_nonneg fun e _ => ?_
        rw [Complex.re_sum]
        refine Finset.sum_nonneg fun ρ _ => ?_
        rw [Complex.re_ofReal_mul]
        exact mul_nonneg (mul_self_nonneg _) (hsInner_self_re_nonneg _)
    · rw [if_neg h2]
      simp
  · rw [dite_eq_right h1]
    simp

theorem posAt_of_forms (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (N : ℕ)
    (hnn : ∀ y, 0 ≤ nn y)
    (hform : ∀ (j : ℕ) (w : List C.Letter) (h : C.LPt), j ≤ P.r → TBB.AdmW P p.l0 Y w → w.length ≤ N →
      0 ≤ (p.RR F j w h h).re) : TBB.PosAt p nn F Y N := by
  intro i w h hw hN
  unfold TBB.Ew TBB.NP
  rw [Complex.re_ofReal_mul]
  apply mul_nonneg
  · apply div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    unfold TBB.normC
    apply List.prod_nonneg
    intro a ha
    rw [List.mem_map] at ha
    obtain ⟨l, _, rfl⟩ := ha
    exact hnn _
  · by_cases hi : i ≤ P.r
    · exact hform i w h hi hw hN
    · exact rr_top_re_nonneg p F i w h (by omega)

theorem ew_zero_nil (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) :
    TBB.Ew p nn G 0 w [] = (p.RR G 0 w [] []).re / TBB.normC nn w := by
  have h1 : ∀ TT : ℝ, TBB.nPt P.k P.r TT [] = 1 := fun TT => by simp [TBB.nPt, C.nAux]
  unfold TBB.Ew TBB.NP
  simp only [h1, Real.sqrt_one, one_mul]
  rw [Complex.re_ofReal_mul, one_div, inv_mul_eq_div]

theorem limZeroAt_of_limits (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (Y : Finset ℝ) (N : ℕ) (κ₀ : ℝ)
    (hE : ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → ∃ sz : ℝ, 0 ≤ sz ∧ sz ≤ TBB.normC nn w ∧
      Tendsto (fun ε : ℝ => (p.RR (D.cutF p.T.base χ F ε) 0 w [] []).re) (𝓝[>] 0)
        (𝓝 (sz * (B.beta p.T.base F F).re)))
    (hB : ENNReal.ofReal (B.beta p.T.base F F).re ≤ ENNReal.ofReal κ₀ * TBB.jN2 p F) :
    TBB.LimZeroAt p nn χ F Y N κ₀ := by
  intro w hw hN
  obtain ⟨sz, hsz0, hszn, hlim⟩ := hE w hw hN
  have hEw : ∀ ε, TBB.Ew p nn (D.cutF p.T.base χ F ε) 0 w [] =
      (p.RR (D.cutF p.T.base χ F ε) 0 w [] []).re / TBB.normC nn w := fun ε => ew_zero_nil p nn _ w
  have hlim2 : Tendsto (fun ε => ENNReal.ofReal (TBB.Ew p nn (D.cutF p.T.base χ F ε) 0 w [])) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal (sz * (B.beta p.T.base F F).re / TBB.normC nn w))) := by
    simp only [hEw]
    exact ENNReal.tendsto_ofReal (hlim.div_const _)
  rw [hlim2.limsup_eq]
  refine le_trans ?_ hB
  rw [ENNReal.ofReal_le_ofReal_iff']
  have hn0 : 0 ≤ TBB.normC nn w := le_trans hsz0 hszn
  by_cases hb : 0 ≤ (B.beta p.T.base F F).re
  · left
    rcases hn0.lt_or_eq with hpos | hzero
    · rw [div_le_iff₀ hpos]
      calc sz * (B.beta p.T.base F F).re ≤ TBB.normC nn w * (B.beta p.T.base F F).re :=
            mul_le_mul_of_nonneg_right hszn hb
        _ = (B.beta p.T.base F F).re * TBB.normC nn w := mul_comm _ _
    · rw [← hzero, div_zero]
      exact hb
  · right
    push_neg at hb
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hsz0 hb.le) hn0

end

end Formalism.FourierDecayAlt.P.TBBx3

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

theorem vector_truncation_at_place {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par} (p : KB.Pl P Wp Wq)
    (χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (hχ : ∀ x, 1 ≤ x → χ x = 1) : Formalism.FourierDecayAlt.TBB.VecCutAt p χ F := by
  exact TBBx3.vecCutAt_of_one p χ F hχ

theorem limit_zero_at_place {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par} (p : KB.Pl P Wp Wq)
    (nn : ℝ → ℝ) (χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (N : ℕ) (κ₀ : ℝ)
    (hE : ∀ w, Formalism.FourierDecayAlt.TBB.AdmW P p.l0 Y w → w.length ≤ N → ∃ sz : ℝ, 0 ≤ sz ∧ sz ≤ Formalism.FourierDecayAlt.TBB.normC nn w ∧
      Tendsto (fun ε : ℝ => (p.RR (D.cutF p.T.base χ F ε) 0 w [] []).re) (𝓝[>] 0)
        (𝓝 (sz * (B.beta p.T.base F F).re)))
    (hB : ENNReal.ofReal (B.beta p.T.base F F).re ≤ ENNReal.ofReal κ₀ * Formalism.FourierDecayAlt.TBB.jN2 p F) :
    Formalism.FourierDecayAlt.TBB.LimZeroAt p nn χ F Y N κ₀ := by
  exact TBBx3.limZeroAt_of_limits p nn χ F Y N κ₀ hE hB

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddGen
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.P.CutMP.JA.BStar Formalism.QuantumDeterminants
open scoped ComplexConjugate Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

section gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]

def orderZeroDifferentialOperator (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (c ca : Coef S v)
    (hadj : ∀ x A B', B.hsInner (c x A) B' = B.hsInner A (ca x B')) :
    B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) :=
  [⟨c, ca, [], fun X hX => by simp at hX, hadj⟩]

variable {S : C.HidaSetting E Wp Wq} {v : Fin S.f} {c ca : Coef S v}
  {hadj : ∀ x A B', B.hsInner (c x A) B' = B.hsInner A (ca x B')}

theorem order_zero_operator_apply (J : B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) :
    B.opApply (orderZeroDifferentialOperator S v c ca hadj) J = fun g => c g (J g) := by
  funext g
  simp only [B.opApply, orderZeroDifferentialOperator, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  first
    | rfl
    | simp [B.Rw]

theorem order_zero_operator_adjoint (J : B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) :
    B.opAdj (orderZeroDifferentialOperator S v c ca hadj) J = fun g => ca g (J g) := by
  funext g
  first
    | (simp [B.opAdj, orderZeroDifferentialOperator]; done)
    | (simp [B.opAdj, orderZeroDifferentialOperator]; rfl)
    | rfl

theorem order_zero_operator_order : B.opOrder (orderZeroDifferentialOperator S v c ca hadj) = 0 := by
  first
    | rfl
    | simp [B.opOrder, orderZeroDifferentialOperator]

end gen

section eqv

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {S : C.HidaSetting E Wp Wq} {T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))} {v : Fin S.f}

theorem eqv_left {c : Coef S v} (he : EqvC S T v c) {g : B.Mat S.G.k S.G.r} (hg : g ∈ B.GV S.G.k S.G.r)
    {n : B.Mat S.G.k S.G.r} (hn : n ∈ Nset S.G.k S.G.r) (X : Wq (S.pl v) →L[ℂ] Wp (S.pl v)) :
    c (n * g) X = c g X := by
  have hp : (T v).base.inSS ((Matrix.of.symm 1, Matrix.of.symm n⁻¹), (Matrix.of.symm 1, Matrix.of.symm 1)) :=
    ⟨by simpa only [Equiv.apply_symm_apply] using P.BigCellZetaMinors.one_uw (T v).base.z, by simpa only [Equiv.apply_symm_apply] using WeylGroupFacts.mem_n_inv hn,
      by simpa only [Equiv.apply_symm_apply] using P.BigCellZetaMinors.one_uw (T v).base.z', by simpa only [Equiv.apply_symm_apply] using WeylGroupFacts.mem_n_one⟩
  have h := he _ hp g hg X
  have hu : IsUnit n.det := WeylGroupFacts.isUnit_of_uh hn.1
  simp only [Equiv.apply_symm_apply, inv_one, (T v).base.π_rep.1, (T v).base.π'_rep.1, B.sgs,
    Matrix.nonsing_inv_nonsing_inv n hu, Matrix.one_mul, Matrix.mul_one] at h
  simpa [ContinuousLinearMap.one_def] using h.symm

theorem eqv_right {c : Coef S v} (he : EqvC S T v c) {g : B.Mat S.G.k S.G.r} (hg : g ∈ B.GV S.G.k S.G.r)
    {n : B.Mat S.G.k S.G.r} (hn : n ∈ Nset S.G.k S.G.r) (X : Wq (S.pl v) →L[ℂ] Wp (S.pl v)) :
    c (g * n) X = c g X := by
  have hp : (T v).base.inSS ((Matrix.of.symm 1, Matrix.of.symm 1), (Matrix.of.symm 1, Matrix.of.symm n)) :=
    ⟨by simpa only [Equiv.apply_symm_apply] using P.BigCellZetaMinors.one_uw (T v).base.z, by simpa only [Equiv.apply_symm_apply] using WeylGroupFacts.mem_n_one,
      by simpa only [Equiv.apply_symm_apply] using P.BigCellZetaMinors.one_uw (T v).base.z', by simpa only [Equiv.apply_symm_apply] using hn⟩
  have h := he _ hp g hg X
  simp only [Equiv.apply_symm_apply, inv_one, (T v).base.π_rep.1, (T v).base.π'_rep.1, B.sgs,
    Matrix.one_mul, Matrix.mul_one] at h
  simpa [ContinuousLinearMap.one_def] using h.symm

theorem eqv_uw {c : Coef S v} (he : EqvC S T v c) {g : B.Mat S.G.k S.G.r} (hg : g ∈ B.GV S.G.k S.G.r)
    {h h' : B.Mat S.G.k S.G.r} (hh : h ∈ UWset S.G.k S.G.r (T v).base.z) (hh' : h' ∈ UWset S.G.k S.G.r (T v).base.z')
    (X : Wq (S.pl v) →L[ℂ] Wp (S.pl v)) :
    c (h * g * h') (((T v).base.π h).comp (X.comp ((T v).base.π' h'))) =
      ((T v).base.π h).comp ((c g X).comp ((T v).base.π' h')) := by
  have hp : (T v).base.inSS ((Matrix.of.symm h, Matrix.of.symm 1), (Matrix.of.symm h'⁻¹, Matrix.of.symm 1)) :=
    ⟨by simpa only [Equiv.apply_symm_apply] using hh, by simpa only [Equiv.apply_symm_apply] using WeylGroupFacts.mem_n_one,
      by simpa only [Equiv.apply_symm_apply] using P.BigCellInversePair.uw_inv hh', by simpa only [Equiv.apply_symm_apply] using WeylGroupFacts.mem_n_one⟩
  have hg' : h * g * h' ∈ B.GV S.G.k S.G.r := WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul hh.1 hg) hh'.1
  have e := he _ hp (h * g * h') hg' X
  have hu' : IsUnit h'.det := WeylGroupFacts.isUnit_of_uh hh'.1
  have hs : B.sgs ((Matrix.of.symm h, Matrix.of.symm 1), (Matrix.of.symm h'⁻¹, Matrix.of.symm 1)) (h * g * h') = g := by
    simp only [B.sgs, Equiv.apply_symm_apply, inv_one, Matrix.mul_one]
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu', Matrix.mul_one, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ (WeylGroupFacts.isUnit_of_uh hh.1), Matrix.one_mul]
  rw [hs] at e
  simpa only [Equiv.apply_symm_apply, Matrix.nonsing_inv_nonsing_inv h' hu'] using e

theorem equivariant_coefficient_preserves_forms {c : Coef S v} (hc : B.CkOn ⊤ (B.GPos (T v).base) c) (he : EqvC S T v c)
    {J : B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} (hJ : J ∈ smoothFormsPositiveCone S T v) :
    (fun g => c g (J g)) ∈ smoothFormsPositiveCone S T v := by
  obtain ⟨hS, hL, hR, hU⟩ := hJ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g₀ hg₀
    obtain ⟨U1, J', hU1, hg1, hJ', hJeq⟩ := hS g₀ hg₀
    obtain ⟨U2, c', hU2, hg2, hc', hceq⟩ := hc g₀ ⟨hg₀.1.1, hg₀.2.1⟩
    have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun g => ContinuousLinearMap.restrictScalarsL ℂ (Wq (S.pl v) →L[ℂ] Wp (S.pl v))
          (Wq (S.pl v) →L[ℂ] Wp (S.pl v)) ℝ ℝ (c' g)) (U1 ∩ U2) :=
      (ContinuousLinearMap.restrictScalarsL ℂ (Wq (S.pl v) →L[ℂ] Wp (S.pl v))
          (Wq (S.pl v) →L[ℂ] Wp (S.pl v)) ℝ ℝ).contDiff.comp_contDiffOn (hc'.mono Set.inter_subset_right)
    refine ⟨U1 ∩ U2, fun g => c' g (J' g), hU1.inter hU2, ⟨hg1, hg2⟩,
      h2.clm_apply (hJ'.mono Set.inter_subset_left), ?_⟩
    intro g hg hgl
    simp only
    rw [hJeq g hg.1 hgl, hceq g hg.2 hgl.1]
  · intro g hg n hn
    simp only
    rw [hL g hg n hn, ContinuousLinearMap.map_smul, eqv_left he hg.1.1 hn.1]
  · intro g hg n hn
    simp only
    rw [hR g hg n hn, ContinuousLinearMap.map_smul, eqv_right he hg.1.1 hn.1]
  · intro g hg h hh h' hh'
    simp only
    rw [hU g hg h hh h' hh', eqv_uw he hg.1.1 hh hh']

end eqv

section transfer

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
  [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

theorem trJ_of_fibMat (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π')
    (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (hFr : IsFrame S T v e) (c : Coef S v)
    (V : M.Ty (D.parOf S v) → M.Ty (D.parOf S v) → Qp (D.parOf S v).r (D.parOf S v).TT → ℂ)
    (hV : FibMat S T v e c V) (b : A (D.parOf S v) (DQ (D.parOf S v)))
    (β : M.Ty (D.parOf S v) → M.Ty (D.parOf S v) → (DQ (D.parOf S v)).R)
    (hβ : ∀ ρ π, b ρ π = (DQ (D.parOf S v)).fnP (β ρ π) (cjD (D.parOf S v) (β ρ π)))
    (hβV : ∀ ρ π q, evD (D.parOf S v) q (β ρ π) = V ρ π q)
    (J : B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (hJ : J ∈ smoothFormsPositiveCone S T v) :
    actA (D.parOf S v) b (trJ S T v e J) = trJ S T v e (fun g => c g (J g)) := by
  funext ρ
  set X := actA (D.parOf S v) b (trJ S T v e J) ρ with hXdef
  have hsm : ∀ π (q : Qp (D.parOf S v).r (D.parOf S v).TT), evQ (D.parOf S v) (trJ S T v e J π) q =
      ((Real.sqrt (MA.wq S.G.k q.1 (D.parOf S v).TT) : ℝ) : ℂ) *
        inner ℂ (B.hsVec (e π q.1.2)) (B.hsVec (J (B.gq (T v).base q.1))) := fun π q =>
    congrFun (En.toSm_val_of_mem (D.parOf S v) (En.trace_smoothness E Wp Wq S T v hPl e hFr J hJ π)) q
  have hw : (fun q : Qp (D.parOf S v).r (D.parOf S v).TT =>
      ((Real.sqrt (MA.wq S.G.k q.1 (D.parOf S v).TT) : ℝ) : ℂ) *
        inner ℂ (B.hsVec (e ρ q.1.2)) (B.hsVec (c (B.gq (T v).base q.1) (J (B.gq (T v).base q.1))))) =
      (X : Qp (D.parOf S v).r (D.parOf S v).TT → ℂ) := by
    funext q
    have hX := actA_fm_apply (D.parOf S v) hβ (trJ S T v e J) ρ q
    change _ = evQ (D.parOf S v) X q
    rw [hX]
    simp only [hsm, hβV]
    have hfib := En.fibre_membership_holds E Wp Wq S T v hPl J hJ q.1 q.2
    have hspan := (hFr.2 q.1.2 q.2.2).2.2 _ hfib
    have hcJ : c (B.gq (T v).base q.1) (J (B.gq (T v).base q.1)) =
        ∑ π, inner ℂ (B.hsVec (e π q.1.2)) (B.hsVec (J (B.gq (T v).base q.1))) •
          c (B.gq (T v).base q.1) (e π q.1.2) := by
      conv_lhs => rw [hspan]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [ContinuousLinearMap.map_smul]
    rw [hcJ, En.hsVec_sum_smul, inner_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun π _ => ?_
    rw [inner_smul_right, hV q.1 q.2 ρ π]
    ring
  unfold trJ
  beta_reduce
  rw [hw]
  unfold MA.toSm
  rw [dite_eq_left X.2]

theorem real_to_bounded_holds : RealToBdd := by
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T v hPl e Cb c ca V b hFr hR hb
  obtain ⟨hadj, hc, hca, he, hea, hbc, hbca, hV⟩ := hR
  choose β hβ hβV using hb
  refine ⟨orderZeroDifferentialOperator S v c ca hadj, order_zero_operator_order, ⟨?_, ?_⟩, ?_, fun J hJ => ⟨?_, ?_, ?_⟩⟩
  · intro Tm hTm
    simp only [orderZeroDifferentialOperator, List.mem_singleton] at hTm
    subst hTm
    exact ⟨hc, hca⟩
  · intro p hp f _ g hg
    rw [order_zero_operator_apply, order_zero_operator_apply]
    exact he p hp g hg.1 _
  · intro Tm hTm ε hε m
    simp only [orderZeroDifferentialOperator, List.mem_singleton] at hTm
    subst hTm
    obtain ⟨C1, h1⟩ := hbc ε hε m
    obtain ⟨C2, h2⟩ := hbca ε hε m
    refine ⟨max C1 C2, fun u w hu hw hl g hg hG => ⟨?_, ?_⟩⟩
    · have hpow : 0 ≤ B.gN g ^ (Cb * ((S.G.r : ℝ) + 1) * m) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
      rw [zero_add]
      exact (h1 u w hu hw hl g hg hG).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpow)
    · have hpow : 0 ≤ B.gN g ^ (Cb * ((S.G.r : ℝ) + 1) * m) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
      rw [zero_add]
      exact (h2 u w hu hw hl g hg hG).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hpow)
  · rw [order_zero_operator_apply]; exact equivariant_coefficient_preserves_forms hc he hJ
  · rw [order_zero_operator_adjoint]; exact equivariant_coefficient_preserves_forms hca hea hJ
  · rw [order_zero_operator_apply]
    exact trJ_of_fibMat S T v hPl e hFr c V hV b β hβ hβV J hJ

end transfer

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpMCont
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

noncomputable section

section tdUv

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

def tdUv (r : ℕ) (Y : ℂ) : ℕ → Fin 2 → (((Fin r → ℂ) → X) → (Fin r → ℂ) → X)
  | 0, b => if b = 0 then id else fun _ => 0
  | 1, b => if h : 1 ≤ r then (if b = 0 then fun f => Y • f - pbOp ⟨r - 1, by omega⟩ f else cbiOp ⟨r - 1, by omega⟩)
      else fun _ => 0
  | m + 2, b => if h : m + 2 ≤ r then
        fun f => Y • tdUv r Y (m + 1) b f - pbOp ⟨r - (m + 2), by omega⟩ (tdUv r Y (m + 1) b f) -
          cbOp ⟨r - (m + 1), by omega⟩ (cbiOp ⟨r - (m + 2), by omega⟩ (tdUv r Y m b f))
      else fun _ => 0

end tdUv

def JDRvCont : Prop :=
  ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (r : ℕ) (Y : ℂ) (O : Set (Fin r → ℂ)), IsOpen O → O ⊆ OmX r →
    ∀ f : (Fin r → ℂ) → X, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f O → ∀ c ∈ O, ∀ b : Fin 2,
      tdUv r Y r b f c = Q.cmp (Q.vABs r Y r) b f c

end

end Formalism.FourierDecayAlt.P.CutMP
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpMTop
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open Matrix

noncomputable section

theorem vtop_rows (k r : ℕ) (s : Fin (k + 1)) : rowsNv k r (Fin.last r) s = rowsN k r (Fin.last r) s := by
  funext j
  apply Fin.ext
  simp [rowsNv, rowsN]

theorem mirror_residue_top_holds : JDRvTop := by
  intro Wp Wq _ _ _ _ k r z z' π π' D Y hz hz' hD J hJ c hc g hg hcg
  have hm : Q.mdim k r (Fin.last r) = k + 1 := by simp [Q.mdim]
  have hpos : ∀ j, (Q.posL k r (Fin.last r) j).val = r + j.val := fun j => by
    simp [Q.posL]; omega
  have hW : Q.wCell k r (Fin.last r) c ∈ Q.Glev k r 0 := Formalism.FourierDecayAlt.P.Qx3.wlist_glev hc _
  simp only [FNv, Q.resG, Q.QL, Q.grp, Q.tL, Pi.neg_apply, neg_neg]
  have e1 : Q.resG k r (Fin.last r) J c =
      ((∏ a : Fin r, (if a.val < (Fin.last r).val then ‖c a‖ ^ (Mdim k r a - 1) else 1) : ℝ) : ℂ) •
        (fun g' => J (Q.wCell k r (Fin.last r) c * g')) := rfl
  rw [e1, Formalism.FourierDecayAlt.P5.chatL_smulC, Pi.smul_apply]
  congr 1
  rw [top_chatL hm _ hpos]
  unfold NLv
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
  rw [Formalism.FourierDecayAlt.P.quantum_minor_left_hermitian, vtop_rows, vtop_rows]
  congr 1
  have ez : Q.wCell k r (Fin.last r) c *ᵥ z = z := top_wlist_wb c _ z hz
  have eh : herm (Hpk k r) ((Q.wCell k r (Fin.last r) c * g) *ᵥ bvec (wI k r s)) z =
      herm (Hpk k r) (g *ᵥ bvec (wI k r s)) z := by
    rw [← Matrix.mulVec_mulVec]
    conv_lhs => rw [← ez]
    exact Formalism.FourierDecayAlt.P.Qx2.herm_uh hW.1 _ _
  have es : Q.posL k r (Fin.last r) (Fin.cast hm.symm s) = wI k r s := by
    apply Fin.ext; simp [Q.posL, wI]; omega
  have et : Q.posL k r (Fin.last r) (Fin.cast hm.symm t) = wI k r t := by
    apply Fin.ext; simp [Q.posL, wI]; omega
  rw [eh]
  simp only [Q.ybv, Q.xv, fvec, es, et]
  simp

end

end Formalism.FourierDecayAlt.P.CutMP
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRModelV
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

noncomputable section

theorem site_vector_eq_tensor_product (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (hL : MA.IsModelLevel P (MA.DQ P) L)
    (y : ℂ) (b : Fin 2) : Wd.v0 (MA.sites P (MA.DQ P)) y b = L.Tprod y b 0 := by
  obtain ⟨hp, -, hc, hci, -⟩ := hL
  have hT : (fun σ => Wd.Ts σ y) ∘ MA.siteA P (MA.DQ P) = L.Tl y := by
    funext l
    simp only [Function.comp_apply]
    unfold R.LevelData.Tl
    rw [hp, hc, hci]
    rfl
  unfold Wd.v0 MA.sites R.LevelData.Tprod
  rw [List.map_reverse, List.map_ofFn, hT]

theorem star_site_vector_eq_tensor (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (hL : MA.IsModelLevel P (MA.DQ P) L)
    (y : ℂ) (a : Fin 2) :
    star (Wd.v0 (MA.sites P (MA.DQ P)) y a) = L.Tvprod (starRingEnd ℂ y) a 0 := by
  have hL' := hL
  obtain ⟨hp, hpb, hc, hci, hcb, hcbi, -⟩ := hL'
  have sp : ∀ l, star (L.p l) = -L.pb l := fun l => by
    rw [hp, hpb]
    show star (MA.sc P (MA.DQ P) ((MA.DQ P).pP l)) = -MA.sc P (MA.DQ P) ((MA.DQ P).pbP l)
    rw [Formalism.FourierDecayAlt.P.MAx3.F.star_sc, Formalism.FourierDecayAlt.P.MAx3.F.star_pP]
    unfold MA.sc
    simp
  have sc : ∀ l, star (L.c l) = L.cb l := fun l => by
    rw [hc, hcb]
    show star (MA.sc P (MA.DQ P) ((MA.DQ P).cP l)) = MA.sc P (MA.DQ P) ((MA.DQ P).cbP l)
    rw [Formalism.FourierDecayAlt.P.MAx3.F.star_sc]
    rfl
  have sci : ∀ l, star (L.ci l) = L.cbi l := fun l => by
    rw [hci, hcbi]
    show star (MA.sc P (MA.DQ P) ((MA.DQ P).ciP l)) = MA.sc P (MA.DQ P) ((MA.DQ P).cbiP l)
    rw [Formalism.FourierDecayAlt.P.MAx3.F.star_sc]
    rfl
  have h := congrArg (fun M => M 0 a) (Formalism.FourierDecayAlt.P.TLB.star_Tprod_gen L sp sc sci y)
  simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply] at h
  rw [site_vector_eq_tensor_product P L hL y a]
  exact h

theorem mirror_residue_model_holds : JDRModelV := by
  intro P L hL y
  refine ⟨fun b => site_vector_eq_tensor_product P L hL (y : ℂ) b, fun a => ?_⟩
  rw [star_site_vector_eq_tensor P L hL (y : ℂ) a, Complex.conj_ofReal]

end

end Formalism.FourierDecayAlt.P.CutMP
end
