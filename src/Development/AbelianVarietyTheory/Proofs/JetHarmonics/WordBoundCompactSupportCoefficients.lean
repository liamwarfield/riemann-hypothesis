module

public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WordOperatorRadialPointwiseBound
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLemB

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BigCellVectorNormEqRadialValueNorm
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BigCellVectorNormEqRadialValueNorm
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF

theorem vec_bigPt_eq_radial : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (c : Fin (P.r + 1) → ℂ), (∀ l, c l ≠ 0) → 0 < TBB.Gp p (TBB.bigPt P.r c) → ∃ x ∈ Q.DomR P.k P.r p.T.base.z p.T.base.z', gR P p.T.base x.1 x.2 = TBB.Gp p (TBB.bigPt P.r c) ∧ dR P p.T.base x.1 x.2 = ‖∏ l, c l‖ ∧ ∃ lam : ℝ, 0 < lam ∧ ∀ (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Φ : Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π'), Top.IsRadOf P p.T.base Φ H → ‖B.hsVec (p.V H (TBB.bigPt P.r c))‖ = lam * nv Φ x := by
  intro Wp Wq _ _ _ _ _ _ P p c hc hG
  have hζ : Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' < Complex.normSq (c (Fin.last P.r)) :=
    Formalism.FourierDecayAlt.P.PBM.zeta_big _ c hG
  have hc' : ∀ a : Fin P.r, c a.castSucc ≠ 0 := fun a => hc _
  have hz := Formalism.FourierDecayAlt.P.NFRadRedA.zeta_muZ p.T.base.z_mem p.T.base.z'_mem p.T.base.sec hζ
  have hx : ((fun a : Fin P.r => c a.castSucc), NF.muZ P.k P.r p.T.base.μsec (c (Fin.last P.r))) ∈
      Q.DomR P.k P.r p.T.base.z p.T.base.z' :=
    Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR p.T.base.z_mem p.T.base.z'_mem p.T.base.sec
      (q := ((fun a : Fin P.r => c a.castSucc), c (Fin.last P.r))) ⟨hc', hζ⟩
  refine ⟨_, hx, ?_, ?_, ?_⟩
  · show Complex.normSq (∏ a : Fin P.r, c a.castSucc) *
        (Complex.normSq (Q.zetaL P.k P.r p.T.base.z p.T.base.z' (Fin.last P.r)
          (NF.muZ P.k P.r p.T.base.μsec (c (Fin.last P.r)))) - Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') =
        D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r (Formalism.FourierDecayAlt.P.PBJ.bigPt c)
    unfold D.ptG
    rw [hz, Formalism.FourierDecayAlt.P.PBM.ptMatN_bigPt_head, Formalism.FourierDecayAlt.P.PBJ.Dens.ptMatN_bigPt, Formalism.FourierDecayAlt.P.PBM.hMat_one,
      Matrix.det_diagonal, Matrix.det_diagonal, Fin.prod_univ_castSucc c, Complex.normSq_mul]
    ring
  · show ‖(∏ a : Fin P.r, c a.castSucc) * Q.zetaL P.k P.r p.T.base.z p.T.base.z' (Fin.last P.r)
          (NF.muZ P.k P.r p.T.base.μsec (c (Fin.last P.r)))‖ = _
    rw [hz, Fin.prod_univ_castSucc c]
  · have hpos : 0 < ∏ a : Fin P.r,
        (if a.val < (Fin.last P.r).val then ‖c a.castSucc‖ ^ (Mdim P.k P.r a - 1) else 1 : ℝ) := by
      refine Finset.prod_pos fun a _ => ?_
      split_ifs
      · exact pow_pos (norm_pos_iff.2 (hc' a)) _
      · exact one_pos
    refine ⟨_, inv_pos.2 hpos, fun H Φ hΦ => ?_⟩
    rw [Formalism.FourierDecayAlt.P.CutBP.hsVec_norm_V_bigPt p H c hc hG]
    unfold nv
    rw [hΦ _ hx]
    unfold Q.resG
    rw [Formalism.FourierDecayAlt.P.TBBx2.Tri.hsVec_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg hpos.le,
      inv_mul_cancel_left₀ hpos.ne']
    have e : Q.wCell P.k P.r (Fin.last P.r) (fun a : Fin P.r => c a.castSucc) *
        NF.muZ P.k P.r p.T.base.μsec (c (Fin.last P.r)) =
        bigCell P.k P.r (fun a : Fin P.r => c a.castSucc) (p.T.base.μsec (c (Fin.last P.r))) := by
      unfold NF.muZ
      rw [Formalism.FourierDecayAlt.P5.Rad.wCell_last_eq, ← (Formalism.FourierDecayAlt.P.bruhat_big_cell_factorization _ _ _ _).1]
    rw [e]

end GlobalTheory.HatNF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BigCellVectorNormEqRadialValueNormStatement
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bigCellVector_norm_eq_radialValue_norm : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (c : Fin (P.r + 1) → ℂ), (∀ l, c l ≠ 0) → 0 < TBB.Gp p (TBB.bigPt P.r c) → ∃ x ∈ Q.DomR P.k P.r p.T.base.z p.T.base.z', gR P p.T.base x.1 x.2 = TBB.Gp p (TBB.bigPt P.r c) ∧ dR P p.T.base x.1 x.2 = ‖∏ l, c l‖ ∧ ∃ lam : ℝ, 0 < lam ∧ ∀ (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Φ : Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π'), Top.IsRadOf P p.T.base Φ H → ‖B.hsVec (p.V H (TBB.bigPt P.r c))‖ = lam * nv Φ x := by
  first | exact @GlobalTheory.HatNF.vec_bigPt_eq_radial | exact GlobalTheory.HatNF.vec_bigPt_eq_radial | (intros; apply GlobalTheory.HatNF.vec_bigPt_eq_radial <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RadialPictureSmulCutoffGMultiplier
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RadialPictureSmulCutoffGMultiplier
namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory

noncomputable section

theorem jf_mulG {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (φ : ℝ → ℝ) (f : B.Mat k r → (Wq →L[ℂ] Wp))
    (g : B.Mat k r) : B.JF Bs (mulG Bs φ f) g = ((φ (Gf k r Bs.z Bs.z' g) : ℝ) : ℂ) • B.JF Bs f g := by
  show ∫ p, JF.xiP Bs p • B.rho Bs p (mulG Bs φ f) g ∂Bs.μSS =
    ((φ (Gf k r Bs.z Bs.z' g) : ℝ) : ℂ) • ∫ p, JF.xiP Bs p • B.rho Bs p f g ∂Bs.μSS
  rw [← integral_smul]
  refine integral_congr_ae ?_
  filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS Bs] with p hp
  simp only [B.rho, mulG, Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs Bs hp]
  rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_comm]


attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem cptCoef_mulG {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) {f : B.Mat k r → (Wq →L[ℂ] Wp)} (hf : KB.CptCoef Bs f) :
    KB.CptCoef Bs (mulG Bs φ f) := by
  obtain ⟨hs, ⟨R, hR⟩, ⟨δ, hδ, hG⟩⟩ := hf
  have hne : ∀ g, mulG Bs φ f g ≠ 0 → f g ≠ 0 := fun g h h0 => h (by simp [mulG, h0])
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun g : B.Mat k r => ((φ (Gf k r Bs.z Bs.z' g) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hφ.comp (Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf Bs.z Bs.z'))
  exact ⟨Formalism.FourierDecayAlt.P.JCx2.pd_smooth_smul hc hs, ⟨R, fun g hg h => hR g hg (hne g h)⟩,
    ⟨δ, hδ, fun g hg h => hG g hg (hne g h)⟩⟩

theorem radial_mulG : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq), ∀ (φ : ℝ → ℝ) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), (ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → LE.SmoothLog φ ∧ (KB.CptCoef Bs f → KB.CptCoef Bs (mulG Bs φ f))) ∧ ∀ (W : ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), IsMulG P Bs φ W → Top.IsRadOf P Bs Φ f → Top.IsRadOf P Bs (W 0 Φ) (mulG Bs φ f) := by
  intro Wp Wq _ _ _ _ _ _ P Bs φ f
  refine ⟨fun hφ => ⟨hφ.comp Real.contDiff_exp, fun hf => cptCoef_mulG Bs hφ hf⟩, ?_⟩
  intro W Φ hW hΦ x hx
  have hcell := Formalism.FourierDecayAlt.P.big_cell_values P.k P.r Wp Wq Bs x hx
  have hpos : 0 < gR P Bs x.1 x.2 := by
    have := hcell.1.2.1
    rw [hcell.2.2.2] at this
    exact this
  have hld : LE.ld 0 φ (gR P Bs x.1 x.2) = φ (gR P Bs x.1 x.2) := by
    simp only [LE.ld, iteratedDeriv_zero, Real.exp_log hpos]
  rw [hW 0 Φ x.1 x.2, hΦ x hx]
  simp only [Q.resG]
  rw [jf_mulG, hcell.2.2.2, hld, smul_comm]
  rfl

end

end GlobalTheory.HatNF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RadialPictureSmulCutoffGMultiplierStatement
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.radial_picture_smul_cutoff_G_multiplier : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq), ∀ (φ : ℝ → ℝ) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), (ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → LE.SmoothLog φ ∧ (KB.CptCoef Bs f → KB.CptCoef Bs (mulG Bs φ f))) ∧ ∀ (W : ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), IsMulG P Bs φ W → Top.IsRadOf P Bs Φ f → Top.IsRadOf P Bs (W 0 Φ) (mulG Bs φ f) := by
  first | exact @GlobalTheory.HatNF.radial_mulG | exact GlobalTheory.HatNF.radial_mulG | (intros; apply GlobalTheory.HatNF.radial_mulG <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsRadialPartPolyDiffOperatorClosed
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PolyOpExistsComposition
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF.PolyComp

open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose MvPolynomial

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {k r : ℕ}

def scalTerm (P : B.Mat k r → ℂ) (w : List (B.Mat k r)) (hw : ∀ X ∈ w, inLie k r X) : DTerm k r Wp Wq where
  coef g := P g • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)
  coefAdj g := star (P g) • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)
  word := w
  word_lie := hw
  adj_id := by
    intro x A B
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, hsInner, PI.UnitaryGroupMassFormula.UsCompose.hsVec_smul,
      inner_smul_right, inner_smul_left, Complex.star_def, Complex.conj_conj]

end

end GlobalTheory.HatNF.PolyComp

namespace GlobalTheory.HatNF

open GlobalTheory.HatNF.PolyComp

end GlobalTheory.HatNF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsRadialPartPolyDiffOperatorClosed
namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory

noncomputable section

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

end

open MvPolynomial in
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {k r : ℕ} in
private lemma polyOp_mono' {n n' κ κ' : ℕ} {Θ : _root_.Formalism.FourierDecayAlt.B.DiffOp k r Wp Wq} (h : _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp n κ Θ)
    (hn : n ≤ n') (hκ : κ ≤ κ') : _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp n' κ' Θ := by
  unfold _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp at h ⊢
  intro T hT
  obtain ⟨hlen, Q, ⟨q, hq, hQ⟩, hc, hca⟩ := h T hT
  exact ⟨hlen.trans hn, Q, ⟨q, hq.trans hκ, hQ⟩, hc, hca⟩

open MvPolynomial in
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {k r : ℕ} in
private lemma polyOp_nil (n κ : ℕ) : _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp n κ ([] : _root_.Formalism.FourierDecayAlt.B.DiffOp k r Wp Wq) := by
  unfold _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp
  simp

open MvPolynomial in
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {k r : ℕ} in
private lemma opApply_nil (F : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp) (g : _root_.Formalism.FourierDecayAlt.B.Mat k r) :
    _root_.Formalism.FourierDecayAlt.B.opApply ([] : _root_.Formalism.FourierDecayAlt.B.DiffOp k r Wp Wq) F g = 0 := by
  simp [_root_.Formalism.FourierDecayAlt.B.opApply]

open MvPolynomial in
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {k r : ℕ} in
private lemma polyOp_of_polyOp_cons {n κ : ℕ} {T : _root_.Formalism.FourierDecayAlt.B.DTerm k r Wp Wq} {Θ : _root_.Formalism.FourierDecayAlt.B.DiffOp k r Wp Wq}
    (h : _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp n κ (T :: Θ)) : _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp n κ Θ := by
  unfold _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp at h ⊢
  exact fun T' hT' => h T' (by simp [hT'])

open MvPolynomial in
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {k r : ℕ} in
private lemma totalDegree_lin_le_one {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ) (i : _root_.PI.UnitaryGroupMassFormula.UsCompose.Vr N) :
    (_root_.PI.UnitaryGroupMassFormula.UsCompose.lin X i).totalDegree ≤ 1 := by
  rcases i with x | x <;>
  · simp only [_root_.PI.UnitaryGroupMassFormula.UsCompose.lin]
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun c _ => ?_)
    exact (totalDegree_mul _ _).trans (by simp [totalDegree_C, totalDegree_X])

open MvPolynomial in
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {k r : ℕ} in
private lemma totalDegree_pderiv_add_one_le_of_ne_zero {σ : Type*} (q : MvPolynomial σ ℂ) (i : σ)
    (h : pderiv i q ≠ 0) : (pderiv i q).totalDegree + 1 ≤ q.totalDegree := by
  have hne : (pderiv i q).support.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr (by simpa [MvPolynomial.support_eq_empty] using h)
  obtain ⟨m, hm, hdeg⟩ := Finset.exists_mem_eq_sup _ hne (fun s : σ →₀ ℕ => s.sum fun _ e => e)
  rw [totalDegree, hdeg]
  have hm' := (mem_support_iff.mp hm)
  rw [coeff_pderiv] at hm'
  have hs : m + Finsupp.single i 1 ∈ q.support := by
    rw [mem_support_iff]
    intro h0
    exact hm' (by simp [h0])
  have := le_totalDegree hs
  rwa [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl] at this

open MvPolynomial in
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {k r : ℕ} in
private lemma totalDegree_dP_le {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ)
    (q : MvPolynomial (_root_.PI.UnitaryGroupMassFormula.UsCompose.Vr N) ℂ) : (_root_.PI.UnitaryGroupMassFormula.UsCompose.dP X q).totalDegree ≤ q.totalDegree := by
  unfold _root_.PI.UnitaryGroupMassFormula.UsCompose.dP
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun i _ => ?_)
  by_cases h : pderiv i q = 0
  · simp [h]
  · exact (totalDegree_mul _ _).trans
      ((Nat.add_le_add_left (totalDegree_lin_le_one X i) _).trans (totalDegree_pderiv_add_one_le_of_ne_zero q i h))

open MvPolynomial in
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {k r : ℕ} in
private lemma exists_isPolyDeg_hasDerivAt_comp_crv {X : _root_.Formalism.FourierDecayAlt.B.Mat k r} {κ : ℕ} {Q : _root_.Formalism.FourierDecayAlt.B.Mat k r → ℂ}
    (hQ : _root_.Formalism.FourierDecayAlt.U.IsPolyDeg κ Q) : ∃ Q' : _root_.Formalism.FourierDecayAlt.B.Mat k r → ℂ, _root_.Formalism.FourierDecayAlt.U.IsPolyDeg κ Q' ∧
      ∀ g, HasDerivAt (fun t => Q (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.crv (false, X) g t)) (Q' g) 0 := by
  obtain ⟨q, hq, hQq⟩ := hQ
  refine ⟨fun g => MvPolynomial.eval (_root_.PI.UnitaryGroupMassFormula.UsCompose.vars g) (_root_.PI.UnitaryGroupMassFormula.UsCompose.dP X q),
    ⟨_root_.PI.UnitaryGroupMassFormula.UsCompose.dP X q, (totalDegree_dP_le X q).trans hq, fun g => rfl⟩, fun g => ?_⟩
  have e : (fun t => Q (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.crv (false, X) g t)) =
      fun t => MvPolynomial.eval (_root_.PI.UnitaryGroupMassFormula.UsCompose.vars (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.crv (false, X) g t)) q := by
    funext t
    rw [hQq]
    rfl
  rw [e]
  exact _root_.PI.UnitaryGroupMassFormula.UsCompose.hasDerivAt_poly X g q

open MvPolynomial in
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {k r : ℕ} in
private lemma ckOn_rightWordDeriv_of_forall_inLie {F : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp}
    (hF : _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) F) : ∀ w : List (_root_.Formalism.FourierDecayAlt.B.Mat k r), (∀ X ∈ w, _root_.Formalism.FourierDecayAlt.B.inLie k r X) →
      _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) (_root_.Formalism.FourierDecayAlt.B.Rw w F)
  | [], _ => by simpa [_root_.Formalism.FourierDecayAlt.B.Rw] using hF
  | X :: w, hw => by
    have h := ckOn_rightWordDeriv_of_forall_inLie hF w (fun Y hY => hw Y (by simp [hY]))
    have := _root_.Formalism.FourierDecayAlt.P.B5.ckOn_RdV (m := ⊤) (hw X (by simp)) (by simpa using h)
    simpa [_root_.Formalism.FourierDecayAlt.B.Rw] using this

open MvPolynomial in
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {k r : ℕ} in
private lemma opApply_cons' (T : _root_.Formalism.FourierDecayAlt.B.DTerm k r Wp Wq) (Θ : _root_.Formalism.FourierDecayAlt.B.DiffOp k r Wp Wq)
    (F : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp) (g : _root_.Formalism.FourierDecayAlt.B.Mat k r) :
    _root_.Formalism.FourierDecayAlt.B.opApply (T :: Θ) F g = (T.coef g) (_root_.Formalism.FourierDecayAlt.B.Rw T.word F g) + _root_.Formalism.FourierDecayAlt.B.opApply Θ F g := by
  simp [_root_.Formalism.FourierDecayAlt.B.opApply]

open MvPolynomial in
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {k r : ℕ} in
private lemma polyOp_deriv_lemma_10 {X : _root_.Formalism.FourierDecayAlt.B.Mat k r} (hX : _root_.Formalism.FourierDecayAlt.B.inLie k r X) {κ : ℕ} :
    ∀ (Θ : _root_.Formalism.FourierDecayAlt.B.DiffOp k r Wp Wq) (n : ℕ), _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp n κ Θ → ∃ Θ' : _root_.Formalism.FourierDecayAlt.B.DiffOp k r Wp Wq,
      _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp (n + 1) κ Θ' ∧ ∀ F : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp, _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) F →
        ∀ g ∈ _root_.Formalism.FourierDecayAlt.B.GV k r,
          HasDerivAt (fun t => _root_.Formalism.FourierDecayAlt.B.opApply Θ F (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.crv (false, X) g t)) (_root_.Formalism.FourierDecayAlt.B.opApply Θ' F g) 0
  | [], n, _ => ⟨[], polyOp_nil _ _, fun F _ g _ => by
      simpa [opApply_nil] using hasDerivAt_const (0 : ℝ) (0 : Wq →L[ℂ] Wp)⟩
  | T :: Θ, n, h => by
    have hT := h
    unfold _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp at hT
    obtain ⟨hlen, Q, hQ, hc, -⟩ := hT T (by simp)
    obtain ⟨Θr, hJr, hDr⟩ := polyOp_deriv_lemma_10 hX Θ n (polyOp_of_polyOp_cons h)
    obtain ⟨Q', hQ', hdQ⟩ := exists_isPolyDeg_hasDerivAt_comp_crv (X := X) hQ
    have hw : ∀ Y ∈ X :: T.word, _root_.Formalism.FourierDecayAlt.B.inLie k r Y := by
      intro Y hY
      rcases List.mem_cons.mp hY with rfl | hY
      exacts [hX, T.word_lie Y hY]
    refine ⟨_root_.GlobalTheory.HatNF.PolyComp.scalTerm Q' T.word T.word_lie ::
      _root_.GlobalTheory.HatNF.PolyComp.scalTerm Q (X :: T.word) hw :: Θr, ?_, ?_⟩
    · unfold _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp at hJr ⊢
      intro T' hT'
      rcases List.mem_cons.mp hT' with rfl | hT'
      · exact ⟨hlen.trans (Nat.le_succ n), Q', hQ', fun _ => rfl, fun _ => rfl⟩
      rcases List.mem_cons.mp hT' with rfl | hT'
      · exact ⟨by simp [_root_.GlobalTheory.HatNF.PolyComp.scalTerm, hlen], Q, hQ, fun _ => rfl, fun _ => rfl⟩
      · exact hJr T' hT'
    · intro F hF g hg
      have hG := ckOn_rightWordDeriv_of_forall_inLie hF T.word T.word_lie
      have hD : HasDerivAt (fun t => _root_.Formalism.FourierDecayAlt.B.Rw T.word F (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.crv (false, X) g t))
          (_root_.Formalism.FourierDecayAlt.B.Rw (X :: T.word) F g) 0 := by
        have := _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_diff (x := (false, X)) hX (_root_.Formalism.FourierDecayAlt.P.B6.smooth_on_mono le_top hG) hg hg
        rw [← _root_.PI.UnitaryGroupMassFormula.UsCompose.RdV_eq_Dx] at this
        exact this
      have hfun : (fun t => _root_.Formalism.FourierDecayAlt.B.opApply (T :: Θ) F (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.crv (false, X) g t)) = fun t =>
          Q (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.crv (false, X) g t) • _root_.Formalism.FourierDecayAlt.B.Rw T.word F (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.crv (false, X) g t) +
            _root_.Formalism.FourierDecayAlt.B.opApply Θ F (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.crv (false, X) g t) := by
        funext t
        rw [opApply_cons', hc]
        simp
      rw [hfun]
      have := ((hdQ g).smul hD).add (hDr F hF g hg)
      refine this.congr_deriv ?_
      rw [opApply_cons', opApply_cons']
      simp only [_root_.GlobalTheory.HatNF.PolyComp.scalTerm, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.id_apply, _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.crv_zero]
      abel

open MvPolynomial in
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {k r : ℕ} in
private lemma polyOp_word_lemma_6 {κ : ℕ} : ∀ (u : List (_root_.Formalism.FourierDecayAlt.B.Mat k r)), (∀ X ∈ u, _root_.Formalism.FourierDecayAlt.B.inLie k r X) →
    ∀ (Θ : _root_.Formalism.FourierDecayAlt.B.DiffOp k r Wp Wq) (n : ℕ), _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp n κ Θ → ∃ Θ' : _root_.Formalism.FourierDecayAlt.B.DiffOp k r Wp Wq,
      _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp (n + u.length) κ Θ' ∧ ∀ F : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp,
        _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) F → ∀ g ∈ _root_.Formalism.FourierDecayAlt.B.GV k r,
          _root_.Formalism.FourierDecayAlt.B.Rw u (_root_.Formalism.FourierDecayAlt.B.opApply Θ F) g = _root_.Formalism.FourierDecayAlt.B.opApply Θ' F g
  | [], _, Θ, n, h => ⟨Θ, h, fun F _ g _ => rfl⟩
  | X :: u, hu, Θ, n, h => by
    have hX : _root_.Formalism.FourierDecayAlt.B.inLie k r X := hu X (by simp)
    obtain ⟨Θ1, hJ1, hE1⟩ := polyOp_word_lemma_6 u (fun Y hY => hu Y (by simp [hY])) Θ n h
    obtain ⟨Θ2, hJ2, hD2⟩ := polyOp_deriv_lemma_10 hX Θ1 (n + u.length) hJ1
    refine ⟨Θ2, ?_, fun F hF g hg => ?_⟩
    · have e : n + (X :: u).length = n + u.length + 1 := by simp [add_assoc]
      rw [e]
      exact hJ2
    · have step : _root_.Formalism.FourierDecayAlt.B.Rw (X :: u) (_root_.Formalism.FourierDecayAlt.B.opApply Θ F) g =
          _root_.Formalism.REAL.RdV X (_root_.Formalism.FourierDecayAlt.B.Rw u (_root_.Formalism.FourierDecayAlt.B.opApply Θ F)) g := rfl
      rw [step, _root_.Formalism.FourierDecayAlt.P.PositiveOrbitOpen.rdV_local isOpen_univ (fun x _ hx => hE1 F hF x hx) hX g (Set.mem_univ g) hg,
        _root_.PI.UnitaryGroupMassFormula.UsCompose.RdV_eq_Dx, _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.Dx_eq]
      exact (hD2 F hF g hg).deriv

open MvPolynomial in
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {k r : ℕ} in
private lemma exists_polyOp_opApply_eq_smul {κa : ℕ} {Pf : _root_.Formalism.FourierDecayAlt.B.Mat k r → ℂ} (hP : _root_.Formalism.FourierDecayAlt.U.IsPolyDeg κa Pf) :
    ∀ (Θ : _root_.Formalism.FourierDecayAlt.B.DiffOp k r Wp Wq) (n κ : ℕ), _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp n κ Θ → ∃ Θ' : _root_.Formalism.FourierDecayAlt.B.DiffOp k r Wp Wq,
      _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp n (κa + κ) Θ' ∧ ∀ (F : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp) g,
        _root_.Formalism.FourierDecayAlt.B.opApply Θ' F g = Pf g • _root_.Formalism.FourierDecayAlt.B.opApply Θ F g
  | [], n, κ, _ => ⟨[], polyOp_nil _ _, fun F g => by simp [opApply_nil]⟩
  | T :: Θ, n, κ, h => by
    have hT := h
    unfold _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp at hT
    obtain ⟨hlen, Q, hQ, hc, -⟩ := hT T (by simp)
    obtain ⟨Θr, hJr, hEr⟩ := exists_polyOp_opApply_eq_smul hP Θ n κ (polyOp_of_polyOp_cons h)
    refine ⟨_root_.GlobalTheory.HatNF.PolyComp.scalTerm (fun g => Pf g * Q g) T.word T.word_lie :: Θr, ?_,
      fun F g => ?_⟩
    · unfold _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp at hJr ⊢
      intro T' hT'
      rcases List.mem_cons.mp hT' with rfl | hT'
      · obtain ⟨p, hp, hPp⟩ := hP
        obtain ⟨q, hq, hQq⟩ := hQ
        exact ⟨hlen, _, ⟨p * q, (totalDegree_mul p q).trans (add_le_add hp hq),
          fun g => by simp [hPp, hQq]⟩, fun _ => rfl, fun _ => rfl⟩
      · exact hJr T' hT'
    · rw [opApply_cons', opApply_cons', hEr F g, hc]
      simp [_root_.GlobalTheory.HatNF.PolyComp.scalTerm, smul_add, mul_smul]

open MvPolynomial in
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {k r : ℕ} in
private lemma opApply_append' (Θ₁ Θ₂ : _root_.Formalism.FourierDecayAlt.B.DiffOp k r Wp Wq)
    (F : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp) (g : _root_.Formalism.FourierDecayAlt.B.Mat k r) :
    _root_.Formalism.FourierDecayAlt.B.opApply (Θ₁ ++ Θ₂) F g = _root_.Formalism.FourierDecayAlt.B.opApply Θ₁ F g + _root_.Formalism.FourierDecayAlt.B.opApply Θ₂ F g := by
  simp [_root_.Formalism.FourierDecayAlt.B.opApply]

open MvPolynomial in
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {k r : ℕ} in
private lemma polyOp_comp_lemma_2 {o₂ κ₁ κ₂ : ℕ} {Θb : _root_.Formalism.FourierDecayAlt.B.DiffOp k r Wp Wq} (hb : _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp o₂ κ₂ Θb) :
    ∀ (Θa : _root_.Formalism.FourierDecayAlt.B.DiffOp k r Wp Wq) (o₁ : ℕ), _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp o₁ κ₁ Θa → ∃ Θ : _root_.Formalism.FourierDecayAlt.B.DiffOp k r Wp Wq,
      _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp (o₁ + o₂) (κ₁ + κ₂) Θ ∧ ∀ F : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp,
        _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) F → ∀ g ∈ _root_.Formalism.FourierDecayAlt.B.GV k r,
          _root_.Formalism.FourierDecayAlt.B.opApply Θ F g = _root_.Formalism.FourierDecayAlt.B.opApply Θa (_root_.Formalism.FourierDecayAlt.B.opApply Θb F) g
  | [], o₁, _ => ⟨[], polyOp_nil _ _, fun F _ g _ => by simp [opApply_nil]⟩
  | T :: Θa, o₁, h => by
    have hT := h
    unfold _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp at hT
    obtain ⟨hlen, Pf, hP, hc, -⟩ := hT T (by simp)
    obtain ⟨Θr, hJr, hEr⟩ := polyOp_comp_lemma_2 hb Θa o₁ (polyOp_of_polyOp_cons h)
    obtain ⟨Θ1, hJ1, hE1⟩ := polyOp_word_lemma_6 T.word T.word_lie Θb o₂ hb
    obtain ⟨Θ2, hJ2, hE2⟩ := exists_polyOp_opApply_eq_smul hP Θ1 (o₂ + T.word.length) κ₂ hJ1
    refine ⟨Θ2 ++ Θr, ?_, fun F hF g hg => ?_⟩
    · have hJ2' := polyOp_mono' hJ2 (show o₂ + T.word.length ≤ o₁ + o₂ by omega) le_rfl
      unfold _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp at hJ2' hJr ⊢
      intro T' hT'
      rcases List.mem_append.mp hT' with hT' | hT'
      exacts [hJ2' T' hT', hJr T' hT']
    · rw [opApply_append', opApply_cons', hE2 F g, ← hE1 F hF g hg, hEr F hF g hg, hc]
      simp


open MeasureTheory in
theorem _root_.GlobalTheory.HatNF.polyLift_closed : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : _root_.Formalism.FourierDecayAlt.M.Par)
    (Bs : _root_.Formalism.FourierDecayAlt.B.RealPlaceData P.k P.r Wp Wq), _root_.GlobalTheory.HatNF.PolyLift P Bs 0 0 1 ∧
      (∀ o o' κ κ' a, o ≤ o' → κ ≤ κ' → _root_.GlobalTheory.HatNF.PolyLift P Bs o κ a →
        _root_.GlobalTheory.HatNF.PolyLift P Bs o' κ' a) ∧
      ∀ o₁ κ₁ o₂ κ₂ a b, _root_.GlobalTheory.HatNF.PolyLift P Bs o₁ κ₁ a →
        _root_.GlobalTheory.HatNF.PolyLift P Bs o₂ κ₂ b →
        _root_.GlobalTheory.HatNF.PolyLift P Bs (o₁ + o₂) (κ₁ + κ₂) (a * b) := by
  intro Wp Wq _ _ _ _ _ _ P Bs
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨[_root_.GlobalTheory.HatNF.PolyComp.scalTerm (fun _ => 1) [] (by simp)], ?_, ?_⟩
    · intro Tm hTm
      simp only [List.mem_singleton] at hTm
      subst hTm
      refine ⟨by simp [_root_.GlobalTheory.HatNF.PolyComp.scalTerm], fun _ => 1, ?_, fun _ => rfl, fun _ => rfl⟩
      exact ⟨MvPolynomial.C 1, by simp, fun g => by simp⟩
    · intro F _ Φ hΦ
      have hF : _root_.Formalism.FourierDecayAlt.B.opApply [_root_.GlobalTheory.HatNF.PolyComp.scalTerm (Wp := Wp) (Wq := Wq) (fun _ => 1) []
          (by simp)] F = F := by
        funext g
        simp [_root_.Formalism.FourierDecayAlt.B.opApply, _root_.Formalism.FourierDecayAlt.B.Rw, _root_.GlobalTheory.HatNF.PolyComp.scalTerm]
      rw [hF]
      exact hΦ
  · rintro o o' κ κ' a ho hκ ⟨Θ, hΘ, hR⟩
    exact ⟨Θ, polyOp_mono' hΘ ho hκ, hR⟩
  · rintro o₁ κ₁ o₂ κ₂ a b ⟨Θa, hJa, hRa⟩ ⟨Θb, hJb, hRb⟩
    obtain ⟨Θ, hJ, hE⟩ := polyOp_comp_lemma_2 hJb Θa o₁ hJa
    refine ⟨Θ, hJ, ?_⟩
    unfold _root_.Formalism.FourierDecayAlt.TL.RadIs at hRa hRb ⊢
    intro F hF Φ hΦ
    have hsmooth : _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV P.k P.r) F := by
      unfold _root_.Formalism.FourierDecayAlt.KB.CptCoef at hF
      exact hF.1
    have hsm : _root_.Formalism.FourierDecayAlt.B.SmoothCoef (_root_.Formalism.FourierDecayAlt.C6.domL Bs ∅) Θb :=
      (_root_.GlobalTheory.HatNF.polyOp_ok P.k P.r Wp Wq o₂ κ₂ Θb hJb).1 _
    have h2 := hRa _ (_root_.Formalism.FourierDecayAlt.P.TLB.cpt_op hF hsm) _ (hRb F hF Φ hΦ)
    unfold _root_.Formalism.FourierDecayAlt.Top.IsRadOf at h2 ⊢
    intro x hx
    rw [show (a * b).1 Φ = a.1 (b.1 Φ) from rfl, h2 x hx]
    unfold _root_.Formalism.FourierDecayAlt.Q.resG
    rw [_root_.Formalism.FourierDecayAlt.P.JCx2.sq_jf_congr Bs (fun g hg => (hE F hsmooth g hg).symm) (_root_.Formalism.FourierDecayAlt.P.TLB.wCell_gv Bs hx)]

end GlobalTheory.HatNF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsRadialPartPolyDiffOperatorClosedStatement
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polyLift_one_mono_mul : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq), PolyLift P Bs 0 0 1 ∧ (∀ o o' κ κ' a, o ≤ o' → κ ≤ κ' → PolyLift P Bs o κ a → PolyLift P Bs o' κ' a) ∧ ∀ o₁ κ₁ o₂ κ₂ a b, PolyLift P Bs o₁ κ₁ a → PolyLift P Bs o₂ κ₂ b → PolyLift P Bs (o₁ + o₂) (κ₁ + κ₂) (a * b) := by
  first | exact @GlobalTheory.HatNF.polyLift_closed | exact GlobalTheory.HatNF.polyLift_closed | (intros; apply GlobalTheory.HatNF.polyLift_closed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIsMulGOfSmoothLog
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
open scoped ContDiff

namespace GlobalTheory.HatNF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem mulG_normSq_contDiff : ContDiff ℝ ∞ (fun w : ℂ => Complex.normSq w) := by
  have h : (fun w : ℂ => Complex.normSq w) = fun w => w.re * w.re + w.im * w.im := by
    funext w; exact Complex.normSq_apply w
  rw [h]
  exact (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)

theorem mulG_ld_contDiffOn {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) (q : ℕ) :
    ContDiffOn ℝ ∞ (LE.ld q φ) (Set.Ioi 0) := by
  have h1 : ContDiff ℝ ∞ (iteratedDeriv q (fun u : ℝ => φ (Real.exp u))) := by
    rw [iteratedDeriv_eq_iterate]
    exact ContDiff.iterate_deriv q hφ
  exact h1.comp_contDiffOn (Real.contDiffOn_log.mono fun x hx => by simpa using (ne_of_gt hx))

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem mulG_gR_contDiff (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) :
    ContDiff ℝ ∞ (fun x : (Fin P.r → ℂ) × Q.Mx P.k P.r => gR P Bs x.1 x.2) := by
  unfold gR Q.GGl
  refine ContDiff.mul (mulG_normSq_contDiff.comp ?_) (ContDiff.sub (mulG_normSq_contDiff.comp ?_) contDiff_const)
  · exact contDiff_prod fun a _ => Formalism.FourierDecayAlt.P.Qx5.coord_contDiff a
  · exact (Formalism.FourierDecayAlt.P.Qx5.zetaL_contDiff _ _ _ _ _).comp contDiff_snd

theorem mulG_gR_pos (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) {x : (Fin P.r → ℂ) × Q.Mx P.k P.r}
    (hx : x ∈ Formalism.FourierDecayAlt.P.Qx5.OpR P.k P.r Bs.z Bs.z') : 0 < gR P Bs x.1 x.2 :=
  mul_pos (Complex.normSq_pos.2 (Finset.prod_ne_zero_iff.2 fun a _ => hx.1 a)) hx.2

theorem mulG_mem (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) (q : ℕ)
    {Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)} (hΦ : Φ ∈ Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
    (fun c g => ((LE.ld q φ (gR P Bs c g) : ℝ) : ℂ) • Φ c g) ∈ Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' := by
  refine Formalism.FourierDecayAlt.P.Qx5.smul_mem (a := fun x => ((LE.ld q φ (gR P Bs x.1 x.2) : ℝ) : ℂ)) ?_ ?_ hΦ
  · refine Complex.ofRealCLM.contDiff.comp_contDiffOn ?_
    exact (mulG_ld_contDiffOn hφ q).comp (mulG_gR_contDiff P Bs).contDiffOn fun x hx => mulG_gR_pos P Bs hx
  · intro x _ h hh h' hh'
    simp only [gR, Formalism.FourierDecayAlt.P.Qx5.GG_inv hh hh']

theorem exists_isMulG_of_smoothLog (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) :
    ∃ W : ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), IsMulG P Bs φ W := by
  refine ⟨fun q =>
    { toFun := fun Φ => ⟨_, mulG_mem P Bs hφ q Φ.2⟩
      map_add' := fun Φ Ψ => ?_
      map_smul' := fun s Φ => ?_ }, fun q Φ c g => rfl⟩
  · apply Subtype.ext
    funext c g
    simp only [Submodule.coe_add, Pi.add_apply, smul_add]
  · apply Subtype.ext
    funext c g
    simp only [Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply]
    exact smul_comm _ _ _

theorem mulG_exists : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ φ : ℝ → ℝ, LE.SmoothLog φ → ∃ W : ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), IsMulG P Bs φ W :=
  fun _ _ _ _ _ _ _ _ P Bs _ _ _ _ _ _ _ _ _ hφ => exists_isMulG_of_smoothLog P Bs hφ

end GlobalTheory.HatNF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WordBoundCompactSupportCoefficients
namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem polyLift_listProd {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (Bs : B.RealPlaceData P.k P.r Wp Wq) (o κ : ℕ) (H : List (RA P Bs)) (hH : ∀ h ∈ H, PolyLift P Bs o κ h) :
    PolyLift P Bs (H.length * o) (H.length * κ) H.prod := by
  obtain ⟨h1, -, hmul⟩ := GlobalTheory.T.polyLift_one_mono_mul Wp Wq P Bs
  induction H with
  | nil => simpa using h1
  | cons a H ih =>
    have := hmul _ _ _ _ _ _ (hH a (by simp)) (ih fun h hh => hH h (by simp [hh]))
    rw [List.prod_cons, List.length_cons, Nat.succ_mul, Nat.succ_mul, add_comm _ o, add_comm _ κ]
    exact this

theorem wordBound_cptCoef : ∀ a : ℕ → ℕ, BasicLiftAll a → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (w : List C.Letter), KB.CutWord P p.l0 w → ∃ (C : ℝ) (J : ℕ) (Θs : List (B.DiffOp P.k P.r Wp Wq)), WordBound p (a P.r) w C J Θs (fun φ f => ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧ KB.CptCoef p.T.base f) := by
  intro a ha Wp Wq _ _ _ _ _ _ P p w hw
  obtain ⟨X, μ, L, st, hD, hL⟩ := p.hΘ
  obtain ⟨d, hd⟩ := Formalism.FourierDecayAlt.P.normal_form_actual Wp Wq P _ _ _ _ p.hP X
  have hNF : IsNF (Bs := p.T.base) X d := hd
  have hok := Formalism.FourierDecayAlt.P.JCTx5.wordOK_of P _ _ _ _ st p.l0 hD.1.1 p.hl.1 p.hl.2.1 hD.2.2.2.2.1 hD.2.2.2.2.2.1 w
    hw.1 hw.2
  have hl : (D.positionted w).length = w.length := by simp [D.positionted]
  obtain ⟨C, J, Ts, hC, hTs, hB⟩ := GlobalTheory.T.wordOperator_radial_pointwise_bound Wp Wq P p.T.base X μ L st p.l0 d hD hNF (Fin w.length) _ (a P.r)
    (ha Wp Wq P p.T.base X μ L st p.l0 d hD hNF) (D.positionted w) hok.1
  rw [hl] at hTs hB
  have hlift : ∀ H : List (RA P p.T.base), ∃ Θ : B.DiffOp P.k P.r Wp Wq, H ∈ Ts →
      Formalism.FourierDecayAlt.P.CutMP.PolyOp (w.length * (2 * P.r + P.k + 1))
        (w.length * (8 * (P.r + 1) * (2 * P.r + P.k + 1))) Θ ∧ TL.RadIs P p.T.base Θ H.prod.1 := by
    intro H
    by_cases hH : H ∈ Ts
    · obtain ⟨Θ, hΘ⟩ := polyLift_listProd P p.T.base _ _ H (hTs H hH).2
      rw [(hTs H hH).1] at hΘ
      exact ⟨Θ, fun _ => hΘ⟩
    · obtain ⟨Θ, -⟩ := (GlobalTheory.T.polyLift_one_mono_mul Wp Wq P p.T.base).1
      exact ⟨Θ, fun h => absurd h hH⟩
  choose lf hlf using hlift
  refine ⟨C, J, Ts.map lf, hC, ?_, ?_⟩
  · intro Θ hΘ
    obtain ⟨H, hH, rfl⟩ := List.mem_map.1 hΘ
    exact (hlf H hH).1
  · rintro φ f ⟨hφ, hf⟩ e c hc hG
    obtain ⟨hm1, hm2⟩ := GlobalTheory.T.radial_picture_smul_cutoff_G_multiplier Wp Wq P p.T.base φ f
    obtain ⟨hsl, hcpt⟩ := hm1 hφ
    obtain ⟨W, hW⟩ := mulG_exists Wp Wq P p.T.base X μ L st p.l0 d hD hNF φ hsl
    obtain ⟨⟨ε, hε, hN⟩, -⟩ := Formalism.FourierDecayAlt.P.compact_support_facts P.k P.r Wp Wq p.T.base f hf
    obtain ⟨Φ, hΦ⟩ := Formalism.FourierDecayAlt.P5.radJFExists Wp Wq P _ _ _ _ p.T.base f p.hP rfl rfl rfl rfl
      ⟨hN.2.1, ε, hε, hN.2.2⟩
    have hΦ' : Top.IsRadOf P p.T.base Φ f := hΦ
    have hrad := hL w hw _ (hcpt hf) _ (hm2 W Φ hW hΦ') e
    rw [TL.act_e1Vec] at hrad
    obtain ⟨x, hx, hg, hdd, lam, hlam, hV⟩ := GlobalTheory.T.bigCellVector_norm_eq_radialValue_norm Wp Wq P p c hc hG
    have hb := hB φ W hsl hW Φ e x hx
    rw [hg, hdd] at hb
    have hs : ((Ts.map lf).map fun Θ => ‖B.hsVec (p.V (B.opApply Θ f) (TBB.bigPt P.r c))‖).sum =
        lam * (Ts.map fun H => nv (H.prod.1 Φ) x).sum := by
      rw [List.map_map, ← List.sum_map_mul_left]
      congr 1
      refine List.map_congr_left fun H hH => ?_
      exact hV _ _ ((hlf H hH).2 f hf Φ hΦ')
    rw [hV _ _ hrad, hs]
    have := mul_le_mul_of_nonneg_left hb hlam.le
    refine le_trans (le_of_eq rfl) (this.trans (le_of_eq ?_))
    ring

end GlobalTheory.HatNF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WordBoundCompactSupportCoefficientsStatement
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wordBound_compactSupportCoefficients : ∀ a : ℕ → ℕ, BasicLiftAll a → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (w : List C.Letter), KB.CutWord P p.l0 w → ∃ (C : ℝ) (J : ℕ) (Θs : List (B.DiffOp P.k P.r Wp Wq)), WordBound p (a P.r) w C J Θs (fun φ f => ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧ KB.CptCoef p.T.base f) := by
  first | exact @GlobalTheory.HatNF.wordBound_cptCoef | exact GlobalTheory.HatNF.wordBound_cptCoef | (intros; apply GlobalTheory.HatNF.wordBound_cptCoef <;> assumption)
end
