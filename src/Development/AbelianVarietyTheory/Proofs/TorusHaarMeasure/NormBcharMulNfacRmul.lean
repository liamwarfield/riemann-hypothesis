module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfE
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.NormBcharMulNfacRmul
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.NormFactor

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private lemma nfac_eq_prod_norm_dmin_ratio_rpow {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) :
    X.nfac la x = ∏ τ, ∏ i : Fin r,
      ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.succ / _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.castSucc‖ ^ (-(la τ i : ℝ) / 2) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.nfac _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin
  rfl

private lemma blockTriangular_id_of_mem_bor {r : ℕ} {Ψ : Finset (E →+* ℂ)} {b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r} (hb : b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor Ψ r)
    (τ : Ψ) : (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ).BlockTriangular id := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor at hb
  intro a c hca
  exact (hb τ).2 a c hca

private lemma mat_diag_ne_zero_of_mem_bor {r : ℕ} {Ψ : Finset (E →+* ℂ)} {b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r}
    (hb : b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor Ψ r) (τ : Ψ) (j : Fin r) : _root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ j j ≠ 0 := by
  have hdet := (show (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ).det ≠ 0 by unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor at hb; exact (hb τ).1)
  rw [Matrix.det_of_upperTriangular (blockTriangular_id_of_mem_bor hb τ)] at hdet
  exact Finset.prod_ne_zero_iff.1 hdet j (Finset.mem_univ j)

private lemma diag_prod_ne_zero_of_mem_bor {r : ℕ} {Ψ : Finset (E →+* ℂ)} {b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r}
    (hb : b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor Ψ r) (τ : Ψ) (i : Fin (r + 1)) :
    ∏ j : Fin i, _root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ (Fin.castLE (by omega) j) (Fin.castLE (by omega) j) ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun j _ => mat_diag_ne_zero_of_mem_bor hb τ _

private lemma gram_rmul_eq_transpose_mul_gram {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) (τ : X.Ψ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.gram (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) τ) =
      (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ).transpose * _root_.ReciprocityTheory.ChartRestriction.G.FD.gram (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) * (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ).map (starRingEnd ℂ) := by
  have hmul : _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) τ = _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul
    conv_lhs => unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.mat
    rfl
  rw [hmul, _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.gram_mul]

private lemma dmin_rmul_eq_diag_prod_mul_conj {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) (hb : b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r)
    (τ : X.Ψ) (i : Fin (r + 1)) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) τ i = (∏ j : Fin i, _root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ (Fin.castLE (by omega) j) (Fin.castLE (by omega) j)) *
      _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i * starRingEnd ℂ (∏ j : Fin i, _root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ (Fin.castLE (by omega) j) (Fin.castLE (by omega) j)) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin
  rw [gram_rmul_eq_transpose_mul_gram]
  exact _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.lminor_conj (blockTriangular_id_of_mem_bor hb τ) i

private lemma diag_prod_succ {r : ℕ} (M : Matrix (Fin r) (Fin r) ℂ) (i : Fin r) :
    ∏ j : Fin (i.succ : ℕ), M (Fin.castLE (by omega) j) (Fin.castLE (by omega) j) =
      (∏ j : Fin (i.castSucc : ℕ), M (Fin.castLE (by omega) j) (Fin.castLE (by omega) j)) * M i i := by
  show ∏ j : Fin ((i : ℕ) + 1), M (Fin.castLE (by omega) j) (Fin.castLE (by omega) j) = _
  rw [Fin.prod_univ_castSucc]
  rfl

private lemma norm_ratio_rmul_lemma_2 {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r)
    (hb : b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r) (τ : X.Ψ) (i : Fin r) :
    ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) τ i.succ / _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) τ i.castSucc‖ =
      ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ i i‖ ^ 2 * ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.succ / _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.castSucc‖ := by
  have hp := diag_prod_ne_zero_of_mem_bor hb τ i.castSucc
  rw [dmin_rmul_eq_diag_prod_mul_conj X x b hb τ i.succ, dmin_rmul_eq_diag_prod_mul_conj X x b hb τ i.castSucc, diag_prod_succ]
  simp only [norm_div, norm_mul, map_mul, RCLike.norm_conj]
  have hp' : ‖∏ j : Fin (i.castSucc : ℕ), _root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ (Fin.castLE (by omega) j) (Fin.castLE (by omega) j)‖ ≠ 0 :=
    norm_ne_zero_iff.2 hp
  by_cases hm : ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.castSucc‖ = 0
  · simp [hm]
  · field_simp

private lemma rpow_sq_mul_eq_inv_zpow_mul_rpow {d t : ℝ} (hd : 0 ≤ d) (ht : 0 ≤ t) (l : ℤ) :
    (d ^ 2 * t) ^ (-(l : ℝ) / 2) = (d ^ l)⁻¹ * t ^ (-(l : ℝ) / 2) := by
  rw [Real.mul_rpow (by positivity) ht, ← Real.rpow_natCast, ← Real.rpow_mul hd]
  congr 1
  rw [show ((2 : ℕ) : ℝ) * (-(l : ℝ) / 2) = -(l : ℝ) by push_cast; ring, Real.rpow_neg hd,
    Real.rpow_intCast]

theorem _root_.GlobalTheory.NormFactor.norm_bchar_mul_nfac_rmul {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r)
    {x b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hx : x ∈ X.dom) (hb : b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r) :
    ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.bchar la b‖ * X.nfac la (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) = X.nfac la x := by
  rw [nfac_eq_prod_norm_dmin_ratio_rpow, nfac_eq_prod_norm_dmin_ratio_rpow]
  simp_rw [norm_ratio_rmul_lemma_2 X x b hb, rpow_sq_mul_eq_inv_zpow_mul_rpow (norm_nonneg _) (norm_nonneg _),
    Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  have hbc : ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.bchar la b‖ = ∏ τ, ∏ i : Fin r, ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ i i‖ ^ la τ i := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.bchar _root_.ReciprocityTheory.ChartRestriction.G.FD.mat
    simp [norm_prod, norm_zpow]
  have hne : ∏ τ, ∏ i : Fin r, ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ i i‖ ^ la τ i ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun τ _ => Finset.prod_ne_zero_iff.2 fun i _ =>
      zpow_ne_zero _ (norm_ne_zero_iff.2 (mat_diag_ne_zero_of_mem_bor hb τ i))
  rw [hbc, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]

theorem _root_.GlobalTheory.NormFactor.nfacRmul_holds : _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.NfacRmulStatement (E := E) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.NfacRmulStatement
  intro r X la x hx b hb
  have hne : ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.bchar la b‖ ≠ 0 := norm_ne_zero_iff.2 (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE.bchar_ne X la hb)
  rw [eq_inv_mul_iff_mul_eq₀ hne]
  exact _root_.GlobalTheory.NormFactor.norm_bchar_mul_nfac_rmul X la hx hb

theorem _root_.GlobalTheory.NormFactor.dmin_lact {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {γ : GL (Fin r) E}
    (hγ : γ ∈ X.Γ) (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) (τ : X.Ψ) (i : Fin (r + 1)) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ x) τ i = _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin
  rw [_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS.gram_lact X hγ x τ]

theorem _root_.GlobalTheory.NormFactor.nfacLact_holds : _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.NfacLactStatement (E := E) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.NfacLactStatement
  intro r X la γ hγ x _
  rw [nfac_eq_prod_norm_dmin_ratio_rpow, nfac_eq_prod_norm_dmin_ratio_rpow]
  simp only [_root_.GlobalTheory.NormFactor.dmin_lact X hγ]

theorem _root_.GlobalTheory.NormFactor.pnormInv_holds : _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.PnormInvStatement (E := E) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.PnormInvStatement
  intro r X la P hP γ hγ x hx b hb
  have hpn : ∀ y, X.pnorm la P y = ‖P y‖ * X.nfac la y := by
    intro y
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm
    rw [nfac_eq_prod_norm_dmin_ratio_rpow]
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.IsSec at hP
  obtain ⟨-, hPb, hPγ⟩ := hP
  have hxb := _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS.dom_rmul X hx hb
  have hlact := _root_.GlobalTheory.NormFactor.nfacLact_holds (E := E)
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.NfacLactStatement at hlact
  rw [hpn, hpn, hPγ γ hγ _ hxb, norm_mul, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE.chi_norm X la hγ, one_mul, hlact r X la γ hγ _ hxb,
    hPb x hx b hb, norm_mul, ← _root_.GlobalTheory.NormFactor.norm_bchar_mul_nfac_rmul X la hx hb]
  ring

theorem _root_.GlobalTheory.NormFactor.nfac_transform :
    _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.NfacRmulStatement (E := E) ∧ _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.NfacLactStatement (E := E) ∧ _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.PnormInvStatement (E := E) :=
  ⟨_root_.GlobalTheory.NormFactor.nfacRmul_holds, _root_.GlobalTheory.NormFactor.nfacLact_holds, _root_.GlobalTheory.NormFactor.pnormInv_holds⟩

end GlobalTheory.NormFactor
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasurableSetSatFrames
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.Unfold

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def satFrames (X : Data E r) (x0 : Frame X.Ψ r) (A : Set (V (nd X))) : Set (Frame X.Ψ r) :=
  {x | ∃ z ∈ A, ∃ b ∈ Bor X.Ψ r, x = rmul (cpt X x0 z) b}

theorem measurableSet_Bor (X : Data E r) : MeasurableSet (Bor X.Ψ r) := by
  have h : Bor X.Ψ r = ⋂ τ : X.Ψ, ({b : Frame X.Ψ r | (mat b τ).det ≠ 0} ∩
      ⋂ a : Fin r, ⋂ c : Fin r, ⋂ (_ : c < a), {b : Frame X.Ψ r | b τ a c = 0}) := by
    ext b; simp [Bor]
  rw [h]
  refine MeasurableSet.iInter fun τ => MeasurableSet.inter ?_ ?_
  · have hM : Continuous fun b : Frame X.Ψ r => mat b τ := continuous_apply τ
    exact (isOpen_ne_fun hM.matrix_det continuous_const).measurableSet
  · refine MeasurableSet.iInter fun a => MeasurableSet.iInter fun c => MeasurableSet.iInter fun _ => ?_
    exact (isClosed_eq (by fun_prop) continuous_const).measurableSet

theorem continuous_rmul (X : Data E r) :
    Continuous fun p : Frame X.Ψ r × Frame X.Ψ r => rmul p.1 p.2 := by
  refine continuous_pi fun τ => ?_
  have hM : Continuous fun b : Frame X.Ψ r => mat b τ := continuous_apply τ
  exact (hM.comp continuous_fst).matrix_mul (hM.comp continuous_snd)

theorem continuous_lact (X : Data E r) (γ : GL (Fin r) E) :
    Continuous fun x : Frame X.Ψ r => lact γ x := by
  refine continuous_pi fun τ => ?_
  have hM : Continuous fun b : Frame X.Ψ r => mat b τ := continuous_apply τ
  exact continuous_const.matrix_mul hM

theorem rmul_right_cancel (X : Data E r) {y b b' : Frame X.Ψ r} (hy : y ∈ X.dom)
    (h : rmul y b = rmul y b') : b = b' := by
  funext τ
  have h1 : mat y τ * mat b τ = mat y τ * mat b' τ := congrFun h τ
  have hu : IsUnit (mat y τ).det := isUnit_iff_ne_zero.mpr (hy τ).1
  have := congrArg (fun M => (mat y τ)⁻¹ * M) h1
  simp only [Matrix.nonsing_inv_mul_cancel_left _ _ hu] at this
  exact this

theorem measurableSet_satFrames (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0)
    {A : Set (V (nd X))} (hA : MeasurableSet A) (hAO : A ⊆ OmF X x0) :
    MeasurableSet (satFrames X x0 A) := by
  have h : satFrames X x0 A =
      (fun p : V (nd X) × Frame X.Ψ r => rmul (cpt X x0 p.1) p.2) '' (A ×ˢ Bor X.Ψ r) := by
    ext x
    constructor
    · rintro ⟨z, hz, b, hb, rfl⟩; exact ⟨(z, b), ⟨hz, hb⟩, rfl⟩
    · rintro ⟨⟨z, b⟩, ⟨hz, hb⟩, rfl⟩; exact ⟨z, hz, b, hb, rfl⟩
  rw [h]
  have : PolishSpace (Fin r → ℂ) := inferInstance
  have : PolishSpace (Fin r → Fin r → ℂ) := inferInstance
  have : PolishSpace (Frame X.Ψ r) := inferInstance
  have : PolishSpace (V (nd X)) := inferInstance
  refine MeasurableSet.image_of_continuousOn_injOn (hA.prod (measurableSet_Bor X)) ?_ ?_
  · exact ((continuous_rmul X).comp (((FundSetPf.cont_cpt X x0).comp continuous_fst).prodMk
      continuous_snd)).continuousOn
  · rintro ⟨z, b⟩ ⟨hz, hb⟩ ⟨z', b'⟩ ⟨-, hb'⟩ hh
    obtain rfl : z = z' := FundSetPf.cpt_uniq X ho hb hb' hh
    exact Prod.ext rfl (rmul_right_cancel X (hAO hz) hh)

theorem rmul_mem_satFrames_iff (X : Data E r) (x0 : Frame X.Ψ r) (A : Set (V (nd X)))
    (x : Frame X.Ψ r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) :
    rmul x b ∈ satFrames X x0 A ↔ x ∈ satFrames X x0 A := by
  constructor
  · rintro ⟨z, hz, b', hb', h⟩
    refine ⟨z, hz, rmul b' (ExtFPf.invF X b), ExtFPf.mul_mem X hb' (ExtFPf.invF_mem X hb), ?_⟩
    rw [← ExtFPf.rmul_assoc, ← h, ExtFPf.rmul_assoc, ExtFPf.rmul_invF X hb, ExtFPf.rmul_oneF]
  · rintro ⟨z, hz, b', hb', rfl⟩
    exact ⟨z, hz, rmul b' b, ExtFPf.mul_mem X hb' hb, by rw [ExtFPf.rmul_assoc]⟩

theorem cpt_mem_satFrames_iff (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0)
    (A : Set (V (nd X))) (z : V (nd X)) : cpt X x0 z ∈ satFrames X x0 A ↔ z ∈ A := by
  constructor
  · rintro ⟨z', hz', b, hb, h⟩
    rw [← ExtFPf.rmul_oneF X (cpt X x0 z)] at h
    rw [FundSetPf.cpt_uniq X ho (ExtFPf.oneF_mem X) hb h]; exact hz'
  · intro hz
    exact ⟨z, hz, ExtFPf.oneF X, ExtFPf.oneF_mem X, (ExtFPf.rmul_oneF X _).symm⟩

theorem cpt_lact (X : Data E r) (x0 : Frame X.Ψ r) (γ : GL (Fin r) E) (z : V (nd X)) :
    cpt X (lact γ x0) z = lact γ (cpt X x0 z) := (FundSetPf.lact_rmul γ _ _).symm

theorem isOrth_lact (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) {γ : GL (Fin r) E}
    (hγ : γ ∈ X.Γ) : IsOrth X (lact γ x0) := fun τ => by
  rw [OntoS.gram_lact X hγ]; exact ho τ

theorem muF_lact (X : Data E r) (x0 : Frame X.Ψ r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) :
    muF X (lact γ x0) = muF X x0 := by
  have h1 : OmF X (lact γ x0) = OmF X x0 := by
    ext z
    show cpt X (lact γ x0) z ∈ X.dom ↔ cpt X x0 z ∈ X.dom
    rw [cpt_lact]
    refine ⟨fun h => ?_, OntoS.dom_lact X hγ⟩
    have := OntoS.dom_lact X (X.Γ.inv_mem hγ) h
    rwa [FundSetPf.lact_inv] at this
  have h2 : densF X (lact γ x0) = densF X x0 := by
    funext z
    simp only [densF, dmin, cpt_lact, OntoS.gram_lact X hγ]
  simp only [muF, h1, h2]

theorem unique_translate (X : Data E r) {x0 : Frame X.Ψ r} {FF : Set (V (nd X))}
    (hF : IsFundSet X x0 FF) {x : Frame X.Ψ r} {γ γ' : GL (Fin r) E} (hγ : γ ∈ X.Γ) (hγ' : γ' ∈ X.Γ)
    (h : lact γ⁻¹ x ∈ satFrames X x0 FF) (h' : lact γ'⁻¹ x ∈ satFrames X x0 FF) : γ = γ' := by
  obtain ⟨z, hz, b, hb, h⟩ := h
  obtain ⟨z', hz', b', hb', h'⟩ := h'
  have hδ : γ'⁻¹ * γ ∈ X.Γ := X.Γ.mul_mem (X.Γ.inv_mem hγ') hγ
  have e1 : lact (γ'⁻¹ * γ) (rmul (cpt X x0 z) b) = rmul (cpt X x0 z') b' := by
    rw [← h, ← h', ← FundSetPf.lact_mul, mul_assoc, mul_inv_cancel, mul_one]
  have hbb := ExtFPf.mul_mem X hb (ExtFPf.invF_mem X hb')
  have e2 : cpt X x0 z' = lact (γ'⁻¹ * γ) (rmul (cpt X x0 z) (rmul b (ExtFPf.invF X b'))) := by
    rw [← ExtFPf.rmul_assoc, FundSetPf.lact_rmul, e1, ExtFPf.rmul_assoc, ExtFPf.rmul_invF X hb',
      ExtFPf.rmul_oneF]
  obtain rfl : z = z' := hF.2.2.1 z hz z' hz' _ hδ _ hbb e2
  have e3 : lact (γ'⁻¹ * γ) (cpt X x0 z) = rmul (cpt X x0 z) (rmul b' (ExtFPf.invF X b)) := by
    rw [← ExtFPf.rmul_assoc, ← e1, ← FundSetPf.lact_rmul, ExtFPf.rmul_assoc, ExtFPf.rmul_invF X hb,
      ExtFPf.rmul_oneF]
  have := X.Γ_free _ hδ _ (hF.2.1 hz) _ (ExtFPf.mul_mem X hb' (ExtFPf.invF_mem X hb)) e3
  exact (inv_mul_eq_one.mp this).symm

theorem lintegral_unfold (hM : MeasInvStatement (E := E)) (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r)
    (ho : IsOrth X x0) (FF : Set (V (nd X))) (hF : IsFundSet X x0 FF) (ψ : Frame X.Ψ r → ℝ≥0∞)
    (hψ : Measurable ψ) (hB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ψ (rmul x b) = ψ x) :
    ∫⁻ z, ψ (cpt X x0 z) ∂muF X x0 =
      ∫⁻ z in FF, ∑' γ : X.Γ, ψ (lact γ.1 (cpt X x0 z)) ∂muF X x0 := by
  classical
  have := FundSetPf.countable_GL (E := E) (r := r)
  have hS := measurableSet_satFrames X ho hF.1 hF.2.1
  have hc : Measurable (cpt X x0) := (FundSetPf.cont_cpt X x0).measurable
  let φ : X.Γ → Frame X.Ψ r → ℝ≥0∞ := fun γ =>
    ((fun x => lact (γ.1)⁻¹ x) ⁻¹' satFrames X x0 FF).indicator ψ
  have hφm : ∀ γ, Measurable (φ γ) := fun γ =>
    hψ.indicator ((continuous_lact X _).measurable hS)
  have hφB : ∀ γ, ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ γ (rmul x b) = φ γ x := by
    intro γ x hx b hb
    simp only [φ, Set.indicator, Set.mem_preimage, FundSetPf.lact_rmul,
      rmul_mem_satFrames_iff X x0 FF _ hb, hB x hx b hb]
  have h1 : ∀ᵐ z ∂muF X x0, ψ (cpt X x0 z) = ∑' γ : X.Γ, φ γ (cpt X x0 z) := by
    filter_upwards [hF.2.2.2] with z hz
    obtain ⟨z', hz', γ, hγ, b, hb, h⟩ := hz
    have hm : lact γ⁻¹ (cpt X x0 z) ∈ satFrames X x0 FF :=
      ⟨z', hz', b, hb, by rw [h, FundSetPf.lact_inv]⟩
    rw [tsum_eq_single (⟨γ, hγ⟩ : X.Γ)]
    · exact (Set.indicator_of_mem (s := (fun x => lact γ⁻¹ x) ⁻¹' satFrames X x0 FF) hm ψ).symm
    · intro γ' hne
      refine Set.indicator_of_notMem (fun hm' => hne ?_) ψ
      exact Subtype.ext (unique_translate X hF γ'.2 hγ hm' hm)
  rw [lintegral_congr_ae h1,
    lintegral_tsum (f := fun γ z => φ γ (cpt X x0 z)) fun γ => ((hφm γ).comp hc).aemeasurable,
    lintegral_tsum (f := fun (γ : X.Γ) z => ψ (lact γ.1 (cpt X x0 z))) fun γ : X.Γ =>
      ((hψ.comp (continuous_lact X γ.1).measurable).comp hc).aemeasurable]
  refine tsum_congr fun γ => ?_
  rw [hM r X x0 (lact γ.1 x0) ho (isOrth_lact X ho γ.2) (φ γ) (hφm γ) (hφB γ), muF_lact X x0 γ.2,
    ← lintegral_indicator hF.1]
  refine lintegral_congr fun z => ?_
  simp only [φ, Set.indicator, Set.mem_preimage, cpt_lact, FundSetPf.lact_inv,
    cpt_mem_satFrames_iff X ho]

end GlobalTheory.Unfold
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasurableSetBorSat
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.FrameMeas

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def borSat {r : ℕ} (X : Data E r) (C : Set (Frame X.Ψ r)) : Set (Frame X.Ψ r) :=
  {y | ∃ x ∈ C, ∃ b ∈ Bor X.Ψ r, y = rmul x b}

theorem borSat_subset_dom {r : ℕ} (X : Data E r) {C : Set (Frame X.Ψ r)} (hC : C ⊆ X.dom) :
    borSat X C ⊆ X.dom := by
  rintro y ⟨x, hx, b, hb, rfl⟩
  exact OrthogonalFrameDomain.rmul_mem_dom X (hC hx) hb

theorem subset_borSat {r : ℕ} (X : Data E r) (C : Set (Frame X.Ψ r)) : C ⊆ borSat X C :=
  fun x hx => ⟨x, hx, ExtFPf.oneF X, ExtFPf.oneF_mem X, (ExtFPf.rmul_oneF X x).symm⟩

theorem rmul_mem_borSat_iff {r : ℕ} (X : Data E r) (C : Set (Frame X.Ψ r)) {y b : Frame X.Ψ r}
    (hb : b ∈ Bor X.Ψ r) : rmul y b ∈ borSat X C ↔ y ∈ borSat X C := by
  constructor
  · rintro ⟨x, hx, b', hb', h⟩
    refine ⟨x, hx, rmul b' (ExtFPf.invF X b), ExtFPf.mul_mem X hb' (ExtFPf.invF_mem X hb), ?_⟩
    rw [← ExtFPf.rmul_assoc, ← h, ExtFPf.rmul_assoc, ExtFPf.rmul_invF X hb, ExtFPf.rmul_oneF]
  · rintro ⟨x, hx, b', hb', rfl⟩
    exact ⟨x, hx, rmul b' b, ExtFPf.mul_mem X hb' hb, ExtFPf.rmul_assoc X _ _ _⟩

theorem measurableSet_borSat {r : ℕ} (X : Data E r) {C : Set (Frame X.Ψ r)} (hK : IsCompact C)
    (hC : C ⊆ X.dom) : MeasurableSet (borSat X C) := by
  have : CompactSpace C := isCompact_iff_compactSpace.mp hK
  let T : Set (Frame X.Ψ r × C) := {p | ∀ τ : X.Ψ, ∀ a c : Fin r, c < a →
    ((mat p.2.1 τ).adjugate * ((1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 *
      mat p.1 τ) a c = 0}
  have hm : ∀ τ : X.Ψ, Continuous fun y : Frame X.Ψ r => mat y τ := fun τ => continuous_apply τ
  have hT : IsClosed T := by
    simp only [T, Set.setOf_forall]
    refine isClosed_iInter fun τ => isClosed_iInter fun a => isClosed_iInter fun c =>
      isClosed_iInter fun _ => isClosed_eq ?_ continuous_const
    exact (((((hm τ).comp (continuous_subtype_val.comp continuous_snd)).matrix_adjugate).matrix_mul
      continuous_const).matrix_mul ((hm τ).comp continuous_fst)).matrix_elem a c
  have hT' : IsClosed (Prod.fst '' T) := isClosedMap_fst_of_compactSpace T hT
  have hU : IsOpen {y : Frame X.Ψ r | ∀ τ, (mat y τ).det ≠ 0} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun τ => isOpen_ne_fun (hm τ).matrix_det continuous_const
  have heq : borSat X C = {y : Frame X.Ψ r | ∀ τ, (mat y τ).det ≠ 0} ∩ Prod.fst '' T := by
    ext y
    constructor
    · intro hy
      have hyd : ∀ τ, (mat y τ).det ≠ 0 := fun τ => (borSat_subset_dom X hC hy τ).1
      obtain ⟨x, hx, b, hb, h⟩ := hy
      refine ⟨hyd, (y, ⟨x, hx⟩), ?_, rfl⟩
      exact (FundSetPf.charB 1 hyd fun τ => (hC hx τ).1).mp
        ⟨b, hb, by rw [FundSetPf.lact_one]; exact h⟩
    · rintro ⟨hyd, ⟨y', x, hx⟩, hp, rfl⟩
      obtain ⟨b, hb, h⟩ := (FundSetPf.charB 1 hyd fun τ => (hC hx τ).1).mpr hp
      rw [FundSetPf.lact_one] at h
      exact ⟨x, hx, b, hb, h⟩
  rw [heq]
  exact hU.measurableSet.inter hT'.measurableSet

theorem sat_eq_preimage {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) {C : Set (Frame X.Ψ r)}
    (hC : C ⊆ X.dom) : sat X x0 C = cpt X x0 ⁻¹' borSat X C := by
  ext z
  exact ⟨fun h => h.2, fun h => ⟨borSat_subset_dom X hC h, h⟩⟩

theorem frameMeas_of_local (hI : MeasInvStatement (E := E))
    (hL : ∀ (r : ℕ) (X : Data E r) (x1 : Frame X.Ψ r), IsOrth X x1 → ∀ b1 ∈ Bor X.Ψ r,
      ∃ U ∈ 𝓝 (rmul x1 b1), ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ G : Frame X.Ψ r → ℝ≥0∞, Measurable G →
        (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, G (rmul x b) = G x) →
        ∫⁻ x in U, G x ≤ K * ∫⁻ z, G (cpt X x1 z) ∂muF X x1) :
    FrameMeasStatement (E := E) := by
  intro r X x0 hx0 C hK hC
  have key : ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ G : Frame X.Ψ r → ℝ≥0∞, Measurable G →
      (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, G (rmul x b) = G x) →
      ∫⁻ x in C, G x ≤ K * ∫⁻ z, G (cpt X x0 z) ∂muF X x0 := by
    refine hK.induction_on (p := fun s => ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ G : Frame X.Ψ r → ℝ≥0∞,
      Measurable G → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, G (rmul x b) = G x) →
      ∫⁻ x in s, G x ≤ K * ∫⁻ z, G (cpt X x0 z) ∂muF X x0) ?_ ?_ ?_ ?_
    · exact ⟨0, ENNReal.zero_lt_top, fun G _ _ => by simp⟩
    · rintro s t hst ⟨K, hK, h⟩
      exact ⟨K, hK, fun G hG hB => (lintegral_mono_set hst).trans (h G hG hB)⟩
    · rintro s t ⟨K, hK, h⟩ ⟨K', hK', h'⟩
      refine ⟨K + K', ENNReal.add_lt_top.mpr ⟨hK, hK'⟩, fun G hG hB => ?_⟩
      rw [add_mul]
      exact (lintegral_union_le _ _ _).trans (add_le_add (h G hG hB) (h' G hG hB))
    · intro x hx
      obtain ⟨x1, hx1, b1, hb1, rfl⟩ := ortho_holds r X x (hC hx)
      obtain ⟨U, hU, K, hK, h⟩ := hL r X x1 hx1 b1 hb1
      refine ⟨U, mem_nhdsWithin_of_mem_nhds hU, K, hK, fun G hG hB => ?_⟩
      rw [hI r X x0 x1 hx0 hx1 G hG hB]
      exact h G hG hB
  obtain ⟨K, hKt, h⟩ := key
  refine ⟨K, hKt, fun G hG hB => ?_⟩
  have hS := measurableSet_borSat X hK hC
  have h1 := h ((borSat X C).indicator G) (hG.indicator hS) (by
    intro x hx b hb
    by_cases hxS : x ∈ borSat X C
    · rw [Set.indicator_of_mem hxS, Set.indicator_of_mem ((rmul_mem_borSat_iff X C hb).mpr hxS),
        hB x hx b hb]
    · rw [Set.indicator_of_notMem hxS,
        Set.indicator_of_notMem fun h => hxS ((rmul_mem_borSat_iff X C hb).mp h)])
  have h2 : ∫⁻ x in C, (borSat X C).indicator G x = ∫⁻ x in C, G x :=
    setLIntegral_congr_fun hK.measurableSet fun x hx =>
      Set.indicator_of_mem (subset_borSat X C hx) G
  have h3 : ∫⁻ z, (borSat X C).indicator G (cpt X x0 z) ∂muF X x0 =
      ∫⁻ z in sat X x0 C, G (cpt X x0 z) ∂muF X x0 := by
    rw [sat_eq_preimage X x0 hC,
      ← lintegral_indicator ((FundSetPf.cont_cpt X x0).measurable hS)]
    rfl
  rw [← h2, ← h3]
  exact h1

end GlobalTheory.FrameMeas
end
