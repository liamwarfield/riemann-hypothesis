module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfS
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsPosLeLatticeHeightAtFrame
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.GramDetInequalitiesClosedForms

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MajLactRmul
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.MajInv

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

section copy
open Matrix
open scoped ComplexConjugate
variable {r : ℕ} (X : Data E r)

omit [NumberField E] [IsCMField E] in
theorem col_map_eq (P : Matrix (Fin r) (Fin r) E) (τ : E →+* ℂ) (k : Fin r) :
    ReciprocityTheory.ChartRestriction.G.FD.col (P.map τ) k = Data.emb τ (P *ᵥ Pi.single k 1) := by
  funext i
  simp [ReciprocityTheory.ChartRestriction.G.FD.col, Data.emb]

theorem hermC_expand (τ : E →+* ℂ) (P : Matrix (Fin r) (Fin r) E) (u w : Fin r → ℂ) :
    hermC τ X.Gm ((P.map τ) *ᵥ u) ((P.map τ) *ᵥ w) =
      ∑ k, ∑ l, u k * conj (w l) * τ (herm X.Gm (P *ᵥ Pi.single k 1) (P *ᵥ Pi.single l 1)) := by
  rw [Data.mulVec_eq_sum_col (P.map τ) u, Data.mulVec_eq_sum_col (P.map τ) w, hermC_sum_left]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hermC_smul_left, hermC_sum_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hermC_smul_right, col_map_eq, col_map_eq, hermC_emb]
  ring

theorem hermC_stab {γ : Matrix (Fin r) (Fin r) E}
    (hγ : ∀ x y, herm X.Gm (γ *ᵥ x) (γ *ᵥ y) = herm X.Gm x y) (τ : E →+* ℂ) (u w : Fin r → ℂ) :
    hermC τ X.Gm ((γ.map τ) *ᵥ u) ((γ.map τ) *ᵥ w) = hermC τ X.Gm u w := by
  have h1 : ((1 : Matrix (Fin r) (Fin r) E).map τ) = 1 := Matrix.map_one τ τ.map_zero τ.map_one
  conv_rhs => rw [← one_mulVec u, ← one_mulVec w, ← h1]
  rw [hermC_expand, hermC_expand]
  simp only [hγ, one_mulVec]

theorem gram_stab {γ : Matrix (Fin r) (Fin r) E}
    (hγ : ∀ x y, herm X.Gm (γ *ᵥ x) (γ *ᵥ y) = herm X.Gm x y) (τ : E →+* ℂ)
    (Y : Matrix (Fin r) (Fin r) ℂ) :
    ReciprocityTheory.ChartRestriction.G.FD.gram τ X.Gm (γ.map τ * Y) = ReciprocityTheory.ChartRestriction.G.FD.gram τ X.Gm Y := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, of_apply]
  have hc : ∀ c, ReciprocityTheory.ChartRestriction.G.FD.col (γ.map τ * Y) c = (γ.map τ) *ᵥ ReciprocityTheory.ChartRestriction.G.FD.col Y c := by
    intro c; funext i; simp [ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.mul_apply, mulVec, dotProduct]
  rw [hc, hc, hermC_stab X hγ]

end copy

theorem exists_colP_rmul_eq_sum {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r)
    (τ : X.Ψ) (a : Fin X.p0) :
    ∃ L : Fin X.p0 → ℂ, X.colP (rmul x b) τ a = ∑ c, L c • X.colP x τ c := by
  classical
  refine ⟨fun c => b τ (Fin.castLE X.p0_le c) (Fin.castLE X.p0_le a), ?_⟩
  funext k
  have e1 : X.colP (rmul x b) τ a k = ∑ j, x τ k j * b τ j (Fin.castLE X.p0_le a) := by
    show (mat x τ * mat b τ : Matrix (Fin r) (Fin r) ℂ) k (Fin.castLE X.p0_le a) = _
    rw [Matrix.mul_apply]; rfl
  rw [e1, Finset.sum_apply]
  symm
  refine Finset.sum_of_injOn (Fin.castLE X.p0_le) ((Fin.castLE_injective _).injOn)
    (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) (fun j _ hj => ?_) (fun c _ => ?_)
  · have hj' : X.p0 ≤ (j : ℕ) := by
      by_contra h
      exact hj ⟨⟨j, not_le.mp h⟩, by simp, by ext; simp⟩
    rw [(hb τ).2 j _ (by
      show ((Fin.castLE X.p0_le a : Fin r) : ℕ) < j
      have := a.isLt
      simp only [Fin.val_castLE]; omega), mul_zero]
  · show b τ _ _ * x τ k _ = _
    rw [mul_comm]

theorem maj_rmul {r : ℕ} (X : Data E r) {x b : Frame X.Ψ r} (hx : x ∈ X.dom) (hb : b ∈ Bor X.Ψ r)
    (τ : X.Ψ) (v : Fin r → ℂ) : X.maj (rmul x b) τ v = X.maj x τ v := by
  have h := MajorantConjugateTransfer.maj_transfer X hx (OrthogonalFrameDomain.rmul_mem_dom X hx hb) τ 1 1 (by simp) (by simp)
    (fun c => ?_) (fun a => ?_) v
  · simpa using h
  · have := exists_colP_rmul_eq_sum X (rmul x b) (ExtFPf.invF_mem X hb) τ c
    rw [ExtFPf.rmul_assoc, ExtFPf.rmul_invF X hb, ExtFPf.rmul_oneF] at this
    simpa using this
  · simpa using exists_colP_rmul_eq_sum X x hb τ a

theorem gram_lact {r : ℕ} (X : Data E r) {γ : GL (Fin r) E} (hγ : IsUStab X.Gm X.Λ γ)
    (x : Frame X.Ψ r) (τ : X.Ψ) :
    gram τ.1 X.Gm (mat (lact γ x) τ) = gram τ.1 X.Gm (mat x τ) :=
  gram_stab X hγ.1 τ.1 (mat x τ)

theorem lact_mem_dom {r : ℕ} (X : Data E r) {γ : GL (Fin r) E} (hγ : IsUStab X.Gm X.Λ γ)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) : lact γ x ∈ X.dom := by
  intro τ
  refine ⟨?_, fun i => ?_⟩
  · have e1 : mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl
    rw [e1, Matrix.det_mul, show ((γ : Matrix (Fin r) (Fin r) E).map τ.1).det =
      τ.1 (γ : Matrix (Fin r) (Fin r) E).det by rw [RingHom.map_det]; rfl]
    refine mul_ne_zero ?_ (hx τ).1
    have hu : IsUnit ((γ : Matrix (Fin r) (Fin r) E).det) :=
      (Matrix.isUnit_iff_isUnit_det _).1 γ.isUnit
    exact (hu.map τ.1).ne_zero
  · have := (hx τ).2 i
    unfold dmin at this ⊢
    rwa [gram_lact X hγ]

theorem maj_lact {r : ℕ} (X : Data E r) {γ : GL (Fin r) E} (hγ : IsUStab X.Gm X.Λ γ)
    (x : Frame X.Ψ r) (τ : X.Ψ) (v : Fin r → ℂ) :
    X.maj (lact γ x) τ (Matrix.mulVec ((γ : Matrix (Fin r) (Fin r) E).map τ.1) v) =
      X.maj x τ v := by
  have hc : ∀ c, col (mat (lact γ x) τ) c =
      ((γ : Matrix (Fin r) (Fin r) E).map τ.1) *ᵥ col (mat x τ) c := by
    intro c; funext i
    show ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ : Matrix (Fin r) (Fin r) ℂ) i c = _
    simp [col, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  unfold Data.maj Data.posPart Data.gramPos
  simp only [hc, gram_lact X hγ, hermC_stab X hγ.1]

end GlobalTheory.MajInv

namespace GlobalTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem maj_lact_rmul :
    (∀ (r : ℕ) (X : Data E r) (γ : GL (Fin r) E), IsUStab X.Gm X.Λ γ → ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, lact γ (rmul x b) ∈ X.dom ∧ ∀ (τ : X.Ψ) (v : Fin r → ℂ), X.maj (lact γ (rmul x b)) τ (Matrix.mulVec ((γ : Matrix (Fin r) (Fin r) E).map τ.1) v) = X.maj x τ v) := by
  intro r X γ hγ x hx b hb
  refine ⟨MajInv.lact_mem_dom X hγ (OrthogonalFrameDomain.rmul_mem_dom X hx hb), fun τ v => ?_⟩
  rw [MajInv.maj_lact X hγ, MajInv.maj_rmul X hx hb]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsIsLUBHeightRpowLowerSemicontinuousOn
section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LatticeHeightContinuousOnFrames
section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LatticeHeightContinuousOnFrames
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.HeightCont

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem height_continuousOn : (∀ (r : ℕ) (X : Data E r) (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → ∀ W, ContinuousOn (fun x => d x W) {x : Frame X.Ψ r | (∀ τ : X.Ψ, (mat x τ).det ≠ 0)}) := by
  intro r X d hd W
  obtain ⟨w, hw, hΛ, hsp⟩ := GlobalTheory.LatBasis.exists_basis_mem r X W
  suffices H : ContinuousOn (fun x => d x (Submodule.span E (Set.range w)))
      {x : Frame X.Ψ r | (∀ τ : X.Ψ, (mat x τ).det ≠ 0)} by rwa [hsp] at H
  refine ContinuousOn.congr ?_ (fun x hx => hd x hx _ w hw hΛ)
  refine ContinuousOn.div_const ?_ _
  refine continuousOn_finsetProd _ fun τ _ x hx => ContinuousAt.continuousWithinAt ?_
  have hm : Continuous (fun x : Frame X.Ψ r => mat x τ) := continuous_apply τ
  have hr : ContinuousAt (Ring.inverse : ℂ → ℂ) (mat x τ).det := by
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ (hx τ)
  have hi : ContinuousAt (fun x : Frame X.Ψ r => (mat x τ)⁻¹) x :=
    ContinuousAt.comp (f := fun x : Frame X.Ψ r => mat x τ) (continuousAt_matrix_inv _ hr)
      hm.continuousAt
  have hg : Continuous (fun A : Matrix (Fin r) (Fin r) ℂ =>
      ((A * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * (A * (Matrix.of fun k a => τ.1 (w a k)))).det.re) :=
    Complex.continuous_re.comp
      (((continuous_id.matrix_mul continuous_const).matrix_conjTranspose.matrix_mul
        (continuous_id.matrix_mul continuous_const)).matrix_det)
  exact ContinuousAt.comp (f := fun x : Frame X.Ψ r => (mat x τ)⁻¹) hg.continuousAt hi

end GlobalTheory.HeightCont
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LatticeHeightContinuousOnFramesStatement
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
theorem _root_.GlobalTheory.T.latticeHeight_continuousOn_frames : (∀ (r : ℕ) (X : Data E r) (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → ∀ W, ContinuousOn (fun x => d x W) {x : Frame X.Ψ r | (∀ τ : X.Ψ, (mat x τ).det ≠ 0)}) := by
  first | exact @GlobalTheory.HeightCont.height_continuousOn | exact GlobalTheory.HeightCont.height_continuousOn | (intros; apply GlobalTheory.HeightCont.height_continuousOn <;> assumption)
end
end

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace GlobalTheory

theorem exists_submodule_finrank_eq_of_le {K : Type} [Field K] {r i : ℕ} (h : i ≤ r) :
    ∃ W : Submodule K (Fin r → K), Module.finrank K W = i := by

  have hli : LinearIndependent K ((Pi.basisFun K (Fin r)) ∘ Fin.castLE h) :=
    (Pi.basisFun K (Fin r)).linearIndependent.comp _ (Fin.castLE_injective h)
  exact ⟨_, (finrank_span_eq_card hli).trans (Fintype.card_fin i)⟩

theorem exists_isLUB_height_rpow_lowerSemicontinuousOn : (∀ (r : ℕ) (X : Data E r) (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → ∀ δ : ℝ, 0 < δ → ∃ α : ℕ → Frame X.Ψ r → ℝ, (∀ i ≤ r, ∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → IsLUB ((fun W => d x W ^ (-δ)) '' {W | Module.finrank E W = i}) (α i x)) ∧ ∀ i ≤ r, LowerSemicontinuousOn (α i) {x : Frame X.Ψ r | (∀ τ : X.Ψ, (mat x τ).det ≠ 0)}) := by
  intro r X d hd δ hδ
  set s := {x : Frame X.Ψ r | ∀ τ : X.Ψ, (mat x τ).det ≠ 0} with hs

  have hbdd : ∀ x ∈ s, ∀ i : ℕ, BddAbove ((fun W => d x W ^ (-δ)) ''
      {W : Submodule E (Fin r → E) | Module.finrank E W = i}) := by
    intro x hx i
    obtain ⟨m, hm, hmW⟩ := GlobalTheory.T.exists_pos_le_latticeHeight_at_frame r X d hd x hx
    refine ⟨m ^ (-δ), ?_⟩
    rintro _ ⟨W, -, rfl⟩
    exact Real.rpow_le_rpow_of_nonpos hm (hmW W) (by linarith)
  refine ⟨fun i x => sSup ((fun W => d x W ^ (-δ)) ''
      {W : Submodule E (Fin r → E) | Module.finrank E W = i}), ?_, ?_⟩
  · intro i hi x hx
    obtain ⟨W, hW⟩ := exists_submodule_finrank_eq_of_le (K := E) hi
    exact isLUB_csSup (Set.Nonempty.image _ (⟨W, hW⟩ : Set.Nonempty {W : Submodule E (Fin r → E) | Module.finrank E W = i})) (hbdd x hx i)
  ·
    intro i hi x hx y hy
    obtain ⟨W, hW⟩ := exists_submodule_finrank_eq_of_le (K := E) hi
    obtain ⟨_, ⟨V, hV, rfl⟩, hyV⟩ := exists_lt_of_lt_csSup (Set.Nonempty.image _ (⟨W, hW⟩ : Set.Nonempty {W : Submodule E (Fin r → E) | Module.finrank E W = i})) hy
    have hpos : ∀ x' ∈ s, 0 < d x' V := fun x' hx' => by
      obtain ⟨m, hm, hmW⟩ := GlobalTheory.T.exists_pos_le_latticeHeight_at_frame r X d hd x' hx'
      exact hm.trans_le (hmW V)
    have hcont : ContinuousOn (fun x' => d x' V ^ (-δ)) s :=
      (GlobalTheory.T.latticeHeight_continuousOn_frames r X d hd V).rpow_const fun x' hx' => Or.inl (hpos x' hx').ne'
    have hev : ∀ᶠ x' in 𝓝[s] x, y < d x' V ^ (-δ) := (hcont x hx).eventually (lt_mem_nhds hyV)
    filter_upwards [hev, self_mem_nhdsWithin] with x' h1 h2
    exact h1.trans_le (le_csSup (hbdd x' h2 i) ⟨V, hV, rfl⟩)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.HeightRpowNegDistortionContraction
section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LatticeHeightUpdateFrameComponent
section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LatticeHeightUpdateFrameComponent
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.HeightStep

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem _root_.GlobalTheory.HeightStep.height_update : (∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (d : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r, (∀ τ : X.Ψ, (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → ∀ x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r, (∀ τ : X.Ψ, (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ).det ≠ 0) → ∀ (τ0 : X.Ψ) (W : Submodule E (Fin r → E)), ∃ M : Matrix (Fin r) (Fin (Module.finrank E W)) ℂ, 0 < (((M)ᴴ * (M)).det.re) ∧ ∀ a : Matrix (Fin r) (Fin r) ℂ, a.det ≠ 0 → d (@Function.update X.Ψ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _) x τ0 (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ0 * a⁻¹ : Matrix (Fin r) (Fin r) ℂ)) W = d x W * ((((a * M)ᴴ * (a * M)).det.re) / (((M)ᴴ * (M)).det.re))) := by
  classical
  intro r X d hd x hx τ0 W
  obtain ⟨w, hli, hmem, hspan⟩ := _root_.GlobalTheory.LatBasis.exists_basis_mem r X W
  obtain ⟨e, -, hdet⟩ := _root_.GlobalTheory.exists_maximal_minor_ne_zero_of_linearIndependent E r _ w hli
  set N : X.Ψ → Matrix (Fin r) (Fin (Module.finrank E W)) ℂ :=
    fun τ => Matrix.of fun k a => τ.1 (w a k) with hN
  set M := (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ0)⁻¹ * N τ0 with hM
  have hA : IsUnit (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ0).det := isUnit_iff_ne_zero.mpr (hx τ0)
  have hminor : (Matrix.of fun k a => N τ0 (e k) a).det ≠ 0 := by
    have hmap : (Matrix.of fun k a => N τ0 (e k) a) =
        τ0.1.mapMatrix (Matrix.of fun k a => w a (e k)) := by
      ext k a
      rfl
    rw [hmap, ← RingHom.map_det]
    exact (map_ne_zero τ0.1).mpr hdet
  have hinj : Function.Injective M.mulVec := by
    intro u v huv
    rw [← sub_eq_zero]
    have h0 : M *ᵥ (u - v) = 0 := by rw [Matrix.mulVec_sub, huv, sub_self]
    have h1 : N τ0 *ᵥ (u - v) = 0 := by
      have : N τ0 = _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ0 * M := by
        rw [hM, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hA, Matrix.one_mul]
      rw [this, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]
    apply Matrix.eq_zero_of_mulVec_eq_zero hminor
    funext k
    have := congrFun h1 (e k)
    simpa [Matrix.mulVec, dotProduct] using this
  have hpos : 0 < ((Mᴴ * M).det.re) := by
    have := (Matrix.PosDef.conjTranspose_mul_self M hinj).det_pos
    exact (Complex.pos_iff.mp this).1
  refine ⟨M, hpos, fun a ha => ?_⟩
  set x' : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r := @Function.update X.Ψ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _)
    x τ0 (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ0 * a⁻¹ : Matrix (Fin r) (Fin r) ℂ) with hx'
  have haU : IsUnit a.det := isUnit_iff_ne_zero.mpr ha
  have hupd : ∀ τ, _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x' τ = if τ = τ0 then _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ0 * a⁻¹ else _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ := by
    intro τ
    by_cases h : τ = τ0
    · subst h
      rw [if_pos rfl, hx']
      unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.mat
      exact @Function.update_self _ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _) _ _ _
    · rw [if_neg h, hx']
      unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.mat
      exact @Function.update_of_ne _ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _) _ _ h _ _
  have hx'det : ∀ τ : X.Ψ, (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x' τ).det ≠ 0 := by
    intro τ
    rw [hupd]
    split_ifs
    · rw [Matrix.det_mul]
      exact mul_ne_zero (hx τ0) (Matrix.isUnit_nonsing_inv_det a haU).ne_zero
    · exact hx τ
  set F : X.Ψ → ℝ := fun τ => (((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹ * N τ)ᴴ * ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹ * N τ)).det.re with hF
  have h1 := hd x' hx'det _ w hli hmem
  have h2 := hd x hx _ w hli hmem
  rw [hspan] at h1 h2
  rw [h1, h2]
  have hprod' : ∏ τ : X.Ψ, ((((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x' τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ *
      ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x' τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re) =
      (((a * M)ᴴ * (a * M)).det.re) * ∏ τ ∈ Finset.univ \ {τ0}, F τ := by
    rw [← Finset.prod_update_of_mem (Finset.mem_univ τ0)]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [Function.update_apply, hupd]
    split_ifs with h
    · subst h
      rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv a haU, Matrix.mul_assoc]
    · rfl
  have hprod : ∏ τ : X.Ψ, ((((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ *
      ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re) =
      ((Mᴴ * M).det.re) * ∏ τ ∈ Finset.univ \ {τ0}, F τ := by
    rw [← Finset.prod_update_of_mem (Finset.mem_univ τ0), Function.update_eq_self]
  rw [hprod', hprod]
  have hne : (Mᴴ * M).det.re ≠ 0 := hpos.ne'
  field_simp

end GlobalTheory.HeightStep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LatticeHeightUpdateFrameComponentStatement
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
theorem _root_.GlobalTheory.T.latticeHeight_update_frameComponent : (∀ (r : ℕ) (X : Data E r) (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → ∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (τ0 : X.Ψ) (W : Submodule E (Fin r → E)), ∃ M : Matrix (Fin r) (Fin (Module.finrank E W)) ℂ, 0 < (((M)ᴴ * (M)).det.re) ∧ ∀ a : Matrix (Fin r) (Fin r) ℂ, a.det ≠ 0 → d (@Function.update X.Ψ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _) x τ0 (mat x τ0 * a⁻¹ : Matrix (Fin r) (Fin r) ℂ)) W = d x W * ((((a * M)ᴴ * (a * M)).det.re) / (((M)ᴴ * (M)).det.re))) := by
  first | exact @GlobalTheory.HeightStep.height_update | exact GlobalTheory.HeightStep.height_update | (intros; apply GlobalTheory.HeightStep.height_update <;> assumption)
end
end

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace GlobalTheory

theorem rpow_neg_le_of_le_mul {p q ω δ : ℝ} (hp : 0 < p) (hq : 0 < q) (hω : 0 < ω) (hδ : 0 ≤ δ)
    (h : q ≤ ω * p) : p ^ (-δ) ≤ ω ^ δ * q ^ (-δ) := by
  have h1 : (ω * p) ^ (-δ) ≤ q ^ (-δ) :=
    Real.rpow_le_rpow_of_nonpos hq h (by linarith)
  rw [Real.mul_rpow hω.le hp.le] at h1
  have h2 : ω ^ δ * ω ^ (-δ) = 1 := by
    rw [← Real.rpow_add hω]; simp
  have h3 : 0 < ω ^ δ := Real.rpow_pos_of_pos hω δ
  calc p ^ (-δ) = ω ^ δ * (ω ^ (-δ) * p ^ (-δ)) := by rw [← mul_assoc, h2, one_mul]
    _ ≤ ω ^ δ * q ^ (-δ) := mul_le_mul_of_nonneg_left h1 h3.le

theorem height_rpow_neg_distortion_contraction : (∀ (r : ℕ) (X : Data E r) (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → ∀ (τ0 : X.Ψ) (S : Finset (Matrix (Fin r) (Fin r) ℂ)), (∀ a ∈ S, a.IsHermitian ∧ a.det ≠ 0 ∧ a⁻¹ ∈ S) → (∀ W : Submodule ℂ (Fin r → ℂ), (∀ a ∈ S, ∀ v ∈ W, (a * a).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) → ∃ δ c Ω : ℝ, 0 < δ ∧ 0 ≤ c ∧ c < 1 ∧ 1 ≤ Ω ∧ ∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ W, (∀ a ∈ S, d (@Function.update X.Ψ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _) x τ0 (mat x τ0 * a⁻¹ : Matrix (Fin r) (Fin r) ℂ)) W ^ (-δ) ≤ Ω * d x W ^ (-δ) ∧ d x W ^ (-δ) ≤ Ω * d (@Function.update X.Ψ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _) x τ0 (mat x τ0 * a⁻¹ : Matrix (Fin r) (Fin r) ℂ)) W ^ (-δ)) ∧ (W ≠ ⊥ → W ≠ ⊤ → ∑ a ∈ S, d (@Function.update X.Ψ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _) x τ0 (mat x τ0 * a⁻¹ : Matrix (Fin r) (Fin r) ℂ)) W ^ (-δ) ≤ S.card * (c * d x W ^ (-δ)))) := by
  intro r X d hd τ0 S hS hirr
  obtain ⟨δ, c, ω, hδ, hc0, hc1, hω, H⟩ := GlobalTheory.T.gramDet_inequalities_closed_forms.2.2.1 r S hS hirr
  refine ⟨δ, c, ω ^ δ, hδ, hc0, hc1, Real.one_le_rpow hω hδ.le, ?_⟩
  intro x hx W
  obtain ⟨m, hm, hmd⟩ := GlobalTheory.T.exists_pos_le_latticeHeight_at_frame r X d hd x hx
  have hD : 0 < d x W := lt_of_lt_of_le hm (hmd W)
  obtain ⟨M, hM, hstep⟩ := GlobalTheory.T.latticeHeight_update_frameComponent r X d hd x hx τ0 W
  obtain ⟨H1, H2⟩ := H _ M hM
  have hω0 : 0 < ω := by linarith
  have hpos : ∀ a ∈ S, 0 < ((a * M)ᴴ * (a * M)).det.re := by
    intro a ha
    have := lt_of_lt_of_le hM (H1 a ha).2
    exact (mul_pos_iff_of_pos_left hω0).mp this
  refine ⟨fun a ha => ?_, fun hb ht => ?_⟩
  · rw [hstep a (hS a ha).2.1]
    obtain ⟨h1, h2⟩ := H1 a ha
    have hp := hpos a ha
    generalize ((a * M)ᴴ * (a * M)).det.re = A at h1 h2 hp
    generalize (Mᴴ * M).det.re = B at h1 h2 hM
    have hq : 0 < d x W * (A / B) := mul_pos hD (div_pos hp hM)
    refine ⟨rpow_neg_le_of_le_mul hq hD hω0 hδ.le ?_, rpow_neg_le_of_le_mul hD hq hω0 hδ.le ?_⟩
    · have : 1 ≤ ω * (A / B) := by
        rw [← mul_div_assoc, le_div_iff₀ hM]; linarith
      nlinarith
    · have : A / B ≤ ω := by rw [div_le_iff₀ hM]; exact h1
      nlinarith
  · have h0 : 0 < Module.finrank E W := by
      rw [Nat.pos_iff_ne_zero]
      intro h
      exact hb (Submodule.finrank_eq_zero.mp h)
    have hr : Module.finrank E W < r := by
      have := Submodule.finrank_lt ht
      simpa using this
    have H3 := H2 h0 hr
    have hDp : 0 < d x W ^ (-δ) := Real.rpow_pos_of_pos hD _
    calc _ = ∑ a ∈ S, d x W ^ (-δ) *
          (((a * M)ᴴ * (a * M)).det.re / (Mᴴ * M).det.re) ^ (-δ) := by
          refine Finset.sum_congr rfl fun a ha => ?_
          rw [hstep a (hS a ha).2.1, Real.mul_rpow hD.le (div_pos (hpos a ha) hM).le]
      _ = d x W ^ (-δ) * ∑ a ∈ S,
          (((a * M)ᴴ * (a * M)).det.re / (Mᴴ * M).det.re) ^ (-δ) := by rw [Finset.mul_sum]
      _ ≤ d x W ^ (-δ) * (S.card * c) := mul_le_mul_of_nonneg_left H3 hDp.le
      _ = _ := by ring

end GlobalTheory
end
