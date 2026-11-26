module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfE
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KaUnfoldPfA
public import Lemmata.GeneralBFactVariant.Imports
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.VanishAtSStatementPf

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OmFConnPf
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OFC

open NumberField Complex Matrix Topology ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

def isW (i : Fin (nd X)) : Prop :=
  X.p0 ≤ (((Fintype.equivFin (Ent X)).symm i).2.1.1 : ℕ) ∧ (((Fintype.equivFin (Ent X)).symm i).2.1.2 : ℕ) < X.p0

instance (i : Fin (nd X)) : Decidable (isW X i) := by unfold isW; infer_instance

def S1 (t : ℝ) (z : V (nd X)) : V (nd X) := WithLp.toLp 2 fun i => if isW X i then (t : ℂ) * z i else z i

def S2 (t : ℝ) (z : V (nd X)) : V (nd X) := WithLp.toLp 2 fun i => if isW X i then 0 else (t : ℂ) * z i

theorem scaledWm_linear (t : ℝ) (z : V (nd X)) (τ : X.Ψ) : ExF.Wm X (S1 X t z) τ = (t : ℂ) • ExF.Wm X z τ := by
  ext m c
  have hc := c.isLt
  have hlt : Fin.castLE X.p0_le c < ExF.qI X m := by
    rw [Fin.lt_def]
    simp only [Fin.coe_castLE, ExF.qI]
    omega
  simp only [ExF.Wm, ExF.n1, ExF.nM, mat, nmat, Matrix.submatrix_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, WithLp.ofLp_toLp, PiLp.toLp_apply, S1, dif_pos hlt]
  rw [if_pos]
  simp only [isW, Equiv.symm_apply_apply, ExF.qI, Fin.coe_castLE]
  omega

theorem unipotentFrame_scaling_invariant (t : ℝ) (z : V (nd X)) (τ : X.Ψ) : ExF.n1 X (S1 X t z) τ = ExF.n1 X z τ := by
  ext a b
  have ha := a.isLt
  simp only [ExF.Wm, ExF.n1, ExF.nM, mat, nmat, Matrix.submatrix_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, WithLp.ofLp_toLp, PiLp.toLp_apply, S1]
  split_ifs with h1 h2 <;>
    first
    | rfl
    | (exfalso
       simp only [isW, Equiv.symm_apply_apply, Fin.coe_castLE] at *
       omega)

theorem retractedWm_eq_zero (t : ℝ) (z : V (nd X)) (τ : X.Ψ) : ExF.Wm X (S2 X t z) τ = 0 := by
  ext m c
  have hc := c.isLt
  have hlt : Fin.castLE X.p0_le c < ExF.qI X m := by
    rw [Fin.lt_def]
    simp only [Fin.coe_castLE, ExF.qI]
    omega
  simp only [ExF.Wm, ExF.n1, ExF.nM, mat, nmat, Matrix.submatrix_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, WithLp.ofLp_toLp, PiLp.toLp_apply, S2, dif_pos hlt, Matrix.zero_apply]
  rw [if_pos]
  simp only [isW, Equiv.symm_apply_apply, ExF.qI, Fin.coe_castLE]
  omega

theorem scaledZt_linear (t : ℝ) (z : V (nd X)) (τ : X.Ψ) : ExF.Zt X (S1 X t z) τ = (t : ℂ) • ExF.Zt X z τ := by
  simp only [ExF.Zt, scaledWm_linear, unipotentFrame_scaling_invariant, Matrix.smul_mul, Matrix.transpose_smul]

theorem retractedZt_eq_zero (t : ℝ) (z : V (nd X)) (τ : X.Ψ) : ExF.Zt X (S2 X t z) τ = 0 := by
  simp only [ExF.Zt, retractedWm_eq_zero, Matrix.zero_mul, Matrix.transpose_zero]

theorem S1_mem_OmF (x0 : Frame X.Ψ r) (ho : IsOrth X x0) {z : V (nd X)} (hz : z ∈ OmF X x0) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : S1 X t z ∈ OmF X x0 := by
  rw [ExF.mem_OmF_iff X x0 ho] at hz ⊢
  intro τ
  have hA := hz τ
  have heq : ExF.Am X (S1 X t z) τ =
      ((1 - t ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin X.p0) (Fin X.p0) ℂ) + ((t ^ 2 : ℝ) : ℂ) • ExF.Am X z τ := by
    simp only [ExF.Am, scaledZt_linear, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Complex.star_def, Complex.conj_ofReal]
    have e1 : ((1 - t ^ 2 : ℝ) : ℂ) = 1 - (t : ℂ) * t := by
      push_cast
      ring
    have e2 : ((t ^ 2 : ℝ) : ℂ) = (t : ℂ) * t := by
      push_cast
      ring
    rw [e1, e2, sub_smul, one_smul, smul_sub]
    abel
  rw [heq]
  rcases ht0.lt_or_eq with htpos | rfl
  · have h2 : (0 : ℂ) < ((t ^ 2 : ℝ) : ℂ) := by
      exact_mod_cast pow_pos htpos 2
    have h1 : (0 : ℂ) ≤ ((1 - t ^ 2 : ℝ) : ℂ) := by
      have : t ^ 2 ≤ 1 := by nlinarith
      exact_mod_cast sub_nonneg.2 this
    exact (hA.smul h2).posSemidef_add ((Matrix.PosSemidef.one).smul h1)
  · simpa using Matrix.PosDef.one

theorem radialRetraction_mem_chart (x0 : Frame X.Ψ r) (ho : IsOrth X x0) (z : V (nd X)) (t : ℝ) : S2 X t z ∈ OmF X x0 := by
  rw [ExF.mem_OmF_iff X x0 ho]
  intro τ
  simp only [ExF.Am, retractedZt_eq_zero, Matrix.zero_mul, sub_zero]
  exact Matrix.PosDef.one

theorem continuous_linearScaling (z : V (nd X)) : Continuous fun t : ℝ => S1 X t z := by
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  by_cases h : isW X i
  · simp only [h, if_true]
    fun_prop
  · simp only [h, if_false]
    fun_prop

theorem continuous_radialRetraction (z : V (nd X)) : Continuous fun t : ℝ => S2 X t z := by
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  by_cases h : isW X i
  · simp only [h, if_true]
    fun_prop
  · simp only [h, if_false]
    fun_prop

theorem linearScaling_zero_eq_retraction (z : V (nd X)) : S1 X 0 z = S2 X 1 z := by
  ext i
  simp only [S1, S2, WithLp.ofLp_toLp, PiLp.toLp_apply]
  split_ifs <;> simp

theorem radialRetraction_at_zero (z : V (nd X)) : S2 X 0 z = 0 := by
  ext i
  simp only [S2, WithLp.ofLp_toLp, PiLp.toLp_apply]
  split_ifs <;> simp

theorem linearScaling_at_one (z : V (nd X)) : S1 X 1 z = z := by
  ext i
  simp only [S1, WithLp.ofLp_toLp, PiLp.toLp_apply]
  split_ifs <;> simp

end

theorem omFConn_of_cm {E : Type} [Field E] [NumberField E] [IsCMField E] : OmFConnStatement (E := E) := by
  intro r X x0 ho
  refine isPreconnected_of_forall 0 fun y hy => ?_
  refine ⟨(fun t => S2 X t y) '' Set.Icc 0 1 ∪ (fun t => S1 X t y) '' Set.Icc 0 1, ?_, ?_, ?_, ?_⟩
  · rintro w (⟨t, -, rfl⟩ | ⟨t, ⟨ht0, ht1⟩, rfl⟩)
    · exact radialRetraction_mem_chart X x0 ho y t
    · exact S1_mem_OmF X x0 ho hy ht0 ht1
  · exact Or.inl ⟨0, ⟨le_rfl, zero_le_one⟩, radialRetraction_at_zero X y⟩
  · exact Or.inr ⟨1, ⟨zero_le_one, le_rfl⟩, linearScaling_at_one X y⟩
  · refine IsPreconnected.union (S2 X 1 y) ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩
      ⟨0, ⟨le_rfl, zero_le_one⟩, linearScaling_zero_eq_retraction X y⟩ ?_ ?_
    · exact isPreconnected_Icc.image _ (continuous_radialRetraction X y).continuousOn
    · exact isPreconnected_Icc.image _ (continuous_linearScaling X y).continuousOn

end ReciprocityTheory.ChartRestriction.G.AR.Up.OFC

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField

theorem OmFConnStatement_holds {E : Type} [Field E] [NumberField E] [IsCMField E] :
    OmFConnStatement (E := E) :=
  OFC.omFConn_of_cm

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KaUnfoldPfB
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.KU

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Matrix
open scoped ENNReal ComplexOrder

noncomputable section

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def untl (X : Data E r) (M : Matrix (Fin (r - X.p0) ⊕ Fin X.p0) (Fin (r - X.p0) ⊕ Fin X.p0) ℂ) :
    Matrix (Fin r) (Fin r) ℂ := M.submatrix (eT X).symm (eT X).symm

theorem untl_tl (X : Data E r) (M : Matrix (Fin r) (Fin r) ℂ) : untl X (tl X M) = M := by
  ext a b; simp [untl, tl]

theorem tl_one (X : Data E r) : tl X (1 : Matrix (Fin r) (Fin r) ℂ) = 1 := by
  rw [tl, Matrix.submatrix_one_equiv]

theorem gm_mul (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) (γ γ' : GL (Fin r) E) (τ : X.Ψ) :
    gm X x0 (γ * γ') τ = gm X x0 γ τ * gm X x0 γ' τ := by
  have hu : IsUnit (mat x0 τ).det := isUnit_iff_ne_zero.mpr (ExF.det_ne_of_orth X ho τ)
  rw [gm, gm, gm, ← tl_mul]
  congr 1
  rw [Units.val_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (mat x0 τ) (mat x0 τ)⁻¹, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]

theorem gm_one (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) (τ : X.Ψ) :
    gm X x0 1 τ = 1 := by
  have hu : IsUnit (mat x0 τ).det := isUnit_iff_ne_zero.mpr (ExF.det_ne_of_orth X ho τ)
  rw [gm, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one,
    Matrix.nonsing_inv_mul _ hu, tl_one]

theorem mat_lact_eq (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) (γ : GL (Fin r) E) (τ : X.Ψ) :
    mat (lact γ x0) τ = mat x0 τ * untl X (gm X x0 γ τ) := by
  have hu : IsUnit (mat x0 τ).det := isUnit_iff_ne_zero.mpr (ExF.det_ne_of_orth X ho τ)
  rw [gm, untl_tl, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]; rfl

theorem orth_dom (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) : x0 ∈ X.dom := by
  refine ExF.mem_dom_of_gramPos X fun τ => ⟨ExF.det_ne_of_orth X ho τ, ?_⟩
  have e : X.gramPos x0 τ = 1 := by
    ext a b
    simp only [Data.gramPos, ho τ, Matrix.submatrix_apply, Matrix.diagonal_apply, Matrix.one_apply,
      Fin.castLE_inj]
    split_ifs <;> simp [sgn]
  rw [e]; exact Matrix.PosDef.one

def rho (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) :
    GL (Fin r) E →* (Fin (Fintype.card X.Ψ) → GL (Fin (r - X.p0) ⊕ Fin X.p0) ℂ) where
  toFun γ k := ⟨gm X x0 γ ((Fintype.equivFin X.Ψ).symm k), gm X x0 γ⁻¹ ((Fintype.equivFin X.Ψ).symm k),
    by rw [← gm_mul X ho, mul_inv_cancel, gm_one X ho],
    by rw [← gm_mul X ho, inv_mul_cancel, gm_one X ho]⟩
  map_one' := by funext k; exact Units.ext (gm_one X ho _)
  map_mul' γ γ' := by funext k; exact Units.ext (gm_mul X ho γ γ' _)

theorem rho_apply (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) (γ : GL (Fin r) E)
    (k : Fin (Fintype.card X.Ψ)) :
    ((rho X ho γ k : GL (Fin (r - X.p0) ⊕ Fin X.p0) ℂ) : Matrix _ _ ℂ) =
      gm X x0 γ ((Fintype.equivFin X.Ψ).symm k) := rfl

theorem lact_eq_of_rho (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) {γ γ' : GL (Fin r) E}
    (h : rho X ho γ = rho X ho γ') : lact γ x0 = lact γ' x0 := by
  funext τ
  have hk := congrArg (fun g : Fin (Fintype.card X.Ψ) → GL (Fin (r - X.p0) ⊕ Fin X.p0) ℂ =>
    (g (Fintype.equivFin X.Ψ τ)).val) h
  simp only [rho_apply, Equiv.symm_apply_apply] at hk
  have e1 := mat_lact_eq X ho γ τ
  have e2 := mat_lact_eq X ho γ' τ
  rw [hk, ← e2] at e1
  exact e1

theorem rho_inj (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) :
    Function.Injective ((rho X ho).comp X.Γ.subtype) := by
  intro γ γ' h
  have hl : lact γ.1 x0 = lact γ'.1 x0 := lact_eq_of_rho X ho h
  have hδ : (γ'.1)⁻¹ * γ.1 ∈ X.Γ := X.Γ.mul_mem (X.Γ.inv_mem γ'.2) γ.2
  have h1 : lact ((γ'.1)⁻¹ * γ.1) x0 = rmul x0 (ExtFPf.oneF X) := by
    rw [ExtFPf.rmul_oneF, ← lact_lact, hl, lact_lact, inv_mul_cancel, lact_one]
  have := X.Γ_free _ hδ x0 (orth_dom X ho) _ (ExtFPf.oneF_mem X) h1
  exact Subtype.ext (inv_mul_eq_one.mp this).symm

end

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def Phi (X : Data E r) (x0 : Frame X.Ψ r)
    (g : Fin (Fintype.card X.Ψ) → GL (Fin (r - X.p0) ⊕ Fin X.p0) ℂ) : Frame X.Ψ r :=
  fun τ => (mat x0 τ * untl X (g (Fintype.equivFin X.Ψ τ)).val : Matrix (Fin r) (Fin r) ℂ)

theorem Phi_rho (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) (γ : GL (Fin r) E) :
    Phi X x0 (rho X ho γ) = lact γ x0 := by
  funext τ
  have := mat_lact_eq X ho γ τ
  rw [show mat (lact γ x0) τ = lact γ x0 τ from rfl] at this
  rw [this, Phi, rho_apply, Equiv.symm_apply_apply]

theorem Phi_cont (X : Data E r) (x0 : Frame X.Ψ r) : Continuous (Phi X x0) := by
  refine continuous_pi fun τ => ?_
  have hc : Continuous fun g : Fin (Fintype.card X.Ψ) → GL (Fin (r - X.p0) ⊕ Fin X.p0) ℂ =>
      ((g (Fintype.equivFin X.Ψ τ) : GL (Fin (r - X.p0) ⊕ Fin X.p0) ℂ) :
        Matrix (Fin (r - X.p0) ⊕ Fin X.p0) (Fin (r - X.p0) ⊕ Fin X.p0) ℂ) :=
    Units.continuous_val.comp (continuous_apply _)
  exact Continuous.matrix_mul continuous_const (hc.matrix_submatrix _ _)

theorem disc (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) (hPD : PropDisc X) :
    DiscreteTopology ((rho X ho).comp X.Γ.subtype).range := by
  apply discreteTopology_of_isOpen_singleton_one
  obtain ⟨U, hU, U', hU', hfin⟩ := hPD x0 (orth_dom X ho) x0 (orth_dom X ho)
  have h1 : Phi X x0 ⁻¹' U' ∈ 𝓝 (1 : Fin (Fintype.card X.Ψ) → GL (Fin (r - X.p0) ⊕ Fin X.p0) ℂ) := by
    refine (Phi_cont X x0).continuousAt.preimage_mem_nhds ?_
    rw [← map_one (rho X ho), Phi_rho, lact_one]; exact hU'
  have hF : IsClosed ((rho X ho '' {γ : GL (Fin r) E | γ ∈ X.Γ ∧ ∃ u ∈ U, ∃ u' ∈ U', ∃ b ∈ Bor X.Ψ r,
      lact γ u = rmul u' b}) \ {1}) := ((hfin.image _).sdiff).isClosed
  rw [isOpen_induced_iff]
  refine ⟨interior (Phi X x0 ⁻¹' U') \ _, isOpen_interior.sdiff hF, ?_⟩
  ext g
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_sdiff]
  constructor
  · rintro ⟨hg1, hg2⟩
    obtain ⟨γ, hγ⟩ := g.2
    apply Subtype.ext
    by_contra hne
    apply hg2
    have hU'γ : lact γ.1 x0 ∈ U' := by
      have := interior_subset hg1
      rw [Set.mem_preimage, ← hγ] at this
      rwa [MonoidHom.comp_apply, Subgroup.subtype_apply, Phi_rho] at this
    exact ⟨⟨γ.1, ⟨γ.2, x0, mem_of_mem_nhds hU, lact γ.1 x0, hU'γ, ExtFPf.oneF X, ExtFPf.oneF_mem X,
      (ExtFPf.rmul_oneF X _).symm⟩, hγ⟩, hne⟩
  · rintro rfl
    exact ⟨mem_interior_iff_mem_nhds.2 h1, fun h => h.2 rfl⟩

theorem upq_range (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) :
    ∀ g ∈ ((rho X ho).comp X.Γ.subtype).range, ∀ k,
      IsUpq ((g k : GL (Fin (r - X.p0) ⊕ Fin X.p0) ℂ) : Matrix (Fin (r - X.p0) ⊕ Fin X.p0) (Fin (r - X.p0) ⊕ Fin X.p0) ℂ) := by
  rintro g ⟨γ, rfl⟩ k
  rw [MonoidHom.comp_apply, Subgroup.subtype_apply, rho_apply]
  exact gm_upq X ho γ.2 _

theorem kap_lact_cpt (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) (bb : ℝ) (γ : GL (Fin r) E)
    (z : V (nd X)) :
    kap X x0 bb (lact γ (cpt X x0 z)) =
      ∏ k, dpow (mob (gm X x0 γ ((Fintype.equivFin X.Ψ).symm k))
        (ExF.Zt X z ((Fintype.equivFin X.Ψ).symm k))ᵀ) bb := by
  rw [kap, ← Equiv.prod_comp (Fintype.equivFin X.Ψ).symm]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Mx_lact X ho, Mx_cpt X ho, Yb_mul _ _ (by rw [tl_nM₂₂, ExF.det_unipotentFrame_eq_one]; exact one_ne_zero), Yb_tl_nM]

def vpt (X : Data E r) (z : V (nd X)) : V (nD (Fintype.card X.Ψ) (r - X.p0) X.p0) :=
  WithLp.toLp 2 fun i =>
    (ExF.Zt X z ((Fintype.equivFin X.Ψ).symm (finProdFinEquiv.symm i).1))ᵀ
      (finProdFinEquiv.symm (finProdFinEquiv.symm i).2).1 (finProdFinEquiv.symm (finProdFinEquiv.symm i).2).2

theorem Zof_vpt (X : Data E r) (z : V (nd X)) (k : Fin (Fintype.card X.Ψ)) :
    Zof (vpt X z) k = (ExF.Zt X z ((Fintype.equivFin X.Ψ).symm k))ᵀ := by
  ext a b; simp [Zof, vpt, -finProdFinEquiv_symm_apply, Equiv.symm_apply_apply]

theorem sum_bound (hSB : SumBoundStatement) (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0)
    (hPD : PropDisc X) (bb : ℝ) (hbb : 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ z ∈ OmF X x0,
      ∑' γ : X.Γ, ENNReal.ofReal (kap X x0 bb (lact γ.1 (cpt X x0 z))) ≤ C := by
  have hs : 2 * (Fintype.card X.Ψ : ℝ) * (((r - X.p0 + X.p0 : ℕ)) : ℝ) ^ 2 < bb := by
    have e : r - X.p0 + X.p0 = r := by have := X.p0_le; omega
    rw [e, Fintype.card_coe]
    have : 0 ≤ (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 := by positivity
    nlinarith
  have hdisc := disc X ho hPD
  obtain ⟨C, hC, hCb⟩ := hSB (Fintype.card X.Ψ) (r - X.p0) X.p0 bb hs _ hdisc (upq_range X ho)
  refine ⟨C, hC, fun z hz => ?_⟩
  have hv : vpt X z ∈ Dset (Fintype.card X.Ψ) (r - X.p0) X.p0 := fun k => by
    rw [Zof_vpt]; exact posDef_Zt X ho hz _
  refine le_trans (le_of_eq ?_) (hCb _ hv)
  rw [← (MonoidHom.ofInjective (rho_inj X ho)).toEquiv.tsum_eq]
  refine tsum_congr fun γ => ?_
  congr 1
  rw [kap_lact_cpt X ho]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Zof_vpt]
  rfl

end

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem cont_cpt (X : Data E r) (x0 : Frame X.Ψ r) : Continuous (cpt X x0) := by
  refine continuous_pi fun τ => continuous_pi fun a => continuous_pi fun b => ?_
  simp only [cpt, rmul, mat, Matrix.mul_apply, Matrix.of_apply, nmat]
  refine continuous_finsetSum _ fun k _ => continuous_const.mul ?_
  split_ifs <;> fun_prop

theorem lu_unique {n : ℕ} {N N' B B' : Matrix (Fin n) (Fin n) ℂ}
    (hN : N.BlockTriangular OrderDual.toDual) (hN' : N'.BlockTriangular OrderDual.toDual)
    (hd : ∀ i, N i i = 1) (hd' : ∀ i, N' i i = 1)
    (hB : B.BlockTriangular id) (hB' : B'.BlockTriangular id) (hBd : B.det ≠ 0)
    (h : N * B = N' * B') : N = N' := by
  exact Bl.general_b_fact_variant.goal1 hN hN' hd hd' hB hB' hBd h

theorem nM_low (X : Data E r) (z : V (nd X)) (τ : X.Ψ) :
    (ExF.nM X z τ).BlockTriangular OrderDual.toDual := fun _ _ hca => ExF.nM_upper X z τ hca

theorem nmat_inj (X : Data E r) {z z' : V (nd X)} (h : ∀ τ, ExF.nM X z τ = ExF.nM X z' τ) : z = z' := by
  ext i
  obtain ⟨⟨τ, ⟨⟨a, b⟩, hab⟩⟩, rfl⟩ := (Fintype.equivFin (Ent X)).surjective i
  have := congrFun (congrFun (h τ) a) b
  simpa [ExF.nM, mat, nmat, hab] using this

theorem cpt_inj (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) {z z' : V (nd X)} {b b' : Frame X.Ψ r}
    (hb : b ∈ Bor X.Ψ r) (hb' : b' ∈ Bor X.Ψ r) (h : rmul (cpt X x0 z) b = rmul (cpt X x0 z') b') :
    z = z' ∧ b = b' := by
  have hN : ∀ τ, ExF.nM X z τ * mat b τ = ExF.nM X z' τ * mat b' τ := by
    intro τ
    have hu : IsUnit (mat x0 τ).det := isUnit_iff_ne_zero.mpr (ExF.det_ne_of_orth X ho τ)
    have := congrArg (fun y : Frame X.Ψ r => (mat x0 τ)⁻¹ * mat y τ) h
    rwa [show mat (rmul (cpt X x0 z) b) τ = mat x0 τ * (ExF.nM X z τ * mat b τ) by
        show (mat x0 τ * ExF.nM X z τ) * mat b τ = _; exact Matrix.mul_assoc _ _ _,
      show mat (rmul (cpt X x0 z') b') τ = mat x0 τ * (ExF.nM X z' τ * mat b' τ) by
        show (mat x0 τ * ExF.nM X z' τ) * mat b' τ = _; exact Matrix.mul_assoc _ _ _,
      Matrix.nonsing_inv_mul_cancel_left _ _ hu, Matrix.nonsing_inv_mul_cancel_left _ _ hu] at this
  have hn : ∀ τ, ExF.nM X z τ = ExF.nM X z' τ := fun τ =>
    lu_unique (nM_low X z τ) (nM_low X z' τ) (ExF.nM_diag X z τ) (ExF.nM_diag X z' τ)
      (FrameDegreeData.upper_of_bor X hb τ) (FrameDegreeData.upper_of_bor X hb' τ) (hb τ).1 (hN τ)
  refine ⟨nmat_inj X hn, ?_⟩
  funext τ
  have hu : IsUnit (ExF.nM X z τ).det := by rw [ExF.det_nM]; exact isUnit_one
  have := hN τ
  rw [hn τ] at this
  rw [← hn τ] at this
  have := congrArg (fun M => (ExF.nM X z τ)⁻¹ * M) this
  simp only [Matrix.nonsing_inv_mul_cancel_left _ _ hu] at this
  exact this

end

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.KU
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPfC
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf

open Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
  Metric

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r} {x0 : Frame X.Ψ r}

theorem diffOn_det {k : ℕ} {s : Set (Frame X.Ψ r)} (m : Frame X.Ψ r → Matrix (Fin k) (Fin k) ℂ)
    (hm : ∀ i j, DifferentiableOn ℂ (fun x => m x i j) s) : DifferentiableOn ℂ (fun x => (m x).det) s := by
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  have hp : ∀ σ : Equiv.Perm (Fin k), DifferentiableOn ℂ (fun x => ∏ i, m x (σ i) i) s := by
    intro σ
    induction (Finset.univ : Finset (Fin k)) using Finset.induction_on with
    | empty => simp [differentiableOn_const]
    | insert a t ha ih =>
      simp only [Finset.prod_insert ha]
      exact (hm (σ a) a).mul ih
  fun_prop

theorem diffOn_inv {k : ℕ} {s : Set (Frame X.Ψ r)} (m : Frame X.Ψ r → Matrix (Fin k) (Fin k) ℂ)
    (hm : ∀ i j, DifferentiableOn ℂ (fun x => m x i j) s) (hd : ∀ x ∈ s, (m x).det ≠ 0) :
    ∀ i j, DifferentiableOn ℂ (fun x => (m x)⁻¹ i j) s := by
  intro i j
  have hadj : DifferentiableOn ℂ (fun x => (m x).adjugate i j) s := by
    simp only [Matrix.adjugate_apply]
    refine diffOn_det (fun x => (m x).updateRow j (Pi.single i 1)) ?_
    intro a b
    by_cases h : a = j
    · simp [Matrix.updateRow_apply, h, differentiableOn_const]
    · simpa [Matrix.updateRow_apply, h] using hm a b
  have hinv : DifferentiableOn ℂ (fun x => ((m x).det)⁻¹) s := (diffOn_det m hm).inv hd
  refine (hinv.mul hadj).congr ?_
  intro x _
  simp [Matrix.inv_def, Ring.inverse_eq_inv']

theorem Mx_diff (τ : X.Ψ) (a c : Fin r) : Differentiable ℂ (fun x => Mx X x0 x τ a c) := by
  simp only [Mx, Matrix.mul_apply, ReciprocityTheory.ChartRestriction.G.FD.mat, Matrix.of_apply]
  first
    | fun_prop
    | exact Differentiable.sum fun b _ => (differentiable_const _).mul
        ((differentiable_apply c).comp ((differentiable_apply b).comp (differentiable_apply τ)))

theorem Delta_diff : Differentiable ℂ (DeltaF X x0) := by
  have hdet : ∀ τ (k : Fin (r + 1)), Differentiable ℂ (fun x => lminor (Mx X x0 x τ) k) := by
    intro τ k
    rw [← differentiableOn_univ]
    exact diffOn_det (s := Set.univ)
      (fun x => (Mx X x0 x τ).submatrix (Fin.castLE (Nat.le_of_lt_succ k.isLt))
        (Fin.castLE (Nat.le_of_lt_succ k.isLt)))
      (fun i j => (Mx_diff τ _ _).differentiableOn)
  show Differentiable ℂ (fun x => ∏ τ, ∏ k : Fin (r + 1), lminor (Mx X x0 x τ) k)
  fun_prop

def cellL (X : Data E r) (x0 : Frame X.Ψ r) : Set (Frame X.Ψ r) := {x | x ∈ X.dom ∧ DeltaF X x0 x ≠ 0}

theorem Lm_diff (τ : X.Ψ) (i k : Fin r) :
    DifferentiableOn ℂ (fun x => Lm (Mx X x0 x τ) i k) (cellL X x0) := by
  have hl : ∀ x ∈ cellL X x0, ∀ k : Fin (r + 1), lminor (Mx X x0 x τ) k ≠ 0 := by
    intro x hx k
    have h1 : DeltaF X x0 x ≠ 0 := hx.2
    unfold DeltaF at h1
    exact Finset.prod_ne_zero_iff.mp (Finset.prod_ne_zero_iff.mp h1 τ (Finset.mem_univ _)) k
      (Finset.mem_univ _)
  by_cases h1 : (k : ℕ) < i
  · simp only [Lm, Matrix.of_apply, h1, ↓reduceDIte]
    have hinv : ∀ a b, DifferentiableOn ℂ (fun x => (lb (Mx X x0 x τ) i)⁻¹ a b) (cellL X x0) :=
      diffOn_inv (fun x => lb (Mx X x0 x τ) i) (fun a b => (Mx_diff τ _ _).differentiableOn)
        (fun x hx => by rw [det_lb]; exact hl x hx _)
    have hM : ∀ a b, DifferentiableOn ℂ (fun x => Mx X x0 x τ a b) (cellL X x0) :=
      fun a b => (Mx_diff τ a b).differentiableOn
    simp only [wv, Matrix.vecMul, dotProduct]
    refine DifferentiableOn.fun_neg ?_
    refine DifferentiableOn.fun_sum fun j _ => ?_
    exact (hM i _).mul (hinv j ⟨k, h1⟩)
  · by_cases h2 : k = i
    · subst h2
      simp only [Lm, Matrix.of_apply, lt_irrefl, ↓reduceDIte, ↓reduceIte]
      fun_prop
    · simp only [Lm, Matrix.of_apply, h1, ↓reduceDIte, h2, ↓reduceIte]
      fun_prop

theorem nF_diff (τ : X.Ψ) (a c : Fin r) : DifferentiableOn ℂ (fun x => nF X x0 x τ a c) (cellL X x0) :=
  diffOn_inv (fun x => Lm (Mx X x0 x τ)) (fun i k => Lm_diff τ i k)
    (fun x _ => by rw [Lm_det]; exact one_ne_zero) a c

theorem bF_diff (τ : X.Ψ) (a c : Fin r) : DifferentiableOn ℂ (fun x => bF X x0 x τ a c) (cellL X x0) := by
  simp only [bF, Matrix.mul_apply]
  exact DifferentiableOn.fun_sum fun b _ => (Lm_diff τ a b).mul (Mx_diff τ b c).differentiableOn

theorem bF_diffOn : DifferentiableOn ℂ (bF X x0) (cellL X x0) := by
  rw [differentiableOn_pi]
  intro τ
  rw [differentiableOn_pi]
  intro a
  rw [differentiableOn_pi]
  intro c
  exact bF_diff τ a c

theorem zF_diffOn : DifferentiableOn ℂ (zF X x0) (cellL X x0) := by
  rw [differentiableOn_euclidean]
  intro k
  simp only [zF, PiLp.toLp_apply]
  exact nF_diff _ _ _

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustFStatementPf
namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField Topology Filter ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
  ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD ReciprocityTheory.ChartRestriction.G.AR.Up.ExhE
open scoped ContDiff

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private theorem val_chart_symm_apply {n : ℕ} {U : Set (V n)} (e : OpenPartialHomeomorph U (V n))
    (he : IsChart n Subtype.val e) {w : V n} (hw : w ∈ e.target) : ((e.symm w : U) : V n) = w := by
  have h1 : e.symm w ∈ e.source := e.map_target hw
  rw [he h1]
  exact e.right_inv hw

private theorem comp_chart_symm_eventuallyEq_of_mem_target {n : ℕ} {U : Set (V n)} (e : OpenPartialHomeomorph U (V n))
    (he : IsChart n Subtype.val e) (g : V n → ℂ) {w : V n} (hw : w ∈ e.target) :
    (fun y : U => g y.1) ∘ e.symm =ᶠ[nhds w] g := by
  filter_upwards [e.open_target.mem_nhds hw] with y hy
  simp only [Function.comp_apply]
  rw [val_chart_symm_apply e he hy]

private theorem exists_isChart_subtype_val {n : ℕ} {U : Set (V n)} (hz : IsLocalHomeomorph (Subtype.val : U → V n))
    (y : U) : ∃ e : OpenPartialHomeomorph U (V n), IsChart n Subtype.val e ∧ y ∈ e.source := by
  obtain ⟨e, hy, he⟩ := hz y
  exact ⟨e, fun a _ => by rw [he], hy⟩

private theorem db_subtype_val_eq_wdb {n : ℕ} {U : Set (V n)} (hz : IsLocalHomeomorph (Subtype.val : U → V n))
    (g : V n → ℂ) (k : Fin n) (y : U) : db n Subtype.val k (fun y : U => g y.1) y = wdb n k g y.1 := by
  have hex := exists_isChart_subtype_val hz y
  unfold db
  rw [dite_eq_left hex]
  have hc := Classical.choose_spec hex
  have hw : y.1 ∈ (Classical.choose hex).target := by
    rw [hc.1 hc.2]
    exact (Classical.choose hex).map_source hc.2
  unfold wdb
  rw [(comp_chart_symm_eventuallyEq_of_mem_target _ hc.1 g hw).fderiv_eq]

private theorem d_subtype_val_eq_wd {n : ℕ} {U : Set (V n)} (hz : IsLocalHomeomorph (Subtype.val : U → V n))
    (g : V n → ℂ) (k : Fin n) (y : U) : d n Subtype.val k (fun y : U => g y.1) y = wd n k g y.1 := by
  have hex := exists_isChart_subtype_val hz y
  unfold d
  rw [dite_eq_left hex]
  have hc := Classical.choose_spec hex
  have hw : y.1 ∈ (Classical.choose hex).target := by
    rw [hc.1 hc.2]
    exact (Classical.choose hex).map_source hc.2
  unfold wd
  rw [(comp_chart_symm_eventuallyEq_of_mem_target _ hc.1 g hw).fderiv_eq]

private theorem levi_lemma_6 {n : ℕ} {U : Set (V n)} (hz : IsLocalHomeomorph (Subtype.val : U → V n))
    (ph : V n → ℝ) (x : U) (ξ : Fin n → ℂ) :
    Levi n Subtype.val (fun y : U => ph y.1) x ξ = leviV n (fun w => ((ph w : ℝ) : ℂ)) x.1 ξ := by
  unfold Levi leviV
  beta_reduce
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  have h1 : db n Subtype.val k (fun y : U => ((ph y.1 : ℝ) : ℂ)) =
      fun y : U => wdb n k (fun w => ((ph w : ℝ) : ℂ)) y.1 :=
    funext fun y => db_subtype_val_eq_wdb hz (fun w => ((ph w : ℝ) : ℂ)) k y
  rw [h1, d_subtype_val_eq_wd hz (wdb n k (fun w => ((ph w : ℝ) : ℂ))) j x]

private theorem leviV_add {n : ℕ} (g1 g2 : V n → ℂ) (y : V n)
    (h1 : ∀ᶠ w in nhds y, ContDiffAt ℝ ∞ g1 w) (h2 : ∀ᶠ w in nhds y, ContDiffAt ℝ ∞ g2 w)
    (ξ : Fin n → ℂ) :
    leviV n (fun w => g1 w + g2 w) y ξ = leviV n g1 y ξ + leviV n g2 y ξ := by
  have hev : ∀ k, wdb n k (fun w => g1 w + g2 w) =ᶠ[nhds y] fun w => wdb n k g1 w + wdb n k g2 w := by
    intro k
    filter_upwards [h1, h2] with w hw1 hw2
    have d1 : DifferentiableAt ℝ g1 w := hw1.differentiableAt (by first | norm_num | simp)
    have d2 : DifferentiableAt ℝ g2 w := hw2.differentiableAt (by first | norm_num | simp)
    unfold wdb
    first
      | rw [fderiv_fun_add d1 d2]
      | rw [fderiv_add' d1 d2]
      | rw [show (fun w => g1 w + g2 w) = g1 + g2 from rfl, fderiv_add d1 d2]
    simp only [ContinuousLinearMap.add_apply]
    ring
  have hdiff : ∀ g : V n → ℂ, ContDiffAt ℝ ∞ g y → ∀ k, DifferentiableAt ℝ (wdb n k g) y := by
    intro g hg k
    have hf : ContDiffAt ℝ 1 (fderiv ℝ g) y := hg.fderiv_right (by
      first
        | exact WithTop.coe_le_coe.mpr le_top
        | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤)
        | (norm_num; done)
        | (simp; done))
    have hfd : DifferentiableAt ℝ (fderiv ℝ g) y := hf.differentiableAt (by first | exact one_ne_zero | exact le_rfl | simp)
    have ha : DifferentiableAt ℝ (fun w => fderiv ℝ g w (bas n k)) y :=
      hfd.clm_apply (differentiableAt_const _)
    have hb : DifferentiableAt ℝ (fun w => fderiv ℝ g w (Complex.I • bas n k)) y :=
      hfd.clm_apply (differentiableAt_const _)
    unfold wdb
    first
      | exact (ha.fun_add (hb.const_mul Complex.I)).div_const 2
      | exact (ha.add (hb.const_mul Complex.I)).div_const 2
      | fun_prop
  unfold leviV
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e1 : wd n j (wdb n k (fun w => g1 w + g2 w)) y =
      wd n j (wdb n k g1) y + wd n j (wdb n k g2) y := by
    unfold wd
    rw [(hev k).fderiv_eq]
    first
      | rw [fderiv_fun_add (hdiff g1 h1.self_of_nhds k) (hdiff g2 h2.self_of_nhds k)]
      | rw [fderiv_add' (hdiff g1 h1.self_of_nhds k) (hdiff g2 h2.self_of_nhds k)]
      | rw [show (fun w => wdb n k g1 w + wdb n k g2 w) = wdb n k g1 + wdb n k g2 from rfl,
          fderiv_add (hdiff g1 h1.self_of_nhds k) (hdiff g2 h2.self_of_nhds k)]
    simp only [ContinuousLinearMap.add_apply]
    ring
  rw [e1]
  ring

theorem exhaustF_holds : ExhaustFStatement (E := E) := by
  intro r X x0 ho
  have hU : IsOpen (OmF X x0) := ExF.isOpen_OmF X x0
  have hz : IsLocalHomeomorph (Subtype.val : OmF X x0 → _) := by
    first
      | exact hU.isOpenEmbedding_subtypeVal.isLocalHomeomorph
      | exact hU.openEmbedding_subtype_val.isLocalHomeomorph
  have hgE : ∀ w ∈ OmF X x0, ContDiffAt ℝ ∞ (fun w => ((eF X x0 w : ℝ) : ℂ)) w := fun w hw =>
    Complex.ofRealCLM.contDiff.contDiffAt.comp w (ExF.eF_contDiffAt X x0 ho hw)
  have hg1 : ∀ w ∈ OmF X x0, ContDiffAt ℝ ∞ (fun w => ((rhF X x0 w : ℝ) : ℂ)) w := fun w hw =>
    Complex.ofRealCLM.contDiff.contDiffAt.comp w (ExF.rhF_contDiffAt X x0 ho hw)
  have hg2 : ∀ {m : ℕ} (w : V m), ContDiffAt ℝ ∞ (fun w : V m => ((Real.log (1 + ‖w‖ ^ 2) : ℝ) : ℂ)) w :=
    fun w => Complex.ofRealCLM.contDiff.contDiffAt.comp w
      ((contDiff_const.add (contDiff_norm_sq ℂ)).log fun w => by positivity).contDiffAt
  refine ⟨{
      z := Subtype.val
      isLocalHomeomorph := hz
      e := (fun y => eF X x0 y.1)
      smooth_e := ?_
      levi_e := ?_
      isCompact_le := ?_ }, rfl, rfl⟩
  · unfold SmoothR Smooth
    intro e he
    refine ContDiffOn.congr (f := fun w => ((eF X x0 w : ℝ) : ℂ))
      (fun w hw => (hgE w ?_).contDiffWithinAt) (fun w hw => ?_)
    · rw [← val_chart_symm_apply e he hw]
      exact (e.symm w).2
    · simp only [Function.comp_apply]
      rw [val_chart_symm_apply e he hw]
  · unfold LeviNonneg
    intro x ξ
    rw [levi_lemma_6 hz (eF X x0) x ξ]
    have hsplit : (fun w => ((eF X x0 w : ℝ) : ℂ)) =
        fun w => ((rhF X x0 w : ℝ) : ℂ) + ((Real.log (1 + ‖w‖ ^ 2) : ℝ) : ℂ) := by
      funext w
      simp [eF]
    have hev1 : ∀ᶠ w in nhds x.1, ContDiffAt ℝ ∞ (fun w => ((rhF X x0 w : ℝ) : ℂ)) w :=
      Filter.eventually_of_mem (hU.mem_nhds x.2) hg1
    have hev2 : ∀ᶠ w in nhds x.1, ContDiffAt ℝ ∞ (fun w => ((Real.log (1 + ‖w‖ ^ 2) : ℝ) : ℂ)) w :=
      Filter.Eventually.of_forall fun w => hg2 w
    rw [hsplit, leviV_add _ _ _ hev1 hev2, Complex.add_re]
    exact add_nonneg (ExF.levi_rhF_nonneg X x0 ho x.2 ξ) (ExF.leviT_nonneg _ ξ)
  · intro a
    have hc := ExF.isCompact_subF X x0 ho a
    rw [Subtype.isCompact_iff]
    convert hc using 1
    ext w
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨hw, ha⟩
      exact ⟨⟨w, hw⟩, ha, rfl⟩

end ReciprocityTheory.ChartRestriction.G.AR.Up
end
