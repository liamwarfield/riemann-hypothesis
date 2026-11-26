module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfToRealRel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitTauCoordinateAddNsmulFirstVariable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadingEqZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefficientMapEnlargedBaseEqComplexMultiple
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoefficientMapsAgreeRootOfUnityEnlarged

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicFrameSliceComponentUniformisati
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundedDomainArithmeticGroupLocallyInjective
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundedDomainArithmeticGroupLocallyInjective
open NumberField

open Matrix Formalism.DegreeFormula Formalism.MJ Formalism.UG ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.TrueCx Topology Filter

noncomputable section

namespace GlobalTheory.LocInj

variable {ι : Type} [Fintype ι] {p q : ℕ}

theorem isOpen_domI : IsOpen (DomI ι p q) := by
  have hc : Continuous (flat : (ι → Matrix (Fin p) (Fin q) ℂ) → ι × Fin p × Fin q → ℂ) :=
    continuous_pi fun x => (continuous_apply x.1).matrix_elem x.2.1 x.2.2
  exact GlobalTheory.HodgeDomain.ActionDeriv.isOpen_domFlat.preimage hc

theorem continuousAt_moeb (M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (z : Matrix (Fin p) (Fin q) ℂ)
    (hu : IsUnit (M.toBlocks₂₁ * z + M.toBlocks₂₂).det) :
    ContinuousAt (fun w : Matrix (Fin p) (Fin q) ℂ => moeb M w) z := by
  unfold moeb
  set A := M.toBlocks₁₁
  set B := M.toBlocks₁₂
  set C := M.toBlocks₂₁
  set D := M.toBlocks₂₂
  have h1 : Continuous (fun w : Matrix (Fin p) (Fin q) ℂ => A * w + B) :=
    (continuous_const.matrix_mul continuous_id).add continuous_const
  have h2 : Continuous (fun w : Matrix (Fin p) (Fin q) ℂ => C * w + D) :=
    (continuous_const.matrix_mul continuous_id).add continuous_const
  have hi : ContinuousAt (Inv.inv : Matrix (Fin q) (Fin q) ℂ → Matrix (Fin q) (Fin q) ℂ) (C * z + D) := by
    refine continuousAt_matrix_inv _ ?_
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hu.ne_zero
  have h3 : ContinuousAt (fun w : Matrix (Fin p) (Fin q) ℂ => (C * w + D)⁻¹) z :=
    ContinuousAt.comp (g := Inv.inv) hi h2.continuousAt
  have hm : Continuous (fun x : Matrix (Fin p) (Fin q) ℂ × Matrix (Fin q) (Fin q) ℂ => x.1 * x.2) :=
    continuous_fst.matrix_mul continuous_snd
  exact ContinuousAt.comp (g := fun x : Matrix (Fin p) (Fin q) ℂ × Matrix (Fin q) (Fin q) ℂ => x.1 * x.2)
    (f := fun w => (A * w + B, (C * w + D)⁻¹)) hm.continuousAt (h1.continuousAt.prodMk h3)

theorem continuousAt_moebI {g : ι → GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ UpqI ι p q) {z : ι → Matrix (Fin p) (Fin q) ℂ}
    (hz : z ∈ DomI ι p q) : ContinuousAt (moebI g) z := by
  refine continuousAt_pi.2 fun t => ?_
  have hu := GlobalTheory.HodgeDomain.kapQ_isUnit (hg t trivial) (hz t)
  exact ContinuousAt.comp (g := fun w => moeb ((g t : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) w)
    (continuousAt_moeb _ _ hu) (continuous_apply t).continuousAt

theorem moebI_one (z : ι → Matrix (Fin p) (Fin q) ℂ) : moebI (1 : ι → GL (Fin p ⊕ Fin q) ℂ) z = z := by
  funext t
  simp [moebI, GlobalTheory.TrueCx.PointWell.moeb_one]

end GlobalTheory.LocInj

namespace GlobalTheory.LocInj

open GlobalTheory.ShFam.SecFrame

theorem continuous_frameAt {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {j : ℕ}
    (hj : j ≤ r) {Tau : Type} (κ : Tau ≃ X.Ψ) : Continuous (frameAt X hj κ) := by
  refine continuous_pi fun τ => ?_
  show Continuous fun z : Tau → Matrix (Fin j) (Fin (r - j)) ℂ =>
    mat (x0F X) τ * (reindex (idx hj) (idx hj)).symm (fromBlocks 1 (z (κ.symm τ)) 0 1)
  refine continuous_const.matrix_mul ?_
  simp only [reindex_symm, reindex_apply, Equiv.symm_symm]
  exact (continuous_const.matrix_fromBlocks (continuous_apply _) continuous_const continuous_const).matrix_submatrix _ _

theorem locInj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r j : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (hj : j ≤ r) (Tau : Type) [Fintype Tau] (κ : Tau ≃ X.Ψ), X.p0 = r - j → ∀ z₀ ∈ Formalism.DegreeFormula.DomI Tau j (r - j), ∃ O : Set (Tau → Matrix (Fin j) (Fin (r - j)) ℂ), IsOpen O ∧ z₀ ∈ O ∧ ∀ z ∈ O ∩ Formalism.DegreeFormula.DomI Tau j (r - j), ∀ z' ∈ O ∩ Formalism.DegreeFormula.DomI Tau j (r - j), ∀ γ ∈ X.Γ, z' = Formalism.DegreeFormula.moebI (GlobalTheory.TrueCx.toUpq X hj κ γ) z → z = z' := by
  intro E _ _ _ r j X hj Tau _ κ hp z₀ hz₀
  haveI : LocallyCompactSpace (Tau → Matrix (Fin j) (Fin (r - j)) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Tau → Fin j → Fin (r - j) → ℂ))

  obtain ⟨C, hCn, hCD, hCc⟩ := local_compact_nhds (isOpen_domI.mem_nhds hz₀)
  set K := frameAt X hj κ '' C with hK
  have hKc : IsCompact K := hCc.image (continuous_frameAt X hj κ)
  have hKd : K ⊆ X.dom := by
    rintro _ ⟨z, hz, rfl⟩
    exact frameAt_mem X hj κ hp (hCD hz)
  have hS := GlobalTheory.T.finite_setOf_lact_eq_rmul_blockTriangular E r X K hKc hKd
  set S := {γ : GL (Fin r) E | γ ∈ X.Γ ∧ ∃ x ∈ K, ∃ y ∈ K, ∃ b : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r,
    (∀ τ, (ReciprocityTheory.ChartRestriction.G.FD.mat b τ).det ≠ 0) ∧
    (∀ τ (a c : Fin r), (c : ℕ) < X.p0 → ¬ (a : ℕ) < X.p0 → b τ a c = 0) ∧
    ReciprocityTheory.ChartRestriction.G.FD.lact γ x = ReciprocityTheory.ChartRestriction.G.FD.rmul y b} with hSdef

  have hev : ∀ γ ∈ S, ∀ᶠ w in 𝓝 z₀ ×ˢ 𝓝 z₀, γ ≠ 1 → moebI (toUpq X hj κ γ) w.1 ≠ w.2 := by
    intro γ hγS
    by_cases h1 : γ = 1
    · exact Filter.Eventually.of_forall fun _ h => absurd h1 h
    have hne : moebI (toUpq X hj κ γ) z₀ ≠ z₀ := by
      intro h
      have hx := frameAt_mem X hj κ hp hz₀
      refine h1 (GlobalTheory.FreeOnDomain.eq_one_of_domPt_lact_eq E r j X hj Tau κ hp γ hγS.1 _ hx ?_)
      rw [domPt_lact X hj κ hp γ hx, domPt_frameAt, h]
    have hc : ContinuousAt (fun w : (Tau → Matrix (Fin j) (Fin (r - j)) ℂ) × (Tau → Matrix (Fin j) (Fin (r - j)) ℂ) =>
        moebI (toUpq X hj κ γ) w.1) (z₀, z₀) :=
      ContinuousAt.comp (g := moebI (toUpq X hj κ γ))
        (continuousAt_moebI (gammaU_le X hj κ hp ⟨γ, hγS.1, rfl⟩) hz₀) continuous_fst.continuousAt
    have hO : IsOpen {w : (Tau → Matrix (Fin j) (Fin (r - j)) ℂ) × (Tau → Matrix (Fin j) (Fin (r - j)) ℂ) |
        w.1 ≠ w.2} := isOpen_ne_fun continuous_fst continuous_snd
    have := (hc.prodMk continuous_snd.continuousAt).preimage_mem_nhds (hO.mem_nhds hne)
    rw [nhds_prod_eq] at this
    exact Filter.mem_of_superset this fun w hw _ => hw
  have hCC : C ×ˢ C ∈ 𝓝 z₀ ×ˢ 𝓝 z₀ := Filter.prod_mem_prod hCn hCn
  have hall : ∀ᶠ w in 𝓝 z₀ ×ˢ 𝓝 z₀, (fun a b => a ∈ C ∧ b ∈ C ∧ ∀ γ ∈ S, γ ≠ 1 → moebI (toUpq X hj κ γ) a ≠ b) w.1 w.2 :=
    (Filter.Eventually.and hCC ((Filter.eventually_all_finite hS).2 hev)).mono fun w h => ⟨h.1.1, h.1.2, h.2⟩
  obtain ⟨t, ht, htP⟩ := (Filter.eventually_prod_self_iff (la := 𝓝 z₀)
    (r := fun a b => a ∈ C ∧ b ∈ C ∧ ∀ γ ∈ S, γ ≠ 1 → moebI (toUpq X hj κ γ) a ≠ b)).1 hall
  refine ⟨interior t, isOpen_interior, mem_interior_iff_mem_nhds.2 ht, ?_⟩
  rintro z ⟨hzt, hzD⟩ z' ⟨hzt', hzD'⟩ γ hγ e
  obtain ⟨hzC, hzC', hmove⟩ := htP z (interior_subset hzt) z' (interior_subset hzt')
  have hx := frameAt_mem X hj κ hp hzD
  have hy := frameAt_mem X hj κ hp hzD'
  have hgx := KU.lact_dom X hγ hx
  set x := frameAt X hj κ z
  set y := frameAt X hj κ z'
  have hpt : domPt X hj κ (lact γ x) = domPt X hj κ y := by
    rw [domPt_lact X hj κ hp γ hx, domPt_frameAt, domPt_frameAt, e]
  have hblk : ∀ τ (a c : Fin r), X.p0 ≤ a → (c : ℕ) < X.p0 → ((mat y τ)⁻¹ * mat (lact γ x) τ) a c = 0 := by
    intro τ
    refine GlobalTheory.TrueCx.PointWell.block_of_moeb_eq X hj hp hy hgx τ ?_
    obtain ⟨s, rfl⟩ := κ.surjective τ
    exact (congrFun hpt s).symm
  have hγS : γ ∈ S := by
    refine ⟨hγ, x, ⟨z, hzC, rfl⟩, y, ⟨z', hzC', rfl⟩, fun τ => (mat y τ)⁻¹ * mat (lact γ x) τ, fun τ => ?_,
      fun τ a c hc ha => hblk τ a c (not_lt.1 ha) hc, ?_⟩
    · show ((mat y τ)⁻¹ * mat (lact γ x) τ).det ≠ 0
      rw [det_mul, det_nonsing_inv]
      exact mul_ne_zero (by rw [Ring.inverse_eq_inv']; exact inv_ne_zero (hy τ).1) (hgx τ).1
    · funext τ
      show mat (lact γ x) τ = mat y τ * ((mat y τ)⁻¹ * mat (lact γ x) τ)
      rw [mul_nonsing_inv_cancel_left _ _ (hy τ).1.isUnit]
  by_contra hne
  by_cases h1 : γ = 1
  · subst h1
    apply hne
    rw [e, map_one, moebI_one]
  · exact hmove γ hγS h1 e.symm

end GlobalTheory.LocInj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundedDomainArithmeticGroupLocallyInjectiveStatement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundedDomain_arithmeticGroup_locally_injective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r j : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (hj : j ≤ r) (Tau : Type) [Fintype Tau] (κ : Tau ≃ X.Ψ), X.p0 = r - j → ∀ z₀ ∈ Formalism.DegreeFormula.DomI Tau j (r - j), ∃ O : Set (Tau → Matrix (Fin j) (Fin (r - j)) ℂ), IsOpen O ∧ z₀ ∈ O ∧ ∀ z ∈ O ∩ Formalism.DegreeFormula.DomI Tau j (r - j), ∀ z' ∈ O ∩ Formalism.DegreeFormula.DomI Tau j (r - j), ∀ γ ∈ X.Γ, z' = Formalism.DegreeFormula.moebI (GlobalTheory.TrueCx.toUpq X hj κ γ) z → z = z' := by
  first | exact @GlobalTheory.LocInj.locInj | exact GlobalTheory.LocInj.locInj | (intros; apply GlobalTheory.LocInj.locInj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicFrameSliceComponentUniformisati
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open scoped ComplexOrder Topology
open ReciprocityTheory.L2DbarEstimates (V)
open ReciprocityTheory.ChartRestriction.G.FD (Frame mat)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnifSlice

open Matrix Formalism.DegreeFormula GlobalTheory.TrueCx ReciprocityTheory.ChartRestriction.G.FD

theorem locInj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r j : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (hj : j ≤ r) (Tau : Type) [Fintype Tau] (κ : Tau ≃ X.Ψ), X.p0 = r - j → ∀ z₀ ∈ Formalism.DegreeFormula.DomI Tau j (r - j), ∃ O : Set (Tau → Matrix (Fin j) (Fin (r - j)) ℂ), IsOpen O ∧ z₀ ∈ O ∧ ∀ z ∈ O ∩ Formalism.DegreeFormula.DomI Tau j (r - j), ∀ z' ∈ O ∩ Formalism.DegreeFormula.DomI Tau j (r - j), ∀ γ ∈ X.Γ, z' = Formalism.DegreeFormula.moebI (GlobalTheory.TrueCx.toUpq X hj κ γ) z → z = z' := GlobalTheory.T.boundedDomain_arithmeticGroup_locally_injective

theorem domPt_rel_of_pt_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (U : Formalism.L2.PjFree.Unf Xo c σ r)
    (hU : Formalism.L2.PjFree.IsUnf U) (hσ : Formalism.L2.PjFree.GoodEmb c σ)
    (k : U.Comp) {j : ℕ} (hj : j ≤ r) (hp : (U.X k).p0 = r - j) {Tau : Type} [Fintype Tau] (κ : Tau ≃ (U.X k).Ψ)
    (x x' : (U.X k).dom) (h : (U.un k x).x = (U.un k x').x) :
    ∃ γ ∈ (U.X k).Γ, domPt (U.X k) hj κ x'.1 = moebI (toUpq (U.X k) hj κ γ) (domPt (U.X k) hj κ x.1) := by
  obtain ⟨b, hb, hb0, hm, t, ht⟩ := GlobalTheory.PointOfFrames.exists_frBor U hU hσ k x (U.un k x') h
  obtain ⟨γ, hγ, b', hb', e⟩ := (hU.2.2.2.1 k k ⟨_, hm⟩ x').1 ⟨t, ht⟩
  have e' : x'.1 = rmul (lact γ (rmul x.1 b)) b' := eq_of_heq (Sigma.mk.inj e).2
  refine ⟨γ, hγ, ?_⟩
  rw [e', domPt_rmul _ hj κ hb', domPt_lact _ hj κ hp γ hm,
    GlobalTheory.PointOfFrames.domPt_rmul_block _ hj κ _ b hb (by rw [← hp]; exact hb0)]

theorem flat_unflat {ι : Type} {p q : ℕ} (v : ι × Fin p × Fin q → ℂ) : flat (unflat v) = v := by
  funext ⟨i, a, b⟩; rfl

theorem unflat_flat {ι : Type} {p q : ℕ} (z : ι → Matrix (Fin p) (Fin q) ℂ) : unflat (flat z) = z := by
  funext i; ext a b; rfl

theorem continuous_unflat {ι : Type} {p q : ℕ} :
    Continuous (unflat : (ι × Fin p × Fin q → ℂ) → ι → Matrix (Fin p) (Fin q) ℂ) :=
  continuous_pi fun _ => continuous_matrix fun _ _ => continuous_apply _

theorem exists_slice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (k : U.Comp) (x₀ : (U.X k).dom) (n : ℕ), n = (U.X k).Ψ.card * (Dw.p * Dw.q) → ∃ (W : Set (V n)) (a : V n) (ψ : V n → Frame (U.X k).Ψ (Dw.p + Dw.q)), IsOpen W ∧ a ∈ W ∧ (∀ w ∈ W, ψ w ∈ (U.X k).dom) ∧ (∀ τ i i', DifferentiableOn ℂ (fun w => mat (ψ w) τ i i') W) ∧ (∀ h : ψ a ∈ (U.X k).dom, (U.un k ⟨ψ a, h⟩).x = (U.un k x₀).x) ∧ ∀ w ∈ W, ∀ w' ∈ W, ∀ (h : ψ w ∈ (U.X k).dom) (h' : ψ w' ∈ (U.X k).dom), (U.un k ⟨ψ w, h⟩).x = (U.un k ⟨ψ w', h'⟩).x → w = w' := by
  intro E _ _ _ H Dw l Xo c σ U hσ hU k x₀ n hn
  classical
  have hj : Dw.p ≤ Dw.p + Dw.q := Nat.le_add_right _ _
  have hp : (U.X k).p0 = Dw.p + Dw.q - Dw.p := by have := (hU.2.1 k).1; omega
  have hcard : Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p)) = n := by
    rw [hn, Fintype.card_prod, Fintype.card_prod, Fintype.card_coe, Fintype.card_fin, Fintype.card_fin,
      Nat.add_sub_cancel_left]
  let f : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p)) ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let L : V n ≃L[ℂ] ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) :=
    (EuclideanSpace.equiv (Fin n) ℂ).trans (LinearEquiv.funCongrLeft ℂ ℂ f).toContinuousLinearEquiv
  set z₀ := domPt (U.X k) hj (Equiv.refl (U.X k).Ψ) x₀.1 with hz₀
  have hz₀D : z₀ ∈ DomI (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) := domPt_mem (U.X k) hj _ hp x₀.2
  obtain ⟨O, hO, hz₀O, hinj⟩ := locInj E (Dw.p + Dw.q) Dw.p (U.X k) hj (U.X k).Ψ (Equiv.refl _) hp z₀ hz₀D
  let ψ : V n → Frame (U.X k).Ψ (Dw.p + Dw.q) := fun w => SecFrame.frameAt (U.X k) hj (Equiv.refl _) (unflat (L w))
  have hdom : ∀ w, unflat (L w) ∈ DomI (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) → ψ w ∈ (U.X k).dom := fun w hw =>
    SecFrame.frameAt_mem (U.X k) hj _ hp hw
  have hpt : ∀ w, domPt (U.X k) hj (Equiv.refl (U.X k).Ψ) (ψ w) = unflat (L w) := fun w => SecFrame.domPt_frameAt (U.X k) hj _ _
  refine ⟨{w | unflat (L w) ∈ O} ∩ L ⁻¹' DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p), L.symm (flat z₀), ψ,
    (hO.preimage (continuous_unflat.comp L.continuous)).inter
      (GlobalTheory.HodgeDomain.ActionDeriv.isOpen_domFlat.preimage L.continuous), ?_, fun w hw => hdom w hw.2,
    fun τ i i' => ((SecFrame.differentiable_frameAt (U.X k) hj (Equiv.refl _) τ i i').comp L.differentiable).differentiableOn,
    fun h => ?_, fun w hw w' hw' h h' e => ?_⟩
  · refine ⟨?_, ?_⟩
    · show unflat (L (L.symm (flat z₀))) ∈ O
      rw [L.apply_symm_apply, unflat_flat]; exact hz₀O
    · show unflat (L (L.symm (flat z₀))) ∈ DomI (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p)
      rw [L.apply_symm_apply, unflat_flat]; exact hz₀D
  · have e0 : domPt (U.X k) hj (Equiv.refl (U.X k).Ψ) (ψ (L.symm (flat z₀))) = domPt (U.X k) hj (Equiv.refl (U.X k).Ψ) x₀.1 := by
      rw [hpt, L.apply_symm_apply, unflat_flat]
    have h5 : ∀ τ, Formalism.MJ.moeb (frameCo (U.X k) hj (ψ (L.symm (flat z₀))) τ) 0 = Formalism.MJ.moeb (frameCo (U.X k) hj x₀.1 τ) 0 :=
      fun τ => congrFun e0 τ
    exact PointWell.pt_eq_of_block hU hσ k ⟨_, h⟩ x₀
      (fun τ => PointWell.block_of_moeb_eq (U.X k) hj hp h x₀.2 τ (h5 τ))
      (fun τ => PointWell.block_of_moeb_eq (U.X k) hj hp x₀.2 h τ (h5 τ).symm)
  · obtain ⟨γ, hγ, hγe⟩ := domPt_rel_of_pt_eq U hU hσ k hj hp (Equiv.refl (U.X k).Ψ) ⟨_, h⟩ ⟨_, h'⟩ e
    have hγe' : unflat (L w') = moebI (toUpq (U.X k) hj (Equiv.refl (U.X k).Ψ) γ) (unflat (L w)) := by
      rw [← hpt w', ← hpt w]; exact hγe
    have h1 := hinj _ ⟨hw.1, hw.2⟩ _ ⟨hw'.1, hw'.2⟩ γ hγ hγe'
    have h2 : L w = L w' := by rw [← flat_unflat (L w), h1, flat_unflat]
    exact L.injective h2

end GlobalTheory.UnifSlice
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicFrameSliceComponentUniformisatiStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open scoped ComplexOrder Topology
open ReciprocityTheory.L2DbarEstimates (V)
open ReciprocityTheory.ChartRestriction.G.FD (Frame mat)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_holomorphic_frame_slice_componentUniformisation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (k : U.Comp) (x₀ : (U.X k).dom) (n : ℕ), n = (U.X k).Ψ.card * (Dw.p * Dw.q) → ∃ (W : Set (V n)) (a : V n) (ψ : V n → Frame (U.X k).Ψ (Dw.p + Dw.q)), IsOpen W ∧ a ∈ W ∧ (∀ w ∈ W, ψ w ∈ (U.X k).dom) ∧ (∀ τ i i', DifferentiableOn ℂ (fun w => mat (ψ w) τ i i') W) ∧ (∀ h : ψ a ∈ (U.X k).dom, (U.un k ⟨ψ a, h⟩).x = (U.un k x₀).x) ∧ ∀ w ∈ W, ∀ w' ∈ W, ∀ (h : ψ w ∈ (U.X k).dom) (h' : ψ w' ∈ (U.X k).dom), (U.un k ⟨ψ w, h⟩).x = (U.un k ⟨ψ w', h'⟩).x → w = w' := by
  first | exact @GlobalTheory.UnifSlice.exists_slice | exact GlobalTheory.UnifSlice.exists_slice | (intros; apply GlobalTheory.UnifSlice.exists_slice <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComponentUniformisationContinuousOnAnalyticAtCha
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComponentUniformisationContinuousOnAnalyticAtCha
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnifHolo

theorem unif_continuousOn_analyticAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ContinuousOn ψ (DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p)) ∧ ∀ w ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p), ∀ ch : AlgChart X.str (σ.comp e.toRingHom) X.dim, ψ w ∈ ch.e.source → AnalyticAt ℂ (fun w' => ch.e (ψ w')) w := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ
  classical
  haveI : IsOpenImmersion j := hL.1
  have hp0 : (U.X k).p0 = Dw.p + Dw.q - Dw.p := by rw [(hU.2.1 k).1]; omega
  let L : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) ≃L[ℂ]
      (Fin (Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p))) → ℂ) :=
    (LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFin _).symm).toContinuousLinearEquiv
  have ho : IsOpen (DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p)) := GlobalTheory.HodgeDomain.ActionDeriv.isOpen_domFlat
  set B : Set (Fin (Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p))) → ℂ) :=
    L.symm ⁻¹' DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) with hBdef
  have hB : IsOpen B := ho.preimage L.symm.continuous
  let x : (Fin (Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p))) → ℂ) → (U.X k).dom := fun b =>
    stdFrame (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl _) hp0 (unflat (L.symm b))
  have hd : ∀ τ a c, DifferentiableOn ℂ (fun b => ReciprocityTheory.ChartRestriction.G.FD.mat (x b).1 τ a c) B := fun τ a c =>
    ((GlobalTheory.TrueCx.TorHolo.differentiable_stdMat (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl _) τ a c).comp
      L.symm.differentiable).differentiableOn.congr fun b hb => by
        show ReciprocityTheory.ChartRestriction.G.FD.mat (stdFrame _ _ _ _ _).1 τ a c = _
        rw [stdFrame_val _ _ _ _ hb]
        rfl
  have hY := GlobalTheory.GramFamily.isHolTo_cxPt T.Z hU k hB x hd
  have key : ∀ v ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p),
      cxOf e σ hj (ψ v) = cxPt T.Z (U.un k (x (L v))) := by
    intro v hv
    have h1 := hψ (x (L v))
    have h2 : flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) (x (L v)).1) = v := by
      show flat (domPt _ _ _ (stdFrame _ _ _ hp0 (unflat (L.symm (L v)))).1) = v
      rw [L.symm_apply_apply, domPt_stdFrame _ _ _ hp0 hv]
      rfl
    rw [h2] at h1
    exact h1
  have hcont : ContinuousOn (fun b => cxPt T.Z (U.un k (x b))) B := by
    rw [continuousOn_iff_continuous_restrict]
    refine GlobalTheory.CxPts.continuous_iff.2 fun W => ⟨?_, fun g => ?_⟩
    · have := (hY W 0).1.preimage (continuous_subtype_val (p := (· ∈ B)))
      convert this using 1
      ext v
      simp only [Set.mem_preimage, Set.restrict_apply, Set.mem_setOf_eq]
      exact ⟨fun h => ⟨v.2, h⟩, fun h => h.2⟩
    · intro v hv
      have hm : (v : Fin _ → ℂ) ∈ {b ∈ B | ⊤ ≤ (cxPt T.Z (U.un k (x b))).1 ⁻¹ᵁ W} := ⟨v.2, hv⟩
      have hca := (((hY W g).2).differentiableAt (((hY W g).1).mem_nhds hm)).continuousAt
      exact (hca.comp continuous_subtype_val.continuousAt).continuousWithinAt
  have hκ := isOpenEmbedding_cxOf e σ hj
  have hLB : ∀ v ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p), L v ∈ B := fun v hv => by
    show L.symm (L v) ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p)
    rwa [L.symm_apply_apply]
  have hψc : ContinuousOn ψ (DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p)) := by
    rw [hκ.isInducing.continuousOn_iff]
    exact (hcont.comp L.continuous.continuousOn hLB).congr fun v hv => key v hv
  refine ⟨hψc, fun w hw ch hch => ?_⟩
  have hS : IsOpen (DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) ∩ ψ ⁻¹' ch.e.source) :=
    hψc.isOpen_inter_preimage ho ch.e.open_source
  refine GlobalTheory.SCV.analyticAt_of_differentiableOn ?_ (hS.mem_nhds ⟨hw, hch⟩)
  refine differentiableOn_euclidean.2 fun a => ?_
  have hmaps : Set.MapsTo L (DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) ∩ ψ ⁻¹' ch.e.source)
      {b ∈ B | ⊤ ≤ (cxPt T.Z (U.un k (x b))).1 ⁻¹ᵁ (j ''ᵁ ch.U)} := fun v hv => by
    refine ⟨hLB v hv.1, ?_⟩
    rw [← key v hv.1]
    exact le_preimage_cxOf e σ hj ch.U (ch.source_subset hv.2)
  refine ((hY (j ''ᵁ ch.U) ((j.appIso ch.U).inv.hom (ch.x a))).2.comp L.differentiableOn hmaps).congr
    fun v hv => ?_
  show ch.e (ψ v) a = valAt' (cxPt T.Z (U.un k (x (L v)))).1 (j ''ᵁ ch.U) ((j.appIso ch.U).inv.hom (ch.x a))
  rw [ch.apply_eq _ hv.2 a, ev_eq_valAt'_cxOf e σ hj _ _ (ch.source_subset hv.2), key v hv.1]

end GlobalTheory.UnifHolo
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComponentUniformisationContinuousOnAnalyticAtChaStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.componentUniformisation_continuousOn_analyticAt_charts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ContinuousOn ψ (DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p)) ∧ ∀ w ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p), ∀ ch : AlgChart X.str (σ.comp e.toRingHom) X.dim, ψ w ∈ ch.e.source → AnalyticAt ℂ (fun w' => ch.e (ψ w')) w := by
  first | exact @GlobalTheory.UnifHolo.unif_continuousOn_analyticAt | exact GlobalTheory.UnifHolo.unif_continuousOn_analyticAt | (intros; apply GlobalTheory.UnifHolo.unif_continuousOn_analyticAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoefficientMapExtensionOverEnlargedBase
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoefficientMapExtensionOverEnlargedBase
set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.R3.Rw.OmCoef

theorem smul_eq_of_heq {W W' : Type} [nW : NormedAddCommGroup W] [iW : InnerProductSpace ℂ W] [nW' : NormedAddCommGroup W']
    [iW' : InnerProductSpace ℂ W'] (hW : W' = W) (hn : HEq nW' nW) (hi : HEq iW' iW) {x' : W'} {y : W} {μ a b : ℂ}
    (h1 : HEq x' (μ • y)) (h2 : HEq (a • x') (b • y)) : (a * μ) • y = b • y := by
  subst hW
  cases hn
  cases hi
  cases h1
  rw [mul_smul]
  exact eq_of_heq h2

theorem heq_smul {W W' : Type} [nW : NormedAddCommGroup W] [iW : InnerProductSpace ℂ W] [nW' : NormedAddCommGroup W']
    [iW' : InnerProductSpace ℂ W'] (hW : W' = W) (hn : HEq nW' nW) (hi : HEq iW' iW) {x' : W'} {y : W} {μ : ℂ}
    (h1 : HEq x' (μ • y)) (a : ℂ) : HEq (a • x') ((a * μ) • y) := by
  subst hW
  cases hn
  cases hi
  cases h1
  rw [mul_smul]

end GlobalTheory.Mem.R3.Rw.OmCoef


set_option maxHeartbeats 4000000 in
theorem GlobalTheory.Mem.R3.Rw.OmCoef.exists_coefFam_ext : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl}
  (z : Dat (w.st Z) w.I hX T Wt), Enl0 B B' → HEq f' f → HEq w'.px w.px → z.Std →
  ∀ {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
    (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks)
    (cG' : G0 R'.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
    Pins R' (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) cG' → LevOf (w'.st Z') w'.I (usedOf w'.I T' Wt') R'.toLevCh →
    BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr R'.toRealDat → RSideW z Wt' R' →
    ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
    ∀ c0L, GlobalTheory.Mem.R3.Rw.OmExt.CoefFam z.R.toRealDat c0L →
      (∀ x : (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.fam.amb.FL i (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0, x = 0) ∨
      ∃ c0L', GlobalTheory.Mem.R3.Rw.OmExt.CoefFam R'.toRealDat c0L' ∧
        ∀ (v : Formalism.IndefR.FWT.VsV (w.st Z).toD7 i (w.st Z).toD7.what₂.LL) (v' : Formalism.IndefR.FWT.VsV (w'.st Z').toD7 i' (w'.st Z').toD7.what₂.LL),
          HEq (MvPolynomial.map (w'.st Z').toD7.what₂.embLL v'.1) (MvPolynomial.map (w.st Z).toD7.what₂.embLL v.1) → HEq (c0L' i' v') (c0L i v) := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Wt' z hE hf hpx hstd Ks _ _ _ Xg tr R' cG' hP hL hB hR i i' hii c0L hc
  obtain ⟨g'', c0R'', c0L'', hT''⟩ := hP.char.base.fam.tie
  have hc'' : GlobalTheory.Mem.R3.Rw.OmExt.CoefFam R'.toRealDat c0L'' := ⟨g'', c0R'', hT''⟩
  by_cases h0 : ∀ x : (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.fam.amb.FL i
      (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0, x = 0
  · exact Or.inl h0
  right
  push_neg at h0
  obtain ⟨x, hx⟩ := h0
  obtain ⟨μ, hμ⟩ := GlobalTheory.T.coefficientMap_enlargedBase_eq_complexMultiple z hE hf hpx hstd R' cG' hP hL hB hR i i' hii c0L hc c0L'' hc''
  obtain ⟨v, v', u, u', n, n', hn, hun, hn', hun', hvv, hv0, hrel⟩ :=
    GlobalTheory.T.exists_coefficientMaps_agree_rootOfUnity_enlarged z hE hf hpx hstd R' cG' hP hL hB hR i i' hii c0L hc c0L'' hc'' x hx
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hcv, -⟩ := hR
  obtain ⟨hW, -, hnW, hiW, -⟩ := hcv i i' hii
  have key := GlobalTheory.Mem.R3.Rw.OmCoef.smul_eq_of_heq (eq_of_heq hW) hnW hiW (hμ v v' hvv) hrel
  have hμe : (w'.st Z').toD7.what₂.embLL u' * μ = (w.st Z).toD7.what₂.embLL u := smul_left_injective ℂ hv0 key
  have hu0 : (w.st Z).toD7.what₂.embLL u ≠ 0 := (map_ne_zero _).2 fun h => by
    rw [h, zero_pow hn] at hun
    exact zero_ne_one hun
  obtain ⟨b, hb⟩ : (w.st Z).toD7.what₂.embLL u ∈ Set.range (w'.st Z').toD7.what₂.embLL := hE.2.2.2 ⟨u, rfl⟩
  have hb1 : b ^ n = 1 := (w'.st Z').toD7.what₂.embLL.injective (by rw [map_pow, hb, ← map_pow, hun, map_one, map_one])
  have ha : (u' * b⁻¹) ^ (n * n') = 1 := by
    have e1 : u' ^ (n * n') = 1 := by rw [mul_comm, pow_mul, hun', one_pow]
    have e2 : b ^ (n * n') = 1 := by rw [pow_mul, hb1, one_pow]
    rw [mul_pow, inv_pow, e1, e2, inv_one, mul_one]
  refine ⟨Function.update c0L'' i' ((w'.st Z').toD7.what₂.embLL (u' * b⁻¹) • c0L'' i'),
    GlobalTheory.T.definiteFamilyCoefficientMaps_mul_rootOfUnity R'.toRealDat c0L'' hc'' i' (u' * b⁻¹) (n * n') (mul_ne_zero hn hn') ha, fun v1 v1' h => ?_⟩
  have eu : Function.update c0L'' i' ((w'.st Z').toD7.what₂.embLL (u' * b⁻¹) • c0L'' i') i' =
      (w'.st Z').toD7.what₂.embLL (u' * b⁻¹) • c0L'' i' := Function.update_self _ _ _
  refine (heq_of_eq ((congrArg (fun g => g v1') eu).trans (LinearMap.smul_apply _ _ _))).trans ?_
  refine (GlobalTheory.Mem.R3.Rw.OmCoef.heq_smul (eq_of_heq hW) hnW hiW (hμ v1 v1' h) _).trans (heq_of_eq ?_)
  have e1 : (w'.st Z').toD7.what₂.embLL (u' * b⁻¹) * μ = 1 := by
    calc (w'.st Z').toD7.what₂.embLL (u' * b⁻¹) * μ = ((w'.st Z').toD7.what₂.embLL u' * μ) * ((w.st Z).toD7.what₂.embLL u)⁻¹ := by
          rw [map_mul, map_inv₀, hb]; ring
      _ = 1 := by rw [hμe, mul_inv_cancel₀ hu0]
  rw [e1, one_smul]

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoefficientMapExtensionOverEnlargedBaseStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coefficientMap_extension_over_enlarged_base : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl}
  (z : Dat (w.st Z) w.I hX T Wt), Enl0 B B' → HEq f' f → HEq w'.px w.px → z.Std →
  ∀ {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
    (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks)
    (cG' : G0 R'.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
    Pins R' (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) cG' → LevOf (w'.st Z') w'.I (usedOf w'.I T' Wt') R'.toLevCh →
    BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr R'.toRealDat → RSideW z Wt' R' →
    ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
    ∀ c0L, GlobalTheory.Mem.R3.Rw.OmExt.CoefFam z.R.toRealDat c0L →
      (∀ x : (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.fam.amb.FL i (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0, x = 0) ∨
      ∃ c0L', GlobalTheory.Mem.R3.Rw.OmExt.CoefFam R'.toRealDat c0L' ∧
        ∀ (v : Formalism.IndefR.FWT.VsV (w.st Z).toD7 i (w.st Z).toD7.what₂.LL) (v' : Formalism.IndefR.FWT.VsV (w'.st Z').toD7 i' (w'.st Z').toD7.what₂.LL),
          HEq (MvPolynomial.map (w'.st Z').toD7.what₂.embLL v'.1) (MvPolynomial.map (w.st Z).toD7.what₂.embLL v.1) → HEq (c0L' i' v') (c0L i v) := by
  first | exact @GlobalTheory.Mem.R3.Rw.OmCoef.exists_coefFam_ext | exact GlobalTheory.Mem.R3.Rw.OmCoef.exists_coefFam_ext | (intros; apply GlobalTheory.Mem.R3.Rw.OmCoef.exists_coefFam_ext <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernPolyTopDensityEqZeroOfWeightedDegreeNeDim
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernPolyTopDensityEqZeroOfWeightedDegreeNeDim
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodMetric.ChernDegree

def gradedCoeff (σ : Type) : Subring (Polynomial (MvPolynomial σ ℂ)) where
  carrier := {p | ∀ k, (p.coeff k).IsHomogeneous k}
  mul_mem' := by
    intro p q hp hq k
    rw [Polynomial.coeff_mul]
    refine IsHomogeneous.sum _ _ _ fun x hx => ?_
    have := (hp x.1).mul (hq x.2)
    rwa [Finset.HasAntidiagonal.mem_antidiagonal.1 hx] at this
  one_mem' := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | h
    · simpa using isHomogeneous_one σ ℂ
    · rw [Polynomial.coeff_one, if_neg (by omega)]; exact isHomogeneous_zero _ _ _
  add_mem' := by
    intro p q hp hq k
    rw [Polynomial.coeff_add]; exact (hp k).add (hq k)
  zero_mem' := by
    intro k
    rw [Polynomial.coeff_zero]; exact isHomogeneous_zero _ _ _
  neg_mem' := by
    intro p hp k
    rw [Polynomial.coeff_neg]; exact (hp k).neg

theorem charpolyRev_coeff_isHomogeneous {σ r : Type} [Fintype r] [DecidableEq r]
    (M : Matrix r r (MvPolynomial σ ℂ)) (hM : ∀ i j, (M i j).IsHomogeneous 1) (k : ℕ) :
    ((Matrix.charpolyRev M).coeff k).IsHomogeneous k := by
  have hent : ∀ i j, (1 - (Polynomial.X : Polynomial (MvPolynomial σ ℂ)) • M.map Polynomial.C) i j ∈ gradedCoeff σ := by
    intro i j
    rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    refine Subring.sub_mem _ ?_ ?_
    · rw [Matrix.one_apply]
      split_ifs
      · exact Subring.one_mem _
      · exact Subring.zero_mem _
    · intro l
      rw [mul_comm, Polynomial.coeff_C_mul_X]
      split_ifs with h
      · subst h; exact hM i j
      · exact isHomogeneous_zero _ _ _
  have hdet : Matrix.charpolyRev M ∈ gradedCoeff σ := by
    rw [Matrix.charpolyRev, Matrix.det_apply']
    refine Subring.sum_mem _ fun s _ => Subring.mul_mem _ (intCast_mem _ _) ?_
    exact Subring.prod_mem _ fun i _ => hent _ _
  exact hdet k

theorem chernPoly_isHomogeneous {n : ℕ} {r : Type} [Fintype r] [DecidableEq r]
    (G : ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ) (v : ReciprocityTheory.L2DbarEstimates.V n) (k : ℕ) :
    (chernPoly G v k).IsHomogeneous k := by
  refine charpolyRev_coeff_isHomogeneous _ (fun i j => ?_) k
  rw [Matrix.neg_apply, curvPoly, Matrix.of_apply]
  exact (IsHomogeneous.sum _ _ _ fun a _ => IsHomogeneous.sum _ _ _ fun b _ =>
    isHomogeneous_C_mul_X _ _).neg

theorem aeval_isWeightedHomogeneous {σ τ : Type} {w : σ → ℕ} {w' : τ → ℕ}
    {φ : MvPolynomial σ ℝ} {m : ℕ} (hφ : IsWeightedHomogeneous w φ m)
    (g : σ → MvPolynomial τ ℂ) (hg : ∀ i, IsWeightedHomogeneous w' (g i) (w i)) :
    IsWeightedHomogeneous w' (aeval g φ) m := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [φ.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  rw [aeval_monomial]
  have hdeg : (Finsupp.weight w) d = m := hφ (mem_support_iff.mp hd)
  have h1 : IsWeightedHomogeneous w' (d.prod fun i k => g i ^ k) (∑ i ∈ d.support, d i • w i) :=
    IsWeightedHomogeneous.prod _ _ _ fun i _ => (hg i).pow (d i)
  have h2 : (∑ i ∈ d.support, d i • w i) = m := by
    rw [← hdeg, Finsupp.weight_apply, Finsupp.sum]
  rw [h2] at h1
  have h3 := (isWeightedHomogeneous_C w' (algebraMap ℝ ℂ (AddMonoidAlgebra.coeff φ d))).mul h1
  rw [zero_add] at h3
  rw [MvPolynomial.algebraMap_apply]
  exact h3

theorem topCoeff_eq_zero {n d : ℕ} {P : MvPolynomial (Fin n × Fin n) ℂ} (hP : P.IsHomogeneous d) (hd : d ≠ n) :
    topCoeff P = 0 := by
  unfold topCoeff
  refine Finset.sum_eq_zero fun w _ => ?_
  rw [hP.coeff_eq_zero, mul_zero]
  intro h
  apply hd
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← h, Finsupp.degree_eq_weight_one, map_sum]
  simp [Finsupp.weight_single]

end GlobalTheory.GoodMetric.ChernDegree


open GlobalTheory.GoodMetric.ChernDegree in
theorem GlobalTheory.GoodMetric.chernTop_eq_zero_of_weightedHomogeneous (n : ℕ) (ι : Type) (m : ι → ℕ)
    (G : ReciprocityTheory.L2DbarEstimates.V n → FlagBundle.Mat m ℂ) (v : ReciprocityTheory.L2DbarEstimates.V n) (Q : MvPolynomial (ι × ℕ) ℝ) (d : ℕ)
    (hQ : MvPolynomial.IsWeightedHomogeneous (Prod.snd : ι × ℕ → ℕ) Q d) (hd : d ≠ n) :
    chernTop Q G v = 0 := by
  have h : (aeval (fun x : ι × ℕ => chernPoly (fun u => G u x.1) v x.2) Q).IsHomogeneous d :=
    aeval_isWeightedHomogeneous hQ _ fun x => chernPoly_isHomogeneous _ _ _
  rw [chernTop, topCoeff_eq_zero h hd, Complex.zero_re, mul_zero]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernPolyTopDensityEqZeroOfWeightedDegreeNeDimStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernPolyTopDensity_eq_zero_of_weightedDegree_ne_dim : ∀ (n : ℕ) (ι : Type) (m : ι → ℕ) (G : ReciprocityTheory.L2DbarEstimates.V n → FlagBundle.Mat m ℂ) (v : ReciprocityTheory.L2DbarEstimates.V n) (Q : MvPolynomial (ι × ℕ) ℝ) (d : ℕ), MvPolynomial.IsWeightedHomogeneous (Prod.snd : ι × ℕ → ℕ) Q d → d ≠ n → chernTop Q G v = 0 := by
  first | exact @GlobalTheory.GoodMetric.chernTop_eq_zero_of_weightedHomogeneous | exact GlobalTheory.GoodMetric.chernTop_eq_zero_of_weightedHomogeneous | (intros; apply GlobalTheory.GoodMetric.chernTop_eq_zero_of_weightedHomogeneous <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolyhedralPolarisationFaceCutIsCell
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolyhedralPolarisationFaceCutIsCell
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.CarDim

namespace GlobalTheory.PolFan.FaceCutCell

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {ψ : InvFun (𝓞 E)}
  {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X]


omit [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] in
theorem apply_eq_sum_of_toReal {m : ℕ} {β : LinearMap.BilinForm ℤ X} {u : Fin m → LinearMap.BilinForm ℤ X}
    {c : Fin m → ℝ} (hβ : toReal β = ∑ i, c i • toReal (u i)) (F : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) :
    (F β : ℝ) = ∑ i, c i * (F (u i) : ℝ) := by
  have h := sum_mul_eq_zero_of_sum_toReal (j := LinearMap.id) Function.injective_id F
    (β := Fin.cons β u) (c := Fin.cons (-1) c) (by
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, LinearMap.id_apply, neg_smul, one_smul, hβ, neg_add_cancel])
  rw [Fin.sum_univ_succ] at h
  simp only [Fin.cons_zero, Fin.cons_succ] at h
  linarith

theorem est_at {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} {N : ℕ} {ℓ h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ}
    (hstr : ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → N * ψ.evalZ β = ℓ β →
      ∃ (k : ℕ) (c : Fin m → ℕ), 0 < k ∧ k • β = ∑ i, c i • γ i)
    (hle : ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → N * ψ.evalZ β ≤ ℓ β)
    (hγ : ∀ j, 0 ≤ h (γ j)) {C : ℕ} (hC : ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → -(h β : ℝ) ≤ C * ℓ β)
    {u : LinearMap.BilinForm ℤ X} (hu : u ∈ balForms H.bar X) (hp : ∀ y, 0 ≤ u y y) (n : ℤ) (hn : ψ.evalZ u = n)
    {B0 L : ℝ} (hb : N * ψ.evalZ u ≤ B0) (hB0 : 0 ≤ B0) (hL : C * (B0 + 1) + C ≤ L) :
    L * (N * ψ.evalZ u) ≤ L * ℓ u + h u := by
  by_cases he : (N : ℝ) * ψ.evalZ u = ℓ u
  · obtain ⟨k, c, hk, hc⟩ := hstr u hu hp he
    have e3 : h (k • u) = ∑ i, (c i : ℤ) * h (γ i) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hc, map_sum]; simp only [map_nsmul, nsmul_eq_mul]
    have h2 : 0 ≤ ∑ i, (c i : ℤ) * h (γ i) := Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (hγ i)
    rw [← e3, map_nsmul, nsmul_eq_mul] at h2
    have h3 : 0 ≤ h u := by
      by_contra hneg
      push_neg at hneg
      have : (k : ℤ) * h u < 0 := mul_neg_of_pos_of_neg (by exact_mod_cast hk) hneg
      linarith
    have h4 : (0 : ℝ) ≤ h u := by exact_mod_cast h3
    rw [he]
    linarith
  · have hlt : (N : ℝ) * ψ.evalZ u < ℓ u := lt_of_le_of_ne (hle u hu hp) he
    rw [hn] at hlt hb ⊢
    have h1 : (N : ℤ) * n < ℓ u := by exact_mod_cast hlt
    have h2 : ((N : ℤ) * n + 1 : ℤ) ≤ ℓ u := h1
    have h3 : (N : ℝ) * n + 1 ≤ ℓ u := by exact_mod_cast h2
    have h5 := hC u hu hp
    have hC0 : (0 : ℝ) ≤ C := Nat.cast_nonneg _
    have hLC : (0 : ℝ) ≤ L - C := by nlinarith [mul_nonneg hC0 hB0]
    nlinarith [mul_nonneg hLC (show (0 : ℝ) ≤ ℓ u - N * n - 1 by linarith),
      mul_nonneg hC0 (show (0 : ℝ) ≤ B0 - N * n by linarith), mul_nonneg hC0 hB0]

theorem isCell_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ψ : InvFun (𝓞 E)) (X : Type)
    [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X], IsPolyFanOn H.bar ψ X → Dominates H.bar X →
    ∀ (m m' : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ),
    IsCell H.bar ψ γ → IsFaceCut γ s h → IsCell H.bar ψ (fun i => γ (s i)) := by
  intro E _ _ _ H ψ X _ _ _ hP hD m m' γ s h hγ hf
  refine ⟨fun i => hγ.mem _, fun i y => hγ.nonneg _ y, linearOn_comp hγ.linear s, ?_⟩
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hγ.strict
  have hpos : ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → β ≠ 0 → 0 < ℓ β := fun β hβ hp h0 => by
    have e1 := h2 β hβ hp
    have e2 := hP.pos β hβ hp h0
    have e3 : (0 : ℝ) < ℓ β := lt_of_lt_of_le (mul_pos (by exact_mod_cast hN) e2) e1
    exact_mod_cast e3
  obtain ⟨C, hC⟩ := hD ℓ (-h) hpos
  have hC' : ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → -(h β : ℝ) ≤ C * ℓ β := fun β hβ hp => by
    have e1 := hC β hβ hp
    simp only [LinearMap.neg_apply] at e1
    exact_mod_cast e1
  obtain ⟨S, hS, hcov⟩ := hP.finite
  obtain ⟨B1, hB1⟩ := (hS.image fun τ => (N : ℝ) * ψ.evalZ τ).bddAbove
  set B0 := max B1 0 with hB0def
  have hB0nn : (0 : ℝ) ≤ B0 := le_max_right _ _
  have hB0 : ∀ τ ∈ S, (N : ℝ) * ψ.evalZ τ ≤ B0 := fun τ hτ => (hB1 ⟨τ, hτ, rfl⟩).trans (le_max_left _ _)
  have est : ∀ L : ℝ, C * (B0 + 1) + C ≤ L → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) →
      L * (N * ψ.evalZ β) ≤ L * ℓ β + h β := by
    intro L hL β hβ hp
    have hmem : toReal β ∈ psdCone (bar := H.bar) (X := X) := by
      have e1 := ConeSub.sum_smul_toReal_mem_psdCone (𝓞 E) H.bar X 1 ![β] ![1]
        (fun i => by fin_cases i; simpa using hβ) (fun i y => by fin_cases i; simpa using hp y)
        (fun i => by fin_cases i; simp)
      simpa using e1
    obtain ⟨e, k, τ, c, hτ, hτS, hc, hdec⟩ := hcov _ hmem
    let u : Fin k → LinearMap.BilinForm ℤ X := fun i => pull e.symm.toLinearMap (τ i)
    have hu : IsCell H.bar ψ u := isCell_pull_equiv hτ e.symm
    have hβu : toReal β = ∑ i, c i • toReal (u i) := LinearMap.ext₂ fun a b => by
      have e1 := LinearMap.congr_fun₂ hdec (e.symm a) (e.symm b)
      simpa [u, LinearMap.sum_apply] using e1
    have hψ : ψ.evalZ β = ∑ i, c i * ψ.evalZ (u i) := by
      rw [← evalR_toReal, hβu]
      exact (linearOn_iff ψ u).1 hu.linear c hc
    have hℓ := apply_eq_sum_of_toReal hβu ℓ
    have hh := apply_eq_sum_of_toReal hβu h
    have hterm : ∀ i, L * (N * ψ.evalZ (u i)) ≤ L * ℓ (u i) + h (u i) := fun i => by
      obtain ⟨n, hn⟩ := hP.integral _ (hu.mem i) (hu.nonneg i)
      refine est_at h3 h2 hf.1 hC' (hu.mem i) (hu.nonneg i) n hn ?_ hB0nn hL
      rw [show ψ.evalZ (u i) = ψ.evalZ (τ i) from evalZ_pull ψ e.symm.surjective _]
      exact hB0 _ (hτS i)
    rw [hψ, hℓ, hh]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have e1 := mul_le_mul_of_nonneg_left (hterm i) (hc i)
    convert e1 using 1 <;> ring
  obtain ⟨K, hK⟩ := exists_nat_ge (C * (B0 + 1) + C + 1 : ℝ)
  have hK1 : C * (B0 + 1) + C ≤ (K : ℝ) - 1 := by linarith
  have hK0 : C * (B0 + 1) + C ≤ (K : ℝ) := by linarith
  have hCB : (0 : ℝ) ≤ C * (B0 + 1) + C :=
    add_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) (Nat.cast_nonneg _)
  have hKpos : 0 < K := by exact_mod_cast (show (0 : ℝ) < K by linarith)
  refine ⟨K * N, (K : ℤ) • ℓ + h, Nat.mul_pos hKpos hN, fun i => ?_, fun β hβ hp => ?_, fun β hβ hp he => ?_⟩
  · have h0 : h (γ (s i)) = 0 := (hf.2 _).2 ⟨i, rfl⟩
    simp only [LinearMap.add_apply, LinearMap.smul_apply, h0, add_zero, smul_eq_mul]
    push_cast
    rw [h1]
    ring
  · have e1 := est K hK0 β hβ hp
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    push_cast
    linarith
  · simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at he
    push_cast at he
    have e1 := est (K - 1) hK1 β hβ hp
    have e2 := h2 β hβ hp
    have heq : (N : ℝ) * ψ.evalZ β = ℓ β := by nlinarith
    obtain ⟨k, c, hk, hc⟩ := h3 β hβ hp heq
    have hh0 : h β = 0 := by
      have e4 : (h β : ℝ) = 0 := by nlinarith
      exact_mod_cast e4
    have e3 : h (k • β) = ∑ i, (c i : ℤ) * h (γ i) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hc, map_sum]; simp only [map_nsmul, nsmul_eq_mul]
    have hsum : ∑ i, (c i : ℤ) * h (γ i) = 0 := by
      rw [← e3, map_nsmul, hh0, smul_zero]
    have hz : ∀ j, (c j : ℤ) * h (γ j) = 0 := fun j =>
      (Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (hf.1 i)).1 hsum j
        (Finset.mem_univ _)
    refine ⟨k, fun i => c (s i), hk, hc.trans ?_⟩
    refine (Fintype.sum_of_injective s s.injective _ _ (fun j hj => ?_) fun i => rfl).symm
    have hne : h (γ j) ≠ 0 := fun h0 => hj ((hf.2 j).1 h0)
    have hcj : c j = 0 := by
      rcases mul_eq_zero.1 (hz j) with h' | h'
      · exact_mod_cast h'
      · exact absurd h' hne
    simp [hcj]

end GlobalTheory.PolFan.FaceCutCell
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolyhedralPolarisationFaceCutIsCellStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.CarDim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polyhedralPolarisation_face_cut_isCell : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ψ : InvFun (𝓞 E)) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X], IsPolyFanOn H.bar ψ X → Dominates H.bar X → ∀ (m m' : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsCell H.bar ψ γ → IsFaceCut γ s h → IsCell H.bar ψ (fun i => γ (s i)) := by
  first | exact @GlobalTheory.PolFan.FaceCutCell.isCell_comp | exact GlobalTheory.PolFan.FaceCutCell.isCell_comp | (intros; apply GlobalTheory.PolFan.FaceCutCell.isCell_comp <;> assumption)
end
end
