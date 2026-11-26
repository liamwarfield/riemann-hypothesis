module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfToRealRel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAdmissibleFanOfCellMultOneCMField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitTauCoordinateAddNsmulFirstVariable

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NatCardTorsionQuotSpanDvdOfRangeSubset
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory

theorem natCard_torsion_quot_span_dvd_of_range_subset :
    ∀ (L : Type) [AddCommGroup L] {m n : ℕ} (δ : Fin m → L) (γ : Fin n → L), LinearIndependent ℤ δ →
    Set.range γ ⊆ Set.range δ →
    Nat.card (Submodule.torsion ℤ (L ⧸ Submodule.span ℤ (Set.range γ))) ∣
      Nat.card (Submodule.torsion ℤ (L ⧸ Submodule.span ℤ (Set.range δ))) := by
  intro L _ m n δ γ hli hsub
  have hAB : Submodule.span ℤ (Set.range γ) ≤ Submodule.span ℤ (Set.range δ) :=
    Submodule.span_mono hsub
  have key : ∀ z : L, z ∈ Submodule.span ℤ (Set.range δ) → ∀ a : ℤ, a ≠ 0 →
      a • z ∈ Submodule.span ℤ (Set.range γ) → z ∈ Submodule.span ℤ (Set.range γ) := by
    intro z hz a ha haz
    have himg : δ '' (δ ⁻¹' Set.range γ) = Set.range γ := Set.image_preimage_eq_of_subset hsub
    rw [← himg] at haz ⊢
    rw [Finsupp.mem_span_image_iff_linearCombination] at haz ⊢
    obtain ⟨l', hl'S, hl'⟩ := haz
    rw [Finsupp.mem_span_range_iff_exists_finsupp] at hz
    obtain ⟨c, hc⟩ := hz
    have hlc : Finsupp.linearCombination ℤ δ c = z := by
      rw [Finsupp.linearCombination_apply]; exact hc
    have heq : a • c = l' := by
      apply hli
      rw [map_smul, hlc, hl']
    refine ⟨c, ?_, hlc⟩
    rw [Finsupp.mem_supported'] at hl'S ⊢
    intro i hi
    have := hl'S i hi
    rw [← heq, Finsupp.smul_apply, smul_eq_mul] at this
    exact (mul_eq_zero.mp this).resolve_left ha
  let q : (L ⧸ Submodule.span ℤ (Set.range γ)) →ₗ[ℤ] (L ⧸ Submodule.span ℤ (Set.range δ)) :=
    Submodule.factor hAB
  let f : Submodule.torsion ℤ (L ⧸ Submodule.span ℤ (Set.range γ)) →+
      Submodule.torsion ℤ (L ⧸ Submodule.span ℤ (Set.range δ)) :=
    (q.restrict (p := Submodule.torsion ℤ _) (q := Submodule.torsion ℤ _) (fun x hx => by
      rw [Submodule.mem_torsion_iff] at hx ⊢
      obtain ⟨a, ha⟩ := hx
      exact ⟨a, by rw [Submonoid.smul_def] at ha ⊢; rw [← map_smul, ha, map_zero]⟩)).toAddMonoidHom
  have hinj : Function.Injective f := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    rintro ⟨x, hx⟩ hfx
    have hqx : q x = 0 := congrArg Subtype.val hfx
    apply Subtype.ext
    simp only [ZeroMemClass.coe_zero]
    induction x using Submodule.Quotient.induction_on with
    | H z =>
      rw [Submodule.mem_torsion_iff] at hx
      obtain ⟨⟨a, ha0⟩, ha⟩ := hx
      have hz : z ∈ Submodule.span ℤ (Set.range δ) := by
        rw [← Submodule.Quotient.mk_eq_zero]
        simpa [q] using hqx
      have ha' : a ≠ 0 := nonZeroDivisors.ne_zero ha0
      have haz : a • z ∈ Submodule.span ℤ (Set.range γ) := by
        rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
        simpa [Submonoid.smul_def] using ha
      rw [Submodule.Quotient.mk_eq_zero]
      exact key z hz a ha' haz
  exact AddSubgroup.card_dvd_of_injective f hinj

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntLinearFormCuttingSubcell
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntLinearFormCuttingSubcell
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem apply_eq_of_inRCone_cell {O : Type} [CommRing O] {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] {m : ℕ} {G : Fin m → LinearMap.BilinForm ℤ X} (hlin : φ.LinearOn G) {N : ℕ}
    {ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ} (h1 : ∀ i, (ℓ (G i) : ℝ) = N * φ.evalZ (G i))
    {β : LinearMap.BilinForm ℤ X} (hβ : InRCone G β) : (ℓ β : ℝ) = N * φ.evalZ β := by
  obtain ⟨c, hc, e⟩ := hβ
  rw [apply_eq_of_toReal_eq e ℓ, ← evalR_toReal, e, (linearOn_iff φ G).1 hlin c hc, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [h1 i]; ring

theorem inRCone_of_nat_rel {X : Type} [AddCommGroup X] {n : ℕ} {δ : Fin n → LinearMap.BilinForm ℤ X}
    {β : LinearMap.BilinForm ℤ X} {k : ℕ} {c : Fin n → ℕ} (hk : 0 < k) (h : k • β = ∑ i, c i • δ i) : InRCone δ β := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  refine ⟨fun i => (c i : ℝ) / k, fun i => by positivity, LinearMap.ext₂ fun a b => ?_⟩
  have h1 : (k : ℤ) * β a b = ∑ i, (c i : ℤ) * δ i a b := by
    simpa [LinearMap.sum_apply] using LinearMap.congr_fun₂ h a b
  have h2 : (k : ℝ) * (β a b : ℝ) = ∑ i, (c i : ℝ) * (δ i a b : ℝ) := by exact_mod_cast h1
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, smul_eq_mul]
  rw [show (β a b : ℝ) = (∑ i, (c i : ℝ) * (δ i a b : ℝ)) / k from by rw [← h2]; field_simp, Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem exists_cut_of_cell_le : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (X : Type) [AddCommGroup X] [Module O X]
    [Module.Finite O X] (m n : ℕ) (G : Fin m → LinearMap.BilinForm ℤ X) (δ : Fin n → LinearMap.BilinForm ℤ X),
    IsCell bar φ G → IsCell bar φ δ → (∀ k, InRCone G (δ k)) → ∃ h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ,
      (∀ j, 0 ≤ h (G j)) ∧ (∀ k, h (δ k) = 0) ∧
      ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone G β → h β = 0 → InRCone δ β := by
  intro O _ bar φ X _ _ _ m n G δ hG hδ hin
  obtain ⟨NG, ℓG, hNG, g1, -, -⟩ := hG.strict
  obtain ⟨Nδ, ℓδ, hNδ, d1, d2, d3⟩ := hδ.strict
  have hNG' : (0 : ℝ) < NG := by exact_mod_cast hNG
  have key : ∀ β : LinearMap.BilinForm ℤ X, InRCone G β → (ℓG β : ℝ) = NG * φ.evalZ β :=
    fun β hβ => apply_eq_of_inRCone_cell hG.linear g1 hβ
  have hval : ∀ β : LinearMap.BilinForm ℤ X, (((((NG : ℤ) • ℓδ - (Nδ : ℤ) • ℓG) β : ℤ)) : ℝ) = NG * ℓδ β - Nδ * ℓG β :=
    fun β => by simp
  refine ⟨(NG : ℤ) • ℓδ - (Nδ : ℤ) • ℓG, fun j => ?_, fun k => ?_, fun β hβ hp hc h0 => ?_⟩
  · have h1 : (0 : ℝ) ≤ (((((NG : ℤ) • ℓδ - (Nδ : ℤ) • ℓG) (G j) : ℤ)) : ℝ) := by
      rw [hval, g1 j]
      have := d2 (G j) (hG.mem j) (hG.nonneg j)
      nlinarith
    exact_mod_cast h1
  · have h1 : (((((NG : ℤ) • ℓδ - (Nδ : ℤ) • ℓG) (δ k) : ℤ)) : ℝ) = 0 := by
      rw [hval, key _ (hin k), d1 k]; ring
    exact_mod_cast h1
  · have h1 := hval β
    rw [h0, key β hc] at h1
    have h2 : (Nδ : ℝ) * φ.evalZ β = ℓδ β := by
      have : (NG : ℝ) * ((Nδ : ℝ) * φ.evalZ β - ℓδ β) = 0 := by push_cast at h1; linarith
      have := (mul_eq_zero.1 this).resolve_left hNG'.ne'
      linarith
    obtain ⟨k, c, hk, e⟩ := d3 β hβ hp h2
    exact inRCone_of_nat_rel hk e

end GlobalTheory.PolFan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntLinearFormCuttingSubcellStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_intLinearForm_cutting_subcell : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (m n : ℕ) (G : Fin m → LinearMap.BilinForm ℤ X) (δ : Fin n → LinearMap.BilinForm ℤ X), IsCell bar φ G → IsCell bar φ δ → (∀ k, InRCone G (δ k)) → ∃ h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ, (∀ j, 0 ≤ h (G j)) ∧ (∀ k, h (δ k) = 0) ∧ ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone G β → h β = 0 → InRCone δ β := by
  first | exact @GlobalTheory.PolFan.exists_cut_of_cell_le | exact GlobalTheory.PolFan.exists_cut_of_cell_le | (intros; apply GlobalTheory.PolFan.exists_cut_of_cell_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLinFormCutFaceOfFaceOfCone
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLinFormCutFaceOfFaceOfCone
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem exists_linForm_cut_face_of_face : ∀ {O : Type} [CommRing O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X] {m n p : ℕ}
    (δ : Fin m → LinearMap.BilinForm ℤ X) (γ : Fin n → LinearMap.BilinForm ℤ X) (γ' : Fin p → LinearMap.BilinForm ℤ X)
    (h₂ h₁ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ),
    (∀ i, δ i ∈ balForms bar X) → (∀ i y, 0 ≤ δ i y y) → (∀ j, InRCone γ (γ' j)) →
    (∀ i, 0 ≤ h₂ (δ i)) → (∀ k, h₂ (γ k) = 0) →
    (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone δ β → h₂ β = 0 → InRCone γ β) →
    (∀ k, 0 ≤ h₁ (γ k)) → (∀ j, h₁ (γ' j) = 0) →
    (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → h₁ β = 0 → InRCone γ' β) →
    ∃ h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ, (∀ i, 0 ≤ h (δ i)) ∧ (∀ j, h (γ' j) = 0) ∧
      ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone δ β → h β = 0 → InRCone γ' β := by
  intro O _ bar X _ _ m n p δ γ γ' h₂ h₁ hδb hδp hγ' h2δ h2γ hf2 h1γ h1γ' hf1
  set K : ℤ := 1 + ∑ i, |h₁ (δ i)| with hK
  have hKi : ∀ i, |h₁ (δ i)| < K := fun i => by
    have := Finset.single_le_sum (f := fun i => |h₁ (δ i)|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)
    linarith
  have hK0 : 0 ≤ K := by
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => abs_nonneg (h₁ (δ i)))
    linarith
  have happ : ∀ x, (K • h₂ + h₁) x = K * h₂ x + h₁ x := fun x => by simp
  have hpos : ∀ i, 0 < h₂ (δ i) → 0 < (K • h₂ + h₁) (δ i) := fun i hi => by
    rw [happ]
    have h1 : K ≤ K * h₂ (δ i) := by nlinarith
    have := neg_abs_le (h₁ (δ i))
    linarith [hKi i]
  have hnn : ∀ i, 0 ≤ (K • h₂ + h₁) (δ i) := fun i => by
    rcases (h2δ i).lt_or_eq with hi | hi
    · exact (hpos i hi).le
    · rw [happ, ← hi, mul_zero, zero_add]
      exact InRCone.apply_nonneg (hf2 _ (hδb i) (hδp i) (inRCone_self δ i) hi.symm) h₁ h1γ
  have h2γ' : ∀ j, h₂ (γ' j) = 0 := fun j => le_antisymm (by
      have := InRCone.apply_nonneg (hγ' j) (-h₂) (fun k => by simp [h2γ k])
      simpa using this)
    (InRCone.apply_nonneg (hγ' j) h₂ (fun k => (h2γ k).ge))
  refine ⟨K • h₂ + h₁, hnn, fun j => by rw [happ, h2γ' j, h1γ' j]; ring, ?_⟩
  intro β hb hp hc hz
  have h2β : h₂ β = 0 := by
    obtain ⟨c, hc0, e⟩ := hc
    have eh := apply_eq_of_toReal_eq e (K • h₂ + h₁)
    have e2 := apply_eq_of_toReal_eq e h₂
    rw [hz, Int.cast_zero] at eh
    have hterm : ∀ i ∈ Finset.univ, 0 ≤ c i * ((K • h₂ + h₁) (δ i) : ℝ) := fun i _ =>
      mul_nonneg (hc0 i) (by exact_mod_cast hnn i)
    have hall := (Finset.sum_eq_zero_iff_of_nonneg hterm).1 eh.symm
    have hs : ∑ i, c i * (h₂ (δ i) : ℝ) = 0 := Finset.sum_eq_zero fun i _ => by
      rcases (h2δ i).lt_or_eq with hi | hi
      · have h0 := hall i (Finset.mem_univ _)
        have hp' : (0 : ℝ) < (K • h₂ + h₁) (δ i) := by exact_mod_cast hpos i hi
        rw [(mul_eq_zero.1 h0).resolve_right hp'.ne', zero_mul]
      · rw [← hi]; simp
    exact_mod_cast e2.trans hs
  have hγβ := hf2 β hb hp hc h2β
  refine hf1 β hb hp hγβ ?_
  have := happ β
  rw [hz, h2β] at this
  linarith

end GlobalTheory.PolFan
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLinFormCutFaceOfFaceOfConeStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linForm_cut_face_of_face_of_cone : ∀ {O : Type} [CommRing O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X] {m n p : ℕ}
    (δ : Fin m → LinearMap.BilinForm ℤ X) (γ : Fin n → LinearMap.BilinForm ℤ X) (γ' : Fin p → LinearMap.BilinForm ℤ X)
    (h₂ h₁ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ),
    (∀ i, δ i ∈ balForms bar X) → (∀ i y, 0 ≤ δ i y y) → (∀ j, InRCone γ (γ' j)) →
    (∀ i, 0 ≤ h₂ (δ i)) → (∀ k, h₂ (γ k) = 0) →
    (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone δ β → h₂ β = 0 → InRCone γ β) →
    (∀ k, 0 ≤ h₁ (γ k)) → (∀ j, h₁ (γ' j) = 0) →
    (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → h₁ β = 0 → InRCone γ' β) →
    ∃ h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ, (∀ i, 0 ≤ h (δ i)) ∧ (∀ j, h (γ' j) = 0) ∧
      ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone δ β → h β = 0 → InRCone γ' β := by
  first | exact @GlobalTheory.PolFan.exists_linForm_cut_face_of_face | exact GlobalTheory.PolFan.exists_linForm_cut_face_of_face | (intros; apply GlobalTheory.PolFan.exists_linForm_cut_face_of_face <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicFrameFamilyChartCoordinatesHolomorphi
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicFrameFamilyChartCoordinatesHolomorphi
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open scoped ComplexOrder Topology
open ReciprocityTheory.L2DbarEstimates (V)
open ReciprocityTheory.ChartRestriction.G.FD (Frame mat)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieBase

theorem isHol_chart_framePt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (X : Var F) (j : X.X ⟶ gen T.Z), IsOpenImmersion j → ∀ (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), ∀ (c' : AlgChart X.str (σ.comp e.toRingHom) X.dim) (k : U.Comp) (n : ℕ) (W : Set (V n)) (ψ : V n → Frame (U.X k).Ψ (Dw.p + Dw.q)), IsOpen W → (∀ w ∈ W, ψ w ∈ (U.X k).dom) → (∀ τ i i', DifferentiableOn ℂ (fun w => mat (ψ w) τ i i') W) → ∃ q : V n → CxPts X.str (σ.comp e.toRingHom), IsOpen {w | w ∈ W ∧ ∃ h : ψ w ∈ (U.X k).dom, ∃ y' ∈ c'.e.source, cxOf e σ hj y' = cxPt T.Z (U.un k ⟨ψ w, h⟩)} ∧ (∀ w ∈ W, ∀ h : ψ w ∈ (U.X k).dom, (∃ y' ∈ c'.e.source, cxOf e σ hj y' = cxPt T.Z (U.un k ⟨ψ w, h⟩)) → q w ∈ c'.e.source ∧ cxOf e σ hj (q w) = cxPt T.Z (U.un k ⟨ψ w, h⟩)) ∧ DifferentiableOn ℂ (fun w => c'.e (q w)) {w | w ∈ W ∧ ∃ h : ψ w ∈ (U.X k).dom, ∃ y' ∈ c'.e.source, cxOf e σ hj y' = cxPt T.Z (U.un k ⟨ψ w, h⟩)} := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U _hσ hU X j hji hj c' k n W ψ hW hψW hψd
  classical
  haveI := hji
  have hU' : Formalism.L2.Pj.IsUnf U.toPj := (Formalism.L2.PjFree.isUnf_ofPj U.toPj).1 hU
  by_cases hne : ((U.X k).dom).Nonempty
  · obtain ⟨x₀, hx₀⟩ := hne
    let sf : Frame (U.X k).Ψ (Dw.p + Dw.q) → (U.X k).dom := fun x =>
      if h : x ∈ (U.X k).dom then ⟨x, h⟩ else ⟨x₀, hx₀⟩
    have hsf : ∀ x (h : x ∈ (U.X k).dom), sf x = ⟨x, h⟩ := fun x h => dif_pos h
    have h1 := BdArc.Leave.isHolTo_ptC (U := U.toPj) hU' k sf fun x h => by rw [hsf x h]
    have h2 := LocLift.isHolTo_comp_hom h1 T.Z.jQ
    have hψ : DifferentiableOn ℂ ψ W :=
      differentiableOn_pi.2 fun τ => differentiableOn_pi.2 fun a => differentiableOn_pi.2 fun b => hψd τ a b
    have h3 := LocLift.isHolTo_comp h2 hW hψ hψW
    let P : V n → CxPts (genStr T.Z) σ := fun w => cxPt T.Z (U.un k (sf (ψ w)))
    have h4 : IsHolTo W fun w => (P w).1 := h3
    have hP : ∀ w, ∀ h : ψ w ∈ (U.X k).dom, cxPt T.Z (U.un k ⟨ψ w, h⟩) = P w := fun w h => by
      simp only [P, hsf _ h]
    have hc : ContinuousOn P W := GlobalTheory.TrueCx.TorHolo.continuousOn_of_isHolTo h4
    have hκ : Topology.IsOpenEmbedding (cxOf e σ hj) := isOpenEmbedding_cxOf e σ hj
    have hS : {w | w ∈ W ∧ ∃ h : ψ w ∈ (U.X k).dom, ∃ y' ∈ c'.e.source,
        cxOf e σ hj y' = cxPt T.Z (U.un k ⟨ψ w, h⟩)} = W ∩ P ⁻¹' (cxOf e σ hj '' c'.e.source) := by
      ext w
      constructor
      · rintro ⟨hw, h, y', hy', he⟩
        exact ⟨hw, y', hy', he.trans (hP w h)⟩
      · rintro ⟨hw, y', hy', he⟩
        exact ⟨hw, hψW w hw, y', hy', he.trans (hP w _).symm⟩
    let q : V n → CxPts X.str (σ.comp e.toRingHom) := fun w =>
      if h : ∃ y' ∈ c'.e.source, cxOf e σ hj y' = P w then h.choose else c'.e.symm 0
    have hq : ∀ w, (∃ y' ∈ c'.e.source, cxOf e σ hj y' = P w) →
        q w ∈ c'.e.source ∧ cxOf e σ hj (q w) = P w := fun w h => by
      simp only [q, dif_pos h]
      exact h.choose_spec
    refine ⟨q, ?_, fun w _ h hex => ?_, ?_⟩
    · rw [hS]
      exact hc.isOpen_inter_preimage hW (hκ.isOpenMap _ c'.e.open_source)
    · rw [hP w h] at hex ⊢
      exact hq w hex
    · rw [hS, differentiableOn_euclidean]
      intro a
      have hd := (h4 (j ''ᵁ c'.U) ((j.appIso c'.U).inv.hom (c'.x a))).2
      refine (hd.mono fun w (hw : w ∈ W ∩ P ⁻¹' (cxOf e σ hj '' c'.e.source)) => ⟨hw.1, ?_⟩).congr fun w hw => ?_
      · obtain ⟨hq1, hq2⟩ := hq w (by obtain ⟨y', hy', he⟩ := hw.2; exact ⟨y', hy', he⟩)
        show ⊤ ≤ (P w).1 ⁻¹ᵁ _
        rw [← hq2]
        exact le_preimage_cxOf e σ hj c'.U (c'.source_subset hq1)
      · obtain ⟨hq1, hq2⟩ := hq w (by obtain ⟨y', hy', he⟩ := hw.2; exact ⟨y', hy', he⟩)
        show c'.e (q w) a = valAt' (P w).1 _ _
        rw [c'.apply_eq _ hq1 a, ev_eq_valAt'_cxOf e σ hj _ _ (c'.source_subset hq1), hq2]
  · have hS : {w | w ∈ W ∧ ∃ h : ψ w ∈ (U.X k).dom, ∃ y' ∈ c'.e.source,
        cxOf e σ hj y' = cxPt T.Z (U.un k ⟨ψ w, h⟩)} = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 fun w hw => hne ⟨_, hw.2.1⟩
    refine ⟨fun _ => c'.e.symm 0, ?_, fun w _ h _ => absurd ⟨_, h⟩ hne, ?_⟩
    · rw [hS]
      exact isOpen_empty
    · rw [hS]
      exact differentiableOn_empty

end GlobalTheory.LieBase
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicFrameFamilyChartCoordinatesHolomorphiStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open scoped ComplexOrder Topology
open ReciprocityTheory.L2DbarEstimates (V)
open ReciprocityTheory.ChartRestriction.G.FD (Frame mat)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_frameFamily_chart_coordinates_holomorphic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (X : Var F) (j : X.X ⟶ gen T.Z), IsOpenImmersion j → ∀ (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), ∀ (c' : AlgChart X.str (σ.comp e.toRingHom) X.dim) (k : U.Comp) (n : ℕ) (W : Set (V n)) (ψ : V n → Frame (U.X k).Ψ (Dw.p + Dw.q)), IsOpen W → (∀ w ∈ W, ψ w ∈ (U.X k).dom) → (∀ τ i i', DifferentiableOn ℂ (fun w => mat (ψ w) τ i i') W) → ∃ q : V n → CxPts X.str (σ.comp e.toRingHom), IsOpen {w | w ∈ W ∧ ∃ h : ψ w ∈ (U.X k).dom, ∃ y' ∈ c'.e.source, cxOf e σ hj y' = cxPt T.Z (U.un k ⟨ψ w, h⟩)} ∧ (∀ w ∈ W, ∀ h : ψ w ∈ (U.X k).dom, (∃ y' ∈ c'.e.source, cxOf e σ hj y' = cxPt T.Z (U.un k ⟨ψ w, h⟩)) → q w ∈ c'.e.source ∧ cxOf e σ hj (q w) = cxPt T.Z (U.un k ⟨ψ w, h⟩)) ∧ DifferentiableOn ℂ (fun w => c'.e (q w)) {w | w ∈ W ∧ ∃ h : ψ w ∈ (U.X k).dom, ∃ y' ∈ c'.e.source, cxOf e σ hj y' = cxPt T.Z (U.un k ⟨ψ w, h⟩)} := by
  first | exact @GlobalTheory.LieBase.isHol_chart_framePt | exact GlobalTheory.LieBase.isHol_chart_framePt | (intros; apply GlobalTheory.LieBase.isHol_chart_framePt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCellQuotientByRadicalOfMemCone
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCellQuotientByRadicalOfMemCone
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.CarDim

namespace GlobalTheory.PolFan.CarDim

section Descend

variable {O : Type} [CommRing O] {X : Type} [AddCommGroup X] [Module O X]

theorem exists_pull_mkQ_eq_of_vanish (K : Submodule O X) (f : LinearMap.BilinForm ℤ X)
    (h1 : ∀ x ∈ K, ∀ y, f x y = 0) (h2 : ∀ x, ∀ y ∈ K, f x y = 0) :
    ∃ δ : LinearMap.BilinForm ℤ (X ⧸ K), pull K.mkQ δ = f := by
  let e := Submodule.Quotient.restrictScalarsEquiv ℤ K
  let g := LinearMap.liftQ₂ (K.restrictScalars ℤ) (K.restrictScalars ℤ) f
    (fun x hx => LinearMap.ext fun y => h1 x hx y) (fun y hy => LinearMap.ext fun x => h2 x y hy)
  refine ⟨g.compl₁₂ e.symm.toLinearMap e.symm.toLinearMap, LinearMap.ext₂ fun a b => ?_⟩
  simp [pull_apply, e, g]
  rfl

end Descend

theorem exists_cell_quot_orad_of_inRCone : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ψ : InvFun (𝓞 E))
    (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X],
    (∀ (m m' : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ),
      IsCell H.bar ψ γ → IsFaceCut γ s h → IsCell H.bar ψ (fun i => γ (s i))) →
    ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ →
      InRCone γ β → ∃ (m' : ℕ) (δ : Fin m' → LinearMap.BilinForm ℤ (X ⧸ (orad β : Submodule (𝓞 E) X))),
        IsCell H.bar ψ δ ∧ InRCone (fun i => pull (orad β : Submodule (𝓞 E) X).mkQ (δ i)) β ∧ genRank δ ≤ genRank γ := by
  intro E _ _ _ H ψ X _ _ _ hface β hβ hβp m γ hγ hβγ
  classical
  set K : Submodule (𝓞 E) X := orad β with hK
  haveI : Module.Finite ℤ X := Module.Finite.trans (𝓞 E) X
  obtain ⟨T, hT⟩ := (IsNoetherian.noetherian (K.restrictScalars ℤ) : (K.restrictScalars ℤ).FG)
  have hTK : ∀ k ∈ T, k ∈ K := fun k hk => by
    have : k ∈ K.restrictScalars ℤ := hT ▸ Submodule.subset_span hk
    exact this
  let hl : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ := ∑ k ∈ T, LinearMap.applyₗ k ∘ₗ LinearMap.applyₗ k
  have hl_apply : ∀ β', hl β' = ∑ k ∈ T, β' k k := fun β' => by simp [hl]
  have hsym : ∀ i y z, γ i y z = γ i z y := fun i => (hγ.mem i).1
  have hvan : ∀ i, hl (γ i) = 0 ↔ ∀ x ∈ K, ∀ y, γ i x y = 0 := by
    intro i
    rw [hl_apply]
    constructor
    · intro h0
      have hkk : ∀ k ∈ T, γ i k k = 0 := (Finset.sum_eq_zero_iff_of_nonneg fun k _ => hγ.nonneg i k).1 h0
      have hle : K.restrictScalars ℤ ≤ LinearMap.ker (γ i) := by
        rw [← hT, Submodule.span_le]
        intro k hk
        exact LinearMap.ext fun w => ConeSub.eq_zero_of_self_eq_zero (γ i) (hsym i) (hγ.nonneg i) (hkk k hk) w
      intro x hx y
      have := hle hx
      rw [LinearMap.mem_ker] at this
      rw [this]; rfl
    · intro h0
      exact Finset.sum_eq_zero fun k hk => h0 k (hTK k hk) k
  have hnn : ∀ i, 0 ≤ hl (γ i) := fun i => by
    rw [hl_apply]; exact Finset.sum_nonneg fun k _ => hγ.nonneg i k
  set S : Finset (Fin m) := Finset.univ.filter fun i => hl (γ i) = 0 with hS
  let s : Fin S.card ↪ Fin m := (S.orderEmbOfFin rfl).toEmbedding
  have hs : Set.range s = ↑S := Finset.range_orderEmbOfFin S rfl
  have hcut : IsFaceCut γ s hl := ⟨hnn, fun j => by
    rw [hs]; simp [hS]⟩
  have hcell := hface m S.card γ s hl hγ hcut
  have hdesc : ∀ i : Fin S.card, ∃ δ : LinearMap.BilinForm ℤ (X ⧸ K), pull K.mkQ δ = γ (s i) := by
    intro i
    have hi : hl (γ (s i)) = 0 := by
      have : s i ∈ (S : Set (Fin m)) := hs ▸ Set.mem_range_self i
      simpa [hS] using this
    have h1 := (hvan (s i)).1 hi
    exact exists_pull_mkQ_eq_of_vanish K _ h1 fun x y hy => by rw [hsym]; exact h1 y hy x
  choose δ hδ using hdesc
  have hδ' : (fun i => pull K.mkQ (δ i)) = fun i => γ (s i) := funext hδ
  have hsurj : Function.Surjective K.mkQ := K.mkQ_surjective
  refine ⟨S.card, δ, ?_, ?_, ?_⟩
  · refine ⟨fun i => ?_, fun i y => ?_, ?_, ?_⟩
    · have hm := hcell.mem i
      rw [← hδ i] at hm
      refine ⟨fun y z => ?_, fun a y z => ?_⟩
      · obtain ⟨y, rfl⟩ := hsurj y
        obtain ⟨z, rfl⟩ := hsurj z
        exact hm.1 y z
      · obtain ⟨y, rfl⟩ := hsurj y
        obtain ⟨z, rfl⟩ := hsurj z
        have := hm.2 a y z
        simpa [pull_apply, map_smul] using this
    · obtain ⟨y, rfl⟩ := hsurj y
      have := hcell.nonneg i y
      rw [← hδ i] at this
      exact this
    · rw [← linearOn_pull_iff hsurj, hδ']
      exact hcell.linear
    · apply IsStrict.of_pull hsurj
      rw [hδ']
      exact hcell.strict
  · rw [hδ']
    obtain ⟨c, hc0, hc⟩ := hβγ
    have hzero : ∀ j, j ∉ S → c j = 0 := by
      intro j hj
      have hj' : hl (γ j) ≠ 0 := by simpa [hS] using hj
      rw [hl_apply] at hj'
      obtain ⟨k, hkT, hk0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hj'
      have hk := LinearMap.congr_fun₂ hc k k
      simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at hk
      have hb : β k k = 0 := by
        have := (mem_orad.1 (hTK k hkT)) 1 k
        simpa using this
      rw [hb, Int.cast_zero] at hk
      have hall := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
        mul_nonneg (hc0 i) (Int.cast_nonneg (hγ.nonneg i k))).1 hk.symm j (Finset.mem_univ _)
      rcases mul_eq_zero.1 hall with h | h
      · exact h
      · exact absurd (Int.cast_eq_zero.1 h) hk0
    refine ⟨fun i => c (s i), fun i => hc0 _, ?_⟩
    rw [hc]
    exact (Fintype.sum_of_injective s s.injective (fun i => c (s i) • toReal (γ (s i))) (fun j => c j • toReal (γ j))
      (fun j hj => by
        rw [hzero j (by rw [hs] at hj; simpa using hj), zero_smul]) (fun i => rfl)).symm
  · rw [← genRank_pull hsurj δ, hδ']
    unfold genRank
    haveI : Module.Finite ℤ (Submodule.span ℤ (Set.range γ)) := Module.Finite.span_of_finite ℤ (Set.finite_range γ)
    exact Submodule.finrank_mono (Submodule.span_mono (Set.range_comp_subset_range s γ))

end GlobalTheory.PolFan.CarDim
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCellQuotientByRadicalOfMemConeStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.CarDim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cell_quotient_by_radical_of_mem_cone : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ψ : InvFun (𝓞 E)) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X], (∀ (m m' : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsCell H.bar ψ γ → IsFaceCut γ s h → IsCell H.bar ψ (fun i => γ (s i))) → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ → InRCone γ β → ∃ (m' : ℕ) (δ : Fin m' → LinearMap.BilinForm ℤ (X ⧸ (orad β : Submodule (𝓞 E) X))), IsCell H.bar ψ δ ∧ InRCone (fun i => pull (orad β : Submodule (𝓞 E) X).mkQ (δ i)) β ∧ genRank δ ≤ genRank γ := by
  first | exact @GlobalTheory.PolFan.CarDim.exists_cell_quot_orad_of_inRCone | exact GlobalTheory.PolFan.CarDim.exists_cell_quot_orad_of_inRCone | (intros; apply GlobalTheory.PolFan.CarDim.exists_cell_quot_orad_of_inRCone <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionDepthHostFixingAutInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionDepthHostFixingAutInvariant
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolFan

section Transfer

variable {O : Type} [CommRing O] (bar : O → O) {X : Type} [AddCommGroup X]

theorem isCell_transfer {φ : InvFun O} (m1 m2 : Module O X) (f1 : letI := m1; Module.Finite O X)
    (f2 : letI := m2; Module.Finite O X)
    (hbal : ∀ β, β ∈ (letI := m1; balForms bar X) ↔ β ∈ (letI := m2; balForms bar X))
    (hφ : ∀ B : X → X → ℝ, (letI := m1; letI := f1; φ.eval X B) = (letI := m2; letI := f2; φ.eval X B))
    {k : ℕ} {γ : Fin k → LinearMap.BilinForm ℤ X} (h : letI := m1; letI := f1; IsCell bar φ γ) :
    letI := m2; letI := f2; IsCell bar φ γ := by
  obtain ⟨hm, hn, hl, hs⟩ := h
  have hZ : ∀ β : LinearMap.BilinForm ℤ X, (letI := m1; letI := f1; φ.evalZ β) = (letI := m2; letI := f2; φ.evalZ β) :=
    fun β => hφ _
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hs
  letI := m2
  letI := f2
  refine ⟨fun i => (hbal _).1 (hm i), hn, fun c hc => ?_, N, ℓ, hN, fun i => ?_, fun β hβ hp => ?_, fun β hβ hp he => ?_⟩
  · rw [← hφ]
    simp only [← hZ]
    exact hl c hc
  · rw [← hZ]; exact h1 i
  · rw [← hZ]; exact h2 β ((hbal β).2 hβ) hp
  · exact h3 β ((hbal β).2 hβ) hp (by rw [hZ]; exact he)

theorem isStarDepth_transfer {ψ w : InvFun O} (m1 m2 : Module O X) (f1 : letI := m1; Module.Finite O X)
    (f2 : letI := m2; Module.Finite O X)
    (hbal : ∀ β, β ∈ (letI := m1; balForms bar X) ↔ β ∈ (letI := m2; balForms bar X))
    (hψ : ∀ B : X → X → ℝ, (letI := m1; letI := f1; ψ.eval X B) = (letI := m2; letI := f2; ψ.eval X B))
    (hw : ∀ B : X → X → ℝ, (letI := m1; letI := f1; w.eval X B) = (letI := m2; letI := f2; w.eval X B))
    {B₁ : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} {t : ℝ} (h : letI := m1; letI := f1; IsStarDepth bar ψ w B₁ t) :
    letI := m2; letI := f2; IsStarDepth bar ψ w B₁ t := by
  obtain ⟨ht, k, γ, v, hc, hv, hpos, hw1, hin, hB, hBt⟩ := h
  exact ⟨ht, k, γ, v, isCell_transfer bar m1 m2 f1 f2 hbal hψ hc, (hbal v).1 hv, hpos, (hw _).symm.trans hw1, hin, hB,
    hBt⟩

end Transfer

section Twist

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E)

theorem host_bar_map_comm (σ : 𝓞 E ≃+* 𝓞 E) (a : 𝓞 E) : σ (H.bar a) = H.bar (σ a) := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  let s : E ≃+* E := IsFractionRing.ringEquivOfRingEquiv σ
  have hs : ∀ x : 𝓞 E, ((σ x : 𝓞 E) : E) = s x := fun x =>
    (IsFractionRing.ringEquivOfRingEquiv_algebraMap σ x).symm
  apply RingOfIntegers.ext
  apply φ.injective
  rw [H.bar_eq, hs, hs, H.bar_eq, IsCMField.complexEmbedding_complexConj]
  exact IsCMField.complexEmbedding_complexConj E (φ.comp s.toRingHom) _

variable {X : Type} [AddCommGroup X] [Module (𝓞 E) X]

theorem mem_balForms_twist (τ : 𝓞 E ≃+* 𝓞 E) (β : LinearMap.BilinForm ℤ X) :
    β ∈ balForms H.bar X ↔ β ∈ (letI := Module.compHom X τ.toRingHom; balForms H.bar X) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun a y z => ?_⟩
    show β (τ a • y) z = β y (τ (H.bar a) • z)
    rw [h2, host_bar_map_comm]
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun a y z => ?_⟩
    have := h2 (τ.symm a) y z
    change β (τ (τ.symm a) • y) z = β y (τ (H.bar (τ.symm a)) • z) at this
    rwa [host_bar_map_comm, τ.apply_symm_apply] at this

theorem eval_twist_of_isTwInv {φ : InvFun (𝓞 E)} (hφ : IsTwInv H φ) (τ : 𝓞 E ≃+* 𝓞 E) (hτ : τ H.w0 = H.w0)
    [Module.Finite (𝓞 E) X] (hf : letI := Module.compHom X τ.toRingHom; Module.Finite (𝓞 E) X) (B : X → X → ℝ) :
    φ.eval X B = (letI := Module.compHom X τ.toRingHom; letI := hf; φ.eval X B) := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' (𝓞 E) X
  rw [φ.eval_eq hr, ← hφ τ hτ]
  let g : (Fin n → 𝓞 E) →+ X := r.toAddMonoidHom.comp
    ⟨⟨fun a i => τ (a i), by ext; simp⟩, fun a b => by ext; simp⟩
  have hg : ∀ (c : 𝓞 E) a, g (c • a) = τ c • g a := fun c a => by
    change r _ = τ c • r _
    rw [← map_smul]
    congr 1
    ext i
    simp
  have hs : Function.Surjective g := hr.comp fun a => ⟨fun i => τ.symm (a i), funext fun i => τ.apply_symm_apply _⟩
  letI : Module (𝓞 E) X := Module.compHom _ τ.toRingHom
  letI := hf
  exact (φ.eval_eq (r := ⟨g.toAddHom, hg⟩) hs _).symm


omit [Module (𝓞 E) X] in
theorem depthSet_twist_subset {ψ w : InvFun (𝓞 E)} (hψ : IsTwInv H ψ) (hw : IsTwInv H w) (σ : 𝓞 E ≃+* 𝓞 E)
    (hσ : σ H.w0 = H.w0) (n : ℕ) (B : (Fin n → 𝓞 E) → (Fin n → 𝓞 E) → ℝ) :
    depthSet H.bar ψ w n (fun a b => B (fun i => σ (a i)) (fun i => σ (b i))) ⊆ depthSet H.bar ψ w n B := by
  rintro t ⟨X₁, i1, i2, i3, r, B₁, hr, hrad, hB, hd⟩
  set τ := σ.symm with hτdef
  have hτ : τ H.w0 = H.w0 := (σ.symm_apply_eq).2 hσ.symm
  let g : (Fin n → 𝓞 E) →+ X₁ := r.toAddMonoidHom.comp
    ⟨⟨fun a i => τ (a i), by ext; simp⟩, fun a b => by ext; simp⟩
  have hg : ∀ (c : 𝓞 E) a, g (c • a) = τ c • g a := fun c a => by
    change r _ = τ c • r _
    rw [← map_smul]
    congr 1
    ext i
    simp
  have hs : Function.Surjective g := hr.comp fun a => ⟨fun i => σ (a i), funext fun i => σ.symm_apply_apply _⟩
  have hgB : ∀ a b, B a b = B₁ (g a) (g b) := fun a b => by
    have := hB (fun i => τ (a i)) (fun i => τ (b i))
    simp only [hτdef, RingEquiv.apply_symm_apply] at this
    exact this
  have hf' : letI := Module.compHom X₁ τ.toRingHom; Module.Finite (𝓞 E) X₁ := by
    letI := Module.compHom X₁ τ.toRingHom
    exact Module.Finite.of_surjective (⟨g.toAddHom, hg⟩ : (Fin n → 𝓞 E) →ₗ[𝓞 E] X₁) hs
  have hd' := isStarDepth_transfer H.bar i2 (Module.compHom X₁ τ.toRingHom) i3 hf' (mem_balForms_twist H τ)
    (eval_twist_of_isTwInv H hψ τ hτ hf') (eval_twist_of_isTwInv H hw τ hτ hf') hd
  letI := Module.compHom X₁ τ.toRingHom
  exact ⟨X₁, i1, _, hf', ⟨g.toAddHom, hg⟩, B₁, hs, hrad, hgB, hd'⟩

theorem isTwInv_starDepth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ψ w : InvFun (𝓞 E)),
    IsTwInv H ψ → IsTwInv H w → IsTwInv H (starDepth H.bar ψ w) := by
  intro E _ _ _ H ψ w hψ hw σ hσ n B
  show sSup _ = sSup _
  congr 1
  refine Set.Subset.antisymm (depthSet_twist_subset H hψ hw σ hσ n B) ?_
  have h := depthSet_twist_subset H hψ hw σ.symm ((σ.symm_apply_eq).2 hσ.symm) n
    (fun a b => B (fun i => σ (a i)) (fun i => σ (b i)))
  simpa only [RingEquiv.apply_symm_apply] using h

end Twist

end GlobalTheory.PolFan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionDepthHostFixingAutInvariantStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.starSubdivisionDepth_hostFixingAut_invariant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ψ w : InvFun (𝓞 E)), IsTwInv H ψ → IsTwInv H w → IsTwInv H (starDepth H.bar ψ w) := by
  first | exact @GlobalTheory.PolFan.isTwInv_starDepth | exact GlobalTheory.PolFan.isTwInv_starDepth | (intros; apply GlobalTheory.PolFan.isTwInv_starDepth <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqSubfamilyOfFaceSimplicialConePrimitive
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqOfPrimitiveBalancedFormSameRealRay
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqOfPrimitiveBalancedFormSameRealRay
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan.SmoothEnd

theorem eq_of_isPrim_of_toReal_eq_smul : ∀ {O : Type} [CommRing O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X] (x y : LinearMap.BilinForm ℤ X)
    (hx : x ∈ balForms bar X) (hy : y ∈ balForms bar X), IsPrim bar (⟨x, hx⟩ : balForms bar X) →
    IsPrim bar (⟨y, hy⟩ : balForms bar X) → ∀ b : ℝ, 0 < b → toReal x = b • toReal y → x = y := by
  intro O _ bar X _ _ x y hx hy px py b hb h
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact not_isPrim_zero (bar := bar) py
  obtain ⟨a, c, hac⟩ : ∃ a c, y a c ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hy0 (LinearMap.ext₂ hc)
  have hR : ∀ u v, (x u v : ℝ) = b * (y u v : ℝ) := fun u v => by
    have := LinearMap.congr_fun₂ h u v
    simpa [toReal_apply] using this
  have hacR : (y a c : ℝ) ≠ 0 := by exact_mod_cast hac
  have hxac : x a c ≠ 0 := by
    have : (x a c : ℝ) ≠ 0 := by rw [hR]; exact mul_ne_zero hb.ne' hacR
    exact_mod_cast this
  have habs : |(x a c : ℝ)| = b * |(y a c : ℝ)| := by
    rw [hR, abs_mul, abs_of_pos hb]
  apply eq_of_isPrim hx hy px py (k := (y a c).natAbs) (n := (x a c).natAbs)
    (Int.natAbs_pos.2 hac) (Int.natAbs_pos.2 hxac)
  apply LinearMap.ext₂
  intro u v
  simp only [LinearMap.smul_apply, smul_eq_mul, Int.natCast_natAbs]
  have e : |(y a c : ℝ)| * (x u v : ℝ) = |(x a c : ℝ)| * (y u v : ℝ) := by
    rw [hR u v, habs]; ring
  exact_mod_cast e

end GlobalTheory.PolFan.SmoothEnd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqOfPrimitiveBalancedFormSameRealRayStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_primitiveBalancedForm_same_real_ray : ∀ {O : Type} [CommRing O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X] (x y : LinearMap.BilinForm ℤ X)
    (hx : x ∈ balForms bar X) (hy : y ∈ balForms bar X), IsPrim bar (⟨x, hx⟩ : balForms bar X) →
    IsPrim bar (⟨y, hy⟩ : balForms bar X) → ∀ b : ℝ, 0 < b → toReal x = b • toReal y → x = y := by
  first | exact @GlobalTheory.PolFan.SmoothEnd.eq_of_isPrim_of_toReal_eq_smul | exact GlobalTheory.PolFan.SmoothEnd.eq_of_isPrim_of_toReal_eq_smul | (intros; apply GlobalTheory.PolFan.SmoothEnd.eq_of_isPrim_of_toReal_eq_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqSubfamilyOfFaceSimplicialConePrimitive
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

noncomputable section

namespace GlobalTheory.PolFan.FaceSub

variable {X : Type} [AddCommGroup X]

theorem eq_of_toReal_sum_eq {p : ℕ} {u : Fin p → LinearMap.BilinForm ℤ X} (hu : LinearIndependent ℤ u)
    {r r' : Fin p → ℝ} (h : ∑ j, r j • toReal (u j) = ∑ j, r' j • toReal (u j)) : r = r' := by
  have hind : ∀ (d : Fin 0 → ℤ) (c : Fin p → ℤ), ∑ j, c j • u j = ∑ k, d k • (Fin.elim0 k : LinearMap.BilinForm ℤ X) →
      c = 0 := fun d c hc => by
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at hc
    exact funext (Fintype.linearIndependent_iff.1 hu c hc)
  have h0 : ∑ j, (r - r') j • toReal (u j) = ∑ k, (Fin.elim0 k : ℝ) • toReal (Fin.elim0 k : LinearMap.BilinForm ℤ X) := by
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h, sub_self, Finset.univ_eq_empty, Finset.sum_empty]
  exact sub_eq_zero.1 (eq_zero_of_toReal_rel hind h0)

theorem eq_zero_of_toReal_eq_zero {β : LinearMap.BilinForm ℤ X} (h : toReal β = 0) : β = 0 :=
  LinearMap.ext₂ fun a b => by
    have := LinearMap.congr_fun₂ h a b
    simp only [toReal_apply, LinearMap.zero_apply] at this
    simpa using this

theorem exists_ray {p q : ℕ} {u : Fin p → LinearMap.BilinForm ℤ X} {v : Fin q → LinearMap.BilinForm ℤ X}
    (hu : LinearIndependent ℤ u) (hv : ∀ l, v l ≠ 0) (A : Fin q → ℝ) (B : Fin q → Fin p → ℝ) (hA : ∀ l, 0 ≤ A l)
    (hB : ∀ l k', 0 ≤ B l k') (k : Fin p) (hk : toReal (u k) = ∑ l, A l • toReal (v l))
    (hBe : ∀ l, 0 < A l → toReal (v l) = ∑ k', B l k' • toReal (u k')) :
    ∃ l, 0 < A l ∧ ∃ c : ℝ, 0 < c ∧ toReal (v l) = c • toReal (u k) := by
  classical
  set B' : Fin q → Fin p → ℝ := fun l k' => if 0 < A l then B l k' else 0 with hB'
  have hB'0 : ∀ l k', 0 ≤ B' l k' := fun l k' => by
    simp only [hB']; split_ifs <;> [exact hB l k'; exact le_rfl]
  have hterm : ∀ l, A l • toReal (v l) = A l • ∑ k', B' l k' • toReal (u k') := fun l => by
    rcases (hA l).lt_or_eq with hl | hl
    · simp only [hB', if_pos hl]; rw [hBe l hl]
    · simp [← hl]
  have hsum : ∑ k', (if k' = k then (1 : ℝ) else 0) • toReal (u k') =
      ∑ k', (∑ l, A l * B' l k') • toReal (u k') := by
    rw [Finset.sum_eq_single k (fun b _ hb => by simp [hb]) (by simp)]
    rw [if_pos rfl, one_smul, hk]
    simp only [hterm, Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  have hc := eq_of_toReal_sum_eq hu hsum
  have hk1 : ∑ l, A l * B' l k = 1 := by simpa using (congrFun hc k).symm
  obtain ⟨l, -, hl⟩ : ∃ l ∈ Finset.univ, A l * B' l k ≠ 0 := by
    by_contra hne
    push_neg at hne
    rw [Finset.sum_eq_zero hne] at hk1
    exact zero_ne_one hk1
  have hAl : 0 < A l := (hA l).lt_of_ne fun h0 => hl (by rw [← h0, zero_mul])
  have hoff : ∀ k', k' ≠ k → B l k' = 0 := fun k' hk' => by
    have h0 : ∑ l, A l * B' l k' = 0 := by simpa [hk'] using (congrFun hc k').symm
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun l _ => mul_nonneg (hA l) (hB'0 l k'))).1 h0 l (Finset.mem_univ _)
    simpa [hB', if_pos hAl, hAl.ne'] using this
  have hvl : toReal (v l) = B l k • toReal (u k) := by
    rw [hBe l hAl, Finset.sum_eq_single k (fun b _ hb => by rw [hoff b hb, zero_smul]) (by simp)]
  refine ⟨l, hAl, B l k, (hB l k).lt_of_ne fun h0 => hv l (eq_zero_of_toReal_eq_zero ?_), hvl⟩
  rw [hvl, ← h0, zero_smul]

end GlobalTheory.PolFan.FaceSub


open GlobalTheory.PolFan.FaceSub in
theorem GlobalTheory.PolFan.eq_subfamily_of_face : ∀ {O : Type} [CommRing O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X] {m n : ℕ}
    (δ : Fin m → LinearMap.BilinForm ℤ X) (γ : Fin n → LinearMap.BilinForm ℤ X) (hδ : ∀ i, δ i ∈ balForms bar X)
    (hγ : ∀ j, γ j ∈ balForms bar X) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ),
    LinearIndependent ℤ δ → LinearIndependent ℤ γ → (∀ i, IsPrim bar (⟨δ i, hδ i⟩ : balForms bar X)) →
    (∀ j, IsPrim bar (⟨γ j, hγ j⟩ : balForms bar X)) → (∀ j, InRCone δ (γ j)) → (∀ i, 0 ≤ h (δ i)) →
    (∀ j, h (γ j) = 0) → (∀ i, h (δ i) = 0 → InRCone γ (δ i)) →
    ∃ s : Fin n ↪ Fin m, (∀ j, γ j = δ (s j)) ∧ ∀ i, h (δ i) = 0 ↔ i ∈ Set.range s := by
  intro O _ bar X _ _ m n δ γ hδ hγ h hδi hγi hδp hγp hγc hδn hγz hZ
  classical
  choose b hb hbe using hγc
  choose a ha hae using hZ
  have hsupp : ∀ j i, 0 < b j i → h (δ i) = 0 := fun j i hji => by
    have e := apply_eq_of_toReal_eq (hbe j) h
    rw [hγz j, Int.cast_zero] at e
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_nonneg (hb j i) (by exact_mod_cast hδn i))).1 e.symm i
      (Finset.mem_univ _)
    have h2 : ((h (δ i) : ℤ) : ℝ) = 0 := (mul_eq_zero.1 this).resolve_left hji.ne'
    exact_mod_cast h2
  have hex1 : ∀ i, h (δ i) = 0 → ∃ j, γ j = δ i := fun i hi => by
    obtain ⟨j, -, c, hc, e⟩ := exists_ray hδi hγi.ne_zero (a i hi) b (ha i hi) hb i (hae i hi) (fun l _ => hbe l)
    exact ⟨j, GlobalTheory.T.eq_of_primitiveBalancedForm_same_real_ray bar (γ j) (δ i) (hγ j) (hδ i) (hγp j) (hδp i) c hc e⟩
  have hex2 : ∀ j, ∃ i, h (δ i) = 0 ∧ γ j = δ i := fun j => by
    obtain ⟨i, hbi, c, hc, e⟩ := exists_ray hγi hδi.ne_zero (b j)
      (fun i => if hi : h (δ i) = 0 then a i hi else 0) (hb j)
      (fun i j' => by split_ifs with hi <;> [exact ha i hi j'; exact le_rfl]) j (hbe j)
      (fun l hl => by rw [dite_eq_left (hsupp j l hl)]; exact hae l _)
    exact ⟨i, hsupp j i hbi, (GlobalTheory.T.eq_of_primitiveBalancedForm_same_real_ray bar (δ i) (γ j) (hδ i) (hγ j) (hδp i) (hγp j) c hc e).symm⟩
  choose s hsZ hsγ using hex2
  have hsinj : Function.Injective s := fun j j' hjj => hγi.injective (by rw [hsγ j, hsγ j', hjj])
  refine ⟨⟨s, hsinj⟩, hsγ, fun i => ⟨fun hi => ?_, ?_⟩⟩
  · obtain ⟨j, hj⟩ := hex1 i hi
    exact ⟨j, hδi.injective (show δ (s j) = δ i by rw [← hsγ j, hj])⟩
  · rintro ⟨j, rfl⟩
    exact hsZ j
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqSubfamilyOfFaceSimplicialConePrimitiveStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_subfamily_of_face_simplicialCone_primitive : ∀ {O : Type} [CommRing O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X] {m n : ℕ}
    (δ : Fin m → LinearMap.BilinForm ℤ X) (γ : Fin n → LinearMap.BilinForm ℤ X) (hδ : ∀ i, δ i ∈ balForms bar X)
    (hγ : ∀ j, γ j ∈ balForms bar X) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ),
    LinearIndependent ℤ δ → LinearIndependent ℤ γ → (∀ i, IsPrim bar (⟨δ i, hδ i⟩ : balForms bar X)) →
    (∀ j, IsPrim bar (⟨γ j, hγ j⟩ : balForms bar X)) → (∀ j, InRCone δ (γ j)) → (∀ i, 0 ≤ h (δ i)) →
    (∀ j, h (γ j) = 0) → (∀ i, h (δ i) = 0 → InRCone γ (δ i)) →
    ∃ s : Fin n ↪ Fin m, (∀ j, γ j = δ (s j)) ∧ ∀ i, h (δ i) = 0 ↔ i ∈ Set.range s := by
  first | exact @GlobalTheory.PolFan.eq_subfamily_of_face | exact GlobalTheory.PolFan.eq_subfamily_of_face | (intros; apply GlobalTheory.PolFan.eq_subfamily_of_face <;> assumption)
end
end
