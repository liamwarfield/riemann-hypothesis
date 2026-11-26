module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaneZeroInsertionLinearApply
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducible
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SigmaFiniteParameterProductMeasure
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCuspidalOfIsSubquotient
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalMapLaw
public import Lean.LibrarySuggestions.Basic
public import Lean.Elab.Command

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalComparisonInert
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalComparisonInert
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.CompanionTheory.LocInert

open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin

def glEquiv {R S : Type} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
    (f : R ≃+* S) (hf : Continuous f) (hf' : Continuous f.symm) (n : ℕ) : GL (Fin n) R ≃ₜ* GL (Fin n) S where
  toFun := GeneralLinearGroup.map f.toRingHom
  invFun := GeneralLinearGroup.map f.symm.toRingHom
  left_inv g := by
    ext i j
    simp
  right_inv g := by
    ext i j
    simp
  map_mul' := map_mul _
  continuous_toFun := Units.continuous_iff.2
    ⟨Units.continuous_val.matrix_map hf, Units.continuous_coe_inv.matrix_map hf⟩
  continuous_invFun := Units.continuous_iff.2
    ⟨Units.continuous_val.matrix_map hf', Units.continuous_coe_inv.matrix_map hf'⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

abbrev aw (w : Pl E) : Above (w.under (𝓞 (maximalRealSubfield E))) := ⟨w, rfl⟩

theorem eq_aw {w : Pl E} (hw : ¬ IsSplitAt w) (u : Above (w.under (𝓞 (maximalRealSubfield E)))) : u = aw w := by
  by_contra h
  exact hw ⟨u.1, fun e => h (Subtype.ext e), u.2⟩

def uniq {w : Pl E} (hw : ¬ IsSplitAt w) : Unique (Above (w.under (𝓞 (maximalRealSubfield E)))) :=
  ⟨⟨aw w⟩, eq_aw hw⟩

def evR {w : Pl E} (hw : ¬ IsSplitAt w) : Av (w.under (𝓞 (maximalRealSubfield E))) ≃+* w.adicCompletion E :=
  letI := uniq hw
  RingEquiv.piUnique fun u : Above (w.under (𝓞 (maximalRealSubfield E))) => u.1.adicCompletion E

theorem evR_apply {w : Pl E} (hw : ¬ IsSplitAt w) (x : Av (w.under (𝓞 (maximalRealSubfield E)))) :
    evR hw x = x (aw w) := rfl

theorem continuous_evR {w : Pl E} (hw : ¬ IsSplitAt w) : Continuous (evR hw) :=
  continuous_apply (aw w)

theorem continuous_evR_symm {w : Pl E} (hw : ¬ IsSplitAt w) : Continuous (evR hw).symm := by
  letI := uniq hw
  exact (Homeomorph.piUnique fun u : Above (w.under (𝓞 (maximalRealSubfield E))) => u.1.adicCompletion E).symm.continuous

def evY {w : Pl E} (hw : ¬ IsSplitAt w) (a b : ℕ) :
    Yv a b (w.under (𝓞 (maximalRealSubfield E))) ≃ₜ* GLw a w × GLw b w where
  toMulEquiv := MulEquiv.prodCongr (glEquiv (evR hw) (continuous_evR hw) (continuous_evR_symm hw) a).toMulEquiv
    (glEquiv (evR hw) (continuous_evR hw) (continuous_evR_symm hw) b).toMulEquiv
  continuous_toFun := (glEquiv (evR hw) (continuous_evR hw) (continuous_evR_symm hw) a).continuous.prodMap
    (glEquiv (evR hw) (continuous_evR hw) (continuous_evR_symm hw) b).continuous
  continuous_invFun := (glEquiv (evR hw) (continuous_evR hw) (continuous_evR_symm hw) a).symm.continuous.prodMap
    (glEquiv (evR hw) (continuous_evR hw) (continuous_evR_symm hw) b).symm.continuous

theorem evY_apply {w : Pl E} (hw : ¬ IsSplitAt w) (a b : ℕ) (y : Yv a b (w.under (𝓞 (maximalRealSubfield E)))) :
    evY hw a b y = evw (aw w) y := rfl

theorem cjv_apply (hC : CjEx) (hU : Unr E) {w : Pl E} (hw : ¬ IsSplitAt w)
    (x : Av (w.under (𝓞 (maximalRealSubfield E)))) : evR hw (cjv _ x) = cj w (evR hw x) := by
  obtain ⟨-, -, -, h4, -⟩ := GlobalTheory.ConjAtPlace.main E hU w
  have hc' := (h4 hw).2.2.1
  have h := hC E (w.under (𝓞 (maximalRealSubfield E)))
  set X : Af E := sLoc E w (evR hw x) with hX
  have hp : pLoc E w X = evR hw x := by
    change (Pi.single w (evR hw x) : ∀ u : Pl E, u.adicCompletion E) w = _
    simp
  have hx : projv _ X = x := by
    funext u
    obtain rfl := eq_aw hw u
    exact hp
  have hs : cjv (w.under (𝓞 (maximalRealSubfield E))) = h.choose := by
    rw [cjv, dite_eq_left h]
  rw [← hx, hs, ← h.choose_spec.2 X]
  rw [evR_apply, evR_apply]
  exact hc' X

theorem evY_thv (hC : CjEx) (hU : Unr E) {w : Pl E} (hw : ¬ IsSplitAt w) (a b : ℕ)
    (y : Yv a b (w.under (𝓞 (maximalRealSubfield E)))) :
    evY hw a b (thv a b _ y) = ((thL a w).prodMap (thL b w)) (evY hw a b y) := by
  have h : ∀ n (g : GL (Fin n) (Av (w.under (𝓞 (maximalRealSubfield E))))),
      GeneralLinearGroup.map (evR hw).toRingHom (thetaGL n (cjv _) g) =
        thL n w (GeneralLinearGroup.map (evR hw).toRingHom g) := fun n g => by
    rw [thL, if_neg hw]
    exact GlobalTheory.ThetaPull.map_thetaGL _ _ _ (cjv_apply hC hU hw) g
  exact Prod.ext (h a y.1) (h b y.2)

theorem mem_Kv_iff {w : Pl E} (hw : ¬ IsSplitAt w) (a b : ℕ) (y : Yv a b (w.under (𝓞 (maximalRealSubfield E)))) :
    y ∈ Kv a b _ ↔ evY hw a b y ∈ K2 a b w := by
  rw [Kv, Subgroup.mem_iInf]
  constructor
  · intro h
    exact h (aw w)
  · intro h u
    obtain rfl := eq_aw hw u
    exact h

theorem evY_pv {w : Pl E} (hw : ¬ IsSplitAt w) (a b : ℕ) (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E) :
    evY hw a b (pv a b _ (ratF E a δ₁, ratF E b δ₂)) = (locEl a w δ₁, locEl b w δ₂) := by
  have h : ∀ n (δ : GL (Fin n) E), GeneralLinearGroup.map (evR hw).toRingHom
      (GeneralLinearGroup.map (projv (w.under (𝓞 (maximalRealSubfield E)))) (ratF E n δ)) = locEl n w δ := fun n δ => by
    rw [locEl, if_neg hw]
    ext i j
    rfl
  exact Prod.ext (h a δ₁) (h b δ₂)

theorem fv_eq {w : Pl E} (hw : ¬ IsSplitAt w) {a b : ℕ} {S : Set (Pl E)} (hS : w ∈ S)
    (φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ) (y : Yv a b (w.under (𝓞 (maximalRealSubfield E)))) :
    seen φ₁ φ₂ w (evY hw a b y) = fv S φ₁ φ₂ _ y := by
  letI := uniq hw
  rw [fv, finprod_unique]
  change _ = ∏ᶠ (_ : w ∈ S), φ₁ w (evw (aw w) y) * if IsSplitAt w then _ else 1
  rw [finprod_eq_if, if_pos hS, if_neg hw, mul_one, seen, if_neg hw, evY_apply]

theorem locCompareInert : LocCompareInert := by
  intro hC E _ _ _ hU a b S _ φ₁ φ₂ _ _ δ₁ δ₂ _ _ w hS hw
  rw [← evY_pv hw a b δ₁ δ₂]
  exact GlobalTheory.EulerTw.Transport.twOrb_transport _ _ (evY hw a b) _ _ _ _ _ _ _
    (evY_thv hC hU hw a b) (mem_Kv_iff hw a b) (fv_eq hw hS φ₁ φ₂)

end GlobalTheory.CompanionTheory.LocInert
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalComparisonInertStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_comparison_inert : PositivityTheory.Rg.BcB.G8.Fin.LocCompareInert := by
  first | exact @GlobalTheory.CompanionTheory.LocInert.locCompareInert | exact GlobalTheory.CompanionTheory.LocInert.locCompareInert | (intros; apply GlobalTheory.CompanionTheory.LocInert.locCompareInert <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueFieldMapPtCoordSndM
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.MPDict.FnDeg

open GlobalTheory.ProjSpace

theorem eval_pullRatio_comp {X Y : Scheme.{0}} {N : ℕ} (g : X ⟶ Y) (ψ : Y ⟶ PSpace ℤ N) (x : X)
    (i : Fin (N + 1)) (hx : g x ∈ ψ ⁻¹ᵁ chart ℤ N i) (j : Fin (N + 1)) :
    (g.residueFieldMap x).hom ((Y.evaluation (ψ ⁻¹ᵁ chart ℤ N i) (g x) hx).hom (pullRatio ψ _ i le_rfl j)) =
      (X.evaluation ((g ≫ ψ) ⁻¹ᵁ chart ℤ N i) x hx).hom (pullRatio (g ≫ ψ) _ i le_rfl j) := by
  have h1 := Scheme.evaluation_naturality_apply g x hx (pullRatio ψ _ i le_rfl j)
  have h2 : g.app (ψ ⁻¹ᵁ chart ℤ N i) (pullRatio ψ _ i le_rfl j) = pullRatio (g ≫ ψ) _ i le_rfl j := by
    rw [Scheme.Hom.app_eq_appLE]
    exact appLE_pullRatio (hi := le_rfl) g le_rfl
  exact h1.trans (congrArg _ h2)

theorem closure_eval_ratio {N : ℕ} (p : PSpace ℤ N) (i : Fin (N + 1)) (hp : p ∈ chart ℤ N i) :
    Subfield.closure (Set.range fun j => ((PSpace ℤ N).evaluation (chart ℤ N i) p hp).hom (ratio ℤ N i j)) = ⊤ := by
  set K := Subfield.closure (Set.range fun j => ((PSpace ℤ N).evaluation (chart ℤ N i) p hp).hom (ratio ℤ N i j))
  have hmem : ∀ s, ((PSpace ℤ N).evaluation (chart ℤ N i) p hp).hom s ∈ K := by
    intro s
    obtain ⟨q, rfl⟩ := aeval_ratio_surjective ℤ N i s
    induction q using MvPolynomial.induction_on with
    | C a =>
      rw [aeval_C]
      simpa using K.intCast_mem a
    | add a b ha hb =>
      rw [map_add (f := _), map_add (f := _)]
      exact K.add_mem ha hb
    | mul_X a j ha =>
      rw [map_mul, map_mul, aeval_X]
      exact K.mul_mem ha (Subfield.subset_closure ⟨j, rfl⟩)
  let ρ : Γ(PSpace ℤ N, chart ℤ N i) ⟶ CommRingCat.of K :=
    CommRingCat.ofHom (R := Γ(PSpace ℤ N, chart ℤ N i)) (S := K)
      (((PSpace ℤ N).evaluation (chart ℤ N i) p hp).hom.codRestrict K hmem)
  refine GlobalTheory.subfield_eq_top_of_fromSpecResidueField_factors _ p K
    (Spec.map ρ ≫ (isAffineOpen_chart ℤ N i).fromSpec) ?_
  rw [← Category.assoc, ← Spec.map_comp]
  have hev : Spec.map ((PSpace ℤ N).evaluation (chart ℤ N i) p hp) ≫ (isAffineOpen_chart ℤ N i).fromSpec =
      (PSpace ℤ N).fromSpecResidueField p := by
    rw [Scheme.fromSpecResidueField, ← (isAffineOpen_chart ℤ N i).fromSpecStalk_eq_fromSpecStalk hp,
      IsAffineOpen.fromSpecStalk, Scheme.evaluation, Spec.map_comp, Category.assoc]
  exact hev

theorem range_residueFieldMap_le {X : Scheme.{0}} {N : ℕ} (φ : X ⟶ PSpace ℤ N) (x : X) (i : Fin (N + 1))
    (hx : x ∈ φ ⁻¹ᵁ chart ℤ N i) :
    Set.range (φ.residueFieldMap x).hom ⊆
      Subfield.closure (Set.range fun j => (X.evaluation (φ ⁻¹ᵁ chart ℤ N i) x hx).hom (pullRatio φ _ i le_rfl j)) := by
  rintro _ ⟨a, rfl⟩
  have ha : a ∈ Subfield.closure (Set.range fun j =>
      ((PSpace ℤ N).evaluation (chart ℤ N i) (φ x) hx).hom (ratio ℤ N i j)) := by
    have hc := closure_eval_ratio (φ x) i hx
    rw [hc]
    exact Subfield.mem_top a
  have h1 : (φ.residueFieldMap x).hom a ∈ _ := Subfield.mem_map.2 ⟨a, ha, rfl⟩
  rw [RingHom.map_field_closure] at h1
  refine Subfield.closure_mono ?_ h1
  rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
  refine ⟨j, ?_⟩
  have h2 := Scheme.evaluation_naturality_apply φ x hx (ratio ℤ N i j)
  rw [Scheme.Hom.app_eq_appLE] at h2
  exact h2.symm

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem ptCoord_ptChart (x : MP ℤ m n) (k : Fin (m + 1)) : ptCoord x ⟨k, ptChart x k⟩ = 1 := by
  simp only [ptCoord, pullRatio_self, map_one]

theorem range_prB_le (x : MP ℤ m n) (k : Fin (m + 1)) :
    Set.range ((prB n k).residueFieldMap x).hom ⊆ Subfield.closure (Set.range (ptCoord x)) := by
  refine (range_residueFieldMap_le (prB n k) x (ptChart x k) (mem_ptChart x k)).trans ?_
  refine Subfield.closure_le.2 ?_
  rintro _ ⟨j, rfl⟩
  exact Subfield.subset_closure ⟨⟨k, j⟩, rfl⟩

abbrev sndM (m : ℕ) (n : Fin (m + 2) → ℕ) : MP ℤ (m + 1) n ⟶ MP ℤ m (Fin.tail n) :=
  pullback.snd (toSpecBase ℤ (n 0)) (mpStr ℤ m (Fin.tail n))

theorem residueFieldMap_ptCoord_sndM {n : Fin (m + 2) → ℕ} (x : MP ℤ (m + 1) n) (k : Fin (m + 1))
    (j : Bk (Fin.tail n) k) :
    ((sndM m n).residueFieldMap x).hom (ptCoord (sndM m n x) ⟨k, j⟩) = ptCoord x ⟨k.succ, j⟩ :=
  eval_pullRatio_comp (sndM m n) (prB (Fin.tail n) k) x (ptChart (sndM m n x) k) (mem_ptChart (sndM m n x) k) j

theorem closure_ptCoord : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ m n),
    Subfield.closure (Set.range (ptCoord x)) = ⊤
  | 0, n, x => by
    haveI : IsOpenImmersion (prB n 0) := inferInstanceAs (IsOpenImmersion (𝟙 _))
    refine eq_top_iff.2 fun a _ => range_prB_le x 0 ?_
    exact (ConcreteCategory.bijective_of_isIso ((prB n 0).residueFieldMap x)).2 a
  | m + 1, n, x => by
    have H : Subfield.closure (Set.range ((prB n 0).residueFieldMap x).hom ∪
        Set.range ((sndM m n).residueFieldMap x).hom) = ⊤ :=
      GlobalTheory.closure_range_residueFieldMap_pullback_eq_top _ _ _ (toSpecBase ℤ (n 0)) (mpStr ℤ m (Fin.tail n)) x
    rw [eq_top_iff, ← H]
    refine Subfield.closure_le.2 (Set.union_subset ?_ ?_)
    · rintro _ ⟨a, rfl⟩
      exact range_prB_le x 0 ⟨a, rfl⟩
    · rintro _ ⟨a, rfl⟩
      have ha : a ∈ Subfield.closure (Set.range (ptCoord (sndM m n x))) := by
        rw [closure_ptCoord m (Fin.tail n) (sndM m n x)]
        exact Subfield.mem_top a
      have h1 : ((sndM m n).residueFieldMap x).hom a ∈ _ := Subfield.mem_map.2 ⟨a, ha, rfl⟩
      rw [RingHom.map_field_closure] at h1
      refine Subfield.closure_mono ?_ h1
      rintro _ ⟨_, ⟨⟨k, j⟩, rfl⟩, rfl⟩
      exact ⟨⟨k.succ, j⟩, (residueFieldMap_ptCoord_sndM x k j).symm⟩

theorem blockFnField_ptCoord (x : MP ℤ m n) [CharZero ((MP ℤ m n).residueField x)] :
    blockFnField (ptCoord x) = ⊤ := by
  refine eq_top_iff.2 fun a _ => ?_
  have hle : Subfield.closure (Set.range (ptCoord x)) ≤ (blockFnField (ptCoord x)).toSubfield := by
    refine Subfield.closure_le.2 ?_
    rintro _ ⟨p, rfl⟩
    refine IntermediateField.subset_adjoin _ _ ⟨p, ⟨p.1, ptChart x p.1⟩, rfl, ?_⟩
    rw [ptCoord_ptChart, div_one]
  exact hle (by rw [closure_ptCoord]; exact Subfield.mem_top a)

theorem blockFnField_comp {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {Ω Ω' : Type*} [Field Ω]
    [CharZero Ω] [Field Ω'] [CharZero Ω'] (g : Ω →ₐ[ℚ] Ω') (y : (Σ k, ι k) → Ω) :
    blockFnField (g ∘ y) = (blockFnField y).map g := by
  unfold blockFnField
  rw [IntermediateField.adjoin_map]
  congr 1
  ext t
  constructor
  · rintro ⟨p, q, h, rfl⟩
    exact ⟨_, ⟨p, q, h, rfl⟩, by simp [map_div₀]⟩
  · rintro ⟨_, ⟨p, q, h, rfl⟩, rfl⟩
    exact ⟨p, q, h, by simp [map_div₀]⟩

theorem ptCoord_sv (n' : ℕ) {m : ℕ} (n : Fin (m + 1) → ℕ) (x : MP ℤ (m + 1) (consN n' n)) (p : Σ k, Bk n k) :
    ptCoord x (sv n' n p) = ((qpSnd n' m n).residueFieldMap x).hom (ptCoord ((qpSnd n' m n) x) p) :=
  (residueFieldMap_ptCoord_sndM (n := consN n' n) x p.1 p.2).symm

theorem relfinrank_blockFnField_sv : ∀ (n' m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ (m + 1) (consN n' n))
    [CharZero ((MP ℤ (m + 1) (consN n' n)).residueField x)],
    IntermediateField.relfinrank (blockFnField (ptCoord x ∘ sv n' n)) (blockFnField (ptCoord x)) =
      (qpSnd n' m n).residueDegree x := by
  intro n' m n x _
  let f : (MP ℤ m n).residueField ((qpSnd n' m n) x) ⟶ (MP ℤ (m + 1) (consN n' n)).residueField x :=
    (qpSnd n' m n).residueFieldMap x
  haveI : CharZero ((MP ℤ m n).residueField ((qpSnd n' m n) x)) :=
    (RingHom.charZero_iff f.hom.injective).2 inferInstance
  let g := f.hom.toRatAlgHom
  have e : ptCoord x ∘ sv n' n = g ∘ ptCoord ((qpSnd n' m n) x) := _root_.funext fun p => ptCoord_sv n' n x p
  rw [e, blockFnField_comp, blockFnField_ptCoord, blockFnField_ptCoord, IntermediateField.relfinrank_top_right]
  letI := f.hom.toAlgebra
  let i := (IntermediateField.topEquiv.symm.trans (IntermediateField.equivMap ⊤ g)).toRingEquiv
  refine (Algebra.finrank_eq_of_equiv_equiv i (RingEquiv.refl _) ?_).symm
  ext a
  rfl

end GlobalTheory.CompanionTheory.MPDict.FnDeg
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JoinedBlockFormula
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JoinedBlockFormula
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ColumnSplitting

theorem jnBl : JnBl := by
  intro D n t a r hn w v y
  unfold jn PositivityTheory.Rg.Rsw.L.mm
  rw [show bl hn (1 : Mx D r r) y (0 : Mx D t r) (1 : Mx D t t) =
      (Matrix.fromBlocks (1 : Mx D r r) y (0 : Mx D t r) (1 : Mx D t t)).submatrix
        (finSumFinEquiv.trans (finCongr hn)).symm (finSumFinEquiv.trans (finCongr hn)).symm from rfl]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromCols_mul_fromBlocks]
  simp

end GlobalTheory.CompanionTheory.ColumnSplitting
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JoinedBlockFormulaStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.joined_block_formula : JnBl := by
  first | exact @GlobalTheory.CompanionTheory.ColumnSplitting.jnBl | exact GlobalTheory.CompanionTheory.ColumnSplitting.jnBl | (intros; apply GlobalTheory.CompanionTheory.ColumnSplitting.jnBl <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplexPointHasNonzeroLift
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict

theorem exists_isUnder_of_cxPt (m : ℕ) (n : Fin (m + 1) → ℕ) (y : CxPts (mpStr ℤ m n) σ₀) :
    ∃ z : (Σ k, Bk n k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) ∧ IsUnder y z := by
  have hc : ∀ k, ∃ i, y ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k i) := fun k =>
    ⟨ptChart _ k, CxPts.mem_ptsIn.2 (mem_ptChart _ k)⟩
  choose c hc using hc
  let z : (Σ k, Bk n k) → ℂ := fun p =>
    CxPts.ev (mpStr ℤ m n) σ₀ (blockChart n p.1 (c p.1)) (pullRatio (prB n p.1) _ (c p.1) le_rfl p.2) y
  have hz1 : ∀ k, z ⟨k, c k⟩ = 1 := fun k => by
    change CxPts.ev (mpStr ℤ m n) σ₀ (blockChart n k (c k)) (pullRatio (prB n k) _ (c k) le_rfl (c k)) y = 1
    rw [pullRatio_self, CxPts.ev_eq (hc k), map_one]
  refine ⟨z, fun k => ⟨c k, by rw [hz1]; exact one_ne_zero⟩, fun k i => ?_⟩
  have hmem : y ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k i) ↔ z ⟨k, i⟩ ≠ 0 := by
    have e := CxPts.mem_ptsIn_basicOpen (hc k) (pullRatio (prB n k) _ (c k) le_rfl i)
    rw [basicOpen_pullRatio, CxPts.mem_ptsIn_inf] at e
    exact ⟨fun h => e.1 ⟨hc k, h⟩, fun h => (e.2 h).2⟩
  refine ⟨hmem, fun j hi => ?_⟩
  have hW : y ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k (c k) ⊓ blockChart n k i) :=
    CxPts.mem_ptsIn_inf.2 ⟨hc k, hi⟩
  have r1 : ∀ l, CxPts.ev (mpStr ℤ m n) σ₀ (blockChart n k (c k) ⊓ blockChart n k i)
      (pullRatio (prB n k) _ (c k) inf_le_left l) y = z ⟨k, l⟩ := fun l => by
    rw [← resG_pullRatio (φ := prB n k) (W := blockChart n k (c k)) (i := c k) (hi := le_rfl) inf_le_left]
    exact CxPts.ev_res inf_le_left hW _
  have r2 : CxPts.ev (mpStr ℤ m n) σ₀ (blockChart n k (c k) ⊓ blockChart n k i)
      (pullRatio (prB n k) _ i inf_le_right j) y =
      CxPts.ev (mpStr ℤ m n) σ₀ (blockChart n k i) (pullRatio (prB n k) _ i le_rfl j) y := by
    rw [← resG_pullRatio (φ := prB n k) (W := blockChart n k i) (i := i) (hi := le_rfl) inf_le_right]
    exact CxPts.ev_res inf_le_right hW _
  have e := congrArg (fun f => CxPts.ev (mpStr ℤ m n) σ₀ (blockChart n k (c k) ⊓ blockChart n k i) f y)
    (pullRatio_mul_pullRatio (φ := prB n k) (W := blockChart n k (c k) ⊓ blockChart n k i) (i := c k) (j := i)
      (k := j) (hi := inf_le_left) (hj := inf_le_right))
  simp only [CxPts.ev_mul, r1, r2] at e
  rw [eq_div_iff (hmem.1 hi), mul_comm]
  exact e

end GlobalTheory.CompanionTheory.MPDict
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepDualInverse
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict

theorem ev_unit_inv_mul {m : ℕ} {n : Fin (m + 1) → ℕ} {U : (MP ℤ m n).Opens} (v : Γ(MP ℤ m n, U)ˣ)
    (y : CxPts (mpStr ℤ m n) σ₀) (hy : y ∈ ptsIn (mpStr ℤ m n) σ₀ U) :
    CxPts.ev (mpStr ℤ m n) σ₀ U (↑v⁻¹ : Γ(MP ℤ m n, U)) y *
      CxPts.ev (mpStr ℤ m n) σ₀ U (v : Γ(MP ℤ m n, U)) y = 1 := by
  unfold CxPts.ev ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR
  split_ifs with h
  · rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]
  · exact (h hy).elim

theorem isHermRep_dual : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (M : HermLB (mpStr ℤ m n)) (A : Geo.HermLine (Bk n)),
    IsHermRep M A → IsHermRep M.dual A.inv := by
  intro m n M A hA
  obtain ⟨u, h1, h2, h3⟩ := hA
  refine ⟨fun i c => (u i c)⁻¹, ?_, ?_, ?_⟩
  · rintro (i : M.B.ι) (j : M.B.ι) c
    change Semi.res _ (u j c)⁻¹ = Semi.res _ (M.B.g i j)⁻¹ * Semi.res _ (u i c)⁻¹
    rw [map_inv, map_inv, map_inv, ← mul_inv]
    exact congrArg (·⁻¹) (h1 i j c)
  · rintro (i : M.B.ι) c c'
    change Semi.res _ (u i c)⁻¹ = Semi.res _ (u i c')⁻¹ * ∏ k, blockUnit (c k) (c' k) _ ^ (-A.a k)
    rw [map_inv, map_inv]
    have h := congrArg (·⁻¹) (h2 i c c')
    simp only [mul_inv, ← Finset.prod_inv_distrib, ← zpow_neg] at h
    exact h
  · rintro (i : M.B.ι) c y z hz (hyin : y ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c))
    change (A.h z)⁻¹ = (∏ k, ‖z ⟨k, c k⟩‖ ^ (-A.a k)) *
      ‖CxPts.ev (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c) (↑(u i c)⁻¹) y‖ * Real.exp (-(M.φ σ₀).φ i y / 2)
    have e : CxPts.ev (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c) (↑(u i c)⁻¹) y =
        (CxPts.ev (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c) (↑(u i c)) y)⁻¹ :=
      eq_inv_of_mul_eq_one_left (ev_unit_inv_mul (u i c) y hyin)
    rw [h3 i c y z hz hyin]
    simp only [zpow_neg, Finset.prod_inv_distrib, neg_div, Real.exp_neg, mul_inv]
    congr 2
    rw [e, norm_inv]

end GlobalTheory.CompanionTheory.MPDict
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbscissaConvergenceIdentity
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbscissaConvergenceIdentity
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ColumnSplitting.GramAct

theorem ip_mt {D : D7} {a b : ℕ} (V : HSp D) (g : GA D V) (x : Mx D V.rank a) (y : Mx D V.rank b) :
    ip V (mm (mt V g) x) (mm (mt V g) y) = ip V x y := by
  have hu : adj (mt V g) * (gA V * mt V g) = gA V := mt_unitary V g
  unfold ip mm
  rw [adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA V), ← Matrix.mul_assoc (adj (mt V g)), hu]

theorem acEq : AcEq := by
  intro D r t V b₀ g z
  have h12 : ip V (ac V g z).1 (ac V g z).2 = ip V z.1 z.2 := ip_mt V g z.1 z.2
  have h22 : ip V (ac V g z).2 (ac V g z).2 = ip V z.2 z.2 := ip_mt V g z.2 z.2
  have hy : yv V b₀ (ac V g z) = yv V b₀ z := by
    unfold yv
    rw [h12]
  refine ⟨ip_mt V g z.1 z.1, hy, ?_⟩
  unfold qv
  rw [h22, hy]

end GlobalTheory.CompanionTheory.ColumnSplitting.GramAct

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbscissaConvergenceIdentityStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abscissa_convergence_identity : AcEq := by
  first | exact @GlobalTheory.CompanionTheory.ColumnSplitting.GramAct.acEq | exact GlobalTheory.CompanionTheory.ColumnSplitting.GramAct.acEq | (intros; apply GlobalTheory.CompanionTheory.ColumnSplitting.GramAct.acEq <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepOfIsometric
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.IsomT

variable {X : Scheme.{0}}

theorem res_twice {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (u : Γ(X, U)ˣ) :
    res h₂ (res h₁ u) = res (h₂.trans h₁) u := by
  apply Units.ext
  show (X.presheaf.map (homOfLE h₂).op).hom ((X.presheaf.map (homOfLE h₁).op).hom (u : Γ(X, U))) =
    (X.presheaf.map (homOfLE (h₂.trans h₁)).op).hom (u : Γ(X, U))
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
  rfl

theorem units_ext_cover {ι : Type} (V : ι → X.Opens) (hc : ⨆ i, V i = ⊤) {W : X.Opens}
    {f g : Γ(X, W)ˣ} (h : ∀ i, res (inf_le_left : W ⊓ V i ≤ W) f = res inf_le_left g) : f = g := by
  apply Units.ext
  have hcov : W ≤ ⨆ i, W ⊓ V i := by
    rw [← inf_iSup_eq, hc, inf_top_eq]
  refine TopCat.Sheaf.eq_of_locally_eq' X.sheaf (fun i => W ⊓ V i) W (fun i => homOfLE inf_le_left) hcov _ _
    fun i => ?_
  exact congrArg Units.val (h i)

theorem exists_glue {ι : Type} (V : ι → X.Opens) (hc : ⨆ i, V i = ⊤) (W : X.Opens)
    (f : ∀ i, Γ(X, W ⊓ V i)ˣ)
    (hf : ∀ i j, res (inf_le_left : (W ⊓ V i) ⊓ (W ⊓ V j) ≤ W ⊓ V i) (f i) =
      res inf_le_right (f j)) :
    ∃ u : Γ(X, W)ˣ, ∀ i, res inf_le_left u = f i := by
  have hcov : W ≤ ⨆ i, W ⊓ V i := by
    rw [← inf_iSup_eq, hc, inf_top_eq]
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf (fun i => W ⊓ V i) W
    (fun i => homOfLE inf_le_left) hcov (fun i => ((f i : Γ(X, W ⊓ V i))))
    (fun i j => congrArg Units.val (hf i j))
  obtain ⟨t, ht, -⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf (fun i => W ⊓ V i) W
    (fun i => homOfLE inf_le_left) hcov (fun i => (((f i)⁻¹ : Γ(X, W ⊓ V i)ˣ) : Γ(X, W ⊓ V i)))
    (fun i j => by
      have := congrArg Units.val (congrArg (·⁻¹) (hf i j))
      rw [← map_inv, ← map_inv] at this
      exact this)
  have hst : s * t = 1 := by
    refine TopCat.Sheaf.eq_of_locally_eq' X.sheaf (fun i => W ⊓ V i) W (fun i => homOfLE inf_le_left) hcov _ _
      fun i => ?_
    rw [map_mul, map_one, hs i, ht i]
    exact (f i).mul_inv
  refine ⟨⟨s, t, hst, by show (t : Γ(X, W)) * s = 1; rw [mul_comm]; exact hst⟩, fun i => Units.ext ?_⟩
  exact hs i

theorem ofMem {V U : X.Opens} (h : ∀ x, x ∈ V → x ∈ U) : V ≤ U := by
  intro x hx
  exact h x hx

end GlobalTheory.CompanionTheory.MPDict.IsomT

namespace GlobalTheory.CompanionTheory.MPDict

open IsomT

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem res_blockUnit {k : Fin (m + 1)} (i j : Bk n k)
    {W W' : (MP ℤ m n).Opens} (h : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) i ⊓ chart ℤ (n k) j)) (h' : W' ≤ W) :
    res h' (blockUnit i j h) = blockUnit i j (h'.trans h) := by
  unfold blockUnit
  exact res_twice _ _ _

theorem res_mul_prod (c c' : ∀ k, Bk n k) (e : Fin (m + 1) → ℤ)
    {W W' : (MP ℤ m n).Opens} (x : Γ(MP ℤ m n, W)ˣ)
    (H : ∀ k, W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c k) ⊓ chart ℤ (n k) (c' k))) (h' : W' ≤ W) :
    res h' (x * ∏ k, blockUnit (c k) (c' k) (H k) ^ e k) =
      res h' x * ∏ k, blockUnit (c k) (c' k) (h'.trans (H k)) ^ e k := by
  rw [map_mul, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_zpow, res_blockUnit]

end GlobalTheory.CompanionTheory.MPDict
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInjectiveOfSubsingleton
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.SmGL.Exponents

noncomputable section

namespace GlobalTheory.CompanionTheory.SubEmb

theorem exists_injective_of_subsingleton {G V Y : Type} [Group G] [Subsingleton G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup Y] [Module ℂ Y] [Nontrivial Y] (π : Representation ℂ G V) (τ : Representation ℂ G Y)
    (hi : π.IsIrreducible) : ∃ φ : π.IntertwiningMap τ, Function.Injective φ := by
  classical
  haveI := hi
  haveI : Nontrivial V := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hi
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨w, hw⟩ := exists_ne (0 : Y)
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual ℂ V, f v ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv ((Module.forall_dual_apply_eq_zero_iff ℂ v).1 h)
  let φ : π.IntertwiningMap τ :=
    { toFun := fun u => f u • w
      map_add' := fun a b => by simp [add_smul]
      map_smul' := fun c a => by simp [mul_smul]
      isIntertwining' := fun g => by
        rw [Subsingleton.elim g 1, map_one, map_one]
        exact LinearMap.ext fun _ => rfl }
  refine ⟨φ, (Representation.IsIrreducible.injective_or_eq_zero φ).resolve_right fun h => ?_⟩
  have h1 : f v • w = 0 := congrArg (fun ψ : π.IntertwiningMap τ => ψ v) h
  exact (smul_ne_zero hf hw) h1

theorem zero_case {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin 0) k) V) (hi : π.IsIrreducible)
    (x : Fin 0 → IrrGL (k := k)) (hd : ∑ a, (x a).1 = 0) :
    ∃ φ : π.IntertwiningMap (prodIrr x hd), Function.Injective φ := by
  haveI : Subsingleton (GL (Fin 0) k) := ⟨fun _ _ => Units.ext (Subsingleton.elim _ _)⟩
  have hirr : (prodIrr x hd).IsIrreducible := GlobalTheory.SmGL.MultiIrr.isIrreducible_multiProd_zero _ _
  haveI := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hirr
  exact exists_injective_of_subsingleton π _ hi

theorem succ_case
    (hstage : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p q r t : ℕ) (x : Fin p → IrrGL (k := k)) (y : Fin q → IrrGL (k := k)) (hx : ∑ a, (x a).1 = r) (hy : ∑ a, (y a).1 = t) (h : ∑ a, (Fin.append x y a).1 = r + t), Nonempty ((prod₂ (prodIrr x hx) (prodIrr y hy)).Equiv (prodIrr (Fin.append x y) h)))
    {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b c : ℕ} {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (σ : Representation ℂ (GL (Fin a) k) W) (ρ : Representation ℂ (GL (Fin b) k) W')
    (hb : 0 < b) (hρs : IsSmooth ρ) (hρi : ρ.IsIrreducible) (hρc : IsCuspidal ρ)
    (x' : Fin c → IrrGL (k := k)) (hd' : ∑ i, (x' i).1 = a) (hcusp : ∀ i, (x' i).IsCusp)
    (f : σ.IntertwiningMap (prodIrr x' hd')) (hf : Function.Injective f) :
    ∃ (c' : ℕ) (x : Fin c' → IrrGL (k := k)) (hd : ∑ i, (x i).1 = a + b), (∀ i, (x i).IsCusp) ∧
      ∃ Φ : (prod₂ σ ρ).IntertwiningMap (prodIrr x hd), Function.Injective Φ := by
  have hF0 := GlobalTheory.CompanionTheory.ProdInj.prod₂_map_injective k a b _ _ W' σ _ ρ f hf
  obtain ⟨F, hF⟩ := hF0
  let y : Fin 1 → IrrGL (k := k) := fun _ => IrrGL.of ρ hρs hρi
  have hy : ∑ i, (y i).1 = b := by simp [y, IrrGL.of]
  have hy' : ∑ i : Fin 1, (IrrGL.of ρ hρs hρi).1 = (IrrGL.of ρ hρs hρi).1 := by simp
  have e₁0 := nonempty_equiv_prodIrr_one (IrrGL.of ρ hρs hρi) hy'
  obtain ⟨e₁⟩ := e₁0
  have e₂ : ρ.Equiv (prodIrr y hy) := (IrrGL.equivOf ρ hρs hρi).trans e₁
  have hd : ∑ i, (Fin.append x' y i).1 = a + b := by
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    rw [hd', hy]
  have e₃0 := hstage k c 1 a b x' y hd' hy hd
  obtain ⟨e₃⟩ := e₃0
  refine ⟨c + 1, Fin.append x' y, hd, fun i => ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [Fin.append_left]; exact hcusp i
    · rw [Fin.append_right]; exact IrrGL.isCusp_of.2 ⟨hb, hρc⟩
  · let E := (prod₂Equiv (Representation.Equiv.refl _) e₂).trans e₃
    refine ⟨E.toIntertwiningMap.comp F, ?_⟩
    exact E.toLinearEquiv.injective.comp hF

theorem subEmbedding_of_stage
    (hstage : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p q r t : ℕ) (x : Fin p → IrrGL (k := k)) (y : Fin q → IrrGL (k := k)) (hx : ∑ a, (x a).1 = r) (hy : ∑ a, (y a).1 = t) (h : ∑ a, (Fin.append x y a).1 = r + t), Nonempty ((prod₂ (prodIrr x hx) (prodIrr y hy)).Equiv (prodIrr (Fin.append x y) h))) :
    Ysupp.SubEmbedding := by
  intro k _ _ _ _ N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro V _ _ π hs hi
    by_cases hN0 : N = 0
    · subst hN0
      exact ⟨0, Fin.elim0, by simp, fun a => a.elim0, zero_case π hi _ _⟩
    · have hN : 0 < N := Nat.pos_of_ne_zero hN0
      have h0 := GlobalTheory.JacFactor.exists_map_jac₂ k N V π hs hi hN
      obtain ⟨a, b, h, W, W', _, _, _, _, σ, ρ, hb, hσs, hσi, hρs, hρi, hρc, φ, hφ⟩ := h0
      subst h
      have h1 := GlobalTheory.CompanionTheory.Frob.exists_injective_of_jac₂ k a b V W W' π σ ρ hs hi φ hφ
      obtain ⟨ψ, hψ⟩ := h1
      have h2 := ih a (by omega) W σ hσs hσi
      obtain ⟨c, x', hd', hcusp, f, hf⟩ := h2
      have h3 := succ_case hstage σ ρ hb hρs hρi hρc x' hd' hcusp f hf
      obtain ⟨c', x, hd, hx, Φ, hΦ⟩ := h3
      exact ⟨c', x, hd, hx, Φ.comp ψ, hΦ.comp hψ⟩

end GlobalTheory.CompanionTheory.SubEmb
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImageZMCoordIdealOfEq
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.MPDict.ProjImage

section Alg

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
  {K' : Type*} [Fintype K'] {ι' : K' → Type*} [∀ k, Fintype (ι' k)]
  {Ω₀ Ω : Type*} [Field Ω₀] [Field Ω]

def scaleT (c : K → Ω) : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω :=
  aeval fun k => C (c k) * X k

theorem scaleT_injective (c : K → Ω) (hc : ∀ k, c k ≠ 0) : Function.Injective (scaleT c) := by
  have h : (scaleT (fun k => (c k)⁻¹)).comp (scaleT c) = AlgHom.id Ω _ := by
    refine MvPolynomial.algHom_ext fun k => ?_
    simp only [scaleT, AlgHom.comp_apply, aeval_X, map_mul, algHom_C, AlgHom.id_apply]
    rw [MvPolynomial.algebraMap_eq, ← mul_assoc, ← C_mul, mul_inv_cancel₀ (hc k), C_1, one_mul]
  exact Function.LeftInverse.injective (g := scaleT fun k => (c k)⁻¹) fun f => by
    simpa using congrArg (fun g => g f) h

theorem imageZ_mCoordIdeal_of_eq (κ : K → K') (hκ : Function.Injective κ) (v : (Σ k, ι k) → (Σ k', ι' k'))
    (hv : ∀ p, (v p).1 = κ p.1) (φ : Ω₀ →+* Ω) (b : K → Ω) (hb : ∀ k, b k ≠ 0)
    (y₀ : (Σ k, ι k) → Ω₀) (y : (Σ k', ι' k') → Ω) (h : ∀ p, φ (y₀ p) = b p.1 * y (v p)) :
    imageZ v (Geo.mCoordIdeal y) = Geo.mCoordIdeal y₀ := by
  let ψ : MvPolynomial K Ω₀ →+* MvPolynomial K' Ω :=
    ((rename κ : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K' Ω).toRingHom.comp
      (scaleT fun k => (b k)⁻¹).toRingHom).comp (MvPolynomial.map φ)
  have hψ : Function.Injective ψ :=
    (rename_injective κ hκ).comp ((scaleT_injective _ fun k => inv_ne_zero (hb k)).comp
      (map_injective φ φ.injective))
  have key : ∀ f : Geo.MRing ι, ψ (Geo.mConeMap y₀ f) = Geo.mConeMap y (rename v f) := by
    intro f
    have e : ψ.comp (Geo.mConeMap y₀ : Geo.MRing ι →ₐ[ℤ] MvPolynomial K Ω₀).toRingHom =
        ((Geo.mConeMap y : Geo.MRing ι' →ₐ[ℤ] MvPolynomial K' Ω).toRingHom.comp
          (rename v : Geo.MRing ι →ₐ[ℤ] Geo.MRing ι').toRingHom) := by
      refine MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)
      · simp
      · simp only [ψ, Geo.mConeMap, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X,
          rename_X, map_mul, map_C, map_X, scaleT, algHom_C, rename_C]
        rw [hv p, h p]
        simp only [MvPolynomial.algebraMap_eq, rename_C]
        rw [← mul_assoc, ← C_mul, mul_comm (b p.1), mul_assoc, mul_inv_cancel₀ (hb p.1), mul_one]
    exact congrArg (fun g => g f) e
  ext f
  simp only [imageZ, Geo.mCoordIdeal, Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [← key, map_eq_zero_iff ψ hψ]

end Alg

end GlobalTheory.CompanionTheory.MPDict.ProjImage

namespace GlobalTheory.CompanionTheory.MPDict.ProjImage

theorem evaluation_resG {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (x : X) (hx : x ∈ V) (s : Γ(X, U)) :
    X.evaluation V x hx (resG X h s) = X.evaluation U x (h hx) s := by
  show X.residue x (X.presheaf.germ V x hx (X.presheaf.map (homOfLE h).op s)) = _
  rw [TopCat.Presheaf.germ_res_apply]
  rfl

theorem ptCoord_qpSnd (n' m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ (m + 1) (consN n' n)) (k : Fin (m + 1)) :
    ∃ b : (MP ℤ (m + 1) (consN n' n)).residueField x, b ≠ 0 ∧ ∀ i : Bk n k,
      (qpSnd n' m n).residueFieldMap x (ptCoord (qpSnd n' m n x) ⟨k, i⟩) = b * ptCoord x ⟨k.succ, i⟩ := by
  let F : MP ℤ (m + 1) (consN n' n) ⟶ MP ℤ m n := qpSnd n' m n
  let P : MP ℤ (m + 1) (consN n' n) ⟶ PSpace ℤ (n k) := prB (consN n' n) k.succ
  have hP : F ≫ prB n k = P := rfl
  let c₀ := ptChart (F x) k
  let c₁ := ptChart x k.succ
  have hx₀ : F x ∈ blockChart n k c₀ := mem_ptChart _ _
  have hx₁ : x ∈ blockChart (consN n' n) k.succ c₁ := mem_ptChart _ _
  let W₀ : (MP ℤ (m + 1) (consN n' n)).Opens := F ⁻¹ᵁ blockChart n k c₀
  let W₁ : (MP ℤ (m + 1) (consN n' n)).Opens := blockChart (consN n' n) k.succ c₁
  have h₀ : W₀ ≤ P ⁻¹ᵁ chart ℤ (n k) c₀ := le_rfl
  have h₁ : W₁ ≤ P ⁻¹ᵁ chart ℤ (n k) c₁ := le_rfl
  let V := W₀ ⊓ W₁
  have hxV : x ∈ V := ⟨hx₀, hx₁⟩
  have hV₀ : V ≤ P ⁻¹ᵁ chart ℤ (n k) c₀ := inf_le_left.trans h₀
  have hV₁ : V ≤ P ⁻¹ᵁ chart ℤ (n k) c₁ := inf_le_right.trans h₁
  have e₀ : ∀ i : Bk n k, F.residueFieldMap x (ptCoord (F x) ⟨k, i⟩) =
      (MP ℤ (m + 1) (consN n' n)).evaluation V x hxV (pullRatio P V c₀ hV₀ i) := by
    intro i
    show F.residueFieldMap x ((MP ℤ m n).evaluation (blockChart n k c₀) (F x) hx₀
      (pullRatio (prB n k) _ c₀ le_rfl i)) = _
    rw [Scheme.evaluation_naturality_apply, Scheme.Hom.app_eq_appLE, appLE_pullRatio,
      ← evaluation_resG (inf_le_left : V ≤ W₀) x hxV, resG_pullRatio]
    rfl
  have e₁ : ∀ i : Bk n k, ptCoord x ⟨k.succ, i⟩ =
      (MP ℤ (m + 1) (consN n' n)).evaluation V x hxV (pullRatio P V c₁ hV₁ i) := by
    intro i
    show (MP ℤ (m + 1) (consN n' n)).evaluation W₁ x hx₁ (pullRatio P W₁ c₁ h₁ i) = _
    rw [← evaluation_resG (inf_le_right : V ≤ W₁) x hxV]
    exact congrArg _ (resG_pullRatio (φ := P) (hi := h₁) inf_le_right)
  refine ⟨(MP ℤ (m + 1) (consN n' n)).evaluation V x hxV (pullRatio P V c₀ hV₀ c₁), ?_, fun i => ?_⟩
  · intro h0
    have e := congrArg ((MP ℤ (m + 1) (consN n' n)).evaluation V x hxV)
      ((pullRatio_mul_pullRatio (φ := P) (hi := hV₀) (hj := hV₁) (k := c₀)).trans pullRatio_self)
    rw [map_mul, h0, zero_mul, map_one] at e
    exact zero_ne_one e
  · refine (e₀ i).trans ?_
    rw [e₁ i, ← map_mul]
    exact congrArg _ (pullRatio_mul_pullRatio (φ := P) (hi := hV₀) (hj := hV₁) (k := i)).symm

end GlobalTheory.CompanionTheory.MPDict.ProjImage

namespace GlobalTheory.CompanionTheory.MPDict.ProjImage

theorem imageZ_ptIdeal (n' m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ (m + 1) (consN n' n)) :
    imageZ (sv n' n) (ptIdeal x) = ptIdeal (qpSnd n' m n x) := by
  choose b hb h using ptCoord_qpSnd n' m n x
  exact imageZ_mCoordIdeal_of_eq Fin.succ (Fin.succ_injective _) (sv n' n) (fun _ => rfl)
    ((qpSnd n' m n).residueFieldMap x).hom b hb (ptCoord (qpSnd n' m n x)) (ptCoord x) fun p => h p.1 p.2

end GlobalTheory.CompanionTheory.MPDict.ProjImage
end
end
