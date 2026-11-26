module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.SheetUnsheet

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogNormSheetEq
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogNormSheetEq
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

noncomputable section

theorem GlobalTheory.CompanionTheory.Ar.BaseZ.logNorm_sheet : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ) (B : LB X) (φ : ∀ σ : k →+* ℂ, Weight p σ B) (ψ : Weight t τ B), WOver φ ψ → ∀ (r : B.ι → X.functionFieldˣ) (hr : IsRatSec B r) (σ : k →+* ℂ) (y : CxPts p σ), y ∈ offSupp p σ (divOfRatSec ψ.isLB hr) → logNorm ψ r (sheet t τ y) = logNorm (φ σ) r y := by
  intro k _ X _ p t τ B φ ψ h r hr σ y hy
  have hy' : sheet t τ y ∈ offSupp t τ (divOfRatSec ψ.isLB hr) := mem_offSupp.2 (mem_offSupp.1 hy)
  have hi' := mem_pick ψ.isLB (sheet t τ y)
  set i := pick ψ.isLB (sheet t τ y)
  have hi : y ∈ ptsIn p σ (B.U i) := mem_ptsIn.2 (mem_ptsIn.1 hi')
  rw [logNorm_eq ψ hr hy' hi', logNorm_eq (φ σ) hr hy hi, h σ i y hi]
  congr 3
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogNormSheetEqStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logNorm_sheet_eq : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ) (B : LB X) (φ : ∀ σ : k →+* ℂ, Weight p σ B) (ψ : Weight t τ B), WOver φ ψ → ∀ (r : B.ι → X.functionFieldˣ) (hr : IsRatSec B r) (σ : k →+* ℂ) (y : CxPts p σ), y ∈ offSupp p σ (divOfRatSec ψ.isLB hr) → logNorm ψ r (sheet t τ y) = logNorm (φ σ) r y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BaseZ.logNorm_sheet | exact GlobalTheory.CompanionTheory.Ar.BaseZ.logNorm_sheet | (intros; apply GlobalTheory.CompanionTheory.Ar.BaseZ.logNorm_sheet <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ToZPowCombIsometric
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ToZIsometric
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

namespace GlobalTheory.CompanionTheory.Ar.BaseZ

theorem toZ_isometric : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (L M : HermLB p)
    (hL : ∀ τ, (wZ L t τ).IsCInf) (hM : ∀ τ, (wZ M t τ).IsCInf), L.Isometric M →
    (toZ L t hL).Isometric (toZ M t hM) := by
  intro k _ X p t L M hL hM ⟨w, hw, h⟩
  refine ⟨w, hw, fun τ a b y ha hb => ?_⟩
  exact h (emb p y) a b (unsheet p y) ha hb

end GlobalTheory.CompanionTheory.Ar.BaseZ
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ToZPowCombIsometric
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

namespace GlobalTheory.CompanionTheory.Ar.BaseZ

section

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {t : X ⟶ Sp ℤ}

theorem toZ_tens_isometric (L M : HermLB p) (hLM : ∀ τ, (wZ (L.tens M) t τ).IsCInf)
    (hL : ∀ τ, (wZ L t τ).IsCInf) (hM : ∀ τ, (wZ M t τ).IsCInf) :
    (toZ (L.tens M) t hLM).Isometric ((toZ L t hL).tens (toZ M t hM)) :=
  HermLB.isometric_of_eqOn fun _ _ _ _ => rfl

noncomputable def toZClass (t : X ⟶ Sp ℤ) (H : ∀ (L : HermLB p) (τ : ℤ →+* ℂ), (wZ L t τ).IsCInf) :
    HermLB.IsomClass p →+ HermLB.IsomClass t :=
  AddMonoidHom.mk' (M := HermLB.IsomClass p) (G := HermLB.IsomClass t)
    (Quotient.map (sa := HermLB.isometrySetoid p) (sb := HermLB.isometrySetoid t)
      (fun L => toZ L t (H L)) fun L M h => toZ_isometric k X p t L M (H L) (H M) h)
    (by
      rintro ⟨L⟩ ⟨M⟩
      exact HermLB.icls_eq_iff.2 (toZ_tens_isometric L M (H _) (H _) (H _)))

theorem toZClass_icls (H : ∀ (L : HermLB p) (τ : ℤ →+* ℂ), (wZ L t τ).IsCInf) (L : HermLB p) :
    toZClass t H L.icls = (toZ L t (H L)).icls := rfl

end

theorem toZ_pow_comb : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ)
    (H : ∀ (L : HermLB p) (τ : ℤ →+* ℂ), (wZ L t τ).IsCInf),
    (∀ (L : HermLB p) (m : ℕ), (toZ (L.pow m) t (H _)).Isometric ((toZ L t (H _)).pow m)) ∧
    ∀ (ι : Type) [Fintype ι] (L : ι → HermLB p) (n : ι → ℤ),
      (toZ (ArInt.comb L n) t (H _)).Isometric (ArInt.comb (fun i => toZ (L i) t (H _)) n) := by
  intro k _ X p t H
  refine ⟨fun L m => HermLB.icls_eq_iff.1 ?_, fun ι _ L n => HermLB.icls_eq_iff.1 ?_⟩
  · rw [← toZClass_icls H, HermLB.icls_pow, HermLB.icls_pow, map_nsmul, toZClass_icls H]
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [← toZClass_icls H, ArInt.icls_comb, ArInt.icls_comb, map_sum]
      simp only [map_zsmul, toZClass_icls H]

end GlobalTheory.CompanionTheory.Ar.BaseZ
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ToZPowCombIsometricStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toZ_pow_comb_isometric : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (H : ∀ (L : HermLB p) (τ : ℤ →+* ℂ), (wZ L t τ).IsCInf), (∀ (L : HermLB p) (m : ℕ), (toZ (L.pow m) t (H _)).Isometric ((toZ L t (H _)).pow m)) ∧ ∀ (ι : Type) [Fintype ι] (L : ι → HermLB p) (n : ι → ℤ), (toZ (comb L n) t (H _)).Isometric (comb (fun i => toZ (L i) t (H _)) n) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BaseZ.toZ_pow_comb | exact GlobalTheory.CompanionTheory.Ar.BaseZ.toZ_pow_comb | (intros; apply GlobalTheory.CompanionTheory.Ar.BaseZ.toZ_pow_comb <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SheetIsOpenEmbeddingRange
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SheetIsOpenEmbeddingRange
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BaseZ.Sheet

theorem finite_ringHom (k : Type) [CommRing k] [Module.Finite ℤ k] : Finite (k →+* ℂ) := by
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ k).FG)
  have hroot : ∀ a : k, ∃ S : Set ℂ, S.Finite ∧ ∀ σ : k →+* ℂ, σ a ∈ S := by
    intro a
    obtain ⟨P, hm, hP⟩ := (Algebra.IsIntegral.isIntegral a : IsIntegral ℤ a)
    refine ⟨{z | (P.map (Int.castRingHom ℂ)).IsRoot z}, ?_, fun σ => ?_⟩
    · exact Polynomial.finite_setOf_isRoot (hm.map _).ne_zero
    · have h : Polynomial.eval₂ (σ.comp (algebraMap ℤ k)) (σ a) P = 0 := by
        rw [← Polynomial.hom_eval₂, hP, map_zero]
      rw [Subsingleton.elim (σ.comp (algebraMap ℤ k)) (Int.castRingHom ℂ)] at h
      simpa [Polynomial.IsRoot, Polynomial.eval_map] using h
  choose S hS hm using hroot
  have : ∀ i : s, Finite (S i) := fun i => (hS i).to_subtype
  refine Finite.of_injective (fun (σ : k →+* ℂ) (i : s) => (⟨σ i, hm i σ⟩ : S i)) fun σ₁ σ₂ h => ?_
  have hs' : ∀ i ∈ s, σ₁ i = σ₂ i := fun i hi => congrArg Subtype.val (congrFun h ⟨i, hi⟩)
  have hspan : ∀ x ∈ Submodule.span ℤ (s : Set k), σ₁ x = σ₂ x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x h => exact hs' x h
    | zero => simp
    | add x y _ _ hx hy => simp [map_add (f := _), hx, hy]
    | smul a x _ hx => simp [map_zsmul, hx]
  exact RingHom.ext fun x => hspan x (hs ▸ Submodule.mem_top)

variable {k : Type} [CommRing k] {X : Scheme.{0}}

theorem emb_apply (p : X ⟶ Sp k) {t : X ⟶ Sp ℤ} {τ : ℤ →+* ℂ} (y : CxPts t τ) (a : k) :
    emb p y a = ev t τ ⊤ (algX p ⊤ a) y :=
  (ev_algX (y := unsheet p y) mem_ptsIn_top a).symm

theorem range_sheet (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ) (σ : k →+* ℂ) :
    Set.range (sheet t τ : CxPts p σ → CxPts t τ) = {y | emb p y = σ} := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact emb_sheet t τ z
  · intro h
    have h' : emb p y = σ := h
    subst h'
    exact ⟨unsheet p y, rfl⟩

theorem isOpen_emb_eq [Finite (k →+* ℂ)] (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ) (σ : k →+* ℂ) :
    IsOpen {y : CxPts t τ | emb p y = σ} := by
  have hc (a : k) : Continuous fun y : CxPts t τ => emb p y a := by
    simp only [emb_apply]
    exact (Points.continuous_valR_top _).comp continuous_subtype_val
  have e : {y : CxPts t τ | emb p y = σ} =
      ⋂ σ' : {s : k →+* ℂ // s ≠ σ}, ⋃ a : k, {y | emb p y a ≠ σ'.1 a} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion]
    constructor
    · rintro rfl σ'
      by_contra h
      push Not at h
      exact σ'.2 (RingHom.ext fun a => (h a).symm)
    · intro h
      by_contra he
      obtain ⟨a, ha⟩ := h ⟨_, he⟩
      exact ha rfl
  rw [e]
  exact isOpen_iInter_of_finite fun σ' => isOpen_iUnion fun a => isOpen_ne_fun (hc a) continuous_const

theorem isOpenEmbedding_and_range : ∀ (k : Type) [CommRing k] [Module.Finite ℤ k] (X : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ) (σ : k →+* ℂ), Topology.IsOpenEmbedding (sheet t τ : CxPts p σ → CxPts t τ) ∧ Set.range (sheet t τ : CxPts p σ → CxPts t τ) = {y | emb p y = σ} := by
  intro k _ _ X p t τ σ
  have := finite_ringHom k
  have hr := range_sheet p t τ σ
  refine ⟨⟨IsEmbedding.of_comp (continuous_subtype_val.subtype_mk _) continuous_subtype_val
    IsEmbedding.subtypeVal, ?_⟩, hr⟩
  rw [hr]
  exact isOpen_emb_eq p t τ σ

end GlobalTheory.CompanionTheory.Ar.BaseZ.Sheet
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SheetIsOpenEmbeddingRangeStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sheet_isOpenEmbedding_range : ∀ (k : Type) [CommRing k] [Module.Finite ℤ k] (X : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ) (σ : k →+* ℂ), Topology.IsOpenEmbedding (sheet t τ : CxPts p σ → CxPts t τ) ∧ Set.range (sheet t τ : CxPts p σ → CxPts t τ) = {y | emb p y = σ} := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BaseZ.Sheet.isOpenEmbedding_and_range | exact GlobalTheory.CompanionTheory.Ar.BaseZ.Sheet.isOpenEmbedding_and_range | (intros; apply GlobalTheory.CompanionTheory.Ar.BaseZ.Sheet.isOpenEmbedding_and_range <;> assumption)
end
end
