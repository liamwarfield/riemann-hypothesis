module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionTowerPresentationCotangentPullbackResRigi
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisQuotientAffineOpenSpecInvariants
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.DivisorCenterProperLift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleRigidFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeakResolutionOfPrincipalisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldMapBijectiveOfIsIsoRestrictStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantOfIsIsoRestrictStatement

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.FormOrderBirationalPullback
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.form_order_birational_pullback : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s], Function.Bijective (functionFieldMap s) → ∀ (E' : DivOver (s ≫ p)) (E : DivOver p), DivOver.Over s E' E → ∀ (n : ℕ) (η : RatForms p n), η ≠ 0 → (fun ω => @dite ℤ (∃ a, E'.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (EtaleKlt.ratPull p s n η) = (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) η := by
  first | exact @_root_.GlobalTheory.BirOrd.formOrd_ratPull_of_over | exact _root_.GlobalTheory.BirOrd.formOrd_ratPull_of_over | (intros; apply _root_.GlobalTheory.BirOrd.formOrd_ratPull_of_over <;> assumption)
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsSncChart
section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.RegularSequenceExtendCoords
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.regular_sequence_extend_coords : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q] (y : Y) (U : Y.affineOpens) (hy : y ∈ U.1) (c : ℕ) (a : Fin c → Γ(Y, U.1)), FinalTheorems.Rsp (Y.presheaf.stalk y) c (fun i => Y.presheaf.germ U.1 y hy (a i)) → ∃ (V : Y.Opens) (hV : V ≤ U.1) (_ : y ∈ V) (z : Fin n → Γ(Y, V)) (e : Fin c ↪ Fin n), (∀ j, z (e j) = resG Y hV (a j)) ∧ IsFrame (dOn q z) := by
  first | exact @_root_.GlobalTheory.ParamFrame.exists_frame_of_rsp | exact _root_.GlobalTheory.ParamFrame.exists_frame_of_rsp | (intros; apply _root_.GlobalTheory.ParamFrame.exists_frame_of_rsp <;> assumption)
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsSncChart
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy

theorem not_mem_basicOpen_prod {Y : Scheme.{0}} {U : Y.Opens} {v : Y} (hv : v ∈ U) {c : ℕ}
    (f : Fin c → Γ(Y, U)) (s : Finset (Fin c)) :
    v ∉ Y.basicOpen (∏ i ∈ s, f i) ↔ ∃ i ∈ s, v ∉ Y.basicOpen (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.notMem_empty, false_and, exists_false, iff_false, not_not]
    rw [Scheme.basicOpen_of_isUnit Y isUnit_one]
    exact hv
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Scheme.basicOpen_mul]
    simp only [TopologicalSpace.Opens.mem_inf, not_and_or, ih, Finset.mem_insert,
      exists_eq_or_imp]

theorem exists_isSncChart (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) [IsIntegral Y]
    [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q] (B : Closeds Y)
    (hB : FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal B)) (y : Y) :
    ∃ (U : Y.Opens) (hy : y ∈ U) (z : Fin n → Γ(Y, U)) (J : Finset (Fin n)) (w : Fin n → Y)
      (u : Fin n → Y.functionFieldˣ), IsSncChart q n B y U hy z J w u := by
  classical
  obtain ⟨hreg, U, hyU, c, f, J₀, hrsp, hid⟩ := hB y
  obtain ⟨V, hV, hyV, z, e, hz, hframe⟩ := GlobalTheory.T.regular_sequence_extend_coords k Y q n y U hyU c f hrsp
  obtain ⟨w₀, u₀, hinj, hw⟩ := GlobalTheory.T.regular_sequence_prime_divisors Y y U.1 hyU c f hreg hrsp
  have hwe : ∀ i, Function.extend e w₀ (fun _ => y) (e i) = w₀ i :=
    fun i => e.injective.extend_apply _ _ i
  have hue : ∀ i, Function.extend e u₀ (fun _ => 1) (e i) = u₀ i :=
    fun i => e.injective.extend_apply _ _ i

  have hB' : ∀ v, v ∈ U.1 → (v ∈ B ↔ ∃ i ∈ J₀, v ∉ Y.basicOpen (f i)) := by
    intro v hv
    have h1 : v ∈ B ↔ v ∈ (Scheme.IdealSheafData.vanishingIdeal B).support := Iff.rfl
    rw [h1, Scheme.IdealSheafData.mem_support_iff_of_mem (U := U) hv, hid, Scheme.zeroLocus_span,
      Scheme.zeroLocus_singleton]
    exact not_mem_basicOpen_prod hv f J₀
  refine ⟨V, hyV, z, J₀.map e, Function.extend e w₀ (fun _ => y),
    Function.extend e u₀ (fun _ => 1), ⟨hframe, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro j hj
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hj
    rw [hue, (hw i).1, hz, fnOf_resG]
  · intro j hj
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hj
    rw [hwe]; exact (hw i).2.1
  · intro j hj
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hj
    rw [hwe]; exact (hw i).2.2.1
  · intro a ha b hb hab
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 (Finset.mem_coe.1 ha)
    obtain ⟨i', -, rfl⟩ := Finset.mem_map.1 (Finset.mem_coe.1 hb)
    rw [hwe, hwe] at hab
    rw [hinj hab]
  · intro j hj
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hj
    rw [hwe, hue]; exact (hw i).2.2.2.2.1
  · intro j hj v hvy hne
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hj
    rw [hwe] at hne
    rw [hue]
    by_cases hc : Order.coheight v = 1
    · have hvU : v ∈ U.1 := hvy.mem_open U.1.isOpen hyU
      have hb : v ∈ Y.basicOpen (f i) := (hw i).2.2.2.2.2 v hvy hc hne
      rw [(hw i).1]
      exact UnitAt.ord_eq_zero ((unitAt_fnOf_iff hvU _ _).2 hb)
    · exact Scheme.ord_eq_zero_of_coheight_neq_one hc _
  · intro v hvy hc
    have hvU : v ∈ U.1 := hvy.mem_open U.1.isOpen hyU
    rw [hB' v hvU]
    constructor
    · rintro ⟨i, hi, hnot⟩
      refine ⟨e i, Finset.mem_map_of_mem e hi, ?_⟩
      rw [hwe]
      by_contra hne
      exact hnot ((hw i).2.2.2.2.2 v hvy hc hne)
    · rintro ⟨j, hj, rfl⟩
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.1 hj
      rw [hwe]
      exact ⟨i, hi, (hw i).2.2.2.1⟩

end GlobalTheory.Discrepancy
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsSncChartStatement
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.exists_snc_chart : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q] (B : Closeds Y), FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal B) → ∀ y : Y, ∃ (U : Y.Opens) (hy : y ∈ U) (z : Fin n → Γ(Y, U)) (J : Finset (Fin n)) (w : Fin n → Y) (u : Fin n → Y.functionFieldˣ), IsSncChart q n B y U hy z J w u := by
  first | exact @_root_.GlobalTheory.Discrepancy.exists_isSncChart | exact _root_.GlobalTheory.Discrepancy.exists_isSncChart | (intros; apply _root_.GlobalTheory.Discrepancy.exists_isSncChart <;> assumption)
end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CanonicalDivisorOfForm
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.canonical_divisor_of_form : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q] (η : RatForms q n), η ≠ 0 → (∃ K : CartierDiv Y, IsDivOfForm K η) ∧ ∀ K : CartierDiv Y, IsDivOfForm K η → ∀ Kc : CanonLB q n, toPic K = cls Kc.bundle Kc.isLB := by
  first | exact @_root_.GlobalTheory.Discrepancy.exists_isDivOfForm_and_toPic | exact _root_.GlobalTheory.Discrepancy.exists_isDivOfForm_and_toPic | (intros; apply _root_.GlobalTheory.Discrepancy.exists_isDivOfForm_and_toPic <;> assumption)
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsSmoothProjectiveModel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothProjectiveModel
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.BirModel

theorem exists_smooth_projective_model : GlobalTheory.Published.Principalisation → ∀ (k : Type) [Field k] [CharZero k]
    (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → topologicalKrullDim X = n →
    ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (s : Y ⟶ X) (_ : IsDominant s), SmoothOfRelativeDimension n (s ≫ p) ∧
      IsProjOver (s ≫ p) ∧ Function.Bijective (functionFieldMap s) := by
  intro hP k _ _ X _ p n hp hdim
  obtain ⟨Y, s, U, hY, hsm, hpr, hU, hiso⟩ := GlobalTheory.WeakRes.weak_resolution hP k X p n hp hdim
  have hdom : IsDominant s := GlobalTheory.T.isDominant_of_isIso_restrict' X Y s U hU hiso
  exact ⟨Y, hY, s, hdom, hsm, hpr, GlobalTheory.T.functionFieldMap_bijective_of_isIso_restrict' X Y s U hU hiso⟩

end GlobalTheory.BirModel
end

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.exists_smooth_projective_birational_model : GlobalTheory.Published.Principalisation → ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (s : Y ⟶ X) (_ : IsDominant s), SmoothOfRelativeDimension n (s ≫ p) ∧ IsProjOver (s ≫ p) ∧ Function.Bijective (functionFieldMap s) := by
  first | exact @_root_.GlobalTheory.BirModel.exists_smooth_projective_model | exact _root_.GlobalTheory.BirModel.exists_smooth_projective_model | (intros; apply _root_.GlobalTheory.BirModel.exists_smooth_projective_model <;> assumption)
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.DivisorPointProperLift
section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.DivisorPointProperLift
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

namespace GlobalTheory.Discrepancy

theorem DivOver.isAt_lift : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y]
    (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s], Function.Bijective (functionFieldMap s) →
    IsProper s → ∀ (E' : DivOver (s ≫ p)) (E : DivOver p), DivOver.Over s E' E →
    ∀ z : X, E.IsAt z → ∃ w : Y, s w = z ∧ E'.IsAt w := by
  intro k _ X Y _ _ p s _ hbij hprop E' E hOver z hz
  obtain ⟨w, hw, hwt⟩ := GlobalTheory.T.divisor_center_proper_lift k X Y p s hbij hprop E' E hOver z
    (hz.through specializes_rfl)
  subst hw
  refine ⟨w, rfl, fun f => ⟨fun hf => ?_, hwt f⟩⟩
  obtain ⟨g, rfl⟩ := hbij.2 f
  obtain ⟨a, rfl⟩ := (hz g).1 ((hOver g).2 hf)
  exact ⟨s.stalkMap w a, (GlobalTheory.functionFieldMap_algebraMap s w a).symm⟩

end GlobalTheory.Discrepancy
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.DivisorPointProperLiftStatement
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.divisor_point_proper_lift : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s], Function.Bijective (functionFieldMap s) → IsProper s → ∀ (E' : DivOver (s ≫ p)) (E : DivOver p), DivOver.Over s E' E → ∀ z : X, E.IsAt z → ∃ w : Y, s w = z ∧ E'.IsAt w := by
  first | exact @_root_.GlobalTheory.Discrepancy.DivOver.isAt_lift | exact _root_.GlobalTheory.Discrepancy.DivOver.isAt_lift | (intros; apply _root_.GlobalTheory.Discrepancy.DivOver.isAt_lift <;> assumption)
end
end
