module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendRegularThetaSectionAnyFractionField

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveChartCoordinateRatioMemModelRing
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveChartCoordinateRatioMemModelRing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.ChartDiv

theorem chart_ratio_mem_O : ∀ (k Ω : Type) [CommRing k] [Field Ω] [Algebra k Ω] (M : RatModel k Ω) (n : ℕ) (c : Fin (n + 1) → Ω) (h : M.Z ⟶ PSpace k n) (a : Fin (n + 1)) (z : M.Z), PCrd (M.pt ≫ h) c → z ∈ h ⁻¹ᵁ chart k n a → c a ≠ 0 ∧ ∀ z' ∈ h ⁻¹ᵁ chart k n a, ∀ b, c b / c a ∈ M.O z' := by
  intro k Ω _ _ _ M n c h a z hc hz
  have hx : ⊤ ≤ (M.pt ≫ h) ⁻¹ᵁ chart k n a := M.top_le_preimage_pt (U := h ⁻¹ᵁ chart k n a) ⟨z, hz⟩
  obtain ⟨ha, hb⟩ := GlobalTheory.UMin.CrdChart.pCrd_chart k Ω n (M.pt ≫ h) c a hc hx
  refine ⟨ha, fun z' hz' b => ?_⟩
  rw [← hb b, Points.valR_comp, ← Points.valF_eq_valR]
  exact RatModel.valF_mem_O hz' _

end GlobalTheory.UMin.ChartDiv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveChartCoordinateRatioMemModelRingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projective_chart_coordinate_ratio_mem_model_ring : ∀ (k Ω : Type) [CommRing k] [Field Ω] [Algebra k Ω] (M : RatModel k Ω) (n : ℕ) (c : Fin (n + 1) → Ω) (h : M.Z ⟶ PSpace k n) (a : Fin (n + 1)) (z : M.Z), PCrd (M.pt ≫ h) c → z ∈ h ⁻¹ᵁ chart k n a → c a ≠ 0 ∧ ∀ z' ∈ h ⁻¹ᵁ chart k n a, ∀ b, c b / c a ∈ M.O z' := by
  first | exact @GlobalTheory.UMin.ChartDiv.chart_ratio_mem_O | exact GlobalTheory.UMin.ChartDiv.chart_ratio_mem_O | (intros; apply GlobalTheory.UMin.ChartDiv.chart_ratio_mem_O <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenImmersionSpecRingOnAffine
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenImmersionSpecRingOnAffine
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Div.AffChart

open GlobalTheory.Points

theorem exists_openImm_spec_ringOn (k Ω : Type) [CommRing k] [Field Ω] [Algebra k Ω] (M : RatModel k Ω)
    (W : M.Z.Opens) (hW : IsAffineOpen W) (hne : (W : Set M.Z).Nonempty) :
    ∃ (χ : Sp (M.ringOn W) ⟶ M.Z) (_ : IsOpenImmersion χ), χ.opensRange = W ∧
      spMap (algebraMap (M.ringOn W) Ω) ≫ χ = M.pt := by
  let φ : Γ(M.Z, W) ⟶ CommRingCat.of (M.ringOn W) := (M.sectionsEquiv W hne).toCommRingCatIso.hom
  haveI : IsIso φ := inferInstanceAs (IsIso (M.sectionsEquiv W hne).toCommRingCatIso.hom)
  refine ⟨Spec.map φ ≫ hW.fromSpec, inferInstance, ?_, ?_⟩
  · rw [Scheme.Hom.opensRange_comp_of_isIso, hW.opensRange_fromSpec]
  · have hp := M.top_le_preimage_pt hne
    have e : φ ≫ CommRingCat.ofHom (algebraMap (M.ringOn W) Ω) = valMap M.pt W hp := by
      ext f
      exact (M.coe_sectionsEquiv W hne f).trans (M.res_apply W hne f).symm
    rw [spMap, ← Category.assoc, ← Spec.map_comp, e, specMap_valMap_fromSpec]

end GlobalTheory.Div.AffChart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenImmersionSpecRingOnAffineStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_openImmersion_spec_ringOn_affine : ∀ (k Ω : Type) [CommRing k] [Field Ω] [Algebra k Ω] (M : RatModel k Ω) (W : M.Z.Opens), IsAffineOpen W → (W : Set M.Z).Nonempty → ∃ (χ : Sp (M.ringOn W) ⟶ M.Z) (_ : IsOpenImmersion χ), χ.opensRange = W ∧ spMap (algebraMap (M.ringOn W) Ω) ≫ χ = M.pt := by
  first | exact @GlobalTheory.Div.AffChart.exists_openImm_spec_ringOn | exact GlobalTheory.Div.AffChart.exists_openImm_spec_ringOn | (intros; apply GlobalTheory.Div.AffChart.exists_openImm_spec_ringOn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineNbhdNoetherianIntegrallyClosed
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineNbhdNoetherianIntegrallyClosed
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.ZH.RatModel.exists_isAffineOpen_noetherian_integrallyClosed : ∀ (k Ω : Type) [CommRing k] [IsNoetherianRing k] [Field Ω] [Algebra k Ω] (M : RatModel k Ω), Geo.Tor.IsNormalScheme M.Z → ∀ (V : M.Z.Opens) (z : M.Z), z ∈ V → ∃ W : M.Z.Opens, IsAffineOpen W ∧ z ∈ W ∧ W ≤ V ∧ IsNoetherianRing (M.ringOn W) ∧ IsIntegrallyClosed (M.ringOn W) := by
  intro k Ω _ _ _ _ M hn V z hz
  obtain ⟨W, hW, hzW, hWV⟩ := exists_isAffineOpen_mem_and_subset (U := V) hz
  have hWV' : W ≤ V := hWV
  have hne : ((W : M.Z.Opens) : Set M.Z).Nonempty := ⟨z, hzW⟩
  refine ⟨W, hW, hzW, hWV', ?_, ?_⟩
  · have h1 : (M.s.appLE ⊤ W le_top).hom.FiniteType :=
      HasRingHomProperty.appLE @LocallyOfFiniteType M.s M.lft ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ le_top
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.FiniteType :=
      RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.surjective
    have h4 := h1.comp h2
    letI := ((M.s.appLE ⊤ W le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).toAlgebra
    haveI : Algebra.FiniteType k Γ(M.Z, W) := h4
    haveI : IsNoetherianRing Γ(M.Z, W) := Algebra.FiniteType.isNoetherianRing k _
    exact isNoetherianRing_of_ringEquiv _ (M.sectionsEquiv W hne)
  · haveI := GlobalTheory.ZH.RatModel.isFractionRing_ringOn hW hne
    refine (isIntegrallyClosed_iff Ω).2 fun {x} hx => ?_
    have hmem : x ∈ M.ringOn W := GlobalTheory.ZH.RatModel.mem_ringOn.2 fun z' hz' => by
      haveI := GlobalTheory.ZH.RatModel.isIntegrallyClosed_O hn z'
      have hle := GlobalTheory.ZH.RatModel.ringOn_le_O (M := M) hz'
      letI : Algebra (M.ringOn W) (M.O z') := (Subalgebra.inclusion hle).toRingHom.toAlgebra
      haveI : IsScalarTower (M.ringOn W) (M.O z') Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
      have hx' : IsIntegral (M.O z') x := hx.tower_top
      obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hx'
      rw [← hy]
      exact y.2
    exact ⟨⟨x, hmem⟩, rfl⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineNbhdNoetherianIntegrallyClosedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_nbhd_noetherian_integrallyClosed : ∀ (k Ω : Type) [CommRing k] [IsNoetherianRing k] [Field Ω] [Algebra k Ω] (M : RatModel k Ω), Geo.Tor.IsNormalScheme M.Z → ∀ (V : M.Z.Opens) (z : M.Z), z ∈ V → ∃ W : M.Z.Opens, IsAffineOpen W ∧ z ∈ W ∧ W ≤ V ∧ IsNoetherianRing (M.ringOn W) ∧ IsIntegrallyClosed (M.ringOn W) := by
  first | exact @GlobalTheory.ZH.RatModel.exists_isAffineOpen_noetherian_integrallyClosed | exact GlobalTheory.ZH.RatModel.exists_isAffineOpen_noetherian_integrallyClosed | (intros; apply GlobalTheory.ZH.RatModel.exists_isAffineOpen_noetherian_integrallyClosed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSectionOfOpenImmersionSpec
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSectionOfOpenImmersionSpec
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.LocSecOfImm

theorem bij_appLE {X Y : Scheme.{0}} (q : X ⟶ Y) [IsOpenImmersion q] (U : Y.Opens) (hU : U ≤ q.opensRange)
    (V : X.Opens) (h : V ≤ q ⁻¹ᵁ U) (h' : q ⁻¹ᵁ U ≤ V) : Function.Bijective (q.appLE U V h).hom := by
  obtain rfl : V = q ⁻¹ᵁ U := le_antisymm h h'
  have := q.isIso_app U hU
  rw [Scheme.Hom.appLE_eq_app]
  exact ConcreteCategory.bijective_of_isIso (q.app U)

theorem appLE_res {X Y : Scheme.{0}} (q : X ⟶ Y) {U U' : Y.Opens} {V : X.Opens} (h : U' ≤ U) (e : V ≤ q ⁻¹ᵁ U')
    (e' : V ≤ q ⁻¹ᵁ U) (a : Γ(Y, U)) : (q.appLE U' V e).hom (resG Y h a) = (q.appLE U V e').hom a :=
  congrArg (fun φ => CommRingCat.Hom.hom φ a) (q.map_appLE e (homOfLE h).op)

theorem res_appLE {X Y : Scheme.{0}} (q : X ⟶ Y) {U : Y.Opens} {V V' : X.Opens} (h : V' ≤ V) (e : V ≤ q ⁻¹ᵁ U)
    (e' : V' ≤ q ⁻¹ᵁ U) (a : Γ(Y, U)) : resG X h ((q.appLE U V e).hom a) = (q.appLE U V' e').hom a :=
  congrArg (fun φ => CommRingCat.Hom.hom φ a) (q.appLE_map e (homOfLE h).op)

theorem appLE_appLE {X Y Z : Scheme.{0}} (p : X ⟶ Y) (q : Y ⟶ Z) (r : X ⟶ Z) (hr : p ≫ q = r) {U : Z.Opens}
    {V : Y.Opens} {W : X.Opens} (e₁ : V ≤ q ⁻¹ᵁ U) (e₂ : W ≤ p ⁻¹ᵁ V) (e₃ : W ≤ r ⁻¹ᵁ U) (a : Γ(Z, U)) :
    (p.appLE V W e₂).hom ((q.appLE U V e₁).hom a) = (r.appLE U W e₃).hom a := by
  subst hr
  exact congrArg (fun φ => CommRingCat.Hom.hom φ a) (Scheme.Hom.appLE_comp_appLE p q U V W e₁ e₂)

theorem valF_ne_zero_of_le {F : Type} [Field F] {X : Scheme.{0}} {x : Sp F ⟶ X} {U : X.Opens} (a : Γ(X, U))
    (hle : ⊤ ≤ x ⁻¹ᵁ X.basicOpen a) : valF x U a ≠ 0 := by
  have h : ⊤ ≤ x ⁻¹ᵁ U := hle.trans (Scheme.Hom.preimage_mono _ (X.basicOpen_le a))
  have e1 := Scheme.basicOpen_appLE x ⊤ U h a
  rw [top_inf_eq] at e1
  have e2 : (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (valF x U a) = (x.appLE U ⊤ h).hom a := by
    rw [valF, dite_eq_left h]
    exact (Scheme.ΓSpecIso (CommRingCat.of F)).hom_inv_id_apply _
  have e3 : x ⁻¹ᵁ X.basicOpen a =
      (Sp F).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (valF x U a)) := by
    rw [e2]; exact e1.symm
  intro h0
  rw [e3, h0, map_zero, Scheme.basicOpen_zero] at hle
  exact hle (show (IsLocalRing.closedPoint F : Sp F) ∈ (⊤ : (Sp F).Opens) from trivial)

theorem exists_point {X Y : Scheme.{0}} {K : Type} [Field K] [IsAlgClosed K] (π : X ⟶ Y) [LocallyOfFiniteType π]
    (x : Sp K ⟶ Y) (O : X.Opens) (p : X) (hp : p ∈ O) (hx : π p = x (IsLocalRing.closedPoint K)) :
    ∃ g : Sp K ⟶ X, g ≫ π = x ∧ ⊤ ≤ g ⁻¹ᵁ O := by
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := π) (g := x) p (IsLocalRing.closedPoint K) hx
  have := LocallyOfFiniteType.jacobsonSpace (pullback.snd π x)
  obtain ⟨c, hcO, hc'⟩ := nonempty_inter_closedPoints (Z := (pullback.fst π x ⁻¹ᵁ O : Set _))
    ⟨z, show pullback.fst π x z ∈ O from hz ▸ hp⟩ (pullback.fst π x ⁻¹ᵁ O).isOpen.isLocallyClosed
  have hc : IsClosed {c} := hc'
  refine ⟨pointOfClosedPoint (pullback.snd π x) c hc ≫ pullback.fst π x, ?_, fun a _ => ?_⟩
  · rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]
  · show pullback.fst π x (pointOfClosedPoint (pullback.snd π x) c hc a) ∈ O
    rw [pointOfClosedPoint_apply]
    exact hcO

theorem exists_locSec : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (R : Type) [CommRing R] (χ : Sp R ⟶ S) [IsOpenImmersion χ] (σ : SecAt G L χ), LocallyOfFiniteType G.hom → (∀ s : Sp R, ∃ z : (Over.mk χ ⊗ G).left, (fst (Over.mk χ) G).left z = s ∧ z ∈ nonzeroLocus σ) → ∃ s : LocSec G L χ.opensRange, IsLocSec s ∧ (∀ (K : Type) [Field K] (i : R →+* K), GenIs (spMap i ≫ χ) s (SecM.ofSec G (SecAt.pull G L σ i))) ∧ FibNz s χ.opensRange := by
  intro S G _ L R _ χ _ σ hft hnz
  let q : (Over.mk χ ⊗ G).left ⟶ G.left := (snd (Over.mk χ) G).left
  have hq : IsOpenImmersion q := inferInstanceAs (IsOpenImmersion (pullback.snd χ G.hom))
  have ew : q ≫ G.hom = (fst (Over.mk χ) G).left ≫ χ :=
    (Over.w (snd (Over.mk χ) G)).trans (Over.w (fst (Over.mk χ) G)).symm
  have hN : ∀ y, G.hom (q y) ∈ χ.opensRange := fun y => by
    rw [← Scheme.Hom.comp_apply, ew, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  have hrange : G.hom ⁻¹ᵁ χ.opensRange ≤ q.opensRange := fun y hy =>
    (Scheme.Pullback.range_snd χ G.hom).ge hy
  have hle : ∀ j : Fin 1 → L.ι, (LPow G L ((1 : ℕ) : ℤ) (Over.mk χ)).U j ≤
      q ⁻¹ᵁ (L.U (j 0) ⊓ G.hom ⁻¹ᵁ χ.opensRange) := fun j y hy => ⟨Set.mem_iInter.1 hy 0, hN y⟩
  have hbij : ∀ i : L.ι, Function.Bijective (q.appLE (L.U i ⊓ G.hom ⁻¹ᵁ χ.opensRange)
      ((LPow G L ((1 : ℕ) : ℤ) (Over.mk χ)).U fun _ => i) (hle fun _ => i)).hom := fun i =>
    bij_appLE q _ (inf_le_right.trans hrange) _ _ fun y hy => Set.mem_iInter.2 fun _ => hy.1
  choose s hs using fun i : L.ι => (hbij i).2 (σ.f fun _ => i)
  have hs' : ∀ j : Fin 1 → L.ι, (q.appLE _ _ (hle j)).hom (s (j 0)) = σ.f j := fun j => by
    obtain ⟨i, rfl⟩ : ∃ i, j = fun _ => i := ⟨j 0, funext fun k => congrArg j (Subsingleton.elim _ _)⟩
    exact hs i
  refine ⟨s, fun i j => ?_, fun K _ i => ⟨?_, funext fun j => ?_⟩, fun K _ _ x hx => ?_⟩
  · have hV : (LPow G L ((1 : ℕ) : ℤ) (Over.mk χ)).U (fun _ => i) ⊓ (LPow G L ((1 : ℕ) : ℤ) (Over.mk χ)).U (fun _ => j) ≤
        q ⁻¹ᵁ (L.U i ⊓ L.U j ⊓ G.hom ⁻¹ᵁ χ.opensRange) := fun y hy =>
      ⟨⟨Set.mem_iInter.1 hy.1 0, Set.mem_iInter.1 hy.2 0⟩, hN y⟩
    refine (bij_appLE q _ (inf_le_right.trans hrange) _ hV fun y hy =>
      ⟨Set.mem_iInter.2 fun _ => hy.1.1, Set.mem_iInter.2 fun _ => hy.1.2⟩).1 ?_
    have hc := σ.compat (fun _ => i) (fun _ => j)
    rw [← hs i, ← hs j] at hc
    rw [map_mul]
    refine (appLE_res q _ _ (inf_le_left.trans (hle fun _ => i)) _).trans
      (((res_appLE q _ _ _ _).symm.trans hc).trans (congrArg₂ (· * ·) ?_ ?_))
    · refine Eq.trans ?_ (appLE_res q _ _ (hV.trans (Scheme.Hom.preimage_mono _ inf_le_left)) _).symm
      simp only [LPow, LB.LinComb, Fin.prod_univ_one, Nat.cast_one, zpow_one]
      rfl
    · exact (res_appLE q _ _ (inf_le_right.trans (hle fun _ => j)) _).trans (appLE_res q _ _ _ _).symm
  · rintro _ ⟨y, rfl⟩
    exact ⟨spMap i y, (Scheme.Hom.comp_apply _ _ _).symm⟩
  · show genPull _ s j = (SecAt.pull G L σ i).f j
    unfold genPull SecAt.pull VVRank.pullS VVRank.pullTo
    dsimp only
    rw [← hs' j]
    exact (appLE_appLE _ q _ (VVRank.whisker_snd_left G _) _ _ _ _).symm
  · obtain ⟨s₀, hs₀⟩ : x (IsLocalRing.closedPoint K) ∈ χ.opensRange := hx ⟨_, rfl⟩
    obtain ⟨z, hz, hz'⟩ := hnz s₀
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hz'
    rw [← hs' j] at hj
    have hb := ((Scheme.basicOpen_appLE q _ _ (hle j) (s (j 0))).le hj).2
    obtain ⟨y, hy, hy'⟩ := exists_point G.hom x (G.left.basicOpen (s (j 0))) (q z) hb (by
      rw [← Scheme.Hom.comp_apply, ew, Scheme.Hom.comp_apply, hz]
      exact hs₀)
    refine ⟨y, j 0, hy, ?_, valF_ne_zero_of_le _ hy'⟩
    rintro _ ⟨a, rfl⟩
    exact G.left.basicOpen_le (s (j 0)) (hy' (Set.mem_univ a))

end GlobalTheory.UMin.LocSecOfImm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSectionOfOpenImmersionSpecStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localSection_of_openImmersion_spec : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (R : Type) [CommRing R] (χ : Sp R ⟶ S) [IsOpenImmersion χ] (σ : SecAt G L χ), LocallyOfFiniteType G.hom → (∀ s : Sp R, ∃ z : (Over.mk χ ⊗ G).left, (fst (Over.mk χ) G).left z = s ∧ z ∈ nonzeroLocus σ) → ∃ s : LocSec G L χ.opensRange, IsLocSec s ∧ (∀ (K : Type) [Field K] (i : R →+* K), GenIs (spMap i ≫ χ) s (SecM.ofSec G (SecAt.pull G L σ i))) ∧ FibNz s χ.opensRange := by
  first | exact @GlobalTheory.UMin.LocSecOfImm.exists_locSec | exact GlobalTheory.UMin.LocSecOfImm.exists_locSec | (intros; apply GlobalTheory.UMin.LocSecOfImm.exists_locSec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSectionThetaQuotientProjChart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.ThBdl

theorem exists_locSec_of_openImmersion (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S)
    (g m N : ℕ) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R]
    (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] (χ : Sp R ⟶ S) [IsOpenImmersion χ] (ξ : Sp K ⟶ S)
    (e : spMap (algebraMap R K) ≫ χ = ξ) (θ : SecAt t.G t.PP.L ξ) (pt : Fin N → (Over.mk ξ ⟶ t.G)) (c : Fin N → R)
    (hodd : Odd m) (hm3 : 3 ≤ m) (hm : IsUnit (m : R)) (hpol : PolFib t.G t.PP.L g ξ)
    (hth : ThList t.G t.PP.L t.PP.rig m ξ θ pt (fun a => algebraMap R K (c a))) (hu : ∃ a, IsUnit (c a)) :
    ∃ s : LocSec t.G t.PP.L χ.opensRange, IsLocSec s ∧ GenIs ξ s (SecM.ofSec t.G θ) ∧ FibNz s χ.opensRange := by
  subst e
  have hlft : LocallyOfFiniteType t.G.hom := by
    haveI := t.semi.smooth
    infer_instance
  obtain ⟨σ, hσ, hσnz⟩ := GlobalTheory.T.extend_regularThetaSection_any_fractionField E H S t g m N R K χ θ pt c hodd hm3 hm hpol hth hu
  obtain ⟨s, hs, hsgen, hsfib⟩ := GlobalTheory.T.exists_localSection_of_openImmersion_spec S t.G t.PP.L R χ σ hlft hσnz
  refine ⟨s, hs, ?_, hsfib⟩
  have := hsgen K (algebraMap R K)
  rw [hσ] at this
  exact this

theorem exists_locSec_theta_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k Ω : Type) [CommRing k]
    [IsNoetherianRing k] [Field Ω] [CharZero Ω] [Algebra k Ω] (M : RatModel k Ω) (t : SAB H M.Z) (g m n : ℕ)
    (c : Fin (n + 1) → Ω) (h : M.Z ⟶ PSpace k n) (θ : SecAt t.G t.PP.L M.pt) (pt : Fin (n + 1) → (Over.mk M.pt ⟶ t.G)),
    Geo.Tor.IsNormalScheme M.Z → Odd m → 3 ≤ m → IsUnit (m : k) → PolFib t.G t.PP.L g M.pt →
    IsGenSec t.G t.PP.L _ θ → ThList t.G t.PP.L t.PP.rig m M.pt θ pt c → PCrd (M.pt ≫ h) c →
    ∀ (a : Fin (n + 1)) (z : M.Z), z ∈ h ⁻¹ᵁ chart k n a → ∃ N : M.Z.Opens, z ∈ N ∧ N ≤ h ⁻¹ᵁ chart k n a ∧
      ∃ s : LocSec t.G t.PP.L N, IsLocSec s ∧
        GenIs M.pt s ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c a)⁻¹ • SecM.ofSec t.G θ) ∧ FibNz s N := by
  intro E _ _ _ H k Ω _ _ _ _ _ M t g m n c h θ pt hN hodd hm3 hmu hpol hgen hth hcrd a z hz
  obtain ⟨hca, hdiv⟩ := GlobalTheory.T.projective_chart_coordinate_ratio_mem_model_ring k Ω M n c h a z hcrd hz
  obtain ⟨W, hWa, hzW, hWV, hnoeth, hic⟩ := GlobalTheory.T.exists_affine_nbhd_noetherian_integrallyClosed k Ω M hN (h ⁻¹ᵁ chart k n a) z hz
  have hne : (W : Set M.Z).Nonempty := ⟨z, hzW⟩
  obtain ⟨χ, hoi, hrange, hgenpt⟩ := GlobalTheory.T.exists_openImmersion_spec_ringOn_affine k Ω M W hWa hne
  haveI := M.isFractionRing_ringOn hWa hne
  let c'' : Fin (n + 1) → M.ringOn W := fun b =>
    ⟨c b / c a, RatModel.mem_ringOn.2 fun z' hz' => hdiv z' (hWV hz') b⟩
  let θ' : SecAt t.G t.PP.L M.pt :=
    SecM.toSec t.G ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c a)⁻¹ • SecM.ofSec t.G θ)
  have hmΩ : (m : Ω) ≠ 0 := by
    have := hmu.map (algebraMap k Ω)
    rw [map_natCast] at this
    exact this.ne_zero
  have hth' : ThList t.G t.PP.L t.PP.rig m M.pt θ' pt (fun b => algebraMap (M.ringOn W) Ω (c'' b)) := by
    refine ⟨hth.1, fun b => ?_, hth.2.2⟩
    have key := GlobalTheory.UMin.thG_smul_iff M.Z t.G t.PP.L t.PP.rig t.PP.isLB t.PP.rigGen g m Ω M.pt θ θ' (pt b)
      (c a)⁻¹ (c b) (c b / c a) hodd hmΩ hpol rfl (hth.2.1 b)
    exact key.2 (by rw [div_eq_inv_mul])
  have hmR : IsUnit (m : M.ringOn W) := by
    have := hmu.map (algebraMap k (M.ringOn W))
    rwa [map_natCast] at this
  have hunit : ∃ b, IsUnit (c'' b) := ⟨a, by
    have : c'' a = 1 := Subtype.ext (by simp [c'', div_self hca])
    rw [this]; exact isUnit_one⟩
  obtain ⟨s, hs, hsgen, hsfib⟩ := exists_locSec_of_openImmersion E H M.Z t g m (n + 1) (M.ringOn W) Ω χ M.pt hgenpt θ' pt c'' hodd hm3 hmR hpol hth' hunit
  exact ⟨χ.opensRange, by rw [hrange]; exact hzW, by rw [hrange]; exact hWV, s, hs, hsgen, hsfib⟩

end GlobalTheory.UMin.ThBdl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSectionThetaQuotientProjChartStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localSection_thetaQuotient_projChart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k Ω : Type) [CommRing k]
    [IsNoetherianRing k] [Field Ω] [CharZero Ω] [Algebra k Ω] (M : RatModel k Ω) (t : SAB H M.Z) (g m n : ℕ)
    (c : Fin (n + 1) → Ω) (h : M.Z ⟶ PSpace k n) (θ : SecAt t.G t.PP.L M.pt) (pt : Fin (n + 1) → (Over.mk M.pt ⟶ t.G)),
    Geo.Tor.IsNormalScheme M.Z → Odd m → 3 ≤ m → IsUnit (m : k) → PolFib t.G t.PP.L g M.pt →
    IsGenSec t.G t.PP.L _ θ → ThList t.G t.PP.L t.PP.rig m M.pt θ pt c → PCrd (M.pt ≫ h) c →
    ∀ (a : Fin (n + 1)) (z : M.Z), z ∈ h ⁻¹ᵁ chart k n a → ∃ N : M.Z.Opens, z ∈ N ∧ N ≤ h ⁻¹ᵁ chart k n a ∧
      ∃ s : LocSec t.G t.PP.L N, IsLocSec s ∧
        GenIs M.pt s ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c a)⁻¹ • SecM.ofSec t.G θ) ∧ FibNz s N := by
  first | exact @GlobalTheory.UMin.ThBdl.exists_locSec_theta_chart | exact GlobalTheory.UMin.ThBdl.exists_locSec_theta_chart | (intros; apply GlobalTheory.UMin.ThBdl.exists_locSec_theta_chart <;> assumption)
end
