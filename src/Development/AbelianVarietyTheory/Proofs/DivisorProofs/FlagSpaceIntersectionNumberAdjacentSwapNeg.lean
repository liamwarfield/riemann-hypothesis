module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDivisorsDoubleFlagSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberSwapOfDoubleSpace

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDoubleSpaceOfGenericFunctionFieldPair
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsReducedClosurePointFibreSquare
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsReducedClosurePointFibreSquare
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem exists_closure_pair : ∀ (F : Type) [Field F] (Y : Var F) (K : Type) [Field K] (q₁ q₂ : Sp K ⟶ Y.X), q₁ ≫ Y.str = q₂ ≫ Y.str → ∃ (Z : Scheme.{0}) (_ : IsIntegral Z) (p₁ p₂ : Z ⟶ Y.X) (h : p₁ ≫ Y.str = p₂ ≫ Y.str) (ζ : Sp K ⟶ Z), IsClosedImmersion (Limits.pullback.lift p₁ p₂ h) ∧ ζ ≫ p₁ = q₁ ∧ ζ ≫ p₂ = q₂ ∧ ζ (IsLocalRing.closedPoint K) = genericPoint Z := by
  intro F _ Y K _ q₁ q₂ hq
  let ξ : Sp K ⟶ Limits.pullback Y.str Y.str := Limits.pullback.lift q₁ q₂ hq
  let x := ξ (IsLocalRing.closedPoint K)
  let i := GlobalTheory.MixHt.cloι x
  have hw : (i ≫ Limits.pullback.fst Y.str Y.str) ≫ Y.str = (i ≫ Limits.pullback.snd Y.str Y.str) ≫ Y.str := by
    rw [Category.assoc, Category.assoc, Limits.pullback.condition]
  have hl : Limits.pullback.lift _ _ hw = i := by
    apply Limits.pullback.hom_ext
    · exact Limits.pullback.lift_fst _ _ _
    · exact Limits.pullback.lift_snd _ _ _
  have : IsReduced (Sp K) := inferInstanceAs (IsReduced (Spec _))
  have hr : Set.range ξ ⊆ Set.range i := by
    rintro _ ⟨a, rfl⟩
    have ha : a = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    exact ⟨genericPoint _, by rw [ha, GlobalTheory.MixHt.cloι_genericPoint]⟩
  have hk : i.ker ≤ ξ.ker := ker_le_ker_of_range_subset_of_isReduced i ξ hr
  let ζ := IsClosedImmersion.lift i ξ hk
  have hζ : ζ ≫ i = ξ := IsClosedImmersion.lift_fac _ _ _
  refine ⟨GlobalTheory.MixHt.clo x, inferInstance, i ≫ Limits.pullback.fst _ _, i ≫ Limits.pullback.snd _ _, hw, ζ, ?_, ?_, ?_, ?_⟩
  · rw [hl]; infer_instance
  · rw [← Category.assoc, hζ]; exact Limits.pullback.lift_fst _ _ _
  · rw [← Category.assoc, hζ]; exact Limits.pullback.lift_snd _ _ _
  · apply i.isClosedEmbedding.injective
    refine (Scheme.Hom.comp_apply ζ i _).symm.trans ?_
    rw [hζ, GlobalTheory.MixHt.cloι_genericPoint]

end GlobalTheory.FlagPush
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsReducedClosurePointFibreSquareStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_reduced_closure_point_fibreSquare : ∀ (F : Type) [Field F] (Y : Var F) (K : Type) [Field K] (q₁ q₂ : Sp K ⟶ Y.X), q₁ ≫ Y.str = q₂ ≫ Y.str → ∃ (Z : Scheme.{0}) (_ : IsIntegral Z) (p₁ p₂ : Z ⟶ Y.X) (h : p₁ ≫ Y.str = p₂ ≫ Y.str) (ζ : Sp K ⟶ Z), IsClosedImmersion (Limits.pullback.lift p₁ p₂ h) ∧ ζ ≫ p₁ = q₁ ∧ ζ ≫ p₂ = q₂ ∧ ζ (IsLocalRing.closedPoint K) = genericPoint Z := by
  first | exact @GlobalTheory.FlagPush.exists_closure_pair | exact GlobalTheory.FlagPush.exists_closure_pair | (intros; apply GlobalTheory.FlagPush.exists_closure_pair <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPairSpecializesDiagonalGenericPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPairSpecializesDiagonalGenericPoint
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem genPair_specializes_diagonal : ∀ (F : Type) [Field F] (Y : Var F) (K : Type) [Field K] (ψ₁ ψ₂ : Y.Fn →+* K),
    GenPair Y ψ₁ ψ₂ → ∃ h : (spMap ψ₁ ≫ (ratOf Y).pt) ≫ Y.str = (spMap ψ₂ ≫ (ratOf Y).pt) ≫ Y.str,
      Limits.pullback.lift (f := Y.str) (g := Y.str) (spMap ψ₁ ≫ (ratOf Y).pt) (spMap ψ₂ ≫ (ratOf Y).pt) h
        (IsLocalRing.closedPoint K) ⤳ Limits.pullback.diagonal Y.str (genericPoint Y.X) := by
  intro F _ Y K _ ψ₁ ψ₂ hG
  obtain ⟨hF, V, v₁, v₂, e₁, e₂, e₃, e₄⟩ := hG
  have hs : (ratOf Y).pt ≫ Y.str = spMap (algebraMap F Y.Fn) := (ratOf Y).pt_s
  have k : ∀ ψ : Y.Fn →+* K, (spMap ψ ≫ (ratOf Y).pt) ≫ Y.str = spMap (ψ.comp (algebraMap F Y.Fn)) :=
    fun ψ => (Category.assoc (spMap ψ) (ratOf Y).pt Y.str).trans
      ((congrArg (fun g => spMap ψ ≫ g) hs).trans (by rw [← Spec.map_comp]; rfl))
  have h : (spMap ψ₁ ≫ (ratOf Y).pt) ≫ Y.str = (spMap ψ₂ ≫ (ratOf Y).pt) ≫ Y.str := by
    rw [k, k, hF]
  refine ⟨h, ?_⟩
  haveI : IsDominant (spMap (algebraMap V K)) := by
    refine ⟨?_⟩
    change DenseRange (PrimeSpectrum.comap (algebraMap V K))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot _).mp (show Function.Injective (algebraMap V K) from Subtype.val_injective)]
    exact bot_le
  have hv : v₁ ≫ Y.str = v₂ ≫ Y.str := by
    refine ext_of_isDominant (spMap (algebraMap V K)) ?_
    rw [← Category.assoc, ← Category.assoc, e₁, e₂]
    exact h
  let v := Limits.pullback.lift v₁ v₂ hv
  have hgen : spMap (algebraMap V K) ≫ v =
      Limits.pullback.lift (f := Y.str) (g := Y.str) (spMap ψ₁ ≫ (ratOf Y).pt) (spMap ψ₂ ≫ (ratOf Y).pt) h := by
    apply Limits.pullback.hom_ext
    · simp only [v, Category.assoc, Limits.pullback.lift_fst]; exact e₁.trans (Limits.pullback.lift_fst _ _ _).symm
    · simp only [v, Category.assoc, Limits.pullback.lift_snd]; exact e₂.trans (Limits.pullback.lift_snd _ _ _).symm
  have hres : spMap (IsLocalRing.residue V) ≫ v =
      (spMap (IsLocalRing.residue V) ≫ v₁) ≫ Limits.pullback.diagonal Y.str := by
    apply Limits.pullback.hom_ext
    · simp only [v, Category.assoc, Limits.pullback.lift_fst, Limits.pullback.diagonal_fst, Category.comp_id]
    · simp only [v, Category.assoc, Limits.pullback.lift_snd, Limits.pullback.diagonal_snd, Category.comp_id]
      exact e₃.symm
  have hsp := ClosedPt.gen_specializes v (IsLocalRing.closedPoint K)
  rw [hgen] at hsp
  have hc : v (IsLocalRing.closedPoint V) = Limits.pullback.diagonal Y.str (genericPoint Y.X) := by
    calc v (IsLocalRing.closedPoint V) = (spMap (IsLocalRing.residue V) ≫ v) (IsLocalRing.closedPoint _) :=
          (ClosedPt.closedPt_comp v).symm
      _ = ((spMap (IsLocalRing.residue V) ≫ v₁) ≫ Limits.pullback.diagonal Y.str) (IsLocalRing.closedPoint _) := by
          rw [hres]
      _ = Limits.pullback.diagonal Y.str ((spMap (IsLocalRing.residue V) ≫ v₁) (IsLocalRing.closedPoint _)) :=
          Scheme.Hom.comp_apply _ _ _
      _ = Limits.pullback.diagonal Y.str (genericPoint Y.X) := by rw [ClosedPt.closedPt_comp v₁, e₄]
  rw [hc] at hsp
  exact hsp

end GlobalTheory.FlagPush
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPairSpecializesDiagonalGenericPointStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericPair_specializes_diagonal_genericPoint : ∀ (F : Type) [Field F] (Y : Var F) (K : Type) [Field K] (ψ₁ ψ₂ : Y.Fn →+* K), GenPair Y ψ₁ ψ₂ → ∃ h : (spMap ψ₁ ≫ (ratOf Y).pt) ≫ Y.str = (spMap ψ₂ ≫ (ratOf Y).pt) ≫ Y.str, Limits.pullback.lift (f := Y.str) (g := Y.str) (spMap ψ₁ ≫ (ratOf Y).pt) (spMap ψ₂ ≫ (ratOf Y).pt) h (IsLocalRing.closedPoint K) ⤳ Limits.pullback.diagonal Y.str (genericPoint Y.X) := by
  first | exact @GlobalTheory.FlagPush.genPair_specializes_diagonal | exact GlobalTheory.FlagPush.genPair_specializes_diagonal | (intros; apply GlobalTheory.FlagPush.genPair_specializes_diagonal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFunctionFieldMapDoubleSpaceGenericPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFunctionFieldMapDoubleSpaceGenericPoint
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagPush

theorem exists_functionField_map_of_genericPoint :
    ∀ (F : Type) [Field F] (Y : Var F) (W : Dbl Y), ∀ (K : Type) [Field K] (ψ₁ ψ₂ : Y.Fn →+* K)
      (ζ : Sp K ⟶ W.Z), ζ (IsLocalRing.closedPoint K) = genericPoint W.Z → ζ ≫ W.p₁ = spMap ψ₁ ≫ (ratOf Y).pt →
        ζ ≫ W.p₂ = spMap ψ₂ ≫ (ratOf Y).pt → ∃ j : W.Z.functionField →+* K, j.comp W.α₁ = ψ₁ ∧ j.comp W.α₂ = ψ₂ := by
  intro F _ Y W K _ ψ₁ ψ₂ ζ h h₁ h₂
  have hs : ζ (IsLocalRing.closedPoint K) ⤳ genericPoint W.Z := h ▸ specializes_rfl
  let j : W.Z.functionField →+* K :=
    (W.Z.presheaf.stalkSpecializes hs ≫ Scheme.stalkClosedPointTo (R := .of K) ζ).hom
  have e : spMap j ≫ W.Z.fromSpecStalk (genericPoint W.Z) = ζ := by
    change Spec.map (CommRingCat.ofHom j) ≫ W.Z.fromSpecStalk (genericPoint W.Z) = ζ
    rw [CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    exact spMap_stalkClosedPointTo ζ
  have key : ∀ (p : W.Z ⟶ Y.X) [IsDominant p] (ψ : Y.Fn →+* K), ζ ≫ p = spMap ψ ≫ (ratOf Y).pt →
      j.comp (functionFieldMap p) = ψ := by
    intro p _ ψ hp
    have e2 : spMap (j.comp (functionFieldMap p)) ≫ Y.X.fromSpecStalk (genericPoint Y.X) =
        spMap ψ ≫ Y.X.fromSpecStalk (genericPoint Y.X) := by
      change Spec.map (CommRingCat.ofHom (j.comp (functionFieldMap p))) ≫ genericFieldPoint Y.X = _
      rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, specMap_functionFieldMap,
        ← Category.assoc]
      change (spMap j ≫ W.Z.fromSpecStalk (genericPoint W.Z)) ≫ p = _
      rw [e, hp]
      rfl
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).mp e2))
  exact ⟨j, key W.p₁ ψ₁ h₁, key W.p₂ ψ₂ h₂⟩

end GlobalTheory.FlagPush
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFunctionFieldMapDoubleSpaceGenericPointStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_functionField_map_doubleSpace_genericPoint : ∀ (F : Type) [Field F] (Y : Var F) (W : Dbl Y), ∀ (K : Type) [Field K] (ψ₁ ψ₂ : Y.Fn →+* K) (ζ : Sp K ⟶ W.Z), ζ (IsLocalRing.closedPoint K) = genericPoint W.Z → ζ ≫ W.p₁ = spMap ψ₁ ≫ (ratOf Y).pt → ζ ≫ W.p₂ = spMap ψ₂ ≫ (ratOf Y).pt → ∃ j : W.Z.functionField →+* K, j.comp W.α₁ = ψ₁ ∧ j.comp W.α₂ = ψ₂ := by
  first | exact @GlobalTheory.FlagPush.exists_functionField_map_of_genericPoint | exact GlobalTheory.FlagPush.exists_functionField_map_of_genericPoint | (intros; apply GlobalTheory.FlagPush.exists_functionField_map_of_genericPoint <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleSpaceOfClosedImmersionContainsDiagonal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleSpaceOfClosedImmersionContainsDiagonal
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

set_option autoImplicit false

namespace GlobalTheory.FlagPush

theorem dbl_of_isClosedImmersion_lift : ∀ (F : Type) [Field F] (Y : Var F) (Z : Scheme.{0}) [IsIntegral Z] (p₁ p₂ : Z ⟶ Y.X) (h : p₁ ≫ Y.str = p₂ ≫ Y.str), IsClosedImmersion (Limits.pullback.lift p₁ p₂ h) → Limits.pullback.diagonal Y.str (genericPoint Y.X) ∈ Set.range (Limits.pullback.lift p₁ p₂ h) → IsProjOver (p₁ ≫ Y.str) ∧ ∃ δ : Y.X ⟶ Z, IsClosedImmersion δ ∧ δ ≫ p₁ = 𝟙 _ ∧ δ ≫ p₂ = 𝟙 _ ∧ ∀ (K : Type) [Field K] (w : Sp K ⟶ Z), w ≫ p₁ = w ≫ p₂ → w (IsLocalRing.closedPoint K) ∈ Set.range δ := by
  intro F _ Y Z _ p₁ p₂ h hi hη
  have hp₁ : p₁ = Limits.pullback.lift p₁ p₂ h ≫ Limits.pullback.fst Y.str Y.str :=
    (Limits.pullback.lift_fst _ _ _).symm
  have hp₂ : p₂ = Limits.pullback.lift p₁ p₂ h ≫ Limits.pullback.snd Y.str Y.str :=
    (Limits.pullback.lift_snd _ _ _).symm
  refine ⟨?_, ?_⟩
  · rw [hp₁, Category.assoc]
    exact ProjSpace.isProjOver_comp_of_isClosedImmersion _
      (ProjSpace.isProjOver_pullback Y.isProjOver Y.isProjOver)
  have hc : IsClosed (Set.range (Limits.pullback.lift p₁ p₂ h)) :=
    (Limits.pullback.lift p₁ p₂ h).isClosedEmbedding.isClosed_range
  have hrange : Set.range (Limits.pullback.diagonal Y.str) ⊆ Set.range (Limits.pullback.lift p₁ p₂ h) := by
    rintro _ ⟨y, rfl⟩
    have hs := ((genericPoint_spec Y.X).specializes (Set.mem_univ y)).map
      (Limits.pullback.diagonal Y.str).continuous
    exact hs.mem_closed hc hη
  have hle : (Limits.pullback.lift p₁ p₂ h).ker ≤ (Limits.pullback.diagonal Y.str).ker := by
    refine le_trans ?_ (ReducedSubgroup.vanishingIdeal_le_ker _ ⟨_, hc⟩ hrange)
    rw [← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal]
    exact (Limits.pullback.lift p₁ p₂ h).range_subset_ker_support
  have hδ := IsClosedImmersion.lift_fac (Limits.pullback.lift p₁ p₂ h) (Limits.pullback.diagonal Y.str) hle
  refine ⟨IsClosedImmersion.lift _ _ hle, ?_, ?_, ?_, ?_⟩
  · have : IsClosedImmersion (IsClosedImmersion.lift _ _ hle ≫ Limits.pullback.lift p₁ p₂ h) := by
      rw [hδ]; infer_instance
    exact IsClosedImmersion.of_comp _ (Limits.pullback.lift p₁ p₂ h)
  · have e₁ := hδ =≫ Limits.pullback.fst Y.str Y.str
    rwa [Category.assoc, Limits.pullback.lift_fst, Limits.pullback.diagonal_fst] at e₁
  · have e₂ := hδ =≫ Limits.pullback.snd Y.str Y.str
    rwa [Category.assoc, Limits.pullback.lift_snd, Limits.pullback.diagonal_snd] at e₂
  · intro K _ w hw
    have e : w = (w ≫ p₁) ≫ IsClosedImmersion.lift _ _ hle := by
      rw [← cancel_mono (Limits.pullback.lift p₁ p₂ h), Category.assoc, hδ]
      apply Limits.pullback.hom_ext
      · simp only [Category.assoc, Limits.pullback.lift_fst, Limits.pullback.diagonal_fst, Category.comp_id]
      · simp only [Category.assoc, Limits.pullback.lift_snd, Limits.pullback.diagonal_snd, Category.comp_id, hw]
    refine ⟨(w ≫ p₁) (IsLocalRing.closedPoint K), ?_⟩
    have e' := congrArg (fun f : Sp K ⟶ Z => f (IsLocalRing.closedPoint K)) e
    exact e'.symm

end GlobalTheory.FlagPush
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleSpaceOfClosedImmersionContainsDiagonalStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleSpace_of_closedImmersion_contains_diagonal : ∀ (F : Type) [Field F] (Y : Var F) (Z : Scheme.{0}) [IsIntegral Z] (p₁ p₂ : Z ⟶ Y.X) (h : p₁ ≫ Y.str = p₂ ≫ Y.str), IsClosedImmersion (Limits.pullback.lift p₁ p₂ h) → Limits.pullback.diagonal Y.str (genericPoint Y.X) ∈ Set.range (Limits.pullback.lift p₁ p₂ h) → IsProjOver (p₁ ≫ Y.str) ∧ ∃ δ : Y.X ⟶ Z, IsClosedImmersion δ ∧ δ ≫ p₁ = 𝟙 _ ∧ δ ≫ p₂ = 𝟙 _ ∧ ∀ (K : Type) [Field K] (w : Sp K ⟶ Z), w ≫ p₁ = w ≫ p₂ → w (IsLocalRing.closedPoint K) ∈ Set.range δ := by
  first | exact @GlobalTheory.FlagPush.dbl_of_isClosedImmersion_lift | exact GlobalTheory.FlagPush.dbl_of_isClosedImmersion_lift | (intros; apply GlobalTheory.FlagPush.dbl_of_isClosedImmersion_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDoubleSpaceOfGenericFunctionFieldPair
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem exists_dbl_of_genPair : ∀ (F : Type) [Field F] (Y : Var F) (K : Type) [Field K] (ψ₁ ψ₂ : Y.Fn →+* K),
    GenPair Y ψ₁ ψ₂ → ∃ (W : Dbl Y) (j : W.Z.functionField →+* K), j.comp W.α₁ = ψ₁ ∧ j.comp W.α₂ = ψ₂ := by
  intro F _ Y K _ ψ₁ ψ₂ hg
  obtain ⟨h, hsp⟩ := GlobalTheory.T.genericPair_specializes_diagonal_genericPoint F Y K ψ₁ ψ₂ hg
  obtain ⟨Z, hZi, p₁, p₂, hZ, ζ, hci, hζ₁, hζ₂, hζg⟩ :=
    GlobalTheory.T.exists_reduced_closure_point_fibreSquare F Y K (spMap ψ₁ ≫ (ratOf Y).pt) (spMap ψ₂ ≫ (ratOf Y).pt) h
  haveI := hZi
  have hcomp : ζ ≫ Limits.pullback.lift p₁ p₂ hZ =
      Limits.pullback.lift (f := Y.str) (g := Y.str) (spMap ψ₁ ≫ (ratOf Y).pt) (spMap ψ₂ ≫ (ratOf Y).pt) h := by
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, Limits.pullback.lift_fst]; exact hζ₁.trans (Limits.pullback.lift_fst _ _ _).symm
    · rw [Category.assoc, Limits.pullback.lift_snd]; exact hζ₂.trans (Limits.pullback.lift_snd _ _ _).symm
  have hmem : Limits.pullback.diagonal Y.str (genericPoint Y.X) ∈ Set.range (Limits.pullback.lift p₁ p₂ hZ) := by
    have hcl : IsClosed (Set.range (Limits.pullback.lift p₁ p₂ hZ)) := hci.isClosedEmbedding.isClosed_range
    refine hsp.mem_closed hcl ⟨ζ (IsLocalRing.closedPoint K), ?_⟩
    rw [← hcomp]
    first | rfl | exact (Scheme.Hom.comp_apply _ _ _).symm | simp
  obtain ⟨hproj, δ, hδc, hδ₁, hδ₂, hdiag⟩ := GlobalTheory.T.doubleSpace_of_closedImmersion_contains_diagonal F Y Z p₁ p₂ hZ hci hmem
  let W : Dbl Y :=
    { Z := Z, integral := hZi, p₁ := p₁, p₂ := p₂, δ := δ, str_eq := hZ, proj := hproj, closed := hδc,
      δ₁ := hδ₁, δ₂ := hδ₂, diag := hdiag }
  obtain ⟨j, hj₁, hj₂⟩ := GlobalTheory.T.exists_functionField_map_doubleSpace_genericPoint F Y W K ψ₁ ψ₂ ζ hζg hζ₁ hζ₂
  exact ⟨W, j, hj₁, hj₂⟩

end GlobalTheory.FlagPush
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDoubleSpaceOfGenericFunctionFieldPairStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_doubleSpace_of_genericFunctionFieldPair : ∀ (F : Type) [Field F] (Y : Var F) (K : Type) [Field K] (ψ₁ ψ₂ : Y.Fn →+* K), GenPair Y ψ₁ ψ₂ → ∃ (W : Dbl Y) (j : W.Z.functionField →+* K), j.comp W.α₁ = ψ₁ ∧ j.comp W.α₂ = ψ₂ := by
  first | exact @GlobalTheory.FlagPush.exists_dbl_of_genPair | exact GlobalTheory.FlagPush.exists_dbl_of_genPair | (intros; apply GlobalTheory.FlagPush.exists_dbl_of_genPair <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleSpaceSmallOfFunctionFieldEmbedsRatFunc
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrdegLeSuccOfEmbeddingRatFunc
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrdegLeSuccOfEmbeddingRatFunc
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

theorem GlobalTheory.FlagPush.trdeg_le_succ_of_ratFunc :
    ∀ (F k L : Type) [Field F] [Field k] [Field L] [Algebra F k] [Algebra F L] (α : k →+* L)
      (j : L →+* RatFunc k) (d : ℕ), α.comp (algebraMap F k) = algebraMap F L →
      j.comp α = algebraMap k (RatFunc k) → Algebra.trdeg F k = d →
      Algebra.trdeg F L ≤ (d + 1 : ℕ) := by
  intro F k L _ _ _ _ _ α j d hα hj hd
  let jF : L →ₐ[F] RatFunc k :=
    { j with
      commutes' := fun x => by
        show j (algebraMap F L x) = algebraMap k (RatFunc k) (algebraMap F k x)
        rw [← hα, ← hj]; rfl }
  have h1 : Algebra.trdeg F L ≤ Algebra.trdeg F (RatFunc k) :=
    trdeg_le_of_injective jF j.injective
  have hR : Algebra.trdeg k (RatFunc k) = 1 := by
    have : Algebra.IsAlgebraic (Polynomial k) (RatFunc k) :=
      IsLocalization.isAlgebraic (RatFunc k) (nonZeroDivisors (Polynomial k))
    rw [← trdeg_add_eq k (Polynomial k), trdeg_eq_zero (R := Polynomial k) (A := RatFunc k),
      add_zero, Polynomial.trdeg_of_isDomain]
  have h2 := trdeg_add_eq F k (A := RatFunc k)
  calc Algebra.trdeg F L ≤ Algebra.trdeg F (RatFunc k) := h1
    _ = ((d + 1 : ℕ) : Cardinal) := by rw [← h2, hR, hd]; push_cast; rfl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrdegLeSuccOfEmbeddingRatFuncStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trdeg_le_succ_of_embedding_ratFunc : ∀ (F k L : Type) [Field F] [Field k] [Field L] [Algebra F k] [Algebra F L] (α : k →+* L) (j : L →+* RatFunc k) (d : ℕ), α.comp (algebraMap F k) = algebraMap F L → j.comp α = algebraMap k (RatFunc k) → Algebra.trdeg F k = d → Algebra.trdeg F L ≤ (d + 1 : ℕ) := by
  first | exact @GlobalTheory.FlagPush.trdeg_le_succ_of_ratFunc | exact GlobalTheory.FlagPush.trdeg_le_succ_of_ratFunc | (intros; apply GlobalTheory.FlagPush.trdeg_le_succ_of_ratFunc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleSpaceSmallOfFunctionFieldEmbedsRatFunc
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush.SmallPf

theorem exists_dim (F : Type) [Field F] {Z : Scheme.{0}} [IsIntegral Z] (f : Z ⟶ Sp F) [LocallyOfFiniteType f] :
    ∃ d : ℕ, topologicalKrullDim Z = d := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (genericPoint Z)) isOpen_univ
  have hU : IsAffineOpen U := hU
  obtain ⟨d, h₁, -⟩ := GlobalTheory.OpenDim.ringKrullDim_affineOpen F f hU ⟨_, hxU⟩
  refine ⟨d, ?_⟩
  rw [← GlobalTheory.OpenDim.topologicalKrullDim_open F f U ⟨_, hxU⟩, ← h₁, ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding hU.range_fromSpec

theorem main : ∀ (F : Type) [Field F] (Y : Var F) (W : Dbl Y), ∀ j : W.Z.functionField →+* RatFunc Y.Fn, j.comp W.α₁ = algebraMap Y.Fn (RatFunc Y.Fn) → W.Small := by
  intro F _ Y W j hj
  have hp := W.proj
  have hlft : LocallyOfFiniteType (W.p₁ ≫ Y.str) := by
    obtain ⟨N, i, hi, hcomp⟩ := hp
    haveI : IsProper (PSpace.str F N) := isProper_str F N
    rw [← hcomp]; infer_instance
  obtain ⟨d, hd⟩ := exists_dim F (W.p₁ ≫ Y.str)
  have hY : Y.X.fromSpecStalk (genericPoint Y.X) ≫ Y.str = spMap (algebraMap F Y.Fn) := (ratOf Y).pt_s
  have hZ : W.Z.fromSpecStalk (genericPoint W.Z) ≫ W.p₁ ≫ Y.str = spMap (W.α₁.comp (algebraMap F Y.Fn)) := by
    have h1 : spMap W.α₁ ≫ Y.X.fromSpecStalk (genericPoint Y.X) = W.Z.fromSpecStalk (genericPoint W.Z) ≫ W.p₁ :=
      specMap_functionFieldMap W.p₁
    rw [← Category.assoc, ← h1, Category.assoc, hY]
    exact (Spec.map_comp (CommRingCat.ofHom (algebraMap F Y.Fn)) (CommRingCat.ofHom W.α₁)).symm
  have t₁ := GlobalTheory.FunctionFieldTrdeg.trdeg_functionField_eq F Y.X Y.str Y.dim Y.isProjOver Y.topologicalKrullDim_eq _ hY
  have t₂ := GlobalTheory.FunctionFieldTrdeg.trdeg_functionField_eq F W.Z _ d W.proj hd _ hZ
  have t₃ := @GlobalTheory.T.trdeg_le_succ_of_embedding_ratFunc F Y.Fn W.Z.functionField _ _ _ (algebraMap F Y.Fn).toAlgebra
    (W.α₁.comp (algebraMap F Y.Fn)).toAlgebra W.α₁ j Y.dim rfl hj t₁
  rw [t₂] at t₃
  have : d ≤ Y.dim + 1 := by exact_mod_cast t₃
  unfold Dbl.Small
  rw [hd]
  exact_mod_cast this

end GlobalTheory.FlagPush.SmallPf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleSpaceSmallOfFunctionFieldEmbedsRatFuncStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleSpace_small_of_functionField_embeds_ratFunc : ∀ (F : Type) [Field F] (Y : Var F) (W : Dbl Y), ∀ j : W.Z.functionField →+* RatFunc Y.Fn, j.comp W.α₁ = algebraMap Y.Fn (RatFunc Y.Fn) → W.Small := by
  first | exact @GlobalTheory.FlagPush.SmallPf.main | exact GlobalTheory.FlagPush.SmallPf.main | (intros; apply GlobalTheory.FlagPush.SmallPf.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericPairFlagsDifferingOneStep
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShearedGenericFlagEqGenericFlagAtSpecial
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShearedGenericFlagEqGenericFlagAtSpecial
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush.Meet

theorem val_spMap_pt {F : Type} [Field F] (Y : Var F) {K : Type} [Field K] (σ : Y.Fn →+* K) (x : Y.Fn) :
    (ratOf Y).val (spMap σ ≫ (ratOf Y).pt) x = σ x := by
  have hx : x ∈ (ratOf Y).O ((ratOf Y).pt (IsLocalRing.closedPoint Y.Fn)) := by
    refine (congrArg (fun z => x ∈ (ratOf Y).O z) ((ratOf Y).pt_apply _)).mpr ?_
    rw [RatModel.O_genericPoint]; exact Algebra.mem_top
  have h := RatModel.val_spMap_comp (M := ratOf Y) σ (ratOf Y).pt specializes_rfl ⟨x, hx⟩
  rw [RatModel.valLoc_eq_val] at h
  exact h.trans (congrArg σ (RatModel.val_pt x))


open GlobalTheory.FlagBundle.ClosedPt in
theorem meet : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ B ∈ E'.S (genericPoint Y.X), ∀ A ∈ E.S (f (genericPoint Y.X)), ∀ (τ : ι) (a b : Fin (m τ)), a < b → ∀ (K : Type) [Field K] (V : ValuationSubring K) (c : Y.Fn →+* V) (t : V), IsLocalRing.residue V t = 0 → ∀ v₂ : Sp V ⟶ Y.X, v₂ ≫ f = spMap c ≫ (ratOf Y).pt ≫ f → Bears E' φ A (shear τ a b (t : K) * (B * (A.map φ)⁻¹).map ((algebraMap V K).comp c)) (spMap (algebraMap V K) ≫ v₂) → spMap (IsLocalRing.residue V) ≫ spMap c ≫ (ratOf Y).pt = spMap (IsLocalRing.residue V) ≫ v₂ := by
  intro F _ X Y ι _ m E E' φ f hf B hB A hA τ a b hab K _ V c t ht v₂ e hbear
  have hM := hf.sub _ B hB A hA
  obtain ⟨-, -, -, hsm⟩ := GlobalTheory.T.blockMatrixElementaryShear_properties ι m τ a b hab V t
  obtain ⟨-, -, hs0, -⟩ := GlobalTheory.T.blockMatrixElementaryShear_properties ι m τ a b hab (IsLocalRing.ResidueField V) 0
  have hpt : ∀ (R : Type) [CommRing R] (g : Y.Fn →+* R) (w : Sp R),
      (spMap g ≫ (ratOf Y).pt) w = genericPoint Y.X := fun R _ g w =>
    (Scheme.Hom.comp_apply _ _ _).trans ((ratOf Y).pt_apply _)
  have hf₂ : f (v₂ (IsLocalRing.closedPoint V)) = f (genericPoint Y.X) := by
    refine (Scheme.Hom.comp_apply _ _ _).symm.trans ?_
    rw [e]
    exact (Scheme.Hom.comp_apply (spMap c ≫ (ratOf Y).pt) f _).trans (congrArg f (hpt _ c _))
  obtain ⟨A₂, hA₂⟩ := E'.nonempty (v₂ (IsLocalRing.closedPoint V))
  have hM₂ := hf.sub _ A₂ hA₂ A ((congrArg (fun z => A ∈ E.S z) hf₂).mpr hA)
  obtain ⟨A₂', hA₂', hpar⟩ := hbear
  have hA₂g : A₂ ∈ E'.S ((spMap (algebraMap V K) ≫ v₂) (IsLocalRing.closedPoint K)) :=
    Fr.mem_of_specializes hA₂ (gen_specializes v₂ _)
  have hsp₂ := gen_specializes (L := K) v₂ (IsLocalRing.closedPoint K)
  have hG := (Fr.mem_iff hA₂g).1 hA₂'
  have hM₂g : Par 0 ((ratOf Y).O ((spMap (algebraMap V K) ≫ v₂) (IsLocalRing.closedPoint K))).toSubring
      (A₂ * (A.map φ)⁻¹) :=
    hM₂.mono le_rfl fun _ hx => RatModel.O_le_of_specializes hsp₂ hx
  set ψ := RatModel.valHom (M := ratOf Y) (spMap (algebraMap V K) ≫ v₂) _
    (RatModel.range_eq_singleton _ (IsLocalRing.closedPoint K))
  have hv : ∀ x : ((ratOf Y).O ((spMap (algebraMap V K) ≫ v₂) (IsLocalRing.closedPoint K))).toSubring,
      (ratOf Y).val (spMap (algebraMap V K) ≫ v₂) x = ψ x := fun _ => rfl
  have heqM : A₂' * (A.map φ)⁻¹ = (A₂' * A₂⁻¹) * (A₂ * (A.map φ)⁻¹) := by
    rw [mul_assoc, ← mul_assoc A₂⁻¹, Mat.inv_mul (Fr.det_ne hA₂), one_mul]
  have hmap : (A₂' * (A.map φ)⁻¹).map ((ratOf Y).val (spMap (algebraMap V K) ≫ v₂)) =
      (A₂' * A₂⁻¹).map ((ratOf Y).val (spMap (algebraMap V K) ≫ v₂)) *
        (A₂ * (A.map φ)⁻¹).map ((ratOf Y).val (spMap (algebraMap V K) ≫ v₂)) := by
    rw [heqM]
    exact Par.map_mul_of hG hM₂g ((ratOf Y).val (spMap (algebraMap V K) ≫ v₂)) ψ hv
  have hGv := Par.map_of hG ((ratOf Y).val (spMap (algebraMap V K) ≫ v₂)) ψ hv
  have hpar2 := hpar
  erw [hmap] at hpar2
  rw [Mat.mul_inv_rev] at hpar2
  clear hpar
  have hL := hpar2.mul hGv
  rw [mul_assoc, mul_assoc, mul_assoc, Mat.inv_mul hGv.det_ne, mul_one, ← mul_assoc] at hL
  rw [map_val (algebraMap V K) v₂ _ (fun τ a b => (hM₂ τ).1 a b)] at hL
  have hN : ∀ (S : Type) [CommRing S] (g : V →+* S),
      (shear τ a b t * (B * (A.map φ)⁻¹).map c).map g =
        shear τ a b (g t) * (B * (A.map φ)⁻¹).map (g.comp c) := fun S _ g => by
    rw [← hsm S g]
    funext σ
    exact Matrix.map_mul
  have hN1 := hN K (algebraMap V K)
  have hN2 := hN _ (IsLocalRing.residue V)
  rw [ht, hs0, one_mul] at hN2
  have hh : Par 0 ⊤ ((B * (A.map φ)⁻¹).map ((IsLocalRing.residue V).comp c)) :=
    hM.map _ fun _ _ => trivial
  have hk₂ := par_val (IsLocalRing.residue V) v₂ hM₂
  have hD := descend (L := K) (shear τ a b t * (B * (A.map φ)⁻¹).map c)
    (vals v₂ _ (fun τ a b => (hM₂ τ).1 a b)) (by rw [hN2]; exact hh.det_ne)
    (by rw [← map_val]; exact hk₂.det_ne) (by rw [hN1]; exact hL)
  rw [hN2, ← map_val] at hD
  have ec : spMap (IsLocalRing.residue V) ≫ spMap c ≫ (ratOf Y).pt =
      spMap ((IsLocalRing.residue V).comp c) ≫ (ratOf Y).pt := by
    rw [← Category.assoc, ← Spec.map_comp]
    rfl
  have hb₂ : Bears E' φ A ((B * (A.map φ)⁻¹).map ((IsLocalRing.residue V).comp c))
      (spMap (IsLocalRing.residue V) ≫ v₂) :=
    ⟨A₂, (congrArg (fun z => A₂ ∈ E'.S z) (closedPt_comp v₂)).mpr hA₂, hD⟩
  have hb₁ : Bears E' φ A ((B * (A.map φ)⁻¹).map ((IsLocalRing.residue V).comp c))
      (spMap ((IsLocalRing.residue V).comp c) ≫ (ratOf Y).pt) := by
    refine ⟨B, (congrArg (fun z => B ∈ E'.S z) (hpt _ _ _)).mpr hB, ?_⟩
    rw [show (ratOf Y).val (spMap ((IsLocalRing.residue V).comp c) ≫ (ratOf Y).pt) =
      ⇑((IsLocalRing.residue V).comp c) from funext (val_spMap_pt Y _), Mat.mul_inv hh.det_ne]
    exact Par.one
  have hAk : A ∈ E.S (((spMap (IsLocalRing.residue V) ≫ v₂) ≫ f)
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField V))) := by
    refine (congrArg (fun z => A ∈ E.S z) ?_).mpr hA
    exact (Scheme.Hom.comp_apply _ _ _).trans ((congrArg f (closedPt_comp v₂)).trans hf₂)
  obtain ⟨p, -, hp⟩ := hf.lifts _ _ A hAk _ hh
  refine (ec.trans (hp _ ⟨?_, hb₁⟩)).trans (hp _ ⟨rfl, hb₂⟩).symm
  rw [← ec]
  exact congrArg (spMap (IsLocalRing.residue V) ≫ ·) e.symm

end GlobalTheory.FlagPush.Meet
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShearedGenericFlagEqGenericFlagAtSpecialStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shearedGenericFlag_eq_genericFlag_at_special : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ B ∈ E'.S (genericPoint Y.X), ∀ A ∈ E.S (f (genericPoint Y.X)), ∀ (τ : ι) (a b : Fin (m τ)), a < b → ∀ (K : Type) [Field K] (V : ValuationSubring K) (c : Y.Fn →+* V) (t : V), IsLocalRing.residue V t = 0 → ∀ v₂ : Sp V ⟶ Y.X, v₂ ≫ f = spMap c ≫ (ratOf Y).pt ≫ f → Bears E' φ A (shear τ a b (t : K) * (B * (A.map φ)⁻¹).map ((algebraMap V K).comp c)) (spMap (algebraMap V K) ≫ v₂) → spMap (IsLocalRing.residue V) ≫ spMap c ≫ (ratOf Y).pt = spMap (IsLocalRing.residue V) ≫ v₂ := by
  first | exact @GlobalTheory.FlagPush.Meet.meet | exact GlobalTheory.FlagPush.Meet.meet | (intros; apply GlobalTheory.FlagPush.Meet.meet <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsValuationSubringRatFuncXResidueZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsValuationSubringRatFuncXResidueZero
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem exists_valuationSubring_ratFunc_residue_X_eq_zero :
    ∀ (k : Type) [Field k], ∃ (V : ValuationSubring (RatFunc k)) (c : k →+* V) (t : V), (algebraMap V (RatFunc k)).comp c = algebraMap k (RatFunc k) ∧ (t : RatFunc k) = RatFunc.X ∧ IsLocalRing.residue V t = 0 := by
  intro k _
  let v := (Polynomial.idealX k).valuation (RatFunc k)
  have hc : ∀ a : k, algebraMap k (RatFunc k) a ∈ v.valuationSubring := by
    intro a
    rw [Valuation.mem_valuationSubring_iff,
      IsScalarTower.algebraMap_apply k (Polynomial k) (RatFunc k)]
    exact (Polynomial.idealX k).valuation_le_one _
  have hX : v RatFunc.X < 1 := by
    rw [← RatFunc.algebraMap_X]
    exact ((Polynomial.idealX k).valuation_lt_one_iff_mem _).2 (by
      rw [Polynomial.idealX_span]; exact Ideal.mem_span_singleton_self _)
  have hX' : RatFunc.X ∈ v.valuationSubring := by
    rw [Valuation.mem_valuationSubring_iff]; exact hX.le
  refine ⟨v.valuationSubring, (algebraMap k (RatFunc k)).codRestrict v.valuationSubring hc,
    ⟨RatFunc.X, hX'⟩, ?_, rfl, ?_⟩
  · ext a; rfl
  · rw [IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
    exact ((Valuation.isEquiv_valuation_valuationSubring v).lt_one_iff_lt_one).1 hX

end GlobalTheory.FlagPush
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsValuationSubringRatFuncXResidueZeroStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_valuationSubring_ratFunc_X_residue_zero : ∀ (k : Type) [Field k], ∃ (V : ValuationSubring (RatFunc k)) (c : k →+* V) (t : V), (algebraMap V (RatFunc k)).comp c = algebraMap k (RatFunc k) ∧ (t : RatFunc k) = RatFunc.X ∧ IsLocalRing.residue V t = 0 := by
  first | exact @GlobalTheory.FlagPush.exists_valuationSubring_ratFunc_residue_X_eq_zero | exact GlobalTheory.FlagPush.exists_valuationSubring_ratFunc_residue_X_eq_zero | (intros; apply GlobalTheory.FlagPush.exists_valuationSubring_ratFunc_residue_X_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagOfDominantPointAsTriangularMatrix
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagOfDominantPointAsTriangularMatrix
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem val_spMap_pt {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (M : RatModel F Ω) {K : Type} [Field K]
    (σ : Ω →+* K) (x : Ω) : M.val (spMap σ ≫ M.pt) x = σ x := by
  have hx : x ∈ M.O (genericPoint M.Z) := by rw [RatModel.O_genericPoint]; exact Algebra.mem_top
  have := M.val_spMap_comp σ M.pt (M.pt_specializes _ _) ⟨x, hx⟩
  rw [RatModel.valLoc_eq_val, RatModel.val_pt] at this
  exact this

theorem flag_conv : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ B ∈ E'.S (genericPoint Y.X), ∀ A ∈ E.S (f (genericPoint Y.X)), ∀ (K : Type) [Field K] (ψ₁ ψ₂ : Y.Fn →+* K) (U : Mat m K), spMap ψ₁ ≫ (ratOf Y).pt ≫ f = spMap ψ₂ ≫ (ratOf Y).pt ≫ f → Bears E' φ A (U * (B * (A.map φ)⁻¹).map ψ₁) (spMap ψ₂ ≫ (ratOf Y).pt) → (∀ u : X.Fn, ψ₁ (φ u) = ψ₂ (φ u)) ∧ Par m ⊤ (U * (B.map ψ₁ * (B.map ψ₂)⁻¹)) := by
  intro F _ X Y ι _ m E E' φ f hR B hB A hA K _ ψ₁ ψ₂ U hpt hBe
  have hom : (ratOf Y).pt ≫ f = spMap φ.toRingHom ≫ (ratOf X).pt := hR.hom
  have key : ∀ σ : Y.Fn →+* K, spMap σ ≫ (ratOf Y).pt ≫ f = spMap (σ.comp φ.toRingHom) ≫ (ratOf X).pt := by
    intro σ
    rw [hom]
    show Spec.map _ ≫ Spec.map _ ≫ _ = Spec.map (CommRingCat.ofHom (σ.comp φ.toRingHom)) ≫ _
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
    exact (Category.assoc _ _ _).symm
  have h1 : ∀ u : X.Fn, ψ₁ (φ u) = ψ₂ (φ u) := by
    intro u
    have e1 := val_spMap_pt (ratOf X) (ψ₁.comp φ.toRingHom) u
    have e2 := val_spMap_pt (ratOf X) (ψ₂.comp φ.toRingHom) u
    rw [← key, hpt, key] at e1
    exact e1.symm.trans e2
  refine ⟨h1, ?_⟩
  obtain ⟨A', hA', hP⟩ := hBe
  have hgen : (spMap ψ₂ ≫ (ratOf Y).pt) (IsLocalRing.closedPoint K) = genericPoint Y.X :=
    (ratOf Y).pt_apply _
  rw [hgen] at hA'
  have hval : (ratOf Y).val (spMap ψ₂ ≫ (ratOf Y).pt) = ψ₂ := funext (val_spMap_pt (ratOf Y) ψ₂)
  rw [hval] at hP
  have hAd : ∀ τ, (A τ).det ≠ 0 := Fr.det_ne hA
  have hBd : ∀ τ, (B τ).det ≠ 0 := Fr.det_ne hB
  have hA'd : ∀ τ, (A' τ).det ≠ 0 := Fr.det_ne hA'
  set C : Mat m Y.Fn := A.map φ with hC
  have hCd : ∀ τ, (C τ).det ≠ 0 := fun τ => by
    rw [hC]; exact fun h0 => (map_ne_zero φ.toRingHom).2 (hAd τ) ((Mat.det_map A φ.toRingHom τ).symm.trans h0)
  have hCψ : C.map ψ₁ = C.map ψ₂ := by
    funext τ; ext i j; exact h1 (A τ i j)
  have hC2d : ∀ τ, (C.map ψ₂ τ).det ≠ 0 := fun τ => by
    rw [Mat.det_map]; exact (map_ne_zero _).2 (hCd τ)
  have hA'2d : ∀ τ, (A'.map ψ₂ τ).det ≠ 0 := fun τ => by
    rw [Mat.det_map]; exact (map_ne_zero _).2 (hA'd τ)
  have e : U * (B * C⁻¹).map ψ₁ * ((A' * C⁻¹).map ψ₂)⁻¹ = U * B.map ψ₁ * (A'.map ψ₂)⁻¹ := by
    rw [Mat.map_mul, Mat.map_mul, Mat.map_inv, Mat.map_inv, hCψ, Mat.mul_inv_rev, Mat.inv_inv hC2d]
    rw [mul_assoc U, mul_assoc (B.map ψ₁), ← mul_assoc (C.map ψ₂)⁻¹, Mat.inv_mul hC2d, one_mul, ← mul_assoc]
  rw [e] at hP
  have hQ : Par m (⊤ : Subring K) ((A' * B⁻¹).map ψ₂) := by
    have := (Fr.mem_iff hB).1 hA'
    exact this.map ψ₂ (fun _ _ => trivial)
  have := hP.mul hQ
  rw [Mat.map_mul, Mat.map_inv] at this
  have e2 : U * B.map ψ₁ * (A'.map ψ₂)⁻¹ * (A'.map ψ₂ * (B.map ψ₂)⁻¹) = U * (B.map ψ₁ * (B.map ψ₂)⁻¹) := by
    rw [mul_assoc (U * B.map ψ₁), ← mul_assoc (A'.map ψ₂)⁻¹, Mat.inv_mul hA'2d, one_mul, mul_assoc]
  rwa [e2] at this

end GlobalTheory.FlagPush
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagOfDominantPointAsTriangularMatrixStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_of_dominant_point_as_triangular_matrix : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ B ∈ E'.S (genericPoint Y.X), ∀ A ∈ E.S (f (genericPoint Y.X)), ∀ (K : Type) [Field K] (ψ₁ ψ₂ : Y.Fn →+* K) (U : Mat m K), spMap ψ₁ ≫ (ratOf Y).pt ≫ f = spMap ψ₂ ≫ (ratOf Y).pt ≫ f → Bears E' φ A (U * (B * (A.map φ)⁻¹).map ψ₁) (spMap ψ₂ ≫ (ratOf Y).pt) → (∀ u : X.Fn, ψ₁ (φ u) = ψ₂ (φ u)) ∧ Par m ⊤ (U * (B.map ψ₁ * (B.map ψ₂)⁻¹)) := by
  first | exact @GlobalTheory.FlagPush.flag_conv | exact GlobalTheory.FlagPush.flag_conv | (intros; apply GlobalTheory.FlagPush.flag_conv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftValuativeCriterionVarieties
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftValuativeCriterionVarieties
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagPush

theorem exists_lift_of_var : ∀ (F : Type) [Field F] (X Y : Var F) (f : Y.X ⟶ X.X), f ≫ X.str = Y.str → ∀ (K : Type) [Field K] (V : ValuationSubring K) (v₁ : Sp V ⟶ Y.X) (q₂ : Sp K ⟶ Y.X), q₂ ≫ f = spMap (algebraMap V K) ≫ v₁ ≫ f → ∃ v₂ : Sp V ⟶ Y.X, spMap (algebraMap V K) ≫ v₂ = q₂ ∧ v₂ ≫ f = v₁ ≫ f := by
  intro F _ X Y f hs K _ V v₁ q₂ hq
  haveI : IsProper (f ≫ X.str) := hs ▸ inferInstance
  haveI : UniversallyClosed f := UniversallyClosed.of_comp_of_isSeparated f X.str
  have hE : ValuativeCriterion.Existence f :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed f) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact) f).1
  obtain ⟨⟨l⟩⟩ := hE { R := V, K := K, i₁ := q₂, i₂ := v₁ ≫ f, commSq := ⟨hq⟩ }
  exact ⟨l.l, l.fac_left, l.fac_right⟩

end GlobalTheory.FlagPush
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftValuativeCriterionVarietiesStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_valuative_criterion_varieties : ∀ (F : Type) [Field F] (X Y : Var F) (f : Y.X ⟶ X.X), f ≫ X.str = Y.str → ∀ (K : Type) [Field K] (V : ValuationSubring K) (v₁ : Sp V ⟶ Y.X) (q₂ : Sp K ⟶ Y.X), q₂ ≫ f = spMap (algebraMap V K) ≫ v₁ ≫ f → ∃ v₂ : Sp V ⟶ Y.X, spMap (algebraMap V K) ≫ v₂ = q₂ ∧ v₂ ≫ f = v₁ ≫ f := by
  first | exact @GlobalTheory.FlagPush.exists_lift_of_var | exact GlobalTheory.FlagPush.exists_lift_of_var | (intros; apply GlobalTheory.FlagPush.exists_lift_of_var <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericPairFlagsDifferingOneStep
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush.Gen

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (g : A →+* B) (h : B →+* C) :
    spMap h ≫ spMap g = spMap (h.comp g) := by
  rw [← Spec.map_comp]
  rfl

theorem exists_genPair : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ B ∈ E'.S (genericPoint Y.X), ∀ (τ : ι) (a b : Fin (m τ)), a < b → ∃ ψ₂ : Y.Fn →+* RatFunc Y.Fn, GenPair Y (algebraMap Y.Fn (RatFunc Y.Fn)) ψ₂ ∧ (∀ u : X.Fn, algebraMap Y.Fn (RatFunc Y.Fn) (φ u) = ψ₂ (φ u)) ∧ Par m ⊤ (shear τ a b (RatFunc.X : RatFunc Y.Fn) * (B.map (algebraMap Y.Fn (RatFunc Y.Fn)) * (B.map ψ₂)⁻¹)) := by
  intro F _ X Y ι _ m E E' φ f hf B hB τ a b hab
  obtain ⟨V, c, t, hc, ht, hr⟩ := GlobalTheory.T.exists_valuationSubring_ratFunc_X_residue_zero Y.Fn
  obtain ⟨A, hA⟩ := E.nonempty (f (genericPoint Y.X))
  have hM : Par 0 ((ratOf Y).O (genericPoint Y.X)).toSubring (B * (A.map φ)⁻¹) := hf.sub _ B hB A hA
  obtain ⟨pt, hpt⟩ : ∃ pt : Sp Y.Fn ⟶ Y.X, pt = (ratOf Y).pt := ⟨_, rfl⟩
  have hpa (w) : pt w = genericPoint Y.X := hpt ▸ (ratOf Y).pt_apply w
  have hps : pt ≫ Y.str = spMap (algebraMap F Y.Fn) := hpt ▸ (ratOf Y).pt_s
  have hq : spMap (algebraMap V (RatFunc Y.Fn)) ≫ spMap c ≫ pt = spMap (algebraMap Y.Fn (RatFunc Y.Fn)) ≫ pt := by
    rw [← Category.assoc, spMap_comp, hc]
  have hh : Par 0 ⊤ (shear τ a b (RatFunc.X : RatFunc Y.Fn) *
      (B * (A.map φ)⁻¹).map (algebraMap Y.Fn (RatFunc Y.Fn))) := by
    refine Par.mul (ClosedPt.par_zero_top fun σ => ?_) (hM.map _ fun _ _ => trivial)
    rw [(GlobalTheory.T.blockMatrixElementaryShear_properties ι m τ a b hab _ _).1 σ]
    exact one_ne_zero
  have hx : ((spMap (algebraMap Y.Fn (RatFunc Y.Fn)) ≫ pt) ≫ f)
      (IsLocalRing.closedPoint (RatFunc Y.Fn)) = f (genericPoint Y.X) :=
    congrArg f (hpa _)
  have hA' : A ∈ E.S (((spMap (algebraMap Y.Fn (RatFunc Y.Fn)) ≫ pt) ≫ f)
      (IsLocalRing.closedPoint (RatFunc Y.Fn))) := (congrArg (fun z : X.X => A ∈ E.S z) hx).mpr hA
  obtain ⟨q₂, hq₂, hb⟩ : ∃ q₂ : Sp (RatFunc Y.Fn) ⟶ Y.X,
      q₂ ≫ f = (spMap (algebraMap Y.Fn (RatFunc Y.Fn)) ≫ pt) ≫ f ∧ Bears E' φ A (shear τ a b (RatFunc.X : RatFunc Y.Fn) *
      (B * (A.map φ)⁻¹).map (algebraMap Y.Fn (RatFunc Y.Fn))) q₂ := (hf.lifts (RatFunc Y.Fn) _ A hA' _ hh).exists
  have hs : f ≫ X.str = Y.str := hf.hom.inducedModelMorphism_comp_structureMap
  obtain ⟨v₂, hv₂, hv₂f⟩ := GlobalTheory.T.exists_lift_valuative_criterion_varieties F X Y f hs _ V (spMap c ≫ pt) q₂ (by
    rw [hq₂, ← hq]; simp only [Category.assoc])
  have hmeet : spMap (IsLocalRing.residue V) ≫ spMap c ≫ pt = spMap (IsLocalRing.residue V) ≫ v₂ := by
    subst hpt
    exact GlobalTheory.T.shearedGenericFlag_eq_genericFlag_at_special F X Y ι m E E' φ f hf B hB A hA τ a b hab _ V c t hr v₂
      (hv₂f.trans (Category.assoc _ _ _)) (by subst hv₂; rw [hc, ht]; exact hb)
  have h1 : (spMap c ≫ pt) (IsLocalRing.closedPoint V) = genericPoint Y.X := hpa _
  have h2 : v₂ (IsLocalRing.closedPoint V) = genericPoint Y.X := by
    rw [← ClosedPt.closedPt_comp v₂, ← hmeet, ClosedPt.closedPt_comp, h1]
  letI : Algebra F (RatFunc Y.Fn) := ((algebraMap Y.Fn (RatFunc Y.Fn)).comp (algebraMap F Y.Fn)).toAlgebra
  have hsp : q₂ (IsLocalRing.closedPoint (RatFunc Y.Fn)) ⤳ genericPoint Y.X := by
    have := ClosedPt.gen_specializes v₂ (IsLocalRing.closedPoint (RatFunc Y.Fn))
    rwa [hv₂, h2] at this
  have hstr : q₂ ≫ Y.str = spMap ((algebraMap Y.Fn (RatFunc Y.Fn)).comp (algebraMap F Y.Fn)) := by
    rw [← hs, ← Category.assoc, hq₂, Category.assoc, hs, Category.assoc, ← spMap_comp, hps]
  obtain ⟨ψ, hψ⟩ := exists_algHom_of_specializes_genericPoint F Y (RatFunc Y.Fn) q₂ hsp hstr
  subst hpt
  have hcv := GlobalTheory.T.flag_of_dominant_point_as_triangular_matrix F X Y ι m E E' φ f hf B hB A hA _ (algebraMap Y.Fn (RatFunc Y.Fn)) ψ.toRingHom
    (shear τ a b RatFunc.X) (by
      subst hψ
      exact (Category.assoc _ _ _).symm.trans (hq₂.symm.trans (Category.assoc _ _ _))) (by subst hψ; exact hb)
  refine ⟨ψ.toRingHom, ⟨?_, V, spMap c ≫ (ratOf Y).pt, v₂, hq, hv₂.trans hψ, hmeet, h1⟩, hcv.1, hcv.2⟩
  exact RingHom.ext fun r => (ψ.commutes r).symm

end GlobalTheory.FlagPush.Gen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericPairFlagsDifferingOneStepStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generic_pair_flags_differing_one_step : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ B ∈ E'.S (genericPoint Y.X), ∀ (τ : ι) (a b : Fin (m τ)), a < b → ∃ ψ₂ : Y.Fn →+* RatFunc Y.Fn, GenPair Y (algebraMap Y.Fn (RatFunc Y.Fn)) ψ₂ ∧ (∀ u : X.Fn, algebraMap Y.Fn (RatFunc Y.Fn) (φ u) = ψ₂ (φ u)) ∧ Par m ⊤ (shear τ a b (RatFunc.X : RatFunc Y.Fn) * (B.map (algebraMap Y.Fn (RatFunc Y.Fn)) * (B.map ψ₂)⁻¹)) := by
  first | exact @GlobalTheory.FlagPush.Gen.exists_genPair | exact GlobalTheory.FlagPush.Gen.exists_genPair | (intros; apply GlobalTheory.FlagPush.Gen.exists_genPair <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlmostLowerTriangularOfShearParabolic
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlmostLowerTriangularOfShearParabolic
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem shear_apply_of_ne {ι : Type} {m : ι → ℕ} (τ : ι) (a b : Fin (m τ)) {K : Type} [CommRing K] (t : K)
    {σ : ι} (h : σ ≠ τ) : shear τ a b t σ = 1 := by
  ext i k
  simp only [shear, Matrix.add_apply, Matrix.of_apply]
  rw [if_neg, add_zero]
  rintro ⟨h1, -⟩
  exact h (congrArg Sigma.fst h1)

theorem shear_self_mul_apply {ι : Type} {m : ι → ℕ} (τ : ι) (a b : Fin (m τ)) {K : Type} [CommRing K] (t : K)
    (A : Matrix (Fin (m τ)) (Fin (m τ)) K) (i c : Fin (m τ)) :
    (shear τ a b t τ * A) i c = A i c + if i = a then t * A b c else 0 := by
  have e : ∀ k, shear τ a b t τ i k = (1 : Matrix (Fin (m τ)) (Fin (m τ)) K) i k + if i = a ∧ k = b then t else 0 := by
    intro k
    simp only [shear, Matrix.add_apply, Matrix.of_apply]
    congr 1
    by_cases h1 : i = a <;> by_cases h2 : k = b <;> simp [h1, h2]
  rw [Matrix.mul_apply]
  simp only [e, add_mul, Finset.sum_add_distrib, Matrix.one_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  by_cases h1 : i = a <;> simp [h1]

theorem almostLow_of_shear : ∀ (ι : Type) (m : ι → ℕ) (τ : ι) (a b : Fin (m τ)), (b : ℕ) = a + 1 →
    ∀ (L K : Type) [Field L] [Field K] (j : L →+* K) (t : K), t ≠ 0 → ∀ C : Mat m L,
      Par m ⊤ (shear τ a b t * C.map j) → AlmostLow τ a b C := by
  intro ι m τ a b hab L K _ _ j t ht C hP
  have hmap : ∀ σ i c, (C.map j) σ i c = j (C σ i c) := fun _ _ _ => rfl
  have hL : ∀ σ, shear τ a b t σ * (C.map j) σ = (shear τ a b t * C.map j) σ := fun _ => rfl
  have hz : ∀ σ (i c : Fin (m σ)), i < c → (shear τ a b t σ * (C.map j) σ) i c = 0 := fun σ i c h => by
    rw [hL]; exact (hP σ).2.2.2 i c i.isLt h
  have hd : ∀ σ, (shear τ a b t σ * (C.map j) σ).det ≠ 0 := fun σ => by rw [hL]; exact (hP σ).2.1
  have hdiag : ∀ σ (i : Fin (m σ)), (shear τ a b t σ * (C.map j) σ) i i ≠ 0 := fun σ i => by
    have hbt : (shear τ a b t σ * (C.map j) σ).BlockTriangular OrderDual.toDual := fun p q hpq =>
      hz σ p q (OrderDual.toDual_lt_toDual.1 hpq)
    have := hd σ
    rw [Matrix.det_of_lowerTriangular _ hbt] at this
    exact Finset.prod_ne_zero_iff.1 this i (Finset.mem_univ _)
  have hab' : a < b := by rw [Fin.lt_def]; omega
  have hba : b ≠ a := ne_of_gt hab'
  refine ⟨fun σ hσ => hd σ ?_, ?_, ?_⟩
  · rw [Matrix.det_mul, Mat.det_map, hσ, map_zero, mul_zero]
  · intro h0
    have h1 := hz τ a b hab'
    have h2 := hdiag τ b
    rw [shear_self_mul_apply] at h1 h2
    rw [if_pos rfl, hmap, h0, map_zero, zero_add] at h1
    rw [if_neg hba, add_zero] at h2
    exact h2 ((mul_eq_zero.1 h1).resolve_left ht)
  · intro σ i c hic hn
    refine (map_eq_zero j).1 ?_
    rw [← hmap]
    by_cases hσ : σ = τ
    · subst hσ
      have hn' : ¬ (i = a ∧ c = b) := fun h => hn ⟨by rw [h.1], by rw [h.2]⟩
      have h1 := hz σ i c hic
      rw [shear_self_mul_apply] at h1
      by_cases hi : i = a
      · subst hi
        have hcb : c ≠ b := fun h => hn' ⟨rfl, h⟩
        have hbc : b < c := by
          rw [Fin.lt_def] at hic ⊢
          have : (c : ℕ) ≠ b := fun h => hcb (Fin.ext h)
          omega
        have h2 := hz σ b c hbc
        rw [shear_self_mul_apply, if_neg hba, add_zero] at h2
        rw [if_pos rfl, h2, mul_zero, add_zero] at h1
        exact h1
      · rw [if_neg hi, add_zero] at h1
        exact h1
    · have h1 := hz σ i c hic
      rw [shear_apply_of_ne τ a b t hσ, one_mul] at h1
      exact h1

end GlobalTheory.FlagPush
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlmostLowerTriangularOfShearParabolicStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAlmostLowerTriangular_of_shear_parabolic : ∀ (ι : Type) (m : ι → ℕ) (τ : ι) (a b : Fin (m τ)), (b : ℕ) = a + 1 → ∀ (L K : Type) [Field L] [Field K] (j : L →+* K) (t : K), t ≠ 0 → ∀ C : Mat m L, Par m ⊤ (shear τ a b t * C.map j) → AlmostLow τ a b C := by
  first | exact @GlobalTheory.FlagPush.almostLow_of_shear | exact GlobalTheory.FlagPush.almostLow_of_shear | (intros; apply GlobalTheory.FlagPush.almostLow_of_shear <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagSpaceIntersectionNumberAdjacentSwapNeg
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem interPoly_swap_adjacent : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ (gr : Root m → Y.Dv), IsGraded E' gr → ∀ (τ : ι) (a b : Fin (m τ)), (b : ℕ) = a + 1 → ∀ Q : MvPolynomial (Root m) ℝ, Y.interPoly gr (rename (Equiv.swap (⟨τ, a⟩ : Root m) ⟨τ, b⟩) Q) = - Y.interPoly gr Q := by
  intro F _ X Y ι _ m E E' φ f hR gr hgr τ a b hab Q
  obtain ⟨B, hB, hBg⟩ := hgr
  have hlt : a < b := by
    show (a : ℕ) < b
    omega
  obtain ⟨ψ₂, hgen, hφ, hpar⟩ := GlobalTheory.T.exists_generic_pair_flags_differing_one_step F X Y ι m E E' φ f hR B hB τ a b hlt
  obtain ⟨W, j, h1, h2⟩ := GlobalTheory.T.exists_doubleSpace_of_genericFunctionFieldPair F Y _ _ _ hgen
  have hs : W.Small := GlobalTheory.T.doubleSpace_small_of_functionField_embeds_ratFunc F Y W j h1
  have e1 : ∀ u, j (W.α₁ u) = algebraMap Y.Fn (RatFunc Y.Fn) u := fun u => DFunLike.congr_fun h1 u
  have e2 : ∀ u, j (W.α₂ u) = ψ₂ u := fun u => DFunLike.congr_fun h2 u
  have hα : ∀ u : X.Fn, W.α₁ (φ u) = W.α₂ (φ u) := fun u =>
    j.injective (by rw [e1, e2, hφ])
  have m1 : (B.map W.α₁).map j = B.map (algebraMap Y.Fn (RatFunc Y.Fn)) := by
    funext σ; ext i k; exact e1 _
  have m2 : (B.map W.α₂).map j = B.map ψ₂ := by
    funext σ; ext i k; exact e2 _
  have hlow : AlmostLow τ a b (B.map W.α₁ * (B.map W.α₂)⁻¹) := by
    refine GlobalTheory.T.isAlmostLowerTriangular_of_shear_parabolic ι m τ a b hab _ _ j RatFunc.X RatFunc.X_ne_zero _ ?_
    rw [Mat.map_mul, Mat.map_inv, m1, m2]
    exact hpar
  obtain ⟨D₁, D₂, Θ, h⟩ := GlobalTheory.T.exists_divisors_doubleFlagSpace F X Y ι m E E' φ f hR gr B hB hBg W hα τ a b hab hlow
  have hne : (⟨τ, a⟩ : Root m) ≠ ⟨τ, b⟩ := fun h => hlt.ne (eq_of_heq (Sigma.mk.inj h).2)
  have := GlobalTheory.T.intersectionNumber_swap_of_doubleSpace F Y W hs (Root m) _ _ hne gr D₁ D₂ Θ h Q
  convert this

end GlobalTheory.FlagPush
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagSpaceIntersectionNumberAdjacentSwapNegStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagSpace_intersectionNumber_adjacent_swap_neg : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ (gr : Root m → Y.Dv), IsGraded E' gr → ∀ (τ : ι) (a b : Fin (m τ)), (b : ℕ) = a + 1 → ∀ Q : MvPolynomial (Root m) ℝ, Y.interPoly gr (rename (Equiv.swap (⟨τ, a⟩ : Root m) ⟨τ, b⟩) Q) = - Y.interPoly gr Q := by
  first | exact @GlobalTheory.FlagPush.interPoly_swap_adjacent | exact GlobalTheory.FlagPush.interPoly_swap_adjacent | (intros; apply GlobalTheory.FlagPush.interPoly_swap_adjacent <;> assumption)
end
