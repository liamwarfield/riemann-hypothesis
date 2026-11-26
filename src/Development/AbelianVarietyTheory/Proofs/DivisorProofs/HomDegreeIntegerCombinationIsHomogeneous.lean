module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionCorrectionIsTopDegreeForm
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.NefEffectiveCones.EventuallyEvalNegOfCoeffNeg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyFlatFinrank
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundleGeometricDegreeRaiseWeight

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionPullbackEqDegreeMulIntersection
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionPullbackIsogenyEqDegreeMul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineFiniteFree
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM

namespace GlobalTheory.GenFree

theorem exists_free_away (A M : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [AddCommGroup M] [Module A M]
    [Module.Finite A M] : ∃ g : A, g ≠ 0 ∧ Module.Free (Localization.Away g) (LocalizedModule.Away g M) := by
  haveI : Module.FinitePresentation A M := Module.finitePresentation_of_finite A M
  obtain ⟨g, hg, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    (nonZeroDivisors A) (LocalizedModule.mkLinearMap (nonZeroDivisors A) M) (FractionRing A)
  exact ⟨g, nonZeroDivisors.ne_zero hg, hfree⟩

theorem free_basicOpen {X Y : Scheme.{0}} (f : X ⟶ Y) {V : Y.Opens} (hV : IsAffineOpen V)
    (hV' : IsAffineOpen (f ⁻¹ᵁ V)) (g : Γ(Y, V))
    (hfree : letI := (f.app V).hom.toAlgebra
      Module.Free (Localization.Away g) (LocalizedModule.Away g Γ(X, f ⁻¹ᵁ V))) :
    letI := (f.app (Y.basicOpen g)).hom.toAlgebra
    Module.Free Γ(Y, Y.basicOpen g) Γ(X, f ⁻¹ᵁ Y.basicOpen g) := by
  letI : Algebra Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := (f.app V).hom.toAlgebra
  have hpre : f ⁻¹ᵁ Y.basicOpen g = X.basicOpen (f.app V g) := Scheme.preimage_basicOpen _ _
  let A := Γ(Y, V)
  let M := Γ(X, f ⁻¹ᵁ V)
  let R := Γ(Y, Y.basicOpen g)
  let N := Γ(X, f ⁻¹ᵁ Y.basicOpen g)
  letI : Algebra A R := (Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op).hom.toAlgebra
  haveI : IsLocalization.Away g R := hV.isLocalization_basicOpen g
  have hle : f ⁻¹ᵁ Y.basicOpen g ≤ f ⁻¹ᵁ V := f.preimage_mono (Y.basicOpen_le g)
  letI : Algebra M N := (X.presheaf.map (homOfLE hle).op).hom.toAlgebra
  haveI : IsLocalization.Away (algebraMap A M g) N :=
    hV'.isLocalization_of_eq_basicOpen (f.app V g) (homOfLE hle) hpre
  letI : Algebra R N := (f.app (Y.basicOpen g)).hom.toAlgebra
  letI : Algebra A N := ((algebraMap R N).comp (algebraMap A R)).toAlgebra
  haveI : IsScalarTower A R N := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower A M N := IsScalarTower.of_algebraMap_eq fun a => by
    change (f.app _).hom ((Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op).hom a) =
      (X.presheaf.map (homOfLE hle).op).hom ((f.app V).hom a)
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]
    rfl
  haveI : IsLocalization (Algebra.algebraMapSubmonoid M (Submonoid.powers g)) N := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]; infer_instance
  haveI : IsLocalizedModule (Submonoid.powers g) (IsScalarTower.toAlgHom A M N).toLinearMap :=
    isLocalizedModule_iff_isLocalization.2 inferInstance
  let l := IsLocalizedModule.linearEquiv (Submonoid.powers g)
    (LocalizedModule.mkLinearMap (Submonoid.powers g) M) (IsScalarTower.toAlgHom A M N).toLinearMap
  let b₀ := Module.Free.chooseBasis (Localization.Away g) (LocalizedModule.Away g M)
  let τ := IsLocalization.algEquiv (Submonoid.powers g) (Localization.Away g) R
  let Ψ := l.symm ≪≫ₗ b₀.repr.restrictScalars A ≪≫ₗ Finsupp.mapRange.linearEquiv τ.toLinearEquiv
  let Ψ' := Ψ.extendScalarsOfIsLocalization (Submonoid.powers g) R
  exact Module.Free.of_basis (Module.Basis.ofRepr Ψ')

theorem exists_dim_eq (F : Type) [Field F] {Y : Scheme.{0}} [IsIntegral Y] (q : Y ⟶ Sp F) [LocallyOfFiniteType q] :
    ∃ n : ℕ, topologicalKrullDim Y = n := by
  obtain ⟨U, hU, hxU, -⟩ := Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens (Opens.mem_top (genericPoint Y))
  replace hU : IsAffineOpen U := hU
  haveI : Nonempty U := ⟨⟨_, hxU⟩⟩
  let φ := Spec.preimage (hU.fromSpec ≫ q)
  have hφ : Spec.map φ = hU.fromSpec ≫ q := Spec.map_preimage _
  letI : Algebra F Γ(Y, U) := φ.hom.toAlgebra
  have : Algebra.FiniteType F Γ(Y, U) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := φ)).mp (hφ ▸ inferInstance)
  obtain ⟨d, h₁, -⟩ := exists_ringKrullDim_eq_and_trdeg_eq F Γ(Y, U)
  refine ⟨d, ?_⟩
  rw [← GlobalTheory.OpenDim.topologicalKrullDim_open F q U ⟨_, hxU⟩, ← h₁, ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding hU.range_fromSpec

theorem exists_affine_finite_free : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (sY : Y ⟶ Sp k) (f : X ⟶ Y), IsProjOver (f ≫ sY) → IsProjOver sY → f (genericPoint X) = genericPoint Y → topologicalKrullDim X ≤ topologicalKrullDim Y → ∀ n : ℕ, f.residueDegree (genericPoint X) = n → ∃ V : Y.Opens, genericPoint Y ∈ V ∧ IsAffineOpen V ∧ IsAffineOpen (f ⁻¹ᵁ V) ∧ (letI := (f.app V).hom.toAlgebra; Module.Free Γ(Y, V) Γ(X, f ⁻¹ᵁ V) ∧ Module.Finite Γ(Y, V) Γ(X, f ⁻¹ᵁ V) ∧ Module.finrank Γ(Y, V) Γ(X, f ⁻¹ᵁ V) = n) := by
  intro k _ X Y _ _ sY f hX hY hη hdim n hn
  have := GlobalTheory.SchemeWords.isProper_of_isProjOver hX
  have := GlobalTheory.SchemeWords.isProper_of_isProjOver hY
  have : IsProper f := IsProper.of_comp f sY
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : IsDominant f := ⟨(dense_iff_closure_eq.2 (genericPoint_spec Y)).mono
    (Set.singleton_subset_iff.2 ⟨_, hη⟩)⟩
  have hs := surjective_of_isDominant_of_isClosed_range f f.isClosedMap.isClosed_range
  obtain ⟨d, hdY⟩ := exists_dim_eq k sY
  have hdX : topologicalKrullDim X = d :=
    (le_antisymm hdim (PosBaseChange.dim_le_of_isClosedMap f.isClosedMap f.surjective)).trans hdY
  have hd : f.residueDegree (genericPoint X) ≠ 0 :=
    GenFinite.residueDegree_genericPoint_ne_zero k X Y sY f d inferInstance inferInstance hs hdX hdY
  obtain ⟨V₀, hV₀, hfin⟩ := exists_isFinite_morphismRestrict_of_finite_preimage_singleton f
    (genericPoint Y) ((Set.finite_singleton (genericPoint X)).subset
      fun y hy => GenFiniteEtale.eq_genericPoint f hη hd hy)
  obtain ⟨V, hV, hxV, hle⟩ := Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens hV₀
  replace hV : IsAffineOpen V := hV
  haveI : Nonempty V := ⟨⟨_, hxV⟩⟩
  obtain ⟨hW, hf⟩ := GenFiniteEtale.finite_app_of_le f hV hle
  letI := (f.app V).hom.toAlgebra
  haveI : IsNoetherianRing Γ(Y, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  haveI : Module.Finite Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := hf
  obtain ⟨g, hg, hfree⟩ := exists_free_away Γ(Y, V) Γ(X, f ⁻¹ᵁ V)
  have hU := hV.basicOpen g
  have hxU := GenFiniteEtale.genericPoint_mem_basicOpen hg
  obtain ⟨hW', hf'⟩ := GenFiniteEtale.finite_app_of_le f hU ((Y.basicOpen_le g).trans hle)
  refine ⟨Y.basicOpen g, hxU, hU, hW', free_basicOpen f hV hW g hfree, hf', ?_⟩
  have := (GenFiniteEtale.affine_pair f hη hd hU hW' le_rfl (show f _ ∈ Y.basicOpen g from hη ▸ hxU)).2.2.1
  rw [← f.app_eq_appLE] at this
  exact this.trans hn

end GlobalTheory.GenFree
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionPullbackIsogenyEqDegreeMul
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem inter_pull_isogeny_eq_deg_mul : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), IsIsogeny f →
    ∀ (J : Type) [Fintype J], Fintype.card J = A.dim → ∀ c : J → Pic B.X.left,
    inter A (fun j => CechPic.pull f.hom.left (c j)) = deg f * inter B c := by
  intro K _ A B f hf J _ hJ c
  obtain ⟨hdim, hflat, -, hrank⟩ := isogeny_flat_finrank K A B f hf
  haveI : IsFinite f.hom.left := hf.1
  haveI : Surjective f.hom.left := hf.2
  haveI := (isIntegral_isLocallyNoetherian_compactSpace K A).1
  haveI := (isIntegral_isLocallyNoetherian_compactSpace K B).1
  have hAproj := (GlobalTheory.AV.AbVarProj.strHom_eq_and_isProjOver K A).2
  have hBproj := (GlobalTheory.AV.AbVarProj.strHom_eq_and_isProjOver K B).2
  have hw : f.hom.left ≫ B.X.hom = A.X.hom := Over.w f.hom
  have hXproj : IsProjOver (f.hom.left ≫ B.X.hom) := by rw [hw]; exact hAproj
  have hAd := topologicalKrullDim_eq_dim K A
  have hBd := topologicalKrullDim_eq_dim K B

  have hgen : f.hom.left (genericPoint A.X.left) = genericPoint B.X.left := by
    have h1 := (genericPoint_spec A.X.left).image f.hom.left.continuous
    rw [Set.image_univ_of_surjective f.hom.left.surjective, closure_univ] at h1
    exact h1.eq (genericPoint_spec B.X.left)
  obtain ⟨V, hgV, hV, hV', hfree⟩ := GlobalTheory.GenFree.exists_affine_finite_free K A.X.left B.X.left B.X.hom
    f.hom.left hXproj hBproj hgen (by rw [hAd, hBd, hdim]) (f.hom.left.residueDegree (genericPoint A.X.left)) rfl
  set n := f.hom.left.residueDegree (genericPoint A.X.left)

  have hn : deg f = n := by
    letI := (f.hom.left.app V).hom.toAlgebra
    obtain ⟨hfr, hfin, hrk⟩ := hfree
    haveI := hfr
    haveI := hfin
    haveI : Module.Flat Γ(B.X.left, V) Γ(A.X.left, f.hom.left ⁻¹ᵁ V) := inferInstance
    obtain ⟨z, -⟩ : genericPoint B.X.left ∈ Set.range hV.fromSpec := by rwa [hV.range_fromSpec]
    have e := Scheme.Hom.finrank_of_isPullback _ _ _ _ (GlobalTheory.isPullback_fromSpec_app f.hom.left hV hV') z
    rw [hrank] at e
    have e2 := (Scheme.Hom.finrank_SpecMap_algebraMap Γ(B.X.left, V) Γ(A.X.left, f.hom.left ⁻¹ᵁ V) z).symm.trans e
    rw [Module.rankAtStalk_eq_finrank_of_free, hrk] at e2
    exact e2.symm

  choose L hL hc using fun j => cls_surj (c j)
  obtain rfl : c = fun j => cls (L j) (hL j) := funext fun j => (hc j).symm
  let e : Fin A.dim ≃ J := (Fintype.equivFinOfCardEq hJ).symm
  have key := GlobalTheory.FieldProj.interNum_pull_eq_mul K A.X.left B.X.left B.X.hom f.hom.left hXproj hBproj V n
    hgV hV hV' hfree A.dim (by rw [hBd, hdim]) (fun i => L (e i)) (fun i => hL (e i))
  rw [hw] at key
  rw [hn]
  have hL' : ∀ i, ((fun i => L (e i)) i).pull f.hom.left |>.IsLB := fun i => Semi.LB.isLB_pull (hL (e i)) _
  letI := GlobalTheory.algebraΓOfHom A.X.hom
  letI := GlobalTheory.algebraΓOfHom B.X.hom
  rw [interNum_eq_multiDiff K _ hL', interNum_eq_multiDiff K _ (fun i => hL (e i))] at key
  unfold inter
  rw [← multiDiff_comp_equiv e, ← multiDiff_comp_equiv e (fun j => cls (L j) (hL j))]
  convert key using 3
  · rename_i i
    exact (cls_pull (hL (e i)) f.hom.left _).symm
  · rfl

end GlobalTheory.AV.AbVar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionPullbackIsogenyEqDegreeMulStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_pullback_isogeny_eq_degree_mul : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), IsIsogeny f → ∀ (J : Type) [Fintype J], Fintype.card J = A.dim → ∀ c : J → Pic B.X.left, inter A (fun j => CechPic.pull f.hom.left (c j)) = deg f * inter B c := by
  first | (exact @GlobalTheory.AV.AbVar.inter_pull_isogeny_eq_deg_mul) | (exact GlobalTheory.AV.AbVar.inter_pull_isogeny_eq_deg_mul) | (intros; apply GlobalTheory.AV.AbVar.inter_pull_isogeny_eq_deg_mul  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackNotSurjectiveEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackNotSurjectiveEqZero
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.AbVar

theorem hom_genericPoint_ne {K : Type} [Field K] {A B : AbVar K} (f : A ⟶ B) [IsIntegral A.X.left]
    [IsIntegral B.X.left] (hns : ¬ Surjective f.hom.left) :
    f.hom.left (genericPoint A.X.left) ≠ genericPoint B.X.left := by
  intro h
  apply hns
  have : IsProper A.X.hom := A.ab.proper
  have : IsProper B.X.hom := B.ab.proper
  have hw : f.hom.left ≫ B.X.hom = A.X.hom := Over.w f.hom
  have : IsProper (f.hom.left ≫ B.X.hom) := by rw [hw]; infer_instance
  have : IsProper f.hom.left := IsProper.of_comp _ B.X.hom
  have hcl : IsClosed (Set.range f.hom.left) := by
    rw [← Set.image_univ]; exact f.hom.left.isClosedMap _ isClosed_univ
  have hsub : closure ({genericPoint B.X.left} : Set B.X.left) ⊆ Set.range f.hom.left :=
    hcl.closure_subset_iff.2 (Set.singleton_subset_iff.2 ⟨_, h⟩)
  rw [(genericPoint_spec B.X.left).def] at hsub
  exact ⟨fun y => hsub (Set.mem_univ y)⟩

theorem inter_pull_eq_zero_of_not_surjective : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), A.dim = B.dim → ¬ Surjective f.hom.left → ∀ (J : Type) [Fintype J], Fintype.card J = A.dim → ∀ c : J → Pic B.X.left, inter A (fun j => CechPic.pull f.hom.left (c j)) = 0 := by
  intro K _ A B f hdim hns J _ hJ c
  haveI := (GlobalTheory.AV.AbVar.isIntegral_isLocallyNoetherian_compactSpace K A).1
  haveI := (GlobalTheory.AV.AbVar.isIntegral_isLocallyNoetherian_compactSpace K B).1
  letI := A.algΓ
  obtain ⟨hs, hp⟩ := GlobalTheory.AV.AbVarProj.strHom_eq_and_isProjOver K A
  choose L hL hc using fun j => cls_surj (c j)
  have hne := hom_genericPoint_ne f hns
  have hη : genericPoint B.X.left ∈ (closure ({f.hom.left (genericPoint A.X.left)} : Set B.X.left))ᶜ :=
    fun h => hne (((specializes_iff_mem_closure.2 h).antisymm (genericPoint_specializes _)).eq)
  have h1 := GlobalTheory.PullVanish.dim_closure_add_one_le (genericPoint_specializes (f.hom.left (genericPoint A.X.left)))
    isClosed_closure.isOpen_compl hη (fun h => h (subset_closure rfl))
  have h2 : topologicalKrullDim (closure ({genericPoint B.X.left} : Set B.X.left)) = topologicalKrullDim B.X.left := by
    rw [(genericPoint_spec B.X.left).def]
    exact (Homeomorph.Set.univ B.X.left).isHomeomorph.topologicalKrullDim_eq
  have hB : topologicalKrullDim B.X.left ≤ (A.dim : ℕ) := by
    rw [GlobalTheory.AV.AbVar.topologicalKrullDim_eq_dim K B, hdim]
  have h3 := GlobalTheory.PullVanish.withBot_lt_of_add_one_le_nat (h1.trans (h2.trans_le hB))
  have hA : topologicalKrullDim A.X.left ≤ ((0 + A.dim : ℕ) : WithBot ℕ∞) := by
    rw [Nat.zero_add, GlobalTheory.AV.AbVar.topologicalKrullDim_eq_dim K A]
  let e : Fin 0 ⊕ Fin A.dim ≃ J := (Equiv.emptySum (Fin 0) (Fin A.dim)).trans (Fintype.equivFinOfCardEq hJ).symm
  have h := GlobalTheory.PullVanish.interNum_pull_eq_zero K 0 A.dim A.X.left B.X.left (hs ▸ hp) hA f.hom.left h3
    (fun i => i.elim0) (fun i => i.elim0) (fun a => L (e (.inr a))) (fun a => hL _)
  have hL' : ∀ j, ((L j).pull f.hom.left).IsLB := fun j => pull_isLB (hL j) _
  have hcl : (fun j => CechPic.pull f.hom.left (c j)) = fun j => cls ((L j).pull f.hom.left) (hL' j) := by
    funext j; rw [← hc j]; rfl
  rw [inter, hcl, ← interNum_eq_multiDiff K _ hL', ← interNum_comp_equiv K _ hL' e, ← h]
  congr 1
  funext x
  rcases x with i | a
  · exact i.elim0
  · rfl

end GlobalTheory.AV.AbVar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackNotSurjectiveEqZeroStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_number_pullback_not_surjective_eq_zero : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), A.dim = B.dim → ¬ Surjective f.hom.left → ∀ (J : Type) [Fintype J], Fintype.card J = A.dim → ∀ c : J → Pic B.X.left, inter A (fun j => CechPic.pull f.hom.left (c j)) = 0 := by
  first | (exact @GlobalTheory.AV.AbVar.inter_pull_eq_zero_of_not_surjective) | (exact GlobalTheory.AV.AbVar.inter_pull_eq_zero_of_not_surjective) | (intros; apply GlobalTheory.AV.AbVar.inter_pull_eq_zero_of_not_surjective  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionPullbackEqDegreeMulIntersection
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem inter_pull_eq_deg_mul_inter : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), A.dim = B.dim →
    ∀ (J : Type) [Fintype J], Fintype.card J = A.dim → ∀ c : J → Pic B.X.left,
      inter A (fun j => CechPic.pull f.hom.left (c j)) = deg f * inter B c := by
  intro K _ A B f hd J _ hJ c
  by_cases hi : IsIsogeny f
  · exact GlobalTheory.T.intersection_pullback_isogeny_eq_degree_mul K A B f hi J hJ c
  · have hs : ¬ Surjective f.hom.left := by
      intro hs
      exact hi ⟨GlobalTheory.AV.AbVar.isFinite_of_surjective_of_dim_eq K A B f hd hs, hs⟩
    rw [GlobalTheory.T.intersection_number_pullback_not_surjective_eq_zero K A B f hd hs J hJ c, deg, if_neg hi]
    simp

end GlobalTheory.AV.AbVar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionPullbackEqDegreeMulIntersectionStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_pullback_eq_degree_mul_intersection : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), A.dim = B.dim → ∀ (J : Type) [Fintype J], Fintype.card J = A.dim → ∀ c : J → Pic B.X.left, inter A (fun j => CechPic.pull f.hom.left (c j)) = deg f * inter B c := by
  first | (exact @GlobalTheory.AV.AbVar.inter_pull_eq_deg_mul_inter) | (exact GlobalTheory.AV.AbVar.inter_pull_eq_deg_mul_inter) | (intros; apply GlobalTheory.AV.AbVar.inter_pull_eq_deg_mul_inter  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoSmulPullbackSymmetricClassIntegralCombination
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoSmulPullbackSymmetricClassIntegralCombination
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.QuadSum

variable {K : Type} [Field K]

theorem hom_finset_sum {B A : AbVar K} {J : Type} (s : Finset J) (g : J → (B ⟶ A)) :
    Hom.hom (A := B) (B := A) (show B ⟶ A from ∑ i ∈ s, g i) = ∏ i ∈ s, (g i).hom := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, add_hom, ih]

theorem lam_symm {A : AbVar K} (c : Pic A.X.left) {Y : Over (Sp K)} (x y : Y ⟶ A.X) :
    AbVar.lam c x y = AbVar.lam c y x := by
  unfold AbVar.lam
  rw [mul_comm x y]
  abel

theorem lam_prod_right {A : AbVar K} (c : Pic A.X.left) {Y : Over (Sp K)} (x : Y ⟶ A.X) {J : Type}
    (s : Finset J) (y : J → (Y ⟶ A.X)) :
    AbVar.lam c x (∏ j ∈ s, y j) = ∑ j ∈ s, AbVar.lam c x (y j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (GlobalTheory.T.abelianVarietyMumfordClass_bilinear K A c Y x 1 1 0).2.2.1
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, (GlobalTheory.T.abelianVarietyMumfordClass_bilinear K A c Y x (y a) _ 0).1, ih]

theorem lam_prod_left {A : AbVar K} (c : Pic A.X.left) {Y : Over (Sp K)} {J : Type}
    (s : Finset J) (x : J → (Y ⟶ A.X)) (y : Y ⟶ A.X) :
    AbVar.lam c (∏ i ∈ s, x i) y = ∑ i ∈ s, AbVar.lam c (x i) y := by
  rw [lam_symm, lam_prod_right]
  exact Finset.sum_congr rfl (fun i _ => lam_symm c y (x i))

theorem lam_zpow_zpow {A : AbVar K} (c : Pic A.X.left) {Y : Over (Sp K)} (x y : Y ⟶ A.X) (m n : ℤ) :
    AbVar.lam c (x ^ m) (y ^ n) = (m * n) • AbVar.lam c x y := by
  rw [(GlobalTheory.T.abelianVarietyMumfordClass_bilinear K A c Y (x ^ m) y y n).2.2.2.2, (GlobalTheory.T.abelianVarietyMumfordClass_bilinear K A c Y x y y m).2.2.2.1, smul_smul,
    mul_comm n m]

end GlobalTheory.AV.QuadSum

theorem GlobalTheory.AV.QuadSum.pull_sum_smul : ∀ (K : Type) [Field K] (B A : AbVar K) (c : Pic A.X.left), CechPic.pull (Hom.hom (-(𝟙 A))).left c = c → ∀ (n : ℕ) (f : Fin n → (B ⟶ A)) (m : Fin n → ℤ), 2 • CechPic.pull (Hom.hom (A := B) (B := A) (show B ⟶ A from ∑ i, m i • f i)).left c = ∑ i, ∑ j, (m i * m j) • AbVar.lam c (f i).hom (f j).hom := by
  intro K _ B A c hc n f m
  rw [← (GlobalTheory.T.mumfordClass_symmetric_pullback_quadratic K B A c hc (∑ i, m i • f i) 1).1, QuadSum.hom_finset_sum, QuadSum.lam_prod_left]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [QuadSum.lam_prod_right]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [zsmul_hom, zsmul_hom, QuadSum.lam_zpow_zpow]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoSmulPullbackSymmetricClassIntegralCombinationStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_smul_pullback_symmetric_class_integral_combination : ∀ (K : Type) [Field K] (B A : AbVar K) (c : Pic A.X.left), CechPic.pull (Hom.hom (-(𝟙 A))).left c = c → ∀ (n : ℕ) (f : Fin n → (B ⟶ A)) (m : Fin n → ℤ), 2 • CechPic.pull (Hom.hom (A := B) (B := A) (show B ⟶ A from ∑ i, m i • f i)).left c = ∑ i, ∑ j, (m i * m j) • AbVar.lam c (f i).hom (f j).hom := by
  first | (exact @GlobalTheory.AV.QuadSum.pull_sum_smul) | (exact GlobalTheory.AV.QuadSum.pull_sum_smul) | (intros; apply GlobalTheory.AV.QuadSum.pull_sum_smul  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyTopSelfIntersectionAmplePos
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyTopSelfIntersectionAmplePos
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.AV.AmpleTopPos

theorem inter_comp_equiv {K : Type} [Field K] (A : AbVar K) {J J' : Type} [Fintype J] [Fintype J']
    (e : J' ≃ J) (c : J → Pic A.X.left) : inter A (c ∘ e) = inter A c := by
  unfold inter
  rw [GlobalTheory.multiDiff_comp_equiv]

theorem inter_top_pos : ∀ (K : Type) [Field K] (A : AbVar K) (c : Pic A.X.left), IsAmpleCls c →
    ∀ (J : Type) [Fintype J], Fintype.card J = A.dim → 0 < inter A (fun _ : J => c) := by
  intro K _ A c hc J _ hJ
  obtain ⟨L, hL, hr, rfl⟩ := hc
  have hA : IsAmpleLB L := (GlobalTheory.AmpleClsIff.isAmpleCls_cls_iff K A L hL).1 ⟨L, hL, hr, rfl⟩
  have e : Fin A.dim ≃ J := (Fintype.equivFinOfCardEq hJ).symm
  have h1 : inter A (fun _ : J => cls L hL) = inter A (fun _ : Fin A.dim => cls L hL) :=
    (inter_comp_equiv A e (fun _ : J => cls L hL)).symm
  rw [h1, GlobalTheory.T.abelianVariety_intersection_eq_lineBundleIntersection K A (Fin A.dim) (fun _ => L) (fun _ => hL)]
  letI := A.algΓ
  obtain ⟨hI, -, -⟩ := GlobalTheory.AV.AbVar.isIntegral_isLocallyNoetherian_compactSpace K A
  obtain ⟨hs, hp⟩ := GlobalTheory.AV.AbVarProj.strHom_eq_and_isProjOver K A
  have hp' : IsProjOver (strHom K (X := A.X.left)) := by rw [hs]; exact hp
  exact GlobalTheory.CompanionTheory.NefKleiman.interNum_top_pos_of_isAmpleLB K A.X.left hp' A.dim
    (GlobalTheory.AV.AbVar.topologicalKrullDim_eq_dim K A) L hA

end GlobalTheory.AV.AmpleTopPos
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyTopSelfIntersectionAmplePosStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianVariety_topSelfIntersection_ample_pos : ∀ (K : Type) [Field K] (A : AbVar K) (c : Pic A.X.left), IsAmpleCls c → ∀ (J : Type) [Fintype J], Fintype.card J = A.dim → 0 < inter A (fun _ : J => c) := by
  first | (exact @GlobalTheory.AV.AmpleTopPos.inter_top_pos) | (exact GlobalTheory.AV.AmpleTopPos.inter_top_pos) | (intros; apply GlobalTheory.AV.AmpleTopPos.inter_top_pos  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultilinearQuadraticIsHomogeneous
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem multilinear_quadratic_isHomogeneous : ∀ (P : Type) [AddCommGroup P] (g n : ℕ) (M : (Fin g → P) →ₘₗ[ℤ] ℤ) (a : Fin n → Fin n → P), ∃ F : MvPolynomial (Fin n) ℤ, F.IsHomogeneous (2 * g) ∧ ∀ m : Fin n → ℤ, MvPolynomial.eval m F = M (fun _ => ∑ i, ∑ j, (m i * m j) • a i j) := by
  intro P _ g n M a
  refine ⟨∑ r : Fin g → Fin n × Fin n, MvPolynomial.C (M (fun k => a (r k).1 (r k).2)) *
      ∏ k, (MvPolynomial.X (r k).1 * MvPolynomial.X (r k).2), ?_, ?_⟩
  · apply MvPolynomial.IsHomogeneous.sum
    intro r _
    have hX : ∀ k, (MvPolynomial.X (R := ℤ) (r k).1 * MvPolynomial.X (r k).2).IsHomogeneous 2 :=
      fun k => (MvPolynomial.isHomogeneous_X ℤ _).mul (MvPolynomial.isHomogeneous_X ℤ _)
    have h := (MvPolynomial.isHomogeneous_C (Fin n) (M fun k => a (r k).1 (r k).2)).mul
      (MvPolynomial.IsHomogeneous.prod Finset.univ _ (fun _ => 2) (fun k _ => hX k))
    convert h using 1
    simp [mul_comm]
  · intro m
    have hx : (fun _ : Fin g => ∑ i, ∑ j, (m i * m j) • a i j) =
        fun _ => ∑ p : Fin n × Fin n, (m p.1 * m p.2) • a p.1 p.2 := by
      funext _; exact (Fintype.sum_prod_type' (fun i j => (m i * m j) • a i j)).symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hx, MultilinearMap.map_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, MvPolynomial.eval_C, map_prod, MvPolynomial.eval_X]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [MultilinearMap.map_smul_univ, smul_eq_mul, mul_comm]
    simp only [RingHom.id_apply]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomDegreeIntegerCombinationIsHomogeneous
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.AV.AbVar.multilinear_quadratic_isHomogeneous' (P : Type*) [AddCommGroup P] (g n : ℕ)
    (M : (Fin g → P) →ₘₗ[ℤ] ℤ) (a : Fin n → Fin n → P) :
    ∃ F : MvPolynomial (Fin n) ℤ, F.IsHomogeneous (2 * g) ∧
      ∀ m : Fin n → ℤ, MvPolynomial.eval m F = M (fun _ => ∑ i, ∑ j, (m i * m j) • a i j) := by
  let φ : (Fin n → Fin n → ℤ) →ₗ[ℤ] P :=
    { toFun := fun x => ∑ i, ∑ j, x i j • a i j
      map_add' := fun x y => by
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun r x => by
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply] }
  let e : Fin n → Fin n → (Fin n → Fin n → ℤ) := fun i j => Pi.single i (Pi.single j 1)
  have he : ∀ i j, φ (e i j) = a i j := by
    intro i j
    simp only [φ, e, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Finset.sum_eq_single i (fun k _ hk => by simp [hk]) (by simp)]
    rw [Finset.sum_eq_single j (fun k _ hk => by simp [hk]) (by simp)]
    simp
  obtain ⟨F, hF, hFe⟩ := GlobalTheory.multilinear_quadratic_isHomogeneous (Fin n → Fin n → ℤ) g n
    (M.compLinearMap (fun _ => φ)) e
  refine ⟨F, hF, fun m => ?_⟩
  rw [hFe m, MultilinearMap.compLinearMap_apply]
  congr 1
  simp only [map_sum, map_smul, he]

theorem GlobalTheory.AV.AbVar.deg_isHomogeneousPoly : ∀ (K : Type) [Field K] (A B : AbVar K), A.dim = B.dim → ∀ (n : ℕ) (f : Fin n → (A ⟶ B)), ∃ F : MvPolynomial (Fin n) ℚ, F.IsHomogeneous (2 * A.dim) ∧ ∀ m : Fin n → ℤ, MvPolynomial.eval (fun i => (m i : ℚ)) F = (deg (∑ i, m i • f i) : ℚ) := by
  intro K _ A B hAB n f
  obtain ⟨c, hamp, hsym⟩ := GlobalTheory.AV.AbVar.exists_symm_ample K B
  obtain ⟨⟨M, hM⟩, -⟩ := GlobalTheory.T.intersection_number_multilinear_symm K A (Fin A.dim) (Fintype.card_fin _)
  set D : ℤ := inter B (fun _ : Fin A.dim => c) with hD
  have hDpos : 0 < D := GlobalTheory.T.abelianVariety_topSelfIntersection_ample_pos K B c hamp (Fin A.dim) (by rw [Fintype.card_fin, hAB])
  obtain ⟨F, hFh, hFe⟩ := GlobalTheory.AV.AbVar.multilinear_quadratic_isHomogeneous' (Pic A.X.left) A.dim n M
    (fun i j => AbVar.lam c (f i).hom (f j).hom)
  refine ⟨MvPolynomial.C ((1 : ℚ) / ((2 : ℚ) ^ A.dim * D)) * MvPolynomial.map (Int.castRingHom ℚ) F, ?_, ?_⟩
  · have := (MvPolynomial.isHomogeneous_C (Fin n) ((1 : ℚ) / ((2 : ℚ) ^ A.dim * D))).mul (hFh.map (Int.castRingHom ℚ))
    rwa [zero_add] at this
  · intro m
    have hq := GlobalTheory.T.two_smul_pullback_symmetric_class_integral_combination K A B c hsym n f m
    have hp := GlobalTheory.T.intersection_pullback_eq_degree_mul_intersection K A B (show A ⟶ B from ∑ i, m i • f i) hAB (Fin A.dim) (Fintype.card_fin _) (fun _ => c)
    have key : MvPolynomial.eval m F = 2 ^ A.dim * ((deg (show A ⟶ B from ∑ i, m i • f i) : ℤ) * D) := by
      rw [hFe m, ← hq, ← hp, ← hM]
      simpa only [RingHom.id_apply, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        smul_eq_mul, two_smul ℕ, two_smul ℤ] using
        M.map_smul_univ (fun _ => (2 : ℤ))
          (fun _ => CechPic.pull (Hom.hom (show A ⟶ B from ∑ i, m i • f i)).left c)
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_map]
    have e2 : MvPolynomial.eval₂ (Int.castRingHom ℚ) (fun i => (m i : ℚ)) F = ((MvPolynomial.eval m F : ℤ) : ℚ) := by
      rw [MvPolynomial.eval, MvPolynomial.coe_eval₂Hom, ← eq_intCast (Int.castRingHom ℚ), MvPolynomial.eval₂_comp_left]
      rfl
    rw [e2, key]
    have hD0 : (D : ℚ) ≠ 0 := by exact_mod_cast hDpos.ne'
    push_cast
    field_simp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomDegreeIntegerCombinationIsHomogeneousStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homDegree_integerCombination_isHomogeneous : ∀ (K : Type) [Field K] (A B : AbVar K), A.dim = B.dim → ∀ (n : ℕ) (f : Fin n → (A ⟶ B)), ∃ F : MvPolynomial (Fin n) ℚ, F.IsHomogeneous (2 * A.dim) ∧ ∀ m : Fin n → ℤ, MvPolynomial.eval (fun i => (m i : ℚ)) F = (deg (∑ i, m i • f i) : ℚ) := by
  first | (exact @GlobalTheory.AV.AbVar.deg_isHomogeneousPoly) | (exact GlobalTheory.AV.AbVar.deg_isHomogeneousPoly) | (intros; apply GlobalTheory.AV.AbVar.deg_isHomogeneousPoly  <;> assumption)
end
