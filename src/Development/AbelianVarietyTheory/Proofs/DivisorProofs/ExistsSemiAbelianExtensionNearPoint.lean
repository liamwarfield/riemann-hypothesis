module

public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.KltOfSncCoefficients
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasExtOfSetup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemePullbackOfIsPullback

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendsToSemiAbelianAwayOfCharts
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierDivClosure
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

set_option autoImplicit false

namespace GlobalTheory.Desc.ExtDiv

open TopologicalSpace CartierDiv

theorem unitAt_map {Y V X : Scheme.{0}} [IsIntegral Y] [IsIntegral X] (i : V ⟶ Y) [IsOpenImmersion i]
    (φ : V ⟶ X) (θ : X.functionField →+* Y.functionField) (h : PFF i φ θ) (v : V)
    {u : X.functionField} (hu : UnitAt (φ v) u) : UnitAt (i v) (θ u) := by
  obtain ⟨l, h₁, h₂⟩ := h
  obtain ⟨a, ha, rfl⟩ := hu
  let sY := Y.presheaf.stalkSpecializes (genericPoint_specializes (i v))
  let sX := X.presheaf.stalkSpecializes (genericPoint_specializes (φ v))
  have e₁ : Spec.map (inv (i.stalkMap v) ≫ sY) ≫ V.fromSpecStalk v = l := by
    rw [← cancel_mono i, h₁, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk,
      ← Spec.map_comp_assoc, IsIso.hom_inv_id_assoc]
    exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk _
  let t : X.presheaf.stalk (genericPoint X) ⟶ Y.presheaf.stalk (genericPoint Y) := CommRingCat.ofHom θ
  have e₂ : φ.stalkMap v ≫ inv (i.stalkMap v) ≫ sY = sX ≫ t := by
    apply Spec.map_injective
    rw [← cancel_mono (X.fromSpecStalk (φ v)), Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc, e₁, h₂, Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    rfl
  refine ⟨(φ.stalkMap v ≫ inv (i.stalkMap v)).hom a, ha.map _, ?_⟩
  exact congrArg (fun f => CommRingCat.Hom.hom f a) e₂

variable {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]

theorem finite_mult (D : CartierDiv Y) (U : Set Y) [NoetherianSpace U] :
    {z | z ∈ U ∧ D.mult z ≠ 0}.Finite := by
  classical
  obtain ⟨S, hS, hc, hi, hU⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible
    (D.supp.isClosed.preimage (continuous_subtype_val (p := (· ∈ U))))
  refine (hS.image fun T => if h : IsIrreducible ((Subtype.val : U → Y) '' T) then h.genericPoint
    else genericPoint Y).subset fun z hz => ?_
  obtain ⟨T, hT, hzT⟩ := Set.mem_sUnion.1 (hU.le
    (show (⟨z, hz.1⟩ : U) ∈ Subtype.val ⁻¹' (D.supp : Set Y) from mem_supp_of_mult_ne_zero hz.2))
  have hi' : IsIrreducible ((Subtype.val : U → Y) '' T) :=
    (hi T hT).image _ continuous_subtype_val.continuousOn
  refine ⟨T, hT, ?_⟩
  simp only [dif_pos hi']
  have hg := hi'.isGenericPoint_genericPoint_closure
  have h₁ : z ≤ hi'.genericPoint := hg.specializes (subset_closure ⟨_, hzT, rfl⟩)
  have hsub : closure ((Subtype.val : U → Y) '' T) ⊆ D.supp :=
    closure_minimal (by rintro _ ⟨t, ht, rfl⟩; exact hU.ge (Set.mem_sUnion.2 ⟨T, hT, ht⟩))
      D.supp.isClosed
  have h₂ : hi'.genericPoint < genericPoint Y := by
    refine lt_of_le_not_ge (genericPoint_specializes _) fun e => ?_
    have e' : _ = genericPoint Y := (Specializes.antisymm e (genericPoint_specializes _)).eq
    exact D.genericPoint_notMem_supp (e' ▸ hsub hg.mem)
  by_contra hne
  have h₃ := Order.coheight_add_one_le (lt_of_le_not_ge h₁ fun e =>
    hne (Specializes.antisymm h₁ e).eq)
  have h₄ := Order.coheight_add_one_le h₂
  rw [coheight_eq_one_of_mult_ne_zero hz.2] at h₃
  have h₅ : (1 : ℕ∞) + 1 ≤ 1 := (add_le_add_left (le_add_self.trans h₄) 1).trans h₃
  exact absurd h₅ (by decide)

theorem locally_finite (O : Set Y) (c : Y → ℤ) (h0 : ∀ z, z ∉ O → c z = 0)
    (hc : ∀ z ∈ O, ∃ N : Set Y, IsOpen N ∧ z ∈ N ∧ ∃ E : CartierDiv Y, ∀ w ∈ N, c w = E.mult w)
    (y : Y) : ∃ W : Y.Opens, y ∈ W ∧ {z | z ∈ W ∧ c z ≠ 0}.Finite := by
  obtain ⟨_, ⟨U : Y.Opens, hU, rfl⟩, hy, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ y) isOpen_univ
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.1 (IsAffineOpen.isCompact hU)
  have : IsNoetherian U.toScheme := {}
  have : NoetherianSpace (U : Set Y) := inferInstanceAs (NoetherianSpace U.toScheme)
  choose! N hN hzN E hE using hc
  have hK : IsCompact ((Subtype.val : ↥(U : Set Y) → Y) '' ((Subtype.val : ↥(U : Set Y) → Y) ⁻¹' O)) :=
    (NoetherianSpace.isCompact _).image continuous_subtype_val
  have hKO : ∀ z ∈ ((Subtype.val : ↥(U : Set Y) → Y) '' ((Subtype.val : ↥(U : Set Y) → Y) ⁻¹' O)), z ∈ O := by
    rintro _ ⟨t, ht, rfl⟩; exact ht
  obtain ⟨t, ht, hcov⟩ := hK.elim_nhds_subcover N fun z hz =>
    (hN z (hKO z hz)).mem_nhds (hzN z (hKO z hz))
  refine ⟨U, hy, (t.finite_toSet.biUnion fun z _ => finite_mult (E z) (U : Set Y)).subset fun w hw => ?_⟩
  have hwO : w ∈ O := by_contra fun h => hw.2 (h0 w h)
  obtain ⟨z, hz, hwz⟩ := Set.mem_iUnion₂.1 (hcov ⟨⟨w, hw.1⟩, hwO, rfl⟩)
  exact Set.mem_iUnion₂.2 ⟨z, hz, hw.1, hE z (hKO z (ht z hz)) w hwz ▸ hw.2⟩

theorem exists_mult_eq (hY : ∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)) (c : Y → ℤ)
    (h1 : ∀ z, c z ≠ 0 → Order.coheight z = 1)
    (hf : ∀ y, ∃ W : Y.Opens, y ∈ W ∧ {z | z ∈ W ∧ c z ≠ 0}.Finite) :
    ∃ D : CartierDiv Y, ∀ z, D.mult z = c z := by
  classical
  have : GlobalTheory.IsNormalScheme Y := ⟨fun x => inferInstance, fun x => by have := hY x; infer_instance⟩
  choose W hW hfin using hf
  have hE : ∀ y, ∃ E : CartierDiv Y, ∀ z ∈ W y, E.mult z = c z := fun y => by
    obtain ⟨E, hE⟩ := exists_mult_eq_of_locallyFactorial Y hY (fun z => if z ∈ W y then c z else 0)
      ((hfin y).subset fun z hz => by
        by_cases h : z ∈ W y
        · exact ⟨h, by simpa [h] using hz⟩
        · simp [h] at hz)
      fun z hz => h1 z fun h => hz (by simp [h])
    exact ⟨E, fun z hz => by rw [hE z, if_pos hz]⟩
  choose E hE using hE
  let D : CartierDiv Y := show cartierGroup Y from ⟨fun y => (E y).germ y, fun y => by
    obtain ⟨U, hU, g, hg⟩ := (E y).exists_isEqn_nhds y
    refine ⟨U ⊓ W y, ⟨hU, hW y⟩, g, fun z hz =>
      (MultEff.eff_supp_eq_of_mult Y (E z)).2.2.2 z g fun w hw => ?_⟩
    rw [hE z w (hw.mem_open (W z).isOpen (hW z)), ← hE y w (hw.mem_open (W y).isOpen hz.2),
      (hg w (hw.mem_open U.isOpen hz.1)).mult_eq]⟩
  refine ⟨D, fun z => ?_⟩
  obtain ⟨g, hg⟩ := (E z).exists_isEqn z
  rw [(show D.IsEqn z g from hg).mult_eq, ← hg.mult_eq, hE z z (hW z)]

end GlobalTheory.Desc.ExtDiv


open GlobalTheory.Desc.ExtDiv CartierDiv in
theorem GlobalTheory.Desc.exists_cartierDiv_closure : ∀ (Y V X : Scheme.{0}) [IsIntegral Y] [IsIntegral X] [IsLocallyNoetherian Y], (∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)) → ∀ (i : V ⟶ Y) [IsOpenImmersion i] (φ : V ⟶ X) (θ : X.functionField →+* Y.functionField), Flat φ → PFF i φ θ → ∀ D : CartierDiv X, ∃ D₁ : CartierDiv Y, PPull i φ θ D D₁ ∧ ∀ y : Y, y ∉ Set.range i → ringKrullDim (Y.presheaf.stalk y) = 1 → D₁.IsEqn y 1 := by
  intro Y V X _ _ _ hY i _ φ θ _ hθ D
  classical
  have : GlobalTheory.IsNormalScheme Y := ⟨fun x => inferInstance, fun x => by have := hY x; infer_instance⟩
  choose e he using fun v : V => D.exists_isEqn (φ v)
  let c : Y → ℤ := fun z => if h : z ∈ Set.range i then Scheme.ord (θ (e h.choose)) z else 0
  have h0 : ∀ z, z ∉ Set.range i → c z = 0 := fun z hz => dif_neg hz
  have h1 : ∀ z, c z ≠ 0 → Order.coheight z = 1 := fun z hz => by
    by_contra h
    apply hz
    simp only [c]
    split_ifs
    · exact Scheme.ord_eq_zero_of_coheight_neq_one h _
    · rfl
  have hc : ∀ v (g : X.functionFieldˣ), D.IsEqn (φ v) g → c (i v) = Scheme.ord (θ g) (i v) := by
    intro v g hg
    have hv : i v ∈ Set.range i := ⟨v, rfl⟩
    have e₀ : hv.choose = v := i.isOpenEmbedding.injective hv.choose_spec
    have hu := (unitAt_map i φ θ hθ v (hg.iff_unitAt.1 (he v))).ord_eq_zero
    simp only [c, dif_pos hv, e₀]
    rw [← div_mul_cancel₀ (e v : X.functionField) g.ne_zero, map_mul,
      Scheme.ord_mul ((map_ne_zero θ).2 (div_ne_zero (e v).ne_zero g.ne_zero))
        ((map_ne_zero θ).2 g.ne_zero), hu, zero_add]
  obtain ⟨D₁, hD₁⟩ := exists_mult_eq hY c h1 (locally_finite (Set.range i) c h0 (by
    rintro _ ⟨v, rfl⟩
    obtain ⟨U, hU, g, hg⟩ := D.exists_isEqn_nhds (φ v)
    refine ⟨i '' (φ ⁻¹ᵁ U), i.isOpenEmbedding.isOpenMap _ (φ ⁻¹ᵁ U).isOpen, ⟨v, hU, rfl⟩,
      principal (Units.map θ.toMonoidHom g), ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    rw [hc w g (hg _ hw), (isEqn_principal _ _).mult_eq]
    rfl))
  refine ⟨D₁, fun v g hg => (MultEff.eff_supp_eq_of_mult Y D₁).2.2.2 _ _ fun w hw => ?_,
    fun y hy hd => (MultEff.eff_supp_eq_of_mult Y D₁).2.2.2 _ _ fun w hw => ?_⟩
  · obtain ⟨w, rfl⟩ : w ∈ Set.range i := hw.mem_open i.isOpenEmbedding.isOpen_range ⟨v, rfl⟩
    obtain ⟨U, hU, hgU⟩ := hg.exists_nhds
    have hwv := (i.isOpenEmbedding.isInducing.specializes_iff.1 hw).map φ.continuous
    rw [hD₁, hc w g (hgU _ (hwv.mem_open U.isOpen hU))]
    rfl
  · rw [hD₁, Units.val_one, MultEff.ord_one]
    by_contra hne
    have hw1 := h1 w (Ne.symm hne)
    have hy1 : Order.coheight y = 1 := by
      rw [ringKrullDim_stalk_eq_coheight] at hd
      exact_mod_cast hd
    have hlt : y < w := lt_of_le_not_ge hw fun e =>
      hne ((Specializes.antisymm hw e).eq ▸ (h0 y hy).symm)
    have h₃ := Order.coheight_add_one_le hlt
    rw [hw1, hy1] at h₃
    exact absurd h₃ (by decide)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleDivSymm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullInvSymmIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SymLB

theorem pull_inv_symm_iso : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left), L.IsLB → LBIso ((LB.LinComb L (K := Fin 2) ![𝟙 G.left, (GrpObj.inv : G ⟶ G).left] ![1, 1]).pull (GrpObj.inv : G ⟶ G).left) (LB.LinComb L (K := Fin 2) ![𝟙 G.left, (GrpObj.inv : G ⟶ G).left] ![1, 1]) := by
  intro S G _ L hL
  have h₁ := LB.isLB_linComb hL (K := Fin 2) ![𝟙 G.left, (GrpObj.inv : G ⟶ G).left] ![1, 1]
  refine (GlobalTheory.CechPic.cls_eq_iff (pull_isLB h₁ _) h₁).1 ?_
  rw [GlobalTheory.CechPic.cls_pull h₁, GlobalTheory.CechPic.cls_linComb hL _ _ h₁]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, one_smul, map_add (f := _),
    ← GlobalTheory.CechPic.pull_comp]
  rw [← Over.comp_left, GrpObj.inv_comp_inv, Over.id_left, Category.comp_id, add_comm]

end GlobalTheory.SymLB
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.SymDiv

theorem exists_ampleDiv_symm : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsIntegral A.left], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → RelAmple A L → ∃ D : CartierDiv A.left, AmpleDiv D ∧ LBIso ((toLB D).pull (GrpObj.inv : A ⟶ A).left) (toLB D) := by
  intro R _ A _ _ hA L hL hamp
  classical
  have hprop : IsProper A.hom := hA.proper
  set σ := (GrpObj.inv : A ⟶ A).left with hσ
  have hii : (GrpObj.inv : A ⟶ A) ≫ (GrpObj.inv : A ⟶ A) = 𝟙 A := by
    have h := IsIso.hom_inv_id (GrpObj.inv : A ⟶ A)
    rwa [GrpObj.inv_inv] at h
  have hii' : σ ≫ σ = 𝟙 A.left := by
    rw [hσ, ← Over.comp_left, hii, Over.id_left]
  have : IsIso σ := ⟨⟨σ, hii', hii'⟩⟩
  set L' := LB.LinComb L (K := Fin 2) ![𝟙 A.left, σ] ![1, 1] with hL'def
  have hL' : L'.IsLB := LB.isLB_linComb hL (K := Fin 2) ![𝟙 A.left, σ] ![1, 1]
  have hamL : IsAmpleLB L := (relAmple_iff_isAmpleLB_of_isAffine A hL).1 hamp
  have hamσ : IsAmpleLB (L.pull σ) := hamL.pull_of_isAffineHom σ
  have hamL' : IsAmpleLB L' := by
    refine hamL.tensor hamσ hL' ?_
    have hM := pull_isLB hL σ
    have hD1 := LB.isLB_div hL' hL
    have hD2 := LB.isLB_div hD1 hM
    refine (CechPic.cls_eq_zero_iff hD2).1 ?_
    rw [CechPic.cls_div hD1 hM, CechPic.cls_div hL' hL, CechPic.cls_linComb hL _ _ hL', CechPic.cls_pull hL σ hM]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, one_zsmul,
      CechPic.pull_id]
    abel
  have : CompactSpace A.left := hamL'.compactSpace
  obtain ⟨i₀, h₀⟩ := exists_chart hL' (genericPoint A.left)
  refine ⟨ofLB hL' i₀ h₀, ?_, ?_⟩
  · have e : LBIso L' (toLB (ofLB hL' i₀ h₀)) := (presents_ofLB hL' i₀ h₀).lbIso (presents_toLB _)
    have hT := isLB_toLB (ofLB hL' i₀ h₀)
    exact (ampleDiv_iff_isAmpleLB _ _).2 (hamL'.of_lbIso hT e.symm)
  · have e : LBIso L' (toLB (ofLB hL' i₀ h₀)) := (presents_ofLB hL' i₀ h₀).lbIso (presents_toLB _)
    have hT := isLB_toLB (ofLB hL' i₀ h₀)
    have hs : LBIso (L'.pull σ) L' := GlobalTheory.SymLB.pull_inv_symm_iso _ A L hL
    have e₁ : LBIso ((toLB (ofLB hL' i₀ h₀)).pull σ) (L'.pull σ) := GlobalTheory.FamRep.lbIso_pull e.symm σ
    exact LBIso.trans (pull_isLB hT σ) hL' hT (LBIso.trans (pull_isLB hT σ) (pull_isLB hL' σ) hL' e₁ hs) e

end GlobalTheory.SymDiv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoPreimageBasicOpen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc.ChartPart

theorem flat_preimage_of_stalk {R Rc : Type} [CommRing R] [CommRing Rc] [IsLocalRing Rc] (ξ : Sp Rc ⟶ Sp R)
    (h : (Scheme.stalkClosedPointTo ξ).hom.Flat) : (Spec.preimage ξ).hom.Flat := by
  have h1 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of Rc) ξ
  have h2 : Flat (Spec.map (Scheme.stalkClosedPointTo ξ)) := HasRingHomProperty.Spec_iff.mpr h
  have h3 : Flat ξ := by
    rw [← h1]
    exact MorphismProperty.comp_mem @Flat _ _ h2 (GlobalTheory.LocalRingGeneralisation.flat_fromSpecStalk _ _)
  rw [← Spec.map_preimage ξ] at h3
  exact HasRingHomProperty.Spec_iff.mp h3

theorem injective_of_flat {R Rc : Type} [CommRing R] [IsDomain R] [CommRing Rc] [Nontrivial Rc] (ρ : R →+* Rc)
    (h : ρ.Flat) : Function.Injective ρ := by
  algebraize [ρ]
  exact FaithfulSMul.algebraMap_injective R Rc

theorem isPullback_away {R Rc : Type} [CommRing R] [CommRing Rc] (ρ : R →+* Rc) (f : R) :
    IsPullback (spMap (Localization.awayMap ρ f)) (spMap (algebraMap Rc (Localization.Away (ρ f)))) (awayMap f)
      (spMap ρ) := by
  refine (IsOpenImmersion.isPullback _ _ _ _ ?_ ?_)
  · rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext r
    simp [Localization.awayMap, IsLocalization.Away.map]
  · rw [Scheme.Hom.opensRange_localizationAway (R := .of R), Scheme.Hom.opensRange_localizationAway (R := .of Rc)]
    rfl

theorem exists_iso_preimage_basicOpen {Rc : Type} [CommRing Rc] (G : Over (Sp Rc)) (r : Rc) :
    ∃ e : (G.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r).toScheme ≅
      pullback G.hom (spMap (algebraMap Rc (Localization.Away r))),
      e.hom ≫ pullback.fst _ _ = (G.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι := by
  refine ⟨IsOpenImmersion.isoOfRangeEq _ (pullback.fst _ _) ?_, IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _⟩
  rw [IsOpenImmersion.range_pullbackFst, Scheme.Hom.opensRange_localizationAway (R := .of Rc)]
  simp

theorem exists_pff_of_flat {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (V : Y.Opens) (hV : (V : Set Y).Nonempty)
    (φ : V.toScheme ⟶ X) [Flat φ] : ∃ θ : X.functionField →+* Y.functionField, PFF V.ι φ θ := by
  have hη : genericPoint Y ∈ V := ((genericPoint_spec Y).mem_open_set_iff V.isOpen).2 (by simpa using hV)
  have hrange : Set.range (gp Y) ⊆ Set.range V.ι := by
    rw [gp, Scheme.range_fromSpecStalk, Scheme.Opens.range_ι]
    exact fun y hy => hy.mem_open V.isOpen hη
  let l := IsOpenImmersion.lift V.ι (gp Y) hrange
  have hl : l ≫ V.ι = gp Y := IsOpenImmersion.lift_fac _ _ _
  have hl0 : V.ι (l (closedPoint Y.functionField)) = genericPoint Y := by
    have : (l ≫ V.ι) (closedPoint Y.functionField) = genericPoint Y := by
      rw [hl]; exact Scheme.fromSpecStalk_closedPoint
    exact this
  have hx : (l ≫ φ) (closedPoint Y.functionField) = genericPoint X := by
    obtain ⟨v, hv, hφv⟩ := Flat.generalizingMap φ
      (genericPoint_specializes (φ (l (closedPoint Y.functionField))))
    have h1 : V.ι v ⤳ genericPoint Y := hl0 ▸ hv.map V.ι.continuous
    have h2 : V.ι v = genericPoint Y := (h1.antisymm (genericPoint_specializes _)).eq
    have h3 : v = l (closedPoint Y.functionField) := V.ι.isOpenEmbedding.injective (h2.trans hl0.symm)
    subst h3
    exact hφv
  have hφ := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := Y.functionField) (l ≫ φ)
  revert hφ
  generalize Scheme.stalkClosedPointTo (R := Y.functionField) (l ≫ φ) = ψ
  revert ψ
  rw [show (l ≫ φ) (closedPoint Y.functionField) = genericPoint X from hx]
  intro ψ hψ
  exact ⟨ψ.hom, l, hl, hψ.symm⟩

end GlobalTheory.Desc.ChartPart

namespace GlobalTheory.Desc


open GlobalTheory.Desc.ChartPart in
theorem chart_part : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (f : R), f ≠ 0 → ∀ (A : Over (Sp (Localization.Away f))) [GrpObj A], IsAbelianScheme A → ∀ [IsIntegral A.left] (x : Sp R) (C : Chart (awayMap f) A x) [IsIntegral C.G.left], ∃ (ρ : R →+* C.R) (V : C.G.left.Opens) (φ : V.toScheme ⟶ A.left) (θ : A.left.functionField →+* C.G.left.functionField), C.ξ = spMap ρ ∧ ρ.Flat ∧ (∀ z : C.G.left, z ∈ V ↔ ρ f ∉ (C.G.hom z).asIdeal) ∧ IsPullback φ (V.ι ≫ C.G.hom) (A.hom ≫ awayMap f) (spMap ρ) ∧ (∀ (T : Scheme.{0}) (t : T ⟶ pullback C.G.hom (jK C.R)) (t' : T ⟶ V.toScheme), t ≫ pullback.fst _ _ = t' ≫ V.ι → t ≫ C.α = t' ≫ φ) ∧ PFF V.ι φ θ := by
  intro R _ _ _ f hf0 A _ hAb _ x C _
  set ρ : R →+* C.R := (Spec.preimage C.ξ).hom with hρdef
  have hξ : C.ξ = spMap ρ := by
    rw [hρdef]; exact (Spec.map_preimage C.ξ).symm
  have hflat : ρ.Flat := flat_preimage_of_stalk C.ξ C.etc.1
  have hρf : ρ f ≠ 0 := fun h => hf0 (injective_of_flat ρ hflat (h.trans (map_zero ρ).symm))
  obtain ⟨_, hnorm⟩ := GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing C.R

  let Rf := Localization.Away (ρ f)
  have hle : Submonoid.powers (ρ f) ≤ nonZeroDivisors C.R := powers_le_nonZeroDivisors_of_noZeroDivisors hρf
  haveI : IsDomain Rf := IsLocalization.isDomain_localization hle
  haveI : IsNoetherianRing Rf := IsLocalization.isNoetherianRing (Submonoid.powers (ρ f)) Rf inferInstance
  haveI : IsIntegrallyClosed Rf := isIntegrallyClosed_of_isLocalization Rf _ hle
  let ιf : C.R →+* Rf := algebraMap C.R Rf
  let g : Sp Rf ⟶ Sp (Localization.Away f) := spMap (Localization.awayMap ρ f)
  have sq2 := isPullback_away ρ f

  let K := FractionRing C.R
  have hu : IsUnit (algebraMap C.R K (ρ f)) :=
    IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective C.R K)).mpr hρf)
  letI : Algebra Rf K := (Localization.awayLift (algebraMap C.R K) (ρ f) hu).toAlgebra
  haveI : IsScalarTower C.R Rf K := IsScalarTower.of_algebraMap_eq fun r => by
    show algebraMap C.R K r = Localization.awayLift (algebraMap C.R K) (ρ f) hu (algebraMap C.R Rf r)
    exact (IsLocalization.Away.lift_eq (ρ f) hu r).symm
  haveI : IsFractionRing Rf K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers (ρ f)) Rf K
  let j : Sp K ⟶ Sp Rf := spMap (algebraMap Rf K)
  have hjK : j ≫ spMap ιf = jK C.R := by
    simp only [j, spMap, ← Spec.map_comp]; congr 1; ext r
    exact (IsScalarTower.algebraMap_apply C.R Rf K r).symm
  have hy' : j ≫ g = C.y := by
    rw [← cancel_mono (awayMap f), Category.assoc, sq2.w, ← Category.assoc, hjK, C.hy, hξ]

  let GK := (Over.pullback (jK C.R)).obj C.G
  letI : GrpObj GK := Functor.grpObjObj
  let G₁ := (Over.pullback (spMap ιf)).obj C.G
  letI : GrpObj G₁ := Functor.grpObjObj
  have hG₁ : IsSemiAbelian G₁ := IsSemiAbelian.pullback (spMap ιf) C.G C.semi
  let H₁ := (Over.pullback g).obj A
  letI : GrpObj H₁ := Functor.grpObjObj
  have hH₁ : IsSemiAbelian H₁ :=
    IsSemiAbelian.pullback g A (isSemiAbelian_of_isAbelianScheme A hAb)
  let i₁ : GK.left ⟶ G₁.left := pullback.lift (pullback.fst C.G.hom (jK C.R)) (pullback.snd _ _ ≫ j)
    (by rw [Category.assoc, hjK]; exact pullback.condition)
  have h₁ : IsGrpPullback GK G₁ j i₁ := by
    refine IsGrpPullback.cancel (isGrpPullback_pullback C.G (spMap ιf)) ?_ (pullback.lift_snd _ _ _)
    exact (isGrpPullback_pullback C.G (jK C.R)).congr hjK.symm (pullback.lift_fst _ _ _).symm
  let i₂ : GK.left ⟶ H₁.left := pullback.lift C.α (pullback.snd _ _ ≫ j)
    (by rw [Category.assoc, hy']; exact C.gen.1.w)
  have h₂ : IsGrpPullback GK H₁ j i₂ := by
    refine IsGrpPullback.cancel (isGrpPullback_pullback A g) ?_ (pullback.lift_snd _ _ _)
    exact C.gen.congr hy'.symm (pullback.lift_fst _ _ _).symm
  obtain ⟨E, ⟨hEm, hE⟩, -⟩ := semiAbelianHomExtension_holds.generic_existsUnique_iso_of_extensions
    (GlobalTheory.IsNormalScheme.pred _) (IsGenericPointHom.fractionField Rf K) hG₁ hH₁ h₁ h₂

  haveI : IsMonHom E.hom := hEm
  let φ₁ : G₁.left ⟶ A.left := E.hom.left ≫ pullback.fst A.hom g
  have sq1 : IsPullback φ₁ G₁.hom A.hom g :=
    (((isGrpPullback_of_iso E).comp (isGrpPullback_pullback A g)).congr (Category.id_comp g) rfl).1

  let V : C.G.left.Opens := C.G.hom ⁻¹ᵁ PrimeSpectrum.basicOpen (ρ f)
  obtain ⟨e, he⟩ := exists_iso_preimage_basicOpen C.G (ρ f)
  let φ : V.toScheme ⟶ A.left := e.hom ≫ φ₁
  have sq0 : IsPullback e.hom (V.ι ≫ C.G.hom) (G₁.hom ≫ spMap ιf) (𝟙 _) := by
    refine IsPullback.of_horiz_isIso ⟨?_⟩
    show e.hom ≫ pullback.snd _ _ ≫ spMap ιf = (V.ι ≫ C.G.hom) ≫ 𝟙 _
    rw [Category.comp_id, ← pullback.condition, ← Category.assoc, he]
  have hcart : IsPullback φ (V.ι ≫ C.G.hom) (A.hom ≫ awayMap f) (spMap ρ) := by
    have := sq0.paste_horiz (sq1.paste_vert sq2)
    rwa [Category.id_comp] at this
  haveI : Flat (spMap ρ) := HasRingHomProperty.Spec_iff.mpr hflat
  haveI : Flat φ := MorphismProperty.of_isPullback hcart.flip inferInstance

  have hVne : (V : Set C.G.left).Nonempty := by
    let s : Sp C.R ⟶ C.G.left := (η[C.G] : 𝟙_ (Over (Sp C.R)) ⟶ C.G).left
    have hs : s ≫ C.G.hom = 𝟙 _ := Over.w η[C.G]
    let p : Sp C.R := (⊥ : PrimeSpectrum C.R)
    refine ⟨s p, ?_⟩
    show ρ f ∉ (C.G.hom (s p)).asIdeal
    rw [← Scheme.Hom.comp_apply, hs]
    exact fun h => hρf (Ideal.mem_bot.1 h)
  obtain ⟨θ, hθ⟩ := exists_pff_of_flat V hVne φ
  refine ⟨ρ, V, φ, θ, hξ, hflat, fun z => Iff.rfl, hcart, ?_, hθ⟩
  intro T t t' htt'
  have key : t ≫ i₁ = t' ≫ e.hom := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, htt', Category.assoc, he]
    · rw [← cancel_mono (spMap ιf)]
      have l : t ≫ i₁ ≫ pullback.snd _ _ ≫ spMap ιf = t ≫ pullback.fst _ _ ≫ C.G.hom := by
        simp only [i₁, pullback.lift_snd_assoc, Category.assoc, hjK]; rw [pullback.condition]
      have r : t' ≫ e.hom ≫ pullback.snd _ _ ≫ spMap ιf = t' ≫ V.ι ≫ C.G.hom := by
        rw [← pullback.condition, ← Category.assoc e.hom, he]
      simp only [Category.assoc]
      rw [l, r, ← Category.assoc t, htt', Category.assoc]
  have : t ≫ C.α = t ≫ i₂ ≫ pullback.fst A.hom g := by rw [pullback.lift_fst]
  rw [this, ← hE, Category.assoc, ← Category.assoc t, key, Category.assoc]

end GlobalTheory.Desc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendsToSemiAbelianAwayOfCharts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem ufm_stalk_of_smooth_regularLocal {E : Type} [CommRing E] [IsRegularLocalRing E] {Y : Scheme.{0}} [IsIntegral Y]
    (p : Y ⟶ Sp E) [Smooth p] (y : Y) : UniqueFactorizationMonoid (Y.presheaf.stalk y) := by
  have : IsRegularRing E := GlobalTheory.isRegularRing_of_isRegularLocalRing E
  have := ExtendRig.isRegularRing_stalk isRegularRing_of_smooth E p y
  exact uniqueFactorizationMonoid_of_isRegularRing_of_isLocalRing exists_hasProjectiveDimensionLE_of_isRegularLocalRing
    isPrincipal_map_away_of_hasProjectiveDimensionLE _

theorem hasExt_awayMap_of_charts : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (f : R), f ≠ 0 → ∀ (A : Over (Sp (Localization.Away f))) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → RelAmple A L → (∀ x : Sp R, Nonempty (Chart (awayMap f) A x)) → HasExt (awayMap f) A := by
  intro R _ _ _ _ f hf A _ hA L hL hamp hC
  have : IsDomain (Localization.Away f) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hf)
  have : IsIntegral A.left := isIntegral_left_of_isAbelianScheme A
  obtain ⟨D, hD, hsym⟩ := GlobalTheory.SymDiv.exists_ampleDiv_symm _ A hA L hL hamp
  let C : ∀ x : Sp R, Chart (awayMap f) A x := fun x => (hC x).some
  have intC : ∀ x, IsIntegral (C x).G.left := fun x =>
    have := (C x).semi
    isIntegral_left_of_isSemiAbelian (C x).G
  choose ρ V φ θ hρ hflat hV hcart hcompat hθ using fun x => chart_part R f hf A hA x (C x)
  have hdiv : ∀ x, ∃ D₁ : CartierDiv (C x).G.left, PPull (V x).ι (φ x) (θ x) D D₁ ∧
      ∀ z, Vert (C x).G.hom (ρ x f) z → D₁.IsEqn z 1 := fun x => by
    have := (C x).semi.smooth
    have : IsLocallyNoetherian (C x).G.left := LocallyOfFiniteType.isLocallyNoetherian (C x).G.hom
    have hρf : Flat (spMap (ρ x)) := by
      rw [HasRingHomProperty.Spec_iff (P := @Flat)]
      exact hflat x
    have hφ : Flat (φ x) := MorphismProperty.of_isPullback (hcart x).flip hρf
    obtain ⟨D₁, h₁, h₂⟩ := exists_cartierDiv_closure (C x).G.left (V x).toScheme A.left
      (ufm_stalk_of_smooth_regularLocal (C x).G.hom) (V x).ι (φ x) (θ x) hφ (hθ x) D
    refine ⟨D₁, h₁, fun z hz => h₂ z ?_ hz.1⟩
    rw [Scheme.Opens.range_ι]
    exact fun hzV => (hV x z).1 hzV hz.2
  choose D₁ hpull hvert using hdiv
  have hamp₁ : ∀ x, AmpleDiv (D₁ x) := fun x => by
    have := (C x).charZero
    have hne : ρ x f ≠ 0 := fun h0 => by
      obtain ⟨l, -⟩ := hθ x
      let v : (V x).toScheme := l (closedPoint _)
      refine (hV x v.1).1 v.2 ?_
      rw [h0]
      exact zero_mem _
    exact ampleDiv_closure_on_chart R f A hA D hD hsym (C x).R (C x).complete (ρ x) (hflat x) hne (C x).G (C x).semi (V x) (φ x) (θ x)
      (D₁ x) (hV x) (hcart x) (C x).y (C x).α (C x).gen (hcompat x) (hθ x) (hpull x)
  exact hasExt_of_setup
    { R := R, f := f, hf := hf, A := A, ab := hA, D := D, amp := hD, C := C, ρ := ρ, hρ := hρ, flat := hflat, V := V,
      hV := hV, φ := φ, cart := hcart, compat := hcompat, θ := θ, hθ := hθ, D₁ := D₁, pull := hpull, noVert := hvert,
      amp₁ := hamp₁ }

end GlobalTheory.Desc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendsToSemiAbelianAwayOfChartsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extendsToSemiAbelian_away_of_charts : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (f : R), f ≠ 0 → ∀ (A : Over (Sp (Localization.Away f))) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → RelAmple A L → (∀ x : Sp R, Nonempty (Chart (awayMap f) A x)) → HasExt (awayMap f) A := by
  first | exact @GlobalTheory.Desc.hasExt_awayMap_of_charts | exact GlobalTheory.Desc.hasExt_awayMap_of_charts | (intros; apply GlobalTheory.Desc.hasExt_awayMap_of_charts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianExtensionNearPoint
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem HasExt.of_comp {W V T : Scheme.{0}} (g : W ⟶ V) (e : V ⟶ T) (B : Over W) [GrpObj B] (h : HasExt (g ≫ e) B) :
    HasExt g B := by
  obtain ⟨G, _, φ, hG, hφ⟩ := h
  exact ⟨(Over.pullback e).obj G, inferInstance, _, IsSemiAbelian.pullback _ _ hG,
    ReciprocityTheory.ChartRestriction.G.Chart.isGrpPullback_factor e g hφ⟩

theorem HasExt.of_dense {W V U : Scheme.{0}} [AlgebraicGeometry.IsNoetherian V]
    (hV : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme V) (l : W ⟶ V) [IsOpenImmersion l] [IsDominant l] (j : V ⟶ U)
    (A : Over V) [GrpObj A] (hA : IsSemiAbelian A) (B : Over W) [GrpObj B] (κ : B.left ⟶ A.left)
    (hκ : IsGrpPullback B A l κ) (h : HasExt (l ≫ j) B) : HasExt j A := by
  obtain ⟨G, _, φ, hG, hφ⟩ := h
  have h2 := ReciprocityTheory.ChartRestriction.G.Chart.isGrpPullback_factor j l hφ
  obtain ⟨e, ⟨he, -⟩, -⟩ := GlobalTheory.semiAbelianHomExtension_holds.existsUnique_iso_of_extensions hV hA
    (IsSemiAbelian.pullback j G hG) hκ h2
  exact ⟨G, inferInstance, e.hom.left ≫ pullback.fst _ _, hG,
    ((isGrpPullback_of_iso e).comp (isGrpPullback_pullback G j)).congr (Category.id_comp _) rfl⟩

theorem etale_of_comp_bijective {B A R : Type} [CommRing B] [IsLocalRing B] [CommRing A] [IsLocalRing A]
    [CommRing R] [IsLocalRing R] (e : B →+* A) (he : Function.Bijective e) (φ : A →+* R)
    (h : IsEtaleCompletion (φ.comp e)) (h' : ((residue R).comp (φ.comp e)).FormallyUnramified) :
    IsEtaleCompletion φ ∧ ((residue R).comp φ).FormallyUnramified := by
  obtain ⟨h1, h2, h3⟩ := h
  let E := RingEquiv.ofBijective e he
  have hφ : φ = (φ.comp e).comp E.symm.toRingHom := by
    ext a
    exact congrArg φ (E.apply_symm_apply a).symm
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hφ]
    exact RingHom.Flat.comp (RingHom.Flat.of_bijective E.symm.bijective) h1
  · rw [← h2, ← Ideal.map_map, IsLocalRing.map_maximalIdeal_of_surjective e he.2]
  · exact RingHom.Finite.of_comp_finite (f := e) h3
  · exact RingHom.FormallyUnramified.of_comp (f := e) h'

theorem etale_of_comp_openImmersion {S S' : Scheme.{0}} (i : S' ⟶ S) [IsOpenImmersion i] {R : Type} [CommRing R]
    [IsLocalRing R] (ξ' : Sp R ⟶ S') (ξ : Sp R ⟶ S) (hξ : ξ' ≫ i = ξ)
    (h : IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom)
    (h' : ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified) :
    IsEtaleCompletion (Scheme.stalkClosedPointTo ξ').hom ∧
      ((residue R).comp (Scheme.stalkClosedPointTo ξ').hom).FormallyUnramified := by
  subst hξ
  have hiso : IsIso (i.stalkMap (ξ' (IsLocalRing.closedPoint (CommRingCat.of R)))) :=
    (IsOpenImmersion.iff_isIso_stalkMap.1 inferInstance).2 _
  have hb : Function.Bijective (i.stalkMap (ξ' (IsLocalRing.closedPoint (CommRingCat.of R)))).hom :=
    ConcreteCategory.bijective_of_isIso _
  rw [Scheme.stalkClosedPointTo_comp] at h h'
  exact etale_of_comp_bijective _ hb _ h h'

theorem generic_mem_of_flat {S : Scheme.{0}} {R : Type} [CommRing R] [IsLocalRing R] [IsDomain R] (ξ : Sp R ⟶ S)
    (h : (Scheme.stalkClosedPointTo ξ).hom.Flat) (U : S.Opens) (t : S) (ht : t ∈ U) (hs : t ⤳ ξ (closedPoint R))
    (z : Sp (FractionRing R)) : (jK R ≫ ξ) z ∈ U := by
  have hfl : Flat ξ := by
    rw [← Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of R) ξ]
    have : Flat (Spec.map (Scheme.stalkClosedPointTo ξ)) := (HasRingHomProperty.Spec_iff (P := @Flat)).2 h
    exact MorphismProperty.comp_mem @Flat _ _ this (GlobalTheory.LocalRingGeneralisation.flat_fromSpecStalk _ _)
  obtain ⟨p, -, hp⟩ := Flat.generalizingMap ξ hs
  have hz : jK R z ⤳ p := by
    refine (PrimeSpectrum.le_iff_specializes _ _).1 fun a ha => ?_
    have ha' : algebraMap R (FractionRing R) a ∈ z.asIdeal := ha
    have := z.isPrime
    rw [Ideal.eq_bot_of_prime z.asIdeal, Ideal.mem_bot, map_eq_zero_iff _ (IsFractionRing.injective R _)] at ha'
    rw [ha']
    exact zero_mem _
  exact (hz.map ξ.continuous).mem_open U.isOpen (by rw [hp]; exact ht)

theorem Chart.nonempty_restrict {X S X' S' : Scheme.{0}} [IrreducibleSpace S'] [Nonempty X'] (j : X ⟶ S) [Mono j]
    (j' : X' ⟶ S') [IsOpenImmersion j'] (i : S' ⟶ S) [IsOpenImmersion i] (k : X' ⟶ X) (w : k ≫ j = j' ≫ i)
    (A : Over X) [GrpObj A] (x : S') (C : Chart j A (i x)) : Nonempty (Chart j' ((Over.pullback k).obj A) x) := by
  have h1 : Set.range C.ξ ⊆ Set.range i := by
    rintro _ ⟨y, rfl⟩
    exact (Scheme.preimage_eq_top_of_closedPoint_mem (R := .of C.R) C.ξ (U := i.opensRange)
      ⟨x, C.centre.symm⟩).ge (Set.mem_univ y)
  let ξ' : Sp C.R ⟶ S' := IsOpenImmersion.lift i C.ξ h1
  have hξ : ξ' ≫ i = C.ξ := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨he, hu⟩ := etale_of_comp_openImmersion i ξ' C.ξ hξ C.etc C.unr
  have hg : genericPoint S' ∈ j'.opensRange :=
    ((genericPoint_spec S').mem_open_set_iff j'.opensRange.isOpen).2 (by
      rw [Set.univ_inter]; exact Set.range_nonempty _)
  have h2 : Set.range (jK C.R ≫ ξ') ⊆ Set.range j' := by
    rintro _ ⟨z, rfl⟩
    exact generic_mem_of_flat ξ' he.1 j'.opensRange _ hg (genericPoint_specializes _) z
  let y' : Sp (FractionRing C.R) ⟶ X' := IsOpenImmersion.lift j' (jK C.R ≫ ξ') h2
  have hy' : y' ≫ j' = jK C.R ≫ ξ' := IsOpenImmersion.lift_fac _ _ _
  have hk : C.y = y' ≫ k := by
    rw [← cancel_mono j, Category.assoc, w, ← Category.assoc, hy', Category.assoc, hξ, C.hy]
  refine ⟨{ R := C.R, complete := C.complete, charZero := C.charZero, ξ := ξ', centre := ?_, etc := he, unr := hu,
            G := C.G, semi := C.semi, y := y', hy := hy', α := _,
            gen := ReciprocityTheory.ChartRestriction.G.Chart.isGrpPullback_factor k y' (C.gen.congr hk rfl) }⟩
  apply i.isOpenEmbedding.injective
  exact (congrArg (fun q => q (closedPoint C.R)) hξ).trans C.centre

theorem hasExt_opensRange (X S : Scheme.{0}) [AlgebraicGeometry.IsNoetherian S]
    (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S) (j : X ⟶ S) [IsOpenImmersion j] [IsDominant j]
    (A : Over X) [GrpObj A] (hA : IsAbelianScheme A) (L : LB A.left) (hL : L.IsLB) (hamp : RelAmple A L)
    (hC : ∀ x : S, Nonempty (Chart j A x)) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] (i : Sp R ⟶ S) [IsOpenImmersion i] :
    HasExt (j ∣_ i.opensRange) ((Over.pullback (j ⁻¹ᵁ i.opensRange).ι).obj A) := by
  obtain ⟨x₀, p, hp⟩ := j.denseRange.exists_mem_open i.opensRange.isOpen (Set.range_nonempty i)
  obtain ⟨_, ⟨f : R, rfl⟩, hpf, hf⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (a := p) (u := (i ⁻¹ᵁ j.opensRange).1) ⟨x₀, hp.symm⟩ (i ⁻¹ᵁ j.opensRange).isOpen
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hpf (zero_mem _)
  have hrange : Set.range (awayMap f) = (PrimeSpectrum.basicOpen f).1 :=
    PrimeSpectrum.localization_away_comap_range (Localization.Away f) f
  have : IsOpenImmersion (awayMap f) := IsOpenImmersion.of_isLocalization f
  have hne : Nonempty (Sp (Localization.Away f)) := by
    obtain ⟨q, -⟩ : p ∈ Set.range (awayMap f) := hrange ▸ hpf
    exact ⟨q⟩
  have h1 : Set.range (awayMap f ≫ i) ⊆ Set.range j := by
    rintro _ ⟨z, rfl⟩
    exact hf (hrange.le (Set.mem_range_self z))
  let k : Sp (Localization.Away f) ⟶ X := IsOpenImmersion.lift j (awayMap f ≫ i) h1
  have hk : k ≫ j = awayMap f ≫ i := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion (k ≫ j) := by rw [hk]; infer_instance
  have : IsOpenImmersion k := IsOpenImmersion.of_comp k j
  have hL' := pull_isLB hL (pullback.fst A.hom k)
  obtain ⟨u, hu⟩ := GlobalTheory.lbIso_refl hL'
  have hext : HasExt (awayMap f) ((Over.pullback k).obj A) :=
    GlobalTheory.T.extendsToSemiAbelian_away_of_charts R f hf0 _ (isAbelianScheme_pullback_obj k A hA) (L.pull (pullback.fst A.hom k)) hL'
      (relAmple_pull (isGrpPullback_pullback A k).1 hL hL' ((isGen_iff u).1 hu) k.opensRange
        (isAffineOpen_opensRange k) (fun y => ⟨y, rfl⟩) hamp)
      fun x => (hC (i x)).elim fun C => Chart.nonempty_restrict j (awayMap f) i k hk A x C
  have h2 : Set.range k ⊆ Set.range (j ⁻¹ᵁ i.opensRange).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact ⟨awayMap f z, (congrArg (fun q => q z) hk).symm⟩
  let l : Sp (Localization.Away f) ⟶ (j ⁻¹ᵁ i.opensRange).toScheme := IsOpenImmersion.lift _ k h2
  have hl : l ≫ (j ⁻¹ᵁ i.opensRange).ι = k := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion (l ≫ (j ⁻¹ᵁ i.opensRange).ι) := by rw [hl]; infer_instance
  have : IsOpenImmersion l := IsOpenImmersion.of_comp l (j ⁻¹ᵁ i.opensRange).ι
  have hcomp : l ≫ (j ∣_ i.opensRange) ≫ i.isoOpensRange.inv = awayMap f := by
    rw [← cancel_mono i, Category.assoc, Category.assoc, i.isoOpensRange_inv_comp, morphismRestrict_ι, ← Category.assoc,
      hl, hk]
  have : IsDominant l := by
    have hd : Dense (Set.range (awayMap f)) :=
      (awayMap f).isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)
    have hg := ((j ∣_ i.opensRange) ≫ i.isoOpensRange.inv).isOpenEmbedding
    refine ⟨(hd.preimage hg.isOpenMap).mono ?_⟩
    rintro y ⟨z, hz⟩
    exact ⟨z, hg.injective ((congrArg (fun q => q z) hcomp).trans hz)⟩
  have := GlobalTheory.IsNormalScheme.of_pred hS
  have : IsLocallyNoetherian (j ⁻¹ᵁ i.opensRange).toScheme :=
    isLocallyNoetherian_of_isOpenImmersion ((j ⁻¹ᵁ i.opensRange).ι ≫ j)
  have : TopologicalSpace.NoetherianSpace (j ⁻¹ᵁ i.opensRange).toScheme :=
    ((j ⁻¹ᵁ i.opensRange).ι ≫ j).isOpenEmbedding.isInducing.noetherianSpace
  have : AlgebraicGeometry.IsNoetherian (j ⁻¹ᵁ i.opensRange).toScheme := {}
  have : GlobalTheory.IsNormalScheme (j ⁻¹ᵁ i.opensRange).toScheme :=
    GlobalTheory.IsNormalScheme.of_isOpenImmersion ((j ⁻¹ᵁ i.opensRange).ι ≫ j)
  refine HasExt.of_dense (GlobalTheory.IsNormalScheme.pred _) l _ _
    (isSemiAbelian_of_isAbelianScheme _ (isAbelianScheme_pullback_obj _ A hA)) ((Over.pullback k).obj A) _
    (ReciprocityTheory.ChartRestriction.G.Chart.isGrpPullback_factor _ l ((isGrpPullback_pullback A k).congr hl.symm rfl))
    (HasExt.of_comp _ i.isoOpensRange.inv _ ?_)
  rw [Category.assoc, hcomp]
  exact hext

theorem exists_hasExt_near : ∀ (X S : Scheme.{0}) [AlgebraicGeometry.IsNoetherian S], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S → ∀ (j : X ⟶ S) [IsOpenImmersion j], IsDominant j → ∀ (A : Over X) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → RelAmple A L → (∀ x : S, Nonempty (Chart j A x)) → ∀ s : S, ∃ U : S.Opens, s ∈ U ∧ HasExt (j ∣_ U) ((Over.pullback (j ⁻¹ᵁ U).ι).obj A) := by
  intro X S _ hS j _ hj A _ hA L hL hamp hC s
  have := GlobalTheory.IsNormalScheme.of_pred hS
  let Z : S.Opens := GlobalTheory.IsNormalScheme.component ⟨_, irreducibleComponent_mem_irreducibleComponents s⟩
  obtain ⟨U, hU, hs, hle⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := Z) (x := s) mem_irreducibleComponent
  have : IrreducibleSpace U.toScheme := Subtype.irreducibleSpace
    ⟨⟨s, hs⟩, isIrreducible_irreducibleComponent.2.open_subset U.isOpen hle⟩
  have : IsIntegral U.toScheme := GlobalTheory.IsNormalScheme.isIntegral_of_irreducibleSpace _
  have : IsIntegral (Spec Γ(S, U)) := IsIntegral.of_isIso hU.isoSpec.hom
  have : IsDomain Γ(S, U) := (affine_isIntegral_iff _).1 this
  have : IsNoetherianRing Γ(S, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : IsIntegrallyClosed Γ(S, U) := GlobalTheory.IsNormalScheme.isIntegrallyClosed_of_isAffineOpen hU
  let i : Sp Γ(S, U) ⟶ S := hU.fromSpec
  have : IsOpenImmersion i := inferInstanceAs (IsOpenImmersion hU.fromSpec)
  refine ⟨i.opensRange, ?_, hasExt_opensRange X S hS j A hA L hL hamp hC Γ(S, U) i⟩
  exact hU.range_fromSpec.ge hs

end GlobalTheory.Desc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianExtensionNearPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semiAbelianExtension_near_point : ∀ (X S : Scheme.{0}) [AlgebraicGeometry.IsNoetherian S], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S → ∀ (j : X ⟶ S) [IsOpenImmersion j], IsDominant j → ∀ (A : Over X) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → RelAmple A L → (∀ x : S, Nonempty (Chart j A x)) → ∀ s : S, ∃ U : S.Opens, s ∈ U ∧ HasExt (j ∣_ U) ((Over.pullback (j ⁻¹ᵁ U).ι).obj A) := by
  first | exact @GlobalTheory.Desc.exists_hasExt_near | exact GlobalTheory.Desc.exists_hasExt_near | (intros; apply GlobalTheory.Desc.exists_hasExt_near <;> assumption)
end
