module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CardTorsionTranslateZerosLt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSectionApplyEqOfIsAlgClosed
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

private lemma exists_retraction_of_flat_quasiFinite (V K : Type) [CommRing V] [IsDomain V]
    [ValuationRing V] [Field K] [IsAlgClosed K] [Algebra V K] [IsFractionRing V K] {B : Type}
    [CommRing B] (φ : V →+* B) (hflat : φ.Flat) (hqf : φ.QuasiFinite) (q : Ideal B) [q.IsPrime]
    (hq : q.comap φ = IsLocalRing.maximalIdeal V) :
    ∃ ψ : B →+* V, ψ.comp φ = RingHom.id V ∧ (IsLocalRing.maximalIdeal V).comap ψ = q := by
  letI : Algebra V B := φ.toAlgebra
  haveI : Module.Flat V B := hflat
  haveI : Algebra.QuasiFinite V B := hqf.toAlgebra
  haveI : q.LiesOver (IsLocalRing.maximalIdeal V) := ⟨hq.symm⟩
  obtain ⟨P, hPq, hP, hPl⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := (⊥ : Ideal V))
    (q := IsLocalRing.maximalIdeal V) q bot_le
  have hPV : P.comap φ = ⊥ := hPl.over.symm
  set κ := P.ResidueField
  have hinj : Function.Injective (algebraMap V κ) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro v hv
    rw [IsScalarTower.algebraMap_apply V B κ, Ideal.algebraMap_residueField_eq_zero] at hv
    have : v ∈ P.comap φ := hv
    rwa [hPV, Ideal.mem_bot] at this
  letI : Algebra K κ := (IsFractionRing.lift (K := K) hinj).toAlgebra
  haveI : IsScalarTower V K κ := IsScalarTower.of_algebraMap_eq
    (fun v => (IsFractionRing.lift_algebraMap (K := K) hinj v).symm)
  haveI : Algebra.QuasiFinite K κ := Algebra.QuasiFinite.of_restrictScalars V K κ
  haveI : Module.Finite K κ := Module.Finite.of_quasiFinite
  let e : K ≃+* κ := RingEquiv.ofBijective (algebraMap K κ)
    ⟨(algebraMap K κ).injective, IsSepClosed.algebraMap_surjective K κ⟩
  let χ : B →+* K := e.symm.toRingHom.comp (algebraMap B κ)
  have hχφ : ∀ v, χ (φ v) = algebraMap V K v := by
    intro v
    apply e.injective
    simp only [χ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.apply_symm_apply]
    change algebraMap B κ (algebraMap V B v) = algebraMap K κ (algebraMap V K v)
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hχ0 : ∀ b, χ b = 0 → b ∈ q := by
    intro b hb
    apply hPq
    rw [← Ideal.algebraMap_residueField_eq_zero]
    have : e (χ b) = algebraMap B κ b := by simp [χ]
    rw [← this, hb, map_zero]
  have hφq : ∀ v ∈ IsLocalRing.maximalIdeal V, φ v ∈ q := by
    intro v hv
    rw [← hq] at hv
    exact hv
  have hmem : ∀ b, χ b ∈ (algebraMap V K).range := by
    intro b
    rcases ValuationRing.isInteger_or_isInteger V (χ b) with ⟨v, hv⟩ | ⟨v, hv⟩
    · exact ⟨v, hv⟩
    by_cases hb0 : χ b = 0
    · exact ⟨0, by rw [hb0, map_zero]⟩
    by_cases hvu : IsUnit v
    · obtain ⟨u, rfl⟩ := hvu
      refine ⟨↑u⁻¹, ?_⟩
      rw [← inv_inv (χ b), ← hv]
      exact map_units_inv (algebraMap V K : V →* K) u
    · exfalso
      have hvm : v ∈ IsLocalRing.maximalIdeal V := hvu
      have h1 : χ (b * φ v - 1) = 0 := by
        rw [map_sub, map_mul, map_one, hχφ, hv, mul_inv_cancel₀ hb0, sub_self]
      have h2 := hχ0 _ h1
      have h3 : b * φ v ∈ q := q.mul_mem_left b (hφq v hvm)
      have h4 := q.sub_mem h3 h2
      rw [sub_sub_cancel] at h4
      exact ‹q.IsPrime›.ne_top ((Ideal.eq_top_iff_one q).mpr h4)
  let j := algebraMap V K
  have hj : Function.Injective j := IsFractionRing.injective V K
  let e₂ : V ≃+* j.range := RingEquiv.ofBijective j.rangeRestrict
    ⟨fun a b h => hj (congrArg Subtype.val h), j.rangeRestrict_surjective⟩
  let ψ : B →+* V := e₂.symm.toRingHom.comp (χ.codRestrict j.range hmem)
  have hψ : ∀ b, j (ψ b) = χ b := by
    intro b
    have : e₂ (ψ b) = χ.codRestrict j.range hmem b := by simp [ψ]
    exact congrArg Subtype.val this
  refine ⟨ψ, ?_, ?_⟩
  · ext v
    apply hj
    simp only [RingHom.comp_apply, RingHom.id_apply]
    rw [hψ, hχφ]
  · ext b
    rw [Ideal.mem_comap]
    constructor
    · intro hb
      have h1 : χ (b - φ (ψ b)) = 0 := by rw [map_sub, hχφ, hψ, sub_self]
      have h2 := hχ0 _ h1
      have h3 := hφq _ hb
      simpa using q.add_mem h2 h3
    · intro hb
      by_contra hn
      have hu : IsUnit (ψ b) := by
        by_contra h
        exact hn h
      obtain ⟨u, hu⟩ := hu
      have h1 : χ (b * φ ↑u⁻¹ - 1) = 0 := by
        rw [map_sub, map_mul, map_one, hχφ, ← hψ, ← hu, ← map_mul, Units.mul_inv, map_one, sub_self]
      have h2 := hχ0 _ h1
      have h3 : b * φ ↑u⁻¹ ∈ q := q.mul_mem_right _ hb
      have h4 := q.sub_mem h3 h2
      rw [sub_sub_cancel] at h4
      exact ‹q.IsPrime›.ne_top ((Ideal.eq_top_iff_one q).mpr h4)

private lemma exists_section_through_closed_fiber_point (V K : Type) [CommRing V] [IsDomain V]
    [ValuationRing V] [Field K] [IsAlgClosed K] [Algebra V K] [IsFractionRing V K]
    (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of V)) [LocallyQuasiFinite f] [Flat f] (x : X)
    (hx : f x = IsLocalRing.closedPoint V) :
    ∃ s : Spec (CommRingCat.of V) ⟶ X, s ≫ f = 𝟙 _ ∧ s (IsLocalRing.closedPoint V) = x := by
  obtain ⟨_, ⟨U, hU₀, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hU : IsAffineOpen U := hU₀
  have hg : Spec.map (Spec.preimage (hU.fromSpec ≫ f)) = hU.fromSpec ≫ f := Spec.map_preimage _
  set φ := Spec.preimage (hU.fromSpec ≫ f)
  haveI : Flat hU.fromSpec := inferInstance
  haveI : LocallyQuasiFinite hU.fromSpec := inferInstance
  haveI : Flat (hU.fromSpec ≫ f) := MorphismProperty.comp_mem _ _ _ ‹_› ‹_›
  haveI : LocallyQuasiFinite (hU.fromSpec ≫ f) := MorphismProperty.comp_mem _ _ _ ‹_› ‹_›
  have hflat : φ.hom.Flat := (HasRingHomProperty.Spec_iff (P := @Flat)).mp (hg ▸ inferInstance)
  have hqf : φ.hom.QuasiFinite :=
    (HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite)).mp (hg ▸ inferInstance)
  have hqx : hU.fromSpec (hU.primeIdealOf ⟨x, hxU⟩) = x := hU.fromSpec_primeIdealOf _
  set q := hU.primeIdealOf ⟨x, hxU⟩
  have hq : q.asIdeal.comap φ.hom = IsLocalRing.maximalIdeal V := by
    have h1 : (Spec.map φ) q = IsLocalRing.closedPoint V := by
      rw [hg]
      exact (congrArg f hqx).trans hx
    exact congrArg PrimeSpectrum.asIdeal h1
  obtain ⟨ψ, hψ, hψq⟩ := exists_retraction_of_flat_quasiFinite V K φ.hom hflat hqf q.asIdeal hq
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ hU.fromSpec, ?_, ?_⟩
  · rw [Category.assoc, ← hg, ← Spec.map_comp]
    have : φ ≫ CommRingCat.ofHom ψ = 𝟙 _ := by ext1; exact hψ
    rw [this, Spec.map_id]
  · have : (Spec.map (CommRingCat.ofHom ψ)) (IsLocalRing.closedPoint V) = q :=
      PrimeSpectrum.ext hψq
    exact (congrArg hU.fromSpec this).trans hqx

theorem _root_.GlobalTheory.exists_section_of_quasiFinite_flat :
    ∀ (V K : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [IsAlgClosed K]
      [Algebra V K] [IsFractionRing V K] (X : Scheme.{0}) (f : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp V) [IsSeparated f]
      [QuasiCompact f] [LocallyOfFiniteType f] [LocallyQuasiFinite f] [Flat f] (x : X),
      f x = IsLocalRing.closedPoint V →
        ∃ s : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp V ⟶ X, s ≫ f = 𝟙 _ ∧ s (IsLocalRing.closedPoint V) = x := by
  intro V K _ _ _ _ _ _ _ X f _ _ _ _ _ x hx
  exact exists_section_through_closed_fiber_point V K X f x hx

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralNthRootTestModelPoint
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.IntDiv

theorem exists_open_flat {X Y : Scheme.{0}} [IrreducibleSpace X] [IsIntegral Y]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]
    (hf : f (genericPoint X) = genericPoint Y) :
    ∃ W : X.Opens, (W : Set X).Nonempty ∧ ∀ x ∈ W, (f.stalkMap x).hom.Flat := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hξ, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint Y)) isOpen_univ
  have : Nonempty U := ⟨⟨_, hξ⟩⟩
  have : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let b : Sp Γ(Y, U) ⟶ Y := hU.fromSpec
  have : IsOpenImmersion b := IsAffineOpen.isOpenImmersion_fromSpec hU
  obtain ⟨r, hr, H⟩ := generic_flatness_scheme Γ(Y, U) _ (pullback.snd f b) inferInstance inferInstance
  let φ := algebraMap Γ(Y, U) (Localization.Away r)
  have h1 := H _ φ (IsLocalization.Away.algebraMap_isUnit r)
  have : IsOpenImmersion (spMap φ) := IsOpenImmersion.of_isLocalization r
  let j := pullback.fst (pullback.snd f b) (spMap φ) ≫ pullback.fst f b
  have hj : j ≫ f = pullback.snd (pullback.snd f b) (spMap φ) ≫ spMap φ ≫ b := by
    simp only [j, Category.assoc, pullback.condition, pullback.condition_assoc]
  have h2 : Flat (j ≫ f) := by rw [hj]; infer_instance
  have hd : IsDomain (Localization.Away r) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hr)
  refine ⟨j.opensRange, ?_, ?_⟩
  · have h3 : genericPoint Y ∈ Set.range (spMap φ ≫ b) :=
      ((genericPoint_spec Y).mem_open_set_iff (spMap φ ≫ b).opensRange.2).mpr
        ⟨_, trivial, (⊥ : PrimeSpectrum (Localization.Away r)), rfl⟩
    obtain ⟨z, hz⟩ := h3
    obtain ⟨w, -, hw⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := b) (genericPoint X)
      (spMap φ z) (hf.trans (hz.symm.trans (Scheme.Hom.comp_apply _ _ _)))
    obtain ⟨v, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.snd f b) (g := spMap φ) w z hw
    exact ⟨_, v, rfl⟩
  · rintro _ ⟨v, rfl⟩
    have h4 := Flat.stalkMap (j ≫ f) v
    rw [Scheme.Hom.stalkMap_comp] at h4
    exact (RingHom.Flat.respectsIso.cancel_right_isIso (f.stalkMap (j v)) (j.stalkMap v)).mp h4

open UnramifiedEndFlat in
theorem flat_of_quasiFinite_grpEnd (K : Type) [Field K] [IsAlgClosed K]
    (G : Over (Spec (CommRingCat.of K))) [GrpObj G] [IsIntegral G.left]
    [LocallyOfFiniteType G.hom] (φ : G ⟶ G) [IsMonHom φ] [LocallyQuasiFinite φ.left] [QuasiCompact φ.left] :
    Flat φ.left := by
  have := LocallyOfFiniteType.jacobsonSpace G.hom
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have : LocallyOfFiniteType (φ.left ≫ G.hom) := by rw [Over.w φ]; infer_instance
  have : LocallyOfFiniteType φ.left := locallyOfFiniteType_of_comp _ G.hom
  let o : G.left := η[G].left (IsLocalRing.closedPoint K)
  have hfo : φ.left o = o := by
    have : η[G] ≫ φ = η[G] := IsMonHom.one_hom φ
    exact congr(($this).left (IsLocalRing.closedPoint K))
  have hξ := FiniteEndFlat.apply_genericPoint φ.left hfo
  obtain ⟨W, hW, H⟩ := exists_open_flat φ.left hξ
  obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints hW W.2.isLocallyClosed
  refine flat_of_closedPoints _ fun x hx => ?_
  let x' : 𝟙_ _ ⟶ G := Over.homMk _ ((pointEquivClosedPoint G.hom).symm ⟨x, hx⟩).2
  let y' : 𝟙_ _ ⟶ G := Over.homMk _ ((pointEquivClosedPoint G.hom).symm ⟨y, hyc⟩).2
  let α := GrpObj.mulRight (A := G) (y'⁻¹ * x')
  let β := GrpObj.mulRight (A := G) ((y'⁻¹ * x') ≫ φ)
  have hαβ : α.hom ≫ φ = φ ≫ β.hom := by
    simp only [α, β]
    generalize y'⁻¹ * x' = z
    simp [comp_lift_assoc]
  have hα : y' ≫ α.hom = x' := by
    have : y' ≫ α.hom = y' * (y'⁻¹ * x') := by
      simp [α, comp_lift_assoc, Hom.mul_def]
    rw [this, mul_inv_cancel_left]
  have hα' : α.hom.left y = x := by
    have h := congr(($hα).left (IsLocalRing.closedPoint K))
    rw [← pointOfClosedPoint_apply G.hom x hx (IsLocalRing.closedPoint K),
      ← pointOfClosedPoint_apply G.hom y hyc (IsLocalRing.closedPoint K)]
    exact h
  have : IsIso α.hom.left := inferInstanceAs (IsIso ((Over.forget _).map α.hom))
  have : IsIso β.hom.left := inferInstanceAs (IsIso ((Over.forget _).map β.hom))
  have h1 : ((φ.left ≫ β.hom.left).stalkMap y).hom.Flat := by
    rw [Scheme.Hom.stalkMap_comp]
    exact (Flat.stalkMap β.hom.left _).comp (H y hy)
  rw [← Over.comp_left, ← hαβ, Over.comp_left, Scheme.Hom.stalkMap_comp] at h1
  rw [← hα']
  exact (RingHom.Flat.respectsIso.cancel_right_isIso
    (φ.left.stalkMap (α.hom.left y)) (α.hom.left.stalkMap y)).mp h1

theorem flat_fibre {S : Scheme.{0}} (G : Over S) [GrpObj G] [Smooth G.hom] [GeometricallyConnected G.hom]
    (φ : G ⟶ G) [IsMonHom φ] [LocallyQuasiFinite φ.left] [QuasiCompact φ.left] (k : Type) [Field k]
    (s : Sp k ⟶ S) : Flat ((Over.pullback s).map φ).left := by
  refine flat_of_flat_fieldBaseChange k (AlgebraicClosure k) (algebraMap _ _) _ _ _ ?_
  let t : Sp (AlgebraicClosure k) ⟶ Sp k := spMap (algebraMap _ _)
  have hi := grpObj_geometricallyIntegral_of_smooth _ G
  have h₁ : GeometricallyIntegral ((Over.pullback s).obj G).hom :=
    inferInstanceAs (GeometricallyIntegral (pullback.snd G.hom s))
  have h₂ : GeometricallyIntegral ((Over.pullback t).obj ((Over.pullback s).obj G)).hom :=
    inferInstanceAs (GeometricallyIntegral (pullback.snd ((Over.pullback s).obj G).hom t))
  have := GeometricallyIntegral.isIntegral_of_subsingleton ((Over.pullback t).obj ((Over.pullback s).obj G)).hom
  have h₃ : LocallyOfFiniteType ((Over.pullback s).obj G).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd G.hom s))
  have h₄ : LocallyOfFiniteType ((Over.pullback t).obj ((Over.pullback s).obj G)).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd ((Over.pullback s).obj G).hom t))
  have p₁ := AbLaw.MulN.isPullback_baseChange s φ
  have p₂ := AbLaw.MulN.isPullback_baseChange t ((Over.pullback s).map φ)
  have : LocallyQuasiFinite ((Over.pullback t).map ((Over.pullback s).map φ)).left :=
    MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) p₂
      (MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) p₁ inferInstance)
  have : QuasiCompact ((Over.pullback t).map ((Over.pullback s).map φ)).left :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) p₂
      (MorphismProperty.of_isPullback (P := @QuasiCompact) p₁ inferInstance)
  exact flat_of_quasiFinite_grpEnd _ _ _

theorem comp_mulA {S : Scheme.{0}} {G T : Over S} [GrpObj G] (x : T ⟶ G) (n : ℕ) : x ≫ mulA G n = x ^ n := by
  rw [mulA, MonObj.comp_pow, Category.comp_id]

theorem points_of_finite_surjective {S : Scheme.{0}} (B : Over S) [GrpObj B] (n : ℕ)
    [IsFinite (mulA B n).left] [Surjective (mulA B n).left] {K : Type} [Field K] [IsAlgClosed K] (t : Sp K ⟶ S) :
    Finite {x : Over.mk t ⟶ B // x ^ n = 1} ∧ ∀ x : Over.mk t ⟶ B, ∃ y, y ^ n = x := by
  constructor
  · let e : Sp K ⟶ B.left := (1 : Over.mk t ⟶ B).left
    let g := pullback.snd (mulA B n).left e
    have hfin : Finite ↥(pullback (mulA B n).left e) := by
      have := g.finite_preimage_singleton (IsLocalRing.closedPoint K)
      refine Set.finite_univ_iff.mp (this.subset fun z _ => ?_)
      exact Subsingleton.elim (α := PrimeSpectrum K) _ _
    have hx : ∀ x : {x : Over.mk t ⟶ B // x ^ n = 1}, x.1.left ≫ (mulA B n).left = 𝟙 _ ≫ e := fun x => by
      rw [Category.id_comp, ← Over.comp_left, comp_mulA, x.2]
    refine Finite.of_injective (β := ↥(pullback (mulA B n).left e))
      (fun x => pullback.lift x.1.left (𝟙 (Sp K)) (hx x) (IsLocalRing.closedPoint K)) fun a b h => ?_
    have := ext_of_apply_closedPoint_eq (K := K) g (pullback.lift_snd _ _ (hx a)) (pullback.lift_snd _ _ (hx b)) h
    refine Subtype.ext (Over.OverMorphism.ext ?_)
    exact (pullback.lift_fst _ _ (hx a)).symm.trans
      ((congrArg (· ≫ pullback.fst _ _) this).trans (pullback.lift_fst _ _ (hx b)))
  · intro x
    obtain ⟨y, hy⟩ := GeomSurj.exists_lift_of_surjective (mulA B n).left x.left
    refine ⟨Over.homMk y ?_, ?_⟩
    · rw [← Over.w (mulA B n), ← Category.assoc, ← hy]; exact Over.w x
    · rw [← comp_mulA]; exact Over.OverMorphism.ext hy.symm

theorem points_of_unifPre (hm : MulNSt) {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {D : DegData V (IsLocalRing.maximalIdeal V)} {A : PolAV (Spec (CommRingCat.of (FractionRing V)))}
    {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G]
    (U : UnifPre (IsLocalRing.maximalIdeal V) D A G) {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [IsAlgClosed K]
    (t : Sp K ⟶ Sp V) :
    Finite {x : Over.mk t ⟶ G // x ^ n = 1} ∧ ∀ x : Over.mk t ⟶ G, ∃ y, y ^ n = x := by
  rcases ZJ.field_point_factor_dvr V K t with ⟨r, hr⟩ | ⟨r, hr⟩
  · have ht : Set.range t = {IsLocalRing.closedPoint V} := by
      have : ∀ z, t z = IsLocalRing.closedPoint V := fun z => by
        rw [hr, Scheme.Hom.comp_apply,
          Subsingleton.elim (α := PrimeSpectrum _) (r z) (IsLocalRing.closedPoint (IsLocalRing.ResidueField V))]
        exact IsLocalRing.comap_closedPoint (IsLocalRing.residue V)
      exact Set.eq_singleton_iff_unique_mem.2 ⟨⟨IsLocalRing.closedPoint K, this _⟩, by rintro _ ⟨z, rfl⟩; exact this z⟩
    obtain ⟨p, h₁, h₂, h₃, -⟩ := FewZeros.exists_points_hom U t ht hn
    obtain ⟨m₁, -, m₂, -⟩ := hm _ D.toPre.P n hn
    obtain ⟨b₁, b₂⟩ := points_of_finite_surjective D.toPre.P.A n t
    refine ⟨h₃ b₁, fun x => ?_⟩
    obtain ⟨b, hb⟩ := b₂ (p x)
    obtain ⟨y, rfl⟩ := h₁ b
    obtain ⟨z, -, hz⟩ := h₂ (x * (y ^ n)⁻¹) (by rw [map_mul, map_inv, map_pow, hb, mul_inv_cancel])
    exact ⟨z * y, by rw [mul_pow, hz, inv_mul_cancel_right]⟩
  · obtain ⟨m₁, -, m₂, -⟩ := hm _ A n hn
    obtain ⟨b₁, b₂⟩ := points_of_finite_surjective A.A n r
    have := U.gen_hom
    let e₁ := TorsionLift.ptsEquiv (jK V) G (Over.mk r) t hr.symm
    let e₂ : (Over.mk r ⟶ (Over.pullback (jK V)).obj G) ≃* (Over.mk r ⟶ A.A) :=
      MulEquiv.ofBijective (IsMonHom.monoidHom U.gen.hom (Over.mk r))
        ⟨fun a b h => (cancel_mono U.gen.hom).1 h, fun b => ⟨b ≫ U.gen.inv, by
          change (b ≫ U.gen.inv) ≫ U.gen.hom = b
          simp⟩⟩
    let e := e₂.symm.trans e₁
    refine ⟨FewZeros.finite_torsion_of_mulEquiv e n b₁, fun x => ?_⟩
    obtain ⟨y, hy⟩ := b₂ (e.symm x)
    exact ⟨e y, by rw [← map_pow, hy, e.apply_symm_apply]⟩

theorem exists_root {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom]
    [GeometricallyConnected G.hom] (n : ℕ)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ Sp V),
      Finite {x : Over.mk t ⟶ G // x ^ n = 1} ∧ ∀ x : Over.mk t ⟶ G, ∃ y, y ^ n = x)
    (O C : Type) [CommRing O] [IsDomain O] [ValuationRing O] [Field C] [IsAlgClosed C] [Algebra O C]
    [IsFractionRing O C] (c : Sp O ⟶ G.left) : ∃ c' : Sp O ⟶ G.left, c' ≫ (mulA G n).left = c := by
  have hm := AbLaw.MulN.isMonHom_mulA G n
  have : LocallyOfFiniteType ((mulA G n).left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : LocallyOfFiniteType (mulA G n).left := locallyOfFiniteType_of_comp _ G.hom
  have : QuasiCompact ((mulA G n).left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : QuasiCompact (mulA G n).left := QuasiCompact.of_comp _ G.hom
  have : IsSeparated ((mulA G n).left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : IsSeparated (mulA G n).left := IsSeparated.of_comp _ G.hom
  have : LocallyQuasiFinite (mulA G n).left :=
    locallyQuasiFinite_of_finite_geometric_ker _ G G _ hm inferInstance inferInstance fun K _ _ t => by
      simp only [comp_mulA]
      exact (h K t).1
  have : Flat (mulA G n).left :=
    flat_of_flat_fibres_dvr V (FractionRing V) G G _ inferInstance inferInstance inferInstance inferInstance
      (flat_fibre G _ _ _) (flat_fibre G _ _ _)
  let K := AlgebraicClosure (IsLocalRing.ResidueField O)
  let r : Sp K ⟶ Sp O := spMap (algebraMap (IsLocalRing.ResidueField O) K) ≫ spMap (IsLocalRing.residue O)
  have hr : ∀ z : Sp K, r z = IsLocalRing.closedPoint O := fun z => by
    refine (Scheme.Hom.comp_apply _ _ z).trans ?_
    rw [Subsingleton.elim (α := PrimeSpectrum _)
      (spMap (algebraMap (IsLocalRing.ResidueField O) K) z) (IsLocalRing.closedPoint (IsLocalRing.ResidueField O))]
    exact IsLocalRing.comap_closedPoint (IsLocalRing.residue O)
  obtain ⟨y, hy⟩ := (h K ((r ≫ c) ≫ G.hom)).2 (Over.homMk (r ≫ c) rfl)
  have hy' : y.left ≫ (mulA G n).left = r ≫ c := by
    rw [← Over.comp_left, comp_mulA, hy]; rfl
  obtain ⟨s, hs, -⟩ := exists_section_of_quasiFinite_flat O C _ (pullback.snd (mulA G n).left c)
    (pullback.lift y.left r hy' (IsLocalRing.closedPoint K))
    ((congrArg (fun g => g (IsLocalRing.closedPoint K)) (pullback.lift_snd y.left r hy')).trans (hr _))
  exact ⟨s ≫ pullback.fst _ _, by rw [Category.assoc, pullback.condition, reassoc_of% hs]⟩

theorem exists_integral_root : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (a : u.PtC) (k : ℕ), 1 ≤ k → u.Int a → ∃ a' : u.PtC, u.Int a' ∧ a' ^ k = a := by
  intro hL o Ω _ _ _ _ S ρ p _ y₀ u a k hk ⟨c, hc, hca⟩
  have := u.semi.smooth
  have := u.semi.separated
  have := u.semi.quasiCompact
  have := u.semi.geomConnected
  obtain ⟨c', hc'⟩ := exists_root u.G k (fun K _ _ t => points_of_unifPre hL.1.mulN u.U.toUnifPre hk t)
    (OO p) (PadicAlgCl p) c
  have h₁ : c' ≫ u.G.hom = c ≫ u.G.hom := by rw [← hc', Category.assoc, Over.w]
  let e := TorsionLift.ptsEquiv (jK u.V) u.G (TFK (R := u.V) (PadicAlgCl p)) _ rfl
  have he : ∀ x : u.PtC, (e x).left = u.toG x := fun x => TorsionLift.ptsEquiv_left _ _ _ _ _ x
  let x' : Over.mk ((TFK (R := u.V) (PadicAlgCl p)).hom ≫ jK u.V) ⟶ u.G :=
    Over.homMk (gPt p ≫ c') (by
      rw [Category.assoc, h₁, ← Category.assoc, hca, ← he]
      exact Over.w (e a))
  refine ⟨e.symm x', ⟨c', h₁.trans hc, ?_⟩, e.injective ?_⟩
  · rw [← he, e.apply_symm_apply]; rfl
  · rw [map_pow, e.apply_symm_apply, ← comp_mulA]
    refine Over.OverMorphism.ext ?_
    rw [he, ← hca, ← hc']
    exact Category.assoc _ _ _

end GlobalTheory.IntDiv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralNthRootTestModelPointStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_nthRoot_testModel_point : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (a : u.PtC) (k : ℕ), 1 ≤ k → u.Int a → ∃ a' : u.PtC, u.Int a' ∧ a' ^ k = a := by
  first | exact @GlobalTheory.IntDiv.exists_integral_root | exact GlobalTheory.IntDiv.exists_integral_root | (intros; apply GlobalTheory.IntDiv.exists_integral_root <;> assumption)
end
