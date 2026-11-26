module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcGenericPointDescendsToPowerSeries
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExtendedArcUAdicUniformisationOfArcData
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcGenericPointExtendsPowerSeriesStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcAbelianLocusAndModuliOfTraitData
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcAbelianLocusAndModuliOfTraitData
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

namespace GlobalTheory
namespace ArcLocus

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem closedPoint_notMem (Y : Model Xo c β) {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'}
    (a : ArcIn D l β O' b) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (f : O' →+* R) (u : R)
    (χ : Sp R ⟶ Y.X) (h : Y.HasArcData a (IsLocalRing.maximalIdeal R) f u χ) :
    χ (IsLocalRing.closedPoint R) ∉ abLocus Y.t.G := by
  intro h₁
  obtain ⟨W⟩ := (Y.hasArcData_iff a _ f u χ).1 h
  have h₂ := (abLocus_pullback abLocusOne Y.t.semi W.m.cart.1 _).1 h₁
  have hmax : (IsLocalRing.maximalIdeal R ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  have hF : IsField (R ⧸ IsLocalRing.maximalIdeal R ^ (0 + 1)) :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 hmax
  obtain ⟨p, hp⟩ : IsLocalRing.closedPoint R ∈ Set.range (PrimeSpectrum.comap
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (0 + 1)))) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker, zero_add, pow_one]
    exact le_refl (IsLocalRing.maximalIdeal R)
  let g := W.P.U.gt 0
  have m : Mono g.i := ⟨fun a b h => g.isKernel.hom_ext h (toUnit_unique _ _)⟩
  have hp' : thick R (IsLocalRing.maximalIdeal R) 0 p ∈ abLocus W.t.G := by
    rw [← hp] at h₂; exact h₂
  have hs := ArcNotAbelian.subsingleton_of_mem_abLocus W.t.G W.t.semi _ hF _ p hp' W.P.D.toPre.X g.i g.i_hom
  have hn : Nontrivial a.D₀.X := a.nontriv
  exact not_subsingleton _ (W.e.toEquiv.subsingleton)

theorem exists_trait (R : Type) [CommRing R] [IsDomain R] [CharZero R] [IsNoetherianRing R] (x : PrimeSpectrum R)
    (hx : x.asIdeal ≠ ⊥) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R →+* W)
      (gam : FractionRing R →+* FractionRing W), CDvr W ∧ (∀ r, gam (algebraMap R _ r) = algebraMap W _ (φ r)) ∧
      (IsLocalRing.maximalIdeal W).comap φ = x.asIdeal := by
  obtain ⟨W, _, _, _, _, φ, h1, h2⟩ :=
    exists_complete_discreteValuationRing_of_prime_lt (⊥ : Ideal R) x.asIdeal (bot_lt_iff_ne_bot.2 hx)
  have hφ : Function.Injective φ := (RingHom.injective_iff_ker_eq_bot φ).2 h1
  have hφ' : Function.Injective ((algebraMap W (FractionRing W)).comp φ) :=
    (IsFractionRing.injective W (FractionRing W)).comp hφ
  exact ⟨W, inferInstance, inferInstance, inferInstance, φ, IsFractionRing.lift hφ',
    ⟨inferInstance, inferInstance, charZero_of_injective_ringHom hφ⟩,
    fun r => IsFractionRing.lift_algebraMap hφ' r, h2⟩

theorem j_mem (Y : Model Xo c β) (p : Xo.XF c) : Y.j p ∈ abLocus Y.t.G := by
  have hz : Y.jQ p ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G := by
    rw [Y.ab_gen]; exact ⟨_, rfl⟩
  exact hz

theorem mem_range_j (Y : Model Xo c β) (z : Y.X) (hz : z ∈ abLocus Y.t.G) (p : Xo.XF c)
    (hp : Y.s z = Y.s (Y.j p)) : z ∈ Set.range Y.j := by
  have h₁ : z ∈ Set.range (pullback.fst Y.s (spMap β)) := by
    rw [Scheme.Pullback.range_fst, Set.mem_preimage, hp]
    have : Y.j p ∈ Set.range (pullback.fst Y.s (spMap β)) := ⟨Y.jQ p, rfl⟩
    rwa [Scheme.Pullback.range_fst] at this
  obtain ⟨w, rfl⟩ := h₁
  have h₂ : w ∈ Set.range Y.jQ := by rw [← Y.ab_gen]; exact hz
  obtain ⟨q, rfl⟩ := h₂
  exact ⟨q, rfl⟩

theorem exists_jK_eq_bot (R : Type) [CommRing R] [IsDomain R] :
    ∃ pt : Sp (FractionRing R), jK R pt = (⊥ : PrimeSpectrum R) := by
  refine ⟨(⊥ : PrimeSpectrum (FractionRing R)), PrimeSpectrum.ext ?_⟩
  exact (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))

end ArcLocus


open ArcLocus in
theorem arc_abLocus_of_traitData : Laws → Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b : c.V W₀ →+* O') (a : ArcIn D l (c.V W₀).subtype O' b) (ϖ : O'), ArcBase O' ϖ → ∀ (y : Sp (FractionRing (PowerSeries O')) ⟶ Xo.XF c) (χ : Sp (PowerSeries O') ⟶ Y.X), jK _ ≫ χ = y ≫ Y.j → TraitData Y a (RingHom.id _) y → χ ≫ Y.s = spMap (PowerSeries.C (R := O')) ≫ spMap b ∧ (∀ x : Sp (PowerSeries O'), χ x ∈ abLocus Y.t.G ↔ PowerSeries.X ∉ x.asIdeal) ∧ ∀ x : Sp (PowerSeries O'), PowerSeries.C ϖ * PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j := by
  intro _ _ E _ _ _ H D l Xo c W₀ Y O' _ _ _ b a ϖ hb y χ hχ hT
  have hN : IsNoetherianRing O' := by
    rcases hb with h | h
    · letI := h.1.toField; infer_instance
    · have := h.1; infer_instance
  have hc : CharZero (PowerSeries O') := charZero_of_injective_ringHom (PowerSeries.C_injective (R := O'))
  obtain ⟨pt, hpt⟩ := exists_jK_eq_bot (PowerSeries O')
  have h0 : χ (⊥ : PrimeSpectrum (PowerSeries O')) = Y.j (y pt) := by
    rw [← hpt, ← Scheme.Hom.comp_apply, hχ, Scheme.Hom.comp_apply]
  have h1 : χ ≫ Y.s = spMap (PowerSeries.C (R := O')) ≫ spMap b := by
    have hd : IsDominant (jK (PowerSeries O')) := by
      constructor
      exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap (PowerSeries O') (FractionRing (PowerSeries O')))).2
        (by rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective (PowerSeries O') _)]; exact bot_le)
    refine ext_of_isDominant (jK (PowerSeries O')) ?_
    rw [← Category.assoc, hχ, Category.assoc, hT.1]
    have : spMap (RingHom.id (PowerSeries O')) = 𝟙 _ := Spec.map_id _
    rw [this, Category.id_comp]
  have h2 : ∀ x : Sp (PowerSeries O'), χ x ∈ abLocus Y.t.G ↔ PowerSeries.X ∉ x.asIdeal := by
    intro x
    by_cases hx : x.asIdeal = ⊥
    · have e : x = (⊥ : PrimeSpectrum (PowerSeries O')) := PrimeSpectrum.ext hx
      refine iff_of_true ?_ ?_
      · rw [e, h0]; exact j_mem Y _
      · rw [hx]; exact PowerSeries.X_ne_zero
    obtain ⟨W, _, _, _, φ, gam, hW, hg, hφ⟩ := exists_trait (PowerSeries O') x hx
    have key : spMap gam ≫ jK (PowerSeries O') = jK W ≫ spMap φ := by
      show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 2
      exact RingHom.ext hg
    have ht := hT.2 W hW φ gam hg (spMap φ ≫ χ) (by rw [← hχ, ← Category.assoc, key, Category.assoc])
    have hu : PowerSeries.X ∉ x.asIdeal ↔ IsUnit (φ PowerSeries.X) := by
      rw [← hφ, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
    have hcl : spMap φ (IsLocalRing.closedPoint W) = x := PrimeSpectrum.ext hφ
    rw [hu]
    refine ⟨fun hab => ?_, fun h => ht.1 h ⟨IsLocalRing.closedPoint W, (Scheme.Hom.comp_apply _ _ _).trans (congrArg χ hcl)⟩⟩
    by_contra h
    obtain ⟨W', _, _, _, io, -, -, hfin, hA⟩ := ht.2 h
    refine closedPoint_notMem Y a _ _ _ hA ?_
    have hcl' : spMap io (IsLocalRing.closedPoint W') = IsLocalRing.closedPoint W := by
      refine PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal ?_)
      exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' io hfin.to_isIntegral (IsLocalRing.maximalIdeal W')
    have e : (spMap io ≫ spMap φ ≫ χ) (IsLocalRing.closedPoint W') = χ x :=
      (Scheme.Hom.comp_apply _ _ _).trans ((congrArg (spMap φ ≫ χ) hcl').trans
        ((Scheme.Hom.comp_apply _ _ _).trans (congrArg χ hcl)))
    rw [e]
    exact hab
  refine ⟨h1, h2, fun x hx => mem_range_j Y _ ((h2 x).2 fun h => hx (Ideal.mul_mem_left _ _ h)) (y pt) ?_⟩
  have hC : ∀ z : Sp (PowerSeries O'), PowerSeries.C ϖ * PowerSeries.X ∉ z.asIdeal →
      spMap (PowerSeries.C (R := O')) z = (⊥ : PrimeSpectrum O') := by
    intro z hz
    refine PrimeSpectrum.ext ?_
    change z.asIdeal.comap (PowerSeries.C (R := O')) = ⊥
    have hzp := z.isPrime
    rcases hb with h | h
    · letI := h.1.toField
      exact Ideal.eq_bot_of_prime _
    · have := h.1
      by_contra hne
      have hm := IsLocalRing.eq_maximalIdeal (Ring.DimensionLEOne.maximalOfPrime hne inferInstance)
      have : ϖ ∈ z.asIdeal.comap (PowerSeries.C (R := O')) := by
        rw [hm]; exact h.2.1.not_isUnit
      exact hz (Ideal.mul_mem_right _ _ this)
  have hb0 : spMap (PowerSeries.C (R := O')) (⊥ : PrimeSpectrum (PowerSeries O')) = (⊥ : PrimeSpectrum O') :=
    PrimeSpectrum.ext ((RingHom.injective_iff_ker_eq_bot _).1 (PowerSeries.C_injective (R := O')))
  have h3 : ∀ z : Sp (PowerSeries O'), Y.s (χ z) = spMap b (spMap (PowerSeries.C (R := O')) z) := fun z => by
    rw [← Scheme.Hom.comp_apply, h1, Scheme.Hom.comp_apply]
  rw [← h0, h3, hC x hx]
  exact ((h3 _).trans (congrArg (spMap b) hb0)).symm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcAbelianLocusAndModuliOfTraitDataStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arc_abelianLocus_and_moduli_of_traitData : Laws → Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b : c.V W₀ →+* O') (a : ArcIn D l (c.V W₀).subtype O' b) (ϖ : O'), ArcBase O' ϖ → ∀ (y : Sp (FractionRing (PowerSeries O')) ⟶ Xo.XF c) (χ : Sp (PowerSeries O') ⟶ Y.X), jK _ ≫ χ = y ≫ Y.j → TraitData Y a (RingHom.id _) y → χ ≫ Y.s = spMap (PowerSeries.C (R := O')) ≫ spMap b ∧ (∀ x : Sp (PowerSeries O'), χ x ∈ abLocus Y.t.G ↔ PowerSeries.X ∉ x.asIdeal) ∧ ∀ x : Sp (PowerSeries O'), PowerSeries.C ϖ * PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j := by
  first | exact @GlobalTheory.arc_abLocus_of_traitData | exact GlobalTheory.arc_abLocus_of_traitData | (intros; apply GlobalTheory.arc_abLocus_of_traitData <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcFamilyFourthConditionInvertiblePushforward
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

namespace GlobalTheory.LN.ArcClause

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem exists_lift (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) {K : Type} [Field K] (z : Sp K ⟶ Y.X)
    (h : Set.range z ⊆ Set.range Y.j) : ∃ y : Sp K ⟶ Xo.XF c, y ≫ Y.j = z := by
  obtain ⟨g, hg⟩ : ∃ g : V →+* K, z ≫ Y.s = spMap g := ⟨(Spec.preimage (z ≫ Y.s)).hom, (Spec.map_preimage _).symm⟩
  obtain ⟨x, hx⟩ := h ⟨(default : PrimeSpectrum K), rfl⟩
  have e : Y.j ≫ Y.s = (Y.jQ ≫ pullback.snd _ _) ≫ spMap V.subtype := by
    rw [Model.j, Category.assoc, pullback.condition, Category.assoc]
  obtain ⟨q, e1⟩ : ∃ q : PrimeSpectrum c.F, PrimeSpectrum.comap g default = PrimeSpectrum.comap V.subtype q := by
    have e2 : (z ≫ Y.s) (default : PrimeSpectrum K) = (Y.j ≫ Y.s) x := congrArg Y.s hx.symm
    rw [hg, e] at e2
    exact ⟨_, e2⟩
  have hinj : Function.Injective g := by
    refine (injective_iff_map_eq_zero g).2 fun v hv => ?_
    have h1 : v ∈ (PrimeSpectrum.comap g default).asIdeal := by
      rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, hv]; exact zero_mem _
    rw [e1, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] at h1
    rw [Ideal.eq_bot_of_prime q.asIdeal] at h1
    exact Subtype.ext h1
  let g' : c.F →+* K := IsFractionRing.lift hinj
  have hg' : spMap g' ≫ spMap V.subtype = spMap g := by
    rw [← Spec.map_comp]
    congr 1
    ext v
    exact IsFractionRing.lift_algebraMap hinj v
  let z' : Sp K ⟶ pullback Y.s (spMap V.subtype) := pullback.lift z (spMap g') (hg.trans hg'.symm)
  have hz' : z' ≫ pullback.fst _ _ = z := pullback.lift_fst _ _ _
  have : IsPreimmersion (spMap V.subtype) := IsPreimmersion.of_isLocalization (nonZeroDivisors V) (S := c.F)
  have h1 : IsPreimmersion (pullback.fst Y.s (spMap V.subtype)) :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip this
  have := Y.jQ_open
  have hr : Set.range z' ⊆ Set.range Y.jQ := by
    rintro _ ⟨p, rfl⟩
    obtain rfl : p = (default : PrimeSpectrum K) := Subsingleton.elim (α := PrimeSpectrum K) _ _
    refine ⟨x, (pullback.fst Y.s (spMap V.subtype)).isEmbedding.injective ?_⟩
    have e3 : (z' ≫ pullback.fst Y.s (spMap V.subtype)) (default : PrimeSpectrum K) = z (default : PrimeSpectrum K) := by
      rw [hz']
    exact hx.trans e3.symm
  refine ⟨IsOpenImmersion.lift Y.jQ z' hr, ?_⟩
  rw [Model.j, ← Category.assoc, IsOpenImmersion.lift_fac, hz']

theorem not_mem_generic {R R' : Type} [CommRing R] [CommRing R'] [IsDomain R'] (f : R →+* R') {r : R} (hr : f r ≠ 0)
    (p : PrimeSpectrum (FractionRing R')) : r ∉ ((jK R' ≫ spMap f) p).asIdeal := by
  intro h
  have h1 : algebraMap R' (FractionRing R') (f r) ∈ PrimeSpectrum.asIdeal p := h
  rw [Ideal.eq_bot_of_prime (PrimeSpectrum.asIdeal p)] at h1
  exact hr (IsFractionRing.injective R' (FractionRing R') (h1.trans (map_zero _).symm))

theorem arc_clause : DVR.TwistBaseChangeStatement → Laws → Laws2 → Laws3 → Laws4 → Laws5 → Laws6 → Ega → USt → PelSt → HomExtSt → ArcFamSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (p : ℕ), Y.LevelStructureConditions p → Amp Y → Y.N4 := by
  intro hT h1 h2 h3 h4 h5 h6 hE hU hP hX hF E _ _ _ H D l Xo c W₀ Y p hN hA O' _ _ _ b ϖ a hB
  obtain ⟨m, Z, π, t, mt, hodd, hunit, hfin, hsurj, hAF⟩ := hA
  have hm : IsUnit (m : O') := by simpa using hunit.map b
  obtain ⟨R₁, _, _, g, y₁, hg, hgf, hR, hTD, hθ, hf⟩ := hF E H D l Xo c W₀ Y O' b ϖ a hB m hodd hm
  let gam : FractionRing (PowerSeries O') →+* FractionRing R₁ :=
    IsFractionRing.lift (g := (algebraMap R₁ (FractionRing R₁)).comp g) ((IsFractionRing.injective R₁ _).comp hg)
  have hgam : ∀ r, gam (algebraMap (PowerSeries O') _ r) = algebraMap R₁ _ (g r) := fun r =>
    IsFractionRing.lift_algebraMap _ r
  obtain ⟨y, hy, hTy⟩ := GlobalTheory.T.arcGenericPoint_descends_to_powerSeries h1 h2 h3 h4 h5 h6 E H D l Xo c W₀ Y O' b a ϖ hB R₁ g y₁ gam hgam hgf hR hTD
  have hys : y ≫ Y.j ≫ Y.s = jK _ ≫ spMap (PowerSeries.C (R := O')) ≫ spMap b := by
    have := hTy.1
    rwa [show spMap (RingHom.id (PowerSeries O')) = 𝟙 _ from Spec.map_id _, Category.id_comp] at this
  obtain ⟨χ, hχ⟩ := GlobalTheory.T.arc_generic_point_extends_powerSeries h1 h2 E H D l Xo c W₀ Y O' b a ϖ hB m Z π t mt hfin hsurj hAF R₁ g y₁ gam hgam hgf hR
    y hy hys hθ hf
  obtain ⟨c1, c2, c3⟩ := GlobalTheory.T.arc_abelianLocus_and_moduli_of_traitData h1 h2 E H D l Xo c W₀ Y O' b a ϖ hB y χ hχ hTy
  have c4 := GlobalTheory.T.extendedArc_uAdicUniformisation_of_arcData h1 h2 h3 h4 h5 h6 hE hU hP hX E H D l Xo c W₀ Y O' b a ϖ hB hN.2.2.1 y χ hχ hTy
  have hϖ : ϖ ≠ 0 := by
    rcases hB with ⟨-, rfl⟩ | ⟨-, h, -⟩
    exacts [one_ne_zero, h.ne_zero]
  refine ⟨χ, fun χ' => ⟨fun h => h ▸ ⟨c1, c2, c3, c4⟩, fun ⟨d1, _, d3, d4⟩ => ?_⟩, fun hirr y' ev hs hr hd hC hXv => ?_⟩
  · have hpid : IsPrincipalIdealRing O' ∧ IsLocalRing O' := by
      rcases hB with ⟨h, -⟩ | ⟨h, -⟩
      · letI := h.toField
        exact ⟨inferInstance, inferInstance⟩
      · exact ⟨inferInstance, inferInstance⟩
    obtain ⟨_, _⟩ := hpid
    have : CharZero (PowerSeries O') := charZero_of_injective_ringHom (f := PowerSeries.C (R := O')) PowerSeries.C_injective
    obtain ⟨y', hy'⟩ := exists_lift (c.V W₀) Y (jK (PowerSeries O') ≫ χ') (by
      rintro _ ⟨q, rfl⟩
      refine d3 _ ?_
      have := not_mem_generic (RingHom.id (PowerSeries O')) (r := PowerSeries.C ϖ * PowerSeries.X)
        (mul_ne_zero (fun h => hϖ (PowerSeries.C_injective (h.trans (map_zero _).symm))) PowerSeries.X_ne_zero) q
      exact this)
    exact GlobalTheory.T.model_points_eq_of_same_degeneration_data h1 h2 h3 h4 h5 E H D l Xo c W₀ Y O' b a (PowerSeries O') (Ideal.span {PowerSeries.X})
      (PowerSeries.C (R := O')) PowerSeries.X ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
      (fun h => PowerSeries.X_prime.not_unit (Ideal.span_singleton_eq_top.1 h)) PowerSeries.C_injective
      χ' χ y' y hy' hχ.symm d1 c1 d4 c4
  · rcases hB with ⟨-, rfl⟩ | ⟨hdvr, -, hc⟩
    · exact absurd isUnit_one hirr.not_isUnit
    have hc' : IsAdicComplete (IsLocalRing.maximalIdeal O') O' := by
      rwa [hirr.maximalIdeal_eq]
    have hrg : Set.range (jK O' ≫ spMap ev ≫ χ) ⊆ Set.range Y.j := by
      rintro _ ⟨q, rfl⟩
      refine c3 _ ?_
      have := not_mem_generic ev (r := PowerSeries.C ϖ * PowerSeries.X)
        (by rw [map_mul, hC, hXv]; exact mul_ne_zero hϖ hϖ) q
      exact this
    have c5 := GlobalTheory.T.arcData_specialise_at_uniformiser h1 h2 hT h4.unifBaseChange h5 E H D l Xo c _ _ Y O' b ϖ a hirr hc' ev hC hXv χ c1 hrg c4
    obtain ⟨z, hz⟩ := exists_lift (c.V W₀) Y _ hrg
    obtain ⟨z', hz'⟩ := exists_lift (c.V W₀) Y _ hr
    have hid : spMap (RingHom.id O') = 𝟙 _ := Spec.map_id _
    have hev : spMap ev ≫ spMap (PowerSeries.C (R := O')) = spMap (RingHom.id O') := by
      rw [← Spec.map_comp]
      congr 1
      ext x
      exact hC x
    refine GlobalTheory.T.model_points_eq_of_same_degeneration_data h1 h2 h3 h4 h5 E H D l Xo c W₀ Y O' b a O' (Ideal.span {ϖ}) (RingHom.id O') ϖ
      ⟨inferInstance, inferInstance, inferInstance, hc⟩
      (fun h => hirr.not_isUnit (Ideal.span_singleton_eq_top.1 h)) Function.injective_id
      _ y' z z' hz hz' ?_ ?_ c5 hd
    · rw [Category.assoc, c1, ← Category.assoc, hev]
    · rw [hid, Category.id_comp, hs]

end GlobalTheory.LN.ArcClause
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcFamilyFourthConditionInvertiblePushforwardStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arcFamily_fourthCondition_invertible_pushforward : DVR.TwistBaseChangeStatement → Laws → Laws2 → Laws3 → Laws4 → Laws5 → Laws6 → Ega → USt → PelSt → HomExtSt → ArcFamSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (p : ℕ), Y.LevelStructureConditions p → Amp Y → Y.N4 := by
  first | exact @GlobalTheory.LN.ArcClause.arc_clause | exact GlobalTheory.LN.ArcClause.arc_clause | (intros; apply GlobalTheory.LN.ArcClause.arc_clause <;> assumption)
end
