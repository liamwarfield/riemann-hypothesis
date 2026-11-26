module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompactNormalNoetherianOfFlagCellCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.MemRangeOfForallHeightOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasFibrewiseNonvanishingThetaSectionOfSmoothMode
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftShearMapSquareZeroAbelianSchemes

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtensionOverNormalQuasiProjectiveBase
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtensionOverNormalQuasiProjectiveBase
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.ExtendNormal

theorem isDominant_fst {P Y₀ Y : Scheme.{0}} (p : P ⟶ Y) (i : Y₀ ⟶ Y) [IsOpenImmersion p] [IsDominant i] :
    IsDominant (pullback.fst p i) := by
  refine ⟨?_⟩
  rw [DenseRange, Scheme.Pullback.range_fst]
  exact i.denseRange.preimage p.isOpenEmbedding.isOpenMap

theorem glue {Y₀ Y X : Scheme.{0}} (i : Y₀ ⟶ Y) (t₀ : Y₀ ⟶ X) [IsDominant i] [IsReduced Y] [X.IsSeparated]
    (h : ∀ y : Y, ∃ (U : Y.Opens) (_ : y ∈ U) (t : U.toScheme ⟶ X),
      ∀ (T : Scheme.{0}) (a : T ⟶ U.toScheme) (b : T ⟶ Y₀), a ≫ U.ι = b ≫ i → a ≫ t = b ≫ t₀) :
    ∃ t : Y ⟶ X, i ≫ t = t₀ := by
  choose U hy t ht using h
  have hU : TopologicalSpace.IsOpenCover U := by
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    intro y _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hy y⟩
  let 𝒰 := Y.openCoverOfIsOpenCover U hU
  have hc : ∀ x y, pullback.fst (𝒰.f x) (𝒰.f y) ≫ t x = pullback.snd (𝒰.f x) (𝒰.f y) ≫ t y := by
    intro x y
    change pullback.fst (U x).ι (U y).ι ≫ t x = pullback.snd (U x).ι (U y).ι ≫ t y
    let p := pullback.fst (U x).ι (U y).ι ≫ (U x).ι
    have : IsReduced (pullback (U x).ι (U y).ι) := isReduced_of_isOpenImmersion p
    have := isDominant_fst p i
    refine ext_of_isDominant (pullback.fst p i) ?_
    rw [← Category.assoc, ← Category.assoc, ht x _ _ (pullback.snd p i), ht y _ _ (pullback.snd p i)]
    · rw [Category.assoc, ← pullback.condition]
      exact pullback.condition
    · rw [Category.assoc]
      exact pullback.condition
  refine ⟨𝒰.glueMorphisms t hc, ?_⟩
  refine Scheme.Cover.hom_ext (𝒰.pullback₁ i) _ _ fun y => ?_
  have e := 𝒰.ι_glueMorphisms t hc y
  change pullback.fst i (𝒰.f y) ≫ _ = pullback.fst i (𝒰.f y) ≫ _
  rw [pullback.condition_assoc, e]
  exact ht y _ _ _ pullback.condition.symm

theorem exists_eq_fromSpec {X : Scheme.{0}} {W : X.Opens} (hW : IsAffineOpen W) (A : CommRingCat.{0})
    (z : Spec A ⟶ X) (hz : ∀ p, z p ∈ W) : ∃ ψ : Γ(X, W) ⟶ A, Spec.map ψ ≫ hW.fromSpec = z := by
  have hr : Set.range z ⊆ Set.range hW.fromSpec := by
    rw [hW.range_fromSpec]
    rintro _ ⟨p, rfl⟩
    exact hz p
  exact ⟨Spec.preimage (IsOpenImmersion.lift hW.fromSpec z hr), by
    rw [Spec.map_preimage, IsOpenImmersion.lift_fac]⟩

theorem exists_extension_local {X : Scheme.{0}} {W : X.Opens} (hW : IsAffineOpen W) (O K : Type) [CommRing O]
    [IsDomain O] [IsLocalRing O] [IsNoetherianRing O] [IsIntegrallyClosed O] [Field K] [Algebra O K]
    [IsFractionRing O K] (x : Sp K ⟶ X)
    (h : ∀ (V : ValuationSubring K) [IsDiscreteValuationRing V] (hV : ∀ r, algebraMap O K r ∈ V),
      IsLocalHom ((algebraMap O K).codRestrict V hV) →
      ∃ z : Sp V ⟶ X, spMap (algebraMap V K) ≫ z = x ∧ z (IsLocalRing.closedPoint V) ∈ W) :
    ∃ g : Sp O ⟶ X, spMap (algebraMap O K) ≫ g = x := by
  have h' : ∀ (V : ValuationSubring K), IsDiscreteValuationRing V →
      LocalSubring.range (algebraMap O K) ≤ V.toLocalSubring →
      ∃ ψ : Γ(X, W) ⟶ CommRingCat.of V, Spec.map (ψ ≫ CommRingCat.ofHom (algebraMap V K)) ≫ hW.fromSpec = x := by
    intro V hV hle
    obtain ⟨h1, h2⟩ := (localSubring_range_le_valuationSubring_iff_isLocalHom _ _).mp hle
    obtain ⟨z, hz, hzW⟩ := h V h1 h2
    obtain ⟨ψ, rfl⟩ := exists_eq_fromSpec hW _ z fun p =>
      ((IsLocalRing.specializes_closedPoint p).map z.continuous).mem_open W.isOpen hzW
    exact ⟨ψ, by rw [Spec.map_comp, Category.assoc, ← hz]⟩
  by_cases hO : IsField O
  · have hb : Function.Bijective (algebraMap O K) :=
      ⟨IsFractionRing.injective O K, IsFractionRing.surjective_iff_isField.mpr hO⟩
    have : IsIso (CommRingCat.ofHom (algebraMap O K)) := (ConcreteCategory.isIso_iff_bijective _).mpr hb
    exact ⟨inv (spMap (algebraMap O K)) ≫ x, IsIso.hom_inv_id_assoc _ _⟩
  obtain ⟨V₀, hV₀, hle₀⟩ := exists_discreteValuationSubring_dominating O K K hO
  obtain ⟨ψ₀, hψ₀⟩ := h' V₀ hV₀ hle₀
  set φ := ψ₀ ≫ CommRingCat.ofHom (algebraMap V₀ K) with hφ
  have hmem : ∀ b, φ.hom b ∈ (algebraMap O K).range := by
    intro b
    rw [range_algebraMap_eq_iInf_discreteValuationSubring, Subring.mem_iInf]
    rintro ⟨V, h1, h2⟩
    obtain ⟨ψ, hψ⟩ := h' V h1 h2
    rw [← hψ₀, cancel_mono] at hψ
    rw [← Spec.map_injective hψ]
    exact (ψ.hom b).2
  let e : O ≃+* (algebraMap O K).range :=
    RingEquiv.ofBijective (algebraMap O K).rangeRestrict
      ⟨fun a b hab => IsFractionRing.injective O K (congrArg Subtype.val hab),
        (algebraMap O K).rangeRestrict_surjective⟩
  let φ' : Γ(X, W) →+* O := e.symm.toRingHom.comp (φ.hom.codRestrict _ hmem)
  refine ⟨Spec.map (CommRingCat.ofHom φ') ≫ hW.fromSpec, ?_⟩
  rw [← hψ₀, ← Spec.map_comp_assoc]
  congr 2
  ext b
  exact congrArg Subtype.val (e.apply_symm_apply ⟨φ.hom b, hmem b⟩)

theorem isDominant_spMap (O K : Type) [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K] :
    IsDominant (spMap (algebraMap O K)) := by
  refine ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr ?_⟩
  exact ((RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective O K)).le.trans bot_le

theorem exists_nhds_specializes {Y : Scheme.{0}} [IsLocallyNoetherian Y] (y : Y) [IsDomain (Y.presheaf.stalk y)]
    (V : Y.Opens) (hy : y ∈ V) :
    ∃ U : Y.Opens, y ∈ U ∧ U ≤ V ∧
      ∀ u ∈ U, Y.fromSpecStalk y (⊥ : PrimeSpectrum (Y.presheaf.stalk y)) ⤳ u := by
  obtain ⟨U, hyU, hU, hUV, hinj⟩ := Y.exists_le_and_germ_injective y V hy
  have : IsDomain Γ(Y, U) := hinj.isDomain _
  refine ⟨U, hyU, hUV, fun u hu => ?_⟩
  have key : ∀ v ∈ U, hU.fromSpec (⊥ : PrimeSpectrum Γ(Y, U)) ⤳ v := by
    intro v hv
    obtain ⟨q, rfl⟩ : v ∈ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; exact hv
    exact ((PrimeSpectrum.le_iff_specializes ⊥ q).mp bot_le).map hU.fromSpec.continuous
  obtain ⟨q, hq⟩ : hU.fromSpec (⊥ : PrimeSpectrum Γ(Y, U)) ∈ Set.range (Y.fromSpecStalk y) := by
    rw [Scheme.range_fromSpecStalk]; exact key y hyU
  refine Specializes.trans ?_ (key u hu)
  rw [← hq]
  exact ((PrimeSpectrum.le_iff_specializes ⊥ q).mp bot_le).map (Y.fromSpecStalk y).continuous

theorem spMap_apply_eq_bot (O K : Type) [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
    (p : Sp K) : spMap (algebraMap O K) p = (⊥ : PrimeSpectrum O) := by
  refine PrimeSpectrum.ext ?_
  change Ideal.comap (algebraMap O K) p.asIdeal = ⊥
  have hp : Ideal.IsPrime (α := K) p.asIdeal := p.isPrime
  rw [Ideal.eq_bot_of_prime (K := K) p.asIdeal]
  exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective O K)

theorem exists_extension_nhds {R : Type} [CommRing R] {Y₀ Y X : Scheme.{0}} (i : Y₀ ⟶ Y) (σ : Y ⟶ Sp R)
    (τ : X ⟶ Sp R) (t₀ : Y₀ ⟶ X) [IsOpenImmersion i] [IsDominant i] [IsLocallyNoetherian Y] [IsReduced Y]
    [X.IsSeparated] [LocallyOfFiniteType τ] (hc : i ≫ σ = t₀ ≫ τ) (y : Y) [IsDomain (Y.presheaf.stalk y)]
    [IsIntegrallyClosed (Y.presheaf.stalk y)] {W : X.Opens} (hW : IsAffineOpen W)
    (h : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
      [IsFractionRing V K] (y' : Sp V ⟶ Y) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ i →
      y' (IsLocalRing.closedPoint V) = y →
      ∃ z : Sp V ⟶ X, spMap (algebraMap V K) ≫ z = x ≫ t₀ ∧ z (IsLocalRing.closedPoint V) ∈ W) :
    ∃ (U : Y.Opens) (_ : y ∈ U) (t : U.toScheme ⟶ X),
      ∀ (T : Scheme.{0}) (a : T ⟶ U.toScheme) (b : T ⟶ Y₀), a ≫ U.ι = b ≫ i → a ≫ t = b ≫ t₀ := by
  let O : Type := Y.presheaf.stalk y
  let K : Type := FractionRing O
  let j : Sp K ⟶ Spec (Y.presheaf.stalk y) := spMap (algebraMap O K)
  have hjd : IsDominant j := isDominant_spMap O K
  let ξ : Y := Y.fromSpecStalk y (⊥ : PrimeSpectrum (Y.presheaf.stalk y))
  have hgen : ∀ p, (j ≫ Y.fromSpecStalk y) p = ξ := fun p =>
    (Scheme.Hom.comp_apply _ _ _).trans (congrArg (Y.fromSpecStalk y) (spMap_apply_eq_bot O K p))
  have hgi : ξ ∈ Set.range i := by
    obtain ⟨U, hyU, -, hU⟩ := exists_nhds_specializes y ⊤ trivial
    obtain ⟨u, hu⟩ := i.denseRange.exists_mem_open U.isOpen ⟨y, hyU⟩
    exact (hU _ hu).mem_open i.isOpenEmbedding.isOpen_range ⟨u, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : Sp K ⟶ Y₀, x ≫ i = j ≫ Y.fromSpecStalk y :=
    ⟨_, IsOpenImmersion.lift_fac i (j ≫ Y.fromSpecStalk y) (by rintro _ ⟨p, rfl⟩; rw [hgen]; exact hgi)⟩
  obtain ⟨g, hg⟩ : ∃ g : Spec (Y.presheaf.stalk y) ⟶ X, j ≫ g = x ≫ t₀ := by
    refine exists_extension_local hW O K (x ≫ t₀) fun V _ hV hloc => ?_
    let k : Sp V ⟶ Spec (Y.presheaf.stalk y) := spMap ((algebraMap O K).codRestrict V hV)
    refine h V K (k ≫ Y.fromSpecStalk y) x ?_ ?_
    · rw [hx, ← Category.assoc]
      congr 1
      exact (Spec.map_comp _ _).symm
    · refine (Scheme.Hom.comp_apply _ _ _).trans
        (Eq.trans (congrArg (Y.fromSpecStalk y) ?_) (Scheme.fromSpecStalk_closedPoint (x := y)))
      exact IsLocalRing.comap_closedPoint ((algebraMap O K).codRestrict V hV)
  have hgτ : g ≫ τ = Y.fromSpecStalk y ≫ σ := by
    refine ext_of_isDominant j ?_
    rw [reassoc_of% hg, ← reassoc_of% hx, hc]
  obtain ⟨U₁, hy₁, t₁, ht₁, -⟩ := spread_out_of_isGermInjective' σ τ g hgτ
  obtain ⟨U, hyU, hle, hU⟩ := exists_nhds_specializes y U₁ hy₁
  refine ⟨U, hyU, Y.homOfLE hle ≫ t₁, fun T a b hab => ?_⟩
  have hw : (j ≫ U.fromSpecStalkOfMem y hyU) ≫ U.ι = x ≫ i := by simp [hx]
  let w : Sp K ⟶ pullback U.ι i := pullback.lift _ _ hw
  let p : pullback U.ι i ⟶ Y := pullback.fst U.ι i ≫ U.ι
  have hwp : w ≫ p = j ≫ Y.fromSpecStalk y := by
    rw [← hx, ← hw]
    exact pullback.lift_fst_assoc _ _ hw _
  have : IsReduced (pullback U.ι i) := isReduced_of_isOpenImmersion p
  have : IsDominant w := by
    refine ⟨fun q => ?_⟩
    have h1 : w (IsLocalRing.closedPoint K) ⤳ q := by
      have h0 : p (w (IsLocalRing.closedPoint K)) = ξ :=
        (Scheme.Hom.comp_apply w p _).symm.trans (by rw [hwp]; exact hgen _)
      rw [← p.isOpenEmbedding.isInducing.specializes_iff, h0]
      exact hU _ (pullback.fst U.ι i q).2
    exact h1.mem_closed isClosed_closure (subset_closure ⟨_, rfl⟩)
  have e : pullback.fst U.ι i ≫ Y.homOfLE hle ≫ t₁ = pullback.snd U.ι i ≫ t₀ := by
    refine ext_of_isDominant w ?_
    have h2 : U.fromSpecStalkOfMem y hyU ≫ Y.homOfLE hle = U₁.fromSpecStalkOfMem y hy₁ := by
      rw [← cancel_mono U₁.ι]; simp
    simp only [w, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.assoc]
    rw [reassoc_of% h2, ← ht₁, hg]
  rw [← pullback.lift_fst a b hab, Category.assoc, e, pullback.lift_snd_assoc]

theorem exists_extension : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Y₀ Y X : Scheme.{0}) (i : Y₀ ⟶ Y) (σ : Y ⟶ Sp R) (τ : X ⟶ Sp R) (t₀ : Y₀ ⟶ X), IsOpenImmersion i → IsDominant i → IsLocallyNoetherian Y → IsReduced Y → (∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) → IsQProjOver τ → i ≫ σ = t₀ ≫ τ → (∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (y : Sp V ⟶ Y) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y = x ≫ i → ∃ z : Sp V ⟶ X, spMap (algebraMap V K) ≫ z = x ≫ t₀) → (∀ y : Y, {z : X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' : Sp V ⟶ Y) (z' : Sp V ⟶ X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ i ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧ y' (IsLocalRing.closedPoint V) = y ∧ z' (IsLocalRing.closedPoint V) = z}.Finite) → ∃ t : Y ⟶ X, i ≫ t = t₀ ∧ t ≫ τ = σ := by
  intro R _ _ Y₀ Y X i σ τ t₀ hi hd hY hred hint hq hc hval hqf
  obtain ⟨hsep, hlft, -⟩ := GlobalTheory.ZM.isSeparated_finiteType_of_isQProjOver hq
  have hfin := GlobalTheory.FiniteSubsetsInAffineOpens.of_isQProjOver hq
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from τ]; infer_instance⟩
  obtain ⟨t, ht⟩ := glue i t₀ fun y => by
    have := hint y
    have : IsDomain (Y.presheaf.stalk y) := GlobalTheory.isDomain_of_isIntegrallyClosed_of_isReduced _ (hint y)
    obtain ⟨W, hW, hSW⟩ := hfin.exists_isAffineOpen _ (hqf y)
    exact exists_extension_nhds i σ τ t₀ hc y hW fun V K _ _ _ _ _ _ y' x hx hy => by
      obtain ⟨z, hz⟩ := hval V K y' x hx
      exact ⟨z, hz, hSW ⟨V, K, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
        inferInstance, y', z, x, hx, hz, hy, rfl⟩⟩
  refine ⟨t, ht, ext_of_isDominant i ?_⟩
  rw [reassoc_of% ht, hc]

end GlobalTheory.ExtendNormal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtensionOverNormalQuasiProjectiveBaseStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extension_over_normal_quasi_projective_base : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Y₀ Y X : Scheme.{0}) (i : Y₀ ⟶ Y) (σ : Y ⟶ Sp R) (τ : X ⟶ Sp R) (t₀ : Y₀ ⟶ X), IsOpenImmersion i → IsDominant i → IsLocallyNoetherian Y → IsReduced Y → (∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) → IsQProjOver τ → i ≫ σ = t₀ ≫ τ → (∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (y : Sp V ⟶ Y) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y = x ≫ i → ∃ z : Sp V ⟶ X, spMap (algebraMap V K) ≫ z = x ≫ t₀) → (∀ y : Y, {z : X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' : Sp V ⟶ Y) (z' : Sp V ⟶ X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ i ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧ y' (IsLocalRing.closedPoint V) = y ∧ z' (IsLocalRing.closedPoint V) = z}.Finite) → ∃ t : Y ⟶ X, i ≫ t = t₀ ∧ t ≫ τ = σ := by
  first | (exact @GlobalTheory.ExtendNormal.exists_extension) | (exact GlobalTheory.ExtendNormal.exists_extension) | (intros; apply GlobalTheory.ExtendNormal.exists_extension  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEffCartierOfOrders
open AlgebraicGeometry CategoryTheory Limits IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor

namespace GlobalTheory.Poinc.TraitGlue

theorem dvd_of_height_one {A : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] {a b : A}
    (ha : a ≠ 0) (h : ∀ (P : Ideal A) [P.IsPrime], P.height = 1 →
      algebraMap A (Localization.AtPrime P) a ∣ algebraMap A (Localization.AtPrime P) b) : a ∣ b := by
  have ha' : algebraMap A (FractionRing A) a ≠ 0 := fun e =>
    ha (IsFractionRing.injective A (FractionRing A) (e.trans (map_zero _).symm))
  obtain ⟨c, hc⟩ := KrullAlg.mem_range_of_forall_height_one (A := A)
    (algebraMap A (FractionRing A) b / algebraMap A (FractionRing A) a) (fun P hP h1 => by
      obtain ⟨c, hc⟩ := h P h1
      obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl c
      have e : algebraMap A (Localization.AtPrime P) (s * b) = algebraMap A (Localization.AtPrime P) (a * r) := by
        rw [map_mul, map_mul, hc, mul_left_comm, IsLocalization.mk'_spec']
      have e' : s * b = a * r := IsLocalization.injective _ P.primeCompl_le_nonZeroDivisors e
      refine ⟨s, s.2, r, ?_⟩
      rw [← mul_div_assoc, ← map_mul, e', map_mul, mul_div_cancel_left₀ _ ha'])
  refine ⟨c, IsFractionRing.injective A (FractionRing A) ?_⟩
  rw [map_mul, hc, mul_div_cancel₀ _ ha']

theorem dvd_of_generisations {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (hX : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) (x : X)
    {a b : X.presheaf.stalk x} (ha : a ≠ 0)
    (h : ∀ (η : X) (hη : η ⤳ x), ringKrullDim (X.presheaf.stalk η) = 1 →
      (X.presheaf.stalkSpecializes hη).hom a ∣ (X.presheaf.stalkSpecializes hη).hom b) : a ∣ b := by
  have := (hX x).2
  refine dvd_of_height_one ha fun q _ hq => ?_
  let y : PrimeSpectrum (X.presheaf.stalk x) := ⟨q, inferInstance⟩
  obtain ⟨e, he⟩ := LocalRingGeneralisation.stalk_fromSpecStalk_equiv X x q
  have hs : X.fromSpecStalk x y ⤳ x := by
    have : X.fromSpecStalk x y ∈ Set.range (X.fromSpecStalk x) := ⟨y, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  have hcomp : ∀ t, e ((X.presheaf.stalkSpecializes hs).hom t) = algebraMap _ (Localization.AtPrime q) t := by
    intro t
    obtain ⟨U, hxU, s, rfl⟩ := X.presheaf.exists_germ_eq t
    have h3 := congrArg (fun f => f.hom s) (TopCat.Presheaf.germ_stalkSpecializes X.presheaf hxU hs)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h3
    erw [h3]
    exact he U _ hxU s
  rw [← hcomp, ← hcomp]
  refine map_dvd e (h _ hs ?_)
  rw [ringKrullDim_eq_of_ringEquiv e, IsLocalization.AtPrime.ringKrullDim_eq_height q, hq]
  rfl

theorem finite_dim_one {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] {W : X.Opens} (hW : IsAffineOpen W)
    (V : X.Opens) {z : X} (hzW : z ∈ W) (hzV : z ∈ V) :
    {η : X | η ∈ W ∧ ringKrullDim (X.presheaf.stalk η) = 1 ∧ η ∉ V}.Finite := by
  obtain ⟨a, haV, hza⟩ := hW.exists_basicOpen_le ⟨z, hzV⟩ hzW
  have : Nonempty W := ⟨⟨z, hzW⟩⟩
  have : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  have ha : a ≠ 0 := by
    rintro rfl
    simp at hza
  have hfin := (KrullAlg.finite_height_one ha).preimage
    (f := fun p : PrimeSpectrum Γ(X, W) => p.asIdeal) (fun _ _ _ _ e => PrimeSpectrum.ext e)
  refine (hfin.image (fun p => hW.fromSpec p)).subset ?_
  rintro η ⟨h1, h2, h3⟩
  letI : Algebra Γ(X, W) (X.presheaf.stalk η) := X.presheaf.algebra_section_stalk ⟨η, h1⟩
  haveI := hW.isLocalization_stalk ⟨η, h1⟩
  refine ⟨hW.primeIdealOf ⟨η, h1⟩, ⟨inferInstance, ?_, ?_⟩, hW.fromSpec_primeIdealOf ⟨η, h1⟩⟩
  · rw [IsLocalization.AtPrime.ringKrullDim_eq_height (hW.primeIdealOf ⟨η, h1⟩).asIdeal] at h2
    exact_mod_cast h2
  · by_contra hn
    refine h3 (haV ((X.mem_basicOpen a η h1).2 ?_))
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk η) (hW.primeIdealOf ⟨η, h1⟩).asIdeal a).2 hn

theorem associated_of_map {A V : Type} [CommRing A] [IsDomain A] [ValuationRing A] [CommRing V] [IsDomain V]
    (φ : A →+* V) [IsLocalHom φ] {a b : A} (h : Associated (φ a) (φ b)) (ha : φ a ≠ 0) : Associated a b := by
  have key : ∀ {a c : A}, Associated (φ a) (φ (a * c)) → φ a ≠ 0 → Associated a (a * c) := by
    intro a c h ha
    rw [map_mul] at h
    have : IsUnit (φ c) := isUnit_of_associated_mul h.symm ha
    exact (associated_mul_unit_left _ _ (isUnit_of_map_unit φ c this)).symm
  rcases ValuationRing.dvd_total a b with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · exact key h ha
  · exact (key h.symm (h.ne_zero_iff.1 ha)).symm

theorem valuationRing_stalk {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (hX : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) (η : X)
    (h : ringKrullDim (X.presheaf.stalk η) = 1) : ValuationRing (X.presheaf.stalk η) := by
  have := (hX η).2
  have hle : Ring.KrullDimLE 1 (X.presheaf.stalk η) := by
    rw [Ring.krullDimLE_iff, h]
    norm_num
  have : Ring.DimensionLEOne (X.presheaf.stalk η) := by
    refine ⟨fun {p} hp hprime => ?_⟩
    rcases Ring.krullDimLE_one_iff.mp hle p hprime with h | h
    · rw [IsDomain.minimalPrimes_eq_singleton_bot] at h
      exact absurd h hp
    · exact h
  have : IsDedekindDomain (X.presheaf.stalk η) :=
    (isDedekindDomain_iff _ (FractionRing (X.presheaf.stalk η))).mpr
      ⟨inferInstance, inferInstance, inferInstance, fun {y} hy => IsIntegrallyClosed.isIntegral_iff.mp hy⟩
  have h2 := (tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (X.presheaf.stalk η)).out 3 2
  exact h2.1 this

theorem specializes_germ {X : Scheme.{0}} {W : X.Opens} {x η : X} (h : η ⤳ x) (hx : x ∈ W) (hη : η ∈ W) (s : Γ(X, W)) :
    (X.presheaf.stalkSpecializes h).hom ((X.presheaf.germ W x hx).hom s) = (X.presheaf.germ W η hη).hom s :=
  congrArg (fun f => f.hom s) (TopCat.Presheaf.germ_stalkSpecializes X.presheaf hx h)

theorem exists_spread {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] (U : X.Opens)
    (f : ∀ x : X, X.presheaf.stalk x) (hU : ∀ η ∈ U, ringKrullDim (X.presheaf.stalk η) = 1 → IsUnit (f η))
    (hne : ∀ η : X, ringKrullDim (X.presheaf.stalk η) = 1 → genericPoint X ∈ U) (x : X) (h0 : f x ≠ 0)
    (hc : ∀ (η : X) (h : η ⤳ x), ringKrullDim (X.presheaf.stalk η) = 1 →
      Associated ((X.presheaf.stalkSpecializes h).hom (f x)) (f η)) :
    ∃ (W : X.Opens) (hx : x ∈ W) (s : Γ(X, W)), (X.presheaf.germ W x hx).hom s = f x ∧
      ∀ (η : X) (hη : η ∈ W), ringKrullDim (X.presheaf.stalk η) = 1 →
        Associated ((X.presheaf.germ W η hη).hom s) (f η) := by
  obtain ⟨W₀, hx₀, s₀, hs₀⟩ := X.presheaf.exists_germ_eq (f x)
  obtain ⟨⟨W, hW⟩, hx, hle⟩ := EffCartierData.exists_affine_le hx₀
  let s : Γ(X, W) := resG X hle s₀
  have hs : (X.presheaf.germ W x hx).hom s = f x := (Cartier.germ_resG hle _ hx _).trans hs₀
  let B : Set X := {η | ∃ hη : η ∈ W, ringKrullDim (X.presheaf.stalk η) = 1 ∧
    ¬ Associated ((X.presheaf.germ W η hη).hom s) (f η)}
  have hgen : ∀ {V : X.Opens} {y : X}, y ∈ V → genericPoint X ∈ V := fun {V y} hy =>
    ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr ⟨y, trivial, hy⟩
  have hB : B.Finite := by
    rcases B.eq_empty_or_nonempty with h | ⟨η₀, -, h₀, -⟩
    · rw [h]; exact Set.finite_empty
    have hs0 : s ≠ 0 := fun e => h0 (by rw [← hs, e, map_zero])
    have hb : genericPoint X ∈ X.basicOpen s := by
      rw [X.mem_basicOpen s _ (hgen hx)]
      have : (X.presheaf.germ W _ (hgen hx)).hom s ≠ 0 := fun e =>
        hs0 (germ_injective_of_isIntegral X _ (hgen hx) (e.trans (map_zero _).symm))
      exact (IsUnit.mk0 (G₀ := X.functionField) _ this)
    refine (finite_dim_one hW (U ⊓ X.basicOpen s) (hgen hx) ⟨hne η₀ h₀, hb⟩).subset ?_
    rintro η ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun h4 => h3 ?_⟩
    exact (associated_one_iff_isUnit.2 ((X.mem_basicOpen s η h1).1 h4.2)).trans
      (associated_one_iff_isUnit.2 (hU η h4.1 h2)).symm
  have hcl : IsClosed (⋃ η ∈ B, closure ({η} : Set X)) := hB.isClosed_biUnion fun _ _ => isClosed_closure
  let W' : X.Opens := W ⊓ ⟨_, hcl.isOpen_compl⟩
  have hx' : x ∈ W' := by
    refine ⟨hx, fun hm => ?_⟩
    obtain ⟨η, ⟨h1, h2, h3⟩, h4⟩ := Set.mem_iUnion₂.1 hm
    have h5 : η ⤳ x := specializes_iff_mem_closure.2 h4
    refine h3 ?_
    rw [← specializes_germ h5 hx h1, hs]
    exact hc η h5 h2
  refine ⟨W', hx', resG X inf_le_left s, (Cartier.germ_resG _ _ hx' _).trans hs, fun η hη h1 => ?_⟩
  rw [Cartier.germ_resG]
  by_contra hn
  exact hη.2 (Set.mem_iUnion₂.2 ⟨η, ⟨hη.1, h1, hn⟩, subset_closure rfl⟩)

theorem exists_of_germs {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (hX : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) (U : X.Opens)
    (f : ∀ x : X, X.presheaf.stalk x) (hU : ∀ η ∈ U, ringKrullDim (X.presheaf.stalk η) = 1 → IsUnit (f η))
    (hne : ∀ η : X, ringKrullDim (X.presheaf.stalk η) = 1 → genericPoint X ∈ U) (h0 : ∀ x, f x ≠ 0)
    (hc : ∀ (x η : X) (h : η ⤳ x), ringKrullDim (X.presheaf.stalk η) = 1 →
      Associated ((X.presheaf.stalkSpecializes h).hom (f x)) (f η)) :
    ∃ D : EffCartierData X, (∀ x ∈ D.idealSheaf.support, x ∉ U) ∧
      ∀ x, FinalTheorems.stalkId D.idealSheaf x = Ideal.span {f x} := by
  choose W hx s hs hW using fun x => exists_spread U f hU hne x (h0 x) (hc x)
  have hs0 : ∀ x, s x ≠ 0 := fun x e => h0 x (by rw [← hs x, e, map_zero])
  have hreg : ∀ x, Cartier.IsRegularFn (s x) := fun x => Cartier.isRegularFn_of_ne_zero (hs0 x)
  have hdvd : ∀ (i j y : X) (hi : y ∈ W i) (hj : y ∈ W j),
      (X.presheaf.germ _ y hi).hom (s i) ∣ (X.presheaf.germ _ y hj).hom (s j) := by
    intro i j y hi hj
    refine dvd_of_generisations hX y (fun e =>
      hs0 i (germ_injective_of_isIntegral X _ hi (e.trans (map_zero _).symm))) fun η hη h1 => ?_
    have hi' : η ∈ W i := hη.mem_open (W i).isOpen hi
    have hj' : η ∈ W j := hη.mem_open (W j).isOpen hj
    rw [specializes_germ hη hi hi', specializes_germ hη hj hj']
    exact ((hW i η hi' h1).trans (hW j η hj' h1).symm).dvd
  let D : EffCartierData X :=
    { ι := X
      U := W
      f := s
      cover := eq_top_iff.2 fun x _ => Opens.mem_iSup.2 ⟨x, hx x⟩
      regular := hreg
      assoc := fun i j => ((hreg i).resG _).associated_of_germ ((hreg j).resG _) fun y hy => by
        rw [Cartier.germ_resG, Cartier.germ_resG]
        exact le_antisymm (Ideal.span_singleton_le_span_singleton.2 (hdvd j i y hy.2 hy.1))
          (Ideal.span_singleton_le_span_singleton.2 (hdvd i j y hy.1 hy.2)) }
  refine ⟨D, fun x hxD hxU => ?_, fun x => (D.stalkId_idealSheaf x x (hx x)).trans (congrArg (fun t => Ideal.span {t}) (hs x))⟩
  refine (D.mem_support_iff x (hx x)).1 hxD ((X.mem_basicOpen (s x) x (hx x)).2 ?_)
  change IsUnit ((X.presheaf.germ _ x (hx x)).hom (s x))
  rw [hs x]
  refine isUnit_of_dvd_one (dvd_of_generisations hX x (h0 x) fun η hη h1 => ?_)
  exact ((hc x η hη h1).symm.isUnit (hU η (hη.mem_open U.isOpen hxU) h1)).dvd

theorem exists_effCartier_of_orders : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → ∀ (U : X.Opens) (R : ATrait X → ℕ → Prop), (∀ (T : ATrait X) (a : ℕ), Set.range T.ξ ⊆ U → R T a → a = 0) → (∀ η : X, ringKrullDim (X.presheaf.stalk η) = 1 → ∃ (T : ATrait X) (a e : ℕ), T.CentredAt η e ∧ T.GenIn U ∧ R T a) → (∀ x : X, ∃ f : X.presheaf.stalk x, ∀ (T : ATrait X) (h : T.ξ (closedPoint T.V) ⤳ x) (a : ℕ), T.GenIn U → R T a → T.HasOrd h f a) → ∃ D : EffCartierData X, (∀ x ∈ D.idealSheaf.support, x ∉ U) ∧ ∀ (T : ATrait X) (a : ℕ), T.GenIn U → R T a → idlAlong D.idealSheaf T.ξ = Ideal.span {T.ϖ ^ a} := by
  intro X _ _ hX U R hR hT hf
  have hf' : ∀ x : X, ∃ f : X.presheaf.stalk x, f ≠ 0 ∧ ∀ (T : ATrait X) (h : T.ξ (closedPoint T.V) ⤳ x) (a : ℕ),
      T.GenIn U → R T a → T.HasOrd h f a := by
    intro x
    obtain ⟨f, hf⟩ := hf x
    by_cases h0 : f = 0
    · refine ⟨1, one_ne_zero, fun T h a h1 h2 => ?_⟩
      have := hf T h a h1 h2
      rw [h0, ATrait.HasOrd, map_zero, map_zero, Ideal.span_singleton_eq_span_singleton] at this
      exact absurd (this.eq_zero_iff.1 rfl) (pow_ne_zero _ T.irr.ne_zero)
    · exact ⟨f, h0, hf⟩
  choose f h0 hf using hf'
  have hself : ∀ (T : ATrait X) (a : ℕ), T.GenIn U → R T a →
      Ideal.span {(Scheme.stalkClosedPointTo T.ξ).hom (f _)} = Ideal.span {T.ϖ ^ a} := by
    intro T a h1 h2
    have := hf _ T specializes_rfl a h1 h2
    rwa [ATrait.HasOrd, TopCat.Presheaf.stalkSpecializes_refl, CommRingCat.hom_id, RingHom.id_apply] at this
  obtain ⟨D, hD, hD'⟩ := exists_of_germs hX U f (fun η hη h1 => by
      obtain ⟨T, a, e, ⟨rfl, -⟩, h2, h3⟩ := hT η h1
      have ha : a = 0 := hR T a (by
        rintro _ ⟨p, rfl⟩
        exact ((IsLocalRing.specializes_closedPoint p).map T.ξ.continuous).mem_open U.isOpen hη) h3
      have := hself T a h2 h3
      rw [ha, pow_zero, Ideal.span_singleton_one, Ideal.span_singleton_eq_top] at this
      exact isUnit_of_map_unit _ _ this)
    (fun η h1 => by
      obtain ⟨T, a, e, -, h2, -⟩ := hT η h1
      obtain ⟨p⟩ : Nonempty (Sp (FractionRing T.V)) := inferInstanceAs (Nonempty (PrimeSpectrum _))
      exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr ⟨_, trivial, h2 ⟨p, rfl⟩⟩) h0
    (fun x η h h1 => by
      obtain ⟨T, a, e, ⟨rfl, -⟩, h2, h3⟩ := hT η h1
      have := valuationRing_stalk hX _ h1
      have e1 := Ideal.span_singleton_eq_span_singleton.1 (hf x T h a h2 h3)
      have e2 := Ideal.span_singleton_eq_span_singleton.1 (hself T a h2 h3)
      exact associated_of_map (Scheme.stalkClosedPointTo T.ξ).hom (e1.trans e2.symm)
        (e1.ne_zero_iff.2 (pow_ne_zero _ T.irr.ne_zero)))
  refine ⟨D, hD, fun T a h1 h2 => ?_⟩
  rw [idlAlong, hD', Ideal.map_span, Set.image_singleton]
  exact hself T a h1 h2

end GlobalTheory.Poinc.TraitGlue
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyValueHomogOfFibres
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyDatumFalseOfModelSectionZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyDatumFalseOfModelSectionZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.KeyEven

theorem not_keyOn_of_sec_zero : ∀ (K : Type) [Field K] (G : Over (Sp K)) [GrpObj G] [IsCommMonObj G] (L : RigLB G)
    (σ : L.L.Sec) (x : KeyIn K) (y : Fin x.P.g → (epsR K ⟶ G)), KeyOn (RingHom.id K) x G L σ y →
    (∀ i, σ.f i = 0) → False := by
  intro K _ G _ _ L σ x y hK hσ
  obtain ⟨φ, -, ψ, -, -, -, -, hsec, -⟩ := hK
  obtain ⟨z, -, hz⟩ := x.th_ne (IsLocalRing.closedPoint K)
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
  have hzi : z ∈ x.P.L.U i := x.P.A.left.basicOpen_le _ hi
  have hc : φ z ∈ (⨆ a, L.L.U a) := by rw [L.isLB.cover]; trivial
  obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 hc
  let j : (L.L.pull φ).ι := fun _ => a
  have hzj : z ∈ (L.L.pull φ).U j := Set.mem_iInter.2 fun _ => ha
  have h : (L.L.pull φ).U j ⊓ x.P.L.U i ≤ φ ⁻¹ᵁ L.L.U (j PUnit.unit) :=
    inf_le_left.trans (LB.wchart_le L.L (fun _ => φ) j PUnit.unit)
  have e := hsec j i h
  rw [hσ, map_zero] at e
  have e0 : resG x.P.A.left (inf_le_right : (L.L.pull φ).U j ⊓ x.P.L.U i ≤ x.P.L.U i) (x.th.f i) = 0 := by
    have u := (ψ.s (j, i)).isUnit
    exact (u.mul_right_eq_zero).1 e.symm
  have hb : z ∈ x.P.A.left.basicOpen
      (resG x.P.A.left (inf_le_right : (L.L.pull φ).U j ⊓ x.P.L.U i ≤ x.P.L.U i) (x.th.f i)) := by
    rw [Scheme.basicOpen_res]
    exact ⟨⟨hzj, hzi⟩, hi⟩
  rw [e0, Scheme.basicOpen_zero] at hb
  exact hb

end GlobalTheory.KeyEven
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyDatumFalseOfModelSectionZeroStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.keyDatum_false_of_modelSection_zero : ∀ (K : Type) [Field K] (G : Over (Sp K)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (σ : L.L.Sec) (x : KeyIn K) (y : Fin x.P.g → (epsR K ⟶ G)), KeyOn (RingHom.id K) x G L σ y → (∀ i, σ.f i = 0) → False := by
  first | exact @GlobalTheory.KeyEven.not_keyOn_of_sec_zero | exact GlobalTheory.KeyEven.not_keyOn_of_sec_zero | (intros; apply GlobalTheory.KeyEven.not_keyOn_of_sec_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyDatumScaleSectionsByConstant
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyDatumScaleSectionsByConstant
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.KeyEven

theorem appLE_constFn {K : Type} [CommRing K] {X Y : Scheme.{0}} (p : X ⟶ Sp K) (q : Y ⟶ Sp K) (φ : X ⟶ Y)
    (hw : φ ≫ q = p) (V : Y.Opens) (W : X.Opens) (h : W ≤ φ ⁻¹ᵁ V) (a : K) :
    (φ.appLE V W h).hom (constFn q V a) = constFn p W a := by
  subst hw
  unfold constFn
  rw [← CommRingCat.comp_apply]
  congr 2
  exact Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _

theorem resG_constFn {K : Type} [CommRing K] {X : Scheme.{0}} (p : X ⟶ Sp K) {U V : X.Opens} (h : V ≤ U) (a : K) :
    resG X h (constFn p U a) = constFn p V a := by
  unfold constFn resG
  rw [← CommRingCat.comp_apply]
  congr 2
  exact Scheme.Hom.appLE_map _ _ _

theorem keyOn_scale (K : Type) [Field K] (G : Over (Sp K)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (σ σ' : L.L.Sec)
    (x : KeyIn K) (y : Fin x.P.g → (epsR K ⟶ G)) (a : K) (th : x.P.L.Sec)
    (hth : ∀ s : Sp K, ∃ z : x.P.A.left, x.P.A.hom z = s ∧ z ∈ nonzeroLocus th)
    (hth' : ∀ i, th.f i = constFn x.P.A.hom _ a * x.th.f i) (hσ : ∀ i, σ'.f i = constFn G.hom _ a * σ.f i)
    (hK : KeyOn (RingHom.id K) x G L σ y) :
    KeyOn (RingHom.id K) ⟨x.P, x.g_pos, x.rig, x.rig_gen, th, hth, x.v, x.basis⟩ G L σ' y := by
  obtain ⟨φ, he, ψ, F, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := hK
  have hw : φ ≫ G.hom = x.P.A.hom := by
    rw [h₁.1.w, show spMap (RingHom.id K) = 𝟙 (Sp K) from Spec.map_id _, Category.comp_id]
  refine ⟨φ, he, ψ, F, h₁, h₂, h₃, fun j i h => ?_, h₅, h₆, h₇⟩
  show (φ.appLE _ _ h).hom (σ'.f (j PUnit.unit)) = _ * resG _ inf_le_right (th.f i)
  rw [hσ, hth', map_mul, map_mul, h₄ j i h, appLE_constFn x.P.A.hom G.hom φ hw, resG_constFn, mul_left_comm]

end GlobalTheory.KeyEven

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyDatumScaleSectionsByConstantStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.keyDatum_scale_sections_by_constant : ∀ (K : Type) [Field K] (G : Over (Sp K)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (σ σ' : L.L.Sec) (x : KeyIn K) (y : Fin x.P.g → (epsR K ⟶ G)) (a : K) (th : x.P.L.Sec) (hth : ∀ s : Sp K, ∃ z : x.P.A.left, x.P.A.hom z = s ∧ z ∈ nonzeroLocus th), (∀ i, th.f i = constFn x.P.A.hom _ a * x.th.f i) → (∀ i, σ'.f i = constFn G.hom _ a * σ.f i) → KeyOn (RingHom.id K) x G L σ y → KeyOn (RingHom.id K) ⟨x.P, x.g_pos, x.rig, x.rig_gen, th, hth, x.v, x.basis⟩ G L σ' y := by
  first | exact @GlobalTheory.KeyEven.keyOn_scale | exact GlobalTheory.KeyEven.keyOn_scale | (intros; apply GlobalTheory.KeyEven.keyOn_scale <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieBasisLiftModelVectors
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieBasisLiftModelVectors
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieLift

theorem grpPullback_self {S : Scheme.{0}} (G : Over S) [GrpObj G] : IsGrpPullback G G (𝟙 S) (𝟙 G.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let ρ : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have ex : x₀ = ρ ≫ x := Over.OverMorphism.ext (hx.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  have ey : y₀ = ρ ≫ y := Over.OverMorphism.ext (hy.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  rw [ex, ey, ← MonObj.comp_mul]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

theorem isLieBasis_cast {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {n m : ℕ} (h : n = m)
    {w : Fin m → (epsR R ⟶ G)} (hw : IsLieBasis w) : IsLieBasis (fun j : Fin n => w (j.cast h)) := by
  subst h
  simpa using hw

theorem dual_eq_id {K : Type} [Field K] (F : DualNumber K →+* DualNumber K)
    (h₁ : ∀ a, F (algebraMap K _ a) = algebraMap K _ (RingHom.id K a)) (h₂ : F DualNumber.eps = DualNumber.eps) :
    F = RingHom.id _ := by
  let Fa : DualNumber K →ₐ[K] DualNumber K := { F with commutes' := h₁ }
  have : Fa = AlgHom.id K _ := DualNumber.algHom_ext h₂
  exact RingHom.ext fun z => congrArg (fun q : DualNumber K →ₐ[K] DualNumber K => q z) this

theorem main : ∀ (K : Type) [Field K] (G : Over (Sp K)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (σ σ' : L.L.Sec) (x x' : KeyIn K) (hg' : x'.P.g = x.P.g) (y y' : Fin x.P.g → (epsR K ⟶ G)) (M : Matrix (Fin x.P.g) (Fin x.P.g) K), KeyOn (RingHom.id K) x G L σ y → KeyOn (RingHom.id K) x' G L σ' (fun i => y' (i.cast hg')) → (∀ i, IsLieComb (M i) y (y' i)) → ∃ (v : Fin x.P.g → (epsR K ⟶ x.P.A)) (hv : IsLieBasis v), (∀ i, IsLieComb (M i) x.v (v i)) ∧ KeyOn (RingHom.id K) ⟨x.P, x.g_pos, x.rig, x.rig_gen, x.th, x.th_ne, v, hv⟩ G L σ y' := by
  intro K _ G _ _ L σ σ' x x' hg' y y' M hx hx' hM
  obtain ⟨φ, he, ψ, F, hφ, hψ, hmaps, hsec, hF₁, hF₂, hxv⟩ := hx
  obtain ⟨φ', -, -, F', hφ', -, -, -, hF₁', hF₂', hxv'⟩ := hx'
  have e : spMap (RingHom.id K) = 𝟙 (Sp K) := Spec.map_id _
  have e' : spMap (RingHom.id (DualNumber K)) = 𝟙 (Sp (DualNumber K)) := Spec.map_id _
  have hF := dual_eq_id F hF₁ hF₂
  have hF' := dual_eq_id F' hF₁' hF₂'
  subst hF hF'
  have eR : spMap (Chart.dualMapR (RingHom.id K)) = 𝟙 (Sp (DualNumber K)) := by
    refine Eq.trans (congrArg spMap (RingHom.ext fun z => ?_)) e'
    ext <;> simp [Chart.dualMapR]

  have hw : ∀ i, (y' i).left ≫ G.hom = (epsR K).hom ≫ spMap (RingHom.id K) := fun i => by
    rw [e, Category.comp_id]; exact Over.w (y' i)
  let v : Fin x.P.g → (epsR K ⟶ x.P.A) := fun i => Over.homMk (hφ.1.lift (y' i).left (epsR K).hom (hw i))
    (hφ.1.lift_snd _ _ _)
  have hvφ : ∀ i, (v i).left ≫ φ = (y' i).left := fun i => hφ.1.lift_fst _ _ _

  let χ : x.P.A.left ⟶ x'.P.A.left := hφ'.1.lift φ x.P.A.hom hφ.1.w
  have hχ : χ ≫ φ' = φ := hφ'.1.lift_fst _ _ _
  have hχ' : χ ≫ x'.P.A.hom = x.P.A.hom ≫ spMap (RingHom.id K) := by
    rw [hφ'.1.lift_snd, e, Category.comp_id]
  have hn : IsGrpPullback x.P.A G (spMap (RingHom.id K) ≫ spMap (RingHom.id K)) (χ ≫ φ') := by
    rw [hχ, e, Category.comp_id, ← e]; exact hφ
  have hC : IsGrpPullback x.P.A x'.P.A (spMap (RingHom.id K)) χ := IsGrpPullback.cancel hφ' hn hχ'
  have := x'.P.isAb.smooth
  have hvχ : ∀ j, (v j).left ≫ χ = spMap (Chart.dualMapR (RingHom.id K)) ≫ (x'.v (j.cast hg'.symm)).left := by
    intro j
    apply hφ'.1.hom_ext
    · rw [Category.assoc, hχ, hvφ, eR, Category.id_comp, hxv', e', Category.id_comp]
      simp
    · rw [Category.assoc, hχ', ← Category.assoc, Over.w (v j), eR, Category.id_comp, Over.w (x'.v _), e,
        Category.comp_id]
  have hv : IsLieBasis v := Chart.isLieBasis_baseChange (RingHom.id K) hC
    (isLieBasis_cast hg'.symm x'.basis) hvχ
  refine ⟨v, hv, fun i => ?_, φ, he, ψ, RingHom.id _, hφ, hψ, hmaps, hsec, hF₁, hF₂, fun i => ?_⟩
  · apply Chart.comb_baseChange (RingHom.id K) hφ (hM i)
    · intro j
      rw [hxv, e', Category.id_comp, eR, Category.id_comp]
    · rw [hvφ, eR, Category.id_comp]
  · rw [hvφ, e', Category.id_comp]

end GlobalTheory.LieLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieBasisLiftModelVectorsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lieBasis_lift_model_vectors : ∀ (K : Type) [Field K] (G : Over (Sp K)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (σ σ' : L.L.Sec) (x x' : KeyIn K) (hg' : x'.P.g = x.P.g) (y y' : Fin x.P.g → (epsR K ⟶ G)) (M : Matrix (Fin x.P.g) (Fin x.P.g) K), KeyOn (RingHom.id K) x G L σ y → KeyOn (RingHom.id K) x' G L σ' (fun i => y' (i.cast hg')) → (∀ i, IsLieComb (M i) y (y' i)) → ∃ (v : Fin x.P.g → (epsR K ⟶ x.P.A)) (hv : IsLieBasis v), (∀ i, IsLieComb (M i) x.v (v i)) ∧ KeyOn (RingHom.id K) ⟨x.P, x.g_pos, x.rig, x.rig_gen, x.th, x.th_ne, v, hv⟩ G L σ y' := by
  first | exact @GlobalTheory.LieLift.main | exact GlobalTheory.LieLift.main | (intros; apply GlobalTheory.LieLift.main <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.KeyEven

theorem keyValue_homog_of_fibres : ∀ κ : Rule, Homog (fun _ => 1) κ → Funct κ → ∀ (K : Type) [Field K] [CharZero K] (G : Over (Sp K)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (σ σ' : L.L.Sec) (g : ℕ) (y y' : Fin g → (epsR K ⟶ G)) (x x' : KeyIn K) (hg : x.P.g = g) (hg' : x'.P.g = g) (a : K) (M : Matrix (Fin g) (Fin g) K), KeyOn (RingHom.id K) x G L σ (fun i => y (i.cast hg)) → KeyOn (RingHom.id K) x' G L σ' (fun i => y' (i.cast hg')) → (∀ i, σ'.f i = constFn G.hom _ a * σ.f i) → (∀ i, IsLieComb (M i) y (y' i)) → a ^ 8 * (κ K x' : K) = M.det ^ 4 * κ K x := by
  intro κ hH hF K _ _ G _ _ L σ σ' g y y' x x' hg hg' a M hx hx' hσ hM
  subst hg
  have ha : a ≠ 0 := by
    rintro rfl
    exact GlobalTheory.T.keyDatum_false_of_modelSection_zero K G L σ' x' (fun i => y' (i.cast hg')) hx' (fun i => by rw [hσ i]; simp [constFn])
  obtain ⟨v, hv, hvM, hx1⟩ := GlobalTheory.T.exists_lieBasis_lift_model_vectors K G L σ σ' x x' hg' y y' M hx hx' hM
  have hth : ∀ s : Sp K, ∃ z : x.P.A.left, x.P.A.hom z = s ∧ z ∈ nonzeroLocus (KeyOnPol.scale x.P.A.hom a x.th) :=
    fun s => (x.th_ne s).imp fun z hz => ⟨hz.1, KeyOnPol.mem_nonzeroLocus_of_unit x.P.A.hom (Units.mk0 a ha) (fun _ => rfl) hz.2⟩
  have hx2 := GlobalTheory.T.keyDatum_scale_sections_by_constant K G L σ σ' ⟨x.P, x.g_pos, x.rig, x.rig_gen, x.th, x.th_ne, v, hv⟩ y' a
    (KeyOnPol.scale x.P.A.hom a x.th) hth (fun _ => rfl) hσ hx1
  have hx'' : KeyOn ((RingHom.id K).comp (RingHom.id K)) x' G L σ' (fun i => y' (i.cast hg')) := by
    rwa [RingHom.id_comp]
  have hpb := GlobalTheory.T.keyDatum_fibre_of_composable_baseChange K K K (RingHom.id K) (RingHom.id K) G L σ' x.P.g y'
    ⟨x.P, x.g_pos, x.rig, x.rig_gen, KeyOnPol.scale x.P.A.hom a x.th, hth, v, hv⟩ x' rfl hg' hx2 hx''
  have e1 := hF K K (RingHom.id K) _ _ hpb
  have e2 := hH K x.P x.g_pos x.rig x.rig_gen x.th x.th_ne x.v x.basis (KeyOnPol.scale x.P.A.hom a x.th) hth v hv a M
    (fun _ => rfl) hvM
  simp only [Nat.mul_one] at e2
  rw [e1, RingHom.id_apply]
  exact e2

end GlobalTheory.KeyEven
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularAtPointFunctionFieldMapOfGenericPointComp
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularAtPointFunctionFieldMapOfGenericPointComp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc.RegPull

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]

theorem germ_gp (V : Y.Opens) (hY : genericPoint Y ∈ V) (h : gp Y (closedPoint _) ∈ V) :
    Y.presheaf.germ V (gp Y (closedPoint _)) h ≫ Scheme.stalkClosedPointTo (gp Y) =
      Y.presheaf.germ V (genericPoint Y) hY := by
  have hC : ∀ G : Spec (Y.presheaf.stalk (genericPoint Y)) ⟶ Y,
      G = Spec.map (𝟙 _) ≫ Y.fromSpecStalk (genericPoint Y) → ∀ h,
      Y.presheaf.germ V (G (closedPoint _)) h ≫ Scheme.stalkClosedPointTo G =
        Y.presheaf.germ V (genericPoint Y) hY ≫ 𝟙 _ := by
    rintro G rfl h
    exact Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk (𝟙 _) V h
  have e : gp Y = Spec.map (𝟙 _) ≫ Y.fromSpecStalk (genericPoint Y) := by
    rw [Spec.map_id, Category.id_comp]; rfl
  exact (hC (gp Y) e h).trans (Category.comp_id _)

theorem fnOf_map (π : Y ⟶ X) (θ : X.functionField →+* Y.functionField)
    (e : gp Y ≫ π = spMap θ ≫ gp X) (U : X.Opens) (hX : genericPoint X ∈ U)
    (hY : genericPoint Y ∈ π ⁻¹ᵁ U) (s : Γ(X, U)) :
    θ (fnOf U hX s) = fnOf (π ⁻¹ᵁ U) hY (π.app U s) := by
  have hA : ∀ F : Sp Y.functionField ⟶ X, F = spMap θ ≫ gp X → ∀ hU,
      X.presheaf.germ U (F (closedPoint _)) hU ≫ Scheme.stalkClosedPointTo F =
        X.presheaf.germ U (genericPoint X) hX ≫ CommRingCat.ofHom θ := by
    rintro F rfl hU
    exact Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk (CommRingCat.ofHom θ) U hU
  have hg : gp Y (closedPoint _) = genericPoint Y := Scheme.fromSpecStalk_closedPoint
  have hV : gp Y (closedPoint _) ∈ π ⁻¹ᵁ U := by rw [hg]; exact hY
  have hB : ∀ F : Sp Y.functionField ⟶ X, F = gp Y ≫ π → ∀ hU,
      X.presheaf.germ U (F (closedPoint _)) hU ≫ Scheme.stalkClosedPointTo F =
        π.app U ≫ Y.presheaf.germ (π ⁻¹ᵁ U) (genericPoint Y) hY := by
    rintro F rfl hU
    rw [Scheme.stalkClosedPointTo_comp]
    refine (Scheme.Hom.germ_stalkMap_assoc π U (gp Y (closedPoint _)) hV _).trans ?_
    exact congrArg (π.app U ≫ ·) (germ_gp (π ⁻¹ᵁ U) hY hV)
  have := (hA _ e hV).symm.trans (hB _ rfl hV)
  exact congrArg (fun g => g.hom s) this

theorem regAt_map (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (π : Y ⟶ X)
    (θ : X.functionField →+* Y.functionField) (hθ : PFF (𝟙 _) π θ) (y : Y) (u : X.functionField)
    (hu : RegAt (π y) u) : RegAt y (θ u) := by
  obtain ⟨l, hl, e⟩ := hθ
  rw [Category.comp_id] at hl
  subst hl
  obtain ⟨U, hx, s, rfl⟩ := hu.exists_fnOf
  have hy : y ∈ π ⁻¹ᵁ U := hx
  rw [fnOf_map π θ e U _ (gen_mem hy) s]
  exact regAt_fnOf hy _ _

end GlobalTheory.Desc.RegPull
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularAtPointFunctionFieldMapOfGenericPointCompStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularAtPoint_functionField_map_of_genericPoint_comp : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (π : Y ⟶ X) (θ : X.functionField →+* Y.functionField), PFF (𝟙 _) π θ → ∀ (y : Y) (u : X.functionField), GlobalTheory.Cartier.RegAt (π y) u → GlobalTheory.Cartier.RegAt y (θ u) := by
  first | exact @GlobalTheory.Desc.RegPull.regAt_map | exact GlobalTheory.Desc.RegPull.regAt_map | (intros; apply GlobalTheory.Desc.RegPull.regAt_map <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrothendieckMessingLiftHomomorphismOfSquareZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrothendieckMessingLiftHomomorphismOfSquareZero
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqLift.Hom

theorem one_left_comp {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') :
    (1 : T ⟶ G').left ≫ φ = T.hom ≫ f ≫ η[G].left := by
  let x : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ φ) (by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]; rfl)
  have e : x * x = x := Over.OverMorphism.ext (by
    rw [h.2 T 1 1 x x rfl rfl, _root_.mul_one]; rfl)
  have e' : x = 1 := by simpa using e
  have := congrArg (fun z ↦ z.left) e'
  refine this.trans ?_
  rw [Hom.one_def, Over.comp_left, Over.toUnit_left, ← Category.assoc]
  rfl

theorem one_left {S : Scheme.{0}} {G : Over S} [GrpObj G] (T : Over S) :
    (1 : T ⟶ G).left = T.hom ≫ η[G].left := by
  rw [Hom.one_def, Over.comp_left, Over.toUnit_left]

theorem liftHom_sq : AbelianDeRham → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0)
    (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I → AbelianSchemeLifts.At hI π → LiftHom (divided₂ hI) π := by
  intro P R R₀ _ _ I hI π hπ hk H g A₀ _ A _ i h hA hg g' B₀ _ B _ j k hB hg' f₀ _ hf
  have pA := (P.1 R A g hA hg).1
  have pB := (P.1 R B g' hB hg').1
  obtain ⟨l, l₁, l₂⟩ : ∃ l : (A₀ ⊗ B₀).left ⟶ (A ⊗ B).left, l ≫ (fst A B).left = (fst A₀ B₀).left ≫ i ∧
      l ≫ (snd A B).left = (snd A₀ B₀).left ≫ j :=
    ⟨Limits.pullback.lift ((fst A₀ B₀).left ≫ i) ((snd A₀ B₀).left ≫ j) (by
      rw [Category.assoc, Category.assoc, h.1.w, k.1.w, ← Category.assoc, ← Category.assoc, Over.w, Over.w]),
      Limits.pullback.lift_fst _ _ _, Limits.pullback.lift_snd _ _ _⟩
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.exists_lift_shearMap_squareZero_abelianSchemes R R₀ I hI π hπ hk H g g' A₀ B₀ A B i j h k hA hB hg hg' A B i j h.1 k.1
    hA.smooth hB.smooth η[A].left η[B].left (Over.w η[A]) (Over.w η[B])
    ((one_left_comp h _).trans (Category.id_comp _)) ((one_left_comp k _).trans (Category.id_comp _)) l l₁ l₂ f₀
    (by rw [schemeFil_eq_liftFil _ h pA, schemeFil_eq_liftFil _ k pB]; exact hf)
  refine GlobalTheory.T.existsUnique_isMonHom_lift_of_grpPullback_abelian R R₀ π hπ ⟨2, hk ▸ hI⟩ A₀ B₀ A B i j h k hA hB f₀ (lift (𝟙 A) 1 ≫ φ) ?_
  have e : i ≫ (lift (𝟙 A) (1 : A ⟶ B)).left = (lift (𝟙 A₀) (1 : A₀ ⟶ B₀)).left ≫ l := by
    refine Limits.pullback.hom_ext ?_ ?_
    · change (i ≫ _) ≫ (fst A B).left = (_ ≫ l) ≫ (fst A B).left
      rw [Category.assoc, Category.assoc, l₁, ← Over.comp_left, ← Category.assoc, ← Over.comp_left, lift_fst, lift_fst,
        Over.id_left, Over.id_left, Category.comp_id, Category.id_comp]
    · change (i ≫ _) ≫ (snd A B).left = (_ ≫ l) ≫ (snd A B).left
      rw [Category.assoc, Category.assoc, l₂, ← Over.comp_left, ← Category.assoc, ← Over.comp_left, lift_snd, lift_snd,
        one_left_comp k, one_left, ← Category.assoc, h.1.w, Category.assoc]
  rw [Over.comp_left, ← Category.assoc, e, Category.assoc, hφ, ← Category.assoc, ← Over.comp_left, comp_mul,
    lift_fst_assoc, lift_snd, _root_.mul_one, Category.id_comp]

end GlobalTheory.SqLift.Hom
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrothendieckMessingLiftHomomorphismOfSquareZeroStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grothendieckMessingLiftHomomorphism_of_squareZero : AbelianDeRham → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I → AbelianSchemeLifts.At hI π → LiftHom (divided₂ hI) π := by
  first | exact @GlobalTheory.SqLift.Hom.liftHom_sq | exact GlobalTheory.SqLift.Hom.liftHom_sq | (intros; apply GlobalTheory.SqLift.Hom.liftHom_sq <;> assumption)
end
end
