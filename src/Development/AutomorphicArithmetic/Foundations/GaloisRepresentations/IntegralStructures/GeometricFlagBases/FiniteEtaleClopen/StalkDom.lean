module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FiniteEtaleClopen.ClopenExtAlt

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FiniteEtaleClopen.StalkDom
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open GlobalTheory.GalV (HTower)
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Cut

theorem UpperTheory.Gal.Int.Geo.Cut.stalkDom :
    UpperTheory.Gal.Int.Geo.Cut.StalkDom := by
  intro O _ _ _ Y p hp y
  haveI : Smooth p := hp
  haveI := GroundTheory.Arith.SchemeCoh.isRegularLocalRing_stalk_of_smooth p y
  exact GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.isDomain
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FiniteEtaleClopen.GenDense
open CategoryTheory AlgebraicGeometry

namespace UpperTheory.Gal.Int.Geo.Cut

theorem genDense : GenDense := by
  intro O _ _ Y p hp
  have hg : GeneralizingMap p := Flat.generalizingMap p
  rw [dense_iff_inter_open]
  rintro U hU ⟨y, hy⟩
  let η : PrimeSpectrum O := ⟨⊥, Ideal.isPrime_bot⟩
  have hη : η ⤳ p y := (PrimeSpectrum.le_iff_specializes _ _).mp bot_le
  obtain ⟨y', hy', hpy'⟩ := hg hη
  exact ⟨y', hy'.mem_open hU hy, by simp only [Set.mem_setOf_eq, hpy', η]⟩

end UpperTheory.Gal.Int.Geo.Cut
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FiniteEtaleClopen.GenRange
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open GlobalTheory.GalV (HTower)
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Cut

theorem UpperTheory.Gal.Int.Geo.Cut.genRange :
    UpperTheory.Gal.Int.Geo.Cut.GenRange := by
  intro O k _ _ _ _ _ Y p
  haveI : IsPreimmersion (gen O k) := IsPreimmersion.of_isLocalization (nonZeroDivisors O)
  have hker : RingHom.ker (algebraMap O k) = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective O k)
  refine ⟨?_, (pullback.fst p (gen O k)).isEmbedding⟩
  rw [Scheme.Pullback.range_fst]
  ext y
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  constructor
  · rintro ⟨z, hz⟩
    rw [← hz]
    change Ideal.comap (algebraMap O k) (z : PrimeSpectrum k).asIdeal = ⊥
    haveI : (z : PrimeSpectrum k).asIdeal.IsPrime := (z : PrimeSpectrum k).isPrime
    rw [Ideal.eq_bot_of_prime (z : PrimeSpectrum k).asIdeal, ← RingHom.ker_eq_comap_bot, hker]
  · intro h
    refine ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k), ?_⟩
    apply PrimeSpectrum.ext
    change Ideal.comap (algebraMap O k) ⊥ = (p y).asIdeal
    rw [h, ← RingHom.ker_eq_comap_bot, hker]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FiniteEtaleClopen.LiesCut
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open GlobalTheory.GalV (HTower)
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Cut

private theorem fEt_surj {Y X : Scheme.{0}} {f : Y ⟶ X} {d : ℕ} (hf : FEt f d) (hd : 0 < d) (x : X) :
    ∃ y : Y, f y = x := by
  let K := AlgebraicClosure (X.residueField x)
  let b : Spec (CommRingCat.of K) ⟶ Spec (X.residueField x) :=
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) K))
  let a : Spec (CommRingCat.of K) ⟶ X := b ≫ X.fromSpecResidueField x
  have hc := hf.2.2 K a
  have hne : Nonempty {y : Spec (CommRingCat.of K) ⟶ Y // y ≫ f = a} := by
    by_contra hem
    rw [not_nonempty_iff] at hem
    rw [Nat.card_of_isEmpty] at hc
    omega
  obtain ⟨⟨y, hy⟩⟩ := hne
  obtain ⟨pt⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
  refine ⟨y pt, ?_⟩
  have h1 : a pt ∈ Set.range (X.fromSpecResidueField x) := ⟨b pt, by simp [a]⟩
  rw [X.range_fromSpecResidueField] at h1
  rw [← Scheme.Hom.comp_apply, hy]
  exact h1

private theorem fEt_comp_iso {Y X X' : Scheme.{0}} {f : Y ⟶ X} (e : X ⟶ X') [IsIso e] {d : ℕ}
    (hf : FEt f d) : FEt (f ≫ e) d := by
  obtain ⟨h1, h2, h3⟩ := hf
  refine ⟨inferInstance, inferInstance, fun K _ _ x => ?_⟩
  rw [← h3 K (x ≫ inv e)]
  refine Nat.card_congr ⟨fun y => ⟨y.1, ?_⟩, fun y => ⟨y.1, ?_⟩, fun _ => rfl, fun _ => rfl⟩
  · rw [← cancel_mono e]; simp [y.2]
  · rw [← Category.assoc, y.2]; simp

theorem UpperTheory.Gal.Int.Geo.Cut.liesCut :
    UpperTheory.Gal.Int.Geo.Cut.LiesCut := by
  intro k L O _ _ _ _ H θ C C' j hj hπ g T s t m hL
  obtain ⟨hm, κ, h, ht, hF⟩ := hL
  have first : ∀ x : T, s x ∈ Set.range C.π → t x ∈ Set.range C.π := by
    rintro x ⟨z, hz⟩
    obtain ⟨w, hw1, hw2⟩ := Scheme.Pullback.exists_preimage_pullback z x hz
    obtain ⟨y, rfl⟩ := fEt_surj hF hm w
    refine ⟨H.t g y, ?_⟩
    have hx : κ y = x := by
      rw [← hw2, ← Scheme.Hom.comp_apply, pullback.lift_snd]
    rw [← hx, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ht]
  refine ⟨first, ?_⟩
  intro T' i s' t' hR
  have : IsOpenImmersion i := hR.op
  have : IsOpenImmersion j := hj.op
  have hrj : ∀ z, C.π z ∈ Set.range j := fun z =>
    ⟨C'.π z, by rw [← hπ, Scheme.Hom.comp_apply]⟩
  have hκ : Set.range κ ⊆ Set.range i := by
    rintro _ ⟨y, rfl⟩
    rw [hR.rng]
    refine ⟨?_, ?_⟩
    · show s (κ y) ∈ Set.range j
      rw [← Scheme.Hom.comp_apply, ← h, Scheme.Hom.comp_apply]
      exact hrj _
    · show t (κ y) ∈ Set.range j
      rw [← Scheme.Hom.comp_apply, ht, Scheme.Hom.comp_apply]
      exact hrj _
  let κ' : H.Y g ⟶ T' := IsOpenImmersion.lift i κ hκ
  have hκ' : κ' ≫ i = κ := IsOpenImmersion.lift_fac i κ hκ
  have hs' : H.s g ≫ C'.π = κ' ≫ s' := by
    rw [← cancel_mono j, Category.assoc, Category.assoc, hπ, hR.es, ← Category.assoc, hκ', h]
  have ht' : κ' ≫ t' = H.t g ≫ C'.π := by
    rw [← cancel_mono j, Category.assoc, Category.assoc, hπ, hR.et, ← Category.assoc, hκ', ht]
  refine ⟨hm, κ', hs', ht', ?_⟩
  have hσ : Set.range (pullback.snd C.π s) ⊆ Set.range i := by
    rintro _ ⟨w, rfl⟩
    have hs1 : s (pullback.snd C.π s w) = C.π (pullback.fst C.π s w) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
    have hmem : s (pullback.snd C.π s w) ∈ Set.range C.π := ⟨_, hs1.symm⟩
    rw [hR.rng]
    refine ⟨?_, ?_⟩
    · show s (pullback.snd C.π s w) ∈ Set.range j
      rw [hs1]; exact hrj _
    · show t (pullback.snd C.π s w) ∈ Set.range j
      obtain ⟨z, hz⟩ := first _ hmem
      rw [← hz]; exact hrj _
  let σ : pullback C.π s ⟶ T' := IsOpenImmersion.lift i (pullback.snd C.π s) hσ
  have hσ' : σ ≫ i = pullback.snd C.π s := IsOpenImmersion.lift_fac i _ hσ
  have hc : pullback.fst C.π s ≫ C'.π = σ ≫ s' := by
    rw [← cancel_mono j, Category.assoc, Category.assoc, hπ, hR.es, ← Category.assoc, hσ',
      pullback.condition]
  let ψ : pullback C.π s ⟶ pullback C'.π s' := pullback.lift (pullback.fst C.π s) σ hc
  have hc' : pullback.fst C'.π s' ≫ C.π = (pullback.snd C'.π s' ≫ i) ≫ s := by
    rw [← hπ, Category.assoc, ← hR.es, ← Category.assoc, ← Category.assoc, pullback.condition]
  let φ : pullback C'.π s' ⟶ pullback C.π s :=
    pullback.lift (pullback.fst C'.π s') (pullback.snd C'.π s' ≫ i) hc'
  have ψ1 : ψ ≫ pullback.fst C'.π s' = pullback.fst C.π s := pullback.lift_fst _ _ _
  have ψ2 : ψ ≫ pullback.snd C'.π s' = σ := pullback.lift_snd _ _ _
  have φ1 : φ ≫ pullback.fst C.π s = pullback.fst C'.π s' := pullback.lift_fst _ _ _
  have φ2 : φ ≫ pullback.snd C.π s = pullback.snd C'.π s' ≫ i := pullback.lift_snd _ _ _
  have hψφ : ψ ≫ φ = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, φ1, ψ1, Category.id_comp]
    · rw [Category.assoc, φ2, ← Category.assoc, ψ2, hσ', Category.id_comp]
  have hφψ : φ ≫ ψ = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, ψ1, φ1, Category.id_comp]
    · rw [Category.assoc, ψ2, Category.id_comp, ← cancel_mono i, Category.assoc, hσ', φ2]
  have : IsIso ψ := ⟨φ, hψφ, hφψ⟩
  have hfac : pullback.lift (H.s g) κ' hs' = pullback.lift (H.s g) κ h ≫ ψ := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, ψ1, pullback.lift_fst]
    · rw [pullback.lift_snd, Category.assoc, ψ2, ← cancel_mono i, hκ', Category.assoc, hσ',
        pullback.lift_snd]
  rw [hfac]
  exact fEt_comp_iso ψ hF
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FiniteEtaleClopen.CoverCut
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open GlobalTheory.GalV (HTower)
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Cut

namespace UpperTheory.Gal.Int.Geo.Cut

open GlobalTheory.GalV (Splits)

private theorem splits_cancel {A B Z : Scheme.{0}} (m : A ⟶ B) [Mono m] (f : Z ⟶ A) {J : Type}
    (a : J → (Z ⟶ Z)) (h : Splits (f ≫ m) (f ≫ m) a) : Splits f f a := by
  obtain ⟨h, hi⟩ := h
  have h' : ∀ j, a j ≫ f = f := fun j =>
    (cancel_mono m).1 (by rw [Category.assoc]; exact h j)
  refine ⟨h', ?_⟩
  let e : pullback f f ⟶ pullback (f ≫ m) (f ≫ m) :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _) (by rw [pullback.condition_assoc])
  let e' : pullback (f ≫ m) (f ≫ m) ⟶ pullback f f :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _)
      (by rw [← cancel_mono m, Category.assoc, Category.assoc, pullback.condition])
  haveI : IsIso e := ⟨⟨e', by
    apply pullback.hom_ext
    · simp only [e, e', Category.assoc, Category.id_comp]
      repeat' rw [pullback.lift_fst]
    · simp only [e, e', Category.assoc, Category.id_comp]
      repeat' rw [pullback.lift_snd], by
    apply pullback.hom_ext
    · simp only [e, e', Category.assoc, Category.id_comp]
      repeat' rw [pullback.lift_fst]
    · simp only [e, e', Category.assoc, Category.id_comp]
      repeat' rw [pullback.lift_snd]⟩⟩
  have heq : (Limits.Sigma.desc fun j => pullback.lift (a j) (𝟙 Z) (by simp [h' j]) :
      (∐ fun _ : J => Z) ⟶ pullback f f) ≫ e =
      Limits.Sigma.desc fun j => pullback.lift (a j) (𝟙 Z) (by simp [h j]) := by
    apply Limits.Sigma.hom_ext
    intro j
    simp only [Limits.colimit.ι_desc_assoc, Limits.colimit.ι_desc, Limits.Cofan.mk_ι_app]
    apply pullback.hom_ext
    · simp only [e, Category.assoc]
      repeat' rw [pullback.lift_fst]
    · simp only [e, Category.assoc]
      repeat' rw [pullback.lift_snd]
  haveI : IsIso ((Limits.Sigma.desc fun j => pullback.lift (a j) (𝟙 Z) (by simp [h' j]) :
      (∐ fun _ : J => Z) ⟶ pullback f f) ≫ e) := by
    rw [heq]
    exact hi
  exact IsIso.of_isIso_comp_right _ e

end UpperTheory.Gal.Int.Geo.Cut

theorem UpperTheory.Gal.Int.Geo.Cut.coverCut :
    UpperTheory.Gal.Int.Geo.Cut.CoverCut := by
  intro k L O _ _ _ _ H θ C V hVcl hpre
  have hV : ∀ z, C.π z ∈ V := by
    intro z
    have hz : pullback.lift C.π H.q C.ov z ∈
        ⇑(pullback.fst C.p (gen O k)) ⁻¹' (V : Set C.Y) := by
      rw [hpre]
      exact ⟨z, rfl⟩
    simpa only [Set.mem_preimage, ← Scheme.Hom.comp_apply, pullback.lift_fst,
      SetLike.mem_coe] using hz
  have hrange : Set.range ⇑C.π ⊆ Set.range ⇑V.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    exact hV z
  let π' : H.Z ⟶ V.toScheme := IsOpenImmersion.lift V.ι C.π hrange
  have hπ' : π' ≫ V.ι = C.π := IsOpenImmersion.lift_fac V.ι C.π hrange
  have ov' : π' ≫ (V.ι ≫ C.p) = H.q ≫ gen O k := by
    rw [← Category.assoc, hπ']
    exact C.ov
  let m : pullback (V.ι ≫ C.p) (gen O k) ⟶ pullback C.p (gen O k) :=
    pullback.lift (pullback.fst _ _ ≫ V.ι) (pullback.snd _ _)
      (by rw [Category.assoc]; exact pullback.condition)
  have hsq : IsPullback (pullback.fst (V.ι ≫ C.p) (gen O k)) m V.ι
      (pullback.fst C.p (gen O k)) := by
    refine IsPullback.of_bot (v₂₁ := pullback.snd C.p (gen O k)) (v₂₂ := C.p)
      (h₃₁ := gen O k) ?_ ?_ (IsPullback.of_hasPullback C.p (gen O k))
    · rw [pullback.lift_snd]
      exact IsPullback.of_hasPullback (V.ι ≫ C.p) (gen O k)
    · rw [pullback.lift_fst]
  haveI hmo : IsOpenImmersion m :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion) hsq
      (inferInstanceAs (IsOpenImmersion V.ι))
  let L' : H.Z ⟶ pullback (V.ι ≫ C.p) (gen O k) := pullback.lift π' H.q ov'
  have hLm : L' ≫ m = pullback.lift C.π H.q C.ov := by
    apply pullback.hom_ext
    · simp only [L', m, Category.assoc]
      rw [pullback.lift_fst, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, hπ']
    · simp only [L', m, Category.assoc]
      rw [pullback.lift_snd, pullback.lift_snd, pullback.lift_snd]
  haveI : Smooth C.p := C.smooth
  haveI : IsClosedImmersion V.ι :=
    .of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hVcl)
  haveI hfin : IsFinite (L' ≫ m) := by
    rw [hLm]
    exact C.finπ
  haveI het : Etale (L' ≫ m) := by
    rw [hLm]
    exact C.etπ
  have spl' : GlobalTheory.GalV.Splits L' L' C.a := by
    apply splits_cancel m L' C.a
    rw [hLm]
    exact C.spl
  have hproj : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver (V.ι ≫ C.p) := by
    obtain ⟨N, i, hi, hic⟩ := C.proj
    haveI := hi
    exact ⟨N, V.ι ≫ i, inferInstance, by rw [Category.assoc, hic]⟩
  have hdim : ∃ d, SmoothOfRelativeDimension d (V.ι ≫ C.p) := by
    obtain ⟨d, hd⟩ := C.dim
    exact ⟨d, HasRingHomProperty.comp_of_isOpenImmersion
      (P := @SmoothOfRelativeDimension d) _ _ hd⟩
  have honto : AlgebraicGeometry.Surjective L' := by
    refine ⟨fun w => ?_⟩
    have hw : m w ∈ ⇑(pullback.fst C.p (gen O k)) ⁻¹' (V : Set C.Y) := by
      rw [Set.mem_preimage, ← Scheme.Hom.comp_apply]
      simp only [m, pullback.lift_fst]
      apply (show Set.range ⇑V.ι ⊆ (V : Set C.Y) by rw [Scheme.Opens.range_ι])
      exact ⟨_, rfl⟩
    rw [hpre] at hw
    obtain ⟨z, hz⟩ := hw
    refine ⟨z, m.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hLm, hz]
  exact ⟨Cover.mk V.toScheme (V.ι ≫ C.p) inferInstance hproj π' ov' C.Δ (grp := C.grp)
      (fin := C.fin) C.a (IsFinite.of_comp L' m) (Etale.of_comp L' m) C.one C.mul spl'
      C.fix hdim,
    V.ι, ⟨inferInstance, by rw [Scheme.Opens.range_ι]; exact hVcl⟩,
    Scheme.Opens.range_ι V, rfl, hπ', honto⟩
end
