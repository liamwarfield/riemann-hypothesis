module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelStructureConditionsAndSplitFibres
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAwaySurjective
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianLocusFiniteEtale
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTransitionMapRaisedModels

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModelsSiegelFamilyComparison
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsClosedImmersionRestrict
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.FiniteImage

open GlobalTheory.DenseFibreIso

theorem exists_isClosedImmersion_restrict {R : Type} [CommRing R] {U Z : Scheme.{0}}
    (s : Z ⟶ Sp R) (u : U ⟶ Z) [IsFinite u] (K : Type) [Field K] [Algebra R K]
    (hc : IsClosedImmersion (pullback.snd u (pullback.fst s (spMap (algebraMap R K)))))
    (x : Z) (hx : RingHom.ker (algebraMap R K) = (s x).asIdeal) :
    ∃ V : Z.Opens, x ∈ V ∧ IsClosedImmersion (u ∣_ V) := by
  obtain ⟨A, B, ψ, φ, j, j', _, ⟨y, rfl⟩, H, hj⟩ := exists_chart s u x
  let : Algebra R A := ψ.hom.toAlgebra
  let : Algebra A B := φ.hom.toAlgebra
  replace H : IsPullback (spMap (algebraMap A B)) j' j u := H
  replace hj : j ≫ s = spMap (algebraMap R A) := hj
  have H₁ := isPullback_tensor R A K
  obtain ⟨m, hm, -⟩ := Scheme.exists_preimage_of_isPullback H₁ y (⊥ : PrimeSpectrum K) (by
    rw [← hj, Scheme.Hom.comp_apply]
    exact PrimeSpectrum.ext hx.symm)
  have H₂ := (isPullback_tensor A (A ⊗[R] K) B).paste_vert H
  have H₀ := (IsPullback.of_hasPullback u (pullback.fst s (spMap (algebraMap R K)))).flip
  have hw : (spMap (algebraMap A (A ⊗[R] K)) ≫ j) ≫ s =
      spMap (Algebra.TensorProduct.includeRight.toRingHom : K →+* A ⊗[R] K) ≫
        spMap (algebraMap R K) := by
    rw [Category.assoc, hj]; exact H₁.w
  have e : pullback.lift _ _ hw ≫ pullback.fst s _ = _ := pullback.lift_fst _ _ _
  have H₃ := IsPullback.of_bot' (v₁₂ := pullback.lift _ _ hw) (by rw [e]; exact H₂) H₀
  have hi := MorphismProperty.of_isPullback (P := @IsClosedImmersion) H₃.flip hc
  have hs : Function.Surjective
      (Algebra.TensorProduct.includeLeftRingHom : (A ⊗[R] K) →+* (A ⊗[R] K) ⊗[A] B) := by
    have h2 := (IsClosedImmersion.isAffine_surjective_of_isAffine (spMap
      (Algebra.TensorProduct.includeLeftRingHom : (A ⊗[R] K) →+* (A ⊗[R] K) ⊗[A] B))).2
    have e := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom : (A ⊗[R] K) →+* (A ⊗[R] K) ⊗[A] B))
    have h3 := (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of ((A ⊗[R] K) ⊗[A] B))).hom).2.comp h2
    rw [← ConcreteCategory.coe_comp, e, ConcreteCategory.coe_comp] at h3
    exact h3.of_comp
  have h1 : IsFinite (spMap (algebraMap A B)) :=
    MorphismProperty.of_isPullback (P := @IsFinite) H.flip ‹_›
  have : Module.Finite A B := RingHom.finite_algebraMap.1 ((IsFinite.SpecMap_iff _).1 h1)
  obtain ⟨a, ha, ha'⟩ := exists_away_surjective (A ⊗[R] K) hs m
  have hQ := IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom _) ha'
  have H₄ := (isPullback_tensor A (Localization.Away a) B).paste_vert H
  let g := spMap (algebraMap A (Localization.Away a)) ≫ j
  refine ⟨g.opensRange, ?_, ?_⟩
  · have hy : y ∈ Set.range (PrimeSpectrum.comap (algebraMap A (Localization.Away a))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away a) a, ← hm]
      exact ha
    obtain ⟨z, rfl⟩ := hy
    exact ⟨z, Scheme.Hom.comp_apply _ _ _⟩
  · have H' := H₄.of_iso (Iso.refl _) g.isoOpensRange (Iso.refl _) (Iso.refl _)
      (fst' := _ ≫ g.isoOpensRange.hom) (snd' := _) (f' := g.opensRange.ι) (g' := u)
      (Category.id_comp _).symm ((Category.comp_id _).trans (Category.id_comp _).symm)
      (by simp [g]) (by simp)
    have H'' := isPullback_morphismRestrict u g.opensRange
    rw [← H''.isoIsPullback_hom_fst _ _ H',
      MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion,
      MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion]
    exact hQ

theorem restrict_sSup (Q : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget Q]
    {U Z : Scheme.{0}} (u : U ⟶ Z) :
    Q (u ∣_ sSup {V : Z.Opens | Q (u ∣_ V)}) := by
  refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict fun x => ?_
  obtain ⟨V, hV, hx⟩ := TopologicalSpace.Opens.mem_sSup.1 x.2
  refine ⟨(sSup {V : Z.Opens | Q (u ∣_ V)}).ι ⁻¹ᵁ V, hx, ?_⟩
  rw [Q.arrow_mk_iso_iff (morphismRestrictRestrict _ _ _)]
  refine (Q.arrow_mk_iso_iff (morphismRestrictEq u ?_)).2 hV
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact inf_eq_right.2 (le_sSup hV)

theorem dense_of_flat {O : Type} [CommRing O] [IsDomain O] {T : Scheme.{0}} (t : T ⟶ Sp O)
    [Flat t] (W : Set T) (hW : ∀ x : T, (t x).asIdeal = ⊥ → x ∈ W) : Dense W := by
  intro x
  have hsp : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum O) ⤳ t x :=
    (PrimeSpectrum.le_iff_specializes _ _).1 (show (⊥ : Ideal O) ≤ _ from bot_le)
  obtain ⟨y, hy, hy'⟩ := Flat.generalizingMap t hsp
  exact hy.mem_closed isClosed_closure (subset_closure (hW y (by rw [hy'])))

theorem main : ∀ (O F : Type) [CommRing O] [IsDedekindDomain O] [Field F] [Algebra O F] [IsFractionRing O F] (U Z : Scheme.{0}) (u : U ⟶ Z) (s : Z ⟶ Sp O), IsFinite u → IsReduced U → Flat (u ≫ s) → LocallyOfFiniteType s → QuasiCompact s → IsClosedImmersion (pullback.snd u (pullback.fst s (spMap (algebraMap O F)))) → ∃ (XX : Scheme.{0}) (u' : U ⟶ XX) (i : XX ⟶ Z) (W : XX.Opens), u' ≫ i = u ∧ IsClosedImmersion i ∧ IsFinite u' ∧ Surjective u' ∧ Dense (W : Set XX) ∧ IsIso (u' ∣_ W) ∧ Dense ((u' ⁻¹ᵁ W : U.Opens) : Set U) ∧ IsReduced XX ∧ Flat (i ≫ s) := by
  intro O F _ _ _ _ _ U Z u s _ _ _ _ _ hc
  let W₀ : Z.Opens := sSup {V : Z.Opens | IsClosedImmersion (u ∣_ V)}
  have hW₀ : IsClosedImmersion (u ∣_ W₀) := restrict_sSup @IsClosedImmersion u
  have hmem : ∀ z : Z, (s z).asIdeal = ⊥ → z ∈ W₀ := fun z hz => by
    obtain ⟨V, hV, hV'⟩ := exists_isClosedImmersion_restrict s u F hc z (by
      rw [hz]; exact (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective O F))
    exact TopologicalSpace.Opens.mem_sSup.2 ⟨V, hV', hV⟩
  have hfl : Flat (u.imageι ≫ s) := flat_image_of_isDedekindDomain (O := CommRingCat.of O) u s
  have : IsFinite (u.toImage ≫ u.imageι) := by rw [u.toImage_imageι]; infer_instance
  have hfin : IsFinite u.toImage := IsFinite.of_comp _ u.imageι
  refine ⟨u.image, u.toImage, u.imageι, u.imageι ⁻¹ᵁ W₀, u.toImage_imageι, inferInstance, hfin,
    surjective_of_isDominant_of_isClosed_range _ u.toImage.isClosedMap.isClosed_range,
    dense_of_flat (u.imageι ≫ s) _ fun x hx => hmem _ (by rwa [← Scheme.Hom.comp_apply]), ?_,
    dense_of_flat (u ≫ s) _ fun x hx => ?_, inferInstance, hfl⟩
  · have h1 : IsClosedImmersion ((u.toImage ≫ u.imageι) ∣_ W₀) := by
      have : ∀ v : U ⟶ Z, v = u → IsClosedImmersion (v ∣_ W₀) := by rintro _ rfl; exact hW₀
      exact this _ u.toImage_imageι
    rw [morphismRestrict_comp] at h1
    have h2 : IsClosedImmersion (u.toImage ∣_ u.imageι ⁻¹ᵁ W₀) :=
      @IsClosedImmersion.of_comp _ _ _ _ (u.imageι ∣_ W₀) h1 _
    have h3 : IsSchemeTheoreticallyDominant (u.toImage ∣_ u.imageι ⁻¹ᵁ W₀) :=
      IsSchemeTheoreticallyDominant.of_isPullback
        (isPullback_morphismRestrict u.toImage (u.imageι ⁻¹ᵁ W₀)).flip
    exact isIso_of_isClosedImmersion_of_schemeDominant _
  · change u.imageι (u.toImage x) ∈ W₀
    rw [← Scheme.Hom.comp_apply, u.toImage_imageι]
    exact hmem _ (by rwa [← Scheme.Hom.comp_apply])

end GlobalTheory.FiniteImage
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.MonoOfUnramifiedOfPoints
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.ModuliEmbed

theorem mono_of_unramified_of_points {X Y : Scheme.{0}} (f : X ⟶ Y) [FormallyUnramified f] [LocallyOfFiniteType f]
    (h : ∀ (k : Type) [Field k] (y y' : Sp k ⟶ X), y ≫ f = y' ≫ f → y = y') : Mono f := by
  have hs : Surjective (pullback.diagonal f) := by
    exact ((tfae_universallyInjective f).out 2 4).1 fun (k : Type) [Field k] y y' e => h k y y' e
  have : IsIso (pullback.diagonal f) := (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨inferInstance, hs⟩
  exact (pullback.isIso_diagonal_iff f).1 this

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem objMap_of_comp_eq {B B' : Type} [CommRing B] [CommRing B'] {b : Base l B} {b' : Base l B'}
    {S T Z : Scheme.{0}} {s : S ⟶ Sp B} {s' : T ⟶ Sp B'} {o : Obj D l b s} {o' : Obj D l b' s'} {t : SAB H Z}
    {f : S ⟶ Z} (ν : SABMap o.t t f) {u uA : D.La → (𝟙_ (Over Z) ⟶ t.G)}
    (h₁ : ∀ x, (o.eta x).left ≫ ν.φ = f ≫ (u x).left) (h₂ : ∀ x, (o.etaA x).left ≫ ν.φ = f ≫ (uA x).left)
    {y y' : T ⟶ S} (e : y ≫ f = y' ≫ f) (m : ObjMap o' o y) : Nonempty (ObjMap o' o y') := by
  have hn : ∃ n : SABMap o'.t t (y' ≫ f), n.φ = m.toSABMap.φ ≫ ν.φ := by
    rw [← e]; exact ObjMaps.exists_sab_comp ν m.toSABMap
  obtain ⟨n, hn⟩ := hn
  obtain ⟨m', hm'⟩ := ObjMaps.exists_sab_cancel ν n
  have k : m'.cm.F ≫ ν.cm.F = m.cm.F ≫ ν.cm.F := hm'.symm.trans hn
  exact ⟨⟨m', fun a => ObjComp.sec_cancel ν.cart.1 m'.cart.1.w (Over.w (o.eta a)) (Over.w (o'.eta a)) (h₁ a)
      (by rw [k, ← e]; exact ObjComp.sec_comp (h₁ a) (m.eta a)),
    fun a => ObjComp.sec_cancel ν.cart.1 m'.cart.1.w (Over.w (o.etaA a)) (Over.w (o'.etaA a)) (h₂ a)
      (by rw [k, ← e]; exact ObjComp.sec_comp (h₂ a) (m.etaA a))⟩⟩

end GlobalTheory.ModuliEmbed

namespace GlobalTheory

theorem moduli_isClosedImmersion : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (o : Obj D l (baseKA l) (pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s)) (_ : ObjMap o Xo.univ (pullback.fst _ _)) (Z : Scheme.{0}) (sZ : Z ⟶ Sp c.F) (t : SAB H Z) (f : Xo.XF c ⟶ Z) (ν : SABMap o.t t f) (η' ηA : D.La → (𝟙_ (Over Z) ⟶ t.G)), f ≫ sZ = pullback.snd _ _ → (∀ x, (o.eta x).left ≫ ν.φ = f ≫ (η' x).left) → (∀ x, (o.etaA x).left ≫ ν.φ = f ≫ (ηA x).left) → IsFinite f → IsClosedImmersion f := by
  intro _ _ _ E _ _ _ H D l Xo c o m0 Z sZ t f ν u uA hf h₁ h₂ hfin
  have key : ∀ (T : Scheme.{0}) (y y' : T ⟶ Xo.XF c), y ≫ f = y' ≫ f →
      y ≫ pullback.snd _ _ = y' ≫ pullback.snd _ _ ∧
      ∃ o' : Obj D l (baseKA l) ((y ≫ pullback.fst _ _) ≫ Xo.s),
        Nonempty (ObjMap o' Xo.univ (y ≫ pullback.fst _ _)) ∧
        Nonempty (ObjMap o' Xo.univ (y' ≫ pullback.fst _ _)) := by
    intro T y y' e
    refine ⟨by rw [← hf, ← Category.assoc, e, Category.assoc], ?_⟩
    obtain ⟨o', ⟨m⟩⟩ := obj_pull E H D l (KA l) (KA l) (baseKA l) (baseKA l) (RingHom.id _) _ T _
      ((y ≫ pullback.fst _ _) ≫ Xo.s) y rfl rfl
      ((Category.assoc _ _ _).symm.trans ((Category.comp_id _).symm.trans
        (congrArg (((y ≫ pullback.fst _ _) ≫ Xo.s) ≫ ·) (Spec.map_id _).symm))) o
    obtain ⟨m'⟩ := ModuliEmbed.objMap_of_comp_eq ν h₁ h₂ e m
    exact ⟨o', ⟨(ObjComp.objMap_comp m0 m).choose⟩, ⟨(ObjComp.objMap_comp m0 m').choose⟩⟩
  have hu : FormallyUnramified f := by
    refine TangentCrit.formallyUnramified_of_tangent f fun k _ _ w hw => ?_
    obtain ⟨e, o', m, m'⟩ := key _ w (constPt w) (hw.trans (by simp only [constPt, Category.assoc]))
    refine pullback.hom_ext ?_ e
    have e' : constPt w ≫ pullback.fst _ _ = constPt (w ≫ pullback.fst _ _) := by
      simp only [constPt, Category.assoc]
    rw [e'] at m'
    exact (Xo.unram k _ o' m m').trans e'.symm
  have hm : Mono f := by
    refine ModuliEmbed.mono_of_unramified_of_points f fun k _ y y' e => ?_
    obtain ⟨e₂, o', m, m'⟩ := key _ y y' e
    refine pullback.hom_ext ?_ e₂
    refine (Xo.rep _ _ inferInstance o').unique ⟨rfl, m⟩ ⟨?_, m'⟩
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc, ← e₂, Category.assoc]
  exact (IsClosedImmersion.iff_isFinite_and_mono f).2 ⟨hfin, hm⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.EtaleOfSemilocalDedekindOfBirational
namespace GlobalTheory

section
open Polynomial IsLocalRing

theorem etale_of_semilocal_dedekind_of_birational (B S : Type*) [CommRing B] [IsDedekindDomain B]
    [Finite (MaximalSpectrum B)] [CommRing S] [IsDomain S] [IsLocalRing S] [Algebra B S]
    (hinj : Function.Injective (algebraMap B S))
    (hq : (maximalIdeal S).comap (algebraMap B S) ≠ ⊥)
    (hfr : ∀ x : S, ∃ a b : B, b ≠ 0 ∧ x * algebraMap B S b = algebraMap B S a) :
    Algebra.Etale B S := by
  classical
  set q := (maximalIdeal S).comap (algebraMap B S) with hq_def
  have hqp : q.IsPrime := Ideal.comap_isPrime _ _
  have hmem : ∀ y : B, y ∈ q ↔ ¬ IsUnit (algebraMap B S y) := fun y => by
    rw [hq_def, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  obtain ⟨s, hs_mem, hsq⟩ : ∃ s : B, (∀ P : Ideal B, P.IsMaximal → P ≠ q → s ∈ P) ∧ s ∉ q := by
    let T : Finset (MaximalSpectrum B) :=
      (Set.toFinite {m : MaximalSpectrum B | m.asIdeal ≠ q}).toFinset
    have hT : ¬ T.inf (fun m => m.asIdeal) ≤ q := by
      intro hle
      obtain ⟨m, hmT, hmq⟩ := hqp.inf_le'.mp hle
      simp only [T, Set.Finite.mem_toFinset] at hmT
      exact hmT (m.isMaximal.eq_of_le hqp.ne_top hmq)
    obtain ⟨s, hsT, hsq⟩ := SetLike.not_le_iff_exists.mp hT
    refine ⟨s, fun P hP hPq => ?_, hsq⟩
    have hPT : (⟨P, hP⟩ : MaximalSpectrum B) ∈ T := by simpa [T] using hPq
    exact Finset.inf_le (f := fun m : MaximalSpectrum B => m.asIdeal) hPT hsT
  have hsu : IsUnit (algebraMap B S s) := by
    by_contra h
    exact hsq ((hmem s).mpr h)
  have key : ∀ x : S, ∃ a t : B, t ∉ q ∧ x * algebraMap B S t = algebraMap B S a := by
    intro x
    obtain ⟨a, b, hb, hx⟩ := hfr x
    have hb' : algebraMap B S b ≠ 0 := fun h => hb (hinj (by rw [h, map_zero]))
    have hdvr := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hq
      (Localization.AtPrime q)
    have hBq : Function.Injective (algebraMap B (Localization.AtPrime q)) :=
      IsLocalization.injective _ q.primeCompl_le_nonZeroDivisors
    obtain ⟨c, hc | hc⟩ := ValuationRing.cond (algebraMap B (Localization.AtPrime q) a)
      (algebraMap B (Localization.AtPrime q) b)
    · obtain ⟨⟨a', t⟩, hct⟩ := IsLocalization.surj q.primeCompl c
      have h1 : a * a' = b * t := hBq (by simp only [map_mul]; rw [← hct, ← hc]; ring)
      have h2 : x * algebraMap B S a' = algebraMap B S t := by
        apply mul_left_cancel₀ hb'
        have h3 := congrArg (algebraMap B S) h1
        simp only [map_mul] at h3
        rw [← hx] at h3
        linear_combination h3
      refine ⟨t, a', ?_, h2⟩
      intro ha'
      have ht : IsUnit (algebraMap B S t) := by
        by_contra h
        exact t.2 ((hmem t).mpr h)
      rw [← h2] at ht
      exact (hmem a').mp ha' (isUnit_of_mul_isUnit_right ht)
    · obtain ⟨⟨a', t⟩, hct⟩ := IsLocalization.surj q.primeCompl c
      have h1 : b * a' = a * t := hBq (by simp only [map_mul]; rw [← hct, ← hc]; ring)
      refine ⟨a', t, t.2, ?_⟩
      apply mul_left_cancel₀ hb'
      have h3 := congrArg (algebraMap B S) h1
      simp only [map_mul] at h3
      rw [← hx] at h3
      linear_combination -h3
  have hsurj : ∀ x : S, ∃ y : B × Submonoid.powers s,
      x * algebraMap B S y.2 = algebraMap B S y.1 := by
    intro x
    obtain ⟨a, t, htq, hxt⟩ := key x
    have ht0 : t ≠ 0 := by
      rintro rfl
      exact htq q.zero_mem
    have hrad : s ∈ (Ideal.span {t}).radical := by
      rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
      rintro P ⟨hP, hPp⟩
      have htP : t ∈ P := hP (Ideal.mem_span_singleton_self t)
      have hPne : P ≠ ⊥ := fun h => ht0 (by rwa [h, Ideal.mem_bot] at htP)
      exact hs_mem P (Ring.DimensionLEOne.maximalOfPrime hPne hPp) (fun h => htq (h ▸ htP))
    obtain ⟨n, hn⟩ := hrad
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp hn
    refine ⟨⟨a * u, ⟨s ^ n, n, rfl⟩⟩, ?_⟩
    show x * algebraMap B S (s ^ n) = algebraMap B S (a * u)
    rw [← hu, map_mul, map_mul]
    linear_combination (algebraMap B S u) * hxt
  have hloc : IsLocalization.Away s S := (isLocalization_iff (Submonoid.powers s) S).mpr
    ⟨fun y => by
      obtain ⟨_, n, rfl⟩ := y
      simpa using hsu.pow n,
     hsurj, fun {x y} h => ⟨1, by rw [hinj h]⟩⟩
  exact Algebra.Etale.of_isLocalizationAway s

theorem etale_adjoin_root_of_unity (O S : Type*) [CommRing O] [IsDomain O] [IsIntegrallyClosed O]
    [CommRing S] [IsDomain S] [Algebra O S] (hinj : Function.Injective (algebraMap O S))
    {N : ℕ} (hN : 0 < N) (hu : IsUnit (N : O)) {z : S} (hz : z ^ N = 1) :
    IsIntegral O z ∧ Algebra.Etale O (Algebra.adjoin O {z}) := by
  have hI : IsIntegral O z := ⟨X ^ N - C 1, monic_X_pow_sub_C 1 hN.ne', by simp [hz]⟩
  refine ⟨hI, ?_⟩
  have : FaithfulSMul O S := (faithfulSMul_iff_algebraMap_injective O S).mpr hinj
  have hfm : (minpoly O z).Monic := minpoly.monic hI
  obtain ⟨h, hgh⟩ : minpoly O z ∣ X ^ N - C 1 :=
    minpoly.isIntegrallyClosed_dvd hI (by simp [hz])
  have hpoly : X * derivative (X ^ N - C (1 : O)) = C (N : O) * (X ^ N - C 1) + C (N : O) := by
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    simp only [derivative_sub, derivative_X_pow, Nat.add_sub_cancel, map_one, derivative_one,
      sub_zero]
    push_cast
    ring
  have hg0 : AdjoinRoot.mk (minpoly O z) (X ^ N - C 1) = 0 := by
    rw [hgh, AdjoinRoot.mk_eq_zero]; exact dvd_mul_right _ _
  have hd : AdjoinRoot.mk (minpoly O z) (derivative (X ^ N - C (1 : O))) =
      AdjoinRoot.mk (minpoly O z) (derivative (minpoly O z)) * AdjoinRoot.mk (minpoly O z) h := by
    rw [hgh, derivative_mul, map_add (f := _), map_mul, map_mul, AdjoinRoot.mk_self, zero_mul, add_zero]
  have h1 := congrArg (AdjoinRoot.mk (minpoly O z)) hpoly
  rw [map_mul, hd, map_add (f := _), map_mul, hg0, mul_zero, zero_add] at h1
  have hu' : IsUnit (AdjoinRoot.mk (minpoly O z) (C (N : O))) := by
    rw [AdjoinRoot.mk_C]; exact hu.map _
  rw [← h1] at hu'
  have hunit := isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_right hu')
  have := etale_adjoinRoot_of_isUnit_derivative hfm hunit
  exact Algebra.Etale.of_equiv (minpoly.equivAdjoin hI)

theorem etale_of_birational_adjoin_root_of_unity (O S : Type*) [CommRing O] [IsDedekindDomain O]
    [IsLocalRing O] [CommRing S] [IsDomain S] [IsLocalRing S] [Algebra O S]
    (hinj : Function.Injective (algebraMap O S))
    {N : ℕ} (hN : 0 < N) (hu : IsUnit (N : O)) {z : S} (hz : z ^ N = 1)
    (π : O) (hπ : π ≠ 0) (hπ' : algebraMap O S π ∈ maximalIdeal S)
    (hfr : ∀ x : S, ∃ a ∈ Algebra.adjoin O {z}, ∃ b ∈ Algebra.adjoin O {z}, b ≠ 0 ∧ x * b = a) :
    Algebra.Etale O S := by
  classical
  obtain ⟨hI, hA⟩ := etale_adjoin_root_of_unity O S hinj hN hu hz
  have : FaithfulSMul O S := (faithfulSMul_iff_algebraMap_injective O S).mpr hinj
  have hfin : Module.Finite O (Algebra.adjoin O {z}) := (Algebra.adjoin.powerBasis' hI).finite
  have hnoeth : IsNoetherianRing (Algebra.adjoin O {z}) :=
    IsNoetherianRing.of_finite O (Algebra.adjoin O {z})
  have hdim : Ring.DimensionLEOne (Algebra.adjoin O {z}) :=
    Ring.DimensionLEOne.of_isIntegral O (Algebra.adjoin O {z})
  have hic : IsIntegrallyClosed (Algebra.adjoin O {z}) :=
    IsIntegrallyClosed.of_localization_maximal fun p _ _ =>
      (isDomain_and_isIntegrallyClosed_atPrime_of_etale O p (Localization.AtPrime p)).2
  have : IsDedekindRing (Algebra.adjoin O {z}) :=
    { toIsNoetherian := hnoeth, toDimensionLEOne := hdim, toIsIntegralClosure := hic }
  have hmax : Finite (MaximalSpectrum (Algebra.adjoin O {z})) := by
    have hf : ((maximalIdeal O).primesOver (Algebra.adjoin O {z})).Finite :=
      Algebra.QuasiFinite.finite_primesOver _
    have := hf.to_subtype
    refine Finite.of_injective (fun m : MaximalSpectrum (Algebra.adjoin O {z}) =>
      (⟨m.asIdeal, m.isMaximal.isPrime, ?_⟩ : (maximalIdeal O).primesOver (Algebra.adjoin O {z})))
      (fun m m' h => MaximalSpectrum.ext (congrArg Subtype.val h))
    have := m.isMaximal
    exact ⟨(IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := O) m.asIdeal)).symm⟩
  have hq : (maximalIdeal S).comap (algebraMap (Algebra.adjoin O {z}) S) ≠ ⊥ := by
    intro h
    have hmem : algebraMap O (Algebra.adjoin O {z}) π ∈
        (maximalIdeal S).comap (algebraMap (Algebra.adjoin O {z}) S) := by
      rw [Ideal.mem_comap, ← IsScalarTower.algebraMap_apply]
      exact hπ'
    rw [h, Ideal.mem_bot] at hmem
    exact hπ (hinj (by rw [IsScalarTower.algebraMap_apply O (Algebra.adjoin O {z}) S, hmem,
      map_zero, map_zero]))
  have hfr' : ∀ x : S, ∃ a b : Algebra.adjoin O {z}, b ≠ 0 ∧
      x * algebraMap (Algebra.adjoin O {z}) S b = algebraMap (Algebra.adjoin O {z}) S a := by
    intro x
    obtain ⟨a, ha, b, hb, hb0, hx⟩ := hfr x
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hb0 (by simpa using congrArg Subtype.val h), hx⟩
  have hAS : Algebra.Etale (Algebra.adjoin O {z}) S :=
    etale_of_semilocal_dedekind_of_birational (Algebra.adjoin O {z}) S
      (fun x y h => Subtype.ext h) hq hfr'
  exact Algebra.Etale.comp O (Algebra.adjoin O {z}) S

end

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Models

theorem etale_coeff_adjoin_zeta (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (l l₁ : Level H) (c : Coeff l) (c₁ : Coeff l₁) (p N : ℕ) (W : ValuationSubring ℂ)
    (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (hNp : N.Coprime p) (hN : 0 < N)
    (hF : c₁.F = c.F ⊔ IntermediateField.adjoin ℚ {zeta N}) (b : c.V W →+* c₁.V W)
    (hb : IsIncl b) : Etale (spMap b) := by
  classical
  obtain ⟨-, -, -, hloc⟩ := CoeffRings.coeff_isDedFrac E H l c
  obtain ⟨⟨⟨_, hdd⟩, -, hfrac⟩, hunit, -⟩ := hloc p W hp hW
  let _ : Algebra (c.V W) (c₁.V W) := b.toAlgebra
  unfold spMap
  rw [HasRingHomProperty.Spec_iff (P := @Etale), CommRingCat.hom_ofHom]
  change Algebra.Etale (c.V W) (c₁.V W)
  let ι₀ : c.V W →+* ℂ := c.F.val.toRingHom.comp (c.V W).subtype
  let ι₁ : c₁.V W →+* ℂ := c₁.F.val.toRingHom.comp (c₁.V W).subtype
  have hι₀ : Function.Injective ι₀ := fun x y h => Subtype.ext (Subtype.ext h)
  have hι₁ : Function.Injective ι₁ := fun x y h => Subtype.ext (Subtype.ext h)
  have hbι : ∀ x, ι₁ (algebraMap (c.V W) (c₁.V W) x) = ι₀ x := hb
  have hinj : Function.Injective (algebraMap (c.V W) (c₁.V W)) := fun x y h =>
    hι₀ (by rw [← hbι, ← hbι, h])
  have hζF : zeta N ∈ c₁.F := by
    rw [hF]
    exact (le_sup_right : IntermediateField.adjoin ℚ {zeta N} ≤ c.F ⊔ IntermediateField.adjoin ℚ {zeta N})
      (IntermediateField.mem_adjoin_simple_self ℚ (zeta N))
  have hζW : (⟨zeta N, hζF⟩ : c₁.F) ∈ c₁.V W :=
    ValuationSubring.mem_comap.mpr (CoeffRings.mem_of_isIntegral W (CoeffRings.isIntegral_int_zeta hN))
  let z : c₁.V W := ⟨⟨zeta N, hζF⟩, hζW⟩
  have hzι : ι₁ z = zeta N := rfl
  have hz : z ^ N = 1 := hι₁ (by
    rw [map_pow, map_one, hzι]
    exact (Complex.isPrimitiveRoot_exp N hN.ne').pow_eq_one)
  have hπ : ((p : ℕ) : c.V W) ≠ 0 := fun h => hp.ne_zero (by
    have h1 := congrArg ι₀ h
    rw [map_natCast, map_zero] at h1
    exact_mod_cast h1)
  have hπ' : algebraMap (c.V W) (c₁.V W) (p : c.V W) ∈ IsLocalRing.maximalIdeal (c₁.V W) := by
    rw [map_natCast, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, hu⟩
    rcases (ValuationSubring.mem_nonunits_iff_or W).mp hW with h0 | hinv
    · exact hp.ne_zero (by exact_mod_cast h0)
    · apply hinv
      have h1 : ι₁ ↑u * ι₁ ↑u⁻¹ = 1 := by rw [← map_mul, Units.mul_inv, map_one]
      rw [hu, map_natCast] at h1
      rw [← eq_inv_of_mul_eq_one_right h1]
      exact ValuationSubring.mem_comap.mp (↑u⁻¹ : c₁.V W).2
  let A' := Algebra.adjoin (c.V W) {z}
  let P : ℂ → Prop := fun y => ∃ d : c.V W, d ≠ 0 ∧ ∃ a ∈ A', ι₁ a = ι₀ d * y
  have hPF : ∀ y ∈ c.F, P y := by
    intro y hy
    obtain ⟨⟨a, d⟩, had⟩ :=
      @IsLocalization.surj _ _ _ _ _ (c.V W).subtype.toAlgebra hfrac ⟨y, hy⟩
    have had' : y * ι₀ d = ι₀ a := congrArg (fun t : c.F => (t : ℂ)) had
    refine ⟨d, nonZeroDivisors.coe_ne_zero d, algebraMap (c.V W) (c₁.V W) a,
      Subalgebra.algebraMap_mem _ _, ?_⟩
    rw [hbι, ← had', mul_comm]
  have hadd : ∀ y₁ y₂, P y₁ → P y₂ → P (y₁ + y₂) := by
    rintro y₁ y₂ ⟨d₁, hd₁, a₁, ha₁, e₁⟩ ⟨d₂, hd₂, a₂, ha₂, e₂⟩
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂,
      algebraMap (c.V W) (c₁.V W) d₂ * a₁ + algebraMap (c.V W) (c₁.V W) d₁ * a₂,
      A'.add_mem (A'.mul_mem (A'.algebraMap_mem _) ha₁) (A'.mul_mem (A'.algebraMap_mem _) ha₂), ?_⟩
    rw [map_add (f := _), map_mul, map_mul, hbι, hbι, e₁, e₂, map_mul]
    ring
  have hmul : ∀ y₁ y₂, P y₁ → P y₂ → P (y₁ * y₂) := by
    rintro y₁ y₂ ⟨d₁, hd₁, a₁, ha₁, e₁⟩ ⟨d₂, hd₂, a₂, ha₂, e₂⟩
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, a₁ * a₂, A'.mul_mem ha₁ ha₂, ?_⟩
    rw [map_mul, e₁, e₂, map_mul]
    ring
  let T : Subalgebra ℚ ℂ :=
    { carrier := {y | P y}
      mul_mem' := fun {y₁ y₂} h₁ h₂ => hmul y₁ y₂ h₁ h₂
      add_mem' := fun {y₁ y₂} h₁ h₂ => hadd y₁ y₂ h₁ h₂
      algebraMap_mem' := fun r => hPF _ (c.F.algebraMap_mem r) }
  have hle : c₁.F.toSubalgebra ≤ T := by
    have := c.fin
    rw [hF, IntermediateField.sup_toSubalgebra_of_left]
    refine sup_le (fun y hy => hPF y hy) ?_
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (CoeffRings.isIntegral_int_zeta hN).tower_top.isAlgebraic]
    refine Algebra.adjoin_le (Set.singleton_subset_iff.mpr ?_)
    exact ⟨1, one_ne_zero, z, Algebra.subset_adjoin rfl, by rw [map_one, one_mul]; exact hzι⟩
  have hfr : ∀ x : c₁.V W, ∃ a ∈ A', ∃ b' ∈ A', b' ≠ 0 ∧ x * b' = a := by
    intro x
    obtain ⟨d, hd, a, ha, e⟩ := hle (x : c₁.F).2
    refine ⟨a, ha, algebraMap (c.V W) (c₁.V W) d, A'.algebraMap_mem d,
      fun h => hd (hinj (by rw [h, map_zero])), hι₁ ?_⟩
    rw [map_mul, hbι, e]
    exact mul_comm _ _
  exact etale_of_birational_adjoin_root_of_unity (c.V W) (c₁.V W) hinj hN (hunit N hNp) hz
    (p : c.V W) hπ hπ' hfr

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModelsSiegelFamilyComparison
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.SiegelComparison

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_pull (hC : Out.CubePullSt) {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) :
    ∃ t' : SAB H S', Nonempty (SABMap t' t f) := by
  obtain ⟨PP, cub, sym, adj, prim, m, hm⟩ := sabPull hC f t
  exact ⟨_, ⟨m⟩⟩

theorem exists_section {S S' : Scheme.{0}} {f : S' ⟶ S} {t : SAB H S} {t' : SAB H S'} (m : SABMap t' t f)
    (x : S' ⟶ t.G.left) (hx : x ≫ t.G.hom = f) : ∃ σ : 𝟙_ (Over S') ⟶ t'.G, σ.left ≫ m.φ = x :=
  ⟨Over.homMk (m.cart.1.lift x (𝟙 S') (hx.trans (Category.id_comp f).symm)) (m.cart.1.lift_snd _ _ _),
    m.cart.1.lift_fst _ _ _⟩

theorem exists_cancel {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S}
    {h : S'' ⟶ S} (m : SABMap t' t f) (n : SABMap t'' t h) (g : S'' ⟶ S') (e : g ≫ f = h) :
    ∃ m' : SABMap t'' t' g, m'.φ ≫ m.φ = n.φ := by
  subst e
  obtain ⟨m', hm⟩ := sabCancel pullCubCancel E H _ _ _ t t' t'' f g m n
  exact ⟨m', hm.symm⟩

theorem isAbelianScheme_of_proper {S : Scheme.{0}} (t : SAB H S) (h : IsProper t.G.hom) : IsAbelianScheme t.G :=
  ⟨t.comm, t.semi.smooth, h, t.semi.geomConnected⟩

theorem exists_square {S S' : Scheme.{0}} {f : S' ⟶ S} {t : SAB H S} {t' : SAB H S'} (m : SABMap t' t f) :
    ∃ m₂ : (G2 t'.G).left ⟶ (G2 t.G).left, IsSquare m.φ m₂ ∧ ∀ (X : Scheme.{0}) (φ₂ : X ⟶ (G2 t'.G).left),
      LBIso ((abelian₂ t'.G t'.PP.L).pull φ₂) ((abelian₂ t.G t.PP.L).pull (φ₂ ≫ m₂)) := by
  have h := m.cart
  let U := lift (pushPt h.1.w (fst t'.G t'.G)) (pushPt h.1.w (snd t'.G t'.G))
  refine ⟨U.left, ⟨?_, ?_⟩, fun X φ₂ => ?_⟩
  · exact congrArg (fun z => z.left) (lift_fst (pushPt h.1.w (fst t'.G t'.G)) (pushPt h.1.w (snd t'.G t'.G)))
  · exact congrArg (fun z => z.left) (lift_snd (pushPt h.1.w (fst t'.G t'.G)) (pushPt h.1.w (snd t'.G t'.G)))
  · obtain ⟨w, hw, -⟩ := m.lin
    refine LBIso.chartPull (chartPullOut t'.PP.L _ _ φ₂ _ fun _ => rfl) (chartPullOut t.PP.L _ _ _ _ fun I => ?_)
      (iso_linComb ((isGen_iff w).1 hw) _ _)
    rw [Category.assoc, Category.assoc]
    congr 1
    refine psum_push h _ _ U (fun i => ?_) I.down
    fin_cases i <;> simp [U, x2]

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem exists_genericPart (Y : Model Xo c β) (hβ : IsDedFrac β) (U : Y.X.Opens) (hU : (U : Set Y.X) = abLocus Y.t.G) :
    ∃ j : Xo.XF c ⟶ U.toScheme, j ≫ U.ι = Y.j ∧ IsPullback j (pullback.snd _ _) (U.ι ≫ Y.s) (spMap β) ∧
      IsLocallyNoetherian U.toScheme ∧ Geo.Tor.IsNormalScheme U.toScheme ∧ IsPreimmersion j ∧ Flat j ∧
      IsDominant j ∧ QuasiCompact j := by
  obtain ⟨⟨_, hD⟩, _, hF⟩ := hβ
  letI : Algebra O c.F := β.toAlgebra
  obtain ⟨hN, -, -, j₁, j₂, j₃, j₄⟩ := genericPart_dense_proOpen O c.F Y.X (Xo.XF c) Y.s Y.jQ Y.flat Y.proj
    Y.jQ_open Y.jQ_dense
  replace j₁ : IsPreimmersion Y.j := j₁
  replace j₂ : Flat Y.j := j₂
  replace j₃ : IsDominant Y.j := j₃
  replace j₄ : QuasiCompact Y.j := j₄
  have hr : Set.range Y.j ⊆ Set.range U.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι, hU]
    have : Y.jQ x ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G := by
      rw [Y.ab_gen]; exact ⟨_, rfl⟩
    exact this
  let j : Xo.XF c ⟶ U.toScheme := IsOpenImmersion.lift U.ι Y.j hr
  have hj : j ≫ U.ι = Y.j := IsOpenImmersion.lift_fac _ _ _
  have sq : IsPullback (𝟙 _) j Y.j U.ι := IsPullback.of_horiz_isIso_mono ⟨by simp [hj]⟩
  have := Y.jQ_open
  have pb : IsPullback j Y.jQ U.ι (pullback.fst Y.s (spMap β)) := by
    refine (IsOpenImmersion.isPullback j Y.jQ U.ι (pullback.fst Y.s (spMap β)) hj.symm ?_)
    ext x
    simp [hU, ← Y.ab_gen]
  refine ⟨j, hj, ?_, inferInstance, fun x => ?_, MorphismProperty.of_isPullback (P := @IsPreimmersion) sq j₁,
    MorphismProperty.of_isPullback (P := @Flat) sq j₂, ?_, MorphismProperty.of_isPullback (P := @QuasiCompact) sq j₄⟩
  · rw [← Y.jQ_over]
    exact pb.paste_vert (IsPullback.of_hasPullback _ _)
  · obtain ⟨_, _⟩ := Y.normal (U.ι x)
    let e := (asIso (U.ι.stalkMap x)).commRingCatIsoToRingEquiv
    exact ⟨e.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e⟩
  · constructor
    have hd := Dense.preimage j₃.denseRange U.ι.isOpenEmbedding.isOpenMap
    refine hd.mono ?_
    rintro y ⟨x, hx⟩
    refine ⟨x, U.ι.isOpenEmbedding.injective ?_⟩
    rw [← hx, ← hj]; rfl

theorem map_nsmul_of_add {La A : Type} [AddCommGroup La] [Group A] (e : La → A) (he : ∀ a b, e (a + b) = e a * e b)
    (k : ℕ) (a : La) : e (k • a) = e a ^ k :=
  map_pow (MonoidHom.mk' (fun x : Multiplicative La => e x.toAdd) fun _ _ => he _ _) (Multiplicative.ofAdd a) k

theorem levels_pow {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B} (o : Obj D l b s)
    (x y : D.La) : (o.eta x * o.etaA y) ^ (l.M * l.A) = 1 := by
  have h₁ : o.eta x ^ l.M = 1 := by
    rw [← map_nsmul_of_add _ o.eta_add, ← Nat.cast_smul_eq_nsmul (𝓞 E)]
    refine o.eta_ker _ (Submodule.smul_mem_smul ?_ trivial)
    have : (l.M : 𝓞 E) ∈ Ideal.span {(l.M : 𝓞 E)} := Ideal.subset_span rfl
    rw [← l.prod] at this
    exact (Ideal.mul_le_inf (I := l.Mb) this).1
  have h₂ : o.etaA y ^ l.A = 1 := by rw [← map_nsmul_of_add _ o.etaA_add, o.etaA_ker]
  rw [mul_pow, pow_mul, h₁, one_pow, _root_.mul_comm l.M, pow_mul, h₂, one_pow, _root_.one_mul]

theorem exists_levelImage (L₁ : Out.Laws) (L₂ : Out.Laws2) (L₃ : Out.Laws3) [Module.Free ℤ D.La] [Module.Finite ℤ D.La]
    (Y : Model Xo c β) (hβ : IsDedFrac β) (U : Y.X.Opens) (hU : (U : Set Y.X) = abLocus Y.t.G)
    (hn : IsUnit ((l.M * l.A : ℕ) : O)) {T : Scheme.{0}} (sT : T ⟶ Sp O) [LocallyOfFiniteType sT] [QuasiCompact sT]
    (tT : SAB H T) (hT : IsProper tT.G.hom) (f : U.toScheme ⟶ T) [IsFinite f] (hf : f ≫ sT = U.ι ≫ Y.s)
    (tU : SAB H U.toScheme) (m₁ : SABMap tU Y.t U.ι) (m₂ : SABMap tU tT f) :
    ∃ (XX : Scheme.{0}) (u : U.toScheme ⟶ XX) (i : XX ⟶ T) (W : XX.Opens) (t : SAB H XX) (m : SABMap tU t u)
      (η' ηA' : D.La → (𝟙_ (Over XX) ⟶ t.G)),
      u ≫ i = f ∧ IsFinite u ∧ Surjective u ∧ Dense (W : Set XX) ∧ IsIso (u ∣_ W) ∧
      Dense ((u ⁻¹ᵁ W : U.toScheme.Opens) : Set U.toScheme) ∧
      IsAbelianScheme t.G ∧ IsReduced XX ∧ Flat (i ≫ sT) ∧ IsFinite i ∧ FormallyUnramified i ∧
      ∀ (a : D.La) (j' : Xo.XF c ⟶ U.toScheme) (g₁ : Xo.XF c ⟶ tU.G.left), j' ≫ U.ι = Y.j →
        (g₁ ≫ m₁.φ = (Y.oF.eta a).left ≫ Y.m.φ → g₁ ≫ m.φ = j' ≫ u ≫ (η' a).left) ∧
        (g₁ ≫ m₁.φ = (Y.oF.etaA a).left ≫ Y.m.φ → g₁ ≫ m.φ = j' ≫ u ≫ (ηA' a).left) := by
  obtain ⟨j, hj, pb, hN, hnorm, j₁, j₂, j₃, j₄⟩ := exists_genericPart Y hβ U hU
  obtain ⟨⟨_, hD⟩, _, hF⟩ := hβ
  letI : Algebra O c.F := β.toAlgebra
  have hn' : IsUnit ((l.M * l.A : ℕ) : Γ(T, ⊤)) := by
    simpa using hn.map (sT.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom)
  obtain ⟨Z, et, z₁, z₂, -, -, hZ⟩ := exists_finiteEtale_latticeTorsionHom T tT.G (l.M * l.A) (D.La × D.La)
    (isAbelianScheme_of_proper tT hT) hn'
  obtain ⟨ν₀, hν₀⟩ := exists_cancel m₁ Y.m j hj
  obtain ⟨ν₁, hν₁⟩ := sabComp pullCubComp E H _ _ _ tT tU Y.oF.t f j m₂ ν₀
  obtain ⟨h, hh, -⟩ := hZ _ (fun x => pushHom ν₁.cart _ (Y.oF.eta x.1 * Y.oF.etaA x.2))
    (fun x y => by
      rw [← map_mul, Prod.fst_add, Prod.snd_add, Y.oF.eta_add, Y.oF.etaA_add, _root_.mul_mul_mul_comm])
    (fun x => by rw [← map_pow, levels_pow, map_one])
  have e₀ : Y.oF.eta 0 = 1 := Y.oF.eta_ker 0 (Submodule.zero_mem _)
  have e₀' : Y.oF.etaA 0 = 1 := by simpa using Y.oF.etaA_ker 0
  obtain ⟨k, hk⟩ : ∃ k : Xo.XF c ⟶ Z.left, k = h.left := ⟨_, rfl⟩
  have hw : k ≫ Z.hom = j ≫ f := by rw [hk]; exact (Over.w h).trans (Category.id_comp _)
  have k₁ : ∀ a, k ≫ (et (a, 0)).left = (Y.oF.eta a).left ≫ ν₁.φ := fun a => by
    have := congrArg (fun z => z.left) (hh (a, 0))
    rw [hk]
    simp only [e₀', _root_.mul_one] at this
    exact this
  have k₂ : ∀ a, k ≫ (et (0, a)).left = (Y.oF.etaA a).left ≫ ν₁.φ := fun a => by
    have := congrArg (fun z => z.left) (hh (0, a))
    rw [hk]
    simp only [e₀, _root_.one_mul] at this
    exact this
  obtain ⟨u₀, ⟨hu₁, hu₂⟩, -⟩ := existsUnique_lift_of_densePart _ _ _ _ j hnorm j₁ j₂ j₃ j₄ Z.hom f k inferInstance hw
  have hu₀ : IsFinite u₀ := by
    have : IsFinite (u₀ ≫ Z.hom) := by rw [hu₂]; infer_instance
    exact IsFinite.of_comp _ Z.hom
  have hs : u₀ ≫ Z.hom ≫ sT = U.ι ≫ Y.s := by rw [reassoc_of% hu₂, hf]

  let p : pullback (Z.hom ≫ sT) (spMap β) ⟶ Z.left := pullback.fst _ _
  let g : Xo.XF c ⟶ pullback (Z.hom ≫ sT) (spMap β) :=
    pullback.lift k (pullback.snd _ _) (by rw [← hu₁, Category.assoc, hs, pb.w])
  have hg₁ : g ≫ p = k := pullback.lift_fst _ _ _
  have hg₂ : g ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  have pb' : IsPullback j g u₀ p :=
    IsPullback.of_bot (by rw [hs, hg₂]; exact pb) (by rw [hu₁, hg₁]) (IsPullback.of_hasPullback _ _)
  obtain ⟨tF, ⟨mF⟩⟩ := exists_pull L₃.cubePull (p ≫ Z.hom) tT
  obtain ⟨νF, hνF⟩ := exists_cancel mF ν₁ g (by rw [reassoc_of% hg₁, hw])
  choose σ hσ using fun x => exists_section mF (p ≫ (et x).left) (by rw [Category.assoc, Over.w])
  have key : ∀ {X : Scheme.{0}} {q : X ⟶ Z.left} {t : SAB H X} (mX : SABMap t tT (q ≫ Z.hom)) (r : Xo.XF c ⟶ X)
      (y : Xo.XF c ⟶ t.G.left) (x : D.La × D.La) (τ : 𝟙_ (Over X) ⟶ t.G) (e : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G),
      r ≫ q = k → τ.left ≫ mX.φ = q ≫ (et x).left → k ≫ (et x).left = e.left ≫ ν₁.φ →
      y ≫ mX.φ = e.left ≫ ν₁.φ → y ≫ t.G.hom = r → y = r ≫ τ.left := by
    intro X q t mX r y x τ e a₁ a₂ a₃ a₄ a₅
    apply mX.cart.1.hom_ext
    · rw [Category.assoc]
      erw [a₂]
      rw [reassoc_of% a₁, a₃, a₄]
    · rw [a₅, Category.assoc]
      erw [Over.w τ]
      exact (Category.comp_id _).symm
  have hsec : ∀ {X : Scheme.{0}} {t : SAB H X} {r : Xo.XF c ⟶ X} (ν : SABMap Y.oF.t t r)
      (e : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G), (e.left ≫ ν.φ) ≫ t.G.hom = r := by
    intro X t r ν e
    rw [Category.assoc, ν.cart.1.w, ← Category.assoc, Over.w e]
    exact Category.id_comp _
  have hcl : IsClosedImmersion g := moduli_isClosedImmersion L₁ L₂ L₃ E H D l Xo c Y.oF Y.m0 _ (pullback.snd _ _) tF g νF
    (fun a => σ (a, 0)) (fun a => σ (0, a)) hg₂
    (fun a => key mF g _ _ _ _ hg₁ (hσ _) (k₁ a) (by rw [← hνF]; exact Category.assoc _ _ _) (hsec νF _))
    (fun a => key mF g _ _ _ _ hg₁ (hσ _) (k₂ a) (by rw [← hνF]; exact Category.assoc _ _ _) (hsec νF _))
    (MorphismProperty.of_isPullback (P := @IsFinite) pb' hu₀)
  have hred : IsReduced U.toScheme := by
    have : ∀ x : U.toScheme, _root_.IsReduced (U.toScheme.presheaf.stalk x) := fun x => by
      obtain ⟨_, _⟩ := hnorm x
      infer_instance
    exact isReduced_of_isReduced_stalk _
  have := Y.flat
  obtain ⟨XX, u, i, W, a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉⟩ := FiniteImage.main O c.F _ _ u₀ (Z.hom ≫ sT) hu₀ hred
    (by rw [hs]; infer_instance) inferInstance inferInstance (by
      have e : pb'.isoPullback.inv ≫ g = pullback.snd u₀ p := pb'.isoPullback_inv_snd
      change IsClosedImmersion (pullback.snd u₀ p)
      rw [← e]; infer_instance)
  obtain ⟨t, ⟨mt⟩⟩ := exists_pull L₃.cubePull (i ≫ Z.hom) tT
  obtain ⟨m, hm⟩ := exists_cancel mt m₂ u (by rw [reassoc_of% a₁, hu₂])
  choose τ hτ using fun x => exists_section mt (i ≫ (et x).left) (by rw [Category.assoc, Over.w])
  refine ⟨XX, u, i ≫ Z.hom, W, t, m, fun a => τ (a, 0), fun a => τ (0, a), by rw [reassoc_of% a₁, hu₂], a₃, a₄, a₅,
    a₆, a₇, isAbelianScheme_of_proper t (MorphismProperty.of_isPullback (P := @IsProper) mt.cart.1 hT), a₈,
    by rw [Category.assoc]; exact a₉, inferInstance,
    MorphismProperty.comp_mem @FormallyUnramified _ _ inferInstance inferInstance, fun a j' g₁ hj' => ?_⟩
  obtain rfl : j' = j := by rw [← cancel_mono U.ι, hj, hj']
  have : Mono m₁.φ := MorphismProperty.of_isPullback (P := .monomorphisms _) m₁.cart.1.flip
    (inferInstanceAs (Mono U.ι))
  have fin : ∀ (x : D.La × D.La) (e : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G), k ≫ (et x).left = e.left ≫ ν₁.φ →
      g₁ ≫ m₁.φ = e.left ≫ Y.m.φ → g₁ ≫ m.φ = j' ≫ u ≫ (τ x).left := by
    intro x e b₁ b₂
    have b₃ : g₁ = e.left ≫ ν₀.φ := by
      rw [← cancel_mono m₁.φ, b₂, ← hν₀]; exact (Category.assoc _ _ _).symm
    refine (key mt (j' ≫ u) _ x _ e (by rw [Category.assoc, a₁, hu₁]) (hτ x) b₁ ?_ ?_).trans (Category.assoc _ _ _)
    · rw [Category.assoc, hm, hν₁, b₃]; exact Category.assoc _ _ _
    · rw [Category.assoc, m.cart.1.w, ← Category.assoc, b₃]
      exact congrArg (· ≫ u) (hsec ν₀ e)
  exact ⟨fin _ _ (k₁ a), fin _ _ (k₂ a)⟩

theorem exists_int_mul_mem {F : Type} [Field F] [Algebra ℚ F] [FiniteDimensional ℚ F] (V : ValuationSubring F) (x : F) :
    ∃ (m : ℤ) (y : V), m ≠ 0 ∧ x * m = y := by
  obtain ⟨m, hm, h⟩ := exists_integral_multiples ℤ ℚ (L := F) {x}
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := V) (K := F)).1 (h x (Finset.mem_singleton_self x)).tower_top
  refine ⟨m, y, hm, ?_⟩
  rw [_root_.mul_comm, ← zsmul_eq_mul]
  exact hy.symm

theorem section_comp {S S' : Scheme.{0}} {f : S' ⟶ S} {t : SAB H S} {t' : SAB H S'} (m : SABMap t' t f)
    (e : 𝟙_ (Over S') ⟶ t'.G) : (e.left ≫ m.φ) ≫ t.G.hom = f := by
  rw [Category.assoc, m.cart.1.w, ← Category.assoc, Over.w e]
  exact Category.id_comp _

theorem eq_comp_section {X S S' : Scheme.{0}} {f : S' ⟶ S} {t : SAB H S} {t' : SAB H S'} (m : SABMap t' t f)
    (r : X ⟶ S') (y : X ⟶ t'.G.left) (τ : 𝟙_ (Over S') ⟶ t'.G) (x : S' ⟶ t.G.left) (h₁ : τ.left ≫ m.φ = x)
    (h₂ : y ≫ m.φ = r ≫ x) (h₃ : y ≫ t'.G.hom = r) : y = r ≫ τ.left := by
  apply m.cart.1.hom_ext
  · exact h₂.trans ((congrArg (r ≫ ·) h₁.symm).trans (Category.assoc _ _ _).symm)
  · exact h₃.trans (((Category.assoc _ _ _).trans (congrArg (r ≫ ·) (Over.w τ))).trans (Category.comp_id _)).symm

theorem comp_section {X S : Scheme.{0}} {G : Over S} (r : X ⟶ S) (τ : 𝟙_ (Over S) ⟶ G) :
    (r ≫ τ.left) ≫ G.hom = r :=
  ((Category.assoc _ _ _).trans (congrArg (r ≫ ·) (Over.w τ))).trans (Category.comp_id _)

theorem siegelCompare : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (T : Top Xo n N), ToroidalLevelCompatibility (H := H) (D := D) → ∀ p : ℕ, p.Prime → p ≠ n → n.Prime → (∃ e, N = n ^ e) → ∃ Ag : SiegelFamily (Module.finrank ℚ E / 2 * (D.p + D.q)) p N, ∀ (W : ValuationSubring ℂ) (l₀ : Level H) (B : BaseModel T l₀) (l l₁ : Level H) (c : Coeff l) (c₁ : Coeff l₁) (Y : Model (Xo l) c (c.V W).subtype) (Y₁ : Model (Xo l₁) c₁ (c₁.V W).subtype) (b : c.V W →+* c₁.V W) (z : ZP p N →+* c₁.V W) (π : Y₁.X ⟶ Y.X), (p : ℂ) ∈ W.nonunits → IsPrimeToPart l₀ l p → n.Coprime l.M → IsIncl b → (∀ x, (((z x : c₁.V W) : c₁.F) : ℂ) = (x : ℂ)) → l₁.M = l.M → l₁.Mb = l.Mb → l₁.A = Nat.lcm l.A N → c₁.F = c.F ⊔ IntermediateField.adjoin ℚ {zeta N} → Raises B Y → Raises B Y₁ → IsTransition Y Y₁ b π → SiegelCompare Y Y₁ b π Ag z := by
  intro L₁ L₂ L₃ E _ _ _ H D Xo n N T hN₁ p hp hpn hn ⟨e, hN⟩
  obtain ⟨Ag, bas, hbas, hs⟩ := T.sieg p hp hpn
  refine ⟨Ag, fun W l₀ B l l₁ c c₁ Y Y₁ b z π hW hl₀ _ hb hz hM hMb hA hF hR hR₁ htr U U₁ hU hU₁ => ?_⟩
  have hnp : n.Coprime p := (Nat.coprime_primes hn hp).2 hpn.symm
  have hNp : N.Coprime p := hN ▸ hnp.pow_left e
  have hN0 : 0 < N := hN ▸ pow_pos hn.pos e
  obtain ⟨ded, unit, -⟩ := (CoeffRings.coeff_isDedFrac E H l c).2.2.2 p W hp hW
  obtain ⟨ded₁, unit₁, rz₁⟩ := (CoeffRings.coeff_isDedFrac E H l₁ c₁).2.2.2 p W hp hW
  refine ⟨?_, ?_⟩
  · have ab : AbOpen Y.t.G := by
      obtain ⟨_, r, ν, -, -, ⟨a⟩⟩ := hR
      exact (good_pullback L₃.gtBaseChange E H _ _ B.C.t Y.t a.π a.mu B.good).1
    refine AbelianLocusCover.abelianLocus_finite_etale L₁ L₂ L₃ E H D Xo hN₁ l c _ _ Y l₁ c₁ _ _ Y₁ b π N ded ded₁ hb
      (etale_coeff_adjoin_zeta E H l l₁ c c₁ p N W hp hW hNp hN0 hF b hb) ⟨n, e, hn, unit n hnp, hN⟩ hM hMb hA
      (hF ▸ le_sup_left) (fun x => ?_) ab htr U U₁ hU hU₁
    have := c₁.fin
    have := ded.2.1
    obtain ⟨m, y, hm, h⟩ := exists_int_mul_mem (c₁.V W) x
    exact ⟨y, m, Int.cast_ne_zero.2 hm, by rw [map_intCast, map_intCast]; exact h⟩
  obtain ⟨hd, hcop, -⟩ := (primeToPart_spec E H p hp).2.1 l l₀ hl₀
  obtain ⟨b', hb'⟩ := rz₁ n N hnp hN0
    (hF ▸ (le_sup_right : _ ≤ c.F ⊔ IntermediateField.adjoin ℚ {zeta N}) (IntermediateField.mem_adjoin_simple_self ℚ _))
  obtain ⟨f, hf, tU, m₁, m₂, hfin, hlev⟩ := AbelianLocusMap.exists_finite_map L₁ L₂ L₃ E H D Xo n N T hN₁ l₀ B l₁ c₁ _ _
    Y₁ b' U₁ hn.pos ⟨e, hN ▸ dvd_rfl⟩ ⟨hM ▸ hd.1, hMb ▸ hd.2.1, hA ▸ hd.2.2.trans (Nat.dvd_lcm_left _ _)⟩
    (hA ▸ Nat.dvd_lcm_right _ _) (by
      have := unit₁ (n * l₀.M) (Nat.Coprime.mul_left hnp hcop)
      rw [Nat.cast_mul] at this
      exact this) ded₁ hb' hR₁ hU₁
  obtain ⟨f', hf₁, hf₂, hfin⟩ : ∃ f' : U₁.toScheme ⟶ pullback T.sM (spMap b'),
      f' ≫ pullback.fst _ _ = f ∧ f' ≫ pullback.snd _ _ = U₁.ι ≫ Y₁.s ∧ IsFinite f' :=
    ⟨_, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, hfin⟩
  obtain ⟨tT, ⟨mT⟩⟩ := exists_pull L₃.cubePull (pullback.fst T.sM (spMap b')) T.tM
  choose levT hlevT using fun x => exists_section mT _ (comp_section (pullback.fst T.sM (spMap b')) (T.lev x))
  choose lev' hlev' using fun x => exists_section m₂ _ (comp_section f (T.lev x))
  obtain ⟨ν', hν'⟩ := exists_cancel mT m₂ f' hf₁
  obtain ⟨w, hw, w₁, w₂⟩ := hs _ (c₁.F.val.toRingHom.comp (c₁.V W).subtype) z b'
    (Subtype.val_injective.comp Subtype.val_injective) hz hb' _ _ _ tT mT levT (IsPullback.of_hasPullback _ _) hlevT
  have hw' : w ≫ pullback.snd _ _ = pullback.snd T.sM (spMap b') := by
    obtain ⟨_, _, _, -, -, -, -, h, -⟩ := hw
    exact h
  have hd := GlobalTheory.SiegelDataPull.siegData_pull E H D _ _ _ _ f' tT tU ν' levT lev' _ p N Ag z bas w (fun x =>
    eq_comp_section mT f' _ _ _ (hlevT x)
      (((Category.assoc _ _ _).trans (congrArg ((lev' x).left ≫ ·) hν')).trans ((hlev' x).trans
        ((congrArg (· ≫ (T.lev x).left) hf₁.symm).trans (Category.assoc _ _ _))))
      (section_comp ν' _)) hw
  rw [hf₂, SiegData, Category.assoc U₁.ι] at hd
  obtain ⟨o, φ, φ₂, o₁, o₂, o₃, o₄, o₅, o₆⟩ := hd
  obtain ⟨q, q₁, q₂⟩ := exists_square m₁
  refine ⟨bas, f' ≫ w, o, φ ≫ m₁.φ, φ₂ ≫ q, hbas, (o₁.comp m₁.cart).congr (Category.id_comp _) rfl, ⟨?_, ?_⟩,
    LBIso.trans o.isLB (pull_isLB (DVR.linComb_isLB _ tU.PP.isLB _ _) _) (pull_isLB (DVR.linComb_isLB _ Y₁.t.PP.isLB _ _) _)
      o₃ (q₂ _ φ₂), fun u j' hj' => ?_, o₅, o₆, inferInstance, fun hM' => ?_⟩
  · rw [Category.assoc, q₁.1, reassoc_of% o₂.1]
  · rw [Category.assoc, q₁.2, reassoc_of% o₂.2]
  · obtain ⟨ν₀, hν₀⟩ := exists_cancel m₁ Y₁.m j' hj'
    have a₁ : ((Y₁.oF.etaA (bas u) ^ (l₁.A / N)).left ≫ ν₀.φ) ≫ m₁.φ =
        (Y₁.oF.etaA (bas u) ^ (l₁.A / N)).left ≫ Y₁.m.φ :=
      (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hν₀)
    have a₂ := eq_comp_section m₂ j' _ _ _ (hlev' (bas u)) (hlev (bas u) j' _ hj' a₁) (section_comp ν₀ _)
    refine Eq.trans ?_ a₁
    rw [a₂, ← o₄]
    exact ((Category.assoc _ _ _).trans (congrArg (j' ≫ ·) (Category.assoc _ _ _))).symm
  · have : Module.Free ℤ D.La := Module.Free.of_equiv bas
    have : Module.Finite ℤ D.La := Module.Finite.equiv bas
    have := Ag.qc
    have : Smooth Ag.s := @SmoothOfRelativeDimension.smooth _ _ _ Ag.s Ag.smooth
    have : LocallyOfFiniteType (pullback.snd T.sM (spMap b')) := by rw [← hw']; infer_instance
    have : QuasiCompact (pullback.snd T.sM (spMap b')) := by rw [← hw']; infer_instance
    have hc : l.M'.Coprime p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hM').symm
    have hc' : (l₁.M * l₁.A).Coprime p := by
      rw [hM, hA]
      exact Nat.Coprime.mul_left (hc.coprime_dvd_left (Nat.dvd_lcm_left _ _))
        ((Nat.Coprime.mul_left (hc.coprime_dvd_left (Nat.dvd_lcm_right _ _)) hNp).coprime_dvd_left
          (Nat.lcm_dvd_mul _ _))
    obtain ⟨XX, u, i, V, t, m, η', ηA', a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, b₁, b₂, b₃⟩ :=
      exists_levelImage L₁ L₂ L₃ Y₁ ded₁ U₁ hU₁ (unit₁ _ hc') (pullback.snd T.sM (spMap b')) tT
        (MorphismProperty.of_isPullback (P := @IsProper) mT.cart.1 T.MM_ab) f' hf₂ tU m₁ ν'
    exact ⟨XX, u, i ≫ w, V, t, tU, m₁, m, η', ηA', by rw [reassoc_of% a₁], a₂, a₃, a₄, a₅, a₆, a₇, a₈,
      by rw [Category.assoc, hw']; exact a₉, inferInstance,
      MorphismProperty.comp_mem @FormallyUnramified _ _ b₂ w₂, b₃⟩

end GlobalTheory.SiegelComparison
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModelsSiegelFamilyComparisonStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_models_siegel_family_comparison : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (T : Top Xo n N), ToroidalLevelCompatibility (H := H) (D := D) → ∀ p : ℕ, p.Prime → p ≠ n → n.Prime → (∃ e, N = n ^ e) → ∃ Ag : SiegelFamily (Module.finrank ℚ E / 2 * (D.p + D.q)) p N, ∀ (W : ValuationSubring ℂ) (l₀ : Level H) (B : BaseModel T l₀) (l l₁ : Level H) (c : Coeff l) (c₁ : Coeff l₁) (Y : Model (Xo l) c (c.V W).subtype) (Y₁ : Model (Xo l₁) c₁ (c₁.V W).subtype) (b : c.V W →+* c₁.V W) (z : ZP p N →+* c₁.V W) (π : Y₁.X ⟶ Y.X), (p : ℂ) ∈ W.nonunits → IsPrimeToPart l₀ l p → n.Coprime l.M → IsIncl b → (∀ x, (((z x : c₁.V W) : c₁.F) : ℂ) = (x : ℂ)) → l₁.M = l.M → l₁.Mb = l.Mb → l₁.A = Nat.lcm l.A N → c₁.F = c.F ⊔ IntermediateField.adjoin ℚ {zeta N} → Raises B Y → Raises B Y₁ → IsTransition Y Y₁ b π → SiegelCompare Y Y₁ b π Ag z := by
  first | exact @GlobalTheory.SiegelComparison.siegelCompare | exact GlobalTheory.SiegelComparison.siegelCompare | (intros; apply GlobalTheory.SiegelComparison.siegelCompare <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LocalModelSystemTransitionSiegelClauses
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.Models

section Incl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l l₂ : Level H} {c : Coeff l}
  {c₂ : Coeff l₂} {W : ValuationSubring ℂ}

theorem exists_isIncl (hc : c.F ≤ c₂.F) : ∃ b : c.V W →+* c₂.V W, IsIncl b := by
  refine ⟨RingHom.codRestrict ((IntermediateField.inclusion hc).toRingHom.comp (c.V W).subtype) (c₂.V W)
    (fun x => x.2), fun x => rfl⟩

theorem isIncl_unique {b b' : c.V W →+* c₂.V W} (hb : IsIncl b) (hb' : IsIncl b') : b = b' := by
  refine RingHom.ext fun x => Subtype.ext (Subtype.ext ?_)
  exact (hb x).trans (hb' x).symm

end Incl

theorem system_clauses : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), 1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) → ∀ (S : System Xo) p W hp hW, N2 (S.Y p W hp hW) := by
  intro hext L1 L2 L3 E _ _ _ H D Xo hD hN S p W hp hW
  refine ⟨fun i => (GlobalTheory.T.localModel_oneModel_and_splitFibres hext L1 L2 L3 E H D Xo hD hN S p W hp hW i).1, ?_⟩
  obtain ⟨hnp, hodd, h3, h4⟩ := S.aux (S.ch p)
  have hcop := (GlobalTheory.T.exists_two_inert_odd_primes_coprime_level E H).2 _ (S.aux (S.ch p))
  obtain ⟨-, hl2, hl3⟩ := GlobalTheory.T.primeToPart_level_exists_unique_mono E H p hp
  have key : ∀ i i₂ : Idx H p, i.l.Dvd i₂.l → i.c.F ≤ i₂.c.F →
      ∃ π : (S.Y p W hp hW i₂).X ⟶ (S.Y p W hp hW i).X, ∀ b : i.c.V W →+* i₂.c.V W, IsIncl b →
        IsTransition (S.Y p W hp hW i) (S.Y p W hp hW i₂) b π := by
    intro i i₂ hl hc
    obtain ⟨b, hb⟩ := exists_isIncl (W := W) hc
    obtain ⟨l₀, h₀, hr⟩ := S.raises p W hp hW i
    obtain ⟨l₀', h₀', hr'⟩ := S.raises p W hp hW i₂
    obtain ⟨π, hπ⟩ := GlobalTheory.T.exists_transition_map_raised_models hext L1 L2 L3 E H D Xo _ _ (S.T (S.ch p)) hN l₀ l₀' _ _ i.l i.c _ _
      (S.Y p W hp hW i) i₂.l i₂.c _ _ (S.Y p W hp hW i₂) b hnp.pos ⟨_, dvd_rfl⟩ (hl3 _ _ _ _ h₀ h₀' hl)
      (hl2 _ _ h₀).1 (hl2 _ _ h₀').1 hl hc ((GlobalTheory.T.coefficientField_integers_dedekind_fractionField E H i.l i.c).2.2.2 p W hp hW).1
      ((GlobalTheory.T.coefficientField_integers_dedekind_fractionField E H i₂.l i₂.c).2.2.2 p W hp hW).1 hb hr hr'
    exact ⟨π, fun b' hb' => isIncl_unique hb hb' ▸ hπ⟩
  choose π hπ using key
  obtain ⟨Ag, hAg⟩ := GlobalTheory.T.cm_models_siegel_family_comparison L1 L2 L3 E H D Xo _ _ (S.T (S.ch p)) hN p hp (S.ch_ne p).symm hnp ⟨_, rfl⟩
  refine ⟨π, hπ, S.n (S.ch p), S.J (S.ch p), Ag, hnp, hodd, S.ch_ne p, ?_, hcop, ?_⟩
  · have h2 : 3 ≤ S.n (S.ch p) := by
      have := hnp.two_le
      obtain ⟨k, hk⟩ := hodd
      omega
    exact h2.trans (Nat.le_self_pow (by have := S.J_pos (S.ch p); omega) _)
  · intro i i₁ hl hc b z hb hz hM hMb hA hF
    obtain ⟨l₀, h₀, hr⟩ := S.raises p W hp hW i
    obtain ⟨l₀', h₀', hr'⟩ := S.raises p W hp hW i₁
    have h₁ : IsPrimeToPart l₀' i.l p := by
      obtain ⟨a1, a2, a3⟩ := h₀'
      exact ⟨a1, hM ▸ a2, hMb ▸ a3⟩
    obtain rfl : l₀' = l₀ := (hl2 _ _ h₀).2.2 _ h₁
    exact hAg W l₀' _ i.l i₁.l i.c i₁.c _ _ b z _ hW h₀ (hcop _) hb hz hM hMb hA hF hr hr' (hπ i i₁ hl hc b hb)

end GlobalTheory.Models
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LocalModelSystemTransitionSiegelClausesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localModelSystem_transition_siegel_clauses : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), 1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) → ∀ (S : System Xo) p W hp hW, N2 (S.Y p W hp hW) := by
  first | exact @GlobalTheory.Models.system_clauses | exact GlobalTheory.Models.system_clauses | (intros; apply GlobalTheory.Models.system_clauses <;> assumption)
end
