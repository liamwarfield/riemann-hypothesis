module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecOfLeChart
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.OriginLineBundlePolarisation

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsAbelianSchemeModelOfIsogenyDedekind
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory

namespace TorsionKernelModel

theorem exists_kernel {S : Scheme.{0}} {G H : Over S} [GrpObj G] [GrpObj H] [IsSeparated H.hom] (f : G ⟶ H)
    [IsMonHom f] :
    ∃ (Z : Over S) (_ : GrpObj Z) (i : Z ⟶ G), IsMonHom i ∧ IsClosedImmersion i.left ∧
      IsPullback i (toUnit Z) f η[H] := by
  have hk : IsPullback (pullback.fst f η[H]) (toUnit _) f η[H] := by
    have := IsPullback.of_hasPullback f η[H]
    rwa [toUnit_unique (pullback.snd f η[H]) (toUnit _)] at this
  generalize pullback.fst f η[H] = i at hk
  generalize pullback f η[H] = Z at i hk
  have h₁ : IsClosedImmersion (η[H].left ≫ H.hom) := by
    rw [Over.w]; exact inferInstanceAs (IsClosedImmersion (𝟙 S))
  have h₂ : IsClosedImmersion η[H].left := IsClosedImmersion.of_comp _ H.hom
  have h₃ : IsClosedImmersion i.left :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) (hk.map (Over.forget S)).flip h₂
  have hm : Mono i := (Over.forget S).mono_of_mono_map (inferInstanceAs (Mono i.left))
  have hi : i ≫ f = 1 := hk.w
  obtain ⟨_, hG⟩ := exists_grpObj_of_mono i
    (hk.lift η[G] (toUnit _) (by simp))
    (hk.lift ((fst Z Z ≫ i) * (snd Z Z ≫ i)) (toUnit _) (by
      rw [MonObj.mul_comp, Category.assoc, Category.assoc, hi, MonObj.comp_one, MonObj.comp_one, _root_.mul_one,
        Hom.one_def]))
    (hk.lift i⁻¹ (toUnit _) (by rw [GrpObj.inv_comp, hi, inv_one, Hom.one_def]))
    (hk.lift_fst _ _ _) ((hk.lift_fst _ _ _).trans (by rw [Hom.mul_def, lift_fst_comp_snd_comp]))
    ((hk.lift_fst _ _ _).trans (Hom.inv_def _))
  exact ⟨Z, _, i, hG, h₃, hk⟩

theorem isPullback_kernel_baseChange {S S' : Scheme.{0}} (j : S' ⟶ S) {Z G H : Over S} [GrpObj H]
    {i : Z ⟶ G} {f : G ⟶ H} (h : IsPullback i (toUnit Z) f η[H]) :
    IsPullback ((Over.pullback j).map i) (toUnit _) ((Over.pullback j).map f) η[(Over.pullback j).obj H] := by
  refine (h.map (Over.pullback j)).of_iso (Iso.refl _) (Iso.refl _) (Functor.Monoidal.εIso (Over.pullback j)).symm
    (Iso.refl _) (by simp) (toUnit_unique _ _) (by simp) ?_
  simp [Functor.obj.η_def]

theorem isFinite_of_pow_eq_one {S : Scheme.{0}} {Z G : Over S} [GrpObj G] [IsSeparated G.hom] (i : Z ⟶ G)
    [IsClosedImmersion i.left] (n : ℕ) [hn : IsFinite (𝟙 G ^ n).left] (h : i ^ n = 1) : IsFinite Z.hom := by
  have h₁ : IsClosedImmersion (η[G].left ≫ G.hom) := by
    rw [Over.w]; exact inferInstanceAs (IsClosedImmersion (𝟙 S))
  have h₂ : IsClosedImmersion η[G].left := IsClosedImmersion.of_comp _ G.hom
  have e₁ : i ≫ (𝟙 G ^ n) = toUnit Z ≫ η[G] := by
    rw [MonObj.comp_pow, Category.comp_id, h, Hom.one_def]
  have e₂ : i.left ≫ (𝟙 G ^ n).left = Z.hom ≫ η[G].left := by
    rw [← Over.comp_left, e₁]; simp
  let l : Z.left ⟶ pullback (𝟙 G ^ n).left η[G].left := pullback.lift i.left Z.hom e₂
  have h₃ : IsClosedImmersion (l ≫ pullback.fst _ _) := by
    rw [pullback.lift_fst]; infer_instance
  have h₄ : IsClosedImmersion l := IsClosedImmersion.of_comp l (pullback.fst _ _)
  have e₃ : l ≫ pullback.snd _ _ = Z.hom := pullback.lift_snd _ _ _
  rw [← e₃]
  infer_instance

end TorsionKernelModel


open TorsionKernelModel in
theorem exists_abelianScheme_model_of_isogeny_dedekind :
    Out.Laws → ∀ (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (P : Out.PolAV (Sp R)) (A₀ B₀ : Over (Sp K)) [GrpObj A₀] [GrpObj B₀] (φ : A₀.left ⟶ P.A.left) (ψ : A₀ ⟶ B₀) (n : ℕ), IsGrpPullback A₀ P.A (spMap (algebraMap R K)) φ → IsAbelianScheme B₀ → IsMonHom ψ → IsFinite ψ.left → Flat ψ.left → Surjective ψ.left → 1 ≤ n → (∀ (T : Over (Sp K)) (x : T ⟶ A₀), x ≫ ψ = 1 → x ^ n = 1) →
  ∃ (B : Over (Sp R)) (_ : GrpObj B) (φB : B₀.left ⟶ B.left) (Ψ : P.A ⟶ B), IsAbelianScheme B ∧ IsGrpPullback B₀ B (spMap (algebraMap R K)) φB ∧ IsMonHom Ψ ∧ IsFinite Ψ.left ∧ Flat Ψ.left ∧ Surjective Ψ.left ∧ ψ.left ≫ φB = φ ≫ Ψ.left := by
  intro hL R K _ _ _ _ _ P A₀ B₀ _ _ φ ψ n hφ hB _ _ _ _ hn hker
  obtain ⟨_, _⟩ := ExtUnique.spec_fractionRing R K
  have := P.isAb.proper
  have := hB.proper
  obtain ⟨a, ha, ha'⟩ := grpPullback_iso (isGrpPullback_pullback P.A _) hφ
  have : IsIso a.hom.left := inferInstanceAs (IsIso ((Over.forget _).map a.hom))
  obtain ⟨Z, _, i, _, hi, hZ⟩ := exists_kernel (a.hom ≫ ψ)
  obtain ⟨Ga, io, e, _, _, he⟩ := IsogenyModel.exists_flat_closure R K P.A Z i hi
  obtain ⟨_, _, -⟩ := exists_grpObj_of_flat_closed _ P.A Ga io Z i e he
  have hkill : (Over.pullback (spMap (algebraMap R K))).map io ≫ a.hom ≫ ψ = toUnit _ ≫ η[B₀] := by
    rw [← he, Category.assoc, hZ.w, comp_toUnit_assoc]
  have hpow : io ^ n = 1 := by
    apply ExtUnique.pullback_map_injective (spMap (algebraMap R K))
    have h₁ := hker _ ((Over.pullback (spMap (algebraMap R K))).map io ≫ a.hom) (by
      rw [Category.assoc, hkill, Hom.one_def])
    rw [← MonObj.pow_comp, ← MonObj.one_comp a.hom, cancel_mono] at h₁
    exact (map_pow (Over.pullback (spMap (algebraMap R K))).homMonoidHom io n).trans
      (h₁.trans (map_one (Over.pullback (spMap (algebraMap R K))).homMonoidHom).symm)
  have := (hL.mulN _ P n hn).1
  have hfin : IsFinite Ga.hom := isFinite_of_pow_eq_one io n hpow
  have hm : Mono io := (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono io.left))
  obtain ⟨B, _, hab, q, _, hq₁, hq₂, hq₃, hq⟩ := hL.quotient R P Ga io ‹_› hm hfin ‹_›
  have hq' := isPullback_kernel_baseChange (spMap (algebraMap R K)) hq
  have hqc : QuasiCompact q.left := inferInstance
  obtain ⟨β, _, hβ⟩ := flatQuotient_iso_of_same_kernel _ _ _ _ _ _
    ((Over.pullback (spMap (algebraMap R K))).map q) ((Over.pullback (spMap (algebraMap R K))).map io) (a.hom ≫ ψ) i
    inferInstance inferInstance
    (MorphismProperty.overPullbackMap (P := @Flat) _ q hq₂)
    (MorphismProperty.overPullbackMap (P := @Surjective) _ q hq₃)
    (MorphismProperty.overPullbackMap (P := @QuasiCompact) _ q hqc) hq' inferInstance inferInstance
    (by rw [Over.comp_left]; infer_instance) (by rw [Over.comp_left]; infer_instance)
    (by rw [Over.comp_left]; infer_instance) hZ
    (by rw [← e.inv_hom_id_assoc i, he, Category.assoc, hq'.w, comp_toUnit_assoc]) hkill
  refine ⟨B, _, β.hom.left ≫ pullback.fst B.hom (spMap (algebraMap R K)), q, hab,
    ((isGrpPullback_of_iso β).comp (isGrpPullback_pullback B _)).congr (Category.id_comp _) rfl,
    ‹_›, hq₁, hq₂, hq₃, ?_⟩
  rw [← cancel_epi a.hom.left, ← Category.assoc a.hom.left φ, ha', ← ExtUnique.pullback_map_left_fst, ← hβ]
  simp only [Over.comp_left, Category.assoc]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsogenyOfSurjectivePolAV
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsogenyOfSurjectivePolAV
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory

namespace SurjIsogeny

theorem eq_bot_of_comap_eq_bot {K R S : Type} [Field K] [CommRing R] [CommRing S] [IsDomain R]
    [IsDomain S] [Algebra K R] [Algebra K S] (φ : R →+* S)
    (hφ : φ.comp (algebraMap K R) = algebraMap K S) {g : ℕ}
    (hR : Algebra.trdeg K R = g) (hS : Algebra.trdeg K S = g) {p : Ideal S}
    (hp : p.comap φ = ⊥) : p = ⊥ := by
  algebraize [φ]
  have : IsScalarTower K R S := IsScalarTower.of_algebraMap_eq' hφ.symm
  have : FaithfulSMul R S := by
    rw [faithfulSMul_iff_algebraMap_injective, RingHom.injective_iff_ker_eq_bot, eq_bot_iff, ← hp]
    exact Ideal.comap_mono bot_le
  have h := trdeg_add_eq K R (A := S)
  rw [hR, hS] at h
  have h0 : Algebra.trdeg R S = 0 := by
    have h1 : Algebra.trdeg R S + g = 0 + g := by rw [add_comm, h, zero_add]
    exact (Cardinal.add_right_inj_of_lt_aleph0 Cardinal.natCast_lt_aleph0).1 h1
  have halg := trdeg_eq_zero_iff.1 h0
  by_contra hne
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact Ideal.comap_ne_bot_of_algebraic_mem hx0 hx (halg.1 x) hp

theorem eq_genericPoint_iff {X : Scheme.{0}} [IsIntegral X] {R : CommRingCat.{0}} [IsDomain R]
    (j : Spec R ⟶ X) [IsOpenImmersion j] (p : Spec R) :
    j p = genericPoint X ↔ p.asIdeal = ⊥ := by
  rw [← genericPoint_eq_of_isOpenImmersion j, j.isOpenEmbedding.injective.eq_iff,
    genericPoint_eq_bot_of_affine]
  exact ⟨fun h => h ▸ rfl, fun h => PrimeSpectrum.ext h⟩

theorem eq_genericPoint_of_apply_eq {K : Type} [Field K] {X Y : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] (f : X ⟶ Y) (s : Y ⟶ Spec (CommRingCat.of K)) {g : ℕ}
    (hY : SmoothOfRelativeDimension g s) (hX : SmoothOfRelativeDimension g (f ≫ s)) {x : X}
    (hx : f x = genericPoint Y) : x = genericPoint X := by
  obtain ⟨R, j, hj, y, hy⟩ := Scheme.exists_Spec_apply_eq (f x)
  obtain ⟨S, k, hk, ⟨p, rfl⟩, hsub⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (x := x) (U := f ⁻¹ᵁ j.opensRange) ⟨y, hy⟩
  have hr : Set.range (k ≫ f) ⊆ Set.range j := by
    rintro _ ⟨z, rfl⟩
    exact hsub ⟨z, rfl⟩
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift j (k ≫ f) hr)
  have hw : Spec.map φ ≫ j = k ≫ f := by rw [hφ, IsOpenImmersion.lift_fac]
  obtain ⟨α, hα⟩ := Spec.map_surjective (j ≫ s)
  have : Nonempty (Spec R) := ⟨y⟩
  have : Nonempty (Spec S) := ⟨p⟩
  have : IsIntegral (Spec R) := isIntegral_of_isOpenImmersion j
  have : IsIntegral (Spec S) := isIntegral_of_isOpenImmersion k
  have : IsDomain R := (affine_isIntegral_iff R).1 inferInstance
  have : IsDomain S := (affine_isIntegral_iff S).1 inferInstance
  letI : Algebra K R := α.hom.toAlgebra
  letI : Algebra K S := (α ≫ φ).hom.toAlgebra
  have hR := trdeg_eq_of_smoothOfRelativeDimension K Y s g hY R j hj hα.symm
  have hS := trdeg_eq_of_smoothOfRelativeDimension K X (f ≫ s) g hX S k hk (by
    rw [← reassoc_of% hw, ← hα, ← Spec.map_comp]; rfl)
  rw [eq_genericPoint_iff]
  refine eq_bot_of_comap_eq_bot φ.hom rfl hR hS ?_
  refine (eq_genericPoint_iff j (Spec.map φ p)).1 ?_
  rw [← Scheme.Hom.comp_apply, hw, Scheme.Hom.comp_apply, hx]

theorem isPullback_kernel_mul {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {Z A B : C} [GrpObj A] [GrpObj B] {i : Z ⟶ A} {ψ : A ⟶ B} [IsMonHom ψ]
    (hp : IsPullback i (toUnit Z) ψ η[B]) :
    IsPullback ((fst Z A ≫ i) * snd Z A) (snd Z A) ψ ψ := by
  have hi : i ≫ ψ = 1 := hp.w
  refine ⟨⟨?_⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => lift (hp.lift (s.fst * s.snd⁻¹) (toUnit _) ?_) s.snd) (fun s => ?_) (fun s => ?_)
    (fun s m h1 h2 => ?_)⟩⟩
  · rw [MonObj.mul_comp, Category.assoc, hi, MonObj.comp_one, _root_.one_mul]
  · rw [MonObj.mul_comp, GrpObj.inv_comp, s.condition, mul_inv_cancel, Hom.one_def]
  · rw [MonObj.comp_mul, lift_fst_assoc, hp.lift_fst, lift_snd, inv_mul_cancel_right]
  · exact lift_snd _ _
  · refine CartesianMonoidalCategory.hom_ext _ _ ?_ (by rw [lift_snd, h2])
    refine hp.hom_ext ?_ (toUnit_unique _ _)
    rw [lift_fst, hp.lift_fst, ← h1, ← h2, MonObj.comp_mul, mul_inv_cancel_right, Category.assoc]

theorem locallyQuasiFinite_of_finite_fibre {S : Scheme.{0}} [Subsingleton S] {A B : Over S}
    [GrpObj A] [GrpObj B] (ψ : A ⟶ B) [IsMonHom ψ] [Surjective ψ.left]
    [LocallyOfFiniteType ψ.left] [QuasiCompact ψ.left] (a : A.left)
    (h : (ψ.left ⁻¹' {ψ.left a}).Finite) : LocallyQuasiFinite ψ.left := by
  have hp : IsPullback (pullback.fst ψ η[B]) (toUnit _) ψ η[B] := by
    have := IsPullback.of_hasPullback ψ η[B]
    rwa [toUnit_unique (pullback.snd ψ η[B]) (toUnit _)] at this
  generalize pullback.fst ψ η[B] = i at hp
  generalize pullback ψ η[B] = Z at i hp
  have hl := hp.map (Over.forget S)
  have hZ1 : LocallyOfFiniteType Z.hom := by
    simpa using MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hl ‹_›
  have hZ2 : QuasiCompact Z.hom := by
    simpa using MorphismProperty.of_isPullback (P := @QuasiCompact) hl ‹_›
  have h1 : IsPullback ((fst Z A ≫ i) * snd Z A).left (pullback.snd Z.hom A.hom) ψ.left ψ.left :=
    (isPullback_kernel_mul hp).map (Over.forget S)
  let j := A.left.fromSpecResidueField a
  have h2 := IsPullback.of_hasPullback (pullback.snd Z.hom A.hom) j
  have h3 := h2.paste_horiz h1
  have h4 := h2.paste_horiz (IsPullback.of_hasPullback Z.hom A.hom)
  have hF : LocallyQuasiFinite (ψ.left.fiberToSpecResidueField (ψ.left a)) := by
    have : Finite (ψ.left.fiber (ψ.left a)) :=
      (ψ.left.fiberHomeo (ψ.left a)).toEquiv.finite_iff.2 h.to_subtype
    have : LocallyOfFiniteType (ψ.left.fiberToSpecResidueField (ψ.left a)) :=
      inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _))
    exact LocallyQuasiFinite.of_finite_preimage_singleton _ fun _ => Set.toFinite _
  rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField] at h3
  have h5 := h3.of_right' (IsPullback.of_hasPullback ψ.left
    (B.left.fromSpecResidueField (ψ.left a)))
  have h6 : LocallyQuasiFinite (pullback.snd (pullback.snd Z.hom A.hom) j) :=
    MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) h5 hF
  have h7 : LocallyQuasiFinite Z.hom :=
    Unif.locallyQuasiFinite_of_isPullback_surjective _ _ _ _ _ _ _ _ h4
      ⟨fun _ => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩ hZ1 hZ2 h6
  exact Unif.locallyQuasiFinite_of_isPullback_surjective _ _ _ _ _ _ _ _ h1 ‹_› ‹_› ‹_›
    inferInstance

end SurjIsogeny


open SurjIsogeny IsogenyModel in
theorem isogeny_of_surjective_of_dim_eq : Out.Laws → ∀ (K : Type) [Field K] (P : Out.PolAV (Sp K)) (B : Over (Sp K)) [GrpObj B] (ψ : P.A ⟶ B), IsAbelianScheme B → SmoothOfRelativeDimension P.g B.hom → IsMonHom ψ → Surjective ψ.left → IsFinite ψ.left ∧ Flat ψ.left ∧ ∃ n : ℕ, 1 ≤ n ∧ ∀ (T : Over (Sp K)) (x : T ⟶ P.A), x ≫ ψ = 1 → x ^ n = 1 := by
  intro hL K _ P B _ ψ hB hg _ _
  have := hB.proper
  have := P.isAb.proper
  have := P.isAb.comm
  have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ B.hom hB.smooth
    hB.geomConnected
  have : IsIntegral B.left := GeometricallyIntegral.isIntegral_of_subsingleton B.hom
  have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ P.A.hom
    P.isAb.smooth P.isAb.geomConnected
  have : IsIntegral P.A.left := GeometricallyIntegral.isIntegral_of_subsingleton P.A.hom
  have : IsProper (ψ.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : IsProper ψ.left := IsProper.of_comp ψ.left B.hom
  have hA : SmoothOfRelativeDimension P.g (ψ.left ≫ B.hom) := by rw [Over.w]; exact P.smoothDim
  obtain ⟨a, ha⟩ := ψ.left.surjective (genericPoint B.left)
  have : LocallyQuasiFinite ψ.left := by
    refine locallyQuasiFinite_of_finite_fibre ψ a ((Set.finite_singleton (genericPoint _)).subset ?_)
    intro x hx
    exact eq_genericPoint_of_apply_eq ψ.left B.hom hg hA (ha ▸ hx)
  have hf : IsFinite ψ.left := .of_isProper_of_locallyQuasiFinite _
  obtain ⟨Z, _, i, _, hi, hZ, hk⟩ := exists_kernel ψ
  have hm : Mono i := (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono i.left))
  have := isCommMonObj_of_mono i
  obtain ⟨N, hN, hZN⟩ := FiniteFlatKilled.main K Z hZ inferInstance
  obtain ⟨A, _, hA', q, _, _, _, _, hq⟩ := hL.quotient K P Z i ‹_› hm hZ inferInstance
  have := hA'.proper
  obtain ⟨e, -, he⟩ := exists_iso_of_same_kernel q ψ i hq hk
  refine ⟨hf, ?_, N, hN, fun T x hx => ?_⟩
  · have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
    rw [← he, Over.comp_left]
    infer_instance
  · have h1 : i ^ N = 1 := by
      rw [← Category.id_comp i, ← MonObj.pow_comp, hZN, MonObj.one_comp]
    rw [← hk.lift_fst x (toUnit _) hx, ← MonObj.comp_pow, h1, MonObj.comp_one]

theorem isogeny_of_surjective_polAV : ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] (σ : K →+* ℂ) (P P' : Out.PolAV (Sp K)) (ψ : P.A ⟶ P'.A), P.g = P'.g → IsMonHom ψ → Surjective ψ.left → IsFinite ψ.left ∧ Flat ψ.left ∧ ∃ n : ℕ, 1 ≤ n ∧ ∀ (T : Over (Sp K)) (x : T ⟶ P.A), x ≫ ψ = 1 → x ^ n = 1 :=
  fun _ hL K _ _ P P' ψ hg => isogeny_of_surjective_of_dim_eq hL K P P'.A ψ P'.isAb
    (hg ▸ P'.smoothDim)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsogenyOfSurjectivePolAVStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

theorem _root_.GlobalTheory.T.finite_flat_torsion_ker_of_surjective_polAV : ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] (σ : K →+* ℂ) (P P' : Out.PolAV (Sp K)) (ψ : P.A ⟶ P'.A), P.g = P'.g → IsMonHom ψ → Surjective ψ.left → IsFinite ψ.left ∧ Flat ψ.left ∧ ∃ n : ℕ, 1 ≤ n ∧ ∀ (T : Over (Sp K)) (x : T ⟶ P.A), x ≫ ψ = 1 → x ^ n = 1 := by
  first | exact @GlobalTheory.isogeny_of_surjective_polAV | exact GlobalTheory.isogeny_of_surjective_polAV | (intros; apply GlobalTheory.isogeny_of_surjective_polAV <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGenOfGenericFibre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.GenericTriv

variable {X Y Z : Scheme.{0}}

theorem cst_spMap {A C : Type} [CommRing A] [CommRing C] (q : Z ⟶ Sp C) (φ : A →+* C) (z : Z) (a : A) :
    cst (q ≫ spMap φ) z a = cst q z (φ a) :=
  (gs_pull q _ z ⊤ trivial _).symm.trans (congrArg (gs q z ⊤) (SecSpread.spMap_appTop φ a))

theorem isUnit_cst {A : Type} [CommRing A] (q : Z ⟶ Sp A) (z : Z) {a : A} (ha : IsUnit a) : IsUnit (cst q z a) := by
  rw [cst, gs_eq q z ⊤ trivial]
  exact ((ha.map _).map _).map _

theorem cst_zero {A : Type} [CommRing A] (q : Z ⟶ Sp A) (z : Z) : cst q z 0 = 0 := by
  rw [cst, gs_eq q z ⊤ trivial, map_zero, map_zero, map_zero]

theorem cst_one {A : Type} [CommRing A] (q : Z ⟶ Sp A) (z : Z) : cst q z 1 = 1 := by
  rw [cst, gs_eq q z ⊤ trivial, map_one, map_one, map_one]

theorem exists_ratio {N : LB X} (hN : N.IsLB) (σ : N.Sec) (π : Y ⟶ X) (t : (N.pull π).Gen) (ht : t.IsGen) :
    ∃ c : Γ(Y, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i : N.ι), π (r z) ∈ N.U i →
      gs (r ≫ π) z (N.U i) (σ.f i) = gs r z ⊤ c * (gm r z ((N.pull π).U fun _ => i) (t.s fun _ => i)).val := by
  let W : N.ι → Y.Opens := fun i => (N.pull π).U fun _ => i
  have hW : ∀ i, W i ≤ π ⁻¹ᵁ N.U i := fun i y hy => mem_pull.1 hy
  let u : ∀ i, Γ(Y, W i) := fun i => (π.appLE (N.U i) (W i) (hW i)).hom (σ.f i) * ((t.s fun _ => i)⁻¹).val
  have hu : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i : N.ι), r z ∈ W i →
      gs r z (W i) (u i) = gs (r ≫ π) z (N.U i) (σ.f i) * ((gm r z (W i) (t.s fun _ => i))⁻¹).val := by
    intro Z r z i hz
    rw [gs_mul r z _ hz, gs_appLE π _ _ _ r z hz, gs_unit r z _ hz, map_inv]
  obtain ⟨c, hc⟩ := Out.TLinPf.glue W (eq_top_iff.2 fun y _ => by
      obtain ⟨i, hi⟩ := exists_chart hN (π y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, mem_pull.2 hi⟩) u (fun i j => fn_ext fun y hy => by
    have hm : (𝟙 Y ≫ π) y ∈ N.U i ⊓ N.U j := ⟨hW i hy.1, hW j hy.2⟩
    have e := congrArg (gs (𝟙 Y ≫ π) y _) (σ.compat i j)
    rw [gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm, gs_unit _ y _ hm] at e
    have e' := gen_trans ht (𝟙 Y) y (j := fun _ => i) (j' := fun _ => j) hy.1 hy.2
    rw [trF, Fintype.prod_unique, zpow_one] at e'
    rw [gs_res _ y _ hy, gs_res _ y _ hy, hu _ _ y i hy.1, hu _ _ y j hy.2, e]
    refine Eq.trans (congrArg (fun q => _ * (q⁻¹).val) e') ?_
    rw [mul_inv, Units.val_mul, _root_.mul_mul_mul_comm, Units.mul_inv, _root_.one_mul]
    rfl)
  refine ⟨c, fun Z r z i hi => ?_⟩
  have hz : r z ∈ W i := mem_pull.2 hi
  rw [← gs_res r z (le_top : W i ≤ ⊤) hz, hc, hu Z r z i hz, _root_.mul_assoc, Units.inv_mul, _root_.mul_one]

theorem exists_sec_isUnit {R k : Type} [CommRing R] [Field k] (j : R →+* k) (hj : j.Flat) [CompactSpace X]
    [QuasiSeparatedSpace X] (f : X ⟶ Sp R) (π : Y ⟶ X) (f' : Y ⟶ Sp k) (H : IsPullback π f' f (spMap j))
    [Nonempty Y] (hs : Function.Surjective f'.appTop.hom) {N : LB X} (hN : N.IsLB) (t : (N.pull π).Gen)
    (ht : t.IsGen) : ∃ σ : N.Sec, ∀ y i, π y ∈ N.U i → IsUnit (gs π y (N.U i) (σ.f i)) := by
  obtain ⟨n, c, u, hu⟩ := FlatSec.exists_comb_of_flat R k j hj X f Y π f' H N hN (genSec t ht)
  choose d hd using fun a => exists_ratio hN (u a) π t ht
  have hd' : ∀ a, ∃ κ : k, ∀ y i, π y ∈ N.U i → gs π y (N.U i) ((u a).f i) =
      cst f' y κ * (gm (𝟙 Y) y ((N.pull π).U fun _ => i) (t.s fun _ => i)).val := fun a => by
    obtain ⟨κ, hκ⟩ := hs (d a)
    obtain ⟨κ, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv).2 κ
    refine ⟨κ, fun y i hi => ?_⟩
    have := hd a Y (𝟙 Y) y i hi
    rw [← hκ] at this
    exact this.trans (congrArg (· * _) (gs_pull (𝟙 Y) f' y ⊤ trivial _))
  choose κ hκ using hd'
  obtain ⟨a, ha⟩ : ∃ a, κ a ≠ 0 := by
    by_contra! h0
    obtain ⟨y⟩ := ‹Nonempty Y›
    obtain ⟨i, hi⟩ := exists_chart hN (π y)
    have := hu y i hi
    rw [Finset.sum_eq_zero fun a _ => by rw [hκ a y i hi, h0 a, cst_zero, zero_mul, mul_zero]] at this
    exact Units.ne_zero _ ((gs_unit (𝟙 Y) y _ (mem_pull.2 hi) (t.s fun _ => i)).symm.trans this)
  exact ⟨u a, fun y i hi => by rw [hκ a y i hi]; exact (isUnit_cst f' y ha.isUnit).mul (Units.isUnit _)⟩

theorem exists_unit_dvr {R V : Type} [CommRing R] [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (g : R →+* V) (hg : Function.Injective g) (f : X ⟶ Sp R) (π : Y ⟶ X) (p : Y ⟶ Sp V) [Smooth p]
    [GeometricallyIntegral p] (hw : π ≫ f = p ≫ spMap g) (e : Sp R ⟶ X) (e' : Sp V ⟶ Y) (he : e' ≫ p = 𝟙 _)
    (he' : e' ≫ π = spMap g ≫ e) {N : LB X} (hN : N.IsLB) (σ : N.Sec) {a : R} (ha : a ≠ 0) (ρ : (N.pull e).Gen)
    (hρ : ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp R) (z : Z) (i : N.ι), e (r z) ∈ N.U i →
      gs (r ≫ e) z (N.U i) (σ.f i) = cst r z a * (gm r z ((N.pull e).U fun _ => i) (ρ.s fun _ => i)).val)
    (hσ : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (i : N.ι), (f (r z)).asIdeal = ⊥ → r z ∈ N.U i →
      IsUnit (gs r z (N.U i) (σ.f i)))
    (y : Y) (i : N.ι) (hy : π y ∈ N.U i) : ∃ u, IsUnit u ∧ gs π y (N.U i) (σ.f i) = cst (π ≫ f) y a * u := by
  obtain ⟨K, _, _, _⟩ : ∃ (K : Type) (_ : Field K) (_ : Algebra V K), IsFractionRing V K :=
    ⟨FractionRing V, inferInstance, inferInstance, inferInstance⟩
  let ξ : Sp K ⟶ Sp V := spMap (algebraMap V K)
  obtain ⟨Y', j, q, hK⟩ : ∃ (Y' : Scheme.{0}) (j : Y' ⟶ Y) (q : Y' ⟶ Sp K), IsPullback j q p ξ :=
    ⟨_, _, _, IsPullback.of_hasPullback p ξ⟩
  have hs := IsPullback.of_hasPullback p (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)))
  have := DvrModel.isIntegral_of_geometricallyIntegral hK
  have := DvrModel.isIntegral_of_geometricallyIntegral hs
  obtain ⟨eK, h₁, h₂⟩ : ∃ eK : Sp K ⟶ Y', eK ≫ j = ξ ≫ e' ∧ eK ≫ q = 𝟙 _ :=
    ⟨hK.lift (ξ ≫ e') (𝟙 _) (by rw [Category.assoc, he]; simp), hK.lift_fst _ _ _, hK.lift_snd _ _ _⟩
  have ha' : algebraMap V K (g a) ≠ 0 := by
    rw [map_ne_zero_iff _ (IsFractionRing.injective V K), map_ne_zero_iff _ hg]; exact ha
  have hinv : ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp K) (z : Z),
      cst r z (algebraMap V K (g a)) * cst r z (algebraMap V K (g a))⁻¹ = 1 := fun Z r z => by
    rw [← SecSpread.cst_mul, mul_inv_cancel₀ ha', cst_one]
  let U : N.ι → Y.Opens := fun i => π ⁻¹ᵁ N.U i
  let t : ∀ i, Γ(Y', j ⁻¹ᵁ U i) := fun i =>
    constFn q _ (algebraMap V K (g a))⁻¹ * (j.app (U i)).hom ((π.app (N.U i)).hom (σ.f i))
  have ht : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (i : N.ι), r z ∈ j ⁻¹ᵁ U i →
      gs r z (j ⁻¹ᵁ U i) (t i) =
        cst (r ≫ q) z (algebraMap V K (g a))⁻¹ * gs ((r ≫ j) ≫ π) z (N.U i) (σ.f i) := fun Z r z i hz => by
    rw [gs_mul r z _ hz, gs_constFn q _ r z hz, gs_pull r j z _ hz, gs_pull (r ≫ j) π z _ hz]
  obtain ⟨i₀, h₀⟩ := exists_chart hN (e (spMap g (IsLocalRing.closedPoint V)))
  let A : (Sp V).Opens := spMap g ⁻¹ᵁ (N.pull e).U fun _ => i₀
  have hA : A ≤ e' ⁻¹ᵁ U i₀ := fun v hv =>
    (congrArg (fun m : Sp V ⟶ X => m v ∈ N.U i₀) he').mpr (mem_pull.1 hv)
  have hA' : ξ ⁻¹ᵁ A ≤ eK ⁻¹ᵁ j ⁻¹ᵁ U i₀ := fun v hv =>
    (congrArg (fun m : Sp K ⟶ Y => m v ∈ U i₀) h₁).mpr (hA hv)
  have c₁ : ∀ b c, Y'.presheaf.map (homOfLE inf_le_left).op (t b) =
      j.appLE (U b ⊓ U c) (j ⁻¹ᵁ U b ⊓ j ⁻¹ᵁ U c) le_rfl ((π.app (N.U b ⊓ N.U c)).hom (N.g b c).val) *
        Y'.presheaf.map (homOfLE inf_le_right).op (t c) := fun b c => fn_ext fun z hz => by
    have hm : ((𝟙 _ ≫ j) ≫ π) z ∈ N.U b ⊓ N.U c := hz
    have e₁ := congrArg (gs ((𝟙 _ ≫ j) ≫ π) z _) (σ.compat b c)
    rw [gs_res _ z _ hm, gs_mul _ z _ hm, gs_res _ z _ hm] at e₁
    refine ((gs_res _ z _ hz _).trans (ht _ _ z b hz.1)).trans (Eq.trans ?_ ((gs_mul _ z _ hz _ _).trans
      (congrArg₂ (· * ·) ((gs_appLE j _ _ _ _ z hz _).trans (gs_pull (𝟙 _ ≫ j) π z (N.U b ⊓ N.U c) hm _))
        ((gs_res _ z _ hz _).trans (ht _ _ z c hz.2)))).symm)
    rw [e₁, mul_left_comm]
  have c₂ : ∀ b, IsUnit (t b) := fun b => Y'.toRingedSpace.isUnit_of_isUnit_germ _ _ fun z hz => by
    refine (congrArg IsUnit ((gs_eq (𝟙 _) z (j ⁻¹ᵁ U b) hz _).symm.trans (ht _ (𝟙 _) z b hz))).mpr
      ((isUnit_cst _ z (inv_ne_zero ha').isUnit).mul (hσ _ _ z b ?_ hz))
    have w : ((𝟙 _ ≫ j) ≫ π) ≫ f = (q ≫ ξ) ≫ spMap g := by
      rw [Category.id_comp, Category.assoc, hw, ← Category.assoc, hK.w]
    refine (congrArg (fun m : Y' ⟶ Sp R => (m z).asIdeal) w).trans ?_
    show Ideal.comap g (Ideal.comap (algebraMap V K) (q z).asIdeal) = ⊥
    rw [Ideal.eq_bot_of_prime (q z).asIdeal, Ideal.comap_bot_of_injective _ (IsFractionRing.injective V K),
      Ideal.comap_bot_of_injective _ hg]
  let u : Γ(Sp V, A) := ((spMap g).app ((N.pull e).U fun _ => i₀)).hom (ρ.s fun _ => i₀).val
  have c₃ : (ξ.appLE A (ξ ⁻¹ᵁ A) le_rfl).hom u = (eK.appLE (j ⁻¹ᵁ U i₀) (ξ ⁻¹ᵁ A) hA').hom (t i₀) := by
    refine fn_ext fun z hz => ?_
    have hm : ((𝟙 (Sp K) ≫ ξ) ≫ spMap g) z ∈ (N.pull e).U fun _ => i₀ := hz
    have k₁ := gs_appLE ξ A (ξ ⁻¹ᵁ A) le_rfl (𝟙 (Sp K)) z hz u
    have k₂ := gs_pull (𝟙 (Sp K) ≫ ξ) (spMap g) z ((N.pull e).U fun _ => i₀) hm (ρ.s fun _ => i₀).val
    have k₃ := gs_unit ((𝟙 (Sp K) ≫ ξ) ≫ spMap g) z ((N.pull e).U fun _ => i₀) hm (ρ.s fun _ => i₀)
    have k₄ := gs_appLE eK (j ⁻¹ᵁ U i₀) (ξ ⁻¹ᵁ A) hA' (𝟙 (Sp K)) z hz (t i₀)
    have k₅ := ht (Sp K) (𝟙 (Sp K) ≫ eK) z i₀ (hA' hz)
    have w : (((𝟙 (Sp K) ≫ eK) ≫ j) ≫ π) = ((𝟙 (Sp K) ≫ ξ) ≫ spMap g) ≫ e := by
      simp only [Category.id_comp, Category.assoc]
      rw [← Category.assoc, h₁, Category.assoc, he']
    rw [w, hρ (Sp K) ((𝟙 (Sp K) ≫ ξ) ≫ spMap g) z i₀ (mem_pull.1 hm), cst_spMap, cst_spMap,
      Category.assoc (𝟙 (Sp K)) eK q, h₂, Category.comp_id,
      ← _root_.mul_assoc, (mul_comm _ _).trans (hinv (Sp K) (𝟙 (Sp K)) z), _root_.one_mul] at k₅
    exact (k₁.trans (k₂.trans k₃)).trans (k₄.trans k₅).symm
  have c₄ : IsUnit u := (Units.isUnit _).map _
  have c₅ : IsLocalRing.closedPoint V ∈ A := mem_pull (F := e).2 h₀
  obtain ⟨s, hsu, -, hsr⟩ := (DvrModel.existsUnique_isUnit_appLE_eq hK hs (U := U)
    (g := fun a b => (π.app (N.U a ⊓ N.U b)).hom (N.g a b).val) (W := fun i => j ⁻¹ᵁ U i) (fun _ => rfl)
    (fun x => exists_chart hN (π x)) (fun a b => (Units.isUnit _).map _) (r := t) c₁ c₂
    he h₁ (a₀ := i₀) (A := A) c₅ hA (A' := ξ ⁻¹ᵁ A) rfl hA' c₄ c₃).exists
  have key : (π.app (N.U i)).hom (σ.f i) = constFn p (U i) (g a) * s i :=
    SecSpread.ext_generic hK (W := U i) fun z hz => by
      have e₁ := (gs_appLE j _ _ _ (𝟙 _) z hz _).symm.trans
        ((congrArg (gs (𝟙 _) z _) (hsr i)).trans (ht _ (𝟙 _) z i hz))
      simp only [Category.id_comp] at e₁
      refine (gs_pull j π z _ hz _).trans (Eq.trans ?_ ((gs_mul j z _ hz _ _).trans (congrArg₂ (· * ·)
        (gs_constFn p _ j z hz _) e₁)).symm)
      rw [show j ≫ p = q ≫ ξ from hK.w, cst_spMap, ← _root_.mul_assoc, hinv, _root_.one_mul]
  refine ⟨gs (𝟙 Y) y (U i) (s i), ?_, ?_⟩
  · rw [gs_eq (𝟙 Y) y (U i) hy]
    exact ((hsu i).map _).map _
  · refine (gs_pull (𝟙 Y) π y _ hy _).symm.trans ((congrArg (gs (𝟙 Y) y (U i)) key).trans
      ((gs_mul (𝟙 Y) y (U i) hy _ _).trans (congrArg (· * _) ((gs_constFn p (U i) (𝟙 Y) y hy _).trans ?_))))
    rw [hw, cst_spMap, Category.id_comp]

theorem exists_gen_of_fibre {R k : Type} [CommRing R] [IsDedekindDomain R] [Field k] (j : R →+* k)
    (hj : Function.Injective j) [CompactSpace X] [QuasiSeparatedSpace X] (f : X ⟶ Sp R) [Smooth f]
    [GeometricallyIntegral f] (e : Sp R ⟶ X) (he : e ≫ f = 𝟙 _) (π : Y ⟶ X) (f' : Y ⟶ Sp k)
    (H : IsPullback π f' f (spMap j)) (hs : Function.Surjective f'.appTop.hom) {N : LB X} (hN : N.IsLB)
    (ρ : (N.pull e).Gen) (hρ : ρ.IsGen) (t : (N.pull π).Gen) (ht : t.IsGen) : ∃ u : N.Gen, u.IsGen := by
  have hef : ∀ v, f (e v) = v := fun v => congrArg (fun m : Sp R ⟶ Sp R => m v) he
  have lift : ∀ x : X, (f x).asIdeal = ⊥ → ∃ y, π y = x := fun x hx => by
    obtain ⟨y, hy, -⟩ := Scheme.exists_preimage_of_isPullback H x (⊥ : PrimeSpectrum k)
      (PrimeSpectrum.ext (hx.trans (Ideal.comap_bot_of_injective j hj).symm))
    exact ⟨y, hy⟩
  let ξ : Sp R := (⊥ : PrimeSpectrum R)
  have hξ : (f (e ξ)).asIdeal = ⊥ := congrArg PrimeSpectrum.asIdeal (hef ξ)
  have : Nonempty Y := ⟨(lift _ hξ).choose⟩
  have hflat : j.Flat := by
    let _ := j.toAlgebra
    have : FaithfulSMul R k := (faithfulSMul_iff_algebraMap_injective R k).2 hj
    exact inferInstanceAs (Module.Flat R k)
  obtain ⟨σ, hσ⟩ := exists_sec_isUnit j hflat f π f' H hs hN t ht
  have hσ₁ : ∀ x i, (f x).asIdeal = ⊥ → x ∈ N.U i → IsUnit (gs (𝟙 X) x (N.U i) (σ.f i)) := fun x i hx hi => by
    obtain ⟨y, rfl⟩ := lift x hx
    have := hσ y i hi
    rwa [gs_stalkMap π y _ hi, isUnit_map_iff] at this
  have hσ₂ : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (i : N.ι), (f (r z)).asIdeal = ⊥ → r z ∈ N.U i →
      IsUnit (gs r z (N.U i) (σ.f i)) := fun Z r z i hz hi => by
    rw [gs_stalkMap r z _ hi]
    exact (hσ₁ _ i hz hi).map _
  obtain ⟨c, hc⟩ := exists_ratio hN σ e ρ hρ
  obtain ⟨a, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).2 c
  have ha : a ≠ 0 := by
    rintro rfl
    obtain ⟨i, hi⟩ := exists_chart hN (e ξ)
    have h := hσ₂ _ (𝟙 _ ≫ e) ξ i hξ hi
    rw [hc _ (𝟙 _) ξ i hi] at h
    exact not_isUnit_zero ((congrArg IsUnit (cst_zero (𝟙 (Sp R)) ξ)).mp (isUnit_of_mul_isUnit_left h))
  have dvd : ∀ i, ∀ x ∈ N.U i, cst f x a ∣ gs (𝟙 X) x (N.U i) (σ.f i) ∧ gs (𝟙 X) x (N.U i) (σ.f i) ∣ cst f x a := by
    intro i x hx
    by_cases h0 : (f x).asIdeal = ⊥
    · refine ⟨IsUnit.dvd ?_, (hσ₁ x i h0 hx).dvd⟩
      obtain ⟨y, rfl⟩ := lift x h0
      have h : IsUnit (cst (π ≫ f) y a) := by
        rw [H.w, cst_spMap]
        exact isUnit_cst _ _ ((map_ne_zero_iff j hj).2 ha).isUnit
      rw [cst, ← gs_pull π f y ⊤ trivial, gs_stalkMap π y (f ⁻¹ᵁ ⊤) trivial, isUnit_map_iff] at h
      exact (congrArg IsUnit (gs_pull (𝟙 X) f (π y) ⊤ trivial _)).mp h
    · let V := Localization.AtPrime (f x).asIdeal
      have : IsDiscreteValuationRing V :=
        IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R h0 V
      have hg : Function.Injective (algebraMap R V) :=
        IsLocalization.injective V (f x).asIdeal.primeCompl_le_nonZeroDivisors
      have H' := IsPullback.of_hasPullback f (spMap (algebraMap R V))
      have : Flat (spMap (algebraMap R V)) := Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance)
      obtain ⟨y, hy, -⟩ := Scheme.exists_preimage_of_isPullback H' x (IsLocalRing.closedPoint V)
        (PrimeSpectrum.ext (Localization.AtPrime.under_maximalIdeal (I := (f x).asIdeal)).symm)
      have hy' : pullback.fst f (spMap (algebraMap R V)) y ∈ N.U i := hy.symm ▸ hx
      obtain ⟨u, hu, h⟩ := exists_unit_dvr (algebraMap R V) hg f _ _ H'.w e
        (H'.lift (spMap (algebraMap R V) ≫ e) (𝟙 _) (by rw [Category.assoc, he]; simp)) (H'.lift_snd _ _ _)
        (H'.lift_fst _ _ _) hN σ ha ρ hc hσ₂ y i hy'
      rw [cst, ← gs_pull _ f y ⊤ trivial, gs_stalkMap _ y _ hy', gs_stalkMap _ y (f ⁻¹ᵁ ⊤) trivial,
        gs_pull (𝟙 X) f _ ⊤ trivial, Category.id_comp] at h
      have d₁ := dvd_descend _ y (Dvd.intro _ h.symm)
      have d₂ := dvd_descend _ y ((dvd_of_eq h).trans (hu.mul_right_dvd.2 dvd_rfl))
      clear h
      generalize pullback.fst f (spMap (algebraMap R V)) y = x' at hy hy' d₁ d₂
      subst hy
      exact ⟨d₁, d₂⟩
  obtain ⟨s, hs'⟩ := exists_div_sec f ha σ fun i x hx => (dvd i x hx).1
  have hu : ∀ i, IsUnit (s.f i) := fun i => X.toRingedSpace.isUnit_of_isUnit_germ _ _ fun x hx => by
    obtain ⟨w, hw⟩ := (dvd i x hx).2
    rw [hs' i, gs_mul _ x _ hx, gs_constFn f _ _ x hx, Category.id_comp, _root_.mul_assoc] at hw
    have h1 := cst_regular f x ha ((_root_.mul_one _).trans hw)
    exact (congrArg IsUnit (gs_eq (𝟙 X) x (N.U i) hx _)).mp (IsUnit.of_mul_eq_one w h1.symm)
  exact ⟨⟨fun i => (hu i).unit⟩, fun i i' => Units.ext (s.compat i i')⟩

end GlobalTheory.GenericTriv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsConjAction
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section

namespace GlobalTheory.CM.EllConj

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem bar_mem (H : Host E) (a : OK H) : H.bar (a : 𝓞 E) ∈ OK H := by
  obtain ⟨a, ha⟩ := a
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    obtain rfl : x = H.w0 := hx
    rw [GlobalTheory.HostModel.cmHost_bar_halfIntegerGenerator]
    exact sub_mem (one_mem _) (wK H).2
  | algebraMap r =>
    have : H.bar (algebraMap ℤ (𝓞 E) r) = algebraMap ℤ (𝓞 E) r := by simp
    show H.bar (algebraMap ℤ (𝓞 E) r) ∈ OK H
    rw [this]
    exact Subalgebra.algebraMap_mem _ r
  | add x y hx hy h₁ h₂ => exact (map_add H.bar x y) ▸ add_mem h₁ h₂
  | mul x y hx hy h₁ h₂ => exact (map_mul H.bar x y) ▸ mul_mem h₁ h₂

def barK (H : Host E) : OK H →+* OK H where
  toFun a := ⟨H.bar (a : 𝓞 E), bar_mem H a⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

theorem barK_wK_add (H : Host E) : barK H (wK H) + wK H = 1 :=
  Subtype.ext (by
    show H.bar H.w0 + H.w0 = 1
    rw [GlobalTheory.HostModel.cmHost_bar_halfIntegerGenerator, sub_add_cancel])

theorem isLieComb_one_sub {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (v : epsR R ⟶ G)
    (hv : IsTangent v) (ω : R) (f g : G ⟶ G) (hfg : g * f = 𝟙 G) (h : IsLieComb ![ω] ![v] (v ≫ f)) :
    IsLieComb ![1 - ω] ![v] (v ≫ g) := by
  have hv' : ∀ i, IsTangent (![v] i) := fun i => by fin_cases i; exact hv
  rw [GlobalTheory.LieComb.isLieComb_iff_tanExp] at h ⊢
  have e₁ : (v ≫ g) * (v ≫ f) = v := by rw [← MonObj.comp_mul, hfg, Category.comp_id]
  have e₂ := map_add (GlobalTheory.LieComb.combHom hv') ![1 - ω] ![ω]
  have e₃ : (![1 - ω] + ![ω] : Fin 1 → R) = Pi.single 0 1 := by
    funext i
    fin_cases i
    simp
  rw [e₃] at e₂
  have e₄ : v = GlobalTheory.SqZero.tanExp ![v] ![1 - ω] * GlobalTheory.SqZero.tanExp ![v] ![ω] :=
    (GlobalTheory.LieComb.tanExp_single hv' 0).symm.trans (congrArg Additive.toMul e₂)
  rw [← h] at e₄
  exact mul_right_cancel (e₁.trans e₄)


open GlobalTheory.PrimNorm in
theorem lbIso_of_adj {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] {M : LB B.left} (hM : M.IsLB)
    {f g : B ⟶ B} (h : LamEq M f (𝟙 B) M (𝟙 B) g) : LBIso (cubeLB B ![𝟙 B, g] M) (cubeLB B ![𝟙 B, f] M) := by
  have h' : LBIso (cubeLB B ![fst B B ≫ f, snd B B] M) (cubeLB B ![fst B B, snd B B ≫ g] M) := by
    simpa only [LamEq, Category.comp_id] using h
  have e := diff₂_ptCls_adj hM h' (𝟙 B) (𝟙 B)
  rw [Category.id_comp, Category.id_comp, diff₂_comm] at e
  exact (lbIso_iff hM _ _ _ _).2 ((prod_square_id _ _ (cls M)).trans (e.symm.trans (prod_square_id _ _ (cls M)).symm))

theorem exists_conj_action (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R]
    (ω : R) (C : Ell H R ω) :
    ∃ a : OAct (OK H) C.P.A, (∀ x y : OK H, (y : 𝓞 E) = H.bar x → a.act x = C.act.act y) ∧
      IsLieComb ![1 - ω] ![C.v] (C.v ≫ a.act (wK H)) ∧
      (∀ x y : OK H, (y : 𝓞 E) = H.bar x → LamEq C.P.L (a.act x) (𝟙 C.P.A) C.P.L (𝟙 C.P.A) (a.act y)) ∧
      LBIso C.P.L (cubeLB C.P.A ![𝟙 C.P.A, a.act (wK H)] C.P.L) := by
  refine ⟨Serre.comapAct C.act (barK H), fun x y h => ?_, ?_, fun x y h => ?_, ?_⟩
  · exact congrArg C.act.act (Subtype.ext h.symm)
  · exact isLieComb_one_sub C.v (C.basis.1 0) ω (C.act.act (wK H)) _
      (by rw [Serre.comapAct_act, ← C.act.add, barK_wK_add, C.act.one]) C.eig
  · exact C.adj _ _ (congrArg H.bar h)
  · exact LBIso.trans C.P.isLB (DVR.linComb_isLB _ C.P.isLB _ _) (DVR.linComb_isLB _ C.P.isLB _ _) C.prim
      (lbIso_of_adj C.P.isLB (C.adj (barK H (wK H)) (wK H) (GlobalTheory.HostModel.bar_bar H _).symm))

end GlobalTheory.CM.EllConj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsIsoOfSurjectivePrincipalPairing
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsIsoOfSurjectivePrincipalPairing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section

namespace GlobalTheory.CM.PairingIso

open GlobalTheory.KerPow

theorem exists_gen_of_lbIso {X : Scheme.{0}} {P Q : LB X} (hP : P.IsLB) (hQ : Q.IsLB) (h : LBIso P Q)
    (H : ∃ t : LB.Gen P, t.IsGen) : ∃ t : LB.Gen Q, t.IsGen := by
  obtain ⟨w, hw⟩ := h.chartPull (chartPullId P) (Geo.Tor.chartPullPull Q (𝟙 X) (𝟙 X) rfl)
  obtain ⟨t, ht⟩ := H
  obtain ⟨a, ha⟩ := gen_chartPull (Geo.Tor.chartPullPull P (𝟙 X) (𝟙 X) rfl) t ht
  obtain ⟨c, hc, -⟩ := exists_up ((isGen_iff w).1 hw) hQ hP a ha
  exact gen_chartPull (chartPullUnpull Q _ (Category.id_comp _)) c hc

theorem locGen_base {X Y B : Scheme.{0}} {L : LB X} (hL : L.IsLB) (π : Y ⟶ B) (a : B ⟶ X) {b : Y ⟶ X}
    (e : b = π ≫ a) : LocGen L π (fun _ : PUnit => b) (fun _ => 1) := by
  subst e
  intro p
  obtain ⟨i, hi⟩ := exists_chart hL (a p)
  exact ⟨a ⁻¹ᵁ L.U i, hi, ChartRig.exists_gen_pull L _ i hL fun y _ => y.2⟩

theorem eq_one_of_comp_eq_one {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]
    {L : LB A.left} {M : LB B.left} {Φ : A ⟶ B} (hL : L.IsLB) (hM : M.IsLB) (hK : Out.KTriv A L)
    (h : LamEq M Φ Φ L (𝟙 A) (𝟙 A)) {T : Over S} (x : T ⟶ A) (hx : x ≫ Φ = 1) : x = 1 := by
  have h' : LBIso (cubeLB B ![1, snd T A ≫ Φ] M) (cubeLB A ![fst T A ≫ x, snd T A] L) :=
    LBIso.chartPull
      (PrimNorm.chartSquare M (lift (fst T A ≫ x) (snd T A))
        (by rw [lift_fst_assoc, Category.assoc, hx, MonObj.comp_one]) (by rw [lift_snd_assoc]))
      (PrimNorm.chartSquare L (lift (fst T A ≫ x) (snd T A)) (by simp) (by simp)) h
  have g₁ : ∃ t : LB.Gen (cubeLB B ![1, snd T A ≫ Φ] M), t.IsGen :=
    hasGen_of_trivial hM fun U _ k => (PrimNorm.prod_square_id _ _ k).trans (by simp [PrimNorm.diff₂])
  have g₂ : HasGen L _ _ :=
    exists_gen_of_lbIso (DVR.linComb_isLB _ hM _ _) (DVR.linComb_isLB _ hL _ _) h' g₁
  have g₃ : LocGen L (fst T A).left
      (fun I : ULift.{0} (Finset (Fin 2)) => (psum A ![fst T A ≫ x, snd T A] I.down).left)
      (fun I => (-1) ^ (2 - I.down.card)) := fun _ => ⟨⊤, trivial, g₂.pull _ fun _ => rfl⟩
  have b₁ := locGen_base hL (fst T A).left x.left (b := (fst T A ≫ x).left) rfl
  have b₀ := locGen_base hL (fst T A).left (1 : T ⟶ A).left (b := (1 : T ⊗ A ⟶ A).left)
    (congrArg (fun q : T ⊗ A ⟶ A => q.left) (MonObj.comp_one (fst T A) : fst T A ≫ (1 : T ⟶ A) = 1).symm)
  have b := b₀.comb hL b₁ (φ'' := ![(1 : T ⊗ A ⟶ A).left, (fst T A ≫ x).left]) (ε'' := ![1, -1])
    fun U _ k => by simp [Fin.prod_univ_two]
  refine eq_one_of_locGen hK x (g₃.comb hL b fun U _ k => ?_)
  rw [PrimNorm.prod_square_id, Fin.prod_univ_two, Fin.prod_univ_two]
  show k ((fst T A ≫ x) * snd T A).left * (k (fst T A ≫ x).left)⁻¹ * (k (snd T A).left)⁻¹ * k (1 : T ⊗ A ⟶ A).left *
    (k (1 : T ⊗ A ⟶ A).left ^ (1 : ℤ) * k (fst T A ≫ x).left ^ (-1 : ℤ))⁻¹ =
    k ((fst T A ≫ x) * snd T A).left ^ (1 : ℤ) * k (snd T A).left ^ (-1 : ℤ)
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  module

theorem isIso_of_lamEq : ∀ (S : Scheme.{0}) [IsReduced S] (A B : Over S) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (Φ : A ⟶ B), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → IsMonHom Φ → Out.KTriv A L → LamEq M Φ Φ L (𝟙 A) (𝟙 A) → Surjective Φ.left → IsIso Φ := by
  intro S _ A B _ _ L M Φ hA hB hL hM hΦ hK h hs
  have := hA.comm
  have := hB.comm
  have := hA.proper
  have := hB.proper
  have := hB.smooth
  have : Mono Φ := ⟨fun {T} x y e => mul_inv_eq_one.1 (eq_one_of_comp_eq_one hL hM hK h (x * y⁻¹) (by
    rw [MonObj.mul_comp, GrpObj.inv_comp, e, mul_inv_cancel]))⟩
  have : Mono Φ.left := inferInstanceAs (Mono ((Over.forget S).map Φ))
  have : IsReduced B.left := GlobalTheory.isReduced_of_smooth_of_isReduced B.hom
  have : IsProper (Φ.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : IsProper Φ.left := IsProper.of_comp Φ.left B.hom
  have : IsClosedImmersion Φ.left := (IsClosedImmersion.iff_isProper_and_mono _).2 ⟨‹_›, ‹_›⟩
  have : IsIso Φ.left := isIso_of_isClosedImmersion_of_surjective _
  have : IsIso ((Over.forget _).map Φ) := ‹_›
  exact isIso_of_reflects_iso Φ (Over.forget _)

end GlobalTheory.CM.PairingIso
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsIsoOfSurjectivePrincipalPairingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIso_of_surjective_principalPairing : ∀ (S : Scheme.{0}) [IsReduced S] (A B : Over S) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (Φ : A ⟶ B), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → IsMonHom Φ → Out.KTriv A L → LamEq M Φ Φ L (𝟙 A) (𝟙 A) → Surjective Φ.left → IsIso Φ := by
  first | exact @GlobalTheory.CM.PairingIso.isIso_of_lamEq | exact GlobalTheory.CM.PairingIso.isIso_of_lamEq | (intros; apply GlobalTheory.CM.PairingIso.isIso_of_lamEq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsLieNormSqIffEqPiDivCovolume
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory

theorem isLieNormSq_iff_eq_pi_div_covolume :
    ThetaUnifAV → Out.PolBaseChangeSt → ∀ (R : Type) [CommRing R] (P : Out.PolAV (Sp R)) (v : epsR R ⟶ P.A) (s : R →+* ℂ) (L : PeriodPair), P.g = 1 → IsTangent v → (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s P P' φ' → IsVecOver s φ' v v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ L.lattice ↔ z • w' ∈ u'.Λ) → 0 < Real.pi / |(L.ω₁ * starRingEnd ℂ L.ω₂).im| ∧ ∀ r, IsLieNormSq P v s r ↔ r = Real.pi / |(L.ω₁ * starRingEnd ℂ L.ω₂).im| := by
  intro hU hB R _ P v s L hg hv hΛ
  have key : ∀ r, IsLieNormSq P v s r → 0 < r ∧ r = Real.pi / |(L.ω₁ * starRingEnd ℂ L.ω₂).im| := by
    rintro r ⟨P', φ, v', u, Hm, χ, w, hP, hv', hA, hd, rfl⟩
    obtain ⟨hw, hL⟩ := hΛ P' φ v' u w hP hv' hd
    obtain ⟨Ef, hEf, hbij⟩ := (GlobalTheory.T.holomorphicUniformisation_tangent_unimodular_riemannForm hU P' u).2.2 Hm χ hA
    have hpos : 0 < (hermForm Hm w w).re := hA.2.1 w hw
    have e := hermForm_principal_dim_one P'.g u.Λ w L Hm Ef (hP.1.trans hg) hw hL hA.1 hpos hEf hbij 1 1
    refine ⟨mul_pos Real.pi_pos hpos, ?_⟩
    rw [one_smul, map_one, _root_.mul_one, one_div, ← Complex.ofReal_inv] at e
    rw [e, Complex.ofReal_re, div_eq_mul_inv]
  obtain ⟨r₀, h₀⟩ := exists_isLieNormSq hU hB P hv s
  obtain ⟨h1, h2⟩ := key r₀ h₀
  exact ⟨h2 ▸ h1, fun r => ⟨fun h => (key r h).2, fun h => (h.trans h2.symm) ▸ h₀⟩⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsPullCubicalOfIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CartTriple

section Charts

variable {X Y : Scheme.{0}} {M : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

theorem chart_of_val (hM : M.IsLB) {u u' : LB.Gen (LB.LinComb M φ ε)} (hu : u.IsGen) (hu' : u'.IsGen)
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (α : (Z.presheaf.stalk z)ˣ)
    (h : ∀ J, Good M z J → val u r z J = α * val u' r z J) (q : K → M.ι) (hq : r z ∈ LB.wchart M φ q) :
    gm r z (LB.wchart M φ q) (u.s q) = α * gm r z (LB.wchart M φ q) (u'.s q) := by
  obtain ⟨J, hJ⟩ := GlobalTheory.DegPull.exists_good' hM z
  rw [gen_trans hu r z hq (hJ.mem φ r), gen_trans hu' r z hq (hJ.mem φ r), mul_left_comm]
  exact congrArg _ (h J hJ)

end Charts

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {G' : Over S'} [GrpObj G'] [IsCommMonObj G']
  {f : S' ⟶ S} {F : G'.left ⟶ G.left}


omit [IsCommMonObj G] [IsCommMonObj G'] in
theorem exists_rigidified (he : eSec G' ≫ F = f ≫ eSec G) (L : RigLB G) (L' : RigLB G')
    (h : LBIso L'.L (L.L.pull F)) : ∃ w : LB.Iso L'.L (L.L.pull F), PGen w ∧
      PMaps w (K := PUnit) (fun _ => eSec G') (fun _ => eSec G) (fun _ => 1) L'.rig L.rig f := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨ρ, hρ, H⟩ := GlobalTheory.DegPull.exists_pmaps ((isGen_iff w).1 hw) L.isLB L'.isLB (K := PUnit)
    (φ' := fun _ => eSec G') (φ := fun _ => eSec G) (ε := fun _ => 1) f (fun _ => he) L.rig L.rigGen
  obtain ⟨a, ha⟩ := GlobalTheory.AbPackage.exists_unit_ratio L'.isLB (φ := fun _ : PUnit => eSec G') (ε := fun _ => 1)
    hρ L'.rigGen
  let b : Γ(G'.left, ⊤)ˣ := pullU G'.hom ⊤ a
  refine ⟨GlobalTheory.UU.scaleGen b w, (isGen_iff _).1 (GlobalTheory.UU.scaleGen_isGen b hw), fun Z r z p q hp hq => ?_⟩
  have hs : eSec G' ≫ G'.hom = 𝟙 _ := Over.w η[G']
  have e : gw (GlobalTheory.UU.scaleGen b w) (r ≫ eSec G') z (p PUnit.unit) (q PUnit.unit) =
      gm r z ⊤ a * gw w (r ≫ eSec G') z (p PUnit.unit) (q PUnit.unit) := by
    have hm : (r ≫ eSec G') z ∈ (L.L.pull F).U (fun _ => p PUnit.unit) ⊓ L'.L.U (q PUnit.unit) :=
      ⟨mem_pull.2 (hp PUnit.unit), hq PUnit.unit⟩
    refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res _ z le_top hm b).trans
      ((gm_pull (r ≫ eSec G') G'.hom z ⊤ trivial a).trans ?_)) rfl)
    rw [Category.assoc, hs]
    exact congrArg (fun g => gm g z ⊤ a) (Category.comp_id r)
  have e₂ := chart_of_val L'.isLB (φ := fun _ : PUnit => eSec G') (ε := fun _ => 1) hρ L'.rigGen r z _
    (ha Z r z) q (Set.mem_iInter.2 hq)
  refine (H Z r z p q hp hq).trans ((congrArg (_ * ·) e₂).trans ?_)
  rw [Fintype.prod_unique, Fintype.prod_unique, zpow_one, zpow_one, ← _root_.mul_assoc]
  exact congrArg (· * _) ((mul_comm _ _).trans e.symm)

theorem val_origin (gp : IsGrpPullback G' G f F) {L : RigLB G} {L' : RigLB G'} (c : CubicalStr G L)
    {w : LB.Iso L'.L (L.L.pull F)} {t : LB.Gen (LB.LinComb L'.L (thφ G' (x3 G')) thε)}
    (H : PMaps w (thφ G' (x3 G')) (thφ G (x3 G)) thε t c.t (cubeMapOf gp).F3) (T : Over S') (y : T.left) (J')
    (hJ' : Good L'.L y J') : val t (lift (1 : T ⟶ G') (lift 1 1)).left y J' = 1 := by
  have hψ : ∀ I : thK, thφ G' (x3 G') I ≫ F = (cubeMapOf gp).F3 ≫ thφ G (x3 G) I :=
    fun I => (cubeMapOf gp).psum_comm I.down
  obtain ⟨J, hJ⟩ := GlobalTheory.DegPull.exists_good' L.isLB y
  have q : ∀ a : T ⟶ G', (lift a (lift a a)).left ≫ (cubeMapOf gp).F3 =
      (lift (pushHom gp T a) (lift (pushHom gp T a) (pushHom gp T a))).left := fun a => hom_ext_triple _ fun i => by
    rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
    fin_cases i <;> simp [x3] <;> rfl
  have e := GlobalTheory.DegPull.pmaps_val hψ H (lift (1 : T ⟶ G') (lift 1 1)).left y hJ hJ'
  rw [q, map_one] at e
  have p := prod_cub (1 : T ⟶ G') 1 1 (fun q => gw w q y (J (q ≫ F)) (J' q))
  rw [_root_.mul_one, _root_.mul_one] at p
  have face : cubV c (T := Over.mk (T.hom ≫ f)) y J 1 1 1 = 1 := by
    have e := val_corr hJ (c.face 0) (lift (1 : Over.mk (T.hom ≫ f) ⟶ G) 1).left
    rw [val_one] at e
    refine (Eq.trans ?_ (val_cub c (lift (1 : Over.mk (T.hom ≫ f) ⟶ G) 1) hJ (pzero G _) (x2 G 0) (x2 G 1)).symm).trans e
    congr 1 <;> simp [x2, pzero, Hom.one_def]
  have e' := face.symm.trans
    (e.trans (congrArg₂ (· * ·) p rfl))
  have alg : ∀ {U : Type} [CommGroup U] (a v : U), 1 = a * a⁻¹ * a⁻¹ * a⁻¹ * a * a * a * a⁻¹ * v → v = 1 :=
    fun a v h => by simpa using h.symm
  exact alg _ _ e'

theorem pmaps_cube (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme G') (gp : IsGrpPullback G' G f F) {L : RigLB G}
    {L' : RigLB G'} (c : CubicalStr G L) (c' : CubicalStr G' L') {w : LB.Iso L'.L (L.L.pull F)} (hw : PGen w) :
    PMaps w (thφ G' (x3 G')) (thφ G (x3 G)) thε c'.t c.t (cubeMapOf gp).F3 := by
  have hψ : ∀ I : thK, thφ G' (x3 G') I ≫ F = (cubeMapOf gp).F3 ≫ thφ G (x3 G) I :=
    fun I => (cubeMapOf gp).psum_comm I.down
  obtain ⟨t, ht, H⟩ := GlobalTheory.DegPull.exists_pmaps hw L.isLB L'.isLB (ε := thε) (cubeMapOf gp).F3 hψ c.t c.isGen
  have face (y : (𝟙_ (Over S')).left) (J') (hJ' : Good L'.L y J') :
      cubV c' y J' (1 : 𝟙_ (Over S') ⟶ G') 1 1 = 1 := by
    have e := val_corr hJ' (c'.face 0) (lift (1 : 𝟙_ (Over S') ⟶ G') 1).left
    rw [val_one] at e
    refine (Eq.trans ?_ (val_cub c' (lift (1 : 𝟙_ (Over S') ⟶ G') 1) hJ' (pzero G' _) (x2 G' 0) (x2 G' 1)).symm).trans e
    congr 1 <;> simp [x2, pzero, Hom.one_def]
  have key := gen_unique L'.isLB (φ := thφ G' (x3 G')) (ε := thε) (G3 G').hom
    (lift (1 : 𝟙_ (Over S') ⟶ G') (lift 1 1)).left (Over.w _) (GlobalTheory.UU.surjective_cube hG hA) ht c'.isGen
    (fun y J' hJ' => (val_origin gp c H (𝟙_ (Over S')) y J' hJ').trans (face y J' hJ').symm)
  intro Z r z p q hp hq
  have e := (chart_of_val L'.isLB (φ := thφ G' (x3 G')) (ε := thε) ht c'.isGen r z 1
    (fun J hJ => (key Z r z J hJ).trans (_root_.one_mul _).symm) q (Set.mem_iInter.2 hq)).trans (_root_.one_mul _)
  exact (H Z r z p q hp hq).trans (congrArg₂ (· * ·) rfl e)

theorem isPullCubical_of_iso (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme G') (gp : IsGrpPullback G' G f F)
    {L : RigLB G} {L' : RigLB G'} (c : CubicalStr G L) (c' : CubicalStr G' L') (h : LBIso L'.L (L.L.pull F)) :
    (cubeMapOf gp).IsPullCubical c' c := by
  obtain ⟨w, hw, hr⟩ := exists_rigidified (cubeMapOf gp).e_comm L L' h
  exact (isPullCubical_iff _ c c').2 ⟨w, hw, hr, pmaps_cube hG hA gp c c' hw⟩

theorem exists_tripleMap : Out.GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (f : S' ⟶ S) (t' : SAB H S') (t : SAB H S) (φ : t'.G.left ⟶ t.G.left), IsAbelianScheme t'.G → IsGrpPullback t'.G t.G f φ → (∀ a, (t'.act.act a).left ≫ φ = φ ≫ (t.act.act a).left) → LBIso t'.PP.L (t.PP.L.pull φ) → ∃ m : SABMap t' t f, m.φ = φ := by
  intro hG E _ _ _ H S S' f t' t φ hA gp hact h
  exact ⟨⟨cubeMapOf gp, gp, rfl, hact, isPullCubical_of_iso hG hA gp t.cub t'.cub h⟩, rfl⟩

end GlobalTheory.CartTriple
end
