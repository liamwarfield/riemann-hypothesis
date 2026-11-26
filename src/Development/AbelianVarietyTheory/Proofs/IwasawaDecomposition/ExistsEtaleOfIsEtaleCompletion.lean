module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ForcedContentEqScaleAtResidueChar
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwArgs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtOfFrameEqOfPointEq

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEtaleOfIsEtaleCompletion
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.TorRef TensorProduct

namespace GlobalTheory.NormalBaseChange

theorem exists_etale_of_isEtaleCompletion (A R : Type) [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R]
    [Algebra A R] [IsNoetherianRing A] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
    (het : IsEtaleCompletion (algebraMap A R)) (hfu : ((residue R).comp (algebraMap A R)).FormallyUnramified) :
    ∃ g : AdicCompletion (maximalIdeal A) A →+* R, g.comp (algebraMap A _) = algebraMap A R ∧
      @Algebra.Etale _ R _ _ g.toAlgebra := by
  obtain ⟨hflat, hmap, hfin⟩ := het
  set h := algebraMap A R with hh
  let D := AdicCompletion (maximalIdeal A) A
  haveI : IsNoetherianRing D := AdicNoeth.isNoetherianRing_adicCompletion A _
  haveI : IsAdicComplete ((maximalIdeal A).map h) R := by rw [hmap]; infer_instance
  obtain ⟨g, hg⟩ := exists_adicCompletion_ringHom_extend (maximalIdeal A) h
  letI : Algebra D R := g.toAlgebra
  have hgA : ∀ a, g (algebraMap A D a) = h a := fun a => RingHom.congr_fun hg a
  have hmA : (maximalIdeal D).map (algebraMap D R) = maximalIdeal R := by
    rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_map]
    change (maximalIdeal A).map (g.comp _) = _
    rw [hg, hmap]
  haveI : IsLocalHom (algebraMap D R) := ((local_hom_tfae _).out 1 3).mpr hmA.le
  have hres : ((residue R).comp g).Finite :=
    RingHom.Finite.of_comp_finite (f := algebraMap A D) (by rw [RingHom.comp_assoc, hg]; exact hfin)
  haveI : Module.Finite D (R ⧸ (maximalIdeal D).map (algebraMap D R)) := by
    rw [← RingHom.finite_algebraMap]
    show ((Ideal.Quotient.mk _).comp (algebraMap D R)).Finite
    rw [hmA]
    exact hres
  haveI : IsHausdorff ((maximalIdeal D).map (algebraMap D R)) R := by rw [hmA]; infer_instance
  haveI : Module.Finite D R := FormalIsogeny.finite_of_finite_quotient_map (maximalIdeal D)
  haveI : Module.Flat D R := by
    refine LocalFlat.flat_of_relationsLift R (I := maximalIdeal D)
      (hmA.le.trans (maximalIdeal_le_jacobson _)) fun n => ?_
    haveI : Module.Flat A R := RingHom.flat_algebraMap_iff.mp hflat
    have fg := (maximalIdeal A).fg_of_isNoetherianRing
    have hkerA : ∀ x : D, AdicCompletion.evalₐ (maximalIdeal A) n x = 0 ↔ x ∈ maximalIdeal D ^ n := by
      intro x
      rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow, ← Submodule.restrictScalars_mem A,
        ← Ideal.smul_top_eq_map, AdicCompletion.pow_smul_top_eq_ker_eval fg, LinearMap.mem_ker]
      constructor
      · intro h0
        rw [← AdicCompletion.factor_evalₐ_eq_eval _ x (by simp), h0, map_zero]
      · intro h0
        rw [← AdicCompletion.factor_eval_eq_evalₐ _ x (by simp), h0, map_zero]
    have hmapn : (maximalIdeal D ^ n).map (algebraMap D R) = (maximalIdeal A ^ n).map (algebraMap A R) := by
      rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow, Ideal.map_map]
      change (maximalIdeal A ^ n).map (g.comp _) = _
      rw [hg]
    refine LocalFlat.relationsLift_of_square
      (AdicCompletion.evalₐ (maximalIdeal A) n).toRingHom
      (Ideal.Quotient.mk ((maximalIdeal A ^ n).map (algebraMap A R)))
      (algebraMap _ _) (AdicCompletion.surjective_evalₐ _ n) Ideal.Quotient.mk_surjective ?_ ?_ ?_ ?_
    · ext x
      exact (hkerA x)
    · rw [Ideal.mk_ker, hmapn]
    · ext x
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (maximalIdeal A) n x)
      have hx : x - algebraMap A D a ∈ maximalIdeal D ^ n := by
        rw [← hkerA, map_sub, ← ha, AlgHom.commutes, sub_eq_zero]
        rfl
      have hx' : algebraMap D R x - h a ∈ (maximalIdeal A ^ n).map (algebraMap A R) := by
        rw [← hmapn, ← hgA]
        rw [show algebraMap D R x - g (algebraMap A D a) = algebraMap D R (x - algebraMap A D a) from
          (map_sub g _ _).symm]
        exact Ideal.mem_map_of_mem _ hx
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ← ha]
      rw [Ideal.Quotient.algebraMap_quotient_map_quotient, eq_comm, Ideal.Quotient.eq]
      exact hx'
    · rw [RingHom.flat_algebraMap_iff]
      exact Module.Flat.of_linearEquiv
        (Algebra.TensorProduct.quotIdealMapEquivQuotTensor R (maximalIdeal A ^ n)).toLinearEquiv
  haveI : Algebra.FormallyUnramified D (ResidueField R) := by
    rw [← RingHom.formallyUnramified_algebraMap]
    have e : (algebraMap D (ResidueField R)).comp (algebraMap A D) = (residue R).comp h := by
      rw [← hg]; rfl
    exact RingHom.FormallyUnramified.of_comp (f := algebraMap A D) (by rw [e]; exact hfu)
  haveI : Algebra.FormallyUnramified D R :=
    GlobalTheory.EtaleCompletionNormal.formallyUnramified_of_map_maximalIdeal hmA
  haveI : Algebra.FinitePresentation D R :=
    (Algebra.FinitePresentation.of_finiteType (R := D) (A := R)).1 inferInstance
  exact ⟨g, hg, Algebra.Etale.of_formallyUnramified_of_flat⟩

end GlobalTheory.NormalBaseChange
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToricTorsionSectionEqPulledTraitPointField
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToricTorsionSectionEqPulledTraitPointField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.ToricOverField

theorem unitOn_val_map {U B : Type} [CommRing U] [CommRing B] (w : U →+* B) (x : Uˣ) (y : Bˣ)
    (h : (y : B) = w x) : (unitOn y).val = (spMap w).appTop.hom (unitOn x).val := by
  have k := congrArg (fun φ => φ.hom (x : U)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom w))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at k
  change (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (y : B) = _
  rw [h]
  exact k

theorem exists_point {A B X : Type} [CommRing A] [CommRing B] [AddCommGroup X] (f : A →+* B)
    (τ : Multiplicative X →* Bˣ) : ∃ z : Over.mk (spMap f) ⟶ splitTorus (Sp A) X,
      ∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ (Multiplicative.ofAdd χ)) := by
  refine ⟨(GlobalTheory.splitTorusPointsEquiv (Sp A) X (Over.mk (spMap f))).symm
    ((Units.map (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom.toMonoidHom).comp τ), fun χ => ?_⟩
  rw [GlobalTheory.UU.chV, MulEquiv.apply_symm_apply]
  rfl

theorem toric_section_eq_over_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W]
    (t' : SAB H (Sp W)) (P' : PELUnif (maximalIdeal W) t') (k : ℕ)
    (s' : ∀ (A : Type) [CommRing A] (a : W →+* A) (τ : Multiplicative P'.D.toPre.X →* Aˣ), τ ^ k = 1 → (Over.mk (spMap a) ⟶ t'.G)),
    (∀ (A A' : Type) [CommRing A] [CommRing A'] (a : W →+* A) (ha : ∀ x ∈ maximalIdeal W, a x = 0) (a' : W →+* A')
      (f : A →+* A') (t₀ : SAB H (Sp A)) (m₀ : SABMap t₀ t' (spMap a)) τ h
      (z : Over.mk (spMap f) ⟶ splitTorus (Sp A) P'.D.toPre.X),
      a' = f.comp a → (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ (Multiplicative.ofAdd χ))) →
      (s' A' a' τ h).left = (z ≫ GlobalTheory.TorusPart.PELUnif.torus P' ha m₀).left ≫ m₀.φ) →
    ∀ (R : Type) [CommRing R] (t : SAB H (Sp R)) (g : R →+* W) (m : SABMap t' t (spMap g))
      (V : Type) [CommRing V] (ψ : R →+* V) (tV : SAB H (Sp V)) (mV : SABMap tV t (spMap ψ))
      (Ω : Type) [Field Ω] (α : V →+* Ω) (β : W →+* Ω) (hβ : ∀ x ∈ maximalIdeal W, β x = 0)
      (tΩ : SAB H (Sp Ω)) (n : SABMap tΩ tV (spMap α)) (n' : SABMap tΩ t' (spMap β))
      (j : splitTorus (Sp V) P'.D.toPre.X ⟶ tV.G),
      GlobalTheory.TorusPart.pullTorus n.cart j = GlobalTheory.TorusPart.PELUnif.torus P' hβ n' →
      n.φ ≫ mV.φ = n'.φ ≫ m.φ →
    ∀ (Ω' : Type) [Field Ω'] (σ : Ω →+* Ω') (a' : W →+* Ω'), a' = σ.comp β →
    ∀ (U : Type) [CommRing U] (u : V →+* U) (w : U →+* Ω'), w.comp u = σ.comp α →
    ∀ (τU : Multiplicative P'.D.toPre.X →* Uˣ) (τ'' : Multiplicative P'.D.toPre.X →* Ω'ˣ) (h : τ'' ^ k = 1),
      (∀ χ, (τ'' χ : Ω') = w (τU χ : U)) →
    ∀ (z : Over.mk (spMap u) ⟶ splitTorus (Sp V) P'.D.toPre.X),
      (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τU (Multiplicative.ofAdd χ))) →
      (s' Ω' a' τ'' h).left ≫ m.φ = spMap w ≫ (z ≫ j).left ≫ mV.φ := by
  intro E _ _ _ H W _ _ _ t' P' k s' hs R _ t g m V _ ψ tV mV Ω _ α β hβ tΩ n n' j hj hn
    Ω' _ σ a' ha' U _ u w hw τU τ'' h hτ z hz
  obtain ⟨z', hz'⟩ := exists_point σ τ''
  have key : z'.left ≫ SplitTorus.bcMap (spMap α) P'.D.toPre.X = spMap w ≫ z.left := by
    refine GlobalTheory.UU.splitTorus_left_hom_ext _ _ ?_ fun χ => ?_
    · rw [Category.assoc, SplitTorus.bcMap_hom, ← Category.assoc, Over.w z', Category.assoc, Over.w z]
      change spMap σ ≫ spMap α = spMap w ≫ spMap u
      simp only [spMap]
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hw]
    · rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, GlobalTheory.UU.bcMap_charUnit,
        Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
      have e1 := (GlobalTheory.UU.chV_val z' χ).symm.trans (congrArg Units.val (hz' χ))
      have e2 := (GlobalTheory.UU.chV_val z χ).symm.trans (congrArg Units.val (hz χ))
      exact e1.trans ((unitOn_val_map w _ _ (hτ _)).trans (congrArg _ e2.symm))
  rw [hs Ω Ω' β hβ a' σ tΩ n' τ'' h z' ha' hz', ← hj, Category.assoc, ← hn, Over.comp_left, Over.comp_left,
    Category.assoc, ← Category.assoc _ n.φ, GlobalTheory.TorusPart.pullTorus_left, Category.assoc,
    ← Category.assoc z'.left, key]
  simp only [Category.assoc]

end GlobalTheory.ToricOverField
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToricTorsionSectionEqPulledTraitPointFieldStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toricTorsionSection_eq_pulled_trait_point_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W]
    (t' : SAB H (Sp W)) (P' : PELUnif (maximalIdeal W) t') (k : ℕ)
    (s' : ∀ (A : Type) [CommRing A] (a : W →+* A) (τ : Multiplicative P'.D.toPre.X →* Aˣ), τ ^ k = 1 → (Over.mk (spMap a) ⟶ t'.G)),
    (∀ (A A' : Type) [CommRing A] [CommRing A'] (a : W →+* A) (ha : ∀ x ∈ maximalIdeal W, a x = 0) (a' : W →+* A')
      (f : A →+* A') (t₀ : SAB H (Sp A)) (m₀ : SABMap t₀ t' (spMap a)) τ h
      (z : Over.mk (spMap f) ⟶ splitTorus (Sp A) P'.D.toPre.X),
      a' = f.comp a → (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ (Multiplicative.ofAdd χ))) →
      (s' A' a' τ h).left = (z ≫ GlobalTheory.TorusPart.PELUnif.torus P' ha m₀).left ≫ m₀.φ) →
    ∀ (R : Type) [CommRing R] (t : SAB H (Sp R)) (g : R →+* W) (m : SABMap t' t (spMap g))
      (V : Type) [CommRing V] (ψ : R →+* V) (tV : SAB H (Sp V)) (mV : SABMap tV t (spMap ψ))
      (Ω : Type) [Field Ω] (α : V →+* Ω) (β : W →+* Ω) (hβ : ∀ x ∈ maximalIdeal W, β x = 0)
      (tΩ : SAB H (Sp Ω)) (n : SABMap tΩ tV (spMap α)) (n' : SABMap tΩ t' (spMap β))
      (j : splitTorus (Sp V) P'.D.toPre.X ⟶ tV.G),
      GlobalTheory.TorusPart.pullTorus n.cart j = GlobalTheory.TorusPart.PELUnif.torus P' hβ n' →
      n.φ ≫ mV.φ = n'.φ ≫ m.φ →
    ∀ (Ω' : Type) [Field Ω'] (σ : Ω →+* Ω') (a' : W →+* Ω'), a' = σ.comp β →
    ∀ (U : Type) [CommRing U] (u : V →+* U) (w : U →+* Ω'), w.comp u = σ.comp α →
    ∀ (τU : Multiplicative P'.D.toPre.X →* Uˣ) (τ'' : Multiplicative P'.D.toPre.X →* Ω'ˣ) (h : τ'' ^ k = 1),
      (∀ χ, (τ'' χ : Ω') = w (τU χ : U)) →
    ∀ (z : Over.mk (spMap u) ⟶ splitTorus (Sp V) P'.D.toPre.X),
      (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τU (Multiplicative.ofAdd χ))) →
      (s' Ω' a' τ'' h).left ≫ m.φ = spMap w ≫ (z ≫ j).left ≫ mV.φ := by
  first | exact @GlobalTheory.ToricOverField.toric_section_eq_over_field | exact GlobalTheory.ToricOverField.toric_section_eq_over_field | (intros; apply GlobalTheory.ToricOverField.toric_section_eq_over_field <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationLtOneOfInvNotMem
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO)
open Pointwise

namespace GlobalTheory.WittFracPlace

theorem valuation_intCast_lt_one_iff {Ω : Type*} [Field Ω] (A : ValuationSubring Ω) {p : ℕ} (hp : p.Prime)
    (h : A.valuation (p : Ω) < 1) (n : ℤ) : A.valuation (n : Ω) < 1 ↔ (p : ℤ) ∣ n := by
  have hle : ∀ m : ℤ, A.valuation (m : Ω) ≤ 1 := fun m => (A.valuation_le_one_iff _).2 (intCast_mem A m)
  have hmul : ∀ (m : ℤ) (x : Ω), A.valuation x < 1 → A.valuation (m * x) < 1 := fun m x hx => by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (hle m)) hx
  constructor
  · intro hn
    by_contra hd
    obtain ⟨a, b, hab⟩ := ((Nat.prime_iff_prime_int.1 hp).irreducible.coprime_iff_not_dvd).2 hd
    have e : (a : Ω) * p + b * n = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab
    have := Valuation.map_add_lt _ (hmul a _ h) (hmul b _ hn)
    rw [e, map_one] at this
    exact lt_irrefl _ this
  · rintro ⟨m, rfl⟩
    rw [Int.cast_mul, mul_comm, Int.cast_natCast]
    exact hmul m _ h

theorem exists_smul_eq {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {p : ℕ} (hp : p.Prime)
    (A A' : ValuationSubring Ω) (h : A.valuation (p : Ω) < 1) (h' : A'.valuation (p : Ω) < 1) :
    ∃ g : Ω ≃ₐ[ℚ] Ω, g • A = A' := by
  have hpr : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2 (Nat.prime_iff_prime_int.1 hp)
  let v : HeightOneSpectrum (𝓞 ℚ) :=
    ⟨(Ideal.span {(p : ℤ)}).comap Rat.ringOfIntegersEquiv.toRingHom, Ideal.comap_isPrime _ _, fun hb => by
      have h1 : (p : 𝓞 ℚ) ∈ (Ideal.span {(p : ℤ)}).comap Rat.ringOfIntegersEquiv.toRingHom := by
        rw [Ideal.mem_comap, map_natCast]; exact Ideal.subset_span rfl
      rw [hb, Ideal.mem_bot] at h1
      exact hp.ne_zero (by exact_mod_cast h1)⟩
  have key : ∀ B : ValuationSubring Ω, B.valuation (p : Ω) < 1 →
      ∀ x : 𝓞 ℚ, B.valuation (algebraMap ℚ Ω (x : ℚ)) < 1 ↔ x ∈ v.asIdeal := by
    intro B hB x
    obtain ⟨n, rfl⟩ := Rat.ringOfIntegersEquiv.symm.surjective x
    have e : Rat.ringOfIntegersEquiv.symm n = (n : 𝓞 ℚ) := eq_intCast Rat.ringOfIntegersEquiv.symm.toRingHom n
    have e2 : algebraMap ℚ Ω ((n : 𝓞 ℚ) : ℚ) = (n : Ω) :=
      map_intCast ((algebraMap ℚ Ω).comp (algebraMap (𝓞 ℚ) ℚ)) n
    rw [e, e2, valuation_intCast_lt_one_iff B hp hB]
    change _ ↔ (n : 𝓞 ℚ) ∈ Ideal.comap _ _
    rw [Ideal.mem_comap, map_intCast, Int.cast_id, Ideal.mem_span_singleton]
  exact ReciprocityTheory.Gal.exists_smul_eq_of_over (key A h) (key A' h')

theorem valuation_lt_one_of_inv_notMem {Ω : Type*} [Field Ω] (A : ValuationSubring Ω) {x : Ω} (h : x⁻¹ ∉ A) :
    A.valuation x < 1 := by
  rw [← A.valuation_le_one_iff, map_inv₀, not_le] at h
  have h0 : A.valuation x ≠ 0 := fun e => by simp [e] at h
  exact (one_lt_inv₀ (zero_lt_iff.2 h0)).1 h

theorem exists_emb_inducing (L : Type) [Field L] [NumberField L] {p : ℕ} (hp : p.Prime)
    (v : HeightOneSpectrum (𝓞 L)) (hv : (p : 𝓞 L) ∈ v.asIdeal) (V : ValuationSubring ℂ) (hV : (p : ℂ)⁻¹ ∉ V) :
    ∃ e : L →+* ℂ, ∀ x, e x ∈ V ↔ v.valuation L x ≤ 1 := by
  let Ω := AlgebraicClosure L
  have : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ L Ω
  have : IsAlgClosure ℚ Ω := ⟨inferInstance, inferInstance⟩
  let ι : Ω →ₐ[ℚ] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  obtain ⟨A', hA'⟩ := GlobalTheory.exists_valuationSubring_comap_eq (v.valuation L).valuationSubring (algebraMap L Ω)
  have hm : ∀ x : L, algebraMap L Ω x ∈ A' ↔ v.valuation L x ≤ 1 := fun x => by
    rw [← ValuationSubring.mem_comap, hA', Valuation.mem_valuationSubring_iff]
  have h1 : (V.comap ι.toRingHom).valuation (p : Ω) < 1 := valuation_lt_one_of_inv_notMem _ (by
    rwa [ValuationSubring.mem_comap, map_inv₀, map_natCast])
  have h2 : A'.valuation (p : Ω) < 1 := valuation_lt_one_of_inv_notMem _ (by
    have h3 : v.valuation L (p : L) < 1 := by
      have := (v.valuation_lt_one_iff_mem (K := L) (p : 𝓞 L)).2 hv
      rw [← map_natCast (algebraMap (𝓞 L) L) p]
      exact this
    have h4 : v.valuation L (p : L) ≠ 0 := by simpa using hp.ne_zero
    rw [← map_natCast (algebraMap L Ω), ← map_inv₀, hm, map_inv₀, not_le]
    exact (one_lt_inv₀ (zero_lt_iff.2 h4)).2 h3)
  obtain ⟨g, hg⟩ := exists_smul_eq hp _ _ h1 h2
  refine ⟨(ι.toRingHom.comp g.symm.toRingEquiv.toRingHom).comp (algebraMap L Ω), fun x => ?_⟩
  rw [← hm, ← hg, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  rfl

theorem exists_jcPin : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (la : PlL D p), ∃ jc : DV.KW p →+* ℂ, JcPin D p la jc := by
  intro D p hp la
  obtain ⟨j⟩ := GlobalTheory.WittFracComplex.nonempty_ringHom_complex p
  obtain ⟨V, -, -, -, hV⟩ :=
    GlobalTheory.exists_valuationSubring_dominating (V := WittVector p (AlgebraicClosure (ZMod p))) j
  have hp' : (p : ℂ)⁻¹ ∉ V := by
    rw [← map_natCast j, ← map_inv₀, hV]
    rintro ⟨a, ha⟩
    have hinj := IsFractionRing.injective (WittVector p (AlgebraicClosure (ZMod p))) (DV.KW p)
    have h0 : (p : DV.KW p) ≠ 0 := fun e => hp.out.ne_zero (by
      have := congrArg j e
      rw [map_natCast, map_zero] at this
      exact_mod_cast this)
    refine (WittVector.irreducible p (k := AlgebraicClosure (ZMod p))).not_isUnit
      (isUnit_iff_exists_inv.2 ⟨a, hinj ?_⟩)
    rw [map_mul, ha, map_natCast, map_one, mul_inv_cancel₀ h0]
  obtain ⟨e, he⟩ := exists_emb_inducing D.what₂.LL hp.out la.1 la.2 V hp'
  have : Countable D.what₂.LL := Cardinal.mk_le_aleph0_iff.1
    ((Algebra.IsAlgebraic.cardinalMk_le_max ℚ D.what₂.LL).trans (by simp))
  obtain ⟨τ, hτ⟩ := GlobalTheory.CompRat.exists_ringEquiv_complex_comp_eq D.what₂.LL e D.what₂.embLL
  refine ⟨τ.toRingHom.comp j, V.comap τ.symm.toRingHom, fun x => ?_, fun a => ?_⟩
  · rw [← he, ← hτ, ValuationSubring.mem_comap]
    simp
  · rw [← hV, ValuationSubring.mem_comap]
    simp

end GlobalTheory.WittFracPlace
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ForcedContentSupportPrimes
noncomputable section

namespace GlobalTheory.Mem.NonzeroPlacesOverPrimes

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def forcedContentSupportPrimes (K : Ctx) (P : Pre) : Finset ℕ :=
  {P.host.g 0, P.host.g 1, P.host.d} ∪ Finset.range (⌊K.s.X'' P.R.n⌋₊ + 1)

end GlobalTheory.Mem.NonzeroPlacesOverPrimes

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModuliOfSignatureEq
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

open MonoidalCategory CartesianMonoidalCategory MonObj

namespace GlobalTheory.ModuliGenus

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_eq_nsmul_of_dvd (D : Datum H) {n : ℕ} (hn : 0 < n) (a : D.La) (h : ∀ b, (n : ℤ) ∣ D.EF a b) :
    ∃ e, a = n • e := by
  choose c hc using h
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  let ψ : D.La →+ ℤ := AddMonoidHom.mk' c fun x y => mul_left_cancel₀ hn' (by rw [mul_add, ← hc, ← hc, ← hc, map_add (f := _)])
  obtain ⟨e, he⟩ := D.unimod.2 ψ.toIntLinearMap
  refine ⟨e, D.unimod.1 (LinearMap.ext fun b => ?_)⟩
  rw [map_nsmul, he, hc, LinearMap.smul_apply, nsmul_eq_mul]
  rfl

variable {l : Level H} {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B}

end GlobalTheory.ModuliGenus
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurePreservingFlagFibreChartCoordinates
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurePreservingFlagFibreChartCoordinates
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

namespace GlobalTheory.FlagFibre

theorem measurePreserving_coords_sorted (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (X : Data E r) (Tau : Type) [Fintype Tau] (κ : Tau ≃ X.Ψ) :
    MeasurePreserving (coords X κ) volume volume := by
  let e : Fin (nd X) ≃ Tau × Low r :=
    ((Equiv.prodCongr κ (Equiv.refl (Low r))).trans (Fintype.equivFin (Ent X))).symm
  have h1 := GlobalTheory.volume_preserving_ofLp_complex (Fin (nd X))
  have h2 := volume_preserving_arrowCongr' e (MeasurableEquiv.refl ℂ) (MeasurePreserving.id _)
  have h3 := GlobalTheory.FlagBase.PoissonV.measurePreserving_curry Tau (Low r)
  exact h3.comp (h2.comp h1)

end GlobalTheory.FlagFibre
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurePreservingFlagFibreChartCoordinatesStatement
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurePreserving_flagFibreChartCoordinates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Tau : Type) [Fintype Tau] (κ : Tau ≃ X.Ψ), MeasurePreserving (coords X κ) volume volume := by
  first | exact @GlobalTheory.FlagFibre.measurePreserving_coords_sorted | exact GlobalTheory.FlagFibre.measurePreserving_coords_sorted | (intros; apply GlobalTheory.FlagFibre.measurePreserving_coords_sorted <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VecOfMulToMatMul
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal
open scoped Kronecker

namespace GlobalTheory.FlagFibre

theorem vecOf_mul_toMat_mul {p q : ℕ} (R : Matrix (Fin p) (Fin p) ℂ) (T : Matrix (Fin q) (Fin q) ℂ)
    (v : Fin p × Fin q → ℂ) : Formalism.MJ.vecOf (R * toMat v * T) = Matrix.toLin' (R ⊗ₖ Tᵀ) v := by
  funext ⟨a, b⟩
  simp only [Formalism.MJ.vecOf, Matrix.toLin'_apply, mulVec, dotProduct, Fintype.sum_prod_type, Matrix.mul_apply,
    kroneckerMap_apply, transpose_apply, toMat, of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem lintegral_affine :
    ∀ (p q : ℕ) (R : Matrix (Fin p) (Fin p) ℂ) (T : Matrix (Fin q) (Fin q) ℂ) (C : Matrix (Fin p) (Fin q) ℂ), IsUnit R.det → IsUnit T.det → ∀ f : (Fin p × Fin q → ℂ) → ℝ≥0∞, Measurable f → ∫⁻ v : Fin p × Fin q → ℂ, f (vecOf (R * toMat v * T + C)) = ENNReal.ofReal ((Complex.normSq R.det ^ q * Complex.normSq T.det ^ p)⁻¹) * ∫⁻ v, f v := by
  intro p q R T C hR hT f hf
  set Lr : (Fin p × Fin q → ℂ) →ₗ[ℝ] (Fin p × Fin q → ℂ) := (Matrix.toLin' (R ⊗ₖ Tᵀ)).restrictScalars ℝ with hLr
  have hdet : LinearMap.det Lr = Complex.normSq R.det ^ q * Complex.normSq T.det ^ p := by
    rw [hLr, LinearMap.det_restrictScalars, Algebra.norm_complex_apply, LinearMap.det_toLin', det_kronecker,
      det_transpose]
    simp
  have hpos : 0 < Complex.normSq R.det ^ q * Complex.normSq T.det ^ p :=
    mul_pos (pow_pos (Complex.normSq_pos.2 hR.ne_zero) _) (pow_pos (Complex.normSq_pos.2 hT.ne_zero) _)
  have hdet0 : LinearMap.det Lr ≠ 0 := by rw [hdet]; exact hpos.ne'
  have hLm : Measurable Lr := (LinearMap.continuous_of_finiteDimensional Lr).measurable
  have hg : Measurable fun w : Fin p × Fin q → ℂ => f (w + Formalism.MJ.vecOf C) := hf.comp (measurable_add_const _)
  have e1 : ∫⁻ v : Fin p × Fin q → ℂ, f (Formalism.MJ.vecOf (R * toMat v * T + C)) =
      ∫⁻ w, f (w + Formalism.MJ.vecOf C) ∂(Measure.map Lr volume) := by
    rw [lintegral_map hg hLm]
    refine lintegral_congr fun v => ?_
    have : Formalism.MJ.vecOf (R * toMat v * T + C) = Formalism.MJ.vecOf (R * toMat v * T) + Formalism.MJ.vecOf C := rfl
    rw [this, vecOf_mul_toMat_mul]; rfl
  refine e1.trans ?_
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet0, lintegral_smul_measure, hdet,
    abs_of_nonneg (inv_nonneg.2 hpos.le), smul_eq_mul, lintegral_add_right_eq_self]

end GlobalTheory.FlagFibre
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LintegralPiFibreMeasurePreserving
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LintegralPiFibreMeasurePreserving
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

namespace GlobalTheory.ProdFibre

theorem lintegral_pi_fibre : ∀ (T A B C : Type) [Fintype T] [MeasureSpace A] [MeasureSpace B] [MeasureSpace C] [SigmaFinite (volume : Measure A)] [SigmaFinite (volume : Measure B)] [SigmaFinite (volume : Measure C)] (g : A × B → C) (π : C → A) (D : C → ℝ≥0∞) (φ : (T → A) → ℝ≥0∞), MeasurePreserving g volume volume → Measurable π → (∀ w, π (g w) = w.1) → Measurable D → Measurable φ → ∫⁻ c : T → C, φ (fun t => π (c t)) * ∏ t, D (c t) = ∫⁻ a : T → A, φ a * ∏ t, ∫⁻ b, D (g (a t, b)) := by
  intro T A B C _ _ _ _ _ _ _ g π D φ hg hπ hgπ hD hφ
  have h1 : MeasurePreserving (fun (a : T → A × B) (t : T) => g (a t)) volume volume :=
    volume_preserving_pi (f := fun _ : T => g) (fun _ => hg)
  have h2 := (volume_measurePreserving_arrowProdEquivProdArrow A B T).symm
  have h3 := h1.comp h2
  have hF : Measurable (fun c : T → C => φ (fun t => π (c t)) * ∏ t, D (c t)) := by
    refine Measurable.mul (hφ.comp ?_) ?_
    · exact Measurable.of_eval (fun t => hπ.comp (measurable_pi_apply t))
    · exact Finset.measurable_prod _ (fun t _ => hD.comp (measurable_pi_apply t))
  rw [← h3.lintegral_comp hF, Measure.volume_eq_prod]
  refine (lintegral_prod _ (hF.comp h3.measurable).aemeasurable).trans ?_
  refine lintegral_congr (fun a => ?_)
  have hm : ∀ t, Measurable (fun b : B => D (g (a t, b))) := fun t =>
    hD.comp (hg.measurable.comp measurable_prodMk_left)
  have hin := GlobalTheory.SnMass.Push.lintegral_fintype_prod (X := fun _ : T => B)
    (μ := fun _ => (volume : Measure B)) (fun t b => D (g (a t, b))) hm
  rw [← hin, ← volume_pi, ← lintegral_const_mul]
  · refine lintegral_congr (fun b => ?_)
    change φ (fun t => π (g (a t, b t))) * ∏ t, D (g (a t, b t)) = _
    simp only [hgπ]
  · exact Finset.measurable_prod _ (fun t _ => (hm t).comp (measurable_pi_apply t))

end GlobalTheory.ProdFibre
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LintegralPiFibreMeasurePreservingStatement
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_pi_fibre_measurePreserving : ∀ (T A B C : Type) [Fintype T] [MeasureSpace A] [MeasureSpace B] [MeasureSpace C] [SigmaFinite (volume : Measure A)] [SigmaFinite (volume : Measure B)] [SigmaFinite (volume : Measure C)] (g : A × B → C) (π : C → A) (D : C → ℝ≥0∞) (φ : (T → A) → ℝ≥0∞), MeasurePreserving g volume volume → Measurable π → (∀ w, π (g w) = w.1) → Measurable D → Measurable φ → ∫⁻ c : T → C, φ (fun t => π (c t)) * ∏ t, D (c t) = ∫⁻ a : T → A, φ a * ∏ t, ∫⁻ b, D (g (a t, b)) := by
  first | exact @GlobalTheory.ProdFibre.lintegral_pi_fibre | exact GlobalTheory.ProdFibre.lintegral_pi_fibre | (intros; apply GlobalTheory.ProdFibre.lintegral_pi_fibre <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPointOfDecoratedLatticeSplicedAtPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPointOfDecoratedLatticeSplicedAtPlace
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.UG.P Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.Col2.Splice

theorem isPtOf_splice : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG Q Q0 Q1 : Finset (HeightOneSpectrum (𝓞 E))) (v : HeightOneSpectrum (𝓞 F)) (g0 h : GL (Fin n) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) (p0 : DecoF E n ST SG Q0) (p1 : DecoF E n ST SG Q1) (q : DecoF E n ST SG Q), GlobalTheory.Mem.Col2.IsPtOf hc g0 p0 → GlobalTheory.Mem.Col2.IsPtOf hc h p1 → (∀ P ∈ Q, ¬ IsOver v P) → (∀ w ∈ SG, ¬ IsOver v w) → Deco.SameOff ST SG v q.deco.1 p1.deco.1 → (∀ P : HeightOneSpectrum (𝓞 E), IsOver v P → localization₂ P.asIdeal q.deco.1.N = localization₂ P.asIdeal p0.deco.1.N) → (∀ P : ST, IsOver v P.1 → q.deco.1.f P = p0.deco.1.f P) → (∀ P : Q, ∃ P' : Q1, P'.1 = P.1 ∧ p1.fr P' = q.fr P) → GlobalTheory.Mem.Col2.IsPtOf hc (h * rll_put n v (bc (prV (E := E) v) (h⁻¹ * g0))) q := by
  intro F E _ _ _ _ _ _ hc n _ ST SG Q Q0 Q1 v g0 h p0 p1 q h0 h1 hQ hSG hoff hN hf hfr
  obtain ⟨⟨hg0, hd0⟩, -⟩ := (ChTwRead.isPtOf_iff hc g0 p0).1 h0
  obtain ⟨⟨hh, hd1⟩, hfr1⟩ := (ChTwRead.isPtOf_iff hc h p1).1 h1
  set m := h * rll_put n v (bc (prV (E := E) v) (h⁻¹ * g0)) with hm
  have hv : bc (prV (E := E) v) m = bc (prV (E := E) v) g0 := by
    rw [hm, map_mul, rll_put_self, ← map_mul, mul_inv_cancel_left]
  have hne : ∀ P : HeightOneSpectrum (𝓞 E), ¬ IsOver v P → P.under (𝓞 F) ≠ v := by
    rintro P hP rfl
    exact hP rfl
  have hw : ∀ P : HeightOneSpectrum (𝓞 E), ¬ IsOver v P →
      bc (prV (E := E) (P.under (𝓞 F))) m = bc (prV (E := E) (P.under (𝓞 F))) h := by
    intro P hP
    rw [hm, map_mul, rll_put_ne n v _ (hne P hP), mul_one]
  have hmU : m ∈ UAd hc n :=
    mul_mem hh (rll_put_mem_UAd hc n v (afsplit_bc_mem hc.sig 1 v _ (mul_mem (inv_mem hh) hg0)))
  refine (ChTwRead.isPtOf_iff hc m q).2 ⟨⟨hmU, ?_⟩, fun P i j => ?_⟩
  · ext1
    · refine Formalism.L2.DIV.eq_of_forall_localized_eq fun P => ?_
      by_cases hP : IsOver v P
      · rw [hN P hP, hd0]
        exact (updn_mem_loc hP hv).symm
      · rw [hoff.N P hP, hd1]
        exact (updn_mem_loc (v := P.under (𝓞 F)) rfl (hw P hP)).symm
    · funext P
      by_cases hP : IsOver v P.1
      · rw [hf P hP, hd0]
        exact (updn_f_loc ST SG P hP hv).symm
      · rw [hoff.f P hP, hd1]
        exact (updn_f_loc ST SG (v := P.1.under (𝓞 F)) P rfl (hw P.1 hP)).symm
    · funext w
      have hP := hSG w.1 w.2
      rw [hoff.be w hP, hd1]
      exact (updn_be_loc ST SG (v := w.1.under (𝓞 F)) w rfl (hw w.1 hP)).symm
  · obtain ⟨⟨P1, hP1⟩, hP', e⟩ := hfr P
    have hPv := hQ P.1 P.2
    simp only at hP'
    subst hP'
    rw [← e, ← hfr1 ⟨_, hP1⟩ i j]
    refine ChTwRead.adAt_congr_prV P.1 ?_
    have := congrArg (fun g : GL (Fin n) (E ⊗[F] (P.1.under (𝓞 F)).adicCompletion F) =>
      g.val i j) (hw P.1 hPv)
    exact this

end GlobalTheory.Mem.Col2.Splice
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPointOfDecoratedLatticeSplicedAtPlaceStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.UG.P Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPointOf_decoratedLattice_splicedAtPlace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG Q Q0 Q1 : Finset (HeightOneSpectrum (𝓞 E))) (v : HeightOneSpectrum (𝓞 F)) (g0 h : GL (Fin n) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) (p0 : DecoF E n ST SG Q0) (p1 : DecoF E n ST SG Q1) (q : DecoF E n ST SG Q), GlobalTheory.Mem.Col2.IsPtOf hc g0 p0 → GlobalTheory.Mem.Col2.IsPtOf hc h p1 → (∀ P ∈ Q, ¬ IsOver v P) → (∀ w ∈ SG, ¬ IsOver v w) → Deco.SameOff ST SG v q.deco.1 p1.deco.1 → (∀ P : HeightOneSpectrum (𝓞 E), IsOver v P → localization₂ P.asIdeal q.deco.1.N = localization₂ P.asIdeal p0.deco.1.N) → (∀ P : ST, IsOver v P.1 → q.deco.1.f P = p0.deco.1.f P) → (∀ P : Q, ∃ P' : Q1, P'.1 = P.1 ∧ p1.fr P' = q.fr P) → GlobalTheory.Mem.Col2.IsPtOf hc (h * rll_put n v (bc (prV (E := E) v) (h⁻¹ * g0))) q := by
  first | exact @GlobalTheory.Mem.Col2.Splice.isPtOf_splice | exact GlobalTheory.Mem.Col2.Splice.isPtOf_splice | (intros; apply GlobalTheory.Mem.Col2.Splice.isPtOf_splice <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoverFieldOfWeberLev
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.FieldSize GlobalTheory.FinalJoin
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.Bl.CoverAt

theorem exists_finset_weberIn (r : ℂ) (M : ℕ) (hM : M ≠ 0) : ∃ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) ∧
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), H.rt0 = r →
      ∀ F : IntermediateField ℚ ℂ, (∀ z ∈ S, z ∈ F) → WeberIn H F M := by
  by_cases h : ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : IsCMField E) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), H.rt0 = r
  · obtain ⟨E₀, _, _, _, H₀, h₀⟩ := h
    obtain ⟨L₀, hL₀⟩ := GlobalTheory.FinalJoin.CurveField.exists_periodPair H₀
    obtain ⟨hfin, halg, -⟩ := weberSet_finite_algebraic_permuted L₀ M (Nat.pos_of_ne_zero hM)
      (GlobalTheory.CompRat.Weber.g₂_ne_zero H₀ L₀ hL₀) (GlobalTheory.CompRat.Weber.g₃_ne_zero H₀ L₀ hL₀)
    refine ⟨hfin.toFinset, fun z hz => halg (GlobalTheory.WeberField.invariant_isAlgebraic H₀ L₀ hL₀) z (hfin.mem_toFinset.1 hz), ?_⟩
    intro E _ _ _ H hH F hF L hL
    have hw : ∀ s, GlobalTheory.CompRat.wC H s = GlobalTheory.CompRat.wC H₀ s := fun s => by
      unfold GlobalTheory.CompRat.wC
      rw [hH, h₀]
    have e : weberSet L M = weberSet L₀ M :=
      GlobalTheory.FieldSize.SmallField.weberSet_congr (Submodule.ext fun z => by
        rw [hL z, hL₀ z]
        simp only [hw]) M
    have hs : ∀ z ∈ weberSet L M, z ∈ F := fun z hz => hF z (hfin.mem_toFinset.2 (e ▸ hz))
    exact ⟨hs _ (Set.mem_insert _ _), fun s hs' => hs _ (Set.mem_insert_of_mem _ ⟨_, (hL _).2 ⟨s, rfl⟩, hs', rfl⟩)⟩
  · exact ⟨∅, by simp, fun E _ _ _ H hH => absurd ⟨E, _, _, _, H, hH⟩ h⟩

open Classical in
def WeberLev (B : Base) (f : Fr B.toPre) (T : TwDat B) : Prop :=
  ∀ S : Finset (HeightOneSpectrum (𝓞 B.host.E)), (∀ Q ∈ S, ∃ χ ∈ T.set f, ¬ χ.UnrAt Q) →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
      H.rt0 = B.host.φ₀ B.host.sqrtMinusD →
      WeberIn H B.LLC (B.host.g 0 * B.host.g 1 * ∏ q ∈ S.image (fun Q => Nat.card (kP Q)), q)

open Classical in
theorem lg_weberLev (K : Ctx) : large₂ K WeberLev := by
  have h : ∀ (P : Pre) (Ξ : Set (HChar P.host.E)), ∃ Z : Finset ℂ, (∀ z ∈ Z, IsAlgebraic ℚ z) ∧
      ({Q : HeightOneSpectrum (𝓞 P.host.E) | ∃ χ ∈ Ξ, ¬ χ.UnrAt Q}.Finite →
        ∀ S : Finset (HeightOneSpectrum (𝓞 P.host.E)), (∀ Q ∈ S, ∃ χ ∈ Ξ, ¬ χ.UnrAt Q) →
        ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
          H.rt0 = P.host.φ₀ P.host.sqrtMinusD → ∀ F : IntermediateField ℚ ℂ, (∀ z ∈ Z, z ∈ F) →
          WeberIn H F (P.host.g 0 * P.host.g 1 * ∏ q ∈ S.image (fun Q => Nat.card (kP Q)), q)) := by
    intro P Ξ
    have hne : ∀ S : Finset (HeightOneSpectrum (𝓞 P.host.E)),
        P.host.g 0 * P.host.g 1 * ∏ q ∈ S.image (fun Q => Nat.card (kP Q)), q ≠ 0 := fun S => by
      refine mul_ne_zero (mul_ne_zero (P.host.g_prime 0).ne_zero (P.host.g_prime 1).ne_zero) ?_
      rw [Finset.prod_ne_zero_iff]
      intro q hq
      obtain ⟨Q, -, rfl⟩ := Finset.mem_image.1 hq
      exact GlobalTheory.Plug.TwistLevels.card_residueField_ne_zero Q
    choose Z hZ hZ' using fun S => exists_finset_weberIn (P.host.φ₀ P.host.sqrtMinusD) _ (hne S)
    by_cases hA : {Q : HeightOneSpectrum (𝓞 P.host.E) | ∃ χ ∈ Ξ, ¬ χ.UnrAt Q}.Finite
    · refine ⟨hA.toFinset.powerset.biUnion Z, fun z hz => ?_, fun _ S hS E _ _ _ H hH F hF => ?_⟩
      · obtain ⟨S, -, hz⟩ := Finset.mem_biUnion.1 hz
        exact hZ S z hz
      · exact hZ' S E H hH F fun z hz => hF z (Finset.mem_biUnion.2
          ⟨S, Finset.mem_powerset.2 fun Q hQ => hA.mem_toFinset.2 (hS Q hQ), hz⟩)
    · exact ⟨∅, by simp, fun h => absurd h hA⟩
  choose Z hZ hZ' using h
  refine ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun P _ _ _ Ξ => Z P Ξ, by simp,
    fun P _ _ _ Ξ => hZ P Ξ, fun B f T _ hH _ _ S hS E _ _ _ H hr => ?_⟩
  refine hZ' B.toPre (T.set f) ?_ S hS E H hr _ hH.2
  refine ((GlobalTheory.Mem.Top.TwFin.tw_fin B f T).1.biUnion fun χ hχ => GlobalTheory.Plug.TwistLevels.ram_finite B f T χ hχ).subset ?_
  rintro Q ⟨χ, hχ, hr⟩
  exact Set.mem_biUnion (x := χ) hχ hr

set_option maxHeartbeats 1000000 in
theorem coverField_of_weberLev {B : Base} {f : Fr B.toPre} {T : TwDat B} (hW : WeberLev B f T) (w : ColW B f T) (Z : w.Lt)
    (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : R3.Dat (w.st Z) w.I hX T Wt) :
    GlobalTheory.TwistField.CoverField z.core z.R.toRealDat := by
  intro i t l₂ _ hM hA Xo₂ c₂ hc
  have hP : z.core.Q.Pins := z.geo.fw.laws.pins
  have hS : ∀ Q ∈ z.R.Q t, ∃ χ ∈ T.set f, ¬ χ.UnrAt Q := fun Q hQ =>
    ⟨z.R.xiH t, by
      rw [z.lev.xiH t, ← w.xi_range]
      exact ⟨_, rfl⟩, (z.lev.is.Q_ram t Q).2 (Or.inl hQ)⟩
  have hw := hW (z.R.Q t) hS _ z.core.Q.H hP.1.2.2.1
  have hlev : l₂.M = B.host.g 0 * B.host.g 1 * GlobalTheory.TwistField.tupPrime z.R.toRealDat t := by
    rw [hM, show z.core.Q.l.M = _ from hP.2.1.1]
    rfl
  have hw' : WeberIn z.core.Q.H c₂.F l₂.M := by
    rw [hlev, hc]
    exact hw
  refine GlobalTheory.FinalJoin.FieldAlg.fnAlgClosed_of_weberIn _ z.core.Q hP ((i : ℕ) + 1) ⟨Nat.succ_le_succ (Nat.zero_le _), i.2⟩ l₂ Xo₂ c₂
    l₂.M (lt_of_lt_of_le (by norm_num) l₂.three_le) ?_ (Or.inl hw')
  rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level.M', hA, Nat.lcm_one_right]

end GlobalTheory.Mem.Top.Bl.CoverAt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameActionUpperTriangularBlockExists
section -- merged from Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.ProperlyDiscontinuousFlags
namespace GlobalTheory.IndefiniteRowSideFullHecke.ProperlyDiscontinuousFlags

open NumberField ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def flagTransporter (X : Data E r) (K L : Set (Frame X.Ψ r)) : Set (GL (Fin r) E) :=
  {γ | γ ∈ X.Γ ∧ ∃ x ∈ K, ∃ y ∈ L, ∃ b ∈ Bor X.Ψ r, lact γ x = rmul y b}

def ProperlyDiscontinuousOnFlags (X : Data E r) : Prop :=
  ∀ K : Set (Frame X.Ψ r), IsCompact K → K ⊆ X.dom → (flagTransporter X K K).Finite

end GlobalTheory.IndefiniteRowSideFullHecke.ProperlyDiscontinuousFlags
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.PropDiscOfFlagDomainData
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst

namespace GlobalTheory

theorem propDisc_of_flagDomainData :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), PropDisc X :=
  fun _ _ _ _ => GlobalTheory.ClosedDiscontinuity.propDisc_and_la1GG.1

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FiniteOfLocallyFinite
namespace GlobalTheory.PropDiscCompare

open NumberField Topology ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem _root_.GlobalTheory.PropDiscCompare.compact_of_local (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (h : _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.PropDisc X) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.ProperlyDiscontinuousFlags.ProperlyDiscontinuousOnFlags X := by
  intro K hK hKdom
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.PropDisc at h
  choose! U hU U' hU' hfin using h
  obtain ⟨t, ht, hcover⟩ := (hK.prod hK).elim_nhds_subcover
    (fun q : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r × _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r => U q.1 q.2 ×ˢ U' q.1 q.2)
    (fun q hq => prod_mem_nhds (hU q.1 (hKdom hq.1) q.2 (hKdom hq.2))
      (hU' q.1 (hKdom hq.1) q.2 (hKdom hq.2)))
  refine (t.finite_toSet.biUnion fun q hq =>
    hfin q.1 (hKdom (ht q hq).1) q.2 (hKdom (ht q hq).2)).subset ?_
  rintro γ ⟨hγ, x, hx, y, hy, b, hb, hxy⟩
  obtain ⟨q, hq, hxq⟩ := Set.mem_iUnion₂.mp (hcover (Set.mk_mem_prod hx hy))
  exact Set.mem_iUnion₂.mpr ⟨q, hq, hγ, x, hxq.1, y, hxq.2, b, hb, hxy⟩

end GlobalTheory.PropDiscCompare
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryMulUpperTriangular
namespace GlobalTheory.UnitaryUpperTriangular

open Module InnerProductSpace

theorem exists_unitary_mul_upperTriangular {n : ℕ} (y : Matrix (Fin n) (Fin n) ℂ) :
    ∃ u ∈ Matrix.unitaryGroup (Fin n) ℂ, ∃ (t : Matrix (Fin n) (Fin n) ℂ),
      Matrix.BlockTriangular t id ∧ y = u * t := by
  classical
  let f : Fin n → EuclideanSpace ℂ (Fin n) := fun i => WithLp.toLp 2 (fun k => y k i)
  have h : finrank ℂ (EuclideanSpace ℂ (Fin n)) = Fintype.card (Fin n) := finrank_euclideanSpace
  let a := EuclideanSpace.basisFun (Fin n) ℂ
  let b := gramSchmidtOrthonormalBasis h f
  refine ⟨a.toBasis.toMatrix b, a.toMatrix_orthonormalBasis_mem_unitary b,
    b.toBasis.toMatrix f, gramSchmidtOrthonormalBasis_inv_isUpperTriangular h f, ?_⟩
  rw [← b.coe_toBasis, Basis.toMatrix_mul_toMatrix]
  ext k i
  simp [Basis.toMatrix_apply, a, f]

end GlobalTheory.UnitaryUpperTriangular
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameActionUpperTriangularBlockExists
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.BlockTransporter

theorem exists_unitary_mul_upper {n : ℕ} (y : Matrix (Fin n) (Fin n) ℂ) :
    ∃ u ∈ Matrix.unitaryGroup (Fin n) ℂ, ∃ t : Matrix (Fin n) (Fin n) ℂ, t.BlockTriangular id ∧ y = u * t := by
  first
  | exact @_root_.GlobalTheory.UnitaryUpperTriangular.exists_unitary_mul_upperTriangular
  | exact _root_.GlobalTheory.UnitaryUpperTriangular.exists_unitary_mul_upperTriangular
  | (apply _root_.GlobalTheory.UnitaryUpperTriangular.exists_unitary_mul_upperTriangular <;> assumption)
  | (intros; apply _root_.GlobalTheory.UnitaryUpperTriangular.exists_unitary_mul_upperTriangular <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UnitaryUpperTriangular.exists_unitary_mul_upperTriangular <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UnitaryUpperTriangular.exists_unitary_mul_upperTriangular ..)

theorem exists_unitary_block {r p : ℕ} (B : Matrix (Fin r) (Fin r) ℂ) (hB : B.det ≠ 0)
    (h0 : ∀ a c : Fin r, (c : ℕ) < p → ¬ (a : ℕ) < p → B a c = 0) :
    ∃ u t : Matrix (Fin r) (Fin r) ℂ, u ∈ Matrix.unitaryGroup (Fin r) ℂ ∧
      (∀ a c : Fin r, (c : ℕ) < p → ¬ (a : ℕ) < p → u a c = 0) ∧
      t.det ≠ 0 ∧ (∀ a c : Fin r, c < a → t a c = 0) ∧ B = u * t := by
  obtain ⟨u, hu, t, ht, e⟩ := exists_unitary_mul_upper B
  have hud : u.det ≠ 0 := by
    intro h
    have := congrArg Matrix.det (Matrix.mem_unitaryGroup_iff'.1 hu)
    rw [det_mul, h, mul_zero, det_one] at this
    exact zero_ne_one this
  have htd : t.det ≠ 0 := by
    intro h; rw [e, det_mul, h, mul_zero] at hB; exact hB rfl
  letI := invertibleOfIsUnitDet t htd.isUnit
  have hti : (t⁻¹).BlockTriangular id := blockTriangular_inv_of_blockTriangular ht
  have hu' : u = B * t⁻¹ := by rw [e, Matrix.mul_nonsing_inv_cancel_right _ _ htd.isUnit]
  refine ⟨u, t, hu, fun a c hc ha => ?_, htd, fun a c h => ht h, e⟩
  rw [hu', Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : k ≤ c
  · rw [h0 a k (lt_of_le_of_lt (Fin.le_def.1 hk) hc) ha, zero_mul]
  · rw [hti (not_le.1 hk), mul_zero]

end GlobalTheory.BlockTransporter

namespace GlobalTheory.BlockTransporter

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def unitBlock (X : Data E r) : Set (Frame X.Ψ r) :=
  {u | ∀ τ, mat u τ ∈ Matrix.unitaryGroup (Fin r) ℂ ∧
    ∀ a c : Fin r, (c : ℕ) < X.p0 → ¬ (a : ℕ) < X.p0 → u τ a c = 0}

theorem isCompact_unitBlock (X : Data E r) : IsCompact (unitBlock X) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · have : unitBlock X = ⋂ τ, ({u : Frame X.Ψ r | star (mat u τ) * mat u τ = 1} ∩
        ⋂ a : Fin r, ⋂ c : Fin r, {u | (c : ℕ) < X.p0 → ¬ (a : ℕ) < X.p0 → u τ a c = 0}) := by
      ext u
      simp only [unitBlock, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff]
      simp only [Matrix.mem_unitaryGroup_iff']
    rw [this]
    refine isClosed_iInter fun τ => IsClosed.inter ?_ (isClosed_iInter fun a => isClosed_iInter fun c => ?_)
    · have hc : Continuous fun u : Frame X.Ψ r => mat u τ := continuous_apply τ
      exact isClosed_eq (hc.star.matrix_mul hc) continuous_const
    · by_cases h : (c : ℕ) < X.p0 ∧ ¬ (a : ℕ) < X.p0
      · have : {u : Frame X.Ψ r | (c : ℕ) < X.p0 → ¬ (a : ℕ) < X.p0 → u τ a c = 0} = {u | u τ a c = 0} := by
          ext u; simp only [Set.mem_setOf_eq]; exact ⟨fun hu => hu h.1 h.2, fun hu _ _ => hu⟩
        rw [this]
        exact isClosed_eq ((continuous_apply c).comp ((continuous_apply a).comp (continuous_apply τ)))
          continuous_const
      · have : {u : Frame X.Ψ r | (c : ℕ) < X.p0 → ¬ (a : ℕ) < X.p0 → u τ a c = 0} = Set.univ := by
          ext u; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]; intro h1 h2; exact absurd ⟨h1, h2⟩ h
        rw [this]; exact isClosed_univ
  · refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨1, fun u hu => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    refine pi_norm_le_iff_of_nonneg zero_le_one |>.2 fun τ => ?_
    refine pi_norm_le_iff_of_nonneg zero_le_one |>.2 fun a => ?_
    refine pi_norm_le_iff_of_nonneg zero_le_one |>.2 fun c => ?_
    exact entry_norm_bound_of_unitary (hu τ).1 a c

theorem continuous_rmul (X : Data E r) : Continuous fun p : Frame X.Ψ r × Frame X.Ψ r => rmul p.1 p.2 := by
  refine continuous_pi fun τ => ?_
  have h1 : Continuous fun p : Frame X.Ψ r × Frame X.Ψ r => mat p.1 τ := (continuous_apply τ).comp continuous_fst
  have h2 : Continuous fun p : Frame X.Ψ r × Frame X.Ψ r => mat p.2 τ := (continuous_apply τ).comp continuous_snd
  exact h1.matrix_mul h2

end GlobalTheory.BlockTransporter

namespace GlobalTheory.BlockTransporter

theorem finite_blockTransporter : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (K : Set (ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r)), IsCompact K → K ⊆ X.dom →
    {γ : GL (Fin r) E | γ ∈ X.Γ ∧ ∃ x ∈ K, ∃ y ∈ K, ∃ b : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r,
      (∀ τ, (ReciprocityTheory.ChartRestriction.G.FD.mat b τ).det ≠ 0) ∧
      (∀ τ (a c : Fin r), (c : ℕ) < X.p0 → ¬ (a : ℕ) < X.p0 → b τ a c = 0) ∧
      ReciprocityTheory.ChartRestriction.G.FD.lact γ x = ReciprocityTheory.ChartRestriction.G.FD.rmul y b}.Finite := by
  intro E _ _ _ r X K hK hKd
  set K' := (fun p : Frame X.Ψ r × Frame X.Ψ r => rmul p.1 p.2) '' (K ×ˢ unitBlock X) with hK'
  have hK'c : IsCompact K' := (hK.prod (isCompact_unitBlock X)).image (continuous_rmul X)
  have hK'd : K' ⊆ X.dom := by
    rintro _ ⟨⟨y, u⟩, ⟨hy, hu⟩, rfl⟩
    refine GlobalTheory.PointOfFrames.rmul_mem_dom X (hKd hy) u (fun τ h => ?_) (fun τ => (hu τ).2)
    have := congrArg Matrix.det (Matrix.mem_unitaryGroup_iff'.1 (hu τ).1)
    rw [det_mul, h, mul_zero, det_one] at this
    exact zero_ne_one this
  have hfin := GlobalTheory.PropDiscCompare.compact_of_local X (GlobalTheory.propDisc_of_flagDomainData E r X) (K ∪ K')
    (hK.union hK'c) (Set.union_subset hKd hK'd)
  refine hfin.subset ?_
  rintro γ ⟨hγ, x, hx, y, hy, b, hb, h0, e⟩
  have key : ∀ τ : X.Ψ, ∃ u t : Matrix (Fin r) (Fin r) ℂ, u ∈ Matrix.unitaryGroup (Fin r) ℂ ∧
      (∀ a c : Fin r, (c : ℕ) < X.p0 → ¬ (a : ℕ) < X.p0 → u a c = 0) ∧
      t.det ≠ 0 ∧ (∀ a c : Fin r, c < a → t a c = 0) ∧ mat b τ = u * t :=
    fun τ => exists_unitary_block (mat b τ) (hb τ) (h0 τ)
  choose u t hu hu0 htd ht hbut using key
  refine ⟨hγ, x, Or.inl hx, rmul y (fun τ => u τ), Or.inr ⟨(y, fun τ => u τ), ⟨hy, fun τ => ⟨hu τ, hu0 τ⟩⟩, rfl⟩,
    fun τ => t τ, fun τ => ⟨htd τ, ht τ⟩, ?_⟩
  rw [e]
  funext τ
  show mat y τ * mat b τ = (mat y τ * u τ) * t τ
  rw [Matrix.mul_assoc, ← hbut τ]

end GlobalTheory.BlockTransporter
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameActionUpperTriangularBlockExistsStatement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_setOf_lact_eq_rmul_blockTriangular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (K : Set (ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r)), IsCompact K → K ⊆ X.dom → {γ : GL (Fin r) E | γ ∈ X.Γ ∧ ∃ x ∈ K, ∃ y ∈ K, ∃ b : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r, (∀ τ, (ReciprocityTheory.ChartRestriction.G.FD.mat b τ).det ≠ 0) ∧ (∀ τ (a c : Fin r), (c : ℕ) < X.p0 → ¬ (a : ℕ) < X.p0 → b τ a c = 0) ∧ ReciprocityTheory.ChartRestriction.G.FD.lact γ x = ReciprocityTheory.ChartRestriction.G.FD.rmul y b}.Finite := by
  first | exact @GlobalTheory.BlockTransporter.finite_blockTransporter | exact GlobalTheory.BlockTransporter.finite_blockTransporter | (intros; apply GlobalTheory.BlockTransporter.finite_blockTransporter <;> assumption)
end
end
