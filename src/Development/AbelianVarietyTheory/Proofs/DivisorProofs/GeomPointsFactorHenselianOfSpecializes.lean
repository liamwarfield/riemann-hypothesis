module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetFactorDepthInChartChartIndependent

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeomPointsFactorHenselianOfSpecializes
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineRingHomPairOfSpecializes
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem asIdeal_spMap_field {B k : Type} [CommRing B] [Field k] (φ : B →+* k) (u : Sp k) :
    ((spMap φ).base u).asIdeal = RingHom.ker φ := by
  have hu : u.asIdeal = ⊥ := @Ideal.eq_bot_of_prime _ _ _ u.isPrime
  rw [RingHom.ker_eq_comap_bot, ← hu]
  rw [spMap, Spec.map_base]
  rfl

theorem exists_ringHom_pair_of_specializes {X : Scheme.{0}} {k k' : Type} [Field k] [Field k'] (x : Sp k ⟶ X)
    (x' : Sp k' ⟶ X) (u : Sp k) (u' : Sp k') (h : x'.base u' ⤳ x.base u) :
    ∃ (B : Type) (_ : CommRing B) (g : B →+* k) (g' : B →+* k') (ρ : Sp B ⟶ X),
      RingHom.ker g' ≤ RingHom.ker g ∧ spMap g ≫ ρ = x ∧ spMap g' ≫ ρ = x' := by
  obtain ⟨V, hV, hxV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
    (show x.base u ∈ (⊤ : X.Opens) from trivial)
  have hV' : IsAffineOpen V := hV
  have hx'V : x'.base u' ∈ V := h.mem_open V.isOpen hxV
  have hsub : Set.range x.base ⊆ Set.range hV'.fromSpec := by
    rw [hV'.range_fromSpec]
    rintro _ ⟨v, rfl⟩
    rwa [Subsingleton.elim v u]
  have hsub' : Set.range x'.base ⊆ Set.range hV'.fromSpec := by
    rw [hV'.range_fromSpec]
    rintro _ ⟨v, rfl⟩
    rwa [Subsingleton.elim v u']
  let xV := IsOpenImmersion.lift hV'.fromSpec x hsub
  let x'V := IsOpenImmersion.lift hV'.fromSpec x' hsub'
  have hfx : xV ≫ hV'.fromSpec = x := IsOpenImmersion.lift_fac _ _ _
  have hfx' : x'V ≫ hV'.fromSpec = x' := IsOpenImmersion.lift_fac _ _ _
  have e1 : spMap (Spec.preimage xV).hom = xV := Spec.map_preimage xV
  have e2 : spMap (Spec.preimage x'V).hom = x'V := Spec.map_preimage x'V
  refine ⟨Γ(X, V), inferInstance, (Spec.preimage xV).hom, (Spec.preimage x'V).hom, hV'.fromSpec, ?_, ?_, ?_⟩
  · rw [← asIdeal_spMap_field _ u, ← asIdeal_spMap_field _ u']
    refine (PrimeSpectrum.le_iff_specializes ((spMap (Spec.preimage x'V).hom).base u')
      ((spMap (Spec.preimage xV).hom).base u)).mpr ?_
    rw [e1, e2]
    have h2 : hV'.fromSpec (x'V u') ⤳ hV'.fromSpec (xV u) := by
      rw [← hfx, ← hfx'] at h
      simpa only [Scheme.Hom.comp_apply] using h
    exact (hV'.fromSpec.isOpenEmbedding.isInducing.specializes_iff).mp h2
  · rw [e1]; exact hfx
  · rw [e2]; exact hfx'

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomExtendOfIsIntegralIsAlgClosed
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomExtendOfIsIntegralIsAlgClosed
open Polynomial

namespace GlobalTheory

theorem ringHom_extend_of_isIntegral_isAlgClosed (A C K : Type) [CommRing A] [CommRing C]
    [Algebra A C] [Algebra.IsIntegral A C] [Field K] [IsAlgClosed K] (h : A →+* K)
    (hk : RingHom.ker (algebraMap A C) ≤ RingHom.ker h) :
    ∃ ψ : C →+* K, ψ.comp (algebraMap A C) = h := by
  classical
  haveI hp : (RingHom.ker h).IsPrime := RingHom.ker_isPrime h
  obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (RingHom.ker h) (⊥ : Ideal C)
    (by simpa [← RingHom.ker_eq_comap_bot] using hk)
  haveI : Q.LiesOver (RingHom.ker h) := (Ideal.liesOver_iff _ _).mpr hQc.symm
  letI : Algebra (A ⧸ RingHom.ker h) K := (RingHom.kerLift h).toAlgebra
  haveI : FaithfulSMul (A ⧸ RingHom.ker h) K :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (RingHom.kerLift_injective h)
  haveI : FaithfulSMul (A ⧸ RingHom.ker h) (C ⧸ Q) := inferInstance
  haveI : Nontrivial (A ⧸ RingHom.ker h) := Ideal.Quotient.nontrivial_iff.mpr hp.ne_top
  haveI : Algebra.IsIntegral (A ⧸ RingHom.ker h) (C ⧸ Q) :=
    Ideal.Quotient.algebra_isIntegral_of_liesOver (A := A) (p := RingHom.ker h) (P := Q)
  haveI : Algebra.IsAlgebraic (A ⧸ RingHom.ker h) (C ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  haveI : Module.IsTorsionFree (A ⧸ RingHom.ker h) (C ⧸ Q) :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (FaithfulSMul.algebraMap_injective _ _)
  haveI : Module.IsTorsionFree (A ⧸ RingHom.ker h) K :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (RingHom.kerLift_injective h)
  let φ : (C ⧸ Q) →ₐ[A ⧸ RingHom.ker h] K := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨φ.toRingHom.comp (Ideal.Quotient.mk Q), ?_⟩
  ext a
  have e1 : (Ideal.Quotient.mk Q) (algebraMap A C a) =
      algebraMap (A ⧸ RingHom.ker h) (C ⧸ Q) (Ideal.Quotient.mk _ a) := rfl
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [e1, φ.commutes]
  rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomExtendOfIsIntegralIsAlgClosedStatement
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringHom_extend_of_isIntegral_of_isAlgClosed : ∀ (A C K : Type) [CommRing A] [CommRing C] [Algebra A C] [Algebra.IsIntegral A C] [Field K] [IsAlgClosed K] (h : A →+* K), RingHom.ker (algebraMap A C) ≤ RingHom.ker h → ∃ ψ : C →+* K, ψ.comp (algebraMap A C) = h := by
  first | exact @GlobalTheory.ringHom_extend_of_isIntegral_isAlgClosed | exact GlobalTheory.ringHom_extend_of_isIntegral_isAlgClosed | (intros; apply GlobalTheory.ringHom_extend_of_isIntegral_isAlgClosed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralDomainExtensionWithMonicRoots
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralDomainExtensionWithMonicRoots
open Polynomial

namespace GlobalTheory

theorem exists_integral_domain_extension_monic_roots :
    ∀ (D : Type) [CommRing D] [IsDomain D], ∃ (C : Type) (_ : CommRing C) (_ : Algebra D C),
      IsDomain C ∧ Algebra.IsIntegral D C ∧ Function.Injective (algebraMap D C) ∧
      (∀ f : C[X], f.Monic → 0 < f.natDegree → ∃ y : C, f.eval y = 0) ∧
      ∀ (K : Type) [Field K] [IsAlgClosed K] (h : D →+* K), Function.Injective h →
        ∃ e : C →+* K, Function.Injective e ∧ e.comp (algebraMap D C) = h := by
  intro D _ _
  have hDL : Function.Injective (algebraMap D (AlgebraicClosure (FractionRing D))) := by
    rw [IsScalarTower.algebraMap_eq D (FractionRing D) (AlgebraicClosure (FractionRing D))]
    exact (algebraMap (FractionRing D) (AlgebraicClosure (FractionRing D))).injective.comp
      (IsFractionRing.injective D (FractionRing D))
  have hCL : Function.Injective (algebraMap (integralClosure D (AlgebraicClosure (FractionRing D)))
      (AlgebraicClosure (FractionRing D))) := Subtype.val_injective
  refine ⟨integralClosure D (AlgebraicClosure (FractionRing D)), inferInstance, inferInstance,
    inferInstance, inferInstance, ?_, ?_, ?_⟩
  · intro a b hab
    apply hDL
    simpa using congrArg Subtype.val hab
  · intro f hf hdeg
    have hdeg' : (f.map (algebraMap (integralClosure D (AlgebraicClosure (FractionRing D)))
        (AlgebraicClosure (FractionRing D)))).degree ≠ 0 := by
      rw [degree_map_eq_of_injective hCL, degree_eq_natDegree hf.ne_zero]
      exact_mod_cast hdeg.ne'
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_root _ hdeg'
    have hy' : f.eval₂ (algebraMap (integralClosure D (AlgebraicClosure (FractionRing D)))
        (AlgebraicClosure (FractionRing D))) y = 0 := by rwa [IsRoot, eval_map] at hy
    have hyC : IsIntegral (integralClosure D (AlgebraicClosure (FractionRing D))) y :=
      ⟨f, hf, hy'⟩
    have hyD : IsIntegral D y := isIntegral_trans y hyC
    refine ⟨⟨y, hyD⟩, ?_⟩
    apply hCL
    rw [← eval₂_at_apply, map_zero]
    exact hy'
  · intro K _ _ h hinj
    letI : Algebra (FractionRing D) K := (IsFractionRing.lift hinj : FractionRing D →+* K).toAlgebra
    let φ : AlgebraicClosure (FractionRing D) →ₐ[FractionRing D] K := (by
      refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
      solve_by_elim* (maxDepth := 2) only [*,
        @_root_.DivisionSemiring.to_moduleIsTorsionFree,
        @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
    refine ⟨φ.toRingHom.comp (integralClosure D (AlgebraicClosure (FractionRing D))).val.toRingHom,
      φ.toRingHom.injective.comp Subtype.val_injective, ?_⟩
    ext a
    show φ (algebraMap D (AlgebraicClosure (FractionRing D)) a) = h a
    rw [IsScalarTower.algebraMap_apply D (FractionRing D) (AlgebraicClosure (FractionRing D)),
      AlgHom.commutes]
    exact IsFractionRing.lift_algebraMap hinj a

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralDomainExtensionWithMonicRootsStatement
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_domain_extension_with_monic_roots : ∀ (D : Type) [CommRing D] [IsDomain D], ∃ (C : Type) (_ : CommRing C) (_ : Algebra D C), IsDomain C ∧ Algebra.IsIntegral D C ∧ Function.Injective (algebraMap D C) ∧ (∀ f : C[X], f.Monic → 0 < f.natDegree → ∃ y : C, f.eval y = 0) ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (h : D →+* K), Function.Injective h → ∃ e : C →+* K, Function.Injective e ∧ e.comp (algebraMap D C) = h := by
  first | exact @GlobalTheory.exists_integral_domain_extension_monic_roots | exact GlobalTheory.exists_integral_domain_extension_monic_roots | (intros; apply GlobalTheory.exists_integral_domain_extension_monic_roots <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

open Polynomial

theorem geomPoints_factor_henselian_of_specializes :
  ∀ {X : Scheme.{0}} {k k' : Type} [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k'] (x : Sp k ⟶ X) (x' : Sp k' ⟶ X) (u : Sp k) (u' : Sp k'), x'.base u' ⤳ x.base u → ∃ (R : Type) (_ : CommRing R) (_ : HenselianLocalRing R) (_ : IsAlgClosed (IsLocalRing.ResidueField R)) (r : Sp R ⟶ X) (i : Sp k ⟶ Sp R) (i' : Sp k' ⟶ Sp R), i ≫ r = x ∧ i' ≫ r = x' := by
  intro X k k' _ _ _ _ x x' u u' hsp
  have hAffine := exists_ringHom_pair_of_specializes x x' u u' hsp
  obtain ⟨B, _, g, g', ρ, hker, hx, hx'⟩ := hAffine
  set q := RingHom.ker g' with hq
  haveI : q.IsPrime := RingHom.ker_isPrime g'
  let D := B ⧸ q
  let h' : D →+* k' := RingHom.kerLift g'
  have h'inj : Function.Injective h' := RingHom.kerLift_injective g'
  let h : D →+* k := Ideal.Quotient.lift q g (fun b hb => hker hb)
  obtain ⟨C, _, _, hCdom, hCint, hCinj, hCroot, hCext⟩ := GlobalTheory.T.exists_integral_domain_extension_with_monic_roots D
  obtain ⟨e', he'inj, he'⟩ := hCext k' h' h'inj
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_ringHom_extend_of_isIntegral_of_isAlgClosed D C k h (by
    intro a ha; rw [RingHom.mem_ker] at ha ⊢
    rw [show a = 0 from hCinj (by rw [ha, map_zero])]; exact map_zero h)
  let P := RingHom.ker ψ
  haveI : P.IsPrime := RingHom.ker_isPrime ψ
  let R := Localization.AtPrime P
  have h0 : (0 : C) ∉ P.primeCompl := fun h0 => h0 P.zero_mem
  have hRloc := (absIntClosed_localization_and_quotient C ⟨hCdom, hCroot⟩).1 P.primeCompl h0
  obtain ⟨hH, hAC, -⟩ := AbsIntClosedLocal.henselian_isAlgClosed_pow_surj R hRloc
  let φ : B →+* R := (algebraMap C R).comp ((algebraMap D C).comp (Ideal.Quotient.mk q))
  let f : R →+* k := IsLocalization.lift (M := P.primeCompl) (g := ψ) (fun s => by
    refine IsUnit.mk0 _ ?_
    exact s.2)
  let f' : R →+* k' := IsLocalization.lift (M := P.primeCompl) (g := e') (fun s => by
    refine IsUnit.mk0 _ ?_
    intro hs
    exact s.2 (by rw [show (s : C) = 0 from he'inj (by rw [hs, map_zero])]; exact P.zero_mem))
  have hf : f.comp φ = g := by
    ext b
    simp only [f, φ, RingHom.comp_apply, IsLocalization.lift_eq]
    rw [← RingHom.comp_apply ψ, hψ]
    rfl
  have hf' : f'.comp φ = g' := by
    ext b
    simp only [f', φ, RingHom.comp_apply, IsLocalization.lift_eq]
    rw [← RingHom.comp_apply e', he']
    rfl
  refine ⟨R, inferInstance, hH, hAC, spMap φ ≫ ρ, spMap f, spMap f', ?_, ?_⟩
  · rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hf, hx]
  · rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hf', hx']

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogNcardSeminormBallExpSmallLe
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardSeminormBallPowLeRadiusChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardSeminormBallPowLeRadiusChange
open Filter Topology GlobalTheory.VolBr

namespace GlobalTheory.VolBr

set_option autoImplicit false in
open Filter Topology in
private lemma isBallFam_mono {G : Type} [AddCommGroup G] {Λ : AddSubgroup G} {B : ℝ → Set G}
    (hB : _root_.GlobalTheory.VolBr.IsBallFam Λ B) {r r' : ℝ} (hrr' : r ≤ r') : B r ⊆ B r' := by
  intro x hx
  have := hB.sub_mem r (r' - r) x 0 hx (hB.zero_mem _ (sub_nonneg.2 hrr'))
  simpa using this

set_option autoImplicit false in
open Filter Topology in
private lemma encard_mul_encard_le_isBallFam {G : Type} [AddCommGroup G] {Λ : AddSubgroup G}
    {B : ℝ → Set G} (hB : _root_.GlobalTheory.VolBr.IsBallFam Λ B) {a b : ℝ} {m : ℕ} (hm : 0 < m)
    (hbm : b + b ≤ m) (hfa : (B a).Finite) (hfb : (B b).Finite) (hf1 : (B 1).Finite) :
    (B a).encard * (B b).encard ≤ (B 1).encard * (B (m * a + b)).encard := by
  classical
  set S := hfa.toFinset ×ˢ hfb.toFinset with hS
  let f : G × G → G := fun p ↦ m • p.1 + p.2
  have hmem : ∀ p ∈ S, f p ∈ B (m * a + b) := by
    intro p hp
    rw [hS, Finset.mem_product, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset] at hp
    have h1 : m • p.1 ∈ B (m * a) :=
      (hB.nsmul_iff m a p.1 hm (hB.subset a hp.1)).2 hp.1
    have h2 : -p.2 ∈ B (0 + b) := by
      simpa using hB.sub_mem 0 b 0 p.2 (hB.zero_mem 0 le_rfl) hp.2
    have := hB.sub_mem _ _ _ _ h1 h2
    simpa [f, sub_neg_eq_add] using this
  have hcard : S.card ≤ hf1.toFinset.card * (S.image f).card := by
    refine Finset.card_le_mul_card_image S _ fun w hw ↦ ?_
    obtain ⟨p₀, hp₀, rfl⟩ := Finset.mem_image.1 hw
    refine Finset.card_le_card_of_injOn (fun p ↦ p₀.1 - p.1) ?_ ?_
    · intro p hp
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_filter] at hp
      obtain ⟨hpS, hfp⟩ := hp
      have hp₀' := hp₀
      rw [hS, Finset.mem_product, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset] at hpS hp₀'
      rw [Finset.mem_coe, Set.Finite.mem_toFinset]
      have hd : m • (p₀.1 - p.1) = p.2 - p₀.2 := by
        simp only [f] at hfp
        rw [smul_sub, sub_eq_sub_iff_add_eq_add, ← hfp]
        abel
      have hΛ : p₀.1 - p.1 ∈ Λ := Λ.sub_mem (hB.subset a hp₀'.1) (hB.subset a hpS.1)
      have h2 : p.2 - p₀.2 ∈ B ((m : ℝ) * 1) :=
        isBallFam_mono hB (by simpa using hbm) (hB.sub_mem _ _ _ _ hpS.2 hp₀'.2)
      exact (hB.nsmul_iff m 1 _ hm hΛ).1 (hd ▸ h2)
    · intro p hp q hq hpq
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hp hq
      have h1 : p.1 = q.1 := by simpa using hpq
      have h2 : p.2 = q.2 := by
        have := hp.2.trans hq.2.symm
        simp only [f, h1] at this
        exact add_left_cancel this
      exact Prod.ext h1 h2
  have himg : ((S.image f).card : ℕ∞) ≤ (B (m * a + b)).encard := by
    rw [← Set.encard_coe_eq_coe_finsetCard]
    refine Set.encard_le_encard fun w hw ↦ ?_
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hw
    exact hmem p hp
  rw [hfa.encard_eq_coe_toFinset_card, hfb.encard_eq_coe_toFinset_card,
    hf1.encard_eq_coe_toFinset_card, ← Nat.cast_mul, ← Finset.card_product]
  calc ((S.card : ℕ) : ℕ∞) ≤ ((hf1.toFinset.card * (S.image f).card : ℕ) : ℕ∞) := by
        exact_mod_cast hcard
    _ ≤ (hf1.toFinset.card : ℕ∞) * (B (m * a + b)).encard := by
        push_cast
        gcongr


open Filter Topology in
theorem _root_.GlobalTheory.VolBr.encard_ball_pow_le : ∀ (G : Type) [AddCommGroup G]
    (Λ : AddSubgroup G) (B : ℝ → Set G), _root_.GlobalTheory.VolBr.IsBallFam Λ B → ∀ (R : ℝ) (Q e : ℕ),
    1 ≤ R → 2 * R + 1 ≤ Q → (B R).Finite →
    (B R).encard ^ e ≤ (B 1).encard ^ e * (B (R * Q ^ e)).encard := by
  intro G _ Λ B hB R Q e hR hQ hfin
  have h1 : (B 1).Finite := hfin.subset (isBallFam_mono hB hR)
  have hQ2 : (2 : ℝ) ≤ Q := by linarith
  have hB1 : (B 1).encard ≠ 0 := by
    rw [Ne, Set.encard_eq_zero]
    exact Set.nonempty_iff_ne_empty.1 ⟨0, hB.zero_mem 1 zero_le_one⟩
  by_cases hbig : (B (R * Q ^ e)).Finite
  swap
  · rw [Set.Infinite.encard_eq hbig, ENat.mul_top (pow_ne_zero _ hB1)]
    exact le_top
  set s : ℕ → ℝ := fun j ↦ ∑ i ∈ Finset.range j, (Q : ℝ) ^ i with hs
  have hs_succ : ∀ j, s (j + 1) = Q * s j + 1 := by
    intro j
    simp only [hs, Finset.sum_range_succ', pow_succ, pow_zero, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    ring
  have hs_nonneg : ∀ j, 0 ≤ s j := fun j ↦ Finset.sum_nonneg fun i _ ↦ by positivity
  have hs_le : ∀ j, s j + 1 ≤ (Q : ℝ) ^ j := by
    intro j
    induction j with
    | zero => simp [hs]
    | succ j ih =>
      rw [hs_succ, pow_succ]
      nlinarith [hs_nonneg j]
  have hclaim : ∀ j ≤ e, (B R).encard ^ j ≤ (B 1).encard ^ j * (B (R * s j)).encard := by
    intro j
    induction j with
    | zero =>
      intro _
      simp only [pow_zero, one_mul, hs, Finset.range_zero, Finset.sum_empty, mul_zero]
      exact Set.one_le_encard_iff_nonempty.2 ⟨0, hB.zero_mem 0 le_rfl⟩
    | succ j ih =>
      intro hj
      have hRs : R * s j ≤ R * Q ^ e := by
        refine mul_le_mul_of_nonneg_left ?_ (by linarith)
        calc s j ≤ (Q : ℝ) ^ j := by linarith [hs_le j]
          _ ≤ (Q : ℝ) ^ e := pow_le_pow_right₀ (by linarith) (by omega)
      have hfs : (B (R * s j)).Finite := hbig.subset (isBallFam_mono hB hRs)
      have hQpos : 0 < Q := by exact_mod_cast (show (0 : ℝ) < Q by linarith)
      have step := encard_mul_encard_le_isBallFam hB (a := R * s j) (b := R) hQpos (by linarith)
        hfs hfin h1
      have hrad : (Q : ℝ) * (R * s j) + R = R * s (j + 1) := by rw [hs_succ]; ring
      rw [hrad] at step
      calc (B R).encard ^ (j + 1) = (B R).encard ^ j * (B R).encard := pow_succ _ _
        _ ≤ (B 1).encard ^ j * (B (R * s j)).encard * (B R).encard := by
            gcongr; exact ih (by omega)
        _ = (B 1).encard ^ j * ((B (R * s j)).encard * (B R).encard) := mul_assoc _ _ _
        _ ≤ (B 1).encard ^ j * ((B 1).encard * (B (R * s (j + 1))).encard) := by gcongr
        _ = (B 1).encard ^ (j + 1) * (B (R * s (j + 1))).encard := by rw [pow_succ, mul_assoc]
  calc (B R).encard ^ e ≤ (B 1).encard ^ e * (B (R * s e)).encard := hclaim e le_rfl
    _ ≤ (B 1).encard ^ e * (B (R * Q ^ e)).encard := by
        gcongr
        exact isBallFam_mono hB (mul_le_mul_of_nonneg_left (by linarith [hs_le e]) (by linarith))

end GlobalTheory.VolBr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardSeminormBallPowLeRadiusChangeStatement
open Filter Topology GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.encard_seminormBall_pow_le_radius_change : ∀ (G : Type) [AddCommGroup G] (Λ : AddSubgroup G) (B : ℝ → Set G), IsBallFam Λ B → ∀ (R : ℝ) (Q e : ℕ), 1 ≤ R → 2 * R + 1 ≤ Q → (B R).Finite → (B R).encard ^ e ≤ (B 1).encard ^ e * (B (R * Q ^ e)).encard := by
  first | exact @GlobalTheory.VolBr.encard_ball_pow_le | exact GlobalTheory.VolBr.encard_ball_pow_le | (intros; apply GlobalTheory.VolBr.encard_ball_pow_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogNcardSeminormBallExpSmallLe
set_option autoImplicit false

open Filter Topology GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem log_ncard_ball_exp_le : ∀ (G : Type) [AddCommGroup G] (Λ : ℕ → AddSubgroup G) (B : ℕ → ℝ → Set G) (d : ℕ),
    0 < d → (∀ m, IsBallFam (Λ m) (B m)) → (∀ m R, (B m R).Finite) → ∀ C : ℝ,
    (∀ᶠ m : ℕ in atTop, Real.log ((B m (Real.exp (3 * m))).ncard : ℝ) ≤ C * (m : ℝ) ^ d) →
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ m : ℕ in atTop,
      Real.log ((B m (Real.exp (δ * m))).ncard : ℝ) ≤ Real.log ((B m 1).ncard : ℝ) + ε * (m : ℝ) ^ d := by
  intro G _ Λ B d _ hB hfin C hC ε hε
  set e : ℕ := max 1 ⌈C / ε⌉₊ with he_def
  have he1 : 1 ≤ e := le_max_left _ _
  have heR : (0 : ℝ) < e := by exact_mod_cast he1
  have he1R : (1 : ℝ) ≤ e := by exact_mod_cast he1
  have hCe : C ≤ ε * e := by
    have h1 : C / ε ≤ (⌈C / ε⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈C / ε⌉₊ : ℝ) ≤ e := by exact_mod_cast le_max_right _ _
    rw [div_le_iff₀ hε] at h1
    nlinarith
  refine ⟨1 / e, by positivity, ?_⟩
  filter_upwards [hC, eventually_ge_atTop (3 * e)] with m hm hm3
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  set R := Real.exp (1 / e * m) with hR
  have hR1 : 1 ≤ R := Real.one_le_exp (by positivity)
  set Q := ⌈2 * R + 1⌉₊ with hQdef
  have hQ : 2 * R + 1 ≤ Q := Nat.le_ceil _
  have hQ4 : (Q : ℝ) ≤ 4 * R := by
    have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 2 * R + 1 by linarith)
    linarith
  have key := GlobalTheory.T.encard_seminormBall_pow_le_radius_change G (Λ m) (B m) (hB m) R Q e hR1 hQ (hfin m R)
  have mono : ∀ r s : ℝ, r ≤ s → B m r ⊆ B m s := by
    intro r s hrs x hx
    have := (hB m).sub_mem r (s - r) x 0 hx ((hB m).zero_mem _ (by linarith))
    simpa using this
  have hRe : R ^ (e + 1) ≤ Real.exp (2 * m) := by
    rw [hR, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have : (m : ℝ) / e ≤ m := div_le_self hm0 he1R
    have h3 : ((e + 1 : ℕ) : ℝ) * (1 / e * m) = m + m / e := by
      push_cast; field_simp
    rw [h3]; linarith
  have hbig : R * (Q : ℝ) ^ e ≤ Real.exp (3 * m) := by
    have h4 : (4 : ℝ) ≤ Real.exp 3 := by
      have := Real.add_one_le_exp 3; linarith
    have hQ0 : (0 : ℝ) ≤ Q := Nat.cast_nonneg _
    calc R * (Q : ℝ) ^ e ≤ R * (4 * R) ^ e := by gcongr
      _ = 4 ^ e * R ^ (e + 1) := by ring
      _ ≤ Real.exp 3 ^ e * Real.exp (2 * m) := by gcongr
      _ = Real.exp (3 * e + 2 * m) := by rw [← Real.exp_nat_mul, ← Real.exp_add]; ring_nf
      _ ≤ Real.exp (3 * m) := by
        apply Real.exp_le_exp.mpr
        have : (3 * e : ℝ) ≤ m := by exact_mod_cast hm3
        linarith
  have hsub := mono _ _ hbig
  have hN : (B m R).ncard ^ e ≤ (B m 1).ncard ^ e * (B m (Real.exp (3 * m))).ncard := by
    rw [← (hfin m R).cast_ncard_eq, ← (hfin m 1).cast_ncard_eq, ← (hfin m _).cast_ncard_eq] at key
    norm_cast at key
    have hsub' : B m (R * ((Q ^ e : ℕ) : ℝ)) ⊆ B m (Real.exp (3 * m)) := by push_cast; exact hsub
    exact key.trans (Nat.mul_le_mul_left _ (Set.ncard_le_ncard hsub' (hfin m _)))
  have pos : ∀ r : ℝ, 0 ≤ r → (0 : ℝ) < (B m r).ncard := fun r hr => by
    exact_mod_cast (Set.ncard_pos (hfin m r)).mpr ⟨0, (hB m).zero_mem r hr⟩
  have hA := pos R (by linarith)
  have h1 := pos 1 zero_le_one
  have h3 := pos (Real.exp (3 * m)) (Real.exp_pos _).le
  have hNR : ((B m R).ncard : ℝ) ^ e ≤ ((B m 1).ncard : ℝ) ^ e * (B m (Real.exp (3 * m))).ncard := by
    exact_mod_cast hN
  have hlog := Real.log_le_log (by positivity) hNR
  rw [Real.log_mul (by positivity) h3.ne', Real.log_pow, Real.log_pow] at hlog
  have hCm : C * (m : ℝ) ^ d ≤ ε * e * (m : ℝ) ^ d := mul_le_mul_of_nonneg_right hCe (pow_nonneg hm0 d)
  have : (e : ℝ) * Real.log ((B m R).ncard : ℝ) ≤
      e * (Real.log ((B m 1).ncard : ℝ) + ε * (m : ℝ) ^ d) := by nlinarith
  exact le_of_mul_le_mul_left this heR

end GlobalTheory.VolBr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogNcardSeminormBallExpSmallLeStatement
open Filter Topology GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_log_ncard_seminormBall_exp_small_le : ∀ (G : Type) [AddCommGroup G] (Λ : ℕ → AddSubgroup G) (B : ℕ → ℝ → Set G) (d : ℕ), 0 < d → (∀ m, IsBallFam (Λ m) (B m)) → (∀ m R, (B m R).Finite) → ∀ C : ℝ, (∀ᶠ m : ℕ in atTop, Real.log ((B m (Real.exp (3 * m))).ncard : ℝ) ≤ C * (m : ℝ) ^ d) → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ m : ℕ in atTop, Real.log ((B m (Real.exp (δ * m))).ncard : ℝ) ≤ Real.log ((B m 1).ncard : ℝ) + ε * (m : ℝ) ^ d := by
  first | exact @GlobalTheory.VolBr.log_ncard_ball_exp_le | exact GlobalTheory.VolBr.log_ncard_ball_exp_le | (intros; apply GlobalTheory.VolBr.log_ncard_ball_exp_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusTwistDivisorRecursion
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

theorem GlobalTheory.nat_mul_div_bounds_rounded_multiples (p r m : ℕ) (hp : 0 < p) (hr : 0 < r) :
    p * (m / r) ≤ p * m / r ∧ p * m / r + 1 ≤ p * (m / r) + p := by
  have h1 : p * m = p * (m % r) + r * (p * (m / r)) := by
    conv_lhs => rw [← Nat.mod_add_div m r]
    ring
  have h2 : p * m / r = p * (m % r) / r + p * (m / r) := by
    rw [h1, Nat.add_mul_div_left _ _ hr]
  have h4 : p * (m % r) < p * r := Nat.mul_lt_mul_of_pos_left (Nat.mod_lt m hr) hp
  have h3 : p * (m % r) / r < p := (Nat.div_lt_iff_lt_mul hr).2 h4
  rw [h2]
  generalize p * (m % r) / r = q at h3 ⊢
  generalize p * (m / r) = s
  constructor <;> omega

theorem GlobalTheory.rounded_multiples_step : ∀ (X : Scheme.{0}) [IsIntegral X] (p : ℕ) {C : Type} [Fintype C] (E : C → CartierDiv X) (M Kc : CartierDiv X) (r : ℕ) (b : C → ℕ), 0 < p → 0 < r → ∀ e : ℕ, ∃ ρ : C → ℕ, (∀ c, ρ c < p) ∧ (fun e => p ^ e • (M - Kc) - ∑ c, (p ^ e * b c / r) • E c - ∑ c, E c) (e + 1) = p • (fun e => p ^ e • (M - Kc) - ∑ c, (p ^ e * b c / r) • E c - ∑ c, E c) e + ∑ c, ρ c • E c := by
  intro X _ p C _ E M Kc r b hp hr e
  have hm : ∀ c, p ^ (e + 1) * b c = p * (p ^ e * b c) := fun c => by ring
  refine ⟨fun c => p * (p ^ e * b c / r) + p - 1 - p ^ (e + 1) * b c / r, ?_, ?_⟩
  · intro c
    have := GlobalTheory.nat_mul_div_bounds_rounded_multiples p r (p ^ e * b c) hp hr
    show p * (p ^ e * b c / r) + p - 1 - p ^ (e + 1) * b c / r < p
    rw [hm c]
    omega
  · have hc : ∀ c, p • ((p ^ e * b c / r) • E c + E c)
        = (p ^ (e + 1) * b c / r) • E c + E c
          + (p * (p ^ e * b c / r) + p - 1 - p ^ (e + 1) * b c / r) • E c := by
      intro c
      have := GlobalTheory.nat_mul_div_bounds_rounded_multiples p r (p ^ e * b c) hp hr
      have hk : p * (p ^ e * b c / r) + p
          = p ^ (e + 1) * b c / r + 1 + (p * (p ^ e * b c / r) + p - 1 - p ^ (e + 1) * b c / r) := by
        rw [hm c]; omega
      rw [smul_add, ← mul_smul, ← add_smul]
      conv_lhs => rw [hk]
      rw [add_smul, add_smul, one_smul]
    have hs : p • (∑ c, (p ^ e * b c / r) • E c + ∑ c, E c)
        = ∑ c, (p ^ (e + 1) * b c / r) • E c + ∑ c, E c
          + ∑ c, (p * (p ^ e * b c / r) + p - 1 - p ^ (e + 1) * b c / r) • E c := by
      rw [← Finset.sum_add_distrib, Finset.smul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun c _ => hc c)
    have hs' : p • (p ^ e • (M - Kc) - ∑ c, (p ^ e * b c / r) • E c - ∑ c, E c)
        = p ^ (e + 1) • (M - Kc) - p • (∑ c, (p ^ e * b c / r) • E c + ∑ c, E c) := by
      rw [pow_succ', mul_smul, smul_sub, smul_sub, smul_add]; abel
    beta_reduce
    rw [hs', hs]
    abel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversallyClosedOpenContainingFibreContainsNear
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversallyClosedOpenContainingFibreContainsNear
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory

theorem spMap_base_mem_basicOpen {R T : Type} [CommRing R] [CommRing T] (χ : R →+* T) (a : R)
    (ha : IsUnit (χ a)) (t : Sp T) : (spMap χ).base t ∈ (PrimeSpectrum.basicOpen a : (Sp R).Opens) := by
  change a ∉ (PrimeSpectrum.comap χ t).asIdeal
  intro h
  exact t.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h ha)

theorem tube_of_universallyClosed : ∀ (R k : Type) [CommRing R] [Field k] (φ : R →+* k) (X X' : Scheme.{0})
    (f : X ⟶ Sp R) (f' : X' ⟶ Sp k) (π : X' ⟶ X) [UniversallyClosed f] (W : X.Opens),
    IsPullback π f' f (spMap φ) → π ⁻¹ᵁ W = ⊤ → ∃ a : R, φ a ≠ 0 ∧ ∀ (T : Type) [CommRing T] (χ : R →+* T),
    IsUnit (χ a) → ∀ (Z : Scheme.{0}) (g : Z ⟶ Sp T) (ρ : Z ⟶ X), IsPullback ρ g f (spMap χ) → ρ ⁻¹ᵁ W = ⊤ := by
  intro R k _ _ φ X X' f f' π _ W H hW
  have hc : IsClosed (f.base '' (W : Set X)ᶜ) := f.isClosedMap _ W.isOpen.isClosed_compl
  let t : Sp k := ⟨⊥, Ideal.isPrime_bot⟩
  have hx : (spMap φ).base t ∈ (f.base '' (W : Set X)ᶜ)ᶜ := by
    rintro ⟨x, hx, e⟩
    obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback H x t e
    exact hx (hW.ge (Set.mem_univ z))
  obtain ⟨_, ⟨a, rfl⟩, ha, hle⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hx hc.isOpen_compl
  refine ⟨a, ?_, ?_⟩
  · intro h0
    apply ha
    change φ a ∈ (⊥ : Ideal k)
    exact h0
  · intro T _ χ hχ Z g ρ H'
    refine top_le_iff.1 fun z _ => ?_
    by_contra hz
    have hm := spMap_base_mem_basicOpen χ a hχ (g.base z)
    have e : f.base (ρ.base z) = (spMap χ).base (g.base z) := by
      have := congrArg (fun h : Z ⟶ Sp R => h.base z) H'.w
      simpa using this
    exact hle (e ▸ hm : f.base (ρ.base z) ∈ _) ⟨ρ.base z, hz, rfl⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversallyClosedOpenContainingFibreContainsNearStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.universallyClosed_open_containing_fibre_contains_nearby : ∀ (R k : Type) [CommRing R] [Field k] (φ : R →+* k) (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp k) (π : X' ⟶ X) [UniversallyClosed f] (W : X.Opens), IsPullback π f' f (spMap φ) → π ⁻¹ᵁ W = ⊤ → ∃ a : R, φ a ≠ 0 ∧ ∀ (T : Type) [CommRing T] (χ : R →+* T), IsUnit (χ a) → ∀ (Z : Scheme.{0}) (g : Z ⟶ Sp T) (ρ : Z ⟶ X), IsPullback ρ g f (spMap χ) → ρ ⁻¹ᵁ W = ⊤ := by
  first | exact @GlobalTheory.tube_of_universallyClosed | exact GlobalTheory.tube_of_universallyClosed | (intros; apply GlobalTheory.tube_of_universallyClosed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralClopenCoverOfSmoothQuasiCompactFie
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralClopenCoverOfSmoothQuasiCompactFie
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory

theorem exists_integral_clopen_cover_of_smooth_field :
    ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Sp k) [Smooth f] [QuasiCompact f], ∃ (κ : Type) (U : κ → X.Opens), ⨆ c, U c = ⊤ ∧ (Pairwise fun a b => Disjoint (U a) (U b)) ∧ ∀ c, IsIntegral (U c).toScheme ∧ IsClosedImmersion (U c).ι := by
  intro k _ X f _ _
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hopen : ∀ c : _root_.ConnectedComponents X, IsOpen ((_root_.ConnectedComponents.mk : X → _) ⁻¹' {c}) := by
    intro c
    obtain ⟨x, rfl⟩ := _root_.ConnectedComponents.surjective_coe c
    rw [connectedComponents_preimage_singleton]
    exact GlobalTheory.isOpen_connectedComponent_of_isLocallyNoetherian X inferInstance x
  let U : _root_.ConnectedComponents X → X.Opens := fun c => ⟨_, hopen c⟩
  refine ⟨_root_.ConnectedComponents X, U, ?_, ?_, fun c => ?_⟩
  · rw [eq_top_iff]
    intro x _
    exact Opens.mem_iSup.2 ⟨_root_.ConnectedComponents.mk x, rfl⟩
  · intro a b hab
    rw [disjoint_iff, ← SetLike.coe_set_eq]
    ext x
    simp only [U, Opens.coe_inf, Opens.coe_mk, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_singleton_iff, Opens.coe_bot, Set.mem_empty_iff_false, iff_false, not_and]
    rintro rfl rfl
    exact hab rfl
  · obtain ⟨x, rfl⟩ := _root_.ConnectedComponents.surjective_coe c
    have hU : ((U (_root_.ConnectedComponents.mk x) : X.Opens) : Set X) = connectedComponent x :=
      connectedComponents_preimage_singleton
    constructor
    · haveI : ConnectedSpace (U (_root_.ConnectedComponents.mk x)).toScheme := by
        show ConnectedSpace ((U (_root_.ConnectedComponents.mk x) : Set X))
        rw [← isConnected_iff_connectedSpace, hU]
        exact isConnected_connectedComponent
      exact isIntegral_of_smooth_field_of_connectedSpace ((U (_root_.ConnectedComponents.mk x)).ι ≫ f)
    · refine IsClosedImmersion.of_isPreimmersion _ ?_
      rw [Scheme.Opens.range_ι, hU]
      exact isClosed_connectedComponent

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralClopenCoverOfSmoothQuasiCompactFieStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_clopen_cover_of_smooth_quasiCompact_field : ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Sp k) [Smooth f] [QuasiCompact f], ∃ (κ : Type) (U : κ → X.Opens), ⨆ c, U c = ⊤ ∧ (Pairwise fun a b => Disjoint (U a) (U b)) ∧ ∀ c, IsIntegral (U c).toScheme ∧ IsClosedImmersion (U c).ι := by
  first | exact @GlobalTheory.exists_integral_clopen_cover_of_smooth_field | exact GlobalTheory.exists_integral_clopen_cover_of_smooth_field | (intros; apply GlobalTheory.exists_integral_clopen_cover_of_smooth_field <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatBaseChangeSections
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SecFlatBC

theorem pullLE_ofSec {X X' : Scheme.{0}} {L : LB X} (τ : L.Sec) (π : X' ⟶ X) (V : X.Opens) (V' : X'.Opens)
    (e : V' ≤ π ⁻¹ᵁ V) :
    AbLaw.SecOn.pullLE L π V V' e (LB.ofSec τ V) = LB.ofSec (Cartier.secPull τ π) V' := by
  refine LB.sec_ext fun j => ?_
  rw [AbLaw.SecOn.coord_pullLE, LB.coord_ofSec, LB.coord_ofSec]
  simp only [Cartier.secPull, resG, Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

theorem sum_smul_f {X' : Scheme.{0}} {R' : Type} [CommRing R'] (f' : X' ⟶ Sp R') {M : LB X'} {n : ℕ}
    (c : Fin n → R') (τ : Fin n → M.Sec) (i : M.ι) :
    (∑ a, AbLaw.cst f' ⊤ (c a) • τ a).f i = ∑ a, cstOn f' _ (c a) * (τ a).f i := by
  let F : M.Sec →+ Γ(X', M.U i) := ⟨⟨fun s => s.f i, rfl⟩, fun _ _ => rfl⟩
  change F _ = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  change resG X' le_top (AbLaw.cst f' ⊤ (c a)) * (τ a).f i = _
  rw [show resG X' (le_top : M.U i ≤ ⊤) = AbLaw.rs X' le_top from rfl, AbLaw.rs_cst]
  rfl

theorem exists_sum_secPull : ∀ (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp R') (π : X' ⟶ X) [QuasiCompact f] [IsSeparated f] (L : LB X), φ.Flat → IsPullback π f' f (spMap φ) → L.IsLB → ∀ σ : (L.pull π).Sec, ∃ (n : ℕ) (c : Fin n → R') (τ : Fin n → L.Sec), ∀ i, σ.f i = ∑ a, cstOn f' _ (c a) * (Cartier.secPull (τ a) π).f i := by
  intro R R' _ _ φ X X' f f' π _ _ L hφ H hL σ
  letI := φ.toAlgebra
  haveI : Module.Flat R R' := hφ
  have H' : IsPullback π f' f (Spec.map (CommRingCat.ofHom (algebraMap R R'))) := H
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have := GlobalTheory.isAffineHom_diagonal_of_isSeparated f
  obtain ⟨m, D, hD, hc⟩ := GlobalTheory.exists_fin_affine_cover (X := X) (V := ⊤) isCompact_univ
  have hD' : ∀ s : Finset (Fin m), s.Nonempty → IsAffineOpen (⨅ i ∈ s, D i) :=
    GlobalTheory.isAffineOpen_finset_biInf hD
  have hc' := AbLaw.PerfOfModel.iSup_preimage π hc
  let E := AbLaw.CechOne.secKerEquiv (L.pull π) f' hc'
  let E₀ := AbLaw.CechOne.secKerEquiv L f hc
  let d := ((AbLaw.cechLB f L D).d 0 1).hom
  obtain ⟨x, hx, hxy⟩ := (AbLaw.PerfOfModel.termMap_bijOn hL H' hD').2.2 (E σ).2
  have hker : LinearMap.ker (d.baseChange R') = LinearMap.range ((LinearMap.ker d).subtype.baseChange R') :=
    Module.Flat.ker_lTensor_eq (R := R) R' R' d
  rw [hker] at hx
  obtain ⟨z, rfl⟩ := hx
  obtain ⟨S, rfl⟩ := TensorProduct.exists_finset z
  let e := S.equivFin
  refine ⟨S.card, fun a => (e.symm a).1.1, fun a => E₀.symm (e.symm a).1.2, ?_⟩

  have key : σ = ∑ a, AbLaw.cst f' ⊤ ((e.symm a).1.1) • Cartier.secPull (E₀.symm (e.symm a).1.2) π := by
    apply E.injective
    apply Subtype.ext
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hxy, map_sum, map_sum, map_sum, Submodule.coe_sum,
      ← Finset.sum_coe_sort S, ← e.symm.sum_comp]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [AbLaw.CechOne.secKerEquiv_smul, LinearMap.baseChange_tmul]
    funext s
    have hk : (((e.symm a).1.2).1 : (AbLaw.cechLB f L D).X 0) s =
        AbLaw.SecOnR.of f L _ (LB.ofSec (E₀.symm (e.symm a).1.2) (⨅ i ∈ s.1, D i)) := by
      rw [← AbLaw.CechOne.secKerEquiv_val L f hc]
      exact congrArg (fun y => (y.1 : (AbLaw.cechLB f L D).X 0) s) (E₀.apply_symm_apply _).symm
    change (e.symm a).1.1 • AbLaw.secCubePull L D H'.w s.1 ((((e.symm a).1.2).1 : (AbLaw.cechLB f L D).X 0) s) =
      (e.symm a).1.1 • ((E (Cartier.secPull (E₀.symm (e.symm a).1.2) π)).1 : (AbLaw.cechLB f' (L.pull π) fun i ↦ π ⁻¹ᵁ D i).X 0) s
    rw [hk, AbLaw.CechOne.secKerEquiv_val]
    change _ • AbLaw.SecOnR.pull L H'.w _ _ _ _ = _
    rw [AbLaw.SecOnR.pull_of, pullLE_ofSec]
    rfl
  intro i
  rw [key, sum_smul_f]

end GlobalTheory.SecFlatBC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActionLinearLogCoordinatesIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActionLinearLogCoordinatesIntegral
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory.LawLog ReciprocityTheory.ChartRestriction.G.TB

theorem actSt : ActSt := by
  intro C _ _ v d R _ _ O _ _ B hB σ _ a

  have hφ0 : ∀ i, constantCoeff (B.actK C a i) = 0 := by
    intro i
    show constantCoeff (MvPowerSeries.map (algebraMap R C) (B.A.act a i)) = 0
    rw [MvPowerSeries.constantCoeff_map, GlobalTheory.FBMap.nc_act B.A a i, map_zero]

  have hhom : comp1 (B.actK C a) (GlobalTheory.FBMap.mapLaw (algebraMap R C) B.G).F =
      addOf (GlobalTheory.FBMap.mapLaw (algebraMap R C) B.G).F (comp1 (B.actK C a) (pt C (n := 2) d 0))
        (comp1 (B.actK C a) (pt C (n := 2) d 1)) := by
    have h := (GlobalTheory.FBMap.mapAct (algebraMap R C) B.A).hom a
    rw [GlobalTheory.LawLog.add_pt] at h
    exact h

  have hcomp := GlobalTheory.FactorDepth.logOf_comp_hom _ _ (B.actK C a) hφ0 hhom
  have h0 : ∀ e, constantCoeff (subst (oneVar C d) (B.actK C a e)) = 0 := fun e =>
    constantCoeff_subst_eq_zero hs_oneVar cc_oneVar (hφ0 e)
  have hl : ∀ e, subst (fun f => subst (oneVar C d) (B.actK C a f)) ((fglOf hB).lg e) =
      ∑ f, dAct C B a e f • (fglOf hB).lg f := by
    intro e
    calc subst (fun f => subst (oneVar C d) (B.actK C a f)) ((fglOf hB).lg e)
        = subst (oneVar C d)
            (comp1 (GlobalTheory.FormalLog.logOf (GlobalTheory.FBMap.mapLaw (algebraMap R C) B.G)) (B.actK C a) e) :=
          GlobalTheory.LawLog.subst_oneVar (oneVar C d) cc_oneVar (B.actK C a) hφ0
            (GlobalTheory.FormalLog.logOf (GlobalTheory.FBMap.mapLaw (algebraMap R C) B.G) e)
      _ = ∑ f, dAct C B a e f • (fglOf hB).lg f := by
          rw [hcomp]
          dsimp only
          set_option synthInstance.maxHeartbeats 100000 in
            rw [← coe_substAlgHom hs_oneVar, map_sum]
          simp only [map_smul, coe_substAlgHom]
          exact Finset.sum_congr rfl fun f _ => rfl

  have hexp : ∀ w : Fin d → MvPowerSeries σ C, (∀ i, constantCoeff (w i) = 0) →
      expPt (fglOf hB) (mv (dAct C B a) w) =
        fun i => subst (fun q : Fin 1 × Fin d => expPt (fglOf hB) w q.2) (B.actK C a i) := by
    intro w hw
    have hsE : HasSubst (fun f => subst w (GlobalTheory.FGDepth.expOf (fglOf hB) f)) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero fun f => cc_expPt (fglOf hB) hw f
    funext i
    have key := GlobalTheory.FactorDepth.exp_eq_of_log_hom (fglOf hB) (fglOf hB) _ h0 (dAct C B a) hl
      (mv (dAct C B a) w) w hw (fun e => rfl) i
    show subst (mv (dAct C B a) w) (GlobalTheory.FGDepth.expOf (fglOf hB) i) = _
    rw [key, subst_comp_subst_apply hs_oneVar hsE]
    congr 1
    funext q
    exact subst_X hsE q.2
  refine ⟨hexp, fun w hw => ⟨cc_mv (dAct C B a) hw.1, fun i => ?_⟩⟩

  rw [hexp w hw.1]
  exact ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst v (hB.2.1 a i) (fun q => hw.2 q.2)
    (fun q => cc_expPt (fglOf hB) hw.1 q.2)

end GlobalTheory.IsoTriv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActionLinearLogCoordinatesIntegralStatement
open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.action_linear_logCoordinates_integral : ActSt := by
  first | exact @GlobalTheory.IsoTriv.actSt | exact GlobalTheory.IsoTriv.actSt | (intros; apply GlobalTheory.IsoTriv.actSt <;> assumption)
end
end
