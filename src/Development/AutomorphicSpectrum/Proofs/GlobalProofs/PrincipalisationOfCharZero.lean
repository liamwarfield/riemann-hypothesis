module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ResKOfResolutionPrincipalisation
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsIntegralBlowupOfSmooth
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.VanishingIdealSmoothAgreesOff

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocPrincipalSpan
namespace GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

def LocPrincipal {A : Type} [CommRing A] (I p : Ideal A) : Prop :=
  ∃ t f : A, t ∉ p ∧ f ∈ I ∧ f ≠ 0 ∧ ∀ g ∈ I, ∃ n : ℕ, t ^ n * g ∈ Ideal.span {f}

end GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsClosedCartierLocusSupport
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsSmoothAffinePresentationPair
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsSmoothAffinePresentationPair
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Charts

theorem smooth_affine_chart {k : Type} [Field k] {X : Scheme.{0}} (g : X ⟶ Sp k)
    (Z : X.IdealSheafData) (U : X.affineOpens) (hg : Smooth g) (hZ : Smooth (Z.subschemeι ≫ g)) :
    ∃ φ : k →+* Γ(X, U.1), φ.Smooth ∧ ((Ideal.Quotient.mk (Z.ideal U)).comp φ).Smooth := by
  let φ₀ : CommRingCat.of k ⟶ Γ(X, U.1) := Spec.preimage (U.2.fromSpec ≫ g)
  have h1 : Spec.map φ₀ = U.2.fromSpec ≫ g := Spec.map_preimage _
  refine ⟨φ₀.hom, ?_, ?_⟩
  · have : Smooth (Spec.map φ₀) := by
      rw [h1]
      exact @HasRingHomProperty.comp_of_isOpenImmersion @Smooth _ _ _ _ _ _ _
        (IsAffineOpen.isOpenImmersion_fromSpec (hU := U.2)) hg
    exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mp this
  · have hc : Z.subschemeCover.f U ≫ (Z.subschemeι ≫ g) =
        Spec.map (φ₀ ≫ CommRingCat.ofHom (Ideal.Quotient.mk (Z.ideal U))) := by
      rw [Spec.map_comp, h1, ← Category.assoc, Z.subschemeCover_map_subschemeι,
        Z.glueDataObjι_ι]
      exact Category.assoc _ _ _
    have : Smooth (Spec.map (φ₀ ≫ CommRingCat.ofHom (Ideal.Quotient.mk (Z.ideal U)))) := by
      rw [← hc]
      exact @HasRingHomProperty.comp_of_isOpenImmersion @Smooth _ _ _ _ _ _ _
        (Z.subschemeCover.map_prop U) hZ
    exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mp this

end GlobalTheory.CompanionTheory.Hypotheses₂.Charts
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsSmoothAffinePresentationPairStatement
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smooth_affine_presentation_pair : ∀ {k : Type} [Field k] {X : Scheme.{0}} (g : X ⟶ Sp k) (Z : X.IdealSheafData) (U : X.affineOpens), Smooth g → Smooth (Z.subschemeι ≫ g) → ∃ φ : k →+* Γ(X, U.1), φ.Smooth ∧ ((Ideal.Quotient.mk (Z.ideal U)).comp φ).Smooth := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Charts.smooth_affine_chart | exact GlobalTheory.CompanionTheory.Hypotheses₂.Charts.smooth_affine_chart | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Charts.smooth_affine_chart <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocallyPrincipalOfCartierAt
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocallyPrincipalOfCartierAt
noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

namespace GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

theorem exists_gen_of_map_eq_span {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (t : A)
    [IsLocalization.Away t B] (I : Ideal A) (b : B) (hb : b ≠ 0)
    (hI : I.map (algebraMap A B) = Ideal.span {b}) :
    ∃ f ∈ I, f ≠ 0 ∧ ∀ g ∈ I, ∃ n : ℕ, t ^ n * g ∈ Ideal.span {f} := by
  have hbI : b ∈ I.map (algebraMap A B) := by
    rw [hI]
    exact Ideal.mem_span_singleton_self b
  obtain ⟨⟨f, s⟩, hf⟩ := (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers t) B).mp hbI
  refine ⟨f, f.2, ?_, ?_⟩
  · intro h0
    apply hb
    rw [h0, map_zero] at hf
    exact ((IsLocalization.map_units B s).mul_left_eq_zero).mp hf
  · intro g hg
    have hg' : algebraMap A B g ∈ Ideal.span {b} := by
      rw [← hI]
      exact Ideal.mem_map_of_mem _ hg
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hg'
    obtain ⟨⟨a, u⟩, hu⟩ := IsLocalization.surj (Submonoid.powers t) c
    have key : algebraMap A B ((u : A) * (s : A) * g) = algebraMap A B (a * (f : A)) := by
      rw [map_mul, map_mul, map_mul, ← hc, ← hu, ← hf]
      ring
    obtain ⟨e, he⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers t) B).mp key
    obtain ⟨l, hl⟩ := (Submonoid.mem_powers_iff _ _).mp e.2
    obtain ⟨j, hj⟩ := (Submonoid.mem_powers_iff _ _).mp u.2
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
    rw [← hl, ← hj, ← hk] at he
    refine ⟨l + j + k, Ideal.mem_span_singleton'.mpr ⟨t ^ l * a, ?_⟩⟩
    rw [pow_add, pow_add]
    linear_combination -he

theorem locPrincipal_of_cartAt : ∀ {X : Scheme.{0}} [IsIntegral X] (Z : X.IdealSheafData)
    (U : X.affineOpens) (q : PrimeSpectrum Γ(X, U.1)), CartAt Z (U.2.fromSpec q) →
    LocPrincipal (Z.ideal U) q.asIdeal := by
  intro X _ Z U q hC
  obtain ⟨V, h, hxV, hh, hZV⟩ := hC
  have hxU : U.2.fromSpec q ∈ (U.1 : X.Opens) := by
    have hr : U.2.fromSpec q ∈ Set.range U.2.fromSpec := ⟨q, rfl⟩
    rw [U.2.range_fromSpec] at hr
    exact hr
  obtain ⟨f, g, hfg, hxf⟩ :=
    exists_basicOpen_le_affine_inter U.2 V.2 (U.2.fromSpec q) ⟨hxU, hxV⟩
  have hWU : X.basicOpen f ≤ U.1 := X.basicOpen_le f
  have hWV : X.basicOpen f ≤ V.1 := by
    rw [hfg]
    exact X.basicOpen_le g
  haveI : Nonempty (X.basicOpen f) := ⟨⟨_, hxf⟩⟩
  haveI : Nonempty (V.1 : X.Opens) := ⟨⟨_, hxV⟩⟩
  haveI : IsDomain Γ(X, V.1) := IsIntegral.component_integral V.1
  have hZW : Z.ideal (X.affineBasicOpen f) =
      Ideal.span {(X.presheaf.map (homOfLE hWV).op).hom h} := by
    have hmap := Z.map_ideal (U := X.affineBasicOpen f) (V := V) hWV
    rw [hZV, Ideal.map_span, Set.image_singleton] at hmap
    first
      | exact hmap.symm
      | (rw [← hmap]; rfl)
      | (convert hmap.symm using 3)
  letI : Algebra Γ(X, U.1) Γ(X, X.basicOpen f) := (X.presheaf.map (homOfLE hWU).op).hom.toAlgebra
  haveI : IsLocalization.Away f Γ(X, X.basicOpen f) := U.2.isLocalization_basicOpen f
  have hb : (X.presheaf.map (homOfLE hWV).op).hom h ≠ 0 := by
    intro h0
    apply nonZeroDivisors.ne_zero hh
    apply map_injective_of_isIntegral X (homOfLE hWV)
    rw [map_zero]
    exact h0
  have hI : (Z.ideal U).map (algebraMap Γ(X, U.1) Γ(X, X.basicOpen f)) =
      Ideal.span {(X.presheaf.map (homOfLE hWV).op).hom h} := by
    rw [← hZW]
    first
      | exact Z.map_ideal (U := X.affineBasicOpen f) (V := U) hWU
      | exact Z.map_ideal_basicOpen U f
  obtain ⟨f0, hf0, hf0ne, hgen⟩ :=
    GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.exists_gen_of_map_eq_span f (Z.ideal U) _ hb hI
  refine ⟨f, f0, ?_, hf0, hf0ne, hgen⟩
  have hq : q ∈ PrimeSpectrum.basicOpen f :=
    Eq.mp (congrArg (q ∈ ·) (U.2.fromSpec_preimage_basicOpen f)) hxf
  exact (PrimeSpectrum.mem_basicOpen f q).mp hq

end GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocallyPrincipalOfCartierAtStatement
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locally_principal_of_cartier_at : ∀ {X : Scheme.{0}} [IsIntegral X] (Z : X.IdealSheafData) (U : X.affineOpens) (q : PrimeSpectrum Γ(X, U.1)), CartAt Z (U.2.fromSpec q) → LocPrincipal (Z.ideal U) q.asIdeal := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.locPrincipal_of_cartAt | exact GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.locPrincipal_of_cartAt | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.locPrincipal_of_cartAt <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocallyPrincipalOfConormalRankOne
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocallyPrincipalOfConormalRankOne
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

namespace GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

theorem exists_generator_of_rankAtStalk_eq_one {B M : Type*} [CommRing B] [AddCommGroup M]
    [Module B M] [Module.Finite B M] [Module.Projective B M] (P : PrimeSpectrum B)
    (h : Module.rankAtStalk M P = 1) :
    ∃ m : M, ∀ x : M, ∃ s : B, s ∉ P.asIdeal ∧ ∃ b : B, s • x = b • m := by
  haveI : Module.Flat B M := Module.Flat.of_projective
  let S := P.asIdeal.primeCompl
  let f := LocalizedModule.mkLinearMap S M
  haveI : Module.Free (Localization.AtPrime P.asIdeal) (LocalizedModule S M) :=
    Module.mem_freeLocus.mp (by simp only [Module.freeLocus_eq_univ, Set.mem_univ])
  haveI : Module.Finite (Localization.AtPrime P.asIdeal) (LocalizedModule S M) :=
    Module.Finite.of_isLocalizedModule S f
  let e := Module.finBasisOfFinrankEq (Localization.AtPrime P.asIdeal) (LocalizedModule S M) h
  obtain ⟨⟨m, s0⟩, hm⟩ := IsLocalizedModule.surj S f (e 0)
  refine ⟨m, fun x => ?_⟩
  have hx : f x = (e.repr (f x) 0) • e 0 := by
    have hsum := e.sum_repr (f x)
    rw [Fin.sum_univ_one] at hsum
    exact hsum.symm
  obtain ⟨⟨a, u⟩, hu⟩ := IsLocalization.surj S (e.repr (f x) 0)
  have key : f (((u : B) * (s0 : B)) • x) = f (a • m) := by
    rw [map_smul, map_smul, hx, ← hm, Submonoid.smul_def,
      ← algebraMap_smul (Localization.AtPrime P.asIdeal) ((u : B) * (s0 : B)),
      ← algebraMap_smul (Localization.AtPrime P.asIdeal) a,
      ← algebraMap_smul (Localization.AtPrime P.asIdeal) (s0 : B)]
    simp only [smul_smul]
    congr 1
    rw [map_mul, ← hu]
    ring
  obtain ⟨v, hv⟩ := (IsLocalizedModule.eq_iff_exists S f).mp key
  refine ⟨(v : B) * ((u : B) * (s0 : B)), (v * (u * s0)).2, (v : B) * a, ?_⟩
  first
    | (rw [mul_smul (v : B) ((u : B) * (s0 : B)) x, mul_smul (v : B) a m]; exact hv)
    | simpa only [Submonoid.smul_def, mul_smul] using hv

theorem locPrincipal_of_rankAtStalk_eq_one {A : Type} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] (I : Ideal A) [Module.Finite (A ⧸ I) I.Cotangent]
    [Module.Projective (A ⧸ I) I.Cotangent] (P : PrimeSpectrum (A ⧸ I))
    (hP : Module.rankAtStalk I.Cotangent P = 1) :
    LocPrincipal I (P.asIdeal.comap (Ideal.Quotient.mk I)) := by
  set p := P.asIdeal.comap (Ideal.Quotient.mk I) with hp_def
  haveI hpP : p.IsPrime := Ideal.comap_isPrime _ _
  have hIp : I ≤ p := fun x hx => by
    rw [hp_def, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact P.asIdeal.zero_mem
  obtain ⟨m0, hm0⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.exists_generator_of_rankAtStalk_eq_one P hP
  obtain ⟨⟨f0, hf0I⟩, hf0⟩ := Ideal.toCotangent_surjective I m0
  have hsm : ∀ (r : A) (y : I.Cotangent), Ideal.Quotient.mk I r • y = r • y := by
    intro r y
    first
      | (rw [← Ideal.Quotient.algebraMap_eq]; exact algebraMap_smul (A ⧸ I) r y)
      | rfl
      | (obtain ⟨y', rfl⟩ := Ideal.toCotangent_surjective I y; rfl)
  have step : ∀ x ∈ I, ∃ s ∉ p, ∃ b : A, s * x - b * f0 ∈ I ^ 2 := by
    intro x hx
    obtain ⟨sq, hsq, bq, hsb⟩ := hm0 (I.toCotangent ⟨x, hx⟩)
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective sq
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective bq
    refine ⟨s, hsq, b, ?_⟩
    rw [← hf0, hsm, hsm, ← map_smul I.toCotangent, ← map_smul I.toCotangent,
      Ideal.toCotangent_eq] at hsb
    simpa only [Submodule.coe_smul, smul_eq_mul] using hsb
  let φ := algebraMap A (Localization.AtPrime p)
  set K : Ideal A := Ideal.span {f0} with hK
  have hIfg : I.FG := IsNoetherian.noetherian I
  have hle : I.map φ ≤ K.map φ ⊔ IsLocalRing.maximalIdeal (Localization.AtPrime p) • I.map φ := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap]
    obtain ⟨s, hs, b, hsb⟩ := step x hx
    have hunit : IsUnit (φ s) :=
      IsLocalization.map_units (Localization.AtPrime p) (⟨s, hs⟩ : p.primeCompl)
    rw [← Ideal.unit_mul_mem_iff_mem _ hunit, ← map_mul]
    have hdecomp : s * x = b * f0 + (s * x - b * f0) := by ring
    rw [hdecomp, map_add (f := _)]
    refine Submodule.add_mem_sup ?_ ?_
    · exact Ideal.mem_map_of_mem _ (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self f0))
    · have h2 : φ (s * x - b * f0) ∈ (I ^ 2).map φ := Ideal.mem_map_of_mem _ hsb
      rw [Ideal.map_pow, pow_two] at h2
      rw [Ideal.smul_eq_mul]
      exact Ideal.mul_mono_left
        (le_trans (Ideal.map_mono hIp) (Localization.AtPrime.map_eq_maximalIdeal).le) h2
  have hnak : I.map φ ≤ K.map φ :=
    Submodule.le_of_le_smul_of_le_jacobson_bot (hIfg.map φ)
      (IsLocalRing.maximalIdeal_le_jacobson ⊥) hle
  have hloc : ∀ x ∈ I, ∃ s ∉ p, s * x ∈ K := by
    intro x hx
    obtain ⟨s, hs, hsx⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff p.primeCompl
      (Localization.AtPrime p) K x).mp (hnak (Ideal.mem_map_of_mem φ hx))
    exact ⟨s, hs, hsx⟩
  have hunif : ∀ N : Submodule A A, N.FG → N ≤ I → ∃ s ∉ p, ∀ y ∈ N, s * y ∈ K := by
    intro N hN
    refine Submodule.fg_induction
      (motive := fun N _ => N ≤ I → ∃ s ∉ p, ∀ y ∈ N, s * y ∈ K) ?_ ?_ N hN
    · intro x hxI
      obtain ⟨s, hs, hsx⟩ := hloc x (hxI (Submodule.mem_span_singleton_self x))
      refine ⟨s, hs, fun y hy => ?_⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
      rw [smul_eq_mul, mul_left_comm]
      exact K.mul_mem_left c hsx
    · intro N₁ N₂ _ _ ih₁ ih₂ h₁₂
      obtain ⟨s₁, hs₁, h₁⟩ := ih₁ (le_trans le_sup_left h₁₂)
      obtain ⟨s₂, hs₂, h₂⟩ := ih₂ (le_trans le_sup_right h₁₂)
      refine ⟨s₁ * s₂, fun hmem => (hpP.mem_or_mem hmem).elim hs₁ hs₂, fun y hy => ?_⟩
      obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.mp hy
      have hsplit : s₁ * s₂ * (y₁ + y₂) = s₂ * (s₁ * y₁) + s₁ * (s₂ * y₂) := by ring
      rw [hsplit]
      exact K.add_mem (K.mul_mem_left _ (h₁ y₁ hy₁)) (K.mul_mem_left _ (h₂ y₂ hy₂))
  obtain ⟨t, ht, htI⟩ := hunif I hIfg le_rfl
  have hf0ne : f0 ≠ 0 := by
    intro h0
    have hbot : ∀ y : I, y = 0 := by
      intro y
      apply Subtype.ext
      obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp (htI y y.2)
      rw [h0, mul_zero] at ha
      rcases mul_eq_zero.mp ha.symm with h | h
      · rw [h] at ht
        exact absurd p.zero_mem ht
      · exact h
    haveI : Subsingleton I.Cotangent := ⟨fun a b => by
      obtain ⟨a', rfl⟩ := Ideal.toCotangent_surjective I a
      obtain ⟨b', rfl⟩ := Ideal.toCotangent_surjective I b
      rw [hbot a', hbot b']⟩
    have h0rank := Module.rankAtStalk_eq_zero_of_subsingleton (R := A ⧸ I) (M := I.Cotangent)
    rw [h0rank] at hP
    first
      | exact zero_ne_one hP
      | simp at hP
  refine ⟨t, f0, ht, hf0I, hf0ne, fun g hg => ⟨1, ?_⟩⟩
  rw [pow_one]
  exact htI g hg

end GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocallyPrincipalOfConormalRankOneStatement
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locally_principal_of_conormal_rank_one : ∀ {A : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A] (I : Ideal A) [Module.Finite (A ⧸ I) I.Cotangent] [Module.Projective (A ⧸ I) I.Cotangent] (P : PrimeSpectrum (A ⧸ I)), Module.rankAtStalk I.Cotangent P = 1 → LocPrincipal I (P.asIdeal.comap (Ideal.Quotient.mk I)) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.locPrincipal_of_rankAtStalk_eq_one | exact GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.locPrincipal_of_rankAtStalk_eq_one | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.locPrincipal_of_rankAtStalk_eq_one <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConormalRankOneOfLocallyPrincipal
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConormalRankOneOfLocallyPrincipal
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

namespace GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

theorem LocPrincipal.exists_pow_mul_sq {A : Type} [CommRing A] {I : Ideal A} {t f : A}
    (h : ∀ g ∈ I, ∃ n : ℕ, t ^ n * g ∈ Ideal.span {f}) {x : A} (hx : x ∈ I ^ 2) :
    ∃ N : ℕ, ∃ c : A, t ^ N * x = c * (f * f) := by
  rw [pow_two] at hx
  refine Submodule.mul_induction_on hx ?_ ?_
  · intro g hg k hk
    obtain ⟨n, hn⟩ := h g hg
    obtain ⟨m, hm⟩ := h k hk
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hn
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 hm
    refine ⟨n + m, a * b, ?_⟩
    calc t ^ (n + m) * (g * k) = (t ^ n * g) * (t ^ m * k) := by ring
      _ = a * b * (f * f) := by rw [← ha, ← hb]; ring
  · rintro x y ⟨N, c, hc⟩ ⟨M, d, hd⟩
    refine ⟨N + M, t ^ M * c + t ^ N * d, ?_⟩
    calc t ^ (N + M) * (x + y) = t ^ M * (t ^ N * x) + t ^ N * (t ^ M * y) := by ring
      _ = _ := by rw [hc, hd]; ring

theorem LocPrincipal.smul_toCotangent_ne_zero {A : Type} [CommRing A] [IsDomain A] {I p : Ideal A}
    [p.IsPrime] (hIp : I ≤ p) {t f : A} (ht : t ∉ p) (hf : f ∈ I) (hf0 : f ≠ 0)
    (h : ∀ g ∈ I, ∃ n : ℕ, t ^ n * g ∈ Ideal.span {f}) {s : A} (hs : s ∉ p) :
    s • I.toCotangent ⟨f, hf⟩ ≠ 0 := by
  intro h0
  rw [← map_smul I.toCotangent s ⟨f, hf⟩, Ideal.toCotangent_eq_zero] at h0
  have h0' : s * f ∈ I ^ 2 := by simpa [smul_eq_mul] using h0
  obtain ⟨N, c, hc⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.LocPrincipal.exists_pow_mul_sq h h0'
  have hcancel : t ^ N * s = c * f := by
    apply mul_right_cancel₀ hf0
    calc t ^ N * s * f = t ^ N * (s * f) := by ring
      _ = c * (f * f) := hc
      _ = c * f * f := by ring
  have hmem : t ^ N * s ∈ p := by
    rw [hcancel]
    exact hIp (I.mul_mem_left c hf)
  rcases Ideal.IsPrime.mem_or_mem ‹p.IsPrime› hmem with h1 | h1
  · exact ht (Ideal.IsPrime.mem_of_pow_mem ‹p.IsPrime› N h1)
  · exact hs h1

theorem LocPrincipal.exists_pow_smul_eq {A : Type} [CommRing A] {I : Ideal A} {t f : A}
    (hf : f ∈ I) (h : ∀ g ∈ I, ∃ n : ℕ, t ^ n * g ∈ Ideal.span {f}) (m : I.Cotangent) :
    ∃ (n : ℕ) (c : A), t ^ n • m = c • I.toCotangent ⟨f, hf⟩ := by
  obtain ⟨g, rfl⟩ := I.toCotangent_surjective m
  obtain ⟨n, hn⟩ := h g g.2
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hn
  refine ⟨n, c, ?_⟩
  rw [← map_smul I.toCotangent (t ^ n) g, ← map_smul I.toCotangent c ⟨f, hf⟩]
  congr 1
  ext
  simp [smul_eq_mul, hc]

theorem rankAtStalk_cotangent_eq_one {A : Type} [CommRing A] [IsDomain A] (I : Ideal A)
    [Module.Finite (A ⧸ I) I.Cotangent] [Module.Projective (A ⧸ I) I.Cotangent]
    (P : PrimeSpectrum (A ⧸ I))
    (hP : LocPrincipal I (P.asIdeal.comap (Ideal.Quotient.mk I))) :
    Module.rankAtStalk I.Cotangent P = 1 := by
  obtain ⟨t, f, ht, hf, hf0, h⟩ := hP
  have htP : Ideal.Quotient.mk I t ∉ P.asIdeal := fun H => ht (Ideal.mem_comap.mpr H)
  have hIq : I ≤ P.asIdeal.comap (Ideal.Quotient.mk I) := fun g hg => by
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hg]
    exact zero_mem _
  have hsmul : ∀ (a : A) (m : I.Cotangent), Ideal.Quotient.mk I a • m = a • m := fun a m => by
    rw [← Ideal.Quotient.algebraMap_eq, algebraMap_smul]
  have hspan : Submodule.span (Localization.AtPrime P.asIdeal)
      {LocalizedModule.mk (I.toCotangent ⟨f, hf⟩) (1 : P.asIdeal.primeCompl)} = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro y
    induction y using LocalizedModule.induction_on with
    | h m s =>
      obtain ⟨n, c, hc⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.LocPrincipal.exists_pow_smul_eq hf h m
      have htn : (Ideal.Quotient.mk I t) ^ n ∈ P.asIdeal.primeCompl :=
        Ideal.mem_primeCompl_iff.mpr fun H => htP (Ideal.IsPrime.mem_of_pow_mem P.isPrime n H)
      have key : Ideal.Quotient.mk I c • I.toCotangent ⟨f, hf⟩ =
          (⟨_, htn⟩ : P.asIdeal.primeCompl) • m := by
        rw [Submonoid.mk_smul, hsmul, ← map_pow, hsmul]
        exact hc.symm
      rw [Submodule.mem_span_singleton]
      refine ⟨Localization.mk (Ideal.Quotient.mk I c) (⟨_, htn⟩ * s), ?_⟩
      rw [LocalizedModule.mk_smul_mk, key, mul_one, LocalizedModule.mk_cancel_common_left]
  have hx : LocalizedModule.mk (I.toCotangent ⟨f, hf⟩) (1 : P.asIdeal.primeCompl) ≠ 0 := by
    intro H
    rw [← LocalizedModule.zero_mk (1 : P.asIdeal.primeCompl), LocalizedModule.mk_eq] at H
    obtain ⟨⟨u, hu⟩, hu0⟩ := H
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective u
    simp only [one_smul, smul_zero, Submonoid.mk_smul] at hu0
    rw [hsmul] at hu0
    exact GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.LocPrincipal.smul_toCotangent_ne_zero hIq ht hf hf0 h
      (fun hs => Ideal.mem_primeCompl_iff.mp hu (Ideal.mem_comap.mp hs)) hu0
  have hfree : Module.Free (Localization.AtPrime P.asIdeal)
      (LocalizedModule P.asIdeal.primeCompl I.Cotangent) := by
    haveI : Module.Flat (A ⧸ I) I.Cotangent := Module.Flat.of_projective
    have hmem : P ∈ Module.freeLocus (A ⧸ I) I.Cotangent := by
      rw [Module.freeLocus_eq_univ]
      trivial
    exact Module.mem_freeLocus.mp hmem
  haveI : Module.Finite (Localization.AtPrime P.asIdeal)
      (LocalizedModule P.asIdeal.primeCompl I.Cotangent) :=
    Module.Finite.of_fg_top ⟨{LocalizedModule.mk (I.toCotangent ⟨f, hf⟩) 1}, by
      rw [Finset.coe_singleton]
      exact hspan⟩
  haveI := nontrivial_of_ne _ _ hx
  have hle : Module.finrank (Localization.AtPrime P.asIdeal)
      (LocalizedModule P.asIdeal.primeCompl I.Cotangent) ≤ 1 := by
    have := finrank_le_of_span_eq_top (R := Localization.AtPrime P.asIdeal)
      (v := fun _ : Unit => LocalizedModule.mk (I.toCotangent ⟨f, hf⟩)
        (1 : P.asIdeal.primeCompl)) (by rw [Set.range_const]; exact hspan)
    simpa using this
  have hpos : 0 < Module.finrank (Localization.AtPrime P.asIdeal)
      (LocalizedModule P.asIdeal.primeCompl I.Cotangent) :=
    (Module.finrank_pos_iff_of_free _ _).mpr inferInstance
  show Module.finrank (Localization.AtPrime P.asIdeal)
    (LocalizedModule P.asIdeal.primeCompl I.Cotangent) = 1
  omega

end GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConormalRankOneOfLocallyPrincipalStatement
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conormal_rank_one_of_locally_principal : ∀ {A : Type} [CommRing A] [IsDomain A] (I : Ideal A) [Module.Finite (A ⧸ I) I.Cotangent] [Module.Projective (A ⧸ I) I.Cotangent] (P : PrimeSpectrum (A ⧸ I)), LocPrincipal I (P.asIdeal.comap (Ideal.Quotient.mk I)) → Module.rankAtStalk I.Cotangent P = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.rankAtStalk_cotangent_eq_one | exact GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.rankAtStalk_cotangent_eq_one | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.rankAtStalk_cotangent_eq_one <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.CartierAtOfLocallyPrincipal
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.CartierAtOfLocallyPrincipal
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

namespace GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

theorem cartAt_of_locPrincipal : ∀ {X : Scheme.{0}} [IsIntegral X] (Z : X.IdealSheafData)
    (U : X.affineOpens) (q : PrimeSpectrum Γ(X, U.1)),
    LocPrincipal (Z.ideal U) q.asIdeal → CartAt Z (U.2.fromSpec q) := by
  intro X _ Z U q h
  obtain ⟨t, f, ht, hfI, hf0, hg⟩ := h
  have hx : U.2.fromSpec q ∈ X.basicOpen t := by
    have h1 : q ∈ U.2.fromSpec ⁻¹ᵁ X.basicOpen t := by
      rw [U.2.fromSpec_preimage_basicOpen]
      exact ht
    exact h1
  have hxU : U.2.fromSpec q ∈ U.1 := X.basicOpen_le t hx
  have inst := U.2.isLocalization_basicOpen t
  let ρ : Γ(X, U.1) →+* Γ(X, X.basicOpen t) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le t)).op).hom
  have hu : IsUnit (ρ t) :=
    IsLocalization.Away.algebraMap_isUnit (S := Γ(X, X.basicOpen t)) t
  have hZ : Z.ideal (X.affineBasicOpen t) = Ideal.map ρ (Z.ideal U) :=
    (Z.map_ideal_basicOpen U t).symm
  have hne : Nonempty (X.basicOpen t : X.Opens) := ⟨⟨_, hx⟩⟩
  have hρf : ρ f ≠ 0 := by
    intro h0
    apply hf0
    apply germ_injective_of_isIntegral X (U := U.1) (U.2.fromSpec q) hxU
    have h2 := congrArg (X.presheaf.germ (X.basicOpen t) (U.2.fromSpec q) hx).hom h0
    rw [map_zero] at h2 ⊢
    rw [← h2]
    simp [ρ]
  have hnz : ρ f ∈ nonZeroDivisors Γ(X, X.basicOpen t) := mem_nonZeroDivisors_of_ne_zero hρf
  suffices hspan : Ideal.map ρ (Z.ideal U) = Ideal.span {ρ f} from
    ⟨X.affineBasicOpen t, ρ f, hx, hnz, hZ.trans hspan⟩
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro g hgI
    obtain ⟨n, hn⟩ := hg g hgI
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hn
    rw [Ideal.mem_comap, Ideal.mem_span_singleton']
    obtain ⟨u, hu'⟩ := hu.pow n
    refine ⟨(↑u⁻¹ : Γ(X, X.basicOpen t)) * ρ c, ?_⟩
    have h3 : ρ c * ρ f = ρ t ^ n * ρ g := by
      rw [← map_mul, hc, map_mul, map_pow]
    rw [mul_assoc, h3, ← hu', Units.inv_mul_cancel_left]
  · rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_map_of_mem ρ hfI

end GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.CartierAtOfLocallyPrincipalStatement
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cartier_at_of_locally_principal : ∀ {X : Scheme.{0}} [IsIntegral X] (Z : X.IdealSheafData) (U : X.affineOpens) (q : PrimeSpectrum Γ(X, U.1)), LocPrincipal (Z.ideal U) q.asIdeal → CartAt Z (U.2.fromSpec q) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.cartAt_of_locPrincipal | exact GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.cartAt_of_locPrincipal | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.cartAt_of_locPrincipal <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConormalFiniteProjectiveOfSmooth
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConormalFiniteProjectiveOfSmooth
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver


open TensorProduct in
theorem GlobalTheory.CompanionTheory.Hypotheses₂.Conormal.finite_projective_cotangent :
    ∀ {k A : Type} [Field k] [CommRing A] (φ : k →+* A) (I : Ideal A), φ.Smooth →
      ((Ideal.Quotient.mk I).comp φ).Smooth →
        Module.Finite (A ⧸ I) I.Cotangent ∧ Module.Projective (A ⧸ I) I.Cotangent := by
  intro k A _ _ φ I h1 h2
  letI := φ.toAlgebra
  haveI hA : Algebra.Smooth k A := h1
  have halg : (Ideal.Quotient.algebra k : Algebra k (A ⧸ I)) =
      ((Ideal.Quotient.mk I).comp φ).toAlgebra := Algebra.algebra_ext _ _ fun _ => rfl
  have hQ : Algebra.FormallySmooth k (A ⧸ I) := by
    have hs : @Algebra.Smooth k _ (A ⧸ I) _ ((Ideal.Quotient.mk I).comp φ).toAlgebra := h2
    rw [← halg] at hs
    exact hs.formallySmooth
  haveI : Algebra.FormallySmooth k A := hA.formallySmooth
  haveI : Module.Projective A (KaehlerDifferential k A) :=
    Algebra.FormallySmooth.projective_kaehlerDifferential
  haveI : Algebra.FinitePresentation k A := hA.finitePresentation
  haveI : Algebra.FiniteType k A := Algebra.FiniteType.of_finitePresentation
  haveI : Algebra.EssFiniteType k A := Algebra.EssFiniteType.of_finiteType k A
  haveI : Module.Finite A (KaehlerDifferential k A) := KaehlerDifferential.finite k A
  haveI : Module.Finite (A ⧸ I) ((A ⧸ I) ⊗[A] KaehlerDifferential k A) :=
    Module.Finite.base_change A (A ⧸ I) _
  haveI : IsScalarTower A (A ⧸ I) I.Cotangent := by
    first
    | infer_instance
    | exact IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  obtain ⟨l, hl⟩ := (Algebra.FormallySmooth.iff_split_injection (R := k) (P := A) (A := A ⧸ I)
    Ideal.Quotient.mk_surjective).mp hQ
  have hsurj : Function.Surjective (algebraMap A (A ⧸ I)) := Ideal.Quotient.mk_surjective
  let e := Ideal.Cotangent.equivOfEq _ _ (Ideal.mk_ker (I := I))
  let i : I.Cotangent →ₗ[A ⧸ I] (A ⧸ I) ⊗[A] KaehlerDifferential k A :=
    LinearMap.extendScalarsOfSurjective hsurj
      (KaehlerDifferential.kerCotangentToTensor k A (A ⧸ I) ∘ₗ e.symm.toLinearMap)
  let s : (A ⧸ I) ⊗[A] KaehlerDifferential k A →ₗ[A ⧸ I] I.Cotangent :=
    LinearMap.extendScalarsOfSurjective hsurj (e.toLinearMap ∘ₗ l)
  have hsi : s ∘ₗ i = LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    have h := LinearMap.congr_fun hl (e.symm x)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h
    first
    | (simp only [s, i, LinearMap.comp_apply, LinearMap.extendScalarsOfSurjective_apply,
        LinearEquiv.coe_coe, LinearMap.id_apply, h, LinearEquiv.apply_symm_apply]; done)
    | (show e (l (KaehlerDifferential.kerCotangentToTensor k A (A ⧸ I) (e.symm x))) = x
       rw [h, LinearEquiv.apply_symm_apply])
  refine ⟨Module.Finite.of_surjective s fun x => ⟨i x, ?_⟩, Module.Projective.of_split i s hsi⟩
  simpa only [LinearMap.comp_apply, LinearMap.id_apply] using LinearMap.congr_fun hsi x
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConormalFiniteProjectiveOfSmoothStatement
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conormal_finite_projective_of_smooth : ∀ {k A : Type} [Field k] [CommRing A] (φ : k →+* A) (I : Ideal A), φ.Smooth → ((Ideal.Quotient.mk I).comp φ).Smooth → Module.Finite (A ⧸ I) I.Cotangent ∧ Module.Projective (A ⧸ I) I.Cotangent := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Conormal.finite_projective_cotangent | exact GlobalTheory.CompanionTheory.Hypotheses₂.Conormal.finite_projective_cotangent | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Conormal.finite_projective_cotangent <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsClosedCartierLocusSupport
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

namespace GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

theorem locPrincipal_locally_const {k A : Type} [Field k] [CommRing A] [IsDomain A] (φ : k →+* A) (I : Ideal A)
    (hφ : φ.Smooth) (hI : ((Ideal.Quotient.mk I).comp φ).Smooth) (p : PrimeSpectrum A)
    (hp : I ≤ p.asIdeal) :
    ∃ s, s ∉ p.asIdeal ∧ ∀ q : PrimeSpectrum A, s ∉ q.asIdeal → I ≤ q.asIdeal →
      (LocPrincipal I q.asIdeal ↔ LocPrincipal I p.asIdeal) := by
  obtain ⟨hfin, hproj⟩ := GlobalTheory.T.conormal_finite_projective_of_smooth φ I hφ hI
  have hnoeth : IsNoetherianRing A := by
    algebraize [φ]
    have : Algebra.FiniteType k A := inferInstance
    exact Algebra.FiniteType.isNoetherianRing k A
  have := Module.finitePresentation_of_projective (A ⧸ I) I.Cotangent
  have hsurj : Function.Surjective (Ideal.Quotient.mk I) := Ideal.Quotient.mk_surjective
  have hce := PrimeSpectrum.isClosedEmbedding_comap_of_surjective (A ⧸ I) (Ideal.Quotient.mk I) hsurj
  have hrange : ∀ q : PrimeSpectrum A, I ≤ q.asIdeal →
      ∃ Q : PrimeSpectrum (A ⧸ I), PrimeSpectrum.comap (Ideal.Quotient.mk I) Q = q := by
    intro q hq
    have : q ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) := by
      rw [_root_.range_comap_of_surjective _ _ hsurj, Ideal.mk_ker]
      exact hq
    exact this
  obtain ⟨P0, hP0⟩ := hrange p hp
  have hlc : IsLocallyConstant (Module.rankAtStalk (R := A ⧸ I) I.Cotangent) :=
    Module.isLocallyConstant_rankAtStalk
  have hO := hlc.isOpen_fiber (Module.rankAtStalk (R := A ⧸ I) I.Cotangent P0)
  obtain ⟨W, hW, hWO⟩ := hce.isInducing.isOpen_iff.1 hO
  have hpW : p ∈ W := by
    have : P0 ∈ PrimeSpectrum.comap (Ideal.Quotient.mk I) ⁻¹' W := by rw [hWO]; rfl
    rwa [Set.mem_preimage, hP0] at this
  obtain ⟨_, ⟨s, rfl⟩, hps, hsW⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hpW hW
  refine ⟨s, hps, fun q hs hq => ?_⟩
  obtain ⟨Q, hQ⟩ := hrange q hq
  have hQO : Module.rankAtStalk (R := A ⧸ I) I.Cotangent Q = Module.rankAtStalk (R := A ⧸ I) I.Cotangent P0 := by
    have : Q ∈ PrimeSpectrum.comap (Ideal.Quotient.mk I) ⁻¹' W := by
      rw [Set.mem_preimage, hQ]; exact hsW hs
    rw [hWO] at this
    exact this
  have e : ∀ R : PrimeSpectrum (A ⧸ I), LocPrincipal I (PrimeSpectrum.comap (Ideal.Quotient.mk I) R).asIdeal ↔ Module.rankAtStalk (R := A ⧸ I) I.Cotangent R = 1 :=
    fun R => ⟨GlobalTheory.T.conormal_rank_one_of_locally_principal I R, GlobalTheory.T.locally_principal_of_conormal_rank_one I R⟩
  rw [← hQ, ← hP0, e, e, hQO]

theorem fromSpec_mem_basicOpen_iff {X : Scheme.{0}} (U : X.affineOpens) (q : PrimeSpectrum Γ(X, U.1))
    (f : Γ(X, U.1)) : U.2.fromSpec q ∈ X.basicOpen f ↔ f ∉ q.asIdeal := by
  have := U.2.fromSpec_preimage_basicOpen f
  have h2 : q ∈ U.2.fromSpec ⁻¹ᵁ X.basicOpen f ↔ q ∈ PrimeSpectrum.basicOpen f := by
    rw [this]; rfl
  exact h2

theorem isClosed_of_locally_iff {T : Type*} [TopologicalSpace T] {C : Set T} (hC : IsClosed C)
    (P : T → Prop) (h : ∀ x ∈ C, ∃ V : Set T, IsOpen V ∧ x ∈ V ∧ ∀ y ∈ V, y ∈ C → (P y ↔ P x)) :
    IsClosed {x | x ∈ C ∧ P x} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  by_cases hxC : x ∈ C
  · obtain ⟨V, hV, hxV, hy⟩ := h x hxC
    refine ⟨V, fun y hyV hyS => hx ⟨hxC, (hy y hyV hyS.1).1 hyS.2⟩, hV, hxV⟩
  · exact ⟨Cᶜ, fun y hy hyS => hy hyS.1, hC.isOpen_compl, hxC⟩

theorem isClosed_cartAt : ∀ {k : Type} [Field k] {X : Scheme.{0}} (g : X ⟶ Sp k) (Z : X.IdealSheafData), Smooth g → IsIntegral X → Smooth (Z.subschemeι ≫ g) → IsClosed {x : X | x ∈ Z.support ∧ CartAt Z x} ∧ IsClosed {x : X | x ∈ Z.support ∧ ¬ CartAt Z x} := by
  intro k _ X g Z hg hX hZ
  have key : ∀ x ∈ (Z.support : Set X), ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
      ∀ y ∈ V, y ∈ (Z.support : Set X) → (CartAt Z y ↔ CartAt Z x) := by
    intro x hx
    obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
    let U' : X.affineOpens := ⟨U, hU⟩
    have hne : Nonempty U := ⟨⟨x, hxU⟩⟩
    have hdom : IsDomain Γ(X, U'.1) := inferInstanceAs (IsDomain Γ(X, U))
    obtain ⟨φ, hφ, hI⟩ := GlobalTheory.T.exists_smooth_affine_presentation_pair g Z U' hg hZ
    have hrange : ∀ y ∈ U, ∃ q, U'.2.fromSpec q = y := by
      intro y hy
      have : y ∈ Set.range U'.2.fromSpec := by rw [U'.2.range_fromSpec]; exact hy
      exact this
    have hIq : ∀ q : PrimeSpectrum Γ(X, U'.1), U'.2.fromSpec q ∈ (Z.support : Set X) →
        Z.ideal U' ≤ q.asIdeal := by
      intro q hq f hf
      by_contra hfq
      have hb := (fromSpec_mem_basicOpen_iff U' q f).2 hfq
      have hmem : U'.2.fromSpec q ∈ (Z.support : Set X) ∩ (U'.1 : Set X) :=
        ⟨hq, X.basicOpen_le f hb⟩
      rw [Z.coe_support_inter U'] at hmem
      exact (Scheme.mem_zeroLocus_iff _ _ _).1 hmem.1 f hf hb
    obtain ⟨q0, rfl⟩ := hrange x hxU
    obtain ⟨s, hs, h⟩ := locPrincipal_locally_const φ (Z.ideal U') hφ hI q0 (hIq q0 hx)
    refine ⟨X.basicOpen s, (X.basicOpen s).isOpen, (fromSpec_mem_basicOpen_iff U' q0 s).2 hs, ?_⟩
    intro y hy hyZ
    obtain ⟨q, rfl⟩ := hrange y (X.basicOpen_le s hy)
    have := h q ((fromSpec_mem_basicOpen_iff U' q s).1 hy) (hIq q hyZ)
    exact ⟨fun hc => GlobalTheory.T.cartier_at_of_locally_principal Z U' q0 (this.1 (GlobalTheory.T.locally_principal_of_cartier_at Z U' q hc)),
      fun hc => GlobalTheory.T.cartier_at_of_locally_principal Z U' q (this.2 (GlobalTheory.T.locally_principal_of_cartier_at Z U' q0 hc))⟩
  have hC : IsClosed (Z.support : Set X) := Z.support.isClosed
  refine ⟨isClosed_of_locally_iff hC _ key, isClosed_of_locally_iff hC _ fun x hx => ?_⟩
  obtain ⟨V, hV, hxV, hy⟩ := key x hx
  exact ⟨V, hV, hxV, fun y hyV hyC => not_congr (hy y hyV hyC)⟩

end GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsClosedCartierLocusSupportStatement
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosed_cartier_locus_support : ∀ {k : Type} [Field k] {X : Scheme.{0}} (g : X ⟶ Sp k) (Z : X.IdealSheafData), Smooth g → IsIntegral X → Smooth (Z.subschemeι ≫ g) → IsClosed {x : X | x ∈ Z.support ∧ CartAt Z x} ∧ IsClosed {x : X | x ∈ Z.support ∧ ¬ CartAt Z x} := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.isClosed_cartAt | exact GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.isClosed_cartAt | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.isClosed_cartAt <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.CartierAtOfNotMemSupport
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.CartierAtOfNotMemSupport
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

namespace GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

theorem cartAt_of_notMem_support {X : Scheme.{0}} (J : X.IdealSheafData) (x : X) (hx : x ∉ J.support) :
    CartAt J x := by
  rw [Scheme.IdealSheafData.mem_support_iff] at hx
  push_neg at hx
  obtain ⟨U, hU⟩ := hx
  rw [Scheme.mem_zeroLocus_iff] at hU
  push_neg at hU
  obtain ⟨f, hf, hxf⟩ := hU
  refine ⟨X.affineBasicOpen f, 1, hxf, Submonoid.one_mem _, ?_⟩
  rw [Ideal.span_singleton_one, ← J.map_ideal_basicOpen U f]
  exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hf)
    (X.toRingedSpace.isUnit_res_basicOpen f)

end GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.CartierAtOfNotMemSupportStatement
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cartier_at_of_not_mem_support : ∀ {X : Scheme.{0}} (J : X.IdealSheafData) (x : X), x ∉ J.support → CartAt J x := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.cartAt_of_notMem_support | exact GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.cartAt_of_notMem_support | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.cartAt_of_notMem_support <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsIsoRestrictOfBlowupComp
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsIsoRestrictOfBlowupComp
noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace GlobalTheory.CompanionTheory.Principalise

theorem isIso_of_isIso_comp_of_dense_range {A P V : Scheme.{0}} (a : A ⟶ P) (b : P ⟶ V) [IsIso (a ≫ b)]
    [IsSeparated b] [IsReduced P] (hd : Dense (Set.range a)) : IsIso b ∧ IsIso a := by
  obtain ⟨σ, hσdef⟩ : ∃ σ : V ⟶ P, σ = inv (a ≫ b) ≫ a := ⟨_, rfl⟩
  have hσ : σ ≫ b = 𝟙 V := by simp [hσdef]
  have haσ : (a ≫ b) ≫ σ = a := by simp [hσdef]
  have hid : IsIso (σ ≫ b) := by rw [hσ]; infer_instance
  have : IsClosedImmersion (σ ≫ b) := by rw [hσ]; infer_instance
  have : IsClosedImmersion σ := IsClosedImmersion.of_comp σ b
  have hr : Set.range a ⊆ Set.range σ := by
    rintro _ ⟨x, rfl⟩
    exact ⟨(a ≫ b) x, by rw [← Scheme.Hom.comp_apply, haσ]⟩
  have hcl : IsClosed (Set.range σ) := σ.isClosedEmbedding.isClosed_range
  have : Surjective σ := ⟨Set.range_eq_univ.1 (by
    have h := (hd.mono hr).closure_eq
    rwa [hcl.closure_eq] at h)⟩
  have : IsIso σ := isIso_of_isClosedImmersion_of_surjective σ
  have hb : IsIso b := IsIso.of_isIso_comp_left σ b
  exact ⟨hb, IsIso.of_isIso_comp_right a b⟩

theorem isEmpty_of_effCartier_bot {W : Scheme.{0}} (h : FinalTheorems.EffCartier (⊥ : W.IdealSheafData)) : IsEmpty W := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, f, hx, hf, e⟩ := h x
  have hf0 : f = 0 := by
    have : f ∈ (⊥ : W.IdealSheafData).ideal U := e ▸ Ideal.mem_span_singleton_self f
    simpa using this
  have : Nonempty U.1 := ⟨⟨x, hx⟩⟩
  exact nonZeroDivisors.ne_zero hf hf0

theorem dense_range_restrict_of_blowup {X₁ X₂ : Scheme.{0}} [IsIntegral X₁] [Nonempty X₂] {π : X₂ ⟶ X₁}
    {Z : X₁.IdealSheafData} (hB : FinalTheorems.Blowup π Z) (U : X₁.Opens) : Dense (Set.range (π ∣_ U)) := by
  have hZ : Z ≠ ⊥ := by
    rintro rfl
    have h := hB.1
    rw [Scheme.IdealSheafData.comap_bot] at h
    exact (isEmpty_of_effCartier_bot h).false (Nonempty.some inferInstance)
  have hO := GlobalTheory.Principalise.nonempty_compl_support hZ
  have hiso : IsIso (π ∣_ Z.support.compl) :=
    GlobalTheory.Principalise.isIso_restrict_of_blowup hB _ fun x hx => hx
  have hdO : Dense (Z.support.compl : Set X₁) := Z.support.compl.isOpen.dense hO
  have hdU : Dense (U.ι ⁻¹' (Z.support.compl : Set X₁)) := hdO.preimage U.ι.isOpenMap
  refine hdU.mono fun x hx => ?_
  obtain ⟨y, hy⟩ := (π ∣_ Z.support.compl).surjective ⟨x.1, hx⟩
  have hw : π y.1 = x.1 := by
    have := morphismRestrict_base_coe π Z.support.compl y
    rw [hy] at this
    exact this.symm
  refine ⟨⟨y.1, show π y.1 ∈ U by rw [hw]; exact x.2⟩, Subtype.ext ?_⟩
  exact (morphismRestrict_base_coe π U ⟨y.1, _⟩).trans hw

theorem isIso_restrict_of_isIso_restrict_comp_blowup : ∀ {X X₁ X₂ : Scheme.{0}} (s : X₁ ⟶ X) (π : X₂ ⟶ X₁)
    (Z : X₁.IdealSheafData) (V : X.Opens), IsIntegral X₁ → IsSeparated s → FinalTheorems.Blowup π Z → Nonempty X₂ →
    IsIso ((π ≫ s) ∣_ V) → IsIso (s ∣_ V) ∧ IsIso (π ∣_ (s ⁻¹ᵁ V)) := by
  intro X X₁ X₂ s π Z V hX hs hB hne he
  have he' : IsIso (π ∣_ (s ⁻¹ᵁ V) ≫ s ∣_ V) := by
    rw [← morphismRestrict_comp]
    exact he
  exact isIso_of_isIso_comp_of_dense_range (π ∣_ (s ⁻¹ᵁ V)) (s ∣_ V) (dense_range_restrict_of_blowup hB _)

end GlobalTheory.CompanionTheory.Principalise
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsIsoRestrictOfBlowupCompStatement
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIso_restrict_of_blowup_comp : ∀ {X X₁ X₂ : Scheme.{0}} (s : X₁ ⟶ X) (π : X₂ ⟶ X₁) (Z : X₁.IdealSheafData) (V : X.Opens), IsIntegral X₁ → IsSeparated s → FinalTheorems.Blowup π Z → Nonempty X₂ → IsIso ((π ≫ s) ∣_ V) → IsIso (s ∣_ V) ∧ IsIso (π ∣_ (s ⁻¹ᵁ V)) := by
  first | exact @GlobalTheory.CompanionTheory.Principalise.isIso_restrict_of_isIso_restrict_comp_blowup | exact GlobalTheory.CompanionTheory.Principalise.isIso_restrict_of_isIso_restrict_comp_blowup | (intros; apply GlobalTheory.CompanionTheory.Principalise.isIso_restrict_of_isIso_restrict_comp_blowup <;> assumption)
end
end

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

open GlobalTheory.CompanionTheory.Hypotheses₂.SncBlowup GlobalTheory.CompanionTheory.Hypotheses₂.ResKSide GlobalTheory.CompanionTheory.Hypotheses₂.Resolution

theorem exists_centre_off {k : Type} [Field k] {X₁ X₂ : Scheme.{0}} (g : X₁ ⟶ Sp k) (Z : X₁.IdealSheafData) (π : X₂ ⟶ X₁)
    (V : X₁.Opens) (h₀ : Smooth g) (h₁ : IsIntegral X₁) (h₂ : Smooth (Z.subschemeι ≫ g)) (h₃ : FinalTheorems.Blowup π Z)
    (h₄ : IsIso (π ∣_ V)) :
    ∃ Z' : X₁.IdealSheafData, Smooth (Z'.subschemeι ≫ g) ∧ (Z'.support : Set X₁) ⊆ (V : Set X₁)ᶜ ∧
      FinalTheorems.Blowup π Z' := by
  obtain ⟨hB, hA⟩ := GlobalTheory.T.isClosed_cartier_locus_support g Z h₀ h₁ h₂
  let A : Closeds X₁ := ⟨_, hA⟩
  let O₁ : X₁.Opens := ⟨_, hB.isOpen_compl⟩
  let O₂ : X₁.Opens := ⟨_, hA.isOpen_compl⟩
  have hO₁ : (O₁ : Set X₁) = ((Z.support : Set X₁) \ A)ᶜ := by
    ext x
    change ¬ (x ∈ Z.support ∧ CartAt Z x) ↔ ¬ (x ∈ Z.support ∧ ¬ (x ∈ Z.support ∧ ¬ CartAt Z x))
    tauto
  obtain ⟨c₁, c₂⟩ := GlobalTheory.T.vanishing_ideal_smooth_agrees_off g Z A O₁ h₂ (fun x hx => hx.1) hO₁
  have hV : FinalTheorems.EffCartier (Z.comap V.ι) := GlobalTheory.effCartier_comap_of_isIso_restrict π Z V h₄ h₃.1
  have hsupp : ((Scheme.IdealSheafData.vanishingIdeal A).support : Set X₁) = A :=
    Scheme.IdealSheafData.coe_support_vanishingIdeal A
  refine ⟨_, c₁, ?_, GlobalTheory.T.blowup_of_agreeing_ideal_cartier π Z _ O₁ O₂ h₃ ?_ c₂ ?_ ?_⟩
  · rw [hsupp]
    intro x hx hxV
    exact hx.2 ((GlobalTheory.T.effCartier_restrict_iff_cartier_at Z V).1 hV x hxV)
  · refine top_le_iff.1 fun x _ => ?_
    by_cases hx : x ∈ Z.support ∧ CartAt Z x
    · exact Or.inr fun h => h.2 hx.2
    · exact Or.inl hx
  · intro x hx hx'
    rw [← SetLike.mem_coe, hsupp] at hx'
    exact hx hx'
  · refine (GlobalTheory.T.effCartier_restrict_iff_cartier_at Z O₂).2 fun x hx => ?_
    by_contra hc
    exact hx ⟨by_contra fun h => hc (GlobalTheory.T.cartier_at_of_not_mem_support Z x h), hc⟩

theorem isIntegral_of_seq {k : Type} [Field k] {X X' : Scheme.{0}} {g : X ⟶ Sp k} {E : Closeds X} {s : X' ⟶ X}
    {E' : Closeds X'} (h : IsSncBlowupSeq g E s E') (hX : IsIntegral X) :
    Nonempty X' → Smooth (s ≫ g) → IsIntegral X' := by
  induction h with
  | id => exact fun _ _ => hX
  | @step X₁ X₂ s E₁ Z π h₁ h₂ h₃ h₄ h₅ ih =>
    intro hn hsm
    have : Nonempty X₁ := ⟨π hn.some⟩
    exact GlobalTheory.T.isIntegral_blowup_of_smooth (s ≫ g) Z π (ih this h₂) h₅ (by simpa using hsm) hn

theorem seq_of_iso {k : Type} [Field k] {X X' : Scheme.{0}} {g : X ⟶ Sp k} {E : Closeds X} {s : X' ⟶ X}
    {E' : Closeds X'} (h : IsSncBlowupSeq g E s E') (hX : IsIntegral X) (hg : IsProjOver g) :
    Nonempty X' → ∀ V : X.Opens, IsIso (s ∣_ V) → IsSmoothBlowupSeq g (V : Set X)ᶜ s := by
  induction h with
  | id => exact fun _ _ _ => .id
  | @step X₁ X₂ s E₁ Z π h₁ h₂ h₃ h₄ h₅ ih =>
    intro hn V hV
    have : Nonempty X₁ := ⟨π hn.some⟩
    have hi : IsIntegral X₁ := isIntegral_of_seq h₁ hX this h₂
    have hp : IsProjOver (s ≫ g) :=
      (Resolution.IsBlowupSeq.of_smooth h₁.isSmoothBlowupSeq).isProjOver hg
    have hP : IsProper (s ≫ g) := isProper_of_isProjOver hp
    have hs : IsSeparated s := IsSeparated.of_comp s g
    obtain ⟨a, b⟩ := GlobalTheory.T.isIso_restrict_of_blowup_comp s π Z V hi hs h₅ hn hV
    obtain ⟨Z', c₁, c₂, c₃⟩ := exists_centre_off (s ≫ g) Z π (s ⁻¹ᵁ V) h₂ hi h₃ h₅ b
    exact .step Z' π (ih this V a) c₁ c₂ c₃

end GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

namespace GlobalTheory.CompanionTheory.Hypotheses₂


end GlobalTheory.CompanionTheory.Hypotheses₂
