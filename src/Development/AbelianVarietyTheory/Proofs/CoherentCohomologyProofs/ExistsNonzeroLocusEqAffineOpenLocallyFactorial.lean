module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.DimEqZero
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.CoeNonzeroLocusCanonicalEqComplRange

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsPowMulMemRangeOfLocalDenominators
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory

theorem exists_dvd_pow_of_forall_prime_dvd {A : Type} [CommRing A] [IsDomain A]
    [UniqueFactorizationMonoid A] (a y : A) :
    y ≠ 0 → (∀ q, Prime q → q ∣ y → q ∣ a) → ∃ n : ℕ, y ∣ a ^ n := by
  refine UniqueFactorizationMonoid.induction_on_prime y ?_ ?_ ?_
  · intro h; exact absurd rfl h
  · intro u hu _ _; exact ⟨0, hu.dvd⟩
  · intro z p hz hp ih _ h
    obtain ⟨n, hn⟩ := ih hz fun q hq hqz => h q hq (hqz.mul_left p)
    exact ⟨n + 1, by rw [pow_succ']; exact mul_dvd_mul (h p hp (dvd_mul_right _ _)) hn⟩

theorem exists_pow_mul_mem_range_of_local_denominators {A B : Type} [CommRing A] [IsDomain A]
    [UniqueFactorizationMonoid A] [CommRing B] [IsDomain B] (φ : A →+* B)
    (hφ : Function.Injective φ) (W : Set (PrimeSpectrum A)) (hW : W.Nonempty) (a : A)
    (ha : ∀ (q : A) (p : PrimeSpectrum A), Prime q → p.asIdeal = Ideal.span {q} → p ∉ W → q ∣ a)
    (v : B) (hv : ∀ p ∈ W, ∃ s, s ∉ p.asIdeal ∧ ∃ x, φ x = φ s * v) :
    ∃ (n : ℕ) (x : A), φ x = φ a ^ n * v := by
  obtain ⟨p₀, hp₀⟩ := hW
  obtain ⟨s, hs, x, e⟩ := hv p₀ hp₀
  have hs0 : s ≠ 0 := fun h => hs (h ▸ p₀.asIdeal.zero_mem)
  obtain ⟨y, x', c, hrel, rfl, rfl⟩ := UniqueFactorizationMonoid.exists_reduced_factors s hs0 x
  have hc : c ≠ 0 := left_ne_zero_of_mul hs0
  have hy : y ≠ 0 := right_ne_zero_of_mul hs0
  have e' : φ x' = φ y * v := by
    rw [map_mul, map_mul, _root_.mul_assoc] at e
    exact mul_left_cancel₀ ((map_ne_zero_iff _ hφ).mpr hc) e
  obtain ⟨n, z, hz⟩ := exists_dvd_pow_of_forall_prime_dvd a y hy fun q hq hqy => by
    refine ha q ⟨Ideal.span {q}, (Ideal.span_singleton_prime hq.ne_zero).2 hq⟩ hq rfl fun hm => ?_
    obtain ⟨t, ht, w, ew⟩ := hv _ hm
    refine ht (Ideal.mem_span_singleton.2 (hqy.trans (hrel.dvd_of_dvd_mul_right ⟨w, hφ ?_⟩)))
    rw [map_mul, map_mul, e', ew, mul_left_comm]
  refine ⟨n, z * x', ?_⟩
  rw [← map_pow, hz, map_mul, map_mul, e']
  ring

theorem exists_eq_basicOpen_of_isAffineOpen_of_uniqueFactorization :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [UniqueFactorizationMonoid A] (U : (Spec (CommRingCat.of A)).Opens), IsAffineOpen U → (U : Set (Spec (CommRingCat.of A))).Nonempty → ∃ a : A, U = PrimeSpectrum.basicOpen a := by
  classical
  intro A _ _ _ _ U hU hne
  have hloc : ∀ p : PrimeSpectrum A, p ∈ U → ∃ f : A,
      p ∈ PrimeSpectrum.basicOpen f ∧ PrimeSpectrum.basicOpen f ≤ U := by
    intro p hp
    obtain ⟨_, ⟨f, rfl⟩, h1, h2⟩ :=
      (PrimeSpectrum.isTopologicalBasis_basic_opens (R := A)).exists_subset_of_mem_open hp U.isOpen
    exact ⟨f, h1, h2⟩
  obtain ⟨p₀, hp₀⟩ := hne
  obtain ⟨f, hf, hfU⟩ := hloc p₀ hp₀
  have hf0 : f ≠ 0 := fun h => hf (h ▸ p₀.asIdeal.zero_mem)
  let a : A := ((UniqueFactorizationMonoid.factors f).filter fun q =>
    ∃ p : PrimeSpectrum A, p.asIdeal = Ideal.span {q} ∧ p ∉ U).prod
  have ha : ∀ (q : A) (p : PrimeSpectrum A), Prime q → p.asIdeal = Ideal.span {q} →
      p ∉ U → q ∣ a := by
    intro q p hq hp hpU
    have hqf : q ∣ f := by
      rw [← Ideal.mem_span_singleton, ← hp]
      by_contra h
      exact hpU (hfU h)
    obtain ⟨r, hr, hqr⟩ :=
      UniqueFactorizationMonoid.exists_mem_factors_of_dvd hf0 hq.irreducible hqf
    refine hqr.dvd.trans (Multiset.dvd_prod (Multiset.mem_filter.2 ⟨hr, p, ?_, hpU⟩))
    rw [hp]
    exact Ideal.span_singleton_eq_span_singleton.2 hqr
  refine ⟨a, le_antisymm ?_ ?_⟩
  · intro p hp hpa
    have := p.isPrime
    obtain ⟨q, hq, hqp⟩ := (Ideal.IsPrime.multiset_prod_mem_iff_exists_mem p.isPrime _).1 hpa
    obtain ⟨-, p', hp', hp'U⟩ := Multiset.mem_filter.1 hq
    obtain ⟨g, hg, hgU⟩ := hloc p hp
    refine hp'U (hgU fun h => hg ?_)
    have h' : g ∈ p'.asIdeal := h
    rw [hp'] at h'
    exact (Ideal.span_singleton_le_iff_mem _).2 hqp h'
  · have : Nonempty U := ⟨⟨_, hp₀⟩⟩
    have hinj := map_injective_of_isIntegral (Spec (CommRingCat.of A)) (homOfLE (le_top : U ≤ ⊤))
    let φ : CommRingCat.of A ⟶ Γ(Spec (CommRingCat.of A), U) :=
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
        (Spec (CommRingCat.of A)).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
    have hφ : Function.Injective φ :=
      hinj.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv).1
    have key : ∀ (v : Γ(Spec (CommRingCat.of A), U)) (p : PrimeSpectrum A), p ∈ U →
        ∃ s, s ∉ p.asIdeal ∧ ∃ a, φ a = φ s * v := by
      intro v p hp
      let x : Spec (CommRingCat.of A) := p
      obtain ⟨⟨a, s⟩, e⟩ := IsLocalization.surj (S := (Spec.structureSheaf A).presheaf.stalk p)
        p.asIdeal.primeCompl ((Spec (CommRingCat.of A)).presheaf.germ U x hp v)
      refine ⟨s, s.2, a, germ_injective_of_isIntegral _ x hp ?_⟩
      have hg : ∀ a : A, (Spec (CommRingCat.of A)).presheaf.germ U x hp (φ a) =
          algebraMap A ((Spec.structureSheaf A).presheaf.stalk p) a := by
        intro a
        exact ((Spec (CommRingCat.of A)).presheaf.germ_res_apply (homOfLE (le_top : U ≤ ⊤)) x hp
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)).trans rfl
      rw [map_mul, hg, hg]
      exact e.symm.trans (mul_comm _ _)
    have key2 : ∀ v : Γ(Spec (CommRingCat.of A), U), ∃ (n : ℕ) (x : A), φ x = φ a ^ n * v :=
      fun v => exists_pow_mul_mem_range_of_local_denominators φ.hom hφ
        (U : Set (Spec (CommRingCat.of A))) ⟨p₀, hp₀⟩ a ha v (key v)
    intro p hpa
    by_contra hpU
    have hspan : Ideal.span (φ '' {g : A | PrimeSpectrum.basicOpen g ≤ U}) = ⊤ := by
      rw [← hU.self_le_iSup_basicOpen_iff]
      intro x hx
      obtain ⟨g, hg, hgU⟩ := hloc x hx
      refine TopologicalSpace.Opens.mem_iSup.2 ⟨⟨φ g, g, hgU, rfl⟩, ?_⟩
      have e : (Spec (CommRingCat.of A)).basicOpen (φ g) = U ⊓ PrimeSpectrum.basicOpen g := by
        rw [← basicOpen_eq_of_affine (R := CommRingCat.of A) g]
        exact Scheme.basicOpen_res _ _ (homOfLE (le_top : U ≤ ⊤)).op
      show x ∈ (Spec (CommRingCat.of A)).basicOpen (φ g)
      rw [e]
      exact ⟨hx, hg⟩
    have hall : ∀ v ∈ Ideal.span (φ '' {g : A | PrimeSpectrum.basicOpen g ≤ U}),
        ∃ (n : ℕ) (x : A), x ∈ p.asIdeal ∧ φ x = φ a ^ n * v := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨g, hg, rfl⟩ := hv
        refine ⟨0, g, ?_, by simp⟩
        by_contra h
        exact hpU (hg h)
      | zero => exact ⟨0, 0, p.asIdeal.zero_mem, by simp⟩
      | add v w _ _ hv hw =>
        obtain ⟨n, x, hx, e⟩ := hv
        obtain ⟨m, y, hy, e'⟩ := hw
        refine ⟨n + m, a ^ m * x + a ^ n * y,
          p.asIdeal.add_mem (p.asIdeal.mul_mem_left _ hx) (p.asIdeal.mul_mem_left _ hy), ?_⟩
        rw [map_add (f := _), map_mul, map_mul, map_pow, map_pow, e, e']
        ring
      | smul c v _ hv =>
        obtain ⟨n, x, hx, e⟩ := hv
        obtain ⟨m, y, e'⟩ := key2 c
        refine ⟨n + m, y * x, p.asIdeal.mul_mem_left _ hx, ?_⟩
        rw [map_mul, e, e', smul_eq_mul]
        ring
    obtain ⟨n, x, hx, e⟩ := hall 1 (hspan ▸ Submodule.mem_top)
    rw [_root_.mul_one, ← map_pow] at e
    rw [hφ e] at hx
    exact hpa (p.isPrime.mem_of_pow_mem n hx)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsNonzeroLocusEqAffineOpenLocallyFactorial
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.AffineComplement

open ReciprocityTheory.AnForm.R

theorem effCartier_of_stalkId_of_isLocallyNoetherian {W : Scheme.{0}} [IsLocallyNoetherian W]
    (G : W.IdealSheafData)
    (hG : ∀ x : W, ∃ t ∈ nonZeroDivisors (W.presheaf.stalk x), FinalTheorems.stalkId G x = Ideal.span {t}) :
    FinalTheorems.EffCartier G := by
  intro x
  obtain ⟨t, htnzd, ht⟩ := hG x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    W.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let U' : W.affineOpens := ⟨U, hU⟩
  have hx : x ∈ U'.1 := hxU
  rw [ds_stalkId_eq_map G U' x hx] at ht
  haveI : IsNoetherianRing Γ(W, U) := IsLocallyNoetherian.component_noetherian U'
  letI : Algebra Γ(W, U) (W.presheaf.stalk x) := W.presheaf.algebra_section_stalk ⟨x, hx⟩
  haveI := hU.isLocalization_stalk ⟨x, hx⟩
  have halg : algebraMap Γ(W, U) (W.presheaf.stalk x) = (W.presheaf.germ U x hx).hom := rfl
  rw [Ideal.map] at ht
  obtain ⟨y, ⟨a, haI, rfl⟩, c, hc⟩ := ds_gen_of_span _ t htnzd ht
  have hmap : (G.ideal U').map (algebraMap Γ(W, U) (W.presheaf.stalk x)) =
      Ideal.span {algebraMap Γ(W, U) (W.presheaf.stalk x) a} := by
    rw [halg, Ideal.map, ht, hc, Ideal.span_singleton_mul_left_unit c.isUnit]
  have hnzd : algebraMap Γ(W, U) (W.presheaf.stalk x) a ∈ nonZeroDivisors (W.presheaf.stalk x) := by
    rw [halg, hc]
    exact mul_mem (IsUnit.mem_nonZeroDivisors c.isUnit) htnzd
  obtain ⟨σ, hσP, hT⟩ := ds_spread (hU.primeIdealOf ⟨x, hx⟩).asIdeal (G.ideal U') a haI hmap hnzd
  haveI := hU.isLocalization_basicOpen σ
  obtain ⟨h1, h2⟩ := hT Γ(W, W.basicOpen σ)
  refine ⟨W.affineBasicOpen (U := U') σ, algebraMap Γ(W, U) Γ(W, W.basicOpen σ) a, ?_, h2, ?_⟩
  · show x ∈ W.basicOpen σ
    rw [W.mem_basicOpen σ x hx]
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (W.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal σ).2 hσP
  · rw [← G.map_ideal_basicOpen U' σ]
    exact h1

theorem exists_radical_span_singleton_eq {A : Type} [CommRing A] [IsDomain A]
    [UniqueFactorizationMonoid A] {a : A} (ha : a ≠ 0) :
    ∃ t ∈ nonZeroDivisors A, (Ideal.span {a}).radical = Ideal.span {t} := by
  obtain ⟨y, n, hy, hya, hay⟩ := exists_squarefree_dvd_pow_of_ne_zero ha
  refine ⟨y, mem_nonZeroDivisors_of_ne_zero hy.ne_zero, le_antisymm ?_ ?_⟩
  · rw [← (isRadical_iff_span_singleton.1 hy.isRadical).radical]
    exact Ideal.radical_mono (Ideal.span_singleton_le_span_singleton.2 hya)
  · rw [Ideal.span_singleton_le_iff_mem]
    exact ⟨n, Ideal.mem_span_singleton.2 hay⟩

theorem stalkId_vanishingIdeal_compl {X : Scheme.{0}} (U : X.Opens) (x : X)
    (a : X.presheaf.stalk x)
    (h : ∀ q : PrimeSpectrum (X.presheaf.stalk x), X.fromSpecStalk x q ∈ U ↔ a ∉ q.asIdeal) :
    FinalTheorems.stalkId (Scheme.IdealSheafData.vanishingIdeal U.compl) x = (Ideal.span {a}).radical := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hx, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  rw [ds_stalkId_eq_map _ ⟨W, hW⟩ x hx, Scheme.IdealSheafData.vanishingIdeal_ideal]
  letI : Algebra Γ(X, W) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  haveI := hW.isLocalization_stalk ⟨x, hx⟩
  have hcl : IsClosed (X := PrimeSpectrum Γ(X, W)) (hW.fromSpec ⁻¹' (U.compl : Set X)) :=
    U.compl.isClosed.preimage hW.fromSpec.continuous
  generalize hJ : PrimeSpectrum.vanishingIdeal (R := Γ(X, W)) (hW.fromSpec ⁻¹' (U.compl : Set X)) = J
  have hz : PrimeSpectrum.zeroLocus (J : Set Γ(X, W)) = hW.fromSpec ⁻¹' (U.compl : Set X) := by
    rw [← hJ, PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hcl.closure_eq]
    rfl
  have hr : J.radical = J := hJ ▸ (PrimeSpectrum.isRadical_vanishingIdeal _).radical
  change J.map (algebraMap Γ(X, W) (X.presheaf.stalk x)) = _
  rw [← hr, IsLocalization.map_radical (hW.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl,
    ← PrimeSpectrum.zeroLocus_eq_iff]
  ext q
  have e : X.fromSpecStalk x q =
      hW.fromSpec (PrimeSpectrum.comap (algebraMap Γ(X, W) (X.presheaf.stalk x)) q) := by
    rw [← hW.fromSpecStalk_eq_fromSpecStalk hx]
    rfl
  rw [PrimeSpectrum.mem_zeroLocus, PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe,
    SetLike.coe_subset_coe, Ideal.map_le_iff_le_comap, Ideal.span_singleton_le_iff_mem,
    ← not_iff_not, ← h, e]
  have := Set.ext_iff.1 hz (PrimeSpectrum.comap (algebraMap Γ(X, W) (X.presheaf.stalk x)) q)
  exact (not_congr this).trans not_not

theorem exists_nonzeroLocus_eq : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [X.IsSeparated] (U : X.Opens), IsAffineOpen U → (U : Set X).Nonempty → (∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) → ∃ (L : LB X) (σ : LB.Sec L), L.IsLB ∧ nonzeroLocus σ = U := by
  intro X _ _ _ U hU hne hufd
  have hι : IsAffineHom U.ι :=
    haveI : IsAffine U := hU
    haveI : IsAffineHom (U.ι ≫ terminal.from X) := inferInstance
    IsAffineHom.of_comp _ (terminal.from X)
  have hE : FinalTheorems.EffCartier (Scheme.IdealSheafData.vanishingIdeal U.compl) := by
    refine effCartier_of_stalkId_of_isLocallyNoetherian _ fun x => ?_
    haveI := hufd x
    have hd : IsDomain (X.presheaf.stalk x) := inferInstance
    have hn : IsNoetherianRing (X.presheaf.stalk x) := inferInstance
    have hA : IsAffineOpen (X.fromSpecStalk x ⁻¹ᵁ U) := by
      have : IsAffineHom (X.fromSpecStalk x ⁻¹ᵁ U).ι :=
        MorphismProperty.of_isPullback (P := @IsAffineHom)
          (isPullback_morphismRestrict (X.fromSpecStalk x) U) hι
      exact isAffine_of_isAffineHom (X.fromSpecStalk x ⁻¹ᵁ U).ι
    have hg : genericPoint X ∈ Set.range (X.fromSpecStalk x) := by
      rw [Scheme.range_fromSpecStalk]
      exact (genericPoint_spec X).specializes trivial
    obtain ⟨q, hq⟩ := hg
    have hqU : q ∈ X.fromSpecStalk x ⁻¹ᵁ U := by
      change X.fromSpecStalk x q ∈ U
      rw [hq]
      exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).2 (by simpa using hne)
    obtain ⟨a, ha⟩ := @GlobalTheory.exists_eq_basicOpen_of_isAffineOpen_of_uniqueFactorization (X.presheaf.stalk x) (X.presheaf.stalk x).commRing hd hn (hufd x)
      (X.fromSpecStalk x ⁻¹ᵁ U) hA ⟨q, hqU⟩
    have h : ∀ q : PrimeSpectrum (X.presheaf.stalk x),
        X.fromSpecStalk x q ∈ U ↔ a ∉ q.asIdeal := fun q =>
      iff_of_eq (congrArg (fun V => q ∈ V) ha)
    have ha0 : a ≠ 0 := fun h0 => (h q).1 hqU (h0 ▸ zero_mem _)
    rw [stalkId_vanishingIdeal_compl U x a h]
    exact exists_radical_span_singleton_eq ha0
  obtain ⟨D, hD⟩ := EffCartierData.exists_idealSheaf_eq hE
  refine ⟨D.lb, D.canonical, D.isLB_lb, TopologicalSpace.Opens.ext ?_⟩
  refine D.coe_nonzeroLocus_canonical.trans ?_
  rw [hD]
  exact compl_compl _

end GlobalTheory.AffineComplement
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsNonzeroLocusEqAffineOpenLocallyFactorialStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
theorem _root_.GlobalTheory.T.exists_nonzeroLocus_eq_affineOpen_locallyFactorial : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [X.IsSeparated] (U : X.Opens), IsAffineOpen U → (U : Set X).Nonempty → (∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) → ∃ (L : LB X) (σ : LB.Sec L), L.IsLB ∧ nonzeroLocus σ = U := by
  first | exact @GlobalTheory.AffineComplement.exists_nonzeroLocus_eq | exact GlobalTheory.AffineComplement.exists_nonzeroLocus_eq | (intros; apply GlobalTheory.AffineComplement.exists_nonzeroLocus_eq <;> assumption)
end
