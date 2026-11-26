module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
open TensorProduct AlgebraicGeometry

universe u

namespace GlobalTheory

theorem isDomain_and_isIntegrallyClosed_atPrime_of_isLocalization {B : Type*} [CommRing B]
    (M : Submonoid B) (T : Type*) [CommRing T] [Algebra B T] [IsLocalization M T]
    (p : Ideal B) [hp : p.IsPrime] (hM : Disjoint (M : Set B) (p : Set B))
    (h : ∀ (q : Ideal T) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q))
    (Bp : Type*) [CommRing Bp] [Algebra B Bp] [IsLocalization.AtPrime Bp p] :
    IsDomain Bp ∧ IsIntegrallyClosed Bp := by
  have hq : (p.map (algebraMap B T)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M T p hp hM
  have hc : (p.map (algebraMap B T)).comap (algebraMap B T) = p :=
    IsLocalization.under_map_of_isPrime_disjoint M T hp hM
  have h1 := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
    (Localization.AtPrime (p.map (algebraMap B T))) (p.map (algebraMap B T))
  have h2 : IsLocalization p.primeCompl (Localization.AtPrime (p.map (algebraMap B T))) := by
    convert h1 using 1
    ext x
    simp [Ideal.primeCompl, hc]
  obtain ⟨h3, h4⟩ := h (p.map (algebraMap B T))
  let e : Localization.AtPrime (p.map (algebraMap B T)) ≃ₐ[B] Bp :=
    IsLocalization.algEquiv p.primeCompl _ _
  exact ⟨e.symm.injective.isDomain _, IsIntegrallyClosed.of_equiv e.toRingEquiv⟩

theorem isDomain_and_isIntegrallyClosed_atPrime_of_isDomain {B : Type*} [CommRing B] [IsDomain B]
    [IsIntegrallyClosed B] (p : Ideal B) [hp : p.IsPrime]
    (Bp : Type*) [CommRing Bp] [Algebra B Bp] [IsLocalization.AtPrime Bp p] :
    IsDomain Bp ∧ IsIntegrallyClosed Bp :=
  ⟨IsLocalization.isDomain_of_le_nonZeroDivisors Bp p.primeCompl_le_nonZeroDivisors,
    isIntegrallyClosed_of_isLocalization Bp p.primeCompl p.primeCompl_le_nonZeroDivisors⟩

theorem isDomain_and_isIntegrallyClosed_atPrime_of_isIntegrallyClosedIn_pi {B : Type*} [CommRing B]
    {ι : Type*} [Finite ι] (K : ι → Type*) [∀ i, Field (K i)] [Algebra B (Π i, K i)]
    [hB : IsIntegrallyClosedIn B (Π i, K i)] (p : Ideal B) [hp : p.IsPrime]
    (Bp : Type*) [CommRing Bp] [Algebra B Bp] [IsLocalization.AtPrime Bp p] :
    IsDomain Bp ∧ IsIntegrallyClosed Bp := by
  classical
  have := Fintype.ofFinite ι
  have hinj : Function.Injective (algebraMap B (Π i, K i)) := (isIntegrallyClosedIn_iff.mp hB).1
  let φ (i : ι) : B →+* K i := (Pi.evalRingHom K i).comp (algebraMap B (Π i, K i))
  have key (i : ι) (x : K i) (hx : (φ i).IsIntegralElem x) :
      ∃ b : B, algebraMap B (Π i, K i) b = Pi.single i x := by
    apply IsIntegrallyClosedIn.algebraMap_eq_of_integral
    obtain ⟨f, hf, hfx⟩ := hx
    refine ⟨Polynomial.X * f, Polynomial.monic_X.mul hf, ?_⟩
    rw [Polynomial.eval₂_mul, Polynomial.eval₂_X]
    funext j
    by_cases hj : j = i
    · subst hj
      have : (Polynomial.eval₂ (algebraMap B (Π i, K i)) (Pi.single j x) f) j = 0 := by
        have := Polynomial.hom_eval₂ f (algebraMap B (Π i, K i)) (Pi.evalRingHom K j)
          (Pi.single j x)
        simpa [φ] using this.trans (by simpa [φ] using hfx)
      simp [this]
    · simp [hj]
  choose e he using fun i ↦ key i 1 (RingHom.isIntegralElem_one _)
  have hsum : ∑ i, e i = 1 := by
    apply hinj
    simp [he, Finset.univ_sum_single, ← Pi.one_def]
  obtain ⟨i, hi⟩ : ∃ i, e i ∉ p := by
    by_contra! H
    exact hp.ne_top ((Ideal.eq_top_iff_one _).mpr (hsum ▸ p.sum_mem fun i _ ↦ H i))
  let D := (φ i).range
  letI : Algebra B D := (φ i).rangeRestrict.toAlgebra
  have hsurj : Function.Surjective (algebraMap B D) := (φ i).rangeRestrict_surjective
  have hidem : IsIdempotentElem (e i) := by
    apply hinj
    simp [he, ← Pi.single_mul]
  have : IsLocalization.Away (e i) D := by
    refine IsLocalization.away_of_isIdempotentElem_of_mul hidem (fun x y ↦ ?_) hsurj
    rw [Subtype.ext_iff, ← hinj.eq_iff, map_mul, map_mul, he]
    change algebraMap B (Π i, K i) x i = algebraMap B (Π i, K i) y i ↔ _
    refine ⟨fun h ↦ funext fun j ↦ ?_, fun h ↦ by simpa using congrFun h i⟩
    by_cases hj : j = i
    · subst hj
      simp [h]
    · simp [hj]
  have : IsIntegrallyClosedIn D (K i) := by
    rw [Subring.isIntegrallyClosedIn_iff]
    intro x hx
    letI : Algebra B (K i) := (φ i).toAlgebra
    have : IsScalarTower B D (K i) := .of_algebraMap_eq fun _ ↦ rfl
    have : Algebra.IsIntegral B D := Algebra.isIntegral_of_surjective hsurj
    obtain ⟨b, hb⟩ := key i x (isIntegral_trans x hx)
    exact ⟨b, by simp [φ, hb]⟩
  have : IsIntegrallyClosed D := IsIntegrallyClosed.of_isIntegrallyClosedIn D (K i)
  refine isDomain_and_isIntegrallyClosed_atPrime_of_isLocalization (.powers (e i)) D p ?_
    (fun q _ ↦ isDomain_and_isIntegrallyClosed_atPrime_of_isDomain q _) Bp
  rwa [Ideal.disjoint_powers_iff_notMem_of_isPrime]

theorem isIntegrallyClosedIn_tensor_of_smooth {A B L : Type*} [CommRing A] [CommRing B]
    [CommRing L] [Algebra A B] [Algebra A L] [Algebra.Smooth A B] [hL : IsIntegrallyClosedIn A L] :
    IsIntegrallyClosedIn B (B ⊗[A] L) := by
  obtain ⟨hinj, hcl⟩ := isIntegrallyClosedIn_iff.mp hL
  refine isIntegrallyClosedIn_iff.mpr ⟨?_, fun {x} hx ↦ ?_⟩
  · exact Algebra.TensorProduct.includeLeft_injective (S := A) hinj
  · obtain ⟨y, hy⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth
      (R := A) (S := B) (B := L)).2 ⟨x, hx⟩
    have hy' : Algebra.TensorProduct.map (.id B B) (integralClosure A L).val y = x :=
      congrArg Subtype.val hy
    subst hy'
    clear hx hy
    induction y with
    | add x y hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [map_add (f := _), map_add (f := _), ha, hb]⟩
    | tmul b y =>
      obtain ⟨a, ha⟩ := hcl y.2
      refine ⟨a • b, ?_⟩
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.algebraMap_apply,
        Subalgebra.coe_val, ← ha, Algebra.algebraMap_eq_smul_one a, ← TensorProduct.smul_tmul]
      rfl

theorem isIntegrallyClosed_mvPolynomial_fin (A : Type*) [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] (n : ℕ) : IsIntegrallyClosed (MvPolynomial (Fin n) A) := by
  induction n with
  | zero => exact IsIntegrallyClosed.of_equiv (MvPolynomial.isEmptyRingEquiv A (Fin 0)).symm
  | succ n ih => exact IsIntegrallyClosed.of_equiv (MvPolynomial.finSuccEquiv A n).symm.toRingEquiv

theorem isDomain_and_isIntegrallyClosed_atPrime_of_etale (A : Type*) {B : Type*} [CommRing A]
    [CommRing B] [IsDomain A] [IsIntegrallyClosed A] [Algebra A B] [Algebra.Etale A B]
    (p : Ideal B) [hp : p.IsPrime]
    (Bp : Type*) [CommRing Bp] [Algebra B Bp] [IsLocalization.AtPrime Bp p] :
    IsDomain Bp ∧ IsIntegrallyClosed Bp := by
  let L := FractionRing A
  have h1 : IsIntegrallyClosedIn B (B ⊗[A] L) := isIntegrallyClosedIn_tensor_of_smooth
  have := Algebra.FormallyUnramified.finite_of_free L (L ⊗[A] B)
  have := Algebra.FormallyUnramified.isReduced_of_field L (L ⊗[A] B)
  have : IsArtinianRing (L ⊗[A] B) := isArtinian_of_tower L inferInstance
  let e := (Algebra.TensorProduct.comm A B L).toRingEquiv
  have : IsArtinianRing (B ⊗[A] L) := e.symm.isArtinianRing
  have : IsReduced (B ⊗[A] L) := isReduced_of_injective e e.injective
  letI (m : MaximalSpectrum (B ⊗[A] L)) : Field ((B ⊗[A] L) ⧸ m.asIdeal) :=
    Ideal.Quotient.field m.asIdeal
  have := (((IsArtinianRing.equivPi (B ⊗[A] L)).restrictScalars B).isIntegrallyClosedIn).mp h1
  exact isDomain_and_isIntegrallyClosed_atPrime_of_isIntegrallyClosedIn_pi
    (fun m : MaximalSpectrum (B ⊗[A] L) ↦ (B ⊗[A] L) ⧸ m.asIdeal) p Bp

theorem isDomain_and_isIntegrallyClosed_atPrime_of_smooth (A : Type*) {B : Type*} [CommRing A]
    [CommRing B] [IsDomain A] [IsIntegrallyClosed A] [Algebra A B] [Algebra.Smooth A B]
    (p : Ideal B) [hp : p.IsPrime]
    (Bp : Type*) [CommRing Bp] [Algebra B Bp] [IsLocalization.AtPrime Bp p] :
    IsDomain Bp ∧ IsIntegrallyClosed Bp := by
  obtain ⟨f, hfm, n, _, _, _⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := A) (p := p)
  have := isIntegrallyClosed_mvPolynomial_fin A n
  refine isDomain_and_isIntegrallyClosed_atPrime_of_isLocalization (.powers f)
    (Localization.Away f) p ?_
    (fun q _ ↦ isDomain_and_isIntegrallyClosed_atPrime_of_etale (MvPolynomial (Fin n) A) q _) Bp
  rwa [Ideal.disjoint_powers_iff_notMem_of_isPrime]

theorem isDomain_and_isIntegrallyClosed_atPrime_of_smooth_of_comap {A B : Type*} [CommRing A]
    [CommRing B] [Algebra A B] [Algebra.Smooth A B] (p : Ideal B) [hp : p.IsPrime]
    (Ap : Type*) [CommRing Ap] [Algebra A Ap]
    [IsLocalization.AtPrime Ap (p.comap (algebraMap A B))] [IsDomain Ap] [IsIntegrallyClosed Ap]
    (Bp : Type*) [CommRing Bp] [Algebra B Bp] [IsLocalization.AtPrime Bp p] :
    IsDomain Bp ∧ IsIntegrallyClosed Bp := by
  let M := (p.comap (algebraMap A B)).primeCompl
  letI : Algebra B (Ap ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  have : IsLocalization (Algebra.algebraMapSubmonoid B M) (Ap ⊗[A] B) :=
    IsLocalization.tensorRight _ _
  refine isDomain_and_isIntegrallyClosed_atPrime_of_isLocalization
    (Algebra.algebraMapSubmonoid B M) (Ap ⊗[A] B) p ?_
    (fun q _ ↦ isDomain_and_isIntegrallyClosed_atPrime_of_smooth Ap q _) Bp
  rw [Set.disjoint_left]
  rintro _ ⟨a, ha, rfl⟩ h
  exact ha h

theorem isDomain_and_isIntegrallyClosed_atPrime_of_smooth_of_forall (A : Type*) {B : Type*}
    [CommRing A] [CommRing B] [Algebra A B] [Algebra.Smooth A B]
    (hA : ∀ (q : Ideal A) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q))
    (p : Ideal B) [hp : p.IsPrime]
    (Bp : Type*) [CommRing Bp] [Algebra B Bp] [IsLocalization.AtPrime Bp p] :
    IsDomain Bp ∧ IsIntegrallyClosed Bp := by
  obtain ⟨_, _⟩ := hA (p.comap (algebraMap A B))
  exact isDomain_and_isIntegrallyClosed_atPrime_of_smooth_of_comap (A := A) p
    (Localization.AtPrime (p.comap (algebraMap A B))) Bp

theorem isIntegrallyClosed_of_smooth (A B : Type*) [CommRing A] [CommRing B] [IsDomain A]
    [IsIntegrallyClosed A] [Algebra A B] [Algebra.Smooth A B] [IsDomain B] :
    IsIntegrallyClosed B :=
  IsIntegrallyClosed.of_localization_maximal fun p _ _ ↦
    (isDomain_and_isIntegrallyClosed_atPrime_of_smooth A p _).2

theorem isReduced_of_smooth_of_isIntegrallyClosed (A B : Type*) [CommRing A] [CommRing B]
    [IsDomain A] [IsIntegrallyClosed A] [Algebra A B] [Algebra.Smooth A B] : IsReduced B :=
  isReduced_ofLocalizationMaximal B fun p _ ↦
    have := (isDomain_and_isIntegrallyClosed_atPrime_of_smooth A p (Localization.AtPrime p)).1
    inferInstance

theorem isDomain_and_isIntegrallyClosed_stalk_of_smooth {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f]
    (x : X) [IsDomain (Y.presheaf.stalk (f x))] [IsIntegrallyClosed (Y.presheaf.stalk (f x))] :
    IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) := by
  obtain ⟨U, hU, V, hV, hx, e, -⟩ := Smooth.exists_isStandardSmooth f x
  have hs := f.smooth_appLE hU hV e
  algebraize [(f.appLE U V e).hom]
  letI := X.presheaf.algebra_section_stalk (⟨x, hx⟩ : V)
  letI := Y.presheaf.algebra_section_stalk (⟨f x, e hx⟩ : U)
  have h1 := hV.isLocalization_stalk ⟨x, hx⟩
  have h2 := hU.isLocalization_stalk ⟨f x, e hx⟩
  have h3 : (hV.primeIdealOf ⟨x, hx⟩).asIdeal.comap (algebraMap Γ(Y, U) Γ(X, V)) =
      (hU.primeIdealOf ⟨f x, e hx⟩).asIdeal :=
    congrArg PrimeSpectrum.asIdeal (IsAffineOpen.comap_primeIdealOf_appLE U hU V hV e hx)
  have h4 : IsLocalization.AtPrime (Y.presheaf.stalk (f x))
      ((hV.primeIdealOf ⟨x, hx⟩).asIdeal.comap (algebraMap Γ(Y, U) Γ(X, V))) := by
    convert h2
  exact isDomain_and_isIntegrallyClosed_atPrime_of_smooth_of_comap (A := Γ(Y, U))
    (hV.primeIdealOf ⟨x, hx⟩).asIdeal (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)

theorem forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Smooth f]
    (hY : ∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧ IsIntegrallyClosed (Y.presheaf.stalk y))
    (x : X) : IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) :=
  have := (hY (f x)).1
  have := (hY (f x)).2
  isDomain_and_isIntegrallyClosed_stalk_of_smooth f x

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsRingEquivOfIsTranscendenceBasis
open MvPolynomial Cardinal

namespace GlobalTheory.GaloisDescent

theorem _root_.GlobalTheory.GaloisDescent.exists_ringEquiv_of_isTranscendenceBasis {F F' L L' ι κ : Type*} [Field F] [Field F']
    [Field L] [Field L'] [Algebra F L] [Algebra F' L'] [IsAlgClosed L] [IsAlgClosed L']
    {v : ι → L} {w : κ → L'} (hv : IsTranscendenceBasis F v) (hw : IsTranscendenceBasis F' w)
    (e : MvPolynomial ι F ≃+* MvPolynomial κ F') :
    ∃ σ : L ≃+* L', ∀ p, σ (aeval v p) = aeval w (e p) := by
  letI : Algebra (MvPolynomial ι F) L := (aeval v).toRingHom.toAlgebra
  letI : Algebra (MvPolynomial κ F') L' := (aeval w).toRingHom.toAlgebra
  have : Module.IsTorsionFree (MvPolynomial ι F) L :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hv.1
  have : Module.IsTorsionFree (MvPolynomial κ F') L' :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hw.1
  have : IsAlgClosure (MvPolynomial ι F) L := by
    refine ⟨inferInstance, ?_⟩
    have := hv.isAlgebraic
    refine Algebra.IsAlgebraic.ringHom_of_comp_eq hv.1.aevalEquiv.symm (RingHom.id L)
      hv.1.aevalEquiv.symm.injective Function.surjective_id ?_
    ext a
    change aeval v (hv.1.aevalEquiv.symm a) = algebraMap _ L a
    rw [← hv.1.algebraMap_aevalEquiv, AlgEquiv.apply_symm_apply]
  have : IsAlgClosure (MvPolynomial κ F') L' := by
    refine ⟨inferInstance, ?_⟩
    have := hw.isAlgebraic
    refine Algebra.IsAlgebraic.ringHom_of_comp_eq hw.1.aevalEquiv.symm (RingHom.id L')
      hw.1.aevalEquiv.symm.injective Function.surjective_id ?_
    ext a
    change aeval w (hw.1.aevalEquiv.symm a) = algebraMap _ L' a
    rw [← hw.1.algebraMap_aevalEquiv, AlgEquiv.apply_symm_apply]
  exact ⟨IsAlgClosure.equivOfEquiv L L' e, fun p => IsAlgClosure.equivOfEquiv_algebraMap L L' e p⟩

theorem exists_ringEquiv_extend {F L : Type*} [Field F] [Field L] [Algebra F L] [IsAlgClosed L]
    (τ : F ≃+* F) : ∃ σ : L ≃+* L, ∀ a, σ (algebraMap F L a) = algebraMap F L (τ a) := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis F L
  obtain ⟨σ, hσ⟩ := exists_ringEquiv_of_isTranscendenceBasis hs hs (mapEquiv s τ)
  refine ⟨σ, fun a => ?_⟩
  simpa using hσ (C a)

theorem exists_algEquiv_extend {K F L : Type*} [Field K] [Field F] [Field L] [Algebra K F]
    [Algebra F L] [Algebra K L] [IsScalarTower K F L] [IsAlgClosed L]
    (τ : F ≃ₐ[K] F) : ∃ σ : L ≃ₐ[K] L, ∀ a, σ (algebraMap F L a) = algebraMap F L (τ a) := by
  obtain ⟨σ, hσ⟩ := exists_ringEquiv_extend (L := L) τ.toRingEquiv
  refine ⟨AlgEquiv.ofRingEquiv (f := σ) fun k => ?_, hσ⟩
  rw [IsScalarTower.algebraMap_apply K F L, hσ]
  congr 1
  exact τ.commutes k

theorem exists_algEquiv_apply_eq_add_one {K L : Type*} [Field K] [Field L] [Algebra K L]
    [IsAlgClosed L] {x : L} (hx : Transcendental K x) : ∃ σ : L ≃ₐ[K] L, σ x = x + 1 := by
  have h1 : AlgebraicIndepOn K id ({x} : Set L) :=
    algebraicIndependent_unique_type_iff.2 hx
  obtain ⟨s, hxs, hs⟩ := exists_isTranscendenceBasis_superset h1
  let e : MvPolynomial s K ≃ₐ[K] MvPolynomial s K :=
    AlgEquiv.ofAlgHom (aeval fun i => X i + 1) (aeval fun i => X i - 1)
      (by ext i : 1; simp) (by ext i : 1; simp)
  obtain ⟨σ, hσ⟩ := exists_ringEquiv_of_isTranscendenceBasis hs hs e.toRingEquiv
  refine ⟨AlgEquiv.ofRingEquiv (f := σ) fun k => ?_, ?_⟩
  · simpa [e] using hσ (C k)
  · simpa [e] using hσ (X ⟨x, hxs rfl⟩)

theorem _root_.GlobalTheory.GaloisDescent.mem_range_algebraMap_of_forall_algEquiv {K L : Type*} [Field K] [Field L] [Algebra K L]
    [PerfectField K] [IsAlgClosed L] (x : L) (hx : ∀ σ : L ≃ₐ[K] L, σ x = x) :
    x ∈ Set.range (algebraMap K L) := by
  by_cases halg : IsAlgebraic K x
  · have hxA : x ∈ algebraicClosure K L := mem_algebraicClosure_iff.2 halg
    have hfix : ∀ f : Gal(algebraicClosure K L/K), f ⟨x, hxA⟩ = ⟨x, hxA⟩ := by
      intro f
      obtain ⟨s, hs⟩ := exists_isTranscendenceBasis (algebraicClosure K L) L
      obtain ⟨τ, hτ⟩ := _root_.GlobalTheory.GaloisDescent.exists_ringEquiv_of_isTranscendenceBasis hs hs
        (MvPolynomial.mapEquiv s (f : algebraicClosure K L ≃+* algebraicClosure K L))
      have hτA : ∀ a : algebraicClosure K L, τ (a : L) = (f a : L) := fun a => by
        simpa using hτ (MvPolynomial.C a)
      let σ : L ≃ₐ[K] L := AlgEquiv.ofRingEquiv (f := τ) (fun k => by
        simpa using hτA (algebraMap K (algebraicClosure K L) k))
      apply Subtype.ext
      rw [← hτA]
      exact hx σ
    obtain ⟨k, hk⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed _).2 hfix
    exact ⟨k, congrArg Subtype.val hk⟩
  · classical
    have hind : AlgebraicIndepOn K id {x} :=
      (algebraicIndependent_singleton_iff (⟨x, rfl⟩ : ({x} : Set L))).2 halg
    obtain ⟨t, hxt, ht⟩ := exists_isTranscendenceBasis_superset hind
    let i : t := ⟨x, hxt rfl⟩
    let φ : MvPolynomial t K ≃ₐ[K] MvPolynomial t K := AlgEquiv.ofAlgHom
      (aeval fun j => if j = i then X j + 1 else X j) (aeval fun j => if j = i then X j - 1 else X j)
      (MvPolynomial.algHom_ext fun j => by by_cases h : j = i <;> simp [h])
      (MvPolynomial.algHom_ext fun j => by by_cases h : j = i <;> simp [h])
    obtain ⟨τ, hτ⟩ := _root_.GlobalTheory.GaloisDescent.exists_ringEquiv_of_isTranscendenceBasis ht ht φ.toRingEquiv
    have hτx : τ x = x + 1 := by simpa [φ, i] using hτ (X i)
    let σ : L ≃ₐ[K] L := AlgEquiv.ofRingEquiv (f := τ) (fun k => by simpa [φ] using hτ (C k))
    have h1 := hx σ
    have h2 : τ x = x := h1
    rw [hτx] at h2
    simp at h2

theorem _root_.GlobalTheory.GaloisDescent.complex_mem_range_of_forall_algEquiv {K : Type*} [Field K] [Algebra K ℂ] (x : ℂ)
    (hx : ∀ σ : ℂ ≃ₐ[K] ℂ, σ x = x) : x ∈ Set.range (algebraMap K ℂ) := by
  haveI : CharZero K := RingHom.charZero (algebraMap K ℂ)
  exact _root_.GlobalTheory.GaloisDescent.mem_range_algebraMap_of_forall_algEquiv x hx

theorem _root_.GlobalTheory.GaloisDescent.exists_complex_ringEquiv_comp_eq {K : Type} [Field K] [Countable K] (f g : K →+* ℂ) :
    ∃ σ : ℂ ≃+* ℂ, ∀ a, σ (f a) = g a := by
  have hK : Cardinal.mk K ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0
  have hC : Cardinal.aleph0 < Cardinal.mk ℂ := by
    rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum
  letI Af : Algebra K ℂ := f.toAlgebra
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis K ℂ
  have hsc := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ hs hK hC
  letI Ag : Algebra K ℂ := g.toAlgebra
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis K ℂ
  have htc := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ ht hK hC
  obtain ⟨eqv⟩ := Cardinal.eq.1 (hsc.symm.trans htc)
  obtain ⟨σ, hσ⟩ := @_root_.GlobalTheory.GaloisDescent.exists_ringEquiv_of_isTranscendenceBasis K K ℂ ℂ s t _ _ _ _ Af Ag _ _ _ _
    hs ht (MvPolynomial.renameEquiv K eqv).toRingEquiv
  refine ⟨σ, fun a => ?_⟩
  simpa [RingHom.algebraMap_toAlgebra] using hσ (MvPolynomial.C a)

end GlobalTheory.GaloisDescent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsVariableChangeEqLatticeCurve
open UpperHalfPlane ModularForm MatrixGroups Filter EisensteinSeries
open scoped Real Topology

noncomputable section

namespace GlobalTheory

def latticeCurve (L : PeriodPair) : WeierstrassCurve ℂ := ⟨0, 0, 0, -L.g₂ / 4, -L.g₃ / 4⟩

lemma latticeCurve_Δ (L : PeriodPair) : (latticeCurve L).Δ = L.g₂ ^ 3 - 27 * L.g₃ ^ 2 := by
  simp only [latticeCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

lemma latticeCurve_c₄ (L : PeriodPair) : (latticeCurve L).c₄ = 12 * L.g₂ := by
  simp only [latticeCurve, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  ring

def periodPairOfTau (τ : ℍ) : PeriodPair where
  ω₁ := τ
  ω₂ := 1
  indep := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have h1 := congrArg Complex.im h
    have h2 := congrArg Complex.re h
    simp [τ.im_ne_zero] at h1
    simp [h1] at h2
    exact ⟨h1, h2⟩

lemma mem_lattice_periodPairOfTau (τ : ℍ) (x : ℂ) :
    x ∈ (periodPairOfTau τ).lattice ↔ ∃ m n : ℤ, 1 * (m * (τ : ℂ) + n) = x := by
  simp [PeriodPair.mem_lattice, periodPairOfTau]

theorem exists_lattice_eq_mul_tau (L : PeriodPair) :
    ∃ (a : ℂ) (τ : ℍ), a ≠ 0 ∧ ∀ x, x ∈ L.lattice ↔ ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = x := by
  have hi := LinearIndependent.pair_iff.mp L.indep
  have h2 : L.ω₂ ≠ 0 := fun h ↦ by simpa using (hi 0 1 (by simp [h])).2
  have him : (L.ω₁ / L.ω₂).im ≠ 0 := fun h ↦ by
    have h3 : L.ω₁ / L.ω₂ = ((L.ω₁ / L.ω₂).re : ℂ) := Complex.ext (by simp) (by simpa using h)
    have := (hi 1 (-(L.ω₁ / L.ω₂).re) (by
      simp only [Complex.real_smul, Complex.ofReal_neg, ← h3]
      field_simp
      simp)).1
    simp at this
  rcases lt_or_gt_of_ne him with h | h
  · refine ⟨L.ω₂, ⟨-(L.ω₁ / L.ω₂), by simpa using h⟩, h2, fun x ↦ ?_⟩
    rw [PeriodPair.mem_lattice]
    constructor
    · rintro ⟨m, n, rfl⟩
      exact ⟨-m, n, by push_cast; field_simp⟩
    · rintro ⟨m, n, rfl⟩
      exact ⟨-m, n, by push_cast; field_simp⟩
  · refine ⟨L.ω₂, ⟨L.ω₁ / L.ω₂, h⟩, h2, fun x ↦ ?_⟩
    rw [PeriodPair.mem_lattice]
    constructor
    · rintro ⟨m, n, rfl⟩
      exact ⟨m, n, by field_simp⟩
    · rintro ⟨m, n, rfl⟩
      exact ⟨m, n, by field_simp⟩

section

variable {L : PeriodPair} {a : ℂ} {τ : ℍ} (ha : a ≠ 0)
  (h : ∀ x, x ∈ L.lattice ↔ ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = x)
include ha h

theorem latticeG_eq_E {k : ℕ} (hk : 3 ≤ k) :
    L.G k = 2 * riemannZeta k * E hk τ / a ^ k := by
  let e : (Fin 2 → ℤ) → L.lattice := fun v ↦ ⟨a * (v 0 * (τ : ℂ) + v 1), (h _).mpr ⟨_, _, rfl⟩⟩
  have he : Function.Bijective e := by
    constructor
    · intro v w hvw
      have h0 : (v 0 * (τ : ℂ) + v 1) = w 0 * (τ : ℂ) + w 1 :=
        mul_left_cancel₀ ha (congrArg Subtype.val hvw)
      have h1 := congrArg Complex.im h0
      simp [τ.im_ne_zero] at h1
      rw [h1, add_right_inj] at h0
      ext i
      fin_cases i
      · exact h1
      · exact_mod_cast h0
    · rintro ⟨x, hx⟩
      obtain ⟨m, n, rfl⟩ := (h x).mp hx
      exact ⟨![m, n], rfl⟩
  have h1 := tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries hk τ
  have h2 : E hk τ = (1 / 2 : ℂ) * eisensteinSeries (N := 1) 0 k τ := rfl
  rw [PeriodPair.G, ← (Equiv.ofBijective e he).tsum_eq, h2]
  have h3 : ∀ v, (((Equiv.ofBijective e he v : L.lattice) : ℂ) ^ k)⁻¹ =
      (a ^ k)⁻¹ * eisSummand k v τ := fun v ↦ by
    simp [e, eisSummand, mul_pow, mul_comm]
  simp_rw [h3]
  rw [tsum_mul_left, h1]
  field_simp

theorem g₂_eq_E₄ : L.g₂ = 4 * π ^ 4 / 3 * E₄ τ / a ^ 4 := by
  have := latticeG_eq_E ha h (k := 4) (by norm_num)
  rw [PeriodPair.g₂, this, Nat.cast_ofNat, riemannZeta_four]
  ring

theorem g₃_eq_E₆ : L.g₃ = 8 * π ^ 6 / 27 * E₆ τ / a ^ 6 := by
  have := latticeG_eq_E ha h (k := 6) (by norm_num)
  have h6 : riemannZeta 6 = π ^ 6 / 945 := by
    have := riemannZeta_two_mul_nat (k := 3) (by norm_num)
    rw [show bernoulli (2 * 3) = 1 / 42 by decide +kernel] at this
    norm_num [Nat.factorial] at this
    rw [this]
    ring
  rw [PeriodPair.g₃, this, Nat.cast_ofNat, h6]
  ring

theorem latticeCurve_Δ_eq_discriminant :
    (latticeCurve L).Δ = (2 * π / a) ^ 12 * discriminant τ := by
  rw [latticeCurve_Δ, g₂_eq_E₄ ha h, g₃_eq_E₆ ha h, discriminant_eq_E₄_cube_sub_E₆_sq]
  field_simp
  ring

end

theorem latticeCurve_Δ_ne_zero (L : PeriodPair) : (latticeCurve L).Δ ≠ 0 := by
  obtain ⟨a, τ, ha, h⟩ := exists_lattice_eq_mul_tau L
  rw [latticeCurve_Δ_eq_discriminant ha h]
  have := discriminant_ne_zero τ
  have := Real.pi_ne_zero
  simp [*]

instance latticeCurve_isElliptic (L : PeriodPair) : (latticeCurve L).IsElliptic :=
  ⟨(latticeCurve_Δ_ne_zero L).isUnit⟩

theorem latticeCurve_j {L : PeriodPair} {a : ℂ} {τ : ℍ} (ha : a ≠ 0)
    (h : ∀ x, x ∈ L.lattice ↔ ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = x) :
    (latticeCurve L).j = E₄ τ ^ 3 / discriminant τ := by
  rw [WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ',
    latticeCurve_Δ_eq_discriminant ha h, latticeCurve_c₄, g₂_eq_E₄ ha h]
  have := discriminant_ne_zero τ
  have : (π : ℂ) ≠ 0 := by simpa using Real.pi_ne_zero
  field_simp
  ring

lemma tendsto_E₄_atImInfty : Tendsto (E₄ : ℍ → ℂ) atImInfty (𝓝 1) := by
  have h0 : valueAtInfty E₄ = 1 := by
    rw [← qExpansion_coeff_zero one_pos
      (ModularFormClass.analyticAt_cuspFunction_zero E₄ one_pos one_mem_strictPeriods_SL)
      (SlashInvariantFormClass.periodic_comp_ofComplex E₄ one_mem_strictPeriods_SL)]
    exact E_qExpansion_coeff_zero _ ⟨2, rfl⟩
  obtain ⟨c, hc, h⟩ := ModularFormClass.exp_decay_sub_atImInfty' (E₄)
  rw [h0] at h
  have h2 : Tendsto (fun τ : ℍ ↦ Real.exp (-c * τ.im)) atImInfty (𝓝 0) := by
    refine Real.tendsto_exp_atBot.comp ?_
    exact Tendsto.const_mul_atTop_of_neg (by linarith) tendsto_comap
  simpa using (h.trans_tendsto h2).add_const 1

theorem exists_E₄_cube_div_discriminant_eq (c : ℂ) :
    ∃ τ : ℍ, E₄ τ ^ 3 / discriminant τ = c := by
  by_contra! hc
  let g : ModularForm 𝒮ℒ 12 := ModularForm.mcast (by decide) (E₄.pow 3) -
    c • (CuspForm.discriminant : ModularForm 𝒮ℒ 12)
  have hg : ∀ τ, g τ = E₄ τ ^ 3 - c * discriminant τ := fun τ ↦ by
    simp [g]
    rfl
  have hg0 : ∀ τ, g τ ≠ 0 := fun τ h ↦ hc τ (by
    rw [hg] at h
    rw [div_eq_iff (discriminant_ne_zero τ)]
    linear_combination h)
  have hlim : Tendsto (g : ℍ → ℂ) atImInfty (𝓝 1) := by
    have := (tendsto_E₄_atImInfty.pow 3).sub
      ((show Tendsto discriminant atImInfty (𝓝 0) from discriminant_isZeroAtImInfty).const_mul c)
    simpa [funext hg] using this
  have hsl : ∀ γ : SL(2, ℤ),
      ((1 : ℍ → ℂ) / g) ∣[(0 : ℤ) - 12] γ = (1 : ℍ → ℂ) / g := fun γ ↦ by
    have hγ : (γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ, rfl⟩
    rw [div_slash_SL2, is_invariant_one, SL_slash, SlashInvariantForm.slash_action_eqn _ _ hγ]
  let f : ModularForm 𝒮ℒ ((0 : ℤ) - 12) :=
    { toFun := (1 : ℍ → ℂ) / g
      slash_action_eq' := fun _ ⟨γ, hγ⟩ ↦ hγ ▸ hsl γ
      holo' := mdifferentiable_const.div g.holo' hg0
      bdd_at_cusps' := fun {c} hc ↦ by
        rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
        rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
        intro γ _
        rw [hsl γ]
        exact ((tendsto_const_nhds (x := (1 : ℂ))).div hlim one_ne_zero).isBigO_one ℝ }
  have := congrFun (ModularFormClass.levelOne_neg_weight_eq_zero (by norm_num) f) UpperHalfPlane.I
  have h3 : (1 : ℂ) / g UpperHalfPlane.I = 0 := this
  simp [hg0] at h3

theorem exists_variableChange_eq_latticeCurve (W : WeierstrassCurve ℂ) [W.IsElliptic] :
    ∃ (L : PeriodPair) (C : WeierstrassCurve.VariableChange ℂ), C • W = latticeCurve L := by
  obtain ⟨τ, hτ⟩ := exists_E₄_cube_div_discriminant_eq W.j
  refine ⟨periodPairOfTau τ, W.exists_variableChange_of_j_eq _ ?_⟩
  rw [latticeCurve_j one_ne_zero (mem_lattice_periodPairOfTau τ), hτ]

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringLiftOfSpecialFibre
open IsLocalRing

namespace GlobalTheory

universe u

section Algebra

theorem height_le_one_of_forall_mem {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B]
    (m : Ideal B) [m.IsPrime] {f : B} (hf : f ≠ 0)
    (h : ∀ p : Ideal B, p.IsPrime → p ≠ ⊥ → p ≤ m → f ∈ p) : m.height ≤ 1 := by
  by_cases hm : m = ⊥
  · subst hm
    simp
  have hfin := (Ideal.span {f}).finite_minimalPrimes_of_isNoetherianRing
  have hsub : (m : Set B) ⊆ ⋃ P ∈ (Ideal.span {f}).minimalPrimes, ((id P : Ideal B) : Set B) := by
    intro x hx
    simp only [Set.mem_iUnion, id, SetLike.mem_coe]
    by_cases hx0 : x = 0
    · obtain ⟨P, hP, -⟩ := Ideal.exists_minimalPrimes_le (I := Ideal.span {f}) (J := m)
        ((Ideal.span_singleton_le_iff_mem _).mpr (h m inferInstance hm le_rfl))
      exact ⟨P, hP, hx0 ▸ P.zero_mem⟩
    obtain ⟨P, hP, hPm⟩ := Ideal.exists_minimalPrimes_le (I := Ideal.span {x}) (J := m)
        ((Ideal.span_singleton_le_iff_mem _).mpr hx)
    have hPp : P.IsPrime := hP.1.1
    have hxP : x ∈ P := (Ideal.span_singleton_le_iff_mem _).mp hP.1.2
    have hP1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hP
    have hfP : f ∈ P := h P hPp (fun e => hx0 (by simpa [e] using hxP)) hPm
    obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le (I := Ideal.span {f}) (J := P)
        ((Ideal.span_singleton_le_iff_mem _).mpr hfP)
    have hQp : Q.IsPrime := hQ.1.1
    have hfQ : f ∈ Q := (Ideal.span_singleton_le_iff_mem _).mp hQ.1.2
    have hQ0 : ⊥ < Q := bot_lt_iff_ne_bot.mpr fun e => hf (by simpa [e] using hfQ)
    refine ⟨Q, hQ, ?_⟩
    rcases hQP.eq_or_lt with e | hlt
    · exact e ▸ hxP
    · exfalso
      have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hQ0
      have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
      have h3 : (⊥ : Ideal B).height + 1 + 1 ≤ 1 := (add_le_add h1 le_rfl).trans (h2.trans hP1)
      simp at h3
      exact absurd h3 (by decide)
  obtain ⟨P, hP, hmP⟩ := (Ideal.subset_union_prime_finite hfin (f := id) ⊥ ⊥
    (fun i hi _ _ => hi.1.1)).mp hsub
  have hPp : P.IsPrime := hP.1.1
  exact (Ideal.height_mono hmP).trans
    (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hP)

theorem exists_notMem_forall_mem_minimalPrimes {B : Type*} [CommRing B] [IsNoetherianRing B]
    (I p : Ideal B) [p.IsPrime] (hp : ∀ P ∈ I.minimalPrimes, P ≤ p → P = p) :
    ∃ s ∉ p, ∀ P ∈ I.minimalPrimes, P ≠ p → s ∈ P := by
  classical
  have hfin : (I.minimalPrimes \ {p}).Finite :=
    I.finite_minimalPrimes_of_isNoetherianRing.subset Set.sdiff_subset
  have : ¬ hfin.toFinset.inf id ≤ p := by
    rw [Ideal.IsPrime.inf_le' inferInstance]
    rintro ⟨P, hP, hle⟩
    rw [Set.Finite.mem_toFinset] at hP
    exact hP.2 (hp P hP.1 hle)
  obtain ⟨s, hs, hsp⟩ := SetLike.not_le_iff_exists.mp this
  refine ⟨s, hsp, fun P hP hne => ?_⟩
  exact (Finset.inf_le (f := id) (hfin.mem_toFinset.mpr ⟨hP, hne⟩) : _ ≤ P) hs

theorem quasiFiniteAt_of_height_le_one {O B : Type*} [CommRing O] [IsNoetherianRing O]
    [CommRing B] [IsDomain B] [Algebra O B] [Algebra.FiniteType O B]
    (m : Ideal B) [hm : m.IsMaximal] (h1 : m.height ≤ 1) (π : O) (hπ : algebraMap O B π ≠ 0)
    (hπm : algebraMap O B π ∈ m) : Algebra.QuasiFiniteAt O m := by
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing O B
  obtain ⟨s, hsm, hs⟩ := exists_notMem_forall_mem_minimalPrimes
    (Ideal.span {algebraMap O B π}) m (fun P hP hle => by
      have hPp : P.IsPrime := hP.1.1
      have hfP : algebraMap O B π ∈ P := (Ideal.span_singleton_le_iff_mem _).mp hP.1.2
      have hP0 : ⊥ < P := bot_lt_iff_ne_bot.mpr fun e => hπ (by simpa [e] using hfP)
      by_contra hne
      have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hP0
      have h3 := Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne hle hne)
      have h4 : (⊥ : Ideal B).height + 1 + 1 ≤ 1 := (add_le_add h2 le_rfl).trans (h3.trans h1)
      simp at h4
      exact absurd h4 (by decide))
  refine Algebra.QuasiFiniteAt.of_isOpen_singleton_fiber (R := O) ⟨m, inferInstance⟩ ?_
  refine isOpen_induced_iff.mpr ⟨PrimeSpectrum.basicOpen s, (PrimeSpectrum.basicOpen s).isOpen, ?_⟩
  ext ⟨q, hq⟩
  simp only [Set.mem_preimage, SetLike.mem_coe, PrimeSpectrum.mem_basicOpen,
    Set.mem_singleton_iff]
  constructor
  · intro hsq
    have hπq : algebraMap O B π ∈ q.asIdeal := by
      have : π ∈ (PrimeSpectrum.comap (algebraMap O B) q).asIdeal := by
        rw [Set.mem_preimage, Set.mem_singleton_iff] at hq
        rw [hq]
        exact hπm
      exact this
    obtain ⟨P, hP, hPq⟩ := Ideal.exists_minimalPrimes_le (J := q.asIdeal)
      ((Ideal.span_singleton_le_iff_mem _).mpr hπq)
    have hPm : P = m := by
      by_contra hne
      exact hsq (hPq (hs P hP hne))
    subst hPm
    exact Subtype.ext <| PrimeSpectrum.ext (hm.eq_of_le q.isPrime.ne_top hPq).symm
  · intro e
    obtain rfl : q = ⟨m, inferInstance⟩ := congrArg Subtype.val e
    exact hsm

theorem exists_valuationSubring_of_height_le_one {O K : Type*} {B : Type u} [CommRing O]
    [IsDomain O] [IsNoetherianRing O] [Field K] [Algebra O K] [IsFractionRing O K]
    [CommRing B] [IsDomain B] [Algebra O B] [Algebra.FiniteType O B]
    (hinj : Function.Injective (algebraMap O B))
    (m : Ideal B) [hm : m.IsMaximal] (h1 : m.height ≤ 1) (π : O) (hπ : π ≠ 0)
    (hπm : algebraMap O B π ∈ m) :
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : Module.Finite K K')
      (O' : ValuationSubring K') (φ : B →+* O'),
      (∀ a : O, (φ (algebraMap O B a) : K') = algebraMap K K' (algebraMap O K a)) ∧
      Function.Injective φ ∧ (maximalIdeal O').comap φ = m := by
  have hq : Algebra.QuasiFiniteAt O m := quasiFiniteAt_of_height_le_one m h1 π
    (fun e => hπ (hinj (by simpa using e))) hπm
  let K' := FractionRing B
  let L := Localization.AtPrime m
  let g : L →ₐ[B] K' := IsLocalization.liftAlgHom (M := m.primeCompl) (f := Algebra.ofId B K')
    (fun y => by
      have : (y : B) ≠ 0 := fun e => y.2 (e ▸ m.zero_mem)
      exact IsUnit.mk0 _ (by simpa [K'] using this))
  have hqK : Algebra.QuasiFinite O K' := by
    refine .of_forall_exists_mul_mem_range (g.restrictScalars O) fun x => ?_
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := B) x
    have hb' : algebraMap B K' b ≠ 0 := by
      simpa [K'] using nonZeroDivisors.ne_zero hb
    refine ⟨algebraMap B L b, ?_, algebraMap B L a, ?_⟩
    · have : (g.restrictScalars O) (algebraMap B L b) = algebraMap B K' b := g.commutes b
      rw [this]
      exact IsUnit.mk0 _ hb'
    · simp [div_mul_cancel₀ _ hb']
  have hOK' : Function.Injective (algebraMap O K') := by
    rw [IsScalarTower.algebraMap_eq O B K']
    exact (IsFractionRing.injective B K').comp hinj
  let _ : Algebra K K' := (IsFractionRing.lift (K := K) hOK').toAlgebra
  have hst : IsScalarTower O K K' := .of_algebraMap_eq fun a => by
    simp [RingHom.algebraMap_toAlgebra]
  have : Algebra.QuasiFinite K K' := .of_restrictScalars O K K'
  obtain ⟨O', hO', hloc⟩ := IsLocalRing.exists_factor_valuationRing (g : L →+* K')
  let ψ : L →+* O' := (g : L →+* K').codRestrict O'.toSubring hO'
  have hψ : IsLocalHom ψ := hloc
  have hval : ∀ b : B, ((ψ.comp (algebraMap B L)) b : K') = algebraMap B K' b := fun b =>
    g.commutes b
  refine ⟨K', inferInstance, inferInstance, .of_quasiFinite, O', ψ.comp (algebraMap B L),
    fun a => ?_, fun a b hab => ?_, ?_⟩
  · rw [hval, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  · apply IsFractionRing.injective B K'
    rw [← hval, ← hval, hab]
  · rw [← Ideal.comap_comap, maximalIdeal_comap ψ]
    exact IsLocalization.AtPrime.under_maximalIdeal L m

theorem exists_mem_height_map_le_one {A : Type*} [CommRing A] [IsNoetherianRing A]
    (m : Ideal A) [m.IsPrime] {U : Set (PrimeSpectrum A)} (hU : IsOpen U)
    (h : ∃ p ∈ U, p.asIdeal ≤ m) :
    ∃ q ∈ U, q.asIdeal ≤ m ∧ (m.map (Ideal.Quotient.mk q.asIdeal)).height ≤ 1 := by
  obtain ⟨p₀, hp₀, hp₀m⟩ := h
  obtain ⟨I, ⟨q, ⟨hqU, hqm⟩, rfl⟩, hmax⟩ := set_has_maximal_iff_noetherian.mpr
    (inferInstance : IsNoetherian A A)
    (PrimeSpectrum.asIdeal '' {p | p ∈ U ∧ p.asIdeal ≤ m}) ⟨_, p₀, ⟨hp₀, hp₀m⟩, rfl⟩
  refine ⟨q, hqU, hqm, ?_⟩
  obtain ⟨_, ⟨f, rfl⟩, hfq, hfU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hqU hU
  have hsurj := Ideal.Quotient.mk_surjective (I := q.asIdeal)
  have : (m.map (Ideal.Quotient.mk q.asIdeal)).IsPrime :=
    Ideal.map_isPrime_of_surjective hsurj (by simpa using hqm)
  refine height_le_one_of_forall_mem _ (f := Ideal.Quotient.mk q.asIdeal f)
    (fun e => hfq (Ideal.Quotient.eq_zero_iff_mem.mp e)) fun p hp hp0 hpm => ?_
  by_contra hfp
  let p' : PrimeSpectrum A := ⟨p.comap (Ideal.Quotient.mk q.asIdeal), inferInstance⟩
  have hle : q.asIdeal ≤ p'.asIdeal := fun x hx => by
    change Ideal.Quotient.mk q.asIdeal x ∈ p
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact p.zero_mem
  have hp'm : p'.asIdeal ≤ m := by
    refine (Ideal.comap_mono hpm).trans ?_
    rw [Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact sup_le le_rfl hqm
  refine hmax p'.asIdeal ⟨p', ⟨hfU hfp, hp'm⟩, rfl⟩ (lt_of_le_of_ne hle fun e => hp0 ?_)
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨x, rfl⟩ := hsurj x
  have : x ∈ q.asIdeal := e ▸ hx
  simpa using Ideal.Quotient.eq_zero_iff_mem.mpr this

end Algebra

section Scheme

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

variable {O K : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K]

end Scheme

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.StalkGenericPointSpecializesOfSpecializes
open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

namespace GlobalTheory

section Generisation

variable {Z : Scheme.{u}} (η : Z) [IsDomain (Z.presheaf.stalk η)]

variable [IsDiscreteValuationRing (Z.presheaf.stalk η)]

end Generisation

section ResidueCharacteristic

end ResidueCharacteristic

section LocalSource

variable {Z : Scheme.{u}} {R : CommRingCat.{u}} [IsLocalRing R]

variable {η ξ : Z} [IsDomain (Z.presheaf.stalk η)] [IsDiscreteValuationRing (Z.presheaf.stalk η)]

end LocalSource

section ThetaShiftProofs

open PowerSeries

theorem exists_algHom_powerSeries_apply_X_of_isAdicComplete {O : Type*} [CommRing O] (I : Ideal O)
    [h : IsAdicComplete I O] {π : O} (hπ : π ∈ I) : ∃ ev : O⟦X⟧ →ₐ[O] O, ev X = π := by
  let : WithIdeal O := ⟨I⟩
  have hI : IsAdic I := rfl
  obtain ⟨h1, h2⟩ := hI.isAdicComplete_iff.mp h
  have ha : PowerSeries.HasEval π := WithIdeal.isTopologicallyNilpotent_of_mem hπ
  refine ⟨PowerSeries.aeval ha, ?_⟩
  rw [← Polynomial.coe_X, PowerSeries.aeval_coe, Polynomial.aeval_X]

variable {Z : Scheme.{u}} {η ξ : Z} [IsDomain (Z.presheaf.stalk η)]
  [IsDiscreteValuationRing (Z.presheaf.stalk η)]
  {O : Type u} [CommRing O] [IsDomain O] [IsLocalRing O]

end ThetaShiftProofs

section Model

open PowerSeries

end Model

end GlobalTheory
end
