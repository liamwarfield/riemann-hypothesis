module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundaryEffectiveUpEtaleTowerNormalLocalStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KltOfKltRestrict

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.DominatesIffIsLocalHom
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair

variable {k K L : Type} [Field k] [Field K] [Field L]

namespace PolyTower

variable (R : Subring K) [IsLocalRing R] (r : ℕ)

end PolyTower


theorem IsEtTower.ker_eq_span {cK : k →+* K} {R : Subring K} {cL : k →+* L} {T : Subring L}
    {r : ℕ} {ι : R →+* T} {ψ : T →+* R} {τ : Fin r → T} (h : IsEtTower cK R cL T ι ψ τ) :
    RingHom.ker ψ = Ideal.span (Set.range τ) := by
  haveI := h.top.isLocalRing
  haveI : IsNoetherianRing T := by
    letI := (cL.codRestrict T h.top.const_mem).toAlgebra
    haveI : Algebra.EssFiniteType k T := h.top.essFiniteType
    exact Algebra.EssFiniteType.isNoetherianRing k T
  let P := MvPolynomial (Fin r) R
  letI : Algebra P T := (MvPolynomial.eval₂Hom ι τ).toAlgebra
  haveI : Algebra.FormallyEtale P T := h.etale
  set I := RingHom.ker ψ
  set J : Ideal T := Ideal.span (Set.range τ)
  have hJI : J ≤ I := Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact h.zero i)
  have hsub : ∀ x, x - ι (ψ x) ∈ I := fun x => by
    show ψ _ = 0
    rw [map_sub, h.retr, sub_self]
  let Q : Ideal T := J ⊔ I * I
  let g : T →ₐ[P] T ⧸ Q :=
    { (Ideal.Quotient.mk Q).comp (ι.comp ψ) with
      commutes' := fun x => by
        have : ((Ideal.Quotient.mk Q).comp (ι.comp ψ)).comp (MvPolynomial.eval₂Hom ι τ) =
            (Ideal.Quotient.mk Q).comp (MvPolynomial.eval₂Hom ι τ) := by
          apply MvPolynomial.ringHom_ext
          · intro a; simp [h.retr]
          · intro i
            have : τ i ∈ Q := Ideal.mem_sup_left (Ideal.subset_span ⟨i, rfl⟩)
            simp [h.zero, Ideal.Quotient.eq_zero_iff_mem.2 this]
        exact RingHom.congr_fun this x }
  have hn : IsNilpotent (I.map (Ideal.Quotient.mk Q)) := by
    refine ⟨2, ?_⟩
    rw [pow_two, ← Ideal.map_mul, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
    exact le_sup_right
  have he : Ideal.Quotient.mkₐ P Q = g := by
    refine Algebra.FormallyUnramified.ext _ hn fun x => ?_
    rw [Ideal.Quotient.eq]
    have := Ideal.mem_map_of_mem (Ideal.Quotient.mk Q) (hsub x)
    rw [map_sub] at this
    exact this
  have hIQ : I ≤ J ⊔ I • I := fun x hx => by
    have e := AlgHom.congr_fun he x
    have hx' : ψ x = 0 := hx
    have : Ideal.Quotient.mk Q x = 0 := by
      refine e.trans ?_
      show Ideal.Quotient.mk Q (ι (ψ x)) = 0
      rw [hx', map_zero, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.1 this
  have hI : I ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top ψ)
  exact le_antisymm (Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian I) hI hIQ) hJI

theorem IsEtTower.bijective_of_zero {cK : k →+* K} {R : Subring K} {cL : k →+* L} {T : Subring L}
    {ι : R →+* T} {ψ : T →+* R} {τ : Fin 0 → T} (h : IsEtTower cK R cL T ι ψ τ) :
    Function.Bijective ψ := by
  refine ⟨(RingHom.injective_iff_ker_eq_bot ψ).2 ?_, fun a => ⟨ι a, h.retr a⟩⟩
  rw [h.ker_eq_span, Set.range_eq_empty, Ideal.span_empty]

end GlobalTheory.FieldPair
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientLastCoordinateEtaleTowerNormalLoca
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientLastCoordinateEtaleTowerNormalLoca
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory.FieldPair

open CategoryTheory AlgebraicGeometry TopologicalSpace in
open scoped TensorProduct in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
open MvPolynomial in
private lemma ne_zero_of_eval₂Hom_formallyEtale {A T : Type} [CommRing A] [CommRing T] [Nontrivial T]
    {n : ℕ} (ι : A →+* T) (τ : Fin n → T) (h : (MvPolynomial.eval₂Hom ι τ).FormallyEtale) (i : Fin n) :
    τ i ≠ 0 := by
  letI := (eval₂Hom ι τ).toAlgebra
  have hE : Algebra.FormallyEtale (MvPolynomial (Fin n) A) T := h
  let g : MvPolynomial (Fin n) A →+* DualNumber T :=
    eval₂Hom ((TrivSqZeroExt.inlHom T T).comp ι)
      (fun j => TrivSqZeroExt.inl (τ j) + if j = i then DualNumber.eps else 0)
  letI := g.toAlgebra
  have hfst : (TrivSqZeroExt.fstHom T T T).toRingHom.comp g = eval₂Hom ι τ := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp [g]
    · intro j
      simp only [g, RingHom.comp_apply, eval₂Hom_X']
      split_ifs <;> simp
  let p : DualNumber T →ₐ[MvPolynomial (Fin n) A] T :=
    { (TrivSqZeroExt.fstHom T T T).toRingHom with
      commutes' := fun x => by
        show (TrivSqZeroExt.fstHom T T T).toRingHom.comp g x = _
        rw [hfst]; rfl }
  have hp : Function.Surjective p := fun x => ⟨TrivSqZeroExt.inl x, rfl⟩
  have hnil : IsNilpotent (RingHom.ker (p : DualNumber T →+* T)) := by
    refine ⟨2, le_bot_iff.mp ?_⟩
    rw [pow_two]
    refine Ideal.mul_le.mpr fun a ha b hb => ?_
    have ha' : a.fst = 0 := ha
    have hb' : b.fst = 0 := hb
    rw [Ideal.mem_bot]
    ext <;> simp [ha', hb']
  intro h0
  have hc := (Algebra.FormallySmooth.liftOfSurjective (AlgHom.id _ T) p hp hnil).commutes (X i)
  have h1 : algebraMap (MvPolynomial (Fin n) A) T (X i) = 0 := by
    rw [RingHom.algebraMap_toAlgebra, eval₂Hom_X', h0]
  have h2 : algebraMap (MvPolynomial (Fin n) A) (DualNumber T) (X i) = DualNumber.eps := by
    rw [RingHom.algebraMap_toAlgebra]; simp [g, h0]
  rw [h1, h2, map_zero] at hc
  have := congrArg TrivSqZeroExt.snd hc
  simp at this

open CategoryTheory AlgebraicGeometry TopologicalSpace in
open scoped TensorProduct in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
open MvPolynomial in
private lemma formallyEtale_quotient_last {A T : Type} [CommRing A] [CommRing T] {n : ℕ}
    (ι : A →+* T) (τ : Fin (n + 1) → T) (h : (MvPolynomial.eval₂Hom ι τ).FormallyEtale) :
    (MvPolynomial.eval₂Hom ((Ideal.Quotient.mk (Ideal.span {τ (Fin.last n)})).comp ι)
      (fun i => Ideal.Quotient.mk (Ideal.span {τ (Fin.last n)}) (τ (Fin.castSucc i)))).FormallyEtale := by
  set I : Ideal T := Ideal.span {τ (Fin.last n)} with hI
  set φ := eval₂Hom ι τ with hφ
  set φ' := eval₂Hom ((Ideal.Quotient.mk I).comp ι)
    (fun i => Ideal.Quotient.mk I (τ (Fin.castSucc i))) with hφ'
  let σ : MvPolynomial (Fin (n + 1)) A →+* MvPolynomial (Fin n) A :=
    eval₂Hom C (Fin.lastCases 0 X)
  have hσ : ∀ p, φ' (σ p) = Ideal.Quotient.mk I (φ p) := by
    intro p
    show (φ'.comp σ) p = ((Ideal.Quotient.mk I).comp φ) p
    congr 1
    apply MvPolynomial.ringHom_ext
    · intro a; simp [σ, φ, φ']
    · intro j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simp [σ, φ, φ', I, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton_self]
      · simp [σ, φ, φ']
  letI := φ.toAlgebra
  letI := φ'.toAlgebra
  have hE : Algebra.FormallyEtale (MvPolynomial (Fin (n + 1)) A) T := h
  show Algebra.FormallyEtale (MvPolynomial (Fin n) A) (T ⧸ I)
  have toT : ∀ (C' : Type) [CommRing C'] [Algebra (MvPolynomial (Fin n) A) C']
      [Algebra (MvPolynomial (Fin (n + 1)) A) C']
      (_ : ∀ p, algebraMap (MvPolynomial (Fin (n + 1)) A) C' p =
        algebraMap (MvPolynomial (Fin n) A) C' (σ p)),
      ∃ F : (T ⧸ I →ₐ[MvPolynomial (Fin n) A] C') → (T →ₐ[MvPolynomial (Fin (n + 1)) A] C'),
        Function.Bijective F ∧ ∀ f x, F f x = f (Ideal.Quotient.mk I x) := by
    intro C' _ _ _ hC
    refine ⟨fun f => { f.toRingHom.comp (Ideal.Quotient.mk I) with
      commutes' := fun p => by
        show f (Ideal.Quotient.mk I (φ p)) = _
        rw [← hσ, hC]; exact f.commutes (σ p) }, ⟨?_, ?_⟩, fun f x => rfl⟩
    · intro f₁ f₂ hf
      ext x
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact DFunLike.congr_fun hf y
    · intro g
      have hg : I ≤ RingHom.ker g.toRingHom := by
        rw [hI, Ideal.span_le, Set.singleton_subset_iff]
        show g (τ (Fin.last n)) = 0
        have : τ (Fin.last n) = algebraMap (MvPolynomial (Fin (n + 1)) A) T (X (Fin.last n)) := by
          simp [RingHom.algebraMap_toAlgebra, φ]
        rw [this, g.commutes, hC]
        simp [σ]
      refine ⟨{ Ideal.Quotient.lift I g.toRingHom hg with commutes' := fun p => ?_ }, ?_⟩
      · show (Ideal.Quotient.lift I g.toRingHom hg).comp φ' p = algebraMap _ C' p
        congr 1
        apply MvPolynomial.ringHom_ext
        · intro a
          have := g.commutes (C a)
          rw [hC] at this
          simpa [φ', φ, σ, RingHom.algebraMap_toAlgebra] using this
        · intro i
          have := g.commutes (X (Fin.castSucc i))
          rw [hC] at this
          simpa [φ', φ, σ, RingHom.algebraMap_toAlgebra] using this
      · ext x; rfl
  rw [Algebra.FormallyEtale.iff_comp_bijective]
  intro B _ _ J hJ
  letI : Algebra (MvPolynomial (Fin (n + 1)) A) B :=
    ((algebraMap (MvPolynomial (Fin n) A) B).comp σ).toAlgebra
  obtain ⟨F, hF, hFa⟩ := toT B (fun p => rfl)
  obtain ⟨G, hG, hGa⟩ := toT (B ⧸ J) (fun p => rfl)
  have hbij := Algebra.FormallyEtale.comp_bijective (MvPolynomial (Fin (n + 1)) A) T J hJ
  have hcomm : ∀ f, G ((Ideal.Quotient.mkₐ _ J).comp f) = (Ideal.Quotient.mkₐ _ J).comp (F f) := by
    intro f; ext x; simp [hFa, hGa]
  constructor
  · intro f₁ f₂ hf
    apply hF.1
    apply hbij.1
    rw [← hcomm, ← hcomm, hf]
  · intro g
    obtain ⟨f, hf⟩ := hbij.2 (G g)
    obtain ⟨f', rfl⟩ := hF.2 f
    exact ⟨f', hG.1 (by rw [hcomm, hf])⟩

open CategoryTheory AlgebraicGeometry TopologicalSpace in
open scoped TensorProduct in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
private lemma isDomain_of_formallyEtale_of_isLocalRing {A B : Type} [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [IsNoetherianRing A] [CommRing B] [IsLocalRing B] [Algebra A B]
    [Algebra.EssFiniteType A B] [Algebra.FormallyEtale A B] : IsDomain B := by
  obtain ⟨S, M, hS, hM⟩ := (Algebra.essFiniteType_iff_exists_subalgebra A B).1 inferInstance
  haveI : Algebra.FinitePresentation A S := Algebra.FinitePresentation.of_finiteType.mp hS
  let q : Ideal S := (IsLocalRing.maximalIdeal B).comap (algebraMap S B)
  haveI hq : q.IsPrime := Ideal.comap_isPrime _ _
  haveI : IsLocalization.AtPrime B q := by
    refine IsLocalization.of_le M _ ?_ ?_
    · intro m hm hmq
      exact (IsLocalRing.mem_maximalIdeal _).1 hmq (IsLocalization.map_units B ⟨m, hm⟩)
    · intro y hy
      by_contra hu
      exact hy ((IsLocalRing.mem_maximalIdeal _).2 hu)
  let e : Localization.AtPrime q ≃ₐ[A] B :=
    (IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) B).restrictScalars A
  haveI : Algebra.FormallyEtale A (Localization.AtPrime q) := Algebra.FormallyEtale.of_equiv e.symm
  have hmem : (⟨q, hq⟩ : PrimeSpectrum S) ∈ Algebra.etaleLocus A S := by
    rw [Algebra.mem_etaleLocus_iff]; exact ‹_›
  obtain ⟨_, ⟨f, rfl⟩, hqf, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hmem Algebra.isOpen_etaleLocus
  haveI : Algebra.FormallyEtale A (Localization.Away f) :=
    Algebra.basicOpen_subset_etaleLocus_iff.1 hsub
  haveI : Algebra.Etale A (Localization.Away f) :=
    ⟨inferInstance, Algebra.FinitePresentation.trans A S (Localization.Away f)⟩
  have hdisj : Disjoint (Submonoid.powers f : Set S) (q : Set S) := by
    rw [Set.disjoint_left]
    rintro _ ⟨k, rfl⟩ hk
    exact hqf (hq.mem_of_pow_mem k hk)
  let q' : Ideal (Localization.Away f) := q.map (algebraMap S _)
  haveI hq' : q'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f) _ q hq hdisj
  have hcomap : q'.comap (algebraMap S (Localization.Away f)) = q :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers f) _ hq hdisj
  obtain ⟨hdom, -⟩ := _root_.GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_etale A q' (Localization.AtPrime q')
  haveI : IsLocalization q.primeCompl (Localization.AtPrime q') := by
    have h1 : IsLocalization (q'.comap (algebraMap S (Localization.Away f))).primeCompl
        (Localization.AtPrime q') :=
      IsLocalization.isLocalization_atPrime_localization_atPrime (Submonoid.powers f) q'
    have h2 : q.primeCompl = (q'.comap (algebraMap S (Localization.Away f))).primeCompl := by
      ext x; simp only [Ideal.mem_primeCompl_iff, hcomap]
    exact h2 ▸ h1
  let e' : Localization.AtPrime q' ≃+* B :=
    (IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q') B).toRingEquiv
  exact e'.symm.toMulEquiv.isDomain


open CategoryTheory AlgebraicGeometry TopologicalSpace in
open scoped TensorProduct in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
theorem _root_.GlobalTheory.FieldPair.IsEtTower.exists_quotient_last :
    ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (r : ℕ) (R : Subring K)
    (T : Subring L) (ι : R →+* T) (ψ : T →+* R) (τ : Fin (r + 1) → T)
    (hT : _root_.GlobalTheory.FieldPair.IsEtTower cK R cL T ι ψ τ),
  ∃ (L' : Type) (_ : Field L') (cL' : ℂ →+* L') (T' : Subring L') (π : T →+* T') (ι' : R →+* T')
    (ψ' : T' →+* R),
    Function.Surjective π ∧ RingHom.ker π = Ideal.span {τ (Fin.last r)} ∧ τ (Fin.last r) ≠ 0 ∧
    _root_.GlobalTheory.FieldPair.IsEtTower cK R cL' T' ι' ψ' (fun i => π (τ (Fin.castSucc i))) ∧
    ψ'.comp π = ψ ∧ π.comp ι = ι' ∧
    ∀ a, (π ⟨cL a, hT.top.const_mem a⟩ : L') =
      cL' a := by
  intro K L _ _ cK cL r R T ι ψ τ hT
  have hne : τ (Fin.last r) ≠ 0 :=
    ne_zero_of_eval₂Hom_formallyEtale ι τ hT.etale _
  set I : Ideal T := Ideal.span {τ (Fin.last r)} with hI
  have hIt : I ≠ ⊤ := by
    rw [Ne, Ideal.eq_top_iff_one, hI, Ideal.mem_span_singleton]
    rintro ⟨u, hu⟩
    have h1 := congrArg ψ hu
    rw [map_mul, hT.zero, zero_mul, map_one] at h1
    exact one_ne_zero h1
  haveI : Nontrivial (T ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hIt
  haveI : IsLocalRing T := hT.top.isLocalRing
  haveI : IsLocalRing (T ⧸ I) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  haveI : IsIntegrallyClosed R := hT.normal
  letI : Algebra ℂ R :=
    (cK.codRestrict R hT.base.const_mem).toAlgebra
  haveI : Algebra.EssFiniteType ℂ R :=
    hT.base.essFiniteType
  haveI : IsNoetherianRing R := Algebra.EssFiniteType.isNoetherianRing ℂ R
  haveI : IsIntegrallyClosed (MvPolynomial (Fin r) R) := _root_.GlobalTheory.isIntegrallyClosed_mvPolynomial_fin R r
  letI : Algebra ℂ T :=
    (cL.codRestrict T hT.top.const_mem).toAlgebra
  haveI : Algebra.EssFiniteType ℂ T :=
    hT.top.essFiniteType
  haveI : Algebra.EssFiniteType ℂ (T ⧸ I) := Algebra.EssFiniteType.comp ℂ T (T ⧸ I)
  set φ' := MvPolynomial.eval₂Hom ((Ideal.Quotient.mk I).comp ι)
    (fun i => Ideal.Quotient.mk I (τ (Fin.castSucc i))) with hφ'
  letI : Algebra (MvPolynomial (Fin r) R) (T ⧸ I) := φ'.toAlgebra
  haveI : IsScalarTower ℂ (MvPolynomial (Fin r) R) (T ⧸ I) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      show Ideal.Quotient.mk I (algebraMap ℂ T a) = φ' (MvPolynomial.C (algebraMap ℂ R a))
      rw [hφ', MvPolynomial.eval₂Hom_C, RingHom.comp_apply]
      congr 1
      exact Subtype.ext (hT.const a).symm
  haveI : Algebra.EssFiniteType (MvPolynomial (Fin r) R) (T ⧸ I) :=
    Algebra.EssFiniteType.of_comp ℂ _ _
  haveI : Algebra.FormallyEtale (MvPolynomial (Fin r) R) (T ⧸ I) :=
    formallyEtale_quotient_last ι τ hT.etale
  haveI : IsDomain (T ⧸ I) := isDomain_of_formallyEtale_of_isLocalRing (A := MvPolynomial (Fin r) R)
  set f : (T ⧸ I) →+* FractionRing (T ⧸ I) := algebraMap _ _ with hf_def
  have hf : Function.Injective f := IsFractionRing.injective _ _
  let e : (T ⧸ I) ≃+* f.range := RingEquiv.ofBijective f.rangeRestrict
    ⟨fun x y h => hf (by simpa using congrArg Subtype.val h), f.rangeRestrict_surjective⟩
  have hψI : I ≤ RingHom.ker ψ := by
    rw [hI, Ideal.span_le, Set.singleton_subset_iff]
    exact hT.zero _
  let ψQ : (T ⧸ I) →+* R := Ideal.Quotient.lift I ψ hψI
  let π : T →+* f.range := (e : (T ⧸ I) →+* f.range).comp (Ideal.Quotient.mk I)
  refine ⟨FractionRing (T ⧸ I), inferInstance, f.comp ((Ideal.Quotient.mk I).comp
    (cL.codRestrict T hT.top.const_mem)), f.range, π,
    π.comp ι, ψQ.comp (e.symm : f.range →+* (T ⧸ I)), ?_, ?_, hne, ?_, ?_, rfl, fun a => rfl⟩
  · exact e.surjective.comp Ideal.Quotient.mk_surjective
  · ext x
    simp only [RingHom.mem_ker]
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← map_eq_zero_iff _ e.injective]
    rfl
  · refine ⟨hT.base, hT.normal, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨fun a => ⟨_, rfl⟩, ?_, ?_, ?_⟩
      · exact IsLocalRing.of_surjective' (e : (T ⧸ I) →+* f.range) e.surjective
      · have h1 : (algebraMap ℂ (T ⧸ I)).EssFiniteType := RingHom.essFiniteType_algebraMap.2 inferInstance
        have h2 := h1.comp (RingHom.FiniteType.of_surjective (e : (T ⧸ I) →+* f.range)
          e.surjective).essFiniteType
        exact h2
      · intro z
        obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := T ⧸ I) z
        have hb' : f b ≠ 0 := (map_ne_zero_iff _ hf).2 (nonZeroDivisors.ne_zero hb)
        exact ⟨f a, ⟨a, rfl⟩, f b, ⟨b, rfl⟩, hb', div_mul_cancel₀ _ hb'⟩
    · intro a
      show f (Ideal.Quotient.mk I (ι _)) = f (Ideal.Quotient.mk I _)
      congr 2
      exact Subtype.ext (hT.const a)
    · intro a
      show ψQ (e.symm (e (Ideal.Quotient.mk I (ι a)))) = a
      rw [RingEquiv.symm_apply_apply]
      exact hT.retr a
    · intro i
      show ψQ (e.symm (e (Ideal.Quotient.mk I (τ (Fin.castSucc i))))) = 0
      rw [RingEquiv.symm_apply_apply]
      exact hT.zero _
    · have heq : MvPolynomial.eval₂Hom (π.comp ι) (fun i => π (τ (Fin.castSucc i))) =
          (e : (T ⧸ I) →+* f.range).comp φ' := by
        apply MvPolynomial.ringHom_ext <;> intro <;> simp [π, φ']
      rw [heq]
      letI := ((e : (T ⧸ I) →+* f.range).comp φ').toAlgebra
      exact Algebra.FormallyEtale.of_equiv
        { e with commutes' := fun p => rfl : (T ⧸ I) ≃ₐ[MvPolynomial (Fin r) R] f.range }
  · refine RingHom.ext fun x => ?_
    show ψQ (e.symm (e (Ideal.Quotient.mk I x))) = ψ x
    rw [RingEquiv.symm_apply_apply]
    rfl

end GlobalTheory.FieldPair
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientLastCoordinateEtaleTowerNormalLocaStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_quotient_lastCoordinate_etaleTowerNormalLocal : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (r : ℕ) (R : Subring K) (T : Subring L)
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin (r + 1) → T) (hT : IsEtTower cK R cL T ι ψ τ),
  ∃ (L' : Type) (_ : Field L') (cL' : ℂ →+* L') (T' : Subring L') (π : T →+* T') (ι' : R →+* T') (ψ' : T' →+* R),
    Function.Surjective π ∧ RingHom.ker π = Ideal.span {τ (Fin.last r)} ∧ τ (Fin.last r) ≠ 0 ∧
    IsEtTower cK R cL' T' ι' ψ' (fun i => π (τ (Fin.castSucc i))) ∧ ψ'.comp π = ψ ∧ π.comp ι = ι' ∧
    ∀ a, (π ⟨cL a, hT.top.const_mem a⟩ : L') = cL' a := by
  first | exact @GlobalTheory.FieldPair.IsEtTower.exists_quotient_last | exact GlobalTheory.FieldPair.IsEtTower.exists_quotient_last | (intros; apply GlobalTheory.FieldPair.IsEtTower.exists_quotient_last <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrPlaceDiscKaehlerWedgePermNeg
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrPlaceDiscKaehlerWedgePermNeg
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory.FieldPair.Place

variable {k K : Type} [Field k] [Field K] {c : k →+* K} (E : Place c) {n : ℕ}

theorem ord_neg (f : K) : E.ord (-f) = E.ord f := by
  by_cases hf : f = 0
  · simp [hf]
  have h1 : ((-1 : E.ring) : K) = -1 := rfl
  have hu : IsUnit (-1 : E.ring) := isUnit_one.neg
  have h0 : E.ord (-1) = 0 := by rw [← h1]; exact E.ord_eq_zero hu
  rw [neg_eq_neg_one_mul, E.ord_mul (by norm_num) hf, h0, zero_add]

theorem isFormOrd_neg_iff (η : Forms c n) (a : ℤ) : E.IsFormOrd (-η) a ↔ E.IsFormOrd η a := by
  have key : ∀ η : Forms c n, E.IsFormOrd η a → E.IsFormOrd (-η) a := by
    rintro η ⟨ω, hω, f, rfl, hf⟩
    refine ⟨ω, hω, -f, ?_, ?_⟩
    · rw [Units.val_neg, neg_smul]
    · rw [Units.val_neg, E.ord_neg, hf]
  exact ⟨fun h => by simpa using key _ h, key η⟩

theorem formOrd_neg (η : Forms c n) : E.formOrd (-η) = E.formOrd η := by
  by_cases h : ∃ a, E.IsFormOrd η a
  · obtain ⟨a, ha⟩ := h
    rw [((E.isFormOrd_neg_iff η a).2 ha).formOrd_eq, ha.formOrd_eq]
  · have h' : ¬ ∃ a, E.IsFormOrd (-η) a := fun ⟨a, ha⟩ => h ⟨a, (E.isFormOrd_neg_iff η a).1 ha⟩
    rw [formOrd, formOrd, dite_eq_right h, dite_eq_right h']

theorem disc_neg (η : Forms c n) (φ : K →₀ ℚ) : E.disc (-η) φ = E.disc η φ := by
  change (E.formOrd (-η) : ℚ) - E.ordQ φ = (E.formOrd η : ℚ) - E.ordQ φ
  rw [E.formOrd_neg]

end GlobalTheory.FieldPair.Place

namespace GlobalTheory.FieldPair

theorem dForm_comp_perm {k K : Type} [Field k] [Field K] (c : k →+* K) {n : ℕ} (x : Fin n → K)
    (σ : Equiv.Perm (Fin n)) : dForm c (x ∘ σ) = Equiv.Perm.sign σ • dForm c x := by
  rw [dForm_eq, dForm_eq]
  exact (exteriorPower.ιMulti K n).map_perm (fun i => dFun c (x i)) σ

theorem disc_dForm_perm_neg {k K : Type} [Field k] [CharZero k] [Field K] (c : k →+* K) (n : ℕ)
    (x : Fin n → K) (σ : Equiv.Perm (Fin n)) (E : Place c) (φ : K →₀ ℚ) :
    E.disc (dForm c (x ∘ σ)) φ = E.disc (dForm c x) φ ∧ E.disc (-dForm c x) φ = E.disc (dForm c x) φ := by
  refine ⟨?_, E.disc_neg _ φ⟩
  rw [dForm_comp_perm]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · rw [h, one_smul]
  · rw [h, Units.neg_smul, one_smul, E.disc_neg]

end GlobalTheory.FieldPair
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrPlaceDiscKaehlerWedgePermNegStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvrPlace_disc_kaehlerWedge_perm_neg : ∀ {k K : Type} [Field k] [CharZero k] [Field K] (c : k →+* K) (n : ℕ) (x : Fin n → K) (σ : Equiv.Perm (Fin n))
  (E : Place c) (φ : K →₀ ℚ), E.disc (dForm c (x ∘ σ)) φ = E.disc (dForm c x) φ ∧ E.disc (-dForm c x) φ = E.disc (dForm c x) φ := by
  first | exact @GlobalTheory.FieldPair.disc_dForm_perm_neg | exact GlobalTheory.FieldPair.disc_dForm_perm_neg | (intros; apply GlobalTheory.FieldPair.disc_dForm_perm_neg <;> assumption)
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair.SpecTower

theorem klt_comp_equiv {k L : Type} [Field k] [CharZero k] [Field L] (c : k →+* L) {m m' : ℕ}
    (σ : Fin m ≃ Fin m') (y : Fin m' → L) (R : Subring L) (D : L →₀ ℚ) :
    Klt c m R (dForm c (y ∘ σ)) D ↔ Klt c m' R (dForm c y) D := by
  obtain rfl : m = m' := by simpa using Fintype.card_congr σ
  have hs : dForm c (y ∘ σ) = Equiv.Perm.sign σ • dForm c y := by
    rw [dForm_eq, dForm_eq]
    exact (exteriorPower.ιMulti L m).map_perm (fun i => dFun c (y i)) σ
  have hne : dForm c (y ∘ σ) ≠ 0 ↔ dForm c y ≠ 0 := by
    rw [hs]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  have hd : ∀ E : Place c, E.disc (dForm c (y ∘ σ)) D = E.disc (dForm c y) D :=
    fun E => (GlobalTheory.T.dvrPlace_disc_kaehlerWedge_perm_neg c m y σ E D).1
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨hne.1 h1, h2, fun E hE => hd E ▸ h3 E hE⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨hne.2 h1, h2, fun E hE => (hd E).symm ▸ h3 E hE⟩

theorem effAt_comp_equiv {k L : Type} [Field k] [CharZero k] [Field L] (c : k →+* L) {m m' : ℕ}
    (σ : Fin m ≃ Fin m') (y : Fin m' → L) (R : Subring L) (D : L →₀ ℚ) :
    EffAt c m R (dForm c (y ∘ σ)) D ↔ EffAt c m' R (dForm c y) D := by
  obtain rfl : m = m' := by simpa using Fintype.card_congr σ
  have hs : dForm c (y ∘ σ) = Equiv.Perm.sign σ • dForm c y := by
    rw [dForm_eq, dForm_eq]
    exact (exteriorPower.ιMulti L m).map_perm (fun i => dFun c (y i)) σ
  have hne : dForm c (y ∘ σ) ≠ 0 ↔ dForm c y ≠ 0 := by
    rw [hs]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  have hd : ∀ E : Place c, E.disc (dForm c (y ∘ σ)) D = E.disc (dForm c y) D :=
    fun E => (GlobalTheory.T.dvrPlace_disc_kaehlerWedge_perm_neg c m y σ E D).1
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨hne.1 h1, h2, fun E hE => hd E ▸ h3 E hE⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨hne.2 h1, h2, fun E hE => (hd E).symm ▸ h3 E hE⟩

theorem exists_equiv_cons_last {α : Type} (r n : ℕ) (τ : Fin (r + 1) → α) (v : Fin n → α) :
    ∃ σ : Fin (r + n + 1) ≃ Fin (r + 1 + n),
      (Fin.cons (τ (Fin.last r)) (Fin.append (fun i => τ (Fin.castSucc i)) v) : Fin (r + n + 1) → α) =
        Fin.append τ v ∘ σ := by
  let s : Fin (r + n + 1) → Fin (r + 1 + n) := fun j =>
    ⟨if (j : ℕ) = 0 then r else if (j : ℕ) ≤ r then (j : ℕ) - 1 else j, by
      have := j.2; split_ifs <;> omega⟩
  have hs : Function.Injective s := by
    intro a b hab
    have := congrArg Fin.val hab
    simp only [s] at this
    ext
    split_ifs at this <;> omega
  have hb : Function.Bijective s :=
    (Fintype.bijective_iff_injective_and_card s).2 ⟨hs, by simp; omega⟩
  refine ⟨Equiv.ofBijective s hb, funext fun j => ?_⟩
  refine Fin.cases ?_ (fun j => ?_) j
  · simp only [Fin.cons_zero, Function.comp_apply, Equiv.ofBijective_apply]
    have : s 0 = Fin.castAdd n (Fin.last r) := Fin.ext (by simp [s])
    rw [this, Fin.append_left]
  · simp only [Fin.cons_succ, Function.comp_apply, Equiv.ofBijective_apply]
    refine Fin.addCases (fun i => ?_) (fun m => ?_) j
    · rw [Fin.append_left]
      have : s (Fin.castAdd n i).succ = Fin.castAdd n (Fin.castSucc i) :=
        Fin.ext (by simp [s] <;> first | omega | (split_ifs <;> omega))
      rw [this, Fin.append_left]
    · rw [Fin.append_right]
      have : s (Fin.natAdd r m).succ = Fin.natAdd (r + 1) m :=
        Fin.ext (by simp [s] <;> first | omega | (split_ifs <;> omega))
      rw [this, Fin.append_right]

theorem mapDomain_nonneg {α β : Type} (v : α →₀ ℚ) (hv : ∀ a ∈ v.support, 0 ≤ v a) (f : α → β)
    (b : β) : 0 ≤ Finsupp.mapDomain f v b := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply]
  refine Finset.sum_nonneg fun a ha => ?_
  show 0 ≤ (Finsupp.single (f a) (v a)) b
  rw [Finsupp.single_apply]
  split_ifs
  · exact hv a ha
  · exact le_rfl

end GlobalTheory.FieldPair.SpecTower

namespace GlobalTheory.FieldPair.SpecTower

theorem isFractionRing_of_isLocModel {k K : Type} [Field k] [Field K] {c : k →+* K}
    {R : Subring K} (h : IsLocModel c R) : IsFractionRing R K :=
  IsFractionRing.of_field R K fun z => by
    obtain ⟨a, ha, b, hb, hb0, e⟩ := h.frac z
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, eq_div_of_mul_eq hb0 e⟩

theorem klt_tower_zero {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (n : ℕ)
    (R : Subring K) (T : Subring L) (ι : R →+* T) (ψ : T →+* R) (τ : Fin 0 → T) (x : Fin n → R)
    (φ : R →₀ ℚ) (θ : T →₀ ℚ) (h : IsEtTower cK R cL T ι ψ τ)
    (hx : TrBasis cK (fun i => (x i : K)))
    (hk : Klt cK n R (dForm cK (fun i => (x i : K)))
      (Finsupp.mapDomain (fun g : R => (g : K)) φ + Finsupp.mapDomain (fun g : T => ((ψ g : R) : K)) θ)) :
    Klt cL (0 + n) T (dForm cL (Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L))))
      (Finsupp.mapDomain (fun g : R => (ι g : L)) φ + Finsupp.mapDomain (fun g : T => (g : L)) θ) := by
  have hb := h.bijective_of_zero
  have hιψ : ∀ t, ι (ψ t) = t := fun t => hb.1 (by rw [h.retr])
  haveI := isFractionRing_of_isLocModel h.base
  haveI := isFractionRing_of_isLocModel h.top
  let e0 : R ≃+* T := (RingEquiv.ofBijective ψ hb).symm
  have he0 : ∀ a, e0 a = ι a := fun a =>
    (RingEquiv.ofBijective ψ hb).symm_apply_eq.2 (h.retr a).symm
  let e : K ≃+* L := IsFractionRing.ringEquivOfRingEquiv e0
  have he : ∀ a : R, e a = (ι a : L) := fun a => by
    have := IsFractionRing.ringEquivOfRingEquiv_algebraMap (K := K) (L := L) e0 a
    rw [he0] at this
    exact this
  have hc : ∀ a, e (cK a) = cL a := fun a => (he ⟨cK a, h.base.const_mem a⟩).trans (h.const a)
  have hmap : R.map e.toRingHom = T := by
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      have := he ⟨a, ha⟩
      change e a ∈ T
      rw [this]
      exact (ι _).2
    · intro hy
      refine ⟨(ψ ⟨y, hy⟩ : K), (ψ ⟨y, hy⟩).2, ?_⟩
      change e _ = y
      rw [he, hιψ]
  have key := ((GlobalTheory.T.ringEquiv_transports_varietyPair_data cK cL e hc n (fun i => (x i : K)) R _ hx).2.2.1).1 hk
  rw [hmap] at key
  have hx' : (⇑e ∘ fun i => (x i : K)) = fun i => (ι (x i) : L) := funext fun i => he (x i)
  have hD : Finsupp.mapDomain e (Finsupp.mapDomain (fun g : R => (g : K)) φ +
      Finsupp.mapDomain (fun g : T => ((ψ g : R) : K)) θ) =
      Finsupp.mapDomain (fun g : R => (ι g : L)) φ + Finsupp.mapDomain (fun g : T => (g : L)) θ := by
    rw [Finsupp.mapDomain_add, ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
    congr 2
    · funext g; exact he g
    · funext g; simp only [Function.comp_apply]; rw [he, hιψ]
  rw [hx', hD] at key
  rw [Fin.append_left_nil _ _ rfl]
  exact (klt_comp_equiv cL (finCongr (Nat.zero_add n)) _ T _).2 key

end GlobalTheory.FieldPair.SpecTower

namespace GlobalTheory.FieldPair.SpecTower

theorem klt_of_tower (hP : GlobalTheory.Published.Principalisation) (r : ℕ) :
    ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (n : ℕ) (R : Subring K)
      (T : Subring L) (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T) (x : Fin n → R) (φ : R →₀ ℚ)
      (θ : T →₀ ℚ),
    IsEtTower cK R cL T ι ψ τ → TrBasis cK (fun i => (x i : K)) → (∀ g ∈ φ.support, g ≠ 0) →
    (∀ g ∈ θ.support, ψ g ≠ 0 ∧ 0 ≤ θ g) →
    EffAt cK n R (dForm cK (fun i => (x i : K))) (Finsupp.mapDomain (fun g : R => (g : K)) φ) →
    Klt cK n R (dForm cK (fun i => (x i : K)))
      (Finsupp.mapDomain (fun g : R => (g : K)) φ + Finsupp.mapDomain (fun g : T => ((ψ g : R) : K)) θ) →
    Klt cL (r + n) T (dForm cL (Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L))))
      (Finsupp.mapDomain (fun g : R => (ι g : L)) φ + Finsupp.mapDomain (fun g : T => (g : L)) θ) := by
  induction r with
  | zero =>
    intro K L _ _ cK cL n R T ι ψ τ x φ θ h hx _ _ _ hk
    exact klt_tower_zero cK cL n R T ι ψ τ x φ θ h hx hk
  | succ r ih =>
    classical
    intro K L _ _ cK cL n R T ι ψ τ x φ θ h hx hφ hθ hE hk
    obtain ⟨L', _, cL', T', π, ι', ψ', hπs, hker, hf0, h', hψπ, hπι, hcst⟩ :=
      GlobalTheory.T.exists_quotient_lastCoordinate_etaleTowerNormalLocal cK cL r R T ι ψ τ h
    have hψπ' : ∀ t, ψ' (π t) = ψ t := fun t => RingHom.congr_fun hψπ t
    have hπι' : ∀ a, π (ι a) = ι' a := fun a => RingHom.congr_fun hπι a

    let w : Fin (r + n) → T := Fin.append (fun i => τ (Fin.castSucc i)) (fun i => ι (x i))
    let θr : T →₀ ℚ := Finsupp.mapDomain ι φ + θ
    let ψr : T →+* L' := T'.subtype.comp π
    have hrange : ψr.range = T' := by
      ext y
      constructor
      · rintro ⟨t, rfl⟩
        exact (π t).2
      · intro hy
        obtain ⟨t, ht⟩ := hπs ⟨y, hy⟩
        exact ⟨t, by simp [ψr, ht]⟩
    have hkerr : RingHom.ker ψr = Ideal.span {τ (Fin.last r)} := by
      rw [← hker]
      ext t
      simp only [RingHom.mem_ker, ψr, RingHom.comp_apply, Subring.coe_subtype]
      exact ⟨fun e => Subtype.ext e, fun e => by rw [e]; rfl⟩

    let θ' : T' →₀ ℚ := Finsupp.mapDomain π θ
    have hθ' : ∀ g ∈ θ'.support, ψ' g ≠ 0 ∧ 0 ≤ θ' g := by
      intro g hg
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hg)
      refine ⟨by rw [hψπ']; exact (hθ t ht).1, ?_⟩
      exact mapDomain_nonneg θ (fun a ha => (hθ a ha).2) π _
    have hkR : Klt cK n R (dForm cK (fun i => (x i : K)))
        (Finsupp.mapDomain (fun g : R => (g : K)) φ +
          Finsupp.mapDomain (fun g : T' => ((ψ' g : R) : K)) θ') := by
      have e : Finsupp.mapDomain (fun g : T' => ((ψ' g : R) : K)) θ' =
          Finsupp.mapDomain (fun g : T => ((ψ g : R) : K)) θ := by
        rw [← Finsupp.mapDomain_comp]
        congr 1
        funext g
        simp [hψπ']
      rw [e]
      exact hk
    have ih' := ih cK cL' n R T' ι' ψ' (fun i => π (τ (Fin.castSucc i))) x φ θ' h' hx hφ hθ' hE hkR
    have hw : (fun i => ψr (w i)) =
        Fin.append (fun i => (π (τ (Fin.castSucc i)) : L')) (fun i => (ι' (x i) : L')) := by
      funext i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simp [w, ψr, Fin.append_left]
      · simp [w, ψr, Fin.append_right, hπι']
    have hDr : Finsupp.mapDomain ψr θr = Finsupp.mapDomain (fun g : R => (ι' g : L')) φ +
        Finsupp.mapDomain (fun g : T' => (g : L')) θ' := by
      simp only [θr, θ', Finsupp.mapDomain_add, ← Finsupp.mapDomain_comp]
      congr 2
      funext g
      simp [ψr, hπι']
    have hklt' : Klt cL' (r + n) ψr.range (dForm cL' (fun i => ψr (w i)))
        (Finsupp.mapDomain ψr θr) := by
      rw [hrange, hw, hDr]
      exact ih'
    have hloc : IsLocModel cL' ψr.range := hrange ▸ h'.top
    have htr : TrBasis cL' (fun i => ψr (w i)) :=
      hw ▸ GlobalTheory.T.etaleTower_trBasis_append_coordinates cK cL' n r R T' ι' ψ' _ x h' hx
    have hsupp : ∀ g ∈ θr.support, ψr g ≠ 0 := by
      intro g hg
      rcases Finset.mem_union.1 (Finsupp.support_add hg) with hg | hg
      · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hg)
        intro h0
        have h1 : π (ι a) = 0 := Subtype.ext h0
        apply hφ a ha
        rw [← h.retr a, ← hψπ', h1, map_zero]
      · intro h0
        have h1 : π g = 0 := Subtype.ext h0
        apply (hθ g hg).1
        rw [← hψπ', h1, map_zero]

    obtain ⟨σ, hσ⟩ := exists_equiv_cons_last r n (fun i => (τ i : L)) (fun i => (ι (x i) : L))
    have hcons : (Fin.cons ((τ (Fin.last r) : T) : L) (fun i => (w i : L)) : Fin (r + n + 1) → L) =
        Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L)) ∘ σ := by
      rw [← hσ]
      congr 1
      funext i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simp [w, Fin.append_left]
      · simp [w, Fin.append_right]
    have hDL : Finsupp.mapDomain (fun g : T => (g : L)) θr =
        Finsupp.mapDomain (fun g : R => (ι g : L)) φ + Finsupp.mapDomain (fun g : T => (g : L)) θ := by
      simp only [θr, Finsupp.mapDomain_add, ← Finsupp.mapDomain_comp]
      rfl
    have hθL : ∀ g ∈ θ.support, (g : L) ≠ 0 ∧ 0 ≤ θ g := fun g hg =>
      ⟨fun e => (hθ g hg).1 (by rw [show g = 0 from Subtype.ext e, map_zero]), (hθ g hg).2⟩
    have hEff := GlobalTheory.T.boundaryEffective_up_etale_tower_normal_local cK cL n (r + 1) R T ι ψ τ x φ θ h hx hφ hθL hE
    have hEff' : EffAt cL (r + n + 1) T
        (dForm cL (Fin.cons ((τ (Fin.last r) : T) : L) (fun i => (w i : L)) : Fin (r + n + 1) → L))
        (Finsupp.mapDomain (fun g : T => (g : L)) θr) := by
      rw [hcons, hDL]
      exact (effAt_comp_equiv cL σ _ T _).2 hEff
    have hres := GlobalTheory.T.klt_of_klt_restrict_alt hP cL cL' (r + n) T h.top ψr (τ (Fin.last r)) w θr
      (GlobalTheory.T.isIntegrallyClosed_of_isEtaleTowerOverNormalLocal cK cL (r + 1) R T ι ψ τ h) hcst hkerr hf0 hloc htr hsupp hEff' hklt'
    rw [hcons, hDL] at hres
    exact (klt_comp_equiv cL σ _ T _).1 hres

end GlobalTheory.FieldPair.SpecTower

theorem GlobalTheory.FieldPair.klt_of_isEtTower : GlobalTheory.Published.Principalisation →
  ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (n r : ℕ) (R : Subring K) (T : Subring L)
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T) (x : Fin n → R) (φ : R →₀ ℚ) (θ : T →₀ ℚ),
  IsEtTower cK R cL T ι ψ τ → TrBasis cK (fun i => (x i : K)) → (∀ g ∈ φ.support, g ≠ 0) →
  (∀ g ∈ θ.support, ψ g ≠ 0 ∧ 0 ≤ θ g) →
  EffAt cK n R (dForm cK (fun i => (x i : K))) (Finsupp.mapDomain (fun g : R => (g : K)) φ) →
  Klt cK n R (dForm cK (fun i => (x i : K)))
    (Finsupp.mapDomain (fun g : R => (g : K)) φ + Finsupp.mapDomain (fun g : T => ((ψ g : R) : K)) θ) →
  Klt cL (r + n) T (dForm cL (Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L))))
    (Finsupp.mapDomain (fun g : R => (ι g : L)) φ + Finsupp.mapDomain (fun g : T => (g : L)) θ) :=
  fun hP _ _ _ _ cK cL n r => GlobalTheory.FieldPair.SpecTower.klt_of_tower hP r cK cL n
