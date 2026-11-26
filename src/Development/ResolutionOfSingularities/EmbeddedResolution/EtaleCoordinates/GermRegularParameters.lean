module

public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinatePolynomialRing
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateSubscheme

@[expose] public section

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateQuotient
universe u

namespace FunctorialResolution.EmbeddedResolution

noncomputable def etaleChartCoordIdeal (k : Type u) [Field k] (m : ℕ) (S : Type u) [CommRing S]
    [Algebra (CoordPolynomialRing k m) S] (J : Finset (Fin m)) : Ideal S :=
  Ideal.span (etaleChartCoord k m S '' (J : Set (Fin m)))

theorem etaleChartCoordIdeal_eq_span_image (k : Type u) [Field k] (m : ℕ) (S : Type u) [CommRing S]
    [Algebra (CoordPolynomialRing k m) S] (J : Finset (Fin m)) :
    etaleChartCoordIdeal k m S J = Ideal.span (etaleChartCoord k m S '' (J : Set (Fin m))) :=
  rfl

theorem etaleChartCoordIdeal_le (k : Type u) [Field k] (m : ℕ) (S : Type u) [CommRing S]
    [Algebra (CoordPolynomialRing k m) S] (J : Finset (Fin m)) (I : Ideal S)
    (hI : ∀ j ∈ J, etaleChartCoord k m S j ∈ I) : etaleChartCoordIdeal k m S J ≤ I := by
  refine Ideal.span_le.mpr ?_
  rintro x ⟨j, hj, rfl⟩
  exact hI j (Finset.mem_coe.mp hj)

theorem map_mvPolynomialCoordIdeal_eq_etaleChartCoordIdeal (k : Type u) [Field k] (m : ℕ) (S : Type u)
    [CommRing S] [Algebra (CoordPolynomialRing k m) S] (J : Finset (Fin m)) :
    Ideal.map (algebraMap (CoordPolynomialRing k m) S) (mvPolynomialCoordIdeal k m J) =
      etaleChartCoordIdeal k m S J := by
  rw [etaleChartCoordIdeal_eq_span_image, mvPolynomialCoordIdeal_eq_span, Ideal.map_span, Set.image_image]
  rfl

@[reducible] noncomputable def algebraQuotientCoordIdeal (k : Type u) [Field k] (m : ℕ)
    (S : Type u) [CommRing S] [Algebra (CoordPolynomialRing k m) S] (J : Finset (Fin m)) :
    Algebra (MvPolynomial (ULift.{u} (Fin (m - J.card))) k) (S ⧸ etaleChartCoordIdeal k m S J) :=
  RingHom.toAlgebra
    (((Ideal.Quotient.mk (etaleChartCoordIdeal k m S J)).comp
      (algebraMap (CoordPolynomialRing k m) S)).comp (renameCompl k m J).toRingHom)

private theorem etale_algebraMap_coordPolynomialRing (k : Type u) [Field k] (m : ℕ) (S : Type u) [CommRing S]
    [Algebra (CoordPolynomialRing k m) S] [Algebra.Etale (CoordPolynomialRing k m) S] :
    (algebraMap (CoordPolynomialRing k m) S).Etale := by
  have hiff : (algebraMap (CoordPolynomialRing k m) S).toAlgebra
      = (inferInstance : Algebra (CoordPolynomialRing k m) S) :=
    Algebra.algebra_ext _ _ fun r => rfl
  show @Algebra.Etale _ _ _ _ (algebraMap (CoordPolynomialRing k m) S).toAlgebra
  rw [hiff]
  infer_instance

theorem isRegularLocalRing_quotient_map_etaleChartCoordIdeal (k : Type u) [Field k] (m : ℕ)
    (S : Type u) [CommRing S] [Algebra (CoordPolynomialRing k m) S]
    [Algebra.Etale (CoordPolynomialRing k m) S] (q : Ideal S) [q.IsPrime] (A : Type u) [CommRing A]
    [Algebra S A] [IsLocalization q.primeCompl A] (J : Finset (Fin m))
    (hJ : ∀ j ∈ J, etaleChartCoord k m S j ∈ q) :
    IsRegularLocalRing
      (A ⧸ Ideal.map (algebraMap S A) (etaleChartCoordIdeal k m S J)) := by
  classical
  have hIq : etaleChartCoordIdeal k m S J ≤ q := etaleChartCoordIdeal_le k m S J q hJ
  have hq' : (Ideal.map (Ideal.Quotient.mk (etaleChartCoordIdeal k m S J)) q).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hIq)
  let algQuotient : Algebra (CoordPolynomialRing k (m - J.card)) (S ⧸ etaleChartCoordIdeal k m S J) :=
    algebraQuotientCoordIdeal k m S J
  have : Algebra.Etale (CoordPolynomialRing k (m - J.card)) (S ⧸ etaleChartCoordIdeal k m S J) :=
    etale_quotientMk_comp_renameCompl k m J (algebraMap (CoordPolynomialRing k m) S)
      (etale_algebraMap_coordPolynomialRing k m S) (etaleChartCoordIdeal k m S J)
      (map_mvPolynomialCoordIdeal_eq_etaleChartCoordIdeal k m S J).symm
  have h2 : Submonoid.map (Ideal.Quotient.mk (etaleChartCoordIdeal k m S J)) q.primeCompl
      = (Ideal.map (Ideal.Quotient.mk (etaleChartCoordIdeal k m S J)) q).primeCompl := by
    ext x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    constructor
    · rintro ⟨b, hb, hba⟩ hcon
      refine hb ((Ideal.mem_quotient_iff_mem hIq).mp ?_)
      rw [hba]
      exact hcon
    · intro ha
      exact ⟨a, fun hq => ha ((Ideal.mem_quotient_iff_mem hIq).mpr hq), rfl⟩
  have hloc : IsLocalization
      (Submonoid.map (Ideal.Quotient.mk (etaleChartCoordIdeal k m S J)) q.primeCompl)
      (A ⧸ Ideal.map (algebraMap S A) (etaleChartCoordIdeal k m S J)) :=
    inferInstanceAs (IsLocalization
      (Algebra.algebraMapSubmonoid (S ⧸ etaleChartCoordIdeal k m S J) q.primeCompl)
      (A ⧸ Ideal.map (algebraMap S A) (etaleChartCoordIdeal k m S J)))
  have : IsLocalization (Ideal.map (Ideal.Quotient.mk (etaleChartCoordIdeal k m S J)) q).primeCompl
      (A ⧸ Ideal.map (algebraMap S A) (etaleChartCoordIdeal k m S J)) := h2 ▸ hloc
  exact isRegularLocalRing_of_isLocalization_etale k (m - J.card)
    (S ⧸ etaleChartCoordIdeal k m S J)
    (Ideal.map (Ideal.Quotient.mk (etaleChartCoordIdeal k m S J)) q)
    (A ⧸ Ideal.map (algebraMap S A) (etaleChartCoordIdeal k m S J))

private noncomputable def coordinateBasis (k : Type u) [Field k] (m : ℕ)
    (S : Type u) [CommRing S] [Algebra (CoordPolynomialRing k m) S]
    [Algebra k S] [IsScalarTower k (CoordPolynomialRing k m) S]
    [Algebra.Etale (CoordPolynomialRing k m) S] :
    Module.Basis (ULift.{u} (Fin m)) S (KaehlerDifferential k S) :=
  (Algebra.TensorProduct.basis S
    (KaehlerDifferential.mvPolynomialBasis k (ULift.{u} (Fin m)))).map
      (KaehlerDifferential.isBaseChange_of_formallyEtale k (CoordPolynomialRing k m) S).equiv

private theorem coordinateBasis_apply (k : Type u) [Field k] (m : ℕ)
    (S : Type u) [CommRing S] [Algebra (CoordPolynomialRing k m) S]
    [Algebra k S] [IsScalarTower k (CoordPolynomialRing k m) S]
    [Algebra.Etale (CoordPolynomialRing k m) S] (i : Fin m) :
    coordinateBasis k m S (ULift.up i) =
      KaehlerDifferential.D k S (etaleChartCoord k m S i) := by
  simp only [coordinateBasis, Module.Basis.map_apply, Algebra.TensorProduct.basis_apply,
    KaehlerDifferential.mvPolynomialBasis_apply, IsBaseChange.equiv_tmul, one_smul,
    KaehlerDifferential.map_D]
  rfl

private theorem algebraMap_etaleChartCoord_notMem_maximalIdeal_sq_sup (k : Type u) [Field k] (m : ℕ) (S : Type u) [CommRing S]
    [Algebra (CoordPolynomialRing k m) S] [Algebra.Etale (CoordPolynomialRing k m) S]
    (q : Ideal S) [q.IsPrime] (A : Type u) [CommRing A] [Algebra S A]
    [IsLocalization q.primeCompl A] [IsLocalRing A] (J' : Finset (Fin m))
    (hJ' : ∀ i ∈ J', etaleChartCoord k m S i ∈ q) (j : Fin m) (hj : j ∉ J') :
    algebraMap S A (etaleChartCoord k m S j) ∉
      IsLocalRing.maximalIdeal A ^ 2 ⊔ Ideal.map (algebraMap S A) (etaleChartCoordIdeal k m S J') := by
  classical
  let algebraKS : Algebra k S := ((algebraMap (CoordPolynomialRing k m) S).comp
    (algebraMap k (CoordPolynomialRing k m))).toAlgebra
  have : IsScalarTower k (CoordPolynomialRing k m) S := IsScalarTower.of_algebraMap_eq' rfl
  let algebraKA : Algebra k A := ((algebraMap S A).comp (algebraMap k S)).toAlgebra
  have : IsScalarTower k S A := IsScalarTower.of_algebraMap_eq' rfl
  let D : Derivation k S S :=
    ((coordinateBasis k m S).coord (ULift.up.{u} j)).compDer (KaehlerDifferential.D k S)
  let DA : Derivation k A A := D.mapToLocalization q.primeCompl
  have hderivAlgebraMap : ∀ s : S, DA (algebraMap S A s) = algebraMap S A (D s) :=
    Derivation.mapToLocalization_algebraMap D q.primeCompl
  have hDx : D (etaleChartCoord k m S j) = 1 :=
    by
      change (coordinateBasis k m S).repr (KaehlerDifferential.D k S
        (etaleChartCoord k m S j)) (ULift.up j) = 1
      rw [← coordinateBasis_apply k m S j, Module.Basis.repr_self, Finsupp.single_eq_same]
  have hDne : ∀ i : Fin m, i ≠ j → D (etaleChartCoord k m S i) = 0 := by
    intro i hne
    have hup : (ULift.up.{u} j) ≠ ULift.up.{u} i := fun h => hne (congrArg ULift.down h).symm
    change (coordinateBasis k m S).repr (KaehlerDifferential.D k S
      (etaleChartCoord k m S i)) (ULift.up j) = 0
    rw [← coordinateBasis_apply k m S i, Module.Basis.repr_self, Finsupp.single_apply]
    simp [Ne.symm hup]
  have hmapeq : Ideal.map (algebraMap S A) (etaleChartCoordIdeal k m S J')
      = Ideal.span ((fun i : Fin m => algebraMap S A (etaleChartCoord k m S i)) ''
        (J' : Set (Fin m))) := by
    rw [etaleChartCoordIdeal_eq_span_image, Ideal.map_span, Set.image_image]
  have hspan_le : Ideal.span ((fun i : Fin m => algebraMap S A (etaleChartCoord k m S i)) ''
      (J' : Set (Fin m))) ≤ IsLocalRing.maximalIdeal A := by
    refine Ideal.span_le.mpr ?_
    rintro x ⟨i, hi, rfl⟩
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff A q (etaleChartCoord k m S i)
      inferInstance).mpr (hJ' i (Finset.mem_coe.mp hi))
  intro hmem
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hmem
  have hsq : IsLocalRing.maximalIdeal A ^ 2
      = IsLocalRing.maximalIdeal A * IsLocalRing.maximalIdeal A := sq _
  rw [hsq] at ha
  have hDa : DA a ∈ IsLocalRing.maximalIdeal A := by
    refine Submodule.mul_induction_on ha ?_ ?_
    · intro p hp r hr
      rw [DA.leibniz, smul_eq_mul, smul_eq_mul]
      exact add_mem (Ideal.mul_mem_right _ _ hp) (Ideal.mul_mem_right _ _ hr)
    · intro x y hx hy
      rw [map_add (f := _)]
      exact add_mem hx hy
  rw [hmapeq] at hb
  have hDb : DA b ∈ IsLocalRing.maximalIdeal A := by
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hb
    · rintro z ⟨i, hi, rfl⟩
      rw [hderivAlgebraMap, hDne i (by rintro rfl; exact hj (Finset.mem_coe.mp hi)), map_zero]
      exact zero_mem _
    · rw [map_zero]
      exact zero_mem _
    · intro x y hx hy px py
      rw [map_add (f := _)]
      exact add_mem px py
    · intro c x hx px
      have hxm : x ∈ IsLocalRing.maximalIdeal A := hspan_le hx
      rw [smul_eq_mul, DA.leibniz, smul_eq_mul, smul_eq_mul]
      exact add_mem (Ideal.mul_mem_left _ _ px) (Ideal.mul_mem_right _ _ hxm)
  have hone : DA (algebraMap S A (etaleChartCoord k m S j)) = 1 := by
    rw [hderivAlgebraMap, hDx, map_one]
  rw [← hab, map_add (f := _)] at hone
  have h1 : (1 : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [← hone]
    exact add_mem hDa hDb
  exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).mpr h1)

theorem ringKrullDim_quotient_map_etaleChartCoordIdeal_add_card (k : Type u) [Field k] (m : ℕ)
    (S : Type u) [CommRing S] [Algebra (CoordPolynomialRing k m) S]
    [Algebra.Etale (CoordPolynomialRing k m) S] (q : Ideal S) [q.IsPrime] (A : Type u) [CommRing A]
    [Algebra S A] [IsLocalization q.primeCompl A] (J : Finset (Fin m))
    (hJ : ∀ j ∈ J, etaleChartCoord k m S j ∈ q) :
    ringKrullDim (A ⧸ Ideal.map (algebraMap S A) (etaleChartCoordIdeal k m S J)) +
        (J.card : WithBot ℕ∞) = ringKrullDim A := by
  classical
  have : IsRegularLocalRing A := isRegularLocalRing_of_isLocalization_etale k m S q A
  revert hJ
  induction J using Finset.induction_on with
  | empty =>
      intro _
      have h0 : Ideal.map (algebraMap S A) (etaleChartCoordIdeal k m S (∅ : Finset (Fin m))) = ⊥ := by
        rw [etaleChartCoordIdeal_eq_span_image]
        simp
      have hker : (⊥ : Ideal A) = RingHom.ker (RingHom.id A) := by
        ext a
        simp [RingHom.mem_ker]
      have e : (A ⧸ (⊥ : Ideal A)) ≃+* A :=
        (Ideal.quotEquivOfEq hker).trans
          (RingHom.quotientKerEquivOfSurjective
            (show Function.Surjective (RingHom.id A) from fun a => ⟨a, rfl⟩))
      rw [h0, ringKrullDim_eq_of_ringEquiv e]
      simp
  | @insert j J' hjJ ih =>
      intro hJ
      have hJ' : ∀ i ∈ J', etaleChartCoord k m S i ∈ q := fun i hi =>
        hJ i (Finset.mem_insert_of_mem hi)
      have hjq : etaleChartCoord k m S j ∈ q := hJ j (Finset.mem_insert_self _ _)
      set I' := Ideal.map (algebraMap S A) (etaleChartCoordIdeal k m S J') with hI'
      have hR : IsRegularLocalRing (A ⧸ I') :=
        isRegularLocalRing_quotient_map_etaleChartCoordIdeal k m S q A J' hJ'
      set y : A := algebraMap S A (etaleChartCoord k m S j) with hy
      have hins : Ideal.map (algebraMap S A) (etaleChartCoordIdeal k m S (insert j J'))
          = I' ⊔ Ideal.span {y} := by
        rw [hI', hy, etaleChartCoordIdeal_eq_span_image, etaleChartCoordIdeal_eq_span_image, Finset.coe_insert,
          Set.image_insert_eq, Ideal.span_insert, Ideal.map_sup, Ideal.map_span, Ideal.map_span,
          Set.image_singleton]
        exact sup_comm _ _
      have hspan : Ideal.map (Ideal.Quotient.mk I') (Ideal.span {y})
          = Ideal.span {Ideal.Quotient.mk I' y} := by
        rw [Ideal.map_span, Set.image_singleton]
      have e := (Ideal.quotEquivOfEq hspan.symm).trans
        (DoubleQuot.quotQuotEquivQuotSup I' (Ideal.span {y}))
      have hdim1 : ringKrullDim
          (A ⧸ Ideal.map (algebraMap S A) (etaleChartCoordIdeal k m S (insert j J')))
          = ringKrullDim ((A ⧸ I') ⧸ Ideal.span {Ideal.Quotient.mk I' y}) := by
        rw [hins]
        exact (ringKrullDim_eq_of_ringEquiv e).symm
      have hmaxR : IsLocalRing.maximalIdeal (A ⧸ I')
          = Ideal.map (Ideal.Quotient.mk I') (IsLocalRing.maximalIdeal A) :=
        (IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk I')
          Ideal.Quotient.mk_surjective).symm
      have hy1 : Ideal.Quotient.mk I' y ∈ IsLocalRing.maximalIdeal (A ⧸ I') := by
        rw [hmaxR, hy]
        exact Ideal.mem_map_of_mem _
          ((IsLocalization.AtPrime.to_map_mem_maximal_iff A q (etaleChartCoord k m S j)
            inferInstance).mpr hjq)
      have hy2 : Ideal.Quotient.mk I' y ∉ IsLocalRing.maximalIdeal (A ⧸ I') ^ 2 := by
        rw [hmaxR, ← Ideal.map_pow]
        intro hcon
        have hcon2 : y ∈ Ideal.comap (Ideal.Quotient.mk I')
            (Ideal.map (Ideal.Quotient.mk I') (IsLocalRing.maximalIdeal A ^ 2)) := hcon
        rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
          ← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at hcon2
        rw [hy, hI'] at hcon2
        exact algebraMap_etaleChartCoord_notMem_maximalIdeal_sq_sup k m S q A J' hJ' j hjJ hcon2
      have hstep :=
        IsRegularLocalRing.ringKrullDim_quotient_span_singleton_add_one hy1 hy2
      rw [hdim1, Finset.card_insert_of_notMem hjJ]
      have hcard : (((J'.card + 1 : ℕ)) : WithBot ℕ∞) = 1 + (J'.card : WithBot ℕ∞) := by
        push_cast
        ring
      rw [hcard, ← add_assoc, hstep]
      exact ih hJ'

private theorem exists_span_eq_maximalIdeal_card_eq_ringKrullDim (Q : Type u) [CommRing Q] [IsRegularLocalRing Q] :
    ∃ (n : ℕ) (z : Fin n → Q), Ideal.span (Set.range z) = IsLocalRing.maximalIdeal Q ∧
      (n : WithBot ℕ∞) = ringKrullDim Q := by
  classical
  have : IsLocalRing Q := inferInstance
  have : IsNoetherianRing Q := inferInstance
  have : Module.Finite (IsLocalRing.ResidueField Q) (IsLocalRing.CotangentSpace Q) :=
    inferInstance
  have hsurjres : Function.Surjective (algebraMap Q (IsLocalRing.ResidueField Q)) := by
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨y, rfl⟩
  set b := Module.finBasis (IsLocalRing.ResidueField Q) (IsLocalRing.CotangentSpace Q) with hb
  have hsurj : Function.Surjective (IsLocalRing.maximalIdeal Q).toCotangent :=
    Ideal.toCotangent_surjective _
  choose w hw using fun i => hsurj (b i)
  have hspanQ : Submodule.span Q (Set.range b) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ Submodule.span (IsLocalRing.ResidueField Q) (Set.range b) := by
      rw [b.span_eq]
      trivial
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · intro y hy
      exact Submodule.subset_span hy
    · exact zero_mem _
    · intro y z _ _ hy hz
      exact add_mem hy hz
    · intro c y _ hy
      obtain ⟨c', rfl⟩ := hsurjres c
      rw [algebraMap_smul]
      exact Submodule.smul_mem _ _ hy
  have himg : ⇑(IsLocalRing.maximalIdeal Q).toCotangent '' (Set.range w) = Set.range b := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext hw)
  have hMtop : Submodule.span Q (Set.range w) = ⊤ := by
    refine IsLocalRing.CotangentSpace.map_eq_top_iff.mp ?_
    rw [Submodule.map_span, himg]
    exact hspanQ
  refine ⟨Module.finrank (IsLocalRing.ResidueField Q) (IsLocalRing.CotangentSpace Q),
    fun i => ((w i : Q)), ?_, ?_⟩
  · have h1 : Submodule.map (IsLocalRing.maximalIdeal Q).subtype
        (Submodule.span Q (Set.range w)) = Ideal.span (Set.range fun i => ((w i : Q))) := by
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    rw [← h1, hMtop, Submodule.map_subtype_top]
  · exact (IsRegularLocalRing.iff_finrank_cotangentSpace Q).mp ‹_›

theorem exists_regularSystemOfParameters_containing_etaleChartCoords (k : Type u) [Field k] (m : ℕ)
    (S : Type u) [CommRing S] [Algebra (CoordPolynomialRing k m) S]
    [Algebra.Etale (CoordPolynomialRing k m) S] (q : Ideal S) [q.IsPrime] (A : Type u) [CommRing A]
    [Algebra S A] [IsLocalization q.primeCompl A] [IsLocalRing A] (J₀ : Finset (Fin m))
    (hJ₀ : ∀ j ∈ J₀, etaleChartCoord k m S j ∈ q) :
    ∃ (d : ℕ) (x : Fin d → S),
      (∀ i, x i ∈ q) ∧
      (∀ j ∈ J₀, ∃ i, x i = etaleChartCoord k m S j) ∧
      Ideal.span (Set.range fun i => algebraMap S A (x i)) = IsLocalRing.maximalIdeal A ∧
      (d : WithBot ℕ∞) = ringKrullDim A := by
  classical
  set I := Ideal.map (algebraMap S A) (etaleChartCoordIdeal k m S J₀) with hIdef
  have hreg : IsRegularLocalRing (A ⧸ I) :=
    isRegularLocalRing_quotient_map_etaleChartCoordIdeal k m S q A J₀ hJ₀
  have : IsLocalRing (A ⧸ I) := inferInstance
  obtain ⟨n, z, hzspan, hzdim⟩ := exists_span_eq_maximalIdeal_card_eq_ringKrullDim (A ⧸ I)
  have hIle : I ≤ IsLocalRing.maximalIdeal A := by
    rw [hIdef]
    refine Ideal.map_le_iff_le_comap.mpr ?_
    intro s hs
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff A q s inferInstance).mpr
      (etaleChartCoordIdeal_le k m S J₀ q hJ₀ hs)
  have hmaxQ : IsLocalRing.maximalIdeal (A ⧸ I)
      = Ideal.map (Ideal.Quotient.mk I) (IsLocalRing.maximalIdeal A) :=
    (IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective).symm
  choose a ha using fun i : Fin n => Ideal.Quotient.mk_surjective (z i)
  have hamem : ∀ i, a i ∈ IsLocalRing.maximalIdeal A := by
    intro i
    refine (Ideal.mem_quotient_iff_mem hIle).mp ?_
    rw [← hmaxQ, ha i, ← hzspan]
    exact Ideal.subset_span ⟨i, rfl⟩
  choose rt hrt using fun i : Fin n => IsLocalization.surj (M := q.primeCompl) (a i)
  have hsq : ∀ i : Fin n, (rt i).1 ∈ q := by
    intro i
    refine (IsLocalization.AtPrime.to_map_mem_maximal_iff A q (rt i).1 inferInstance).mp ?_
    rw [← hrt i]
    exact Ideal.mul_mem_right _ _ (hamem i)
  refine ⟨J₀.card + n,
    Fin.append
      (fun i : Fin J₀.card => etaleChartCoord k m S ((J₀.equivFin.symm i : {x // x ∈ J₀}) : Fin m))
      (fun i : Fin n => (rt i).1), ?_, ?_, ?_, ?_⟩
  · intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [Fin.append_left]
      exact hJ₀ _ (J₀.equivFin.symm i).2
    · rw [Fin.append_right]
      exact hsq i
  · intro j hj
    refine ⟨Fin.castAdd n (J₀.equivFin ⟨j, hj⟩), ?_⟩
    rw [Fin.append_left, Equiv.symm_apply_apply]
  · have hxq : ∀ i : Fin (J₀.card + n),
        Fin.append
          (fun i : Fin J₀.card =>
            etaleChartCoord k m S ((J₀.equivFin.symm i : {x // x ∈ J₀}) : Fin m))
          (fun i : Fin n => (rt i).1) i ∈ q := by
      intro i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · rw [Fin.append_left]
        exact hJ₀ _ (J₀.equivFin.symm i).2
      · rw [Fin.append_right]
        exact hsq i
    have hTle : Ideal.span (Set.range fun i =>
        algebraMap S A (Fin.append
          (fun i : Fin J₀.card =>
            etaleChartCoord k m S ((J₀.equivFin.symm i : {x // x ∈ J₀}) : Fin m))
          (fun i : Fin n => (rt i).1) i)) ≤ IsLocalRing.maximalIdeal A := by
      refine Ideal.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff A q _ inferInstance).mpr (hxq i)
    have hIT : I ≤ Ideal.span (Set.range fun i =>
        algebraMap S A (Fin.append
          (fun i : Fin J₀.card =>
            etaleChartCoord k m S ((J₀.equivFin.symm i : {x // x ∈ J₀}) : Fin m))
          (fun i : Fin n => (rt i).1) i)) := by
      rw [hIdef, etaleChartCoordIdeal_eq_span_image, Ideal.map_span, Set.image_image]
      refine Ideal.span_le.mpr ?_
      rintro _ ⟨j, hj, rfl⟩
      refine Ideal.subset_span ⟨Fin.castAdd n (J₀.equivFin ⟨j, Finset.mem_coe.mp hj⟩), ?_⟩
      refine congrArg (algebraMap S A) ?_
      rw [Fin.append_left, Equiv.symm_apply_apply]
    refine le_antisymm hTle ?_
    intro y hy
    refine (Ideal.mem_quotient_iff_mem hIT).mp ?_
    have hz : ∀ i : Fin n, z i ∈ Ideal.map (Ideal.Quotient.mk I) (Ideal.span (Set.range fun i =>
        algebraMap S A (Fin.append
          (fun i : Fin J₀.card =>
            etaleChartCoord k m S ((J₀.equivFin.symm i : {x // x ∈ J₀}) : Fin m))
          (fun i : Fin n => (rt i).1) i))) := by
      intro i
      have hunit : IsUnit (Ideal.Quotient.mk I (algebraMap S A ((rt i).2 : S))) :=
        (IsLocalization.map_units A ((rt i).2)).map (Ideal.Quotient.mk I)
      obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp hunit
      have hmem : Ideal.Quotient.mk I (algebraMap S A ((rt i).1))
          ∈ Ideal.map (Ideal.Quotient.mk I) (Ideal.span (Set.range fun i =>
            algebraMap S A (Fin.append
              (fun i : Fin J₀.card =>
                etaleChartCoord k m S ((J₀.equivFin.symm i : {x // x ∈ J₀}) : Fin m))
              (fun i : Fin n => (rt i).1) i))) := by
        refine Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨Fin.natAdd J₀.card i, ?_⟩)
        exact congrArg (algebraMap S A) (Fin.append_right _ _ i)
      have heq : Ideal.Quotient.mk I (algebraMap S A ((rt i).1))
          = z i * Ideal.Quotient.mk I (algebraMap S A ((rt i).2 : S)) := by
        rw [← hrt i, map_mul, ha i]
      have hzi : z i = Ideal.Quotient.mk I (algebraMap S A ((rt i).1)) * v := by
        rw [heq, mul_assoc, hv, mul_one]
      rw [hzi]
      exact Ideal.mul_mem_right _ _ hmem
    have hmq : IsLocalRing.maximalIdeal (A ⧸ I) ≤ Ideal.map (Ideal.Quotient.mk I)
        (Ideal.span (Set.range fun i =>
          algebraMap S A (Fin.append
            (fun i : Fin J₀.card =>
              etaleChartCoord k m S ((J₀.equivFin.symm i : {x // x ∈ J₀}) : Fin m))
            (fun i : Fin n => (rt i).1) i))) := by
      rw [← hzspan]
      refine Ideal.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      exact hz i
    refine hmq ?_
    rw [hmaxQ]
    exact Ideal.mem_map_of_mem _ hy
  · have h2 := ringKrullDim_quotient_map_etaleChartCoordIdeal_add_card k m S q A J₀ hJ₀
    rw [← hIdef] at h2
    rw [← h2, ← hzdim, Nat.cast_add]
    exact add_comm _ _

end FunctorialResolution.EmbeddedResolution
end

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.GermRegularParameters
universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem germ_mem_maximalIdeal_iff {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (x : X) (hx : x ∈ U) (s : Γ(X, U)) :
    X.presheaf.germ U x hx s ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ↔
      s ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
  let instSt : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    (X.presheaf.germ U x hx).hom.toAlgebra
  have instLoc : IsLocalization.AtPrime (X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal := hU.isLocalization_stalk ⟨x, hx⟩
  exact IsLocalization.AtPrime.to_map_mem_maximal_iff (X.presheaf.stalk x)
    (hU.primeIdealOf ⟨x, hx⟩).asIdeal s

variable {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)}
  {U : X.Opens} {m : ℕ}

theorem exists_sections_span_eq_maximalIdeal_with_coords (hU : IsAffineOpen U)
    (c : EtaleChart p U m) (x : X) (hx : x ∈ U) (J₀ : Finset (Fin m))
    (hJ₀ : ∀ j ∈ J₀, X.presheaf.germ U x hx (c.coord j) ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk x)) :
    ∃ (d : ℕ) (f : Fin d → Γ(X, U)),
      (∀ i, X.presheaf.germ U x hx (f i) ∈
          IsLocalRing.maximalIdeal (X.presheaf.stalk x)) ∧
      (∀ j ∈ J₀, ∃ i, f i = c.coord j) ∧
      Ideal.span (Set.range fun i => X.presheaf.germ U x hx (f i)) =
          IsLocalRing.maximalIdeal (X.presheaf.stalk x) ∧
      (d : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk x) := by
  let instAlg : Algebra (CoordPolynomialRing k m) Γ(X, U) := c.algebra
  have instEt : Algebra.Etale (CoordPolynomialRing k m) Γ(X, U) := c.algebra_etale hU
  let instSt : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    (X.presheaf.germ U x hx).hom.toAlgebra
  have instLoc : IsLocalization.AtPrime (X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal := hU.isLocalization_stalk ⟨x, hx⟩
  have halg : ∀ t : Γ(X, U),
      algebraMap Γ(X, U) (X.presheaf.stalk x) t = X.presheaf.germ U x hx t := fun _ => rfl
  have hcoord : ∀ j : Fin m, etaleChartCoord k m Γ(X, U) j = c.coord j := by
    intro j
    show c.coordRingHom (MvPolynomial.X (ULift.up j : ULift.{u} (Fin m))) = c.coord j
    exact c.coordRingHom_X j
  have hq : ∀ j ∈ J₀, etaleChartCoord k m Γ(X, U) j ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
    intro j hj
    rw [hcoord j]
    exact (germ_mem_maximalIdeal_iff hU x hx (c.coord j)).mp (hJ₀ j hj)
  obtain ⟨d, f, hf1, hf2, hf3, hf4⟩ :=
    exists_regularSystemOfParameters_containing_etaleChartCoords k m Γ(X, U)
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal (X.presheaf.stalk x) J₀ hq
  refine ⟨d, f, ?_, ?_, ?_, hf4⟩
  · intro i
    exact (germ_mem_maximalIdeal_iff hU x hx (f i)).mpr (hf1 i)
  · intro j hj
    obtain ⟨i, hi⟩ := hf2 j hj
    exact ⟨i, by rw [hi, hcoord j]⟩
  · simpa only [halg] using hf3

theorem exists_isRegularParameterSystem_with_coords_of_mem_prime (hU : IsAffineOpen U)
    (c : EtaleChart p U m) (x : X) (hx : x ∈ U) (J₀ : Finset (Fin m))
    (hJ₀ : ∀ j ∈ J₀, c.coord j ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal) :
    ∃ (n : ℕ) (f : Fin n → Γ(X, U)),
      (∀ j ∈ J₀, ∃ i, f i = c.coord j) ∧
      IsRegularParameterSystem (X.presheaf.stalk x) n
        (fun i => X.presheaf.germ U x hx (f i)) := by
  obtain ⟨d, f, -, h2, h3, h4⟩ :=
    exists_sections_span_eq_maximalIdeal_with_coords hU c x hx J₀
      (fun j hj => (germ_mem_maximalIdeal_iff hU x hx (c.coord j)).mpr (hJ₀ j hj))
  exact ⟨d, f, h2, h3, h4⟩

end FunctorialResolution.EmbeddedResolution
end
end

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateDivisorRadical
universe u

namespace FunctorialResolution.EmbeddedResolution

private theorem algebraMap_coordPolynomialRing_injective_of_etale (k : Type u) [Field k] (m : ℕ) (S : Type u)
    [CommRing S] [Algebra (CoordPolynomialRing k m) S] [Algebra.Etale (CoordPolynomialRing k m) S]
    [Nontrivial S] : Function.Injective (algebraMap (CoordPolynomialRing k m) S) := by
  refine (injective_iff_map_eq_zero _).mpr ?_
  intro a ha
  by_contra h
  have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := S)
    (mem_nonZeroDivisors_of_ne_zero h)
  have h1 : (1 : S) = 0 := by
    apply hreg
    show a • (1 : S) = a • (0 : S)
    rw [smul_zero, Algebra.smul_def, ha, zero_mul]
  exact one_ne_zero h1

private theorem isRadical_span_singleton_of_isRadical_map_atPrime {S : Type u} [CommRing S] (a : S)
    (h : ∀ (Q : Ideal S) [Q.IsPrime],
      (Ideal.map (algebraMap S (Localization.AtPrime Q)) (Ideal.span ({a} : Set S))).IsRadical) :
    (Ideal.span ({a} : Set S)).IsRadical := by
  intro x hx
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hx
  by_contra hxI
  obtain ⟨K, hKmem⟩ : ∃ K : Ideal S, ∀ b : S, b ∈ K ↔ b * x ∈ Ideal.span ({a} : Set S) :=
    ⟨{ carrier := {s : S | s * x ∈ Ideal.span ({a} : Set S)}
       zero_mem' := by
         show (0 : S) * x ∈ Ideal.span ({a} : Set S)
         rw [zero_mul]
         exact Ideal.zero_mem _
       add_mem' := by
         intro b c hb hc
         show (b + c) * x ∈ Ideal.span ({a} : Set S)
         rw [add_mul]
         exact Ideal.add_mem _ hb hc
       smul_mem' := by
         intro c b hb
         show (c • b) * x ∈ Ideal.span ({a} : Set S)
         rw [smul_eq_mul, mul_assoc]
         exact Ideal.mul_mem_left _ c hb },
     fun b => Iff.rfl⟩
  have hKne : K ≠ ⊤ := by
    intro htop
    have h1 : (1 : S) ∈ K := by rw [htop]; exact Submodule.mem_top
    have h2 := (hKmem 1).mp h1
    rw [one_mul] at h2
    exact hxI h2
  obtain ⟨Q, hQmax, hKQ⟩ := Ideal.exists_le_maximal K hKne
  have hQp : Q.IsPrime := hQmax.isPrime
  have hrad := h Q
  have hpow : (algebraMap S (Localization.AtPrime Q) x) ^ n ∈
      Ideal.map (algebraMap S (Localization.AtPrime Q)) (Ideal.span ({a} : Set S)) := by
    rw [← map_pow]
    exact Ideal.mem_map_of_mem _ hn
  have hxmem : algebraMap S (Localization.AtPrime Q) x ∈
      Ideal.map (algebraMap S (Localization.AtPrime Q)) (Ideal.span ({a} : Set S)) :=
    hrad (Ideal.mem_radical_iff.mpr ⟨n, hpow⟩)
  rw [Ideal.map_span, Set.image_singleton] at hxmem
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hxmem
  obtain ⟨⟨y, s⟩, hys⟩ := IsLocalization.surj (M := Q.primeCompl) c
  have key : algebraMap S (Localization.AtPrime Q) (x * (s : S)) =
      algebraMap S (Localization.AtPrime Q) (a * y) := by
    have h1 : algebraMap S (Localization.AtPrime Q) (x * (s : S))
        = (c * algebraMap S (Localization.AtPrime Q) (s : S)) *
            algebraMap S (Localization.AtPrime Q) a := by
      rw [map_mul, ← hc]; ring
    rw [h1, hys, map_mul]; ring
  obtain ⟨dd, hd⟩ := (IsLocalization.eq_iff_exists Q.primeCompl (Localization.AtPrime Q)).mp key
  have hmem0 : ((dd : S) * (s : S)) * x ∈ Ideal.span ({a} : Set S) := by
    have heq : ((dd : S) * (s : S)) * x = (dd : S) * (x * (s : S)) := by ring
    rw [heq, hd]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right y _ (Ideal.mem_span_singleton_self a))
  have hmem : ((dd : S) * (s : S)) ∈ K := (hKmem _).mpr hmem0
  have hQmem : ((dd : S) * (s : S)) ∈ Q := hKQ hmem
  rcases hQp.mem_or_mem hQmem with hcase | hcase
  · exact dd.2 hcase
  · exact s.2 hcase

theorem etaleChartCoord_injective (k : Type u) [Field k] (m : ℕ) (S : Type u) [CommRing S]
    [Algebra (CoordPolynomialRing k m) S] [Algebra.Etale (CoordPolynomialRing k m) S]
    [Nontrivial S] : Function.Injective (etaleChartCoord k m S) := by
  have hinj := algebraMap_coordPolynomialRing_injective_of_etale k m S
  intro i j hij
  have h : (MvPolynomial.X (ULift.up i) : CoordPolynomialRing k m)
      = MvPolynomial.X (ULift.up j) := by
    apply hinj
    rw [← etaleChartCoord_def, ← etaleChartCoord_def]
    exact hij
  exact congrArg ULift.down (MvPolynomial.X_injective h)

theorem linearIndependent_toCotangent_etaleChartCoord (k : Type u) [Field k] (m : ℕ) (S : Type u)
    [CommRing S] [Algebra (CoordPolynomialRing k m) S] [Algebra.Etale (CoordPolynomialRing k m) S]
    (q : Ideal S) [q.IsPrime] (A : Type u) [CommRing A] [Algebra S A]
    [IsLocalization q.primeCompl A] [IsLocalRing A] (J : Finset (Fin m))
    (hJ : ∀ j ∈ J, etaleChartCoord k m S j ∈ q)
    (hJA : ∀ j ∈ J, algebraMap S A (etaleChartCoord k m S j) ∈ IsLocalRing.maximalIdeal A) :
    LinearIndependent (IsLocalRing.ResidueField A)
      (fun j : { x : Fin m // x ∈ J } =>
          (IsLocalRing.maximalIdeal A).toCotangent
            ⟨algebraMap S A (etaleChartCoord k m S (j : Fin m)), hJA (j : Fin m) j.2⟩ :
        { x : Fin m // x ∈ J } → IsLocalRing.CotangentSpace A) := by
  classical
  have hreg : IsRegularLocalRing A := isRegularLocalRing_of_isLocalization_etale k m S q A
  have hnt : Nontrivial S := by
    rcases subsingleton_or_nontrivial S with hs | hs
    · exfalso
      have := hs
      have h10 : (1 : S) = (0 : S) := Subsingleton.elim _ _
      have hA : (1 : A) = 0 := by
        calc (1 : A) = algebraMap S A 1 := (map_one _).symm
          _ = algebraMap S A 0 := by rw [h10]
          _ = 0 := map_zero _
      exact one_ne_zero hA
    · exact hs
  obtain ⟨d, w, hwq, hwJ, hspan, hdim⟩ :=
    exists_regularSystemOfParameters_containing_etaleChartCoords k m S q A J hJ
  have hwm : ∀ i, algebraMap S A (w i) ∈ IsLocalRing.maximalIdeal A := by
    intro i
    rw [← hspan]
    exact Ideal.subset_span ⟨i, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : Fin d → IsLocalRing.CotangentSpace A,
      ∀ i, y i = (IsLocalRing.maximalIdeal A).toCotangent ⟨algebraMap S A (w i), hwm i⟩ :=
    ⟨_, fun i => rfl⟩
  have key : ∀ (b : A), b ∈ Ideal.span (Set.range fun i => algebraMap S A (w i)) →
      ∀ (hb : b ∈ IsLocalRing.maximalIdeal A),
        (IsLocalRing.maximalIdeal A).toCotangent ⟨b, hb⟩ ∈
          Submodule.span (IsLocalRing.ResidueField A) (Set.range y) := by
    intro b hb0
    have hb' : b ∈ Submodule.span A (Set.range fun i => algebraMap S A (w i)) := hb0
    clear hb0
    induction hb' using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨i, rfl⟩ := hz
        intro hz'
        exact Submodule.subset_span ⟨i, by rw [hy i]⟩
    | zero =>
        intro hz'
        have h0 : (⟨(0 : A), hz'⟩ : IsLocalRing.maximalIdeal A) = 0 := rfl
        rw [h0, map_zero]
        exact Submodule.zero_mem _
    | add z z' hz hz' ihz ihz' =>
        intro hbb
        have hzm : z ∈ IsLocalRing.maximalIdeal A := by rw [← hspan]; exact hz
        have hzm' : z' ∈ IsLocalRing.maximalIdeal A := by rw [← hspan]; exact hz'
        have hsum : (⟨z + z', hbb⟩ : IsLocalRing.maximalIdeal A) = ⟨z, hzm⟩ + ⟨z', hzm'⟩ := rfl
        rw [hsum, map_add (f := _)]
        exact Submodule.add_mem _ (ihz hzm) (ihz' hzm')
    | smul c z hz ih =>
        intro hbb
        have hzm : z ∈ IsLocalRing.maximalIdeal A := by rw [← hspan]; exact hz
        have hsm : (⟨c • z, hbb⟩ : IsLocalRing.maximalIdeal A) = c • ⟨z, hzm⟩ := rfl
        rw [hsm, map_smul, ← IsScalarTower.algebraMap_smul (IsLocalRing.ResidueField A) c]
        exact Submodule.smul_mem _ _ (ih hzm)
  have hspanY : ⊤ ≤ Submodule.span (IsLocalRing.ResidueField A) (Set.range y) := by
    intro v _
    obtain ⟨⟨b, hb⟩, rfl⟩ := Ideal.toCotangent_surjective (IsLocalRing.maximalIdeal A) v
    exact key b (by rw [hspan]; exact hb) hb
  have hcard0 : ((d : ℕ) : WithBot ℕ∞) =
      ((Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.CotangentSpace A) : ℕ) :
        WithBot ℕ∞) :=
    hdim.trans ((IsRegularLocalRing.iff_finrank_cotangentSpace A).mp ‹_›).symm
  have hcard : Fintype.card (Fin d) =
      Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.CotangentSpace A) := by
    rw [Fintype.card_fin]
    exact_mod_cast hcard0
  have hliY : LinearIndependent (IsLocalRing.ResidueField A) y :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspanY hcard
  have hchoice : ∀ j : { x : Fin m // x ∈ J },
      ∃ i : Fin d, w i = etaleChartCoord k m S (j : Fin m) := fun j => hwJ (j : Fin m) j.2
  choose f hf using hchoice
  have hfinj : Function.Injective f := by
    intro j₁ j₂ hjj
    have h1 : etaleChartCoord k m S (j₁ : Fin m) = etaleChartCoord k m S (j₂ : Fin m) := by
      rw [← hf j₁, ← hf j₂, hjj]
    exact Subtype.ext (etaleChartCoord_injective k m S h1)
  have hcomp := hliY.comp f hfinj
  have heq : y ∘ f = fun j : { x : Fin m // x ∈ J } =>
      (IsLocalRing.maximalIdeal A).toCotangent
        ⟨algebraMap S A (etaleChartCoord k m S (j : Fin m)), hJA (j : Fin m) j.2⟩ := by
    funext j
    have h1 : (⟨algebraMap S A (w (f j)), hwm (f j)⟩ : IsLocalRing.maximalIdeal A)
        = ⟨algebraMap S A (etaleChartCoord k m S (j : Fin m)), hJA (j : Fin m) j.2⟩ :=
      Subtype.ext (congrArg (algebraMap S A) (hf j))
    show y (f j) = _
    rw [hy (f j)]
    exact congrArg _ h1
  rw [← heq]
  exact hcomp

theorem isRadical_span_singleton_prod_algebraMap_etaleChartCoord (k : Type u) [Field k] (m : ℕ)
    (S : Type u) [CommRing S] [Algebra (CoordPolynomialRing k m) S]
    [Algebra.Etale (CoordPolynomialRing k m) S] (q : Ideal S) [q.IsPrime] (A : Type u) [CommRing A]
    [Algebra S A] [IsLocalization q.primeCompl A] [IsLocalRing A] (J : Finset (Fin m))
    (hJ : ∀ j ∈ J, etaleChartCoord k m S j ∈ q) :
    (Ideal.span ({∏ j ∈ J, algebraMap S A (etaleChartCoord k m S j)} : Set A)).IsRadical := by
  classical
  have hreg : IsRegularLocalRing A := isRegularLocalRing_of_isLocalization_etale k m S q A
  have hJA : ∀ j ∈ J, algebraMap S A (etaleChartCoord k m S j) ∈ IsLocalRing.maximalIdeal A := by
    intro j hj
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff A q
      (etaleChartCoord k m S j)).mpr (hJ j hj)
  have hli := linearIndependent_toCotangent_etaleChartCoord k m S q A J hJ hJA
  have hmain := _root_.IsRegularLocalRing.isRadical_span_singleton_prod
    (fun j : { x : Fin m // x ∈ J } => algebraMap S A (etaleChartCoord k m S (j : Fin m)))
    (fun j => hJA (j : Fin m) j.2) hli
  rw [← Finset.prod_coe_sort J (fun j => algebraMap S A (etaleChartCoord k m S j))]
  exact hmain

theorem isRadical_map_span_singleton_prod_etaleChartCoord (k : Type u) [Field k] (m : ℕ)
    (S : Type u) [CommRing S] [Algebra (CoordPolynomialRing k m) S]
    [Algebra.Etale (CoordPolynomialRing k m) S] (q : Ideal S) [q.IsPrime] (A : Type u) [CommRing A]
    [Algebra S A] [IsLocalization q.primeCompl A] [IsLocalRing A] (T : Finset (Fin m)) :
    (Ideal.map (algebraMap S A)
      (Ideal.span ({∏ j ∈ T, etaleChartCoord k m S j} : Set S))).IsRadical := by
  classical
  obtain ⟨J, hJdef⟩ : ∃ J : Finset (Fin m),
      J = T.filter (fun j => etaleChartCoord k m S j ∈ q) := ⟨_, rfl⟩
  have hJsub : J ⊆ T := by rw [hJdef]; exact Finset.filter_subset _ _
  have hJ : ∀ j ∈ J, etaleChartCoord k m S j ∈ q := by
    intro j hj
    rw [hJdef] at hj
    exact (Finset.mem_filter.mp hj).2
  have hunit : IsUnit (∏ j ∈ T \ J, algebraMap S A (etaleChartCoord k m S j)) := by
    refine Finset.prod_induction _ _ (fun u v hu hv => hu.mul hv) isUnit_one ?_
    intro j hj
    have h1 := Finset.mem_sdiff.mp hj
    have hj' : etaleChartCoord k m S j ∉ q := by
      intro hmem
      exact h1.2 (by rw [hJdef]; exact Finset.mem_filter.mpr ⟨h1.1, hmem⟩)
    exact IsLocalization.map_units A (⟨etaleChartCoord k m S j, hj'⟩ : q.primeCompl)
  have hsplit : ∏ j ∈ T, algebraMap S A (etaleChartCoord k m S j)
      = (∏ j ∈ T \ J, algebraMap S A (etaleChartCoord k m S j)) *
        ∏ j ∈ J, algebraMap S A (etaleChartCoord k m S j) := by
    rw [← Finset.prod_union Finset.sdiff_disjoint, Finset.sdiff_union_of_subset hJsub]
  rw [Ideal.map_span, Set.image_singleton, map_prod, hsplit,
    Ideal.span_singleton_mul_left_unit hunit _]
  exact isRadical_span_singleton_prod_algebraMap_etaleChartCoord k m S q A J hJ

theorem isRadical_span_singleton_prod_etaleChartCoord (k : Type u) [Field k] (m : ℕ) (S : Type u)
    [CommRing S] [Algebra (CoordPolynomialRing k m) S] [Algebra.Etale (CoordPolynomialRing k m) S]
    (T : Finset (Fin m)) :
    (Ideal.span ({∏ j ∈ T, etaleChartCoord k m S j} : Set S)).IsRadical := by
  refine isRadical_span_singleton_of_isRadical_map_atPrime (∏ j ∈ T, etaleChartCoord k m S j) ?_
  intro Q hQ
  have : Q.IsPrime := hQ
  exact isRadical_map_span_singleton_prod_etaleChartCoord k m S Q (Localization.AtPrime Q) T

end FunctorialResolution.EmbeddedResolution
end
