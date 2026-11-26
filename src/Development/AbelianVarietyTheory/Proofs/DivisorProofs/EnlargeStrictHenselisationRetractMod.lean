module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNoetherianModelOfDivisorOfConstants
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalRingModTEmbedsStrictHenselian
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomToFieldFactorsAlgClosedSubfield
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomToFieldFactorsAlgClosedSubfield
open IsLocalRing

open scoped TensorProduct

namespace GlobalTheory

theorem etale_hom_to_field_lands_in_algClosed_subfield
    (A B K L : Type) [CommRing A] [IsLocalRing A] [CommRing B] [Algebra A B]
    [Algebra.Etale A B] [Field K] [IsAlgClosed K] [Field L]
    (α : A →+* K) (ι : K →+* L) (β : B →+* L) :
    (∀ a ∈ maximalIdeal A, α a = 0) → β.comp (algebraMap A B) = ι.comp α →
      ∃ ψ : B →+* K, ψ.comp (algebraMap A B) = α ∧ ι.comp ψ = β := by
  intro _ hβ
  letI : Algebra A K := α.toAlgebra
  letI : Algebra K L := ι.toAlgebra
  letI : Algebra A L := (ι.comp α).toAlgebra
  haveI : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let g : B →ₐ[A] L :=
    { β with
      commutes' := fun a => congrArg (fun f : A →+* L => f a) hβ }
  let f : K ⊗[A] B →ₐ[K] L :=
    Algebra.TensorProduct.lift (Algebra.ofId K L) g (fun _ _ => Commute.all _ _)
  haveI : Module.Finite K (K ⊗[A] B) := Algebra.FormallyUnramified.finite_of_free K (K ⊗[A] B)
  haveI : Algebra.IsIntegral K (K ⊗[A] B) := Algebra.IsIntegral.of_finite K _
  haveI : Algebra.IsIntegral K f.range :=
    Algebra.IsIntegral.of_surjective f.rangeRestrict (AlgHom.rangeRestrict_surjective f)
  have hsurj : Function.Surjective (algebraMap K f.range) := by
    intro y
    have hy : IsIntegral K (y : L) := (Algebra.IsIntegral.isIntegral y).map f.range.val
    obtain ⟨k, hk⟩ := minpoly.mem_range_of_degree_eq_one K (y : L)
      (IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hy))
    exact ⟨k, Subtype.ext hk⟩
  let e : K ≃+* f.range :=
    RingEquiv.ofBijective (algebraMap K f.range) ⟨(algebraMap K f.range).injective, hsurj⟩
  let ψ : B →+* K :=
    e.symm.toRingHom.comp (f.rangeRestrict.toRingHom.comp
      (Algebra.TensorProduct.includeRight : B →ₐ[A] K ⊗[A] B).toRingHom)
  have hι : ∀ x, ι (ψ x) = β x := by
    intro x
    have h1 : (algebraMap K f.range (ψ x) : L) = ι (ψ x) := rfl
    have h2 : algebraMap K f.range (ψ x) = f.rangeRestrict (1 ⊗ₜ x) := by
      simp only [ψ, e, RingHom.comp_apply]
      exact (RingEquiv.ofBijective (algebraMap K f.range) _).apply_symm_apply _
    rw [← h1, h2]
    simp [f, g]
  refine ⟨ψ, ?_, ?_⟩
  · ext a
    apply ι.injective
    rw [RingHom.comp_apply, hι]
    exact congrArg (fun f : A →+* L => f a) hβ
  · ext x
    exact hι x

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomToFieldFactorsAlgClosedSubfieldStatement
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_hom_to_field_factors_algClosed_subfield : ∀ (A B K L : Type) [CommRing A] [IsLocalRing A] [CommRing B] [Algebra A B] [Algebra.Etale A B] [Field K] [IsAlgClosed K] [Field L] (α : A →+* K) (ι : K →+* L) (β : B →+* L), (∀ a ∈ maximalIdeal A, α a = 0) → β.comp (algebraMap A B) = ι.comp α → ∃ ψ : B →+* K, ψ.comp (algebraMap A B) = α ∧ ι.comp ψ = β := by
  first | (exact @GlobalTheory.etale_hom_to_field_lands_in_algClosed_subfield) | (exact GlobalTheory.etale_hom_to_field_lands_in_algClosed_subfield) | (intros; apply GlobalTheory.etale_hom_to_field_lands_in_algClosed_subfield  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalRingModTEmbedsStrictHenselian
open IsLocalRing Polynomial

noncomputable section
namespace GlobalTheory.FibreRetract

theorem exists_section_mod (T O : Type) [CommRing T] [IsLocalRing T] [HenselianLocalRing T]
    [IsAlgClosed (ResidueField T)] [CommRing O] [HenselianLocalRing O] [Algebra T O]
    [IsLocalHom (algebraMap T O)] (I : Ideal O) (hI : I ≠ ⊤)
    (A : Type) [CommRing A] [IsLocalRing A] (i : A →+* T) [IsLocalHom i]
    (B : Type) [CommRing B] [Algebra A B] [Algebra.Etale A B] (b : B →+* O ⧸ I)
    (hb : b.comp (algebraMap A B) = ((Ideal.Quotient.mk I).comp (algebraMap T O)).comp i) :
    ∃ s : B →+* T, s.comp (algebraMap A B) = i ∧
      ((Ideal.Quotient.mk I).comp (algebraMap T O)).comp s = b := by
  haveI : Nontrivial (O ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  haveI : IsLocalRing (O ⧸ I) := .of_surjective' _ Ideal.Quotient.mk_surjective
  haveI : HenselianLocalRing (O ⧸ I) := GlobalTheory.henselianLocalRing_of_finite O (O ⧸ I)
  set π : T →+* O ⧸ I := (Ideal.Quotient.mk I).comp (algebraMap T O) with hπ
  haveI : IsLocalHom (Ideal.Quotient.mk I) := isLocalHom_of_le_jacobson_bot I
    (by rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]; exact le_maximalIdeal hI)
  haveI : IsLocalHom π := inferInstance
  have het : (algebraMap A B).Etale := RingHom.etale_algebraMap.mpr inferInstance
  obtain ⟨ψ, hψ1, hψ2⟩ := GlobalTheory.T.etale_hom_to_field_factors_algClosed_subfield A B (ResidueField T) (ResidueField (O ⧸ I))
    ((residue T).comp i) (ResidueField.map π) ((residue (O ⧸ I)).comp b)
    (fun a ha => by
      simp only [RingHom.comp_apply, residue_eq_zero_iff]
      exact map_nonunit i a ha)
    (by
      ext a
      have := DFunLike.congr_fun hb a
      simp only [RingHom.comp_apply] at this ⊢
      rw [this, ResidueField.map_residue])
  obtain ⟨s, hs1, hs2⟩ := GlobalTheory.NCyc.StrictLocLift.lift_exists (algebraMap A B) het i ψ hψ1
  refine ⟨s, hs1, ?_⟩
  refine GlobalTheory.NCyc.StrictLocLift.lift_unique (algebraMap A B) het (π.comp i) _ _ ?_ hb ?_
  · rw [RingHom.comp_assoc, hs1]
  · ext x
    have h2 := DFunLike.congr_fun hψ2 x
    have h3 := DFunLike.congr_fun hs2 x
    simp only [RingHom.comp_apply] at h2 h3 ⊢
    rw [← h2, ← h3, ResidueField.map_residue]

end GlobalTheory.FibreRetract

namespace GlobalTheory.FibreRetract

theorem fibre_retract : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [HenselianLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    IsLocalHom (algebraMap T O) → algebraMap (Polynomial T) O Polynomial.X ∈ maximalIdeal O →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T), Function.Injective i → IsLocalHom i →
    ∀ (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA] (j : EA →+* O),
      j.comp (algebraMap (Polynomial A) EA) = (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) →
    ∃ (A₁ : Type) (_ : CommRing A₁) (_ : IsDomain A₁) (_ : IsLocalRing A₁) (_ : IsNoetherianRing A₁)
      (_ : IsIntegrallyClosed A₁) (_ : Algebra.EssFiniteType ℤ A₁) (f : A →+* A₁) (i₁ : A₁ →+* T) (e : EA →+* A₁),
      Function.Injective i₁ ∧ IsLocalHom i₁ ∧ i₁.comp f = i ∧
      e.comp (algebraMap (Polynomial A) EA) = f.comp (Polynomial.evalRingHom 0) ∧
      ∀ x : EA, algebraMap T O (i₁ (e x)) - j x ∈ Ideal.span {algebraMap (Polynomial T) O Polynomial.X} := by
  intro T O _ _ _ _ _ _ _ _ hT hTO ht A _ _ _ _ _ _ i hi hil EA _ _ _ _ _ j hj
  obtain ⟨hTh, hTac, -⟩ := GlobalTheory.AbsIntClosedLocal.henselian_isAlgClosed_pow_surj T ⟨inferInstance, hT⟩
  set I : Ideal O := Ideal.span {algebraMap (Polynomial T) O Polynomial.X} with hIdef
  have hI : I ≠ ⊤ := fun h => (maximalIdeal.isMaximal O).ne_top (top_le_iff.mp
    (h ▸ (Ideal.span_singleton_le_iff_mem _).mpr ht))
  letI : Algebra (Polynomial A) A := (Polynomial.evalRingHom 0).toAlgebra
  let B := TensorProduct (Polynomial A) A EA
  have hC : ∀ c : T, algebraMap (Polynomial T) O (Polynomial.C c) = algebraMap T O c := fun c => by
    rw [IsScalarTower.algebraMap_apply T (Polynomial T) O c, Polynomial.algebraMap_eq]
  let φ : Polynomial A →+* O ⧸ I :=
    (Ideal.Quotient.mk I).comp ((algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i))
  letI : Algebra (Polynomial A) (O ⧸ I) := φ.toAlgebra
  let f₁ : A →ₐ[Polynomial A] O ⧸ I :=
    { toRingHom := ((Ideal.Quotient.mk I).comp (algebraMap T O)).comp i
      commutes' := fun p => by
        change Ideal.Quotient.mk I (algebraMap T O (i (p.eval 0))) =
          Ideal.Quotient.mk I (algebraMap (Polynomial T) O (p.map i))
        rw [Ideal.Quotient.eq]
        obtain ⟨q, hq⟩ := Polynomial.X_dvd_sub_C (p := p.map i)
        have h0 : (p.map i).coeff 0 = i (p.eval 0) := by
          rw [Polynomial.coeff_map, Polynomial.coeff_zero_eq_eval_zero]
        rw [h0] at hq
        rw [← hC, ← map_sub, ← neg_sub, hq, map_neg, map_mul]
        exact I.neg_mem (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)) }
  let f₂ : EA →ₐ[Polynomial A] O ⧸ I :=
    { toRingHom := (Ideal.Quotient.mk I).comp j
      commutes' := fun p => by
        change Ideal.Quotient.mk I (j (algebraMap (Polynomial A) EA p)) = φ p
        have := DFunLike.congr_fun hj p
        simp only [RingHom.comp_apply] at this
        simp only [φ, RingHom.comp_apply, this, Polynomial.coe_mapRingHom] }
  let b : B →+* O ⧸ I := (Algebra.TensorProduct.lift f₁ f₂ (fun _ _ => Commute.all _ _)).toRingHom
  have hb : b.comp (algebraMap A B) = ((Ideal.Quotient.mk I).comp (algebraMap T O)).comp i := by
    ext a
    change b (algebraMap A B a) = _
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply]
    exact (Algebra.TensorProduct.lift_tmul f₁ f₂ _ a 1).trans (by rw [map_one, mul_one]; rfl)
  haveI := hTh; haveI := hTac
  obtain ⟨s, hs1, hs2⟩ := exists_section_mod T O I hI A i B b hb
  let P : Ideal B := (maximalIdeal T).comap s
  haveI hP : P.IsPrime := Ideal.comap_isPrime s (maximalIdeal T)
  let A₁ := Localization.AtPrime P
  have hunit : ∀ y : P.primeCompl, IsUnit (s y) := fun y => by
    have hy : (y : B) ∉ P := y.2
    by_contra h
    exact hy ((IsLocalRing.mem_maximalIdeal _).mpr h)
  let i₁ : A₁ →+* T := IsLocalization.lift hunit
  have hi₁ : i₁.comp (algebraMap B A₁) = s := IsLocalization.lift_comp hunit
  let f : A →+* A₁ := algebraMap A A₁
  let e : EA →+* A₁ := (algebraMap B A₁).comp
    (Algebra.TensorProduct.includeRight : EA →ₐ[Polynomial A] B).toRingHom
  obtain ⟨hdom, hic⟩ := GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_etale A P A₁
  haveI := hdom
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  haveI : IsNoetherianRing A₁ := IsLocalization.isNoetherianRing P.primeCompl A₁ inferInstance
  haveI : Algebra.EssFiniteType ℤ B := Algebra.EssFiniteType.comp ℤ A B
  haveI : Algebra.EssFiniteType B A₁ := Algebra.EssFiniteType.of_isLocalization A₁ P.primeCompl
  haveI : Algebra.EssFiniteType ℤ A₁ := Algebra.EssFiniteType.comp ℤ B A₁
  have hcomp : i₁.comp f = i := by
    rw [show f = (algebraMap B A₁).comp (algebraMap A B) from IsScalarTower.algebraMap_eq A B A₁,
      ← RingHom.comp_assoc, hi₁, hs1]
  have hloc : IsLocalHom i₁ := ⟨fun x hx => by
    obtain ⟨⟨b', y⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl x
    rw [IsLocalization.AtPrime.isUnit_mk'_iff]
    have h1 : i₁ (IsLocalization.mk' A₁ b' y) * s y = s b' := by
      rw [← hi₁, RingHom.comp_apply, RingHom.comp_apply, ← map_mul, IsLocalization.mk'_spec]
    have h2 : IsUnit (s b') := h1 ▸ hx.mul (hunit y)
    intro hb'
    exact (IsLocalRing.mem_maximalIdeal _).mp hb' h2⟩
  haveI : Algebra.QuasiFinite A B := inferInstance
  haveI : Algebra.QuasiFinite A A₁ := inferInstance
  have hinj : Function.Injective i₁ := by
    have h1 : (RingHom.ker i₁).comap f = ⊥ := by
      rw [RingHom.comap_ker, hcomp]; exact (RingHom.injective_iff_ker_eq_bot i).mp hi
    have h2 : (⊥ : Ideal A₁).comap f = ⊥ := eq_bot_iff.mpr fun a ha => h1 ▸ Ideal.comap_mono bot_le ha
    haveI : (RingHom.ker i₁).IsPrime := RingHom.ker_isPrime i₁
    have := Algebra.QuasiFinite.eq_of_le_of_under_eq (R := A) (⊥ : Ideal A₁) (RingHom.ker i₁) bot_le
      (by rw [Ideal.under, Ideal.under]; exact h2.trans h1.symm)
    exact (RingHom.injective_iff_ker_eq_bot i₁).mpr this.symm
  refine ⟨A₁, inferInstance, hdom, inferInstance, inferInstance, hic, ?_, f, i₁, e, hinj,
    hloc, hcomp, ?_, fun x => ?_⟩
  · convert ‹Algebra.EssFiniteType ℤ A₁› using 1
    exact Subsingleton.elim _ _
  · refine RingHom.ext fun p => ?_
    change algebraMap B A₁ (Algebra.TensorProduct.includeRight (algebraMap (Polynomial A) EA p)) =
      algebraMap A A₁ (p.eval 0)
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply A B A₁]
    rfl
  · have h3 := DFunLike.congr_fun hs2 (Algebra.TensorProduct.includeRight x)
    have h4 : i₁ (e x) = s (Algebra.TensorProduct.includeRight x) := by
      rw [← hi₁]; rfl
    rw [h4]
    apply Ideal.Quotient.eq.mp
    refine h3.trans ?_
    change Algebra.TensorProduct.lift f₁ f₂ _ ((1 : A) ⊗ₜ x) = _
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    rfl

end GlobalTheory.FibreRetract
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalRingModTEmbedsStrictHenselianStatement
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localRing_mod_t_embeds_strictHenselian : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [HenselianLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    IsLocalHom (algebraMap T O) → algebraMap (Polynomial T) O Polynomial.X ∈ maximalIdeal O →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T), Function.Injective i → IsLocalHom i →
    ∀ (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA] (j : EA →+* O),
      j.comp (algebraMap (Polynomial A) EA) = (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) →
    ∃ (A₁ : Type) (_ : CommRing A₁) (_ : IsDomain A₁) (_ : IsLocalRing A₁) (_ : IsNoetherianRing A₁)
      (_ : IsIntegrallyClosed A₁) (_ : Algebra.EssFiniteType ℤ A₁) (f : A →+* A₁) (i₁ : A₁ →+* T) (e : EA →+* A₁),
      Function.Injective i₁ ∧ IsLocalHom i₁ ∧ i₁.comp f = i ∧
      e.comp (algebraMap (Polynomial A) EA) = f.comp (Polynomial.evalRingHom 0) ∧
      ∀ x : EA, algebraMap T O (i₁ (e x)) - j x ∈ Ideal.span {algebraMap (Polynomial T) O Polynomial.X} := by
  first | (exact @GlobalTheory.FibreRetract.fibre_retract) | (exact GlobalTheory.FibreRetract.fibre_retract) | (intros; apply GlobalTheory.FibreRetract.fibre_retract  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FittingDatumBaseChangeLocalEnlargement
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FittingDatumBaseChangeLocalEnlargement
open IsLocalRing Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.EnlargeBaseChange

end GlobalTheory.EnlargeBaseChange

namespace GlobalTheory.EnlargeBaseChange

open IsLocalRing Polynomial in
open scoped TensorProduct in
private theorem exists_ringHom_tensor_of_comp_eq {R S E : Type} [CommRing R] [CommRing S]
    [CommRing E] [Algebra R S] [Algebra R E] (Z : Type) [CommRing Z] (u : S →+* Z) (v : E →+* Z)
    (h : u.comp (algebraMap R S) = v.comp (algebraMap R E)) :
    ∃ w : S ⊗[R] E →+* Z, w.comp (algebraMap S (S ⊗[R] E)) = u ∧
      w.comp (Algebra.TensorProduct.includeRight.toRingHom : E →+* S ⊗[R] E) = v := by
  letI : Algebra R Z := (v.comp (algebraMap R E)).toAlgebra
  let u' : S →ₐ[R] Z := { u with commutes' := fun r => RingHom.congr_fun h r }
  let v' : E →ₐ[R] Z := { v with commutes' := fun _ => rfl }
  refine ⟨(Algebra.TensorProduct.lift u' v' fun _ _ => Commute.all _ _).toRingHom, ?_, ?_⟩
  · refine RingHom.ext fun s => ?_
    simp [Algebra.TensorProduct.algebraMap_apply, u', v']
  · refine RingHom.ext fun e => ?_
    simp [u', v']

open IsLocalRing Polynomial in
open scoped TensorProduct in
private theorem includeRight_comp_algebraMap_eq {R S E : Type} [CommRing R] [CommRing S]
    [CommRing E] [Algebra R S] [Algebra R E] :
    (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := E)).toRingHom.comp
        (algebraMap R E) = (algebraMap S (S ⊗[R] E)).comp (algebraMap R S) := by
  ext r
  simp [Algebra.TensorProduct.algebraMap_apply]

open IsLocalRing Polynomial in
open scoped TensorProduct in
private theorem tensorProduct_ringHom_ext_of_comp_eq {R S E Z : Type} [CommRing R] [CommRing S] [CommRing E]
    [CommRing Z] [Algebra R S] [Algebra R E] (w₁ w₂ : S ⊗[R] E →+* Z)
    (h₁ : w₁.comp (algebraMap S (S ⊗[R] E)) = w₂.comp (algebraMap S (S ⊗[R] E)))
    (h₂ : w₁.comp (Algebra.TensorProduct.includeRight.toRingHom : E →+* S ⊗[R] E) =
      w₂.comp (Algebra.TensorProduct.includeRight.toRingHom : E →+* S ⊗[R] E)) : w₁ = w₂ := by
  refine RingHom.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul s e =>
    have hs := RingHom.congr_fun h₁ s
    have he : w₁ ((1 : S) ⊗ₜ[R] e) = w₂ ((1 : S) ⊗ₜ[R] e) := RingHom.congr_fun h₂ e
    simp only [RingHom.comp_apply, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply] at hs
    rw [show s ⊗ₜ[R] e = (s ⊗ₜ[R] (1 : E)) * ((1 : S) ⊗ₜ[R] e) by simp, map_mul, map_mul, hs, he]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]


open IsLocalRing Polynomial in
open scoped TensorProduct in
theorem _root_.GlobalTheory.EnlargeBaseChange.fits_baseChange : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], _root_.GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = _root_.GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T)
      (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O)
      (ψA : _root_.GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* _root_.GlobalTheory.LocAcyc.GenFib T O)
      (DA : Type) [CommRing DA] [Algebra (_root_.GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[_root_.GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    _root_.GlobalTheory.KeyOriginEnlarge.Fits T O q A i EA QA jA ψA DA actA →
    ∀ (A₁ : Type) [CommRing A₁] [IsDomain A₁] [IsLocalRing A₁] (f : A →+* A₁) (i₁ : A₁ →+* T),
    Function.Injective i₁ → IsLocalHom i₁ → i₁.comp f = i →
    ∃ (EA' : Type) (_ : CommRing EA') (_ : Algebra (Polynomial A₁) EA') (_ : Algebra A₁ EA')
      (_ : IsScalarTower A₁ (Polynomial A₁) EA') (_ : Algebra.Etale (Polynomial A₁) EA')
      (QA' : Ideal EA') (_ : QA'.IsPrime) (jA' : Localization.AtPrime QA' →+* O)
      (ψA' : _root_.GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA') →+* _root_.GlobalTheory.LocAcyc.GenFib T O)
      (DA' : Type) (_ : CommRing DA') (_ : Algebra (_root_.GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA')) DA')
      (actA' : Multiplicative (ZMod q) →* (DA' ≃ₐ[_root_.GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA')] DA')),
      _root_.GlobalTheory.KeyOriginEnlarge.Fits T O q A₁ i₁ EA' QA' jA' ψA' DA' actA' ∧
      (∃ (β : _root_.GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* _root_.GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA'))
        (h : DA →+* DA'), ψA'.comp β = ψA ∧
        h.comp (algebraMap (_root_.GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) =
          (algebraMap (_root_.GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA')) DA').comp β) ∧
      ∃ γ : EA →+* EA',
        γ.comp (algebraMap (Polynomial A) EA) = (algebraMap (Polynomial A₁) EA').comp (Polynomial.mapRingHom f) ∧
        jA'.comp ((algebraMap EA' (Localization.AtPrime QA')).comp γ) = jA.comp (algebraMap EA (Localization.AtPrime QA)) ∧
        QA' = (maximalIdeal O).comap (jA'.comp (algebraMap EA' (Localization.AtPrime QA'))) ∧
        (∀ (Z : Type) [CommRing Z] (u : Polynomial A₁ →+* Z) (v : EA →+* Z),
          u.comp (Polynomial.mapRingHom f) = v.comp (algebraMap (Polynomial A) EA) →
          ∃ w : EA' →+* Z, w.comp (algebraMap (Polynomial A₁) EA') = u ∧ w.comp γ = v) ∧
        (∀ (Z : Type) [CommRing Z] (w₁ w₂ : EA' →+* Z),
          w₁.comp (algebraMap (Polynomial A₁) EA') = w₂.comp (algebraMap (Polynomial A₁) EA') →
          w₁.comp γ = w₂.comp γ → w₁ = w₂) := by
  intro T O _ _ _ _ _ _ _ _ _ P _ φ hφ hφs hP q hq _ A _ _ _ _ _ _ i EA _ _ _ _ _ QA _ jA ψA DA _ _
    actA hfits A₁ _ _ _ f i₁ hi₁ hloc hcomp
  obtain ⟨hi, -, hqA, -, hjA, hψA, htors⟩ := hfits
  haveI : IsLocalHom φ := hφs.2.2.1
  letI : Algebra A[X] A₁[X] := (Polynomial.mapRingHom f).toAlgebra

  have huv : ((algebraMap T[X] O).comp (Polynomial.mapRingHom i₁)).comp (algebraMap A[X] A₁[X]) =
      (jA.comp (algebraMap EA (Localization.AtPrime QA))).comp (algebraMap A[X] EA) := by
    rw [RingHom.comp_assoc, RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, hjA,
      RingHom.algebraMap_toAlgebra, Polynomial.mapRingHom_comp, hcomp]
  obtain ⟨g, hgu, hgv⟩ := exists_ringHom_tensor_of_comp_eq O _ _ huv
  let QA' : Ideal (A₁[X] ⊗[A[X]] EA) := (maximalIdeal O).comap g
  have hmemQ : ∀ z, z ∈ QA' ↔ ¬IsUnit (g z) := fun z => by
    simp [QA', Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  haveI : QA'.IsPrime := Ideal.comap_isPrime _ _
  let jA' : Localization.AtPrime QA' →+* O :=
    IsLocalization.lift (M := QA'.primeCompl) (g := g) fun s => by
      by_contra hs
      exact s.2 ((hmemQ s).2 hs)
  have hjA'comp : jA'.comp (algebraMap _ (Localization.AtPrime QA')) = g :=
    IsLocalization.lift_comp _
  have hjA'g : ∀ z, jA' (algebraMap _ (Localization.AtPrime QA') z) = g z := fun z =>
    RingHom.congr_fun hjA'comp z
  have hgγ : ∀ e, g (Algebra.TensorProduct.includeRight e) =
      jA (algebraMap EA (Localization.AtPrime QA) e) := fun e => RingHom.congr_fun hgv e
  have hgA₁ : ∀ a : A₁, g (algebraMap A₁ _ a) = algebraMap T O (i₁ a) := fun a => by
    have := RingHom.congr_fun hgu (Polynomial.C a)
    simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C] at this
    rw [IsScalarTower.algebraMap_apply A₁ A₁[X] (A₁[X] ⊗[A[X]] EA), Polynomial.algebraMap_eq,
      IsScalarTower.algebraMap_apply T T[X] O, Polynomial.algebraMap_eq]
    exact this
  have hjA'A₁ : ∀ a : A₁, jA' (algebraMap A₁ (Localization.AtPrime QA') a) = algebraMap T O (i₁ a) :=
    fun a => by
      rw [IsScalarTower.algebraMap_apply A₁ (A₁[X] ⊗[A[X]] EA) (Localization.AtPrime QA'), hjA'g, hgA₁]
  have hunitT : ∀ a : A₁, a ∈ nonZeroDivisors A₁ →
      IsUnit (algebraMap O (_root_.GlobalTheory.LocAcyc.GenFib T O) (algebraMap T O (i₁ a))) := fun a ha =>
    IsLocalization.map_units (M := Algebra.algebraMapSubmonoid O (nonZeroDivisors T))
      (_root_.GlobalTheory.LocAcyc.GenFib T O)
      ⟨algebraMap T O (i₁ a), ⟨i₁ a, mem_nonZeroDivisors_of_ne_zero
        ((map_ne_zero_iff i₁ hi₁).2 (nonZeroDivisors.ne_zero ha)), rfl⟩⟩
  haveI hlocA₁ : IsLocalization
      (Algebra.algebraMapSubmonoid (Localization.AtPrime QA') (nonZeroDivisors A₁))
      (_root_.GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA')) := by
    unfold _root_.GlobalTheory.LocAcyc.GenFib
    exact Localization.isLocalization
  let ψA' : _root_.GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA') →+* _root_.GlobalTheory.LocAcyc.GenFib T O :=
    IsLocalization.lift (M := Algebra.algebraMapSubmonoid (Localization.AtPrime QA') (nonZeroDivisors A₁))
      (g := (algebraMap O (_root_.GlobalTheory.LocAcyc.GenFib T O)).comp jA') fun s => by
        obtain ⟨a, ha, hs⟩ := s.2
        rw [RingHom.comp_apply, ← hs, hjA'A₁]
        exact hunitT a ha
  have hψA'comp : ψA'.comp (algebraMap _ (_root_.GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA'))) =
      (algebraMap O (_root_.GlobalTheory.LocAcyc.GenFib T O)).comp jA' := IsLocalization.lift_comp _
  have hψA'alg : ∀ y, ψA' (algebraMap _ (_root_.GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA')) y) =
      algebraMap O (_root_.GlobalTheory.LocAcyc.GenFib T O) (jA' y) := fun y => RingHom.congr_fun hψA'comp y
  let ℓ : Localization.AtPrime QA →+* Localization.AtPrime QA' :=
    IsLocalization.lift (M := QA.primeCompl)
      (g := (algebraMap _ (Localization.AtPrime QA')).comp
        (Algebra.TensorProduct.includeRight.toRingHom : EA →+* A₁[X] ⊗[A[X]] EA)) fun s => by
        refine IsLocalization.map_units (M := QA'.primeCompl) (Localization.AtPrime QA')
          (⟨Algebra.TensorProduct.includeRight (s : EA), ?_⟩ : QA'.primeCompl)
        rw [Ideal.mem_primeCompl_iff, hmemQ, not_not, hgγ]
        exact (IsLocalization.map_units (Localization.AtPrime QA) s).map jA
  have hℓ : ∀ e, ℓ (algebraMap EA (Localization.AtPrime QA) e) =
      algebraMap (A₁[X] ⊗[A[X]] EA) (Localization.AtPrime QA')
        (Algebra.TensorProduct.includeRight (R := A[X]) (A := A₁[X]) e) := fun e =>
    IsLocalization.lift_eq _ e
  have hγ1 : (Algebra.TensorProduct.includeRight.toRingHom : EA →+* A₁[X] ⊗[A[X]] EA).comp
      (algebraMap A[X] EA) = (algebraMap A₁[X] (A₁[X] ⊗[A[X]] EA)).comp (Polynomial.mapRingHom f) :=
    includeRight_comp_algebraMap_eq
  have hγC : ∀ a : A, Algebra.TensorProduct.includeRight (R := A[X]) (A := A₁[X]) (algebraMap A EA a) =
      algebraMap A₁ (A₁[X] ⊗[A[X]] EA) (f a) := fun a => by
    rw [IsScalarTower.algebraMap_apply A A[X] EA, Polynomial.algebraMap_eq,
      IsScalarTower.algebraMap_apply A₁ A₁[X] (A₁[X] ⊗[A[X]] EA), Polynomial.algebraMap_eq]
    have := RingHom.congr_fun hγ1 (Polynomial.C a)
    simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C,
      AlgHom.coe_toRingHom] at this
    exact this
  let β : _root_.GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+*
      _root_.GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA') :=
    IsLocalization.lift (M := Algebra.algebraMapSubmonoid (Localization.AtPrime QA) (nonZeroDivisors A))
      (g := (algebraMap _ (_root_.GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA'))).comp ℓ) fun s => by
        obtain ⟨a, ha, hs⟩ := s.2
        rw [RingHom.comp_apply, ← hs, IsScalarTower.algebraMap_apply A EA (Localization.AtPrime QA),
          hℓ, hγC, ← IsScalarTower.algebraMap_apply A₁ (A₁[X] ⊗[A[X]] EA) (Localization.AtPrime QA')]
        refine IsLocalization.map_units
          (M := Algebra.algebraMapSubmonoid (Localization.AtPrime QA') (nonZeroDivisors A₁)) _
          ⟨_, ⟨f a, mem_nonZeroDivisors_of_ne_zero fun h0 => ?_, rfl⟩⟩
        apply nonZeroDivisors.ne_zero ha
        apply hi
        rw [map_zero, ← hcomp, RingHom.comp_apply, h0, map_zero]
  have hβalg : ∀ y, β (algebraMap _ (_root_.GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) y) =
      algebraMap _ (_root_.GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA')) (ℓ y) := fun y =>
    IsLocalization.lift_eq _ y
  letI : Algebra (_root_.GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA))
      (_root_.GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA')) := β.toAlgebra
  have htors' : _root_.GlobalTheory.LocAcyc.IsZModTorsor _ DA q actA := by
    unfold _root_.GlobalTheory.KeyOriginCut.IsZTorsor at htors
    unfold _root_.GlobalTheory.LocAcyc.IsZModTorsor
    exact htors
  obtain ⟨act', -, hact'⟩ := _root_.GlobalTheory.LocAcyc.isZModTorsor_baseChange
    (_root_.GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA))
    (_root_.GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA')) DA q hq actA htors'
  refine ⟨A₁[X] ⊗[A[X]] EA, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    QA', inferInstance, jA', ψA',
    _root_.GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA') ⊗[_root_.GlobalTheory.LocAcyc.GenFib A
      (Localization.AtPrime QA)] DA, inferInstance, inferInstance, act', ?_,
    ⟨β, Algebra.TensorProduct.includeRight.toRingHom, ?_, includeRight_comp_algebraMap_eq⟩,
    Algebra.TensorProduct.includeRight.toRingHom, hγ1, ?_, ?_, ?_, ?_⟩
  · unfold _root_.GlobalTheory.KeyOriginEnlarge.Fits
    refine ⟨hi₁, hloc, by simpa using hqA.map f, ?_, ?_, hψA'comp, ?_⟩
    · have hO : (maximalIdeal O).comap (algebraMap T[X] O) = _root_.GlobalTheory.KeyOriginCut.originIdeal T := by
        rw [← hφ, ← Ideal.comap_comap, IsLocalRing.maximalIdeal_comap φ, ← hP]
        exact IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime P) P
      show ((maximalIdeal O).comap g).comap _ = _
      rw [Ideal.comap_comap, hgu, ← Ideal.comap_comap, hO]
      exact _root_.GlobalTheory.VertUnitsNoeth.comap_originIdeal' A₁ T i₁
    · rw [IsScalarTower.algebraMap_eq A₁[X] (A₁[X] ⊗[A[X]] EA) (Localization.AtPrime QA'),
        ← RingHom.comp_assoc, hjA'comp, hgu]
    · unfold _root_.GlobalTheory.LocAcyc.IsZModTorsor at hact'
      unfold _root_.GlobalTheory.KeyOriginCut.IsZTorsor
      exact hact'
  · refine _root_.GlobalTheory.LocAcyc.genFib_ringHom_ext fun y => ?_
    have key : (ψA'.comp β).comp
        (algebraMap (Localization.AtPrime QA) (_root_.GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA))) =
        ψA.comp (algebraMap (Localization.AtPrime QA)
          (_root_.GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA))) := by
      refine IsLocalization.ringHom_ext QA.primeCompl (RingHom.ext fun e => ?_)
      simp only [RingHom.comp_apply]
      rw [hβalg, hℓ, hψA'alg, hjA'g, hgγ]
      exact (RingHom.congr_fun hψA _).symm
    exact RingHom.congr_fun key y
  · rw [← RingHom.comp_assoc, hjA'comp, hgv]
  · rw [hjA'comp]
  · intro Z _ u v huv'
    exact exists_ringHom_tensor_of_comp_eq Z u v huv'
  · intro Z _ w₁ w₂ h₁ h₂
    exact tensorProduct_ringHom_ext_of_comp_eq w₁ w₂ h₁ h₂

end GlobalTheory.EnlargeBaseChange
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FittingDatumBaseChangeLocalEnlargementStatement
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fittingDatum_baseChange_localEnlargement : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T)
      (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O)
      (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    GlobalTheory.KeyOriginEnlarge.Fits T O q A i EA QA jA ψA DA actA →
    ∀ (A₁ : Type) [CommRing A₁] [IsDomain A₁] [IsLocalRing A₁] (f : A →+* A₁) (i₁ : A₁ →+* T),
    Function.Injective i₁ → IsLocalHom i₁ → i₁.comp f = i →
    ∃ (EA' : Type) (_ : CommRing EA') (_ : Algebra (Polynomial A₁) EA') (_ : Algebra A₁ EA')
      (_ : IsScalarTower A₁ (Polynomial A₁) EA') (_ : Algebra.Etale (Polynomial A₁) EA')
      (QA' : Ideal EA') (_ : QA'.IsPrime) (jA' : Localization.AtPrime QA' →+* O)
      (ψA' : GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA') →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA' : Type) (_ : CommRing DA') (_ : Algebra (GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA')) DA')
      (actA' : Multiplicative (ZMod q) →* (DA' ≃ₐ[GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA')] DA')),
      GlobalTheory.KeyOriginEnlarge.Fits T O q A₁ i₁ EA' QA' jA' ψA' DA' actA' ∧
      (∃ (β : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA'))
        (h : DA →+* DA'), ψA'.comp β = ψA ∧
        h.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) =
          (algebraMap (GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA')) DA').comp β) ∧
      ∃ γ : EA →+* EA',
        γ.comp (algebraMap (Polynomial A) EA) = (algebraMap (Polynomial A₁) EA').comp (Polynomial.mapRingHom f) ∧
        jA'.comp ((algebraMap EA' (Localization.AtPrime QA')).comp γ) = jA.comp (algebraMap EA (Localization.AtPrime QA)) ∧
        QA' = (maximalIdeal O).comap (jA'.comp (algebraMap EA' (Localization.AtPrime QA'))) ∧
        (∀ (Z : Type) [CommRing Z] (u : Polynomial A₁ →+* Z) (v : EA →+* Z),
          u.comp (Polynomial.mapRingHom f) = v.comp (algebraMap (Polynomial A) EA) →
          ∃ w : EA' →+* Z, w.comp (algebraMap (Polynomial A₁) EA') = u ∧ w.comp γ = v) ∧
        (∀ (Z : Type) [CommRing Z] (w₁ w₂ : EA' →+* Z),
          w₁.comp (algebraMap (Polynomial A₁) EA') = w₂.comp (algebraMap (Polynomial A₁) EA') →
          w₁.comp γ = w₂.comp γ → w₁ = w₂) := by
  first | (exact @GlobalTheory.EnlargeBaseChange.fits_baseChange) | (exact GlobalTheory.EnlargeBaseChange.fits_baseChange) | (intros; apply GlobalTheory.EnlargeBaseChange.fits_baseChange  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EnlargeStrictHenselisationRetractMod
open IsLocalRing Polynomial

namespace GlobalTheory.KeyOriginRetract

theorem mem_originIdeal {R : Type} [CommRing R] [IsLocalRing R] (p : Polynomial R) :
    p ∈ GlobalTheory.KeyOriginCut.originIdeal R ↔ p.coeff 0 ∈ maximalIdeal R := by
  unfold GlobalTheory.KeyOriginCut.originIdeal
  constructor
  · intro hp
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hp
    rw [Polynomial.coeff_add]
    refine Ideal.add_mem _ ((Ideal.mem_map_C_iff.1 ha) 0) ?_
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.1 hb
    simp
  · intro hp
    have h1 : Polynomial.C (p.coeff 0) ∈ (maximalIdeal R).map (Polynomial.C : R →+* Polynomial R) :=
      Ideal.mem_map_of_mem _ hp
    have h2 : p - Polynomial.C (p.coeff 0) ∈ Ideal.span {(Polynomial.X : Polynomial R)} :=
      Ideal.mem_span_singleton.2 Polynomial.X_dvd_sub_C
    have := Submodule.add_mem_sup h1 h2
    simpa using this

theorem sub_coeff_zero_mem {R B : Type} [CommRing R] [CommRing B] [Algebra R B] [Algebra (Polynomial R) B]
    [IsScalarTower R (Polynomial R) B] (p : Polynomial R) :
    algebraMap (Polynomial R) B p - algebraMap R B (p.coeff 0) ∈
      Ideal.span {algebraMap (Polynomial R) B Polynomial.X} := by
  obtain ⟨r, hr⟩ := (Polynomial.X_dvd_sub_C (p := p))
  rw [IsScalarTower.algebraMap_apply R (Polynomial R) B, Polynomial.algebraMap_eq, ← map_sub, hr, map_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

theorem map_mem_max_iff {R S : Type} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f] (a : R) : f a ∈ maximalIdeal S ↔ a ∈ maximalIdeal R :=
  ⟨fun h => (mem_maximalIdeal _).2 fun hu => (mem_maximalIdeal _).1 h (hu.map f), fun h => map_nonunit f a h⟩

end GlobalTheory.KeyOriginRetract

namespace GlobalTheory.KeyOriginRetract

theorem ker_eq_bot_of_section : ∀ (R C D : Type) [CommRing R] [CommRing C] [IsLocalRing C] [IsNoetherianRing C] [CommRing D] [Nontrivial D]
    [Algebra R C] [Algebra R D] [Algebra.FormallyUnramified R C] (ρ : C →ₐ[R] D) (ι : D →ₐ[R] C),
    ρ.comp ι = AlgHom.id R D → RingHom.ker ρ = ⊥ := by
  intro R C D _ _ _ _ _ _ _ _ _ ρ ι hρι
  have hsec : ∀ y : C, ρ (ι (ρ y)) = ρ y := fun y => AlgHom.congr_fun hρι (ρ y)
  have hsq : RingHom.ker ρ ≤ RingHom.ker ρ ^ 2 := by
    intro x hx
    let π : C →ₐ[R] C ⧸ RingHom.ker ρ ^ 2 := Ideal.Quotient.mkₐ R (RingHom.ker ρ ^ 2)
    let I : Ideal (C ⧸ RingHom.ker ρ ^ 2) := (RingHom.ker ρ).map (Ideal.Quotient.mk (RingHom.ker ρ ^ 2))
    have hI : I ^ 2 = ⊥ := by
      simp only [I, ← Ideal.map_pow, Ideal.map_quotient_self]
    have key : π = (π.comp ι).comp ρ := by
      apply Algebra.FormallyUnramified.comp_injective I hI
      refine AlgHom.ext fun y => ?_
      simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, π]
      rw [Ideal.Quotient.eq, ← map_sub]
      refine Ideal.mem_map_of_mem _ ?_
      rw [RingHom.mem_ker, map_sub, hsec, sub_self]
    have h1 := AlgHom.congr_fun key x
    rw [AlgHom.comp_apply, AlgHom.comp_apply, (RingHom.mem_ker).1 hx, map_zero, map_zero] at h1
    exact Ideal.Quotient.eq_zero_iff_mem.1 h1
  have hid : IsIdempotentElem (RingHom.ker ρ) := by
    refine le_antisymm ?_ ?_
    · exact Ideal.mul_le_right
    · simpa [pow_two] using hsq
  obtain ⟨e, he, hJ⟩ := (Ideal.isIdempotentElem_iff_of_fg _ (IsNoetherian.noetherian _)).1 hid
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self e with hu | hu
  · exfalso
    have he1 : e = 1 := by
      have : e * e = e * 1 := by rw [he.eq, mul_one]
      exact hu.mul_left_cancel this
    have : (1 : C) ∈ RingHom.ker ρ := by
      rw [hJ, he1]; exact Ideal.mem_span_singleton_self 1
    rw [RingHom.mem_ker, map_one] at this
    exact one_ne_zero this
  · have he0 : e = 0 := by
      have : (1 - e) * e = (1 - e) * 0 := by rw [sub_mul, one_mul, he.eq, sub_self, mul_zero]
      exact hu.mul_left_cancel this
    rw [hJ, he0]
    simp
end GlobalTheory.KeyOriginRetract

namespace GlobalTheory.KeyOriginEnlarge
open GlobalTheory.KeyOriginRetract in
theorem enlarge_retract : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T)
      (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O)
      (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    GlobalTheory.KeyOriginEnlarge.Fits T O q A i EA QA jA ψA DA actA →
    ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : IsLocalRing A') (_ : IsNoetherianRing A')
      (_ : IsIntegrallyClosed A') (_ : Algebra.EssFiniteType ℤ A') (i' : A' →+* T)
      (EA' : Type) (_ : CommRing EA') (_ : Algebra (Polynomial A') EA') (_ : Algebra A' EA')
      (_ : IsScalarTower A' (Polynomial A') EA') (_ : Algebra.Etale (Polynomial A') EA')
      (QA' : Ideal EA') (_ : QA'.IsPrime) (jA' : Localization.AtPrime QA' →+* O)
      (ψA' : GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA') →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA' : Type) (_ : CommRing DA') (_ : Algebra (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA')
      (actA' : Multiplicative (ZMod q) →* (DA' ≃ₐ[GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')] DA')),
      GlobalTheory.KeyOriginEnlarge.Fits T O q A' i' EA' QA' jA' ψA' DA' actA' ∧
      (∃ ρ' : Localization.AtPrime QA' →+* A',
        GlobalTheory.KeyOriginEnlarge.Retracts T O A' i' EA' QA' jA' ρ' ∧ True) ∧
      ∃ (β : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) (h : DA →+* DA'),
        ψA'.comp β = ψA ∧
        h.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) = (algebraMap (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA').comp β := by
  intro T O _ _ _ _ _ _ _ _ hT P _ φ hφ hsh hP q hq0 hqT A _ _ _ _ _ _ i EA _ _ _ _ _ QA _ jA ψA DA _ _ actA hF
  have hF0 := hF
  obtain ⟨hi, hil, hqA, hQA, hjA, hψA, htor⟩ := hF
  haveI : HenselianLocalRing O := hsh.1
  haveI : IsLocalHom φ := hsh.2.2.1
  have hPmax : ∀ p : Polynomial T, algebraMap (Polynomial T) O p ∈ maximalIdeal O ↔ p ∈ P := by
    intro p
    rw [← hφ, RingHom.comp_apply, map_mem_max_iff,
      IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P p]
  have hTO : IsLocalHom (algebraMap T O) := by
    refine ⟨fun t ht => ?_⟩
    by_contra hu
    have hm : Polynomial.C t ∈ P := by
      rw [hP, mem_originIdeal]; simpa using hu
    rw [IsScalarTower.algebraMap_apply T (Polynomial T) O, Polynomial.algebraMap_eq] at ht
    exact (mem_maximalIdeal _).1 ((hPmax _).2 hm) ht
  haveI := hTO
  have hX : algebraMap (Polynomial T) O Polynomial.X ∈ maximalIdeal O :=
    (hPmax _).2 (by rw [hP, mem_originIdeal]; simp)
  let I : Ideal O := Ideal.span {algebraMap (Polynomial T) O Polynomial.X}
  have hIm : I ≤ maximalIdeal O := (Ideal.span_singleton_le_iff_mem _).2 hX
  have hj : (jA.comp (algebraMap EA (Localization.AtPrime QA))).comp (algebraMap (Polynomial A) EA) =
      (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) := by
    rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, hjA]
  obtain ⟨A₁, _, _, _, _, _, _, f, i₁, e, hi₁, hil₁, hfi, he, hag⟩ :=
    GlobalTheory.T.localRing_mod_t_embeds_strictHenselian T O hT hTO hX A i hi hil EA (jA.comp (algebraMap EA (Localization.AtPrime QA))) hj
  obtain ⟨EA', _, _, _, _, _, QA', _, jA', ψA', DA', _, _, actA', hF', ⟨β, h, hβ, hh⟩, γ, hγ, hjγ, hQ',
    hex, huniq⟩ := GlobalTheory.T.fittingDatum_baseChange_localEnlargement T O hT P φ hφ hsh hP q hq0 hqT A i EA QA jA ψA DA actA hF0 A₁ f i₁ hi₁ hil₁ hfi
  haveI := hil₁
  obtain ⟨σ, hσC, hσγ⟩ := hex A₁ (Polynomial.evalRingHom 0) e (by
    rw [he]
    refine RingHom.ext fun p => ?_
    simp only [RingHom.comp_apply, Polynomial.coe_evalRingHom, Polynomial.coe_mapRingHom,
      ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map])
  have hag' : (Ideal.Quotient.mk I).comp ((algebraMap T O).comp (i₁.comp σ)) =
      (Ideal.Quotient.mk I).comp (jA'.comp (algebraMap EA' (Localization.AtPrime QA'))) := by
    apply huniq (O ⧸ I)
    · refine RingHom.ext fun p => ?_
      simp only [RingHom.comp_apply]
      rw [← RingHom.comp_apply σ, hσC, ← IsScalarTower.algebraMap_apply,
        ← RingHom.comp_apply jA', hF'.2.2.2.2.1, Ideal.Quotient.eq]
      have := sub_coeff_zero_mem (B := O) (p.map i₁)
      rw [Polynomial.coeff_map] at this
      rw [← neg_mem_iff, neg_sub]
      simpa [Polynomial.coeff_zero_eq_eval_zero] using this
    · refine RingHom.ext fun x => ?_
      have h1 := RingHom.congr_fun hjγ x
      simp only [RingHom.comp_apply] at h1 ⊢
      rw [← RingHom.comp_apply σ γ, hσγ, h1, Ideal.Quotient.eq]
      exact hag x

  have hdiff : ∀ y : EA', algebraMap T O (i₁ (σ y)) - jA' (algebraMap EA' (Localization.AtPrime QA') y) ∈ I := by
    intro y
    have := RingHom.congr_fun hag' y
    simp only [RingHom.comp_apply] at this
    exact Ideal.Quotient.eq.1 this
  have hQc : ∀ y : EA', y ∈ QA' ↔ σ y ∈ maximalIdeal A₁ := by
    intro y
    rw [← map_mem_max_iff i₁, ← map_mem_max_iff (algebraMap T O)]
    conv_lhs => rw [hQ', Ideal.mem_comap, RingHom.comp_apply]
    have hd := hIm (hdiff y)
    constructor
    · intro hy; simpa using Ideal.add_mem _ hd hy
    · intro hy; simpa using Ideal.sub_mem _ hy hd
  have hunit : ∀ y : QA'.primeCompl, IsUnit (σ y) := by
    intro y
    by_contra hu
    exact y.2 ((hQc y).2 ((mem_maximalIdeal _).2 hu))
  let ρ' : Localization.AtPrime QA' →+* A₁ := IsLocalization.lift (M := QA'.primeCompl) hunit
  have hρσ : ρ'.comp (algebraMap EA' (Localization.AtPrime QA')) = σ := IsLocalization.lift_comp hunit
  have hρA : ρ'.comp (algebraMap A₁ (Localization.AtPrime QA')) = RingHom.id A₁ := by
    refine RingHom.ext fun a => ?_
    simp only [RingHom.comp_apply, RingHom.id_apply]
    rw [IsScalarTower.algebraMap_apply A₁ EA' (Localization.AtPrime QA'), ← RingHom.comp_apply ρ', hρσ,
      IsScalarTower.algebraMap_apply A₁ (Polynomial A₁) EA', ← RingHom.comp_apply σ, hσC]
    simp
  have hρP : ∀ p : Polynomial A₁, ρ' (algebraMap (Polynomial A₁) (Localization.AtPrime QA') p) = p.coeff 0 := by
    intro p
    rw [IsScalarTower.algebraMap_apply (Polynomial A₁) EA' (Localization.AtPrime QA'), ← RingHom.comp_apply ρ', hρσ,
      ← RingHom.comp_apply σ, hσC]
    simp [Polynomial.coeff_zero_eq_eval_zero]
  have hagR : (Ideal.Quotient.mk I).comp ((algebraMap T O).comp (i₁.comp ρ')) = (Ideal.Quotient.mk I).comp jA' := by
    refine IsLocalization.ringHom_ext QA'.primeCompl (RingHom.ext fun y => ?_)
    have h1 := RingHom.congr_fun hag' y
    simp only [RingHom.comp_apply] at h1 ⊢
    rw [← RingHom.comp_apply ρ' (algebraMap EA' (Localization.AtPrime QA')), hρσ]
    exact h1
  have hmod : ∀ x : Localization.AtPrime QA', algebraMap T O (i₁ (ρ' x)) - jA' x ∈ I := by
    intro x
    have := RingHom.congr_fun hagR x
    simp only [RingHom.comp_apply] at this
    exact Ideal.Quotient.eq.1 this

  let J : Ideal (Localization.AtPrime QA') := Ideal.span {algebraMap (Polynomial A₁) (Localization.AtPrime QA') Polynomial.X}
  have hJle : J ≤ RingHom.ker ρ' := by
    rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, hρP]; simp
  have hJne : J ≠ ⊤ := by
    intro hJ
    have h1 : (1 : Localization.AtPrime QA') ∈ RingHom.ker ρ' := hJle (hJ ▸ Submodule.mem_top)
    rw [RingHom.mem_ker, map_one] at h1
    exact one_ne_zero h1
  haveI : Nontrivial (Localization.AtPrime QA' ⧸ J) := Ideal.Quotient.nontrivial_iff.2 hJne
  haveI : IsLocalRing (Localization.AtPrime QA' ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  haveI : IsNoetherianRing EA' := Algebra.FiniteType.isNoetherianRing (Polynomial A₁) EA'
  haveI : IsNoetherianRing (Localization.AtPrime QA') :=
    IsLocalization.isNoetherianRing QA'.primeCompl _ inferInstance
  haveI : Algebra.FormallyUnramified EA' (Localization.AtPrime QA') :=
    Algebra.FormallyUnramified.of_isLocalization QA'.primeCompl
  haveI : Algebra.FormallyUnramified (Polynomial A₁) (Localization.AtPrime QA') :=
    Algebra.FormallyUnramified.comp _ EA' _
  haveI : Algebra.FormallyUnramified (Polynomial A₁) (Localization.AtPrime QA' ⧸ J) :=
    Algebra.FormallyUnramified.of_surjective (Ideal.Quotient.mkₐ (Polynomial A₁) J) Ideal.Quotient.mk_surjective
  letI : Algebra (Polynomial A₁) A₁ := (Polynomial.evalRingHom 0).toAlgebra
  haveI : IsScalarTower A₁ (Polynomial A₁) (Localization.AtPrime QA') :=
    IsScalarTower.of_algebraMap_eq fun a => by
      rw [IsScalarTower.algebraMap_apply A₁ EA' (Localization.AtPrime QA'),
        IsScalarTower.algebraMap_apply A₁ (Polynomial A₁) EA', ← IsScalarTower.algebraMap_apply]
  have hρc : ∀ p : Polynomial A₁, ρ' (algebraMap (Polynomial A₁) (Localization.AtPrime QA') p) =
      algebraMap (Polynomial A₁) A₁ p := by
    intro p
    change ρ' _ = Polynomial.eval 0 p
    rw [hρP, Polynomial.coeff_zero_eq_eval_zero]
  let ρa : Localization.AtPrime QA' →ₐ[Polynomial A₁] A₁ := AlgHom.mk ρ' hρc
  let ρb : (Localization.AtPrime QA' ⧸ J) →ₐ[Polynomial A₁] A₁ :=
    Ideal.Quotient.liftₐ J ρa (fun a ha => hJle ha)
  have hιc : ∀ p : Polynomial A₁, ((Ideal.Quotient.mk J).comp (algebraMap A₁ (Localization.AtPrime QA')))
      (algebraMap (Polynomial A₁) A₁ p) = algebraMap (Polynomial A₁) (Localization.AtPrime QA' ⧸ J) p := by
    intro p
    change Ideal.Quotient.mk J (algebraMap A₁ (Localization.AtPrime QA') (Polynomial.eval 0 p)) =
      Ideal.Quotient.mk J (algebraMap (Polynomial A₁) (Localization.AtPrime QA') p)
    rw [Ideal.Quotient.eq, ← neg_mem_iff, neg_sub, ← Polynomial.coeff_zero_eq_eval_zero]
    exact sub_coeff_zero_mem p
  let ιb : A₁ →ₐ[Polynomial A₁] (Localization.AtPrime QA' ⧸ J) :=
    AlgHom.mk ((Ideal.Quotient.mk J).comp (algebraMap A₁ (Localization.AtPrime QA'))) hιc
  have hcomp : ρb.comp ιb = AlgHom.id (Polynomial A₁) A₁ := by
    refine AlgHom.ext fun a => ?_
    exact RingHom.congr_fun hρA a
  have hkb := ker_eq_bot_of_section (Polynomial A₁) (Localization.AtPrime QA' ⧸ J) A₁ ρb ιb hcomp
  have hker : RingHom.ker ρ' = J := by
    refine le_antisymm (fun x hx => ?_) hJle
    have h1 : Ideal.Quotient.mk J x ∈ RingHom.ker ρb := hx
    rw [hkb, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at h1
    exact h1
  exact ⟨A₁, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, i₁,
    EA', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, QA', inferInstance, jA', ψA',
    DA', inferInstance, inferInstance, actA', hF', ⟨ρ', ⟨hρA, hker, hmod⟩, trivial⟩, β, h, hβ, hh⟩
end GlobalTheory.KeyOriginEnlarge
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EnlargeStrictHenselisationRetractModStatement
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.enlarge_strictHenselisation_retract_mod : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T)
      (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O)
      (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    GlobalTheory.KeyOriginEnlarge.Fits T O q A i EA QA jA ψA DA actA →
    ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : IsLocalRing A') (_ : IsNoetherianRing A')
      (_ : IsIntegrallyClosed A') (_ : Algebra.EssFiniteType ℤ A') (i' : A' →+* T)
      (EA' : Type) (_ : CommRing EA') (_ : Algebra (Polynomial A') EA') (_ : Algebra A' EA')
      (_ : IsScalarTower A' (Polynomial A') EA') (_ : Algebra.Etale (Polynomial A') EA')
      (QA' : Ideal EA') (_ : QA'.IsPrime) (jA' : Localization.AtPrime QA' →+* O)
      (ψA' : GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA') →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA' : Type) (_ : CommRing DA') (_ : Algebra (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA')
      (actA' : Multiplicative (ZMod q) →* (DA' ≃ₐ[GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')] DA')),
      GlobalTheory.KeyOriginEnlarge.Fits T O q A' i' EA' QA' jA' ψA' DA' actA' ∧
      (∃ ρ' : Localization.AtPrime QA' →+* A',
        GlobalTheory.KeyOriginEnlarge.Retracts T O A' i' EA' QA' jA' ρ' ∧ True) ∧
      ∃ (β : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) (h : DA →+* DA'),
        ψA'.comp β = ψA ∧
        h.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) = (algebraMap (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA').comp β := by
  first | (exact @GlobalTheory.KeyOriginEnlarge.enlarge_retract) | (exact GlobalTheory.KeyOriginEnlarge.enlarge_retract) | (intros; apply GlobalTheory.KeyOriginEnlarge.enlarge_retract  <;> assumption)
end
