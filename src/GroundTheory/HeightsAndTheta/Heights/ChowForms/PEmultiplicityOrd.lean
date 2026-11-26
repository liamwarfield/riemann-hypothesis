module

public import GroundTheory.HeightsAndTheta.Heights.ChowForms.StatementsSectionOrder
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowFormReducedRadical

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ChowForms.PEmultiplicityOrd
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing

theorem EmultiplicityOrd.proof (h₁ : LocalizationPrimeDVR.Statement) : EmultiplicityOrd.Statement := by
  intro R _ _ _ _ q x p _ hq hp hx
  have : IsDiscreteValuationRing (Localization.AtPrime p) := h₁ R q p hq hp
  set O := Localization.AtPrime p
  have hfin : FiniteMultiplicity q x := FiniteMultiplicity.of_prime_left hq hx
  obtain ⟨y, hxy, hy⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  rw [hfin.emultiplicity_eq_multiplicity]

  have hyu : IsUnit (algebraMap R O y) := by
    rw [IsLocalization.AtPrime.isUnit_to_map_iff O p y]
    change y ∉ p
    rw [hp, Ideal.mem_span_singleton]
    exact hy

  have hmax : maximalIdeal O = Ideal.span {algebraMap R O q} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p O, congrArg (Ideal.map (algebraMap R O)) hp,
      Ideal.map_span, Set.image_singleton]
  have hirr : Irreducible (algebraMap R O q) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hmax
  have hnz : algebraMap R O q ∈ nonZeroDivisors O :=
    mem_nonZeroDivisors_of_ne_zero hirr.ne_zero
  conv_rhs => rw [hxy, map_mul, map_pow, Ring.ord_mul_of_isUnit_right hyu, Ring.ord_pow hnz,
    Ring.ord_of_irreducible hirr]
  simp

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ChowForms.PSpecFirstNe
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

section Choice

variable {F : Type} [Field F] {k n : ℕ}

def specFirstSplit (ij : Fin (k + 1) × Fin n) : (Fin k × Fin n) ⊕ Fin n :=
  Fin.cases (motive := fun _ => (Fin k × Fin n) ⊕ Fin n) (Sum.inr ij.2) (fun i => Sum.inl (i, ij.2)) ij.1

theorem specFirstSplit_injective : Function.Injective (specFirstSplit (k := k) (n := n)) := by
  rintro ⟨i, m⟩ ⟨j, m'⟩ h
  cases i using Fin.cases <;> cases j using Fin.cases <;> simp_all [specFirstSplit]

theorem specFirst_eq_map_eval (g : MvPolynomial (Fin (k + 1) × Fin n) F) (t : Fin n → F) :
    specFirst g t = map (eval t) (sumAlgEquiv F (Fin k × Fin n) (Fin n) (rename specFirstSplit g)) := by
  have h : (bind₁ (specFirstVar t) : MvPolynomial (Fin (k + 1) × Fin n) F →ₐ[F] _).toRingHom =
      (map (eval t)).comp ((sumAlgEquiv F (Fin k × Fin n) (Fin n)).toRingHom.comp
        (rename specFirstSplit).toRingHom) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change bind₁ (specFirstVar t) (C a) =
        map (eval t) (sumAlgEquiv F (Fin k × Fin n) (Fin n) (rename specFirstSplit (C a)))
      rw [bind₁_C_right, rename_C, sumAlgEquiv_C_inl, map_C, eval_C]
    · rintro ⟨i, m⟩
      cases i using Fin.cases <;>
        simp [specFirstVar, specFirstSplit, sumAlgEquiv_X_inl, sumAlgEquiv_X_inr]
  exact RingHom.congr_fun h g

theorem exists_specFirst_ne_zero [Infinite F] {f : MvPolynomial (Fin (k + 1) × Fin n) F} (hf : f ≠ 0) :
    ∃ t : Fin n → F, specFirst f t ≠ 0 := by
  set g := sumAlgEquiv F (Fin k × Fin n) (Fin n) (rename specFirstSplit f) with hg_def
  have hg : g ≠ 0 :=
    (map_ne_zero_iff _ (sumAlgEquiv F (Fin k × Fin n) (Fin n)).injective).mpr
      ((map_ne_zero_iff _ (rename_injective _ specFirstSplit_injective)).mpr hf)
  obtain ⟨β, hβ⟩ := ne_zero_iff.mp hg
  have ht : ∃ t : Fin n → F, eval t (AddMonoidAlgebra.coeff g β) ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hβ (MvPolynomial.funext fun x => by simp [h x])
  obtain ⟨t, ht⟩ := ht
  refine ⟨t, fun h0 => ht ?_⟩
  have := congr_arg (AddMonoidAlgebra.coeff · β) h0
  simpa only [specFirst_eq_map_eval, ← hg_def, coeff_map, AddMonoidAlgebra.coeff_zero,
    Finsupp.zero_apply] using this

end Choice

theorem det_mulLeft_ne_zero {O B : Type*} [CommRing O] [IsDomain O] [CommRing B] [IsDomain B] [Algebra O B]
    {θ : B} (hθ : θ ≠ 0) : LinearMap.det (LinearMap.mulLeft O θ) ≠ 0 := by
  classical
  intro h
  by_cases H : ∃ s : Finset B, Nonempty (Module.Basis s O B)
  · obtain ⟨s, ⟨b⟩⟩ := H
    have : Module.Free O B := Module.Free.of_basis b
    have hker := LinearMap.bot_lt_ker_of_det_eq_zero h
    rw [bot_lt_iff_ne_bot, Ne, LinearMap.ker_eq_bot] at hker
    exact hker fun x y hxy => mul_left_cancel₀ hθ (by simpa using hxy)
  · simp [LinearMap.coe_det, H] at h

theorem SpecFirstNe.proof (h₁ : IncIdealBelow.Statement) (h₂ : SpecFirstMemIncIdeal.Statement)
    (h₄ : ChartLocDomain.Statement) (h₅ : ChartNorm.Statement) : SpecFirstNe.Statement := by
  intro F _ _ n e I f u hI hf hu
  obtain ⟨t, ht⟩ := exists_specFirst_ne_zero hf.1
  have hlt : linForm t ∉ I := fun hmem => ht (by
    have hmem' := h₂ F n e I I f t hf le_rfl hmem
    rwa [h₁ F n e I f hI hf, Ideal.mem_bot] at hmem')
  have htp : specFirst f t ∉ (⊥ : Ideal (MvPolynomial (Fin e × Fin n) F)) := by
    rwa [Ideal.mem_bot]
  obtain ⟨hdom, -, hθ⟩ := h₄ F n e I f t ⊥ hI hf hlt
  have hnorm := h₅ F n e I f t ⊥ hI hf (Or.inl rfl) htp u
  have ha : algebraMap _ (Localization.AtPrime (⊥ : Ideal (MvPolynomial (Fin e × Fin n) F)))
      (specFirst f t) ≠ 0 := fun h => ht
    (IsLocalization.injective (Localization.AtPrime (⊥ : Ideal (MvPolynomial (Fin e × Fin n) F)))
      (Ideal.primeCompl_le_nonZeroDivisors ⊥) (h.trans (map_zero _).symm))
  have hdet := det_mulLeft_ne_zero (O := Localization.AtPrime (⊥ : Ideal (MvPolynomial (Fin e × Fin n) F)))
    (hθ u hu)
  intro h0
  rw [h0, map_zero] at hnorm
  exact mul_ne_zero ha hdet hnorm.symm

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartChoice
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace ChartChoice

variable {F : Type} [Field F] {n e : ℕ}

def shiftVar (e n : ℕ) : Fin e × Fin n → Fin (e + 1) × Fin n := fun jm => (jm.1.succ, jm.2)

def splitFirst (F : Type) [Field F] (e n : ℕ) :
    MvPolynomial (Fin (e + 1) × Fin n) F →ₐ[F] MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) F) :=
  aeval fun ij => Fin.cases (motive := fun _ => MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) F))
    (X ij.2) (fun j => C (X (j, ij.2))) ij.1

def joinFirst (F : Type) [Field F] (e n : ℕ) :
    MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) F) →+* MvPolynomial (Fin (e + 1) × Fin n) F :=
  eval₂Hom (rename (shiftVar e n)).toRingHom (fun m => X (0, m))

theorem joinFirst_splitFirst (p : MvPolynomial (Fin (e + 1) × Fin n) F) :
    joinFirst F e n (splitFirst F e n p) = p := by
  have h : (joinFirst F e n).comp (splitFirst F e n).toRingHom = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [joinFirst, splitFirst, MvPolynomial.algebraMap_eq]
    · rintro ⟨i, m⟩
      induction i using Fin.cases <;> simp [joinFirst, splitFirst, shiftVar]
  exact RingHom.congr_fun h p

theorem joinFirst_C (a : MvPolynomial (Fin e × Fin n) F) :
    joinFirst F e n (C a) = rename (shiftVar e n) a := by
  simp [joinFirst]

theorem specFirst_rename_shiftVar (q : MvPolynomial (Fin e × Fin n) F) :
    specFirst (rename (shiftVar e n) q) 0 = q := by
  unfold specFirst
  rw [bind₁_rename]
  have : (specFirstVar (0 : Fin n → F) ∘ shiftVar e n) = X := by
    funext jm
    simp [specFirstVar, shiftVar]
  rw [this, bind₁_X_left]
  rfl

theorem specFirst_zero_of_isMultiHomog {δ : ℕ} (hδ : 1 ≤ δ) {f : MvPolynomial (Fin (e + 1) × Fin n) F}
    (hf : IsMultiHomog δ f) : specFirst f 0 = 0 := _root_.GroundTheory.Heights₂.Heights.ChartChoiceAlgClosed.specFirst_zero_of_isMultiHomog (δ := δ) (f := f) hδ hf

theorem eval_map_splitFirst (J : Ideal (MvPolynomial (Fin e × Fin n) F)) (t : Fin n → F)
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) :
    eval (fun m => Ideal.Quotient.mk J (C (t m))) (map (Ideal.Quotient.mk J) (splitFirst F e n f)) =
      Ideal.Quotient.mk J (specFirst f t) := by
  rw [eval_map]
  have h : (eval₂Hom (Ideal.Quotient.mk J) (fun m => Ideal.Quotient.mk J (C (t m)))).comp
      (splitFirst F e n).toRingHom = (Ideal.Quotient.mk J).comp (bind₁ (specFirstVar t)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [splitFirst, MvPolynomial.algebraMap_eq]
    · rintro ⟨i, m⟩
      induction i using Fin.cases <;> simp [splitFirst, specFirstVar]
  exact RingHom.congr_fun h f

end ChartChoice


open ChartChoice in
theorem ChartChoice.proof (h₁ : IncIdealPrime.Statement) (h₂ : ChowFormMultiHomog.Statement) :
    ChartChoice.Statement := by
  intro F _ _ n e I f q hI hf hq
  classical
  obtain ⟨hf0, hspan⟩ := isChowForm_iff.mp hf
  have hfp : Prime f := by
    have := h₁ F n (e + 1) I hI.isPrime hI.isRelevant
    rw [hspan] at this
    exact (Ideal.span_singleton_prime hf0).mp this
  obtain ⟨δ, hδ, hhom⟩ := h₂ F n (e + 1) I f hI hf

  have hndvd : ¬ rename (shiftVar e n) q ∣ f := by
    rintro ⟨g, hg⟩
    rcases hfp.2.2 (rename (shiftVar e n) q) g (hg ▸ dvd_refl f) with ⟨h, hh⟩ | ⟨h, hh⟩
    · have := congrArg (fun p => specFirst p 0) hh
      rw [specFirst_rename_shiftVar] at this
      unfold specFirst at this
      rw [map_mul] at this
      have h0 : specFirst f 0 = 0 := specFirst_zero_of_isMultiHomog hδ hhom
      unfold specFirst at h0
      rw [h0, zero_mul] at this
      exact hq.ne_zero this
    · have hunit : IsUnit (rename (shiftVar e n) q) := by
        refine isUnit_iff_exists_inv.mpr ⟨h, ?_⟩
        apply mul_left_cancel₀ hf0
        calc f * (rename (shiftVar e n) q * h) = rename (shiftVar e n) q * (f * h) := by ring
          _ = f * 1 := by rw [← hh, ← hg, mul_one]
      have := hunit.map (bind₁ (specFirstVar (0 : Fin n → F)))
      have h' : bind₁ (specFirstVar (0 : Fin n → F)) (rename (shiftVar e n) q) = q :=
        specFirst_rename_shiftVar q
      rw [h'] at this
      exact hq.not_isUnit this
  set J : Ideal (MvPolynomial (Fin e × Fin n) F) := Ideal.span {q} with hJ
  have : J.IsPrime := (Ideal.span_singleton_prime hq.ne_zero).mpr hq
  set P := map (Ideal.Quotient.mk J) (splitFirst F e n f) with hP
  have hP0 : P ≠ 0 := by
    intro h0
    have hmem : splitFirst F e n f ∈ RingHom.ker (map (σ := Fin n) (Ideal.Quotient.mk J)) := by
      rw [RingHom.mem_ker]; exact h0
    rw [MvPolynomial.ker_map, Ideal.mk_ker, hJ, Ideal.map_span, Set.image_singleton,
      Ideal.mem_span_singleton] at hmem
    apply hndvd
    have := map_dvd (joinFirst F e n) hmem
    rwa [joinFirst_splitFirst, joinFirst_C] at this
  have : CharZero (MvPolynomial (Fin e × Fin n) F ⧸ J) :=
    charZero_of_injective_algebraMap (algebraMap F _).injective
  by_contra hall
  push Not at hall
  apply hP0
  refine eq_zero_of_eval_zero_at_prod_finset P
    (fun _ => (Finset.range (P.totalDegree + 1)).image (fun k : ℕ => (k : MvPolynomial (Fin e × Fin n) F ⧸ J)))
    (fun i => ?_) (fun x hx => ?_)
  · rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
    exact Nat.lt_succ_of_le (degreeOf_le_totalDegree P i)
  · choose k _ hk using fun i => Finset.mem_image.mp (hx i)
    have hx' : x = fun m => Ideal.Quotient.mk J (C ((k m : ℕ) : F)) := by
      funext m
      rw [← hk m]
      simp
    rw [hx', hP, eval_map_splitFirst]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (hall _))

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ChowForms.PLengthFiniteAlgebra
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing

noncomputable section

namespace LengthFiniteAlgebra

variable {O B : Type} [CommRing O] [IsLocalRing O] [CommRing B] [Algebra O B]

theorem comap_eq_maximalIdeal [Module.Finite O B] (P : Ideal B) [P.IsMaximal] :
    P.comap (algebraMap O B) = maximalIdeal O :=
  IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal P)

theorem finite_maximalSpectrum [Module.Finite O B] : Finite (MaximalSpectrum B) := by
  have hfin := Algebra.QuasiFinite.finite_primesOver (R := O) (S := B) (maximalIdeal O)
  have := hfin.to_subtype
  refine Finite.of_injective (β := (maximalIdeal O).primesOver B)
    (fun P => ⟨P.asIdeal, P.isMaximal.isPrime, ⟨(comap_eq_maximalIdeal P.asIdeal).symm⟩⟩) ?_
  intro P Q h
  exact MaximalSpectrum.ext (congrArg Subtype.val h)

theorem length_eq_finsum_localization [IsNoetherianRing O] [Module.Finite O B] :
    Module.length O B =
      ∑ᶠ P : MaximalSpectrum B, Module.length O (Localization.AtPrime P.asIdeal) := by
  have := finite_maximalSpectrum (O := O) (B := B)
  let := Fintype.ofFinite (MaximalSpectrum B)
  rw [finsum_eq_sum_of_fintype, ← Module.length_pi_of_fintype]
  let φ : B →ₗ[O] (∀ P : MaximalSpectrum B, Localization.AtPrime P.asIdeal) :=
    LinearMap.pi fun P => (IsScalarTower.toAlgHom O B (Localization.AtPrime P.asIdeal)).toLinearMap
  have hφ : Function.Injective φ := by
    intro x y h
    apply MaximalSpectrum.toPiLocalization_injective B
    funext P
    exact congrFun h P
  by_cases h : Module.length O B = ⊤
  · rw [h]
    exact (top_le_iff.mp (h ▸ Module.length_le_of_injective φ hφ)).symm
  · have hfl : IsFiniteLength O B := Module.length_ne_top_iff.mp h
    rw [isFiniteLength_iff_isNoetherian_isArtinian] at hfl
    have : IsArtinianRing B := isArtinian_of_tower O hfl.2
    have hsurj : Function.Surjective φ := by
      intro z
      obtain ⟨x, hx⟩ := PrimeSpectrum.maximalSpectrumToPiLocalization_surjective_of_discreteTopology B z
      exact ⟨x, hx⟩
    exact (LinearEquiv.ofBijective φ ⟨hφ, hsurj⟩).length_eq

theorem isLocalHom_localization [Module.Finite O B] (P : Ideal B) [P.IsMaximal] :
    IsLocalHom (algebraMap O (Localization.AtPrime P)) := by
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  have h1 : a ∈ P.comap (algebraMap O B) := by
    rw [comap_eq_maximalIdeal P]; exact hna
  have h2 : algebraMap B (Localization.AtPrime P) (algebraMap O B a) ∈
      maximalIdeal (Localization.AtPrime P) :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P _).mpr h1
  rw [← IsScalarTower.algebraMap_apply] at h2
  exact h2 ha


omit [IsLocalRing O] in
theorem length_residueField (P : Ideal B) [P.IsMaximal] :
    Module.length O (ResidueField (Localization.AtPrime P)) = Module.length O (B ⧸ P) := by
  let e' : (B ⧸ P) ≃ₐ[B] ResidueField (Localization.AtPrime P) :=
    IsLocalization.AtPrime.equivQuotMaximalIdeal P (Localization.AtPrime P)
  exact (e'.toLinearEquiv.restrictScalars O).length_eq.symm

theorem ord_mul_length [Module.Finite O B] (P : Ideal B) [P.IsMaximal] (θ : B) :
    Ring.ord (Localization.AtPrime P) (algebraMap B _ θ) * Module.length O (B ⧸ P) =
      Module.length O (Localization.AtPrime P ⧸
        Ideal.span {algebraMap B (Localization.AtPrime P) θ}) := by
  have := isLocalHom_localization (O := O) P
  have h1 := IsLocalRing.length_restrictScalars O (Localization.AtPrime P)
    (Localization.AtPrime P ⧸ Ideal.span {algebraMap B (Localization.AtPrime P) θ})
  have h2 := IsLocalRing.length_restrictScalars O (Localization.AtPrime P)
    (ResidueField (Localization.AtPrime P))
  have h3 : Module.length (Localization.AtPrime P) (ResidueField (Localization.AtPrime P)) = 1 := by
    rw [Module.length_eq_of_surjective (S := Localization.AtPrime P)
      (R := ResidueField (Localization.AtPrime P)) residue_surjective]
    exact Module.length_eq_one _ _
  rw [length_residueField, h3, one_mul] at h2
  rw [h2, h1]
  rfl


omit [IsLocalRing O] in
theorem length_localization_quotient (I : Ideal B) (Q : Ideal (B ⧸ I)) [Q.IsMaximal] :
    Module.length O (Localization.AtPrime Q) =
      Module.length O (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I)) ⧸
        I.map (algebraMap B (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I))))) := by
  have hsub : Algebra.algebraMapSubmonoid (B ⧸ I) (Q.comap (Ideal.Quotient.mk I)).primeCompl =
      Q.primeCompl := by
    ext y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    constructor
    · rintro ⟨x, hx, hxy⟩
      rw [← hxy]
      exact hx
    · intro hy
      exact ⟨y, hy, rfl⟩
  have : IsLocalization Q.primeCompl
      (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I)) ⧸
        I.map (algebraMap B (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I))))) := by
    rw [← hsub]; infer_instance
  let e := IsLocalization.algEquiv Q.primeCompl (Localization.AtPrime Q)
    (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I)) ⧸
        I.map (algebraMap B (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I)))))
  have : IsScalarTower O (B ⧸ I)
      (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I)) ⧸
        I.map (algebraMap B (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I))))) :=
    IsScalarTower.of_algebraMap_eq fun c => by
      rw [IsScalarTower.algebraMap_apply O B (B ⧸ I),
        IsScalarTower.algebraMap_apply O (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I))),
        IsScalarTower.algebraMap_apply O B (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I)))]
      rfl
  exact (e.toLinearEquiv.restrictScalars O).length_eq

theorem finsum_reindex [Module.Finite O B] (θ : B) :
    ∑ᶠ Q : MaximalSpectrum (B ⧸ Ideal.span {θ}), Module.length O (Localization.AtPrime Q.asIdeal) =
      ∑ᶠ P : MaximalSpectrum B, Module.length O (Localization.AtPrime P.asIdeal ⧸
        Ideal.span {algebraMap B (Localization.AtPrime P.asIdeal) θ}) := by
  have := finite_maximalSpectrum (O := O) (B := B)
  have : Module.Finite O (B ⧸ Ideal.span {θ}) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ O _).toLinearMap Ideal.Quotient.mk_surjective
  have := finite_maximalSpectrum (O := O) (B := B ⧸ Ideal.span {θ})
  let := Fintype.ofFinite (MaximalSpectrum B)
  let := Fintype.ofFinite (MaximalSpectrum (B ⧸ Ideal.span {θ}))
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  let ι : MaximalSpectrum (B ⧸ Ideal.span {θ}) → MaximalSpectrum B := fun Q =>
    ⟨Q.asIdeal.comap (Ideal.Quotient.mk _), by
      have := Q.isMaximal; exact Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective⟩
  refine Fintype.sum_of_injective ι ?_ _ _ ?_ ?_
  · intro Q₁ Q₂ h
    exact MaximalSpectrum.ext (Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
      (congrArg MaximalSpectrum.asIdeal h))
  · intro P hP
    have hθ : θ ∉ P.asIdeal := by
      intro hθ
      apply hP
      have hle : Ideal.span {θ} ≤ P.asIdeal := (Ideal.span_singleton_le_iff_mem _).mpr hθ
      have := P.isMaximal
      have hmax := Ideal.IsMaximal.map_of_surjective_of_ker_le (m := P.asIdeal)
        (f := Ideal.Quotient.mk (Ideal.span {θ})) Ideal.Quotient.mk_surjective
        (by rwa [Ideal.mk_ker])
      exact ⟨⟨_, hmax⟩, MaximalSpectrum.ext (Ideal.comap_map_mk hle)⟩
    have hu : IsUnit (algebraMap B (Localization.AtPrime P.asIdeal) θ) :=
      IsLocalization.map_units (Localization.AtPrime P.asIdeal) (⟨θ, hθ⟩ : P.asIdeal.primeCompl)
    rw [Ideal.span_singleton_eq_top.mpr hu]
    exact Module.length_eq_zero
  · intro Q
    have := Q.isMaximal
    rw [length_localization_quotient (Ideal.span {θ}) Q.asIdeal, Ideal.map_span, Set.image_singleton]

end LengthFiniteAlgebra


open LengthFiniteAlgebra in
theorem LengthFiniteAlgebra.proof : LengthFiniteAlgebra.Statement := by
  intro O B _ _ _ _ _ _ θ
  have hr : LinearMap.range (LinearMap.mulLeft O θ) = (Ideal.span {θ}).restrictScalars O := by
    ext x
    simp [Ideal.mem_span_singleton', mul_comm]
  have : Module.Finite O (B ⧸ Ideal.span {θ}) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ O _).toLinearMap Ideal.Quotient.mk_surjective
  rw [(Submodule.quotEquivOfEq _ _ hr ≪≫ₗ
      Submodule.Quotient.restrictScalarsEquiv O (Ideal.span {θ})).length_eq,
    length_eq_finsum_localization, finsum_reindex]
  congr 1
  funext P
  exact (ord_mul_length P.asIdeal θ).symm

end

end GroundTheory.Heights₂.Heights
end
