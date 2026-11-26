module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedEquationPullbackEtaleOverAffineSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SndSectionValueTranslateProdFirstOrderLinear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BalTau

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPushoutLocalizedPresentationBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPushoutLocalizedPresentationBaseChange
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Pinch

section LocalizationBaseChange

variable {R R' C' L ν σ : Type} [CommRing R] [CommRing R'] [CommRing C'] [CommRing L] (a : R →+* R')
  [Algebra R' C'] [Algebra C' L] (F : σ → MvPolynomial ν R) (h : MvPolynomial ν R) (ξ : ν → C')

theorem localization_baseChange_ext (hsurj : Function.Surjective (MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C'))
    [IsLocalization.Away (MvPolynomial.aeval ξ (MvPolynomial.map a h)) L] {T : Type} [CommRing T]
    (w₁ w₂ : L →+* T)
    (h₁ : ∀ r : R', w₁ (algebraMap C' L (algebraMap R' C' r)) = w₂ (algebraMap C' L (algebraMap R' C' r)))
    (h₂ : ∀ i, w₁ (algebraMap C' L (ξ i)) = w₂ (algebraMap C' L (ξ i))) : w₁ = w₂ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (MvPolynomial.aeval ξ (MvPolynomial.map a h)))
  refine RingHom.ext fun c => ?_
  obtain ⟨P, rfl⟩ := hsurj c
  have e : w₁.comp ((algebraMap C' L).comp (MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C').toRingHom) =
      w₂.comp ((algebraMap C' L).comp (MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C').toRingHom) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simpa using h₁ r
    · intro i
      simpa using h₂ i
  exact congr($e P)

theorem localization_baseChange_desc (hsurj : Function.Surjective (MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C'))
    (hker : ∀ G : MvPolynomial ν R', MvPolynomial.aeval ξ G = 0 →
      MvPolynomial.map a h * G ∈ Ideal.span (Set.range fun s ↦ MvPolynomial.map a (F s)))
    [IsLocalization.Away (MvPolynomial.aeval ξ (MvPolynomial.map a h)) L] {T : Type} [CommRing T]
    (u : Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range F)) h) →+* T) (v : R' →+* T)
    (huv : ∀ r : R, u (algebraMap R _ r) = v (a r)) :
    ∃ w : L →+* T, (∀ G : MvPolynomial ν R, w (algebraMap C' L (MvPolynomial.aeval ξ (MvPolynomial.map a G))) =
        u (algebraMap (MvPolynomial ν R ⧸ Ideal.span (Set.range F)) _ (Ideal.Quotient.mk _ G))) ∧
      ∀ r : R', w (algebraMap C' L (algebraMap R' C' r)) = v r := by
  let θ : MvPolynomial ν R' →+* T := MvPolynomial.eval₂Hom v (fun i ↦
    u (algebraMap (MvPolynomial ν R ⧸ Ideal.span (Set.range F)) _ (Ideal.Quotient.mk _ (MvPolynomial.X i))))
  have hθ : θ.comp (MvPolynomial.map a) = u.comp ((algebraMap (MvPolynomial ν R ⧸ Ideal.span (Set.range F))
      (Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range F)) h))).comp (Ideal.Quotient.mk _)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, MvPolynomial.map_C, θ, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
      rw [← huv]
      rfl
    · intro i
      simp [θ]
  have hθ' : ∀ G, θ (MvPolynomial.map a G) =
      u (algebraMap (MvPolynomial ν R ⧸ Ideal.span (Set.range F)) _ (Ideal.Quotient.mk _ G)) :=
    fun G ↦ congr($hθ G)
  have hunit : IsUnit (θ (MvPolynomial.map a h)) := by
    rw [hθ']
    exact (IsLocalization.Away.algebraMap_isUnit _).map u
  have hspan : Ideal.span (Set.range fun s ↦ MvPolynomial.map a (F s)) ≤ RingHom.ker θ := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨s, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, hθ', (Ideal.Quotient.eq_zero_iff_mem (a := F s) (I := Ideal.span (Set.range F))).2 (Ideal.subset_span ⟨s, rfl⟩),
      map_zero, map_zero]
  have hk : RingHom.ker (MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C').toRingHom ≤ RingHom.ker θ := by
    intro G hG
    rw [RingHom.mem_ker] at hG
    have e := RingHom.mem_ker.1 (hspan (hker G hG))
    rw [map_mul] at e
    exact RingHom.mem_ker.2 ((hunit.mul_right_eq_zero).1 e)
  let θ' : C' →+* T := (MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C').toRingHom.liftOfRightInverse
    (Function.surjInv hsurj) (Function.rightInverse_surjInv hsurj) ⟨θ, hk⟩
  have hθ'e : ∀ P, θ' (MvPolynomial.aeval ξ P) = θ P := fun P ↦
    RingHom.liftOfRightInverse_comp_apply _ _ _ _ P
  have hu2 : IsUnit (θ' (MvPolynomial.aeval ξ (MvPolynomial.map a h))) := by
    rw [hθ'e]
    exact hunit
  refine ⟨IsLocalization.Away.lift (MvPolynomial.aeval ξ (MvPolynomial.map a h)) hu2, fun G ↦ ?_, fun r ↦ ?_⟩
  · rw [IsLocalization.Away.lift_eq, hθ'e, hθ']
  · rw [IsLocalization.Away.lift_eq, ← MvPolynomial.aeval_C (R := R') ξ r, hθ'e]
    simp [θ]

end LocalizationBaseChange

theorem isPushout_localization_baseChange : ∀ (R R' C' L ν σ : Type) [CommRing R] [CommRing R'] [CommRing C'] [CommRing L] (a : R →+* R') [Algebra R' C'] [Algebra C' L] (F : σ → MvPolynomial ν R) (h : MvPolynomial ν R) (ξ : ν → C'), Function.Surjective (MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C') → (∀ s, MvPolynomial.aeval ξ (MvPolynomial.map a (F s)) = 0) → (∀ G : MvPolynomial ν R', MvPolynomial.aeval ξ G = 0 → MvPolynomial.map a h * G ∈ Ideal.span (Set.range fun s ↦ MvPolynomial.map a (F s))) → IsLocalization.Away (MvPolynomial.aeval ξ (MvPolynomial.map a h)) L → ∃ α : Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range F)) h) →+* L, IsPushout (CommRingCat.ofHom (algebraMap R (Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range F)) h)))) (CommRingCat.ofHom a) (CommRingCat.ofHom α) (CommRingCat.ofHom ((algebraMap C' L).comp (algebraMap R' C'))) ∧ ∀ G : MvPolynomial ν R, α (algebraMap (MvPolynomial ν R ⧸ Ideal.span (Set.range F)) _ (Ideal.Quotient.mk _ G)) = algebraMap C' L (MvPolynomial.aeval ξ (MvPolynomial.map a G)) := by
  intro R R' C' L ν σ _ _ _ _ a _ _ F h ξ hsurj hF hker hL
  have hI : Ideal.span (Set.range F) ≤
      RingHom.ker ((MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C').toRingHom.comp (MvPolynomial.map a)) := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨s, rfl⟩
    exact RingHom.mem_ker.2 (hF s)
  let β := Ideal.Quotient.lift (Ideal.span (Set.range F))
    ((MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C').toRingHom.comp (MvPolynomial.map a))
    (fun x hx ↦ RingHom.mem_ker.1 (hI hx))
  have hβ : ∀ G, β (Ideal.Quotient.mk _ G) = MvPolynomial.aeval ξ (MvPolynomial.map a G) := fun G ↦ rfl
  have hu : IsUnit (((algebraMap C' L).comp β) (Ideal.Quotient.mk (Ideal.span (Set.range F)) h)) := by
    rw [RingHom.comp_apply, hβ]
    exact IsLocalization.Away.algebraMap_isUnit _
  let α : Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range F)) h) →+* L :=
    IsLocalization.Away.lift (Ideal.Quotient.mk (Ideal.span (Set.range F)) h) hu
  have hα : ∀ G : MvPolynomial ν R, α (algebraMap (MvPolynomial ν R ⧸ Ideal.span (Set.range F)) _
      (Ideal.Quotient.mk _ G)) = algebraMap C' L (MvPolynomial.aeval ξ (MvPolynomial.map a G)) := fun G ↦ by
    simp only [α]
    rw [IsLocalization.Away.lift_eq, RingHom.comp_apply, hβ]
  have hR : ∀ r : R, algebraMap R (Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range F)) h)) r =
      algebraMap (MvPolynomial ν R ⧸ Ideal.span (Set.range F)) _ (Ideal.Quotient.mk _ (MvPolynomial.C r)) :=
    fun r ↦ rfl
  refine ⟨α, IsPushout.of_isColimit' ⟨?_⟩ (PushoutCocone.IsColimit.mk _
    (fun s ↦ CommRingCat.ofHom (Classical.choose (localization_baseChange_desc (L := L) a F h ξ hsurj hker s.inl.hom s.inr.hom
      (fun r ↦ congr($(s.condition) r))))) ?_ ?_ ?_), hα⟩
  · ext r
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    rw [hR, hα]
    simp
  · intro s
    obtain ⟨hd1, -⟩ := Classical.choose_spec (localization_baseChange_desc (L := L) a F h ξ hsurj hker s.inl.hom s.inr.hom
      (fun r ↦ congr($(s.condition) r)))
    apply CommRingCat.hom_ext
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom]
    apply IsLocalization.ringHom_ext (Submonoid.powers (Ideal.Quotient.mk (Ideal.span (Set.range F)) h))
    apply Ideal.Quotient.ringHom_ext
    refine RingHom.ext fun G ↦ ?_
    simp only [RingHom.comp_apply]
    rw [hα, hd1]
  · intro s
    obtain ⟨-, hd2⟩ := Classical.choose_spec (localization_baseChange_desc (L := L) a F h ξ hsurj hker s.inl.hom s.inr.hom
      (fun r ↦ congr($(s.condition) r)))
    ext r
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    exact hd2 r
  · intro s m h₁ h₂
    obtain ⟨hd1, hd2⟩ := Classical.choose_spec (localization_baseChange_desc (L := L) a F h ξ hsurj hker s.inl.hom s.inr.hom
      (fun r ↦ congr($(s.condition) r)))
    apply CommRingCat.hom_ext
    simp only [CommRingCat.hom_ofHom]
    apply localization_baseChange_ext a h ξ hsurj
    · intro r
      rw [hd2]
      exact congr($h₂ r)
    · intro i
      have e : algebraMap C' L (ξ i) = algebraMap C' L (MvPolynomial.aeval ξ (MvPolynomial.map a (MvPolynomial.X i))) := by
        simp
      rw [e, hd1, ← hα]
      exact congr($h₁ _)

end GlobalTheory.Pinch
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPushoutLocalizedPresentationBaseChangeStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPushout_localized_presentation_baseChange : ∀ (R R' C' L ν σ : Type) [CommRing R] [CommRing R'] [CommRing C'] [CommRing L] (a : R →+* R') [Algebra R' C'] [Algebra C' L] (F : σ → MvPolynomial ν R) (h : MvPolynomial ν R) (ξ : ν → C'), Function.Surjective (MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C') → (∀ s, MvPolynomial.aeval ξ (MvPolynomial.map a (F s)) = 0) → (∀ G : MvPolynomial ν R', MvPolynomial.aeval ξ G = 0 → MvPolynomial.map a h * G ∈ Ideal.span (Set.range fun s ↦ MvPolynomial.map a (F s))) → IsLocalization.Away (MvPolynomial.aeval ξ (MvPolynomial.map a h)) L → ∃ α : Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range F)) h) →+* L, IsPushout (CommRingCat.ofHom (algebraMap R (Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range F)) h)))) (CommRingCat.ofHom a) (CommRingCat.ofHom α) (CommRingCat.ofHom ((algebraMap C' L).comp (algebraMap R' C'))) ∧ ∀ G : MvPolynomial ν R, α (algebraMap (MvPolynomial ν R ⧸ Ideal.span (Set.range F)) _ (Ideal.Quotient.mk _ G)) = algebraMap C' L (MvPolynomial.aeval ξ (MvPolynomial.map a G)) := by
  first | exact @GlobalTheory.Pinch.isPushout_localization_baseChange | exact GlobalTheory.Pinch.isPushout_localization_baseChange | (intros; apply GlobalTheory.Pinch.isPushout_localization_baseChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootOfMonomialQuotientIntegral
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

namespace GlobalTheory.EtRoot

open MvPolynomial

theorem not_X_dvd_X {K : Type} [Field K] {n : ℕ} {i k : Fin n} (hik : i ≠ k) :
    ¬ (X i : MvPolynomial (Fin n) K) ∣ X k := by
  rintro ⟨q, hq⟩
  have := congrArg (MvPolynomial.eval (fun j => if j = i then (0 : K) else 1)) hq
  simp [hik.symm] at this

theorem prod_X_dvd_of_dvd_X_mul {K : Type} [Field K] {n : ℕ} (k : Fin n) :
    ∀ (S : Finset (Fin n)), k ∉ S → ∀ h : MvPolynomial (Fin n) K,
      (∏ j ∈ S, X j) ∣ X k * h → (∏ j ∈ S, X j) ∣ h := by
  intro S
  induction S using Finset.induction_on with
  | empty => intros; simp
  | insert i S hi ih =>
    intro hk h hd
    rw [Finset.prod_insert hi] at hd ⊢
    have hik : i ≠ k := fun e => hk (e ▸ Finset.mem_insert_self _ _)
    have hXi : (X i : MvPolynomial (Fin n) K) ∣ h := by
      rcases (X_prime (R := K) (i := i)).dvd_or_dvd (dvd_trans (dvd_mul_right _ _) hd) with h1 | h1
      · exact absurd h1 (not_X_dvd_X hik)
      · exact h1
    obtain ⟨h', rfl⟩ := hXi
    have hd' : X i * (∏ j ∈ S, X j) ∣ X i * (X k * h') := by
      rw [mul_left_comm (X i) (X k) h']; exact hd
    have h2 := (mul_dvd_mul_iff_left (X_ne_zero (R := K) i)).1 hd'
    exact mul_dvd_mul_left _ (ih (fun h => hk (Finset.mem_insert_of_mem h)) h' h2)

theorem prod_X_dvd_of_dvd_X_pow_mul {K : Type} [Field K] {n : ℕ} (k : Fin n)
    (S : Finset (Fin n)) (hk : k ∉ S) :
    ∀ (e : ℕ) (h : MvPolynomial (Fin n) K), (∏ j ∈ S, X j) ∣ X k ^ e * h → (∏ j ∈ S, X j) ∣ h := by
  intro e
  induction e with
  | zero => intro h hd; simpa using hd
  | succ e ih =>
    intro h hd
    apply ih
    apply prod_X_dvd_of_dvd_X_mul k S hk
    rwa [pow_succ, mul_comm _ (X k), mul_assoc] at hd

theorem prod_X_dvd_of_dvd_pow {K : Type} [Field K] {n : ℕ} :
    ∀ (S : Finset (Fin n)) (f : MvPolynomial (Fin n) K) (m : ℕ),
      (∏ j ∈ S, X j) ∣ f ^ m → (∏ j ∈ S, X j) ∣ f := by
  intro S
  induction S using Finset.induction_on with
  | empty => intros; simp
  | insert k S hk ih =>
    intro f m hd
    rw [Finset.prod_insert hk] at hd ⊢
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [pow_zero] at hd
      exact dvd_trans hd (one_dvd _)
    have hXk : (X k : MvPolynomial (Fin n) K) ∣ f :=
      (X_prime (R := K) (i := k)).dvd_of_dvd_pow (dvd_trans (dvd_mul_right _ _) hd)
    obtain ⟨f', rfl⟩ := hXk
    have h1 : (∏ j ∈ S, X j) ∣ X k ^ m * f' ^ m := by
      rw [← mul_pow]; exact dvd_trans (dvd_mul_left _ _) hd
    exact mul_dvd_mul_left _ (ih f' m (prod_X_dvd_of_dvd_X_pow_mul k S hk m _ h1))

theorem isRadical_span_prod_X {K : Type} [Field K] {n : ℕ} (S : Finset (Fin n)) :
    (Ideal.span {∏ j ∈ S, (X j : MvPolynomial (Fin n) K)}).IsRadical := by
  intro y hy
  obtain ⟨e, he⟩ := (Ideal.mem_radical_iff).1 hy
  rw [Ideal.mem_span_singleton] at he ⊢
  exact prod_X_dvd_of_dvd_pow S y e he

end GlobalTheory.EtRoot

namespace GlobalTheory.EtRoot

open MvPolynomial

theorem dvd_of_dvd_pow_prod_coords (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A]
    [Algebra (ZMod p) A] {n : ℕ} (t : Fin n → A)
    (he : (MvPolynomial.aeval (R := ZMod p) t).toRingHom.Etale) (S : Finset (Fin n))
    (z : A) (k : ℕ) (hz : (∏ j ∈ S, t j) ∣ z ^ k) : (∏ j ∈ S, t j) ∣ z := by
  letI : Algebra (MvPolynomial (Fin n) (ZMod p)) A := (MvPolynomial.aeval t).toRingHom.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin n) (ZMod p)) A := he
  have h1 := GlobalTheory.EtaleReducedEq.isRadical_map_of_etale (C := A)
    (Ideal.span {∏ j ∈ S, (X j : MvPolynomial (Fin n) (ZMod p))}) (isRadical_span_prod_X S)
  rw [Ideal.map_span, Set.image_singleton] at h1
  have h2 : algebraMap (MvPolynomial (Fin n) (ZMod p)) A (∏ j ∈ S, X j) = ∏ j ∈ S, t j := by
    rw [RingHom.algebraMap_toAlgebra, map_prod]
    simp
  rw [h2] at h1
  have hmem : z ∈ (Ideal.span {∏ j ∈ S, t j}).radical :=
    (Ideal.mem_radical_iff).2 ⟨k, Ideal.mem_span_singleton.2 hz⟩
  exact Ideal.mem_span_singleton.1 (h1 hmem)

theorem mem_local_of_pow_mem (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [IsDomain A]
    [Algebra (ZMod p) A] {n : ℕ} (t : Fin n → A)
    (he : (MvPolynomial.aeval (R := ZMod p) t).toRingHom.Etale) (P : Ideal A) [P.IsPrime]
    (L : Type) [Field L] [Algebra A L] [IsFractionRing A L] (x : L) (m : ℕ) (hm : 0 < m)
    (hx : ∃ a b : A, b ∉ P ∧ x ^ m * algebraMap A L b = algebraMap A L a) :
    ∃ a b : A, b ∉ P ∧ x * algebraMap A L b = algebraMap A L a := by
  let Q := MvPolynomial (Fin n) (ZMod p)
  letI : Algebra Q A := (MvPolynomial.aeval t).toRingHom.toAlgebra
  haveI : Algebra.Etale Q A := he
  let T := Localization.AtPrime P
  haveI : Algebra.FormallyEtale Q T := inferInstance
  haveI : Algebra.EssFiniteType A T := Algebra.EssFiniteType.of_isLocalization T P.primeCompl
  haveI : Algebra.EssFiniteType Q T := Algebra.EssFiniteType.comp Q A T
  haveI : IsIntegrallyClosed Q := isIntegrallyClosed_mvPolynomial_fin (ZMod p) n
  obtain ⟨_, hT⟩ := GlobalTheory.EtNormal.isDomain_and_isIntegrallyClosed_of_formallyEtale Q T
  have hunit : ∀ y : P.primeCompl, IsUnit (algebraMap A L y) := fun y => by
    have hy : (y : A) ≠ 0 := fun h => y.2 (h ▸ P.zero_mem)
    exact isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective A L)).2 hy)
  letI : Algebra T L := (IsLocalization.lift (M := P.primeCompl) (S := T) hunit).toAlgebra
  haveI : IsScalarTower A T L := IsScalarTower.of_algebraMap_eq
    (fun y => (IsLocalization.lift_eq (M := P.primeCompl) (S := T) hunit y).symm)
  haveI : IsFractionRing T L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P.primeCompl T L
  have hmk : ∀ (a : A) (b : P.primeCompl),
      algebraMap T L (IsLocalization.mk' T a b) * algebraMap A L b = algebraMap A L a := by
    intro a b
    rw [IsScalarTower.algebraMap_apply A T L b, ← map_mul, IsLocalization.mk'_spec,
      ← IsScalarTower.algebraMap_apply]
  obtain ⟨a, b, hb, hab⟩ := hx
  have hbL : algebraMap A L b ≠ 0 := (hunit ⟨b, hb⟩).ne_zero
  have hxm : x ^ m = algebraMap T L (IsLocalization.mk' T a (⟨b, hb⟩ : P.primeCompl)) := by
    apply mul_right_cancel₀ hbL
    rw [hab]; exact (hmk a ⟨b, hb⟩).symm
  have hint : IsIntegral T x := by
    apply IsIntegral.of_pow hm
    rw [hxm]; exact isIntegral_algebraMap
  obtain ⟨u, hu⟩ := (IsIntegrallyClosed.isIntegral_iff (R := T) (K := L)).1 hint
  obtain ⟨⟨c, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl u
  refine ⟨c, s, s.2, ?_⟩
  rw [← hu]; exact hmk c s

theorem div_prod_coords_mem_of_pow : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [IsDomain A] [Algebra (ZMod p) A] {n : ℕ} (t : Fin n → A), (MvPolynomial.aeval (R := ZMod p) t).toRingHom.Etale → ∀ (P : Ideal A) [P.IsPrime] (L : Type) [Field L] [Algebra A L] [IsFractionRing A L] (S : Finset (Fin n)) (g : L) (m : ℕ), 0 < m → (∃ a b : A, b ∉ P ∧ g ^ m / algebraMap A L (∏ j ∈ S, t j) * algebraMap A L b = algebraMap A L a) → ∃ a b : A, b ∉ P ∧ g / algebraMap A L (∏ j ∈ S, t j) * algebraMap A L b = algebraMap A L a := by
  intro p _ A _ _ _ n t he P _ L _ _ _ S g m hm ⟨a, b, hb, hab⟩
  have h1P : (1 : A) ∉ P := (Ideal.ne_top_iff_one P).1 (Ideal.IsPrime.ne_top ‹_›)
  by_cases h0 : (∏ j ∈ S, t j) = 0
  · exact ⟨0, 1, h1P, by simp [h0]⟩
  have hπL : algebraMap A L (∏ j ∈ S, t j) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A L)).2 h0
  have h1 : ∃ a' b' : A, b' ∉ P ∧ g ^ m * algebraMap A L b' = algebraMap A L a' :=
    ⟨a * ∏ j ∈ S, t j, b, hb, by
      rw [map_mul, ← hab, div_mul_eq_mul_div, div_mul_cancel₀ _ hπL]⟩
  obtain ⟨x, s, hs, hxs⟩ := mem_local_of_pow_mem p A t he P L g m hm h1
  have hbs : s * b ∉ P := fun h => ((‹P.IsPrime›).mem_or_mem h).elim hs hb
  have h2 : x ^ m * b = a * (∏ j ∈ S, t j) * s ^ m := by
    apply IsFractionRing.injective A L
    simp only [map_mul, map_pow]
    rw [← hxs, ← hab]
    field_simp
    ring
  have h3 : (∏ j ∈ S, t j) ∣ (x * b) ^ m := by
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    refine ⟨a * s ^ (k + 1) * b ^ k, ?_⟩
    calc (x * b) ^ (k + 1) = (x ^ (k + 1) * b) * b ^ k := by ring
      _ = _ := by rw [h2]; ring
  obtain ⟨y, hy⟩ := dvd_of_dvd_pow_prod_coords p A t he S (x * b) m h3
  refine ⟨y, s * b, hbs, ?_⟩
  have h4 : algebraMap A L (x * b) = algebraMap A L (∏ j ∈ S, t j) * algebraMap A L y := by
    rw [hy, map_mul]
  rw [map_mul, ← hxs] at h4
  rw [map_mul, div_mul_eq_mul_div, div_eq_iff hπL]
  linear_combination h4

end GlobalTheory.EtRoot
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyOfFiniteTypeNearGenerisationOfPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyOfFiniteTypeNearGenerisationOfPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.USpread

theorem lft_of_pullback {X V P S T Y : Scheme.{0}} (j : X ⟶ V) (q : V ⟶ P) (s : S ⟶ P) (t : T ⟶ S)
    (u : Y ⟶ X) (b : Y ⟶ T) [LocallyOfFiniteType j] [LocallyOfFiniteType (pullback.snd q s)]
    (h : IsPullback u b (j ≫ q) (t ≫ s)) : LocallyOfFiniteType b := by
  have h1 := (IsPullback.of_hasPullback j (pullback.fst q s)).paste_vert (IsPullback.of_hasPullback q s)
  have h2 := (IsPullback.of_hasPullback (pullback.snd j (pullback.fst q s) ≫ pullback.snd q s) t).paste_horiz h1
  rw [← h.isoIsPullback_hom_snd _ _ h2]
  infer_instance

theorem exists_to_stalk (R : Type) [CommRing R] (x : Sp R) [x.asIdeal.IsPrime] :
    ∃ t : Sp (Localization.AtPrime x.asIdeal) ⟶ Spec ((Sp R).presheaf.stalk x),
      t ≫ (Sp R).fromSpecStalk x =
        Spec.map (CommRingCat.ofHom (algebraMap R (Localization.AtPrime x.asIdeal))) := by
  let y : PrimeSpectrum R := x
  haveI := StructureSheaf.IsLocalization.to_stalk R y
  let e := IsLocalization.algEquiv (R := R) y.asIdeal.primeCompl
    ((Spec.structureSheaf R).presheaf.stalk y) (Localization.AtPrime y.asIdeal)
  refine ⟨Spec.map (CommRingCat.ofHom e.toRingEquiv.toRingHom), ?_⟩
  have := Spec.fromSpecStalk_eq' (CommRingCat.of R) x
  erw [this, ← Spec.map_comp]
  congr 1
  ext r
  exact e.commutes r

theorem away_finiteType (R : Type) [CommRing R] (f : R) (P A : Scheme.{0})
    (p : P ⟶ Sp R) (ιA : A ⟶ P) (a : A ⟶ Sp (Localization.Away f))
    (h : IsPullback ιA a p (GlobalTheory.Desc.awayMap f)) [LocallyOfFiniteType a]
    (C : Type) [CommRing C] [Algebra R C] (j : Sp C ⟶ P) [IsOpenImmersion j]
    (hj : j ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R C))) :
    Algebra.FiniteType R (Localization.Away (algebraMap R C f)) := by
  let D := Localization.Away (algebraMap R C f)
  have hu : IsUnit (algebraMap R D f) := by
    rw [IsScalarTower.algebraMap_apply R C D]
    exact IsLocalization.Away.algebraMap_isUnit _
  let ψ : Localization.Away f →+* D := IsLocalization.Away.lift f hu
  have hψ : ψ.comp (algebraMap R (Localization.Away f)) = algebraMap R D :=
    IsLocalization.Away.lift_comp f hu
  let k : Sp D ⟶ Sp C := Spec.map (CommRingCat.ofHom (algebraMap C D))
  haveI : IsOpenImmersion k := IsOpenImmersion.of_isLocalization (algebraMap R C f)
  have hψ' : Spec.map (CommRingCat.ofHom ψ) ≫ GlobalTheory.Desc.awayMap f =
      Spec.map (CommRingCat.ofHom (algebraMap R D)) := by
    rw [← hψ, CommRingCat.ofHom_comp, Spec.map_comp]
  have w : (k ≫ j) ≫ p = Spec.map (CommRingCat.ofHom ψ) ≫ GlobalTheory.Desc.awayMap f := by
    rw [hψ', Category.assoc, hj, IsScalarTower.algebraMap_eq R C D, CommRingCat.ofHom_comp,
      Spec.map_comp]
  haveI : IsOpenImmersion (GlobalTheory.Desc.awayMap f) := IsOpenImmersion.of_isLocalization f
  haveI : IsOpenImmersion ιA := MorphismProperty.of_isPullback h.flip ‹_›
  let l := h.lift _ _ w
  have hl : l ≫ ιA = k ≫ j := h.lift_fst _ _ w
  haveI : IsOpenImmersion (l ≫ ιA) := by rw [hl]; infer_instance
  haveI : IsOpenImmersion l := IsOpenImmersion.of_comp l ιA
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap R D))) := by
    rw [← hψ', ← h.lift_snd _ _ w]
    change LocallyOfFiniteType ((l ≫ a) ≫ _)
    infer_instance
  exact RingHom.finiteType_algebraMap.1
    ((HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 this)

theorem ne_zero (R : Type) [CommRing R] (f : R) (P A : Scheme.{0}) [IsIntegral P] [Nonempty A]
    (p : P ⟶ Sp R) (ιA : A ⟶ P) (a : A ⟶ Sp (Localization.Away f))
    (h : IsPullback ιA a p (GlobalTheory.Desc.awayMap f))
    (C : Type) [CommRing C] [Algebra R C] [Nonempty (Sp C)] (j : Sp C ⟶ P) [IsOpenImmersion j]
    (hj : j ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R C))) :
    algebraMap R C f ≠ 0 := by
  intro h0
  haveI : IsOpenImmersion (GlobalTheory.Desc.awayMap f) := IsOpenImmersion.of_isLocalization f
  haveI : IsOpenImmersion ιA := MorphismProperty.of_isPullback h.flip ‹_›
  obtain ⟨y, ⟨c, hc⟩, ⟨t, ht⟩⟩ := nonempty_preirreducible_inter
    j.isOpenEmbedding.isOpen_range ιA.isOpenEmbedding.isOpen_range
    (Set.range_nonempty _) (Set.range_nonempty _)
  have h1 : p y = PrimeSpectrum.comap (algebraMap R C) c := by
    rw [← hc, ← Scheme.Hom.comp_apply, hj]; rfl
  have h2 : p y = PrimeSpectrum.comap (algebraMap R (Localization.Away f)) (a t) := by
    rw [← ht, ← Scheme.Hom.comp_apply, h.w, Scheme.Hom.comp_apply]; rfl
  have h3 : f ∈ (PrimeSpectrum.comap (algebraMap R C) c).asIdeal := by
    change algebraMap R C f ∈ c.asIdeal
    rw [h0]; exact zero_mem _
  rw [← h1, h2] at h3
  exact (a t).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h3
    (IsLocalization.Away.algebraMap_isUnit f))

theorem affine_case (R : Type) [CommRing R] [IsNoetherianRing R] (f : R) (P A : Scheme.{0})
    [IsIntegral P] [Nonempty A]
    (p : P ⟶ Sp R) (ιA : A ⟶ P) (a : A ⟶ Sp (Localization.Away f))
    (h : IsPullback ιA a p (GlobalTheory.Desc.awayMap f)) [LocallyOfFiniteType a]
    (x : Sp R) (V : P.Opens)
    [LocallyOfFiniteType (Limits.pullback.snd (V.ι ≫ p) ((Sp R).fromSpecStalk x))]
    (C : Type) [CommRing C] [IsDomain C] [Algebra R C] (j : Sp C ⟶ V) [IsOpenImmersion j]
    (hj : (j ≫ V.ι) ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R C)))
    (c : Sp C) (hc : (p ((j ≫ V.ι) c)).asIdeal ≤ x.asIdeal) :
    ∃ W : P.Opens, (j ≫ V.ι) c ∈ W ∧ W ≤ V ∧ LocallyOfFiniteType (W.ι ≫ p) := by
  haveI : Nonempty (Sp C) := ⟨c⟩
  haveI := x.isPrime
  have h1 := ne_zero R f P A p ιA a h C (j ≫ V.ι) hj
  have h2 := away_finiteType R f P A p ιA a h C (j ≫ V.ι) hj
  obtain ⟨t, ht⟩ := exists_to_stalk R x
  have hpb := (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct R (Localization.AtPrime x.asIdeal) C)).flip
  rw [← hj, ← ht, Category.assoc] at hpb
  have h3 := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1
    (lft_of_pullback _ _ _ _ _ _ hpb)
  have h4 : Algebra.FiniteType (Localization.AtPrime x.asIdeal)
      (TensorProduct R (Localization.AtPrime x.asIdeal) C) := RingHom.finiteType_algebraMap.1 h3
  obtain ⟨g, hg, hft⟩ := GlobalTheory.T.exists_finiteType_away_of_finiteType_atPrime R C f x.asIdeal h1 h2 h4
  let D := Localization.Away (algebraMap R C g)
  let k : Sp D ⟶ Sp C := Spec.map (CommRingCat.ofHom (algebraMap C D))
  haveI : IsOpenImmersion k := IsOpenImmersion.of_isLocalization (algebraMap R C g)
  have h5 : p ((j ≫ V.ι) c) = PrimeSpectrum.comap (algebraMap R C) c := by
    rw [← Scheme.Hom.comp_apply, hj]; rfl
  refine ⟨(k ≫ j ≫ V.ι).opensRange, ?_, ?_, ?_⟩
  · have : c ∈ Set.range (PrimeSpectrum.comap (algebraMap C D)) := by
      rw [PrimeSpectrum.localization_away_comap_range D (algebraMap R C g)]
      intro hgc
      apply hg
      apply hc
      rw [h5]
      exact hgc
    obtain ⟨d, hd⟩ := this
    exact ⟨d, by rw [Scheme.Hom.comp_apply, ← hd]; rfl⟩
  · rintro _ ⟨d, rfl⟩
    rw [← Category.assoc, Scheme.Hom.comp_apply]
    exact ((k ≫ j) d).2
  · have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap R D))) :=
      (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2
        (RingHom.finiteType_algebraMap.2 hft)
    have e : (k ≫ j ≫ V.ι) ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R D)) := by
      rw [Category.assoc, hj, IsScalarTower.algebraMap_eq R C D, CommRingCat.ofHom_comp,
        Spec.map_comp]
    rw [← Scheme.Hom.isoOpensRange_inv_comp, Category.assoc, e]
    infer_instance

theorem locally_finiteType_near : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (f : R) (P A : Scheme.{0}) [IsIntegral P] [Nonempty A] (p : P ⟶ Sp R) (ιA : A ⟶ P) (a : A ⟶ Sp (Localization.Away f)), IsPullback ιA a p (GlobalTheory.Desc.awayMap f) → LocallyOfFiniteType a → ∀ (x : Sp R) (V : P.Opens), LocallyOfFiniteType (Limits.pullback.snd (V.ι ≫ p) ((Sp R).fromSpecStalk x)) → ∀ z : P, z ∈ V → (p z).asIdeal ≤ x.asIdeal → ∃ W : P.Opens, z ∈ W ∧ W ≤ V ∧ LocallyOfFiniteType (W.ι ≫ p) := by
  intro R _ _ f P A _ _ p ιA a h ha x V hV z hz hzx
  obtain ⟨_, ⟨W₀, hW₀, rfl⟩, hzW, hWV⟩ :=
    P.isBasis_affineOpens.exists_subset_of_mem_open hz V.isOpen
  replace hW₀ : IsAffineOpen W₀ := hW₀
  haveI : Nonempty W₀ := ⟨⟨z, hzW⟩⟩
  have hr : Set.range hW₀.fromSpec ⊆ Set.range V.ι := by
    rw [hW₀.range_fromSpec, Scheme.Opens.range_ι]; exact hWV
  let j := IsOpenImmersion.lift V.ι hW₀.fromSpec hr
  have hj : j ≫ V.ι = hW₀.fromSpec := IsOpenImmersion.lift_fac _ _ _
  haveI : IsOpenImmersion (j ≫ V.ι) := by rw [hj]; infer_instance
  haveI : IsOpenImmersion j := IsOpenImmersion.of_comp j V.ι
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (hW₀.fromSpec ≫ p)
  letI : Algebra R Γ(P, W₀) := φ.hom.toAlgebra
  obtain ⟨c, hc⟩ : z ∈ Set.range hW₀.fromSpec := by rw [hW₀.range_fromSpec]; exact hzW
  have hc' : (j ≫ V.ι) c = z := by rw [hj]; exact hc
  have := affine_case R f P A p ιA a h x V Γ(P, W₀) j (by rw [hj, ← hφ]; rfl) c
    (by erw [hc']; exact hzx)
  erw [hc'] at this
  exact this

end GlobalTheory.USpread
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyOfFiniteTypeNearGenerisationOfPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locallyOfFiniteType_near_generisation_of_point : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (f : R) (P A : Scheme.{0}) [IsIntegral P] [Nonempty A] (p : P ⟶ Sp R) (ιA : A ⟶ P) (a : A ⟶ Sp (Localization.Away f)), IsPullback ιA a p (awayMap f) → LocallyOfFiniteType a → ∀ (x : Sp R) (V : P.Opens), LocallyOfFiniteType (Limits.pullback.snd (V.ι ≫ p) ((Sp R).fromSpecStalk x)) → ∀ z : P, z ∈ V → (p z).asIdeal ≤ x.asIdeal → ∃ W : P.Opens, z ∈ W ∧ W ≤ V ∧ LocallyOfFiniteType (W.ι ≫ p) := by
  first | exact @GlobalTheory.USpread.locally_finiteType_near | exact GlobalTheory.USpread.locally_finiteType_near | (intros; apply GlobalTheory.USpread.locally_finiteType_near <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoheightLeOneOfFlat
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

set_option autoImplicit false

namespace GlobalTheory.Desc.GaussPt

section Top

theorem coheight_le_one_of_flat {H S : Scheme.{0}} (p : H ⟶ S) [Flat p] (x : H)
    (hx : Order.coheight x ≤ 1) : Order.coheight (p x) ≤ 1 := by
  have hp := Flat.generalizingMap p
  have hx' := (Order.coheight_le_coe_iff (n := 1)).1 hx
  refine (Order.coheight_le_coe_iff (n := 1)).2 fun y hy ↦ ?_
  obtain ⟨x', h₁, rfl⟩ := hp (show y ⤳ p x from hy.le)
  have hlt : x < x' := ⟨h₁, fun h ↦ hy.not_ge (Specializes.map h p.continuous)⟩
  have hm : IsMax x' := by simpa using hx' x' hlt
  have : IsMax (p x') := fun w hw ↦ by
    obtain ⟨x'', h₂, rfl⟩ := hp (show w ⤳ p x' from hw)
    exact Specializes.map (hm (show x' ≤ x'' from h₂)) p.continuous
  simpa using this

theorem coheight_le_one_iff {X : Scheme.{0}} (x : X) :
    Order.coheight x ≤ 1 ↔ ringKrullDim (X.presheaf.stalk x) ≤ 1 := by
  rw [ringKrullDim_stalk_eq_coheight]
  exact_mod_cast Iff.rfl

theorem height_le_one {R : Type} [CommRing R] (q : Sp R) (h : Order.coheight q ≤ 1) :
    q.asIdeal.height ≤ 1 := by
  rw [coheight_le_one_iff] at h
  have : q.asIdeal.IsPrime := q.2
  letI : Algebra R ((Sp R).presheaf.stalk q) := StructureSheaf.stalkAlgebra R q
  have : IsLocalization.AtPrime ((Sp R).presheaf.stalk q) q.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R q
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal] at h
  exact_mod_cast h

variable {R : Type} [CommRing R] [IsDomain R] {X : Scheme.{0}} [IsIntegral X]

theorem asIdeal_genericPoint (p : X ⟶ Sp R) [Flat p] : (p (genericPoint X)).asIdeal = ⊥ := by
  let o : Sp R := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)
  have h : o ⤳ p (genericPoint X) := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
  obtain ⟨x, h₁, h₂⟩ := Flat.generalizingMap p h
  have : x = genericPoint X := (h₁.antisymm (genericPoint_specializes x)).eq
  rw [← this, h₂]

theorem cst_injective (p : X ⟶ Sp R) [Flat p] : Function.Injective (GlobalTheory.Desc.cst p) := by
  refine (injective_iff_map_eq_zero _).2 fun r hr => ?_
  by_contra h
  refine ((unitAt_cst_iff p (genericPoint X) r).2 ?_).ne_zero hr
  rwa [asIdeal_genericPoint]

theorem ringKrullDim_eq_one (p : X ⟶ Sp R) [Flat p] {x : X} (h : (p x).asIdeal ≠ ⊥)
    (hx : Order.coheight x ≤ 1) : ringKrullDim (X.presheaf.stalk x) = 1 := by
  rw [ringKrullDim_stalk_eq_coheight]
  have h0 : Order.coheight x ≠ 0 := fun h0 => by
    rw [Order.coheight_eq_zero] at h0
    have h₁ : x ⤳ genericPoint X := h0 (show x ≤ genericPoint X from genericPoint_specializes x)
    obtain rfl : x = genericPoint X := (h₁.antisymm (genericPoint_specializes x)).eq
    exact h (asIdeal_genericPoint p)
  have : Order.coheight x = 1 := le_antisymm hx (Order.one_le_iff_ne_zero.2 h0)
  rw [this]; rfl

theorem eq_of_coheight_le_one (p : X ⟶ Sp R) [Smooth p] [GeometricallyConnected p] {x x' : X}
    (e : p x = p x') (h : (p x).asIdeal ≠ ⊥) (hx : Order.coheight x ≤ 1) (hx' : Order.coheight x' ≤ 1) :
    x = x' := by
  have := isIntegral_fiber_of_smooth p (p x)
  let ξ := p.fiberι (p x) (genericPoint _)
  have hξ : p ξ = p x := (p.range_fiberι (p x)).le ⟨_, rfl⟩
  have key : ∀ w : X, p w = p x → Order.coheight w ≤ 1 → w = ξ := by
    intro w hw hc
    obtain ⟨w', rfl⟩ := (p.range_fiberι (p x)).ge hw
    have hs : ξ ⤳ p.fiberι (p x) w' := (genericPoint_specializes w').map (p.fiberι (p x)).continuous
    by_contra hne
    have hlt : p.fiberι (p x) w' < ξ := ⟨hs, fun h' => hne (Specializes.antisymm h' hs).eq⟩
    have hm : IsMax ξ := by simpa using (Order.coheight_le_coe_iff (n := 1)).1 hc ξ hlt
    have h₁ : ξ ⤳ genericPoint X := hm (show ξ ≤ genericPoint X from genericPoint_specializes ξ)
    have h₂ : ξ = genericPoint X := (h₁.antisymm (genericPoint_specializes ξ)).eq
    apply h
    rw [← hξ, h₂]
    exact asIdeal_genericPoint p
  rw [key x rfl hx, key x' e.symm hx']

end Top

section Ring

theorem exists_common_field {R A B : Type} [CommRing R] [CommRing A] [CommRing B] (ρ : R →+* A)
    (ρ' : R →+* B) (q : Sp A) (q' : Sp B) (h : spMap ρ q = spMap ρ' q') :
    ∃ (Ω : Type) (_ : Field Ω) (u : A →+* Ω) (u' : B →+* Ω), RingHom.ker u = q.asIdeal ∧
      RingHom.ker u' = q'.asIdeal ∧ u.comp ρ = u'.comp ρ' := by
  obtain ⟨w, h₁, h₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := spMap ρ) (g := spMap ρ') q q' h
  let k := (pullback (spMap ρ) (spMap ρ')).fromSpecResidueField w
  have hk : ∀ {C : Type} [CommRing C] (g : pullback (spMap ρ) (spMap ρ') ⟶ Sp C),
      RingHom.ker (Spec.preimage (k ≫ g)).hom = (g w).asIdeal := by
    intro C _ g
    let o : Spec ((pullback (spMap ρ) (spMap ρ')).residueField w) := (⊥ : PrimeSpectrum _)
    have e := congrArg (fun m => m o) (Spec.map_preimage (k ≫ g))
    have e' : (k ≫ g) o = g w := by
      rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
    rw [← e', ← e]
    rfl
  refine ⟨_, inferInstance, (Spec.preimage (k ≫ pullback.fst _ _)).hom,
    (Spec.preimage (k ≫ pullback.snd _ _)).hom, (hk _).trans (by rw [h₁]), (hk _).trans (by rw [h₂]), ?_⟩
  have : CommRingCat.ofHom ρ ≫ Spec.preimage (k ≫ pullback.fst _ _) =
      CommRingCat.ofHom ρ' ≫ Spec.preimage (k ≫ pullback.snd _ _) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, Spec.map_preimage, Spec.map_preimage, Category.assoc,
      Category.assoc, pullback.condition]
  exact congrArg CommRingCat.Hom.hom this

theorem dvr_of_height {E : Type} [CommRing E] [IsRegularLocalRing E] [IsDomain E]
    (h : (maximalIdeal E).height ≤ 1) (h0 : maximalIdeal E ≠ ⊥) : IsDiscreteValuationRing E := by
  have : IsPrincipalIdealRing E :=
    GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.isPrincipalIdealRing_of_ringKrullDim_le_one (by
      rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]; exact_mod_cast h)
  exact ⟨h0⟩

theorem height_le_of_map {A E : Type} [CommRing A] [IsNoetherianRing A] [CommRing E] [IsLocalRing E]
    [IsNoetherianRing E] (a : A →+* E) (q : Ideal A) [q.IsPrime] (hq : q.height ≤ 1)
    (h₁ : (maximalIdeal E).comap a = q) (h₂ : q.map a = maximalIdeal E) : (maximalIdeal E).height ≤ 1 := by
  letI := a.toAlgebra
  have : (maximalIdeal E).LiesOver q := ⟨h₁.symm⟩
  refine (Ideal.height_le_height_add_of_liesOver q (maximalIdeal E)).trans ?_
  have h₃ : q.map (algebraMap A E) = maximalIdeal E := h₂
  have h₄ : (maximalIdeal E).map (Ideal.Quotient.mk (q.map (algebraMap A E))) = ⊥ := by
    rw [← h₃, Ideal.map_quotient_self]
  have : Nontrivial (E ⧸ q.map (algebraMap A E)) :=
    Ideal.Quotient.nontrivial_iff.2 (h₃ ▸ (maximalIdeal.isMaximal E).ne_top)
  rw [h₄, Ideal.height_bot, add_zero]
  exact hq

theorem injective_of_flat {A E : Type} [CommRing A] [IsDomain A] [CommRing E] [Nontrivial E]
    {a : A →+* E} (h : a.Flat) : Function.Injective a := by
  letI := a.toAlgebra
  have : Module.Flat A E := h
  exact FaithfulSMul.algebraMap_injective A E

theorem dvd_pow_of_dim {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] (h : ringKrullDim O ≤ 1)
    {g t : O} (hg : g ≠ 0) (ht : ¬ IsUnit t) : ∃ n : ℕ, g ∣ t ^ n := by
  have : Ring.KrullDimLE 1 O := Ring.krullDimLE_iff.2 h
  have : t ∈ (Ideal.span {g}).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro J ⟨hJ, hp⟩
    have hne : J ≠ ⊥ := fun e => hg (by simpa [e] using hJ)
    rw [eq_maximalIdeal (hp.isMaximal_of_ne_bot hne)]
    exact ht
  obtain ⟨n, hn⟩ := this
  exact ⟨n, Ideal.mem_span_singleton.1 hn⟩

end Ring

section Span

variable {R₁ F₁ : Type} [CommRing R₁] [CommRing F₁] (c : R₁ →+* F₁)

theorem mem_spanBy_iff (T : Set F₁) (v : F₁) :
    v ∈ spanBy c T ↔ letI := c.toAlgebra; v ∈ Submodule.span R₁ T := by
  letI := c.toAlgebra
  rw [Submodule.mem_span_set']
  constructor
  · rintro ⟨n, r, t, ht, rfl⟩
    exact ⟨n, r, fun i => ⟨t i, ht i⟩, rfl⟩
  · rintro ⟨n, r, t, rfl⟩
    exact ⟨n, r, fun i => t i, fun i => (t i).2, rfl⟩

variable {c}

theorem spanBy_zero (T : Set F₁) : (0 : F₁) ∈ spanBy c T :=
  (mem_spanBy_iff c T _).2 (zero_mem _)

theorem spanBy_add {T : Set F₁} {u v : F₁} (hu : u ∈ spanBy c T) (hv : v ∈ spanBy c T) :
    u + v ∈ spanBy c T :=
  (mem_spanBy_iff c T _).2 (add_mem ((mem_spanBy_iff c T _).1 hu) ((mem_spanBy_iff c T _).1 hv))

theorem spanBy_smul {T : Set F₁} (r : R₁) {u : F₁} (hu : u ∈ spanBy c T) : c r * u ∈ spanBy c T :=
  letI := c.toAlgebra
  (mem_spanBy_iff c T _).2 (Submodule.smul_mem _ r ((mem_spanBy_iff c T _).1 hu))

theorem spanBy_induction {T : Set F₁} {P : F₁ → Prop} (h₀ : P 0) (h₁ : ∀ t ∈ T, P t)
    (h₂ : ∀ u v, P u → P v → P (u + v)) (h₃ : ∀ r u, P u → P (c r * u)) {v : F₁}
    (hv : v ∈ spanBy c T) : P v := by
  letI := c.toAlgebra
  rw [mem_spanBy_iff] at hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact h₁ x hx
  | zero => exact h₀
  | add x y _ _ hx hy => exact h₂ x y hx hy
  | smul r x _ hx => exact h₃ r x hx

end Span

end GlobalTheory.Desc.GaussPt
end
