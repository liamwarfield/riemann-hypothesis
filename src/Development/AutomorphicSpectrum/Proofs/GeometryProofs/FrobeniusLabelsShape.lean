module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteBaseChange

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FrobeniusShapeOfSidePreserving
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FrobeniusShapeOfSidePreserving
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem isLeft_pow_congr {Ψ : Type} (f : Equiv.Perm (Ψ ⊕ Ψ))
    (hf : (∀ σ, (f σ).isLeft = σ.isLeft) ∨ ∀ σ, (f σ).isLeft = σ.isRight) (k : ℕ) :
    ∀ σ σ' : Ψ ⊕ Ψ, σ.isLeft = σ'.isLeft → ((f ^ k) σ).isLeft = ((f ^ k) σ').isLeft := by
  induction k with
  | zero =>
    intro σ σ' h
    simpa using h
  | succ k ih =>
    intro σ σ' h
    have h' := ih σ σ' h
    rw [pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    rcases hf with hf | hf
    · rw [hf, hf]
      exact h'
    · rw [hf, hf]
      cases h1 : (f ^ k) σ <;> cases h2 : (f ^ k) σ' <;> simp_all

theorem frobShape_of_side : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (φ : ℕ → Equiv.Perm (Ψ ⊕ Ψ)), (∀ p, (∀ σ, (φ p σ).isLeft = σ.isLeft) ∨ ∀ σ, (φ p σ).isLeft = σ.isRight) → FrobShape fun p τ n => (φ p ^ (n + 1)) (Sum.inl τ : Ψ ⊕ Ψ) := by
  intro Ψ _ _ φ h
  unfold FrobShape
  intro p n τ τ'
  exact isLeft_pow_congr (φ p) (h p) (n + 1) _ _ rfl

end GlobalTheory.CompanionTheory.Ar.Num
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FrobeniusShapeOfSidePreservingStatement
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_shape_of_side_preserving : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (φ : ℕ → Equiv.Perm (Ψ ⊕ Ψ)), (∀ p, (∀ σ, (φ p σ).isLeft = σ.isLeft) ∨ ∀ σ, (φ p σ).isLeft = σ.isRight) → FrobShape fun p τ n => (φ p ^ (n + 1)) (Sum.inl τ : Ψ ⊕ Ψ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.frobShape_of_side | exact GlobalTheory.CompanionTheory.Ar.Num.frobShape_of_side | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.frobShape_of_side <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.AbelianFrobeniusLift
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Imports
theorem UpperTheory.Reformulated.B.DYda8.main :
    ∀ (E : Type) [inst : Field E] [inst_1 : NumberField E] [IsGalois ℚ E],
      (∀ (a b : Gal(E/ℚ)), a * b = b * a) →
        ∀ (p : ℕ),
          Nat.Prime p →
            ∃ (φ : Gal(E/ℚ)),
              ∀ (O : Type) [inst_3 : CommRing O] (n : Ideal O),
                n.IsPrime →
                  (↑p : O) ∈ n →
                    ∀ (τ : NumberField.RingOfIntegers E →+* O) (x : NumberField.RingOfIntegers E),
                      (τ : NumberField.RingOfIntegers E → O)
                            ((NumberField.RingOfIntegers.mapRingEquiv φ.toRingEquiv :
                                NumberField.RingOfIntegers E → NumberField.RingOfIntegers E)
                              x) -
                          (τ : NumberField.RingOfIntegers E → O) x ^ p ∈
                        n := by
  intro E _ _ _ hc p hp
  haveI : Fact p.Prime := ⟨hp⟩
  have hp0 : (Ideal.span {(p : ℤ)}) ≠ ⊥ := by
    simpa using hp.ne_zero
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    Ideal.IsPrime.isMaximal ((Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2
      (Nat.prime_iff_prime_int.1 hp)) hp0
  obtain ⟨Q, hQm, hQo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := NumberField.RingOfIntegers E) (Ideal.span {(p : ℤ)})
  have hQbot : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp0 Q
  haveI : Finite (NumberField.RingOfIntegers E ⧸ Q) := Ideal.finiteQuotientOfFreeOfNeBot Q hQbot
  obtain ⟨φ, hφ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ Gal(E/ℚ) Q
  refine ⟨φ, ?_⟩
  intro O _ n hn hpn τ x
  have hP : (n.comap τ).IsPrime := Ideal.comap_isPrime τ n
  have hle : Ideal.span {(p : ℤ)} ≤ (n.comap τ).under ℤ := by
    rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap, Ideal.mem_comap]
    simpa using hpn
  have hund : (n.comap τ).under ℤ = Ideal.span {(p : ℤ)} :=
    (hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle).symm
  have hund' : Q.under ℤ = Ideal.span {(p : ℤ)} := hQo.over.symm
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq ℤ (NumberField.RingOfIntegers E)
    Gal(E/ℚ) Q (n.comap τ) (hund'.trans hund.symm)
  have hcj := hφ.conj g
  have hcomm : g * φ * g⁻¹ = φ := by
    rw [hc g φ, mul_assoc, mul_inv_cancel, mul_one]
  rw [hcomm, ← hg] at hcj
  have hx := hcj x
  rw [hund] at hx
  rw [Int.card_ideal_quot, Ideal.mem_comap] at hx
  have he : (MulSemiringAction.toAlgHom ℤ (NumberField.RingOfIntegers E) φ) x =
      NumberField.RingOfIntegers.mapRingEquiv φ.toRingEquiv x := by
    ext
    rfl
  rw [he, map_sub, map_pow] at hx
  exact hx
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.AbelianFrobeniusLift
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem exists_frobenius_all_primes : ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E], (∀ a b : E ≃ₐ[ℚ] E, a * b = b * a) → ∀ p : ℕ, p.Prime → ∃ φ : E ≃ₐ[ℚ] E, ∀ (O : Type) [CommRing O] (n : Ideal O), n.IsPrime → (p : O) ∈ n → ∀ (τ : 𝓞 E →+* O) (x : 𝓞 E), τ (RingOfIntegers.mapRingEquiv φ.toRingEquiv x) - τ x ^ p ∈ n :=
  _root_.UpperTheory.Reformulated.B.DYda8.main

end GlobalTheory.CompanionTheory.Ar.Num
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.AbelianFrobeniusLiftStatement
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_frobenius_lift : ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E], (∀ a b : E ≃ₐ[ℚ] E, a * b = b * a) → ∀ p : ℕ, p.Prime → ∃ φ : E ≃ₐ[ℚ] E, ∀ (O : Type) [CommRing O] (n : Ideal O), n.IsPrime → (p : O) ∈ n → ∀ (τ : 𝓞 E →+* O) (x : 𝓞 E), τ (RingOfIntegers.mapRingEquiv φ.toRingEquiv x) - τ x ^ p ∈ n := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.exists_frobenius_all_primes | exact GlobalTheory.CompanionTheory.Ar.Num.exists_frobenius_all_primes | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.exists_frobenius_all_primes <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrobeniusLabelsShape
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num

section Labels

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def labelEquiv (H : Host E) : (CMType H ⊕ CMType H) ≃ (E →+* ℂ) :=
  Equiv.ofBijective _ (LabelCount.labelCx_bijective H)

def embPrecomp (g : E ≃ₐ[ℚ] E) : (E →+* ℂ) ≃ (E →+* ℂ) where
  toFun σ := σ.comp (g : E →+* E)
  invFun σ := σ.comp (g.symm : E →+* E)
  left_inv σ := RingHom.ext fun x => by simp
  right_inv σ := RingHom.ext fun x => by simp

def labelPerm (H : Host E) (g : E ≃ₐ[ℚ] E) : Equiv.Perm (CMType H ⊕ CMType H) :=
  (labelEquiv H).trans ((embPrecomp g).trans (labelEquiv H).symm)

theorem labelCx_labelPerm (H : Host E) (g : E ≃ₐ[ℚ] E) (s : CMType H ⊕ CMType H) (x : E) :
    LabelCount.labelCx H (labelPerm H g s) x = LabelCount.labelCx H s (g x) := by
  have h : labelEquiv H (labelPerm H g s) = embPrecomp g (labelEquiv H s) := by
    simp [labelPerm]
  exact RingHom.congr_fun h x

theorem labelCx_rt (H : Host E) (s : CMType H ⊕ CMType H) :
    LabelCount.labelCx H s (H.rt : E) = if s.isLeft then H.rt0 else -H.rt0 := by
  rcases s with τ | τ
  · simp [LabelCount.labelCx, τ.2]
  · simp [LabelCount.labelCx, τ.2, HodgeCptTest.imaginary_root_conj]

theorem labelPerm_side (H : Host E) (g : E ≃ₐ[ℚ] E) :
    (∀ σ, (labelPerm H g σ).isLeft = σ.isLeft) ∨ ∀ σ, (labelPerm H g σ).isLeft = σ.isRight := by
  have hsq : ((H.rt : 𝓞 E) : E) ^ 2 = -(H.d : E) := by
    have := congrArg (fun x : 𝓞 E => (x : E)) H.rt_sq
    simpa using this
  have hg : g (H.rt : E) ^ 2 = (H.rt : E) ^ 2 := by
    rw [← map_pow, hsq]
    simp
  have hne := LabelCount.rt0_ne_neg H
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hg with h | h
  · left
    intro σ
    have h1 := labelCx_labelPerm H g σ (H.rt : E)
    rw [h, labelCx_rt, labelCx_rt] at h1
    cases h2 : (labelPerm H g σ).isLeft <;> cases h3 : σ.isLeft <;> simp [h2, h3] at h1 ⊢
    · exact hne h1.symm
    · exact hne h1
  · right
    intro σ
    have h1 := labelCx_labelPerm H g σ (H.rt : E)
    rw [h, map_neg, labelCx_rt, labelCx_rt] at h1
    have hr : σ.isRight = !σ.isLeft := by cases σ <;> rfl
    rw [hr]
    cases h2 : (labelPerm H g σ).isLeft <;> cases h3 : σ.isLeft <;> simp [h2, h3] at h1 ⊢
    · exact hne h1.symm
    · exact hne h1

variable {H : Host E} {l : Level H}

theorem coe_labelEmb_eq (c : Coeff l) (s : CMType H ⊕ CMType H) (a : 𝓞 E) :
    ((labelEmb c s a : c.F) : ℂ) = LabelCount.labelCx H s (a : E) := by
  rcases s with τ | τ
  · rfl
  · show τ.1 ((H.bar a : 𝓞 E) : E) = (starRingEnd ℂ) (τ.1 (a : E))
    rw [H.bar_eq, IsCMField.complexEmbedding_complexConj]

def labelInt (c : Coeff l) (s : CMType H ⊕ CMType H) : 𝓞 E →+* 𝓞 c.F :=
  (labelEmb c s).codRestrict (integralClosure ℤ c.F).toSubring fun a =>
    IsIntegral.map (labelEmb c s).toIntAlgHom (RingOfIntegers.isIntegral a)

theorem coe_labelInt (c : Coeff l) (s : CMType H ⊕ CMType H) (a : 𝓞 E) :
    ((labelInt c s a : 𝓞 c.F) : c.F) = labelEmb c s a := rfl

theorem labelPerm_isFrobLabels (c : Coeff l) (p : ℕ) (g : E ≃ₐ[ℚ] E)
    (hg : ∀ (O : Type) [CommRing O] (n : Ideal O), n.IsPrime → (p : O) ∈ n → ∀ (τ : 𝓞 E →+* O) (x : 𝓞 E),
      τ (RingOfIntegers.mapRingEquiv g.toRingEquiv x) - τ x ^ p ∈ n) :
    IsFrobLabels c p (labelPerm H g) := by
  intro n hn hp s a u v hu hv
  have key := hg (𝓞 c.F) n hn hp (labelInt c s) a
  have h1 : u = labelInt c s (RingOfIntegers.mapRingEquiv g.toRingEquiv a) := by
    apply RingOfIntegers.ext
    rw [hu, coe_labelInt]
    apply Subtype.ext
    show ((labelEmb c (labelPerm H g s) a : c.F) : ℂ) =
      ((labelEmb c s (RingOfIntegers.mapRingEquiv g.toRingEquiv a) : c.F) : ℂ)
    rw [coe_labelEmb_eq, coe_labelEmb_eq, labelCx_labelPerm]
    rfl
  have h2 : v = labelInt c s a := by
    apply RingOfIntegers.ext
    rw [hv, coe_labelInt]
  rw [h1, h2]
  exact key

end Labels

theorem exists_frob_labels : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E], (∀ a b : E ≃ₐ[ℚ] E, a * b = b * a) → ∀ (H : Host E) (l : Level H) (c : Coeff l) [Fintype (CMType H)] [DecidableEq (CMType H)], ∃ φ : ℕ → Equiv.Perm (CMType H ⊕ CMType H), (∀ p : ℕ, p.Prime → IsFrobLabels c p (φ p)) ∧ FrobShape fun p τ n => (φ p ^ (n + 1)) (Sum.inl τ) := by
  intro E _ _ _ _ hab H l c _ _
  classical
  have h := GlobalTheory.T.abelian_frobenius_lift E hab
  let φ : ℕ → Equiv.Perm (CMType H ⊕ CMType H) := fun p =>
    if hp : p.Prime then labelPerm H (h p hp).choose else 1
  refine ⟨φ, fun p hp => ?_, GlobalTheory.T.frobenius_shape_of_side_preserving _ φ fun p => ?_⟩
  · simp only [φ, dif_pos hp]
    exact labelPerm_isFrobLabels c p _ (h p hp).choose_spec
  · by_cases hp : p.Prime
    · simp only [φ, dif_pos hp]
      exact labelPerm_side H _
    · left
      intro σ
      simp [φ, dif_neg hp]

end GlobalTheory.CompanionTheory.Ar.Num

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrobeniusLabelsShapeStatement
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_labels_shape : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E], (∀ a b : E ≃ₐ[ℚ] E, a * b = b * a) → ∀ (H : Host E) (l : Level H) (c : Coeff l) [Fintype (CMType H)] [DecidableEq (CMType H)], ∃ φ : ℕ → Equiv.Perm (CMType H ⊕ CMType H), (∀ p : ℕ, p.Prime → IsFrobLabels c p (φ p)) ∧ FrobShape fun p τ n => (φ p ^ (n + 1)) (Sum.inl τ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.exists_frob_labels | exact GlobalTheory.CompanionTheory.Ar.Num.exists_frob_labels | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.exists_frob_labels <;> assumption)
end
