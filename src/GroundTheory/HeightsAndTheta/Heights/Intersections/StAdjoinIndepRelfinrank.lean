module

public import Mathlib

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.StAdjoinIndepRelfinrank
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

def AdjoinIndepRelfinrank.Statement : Prop :=
  ∀ (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (L₀ L : IntermediateField F Ω) (ι : Type) (t : ι → Ω),
    L₀ ≤ L → AlgebraicIndependent L t →
      IntermediateField.relfinrank (L₀ ⊔ IntermediateField.adjoin F (Set.range t))
          (L ⊔ IntermediateField.adjoin F (Set.range t)) =
        IntermediateField.relfinrank L₀ L

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.StRankAdjoinFrac
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

abbrev adjoinInclAlgebra (F : Type*) {Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] {S T : Set Ω} (h : S ⊆ T) :
    Algebra (Algebra.adjoin F S) (Algebra.adjoin F T) :=
  (Subalgebra.inclusion (Algebra.adjoin_mono h)).toRingHom.toAlgebra

def RankAdjoinFrac.Statement : Prop :=
  ∀ (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (S T : Set Ω) (h : S ⊆ T),
    letI := adjoinInclAlgebra F h
    Module.finrank (Algebra.adjoin F S) (Algebra.adjoin F T) =
      IntermediateField.relfinrank (IntermediateField.adjoin F S) (IntermediateField.adjoin F T)

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.CardLength
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open IsLocalRing

universe u v

variable {R : Type u} [CommRing R] [IsLocalRing R]

theorem card_eq_card_residueField_of_isSimpleModule (N : Type v) [AddCommGroup N] [Module R N]
    [IsSimpleModule R N] : Nat.card N = Nat.card (ResidueField R) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp ‹IsSimpleModule R N›
  rw [IsLocalRing.eq_maximalIdeal hI] at e
  exact Nat.card_congr e.toEquiv

theorem card_eq_pow_of_length_eq (n : ℕ) : ∀ (M : Type v) [AddCommGroup M] [Module R M],
    Module.length R M = n → Nat.card M = Nat.card (ResidueField R) ^ n := by
  induction n with
  | zero =>
    intro M _ _ h
    have : Subsingleton M := Module.length_eq_zero_iff.mp (by exact_mod_cast h)
    rw [pow_zero]
    exact Nat.card_eq_one_iff_unique.mpr ⟨this, ⟨0⟩⟩
  | succ n ih =>
    intro M _ _ h
    have hfin : IsFiniteLength R M := Module.length_ne_top_iff.mp (by rw [h]; exact ENat.natCast_ne_top _)
    obtain ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hfin
    have hnt : Nontrivial M := Module.length_pos_iff.mp (by rw [h]; exact_mod_cast Nat.succ_pos n)
    obtain ⟨N, hN, -⟩ := (eq_bot_or_exists_atom_le (⊤ : Submodule R M)).resolve_left top_ne_bot
    have hs : IsSimpleModule R N := (isSimpleModule_iff_isAtom).mpr hN
    have hlen := Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
      (LinearMap.exact_subtype_mkQ N)
    rw [h, Module.length_eq_one] at hlen
    have hq : Module.length R (M ⧸ N) = n := by
      have hne : Module.length R (M ⧸ N) ≠ ⊤ := by
        intro ht
        rw [ht] at hlen
        exact ENat.natCast_ne_top _ (hlen.trans (add_top _))
      obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hne
      rw [← hm] at hlen ⊢
      have : n + 1 = 1 + m := by exact_mod_cast hlen
      congr 1
      omega
    rw [Submodule.card_eq_card_quotient_mul_card N, card_eq_card_residueField_of_isSimpleModule (R := R) N, ih (M ⧸ N) hq,
      pow_succ, mul_comm]

theorem card_eq_card_residueField_pow_length (M : Type v) [AddCommGroup M] [Module R M]
    (h : Module.length R M ≠ ⊤) :
    Nat.card M = Nat.card (ResidueField R) ^ (Module.length R M).toNat := by
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp h
  rw [← hn, ENat.toNat_natCast]
  exact card_eq_pow_of_length_eq n M hn.symm

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.StRelAlgClosureFinite
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

def RelAlgClosureFinite.Statement : Prop :=
  ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (S : Finset L),
    IntermediateField.adjoin K (S : Set L) = ⊤ → FiniteDimensional K (algebraicClosure K L)

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.StRankFracDegree
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

def RankFracDegree.Statement : Prop :=
  ∀ (F Ω A B : Type) [Field F] [Field Ω] [Algebra F Ω] [CommRing A] [CommRing B] [Algebra A B]
    (L₀ L : IntermediateField F Ω) (f : A →+* Ω) (g : B →+* Ω),
    Function.Injective f → Function.Injective g → (∀ a, g (algebraMap A B a) = f a) →
    (∀ a, f a ∈ L₀) → (∀ b, g b ∈ L) →
    L₀.toSubfield ≤ Subfield.closure (Set.range f) → L.toSubfield ≤ Subfield.closure (Set.range g) →
    Module.Finite A B → Module.finrank A B = IntermediateField.relfinrank L₀ L

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsLinearQuotient
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial

def LinearQuotient.Statement : Prop :=
  ∀ (F : Type) [Field F] (σ : Type) [Fintype σ] (S : Set (MvPolynomial σ F)),
    (∀ f ∈ S, f.IsHomogeneous 1) →
    ∃ (r : ℕ) (φ : MvPolynomial σ F →ₐ[F] MvPolynomial (Fin r) F), Function.Surjective φ ∧
      RingHom.ker φ = Ideal.span S ∧ ∀ s, (φ (X s)).IsHomogeneous 1

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.StIntClosureLocFinite
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

def IntClosureLocFinite.Statement : Prop :=
  ∀ (F L : Type) [Field F] [Field L] (φ : F →+* L) (S : Finset L), Subfield.closure (S : Set L) = ⊤ →
    ∀ (A : Subring F) (T : Finset F), Subring.closure (T : Set F) ≤ A →
    (∀ z ∈ A, ∃ b ∈ Subring.closure (T : Set F), ∃ c ∈ Subring.closure (T : Set F),
      c ≠ 0 ∧ c⁻¹ ∈ A ∧ z * c = b) →
    letI := (φ.comp A.subtype).toAlgebra
    letI : Module A L := Algebra.toModule
    ∃ t : Finset L, ∀ x : L, IsIntegral A x → x ∈ Submodule.span A (t : Set L)

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.StFinrankAdjoinRange
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

def FinrankAdjoinRange.Statement : Prop :=
  ∀ (F Φ Ω : Type) [Field F] [Field Φ] [Field Ω] [Algebra F Φ] [Algebra F Ω] [Algebra Φ Ω] [IsScalarTower F Φ Ω]
    (S : Set Ω),
    Module.finrank Φ (IntermediateField.adjoin Φ S) =
      IntermediateField.relfinrank (IsScalarTower.toAlgHom F Φ Ω).fieldRange
        ((IsScalarTower.toAlgHom F Φ Ω).fieldRange ⊔ IntermediateField.adjoin F S)

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.StLocAwaySpec
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

def LocAwaySpec.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (Φ : Type) [Field Φ] (φ : R →+* Φ) (S : Finset Φ),
    (∀ c : Φ, ∃ f g : R, φ g ≠ 0 ∧ c = φ f / φ g) →
    ∃ (E : R) (hE : IsUnit (φ E)),
      (∀ c ∈ S, c ∈ Set.range (IsLocalization.Away.lift E hE : Localization.Away E →+* Φ)) ∧
      ∀ (B : Type) [CommRing B] (ψ : R →+* B) (hψ : IsUnit (ψ E)), RingHom.ker φ ≤ RingHom.ker ψ →
        RingHom.ker (IsLocalization.Away.lift E hE : Localization.Away E →+* Φ) ≤
          RingHom.ker (IsLocalization.Away.lift E hψ : Localization.Away E →+* B)

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.StChartPrimElt
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open Polynomial

def ChartPrimElt.Statement : Prop :=
  ∀ (Φ : Type) [Field Φ] [CharZero Φ] (Φ' : Type) [Field Φ'] [Algebra Φ Φ'] (Q : Type) [Fintype Q]
    (r : Q → Φ'),
    FiniteDimensional Φ (IntermediateField.adjoin Φ (Set.range r)) →
    ∃ (τ : MvPolynomial Q Φ) (g : Q → Φ[X]) (u : Φ[X]),
      (minpoly Φ (MvPolynomial.aeval r τ)).natDegree =
        Module.finrank Φ (IntermediateField.adjoin Φ (Set.range r)) ∧
      (∀ q, aeval (MvPolynomial.aeval r τ) (g q) = r q) ∧
      minpoly Φ (MvPolynomial.aeval r τ) ∣ u * derivative (minpoly Φ (MvPolynomial.aeval r τ)) - 1 ∧
      minpoly Φ (MvPolynomial.aeval r τ) ∣ MvPolynomial.aeval g τ - X ∧
      ∀ q, r q ≠ 0 → ∃ h : Φ[X], minpoly Φ (MvPolynomial.aeval r τ) ∣ h * g q - 1

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.StChartSpecCount
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

def ChartSpecCount.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (Φ : Type) [Field Φ] [CharZero Φ] (Φ' : Type) [Field Φ'] [Algebra Φ Φ']
    (φ : R →+* Φ) (Q : Type) [Fintype Q] (r : Q → Φ'),
    (∀ c : Φ, ∃ f g : R, φ g ≠ 0 ∧ c = φ f / φ g) →
    FiniteDimensional Φ (IntermediateField.adjoin Φ (Set.range r)) →
    ∃ E : R, φ E ≠ 0 ∧ ∀ ψ : R →+* ℂ, RingHom.ker φ ≤ RingHom.ker ψ → ψ E ≠ 0 →
      {y : Q → ℂ | ∀ F : MvPolynomial Q R, MvPolynomial.eval₂ ((algebraMap Φ Φ').comp φ) r F = 0 →
          MvPolynomial.eval₂ ψ y F = 0}.Finite ∧
      {y : Q → ℂ | ∀ F : MvPolynomial Q R, MvPolynomial.eval₂ ((algebraMap Φ Φ').comp φ) r F = 0 →
          MvPolynomial.eval₂ ψ y F = 0}.ncard =
        Module.finrank Φ (IntermediateField.adjoin Φ (Set.range r)) ∧
      ∀ y : Q → ℂ, (∀ F : MvPolynomial Q R, MvPolynomial.eval₂ ((algebraMap Φ Φ').comp φ) r F = 0 →
          MvPolynomial.eval₂ ψ y F = 0) → ∀ q, r q ≠ 0 → y q ≠ 0

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PProjBundleMultiHomogGrad
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial

section Graded

variable {σ τ R M : Type*} [CommRing R] [AddCommMonoid M]

theorem aeval_weightedHomogeneousComponent_of_weights (w : σ → M) (ω : τ → M)
    (e : σ → MvPolynomial τ R) (he : ∀ v, IsWeightedHomogeneous ω (e v) (w v)) (m : M)
    (p : MvPolynomial σ R) :
    aeval e (weightedHomogeneousComponent w m p) = weightedHomogeneousComponent ω m (aeval e p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial d c =>
    have hmon : IsWeightedHomogeneous ω (aeval e (monomial d c)) (Finsupp.weight w d) := by
      rw [aeval_monomial, Finsupp.weight_apply, algebraMap_eq]
      have := (isWeightedHomogeneous_C ω c).mul (IsWeightedHomogeneous.prod d.support
        (fun v => e v ^ d v) (fun v => d v • w v) (fun v _ => (he v).pow (d v)))
      rw [zero_add] at this
      exact this
    by_cases hdm : Finsupp.weight w d = m
    · have hmon' : IsWeightedHomogeneous ω (aeval e (monomial d c)) m := hdm ▸ hmon
      rw [(isWeightedHomogeneous_monomial _ d c hdm).weightedHomogeneousComponent_same,
        hmon'.weightedHomogeneousComponent_same]
    · rw [(isWeightedHomogeneous_monomial w d c
        (m := Finsupp.weight w d) rfl).weightedHomogeneousComponent_ne m
        (Ne.symm hdm), hmon.weightedHomogeneousComponent_ne m (Ne.symm hdm), map_zero]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]

end Graded

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end
