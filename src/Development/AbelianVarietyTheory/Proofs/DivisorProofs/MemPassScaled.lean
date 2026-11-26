module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitCocycleLiftObstructionPullbackNaturality

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDenominatorPrimeToLFiniteAdele
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDenominatorPrimeToLFiniteAdele
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)

namespace GlobalTheory.HilbFam.AdeleDen

theorem val_nat {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) :
    Valued.v ((n : w.adicCompletion E)) = w.valuation E (algebraMap (𝓞 E) E (n : 𝓞 E)) := by
  rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w]
  congr 1
  rw [map_natCast]
  exact (map_natCast (algebraMap E (w.adicCompletion E)) n).symm

theorem val_nat_le {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) :
    Valued.v ((n : w.adicCompletion E)) ≤ 1 := by
  rw [val_nat]; exact w.valuation_le_one _

theorem exists_nat_mem {E : Type} [Field E] [NumberField E] {l : ℕ} (hl : l.Prime)
    (w : HeightOneSpectrum (𝓞 E)) (hw : (l : 𝓞 E) ∉ w.asIdeal) :
    ∃ m : ℕ, ¬ l ∣ m ∧ (m : 𝓞 E) ∈ w.asIdeal := by
  have h0 : Ideal.absNorm w.asIdeal ≠ 0 := fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  obtain ⟨k, m, hm, e⟩ := Nat.exists_eq_pow_mul_and_not_dvd h0 l hl.ne_one
  refine ⟨m, hm, ?_⟩
  have h := Ideal.absNorm_mem w.asIdeal
  rw [e] at h
  push_cast at h
  rcases w.isPrime.mem_or_mem h with h | h
  · exact absurd (w.isPrime.mem_of_pow_mem _ h) hw
  · exact h

theorem exists_local {E : Type} [Field E] [NumberField E] {l : ℕ} (hl : l.Prime)
    (w : HeightOneSpectrum (𝓞 E)) (hw : (l : 𝓞 E) ∉ w.asIdeal) (x : w.adicCompletion E) :
    ∃ m : ℕ, ¬ l ∣ m ∧ Valued.v ((m : w.adicCompletion E) * x) ≤ 1 := by
  obtain ⟨m, hm, hmw⟩ := exists_nat_mem hl w hw
  by_cases hx : Valued.v x = 0
  · exact ⟨m, hm, by simp [hx]⟩
  have h1 : Valued.v ((m : w.adicCompletion E)) < 1 := by
    rw [val_nat]; exact (w.valuation_lt_one_iff_mem _).mpr hmw
  obtain ⟨n, hn⟩ := exists_pow_lt₀ h1 (Units.mk0 _ (inv_ne_zero hx))
  refine ⟨m ^ n, fun h => hm (hl.dvd_of_dvd_pow h), ?_⟩
  rw [Nat.cast_pow, map_mul, map_pow]
  calc _ ≤ (Valued.v x)⁻¹ * Valued.v x := mul_le_mul_left hn.le _
    _ = 1 := inv_mul_cancel₀ hx

theorem exists_den_prime_to : ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) (z : Af E), l.Prime → (∀ w : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ w.asIdeal → Valued.v (z w) ≤ 1) → ∃ M : ℕ, ¬ l ∣ M ∧ ∀ w : HeightOneSpectrum (𝓞 E), Valued.v ((algebraMap E (Af E) (M : E) * z) w) ≤ 1 := by
  intro E _ _ l z hl hz
  have key : ∀ w : HeightOneSpectrum (𝓞 E), ∃ m : ℕ, ¬ l ∣ m ∧
      Valued.v ((m : w.adicCompletion E) * z w) ≤ 1 := by
    intro w
    by_cases hw : (l : 𝓞 E) ∈ w.asIdeal
    · exact ⟨1, hl.not_dvd_one, by simpa using hz w hw⟩
    · exact exists_local hl w hw _
  choose m hm hmz using key
  have hfin : {w : HeightOneSpectrum (𝓞 E) | ¬ z w ∈ w.adicCompletionIntegers E}.Finite :=
    Filter.eventually_cofinite.mp z.2
  refine ⟨∏ w ∈ hfin.toFinset, m w, ?_, fun w => ?_⟩
  · have hprod : ∀ s : Finset (HeightOneSpectrum (𝓞 E)), ¬ l ∣ ∏ w ∈ s, m w := by
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using hl.not_dvd_one
      | @insert a s ha ih =>
        simp only [Finset.prod_insert ha]
        intro h
        rcases hl.dvd_mul.mp h with h | h
        · exact hm a h
        · exact ih h
    exact hprod _
  · have e : ∀ M : ℕ, (algebraMap E (Af E) (M : E) * z) w = (M : w.adicCompletion E) * z w := by
      intro M
      rw [← map_natCast (algebraMap E (w.adicCompletion E)) M]
      rfl
    rw [e]
    by_cases hw : w ∈ hfin.toFinset
    · rw [← Finset.prod_erase_mul _ _ hw, Nat.cast_mul, mul_assoc, map_mul]
      exact mul_le_one' (val_nat_le _ _) (hmz w)
    · have : z w ∈ w.adicCompletionIntegers E := by simpa using hw
      rw [map_mul]
      exact mul_le_one' (val_nat_le _ _) this

end GlobalTheory.HilbFam.AdeleDen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDenominatorPrimeToLFiniteAdeleStatement
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_denominator_prime_to_l_finiteAdele : ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) (z : Af E), l.Prime → (∀ w : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ w.asIdeal → Valued.v (z w) ≤ 1) → ∃ M : ℕ, ¬ l ∣ M ∧ ∀ w : HeightOneSpectrum (𝓞 E), Valued.v ((algebraMap E (Af E) (M : E) * z) w) ≤ 1 := by
  first | exact @GlobalTheory.HilbFam.AdeleDen.exists_den_prime_to | exact GlobalTheory.HilbFam.AdeleDen.exists_den_prime_to | (intros; apply GlobalTheory.HilbFam.AdeleDen.exists_den_prime_to <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmLatticeExistsMultipleIntegralPrimeToL
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmLatticeExistsMultipleIntegralPrimeToL
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)

namespace GlobalTheory.HilbFam.LatticeUp

theorem exists_mul_integral : ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) (c : Ideal (OF E)) (y : (Af E)ˣ), l.Prime →
    OneOver l y → ∃ M : ℕ, ¬ l ∣ M ∧ ∀ x ∈ lattice c y, IsIntegral ℤ ((M : E) * x) := by
  intro E _ _ l c y hl hy
  obtain ⟨M, hM, hMv⟩ := GlobalTheory.T.exists_denominator_prime_to_l_finiteAdele E l (y : Af E) hl fun w hw => by rw [hy w hw, map_one]
  refine ⟨M, hM, fun x hx => ?_⟩
  have hx' : algebraMap E (Af E) x * (↑y⁻¹ : Af E) ∈ hatO c := hx
  have key : algebraMap E (Af E) ((M : E) * x) =
      (algebraMap E (Af E) x * (↑y⁻¹ : Af E)) * (algebraMap E (Af E) (M : E) * (y : Af E)) := by
    have hyy : (↑y⁻¹ : Af E) * (y : Af E) = 1 := y.inv_mul
    rw [map_mul]
    calc algebraMap E (Af E) (M : E) * algebraMap E (Af E) x
        = algebraMap E (Af E) (M : E) * algebraMap E (Af E) x * ((↑y⁻¹ : Af E) * (y : Af E)) := by rw [hyy, mul_one]
      _ = _ := by ring
  obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E ((M : E) * x) fun v => by
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v ((M : E) * x)]
    have h1 := GlobalTheory.CMVal.ObjModel.hatO_integral hx' v
    have h2 := hMv v
    have : (algebraMap E (Af E) ((M : E) * x)) v =
        (algebraMap E (Af E) x * (↑y⁻¹ : Af E)) v * (algebraMap E (Af E) (M : E) * (y : Af E)) v := by
      rw [key]; rfl
    rw [show ((((M : E) * x : E)) : v.adicCompletion E) = (algebraMap E (Af E) ((M : E) * x)) v from rfl, this, map_mul]
    exact mul_le_one' h1 h2
  rw [← hb]
  exact (b.isIntegral_coe)

end GlobalTheory.HilbFam.LatticeUp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmLatticeExistsMultipleIntegralPrimeToLStatement
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmLattice_exists_multiple_integral_prime_to_l : ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) (c : Ideal (OF E)) (y : (Af E)ˣ), l.Prime → OneOver l y → ∃ M : ℕ, ¬ l ∣ M ∧ ∀ x ∈ lattice c y, IsIntegral ℤ ((M : E) * x) := by
  first | exact @GlobalTheory.HilbFam.LatticeUp.exists_mul_integral | exact GlobalTheory.HilbFam.LatticeUp.exists_mul_integral | (intros; apply GlobalTheory.HilbFam.LatticeUp.exists_mul_integral <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatMulIntegralMemCmLatticePrimeTo
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatMulIntegralMemCmLatticePrimeTo
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)

namespace GlobalTheory.HilbFam.LatDen

theorem nat_mul_integral_mem_lattice : ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) (c : Ideal (OF E)) (y : (Af E)ˣ) (R : ℕ), l.Prime → OneOver l y → 0 < R → (R : OF E) ∈ c → ∃ M : ℕ, ¬ l ∣ M ∧ ∀ x : E, IsIntegral ℤ x → ((M * R : ℕ) : E) * x ∈ lattice c y := by
  intro E _ _ l c y R hl hy hR hRc
  obtain ⟨M, hM, hMz⟩ := GlobalTheory.HilbFam.AdeleDen.exists_den_prime_to E l ((y⁻¹ : (Af E)ˣ) : Af E) hl (fun w hw => by
    have h1 : ((y⁻¹ : (Af E)ˣ) : Af E) w * (y : Af E) w = 1 := by
      have h := congrArg (fun a : Af E => a w) (Units.inv_mul y)
      exact h
    rw [hy w hw, mul_one] at h1
    rw [h1, map_one])
  refine ⟨M, hM, fun x hx => ?_⟩
  show algebraMap E (Af E) (((M * R : ℕ) : E) * x) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c
  refine GlobalTheory.CMVal.LatEnt.mem_hatO_of_sub hR hRc (zero_mem _) fun P => ?_
  have e : (algebraMap E (Af E) (((M * R : ℕ) : E) * x) * ((y⁻¹ : (Af E)ˣ) : Af E)) P - (0 : Af E) P =
      (R : P.adicCompletion E) * (algebraMap E (P.adicCompletion E) x *
        (algebraMap E (Af E) (M : E) * ((y⁻¹ : (Af E)ˣ) : Af E)) P) := by
    rw [show (0 : Af E) P = 0 from rfl, sub_zero,
      show (algebraMap E (Af E) (M : E) * ((y⁻¹ : (Af E)ˣ) : Af E)) P =
        algebraMap E (P.adicCompletion E) (M : E) * ((y⁻¹ : (Af E)ˣ) : Af E) P from rfl]
    show algebraMap E (P.adicCompletion E) (((M * R : ℕ) : E) * x) * ((y⁻¹ : (Af E)ˣ) : Af E) P = _
    rw [map_mul, map_natCast, map_natCast]
    push_cast
    ring
  have hx1 : Valued.v (algebraMap E (P.adicCompletion E) x) ≤ 1 := by
    have h2 : Valued.v (algebraMap E (P.adicCompletion E) x) = P.valuation E x := by
      rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P]
      rfl
    rw [h2]
    have : x = algebraMap (𝓞 E) E ⟨x, hx⟩ := rfl
    rw [this]
    exact P.valuation_le_one _
  rw [e, map_mul, GlobalTheory.CMVal.LatEnt.radN, map_mul]
  exact mul_le_of_le_one_right' (mul_le_one' hx1 (hMz P))

end GlobalTheory.HilbFam.LatDen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatMulIntegralMemCmLatticePrimeToStatement
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nat_mul_integral_mem_cmLattice_prime_to : ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) (c : Ideal (OF E)) (y : (Af E)ˣ) (R : ℕ), l.Prime → OneOver l y → 0 < R → (R : OF E) ∈ c → ∃ M : ℕ, ¬ l ∣ M ∧ ∀ x : E, IsIntegral ℤ x → ((M * R : ℕ) : E) * x ∈ lattice c y := by
  first | exact @GlobalTheory.HilbFam.LatDen.nat_mul_integral_mem_lattice | exact GlobalTheory.HilbFam.LatDen.nat_mul_integral_mem_lattice | (intros; apply GlobalTheory.HilbFam.LatDen.nat_mul_integral_mem_lattice <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationBoundOfMulSqIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationBoundOfMulSqIntegral
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)

noncomputable section

namespace GlobalTheory.SizeSqIntegral

theorem sz_nat_val (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (D : ℕ) :
    Sz l lam (-(padicValNat l D : ℝ)) (D : ℂ) := by
  have h := GlobalTheory.SizeRat.sz_ratCast l lam (D : ℚ) (-(padicValNat l D : ℝ)) (by
    rw [padicValRat.of_nat, Nat.padicValNat_def]; simp)
  simpa using h

theorem sz_zero_of_isIntegral (l : ℕ) [hl : Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (x : ℂ)
    (h : IsIntegral ℤ x) : Sz l lam 0 x :=
  GlobalTheory.SzRules.sz_of_isIntegral 1 x (fun hd => hl.out.one_lt.ne' (Nat.dvd_one.1 hd)) (by simpa using h)

theorem main : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (D M : ℕ) (x : ℂ), 0 < D → IsIntegral ℤ ((D : ℂ) * x ^ 2) → Sz l lam (-(padicValNat l D : ℝ) / 2) ((D : ℂ) * x) ∧ Sz l lam (-(padicValNat l D : ℝ) / 2) ((M * l ^ padicValNat l D : ℕ) : ℂ) := by
  intro l hl lam D M x _ hx
  constructor
  · apply GlobalTheory.SzRules.sz_of_sq
    have h := GlobalTheory.SzRules.sz_mul (sz_nat_val l lam D) (sz_zero_of_isIntegral l lam _ hx)
    rw [add_zero] at h
    convert h using 1
    ring
  · have h1 := sz_nat_val l lam (l ^ padicValNat l D)
    rw [Nat.padicValNat_def, Nat.multiplicity_prime_pow] at h1
    have h2 : Sz l lam 0 (M : ℂ) := sz_zero_of_isIntegral l lam _ (by simpa using (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (M : ℤ))))
    have h := GlobalTheory.SzRules.sz_mul h2 h1
    rw [zero_add, ← Nat.cast_mul] at h
    refine GlobalTheory.SzRules.sz_mono ?_ h
    have : (0 : ℝ) ≤ (padicValNat l D : ℝ) := Nat.cast_nonneg _
    linarith

end GlobalTheory.SizeSqIntegral
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationBoundOfMulSqIntegralStatement
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicValuation_bound_of_mul_sq_integral : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (D M : ℕ) (x : ℂ), 0 < D → IsIntegral ℤ ((D : ℂ) * x ^ 2) → Sz l lam (-(padicValNat l D : ℝ) / 2) ((D : ℂ) * x) ∧ Sz l lam (-(padicValNat l D : ℝ) / 2) ((M * l ^ padicValNat l D : ℕ) : ℂ) := by
  first | exact @GlobalTheory.SizeSqIntegral.main | exact GlobalTheory.SizeSqIntegral.main | (intros; apply GlobalTheory.SizeSqIntegral.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralDiscMulCoordsOfCmFieldIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralDiscMulCoordsOfCmFieldIntegral
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)

namespace GlobalTheory.HilbFam

theorem isIntegral_coord_of_isIntegral (E : Type) [Field E] [NumberField E] [IsCMField E] (θ : E) (D : ℕ)
    (x : Fin 2 → FR E) (_hD : 0 < D) (hθ : IsIntegral ℤ θ)
    (hr : (θ - IsCMField.complexConj E θ) ^ 2 = -(D : E))
    (hu : IsIntegral ℤ ((x 0 : E) * θ + (x 1 : E))) (j : Fin 2) :
    IsIntegral ℤ ((D : FR E) * x j ^ 2) ∧ IsIntegral ℤ ((D : FR E) * x j) := by
  have hc : ∀ y : E, IsIntegral ℤ y → IsIntegral ℤ (IsCMField.complexConj E y) := fun y hy =>
    map_isIntegral_int (IsCMField.complexConj E) hy
  have hfix : ∀ y : FR E, IsCMField.complexConj E (y : E) = y := fun y =>
    IsCMField.complexConj_apply_eq_self E y
  set r := θ - IsCMField.complexConj E θ with hrdef
  have hri : IsIntegral ℤ r := hθ.sub (hc _ hθ)
  have h0 : IsIntegral ℤ ((x 0 : E) * r) := by
    have := hu.sub (hc _ hu)
    rw [map_add (f := _), map_mul, hfix, hfix] at this
    have e : (x 0 : E) * r = (x 0 : E) * θ + (x 1 : E) -
        ((x 0 : E) * IsCMField.complexConj E θ + (x 1 : E)) := by rw [hrdef]; ring
    rw [e]; exact this
  have h1 : IsIntegral ℤ ((x 1 : E) * r) := by
    have := (hu.mul hri).sub (h0.mul hθ)
    have e : (x 1 : E) * r = ((x 0 : E) * θ + (x 1 : E)) * r - (x 0 : E) * r * θ := by ring
    rw [e]; exact this
  have hj : IsIntegral ℤ ((x j : E) * r) := by
    fin_cases j
    · exact h0
    · exact h1
  have hD' : (D : E) = -r ^ 2 := by rw [hr]; ring
  have hinj : Function.Injective (algebraMap (FR E) E) := (algebraMap (FR E) E).injective
  have hx : algebraMap (FR E) E (x j) = (x j : E) := rfl
  constructor
  · rw [← (isIntegral_algebraMap_iff (B := E)), map_mul, map_pow, map_natCast, hx, hD']
    have e : -r ^ 2 * (x j : E) ^ 2 = -((x j : E) * r * ((x j : E) * r)) := by ring
    rw [e]; exact (hj.mul hj).neg
  · rw [← (isIntegral_algebraMap_iff (B := E)), map_mul, map_natCast, hx, hD']
    have e : -r ^ 2 * (x j : E) = -((x j : E) * r * r) := by ring
    rw [e]; exact (hj.mul hri).neg

end GlobalTheory.HilbFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralDiscMulCoordsOfCmFieldIntegralStatement
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_disc_mul_coords_of_cmField_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (θ : E) (D : ℕ) (x : Fin 2 → FR E), 0 < D → IsIntegral ℤ θ → (θ - IsCMField.complexConj E θ) ^ 2 = -(D : E) → IsIntegral ℤ ((x 0 : E) * θ + (x 1 : E)) → ∀ j, IsIntegral ℤ ((D : FR E) * x j ^ 2) ∧ IsIntegral ℤ ((D : FR E) * x j) := by
  first | exact @GlobalTheory.HilbFam.isIntegral_coord_of_isIntegral | exact GlobalTheory.HilbFam.isIntegral_coord_of_isIntegral | (intros; apply GlobalTheory.HilbFam.isIntegral_coord_of_isIntegral <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoprimeMulPrimePowMemConductor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoprimeMulPrimePowMemConductor
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)

namespace GlobalTheory.HilbFam.CondNumber

theorem exists_mul_pow_mem {K : Type} [Field K] [NumberField K] {l : ℕ} (hl : l.Prime) {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    ∃ M j : ℕ, ¬ l ∣ M ∧ (M : 𝓞 K) * (l : 𝓞 K) ^ j ∈ I := by
  have h0 : Ideal.absNorm I ≠ 0 := fun h => hI (Ideal.absNorm_eq_zero_iff.1 h)
  obtain ⟨j, M, hM, he⟩ := Nat.exists_eq_pow_mul_and_not_dvd h0 l hl.ne_one
  refine ⟨M, j, hM, ?_⟩
  have := Ideal.absNorm_mem I
  rw [he] at this
  push_cast at this
  rwa [mul_comm] at this

theorem mem_of_forall_pow {R : Type} [CommRing R] [IsDedekindDomain R] {I : Ideal R} (hI : I ≠ ⊥) {x : R}
    (h : ∀ (v : HeightOneSpectrum R) (n : ℕ), v.asIdeal ^ n ∣ I → x ∈ v.asIdeal ^ n) : x ∈ I := by
  have e := Ideal.iInf_maxPowDividing_eq (I := I) hI
  rw [← e, Submodule.mem_iInf]
  intro v
  apply h v
  rw [Ideal.dvd_iff_le]
  exact e.ge.trans (iInf_le _ v)

theorem exists_mem_condQ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))), l.Prime → IsBaseCond 𝔣 → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) → ∃ M : ℕ, ¬ l ∣ M ∧ ((M * l ^ a0 𝔣 l : ℕ) : OF E) ∈ condQ 𝔣 Q := by
  intro E _ _ _ l 𝔣 Q hl h𝔣 hQ
  obtain ⟨M₁, j, hM₁, hj⟩ := exists_mul_pow_mem hl h𝔣.1
  have h1 : (M₁ : OF E) * (l : OF E) ^ a0 𝔣 l ∈ 𝔣 := by
    refine mem_of_forall_pow h𝔣.1 fun v n hn => ?_
    by_cases hv : (l : OF E) ∈ v.asIdeal
    · have hfin : FiniteMultiplicity v.asIdeal 𝔣 :=
        FiniteMultiplicity.of_not_isUnit v.irreducible.not_isUnit h𝔣.1
      have hle : n ≤ a0 𝔣 l :=
        (hfin.le_multiplicity_of_pow_dvd hn).trans (GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.expIn_le_maxConductorExponentOverPrime h𝔣 hv)
      exact Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right hle (Ideal.pow_mem_pow hv _))
    · have h2 := Ideal.le_of_dvd hn hj
      have := v.isPrime
      rcases Ideal.IsPrime.mem_pow_mul v.asIdeal h2 with h3 | h3
      · exact Ideal.mul_mem_right _ _ h3
      · exact absurd (v.isPrime.mem_of_pow_mem _ h3) hv
  have h2 : ∀ q : HeightOneSpectrum (OF E), ∃ M : ℕ, ¬ l ∣ M ∧ (q ∈ Q → (M : OF E) ∈ q.asIdeal) := by
    intro q
    obtain ⟨M, i, hM, hi⟩ := exists_mul_pow_mem hl q.ne_bot
    refine ⟨M, hM, fun hq => ?_⟩
    rcases q.isPrime.mem_or_mem hi with h3 | h3
    · exact h3
    · exact absurd (q.isPrime.mem_of_pow_mem _ h3) (hQ q hq)
  choose N hN hNq using h2
  refine ⟨M₁ * ∏ q ∈ Q, N q, ?_, ?_⟩
  · intro h
    rcases (Nat.Prime.dvd_mul hl).1 h with h | h
    · exact hM₁ h
    · obtain ⟨q, -, hq⟩ := (Prime.dvd_finsetProd_iff hl.prime _).1 h
      exact hN q hq
  · have h3 : (∏ q ∈ Q, (N q : OF E)) ∈ ∏ q ∈ Q, q.asIdeal := Ideal.prod_mem_prod fun q hq => hNq q hq
    have h4 := Ideal.mul_mem_mul h1 h3
    unfold condQ
    convert h4 using 1
    push_cast
    ring

end GlobalTheory.HilbFam.CondNumber
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoprimeMulPrimePowMemConductorStatement
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coprime_mul_prime_pow_mem_conductor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))), l.Prime → IsBaseCond 𝔣 → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) → ∃ M : ℕ, ¬ l ∣ M ∧ ((M * l ^ a0 𝔣 l : ℕ) : OF E) ∈ condQ 𝔣 Q := by
  first | exact @GlobalTheory.HilbFam.CondNumber.exists_mem_condQ | exact GlobalTheory.HilbFam.CondNumber.exists_mem_condQ | (intros; apply GlobalTheory.HilbFam.CondNumber.exists_mem_condQ <;> assumption)
end
end

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)

namespace GlobalTheory.RoadE

open GlobalTheory.CMVal

variable {E : Type} [Field E] [NumberField E]

def passScaled (t : E) (c : Ideal (OF E)) (y : (Af E)ˣ) (N : ℕ) : Lat (FR E) where
  carrier := {x | ∃ y' ∈ lattice c y, (N : E) * y' = ptE t x}
  add_mem' := fun {x x'} ⟨a, ha, hxa⟩ ⟨b, hb, hxb⟩ => ⟨a + b, (latticeSub c y).add_mem ha hb, by
    have : ptE t (x + x') = ptE t x + ptE t x' := by simp only [ptE, Pi.add_apply, Subfield.coe_add]; ring
    rw [this, ← hxa, ← hxb]; ring⟩
  zero_mem' := ⟨0, (latticeSub c y).zero_mem, by simp [ptE]⟩
  smul_mem' := fun a x ⟨b, hb, hxb⟩ => ⟨algebraMap (OF E) E a * b, mul_mem_lattice (algebraMap_mem_orderC c a) hb, by
    rw [ptE_smul, ← hxb]; ring⟩

end GlobalTheory.RoadE

namespace GlobalTheory.RoadE
open GlobalTheory.CMVal

theorem passl : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) (y : (Af E)ˣ) (θ : E) (D M₀ : ℕ), IsBaseCond 𝔣 → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) → OneOver l y → 0 < D → IsIntegral ℤ θ → (θ - IsCMField.complexConj E θ) ^ 2 = -(D : E) → ¬ l ∣ M₀ → ∃ (M M' : ℕ) (L : Lat (FR E)), ¬ l ∣ M ∧ ¬ l ∣ M' ∧ M₀ ∣ M' ∧ HasLevel (M' * l ^ (padicValNat l D + a0 𝔣 l)) L ∧ (∀ x : Fin 2 → FR E, x ∈ L ↔ ∃ y' ∈ lattice (condQ 𝔣 Q) y, ((M * D : ℕ) : E) * y' = (x 0 : E) * θ + (x 1 : E)) ∧ (∀ v ∈ L, ∀ (j : Fin 2) (i : Emb (FR E)), Sz l lam (-(padicValNat l D : ℝ) / 2) ((i (v j) : ℝ) : ℂ)) ∧ Sz l lam (-(padicValNat l D : ℝ) / 2) ((M' * l ^ (padicValNat l D + a0 𝔣 l) : ℕ) : ℂ) := by
  intro E _ _ _ l _ lam 𝔣 Q y θ D M₀ hf hQ hy hD hθ hθD hM₀
  have hl : l.Prime := Fact.out
  set c := condQ 𝔣 Q with hc
  obtain ⟨M, hMl, hMint⟩ := GlobalTheory.T.cmLattice_exists_multiple_integral_prime_to_l E l c y hl hy
  obtain ⟨M₁, hM₁l, hM₁c⟩ := GlobalTheory.T.exists_coprime_mul_prime_pow_mem_conductor E l 𝔣 Q hl hf hQ
  have hM₁0 : M₁ ≠ 0 := by rintro rfl; exact hM₁l (dvd_zero l)
  have hM0 : M ≠ 0 := by rintro rfl; exact hMl (dvd_zero l)
  have hR : 0 < M₁ * l ^ a0 𝔣 l := Nat.pos_of_ne_zero (mul_ne_zero hM₁0 (pow_ne_zero _ hl.ne_zero))
  obtain ⟨M₂, hM₂l, hM₂⟩ := GlobalTheory.T.nat_mul_integral_mem_cmLattice_prime_to E l c y (M₁ * l ^ a0 𝔣 l) hl hy hR hM₁c
  obtain ⟨D', hD'⟩ := (fun {p n : ℕ} => _root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat p n)) (p := l) (n := D)
  have hD'l : ¬ l ∣ D' := by
    rintro ⟨e, he⟩
    apply pow_succ_padicValNat_not_dvd (p := l) hD.ne'
    refine ⟨e, ?_⟩
    calc D = l ^ padicValNat l D * D' := hD'
      _ = l ^ (multiplicity l D + 1) * e := by rw [he, ← Nat.padicValNat_def, pow_succ]; ring
  have hnat : ∀ n : ℕ, IsIntegral ℤ (n : E) := fun n => by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := E) (x := (n : ℤ)))
  have hDE : (D : E) ≠ 0 := by exact_mod_cast hD.ne'
  have hDF : (D : FR E) ≠ 0 := by exact_mod_cast hD.ne'
  have key : ∀ x ∈ passScaled θ c y (M * D), ∀ j,
      IsIntegral ℤ ((D : FR E) * ((D : FR E)⁻¹ * x j) ^ 2) ∧ IsIntegral ℤ (x j) := by
    rintro x ⟨y', hy', hxy⟩ j
    have hpt : (((D : FR E)⁻¹ * x 0 : FR E) : E) * θ + (((D : FR E)⁻¹ * x 1 : FR E) : E) = (M : E) * y' := by
      simp only [ptE] at hxy
      push_cast at hxy ⊢
      have h' : (M : E) * y' = (D : E)⁻¹ * (((x 0 : FR E) : E) * θ + ((x 1 : FR E) : E)) := by
        rw [← hxy]; field_simp
      rw [h']; ring
    have h := GlobalTheory.T.isIntegral_disc_mul_coords_of_cmField_integral E θ D (fun j => (D : FR E)⁻¹ * x j) hD hθ hθD (by rw [hpt]; exact hMint y' hy') j
    refine ⟨h.1, ?_⟩
    have h2 := h.2
    simp only [mul_inv_cancel_left₀ hDF] at h2
    exact h2
  refine ⟨M, M₀ * M * D' * M₂ * M₁, passScaled θ c y (M * D), hMl, ?_, ⟨M * D' * M₂ * M₁, by ring⟩, ?_, ?_, ?_, ?_⟩
  · intro h
    rcases (Nat.Prime.dvd_mul hl).1 h with h | h
    rcases (Nat.Prime.dvd_mul hl).1 h with h | h
    rcases (Nat.Prime.dvd_mul hl).1 h with h | h
    rcases (Nat.Prime.dvd_mul hl).1 h with h | h
    exacts [hM₀ h, hMl h, hD'l h, hM₂l h, hM₁l h]
  · refine ⟨fun w hw => ?_, fun x hx => ?_⟩
    · have hwj : ∀ j, IsIntegral ℤ ((w j : FR E) : E) := by
        intro j
        have hwj1 : w j ∈ (1 : Submodule (𝓞 (FR E)) (FR E)) := Submodule.mem_pi.1 hw j (Set.mem_univ j)
        obtain ⟨a, ha⟩ := Submodule.mem_one.1 hwj1
        rw [← ha]
        exact (RingOfIntegers.isIntegral_coe a).map (RingHom.toIntAlgHom (maximalRealSubfield E).subtype)
      have hP : IsIntegral ℤ ((M₀ : E) * (((w 0 : FR E) : E) * θ + ((w 1 : FR E) : E))) :=
        (hnat M₀).mul (((hwj 0).mul hθ).add (hwj 1))
      refine ⟨_, hM₂ _ hP, ?_⟩
      have e : (D : E) = (l : E) ^ padicValNat l D * D' := by exact_mod_cast hD'
      simp only [ptE, Pi.smul_apply, Algebra.smul_def, Subfield.coe_mul, map_natCast]
      push_cast
      linear_combination ((M : E) * M₂ * M₁ * (l : E) ^ a0 𝔣 l * M₀ * (((w 0 : FR E) : E) * θ + ((w 1 : FR E) : E))) * e
    · intro j _
      change x j ∈ (1 : Submodule (𝓞 (FR E)) (FR E))
      rw [Submodule.mem_one]
      exact ⟨⟨x j, (key x hx j).2⟩, rfl⟩
  · intro x; exact Iff.rfl
  · intro w hw j i
    have h1 := (key w hw j).1
    set f : FR E →ₐ[ℤ] ℂ := RingHom.toIntAlgHom (Complex.ofRealHom.comp i) with hf
    have h2 : IsIntegral ℤ ((D : ℂ) * (f ((D : FR E)⁻¹ * w j)) ^ 2) := by
      have := h1.map f
      simpa [map_mul, map_pow, map_natCast] using this
    have h3 := (GlobalTheory.T.algebraicValuation_bound_of_mul_sq_integral l lam D 0 (f ((D : FR E)⁻¹ * w j)) hD h2).1
    have h4 : (D : ℂ) * f ((D : FR E)⁻¹ * w j) = ((i (w j) : ℝ) : ℂ) := by
      rw [← map_natCast f D, ← map_mul, mul_inv_cancel_left₀ hDF]
      rfl
    rwa [h4] at h3
  · have h := (GlobalTheory.T.algebraicValuation_bound_of_mul_sq_integral l lam D (M₀ * M * D' * M₂ * M₁ * l ^ a0 𝔣 l) 0 hD (by simpa using (isIntegral_zero : IsIntegral ℤ (0 : ℂ)))).2
    rwa [show M₀ * M * D' * M₂ * M₁ * l ^ (padicValNat l D + a0 𝔣 l) =
      M₀ * M * D' * M₂ * M₁ * l ^ a0 𝔣 l * l ^ padicValNat l D by ring]

end GlobalTheory.RoadE
