module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionRationalOfRetractGaloisFixedPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativeSncOpenImmersion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPushoutLocalizedPresentationBaseChange
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.FrobeniusDecompositionOfLift

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogLiftPpZero
open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI

section LogMul

variable {K Kt : Type} [Field K] [CommRing Kt] (p : ℕ) [Fact p.Prime] [CharP K p] (π : Kt →+* K)
  {ι : Type} (F : ι → Kt →+* Kt) (s : Finset ι) (A : Subring K)

omit [Fact p.Prime] in
lemma logLift_pp_zero (hπ : IsFlatLift p π) : (p : Kt) * p = 0 := by
  rw [hπ.ann]; simp [map_natCast, CharP.cast_eq_zero]

omit [Fact p.Prime] in
lemma logLift_one : LogLift p π F s (A : Set K) 1 :=
  ⟨1, map_one π, fun i _ => ⟨0, by simp [A.zero_mem], by simp⟩⟩

omit [Fact p.Prime] in
lemma logLift_mul (hπ : IsFlatLift p π) {g g' : K} (hg : LogLift p π F s (A : Set K) g)
    (hg' : LogLift p π F s (A : Set K) g') : LogLift p π F s (A : Set K) (g * g') := by
  obtain ⟨z, hz, hF⟩ := hg
  obtain ⟨z', hz', hF'⟩ := hg'
  have hpp := logLift_pp_zero p π hπ
  refine ⟨z * z', by simp [hz, hz'], fun i hi => ?_⟩
  obtain ⟨w, hw, hFw⟩ := hF i hi
  obtain ⟨w', hw', hFw'⟩ := hF' i hi
  refine ⟨w + w', by rw [map_add (f := _)]; exact A.add_mem hw hw', ?_⟩
  rw [map_mul, hFw, hFw', mul_pow]
  linear_combination (z ^ p * z' ^ p * w * w') * hpp

omit [Fact p.Prime] in
lemma logLift_inv (hπ : IsFlatLift p π) {g : K} (hg0 : g ≠ 0) (hg : LogLift p π F s (A : Set K) g) :
    LogLift p π F s (A : Set K) g⁻¹ := by
  obtain ⟨z, hz, hF⟩ := hg
  have hpp := logLift_pp_zero p π hπ
  have hπp : π (p : Kt) = 0 := by simp [map_natCast, CharP.cast_eq_zero]
  obtain ⟨z', hz'⟩ := hπ.surj g⁻¹
  obtain ⟨e, he⟩ := (hπ.ker (z * z' - 1)).1 (by simp [hz, hz', hg0])
  set u := z' * (1 - p * e) with hu
  have hzu : z * u = 1 := by
    have : z * z' = 1 + p * e := by linear_combination he
    rw [hu, ← mul_assoc, this]; linear_combination (-(e * e)) * hpp
  have hπu : π u = g⁻¹ := by simp [hu, hz', hπp]
  clear_value u
  refine ⟨u, hπu, fun i hi => ?_⟩
  obtain ⟨w, hw, hFw⟩ := hF i hi
  refine ⟨-w, by rw [map_neg]; exact A.neg_mem hw, ?_⟩
  have h1 : F i z * F i u = 1 := by rw [← map_mul, hzu, map_one]
  have h2 : F i z * (u ^ p * (1 + p * -w)) = 1 := by
    rw [hFw]
    have : z ^ p * u ^ p = 1 := by rw [← mul_pow, hzu, one_pow]
    linear_combination (1 - (p:Kt) * w * ((p:Kt) * w)) * this - (w * w) * hpp
  linear_combination (u ^ p * (1 + p * -w)) * h1 - (F i u) * h2

omit [Fact p.Prime] in
lemma logLift_zpow (hπ : IsFlatLift p π) {g : K} (hg0 : g ≠ 0) (hg : LogLift p π F s (A : Set K) g) :
    ∀ n : ℤ, LogLift p π F s (A : Set K) (g ^ n) := by
  have hpow : ∀ {h : K}, LogLift p π F s (A : Set K) h → ∀ k : ℕ, LogLift p π F s (A : Set K) (h ^ k) := by
    intro h hh k
    induction k with
    | zero => simpa using logLift_one p π F s A
    | succ k ih => rw [pow_succ]; exact logLift_mul p π F s A hπ ih hh
  intro n
  cases n with
  | ofNat k => rw [Int.ofNat_eq_coe, zpow_natCast]; exact hpow hg k
  | negSucc k =>
    rw [zpow_negSucc, ← inv_pow]
    exact hpow (logLift_inv p π F s A hπ hg0 hg) (k + 1)

end LogMul

end GlobalTheory.DI
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatModPSquaredTorsion
open GlobalTheory GlobalTheory.DI

namespace GlobalTheory

theorem zmod_sq_dvd_of_mul_eq_zero (p : ℕ) [hp : Fact p.Prime] (a : ZMod (p ^ 2))
    (ha : (p : ZMod (p ^ 2)) * a = 0) : ∃ c : ZMod (p ^ 2), a = (p : ZMod (p ^ 2)) * c := by
  have h0 : ((p * a.val : ℕ) : ZMod (p ^ 2)) = 0 := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]; exact ha
  rw [ZMod.natCast_eq_zero_iff] at h0
  obtain ⟨k, hk⟩ := h0
  have h1 : a.val = p * k := by
    apply Nat.eq_of_mul_eq_mul_left hp.out.pos
    rw [hk]; ring
  refine ⟨(k : ZMod (p ^ 2)), ?_⟩
  rw [← ZMod.natCast_zmod_val a, h1, Nat.cast_mul]

theorem flat_zmod_sq_mul_p_eq_zero_iff : ∀ (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B]
    (φ : ZMod (p ^ 2) →+* B), φ.Flat → ∀ w : B, (p : B) * w = 0 ↔ ∃ v, w = p * v := by
  intro p hp B _ φ hφ w
  letI : Algebra (ZMod (p ^ 2)) B := φ.toAlgebra
  have hflat : Module.Flat (ZMod (p ^ 2)) B := hφ
  have hsmul : ∀ (r : ZMod (p ^ 2)) (b : B), r • b = φ r * b := fun r b => by
    rw [Algebra.smul_def]; rfl
  have hpB : φ (p : ZMod (p ^ 2)) = (p : B) := map_natCast φ p
  constructor
  · intro hw
    have hsum : ∑ i : Unit, (fun _ => (p : ZMod (p ^ 2))) i • (fun _ => w) i = 0 := by
      simp only [Finset.univ_unique, Finset.sum_singleton]
      rw [hsmul, hpB, hw]
    have htr := @Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (ZMod (p ^ 2)) B _ _ _ hflat Unit _ _ _ hsum
    obtain ⟨k, a, y, hy, ha⟩ := htr
    have ha' : ∀ j, (p : ZMod (p ^ 2)) * a () j = 0 := fun j => by
      simpa only [Finset.univ_unique, Finset.sum_singleton] using ha j
    choose c hc using fun j => zmod_sq_dvd_of_mul_eq_zero p (a () j) (ha' j)
    refine ⟨∑ j, φ (c j) * y j, ?_⟩
    have hw : w = ∑ j, a () j • y j := hy ()
    rw [hw, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hsmul, hc j, map_mul, hpB, mul_assoc]
  · rintro ⟨v, rfl⟩
    have h2 : (((p ^ 2 : ℕ) : ZMod (p ^ 2))) = 0 := ZMod.natCast_self _
    have : ((p ^ 2 : ℕ) : B) = 0 := by
      rw [← map_natCast φ, h2, map_zero]
    rw [← mul_assoc, ← Nat.cast_mul, ← pow_two, this, zero_mul]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AssociatedOfHeightOneAgree
namespace GlobalTheory

theorem exists_unit_eq_mul_of_height_one_avoiding (R : Type) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] {n : ℕ} (π : Fin n → R) (J : Finset (Fin n))
    (a b : R) (ha : a ≠ 0) (hb : b ≠ 0) (hπ : ∀ j ∈ J, IsUnit (π j) ∨ Prime (π j))
    (hdiv : ∀ j ∈ J, Prime (π j) → ¬ π j ∣ a ∧ ¬ π j ∣ b)
    (h : ∀ Q : Ideal R, Q.IsPrime → Q.height = 1 → (∀ j ∈ J, π j ∉ Q) →
      ∃ c d : R, c ∉ Q ∧ d ∉ Q ∧ a * d = b * c) :
    ∃ u : Rˣ, a = u * b := by

  have avoid : ∀ (Q : Ideal R) [Q.IsPrime], Q.height = 1 → ∀ x : R, x ≠ 0 → x ∈ Q →
      (∀ j ∈ J, Prime (π j) → ¬ π j ∣ x) → ∀ j ∈ J, π j ∉ Q := by
    intro Q hQ h1 x hx hxQ hnd j hj hjQ
    rcases hπ j hj with hu | hp
    · exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem Q hjQ hu)
    · have hmin := mem_minimalPrimes_span_singleton_of_height_eq_one h1 hp.ne_zero hjQ
      have hsp : (Ideal.span {π j}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
      have hle : Q ≤ Ideal.span {π j} :=
        hmin.2 ⟨hsp, le_refl _⟩ ((Ideal.span_singleton_le_iff_mem Q).mpr hjQ)
      exact hnd j hj hp (Ideal.mem_span_singleton.mp (hle hxQ))
  have hba : b ∣ a := dvd_of_forall_height_eq_one hb fun Q _ h1 hbQ => by
    obtain ⟨c, d, hc, hd, e⟩ :=
      h Q inferInstance h1 (avoid Q h1 b hb hbQ fun j hj hp => (hdiv j hj hp).2)
    exact ⟨d, hd, c, by rw [mul_comm d a, e]⟩
  have hab : a ∣ b := dvd_of_forall_height_eq_one ha fun Q _ h1 haQ => by
    obtain ⟨c, d, hc, hd, e⟩ :=
      h Q inferInstance h1 (avoid Q h1 a ha haQ fun j hj hp => (hdiv j hj hp).1)
    exact ⟨c, hc, d, by rw [mul_comm c b, ← e]⟩
  obtain ⟨u, hu⟩ := associated_of_dvd_dvd hba hab
  exact ⟨u, by rw [← hu, mul_comm]⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStripFinitelyManyPrimeFactors
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStripFinitelyManyPrimeFactors
namespace GlobalTheory

theorem strip_prime_factors (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] {n : ℕ}
    (π : Fin n → R) (J : Finset (Fin n)) (x : R) (hx : x ≠ 0) :
    ∃ (m : Fin n → ℕ) (y : R), x = y * ∏ j ∈ J, π j ^ m j ∧
      ∀ j ∈ J, Prime (π j) → ¬ π j ∣ y := by
  induction J using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, x, by simp, by simp⟩
  | @insert j J hj ih =>
    obtain ⟨m, y, hxy, hy⟩ := ih
    have hy0 : y ≠ 0 := by
      rintro rfl
      exact hx (by simpa using hxy)
    by_cases hp : Prime (π j)
    · obtain ⟨y', hy', hnd⟩ :=
        (FiniteMultiplicity.of_not_isUnit hp.not_unit hy0).exists_eq_pow_mul_and_not_dvd
      refine ⟨Function.update m j (multiplicity (π j) y), y', ?_, ?_⟩
      · rw [Finset.prod_insert hj, Function.update_self]
        have hJ : ∏ i ∈ J, π i ^ Function.update m j (multiplicity (π j) y) i
            = ∏ i ∈ J, π i ^ m i := by
          refine Finset.prod_congr rfl fun i hi => ?_
          rw [Function.update_of_ne (by rintro rfl; exact hj hi)]
        rw [hJ, hxy]
        conv_lhs => rw [hy']
        ring
      · intro i hi hpi hdvd
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact hnd hdvd
        · exact hy i hi hpi (hdvd.trans (Dvd.intro_left _ hy'.symm))
    · refine ⟨Function.update m j 0, y, ?_, ?_⟩
      · rw [Finset.prod_insert hj, Function.update_self, pow_zero, one_mul]
        rw [hxy]
        congr 1
        refine Finset.prod_congr rfl fun i hi => ?_
        rw [Function.update_of_ne (by rintro rfl; exact hj hi)]
      · intro i hi hpi hdvd
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact hp hpi
        · exact hy i hi hpi hdvd

theorem strip_prime_factors_target : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] {n : ℕ} (π : Fin n → R) (J : Finset (Fin n)) (x : R), x ≠ 0 → ∃ (m : Fin n → ℕ) (y : R), x = y * ∏ j ∈ J, π j ^ m j ∧ ∀ j ∈ J, Prime (π j) → ¬ π j ∣ y :=
  fun R _ _ _ _ π J x hx => strip_prime_factors R π J x hx

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStripFinitelyManyPrimeFactorsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_strip_finitely_many_prime_factors : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] {n : ℕ} (π : Fin n → R) (J : Finset (Fin n)) (x : R), x ≠ 0 → ∃ (m : Fin n → ℕ) (y : R), x = y * ∏ j ∈ J, π j ^ m j ∧ ∀ j ∈ J, Prime (π j) → ¬ π j ∣ y := by
  first | exact @GlobalTheory.strip_prime_factors_target | exact GlobalTheory.strip_prime_factors_target | (intros; apply GlobalTheory.strip_prime_factors_target <;> assumption)
end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ModPSquaredStalkSurjective
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.mod_p_squared_stalk_surjective : ∀ (p : ℕ) [Fact p.Prime] (Y X : Scheme.{0}) (g : Y ⟶ Sp (ZMod (p ^ 2))) (f : X ⟶ Sp (ZMod p)) (π : X ⟶ Y), IsPullback π f g (spMap (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p))) → ∀ y : X, Function.Surjective (π.stalkMap y).hom ∧ ∀ z, (π.stalkMap y).hom z = 0 ↔ ∃ w, z = p * w := by
  first | exact @_root_.GlobalTheory.DI.StalkKer.stalkMap_surjective_ker | exact _root_.GlobalTheory.DI.StalkKer.stalkMap_surjective_ker | (intros; apply _root_.GlobalTheory.DI.StalkKer.stalkMap_surjective_ker <;> assumption)
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.EtaleCoordinatesLogChart
section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.RootOfMonomialQuotientIntegral
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

theorem _root_.GlobalTheory.T.root_of_monomial_quotient_integral : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [IsDomain A] [Algebra (ZMod p) A] {n : ℕ} (t : Fin n → A), (MvPolynomial.aeval (R := ZMod p) t).toRingHom.Etale → ∀ (P : Ideal A) [P.IsPrime] (L : Type) [Field L] [Algebra A L] [IsFractionRing A L] (S : Finset (Fin n)) (g : L) (m : ℕ), 0 < m → (∃ a b : A, b ∉ P ∧ g ^ m / algebraMap A L (∏ j ∈ S, t j) * algebraMap A L b = algebraMap A L a) → ∃ a b : A, b ∉ P ∧ g / algebraMap A L (∏ j ∈ S, t j) * algebraMap A L b = algebraMap A L a := by
  first | exact @_root_.GlobalTheory.EtRoot.div_prod_coords_mem_of_pow | exact _root_.GlobalTheory.EtRoot.div_prod_coords_mem_of_pow | (intros; apply _root_.GlobalTheory.EtRoot.div_prod_coords_mem_of_pow <;> assumption)
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.FractionFieldCoordinatesDlog
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

theorem _root_.GlobalTheory.T.fraction_field_coordinates_dlog : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [IsDomain A] [Algebra (ZMod p) A] {n : ℕ} (t : Fin n → A), (MvPolynomial.aeval (R := ZMod p) t).toRingHom.Etale → ∀ (L : Type) [Field L] [Algebra A L] [IsFractionRing A L] (ht : ∀ j, algebraMap A L (t j) ≠ 0), IsCoord (fun j => Units.mk0 (algebraMap A L (t j)) (ht j)) ∧ ∀ f : A, ∃ c : Fin n → A, KaehlerDifferential.D ℤ L (algebraMap A L f) = ∑ j, algebraMap A L (c j) • KaehlerDifferential.D ℤ L (algebraMap A L (t j)) := by
  first | exact @_root_.GlobalTheory.EtCoordBasis.etale_coords_basis | exact _root_.GlobalTheory.EtCoordBasis.etale_coords_basis | (intros; apply _root_.GlobalTheory.EtCoordBasis.etale_coords_basis <;> assumption)
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.UnitOfHeightOnePrimes
section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.EtaleCoordinateQuotientRegular
theorem _root_.GlobalTheory.T.etale_coordinate_quotient_regular : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [Algebra (ZMod p) A] {n : ℕ} (t : Fin n → A), (MvPolynomial.aeval (R := ZMod p) t).toRingHom.Etale → ∀ j : Fin n, IsRegularRing (A ⧸ Ideal.span {t j}) := by
  first | exact @_root_.GlobalTheory.isRegularRing_quotient_etaleCoordinate | exact _root_.GlobalTheory.isRegularRing_quotient_etaleCoordinate | (intros; apply _root_.GlobalTheory.isRegularRing_quotient_etaleCoordinate <;> assumption)
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.RegularQuotientPrimeElement
theorem _root_.GlobalTheory.T.regular_quotient_prime_element : ∀ (A : Type) [CommRing A] [IsDomain A] (P : Ideal A) [P.IsPrime] (x : A), x ≠ 0 → x ∈ P → IsRegularRing (A ⧸ Ideal.span {x}) → Prime (algebraMap A (Localization.AtPrime P) x) := by
  first | exact @_root_.GlobalTheory.prime_algebraMap_localization_of_isRegularRing_quotient | exact _root_.GlobalTheory.prime_algebraMap_localization_of_isRegularRing_quotient | (intros; apply _root_.GlobalTheory.prime_algebraMap_localization_of_isRegularRing_quotient <;> assumption)
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.AssociatedOfHeightOneAgree
theorem _root_.GlobalTheory.T.associated_of_height_one_agree : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] {n : ℕ} (π : Fin n → R) (J : Finset (Fin n)) (a b : R), a ≠ 0 → b ≠ 0 → (∀ j ∈ J, IsUnit (π j) ∨ Prime (π j)) → (∀ j ∈ J, Prime (π j) → ¬ π j ∣ a ∧ ¬ π j ∣ b) → (∀ Q : Ideal R, Q.IsPrime → Q.height = 1 → (∀ j ∈ J, π j ∉ Q) → ∃ c d : R, c ∉ Q ∧ d ∉ Q ∧ a * d = b * c) → ∃ u : Rˣ, a = u * b := by
  first | exact @_root_.GlobalTheory.exists_unit_eq_mul_of_height_one_avoiding | exact _root_.GlobalTheory.exists_unit_eq_mul_of_height_one_avoiding | (intros; apply _root_.GlobalTheory.exists_unit_eq_mul_of_height_one_avoiding <;> assumption)
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.UnitOfHeightOnePrimes
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

namespace GlobalTheory.EtUnit

theorem unit_mul_monomial_of_forall_height_one (R K : Type) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K]
    {n : ℕ} (π : Fin n → R) (J : Finset (Fin n)) (hπ : ∀ j ∈ J, IsUnit (π j) ∨ Prime (π j))
    (x : K) (hx : x ≠ 0)
    (h : ∀ Q : Ideal R, Q.IsPrime → Q.height = 1 → (∀ j ∈ J, π j ∉ Q) →
      ∃ c d : R, c ∉ Q ∧ d ∉ Q ∧ x * algebraMap R K d = algebraMap R K c) :
    ∃ (u : Rˣ) (m : Fin n → ℤ), x = algebraMap R K u * ∏ j ∈ J, (algebraMap R K (π j)) ^ m j := by
  obtain ⟨a0, b0, hb0, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hb0' : b0 ≠ 0 := nonZeroDivisors.ne_zero hb0
  have hb0K : algebraMap R K b0 ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact hb0'
  have ha0 : a0 ≠ 0 := by rintro rfl; simp at hx
  obtain ⟨α, a, ha, hna⟩ := GlobalTheory.T.exists_strip_finitely_many_prime_factors R π J a0 ha0
  obtain ⟨β, b, hb, hnb⟩ := GlobalTheory.T.exists_strip_finitely_many_prime_factors R π J b0 hb0'
  have hπ0 : ∀ j ∈ J, π j ≠ 0 := fun j hj =>
    (hπ j hj).elim (fun hu => hu.ne_zero) (fun hp => hp.ne_zero)
  have han : a ≠ 0 := by rintro rfl; rw [zero_mul] at ha; exact ha0 ha
  have hbn : b ≠ 0 := by rintro rfl; rw [zero_mul] at hb; exact hb0' hb
  have hprodQ : ∀ (Q : Ideal R), Q.IsPrime → (∀ j ∈ J, π j ∉ Q) →
      ∀ e : Fin n → ℕ, ∏ j ∈ J, π j ^ e j ∉ Q := by
    intro Q hQ hQJ e hmem
    obtain ⟨j, hj, hjm⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    exact hQJ j hj (hQ.mem_of_pow_mem _ hjm)
  obtain ⟨u, hu⟩ := GlobalTheory.T.associated_of_height_one_agree R π J a b han hbn hπ
    (fun j hj hp => ⟨hna j hj hp, hnb j hj hp⟩) (fun Q hQ h1 hQJ => by
      obtain ⟨c, d, hc, hd, hcd⟩ := h Q hQ h1 hQJ
      refine ⟨c * ∏ j ∈ J, π j ^ β j, d * ∏ j ∈ J, π j ^ α j,
        hQ.mul_notMem hc (hprodQ Q hQ hQJ β), hQ.mul_notMem hd (hprodQ Q hQ hQJ α), ?_⟩
      have e1 : algebraMap R K a0 * algebraMap R K d = algebraMap R K b0 * algebraMap R K c := by
        rw [← hcd]; field_simp
      have e2 : a0 * d = b0 * c := IsFractionRing.injective R K (by rw [map_mul, map_mul, e1])
      rw [ha, hb] at e2
      linear_combination e2)
  refine ⟨u, fun j => (α j : ℤ) - β j, ?_⟩
  have hK : ∀ j ∈ J, algebraMap R K (π j) ≠ 0 := fun j hj => by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact hπ0 j hj
  have hprodK : ∏ j ∈ J, algebraMap R K (π j) ^ ((α j : ℤ) - β j) =
      (∏ j ∈ J, algebraMap R K (π j) ^ α j) / ∏ j ∈ J, algebraMap R K (π j) ^ β j := by
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [zpow_sub₀ (hK j hj), zpow_natCast, zpow_natCast]
  have hβK : ∏ j ∈ J, algebraMap R K (π j) ^ β j ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j hj => pow_ne_zero _ (hK j hj)
  have hbK : algebraMap R K b ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact hbn
  rw [hprodK, ha, hb, hu]
  simp only [map_mul, map_prod, map_pow]
  field_simp

theorem unit_mul_monomial_iff : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [IsDomain A] [Algebra (ZMod p) A] {n : ℕ} (t : Fin n → A), (MvPolynomial.aeval (R := ZMod p) t).toRingHom.Etale → ∀ (P : Ideal A) [P.IsPrime] (L : Type) [Field L] [Algebra A L] [IsFractionRing A L] (J : Finset (Fin n)) (ht : ∀ j, algebraMap A L (t j) ≠ 0) (g : Lˣ), (∀ Q : Ideal A, Q.IsPrime → Q ≤ P → (∀ j ∈ J, t j ∉ Q) → ∃ a b : A, a ∉ Q ∧ b ∉ Q ∧ (g : L) * algebraMap A L b = algebraMap A L a) ↔ ∃ (u : Lˣ) (m : Fin n → ℤ), (∃ a b : A, a ∉ P ∧ b ∉ P ∧ (u : L) * algebraMap A L b = algebraMap A L a) ∧ g = u * ∏ j ∈ J, Units.mk0 _ (ht j) ^ m j := by
  intro p _ A _ _ _ n t het P _ L _ _ _ J ht g
  constructor
  · intro hL
    letI : Algebra (MvPolynomial (Fin n) (ZMod p)) A :=
      (MvPolynomial.aeval (R := ZMod p) t).toRingHom.toAlgebra
    haveI : Algebra.Etale (MvPolynomial (Fin n) (ZMod p)) A := het
    haveI : IsRegularRing A := GlobalTheory.isRegularRing_of_etale (MvPolynomial (Fin n) (ZMod p)) A
    haveI : IsRegularLocalRing (Localization.AtPrime P) :=
      IsRegularRing.isRegularLocalRing_localization P
    obtain ⟨hRd, hRi⟩ :=
      GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing (Localization.AtPrime P)
    haveI : IsNoetherianRing (Localization.AtPrime P) :=
      IsLocalization.isNoetherianRing P.primeCompl _ inferInstance
    have hunits : ∀ y : P.primeCompl, IsUnit (algebraMap A L y) := fun y => by
      refine IsUnit.mk0 _ ?_
      rw [Ne, IsFractionRing.to_map_eq_zero_iff]
      rintro h0
      exact y.2 (h0 ▸ P.zero_mem)
    letI : Algebra (Localization.AtPrime P) L := (IsLocalization.lift hunits).toAlgebra
    haveI : IsScalarTower A (Localization.AtPrime P) L :=
      IsScalarTower.of_algebraMap_eq (fun a => (IsLocalization.lift_eq hunits a).symm)
    haveI : IsFractionRing (Localization.AtPrime P) L :=
      IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P.primeCompl _ L
    have hprime : ∀ j ∈ J, IsUnit (algebraMap A (Localization.AtPrime P) (t j)) ∨
        Prime (algebraMap A (Localization.AtPrime P) (t j)) := by
      intro j hj
      by_cases hjP : t j ∈ P
      · right
        refine GlobalTheory.T.regular_quotient_prime_element A P (t j) (fun h0 => ht j (by rw [h0, map_zero])) hjP
          (GlobalTheory.T.etale_coordinate_quotient_regular p A t het j)
      · left
        exact IsLocalization.map_units (Localization.AtPrime P) (⟨t j, hjP⟩ : P.primeCompl)
    obtain ⟨u, m, hum⟩ := unit_mul_monomial_of_forall_height_one (Localization.AtPrime P) L
      (fun j => algebraMap A (Localization.AtPrime P) (t j)) J hprime (g : L) g.ne_zero (by
        intro Q hQ _ hQJ
        have hQ'P : Q.comap (algebraMap A (Localization.AtPrime P)) ≤ P := by
          intro x hx
          by_contra hxP
          exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ hx
            (IsLocalization.map_units (Localization.AtPrime P) (⟨x, hxP⟩ : P.primeCompl)))
        obtain ⟨a, b, ha, hb, hab⟩ := hL (Q.comap (algebraMap A (Localization.AtPrime P)))
          (Ideal.comap_isPrime _ Q) hQ'P (fun j hj hjQ => hQJ j hj hjQ)
        refine ⟨algebraMap A _ a, algebraMap A _ b, ha, hb, ?_⟩
        rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
        exact hab)
    obtain ⟨⟨a, s⟩, has⟩ := IsLocalization.mk'_surjective P.primeCompl (u : Localization.AtPrime P)
    change IsLocalization.mk' (Localization.AtPrime P) a s = _ at has
    have haP : a ∈ P.primeCompl := by
      rw [← IsLocalization.AtPrime.isUnit_mk'_iff (Localization.AtPrime P) P a s, has]
      exact u.isUnit
    refine ⟨Units.map (algebraMap (Localization.AtPrime P) L : Localization.AtPrime P →* L) u, m,
      ⟨a, s, haP, s.2, ?_⟩, ?_⟩
    · rw [Units.coe_map, MonoidHom.coe_coe, ← has, IsScalarTower.algebraMap_apply A
        (Localization.AtPrime P) L s, IsScalarTower.algebraMap_apply A (Localization.AtPrime P) L a,
        ← map_mul, IsLocalization.mk'_spec]
    · ext
      rw [hum, Units.val_mul, Units.coe_map, MonoidHom.coe_coe, Units.coe_prod]
      congr 1
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [Units.val_zpow_eq_zpow_val, Units.val_mk0, ← IsScalarTower.algebraMap_apply]
  · rintro ⟨u, m, ⟨a, b, ha, hb, hab⟩, rfl⟩ Q hQ hQP hQJ
    have hK : ∀ j, algebraMap A L (t j) ≠ 0 := ht
    have hprodQ : ∀ e : Fin n → ℕ, ∏ j ∈ J, t j ^ e j ∉ Q := by
      intro e hmem
      obtain ⟨j, hj, hjm⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
      exact hQJ j hj (hQ.mem_of_pow_mem _ hjm)
    refine ⟨a * ∏ j ∈ J, t j ^ (m j).toNat, b * ∏ j ∈ J, t j ^ (-m j).toNat,
      hQ.mul_notMem (fun h => ha (hQP h)) (hprodQ _),
      hQ.mul_notMem (fun h => hb (hQP h)) (hprodQ _), ?_⟩
    have key : ∀ j, algebraMap A L (t j) ^ m j * algebraMap A L (t j) ^ (-m j).toNat =
        algebraMap A L (t j) ^ (m j).toNat := by
      intro j
      have e : m j = ((m j).toNat : ℤ) - ((-m j).toNat : ℤ) := (Int.toNat_sub_toNat_neg _).symm
      calc algebraMap A L (t j) ^ m j * algebraMap A L (t j) ^ (-m j).toNat
          = algebraMap A L (t j) ^ (((m j).toNat : ℤ) - ((-m j).toNat : ℤ)) *
            algebraMap A L (t j) ^ (-m j).toNat := by rw [← e]
        _ = _ := by
          rw [zpow_sub₀ (hK j), zpow_natCast, zpow_natCast,
            div_mul_cancel₀ _ (pow_ne_zero _ (hK j))]
    rw [Units.val_mul, Units.coe_prod, map_mul, map_mul, map_prod, map_prod, ← hab]
    simp only [Units.val_zpow_eq_zpow_val, Units.val_mk0, map_pow]
    rw [show (u : L) * (∏ j ∈ J, algebraMap A L (t j) ^ m j) *
        (algebraMap A L b * ∏ j ∈ J, algebraMap A L (t j) ^ (-m j).toNat) =
        (u : L) * algebraMap A L b * ∏ j ∈ J, (algebraMap A L (t j) ^ m j *
          algebraMap A L (t j) ^ (-m j).toNat) by rw [Finset.prod_mul_distrib]; ring]
    simp only [key]

end GlobalTheory.EtUnit
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.UnitOfHeightOnePrimesStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

theorem _root_.GlobalTheory.T.unit_of_height_one_primes : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [IsDomain A] [Algebra (ZMod p) A] {n : ℕ} (t : Fin n → A), (MvPolynomial.aeval (R := ZMod p) t).toRingHom.Etale → ∀ (P : Ideal A) [P.IsPrime] (L : Type) [Field L] [Algebra A L] [IsFractionRing A L] (J : Finset (Fin n)) (ht : ∀ j, algebraMap A L (t j) ≠ 0) (g : Lˣ), (∀ Q : Ideal A, Q.IsPrime → Q ≤ P → (∀ j ∈ J, t j ∉ Q) → ∃ a b : A, a ∉ Q ∧ b ∉ Q ∧ (g : L) * algebraMap A L b = algebraMap A L a) ↔ ∃ (u : Lˣ) (m : Fin n → ℤ), (∃ a b : A, a ∉ P ∧ b ∉ P ∧ (u : L) * algebraMap A L b = algebraMap A L a) ∧ g = u * ∏ j ∈ J, Units.mk0 _ (ht j) ^ m j := by
  first | exact @_root_.GlobalTheory.EtUnit.unit_mul_monomial_iff | exact _root_.GlobalTheory.EtUnit.unit_mul_monomial_iff | (intros; apply _root_.GlobalTheory.EtUnit.unit_mul_monomial_iff <;> assumption)
end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.EtaleCoordinatesLogChart
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EtLog

variable {X : Scheme.{0}} [IsIntegral X] {U : X.Opens} (hU : IsAffineOpen U)


include hU in
theorem unitAt_fnOf_iff_not_mem {y : X} (hy : y ∈ U) (s : Γ(X, U)) :
    UnitAt y (fnOf U (gen_mem hy) s) ↔ s ∉ (hU.primeIdealOf ⟨y, hy⟩).asIdeal := by
  rw [unitAt_fnOf_iff hy, GlobalTheory.DetHT.RegLoc.mem_basicOpen_iff hU hy]


include hU in
theorem regAt_iff_frac {y : X} (hy : y ∈ U) (g : X.functionField) :
    RegAt y g ↔ ∃ a b : Γ(X, U), b ∉ (hU.primeIdealOf ⟨y, hy⟩).asIdeal ∧
      g * fnOf U (gen_mem hy) b = fnOf U (gen_mem hy) a := by
  constructor
  · intro hg
    exact GlobalTheory.FieldPair.regAt_exists_fraction hU hy hg
  · rintro ⟨a, b, hb, e⟩
    have hu := GlobalTheory.FieldPair.unitAt_fnOf_of_not_mem hU hy hb
    have eg : g = fnOf U (gen_mem hy) a * (fnOf U (gen_mem hy) b)⁻¹ := by
      rw [← e, mul_inv_cancel_right₀ hu.ne_zero]
    rw [eg]
    exact (regAt_fnOf hy _ a).mul hu.inv.regAt


include hU in
theorem unitAt_iff_frac {y : X} (hy : y ∈ U) (g : X.functionField) :
    UnitAt y g ↔ ∃ a b : Γ(X, U), a ∉ (hU.primeIdealOf ⟨y, hy⟩).asIdeal ∧
      b ∉ (hU.primeIdealOf ⟨y, hy⟩).asIdeal ∧ g * fnOf U (gen_mem hy) b = fnOf U (gen_mem hy) a := by
  constructor
  · intro hg
    obtain ⟨a, b, hb, e⟩ := (regAt_iff_frac hU hy g).1 hg.regAt
    refine ⟨a, b, ?_, hb, e⟩
    rw [← unitAt_fnOf_iff_not_mem hU hy, ← e]
    exact hg.mul (GlobalTheory.FieldPair.unitAt_fnOf_of_not_mem hU hy hb)
  · rintro ⟨a, b, ha, hb, e⟩
    have hu := GlobalTheory.FieldPair.unitAt_fnOf_of_not_mem hU hy hb
    have hua := GlobalTheory.FieldPair.unitAt_fnOf_of_not_mem hU hy ha
    have eg : g = fnOf U (gen_mem hy) a * (fnOf U (gen_mem hy) b)⁻¹ := by
      rw [← e, mul_inv_cancel_right₀ hu.ne_zero]
    rw [eg]
    exact hua.mul hu.inv


include hU in
theorem primeIdealOf_le_of_specializes {y z : X} (hy : y ∈ U) (hz : z ∈ U) (hzy : z ⤳ y) :
    (hU.primeIdealOf ⟨z, hz⟩).asIdeal ≤ (hU.primeIdealOf ⟨y, hy⟩).asIdeal := by
  intro s hs
  by_contra hs'
  rw [← GlobalTheory.DetHT.RegLoc.mem_basicOpen_iff hU hy] at hs'
  exact (GlobalTheory.DetHT.RegLoc.mem_basicOpen_iff hU hz s).1 (hzy.mem_open (X.basicOpen s).isOpen hs') hs


include hU in
theorem exists_specializes_of_le {y : X} (hy : y ∈ U) (Q : Ideal Γ(X, U)) (hQ : Q.IsPrime)
    (hQP : Q ≤ (hU.primeIdealOf ⟨y, hy⟩).asIdeal) :
    ∃ (z : X) (hz : z ∈ U), z ⤳ y ∧ (hU.primeIdealOf ⟨z, hz⟩).asIdeal = Q := by
  refine ⟨(GlobalTheory.QCoh.pointOfPrime hU ⟨Q, hQ⟩ : X), (GlobalTheory.QCoh.pointOfPrime hU ⟨Q, hQ⟩).2, ?_, ?_⟩
  · have h1 := ((PrimeSpectrum.le_iff_specializes ⟨Q, hQ⟩ (hU.primeIdealOf ⟨y, hy⟩)).mp hQP).map
      hU.fromSpec.continuous
    rw [hU.fromSpec_primeIdealOf ⟨y, hy⟩] at h1
    exact h1
  · rw [GlobalTheory.QCoh.primeIdealOf_pointOfPrime]

theorem isLogChart_of_isEtCoord : ∀ (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) [IsIntegral X]
    (f : X ⟶ Sp (ZMod p)) (U : X.Opens) (h : genericPoint X ∈ U) {n : ℕ} (t : Fin n → Γ(X, U))
    (x : Fin n → X.functionFieldˣ) (J : Finset (Fin n)) (Z : Set X), IsAffineOpen U →
    IsEtCoord f U t → (∀ j, (x j : X.functionField) = fnOf U h (t j)) →
    (∀ y ∈ U, y ∈ Z ↔ ∃ j ∈ J, ¬ UnitAt y (x j : X.functionField)) → IsLogChart Z U x J := by
  intro p _ X _ f U h n t x J Z hU hEt hx hZ
  haveI : Nonempty U := ⟨⟨_, h⟩⟩
  letI : Algebra (ZMod p) Γ(X, U) := (cstOn f U).toAlgebra
  haveI : IsFractionRing Γ(X, U) X.functionField := functionField_isFractionRing_of_isAffineOpen X U hU
  have hEt' : (MvPolynomial.aeval (R := ZMod p) t).toRingHom.Etale := hEt
  have hA : ∀ s : Γ(X, U), algebraMap Γ(X, U) X.functionField s = fnOf U h s := fun _ => rfl
  have ht : ∀ j, algebraMap Γ(X, U) X.functionField (t j) ≠ 0 := fun j => by
    rw [hA, ← hx j]; exact (x j).ne_zero
  have hxt : x = fun j => Units.mk0 _ (ht j) := funext fun j => Units.ext (hx j)
  have hB := GlobalTheory.T.fraction_field_coordinates_dlog p Γ(X, U) t hEt' X.functionField ht
  have hprod : ∀ S : Finset (Fin n),
      algebraMap Γ(X, U) X.functionField (∏ j ∈ S, t j) = ∏ j ∈ S, (x j : X.functionField) :=
    fun S => by rw [map_prod]; exact Finset.prod_congr rfl fun j _ => (hx j).symm
  refine ⟨fun y hy => ⟨fun i => ?_, ?_, ?_, ?_⟩, fun y hy g => ?_⟩
  · rw [hx i]; exact regAt_fnOf hy h (t i)
  · rw [hxt]; exact hB.1
  · intro g hg
    obtain ⟨a, b, hb, e⟩ := (regAt_iff_frac hU hy g).1 (mem_locRing.1 hg)
    obtain ⟨ca, hca⟩ := hB.2 a
    obtain ⟨cb, hcb⟩ := hB.2 b
    have hu := GlobalTheory.FieldPair.unitAt_fnOf_of_not_mem hU hy hb
    refine ⟨fun i => (fnOf U h b)⁻¹ * (fnOf U h (ca i) - g * fnOf U h (cb i)), fun i => ?_, ?_⟩
    · exact mul_mem (mem_locRing.2 hu.inv.regAt) (sub_mem (mem_locRing.2 (regAt_fnOf hy h _))
        (mul_mem hg (mem_locRing.2 (regAt_fnOf hy h _))))
    · have hB0 : fnOf U h b ≠ 0 := hu.ne_zero
      have key : dK g = (fnOf U h b)⁻¹ • (dK (fnOf U h a) - g • dK (fnOf U h b)) := by
        have e' : g * fnOf U h b = fnOf U h a := e
        rw [← e']
        simp only [dK, Derivation.leibniz]
        rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hB0, one_smul]
      simp only [hA] at hca hcb
      rw [key]
      simp only [dK] at hca hcb ⊢
      rw [hca, hcb, Finset.smul_sum, ← Finset.sum_sub_distrib, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hx i, smul_smul, ← sub_smul, smul_smul, mul_comm g]
  · intro S g m hm hg
    obtain ⟨a, b, hb, e⟩ := GlobalTheory.T.root_of_monomial_quotient_integral p Γ(X, U) t hEt' (hU.primeIdealOf ⟨y, hy⟩).asIdeal
      X.functionField S g m hm (by
        obtain ⟨a, b, hb, e⟩ := (regAt_iff_frac hU hy _).1 (mem_locRing.1 hg)
        exact ⟨a, b, hb, by rw [hprod]; exact e⟩)
    exact mem_locRing.2 ((regAt_iff_frac hU hy _).2 ⟨a, b, hb, by rw [← hprod]; exact e⟩)
  · have hZc : ∀ z (hz : z ∈ U), z ∉ Z ↔ ∀ j ∈ J, t j ∉ (hU.primeIdealOf ⟨z, hz⟩).asIdeal := by
      intro z hz
      rw [hZ z hz]
      simp only [not_exists, not_and, not_not]
      refine forall₂_congr fun j _ => ?_
      rw [hx j]
      exact unitAt_fnOf_iff_not_mem hU hz (t j)
    have hU' := GlobalTheory.T.unit_of_height_one_primes p Γ(X, U) t hEt' (hU.primeIdealOf ⟨y, hy⟩).asIdeal X.functionField J ht g
    refine Iff.trans ?_ (hU'.trans ?_)
    · constructor
      · intro hL Q hQ hQP hJ
        obtain ⟨z, hz, hzy, rfl⟩ := exists_specializes_of_le hU hy Q hQ hQP
        exact (unitAt_iff_frac hU hz g).1 (hL z hzy ((hZc z hz).2 hJ))
      · intro hL z hzy hzZ
        have hz : z ∈ U := hzy.mem_open U.isOpen hy
        exact (unitAt_iff_frac hU hz g).2 (hL _ inferInstance
          (primeIdealOf_le_of_specializes hU hy hz hzy) ((hZc z hz).1 hzZ))
    · subst hxt
      exact exists_congr fun u => exists_congr fun m => and_congr_left' (unitAt_iff_frac hU hy u).symm

end GlobalTheory.EtLog
end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.EtaleCoordinatesLogChartStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

theorem _root_.GlobalTheory.T.etale_coordinates_log_chart : ∀ (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Sp (ZMod p)) (U : X.Opens) (h : genericPoint X ∈ U) {n : ℕ} (t : Fin n → Γ(X, U)) (x : Fin n → X.functionFieldˣ) (J : Finset (Fin n)) (Z : Set X), IsAffineOpen U → IsEtCoord f U t → (∀ j, (x j : X.functionField) = fnOf U h (t j)) → (∀ y ∈ U, y ∈ Z ↔ ∃ j ∈ J, ¬ UnitAt y (x j : X.functionField)) → IsLogChart Z U x J := by
  first | exact @_root_.GlobalTheory.EtLog.isLogChart_of_isEtCoord | exact _root_.GlobalTheory.EtLog.isLogChart_of_isEtCoord | (intros; apply _root_.GlobalTheory.EtLog.isLogChart_of_isEtCoord <;> assumption)
end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.LiftedStalkMapGermAppLE
section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.EtaleCoordinatesFlatLift
section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.EtaleCoordinatesStalkFlat
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.etale_coordinates_stalk_flat : ∀ {R : Type} [CommRing R] {Y : Scheme.{0}} (g : Y ⟶ Sp R) (U : Y.Opens) {n : ℕ} (t : Fin n → Γ(Y, U)), IsAffineOpen U → IsEtCoord g U t → ∀ (y : Y) (hy : y ∈ U), ((Y.presheaf.germ U y hy).hom.comp (cstOn g U)).Flat := by
  first | exact @_root_.GlobalTheory.LogPair.flat_germ_comp_cstOn_of_isEtCoord | exact _root_.GlobalTheory.LogPair.flat_germ_comp_cstOn_of_isEtCoord | (intros; apply _root_.GlobalTheory.LogPair.flat_germ_comp_cstOn_of_isEtCoord <;> assumption)
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.FlatModPSquaredTorsion
open GlobalTheory GlobalTheory.DI
theorem _root_.GlobalTheory.T.flat_mod_p_squared_torsion : ∀ (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (φ : ZMod (p ^ 2) →+* B), φ.Flat → ∀ w : B, (p : B) * w = 0 ↔ ∃ v, w = p * v := by
  first | exact @_root_.GlobalTheory.flat_zmod_sq_mul_p_eq_zero_iff | exact _root_.GlobalTheory.flat_zmod_sq_mul_p_eq_zero_iff | (intros; apply _root_.GlobalTheory.flat_zmod_sq_mul_p_eq_zero_iff <;> assumption)
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.EtaleCoordinatesFlatLift
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.DI

theorem isFlatLift_stalkMap_of_isEtCoord : ∀ (p : ℕ) [Fact p.Prime] (Y X : Scheme.{0}) (g : Y ⟶ Sp (ZMod (p ^ 2))) (f : X ⟶ Sp (ZMod p)) (π : X ⟶ Y), IsPullback π f g (spMap (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p))) → ∀ (U : Y.Opens) {n : ℕ} (t : Fin n → Γ(Y, U)), IsAffineOpen U → IsEtCoord g U t → ∀ y : X, π y ∈ U → IsFlatLift p (π.stalkMap y).hom := by
  intro p _ Y X g f π hP U n t hU ht y hy
  obtain ⟨hs, hk⟩ := GlobalTheory.T.mod_p_squared_stalk_surjective p Y X g f π hP y
  have hfl := GlobalTheory.T.etale_coordinates_stalk_flat g U t hU ht (π y) hy
  refine ⟨hs, hk, fun w => ?_⟩
  rw [GlobalTheory.T.flat_mod_p_squared_torsion p _ hfl w, hk w]

end GlobalTheory.DI
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.EtaleCoordinatesFlatLiftStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.etale_coordinates_flat_lift : ∀ (p : ℕ) [Fact p.Prime] (Y X : Scheme.{0}) (g : Y ⟶ Sp (ZMod (p ^ 2))) (f : X ⟶ Sp (ZMod p)) (π : X ⟶ Y), IsPullback π f g (spMap (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p))) → ∀ (U : Y.Opens) {n : ℕ} (t : Fin n → Γ(Y, U)), IsAffineOpen U → IsEtCoord g U t → ∀ y : X, π y ∈ U → IsFlatLift p (π.stalkMap y).hom := by
  first | exact @_root_.GlobalTheory.DI.isFlatLift_stalkMap_of_isEtCoord | exact _root_.GlobalTheory.DI.isFlatLift_stalkMap_of_isEtCoord | (intros; apply _root_.GlobalTheory.DI.isFlatLift_stalkMap_of_isEtCoord <;> assumption)
end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.LocalRingImageStalkMap
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.local_ring_image_stalk_map : ∀ {X Y : Scheme.{0}} [IsIntegral X] (π : X ⟶ Y) (y : X) (h : π (genericPoint X) ⤳ π y), Function.Surjective (π.stalkMap y).hom → ∀ c : X.functionField, c ∈ locRing y ↔ ∃ z ∈ stalkIm h, (π.stalkMap (genericPoint X)).hom z = c := by
  first | exact @_root_.GlobalTheory.DI.mem_locRing_iff_exists_stalkIm | exact _root_.GlobalTheory.DI.mem_locRing_iff_exists_stalkIm | (intros; apply _root_.GlobalTheory.DI.mem_locRing_iff_exists_stalkIm <;> assumption)
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsFrobeniusLiftStalk
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.exists_frobenius_lift_stalk : ∀ (p : ℕ) [Fact p.Prime] {Y : Scheme.{0}} (g : Y ⟶ Sp (ZMod (p ^ 2))) (U : Y.Opens) {n : ℕ} (t : Fin n → Γ(Y, U)), IsAffineOpen U → IsEtCoord g U t → ∀ (η : Y) (hη : η ∈ U), ∃ F : Y.presheaf.stalk η →+* Y.presheaf.stalk η, (∀ z, ∃ w, F z = z ^ p + p * w) ∧ (∀ l, F ((Y.presheaf.germ U η hη).hom (t l)) = (Y.presheaf.germ U η hη).hom (t l) ^ p) ∧ ∀ (y : Y), y ∈ U → ∀ (h : η ⤳ y), ∀ z ∈ stalkIm h, ∃ w ∈ stalkIm h, F z = z ^ p + p * w := by
  first | exact @_root_.GlobalTheory.DI.exists_frobLift_stalk_of_etCoord | exact _root_.GlobalTheory.DI.exists_frobLift_stalk_of_etCoord | (intros; apply _root_.GlobalTheory.DI.exists_frobLift_stalk_of_etCoord <;> assumption)
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SncChartEquationsDifferUnit
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.snc_chart_equations_differ_unit : ∀ {R : Type} [CommRing R] {Y : Scheme.{0}} (g : Y ⟶ Sp R) {n s : ℕ} (L : Fin s → LB Y) (σ : ∀ i, (L i).Sec), (∀ i, (L i).IsLB) → ∀ (C C' : SncChart g n L σ) (y : Y) (hy : y ∈ C.U) (hy' : y ∈ C'.U) (c : Fin s), ∃ v : (Y.presheaf.stalk y)ˣ, (Y.presheaf.germ C.U y hy).hom ((C.e c).elim 1 C.t) = v * (Y.presheaf.germ C'.U y hy').hom ((C'.e c).elim 1 C'.t) := by
  first | exact @_root_.GlobalTheory.LogPair.sncChart_germ_eqn_unit | exact _root_.GlobalTheory.LogPair.sncChart_germ_eqn_unit | (intros; apply _root_.GlobalTheory.LogPair.sncChart_germ_eqn_unit <;> assumption)
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.FrobeniusLiftUnitTimesCoord
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.frobenius_lift_unit_times_coord : ∀ (p : ℕ) {Kt : Type} [CommRing Kt] (At : Subring Kt) (F : Kt →+* Kt) (v v' t : Kt), (p : Kt) * p = 0 → v' ∈ At → v * v' = 1 → (∃ w ∈ At, F v = v ^ p + p * w) → F t = t ^ p → ∃ w ∈ At, F (v * t) = (v * t) ^ p * (1 + p * w) := by
  first | exact @_root_.GlobalTheory.DI.unit_mul_logarithmic_lift | exact _root_.GlobalTheory.DI.unit_mul_logarithmic_lift | (intros; apply _root_.GlobalTheory.DI.unit_mul_logarithmic_lift <;> assumption)
end

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.DI

theorem lifted_stalkMap_germ_appLE {Y Z : Scheme.{0}} (f : Z ⟶ Y) (W : Y.Opens) (W' : Z.Opens)
    (h : W' ≤ f ⁻¹ᵁ W) (z : Z) (hz : z ∈ W') (s : Γ(Y, W)) :
    (f.stalkMap z).hom ((Y.presheaf.germ W (f z) (h hz)).hom s) =
      (Z.presheaf.germ W' z hz).hom ((f.appLE W W' h).hom s) := by
  have h1 := Scheme.Hom.germ_stalkMap_apply f W z (h hz) s
  have h2 := TopCat.Presheaf.germ_res_apply Z.presheaf (homOfLE h) z hz ((f.app W).hom s)
  exact h1.trans h2.symm

theorem isLifted_of_sncCharts : ∀ (p : ℕ) [Fact p.Prime] (Y X : Scheme.{0}) [IsIntegral X] (g : Y ⟶ Sp (ZMod (p ^ 2))) (f : X ⟶ Sp (ZMod p)) (π : X ⟶ Y), IsPullback π f g (spMap (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p))) → ∀ {n s : ℕ} (L : Fin s → LB Y) (σ : ∀ i, (L i).Sec), (∀ i, (L i).IsLB) → ∀ {ι : Type} [Nonempty ι] (C : ι → SncChart g n L σ) (Z : Set X) (U : ι → X.Opens) (hU : ∀ i, U i ≤ π ⁻¹ᵁ (C i).U) (hgen : ∀ i, genericPoint X ∈ U i) (x : ι → Fin n → X.functionFieldˣ) (J : ι → Finset (Fin n)), (∀ i l, (x i l : X.functionField) = fnOf (U i) (hgen i) ((π.appLE (C i).U (U i) (hU i)).hom ((C i).t l))) → (∀ i l, l ∈ J i → ∃ c, (C i).e c = some l) → (∀ i, IsLogChart Z (U i) (x i) (J i)) → IsLifted p Z U x := by
  intro p _ Y X _ q f π hpb n s L σ hL ι _ C Z U hU hgen x J hx hJ hchart
  obtain ⟨i₁⟩ := ‹Nonempty ι›
  have hη : ∀ i, π (genericPoint X) ∈ (C i).U := fun i => hU i (hgen i)
  let πK : Y.presheaf.stalk (π (genericPoint X)) →+* X.functionField := (π.stalkMap (genericPoint X)).hom
  have hflat : IsFlatLift p πK :=
    GlobalTheory.T.etale_coordinates_flat_lift p Y X q f π hpb (C i₁).U (C i₁).t (C i₁).affine (C i₁).etale (genericPoint X) (hη i₁)
  have hpK : (p : X.functionField) = 0 := by
    have h0 := (hflat.ker (p : Y.presheaf.stalk (π (genericPoint X)))).2 ⟨1, by ring⟩
    simpa using h0
  haveI : CharP X.functionField p := (CharP.charP_iff_prime_eq_zero Fact.out).2 hpK
  have hpp := logLift_pp_zero p πK hflat
  choose F hF1 hF2 hF3 using fun i =>
    GlobalTheory.T.exists_frobenius_lift_stalk p q (C i).U (C i).t (C i).affine (C i).etale (π (genericPoint X)) (hη i)

  have hlift : ∀ i l, πK ((Y.presheaf.germ (C i).U (π (genericPoint X)) (hη i)).hom ((C i).t l)) =
      (x i l : X.functionField) := by
    intro i l
    rw [hx i l]
    exact lifted_stalkMap_germ_appLE π (C i).U (U i) (hU i) (genericPoint X) (hgen i) ((C i).t l)
  refine ⟨Y.presheaf.stalk (π (genericPoint X)), inferInstance, πK, F, hflat, ?_, ?_, ?_⟩
  · intro i z
    obtain ⟨w, hw⟩ := hF1 i z
    rw [hw, map_add (f := _), map_pow, map_mul, map_natCast, hpK, zero_mul, add_zero]
  · intro i l
    exact ⟨_, hlift i l, hF2 i l⟩
  intro y t hyt a ha
  rcases t.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
  · obtain ⟨z, hz⟩ := hflat.surj (a : X.functionField)
    exact ⟨z, hz, fun i hi => absurd hi (Finset.notMem_empty i)⟩
  have hsp : π (genericPoint X) ⤳ π y :=
    ((genericPoint_spec X).specializes (Set.mem_univ y)).map π.continuous
  have hsurj := (GlobalTheory.T.mod_p_squared_stalk_surjective p Y X q f π hpb y).1
  have hloc := GlobalTheory.T.local_ring_image_stalk_map π y hsp hsurj
  set At := stalkIm hsp with hAt
  have hmap : (locRing y : Set X.functionField) = (At.map πK : Set X.functionField) := by
    ext c
    rw [SetLike.mem_coe, hloc, SetLike.mem_coe, Subring.mem_map]
  have hstab : ∀ i ∈ t, ∀ z ∈ At, ∃ w ∈ At, F i z = z ^ p + p * w :=
    fun i hi z hz => hF3 i (π y) (hU i (hyt i hi)) hsp z hz
  obtain ⟨u, m, hu, rfl⟩ := ((hchart i₀).logUnit y (hyt i₀ hi₀) a).1 ha
  rw [hmap]

  have hu0 : (u : X.functionField) ≠ 0 := u.ne_zero
  have hU1 : LogLift p πK F t (At.map πK : Set X.functionField) (u : X.functionField) := by
    have h2 := (unitAt_iff hu0).1 hu
    refine logLift_of_unit_mem_map p πK F t At hflat hstab _ hu0 ?_ ?_
    · exact Subring.mem_map.2 ((hloc _).1 h2.1)
    · exact Subring.mem_map.2 ((hloc _).1 h2.2)

  have hcoord : ∀ j ∈ J i₀, LogLift p πK F t (At.map πK : Set X.functionField) (x i₀ j : X.functionField) := by
    intro j hj
    obtain ⟨c, hc⟩ := hJ i₀ j hj
    refine ⟨_, hlift i₀ j, fun i hi => ?_⟩
    obtain ⟨v, hv⟩ := GlobalTheory.T.snc_chart_equations_differ_unit q L σ hL (C i₀) (C i) (π y) (hU i₀ (hyt i₀ hi₀)) (hU i (hyt i hi)) c
    rw [hc] at hv
    change (Y.presheaf.germ (C i₀).U (π y) (hU i₀ (hyt i₀ hi₀))).hom ((C i₀).t j) = _ at hv
    have hv' := congrArg (Y.presheaf.stalkSpecializes hsp).hom hv
    have e1 : ∀ (V : Y.Opens) (hV : π y ∈ V) (r : Γ(Y, V)),
        (Y.presheaf.stalkSpecializes hsp).hom ((Y.presheaf.germ V (π y) hV).hom r) =
          (Y.presheaf.germ V (π (genericPoint X)) (hsp.mem_open V.isOpen hV)).hom r :=
      fun V hV r => TopCat.Presheaf.germ_stalkSpecializes_apply Y.presheaf hV hsp r
    rw [map_mul] at hv'
    have hv2 : (Y.presheaf.germ (C i₀).U (π (genericPoint X)) (hη i₀)).hom ((C i₀).t j) =
        (Y.presheaf.stalkSpecializes hsp).hom (v : Y.presheaf.stalk (π y)) *
          (Y.presheaf.germ (C i).U (π (genericPoint X)) (hη i)).hom (((C i).e c).elim 1 (C i).t) := by
      refine (e1 _ _ _).symm.trans (hv'.trans ?_)
      congr 1
      exact e1 _ _ _
    set sv := (Y.presheaf.stalkSpecializes hsp).hom (v : Y.presheaf.stalk (π y)) with hsv
    set sv' := (Y.presheaf.stalkSpecializes hsp).hom ((v⁻¹ : (Y.presheaf.stalk (π y))ˣ) :
      Y.presheaf.stalk (π y)) with hsv'
    have hsvA : sv ∈ At := ⟨_, rfl⟩
    have hsv'A : sv' ∈ At := ⟨_, rfl⟩
    have hvv : sv * sv' = 1 := by rw [hsv, hsv', ← map_mul, Units.mul_inv, map_one]
    have hkey : ∀ o : Option (Fin n),
        F i ((Y.presheaf.germ (C i).U (π (genericPoint X)) (hη i)).hom (o.elim 1 (C i).t)) =
          ((Y.presheaf.germ (C i).U (π (genericPoint X)) (hη i)).hom (o.elim 1 (C i).t)) ^ p := by
      rintro (_ | l)
      · show F i ((Y.presheaf.germ (C i).U (π (genericPoint X)) (hη i)).hom 1) = _
        simp
      · exact hF2 i l
    obtain ⟨w, hwA, hw⟩ := GlobalTheory.T.frobenius_lift_unit_times_coord p At (F i) sv sv' _ hpp hsv'A hvv (hstab i hi sv hsvA) (hkey ((C i).e c))
    refine ⟨w, Subring.mem_map.2 ⟨w, hwA, rfl⟩, ?_⟩
    rw [hv2]
    exact hw
  rw [Units.val_mul, Units.coe_prod]
  refine logLift_mul p πK F t _ hflat hU1 ?_
  refine Finset.prod_induction _ (LogLift p πK F t (At.map πK : Set X.functionField))
    (fun _ _ => logLift_mul p πK F t _ hflat) (logLift_one p πK F t _) (fun j hj => ?_)
  rw [Units.val_zpow_eq_zpow_val]
  exact logLift_zpow p πK F t _ hflat (x i₀ j).ne_zero (hcoord j hj) (m j)

end GlobalTheory.DI
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

namespace GlobalTheory.LogAtlas

theorem fnOf_coord_ne_zero {R : Type} [CommRing R] [IsDomain R] {X : Scheme.{0}} [IsIntegral X]
    {f : X ⟶ Sp R} {U : X.Opens} (h : genericPoint X ∈ U) {n : ℕ} {t : Fin n → Γ(X, U)}
    (ht : IsEtCoord f U t) (j : Fin n) : fnOf U h (t j) ≠ 0 := by
  intro h0
  have h1 : t j = 0 := fnOf_injective U h (h0.trans (map_zero _).symm)
  letI := (MvPolynomial.eval₂Hom (cstOn f U) t).toAlgebra
  have : Algebra.Etale (MvPolynomial (Fin n) R) Γ(X, U) := ht
  have : Nonempty U := ⟨⟨_, h⟩⟩
  have h2 := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Γ(X, U))
      (mem_nonZeroDivisors_of_ne_zero (MvPolynomial.X_ne_zero (R := R) j))
  have h3 : (MvPolynomial.X j : MvPolynomial (Fin n) R) • (1 : Γ(X, U)) =
      (MvPolynomial.X j : MvPolynomial (Fin n) R) • (0 : Γ(X, U)) := by
    rw [smul_zero, Algebra.smul_def, mul_one]
    exact (MvPolynomial.eval₂Hom_X' _ _ j).trans h1
  exact one_ne_zero (h2 h3)

theorem exists_div_of_sec {X : Scheme.{0}} [IsIntegral X] {M : LB X} (hM : M.IsLB) (τ : M.Sec) (c₀ : M.ι)
    (h₀ : genericPoint X ∈ M.U c₀) (hτ : fnOf _ h₀ (τ.f c₀) ≠ 0) :
    ∃ E : CartierDiv X, toPic E = cls M hM ∧ ∀ (c : M.ι) (y : X) (hy : y ∈ M.U c)
      (g : X.functionFieldˣ), (g : X.functionField) = fnOf _ (gen_mem hy) (τ.f c) → E.IsEqn y g := by
  have P := presents_ofLB hM c₀ h₀
  have hr : P.rat τ ≠ 0 := fun e => hτ (by rw [← P.rat_mul τ c₀ h₀, e, zero_mul])
  have Q := P.add_principal (Units.mk0 _ hr)
  refine ⟨_, Q.toPic_eq, fun c y hy g hg => ?_⟩
  have e : g = frameRat M c₀ h₀ c * Units.mk0 _ hr := Units.ext (by
    rw [hg, ← P.rat_mul τ c (gen_mem hy), Units.val_mul, Units.val_mk0, mul_comm])
  exact e ▸ Q.isEqn c y hy

theorem exists_div_of_chart {R : Type} [CommRing R] [IsDomain R] {X : Scheme.{0}} [IsIntegral X]
    {f : X ⟶ Sp R} {d s : ℕ} {M : Fin s → LB X} (hM : ∀ i, (M i).IsLB) {τ : ∀ i, (M i).Sec}
    (C₀ : SncChart f d M τ) (h₀ : genericPoint X ∈ C₀.U) :
    ∃ E : Fin s → CartierDiv X, (∀ i, toPic (E i) = cls (M i) (hM i)) ∧
      ∀ (C : SncChart f d M τ) (h : genericPoint X ∈ C.U) (x : Fin d → X.functionFieldˣ),
        (∀ j, (x j : X.functionField) = fnOf C.U h (C.t j)) →
        ∀ i, ∀ y ∈ C.U, (E i).IsEqn y ((C.e i).elim 1 x) := by
  have key (C : SncChart f d M τ) (h : genericPoint X ∈ C.U) (i : Fin s) :
      fnOf _ (C.le i h) ((τ i).f (C.c i)) = fnOf C.U h (C.u i) * fnOf C.U h ((C.e i).elim 1 C.t) := by
    rw [← fnOf_resG (C.le i) h, C.eq i, map_mul]
  have H (i : Fin s) := exists_div_of_sec (hM i) (τ i) (C₀.c i) (C₀.le i h₀) (by
    rw [key C₀ h₀ i]
    refine mul_ne_zero (unitAt_fnOf h₀ h₀ _).ne_zero ?_
    rcases C₀.e i with _ | a
    · simp
    · exact fnOf_coord_ne_zero h₀ C₀.etale a)
  choose E hE hE' using H
  refine ⟨E, hE, fun C h x hx i y hy => ?_⟩
  have hu := unitAt_fnOf hy h (C.u i)
  have e : (((C.e i).elim 1 x : X.functionFieldˣ) : X.functionField) =
      fnOf C.U h ((C.e i).elim 1 C.t) := by
    rcases C.e i with _ | a
    · simp
    · exact hx a
  have h1 := hE' i (C.c i) y (C.le i hy) (Units.mk0 _ hu.ne_zero * (C.e i).elim 1 x) (by
    rw [Units.val_mul, Units.val_mk0, e]; exact (key C h i).symm)
  rw [h1.iff_unitAt, Units.val_mul, Units.val_mk0, div_mul_eq_div_div_swap, div_self (Units.ne_zero _),
    one_div]
  exact hu.inv

noncomputable def pullChart {R R' : Type} [CommRing R] [CommRing R'] {φ : R →+* R'} {X X' : Scheme.{0}}
    {f : X ⟶ Sp R} {f' : X' ⟶ Sp R'} {π : X' ⟶ X} (hP : IsPullback π f' f (spMap φ)) {d s : ℕ}
    {L : Fin s → LB X} {σ : ∀ i, (L i).Sec} (C : SncChart f d L σ) :
    SncChart f' d (fun i => (L i).pull π) (fun i => Cartier.secPull (σ i) π) where
  U := π ⁻¹ᵁ C.U
  affine := (isEtCoord_baseChange R R' φ X X' f f' π C.U d C.t hP C.affine C.etale).1
  t := fun a => (π.app C.U).hom (C.t a)
  etale := (isEtCoord_baseChange R R' φ X X' f f' π C.U d C.t hP C.affine C.etale).2
  c := fun i => fun _ => C.c i
  le := fun i => (π.preimage_mono (C.le i)).trans (Cartier.pull_U (L i) π fun _ => C.c i).ge
  e := C.e
  inj := C.inj
  u := fun i => Units.map (π.app C.U).hom (C.u i)
  eq := fun i => by
    show resG X' _ (resG X' _ ((π.app _).hom ((σ i).f (C.c i)))) = _
    rw [Cartier.resG_resG, ← Cartier.app_resG π (C.le i), C.eq i, map_mul]
    rcases h : C.e i with _ | a
    · simp
    · simp

theorem exists_atlas_decomp : ∀ (p : ℕ) [Fact p.Prime] (Y X : Scheme.{0}) [IsIntegral X] (g : Y ⟶ Sp (ZMod (p ^ 2))) (f : X ⟶ Sp (ZMod p)) (π : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f], IsPullback π f g (spMap (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p))) → IsProjOver f → d < p → ∀ (s : ℕ) (L : Fin s → LB Y) (σ : ∀ i, (L i).Sec) (h : RelSnc g d L σ), ∃ (m : ℕ) (E : Fin s → CartierDiv X) (𝒜 : SncAtlas E d (Fin m)), Decomp p 𝒜 ∧ ∀ i, toPic (E i) = CechPic.pull π (cls (L i) (h.isLB i)) := by
  classical
  intro p _ Y X _ g f π d _ hP hf hd s L σ h
  choose D hD using fun x : X => h.chart (π x)
  have hpr := (isProper_and_exists_isAmpleLB_of_isProjOver hf).1
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun x : X => ((π ⁻¹ᵁ (D x).U : X.Opens) : Set X))
    (fun x => (π ⁻¹ᵁ (D x).U).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hD x⟩)
  let ε := T.equivFin.symm
  let C : Fin T.card → SncChart g d L σ := fun k => D (ε k)
  have hgen (k) : genericPoint X ∈ (pullChart hP (C k)).U := gen_mem (x := ε k) (hD _)
  have hcov (y : X) : ∃ k, y ∈ (pullChart hP (C k)).U := by
    obtain ⟨z, hz, hy⟩ := Set.mem_iUnion₂.1 (hT (Set.mem_univ y))
    obtain ⟨k, hk⟩ := ε.surjective ⟨z, hz⟩
    obtain rfl : (ε k : X) = z := congrArg Subtype.val hk
    exact ⟨k, hy⟩
  obtain ⟨k₀, -⟩ := hcov (genericPoint X)
  have : Nonempty (Fin T.card) := ⟨k₀⟩
  obtain ⟨E, hE, hE'⟩ := exists_div_of_chart (fun i => pull_isLB (h.isLB i) π) (pullChart hP (C k₀)) (hgen k₀)
  let x : Fin T.card → Fin d → X.functionFieldˣ := fun k j =>
    Units.mk0 _ (fnOf_coord_ne_zero (hgen k) (pullChart hP (C k)).etale j)
  let J : Fin T.card → Finset (Fin d) := fun k => Finset.univ.filter fun j => ∃ c, (C k).e c = some j
  have hJ (k j) : j ∈ J k ↔ ∃ c, (C k).e c = some j := by simp [J]
  have heq (k) := hE' (pullChart hP (C k)) (hgen k) (x k) (fun _ => rfl)
  have hlog (k) : IsLogChart (suppAll E) (pullChart hP (C k)).U (x k) (J k) := by
    refine GlobalTheory.T.etale_coordinates_log_chart p X f _ (hgen k) (pullChart hP (C k)).t (x k) (J k) _ (pullChart hP (C k)).affine
      (pullChart hP (C k)).etale (fun _ => rfl) fun y hy => ?_
    constructor
    · intro hy'
      obtain ⟨c, hc⟩ := Set.mem_iUnion.1 hy'
      have h1 := (heq k c y hy).mem_supp_iff.1 hc
      change ¬ UnitAt y ((((C k).e c).elim 1 (x k) : X.functionFieldˣ) : X.functionField) at h1
      rcases he : (C k).e c with _ | a
      · rw [he] at h1
        exact (h1 (unitAt_one y)).elim
      · rw [he] at h1
        exact ⟨a, (hJ k a).2 ⟨c, he⟩, h1⟩
    · rintro ⟨j, hj, hu⟩
      obtain ⟨c, hc⟩ := (hJ k j).1 hj
      refine Set.mem_iUnion.2 ⟨c, (heq k c y hy).mem_supp_iff.2 ?_⟩
      change ¬ UnitAt y ((((C k).e c).elim 1 (x k) : X.functionFieldˣ) : X.functionField)
      rw [hc]
      exact hu
  let 𝒜 : SncAtlas E d (Fin T.card) :=
    { U := fun k => (pullChart hP (C k)).U
      x := x
      J := J
      affine := fun k => (pullChart hP (C k)).affine
      gen := hgen
      cover := eq_top_iff.2 fun y _ => Opens.mem_iSup.2 (hcov y)
      chart := hlog
      snc := fun k => ⟨(C k).e, (C k).inj, hJ k, heq k⟩ }
  have : CharP X.functionField p := charP_of_injective_ringHom (Cartier.constFn f).injective p
  refine ⟨T.card, E, 𝒜, GlobalTheory.T.frobenius_decomposition_of_lift p 𝒜 hd ?_, fun i => (hE i).trans (CechPic.cls_pull (h.isLB i) π _)⟩
  refine DI.isLifted_of_sncCharts p Y X g f π hP L σ h.isLB C _ _ (fun _ => le_rfl) hgen x J
    (fun k l => ?_) (fun k l => (hJ k l).1) hlog
  exact congrArg (fun ψ : Γ(Y, (C k).U) ⟶ Γ(X, π ⁻¹ᵁ (C k).U) => fnOf _ (hgen k) (ψ.hom ((C k).t l)))
    (π.app_eq_appLE)

end GlobalTheory.LogAtlas
