module

public import Development.WeilBound.CoreStatements.FlagImmersions.FibSandwich
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DegreeInvariantLinearEquiv
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TeichmullerCharacterOrderGenerates
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LabelSettingTameGenerator
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.DifferentIdealLogSumRootDiscriminant

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.AdelicProofs.NormEqOneOfValuationEqOne
open NumberField IsDedekindDomain GlobalTheory.CompanionTheory.Ar.Fl

namespace GlobalTheory.CompanionTheory.Ar.Flat

section Place

variable {F : Type} [Field F] [NumberField F] {p : ℕ} [Fact p.Prime]

noncomputable def placeOf (κ : F →+* ℂ_[p]) : HeightOneSpectrum (𝓞 F) where
  asIdeal := GlobalTheory.DatumJets.Place.smallIdeal κ
  isPrime := GlobalTheory.DatumJets.Place.smallIdeal_isPrime κ
  ne_bot := by
    intro hbot
    have hp : ((p : ℕ) : 𝓞 F) ∈ GlobalTheory.DatumJets.Place.smallIdeal κ := by
      rw [GlobalTheory.DatumJets.Place.mem_smallIdeal]
      simpa using GlobalTheory.DatumJets.Place.norm_p_lt_one (p := p)
    rw [hbot, Ideal.mem_bot] at hp
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast hp)

theorem mem_placeOf (κ : F →+* ℂ_[p]) (y : 𝓞 F) :
    y ∈ (placeOf κ).asIdeal ↔ ‖κ (y : F)‖ < 1 := Iff.rfl

theorem valuation_placeOf_le_one_iff (κ : F →+* ℂ_[p]) (a : F) :
    (placeOf κ).valuation F a ≤ 1 ↔ ‖κ a‖ ≤ 1 :=
  ⟨fun h => GlobalTheory.MomPlace.norm_le_one_of_valuation F p κ (placeOf κ) (mem_placeOf κ) a h,
    fun h => GlobalTheory.DatumJets.Place.valuation_le_one_of_norm κ (placeOf κ) (mem_placeOf κ) a h⟩

theorem norm_eq_one_of_valuation_eq_one (κ : F →+* ℂ_[p]) {u : F}
    (hu : (placeOf κ).valuation F u = 1) : ‖κ u‖ = 1 := by
  have h1 : ‖κ u‖ ≤ 1 := (valuation_placeOf_le_one_iff κ u).1 hu.le
  have h2 : ‖κ u⁻¹‖ ≤ 1 := (valuation_placeOf_le_one_iff κ u⁻¹).1 (by simp [hu])
  rw [map_inv₀, norm_inv] at h2
  have h0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  have h3 : 0 < ‖κ u‖ := by simp [h0]
  exact le_antisymm h1 ((inv_le_one₀ h3).1 h2)

theorem log_norm_eq_of_valuation (κ : F →+* ℂ_[p]) {π α : F} {n : ℤ}
    (hπ : (placeOf κ).valuation F π = WithZero.exp (-1 : ℤ))
    (hα : (placeOf κ).valuation F α = WithZero.exp (-n)) (hα0 : α ≠ 0) :
    Real.log ‖κ α‖ = n * Real.log ‖κ π‖ := by
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hu : (placeOf κ).valuation F (α * π ^ (-n)) = 1 := by
    rw [map_mul, map_zpow₀, hα, hπ, ← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp
  have h := norm_eq_one_of_valuation_eq_one κ hu
  rw [map_mul, map_zpow₀, norm_mul, norm_zpow] at h
  have hκπ : ‖κ π‖ ≠ 0 := by simp [hπ0]
  have hκα : ‖κ α‖ ≠ 0 := by simp [hα0]
  have h2 := congrArg Real.log h
  rw [Real.log_mul hκα (zpow_ne_zero _ hκπ), Real.log_zpow, Real.log_one] at h2
  push_cast at h2
  linarith

theorem dvd_absNorm_placeOf (κ : F →+* ℂ_[p]) :
    p ∣ Ideal.absNorm (placeOf κ).asIdeal := by
  refine GlobalTheory.DatumJets.Place.dvd_of_natCast_mem (placeOf κ).asIdeal (placeOf κ).isPrime.ne_top
    Fact.out ?_ (Ideal.absNorm_mem _)
  rw [mem_placeOf]
  simpa using GlobalTheory.DatumJets.Place.norm_p_lt_one (p := p)

end Place

theorem deg_eq_places : ∀ (F : Type) [Field F] [NumberField F] (N : LogNorms F) (r : HeightOneSpectrum (𝓞 F) →₀ ℚ), (∀ (p : Nat.Primes) (κ : F →+* ℂ_[p]) (v : HeightOneSpectrum (𝓞 F)) (π : F), (∀ a : F, v.valuation F a ≤ 1 ↔ ‖κ a‖ ≤ 1) → v.valuation F π = WithZero.exp (-1 : ℤ) → N.fin p κ = (r v : ℝ) * Real.log ‖κ π‖) → N.IsAdelic ∧ N.deg = ((r.sum fun v q => (q : ℝ) * Real.log (Ideal.absNorm v.asIdeal)) - ∑ σ : F →+* ℂ, N.inf σ) / (Module.finrank ℚ F : ℝ) := by
  intro F _ _ N r h
  obtain ⟨M, α, hM, hα, hn⟩ := exists_pow_principal F r
  have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hfin : ∀ (p : Nat.Primes) (κ : F →+* ℂ_[p]), ∃ π : F,
      N.fin p κ = (r (placeOf κ) : ℝ) * Real.log ‖κ π‖ ∧
        (placeOf κ).valuation F π = WithZero.exp (-1 : ℤ) := by
    intro p κ
    obtain ⟨π, hπ⟩ := (placeOf κ).valuation_exists_uniformizer F
    exact ⟨π, h p κ _ π (valuation_placeOf_le_one_iff κ) hπ, hπ⟩
  have key : ∀ (p : Nat.Primes) (κ : F →+* ℂ_[p]), (M : ℝ) * N.fin p κ = Real.log ‖κ α‖ := by
    intro p κ
    obtain ⟨π, h1, hπ⟩ := hfin p κ
    obtain ⟨m, hm, hv⟩ := hn (placeOf κ)
    rw [log_norm_eq_of_valuation κ hπ hv hα, h1]
    have hm' : (m : ℝ) = M * (r (placeOf κ) : ℝ) := by exact_mod_cast congrArg (fun q : ℚ => (q : ℝ)) hm
    rw [hm']
    ring
  have hadel : N.IsAdelic := by
    have hS : ((r.support.biUnion fun v => (Ideal.absNorm v.asIdeal).primeFactors : Finset ℕ) : Set ℕ).Finite :=
      Finset.finite_toSet _
    refine (hS.preimage (f := fun p : Nat.Primes => (p : ℕ)) Subtype.val_injective.injOn).subset ?_
    rintro p ⟨κ, hκ⟩
    obtain ⟨π, h1, -⟩ := hfin p κ
    have hr : r (placeOf κ) ≠ 0 := by
      intro h0
      exact hκ (by rw [h1, h0]; simp)
    simp only [Set.mem_preimage, Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe, Nat.mem_primeFactors]
    refine ⟨placeOf κ, Finsupp.mem_support_iff.2 hr, p.2, dvd_absNorm_placeOf κ, ?_⟩
    have := NumberField.HeightOneSpectrum.one_lt_absNorm (placeOf κ)
    omega
  refine ⟨hadel, ?_⟩
  let n : HeightOneSpectrum (𝓞 F) →₀ ℤ := r.mapRange (fun q => ⌊(M : ℚ) * q⌋) (by simp)
  have hnv : ∀ v, ((n v : ℤ) : ℚ) = M * r v := by
    intro v
    obtain ⟨m, hm, -⟩ := hn v
    simp [n, ← hm]
  have hn' : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F α = WithZero.exp (-(n v)) := by
    intro v
    obtain ⟨m, hm, hv⟩ := hn v
    have : n v = m := by
      have := hnv v
      rw [← hm] at this
      exact_mod_cast this
    rw [this]
    exact hv
  have h1 := sum_log_embeddings_eq F n α hα hn'
  have h2 := (GlobalTheory.T.product_formula_log_norms F α hα).2
  have h3 : ∀ p, (LogNorms.ofElt α).finSum p = M * N.finSum p := by
    intro p
    simp only [LogNorms.finSum, LogNorms.ofElt, Finset.mul_sum, key]
  have hsupp : (Function.support N.finSum).Finite := by
    refine Set.Finite.subset hadel ?_
    intro p hp
    by_contra hc
    simp only [Set.mem_setOf_eq, not_exists, not_not] at hc
    exact hp (by simp [LogNorms.finSum, hc])
  have h4 : ∑ᶠ p, (LogNorms.ofElt α).finSum p = M * ∑ᶠ p, N.finSum p := by
    simp_rw [h3]
    rw [mul_finsum]
  have h5 : (n.sum fun v k => (k : ℝ) * Real.log (Ideal.absNorm v.asIdeal)) =
      M * r.sum fun v q => (q : ℝ) * Real.log (Ideal.absNorm v.asIdeal) := by
    rw [Finsupp.sum_mapRange_index (by simp), Finsupp.sum, Finsupp.sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    have h6 : ((⌊(M : ℚ) * r v⌋ : ℤ) : ℝ) = M * (r v : ℝ) := by
      have h7 := hnv v
      have h8 : n v = ⌊(M : ℚ) * r v⌋ := by simp [n]
      rw [h8] at h7
      exact_mod_cast congrArg (fun q : ℚ => (q : ℝ)) h7
    rw [h6]
    ring
  have h6 : ∑ᶠ p, N.finSum p = -(r.sum fun v q => (q : ℝ) * Real.log (Ideal.absNorm v.asIdeal)) := by
    apply mul_left_cancel₀ hMR
    rw [← h4, mul_neg, ← h5, ← h1]
    linarith
  rw [LogNorms.deg, h6]
  congr 1
  ring

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AdelicProofs.SqrtDiscriminantBoundsCmField
section -- merged from Development.WeilBound.CoreStatements.SesquilinearFractions.SqrtDiscriminantBoundsCmField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

namespace PositivityTheory.Xgf

section SlopeTestRemainingChoices

variable {O J : Type} [CommRing O] [Fintype J] [DecidableEq J]

theorem prime_dvd_trace_of_sq (b : Module.Basis J ℤ O) (d : ℕ) (hd : d.Prime) (y z : O) (h : y ^ 2 = (d : O) * z) :
    (d : ℤ) ∣ Algebra.trace ℤ O y := by
  classical
  haveI : Fact d.Prime := ⟨hd⟩
  rw [Algebra.trace_eq_matrix_trace b y, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hnil : IsNilpotent ((Algebra.leftMulMatrix b y).map (Int.castRingHom (ZMod d))) := by
    refine ⟨2, ?_⟩
    have e : (d : O) * z = (d : ℤ) • z := by simp [zsmul_eq_mul]
    rw [← Matrix.map_pow, ← map_pow, h, e, map_zsmul]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply, eq_intCast,
      Int.cast_mul, Int.cast_natCast, ZMod.natCast_self]
    simp
  have htr := (Matrix.isNilpotent_trace_of_isNilpotent hnil).eq_zero
  have hc : ((Algebra.leftMulMatrix b y).map (Int.castRingHom (ZMod d))).trace
      = (((Algebra.leftMulMatrix b y).trace : ℤ) : ZMod d) := by
    simp [Matrix.trace, Matrix.map_apply]
  rw [← hc]
  exact htr

theorem traceMatrix_mul_leftMulMatrix (b : Module.Basis J ℤ O) (r : O) (i j : J) :
    (Algebra.traceMatrix ℤ b * Algebra.leftMulMatrix b r) i j = Algebra.trace ℤ O (b i * (r * b j)) := by
  rw [Matrix.mul_apply]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Algebra.leftMulMatrix_eq_repr_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    conv_rhs => rw [← b.sum_repr (r * b j), Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_smul_comm, LinearMap.map_smul, smul_eq_mul, mul_comm]

theorem discriminant_bound_sqrt_neg_prime (b : Module.Basis J ℤ O) (d : ℕ) (hd : d.Prime) (r : O) (hr : r ^ 2 = -(d : O))
    (h0 : Algebra.discr ℤ b ≠ 0) : (d : ℤ) ^ Fintype.card J ≤ Algebra.discr ℤ b ^ 2 := by
  classical
  have hd0 : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne_zero
  have hent : ∀ i j, (d : ℤ) ∣ (Algebra.traceMatrix ℤ b * Algebra.leftMulMatrix b r) i j := by
    intro i j
    rw [traceMatrix_mul_leftMulMatrix b r i j]
    refine prime_dvd_trace_of_sq b d hd (b i * (r * b j)) (-((b i) ^ 2 * (b j) ^ 2)) ?_
    have e : (b i * (r * b j)) ^ 2 = (b i) ^ 2 * (b j) ^ 2 * r ^ 2 := by ring
    rw [e, hr]
    ring
  let C : Matrix J J ℤ := fun i j => (Algebra.traceMatrix ℤ b * Algebra.leftMulMatrix b r) i j / d
  have hTL : Algebra.traceMatrix ℤ b * Algebra.leftMulMatrix b r = (d : ℤ) • C := by
    ext i j
    simp only [C, Matrix.smul_apply, smul_eq_mul]
    exact (Int.mul_ediv_cancel' (hent i j)).symm
  have hL2 : (Algebra.leftMulMatrix b r).det ^ 2 = (-(d : ℤ)) ^ Fintype.card J := by
    rw [sq, ← Matrix.det_mul, ← map_mul, ← sq, hr]
    have e : (-(d : O)) = algebraMap ℤ O (-(d : ℤ)) := by simp
    rw [e, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, Matrix.det_smul, Matrix.det_one,
      _root_.mul_one]
  have h1 : (Algebra.traceMatrix ℤ b * Algebra.leftMulMatrix b r).det ^ 2
      = ((d : ℤ) ^ Fintype.card J) ^ 2 * C.det ^ 2 := by
    rw [hTL, Matrix.det_smul]
    ring
  rw [Matrix.det_mul, mul_pow, hL2, ← Algebra.discr_def, neg_pow] at h1
  have key2 : Algebra.discr ℤ b ^ 2 * (-1) ^ Fintype.card J = (d : ℤ) ^ Fintype.card J * C.det ^ 2 := by
    apply mul_right_cancel₀ (pow_ne_zero (Fintype.card J) hd0)
    linear_combination h1
  have hdv : (d : ℤ) ^ Fintype.card J ∣ Algebra.discr ℤ b ^ 2 := by
    have h2 : (d : ℤ) ^ Fintype.card J ∣ Algebra.discr ℤ b ^ 2 * (-1) ^ Fintype.card J := ⟨_, key2⟩
    rcases neg_one_pow_eq_or ℤ (Fintype.card J) with h | h <;> rw [h] at h2 <;> simpa using h2
  exact Int.le_of_dvd (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h0))) hdv

end SlopeTestRemainingChoices

theorem sqrt_discriminant_bounds_cm_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), 1 ≤ Real.sqrt H.d ∧ Real.sqrt H.d ≤ rootDiscr E := by
  intro E _ _ _ H
  classical
  have hd := H.d_prime
  have hd1 : (1 : ℝ) ≤ H.d := by exact_mod_cast hd.one_lt.le
  refine ⟨by simpa using Real.sqrt_le_sqrt hd1, ?_⟩
  set n := Module.finrank ℚ E with hn
  have hn0 : n ≠ 0 := Module.finrank_pos.ne'
  have hD : (H.d : ℤ) ^ n ≤ (discr E) ^ 2 := by
    have h := discriminant_bound_sqrt_neg_prime (RingOfIntegers.basis E) H.d hd H.rt H.rt_sq (discr_ne_zero E)
    rw [← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank] at h
    exact h
  have hR : ((Real.sqrt H.d) ^ n) ^ 2 ≤ |((discr E : ℤ) : ℝ)| ^ 2 := by
    rw [← pow_mul, mul_comm n 2, pow_mul, Real.sq_sqrt (by positivity), sq_abs]
    exact_mod_cast hD
  have hR2 : (Real.sqrt H.d) ^ n ≤ |((discr E : ℤ) : ℝ)| :=
    (pow_le_pow_iff_left₀ (by positivity) (abs_nonneg _) two_ne_zero).mp hR
  rw [rootDiscr_def]
  rw [Int.cast_abs]
  calc Real.sqrt H.d = ((Real.sqrt H.d) ^ n) ^ ((n : ℝ)⁻¹) :=
        (Real.pow_rpow_inv_natCast (Real.sqrt_nonneg _) hn0).symm
    _ ≤ _ := Real.rpow_le_rpow (by positivity) hR2 (by positivity)

end PositivityTheory.Xgf
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AdelicProofs.SqrtDiscriminantBoundsCmField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.sqrt_discriminant_bounds_cm_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), 1 ≤ Real.sqrt H.d ∧ Real.sqrt H.d ≤ rootDiscr E := by
  first | exact @PositivityTheory.Xgf.sqrt_discriminant_bounds_cm_field | exact PositivityTheory.Xgf.sqrt_discriminant_bounds_cm_field
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AdelicProofs.SqrtDiscriminantBoundsCmFieldStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sqrt_discriminant_bounds_cm_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), 1 ≤ Real.sqrt H.d ∧ Real.sqrt H.d ≤ rootDiscr E := by
  first | exact @GlobalTheory.CompanionTheory.Relay.sqrt_discriminant_bounds_cm_field | exact GlobalTheory.CompanionTheory.Relay.sqrt_discriminant_bounds_cm_field | (intros; apply GlobalTheory.CompanionTheory.Relay.sqrt_discriminant_bounds_cm_field <;> assumption)
end
end

noncomputable section

open NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl

namespace RootFieldNumerics.RF

namespace Num

theorem value_bound (p q : ℕ) (l L : ℝ) (h7 : Real.log 7 / 2 ≤ l) :
    |((p : ℝ) - q) / 2 * (Real.eulerMascheroniConstant + Real.log (2 * Real.pi) - l - L)| +
      ((p + q : ℕ) : ℝ) * Real.log 2 ≤ ((p + q : ℕ) : ℝ) * (3 / 2 * l + |L| / 2) := by
  have hc := OnHodge.const_le
  have hγ := Real.one_half_lt_eulerMascheroniConstant
  have h2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have h70 : 0 < Real.log 7 := Real.log_pos (by norm_num)
  have h4 : 2 * Real.log 2 ≤ Real.log (2 * Real.pi) := by
    have : Real.log (2 ^ 2) ≤ Real.log (2 * Real.pi) :=
      Real.log_le_log (by norm_num) (by linarith [Real.pi_gt_three])
    rw [Real.log_pow] at this
    exact_mod_cast this
  have hL := le_abs_self L
  have hL' := neg_abs_le L
  have hp : (0 : ℝ) ≤ p := p.cast_nonneg
  have hq : (0 : ℝ) ≤ q := q.cast_nonneg
  set c := Real.eulerMascheroniConstant + Real.log (2 * Real.pi) with hcdef
  set b := 3 / 2 * l + |L| / 2 - Real.log 2 with hb
  have a1 : 0 ≤ b - (c - l - L) / 2 := by linarith
  have a2 : 0 ≤ b + (c - l - L) / 2 := by linarith
  have : |((p : ℝ) - q) / 2 * (c - l - L)| ≤ (p + q) * b :=
    abs_le.2 ⟨by nlinarith [mul_nonneg hp a2, mul_nonneg hq a1], by nlinarith [mul_nonneg hp a1, mul_nonneg hq a2]⟩
  push_cast
  nlinarith

theorem near_of (n : ℕ) (bad : Finset ℕ) (h2 : 2 ∈ bad) (rd L h₀ : ℝ) (d v : ℕ → ℝ)
    (hb : |h₀| + (n : ℝ) * Real.log 2 ≤ (n : ℝ) * (3 / 2 * Real.log rd + |L| / 2))
    (hd : ∀ r ∈ bad, 0 ≤ v r ∧ |d r| ≤ ((n : ℝ) * cP r + (n : ℝ) * v r) * Real.log r)
    (hv : ∑ r ∈ bad, v r * Real.log r ≤ Real.log rd) : NearRecord n bad rd L (h₀ + ∑ r ∈ bad, d r) := by
  set N : ℝ := (n : ℝ) with hN
  have hN0 : 0 ≤ N * Real.log 2 := mul_nonneg (Nat.cast_nonneg _) (Real.log_pos one_lt_two).le
  obtain ⟨hv2, hd2⟩ := hd 2 h2
  have hv2' := mul_nonneg hN0 hv2
  simp only [cP, if_true, Nat.cast_ofNat] at hd2
  obtain ⟨e, he, he'⟩ : ∃ e : ℝ, |e| ≤ N * Real.log 2 ∧ |d 2 - e| ≤ (N + N * v 2) * Real.log 2 := by
    rw [abs_le] at hd2
    rcases le_total 0 (d 2) with h | h
    · exact ⟨N * Real.log 2, (abs_of_nonneg hN0).le, abs_le.2 ⟨by nlinarith, by nlinarith⟩⟩
    · exact ⟨-(N * Real.log 2), by rw [abs_neg, abs_of_nonneg hN0], abs_le.2 ⟨by nlinarith, by nlinarith⟩⟩
  refine ⟨_ + e, fun r => d r - if r = 2 then e else 0, v, (abs_add_le _ _).trans ((add_le_add le_rfl he).trans hb), ?_,
    fun r hr => ⟨(hd r hr).1, ?_⟩, hv⟩
  · rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' bad 2, if_pos h2]; ring
  · by_cases h : r = 2
    · subst h
      have : ((2 : ℕ) : ℝ) - 1 = 1 := by norm_num
      simp only [if_true, this, div_one]
      exact_mod_cast he'
    · have := (hd r hr).2
      simp only [cP, if_neg h] at this ⊢
      rwa [sub_zero, div_eq_mul_one_div]

def extP (g : Nat.Primes → ℝ) (n : ℕ) : ℝ := if h : n.Prime then g ⟨n, h⟩ else 0

theorem extendFromPrimes_coe (g : Nat.Primes → ℝ) (ℓ : Nat.Primes) : extP g ℓ = g ℓ := dif_pos ℓ.2

theorem exists_primes (bad : Finset ℕ) (hb : ∀ ℓ ∈ bad, ℓ.Prime) :
    ∃ B : Finset Nat.Primes, (∀ ℓ, ℓ ∈ B ↔ (ℓ : ℕ) ∈ bad) ∧ ∀ G : ℕ → ℝ, ∑ ℓ ∈ bad, G ℓ = ∑ ℓ ∈ B, G ℓ := by
  refine ⟨bad.preimage (fun ℓ : Nat.Primes => (ℓ : ℕ)) Subtype.val_injective.injOn, fun ℓ => Finset.mem_preimage,
    fun G => ?_⟩
  exact (Finset.sum_preimage (fun ℓ : Nat.Primes => (ℓ : ℕ)) bad Subtype.val_injective.injOn G
    fun x hx hn => absurd ⟨⟨x, hb x hx⟩, rfl⟩ hn).symm

theorem place_eq {F : Type} [Field F] [NumberField F] {p : ℕ} [Fact p.Prime] (κ : F →+* ℂ_[p])
    (v : HeightOneSpectrum (𝓞 F)) (h : ∀ a : F, v.valuation F a ≤ 1 ↔ ‖κ a‖ ≤ 1) : v = placeOf κ := by
  refine HeightOneSpectrum.eq_of_valuation_isEquiv_valuation (K := F) ?_
  rw [Valuation.isEquiv_iff_val_le_one]
  intro a
  rw [h, valuation_placeOf_le_one_iff]

theorem logIdeal_nonpos {E : Type} [Field E] [NumberField E] (ℓ : Nat.Primes) (j : E →+* ℂ_[ℓ]) :
    logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) ≤ 0 := by
  obtain ⟨a, -, -, -, e⟩ := GlobalTheory.T.padic_logIdeal_max_element E ℓ (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))
    (j.injective.comp RingOfIntegers.coe_injective) differentIdeal_ne_bot
  rw [e]
  refine Real.log_nonpos (norm_nonneg _) ?_
  exact (valuation_placeOf_le_one_iff j (a : E)).1 ((placeOf j).valuation_le_one a)

end Num

open Num in
theorem numerics : Numerics := by
  intro E _ _ _ H p q F F' _ _ _ _ ι σ N r bad hσ h2 hbp hAd hdeg hloc
  classical
  choose π hπ using fun v : HeightOneSpectrum (𝓞 F') => v.valuation_exists_uniformizer F'
  let N' : LogNorms F' := ⟨fun s => N.inf (s.comp ι), fun ℓ κ' => (r (placeOf κ') : ℝ) * Real.log ‖κ' (π (placeOf κ'))‖⟩
  obtain ⟨hAd', hdeg'⟩ := deg_eq_places F' N' r (by
    intro ℓ κ' v π' hv hπ'
    obtain rfl := place_eq κ' v hv
    have h0 : π' ≠ 0 := by
      rintro rfl
      rw [map_zero] at hπ'
      exact WithZero.exp_ne_zero hπ'.symm
    have := log_norm_eq_of_valuation κ' (n := 1) (hπ _) hπ' h0
    show _ * _ = _
    rw [this]
    simp)
  have hgoal : ((r.sum fun v x => (x : ℝ) * Real.log (Ideal.absNorm v.asIdeal)) - ∑ s : F' →+* ℂ, N.inf (s.comp ι)) /
      (Module.finrank ℚ F' : ℝ) = N'.deg := hdeg'.symm
  rw [hgoal]
  obtain ⟨hext, hextA⟩ := GlobalTheory.T.logNorms_ext_degree_adelic F F' ι N
  have hAdx : (N.ext ι).IsAdelic := hextA.2 hAd
  have hl := fun (ℓ : Nat.Primes) (κ' : F' →+* ℂ_[ℓ]) =>
    hloc ℓ κ' (placeOf κ') (π _) (valuation_placeOf_le_one_iff κ') (hπ _)
  have hn' : (0 : ℝ) < Module.finrank ℚ F' := by exact_mod_cast Module.finrank_pos
  have hnE : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  obtain ⟨B, hB, hBs⟩ := exists_primes bad hbp
  let f : E →+* F' := IsFractionRing.lift (A := 𝓞 E) (g := ι.comp σ) (ι.injective.comp hσ)
  have hf : ∀ a : 𝓞 E, f (algebraMap (𝓞 E) E a) = ι (σ a) := fun a => IsFractionRing.lift_algebraMap _ a
  let g : Nat.Primes → ℝ := fun ℓ => -(N'.finSum ℓ - (N.ext ι).finSum ℓ) / Module.finrank ℚ F'
  let w : Nat.Primes → ℝ := fun ℓ =>
    -∑ j : E →+* ℂ_[ℓ], logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))
  have hw0 : ∀ ℓ, 0 ≤ w ℓ := fun ℓ => neg_nonneg.2 (Finset.sum_nonpos fun j _ => logIdeal_nonpos ℓ j)
  have hlog : ∀ ℓ : Nat.Primes, 0 < Real.log (ℓ : ℕ) := fun ℓ => Real.log_pos (by exact_mod_cast ℓ.2.one_lt)
  have hsupp : ∀ M : LogNorms F', M.IsAdelic → (Function.support M.finSum).Finite := fun M hM =>
    Set.Finite.subset hM fun ℓ hℓ => by
      by_contra hc
      simp only [Set.mem_setOf_eq, not_exists, not_not] at hc
      exact hℓ (by simp [LogNorms.finSum, hc])
  have hsplit : N'.deg = N.deg + ∑ ℓ ∈ bad, extP g ℓ := by
    rw [hBs, ← hext]
    simp only [extendFromPrimes_coe, g]
    have e1 : ∑ᶠ ℓ, (N'.finSum ℓ - (N.ext ι).finSum ℓ) = ∑ ℓ ∈ B, (N'.finSum ℓ - (N.ext ι).finSum ℓ) := by
      refine finsum_eq_sum_of_support_subset _ fun ℓ hℓ => ?_
      by_contra hc
      refine hℓ (sub_eq_zero.2 (Finset.sum_congr rfl fun κ' _ => ?_))
      exact (hl ℓ κ').1 fun h => hc ((hB ℓ).2 h)
    rw [finsum_sub_distrib (hsupp _ hAd') (hsupp _ hAdx)] at e1
    rw [← Finset.sum_div, Finset.sum_neg_distrib, ← e1]
    have e2 : ∑ s, N'.inf s = ∑ s, (N.ext ι).inf s := rfl
    simp only [LogNorms.deg]
    rw [e2]
    ring
  rw [hsplit]
  have hrd : hostRd E = rootDiscr E := OnHodge.hostRd_eq E
  refine near_of (p + q) bad h2 _ _ _ _ (extP fun ℓ => w ℓ / Module.finrank ℚ E / Real.log (ℓ : ℕ)) ?_ ?_ ?_
  · rw [hdeg]
    refine value_bound p q _ _ ?_
    have h7 : (7 : ℝ) ≤ H.d := by
      have := H.d_mod
      have : 7 ≤ H.d := by omega
      exact_mod_cast this
    have h1 := (GlobalTheory.T.sqrt_discriminant_bounds_cm_field E H).2
    rw [hrd, ← Real.log_sqrt (by norm_num)]
    exact Real.log_le_log (Real.sqrt_pos.2 (by norm_num)) ((Real.sqrt_le_sqrt h7).trans h1)
  · intro n hn
    obtain ⟨ℓ, rfl⟩ : ∃ ℓ : Nat.Primes, (ℓ : ℕ) = n := ⟨⟨n, hbp n hn⟩, rfl⟩
    rw [extendFromPrimes_coe, extendFromPrimes_coe]
    refine ⟨div_nonneg (div_nonneg (hw0 ℓ) hnE.le) (hlog ℓ).le, ?_⟩
    have hk : ∀ κ' : F' →+* ℂ_[ℓ], |N'.fin ℓ κ' - (N.ext ι).fin ℓ κ'| ≤ ((p + q : ℕ) : ℝ) * (cP ℓ * Real.log (ℓ : ℕ) -
        logIdeal ((κ'.comp f).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))) := fun κ' => by
      obtain ⟨a, ha, ha0, -, e⟩ := GlobalTheory.T.padic_logIdeal_max_element E ℓ ((κ'.comp f).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))
        ((κ'.comp f).injective.comp RingOfIntegers.coe_injective) differentIdeal_ne_bot
      rw [e, RingHom.comp_apply, RingHom.comp_apply, hf]
      exact (hl ℓ κ').2 hn a ha ha0
    have hfib := GlobalTheory.T.sum_embeddings_base_change E F' ℂ_[ℓ] f
      fun j => logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))
    have hs : |N'.finSum ℓ - (N.ext ι).finSum ℓ| ≤ ((p + q : ℕ) : ℝ) * (Module.finrank ℚ F' * (cP ℓ * Real.log (ℓ : ℕ)) -
        ∑ κ' : F' →+* ℂ_[ℓ], logIdeal ((κ'.comp f).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))) := by
      simp only [LogNorms.finSum]
      rw [← Finset.sum_sub_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun κ' _ => hk κ').trans (le_of_eq ?_))
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Embeddings.card, nsmul_eq_mul]
    have hS : ∑ κ' : F' →+* ℂ_[ℓ], logIdeal ((κ'.comp f).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) =
        -(Module.finrank ℚ F' * (w ℓ / Module.finrank ℚ E)) := by
      apply mul_left_cancel₀ hnE.ne'
      rw [hfib]
      simp only [w]
      field_simp
    rw [hS] at hs
    simp only [g]
    rw [abs_div, abs_neg, abs_of_pos hn', div_le_iff₀ hn']
    refine hs.trans (le_of_eq ?_)
    have := (hlog ℓ).ne'
    field_simp
    ring
  · rw [hBs]
    simp only [extendFromPrimes_coe]
    obtain ⟨hfin, hsum⟩ := GlobalTheory.T.different_ideal_log_sum_root_discriminant E
    have hwf : (Function.support w).Finite := hfin.subset fun ℓ hℓ => fun h => hℓ (by simp only [w]; rw [h, neg_zero])
    have hws : ∑ᶠ ℓ, w ℓ = Module.finrank ℚ E * Real.log (rootDiscr E) := by
      simp only [w]
      rw [finsum_neg_distrib, hsum]
      ring
    have hle : ∑ ℓ ∈ B, w ℓ ≤ ∑ᶠ ℓ, w ℓ := by
      rw [finsum_eq_sum_of_support_subset w (s := B ∪ hwf.toFinset) (fun ℓ hℓ => by simp [hℓ])]
      exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left fun ℓ _ _ => hw0 ℓ
    rw [Finset.sum_congr rfl fun ℓ _ => div_mul_cancel₀ _ (hlog ℓ).ne', ← Finset.sum_div, div_le_iff₀ hnE, hrd]
    linarith

end RootFieldNumerics.RF
