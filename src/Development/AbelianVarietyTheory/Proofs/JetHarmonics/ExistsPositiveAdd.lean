module

public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.SplitUnramifiedPlaces
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsIsKroneckerCharOfDiscr
public import Development.AbelianVarietyTheory.Definitions.Jets.PowerSeriesHasSumAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPositiveAdd
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LeastExponentCompare
open NumberField NumberField.IsCMField TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace

set_option autoImplicit false in
theorem _root_.GlobalTheory.LeastExponentCompare.isCMField_of_conj (E : Type) [Field E] [NumberField E] (cj : E → E)
    (h : ∀ (φ : E →+* ℂ) (z : E), φ (cj z) = star (φ z)) (hne : ∃ z : E, cj z ≠ z) :
    IsCMField E := by
  let φ₀ : E →+* ℂ := (Classical.arbitrary (InfinitePlace E)).embedding
  have inj := φ₀.injective
  have hadd : ∀ a b, cj (a + b) = cj a + cj b := fun a b =>
    inj (by rw [h, map_add (f := _), map_add (f := _), h, h, star_add])
  have hmul : ∀ a b, cj (a * b) = cj a * cj b := fun a b =>
    inj (by rw [h, map_mul, map_mul, h, h, star_mul'])
  have hinv : ∀ z, cj (cj z) = z := fun z => inj (by rw [h, h, star_star])
  let e : E ≃+* E :=
    { toFun := cj, invFun := cj, left_inv := hinv, right_inv := hinv,
      map_mul' := hmul, map_add' := hadd }
  let σ : E ≃ₐ[ℚ] E := e.toRatAlgEquiv
  have hσ : ∀ z, σ z = cj z := fun _ => rfl
  have hsq : σ ^ 2 = 1 := AlgEquiv.ext fun z => by
    rw [pow_two, AlgEquiv.mul_apply, hσ, hσ, hinv, AlgEquiv.one_apply]
  have hne1 : σ ≠ 1 := by
    obtain ⟨z, hz⟩ := hne
    intro h1
    exact hz (by rw [← hσ, h1, AlgEquiv.one_apply])
  have hord : orderOf σ = 2 := orderOf_eq_prime hsq hne1
  have hfix : ∀ x, x ∈ IntermediateField.fixedField (Subgroup.zpowers σ) ↔ cj x = x := by
    intro x
    rw [IntermediateField.mem_fixedField_iff]
    refine ⟨fun hx => hx σ (Subgroup.mem_zpowers σ), fun hx f hf => ?_⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hf
    clear hf
    have hσx : σ x = x := hx
    have hσx' : σ⁻¹ x = x := by
      calc σ⁻¹ x = (σ⁻¹ * σ) x := by rw [AlgEquiv.mul_apply, hσx]
        _ = x := by rw [inv_mul_cancel, AlgEquiv.one_apply]
    induction n using Int.induction_on with
    | zero => simp
    | succ k ih => rw [zpow_add_one, AlgEquiv.mul_apply, hσx, ih]
    | pred k ih => rw [zpow_sub_one, AlgEquiv.mul_apply, hσx', ih]
  have hS : maximalRealSubfield E =
      (IntermediateField.fixedField (Subgroup.zpowers σ)).toSubfield := by
    ext x
    rw [mem_maximalRealSubfield_iff, IntermediateField.mem_toSubfield, hfix]
    exact ⟨fun hx => inj ((h φ₀ x).trans (hx φ₀)), fun hx φ => by rw [← h φ x, hx]⟩
  have hfin : Module.finrank (maximalRealSubfield E) E = 2 := by
    rw [hS]
    exact (IntermediateField.finrank_fixedField_eq_card (Subgroup.zpowers σ)).trans
      (by rw [Nat.card_zpowers, hord])
  haveI : IsTotallyComplex E := ⟨fun v => InfinitePlace.not_isReal_iff_isComplex.mp fun hv => by
    rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff] at hv
    obtain ⟨z, hz⟩ := hne
    exact hz (v.embedding.injective ((h _ z).trans (RingHom.congr_fun hv z)))⟩
  haveI : Algebra.IsQuadraticExtension (maximalRealSubfield E) E := ⟨hfin⟩
  exact ⟨⟩

set_option autoImplicit false in
theorem _root_.GlobalTheory.LeastExponentCompare.conj_iff (E : Type) [Field E] [NumberField E]
    (cj : E → E) :
    ((∀ (φ : E →+* ℂ) (z : E), φ (cj z) = star (φ z)) ∧ ∃ z : E, cj z ≠ z) ↔
      ∃ _ : IsCMField E, cj = fun z => complexConj E z := by
  constructor
  · rintro ⟨h, hne⟩
    haveI := _root_.GlobalTheory.LeastExponentCompare.isCMField_of_conj E cj h hne
    refine ⟨this, funext fun z => ?_⟩
    let φ₀ : E →+* ℂ := (Classical.arbitrary (InfinitePlace E)).embedding
    exact φ₀.injective (by rw [h, complexEmbedding_complexConj, RCLike.star_def])
  · rintro ⟨_, rfl⟩
    refine ⟨fun φ z => by rw [complexEmbedding_complexConj, RCLike.star_def], ?_⟩
    by_contra hall
    push_neg at hall
    exact complexConj_ne_one E (AlgEquiv.ext hall)

section Comparison₂
variable {Y : Type} [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y]

def IntegralAreSums (S : Submodule ℝ (Bil Y)) : Prop :=
  ∀ l : S →ₗ[ℝ] ℝ, (∀ β : S, (∀ a c, ∃ z : ℤ, (β : Bil Y) a c = z) → ∃ z : ℤ, l β = z) →
    ∃ (m : ℕ) (x x' : Fin m → Y), ∀ β : S, l β = ∑ i, (β : Bil Y) (x i) (x' i)

end Comparison₂

section AtLattice
variable (E : Type) [Field E] [NumberField E] {Y : Type} [AddCommGroup Y] [Module (𝓞 E) Y]

variable [IsCMField E]

end AtLattice

section Families

abbrev SpaceRule : Type 1 :=
  ∀ (E : Type) [Field E] [NumberField E] (_ : E → E) (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y],
    Submodule ℝ (Bil Y)

abbrev ValueRule (S : SpaceRule) : Type 1 :=
  ∀ (E : Type) [Field E] [NumberField E] (cj : E → E) (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y],
    S E cj Y → ℝ

variable {S : SpaceRule} {φ : ValueRule S}

end Families

end GlobalTheory.LeastExponentCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuadraticFieldDiscPrimeThreeModFour
open NumberField IntermediateField Polynomial

namespace GlobalTheory

theorem _root_.GlobalTheory.sqrtNeg_not_mem_range {K : Type*} [Field K] [CharZero K] [Algebra ℚ K]
    (q : ℕ) (hq : 0 < q) (x : K) (hx : x ^ 2 = -(q : K)) : x ∉ (algebraMap ℚ K).range := by
  rintro ⟨r, rfl⟩
  have hr : r ^ 2 = -(q : ℚ) := by
    apply (algebraMap ℚ K).injective
    rw [map_pow, map_neg, map_natCast]
    exact hx
  have hq' : (0 : ℚ) < q := by exact_mod_cast hq
  nlinarith [sq_nonneg r]

theorem _root_.GlobalTheory.minpoly_eq_of_quadratic_irrational {K : Type*} [Field K] [Algebra ℚ K]
    (p : ℚ[X]) (hm : p.Monic) (hd : p.natDegree = 2) (x : K) (hx : aeval x p = 0)
    (hr : x ∉ (algebraMap ℚ K).range) : p = minpoly ℚ x := by
  have hint : IsIntegral ℚ x := ⟨p, hm, by rwa [aeval_def] at hx⟩
  have hdvd : minpoly ℚ x ∣ p := minpoly.dvd ℚ x hx
  have hpos := minpoly.natDegree_pos hint
  have hne : (minpoly ℚ x).natDegree ≠ 1 := fun h => hr (minpoly.natDegree_eq_one_iff.1 h)
  exact Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hm hdvd (by omega)

theorem _root_.GlobalTheory.natAbs_discr_of_sq_eq_neg_prime (K : Type*) [Field K] [NumberField K] (q : ℕ)
    (hq : q.Prime) (h4 : q % 4 = 3) (x : K) (hx : x ^ 2 = -(q : K))
    (hK : Module.finrank ℚ K = 2) : (NumberField.discr K).natAbs = q := by
  obtain ⟨B, t, n, h0, h1, hd⟩ := _root_.GlobalTheory.QuadraticZeta.exists_basis hK
  obtain ⟨m, hm⟩ : ∃ m : ℕ, q + 1 = 4 * m := ⟨(q + 1) / 4, by omega⟩
  have hxi : IsIntegral ℤ x :=
    ⟨X ^ 2 + C (q : ℤ), monic_X_pow_add_C _ two_ne_zero, by simp [hx]⟩
  have hyi : IsIntegral ℤ ((1 + x) / 2) := by
    refine ⟨X ^ 2 - X + C (m : ℤ), by monicity!, ?_⟩
    have hmK : (4 : K) * m = q + 1 := by exact_mod_cast hm.symm
    simp
    linear_combination (1 / 4 : K) * hx + (1 / 4 : K) * hmK
  obtain ⟨X0, hX0⟩ : ∃ X0 : 𝓞 K, algebraMap (𝓞 K) K X0 = x := ⟨⟨x, hxi⟩, rfl⟩
  obtain ⟨Y0, hY0⟩ : ∃ Y0 : 𝓞 K, algebraMap (𝓞 K) K Y0 = (1 + x) / 2 :=
    ⟨⟨(1 + x) / 2, hyi⟩, rfl⟩
  have hXY : X0 = (2 : ℤ) • Y0 - B 0 := by
    rw [h0, zsmul_eq_mul]
    apply FaithfulSMul.algebraMap_injective (𝓞 K) K
    simp only [map_sub, map_mul, map_intCast, map_one, Int.cast_ofNat, map_ofNat]
    rw [hX0, hY0]
    ring
  have hsq : X0 ^ 2 = -(q : 𝓞 K) := by
    apply RingOfIntegers.ext
    simp only [map_pow, map_neg, map_natCast]
    rw [hX0, hx]
  have hb : B.repr X0 1 = 2 * B.repr Y0 1 := by
    rw [hXY, map_sub, map_zsmul, Finsupp.sub_apply, Finsupp.smul_apply, B.repr_self,
      smul_eq_mul]
    simp
  have hX := B.sum_repr X0
  rw [Fin.sum_univ_two] at hX
  generalize B.repr X0 0 = a at hX
  generalize B.repr X0 1 = c at hX hb
  generalize B.repr Y0 1 = e at hb
  subst hb
  have hli : LinearIndependent ℤ ![B 0, B 1] := by
    convert B.linearIndependent
    ext i
    fin_cases i <;> rfl
  obtain ⟨k1, k2⟩ := LinearIndependent.pair_iff.1 hli (a ^ 2 - (2 * e) ^ 2 * n + q)
    (2 * a * (2 * e) + (2 * e) ^ 2 * t) (by
      simp only [zsmul_eq_mul] at hX ⊢
      rw [h0] at hX ⊢
      push_cast at hX ⊢
      linear_combination ((a : 𝓞 K) * 1 + 2 * (e : 𝓞 K) * B 1 + X0) * hX + hsq
        + (-(2 * (e : 𝓞 K)) ^ 2) * h1)
  have he : e ≠ 0 := by
    rintro rfl
    apply _root_.GlobalTheory.sqrtNeg_not_mem_range q hq.pos x hx
    refine ⟨(a : ℚ), ?_⟩
    have hc := congrArg (algebraMap (𝓞 K) K) hX
    simp only [zero_smul, add_zero, zsmul_eq_mul, h0, mul_one, map_intCast] at hc
    rw [hX0] at hc
    simpa using hc
  have h2 : 2 * a + 2 * e * t = 0 := by
    have h' : (2 * e) * (2 * a + 2 * e * t) = 0 := by linear_combination k2
    rcases mul_eq_zero.1 h' with h | h
    · omega
    · exact h
  have h3 : a + e * t = 0 := by linarith
  have hD : e ^ 2 * discr K = -q := by
    rw [hd]
    linear_combination (e * t - a) * h3 + k1
  have hN := congrArg Int.natAbs hD
  rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_neg, Int.natAbs_natCast] at hN
  have hdvd : e.natAbs ^ 2 ∣ q := ⟨_, hN.symm⟩
  rcases hq.eq_one_or_self_of_dvd _ hdvd with h | h
  · rw [h, one_mul] at hN
    exact hN
  · exfalso
    have hp : (e.natAbs * e.natAbs).Prime := by rw [← sq, h]; exact hq
    rcases Nat.prime_mul_iff.1 hp with ⟨hp', he1⟩ | ⟨hp', he1⟩ <;>
      simp [he1, Nat.not_prime_one] at hp'

theorem isGalois_finrank_discr_adjoin_sqrt_neg_prime :
    ∀ (q : ℕ) (x : ℂ), q.Prime → q % 4 = 3 → x ^ 2 = -(q : ℂ) → ∀ [NumberField ℚ⟮x⟯],
      IsGalois ℚ ℚ⟮x⟯ ∧ Module.finrank ℚ ℚ⟮x⟯ = 2 ∧ (NumberField.discr ℚ⟮x⟯).natAbs = q := by
  intro q x hq h4 hx _
  have hpm : (X ^ 2 + C (q : ℚ)).Monic := by monicity!
  have hpd : (X ^ 2 + C (q : ℚ)).natDegree = 2 := by compute_degree!
  have h0 : aeval x (X ^ 2 + C (q : ℚ)) = 0 := by simp [hx]
  have hmin := minpoly_eq_of_quadratic_irrational _ hpm hpd x h0
    (sqrtNeg_not_mem_range q hq.pos x hx)
  have hfin : Module.finrank ℚ ℚ⟮x⟯ = 2 := by
    have := IntermediateField.adjoin.finrank (K := ℚ) (x := x) ⟨_, hpm, h0⟩
    rw [← hmin, hpd] at this
    exact this
  have : Algebra.IsQuadraticExtension ℚ ℚ⟮x⟯ := ⟨hfin⟩
  refine ⟨Algebra.IsQuadraticExtension.isGalois _ _, hfin, ?_⟩
  refine natAbs_discr_of_sq_eq_neg_prime ℚ⟮x⟯ q hq h4 (AdjoinSimple.gen ℚ x) ?_ hfin
  apply Subtype.ext
  simpa using hx

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormalGroupNatMulSeriesProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormalGroupNatMulSeriesProperties
noncomputable section

namespace GlobalTheory.ConvSer

open MvPowerSeries Finsupp

theorem _root_.GlobalTheory.ConvSer.nMul_hasSubst_pair {R : Type*} [CommRing R] {f g : PowerSeries R}
    (hf : PowerSeries.constantCoeff f = 0) (hg : PowerSeries.constantCoeff g = 0) :
    MvPowerSeries.HasSubst (![f, g] : Fin 2 → MvPowerSeries Unit R) := by
  refine hasSubst_of_constantCoeff_zero fun s => ?_
  fin_cases s
  · exact hf
  · exact hg

theorem _root_.GlobalTheory.ConvSer.nMul_constantCoeff {R : Type*} [CommRing R] (F : FormalGroup R)
    (n : ℕ) : PowerSeries.constantCoeff (_root_.GlobalTheory.ConvSer.nMul F n) = 0 := by
  induction n with
  | zero => simp [_root_.GlobalTheory.ConvSer.nMul_zero]
  | succ n ih =>
    rw [_root_.GlobalTheory.ConvSer.nMul_succ]
    refine constantCoeff_subst_eq_zero
      (_root_.GlobalTheory.ConvSer.nMul_hasSubst_pair ih PowerSeries.constantCoeff_X) (fun s => ?_) F.2
    fin_cases s
    · exact ih
    · exact PowerSeries.constantCoeff_X

theorem nMul_hasSubst {R : Type*} [CommRing R] (F : FormalGroup R) (n : ℕ) :
    PowerSeries.HasSubst (nMul F n) :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (nMul_constantCoeff F n)

theorem coeff_one_formalGroup_subst {R : Type*} [CommRing R] (F : FormalGroup R)
    {f g : PowerSeries R}
    (hf : PowerSeries.constantCoeff f = 0) (hg : PowerSeries.constantCoeff g = 0) :
    PowerSeries.coeff 1 (MvPowerSeries.subst (![f, g] : Fin 2 → MvPowerSeries Unit R)
      F.toPowerSeries) = PowerSeries.coeff 1 f + PowerSeries.coeff 1 g := by
  have hne : (single 0 1 : Fin 2 →₀ ℕ) ≠ single 1 1 := by
    intro h
    have := DFunLike.congr_fun h 0
    simp at this
  have key : ∀ d : Fin 2 →₀ ℕ, (d.prod fun s e => (![f, g] : Fin 2 → MvPowerSeries Unit R) s ^ e)
      = (f ^ d 0 * g ^ d 1 : PowerSeries R) := by
    intro d
    rw [Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]
    rfl
  have hc : ∀ h : PowerSeries R, MvPowerSeries.coeff (single () 1) h = PowerSeries.coeff 1 h :=
    fun _ => rfl
  rw [← hc, coeff_subst (nMul_hasSubst_pair hf hg),
    finsum_eq_sum_of_support_subset (s := {single 0 1, single 1 1})]
  · rw [Finset.sum_pair hne, key, key, hc, hc, F.lin_coeff_X, F.lin_coeff_Y]
    simp
  · intro d hd
    by_contra hn
    apply hd
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff,
      not_or] at hn
    have h2 : d 0 + d 1 = 0 ∨ 2 ≤ d 0 + d 1 := by
      by_contra hh
      have : (d 0 = 1 ∧ d 1 = 0) ∨ (d 0 = 0 ∧ d 1 = 1) := by omega
      rcases this with h | h
      · apply hn.1
        ext s
        fin_cases s <;> simp [h]
      · apply hn.2
        ext s
        fin_cases s <;> simp [h]
    have h0 : PowerSeries.coeff 1 (f ^ d 0 * g ^ d 1) = 0 := by
      rcases h2 with h | h
      · have h0 : d 0 = 0 := by omega
        have h1 : d 1 = 0 := by omega
        simp [h0, h1, PowerSeries.coeff_one]
      · have hd : (PowerSeries.X : PowerSeries R) ^ (d 0 + d 1) ∣ f ^ d 0 * g ^ d 1 := by
          rw [pow_add]
          exact mul_dvd_mul (pow_dvd_pow_of_dvd (PowerSeries.X_dvd_iff.2 hf) _)
            (pow_dvd_pow_of_dvd (PowerSeries.X_dvd_iff.2 hg) _)
        exact PowerSeries.X_pow_dvd_iff.1 hd 1 (by omega)
    show _ • _ = _
    rw [key, hc, h0, smul_zero]

theorem nMul_coeff_one {R : Type*} [CommRing R] (F : FormalGroup R) (n : ℕ) :
    PowerSeries.coeff 1 (nMul F n) = (n : R) := by
  induction n with
  | zero => simp [nMul_zero]
  | succ n ih =>
    rw [nMul_succ, coeff_one_formalGroup_subst F (nMul_constantCoeff F n)
      PowerSeries.constantCoeff_X, ih]
    simp

theorem nMul_one {R : Type*} [CommRing R] (F : FormalGroup R) : nMul F 1 = PowerSeries.X := by
  rw [nMul_succ, nMul_zero]
  exact F.zeroX_eq_X

theorem nMul_add {R : Type*} [CommRing R] (F : FormalGroup R) (i j : ℕ) :
    MvPowerSeries.subst (![nMul F i, nMul F j] : Fin 2 → MvPowerSeries Unit R) F.toPowerSeries
      = nMul F (i + j) := by
  induction j with
  | zero => exact F.add_zero (nMul_hasSubst F i)
  | succ j ih =>
    rw [← add_assoc, nMul_succ, nMul_succ, ← ih]
    exact (F.assoc' (nMul_hasSubst F i) (nMul_hasSubst F j) PowerSeries.HasSubst.X').symm

theorem nMul_subst_nMul {R : Type*} [CommRing R] (F : FormalGroup R) (i j : ℕ) :
    (nMul F i).subst (nMul F j) = nMul F (i * j) := by
  induction i with
  | zero =>
    rw [zero_mul, nMul_zero, ← PowerSeries.coe_substAlgHom (nMul_hasSubst F j), map_zero]
  | succ i ih =>
    rw [add_mul, one_mul, ← nMul_add F (i * j) j, nMul_succ F i, PowerSeries.subst,
      subst_comp_subst_apply
        (nMul_hasSubst_pair (nMul_constantCoeff F i) PowerSeries.constantCoeff_X)
        (nMul_hasSubst F j).const]
    congr! 2 with s
    fin_cases s
    · exact ih
    · exact PowerSeries.subst_X (nMul_hasSubst F j)

private theorem coeff_one_subst_pair_X {R : Type*} [CommRing R] (F : FormalGroup R)
    {f : PowerSeries R} (hf : PowerSeries.constantCoeff f = 0) :
    PowerSeries.coeff 1 (MvPowerSeries.subst (![f, PowerSeries.X] : Fin 2 → MvPowerSeries Unit R)
      F.toPowerSeries : PowerSeries R) = PowerSeries.coeff 1 f + 1 := by
  have ha := _root_.GlobalTheory.ConvSer.nMul_hasSubst_pair hf PowerSeries.constantCoeff_X
  obtain ⟨g, rfl⟩ := PowerSeries.X_dvd_iff.mpr hf
  have hprod : ∀ d : Fin 2 →₀ ℕ, (d.prod fun s e => (![PowerSeries.X * g, PowerSeries.X] :
      Fin 2 → MvPowerSeries Unit R) s ^ e) = PowerSeries.X ^ (d 0 + d 1) * g ^ d 0 := by
    intro d
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
    show (PowerSeries.X * g) ^ d 0 * PowerSeries.X ^ d 1 = _
    ring
  have hcoeff : ∀ h : PowerSeries R, MvPowerSeries.coeff (single () 1) h = PowerSeries.coeff 1 h :=
    fun _ => rfl
  have hne : (single 0 1 : Fin 2 →₀ ℕ) ≠ single 1 1 := by
    intro h
    have := congrArg (fun d => d 0) h
    simp at this
  show MvPowerSeries.coeff (single () 1) _ = _
  rw [coeff_subst ha, finsum_eq_sum_of_support_subset (s := {single 0 1, single 1 1}),
    Finset.sum_pair hne]
  · simp only [hprod, hcoeff, F.3, F.4]
    simp
  · intro d hd
    simp only [Function.mem_support, hprod, hcoeff, PowerSeries.coeff_X_pow_mul'] at hd
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    by_cases h2 : d 0 + d 1 ≤ 1
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h2 with h | h
      · exfalso
        apply hd
        have hd0 : d = 0 := Finsupp.ext fun i => by fin_cases i <;> simp <;> omega
        simp [hd0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, F.2]
      · have h0 : d 0 ≤ 1 := by omega
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h0 with h0 | h0
        · right
          ext i
          fin_cases i <;> simp <;> omega
        · left
          ext i
          fin_cases i <;> simp <;> omega
    · exact absurd (by simp [h2]) hd

theorem _root_.GlobalTheory.ConvSer.nMul_props : ∀ (R : Type) [CommRing R] (F : FormalGroup R), (∀ n, PowerSeries.constantCoeff (_root_.GlobalTheory.ConvSer.nMul F n) = 0 ∧ PowerSeries.coeff 1 (_root_.GlobalTheory.ConvSer.nMul F n) = (n : R)) ∧ _root_.GlobalTheory.ConvSer.nMul F 1 = PowerSeries.X ∧ (∀ i j, MvPowerSeries.subst (![_root_.GlobalTheory.ConvSer.nMul F i, _root_.GlobalTheory.ConvSer.nMul F j] : Fin 2 → MvPowerSeries Unit R) F.toPowerSeries = _root_.GlobalTheory.ConvSer.nMul F (i + j)) ∧ (∀ i j, (_root_.GlobalTheory.ConvSer.nMul F i).subst (_root_.GlobalTheory.ConvSer.nMul F j) = _root_.GlobalTheory.ConvSer.nMul F (i * j)) ∧ (∀ (S : Type) [CommRing S] (φ : R →+* S) (n : ℕ), PowerSeries.map φ (_root_.GlobalTheory.ConvSer.nMul F n) = _root_.GlobalTheory.ConvSer.nMul (F.map φ) n) := by
  intro R _ F
  have hc := _root_.GlobalTheory.ConvSer.nMul_constantCoeff F
  have hs : ∀ n, PowerSeries.HasSubst (_root_.GlobalTheory.ConvSer.nMul F n) :=
    fun n => PowerSeries.HasSubst.of_constantCoeff_zero' (hc n)
  have hX : PowerSeries.HasSubst (PowerSeries.X : PowerSeries R) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' PowerSeries.constantCoeff_X
  have hadd : ∀ i j, MvPowerSeries.subst (![_root_.GlobalTheory.ConvSer.nMul F i,
      _root_.GlobalTheory.ConvSer.nMul F j] : Fin 2 → MvPowerSeries Unit R) F.toPowerSeries =
      _root_.GlobalTheory.ConvSer.nMul F (i + j) := by
    intro i j
    induction j with
    | zero =>
      rw [_root_.GlobalTheory.ConvSer.nMul_zero, Nat.add_zero]
      exact F.add_zero (hs i)
    | succ j ih =>
      rw [_root_.GlobalTheory.ConvSer.nMul_succ F j, show i + (j + 1) = (i + j) + 1 by omega,
        _root_.GlobalTheory.ConvSer.nMul_succ F (i + j), ← ih]
      exact (F.assoc' (hs i) (hs j) hX).symm
  refine ⟨fun n => ⟨hc n, ?_⟩, ?_, hadd, ?_, ?_⟩
  · induction n with
    | zero => simp [_root_.GlobalTheory.ConvSer.nMul_zero]
    | succ n ih =>
      rw [_root_.GlobalTheory.ConvSer.nMul_succ, coeff_one_subst_pair_X F (hc n), ih]
      push_cast
      rfl
  · rw [_root_.GlobalTheory.ConvSer.nMul_succ, _root_.GlobalTheory.ConvSer.nMul_zero]
    exact F.zero_add hX
  · intro i j
    induction i with
    | zero =>
      rw [_root_.GlobalTheory.ConvSer.nMul_zero, Nat.zero_mul, _root_.GlobalTheory.ConvSer.nMul_zero,
        ← PowerSeries.coe_substAlgHom (hs j), map_zero]
    | succ i ih =>
      rw [_root_.GlobalTheory.ConvSer.nMul_succ F i, Nat.succ_mul, ← hadd (i * j) j, ← ih]
      show MvPowerSeries.subst (fun _ => _root_.GlobalTheory.ConvSer.nMul F j) _ = _
      rw [MvPowerSeries.subst_comp_subst_apply
        (_root_.GlobalTheory.ConvSer.nMul_hasSubst_pair (hc i) PowerSeries.constantCoeff_X)
        (hasSubst_of_constantCoeff_zero fun _ => hc j)]
      congr 1
      funext s
      fin_cases s
      · rfl
      · exact PowerSeries.subst_X (hs j)
  · intro S _ φ n
    induction n with
    | zero => simp [_root_.GlobalTheory.ConvSer.nMul_zero]
    | succ n ih =>
      rw [_root_.GlobalTheory.ConvSer.nMul_succ, _root_.GlobalTheory.ConvSer.nMul_succ, FormalGroup.map_toPowerSeries,
        ← ih]
      show MvPowerSeries.map φ _ = _
      rw [MvPowerSeries.map_subst
        (_root_.GlobalTheory.ConvSer.nMul_hasSubst_pair (hc n) PowerSeries.constantCoeff_X)]
      congr 1
      funext s
      fin_cases s
      · rfl
      · exact PowerSeries.map_X φ

end GlobalTheory.ConvSer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormalGroupNatMulSeriesPropertiesStatement
open GlobalTheory.ConvSer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalGroupNatMulSeries_properties : ∀ (R : Type) [CommRing R] (F : FormalGroup R), (∀ n, PowerSeries.constantCoeff (nMul F n) = 0 ∧ PowerSeries.coeff 1 (nMul F n) = (n : R)) ∧ nMul F 1 = PowerSeries.X ∧ (∀ i j, MvPowerSeries.subst (![nMul F i, nMul F j] : Fin 2 → MvPowerSeries Unit R) F.toPowerSeries = nMul F (i + j)) ∧ (∀ i j, (nMul F i).subst (nMul F j) = nMul F (i * j)) ∧ (∀ (S : Type) [CommRing S] (φ : R →+* S) (n : ℕ), PowerSeries.map φ (nMul F n) = nMul (F.map φ) n) := by
  first | exact @GlobalTheory.ConvSer.nMul_props | exact GlobalTheory.ConvSer.nMul_props | (intros; apply GlobalTheory.ConvSer.nMul_props <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsUniqueMaximalAbovePlace
noncomputable section

open scoped TensorProduct

namespace GlobalTheory.OnePrime

open GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R]

theorem nontrivial_Ow (w : Place p R) : Nontrivial w.Ow := by
  apply Ideal.Quotient.nontrivial_iff.mpr
  intro h
  rw [Ideal.span_singleton_eq_top] at h
  have h1 : (1 - w.e) * (1 - w.e) = (1 - w.e) * 1 := by
    rw [mul_one]; exact w.idem.one_sub
  exact w.ne_zero (sub_eq_self.mp (h.mul_left_cancel h1))

theorem idem_Ow (w : Place p R) {d : w.Ow} (hd : IsIdempotentElem d) : d = 0 ∨ d = 1 := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective d
  have hx : x * x - x ∈ Ideal.span {1 - w.e} :=
    Ideal.Quotient.eq.mp (by rw [map_mul]; exact hd)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hx
  have hee : w.e * w.e = w.e := w.idem
  have he1 : Ideal.Quotient.mk (Ideal.span {1 - w.e}) w.e = 1 := by
    rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]
    exact Ideal.mem_span_singleton'.mpr ⟨-1, by ring⟩
  have hf : IsIdempotentElem (w.e * x) := by
    show w.e * x * (w.e * x) = w.e * x
    linear_combination (x * x - c) * hee - w.e * hc
  have hfe : w.e * x * w.e = w.e * x := by linear_combination x * hee
  have hmk : Ideal.Quotient.mk (Ideal.span {1 - w.e}) (w.e * x) =
      Ideal.Quotient.mk (Ideal.span {1 - w.e}) x := by
    rw [map_mul, he1, one_mul]
  rcases w.primitive _ hf hfe with h0 | h1
  · left
    rw [← hmk, h0, map_zero]
  · right
    rw [← hmk, h1, he1]

theorem maximal_unique [Module.Finite ℤ R] (w : Place p R) (M N : Ideal w.Ow) (hM : M.IsMaximal)
    (hN : N.IsMaximal) : N = M := by
  have : HenselianLocalRing ℤ_[p] := GlobalTheory.henselianLocalRing_of_henselianRing ℤ_[p]
  have := hM
  obtain ⟨d, hd, hmem⟩ := GlobalTheory.exists_idempotent_notMem_iff_of_henselian ℤ_[p] (S := w.Ow) M
  rcases idem_Ow w hd with rfl | rfl
  · exact absurd M.zero_mem ((hmem M hM).mpr rfl)
  · exact (hmem N hN).mp (fun h => hN.ne_top ((Ideal.eq_top_iff_one _).mpr h))

private theorem exists_eq_one_tmul_add_mul (x : Op p R) :
    ∃ (r : R) (t : Op p R), x = (1 : ℤ_[p]) ⊗ₜ r + (p : Op p R) * t := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul z r =>
    obtain ⟨n, -, hn⟩ := PadicInt.exists_mem_range (x := z)
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at hn
    obtain ⟨t, ht⟩ := hn
    refine ⟨(n : R) * r, t ⊗ₜ r, ?_⟩
    have hz : z = (n : ℤ_[p]) + t * p := by rw [ht]; ring
    have h1 : (n : ℤ_[p]) ⊗ₜ[ℤ] r = (1 : ℤ_[p]) ⊗ₜ ((n : R) * r) := by
      calc (n : ℤ_[p]) ⊗ₜ[ℤ] r = ((n : ℤ_[p]) ⊗ₜ[ℤ] (1 : R)) * ((1 : ℤ_[p]) ⊗ₜ r) := by
            rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        _ = (n : Op p R) * ((1 : ℤ_[p]) ⊗ₜ r) := by rw [Algebra.TensorProduct.natCast_def]
        _ = ((1 : ℤ_[p]) ⊗ₜ[ℤ] (n : R)) * ((1 : ℤ_[p]) ⊗ₜ r) := by
            rw [Algebra.TensorProduct.natCast_def']
        _ = (1 : ℤ_[p]) ⊗ₜ ((n : R) * r) := by rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    have h2 : (t * p) ⊗ₜ[ℤ] r = (p : Op p R) * (t ⊗ₜ r) := by
      rw [Algebra.TensorProduct.natCast_def, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm]
    rw [hz, TensorProduct.add_tmul, h1, h2]
  | add x y hx hy =>
    obtain ⟨r₁, t₁, h₁⟩ := hx
    obtain ⟨r₂, t₂, h₂⟩ := hy
    exact ⟨r₁ + r₂, t₁ + t₂, by rw [h₁, h₂, TensorProduct.tmul_add]; ring⟩

theorem exists_eq_add (w : Place p R) (s : w.Ow) :
    ∃ (r : R) (t : w.Ow), s = w.toOw r + (p : w.Ow) * t := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective s
  obtain ⟨r, t, h⟩ := exists_eq_one_tmul_add_mul x
  refine ⟨r, Ideal.Quotient.mk _ t, ?_⟩
  rw [h, map_add (f := _), map_mul, map_natCast]
  rfl

theorem exists_prime_under (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [IsDedekindDomain R]
    [CharZero R] [Module.Finite ℤ R] (w : GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces.Place p R) :
    ∃ P : Ideal R, P.IsMaximal ∧ (p : R) ∈ P ∧ (P.map w.toOw).IsMaximal ∧
      ∀ Q : Ideal R, Q.IsMaximal → Q ≠ P → Q.map w.toOw = ⊤ := by
  have : HenselianLocalRing ℤ_[p] := GlobalTheory.henselianLocalRing_of_henselianRing ℤ_[p]
  have : Nontrivial w.Ow := nontrivial_Ow w
  have : IsLocalRing w.Ow := by
    obtain ⟨M, hM⟩ := Ideal.exists_maximal w.Ow
    exact IsLocalRing.of_unique_max_ideal ⟨M, hM, fun N hN => maximal_unique w M N hM hN⟩
  set m := IsLocalRing.maximalIdeal w.Ow with hm
  set P := m.comap w.toOw with hP
  have hpm : (p : w.Ow) ∈ m := by
    have hc := GlobalTheory.comap_eq_maximalIdeal_of_finite (R := ℤ_[p]) (S := w.Ow) m
    have h0 : (p : ℤ_[p]) ∈ m.comap (algebraMap ℤ_[p] w.Ow) := by
      rw [hc, PadicInt.maximalIdeal_eq_span_p]
      exact Ideal.mem_span_singleton_self _
    rw [Ideal.mem_comap, map_natCast] at h0
    exact h0
  have hpP : (p : R) ∈ P := by
    rw [hP, Ideal.mem_comap, map_natCast]
    exact hpm
  have hPne : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hpP
    exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) hpP
  have : P.IsPrime := Ideal.comap_isPrime _ _
  have hPmax : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hPne
  have hmap : P.map w.toOw = m := by
    refine le_antisymm Ideal.map_comap_le fun s hs => ?_
    obtain ⟨r, t, rfl⟩ := exists_eq_add w s
    have hpt : (p : w.Ow) * t ∈ P.map w.toOw := by
      rw [← map_natCast w.toOw p]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hpP)
    have hr : w.toOw r ∈ m := by
      have h1 := m.sub_mem hs (m.mul_mem_right t hpm)
      rwa [add_sub_cancel_right] at h1
    exact Ideal.add_mem _ (Ideal.mem_map_of_mem _ (show r ∈ P from hr)) hpt
  refine ⟨P, hPmax, hpP, by rw [hmap]; infer_instance, fun Q hQ hQP => ?_⟩
  by_contra hne
  have hle : Q.map w.toOw ≤ m := IsLocalRing.le_maximalIdeal hne
  exact hQP (hQ.eq_of_le hPmax.ne_top fun q hq => hle (Ideal.mem_map_of_mem _ hq))

end GlobalTheory.OnePrime
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WignerExtremeNeZero
open Finset

namespace GlobalTheory.WigSh

theorem wigner_den_ne_zero {n : ℕ} (L : Fin (n+1) → ℤ) (l : Fin (n+1)) (hL : StrictAnti L) :
    (∏ j ∈ univ.erase l, ((L j : ℝ) - (L l : ℝ))) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro j hj
  have h1 : j ≠ l := (Finset.mem_erase.mp hj).1
  have h2 : L j ≠ L l := fun h => h1 (hL.injective h)
  exact sub_ne_zero.mpr (by exact_mod_cast h2)

theorem wigner_extreme_ne_zero : ∀ (n : ℕ) (L : Fin (n+1) → ℤ) (l : Fin (n+1)), StrictAnti L → ((∀ j, L j ≠ L l + 1) → GlobalTheory.WigSh.wP L (fun j : Fin n => L j.castSucc) l ≠ 0) ∧ ((∀ j, L j ≠ L l - 1) → GlobalTheory.WigSh.wM L (fun j : Fin n => L j.succ + 1) l ≠ 0) := by
  intro n L l hL
  refine ⟨fun h => ?_, fun h => ?_⟩
  · unfold wP
    refine div_ne_zero ?_ (wigner_den_ne_zero L l hL)
    rw [Finset.prod_ne_zero_iff]
    intro j _
    have h1 : L j.castSucc - 1 - L l ≠ 0 := by
      have := h j.castSucc
      omega
    exact_mod_cast h1
  · unfold wM
    refine div_ne_zero ?_ (wigner_den_ne_zero L l hL)
    rw [Finset.prod_ne_zero_iff]
    intro j _
    have h1 : L j.succ + 1 - L l ≠ 0 := by
      have := h j.succ
      omega
    exact_mod_cast h1

end GlobalTheory.WigSh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DifferentPowerUnramifiedIff
noncomputable section

open scoped TensorProduct

namespace GlobalTheory.Proof.different_power_unramified_iff

open GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces

private lemma eq_zero_of_natCast_mul_eq_zero_op (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    [IsDomain R] [CharZero R] [Module.Finite ℤ R] (z : Op p R) (hz : (p : Op p R) * z = 0) :
    z = 0 := by
  have hp := (Fact.out : p.Prime)
  have : Module.Free ℤ R := Module.free_of_finite_type_torsion_free'
  have hsmul : (p : ℤ_[p]) • z = 0 := by
    rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
    exact hz
  rcases smul_eq_zero.mp hsmul with h | h
  · exact absurd h (Nat.cast_ne_zero.mpr hp.ne_zero)
  · exact h

theorem ow_p_torsionFree (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [IsDomain R] [CharZero R]
    [Module.Finite ℤ R] (w : Place p R) (x : w.Ow) (hx : (p : w.Ow) * x = 0) : x = 0 := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hy : (p : Op p R) * y ∈ Ideal.span {1 - w.e} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_natCast]
    exact hx
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hy
  have hey : w.e * y = 0 := by
    apply eq_zero_of_natCast_mul_eq_zero_op p R
    have hee : w.e * w.e = w.e := w.idem
    calc (p : Op p R) * (w.e * y) = w.e * ((p : Op p R) * y) := by ring
      _ = w.e * (a * (1 - w.e)) := by rw [ha]
      _ = a * (w.e - w.e * w.e) := by ring
      _ = 0 := by rw [hee, sub_self, mul_zero]
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
  exact ⟨y, by rw [mul_sub, mul_one, mul_comm y, hey, sub_zero]⟩

theorem map_eq_top_of_coprime {R S : Type} [CommRing R] [IsDedekindDomain R] [CommRing S]
    (f : R →+* S) (P : Ideal R) (hP : P.IsMaximal)
    (h : ∀ Q : Ideal R, Q.IsMaximal → Q ≠ P → Q.map f = ⊤) (Q : Ideal R) (hQ : Q ≠ ⊥)
    (hPQ : P ⊔ Q = ⊤) : Q.map f = ⊤ := by
  by_contra hne
  obtain ⟨M, hM, hQM⟩ := Ideal.exists_le_maximal _ hne
  have hQ' : Q ≤ M.comap f := Ideal.map_le_iff_le_comap.mp hQM
  have hprime : (M.comap f).IsPrime := Ideal.comap_isPrime f M
  have hbot : M.comap f ≠ ⊥ := fun h => hQ (eq_bot_iff.mpr (h ▸ hQ'))
  have hmax : (M.comap f).IsMaximal := hprime.isMaximal hbot
  by_cases hPeq : M.comap f = P
  · apply hP.ne_top
    rw [← hPQ]
    exact (sup_eq_left.mpr (hPeq ▸ hQ')).symm
  · apply hM.ne_top
    rw [eq_top_iff, ← h _ hmax hPeq]
    exact Ideal.map_comap_le

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

end GlobalTheory.Proof.different_power_unramified_iff
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConvergentSubstOneVariableAndFormalAgreement
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConvergentSubstOneVariableAndFormalAgreement
noncomputable section

namespace GlobalTheory.ConvSer.Bridge

def unitExp : ℕ ≃ (Unit →₀ ℕ) where
  toFun n := Finsupp.single () n
  invFun ν := ν ()
  left_inv n := by simp
  right_inv ν := by ext; simp

variable {K : Type} [NormedField K]

theorem powerSeriesConvergentSubstMv_eq_mv {τ : Type} (s : MvPowerSeries τ K) (f : PowerSeries K) :
    csub1 s f = csub (fun _ : Unit => s) f := by
  ext μ
  change ∑' n : ℕ, PowerSeries.coeff n f * MvPowerSeries.coeff μ (s ^ n) =
    ∑' ν : Unit →₀ ℕ, MvPowerSeries.coeff ν f * MvPowerSeries.coeff μ (∏ i : Unit, s ^ ν i)
  rw [← unitExp.tsum_eq]
  refine tsum_congr fun n => ?_
  simp [unitExp]

theorem powerSeriesEvalTsum_eq_mvPowerSeriesEvalTsum (f : PowerSeries K) (t : K) : ev1 f t = ev f (fun _ : Unit => t) := by
  unfold ev1 ev
  rw [← unitExp.tsum_eq]
  refine tsum_congr fun n => ?_
  simp [unitExp]

theorem powerSeriesHasSumAt_iff_mvPowerSeriesHasSumAt (f : PowerSeries K) (t a : K) : PowerSeriesHasSumAt f t a ↔ HS f (fun _ : Unit => t) a := by
  unfold PowerSeriesHasSumAt HS
  rw [← unitExp.hasSum_iff]
  have h : (fun ν : Unit →₀ ℕ => MvPowerSeries.coeff ν f * ∏ i : Unit, t ^ ν i) ∘ unitExp =
      fun n : ℕ => PowerSeries.coeff n f * t ^ n := by
    funext n
    simp [unitExp]
  rw [h]

theorem csub_C {σ τ : Type} [Fintype σ] (S : MvPowerSeries σ K) (x : σ → K) :
    csub (fun i => (MvPowerSeries.C (x i) : MvPowerSeries τ K)) S = MvPowerSeries.C (ev S x) := by
  have hC : ∀ ν : σ →₀ ℕ, (∏ i, (MvPowerSeries.C (x i) : MvPowerSeries τ K) ^ ν i) =
      MvPowerSeries.C (∏ i, x i ^ ν i) := fun ν => by simp [map_prod, map_pow]
  ext μ
  change ∑' ν : σ →₀ ℕ, MvPowerSeries.coeff ν S *
      MvPowerSeries.coeff μ (∏ i, (MvPowerSeries.C (x i) : MvPowerSeries τ K) ^ ν i) = _
  simp only [hC]
  by_cases h : μ = 0
  · subst h
    simp only [MvPowerSeries.coeff_zero_C]
    rfl
  · simp only [MvPowerSeries.coeff_C_of_ne_zero h, mul_zero, tsum_zero]

theorem shift1_eq_csub (F : MvPowerSeries (Fin 2) K) (y : K) :
    shift1 F y = csub (![PowerSeries.X, PowerSeries.C y] : Fin 2 → MvPowerSeries Unit K) F := by
  ext m
  have hc : ∀ p : PowerSeries K, MvPowerSeries.coeff (unitExp m) p = PowerSeries.coeff m p :=
    fun p => by simp [unitExp]
  change PowerSeries.coeff m (shift1 F y) = ∑' ν : Fin 2 →₀ ℕ, MvPowerSeries.coeff ν F *
    MvPowerSeries.coeff (unitExp m)
      (∏ i, (![PowerSeries.X, PowerSeries.C y] : Fin 2 → MvPowerSeries Unit K) i ^ ν i)
  have hterm : ∀ ν : Fin 2 →₀ ℕ, MvPowerSeries.coeff ν F * MvPowerSeries.coeff (unitExp m)
      (∏ i, (![PowerSeries.X, PowerSeries.C y] : Fin 2 → MvPowerSeries Unit K) i ^ ν i) =
      MvPowerSeries.coeff ν F * (if m = ν 0 then y ^ ν 1 else 0) := by
    intro ν
    rw [hc, Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← map_pow, mul_comm (PowerSeries.X ^ _), PowerSeries.coeff_C_mul_X_pow]
  simp only [hterm]
  rw [shift1, PowerSeries.coeff_mk]
  have hinj : Function.Injective
      (fun b : ℕ => Finsupp.single (0 : Fin 2) m + Finsupp.single 1 b) := by
    intro b b' h
    have h1 := congrArg (fun ν : Fin 2 →₀ ℕ => ν 1) h
    simpa using h1
  have hsupp : Function.support
      (fun ν : Fin 2 →₀ ℕ => MvPowerSeries.coeff ν F * (if m = ν 0 then y ^ ν 1 else 0)) ⊆
      Set.range (fun b : ℕ => Finsupp.single (0 : Fin 2) m + Finsupp.single 1 b) := by
    intro ν hν
    have h0 : m = ν 0 := by
      by_contra h
      exact hν (by simp [h])
    refine ⟨ν 1, ?_⟩
    ext i
    fin_cases i <;> simp [h0]
  refine Eq.trans ?_ (hinj.tsum_eq hsupp)
  refine tsum_congr fun b => ?_
  simp

theorem csub_eq_subst {σ τ : Type} [Fintype σ] (a : σ → MvPowerSeries τ K)
    (S : MvPowerSeries σ K) (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) :
    csub a S = MvPowerSeries.subst a S := by
  have hs : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  ext μ
  rw [MvPowerSeries.coeff_subst hs, ← tsum_eq_finsum (L := SummationFilter.unconditional (σ →₀ ℕ))
    (MvPowerSeries.coeff_subst_finite hs S μ)]
  change ∑' ν : σ →₀ ℕ, MvPowerSeries.coeff ν S * MvPowerSeries.coeff μ (∏ i, a i ^ ν i) = _
  refine tsum_congr fun ν => ?_
  rw [smul_eq_mul, Finsupp.prod_fintype _ _ (fun i => pow_zero _)]

theorem powerSeriesConvergentSubstMv_eq_subst {τ : Type} (a : MvPowerSeries τ K) (f : PowerSeries K)
    (ha : MvPowerSeries.constantCoeff a = 0) : csub1 a f = f.subst a := by
  rw [powerSeriesConvergentSubstMv_eq_mv, csub_eq_subst _ _ (fun _ => ha)]
  rfl

theorem csub_bridge : ∀ (K : Type) [NormedField K], (∀ (τ : Type) (s : MvPowerSeries τ K) (f : PowerSeries K), csub1 s f = csub (fun _ : Unit => s) f) ∧ (∀ (f : PowerSeries K) (t : K), ev1 f t = ev f (fun _ : Unit => t)) ∧ (∀ (f : PowerSeries K) (t a : K), PowerSeriesHasSumAt f t a ↔ HS f (fun _ : Unit => t) a) ∧ (∀ (σ τ : Type) [Fintype σ] (S : MvPowerSeries σ K) (x : σ → K), csub (fun i => (MvPowerSeries.C (x i) : MvPowerSeries τ K)) S = MvPowerSeries.C (ev S x)) ∧ (∀ (F : MvPowerSeries (Fin 2) K) (y : K), shift1 F y = csub (![PowerSeries.X, PowerSeries.C y] : Fin 2 → MvPowerSeries Unit K) F) ∧ (∀ (σ τ : Type) [Fintype σ] (a : σ → MvPowerSeries τ K) (S : MvPowerSeries σ K), (∀ i, MvPowerSeries.constantCoeff (a i) = 0) → csub a S = MvPowerSeries.subst a S) ∧ (∀ (τ : Type) (a : MvPowerSeries τ K) (f : PowerSeries K), MvPowerSeries.constantCoeff a = 0 → csub1 a f = f.subst a) := by
  intro K _
  exact ⟨fun _ s f => powerSeriesConvergentSubstMv_eq_mv s f, fun f t => powerSeriesEvalTsum_eq_mvPowerSeriesEvalTsum f t, fun f t a => powerSeriesHasSumAt_iff_mvPowerSeriesHasSumAt f t a,
    fun _ _ _ S x => csub_C S x, fun F y => shift1_eq_csub F y,
    fun _ _ _ a S ha => csub_eq_subst a S ha, fun _ a f ha => powerSeriesConvergentSubstMv_eq_subst a f ha⟩

end GlobalTheory.ConvSer.Bridge
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConvergentSubstOneVariableAndFormalAgreementStatement
open GlobalTheory.ConvSer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.convergentSubst_oneVariable_and_formal_agreement : ∀ (K : Type) [NormedField K], (∀ (τ : Type) (s : MvPowerSeries τ K) (f : PowerSeries K), csub1 s f = csub (fun _ : Unit => s) f) ∧ (∀ (f : PowerSeries K) (t : K), ev1 f t = ev f (fun _ : Unit => t)) ∧ (∀ (f : PowerSeries K) (t a : K), PowerSeriesHasSumAt f t a ↔ HS f (fun _ : Unit => t) a) ∧ (∀ (σ τ : Type) [Fintype σ] (S : MvPowerSeries σ K) (x : σ → K), csub (fun i => (MvPowerSeries.C (x i) : MvPowerSeries τ K)) S = MvPowerSeries.C (ev S x)) ∧ (∀ (F : MvPowerSeries (Fin 2) K) (y : K), shift1 F y = csub (![PowerSeries.X, PowerSeries.C y] : Fin 2 → MvPowerSeries Unit K) F) ∧ (∀ (σ τ : Type) [Fintype σ] (a : σ → MvPowerSeries τ K) (S : MvPowerSeries σ K), (∀ i, MvPowerSeries.constantCoeff (a i) = 0) → csub a S = MvPowerSeries.subst a S) ∧ (∀ (τ : Type) (a : MvPowerSeries τ K) (f : PowerSeries K), MvPowerSeries.constantCoeff a = 0 → csub1 a f = f.subst a) := by
  first | exact @GlobalTheory.ConvSer.Bridge.csub_bridge | exact GlobalTheory.ConvSer.Bridge.csub_bridge | (intros; apply GlobalTheory.ConvSer.Bridge.csub_bridge <;> assumption)
end
end
