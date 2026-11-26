module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinsetSpanPrincipalCongruenceLevelFunction
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JTranslatesLevelAndScalarMod

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NatDegreeMinpolyLe
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.ValMax

variable {Ω : Type} [Field Ω]

theorem val_int_le_one (V : ValuationSubring Ω) (z : ℤ) : V.valuation (z : Ω) ≤ 1 :=
  V.valuation_le_one ⟨_, intCast_mem V z⟩

theorem val_nat_eq_one (V : ValuationSubring Ω) {q : ℕ} (hq : q.Prime)
    (hV : V.valuation (q : Ω) < 1) {n : ℕ} (hn : ¬ q ∣ n) : V.valuation (n : Ω) = 1 := by
  have hc : IsCoprime (q : ℤ) n :=
    Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hq).2 hn)
  obtain ⟨a, b, hab⟩ := hc
  have h1 : (a : Ω) * (q : Ω) + (b : Ω) * (n : Ω) = 1 := by
    have := congrArg (Int.cast : ℤ → Ω) hab
    push_cast at this
    exact this
  have hle : V.valuation (n : Ω) ≤ 1 := by simpa using val_int_le_one V (n : ℤ)
  by_contra hne
  have hlt : V.valuation (n : Ω) < 1 := lt_of_le_of_ne hle hne
  have ha : V.valuation ((a : Ω) * (q : Ω)) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_int_le_one V a)) hV
  have hb : V.valuation ((b : Ω) * (n : Ω)) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_int_le_one V b)) hlt
  have := V.valuation.map_add_lt ha hb
  rw [h1, map_one] at this
  exact lt_irrefl _ this

theorem val_nat_eq_pow (V : ValuationSubring Ω) {q : ℕ} (hq : q.Prime)
    (hV : V.valuation (q : Ω) < 1) {n : ℕ} (hn : n ≠ 0) :
    ∃ e : ℕ, V.valuation (n : Ω) = V.valuation (q : Ω) ^ e := by
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn q hq.ne_one
  refine ⟨e, ?_⟩
  push_cast
  rw [map_mul, map_pow, val_nat_eq_one V hq hV hm, mul_one]

variable [Algebra ℚ Ω]

theorem val_q_ne_zero (V : ValuationSubring Ω) {q : ℕ} (hq : q.Prime) :
    V.valuation (q : Ω) ≠ 0 := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  rw [Valuation.ne_zero_iff]
  exact Nat.cast_ne_zero.2 hq.ne_zero

theorem val_rat_eq_zpow (V : ValuationSubring Ω) {q : ℕ} (hq : q.Prime)
    (hV : V.valuation (q : Ω) < 1) {r : ℚ} (hr : r ≠ 0) :
    ∃ e : ℤ, V.valuation (algebraMap ℚ Ω r) = V.valuation (q : Ω) ^ e := by
  have h0 := val_q_ne_zero V hq
  obtain ⟨e1, h1⟩ := val_nat_eq_pow V hq hV (n := r.num.natAbs)
    (Int.natAbs_ne_zero.2 (Rat.num_ne_zero.2 hr))
  obtain ⟨e2, h2⟩ := val_nat_eq_pow V hq hV (n := r.den) r.den_nz
  have h3 : V.valuation ((r.num : ℤ) : Ω) = V.valuation (q : Ω) ^ e1 := by
    rw [← h1]
    rcases Int.natAbs_eq r.num with h | h
    · conv_lhs => rw [h]
      simp only [Int.cast_natCast]
    · conv_lhs => rw [h]
      simp only [Int.cast_neg, Int.cast_natCast, Valuation.map_neg]
  refine ⟨(e1 : ℤ) - e2, ?_⟩
  have h4 : algebraMap ℚ Ω r = ((r.num : ℤ) : Ω) / ((r.den : ℕ) : Ω) := by
    conv_lhs => rw [← Rat.num_div_den r]
    rw [map_div₀, map_intCast, map_natCast]
  rw [h4, map_div₀, h3, h2, zpow_sub₀ h0, zpow_natCast, zpow_natCast]

theorem val_pow_sub (V : ValuationSubring Ω) {q : ℕ} (hq : q.Prime)
    (hV : V.valuation (q : Ω) < 1) {x : Ω} (hx : x ≠ 0) {r s : ℚ} (hr : r ≠ 0) (hs : s ≠ 0)
    {i k : ℕ} (h : V.valuation (r • x ^ i) = V.valuation (s • x ^ (i + k))) :
    ∃ e : ℤ, V.valuation x ^ k = V.valuation (q : Ω) ^ e := by
  have h0 := val_q_ne_zero V hq
  obtain ⟨e1, h1⟩ := val_rat_eq_zpow V hq hV hr
  obtain ⟨e2, h2⟩ := val_rat_eq_zpow V hq hV hs
  have hx0 : V.valuation x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_mul, h1, h2, map_pow, map_pow, pow_add,
    mul_comm (V.valuation x ^ i), ← mul_assoc] at h
  have h3 := mul_right_cancel₀ (pow_ne_zero i hx0) h
  refine ⟨e1 - e2, ?_⟩
  rw [zpow_sub₀ h0, h3, mul_div_cancel_left₀ _ (zpow_ne_zero _ h0)]

theorem val_pow_eq_zpow (V : ValuationSubring Ω) {q : ℕ} (hq : q.Prime)
    (hV : V.valuation (q : Ω) < 1) {x : Ω} (hx : x ≠ 0) (hi : IsIntegral ℚ x) :
    ∃ k : ℕ, 0 < k ∧ k ≤ (minpoly ℚ x).natDegree ∧
      ∃ e : ℤ, V.valuation x ^ k = V.valuation (q : Ω) ^ e := by
  classical
  set p := minpoly ℚ x with hp
  set f : ℕ → Ω := fun i => p.coeff i • x ^ i with hf
  have hsum : ∑ i ∈ Finset.range (p.natDegree + 1), f i = 0 := by
    rw [← Polynomial.aeval_eq_sum_range]
    exact minpoly.aeval ℚ x
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image (Finset.range (p.natDegree + 1))
    (fun i => V.valuation (f i)) ⟨0, by simp⟩
  have hj0 : V.valuation (f j) ≠ 0 := by
    intro h
    have h1 := hmax p.natDegree (by simp)
    have h2 : f p.natDegree = x ^ p.natDegree := by
      have : p.coeff p.natDegree = 1 := (minpoly.monic hi).coeff_natDegree
      simp only [hf, this, one_smul]
    rw [h, h2, le_zero_iff, Valuation.zero_iff] at h1
    exact pow_ne_zero _ hx h1
  have hex : ∃ i ∈ Finset.range (p.natDegree + 1) \ {j}, ¬ V.valuation (f i) < V.valuation (f j) := by
    by_contra hcon
    push Not at hcon
    have := V.valuation.map_sum_eq_of_lt hj hcon
    rw [hsum, map_zero] at this
    exact hj0 this.symm
  obtain ⟨i, hi', hlt⟩ := hex
  rw [Finset.mem_sdiff, Finset.mem_singleton] at hi'
  have heq : V.valuation (f i) = V.valuation (f j) :=
    le_antisymm (hmax i hi'.1) (not_lt.1 hlt)
  have hcj : p.coeff j ≠ 0 := by
    intro h
    apply hj0
    simp only [hf, h, zero_smul, map_zero]
  have hci : p.coeff i ≠ 0 := by
    intro h
    apply hj0
    rw [← heq]
    simp only [hf, h, zero_smul, map_zero]
  have hi1 := Finset.mem_range.1 hi'.1
  have hj1 := Finset.mem_range.1 hj
  rcases lt_or_gt_of_ne hi'.2 with hij | hij
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij.le
    exact ⟨k, by omega, by omega, val_pow_sub V hq hV hx hci hcj heq⟩
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij.le
    exact ⟨k, by omega, by omega, val_pow_sub V hq hV hx hcj hci heq.symm⟩

theorem val_pow_factorial (V : ValuationSubring Ω) {q : ℕ} (hq : q.Prime)
    (hV : V.valuation (q : Ω) < 1) {x : Ω} (hx : x ≠ 0) (hi : IsIntegral ℚ x) {n : ℕ}
    (hn : (minpoly ℚ x).natDegree ≤ n) :
    ∃ e : ℤ, V.valuation x ^ n.factorial = V.valuation (q : Ω) ^ e := by
  obtain ⟨k, hk0, hk, e, he⟩ := val_pow_eq_zpow V hq hV hx hi
  obtain ⟨m, hm⟩ := Nat.dvd_factorial hk0 (hk.trans hn)
  exact ⟨e * m, by rw [hm, pow_mul, he, _root_.zpow_mul, zpow_natCast]⟩

theorem natDegree_minpoly_le {K L : Type} [Field K] [Field L] [Algebra K L]
    (F : IntermediateField K L) [FiniteDimensional K F] {x : L} (hx : x ∈ F) :
    (minpoly K x).natDegree ≤ Module.finrank K F := by
  have h1 : (minpoly K (⟨x, hx⟩ : F)).natDegree ≤ Module.finrank K F :=
    minpoly.natDegree_le _
  rwa [IntermediateField.minpoly_eq] at h1

theorem exists_max_valuation : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [Algebra.IsAlgebraic ℚ Ω] (F : IntermediateField ℚ Ω), FiniteDimensional ℚ F → ∀ (q : ℕ), q.Prime → ∀ V : ValuationSubring Ω, ((q : ℕ) : Ω) ∈ V.nonunits → ∀ (ι : Type) (a : ι → Ω) (c : Ω), c ≠ 0 → (∀ i, a i ∈ F) → (∀ i, c * a i ∈ V) → (∃ i, a i ≠ 0) → ∃ i, a i ≠ 0 ∧ ∀ i', V.valuation (a i') ≤ V.valuation (a i) := by
  intro Ω _ _ _ F hF q hq V hV ι a c hc haF hca hex
  rw [ValuationSubring.mem_nonunits_iff] at hV
  have h0 := val_q_ne_zero V hq
  have hpos : 0 < V.valuation (q : Ω) := zero_lt_iff.2 h0
  have hint : ∀ x : Ω, IsIntegral ℚ x := fun x =>
    (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).isIntegral
  set n := Module.finrank ℚ F + (minpoly ℚ c).natDegree with hn
  obtain ⟨e0, he0⟩ := val_pow_factorial V hq hV hc (hint c) (n := n) (by omega)
  have hall : ∀ i, a i ≠ 0 →
      ∃ e : ℤ, V.valuation (a i) ^ n.factorial = V.valuation (q : Ω) ^ e := by
    intro i hi
    refine val_pow_factorial V hq hV hi (hint _) ?_
    exact (natDegree_minpoly_le F (haF i)).trans (Nat.le_add_right _ _)
  obtain ⟨e, ⟨i, hi, he⟩, hmin⟩ := Int.exists_least_of_bdd
    (P := fun e : ℤ => ∃ i, a i ≠ 0 ∧ V.valuation (a i) ^ n.factorial = V.valuation (q : Ω) ^ e)
    ⟨-e0, by
      rintro z ⟨i, -, hz⟩
      have h1 : V.valuation (c * a i) ≤ 1 := V.valuation_le_one ⟨_, hca i⟩
      have h2 : V.valuation (c * a i) ^ n.factorial ≤ 1 := pow_le_one' h1 _
      rw [map_mul, mul_pow, he0, hz, ← zpow_add₀ h0, ← zpow_zero (V.valuation (q : Ω)),
        zpow_le_zpow_iff_right_of_lt_one₀ hpos hV] at h2
      omega⟩
    (by
      obtain ⟨i, hi⟩ := hex
      obtain ⟨e, he⟩ := hall i hi
      exact ⟨e, i, hi, he⟩)
  refine ⟨i, hi, fun i' => ?_⟩
  by_cases hi' : a i' = 0
  · rw [hi', map_zero]
    exact zero_le'
  obtain ⟨e', he'⟩ := hall i' hi'
  have h1 : V.valuation (a i') ^ n.factorial ≤ V.valuation (a i) ^ n.factorial := by
    rw [he, he', zpow_le_zpow_iff_right_of_lt_one₀ hpos hV]
    exact hmin e' ⟨i', hi', he'⟩
  by_contra hcon
  exact absurd h1 (not_le.2 (pow_lt_pow_left₀ (not_le.1 hcon) zero_le' n.factorial_ne_zero))

end GlobalTheory.ValMax
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemClosureOfFixed
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.ArtinFix

variable {K G : Type} [Field K] [Group G] (ρ : G →* RingAut K)

lemma rho_mul_apply (a b : G) (x : K) : ρ (a * b) x = ρ a (ρ b x) := by
  rw [map_mul]; rfl

lemma rho_inv_apply_apply (g : G) (x : K) : ρ g⁻¹ (ρ g x) = x := by
  rw [← rho_mul_apply, inv_mul_cancel, map_one]; rfl

lemma rho_apply_inv_apply (g : G) (x : K) : ρ g (ρ g⁻¹ x) = x := by
  rw [← rho_mul_apply, mul_inv_cancel, map_one]; rfl

variable (Δ : Subgroup G)

def fixSub : Subfield K where
  carrier := {x | ∀ δ ∈ Δ, ρ δ x = x}
  mul_mem' := by
    intro a b ha hb δ hδ
    simp [map_mul, ha δ hδ, hb δ hδ]
  one_mem' := by intro δ _; simp
  add_mem' := by
    intro a b ha hb δ hδ
    simp [map_add (f := _), ha δ hδ, hb δ hδ]
  zero_mem' := by intro δ _; simp
  neg_mem' := by
    intro a ha δ hδ
    simp [map_neg, ha δ hδ]
  inv_mem' := by
    intro a ha δ hδ
    simp [map_inv₀, ha δ hδ]

lemma map_mem_fixSub [hN : Δ.Normal] (g : G) {x : K} (hx : x ∈ fixSub ρ Δ) :
    ρ g x ∈ fixSub ρ Δ := by
  intro δ hδ
  have hm : g⁻¹ * δ * g ∈ Δ := by simpa using hN.conj_mem δ hδ g⁻¹
  have h := hx _ hm
  calc ρ δ (ρ g x) = ρ g (ρ (g⁻¹ * δ * g) x) := by
        rw [← rho_mul_apply, ← rho_mul_apply]; congr 1; group
    _ = ρ g x := by rw [h]

def restr [Δ.Normal] : G →* RingAut (fixSub ρ Δ) where
  toFun g :=
    { toFun := fun x => ⟨ρ g x, map_mem_fixSub ρ Δ g x.2⟩
      invFun := fun x => ⟨ρ g⁻¹ x, map_mem_fixSub ρ Δ g⁻¹ x.2⟩
      left_inv := fun x => Subtype.ext (rho_inv_apply_apply ρ g (x : K))
      right_inv := fun x => Subtype.ext (rho_apply_inv_apply ρ g (x : K))
      map_mul' := fun x y => Subtype.ext (map_mul (ρ g) (x : K) (y : K))
      map_add' := fun x y => Subtype.ext (map_add (ρ g) (x : K) (y : K)) }
  map_one' := by
    ext x
    simp
  map_mul' := by
    intro a b
    ext x
    exact rho_mul_apply ρ a b x

lemma le_ker_restr [Δ.Normal] : Δ ≤ (restr ρ Δ).ker := by
  intro δ hδ
  rw [MonoidHom.mem_ker]
  ext x
  exact x.2 δ hδ

theorem mem_closure_of_fixed (K G : Type) [Field K] [Group G] (ρ : G →* RingAut K)
    (Δ : Subgroup G) (hN : Δ.Normal) (hfi : Δ.FiniteIndex) (Y : Set K) (f : K)
    (hY : ∀ y ∈ Y, ∀ δ ∈ Δ, ρ δ y = y) (hf : ∀ δ ∈ Δ, ρ δ f = f)
    (hfix : ∀ g : G, (∀ y ∈ Y, ρ g y = y) → ρ g f = f) :
    f ∈ Subfield.closure ({x | ∀ g : G, ρ g x = x} ∪ Y) := by
  let L := fixSub ρ Δ
  let act : G ⧸ Δ →* RingAut L := QuotientGroup.lift Δ (restr ρ Δ) (le_ker_restr ρ Δ)
  letI : MulSemiringAction (G ⧸ Δ) L := MulSemiringAction.compHom L act
  have hsmul : ∀ (g : G) (x : L), (((QuotientGroup.mk g : G ⧸ Δ) • x : L) : K) = ρ g x :=
    fun g x => rfl
  let F := FixedPoints.subfield (G ⧸ Δ) L
  let Y' : Set L := {y | (y : K) ∈ Y}
  let E : IntermediateField F L := IntermediateField.adjoin F Y'
  have hfE : (⟨f, hf⟩ : L) ∈ E := by
    rw [← IsGalois.fixedField_fixingSubgroup E, IntermediateField.mem_fixedField_iff]
    intro σ hσ
    rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
    obtain ⟨q, rfl⟩ := FixedPoints.toAlgAut_surjective (G ⧸ Δ) L σ
    induction q using QuotientGroup.induction_on with
    | H g =>
      change (QuotientGroup.mk g : G ⧸ Δ) • (⟨f, hf⟩ : L) = ⟨f, hf⟩
      apply Subtype.ext
      rw [hsmul]
      apply hfix g
      intro y hy
      have h1 := hσ ⟨y, hY y hy⟩ (IntermediateField.subset_adjoin F Y' hy)
      have h2 := congrArg Subtype.val h1
      exact (hsmul g ⟨y, hY y hy⟩).symm.trans h2
  have hle : E.toSubfield ≤ (Subfield.closure ({x | ∀ g : G, ρ g x = x} ∪ Y)).comap L.subtype := by
    rw [IntermediateField.adjoin_toSubfield, Subfield.closure_le]
    rintro x (⟨c, rfl⟩ | hx)
    · apply Subfield.subset_closure
      left
      intro g
      have h1 := c.2 (QuotientGroup.mk g : G ⧸ Δ)
      exact (hsmul g _).symm.trans (congrArg Subtype.val h1)
    · exact Subfield.subset_closure (Or.inr hx)
  exact hle (show (⟨f, hf⟩ : L) ∈ E.toSubfield from hfE)

end GlobalTheory.ArtinFix
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNumberFieldExpansionCoeffs
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.KZ.ES.NF
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem exp_inj (X : Tower Ω ε) : Function.Injective X.exp :=
  (X.exp : X.K →+* HahnSeries ℚ Ω).injective

theorem gal_alg (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) (c : Ω) :
    X.gal s (algebraMap Ω X.K c) = algebraMap Ω X.K (s c) := by
  apply exp_inj X
  ext r
  rw [X.gal_exp, AlgHom.commutes, AlgHom.commutes, HahnSeries.algebraMap_apply', HahnSeries.algebraMap_apply']
  by_cases h : r = 0 <;> simp [h, HahnSeries.coeff_single]

theorem gal_j (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) : X.gal s X.jK = X.jK := by
  apply exp_inj X
  ext r
  rw [X.gal_exp]
  obtain ⟨n, hn⟩ := X.j_exp.2.2 r
  rw [hn, map_intCast]

theorem gal_aeval (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) (p : Polynomial Ω) (h : ∀ c ∈ p.coeffs, s c = c) :
    X.gal s (Polynomial.aeval X.jK p) = Polynomial.aeval X.jK p := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Polynomial.aeval_eq_sum_range, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def, map_mul, map_pow, gal_j, gal_alg]
  by_cases h0 : p.coeff i = 0
  · simp [h0]
  · rw [h _ (Polynomial.coeff_mem_coeffs h0)]

theorem exists_poly (X : Tower Ω ε) (f : X.K) : ∃ (C : Set Ω) (P : Polynomial X.K), C.Finite ∧ P ≠ 0 ∧
    ∀ s : Ω ≃ₐ[ℚ] Ω, (∀ c ∈ C, s c = c) → P.IsRoot (X.gal s f) := by
  obtain ⟨p, hp, hf⟩ := X.alg_j f
  have key : ∀ i : ℕ, ∃ u v : Polynomial Ω, (p.coeff i : X.K) = Polynomial.aeval X.jK u / Polynomial.aeval X.jK v :=
    fun i => (IntermediateField.mem_adjoin_simple_iff Ω _).1 (p.coeff i).2
  choose u v huv using key
  refine ⟨⋃ i ∈ p.support, ((u i).coeffs ∪ (v i).coeffs : Set Ω), p.map (algebraMap _ X.K), ?_, ?_, ?_⟩
  · exact Set.Finite.biUnion (Finset.finite_toSet _) fun i _ => (Finset.finite_toSet _).union (Finset.finite_toSet _)
  · exact Polynomial.map_ne_zero hp
  · intro s hs
    have hP : (p.map (algebraMap _ X.K)).map (X.gal s : X.K →+* X.K) = p.map (algebraMap _ X.K) := by
      ext i
      rw [Polynomial.coeff_map, Polynomial.coeff_map]
      by_cases h0 : p.coeff i = 0
      · simp [h0]
      · have hi : i ∈ p.support := Polynomial.mem_support_iff.2 h0
        show X.gal s (p.coeff i : X.K) = (p.coeff i : X.K)
        rw [huv, map_div₀, gal_aeval X s _ fun c hc => hs c (Set.mem_biUnion hi (Or.inl hc)),
          gal_aeval X s _ fun c hc => hs c (Set.mem_biUnion hi (Or.inr hc))]
    have h1 : (p.map (algebraMap _ X.K)).IsRoot f := by
      rw [Polynomial.IsRoot, Polynomial.eval_map_algebraMap, hf]
    rw [← hP]
    exact Polynomial.IsRoot.map (f := (X.gal s : X.K →+* X.K)) h1

theorem coeff_numberField {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (f : X.K) :
    ∃ F : IntermediateField ℚ Ω, FiniteDimensional ℚ F ∧ ∀ r : ℚ, (X.exp f).coeff r ∈ F := by
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨C, P, hC, hP, hroot⟩ := exists_poly X f
  haveI := hC.to_subtype
  let F₀ : IntermediateField ℚ Ω := IntermediateField.adjoin ℚ C
  haveI : FiniteDimensional ℚ F₀ :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  haveI : @IsScalarTower ℚ F₀ Ω Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : Normal F₀ Ω := IntermediateField.normal ℚ Ω F₀
  let L : Finset ℚ → IntermediateField F₀ Ω := fun T =>
    IntermediateField.adjoin F₀ ((T.image fun r => (X.exp f).coeff r : Finset Ω) : Set Ω)
  have hfin : ∀ T, FiniteDimensional F₀ (L T) := fun T =>
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hb : ∀ T, Module.finrank F₀ (L T) ≤ P.natDegree := by
    intro T
    haveI := hfin T
    haveI : Algebra.IsSeparable F₀ (L T) := by
      haveI : CharZero F₀ := algebraRat.charZero F₀
      infer_instance
    rw [← AlgHom.card F₀ (L T) Ω]
    let e : (L T →ₐ[F₀] Ω) → (Ω ≃ₐ[ℚ] Ω) := fun σ =>
      (AlgEquiv.ofBijective (σ.liftNormal Ω) (Algebra.IsAlgebraic.algHom_bijective _)).restrictScalars ℚ
    have he : ∀ σ (x : L T), e σ x = σ x := fun σ x => σ.liftNormal_commutes Ω x
    have hm : ∀ σ, X.gal (e σ) f ∈ P.roots.toFinset := by
      intro σ
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hP]
      exact hroot _ fun c hc => (σ.liftNormal Ω).commutes (⟨c, IntermediateField.subset_adjoin ℚ C hc⟩ : F₀)
    calc Fintype.card (L T →ₐ[F₀] Ω) ≤ P.roots.toFinset.card := by
          rw [← Finset.card_univ]
          refine Finset.card_le_card_of_injOn (fun σ => X.gal (e σ) f) (fun σ _ => hm σ) ?_
          intro σ _ τ _ h
          apply IntermediateField.adjoin_algHom_ext
          intro x hx
          rw [← he, ← he]
          obtain ⟨r, -, rfl⟩ := Finset.mem_image.1 hx
          show e σ ((X.exp f).coeff r) = e τ ((X.exp f).coeff r)
          rw [← X.gal_exp, ← X.gal_exp]
          exact congrArg (fun g => (X.exp g).coeff r) h
      _ ≤ _ := (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' P)
  have hB : BddAbove (Set.range fun T => Module.finrank F₀ (L T)) := ⟨P.natDegree, by rintro _ ⟨T, rfl⟩; exact hb T⟩
  obtain ⟨T, hT⟩ := Nat.sSup_mem (Set.range_nonempty fun T => Module.finrank F₀ (L T)) hB
  haveI := hfin T
  refine ⟨(L T).restrictScalars ℚ, FiniteDimensional.trans ℚ F₀ (L T), fun r => ?_⟩
  haveI := hfin (insert r T)
  have h : L T = L (insert r T) := by
    refine IntermediateField.eq_of_le_of_finrank_le (IntermediateField.adjoin.mono _ _ _ ?_) ?_
    · exact Finset.coe_subset.2 (Finset.image_subset_image (Finset.subset_insert _ _))
    · exact (le_csSup hB ⟨_, rfl⟩).trans hT.ge
  rw [IntermediateField.mem_restrictScalars, h]
  exact IntermediateField.subset_adjoin _ _ (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_insert_self _ _)))

end GlobalTheory.KZ.ES.NF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPrimitiveQuotientLevelPrimeTo
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

noncomputable section

namespace GlobalTheory.KZ.ES.Quot

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

private lemma hahnSeries_coeff_algebraMap_mul (c : Ω) (x : HahnSeries ℚ Ω) (r : ℚ) :
    (algebraMap Ω (HahnSeries ℚ Ω) c * x).coeff r = c * x.coeff r := by
  rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, HahnSeries.ofPowerSeries_C, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul,
    smul_eq_mul]

theorem _root_.GlobalTheory.KZ.ES.Quot.intC_const_mul {X : _root_.GlobalTheory.KZ.Tower Ω ε}
    {V : ValuationSubring Ω} {c : Ω} (hc : c ∈ V) {f : X.K}
    (hf : _root_.GlobalTheory.KZ.ES.IntC X V f) :
    _root_.GlobalTheory.KZ.ES.IntC X V (algebraMap Ω X.K c * f) := by
  intro r
  rw [map_mul, AlgHom.commutes, hahnSeries_coeff_algebraMap_mul]
  exact V.mul_mem _ _ hc (hf r)

theorem _root_.GlobalTheory.KZ.ES.Quot.intC_add {X : _root_.GlobalTheory.KZ.Tower Ω ε}
    {V : ValuationSubring Ω} {f g : X.K}
    (hf : _root_.GlobalTheory.KZ.ES.IntC X V f) (hg : _root_.GlobalTheory.KZ.ES.IntC X V g) :
    _root_.GlobalTheory.KZ.ES.IntC X V (f + g) := by
  intro r
  rw [map_add (f := _), HahnSeries.coeff_add]
  exact V.add_mem _ _ (hf r) (hg r)

theorem _root_.GlobalTheory.KZ.ES.Quot.intC_mul {X : _root_.GlobalTheory.KZ.Tower Ω ε}
    {V : ValuationSubring Ω} {f g : X.K}
    (hf : _root_.GlobalTheory.KZ.ES.IntC X V f) (hg : _root_.GlobalTheory.KZ.ES.IntC X V g) :
    _root_.GlobalTheory.KZ.ES.IntC X V (f * g) := by
  intro r
  rw [map_mul, HahnSeries.coeff_mul]
  exact V.toSubring.sum_mem fun ij _ => V.mul_mem _ _ (hf _) (hg _)

theorem _root_.GlobalTheory.KZ.ES.Quot.intC_one {X : _root_.GlobalTheory.KZ.Tower Ω ε}
    {V : ValuationSubring Ω} : _root_.GlobalTheory.KZ.ES.IntC X V 1 := by
  intro r
  rw [map_one, HahnSeries.coeff_one]
  split_ifs
  · exact V.one_mem
  · exact V.zero_mem

def bddRing (X : Tower Ω ε) (V : ValuationSubring Ω) (M : ℕ) : Subalgebra Ω X.K where
  carrier := {x | Lev X M x ∧ ∃ c : Ω, c ≠ 0 ∧ IntC X V (algebraMap Ω X.K c * x)}
  mul_mem' := by
    rintro a b ⟨ha, c, hc, hca⟩ ⟨hb, d, hd, hdb⟩
    refine ⟨fun γ hγ => by rw [map_mul, ha γ hγ, hb γ hγ], c * d, mul_ne_zero hc hd, ?_⟩
    have := intC_mul hca hdb
    rwa [mul_mul_mul_comm, ← map_mul] at this
  add_mem' := by
    rintro a b ⟨ha, c, hc, hca⟩ ⟨hb, d, hd, hdb⟩
    refine ⟨fun γ hγ => by rw [map_add (f := _), ha γ hγ, hb γ hγ], ?_⟩
    rcases V.mem_or_inv_mem (c / d) with h | h
    · refine ⟨c, hc, ?_⟩
      have := intC_add hca (intC_const_mul h hdb)
      rwa [← mul_assoc, ← map_mul, div_mul_cancel₀ _ hd, ← mul_add] at this
    · refine ⟨d, hd, ?_⟩
      have := intC_add (intC_const_mul h hca) hdb
      rwa [← mul_assoc, ← map_mul, inv_div, div_mul_cancel₀ _ hc, ← mul_add] at this
  algebraMap_mem' := fun c => by
    refine ⟨fun γ _ => by rw [AlgEquiv.commutes], ?_⟩
    by_cases hc : c = 0
    · refine ⟨1, one_ne_zero, fun r => ?_⟩
      simp [hc, V.zero_mem]
    · refine ⟨c⁻¹, inv_ne_zero hc, ?_⟩
      rw [← map_mul, inv_mul_cancel₀ hc, map_one]
      exact intC_one

def rho (X : Tower Ω ε) (H : Subgroup SL(2, ℤ)) : H →* RingAut X.K where
  toFun g := (X.sl (ofSL (g : SL(2, ℤ))⁻¹)).toRingEquiv
  map_one' := by
    ext f
    simp [X.sl_one]
  map_mul' g h := by
    ext f
    show X.sl (ofSL ((g * h : H) : SL(2, ℤ))⁻¹) f = X.sl (ofSL (g : SL(2, ℤ))⁻¹) (X.sl (ofSL (h : SL(2, ℤ))⁻¹) f)
    rw [← X.sl_mul, ← map_mul, Subgroup.coe_mul, _root_.mul_inv_rev]

section
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ}

private lemma gamma_le_gamma_of_dvd' {n m : ℕ} (h : n ∣ m) :
    CongruenceSubgroup.Gamma m ≤ CongruenceSubgroup.Gamma n := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma_mem] at hγ ⊢
  have hcast : ∀ a : ℤ, (ZMod.castHom h (ZMod n)) (a : ZMod m) = (a : ZMod n) :=
    fun a => map_intCast _ a
  obtain ⟨h1, h2, h3, h4⟩ := hγ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hcast, h1, map_one]
  · rw [← hcast, h2, map_zero]
  · rw [← hcast, h3, map_zero]
  · rw [← hcast, h4, map_one]

private lemma mem_valuationSubring_of_isIntegral_natCast_pow_mul {V : ValuationSubring Ω} {q : ℕ} (hq : q.Prime)
    (hqV : ((q : ℕ) : Ω) ∈ V.nonunits) {D : ℕ} (hqD : ¬ q ∣ D) {y : Ω} {e : ℕ}
    (hy : IsIntegral ℤ ((D : Ω) ^ e * y)) : y ∈ V := by
  have hint : ∀ z : Ω, IsIntegral ℤ z → z ∈ V := fun z hz => by
    obtain ⟨w, hw⟩ := IsIntegrallyClosed.isIntegral_iff.1 (hz.tower_top : IsIntegral V z)
    rw [← hw]
    exact w.2
  have hD1 : V.valuation (D : Ω) = 1 := by
    refine le_antisymm ((V.valuation_le_one_iff _).2 (natCast_mem V D)) (not_lt.1 fun hlt => ?_)
    have hg := Nat.gcd_eq_gcd_ab q D
    rw [((Nat.Prime.coprime_iff_not_dvd hq).2 hqD : Nat.gcd q D = 1)] at hg
    have huw : ((q.gcdA D : ℤ) : Ω) * (q : Ω) + ((q.gcdB D : ℤ) : Ω) * (D : Ω) = 1 := by
      have : (q.gcdA D) * (q : ℤ) + q.gcdB D * (D : ℤ) = 1 := by push_cast at hg; linarith
      have h' := congrArg (Int.cast : ℤ → Ω) this
      push_cast at h'
      exact h'
    have hqlt : V.valuation ((q : ℕ) : Ω) < 1 := (V.mem_nonunits_iff).1 hqV
    have hlt1 : V.valuation (((q.gcdA D : ℤ) : Ω) * (q : Ω) + ((q.gcdB D : ℤ) : Ω) * (D : Ω)) < 1 := by
      refine Valuation.map_add_lt _ ?_ ?_
      · rw [map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' ((V.valuation_le_one_iff _).2
          (intCast_mem V _))) hqlt
      · rw [map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' ((V.valuation_le_one_iff _).2
          (intCast_mem V _))) hlt
    rw [huw, map_one] at hlt1
    exact lt_irrefl _ hlt1
  rw [← V.valuation_le_one_iff]
  have h := (V.valuation_le_one_iff _).2 (hint _ hy)
  rwa [map_mul, map_pow, hD1, one_pow, one_mul] at h

private lemma eOm_mem_valuationSubring (ε : Ω →+* ℂ) (V : ValuationSubring Ω) (s : ℚ) :
    _root_.GlobalTheory.KZ.eOm ε s ∈ V := by
  haveI := IsAlgClosure.isAlgClosed ℚ (K := Ω)
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  set n := s.den with hn
  haveI : NeZero n := ⟨s.den_nz⟩
  set w : ℂ := Complex.exp (2 * Real.pi * Complex.I * s) with hw
  have hwn : w ^ n = 1 := by
    rw [hw, ← Complex.exp_nat_mul]
    have e : (n : ℂ) * (2 * Real.pi * Complex.I * s) = (s.num : ℂ) * (2 * Real.pi * Complex.I) := by
      have hs : (s : ℂ) * n = s.num := by exact_mod_cast Rat.mul_den_eq_num s
      rw [← hs]
      ring
    rw [e, Complex.exp_int_mul_two_pi_mul_I]
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic n Ω)
    (Polynomial.degree_cyclotomic_pos n Ω (NeZero.pos n)).ne'
  haveI : NeZero (n : Ω) := ⟨Nat.cast_ne_zero.2 (NeZero.ne n)⟩
  have hζ' : IsPrimitiveRoot ζ n := Polynomial.isRoot_cyclotomic_iff.1 hζ
  obtain ⟨i, -, hi⟩ := (hζ'.map_of_injective ε.injective).eq_pow_of_pow_eq_one hwn
  have hrange : ∃ z, ε z = w := ⟨ζ ^ i, by rw [map_pow, hi]⟩
  have hz : ε (_root_.GlobalTheory.KZ.eOm ε s) = w := Function.invFun_eq hrange
  have hzn : _root_.GlobalTheory.KZ.eOm ε s ^ n = 1 := by
    apply ε.injective
    rw [map_pow, hz, hwn, map_one]
  have hint : IsIntegral ℤ (_root_.GlobalTheory.KZ.eOm ε s) :=
    ⟨Polynomial.X ^ n - 1, Polynomial.monic_X_pow_sub_C 1 (NeZero.ne n), by simp [hzn]⟩
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 (hint.tower_top : IsIntegral V _)
  rw [← hy]
  exact y.2

private lemma two_mul_pow_dvd_of_sq_dvd_of_dvd_mul_add_two {P x : ℤ} (k : ℕ) (hP : P ≠ 0)
    (hx : (2 * P) ^ 2 ∣ x) (hxx : (2 * P) ^ (k + 2) ∣ x * (x + 2)) : 2 * P ^ (k + 2) ∣ x := by
  obtain ⟨y, rfl⟩ := hx
  have h2P : (2 * P) ^ 2 ≠ 0 := pow_ne_zero _ (mul_ne_zero two_ne_zero hP)
  have h1 : (2 * P) ^ k ∣ y * ((2 * P) ^ 2 * y + 2) := by
    rw [pow_add, mul_comm ((2 * P) ^ k), mul_assoc] at hxx
    exact (mul_dvd_mul_iff_left h2P).1 hxx
  have h2 : P ^ k ∣ (2 * y) * (2 * P ^ 2 * y + 1) := by
    have h := (pow_dvd_pow_of_dvd (dvd_mul_left P 2) k).trans h1
    have e : y * ((2 * P) ^ 2 * y + 2) = (2 * y) * (2 * P ^ 2 * y + 1) := by ring
    rwa [e] at h
  have hcop : IsCoprime (P ^ k) (2 * P ^ 2 * y + 1) :=
    IsCoprime.pow_left ⟨-(2 * P * y), 1, by ring⟩
  have h3 : P ^ k ∣ 2 * y := hcop.dvd_of_dvd_mul_right h2
  have e : (2 * P) ^ 2 * y = (2 * P ^ 2) * (2 * y) := by ring
  have e' : 2 * P ^ (k + 2) = (2 * P ^ 2) * P ^ k := by ring
  rw [e, e']
  exact mul_dvd_mul_left _ h3

private lemma mem_gamma_of_scalar_mod_two_mul_pow {M₀ l k : ℕ} (hM₀ : 0 < M₀) (hl : 0 < l) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma ((2 * M₀ * l) ^ 2))
    (h01 : ((γ 0 1 : ℤ) : ZMod ((2 * M₀ * l) ^ (k + 2))) = 0)
    (h10 : ((γ 1 0 : ℤ) : ZMod ((2 * M₀ * l) ^ (k + 2))) = 0)
    (hdiag : ((γ 0 0 : ℤ) : ZMod ((2 * M₀ * l) ^ (k + 2))) = ((γ 1 1 : ℤ) : ZMod ((2 * M₀ * l) ^ (k + 2)))) :
    γ ∈ CongruenceSubgroup.Gamma (M₀ * l ^ k) := by
  rw [CongruenceSubgroup.Gamma_mem] at hγ ⊢
  obtain ⟨g00, -, -, g11⟩ := hγ
  replace g00 := (ZMod.intCast_eq_intCast_iff_dvd_sub (γ 0 0) 1 ((2 * M₀ * l) ^ 2)).1 (by rw [Int.cast_one]; exact g00)
  replace g11 := (ZMod.intCast_eq_intCast_iff_dvd_sub (γ 1 1) 1 ((2 * M₀ * l) ^ 2)).1 (by rw [Int.cast_one]; exact g11)
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h01 h10
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hdiag
  have hM : ((M₀ * l ^ k : ℕ) : ℤ) ∣ (((2 * M₀ * l) ^ (k + 2) : ℕ) : ℤ) := by
    exact_mod_cast (show M₀ * l ^ k ∣ (2 * M₀ * l) ^ (k + 2) from
      ⟨2 ^ (k + 2) * M₀ ^ (k + 1) * l ^ 2, by ring⟩)
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.2
    rw [Matrix.det_fin_two] at this
    exact this
  set P : ℤ := (M₀ : ℤ) * l
  have hP : P ≠ 0 := mul_ne_zero (by exact_mod_cast hM₀.ne') (by exact_mod_cast hl.ne')
  have hcast : (((2 * M₀ * l) ^ (k + 2) : ℕ) : ℤ) = (2 * P) ^ (k + 2) := by push_cast; ring
  have hcast2 : (((2 * M₀ * l) ^ 2 : ℕ) : ℤ) = (2 * P) ^ 2 := by push_cast; ring
  rw [hcast] at h01 h10 hdiag hM
  rw [hcast2] at g00 g11
  have hx : (2 * P) ^ 2 ∣ γ 0 0 - 1 := dvd_sub_comm.1 g00
  have hxx : (2 * P) ^ (k + 2) ∣ (γ 0 0 - 1) * (γ 0 0 - 1 + 2) := by
    have e : (γ 0 0 - 1) * (γ 0 0 - 1 + 2) =
        γ 0 0 * (γ 1 1 - γ 0 0) * (-1) + γ 0 1 * γ 1 0 + 0 := by
      linear_combination hdet
    rw [e]
    exact dvd_add (dvd_add (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hdiag _) _)
      (dvd_mul_of_dvd_left h01 _)) (dvd_zero _)
  have ha : ((M₀ * l ^ k : ℕ) : ℤ) ∣ γ 0 0 - 1 := by
    refine dvd_trans ?_ (two_mul_pow_dvd_of_sq_dvd_of_dvd_mul_add_two k hP hx hxx)
    exact ⟨2 * M₀ ^ (k + 1) * l ^ 2, by push_cast [P]; ring⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := (ZMod.intCast_eq_intCast_iff_dvd_sub (γ 0 0) 1 (M₀ * l ^ k)).2 (dvd_sub_comm.1 ha)
    rwa [Int.cast_one] at h
  · rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hM.trans h01
  · rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hM.trans h10
  · have e : γ 1 1 - 1 = (γ 0 0 - 1) + (γ 1 1 - γ 0 0) := by ring
    have h := (ZMod.intCast_eq_intCast_iff_dvd_sub (γ 1 1) 1 (M₀ * l ^ k)).2
      (dvd_sub_comm.1 (e ▸ dvd_add ha (hM.trans hdiag)))
    rwa [Int.cast_one] at h

private lemma exists_finset_lev_mem_closure_bddRing (X : _root_.GlobalTheory.KZ.Tower Ω ε)
    (hj : ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ _root_.GlobalTheory.KZ.Hs ∧
      X.an X.jK = (φ : _root_.GlobalTheory.KZ.Mero))
    {l M₀ : ℕ} (hl : l.Prime) (hM₀ : 0 < M₀) :
    ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ V : ValuationSubring Ω,
      ((q : ℕ) : Ω) ∈ V.nonunits → ∀ (k : ℕ) (f : X.K),
      _root_.GlobalTheory.KZ.ES.Lev X (M₀ * l ^ k) f →
      f ∈ Subfield.closure
        (_root_.GlobalTheory.KZ.ES.Quot.bddRing X V ((2 * M₀ * l) ^ (k + 2)) : Set X.K) := by
  have hn : 0 < 2 * M₀ * l := Nat.mul_pos (Nat.mul_pos two_pos hM₀) hl.pos
  obtain ⟨T, hTlev, hTspan⟩ := _root_.GlobalTheory.KZ.ES.LevFin.exists_finset_span ε X hj
    ((2 * M₀ * l) ^ 2) (pow_pos hn 2)
  choose D hD hDint using fun t : X.K => X.bdd t
  refine ⟨(T.prod D).primeFactors, fun q hq hqS V hqV k f hf => ?_⟩
  set m := (2 * M₀ * l) ^ (k + 2) with hm
  have hm0 : 0 < m := pow_pos hn _
  set B := _root_.GlobalTheory.KZ.ES.Quot.bddRing X V m
  set L : IntermediateField Ω X.K := (Subfield.closure (B : Set X.K)).toIntermediateField
    fun c => Subfield.subset_closure (B.algebraMap_mem c)
  have hN₀m : (2 * M₀ * l) ^ 2 ∣ m := pow_dvd_pow _ (by omega)
  have hdvd : M₀ * l ^ k ∣ m := by
    rw [hm, pow_add, mul_comm ((2 * M₀ * l) ^ k)]
    exact mul_dvd_mul (dvd_pow ⟨2 * l, by ring⟩ two_ne_zero)
      (pow_dvd_pow_of_dvd (dvd_mul_left l _) k)
  have hT : ∀ t ∈ T, t ∈ B := by
    intro t ht
    refine ⟨fun γ hγ => hTlev t ht γ (gamma_le_gamma_of_dvd' hN₀m hγ), 1, one_ne_zero, fun r => ?_⟩
    rw [map_one, one_mul]
    obtain ⟨e, he⟩ := hDint t r
    have hqD : ¬ q ∣ D t := fun h => hqS (Nat.mem_primeFactors.2
      ⟨hq, h.trans (Finset.dvd_prod_of_mem D ht), (Finset.prod_pos fun i _ => hD i).ne'⟩)
    exact mem_valuationSubring_of_isIntegral_natCast_pow_mul hq hqV hqD he
  have hjB : X.jK ∈ B := by
    refine ⟨_root_.GlobalTheory.KZ.ES.lev_jK X m, 1, one_ne_zero, fun r => ?_⟩
    rw [map_one, one_mul]
    obtain ⟨z, hz⟩ := X.j_exp.2.2 r
    rw [hz]
    exact intCast_mem V z
  have hY : ∀ g ∈ ({!![(m : ℤ), 0; 0, 1], !![1, 0; 0, (m : ℤ)], !![1, 1; 0, (m : ℤ)]} :
      Set (Matrix (Fin 2) (Fin 2) ℤ)), X.sl (_root_.GlobalTheory.KZ.toGQ g) X.jK ∈ B := by
    intro g hg
    refine ⟨(_root_.GlobalTheory.KZ.ES.Scal.lev_and_scalar ε X m hm0).1 g hg, 1, one_ne_zero, fun r => ?_⟩
    rw [map_one, one_mul]
    have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast hm0.ne'
    have hg' : 0 < g.det ∧ g 1 0 = 0 ∧ g 0 0 ≠ 0 ∧ g 1 1 ≠ 0 := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      have hm'' : (0 : ℤ) < m := by exact_mod_cast hm0
      rcases hg with rfl | rfl | rfl <;> simp [Matrix.det_fin_two, hm', hm'', hm0, hm0.ne']
    obtain ⟨hd, h10, h00, h11⟩ := hg'
    have hE : ∀ i j, _root_.GlobalTheory.KZ.ent (_root_.GlobalTheory.KZ.toGQ g) i j = g i j := fun i j => by
      unfold _root_.GlobalTheory.KZ.ent _root_.GlobalTheory.KZ.toGQ
      rw [dite_eq_left hd]
      simp
    have h := X.exp_upper (_root_.GlobalTheory.KZ.toGQ g)
      (by rw [hE, h10]; simp) X.jK (r * g 1 1 / g 0 0)
    simp only [hE] at h
    have h00' : (g 0 0 : ℚ) ≠ 0 := by exact_mod_cast h00
    have h11' : (g 1 1 : ℚ) ≠ 0 := by exact_mod_cast h11
    have hr : r * (g 1 1 : ℚ) / (g 0 0) * (g 0 0) / (g 1 1) = r := by field_simp
    rw [hr] at h
    rw [h]
    obtain ⟨z, hz⟩ := X.j_exp.2.2 (r * g 1 1 / g 0 0)
    rw [hz]
    exact V.mul_mem _ _ (eOm_mem_valuationSubring ε V _) (intCast_mem V z)
  have hfix : ∀ x : X.K, _root_.GlobalTheory.KZ.ES.Lev X ((2 * M₀ * l) ^ 2) x →
      x ∈ Subfield.closure (B : Set X.K) := by
    intro x hx
    have hjL : IntermediateField.adjoin Ω {X.jK} ≤ L :=
      IntermediateField.adjoin_simple_le_iff.2 (Subfield.subset_closure hjB)
    have hspan := hTspan x hx
    clear hx
    induction hspan using Submodule.span_induction with
    | mem t ht => exact Subfield.subset_closure (hT t ht)
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | smul r y _ hy =>
      show (r : X.K) * y ∈ Subfield.closure (B : Set X.K)
      exact mul_mem (hjL r.2) hy
  haveI : NeZero m := ⟨hm0.ne'⟩
  have hart := _root_.GlobalTheory.ArtinFix.mem_closure_of_fixed X.K (CongruenceSubgroup.Gamma ((2 * M₀ * l) ^ 2))
    (_root_.GlobalTheory.KZ.ES.Quot.rho X _) ((CongruenceSubgroup.Gamma m).subgroupOf _)
    ((CongruenceSubgroup.Gamma_normal m).subgroupOf _) inferInstance
    ((fun g => X.sl (_root_.GlobalTheory.KZ.toGQ g) X.jK) ''
      ({!![(m : ℤ), 0; 0, 1], !![1, 0; 0, (m : ℤ)], !![1, 1; 0, (m : ℤ)]} :
        Set (Matrix (Fin 2) (Fin 2) ℤ))) f ?_ ?_ ?_
  · refine Subfield.closure_le.2 (Set.union_subset (fun x hx => hfix x ?_) ?_) hart
    · intro γ hγ
      have h := hx ⟨γ⁻¹, inv_mem hγ⟩
      change X.sl (_root_.GlobalTheory.KZ.ofSL (γ⁻¹)⁻¹) x = x at h
      rwa [inv_inv] at h
    · rintro _ ⟨g, hg, rfl⟩
      exact Subfield.subset_closure (hY g hg)
  · rintro _ ⟨g, hg, rfl⟩ δ hδ
    change X.sl (_root_.GlobalTheory.KZ.ofSL (δ : SL(2, ℤ))⁻¹) _ = _
    exact (_root_.GlobalTheory.KZ.ES.Scal.lev_and_scalar ε X m hm0).1 g hg _
      (inv_mem (Subgroup.mem_subgroupOf.1 hδ))
  · intro δ hδ
    change X.sl (_root_.GlobalTheory.KZ.ofSL (δ : SL(2, ℤ))⁻¹) f = f
    exact hf _ (gamma_le_gamma_of_dvd' hdvd (inv_mem (Subgroup.mem_subgroupOf.1 hδ)))
  · rintro ⟨g, hg⟩ hgY
    change X.sl (_root_.GlobalTheory.KZ.ofSL g⁻¹) f = f
    obtain ⟨h01, h10, hdiag⟩ := (_root_.GlobalTheory.KZ.ES.Scal.lev_and_scalar ε X m hm0).2 g⁻¹
      fun g' hg' => hgY _ ⟨g', hg', rfl⟩
    exact hf _ (mem_gamma_of_scalar_mod_two_mul_pow hM₀ hl.pos (inv_mem hg) h01 h10 hdiag)

private lemma exists_prim_mul_of_mem_bddRing {X : _root_.GlobalTheory.KZ.Tower Ω ε}
    {q : ℕ} (hq : q.Prime) {V : ValuationSubring Ω} (hqV : ((q : ℕ) : Ω) ∈ V.nonunits) {M : ℕ}
    {x : X.K} (hx : x ∈ _root_.GlobalTheory.KZ.ES.Quot.bddRing X V M) (hx0 : x ≠ 0) :
    ∃ (α : Ω) (a : X.K), α ≠ 0 ∧ _root_.GlobalTheory.KZ.ES.Lev X M a ∧
      _root_.GlobalTheory.KZ.ES.Prim X V a ∧ x = algebraMap Ω X.K α * a := by
  obtain ⟨hlev, c, hc, hcx⟩ := hx
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  obtain ⟨F, hF, hcoef⟩ := _root_.GlobalTheory.KZ.ES.NF.coeff_numberField ε X x
  have hne : ∃ r, (X.exp x).coeff r ≠ 0 := by
    by_contra h
    push_neg at h
    apply hx0
    apply (X.exp : X.K →+* HahnSeries ℚ Ω).injective
    rw [map_zero]
    exact HahnSeries.ext (funext h)
  obtain ⟨r, hr0, hmax⟩ := _root_.GlobalTheory.ValMax.exists_max_valuation F hF q hq V hqV ℚ
    (fun r => (X.exp x).coeff r) c hc hcoef
    (fun r => by simpa [map_mul, AlgHom.commutes, hahnSeries_coeff_algebraMap_mul] using hcx r) hne
  have hval : 0 < V.valuation ((X.exp x).coeff r) :=
    zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hr0)
  refine ⟨(X.exp x).coeff r, algebraMap Ω X.K ((X.exp x).coeff r)⁻¹ * x, hr0,
    fun γ hγ => by rw [map_mul, AlgEquiv.commutes, hlev γ hγ], ⟨fun r' => ?_, r, ?_⟩, ?_⟩
  · rw [map_mul, AlgHom.commutes, hahnSeries_coeff_algebraMap_mul,
      ← ValuationSubring.valuation_le_one_iff, map_mul, map_inv₀]
    exact (inv_mul_le_one₀ hval).2 (hmax r')
  · rw [map_mul, AlgHom.commutes, hahnSeries_coeff_algebraMap_mul, inv_mul_cancel₀ hr0,
      map_one]
  · rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hr0, map_one, one_mul]

theorem _root_.GlobalTheory.KZ.ES.Quot.quot_prim : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : _root_.GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ _root_.GlobalTheory.KZ.Hs ∧ X.an X.jK = (φ : _root_.GlobalTheory.KZ.Mero)) → ∀ (l M₀ : ℕ), l.Prime → 0 < M₀ → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ V : ValuationSubring Ω, ((q : ℕ) : Ω) ∈ V.nonunits → ∀ (k : ℕ) (f : X.K), f ≠ 0 → _root_.GlobalTheory.KZ.ES.Lev X (M₀ * l ^ k) f → ∃ (M' : ℕ) (a b : X.K) (c : Ω), 0 < M' ∧ Nat.Coprime q M' ∧ M₀ * l ^ k ∣ M' ∧ _root_.GlobalTheory.KZ.ES.Lev X M' a ∧ _root_.GlobalTheory.KZ.ES.Lev X M' b ∧ _root_.GlobalTheory.KZ.ES.Prim X V a ∧ _root_.GlobalTheory.KZ.ES.Prim X V b ∧ c ≠ 0 ∧ f * b = algebraMap Ω X.K c * a := by
  intro Ω _ _ _ ε X hj l M₀ hl hM₀
  obtain ⟨S, hS⟩ := exists_finset_lev_mem_closure_bddRing X hj hl hM₀
  refine ⟨S ∪ (2 * M₀ * l).primeFactors, fun q hq hqS V hqV k f hf0 hf => ?_⟩
  have hN : 0 < 2 * M₀ * l := Nat.mul_pos (Nat.mul_pos two_pos hM₀) hl.pos
  have hcop : Nat.Coprime q (2 * M₀ * l) := by
    refine (Nat.Prime.coprime_iff_not_dvd hq).2 fun hdvd => hqS ?_
    exact Finset.mem_union_right _ (Nat.mem_primeFactors.2 ⟨hq, hdvd, hN.ne'⟩)
  have hmem := hS q hq (fun h => hqS (Finset.mem_union_left _ h)) V hqV k f hf
  set B := _root_.GlobalTheory.KZ.ES.Quot.bddRing X V ((2 * M₀ * l) ^ (k + 2))
  obtain ⟨y, hy, z, hz, hyz⟩ := Subfield.mem_closure_iff.1 hmem
  have hB : Subring.closure (B : Set X.K) = B.toSubring := Subring.closure_eq B.toSubring
  rw [hB] at hy hz
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [div_zero] at hyz
    exact hf0 hyz.symm
  have hfz : f * z = y := by rw [← hyz, div_mul_cancel₀ _ hz0]
  have hy0 : y ≠ 0 := by
    rw [← hfz]
    exact mul_ne_zero hf0 hz0
  obtain ⟨α, a, hα, ha, hpa, rfl⟩ := exists_prim_mul_of_mem_bddRing hq hqV hy hy0
  obtain ⟨β, b, hβ, hb, hpb, rfl⟩ := exists_prim_mul_of_mem_bddRing hq hqV hz hz0
  refine ⟨(2 * M₀ * l) ^ (k + 2), a, b, β⁻¹ * α, by positivity, Nat.Coprime.pow_right _ hcop,
    ?_, ha, hb, hpa, hpb, mul_ne_zero (inv_ne_zero hβ) hα, ?_⟩
  · rw [pow_add, mul_comm ((2 * M₀ * l) ^ k)]
    exact mul_dvd_mul (dvd_pow ⟨2 * l, by ring⟩ two_ne_zero)
      (pow_dvd_pow_of_dvd (dvd_mul_left l _) k)
  · calc f * b = algebraMap Ω X.K β⁻¹ * (f * (algebraMap Ω X.K β * b)) := by
          rw [mul_left_comm f, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hβ, map_one, one_mul]
      _ = algebraMap Ω X.K (β⁻¹ * α) * a := by rw [hfz, map_mul, mul_assoc]
end

end GlobalTheory.KZ.ES.Quot
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPrimitiveQuotientLevelPrimeToStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primitive_quotient_level_prime_to : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (l M₀ : ℕ), l.Prime → 0 < M₀ → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ V : ValuationSubring Ω, ((q : ℕ) : Ω) ∈ V.nonunits → ∀ (k : ℕ) (f : X.K), f ≠ 0 → Lev X (M₀ * l ^ k) f → ∃ (M' : ℕ) (a b : X.K) (c : Ω), 0 < M' ∧ Nat.Coprime q M' ∧ M₀ * l ^ k ∣ M' ∧ Lev X M' a ∧ Lev X M' b ∧ Prim X V a ∧ Prim X V b ∧ c ≠ 0 ∧ f * b = algebraMap Ω X.K c * a := by
  first | exact @GlobalTheory.KZ.ES.Quot.quot_prim | exact GlobalTheory.KZ.ES.Quot.quot_prim | (intros; apply GlobalTheory.KZ.ES.Quot.quot_prim <;> assumption)
end
