module

public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.IsOpenPart
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.MemPrimitiveTensorsIffIsPrimitiveElem

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIntegralOfDivisibleCharacters
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIntegralOfDivisibleCharacters
open Formalism.MainNotions.DIV.Cons (intO)
open Polynomial

namespace GlobalTheory.IntegralOfPointValues

theorem mem_intO_of_isIntegral {C : Type} [NormedField C] [IsUltrametricDist C] {z : C}
    (hz : IsIntegral ↥(intO C) z) : z ∈ intO C := by
  let V : ValuationSubring C :=
    { intO C with
      mem_or_inv_mem' := fun x => by
        change ‖x‖ ≤ 1 ∨ ‖x⁻¹‖ ≤ 1
        rcases le_total ‖x‖ 1 with h | h
        · exact Or.inl h
        · exact Or.inr (by rw [norm_inv]; exact inv_le_one_of_one_le₀ h) }
  have hz' : IsIntegral V z := hz
  obtain ⟨v, rfl⟩ := (IsIntegrallyClosed.isIntegral_iff (R := V) (K := C)).1 hz'
  exact v.2

theorem _root_.GlobalTheory.IntegralOfPointValues.isIntegral_inv_smul_of_closed {O C B₀ B₁ : Type*} [CommRing O] [Field C] [IsAlgClosed C]
    [Algebra O C] (hinj : Function.Injective (algebraMap O C))
    (hcl : ∀ z : C, IsIntegral O z → z ∈ (algebraMap O C).range)
    [CommRing B₀] [Algebra O B₀] [Algebra.IsIntegral O B₀] [CommRing B₁] [Algebra C B₁]
    [Algebra O B₁] [IsScalarTower O C B₁] (j : B₀ →ₐ[O] B₁) (x : B₀) (q : O) (hq : q ≠ 0)
    (h : ∀ χ : B₀ →ₐ[O] O, q ∣ χ x) : IsIntegral O ((algebraMap O C q)⁻¹ • j x) := by
  classical
  set y := j x with hy
  set a := (algebraMap O C q)⁻¹ with ha
  have hjint : ∀ b, IsIntegral C (j b) := fun b =>
    ((Algebra.IsIntegral.isIntegral (R := O) b).map j).tower_top
  have hyint : IsIntegral C y := hjint x
  have hroot : ∀ α ∈ (minpoly C y).roots, ∃ k : O, algebraMap O C k = a * α := by
    intro α hα
    set D := Algebra.adjoin C (Set.range j) with hD
    haveI : Algebra.IsIntegral C D :=
      Algebra.IsIntegral.adjoin (by rintro _ ⟨b, rfl⟩; exact hjint b)
    have hmem : ∀ b, j b ∈ D := fun b => Algebra.subset_adjoin ⟨b, rfl⟩
    let yD : D := ⟨y, hmem x⟩
    have hnu : yD - algebraMap C D α ∈ nonunits D := by
      intro hu
      have hu' : IsUnit (y - algebraMap C B₁ α) := by
        simpa using hu.map D.val
      have hαr : IsRoot (minpoly C y) α := (mem_roots (minpoly.ne_zero hyint)).1 hα
      have hfac := mul_divByMonic_eq_iff_isRoot.2 hαr
      have hmon : ((minpoly C y) /ₘ (X - Polynomial.C α)).Monic :=
        (monic_X_sub_C α).of_mul_monic_left (by rw [hfac]; exact minpoly.monic hyint)
      apply minpoly.aeval_ne_zero_of_dvdNotUnit_minpoly (A := C) (x := y) hyint hmon
      · refine ⟨hmon.ne_zero, X - Polynomial.C α, ?_, by rw [mul_comm, hfac]⟩
        exact not_isUnit_X_sub_C α
      · have h0 := minpoly.aeval C y
        rw [← hfac, map_mul] at h0
        simpa using (hu'.mul_right_eq_zero).1 (by simpa using h0)
    obtain ⟨M, hMmax, hMmem⟩ := exists_max_ideal_of_mem_nonunits hnu
    letI : Field (D ⧸ M) := Ideal.Quotient.field M
    have hbij : Function.Bijective (algebraMap C (D ⧸ M)) :=
      IsAlgClosed.algebraMap_bijective_of_isIntegral
    let e : C ≃ₐ[C] D ⧸ M := AlgEquiv.ofBijective (Algebra.ofId C (D ⧸ M)) hbij
    let ψ : D →ₐ[C] C := e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ C M)
    have hψy : ψ yD = α := by
      have h1 : Ideal.Quotient.mkₐ C M yD = e α := by
        rw [Ideal.Quotient.mkₐ_eq_mk]
        change _ = Ideal.Quotient.mk M (algebraMap C D α)
        rw [Ideal.Quotient.eq]
        exact hMmem
      simp only [ψ, AlgHom.comp_apply, h1]
      exact e.symm_apply_apply α
    have hcomm : ∀ o : O,
        (⟨j (algebraMap O B₀ o), hmem _⟩ : D) = algebraMap C D (algebraMap O C o) :=
      fun o => by ext; simp [IsScalarTower.algebraMap_apply O C B₁]
    let jres : B₀ →+* D := (j : B₀ →+* B₁).codRestrict D hmem
    let χ₀ : B₀ →ₐ[O] C :=
      { ψ.toRingHom.comp jres with
        commutes' := fun o => by
          show ψ ⟨j (algebraMap O B₀ o), hmem _⟩ = _
          rw [hcomm]; exact ψ.commutes _ }
    have hχ₀x : χ₀ x = α := hψy
    have hval : ∀ b, χ₀ b ∈ (⊥ : Subalgebra O C) := fun b => by
      rw [Algebra.mem_bot]
      obtain ⟨t, ht⟩ := hcl _ ((Algebra.IsIntegral.isIntegral (R := O) b).map χ₀)
      exact ⟨t, ht⟩
    let eb := Algebra.botEquivOfInjective hinj
    let χ : B₀ →ₐ[O] O := eb.toAlgHom.comp (χ₀.codRestrict ⊥ hval)
    have hback : ∀ s : (⊥ : Subalgebra O C), algebraMap O C (eb s) = s := fun s => by
      have h2 : eb.symm (eb s) = s := eb.symm_apply_apply s
      rw [← Algebra.algebraMap_self_apply (eb s), eb.symm.commutes] at h2
      exact congrArg Subtype.val h2
    have hχx : algebraMap O C (χ x) = α := by
      rw [← hχ₀x]; exact hback _
    obtain ⟨k, hk⟩ := h χ
    refine ⟨k, ?_⟩
    have hq' : algebraMap O C q ≠ 0 := (map_ne_zero_iff _ hinj).2 hq
    rw [← hχx, hk, map_mul, ha, ← mul_assoc, inv_mul_cancel₀ hq', one_mul]
  set s := (minpoly C y).roots with hs
  let f : C → O := fun α => if hh : ∃ k : O, algebraMap O C k = a * α then hh.choose else 0
  have hf : ∀ α ∈ s, algebraMap O C (f α) = a * α := fun α hα => by
    have hh := hroot α hα
    simp only [f, dif_pos hh]
    exact hh.choose_spec
  have hsplit : minpoly C y = (s.map fun α => X - Polynomial.C α).prod :=
    (IsAlgClosed.splits (minpoly C y)).eq_prod_roots_of_monic (minpoly.monic hyint)
  have hzero : (s.map fun α => y - algebraMap C B₁ α).prod = 0 := by
    have h0 := minpoly.aeval C y
    rw [hsplit, map_multiset_prod, Multiset.map_map] at h0
    simpa [Function.comp_def] using h0
  refine ⟨(s.map fun α => X - Polynomial.C (f α)).prod,
    monic_multiset_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _), ?_⟩
  rw [eval₂_multiset_prod, Multiset.map_map]
  have hfac : ∀ α ∈ s, (eval₂ (algebraMap O B₁) (a • y) ∘ fun α => X - Polynomial.C (f α)) α =
      algebraMap C B₁ a * (y - algebraMap C B₁ α) := fun α hα => by
    simp only [Function.comp_apply, eval₂_sub, eval₂_X, eval₂_C]
    rw [IsScalarTower.algebraMap_apply O C B₁, hf α hα, Algebra.smul_def, map_mul, mul_sub]
  rw [Multiset.map_congr rfl hfac, Multiset.prod_map_mul, hzero, mul_zero]

theorem isIntegral_inv_smul : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] (B₀ B₁ : Type) [CommRing B₀] [Algebra ↥(intO C) B₀] [Module.Finite ↥(intO C) B₀] [CommRing B₁] [Algebra C B₁] [Algebra ↥(intO C) B₁] [IsScalarTower ↥(intO C) C B₁] (j : B₀ →ₐ[↥(intO C)] B₁) (x : B₀) (q : ↥(intO C)), q ≠ 0 → (∀ χ : B₀ →ₐ[↥(intO C)] ↥(intO C), q ∣ χ x) → IsIntegral ↥(intO C) (((q : C)⁻¹) • j x) := by
  intro C _ _ _ B₀ B₁ _ _ _ _ _ _ _ j x q hq h
  exact isIntegral_inv_smul_of_closed (O := ↥(intO C)) (C := C) Subtype.val_injective
    (fun z hz => ⟨⟨z, mem_intO_of_isIntegral hz⟩, rfl⟩) j x q hq h

end GlobalTheory.IntegralOfPointValues
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIntegralOfDivisibleCharactersStatement
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_of_divisible_characters : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] (B₀ B₁ : Type) [CommRing B₀] [Algebra ↥(intO C) B₀] [Module.Finite ↥(intO C) B₀] [CommRing B₁] [Algebra C B₁] [Algebra ↥(intO C) B₁] [IsScalarTower ↥(intO C) C B₁] (j : B₀ →ₐ[↥(intO C)] B₁) (x : B₀) (q : ↥(intO C)), q ≠ 0 → (∀ χ : B₀ →ₐ[↥(intO C)] ↥(intO C), q ∣ χ x) → IsIntegral ↥(intO C) (((q : C)⁻¹) • j x) := by
  first | exact @GlobalTheory.IntegralOfPointValues.isIntegral_inv_smul | exact GlobalTheory.IntegralOfPointValues.isIntegral_inv_smul | (intros; apply GlobalTheory.IntegralOfPointValues.isIntegral_inv_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormSmulLeOneOfPrimitiveBoundedPowers
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormSmulLeOneOfPrimitiveBoundedPowers
noncomputable section

namespace GlobalTheory.NearlyPrimitive

open Finset Filter Topology

section Factorial

variable {C : Type} [NormedField C] [IsUltrametricDist C]

theorem norm_natCast_eq_one_of_coprime {p m : ℕ} (hp : ‖(p : C)‖ < 1) (h : Nat.Coprime p m) :
    ‖(m : C)‖ = 1 := by
  refine le_antisymm (IsUltrametricDist.norm_natCast_le_one C m) ?_
  by_contra hlt
  push Not at hlt
  have hb : ((Nat.gcd p m : ℤ) : C) = ((p * Nat.gcdA p m + m * Nat.gcdB p m : ℤ) : C) := by
    rw [← Nat.gcd_eq_gcd_ab]
  rw [h.gcd_eq_one] at hb
  push_cast at hb
  have h1 : ‖(p : C) * ((Nat.gcdA p m : ℤ) : C)‖ < 1 := by
    rw [norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _)
      (IsUltrametricDist.norm_intCast_le_one C _)) hp
  have h2 : ‖(m : C) * ((Nat.gcdB p m : ℤ) : C)‖ < 1 := by
    rw [norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _)
      (IsUltrametricDist.norm_intCast_le_one C _)) hlt
  have h3 := (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt h1 h2)
  rw [← hb, norm_one] at h3
  exact lt_irrefl _ h3

theorem norm_factorial_inv_le (p : ℕ) [hp : Fact p.Prime] (h : ‖(p : C)‖ = (p : ℝ)⁻¹) (n : ℕ) :
    ‖((n.factorial : C))⁻¹‖ ≤ ((p : ℝ) ^ (1 / ((p : ℝ) - 1))) ^ n := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hlt : ‖(p : C)‖ < 1 := by rw [h]; exact inv_lt_one_of_one_lt₀ hp1
  obtain ⟨v, m, hm, hv⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Nat.factorial_ne_zero n) p
    hp.out.ne_one
  have hval : padicValNat p n.factorial = v := by
    have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero _)
    rw [Nat.padicValNat_def, hv, Nat.multiplicity_mul (pow_ne_zero _ hp.out.ne_zero) hm0,
      Nat.multiplicity_prime_pow, multiplicity_eq_zero_of_not_dvd hm, add_zero]
  have hle : (p - 1) * v ≤ n := by
    rw [← hval, Nat.padicValNat_def, hp.out.sub_one_mul_multiplicity_factorial]
    exact Nat.sub_le _ _
  have hle' : ((p : ℝ) - 1) * v ≤ n := by
    have : (((p - 1) * v : ℕ) : ℝ) ≤ n := by exact_mod_cast hle
    rwa [Nat.cast_mul, Nat.cast_sub hp.out.one_le, Nat.cast_one] at this
  have hm1 : ‖(m : C)‖ = 1 :=
    norm_natCast_eq_one_of_coprime hlt ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hm)
  rw [norm_inv, hv, Nat.cast_mul, Nat.cast_pow, norm_mul, norm_pow, hm1, h, mul_one, inv_pow,
    inv_inv, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
  refine Real.rpow_le_rpow_of_exponent_le hp1.le ?_
  rw [one_div, inv_mul_eq_div, le_div_iff₀ (by linarith)]
  linarith

end Factorial

def dpow (C : Type) [Field C] {B : Type} [CommRing B] [Algebra C B] (n : ℕ) (x : B) : B :=
  ((n.factorial : C))⁻¹ • x ^ n

theorem dpow_add {C : Type} [Field C] [CharZero C] {B : Type} [CommRing B] [Algebra C B]
    (n : ℕ) (x y : B) :
    dpow C n (x + y) = ∑ m ∈ antidiagonal n, dpow C m.1 x * dpow C m.2 y := by
  unfold dpow
  rw [(Commute.all x y).add_pow', Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' := Finset.HasAntidiagonal.mem_antidiagonal.mp hm
  rw [smul_mul_smul_comm, ← Nat.cast_smul_eq_nsmul C, smul_smul]
  congr 1
  have h := Nat.choose_mul_factorial_mul_factorial (n := n) (k := m.1) (by omega)
  rw [show n - m.1 = m.2 by omega] at h
  have h' : (n.choose m.1 : C) * m.1.factorial * m.2.factorial = n.factorial := by
    exact_mod_cast h
  have h1 : (m.1.factorial : C) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have h2 : (m.2.factorial : C) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have h3 : (n.factorial : C) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  field_simp
  linear_combination h'

theorem map_dpow {C : Type} [Field C] {B B' : Type} [CommRing B] [Algebra C B] [CommRing B']
    [Algebra C B'] (f : B →ₐ[C] B') (n : ℕ) (x : B) : f (dpow C n x) = dpow C n (f x) := by
  simp [dpow]

theorem sum_lt {B ι : Type} [AddCommGroup B] (N : B → ℝ) (h0 : N 0 = 0)
    (hadd : ∀ x y, N (x + y) ≤ max (N x) (N y)) {T : ℝ} (hT : 0 < T) (s : Finset ι) (f : ι → B)
    (hf : ∀ i ∈ s, N (f i) < T) : N (∑ i ∈ s, f i) < T := by
  refine Finset.sum_induction f (fun x => N x < T) (fun a b ha hb => ?_) (by rwa [h0]) hf
  exact (hadd a b).trans_lt (max_lt ha hb)

theorem sum_le {B ι : Type} [AddCommGroup B] (N : B → ℝ) (h0 : N 0 = 0)
    (hadd : ∀ x y, N (x + y) ≤ max (N x) (N y)) {T : ℝ} (hT : 0 ≤ T) (s : Finset ι) (f : ι → B)
    (hf : ∀ i ∈ s, N (f i) ≤ T) : N (∑ i ∈ s, f i) ≤ T := by
  refine Finset.sum_induction f (fun x => N x ≤ T) (fun a b ha hb => ?_) (by rwa [h0]) hf
  exact (hadd a b).trans (max_le ha hb)

theorem exists_last_max (t : ℕ → ℝ) (ht : Tendsto t atTop (𝓝 0)) (n : ℕ) (hn : 1 < t n) :
    ∃ k, 1 < t k ∧ (∀ a, t a ≤ t k) ∧ ∀ a, k < a → t a < t k := by
  obtain ⟨M, hM⟩ := eventually_atTop.1 (ht.eventually (gt_mem_nhds (zero_lt_one' ℝ)))
  have hnM : n ∈ range M := by
    rw [mem_range]
    by_contra h
    exact absurd (hM n (not_lt.1 h)) (not_lt.2 hn.le)
  obtain ⟨k₀, hk₀, hmax⟩ := Finset.exists_max_image (range M) t ⟨n, hnM⟩
  obtain ⟨k, hk, hlast⟩ := Finset.exists_max_image ((range M).filter fun a => t a = t k₀) id
    ⟨k₀, by simp [mem_range.1 hk₀]⟩
  rw [mem_filter] at hk
  have h1 : 1 < t k := by rw [hk.2]; exact hn.trans_le (hmax n hnM)
  have hall : ∀ a, t a ≤ t k := fun a => by
    by_cases ha : a < M
    · rw [hk.2]; exact hmax a (mem_range.2 ha)
    · exact ((hM a (not_lt.1 ha)).trans h1).le
  refine ⟨k, h1, hall, fun a hka => ?_⟩
  by_cases ha : a < M
  · refine lt_of_le_of_ne (hall a) fun h => ?_
    have := hlast a (by rw [mem_filter]; exact ⟨mem_range.2 ha, h.trans hk.2⟩)
    exact absurd hka (not_lt.2 this)
  · exact (hM a (not_lt.1 ha)).trans h1

theorem norm_smul_le_one_of_lt (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C]
    [CharZero C] (p : ℕ) [hp : Fact p.Prime] (hpn : ‖(p : C)‖ = (p : ℝ)⁻¹)
    (B₁ B₂ : Type) [CommRing B₁] [Algebra C B₁] [CommRing B₂] [Algebra C B₂]
    (N₁ : B₁ → ℝ) (N₂ : B₂ → ℝ) (Δ i j : B₁ →ₐ[C] B₂)
    (hs₁ : ∀ (c : C) x, N₁ (c • x) = ‖c‖ * N₁ x) (hs₂ : ∀ (c : C) x, N₂ (c • x) = ‖c‖ * N₂ x)
    (hn₁ : ∀ x, 0 ≤ N₁ x) (hn₂ : ∀ x, 0 ≤ N₂ x)
    (hadd : ∀ x y, N₂ (x + y) ≤ max (N₂ x) (N₂ y)) (hmul : ∀ x y, N₂ (x * y) ≤ N₂ x * N₂ y)
    (hΔ : ∀ x, N₂ (Δ x) ≤ N₁ x) (hij : ∀ x y, N₂ (i x * j y) = N₁ x * N₁ y)
    (y : B₁) (K : ℝ) (hK : ∀ k : ℕ, N₁ (y ^ k) ≤ K) (he : N₂ (Δ y - i y - j y) ≤ 1)
    (c : C) (hc : ‖c‖ < (p : ℝ) ^ (-(1 / ((p : ℝ) - 1)))) : N₁ (c • y) ≤ 1 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  set q : ℝ := (p : ℝ) ^ (1 / ((p : ℝ) - 1)) with hq
  have hq0 : 0 < q := Real.rpow_pos_of_pos hp0 _
  set ρ : ℝ := q * ‖c‖ with hρ
  have hρ0 : 0 ≤ ρ := mul_nonneg hq0.le (norm_nonneg _)
  have hρ1 : ρ < 1 := by
    rw [Real.rpow_neg hp0.le, ← hq] at hc
    calc ρ < q * q⁻¹ := mul_lt_mul_of_pos_left hc hq0
      _ = 1 := mul_inv_cancel₀ hq0.ne'
  have hcoef : ∀ n : ℕ, ‖((n.factorial : C))⁻¹‖ * ‖c ^ n‖ ≤ ρ ^ n := fun n => by
    rw [hρ, mul_pow, norm_pow]
    exact mul_le_mul_of_nonneg_right (norm_factorial_inv_le p hpn n) (by positivity)
  have h0 : N₂ 0 = 0 := by simpa using hs₂ 0 0
  have hneg : ∀ x, N₂ (-x) = N₂ x := fun x => by simpa using hs₂ (-1) x
  set e := Δ y - i y - j y with hedef
  have hepow : ∀ l : ℕ, N₂ (e ^ (l + 1)) ≤ 1 := fun l => by
    induction l with
    | zero => simpa using he
    | succ l ih =>
      rw [pow_succ]
      exact (hmul _ _).trans (mul_le_one₀ ih (hn₂ _) he)
  have hd : ∀ l : ℕ, l ≠ 0 → N₂ (dpow C l (c • e)) < 1 := fun l hl => by
    obtain ⟨l', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hl
    rw [dpow, smul_pow, hs₂, hs₂, ← mul_assoc]
    calc _ ≤ ρ ^ (l' + 1) * 1 := mul_le_mul (hcoef _) (hepow _) (hn₂ _) (by positivity)
      _ < 1 := by rw [mul_one]; exact pow_lt_one₀ hρ0 hρ1 hl
  set t : ℕ → ℝ := fun n => N₁ (dpow C n (c • y)) with ht
  have ht0 : ∀ n, 0 ≤ t n := fun n => hn₁ _
  have htle : ∀ n, t n ≤ ρ ^ n * K := fun n => by
    simp only [ht]
    rw [dpow, smul_pow, hs₁, hs₁, ← mul_assoc]
    exact mul_le_mul (hcoef _) (hK _) (hn₁ _) (by positivity)
  have hlim : Tendsto t atTop (𝓝 0) := by
    refine squeeze_zero ht0 htle ?_
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).mul_const K
  by_contra hcon
  have h1 : 1 < t 1 := by simpa [ht, dpow] using hcon
  obtain ⟨k, hk1, hmax, hlast⟩ := exists_last_max t hlim 1 h1
  have hk0 : 0 < t k := by linarith
  have hT : 0 < t k * t k := mul_pos hk0 hk0
  set s := i (c • y) + j (c • y) with hsdef
  have hγs : ∀ m, dpow C m s =
      ∑ x ∈ antidiagonal m, i (dpow C x.1 (c • y)) * j (dpow C x.2 (c • y)) := fun m => by
    rw [hsdef, dpow_add]
    simp only [map_dpow]
  have hsle : ∀ m, N₂ (dpow C m s) ≤ t k * t k := fun m => by
    rw [hγs]
    refine sum_le N₂ h0 hadd hT.le _ _ fun x _ => ?_
    rw [hij]
    exact mul_le_mul (hmax _) (hmax _) (ht0 _) hk0.le
  have hΔz : Δ (c • y) = s + c • e := by
    simp only [hsdef, hedef, map_smul, smul_sub]
    abel
  have hkk : (k, k) ∈ antidiagonal (k + k) := by simp
  have h2k : (k + k, 0) ∈ antidiagonal (k + k) := by simp
  have E1 := dpow_add (C := C) (k + k) s (c • e)
  rw [← hΔz, ← map_dpow, ← Finset.add_sum_erase _ _ h2k] at E1
  have E2 := hγs (k + k)
  rw [← Finset.add_sum_erase _ _ hkk] at E2
  have hz : dpow C 0 (c • e) = 1 := by simp [dpow]
  simp only [hz, mul_one] at E1 E2
  have hA : N₂ (Δ (dpow C (k + k) (c • y))) < t k * t k := by
    refine (hΔ _).trans_lt ((hmax (k + k)).trans_lt ?_)
    nlinarith
  have hB : N₂ (∑ x ∈ (antidiagonal (k + k)).erase (k + k, 0),
      dpow C x.1 s * dpow C x.2 (c • e)) < t k * t k := by
    refine sum_lt N₂ h0 hadd hT _ _ fun x hx => ?_
    rw [mem_erase, Finset.HasAntidiagonal.mem_antidiagonal] at hx
    have hx2 : x.2 ≠ 0 := fun h => hx.1 (Prod.ext (by have := hx.2; simp only; omega) h)
    calc _ ≤ N₂ (dpow C x.1 s) * N₂ (dpow C x.2 (c • e)) := hmul _ _
      _ ≤ t k * t k * N₂ (dpow C x.2 (c • e)) := mul_le_mul_of_nonneg_right (hsle _) (hn₂ _)
      _ < t k * t k := mul_lt_of_lt_one_right hT (hd _ hx2)
  have hC : N₂ (∑ x ∈ (antidiagonal (k + k)).erase (k, k),
      i (dpow C x.1 (c • y)) * j (dpow C x.2 (c • y))) < t k * t k := by
    refine sum_lt N₂ h0 hadd hT _ _ fun x hx => ?_
    rw [mem_erase, Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rw [hij]
    change t x.1 * t x.2 < _
    have : k < x.1 ∨ k < x.2 := by
      by_contra h
      push Not at h
      have := hx.2
      exact hx.1 (Prod.ext (by simp only; omega) (by simp only; omega))
    rcases this with h | h
    · exact (mul_le_mul_of_nonneg_left (hmax _) (ht0 _)).trans_lt
        (mul_lt_mul_of_pos_right (hlast _ h) hk0)
    · exact mul_lt_mul' (hmax _) (hlast _ h) (ht0 _) hk0
  have E3 : i (dpow C k (c • y)) * j (dpow C k (c • y)) =
      Δ (dpow C (k + k) (c • y)) + -(∑ x ∈ (antidiagonal (k + k)).erase (k + k, 0),
      dpow C x.1 s * dpow C x.2 (c • e)) + -(∑ x ∈ (antidiagonal (k + k)).erase (k, k),
      i (dpow C x.1 (c • y)) * j (dpow C x.2 (c • y))) := by
    rw [E1, E2]; abel
  have hfin : N₂ (i (dpow C k (c • y)) * j (dpow C k (c • y))) < t k * t k := by
    rw [E3]
    refine (hadd _ _).trans_lt (max_lt ((hadd _ _).trans_lt (max_lt hA ?_)) ?_)
    · rwa [hneg]
    · rwa [hneg]
  rw [hij] at hfin
  exact lt_irrefl _ hfin

theorem norm_smul_le_one : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] (p : ℕ) [Fact p.Prime], ‖(p : C)‖ = (p : ℝ)⁻¹ → ∀ (B₁ B₂ : Type) [CommRing B₁] [Algebra C B₁] [CommRing B₂] [Algebra C B₂] (N₁ : B₁ → ℝ) (N₂ : B₂ → ℝ) (Δ i j : B₁ →ₐ[C] B₂), (∀ (c : C) x, N₁ (c • x) = ‖c‖ * N₁ x) → (∀ (c : C) x, N₂ (c • x) = ‖c‖ * N₂ x) → (∀ x, 0 ≤ N₁ x) → (∀ x, 0 ≤ N₂ x) → (∀ x y, N₂ (x + y) ≤ max (N₂ x) (N₂ y)) → (∀ x y, N₂ (x * y) ≤ N₂ x * N₂ y) → (∀ x, N₂ (Δ x) ≤ N₁ x) → (∀ x y, N₂ (i x * j y) = N₁ x * N₁ y) → ∀ y : B₁, (∃ K : ℝ, ∀ k : ℕ, N₁ (y ^ k) ≤ K) → N₂ (Δ y - i y - j y) ≤ 1 → ∀ a : C, ‖a‖ ≤ (p : ℝ) ^ (-(1 / ((p : ℝ) - 1))) → N₁ (a • y) ≤ 1 := by
  intro C _ _ _ _ p hp hpn B₁ B₂ _ _ _ _ N₁ N₂ Δ i j hs₁ hs₂ hn₁ hn₂ hadd hmul hΔ hij y ⟨K, hK⟩
    he a ha
  by_contra hcon
  push Not at hcon
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (p : ℝ) hcon
  have hn0 : n ≠ 0 := by rintro rfl; rw [pow_zero] at hn; linarith
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (p : C) (Nat.pos_of_ne_zero hn0)
  have hbn : ‖b‖ ^ n = (p : ℝ)⁻¹ := by rw [← norm_pow, hb, hpn]
  have hb1 : ‖b‖ < 1 := by
    rw [← pow_lt_one_iff_of_nonneg (norm_nonneg b) hn0, hbn]
    exact inv_lt_one_of_one_lt₀ hp1
  have hpos : 0 < (p : ℝ) ^ (-(1 / ((p : ℝ) - 1))) := Real.rpow_pos_of_pos (by linarith) _
  have hc : ‖b * a‖ < (p : ℝ) ^ (-(1 / ((p : ℝ) - 1))) := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left ha (norm_nonneg b)).trans_lt
      (mul_lt_of_lt_one_left hpos hb1)
  have h := norm_smul_le_one_of_lt C p hpn B₁ B₂ N₁ N₂ Δ i j hs₁ hs₂ hn₁ hn₂ hadd hmul hΔ hij y K
    hK he (b * a) hc
  rw [mul_smul, hs₁] at h
  have h2 := pow_le_one₀ (n := n) (mul_nonneg (norm_nonneg b) (hn₁ _)) h
  rw [mul_pow, hbn, inv_mul_le_iff₀ (by linarith), mul_one] at h2
  linarith

end GlobalTheory.NearlyPrimitive
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormSmulLeOneOfPrimitiveBoundedPowersStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_smul_le_one_of_primitive_bounded_powers : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] (p : ℕ) [Fact p.Prime], ‖(p : C)‖ = (p : ℝ)⁻¹ → ∀ (B₁ B₂ : Type) [CommRing B₁] [Algebra C B₁] [CommRing B₂] [Algebra C B₂] (N₁ : B₁ → ℝ) (N₂ : B₂ → ℝ) (Δ i j : B₁ →ₐ[C] B₂), (∀ (c : C) x, N₁ (c • x) = ‖c‖ * N₁ x) → (∀ (c : C) x, N₂ (c • x) = ‖c‖ * N₂ x) → (∀ x, 0 ≤ N₁ x) → (∀ x, 0 ≤ N₂ x) → (∀ x y, N₂ (x + y) ≤ max (N₂ x) (N₂ y)) → (∀ x y, N₂ (x * y) ≤ N₂ x * N₂ y) → (∀ x, N₂ (Δ x) ≤ N₁ x) → (∀ x y, N₂ (i x * j y) = N₁ x * N₁ y) → ∀ y : B₁, (∃ K : ℝ, ∀ k : ℕ, N₁ (y ^ k) ≤ K) → N₂ (Δ y - i y - j y) ≤ 1 → ∀ a : C, ‖a‖ ≤ (p : ℝ) ^ (-(1 / ((p : ℝ) - 1))) → N₁ (a • y) ≤ 1 := by
  first | exact @GlobalTheory.NearlyPrimitive.norm_smul_le_one | exact GlobalTheory.NearlyPrimitive.norm_smul_le_one | (intros; apply GlobalTheory.NearlyPrimitive.norm_smul_le_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DerivationDivisibleOfCocomm
noncomputable section

open Formalism.MainNotions.DIV.Cons (intO)
open TensorProduct Coalgebra WithConv

namespace GlobalTheory.GroupLikeDerivation

section Norm

variable {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]
  {M : Type} [AddCommGroup M] [Module ↥(intO C) M]

theorem norm_smul_le (o : ↥(intO C)) (x : C) : ‖o • x‖ ≤ ‖x‖ := by
  have ho : ‖(o : C)‖ ≤ 1 := o.2
  change ‖(o : C) * x‖ ≤ _
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) ho

theorem norm_le_of_mem_span (f : M →ₗ[↥(intO C)] C) {s : Set M} {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ m ∈ s, ‖f m‖ ≤ r) {m : M} (hm : m ∈ Submodule.span ↥(intO C) s) : ‖f m‖ ≤ r := by
  induction hm using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simpa using hr
  | add x y _ _ hx hy =>
    rw [map_add (f := _)]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
  | smul o x _ hx => rw [map_smul]; exact (norm_smul_le _ _).trans hx

theorem bddAbove_norm [Module.Finite ↥(intO C) M] (f : M →ₗ[↥(intO C)] C) :
    BddAbove (Set.range fun m => ‖f m‖) := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ↥(intO C)) (M := M)
  refine ⟨∑ m ∈ s, ‖f m‖, ?_⟩
  rintro _ ⟨m, rfl⟩
  refine norm_le_of_mem_span f (s := s) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    (fun m hm => Finset.single_le_sum (f := fun m => ‖f m‖) (fun _ _ => norm_nonneg _) hm) ?_
  rw [hs]; trivial

def supNorm (f : WithConv (M →ₗ[↥(intO C)] C)) : ℝ := ⨆ m, ‖f.ofConv m‖

theorem le_supNorm [Module.Finite ↥(intO C) M] (f : WithConv (M →ₗ[↥(intO C)] C)) (m : M) :
    ‖f.ofConv m‖ ≤ supNorm f := le_ciSup (bddAbove_norm f.ofConv) m

theorem supNorm_le {f : WithConv (M →ₗ[↥(intO C)] C)} {r : ℝ} (h : ∀ m, ‖f.ofConv m‖ ≤ r) :
    supNorm f ≤ r := ciSup_le h

theorem supNorm_nonneg (f : WithConv (M →ₗ[↥(intO C)] C)) : 0 ≤ supNorm f :=
  Real.iSup_nonneg fun _ => norm_nonneg _

theorem supNorm_smul (c : C) (f : WithConv (M →ₗ[↥(intO C)] C)) :
    supNorm (c • f) = ‖c‖ * supNorm f := by
  rw [supNorm, supNorm, Real.mul_iSup_of_nonneg (norm_nonneg c)]
  congr 1
  ext m
  rw [← norm_mul]
  rfl

theorem supNorm_add_le [Module.Finite ↥(intO C) M] (f g : WithConv (M →ₗ[↥(intO C)] C)) :
    supNorm (f + g) ≤ max (supNorm f) (supNorm g) :=
  supNorm_le fun m => (IsUltrametricDist.norm_add_le_max (f.ofConv m) (g.ofConv m)).trans
    (max_le_max (le_supNorm f m) (le_supNorm g m))

theorem supNorm_mul_le [Module.Finite ↥(intO C) M] [Coalgebra ↥(intO C) M]
    (f g : WithConv (M →ₗ[↥(intO C)] C)) : supNorm (f * g) ≤ supNorm f * supNorm g := by
  refine supNorm_le fun m => ?_
  have h := (Coalgebra.Repr.arbitrary ↥(intO C) m).convMul_apply f g
  rw [h]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (mul_nonneg (supNorm_nonneg _) (supNorm_nonneg _)) fun i _ => ?_
  rw [norm_mul]
  exact mul_le_mul (le_supNorm f _) (le_supNorm g _) (norm_nonneg _) (supNorm_nonneg _)

theorem supNorm_le_of_tmul {f : WithConv (M ⊗[↥(intO C)] M →ₗ[↥(intO C)] C)} {r : ℝ}
    (hr : 0 ≤ r) (h : ∀ a b, ‖f.ofConv (a ⊗ₜ b)‖ ≤ r) : supNorm f ≤ r := by
  refine supNorm_le fun t => ?_
  induction t with
  | tmul a b => exact h a b
  | add x y hx hy =>
    rw [map_add (f := _)]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)

theorem supNorm_eq_mul [Module.Finite ↥(intO C) M] (f g : WithConv (M →ₗ[↥(intO C)] C))
    (h : WithConv (M ⊗[↥(intO C)] M →ₗ[↥(intO C)] C))
    (hh : ∀ a b, h.ofConv (a ⊗ₜ b) = f.ofConv a * g.ofConv b) :
    supNorm h = supNorm f * supNorm g := by
  apply le_antisymm
  · refine supNorm_le_of_tmul (mul_nonneg (supNorm_nonneg _) (supNorm_nonneg _)) fun a b => ?_
    rw [hh, norm_mul]
    exact mul_le_mul (le_supNorm f _) (le_supNorm g _) (norm_nonneg _) (supNorm_nonneg _)
  · rw [supNorm.eq_1 f, Real.iSup_mul_of_nonneg (supNorm_nonneg g)]
    refine ciSup_le fun a => ?_
    rw [supNorm.eq_1 g, Real.mul_iSup_of_nonneg (norm_nonneg _)]
    refine ciSup_le fun b => ?_
    rw [← norm_mul, ← hh]
    exact le_supNorm h _

theorem exists_supNorm_pow_le [Module.Finite ↥(intO C) M] [Coalgebra ↥(intO C) M]
    [IsCocomm ↥(intO C) M] {y : WithConv (M →ₗ[↥(intO C)] C)} (hy : IsIntegral ↥(intO C) y) :
    ∃ K : ℝ, ∀ k : ℕ, supNorm (y ^ k) ≤ K := by
  obtain ⟨s, hs⟩ := hy.fg_adjoin_singleton
  refine ⟨∑ f ∈ s, supNorm f, fun k => supNorm_le fun m => ?_⟩
  have hk : y ^ k ∈ Submodule.span ↥(intO C) (s : Set (WithConv (M →ₗ[↥(intO C)] C))) := by
    rw [hs]
    exact pow_mem (Algebra.self_mem_adjoin_singleton _ y) k
  let ev : WithConv (M →ₗ[↥(intO C)] C) →ₗ[↥(intO C)] C :=
    { toFun := fun f => f.ofConv m
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact norm_le_of_mem_span ev (Finset.sum_nonneg fun _ _ => supNorm_nonneg _)
    (fun f hf => (le_supNorm f m).trans
      (Finset.single_le_sum (f := fun f => supNorm f) (fun _ _ => supNorm_nonneg _) hf)) hk

end Norm

section Conv

variable {R C A : Type} [CommRing R] [CommRing C] [Algebra R C] [CommRing A] [Bialgebra R A]

def extProd (f g : WithConv (A →ₗ[R] C)) : WithConv (A ⊗[R] A →ₗ[R] C) :=
  toConv ((Algebra.TensorProduct.lmul' R (S := C)).toLinearMap ∘ₗ TensorProduct.map f.ofConv g.ofConv)

@[simp] theorem extProd_tmul (f g : WithConv (A →ₗ[R] C)) (a b : A) :
    (extProd f g).ofConv (a ⊗ₜ b) = f.ofConv a * g.ofConv b := by
  simp [extProd]

theorem extProd_mul (f g h k : WithConv (A →ₗ[R] C)) :
    extProd f g * extProd h k = extProd (f * h) (g * k) := by
  have h1 := TensorProduct.map_convMul_map (f := f) (h := h) (g := g) (k := k)
  have h2 := LinearMap.algHom_comp_convMul_distrib (Algebra.TensorProduct.lmul' R (S := C))
    (toConv (TensorProduct.map f.ofConv g.ofConv)) (toConv (TensorProduct.map h.ofConv k.ofConv))
  rw [h1] at h2
  exact (congrArg toConv h2).symm

theorem tensor_ext {f g : WithConv (A ⊗[R] A →ₗ[R] C)}
    (h : ∀ a b, f.ofConv (a ⊗ₜ b) = g.ofConv (a ⊗ₜ b)) : f = g :=
  WithConv.ext (TensorProduct.ext' h)

theorem extProd_one : extProd (1 : WithConv (A →ₗ[R] C)) 1 = 1 :=
  tensor_ext fun a b => by simp [mul_comm]

variable (R C A) in
def inlHom : WithConv (A →ₗ[R] C) →ₐ[C] WithConv (A ⊗[R] A →ₗ[R] C) :=
  AlgHom.ofLinearMap
    { toFun := fun f => extProd f 1
      map_add' := fun f g => tensor_ext fun a b => by simp [add_mul]
      map_smul' := fun c f => tensor_ext fun a b => by simp [mul_assoc] }
    extProd_one fun f g => by simp [extProd_mul]

variable (R C A) in
def inrHom : WithConv (A →ₗ[R] C) →ₐ[C] WithConv (A ⊗[R] A →ₗ[R] C) :=
  AlgHom.ofLinearMap
    { toFun := fun f => extProd 1 f
      map_add' := fun f g => tensor_ext fun a b => by simp [mul_add]
      map_smul' := fun c f => tensor_ext fun a b => by simp [mul_left_comm] }
    extProd_one fun f g => by simp [extProd_mul]

variable (R C A) in
def mulHom : WithConv (A →ₗ[R] C) →ₐ[C] WithConv (A ⊗[R] A →ₗ[R] C) :=
  AlgHom.ofLinearMap
    { toFun := fun f => toConv (f.ofConv ∘ₗ (Bialgebra.mulCoalgHom R A).toLinearMap)
      map_add' := fun f g => rfl
      map_smul' := fun c f => rfl }
    (tensor_ext fun a b => by simp [mul_comm])
    fun f g => congrArg toConv (LinearMap.convMul_comp_coalgHom_distrib f g _)

variable (R C A) in
def extendHom : WithConv (A →ₗ[R] R) →ₐ[R] WithConv (A →ₗ[R] C) :=
  AlgHom.ofLinearMap
    { toFun := fun f => toConv ((Algebra.ofId R C).toLinearMap ∘ₗ f.ofConv)
      map_add' := fun f g => WithConv.ext (LinearMap.ext fun a => by simp)
      map_smul' := fun c f => WithConv.ext (LinearMap.ext fun a =>
        map_smul (Algebra.ofId R C).toLinearMap c (f.ofConv a)) }
    (WithConv.ext (LinearMap.ext fun a => by simp))
    fun f g => congrArg toConv (LinearMap.algHom_comp_convMul_distrib _ f g)

theorem inlHom_mul_inrHom (f g : WithConv (A →ₗ[R] C)) :
    inlHom R C A f * inrHom R C A g = extProd f g := by
  change extProd f 1 * extProd 1 g = _
  rw [extProd_mul, mul_one, one_mul]

end Conv

theorem exists_isGroupLikeElem {R A : Type} [CommRing R] [CommRing A] [Bialgebra R A]
    [Module.Finite R A] [Module.Projective R A] (χ : CartierDual R A →ₐ[R] R) :
    ∃ u : A, IsGroupLikeElem R u ∧ ∀ φ : CartierDual R A, φ.ofConv u = χ φ := by
  have h : ∀ φ : CartierDual R A,
      φ.ofConv ((CartierDual.bidual R A).symm (toConv χ.toLinearMap)) = χ φ :=
    fun φ => CartierDual.apply_bidual_symm _ φ
  refine ⟨_, (CartierDual.isGroupLikeElem_iff_mul _).2 ⟨?_, fun φ ψ => ?_⟩, h⟩
  · rw [h]; exact map_one χ
  · rw [h, h, h]; exact map_mul χ φ ψ

theorem dvd_iff_norm {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]
    {q : ↥(intO C)} (hq : q ≠ 0) (x : ↥(intO C)) : q ∣ x ↔ ‖(q : C)⁻¹ * (x : C)‖ ≤ 1 := by
  have hq' : (q : C) ≠ 0 := fun h => hq (Subtype.ext h)
  constructor
  · rintro ⟨z, rfl⟩
    rw [Subring.coe_mul, inv_mul_cancel_left₀ hq']
    exact z.2
  · intro h
    refine ⟨⟨_, h⟩, Subtype.ext ?_⟩
    rw [Subring.coe_mul]
    exact (mul_inv_cancel_left₀ hq' _).symm

theorem dvd_mul_of_groupLike (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C]
    [IsAlgClosed C] [CharZero C] (p : ℕ) [Fact p.Prime] (hp : ‖(p : C)‖ = (p : ℝ)⁻¹)
    (A : Type) [CommRing A] [Bialgebra ↥(intO C) A] [Coalgebra.IsCocomm ↥(intO C) A]
    [Module.Finite ↥(intO C) A] [Module.Free ↥(intO C) A] (q : ↥(intO C)) (hq : q ≠ 0)
    (D : A →ₗ[↥(intO C)] ↥(intO C))
    (hD : ∀ a b : A, q ∣ D (a * b) - Coalgebra.counit (R := ↥(intO C)) a * D b -
      Coalgebra.counit (R := ↥(intO C)) b * D a)
    (hu : ∀ u : A, IsGroupLikeElem ↥(intO C) u → q ∣ D u)
    (c : ↥(intO C)) (hc : ‖(c : C)‖ ≤ (p : ℝ) ^ (-(1 / ((p : ℝ) - 1)))) (a : A) :
    q ∣ c * D a := by
  set y : WithConv (A →ₗ[↥(intO C)] C) := (q : C)⁻¹ • extendHom ↥(intO C) C A (toConv D) with hy
  have hya : ∀ a, y.ofConv a = (q : C)⁻¹ * (D a : C) := fun _ => rfl
  have hint : IsIntegral ↥(intO C) y :=
    GlobalTheory.T.isIntegral_of_divisible_characters C (CartierDual ↥(intO C) A) _ (extendHom ↥(intO C) C A) (toConv D) q hq
      fun χ => by
        obtain ⟨u, h1, h2⟩ := exists_isGroupLikeElem χ
        rw [← h2]
        exact hu u h1
  have key := GlobalTheory.T.norm_smul_le_one_of_primitive_bounded_powers C p hp _ _ supNorm supNorm (mulHom ↥(intO C) C A)
    (inlHom ↥(intO C) C A) (inrHom ↥(intO C) C A) supNorm_smul supNorm_smul supNorm_nonneg
    supNorm_nonneg supNorm_add_le supNorm_mul_le
    (fun f => supNorm_le fun t => le_supNorm f _)
    (fun f g => supNorm_eq_mul f g _ fun a b => by rw [inlHom_mul_inrHom, extProd_tmul])
    y (exists_supNorm_pow_le hint)
    (supNorm_le_of_tmul zero_le_one fun a b => by
      have h := (dvd_iff_norm hq _).1 (hD a b)
      convert h using 2
      change y.ofConv (a * b) - (extProd y 1).ofConv (a ⊗ₜ b) - (extProd 1 y).ofConv (a ⊗ₜ b) = _
      rw [extProd_tmul, extProd_tmul, hya, hya, hya, LinearMap.convOne_apply,
        LinearMap.convOne_apply]
      change _ - _ * ((counit (R := ↥(intO C)) b : ↥(intO C)) : C) -
        ((counit (R := ↥(intO C)) a : ↥(intO C)) : C) * _ = _
      push_cast
      ring)
    c hc
  rw [dvd_iff_norm hq]
  have h : (q : C)⁻¹ * ((c * D a : ↥(intO C)) : C) = ((c : C) • y).ofConv a := by
    change _ = (c : C) * y.ofConv a
    rw [hya]
    push_cast
    ring
  rw [h]
  exact (le_supNorm _ a).trans key

end GlobalTheory.GroupLikeDerivation
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DerivationDivisibleOfCocommStatement
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivation_divisible_of_cocomm : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] (p : ℕ) [Fact p.Prime], ‖(p : C)‖ = (p : ℝ)⁻¹ → ∀ (A : Type) [CommRing A] [Bialgebra ↥(intO C) A] [Coalgebra.IsCocomm ↥(intO C) A] [Module.Finite ↥(intO C) A] [Module.Free ↥(intO C) A] (q : ↥(intO C)), q ≠ 0 → ∀ D : A →ₗ[↥(intO C)] ↥(intO C), (∀ a b : A, q ∣ D (a * b) - Coalgebra.counit (R := ↥(intO C)) a * D b - Coalgebra.counit (R := ↥(intO C)) b * D a) → (∀ u : A, IsGroupLikeElem ↥(intO C) u → q ∣ D u) → ∀ c : ↥(intO C), ‖(c : C)‖ ≤ (p : ℝ) ^ (-(1 / ((p : ℝ) - 1))) → ∀ a : A, q ∣ c * D a := by
  first | exact @GlobalTheory.GroupLikeDerivation.dvd_mul_of_groupLike | exact GlobalTheory.GroupLikeDerivation.dvd_mul_of_groupLike | (intros; apply GlobalTheory.GroupLikeDerivation.dvd_mul_of_groupLike <;> assumption)
end
