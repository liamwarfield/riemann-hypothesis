module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasFDerivAtOfContinuousPartials

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardPrimitiveTupleExtensionsLe
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardHermitianQuadricAffineSubspaceResidueRing
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormGaussSumHermitianFormLinearLe
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormGaussSumHermitianFormLinearLe
open GlobalTheory.GramCount
open scoped Classical

namespace GlobalTheory.GramCount

theorem sum_char_unit_mul_ip_eq_zero {B : Type} [CommRing B] [Fintype B] (c : B →+* B)
    (hc : ∀ u, c (c u) = u) (χ : AddChar B ℂ) (hχ : χ.IsPrimitive) {n : ℕ} {s : B}
    (hs : IsUnit s) {z : Fin n → B} (hz : z ≠ 0) :
    ∑ y : Fin n → B, χ (s * ip c y z) = 0 := by
  let ψ : AddChar (Fin n → B) ℂ :=
    { toFun := fun y => χ (s * ip c y z)
      map_zero_eq_one' := by simp [ip_zero_left]
      map_add_eq_mul' := fun x y => by rw [ip_add_left, mul_add, AddChar.map_add_eq_mul] }
  have hψ : ψ ≠ 1 := by
    intro h
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hz
    have hne : s * c (z i) ≠ 0 := by
      intro h0
      have h1 : c (z i) = 0 := (hs.mul_right_eq_zero).1 h0
      apply hi
      have := congrArg c h1
      simpa [hc] using this
    apply hχ hne
    ext u
    have h2 : χ (s * ip c (Pi.single i u) z) = 1 := DFunLike.congr_fun h (Pi.single i u)
    have h3 : ip c (Pi.single i u) z = u * c (z i) := by
      unfold ip
      rw [Finset.sum_eq_single i]
      · simp
      · intro b _ hb
        simp [hb]
      · simp
    rw [h3] at h2
    rw [AddChar.mulShift_apply, AddChar.one_apply, ← h2]
    congr 1
    ring
  exact AddChar.sum_eq_zero_of_ne_one hψ

theorem norm_gauss_sum_ip_le {B : Type} [CommRing B] [Fintype B] (c : B →+* B)
    (hc : ∀ u, c (c u) = u) (q : ℕ) (_hq : 2 ≤ q) (hB : Fintype.card B = q ^ 2)
    (χ : AddChar B ℂ) (hχ : χ.IsPrimitive) (hinv : ∀ u, χ (c u) = χ u) (n : ℕ) (a : B)
    (ha : IsUnit (a + c a)) (v : Fin n → B) :
    ‖∑ y : Fin n → B, χ (a * ip c y y + ip c y v)‖ ≤ (q : ℝ) ^ n := by
  set Q : (Fin n → B) → B := fun y => a * ip c y y + ip c y v with hQ
  set S : ℂ := ∑ y : Fin n → B, χ (Q y) with hS
  have key : ∀ y z : Fin n → B,
      χ (Q (y + z)) * (starRingEnd ℂ) (χ (Q y)) = χ (Q z) * χ ((a + c a) * ip c y z) := by
    intro y z
    have h1 : χ (a * ip c z y) = χ (c a * ip c y z) := by
      rw [← hinv, map_mul, cj_ip c hc]
    have h2 : Q (y + z) + -Q y = Q z + a * ip c y z + a * ip c z y := by
      simp only [hQ, ip_add_left, ip_add_right]
      ring
    rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul, h2, AddChar.map_add_eq_mul, h1,
      add_mul, AddChar.map_add_eq_mul χ (Q z), AddChar.map_add_eq_mul χ (a * ip c y z), mul_assoc]
  have hsq : S * (starRingEnd ℂ) S = (((q : ℝ) ^ n) ^ 2 : ℝ) := by
    calc S * (starRingEnd ℂ) S
        = ∑ y : Fin n → B, S * (starRingEnd ℂ) (χ (Q y)) := by
          set_option synthInstance.maxHeartbeats 100000 in
            conv_lhs => rw [hS, map_sum, ← hS, Finset.mul_sum]
      _ = ∑ y : Fin n → B, ∑ z : Fin n → B, χ (Q z) * χ ((a + c a) * ip c y z) := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [hS, ← Equiv.sum_comp (Equiv.addLeft y), Finset.sum_mul]
          exact Finset.sum_congr rfl fun z _ => key y z
      _ = ∑ z : Fin n → B, χ (Q z) * ∑ y : Fin n → B, χ ((a + c a) * ip c y z) := by
          rw [Finset.sum_comm]
          simp only [Finset.mul_sum]
      _ = (((q : ℝ) ^ n) ^ 2 : ℝ) := by
          rw [Finset.sum_eq_single (0 : Fin n → B)]
          · simp [hQ, ip_zero_left, ip_zero_right, hB, ← pow_mul, mul_comm]
          · intro z _ hz
            rw [sum_char_unit_mul_ip_eq_zero c hc χ hχ ha hz, mul_zero]
          · simp
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at hsq
  have h3 : ‖S‖ ^ 2 = ((q : ℝ) ^ n) ^ 2 := by exact_mod_cast hsq
  exact ((pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h3).le

end GlobalTheory.GramCount
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormGaussSumHermitianFormLinearLeStatement
open GlobalTheory.GramCount
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_gauss_sum_hermitian_form_linear_le : ∀ {B : Type} [CommRing B] [Fintype B] (c : B →+* B), (∀ u, c (c u) = u) → ∀ (q : ℕ), 2 ≤ q → Fintype.card B = q ^ 2 → ∀ (χ : AddChar B ℂ), χ.IsPrimitive → (∀ u, χ (c u) = χ u) → ∀ (n : ℕ) (a : B), IsUnit (a + c a) → ∀ (v : Fin n → B), ‖∑ y : Fin n → B, χ (a * ip c y y + ip c y v)‖ ≤ (q : ℝ) ^ n := by
  first | exact @GlobalTheory.GramCount.norm_gauss_sum_ip_le | exact GlobalTheory.GramCount.norm_gauss_sum_ip_le | (intros; apply GlobalTheory.GramCount.norm_gauss_sum_ip_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardHermitianQuadricAffineSubspaceResidueRing
open GlobalTheory.GramCount
open scoped Classical

namespace GlobalTheory.GramCount

variable {B : Type} [CommRing B] [Fintype B]

theorem quad_sum_char_pi (χ : AddChar B ℂ) (hχ : χ.IsPrimitive) {m : ℕ} (w : Fin m → B) :
    ∑ s : Fin m → B, χ (∑ i, s i * w i) =
      if w = 0 then (Fintype.card B : ℂ) ^ m else 0 := by
  have h1 : ∀ s : Fin m → B, χ (∑ i, s i * w i) = ∏ i, χ (s i * w i) := by
    intro s
    induction (Finset.univ : Finset (Fin m)) using Finset.induction_on with
    | empty => simp
    | insert a S ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]
  simp only [h1]
  have h2 := Finset.prod_univ_sum (fun _ : Fin m => (Finset.univ : Finset B))
    (fun i b => χ (b * w i))
  rw [Fintype.piFinset_univ] at h2
  rw [← h2]
  simp only [AddChar.sum_mulShift _ hχ]
  split_ifs with hw
  · simp [hw]
  · obtain ⟨i, hi⟩ := Function.ne_iff.1 hw
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [show w i ≠ 0 from hi])


omit [Fintype B] in
theorem quad_char_skew (c : B →+* B) (hc : ∀ u, c (c u) = u) {ω : B} (hω : IsUnit (ω - c ω))
    (χ : AddChar B ℂ) (hχc : ∀ u, χ (c u) = χ u) {a w : B} (ha : c a = -a) (hw : c w = w) :
    χ (a * w) = 1 := by
  obtain ⟨θ, e, hθ, -, -⟩ := exists_trace_one c hc hω
  have h1 : a * w = θ * (a * w) + c (θ * (-(a * w))) := by
    simp only [map_mul, map_neg, ha, hw]
    linear_combination (-(a * w)) * hθ
  rw [h1, AddChar.map_add_eq_mul, hχc, ← AddChar.map_add_eq_mul]
  simp

theorem quad_count {B : Type} [CommRing B] [Fintype B] (c : B →+* B) (hc : ∀ u, c (c u) = u)
    (ω : B) (hω : IsUnit (ω - c ω)) (hf : ∀ t, c t = t → t ≠ 0 → IsUnit t) (q : ℕ) (hq : 2 ≤ q)
    (hB : Fintype.card B = q ^ 2) (χ : AddChar B ℂ) (hχ : χ.IsPrimitive)
    (hχc : ∀ u, χ (c u) = χ u) (k n : ℕ) (hkn : 2 * k + 1 ≤ 2 * n) (x : Fin k → Fin n → B)
    (hx : Prim c x) (g : Fin k → B) (t : B) (ht : c t = t) :
    |(Set.ncard {y : Fin n → B | (∀ i, ip c y (x i) = g i) ∧ ip c y y = t} : ℝ)
      - (q : ℝ) ^ (2 * n - (2 * k + 1))| ≤ (q : ℝ) ^ n := by
  set N := Set.ncard {y : Fin n → B | (∀ i, ip c y (x i) = g i) ∧ ip c y y = t} with hN
  let F : B × (Fin k → B) → ℂ := fun z => ∑ y : Fin n → B,
    χ (z.1 * (ip c y y - t)) * χ (∑ i, z.2 i * (ip c y (x i) - g i))
  let G : B × (Fin k → B) → ℂ := fun z =>
    if c z.1 = -z.1 ∧ z.2 = 0 then (q : ℂ) ^ (2 * n) else 0
  have hF : ∑ z, F z = (N : ℂ) * (q : ℂ) ^ (2 * k + 2) := by
    simp only [F]
    rw [Finset.sum_comm]
    have h1 : ∀ y : Fin n → B, ∑ z : B × (Fin k → B),
        χ (z.1 * (ip c y y - t)) * χ (∑ i, z.2 i * (ip c y (x i) - g i)) =
        if (∀ i, ip c y (x i) = g i) ∧ ip c y y = t then (q : ℂ) ^ (2 * k + 2) else 0 := by
      intro y
      rw [Fintype.sum_prod_type]
      simp only
      rw [← Finset.sum_mul_sum, AddChar.sum_mulShift _ hχ,
        quad_sum_char_pi χ hχ (fun i => ip c y (x i) - g i)]
      have h2 : ((fun i => ip c y (x i) - g i) = 0) ↔ ∀ i, ip c y (x i) = g i := by
        simp [funext_iff, sub_eq_zero]
      simp only [h2, sub_eq_zero, hB]
      by_cases h3 : (∀ i, ip c y (x i) = g i) <;> by_cases h4 : ip c y y = t <;> simp [h3, h4]
      ring
    simp only [h1]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hN, ← Set.ncard_coe_finset]
    congr 3
    ext y
    simp
  have hG : ∑ z, G z = (q : ℂ) ^ (2 * n + 1) := by
    have h1 := (card_fixed_sq c hc hω (M := B) c.toAddMonoidHom hc
      (fun a u => by simp)).2
    rw [Nat.card_eq_fintype_card (α := B), hB] at h1
    have h2 := (Nat.pow_left_injective two_ne_zero) h1
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype] at h2
    simp only [G]
    rw [Fintype.sum_prod_type]
    have h3 : ∀ a : B, (∑ s : Fin k → B,
        if c a = -a ∧ s = 0 then (q : ℂ) ^ (2 * n) else 0) =
        if c a = -a then (q : ℂ) ^ (2 * n) else 0 := by
      intro a
      by_cases h : c a = -a <;> simp [h]
    simp only [h3]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have h4 : (Finset.univ.filter fun a : B => c a = -a).card = q := by
      rw [← h2]; congr 1
    rw [h4]; ring
  have hFG : ∀ z, ‖F z - G z‖ ≤ (q : ℝ) ^ n := by
    rintro ⟨a, s⟩
    have hv : ∀ y : Fin n → B, ∑ i, s i * (ip c y (x i) - g i) =
        ip c y (∑ i, c (s i) • x i) - ∑ i, s i * g i := by
      intro y
      simp [ip_sum_right, ip_smul_right, hc, mul_sub, Finset.sum_sub_distrib]
    by_cases ha : c a = -a
    · have h0 : F (a, s) = G (a, s) := by
        have h1 : ∀ y : Fin n → B, χ (a * (ip c y y - t)) = 1 := fun y =>
          quad_char_skew c hc hω χ hχc ha (by rw [map_sub, cj_ip c hc, ht])
        simp only [F, G, h1, one_mul, ha, true_and]
        split_ifs with hs
        · simp [hs, hB, ← pow_mul]
        · simp only [hv]
          simp only [sub_eq_add_neg, AddChar.map_add_eq_mul]
          rw [← Finset.sum_mul]
          have h2 := quad_sum_char_pi χ hχ (fun j => c ((∑ i, c (s i) • x i) j))
          rw [if_neg] at h2
          · simp only [ip]
            rw [h2, zero_mul]
          · intro h3
            apply hs
            have h4 : ∑ i, c (s i) • x i = 0 := by
              funext j
              have := congrArg c (congrFun h3 j)
              simpa only [hc, Pi.zero_apply, map_zero] using this
            have h5 := hx.eq_zero c (fun i => c (s i)) h4
            funext i
            have := congrArg c (congrFun h5 i)
            simpa only [hc, Pi.zero_apply, map_zero] using this
      rw [h0, sub_self, norm_zero]
      positivity
    · have hu : IsUnit (a + c a) := hf _ (by rw [map_add (f := _), hc, add_comm])
        (fun h => ha (by linear_combination h))
      have h1 := GlobalTheory.T.norm_gauss_sum_hermitian_form_linear_le c hc q hq hB χ hχ hχc n a hu (∑ i, c (s i) • x i)
      have h2 : F (a, s) = χ (-(a * t + ∑ i, s i * g i)) *
          ∑ y : Fin n → B, χ (a * ip c y y + ip c y (∑ i, c (s i) • x i)) := by
        simp only [F, hv, Finset.mul_sum, ← AddChar.map_add_eq_mul]
        refine Finset.sum_congr rfl fun y _ => ?_
        congr 1
        ring
      have h3 : G (a, s) = 0 := by simp [G, ha]
      rw [h3, sub_zero, h2, norm_mul, AddChar.norm_apply, one_mul]
      exact h1
  have hS : ‖∑ z, F z - ∑ z, G z‖ ≤ (q : ℝ) ^ (2 * k + 2) * (q : ℝ) ^ n := by
    rw [← Finset.sum_sub_distrib]
    refine (norm_sum_le_of_le _ fun z _ => hFG z).trans (le_of_eq ?_)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fun,
      Fintype.card_fin, hB, nsmul_eq_mul]
    push_cast
    ring
  have hE : (q : ℂ) ^ (2 * n + 1) = (q : ℂ) ^ (2 * n - (2 * k + 1)) * (q : ℂ) ^ (2 * k + 2) := by
    rw [← pow_add]; congr 1; omega
  rw [hF, hG, hE, ← sub_mul, norm_mul] at hS
  have hq' : (0 : ℝ) < (q : ℝ) ^ (2 * k + 2) := by
    have : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
    positivity
  have h5 : ‖(q : ℂ) ^ (2 * k + 2)‖ = (q : ℝ) ^ (2 * k + 2) := by simp
  have h6 : ‖(N : ℂ) - (q : ℂ) ^ (2 * n - (2 * k + 1))‖ =
      |(N : ℝ) - (q : ℝ) ^ (2 * n - (2 * k + 1))| := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real]
    push_cast
    rfl
  rw [h5, h6, mul_comm] at hS
  exact le_of_mul_le_mul_left hS hq'

end GlobalTheory.GramCount
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardHermitianQuadricAffineSubspaceResidueRingStatement
open GlobalTheory.GramCount
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_hermitianQuadric_affineSubspace_residueRing : ∀ {B : Type} [CommRing B] [Fintype B] (c : B →+* B), (∀ u, c (c u) = u) → ∀ (ω : B), IsUnit (ω - c ω) → (∀ t, c t = t → t ≠ 0 → IsUnit t) → ∀ (q : ℕ), 2 ≤ q → Fintype.card B = q ^ 2 → ∀ (χ : AddChar B ℂ), χ.IsPrimitive → (∀ u, χ (c u) = χ u) → ∀ (k n : ℕ), 2 * k + 1 ≤ 2 * n → ∀ (x : Fin k → Fin n → B), Prim c x → ∀ (g : Fin k → B) (t : B), c t = t → |(Set.ncard {y : Fin n → B | (∀ i, ip c y (x i) = g i) ∧ ip c y y = t} : ℝ) - (q : ℝ) ^ (2 * n - (2 * k + 1))| ≤ (q : ℝ) ^ n := by
  first | exact @GlobalTheory.GramCount.quad_count | exact GlobalTheory.GramCount.quad_count | (intros; apply GlobalTheory.GramCount.quad_count <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsPrimitiveAddCharInvolutionInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsPrimitiveAddCharInvolutionInvariant
open GlobalTheory.GramCount
open scoped Classical

namespace GlobalTheory.GramCount

theorem exists_isPrimitive_invol_invariant {B : Type} [CommRing B] [Fintype B] (c : B →+* B)
    (hc : ∀ u, c (c u) = u) (ω : B) (hω : IsUnit (ω - c ω))
    (hfix : ∀ t, c t = t → t ≠ 0 → IsUnit t) :
    ∃ χ : AddChar B ℂ, χ.IsPrimitive ∧ ∀ u, χ (c u) = χ u := by
  rcases subsingleton_or_nontrivial B with hB | hB
  · refine ⟨1, fun a ha => absurd (Subsingleton.elim a 0) ha, fun u => by simp⟩
  obtain ⟨ψ, hψ⟩ := (AddChar.exists_apply_ne_zero (a := (1 : B))).2 one_ne_zero
  let T : B →+ B := AddMonoidHom.id B + c.toAddMonoidHom
  have hT : ∀ u, T u = u + c u := fun u => rfl
  refine ⟨ψ.compAddMonoidHom T, ?_, ?_⟩
  · intro a ha h
    have hex : ∃ u, a * u + c (a * u) ≠ 0 := by
      by_contra hne
      push_neg at hne
      have h1 := hne 1
      have h2 := hne ω
      rw [mul_one] at h1
      rw [map_mul] at h2
      have h3 : a * (ω - c ω) = 0 := by linear_combination h2 - c ω * h1
      exact ha ((hω.mul_left_eq_zero).1 h3)
    obtain ⟨u, hu⟩ := hex
    have hs : c (a * u + c (a * u)) = a * u + c (a * u) := by
      rw [map_add (f := _), hc, add_comm]
    obtain ⟨s', hs'⟩ := (hfix _ hs hu).exists_right_inv
    have hcs : c s' = s' := by
      have h4 := congrArg c hs'
      rw [map_mul, hs, map_one] at h4
      linear_combination s' * h4 - c s' * hs'
    have h5 : T (a * (u * s')) = 1 := by
      rw [hT, ← mul_assoc, map_mul c (a * u), hcs, ← hs']
      ring
    have h6 := DFunLike.congr_fun h (u * s')
    rw [AddChar.mulShift_apply, AddChar.compAddMonoidHom_apply, h5] at h6
    exact hψ (by simpa using h6)
  · intro u
    simp only [AddChar.compAddMonoidHom_apply, hT, hc, add_comm]

end GlobalTheory.GramCount
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsPrimitiveAddCharInvolutionInvariantStatement
open GlobalTheory.GramCount
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primitive_addChar_involution_invariant : ∀ {B : Type} [CommRing B] [Fintype B] (c : B →+* B), (∀ u, c (c u) = u) → ∀ (ω : B), IsUnit (ω - c ω) → (∀ t, c t = t → t ≠ 0 → IsUnit t) → ∃ χ : AddChar B ℂ, χ.IsPrimitive ∧ ∀ u, χ (c u) = χ u := by
  first | exact @GlobalTheory.GramCount.exists_isPrimitive_invol_invariant | exact GlobalTheory.GramCount.exists_isPrimitive_invol_invariant | (intros; apply GlobalTheory.GramCount.exists_isPrimitive_invol_invariant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NcardDependentVectorsAffineGramLe
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NcardDependentVectorsAffineGramLe
open GlobalTheory.GramCount
open scoped Classical

namespace GlobalTheory.GramCount

variable {B : Type} [CommRing B]

def depSet (c : B →+* B) {k n : ℕ} (x : Fin k → Fin n → B) (g : Fin k → B) (a : B) :
    Set (Fin n → B) :=
  {y | (∀ i, ip c y (x i) = g i) ∧ ∃ s : Fin k → B, a • y = ∑ i, s i • x i}

theorem depSet_subset_mul (c : B →+* B) {k n : ℕ} (x : Fin k → Fin n → B) (g : Fin k → B)
    (a b : B) : depSet c x g a ⊆ depSet c x g (b * a) := by
  rintro y ⟨h, s, hs⟩
  refine ⟨h, fun i => b * s i, ?_⟩
  rw [mul_smul, hs, Finset.smul_sum]
  simp [mul_smul]

theorem dep_isUnit_of_skew (c : B →+* B) (hc : ∀ u, c (c u) = u) {ω : B} (hω : IsUnit (ω - c ω))
    (hf : ∀ t, c t = t → t ≠ 0 → IsUnit t) {u : B} (hu : c u = -u) (h0 : u ≠ 0) : IsUnit u := by
  obtain ⟨θ, e, -, he, hce⟩ := exists_trace_one c hc hω
  refine isUnit_of_mul_isUnit_left (y := e) (hf _ ?_ ?_)
  · rw [map_mul, hu, hce]; ring
  · intro h
    exact h0 (he.mul_left_eq_zero.1 h)

theorem dep_unit_or_idem (c : B →+* B) (hc : ∀ u, c (c u) = u) {ω : B} (hω : IsUnit (ω - c ω))
    (hf : ∀ t, c t = t → t ≠ 0 → IsUnit t) {a : B} (h0 : a ≠ 0) :
    (∃ b, b * a = 1) ∨ ∃ b, (b * a) + c (b * a) = 1 ∧ (b * a) * c (b * a) = 0 := by
  by_cases hu : IsUnit a
  · exact Or.inl hu.exists_left_inv
  right
  have h1 : a * c a = 0 := by
    by_contra h
    exact hu (isUnit_of_mul_isUnit_left (hf _ (by rw [map_mul, hc, mul_comm]) h))
  have h2 : a + c a ≠ 0 := fun h =>
    hu (dep_isUnit_of_skew c hc hω hf (by linear_combination h) h0)
  have h3 : c (a + c a) = a + c a := by rw [map_add (f := _), hc, add_comm]
  obtain ⟨b, hb⟩ := (hf _ h3 h2).exists_left_inv
  have hb' : c b * (a + c a) = 1 := by
    have := congrArg c hb
    rwa [map_mul, h3, map_one] at this
  have hcb : c b = b := by linear_combination b * hb' - c b * hb
  refine ⟨b, ?_, ?_⟩
  · rw [map_mul, hcb]; linear_combination hb
  · rw [map_mul, hcb]; linear_combination b * b * h1

theorem dep_idem_eq (c : B →+* B) (hc : ∀ u, c (c u) = u) {ω : B} (hω : IsUnit (ω - c ω))
    (hf : ∀ t, c t = t → t ≠ 0 → IsUnit t) {ε ε' : B} (h1 : ε + c ε = 1) (h2 : ε * c ε = 0)
    (h1' : ε' + c ε' = 1) (h2' : ε' * c ε' = 0) : ε' = ε ∨ ε' = c ε := by
  by_cases h : ε' = ε
  · exact Or.inl h
  right
  have hu : IsUnit (ε' - ε) := dep_isUnit_of_skew c hc hω hf
    (by rw [map_sub]; linear_combination h1' - h1) (sub_ne_zero.2 h)
  have : (ε' - ε) * (ε' - c ε) = 0 := by
    linear_combination h2 - h2' + ε' * h1' - ε' * h1
  exact sub_eq_zero.1 (hu.mul_right_eq_zero.1 this)

theorem dep_kernel (c : B →+* B) (hc : ∀ u, c (c u) = u) {k n : ℕ} (x d : Fin k → Fin n → B)
    (hd : ∀ a b, ip c (x a) (d b) = if a = b then 1 else 0) {ε : B} (h1 : ε + c ε = 1)
    (h2 : ε * c ε = 0) (z : Fin n → B) (ρ s : Fin k → B) (hz : ∀ i, ip c z (x i) = 0)
    (hs : ε • z = ∑ i, s i • x i) (hA : ∀ i, c (ε * ip c z (d i)) + ε * ρ i = 0)
    (hB : ∀ l, (c ε • z + ∑ j, (c ε * ρ j) • d j) l +
      c ((c ε • z + ∑ j, (c ε * ρ j) • d j) l) = 0) : z = 0 ∧ ρ = 0 := by
  have hw : c ε • z + ∑ j, (c ε * ρ j) • d j = c ε • (z + ∑ j, ρ j • d j) := by
    simp only [smul_add, Finset.smul_sum, mul_smul]
  have hw0 : c ε • z + ∑ j, (c ε * ρ j) • d j = 0 := by
    funext l
    have := hB l
    rw [hw] at this ⊢
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, hc, Pi.zero_apply] at this ⊢
    set u := (z + ∑ j, ρ j • d j) l
    linear_combination c ε * this - c u * h2 + u * h2 - c ε * u * h1
  have hd' : ∀ a b, ip c (d b) (x a) = if a = b then 1 else 0 := fun a b => by
    rw [← cj_ip c hc, hd]; split_ifs <;> simp
  have hη : ∀ i, c ε * ρ i = 0 := fun i => by
    have := congrArg (fun v => ip c v (x i)) hw0
    simpa [ip_add_left, ip_sum_left, ip_smul_left, hd', hz, ip_zero_left] using this
  have hε : ∀ i, ε * ρ i = 0 := fun i => by
    have := hA i
    rw [map_mul] at this
    linear_combination ε * this - c (ip c z (d i)) * h2 + ρ i * h2 - ε * ρ i * h1
  have hs0 : ∀ i, s i = 0 := fun i => by
    have h3 := hA i
    rw [hε, add_zero] at h3
    have h4 := congrArg c h3
    rw [hc, map_zero] at h4
    have := congrArg (fun v => ip c v (d i)) hs
    simpa [ip_sum_left, ip_smul_left, hd, h4] using this.symm
  refine ⟨?_, funext fun i => ?_⟩
  · simp only [hη, zero_smul, Finset.sum_const_zero, add_zero] at hw0
    simp only [hs0, zero_smul, Finset.sum_const_zero] at hs
    rw [← one_smul B z, ← h1, add_smul, hs, hw0, add_zero]
  · have := hε i
    have := hη i
    simp only [Pi.zero_apply]
    linear_combination hε i + hη i - ρ i * h1

theorem ncard_depSet_idem_le [Fintype B] (c : B →+* B) (hc : ∀ u, c (c u) = u) {ω : B}
    (hω : IsUnit (ω - c ω)) {q : ℕ} (hq : Fintype.card B = q ^ 2) {k n : ℕ}
    (x : Fin k → Fin n → B) (hx : Prim c x) (g : Fin k → B) {ε : B} (h1 : ε + c ε = 1)
    (h2 : ε * c ε = 0) : (depSet c x g ε).ncard ≤ q ^ n := by
  obtain ⟨d, hd⟩ := hx
  have hK : Nat.card {t : B // c t = t} = q := by
    have := (card_fixed_sq c hc hω (M := B) c.toAddMonoidHom hc (fun a y => by simp)).1
    rw [Nat.card_eq_fintype_card (α := B), hq] at this
    exact Nat.pow_left_injective two_ne_zero this
  let F : depSet c x g ε × (Fin k → B) → (Fin k → B) × (Fin n → {t : B // c t = t}) :=
    fun p => (fun i => c (ε * ip c p.1.1 (d i)) + ε * p.2 i,
      fun l => ⟨(c ε • p.1.1 + ∑ j, (c ε * p.2 j) • d j) l +
        c ((c ε • p.1.1 + ∑ j, (c ε * p.2 j) • d j) l), by rw [map_add (f := _), hc, add_comm]⟩)
  have hF : Function.Injective F := by
    rintro ⟨⟨y, hy, s, hs⟩, r⟩ ⟨⟨y', hy', s', hs'⟩, r'⟩ h
    obtain ⟨hA, hB⟩ := Prod.ext_iff.1 h
    have key := dep_kernel c hc x d hd h1 h2 (y - y') (r - r') (s - s')
      (fun i => by rw [ip_sub_left, hy, hy', sub_self])
      (by simp only [smul_sub, hs, hs', Pi.sub_apply, sub_smul, Finset.sum_sub_distrib])
      (fun i => by
        have := congrFun hA i
        simp only [F, map_mul] at this
        simp only [ip_sub_left, map_mul, map_sub, Pi.sub_apply]
        linear_combination this)
      (fun l => by
        have := congrArg Subtype.val (congrFun hB l)
        simp only [F, Pi.add_apply, map_add (f := _)] at this
        simp only [smul_sub, mul_sub, sub_smul, Finset.sum_sub_distrib, Pi.add_apply,
          Pi.sub_apply, map_add, map_sub]
        linear_combination this)
    exact Prod.ext (Subtype.ext (sub_eq_zero.1 key.1)) (sub_eq_zero.1 key.2)
  have h3 := Nat.card_le_card_of_injective F hF
  rw [Nat.card_prod, Nat.card_prod, Nat.card_coe_set_eq, Nat.card_fun (α := Fin n), hK,
    mul_comm] at h3
  have h4 : 0 < Nat.card (Fin k → B) := Nat.card_pos
  simpa using Nat.le_of_mul_le_mul_left h3 h4

theorem ncard_dependent_le : ∀ {B : Type} [CommRing B] [Fintype B] (c : B →+* B),
    (∀ u, c (c u) = u) → ∀ (ω : B), IsUnit (ω - c ω) → (∀ t, c t = t → t ≠ 0 → IsUnit t) →
    ∀ (q : ℕ), 2 ≤ q → Fintype.card B = q ^ 2 → ∀ (k n : ℕ), 2 * k ≤ n →
    ∀ (x : Fin k → Fin n → B), Prim c x → ∀ (g : Fin k → B),
    Set.ncard {y : Fin n → B | (∀ i, ip c y (x i) = g i) ∧
      ∃ a : B, a ≠ 0 ∧ ∃ s : Fin k → B, a • y = ∑ i, s i • x i} ≤ 2 * q ^ n := by
  intro B _ _ c hc ω hω hf q hq2 hq k n hkn x hx g
  by_cases hex : ∃ ε : B, ε + c ε = 1 ∧ ε * c ε = 0
  · obtain ⟨ε, h1, h2⟩ := hex
    have hsub : {y : Fin n → B | (∀ i, ip c y (x i) = g i) ∧
        ∃ a : B, a ≠ 0 ∧ ∃ s : Fin k → B, a • y = ∑ i, s i • x i} ⊆
        depSet c x g ε ∪ depSet c x g (c ε) := by
      rintro y ⟨hy, a, ha, hs⟩
      have hy' : y ∈ depSet c x g a := ⟨hy, hs⟩
      rcases dep_unit_or_idem c hc hω hf ha with ⟨b, hb⟩ | ⟨b, hb1, hb2⟩
      · left
        have := depSet_subset_mul c x g a (ε * b) hy'
        rwa [mul_assoc, hb, mul_one] at this
      · have := depSet_subset_mul c x g a b hy'
        rcases dep_idem_eq c hc hω hf h1 h2 hb1 hb2 with h | h
        · left; rwa [h] at this
        · right; rwa [h] at this
    have hA := ncard_depSet_idem_le c hc hω hq x hx g h1 h2
    have hB := ncard_depSet_idem_le c hc hω hq x hx g (ε := c ε) (by rw [hc, add_comm, h1])
      (by rw [hc, mul_comm, h2])
    have := (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (Set.ncard_union_le _ _)
    omega
  · have hsub : {y : Fin n → B | (∀ i, ip c y (x i) = g i) ∧
        ∃ a : B, a ≠ 0 ∧ ∃ s : Fin k → B, a • y = ∑ i, s i • x i} ⊆
        (fun s : Fin k → B => ∑ i, s i • x i) '' Set.univ := by
      rintro y ⟨hy, a, ha, hs⟩
      have hy' : y ∈ depSet c x g a := ⟨hy, hs⟩
      rcases dep_unit_or_idem c hc hω hf ha with ⟨b, hb⟩ | ⟨b, hb⟩
      · obtain ⟨-, s, hs⟩ := depSet_subset_mul c x g a b hy'
        rw [hb, one_smul] at hs
        exact ⟨s, trivial, hs.symm⟩
      · exact absurd ⟨_, hb⟩ hex
    have h1 := (Set.ncard_le_ncard hsub (Set.toFinite _)).trans
      (Set.ncard_image_le (Set.toFinite _))
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fun, hq, Fintype.card_fin,
      ← pow_mul] at h1
    have h2 : q ^ (2 * k) ≤ q ^ n := Nat.pow_le_pow_right (by omega) hkn
    omega

end GlobalTheory.GramCount
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NcardDependentVectorsAffineGramLeStatement
open GlobalTheory.GramCount
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ncard_dependent_vectors_affine_gram_le : ∀ {B : Type} [CommRing B] [Fintype B] (c : B →+* B), (∀ u, c (c u) = u) → ∀ (ω : B), IsUnit (ω - c ω) → (∀ t, c t = t → t ≠ 0 → IsUnit t) → ∀ (q : ℕ), 2 ≤ q → Fintype.card B = q ^ 2 → ∀ (k n : ℕ), 2 * k ≤ n → ∀ (x : Fin k → Fin n → B), Prim c x → ∀ (g : Fin k → B), Set.ncard {y : Fin n → B | (∀ i, ip c y (x i) = g i) ∧ ∃ a : B, a ≠ 0 ∧ ∃ s : Fin k → B, a • y = ∑ i, s i • x i} ≤ 2 * q ^ n := by
  first | exact @GlobalTheory.GramCount.ncard_dependent_le | exact GlobalTheory.GramCount.ncard_dependent_le | (intros; apply GlobalTheory.GramCount.ncard_dependent_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrimitiveTupleOfLinearIndependentFiniteRing
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrimitiveTupleOfLinearIndependentFiniteRing
open GlobalTheory.GramCount
open scoped Classical

namespace GlobalTheory.GramCount

theorem sum_char_dot_eq_zero {B : Type} [CommRing B] [Fintype B] (χ : AddChar B ℂ)
    (hχ : χ.IsPrimitive) {m : ℕ} (t : Fin m → B) (ht : t ≠ 0) :
    ∑ s : Fin m → B, χ (∑ a, s a * t a) = 0 := by
  let f : (Fin m → B) →+ B :=
    { toFun := fun s => ∑ a, s a * t a
      map_zero' := by simp
      map_add' := fun s s' => by simp [add_mul, Finset.sum_add_distrib] }
  have h : χ.compAddMonoidHom f ≠ 0 := by
    intro h0
    obtain ⟨a, ha⟩ := Function.ne_iff.1 ht
    refine hχ ha ?_
    ext r
    have h1 := DFunLike.congr_fun h0 (Pi.single a r)
    simpa [f, Pi.single_apply, mul_comm] using h1
  exact AddChar.sum_eq_zero_iff_ne_zero.2 h

theorem exists_dot_eq_of_indep {B : Type} [CommRing B] [Fintype B] (χ : AddChar B ℂ)
    (hχ : χ.IsPrimitive) {k n : ℕ} (x : Fin k → Fin n → B)
    (hx : ∀ s : Fin k → B, ∑ a, s a • x a = 0 → s = 0) (u : Fin k → B) :
    ∃ z : Fin n → B, ∀ a, ∑ i, x a i * z i = u a := by
  by_contra hne
  push_neg at hne
  have h1 : ∑ z : Fin n → B, ∑ s : Fin k → B, χ (∑ a, s a * (∑ i, x a i * z i - u a)) = 0 := by
    refine Finset.sum_eq_zero fun z _ => ?_
    refine sum_char_dot_eq_zero χ hχ (fun a => ∑ i, x a i * z i - u a) ?_
    obtain ⟨a, ha⟩ := hne z
    intro h0
    exact ha (sub_eq_zero.1 (congrFun h0 a))
  rw [Finset.sum_comm, Finset.sum_eq_single (0 : Fin k → B)] at h1
  · simp at h1
  · intro s _ hs
    have h2 : ∀ z : Fin n → B, χ (∑ a, s a * (∑ i, x a i * z i - u a)) =
        χ (∑ i, z i * (∑ a, s a • x a) i) * χ (-∑ a, s a * u a) := by
      intro z
      rw [← AddChar.map_add_eq_mul]
      congr 1
      simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Finset.mul_sum, sub_eq_add_neg, mul_add, Finset.sum_add_distrib, mul_neg,
        Finset.sum_neg_distrib]
      congr 1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => ?_
      ring
    simp only [h2]
    rw [← Finset.sum_mul, sum_char_dot_eq_zero χ hχ _ (fun h => hs (hx s h)), zero_mul]
  · simp

theorem prim_of_indep_of_isPrimitive : ∀ {B : Type} [CommRing B] [Fintype B] (c : B →+* B),
    (∀ u, c (c u) = u) → ∀ (χ : AddChar B ℂ), χ.IsPrimitive →
    ∀ (k n : ℕ) (x : Fin k → Fin n → B),
      (∀ s : Fin k → B, ∑ a, s a • x a = 0 → s = 0) → Prim c x := by
  intro B _ _ c hc χ hχ k n x hx
  choose z hz using fun b : Fin k => exists_dot_eq_of_indep χ hχ x hx (Pi.single b 1)
  refine ⟨fun b i => c (z b i), fun a b => ?_⟩
  simp only [ip, hc]
  rw [hz, Pi.single_apply]

end GlobalTheory.GramCount
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrimitiveTupleOfLinearIndependentFiniteRingStatement
open GlobalTheory.GramCount
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPrimitiveTuple_of_linearIndependent_finite_ring : ∀ {B : Type} [CommRing B] [Fintype B] (c : B →+* B), (∀ u, c (c u) = u) → ∀ (χ : AddChar B ℂ), χ.IsPrimitive → ∀ (k n : ℕ) (x : Fin k → Fin n → B), (∀ s : Fin k → B, ∑ a, s a • x a = 0 → s = 0) → Prim c x := by
  first | exact @GlobalTheory.GramCount.prim_of_indep_of_isPrimitive | exact GlobalTheory.GramCount.prim_of_indep_of_isPrimitive | (intros; apply GlobalTheory.GramCount.prim_of_indep_of_isPrimitive <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardPrimitiveTupleExtensionsLe
open GlobalTheory.GramCount
open scoped Classical

namespace GlobalTheory.GramCount

theorem ncard_extend_prim_one : ∀ {B : Type} [CommRing B] [Fintype B] (c : B →+* B), (∀ u, c (c u) = u) → ∀ (ω : B), IsUnit (ω - c ω) → (∀ t, c t = t → t ≠ 0 → IsUnit t) → ∀ (q : ℕ), 2 ≤ q → Fintype.card B = q ^ 2 → ∀ (k n : ℕ), 2 * k + 1 ≤ n → ∀ (x : Fin k → Fin n → B), Prim c x → ∀ (g : Fin k → B) (t : B), c t = t → |(Set.ncard {y : Fin n → B | Prim c (Fin.cons y x : Fin (k + 1) → Fin n → B) ∧ (∀ i, ip c y (x i) = g i) ∧ ip c y y = t} : ℝ) - (q : ℝ) ^ (2 * n - (2 * k + 1))| ≤ 3 * (q : ℝ) ^ n := by
  intro B _ _ c hc ω hω hf q hq hB k n hkn x hx g t ht
  obtain ⟨χ, hχ, hχc⟩ := GlobalTheory.T.exists_primitive_addChar_involution_invariant c hc ω hω hf
  have hZ := GlobalTheory.T.card_hermitianQuadric_affineSubspace_residueRing c hc ω hω hf q hq hB χ hχ hχc k n (by omega) x hx g t ht
  have hD := GlobalTheory.T.ncard_dependent_vectors_affine_gram_le c hc ω hω hf q hq hB k n (by omega) x hx g
  set S := {y : Fin n → B | Prim c (Fin.cons y x : Fin (k + 1) → Fin n → B) ∧ (∀ i, ip c y (x i) = g i) ∧ ip c y y = t} with hS
  set Z := {y : Fin n → B | (∀ i, ip c y (x i) = g i) ∧ ip c y y = t} with hZd
  set D := {y : Fin n → B | (∀ i, ip c y (x i) = g i) ∧ ∃ a : B, a ≠ 0 ∧ ∃ s : Fin k → B, a • y = ∑ i, s i • x i} with hDd
  have h1 : S ⊆ Z := fun y hy => hy.2
  have h2 : Z ⊆ S ∪ D := by
    intro y hy
    by_cases hp : Prim c (Fin.cons y x : Fin (k + 1) → Fin n → B)
    · exact Or.inl ⟨hp, hy⟩
    · right
      have hne : ¬ ∀ s : Fin (k + 1) → B,
          ∑ a, s a • (Fin.cons y x : Fin (k + 1) → Fin n → B) a = 0 → s = 0 :=
        fun h => hp (GlobalTheory.T.isPrimitiveTuple_of_linearIndependent_finite_ring c hc χ hχ (k + 1) n _ h)
      push Not at hne
      obtain ⟨s, hs, hs0⟩ := hne
      rw [Fin.sum_univ_succ] at hs
      simp only [Fin.cons_zero, Fin.cons_succ] at hs
      refine ⟨hy.1, s 0, ?_, fun i => -s i.succ, ?_⟩
      · intro h0
        apply hs0
        rw [h0, zero_smul, zero_add] at hs
        have h3 := hx.eq_zero c (fun i => s i.succ) hs
        funext i
        refine Fin.cases h0 (fun j => ?_) i
        exact congrFun h3 j
      · simp only [neg_smul, Finset.sum_neg_distrib]
        exact eq_neg_of_add_eq_zero_left hs
  have h3 : S.ncard ≤ Z.ncard := Set.ncard_le_ncard h1 (Set.toFinite _)
  have h4 : Z.ncard ≤ S.ncard + 2 * q ^ n :=
    (Set.ncard_le_ncard h2 (Set.toFinite _)).trans
      ((Set.ncard_union_le _ _).trans (Nat.add_le_add_left hD _))
  have h3' : (S.ncard : ℝ) ≤ Z.ncard := by exact_mod_cast h3
  have h4' : (Z.ncard : ℝ) ≤ S.ncard + 2 * (q : ℝ) ^ n := by exact_mod_cast h4
  have h5 : (0 : ℝ) ≤ (q : ℝ) ^ n := by positivity
  rw [abs_le] at hZ ⊢
  constructor <;> linarith [hZ.1, hZ.2]

end GlobalTheory.GramCount
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardPrimitiveTupleExtensionsLeStatement
open GlobalTheory.GramCount
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_primitiveTuple_extensions_le : ∀ {B : Type} [CommRing B] [Fintype B] (c : B →+* B), (∀ u, c (c u) = u) → ∀ (ω : B), IsUnit (ω - c ω) → (∀ t, c t = t → t ≠ 0 → IsUnit t) → ∀ (q : ℕ), 2 ≤ q → Fintype.card B = q ^ 2 → ∀ (k n : ℕ), 2 * k + 1 ≤ n → ∀ (x : Fin k → Fin n → B), Prim c x → ∀ (g : Fin k → B) (t : B), c t = t → |(Set.ncard {y : Fin n → B | Prim c (Fin.cons y x : Fin (k + 1) → Fin n → B) ∧ (∀ i, ip c y (x i) = g i) ∧ ip c y y = t} : ℝ) - (q : ℝ) ^ (2 * n - (2 * k + 1))| ≤ 3 * (q : ℝ) ^ n := by
  first | exact @GlobalTheory.GramCount.ncard_extend_prim_one | exact GlobalTheory.GramCount.ncard_extend_prim_one | (intros; apply GlobalTheory.GramCount.ncard_extend_prim_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NcardPrimitiveTuplesWithGramMatrixResidueRing
open GlobalTheory.GramCount
open scoped Classical

namespace GlobalTheory.GramCount

theorem ncard_eq_sum_tail {α : Type} [Fintype α] {m : ℕ} (S : Set (Fin (m + 1) → α))
    (T : Set (Fin m → α)) (h : ∀ X ∈ S, Fin.tail X ∈ T) :
    S.ncard = ∑ x ∈ T.toFinset, Set.ncard {y : α | (Fin.cons y x : Fin (m + 1) → α) ∈ S} := by
  rw [Set.ncard_eq_toFinset_card' S,
    Finset.card_eq_sum_card_fiberwise (f := fun X => Fin.tail X) (t := T.toFinset)
      (by intro X hX; simpa using h X (by simpa using hX))]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Set.ncard_eq_toFinset_card']
  symm
  refine Finset.card_bij (fun y _ => (Fin.cons y x : Fin (m + 1) → α)) ?_ ?_ ?_
  · intro y hy
    simpa using hy
  · intro y _ y' _ hyy
    simpa using congrFun hyy 0
  · intro X hX
    simp only [Finset.mem_filter, Set.mem_toFinset] at hX
    obtain ⟨h1, rfl⟩ := hX
    exact ⟨X 0, by simpa using h1, by simp⟩

variable {B : Type} [CommRing B]

theorem tail_mem_sols (c : B →+* B) {m n : ℕ} (G : Matrix (Fin (m + 1)) (Fin (m + 1)) B)
    (X : Fin (m + 1) → Fin n → B) (hX : X ∈ sols c n G) :
    Fin.tail X ∈ sols c n (G.submatrix Fin.succ Fin.succ) := by
  obtain ⟨⟨y, hy⟩, h2⟩ := hX
  refine ⟨⟨Fin.tail y, fun a b => ?_⟩, fun a b => h2 _ _⟩
  simpa [Fin.tail] using hy a.succ b.succ

theorem cons_mem_sols (c : B →+* B) (hc : ∀ u, c (c u) = u) {m n : ℕ}
    (G : Matrix (Fin (m + 1)) (Fin (m + 1)) B) (hG : ∀ a b, c (G b a) = G a b)
    (x : Fin m → Fin n → B) (hx : x ∈ sols c n (G.submatrix Fin.succ Fin.succ))
    (y : Fin n → B) :
    (Fin.cons y x : Fin (m + 1) → Fin n → B) ∈ sols c n G ↔
      Prim c (Fin.cons y x : Fin (m + 1) → Fin n → B) ∧ (∀ i, ip c y (x i) = G i.succ 0) ∧
        ip c y y = G 0 0 := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun i => by simpa using h2 i.succ 0, by simpa using h2 0 0⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, fun a b => ?_⟩
    refine Fin.cases ?_ (fun a => ?_) a <;> refine Fin.cases ?_ (fun b => ?_) b
    · simpa using h3
    · simp only [Fin.cons_succ, Fin.cons_zero]
      rw [← cj_ip c hc, h2, hG]
    · simpa using h2 a
    · simpa using hx.2 a b

theorem pow_le_eta_mul {q m n : ℕ} (hq : 2 ≤ q) (h : 2 * m + 1 ≤ n) :
    (q : ℝ) ^ n ≤ (2 ^ (2 * m + 1) / 2 ^ n) * (q : ℝ) ^ (2 * n - (2 * m + 1)) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  have h1 : 2 * (2 * m + 1 + d) - (2 * m + 1) = (2 * m + 1 + d) + d := by omega
  have h2 : (2 : ℝ) ^ d ≤ (q : ℝ) ^ d :=
    pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hq) d
  have h3 : (2 : ℝ) ^ (2 * m + 1) / 2 ^ (2 * m + 1 + d) = 1 / 2 ^ d := by
    rw [pow_add (2 : ℝ) (2 * m + 1) d]; field_simp
  rw [h1, h3, pow_add (q : ℝ) (2 * m + 1 + d) d, one_div_mul_eq_div, le_div_iff₀ (by positivity)]
  gcongr

theorem eta_le {m n : ℕ} (h : 2 * m + 3 ≤ n) : (2 : ℝ) ^ (2 * m + 1) / 2 ^ n ≤ 1 / 4 := by
  rw [div_le_iff₀ (by positivity)]
  have : (2 : ℝ) ^ (2 * m + 3) ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) h
  have h2 : (2 : ℝ) ^ (2 * m + 3) = 4 * 2 ^ (2 * m + 1) := by ring
  linarith

theorem ncard_sols_eta [Fintype B] (c : B →+* B) (hc : ∀ u, c (c u) = u) (ω : B)
    (hω : IsUnit (ω - c ω)) (hf : ∀ t, c t = t → t ≠ 0 → IsUnit t) (q : ℕ) (hq : 2 ≤ q)
    (hB : Fintype.card B = q ^ 2) (n m : ℕ) :
    2 * m + 3 ≤ n → ∀ (G : Matrix (Fin m) (Fin m) B), (∀ a b, c (G b a) = G a b) →
      (1 - 2 ^ (2 * m + 1) / 2 ^ n) * (q : ℝ) ^ (2 * n * m - m ^ 2)
          ≤ (Set.ncard (sols c n G) : ℝ) ∧
        (Set.ncard (sols c n G) : ℝ)
          ≤ (1 + 2 * (2 ^ (2 * m + 1) / 2 ^ n)) * (q : ℝ) ^ (2 * n * m - m ^ 2) := by
  induction m with
  | zero =>
    intro _ G _
    have h1 : sols c n G = Set.univ := by
      ext x
      simp only [Set.mem_univ, iff_true]
      exact ⟨⟨x, fun a => a.elim0⟩, fun a => a.elim0⟩
    have h2 : (0 : ℝ) ≤ 2 ^ (2 * 0 + 1) / 2 ^ n := by positivity
    rw [h1, Set.ncard_univ, Nat.card_unique]
    simp only [mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, tsub_self,
      pow_zero, mul_one, Nat.cast_one] at h2 ⊢
    constructor <;> linarith
  | succ m ih =>
    intro hn G hG
    obtain ⟨i1, i2⟩ := ih (by omega) (G.submatrix Fin.succ Fin.succ) (fun a b => hG _ _)
    have hη := eta_le (m := m) (n := n) (by omega)
    have hp := pow_le_eta_mul (m := m) (n := n) hq (by omega)
    have he : (2 : ℝ) ^ (2 * (m + 1) + 1) / 2 ^ n = 4 * (2 ^ (2 * m + 1) / 2 ^ n) := by ring
    have hx : 2 * n * (m + 1) - (m + 1) ^ 2 = (2 * n * m - m ^ 2) + (2 * n - (2 * m + 1)) := by
      have h1 : m ^ 2 ≤ 2 * n * m := by nlinarith
      have h2 : 2 * n * (m + 1) = 2 * n * m + 2 * n := by ring
      have h3 : (m + 1) ^ 2 = m ^ 2 + (2 * m + 1) := by ring
      omega
    have hη0 : (0 : ℝ) ≤ 2 ^ (2 * m + 1) / 2 ^ n := by positivity
    rw [he, hx, pow_add (q : ℝ)]
    set η : ℝ := 2 ^ (2 * m + 1) / 2 ^ n
    set Q : ℝ := (q : ℝ) ^ (2 * n * m - m ^ 2) with hQ
    set R : ℝ := (q : ℝ) ^ (2 * n - (2 * m + 1)) with hR
    have hQ0 : 0 ≤ Q := by positivity
    have hR0 : 0 ≤ R := by positivity
    have key : ∀ x ∈ (sols c n (G.submatrix Fin.succ Fin.succ)).toFinset,
        (1 - 3 * η) * R ≤ (Set.ncard {y : Fin n → B |
            (Fin.cons y x : Fin (m + 1) → Fin n → B) ∈ sols c n G} : ℝ) ∧
          (Set.ncard {y : Fin n → B |
            (Fin.cons y x : Fin (m + 1) → Fin n → B) ∈ sols c n G} : ℝ) ≤ (1 + 3 * η) * R := by
      intro x hx
      rw [Set.mem_toFinset] at hx
      have := GlobalTheory.T.card_primitiveTuple_extensions_le c hc ω hω hf q hq hB m n (by omega) x hx.1 (fun i => G i.succ 0)
        (G 0 0) (hG 0 0)
      simp only [cons_mem_sols c hc G hG x hx]
      rw [abs_le] at this
      constructor <;> linarith [this.1, this.2]
    rw [ncard_eq_sum_tail _ _ (tail_mem_sols c G), Nat.cast_sum]
    rw [Set.ncard_eq_toFinset_card'] at i1 i2
    have k1 := Finset.card_nsmul_le_sum _ _ _ (fun x hx => (key x hx).1)
    have k2 := Finset.sum_le_card_nsmul _ _ _ (fun x hx => (key x hx).2)
    rw [nsmul_eq_mul] at k1 k2
    have hQR : 0 ≤ Q * R := mul_nonneg hQ0 hR0
    constructor
    · refine le_trans ?_ (le_trans (mul_le_mul_of_nonneg_right i1
        (mul_nonneg (by linarith) hR0)) k1)
      nlinarith [mul_nonneg (mul_nonneg hη0 hη0) hQR]
    · refine le_trans k2 (le_trans (mul_le_mul_of_nonneg_right i2
        (mul_nonneg (by linarith) hR0)) ?_)
      nlinarith [mul_nonneg (mul_nonneg hη0 (show 0 ≤ 1 / 4 - η by linarith)) hQR,
        mul_nonneg hη0 hQR]

theorem ncard_sols_residue : ∀ {B : Type} [CommRing B] [Fintype B] (c : B →+* B), (∀ u, c (c u) = u) → ∀ (ω : B), IsUnit (ω - c ω) → (∀ t, c t = t → t ≠ 0 → IsUnit t) → ∀ (q : ℕ), 2 ≤ q → Fintype.card B = q ^ 2 → ∀ (m n : ℕ), 2 * m + 3 ≤ n → ∀ (G : Matrix (Fin m) (Fin m) B), (∀ a b, c (G b a) = G a b) → (q : ℝ) ^ (2 * n * m - m ^ 2) ≤ 2 * (Set.ncard (sols c n G) : ℝ) ∧ (Set.ncard (sols c n G) : ℝ) ≤ 2 * (q : ℝ) ^ (2 * n * m - m ^ 2) := by
  intro B _ _ c hc ω hω hf q hq hB m n hn G hG
  obtain ⟨h1, h2⟩ := ncard_sols_eta c hc ω hω hf q hq hB n m hn G hG
  have hη := eta_le hn
  have hQ : (0 : ℝ) ≤ (q : ℝ) ^ (2 * n * m - m ^ 2) := by positivity
  have := mul_le_mul_of_nonneg_right hη hQ
  constructor <;> nlinarith

end GlobalTheory.GramCount
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NcardPrimitiveTuplesWithGramMatrixResidueRingStatement
open GlobalTheory.GramCount
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ncard_primitiveTuplesWithGramMatrix_residueRing : ∀ {B : Type} [CommRing B] [Fintype B] (c : B →+* B), (∀ u, c (c u) = u) → ∀ (ω : B), IsUnit (ω - c ω) → (∀ t, c t = t → t ≠ 0 → IsUnit t) → ∀ (q : ℕ), 2 ≤ q → Fintype.card B = q ^ 2 → ∀ (m n : ℕ), 2 * m + 3 ≤ n → ∀ (G : Matrix (Fin m) (Fin m) B), (∀ a b, c (G b a) = G a b) → (q : ℝ) ^ (2 * n * m - m ^ 2) ≤ 2 * (Set.ncard (sols c n G) : ℝ) ∧ (Set.ncard (sols c n G) : ℝ) ≤ 2 * (q : ℝ) ^ (2 * n * m - m ^ 2) := by
  first | exact @GlobalTheory.GramCount.ncard_sols_residue | exact GlobalTheory.GramCount.ncard_sols_residue | (intros; apply GlobalTheory.GramCount.ncard_sols_residue <;> assumption)
end
