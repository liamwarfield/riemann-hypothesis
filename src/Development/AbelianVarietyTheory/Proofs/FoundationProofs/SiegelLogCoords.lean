module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinsupp
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LogCoordsUnitValueTwoVariableIntegralExpansion

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitAtScaledArgumentTwoVariableExpansion
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasQExpansionSmoothedEisensteinFxWeightOne
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasQExpansionSmoothedEisensteinFxWeightOne
noncomputable section

open scoped UpperHalfPlane
open GlobalTheory.Sieg GlobalTheory.QFam GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.Sieg.EisQ

theorem ee_int_mul' (n : ℤ) (z : ℂ) : ee (n * z) = ee z ^ n := by
  simp only [ee, ← Complex.exp_int_mul]; congr 1; ring

theorem hasSum_point {M : ℕ} (hM : 0 < M) (a A e : ℤ) (w : ℤ → ℤ → ℂ) :
    HasSum (fun p : ℤ × ℤ => if p.2 = e ∧ a + M * p.1 = A then w (a + M * p.1) p.2 else 0)
      (if A ≡ a [ZMOD M] then w A e else 0) := by
  have hM' : (M : ℤ) ≠ 0 := by exact_mod_cast hM.ne'
  split_ifs with h
  · obtain ⟨n, hn⟩ := h.symm.dvd
    have hA : a + M * n = A := by linarith
    have := hasSum_single (f := fun p : ℤ × ℤ => if p.2 = e ∧ a + M * p.1 = A then w (a + M * p.1) p.2 else 0)
      (n, e) (fun p hp => by
        rw [if_neg]
        rintro ⟨h1, h2⟩
        apply hp
        refine Prod.ext ?_ h1
        apply mul_left_cancel₀ hM'
        simp only
        linarith)
    simpa [hA] using this
  · have : (fun p : ℤ × ℤ => if p.2 = e ∧ a + M * p.1 = A then w (a + M * p.1) p.2 else 0) = fun _ => 0 := by
      funext p
      rw [if_neg]
      rintro ⟨-, h2⟩
      exact h (Int.ModEq.symm (Int.modEq_iff_dvd.2 ⟨p.1, by linarith⟩))
    rw [this]
    exact hasSum_zero

theorem sum_div_point {m : ℕ} (hm : m ≠ 0) (A e : ℤ) (v : ℂ) :
    ∑ d ∈ m.divisors, ((if e = (d : ℤ) ∧ A = ((m / d : ℕ) : ℤ) then v else 0) +
      (if e = -(d : ℤ) ∧ A = -((m / d : ℕ) : ℤ) then v else 0)) = if A * e = m then v else 0 := by
  have key : ∀ d ∈ m.divisors, (((m / d : ℕ) : ℤ)) * d = m ∧ 0 < (d : ℤ) := fun d hd => by
    refine ⟨?_, by exact_mod_cast Nat.pos_of_mem_divisors hd⟩
    exact_mod_cast Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)
  split_ifs with h
  · have hd : e.natAbs ∈ m.divisors := by
      rw [Nat.mem_divisors]
      refine ⟨?_, hm⟩
      rw [← Int.natCast_dvd_natCast, Int.natAbs_dvd]
      exact ⟨A, by rw [← h, mul_comm]⟩
    rw [Finset.sum_eq_single_of_mem _ hd]
    · obtain ⟨k1, k2⟩ := key _ hd
      generalize ((m / e.natAbs : ℕ) : ℤ) = B at *
      rcases Int.natAbs_eq e with he | he
      · rw [← he] at k1 k2 ⊢
        have : A = B := mul_right_cancel₀ k2.ne' (by rw [h, k1])
        rw [if_pos ⟨rfl, this⟩, if_neg (by omega), add_zero]
      · have he' : (e.natAbs : ℤ) = -e := by omega
        rw [he'] at k1 k2 ⊢
        have : A = -B := mul_right_cancel₀ (b := e) (by omega) (by rw [h, ← k1]; ring)
        rw [if_neg (by omega), if_pos ⟨by ring, this⟩, zero_add]
    · intro d _ hne
      rw [if_neg (by omega), if_neg (by omega), add_zero]
  · refine Finset.sum_eq_zero fun d hd => ?_
    obtain ⟨k1, k2⟩ := key _ hd
    rw [if_neg, if_neg, add_zero]
    · rintro ⟨h1, h2⟩
      exact h (by rw [h1, h2, ← k1]; ring)
    · rintro ⟨h1, h2⟩
      exact h (by rw [h1, h2, ← k1])

theorem fTerm_eq (j : ℕ) {M : ℕ} (hM : 0 < M) (a b : ℤ) (τ : ℍ) (p : ℤ × ℤ) :
    fTerm j ![(a : ℚ) / M, (b : ℚ) / M] τ p =
      if 0 < (a + M * p.1) * p.2 then
        (Int.sign p.2 : ℂ) * (((a + M * p.1 : ℤ) : ℂ) / M) ^ (j - 1) * ee (1 / (M : ℂ)) ^ (b * p.2) *
          ee ((((a + M * p.1) * p.2 : ℤ) : ℂ) * τ / M)
      else 0 := by
  have hQ : (0 : ℚ) < M := by exact_mod_cast hM
  have hC : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hc : (0 < ((a : ℚ) / M + p.1) * p.2) ↔ 0 < (a + M * p.1) * p.2 := by
    have : ((a : ℚ) / M + p.1) * p.2 = (((a + M * p.1) * p.2 : ℤ) : ℚ) / M := by
      push_cast; field_simp
    rw [this, div_pos_iff_of_pos_right hQ, Int.cast_pos]
  unfold fTerm
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hc]
  split_ifs with h
  · rw [← ee_int_mul', mul_right_comm]
    congr 1
    · congr 1
      · congr 2
        push_cast; field_simp
      · congr 1
        push_cast; ring
    · congr 1
      push_cast; field_simp
  · rfl

theorem hasSum_fibre (j : ℕ) {M : ℕ} (hM : 0 < M) (a b : ℤ) (τ : ℍ) (m : ℕ) :
    HasSum (Set.indicator ((fun p : ℤ × ℤ => ((a + M * p.1) * p.2).toNat) ⁻¹' {m})
        (fTerm j ![(a : ℚ) / M, (b : ℚ) / M] τ))
      ((if m = 0 then 0 else coefPos j M (ee (1 / (M : ℂ))) a b m) *
        Complex.exp (2 * Real.pi * Complex.I * m * τ / M)) := by
  split_ifs with hm
  · have : Set.indicator ((fun p : ℤ × ℤ => ((a + M * p.1) * p.2).toNat) ⁻¹' {m})
        (fTerm j ![(a : ℚ) / M, (b : ℚ) / M] τ) = fun _ => 0 := by
      funext p
      rw [Set.indicator_apply_eq_zero]
      intro hp
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hp
      rw [fTerm_eq j hM, if_neg (by omega)]
    rw [this, zero_mul]
    exact hasSum_zero
  · set E := Complex.exp (2 * Real.pi * Complex.I * m * τ / M) with hE
    let w : ℤ → ℤ → ℂ := fun A e => (Int.sign e : ℂ) * ((A : ℂ) / M) ^ (j - 1) * ee (1 / (M : ℂ)) ^ (b * e) * E
    have h1 := hasSum_sum (s := m.divisors) fun d _ =>
      (hasSum_point hM a ((m / d : ℕ) : ℤ) (d : ℤ) w).add (hasSum_point hM a (-((m / d : ℕ) : ℤ)) (-(d : ℤ)) w)
    convert (preTransparency := .reducible) h1 using 1
    · funext p
      classical
      rw [sum_div_point hm, Set.indicator_apply, fTerm_eq j hM]
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      by_cases h : (a + M * p.1) * p.2 = m
      · rw [if_pos (by omega), if_pos (by omega), if_pos h, h]
        simp only [w, hE, ee]
        congr 2
        push_cast; ring
      · rw [if_neg (by omega), if_neg h]
    · unfold coefPos
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun d hd => ?_
      have hd' : (0 : ℤ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
      have s1 : Int.sign (d : ℤ) = 1 := Int.sign_eq_one_of_pos hd'
      simp only [w, Int.sign_neg, s1, mul_neg, Int.cast_neg, Int.cast_one, Int.cast_natCast, neg_div]
      split_ifs <;> ring

theorem fract_eq {M : ℕ} (a : ℤ) : Int.fract ((a : ℚ) / M) = frc M a := by
  unfold frc
  exact Int.fract_div_intCast_eq_div_intCast_mod

theorem eisensteinFxConstantTerm_rationalIndex_eq (j : ℕ) {M : ℕ} (hM : 0 < M) (a b : ℤ) :
    f0 j ![(a : ℚ) / M, (b : ℚ) / M] = const0 j M (ee (1 / (M : ℂ))) a b := by
  have hQ : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have h0 : frc M a = 0 ↔ (M : ℤ) ∣ a := by
    unfold frc
    rw [div_eq_zero_iff, or_iff_left hQ, Int.cast_eq_zero, Int.dvd_iff_emod_eq_zero]
  have he : ee ((((b : ℚ) / M : ℚ)) : ℂ) = ee (1 / (M : ℂ)) ^ b := by
    rw [← ee_int_mul']; congr 1; push_cast; ring
  unfold f0 const0
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, fract_eq, h0, he]
  split_ifs
  · rfl
  · push_cast; ring
  · push_cast; ring

theorem hasQ_F (j : ℕ) {M : ℕ} (hM : 0 < M) (a b : ℤ) :
    HasQ M (F j ![(a : ℚ) / M, (b : ℚ) / M]) (eisF j M (ee (1 / (M : ℂ))) a b) := by
  have h1 : HasQ M (fun τ => ∑' p : ℤ × ℤ, fTerm j ![(a : ℚ) / M, (b : ℚ) / M] τ p)
      (fun m => if m = 0 then 0 else coefPos j M (ee (1 / (M : ℂ))) a b m) := fun τ => by
    have := (Model.summable_fTerm j ![(a : ℚ) / M, (b : ℚ) / M] τ).hasSum.tsum_fiberwise
      (fun p : ℤ × ℤ => ((a + M * p.1) * p.2).toNat)
    have e : ∀ m : ℕ, ∑' q : ((fun p : ℤ × ℤ => ((a + M * p.1) * p.2).toNat) ⁻¹' {m}),
        fTerm j ![(a : ℚ) / M, (b : ℚ) / M] τ q = _ := fun m => by
      rw [tsum_subtype, (hasSum_fibre j hM a b τ m).tsum_eq]
    simpa only [e] using this
  have h2 := (HasQ.const M (f0 j ![(a : ℚ) / M, (b : ℚ) / M])).add h1
  have e : eisF j M (ee (1 / (M : ℂ))) a b = fun n => (if n = 0 then f0 j ![(a : ℚ) / M, (b : ℚ) / M] else 0) +
      (if n = 0 then 0 else coefPos j M (ee (1 / (M : ℂ))) a b n) := by
    funext n
    unfold eisF
    split_ifs
    · rw [eisensteinFxConstantTerm_rationalIndex_eq j hM, add_zero]
    · rw [zero_add]
  rw [e]
  exact h2

theorem hasQ_cF_weight (c j : ℕ) {M : ℕ} (hM : 0 < M) (a b : ℤ) :
    HasQ M (cF c j ![(a : ℚ) / M, (b : ℚ) / M]) (smF (c : ℤ) j M (ee (1 / (M : ℂ))) a b) := by
  have hx : c • ![(a : ℚ) / M, (b : ℚ) / M] = ![(((c : ℤ) * a : ℤ) : ℚ) / M, (((c : ℤ) * b : ℤ) : ℚ) / M] := by
    funext i
    fin_cases i <;> simp [mul_div_assoc]
  have := ((hasQ_F j hM a b).const_mul ((c : ℂ) ^ 2)).sub
    ((hasQ_F j hM (c * a) (c * b)).const_mul ((c : ℂ) ^ (2 - (j : ℤ))))
  rw [← hx] at this
  unfold smF
  simp only [Int.cast_natCast]
  exact this

theorem hasQ_cF_one : ∀ (c M : ℕ) (a b : ℤ), 0 < M → GlobalTheory.QFam.HasQ M (GlobalTheory.Sieg.cF c 1 ![(a : ℚ) / M, (b : ℚ) / M])
    (GlobalTheory.KummerEisensteinGalois.smF (c : ℤ) 1 M (GlobalTheory.Sieg.ee (1 / (M : ℂ))) a b) :=
  fun c _ a b hM => hasQ_cF_weight c 1 hM a b

end GlobalTheory.Sieg.EisQ
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasQExpansionSmoothedEisensteinFxWeightOneStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasQExpansion_smoothedEisensteinFx_weightOne : ∀ (c M : ℕ) (a b : ℤ), 0 < M → GlobalTheory.QFam.HasQ M (GlobalTheory.Sieg.cF c 1 ![(a : ℚ) / M, (b : ℚ) / M]) (GlobalTheory.KummerEisensteinGalois.smF (c : ℤ) 1 M (GlobalTheory.Sieg.ee (1 / (M : ℂ))) a b) := by
  first | exact @GlobalTheory.Sieg.EisQ.hasQ_cF_one | exact GlobalTheory.Sieg.EisQ.hasQ_cF_one | (intros; apply GlobalTheory.Sieg.EisQ.hasQ_cF_one; all_goals assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitAtScaledArgumentTwoVariableExpansion
noncomputable section

open scoped UpperHalfPlane MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois GlobalTheory.Sieg GlobalTheory.QFam GlobalTheory.Sieg.DlogOne GlobalTheory.Sieg.Model

namespace GlobalTheory.SiegTwo

theorem map_smF {K K' : Type} [Field K] [CharZero K] [Field K'] [CharZero K'] (ε : K →+* K') (c : ℤ) (j M : ℕ) (ζ : K)
    (a b : ℤ) (n : ℕ) : ε (smF c j M ζ a b n) = smF c j M (ε ζ) a b n := by
  simp [smF, eisF, const0, coefPos, apply_ite ε, map_ofNat]

theorem map_finsum_zpow {Ω : Type} [Field Ω] (ε : Ω →+* ℂ) (θ : ℤ →₀ ℤ) (w : ℤ → ℤ → ℤ) (hw : ∀ k, w k 0 = 0) (ζ : Ω)
    (g : ℤ) : ε (∑ᶠ k : ℤ, ((w k (θ k) : ℤ) : Ω) * ζ ^ (g * k)) = θ.sum fun k n => ((w k n : ℤ) : ℂ) * (ε ζ ^ g) ^ k := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [finsum_eq_sum_of_support_subset (s := θ.support), map_sum]
  · simp [Finsupp.sum, zpow_mul]
  · intro k hk
    by_contra h
    have : θ k = 0 := by simpa using h
    exact hk (by simp [this, hw])

theorem coeff_sgN {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : GlobalTheory.KZ.Tower Ω ε) (c : ℕ) {N : ℕ}
    (hN : 0 < N) (M : ℕ) (a : ℤ × ℤ) (r : ℚ) :
    (X.exp (sgN X c N M a)).coeff (r * N) = (X.exp (siegel X c ![(a.1 : ℚ) / M, (a.2 : ℚ) / M])).coeff r := by
  have hd : (0 : ℤ) < (!![(N : ℤ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).det := by simpa [Matrix.det_fin_two] using hN
  have he : ∀ i k, ent (toGQ !![(N : ℤ), 0; 0, 1]) i k = ((!![(N : ℤ), 0; 0, 1] i k : ℤ) : ℚ) := fun i k => by
    simp only [ent, toGQ, dif_pos hd]; rfl
  have h := X.exp_upper (toGQ !![(N : ℤ), 0; 0, 1]) (by rw [he]; simp) (siegel X c ![(a.1 : ℚ) / M, (a.2 : ℚ) / M]) r
  rw [he, he, he] at h
  have h0 : eOm ε 0 = 1 := ε.injective (by rw [GalUnits.eps_eOm]; simp [ee])
  simpa [h0, sgN] using h

theorem sgN_two_variable : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (L N c : ℕ) (A₁ a₂ g : ℤ), 1 ≤ L → a₂ ≡ N * g [ZMOD (p : ℤ) ^ L] → (N : ℤ) ∣ a₂ → 0 < N → Nat.Coprime N p → 1 < c → Nat.Coprime c (6 * N * p) → ¬ (((N * p ^ L : ℕ) : ℤ) ∣ A₁) →
  ∃ θ : ℤ → ℤ → ℤ,
    (∀ r : ℤ, ∃ B : ℕ, ∀ k : ℤ, (B : ℤ) < |k| → θ k r = 0) ∧
    (∃ r0 : ℤ, ∀ k r : ℤ, r < r0 → θ k r = 0) ∧
    (∀ k r : ℤ, θ k r ≠ 0 → (p : ℤ) ^ L ∣ r - A₁ * k) ∧
    (∀ r : ℤ, (X.exp (sgN X c N (N * p ^ L) (A₁, a₂))).coeff ((r : ℚ) / (p : ℚ) ^ L) = ∑ᶠ k : ℤ, (θ k r : Ω) * zt ε p L ^ (g * k)) ∧
    (∀ r : ℤ, ∑ᶠ k : ℤ, ((k * θ k r : ℤ) : Ω) * zt ε p L ^ (g * k) =
      -∑ᶠ i : ℤ, (if 0 ≤ i then smF c 1 (N * p ^ L) (eOm ε (1 / ((N * p ^ L : ℕ) : ℚ))) A₁ a₂ i.toNat else 0) *
        (X.exp (sgN X c N (N * p ^ L) (A₁, a₂))).coeff (((r - i : ℤ) : ℚ) / (p : ℚ) ^ L)) ∧
    (∀ n : ℕ, smF c 1 (N * p ^ L) (eOm ε (1 / ((N * p ^ L : ℕ) : ℚ))) A₁ a₂ n ∈ Subring.closure {zt ε p L}) ∧
    (∃ r m : ℤ, (X.exp (sgN X c N (N * p ^ L) (A₁, a₂))).coeff ((r : ℚ) / (p : ℚ) ^ L) = zt ε p L ^ m ∨
      (X.exp (sgN X c N (N * p ^ L) (A₁, a₂))).coeff ((r : ℚ) / (p : ℚ) ^ L) = -(zt ε p L ^ m)) := by
  intro Ω _ _ _ ε X _ p hp _ L N c A₁ a₂ g _ hg hNa hN hNp hc hcop hA
  haveI : CharZero Ω := algebraRat.charZero Ω
  obtain ⟨g', rfl⟩ := hNa
  set M := N * p ^ L with hMd
  have hp0 : 0 < p := hp.out.pos
  have hM : 0 < M := by positivity
  have hMq : (M : ℚ) = N * p ^ L := by rw [hMd]; push_cast; rfl
  have hMc : (M : ℂ) = N * p ^ L := by rw [hMd]; push_cast; rfl
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp0.ne'
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp0.ne'
  have hc6 : Nat.Coprime c 6 := (Nat.Coprime.coprime_mul_right_right hcop).coprime_mul_right_right
  have hcM : Nat.Coprime c M := Nat.Coprime.mul_right (Nat.Coprime.coprime_mul_right_right hcop).coprime_mul_left_right
    (hcop.coprime_mul_left_right.pow_right L)
  have hA2 : ¬ (M : ℤ) ∣ A₁ * c := fun h =>
    hA ((Nat.isCoprime_iff_coprime.2 hcM.symm).dvd_of_dvd_mul_right h)
  have hadm : admitted c ![(A₁ : ℚ) / M, ((N * g' : ℤ) : ℚ) / M] := by
    refine ⟨hc, hc6, fun ⟨⟨m, hm⟩, _⟩ => hA2 ⟨m, ?_⟩⟩
    have hM' : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
    have : (A₁ : ℚ) * c = M * m := by
      rw [hm]; simp only [Matrix.cons_val_zero]; field_simp
    exact_mod_cast this
  have ez : ε (zt ε p L) = ee (1 / (p : ℂ) ^ L) := by rw [zt, GalUnits.eps_eOm]; push_cast; rfl
  have eM : ε (eOm ε (1 / (M : ℚ))) = ee (1 / (M : ℂ)) := by rw [GalUnits.eps_eOm]; push_cast; rfl
  have hz1 : ee (1 / (p : ℂ) ^ L) ^ ((p : ℤ) ^ L) = 1 := by
    rw [← ee_int_mul]; push_cast; rw [mul_one_div_cancel (pow_ne_zero _ hpc)]; simp [ee]
  have hv : ee (((N * g' : ℤ) : ℂ) / M) = ε (zt ε p L) ^ g := by
    have hco : IsCoprime ((p : ℤ) ^ L) (N : ℤ) := (Nat.isCoprime_iff_coprime.2 hNp.symm).pow_left
    obtain ⟨u, hu⟩ := hco.dvd_of_dvd_mul_left (by simpa only [← mul_sub] using hg.dvd : (p : ℤ) ^ L ∣ N * (g - g'))
    rw [ez, show g = g' + (p : ℤ) ^ L * u by linarith, zpow_add₀ (ee_ne_zero _), zpow_mul, hz1, one_zpow, mul_one,
      ← ee_int_mul, hMc]
    congr 1
    push_cast
    field_simp
  obtain ⟨k, a, b, qa, qb, hj, i, hi⟩ := sg_jets hM hadm hA hA2
  rw [hv] at hj hi
  obtain ⟨r1, r2⟩ := exp_of_hasQ X _ _ hM k a (SiegelMem.an_siegel_eq Ω ε X c _ hadm) qa
  set y := X.exp (sgN X c N M (A₁, N * g')) with hy
  have hco : ∀ r : ℤ, y.coeff ((r : ℚ) / (p : ℚ) ^ L) =
      (X.exp (siegel X c ![(A₁ : ℚ) / M, ((N * g' : ℤ) : ℚ) / M])).coeff ((r : ℚ) / M) := fun r => by
    rw [← coeff_sgN X c hN M (A₁, N * g')]
    congr 1
    rw [hMq]; field_simp
  have c1 : ∀ n : ℕ, ε (y.coeff (((k + n : ℤ) : ℚ) / (p : ℚ) ^ L)) = a n := fun n => by
    rw [hco, ← r1]; push_cast; rfl
  have c0 : ∀ r : ℤ, r < k → y.coeff ((r : ℚ) / (p : ℚ) ^ L) = 0 := fun r hr => by
    rw [hco]
    refine r2 _ fun n h => ?_
    rw [div_left_inj' (by exact_mod_cast hM.ne')] at h
    have : r = k + n := by exact_mod_cast h
    omega
  have hb := HasQ.coeff_unique hM qb (by
    simpa only [neg_mul, one_mul] using ((GlobalTheory.T.hasQExpansion_smoothedEisensteinFx_weightOne c M A₁ (N * g') hM).mul_conv qa).const_mul (-1))
  choose θ t1 t2 t3 using fun n => exists_finsupp (hj n)
  have cases : ∀ r : ℤ, r < k ∨ ∃ n : ℕ, r = k + n := fun r => by
    rcases lt_or_ge r k with h | h
    · exact Or.inl h
    · exact Or.inr ⟨(r - k).toNat, by omega⟩
  set Θ : ℤ → ℤ → ℤ := fun l r => if r < k then 0 else θ (r - k).toNat l with hΘ
  have T0 : ∀ l r, r < k → Θ l r = 0 := fun l r h => if_pos h
  have T1 : ∀ l (n : ℕ), Θ l (k + n) = θ n l := fun l n => by
    simp only [hΘ]
    rw [if_neg (by omega), add_sub_cancel_left, Int.toNat_natCast]
  refine ⟨Θ, fun r => ?_, ⟨k, T0⟩, fun l r h => ?_, fun r => ?_, fun r => ?_, ?_, k, g * i, ?_⟩
  · rcases cases r with h | ⟨n, rfl⟩
    · exact ⟨0, fun l _ => T0 l r h⟩
    · refine ⟨(θ n).support.sup Int.natAbs, fun l hl => ?_⟩
      rw [T1]
      by_contra h
      have := Finset.le_sup (f := Int.natAbs) (Finsupp.mem_support_iff.2 h)
      rw [Int.abs_eq_natAbs] at hl
      omega
  · rcases cases r with h' | ⟨n, rfl⟩
    · exact absurd (T0 l r h') h
    · rw [T1] at h
      refine Dvd.dvd.trans ⟨N, ?_⟩ (t1 n l h)
      rw [hMd]; push_cast; ring
  · rcases cases r with h' | ⟨n, rfl⟩
    · simp [c0 r h', T0 _ r h']
    · simp only [T1]
      apply ε.injective
      rw [c1, map_finsum_zpow ε (θ n) (fun _ m => m) (fun _ => rfl)]
      exact t2 n
  · rcases cases r with h' | ⟨n, rfl⟩
    · simp only [T0 _ r h', mul_zero, Int.cast_zero, zero_mul, finsum_zero]
      rw [finsum_eq_zero_of_forall_eq_zero, neg_zero]
      intro l
      split_ifs with h
      · rw [c0 _ (by omega), mul_zero]
      · rw [zero_mul]
    · simp only [T1]
      apply ε.injective
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_finsum_zpow ε (θ n) (fun l m => l * m) (fun _ => mul_zero _), ← t3 n,
        finsum_eq_sum_of_support_subset (s := (Finset.range (n + 1)).image (Nat.cast : ℕ → ℤ)),
        Finset.sum_image (fun _ _ _ _ h => by exact_mod_cast h), hb, map_neg, map_sum]
      · simp only [conv, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, neg_inj]
        refine Finset.sum_congr rfl fun l hl => ?_
        have := Finset.mem_range.1 hl
        rw [map_mul, if_pos (by omega), Int.toNat_natCast, map_smF, eM, ← c1,
          show k + n - l = k + ((n - l : ℕ) : ℤ) by omega]
      · intro l hl
        by_contra h
        apply hl
        dsimp only
        split_ifs with h1
        · rw [c0, mul_zero]
          by_contra h2
          exact h (Finset.mem_coe.2 (Finset.mem_image.2 ⟨l.toNat, Finset.mem_range.2 (by omega), by omega⟩))
        · rw [zero_mul]
  · have hz : eOm ε (1 / (M : ℚ)) ^ (N * g') = zt ε p L ^ g := ε.injective (by
      rw [map_zpow₀, map_zpow₀, ← hv, eM, ← ee_int_mul, mul_one_div])
    have m0 : zt ε p L ∈ Subring.closure {zt ε p L} := Subring.subset_closure rfl
    have m1 : (zt ε p L)⁻¹ ∈ Subring.closure {zt ε p L} := by
      have h1 : zt ε p L ^ (p ^ L) = 1 := ε.injective (by
        rw [map_pow, ez, map_one, ← zpow_natCast]; push_cast; exact hz1)
      have : (zt ε p L)⁻¹ = zt ε p L ^ (p ^ L - 1) := by
        apply inv_eq_of_mul_eq_one_left
        rw [← pow_succ, Nat.sub_add_cancel (pow_pos hp0 L), h1]
      rw [this]
      exact pow_mem m0 _
    have m2 : ∀ m : ℤ, zt ε p L ^ m ∈ Subring.closure {zt ε p L} := fun m => by
      rcases Int.eq_nat_or_neg m with ⟨m, rfl | rfl⟩
      · rw [zpow_natCast]; exact pow_mem m0 _
      · rw [zpow_neg, zpow_natCast, ← inv_pow]; exact pow_mem m1 _
    refine GlobalTheory.T.smoothedEisensteinFxCoefficientSeq_one_mem_subring Ω _ c M _ A₁ _ hM hcM hA (by rw [hz]; exact m2 _) ?_
    rw [zpow_neg, hz, ← zpow_neg]
    exact m2 _
  · have := c1 0
    rw [Nat.cast_zero, add_zero] at this
    refine hi.imp (fun h => ε.injective ?_) (fun h => ε.injective ?_)
    · rw [this, h, map_zpow₀, zpow_mul]
    · rw [this, h, map_neg, map_zpow₀, zpow_mul]

end GlobalTheory.SiegTwo
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitAtScaledArgumentTwoVariableExpansionStatement
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelUnitAtScaledArgument_twoVariableExpansion : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (L N c : ℕ) (A₁ a₂ g : ℤ), 1 ≤ L → a₂ ≡ N * g [ZMOD (p : ℤ) ^ L] → (N : ℤ) ∣ a₂ → 0 < N → Nat.Coprime N p → 1 < c → Nat.Coprime c (6 * N * p) → ¬ (((N * p ^ L : ℕ) : ℤ) ∣ A₁) →
  ∃ θ : ℤ → ℤ → ℤ,
    (∀ r : ℤ, ∃ B : ℕ, ∀ k : ℤ, (B : ℤ) < |k| → θ k r = 0) ∧
    (∃ r0 : ℤ, ∀ k r : ℤ, r < r0 → θ k r = 0) ∧
    (∀ k r : ℤ, θ k r ≠ 0 → (p : ℤ) ^ L ∣ r - A₁ * k) ∧
    (∀ r : ℤ, (X.exp (sgN X c N (N * p ^ L) (A₁, a₂))).coeff ((r : ℚ) / (p : ℚ) ^ L) = ∑ᶠ k : ℤ, (θ k r : Ω) * zt ε p L ^ (g * k)) ∧
    (∀ r : ℤ, ∑ᶠ k : ℤ, ((k * θ k r : ℤ) : Ω) * zt ε p L ^ (g * k) =
      -∑ᶠ i : ℤ, (if 0 ≤ i then smF c 1 (N * p ^ L) (eOm ε (1 / ((N * p ^ L : ℕ) : ℚ))) A₁ a₂ i.toNat else 0) *
        (X.exp (sgN X c N (N * p ^ L) (A₁, a₂))).coeff (((r - i : ℤ) : ℚ) / (p : ℚ) ^ L)) ∧
    (∀ n : ℕ, smF c 1 (N * p ^ L) (eOm ε (1 / ((N * p ^ L : ℕ) : ℚ))) A₁ a₂ n ∈ Subring.closure {zt ε p L}) ∧
    (∃ r m : ℤ, (X.exp (sgN X c N (N * p ^ L) (A₁, a₂))).coeff ((r : ℚ) / (p : ℚ) ^ L) = zt ε p L ^ m ∨
      (X.exp (sgN X c N (N * p ^ L) (A₁, a₂))).coeff ((r : ℚ) / (p : ℚ) ^ L) = -(zt ε p L ^ m)) := by
  first | exact @GlobalTheory.SiegTwo.sgN_two_variable | exact GlobalTheory.SiegTwo.sgN_two_variable | (intros; apply GlobalTheory.SiegTwo.sgN_two_variable ; all_goals assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelLogCoords
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.SiegLog

theorem supp_fin {R : Type} [Ring R] (θ : ℤ → ℤ) (f : ℤ → R) (h : ∃ B : ℕ, ∀ k : ℤ, (B : ℤ) < |k| → θ k = 0) :
    (Function.support (fun k : ℤ => (θ k : R) * f k)).Finite := by
  obtain ⟨B, hB⟩ := h
  refine (Set.finite_Icc (-(B : ℤ)) B).subset fun k hk => ?_
  by_contra hc
  apply hk
  have : (B : ℤ) < |k| := by
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hc
    rcases hc with hc | hc
    · rw [abs_of_neg (by omega)]; omega
    · rw [abs_of_pos (by omega)]; omega
  simp [hB k this]

end GlobalTheory.SiegLog

namespace GlobalTheory.SiegLog

theorem siegel_logCoords : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (A : ValuationSubring Ω), ((p : ℕ) : Ω) ∈ A.nonunits → ∀ (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl], IsClo p Ωl → ∀ (T : GlobalTheory.K5.Tower p Ωl) (j : Ω →+* Ωl), IsCusp ε A T j → ∀ (L : ℕ) (ψ : O0 p →+* Ωl) (io : KT X (p ^ L) →+* Ωl), 1 ≤ L → IsReb T L ψ → IsIo X A T j L ψ io → ∀ ι : On p L →ₐ[O0 p] Ωl, IsEmb T L ι →
  ∀ (N c : ℕ) (A₁ a₂ g : ℤ), a₂ ≡ N * g [ZMOD (p : ℤ) ^ L] → (N : ℤ) ∣ a₂ → 0 < N → Nat.Coprime N p → 1 < c → Nat.Coprime c (6 * N * p) → ¬ (((N * p ^ L : ℕ) : ℤ) ∣ A₁) →
  ∀ y : KT X (p ^ L), (y : X.K) = sgN X c N (N * p ^ L) (A₁, a₂) →
  ∃ (w : (On p L)ˣ) (α β : On p L) (z z' : Ωl), IsDlog p L (w : On p L) α β ∧ ι w = io y ∧ Ev ψ (fun r : ℤ => if 0 ≤ r then j (smF c 1 (N * p ^ L) (eOm ε (1 / ((N * p ^ L : ℕ) : ℚ))) A₁ a₂ r.toNat) else 0) z z' ∧
    Cong (p := p) L (ι α) (-(A₁ : Ωl) * z) ∧
    Cong (p := p) L ((p : Ωl) * ι β) (-(p : Ωl) * (g : Ωl) * z) := by
  intro Ω _ _ _ ε X hj p _ hp2 A hpA Ωl _ _ hclo T j hcusp L ψ io hL hreb hio ι hemb N c A₁ a₂ g ha₂ hNa hN hNp hc hc6 hNA y hy
  obtain ⟨θ, hB, hr0, hcong, hexp, hder, hsm, hunit⟩ := GlobalTheory.T.siegelUnitAtScaledArgument_twoVariableExpansion ε X hj p hp2 L N c A₁ a₂ g hL ha₂ hNa hN hNp hc hc6 hNA
  rw [← hy] at hexp hder hunit
  have hζ : j (zt ε p L) = T.ζ L := hcusp.root L
  have hzA : zt ε p L ∈ A := (hcusp.int _).2 (by rw [hζ]; exact GlobalTheory.KumDlog.int_zeta T L)
  have hzA' : (zt ε p L)⁻¹ ∈ A := (hcusp.int _).2 (by rw [map_inv₀, hζ]; exact GlobalTheory.KumDlog.int_zeta_inv T L)
  have hzpow : ∀ m : ℤ, zt ε p L ^ m ∈ A := by
    intro m
    rcases m with m | m
    · rw [Int.ofNat_eq_coe, zpow_natCast]; exact pow_mem hzA m
    · rw [zpow_negSucc, ← inv_pow]; exact pow_mem hzA' _
  have hpL : 0 < p ^ L := pow_pos (Fact.out : p.Prime).pos L
  have hcoef : ∀ s : ℚ, (X.exp (y : X.K)).coeff s ∈ A ∧
      (X.exp (y : X.K)).coeff s ∈ IntermediateField.adjoin ℚ (({zt ε p L} : Finset Ω) : Set Ω) := by
    intro s
    by_cases hs : (X.exp (y : X.K)).coeff s = 0
    · rw [hs]; exact ⟨zero_mem _, zero_mem _⟩
    have hden := ((KTExp.mem_KT_iff ε X (p ^ L) hpL (y : X.K)).1 y.2) s hs
    have hsr : s = (((s * ((p ^ L : ℕ) : ℚ)).num : ℤ) : ℚ) / (p : ℚ) ^ L := by
      have e := Rat.coe_int_num_of_den_eq_one hden
      have hp0 : (p : ℚ) ^ L ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
      rw [e, Nat.cast_pow, mul_div_assoc, div_self hp0, mul_one]
    rw [hsr, hexp]
    constructor
    · refine finsum_induction (· ∈ A) (zero_mem _) (fun _ _ => add_mem) fun k => ?_
      exact mul_mem (intCast_mem _ _) (hzpow _)
    · refine finsum_induction (· ∈ IntermediateField.adjoin ℚ (({zt ε p L} : Finset Ω) : Set Ω)) (zero_mem _)
        (fun _ _ => add_mem) fun k => ?_
      refine mul_mem (intCast_mem _ _) (zpow_mem (IntermediateField.subset_adjoin _ _ ?_) _)
      simp
  obtain ⟨x', hEv⟩ := hio.ev y {zt ε p L} hcoef
  obtain ⟨r0, hr0'⟩ := hr0
  set cU : ℤ → Ωl := fun r => j ((X.exp (y : X.K)).coeff ((r : ℚ) / (p : ℚ) ^ L)) with hcU
  set cE : ℤ → Ωl := fun r : ℤ => if 0 ≤ r then j (smF c 1 (N * p ^ L) (eOm ε (1 / ((N * p ^ L : ℕ) : ℚ))) A₁ a₂ r.toNat) else 0 with hcE
  have hjexp : ∀ r, cU r = ∑ᶠ k : ℤ, (θ k r : Ωl) * T.ζ L ^ (g * k) := by
    intro r
    simp only [hcU, hexp r]
    rw [map_finsum j (supp_fin (fun k => θ k r) (fun k => zt ε p L ^ (g * k)) (hB r))]
    simp only [map_mul, map_intCast, map_zpow₀, hζ]
  have hcE0 : ∀ r : ℤ, r < 0 → cE r = 0 := by
    intro r hr
    simp [hcE, not_le.2 hr]
  have hcEmem : ∀ r : ℤ, cE r ∈ Subring.closure {T.ζ L} := by
    intro r
    simp only [hcE]
    split_ifs
    · have h1 : j (smF c 1 (N * p ^ L) (eOm ε (1 / ((N * p ^ L : ℕ) : ℚ))) A₁ a₂ r.toNat) ∈ (Subring.closure {zt ε p L}).map j := Subring.mem_map.2 ⟨_, hsm r.toNat, rfl⟩
      rwa [RingHom.map_closure, Set.image_singleton, hζ] at h1
    · exact zero_mem _
  have hjder : ∀ r : ℤ, ∑ᶠ k : ℤ, ((k * θ k r : ℤ) : Ωl) * T.ζ L ^ (g * k) = -∑ᶠ i : ℤ, cE i * cU (r - i) := by
    intro r
    have hfin : (Function.support (fun i : ℤ => (if 0 ≤ i then smF c 1 (N * p ^ L) (eOm ε (1 / ((N * p ^ L : ℕ) : ℚ))) A₁ a₂ i.toNat else 0) *
        (X.exp (y : X.K)).coeff (((r - i : ℤ) : ℚ) / (p : ℚ) ^ L))).Finite := by
      refine (Set.finite_Icc 0 (r - r0)).subset fun i hi => ?_
      rw [Function.mem_support] at hi
      constructor
      · by_contra h0
        apply hi
        rw [if_neg h0, zero_mul]
      · by_contra h1
        apply hi
        have h2 : ∀ k, θ k (r - i) = 0 := fun k => hr0' k _ (by omega)
        rw [hexp (r - i)]
        simp [h2]
    have hB' : ∃ B : ℕ, ∀ k : ℤ, (B : ℤ) < |k| → k * θ k r = 0 := by
      obtain ⟨B, hb⟩ := hB r
      exact ⟨B, fun k hk => by rw [hb k hk, mul_zero]⟩
    have h := congrArg j (hder r)
    rw [map_neg, map_finsum j (supp_fin (fun k => k * θ k r) (fun k => zt ε p L ^ (g * k)) hB'), map_finsum j hfin] at h
    simp only [map_mul, map_intCast, map_zpow₀, hζ] at h
    rw [h]
    congr 1
    refine finsum_congr fun i => ?_
    simp only [hcE, hcU]
    split_ifs <;> simp
  have hzi : ∀ m : ℤ, IsInt (p := p) ((T.ζ L) ^ m) := by
    intro m
    rcases m with m | m
    · rw [Int.ofNat_eq_coe, zpow_natCast]; exact GlobalTheory.KumDlog.int_pow (GlobalTheory.KumDlog.int_zeta T L) m
    · rw [zpow_negSucc, ← inv_pow]; exact GlobalTheory.KumDlog.int_pow (GlobalTheory.KumDlog.int_zeta_inv T L) _
  obtain ⟨r, m, hrm⟩ := hunit
  have hcu : cU r ≠ 0 ∧ IsInt (p := p) (cU r)⁻¹ := by
    have hz0 : (T.ζ L) ^ m ≠ 0 := zpow_ne_zero _ (GlobalTheory.KumDlog.zeta_ne T L)
    rcases hrm with hrm | hrm
    · simp only [hcU, hrm, map_zpow₀, hζ]
      exact ⟨hz0, by rw [← zpow_neg]; exact hzi _⟩
    · simp only [hcU, hrm, map_neg, map_zpow₀, hζ]
      exact ⟨neg_ne_zero.2 hz0, by rw [inv_neg, ← zpow_neg]; exact GlobalTheory.KumDlog.int_neg (hzi _)⟩
  obtain ⟨hx0, hxi⟩ := (GlobalTheory.T.evalSeries_cong_iff_coeff_and_isUnit p Ωl hclo T L ψ hreb 0 cU (io y) x' hEv).2 ⟨r, hcu.1, hcu.2⟩
  have logCoords : ∀ (p : ℕ) [Fact p.Prime] (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl], IsClo p Ωl → ∀ (T : GlobalTheory.K5.Tower p Ωl) (L : ℕ) (ψ : O0 p →+* Ωl) (ι : On p L →ₐ[O0 p] Ωl), 1 ≤ L → IsReb T L ψ → IsEmb T L ι →
    ∀ (A₁ g : ℤ) (θ : ℤ → ℤ → ℤ) (cU cE : ℤ → Ωl) (x x' : Ωl),
    (∀ r : ℤ, ∃ B : ℕ, ∀ k : ℤ, (B : ℤ) < |k| → θ k r = 0) →
    (∃ r0 : ℤ, ∀ k r : ℤ, r < r0 → θ k r = 0) →
    (∀ k r : ℤ, θ k r ≠ 0 → (p : ℤ) ^ L ∣ r - A₁ * k) →
    (∀ r : ℤ, cU r = ∑ᶠ k : ℤ, (θ k r : Ωl) * T.ζ L ^ (g * k)) →
    (∀ r : ℤ, ∑ᶠ k : ℤ, ((k * θ k r : ℤ) : Ωl) * T.ζ L ^ (g * k) = -∑ᶠ i : ℤ, cE i * cU (r - i)) →
    (∀ r : ℤ, r < 0 → cE r = 0) → (∀ r : ℤ, cE r ∈ Subring.closure {T.ζ L}) →
    Ev ψ cU x x' → x ≠ 0 → IsInt (p := p) x⁻¹ →
    ∃ (w : (On p L)ˣ) (α β : On p L) (z z' : Ωl), IsDlog p L (w : On p L) α β ∧ ι w = x ∧ Ev ψ cE z z' ∧
      Cong (p := p) L (ι α) (-(A₁ : Ωl) * z) ∧
      Cong (p := p) L ((p : Ωl) * ι β) (-(p : Ωl) * (g : Ωl) * z) := by
    intro p hp Ω _ _ hc T L ψ ι hL hψ hι A₁ g θ cU cE x x' hB ⟨r0, h0⟩ hdiv hU hE hE0 hEm hx hx0 hxi
    have cong_sum : ∀ {L : ℕ} (S : Finset ℤ) (v : ℤ → ℤ) (e : ℤ → Ω) (he : ∀ k, IsInt (p := p) (e k)) (hv : ∀ k, (p : ℤ) ^ L ∣ v k),
        Cong (p := p) L (∑ k ∈ S, (v k : Ω) * e k) 0 := by
      intro L S v e he hv
      choose c hc using hv
      refine ⟨∑ k ∈ S, (c k : Ω) * e k, IsIntegral.sum _ fun k _ => IsIntegral.mul (Basic.isInt_intCast _) (he k), ?_⟩
      rw [sub_zero, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hc k]
      push_cast
      ring

    have cong_val : ∀ (hc : IsClo p Ω) {T : GlobalTheory.K5.Tower p Ω} {L : ℕ} {ψ : O0 p →+* Ω} (hψ : IsReb T L ψ) (g A : ℤ)
        (θ v : ℤ → ℤ → ℤ) (S : ℤ → Finset ℤ) (cU cE : ℤ → Ω) (x x' z z' y y' : Ω)
        (hv : ∀ k r, θ k r ≠ 0 → (p : ℤ) ^ L ∣ v k r - A * k)
        (hE : ∀ r, ∑ k ∈ S r, ((k * θ k r : ℤ) : Ω) * T.ζ L ^ (g * k) = -∑ᶠ i : ℤ, cE i * cU (r - i))
        (hx : Ev ψ cU x x') (hz : Ev ψ cE z z')
        (hy : Ev ψ (fun r => ∑ k ∈ S r, (v k r : Ω) * (θ k r : Ω) * T.ζ L ^ (g * k)) y y'),
        Cong (p := p) L (y + A * (z * x)) 0 := by
      intro hc T L ψ hψ g A θ v S cU cE x x' z z' y y' hv hE hx hz hy
      have hN : 0 < p ^ L := pow_pos hp.out.pos L
      have hζ : T.ζ L ^ p ^ L = 1 := (T.prim L).pow_eq_one
      obtain ⟨R1, R2⟩ := GlobalTheory.Glue.EvRing.ev_ring p Ω hc T L ψ hψ
      obtain ⟨U, rfl⟩ := (R2 _ _ _ hx).2.2.1
      obtain ⟨E, rfl⟩ := (R2 _ _ _ hz).2.2.1
      obtain ⟨Y, hY⟩ := (R2 _ _ _ hy).2.2.1
      have h1 := (R2 _ _ _ (R1 E U _ _ _ _ hz hx).1).2.2.2.2.1 (A : Ω) (Basic.isInt_intCast _) (GlobalTheory.Glue.SiegLoc.isAlgZp_int _)
      obtain ⟨V, hV⟩ := (R2 _ _ _ h1).2.2.1
      rw [← hV] at h1
      rw [← hY] at hy
      refine ((GlobalTheory.T.evalSeries_cong_iff_coeff_and_isUnit p Ω hc T L ψ hψ L _ _ _ (R1 Y V _ _ _ _ hy h1).2.1).1).2 fun r => ?_
      have e : (Y + V).coeff r = ∑ k ∈ S r, (((v k r - A * k) * θ k r : ℤ) : Ω) * T.ζ L ^ (g * k) := by
        rw [HahnSeries.coeff_add, hY, hV]
        simp only
        rw [GlobalTheory.Glue.SiegLoc.coeff_mul_finsum, ← neg_eq_iff_eq_neg.2 (hE r), mul_neg, Finset.mul_sum, ← sub_eq_add_neg, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        push_cast
        ring
      rw [e]
      refine cong_sum _ (fun k => (v k r - A * k) * θ k r) _ (fun k => ?_) fun k => ?_
      · rw [GlobalTheory.Glue.SiegLoc.zpow_emod hN hζ]
        exact IsIntegral.pow (GlobalTheory.Glue.EvTwist.isInt_of_pow hN hζ) _
      · by_cases h : θ k r = 0
        · simp [h]
        · exact Dvd.dvd.mul_right (hv k r h) _
    obtain ⟨m, rfl⟩ : ∃ m, L = m + 1 := ⟨L - 1, by omega⟩
    choose B hB using hB
    let S : ℤ → Finset ℤ := fun r => Finset.Icc (-(B r : ℤ)) (B r)
    have hS : ∀ (r : ℤ) (f : ℤ → Ω), (∀ k, θ k r = 0 → f k = 0) → ∑ᶠ k, f k = ∑ k ∈ S r, f k := fun r f hf =>
      finsum_eq_sum_of_support_subset _ fun k hk => by
        rw [Finset.mem_coe, Finset.mem_Icc, ← abs_le]
        exact not_lt.1 fun h => hk (hf k (hB r k h))
    have hE' : ∀ r, ∑ k ∈ S r, ((k * θ k r : ℤ) : Ω) * T.ζ (m + 1) ^ (g * k) = -∑ᶠ i : ℤ, cE i * cU (r - i) := fun r => by
      rw [← hE r, hS r _ fun k hk => by simp [hk]]
    obtain ⟨z, z', hz⟩ := GlobalTheory.Glue.SiegLoc.ev_cyc T (m + 1) ψ cE hE0 hEm
    obtain ⟨a, ha⟩ := GlobalTheory.Glue.SiegLoc.rep hψ g θ S r0 h0
    obtain ⟨y0, e0⟩ := ha fun _ _ => 1
    obtain ⟨y1, e1⟩ := ha fun _ j => j
    obtain ⟨y2, e2⟩ := ha fun i _ => i
    have hN : (0 : ℤ) < ((p ^ (m + 1) : ℕ) : ℤ) := by exact_mod_cast pow_pos hp.out.pos _
    have hmod : ∀ r : ℤ, (p : ℤ) ^ (m + 1) ∣ ((r % ((p ^ (m + 1) : ℕ) : ℤ)).toNat : ℤ) - r := fun r => by
      rw [Int.toNat_of_nonneg (Int.emod_nonneg r hN.ne')]
      have := Int.emod_add_mul_ediv r ((p ^ (m + 1) : ℕ) : ℤ)
      push_cast at this ⊢
      exact ⟨-(r / (p : ℤ) ^ (m + 1)), by linarith⟩
    obtain ⟨c1, hc1, k1⟩ := cong_val hc hψ g A₁ θ (fun _ r => ((r % ((p ^ (m + 1) : ℕ) : ℤ)).toNat : ℤ)) S cU cE x x' z z' _ _
      (fun k r h => by simpa using dvd_add (hmod r) (hdiv k r h)) hE' hx hz e1
    obtain ⟨c2, hc2, k2⟩ := cong_val hc hψ g g θ (fun k _ => ((g * k % ((p ^ (m + 1) : ℕ) : ℤ)).toNat : ℤ)) S cU cE x x' z z' _ _
      (fun k r _ => hmod _) hE' hx hz e2
    have hcU : cU = fun r => ∑ k ∈ S r, ((1 : ℤ) : Ω) * (θ k r : Ω) * T.ζ (m + 1) ^ (g * k) := funext fun r => by
      rw [hU r, hS r _ fun k hk => by simp [hk]]
      simp
    rw [← hcU] at e0
    have hxe := (GlobalTheory.T.evalSeriesAndDeriv_unique_of_coefficients p Ω hc T (m + 1) ψ hψ _ _ _ _ _ hx e0).1
    set w0 : On p (m + 1) := ∑ i : Fin (p ^ (m + 1)), ∑ j : Fin (p ^ (m + 1)),
      algebraMap (O0 p) (On p (m + 1)) (a i j) * xn p (m + 1) ^ (i : ℕ) * yn p (m + 1) ^ (j : ℕ) with hw0
    have hw : ι w0 = x := by
      rw [hxe, hw0]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_mul, map_pow, AlgHom.commutes, hι.1, hι.2, Int.cast_one, one_mul]
    obtain ⟨w, hwu⟩ := GlobalTheory.Glue.SiegLoc.isUnit_of_inv ι (GlobalTheory.T.towerLevelEmbedding_injective_range_adjoinRoots p Ω hc T (m + 1) hL ι hι).1 w0 (hw ▸ hx0) (hw ▸ hxi)
    obtain ⟨α, β, hd⟩ := GlobalTheory.K5.exists_isDlog p (m + 1) w
    obtain ⟨d1, d2⟩ := GlobalTheory.Glue.SiegLoc.coef m a w α β (hwu.trans hw0) hd
    obtain ⟨f1, d1⟩ := Ideal.mem_span_singleton'.1 d1
    obtain ⟨f2, d2⟩ := Ideal.mem_span_singleton'.1 d2
    replace d1 := congrArg ι d1
    replace d2 := congrArg ι d2
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, map_pow, map_sub, map_natCast, map_one, AlgHom.commutes, hι.1, hι.2, hwu, hw, GlobalTheory.Glue.SiegLoc.zeta_one] at d1 d2
    simp only [Int.cast_natCast] at k1 k2
    have hinv : x * x⁻¹ = 1 := mul_inv_cancel₀ hx0
    refine ⟨w, α, β, z, z', hd, hwu ▸ hw, hz, ⟨(ι f1 + c1) * x⁻¹,
      IsIntegral.mul (IsIntegral.add (GlobalTheory.Glue.SiegLoc.emb_int _ ι _) hc1) hxi, ?_⟩, ?_⟩
    · linear_combination x⁻¹ * k1 - x⁻¹ * d1 - (ι α + A₁ * z) * hinv
    · have hζ1 : T.ζ 1 - 1 ≠ 0 := sub_ne_zero.2 ((T.prim 1).ne_one (by simpa using hp.out.one_lt))
      have hpd := GlobalTheory.T.isInt_prime_div_rootOfUnity_sub_one_pow p Ω T 1 1 le_rfl (Nat.totient_pos.2 (pow_pos hp.out.pos _))
      rw [pow_one, div_eq_mul_inv] at hpd
      have hinv2 : (T.ζ 1 - 1) * (T.ζ 1 - 1)⁻¹ = 1 := mul_inv_cancel₀ hζ1
      have hpi : IsInt (p := p) (p : Ω) := by simpa using Basic.isInt_intCast (p := p) (Ω := Ω) (p : ℤ)
      refine ⟨(ι f2 * ((p : Ω) * (T.ζ 1 - 1)⁻¹) + p * c2) * x⁻¹,
        IsIntegral.mul (IsIntegral.add (IsIntegral.mul (GlobalTheory.Glue.SiegLoc.emb_int _ ι _) hpd) (IsIntegral.mul hpi hc2)) hxi, ?_⟩
      generalize (∑ i : Fin (p ^ (m + 1)), ∑ j : Fin (p ^ (m + 1)),
        ((i : ℕ) : Ω) * algebraMap (O0 p) Ω (a i j) * T.ζ (m + 1) ^ (i : ℕ) * T.qq (m + 1) ^ (j : ℕ)) = Y at k2 d2
      linear_combination (p * x⁻¹) * k2 - (p * x⁻¹ * (T.ζ 1 - 1)⁻¹) * d2 - (p * x⁻¹ * (x * ι β - Y)) * hinv2
        - (p * (ι β + g * z)) * hinv
  exact logCoords p Ωl hclo T L ψ ι hL hreb hemb A₁ g θ cU cE (io y) x' hB ⟨r0, hr0'⟩ hcong hjexp hjder hcE0 hcEmem hEv hx0 hxi

end GlobalTheory.SiegLog
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelLogCoordsStatement
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_logCoords_alt : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (A : ValuationSubring Ω), ((p : ℕ) : Ω) ∈ A.nonunits → ∀ (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl], IsClo p Ωl → ∀ (T : GlobalTheory.K5.Tower p Ωl) (j : Ω →+* Ωl), IsCusp ε A T j → ∀ (L : ℕ) (ψ : O0 p →+* Ωl) (io : KT X (p ^ L) →+* Ωl), 1 ≤ L → IsReb T L ψ → IsIo X A T j L ψ io → ∀ ι : On p L →ₐ[O0 p] Ωl, IsEmb T L ι →
  ∀ (N c : ℕ) (A₁ a₂ g : ℤ), a₂ ≡ N * g [ZMOD (p : ℤ) ^ L] → (N : ℤ) ∣ a₂ → 0 < N → Nat.Coprime N p → 1 < c → Nat.Coprime c (6 * N * p) → ¬ (((N * p ^ L : ℕ) : ℤ) ∣ A₁) →
  ∀ y : KT X (p ^ L), (y : X.K) = sgN X c N (N * p ^ L) (A₁, a₂) →
  ∃ (w : (On p L)ˣ) (α β : On p L) (z z' : Ωl), IsDlog p L (w : On p L) α β ∧ ι w = io y ∧ Ev ψ (fun r : ℤ => if 0 ≤ r then j (smF c 1 (N * p ^ L) (eOm ε (1 / ((N * p ^ L : ℕ) : ℚ))) A₁ a₂ r.toNat) else 0) z z' ∧
    Cong (p := p) L (ι α) (-(A₁ : Ωl) * z) ∧
    Cong (p := p) L ((p : Ωl) * ι β) (-(p : Ωl) * (g : Ωl) * z) := by
  exact @_root_.GlobalTheory.SiegLog.siegel_logCoords
end
