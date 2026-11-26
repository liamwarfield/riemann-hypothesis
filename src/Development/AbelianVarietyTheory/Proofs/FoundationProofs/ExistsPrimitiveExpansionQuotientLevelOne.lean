module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalCongruenceFunctionMemAdjoinJSiegelUnits

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitJPolynomialBoundedDenominators
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitJPolynomialBoundedDenominators
noncomputable section

open scoped MatrixGroups UpperHalfPlane
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois GlobalTheory.Sieg

namespace GlobalTheory.FracBd

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

def Good (F : HahnSeries ℚ Ω) : Prop :=
  ∃ (S : Finset Ω) (D : ℕ), 0 < D ∧ ∀ r, F.coeff r ∈ IntermediateField.adjoin ℚ (S : Set Ω) ∧
    IsIntegral ℤ ((D : Ω) * F.coeff r)

theorem isIntegral_natCast' (n : ℕ) : IsIntegral ℤ (n : Ω) := by
  simpa using (isIntegral_algebraMap (R := ℤ) (A := Ω) (x := (n : ℤ)))

theorem adj_mono {S S' : Finset Ω} (h : S ⊆ S') :
    IntermediateField.adjoin ℚ (S : Set Ω) ≤ IntermediateField.adjoin ℚ (S' : Set Ω) :=
  IntermediateField.adjoin.mono ℚ _ _ (Finset.coe_subset.2 h)

theorem good_add {F G : HahnSeries ℚ Ω} (hF : Good F) (hG : Good G) : Good (F + G) := by
  classical
  obtain ⟨S, D, hD, h⟩ := hF
  obtain ⟨S', D', hD', h'⟩ := hG
  refine ⟨S ∪ S', D * D', Nat.mul_pos hD hD', fun r => ⟨?_, ?_⟩⟩
  · rw [HahnSeries.coeff_add]
    exact add_mem (adj_mono Finset.subset_union_left (h r).1) (adj_mono Finset.subset_union_right (h' r).1)
  · rw [HahnSeries.coeff_add]
    have e : ((D * D' : ℕ) : Ω) * (F.coeff r + G.coeff r) =
        (D' : Ω) * ((D : Ω) * F.coeff r) + (D : Ω) * ((D' : Ω) * G.coeff r) := by push_cast; ring
    rw [e]
    exact ((isIntegral_natCast' D').mul (h r).2).add ((isIntegral_natCast' D).mul (h' r).2)

theorem good_mul {F G : HahnSeries ℚ Ω} (hF : Good F) (hG : Good G) : Good (F * G) := by
  classical
  obtain ⟨S, D, hD, h⟩ := hF
  obtain ⟨S', D', hD', h'⟩ := hG
  refine ⟨S ∪ S', D * D', Nat.mul_pos hD hD', fun r => ⟨?_, ?_⟩⟩
  · rw [HahnSeries.coeff_mul]
    exact sum_mem fun ij _ => mul_mem (adj_mono Finset.subset_union_left (h ij.1).1)
      (adj_mono Finset.subset_union_right (h' ij.2).1)
  · rw [HahnSeries.coeff_mul, Finset.mul_sum]
    refine IsIntegral.sum _ fun ij _ => ?_
    have e : ((D * D' : ℕ) : Ω) * (F.coeff ij.1 * G.coeff ij.2) =
        ((D : Ω) * F.coeff ij.1) * ((D' : Ω) * G.coeff ij.2) := by push_cast; ring
    rw [e]
    exact (h ij.1).2.mul (h' ij.2).2

theorem good_C [Algebra.IsAlgebraic ℚ Ω] (c : Ω) : Good (algebraMap Ω (HahnSeries ℚ Ω) c) := by
  classical
  have hc : IsAlgebraic ℤ c := (IsFractionRing.isAlgebraic_iff ℤ ℚ Ω).2 (Algebra.IsAlgebraic.isAlgebraic c)
  obtain ⟨y, hy0, hy⟩ := hc.exists_integral_multiple
  have hyc : IsIntegral ℤ ((y.natAbs : Ω) * c) := by
    rw [zsmul_eq_mul] at hy
    rcases Int.natAbs_eq y with e | e
    · rw [e] at hy; simpa using hy
    · rw [e] at hy
      have := hy.neg
      simpa using this
  refine ⟨{c}, y.natAbs, Int.natAbs_pos.2 hy0, fun r => ?_⟩
  have hcoef : (algebraMap Ω (HahnSeries ℚ Ω) c).coeff r = if r = 0 then c else 0 := by
    have e : algebraMap Ω (HahnSeries ℚ Ω) c = HahnSeries.C c := by
      rw [HahnSeries.algebraMap_apply']
      simp
    rw [e]
    by_cases hr : r = 0 <;> simp [hr]
  rw [hcoef]
  split_ifs
  · exact ⟨IntermediateField.subset_adjoin ℚ _ (by simp), hyc⟩
  · exact ⟨zero_mem _, by simpa using (isIntegral_zero : IsIntegral ℤ (0 : Ω))⟩

theorem good_int {F : HahnSeries ℚ Ω} (h : ∀ r, ∃ n : ℤ, F.coeff r = n) : Good F := by
  refine ⟨∅, 1, one_pos, fun r => ?_⟩
  obtain ⟨n, hn⟩ := h r
  rw [hn]
  refine ⟨intCast_mem _ n, ?_⟩
  simpa using (isIntegral_algebraMap (R := ℤ) (A := Ω) (x := n))

end GlobalTheory.FracBd

namespace GlobalTheory.FracBd

open GlobalTheory.QFam

theorem shift_hasQ {N : ℕ} {f : ℍ → ℂ} {a : ℕ → ℂ} (h : HasQ N f a) (d : ℕ) :
    HasQ N (fun τ => f τ * ee ((d : ℂ) / N * (τ : ℂ))) (fun n => if d ≤ n then a (n - d) else 0) := by
  intro τ
  have h1 := (h τ).mul_right (ee ((d : ℂ) / N * (τ : ℂ)))
  rw [← hasSum_nat_add_iff' d]
  have hz : ∑ i ∈ Finset.range d, (if d ≤ i then a (i - d) else 0) *
      Complex.exp (2 * Real.pi * Complex.I * (i : ℂ) * τ / N) = 0 :=
    Finset.sum_eq_zero fun i hi => by simp [not_le.2 (Finset.mem_range.1 hi)]
  rw [hz, sub_zero]
  convert h1 using 2 with n
  case e'_5 =>
    simp only [le_add_iff_nonneg_left, zero_le, if_true, Nat.add_sub_cancel, ee]
    rw [mul_assoc (a n), ← Complex.exp_add]
    congr 2
    push_cast
    ring
  all_goals rfl

theorem coeff_cmp {N : ℕ} (hN : 0 < N) {g : ℍ → ℂ} {k k' : ℤ} {A B : ℕ → ℂ}
    (hA : HasQ N (fun τ => g τ * ee (-((k : ℂ) / N) * (τ : ℂ))) A)
    (hB : HasQ N (fun τ => g τ * ee (-((k' : ℂ) / N) * (τ : ℂ))) B) (n : ℕ) :
    B n = 0 ∨ ∃ m, B n = A m := by
  rcases le_total k k' with hk | hk
  · obtain ⟨d, rfl⟩ : ∃ d : ℕ, k' = k + d := ⟨(k' - k).toNat, by omega⟩
    have hS := shift_hasQ hB d
    have e : (fun τ : ℍ => g τ * ee (-(((k + d : ℤ) : ℂ) / N) * (τ : ℂ)) * ee ((d : ℂ) / N * (τ : ℂ))) =
        fun τ => g τ * ee (-((k : ℂ) / N) * (τ : ℂ)) := by
      funext τ
      simp only [ee]
      rw [mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast
      ring
    rw [e] at hS
    have := HasQ.coeff_unique hN hA hS
    right
    refine ⟨n + d, ?_⟩
    rw [this]
    simp
  · obtain ⟨d, rfl⟩ : ∃ d : ℕ, k = k' + d := ⟨(k - k').toNat, by omega⟩
    have hS := shift_hasQ hA d
    have e : (fun τ : ℍ => g τ * ee (-(((k' + d : ℤ) : ℂ) / N) * (τ : ℂ)) * ee ((d : ℂ) / N * (τ : ℂ))) =
        fun τ => g τ * ee (-((k' : ℂ) / N) * (τ : ℂ)) := by
      funext τ
      simp only [ee]
      rw [mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast
      ring
    rw [e] at hS
    have := HasQ.coeff_unique hN hB hS
    rw [this]
    by_cases h : d ≤ n
    · right; exact ⟨n - d, by simp [h]⟩
    · left; simp [h]

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem eps_zeta [IsAlgClosed Ω] (ε : Ω →+* ℂ) {M : ℕ} (hM : 0 < M) :
    ε (eOm ε (1 / (M : ℚ))) = ee (1 / (M : ℂ)) := by
  have e : Complex.exp (2 * Real.pi * Complex.I * (((1 / (M : ℚ)) : ℚ) : ℂ)) = ee (1 / (M : ℂ)) := by
    unfold ee; push_cast; rfl
  unfold eOm
  rw [e]
  exact Function.invFun_eq (GlobalTheory.KZ.SiegelMem.mem_range_of_isIntegral ε (GlobalTheory.KZ.SiegelMem.isIntegral_ee hM))

theorem mem_closure_of_eps (ε : Ω →+* ℂ) {ζ x : Ω} (h : ε x ∈ Subring.closure {ε ζ}) : x ∈ Subring.closure {ζ} := by
  rw [← Set.image_singleton, ← RingHom.map_closure] at h
  obtain ⟨y, hy, hyx⟩ := Subring.mem_map.1 h
  rwa [← ε.injective hyx]

theorem admissible_of_integral_conj_le {M c : ℕ} (hM : 0 < M) (hc1 : 1 < c) (hc6 : Nat.Coprime c 6) (hcM : c ≡ 1 [MOD M]) {a b : ℤ}
    (hab : ¬ ((M : ℤ) ∣ a ∧ (M : ℤ) ∣ b)) : admitted c ![(a : ℚ) / M, (b : ℚ) / M] := by
  have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have hcop : IsCoprime (M : ℤ) (c : ℤ) := by
    rw [Nat.isCoprime_iff_coprime]
    have := hcM.gcd_eq
    rw [Nat.gcd_one_left] at this
    exact Nat.Coprime.symm this
  have key : ∀ x : ℤ, (c : ℚ) * ((x : ℚ) / M) ∈ Set.range ((↑) : ℤ → ℚ) → (M : ℤ) ∣ x := by
    rintro x ⟨m, hm⟩
    have h1 : (M : ℤ) * m = x * c := by
      have : (M : ℚ) * m = x * c := by rw [hm]; field_simp
      exact_mod_cast this
    exact hcop.dvd_of_dvd_mul_right ⟨m, h1.symm⟩
  exact ⟨hc1, hc6, fun ⟨h0, h1⟩ => hab ⟨key a h0, key b h1⟩⟩

end GlobalTheory.FracBd

namespace GlobalTheory.FracBd

open GlobalTheory.QFam

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem siegel_coeff [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) {M c : ℕ} (hM : 0 < M) (hc1 : 1 < c)
    (hc6 : Nat.Coprime c 6) (hcM : c ≡ 1 [MOD M]) (a b : ℤ) (hab : ¬ ((M : ℤ) ∣ a ∧ (M : ℤ) ∣ b)) (r : ℚ) :
    (X.exp (siegel X c ![(a : ℚ) / M, (b : ℚ) / M])).coeff r ∈ Subring.closure {eOm ε (1 / (M : ℚ))} := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hMz : (M : ℤ) ≠ 0 := by exact_mod_cast hM.ne'
  have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have hcop : Nat.Coprime c M := by
    have := hcM.gcd_eq
    rwa [Nat.gcd_one_left] at this
  set a0 : ℕ := (a % (M : ℤ)).toNat with ha0
  set b0 : ℕ := (b % (M : ℤ)).toNat with hb0
  have ha0' : (a0 : ℤ) = a % M := Int.toNat_of_nonneg (Int.emod_nonneg _ hMz)
  have hb0' : (b0 : ℤ) = b % M := Int.toNat_of_nonneg (Int.emod_nonneg _ hMz)
  have hlt : a0 < M := by
    have := Int.emod_lt_of_pos a (by exact_mod_cast hM : (0 : ℤ) < M)
    omega
  have hqa : (a : ℚ) = (M : ℚ) * ((a / (M : ℤ) : ℤ) : ℚ) + (a0 : ℚ) := by
    have h : a = (M : ℤ) * (a / (M : ℤ)) + (a0 : ℤ) := by linarith [Int.emod_def a (M : ℤ), ha0']
    exact_mod_cast h
  have hqb : (b : ℚ) = (M : ℚ) * ((b / (M : ℤ) : ℤ) : ℚ) + (b0 : ℚ) := by
    have h : b = (M : ℤ) * (b / (M : ℤ)) + (b0 : ℤ) := by linarith [Int.emod_def b (M : ℤ), hb0']
    exact_mod_cast h
  have hab0 : ¬ ((M : ℤ) ∣ (a0 : ℤ) ∧ (M : ℤ) ∣ (b0 : ℤ)) := by
    rintro ⟨h1, h2⟩
    apply hab
    rw [ha0'] at h1
    rw [hb0'] at h2
    exact ⟨(Int.dvd_iff_emod_eq_zero).2 (by have := Int.emod_emod_of_dvd a (dvd_refl (M : ℤ)); omega),
      (Int.dvd_iff_emod_eq_zero).2 (by have := Int.emod_emod_of_dvd b (dvd_refl (M : ℤ)); omega)⟩
  have hadm : admitted c ![(a0 : ℚ) / M, (b0 : ℚ) / M] := by
    have := admissible_of_integral_conj_le hM hc1 hc6 hcM hab0
    simpa using this
  set n : Fin 2 → ℤ := ![a / (M : ℤ), b / (M : ℤ)] with hn
  have hx : (![(a : ℚ) / M, (b : ℚ) / M] : Fin 2 → ℚ) = fun i => (![(a0 : ℚ) / M, (b0 : ℚ) / M] : Fin 2 → ℚ) i + n i := by
    funext i
    fin_cases i
    · simp only [n, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      rw [hqa]; field_simp; ring
    · simp only [n, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rw [hqb]; field_simp; ring
  have hsg : sgC c ![(a : ℚ) / M, (b : ℚ) / M] = sgC c ![(a0 : ℚ) / M, (b0 : ℚ) / M] := by
    funext z
    unfold sgC
    rw [hx]
    exact GlobalTheory.T.smoothedSiegelUnit_index_add_intVector c _ n _ hadm
  have hsie : siegel X c ![(a : ℚ) / M, (b : ℚ) / M] = siegel X c ![(a0 : ℚ) / M, (b0 : ℚ) / M] := by
    unfold siegel
    rw [hsg]
  rw [hsie]
  obtain ⟨k, A, hQ, hc, hz⟩ := GlobalTheory.T.siegel_unit_q_expansion_coefficients Ω ε X c M a0 b0 hM hlt hadm
  obtain ⟨k', hk'⟩ := GlobalTheory.T.smoothedSiegelUnit_qExpansion_coeffs_integral c M a0 hM hlt
  obtain ⟨A', hQ', -, -, hA', -⟩ := hk' b0 hadm
  have hAn : ∀ m, A m ∈ Subring.closure {eOm ε (1 / (M : ℚ))} := by
    intro m
    apply mem_closure_of_eps ε
    rw [eps_zeta ε hM]
    rcases coeff_cmp hM hQ' hQ m with h | ⟨m', h⟩
    · rw [show ε (A m) = 0 from h]; exact zero_mem _
    · rw [show ε (A m) = A' m' from h]; exact hA' hcop m'
  by_cases hr : ∃ m : ℕ, r = ((k : ℚ) + m) / M
  · obtain ⟨m, rfl⟩ := hr
    rw [hc m]
    exact hAn m
  · push_neg at hr
    rw [hz r hr]
    exact zero_mem _

end GlobalTheory.FracBd

namespace GlobalTheory.FracBd

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem good_closure {F : HahnSeries ℚ Ω} {ζ : Ω} {M : ℕ} (hM : 0 < M) (hζ : ζ ^ M = 1)
    (h : ∀ r, F.coeff r ∈ Subring.closure {ζ}) : Good F := by
  classical
  have hi : IsIntegral ℤ ζ := IsIntegral.of_pow hM (by rw [hζ]; exact isIntegral_one)
  have h1 : Subring.closure {ζ} ≤ (IntermediateField.adjoin ℚ (({ζ} : Finset Ω) : Set Ω)).toSubring :=
    Subring.closure_le.2 (by simpa using IntermediateField.subset_adjoin ℚ ({ζ} : Set Ω))
  have h2 : Subring.closure {ζ} ≤ (integralClosure ℤ Ω).toSubring :=
    Subring.closure_le.2 (by simpa [mem_integralClosure_iff] using hi)
  refine ⟨{ζ}, 1, one_pos, fun r => ⟨h1 (h r), ?_⟩⟩
  simpa [mem_integralClosure_iff] using h2 (h r)

theorem good_siegel [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) {M c : ℕ} (hM : 0 < M) (hc1 : 1 < c)
    (hc6 : Nat.Coprime c 6) (hcM : c ≡ 1 [MOD M]) (a b : ℤ) (hab : ¬ ((M : ℤ) ∣ a ∧ (M : ℤ) ∣ b))
    (γ : SL(2, ℤ)) : Good (X.exp (X.sl (ofSL γ) (siegel X c ![(a : ℚ) / M, (b : ℚ) / M]))) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  rw [GlobalTheory.T.siegelUnitInTower_sl_action_rowVector Ω ε X c _ γ (admissible_of_integral_conj_le hM hc1 hc6 hcM hab)]
  have hdet : (γ 0 0 : ℤ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at this
    exact this
  set a' : ℤ := a * γ 0 0 + b * γ 1 0 with ha'
  set b' : ℤ := a * γ 0 1 + b * γ 1 1 with hb'
  have hact : act ![(a : ℚ) / M, (b : ℚ) / M] γ = ![(a' : ℚ) / M, (b' : ℚ) / M] := by
    funext i
    fin_cases i
    · simp [act, Fin.sum_univ_two, a']
      field_simp
    · simp [act, Fin.sum_univ_two, b']
      field_simp
  have hab' : ¬ ((M : ℤ) ∣ a' ∧ (M : ℤ) ∣ b') := by
    rintro ⟨h1, h2⟩
    apply hab
    have ea : a = a' * γ 1 1 - b' * γ 1 0 := by simp only [a', b']; linear_combination (-a) * hdet
    have eb : b = b' * γ 0 0 - a' * γ 0 1 := by simp only [a', b']; linear_combination (-b) * hdet
    exact ⟨ea ▸ dvd_sub (dvd_mul_of_dvd_left h1 _) (dvd_mul_of_dvd_left h2 _),
      eb ▸ dvd_sub (dvd_mul_of_dvd_left h2 _) (dvd_mul_of_dvd_left h1 _)⟩
  rw [hact]
  have hζ : eOm ε (1 / (M : ℚ)) ^ M = 1 := by
    apply ε.injective
    rw [map_pow, eps_zeta ε hM, map_one]
    unfold ee
    rw [← Complex.exp_nat_mul]
    have : (M : ℂ) * (2 * Real.pi * Complex.I * (1 / M)) = 2 * Real.pi * Complex.I := by
      have : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
      field_simp
    rw [this, Complex.exp_two_pi_mul_I]
  exact good_closure hM hζ (siegel_coeff ε X hM hc1 hc6 hcM a' b' hab')

theorem frac_bd : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε),
    ∀ (M c : ℕ), 0 < M → 1 < c → Nat.Coprime c 6 → c ≡ 1 [MOD M] →
    ∀ f ∈ Algebra.adjoin Ω ({X.jK} ∪ {g | ∃ a b : ℤ, ¬ ((M : ℤ) ∣ a ∧ (M : ℤ) ∣ b) ∧
      g = siegel X c ![(a : ℚ) / M, (b : ℚ) / M]}), ∀ γ : SL(2, ℤ),
    (∃ (S : Finset Ω) (D : ℕ), 0 < D ∧ ∀ r, (X.exp (X.sl (ofSL γ) f)).coeff r ∈ IntermediateField.adjoin ℚ (S : Set Ω) ∧
      IsIntegral ℤ ((D : Ω) * (X.exp (X.sl (ofSL γ) f)).coeff r)) := by
  intro Ω _ _ _ ε X M c hM hc1 hc6 hcM f hf γ
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  show Good (X.exp (X.sl (ofSL γ) f))
  induction hf using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with hx | ⟨a, b, hab, rfl⟩
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      rw [X.j_inv γ]
      exact good_int X.j_exp.2.2
    · exact good_siegel ε X hM hc1 hc6 hcM a b hab γ
  | algebraMap r =>
    rw [AlgEquiv.commutes, AlgHom.commutes]
    exact good_C r
  | add x y _ _ hx hy =>
    rw [map_add (f := _), map_add (f := _)]
    exact good_add hx hy
  | mul x y _ _ hx hy =>
    rw [map_mul, map_mul]
    exact good_mul hx hy

end GlobalTheory.FracBd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitJPolynomialBoundedDenominatorsStatement
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelUnit_jPolynomial_bounded_denominators : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), ∀ (M c : ℕ), 0 < M → 1 < c → Nat.Coprime c 6 → c ≡ 1 [MOD M] → ∀ f ∈ Algebra.adjoin Ω ({X.jK} ∪ {g | ∃ a b : ℤ, ¬ ((M : ℤ) ∣ a ∧ (M : ℤ) ∣ b) ∧ g = siegel X c ![(a : ℚ) / M, (b : ℚ) / M]}), ∀ γ : SL(2, ℤ), (∃ (S : Finset Ω) (D : ℕ), 0 < D ∧ ∀ r, (X.exp (X.sl (ofSL γ) f)).coeff r ∈ IntermediateField.adjoin ℚ (S : Set Ω) ∧ IsIntegral ℤ ((D : Ω) * (X.exp (X.sl (ofSL γ) f)).coeff r)) := by
  first | exact @GlobalTheory.FracBd.frac_bd | exact GlobalTheory.FracBd.frac_bd | (intros; apply GlobalTheory.FracBd.frac_bd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimitiveConstMulOfBoundedExpansion
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimitiveConstMulOfBoundedExpansion
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.PrimConst

open NumberField

theorem exists_dividing {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω)
    {ι : Type} (c : ι → Ω) (E : IntermediateField ℚ Ω) [FiniteDimensional ℚ E] (D : ℕ) (hD : 0 < D)
    (hc : ∀ i, c i ∈ E ∧ IsIntegral ℤ ((D : Ω) * c i))
    (hne : ∃ i, c i ≠ 0) : ∃ i0, c i0 ≠ 0 ∧ ∀ i, c i * (c i0)⁻¹ ∈ A := by
  classical
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : NumberField E := by
    refine { to_charZero := inferInstance, to_finiteDimensional := ?_ }
    convert ‹FiniteDimensional ℚ E›
    exact Subsingleton.elim _ _
  have hmem : ∀ i, (D : Ω) * c i ∈ E := fun i => E.mul_mem (E.natCast_mem D) (hc i).1
  let f : ι → 𝓞 E := fun i => ⟨⟨(D : Ω) * c i, hmem i⟩, by
      rw [mem_integralClosure_iff]
      exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ E Ω) E.val.injective).1 (hc i).2⟩
  have hf : ∀ i, algebraMap (𝓞 E) Ω (f i) = (D : Ω) * c i := fun i => rfl
  obtain ⟨s0, hs0⟩ : ∃ s0 : Finset ι, ∀ i, f i ∈ Submodule.span ℤ ((s0.image f : Finset (𝓞 E)) : Set (𝓞 E)) := by
    have hN : IsNoetherian ℤ (𝓞 E) := inferInstance
    obtain ⟨M, ⟨s0, rfl⟩, hmax⟩ := set_has_maximal_iff_noetherian.2 hN
      (Set.range fun s : Finset ι => Submodule.span ℤ ((s.image f : Finset (𝓞 E)) : Set (𝓞 E))) (Set.range_nonempty _)
    refine ⟨s0, fun i => ?_⟩
    have hle : Submodule.span ℤ ((s0.image f : Finset (𝓞 E)) : Set (𝓞 E)) ≤
        Submodule.span ℤ (((insert i s0).image f : Finset (𝓞 E)) : Set (𝓞 E)) :=
      Submodule.span_mono (by intro y hy; simp only [Finset.coe_image, Finset.coe_insert] at hy ⊢; exact Set.image_mono (Set.subset_insert _ _) hy)
    have heq := eq_of_le_of_not_lt hle (hmax _ ⟨insert i s0, rfl⟩)
    rw [heq]; exact Submodule.subset_span (by simp)
  set v := A.valuation
  have hDv : v (D : Ω) ≠ 0 := by
    rw [Valuation.ne_zero_iff]; exact Nat.cast_ne_zero.2 hD.ne'
  have hint : ∀ z : ℤ, v (z : Ω) ≤ 1 := fun z => (A.valuation_le_one_iff _).2 (intCast_mem A z)
  obtain ⟨i1, hi1⟩ := hne
  have ht : (s0.filter (fun i => c i ≠ 0)).Nonempty := by
    by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hcon
    have hz : ∀ y ∈ s0.image f, y = 0 := by
      intro y hy
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hy
      have := hcon hj; push_neg at this
      ext; simp [f, this]
    have h1 := hs0 i1
    rw [Submodule.mem_span_finset] at h1
    obtain ⟨g, -, hg⟩ := h1
    rw [Finset.sum_eq_zero (fun y hy => by rw [hz y hy, smul_zero])] at hg
    have := congrArg (algebraMap (𝓞 E) Ω) hg
    rw [hf, map_zero] at this
    exact hi1 ((mul_eq_zero.1 this.symm).resolve_left (Nat.cast_ne_zero.2 hD.ne'))
  obtain ⟨i0, hi0t, hmax⟩ := (s0.filter (fun i => c i ≠ 0)).exists_max_image (fun i => v (c i)) ht
  have hi0 : c i0 ≠ 0 := (Finset.mem_filter.1 hi0t).2
  have hmax' : ∀ j ∈ s0, v (c j) ≤ v (c i0) := by
    intro j hj
    by_cases hcj : c j = 0
    · rw [hcj, map_zero]; exact zero_le'
    · exact hmax j (Finset.mem_filter.2 ⟨hj, hcj⟩)
  refine ⟨i0, hi0, fun i => ?_⟩
  have h1 := hs0 i
  rw [Submodule.mem_span_finset] at h1
  obtain ⟨g, -, hg⟩ := h1
  have h2 := congrArg (algebraMap (𝓞 E) Ω) hg
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hf, map_sum] at h2
  have hle : v ((D : Ω) * c i) ≤ v (D : Ω) * v (c i0) := by
    rw [← h2]
    refine Valuation.map_sum_le _ (fun y hy => ?_)
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hy
    rw [map_zsmul, hf, zsmul_eq_mul, map_mul, map_mul]
    calc v (g (f j) : Ω) * (v (D : Ω) * v (c j)) ≤ 1 * (v (D : Ω) * v (c j)) := by
          gcongr; exact hint _
      _ ≤ v (D : Ω) * v (c i0) := by rw [one_mul]; gcongr; exact hmax' j hj
  rw [map_mul] at hle
  have hle' : v (c i) ≤ v (c i0) := by
    calc v (c i) = (v (D : Ω))⁻¹ * (v (D : Ω) * v (c i)) := (inv_mul_cancel_left₀ hDv _).symm
      _ ≤ (v (D : Ω))⁻¹ * (v (D : Ω) * v (c i0)) := by gcongr
      _ = v (c i0) := inv_mul_cancel_left₀ hDv _
  have hv0 : v (c i0) ≠ 0 := (Valuation.ne_zero_iff _).2 hi0
  rw [← A.valuation_le_one_iff, map_mul, map_inv₀]
  calc v (c i) * (v (c i0))⁻¹ ≤ v (c i0) * (v (c i0))⁻¹ := by gcongr
    _ = 1 := mul_inv_cancel₀ hv0

theorem prim_of_bounded : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ a : X.K, a ≠ 0 → (∃ (S : Finset Ω) (D : ℕ), 0 < D ∧ ∀ r, (X.exp a).coeff r ∈ IntermediateField.adjoin ℚ (S : Set Ω) ∧ IsIntegral ℤ ((D : Ω) * (X.exp a).coeff r)) → ∃ κ : Ω, κ ≠ 0 ∧ Prim A (X.exp (algebraMap Ω X.K κ * a)) ∧ ∃ S : Finset Ω, ∀ r, (X.exp (algebraMap Ω X.K κ * a)).coeff r ∈ IntermediateField.adjoin ℚ (S : Set Ω) := by
  intro Ω _ _ _ ε X _ l _ A _ a ha hb
  obtain ⟨S, D, hD, hc⟩ := hb
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ (S : Set Ω)) :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  have hne : ∃ r, (X.exp a).coeff r ≠ 0 := by
    by_contra h
    push_neg at h
    have h0 : X.exp a = 0 := HahnSeries.ext (funext h)
    exact ha ((map_eq_zero_iff X.exp (RingHom.injective X.exp.toRingHom)).1 h0)
  obtain ⟨r0, h0, hA⟩ := exists_dividing A (fun r => (X.exp a).coeff r) _ D hD hc hne
  have hcoef : ∀ (κ : Ω) r, (X.exp (algebraMap Ω X.K κ * a)).coeff r = κ * (X.exp a).coeff r := by
    intro κ r
    rw [map_mul, AlgHom.commutes, HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, HahnSeries.ofPowerSeries_C, HahnSeries.C_mul_eq_smul,
      HahnSeries.coeff_smul, smul_eq_mul]
  refine ⟨((X.exp a).coeff r0)⁻¹, inv_ne_zero h0, ⟨fun r => ?_, r0, ?_⟩, S, fun r => ?_⟩
  · rw [hcoef, mul_comm]; exact hA r
  · rw [hcoef, inv_mul_cancel₀ h0, inv_one]
    exact ⟨one_ne_zero, one_mem A⟩
  · rw [hcoef]
    exact IntermediateField.mul_mem _ (IntermediateField.inv_mem _ (hc r0).1) (hc r).1

end GlobalTheory.PrimConst
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimitiveConstMulOfBoundedExpansionStatement
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitive_const_mul_of_bounded_expansion : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ a : X.K, a ≠ 0 → (∃ (S : Finset Ω) (D : ℕ), 0 < D ∧ ∀ r, (X.exp a).coeff r ∈ IntermediateField.adjoin ℚ (S : Set Ω) ∧ IsIntegral ℤ ((D : Ω) * (X.exp a).coeff r)) → ∃ κ : Ω, κ ≠ 0 ∧ Prim A (X.exp (algebraMap Ω X.K κ * a)) ∧ ∃ S : Finset Ω, ∀ r, (X.exp (algebraMap Ω X.K κ * a)).coeff r ∈ IntermediateField.adjoin ℚ (S : Set Ω) := by
  first | exact @GlobalTheory.PrimConst.prim_of_bounded | exact GlobalTheory.PrimConst.prim_of_bounded | (intros; apply GlobalTheory.PrimConst.prim_of_bounded <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPrimitiveExpansionQuotientLevelOne
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

noncomputable section

namespace GlobalTheory.FracPrim

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def Bd (X : Tower Ω ε) (x : X.K) : Prop :=
  ∃ (S : Finset Ω) (D : ℕ), 0 < D ∧ ∀ r, (X.exp x).coeff r ∈ IntermediateField.adjoin ℚ (S : Set Ω) ∧
    IsIntegral ℤ ((D : Ω) * (X.exp x).coeff r)

theorem bd_one (X : Tower Ω ε) : Bd X 1 := by
  refine ⟨∅, 1, one_pos, fun r => ?_⟩
  rw [map_one, HahnSeries.coeff_one]
  split_ifs
  · exact ⟨one_mem _, by simpa using isIntegral_one⟩
  · exact ⟨zero_mem _, by simpa using isIntegral_zero⟩

theorem bd_mul (X : Tower Ω ε) {x y : X.K} (hx : Bd X x) (hy : Bd X y) : Bd X (x * y) := by
  classical
  obtain ⟨S, D, hD, h⟩ := hx
  obtain ⟨S', D', hD', h'⟩ := hy
  refine ⟨S ∪ S', D * D', Nat.mul_pos hD hD', fun r => ?_⟩
  have hS : IntermediateField.adjoin ℚ (S : Set Ω) ≤ IntermediateField.adjoin ℚ ((S ∪ S' : Finset Ω) : Set Ω) :=
    IntermediateField.adjoin.mono _ _ _ (by rw [Finset.coe_union]; exact Set.subset_union_left)
  have hS' : IntermediateField.adjoin ℚ (S' : Set Ω) ≤ IntermediateField.adjoin ℚ ((S ∪ S' : Finset Ω) : Set Ω) :=
    IntermediateField.adjoin.mono _ _ _ (by rw [Finset.coe_union]; exact Set.subset_union_right)
  rw [map_mul, HahnSeries.coeff_mul]
  refine ⟨sum_mem (fun ij _ => mul_mem (hS (h ij.1).1) (hS' (h' ij.2).1)), ?_⟩
  rw [Finset.mul_sum]
  refine IsIntegral.sum _ (fun ij _ => ?_)
  have := (h ij.1).2.mul (h' ij.2).2
  convert this using 1
  push_cast; ring

theorem bd_prod (X : Tower Ω ε) {ι : Type} (s : Finset ι) (t : ι → X.K) (h : ∀ i ∈ s, Bd X (t i)) :
    Bd X (∏ i ∈ s, t i) :=
  Finset.prod_induction t (Bd X) (fun _ _ => bd_mul X) (bd_one X) h

end GlobalTheory.FracPrim

namespace GlobalTheory

open GlobalTheory.FracPrim

theorem exists_prim_frac_level_one : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ f : X.K, f ≠ 0 → ∃ (a b : X.K) (κ : Ω) (S : Finset Ω), κ ≠ 0 ∧ f * b = algebraMap Ω X.K κ * a ∧ Prim A (X.exp a) ∧ Prim A (X.exp b) ∧ (∀ γ : SL(2, ℤ), X.sl (ofSL γ) b = b) ∧ ∀ r, (X.exp a).coeff r ∈ IntermediateField.adjoin ℚ (S : Set Ω) ∧ (X.exp b).coeff r ∈ IntermediateField.adjoin ℚ (S : Set Ω) := by
  intro Ω _ _ _ ε X hj l _ A hl f hf
  classical
  obtain ⟨M, hM, hfM⟩ := X.level f
  have hc1 : 1 < 6 * M + 1 := by omega
  have hc6 : Nat.Coprime (6 * M + 1) 6 := by
    rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec]
    simp [Nat.add_mod]
  have hcM : 6 * M + 1 ≡ 1 [MOD M] :=
    ((Nat.modEq_iff_dvd' (by omega)).mpr (by simp)).symm
  have hfG := GlobalTheory.T.principalCongruenceFunction_mem_adjoin_j_siegelUnits ε X hj M (6 * M + 1) hM hc1 hc6 hcM f hfM
  obtain ⟨P, hP, Q, hQ, hPQ⟩ := IntermediateField.mem_adjoin_iff_div.mp hfG
  have hQ0 : Q ≠ 0 := by
    rintro rfl
    exact hf (by simpa using hPQ)
  have hfQ : f * Q = P := by rw [hPQ, div_mul_cancel₀ _ hQ0]
  obtain ⟨M', hM', hQM'⟩ := X.level Q
  haveI : NeZero M' := ⟨hM'.ne'⟩
  haveI : (CongruenceSubgroup.Gamma M').Normal := CongruenceSubgroup.Gamma_normal M'
  haveI : Fintype (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma M') := Fintype.ofFinite _
  have tq : ∀ g g' : SL(2, ℤ), g⁻¹ * g' ∈ CongruenceSubgroup.Gamma M' → X.sl (ofSL g') Q = X.sl (ofSL g) Q := by
    intro g g' h
    have hc : g * (g⁻¹ * g') * g⁻¹ ∈ CongruenceSubgroup.Gamma M' :=
      (CongruenceSubgroup.Gamma_normal M').conj_mem _ h g
    have e : g' = (g * (g⁻¹ * g') * g⁻¹) * g := by group
    rw [e, map_mul, X.sl_mul, hQM' _ hc]
  set t : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma M' → X.K := fun q => X.sl (ofSL q.out) Q with ht
  set b0 : X.K := ∏ q, t q with hb0def
  have hb0 : ∀ δ : SL(2, ℤ), X.sl (ofSL δ) b0 = b0 := by
    intro δ
    rw [hb0def, map_prod]
    refine Fintype.prod_equiv (Equiv.mulRight (δ : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma M')) _ _ (fun q => ?_)
    simp only [ht, Equiv.coe_mulRight]
    rw [← X.sl_mul, ← map_mul]
    symm
    apply tq
    rw [← QuotientGroup.eq]
    simp
  have ht1 : t 1 = Q := by
    simp only [ht]
    rw [tq 1 _ (by rw [← QuotientGroup.eq]; simp), map_one, X.sl_one]
  have hbd : ∀ γ : SL(2, ℤ), Bd X (X.sl (ofSL γ) Q) := fun γ =>
    GlobalTheory.T.siegelUnit_jPolynomial_bounded_denominators ε X M (6 * M + 1) hM hc1 hc6 hcM Q hQ γ
  have hPbd : Bd X P := by
    have := GlobalTheory.T.siegelUnit_jPolynomial_bounded_denominators ε X M (6 * M + 1) hM hc1 hc6 hcM P hP 1
    rwa [map_one, X.sl_one] at this
  set R : X.K := ∏ q ∈ Finset.univ.erase 1, t q with hR
  have hbR : b0 = R * Q := by
    rw [hb0def, hR, ← ht1, Finset.prod_erase_mul _ _ (Finset.mem_univ _)]
  have ha0 : f * b0 = P * R := by rw [hbR, ← hfQ]; ring
  have hb0bd : Bd X b0 := bd_prod X _ _ (fun q _ => hbd _)
  have ha0bd : Bd X (f * b0) := by
    rw [ha0]; exact bd_mul X hPbd (bd_prod X _ _ (fun q _ => hbd _))
  have hb0ne : b0 ≠ 0 := by
    rw [hb0def]
    exact Finset.prod_ne_zero_iff.mpr (fun q _ => (map_ne_zero _).mpr hQ0)
  have ha0ne : f * b0 ≠ 0 := mul_ne_zero hf hb0ne
  obtain ⟨κa, hκa, hPa, Sa, hSa⟩ := GlobalTheory.T.primitive_const_mul_of_bounded_expansion ε X hj l A hl (f * b0) ha0ne ha0bd
  obtain ⟨κb, hκb, hPb, Sb, hSb⟩ := GlobalTheory.T.primitive_const_mul_of_bounded_expansion ε X hj l A hl b0 hb0ne hb0bd
  refine ⟨algebraMap Ω X.K κa * (f * b0), algebraMap Ω X.K κb * b0, κb / κa, Sa ∪ Sb, div_ne_zero hκb hκa, ?_, hPa, hPb,
    ?_, fun r => ⟨?_, ?_⟩⟩
  · have e : algebraMap Ω X.K (κb / κa) * algebraMap Ω X.K κa = algebraMap Ω X.K κb := by
      rw [← map_mul, div_mul_cancel₀ _ hκa]
    rw [← mul_assoc (algebraMap Ω X.K (κb / κa)), e]; ring
  · intro γ
    rw [map_mul, AlgEquiv.commutes, hb0]
  · exact IntermediateField.adjoin.mono _ _ _ (by rw [Finset.coe_union]; exact Set.subset_union_left) (hSa r)
  · exact IntermediateField.adjoin.mono _ _ _ (by rw [Finset.coe_union]; exact Set.subset_union_right) (hSb r)

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPrimitiveExpansionQuotientLevelOneStatement
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primitive_expansion_quotient_level_one : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ f : X.K, f ≠ 0 → ∃ (a b : X.K) (κ : Ω) (S : Finset Ω), κ ≠ 0 ∧ f * b = algebraMap Ω X.K κ * a ∧ Prim A (X.exp a) ∧ Prim A (X.exp b) ∧ (∀ γ : SL(2, ℤ), X.sl (ofSL γ) b = b) ∧ ∀ r, (X.exp a).coeff r ∈ IntermediateField.adjoin ℚ (S : Set Ω) ∧ (X.exp b).coeff r ∈ IntermediateField.adjoin ℚ (S : Set Ω) := by
  first | exact @GlobalTheory.exists_prim_frac_level_one | exact GlobalTheory.exists_prim_frac_level_one | (intros; apply GlobalTheory.exists_prim_frac_level_one <;> assumption)
end
