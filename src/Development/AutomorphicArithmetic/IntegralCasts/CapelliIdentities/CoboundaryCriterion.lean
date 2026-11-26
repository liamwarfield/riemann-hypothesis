module

public import Mathlib

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CoboundaryCriterion
theorem UpperTheory.Reformulated.B.CoboundaryCriterion.isCoboundary_of_coprime :
    ∀ {R G M : Type} [inst : CommRing R]
    [inst_1 : Group G] [inst_2 : AddCommGroup M] [inst_3 : _root_.Module R M] (ρ : Representation R G M) {l : ℕ}
    {H C : Type} [inst_4 : Group H] [inst_5 : Group C] [Finite C] (i : H →* G) (f : H →* C),
    (Nat.card C).Coprime l →
      (∀ (m : M), l • m = (0 : M)) →
        ∀ (z : G → M),
          (∀ (g h : G), z (g * h) = z g + ((ρ : G → M →ₗ[R] M) g : M → M) (z h)) →
            (∀ (u : H), (f : H → C) u = (1 : C) → z ((i : H → G) u) = (0 : M)) →
              ∃ (b : M), ∀ (u : H), z ((i : H → G) u) = ((ρ : G → M →ₗ[R] M) ((i : H → G) u) : M → M) b - b := by
  intro R G M _ _ _ _ ρ l H C _ _ _ i f hcop hl z hz hker
  classical
  have hfac : ∀ u v : H, f u = f v → z (i u) = z (i v) := by
    intro u v huv
    have h1 : z (i (v⁻¹ * u)) = 0 := hker _ (by simp [huv])
    have h2 : i u = i v * i (v⁻¹ * u) := by simp
    rw [h2, hz, h1, map_zero, add_zero]
  haveI : Fintype f.range := Fintype.ofFinite _
  obtain ⟨s, hs⟩ : ∃ s : f.range → H, ∀ q, f (s q) = (q : C) :=
    ⟨fun q => q.2.choose, fun q => q.2.choose_spec⟩
  have hcop' : (Nat.card f.range).Coprime l :=
    Nat.Coprime.coprime_dvd_left (Subgroup.card_subgroup_dvd_card f.range) hcop
  set n := Nat.card f.range with hn
  set S : M := ∑ q : f.range, z (i (s q)) with hS
  have key : ∀ u : H, S = n • z (i u) + ρ (i u) S := by
    intro u
    have h1 : S = ∑ q : f.range, z (i (s (f.rangeRestrict u * q))) :=
      (Equiv.sum_comp (Equiv.mulLeft (f.rangeRestrict u)) (fun q => z (i (s q)))).symm
    have h2 : ∀ q : f.range,
        z (i (s (f.rangeRestrict u * q))) = z (i u) + ρ (i u) (z (i (s q))) := by
      intro q
      rw [← hz, ← map_mul]
      apply hfac
      simp [hs]
    calc S = ∑ q : f.range, (z (i u) + ρ (i u) (z (i (s q)))) := by
          rw [h1]; exact Finset.sum_congr rfl fun q _ => h2 q
      _ = n • z (i u) + ρ (i u) S := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [Finset.sum_add_distrib, Finset.sum_const, hS, map_sum, hn, Nat.card_eq_fintype_card,
            Finset.card_univ]
  obtain ⟨a, c, hac⟩ : IsCoprime (n : ℤ) (l : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop'
  refine ⟨-(a • S), fun u => ?_⟩
  have h3 : (n : ℤ) • z (i u) = S - ρ (i u) S := by
    rw [natCast_zsmul, eq_sub_iff_add_eq]; exact (key u).symm
  have h4 : (l : ℤ) • z (i u) = 0 := by rw [natCast_zsmul, hl]
  calc z (i u) = (a * n + c * l) • z (i u) := by rw [hac, one_smul]
    _ = a • (S - ρ (i u) S) := by rw [add_smul, mul_smul, mul_smul, h3, h4, smul_zero, add_zero]
    _ = ρ (i u) (-(a • S)) - -(a • S) := by
        rw [map_neg, map_zsmul, smul_sub]; abel
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SingleMemSubmodule
theorem UpperTheory.Reformulated.B.SingleMemSubmodule.single_mem :
    ∀ {K : Type} [inst : Field K] (d : Fin (3 : ℕ) → K),
    Function.Injective d →
      ∀ (W : Submodule K (Fin (3 : ℕ) → K)),
        (∀ v ∈ W, (Matrix.diagonal d).mulVec v ∈ W) →
          ∀ {v : Fin (3 : ℕ) → K}, v ∈ W → ∀ {i : Fin (3 : ℕ)}, v i ≠ (0 : K) → Pi.single i (1 : K) ∈ W := by
  intro K _ d hd W hW v hv i hi
  have step : ∀ (c : K), ∀ w ∈ W, (fun l => (d l - c) * w l) ∈ W := by
    intro c w hw
    have h := W.sub_mem (hW w hw) (W.smul_mem c hw)
    have e : (fun l => (d l - c) * w l) = (Matrix.diagonal d).mulVec w - c • w := by
      funext l
      simp only [Pi.sub_apply, Pi.smul_apply, Matrix.mulVec_diagonal, smul_eq_mul]
      ring
    rw [e]
    exact h
  have iter : ∀ s : Finset (Fin 3), (fun l => (∏ j ∈ s, (d l - d j)) * v l) ∈ W := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have e : (fun l => (∏ j ∈ (∅ : Finset (Fin 3)), (d l - d j)) * v l) = v := by
        funext l
        simp
      rw [e]
      exact hv
    | insert a s ha ih =>
      have h := step (d a) _ ih
      have e : (fun l => (∏ j ∈ insert a s, (d l - d j)) * v l)
          = fun l => (d l - d a) * ((∏ j ∈ s, (d l - d j)) * v l) := by
        funext l
        rw [Finset.prod_insert ha, mul_assoc]
      rw [e]
      exact h
  have hc : (∏ j ∈ Finset.univ.erase i, (d i - d j)) * v i ≠ 0 := by
    refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr ?_) hi
    intro j hj
    exact sub_ne_zero.mpr fun h => (Finset.ne_of_mem_erase hj) (hd h).symm
  have h := W.smul_mem ((∏ j ∈ Finset.univ.erase i, (d i - d j)) * v i)⁻¹
    (iter (Finset.univ.erase i))
  have e : (Pi.single i (1 : K) : Fin 3 → K)
      = ((∏ j ∈ Finset.univ.erase i, (d i - d j)) * v i)⁻¹ •
        (fun l => (∏ j ∈ Finset.univ.erase i, (d l - d j)) * v l) := by
    funext l
    rw [Pi.smul_apply, smul_eq_mul]
    by_cases hl : l = i
    · subst hl
      rw [Pi.single_eq_same, inv_mul_cancel₀ hc]
    · have hz : ∏ j ∈ Finset.univ.erase i, (d l - d j) = 0 :=
        Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hl, Finset.mem_univ l⟩) (sub_self _)
      rw [Pi.single_eq_of_ne hl, hz, zero_mul, mul_zero]
  rw [e]
  exact h
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntertwinerDiagonalization
private theorem UpperTheory.Reformulated.B.IntertwinerDiagonalization.of_intertwine {K : Type} [Field K]
    (M : GL (Fin 2) K) (D P : Matrix (Fin 2) (Fin 2) K) (hP : P.det ≠ 0)
    (h : (↑M : Matrix (Fin 2) (Fin 2) K) * P = P * D) :
    ∃ (g : GL (Fin 2) K), (↑(g * M * g⁻¹) : Matrix (Fin 2) (Fin 2) K) = D := by
  let u : GL (Fin 2) K := Matrix.GeneralLinearGroup.mkOfDetNeZero P hP
  have hu : (↑u : Matrix (Fin 2) (Fin 2) K) = P := rfl
  refine ⟨u⁻¹, ?_⟩
  rw [inv_inv, Units.val_mul, Units.val_mul, mul_assoc, hu, h, ← hu, ← mul_assoc,
    Units.inv_mul, one_mul]

theorem UpperTheory.Reformulated.B.IntertwinerDiagonalization.exists_diag :
    ∀ {K : Type} [inst : Field K]
    (M : GL (Fin (2 : ℕ)) K) {x : K},
    x ≠ (1 : K) →
      (↑M : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) K).trace = (1 : K) + x →
        (↑M : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) K).det = x →
          ∃ (g : GL (Fin (2 : ℕ)) K),
            (↑(g * M * g⁻¹) : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) K) = Matrix.diagonal ![(1 : K), x] := by
  intro K _ M x hx ht hd
  have hx' : x - 1 ≠ 0 := sub_ne_zero.mpr hx
  rw [Matrix.trace_fin_two] at ht
  rw [Matrix.det_fin_two] at hd
  obtain ⟨a, b, c, d, hM⟩ : ∃ a b c d : K, (↑M : Matrix (Fin 2) (Fin 2) K) = !![a, b; c, d] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  have hD : (Matrix.diagonal ![(1 : K), x] : Matrix (Fin 2) (Fin 2) K) = !![1, 0; 0, x] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [hM] at ht hd
  have ht' : a + d = 1 + x := by simpa using ht
  have hd' : a * d - b * c = x := by simpa using hd
  by_cases hc : c = 0
  · by_cases hb : b = 0
    · have hq : (a - 1) * (a - x) = 0 := by
        rw [hb] at hd'
        linear_combination a * ht' - hd'
      rcases mul_eq_zero.mp hq with h | h
      · have ha : a = 1 := sub_eq_zero.mp h
        have hdx : d = x := by linear_combination ht' - ha
        refine UpperTheory.Reformulated.B.IntertwinerDiagonalization.of_intertwine M _ 1 (by simp) ?_
        rw [hM, hD, ha, hb, hc, hdx, mul_one, one_mul]
      · have ha : a = x := sub_eq_zero.mp h
        have hdx : d = 1 := by linear_combination ht' - ha
        refine UpperTheory.Reformulated.B.IntertwinerDiagonalization.of_intertwine M _ !![0, 1; 1, 0] (by simp) ?_
        rw [hM, hD, ha, hb, hc, hdx, Matrix.mul_fin_two, Matrix.mul_fin_two]
        simp
    · refine UpperTheory.Reformulated.B.IntertwinerDiagonalization.of_intertwine M _ !![b, b; 1 - a, x - a] ?_ ?_
      · have : (!![b, b; 1 - a, x - a] : Matrix (Fin 2) (Fin 2) K).det = b * (x - 1) := by
          rw [Matrix.det_fin_two_of]; ring
        rw [this]
        exact mul_ne_zero hb hx'
      · rw [hM, hD, Matrix.mul_fin_two, Matrix.mul_fin_two]
        have e1 : a * b + b * (1 - a) = b * 1 + b * 0 := by ring
        have e2 : a * b + b * (x - a) = b * 0 + b * x := by ring
        have e3 : c * b + d * (1 - a) = (1 - a) * 1 + (x - a) * 0 := by
          linear_combination ht' - hd'
        have e4 : c * b + d * (x - a) = (1 - a) * 0 + (x - a) * x := by
          linear_combination x * ht' - hd'
        rw [e1, e2, e3, e4]
  · refine UpperTheory.Reformulated.B.IntertwinerDiagonalization.of_intertwine M _ !![1 - d, x - d; c, c] ?_ ?_
    · have : (!![1 - d, x - d; c, c] : Matrix (Fin 2) (Fin 2) K).det = -(c * (x - 1)) := by
        rw [Matrix.det_fin_two_of]; ring
      rw [this]
      exact neg_ne_zero.mpr (mul_ne_zero hc hx')
    · rw [hM, hD, Matrix.mul_fin_two, Matrix.mul_fin_two]
      have e1 : a * (1 - d) + b * c = (1 - d) * 1 + (x - d) * 0 := by
        linear_combination ht' - hd'
      have e2 : a * (x - d) + b * c = (1 - d) * 0 + (x - d) * x := by
        linear_combination x * ht' - hd'
      have e3 : c * (1 - d) + d * c = c * 1 + c * 0 := by ring
      have e4 : c * (x - d) + d * c = c * 0 + c * x := by ring
      rw [e1, e2, e3, e4]
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LayerApproximation
private theorem UpperTheory.Reformulated.B.LayerApproximation.first_layer {O R : Type} [CommRing O] [CommRing R]
    [Algebra O R] (m : Ideal R) (A : Subalgebra O R) (T : Set R)
    (h0 : ∀ (x : R), ∃ (a : O), x - algebraMap O R a ∈ m)
    (hT : ∀ t ∈ T, t ∈ A ∧ t ∈ m) (hm : m ≤ Ideal.span T ⊔ m ^ (2 : ℕ)) :
    ∀ x ∈ m, ∃ a ∈ A, a ∈ m ∧ x - a ∈ m ^ 2 := by
  have hspan : ∀ y ∈ Ideal.span T, ∃ a ∈ A, a ∈ m ∧ y - a ∈ m ^ 2 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem t ht => exact ⟨t, (hT t ht).1, (hT t ht).2, by simp⟩
    | zero => exact ⟨0, A.zero_mem, m.zero_mem, by simp⟩
    | add u v _ _ hu hv =>
      obtain ⟨a, ha, ham, hua⟩ := hu
      obtain ⟨b, hb, hbm, hvb⟩ := hv
      refine ⟨a + b, A.add_mem ha hb, m.add_mem ham hbm, ?_⟩
      have e : u + v - (a + b) = (u - a) + (v - b) := by ring
      rw [e]
      exact Ideal.add_mem _ hua hvb
    | smul r u _ hu =>
      obtain ⟨a, ha, ham, hua⟩ := hu
      obtain ⟨c, hc⟩ := h0 r
      refine ⟨algebraMap O R c * a, A.mul_mem (A.algebraMap_mem c) ha,
        m.mul_mem_left _ ham, ?_⟩
      have e : r • u - algebraMap O R c * a = r * (u - a) + (r - algebraMap O R c) * a := by
        rw [smul_eq_mul]; ring
      rw [e]
      refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ hua) ?_
      rw [pow_two]
      exact Ideal.mul_mem_mul hc ham
  intro x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp (hm hx)
  obtain ⟨a, ha, ham, hya⟩ := hspan y hy
  refine ⟨a, ha, ham, ?_⟩
  have e : y + z - a = (y - a) + z := by ring
  rw [e]
  exact Ideal.add_mem _ hya hz

private theorem UpperTheory.Reformulated.B.LayerApproximation.all_layers {O R : Type} [CommRing O] [CommRing R]
    [Algebra O R] (m : Ideal R) (A : Subalgebra O R)
    (h0 : ∀ (x : R), ∃ (a : O), x - algebraMap O R a ∈ m)
    (h1 : ∀ x ∈ m, ∃ a ∈ A, a ∈ m ∧ x - a ∈ m ^ 2) (N : ℕ) :
    ∀ x ∈ m ^ N, ∃ a ∈ A, a ∈ m ^ N ∧ x - a ∈ m ^ (N + 1) := by
  induction N with
  | zero =>
    intro x _
    obtain ⟨c, hc⟩ := h0 x
    exact ⟨algebraMap O R c, A.algebraMap_mem c, by simp, by simpa using hc⟩
  | succ N ih =>
    intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro y hy z hz
      obtain ⟨a, ha, ham, hya⟩ := ih y hy
      obtain ⟨b, hb, hbm, hzb⟩ := h1 z hz
      refine ⟨a * b, A.mul_mem ha hb, ?_, ?_⟩
      · rw [pow_succ]
        exact Ideal.mul_mem_mul ham hbm
      · have e : y * z - a * b = y * (z - b) + (y - a) * b := by ring
        rw [e]
        refine Ideal.add_mem _ ?_ ?_
        · rw [show N + 1 + 1 = N + 2 from rfl, pow_add]
          exact Ideal.mul_mem_mul hy hzb
        · rw [pow_succ]
          exact Ideal.mul_mem_mul hya hbm
    · rintro u v ⟨a, ha, ham, hua⟩ ⟨b, hb, hbm, hvb⟩
      refine ⟨a + b, A.add_mem ha hb, Ideal.add_mem _ ham hbm, ?_⟩
      have e : u + v - (a + b) = (u - a) + (v - b) := by ring
      rw [e]
      exact Ideal.add_mem _ hua hvb

theorem UpperTheory.Reformulated.B.LayerApproximation.co_ext_approx :
    ∀ {O R : Type} [inst : CommRing O] [inst_1 : CommRing R]
    [inst_2 : Algebra O R] (m : Ideal R) (A : Subalgebra O R) (T : Set R),
    (∀ (x : R), ∃ (a : O), x - (Algebra.algebraMap O R : O → R) a ∈ m) →
      (∀ t ∈ T, t ∈ A ∧ t ∈ m) → m ≤ Ideal.span T ⊔ m ^ (2 : ℕ) → ∀ (N : ℕ) (x : R), ∃ a ∈ A, x - a ∈ m ^ N := by
  intro O R _ _ _ m A T h0 hT hm N x
  have h1 := UpperTheory.Reformulated.B.LayerApproximation.first_layer m A T h0 hT hm
  induction N with
  | zero => exact ⟨0, A.zero_mem, by simp⟩
  | succ N ih =>
    obtain ⟨a, ha, hxa⟩ := ih
    obtain ⟨b, hb, -, hab⟩ := UpperTheory.Reformulated.B.LayerApproximation.all_layers m A h0 h1 N _ hxa
    refine ⟨a + b, A.add_mem ha hb, ?_⟩
    have e : x - (a + b) = x - a - b := by ring
    rw [e]
    exact hab
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormNatCastPrime
theorem UpperTheory.Reformulated.B.CapelliMiscellany.norm_natCast_prime :
    ∀ {p : ℕ} [inst : Fact (Nat.Prime p)], ‖(↑p : PadicAlgCl p)‖ = (↑p : ℝ)⁻¹ := by
  intro p _
  rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)) p]
  exact (PadicAlgCl.norm_extends p (p : ℚ_[p])).trans Padic.norm_p
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EpEqOneIff
theorem UpperTheory.Reformulated.B.Qj15.ep_eq_one_iff :
    ∀ (t : ℝ),
    Complex.exp ((2 : ℂ) * (↑Real.pi : ℂ) * Complex.I * (↑t : ℂ)) = (1 : ℂ) ↔ ∃ (n : ℤ), t = (↑n : ℝ) := by
  intro t
  rw [Complex.exp_eq_one_iff]
  refine exists_congr fun n => ?_
  rw [mul_comm ((n : ℤ) : ℂ), mul_right_inj' Complex.two_pi_I_ne_zero]
  exact_mod_cast Iff.rfl
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.UniAMulDiag
theorem UpperTheory.Reformulated.B.Qh23.uniA_mul_diag :
    ∀ {F : Type} [inst : Field F] {k : ℕ} (A B : Matrix (Fin k) (Fin k) F),
    A.BlockTriangular id → B.BlockTriangular id → ∀ (i : Fin k), (A * B) i i = A i i * B i i := by
  intro F _ k A B hA hB i
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun j _ hj => ?_) (fun h => absurd (Finset.mem_univ i) h)
  rcases lt_or_gt_of_ne hj with h | h
  · rw [hA (show id j < id i from h), zero_mul]
  · rw [hB (show id i < id j from h), mul_zero]
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjOfSq
theorem UpperTheory.Reformulated.B.Qh56.conj_of_sq :
    ∀ {w : ℂ} {q : ℕ},
    (0 : ℕ) < q → w ^ (2 : ℕ) = (↑q : ℂ) → (starRingEnd ℂ : ℂ → ℂ) w = w := by
  intro w q _ h
  have hs : ((Real.sqrt q : ℝ) : ℂ) ^ 2 = (q : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg q), Complex.ofReal_natCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (h.trans hs.symm) with hw | hw
  · rw [hw, Complex.conj_ofReal]
  · rw [hw, map_neg, Complex.conj_ofReal]
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CutSub
noncomputable def UpperTheory.Reformulated.B.FirstCoordinatesSubmodule.cutSub :
    (K : Type) → [inst : Field K] → [NumberField K] → (r : ℕ) → ℕ → Submodule (NumberField.RingOfIntegers K) (Fin r → K) :=
  fun K _ _ r n =>
    { carrier := {v : Fin r → K | ∀ i : Fin r, n ≤ (i : ℕ) → v i = 0}
      add_mem' := by
        intro v w hv hw i hi
        rw [Pi.add_apply, hv i hi, hw i hi, add_zero]
      zero_mem' := fun _ _ => rfl
      smul_mem' := by
        intro c v hv i hi
        rw [Pi.smul_apply, hv i hi, smul_zero] }
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ContinuousToZModPow
theorem UpperTheory.Reformulated.B.Yde3.continuous_toZModPow :
    ∀ {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)] (n : ℕ), Continuous (⇑(PadicInt.toZModPow n) : ℤ_[ℓ] → ZMod (ℓ ^ n)) := by
  intro ℓ hℓ n
  refine continuous_of_continuousAt_zero (PadicInt.toZModPow (p := ℓ) n) ?_
  have hpos : (0 : ℝ) < (ℓ : ℝ) ^ (-n : ℤ) :=
    zpow_pos (by exact_mod_cast hℓ.out.pos) _
  refine (continuousAt_const (y := (0 : ZMod (ℓ ^ n)))).congr ?_
  filter_upwards [Metric.closedBall_mem_nhds (0 : ℤ_[ℓ]) hpos] with x hx
  rw [mem_closedBall_zero_iff, PadicInt.norm_le_pow_iff_mem_span_pow,
    ← PadicInt.ker_toZModPow, RingHom.mem_ker] at hx
  exact hx.symm
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MulVecFixOfSupp
theorem UpperTheory.Reformulated.B.Qi20.mulVec_fix_of_supp :
    ∀ {m : ℕ} (y : Matrix (Fin m) (Fin m) ℂ) (v : Fin m → ℂ),
    (∀ (j : Fin m), v j ≠ (0 : ℂ) → ∀ (i : Fin m), y i j = if i = j then (1 : ℂ) else (0 : ℂ)) → y.mulVec v = v := by
  intro m y v h
  have key : y.mulVec v = (1 : Matrix (Fin m) (Fin m) ℂ).mulVec v := by
    funext i
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : v j = 0
    · rw [hj, mul_zero, mul_zero]
    · rw [h j hj i, Matrix.one_apply]
  rw [key, Matrix.one_mulVec]
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsSideTer
theorem UpperTheory.Reformulated.B.Yhd8.main :
    ∀ {n : ℕ} (g g' D : Matrix (Fin n) (Fin n) ℂ),
      g' * g = (1 : Matrix (Fin n) (Fin n) ℂ) →
        g * g' = (1 : Matrix (Fin n) (Fin n) ℂ) → ∀ (k : ℕ), (g' * D * g) ^ k = g' * D ^ k * g := by
  intro n g g' D h1 h2 k
  induction k with
  | zero => simp [h1]
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    calc g' * D ^ k * g * (g' * D * g) = g' * D ^ k * (g * g') * D * g := by
          simp only [Matrix.mul_assoc]
      _ = g' * (D ^ k * D) * g := by rw [h2, Matrix.mul_one]; simp only [Matrix.mul_assoc]
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DegLESum
noncomputable def UpperTheory.Reformulated.B.Qf21.degLE :
    {κ R : Type} → [inst : CommRing R] → Finset κ → ℕ → MvPolynomial κ R → Prop :=
    fun {κ R : Type} [CommRing R] (W : Finset κ) (n : ℕ) (F : MvPolynomial κ R) ↦
      ∀ (β : κ →₀ ℕ), AddMonoidAlgebra.coeff F β ≠ (0 : R) → ∑ k ∈ W, (β : κ → ℕ) k ≤ n

theorem UpperTheory.Reformulated.B.Qf21.degLE_sum.{u_1} :
    ∀ {κ R : Type} [inst : CommRing R] {α : Type u_1} {W : Finset κ} {n : ℕ} (s : Finset α) (F : α → MvPolynomial κ R),
      (∀ a ∈ s, UpperTheory.Reformulated.B.Qf21.degLE W n (F a)) → UpperTheory.Reformulated.B.Qf21.degLE W n (∑ a ∈ s, F a) := by
  intro κ R _ α W n s F h β hβ
  rw [MvPolynomial.coeff_sum] at hβ
  obtain ⟨a, ha, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hβ
  exact h a ha β hne
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PrecompleteOfPowLe
theorem UpperTheory.Reformulated.B.Qk41.precomplete_of_pow_le :
    ∀ {A : Type} [inst : CommRing A]
    {I J : Ideal A}, J ≤ I → ∀ {e : ℕ}, I ^ e ≤ J → ∀ [IsPrecomplete J A], IsPrecomplete I A := by
  intro A _ I J hJI e he hJ
  refine ⟨fun f hf => ?_⟩
  have h1 : ∀ m : ℕ, I ^ ((e + 1) * m) ≤ J ^ m := fun m => by
    rw [pow_mul]
    exact Ideal.pow_right_mono ((Ideal.pow_le_pow_right (Nat.le_succ e)).trans he) m
  obtain ⟨L, hL⟩ := IsPrecomplete.prec hJ (f := fun n => f ((e + 1) * n)) (fun {m n} hmn =>
    SModEq.mono (Submodule.smul_mono_left (h1 m)) (hf (Nat.mul_le_mul_left _ hmn)))
  refine ⟨L, fun n => ?_⟩
  exact (hf (Nat.le_mul_of_pos_left n (Nat.succ_pos e))).trans
    (SModEq.mono (Submodule.smul_mono_left (Ideal.pow_right_mono hJI n)) (hL n))
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ListEig
theorem UpperTheory.Reformulated.B.Qk12.list_eig :
    ∀ {M ι : Type} [inst : AddCommGroup M]
    [inst_1 : _root_.Module ℂ M] (L : ι → Module.End ℂ M) (c : ι → ℂ) (x : M) (l : List ι),
    (∀ i ∈ l, (L i : M → M) x = c i • x) → ((List.map L l).prod : M → M) x = (List.map c l).prod • x := by
  intro M ι _ _ L c x l
  induction l with
  | nil => intro _; simp
  | cons a l ih =>
    intro h
    have h1 : L a x = c a • x := h a List.mem_cons_self
    have h2 := ih (fun i hi => h i (List.mem_cons_of_mem a hi))
    rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, Module.End.mul_apply, h2,
      map_smul, h1, smul_smul, mul_comm]
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.BiHomSum
noncomputable def UpperTheory.Reformulated.B.Qf22.biHom :
    {K ι κ : Type} → [inst : Field K] → ℕ → MvPolynomial κ (MvPolynomial ι K) → Prop :=
    fun {K ι κ : Type} [Field K] (d : ℕ) (F : MvPolynomial κ (MvPolynomial ι K)) ↦
      ∀ (β : κ →₀ ℕ) (n : ι →₀ ℕ),
        AddMonoidAlgebra.coeff (AddMonoidAlgebra.coeff F β) n ≠ (0 : K) →
          (Finsupp.degree : (ι →₀ ℕ) → ℕ) n + (Finsupp.degree : (κ →₀ ℕ) → ℕ) β = d

theorem UpperTheory.Reformulated.B.Qf22.biHom_sum.{u_1} :
    ∀ {K ι κ : Type} [inst : Field K] [Fintype κ] {α : Type u_1} {d : ℕ} (s : Finset α)
      (F : α → MvPolynomial κ (MvPolynomial ι K)),
      (∀ a ∈ s, UpperTheory.Reformulated.B.Qf22.biHom d (F a)) → UpperTheory.Reformulated.B.Qf22.biHom d (∑ a ∈ s, F a) := by
  intro K ι κ _ _ α d s F h β n hne
  rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_sum] at hne
  obtain ⟨a, ha, hna⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  exact h a ha β n hna
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EvalSmulOfIsHomogeneous
theorem UpperTheory.Reformulated.B.HomogeneousEvalSmul.eval_smul_of_isHomogeneous :
    ∀ {σ : Type} [Fintype σ] {h : MvPolynomial σ ℂ} {d : ℕ},
      h.IsHomogeneous d →
        ∀ (t : ℂ) (v : σ → ℂ),
          (MvPolynomial.eval (t • v) : MvPolynomial σ ℂ → ℂ) h = t ^ d * (MvPolynomial.eval v : MvPolynomial σ ℂ → ℂ) h := by
  intro σ _ h d hh t v
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : ∑ i, m i = d := by
    have h1 := hh (MvPolynomial.mem_support_iff.mp hm)
    rw [← h1, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsRestLast
theorem UpperTheory.Reformulated.B.Yhd4.main :
    ∀ {G V : Type} [inst : Group G] [inst_1 : TopologicalSpace G] [ContinuousMul G] [inst_3 : AddCommGroup V]
      [inst_4 : _root_.Module ℂ V] (ρ : Representation ℂ G V) (v : V),
      {g : G | ((ρ : G → V →ₗ[ℂ] V) g : V → V) v = v} ∈ nhds (1 : G) →
        IsOpen {g : G | ((ρ : G → V →ₗ[ℂ] V) g : V → V) v = v} := by
  intro G V _ _ _ _ _ ρ v hS
  rw [isOpen_iff_mem_nhds]
  intro g hg
  simp only [Set.mem_ofPred_eq] at hg
  have hc : Filter.Tendsto (fun h : G => g⁻¹ * h) (nhds g) (nhds 1) := by
    have := ((continuous_const_mul g⁻¹ : Continuous (fun h : G => g⁻¹ * h)).tendsto g)
    simpa using this
  filter_upwards [hc hS] with h hh
  simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hh ⊢
  have : h = g * (g⁻¹ * h) := by group
  rw [this, map_mul, Module.End.mul_apply, hh, hg]
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FirstStatementC
theorem UpperTheory.Reformulated.B.OneAddPowLeTwoPowMul.main :
    ∀ (t : ℝ), (0 : ℝ) ≤ t → ∀ (N : ℕ), ((1 : ℝ) + t) ^ N ≤ (2 : ℝ) ^ N * ((1 : ℝ) + t ^ N) := by
  intro t ht N
  have h1 : (1 : ℝ) + t ≤ 2 * max 1 t := by
    linarith [le_max_left (1 : ℝ) t, le_max_right (1 : ℝ) t]
  have h2 : ((1 : ℝ) + t) ^ N ≤ (2 * max 1 t) ^ N := pow_le_pow_left₀ (by linarith) h1 N
  rw [mul_pow] at h2
  have h3 : (max (1 : ℝ) t) ^ N ≤ 1 + t ^ N := by
    rcases le_total t 1 with h | h
    · rw [max_eq_left h, one_pow]
      have : (0 : ℝ) ≤ t ^ N := pow_nonneg ht N
      linarith
    · rw [max_eq_right h]
      linarith
  calc ((1 : ℝ) + t) ^ N ≤ 2 ^ N * (max 1 t) ^ N := h2
    _ ≤ 2 ^ N * (1 + t ^ N) := mul_le_mul_of_nonneg_left h3 (by positivity)
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsPermOfMapEq
theorem UpperTheory.Reformulated.B.Qh57.exists_perm_of_map_eq :
    ∀ {n : ℕ} (a b : Fin n → ℂ),
    Multiset.map a Finset.univ.val = Multiset.map b Finset.univ.val →
      ∃ (e : Equiv.Perm (Fin n)), ∀ (i : Fin n), b ((e : Fin n → Fin n) i) = a i := by
  intro n a b h
  classical
  have key : ∀ (f : Fin n → ℂ) (c : ℂ),
      Fintype.card {i // f i = c} = Multiset.count c (Multiset.map f Finset.univ.val) := by
    intro f c
    rw [Fintype.card_subtype, Multiset.count_map, Finset.card_def, Finset.filter_val]
    congr 1
    exact Multiset.filter_congr (fun _ _ => eq_comm)
  have hc : ∀ c : ℂ, Fintype.card {i // a i = c} = Fintype.card {i // b i = c} := by
    intro c
    rw [key a c, key b c, h]
  exact ⟨Equiv.ofFiberEquiv (fun c => Fintype.equivOfCardEq (hc c)),
    fun i => Equiv.ofFiberEquiv_map _ i⟩
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Killed
theorem UpperTheory.Reformulated.B.Qe12.killed :
    ∀ (l : ℕ) [inst : Fact (Nat.Prime l)] (M : Type)
    [inst_1 : AddCommGroup M] [inst_2 : _root_.Module ℤ_[l] M] [Finite M],
    ∃ (r : ℕ), (0 : ℕ) < r ∧ ∀ (x : M), (↑l : ℤ_[l]) ^ r • x = (0 : M) := by
  intro l _ M _ _ _
  have hN : ((Nat.card M : ℕ) : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  refine ⟨((Nat.card M : ℕ) : ℤ_[l]).valuation + 1, Nat.succ_pos _, fun x => ?_⟩
  have h1 : ((Nat.card M : ℕ) : ℤ_[l]) • x = 0 := by
    rw [Nat.cast_smul_eq_nsmul]
    exact card_nsmul_eq_zero'
  have h2 : ((PadicInt.unitCoeff hN : ℤ_[l]ˣ) : ℤ_[l]) •
      ((l : ℤ_[l]) ^ ((Nat.card M : ℕ) : ℤ_[l]).valuation • x) = 0 := by
    rw [← mul_smul, ← PadicInt.unitCoeff_spec hN]
    exact h1
  have h3 : (l : ℤ_[l]) ^ ((Nat.card M : ℕ) : ℤ_[l]).valuation • x = 0 :=
    ((PadicInt.unitCoeff hN).isUnit.smul_eq_zero).mp h2
  rw [pow_succ', mul_smul, h3, smul_zero]
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsBoundPolyMulExp
theorem UpperTheory.Reformulated.B.Rc4.exists_bound_poly_mul_exp :
    ∀ (c : ℝ),
    (0 : ℝ) < c →
      ∀ (N : ℕ), ∃ (C : ℝ), ∀ (r : ℝ), (0 : ℝ) ≤ r → ((1 : ℝ) + r) ^ N * Real.exp (-(c * r ^ (2 : ℕ))) ≤ C := by
  intro c hc N
  refine ⟨Real.exp ((N : ℝ) ^ 2 / (4 * c)), fun r hr => ?_⟩
  have h1 : (1 + r) ^ N ≤ Real.exp r ^ N := by
    apply pow_le_pow_left₀ (by linarith)
    linarith [Real.add_one_le_exp r]
  have h2 : (N : ℝ) * r + -(c * r ^ 2) ≤ (N : ℝ) ^ 2 / (4 * c) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg ((N : ℝ) - 2 * c * r)]
  calc (1 + r) ^ N * Real.exp (-(c * r ^ 2))
      ≤ Real.exp r ^ N * Real.exp (-(c * r ^ 2)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.exp ((N : ℝ) * r + -(c * r ^ 2)) := by
        rw [Real.exp_add, Real.exp_nat_mul]
    _ ≤ Real.exp ((N : ℝ) ^ 2 / (4 * c)) := Real.exp_le_exp.mpr h2
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AddGapLe
theorem UpperTheory.Reformulated.B.Yoa4.add_gap_le :
    ∀ {r : ℕ} {d : Fin r → ℕ}, StrictAnti d → ∀ (k : ℕ) (i j : Fin r), (↑j : ℕ) = (↑i : ℕ) + k → d j + k ≤ d i := by
  intro r d hd k
  induction k with
  | zero =>
    intro i j h
    have hij : j = i := Fin.ext (by simpa using h)
    subst hij
    simp
  | succ k ih =>
    intro i j h
    have hj := j.isLt
    have hm : (i : ℕ) + k < r := by omega
    have h1 := ih i ⟨(i : ℕ) + k, hm⟩ rfl
    have h2 : d j < d ⟨(i : ℕ) + k, hm⟩ := hd (by
      rw [Fin.lt_def]
      simp only
      omega)
    omega
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsAlt
theorem UpperTheory.Reformulated.B.ConjEqNegOfSqEqNegNat₂.main :
    ∀ {d : ℕ}, (0 : ℕ) < d → ∀ {z : ℂ}, z ^ (2 : ℕ) = -(↑d : ℂ) → (starRingEnd ℂ : ℂ → ℂ) z = -z := by
  intro d hd z hz
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hre : z.re * z.re - z.im * z.im = -(d : ℝ) := by
    have h := congrArg Complex.re hz
    simpa [pow_two] using h
  have him : z.re * z.im + z.im * z.re = 0 := by
    have h := congrArg Complex.im hz
    simpa [pow_two] using h
  have hprod : z.re * z.im = 0 := by linarith
  have hre0 : z.re = 0 := by
    rcases mul_eq_zero.mp hprod with h | h
    · exact h
    · rw [h] at hre
      nlinarith [mul_self_nonneg z.re]
  apply Complex.ext
  · simp [hre0]
  · simp
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LeIffLtColH
noncomputable def UpperTheory.Reformulated.B.Qk46.colH :
    {n : Nat} → (Fin n → Int) → Int → Nat :=
    fun {n : Nat} (mu : Fin n → Int) (c : Int) ↦ @Finset.card (Fin n) {m : Fin n | @LE.le Int Int.instLEInt c (mu m)}

theorem UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH :
    ∀ {r : Nat} {μ : Fin r → Int},
      @Antitone (Fin r) Int (@PartialOrder.toPreorder (Fin r) (@Fin.instPartialOrder r))
          (@PartialOrder.toPreorder Int
            (@ConditionallyCompletePartialOrderSup.toPartialOrder Int
              (@ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderSup Int
                (@ConditionallyCompleteLattice.toConditionallyCompletePartialOrder Int
                  (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice Int
                    Int.instConditionallyCompleteLinearOrder)))))
          μ →
        ∀ (c : Int) (m : Fin r),
          Iff (@LE.le Int Int.instLEInt c (μ m)) (@LT.lt Nat instLTNat (@Fin.val r m) (@UpperTheory.Reformulated.B.Qk46.colH r μ c)) := by
  intro r μ h c m
  unfold UpperTheory.Reformulated.B.Qk46.colH
  exact (Tuple.lt_card_ge_iff_apply_ge_of_antitone h).symm
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.WithBotEqOfLeOfAddOneLe
theorem UpperTheory.Reformulated.B.Ydd3.withBot_eq_of_le_of_add_one_le :
    ∀ {x : WithBot ℕ∞} {c : ℕ},
      (↑c : WithBot ℕ∞) ≤ x → x + (1 : WithBot ℕ∞) ≤ (↑(c + (1 : ℕ)) : WithBot ℕ∞) → x = (↑c : WithBot ℕ∞) := by
  intro x c h1 h2
  induction x using WithBot.recBotCoe with
  | bot => exact le_antisymm bot_le h1
  | coe y =>
    induction y using ENat.recTopCoe with
    | top =>
      exfalso
      have h3 : ((⊤ : ℕ∞) + 1 : ℕ∞) ≤ ((c + 1 : ℕ) : ℕ∞) := by exact_mod_cast h2
      rw [top_add, top_le_iff] at h3
      exact ENat.coe_ne_top _ h3
    | coe n =>
      have h3 : c ≤ n := by exact_mod_cast h1
      have h4 : n + 1 ≤ c + 1 := by exact_mod_cast h2
      have h5 : n = c := by omega
      subst h5
      rfl
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FinOfHom
theorem UpperTheory.Reformulated.B.Qh10.fin_of_hom :
    ∀ {S R M : Type} [inst : CommRing S] [inst_1 : CommRing R]
    [inst_2 : AddCommGroup M] [inst_3 : _root_.Module S M] [inst_4 : _root_.Module R M] [Module.Finite S M] (f : S → R),
    (∀ (a : S) (m : M), a • m = f a • m) → Module.Finite R M := by
  intro S R M _ _ _ _ _ hfin f hf
  obtain ⟨T, hT⟩ := hfin.fg_top
  refine ⟨⟨T, ?_⟩⟩
  rw [eq_top_iff]
  intro m hm0
  clear hm0
  have hm : m ∈ Submodule.span S (T : Set M) := by
    rw [hT]
    exact Submodule.mem_top
  induction hm using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span hx
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [hf]
    exact Submodule.smul_mem _ _ hx
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DerivationMemPowOfMemPowSucc
theorem UpperTheory.Reformulated.B.Qn11.derivation_mem_pow_of_mem_pow_succ :
    ∀ {R : Type} [inst : CommRing R]
    (I : Ideal R) (D : Derivation ℤ R R) {n : ℕ} {r : R}, r ∈ I ^ (n + (1 : ℕ)) → (D : R → R) r ∈ I ^ n := by
  intro R _ I D n
  induction n with
  | zero =>
    intro r _
    simp
  | succ n ih =>
    intro r hr
    rw [pow_succ] at hr
    refine Submodule.mul_induction_on hr ?_ ?_
    · intro a ha b hb
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ ha) ?_
      rw [pow_succ, mul_comm b]
      exact Ideal.mul_mem_mul (ih ha) hb
    · intro x y hx hy
      rw [map_add (f := _)]
      exact Ideal.add_mem _ hx hy
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntegralPolynomialSecond
noncomputable def UpperTheory.Reformulated.B.IntegralPolynomialSecond.IsIntP :
    {p : ℕ} → [inst : Fact (Nat.Prime p)] → ℂ_[p] → Prop :=
    fun {p : ℕ} [Fact (Nat.Prime p)] (x : ℂ_[p]) ↦ ‖x‖ ≤ (1 : ℝ)

noncomputable def UpperTheory.Reformulated.B.IntegralPolynomialSecond.IntegralMv.{u_1} :
    {σ : Type u_1} → {p : ℕ} → [inst : Fact (Nat.Prime p)] → MvPowerSeries σ ℂ_[p] → Prop :=
    fun {σ : Type u_1} {p : ℕ} [Fact (Nat.Prime p)] (F : MvPowerSeries σ ℂ_[p]) ↦
      ∀ (n : σ →₀ ℕ), UpperTheory.Reformulated.B.IntegralPolynomialSecond.IsIntP ((MvPowerSeries.coeff n : MvPowerSeries σ ℂ_[p] → ℂ_[p]) F)

theorem UpperTheory.Reformulated.B.IntegralPolynomialSecond.intMv_mul.{u_1} :
    ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {σ : Type u_1} {F G : MvPowerSeries σ ℂ_[p]},
      UpperTheory.Reformulated.B.IntegralPolynomialSecond.IntegralMv F → UpperTheory.Reformulated.B.IntegralPolynomialSecond.IntegralMv G → UpperTheory.Reformulated.B.IntegralPolynomialSecond.IntegralMv (F * G) := by
  intro p _ σ F G hF hG n
  classical
  change ‖MvPowerSeries.coeff n (F * G)‖ ≤ 1
  rw [MvPowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one ?_
  intro q _
  rw [norm_mul]
  exact mul_le_one₀ (hF q.1) (norm_nonneg _) (hG q.2)
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsPFSum
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsPF
noncomputable def UpperTheory.Reformulated.B.PolynomialFunction₂.IsPF :
    {A : Type} → [inst : Ring A] → [Algebra ℂ A] → (ℂ → A) → Prop :=
  fun {A} _ _ f => ∃ p : Polynomial A, ∀ Y : ℂ, f Y = Polynomial.eval (algebraMap ℂ A Y) p
end

theorem UpperTheory.Reformulated.B.IsPFSum.isPF_sum :
    ∀ {A : Type} [inst : Ring A] [inst_1 : Algebra ℂ A] {ι : Type} (s : Finset ι) {f : ι → ℂ → A},
      (∀ i ∈ s, UpperTheory.Reformulated.B.PolynomialFunction₂.IsPF (f i)) → UpperTheory.Reformulated.B.PolynomialFunction₂.IsPF fun (Y : ℂ) ↦ ∑ i ∈ s, f i Y := by
  intro A _ _ ι s f h
  classical
  unfold UpperTheory.Reformulated.B.PolynomialFunction₂.IsPF at h ⊢
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun Y => by simp⟩
  | insert a s ha ih =>
    obtain ⟨p, hp⟩ := h a (Finset.mem_insert_self a s)
    obtain ⟨q, hq⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    refine ⟨p + q, fun Y => ?_⟩
    have h1 : (∑ i ∈ s, f i Y) = Polynomial.eval ((algebraMap ℂ A) Y) q := hq Y
    show (∑ i ∈ insert a s, f i Y) = Polynomial.eval ((algebraMap ℂ A) Y) (p + q)
    rw [Finset.sum_insert ha, hp, h1, Polynomial.eval_add]
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntMvPderiv
noncomputable def UpperTheory.Reformulated.B.Gwb7.IsIntP :
    {p : ℕ} → [inst : Fact (Nat.Prime p)] → ℂ_[p] → Prop :=
    fun {p : ℕ} [Fact (Nat.Prime p)] (x : ℂ_[p]) ↦ ‖x‖ ≤ (1 : ℝ)

noncomputable def UpperTheory.Reformulated.B.Gwb7.IntegralMv.{u_1} :
    {σ : Type u_1} → {p : ℕ} → [inst : Fact (Nat.Prime p)] → MvPowerSeries σ ℂ_[p] → Prop :=
    fun {σ : Type u_1} {p : ℕ} [Fact (Nat.Prime p)] (F : MvPowerSeries σ ℂ_[p]) ↦
      ∀ (n : σ →₀ ℕ), UpperTheory.Reformulated.B.Gwb7.IsIntP ((MvPowerSeries.coeff n : MvPowerSeries σ ℂ_[p] → ℂ_[p]) F)

theorem UpperTheory.Reformulated.B.Gwb7.intMv_pderiv.{u_1} :
    ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {σ : Type u_1} {F : MvPowerSeries σ ℂ_[p]} (i : σ),
      UpperTheory.Reformulated.B.Gwb7.IntegralMv F →
        UpperTheory.Reformulated.B.Gwb7.IntegralMv ((MvPowerSeries.pderiv (R := ℂ_[p]) i : MvPowerSeries σ ℂ_[p] → MvPowerSeries σ ℂ_[p]) F) := by
  intro p _ σ F i hF n
  have h1 : ‖MvPowerSeries.coeff (n + Finsupp.single i 1) F‖ ≤ 1 := hF _
  have h2 : ‖((n i : ℕ) : ℂ_[p]) + 1‖ ≤ 1 := by
    have h := IsUltrametricDist.norm_natCast_le_one ℂ_[p] (n i + 1)
    rwa [Nat.cast_add, Nat.cast_one] at h
  change ‖MvPowerSeries.coeff n (MvPowerSeries.pderiv (R := ℂ_[p]) i F)‖ ≤ 1
  rw [MvPowerSeries.coeff_pderiv, norm_mul]
  exact mul_le_one₀ h1 (norm_nonneg _) h2
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HfsAevalRestrict
theorem UpperTheory.Reformulated.B.Qh20.hfs_aeval_restrict :
    ∀ {L W : Type} [inst : Field L] [inst_1 : AddCommGroup W]
    [inst_2 : _root_.Module L W] (f : Module.End L W) {p : Submodule L W} (h : ∀ x ∈ p, (f : W → W) x ∈ p)
    (q : Polynomial L) (x : ↥p),
    (↑(((Polynomial.aeval (LinearMap.restrict f h) : Polynomial L → ↥p →ₗ[L] ↥p) q : ↥p → ↥p) x) : W) =
      ((Polynomial.aeval f : Polynomial L → Module.End L W) q : W → W) (↑x : W) := by
  intro L W _ _ _ f p h q x
  have hpow : ∀ (n : ℕ) (y : p), ((((LinearMap.restrict f h) ^ n) y : p) : W) = (f ^ n) (y : W) := by
    intro n
    induction n with
    | zero => intro y; rfl
    | succ n ih =>
      intro y
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]
      rfl
  induction q using Polynomial.induction_on' with
  | add a b ha hb =>
    rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, Submodule.coe_add, ha, hb]
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, Module.End.mul_apply,
      Module.End.mul_apply, Module.algebraMap_end_apply, Module.algebraMap_end_apply,
      Submodule.coe_smul, hpow]
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EvalFg
theorem UpperTheory.Reformulated.B.Qn15.eval_fg :
    ∀ {R : Type} [inst : CommRing R] [inst_1 : Algebra R ℂ] {σ : Type} {M₀ : Submodule R ℂ},
    M₀.FG →
      ∀ (P : MvPolynomial σ ℂ),
        ∃ (M : Submodule R ℂ),
          M.FG ∧ ∀ (v : σ → ℂ), (∀ (i : σ), v i ∈ M₀) → (MvPolynomial.eval v : MvPolynomial σ ℂ → ℂ) P ∈ M := by
  intro R _ _ σ M₀ h₀ P
  induction P using MvPolynomial.induction_on with
  | C a =>
    refine ⟨Submodule.span R {a}, Submodule.fg_span_singleton a, fun v _ => ?_⟩
    rw [MvPolynomial.eval_C]
    exact Submodule.mem_span_singleton_self a
  | add p q hp hq =>
    obtain ⟨M, hM, hp⟩ := hp
    obtain ⟨N, hN, hq⟩ := hq
    refine ⟨M ⊔ N, hM.sup hN, fun v hv => ?_⟩
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (hp v hv) (hq v hv)
  | mul_X p i hp =>
    obtain ⟨M, hM, hp⟩ := hp
    refine ⟨M * M₀, hM.mul h₀, fun v hv => ?_⟩
    rw [map_mul, MvPolynomial.eval_X]
    exact Submodule.mul_mem_mul (hp v hv) (hv i)
end
