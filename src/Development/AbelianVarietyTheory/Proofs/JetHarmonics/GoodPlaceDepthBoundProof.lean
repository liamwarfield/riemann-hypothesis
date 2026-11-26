module

public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.InertPrimeDepthContentBoundProof
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ComplexConjFrobeniusDepthContentBoundProof
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HalfPrincipalAndSplit
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ForcedContentBoundsProgrammeValueGoodPrime
public import Development.AutomorphicArithmetic.OrbitLabellings.RowBoundLeFnumSumAddError

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.OrbitLabellings.PkgZeroCsNuNonposOfMonSupply
open Formalism.L2.FormalSeriesBounds UpperTheory.G2


open Formalism.IncomingBounds in
private theorem cut (K s B : ℕ) (e : ℕ → ℕ) : ∃ pc : Fin s → ℕ → ℕ,
    (∀ u, ∑ k ∈ Finset.Icc 1 K, pc u k ≤ B) ∧
    (∑ k ∈ Finset.Icc 1 K, e k ≤ s * B → (∀ k, e k ≠ 0 → 1 ≤ k ∧ k ≤ K) → ∀ k, ∑ u, pc u k = e k) := by
  by_cases h : ∑ k ∈ Finset.Icc 1 K, e k ≤ s * B
  · obtain ⟨pc, h1, h2, h3⟩ := GlobalTheory.exists_cut_columns_bounded_width K s B e h
    refine ⟨pc, h2, fun _ hs k => ?_⟩
    by_cases hk : k ∈ Finset.Icc 1 K
    · exact h1 k hk
    · have : e k = 0 := by
        by_contra h0
        exact hk (Finset.mem_Icc.2 (hs k h0))
      rw [this]
      exact Finset.sum_eq_zero fun u _ => h3 u k hk
  · exact ⟨fun _ _ => 0, by simp, fun h' => absurd h' h⟩


open Formalism.IncomingBounds in
private theorem monAl_le_first (K rk : ℕ) (e : ℕ → ℕ) (ρ : ℕ) :
    monAl K rk e ρ ≤ ∑ k ∈ Finset.Icc 1 K, e k := by
  unfold monAl
  apply Finset.sum_le_sum_of_subset
  intro k hk
  rw [Finset.mem_Icc] at hk ⊢
  exact ⟨le_trans (Nat.le_add_left 1 ρ) hk.1, le_trans hk.2 (min_le_left _ _)⟩

theorem UpperTheory.pkgZeroCs_nu_nonpos_of_monSupply :
    RF.MONSupply → ∀ (P : RF.Par) (l : ℕ) (Pk : PkgZeroCs P l), Pk.ν ≤ 0 := by
  intro hM P l Pk
  have hl : Pk.R.V.l = l := Pk.R.hVl
  have hl2 : 2 ≤ l := hl ▸ Pk.R.V.l_prime.two_le
  have hc := fun (o : ↥Pk.Z) (σ : ZMod (2 * P.d)) => cut Pk.K Pk.s (l - 1) (Pk.ga o σ)
  choose pc hpcB hpcE using hc
  have hE : ∀ o σ k, ∑ u, pc o σ u k = Pk.ga o σ k := fun o σ =>
    hpcE o σ (Pk.first o σ) (fun k hk => ⟨(Pk.supp o σ k hk).1, (Pk.supp o σ k hk).2.2⟩)
  let blk : ↥Pk.Z → ZMod (2 * P.d) → Fin Pk.s → RF.GlobalTheory (2 * P.d) := fun o σ u =>
    RF.GlobalTheory.mon 0 (fun a k => if a = σ then pc o σ u k else 0) Pk.K
  let L : ↥Pk.Z → List (RF.GlobalTheory (2 * P.d) × ℝ) := fun o =>
    (Finset.univ : Finset (ZMod (2 * P.d) × Fin Pk.s)).toList.map (fun p => (blk o p.1 p.2, (0 : ℝ)))
  have hmem : ∀ o, ∀ q ∈ L o, ∃ σ u, q = (blk o σ u, (0 : ℝ)) := by
    intro o q hq
    obtain ⟨p, -, rfl⟩ := List.mem_map.1 hq
    exact ⟨p.1, p.2, rfl⟩
  have hzero : ∑ o, (List.map Prod.snd (L o)).sum = 0 := by
    apply Finset.sum_eq_zero
    intro o _
    simp [L]
  rw [← hzero]
  apply Pk.val L
  · intro o q hq
    obtain ⟨σ, u, rfl⟩ := hmem o q hq
    apply (hM _ _ _ _ _ (Pk.R.X o) (Pk.R.F o) 0 _ Pk.K).2
    intro a ρ
    rw [hl]
    calc monAl Pk.K ((Pk.R.X o).rkF 0 a) (fun k => if a = σ then pc o σ u k else 0) ρ
        ≤ ∑ k ∈ Finset.Icc 1 Pk.K, (fun k => if a = σ then pc o σ u k else 0) k := monAl_le_first _ _ _ _
      _ ≤ l - 1 := by
        by_cases ha : a = σ
        · simp only [ha, if_true]
          exact hpcB o σ u
        · simp [ha]
      _ < l := by omega
  · intro o q hq g e N hqe
    obtain ⟨σ, u, rfl⟩ := hmem o q hq
    obtain ⟨-, rfl, -⟩ := RF.GlobalTheory.mon.inj hqe
    exact ⟨σ, fun a k ha => if_neg ha⟩
  · have hrow : ∀ o, (List.map (fun q => RF.GlobalTheory.what₂ (Pk.R.X o).n q.1) (L o)).sum = 2 * P.d * Pk.s * Pk.K := by
      intro o
      simp [L, blk, RF.GlobalTheory.what₂]
    simp only [hrow]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, smul_eq_mul]
    calc 2 * (Pk.Z.card * (2 * P.d * Pk.s * Pk.K)) = 4 * Pk.K * Pk.s * (Pk.Z.card * P.d) := by ring
      _ ≤ Pk.nW := Pk.what₂
  · intro o s k
    simp [L, blk, RF.GlobalTheory.wt]
    split_ifs with hk
    · rw [Fintype.sum_prod_type, Finset.sum_eq_single s]
      · simp [hE]
      · intro b _ hb
        simp [Ne.symm hb]
      · intro hs
        exact absurd (Finset.mem_univ s) hs
    · by_contra hne
      have h3 := Pk.supp o s k (Ne.symm hne)
      exact hk ⟨h3.1, h3.2.2, h3.2.1⟩
end

section -- merged from Development.AutomorphicArithmetic.OrbitLabellings.FMulLeastAdmissibleLevelRowsLe
open Formalism.L2.FormalSeriesBounds

private lemma UpperTheory.least_level_le_log_bound (k l : ℕ) (hk : 1 ≤ k) (hl : 5 ≤ l) :
    ((RF.i0 k l : ℕ) : ℝ) ≤ 3 + 2 * Real.log k := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hlog : 0 ≤ Real.log k := Real.log_nonneg hk1
  have hj1 : Real.log k < (⌊Real.log k⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hj2 : (⌊Real.log k⌋₊ : ℝ) ≤ Real.log k := Nat.floor_le hlog
  have hmem : 2 * ⌊Real.log k⌋₊ + 3 ∈
      {i : ℕ | Odd i ∧ 3 ≤ i ∧ (k:ℝ) ^ ((3:ℝ) / 2) < (l:ℝ) ^ i} := by
    refine ⟨⟨⌊Real.log k⌋₊ + 1, by ring⟩, by omega, ?_⟩
    have e1 : (k:ℝ) ^ ((3:ℝ) / 2) ≤ (k:ℝ) ^ (2:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hk1 (by norm_num)
    have e2 : (k:ℝ) ^ (2:ℝ) = Real.exp (2 * Real.log k) := by
      rw [Real.rpow_def_of_pos hk0, mul_comm]
    have e3 : Real.exp (2 * Real.log k) < Real.exp ((2 * ⌊Real.log k⌋₊ + 3 : ℕ) : ℝ) := by
      apply Real.exp_lt_exp.2
      push_cast
      linarith
    have e4 : Real.exp ((2 * ⌊Real.log k⌋₊ + 3 : ℕ) : ℝ) ≤ (5:ℝ) ^ (2 * ⌊Real.log k⌋₊ + 3) := by
      rw [show ((2 * ⌊Real.log k⌋₊ + 3 : ℕ) : ℝ) = ((2 * ⌊Real.log k⌋₊ + 3 : ℕ) : ℝ) * 1 by ring,
        Real.exp_nat_mul]
      apply pow_le_pow_left₀ (Real.exp_pos 1).le
      have := Real.exp_one_lt_d9
      linarith
    have e5 : (5:ℝ) ^ (2 * ⌊Real.log k⌋₊ + 3) ≤ (l:ℝ) ^ (2 * ⌊Real.log k⌋₊ + 3) := by
      apply pow_le_pow_left₀ (by norm_num)
      exact_mod_cast hl
    linarith
  have hle : RF.i0 k l ≤ 2 * ⌊Real.log k⌋₊ + 3 := Nat.sInf_le hmem
  have hc : ((RF.i0 k l : ℕ) : ℝ) ≤ ((2 * ⌊Real.log k⌋₊ + 3 : ℕ) : ℝ) := by exact_mod_cast hle
  push_cast at hc
  linarith

theorem UpperTheory.f_mul_leastAdmissibleLevel_rows_le :
    ∀ (r f n m nW l k : ℕ) (L : ℝ), 1 ≤ m → m ≤ n → n ≤ r → 2 ≤ f → n + 1 = k → 3 ≤ L → Real.log k ≤ L →
    10 * (r : ℝ) * (f + (f : ℝ) ^ 2 * (n : ℝ) ^ 3 * L ^ 2 / m) ≤ nW → 5 ≤ l → f * ((RF.i0 k l + 1) * n + 4 * r) ≤ nW := by
  intro r f n m nW l k L hm hmn hnr hf hk hL hlogL hW hl
  have hk1 : 1 ≤ k := by omega
  have hi := UpperTheory.least_level_le_log_bound k l hk1 hl
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hmnR : (m:ℝ) ≤ n := by exact_mod_cast hmn
  have hnrR : (n:ℝ) ≤ r := by exact_mod_cast hnr
  have hfR : (2:ℝ) ≤ f := by exact_mod_cast hf
  have hn1 : (1:ℝ) ≤ n := le_trans hmR hmnR
  have hr1 : (1:ℝ) ≤ r := le_trans hn1 hnrR
  have hiL : ((RF.i0 k l : ℕ) : ℝ) ≤ 3 + 2 * L := by linarith
  have hX : (0:ℝ) ≤ (f:ℝ) ^ 2 * (n:ℝ) ^ 2 * L ^ 2 := by positivity
  have hdiv : (f:ℝ) ^ 2 * (n:ℝ) ^ 2 * L ^ 2 ≤ (f:ℝ) ^ 2 * (n:ℝ) ^ 3 * L ^ 2 / m := by
    rw [le_div_iff₀ (by linarith)]
    have := mul_le_mul_of_nonneg_left hmnR hX
    nlinarith
  have h1 : (f:ℝ) * (((RF.i0 k l : ℕ) : ℝ) + 1) * n ≤ f * (4 + 2 * L) * n := by
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    linarith
  have a1 : 4 + 2 * L ≤ 10 * (f:ℝ) * L ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hfR) (sq_nonneg L)]
  have hrn : (1:ℝ) ≤ r * n := by nlinarith
  have a2 : (n:ℝ) ≤ r * (n:ℝ) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hrn (by linarith : (0:ℝ) ≤ n)]
  have h2 : (f:ℝ) * (4 + 2 * L) * n ≤ 10 * r * ((f:ℝ) ^ 2 * (n:ℝ) ^ 2 * L ^ 2) := by
    calc (f:ℝ) * (4 + 2 * L) * n ≤ f * (10 * f * L ^ 2) * n := by gcongr
      _ = 10 * (f:ℝ) ^ 2 * L ^ 2 * n := by ring
      _ ≤ 10 * (f:ℝ) ^ 2 * L ^ 2 * (r * (n:ℝ) ^ 2) := by gcongr
      _ = 10 * r * ((f:ℝ) ^ 2 * (n:ℝ) ^ 2 * L ^ 2) := by ring
  have h3 := mul_le_mul_of_nonneg_left hdiv (by linarith : (0:ℝ) ≤ 10 * r)
  have h4 : 4 * (f:ℝ) * r ≤ 10 * r * f := by nlinarith
  have key : (((f * ((RF.i0 k l + 1) * n + 4 * r)) : ℕ) : ℝ) ≤ nW := by
    push_cast
    nlinarith
  exact_mod_cast key
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelLe
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.DIV Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.GoodDepth NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RowBudgets

lemma level_le (k l : ℕ) (hk : 1 ≤ k) (hl : 5 ≤ l) :
    ((RF.i0 k l : ℕ) : ℝ) ≤ 3 + 2 * Real.log k := by
  have h := GlobalTheory.LevelsOrbits.levelBound k l hk hl
  have e : RF.i0 k l = Formalism.L2.FormalSeriesBounds.i0 k l := rfl
  rw [e]
  linarith

theorem main : ∀ (r f n m nW T l k : ℕ) (b L A : ℝ), 1 ≤ m → m ≤ n → n ≤ r → 2 ≤ f → 1 ≤ T → n + 1 = k → 3 ≤ L → Real.log k ≤ L → 10 * (r : ℝ) * (f + (f : ℝ) ^ 2 * (n : ℝ) ^ 3 * L ^ 2 / m) ≤ nW →
  8 * r * f ≤ nW ∧ (5 ≤ l → f * (RF.i0 k l * n) + 2 * r * f ≤ nW) ∧
  (3 ≤ l → 0 ≤ b → m * b / (T * f * (n : ℝ) ^ 3 * L) ≤ l → ∃ s : ℕ, 4 * r * s * f ≤ nW ∧ ∀ x : ℕ, (T : ℝ) * x ≤ 3 * b → x ≤ s * (l - 1)) ∧
  (0 < l → (l : ℝ) < m * b / (T * f * (n : ℝ) ^ 3 * L) → b ≤ A → T * f * (n : ℝ) ^ 3 * Real.log k ^ 2 ≤ Real.log k * m * A / l) := by
  intro r f n m nW T l k b L A hm hmn hnr hf hT hk hL hkL hW
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hnr' : (n : ℝ) ≤ r := by exact_mod_cast hnr
  have hf' : (2 : ℝ) ≤ f := by exact_mod_cast hf
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hk1 : 1 ≤ k := by omega
  have hlog : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hk1)
  have hn' : (1 : ℝ) ≤ n := hm'.trans hmn'
  have hr' : (1 : ℝ) ≤ r := hn'.trans hnr'
  have hD : (0 : ℝ) < T * f * (n : ℝ) ^ 3 * L := by positivity
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = f * (n : ℝ) ^ 3 * L / m := ⟨_, rfl⟩
  have hYm : Y * m = f * (n : ℝ) ^ 3 * L := by rw [hY]; field_simp
  have hW' : 10 * ((r : ℝ) * f) + 10 * L * (r * f * Y) ≤ nW := by
    refine le_of_eq_of_le ?_ hW
    rw [hY]; ring
  have hYL : L ≤ Y := by
    rw [hY, le_div_iff₀ (by positivity)]
    have h1 : (m : ℝ) ≤ (n : ℝ) ^ 3 := hmn'.trans (le_self_pow₀ hn' (by norm_num))
    have h2 : (n : ℝ) ^ 3 ≤ f * (n : ℝ) ^ 3 := le_mul_of_one_le_left (by positivity) (by linarith)
    have h3 := mul_le_mul_of_nonneg_right (h1.trans h2) (show 0 ≤ L by linarith)
    linarith
  have hrf : (0 : ℝ) ≤ r * f := by positivity
  have hP : (0 : ℝ) ≤ r * f * Y := mul_nonneg hrf (by linarith)
  have hPL : 3 * (r * f * Y) ≤ L * (r * f * Y) := mul_le_mul_of_nonneg_right hL hP
  refine ⟨?_, fun hl => ?_, fun hl hb h => ?_, fun hl h hA => ?_⟩
  · have : (8 * r * f : ℝ) ≤ nW := by linarith
    exact_mod_cast this
  · have h1 : ((RF.i0 k l : ℕ) : ℝ) ≤ 3 * Y := by
      have := level_le k l hk1 hl
      linarith
    have h2 : ((RF.i0 k l : ℕ) : ℝ) * n ≤ 3 * Y * r :=
      mul_le_mul h1 hnr' (by positivity) (by linarith)
    have h3 := mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ f by positivity)
    have : (f * (((RF.i0 k l : ℕ) : ℝ) * n) + 2 * r * f : ℝ) ≤ nW := by linarith
    exact_mod_cast this
  · have hl' : (3 : ℝ) ≤ l := by exact_mod_cast hl
    have hq : (0 : ℝ) < T * ((l : ℝ) - 1) := mul_pos (by linarith) (by linarith)
    rw [div_le_iff₀ hD] at h
    have hbY : b ≤ l * T * Y := by
      refine le_of_mul_le_mul_left (a := (m : ℝ)) ?_ (by linarith)
      calc (m : ℝ) * b ≤ l * (T * f * (n : ℝ) ^ 3 * L) := h
        _ = l * T * (Y * m) := by rw [hYm]; ring
        _ = _ := by ring
    have hTY : (0 : ℝ) ≤ T * Y := mul_nonneg (by linarith) (by linarith)
    have hz : 3 * b / (T * ((l : ℝ) - 1)) ≤ 6 * Y := by
      rw [div_le_iff₀ hq]
      have := mul_le_mul_of_nonneg_right hl' hTY
      nlinarith
    refine ⟨⌈3 * b / (T * ((l : ℝ) - 1))⌉₊, ?_, fun x hx => ?_⟩
    · have h1 := (Nat.ceil_lt_add_one (show 0 ≤ 3 * b / (T * ((l : ℝ) - 1)) by positivity)).le
      have h2 := mul_le_mul_of_nonneg_left (h1.trans (add_le_add_left hz 1)) hrf
      have : (4 * r * (⌈3 * b / (T * ((l : ℝ) - 1))⌉₊ : ℝ) * f : ℝ) ≤ nW := by linarith
      exact_mod_cast this
    · have h1 := Nat.le_ceil (3 * b / (T * ((l : ℝ) - 1)))
      rw [div_le_iff₀ hq] at h1
      have h2 : (x : ℝ) ≤ (⌈3 * b / (T * ((l : ℝ) - 1))⌉₊ : ℝ) * ((l : ℝ) - 1) := by
        refine le_of_mul_le_mul_left (a := (T : ℝ)) ?_ (by linarith)
        linarith
      have h3 : ((l : ℝ) - 1) = ((l - 1 : ℕ) : ℝ) := by
        rw [Nat.cast_sub (by omega)]; simp
      generalize ⌈3 * b / (T * ((l : ℝ) - 1))⌉₊ = s at h2 ⊢
      rw [h3] at h2
      exact_mod_cast h2
  · have hl' : (0 : ℝ) < l := by exact_mod_cast hl
    rw [lt_div_iff₀ hD] at h
    rw [le_div_iff₀ hl']
    have h1 : (m : ℝ) * b ≤ m * A := mul_le_mul_of_nonneg_left hA (by linarith)
    have h2 : l * (T * f * (n : ℝ) ^ 3 * Real.log k) ≤ l * (T * f * (n : ℝ) ^ 3 * L) := by
      gcongr
    have h3 := mul_le_mul_of_nonneg_left (h2.trans (h.le.trans h1)) hlog
    linarith

end GlobalTheory.RowBudgets
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitPrimeDepthContentBoundProof
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitPrimeDepthContentBoundProof
open Formalism.L2.FormalSeriesBounds GlobalTheory.GoodDepth
open scoped BigOperators

namespace GlobalTheory.SplitPackageBound

theorem sum_reps {M : Type} [AddCommMonoid M] (P : RF.Par) (Z : Finset P.Pl)
    (h : RF.IsReps P Z) (W : P.Pl → M) :
    ∑ z ∈ Z, ∑ a, RF.alongOrb P z W a = ∑ z, W z := by
  rw [← Finset.sum_product']
  refine Finset.sum_bij (fun p _ => P.pos p.1 p.2.val) (fun _ _ => Finset.mem_univ _) ?_ ?_
    (fun _ _ => rfl)
  · intro p hp q hq hpq
    exact (h (P.pos q.1 q.2.val)).unique ⟨(Finset.mem_product.1 hp).1, hpq⟩
      ⟨(Finset.mem_product.1 hq).1, rfl⟩
  · intro z _
    obtain ⟨p, hp, -⟩ := h z
    exact ⟨p, Finset.mem_product.2 ⟨hp.1, Finset.mem_univ _⟩, hp.2⟩

theorem card_reps (P : RF.Par) (Z : Finset P.Pl) (h : RF.IsReps P Z) :
    Z.card * Fintype.card (ZMod P.d) = Fintype.card P.Pl := by
  have := sum_reps P Z h (fun _ => (1 : ℕ))
  simpa [RF.alongOrb] using this

theorem deg_le {d : ℕ} [NeZero d] (rk : Fin 2 → ZMod d → ℕ) (n K : ℕ)
    (ga : Fin 2 → ZMod d → ℕ → ℕ) :
    (∑ a, monDeg K (rk 0 a) (fun k => if k = n then 0 else ga 0 a k)) +
      (∑ a, monDeg K (rk 1 a) (ga 1 a)) ≤ RF.restDeg (fun _ => 0) n ga K := by
  have hsub : ∀ r, Finset.Icc 1 (min K r) ⊆ Finset.Icc 1 K := fun r =>
    Finset.Icc_subset_Icc_right (min_le_left _ _)
  unfold RF.restDeg monDeg
  rw [Fin.sum_univ_two]
  refine Nat.add_le_add (Finset.sum_le_sum (N := ℕ) fun a _ => ?_)
    (Finset.sum_le_sum (N := ℕ) fun a _ => ?_)
  · refine le_trans (Finset.sum_le_sum_of_subset (M := ℕ) (hsub _)) (le_of_eq ?_)
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : k = n <;> simp [hk]
  · refine le_trans (Finset.sum_le_sum_of_subset (M := ℕ) (hsub _)) (le_of_eq ?_)
    simp

theorem nu_le (hC : RF.CHSupply) (hM : RF.MONSupply) (P : RF.Par) (l : ℕ) (C1 : ℝ) (hP : ParOK P)
    (hl : l.Prime) (Pk : RF.PkgSplit P l C1) :
    Pk.ν ≤ (∑ z, (Pk.W z : ℝ)) * P.m / ((l : ℝ) - 1) + Pk.rest / ((l : ℝ) - 1) := by
  obtain ⟨R, Z, hZ, hbig, ga, W, nW, T, θ, rest, ν, hW, hr, hD, hV⟩ := Pk
  dsimp only
  have hVl := R.hVl
  have hl' : (0 : ℝ) < (l : ℝ) - 1 := by
    have : (2 : ℝ) ≤ l := by exact_mod_cast hl.two_le
    linarith
  have hk := hP.mk_le
  have hrr := hP.r_eq
  let e0 : P.Pl → ZMod P.d → ℕ → ℕ := fun z a k =>
    if k = P.k - 1 then 0 else ga z 0 a k
  have := hV (fun z =>
    (RF.GlobalTheory.mon 0 (e0 z) P.r, (RF.monDegAll (R.X z) 0 (e0 z) P.r : ℝ) / ((R.V.l : ℝ) - 1)) ::
    (RF.GlobalTheory.mon 1 (ga z 1) P.r, (RF.monDegAll (R.X z) 1 (ga z 1) P.r : ℝ) / ((R.V.l : ℝ) - 1)) ::
    (Finset.univ : Finset (ZMod P.d)).toList.map fun a =>
      (RF.GlobalTheory.ch 0 a (RF.alongOrb P z W a),
        ((RF.alongOrb P z W a : ℕ) : ℝ) * ((R.X z).m / ((R.V.l : ℝ) - 1)))) ?_ ?_ ?_
  · refine this.trans ?_
    simp only [List.map_cons, List.sum_cons, List.map_map, Finset.sum_map_toList,
      Function.comp_def, hVl]
    rw [hW.rest_eq, ← sum_reps P Z hZ (fun z => (W z : ℝ)), Finset.sum_mul, Finset.sum_div,
      Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun z hz => ?_
    rw [(R.hn z).2, ← add_assoc, add_comm, ← Finset.sum_mul, mul_div_assoc, ← add_div]
    refine add_le_add le_rfl (div_le_div_of_nonneg_right ?_ hl'.le)
    have h := deg_le (R.X z).rkF (P.k - 1) P.r (ga z)
    simp only [Nat.cast_zero, mul_zero, Finset.sum_const_zero, add_zero]
    exact_mod_cast h
  · intro z hz p hp
    simp only [List.mem_cons, List.mem_map] at hp
    rcases hp with rfl | rfl | ⟨a, -, rfl⟩
    · exact (hM R.C R.V _ _ _ (R.X z) (R.F z) 0 _ _).1
    · exact (hM R.C R.V _ _ _ (R.X z) (R.F z) 1 _ _).1
    · exact (hC R.C R.V _ _ _ (R.X z) (R.F z) 0 a (hbig z hz a) _).2 (hbig z hz)
  · simp only [List.map_cons, List.sum_cons, List.map_map, Finset.sum_map_toList,
      Function.comp_def, RF.GlobalTheory.what₂, Finset.sum_const, smul_eq_mul, Finset.card_univ]
    have hc := card_reps P Z hZ
    rw [hP.card] at hc
    have hpos : 1 ≤ Fintype.card (ZMod P.d) := Fintype.card_pos
    calc _ ≤ ∑ z ∈ Z, 3 * P.r * Fintype.card (ZMod P.d) := by
          refine Finset.sum_le_sum fun z hz => ?_
          have : (R.X z).n ≤ P.r := by rw [(R.hn z).1]; omega
          nlinarith
      _ = 3 * P.r * P.f := by
          rw [Finset.sum_const, smul_eq_mul, ← hc]; ring
      _ ≤ nW := by nlinarith
  · intro z hz g a k
    simp only [List.map_cons, List.sum_cons, List.map_map, Finset.sum_map_toList,
      Function.comp_def, RF.GlobalTheory.wt]
    obtain ⟨hn, hm⟩ := R.hn z
    have hb := hbig z hz
    have hm' : (R.X z).j + (R.X z).j' = P.m := hm
    have h0 : (R.X z).rkF 0 a = (R.X z).n + (R.X z).j := (R.X z).rk_big 0 a (hb a)
    have h1 : (R.X z).rkF 1 a = (R.X z).j' :=
      (R.X z).rk_small 1 a fun h => ((R.X z).big_compl 0 a).1 (by simpa using h) (hb a)
    have hs := hW.supp z hz g a k
    have hmain := hW.main z hz a
    fin_cases g
    · simp only [Fin.zero_eta, true_and, zero_ne_one, false_and, if_false, zero_add] at hs hmain ⊢
      by_cases hkn : k = P.k - 1
      · subst hkn
        rw [hmain]
        simp [e0, hn]
      · have : k ≠ (R.X z).n := by omega
        by_cases hz0 : ga z 0 a k = 0
        · simp [e0, hkn, this, hz0]
        · have h2 := hs hz0
          rw [if_pos (by omega)]
          simp [e0, hkn, this]
    · simp only [Fin.mk_one, true_and, one_ne_zero, false_and, if_false, zero_add,
        Finset.sum_const_zero, add_zero] at hs ⊢
      by_cases hz0 : ga z 1 a k = 0
      · simp [hz0]
      · have h2 := hs hz0
        rw [if_pos (by omega)]

theorem splitBd_of_supplies (hC : RF.CHSupply) (hM : RF.MONSupply) : SplitBd := by
  intro C1 hC1
  refine ⟨2 * (1 + 2 * C1), by positivity, fun P l hP hl Pk => ?_⟩
  have hν := nu_le hC hM P l C1 hP hl Pk
  have hD := Pk.deg
  have h2 : (2 : ℝ) ≤ l := by exact_mod_cast hl.two_le
  have hl' : (0 : ℝ) < (l : ℝ) - 1 := by linarith
  have hT : 0 ≤ Pk.T := le_trans zero_le_one hD.T_one
  have hSE := hP.SE_nonneg
  have h1 : Pk.T * ∑ z, (Pk.W z : ℝ) ≤ ∑ z, P.w z + P.f * (C1 * P.SE) := by
    rw [Finset.mul_sum]
    refine (Finset.sum_le_sum fun z _ => hD.TW_hi z).trans (le_of_eq ?_)
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, hP.card, nsmul_eq_mul]
  have hw : 0 ≤ ∑ z, P.w z := Finset.sum_nonneg fun z _ => (hD.w_pos z).le
  have hm : (0 : ℝ) ≤ P.m := Nat.cast_nonneg _
  have hmk : (P.m : ℝ) ≤ P.k := by exact_mod_cast (by have := hP.mk_le; omega : P.m ≤ P.k)
  have hf : (0 : ℝ) ≤ P.f := Nat.cast_nonneg _
  set A : ℝ := P.m * ∑ z, P.w z with hA
  set B : ℝ := P.f * P.k * P.SE with hB
  have hA0 : 0 ≤ A := mul_nonneg hm hw
  have hB0 : 0 ≤ B := mul_nonneg (mul_nonneg hf (Nat.cast_nonneg _)) hSE
  have h3 : Pk.T * ((∑ z, (Pk.W z : ℝ)) * P.m + Pk.rest) ≤ (1 + 2 * C1) * (A + B) := by
    have e1 := mul_le_mul_of_nonneg_right h1 hm
    have e2 : P.f * (C1 * P.SE) * P.m ≤ C1 * B := by
      have := mul_le_mul_of_nonneg_left hmk (mul_nonneg hf (mul_nonneg hC1 hSE))
      calc _ ≤ _ := this
        _ = _ := by rw [hB]; ring
    have e3 := hD.rest_le
    have e4 := mul_nonneg hC1 hA0
    nlinarith
  have h4 : 0 ≤ (1 + 2 * C1) * (A + B) := by positivity
  refine (mul_le_mul_of_nonneg_left hν hT).trans ?_
  rw [← add_div, ← mul_div_assoc, ← mul_div_assoc]
  refine (div_le_div_of_nonneg_right h3 hl'.le).trans ?_
  rw [div_le_div_iff₀ hl' (by linarith)]
  nlinarith

end GlobalTheory.SplitPackageBound

theorem GlobalTheory.GoodDepth.splitBd : SplitBd :=
  GlobalTheory.SplitPackageBound.splitBd_of_supplies GlobalTheory.CharBlock.chSupply.2 GlobalTheory.T.monomialBlock_supply_both_typings.2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitPrimeDepthContentBoundProofStatement
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.DIV Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.GoodDepth NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPrimeDepthContentBound_proof : SplitBd := by
  first | exact @GlobalTheory.GoodDepth.splitBd | exact GlobalTheory.GoodDepth.splitBd | (intros; apply GlobalTheory.GoodDepth.splitBd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LargePrimePackagesDepthNonpos
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LargePrimePackagesDepthNonpos
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.DIV
open scoped BigOperators

namespace GlobalTheory.GoodDepth.Zero

theorem cut (K s B : ℕ) (e : ℕ → ℕ) : ∃ pc : Fin s → ℕ → ℕ,
    (∀ u, ∑ k ∈ Finset.Icc 1 K, pc u k ≤ B) ∧
    (∑ k ∈ Finset.Icc 1 K, e k ≤ s * B → (∀ k, e k ≠ 0 → 1 ≤ k ∧ k ≤ K) → ∀ k, ∑ u, pc u k = e k) := by
  by_cases h : ∑ k ∈ Finset.Icc 1 K, e k ≤ s * B
  · obtain ⟨pc, h1, h2, h3⟩ := GlobalTheory.exists_cut_columns_bounded_width K s B e h
    refine ⟨pc, h2, fun _ hsupp k => ?_⟩
    by_cases hk : k ∈ Finset.Icc 1 K
    · exact h1 k hk
    · have hek : e k = 0 := by
        by_contra hne
        exact hk (Finset.mem_Icc.mpr (hsupp k hne))
      rw [hek]
      exact Finset.sum_eq_zero fun u _ => h3 u k hk
  · exact ⟨fun _ _ => 0, fun _ => by simp, fun h' => absurd h' h⟩

theorem monAl_le_first (K rk : ℕ) (e : ℕ → ℕ) (ρ : ℕ) :
    monAl K rk e ρ ≤ ∑ k ∈ Finset.Icc 1 K, e k := by
  unfold monAl
  apply Finset.sum_le_sum_of_subset
  intro k hk
  simp only [Finset.mem_Icc] at hk ⊢
  exact ⟨by omega, hk.2.trans (min_le_left _ _)⟩

theorem zero_of_pkg (hM : RF.MONSupply) (P : RF.Par) (l : ℕ) (Pk : RF.PkgZero P l) : Pk.ν ≤ 0 := by
  classical
  rcases Nat.eq_zero_or_pos l with hl | hl
  · have hz : ∀ z ∈ Pk.Z, ∀ g a k, Pk.ga z g a k = 0 := by
      intro z hz g a k
      by_contra hne
      have hs := Pk.supp z hz g a k hne
      have h0 : Pk.s * (l - 1) = 0 := by simp [hl]
      have hf := (Pk.first z hz g a).trans h0.le
      exact hne ((Finset.sum_eq_zero_iff.mp (Nat.le_zero.mp hf)) k
        (Finset.mem_Icc.mpr ⟨hs.1, hs.2.2⟩))
    have h := Pk.val (fun _ => []) (by simp) (by simp)
      (by intro o ho g a k; simp [hz o ho g a k])
    simpa using h
  · have hcut : ∀ z g a, ∃ pc : Fin Pk.s → ℕ → ℕ,
        (∀ u, ∑ k ∈ Finset.Icc 1 Pk.K, pc u k ≤ l - 1) ∧
        (z ∈ Pk.Z → ∀ k, ∑ u, pc u k = Pk.ga z g a k) := by
      intro z g a
      obtain ⟨pc, h1, h2⟩ := cut Pk.K Pk.s (l - 1) (Pk.ga z g a)
      exact ⟨pc, h1, fun hz => h2 (Pk.first z hz g a)
        fun k hk => ⟨(Pk.supp z hz g a k hk).1, (Pk.supp z hz g a k hk).2.2⟩⟩
    choose pc hpc1 hpc2 using hcut
    let blk : P.Pl → Fin 2 × Fin Pk.s → RF.GlobalTheory P.d × ℝ :=
      fun z q => (RF.GlobalTheory.mon q.1 (fun a => pc z q.1 a q.2) Pk.K, 0)
    let L : P.Pl → List (RF.GlobalTheory P.d × ℝ) :=
      fun z => (Finset.univ : Finset (Fin 2 × Fin Pk.s)).toList.map (blk z)
    have hsum0 : ∑ o ∈ Pk.Z, ((L o).map Prod.snd).sum = 0 := by
      simp [L, blk]
    refine (Pk.val L ?_ ?_ ?_).trans hsum0.le
    · intro o _ p hp
      simp only [L, List.mem_map, Finset.mem_toList] at hp
      obtain ⟨q, -, rfl⟩ := hp
      refine (hM Pk.R.C Pk.R.V P.d (Pk.R.I o) (Pk.R.J o) (Pk.R.X o) (Pk.R.F o) q.1
        (fun a => pc o q.1 a q.2) Pk.K).2 ?_
      intro a ρ
      rw [Pk.R.hVl]
      have h1 := (monAl_le_first Pk.K ((Pk.R.X o).rkF q.1 a) (pc o q.1 a q.2) ρ).trans (hpc1 o q.1 a q.2)
      omega
    · have hrow : ∀ o, ((L o).map fun p => p.1.what₂ (Pk.R.X o).n).sum = 2 * Pk.s * Pk.K := by
        intro o
        simp only [L, List.map_map]
        rw [Finset.sum_map_toList]
        simp [blk, RF.GlobalTheory.what₂]
      rw [Finset.sum_congr rfl fun o _ => hrow o, Finset.sum_const, smul_eq_mul]
      calc Pk.Z.card * (2 * Pk.s * Pk.K) = 2 * Pk.K * Pk.s * Pk.Z.card := by ring
        _ ≤ Pk.nW := Pk.what₂
    · intro o ho g a k
      have hw : ∀ q : Fin 2 × Fin Pk.s, (blk o q).1.wt (Pk.R.X o) g a k =
          if q.1 = g then (if 1 ≤ k ∧ k ≤ min Pk.K ((Pk.R.X o).rkF g a) then pc o g a q.2 k else 0)
          else 0 := by
        rintro ⟨g', u⟩
        by_cases hg : g' = g
        · subst hg
          simp [blk, RF.GlobalTheory.wt]
        · simp [blk, RF.GlobalTheory.wt, hg, Ne.symm hg]
      calc ((L o).map fun p => p.1.wt (Pk.R.X o) g a k).sum
          = ∑ q : Fin 2 × Fin Pk.s, (blk o q).1.wt (Pk.R.X o) g a k := by
            simp only [L, List.map_map]
            rw [Finset.sum_map_toList]
            rfl
        _ = ∑ q : Fin 2 × Fin Pk.s, if q.1 = g then
              (if 1 ≤ k ∧ k ≤ min Pk.K ((Pk.R.X o).rkF g a) then pc o g a q.2 k else 0) else 0 :=
            Finset.sum_congr rfl fun q _ => hw q
        _ = ∑ u : Fin Pk.s,
              (if 1 ≤ k ∧ k ≤ min Pk.K ((Pk.R.X o).rkF g a) then pc o g a u k else 0) := by
            rw [Fintype.sum_prod_type, Finset.sum_eq_single g]
            · simp
            · intro b _ hb
              simp [hb]
            · simp
        _ = Pk.ga o g a k := by
            by_cases hk : 1 ≤ k ∧ k ≤ min Pk.K ((Pk.R.X o).rkF g a)
            · simp only [if_pos hk]
              exact hpc2 o g a ho k
            · simp only [if_neg hk, Finset.sum_const_zero]
              symm
              by_contra hne
              have hs := Pk.supp o ho g a k hne
              exact hk ⟨hs.1, le_min hs.2.2 hs.2.1⟩

theorem zero_of_pkgC (hM : RF.MONSupply) (P : RF.Par) (l : ℕ) (Pk : RF.PkgZeroC P l) : Pk.ν ≤ 0 := by
  classical
  rcases Nat.eq_zero_or_pos l with hl | hl
  · have hz : ∀ z σ k, Pk.gaC z σ k = 0 := by
      intro z σ k
      by_contra hne
      have hs := Pk.supp z σ k hne
      have h0 : Pk.s * (l - 1) = 0 := by simp [hl]
      have hf := (Pk.first z σ).trans h0.le
      exact hne ((Finset.sum_eq_zero_iff.mp (Nat.le_zero.mp hf)) k
        (Finset.mem_Icc.mpr ⟨hs.1, hs.2.2⟩))
    have h := Pk.val (fun _ => []) (by simp) (by simp) (by simp)
      (by intro o σ k; simp [hz o σ k])
    simpa using h
  · have hcut : ∀ z σ, ∃ pc : Fin Pk.s → ℕ → ℕ,
        (∀ u, ∑ k ∈ Finset.Icc 1 Pk.K, pc u k ≤ l - 1) ∧ (∀ k, ∑ u, pc u k = Pk.gaC z σ k) := by
      intro z σ
      obtain ⟨pc, h1, h2⟩ := cut Pk.K Pk.s (l - 1) (Pk.gaC z σ)
      exact ⟨pc, h1, h2 (Pk.first z σ)
        fun k hk => ⟨(Pk.supp z σ k hk).1, (Pk.supp z σ k hk).2.2⟩⟩
    choose pc hpc1 hpc2 using hcut
    let ee : P.Pl → ZMod 2 × Fin Pk.s → ZMod 2 → ℕ → ℕ :=
      fun z q a k => if a = q.1 then pc z q.1 q.2 k else 0
    let blk : P.Pl → ZMod 2 × Fin Pk.s → RF.GlobalTheory 2 × ℝ :=
      fun z q => (RF.GlobalTheory.mon 0 (ee z q) Pk.K, 0)
    let L : P.Pl → List (RF.GlobalTheory 2 × ℝ) :=
      fun z => (Finset.univ : Finset (ZMod 2 × Fin Pk.s)).toList.map (blk z)
    have hsum0 : ∑ o, ((L o).map Prod.snd).sum = 0 := by
      simp [L, blk]
    refine (Pk.val L ?_ ?_ ?_ ?_).trans hsum0.le
    · intro o p hp
      simp only [L, List.mem_map, Finset.mem_toList] at hp
      obtain ⟨q, -, rfl⟩ := hp
      refine (hM Pk.R.C Pk.R.V 2 (Pk.R.I o) (Pk.R.J o) (Pk.R.X o) (Pk.R.F o) 0 (ee o q) Pk.K).2 ?_
      intro a ρ
      rw [Pk.R.hVl]
      have h1 : ∑ k ∈ Finset.Icc 1 Pk.K, ee o q a k ≤ l - 1 := by
        by_cases ha : a = q.1
        · simpa [ee, ha] using hpc1 o q.1 q.2
        · simp [ee, ha]
      have h2 := (monAl_le_first Pk.K ((Pk.R.X o).rkF 0 a) (ee o q a) ρ).trans h1
      omega
    · intro o p hp g e N hpe
      simp only [L, List.mem_map, Finset.mem_toList] at hp
      obtain ⟨q, -, rfl⟩ := hp
      obtain ⟨-, rfl, -⟩ := RF.GlobalTheory.mon.inj hpe
      exact ⟨q.1, fun a k ha => by simp [ee, ha]⟩
    · have hrow : ∀ o, ((L o).map fun p => p.1.what₂ (Pk.R.X o).n).sum = 2 * Pk.s * Pk.K := by
        intro o
        simp only [L, List.map_map]
        rw [Finset.sum_map_toList]
        simp [blk, RF.GlobalTheory.what₂]
      rw [Finset.sum_congr rfl fun o _ => hrow o, Finset.sum_const, smul_eq_mul, Finset.card_univ]
      calc 2 * (Fintype.card P.Pl * (2 * Pk.s * Pk.K)) = 4 * Pk.K * Pk.s * Fintype.card P.Pl := by ring
        _ ≤ Pk.nW := Pk.what₂
    · intro o σ k
      have hw : ∀ q : ZMod 2 × Fin Pk.s,
          (blk o q).1.wt (Pk.R.X o) 0 σ k + (blk o q).1.wt (Pk.R.X o) 1 (σ + 1) k =
          if q.1 = σ then (if 1 ≤ k ∧ k ≤ min Pk.K ((Pk.R.X o).rkF 0 σ) then pc o σ q.2 k else 0)
          else 0 := by
        rintro ⟨a, u⟩
        by_cases ha : a = σ
        · subst ha
          simp [blk, ee, RF.GlobalTheory.wt]
        · simp [blk, ee, RF.GlobalTheory.wt, ha, Ne.symm ha]
      calc ((L o).map fun p => p.1.wt (Pk.R.X o) 0 σ k + p.1.wt (Pk.R.X o) 1 (σ + 1) k).sum
          = ∑ q : ZMod 2 × Fin Pk.s,
              ((blk o q).1.wt (Pk.R.X o) 0 σ k + (blk o q).1.wt (Pk.R.X o) 1 (σ + 1) k) := by
            simp only [L, List.map_map]
            rw [Finset.sum_map_toList]
            rfl
        _ = ∑ q : ZMod 2 × Fin Pk.s, if q.1 = σ then
              (if 1 ≤ k ∧ k ≤ min Pk.K ((Pk.R.X o).rkF 0 σ) then pc o σ q.2 k else 0) else 0 :=
            Finset.sum_congr rfl fun q _ => hw q
        _ = ∑ u : Fin Pk.s,
              (if 1 ≤ k ∧ k ≤ min Pk.K ((Pk.R.X o).rkF 0 σ) then pc o σ u k else 0) := by
            rw [Fintype.sum_prod_type, Finset.sum_eq_single σ]
            · simp
            · intro b _ hb
              simp [hb]
            · simp
        _ = Pk.gaC o σ k := by
            by_cases hk : 1 ≤ k ∧ k ≤ min Pk.K ((Pk.R.X o).rkF 0 σ)
            · simp only [if_pos hk]
              exact hpc2 o σ k
            · simp only [if_neg hk, Finset.sum_const_zero]
              symm
              by_contra hne
              have hs := Pk.supp o σ k hne
              exact hk ⟨hs.1, le_min hs.2.2 hs.2.1⟩

end GlobalTheory.GoodDepth.Zero

theorem GlobalTheory.GoodDepth.zeroBd : GlobalTheory.GoodDepth.ZeroBd :=
  ⟨fun P l Pk => GlobalTheory.GoodDepth.Zero.zero_of_pkg GlobalTheory.T.monomialBlock_supply_both_typings.2 P l Pk,
    fun P l Pk => GlobalTheory.GoodDepth.Zero.zero_of_pkgC GlobalTheory.T.monomialBlock_supply_both_typings.2 P l Pk⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LargePrimePackagesDepthNonposStatement
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.DIV Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.GoodDepth NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.largePrime_packages_depth_nonpos : ZeroBd := by
  first | exact @GlobalTheory.GoodDepth.zeroBd | exact GlobalTheory.GoodDepth.zeroBd | (intros; apply GlobalTheory.GoodDepth.zeroBd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.GoodPlaceDepthBoundProof
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.DIV Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.GoodDepth NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false

namespace GlobalTheory.GoodDepth

theorem le_DF_of_mult_pos {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (τ : E →+* ℂ) (h : 0 < Dw.mult τ) : a (τ, 0) ≤ DF Dw a := by
  unfold DF
  calc a (τ, 0) = a (τ, ((⟨0, h⟩ : Fin (Dw.mult τ)) : ℕ)) := rfl
    _ ≤ ∑ i : Fin (Dw.mult τ), a (τ, i) :=
        Finset.single_le_sum (f := fun i : Fin (Dw.mult τ) => a (τ, i)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
    _ ≤ _ := Finset.single_le_sum (f := fun τ => ∑ i : Fin (Dw.mult τ), a (τ, i)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ τ)

theorem thl_nonneg' (k l : ℕ) : 0 ≤ thl k l := by
  unfold thl
  apply Real.sSup_nonneg
  rintro t ⟨i, -, -, -, rfl⟩
  positivity

theorem one_le_log_of_five_le {k : ℕ} (hk : 5 ≤ k) : 1 ≤ Real.log k := by
  have h5 : (5 : ℝ) ≤ k := by exact_mod_cast hk
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

theorem parOK_parAt {N : NumDatum} {j l : ℕ} (h : ParOK (parOf N j l)) (d : ℕ) [NeZero d] (pos : RPl N.R → ℕ → RPl N.R) :
    ParOK (parAt N j d pos) := ⟨h.card, h.m_pos, h.mk_le, h.r_eq, h.SE_nonneg⟩

theorem degHyp2_parOf {N : NumDatum} {j : ℕ} {W : RPl N.R → ℕ} {T θ0 rest C1 : ℝ}
    (h : RF.DegHyp2 (parAt N j 1 fun z _ => z) W T θ0 rest C1) (l : ℕ) : RF.DegHyp2 (parOf N j l) W T θ0 rest C1 :=
  ⟨h.T_one, h.w_pos, h.TW_lo, h.TW_hi, h.th_rng, h.th_m, h.rest_nonneg, h.rest_le⟩

private theorem odd_ordP_of_conjIn {N : NumDatum} {l : ℕ} (h : ConjIn N l) : Odd (N.ordP l) := by
  unfold NumDatum.ordP
  rw [if_neg (by rw [h.1]; simp)]
  exact h.2

theorem nuGood : NuGoodSt := by
  intro C1 hC1
  obtain ⟨CI, hCI, HI⟩ := GlobalTheory.T.inertPrimeDepthContentBound_proof C1 hC1
  obtain ⟨CP, hCP, HP⟩ := GlobalTheory.T.complexConjFrobeniusDepthContentBound_proof C1 hC1
  obtain ⟨CS, hCS, HS⟩ := GlobalTheory.T.splitPrimeDepthContentBound_proof C1 hC1
  obtain ⟨CC, hCC, HC⟩ := UpperTheory.rowBound_le_Fnum_sum_add_error GlobalTheory.T.oddLevelBlock_bound_attained.2 GlobalTheory.T.characterBlocks_attain_bound.2 GlobalTheory.T.monomialBlock_supply_both_typings.2 C1 hC1
  obtain ⟨HZ, -⟩ := GlobalTheory.T.largePrime_packages_depth_nonpos
  refine ⟨2 * CI + 2 * CP + 2 * CC + CS + 2, by positivity, ?_⟩
  intro E _ _ _ H Dw lv Xo c _ hstar hIC hPk N j pl a nW T b L w hj1 hjm hpl hp hq hdom hG hw hb la h2 hq' hd hg0 hg1 hM
  obtain ⟨PI, PP, PS, PZ, -, PC, PZC⟩ := hPk
  have hl : (resCharOf la).Prime := Crude.resCharOf_prime la
  have hin := hG.inert_ge _ hl
  have red := GlobalTheory.GoodDepth.nuW_bound_of_charts E H Dw lv Xo c hIC la lv.M a nW
  have PI' := PI hstar N j pl a hj1 hjm hpl hp hq hdom la h2 hq' hd hM hin
  have PP' := PP hstar N j pl a hj1 hjm hpl hp hq hdom la h2 hq' hd hM hin
  have PS' := PS hstar N j pl a hj1 hjm hpl hp hq hdom la h2 hq' hd hM hin
  have PZ' := PZ hstar N j pl a hj1 hjm hpl hp hq hdom la h2 hq' hd hM hin
  have PZC' := PZC hstar N j pl a hj1 hjm hpl hp hq hdom la h2 hq' hd hM hin
  have PC' := PC hstar N j pl a hj1 hjm hpl hp hq hdom la h2 hq' hd hM hin
  clear PI PP PS PZ PZC PC
  generalize resCharOf la = l at *
  obtain ⟨θ0, hdeg⟩ := hG.deg
  have hT1 : (1 : ℝ) ≤ T := hdeg.T_one
  have hT1' : 1 ≤ T := by exact_mod_cast hT1
  have hwpos : ∀ z, 0 ≤ N.w j z := fun z => (hdeg.w_pos z).le
  have hsum : 0 ≤ ∑ z, N.w j z := Finset.sum_nonneg fun z _ => hwpos z
  have hw0 : 0 ≤ w := hsum.trans hw
  obtain ⟨hF0, htri, hOK, hFC, hFI⟩ := GlobalTheory.ContentValue.main N j l hl h2 hq' hd hg0 hg1 hwpos hG.ratio
  have hm2 := N.R.two_le_m
  have hmk := N.R.m_add_three_le_k
  have hf2 : 2 ≤ N.R.f := hm2.trans N.R.m_le_f
  have hr : N.R.r = N.R.k + N.R.m - 1 := rfl
  have hn : ((N.R.k - 1 : ℕ) : ℝ) = (N.R.k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hl3 : 3 ≤ l := by
    have := hl.two_le
    have := ne_two_of_not_small h2
    omega
  have hlpos : (0 : ℝ) < l := by exact_mod_cast (by omega : 0 < l)
  obtain ⟨R1, R2, R3, R4⟩ := GlobalTheory.RowBudgets.main N.R.r N.R.f (N.R.k - 1) N.R.m nW T l N.R.k b L w (by omega) (by omega) (by omega)
    hf2 hT1' (by omega) hG.L_ge hG.log_le (by rw [hn]; exact hG.what₂)
  have R5 := UpperTheory.f_mul_leastAdmissibleLevel_rows_le N.R.r N.R.f (N.R.k - 1) N.R.m nW l N.R.k L (by omega) (by omega) (by omega)
    hf2 (by omega) hG.L_ge hG.log_le (by rw [hn]; exact hG.what₂)
  rw [hn] at R3 R4
  have hzero : ∀ s : ℕ, (∀ τ, 0 < Dw.mult τ → a (τ, 0) ≤ s * (l - 1)) → 4 * N.R.r * s * N.R.f ≤ nW →
      ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → ∀ y : IntFr Xo c T io, y.IsAlg →
      ∀ (C : IntChart T io y) (ν : ℝ), (((ramOverZ la : ℝ) * ν : ℝ) : EReal) ≤ nuLocC C e lv.M a nW → ν ≤ 0 := by
    intro s hs hrow V io e ho y hy C ν hν
    by_cases hc : ConjIn N l
    · obtain ⟨Pk, rfl⟩ := PZC' V io e ho y hy C nW ν hν hc.1 (odd_ordP_of_conjIn hc) hwpos s hs hrow
      exact UpperTheory.pkgZeroCs_nu_nonpos_of_monSupply GlobalTheory.T.monomialBlock_supply_both_typings.2 _ _ Pk
    · obtain ⟨d, _, pos, Pk, rfl⟩ := PZ' V io e ho y hy C nW ν hν hc hwpos s hs
        (le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num)))) hrow)
      exact HZ _ _ Pk
  have hSE : 0 ≤ N.Sc + N.eta := hOK.SE_nonneg
  have hlog : 1 ≤ Real.log N.R.k := one_le_log_of_five_le (by omega)
  have hth := thl_nonneg' N.R.k l
  set A1 : ℝ := Real.log N.R.k * N.R.m * w / l with hA1
  set A2 : ℝ := N.R.f * N.R.k * (N.Sc + N.eta) / l with hA2
  set A3 : ℝ := N.R.k * thl N.R.k l * w with hA3
  set A4 : ℝ := if N.sc.X'' N.R.n < (l : ℝ) then N.R.k * w / (l : ℝ) ^ 2 else 0 with hA4
  have a1 : 0 ≤ A1 := by positivity
  have a2 : 0 ≤ A2 := by positivity
  have a3 : 0 ≤ A3 := by positivity
  have a4 : 0 ≤ A4 := by rw [hA4]; split_ifs <;> positivity
  have hA4' : (if N.sc.X'' N.R.n < (l : ℝ) then 2 * (N.R.k * (∑ z, N.w j z) / (l : ℝ) ^ 2) else 0) ≤ 2 * A4 := by
    rw [hA4]
    split_ifs
    · gcongr
    · simp
  set B : ℝ := N.FjP j l + (2 * CI + 2 * CP + 2 * CC + CS + 2) * (A1 + A2 + A3 + A4) with hB
  have hB0 : 0 ≤ B := by positivity
  have hTpos : (0 : ℝ) < T := by linarith
  have hmain : ∀ (V : CDVR) (io : c.F →+* V.Fr) (e : ℕ), OverLa la V.V io e → ∀ y : IntFr Xo c V io, y.IsAlg →
      ∀ (C : IntChart V io y) (ν : ℝ), (((ramOverZ la : ℝ) * ν : ℝ) : EReal) ≤ nuLocC C e lv.M a nW → ν ≤ B / T := by
    intro V io e ho y hy C ν hν
    have hBT : 0 ≤ B / T := by positivity
    by_cases hb0 : b < 0
    · refine le_trans (hzero 0 (fun τ hτ => ?_) (by simp) V io e ho y hy C ν hν) hBT
      have h1 := hG.first τ hτ
      have h2 : (0 : ℝ) ≤ (T : ℝ) * a (τ, 0) := by positivity
      exfalso; linarith
    push Not at hb0
    by_cases hl2 : N.R.m * b / (T * N.R.f * ((N.R.k : ℝ) - 1) ^ 3 * L) ≤ l
    · obtain ⟨s, hs1, hs2⟩ := R3 hl3 hb0 hl2
      exact le_trans (hzero s (fun τ hτ => hs2 _ (hG.first τ hτ)) hs1 V io e ho y hy C ν hν) hBT
    push Not at hl2
    have hadd := R4 (by omega) hl2 hb
    have herr : errB (parOf N j l) l T ≤ 2 * (A1 + A2 + A3) := by
      have e1 : Real.log N.R.k * N.R.m * (∑ z, N.w j z) / l ≤ A1 := by rw [hA1]; gcongr
      have e3 : N.R.k * thl N.R.k l * (∑ z, N.w j z) ≤ A3 := by rw [hA3]; gcongr
      have : errB (parOf N j l) l T = Real.log N.R.k * N.R.m * (∑ z, N.w j z) / l + A2 +
        N.R.k * thl N.R.k l * (∑ z, N.w j z) + T * N.R.f * ((N.R.k : ℝ) - 1) ^ 3 * Real.log N.R.k ^ 2 := rfl
      rw [this]; linarith
    rw [le_div_iff₀ hTpos, mul_comm]
    have p1 := mul_nonneg hCI.le a1
    have p2 := mul_nonneg hCI.le a2
    have p3 := mul_nonneg hCI.le a3
    have p4 := mul_nonneg hCI.le a4
    have q1 := mul_nonneg hCP.le a1
    have q2 := mul_nonneg hCP.le a2
    have q3 := mul_nonneg hCP.le a3
    have q4 := mul_nonneg hCP.le a4
    have s1 := mul_nonneg hCS.le a1
    have s2 := mul_nonneg hCS.le a2
    have s3 := mul_nonneg hCS.le a3
    have s4 := mul_nonneg hCS.le a4
    have c1 := mul_nonneg hCC.le a1
    have c2 := mul_nonneg hCC.le a2
    have c3 := mul_nonneg hCC.le a3
    have c4 := mul_nonneg hCC.le a4
    rcases htri with hI | hS
    · have h5 := hin hI
      by_cases hc : PhiC N l
      · obtain ⟨Pk, hT, hν'⟩ := PP' V io e ho y hy C nW ν hν hc T θ0 C1 (degHyp2_parOf hdeg l) R1
        have h1 := HP _ l hOK hl h5 Pk
        rw [hT, hν'] at h1
        have h2 := hFC hc
        have h3 := mul_le_mul_of_nonneg_left herr hCP.le
        have h1' : (T : ℝ) * ν ≤ ((N.R.k : ℝ) - 1) * (∑ z, N.w j z) / ((l : ℝ) ^ 2 - 1) + CP * errB (parOf N j l) l T := h1
        rw [hB]; linarith
      by_cases hcs : ConjIn N l
      · obtain ⟨Pk, hT, hν'⟩ := PC' V io e ho y hy C nW ν hν hcs.1 (odd_ordP_of_conjIn hcs) T θ0 C1
          (degHyp2_parOf hdeg l) (R5 h5)
        have h1 := HC _ l hOK.card hOK.m_pos hOK.mk_le hOK.r_eq hOK.SE_nonneg hl h5 Pk
        rw [hT, hν'] at h1
        have h2 := hFI hI hc Pk.Z Pk.hZ
        have h3 := mul_le_mul_of_nonneg_left herr hCC.le
        have h1' := le_trans h1 (add_le_add h2 h3)
        rw [hB]; linarith
      · obtain ⟨Pk, hT, hν'⟩ := PI' V io e ho y hy C nW ν hν hI hcs T θ0 C1 (degHyp2_parOf hdeg l) (R2 h5)
        have h1 := HI _ l hOK hl h5 Pk
        rw [hT, hν'] at h1
        have h2 := hFI hI hc Pk.Z Pk.hZ
        have h3 := mul_le_mul_of_nonneg_left herr hCI.le
        have h1' := le_trans h1 (add_le_add h2 h3)
        rw [hB]; linarith
    · obtain ⟨d, _, pos, Pk, hT, hν'⟩ := PS' V io e ho y hy C nW ν hν hS T θ0 C1 hdeg
        (le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num))) R1)
      have h1 := HS _ l (parOK_parAt hOK d pos) hl Pk
      rw [hT, hν'] at h1
      have h1' : (T : ℝ) * ν ≤ CS * ((N.R.m * (∑ z, N.w j z) + N.R.f * N.R.k * (N.Sc + N.eta)) / l) := h1
      have e1 : (N.R.m * (∑ z, N.w j z) + N.R.f * N.R.k * (N.Sc + N.eta)) / l ≤ A1 + A2 := by
        rw [hA1, hA2, add_div]
        have : (N.R.m : ℝ) * (∑ z, N.w j z) ≤ Real.log N.R.k * N.R.m * w := by
          calc (N.R.m : ℝ) * (∑ z, N.w j z) = 1 * N.R.m * (∑ z, N.w j z) := by ring
            _ ≤ _ := by gcongr
        gcongr
      have h3 := mul_le_mul_of_nonneg_left e1 hCS.le
      rw [hB]; linarith
  obtain ⟨r1, r2, -⟩ := red (B / T) (by positivity) hmain
  refine ⟨r1, ?_, fun hDF => ?_⟩
  · rw [le_div_iff₀ hTpos, mul_comm] at r2
    exact r2
  · refine (red 0 le_rfl (hzero 1 (fun τ hτ => ?_) ?_)).2.2 rfl
    · have := le_DF_of_mult_pos Dw a τ hτ
      omega
    · rw [mul_one]
      exact le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num))) R1

end GlobalTheory.GoodDepth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.GoodPlaceDepthBoundProofStatement
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.DIV Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.GoodDepth NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodPlaceDepthBound_proof : NuGoodSt := by
  first | exact @GlobalTheory.GoodDepth.nuGood | exact GlobalTheory.GoodDepth.nuGood | (intros; apply GlobalTheory.GoodDepth.nuGood <;> assumption)
end
