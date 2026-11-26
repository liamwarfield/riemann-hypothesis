module

public import Development.WeilBound.CoreStatements.FlagImmersions.TowerRationalWeightBound

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.FlagImmersions.FlagDegLeGap
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

private theorem prod_le_mul_two_pow_card {ι : Type} [Fintype ι] [DecidableEq ι] (f : ι → ℝ)
    (h0 : ∀ x, 0 ≤ f x) (h2 : ∀ x, f x ≤ 2) (x₀ : ι) (c : ℝ) (hc : f x₀ = c) :
    ∏ x, f x ≤ c * 2 ^ Fintype.card ι := by
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ x₀), hc]
  refine mul_le_mul_of_nonneg_left ?_ (hc ▸ h0 x₀)
  calc ∏ x ∈ Finset.univ.erase x₀, f x ≤ ∏ x ∈ Finset.univ.erase x₀, (2 : ℝ) :=
        Finset.prod_le_prod₀ (fun x _ => h0 x) (fun x _ => h2 x)
    _ = 2 ^ (Finset.univ.erase x₀).card := Finset.prod_const 2
    _ ≤ 2 ^ Fintype.card ι := pow_le_pow_right₀ (by norm_num) (Finset.card_le_univ _)

theorem flagDeg_le_gap : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ), 1 ≤ j → j < N → ∃ C : ℝ, 0 ≤ C ∧ ∀ (lam : Wt Ψ N) (τ₀ : Ψ), ‖lam‖ ≤ 1 → Dominant lam → flagDeg lam ≤ C * gap j lam τ₀ := by
  intro Ψ _ _ N j hj hjN
  refine ⟨((GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N).factorial : ℝ) * 2 ^ Fintype.card (Ψ × Fin N × Fin N),
    by positivity, ?_⟩
  intro lam τ₀ hlam hdom
  have hj1 : j - 1 < N := by omega
  have hbound : ∀ τ i, |lam τ i| ≤ 1 := by
    intro τ i
    have h1 := norm_le_pi_norm (show Ψ → Fin N → ℝ from lam) τ
    have h2 := norm_le_pi_norm (lam τ) i
    rw [Real.norm_eq_abs] at h2
    have h3 : ‖(show Ψ → Fin N → ℝ from lam)‖ ≤ 1 := hlam
    linarith
  have hfac : ∀ τ (i k : Fin N),
      0 ≤ (if i < k then (lam τ i - lam τ k) / (((k : ℕ) : ℝ) - ((i : ℕ) : ℝ)) else 1) ∧
        (if i < k then (lam τ i - lam τ k) / (((k : ℕ) : ℝ) - ((i : ℕ) : ℝ)) else 1) ≤ 2 := by
    intro τ i k
    split_ifs with hik
    · have hik' : (i : ℕ) < (k : ℕ) := hik
      have hd : ((i : ℕ) : ℝ) + 1 ≤ ((k : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hik'
      have hmono := hdom τ i k hik.le
      have hi := abs_le.mp (hbound τ i)
      have hk := abs_le.mp (hbound τ k)
      constructor
      · apply div_nonneg <;> linarith
      · rw [div_le_iff₀ (by linarith)]
        linarith
    · norm_num
  have hgap : GlobalTheory.CompanionTheory.Ar.Top.gap j lam τ₀ = lam τ₀ ⟨j - 1, hj1⟩ - lam τ₀ ⟨j, hjN⟩ := by
    unfold GlobalTheory.CompanionTheory.Ar.Top.gap GlobalTheory.CompanionTheory.Ar.Top.ent
    rw [dite_eq_left hj1, dite_eq_left hjN]
  have hx0 : (if (⟨j - 1, hj1⟩ : Fin N) < ⟨j, hjN⟩ then
      (lam τ₀ ⟨j - 1, hj1⟩ - lam τ₀ ⟨j, hjN⟩) /
        ((((⟨j, hjN⟩ : Fin N) : ℕ) : ℝ) - (((⟨j - 1, hj1⟩ : Fin N) : ℕ) : ℝ)) else 1) =
      lam τ₀ ⟨j - 1, hj1⟩ - lam τ₀ ⟨j, hjN⟩ := by
    have hlt : (⟨j - 1, hj1⟩ : Fin N) < ⟨j, hjN⟩ := by
      rw [Fin.lt_def]
      show j - 1 < j
      omega
    rw [if_pos hlt]
    have hden : (((⟨j, hjN⟩ : Fin N) : ℕ) : ℝ) - (((⟨j - 1, hj1⟩ : Fin N) : ℕ) : ℝ) = 1 := by
      show ((j : ℕ) : ℝ) - ((j - 1 : ℕ) : ℝ) = 1
      rw [Nat.cast_sub hj, Nat.cast_one]
      ring
    rw [hden, div_one]
  have key := prod_le_mul_two_pow_card
    (fun x : Ψ × Fin N × Fin N => if x.2.1 < x.2.2 then
      (lam x.1 x.2.1 - lam x.1 x.2.2) / (((x.2.2 : ℕ) : ℝ) - ((x.2.1 : ℕ) : ℝ)) else 1)
    (fun x => (hfac x.1 x.2.1 x.2.2).1) (fun x => (hfac x.1 x.2.1 x.2.2).2)
    (τ₀, ⟨j - 1, hj1⟩, ⟨j, hjN⟩) _ hx0
  simp only [Fintype.prod_prod_type] at key
  obtain ⟨hdeg, -, -⟩ := GlobalTheory.T.flag_degree_weight_formula Ψ N lam
  rw [hdeg, hgap]
  calc _ ≤ ((GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N).factorial : ℝ) *
        ((lam τ₀ ⟨j - 1, hj1⟩ - lam τ₀ ⟨j, hjN⟩) * 2 ^ Fintype.card (Ψ × Fin N × Fin N)) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = _ := by ring

end RootFieldNumerics
end

section -- merged from Development.WeilBound.CoreStatements.FlagImmersions.ContinuousBoundWallExtension
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

theorem exists_rat_near_le (δ : ℝ) (hδ : 0 < δ) (x : ℝ) : ∃ q : ℚ, |(q : ℝ)| ≤ |x| ∧ |(q : ℝ) - x| ≤ δ := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · obtain ⟨q, h1, h2⟩ := exists_rat_btwn (show x < min (x + δ) 0 from lt_min (by linarith) hx)
    have m1 := min_le_left (x + δ) 0
    have m2 := min_le_right (x + δ) 0
    refine ⟨q, ?_, ?_⟩
    · rw [abs_of_neg hx, abs_of_nonpos (by linarith)]
      linarith
    · rw [abs_le]
      constructor <;> linarith
  · exact ⟨0, by simp [hx], by simp [hx, hδ.le]⟩
  · obtain ⟨q, h1, h2⟩ := exists_rat_btwn (show max (x - δ) 0 < x from max_lt (by linarith) hx)
    have m1 := le_max_left (x - δ) 0
    have m2 := le_max_right (x - δ) 0
    refine ⟨q, ?_, ?_⟩
    · rw [abs_of_pos hx, abs_of_nonneg (by linarith)]
      linarith
    · rw [abs_le]
      constructor <;> linarith

theorem continuous_bound_wall_extension : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (c₀ b : ℝ) (τ₀ : Ψ) (Φ : Wt Ψ N → ℝ), 1 ≤ j → j < N → 0 < c₀ → Continuous Φ → (∀ lam, IsRatWt lam → InWall j τ₀ (c₀ / 2) lam → |Φ lam| ≤ b) → ∀ lam, InWall j τ₀ c₀ lam → |Φ lam| ≤ b := by
  intro Ψ _ _ N j c₀ b τ₀ Φ hj hjN hc hΦ hrat lam hlam
  have hex : ∀ n : ℕ, ∀ x : ℝ, ∃ q : ℚ, |(q:ℝ)| ≤ |x| ∧ |(q:ℝ) - x| ≤ c₀ / 4 * (1 / ((n:ℝ) + 1)) :=
    fun n x => exists_rat_near_le _ (by positivity) x
  choose F hF1 hF2 using hex
  let A : ℕ → Wt Ψ N := fun n τ i => (F n (lam τ i) : ℝ)
  have hδ : ∀ n : ℕ, c₀ / 4 * (1 / ((n:ℝ) + 1)) ≤ c₀ / 4 := by
    intro n
    have h1 : 1 / ((n:ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
    exact mul_le_of_le_one_right (by positivity) h1
  have hent : ∀ n τ k, k < N → ent (A n) τ k = (F n (ent lam τ k) : ℝ) := by
    intro n τ k hk
    simp [ent, hk, A]
  have hclose : ∀ n τ k, k < N → |ent (A n) τ k - ent lam τ k| ≤ c₀ / 4 := by
    intro n τ k hk
    rw [hent n τ k hk]
    exact (hF2 n _).trans (hδ n)
  have hin : ∀ n, InWall j τ₀ (c₀ / 2) (A n) := by
    intro n
    obtain ⟨hn, hg0, hgτ, hcg⟩ := hlam
    have hj1 : j - 1 < N := by omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun τ =>
        (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => ?_
      have h1 : ‖lam τ i‖ ≤ 1 / 2 := (norm_le_pi_norm (lam τ) i).trans ((norm_le_pi_norm lam τ).trans hn)
      simp only [Real.norm_eq_abs, A] at h1 ⊢
      exact (hF1 n _).trans h1
    · simp only [gap] at hg0 ⊢
      rw [hent n τ₀ _ hj1, hent n τ₀ _ hjN, show ent lam τ₀ (j - 1) = ent lam τ₀ j by linarith]
      ring
    · intro τ hτ
      have h := hgτ τ hτ
      simp only [gap] at h ⊢
      have a1 := abs_le.1 (hclose n τ _ hj1)
      have a2 := abs_le.1 (hclose n τ _ hjN)
      linarith [a1.1, a1.2, a2.1, a2.2]
    · intro τ i hi hij
      have h := hcg τ i hi hij
      have a1 := abs_le.1 (hclose n τ i (by omega))
      have a2 := abs_le.1 (hclose n τ (i + 1) hi)
      linarith [a1.1, a1.2, a2.1, a2.2]
  have hAr : ∀ n, IsRatWt (A n) := fun n τ i => ⟨F n (lam τ i), rfl⟩
  have htend : Tendsto A atTop (𝓝 lam) := by
    rw [tendsto_pi_nhds]
    intro τ
    rw [tendsto_pi_nhds]
    intro i
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Tendsto (fun n : ℕ => c₀ / 4 * (1 / ((n:ℝ) + 1))) atTop (𝓝 0) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (c₀ / 4)
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim
    simp only [A, Real.norm_eq_abs]
    exact hF2 n _
  have hΦt : Tendsto (fun n => |Φ (A n)|) atTop (𝓝 |Φ lam|) :=
    (continuous_abs.tendsto _).comp ((hΦ.tendsto lam).comp htend)
  exact le_of_tendsto' hΦt fun n => hrat _ (hAr n) (hin n)

end RootFieldNumerics
end

section -- merged from Development.WeilBound.CoreStatements.FlagImmersions.LinearRootPowerLipschitz
open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics.Pc

theorem abs_prod_sub_prod_le {ι : Type} (s : Finset ι) (a b : ι → ℝ) (δ : ℝ)
    (ha : ∀ i, |a i| ≤ 1) (hb : ∀ i, |b i| ≤ 1) (h : ∀ i, |a i - b i| ≤ δ) :
    |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ s.card * δ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.card_insert_of_notMem hi]
    have hB : |∏ i ∈ s, b i| ≤ 1 := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) (fun i _ => hb i)
    have e : a i * ∏ i ∈ s, a i - b i * ∏ i ∈ s, b i =
        a i * (∏ i ∈ s, a i - ∏ i ∈ s, b i) + (a i - b i) * ∏ i ∈ s, b i := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have h1 : |a i| * |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ 1 * (s.card * δ) :=
      mul_le_mul (ha i) ih (abs_nonneg _) zero_le_one
    have h2 : |a i - b i| * |∏ i ∈ s, b i| ≤ δ * 1 :=
      mul_le_mul (h i) hB (abs_nonneg _) ((abs_nonneg _).trans (h i))
    push_cast
    linarith

def linCoef {Ψ : Type} {N : ℕ} (lam : Wt Ψ N) (s : ℝ) : Option (Ψ × Fin N) → ℝ
  | none => s
  | some x => -lam x.1 x.2

theorem linA_eq {Ψ : Type} [Fintype Ψ] {N : ℕ} (lam : Wt Ψ N) (s : ℝ) :
    linA lam s = ∑ j, C (linCoef lam s j) * X j := by
  rw [Fintype.sum_option]
  simp [linA, toA, linRoot, linCoef, add_comm]

theorem map_linA_pow {Ψ : Type} [Fintype Ψ] {N : ℕ} (d : ℕ) (Φ : RPA Ψ N →ₗ[ℝ] ℝ)
    (lam : Wt Ψ N) (s : ℝ) [Fintype (Fin d → Option (Ψ × Fin N))] :
    Φ (linA lam s ^ d) = ∑ w : Fin d → Option (Ψ × Fin N), (∏ k, linCoef lam s (w k)) *
      Φ (monomial (∑ k, Finsupp.single (w k) 1) 1) := by
  have := RootFieldNumerics.map_prod_linear (Option (Ψ × Fin N)) d Φ (fun _ => linCoef lam s)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← linA_eq] at this
  convert this

end RootFieldNumerics.Pc

theorem RootFieldNumerics.linear_root_power_lipschitz : ∀ (Ψ : Type) [Fintype Ψ] (N d : ℕ), (∀ Φ : RPA Ψ N →ₗ[ℝ] ℝ, Continuous fun z : Wt Ψ N × ℝ => Φ (linA z.1 z.2 ^ d)) ∧ (∀ lam : Wt Ψ N, linA lam 0 = toA (linRoot lam)) ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ (Φ : RPA Ψ N →ₗ[ℝ] ℝ) (b : ℝ), (∀ m, |Φ (monomial m 1)| ≤ b) → ∀ (lam mu : Wt Ψ N) (s s' : ℝ), ‖lam‖ ≤ 1 → ‖mu‖ ≤ 1 → |s| ≤ 1 → |s'| ≤ 1 → |Φ (linA lam s ^ d) - Φ (linA mu s' ^ d)| ≤ C * b * (‖lam - mu‖ + |s - s'|) := by
  intro Ψ _ N d
  classical
  refine ⟨fun Φ => ?_, fun lam => by simp [linA], ?_⟩
  · simp only [RootFieldNumerics.Pc.map_linA_pow]
    refine continuous_finsetSum _ fun w _ => Continuous.mul
      (continuous_finsetProd _ fun k _ => ?_) continuous_const
    cases w k with
    | none => exact continuous_snd
    | some x =>
      simp only [RootFieldNumerics.Pc.linCoef]
      fun_prop
  · refine ⟨(Fintype.card (Fin d → Option (Ψ × Fin N)) : ℝ) * d, by positivity, ?_⟩
    intro Φ b hb lam mu s s' hl hm hs hs'
    have hb0 : 0 ≤ b := (abs_nonneg _).trans (hb 0)
    have hent : ∀ (l : Wt Ψ N) τ i, |l τ i| ≤ ‖l‖ := fun l τ i =>
      (norm_le_pi_norm (l τ) i).trans (norm_le_pi_norm l τ)
    have hc : ∀ (l : Wt Ψ N) (t : ℝ), ‖l‖ ≤ 1 → |t| ≤ 1 → ∀ j, |RootFieldNumerics.Pc.linCoef l t j| ≤ 1 := by
      intro l t h1 h2 j
      cases j with
      | none => exact h2
      | some x => simpa [RootFieldNumerics.Pc.linCoef] using (hent l x.1 x.2).trans h1
    have hd : ∀ j, |RootFieldNumerics.Pc.linCoef lam s j - RootFieldNumerics.Pc.linCoef mu s' j| ≤ ‖lam - mu‖ + |s - s'| := by
      intro j
      cases j with
      | none => exact le_add_of_nonneg_left (norm_nonneg _)
      | some x =>
        have h1 := hent (lam - mu) x.1 x.2
        have e : RootFieldNumerics.Pc.linCoef lam s (some x) - RootFieldNumerics.Pc.linCoef mu s' (some x) =
            -((lam - mu) x.1 x.2) := by
          simp only [RootFieldNumerics.Pc.linCoef, Pi.sub_apply]; ring
        rw [e, abs_neg]
        exact h1.trans (le_add_of_nonneg_right (abs_nonneg _))
    rw [RootFieldNumerics.Pc.map_linA_pow, RootFieldNumerics.Pc.map_linA_pow, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ (d * (‖lam - mu‖ + |s - s'|) * b) fun w _ => ?_).trans ?_
    · rw [← sub_mul, abs_mul]
      refine mul_le_mul ?_ (hb _) (abs_nonneg _) (by positivity)
      simpa using RootFieldNumerics.Pc.abs_prod_sub_prod_le Finset.univ _ _ _
        (fun k => hc lam s hl hs (w k)) (fun k => hc mu s' hm hs' (w k)) (fun k => hd (w k))
    · rw [Finset.card_univ, nsmul_eq_mul]
      exact le_of_eq (by ring)
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelPointHeightDegree
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArithIntersectionMultilinearSlotStatement
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArithIntersectionMultilinear
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem intersection_combLine : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ) (L : Fin d → HermLine ι) (k : Fin d) (J : Type) [Fintype J] (ℓ : J → HermLine ι) (n : J → ℤ), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P d → (∀ i, IsSmoothHerm (L i)) → (∀ j, IsSmoothHerm (ℓ j)) → II K ι P d (Function.update L k (combLine ℓ n)) = ∑ j, (n j : ℝ) * II K ι P d (Function.update L k (ℓ j)) :=
  @RootFieldNumerics.intersection_multilinear_one_position

end GlobalTheory.CompanionTheory.Ar.Top
end

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_intersection_multilinear : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ) (L : Fin d → HermLine ι) (k : Fin d) (J : Type) [Fintype J] (ℓ : J → HermLine ι) (n : J → ℤ), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P d → (∀ i, IsSmoothHerm (L i)) → (∀ j, IsSmoothHerm (ℓ j)) → II K ι P d (Function.update L k (combLine ℓ n)) = ∑ j, (n j : ℝ) * II K ι P d (Function.update L k (ℓ j)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.intersection_combLine | exact GlobalTheory.CompanionTheory.Ar.Top.intersection_combLine | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.intersection_combLine <;> assumption)
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelPointHeightDegree
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem ht_combLine_integral_multiple : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (t : ℝ) (lam : Wt Ψ N) (s : ℝ) (q : ℕ) (n : Option (Ψ × Fin N) → ℤ) (W : Ideal (MRing M.ι)), (∀ j, (n j : ℝ) = q * M.coef lam s j) → M.IsPt W → 0 < degC W ∧ II M.K M.ι W 1 ![combLine (M.line t) n] = q * M.ht II t lam s W * degC W := by
  intro II hII Ψ _ N M t lam s q n W hn hW
  have hpos : 0 < degC W := GroundTheory.Heights₂.Heights.LowerBoundFree.degC_pos_of_isArithVar_one hW.1
  refine ⟨hpos, ?_⟩
  have hl : ∀ j, IsSmoothHerm (M.line t j) := by
    intro j
    cases j with
    | none => exact M.A_smooth
    | some r => exact M.x_smooth t r
  have hupd : ∀ B : HermLine M.ι, Function.update (![M.A] : Fin 1 → HermLine M.ι) 0 B = ![B] := by
    intro B
    funext k
    obtain rfl : k = 0 := Subsingleton.elim _ _
    simp
  have hL : ∀ i, IsSmoothHerm ((![M.A] : Fin 1 → HermLine M.ι) i) := by
    intro i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact M.A_smooth
  have h := GlobalTheory.T.arith_intersection_multilinear II hII M.K M.ι W 1 ![M.A] 0 (Option (Ψ × Fin N)) (M.line t) n hW.1 hL hl
  simp only [hupd] at h
  have hd : (degC W : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
  rw [h, RootModel.ht, mul_assoc, div_mul_cancel₀ _ hd, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hn j, mul_assoc]

end GlobalTheory.CompanionTheory.Ar.Top
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelPointHeightDegreeStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_model_point_height_degree : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (t : ℝ) (lam : Wt Ψ N) (s : ℝ) (q : ℕ) (n : Option (Ψ × Fin N) → ℤ) (W : Ideal (MRing M.ι)), (∀ j, (n j : ℝ) = q * M.coef lam s j) → M.IsPt W → 0 < degC W ∧ II M.K M.ι W 1 ![combLine (M.line t) n] = q * M.ht II t lam s W * degC W := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.ht_combLine_integral_multiple | exact GlobalTheory.CompanionTheory.Ar.Top.ht_combLine_integral_multiple | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.ht_combLine_integral_multiple <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelSemipositiveConj
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelSemipositiveConj
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem semipositive_integral_multiple : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (t : ℝ) (lam : Wt Ψ N) (s : ℝ) (q : ℕ) (n : Option (Ψ × Fin N) → ℤ), (∀ j, (n j : ℝ) = q * M.coef lam s j) → M.Semipos t lam s → IsSemipositiveH M.P (combLine (M.line t) n) ∧ IsConjInvariantH (combLine (M.line t) n) :=
  RootFieldNumerics.root_model_line_semipositive

end GlobalTheory.CompanionTheory.Ar.Top
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelSemipositiveConjStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_model_semipositive_conj : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (t : ℝ) (lam : Wt Ψ N) (s : ℝ) (q : ℕ) (n : Option (Ψ × Fin N) → ℤ), (∀ j, (n j : ℝ) = q * M.coef lam s j) → M.Semipos t lam s → IsSemipositiveH M.P (combLine (M.line t) n) ∧ IsConjInvariantH (combLine (M.line t) n) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.semipositive_integral_multiple | exact GlobalTheory.CompanionTheory.Ar.Top.semipositive_integral_multiple | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.semipositive_integral_multiple <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerComponentHeightBound
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerComponentHeightBound
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem deg_bounds : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KleimanNefFStatement → (∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], ReciprocityTheory.ChartRestriction.G.AI.I1.ExistsUniqueStatement ℚ ι) → ReciprocityTheory.ChartRestriction.G.Geo.DivSuppArithStatement → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N), T.Proportional → T.I7 → ∀ (B : ℕ) (c : T.Comp) (lam : Wt Ψ N) (s : ℚ), IsRatWt lam → 0 ≤ s → Dominant lam → Dominant (T.lamS lam s) → 0 ≤ T.mDeg B c lam s ∧ T.mDeg B c lam s ≤ T.vol c * flagDeg lam :=
  RootFieldNumerics.tower_rational_weight_bound

end GlobalTheory.CompanionTheory.Ar.Top
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerComponentHeightBoundStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tower_component_height_bound : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KleimanNefFStatement → (∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], ReciprocityTheory.ChartRestriction.G.AI.I1.ExistsUniqueStatement ℚ ι) → ReciprocityTheory.ChartRestriction.G.Geo.DivSuppArithStatement → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N), T.Proportional → T.I7 → ∀ (B : ℕ) (c : T.Comp) (lam : Wt Ψ N) (s : ℚ), IsRatWt lam → 0 ≤ s → Dominant lam → Dominant (T.lamS lam s) → 0 ≤ T.mDeg B c lam s ∧ T.mDeg B c lam s ≤ T.vol c * flagDeg lam := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.deg_bounds | exact GlobalTheory.CompanionTheory.Ar.Top.deg_bounds | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.deg_bounds <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerGapHeightUniformBound
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ZhangUpperBoundDensePoints
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ZhangUpperBoundDensePoints
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem zhang_upper_bound_root_model : SuccessiveMinimaUpperBound → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (t : ℝ) (lam : Wt Ψ N) (s : ℚ) (e : ℝ) (F : Set (Ideal (MRing M.ι))), IsRatWt lam → M.Semipos t lam s → M.NefFib lam s → IsZariskiDense M.P F → (∀ W ∈ F, M.IsPt W ∧ M.ht II t lam s W ≤ e) → M.arFun II t (linA lam s ^ (dimFl Ψ N + 1)) ≤ ((dimFl Ψ N : ℝ) + 1) * e * M.geoFun (linA lam s ^ dimFl Ψ N) := by
  intro hZ II hII Ψ _ N M t lam s e F hrat hsp hnef hF hpt
  obtain ⟨q, n, hq, hn⟩ := GlobalTheory.T.rational_weight_integral_coeffs Ψ N M lam s hrat
  have hsemi := GlobalTheory.T.root_model_semipositive_conj Ψ N M t lam s q n hn hsp
  have hnf := (GlobalTheory.T.root_model_curve_degree_nef Ψ N M t lam s q n hn).2 hnef
  have hA := GlobalTheory.T.root_model_arith_intersection_formula II hII Ψ N M t lam s q n hn
  have hG := GlobalTheory.T.root_model_log_integral_formula II hII Ψ N M t (fun _ => lam) (fun _ => (s : ℝ)) q (fun _ => n)
    (fun _ j => hn j)
  have hGeo : geomDeg M.P (combLine (M.line t) n) (dimFl Ψ N) =
      M.δ * (q : ℝ) ^ dimFl Ψ N * M.geoFun (linA lam s ^ dimFl Ψ N) := by
    have hprod : (∏ _k : Fin (dimFl Ψ N), linA lam (s : ℝ)) = linA lam s ^ dimFl Ψ N := by
      simp
    rw [hprod] at hG
    exact hG
  have key := hZ M.K M.ι M.P M.P (dimFl Ψ N) (combLine (M.line t) n) ((q : ℝ) * e) F II hII.1
    M.arith le_rfl hsemi.1 hnf hsemi.2
    (by
      intro W hW
      obtain ⟨hp, hle⟩ := hpt W hW
      obtain ⟨-, hI⟩ := GlobalTheory.T.root_model_point_height_degree II hII Ψ N M t lam s q n W hn hp
      refine ⟨hp.1, hp.2, ?_⟩
      rw [hI]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg q))
        (Nat.cast_nonneg _))
    hF
  rw [hA, hGeo] at key
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hδ : (0 : ℝ) < M.δ := Nat.cast_pos.mpr M.δ_pos
  have hpos : (0 : ℝ) < M.δ * (q : ℝ) ^ (dimFl Ψ N + 1) := mul_pos hδ (pow_pos hqR _)
  refine le_of_mul_le_mul_left ?_ hpos
  calc _ ≤ _ := key
    _ = _ := by push_cast; ring

end GlobalTheory.CompanionTheory.Ar.Top
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ZhangUpperBoundDensePointsStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zhang_upper_bound_dense_points : SuccessiveMinimaUpperBound → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (t : ℝ) (lam : Wt Ψ N) (s : ℚ) (e : ℝ) (F : Set (Ideal (MRing M.ι))), IsRatWt lam → M.Semipos t lam s → M.NefFib lam s → IsZariskiDense M.P F → (∀ W ∈ F, M.IsPt W ∧ M.ht II t lam s W ≤ e) → M.arFun II t (linA lam s ^ (dimFl Ψ N + 1)) ≤ ((dimFl Ψ N : ℝ) + 1) * e * M.geoFun (linA lam s ^ dimFl Ψ N) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.zhang_upper_bound_root_model | exact GlobalTheory.CompanionTheory.Ar.Top.zhang_upper_bound_root_model | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.zhang_upper_bound_root_model <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ZhangLowerBoundRational
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ZhangLowerBoundRational
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem zhang_lower_bound_root_model : SuccessiveMinimaLowerBound → ∀ II : IntersectionSystem, IsFullIntersectionSystem II →
    ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (t : ℝ) (lam : Wt Ψ N) (s : ℚ) (e : ℝ), IsRatWt lam →
      M.Semipos t lam s → M.NefFib lam s → (∀ W, M.IsPt W → e ≤ M.ht II t lam s W) →
      ((dimFl Ψ N : ℝ) + 1) * e * M.geoFun (linA lam s ^ dimFl Ψ N) ≤
        M.arFun II t (linA lam s ^ (dimFl Ψ N + 1)) := by
  intro hZ1 II hII Ψ _ N M t lam s e hrat hsemi hnef hpts
  obtain ⟨q, n, hq, hn⟩ := GlobalTheory.T.rational_weight_integral_coeffs Ψ N M lam s hrat
  have hp := GlobalTheory.T.root_model_semipositive_conj Ψ N M t lam s q n hn hsemi
  have hnf := (GlobalTheory.T.root_model_curve_degree_nef Ψ N M t lam s q n hn).2 hnef
  have hW : ∀ W, ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar W 1 → M.P ≤ W →
      ((q : ℝ) * e) * degC W ≤ II M.K M.ι W 1 ![combLine (M.line t) n] := by
    intro W h1 h2
    have hpt : M.IsPt W := ⟨h1, h2⟩
    obtain ⟨hd, hI⟩ := GlobalTheory.T.root_model_point_height_degree II hII Ψ N M t lam s q n W hn hpt
    rw [hI]
    have hq' : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    have hd' : (0 : ℝ) ≤ degC W := Nat.cast_nonneg _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hpts W hpt) hq') hd'
  have key := hZ1 M.K M.ι M.P M.P (dimFl Ψ N) (combLine (M.line t) n) ((q : ℝ) * e) II hII.1 M.arith le_rfl
    hp.1 hnf hp.2 hW
  have hgeo : geomDeg M.P (combLine (M.line t) n) (dimFl Ψ N) =
      (M.δ : ℝ) * (q : ℝ) ^ dimFl Ψ N * M.geoFun (linA lam s ^ dimFl Ψ N) := by
    have := GlobalTheory.T.root_model_log_integral_formula II hII Ψ N M t (fun _ => lam) (fun _ => (s : ℝ)) q (fun _ => n) (fun _ j => hn j)
    simpa [geomDeg, Finset.prod_const] using this
  rw [hgeo, GlobalTheory.T.root_model_arith_intersection_formula II hII Ψ N M t lam s q n hn] at key
  have hδ : (0 : ℝ) < M.δ := by exact_mod_cast M.δ_pos
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hc : (0 : ℝ) < (M.δ : ℝ) * (q : ℝ) ^ (dimFl Ψ N + 1) := by positivity
  refine le_of_mul_le_mul_left ?_ hc
  calc (M.δ : ℝ) * (q : ℝ) ^ (dimFl Ψ N + 1) * (((dimFl Ψ N : ℝ) + 1) * e * M.geoFun (linA lam s ^ dimFl Ψ N))
      = ((dimFl Ψ N + 1 : ℕ) : ℝ) * ((q : ℝ) * e) *
          ((M.δ : ℝ) * (q : ℝ) ^ dimFl Ψ N * M.geoFun (linA lam s ^ dimFl Ψ N)) := by
        push_cast; ring
    _ ≤ _ := key

end GlobalTheory.CompanionTheory.Ar.Top
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ZhangLowerBoundRationalStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zhang_lower_bound_rational : SuccessiveMinimaLowerBound → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (t : ℝ) (lam : Wt Ψ N) (s : ℚ) (e : ℝ), IsRatWt lam → M.Semipos t lam s → M.NefFib lam s → (∀ W, M.IsPt W → e ≤ M.ht II t lam s W) → ((dimFl Ψ N : ℝ) + 1) * e * M.geoFun (linA lam s ^ dimFl Ψ N) ≤ M.arFun II t (linA lam s ^ (dimFl Ψ N + 1)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.zhang_lower_bound_root_model | exact GlobalTheory.CompanionTheory.Ar.Top.zhang_lower_bound_root_model | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.zhang_lower_bound_root_model <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerGapHeightUniformBound
noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem l1_le_card_mul_of_norm_le_one {Ψ : Type} [Fintype Ψ] {N : ℕ} (lam : Wt Ψ N) (h : ‖lam‖ ≤ 1) :
    l1 lam ≤ (Fintype.card Ψ : ℝ) * N := by
  have hb : ∀ τ i, |lam τ i| ≤ 1 := fun τ i => by
    have h1 : ‖lam τ‖ ≤ ‖lam‖ := norm_le_pi_norm lam τ
    have h2 : ‖lam τ i‖ ≤ ‖lam τ‖ := norm_le_pi_norm (lam τ) i
    rw [← Real.norm_eq_abs]; linarith
  unfold l1
  calc ∑ τ, ∑ i, |lam τ i| ≤ ∑ _τ : Ψ, ∑ _i : Fin N, (1 : ℝ) :=
        Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => hb τ i
    _ = (Fintype.card Ψ : ℝ) * N := by simp

theorem RootTower.isRatWt_lamS {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (T : RootTower Ψ N) {lam : Wt Ψ N}
    (s : ℚ) (h : IsRatWt lam) : IsRatWt (T.lamS lam s) := by
  intro τ i
  obtain ⟨q1, h1⟩ := h τ i
  obtain ⟨q2, h2⟩ := T.nu_rat τ i
  refine ⟨q1 - s * q2, ?_⟩
  simp only [RootTower.lamS, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, h1, h2]
  push_cast; ring

theorem mbarTop_squeeze : SuccessiveMinimaLowerBound → SuccessiveMinimaUpperBound → ∀ II : IntersectionSystem, IsFullIntersectionSystem II →
    ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N), T.I3 → T.I5 II → T.I6 II →
    ∀ c₀ > (0 : ℝ), ∃ θ₀ > (0 : ℝ), ∃ C : ℝ, 0 ≤ C ∧ ∀ B : ℕ, 2 ≤ B → ∀ (c : T.Comp) (lam : Wt Ψ N) (θ : ℝ) (s : ℚ),
      IsRatWt lam → ‖lam‖ ≤ 1 → 0 < θ → θ ≤ θ₀ → (s : ℝ) = θ ^ 2 → (∀ τ, θ ≤ gap T.j lam τ) →
      CompactGapsGE T.j c₀ lam → Dominant (T.lamS lam s) → NefThreshold T.j B (T.lamS lam s) →
      0 ≤ T.mDeg B c lam s →
      |T.mbarTop II B c lam s| ≤ C * Real.log (B / (s : ℝ)) * T.mDeg B c lam s := by
  intro hZ1 hZ2 II hII Ψ _ _ N T hI3 hI5 hI6 c₀ hc₀
  obtain ⟨s₀, hs₀, h3⟩ := hI3 ((Fintype.card Ψ : ℝ) * N)
  obtain ⟨θ₅, hθ₅, C₅, h5⟩ := hI5 c₀ hc₀
  obtain ⟨θ₆, hθ₆, C₆, h6⟩ := hI6 c₀ hc₀
  have hD : (0 : ℝ) ≤ (dimFl Ψ N : ℝ) + 1 := by positivity
  refine ⟨min (min θ₅ θ₆) (min 1 s₀), lt_min (lt_min hθ₅ hθ₆) (lt_min one_pos hs₀),
    ((dimFl Ψ N : ℝ) + 1) * (max C₅ 0 + max C₆ 0),
    mul_nonneg hD (add_nonneg (le_max_right _ _) (le_max_right _ _)), ?_⟩
  intro B hB c lam θ s hrat hnorm hθ hθ₀ hs hgap hcg hdom hnef hdeg
  have hθ1 : θ ≤ 1 := le_trans hθ₀ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hθs : θ ≤ s₀ := le_trans hθ₀ (le_trans (min_le_right _ _) (min_le_right _ _))
  have hθ5 : θ ≤ θ₅ := le_trans hθ₀ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hθ6 : θ ≤ θ₆ := le_trans hθ₀ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hspos : (0 : ℝ) < s := by rw [hs]; positivity
  have hs1 : (s : ℝ) ≤ 1 := by rw [hs]; nlinarith
  have hss₀ : (s : ℝ) ≤ s₀ := by rw [hs]; nlinarith
  have hl1 : l1 lam ≤ (Fintype.card Ψ : ℝ) * N := l1_le_card_mul_of_norm_le_one lam hnorm
  obtain ⟨hNef, hSemi⟩ := h3 B hB c lam (s : ℝ) hl1 hspos hss₀ hdom hnef
  have hrat' : IsRatWt (T.lamS lam s) := RootTower.isRatWt_lamS T s hrat
  have hlow := h5 B hB c lam θ s hrat hnorm hθ hθ5 hs hgap hcg
  obtain ⟨F, hF, hFpt⟩ := h6 B hB c lam θ s hrat hnorm hθ hθ6 hs hgap hcg
  have hL : ((dimFl Ψ N : ℝ) + 1) * (-(C₅ * Real.log (B / (s : ℝ)))) * T.mDeg B c lam s ≤
      T.mbarTop II B c lam s :=
    GlobalTheory.T.zhang_lower_bound_rational hZ1 II hII Ψ N (T.M B c) (scale s) (T.lamS lam s) s (-(C₅ * Real.log (B / (s : ℝ))))
      hrat' hSemi hNef (fun W hW => hlow W hW)
  have hU : T.mbarTop II B c lam s ≤
      ((dimFl Ψ N : ℝ) + 1) * (C₆ * Real.log B) * T.mDeg B c lam s :=
    GlobalTheory.T.zhang_upper_bound_dense_points hZ2 II hII Ψ N (T.M B c) (scale s) (T.lamS lam s) s (C₆ * Real.log B) F
      hrat' hSemi hNef hF (fun W hW => hFpt W hW)
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ B))
  have hlogBs : Real.log B ≤ Real.log (B / (s : ℝ)) :=
    Real.log_le_log hBpos (by rw [le_div_iff₀ hspos]; nlinarith)
  have hLg : 0 ≤ Real.log (B / (s : ℝ)) := le_trans hlogB hlogBs
  have hP : 0 ≤ ((dimFl Ψ N : ℝ) + 1) * Real.log (B / (s : ℝ)) * T.mDeg B c lam s :=
    mul_nonneg (mul_nonneg hD hLg) hdeg
  have hQ : 0 ≤ ((dimFl Ψ N : ℝ) + 1) * Real.log B * T.mDeg B c lam s :=
    mul_nonneg (mul_nonneg hD hlogB) hdeg
  have hQP : ((dimFl Ψ N : ℝ) + 1) * Real.log B * T.mDeg B c lam s ≤
      ((dimFl Ψ N : ℝ) + 1) * Real.log (B / (s : ℝ)) * T.mDeg B c lam s :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlogBs hD) hdeg
  have k1 := mul_le_mul_of_nonneg_right
    (show C₅ ≤ max C₅ 0 + max C₆ 0 by linarith [le_max_left C₅ 0, le_max_right C₆ 0]) hP
  have k2 := mul_le_mul_of_nonneg_right (le_max_left C₆ 0) hQ
  have k3 := mul_le_mul_of_nonneg_left hQP (le_max_right C₆ 0)
  have k4 := mul_le_mul_of_nonneg_right
    (show max C₆ 0 ≤ max C₅ 0 + max C₆ 0 by linarith [le_max_right C₅ 0]) hP
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

end GlobalTheory.CompanionTheory.Ar.Top
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerGapHeightUniformBoundStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tower_gap_height_uniform_bound : SuccessiveMinimaLowerBound → SuccessiveMinimaUpperBound → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N), T.I3 → T.I5 II → T.I6 II → ∀ c₀ > (0 : ℝ), ∃ θ₀ > (0 : ℝ), ∃ C : ℝ, 0 ≤ C ∧ ∀ B : ℕ, 2 ≤ B → ∀ (c : T.Comp) (lam : Wt Ψ N) (θ : ℝ) (s : ℚ), IsRatWt lam → ‖lam‖ ≤ 1 → 0 < θ → θ ≤ θ₀ → (s : ℝ) = θ ^ 2 → (∀ τ, θ ≤ gap T.j lam τ) → CompactGapsGE T.j c₀ lam → Dominant (T.lamS lam s) → NefThreshold T.j B (T.lamS lam s) → 0 ≤ T.mDeg B c lam s → |T.mbarTop II B c lam s| ≤ C * Real.log (B / (s : ℝ)) * T.mDeg B c lam s := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.mbarTop_squeeze | exact GlobalTheory.CompanionTheory.Ar.Top.mbarTop_squeeze | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.mbarTop_squeeze <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PerturbedWeightGapBounds
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PerturbedWeightGapBounds
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem hypotheses_hold_for_large_bound : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (c₀ θ₀ : ℝ), 0 < c₀ → 0 < θ₀ → ∃ B₁ : ℕ, ∀ B : ℕ, B₁ ≤ B → ∀ (τ₀ : Ψ) (lam₀ : Wt Ψ N), InWall T.j τ₀ c₀ lam₀ → let θ : ℝ := 5 * Fintype.card Ψ / B; let lam : Wt Ψ N := fun τ i => lam₀ τ i + (if τ = τ₀ ∧ (i : ℕ) < T.j then 2 * θ else 0); 3 ≤ B ∧ 0 < θ ∧ θ ≤ θ₀ ∧ θ ≤ 1 ∧ ‖lam‖ ≤ 1 ∧ ‖T.lamS lam (θ ^ 2)‖ ≤ 1 ∧ (∀ τ, θ ≤ gap T.j lam τ) ∧ gap T.j lam τ₀ = 2 * θ ∧ CompactGapsGE T.j c₀ lam ∧ Dominant lam ∧ Dominant (T.lamS lam (θ ^ 2)) ∧ NefThreshold T.j B (T.lamS lam (θ ^ 2)) ∧ ‖T.lamS lam (θ ^ 2) - lam₀‖ ≤ 2 * θ + ‖T.nu‖ * θ ^ 2 :=
  @RootFieldNumerics.perturbed_weight_wall_bounds

end GlobalTheory.CompanionTheory.Ar.Top
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PerturbedWeightGapBoundsStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.perturbed_weight_gap_bounds : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (c₀ θ₀ : ℝ), 0 < c₀ → 0 < θ₀ → ∃ B₁ : ℕ, ∀ B : ℕ, B₁ ≤ B → ∀ (τ₀ : Ψ) (lam₀ : Wt Ψ N), InWall T.j τ₀ c₀ lam₀ → let θ : ℝ := 5 * Fintype.card Ψ / B; let lam : Wt Ψ N := fun τ i => lam₀ τ i + (if τ = τ₀ ∧ (i : ℕ) < T.j then 2 * θ else 0); 3 ≤ B ∧ 0 < θ ∧ θ ≤ θ₀ ∧ θ ≤ 1 ∧ ‖lam‖ ≤ 1 ∧ ‖T.lamS lam (θ ^ 2)‖ ≤ 1 ∧ (∀ τ, θ ≤ gap T.j lam τ) ∧ gap T.j lam τ₀ = 2 * θ ∧ CompactGapsGE T.j c₀ lam ∧ Dominant lam ∧ Dominant (T.lamS lam (θ ^ 2)) ∧ NefThreshold T.j B (T.lamS lam (θ ^ 2)) ∧ ‖T.lamS lam (θ ^ 2) - lam₀‖ ≤ 2 * θ + ‖T.nu‖ * θ ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.hypotheses_hold_for_large_bound | exact GlobalTheory.CompanionTheory.Ar.Top.hypotheses_hold_for_large_bound | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.hypotheses_hold_for_large_bound <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagDegreeLeGap
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagDegreeLeGap
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem flagDeg_le_mul_gap : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ), 1 ≤ j → j < N → ∃ C : ℝ, 0 ≤ C ∧ ∀ (lam : Wt Ψ N) (τ₀ : Ψ), ‖lam‖ ≤ 1 → Dominant lam → flagDeg lam ≤ C * gap j lam τ₀ := by
  exact @RootFieldNumerics.flagDeg_le_gap

end GlobalTheory.CompanionTheory.Ar.Top
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagDegreeLeGapStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_degree_le_gap : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ), 1 ≤ j → j < N → ∃ C : ℝ, 0 ≤ C ∧ ∀ (lam : Wt Ψ N) (τ₀ : Ψ), ‖lam‖ ≤ 1 → Dominant lam → flagDeg lam ≤ C * gap j lam τ₀ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.flagDeg_le_mul_gap | exact GlobalTheory.CompanionTheory.Ar.Top.flagDeg_le_mul_gap | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.flagDeg_le_mul_gap <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ContinuousWallBoundExtend
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ContinuousWallBoundExtend
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem rat_points_suffice_on_walls : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (c₀ b : ℝ) (τ₀ : Ψ) (Φ : Wt Ψ N → ℝ), 1 ≤ j → j < N → 0 < c₀ → Continuous Φ → (∀ lam, IsRatWt lam → InWall j τ₀ (c₀ / 2) lam → |Φ lam| ≤ b) → ∀ lam, InWall j τ₀ c₀ lam → |Φ lam| ≤ b :=
  @RootFieldNumerics.continuous_bound_wall_extension

end GlobalTheory.CompanionTheory.Ar.Top
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ContinuousWallBoundExtendStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_wall_bound_extend : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (c₀ b : ℝ) (τ₀ : Ψ) (Φ : Wt Ψ N → ℝ), 1 ≤ j → j < N → 0 < c₀ → Continuous Φ → (∀ lam, IsRatWt lam → InWall j τ₀ (c₀ / 2) lam → |Φ lam| ≤ b) → ∀ lam, InWall j τ₀ c₀ lam → |Φ lam| ≤ b := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.rat_points_suffice_on_walls | exact GlobalTheory.CompanionTheory.Ar.Top.rat_points_suffice_on_walls | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.rat_points_suffice_on_walls <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArithFunctionalLipschitzWeights
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArithFunctionalLipschitzWeights
open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem linA_pow_continuous_lipschitz : ∀ (Ψ : Type) [Fintype Ψ] (N d : ℕ), (∀ Φ : RPA Ψ N →ₗ[ℝ] ℝ, Continuous fun z : Wt Ψ N × ℝ => Φ (linA z.1 z.2 ^ d)) ∧ (∀ lam : Wt Ψ N, linA lam 0 = toA (linRoot lam)) ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ (Φ : RPA Ψ N →ₗ[ℝ] ℝ) (b : ℝ), (∀ m, |Φ (monomial m 1)| ≤ b) → ∀ (lam mu : Wt Ψ N) (s s' : ℝ), ‖lam‖ ≤ 1 → ‖mu‖ ≤ 1 → |s| ≤ 1 → |s'| ≤ 1 → |Φ (linA lam s ^ d) - Φ (linA mu s' ^ d)| ≤ C * b * (‖lam - mu‖ + |s - s'|) :=
  @RootFieldNumerics.linear_root_power_lipschitz

end GlobalTheory.CompanionTheory.Ar.Top
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArithFunctionalLipschitzWeightsStatement
open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_functional_lipschitz_weights : ∀ (Ψ : Type) [Fintype Ψ] (N d : ℕ), (∀ Φ : RPA Ψ N →ₗ[ℝ] ℝ, Continuous fun z : Wt Ψ N × ℝ => Φ (linA z.1 z.2 ^ d)) ∧ (∀ lam : Wt Ψ N, linA lam 0 = toA (linRoot lam)) ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ (Φ : RPA Ψ N →ₗ[ℝ] ℝ) (b : ℝ), (∀ m, |Φ (monomial m 1)| ≤ b) → ∀ (lam mu : Wt Ψ N) (s s' : ℝ), ‖lam‖ ≤ 1 → ‖mu‖ ≤ 1 → |s| ≤ 1 → |s'| ≤ 1 → |Φ (linA lam s ^ d) - Φ (linA mu s' ^ d)| ≤ C * b * (‖lam - mu‖ + |s - s'|) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.linA_pow_continuous_lipschitz | exact GlobalTheory.CompanionTheory.Ar.Top.linA_pow_continuous_lipschitz | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.linA_pow_continuous_lipschitz <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerWeilTheorem
noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

namespace WallBound

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

theorem l1_le_card_mul_of_norm_le_one' (lam : Wt Ψ N) (h : ‖lam‖ ≤ 1) : l1 lam ≤ (Fintype.card Ψ : ℝ) * N := by
  have hb : ∀ τ i, |lam τ i| ≤ 1 := fun τ i => by
    have h1 : ‖lam τ‖ ≤ ‖lam‖ := norm_le_pi_norm lam τ
    have h2 : ‖lam τ i‖ ≤ ‖lam τ‖ := norm_le_pi_norm (lam τ) i
    rw [Real.norm_eq_abs] at h2
    linarith
  unfold l1
  calc ∑ τ, ∑ i, |lam τ i| ≤ ∑ _τ : Ψ, ∑ _i : Fin N, (1 : ℝ) :=
        Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => hb τ i
    _ = (Fintype.card Ψ : ℝ) * N := by simp

theorem toA_linRoot_pow (lam : Wt Ψ N) (d : ℕ) : toA (linRoot lam ^ d) = linA lam 0 ^ d := by
  simp [toA, linA, map_pow]

theorem continuous_lin_zero (Φ : RPA Ψ N →ₗ[ℝ] ℝ) (d : ℕ)
    (h : Continuous fun z : Wt Ψ N × ℝ => Φ (linA z.1 z.2 ^ d)) :
    Continuous fun lam : Wt Ψ N => Φ (linA lam 0 ^ d) := by
  have hz : Continuous fun lam : Wt Ψ N => ((lam, (0 : ℝ)) : Wt Ψ N × ℝ) :=
    Continuous.prodMk continuous_id continuous_const
  have h2 := h.comp hz
  simp only [Function.comp_def] at h2
  exact h2

theorem continuous_PB (T : RootTower Ψ N) (II : IntersectionSystem) (B : ℕ) :
    Continuous fun lam : Wt Ψ N => T.PB II B lam := by
  obtain ⟨hcont, -, -⟩ := GlobalTheory.T.arith_functional_lipschitz_weights Ψ N (dimFl Ψ N + 1)
  have h : (fun lam : Wt Ψ N => T.PB II B lam) =
      fun lam => ∑ c, (T.M B c).PP II (linA lam 0 ^ (dimFl Ψ N + 1)) := by
    funext lam
    simp only [RootTower.PB, RootTower.PPt, RootTower.PPc, toA_linRoot_pow]
  rw [h]
  exact continuous_finsetSum _ fun c _ => continuous_lin_zero _ _ (hcont _)

theorem one_le_log {B : ℕ} (h : 3 ≤ B) : 1 ≤ Real.log B := by
  have hB : (3 : ℝ) ≤ B := by exact_mod_cast h
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

theorem log_div_le {B : ℕ} (h : 3 ≤ B) (a : ℝ) (ha : 1 ≤ a) :
    Real.log (B / (a / B) ^ 2) ≤ 3 * Real.log B := by
  have hB : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have ha0 : 0 < a := by linarith
  have h1 : (B : ℝ) / (a / B) ^ 2 ≤ (B : ℝ) ^ 3 := by
    rw [div_pow, div_div_eq_mul_div, div_le_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ a ^ 2 := by nlinarith
    nlinarith [pow_pos hB 3]
  have h2 : 0 < (B : ℝ) / (a / B) ^ 2 := by positivity
  calc Real.log (B / (a / B) ^ 2) ≤ Real.log ((B : ℝ) ^ 3) := Real.log_le_log h2 h1
    _ = 3 * Real.log B := by rw [Real.log_pow]; norm_num

theorem three_terms {q a p cs c3 c2 cp c8 v n θ L Ls md dist s : ℝ} (hcs : 0 ≤ cs) (hc8 : 0 ≤ c8) (hcp : 0 ≤ cp)
    (hv : 0 ≤ v) (hn : 0 ≤ n) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hL : 1 ≤ L) (hs : s = θ ^ 2)
    (hLs : Ls ≤ 3 * L) (hLs0 : 0 ≤ Ls) (hmd0 : 0 ≤ md) (hmd : md ≤ v * (c8 * (2 * θ)))
    (hsq : |a| ≤ cs * Ls * md) (hap : |a - p| ≤ c3 * s)
    (hpq : |p - q| ≤ cp * (|c2| * L) * (dist + |s - 0|)) (hdist : dist ≤ 2 * θ + n * θ ^ 2) :
    |q| ≤ (|c3| + 6 * cs * c8 * v + cp * |c2| * (3 + n)) * (θ * L) := by
  have hθ2 : θ ^ 2 ≤ θ := by nlinarith
  have hL0 : 0 ≤ L := by linarith
  have hθL : 0 ≤ θ * L := by positivity
  have t1 : |a| ≤ 6 * cs * c8 * v * (θ * L) := by
    have e1 : Ls * md ≤ (3 * L) * (v * (c8 * (2 * θ))) :=
      mul_le_mul hLs hmd hmd0 (by linarith)
    calc |a| ≤ cs * Ls * md := hsq
      _ = cs * (Ls * md) := by ring
      _ ≤ cs * ((3 * L) * (v * (c8 * (2 * θ)))) := mul_le_mul_of_nonneg_left e1 hcs
      _ = 6 * cs * c8 * v * (θ * L) := by ring
  have t2 : |a - p| ≤ |c3| * (θ * L) := by
    have e : s ≤ θ * L := by
      rw [hs]
      nlinarith
    have hs0 : 0 ≤ s := by rw [hs]; positivity
    calc |a - p| ≤ c3 * s := hap
      _ ≤ |c3| * s := mul_le_mul_of_nonneg_right (le_abs_self _) hs0
      _ ≤ |c3| * (θ * L) := mul_le_mul_of_nonneg_left e (abs_nonneg _)
  have t3 : |p - q| ≤ cp * |c2| * (3 + n) * (θ * L) := by
    have hs0 : 0 ≤ s := by rw [hs]; positivity
    have e : dist + |s - 0| ≤ (3 + n) * θ := by
      rw [sub_zero, abs_of_nonneg hs0, hs]
      nlinarith [mul_le_mul_of_nonneg_left hθ2 hn]
    have hk : 0 ≤ cp * (|c2| * L) := by positivity
    calc |p - q| ≤ cp * (|c2| * L) * (dist + |s - 0|) := hpq
      _ ≤ cp * (|c2| * L) * ((3 + n) * θ) := mul_le_mul_of_nonneg_left e hk
      _ = cp * |c2| * (3 + n) * (θ * L) := by ring
  have tri : |q| ≤ |a| + |a - p| + |p - q| := by
    have h1 : q = a - (a - p) - (p - q) := by ring
    calc |q| = |a - (a - p) - (p - q)| := by rw [← h1]
      _ ≤ |a - (a - p)| + |p - q| := abs_sub _ _
      _ ≤ |a| + |a - p| + |p - q| := by gcongr; exact abs_sub _ _
  linarith

end WallBound


open WallBound in
theorem thmW_tower : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KleimanNefFStatement →
    (∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], ReciprocityTheory.ChartRestriction.G.AI.I1.ExistsUniqueStatement ℚ ι) →
    ReciprocityTheory.ChartRestriction.G.Geo.DivSuppArithStatement → SuccessiveMinimaLowerBound → SuccessiveMinimaUpperBound → ∀ II : IntersectionSystem,
    IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N),
    T.Proportional → T.I1 II → T.I2 II → T.I3 → T.I5 II → T.I6 II → T.I7 → T.ThmW II := by
  intro hKl hEx hDs hZ1 hZ2 II hII Ψ _ _ N T hP h1 h2 h3 h5 h6 h7 c₀ hc₀
  have hc₁ : 0 < c₀ / 2 := by positivity
  obtain ⟨θ₀, hθ₀, Cs, hCs, hsq⟩ := GlobalTheory.T.tower_gap_height_uniform_bound hZ1 hZ2 II hII Ψ N T h3 h5 h6 (c₀ / 2) hc₁
  obtain ⟨s₀, hs₀, C3, hI2⟩ := h2 ((Fintype.card Ψ : ℝ) * N)
  obtain ⟨C2, hI1⟩ := h1
  obtain ⟨C8, hC8, hdeg⟩ := GlobalTheory.T.flag_degree_le_gap Ψ N T.j T.j_pos T.j_lt
  obtain ⟨-, hlin, Cp, hCp, hLip⟩ := GlobalTheory.T.arith_functional_lipschitz_weights Ψ N (dimFl Ψ N + 1)
  obtain ⟨B₁, hB₁⟩ := GlobalTheory.T.perturbed_weight_gap_bounds Ψ N T (c₀ / 2) (min θ₀ s₀) hc₁ (lt_min hθ₀ hs₀)
  refine ⟨(∑ c, (|C3| + 6 * Cs * C8 * T.vol c + Cp * |C2| * (3 + ‖T.nu‖))) * (5 * Fintype.card Ψ), B₁,
    fun B hB τ₀ lam₀ hlam₀ => ?_⟩
  refine GlobalTheory.T.continuous_wall_bound_extend Ψ N T.j c₀ _ τ₀ (fun l => T.PB II B l) T.j_pos T.j_lt hc₀ (continuous_PB T II B) ?_ lam₀ hlam₀
  intro l hlr hlw
  obtain ⟨hB3, hθ, hθle, hθ1, hnl, hnl2, hgaps, hgap0, hcg, hdom, hdom2, hnef, hdist⟩ := hB₁ B hB τ₀ l hlw
  have hf : (1 : ℝ) ≤ Fintype.card Ψ := by
    have : 0 < Fintype.card Ψ := Fintype.card_pos_iff.mpr ⟨τ₀⟩
    exact_mod_cast this
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  set θ : ℝ := 5 * (Fintype.card Ψ : ℝ) / B with hθdef
  set lam : Wt Ψ N := fun τ i => l τ i + (if τ = τ₀ ∧ (i : ℕ) < T.j then 2 * θ else 0) with hlamdef
  let s : ℚ := (5 * (Fintype.card Ψ : ℚ) / B) ^ 2
  have hs : (s : ℝ) = θ ^ 2 := by simp [s, hθdef]
  have hdist' : ‖T.lamS lam s - l‖ ≤ 2 * θ + ‖T.nu‖ * θ ^ 2 := by rw [hs]; exact hdist
  rw [← hs] at hnl2 hdom2 hnef
  have hrat : IsRatWt lam := by
    intro τ i
    obtain ⟨q, hq⟩ := hlr τ i
    by_cases h : τ = τ₀ ∧ (i : ℕ) < T.j
    · exact ⟨q + 2 * (5 * (Fintype.card Ψ : ℚ) / B), by
        show l τ i + (if τ = τ₀ ∧ (i : ℕ) < T.j then 2 * θ else 0) = _
        rw [if_pos h, hq, hθdef]
        push_cast
        ring⟩
    · exact ⟨q, by
        show l τ i + (if τ = τ₀ ∧ (i : ℕ) < T.j then 2 * θ else 0) = _
        rw [if_neg h, hq, add_zero]⟩
  have hs0 : (0 : ℝ) < s := by rw [hs]; positivity
  have hsQ : (0 : ℚ) ≤ s := by exact_mod_cast hs0.le
  have hθ2 : θ ^ 2 ≤ θ := by nlinarith
  have hsle : (s : ℝ) ≤ s₀ := by
    rw [hs]
    exact hθ2.trans (hθle.trans (min_le_right _ _))
  have hs1 : |(s : ℝ)| ≤ 1 := by
    rw [abs_of_pos hs0, hs]
    linarith
  have hnl0 : ‖l‖ ≤ 1 := hlw.1.trans (by norm_num)
  have hL := one_le_log hB3
  have hper : ∀ c, |T.PPc II B c (linRoot l ^ (dimFl Ψ N + 1))| ≤
      (|C3| + 6 * Cs * C8 * T.vol c + Cp * |C2| * (3 + ‖T.nu‖)) * (θ * Real.log B) := by
    intro c
    obtain ⟨hm0, hm1⟩ := GlobalTheory.T.tower_component_height_bound hKl hEx hDs II hII Ψ N T hP h7 B c lam s hrat hsQ hdom hdom2
    have hsqc := hsq B (by omega) c lam θ s hrat hnl hθ (hθle.trans (min_le_left _ _)) hs hgaps hcg hdom2 hnef hm0
    have hI2c := hI2 B (by omega) c lam s (l1_le_card_mul_of_norm_le_one' lam hnl) hs0 hsle hdom2
    have hmono : ∀ m, |(T.M B c).PP II (monomial m 1)| ≤ |C2| * Real.log B := fun m =>
      (hI1 B (by omega) c m).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith))
    have hLipc := hLip ((T.M B c).PP II) (|C2| * Real.log B) hmono (T.lamS lam s) l s 0 hnl2 hnl0 hs1 (by simp)
    have hv : 0 < T.vol c := hP.1 c
    have hmd : T.mDeg B c lam s ≤ T.vol c * (C8 * (2 * θ)) := by
      refine hm1.trans (mul_le_mul_of_nonneg_left ?_ hv.le)
      rw [← hgap0]
      exact hdeg lam τ₀ hnl hdom
    have hLs : Real.log (B / (s : ℝ)) ≤ 3 * Real.log B := by
      rw [hs]
      exact log_div_le hB3 (5 * (Fintype.card Ψ : ℝ)) (by linarith)
    have hLs0 : 0 ≤ Real.log (B / (s : ℝ)) := by
      refine Real.log_nonneg ?_
      rw [le_div_iff₀ hs0, hs]
      have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast (by omega : 1 ≤ B)
      nlinarith
    have hq : T.PPc II B c (linRoot l ^ (dimFl Ψ N + 1)) = (T.M B c).PP II (linA l 0 ^ (dimFl Ψ N + 1)) := by
      simp only [RootTower.PPc, toA_linRoot_pow]
    rw [hq]
    exact three_terms hCs hC8 hCp hv.le (norm_nonneg _) hθ hθ1 hL hs hLs hLs0 hm0 hmd hsqc hI2c hLipc hdist'
  have hsum : |T.PB II B l| ≤
      (∑ c, (|C3| + 6 * Cs * C8 * T.vol c + Cp * |C2| * (3 + ‖T.nu‖))) * (θ * Real.log B) := by
    rw [Finset.sum_mul]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun c _ => hper c)
  refine hsum.trans (le_of_eq ?_)
  rw [hθdef]
  ring

end GlobalTheory.CompanionTheory.Ar.Top
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerWeilTheoremStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tower_weil_theorem : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KleimanNefFStatement → (∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], ReciprocityTheory.ChartRestriction.G.AI.I1.ExistsUniqueStatement ℚ ι) → ReciprocityTheory.ChartRestriction.G.Geo.DivSuppArithStatement → SuccessiveMinimaLowerBound → SuccessiveMinimaUpperBound → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N), T.Proportional → T.I1 II → T.I2 II → T.I3 → T.I5 II → T.I6 II → T.I7 → T.ThmW II := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.thmW_tower | exact GlobalTheory.CompanionTheory.Ar.Top.thmW_tower | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.thmW_tower <;> assumption)
end
