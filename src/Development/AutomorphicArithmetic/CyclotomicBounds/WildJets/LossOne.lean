module

public import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.KerLe
public import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.LogSum

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.DepSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem false_of_coprime_natCast_mem_heightOne {R : Type*} [CommRing R] [IsDomain R] (v : HeightOneSpectrum R)
    (a b : ℕ) (hab : Nat.Coprime a b) (ha : (a : R) ∈ v.asIdeal) (hb : (b : R) ∈ v.asIdeal) : False := by
  obtain ⟨x, y, hxy⟩ := Nat.isCoprime_iff_coprime.2 hab
  have h1 : (x : R) * a + (y : R) * b = 1 := by
    have := congrArg (Int.cast : ℤ → R) hxy
    push_cast at this
    exact this
  apply v.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← h1]
  exact add_mem (Ideal.mul_mem_left _ _ ha) (Ideal.mul_mem_left _ _ hb)

private theorem prime_le_absNorm_of_mem_heightOne (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (l : ℕ)
    (hl : l.Prime) (h : (l : 𝓞 K) ∈ v.asIdeal) : l ≤ Ideal.absNorm v.asIdeal := by
  have hN : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  apply Nat.le_of_dvd (Nat.pos_of_ne_zero hN)
  by_contra hd
  exact false_of_coprime_natCast_mem_heightOne v l _ ((Nat.Prime.coprime_iff_not_dvd hl).2 hd) h (Ideal.absNorm_mem _)

private theorem prime_eq_of_natCast_mem_heightOne {R : Type*} [CommRing R] [IsDomain R] (v : HeightOneSpectrum R)
    (l m : ℕ) (hl : l.Prime) (hm : m.Prime) (h1 : (l : R) ∈ v.asIdeal) (h2 : (m : R) ∈ v.asIdeal) : l = m := by
  by_contra hne
  exact false_of_coprime_natCast_mem_heightOne v l m ((Nat.coprime_primes hl hm).2 hne) h1 h2

theorem UpperTheory.WildA.depSum :
    ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc}, ∃ S : Finset ℕ, GlobalTheory.NormSum.Exponents S (fun l => if l.Prime then (depL G l : ℝ) else 0) (sig G) := by
  classical
  intro D T L sc G
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ v ∈ G.pl.S0, Ideal.absNorm v.asIdeal ≤ N := by
    refine ⟨∑ v ∈ G.pl.S0, Ideal.absNorm v.asIdeal, fun v hv => ?_⟩
    exact Finset.single_le_sum (f := fun v : Pl ↥D.host.F => Ideal.absNorm v.asIdeal)
      (fun _ _ => Nat.zero_le _) hv
  obtain ⟨S, hS⟩ : ∃ S : Finset ℕ, ∀ l, l ∈ S ↔ l.Prime ∧ l ≤ N :=
    ⟨(Finset.range (N + 1)).filter Nat.Prime, fun l => by
      rw [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff, and_comm]⟩
  have key : ∀ v ∈ G.pl.S0, ∀ l : ℕ, l.Prime → ((l : ℕ) : 𝓞 D.host.E) ∈ (G.pl.w v).asIdeal →
      l ≤ Ideal.absNorm v.asIdeal := by
    intro v hv l hl h
    apply prime_le_absNorm_of_mem_heightOne _ v l hl
    have := G.pl.w_over v hv
    rw [← this]
    simpa [IsDedekindDomain.HeightOneSpectrum.under] using h
  have hdep : ∀ l : ℕ, depL G l ≤
      ∑ v ∈ G.pl.S0.filter (fun v => ((l : ℕ) : 𝓞 D.host.E) ∈ (G.pl.w v).asIdeal), G.pl.depth sc v := by
    intro l
    unfold GlobalTheory.SumSize.depL
    apply Finset.sup_le
    intro PP hPP
    obtain ⟨hPP1, hmem⟩ := Finset.mem_filter.1 hPP
    unfold GlobalTheory.ChiGrid.Places.W0 at hPP1
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hPP1
    rw [(GlobalTheory.FunObj.depthAt_w G hv).2]
    exact Finset.single_le_sum (f := fun v => G.pl.depth sc v) (fun _ _ => Nat.zero_le _)
      (Finset.mem_filter.2 ⟨hv, hmem⟩)
  have hinner : ∀ v ∈ G.pl.S0,
      ∑ l ∈ S.filter (fun l : ℕ => ((l : ℕ) : 𝓞 D.host.E) ∈ (G.pl.w v).asIdeal), Real.log (l : ℝ) ≤
        Real.log (Ideal.absNorm v.asIdeal : ℝ) := by
    intro v hv
    rcases (S.filter (fun l : ℕ => ((l : ℕ) : 𝓞 D.host.E) ∈ (G.pl.w v).asIdeal)).eq_empty_or_nonempty
      with he | ⟨l0, hl0⟩
    · rw [he, Finset.sum_empty]
      exact Real.log_natCast_nonneg _
    · obtain ⟨hl0S, hl0P⟩ := Finset.mem_filter.1 hl0
      have hp0 : l0.Prime := ((hS l0).1 hl0S).1
      have hsub : S.filter (fun l : ℕ => ((l : ℕ) : 𝓞 D.host.E) ∈ (G.pl.w v).asIdeal) ⊆ {l0} := by
        intro m hm
        rw [Finset.mem_singleton]
        obtain ⟨hmS, hmP⟩ := Finset.mem_filter.1 hm
        exact prime_eq_of_natCast_mem_heightOne _ m l0 ((hS m).1 hmS).1 hp0 hmP hl0P
      calc _ ≤ ∑ l ∈ ({l0} : Finset ℕ), Real.log (l : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => Real.log_natCast_nonneg i)
        _ = Real.log (l0 : ℝ) := Finset.sum_singleton _ _
        _ ≤ _ := by
          apply Real.log_le_log (by exact_mod_cast hp0.pos)
          exact_mod_cast key v hv l0 hp0 hl0P
  refine ⟨S, ?_⟩
  unfold GlobalTheory.NormSum.Exponents
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro l hl
    exact ((hS l).1 hl).1
  · intro l
    dsimp only
    split_ifs <;> positivity
  · intro l hl
    dsimp only
    split_ifs with hp
    · have h0 : depL G l = 0 := by
        apply Nat.eq_zero_of_le_zero
        refine (hdep l).trans (le_of_eq (Finset.sum_eq_zero ?_))
        intro v hv'
        obtain ⟨hv, hmem⟩ := Finset.mem_filter.1 hv'
        exact absurd ((hS l).2 ⟨hp, (key v hv l hp hmem).trans (hN v hv)⟩) hl
      rw [h0, Nat.cast_zero]
    · rfl
  · dsimp only
    calc ∑ l ∈ S, (if l.Prime then (depL G l : ℝ) else 0) * Real.log (l : ℝ)
        ≤ ∑ l ∈ S, ∑ v ∈ G.pl.S0, (if ((l : ℕ) : 𝓞 D.host.E) ∈ (G.pl.w v).asIdeal then
            (G.pl.depth sc v : ℝ) * Real.log (l : ℝ) else 0) := by
          apply Finset.sum_le_sum
          intro l hl
          have hp : l.Prime := ((hS l).1 hl).1
          rw [if_pos hp, ← Finset.sum_filter, ← Finset.sum_mul]
          apply mul_le_mul_of_nonneg_right _ (Real.log_natCast_nonneg l)
          exact_mod_cast hdep l
      _ = ∑ v ∈ G.pl.S0, (G.pl.depth sc v : ℝ) *
            ∑ l ∈ S.filter (fun l : ℕ => ((l : ℕ) : 𝓞 D.host.E) ∈ (G.pl.w v).asIdeal), Real.log (l : ℝ) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun v _ => ?_)
          rw [Finset.mul_sum, Finset.sum_filter]
      _ ≤ ∑ v ∈ G.pl.S0, (G.pl.depth sc v : ℝ) * Real.log (Ideal.absNorm v.asIdeal : ℝ) := by
          apply Finset.sum_le_sum
          intro v hv
          exact mul_le_mul_of_nonneg_left (hinner v hv) (by positivity)
      _ = sig G := by
          unfold GlobalTheory.SumSize.sig
          rfl
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem expAdd {S S' : Finset ℕ} {f g : ℕ → ℝ} {a b : ℝ} (h : GlobalTheory.NormSum.Exponents S f a)
    (h' : GlobalTheory.NormSum.Exponents S' g b) : GlobalTheory.NormSum.Exponents (S ∪ S') (fun l => f l + g l) (a + b) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨g1, g2, g3, g4⟩ := h'
  refine ⟨fun l hl => (Finset.mem_union.1 hl).elim (h1 l) (g1 l), fun l => add_nonneg (h2 l) (g2 l), fun l hl => ?_, ?_⟩
  · rw [Finset.mem_union, not_or] at hl
    dsimp only
    rw [h3 l hl.1, g3 l hl.2, add_zero]
  · simp only [add_mul, Finset.sum_add_distrib]
    rw [← Finset.sum_subset (Finset.subset_union_left (s₁ := S) (s₂ := S')) (fun l _ hl => by rw [h3 l hl, zero_mul]),
      ← Finset.sum_subset (Finset.subset_union_right (s₁ := S) (s₂ := S')) (fun l _ hl => by rw [g3 l hl, zero_mul])]
    exact add_le_add h4 g4

private theorem expMul {S : Finset ℕ} {f : ℕ → ℝ} {a c : ℝ} (hc : 0 ≤ c) (h : GlobalTheory.NormSum.Exponents S f a) :
    GlobalTheory.NormSum.Exponents S (fun l => c * f l) (c * a) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, fun l => mul_nonneg hc (h2 l), fun l hl => ?_, ?_⟩
  · dsimp only
    rw [h3 l hl, mul_zero]
  · simp only [mul_assoc, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left h4 hc

private theorem expMono {S : Finset ℕ} {f : ℕ → ℝ} {a b : ℝ} (h : GlobalTheory.NormSum.Exponents S f a) (hab : a ≤ b) :
    GlobalTheory.NormSum.Exponents S f b := ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.trans hab⟩

private theorem expOne (d : ℕ) : GlobalTheory.NormSum.Exponents (({d} : Finset ℕ).filter Nat.Prime)
    (fun l => if l.Prime ∧ l = d then 1 else 0) (Real.log d) := by
  refine ⟨fun l hl => (Finset.mem_filter.1 hl).2, fun l => by dsimp only; split_ifs <;> norm_num, fun l hl => ?_, ?_⟩
  · exact if_neg fun h => hl (Finset.mem_filter.2 ⟨Finset.mem_singleton.2 h.2, h.1⟩)
  · rw [Finset.filter_singleton]
    split_ifs with h
    · simp [h]
    · simpa using Real.log_natCast_nonneg d

private theorem expLog {y c : ℝ} (hy : 0 ≤ y) (hc : 0 ≤ c) (hyc : Real.log y ≤ c) :
    GlobalTheory.NormSum.Exponents ((Finset.range (⌊y⌋₊ + 1)).filter Nat.Prime)
    (fun l => if l.Prime ∧ (l : ℝ) ≤ y then Real.logb l y else 0) (y * c) := by
  have hm : ∀ l : ℕ, l ∈ (Finset.range (⌊y⌋₊ + 1)).filter Nat.Prime ↔ l.Prime ∧ (l : ℝ) ≤ y := fun l => by
    rw [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff, Nat.le_floor_iff hy, and_comm]
  refine ⟨fun l hl => (Finset.mem_filter.1 hl).2, fun l => ?_, fun l hl => if_neg fun h => hl ((hm l).2 h), ?_⟩
  · dsimp only
    split_ifs with h
    · exact Real.logb_nonneg (by exact_mod_cast h.1.one_lt) (le_trans (by exact_mod_cast h.1.one_lt.le) h.2)
    · exact le_rfl
  · dsimp only
    rw [Finset.sum_congr (g := fun l : ℕ => Real.logb l y * Real.log l) rfl fun l hl => by rw [if_pos ((hm l).1 hl)]]
    rcases le_or_gt 1 y with h | h
    · exact (UpperTheory.WildA.logSum y h).trans (mul_le_mul_of_nonneg_left hyc hy)
    · rw [Nat.floor_eq_zero.2 h]
      have e : (Finset.range (0 + 1)).filter Nat.Prime = ∅ := by decide
      rw [e, Finset.sum_empty]
      exact mul_nonneg hy hc

theorem UpperTheory.WildA.lossOne :
    ∀ C1 : ℝ, 0 < C1 → ∃ C0 : ℝ, 0 < C0 ∧ ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (large₂ : SizeData₂ D), GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂ → HostHyp D → sc.cGap = 1 →
      ∀ (S : Finset ℕ) (δ : ℕ → ℝ), GlobalTheory.NormSum.Letters D S δ → ∃ (S' : Finset ℕ) (h : ℕ → ℝ),
        GlobalTheory.NormSum.Exponents S' h (C0 * D.R.f * (bigN D : ℝ) ^ 2 * (Real.log large₂.sc.b + sig G) * large₂.sc.b) ∧
        ∀ p : GlobalTheory.ChiGrid.Pair T, DefPair D.R.m p → ∀ l : ℕ, l.Prime →
          C1 * GlobalTheory.SumSize.TopInt.kerLoss G δ C1 large₂.sc.b p.small p.big l (depL G l) ≤ h l := by
  intro C1 hC1
  refine ⟨C1 * (26 + C1 * (|Real.log C1| + 1)), by positivity, ?_⟩
  intro D T L sc G large₂ hS hH hc S δ hδ
  obtain ⟨-, -, hN, hf, hm, -, hrd, h12⟩ := GlobalTheory.SizesOfRows.sizes_of_sizeRows large₂ hS
  have hNR : (1 : ℝ) ≤ bigN D := by exact_mod_cast hN
  have hfR : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf
  have hmR : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm
  have hb0 : 0 < large₂.sc.b := by linarith
  have hL : 1 ≤ Real.log large₂.sc.b := by
    rw [Real.le_log_iff_exp_le hb0]
    linarith [Real.exp_one_lt_d9]
  have hd : Real.log D.host.d ≤ Real.log large₂.sc.b := by
    have hb := hS.2.2.2.2.2.1
    have hk : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
    have hN1 : 1 ≤ D.R.N D.R.m := by simp only [Formalism.BasicNotions.Ranks.N]; omega
    have hN1R : (1 : ℝ) ≤ D.R.N D.R.m := by exact_mod_cast hN1
    have h1 : (1 : ℝ) ≤ (D.R.m : ℝ) * D.R.f * (D.R.N D.R.m : ℝ) ^ 2 :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by linarith) hfR) (one_le_pow₀ hN1R)
    have h2 : (D.host.d : ℝ) ≤ large₂.sc.b := (le_mul_of_one_le_left (Nat.cast_nonneg _) h1).trans hb
    rcases Nat.eq_zero_or_pos D.host.d with h | h
    · rw [h, Nat.cast_zero, Real.log_zero]
      linarith
    · exact Real.log_le_log (by exact_mod_cast h) h2
  have hsig : 0 ≤ sig G := Finset.sum_nonneg fun v _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
  have hy : Real.log (C1 * large₂.sc.b) ≤ (|Real.log C1| + 1) * Real.log large₂.sc.b := by
    rw [Real.log_mul hC1.ne' hb0.ne']
    nlinarith [le_abs_self (Real.log C1), abs_nonneg (Real.log C1)]
  obtain ⟨S2, h2⟩ := UpperTheory.WildA.depSum (G := G)
  have h0 : GlobalTheory.NormSum.Exponents S δ (Real.log D.host.rdE) := ⟨hδ.1, hδ.2.1, hδ.2.2.1, hδ.2.2.2.1⟩
  have h3 := expLog (y := C1 * large₂.sc.b) (by positivity) (by positivity) hy
  have h4 := expMul hC1.le (expAdd
    (expMul (c := 13 * D.R.f * bigN D * large₂.sc.b) (by positivity) (expAdd (expAdd h0 (expOne D.host.d)) h2))
    (expMul (c := (D.R.f : ℝ) * (bigN D : ℝ) ^ 2) (by positivity) h3))
  refine ⟨_, _, expMono h4 ?_, fun p hp l hl => ?_⟩
  · set Lb := Real.log large₂.sc.b
    set K := |Real.log C1| + 1 with hK
    have hK0 : 0 ≤ K := by positivity
    have e1 : (13 * D.R.f * bigN D * large₂.sc.b : ℝ) * (Real.log D.host.rdE + Real.log D.host.d + sig G) ≤
        (13 * D.R.f * (bigN D : ℝ) ^ 2 * large₂.sc.b) * (2 * (Lb + sig G)) := by
      refine (mul_le_mul_of_nonneg_left (b := _) (c := 2 * (Lb + sig G)) (by linarith) (by positivity)).trans ?_
      have : (bigN D : ℝ) ≤ (bigN D : ℝ) ^ 2 := by nlinarith
      gcongr
    have e2 : (D.R.f : ℝ) * (bigN D : ℝ) ^ 2 * (C1 * large₂.sc.b * (K * Lb)) ≤
        (D.R.f : ℝ) * (bigN D : ℝ) ^ 2 * (C1 * large₂.sc.b * (K * (Lb + sig G))) := by
      gcongr
      linarith
    refine (mul_le_mul_of_nonneg_left (add_le_add e1 e2) hC1.le).trans (le_of_eq ?_)
    ring
  · refine mul_le_mul_of_nonneg_left ?_ hC1.le
    unfold GlobalTheory.SumSize.TopInt.kerLoss
    simp only [hl, true_and, if_true]
    refine add_le_add (mul_le_mul_of_nonneg_right (UpperTheory.WildA.kerLe (G := G) large₂ hS hH hc p hp) ?_) le_rfl
    have := hδ.2.1 l
    split_ifs <;> positivity
