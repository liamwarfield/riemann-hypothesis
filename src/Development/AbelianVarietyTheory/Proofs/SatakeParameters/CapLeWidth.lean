module

public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RhoThreeOfOfDeterminantCharacterFiniteOrderType
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ScalePolynomialQuantitiesComparison
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XLeA

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NuRowNonnegLeTenMul
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField IsDedekindDomain

namespace GlobalTheory

theorem nuRow_zero_le (D : D7) (u : D.what₂.Word) (j : ℕ) (τ : D.what₂.Tau) (hk : 0 < D.R.k) :
    nuRow D u j τ 0 ≤ ((((D.hcW u τ).u ⟨0, hk⟩ : ℚ)) : ℝ) + wSz D j τ := by
  unfold nuRow srcPar
  rw [dite_eq_left hk]
  have h1 : 1 ≤ D.R.N j := by unfold Ranks.N; omega
  have h1' : (1 : ℝ) ≤ D.R.N j := by exact_mod_cast h1
  have h2 : (0 : ℝ) ≤ D.R.N (j - 1) := Nat.cast_nonneg _
  push_cast
  linarith

theorem nuRow_nonneg_le_ten_mul : ∀ (eps : ℝ) (Fm : FamP eps), (∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ∀ u, ∀ j ∈ SizeData₂.lifts (Fm.D x i), ∀ τ, ∀ l < (Fm.D x i).R.N (j - 1), 0 ≤ nuRow (Fm.D x i) u j τ l ∧ nuRow (Fm.D x i) u j τ l ≤ 10 * x * (Fm.L x i).sc.b) := by
  intro eps Fm
  obtain ⟨x0, h⟩ := GlobalTheory.HCEntries.entries eps Fm
  refine ⟨x0, fun x hx hx1 i u j hj τ l hl => ?_⟩
  obtain ⟨hw, hu, -⟩ := h x hx hx1 i
  obtain ⟨-, hw3, hwe⟩ := hw j hj τ
  have hj' := Finset.mem_Icc.1 hj
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hl' : l < (Fm.D x i).R.N j' := by simpa using hl
  have hjm : j' < (Fm.D x i).R.m := by omega
  have hk : 0 < (Fm.D x i).R.k := by have := (Fm.D x i).R.m_add_three_le_k; omega
  refine ⟨(RowWeightLemmas.nuRow_pos _ u j' hjm τ l hl').le, ?_⟩
  have h1 := RowWeightLemmas.nuRow_anti' _ u j' hjm τ l 0 (Nat.zero_le _) hl'
  have h2 := nuRow_zero_le (Fm.D x i) u (j' + 1) τ hk
  have h3 := (abs_le.1 (hu u τ ⟨0, hk⟩)).2
  have hb : 0 < (Fm.L x i).sc.b := Real.exp_pos _
  have hx' : 1 < x := Fm.one_lt_family_threshold.trans hx1
  have h4 : (Fm.L x i).sc.b ≤ x * (Fm.L x i).sc.b := le_mul_of_one_le_left hb.le hx'.le
  nlinarith

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.YoungDiagramCardEqSumRowLenRange
open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory

theorem youngDiagram_card_eq_sum_rowLen_range (μ : YoungDiagram) (n : ℕ) (h : μ.colLen 0 ≤ n) :
    μ.card = ∑ r ∈ Finset.range n, μ.rowLen r := by
  have hmap : ∀ c ∈ μ.cells, c.1 ∈ Finset.range n := by
    intro c hc
    rw [Finset.mem_range]
    have h1 : (c.1, c.2) ∈ μ := hc
    have h2 : (c.1, 0) ∈ μ := μ.up_left_mem le_rfl (Nat.zero_le _) h1
    exact lt_of_lt_of_le (YoungDiagram.mem_iff_lt_colLen.1 h2) h
  unfold YoungDiagram.card
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (fun c hc => hmap c hc)]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [YoungDiagram.rowLen_eq_card]
  rfl

theorem nuD_card_eq_sum_nuRow : ∀ (D : D7), NuRowOK D → ∀ (u : D.what₂.Word), ∀ j < D.R.m, ∀ (z : Bool × HH D), (((nuD D u j z).card : ℕ) : ℝ) = ∑ r ∈ Finset.range (D.R.N j), DV.nuRow D u (j + 1) (tauPl D z) r := by
  intro D hD u j hj z
  rw [youngDiagram_card_eq_sum_rowLen_range _ _ (nuD_rows D u j z), Nat.cast_sum]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [hD u j hj z r, if_pos (Finset.mem_range.1 hr)]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotMemTopPlaces
open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory.LongRows

theorem not_mem_topPlaces (D : D7) (z : Bool × HH D) (h : ¬ IsTopPl D z) :
    (D.eTau (tauPl D z) : D.R.GG) ∉ D.host.topPlaces := by
  intro hm
  unfold Host.topPlaces at hm
  obtain ⟨t, ht, hte⟩ := Finset.mem_image.1 hm
  unfold tauPl at hte
  rw [Equiv.apply_symm_apply] at hte
  obtain ⟨b, s⟩ := z
  cases b with
  | true =>
    have h1 := congrArg (fun g : D.R.GG => g.1.1) hte
    simp [plGG, Formalism.HC.Frame.tau1, Formalism.HC.Frame.tau2] at h1
  | false =>
    have h1 := congrArg (fun g : D.R.GG => g.2) hte
    simp only [plGG, Formalism.HC.Frame.tau1, Bool.false_eq_true, if_false] at h1
    have := D.R.toFrame.iota_bijective.1 h1
    subst this
    exact h ⟨rfl, ht⟩

theorem row_bounds (D : D7) (u : D.what₂.Word) (j : ℕ) (hj : j < D.R.m) (z : Bool × HH D) (r : ℕ) (hr : r < D.R.k) :
    wPl D (j + 1) z + (((D.hcW u (tauPl D z)).u ⟨r, hr⟩ : ℚ) : ℝ) - D.R.N D.R.m < DV.nuRow D u (j + 1) (tauPl D z) r ∧
    DV.nuRow D u (j + 1) (tauPl D z) r < wPl D (j + 1) z + (((D.hcW u (tauPl D z)).u ⟨r, hr⟩ : ℚ) : ℝ) := by
  have hw : wPl D (j + 1) z = (((D.hcW u (tauPl D z)).e ⟨j, hj⟩ : ℚ) : ℝ) := by
    unfold wPl wj
    rw [dite_eq_left (by simpa using hj), D.hcW_e]
    rfl
  have h1 : D.R.N j + (D.R.t + 1) ≤ D.R.N D.R.m := by
    unfold Ranks.N
    have : (j + 1) * (D.R.t + 1) ≤ D.R.m * (D.R.t + 1) := Nat.mul_le_mul_right _ hj
    rw [Nat.add_mul] at this
    omega
  have h2 : r < D.R.N j := by unfold Ranks.N; omega
  have h1' : (D.R.N j : ℝ) + (D.R.t + 1) ≤ D.R.N D.R.m := by exact_mod_cast h1
  have h2' : (r : ℝ) < D.R.N j := by exact_mod_cast h2
  have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  rw [RowWeightLemmas.nuRow_head D u j hj _ r hr, hw]
  push_cast
  constructor <;> linarith

theorem u_bounds_off {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) (u : D.what₂.Word) (τ : D.what₂.Tau)
    (hτ : (D.eTau τ : D.R.GG) ∉ D.host.topPlaces) (r : ℕ) (hr : r < D.R.k) :
    -(1 / 2 : ℝ) ≤ (((D.hcW u τ).u ⟨r, hr⟩ : ℚ) : ℝ) ∧
      (((D.hcW u τ).u ⟨r, hr⟩ : ℚ) : ℝ) ≤ if r = 0 then 3 * L.Sc else L.Sc := by
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  by_cases h0 : r = 0
  · subst h0
    rw [if_pos rfl, D.hcW_first u τ hr]
    have h1 := P.cloud_place_bound τ (by omega) hτ
    have h2 := L.cloud_v τ ⟨0, by omega⟩
    have h3 : (((D.hc τ).v ⟨0, by omega⟩ : ℚ) : ℝ) < (((D.hc τ).u ⟨0, hr⟩ : ℚ) : ℝ) := by
      exact_mod_cast (D.hc τ).u_gt_v ⟨0, by omega⟩
    push_cast at h1
    constructor <;> linarith [h2.1, h2.2]
  · rw [if_neg h0]
    by_cases hl : r + 1 < D.R.k
    · have := L.cloud_u u τ ⟨r, hr⟩ (by show 1 ≤ r; omega) hl
      constructor <;> linarith [this.1, this.2]
    · obtain rfl : r = D.R.k - 1 := by omega
      rw [D.hcW_last u τ (by omega), P.uk_extreme τ (by omega) hτ]
      have h2 := L.cloud_v τ ⟨D.R.k - 2, by omega⟩
      push_cast
      constructor <;> linarith [h2.1, h2.2]

theorem longRows : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ∀ (u : (Fm.D x i).what₂.Word), ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), ∀ r < (Fm.D x i).R.k, (¬ IsTopPl (Fm.D x i) z → wPl (Fm.D x i) (j + 1) z - (Fm.D x i).R.N (Fm.D x i).R.m - 1 / 2 < DV.nuRow (Fm.D x i) u (j + 1) (tauPl (Fm.D x i) z) r ∧ DV.nuRow (Fm.D x i) u (j + 1) (tauPl (Fm.D x i) z) r < wPl (Fm.D x i) (j + 1) z + (if r = 0 then 3 * (Fm.L x i).Sc else (Fm.L x i).Sc)) ∧ (IsTopPl (Fm.D x i) z → 1 ≤ r → r + 1 < (Fm.D x i).R.k → wPl (Fm.D x i) (j + 1) z - (Fm.D x i).R.N (Fm.D x i).R.m < DV.nuRow (Fm.D x i) u (j + 1) (tauPl (Fm.D x i) z) r ∧ DV.nuRow (Fm.D x i) u (j + 1) (tauPl (Fm.D x i) z) r < wPl (Fm.D x i) (j + 1) z + (Fm.L x i).Sc) := by
  intro eps Fm
  refine ⟨0, fun x _ hx i u j hj z r hr => ?_⟩
  obtain ⟨h1, h2⟩ := row_bounds (Fm.D x i) u j hj z r hr
  refine ⟨fun hz => ?_, fun _ hr1 hr2 => ?_⟩
  · obtain ⟨h3, h4⟩ := u_bounds_off (Fm.params x hx i) u _ (not_mem_topPlaces _ z hz) r hr
    constructor <;> linarith
  · obtain ⟨h3, h4⟩ := (Fm.L x i).cloud_u u (tauPl (Fm.D x i) z) ⟨r, hr⟩ hr1 hr2
    constructor <;> linarith

end GlobalTheory.LongRows
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TopRowsParams
open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory.TopRows

theorem nuRow_tauPl_of_isTopPl {D : D7} (L : SizeData₂ D) (u : D.what₂.Word) (j : ℕ) (hj : j < D.R.m)
    (z : Bool × HH D) (hz : IsTopPl D z) :
    DV.nuRow D u (j + 1) (tauPl D z) 0 = (aL L z.2 : ℝ) + (wPl D (j + 1) z - kaJ D (j + 1)) ∧
    DV.nuRow D u (j + 1) (tauPl D z) (D.R.k - 1) = (wPl D (j + 1) z - kaJ D (j + 1)) - (bL L z.2 : ℝ) ∧
    0 ≤ DV.nuRow D u (j + 1) (tauPl D z) (D.R.k - 1) ∧
    DV.nuRow D u (j + 1) (tauPl D z) (D.R.k - 1) ≤ L.sc.b' / L.sc.x + L.etaSz := by
  obtain ⟨hz1, hz2⟩ := hz
  have hk : 0 < D.R.k := by have := D.R.m_add_three_le_k; omega
  have hτ : (D.eTau (tauPl D z) : D.R.GG) = D.R.tau1 (⟨z.2, hz2⟩ : D.host.TT) := by
    unfold tauPl
    rw [Equiv.apply_symm_apply]
    simp [plGG, hz1]
  obtain ⟨hu1, huk⟩ := L.top_u (tauPl D z) ⟨z.2, hz2⟩ hk hτ
  obtain ⟨-, hw⟩ := L.win_top (j + 1) (by omega) (by omega) (tauPl D z) ⟨z.2, hz2⟩ hτ
  have ha : aL L z.2 = L.aT ⟨z.2, hz2⟩ := by unfold aL; rw [dite_eq_left hz2]
  have hb : bL L z.2 = L.bT ⟨z.2, hz2⟩ := by unfold bL; rw [dite_eq_left hz2]
  have hwe : wPl D (j + 1) z = (((D.hcW u (tauPl D z)).e ⟨j, hj⟩ : ℚ) : ℝ) := by
    unfold wPl wj
    rw [dite_eq_left (by simpa using hj), D.hcW_e]
    rfl
  have hkc : ((D.R.k - 1 : ℕ) : ℝ) = (D.R.k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have e1 : DV.nuRow D u (j + 1) (tauPl D z) 0 = (aL L z.2 : ℝ) + (wPl D (j + 1) z - kaJ D (j + 1)) := by
    rw [RowWeightLemmas.nuRow_head D u j hj _ 0 hk, D.hcW_first u _ hk, ha, hwe]
    unfold kaJ Ranks.N
    push_cast
    rw [hu1]
    ring
  have e2 : DV.nuRow D u (j + 1) (tauPl D z) (D.R.k - 1) =
      (wPl D (j + 1) z - kaJ D (j + 1)) - (bL L z.2 : ℝ) := by
    rw [RowWeightLemmas.nuRow_head D u j hj _ (D.R.k - 1) (by omega), D.hcW_last u _ hk, hb, hwe]
    unfold kaJ Ranks.N
    push_cast
    rw [huk, hkc]
    ring
  refine ⟨e1, e2, (RowWeightLemmas.nuRow_pos D u j hj _ _ (by unfold Ranks.N; omega)).le, ?_⟩
  have hka : 0 ≤ kaJ D (j + 1) := by
    unfold kaJ
    push_cast
    have : (0 : ℝ) ≤ (2 * ((j : ℝ) + 1) - 1) := by have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith
    positivity
  rw [e2, hb]
  change wPl D (j + 1) z ≤ _ at hw
  linarith

theorem eta_le {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) : L.etaSz ≤ L.sc.b' / L.sc.x := by
  have hx : 0 < L.sc.x := lt_trans one_pos L.sc.one_lt_alt
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hb' : 0 < L.sc.b' := div_pos (mul_pos hx hb) (Real.exp_pos _)
  have hn1 : (1 : ℝ) ≤ D.R.n := by
    have : 1 ≤ D.R.n := D.R.ord_pos
    exact_mod_cast this
  have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have h1 : L.etaSz ≤ (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz :=
    le_mul_of_one_le_left L.etaSz_pos.le (by nlinarith)
  have h2 : L.sc.w'' D.R.n ≤ L.sc.b' / L.sc.x := by
    unfold Scale.w''
    exact div_le_div_of_nonneg_left hb'.le hx (le_mul_of_one_le_right hx.le hn1)
  exact h1.trans (P.mteta.trans h2)

theorem top_rows : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ∀ (u : (Fm.D x i).what₂.Word), ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), IsTopPl (Fm.D x i) z → DV.nuRow (Fm.D x i) u (j + 1) (tauPl (Fm.D x i) z) 0 = (aL (Fm.L x i) z.2 : ℝ) + (wPl (Fm.D x i) (j + 1) z - kaJ (Fm.D x i) (j + 1)) ∧ DV.nuRow (Fm.D x i) u (j + 1) (tauPl (Fm.D x i) z) ((Fm.D x i).R.k - 1) = (wPl (Fm.D x i) (j + 1) z - kaJ (Fm.D x i) (j + 1)) - (bL (Fm.L x i) z.2 : ℝ) ∧ 0 ≤ DV.nuRow (Fm.D x i) u (j + 1) (tauPl (Fm.D x i) z) ((Fm.D x i).R.k - 1) ∧ DV.nuRow (Fm.D x i) u (j + 1) (tauPl (Fm.D x i) z) ((Fm.D x i).R.k - 1) ≤ 2 * (Fm.L x i).sc.b' / (Fm.L x i).sc.x := by
  intro eps Fm
  refine ⟨0, fun x _ hx1 i u j hj z hz => ?_⟩
  have h4 := eta_le (Fm.params x hx1 i)
  obtain ⟨e1, e2, e3, e4⟩ := nuRow_tauPl_of_isTopPl (Fm.L x i) u j hj z hz
  refine ⟨e1, e2, e3, e4.trans ?_⟩
  rw [mul_div_assoc]
  linarith

end GlobalTheory.TopRows
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlockRowsMemIcc
open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory

theorem blockRows_mem_Icc : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ∀ (u : (Fm.D x i).what₂.Word), ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), ∀ r, (Fm.D x i).R.k ≤ r → r < (Fm.D x i).R.N j → 0 ≤ DV.nuRow (Fm.D x i) u (j + 1) (tauPl (Fm.D x i) z) r ∧ DV.nuRow (Fm.D x i) u (j + 1) (tauPl (Fm.D x i) z) r ≤ (Fm.L x i).etaSz := by
  intro eps Fm
  refine ⟨0, fun x _ _ i u j hj z r hk hr => ⟨(RowWeightLemmas.nuRow_pos _ u j hj _ r hr).le, ?_⟩⟩
  obtain ⟨q, s, hq, hs, rfl⟩ := RowWeightLemmas.block_decomp _ j r hk hr
  rw [RowWeightLemmas.nuRow_block _ u j hj _ q s hq hs, (Fm.D x i).hcW_e u]
  have h1 := (Fm.L x i).be_close (tauPl (Fm.D x i) z) ⟨q, by omega⟩ ⟨j, hj⟩
  have h2 := ((Fm.D x i).hc (tauPl (Fm.D x i) z)).gap_be ⟨q, by omega⟩
  have h3 : (0 : ℚ) ≤ ((j : ℚ) - q) * (((Fm.D x i).R.t : ℚ) + 1) := by
    have : (q : ℚ) ≤ j := by exact_mod_cast hq.le
    exact mul_nonneg (by linarith) (by positivity)
  have h4 : (0 : ℚ) ≤ (((Fm.D x i).R.t : ℚ) + 3) / 2 := by positivity
  refine le_trans ?_ h1
  refine le_trans ?_ (neg_le_abs _)
  rw [← Rat.cast_neg]
  exact Rat.cast_le.2 (by linarith)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NuDCardLeASq
open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory

theorem nuD_card_le_a_sq : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ∀ (u : (Fm.D x i).what₂.Word), ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), (((nuD (Fm.D x i) u j z).card : ℕ) : ℝ) ≤ (Fm.L x i).sc.a ^ 2 := by
  intro eps Fm
  obtain ⟨x1, h1⟩ := GlobalTheory.nuRow_nonneg_le_ten_mul eps Fm
  obtain ⟨x2, h2⟩ := GlobalTheory.ShNums.size_rel Fm
  refine ⟨max x1 x2, fun x hx hx1 i u j hj z => ?_⟩
  have hr := h1 x (le_trans (le_max_left _ _) hx) hx1 i u (j + 1)
    (Finset.mem_Icc.2 ⟨by omega, by omega⟩) (tauPl (Fm.D x i) z)
  simp only [Nat.add_sub_cancel] at hr
  obtain ⟨hkN, -, -, -, -, h4, -, -, -, hS⟩ := h2 x (le_trans (le_max_right _ _) hx) hx1 i
  have hsx := Fm.L_x x i hx1
  rw [GlobalTheory.nuD_card_eq_sum_nuRow _ (nuRowOK _) u j hj z]
  have hsum := Finset.sum_le_card_nsmul (Finset.range ((Fm.D x i).R.N j))
    (fun r => DV.nuRow (Fm.D x i) u (j + 1) (tauPl (Fm.D x i) z) r) (10 * x * (Fm.L x i).sc.b)
    (fun r hr' => (hr r (Finset.mem_range.1 hr')).2)
  rw [Finset.card_range, nsmul_eq_mul] at hsum
  have hNle : ((Fm.D x i).R.N j : ℝ) ≤ (Fm.D x i).R.N (Fm.D x i).R.m := by
    have : (Fm.D x i).R.N j ≤ (Fm.D x i).R.N (Fm.D x i).R.m := by
      unfold Ranks.N
      have := Nat.mul_le_mul_right ((Fm.D x i).R.t + 1) hj.le
      omega
    exact_mod_cast this
  have hk : (1 : ℝ) ≤ (Fm.D x i).R.k := by
    have := (Fm.D x i).R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ (Fm.D x i).R.k)
  have hN0 : (0 : ℝ) ≤ (Fm.D x i).R.N (Fm.D x i).R.m := Nat.cast_nonneg _
  have hNk := le_mul_of_one_le_left hN0 hk
  have heta := (Fm.L x i).etaSz_pos
  have hb : 0 < (Fm.L x i).sc.b := Real.exp_pos _
  have hN : ((Fm.D x i).R.N j : ℝ) ≤ (Fm.L x i).sc.b / 10 := by linarith
  rw [hsx] at h4
  have hxb : 0 ≤ 10 * x * (Fm.L x i).sc.b := by positivity
  have h5 := mul_le_mul_of_nonneg_right hN hxb
  have ha : (Fm.L x i).sc.a = x * (Fm.L x i).sc.b := by
    unfold Scale.a
    rw [hsx]
  rw [ha]
  have h6 : x * (Fm.L x i).sc.b ^ 2 ≤ x * (x * (Fm.L x i).sc.b ^ 2) :=
    le_mul_of_one_le_left (by positivity) (by linarith)
  nlinarith

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExcessMemIcc
open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory.ExcessLow

theorem excess_sum (f : ℕ → ℝ) (k M : ℕ) (w N S η W : ℝ) (hk : 2 ≤ k) (hN1 : 1 ≤ N) (hS : 0 ≤ S)
    (hlong : ∀ r < k, w - N - 1 / 2 < f r ∧ f r < w + (if r = 0 then 3 * S else S))
    (hblock : ∀ r, k ≤ r → r < k + M → 0 ≤ f r ∧ f r ≤ η)
    (hkN : (k : ℝ) * N ≤ S / 4) (hkS : (k : ℝ) * S ≤ W) (hM : (M : ℝ) * η ≤ W) (hW : W ≤ w) :
    0 ≤ ∑ r ∈ Finset.range (k + M), f r - ((k : ℝ) - 1) * w ∧
      ∑ r ∈ Finset.range (k + M), f r - ((k : ℝ) - 1) * w ≤ 4 * w := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  rw [Finset.sum_range_add]
  have b0 : 0 ≤ ∑ r ∈ Finset.range M, f (k + r) :=
    Finset.sum_nonneg fun r hr =>
      (hblock _ (by omega) (by have := Finset.mem_range.1 hr; omega)).1
  have b1 : ∑ r ∈ Finset.range M, f (k + r) ≤ M * η := by
    have := Finset.sum_le_card_nsmul (Finset.range M) (fun r => f (k + r)) η fun r hr =>
      (hblock _ (by omega) (by have := Finset.mem_range.1 hr; omega)).2
    simpa using this
  have l0 : (k : ℝ) * (w - N - 1 / 2) ≤ ∑ r ∈ Finset.range k, f r := by
    have := Finset.card_nsmul_le_sum (Finset.range k) f (w - N - 1 / 2) fun r hr =>
      (hlong r (Finset.mem_range.1 hr)).1.le
    simpa only [Finset.card_range, nsmul_eq_mul] using this
  have l1 : ∑ r ∈ Finset.range k, f r ≤ k * (w + S) + 2 * S := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [Finset.sum_range_succ']
    have h0 := (hlong 0 (by omega)).2
    rw [if_pos rfl] at h0
    have h1 := Finset.sum_le_card_nsmul (Finset.range k') (fun r => f (r + 1)) (w + S) fun r hr => by
      have := (hlong (r + 1) (by have := Finset.mem_range.1 hr; omega)).2
      rw [if_neg (by omega)] at this
      exact this.le
    simp only [Finset.card_range, nsmul_eq_mul] at h1
    push_cast
    nlinarith
  have h2S : 2 * S ≤ k * S := mul_le_mul_of_nonneg_right hk' hS
  have hkN1 : (k : ℝ) ≤ k * N := le_mul_of_one_le_right (by linarith) hN1
  constructor
  · nlinarith
  · nlinarith

theorem excess_mem_Icc : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ∀ (u : (Fm.D x i).what₂.Word), ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), ¬ IsTopPl (Fm.D x i) z → 0 ≤ (((nuD (Fm.D x i) u j z).card : ℕ) : ℝ) - (((Fm.D x i).R.k : ℝ) - 1) * wPl (Fm.D x i) (j + 1) z ∧ (((nuD (Fm.D x i) u j z).card : ℕ) : ℝ) - (((Fm.D x i).R.k : ℝ) - 1) * wPl (Fm.D x i) (j + 1) z ≤ 4 * wPl (Fm.D x i) (j + 1) z := by
  intro eps Fm
  obtain ⟨x1, h1⟩ := GlobalTheory.ShNums.size_rel Fm
  obtain ⟨x2, h2⟩ := GlobalTheory.Ggeo.wPl_windows Fm
  obtain ⟨x3, h3⟩ := GlobalTheory.LongRows.longRows Fm
  obtain ⟨x4, h4⟩ := GlobalTheory.blockRows_mem_Icc Fm
  refine ⟨max (max x1 x2) (max x3 x4), fun x hx hx1 i u j hj z hz => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hx
  obtain ⟨⟨e1, e2⟩, e3, e4⟩ := hx
  obtain ⟨a1, a2, a3, -⟩ := h1 x e1 hx1 i
  have hk := (Fm.D x i).R.m_add_three_le_k
  rw [GlobalTheory.nuD_card_eq_sum_nuRow (Fm.D x i) (nuRowOK _) u j hj z]
  have heta := (Fm.L x i).etaSz_pos
  refine excess_sum _ (Fm.D x i).R.k (j * ((Fm.D x i).R.t + 1)) _
    ((Fm.D x i).R.N (Fm.D x i).R.m) (Fm.L x i).Sc (Fm.L x i).etaSz
    ((Fm.L x i).sc.w'' (Fm.D x i).R.n) (by omega) ?_ (Fm.L x i).Sc_pos.le
    (fun r hr => (h3 x e3 hx1 i u j hj z r hr).1 hz)
    (fun r hr hr' => h4 x e4 hx1 i u j hj z r hr hr') a1 a2 ?_ (h2 x e2 hx1 i j hj z).1
  · have : 1 ≤ (Fm.D x i).R.N (Fm.D x i).R.m := by
      unfold Ranks.N
      omega
    exact_mod_cast this
  · refine le_trans ?_ a3
    apply mul_le_mul_of_nonneg_right _ heta.le
    push_cast
    have : (j : ℝ) ≤ (Fm.D x i).R.m := by exact_mod_cast hj.le
    exact mul_le_mul_of_nonneg_right this (by positivity)

end GlobalTheory.ExcessLow
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SumRangeSplit
open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory.TopExcess

theorem sum_range_split (f : ℕ → ℝ) (k M : ℕ) (hk : 2 ≤ k) :
    ∑ r ∈ Finset.range (k + M), f r =
      f 0 + ∑ r ∈ Finset.Ico 1 (k - 1), f r + f (k - 1) + ∑ r ∈ Finset.Ico k (k + M), f r := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel, ← Finset.sum_range_add_sum_Ico f (Nat.le_add_right (n + 1) M), Finset.sum_range_succ,
    ← Finset.sum_range_add_sum_Ico f (by omega : 1 ≤ n), Finset.sum_range_one]

theorem sum_Ico_bounds (f : ℕ → ℝ) (a b : ℕ) (lo hi : ℝ) (h : ∀ r, a ≤ r → r < b → lo ≤ f r ∧ f r ≤ hi) :
    ((b - a : ℕ) : ℝ) * lo ≤ ∑ r ∈ Finset.Ico a b, f r ∧ ∑ r ∈ Finset.Ico a b, f r ≤ ((b - a : ℕ) : ℝ) * hi := by
  constructor
  · have := Finset.card_nsmul_le_sum (Finset.Ico a b) f lo
      (fun r hr => (h r (Finset.mem_Ico.1 hr).1 (Finset.mem_Ico.1 hr).2).1)
    rwa [Nat.card_Ico, nsmul_eq_mul] at this
  · have := Finset.sum_le_card_nsmul (Finset.Ico a b) f hi
      (fun r hr => (h r (Finset.mem_Ico.1 hr).1 (Finset.mem_Ico.1 hr).2).2)
    rwa [Nat.card_Ico, nsmul_eq_mul] at this

theorem top_excess : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ∀ (u : (Fm.D x i).what₂.Word), ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), IsTopPl (Fm.D x i) z → 0 ≤ (((nuD (Fm.D x i) u j z).card : ℕ) : ℝ) - (((nuD (Fm.D x i) u j z).rowLen 0 : ℕ) : ℝ) - ((((Fm.D x i).R.k : ℝ) - 1) * wPl (Fm.D x i) (j + 1) z - 2 * wPl (Fm.D x i) (j + 1) z) ∧ (((nuD (Fm.D x i) u j z).card : ℕ) : ℝ) - (((nuD (Fm.D x i) u j z).rowLen 0 : ℕ) : ℝ) - ((((Fm.D x i).R.k : ℝ) - 1) * wPl (Fm.D x i) (j + 1) z - 2 * wPl (Fm.D x i) (j + 1) z) ≤ 4 * wPl (Fm.D x i) (j + 1) z := by
  intro eps Fm
  obtain ⟨x1, h1⟩ := GlobalTheory.ShNums.size_rel Fm
  obtain ⟨x2, h2⟩ := GlobalTheory.Ggeo.wPl_windows Fm
  obtain ⟨x3, h3⟩ := GlobalTheory.LongRows.longRows Fm
  obtain ⟨x4, h4⟩ := GlobalTheory.TopRows.top_rows Fm
  obtain ⟨x5, h5⟩ := GlobalTheory.blockRows_mem_Icc Fm
  refine ⟨max (max (max x1 x2) (max x3 x4)) x5, fun x hx hx1 i u j hj z hz => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hx
  obtain ⟨⟨⟨g1, g2⟩, g3, g4⟩, g5⟩ := hx
  obtain ⟨a1, a2, a3, -, a5, a6, -, -, a9, -⟩ := h1 x g1 hx1 i
  obtain ⟨b1, -, b3⟩ := h2 x g2 hx1 i j hj z
  obtain ⟨b3, -⟩ := b3 hz
  have c := h3 x g3 hx1 i u j hj z
  obtain ⟨-, -, d3, d4⟩ := h4 x g4 hx1 i u j hj z hz
  have e := h5 x g5 hx1 i u j hj z
  clear h1 h2 h3 h4 h5
  generalize Fm.L x i = L at *
  generalize Fm.D x i = D at *
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hN : D.R.N j = D.R.k + j * (D.R.t + 1) := by unfold Ranks.N; omega
  have hok := nuRowOK D
  rw [GlobalTheory.nuD_card_eq_sum_nuRow D hok u j hj z, hok u j hj z 0, if_pos (by omega), hN,
    sum_range_split _ _ _ (by omega)]
  obtain ⟨m1, m2⟩ := sum_Ico_bounds (DV.nuRow D u (j + 1) (tauPl D z)) 1 (D.R.k - 1) _ _
    (fun r hr1 hr2 => let h := (c r (by omega)).2 hz hr1 (by omega); ⟨h.1.le, h.2.le⟩)
  obtain ⟨n1, n2⟩ := sum_Ico_bounds (DV.nuRow D u (j + 1) (tauPl D z)) D.R.k (D.R.k + j * (D.R.t + 1)) _ _
    (fun r hr1 hr2 => e r hr1 (by omega))
  have hkc : ((D.R.k - 1 - 1 : ℕ) : ℝ) = (D.R.k : ℝ) - 2 := by
    rw [Nat.sub_sub, Nat.cast_sub (by omega)]; norm_num
  rw [hkc] at m1 m2
  rw [Nat.add_sub_cancel_left] at n1 n2
  push_cast at n1 n2
  have hS := L.Sc_pos
  have he := L.etaSz_pos
  have hk' : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hk
  have hj' : (j : ℝ) ≤ D.R.m := by exact_mod_cast hj.le
  have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hNm : (0 : ℝ) ≤ D.R.N D.R.m := Nat.cast_nonneg _
  have hx0 : 0 < L.sc.x := by linarith
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hb' : 0 < L.sc.b' := div_pos (mul_pos hx0 hb) (Real.exp_pos _)
  have hq : L.sc.b' / L.sc.x ≤ L.sc.b' / 4 := div_le_div_of_nonneg_left hb'.le (by norm_num) a6
  have hbl : (j : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz ≤ (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz := by gcongr
  have hS1 : L.Sc ≤ (D.R.k : ℝ) * L.Sc := le_mul_of_one_le_left hS.le (by linarith)
  rw [mul_div_assoc] at d4
  constructor <;> nlinarith

end GlobalTheory.TopExcess
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WPlPos
open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory.Ggeo

theorem wPl_pos : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), 0 < wPl (Fm.D x i) (j + 1) z := by
  intro eps Fm
  obtain ⟨x0, h0⟩ := GlobalTheory.ShNums.size_rel Fm
  obtain ⟨y0, h1⟩ := GlobalTheory.Ggeo.wPl_windows Fm
  refine ⟨max x0 y0, fun x hx hx1 i j hj z => ?_⟩
  obtain ⟨-, -, -, -, -, -, -, -, hw, -⟩ := h0 x (le_trans (le_max_left _ _) hx) hx1 i
  have h2 := (h1 x (le_trans (le_max_right _ _) hx) hx1 i j hj z).1
  linarith

end GlobalTheory.Ggeo
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwoWLeFirstRow
open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory.TopFirstRow

theorem two_w_le_first_row : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ∀ (u : (Fm.D x i).what₂.Word), ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), IsTopPl (Fm.D x i) z → 2 * wPl (Fm.D x i) (j + 1) z ≤ (((nuD (Fm.D x i) u j z).rowLen 0 : ℕ) : ℝ) := by
  intro eps Fm
  obtain ⟨x1, h1⟩ := GlobalTheory.ShNums.size_rel Fm
  obtain ⟨x2, h2⟩ := GlobalTheory.TopRows.top_rows Fm
  obtain ⟨x3, h3⟩ := GlobalTheory.Ggeo.wPl_windows Fm
  refine ⟨max x1 (max x2 x3), fun x hx hx1 i u j hj z hz => ?_⟩
  have hxa : x ≥ x1 := le_trans (le_max_left _ _) hx
  have hxb : x ≥ x2 := le_trans ((le_max_left _ _).trans (le_max_right _ _)) hx
  have hxc : x ≥ x3 := le_trans ((le_max_right _ _).trans (le_max_right _ _)) hx
  obtain ⟨-, -, -, -, -, h4, h2b, -, -, -⟩ := h1 x hxa hx1 i
  obtain ⟨e1, e2, e3, -⟩ := h2 x hxb hx1 i u j hj z hz
  obtain ⟨-, -, hw⟩ := h3 x hxc hx1 i j hj z
  obtain ⟨-, hw2⟩ := hw hz
  generalize Fm.L x i = L at *
  generalize Fm.D x i = D at *
  have hxp : 0 < L.sc.x := by linarith
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hb' : 0 < L.sc.b' := div_pos (mul_pos hxp hb) (Real.exp_pos _)
  have ha : aL L z.2 = L.aT ⟨z.2, hz.2⟩ := by unfold aL; rw [dite_eq_left hz.2]
  have hbb : bL L z.2 = L.bT ⟨z.2, hz.2⟩ := by unfold bL; rw [dite_eq_left hz.2]
  have a1 := (L.aT_win ⟨z.2, hz.2⟩).1
  have a2 := L.bT_ge ⟨z.2, hz.2⟩
  have a3 : 4 * L.sc.b ≤ L.sc.a := by
    unfold Scale.a
    exact mul_le_mul_of_nonneg_right h4 hb.le
  have hN : 0 < D.R.N j := by
    have := D.R.m_add_three_le_k
    unfold Ranks.N
    omega
  rw [nuRowOK D u j hj z 0, if_pos hN, e1]
  rw [e2, hbb] at e3
  rw [ha]
  linarith

end GlobalTheory.TopFirstRow
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CapLe
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NonemptyPlacesOfRecord
open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory

theorem nonempty_places_of_record (D : D7) : Nonempty D.what₂.places.Pl := by
  have h : Nonempty (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.what₂.LL)) := by
    obtain ⟨M, hM⟩ := Ideal.exists_maximal (NumberField.RingOfIntegers D.what₂.LL)
    exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM
      (NumberField.RingOfIntegers.not_isField _)⟩⟩
  exact h.map D.plEq.symm

theorem fill_eq_wPl : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x,
    ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)),
      fill (Fm.Gx x i) (bL (Fm.L x i)) (j + 1) z = wPl (Fm.D x i) (j + 1) z := by
  intro eps Fm
  refine ⟨0, fun x _ hx i j hj z => ?_⟩
  obtain ⟨w⟩ := nonempty_places_of_record (Fm.D x i)
  refine (Fm.fills x hx i w).1 (j + 1) ?_ (tauPl _ z) z ?_
  · simp only [SizeData₂.lifts, Finset.mem_Icc]; omega
  · simp [tauPl]

end GlobalTheory
end

open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory.CapBound

theorem row_le (D : D7) (u : D.what₂.Word) (j : ℕ) (hj : j < D.R.m) (z : Bool × HH D) (r : ℕ) (hr1 : r ≤ 1)
    (hr : r < D.R.k) :
    (((nuD D u j z).rowLen r : ℕ) : ℝ) ≤
      wPl D (j + 1) z - kaJ D (j + 1) + (((D.hcW u (tauPl D z)).u ⟨r, hr⟩ : ℚ) : ℝ) := by
  have hw : wPl D (j + 1) z = (((D.hcW u (tauPl D z)).e ⟨j, hj⟩ : ℚ) : ℝ) := by
    unfold wPl wj
    rw [dite_eq_left (by simpa using hj), D.hcW_e]
    rfl
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hk' : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hk
  have hr' : (r : ℝ) ≤ 1 := by exact_mod_cast hr1
  have h2 : r < D.R.N j := by unfold Ranks.N; omega
  rw [nuRowOK D u j hj z r, if_pos h2, RowWeightLemmas.nuRow_head D u j hj _ r hr, hw]
  unfold kaJ Ranks.N
  push_cast
  linarith

theorem cap_le : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ∀ (u : (Fm.D x i).what₂.Word), ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), (if IsTopPl (Fm.D x i) z then (((nuD (Fm.D x i) u j z).rowLen 1 : ℕ) : ℝ) else (((nuD (Fm.D x i) u j z).rowLen 0 : ℕ) : ℝ)) ≤ fillG (Fm.Gx x i) (bL (Fm.L x i)) (j + 1) z + cG (Fm.L x i) := by
  intro eps Fm
  obtain ⟨x0, hx0⟩ := GlobalTheory.fill_eq_wPl Fm
  refine ⟨x0, fun x hx hx1 i u j hj z => ?_⟩
  have hk : 5 ≤ (Fm.D x i).R.k := by
    have := (Fm.D x i).R.m_add_three_le_k; have := (Fm.D x i).R.two_le_m; omega
  have hS := (Fm.L x i).Sc_pos
  unfold fillG cG
  rw [hx0 x hx hx1 i j hj z]
  split_ifs with hz
  · have h1 := row_le (Fm.D x i) u j hj z 1 le_rfl (by omega)
    obtain ⟨-, h4⟩ := (Fm.L x i).cloud_u u (tauPl (Fm.D x i) z) ⟨1, by omega⟩ le_rfl (by show 1 + 1 < _; omega)
    linarith
  · have h1 := row_le (Fm.D x i) u j hj z 0 (by omega) (by omega)
    obtain ⟨-, h4⟩ := GlobalTheory.LongRows.u_bounds_off (Fm.params x hx1 i) u _
      (GlobalTheory.LongRows.not_mem_topPlaces _ z hz) 0 (by omega)
    rw [if_pos rfl] at h4
    linarith

end GlobalTheory.CapBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlLeParams
open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory.AlTop

theorem al_le_rowLen_sub {D : D7} (L : SizeData₂ D) (u : D.what₂.Word) (j : ℕ) (hj : j < D.R.m)
    (t : HH D) (ht : t ∈ D.host.TT) :
    al L (aL L) t ≤ (((nuD D u j (false, t)).rowLen 0 : ℕ) : ℝ) - (((nuD D u j (false, t)).rowLen 1 : ℕ) : ℝ) := by
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hN : D.R.k ≤ D.R.N j := by unfold Ranks.N; omega
  have hz : IsTopPl D (false, t) := ⟨rfl, ht⟩
  obtain ⟨e1, -⟩ := GlobalTheory.TopRows.nuRow_tauPl_of_isTopPl L u j hj (false, t) hz
  have hwe : wPl D (j + 1) (false, t) = (((D.hcW u (tauPl D (false, t))).e ⟨j, hj⟩ : ℚ) : ℝ) := by
    unfold wPl wj
    rw [dite_eq_left (by simpa using hj), D.hcW_e]
    rfl
  obtain ⟨-, h4⟩ := L.cloud_u u (tauPl D (false, t)) ⟨1, by omega⟩ le_rfl (by show 1 + 1 < D.R.k; omega)
  have hk' : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hk
  have hS := L.Sc_pos
  rw [nuRowOK D u j hj, nuRowOK D u j hj, if_pos (by omega), if_pos (by omega), e1,
    RowWeightLemmas.nuRow_head D u j hj _ 1 (by omega), hwe]
  unfold al cG kaJ Ranks.N
  push_cast
  linarith

theorem al_le : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ∀ (u : (Fm.D x i).what₂.Word), ∀ j < (Fm.D x i).R.m, ∀ t ∈ (Fm.D x i).host.TT, al (Fm.L x i) (aL (Fm.L x i)) t ≤ (((nuD (Fm.D x i) u j (false, t)).rowLen 0 : ℕ) : ℝ) - (((nuD (Fm.D x i) u j (false, t)).rowLen 1 : ℕ) : ℝ) :=
  fun Fm => ⟨0, fun x _ _ i u j hj t ht => al_le_rowLen_sub (Fm.L x i) u j hj t ht⟩

end GlobalTheory.AlTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RankTwoLogbFiveSqLe
open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory

theorem rank_two_logb_five_sq_le {eps : ℝ} (Fm : FamP eps) :
    ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x,
      2 * Real.logb 5 ((Fm.L x i).sc.a ^ 2) + 2 ≤ ((Fm.D x i).R.k : ℝ) - 1 := by
  refine ⟨3, fun x hx hx1 i => ?_⟩
  have hK := (Fm.sizes x hx1 i).2.2.1.1
  have hsx := Fm.L_x x i hx1
  have he := (Fm.L x i).sc.eps_pos
  have he' := (Fm.L x i).sc.eps_lt
  have hx3 : (3 : ℝ) ≤ x := hx
  have hx0 : (0 : ℝ) < x := by linarith
  rw [hsx] at hK
  have h4 : x ^ (4 : ℕ) ≤ ((Fm.D x i).R.k : ℝ) := by
    refine le_trans ?_ hK
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    unfold szTh
    push_cast
    linarith
  have hL : (Fm.L x i).sc.L ≤ x := by
    unfold Scale.L
    rw [hsx]
    calc x ^ (Fm.L x i).sc.eps ≤ x ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = x := Real.rpow_one x
  have hL0 : 0 ≤ (Fm.L x i).sc.L := by
    unfold Scale.L
    rw [hsx]
    positivity
  have hla : Real.log (Fm.L x i).sc.a = Real.log x + (Fm.L x i).sc.L := by
    unfold Scale.a Scale.b
    rw [hsx, Real.log_mul hx0.ne' (Real.exp_pos _).ne', Real.log_exp]
  have hlx : Real.log x ≤ x := (Real.log_le_sub_one_of_pos hx0).trans (by linarith)
  have hlx0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have h5 : 1 ≤ Real.log 5 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have := Real.exp_one_lt_d9
    linarith
  have hb : Real.logb 5 ((Fm.L x i).sc.a ^ 2) ≤ 4 * x := by
    rw [Real.logb, Real.log_pow, hla]
    push_cast
    refine (div_le_self (by linarith) h5).trans (by linarith)
  have h27 : 27 ≤ x ^ 3 := by
    calc (27 : ℝ) = 3 ^ 3 := by norm_num
      _ ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) hx3 3
  have : 27 * x ≤ x ^ 4 := by
    calc 27 * x ≤ x ^ 3 * x := mul_le_mul_of_nonneg_right h27 hx0.le
      _ = x ^ 4 := by ring
  linarith

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ScaleOneLtA
open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory

theorem scale_one_lt_a (s : Scale) : 1 < s.a := by
  have hx : 1 < s.x := s.one_lt_alt
  have hL : 0 ≤ s.L := by
    unfold Scale.L
    exact Real.rpow_nonneg (by linarith) _
  have hb : 1 ≤ s.b := by
    unfold Scale.b
    exact Real.one_le_exp hL
  unfold Scale.a
  nlinarith

theorem family_one_lt_scale_a : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x →
    ∀ i : Fm.Ix x, 1 < (Fm.L x i).sc.a :=
  fun Fm => ⟨0, fun x _ _ i => scale_one_lt_a (Fm.L x i).sc⟩

end GlobalTheory
end

open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory.ShapeRows

theorem ent_nu {D : D7} (E : OrbitPlaces.Ent D) (u : D.what₂.Word) (j : ℕ) (hj : j < D.R.m) (z : Bool × HH D) :
    E.nu u j z = nuD D u j z := by
  apply YoungDiagram.ext
  ext ⟨r, c⟩
  rw [YoungDiagram.mem_cells, YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen,
    YoungDiagram.mem_iff_lt_rowLen]
  have h : (E.nu u j z).rowLen r = (nuD D u j z).rowLen r := by
    have h1 := E.nu_row u j hj z r
    have h2 := nuRowOK D u j hj z r
    exact_mod_cast h1.trans h2.symm
  rw [h]

theorem ent_size {D : D7} (E : OrbitPlaces.Ent D) (u : D.what₂.Word) (j : ℕ) (hj : j < D.R.m) (z : Bool × HH D) :
    E.size u j z = (((nuD D u j z).card : ℕ) : ℝ) := by
  unfold OrbitPlaces.Ent.size
  rw [ent_nu E u j hj z]

theorem ent_row {D : D7} (E : OrbitPlaces.Ent D) (u : D.what₂.Word) (j : ℕ) (hj : j < D.R.m) (z : Bool × HH D) (r : ℕ) :
    E.row u j z r = (((nuD D u j z).rowLen r : ℕ) : ℝ) := by
  unfold OrbitPlaces.Ent.row
  rw [ent_nu E u j hj z]

theorem ent_cap {D : D7} (E : OrbitPlaces.Ent D) (u : D.what₂.Word) (j : ℕ) (hj : j < D.R.m) (z : Bool × HH D) :
    E.cap u j z = if IsTopPl D z then (((nuD D u j z).rowLen 1 : ℕ) : ℝ) else (((nuD D u j z).rowLen 0 : ℕ) : ℝ) := by
  unfold OrbitPlaces.Ent.cap
  rw [ent_row E u j hj z, ent_row E u j hj z]

theorem cap_le_width : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ∀ (u : (Fm.D x i).what₂.Word), ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), (if IsTopPl (Fm.D x i) z then (((nuD (Fm.D x i) u j z).rowLen 1 : ℕ) : ℝ) else (((nuD (Fm.D x i) u j z).rowLen 0 : ℕ) : ℝ)) ≤ (Fm.L x i).sc.b + (Fm.L x i).etaSz + 1 + 3 * (Fm.L x i).Sc := by
  intro eps Fm
  obtain ⟨x1, h1⟩ := GlobalTheory.Ggeo.wPl_windows Fm
  obtain ⟨x2, h2⟩ := GlobalTheory.LongRows.longRows Fm
  refine ⟨max x1 x2, fun x hx hx1 i u j hj z => ?_⟩
  obtain ⟨-, hw, -⟩ := h1 x (le_trans (le_max_left _ _) hx) hx1 i j hj z
  have hr := h2 x (le_trans (le_max_right _ _) hx) hx1 i u j hj z
  have hk : 5 ≤ (Fm.D x i).R.k := by
    have := (Fm.D x i).R.m_add_three_le_k
    have := (Fm.D x i).R.two_le_m
    omega
  have hN : (Fm.D x i).R.k ≤ (Fm.D x i).R.N j := by unfold Ranks.N; omega
  have hS := (Fm.L x i).Sc_pos
  split_ifs with hz
  · have e := nuRowOK (Fm.D x i) u j hj z 1
    rw [if_pos (by omega)] at e
    have := ((hr 1 (by omega)).2 hz le_rfl (by omega)).2
    rw [e]
    linarith
  · have e := nuRowOK (Fm.D x i) u j hj z 0
    rw [if_pos (by omega)] at e
    have := ((hr 0 (by omega)).1 hz).2
    rw [if_pos rfl] at this
    rw [e]
    linarith

theorem shape : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ (i : Fm.Ix x) (Ee : OrbitPlaces.Ent (Fm.D x i)), OrbitPlaces.Shape (Fm.D x i) (Fm.L x i) (Fm.Gx x i) Ee := by
  intro eps Fm
  obtain ⟨a1, h1⟩ := GlobalTheory.Ggeo.wPl_pos Fm
  obtain ⟨a2, h2⟩ := GlobalTheory.ExcessLow.excess_mem_Icc Fm
  obtain ⟨a3, h3⟩ := GlobalTheory.TopExcess.top_excess Fm
  obtain ⟨a4, h4⟩ := GlobalTheory.TopFirstRow.two_w_le_first_row Fm
  obtain ⟨a5, h5⟩ := GlobalTheory.nuD_card_le_a_sq Fm
  obtain ⟨a6, h6⟩ := GlobalTheory.rank_two_logb_five_sq_le Fm
  obtain ⟨a7, h7⟩ := GlobalTheory.ShXa.X''_le_a Fm
  obtain ⟨a8, h8⟩ := GlobalTheory.family_one_lt_scale_a Fm
  obtain ⟨a9, h9⟩ := cap_le_width Fm
  obtain ⟨a10, h10⟩ := GlobalTheory.AlTop.al_le Fm
  obtain ⟨a11, h11⟩ := GlobalTheory.CapBound.cap_le Fm
  refine ⟨max a1 (max a2 (max a3 (max a4 (max a5 (max a6 (max a7 (max a8 (max a9 (max a10 a11))))))))),
    fun x hx hx1 i Ee => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hx
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ := hx
  exact
    { wpos := h1 x b1 hx1 i
      low := fun u j hj z hz => by
        rw [ent_size Ee u j hj z]
        exact h2 x b2 hx1 i u j hj z hz
      top := fun u j hj z hz => by
        rw [ent_size Ee u j hj z, ent_row Ee u j hj z]
        exact h3 x b3 hx1 i u j hj z hz
      top1 := fun u j hj z hz => by
        rw [ent_row Ee u j hj z]
        exact h4 x b4 hx1 i u j hj z hz
      sizeA := fun u j hj z => by
        rw [ent_size Ee u j hj z]
        exact h5 x b5 hx1 i u j hj z
      rankA := h6 x b6 hx1 i
      xa := ⟨h7 x b7 hx1 i, h8 x b8 hx1 i⟩
      capW := fun u j hj z => by
        rw [ent_cap Ee u j hj z]
        exact h9 x b9 hx1 i u j hj z
      alG := fun u j hj t ht => by
        rw [ent_row Ee u j hj, ent_row Ee u j hj]
        exact h10 x b10 hx1 i u j hj t ht
      capG := fun u j hj z => by
        rw [ent_cap Ee u j hj z]
        exact h11 x b11 hx1 i u j hj z }

end GlobalTheory.ShapeRows
