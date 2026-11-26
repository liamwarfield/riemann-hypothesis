module

public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NdBNonneg

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.PriceLinearCombinationLe
section -- merged from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NeSumLe
section -- merged from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.PriceBoundLargePrimes
section -- merged from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.PriceBoundSmallPrimes
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

def PriceBoundLargePrimes (C₀ : ℝ) : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (L : SizeData₂ D) (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts),
    C₀ ≤ K.Pr1 → Formalism.MainNotions.SizesAt L →
    ∀ hT : GatTies D, Formalism.MainNotions.G.LatTied hT X Y → ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl)
      (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
      L.sc.p0 D.R.k ≤ ((D.what₂.places.resChar w : ℕ) : ℝ) →
      ∀ t0 ∈ Formalism.MainNotions.G.reps X (D.what₂.places.resChar w), ∀ j ∈ SizeData₂.lifts D,
        Formalism.MainNotions.FormalGroupSystem.Pr (Y.Fl u w hg).t (D.gat u w hg).P.r ((D.gat u w hg).P.lam0 (Y.vOf u w hg t0))
          ((Y.Fl u w hg).w (Y.vOf u w hg t0)) j ≤
          Formalism.MainNotions.G.Pr X K (Formalism.MainNotions.G.bL L) (D.what₂.places.resChar w) j t0

def PriceBoundSmallPrimes : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (L : SizeData₂ D) (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts),
    (Formalism.MainNotions.G.rG L.sc < D.R.k ∧ 2 ≤ L.sc.x) → Formalism.MainNotions.SizesAt L →
    ∀ hT : GatTies D, Formalism.MainNotions.G.LatTied hT X Y → ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl)
      (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
      ((D.what₂.places.resChar w : ℕ) : ℝ) < L.sc.p0 D.R.k →
      ∀ t0 ∈ Formalism.MainNotions.G.reps X (D.what₂.places.resChar w), ∀ j ∈ SizeData₂.lifts D,
        Formalism.MainNotions.FormalGroupSystem.Pr (Y.Fl u w hg).t (D.gat u w hg).P.r ((D.gat u w hg).P.lam0 (Y.vOf u w hg t0))
          ((Y.Fl u w hg).w (Y.vOf u w hg t0)) j ≤
          Formalism.MainNotions.G.Pr X K (Formalism.MainNotions.G.bL L) (D.what₂.places.resChar w) j t0

theorem priceBound_of_largePrimes_of_smallPrimes (C₀ : ℝ) (h1 : PriceBoundLargePrimes C₀) (h2 : PriceBoundSmallPrimes) : PriceBound C₀ := by
  intro D L X Y K hK1 hK2 hS hT hL u w hg _ t0 ht0 j hj
  rcases le_or_gt (L.sc.p0 D.R.k) ((D.what₂.places.resChar w : ℕ) : ℝ) with h | h
  · exact h1 D L X Y K hK1 hS hT hL u w hg h t0 ht0 j hj
  · exact h2 D L X Y K hK2 hS hT hL u w hg h t0 ht0 j hj

variable {n' k1 : ℕ}

theorem ne_abs (t r j : ℕ) (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (w : ℕ → Fin n' → ℤ)
    (A Bt : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ Bt)
    (h : ∀ s : Fin n', IsOddPos s → (r : ℝ) * w j s + ∑ a ∈ Icc (k1 + 2 - r) (k1 + 1), (lamI lam0 s a : ℝ) ≤
      A + (if s ∈ TT then Bt else 0)) :
    Pr t r lam0 w j ≤ n' * A + TT.card * Bt + (n' : ℝ) * r * j * (t + 1) / 2 := by
  unfold Pr
  have h1 : ∑ s ∈ univ.filter (fun s : Fin n' => IsOddPos s),
      ((r : ℝ) * w j s + ∑ a ∈ Icc (k1 + 2 - r) (k1 + 1), (lamI lam0 s a : ℝ)) ≤
      ∑ s ∈ univ.filter (fun s : Fin n' => IsOddPos s), (A + (if s ∈ TT then Bt else 0)) :=
    Finset.sum_le_sum fun s hs => h s (Finset.mem_filter.1 hs).2
  have h2 : ∑ s ∈ univ.filter (fun s : Fin n' => IsOddPos s), (A + (if s ∈ TT then Bt else 0)) ≤
      ∑ s : Fin n', (A + (if s ∈ TT then Bt else 0)) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun s _ _ => by split_ifs <;> linarith)
  have h3 : ∑ s : Fin n', (A + (if s ∈ TT then Bt else 0)) = n' * A + TT.card * Bt := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  linarith

theorem price_sum_single_edge (t j : ℕ) (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (w : ℕ → Fin n' → ℤ)
    (A : ℝ) (E : Fin n' → ℝ) (hA : 0 ≤ A)
    (h : ∀ s : Fin n', IsOddPos s → ((1 : ℕ) : ℝ) * w j s + ∑ a ∈ Icc (k1 + 2 - 1) (k1 + 1), (lamI lam0 s a : ℝ) ≤
      if s ∈ TT then E s else A) :
    Pr t 1 lam0 w j ≤ ∑ s ∈ TT.filter IsOddPos, E s + n' * A + (n' : ℝ) * ((1 : ℕ) : ℝ) * j * (t + 1) / 2 := by
  unfold Pr
  have h1 : ∑ s ∈ univ.filter (fun s : Fin n' => IsOddPos s),
      (((1 : ℕ) : ℝ) * w j s + ∑ a ∈ Icc (k1 + 2 - 1) (k1 + 1), (lamI lam0 s a : ℝ)) ≤
      ∑ s ∈ univ.filter (fun s : Fin n' => IsOddPos s), (if s ∈ TT then E s else A) :=
    Finset.sum_le_sum fun s hs => h s (Finset.mem_filter.1 hs).2
  rw [Finset.sum_ite] at h1
  have e1 : (univ.filter (fun s : Fin n' => IsOddPos s)).filter (fun s => s ∈ TT) = TT.filter IsOddPos := by
    ext s; simp [and_comm]
  rw [e1, Finset.sum_const, nsmul_eq_mul] at h1
  have h2 : (((univ.filter (fun s : Fin n' => IsOddPos s)).filter (fun s => s ∉ TT)).card : ℝ) ≤ n' := by
    have := Finset.card_le_univ ((univ.filter (fun s : Fin n' => IsOddPos s)).filter (fun s => s ∉ TT))
    rw [Fintype.card_fin] at this
    exact_mod_cast this
  have h3 := mul_le_mul_of_nonneg_right h2 hA
  exact add_le_add (le_trans h1 (add_le_add le_rfl h3)) le_rfl

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

section Fl

variable {p : ℕ} {G : Formalism.MainNotions.G.GAtP p} (Fl : Formalism.MainNotions.G.Fills G) (v : Fin G.P.nV)

theorem ne_lamI_last (s : Fin (G.P.n' v)) : lamI (G.P.lam0 v) s (G.P.m + 1) = G.P.lam0 v s (Fin.last G.P.m) := by
  unfold lamI
  rw [dite_eq_left ⟨by omega, le_rfl⟩]
  rfl

theorem ne_lamI_le (s : Fin (G.P.n' v)) (a : ℕ) (hm : 2 ≤ G.P.m) (hb : s ∈ Fl.TT v → 0 ≤ Fl.b v s) :
    lamI (G.P.lam0 v) s a ≤ (Fl.c : ℤ) + (if s ∈ Fl.TT v ∧ a = 1 then Fl.a v s else 0) := by
  have hc : (0 : ℤ) ≤ Fl.c := Int.natCast_nonneg _
  unfold lamI
  by_cases h : 1 ≤ a ∧ a ≤ G.P.m + 1
  · rw [dite_eq_left h]
    by_cases hs : s ∈ Fl.TT v
    · obtain ⟨h1, h2, h3⟩ := (Fl.base v s).1 hs
      by_cases ha : a = 1
      · subst ha
        rw [if_pos ⟨hs, rfl⟩]
        have : G.P.lam0 v s ⟨1 - 1, by omega⟩ = Fl.a v s := h1
        omega
      · rw [if_neg (fun h' => ha h'.2)]
        by_cases hl : a = G.P.m + 1
        · subst hl
          have : G.P.lam0 v s ⟨G.P.m + 1 - 1, by omega⟩ = -Fl.b v s := h2
          have := hb hs
          omega
        · have := (abs_le.1 (h3 ⟨a - 1, by omega⟩ (by show 0 < a - 1; omega) (by show a - 1 < G.P.m; omega))).2
          omega
    · rw [if_neg (fun h' => hs h'.1)]
      have := (abs_le.1 ((Fl.base v s).2 hs ⟨a - 1, by omega⟩)).2
      omega
  · rw [dite_eq_right h, if_neg (fun h' => h ⟨by omega, by omega⟩)]
    omega

end Fl

variable {D : Formalism.BasicNotions.D7} {L : SizeData₂ D}

theorem ne_kaJ_nonneg (j : ℕ) (hj : 1 ≤ j) : 0 ≤ Formalism.MainNotions.G.kaJ D j := by
  unfold Formalism.MainNotions.G.kaJ
  have h1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have h2 : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
  have h3 : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have : 0 ≤ (2 * (j : ℝ) - 1) * ((D.R.t : ℝ) + 1) := mul_nonneg (by linarith) (by linarith)
  linarith

theorem ne_w''_nonneg : 0 ≤ L.sc.w'' D.R.n := by
  unfold Scale.w''
  exact div_nonneg L.sc.b'_pos.le (mul_nonneg L.sc.x_pos.le (Nat.cast_nonneg _))

section Orbit

variable (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (hT : GatTies D) (hL : Formalism.MainNotions.G.LatTied hT X Y)
  (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
  (t0 : Formalism.MainNotions.G.HH D) (ht0 : t0 ∈ Formalism.MainNotions.G.reps X (D.what₂.places.resChar w))


include hL ht0 in
theorem ne_w_non (j : ℕ) (hj : j ∈ SizeData₂.lifts D) (s : Fin ((D.gat u w hg).P.n' (Y.vOf u w hg t0)))
    (hs : s ∉ (Y.Fl u w hg).TT (Y.vOf u w hg t0)) :
    ((Y.Fl u w hg).w (Y.vOf u w hg t0) j s : ℝ) ≤ L.sc.w'' D.R.n + L.etaSz := by
  obtain ⟨_, h2, _, h4⟩ := ((hL u w hg).2.2.2.2.2.2 t0 ht0).2 s
  rw [h4 j hj]
  have hn : t0 + s.val • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w) ∉ D.host.TT := fun h => hs (h2.2 h)
  unfold Formalism.MainNotions.G.fillG Formalism.MainNotions.G.fill
  rw [if_neg (fun h => hn h.2)]
  have h5 := (X.off_thin j (false, t0 + s.val • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w))
    ⟨fun h => hn h.2, fun h => by simpa using h.1⟩).2
  have h6 := ne_kaJ_nonneg (D := D) j (Finset.mem_Icc.1 hj).1
  linarith


include hL ht0 in
theorem ne_w_top (j : ℕ) (hj : j ∈ SizeData₂.lifts D) (s : Fin ((D.gat u w hg).P.n' (Y.vOf u w hg t0)))
    (hs : s ∈ (Y.Fl u w hg).TT (Y.vOf u w hg t0)) :
    ((Y.Fl u w hg).w (Y.vOf u w hg t0) j s : ℝ) ≤
      ((Y.Fl u w hg).b (Y.vOf u w hg t0) s : ℝ) + L.sc.b' / L.sc.x + L.etaSz := by
  obtain ⟨_, h2, h3, h4⟩ := ((hL u w hg).2.2.2.2.2.2 t0 ht0).2 s
  rw [h4 j hj, (h3 hs).2]
  have hn : t0 + s.val • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w) ∈ D.host.TT := h2.1 hs
  unfold Formalism.MainNotions.G.fillG Formalism.MainNotions.G.fill
  rw [if_pos ⟨rfl, hn⟩]
  have h5 := (X.off_top j (false, t0 + s.val • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)) ⟨rfl, hn⟩).2
  have h6 := ne_kaJ_nonneg (D := D) j (Finset.mem_Icc.1 hj).1
  linarith

include hL ht0 in
theorem ne_nP : (Formalism.MainNotions.G.nP D (D.what₂.places.resChar w) : ℝ) = ((D.gat u w hg).P.n' (Y.vOf u w hg t0) : ℕ) := by
  unfold Formalism.MainNotions.G.nP
  rw [if_neg (nc_notSg hg), nc_n_eq X Y hT hL u w hg t0 ht0]

theorem ne_Nm (j : ℕ) (hj : j ∈ SizeData₂.lifts D) : (j : ℝ) * ((D.R.t : ℝ) + 1) / 2 ≤ Formalism.MainNotions.G.Nm D := by
  unfold Formalism.MainNotions.G.Nm Ranks.N
  have h1 : (j : ℝ) ≤ D.R.m := by exact_mod_cast (Finset.mem_Icc.1 hj).2
  have h2 : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have h3 : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
  have h4 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ (D.R.t : ℝ) + 1),
    mul_nonneg h4 (by linarith : (0 : ℝ) ≤ (D.R.t : ℝ) + 1)]

end Orbit


open Classical in
theorem price_bound_large_primes : PriceBoundLargePrimes 1 := by
  intro D L X Y K hK _ hT hL u w hg hp t0 ht0 j hj
  have hr : (D.gat u w hg).P.r = 1 := by rw [(hL u w hg).2.2.2.1, if_neg (not_lt.2 hp)]
  have ht : (Y.Fl u w hg).t = D.R.t := (hL u w hg).2.1
  have hc : ((Y.Fl u w hg).c : ℝ) ≤ Formalism.MainNotions.G.cG L := (hL u w hg).2.2.1
  have hinj := nc_iota_inj X Y hT hL u w hg t0 ht0
  have hA : 0 ≤ L.sc.w'' D.R.n + L.etaSz + Formalism.MainNotions.G.cG L := by
    have := ne_w''_nonneg (L := L)
    have := L.etaSz_pos
    have := nc_cG_nonneg (L := L)
    linarith
  rw [hr]
  have h1 := price_sum_single_edge (Y.Fl u w hg).t j ((Y.Fl u w hg).TT (Y.vOf u w hg t0)) ((D.gat u w hg).P.lam0 (Y.vOf u w hg t0))
    ((Y.Fl u w hg).w (Y.vOf u w hg t0)) (L.sc.w'' D.R.n + L.etaSz + Formalism.MainNotions.G.cG L)
    (fun s => ((Y.Fl u w hg).w (Y.vOf u w hg t0) j s : ℝ) - ((Y.Fl u w hg).b (Y.vOf u w hg t0) s : ℝ)) hA
    (fun s _ => by
      have e : (D.gat u w hg).P.m + 2 - 1 = (D.gat u w hg).P.m + 1 := rfl
      rw [e, Finset.Icc_self, Finset.sum_singleton, ne_lamI_last]
      split_ifs with hs
      · rw [((Y.Fl u w hg).base (Y.vOf u w hg t0) s).1 hs |>.2.1]
        push_cast
        linarith
      · have h2 := ne_w_non X Y hT hL u w hg t0 ht0 j hj s hs
        have h3 := (abs_le.1 (((Y.Fl u w hg).base (Y.vOf u w hg t0) s).2 hs (Fin.last _))).2
        have h4 : (((D.gat u w hg).P.lam0 (Y.vOf u w hg t0) s (Fin.last _) : ℤ) : ℝ) ≤ ((Y.Fl u w hg).c : ℝ) := by
          exact_mod_cast h3
        push_cast
        linarith)
  refine le_trans h1 ?_
  unfold Formalism.MainNotions.G.Pr
  rw [if_pos hp, nc_topsOn X Y hT hL u w hg t0 ht0, Finset.filter_image, Finset.sum_image (fun a _ b _ h => hinj h)]
  have hf : ((Y.Fl u w hg).TT (Y.vOf u w hg t0)).filter
      (fun a => ¬ Formalism.MainNotions.G.IsV X (D.what₂.places.resChar w) (nc_iota Y u w hg t0 a)) =
      ((Y.Fl u w hg).TT (Y.vOf u w hg t0)).filter IsOddPos := by
    apply Finset.filter_congr
    intro s _
    rw [nc_isV X Y hT hL u w hg t0 ht0 s, not_not]
  rw [hf, ne_nP X Y hT hL u w hg t0 ht0, ht]
  have e1 : ∑ s ∈ ((Y.Fl u w hg).TT (Y.vOf u w hg t0)).filter IsOddPos,
      (((Y.Fl u w hg).w (Y.vOf u w hg t0) j s : ℝ) - ((Y.Fl u w hg).b (Y.vOf u w hg t0) s : ℝ)) =
      ∑ s ∈ ((Y.Fl u w hg).TT (Y.vOf u w hg t0)).filter IsOddPos,
        (Formalism.MainNotions.G.fillG X (Formalism.MainNotions.G.bL L) j (false, nc_iota Y u w hg t0 s) -
          (Formalism.MainNotions.G.bL L (nc_iota Y u w hg t0 s) : ℝ)) := by
    apply Finset.sum_congr rfl
    intro s hs
    obtain ⟨_, _, h3, h4⟩ := ((hL u w hg).2.2.2.2.2.2 t0 ht0).2 s
    rw [h4 j hj, (h3 (Finset.mem_filter.1 hs).1).2]
  rw [e1]
  have hN := ne_Nm (D := D) j hj
  have hn : (0 : ℝ) ≤ ((D.gat u w hg).P.n' (Y.vOf u w hg t0) : ℕ) := Nat.cast_nonneg _
  have hNm : 0 ≤ Formalism.MainNotions.G.Nm D := le_trans (by positivity) hN
  have h5 : ((D.gat u w hg).P.n' (Y.vOf u w hg t0) : ℝ) * (L.sc.w'' D.R.n + L.etaSz + Formalism.MainNotions.G.cG L + Formalism.MainNotions.G.Nm D) ≤
      K.Pr1 * ((D.gat u w hg).P.n' (Y.vOf u w hg t0) : ℝ) *
        (L.sc.w'' D.R.n + L.etaSz + Formalism.MainNotions.G.cG L + Formalism.MainNotions.G.Nm D) := by
    have := mul_le_mul_of_nonneg_right hK
      (mul_nonneg hn (by linarith : 0 ≤ L.sc.w'' D.R.n + L.etaSz + Formalism.MainNotions.G.cG L + Formalism.MainNotions.G.Nm D))
    linarith
  have h6 : ((D.gat u w hg).P.n' (Y.vOf u w hg t0) : ℝ) * ((1 : ℕ) : ℝ) * j * ((D.R.t : ℝ) + 1) / 2 ≤
      ((D.gat u w hg).P.n' (Y.vOf u w hg t0) : ℝ) * Formalism.MainNotions.G.Nm D := by
    have := mul_le_mul_of_nonneg_left hN hn
    push_cast
    linarith
  linarith

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

section Fl

variable {p : ℕ} {G : Formalism.MainNotions.G.GAtP p} (Fl : Formalism.MainNotions.G.Fills G) (v : Fin G.P.nV)

theorem ne_sum_le (s : Fin (G.P.n' v)) (r : ℕ) (hm : 2 ≤ G.P.m) (hb : s ∈ Fl.TT v → 0 ≤ Fl.b v s) :
    ∑ a ∈ Icc (G.P.m + 2 - r) (G.P.m + 1), (lamI (G.P.lam0 v) s a : ℝ) ≤
      r * Fl.c + (if s ∈ Fl.TT v ∧ G.P.m + 1 ≤ r then (Fl.a v s : ℝ) else 0) := by
  have h1 : ∑ a ∈ Icc (G.P.m + 2 - r) (G.P.m + 1), (lamI (G.P.lam0 v) s a : ℝ) ≤
      ∑ a ∈ Icc (G.P.m + 2 - r) (G.P.m + 1), ((Fl.c : ℝ) + (if s ∈ Fl.TT v ∧ a = 1 then (Fl.a v s : ℝ) else 0)) := by
    apply Finset.sum_le_sum
    intro a _
    have := ne_lamI_le Fl v s a hm hb
    by_cases hc : s ∈ Fl.TT v ∧ a = 1
    · rw [if_pos hc] at this ⊢
      exact_mod_cast this
    · rw [if_neg hc] at this ⊢
      exact_mod_cast this
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at h1
  have h2 : ((Icc (G.P.m + 2 - r) (G.P.m + 1)).card : ℝ) ≤ r := by
    rw [Nat.card_Icc]
    have : G.P.m + 1 + 1 - (G.P.m + 2 - r) ≤ r := by omega
    exact_mod_cast this
  have h3 := mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg Fl.c : (0 : ℝ) ≤ Fl.c)
  have h4 : ∑ a ∈ Icc (G.P.m + 2 - r) (G.P.m + 1), (if s ∈ Fl.TT v ∧ a = 1 then (Fl.a v s : ℝ) else 0) =
      (if s ∈ Fl.TT v ∧ G.P.m + 1 ≤ r then (Fl.a v s : ℝ) else 0) := by
    by_cases hs : s ∈ Fl.TT v
    · simp only [hs, true_and]
      rw [Finset.sum_ite_eq' (Icc (G.P.m + 2 - r) (G.P.m + 1)) 1 (fun _ => (Fl.a v s : ℝ))]
      have : (1 ∈ Icc (G.P.m + 2 - r) (G.P.m + 1)) ↔ G.P.m + 1 ≤ r := by
        rw [Finset.mem_Icc]; omega
      simp only [this]
    · simp [hs]
  rw [h4] at h1
  linarith

end Fl

variable {D : Formalism.BasicNotions.D7} {L : SizeData₂ D}

theorem ne_k_pos : (1 : ℝ) ≤ D.R.k := by
  have h2 := D.R.m_add_three_le_k
  have : 1 ≤ D.R.k := by omega
  exact_mod_cast this

theorem ne_bT_le (hS : Formalism.MainNotions.SizesAt L) (t) : (L.bT t : ℝ) ≤ 5 / 4 * L.sc.b' := by
  have hx := L.sc.one_lt_alt
  have hLa := hS.2.2.2.2.2.2.2.2.1
  have hRho := hS.2.2.2.2.2.2.2.2.2.1
  have hBot := hS.2.2.2.2.2.2.2.2.2.2.1 t
  unfold Formalism.MainNotions.SizeRho at hRho
  have hk := ne_k_pos (D := D)
  have hLa0 : 0 ≤ L.LaG := le_trans (Real.rpow_nonneg L.sc.x_pos.le _) hLa.1
  have h1 : 0 ≤ L.sc.x ^ Formalism.MainNotions.szTh L * Real.log L.sc.x * L.LaG / D.R.k :=
    div_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg L.sc.x_pos.le _) (Real.log_nonneg hx.le)) hLa0) (by linarith)
  have h2 : L.sc.x ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx.le (by norm_num)
  have h3 : Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k ≤ 1 / 4 := by
    have : 4 * Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k =
        4 * (Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) := by ring
    linarith
  have h4 : Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k =
      (Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) * L.sc.b' := by ring
  have h5 := mul_le_mul_of_nonneg_right h3 L.sc.b'_pos.le
  linarith

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

theorem price_linear_combination_le (n N rr w2 η cg NM b1 jt : ℝ) (hn : 0 ≤ n) (hN : 0 ≤ N) (hr : 0 ≤ rr) (hcg : 0 ≤ cg) (hjt : jt ≤ NM) :
    n * (rr * (w2 + η + cg)) + N * (rr * (2 * b1)) + n * rr * jt ≤
      rr * (N * (2 * b1 + cg) + n * (w2 + η + cg + NM)) := by
  nlinarith [mul_nonneg (mul_nonneg hr hN) hcg, mul_nonneg (mul_nonneg hn hr) (sub_nonneg.mpr hjt)]

variable {D : Formalism.BasicNotions.D7} {L : SizeData₂ D}

section Orbit

variable (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (hT : GatTies D) (hL : Formalism.MainNotions.G.LatTied hT X Y)
  (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
  (t0 : Formalism.MainNotions.G.HH D) (ht0 : t0 ∈ Formalism.MainNotions.G.reps X (D.what₂.places.resChar w))

include hL ht0 in
theorem ne_b_top (hS : Formalism.MainNotions.SizesAt L) (s : Fin ((D.gat u w hg).P.n' (Y.vOf u w hg t0)))
    (hs : s ∈ (Y.Fl u w hg).TT (Y.vOf u w hg t0)) :
    L.sc.b' ≤ ((Y.Fl u w hg).b (Y.vOf u w hg t0) s : ℝ) ∧
      ((Y.Fl u w hg).b (Y.vOf u w hg t0) s : ℝ) ≤ 5 / 4 * L.sc.b' := by
  obtain ⟨_, h2, h3, _⟩ := ((hL u w hg).2.2.2.2.2.2 t0 ht0).2 s
  rw [(h3 hs).2]
  unfold Formalism.MainNotions.G.bL
  rw [dite_eq_left (h2.1 hs)]
  exact ⟨L.bT_ge _, ne_bT_le hS _⟩


end Orbit

def priceThreshold : ℝ := 9

theorem price_threshold_ge_nine : 9 ≤ priceThreshold := by norm_num [priceThreshold]


open Classical in
theorem price_bound_small_primes : PriceBoundSmallPrimes := by
  intro D L X Y K hK hS hT hL u w hg hp t0 ht0 j hj
  obtain ⟨hrk, hx2⟩ := hK
  have hr : (D.gat u w hg).P.r = Formalism.MainNotions.G.rG L.sc := by rw [(hL u w hg).2.2.2.1, if_pos hp]
  have ht : (Y.Fl u w hg).t = D.R.t := (hL u w hg).2.1
  have hc : ((Y.Fl u w hg).c : ℝ) ≤ Formalism.MainNotions.G.cG L := (hL u w hg).2.2.1
  have hinj := nc_iota_inj X Y hT hL u w hg t0 ht0
  have hm := nc_m_ge hT u w hg
  have hk := hT.gat_k u w hg
  have hno : ¬ ((D.gat u w hg).P.m + 1 ≤ Formalism.MainNotions.G.rG L.sc) := by omega
  have hr0 : (0 : ℝ) ≤ (Formalism.MainNotions.G.rG L.sc : ℝ) := Nat.cast_nonneg _
  have hw := ne_w''_nonneg (L := L)
  have hη := L.etaSz_pos
  have hcG := nc_cG_nonneg (L := L)
  have hb' := L.sc.b'_pos
  rw [hr]
  have h1 := ne_abs (Y.Fl u w hg).t (Formalism.MainNotions.G.rG L.sc) j ((Y.Fl u w hg).TT (Y.vOf u w hg t0))
    ((D.gat u w hg).P.lam0 (Y.vOf u w hg t0)) ((Y.Fl u w hg).w (Y.vOf u w hg t0))
    ((Formalism.MainNotions.G.rG L.sc : ℝ) * (L.sc.w'' D.R.n + L.etaSz + Formalism.MainNotions.G.cG L))
    ((Formalism.MainNotions.G.rG L.sc : ℝ) * (2 * L.sc.b'))
    (by positivity) (by positivity)
    (fun s _ => by
      have hsum := ne_sum_le (Y.Fl u w hg) (Y.vOf u w hg t0) s (Formalism.MainNotions.G.rG L.sc) hm (fun hs => by
        have h0 := (ne_b_top X Y hT hL u w hg t0 ht0 hS s hs).1
        have : (0 : ℝ) ≤ ((Y.Fl u w hg).b (Y.vOf u w hg t0) s : ℝ) := by linarith
        exact_mod_cast this)
      rw [if_neg (fun h => hno h.2)] at hsum
      have h7 := mul_le_mul_of_nonneg_left hc hr0
      have h11 := mul_nonneg hr0 hw
      by_cases hs : s ∈ (Y.Fl u w hg).TT (Y.vOf u w hg t0)
      · rw [if_pos hs]
        have hwt := ne_w_top X Y hT hL u w hg t0 ht0 j hj s hs
        have hb := (ne_b_top X Y hT hL u w hg t0 ht0 hS s hs).2
        have hx : L.sc.b' / L.sc.x ≤ L.sc.b' / 2 := div_le_div_of_nonneg_left hb'.le (by norm_num) hx2
        have h5 := mul_le_mul_of_nonneg_left
          (show ((Y.Fl u w hg).w (Y.vOf u w hg t0) j s : ℝ) ≤ 2 * L.sc.b' + L.etaSz by linarith) hr0
        nlinarith [h5, h7, hsum, h11]
      · rw [if_neg hs]
        have hwn := ne_w_non X Y hT hL u w hg t0 ht0 j hj s hs
        have h5 := mul_le_mul_of_nonneg_left hwn hr0
        nlinarith [h5, h7, hsum])
  refine le_trans h1 ?_
  unfold Formalism.MainNotions.G.Pr Formalism.MainNotions.G.Nv
  rw [if_neg (not_le.2 hp), nc_topsOn X Y hT hL u w hg t0 ht0, Finset.card_image_of_injective _ hinj,
    ne_nP X Y hT hL u w hg t0 ht0, ht]
  have hN := ne_Nm (D := D) j hj
  have hfin := price_linear_combination_le ((D.gat u w hg).P.n' (Y.vOf u w hg t0) : ℝ) (((Y.Fl u w hg).TT (Y.vOf u w hg t0)).card : ℝ)
    (Formalism.MainNotions.G.rG L.sc : ℝ) (L.sc.w'' D.R.n) L.etaSz (Formalism.MainNotions.G.cG L) (Formalism.MainNotions.G.Nm D) L.sc.b'
    ((j : ℝ) * ((D.R.t : ℝ) + 1) / 2) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hr0 hcG hN
  have e : ((D.gat u w hg).P.n' (Y.vOf u w hg t0) : ℝ) * (Formalism.MainNotions.G.rG L.sc : ℝ) * (j : ℝ) * ((D.R.t : ℝ) + 1) / 2 =
      ((D.gat u w hg).P.n' (Y.vOf u w hg t0) : ℝ) * (Formalism.MainNotions.G.rG L.sc : ℝ) * ((j : ℝ) * ((D.R.t : ℝ) + 1) / 2) := by ring
  rw [e]
  exact hfin

theorem priceBoundLargePrimes_priceThreshold : PriceBoundLargePrimes priceThreshold :=
  fun D L X Y K hK => price_bound_large_primes D L X Y K (by linarith [price_threshold_ge_nine])

theorem ne_priceThreshold : PriceBound priceThreshold :=
  priceBound_of_largePrimes_of_smallPrimes priceThreshold priceBoundLargePrimes_priceThreshold price_bound_small_primes

theorem numericalComparisonUniform_of_size (hS : nd_NeedSize) : Formalism.MainNotions.FormalGroupSystem.NumericalComparisonUniform :=
  numerical_closed_of_threshold priceThreshold price_threshold_ge_nine (nc_need3_of priceThreshold hS ne_priceThreshold)

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

namespace Formalism.MainNotions.FormalGroupSystem.Pf

theorem stmtNumE : Formalism.MainNotions.FormalGroupSystem.NumericalComparisonUniform := numericalComparisonUniform_of_size nd_size

end Formalism.MainNotions.FormalGroupSystem.Pf
