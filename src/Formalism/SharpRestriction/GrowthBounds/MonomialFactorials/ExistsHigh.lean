module

public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RestTMExists
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RatioConditionOfSegFacts

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.LowerBoundInitialMultiplicity
section -- merged from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.UTopVal
section -- merged from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RestTMSizeOf
section -- merged from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.WindowEntryLeTwoMulA
section -- merged from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.SegDistsLtG
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

variable {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst}

private theorem sort_get_lt_of_lt (s : Finset ℕ) (l u : Fin (s.sort (fun x1 x2 : ℕ => x1 ≤ x2)).length)
    (h : l < u) : (s.sort (fun x1 x2 : ℕ => x1 ≤ x2)).get l < (s.sort (fun x1 x2 : ℕ => x1 ≤ x2)).get u := by
  have hp := Finset.pairwise_sort s (fun x1 x2 : ℕ => x1 ≤ x2)
  have hn := Finset.sort_nodup s (fun x1 x2 : ℕ => x1 ≤ x2)
  have hle : (s.sort (fun x1 x2 : ℕ => x1 ≤ x2)).get l ≤ (s.sort (fun x1 x2 : ℕ => x1 ≤ x2)).get u :=
    hp.rel_get_of_lt h
  have hne : (s.sort (fun x1 x2 : ℕ => x1 ≤ x2)).get l ≠ (s.sort (fun x1 x2 : ℕ => x1 ≤ x2)).get u := by
    intro he
    have := (List.nodup_iff_injective_get.mp hn) he
    exact absurd this (ne_of_lt h)
  omega

theorem segDists_lt {n' : ℕ} (TT : Finset (Fin n')) (j : Fin (numSeg TT)) (l u : Fin (segS TT j)) (h : l < u) :
    (segDists TT j).get l < (segDists TT j).get u := sort_get_lt_of_lt _ l u h

theorem segDists_lt_G {n' : ℕ} (TT : Finset (Fin n')) (j : Fin (numSeg TT)) (u : Fin (segS TT j)) :
    (segDists TT j).get u < segG TT j := by
  have hm : (segDists TT j).get u ∈ segDists TT j := List.get_mem _ _
  unfold segDists at hm
  rw [Finset.mem_sort, Finset.mem_image] at hm
  obtain ⟨x, hx, hxe⟩ := hm
  rw [Finset.mem_filter] at hx
  have e : (segDists TT j).get u = cdist (segStart TT j) x := hxe.symm
  rw [e]
  exact hx.2.2.2

theorem P_step (l u : Fin X.s) (h : l < u) :
    X.p * (X.S C0 CE1 CE2).P X.p u ≤ (X.S C0 CE1 CE2).P X.p l := by
  have h1 := segDists_lt X.L.TT X.j l u h
  have h2 := segDists_lt_G X.L.TT X.j u
  have hp : 0 < X.p := by
    have := X.std.1.five_le
    show 0 < X.L.p
    omega
  show X.p * X.p ^ (segG X.L.TT X.j - (segDists X.L.TT X.j).get u) ≤
    X.p ^ (segG X.L.TT X.j - (segDists X.L.TT X.j).get l)
  rw [← pow_succ']
  exact Nat.pow_le_pow_right hp (by omega)

theorem p_le_P (u : Fin X.s) : X.p ≤ (X.S C0 CE1 CE2).P X.p u := by
  have h1 := segDists_lt_G X.L.TT X.j u
  have hp : 0 < X.p := by
    have := X.std.1.five_le
    show 0 < X.L.p
    omega
  show X.p ≤ X.p ^ (segG X.L.TT X.j - (segDists X.L.TT X.j).get u)
  calc X.p = X.p ^ 1 := (pow_one _).symm
    _ ≤ _ := Nat.pow_le_pow_right hp (by omega)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

variable {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst}

section Deg

variable (hS : SegFacts C0 CE1 CE2 X)
include hS

theorem window_entry_le_two_mul_a (a : Fin X.s → ℕ) (hT : a ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA)) (l : Fin X.s) :
    (a l : ℝ) ≤ 2 * X.L.a := by
  have h2 := (Finset.mem_Icc.1 (Fintype.mem_piFinset.1 hT l)).2
  have h3 : (a l : ℝ) ≤ (⌊(X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) + X.xa⌋₊ : ℝ) := by exact_mod_cast h2
  exact (h3.trans (Nat.floor_le hS.hF.win0)).trans hS.hF.win_le

theorem r5 : (5 : ℝ) ≤ (X.r : ℝ) + 1 := by
  have : (4 : ℝ) ≤ (X.L.m : ℝ) := by exact_mod_cast hS.hF.m4
  show (5 : ℝ) ≤ (X.L.m : ℝ) + 1
  linarith

theorem b_small : 5 / 2 * X.L.b' ≤ X.L.a / 8 := by
  have h1 := hS.kb
  have h2 := r5 hS
  have hb := hS.hF.b0
  nlinarith

theorem chain_wt (a : Fin X.s → ℕ) (hT : a ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA)) (b : SegBlock X.s X.r)
    (hK : Kept X.p X.r (X.S C0 CE1 CE2) a b) (q : Fin (2 * X.s + 1)) (hq : (q : ℕ) ≠ 2 * X.s) :
    ((segChain X.p (X.S C0 CE1 CE2) a b).deg q : ℝ) * ((X.S C0 CE1 CE2).P X.p (topOf q hq) : ℝ) ≤ 2 * X.L.a := by
  have hA : ∀ l, (coarseA X.p (X.S C0 CE1 CE2) b l : ℝ) * ((X.S C0 CE1 CE2).P X.p l : ℝ) ≤ 2 * X.L.a := fun l =>
    (coarseA_upper hS b l).trans (by have := b_small hS; have : (0 : ℝ) ≤ X.L.a := Nat.cast_nonneg _; linarith)
  have hC : ∀ l, (coarseC X.p (X.S C0 CE1 CE2) a b l : ℝ) * ((X.S C0 CE1 CE2).P X.p l : ℝ) ≤ 2 * X.L.a := by
    intro l
    have h1 : coarseC X.p (X.S C0 CE1 CE2) a b l * (X.S C0 CE1 CE2).P X.p l ≤ a l :=
      (Nat.div_mul_le_self _ _).trans (Nat.sub_le _ _)
    have h2 : ((coarseC X.p (X.S C0 CE1 CE2) a b l * (X.S C0 CE1 CE2).P X.p l : ℕ) : ℝ) ≤ (a l : ℝ) := by exact_mod_cast h1
    push_cast at h2
    exact h2.trans (window_entry_le_two_mul_a hS a hT l)
  have hP0 : (0 : ℝ) ≤ ((X.S C0 CE1 CE2).P X.p (topOf q hq) : ℝ) := Nat.cast_nonneg _
  have key : (segChain X.p (X.S C0 CE1 CE2) a b).deg q ≤ coarseA X.p (X.S C0 CE1 CE2) b (topOf q hq) ∨
      (segChain X.p (X.S C0 CE1 CE2) a b).deg q ≤ coarseC X.p (X.S C0 CE1 CE2) a b (topOf q hq) := by
    unfold segChain
    dsimp only
    rw [dite_eq_right hq]
    split_ifs with h2 h3 h3
    · exact Or.inl (hK.2.2.1 _ h3).2.1
    · exact Or.inl (hK.2.1 _ (not_lt.mp h3)).1
    · exact Or.inr (Nat.sub_le _ _)
    · exact Or.inr le_rfl
  rcases key with h | h
  · have : ((segChain X.p (X.S C0 CE1 CE2) a b).deg q : ℝ) ≤ (coarseA X.p (X.S C0 CE1 CE2) b (topOf q hq) : ℝ) := by
      exact_mod_cast h
    exact (mul_le_mul_of_nonneg_right this hP0).trans (hA _)
  · have : ((segChain X.p (X.S C0 CE1 CE2) a b).deg q : ℝ) ≤ (coarseC X.p (X.S C0 CE1 CE2) a b (topOf q hq) : ℝ) := by
      exact_mod_cast h
    exact (mul_le_mul_of_nonneg_right this hP0).trans (hC _)

theorem oplus_le (b : SegBlock X.s X.r) (a : Fin X.s → ℕ) (hK : Kept X.p X.r (X.S C0 CE1 CE2) a b) :
    (b.oPlus : ℝ) ≤ 2 * X.L.a := by
  have h0 := hK.2.2.2
  unfold Oplus at h0
  have hp1 : 1 ≤ X.p := X.std.1.prime.one_lt.le
  have hB : ∀ i, ((X.S C0 CE1 CE2).bTop i : ℝ) ≤ 5 / 2 * X.L.b' := hS.bTop
  have hcap := cap_le (p := X.p) (X.S C0 CE1 CE2) b hp1 hS.E0 (5 / 2 * X.L.b') hB X.s
  have hr5 := r5 hS
  have hs : 2 * (X.s : ℝ) + 2 ≤ (X.r : ℝ) := by exact_mod_cast hS.hF.s_le
  have hp : ((X.r : ℝ) + 1) ^ 2 ≤ (X.p : ℝ) := hS.hF.p_ge
  have hb := hS.hF.b0
  have hkb := hS.kb
  have ha0 : (0 : ℝ) ≤ X.L.a := Nat.cast_nonneg _
  have hLa0 := hS.hF.La0
  have hLa : X.L.La C0 / ((X.r : ℝ) + 1) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by linarith)]; linarith [hS.La4]
  have hp0 : (0 : ℝ) < (X.p : ℝ) := by nlinarith
  have hp5 : (5 : ℝ) ≤ (X.p : ℝ) := by nlinarith
  have h4 : 4 / (X.p : ℝ) ^ 2 ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hsum : (∑ i, 2 * ((X.S C0 CE1 CE2).a : ℝ) / ((X.S C0 CE1 CE2).P X.p i : ℝ)) ≤ (X.s : ℝ) * (2 * X.L.a / X.p) := by
    have : ∀ i, 2 * ((X.S C0 CE1 CE2).a : ℝ) / ((X.S C0 CE1 CE2).P X.p i : ℝ) ≤ 2 * X.L.a / X.p := by
      intro i
      have hP : (X.p : ℝ) ≤ ((X.S C0 CE1 CE2).P X.p i : ℝ) := by exact_mod_cast p_le_P i
      show 2 * (X.L.a : ℝ) / _ ≤ _
      exact div_le_div_of_nonneg_left (by positivity) hp0 hP
    calc _ ≤ ∑ _i : Fin X.s, 2 * (X.L.a : ℝ) / X.p := Finset.sum_le_sum fun i _ => this i
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hsp : (X.s : ℝ) * (2 * X.L.a / X.p) ≤ X.L.a / 5 := by
    rw [mul_div_assoc', div_le_div_iff₀ hp0 (by norm_num)]
    have h10 : 10 * (X.s : ℝ) ≤ (X.p : ℝ) := by nlinarith
    have := mul_le_mul_of_nonneg_left h10 ha0
    linarith
  have hsum0 : 0 ≤ ∑ i, 2 * ((X.S C0 CE1 CE2).a : ℝ) / ((X.S C0 CE1 CE2).P X.p i : ℝ) :=
    Finset.sum_nonneg fun i _ => by positivity
  have hmid : (X.S C0 CE1 CE2).La / ((X.r : ℝ) + 1) + 4 / (X.p : ℝ) ^ 2 ≤ 1 / 2 := by
    show X.L.La C0 / ((X.r : ℝ) + 1) + 4 / (X.p : ℝ) ^ 2 ≤ 1 / 2
    linarith
  have hmid0 : 0 ≤ (X.S C0 CE1 CE2).La / ((X.r : ℝ) + 1) + 4 / (X.p : ℝ) ^ 2 := by
    show 0 ≤ X.L.La C0 / ((X.r : ℝ) + 1) + 4 / (X.p : ℝ) ^ 2
    positivity
  have hT2 : ((X.S C0 CE1 CE2).La / ((X.r : ℝ) + 1) + 4 / (X.p : ℝ) ^ 2) *
      ∑ i, 2 * ((X.S C0 CE1 CE2).a : ℝ) / ((X.S C0 CE1 CE2).P X.p i : ℝ) ≤ X.L.a / 10 := by
    have := mul_le_mul hmid (hsum.trans hsp) hsum0 (by norm_num)
    linarith
  have hBp : ((X.S C0 CE1 CE2).bPlus : ℝ) ≤ 5 / 2 * X.L.b' := hS.hF.bT_le _ (segNext_mem X.L.TT X.j)
  have hT3 : (X.S C0 CE1 CE2).La * ((X.S C0 CE1 CE2).bPlus : ℝ) / ((X.r : ℝ) + 1) ≤ X.L.a / 10 := by
    have e : (X.S C0 CE1 CE2).La * ((X.S C0 CE1 CE2).bPlus : ℝ) / ((X.r : ℝ) + 1) =
        X.L.La C0 / ((X.r : ℝ) + 1) * ((X.S C0 CE1 CE2).bPlus : ℝ) := by
      show X.L.La C0 * _ / _ = _
      ring
    rw [e]
    have h5 := b_small hS
    have h6 : (0 : ℝ) ≤ ((X.S C0 CE1 CE2).bPlus : ℝ) := Nat.cast_nonneg _
    have h7 : X.L.La C0 / ((X.r : ℝ) + 1) * ((X.S C0 CE1 CE2).bPlus : ℝ) ≤ 1 / 4 * (5 / 2 * X.L.b') :=
      mul_le_mul hLa hBp h6 (by norm_num)
    linarith
  have hsB : (X.s : ℝ) * (5 / 2 * X.L.b') ≤ X.L.a / 2 := by
    have h1 : (X.s : ℝ) ≤ ((X.r : ℝ) + 1) / 2 := by linarith
    have h2 : (X.s : ℝ) * (5 / 2 * X.L.b') ≤ ((X.r : ℝ) + 1) / 2 * (5 / 2 * X.L.b') :=
      mul_le_mul_of_nonneg_right h1 (by linarith)
    linarith
  have ha : (X.S C0 CE1 CE2).a = X.L.a := rfl
  rw [ha] at hcap
  linarith

theorem lLL_deg_le_chain (a : Fin X.s → ℕ) (b : SegBlock X.s X.r) (x : Lv C0 CE1 CE2 X) (q : Fin (2 * X.s + 1)) :
    (lLL C0 CE1 CE2 X a b x).deg q ≤ (segChain X.p (X.S C0 CE1 CE2) a b).deg q :=
  (Nat.sub_le _ _).trans (Nat.sub_le _ _)

theorem lLL_deg_le (a : Fin X.s → ℕ) (hT : a ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA)) (b : SegBlock X.s X.r)
    (hK : Kept X.p X.r (X.S C0 CE1 CE2) a b) (x : Lv C0 CE1 CE2 X) (q : Fin (2 * X.s + 1)) :
    (lLL C0 CE1 CE2 X a b x).deg q ≤ 2 * X.L.a := by
  have h1 := lLL_deg_le_chain hS a b x q
  have h2 : ((segChain X.p (X.S C0 CE1 CE2) a b).deg q : ℝ) ≤ 2 * X.L.a := by
    by_cases hq : (q : ℕ) = 2 * X.s
    · have e := segChain_deg_last (p := X.p) (X.S C0 CE1 CE2) a b q hq
      rw [e]
      exact oplus_le hS b a hK
    · have hw := chain_wt hS a hT b hK q hq
      have hP : (1 : ℝ) ≤ ((X.S C0 CE1 CE2).P X.p (topOf q hq) : ℝ) := by exact_mod_cast hS.P1 _
      have h0 : (0 : ℝ) ≤ ((segChain X.p (X.S C0 CE1 CE2) a b).deg q : ℝ) := Nat.cast_nonneg _
      nlinarith
  have h3 : (segChain X.p (X.S C0 CE1 CE2) a b).deg q ≤ 2 * X.L.a := by exact_mod_cast h2
  omega

end Deg

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

variable {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst}


variable (C0 CE1 CE2 X) in
def aTopPt (dl : DCl X) (a : Fin X.s → ℕ) : Fin X.s → ℕ :=
  ovr (uTop (X.S C0 CE1 CE2)) a (fun i => topA C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i))

theorem digits_of_idx {dl : DCl X} {a : Fin X.s → ℕ} {x : Σ _ : SegBlock X.s X.r, Lv C0 CE1 CE2 X}
    (hx : x ∈ idx C0 CE1 CE2 X dl a) :
    Kept X.p X.r (X.S C0 CE1 CE2) a x.1 ∧ (x.1.rz, x.1.ry) = dl ∧ x.2 ∈ lv C0 CE1 CE2 X a x.1 := by
  classical
  unfold idx at hx
  simp only [Finset.mem_sigma, Finset.mem_filter, mem_keptSet] at hx
  exact ⟨hx.1.1, hx.1.2, hx.2⟩

theorem Wl_ne {dl : DCl X} {a : Fin X.s → ℕ} (ha : a ∈ cbox C0 CE1 CE2 X dl) (l : Fin X.s) :
    (Wl C0 CE1 CE2 X dl l).Nonempty := by
  have hbox := cbox_eq C0 CE1 CE2 X dl a ha
  have hW : a ∈ Fintype.piFinset (Wl C0 CE1 CE2 X dl) := hbox ▸ ha
  exact ⟨a l, Fintype.mem_piFinset.1 hW l⟩

theorem topA_mem_Wl {dl : DCl X} {a : Fin X.s → ℕ} (ha : a ∈ cbox C0 CE1 CE2 X dl) (l : Fin X.s) :
    topA C0 CE1 CE2 X dl l ∈ Wl C0 CE1 CE2 X dl l := by
  obtain ⟨M, hM, hMe⟩ := Finset.exists_mem_eq_sup _ (Wl_ne ha l) (id : ℕ → ℕ)
  rw [topA_eq, hMe]
  exact hM

theorem aTopPt_mem {dl : DCl X} {a : Fin X.s → ℕ} (ha : a ∈ cbox C0 CE1 CE2 X dl) :
    aTopPt C0 CE1 CE2 X dl a ∈ cbox C0 CE1 CE2 X dl := by
  have hbox := cbox_eq C0 CE1 CE2 X dl a ha
  have hW : a ∈ Fintype.piFinset (Wl C0 CE1 CE2 X dl) := hbox ▸ ha
  rw [hbox]
  exact ovr_mem _ (uTop_inj C0 CE1 CE2 X) _ a _ hW (Fintype.mem_piFinset.2 fun i => topA_mem_Wl ha _)

theorem setTies_top {dl : DCl X} {a : Fin X.s → ℕ} (ha : a ∈ cbox C0 CE1 CE2 X dl)
    {x : Σ _ : SegBlock X.s X.r, Lv C0 CE1 CE2 X} (hx : x ∈ idx C0 CE1 CE2 X dl a) :
    (XMof C0 CE1 CE2 X dl a x.1 x.2).LL.setTies (XMof C0 CE1 CE2 X dl a x.1 x.2).T
        (XMof C0 CE1 CE2 X dl a x.1 x.2).top = lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2 := by
  have hb : x.1.ry = dl.2 := congrArg Prod.snd (digits_of_idx hx).2.1
  have e1 := lLL_ovr C0 CE1 CE2 X a (fun i => topA C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i)) x.1 x.2
  show (lLL C0 CE1 CE2 X a x.1 x.2).setTies (gT C0 CE1 CE2 X x.1) (XMof C0 CE1 CE2 X dl a x.1 x.2).top = _
  unfold aTopPt
  rw [e1]
  congr 1
  funext i
  rw [top_eq (dl := dl) a x.1 (x := x.2) (fun i => Wl_ne ha _) i]
  unfold cm
  rw [hb]

def RestSI : Prop :=
  ∀ dl ∈ clSet C0 CE1 CE2 X, ∀ a ∈ cbox C0 CE1 CE2 X dl, ∀ x ∈ idx C0 CE1 CE2 X dl a,
    ∀ i, (XMof C0 CE1 CE2 X dl a x.1 x.2).T.S ((XMof C0 CE1 CE2 X dl a x.1 x.2).LL.setTies
        (XMof C0 CE1 CE2 X dl a x.1 x.2).T (XMof C0 CE1 CE2 X dl a x.1 x.2).top) i ≤
      (XMof C0 CE1 CE2 X dl a x.1 x.2).n₀ i

theorem restTMSize_of (hS : SegFacts C0 CE1 CE2 X) (hFree : RestFree C0 CE1 CE2 X) (hSI : RestSI (C0 := C0) (CE1 := CE1)
    (CE2 := CE2) (X := X)) : RestTMSize C0 CE1 CE2 X := by
  intro dl hdl a ha x hx
  have ha' := aTopPt_mem ha
  have hx' : x ∈ idx C0 CE1 CE2 X dl (aTopPt C0 CE1 CE2 X dl a) := by
    rw [← hFree dl hdl a ha _ ha']; exact hx
  obtain ⟨hK', -, -⟩ := digits_of_idx hx'
  classical
  have hT' : aTopPt C0 CE1 CE2 X dl a ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA) := by
    exact (Finset.mem_filter.mp ha').1
  have e := setTies_top ha hx
  refine ⟨hSI dl hdl a ha x hx, ?_, ?_, ?_, ?_⟩
  · intro y
    rw [e]
    exact lLL_deg_le hS _ hT' x.1 hK' x.2 y
  · intro i
    show coarseA X.p (X.S C0 CE1 CE2) x.1 (uTop (X.S C0 CE1 CE2) i) - x.1.o (uTop (X.S C0 CE1 CE2) i) ≤ 2 * X.L.a
    have h1 := coarseA_upper hS x.1 (uTop (X.S C0 CE1 CE2) i)
    have h2 := b_small hS
    have hP : (1 : ℝ) ≤ ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) := by exact_mod_cast hS.P1 _
    have h0 : (0 : ℝ) ≤ (coarseA X.p (X.S C0 CE1 CE2) x.1 (uTop (X.S C0 CE1 CE2) i) : ℝ) := Nat.cast_nonneg _
    have ha0 : (0 : ℝ) ≤ X.L.a := Nat.cast_nonneg _
    have h3 : (coarseA X.p (X.S C0 CE1 CE2) x.1 (uTop (X.S C0 CE1 CE2) i) : ℝ) ≤ 2 * X.L.a := by nlinarith
    have h4 : coarseA X.p (X.S C0 CE1 CE2) x.1 (uTop (X.S C0 CE1 CE2) i) ≤ 2 * X.L.a := by exact_mod_cast h3
    omega
  ·
    rw [e, Fin.sum_univ_castSucc]
    have hs : 2 * X.s + 2 ≤ X.r := hS.hF.s_le
    have hp : ((X.r : ℝ) + 1) ^ 2 ≤ (X.p : ℝ) := hS.hF.p_ge
    have hr5 := r5 hS
    have ha0 : (0 : ℝ) ≤ X.L.a := Nat.cast_nonneg _
    have hp0 : (0 : ℝ) < (X.p : ℝ) := by nlinarith
    have hlast := lLL_deg_le hS _ hT' x.1 hK' x.2 (Fin.last (2 * X.s))
    have hone : ∀ q : Fin (2 * X.s),
        ((lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2).deg q.castSucc : ℝ) * X.p ≤ 2 * X.L.a := by
      intro q
      have hq : ((q.castSucc : Fin (2 * X.s + 1)) : ℕ) ≠ 2 * X.s := by
        have := q.2
        simp only [Fin.val_castSucc]
        omega
      have h1 := chain_wt hS _ hT' x.1 hK' q.castSucc hq
      have h2 : ((lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2).deg q.castSucc : ℝ) ≤
          ((segChain X.p (X.S C0 CE1 CE2) (aTopPt C0 CE1 CE2 X dl a) x.1).deg q.castSucc : ℝ) := by
        exact_mod_cast lLL_deg_le_chain hS _ x.1 x.2 q.castSucc
      have h3 : (X.p : ℝ) ≤ ((X.S C0 CE1 CE2).P X.p (topOf q.castSucc hq) : ℝ) := by
        exact_mod_cast p_le_P (C0 := C0) (CE1 := CE1) (CE2 := CE2) (X := X) (topOf q.castSucc hq)
      calc ((lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2).deg q.castSucc : ℝ) * X.p
          ≤ ((segChain X.p (X.S C0 CE1 CE2) (aTopPt C0 CE1 CE2 X dl a) x.1).deg q.castSucc : ℝ) *
            ((X.S C0 CE1 CE2).P X.p (topOf q.castSucc hq) : ℝ) :=
            mul_le_mul h2 h3 hp0.le (Nat.cast_nonneg _)
        _ ≤ 2 * X.L.a := h1
    have hsum : ((∑ q : Fin (2 * X.s), (lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2).deg q.castSucc : ℕ) : ℝ) *
        X.p ≤ (2 * X.s : ℕ) * (2 * X.L.a) := by
      rw [Nat.cast_sum, Finset.sum_mul]
      calc ∑ q : Fin (2 * X.s), ((lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2).deg q.castSucc : ℝ) * X.p
          ≤ ∑ _q : Fin (2 * X.s), 2 * (X.L.a : ℝ) := Finset.sum_le_sum fun q _ => hone q
        _ = (2 * X.s : ℕ) * (2 * X.L.a) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hsp : ((2 * X.s : ℕ) : ℝ) ≤ X.p := by
      have h1 : ((2 * X.s : ℕ) : ℝ) ≤ (X.r : ℝ) := by exact_mod_cast (by omega : 2 * X.s ≤ X.r)
      nlinarith
    have hsum2 : ((∑ q : Fin (2 * X.s), (lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2).deg q.castSucc : ℕ) : ℝ) ≤
        2 * X.L.a := by
      have h1 : ((2 * X.s : ℕ) : ℝ) * (2 * X.L.a) ≤ (2 * X.L.a) * X.p := by nlinarith
      exact le_of_mul_le_mul_right (hsum.trans h1) hp0
    have hsum3 : (∑ q : Fin (2 * X.s), (lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2).deg q.castSucc) ≤
        2 * X.L.a := by exact_mod_cast hsum2
    exact (Nat.add_le_add hsum3 hlast).trans (by omega)
  · exact_mod_cast hS.hF.a1

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

variable {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst}

section SI

variable (hS : SegFacts C0 CE1 CE2 X)
include hS

private theorem lLL_deg_mul_segP_le_two_mul_a_of_kept (a : Fin X.s → ℕ) (hT : a ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA))
    (b : SegBlock X.s X.r) (hK : Kept X.p X.r (X.S C0 CE1 CE2) a b) (x : Lv C0 CE1 CE2 X)
    (q : Fin (2 * X.s + 1)) (hq : (q : ℕ) ≠ 2 * X.s) :
    ((lLL C0 CE1 CE2 X a b x).deg q : ℝ) * (SegData.P X.p (X.S C0 CE1 CE2) (topOf q hq) : ℝ) ≤ 2 * X.L.a := by
  have hF := hS.hF
  have h1 := lLL_deg_le_chain hS a b x q
  obtain ⟨-, hK1, hK2, -⟩ := hK
  set v := topOf q hq with hv
  set P := SegData.P X.p (X.S C0 CE1 CE2) v with hPdef
  have hc : (segChain X.p (X.S C0 CE1 CE2) a b).deg q ≤ (X.S C0 CE1 CE2).bTop v / P ∨
      (segChain X.p (X.S C0 CE1 CE2) a b).deg q ≤ a v / P := by
    have hA : coarseA X.p (X.S C0 CE1 CE2) b v ≤ (X.S C0 CE1 CE2).bTop v / P :=
      Nat.div_le_div_right (Nat.sub_le _ _)
    have hC : coarseC X.p (X.S C0 CE1 CE2) a b v ≤ a v / P :=
      Nat.div_le_div_right (Nat.sub_le _ _)
    simp only [segChain, dif_neg hq]
    rw [← hv]
    split_ifs with h2 h3 h3
    · exact Or.inl ((hK2 v h3).2.1.trans hA)
    · exact Or.inl (((hK1 v (not_lt.mp h3)).1).trans hA)
    · exact Or.inr ((Nat.sub_le _ _).trans hC)
    · exact Or.inr hC
  have hbT : ((X.S C0 CE1 CE2).bTop v : ℝ) ≤ 2 * X.L.a := by
    have h5 := hS.bTop v
    have hb0 := hF.b0
    have hlt := hF.b_lt
    have hpm := hF.p_ge
    have hm := hF.m4
    have hm' : (4 : ℝ) ≤ X.L.m := by exact_mod_cast hm
    have hp25 : (25 : ℝ) ≤ X.L.p := by nlinarith
    nlinarith
  have haT : (a v : ℝ) ≤ 2 * X.L.a := by
    have hmem := Fintype.mem_piFinset.mp hT v
    simp only [flipOneThree.Inst.winA, Finset.mem_Icc] at hmem
    have h2 := Nat.floor_le hF.win0
    have h3 : (a v : ℝ) ≤ (⌊(X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) + X.xa⌋₊ : ℕ) := by exact_mod_cast hmem.2
    linarith [hF.win_le]
  have hfin : ∀ N : ℕ, (N : ℝ) ≤ 2 * X.L.a → (segChain X.p (X.S C0 CE1 CE2) a b).deg q ≤ N / P →
      ((lLL C0 CE1 CE2 X a b x).deg q : ℝ) * (P : ℝ) ≤ 2 * X.L.a := by
    intro N hN hd
    have h4 : (lLL C0 CE1 CE2 X a b x).deg q * P ≤ N :=
      (Nat.mul_le_mul_right P (h1.trans hd)).trans (Nat.div_mul_le_self N P)
    have h5 : (((lLL C0 CE1 CE2 X a b x).deg q * P : ℕ) : ℝ) ≤ N := by exact_mod_cast h4
    push_cast at h5
    linarith
  rcases hc with hc | hc
  · exact hfin _ hbT hc
  · exact hfin _ haT hc

theorem S_bound (a : Fin X.s → ℕ) (hT : a ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA)) (b : SegBlock X.s X.r)
    (hK : Kept X.p X.r (X.S C0 CE1 CE2) a b) (x : Lv C0 CE1 CE2 X) (i : Fin (X.S C0 CE1 CE2).t) :
    ((gT C0 CE1 CE2 X b).S (lLL C0 CE1 CE2 X a b x) i : ℝ) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) ≤
      5 / 2 * X.L.b' + (2 * X.s + 1) * (2 * X.L.a / X.p) := by
  have hF := hS.hF
  have hK' := hK
  obtain ⟨-, hK1, -, -⟩ := hK'
  set u := uTop (X.S C0 CE1 CE2) i with hu
  have hus : (u : ℕ) < X.s := u.2
  have hσu : (X.S C0 CE1 CE2).sigma ≤ (u : ℕ) := by
    simp [hu, uTop]
  have hSdef : (gT C0 CE1 CE2 X b).S (lLL C0 CE1 CE2 X a b x) i =
      ∑ q : Fin (2 * X.s + 1), if (q : ℕ) ≤ 2 * (u : ℕ) then (lLL C0 CE1 CE2 X a b x).deg q else 0 := rfl
  rw [hSdef]
  push_cast
  rw [Finset.sum_mul]
  have hm' : (4 : ℝ) ≤ X.L.m := by exact_mod_cast hF.m4
  have hpm := hF.p_ge
  have hp : (0 : ℝ) < X.p := by
    show (0 : ℝ) < X.L.p
    nlinarith
  have hb0 := hF.b0
  have hB : (0 : ℝ) ≤ 2 * X.L.a / X.p := by positivity
  have key : ∀ q : Fin (2 * X.s + 1),
      (if (q : ℕ) ≤ 2 * (u : ℕ) then ((lLL C0 CE1 CE2 X a b x).deg q : ℝ) else 0) *
          (SegData.P X.p (X.S C0 CE1 CE2) u : ℝ) ≤
        (if (q : ℕ) = 2 * (u : ℕ) then 5 / 2 * X.L.b' else 0) + 2 * X.L.a / X.p := by
    intro q
    by_cases h : (q : ℕ) ≤ 2 * (u : ℕ)
    · rw [if_pos h]
      by_cases he : (q : ℕ) = 2 * (u : ℕ)
      · rw [if_pos he]
        have h1 := lLL_deg_le_chain hS a b x q
        rw [segChain_deg_even (X.S C0 CE1 CE2) a b q u he hσu] at h1
        have hA : coarseA X.p (X.S C0 CE1 CE2) b u ≤
            (X.S C0 CE1 CE2).bTop u / SegData.P X.p (X.S C0 CE1 CE2) u :=
          Nat.div_le_div_right (Nat.sub_le _ _)
        have h4 : (lLL C0 CE1 CE2 X a b x).deg q * SegData.P X.p (X.S C0 CE1 CE2) u ≤
            (X.S C0 CE1 CE2).bTop u :=
          (Nat.mul_le_mul_right _ ((h1.trans (hK1 u hσu).1).trans hA)).trans (Nat.div_mul_le_self _ _)
        have h5 : (((lLL C0 CE1 CE2 X a b x).deg q * SegData.P X.p (X.S C0 CE1 CE2) u : ℕ) : ℝ) ≤
            (X.S C0 CE1 CE2).bTop u := by exact_mod_cast h4
        push_cast at h5
        linarith [hS.bTop u]
      · rw [if_neg he, zero_add]
        have hq : (q : ℕ) ≠ 2 * X.s := by omega
        have h2 := lLL_deg_mul_segP_le_two_mul_a_of_kept hS a hT b hK x q hq
        have hvu : topOf q hq < u := by
          rw [Fin.lt_iff_val_lt_val]
          simp only [topOf]
          omega
        have h3 := P_step (C0 := C0) (CE1 := CE1) (CE2 := CE2) (X := X) _ _ hvu
        have h3' : ((X.p : ℕ) : ℝ) * (SegData.P X.p (X.S C0 CE1 CE2) u : ℝ) ≤
            (SegData.P X.p (X.S C0 CE1 CE2) (topOf q hq) : ℝ) := by exact_mod_cast h3
        rw [le_div_iff₀ hp]
        have hd0 : (0 : ℝ) ≤ ((lLL C0 CE1 CE2 X a b x).deg q : ℝ) := Nat.cast_nonneg _
        nlinarith
    · rw [if_neg h, zero_mul]
      split_ifs <;> positivity
  calc _ ≤ ∑ q : Fin (2 * X.s + 1),
        ((if (q : ℕ) = 2 * (u : ℕ) then 5 / 2 * X.L.b' else 0) + 2 * X.L.a / X.p) :=
        Finset.sum_le_sum (fun q _ => key q)
    _ = 5 / 2 * X.L.b' + (2 * X.s + 1) * (2 * X.L.a / X.p) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Finset.sum_eq_single (⟨2 * (u : ℕ), by omega⟩ : Fin (2 * X.s + 1))]
        · simp
        · intro c _ hc
          rw [if_neg]
          intro hc'
          exact hc (Fin.ext hc')
        · intro hc
          exact absurd (Finset.mem_univ _) hc

end SI

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

variable {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst}

section N0

variable (hS : SegFacts C0 CE1 CE2 X)
include hS

theorem cast_sub_ge (w j : ℕ) : (w : ℝ) - j ≤ ((w - j : ℕ) : ℝ) := by
  rcases le_total j w with h | h
  · rw [Nat.cast_sub h]
  · rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero]
    have : (w : ℝ) ≤ j := by exact_mod_cast h
    linarith

theorem lower_bound_initial_multiplicity {dl : DCl X} {a : Fin X.s → ℕ} (ha : a ∈ cbox C0 CE1 CE2 X dl)
    {x : Σ _ : SegBlock X.s X.r, Lv C0 CE1 CE2 X} (hx : x ∈ idx C0 CE1 CE2 X dl a) (i : Fin (X.S C0 CE1 CE2).t) :
    (X.L.a : ℝ) - ((X.r : ℝ) + 1) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) - 5 / 2 * X.L.b' ≤
      ((XMof C0 CE1 CE2 X dl a x.1 x.2).n₀ i : ℝ) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) := by
  obtain ⟨hK, hdl, hlv⟩ := digits_of_idx hx
  have hK' := hK
  obtain ⟨hDig, hK1, -, -⟩ := hK'
  set u := uTop (X.S C0 CE1 CE2) i with hu
  have hσu : (X.S C0 CE1 CE2).sigma ≤ (u : ℕ) := by
    simp [hu, uTop]
  set P := SegData.P X.p (X.S C0 CE1 CE2) u with hPdef
  have hPpos : 0 < P := twoPow_pos C0 CE1 CE2 X u
  have hj : x.2.1 i ≤ x.1.o u := (((mem_lv _ _ _).mp hlv).1 i).1
  have hA : coarseA X.p (X.S C0 CE1 CE2) x.1 u ≤ (X.S C0 CE1 CE2).bTop u / P :=
    Nat.div_le_div_right (Nat.sub_le _ _)
  have hjP : x.2.1 i * P ≤ (X.S C0 CE1 CE2).bTop u :=
    (Nat.mul_le_mul_right _ ((hj.trans (hK1 u hσu).1).trans hA)).trans (Nat.div_mul_le_self _ _)
  have hry : x.1.ry = dl.2 := by rw [← hdl]
  have hne : (Nl C0 CE1 CE2 X dl x.2 i).Nonempty := (Wl_ne ha u).image _
  have hn0 : (XMof C0 CE1 CE2 X dl a x.1 x.2).n₀ i = sInf (↑(Nl C0 CE1 CE2 X dl x.2 i) : Set ℕ) := rfl
  have hmem : sInf (↑(Nl C0 CE1 CE2 X dl x.2 i) : Set ℕ) ∈ (↑(Nl C0 CE1 CE2 X dl x.2 i) : Set ℕ) :=
    Nat.sInf_mem (Finset.coe_nonempty.mpr hne)
  rw [Finset.mem_coe] at hmem
  obtain ⟨v, hv, hcm⟩ := Finset.mem_image.mp hmem
  simp only [Wl, Finset.mem_filter, flipOneThree.Inst.winA, Finset.mem_Icc] at hv
  obtain ⟨⟨hav, -⟩, hsv, hdvd⟩ := hv
  rw [← hu] at hsv hdvd
  rw [hn0, ← hcm]
  have hsum : ∑ c : Fin (X.r + 1), dl.2 u c ≤ (X.r + 1) * P := by
    calc ∑ c : Fin (X.r + 1), dl.2 u c ≤ ∑ _c : Fin (X.r + 1), P := by
          apply Finset.sum_le_sum
          intro c _
          rw [← hry]
          exact le_of_lt (hDig.1 u c).2
      _ = (X.r + 1) * P := by simp
  have hQ : (v - ∑ c : Fin (X.r + 1), dl.2 u c) / P * P = v - ∑ c : Fin (X.r + 1), dl.2 u c :=
    Nat.div_mul_cancel hdvd
  have hc1 := cast_sub_ge hS ((v - ∑ c : Fin (X.r + 1), dl.2 u c) / P) (x.2.1 i)
  have hcm' : cm C0 CE1 CE2 X dl x.2 i v = (v - ∑ c : Fin (X.r + 1), dl.2 u c) / P - x.2.1 i := rfl
  rw [hcm']
  have hQr : (((v - ∑ c : Fin (X.r + 1), dl.2 u c) / P : ℕ) : ℝ) * (P : ℝ) =
      (v : ℝ) - (∑ c : Fin (X.r + 1), dl.2 u c : ℕ) := by
    rw [← Nat.cast_sub hsv, ← Nat.cast_mul, hQ]
  have hsumR : ((∑ c : Fin (X.r + 1), dl.2 u c : ℕ) : ℝ) ≤ ((X.r : ℝ) + 1) * (P : ℝ) := by
    exact_mod_cast hsum
  have hjPR : ((x.2.1 i : ℕ) : ℝ) * (P : ℝ) ≤ 5 / 2 * X.L.b' := by
    have h1 : (((x.2.1 i * P : ℕ)) : ℝ) ≤ (X.S C0 CE1 CE2).bTop u := by exact_mod_cast hjP
    push_cast at h1
    linarith [hS.bTop u]
  have havR : (X.L.a : ℝ) ≤ v := by exact_mod_cast hav
  have hPR : (0 : ℝ) ≤ (P : ℝ) := Nat.cast_nonneg _
  nlinarith

theorem restSI_proved (hFree : RestFree C0 CE1 CE2 X) : RestSI (C0 := C0) (CE1 := CE1) (CE2 := CE2) (X := X) := by
  intro dl hdl a ha x hx i
  have hF := hS.hF
  have hinj : Function.Injective (uTop (X.S C0 CE1 CE2)) := by
    intro k k' h
    simp only [uTop, Fin.mk.injEq] at h
    exact Fin.ext (by omega)
  set n : Fin (X.S C0 CE1 CE2).t → ℕ := fun k => topA C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) k) with hn
  set a' := ovr (uTop (X.S C0 CE1 CE2)) a n with haeq
  have ha' : a' ∈ cbox C0 CE1 CE2 X dl := by
    have hb := cbox_eq C0 CE1 CE2 X dl a ha
    rw [hb]
    apply ovr_mem _ hinj
    · rw [← hb]
      exact ha
    · exact Fintype.mem_piFinset.mpr (fun k => topA_mem_Wl ha _)
  have hx' : x ∈ idx C0 CE1 CE2 X dl a' := by
    rw [← hFree dl hdl a ha a' ha']
    exact hx
  obtain ⟨hK', -, -⟩ := digits_of_idx hx'
  obtain ⟨-, hdl0, -⟩ := digits_of_idx hx
  have hry : x.1.ry = dl.2 := by rw [← hdl0]
  have hT' := (mem_cbox' ha').1
  have hSb := S_bound hS a' hT' x.1 hK' x.2 i
  have hn0 := lower_bound_initial_multiplicity hS ha hx i
  have htop : (XMof C0 CE1 CE2 X dl a x.1 x.2).top = fun k =>
      (n k - ∑ c : Fin (X.r + 1), x.1.ry (uTop (X.S C0 CE1 CE2) k) c) /
        SegData.P X.p (X.S C0 CE1 CE2) (uTop (X.S C0 CE1 CE2) k) - x.2.1 k := by
    funext k
    have hne : (Nl C0 CE1 CE2 X dl x.2 k).Nonempty := (Wl_ne ha _).image _
    have h1 := cm_top (dl := dl) x.2 k (Wl_ne ha _)
    have h2 : sInf (↑(Nl C0 CE1 CE2 X dl x.2 k) : Set ℕ) ≤ (Nl C0 CE1 CE2 X dl x.2 k).sup id := by
      have hm := Nat.sInf_mem (Finset.coe_nonempty.mpr hne)
      exact Finset.le_sup (f := id) hm
    rw [hry]
    show sInf (↑(Nl C0 CE1 CE2 X dl x.2 k) : Set ℕ) +
        1 * ((Nl C0 CE1 CE2 X dl x.2 k).sup id - sInf (↑(Nl C0 CE1 CE2 X dl x.2 k) : Set ℕ) + 1 - 1) =
      cm C0 CE1 CE2 X dl x.2 k (n k)
    rw [h1]
    omega
  have hL : (XMof C0 CE1 CE2 X dl a x.1 x.2).LL.setTies (XMof C0 CE1 CE2 X dl a x.1 x.2).T
      (XMof C0 CE1 CE2 X dl a x.1 x.2).top = lLL C0 CE1 CE2 X a' x.1 x.2 := by
    rw [htop, haeq, lLL_ovr]
    rfl
  have hP : (0 : ℝ) < (SegData.P X.p (X.S C0 CE1 CE2) (uTop (X.S C0 CE1 CE2) i) : ℝ) := by
    exact_mod_cast twoPow_pos C0 CE1 CE2 X _
  have hkP := hS.kP (uTop (X.S C0 CE1 CE2) i)
  have hm' : (4 : ℝ) ≤ X.L.m := by exact_mod_cast hF.m4
  have hsm : (2 * (X.s : ℝ) + 2) ≤ X.L.m := by exact_mod_cast hF.s_le
  have hpm := hF.p_ge
  have hp0 : (0 : ℝ) < X.p := by
    show (0 : ℝ) < X.L.p
    nlinarith
  have h48 : (4 * (X.s : ℝ) + 8) ≤ X.p := by
    show (4 * (X.s : ℝ) + 8) ≤ X.L.p
    nlinarith
  have hb'p : X.L.b' ≤ (X.L.a : ℝ) / X.p := by
    rw [le_div_iff₀ hp0]
    have := hF.b_lt
    show X.L.b' * X.L.p ≤ X.L.a
    linarith
  have ha0 : (0 : ℝ) ≤ X.L.a := Nat.cast_nonneg _
  have hsum : (2 * (X.s : ℝ) + 1) * (2 * X.L.a / X.p) + 6 * ((X.L.a : ℝ) / X.p) ≤ X.L.a := by
    calc (2 * (X.s : ℝ) + 1) * (2 * X.L.a / X.p) + 6 * ((X.L.a : ℝ) / X.p)
        = (4 * (X.s : ℝ) + 8) * ((X.L.a : ℝ) / X.p) := by ring
      _ ≤ (X.p : ℝ) * ((X.L.a : ℝ) / X.p) := mul_le_mul_of_nonneg_right h48 (by positivity)
      _ = X.L.a := by field_simp
  have hreal : ((GM.M.TieData.S (lLL C0 CE1 CE2 X a' x.1 x.2) (gT C0 CE1 CE2 X x.1) i : ℕ) : ℝ) *
        (SegData.P X.p (X.S C0 CE1 CE2) (uTop (X.S C0 CE1 CE2) i) : ℝ) ≤
      ((XMof C0 CE1 CE2 X dl a x.1 x.2).n₀ i : ℝ) *
        (SegData.P X.p (X.S C0 CE1 CE2) (uTop (X.S C0 CE1 CE2) i) : ℝ) := by
    linarith
  have hnat : GM.M.TieData.S (lLL C0 CE1 CE2 X a' x.1 x.2) (gT C0 CE1 CE2 X x.1) i ≤
      (XMof C0 CE1 CE2 X dl a x.1 x.2).n₀ i := by
    exact_mod_cast le_of_mul_le_mul_right hreal hP
  rw [hL]
  exact hnat

theorem restTMSize_proved (hFree : RestFree C0 CE1 CE2 X) : RestTMSize C0 CE1 CE2 X :=
  restTMSize_of hS hFree (restSI_proved hS hFree)

end N0

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

variable {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst}

theorem exists_low (lo ρ P : ℕ) (hP : 0 < P) (hρ : ρ ≤ lo) :
    ∃ v, lo ≤ v ∧ v + 1 ≤ lo + P ∧ ρ ≤ v ∧ P ∣ v - ρ := by
  obtain ⟨q, r, hr, hd⟩ : ∃ q r, r < P ∧ lo - ρ = P * q + r :=
    ⟨(lo - ρ) / P, (lo - ρ) % P, Nat.mod_lt _ hP, (Nat.div_add_mod _ _).symm⟩
  rcases Nat.eq_zero_or_pos r with h0 | hpos
  · refine ⟨lo, le_rfl, by omega, hρ, ⟨q, by omega⟩⟩
  · refine ⟨lo + (P - r), by omega, by omega, by omega, ⟨q + 1, ?_⟩⟩
    rw [Nat.mul_add, Nat.mul_one]
    omega

theorem exists_high (hi ρ P : ℕ) (hP : 0 < P) (hρ : ρ ≤ hi) :
    ∃ v, v ≤ hi ∧ hi + 1 ≤ v + P ∧ ρ ≤ v ∧ P ∣ v - ρ := by
  obtain ⟨q, r, hr, hd⟩ : ∃ q r, r < P ∧ hi - ρ = P * q + r :=
    ⟨(hi - ρ) / P, (hi - ρ) % P, Nat.mod_lt _ hP, (Nat.div_add_mod _ _).symm⟩
  exact ⟨hi - r, by omega, by omega, by omega, ⟨q, by omega⟩⟩

section Eps

variable (hS : SegFacts C0 CE1 CE2 X)
include hS

theorem Yl_bound (hFree : RestFree C0 CE1 CE2 X) {dl : DCl X} (hdl : dl ∈ clSet C0 CE1 CE2 X) {a : Fin X.s → ℕ}
    (ha : a ∈ cbox C0 CE1 CE2 X dl) {x : Σ _ : SegBlock X.s X.r, Lv C0 CE1 CE2 X} (hx : x ∈ idx C0 CE1 CE2 X dl a)
    (i : Fin (X.S C0 CE1 CE2).t)
    (hroom : X.L.a + 2 * (X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) ≤
      ⌊(X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) + X.xa⌋₊) :
    ((⌊(X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) + X.xa⌋₊ : ℕ) : ℝ) - X.L.a -
        ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) ≤
      ((XMof C0 CE1 CE2 X dl a x.1 x.2).Yl i : ℝ) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) := by
  set l := uTop (X.S C0 CE1 CE2) i with hl
  set P := (X.S C0 CE1 CE2).P X.p l with hP
  set σ := ∑ c : Fin (X.r + 1), dl.2 l c with hσ
  set N := ⌊(X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) + X.xa⌋₊ with hN
  have hP1 : 1 ≤ P := hS.P1 l
  have hdl' : dl ∈ digSet C0 CE1 CE2 X ×ˢ digSet C0 CE1 CE2 X := hdl
  have h2 : dl.2 ∈ digSet C0 CE1 CE2 X := (Finset.mem_product.1 hdl').2
  have hdig : ∀ c, dl.2 l c < P := fun c =>
    Finset.mem_range.1 (Fintype.mem_piFinset.1 (Fintype.mem_piFinset.1 h2 l) c)
  have hsum : σ < (X.r + 1) * P := by
    have := Finset.sum_lt_sum_of_nonempty (s := (Finset.univ : Finset (Fin (X.r + 1))))
      Finset.univ_nonempty (fun c _ => hdig c)
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] using this
  have hσA : σ ≤ X.L.a := by
    have hkP := hS.kP l
    have hkb := hS.kb
    have hsR : (σ : ℝ) < ((X.r : ℝ) + 1) * (P : ℝ) := by exact_mod_cast hsum
    have hP1R : (1 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP1
    have hr0 : (0 : ℝ) ≤ (X.r : ℝ) := Nat.cast_nonneg _
    have hb0 : (0 : ℝ) ≤ X.L.b' := by nlinarith
    have hA0 : (0 : ℝ) ≤ (X.L.a : ℝ) := Nat.cast_nonneg _
    have : (σ : ℝ) < (X.L.a : ℝ) := by nlinarith
    exact_mod_cast this.le
  obtain ⟨vlo, hlo1, hlo2, hlo3, hlo4⟩ := exists_low X.L.a σ P (by omega) hσA
  obtain ⟨vhi, hhi1, hhi2, hhi3, hhi4⟩ := exists_high N σ P (by omega) (by omega)
  have hWlo : vlo ∈ Wl C0 CE1 CE2 X dl l := by
    simp only [Wl, flipOneThree.Inst.winA, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hlo1, by omega⟩, hlo3, hlo4⟩
  have hWhi : vhi ∈ Wl C0 CE1 CE2 X dl l := by
    simp only [Wl, flipOneThree.Inst.winA, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, hhi1⟩, hhi3, hhi4⟩
  have hry : x.fst.ry = dl.2 := by
    have hx' := (Finset.mem_sigma.1 hx).1
    simp only [Finset.mem_filter] at hx'
    exact congrArg Prod.snd hx'.2
  have hall : ∀ a' ∈ cbox C0 CE1 CE2 X dl, x ∈ idx C0 CE1 CE2 X dl a' := fun a' ha' =>
    (hFree dl hdl a ha a' ha') ▸ hx
  have hroomL : LvlRoom C0 CE1 CE2 X dl x.snd := lvlRoom_of ha hry hall
  have hx1 : x.2.1 i ≤ (vlo - σ) / P := hroomL i vlo hWlo
  obtain ⟨qlo, hqlo⟩ := hlo4
  obtain ⟨qhi, hqhi⟩ := hhi4
  have hPpos : 0 < P := by omega
  have hdlo : (vlo - σ) / P = qlo := by rw [hqlo]; exact Nat.mul_div_cancel_left _ hPpos
  have hdhi : (vhi - σ) / P = qhi := by rw [hqhi]; exact Nat.mul_div_cancel_left _ hPpos
  have hmlo : cm C0 CE1 CE2 X dl x.2 i vlo ∈ Nl C0 CE1 CE2 X dl x.2 i := by
    unfold Nl; exact Finset.mem_image_of_mem _ hWlo
  have hmhi : cm C0 CE1 CE2 X dl x.2 i vhi ∈ Nl C0 CE1 CE2 X dl x.2 i := by
    unfold Nl; exact Finset.mem_image_of_mem _ hWhi
  have hinf : sInf (↑(Nl C0 CE1 CE2 X dl x.2 i) : Set ℕ) ≤ cm C0 CE1 CE2 X dl x.2 i vlo :=
    Nat.sInf_le (Finset.mem_coe.2 hmlo)
  have hsup : cm C0 CE1 CE2 X dl x.2 i vhi ≤ (Nl C0 CE1 CE2 X dl x.2 i).sup id :=
    Finset.le_sup (f := id) hmhi
  have hclo : cm C0 CE1 CE2 X dl x.2 i vlo = qlo - x.2.1 i := by
    show (vlo - σ) / P - x.2.1 i = _; rw [hdlo]
  have hchi : cm C0 CE1 CE2 X dl x.2 i vhi = qhi - x.2.1 i := by
    show (vhi - σ) / P - x.2.1 i = _; rw [hdhi]
  have hY : (XMof C0 CE1 CE2 X dl a x.1 x.2).Yl i =
      (Nl C0 CE1 CE2 X dl x.2 i).sup id - sInf (↑(Nl C0 CE1 CE2 X dl x.2 i) : Set ℕ) + 1 := rfl
  rw [hdlo] at hx1
  have hvv : vlo < vhi := by omega
  have hqq : qlo ≤ qhi := by
    by_contra hc
    push_neg at hc
    have : P * qhi < P * qlo := Nat.mul_lt_mul_of_pos_left hc hPpos
    omega
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hqq
  have hYd : d + 1 ≤ (XMof C0 CE1 CE2 X dl a x.1 x.2).Yl i := by
    rw [hY]; omega
  have hmul : (d + 1) * P ≤ (XMof C0 CE1 CE2 X dl a x.1 x.2).Yl i * P := Nat.mul_le_mul_right _ hYd
  rw [Nat.add_mul, one_mul, mul_comm d P] at hmul
  rw [Nat.mul_add] at hqhi
  have hnat : N ≤ (XMof C0 CE1 CE2 X dl a x.1 x.2).Yl i * P + X.L.a + P := by
    generalize P * qlo = u at *
    generalize P * d = w at *
    generalize (XMof C0 CE1 CE2 X dl a x.1 x.2).Yl i * P = t at *
    omega
  have hR : ((N : ℕ) : ℝ) ≤ (((XMof C0 CE1 CE2 X dl a x.1 x.2).Yl i * P + X.L.a + P : ℕ) : ℝ) := by
    exact_mod_cast hnat
  push_cast at hR
  linarith

end Eps

end Formalism.MainNotions.G.SymmetricFormBlocks

end
