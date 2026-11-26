module

public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreMain
public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreSide
public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreNonv

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CorePair
noncomputable section

open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace

namespace PositivityTheory.KReal

theorem exists_blk {p q r s : ℕ} (a b c d : List ℤ) (hd : PI.FJM.ShapeData p q r s a b c d) (u v : ℚ)
    (hu : ∀ i : Fin p, (pad a (p - a.length - b.length) b).getD i 0 = u)
    (hv : ∀ j : Fin q, (pad c (q - c.length - d.length) d).getD j 0 = v) :
    ∃ (x : Pol p q r s) (dx : ℕ), x ≠ 0 ∧ x ∈ homog (Ix p q × Ix r s) dx ∧ x ∈ Jset p q r s ∧
      ∀ a' b', sameBlock a' b' → fockAct1 p q r s (Eab a' b') x =
        (if a' = b' then (((Sum.elim (fun _ => u + cPair r s) (fun _ => v - cPair r s) a' : ℚ)) : ℂ) else 0) • x := by
  let μ : Ix p q → ℚ := Sum.elim (fun _ => u + cPair r s) (fun _ => v - cPair r s)
  have hS : JointShape p q r s μ (PI.FJM.wtOf2 p q r s a b c d) := by
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12⟩ := hd
    refine ⟨a, b, c, d, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, ?_, ?_⟩
    · funext i
      cases i with
      | inl i => simp only [shiftNu, ofBlocks, μ, Sum.elim_inl, hu]; ring
      | inr i => simp only [shiftNu, ofBlocks, μ, Sum.elim_inr, hv]; ring
    · funext i
      cases i with
      | inl i => simp only [shiftNu, PI.FJM.wtOf2, PI.FJM.sh2, Sum.elim_inl]; ring
      | inr i => simp only [shiftNu, PI.FJM.wtOf2, PI.FJM.sh2, Sum.elim_inr]; ring
  have h1 := (fock_joint_multiplicity p q r s μ _).1 hS
  have hne : hwSub (fockAct1 p q r s) μ ⊓ hwSub (fockAct2 p q r s) (PI.FJM.wtOf2 p q r s a b c d) ⊓
      Submodule.span ℂ (Jset p q r s) ≠ ⊥ := by
    intro h0
    rw [h0] at h1
    simp at h1
  obtain ⟨P, hP, hP0⟩ := (Submodule.ne_bot_iff _).1 hne
  have hPJ : P ∈ Jset p q r s := PI.FJMF.span_jset P (Submodule.mem_inf.1 hP).2
  have hP1 : P ∈ hwSub (fockAct1 p q r s) μ := (Submodule.mem_inf.1 (Submodule.mem_inf.1 hP).1).1
  have hex : ∃ e, homogeneousComponent e P ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hP0
    rw [← sum_homogeneousComponent P]
    exact Finset.sum_eq_zero fun e _ => hcon e
  obtain ⟨e, he⟩ := hex
  refine ⟨homogeneousComponent e P, e, he, homogeneousComponent_mem e P, PI.FJMF.jset_hc P hPJ e, ?_⟩
  intro a' b' hab
  refine scalar_of_hw (μ := μ) ?_ (PI.FJMF.hc_mem_hwSub1 μ P hP1 e) a' b' hab
  intro x y hxy
  cases x <;> cases y <;> simp_all [μ, sameBlock]

theorem fockAct1_Eab_inr_inl_eq_zero_of_mem_Jset {p q r : ℕ} {x : Pol p q r 0} (hx : x ∈ Jset p q r 0) (i : Fin p) (j : Fin q) :
    fockAct1 p q r 0 (Eab (.inr j) (.inl i)) x = 0 := by
  have h := ((PI.FJM.jointHarmonicsIffLaplacians p q r 0 x).1 hx).2.1 i j
  rw [PI.FJM.leftOffDiagonalActionFormula p q r 0 _ _ (by simp)]
  simp only [PI.FJM.rai1, PI.FJM.lapB, PI.FJM.dd, LinearMap.sum_apply, Fintype.sum_sum_type,
    Finset.univ_eq_empty, Finset.sum_empty, add_zero, Module.End.mul_apply, raiB, lowB, linePos] at h ⊢
  simp only [Bool.false_eq_true, if_false, if_true, LinearMap.neg_apply, Finset.sum_neg_distrib, neg_eq_zero]
  rw [← h]
  exact Finset.sum_congr rfl fun k _ => PI.FockOneDegW.Core.pd_comm _ _ _

theorem cross_y {p q s : ℕ} {y : Pol p q 0 s} (hy : y ∈ Jset p q 0 s) (i : Fin p) (j : Fin q) :
    fockAct1 p q 0 s (Eab (.inl i) (.inr j)) y = 0 := by
  have h := ((PI.FJM.jointHarmonicsIffLaplacians p q 0 s y).1 hy).1 i j
  rw [PI.FJM.leftOffDiagonalActionFormula p q 0 s _ _ (by simp)]
  simp only [PI.FJM.rai1, PI.FJM.lapA, PI.FJM.dd, LinearMap.sum_apply, Fintype.sum_sum_type,
    Finset.univ_eq_empty, Finset.sum_empty, zero_add, Module.End.mul_apply, raiB, lowB, linePos] at h ⊢
  simp only [Bool.false_eq_true, if_false, if_true, LinearMap.neg_apply, Finset.sum_neg_distrib, neg_eq_zero]
  exact h

theorem pair_of {p q r s : ℕ} (c0 u v u' v' : ℚ) (h1 : u' + cPair 0 s = c0 - (u + cPair r 0))
    (h2 : v' - cPair 0 s = c0 - (v - cPair r 0))
    (hx : ∃ (x : Pol p q r 0) (dx : ℕ), x ≠ 0 ∧ x ∈ homog (Ix p q × Ix r 0) dx ∧ x ∈ Jset p q r 0 ∧
      ∀ a' b', sameBlock a' b' → fockAct1 p q r 0 (Eab a' b') x =
        (if a' = b' then (((Sum.elim (fun _ => u + cPair r 0) (fun _ => v - cPair r 0) a' : ℚ)) : ℂ) else 0) • x)
    (hy : ∃ (x : Pol p q 0 s) (dx : ℕ), x ≠ 0 ∧ x ∈ homog (Ix p q × Ix 0 s) dx ∧ x ∈ Jset p q 0 s ∧
      ∀ a' b', sameBlock a' b' → fockAct1 p q 0 s (Eab a' b') x =
        (if a' = b' then (((Sum.elim (fun _ => u' + cPair 0 s) (fun _ => v' - cPair 0 s) a' : ℚ)) : ℂ) else 0) • x) :
    PairData p q r s (c0 : ℂ) := by
  obtain ⟨x, dx, x0, xh, xJ, xK⟩ := hx
  obtain ⟨y, dy, y0, -, yJ, yK⟩ := hy
  refine ⟨fun a => (((Sum.elim (fun _ => u + cPair r 0) (fun _ => v - cPair r 0) a : ℚ)) : ℂ), x, y, dx,
    x0, y0, xh, xK, fockAct1_Eab_inr_inl_eq_zero_of_mem_Jset xJ, fun a b hab => ?_, cross_y yJ⟩
  rw [yK a b hab, h1, h2]
  cases a <;> simp only [Sum.elim_inl, Sum.elim_inr, Rat.cast_sub]

theorem pad_l (k : ℕ) (z : ℤ) (i : Fin k) :
    (pad (List.replicate k z) (k - (List.replicate k z).length - ([] : List ℤ).length) []).getD i 0 = (z : ℚ) := by
  simp [pad, List.getD_eq_getElem?_getD]

theorem pad_r (k : ℕ) (z : ℤ) (i : Fin k) :
    (pad [] (k - ([] : List ℤ).length - (List.replicate k z).length) (List.replicate k z)).getD i 0 = (z : ℚ) := by
  simp [pad, List.getD_eq_getElem?_getD]

theorem pad_nil_getD_zero (k : ℕ) (i : Fin k) :
    (pad [] (k - ([] : List ℤ).length - ([] : List ℤ).length) []).getD i 0 = (0 : ℚ) := by
  simp [pad, List.getD_eq_getElem?_getD]

theorem pw_rep (k : ℕ) (z : ℤ) : (List.replicate k z).Pairwise (· ≥ ·) := by
  rw [List.pairwise_replicate]
  exact Or.inr le_rfl

theorem pair_pos {p q r s n m : ℕ} (hp : p ≤ r) (hq : q ≤ s) (hn : 0 < n) (hm : 0 < m) (c0 : ℚ)
    (h1 : c0 = n + cPair r s) (h2 : c0 = m - cPair r s) : PairData p q r s (c0 : ℂ) := by
  refine pair_of c0 ((n : ℤ) : ℚ) 0 0 ((m : ℤ) : ℚ) ?_ ?_
    (exists_blk (List.replicate p (n : ℤ)) [] [] [] ?_ _ _ (pad_l p _) (pad_nil_getD_zero q))
    (exists_blk [] [] (List.replicate q (m : ℤ)) [] ?_ _ _ (pad_nil_getD_zero p) (pad_l q _))
  · simp only [cPair] at *; push_cast at *; linarith
  · simp only [cPair] at *; push_cast at *; linarith
  · refine ⟨?_, by simp, by simp, by simp, pw_rep _ _, by simp, by simp, by simp, by simp, by simp,
      by simpa using hp, by simp⟩
    intro v hv; rw [List.eq_of_mem_replicate hv]; exact_mod_cast hn
  · refine ⟨by simp, ?_, by simp, by simp, by simp, by simp, pw_rep _ _, by simp, by simp, by simp,
      by simp, by simpa using hq⟩
    intro v hv; rw [List.eq_of_mem_replicate hv]; exact_mod_cast hm

theorem pair_neg {p q r s n m : ℕ} (hq : q ≤ r) (hp : p ≤ s) (hn : 0 < n) (hm : 0 < m) (c0 : ℚ)
    (h1 : c0 = -m + cPair r s) (h2 : c0 = -n - cPair r s) : PairData p q r s (c0 : ℂ) := by
  refine pair_of c0 0 ((-(n : ℤ) : ℤ) : ℚ) ((-(m : ℤ) : ℤ) : ℚ) 0 ?_ ?_
    (exists_blk [] [] [] (List.replicate q (-(n : ℤ))) ?_ _ _ (pad_nil_getD_zero p) (pad_r q _))
    (exists_blk [] (List.replicate p (-(m : ℤ))) [] [] ?_ _ _ (pad_r p _) (pad_nil_getD_zero q))
  · simp only [cPair] at *; push_cast at *; linarith
  · simp only [cPair] at *; push_cast at *; linarith
  · refine ⟨by simp, by simp, by simp, ?_, by simp, by simp, by simp, pw_rep _ _, by simp, by simp,
      by simpa using hq, by simp⟩
    intro v hv; rw [List.eq_of_mem_replicate hv]; omega
  · refine ⟨by simp, by simp, ?_, by simp, by simp, pw_rep _ _, by simp, by simp, by simp, by simp,
      by simp, by simpa using hp⟩
    intro v hv; rw [List.eq_of_mem_replicate hv]; omega

end PositivityTheory.KReal

end
end

section -- merged from Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreComb
section -- merged from Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreShape
noncomputable section

open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace

namespace PositivityTheory.KReal

theorem pad_all (a b : List ℤ) (p : ℕ) (hl : a.length + b.length ≤ p) (z : ℤ)
    (h : ∀ i : Fin p, (pad a (p - a.length - b.length) b).getD i 0 = (z : ℚ)) :
    ∀ v ∈ a ++ List.replicate (p - a.length - b.length) 0 ++ b, v = z := by
  intro v hv
  have hlen : (a ++ List.replicate (p - a.length - b.length) 0 ++ b).length = p := by
    simp only [List.length_append, List.length_replicate]
    omega
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
  have h1 := h ⟨i, hlen ▸ hi⟩
  simp only [pad, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi,
    Option.map_some, Option.getD_some] at h1
  exact_mod_cast h1

theorem pad_pos (a b : List ℤ) (p : ℕ) (hl : a.length + b.length ≤ p) (z : ℤ) (hz : 0 < z)
    (hb : ∀ v ∈ b, v < 0)
    (h : ∀ i : Fin p, (pad a (p - a.length - b.length) b).getD i 0 = (z : ℚ)) :
    a = List.replicate p z ∧ b = [] := by
  have hall := pad_all a b p hl z h
  have hb' : b = [] := by
    rcases b with _ | ⟨v, b⟩
    · rfl
    · exfalso
      have h1 := hall v (by simp)
      have h2 := hb v (by simp)
      omega
  subst hb'
  have hk : p - a.length - ([] : List ℤ).length = 0 := by
    by_contra hne
    have := hall 0 (List.mem_append.2 (Or.inl (List.mem_append.2
      (Or.inr (List.mem_replicate.2 ⟨hne, rfl⟩)))))
    omega
  refine ⟨List.eq_replicate_iff.2 ⟨?_, fun v hv => hall v (by simp [hv])⟩, rfl⟩
  simp only [List.length_nil] at hk hl
  omega

theorem pad_neg (a b : List ℤ) (p : ℕ) (hl : a.length + b.length ≤ p) (z : ℤ) (hz : z < 0)
    (ha : ∀ v ∈ a, 0 < v)
    (h : ∀ i : Fin p, (pad a (p - a.length - b.length) b).getD i 0 = (z : ℚ)) :
    a = [] ∧ b = List.replicate p z := by
  have hall := pad_all a b p hl z h
  have ha' : a = [] := by
    rcases a with _ | ⟨v, a⟩
    · rfl
    · exfalso
      have h1 := hall v (by simp)
      have h2 := ha v (by simp)
      omega
  subst ha'
  have hk : p - ([] : List ℤ).length - b.length = 0 := by
    by_contra hne
    have := hall 0 (List.mem_append.2 (Or.inl (List.mem_append.2
      (Or.inr (List.mem_replicate.2 ⟨hne, rfl⟩)))))
    omega
  refine ⟨rfl, List.eq_replicate_iff.2 ⟨?_, fun v hv => hall v (by simp [hv])⟩⟩
  simp only [List.length_nil] at hk hl
  omega

theorem getD_pad_left (p k i : ℕ) (z : ℤ) :
    (pad (List.replicate p z) k []).getD i 0 = if i < p then (z : ℚ) else 0 := by
  simp only [pad, List.append_nil, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_append, List.getElem?_replicate, List.length_replicate]
  split_ifs <;> simp_all <;> omega

theorem getD_pad_right (q r i : ℕ) (z : ℤ) (hq : q ≤ r) (hi : i < r) :
    (pad [] (r - q) (List.replicate q z)).getD i 0 = if r ≤ i + q then (z : ℚ) else 0 := by
  simp only [pad, List.nil_append, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_append, List.getElem?_replicate, List.length_replicate]
  split_ifs <;> simp_all <;> omega

theorem shift_pos_eq (p q r s n m : ℕ) :
    shiftNu (cPair p q) (laPos p q r s n m) =
      ofBlocks (pad (List.replicate p (n : ℤ)) (r - p) []) (pad (List.replicate q (m : ℤ)) (s - q) []) := by
  funext x
  rcases x with k | l
  · simp only [shiftNu, laPos, ofBlocks, getD_pad_left]
    split_ifs <;> push_cast <;> ring
  · simp only [shiftNu, laPos, ofBlocks, getD_pad_left]
    split_ifs <;> push_cast <;> ring

theorem shift_neg_eq (p q r s n m : ℕ) (hq : q ≤ r) (hp : p ≤ s) :
    shiftNu (cPair p q) (laNeg p q r s n m) =
      ofBlocks (pad [] (r - q) (List.replicate q (-(n : ℤ)))) (pad [] (s - p) (List.replicate p (-(m : ℤ)))) := by
  funext x
  rcases x with k | l
  · simp only [shiftNu, laNeg, ofBlocks, getD_pad_right q r k _ hq k.isLt]
    split_ifs <;> push_cast <;> ring
  · simp only [shiftNu, laNeg, ofBlocks, getD_pad_right p s l _ hp l.isLt]
    split_ifs <;> push_cast <;> ring

theorem shiftNu_inj {r s : ℕ} (c : ℚ) {μ ν : Ix r s → ℚ} (h : shiftNu c μ = shiftNu c ν) : μ = ν := by
  funext x
  have := congrFun h x
  rcases x with k | l <;> simp only [shiftNu] at this <;> linarith

theorem shape_pos {p q r s n m : ℕ} (hp : p ≤ r) (hq : q ≤ s) (hn : 0 < n) (hm : 0 < m) (c0 : ℚ)
    (h1 : c0 = n + cPair r s) (h2 : c0 = m - cPair r s) :
    JointShape p q r s (fun _ => c0) (laPos p q r s n m) ∧
      ∀ ν, JointShape p q r s (fun _ => c0) ν → ν = laPos p q r s n m := by
  have hn' : (0 : ℤ) < (n : ℤ) := by exact_mod_cast hn
  have hm' : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm
  refine ⟨⟨List.replicate p (n : ℤ), [], List.replicate q (m : ℤ), [], ?_⟩, ?_⟩
  · refine ⟨fun v hv => (List.eq_of_mem_replicate hv) ▸ hn', fun v hv => (List.eq_of_mem_replicate hv) ▸ hm',
      fun v hv => by simp at hv, fun v hv => by simp at hv,
      List.pairwise_replicate.2 (Or.inr le_rfl), List.Pairwise.nil,
      List.pairwise_replicate.2 (Or.inr le_rfl), List.Pairwise.nil, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · simp
    · simpa using hp
    · simpa using hq
    · funext x
      rcases x with i | j
      · simp only [shiftNu, ofBlocks, List.length_replicate, List.length_nil, Nat.sub_self,
          Nat.zero_sub, getD_pad_left, i.isLt, if_true]
        rw [h1]; push_cast; ring
      · simp only [shiftNu, ofBlocks, List.length_replicate, List.length_nil, Nat.sub_self,
          Nat.zero_sub, getD_pad_left, j.isLt, if_true]
        rw [h2]; push_cast; ring
    · simp only [List.length_replicate, List.length_nil, Nat.sub_zero]
      exact shift_pos_eq p q r s n m
  · rintro ν ⟨a, b, c, d, ha, hc, hb, hd, -, -, -, -, hab, hcd, -, -, hs1, hs2⟩
    have hA := pad_pos a b p hab (n : ℤ) hn' hb (fun i => by
      have hx := congrFun hs1 (Sum.inl i)
      simp only [shiftNu, ofBlocks] at hx
      rw [← hx, h1]; push_cast; ring)
    have hC := pad_pos c d q hcd (m : ℤ) hm' hd (fun j => by
      have hx := congrFun hs1 (Sum.inr j)
      simp only [shiftNu, ofBlocks] at hx
      rw [← hx, h2]; push_cast; ring)
    obtain ⟨rfl, rfl⟩ := hA
    obtain ⟨rfl, rfl⟩ := hC
    apply shiftNu_inj (cPair p q)
    rw [hs2, shift_pos_eq]
    simp only [List.length_replicate, List.length_nil, Nat.sub_zero]

theorem shape_neg {p q r s n m : ℕ} (hq : q ≤ r) (hp : p ≤ s) (hn : 0 < n) (hm : 0 < m) (c0 : ℚ)
    (h1 : c0 = -m + cPair r s) (h2 : c0 = -n - cPair r s) :
    JointShape p q r s (fun _ => c0) (laNeg p q r s n m) ∧
      ∀ ν, JointShape p q r s (fun _ => c0) ν → ν = laNeg p q r s n m := by
  have hn' : (-(n : ℤ)) < 0 := by
    have : (0 : ℤ) < (n : ℤ) := by exact_mod_cast hn
    omega
  have hm' : (-(m : ℤ)) < 0 := by
    have : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm
    omega
  refine ⟨⟨[], List.replicate p (-(m : ℤ)), [], List.replicate q (-(n : ℤ)), ?_⟩, ?_⟩
  · refine ⟨fun v hv => by simp at hv, fun v hv => by simp at hv,
      fun v hv => (List.eq_of_mem_replicate hv) ▸ hm', fun v hv => (List.eq_of_mem_replicate hv) ▸ hn',
      List.Pairwise.nil, List.pairwise_replicate.2 (Or.inr le_rfl),
      List.Pairwise.nil, List.pairwise_replicate.2 (Or.inr le_rfl), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · simp
    · simpa using hq
    · simpa using hp
    · funext x
      rcases x with i | j
      · simp only [shiftNu, ofBlocks, List.length_replicate, List.length_nil, Nat.sub_self,
          Nat.sub_zero]
        have e := getD_pad_right p p i (-(m : ℤ)) le_rfl i.isLt
        rw [Nat.sub_self, if_pos (by omega)] at e
        rw [e, h1]; push_cast; ring
      · simp only [shiftNu, ofBlocks, List.length_replicate, List.length_nil, Nat.sub_self,
          Nat.sub_zero]
        have e := getD_pad_right q q j (-(n : ℤ)) le_rfl j.isLt
        rw [Nat.sub_self, if_pos (by omega)] at e
        rw [e, h2]; push_cast; ring
    · simp only [List.length_replicate, List.length_nil, Nat.sub_zero]
      exact shift_neg_eq p q r s n m hq hp
  · rintro ν ⟨a, b, c, d, ha, hc, hb, hd, -, -, -, -, hab, hcd, -, -, hs1, hs2⟩
    have hA := pad_neg a b p hab (-(m : ℤ)) hm' ha (fun i => by
      have hx := congrFun hs1 (Sum.inl i)
      simp only [shiftNu, ofBlocks] at hx
      rw [← hx, h1]; push_cast; ring)
    have hC := pad_neg c d q hcd (-(n : ℤ)) hn' hc (fun j => by
      have hx := congrFun hs1 (Sum.inr j)
      simp only [shiftNu, ofBlocks] at hx
      rw [← hx, h2]; push_cast; ring)
    obtain ⟨rfl, rfl⟩ := hA
    obtain ⟨rfl, rfl⟩ := hC
    apply shiftNu_inj (cPair p q)
    rw [hs2, shift_neg_eq p q r s n m hq hp]
    simp only [List.length_replicate, List.length_nil, Nat.sub_zero]

end PositivityTheory.KReal

end
end

section -- merged from Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreCasW
noncomputable section

open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace

namespace PositivityTheory.KReal

def rho2 {r s : ℕ} : Ix r s → ℚ
  | .inl k => (r : ℚ) - 1 - 2 * (k : ℕ)
  | .inr l => (s : ℚ) - 1 - 2 * (l : ℕ)

theorem cw_cnt_lt {n : ℕ} (i : Fin n) (c : ℚ) :
    ∑ j : Fin n, (if i < j then c else 0) = ((n : ℚ) - 1 - (i : ℕ)) * c := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
  have h := i.2
  rw [Nat.sub_sub, Nat.cast_sub (by omega)]
  push_cast
  ring

theorem cw_cnt_gt {n : ℕ} (j : Fin n) (c : ℚ) :
    ∑ i : Fin n, (if i < j then c else 0) = ((j : ℕ) : ℚ) * c := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, Finset.filter_gt_eq_Iio, Fin.card_Iio]

theorem cw_blk {n : ℕ} (f : Fin n → ℚ) :
    ∑ i, ∑ j, (if i < j then f i - f j else 0) = ∑ i : Fin n, ((n : ℚ) - 1 - 2 * (i : ℕ)) * f i := by
  have e : ∀ i j : Fin n, (if i < j then f i - f j else 0) = (if i < j then f i else 0) - (if i < j then f j else 0) := by
    intro i j
    split_ifs <;> ring
  simp_rw [e, Finset.sum_sub_distrib, cw_cnt_lt]
  rw [Finset.sum_comm (f := fun i j => if i < j then f j else 0)]
  simp_rw [cw_cnt_gt]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

theorem cw_two {ι : Type} [Fintype ι] [DecidableEq ι] (G H : ι → ℚ) {a b : ι} (hab : a ≠ b)
    (h : ∀ x, x ≠ a → x ≠ b → G x = H x) : ∑ x, G x = ∑ x, H x + (G b - H b) + (G a - H a) := by
  have key : ∑ x, (G x - H x) = (G a - H a) + (G b - H b) :=
    Fintype.sum_eq_add a b hab (fun x hx => by rw [h x hx.1 hx.2, sub_self])
  rw [Finset.sum_sub_distrib] at key
  linarith

theorem cw_root {r s : ℕ} {ν La : Ix r s → ℚ} {a b : Ix r s} (hab : a ≠ b) (h : RootTo ν a b La) :
    ν a = La a - 1 ∧ ν b = La b + 1 ∧ ∀ x, x ≠ a → x ≠ b → ν x = La x := by
  refine ⟨?_, ?_, ?_⟩
  · have := h a
    rw [if_pos rfl, if_neg hab] at this
    linarith
  · have := h b
    rw [if_neg (Ne.symm hab), if_pos rfl] at this
    linarith
  · intro x hxa hxb
    have := h x
    rw [if_neg hxa, if_neg hxb] at this
    linarith

theorem cw_init {r p : ℕ} (hp : p ≤ r) (c : ℚ) :
    ∑ k : Fin r, (if (k : ℕ) < p then c else 0) = p * c := by
  rw [Fin.sum_univ_eq_sum_range (fun k => if k < p then c else 0) r, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  have e : (Finset.range r).filter (fun k => k < p) = Finset.range p := by
    ext k
    simp
    omega
  rw [e, Finset.card_range]

theorem cw_fin {r q : ℕ} (hq : q ≤ r) (c : ℚ) :
    ∑ k : Fin r, (if r ≤ (k : ℕ) + q then c else 0) = q * c := by
  rw [Fin.sum_univ_eq_sum_range (fun k => if r ≤ k + q then c else 0) r, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  have e : (Finset.range r).filter (fun k => r ≤ k + q) = Finset.Ico (r - q) r := by
    ext k
    simp
    omega
  rw [e, Nat.card_Ico, show r - (r - q) = q by omega]

theorem casW_eq {r s : ℕ} (μ : Ix r s → ℚ) : casW μ = ∑ x, μ x ^ 2 + ∑ x, rho2 x * μ x := by
  unfold casW
  congr 1
  simp only [Fintype.sum_sum_type, posC, rho2]
  simp only [if_false, ite_false, Finset.sum_const_zero, add_zero, zero_add]
  rw [cw_blk, cw_blk]

theorem casW_root {r s : ℕ} {ν La : Ix r s → ℚ} {a b : Ix r s} (hab : a ≠ b) (h : RootTo ν a b La) :
    casW ν = casW La + 2 * (La b - La a) + 2 + (rho2 b - rho2 a) := by
  obtain ⟨ha, hb, hx⟩ := cw_root hab h
  rw [casW_eq, casW_eq, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  have key := cw_two (fun x => ν x ^ 2 + rho2 x * ν x) (fun x => La x ^ 2 + rho2 x * La x) hab
    (fun x h1 h2 => by simp only [hx x h1 h2])
  simp only [ha, hb] at key
  linear_combination key

private theorem shiftNu_sub_lemma {r s : ℕ} (c : ℚ) (μ μ' : Ix r s → ℚ) (x : Ix r s) :
    shiftNu c μ x = shiftNu c μ' x + (μ x - μ' x) := by
  cases x <;> simp only [shiftNu] <;> ring

theorem degW_root {r s : ℕ} (c : ℚ) {ν La : Ix r s → ℚ} {a b : Ix r s} (hab : a ≠ b) (h : RootTo ν a b La) :
    degW c ν = degW c La + (|shiftNu c La b + 1| - |shiftNu c La b|) + (|shiftNu c La a - 1| - |shiftNu c La a|) := by
  obtain ⟨ha, hb, hx⟩ := cw_root hab h
  have key := cw_two (fun x => |shiftNu c ν x|) (fun x => |shiftNu c La x|) hab
    (fun x h1 h2 => by
      show |shiftNu c ν x| = |shiftNu c La x|
      rw [shiftNu_sub_lemma c ν La x, hx x h1 h2, sub_self, add_zero])
  have e1 : shiftNu c ν b = shiftNu c La b + 1 := by
    rw [shiftNu_sub_lemma c ν La b, hb]
    ring
  have e2 : shiftNu c ν a = shiftNu c La a - 1 := by
    rw [shiftNu_sub_lemma c ν La a, ha]
    ring
  simp only [e1, e2] at key
  unfold degW
  exact key

theorem degW_laPos {p q r s n m : ℕ} (hp : p ≤ r) (hq : q ≤ s) :
    degW (cPair p q) (laPos p q r s n m) = p * n + q * m := by
  unfold degW
  rw [Fintype.sum_sum_type]
  simp only [shiftNu, laPos, add_sub_cancel_right, sub_add_cancel]
  have e : ∀ (P : Prop) [Decidable P] (t : ℕ), |(if P then (t : ℚ) else 0)| = if P then (t : ℚ) else 0 := by
    intro P _ t
    split_ifs <;> simp
  simp only [e]
  rw [cw_init hp, cw_init hq]

theorem degW_laNeg {p q r s n m : ℕ} (hq : q ≤ r) (hp : p ≤ s) :
    degW (cPair p q) (laNeg p q r s n m) = q * n + p * m := by
  unfold degW
  rw [Fintype.sum_sum_type]
  simp only [shiftNu, laNeg, add_sub_cancel_right, sub_add_cancel]
  have e : ∀ (P : Prop) [Decidable P] (t : ℕ), |(if P then -(t : ℚ) else 0)| = if P then (t : ℚ) else 0 := by
    intro P _ t
    split_ifs <;> simp
  simp only [e]
  rw [cw_fin hq, cw_fin hp]

theorem degW_const {p q : ℕ} (c c0 : ℚ) :
    degW c (fun _ : Ix p q => c0) = p * |c0 - c| + q * |c0 + c| := by
  unfold degW
  simp [Fintype.sum_sum_type, shiftNu]

end PositivityTheory.KReal

end
end

noncomputable section

open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace

namespace PositivityTheory.KReal

theorem top_idx {N : ℕ} (f g : Fin N → ℚ) (i : Fin N) (hdom : ∀ i', i' < i → g i ≤ g i')
    (hg : g i = f i + 1) (hg' : ∀ i', i' ≠ i → g i' = f i') (hf : ∀ i', i' < i → f i' = f i) :
    (i : ℕ) = 0 := by
  by_contra hne
  have hpos : 0 < (i : ℕ) := Nat.pos_of_ne_zero hne
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have h0 : (⟨0, hN⟩ : Fin N) < i := by
    rw [Fin.lt_def]
    exact hpos
  have e1 := hdom _ h0
  have e2 := hg' ⟨0, hN⟩ (ne_of_lt h0)
  have e3 := hf _ h0
  linarith

theorem bot_idx {N : ℕ} (f g : Fin N → ℚ) (j : Fin N) (hdom : ∀ j', j < j' → g j' ≤ g j)
    (hg : g j = f j - 1) (hg' : ∀ j', j' ≠ j → g j' = f j') (hf : ∀ j', j < j' → f j' = f j) :
    (j : ℕ) + 1 = N := by
  by_contra hne
  have hlt : (j : ℕ) + 1 < N := by
    have := j.isLt
    omega
  have h0 : j < (⟨(j : ℕ) + 1, hlt⟩ : Fin N) := by
    rw [Fin.lt_def]
    exact Nat.lt_succ_self _
  have e1 := hdom _ h0
  have e2 := hg' ⟨(j : ℕ) + 1, hlt⟩ (ne_of_gt h0)
  have e3 := hf _ h0
  linarith

theorem cas_lt {r s : ℕ} {ν La : Ix r s → ℚ} {a b : Ix r s} (hab : a ≠ b) (h : RootTo ν a b La) (τ : ℚ)
    (hlt : (r : ℚ) + s < 2 * (La b - La a) + 2 + (rho2 b - rho2 a)) :
    casW (fun x => La x + τ) + ((r : ℚ) + s) < casW (fun x => ν x + τ) := by
  have h' : RootTo (fun x => ν x + τ) a b (fun x => La x + τ) := fun x => by
    have := h x
    simp only
    linarith
  rw [casW_root hab h']
  linarith

theorem abs_up (x : ℚ) : |x + 1| - |x| ≤ 1 := by
  have := abs_add_le x 1
  rw [abs_one] at this
  linarith

theorem abs_down (x : ℚ) : |x - 1| - |x| ≤ 1 := by
  have h := abs_add_le x (-1)
  rw [abs_neg, abs_one, ← sub_eq_add_neg] at h
  linarith

theorem abs_pos_down {m : ℕ} (hm : 0 < m) : |(m : ℚ) - 1| - |(m : ℚ)| = -1 := by
  have h1 : (1 : ℚ) ≤ m := by exact_mod_cast hm
  rw [abs_of_nonneg (by linarith : (0 : ℚ) ≤ (m : ℚ) - 1), abs_of_nonneg (by linarith : (0 : ℚ) ≤ (m : ℚ))]
  ring

theorem abs_neg_up {m : ℕ} (hm : 0 < m) : |-(m : ℚ) + 1| - |-(m : ℚ)| = -1 := by
  have : (1 : ℚ) ≤ m := by exact_mod_cast hm
  rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
  ring

theorem extreme {r s : ℕ} {ν La : Ix r s → ℚ} (hD : Dom ν) :
    (∀ (i : Fin r) (j : Fin s), RootTo ν (.inr j) (.inl i) La →
      (∀ i', i' < i → La (.inl i') = La (.inl i)) → (∀ j', j < j' → La (.inr j') = La (.inr j)) →
      0 < La (.inl i) - La (.inr j) →
      (r : ℚ) + s < 2 * (La (.inl i) - La (.inr j)) + 2 + (rho2 (.inl i : Ix r s) - rho2 (.inr j : Ix r s))) ∧
    (∀ (i : Fin r) (j : Fin s), RootTo ν (.inl i) (.inr j) La →
      (∀ j', j' < j → La (.inr j') = La (.inr j)) → (∀ i', i < i' → La (.inl i') = La (.inl i)) →
      0 < La (.inr j) - La (.inl i) →
      (r : ℚ) + s < 2 * (La (.inr j) - La (.inl i)) + 2 + (rho2 (.inr j : Ix r s) - rho2 (.inl i : Ix r s))) := by
  constructor
  · intro i j hR hi hj hpos
    have hne : (Sum.inr j : Ix r s) ≠ Sum.inl i := Sum.inr_ne_inl
    obtain ⟨ea, eb, eo⟩ := cw_root hne hR
    have h0 : (i : ℕ) = 0 := by
      refine top_idx (fun k => La (.inl k)) (fun k => ν (.inl k)) i ?_ eb ?_ hi
      · intro i' hi'
        exact hD (.inl i') (.inl i) hi'
      · intro i' hi'
        exact eo _ Sum.inl_ne_inr (fun e => hi' (Sum.inl_injective e))
    have h1 : (j : ℕ) + 1 = s := by
      refine bot_idx (fun k => La (.inr k)) (fun k => ν (.inr k)) j ?_ ea ?_ hj
      · intro j' hj'
        exact hD (.inr j) (.inr j') hj'
      · intro j' hj'
        exact eo _ (fun e => hj' (Sum.inr_injective e)) Sum.inr_ne_inl
    have h0' : ((i : ℕ) : ℚ) = 0 := by exact_mod_cast h0
    have h1' : ((j : ℕ) : ℚ) + 1 = s := by exact_mod_cast h1
    simp only [rho2]
    linarith
  · intro i j hR hj hi hpos
    have hne : (Sum.inl i : Ix r s) ≠ Sum.inr j := Sum.inl_ne_inr
    obtain ⟨ea, eb, eo⟩ := cw_root hne hR
    have h0 : (j : ℕ) = 0 := by
      refine top_idx (fun k => La (.inr k)) (fun k => ν (.inr k)) j ?_ eb ?_ hj
      · intro j' hj'
        exact hD (.inr j') (.inr j) hj'
      · intro j' hj'
        exact eo _ Sum.inr_ne_inl (fun e => hj' (Sum.inr_injective e))
    have h1 : (i : ℕ) + 1 = r := by
      refine bot_idx (fun k => La (.inl k)) (fun k => ν (.inl k)) i ?_ ea ?_ hi
      · intro i' hi'
        exact hD (.inl i) (.inl i') hi'
      · intro i' hi'
        exact eo _ (fun e => hi' (Sum.inl_injective e)) Sum.inl_ne_inr
    have h0' : ((j : ℕ) : ℚ) = 0 := by exact_mod_cast h0
    have h1' : ((i : ℕ) : ℚ) + 1 = r := by exact_mod_cast h1
    simp only [rho2]
    linarith

theorem comb_pos {p q r s n m : ℕ} (hp : p ≤ r) (hq : q ≤ s) (hn : 0 < n) (hm : 0 < m) (c0 τ : ℚ)
    (h1 : c0 = n + cPair r s) (h2 : c0 = m - cPair r s)
    (w1 : (0 : ℚ) < n + 2 * cPair p q) (w2 : (0 : ℚ) < m - 2 * cPair p q) :
    CombOK p q c0 τ (laPos p q r s n m) := by
  obtain ⟨hs, hu⟩ := shape_pos hp hq hn hm c0 h1 h2
  refine ⟨hs, hu, ?_⟩
  intro ν a b hab hR hD hS hdeg
  have hne : a ≠ b := by
    rintro rfl
    rcases a with k | l <;> exact hab trivial
  apply cas_lt hne hR
  have hdr := degW_root (cPair p q) hne hR
  rw [degW_laPos hp hq] at hdr
  have e1 : c0 - cPair r s = n := by linarith
  have e2 : c0 + cPair r s = m := by linarith
  rw [degW_const, e1, e2, Nat.abs_cast, Nat.abs_cast] at hdeg
  have hA := abs_up (shiftNu (cPair p q) (laPos p q r s n m) b)
  have hB := abs_down (shiftNu (cPair p q) (laPos p q r s n m) a)
  have hBeq : |shiftNu (cPair p q) (laPos p q r s n m) a - 1| -
      |shiftNu (cPair p q) (laPos p q r s n m) a| = 1 := by
    linarith
  obtain ⟨ea, eb, eo⟩ := cw_root hne hR
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  have hm' : (0 : ℚ) < m := by exact_mod_cast hm
  rcases a with k | l <;> rcases b with k' | l'
  · exact absurd trivial hab
  · have sa : shiftNu (cPair p q) (laPos p q r s n m) (Sum.inl k) =
        (if (k : ℕ) < p then (n : ℚ) else 0) := by
      show (if (k : ℕ) < p then (n : ℚ) else 0) + cPair p q - cPair p q = _
      ring
    have hk : p ≤ (k : ℕ) := by
      by_contra hk
      push_neg at hk
      rw [sa, if_pos hk, abs_pos_down hn] at hBeq
      norm_num at hBeq
    have hl : (l' : ℕ) < q := by
      by_contra hl
      push_neg at hl
      have h5 : ν (Sum.inr l') + cPair p q ≤ 0 := hS.2.1 l' hl
      have e : ν (Sum.inr l') = (if (l' : ℕ) < q then (m : ℚ) else 0) - cPair p q + 1 := eb
      rw [if_neg (not_lt.mpr hl)] at e
      linarith
    refine (extreme hD).2 k l' hR ?_ ?_ ?_
    · intro j' hj'
      have hj'' : (j' : ℕ) < q := lt_trans (Fin.lt_def.mp hj') hl
      show (if (j' : ℕ) < q then (m : ℚ) else 0) - cPair p q =
        (if (l' : ℕ) < q then (m : ℚ) else 0) - cPair p q
      rw [if_pos hj'', if_pos hl]
    · intro i' hi'
      have hi'' : ¬ ((i' : ℕ) < p) := not_lt.mpr (le_trans hk (le_of_lt (Fin.lt_def.mp hi')))
      show (if (i' : ℕ) < p then (n : ℚ) else 0) + cPair p q =
        (if (k : ℕ) < p then (n : ℚ) else 0) + cPair p q
      rw [if_neg hi'', if_neg (not_lt.mpr hk)]
    · show (0 : ℚ) < ((if (l' : ℕ) < q then (m : ℚ) else 0) - cPair p q) -
        ((if (k : ℕ) < p then (n : ℚ) else 0) + cPair p q)
      rw [if_pos hl, if_neg (not_lt.mpr hk)]
      linarith
  · have sa : shiftNu (cPair p q) (laPos p q r s n m) (Sum.inr l) =
        (if (l : ℕ) < q then (m : ℚ) else 0) := by
      show (if (l : ℕ) < q then (m : ℚ) else 0) - cPair p q + cPair p q = _
      ring
    have hl : q ≤ (l : ℕ) := by
      by_contra hl
      push_neg at hl
      rw [sa, if_pos hl, abs_pos_down hm] at hBeq
      norm_num at hBeq
    have hk : (k' : ℕ) < p := by
      by_contra hk
      push_neg at hk
      have h5 : ν (Sum.inl k') - cPair p q ≤ 0 := hS.1 k' hk
      have e : ν (Sum.inl k') = (if (k' : ℕ) < p then (n : ℚ) else 0) + cPair p q + 1 := eb
      rw [if_neg (not_lt.mpr hk)] at e
      linarith
    refine (extreme hD).1 k' l hR ?_ ?_ ?_
    · intro i' hi'
      have hi'' : (i' : ℕ) < p := lt_trans (Fin.lt_def.mp hi') hk
      show (if (i' : ℕ) < p then (n : ℚ) else 0) + cPair p q =
        (if (k' : ℕ) < p then (n : ℚ) else 0) + cPair p q
      rw [if_pos hi'', if_pos hk]
    · intro j' hj'
      have hj'' : ¬ ((j' : ℕ) < q) := not_lt.mpr (le_trans hl (le_of_lt (Fin.lt_def.mp hj')))
      show (if (j' : ℕ) < q then (m : ℚ) else 0) - cPair p q =
        (if (l : ℕ) < q then (m : ℚ) else 0) - cPair p q
      rw [if_neg hj'', if_neg (not_lt.mpr hl)]
    · show (0 : ℚ) < ((if (k' : ℕ) < p then (n : ℚ) else 0) + cPair p q) -
        ((if (l : ℕ) < q then (m : ℚ) else 0) - cPair p q)
      rw [if_pos hk, if_neg (not_lt.mpr hl)]
      linarith
  · exact absurd trivial hab

theorem comb_neg {p q r s n m : ℕ} (hq : q ≤ r) (hp : p ≤ s) (hn : 0 < n) (hm : 0 < m) (c0 τ : ℚ)
    (h1 : c0 = -m + cPair r s) (h2 : c0 = -n - cPair r s)
    (w1 : (0 : ℚ) < m + 2 * cPair p q) (w2 : (0 : ℚ) < n - 2 * cPair p q) :
    CombOK p q c0 τ (laNeg p q r s n m) := by
  obtain ⟨hs, hu⟩ := shape_neg hq hp hn hm c0 h1 h2
  refine ⟨hs, hu, ?_⟩
  intro ν a b hab hR hD hS hdeg
  have hne : a ≠ b := by
    rintro rfl
    rcases a with k | l <;> exact hab trivial
  apply cas_lt hne hR
  have hdr := degW_root (cPair p q) hne hR
  rw [degW_laNeg hq hp] at hdr
  have e1 : c0 - cPair r s = -(m : ℚ) := by linarith
  have e2 : c0 + cPair r s = -(n : ℚ) := by linarith
  rw [degW_const, e1, e2, abs_neg, abs_neg, Nat.abs_cast, Nat.abs_cast] at hdeg
  have hA := abs_up (shiftNu (cPair p q) (laNeg p q r s n m) b)
  have hB := abs_down (shiftNu (cPair p q) (laNeg p q r s n m) a)
  have hAeq : |shiftNu (cPair p q) (laNeg p q r s n m) b + 1| -
      |shiftNu (cPair p q) (laNeg p q r s n m) b| = 1 := by
    linarith
  obtain ⟨ea, eb, eo⟩ := cw_root hne hR
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  have hm' : (0 : ℚ) < m := by exact_mod_cast hm
  rcases a with k | l <;> rcases b with k' | l'
  · exact absurd trivial hab
  · have sb : shiftNu (cPair p q) (laNeg p q r s n m) (Sum.inr l') =
        (if s ≤ (l' : ℕ) + p then -(m : ℚ) else 0) := by
      show (if s ≤ (l' : ℕ) + p then -(m : ℚ) else 0) - cPair p q + cPair p q = _
      ring
    have hl : ¬ (s ≤ (l' : ℕ) + p) := by
      intro hl
      rw [sb, if_pos hl, abs_neg_up hm] at hAeq
      norm_num at hAeq
    have hk : r ≤ (k : ℕ) + q := by
      by_contra hk
      push_neg at hk
      have h5 : 0 ≤ ν (Sum.inl k) - cPair p q := hS.2.2.1 k hk
      have e : ν (Sum.inl k) = (if r ≤ (k : ℕ) + q then -(n : ℚ) else 0) + cPair p q - 1 := ea
      rw [if_neg (not_le.mpr hk)] at e
      linarith
    refine (extreme hD).2 k l' hR ?_ ?_ ?_
    · intro j' hj'
      have hj'' : ¬ (s ≤ (j' : ℕ) + p) := by
        have := Fin.lt_def.mp hj'
        omega
      show (if s ≤ (j' : ℕ) + p then -(m : ℚ) else 0) - cPair p q =
        (if s ≤ (l' : ℕ) + p then -(m : ℚ) else 0) - cPair p q
      rw [if_neg hj'', if_neg hl]
    · intro i' hi'
      have hi'' : r ≤ (i' : ℕ) + q := by
        have := Fin.lt_def.mp hi'
        omega
      show (if r ≤ (i' : ℕ) + q then -(n : ℚ) else 0) + cPair p q =
        (if r ≤ (k : ℕ) + q then -(n : ℚ) else 0) + cPair p q
      rw [if_pos hi'', if_pos hk]
    · show (0 : ℚ) < ((if s ≤ (l' : ℕ) + p then -(m : ℚ) else 0) - cPair p q) -
        ((if r ≤ (k : ℕ) + q then -(n : ℚ) else 0) + cPair p q)
      rw [if_neg hl, if_pos hk]
      linarith
  · have sb : shiftNu (cPair p q) (laNeg p q r s n m) (Sum.inl k') =
        (if r ≤ (k' : ℕ) + q then -(n : ℚ) else 0) := by
      show (if r ≤ (k' : ℕ) + q then -(n : ℚ) else 0) + cPair p q - cPair p q = _
      ring
    have hk : ¬ (r ≤ (k' : ℕ) + q) := by
      intro hk
      rw [sb, if_pos hk, abs_neg_up hn] at hAeq
      norm_num at hAeq
    have hl : s ≤ (l : ℕ) + p := by
      by_contra hl
      push_neg at hl
      have h5 : 0 ≤ ν (Sum.inr l) + cPair p q := hS.2.2.2 l hl
      have e : ν (Sum.inr l) = (if s ≤ (l : ℕ) + p then -(m : ℚ) else 0) - cPair p q - 1 := ea
      rw [if_neg (not_le.mpr hl)] at e
      linarith
    refine (extreme hD).1 k' l hR ?_ ?_ ?_
    · intro i' hi'
      have hi'' : ¬ (r ≤ (i' : ℕ) + q) := by
        have := Fin.lt_def.mp hi'
        omega
      show (if r ≤ (i' : ℕ) + q then -(n : ℚ) else 0) + cPair p q =
        (if r ≤ (k' : ℕ) + q then -(n : ℚ) else 0) + cPair p q
      rw [if_neg hi'', if_neg hk]
    · intro j' hj'
      have hj'' : s ≤ (j' : ℕ) + p := by
        have := Fin.lt_def.mp hj'
        omega
      show (if s ≤ (j' : ℕ) + p then -(m : ℚ) else 0) - cPair p q =
        (if s ≤ (l : ℕ) + p then -(m : ℚ) else 0) - cPair p q
      rw [if_pos hj'', if_pos hl]
    · show (0 : ℚ) < ((if r ≤ (k' : ℕ) + q then -(n : ℚ) else 0) + cPair p q) -
        ((if s ≤ (l : ℕ) + p then -(m : ℚ) else 0) - cPair p q)
      rw [if_neg hk, if_pos hl]
      linarith
  · exact absurd trivial hab

theorem nat_facts {D : RealData} (h : D.Hyp) :
    D.R + D.p + D.q = D.a + D.a' ∧ D.S = D.p + D.q ∧ D.P + D.p = D.a ∧ D.Q = D.p ∧ D.P' = D.q ∧
      D.Q' + D.q = D.a' ∧ 2 * nD D + D.a + D.a' = D.κ + 2 * D.p + 2 * D.q ∧
      2 * mD D + 2 * D.p + 2 * D.q = D.κ + D.a + D.a' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  have hn2 : 2 * nD D = D.κ + 2 * D.y - D.d := by
    unfold nD
    refine Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero ?_)
    simp only [RealData.y, RealData.d]
    omega
  have hm2 : 2 * mD D = D.κ + D.d - 2 * D.y := by
    unfold mD
    refine Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero ?_)
    simp only [RealData.y, RealData.d]
    omega
  simp only [RealData.y, RealData.d] at hn2 hm2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try simp only [RealData.R, RealData.S, RealData.P, RealData.Q, RealData.P', RealData.Q',
    RealData.y, RealData.d]
  all_goals omega

theorem rat_facts {D : RealData} (h : D.Hyp) :
    (D.R : ℚ) + D.p + D.q = D.a + D.a' ∧ (D.S : ℚ) = D.p + D.q ∧ (D.P : ℚ) + D.p = D.a ∧ (D.Q : ℚ) = D.p ∧
      (D.P' : ℚ) = D.q ∧ (D.Q' : ℚ) + D.q = D.a' ∧ 2 * (nD D : ℚ) + D.a + D.a' = D.κ + 2 * D.p + 2 * D.q ∧
      2 * (mD D : ℚ) + 2 * D.p + 2 * D.q = D.κ + D.a + D.a' ∧ (D.a : ℚ) + D.a' < D.κ ∧
      2 * ((D.p : ℚ) + D.q) < D.a' ∧ (D.a' : ℚ) < D.a ∧ (0 : ℚ) ≤ D.p ∧ (0 : ℚ) ≤ D.q := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := nat_facts h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by positivity, by positivity⟩
  · exact_mod_cast e1
  · exact_mod_cast e2
  · exact_mod_cast e3
  · exact_mod_cast e4
  · exact_mod_cast e5
  · exact_mod_cast e6
  · exact_mod_cast e7
  · exact_mod_cast e8
  · exact_mod_cast h.h2
  · exact_mod_cast h.h5
  · exact_mod_cast h.a_gt

theorem nm_facts {D : RealData} (h : D.Hyp) :
    0 < nD D ∧ 0 < mD D ∧ ((D.κ : ℚ) / 2 = nD D + cPair D.R D.S) ∧ ((D.κ : ℚ) / 2 = mD D - cPair D.R D.S) ∧
      D.P ≤ D.R ∧ D.Q ≤ D.S ∧ D.Q' ≤ D.R ∧ D.P' ≤ D.S := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := nat_facts h
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, -⟩ := rat_facts h
  have := h.h2; have := h.h5; have := h.a_gt
  refine ⟨by omega, by omega, ?_, ?_, by omega, by omega, by omega, by omega⟩
  · simp only [cPair]; linarith
  · simp only [cPair]; linarith

theorem la_eq {D : RealData} (h : D.Hyp) :
    (fun x => laNeg D.P' D.Q' D.R D.S (nD D) (mD D) x + (D.κ : ℚ) / 2) =
      fun x => laPos D.P D.Q D.R D.S (nD D) (mD D) x + 0 := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := nat_facts h
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, -⟩ := rat_facts h
  funext x
  rcases x with k | l
  · simp only [laNeg, laPos, cPair]
    by_cases hk : (k : ℕ) < D.P
    · rw [if_pos hk, if_neg (by omega)]; linarith
    · rw [if_neg hk, if_pos (by omega)]; linarith
  · simp only [laNeg, laPos, cPair]
    by_cases hk : (l : ℕ) < D.Q
    · rw [if_pos hk, if_neg (by omega)]; linarith
    · rw [if_neg hk, if_pos (by omega)]; linarith

theorem combV {D : RealData} (h : D.Hyp) :
    CombOK D.P D.Q ((D.κ : ℚ) / 2) 0 (laPos D.P D.Q D.R D.S (nD D) (mD D)) := by
  obtain ⟨hn, hm, e1, e2, hP, hQ, -, -⟩ := nm_facts h
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, g1, g2, g3, g4, g5⟩ := rat_facts h
  refine comb_pos hP hQ hn hm _ _ e1 e2 ?_ ?_ <;> simp only [cPair] <;> linarith

theorem combV' {D : RealData} (h : D.Hyp) :
    CombOK D.P' D.Q' (-((D.κ : ℚ) / 2)) ((D.κ : ℚ) / 2) (laNeg D.P' D.Q' D.R D.S (nD D) (mD D)) := by
  obtain ⟨hn, hm, e1, e2, -, -, hQ, hP⟩ := nm_facts h
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, g1, g2, g3, g4, g5⟩ := rat_facts h
  refine comb_neg hQ hP hn hm _ _ (by linarith) (by linarith) ?_ ?_ <;> simp only [cPair] <;> linarith

end PositivityTheory.KReal

end
end

noncomputable section

open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace

namespace PositivityTheory.KReal

theorem coreLM : CoreLM := by
  intro D h
  obtain ⟨hn, hm, e1, e2, hP, hQ, hQ', hP'⟩ := nm_facts h
  have c1 : ((D.κ : ℂ) / 2) = (((D.κ : ℚ) / 2 : ℚ) : ℂ) := by push_cast; rfl
  have c2 : (-((D.κ : ℂ) / 2)) = ((-((D.κ : ℚ) / 2) : ℚ) : ℂ) := by push_cast; rfl
  have n1 : Nontrivial (ThV D) :=
    nontrivial_of_pair _ _ c1 (c1 ▸ pair_pos hP hQ hn hm _ e1 e2)
  have n2 : Nontrivial (ThV' D) :=
    nontrivial_of_pair _ _ c2 (c2 ▸ pair_neg hQ' hP' hn hm _ (by linarith) (by linarith))
  have s1 := side_of ((D.κ : ℂ) / 2) 0 _ 0 c1 (by simp) _ (combV h) n1
  have s2 := side_of (-((D.κ : ℂ) / 2)) ((D.κ : ℂ) / 2) _ _ c2 c1 _ (combV' h) n2
  rw [la_eq h] at s2
  obtain ⟨Pi, i1, i2, act, π, π', h1, h2, h3, h4, h5, h6⟩ := common_quot _ _ _ _ _ s1 s2
  refine ⟨Pi, i1, i2, act, π, π', h1, h2, fun W x => ?_, fun W x => h4 W x, h5, h6⟩
  rw [← h3 W x]
  congr 1
  simp [thAct, opV]

end PositivityTheory.KReal

end
