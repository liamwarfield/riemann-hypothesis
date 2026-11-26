module

public import CompanionTheory.AutomorphicTheory.BesselWaveGrids.InterlacingGrids.FreeFamily
public import CompanionTheory.AutomorphicTheory.BesselWaveGrids.PStarTie
public import CompanionTheory.AutomorphicTheory.BesselWaveGrids.CoefFacts
public import CompanionTheory.AutomorphicTheory.KFiniteVectors.KDecay

@[expose] public section

section -- merged from CompanionTheory.AutomorphicTheory.BesselWaveGrids.InterlacingGrids.GridSum
namespace GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid

open Finset

theorem grid_sqrt_le {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) (nn Q : ℝ → ℝ) (β : ℝ)
    (hβ : 0 ≤ β)
    (hpos : ∀ a i, 0 < nn (grid a i) ∧ 0 < nn (grid a i + 1) ∧ 0 < Q (grid a i))
    (hb : ∀ a i, nn (grid a i) * nn (grid a i + 1) ≤ β ^ 2 * Q (grid a i))
    (n : Fin K → Fin (d + 1)) :
    Real.sqrt (((List.ofFn fun a => grid a (n a)).map nn).prod *
        ((List.ofFn fun a => grid a (n a)).map fun y => nn (y + 1)).prod /
        ((List.ofFn fun a => grid a (n a)).map Q).prod) ≤ β ^ K := by
  have hmap : ∀ h : ℝ → ℝ,
      ((List.ofFn fun a => grid a (n a)).map h).prod = ∏ a, h (grid a (n a)) := by
    intro h
    rw [List.map_ofFn, List.prod_ofFn]
    rfl
  simp only [hmap]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
  have hle : ∏ a, nn (grid a (n a)) * nn (grid a (n a) + 1) / Q (grid a (n a)) ≤
      ∏ _a : Fin K, β ^ 2 := by
    apply Finset.prod_le_prod₀
    · intro a _
      have h := hpos a (n a)
      exact div_nonneg (mul_nonneg h.1.le h.2.1.le) h.2.2.le
    · intro a _
      rw [div_le_iff₀ (hpos a (n a)).2.2]
      exact hb a (n a)
  calc _ ≤ Real.sqrt (∏ _a : Fin K, β ^ 2) := Real.sqrt_le_sqrt hle
    _ = β ^ K := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, pow_mul',
        Real.sqrt_sq (pow_nonneg hβ K)]

theorem grid_sum_le {K d : ℕ} (grid c : Fin K → Fin (d + 1) → ℝ) (nn Q : ℝ → ℝ) (β : ℝ)
    (hβ : 0 ≤ β)
    (hc : ∀ a, ∑ i, |c a i| ≤ 1)
    (hpos : ∀ a i, 0 < nn (grid a i) ∧ 0 < nn (grid a i + 1) ∧ 0 < Q (grid a i))
    (hb : ∀ a i, nn (grid a i) * nn (grid a i + 1) ≤ β ^ 2 * Q (grid a i)) :
    ∑ n : Fin K → Fin (d + 1), |∏ a, c a (n a)| *
      Real.sqrt (((List.ofFn fun a => grid a (n a)).map nn).prod *
        ((List.ofFn fun a => grid a (n a)).map fun y => nn (y + 1)).prod /
        ((List.ofFn fun a => grid a (n a)).map Q).prod) ≤ β ^ K := by
  calc _ ≤ ∑ n : Fin K → Fin (d + 1), |∏ a, c a (n a)| * β ^ K := by
        apply Finset.sum_le_sum
        intro n _
        exact mul_le_mul_of_nonneg_left (grid_sqrt_le grid nn Q β hβ hpos hb n) (abs_nonneg _)
    _ = (∏ a, ∑ i, |c a i|) * β ^ K := by
        rw [← Finset.sum_mul, Fintype.prod_sum]
        simp only [Finset.abs_prod]
    _ ≤ 1 * β ^ K := by
        refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hβ K)
        apply Finset.prod_le_one₀
        · intro a _
          exact Finset.sum_nonneg (fun i _ => abs_nonneg _)
        · intro a _
          exact hc a
    _ = β ^ K := one_mul _

end GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
end

section -- merged from CompanionTheory.AutomorphicTheory.BesselWaveGrids.InterlacingGrids.ProgYInjective
namespace GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid

open Finset

noncomputable def progY (y0 : ℝ) (M : ℕ) : Finset ℝ := (range M).image fun i : ℕ => y0 + 5 * (i : ℝ)

lemma progY_injective (y0 : ℝ) : Function.Injective fun i : ℕ => y0 + 5 * (i : ℝ) := by
  intro i j h
  have : (i : ℝ) = j := by simpa using h
  exact_mod_cast this

theorem progY_card (y0 : ℝ) (M : ℕ) : (progY y0 M).card = M := by
  unfold progY
  rw [card_image_of_injective _ (progY_injective y0), card_range]

theorem progY_sep (y0 : ℝ) (M : ℕ) : ∀ y ∈ progY y0 M, ∀ y' ∈ progY y0 M, y ≠ y' → 5 ≤ |y - y'| := by
  intro y hy y' hy' hne
  simp only [progY, mem_image, mem_range] at hy hy'
  obtain ⟨i, -, rfl⟩ := hy
  obtain ⟨j, -, rfl⟩ := hy'
  have hij : i ≠ j := by
    rintro rfl
    exact hne rfl
  have hsub : y0 + 5 * (i : ℝ) - (y0 + 5 * (j : ℝ)) = 5 * ((i : ℤ) - (j : ℤ) : ℤ) := by
    push_cast; ring
  rw [hsub, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 5)]
  have h1 : (1 : ℝ) ≤ |(((i : ℤ) - (j : ℤ) : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]
    have : (1 : ℤ) ≤ |(i : ℤ) - (j : ℤ)| := by
      exact Int.one_le_abs (sub_ne_zero.mpr (by exact_mod_cast hij))
    exact_mod_cast this
  linarith

theorem progY_cut (lo hi : ℝ) (M : ℕ) (hlen : 5 * (M : ℝ) ≤ hi - lo) :
    ∀ y ∈ progY (2 - hi) M, (lo + 2 ≤ -y ∧ -y ≤ hi - 2) ∧ (lo + 2 ≤ -(y + 1) ∧ -(y + 1) ≤ hi - 2) := by
  intro y hy
  simp only [progY, mem_image, mem_range] at hy
  obtain ⟨i, hi', rfl⟩ := hy
  have hiM : (i : ℝ) + 1 ≤ M := by exact_mod_cast hi'
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

end GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
end

section -- merged from CompanionTheory.AutomorphicTheory.BesselWaveGrids.InterlacingGrids.LagSum
namespace GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid

open Finset

theorem lag_abs_term_le {d : ℕ} (y : Fin (d + 1) → ℝ) (h : ∀ i j, i ≠ j → 5 ≤ |y i - y j|)
    (j : Fin (d + 1)) :
    |∏ i ∈ (univ : Finset (Fin (d + 1))).erase j, (y j - y i)⁻¹| ≤ (1 / 5 : ℝ) ^ d := by
  rw [abs_prod]
  have hcard : ((univ : Finset (Fin (d + 1))).erase j).card = d := by
    rw [Finset.card_erase_of_mem (mem_univ j)]; simp
  calc ∏ i ∈ (univ : Finset (Fin (d + 1))).erase j, |(y j - y i)⁻¹|
      ≤ ∏ _i ∈ (univ : Finset (Fin (d + 1))).erase j, (1 / 5 : ℝ) := by
        apply Finset.prod_le_prod₀
        · intro i _; exact abs_nonneg _
        · intro i hi
          have hij : j ≠ i := (Finset.ne_of_mem_erase hi).symm
          rw [abs_inv]
          have hx : 0 < |y j - y i| := lt_of_lt_of_le (by norm_num) (h j i hij)
          simpa only [one_div] using
            (div_le_div_iff₀ (a := (1 : ℝ)) (b := |y j - y i|) (c := 1) (d := 5)
              hx (by norm_num : 0 < (5 : ℝ))).2 (by simpa using h j i hij)
    _ = (1 / 5 : ℝ) ^ d := by rw [Finset.prod_const, hcard]

theorem lag_abs_sum_le_one {d : ℕ} (y : Fin (d + 1) → ℝ) (h : ∀ i j, i ≠ j → 5 ≤ |y i - y j|) :
    ∑ j, |∏ i ∈ (univ : Finset (Fin (d + 1))).erase j, (y j - y i)⁻¹| ≤ 1 := by
  have hn : (d : ℝ) + 1 ≤ 5 ^ d := by
    have : d + 1 ≤ 5 ^ d := Nat.lt_pow_self (by norm_num)
    exact_mod_cast this
  calc ∑ j, |∏ i ∈ (univ : Finset (Fin (d + 1))).erase j, (y j - y i)⁻¹|
      ≤ ∑ _j : Fin (d + 1), (1 / 5 : ℝ) ^ d :=
        Finset.sum_le_sum (fun j _ => lag_abs_term_le y h j)
    _ = ((d : ℝ) + 1) / 5 ^ d := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, div_pow, one_pow]
        push_cast; ring
    _ ≤ 1 := by
        rw [div_le_one (by positivity)]
        exact hn

end GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
end

section -- merged from CompanionTheory.AutomorphicTheory.BesselWaveGrids.GridsText
section -- merged from CompanionTheory.AutomorphicTheory.BesselWaveGrids.FourLeOfFive
section -- merged from CompanionTheory.AutomorphicTheory.BesselWaveGrids.Bridge
namespace CompanionTheory.WaveGrid

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Finset

theorem cutWord_of_list (P : M.Par) (l0 : ℕ) (L : List C.Letter)
    (hc : ∀ l ∈ L, I.OnCut P.u P.u' l0 l.2)
    (hp : L.Pairwise fun l l' => 2 < |l.2 - l'.2|) : KB.CutWord P l0 L := by
  refine ⟨fun a => hc _ (List.get_mem L a), fun a b hab => ?_⟩
  rcases lt_or_gt_of_ne hab with h | h
  · exact List.pairwise_iff_get.1 hp a b h
  · have := List.pairwise_iff_get.1 hp b a h
    rwa [abs_sub_comm] at this

theorem list_of_cutWord {P : M.Par} {l0 : ℕ} {L : List C.Letter} (h : KB.CutWord P l0 L) :
    (∀ l ∈ L, I.OnCut P.u P.u' l0 l.2) ∧ L.Pairwise fun l l' => 2 < |l.2 - l'.2| := by
  refine ⟨fun l hl => ?_, List.pairwise_iff_get.2 fun a b hab => h.2 a b (ne_of_lt hab)⟩
  obtain ⟨a, rfl⟩ := List.get_of_mem hl
  exact h.1 a

theorem two_lt_of_five {a t : ℝ} (ha : 5 ≤ |a|) (ht : |t| ≤ 1) : 2 < |a + t| := by
  have h := abs_add_le (a + t) (-t)
  rw [add_neg_cancel_right, abs_neg] at h
  linarith

theorem free_dist {Y : Finset ℝ} (hsep : ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → 5 ≤ |y - y'|) {y : ℝ} (hy : y ∈ Y)
    {l : C.Letter} (hl : ∃ y' ∈ Y, y' ≠ y ∧ (l = (true, y') ∨ l = (false, y' + 1))) :
    2 < |y - l.2| ∧ 2 < |(y + 1) - l.2| := by
  obtain ⟨y', hy', hne, h | h⟩ := hl
  · subst h
    have h5 := hsep y hy y' hy' (Ne.symm hne)
    refine ⟨by simp only; linarith, ?_⟩
    have e : (y + 1) - y' = (y - y') + 1 := by ring
    simp only
    rw [e]
    exact two_lt_of_five h5 (by norm_num)
  · subst h
    have h5 := hsep y hy y' hy' (Ne.symm hne)
    refine ⟨?_, ?_⟩
    · have e : y - (y' + 1) = (y - y') + (-1) := by ring
      simp only
      rw [e]
      exact two_lt_of_five h5 (by norm_num)
    · have e : (y + 1) - (y' + 1) = y - y' := by ring
      simp only
      rw [e]
      linarith

section grid

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem gridOK_of_free (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (Y : Finset ℝ) (B : ℝ) (K : ℕ) (w : List C.Letter)
    (d : ℕ) (grid : Fin K → Fin (d + 1) → ℝ) (hB : 0 ≤ B)
    (hcut : ∀ y ∈ Y, I.OnCut P.u P.u' p.l0 y ∧ I.OnCut P.u P.u' p.l0 (y + 1))
    (hsep : ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → 5 ≤ |y - y'|)
    (hw : KB.CutWord P p.l0 w)
    (hY : ∀ a i, grid a i ∈ Y)
    (hinj : ∀ a i a' i', grid a i = grid a' i' → a = a' ∧ i = i')
    (hfree : ∀ a i, ∀ l ∈ w, ∃ y ∈ Y, y ≠ grid a i ∧ (l = (true, y) ∨ l = (false, y + 1)))
    (hq : ∀ a i, (0 < nn (grid a i) ∧ 0 < nn (grid a i + 1) ∧
        0 < (Wd.qw (M.qC P) (D.positionted w) ((grid a i : ℝ) : ℂ)).re) ∧
        nn (grid a i) * nn (grid a i + 1) ≤ B ^ 2 * (Wd.qw (M.qC P) (D.positionted w) ((grid a i : ℝ) : ℂ)).re) :
    TBBx5.GridOK p nn Y B K w d grid := by
  have hsepg : ∀ a i a' i', (a, i) ≠ (a', i') → 5 ≤ |grid a i - grid a' i'| := by
    intro a i a' i' hne
    refine hsep _ (hY a i) _ (hY a' i') fun h => hne ?_
    obtain ⟨h1, h2⟩ := hinj a i a' i' h
    rw [h1, h2]
  obtain ⟨hwc, hwp⟩ := list_of_cutWord hw
  refine ⟨fun a i j h => (hinj a i a j h).2, hY, fun n => ?_, ?_⟩
  · have hnew : (TBBx5.ysOf grid n).Pairwise fun y y' => 2 < |y - y'| := by
      unfold TBBx5.ysOf
      rw [List.pairwise_ofFn]
      intro a b hab
      have := hsepg a (n a) b (n b) (fun h => (ne_of_lt hab) (Prod.mk.inj h).1)
      linarith
    have hmem : ∀ y ∈ TBBx5.ysOf grid n, ∃ a, grid a (n a) = y := fun y hy => List.mem_ofFn.1 hy
    refine ⟨?_, ?_, hnew⟩
    · rw [TBBx5.plusW_eq]
      refine cutWord_of_list P p.l0 _ (fun l hl => ?_) ?_
      · rcases List.mem_append.1 hl with hl | hl
        · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hl
          obtain ⟨a, rfl⟩ := hmem y hy
          exact (hcut _ (hY a (n a))).1
        · exact hwc l hl
      · refine List.pairwise_append.2 ⟨List.pairwise_map.2 hnew, hwp, fun l hl l' hl' => ?_⟩
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hl
        obtain ⟨a, rfl⟩ := hmem y hy
        exact (free_dist hsep (hY a (n a)) (hfree a (n a) l' hl')).1
    · rw [TBBx5.minusW_eq]
      refine cutWord_of_list P p.l0 _ (fun l hl => ?_) ?_
      · rcases List.mem_append.1 hl with hl | hl
        · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hl
          obtain ⟨a, rfl⟩ := hmem y hy
          exact (hcut _ (hY a (n a))).2
        · exact hwc l hl
      · refine List.pairwise_append.2 ⟨List.pairwise_map.2 (hnew.imp fun h => ?_), hwp, fun l hl l' hl' => ?_⟩
        · simpa [add_sub_add_right_eq_sub] using h
        · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hl
          obtain ⟨a, rfl⟩ := hmem y hy
          exact (free_dist hsep (hY a (n a)) (hfree a (n a) l' hl')).2
  · exact GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.grid_sum_le grid (fun a i => F7.lagCo (grid a) i) nn
      (fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) (y : ℂ)).re) B hB
      (fun a => GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.lag_abs_sum_le_one (grid a)
        (fun i j h => hsepg a i a j (fun h' => h (Prod.mk.inj h').2)))
      (fun a i => (hq a i).1) (fun a i => (hq a i).2)

def FreeBound (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (Y : Finset ℝ) (B : ℝ) (K N : ℕ) : Prop :=
  ∀ w, TBB.AdmW P p.l0 Y w → w.length + K ≤ N → ∀ y ∈ Y,
    (∀ l ∈ w, ∃ y' ∈ Y, y' ≠ y ∧ (l = (true, y') ∨ l = (false, y' + 1))) →
    (0 < nn y ∧ 0 < nn (y + 1) ∧ 0 < (Wd.qw (M.qC P) (D.positionted w) (y : ℂ)).re) ∧
      nn y * nn (y + 1) ≤ B ^ 2 * (Wd.qw (M.qC P) (D.positionted w) (y : ℂ)).re

theorem waveGrid_of_sep (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (Y : Finset ℝ) (B : ℝ) (K N : ℕ) (hB : 0 ≤ B)
    (hcut : ∀ y ∈ Y, I.OnCut P.u P.u' p.l0 y ∧ I.OnCut P.u P.u' p.l0 (y + 1))
    (hsep : ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → 5 ≤ |y - y'|)
    (hcard : N - K + K * (2 * P.r + 1) ≤ Y.card) (hq : FreeBound p nn Y B K N) :
    TBBx5.WaveGrid p nn Y B K N := by
  intro j hj w hw hN
  have h1 : w.length ≤ N - K := by omega
  have h2 : K * (2 * j + 1) ≤ K * (2 * P.r + 1) := Nat.mul_le_mul_left _ (by omega)
  obtain ⟨g, hgY, hginj, hgfree⟩ := GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.exists_free_family Y w K (2 * j + 1)
    hw.2 ((Nat.add_le_add h1 h2).trans hcard)
  exact ⟨g, gridOK_of_free p nn Y B K w (2 * j) g hB hcut hsep hw.1 hgY hginj hgfree
    (fun a i => hq w hw hN _ (hgY a i) (hgfree a i))⟩

theorem liftGrid_of_sep (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (Y : Finset ℝ) (B : ℝ) (K N : ℕ) (hB : 0 ≤ B)
    (hcut : ∀ y ∈ Y, I.OnCut P.u P.u' p.l0 y ∧ I.OnCut P.u P.u' p.l0 (y + 1))
    (hsep : ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → 5 ≤ |y - y'|)
    (hcard : N - K + K * (2 * P.r + 1) ≤ Y.card) (hq : FreeBound p nn Y B K N) :
    TBBx5.LiftGrid p nn Y B K N := by
  intro b s hb hs hbs w hw hN
  have h1 : w.length ≤ N - K := by omega
  have h2 : K * (2 * (b + s - 1 - s) + s + 1) ≤ K * (2 * P.r + 1) := Nat.mul_le_mul_left _ (by omega)
  obtain ⟨g, hgY, hginj, hgfree⟩ := GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.exists_free_family Y w K
    (2 * (b + s - 1 - s) + s + 1) hw.2 ((Nat.add_le_add h1 h2).trans hcard)
  exact ⟨g, gridOK_of_free p nn Y B K w (2 * (b + s - 1 - s) + s) g hB hcut hsep hw.1 hgY hginj hgfree
    (fun a i => hq w hw hN _ (hgY a i) (hgfree a i))⟩

end grid

end CompanionTheory.WaveGrid
end

namespace CompanionTheory.WaveGrid

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Finset GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid

noncomputable def gridY (P : M.Par) (l N : ℕ) : Finset ℝ := progY (2 - max (P.u l) (P.u' l)) (N * (2 * P.r + 1))

noncomputable def gridΛ (P : M.Par) (b : ℝ) (N : ℕ) : ℝ :=
  max 1 (Real.sqrt ((4 / 3 : ℝ) ^ N * (b ^ (8 * P.r + 20) / (P.T * P.T'))))

theorem one_le_gridΛ (P : M.Par) (b : ℝ) (N : ℕ) : 1 ≤ gridΛ P b N := by
  unfold gridΛ
  exact le_max_left _ _

theorem gridΛ_sq (P : M.Par) (b : ℝ) (N : ℕ) (hb : 0 ≤ b) (hTT : 0 < P.T * P.T') :
    (4 / 3 : ℝ) ^ N * (b ^ (8 * P.r + 20) / (P.T * P.T')) ≤ gridΛ P b N ^ 2 := by
  unfold gridΛ
  have hX : 0 ≤ (4 / 3 : ℝ) ^ N * (b ^ (8 * P.r + 20) / (P.T * P.T')) :=
    mul_nonneg (pow_nonneg (by norm_num) _) (div_nonneg (pow_nonneg hb _) hTT.le)
  calc (4 / 3 : ℝ) ^ N * (b ^ (8 * P.r + 20) / (P.T * P.T'))
      = Real.sqrt ((4 / 3 : ℝ) ^ N * (b ^ (8 * P.r + 20) / (P.T * P.T'))) ^ 2 := (Real.sq_sqrt hX).symm
    _ ≤ max 1 (Real.sqrt ((4 / 3 : ℝ) ^ N * (b ^ (8 * P.r + 20) / (P.T * P.T')))) ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) (le_max_right _ _) 2

theorem gridΛ_le (P : M.Par) (b CT : ℝ) (N : ℕ) (hN : N ≤ 3 * (P.r + 1)) (hb : 3 ≤ b) (hCT : 0 ≤ CT)
    (hTT0 : 0 < P.T * P.T') (hTT : b ^ (-(CT * ((2 * P.r + 2 : ℕ) : ℝ))) ≤ P.T * P.T') :
    gridΛ P b N ≤ b ^ ((6 + CT) * ((2 * P.r + 2 : ℕ) : ℝ)) := by
  have hb0 : 0 < b := by linarith
  have hb1 : 1 ≤ b := by linarith
  have hr0 : (0 : ℝ) ≤ P.r := Nat.cast_nonneg _
  have hm' : (((2 * P.r + 2 : ℕ) : ℝ)) = 2 * (P.r : ℝ) + 2 := by push_cast; ring
  set m : ℝ := (((2 * P.r + 2 : ℕ) : ℝ)) with hm
  have hm0 : 0 ≤ m := by rw [hm']; linarith
  have hCm : 0 ≤ CT * m := mul_nonneg hCT hm0
  have hinv : (P.T * P.T')⁻¹ ≤ b ^ (CT * m) := by
    have h1 : 0 < b ^ (CT * m) := Real.rpow_pos_of_pos hb0 _
    rw [Real.rpow_neg hb0.le] at hTT
    exact (inv_le_comm₀ h1 hTT0).mp hTT
  have h43 : (4 / 3 : ℝ) ^ N ≤ b ^ (3 * (P.r + 1)) :=
    le_trans (pow_le_pow_left₀ (by norm_num) (by linarith) N) (pow_le_pow_right₀ hb1 hN)
  have hpow : b ^ (3 * (P.r + 1)) * b ^ (8 * P.r + 20) ≤ b ^ (12 * m) := by
    rw [← pow_add, ← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hb1
    rw [hm']
    push_cast
    linarith
  have hX : (4 / 3 : ℝ) ^ N * (b ^ (8 * P.r + 20) / (P.T * P.T')) ≤ b ^ (12 * m) * b ^ (CT * m) := by
    rw [div_eq_mul_inv]
    calc (4 / 3 : ℝ) ^ N * (b ^ (8 * P.r + 20) * (P.T * P.T')⁻¹)
        ≤ b ^ (3 * (P.r + 1)) * (b ^ (8 * P.r + 20) * b ^ (CT * m)) :=
          mul_le_mul h43 (mul_le_mul_of_nonneg_left hinv (pow_nonneg hb0.le _))
            (mul_nonneg (pow_nonneg hb0.le _) (inv_nonneg.mpr hTT0.le)) (pow_nonneg hb0.le _)
      _ = (b ^ (3 * (P.r + 1)) * b ^ (8 * P.r + 20)) * b ^ (CT * m) := by ring
      _ ≤ b ^ (12 * m) * b ^ (CT * m) := mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hb0.le _)
  have hy : (b ^ ((6 + CT) * m)) ^ 2 = b ^ (12 * m) * b ^ (2 * (CT * m)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hb0.le, ← Real.rpow_add hb0]
    congr 1
    push_cast
    ring
  have hX' : (4 / 3 : ℝ) ^ N * (b ^ (8 * P.r + 20) / (P.T * P.T')) ≤ (b ^ ((6 + CT) * m)) ^ 2 := by
    rw [hy]
    refine le_trans hX (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hb0.le _))
    exact Real.rpow_le_rpow_of_exponent_le hb1 (by linarith)
  unfold gridΛ
  refine max_le (Real.one_le_rpow hb1 (mul_nonneg (by linarith) hm0)) ?_
  calc Real.sqrt ((4 / 3 : ℝ) ^ N * (b ^ (8 * P.r + 20) / (P.T * P.T')))
      ≤ Real.sqrt ((b ^ ((6 + CT) * m)) ^ 2) := Real.sqrt_le_sqrt hX'
    _ = b ^ ((6 + CT) * m) := Real.sqrt_sq (Real.rpow_nonneg hb0.le _)

theorem onCut_of_minmax (u u' : ℕ → ℝ) (l : ℕ) (Y : ℝ) (h1 : min (u l) (u' l) + 2 ≤ -Y)
    (h2 : -Y ≤ max (u l) (u' l) - 2) : I.OnCut u u' l Y := by
  unfold Formalism.FourierDecayAlt.I.OnCut
  rcases le_total (u l) (u' l) with h | h
  · left
    rw [min_eq_left h] at h1
    rw [max_eq_right h] at h2
    exact ⟨h1, h2⟩
  · right
    rw [min_eq_right h] at h1
    rw [max_eq_left h] at h2
    exact ⟨h1, h2⟩

section grid

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem gridY_cut (P : M.Par) (l N : ℕ) (hlen : 5 * ((N * (2 * P.r + 1) : ℕ) : ℝ) ≤ |P.u l - P.u' l|) :
    ∀ y ∈ gridY P l N, I.OnCut P.u P.u' l y ∧ I.OnCut P.u P.u' l (y + 1) := by
  intro y hy
  have hlen' : 5 * ((N * (2 * P.r + 1) : ℕ) : ℝ) ≤ max (P.u l) (P.u' l) - min (P.u l) (P.u' l) := by
    rw [max_sub_min_eq_abs, abs_sub_comm]
    exact hlen
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := progY_cut (min (P.u l) (P.u' l)) (max (P.u l) (P.u' l)) _ hlen' y hy
  exact ⟨onCut_of_minmax _ _ _ _ h1 h2, onCut_of_minmax _ _ _ _ h3 h4⟩

private theorem exists_ge_four_fifths_pow_qw_eq_mul_of_far_letters {S : Type} (q : ℂ → ℂ) (y : ℝ) :
    ∀ L : List (Formalism.FourierDecayAlt.Wd.Letter ℂ S),
      (∀ l ∈ L, ∃ d : ℝ, 5 ≤ |d| ∧ ((l.plus = true ∧ l.pt = ((y - d : ℝ) : ℂ)) ∨
        (l.plus = false ∧ l.pt = ((y - d + 1 : ℝ) : ℂ)))) →
      ∃ t : ℝ, (4 / 5 : ℝ) ^ L.length ≤ t ∧ Formalism.FourierDecayAlt.Wd.qw q L (y : ℂ) = (t : ℂ) * q (y : ℂ) := by
  intro L
  induction L with
  | nil =>
    intro _
    exact ⟨1, by simp, by simp [Formalism.FourierDecayAlt.Wd.qw]⟩
  | cons l L ih =>
    intro h
    obtain ⟨t, ht, heq⟩ := ih (fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))
    obtain ⟨d, hd, hcase⟩ := h l (by simp)
    have ht0 : 0 ≤ t := le_trans (pow_nonneg (by norm_num) _) ht
    rcases hcase with ⟨hp, hpt⟩ | ⟨hp, hpt⟩
    · refine ⟨t * ((y - (y - d) + 1) / (y - (y - d))), ?_, ?_⟩
      · have e : (y - (y - d) + 1) / (y - (y - d)) = (d + 1) / d := by congr 1 <;> ring
        have hf : (4 / 5 : ℝ) ≤ (d + 1) / d := by
          rcases le_abs.mp hd with h5 | h5
          · rw [le_div_iff₀ (by linarith)]
            linarith
          · rw [le_div_iff_of_neg (by linarith)]
            linarith
        rw [e, List.length_cons, pow_succ]
        exact mul_le_mul ht hf (by norm_num) ht0
      · simp only [Formalism.FourierDecayAlt.Wd.qw, hp, if_true, heq, hpt]
        push_cast
        ring
    · refine ⟨t * ((y - d + 1 - y) / (y - d + 1 - y - 1)), ?_, ?_⟩
      · have e : (y - d + 1 - y) / (y - d + 1 - y - 1) = (1 - d) / (-d) := by congr 1 <;> ring
        have hf : (4 / 5 : ℝ) ≤ (1 - d) / (-d) := by
          rcases le_abs.mp hd with h5 | h5
          · rw [le_div_iff_of_neg (by linarith)]
            linarith
          · rw [le_div_iff₀ (by linarith)]
            linarith
        rw [e, List.length_cons, pow_succ]
        exact mul_le_mul ht hf (by norm_num) ht0
      · simp only [Formalism.FourierDecayAlt.Wd.qw, hp, Bool.false_eq_true, ↓reduceIte, heq, hpt]
        push_cast
        ring

theorem freeBound_text (p : KB.Pl P Wp Wq) (K N : ℕ) (lam : ℕ → ℝ) (c g b : ℝ) (hL : PairData P p.l0 lam c g b)
    (hlen : 5 * ((N * (2 * P.r + 1) : ℕ) : ℝ) ≤ |P.u p.l0 - P.u' p.l0|) :
    FreeBound p (Pst P.k P.r lam c) (gridY P p.l0 N) (gridΛ P b N) K N := by
  have hOK : P.OK := p.hP.1
  obtain ⟨hl1, hl2, hk2⟩ := p.hl
  have hTT : 0 < P.T * P.T' := mul_pos hOK.T_pos hOK.T'_pos
  have hb : 0 ≤ b := by linarith [hL.b_ge_three]
  have hc := hL.c_pos
  have hPst : ∀ Y : ℝ, 0 < GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.Pst P.k P.r lam c Y := by
    intro Y
    unfold GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.Pst
    exact Finset.prod_pos (fun s _ => add_pos_of_nonneg_of_pos (abs_nonneg _) hc)
  have hY := gridY_cut P p.l0 N hlen
  have hsep := progY_sep (2 - max (P.u p.l0) (P.u' p.l0)) (N * (2 * P.r + 1))
  intro w _ hwlen y hy hlet
  have hlet' : ∀ l ∈ Formalism.FourierDecayAlt.D.positionted w, ∃ d : ℝ, 5 ≤ |d| ∧ ((l.plus = true ∧ l.pt = ((y - d : ℝ) : ℂ)) ∨
      (l.plus = false ∧ l.pt = ((y - d + 1 : ℝ) : ℂ))) := by
    intro l hl
    unfold Formalism.FourierDecayAlt.D.positionted at hl
    rw [List.mem_ofFn] at hl
    obtain ⟨a, rfl⟩ := hl
    obtain ⟨y', hy', hne, hcase⟩ := hlet (w.get a) (by simp [List.get_eq_getElem])
    refine ⟨y - y', hsep y hy y' hy' (Ne.symm hne), ?_⟩
    rcases hcase with h | h
    · left
      refine ⟨by show (w.get a).1 = true; rw [h], ?_⟩
      simp only [h]
      push_cast
      ring
    · right
      refine ⟨by show (w.get a).1 = false; rw [h], ?_⟩
      simp only [h]
      push_cast
      ring
  obtain ⟨t, ht, heq⟩ := exists_ge_four_fifths_pow_qw_eq_mul_of_far_letters (Formalism.FourierDecayAlt.M.qC P) y _ hlet'
  have hls : (Formalism.FourierDecayAlt.D.positionted w).length = w.length := by
    unfold Formalism.FourierDecayAlt.D.positionted
    simp
  rw [hls] at ht
  have hq := nq_onCut_pair P hOK p.l0 hl1 hl2 hk2 lam c g b hL y (hY y hy).1
  have hre : (Formalism.FourierDecayAlt.Wd.qw (Formalism.FourierDecayAlt.M.qC P) (Formalism.FourierDecayAlt.D.positionted w) (y : ℂ)).re
      = t * (Formalism.FourierDecayAlt.M.qC P (y : ℂ)).re := by
    rw [heq, Complex.re_ofReal_mul]
  have ht0 : 0 < t := lt_of_lt_of_le (pow_pos (by norm_num) _) ht
  refine ⟨⟨hPst y, hPst (y + 1), by rw [hre]; exact mul_pos ht0 hq.1⟩, ?_⟩
  rw [hre]
  have hsq := gridΛ_sq P b N hb hTT
  have h1 : 1 ≤ (4 / 3 : ℝ) ^ N * t := by
    calc (1 : ℝ) ≤ ((4 / 3 : ℝ) * (4 / 5)) ^ w.length := one_le_pow₀ (by norm_num)
      _ = (4 / 3 : ℝ) ^ w.length * (4 / 5) ^ w.length := mul_pow _ _ _
      _ ≤ (4 / 3 : ℝ) ^ N * t :=
        mul_le_mul (pow_le_pow_right₀ (by norm_num) (by omega)) ht (by positivity) (by positivity)
  have hR0 : 0 ≤ b ^ (8 * P.r + 20) / (P.T * P.T') * (Formalism.FourierDecayAlt.M.qC P (y : ℂ)).re :=
    mul_nonneg (div_nonneg (pow_nonneg hb _) hTT.le) hq.1.le
  calc GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.Pst P.k P.r lam c y
        * GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.Pst P.k P.r lam c (y + 1)
      ≤ b ^ (8 * P.r + 20) / (P.T * P.T') * (Formalism.FourierDecayAlt.M.qC P (y : ℂ)).re := hq.2
    _ ≤ b ^ (8 * P.r + 20) / (P.T * P.T') * (Formalism.FourierDecayAlt.M.qC P (y : ℂ)).re * ((4 / 3 : ℝ) ^ N * t) :=
        le_mul_of_one_le_right hR0 h1
    _ = ((4 / 3 : ℝ) ^ N * (b ^ (8 * P.r + 20) / (P.T * P.T'))) * (t * (Formalism.FourierDecayAlt.M.qC P (y : ℂ)).re) := by ring
    _ ≤ gridΛ P b N ^ 2 * (t * (Formalism.FourierDecayAlt.M.qC P (y : ℂ)).re) :=
        mul_le_mul_of_nonneg_right hsq (mul_pos ht0 hq.1).le

theorem grids_text (p : KB.Pl P Wp Wq) (K N : ℕ) (hKN : K ≤ N) (lam : ℕ → ℝ) (c g b : ℝ)
    (hL : PairData P p.l0 lam c g b) (hlen : 5 * ((N * (2 * P.r + 1) : ℕ) : ℝ) ≤ |P.u p.l0 - P.u' p.l0|) :
    TBBx5.WaveGrid p (Pst P.k P.r lam c) (gridY P p.l0 N) (gridΛ P b N) K N ∧
      TBBx5.LiftGrid p (Pst P.k P.r lam c) (gridY P p.l0 N) (gridΛ P b N) K N := by
  have hY := gridY_cut P p.l0 N hlen
  have hsep := progY_sep (2 - max (P.u p.l0) (P.u' p.l0)) (N * (2 * P.r + 1))
  have hcard : N - K + K * (2 * P.r + 1) ≤ (gridY P p.l0 N).card := by
    unfold gridY
    rw [progY_card]
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hKN
    rw [Nat.add_sub_cancel_left]
    nlinarith [Nat.zero_le (j * P.r)]
  have hF := freeBound_text p K N lam c g b hL hlen
  have hB : 0 ≤ gridΛ P b N := le_trans zero_le_one (one_le_gridΛ P b N)
  exact ⟨waveGrid_of_sep p _ _ _ K N hB hY hsep hcard hF, liftGrid_of_sep p _ _ _ K N hB hY hsep hcard hF⟩

end grid

end CompanionTheory.WaveGrid
end

namespace CompanionTheory.WaveGrid

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq

section shift

variable {P : M.Par} {lam : Fin (2 * P.r + P.k + 1) → ℝ} {c g b : ℝ} {l n₀ : ℕ}

theorem pairData_plus (h : HypLam P.k P.r lam c g b) (hu : HypType P.k P.r lam P.u b) (hl1 : 1 ≤ l)
    (hlk : l < P.k) (hposition : (2 * n₀ + 1 : ℝ) ≤ P.u l - P.u (l + 1)) :
    PairData (shP P P.u (uPlus P.u l n₀)) (l + 1) (lamN lam) c g b := by
  open GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid in
  have movedData_of_hyp {Q : M.Par} {lamLocal : Fin (2 * Q.r + Q.k + 1) → ℝ} {c g b : ℝ}
      (h : HypLam Q.k Q.r lamLocal c g b) (hu : HypType Q.k Q.r lamLocal Q.u b) {j : ℕ}
      (hj1 : 1 ≤ j) (hjk : j ≤ Q.k) (hmv : ∀ i, i ≠ j → Q.u' i = Q.u i)
      (hj : |Q.u' j| ≤ b) : PairData Q j (lamN lamLocal) c g b := by
    exact { c_pos := by linarith [h.c_ge]
            g_ge := by linarith [h.c_ge, h.g_ge]
            b_ge_three := h.b_ge_three
            b_ge_k := h.k_le
            b_ge_c := h.b_ge_c
            lam_le := h.lamN_le
            gap := h.lamN_gap
            ul_le := ⟨hu.u_le j hj1 hjk, hj⟩
            pair := fun Y hY =>
              ⟨⟨0, pairOK_of_interlace Q.k (lamN lamLocal) Q.u 0 (-Y) (fun s h1 h2 => inter_half h.hc hu s h1 h2)⟩,
                pairOK_of_moved Q.k j (lamN lamLocal) Q.u Q.u' (-Y) (fun s h1 h2 => inter_half h.hc hu s h1 h2) hmv (by
                  rcases hY with ⟨h1, h2⟩ | ⟨h1, h2⟩
                  · exact Or.inl ⟨by linarith, by linarith⟩
                  · exact Or.inr ⟨by linarith, by linarith⟩)⟩ }
  refine (movedData_of_hyp (Q := shP P P.u (uPlus P.u l n₀)) h hu (by omega) hlk (fun i hi => ?_) ?_)
  · show uPlus P.u l n₀ i = P.u i
    simp only [uPlus, if_neg hi]
  · show |uPlus P.u l n₀ (l + 1)| ≤ b
    have h1 := abs_le.1 (hu.u_le l hl1 hlk.le)
    have h2 := abs_le.1 (hu.u_le (l + 1) (by omega) hlk)
    have h3 : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg _
    simp only [uPlus, if_true]
    rw [abs_le]
    constructor <;> linarith

theorem pairData_minus (h : HypLam P.k P.r lam c g b) (hu : HypType P.k P.r lam P.u b) (hl1 : 1 ≤ l)
    (hlk : l < P.k) (hposition : (2 * n₀ + 1 : ℝ) ≤ P.u l - P.u (l + 1)) :
    PairData (shP P P.u (uMinus P.u l n₀)) l (lamN lam) c g b := by
  open GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid in
  have movedData_of_hyp {Q : M.Par} {lamLocal : Fin (2 * Q.r + Q.k + 1) → ℝ} {c g b : ℝ}
      (h : HypLam Q.k Q.r lamLocal c g b) (hu : HypType Q.k Q.r lamLocal Q.u b) {j : ℕ}
      (hj1 : 1 ≤ j) (hjk : j ≤ Q.k) (hmv : ∀ i, i ≠ j → Q.u' i = Q.u i)
      (hj : |Q.u' j| ≤ b) : PairData Q j (lamN lamLocal) c g b := by
    exact { c_pos := by linarith [h.c_ge]
            g_ge := by linarith [h.c_ge, h.g_ge]
            b_ge_three := h.b_ge_three
            b_ge_k := h.k_le
            b_ge_c := h.b_ge_c
            lam_le := h.lamN_le
            gap := h.lamN_gap
            ul_le := ⟨hu.u_le j hj1 hjk, hj⟩
            pair := fun Y hY =>
              ⟨⟨0, pairOK_of_interlace Q.k (lamN lamLocal) Q.u 0 (-Y) (fun s h1 h2 => inter_half h.hc hu s h1 h2)⟩,
                pairOK_of_moved Q.k j (lamN lamLocal) Q.u Q.u' (-Y) (fun s h1 h2 => inter_half h.hc hu s h1 h2) hmv (by
                  rcases hY with ⟨h1, h2⟩ | ⟨h1, h2⟩
                  · exact Or.inl ⟨by linarith, by linarith⟩
                  · exact Or.inr ⟨by linarith, by linarith⟩)⟩ }
  refine (movedData_of_hyp (Q := shP P P.u (uMinus P.u l n₀)) h hu hl1 hlk.le (fun i hi => ?_) ?_)
  · show uMinus P.u l n₀ i = P.u i
    simp only [uMinus, if_neg hi]
  · show |uMinus P.u l n₀ l| ≤ b
    have h1 := abs_le.1 (hu.u_le l hl1 hlk.le)
    have h2 := abs_le.1 (hu.u_le (l + 1) (by omega) hlk)
    have h3 : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg _
    simp only [uMinus, if_true]
    rw [abs_le]
    constructor <;> linarith

theorem len_le (r : ℕ) : 15 * ((r : ℝ) + 1) * (2 * r + 1) ≤ 30 * ((r : ℝ) + 1) ^ 2 + 6 := by
  have : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  nlinarith

end shift

section grid

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem grids_PStar (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (c g b : ℝ)
    (hL : PairData P p.l0 (lamN lam) c g b)
    (hlen : 15 * ((P.r : ℝ) + 1) * (2 * P.r + 1) ≤ |P.u p.l0 - P.u' p.l0|) :
    TBBx5.WaveGrid p (PStar lam c) (gridY P p.l0 (3 * (P.r + 1))) (gridΛ P b (3 * (P.r + 1))) 3 (3 * (P.r + 1)) ∧
      TBBx5.LiftGrid p (PStar lam c) (gridY P p.l0 (3 * (P.r + 1))) (gridΛ P b (3 * (P.r + 1))) 3
        (3 * (P.r + 1)) := by
  have e : GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.Pst P.k P.r (lamN lam) c = PStar lam c :=
    funext fun y => Pst_lamN P.k P.r lam c y
  rw [← e]
  refine grids_text p 3 (3 * (P.r + 1)) (by omega) (lamN lam) c g b hL (le_trans (le_of_eq ?_) hlen)
  push_cast
  ring

theorem gridΛ_bounds (p : KB.Pl P Wp Wq) (b CT : ℝ) (hb : 3 ≤ b) (hCT : 0 ≤ CT)
    (hTT : b ^ (-(CT * ((2 * P.r + 2 : ℕ) : ℝ))) ≤ P.T * P.T') :
    1 ≤ gridΛ P b (3 * (P.r + 1)) ∧ gridΛ P b (3 * (P.r + 1)) ≤ b ^ ((6 + CT) * ((2 * P.r + 2 : ℕ) : ℝ)) :=
  ⟨one_le_gridΛ _ _ _, gridΛ_le P b CT _ le_rfl hb hCT (mul_pos p.hP.1.T_pos p.hP.1.T'_pos) hTT⟩

theorem grids_diff (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (c g b : ℝ)
    (h : HypLam P.k P.r lam c g b) (hu : HypType P.k P.r lam P.u b) (hu' : HypType P.k P.r lam P.u' b)
    (hlen : 30 * ((P.r : ℝ) + 1) ^ 2 + 6 ≤ |P.u p.l0 - P.u' p.l0|) :
    TBBx5.WaveGrid p (PStar lam c) (gridY P p.l0 (3 * (P.r + 1))) (gridΛ P b (3 * (P.r + 1))) 3 (3 * (P.r + 1)) ∧
      TBBx5.LiftGrid p (PStar lam c) (gridY P p.l0 (3 * (P.r + 1))) (gridΛ P b (3 * (P.r + 1))) 3
        (3 * (P.r + 1)) := by
  have data : LamData P (lamN lam) c g b := {
    c_pos := by linarith [h.c_ge]
    g_ge := by linarith [h.c_ge, h.g_ge]
    b_ge_three := h.b_ge_three
    b_ge_k := h.k_le
    b_ge_c := h.b_ge_c
    lam_le := h.lamN_le
    gap := h.lamN_gap
    inter := fun s h1 h2 => ⟨inter_half h.hc hu s h1 h2, inter_half h.hc hu' s h1 h2⟩
    u_le := fun i h1 h2 => ⟨hu.u_le i h1 h2, hu'.u_le i h1 h2⟩ }
  have pair : PairData P p.l0 (lamN lam) c g b := {
    c_pos := data.c_pos
    g_ge := data.g_ge
    b_ge_three := data.b_ge_three
    b_ge_k := data.b_ge_k
    b_ge_c := data.b_ge_c
    lam_le := data.lam_le
    gap := data.gap
    ul_le := data.u_le p.l0 p.hl.1 p.hl.2.1
    pair := fun Y _ =>
      ⟨⟨0, GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.pairOK_of_interlace P.k (lamN lam) P.u 0 (-Y) (fun s h1 h2 => (data.inter s h1 h2).1)⟩,
       ⟨0, GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.pairOK_of_interlace P.k (lamN lam) P.u' 0 (-Y) (fun s h1 h2 => (data.inter s h1 h2).2)⟩⟩ }
  exact grids_PStar p lam c g b pair ((len_le P.r).trans hlen)

theorem grids_plus {up up' : ℕ → ℝ} (q : KB.Pl (shP P up up') Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ)
    (c g b : ℝ) (l n₀ : ℕ) (h : HypLam P.k P.r lam c g b) (hu : HypType P.k P.r lam P.u b)
    (hn₀ : n₀ = 30 * (P.r + 1) ^ 2 + 6) (hl1 : 1 ≤ l) (hlk : l < P.k)
    (hposition : (2 * n₀ + 1 : ℝ) ≤ P.u l - P.u (l + 1)) (e1 : up = P.u) (e2 : up' = uPlus P.u l n₀)
    (e3 : q.l0 = l + 1) :
    TBBx5.WaveGrid q (PStar lam c) (gridY (shP P up up') q.l0 (3 * (P.r + 1))) (gridΛ P b (3 * (P.r + 1))) 3
        (3 * (P.r + 1)) ∧
      TBBx5.LiftGrid q (PStar lam c) (gridY (shP P up up') q.l0 (3 * (P.r + 1))) (gridΛ P b (3 * (P.r + 1))) 3
        (3 * (P.r + 1)) := by
  subst e1 e2
  have hn₀R : (n₀ : ℝ) = 30 * ((P.r : ℝ) + 1) ^ 2 + 6 := by rw [hn₀]; push_cast; ring
  refine grids_PStar q lam c g b (by rw [e3]; exact pairData_plus h hu hl1 hlk hposition) ?_
  rw [e3]
  show _ ≤ |P.u (l + 1) - uPlus P.u l n₀ (l + 1)|
  simp only [uPlus, if_true]
  rw [show P.u (l + 1) - (P.u (l + 1) + n₀) = -(n₀ : ℝ) by ring, abs_neg, abs_of_nonneg (Nat.cast_nonneg _), hn₀R]
  exact len_le P.r

theorem grids_minus {um um' : ℕ → ℝ} (q : KB.Pl (shP P um um') Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ)
    (c g b : ℝ) (l n₀ : ℕ) (h : HypLam P.k P.r lam c g b) (hu : HypType P.k P.r lam P.u b)
    (hn₀ : n₀ = 30 * (P.r + 1) ^ 2 + 6) (hl1 : 1 ≤ l) (hlk : l < P.k)
    (hposition : (2 * n₀ + 1 : ℝ) ≤ P.u l - P.u (l + 1)) (e1 : um = P.u) (e2 : um' = uMinus P.u l n₀)
    (e3 : q.l0 = l) :
    TBBx5.WaveGrid q (PStar lam c) (gridY (shP P um um') q.l0 (3 * (P.r + 1))) (gridΛ P b (3 * (P.r + 1))) 3
        (3 * (P.r + 1)) ∧
      TBBx5.LiftGrid q (PStar lam c) (gridY (shP P um um') q.l0 (3 * (P.r + 1))) (gridΛ P b (3 * (P.r + 1))) 3
        (3 * (P.r + 1)) := by
  subst e1 e2
  have hn₀R : (n₀ : ℝ) = 30 * ((P.r : ℝ) + 1) ^ 2 + 6 := by rw [hn₀]; push_cast; ring
  refine grids_PStar q lam c g b (by rw [e3]; exact pairData_minus h hu hl1 hlk hposition) ?_
  rw [e3]
  show _ ≤ |P.u l - uMinus P.u l n₀ l|
  simp only [uMinus, if_true]
  rw [show P.u l - (P.u l - n₀) = (n₀ : ℝ) by ring, abs_of_nonneg (Nat.cast_nonneg _), hn₀R]
  exact len_le P.r

end grid

end CompanionTheory.WaveGrid
end

section -- merged from CompanionTheory.AutomorphicTheory.BesselWaveGrids.AsmDiff
namespace CompanionTheory.WaveGrid

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Formalism.FourierDecayAlt.TBB Formalism.QuantumDeterminants


attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
def AsmDiff : Prop :=
  ∀ Cb C₃ CΛ C₀ : ℝ, 0 ≤ C₃ → 0 ≤ CΛ → 1 / 2 ≤ C₀ →
    ∃ C₄ c₃ Cc Cc' Cc'' : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
      (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b Λ A₀ : ℝ) (p₀ : ℕ) (χ nn : ℝ → ℝ) (Y : Finset ℝ) (K N : ℕ),
      3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → 1 ≤ TBB.Tq p →
      (p₀ : ℝ) ≤ C₀ * (3 * ((P.r : ℝ) + 1)) + 1 →
      3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nn y) →
      KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) →
      B.JF p.T.base f ∈ FFKB p →
      c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) →
      Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) →
      Cc' * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) →
      Cc'' * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) →
      N ≤ 2 * p₀ →
      BigCellDerivativeExpansion p f b C₃ (2 * p₀ + 0) →
      TBBx5.WaveGrid p nn Y Λ K N → TBBx5.LiftGrid p nn Y Λ K N →
      LimBd p nn (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) Y N →
      TBB.ThmBpAt p f b C₄ 0 p₀


attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
def AsmEq : Prop :=
  ∀ Cb C₃ CΛ C₀ : ℝ, 0 ≤ C₃ → 0 ≤ CΛ → 1 / 2 ≤ C₀ →
    ∃ C₄ c₃ Cc Cc' Cc'' : ℝ, ∀ (P : M.Par) (Wp Wq : Type)
      [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
      [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
      (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b : ℝ) (n₀ : ℕ) (S : ShiftAtR p f b n₀)
      (Λ A₀ : ℝ) (p₀ : ℕ) (χ nnp nnm : ℝ → ℝ) (Yp Ym : Finset ℝ) (K N : ℕ),
      3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → 1 ≤ Tq p →
      n₀ ≤ 30 * (P.r + 1) ^ 2 + 6 → (p₀ : ℝ) ≤ C₀ * (3 * ((P.r : ℝ) + 1)) + 1 →
      3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nnp y) → (∀ y, 0 < nnm y) →
      KB.InDDplus2 (shP P S.up S.up') S.pp.l0 S.pp.T.base Cb S.pp.Θ →
      KB.InDDplus2 (shP P S.um S.um') S.pm.l0 S.pm.T.base Cb S.pm.Θ →
      B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) →
      B.JF S.pp.T.base (fun g => (f g).comp (S.Ap g)) ∈ FFKB S.pp →
      B.JF S.pm.T.base (fun g => (f g).comp (S.Am g)) ∈ FFKB S.pm →
      c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - ((n₀ * (P.r + 1) : ℕ) : ℝ) →
      Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - ((n₀ * (P.r + 1) : ℕ) : ℝ) →
      Cc' * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - ((n₀ * (P.r + 1) : ℕ) : ℝ) →
      Cc'' * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - ((n₀ * (P.r + 1) : ℕ) : ℝ) →
      N ≤ 2 * p₀ →
      BigCellDerivativeExpansion p f b C₃ (2 * p₀ + n₀) →
      TBBx5.WaveGrid S.pp nnp Yp Λ K N → TBBx5.LiftGrid S.pp nnp Yp Λ K N →
      TBBx5.WaveGrid S.pm nnm Ym Λ K N → TBBx5.LiftGrid S.pm nnm Ym Λ K N →
      LimBd S.pp nnp (fpmSh S.pp f S.Ap p₀) Yp N → LimBd S.pm nnm (fpmSh S.pm f S.Am p₀) Ym N →
      ThmBpAt p f b C₄ n₀ p₀

end CompanionTheory.WaveGrid
end

section -- merged from CompanionTheory.AutomorphicTheory.BesselWaveGrids.LettersPoly
noncomputable section

namespace CompanionTheory.WaveGrid.LimSh

open Formalism.FourierDecayAlt Matrix CompanionTheory.LimBd.Main

section letters

variable {k r : ℕ}

theorem one_mem_letters : (1 : B.Mat k r → ℂ) ∈ Letters k r := Submodule.subset_span (Or.inl rfl)

theorem letters_pow_succ (a : ℕ) : Letters k r ^ a ≤ Letters k r ^ (a + 1) := by
  intro x hx
  rw [pow_succ, ← mul_one x]
  exact Submodule.mul_mem_mul hx one_mem_letters

theorem letters_pow_mono {a d : ℕ} (h : a ≤ d) : Letters k r ^ a ≤ Letters k r ^ d := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (letters_pow_succ _)

theorem mul_mem_letters_pow {a d : ℕ} {x y : B.Mat k r → ℂ} (hx : x ∈ Letters k r ^ a) (hy : y ∈ Letters k r ^ d) :
    x * y ∈ Letters k r ^ (a + d) := by
  rw [pow_add]
  exact Submodule.mul_mem_mul hx hy

theorem entry_mem (i j : Fin (2 * r + k + 1)) : (fun g : B.Mat k r => g i j) ∈ Letters k r :=
  Submodule.subset_span (Or.inr ⟨Pi.single j 1, Pi.single i 1, Or.inl fun g _ => by simp⟩)

theorem star_entry_mem (i j : Fin (2 * r + k + 1)) : (fun g : B.Mat k r => star (g i j)) ∈ Letters k r := by
  refine Submodule.subset_span (Or.inr ⟨fun a => Formalism.QuantumDeterminants.Hpk k r a i, star (Formalism.QuantumDeterminants.Hpk k r j), Or.inr ?_⟩)
  intro g hg
  have hH : Formalism.QuantumDeterminants.Hpk k r * Formalism.QuantumDeterminants.Hpk k r = 1 := (Formalism.QuantumDeterminants.hpkFacts k r).2.1
  have hg' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
  have hinv : g⁻¹ = Formalism.QuantumDeterminants.Hpk k r * gᴴ * Formalism.QuantumDeterminants.Hpk k r := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.mul_assoc (Formalism.QuantumDeterminants.Hpk k r), Matrix.mul_assoc (Formalism.QuantumDeterminants.Hpk k r), hg', hH]
  have e : Formalism.QuantumDeterminants.Hpk k r * (g⁻¹ * Formalism.QuantumDeterminants.Hpk k r) = gᴴ := by
    rw [hinv, Matrix.mul_assoc _ (Formalism.QuantumDeterminants.Hpk k r) (Formalism.QuantumDeterminants.Hpk k r), hH, Matrix.mul_one, ← Matrix.mul_assoc, hH,
      Matrix.one_mul]
  have e2 := congrFun (congrFun e j) i
  rw [conjTranspose_apply] at e2
  rw [star_star]
  exact e2.symm

theorem polyDeg_mem {e : ℕ} {c : B.Mat k r → ℂ} (hc : U.IsPolyDeg e c) : c ∈ Letters k r ^ e := by
  classical
  obtain ⟨q, hq, hcq⟩ := hc
  let X : (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) ⊕ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) →
      B.Mat k r → ℂ := Sum.elim (fun x g => g x.1 x.2) (fun x g => star (g x.1 x.2))
  have hX : ∀ v, X v ∈ Letters k r := by
    rintro (x | x)
    · exact entry_mem x.1 x.2
    · exact star_entry_mem x.1 x.2
  have hpow : ∀ v (n : ℕ), X v ^ n ∈ Letters k r ^ n := fun v n => Submodule.pow_mem_pow _ (hX v) n
  have hprod : ∀ (m : _ →₀ ℕ) (s : Finset _), (∏ v ∈ s, X v ^ m v) ∈ Letters k r ^ (∑ v ∈ s, m v) := by
    intro m s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      exact mul_mem_letters_pow (hpow a _) ih
  have e1 : c = ∑ m ∈ q.support, q.coeff m • ∏ v ∈ m.support, X v ^ m v := by
    funext g
    rw [hcq g, MvPolynomial.eval_eq, Finset.sum_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Pi.smul_apply, Finset.prod_apply, smul_eq_mul]
    congr 1
    refine Finset.prod_congr rfl fun v _ => ?_
    rcases v with x | x <;> rfl
  rw [e1]
  refine Submodule.sum_mem _ fun m hm => Submodule.smul_mem _ _ (letters_pow_mono ?_ (hprod m m.support))
  exact (MvPolynomial.le_totalDegree hm).trans hq

end letters

end CompanionTheory.WaveGrid.LimSh
end
end

namespace CompanionTheory.WaveGrid

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Formalism.FourierDecayAlt.TBB Formalism.QuantumDeterminants
open CompanionTheory.LimBd.Main (GfPoly SpanPow CoefSmooth CoefCC CoefEig PhZero BetaInfZero ZuckT ZuckDualT Box KDecay
  eigStr_of_steps)
open CompanionTheory.WaveGrid.Coef

def LimSteps : Prop := GfPoly ∧ SpanPow ∧ CoefSmooth ∧ CoefCC ∧ CoefEig ∧ PhZero ∧ BetaInfZero

theorem pStar_box {n : ℕ} {lam lam' : Fin n → ℝ} {e d c : ℝ} (h : lam' ∈ Box lam e) (hd : 0 ≤ d) (hc : e + d ≤ c)
    (y : ℝ) : CompanionTheory.LimBd.Main.PStar lam' d y ≤ PStar lam c y := by
  refine Finset.prod_le_prod₀ (fun _ _ => add_nonneg (abs_nonneg _) hd) fun s _ => ?_
  have h1 := h s
  have h2 := abs_add_le (y + lam s) (lam' s - lam s)
  rw [show y + lam s + (lam' s - lam s) = y + lam' s by ring] at h2
  linarith

theorem kDecay_of_gap {t : ∀ n : ℕ, (Fin n → Bool) → ℝ} (hZ : ZuckT t) (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool)
    {X d h : ℝ} (hX : 0 ≤ X) (hd : 0 ≤ d) (hh : t _ ε + X + 3 * d + 1 < h) : KDecay k r ε (X + d) (h - 2 * d) := by
  refine MainStatements.BetaInf.kDecay_of_zuckT hZ k r ε ⌈X + d⌉₊ _ _ (Nat.le_ceil _) ?_
  have := Nat.ceil_lt_add_one (show 0 ≤ X + d by linarith)
  linarith

theorem gap_mono {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {h h' : ℝ} (hg : PI.ZuckTensor.GapAtLeast ε lam h)
    (hh : h' ≤ h) : PI.ZuckTensor.GapAtLeast ε lam h' := fun a b hab => hh.trans (hg a b hab)

end CompanionTheory.WaveGrid
