module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightOfSizeBound

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopNodeFormWeightAbsLeLinear
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopNodeFormWeightAbsLeLinear
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.InfSize.WtSize

theorem wtOf_abs_le {n : ℕ} {E : Finset ℚ} {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ x ∈ E, |(x : ℝ)| ≤ B) (i : Fin n) :
    |(((wtOf n E).w i : ℤ) : ℝ)| ≤ B + n + 1 := by
  unfold wtOf
  split_ifs with h
  · show |((⌊GlobalTheory.SignedHC.highestWeight E h.1 i⌋ : ℤ) : ℝ)| ≤ _
    set y := GlobalTheory.SignedHC.highestWeight E h.1 i with hy
    have hy' : (y : ℝ) = (GlobalTheory.SignedHC.descEnum E h.1 i : ℝ) - (((n : ℝ) - 1) / 2 - ((i : ℕ) : ℝ)) := by
      rw [hy]; unfold GlobalTheory.SignedHC.highestWeight; push_cast; ring
    have hd := hB _ (GlobalTheory.SignedHC.descEnum_mem E h.1 i)
    have hi : ((i : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast i.2
    have hi0 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := by positivity
    have f1 : ((⌊y⌋ : ℤ) : ℝ) ≤ y := by exact_mod_cast Int.floor_le y
    have f2 : (y : ℝ) < ⌊y⌋ + 1 := by exact_mod_cast Int.lt_floor_add_one y
    rw [abs_le] at hd ⊢
    constructor <;> linarith [hd.1, hd.2]
  · show |((((0 : Fin n → ℤ) i : ℤ)) : ℝ)| ≤ _
    have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    simp only [Pi.zero_apply, Int.cast_zero, abs_zero]
    linarith

end GlobalTheory.InfSize.WtSize

namespace GlobalTheory.InfSize.WtSize

theorem weightX_abs_le {D : D7} {large₂ : SizeData₂ D} (hs : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂) (τ : D.what₂.Tau) {x : ℚ}
    (hx : x ∈ (num D 1 τ).weightX D.R.m) : |(x : ℝ)| ≤ 5 * large₂.sc.b := by
  obtain ⟨hγb, hb⟩ := GlobalTheory.BigTop.Fun.gap_le_b hs
  have hs' := hs
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hgap, -, -⟩ := hs'
  have hS := large₂.Sc_pos
  have h4 := (isLeast_gap D 1).1.2.1
  have hm := D.R.two_le_m
  have hk := D.R.m_add_three_le_k
  have hNg : bigN D ≤ gap D 1 := by
    have := Nat.le_self_pow (by norm_num : 3 ≠ 0) (bigN D)
    omega
  have htN : D.R.t + 1 ≤ bigN D := by
    unfold bigN
    have := Nat.le_mul_of_pos_left (D.R.t + sLen D + 1) (by omega : 0 < D.R.m)
    omega
  have hsN : sLen D ≤ gap D 1 := by omega
  have hγ0 : (0 : ℝ) ≤ gap D 1 := by positivity
  have hmR : (0 : ℝ) ≤ D.R.m := by positivity
  have htR : (D.R.t : ℝ) + 1 ≤ large₂.sc.b := by
    have h1 : ((D.R.t + 1 : ℕ) : ℝ) ≤ gap D 1 := by exact_mod_cast htN.trans hNg
    push_cast at h1
    linarith
  have hsR : (sLen D : ℝ) ≤ large₂.sc.b := by
    have h1 : (sLen D : ℝ) ≤ gap D 1 := by exact_mod_cast hsN
    linarith
  have hmγ : (0 : ℝ) ≤ ((D.R.m : ℝ) + 1) * gap D 1 := by positivity
  rcases GlobalTheory.SignedHC.GridData.mem_weightX.1 hx with h | h | ⟨i, hi1, hi2, h⟩ | ⟨l, hl1, hl2, h⟩
  · obtain ⟨i, hi, rfl⟩ := GlobalTheory.SignedHC.GridData.mem_tops.1 h
    have ev : (D.hc τ).v ⟨0, by omega⟩ = ((num D 1 τ).v 2 : ℚ) :=
      (GlobalTheory.SignedHC.GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D 1) (cen D 1 τ)).1 ⟨0, by omega⟩
    obtain ⟨v0, v1⟩ := large₂.cloud_v τ ⟨0, by omega⟩
    rw [ev] at v0 v1
    have ha : (num D 1 τ).a i = ((num D 1 τ).v 2 : ℚ) + 1 / 2 + ((D.R.m : ℚ) + 1 - i) * (gap D 1 : ℚ) := rfl
    have hi' : (i : ℝ) ≤ D.R.m := by exact_mod_cast hi
    have hi0 : (0 : ℝ) ≤ i := by positivity
    have v0' : (0 : ℝ) ≤ ((num D 1 τ).v 2 : ℝ) := by exact_mod_cast v0
    have v1' : ((num D 1 τ).v 2 : ℝ) ≤ large₂.Sc := by exact_mod_cast v1
    rw [ha]
    push_cast
    have p1 : (0 : ℝ) ≤ ((D.R.m : ℝ) + 1 - i) * (gap D 1 : ℝ) := mul_nonneg (by linarith) hγ0
    have p2 : ((D.R.m : ℝ) + 1 - i) * (gap D 1 : ℝ) ≤ ((D.R.m : ℝ) + 1) * gap D 1 := by nlinarith
    rw [abs_le]; constructor <;> linarith
  · obtain ⟨i, hi2, hik, rfl⟩ := GlobalTheory.SignedHC.GridData.mem_cloudHalf.1 h
    have hik' : i ≤ D.R.k := hik
    have ev : (D.hc τ).v ⟨i - 2, by omega⟩ = ((num D 1 τ).v (i - 2 + 2) : ℚ) :=
      (GlobalTheory.SignedHC.GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D 1) (cen D 1 τ)).1 ⟨i - 2, by omega⟩
    rw [show i - 2 + 2 = i by omega] at ev
    obtain ⟨v0, v1⟩ := large₂.cloud_v τ ⟨i - 2, by omega⟩
    rw [ev] at v0 v1
    have v0' : (0 : ℝ) ≤ ((num D 1 τ).v i : ℝ) := by exact_mod_cast v0
    have v1' : ((num D 1 τ).v i : ℝ) ≤ large₂.Sc := by exact_mod_cast v1
    unfold GlobalTheory.SignedHC.GridData.vHalf
    push_cast
    rw [abs_le]; constructor <;> linarith
  · obtain ⟨a, ha, rfl⟩ := GlobalTheory.SignedHC.mem_block.1 h
    obtain ⟨c0, c1⟩ := GlobalTheory.BigTop.Fun.cen_bounds hs τ hi1 hi2
    have ec : (num D 1 τ).cen i = cen D 1 τ i := rfl
    have es : (num D 1 τ).s = sLen D := rfl
    rw [ec, es]
    have hs1 : (((sLen D - 1 : ℕ)) : ℝ) ≤ large₂.sc.b := by
      have : ((sLen D - 1 : ℕ) : ℝ) ≤ sLen D := by exact_mod_cast Nat.sub_le _ _
      linarith
    have ha' : (a : ℝ) + 1 ≤ ((sLen D - 1 : ℕ) : ℝ) := by exact_mod_cast ha
    have ha0 : (0 : ℝ) ≤ a := by positivity
    have c0' : (0 : ℝ) ≤ (cen D 1 τ i : ℝ) := by exact_mod_cast c0
    push_cast
    rw [abs_le]; constructor <;> linarith
  · obtain ⟨a, ha, rfl⟩ := GlobalTheory.SignedHC.mem_block.1 h
    have hl2' : l ≤ D.R.m := hl2
    obtain ⟨e0, e1⟩ := GlobalTheory.BigTop.Fun.numE_bounds hs τ (j := l - 1) (by omega)
    rw [show l - 1 + 1 = l by omega] at e0 e1
    have et : (num D 1 τ).t = D.R.t := rfl
    rw [et]
    have ha' : (a : ℝ) + 1 ≤ (D.R.t : ℝ) + 1 := by exact_mod_cast ha
    have ha0 : (0 : ℝ) ≤ a := by positivity
    have e0' : (0 : ℝ) ≤ ((num D 1 τ).e l : ℝ) := by exact_mod_cast e0
    push_cast
    rw [abs_le]; constructor <;> linarith

theorem wt_top_abs_le : ∃ K1 : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂ → ∀ {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc), sc.cGap = 1 → ∀ τ i, |(((wt G (.top D.R.m) τ).w i : ℤ) : ℝ)| ≤ K1 * large₂.sc.b := by
  refine ⟨7, fun D large₂ hs T L sc G hc τ i => ?_⟩
  obtain ⟨hγb, hb⟩ := GlobalTheory.BigTop.Fun.gap_le_b hs
  have h4 := (isLeast_gap D 1).1.2.1
  have hNg : bigN D ≤ gap D 1 := by
    have := Nat.le_self_pow (by norm_num : 3 ≠ 0) (bigN D)
    omega
  have hn := GlobalTheory.DefRank.rank_le_bigN G (.top D.R.m) (show D.R.m ≤ D.R.m from le_rfl)
  have hnb : (((G.V (.top D.R.m)).rank : ℕ) : ℝ) ≤ large₂.sc.b := by
    have : (((G.V (.top D.R.m)).rank : ℕ) : ℝ) ≤ gap D 1 := by exact_mod_cast hn.trans hNg
    linarith
  have e : wt G (.top D.R.m) τ = wtOf (G.V (.top D.R.m)).rank ((num D 1 τ).weightX D.R.m) := by
    show wtOf _ (GlobalTheory.SignedHC.entries (Node.par D sc.cGap (.top D.R.m) τ)) = _
    rw [hc]
    exact congrArg _ (GlobalTheory.SignedHC.entries_plus _)
  rw [e]
  have := wtOf_abs_le (B := 5 * large₂.sc.b) (by linarith) (fun x hx => weightX_abs_le hs τ hx) i
  linarith

end GlobalTheory.InfSize.WtSize

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopNodeFormWeightAbsLeLinearStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topNodeFormWeight_abs_le_linear : ∃ K1 : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂ → ∀ {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc), sc.cGap = 1 → ∀ τ i, |(((wt G (.top D.R.m) τ).w i : ℤ) : ℝ)| ≤ K1 * large₂.sc.b := by
  first | exact @GlobalTheory.InfSize.WtSize.wt_top_abs_le | exact GlobalTheory.InfSize.WtSize.wt_top_abs_le | (intros; apply GlobalTheory.InfSize.WtSize.wt_top_abs_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogBranchingConstantSqLe
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogBranchingConstantSqLe
open Formalism.BasicNotions

namespace GlobalTheory.BranchBound

theorem branching_D1_le_weight_difference (n : ℕ) (lam : DomWeight (n + 1)) (sg : DomWeight n) :
    Formalism.MainNotions.PrimeDegreeVariant.D1 rfl lam sg ≤ lam.w 0 - lam.w (Fin.last n) := by
  let g : ℕ → ℤ := fun k => if hk : k < n + 1 then lam.w ⟨k, hk⟩ else 0
  have h1 : Formalism.MainNotions.PrimeDegreeVariant.D1 rfl lam sg ≤ ∑ i : Fin n, (g i - g (i + 1)) := by
    unfold Formalism.MainNotions.PrimeDegreeVariant.D1
    refine Finset.sum_le_sum fun i _ => ?_
    have a : g i = lam.w ⟨i.1, by omega⟩ := by simp [g, show i.1 < n + 1 by omega]
    have b : g (i + 1) = lam.w ⟨i.1 + 1, by omega⟩ := by simp [g, show i.1 + 1 < n + 1 by omega]
    rw [a, b]
    exact min_le_left _ _
  have h2 : ∑ i : Fin n, (g i - g (i + 1)) = g 0 - g n := by
    rw [Fin.sum_univ_eq_sum_range (fun k => g k - g (k + 1)) n]
    exact Finset.sum_range_sub' g n
  have a0 : g 0 = lam.w 0 := by simp [g]
  have an : g n = lam.w (Fin.last n) := by simp [g]; rfl
  rw [h2, a0, an] at h1
  exact h1

end GlobalTheory.BranchBound

namespace GlobalTheory.BranchBound

theorem finrank_delSq_le (N : ℕ) (lam : DomWeight N) (B : ℝ) (hB : 1 ≤ B)
    (hw : ∀ i, |((lam.w i : ℤ) : ℝ)| ≤ B) :
    (Module.finrank ℂ (delSq ℂ N lam) : ℝ) ≤ (6 * B) ^ (N * N) := by
  have hq := GlobalTheory.WeylDimGL.finrank_delSq ℂ N lam
  rw [GlobalTheory.WeylDimGL.weylDim_eq_prod_Ioi] at hq
  have hr : (Module.finrank ℂ (delSq ℂ N lam) : ℝ) = ∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
      (((lam.w i : ℝ) - (lam.w j : ℝ) + ((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) / (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ))) := by
    have := congrArg (Rat.cast : ℚ → ℝ) hq
    push_cast at this
    exact this
  rw [hr]
  have h6 : (1 : ℝ) ≤ 6 * B := by linarith
  have hf : ∀ i : Fin N, ∀ j ∈ Finset.Ioi i,
      0 ≤ ((lam.w i : ℝ) - (lam.w j : ℝ) + ((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) / (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) ∧
      ((lam.w i : ℝ) - (lam.w j : ℝ) + ((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) / (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) ≤ 6 * B := by
    intro i j hj
    have hij : i < j := Finset.mem_Ioi.mp hj
    have hlt : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hij
    have hanti : (lam.w j : ℝ) ≤ lam.w i := by exact_mod_cast lam.anti hij.le
    have hbi := abs_le.mp (hw i)
    have hbj := abs_le.mp (hw j)
    have hk : (0 : ℝ) < ((j : ℕ) : ℝ) - ((i : ℕ) : ℝ) := by linarith
    constructor
    · apply div_nonneg <;> linarith
    · rw [div_le_iff₀ hk]
      nlinarith
  calc ∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
      (((lam.w i : ℝ) - (lam.w j : ℝ) + ((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) / (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)))
        ≤ ∏ _i : Fin N, (6 * B) ^ N := by
          refine Finset.prod_le_prod₀ (fun i _ => Finset.prod_nonneg fun j hj => (hf i j hj).1) fun i _ => ?_
          calc _ ≤ ∏ _j ∈ Finset.Ioi i, (6 * B) :=
                Finset.prod_le_prod₀ (fun j hj => (hf i j hj).1) fun j hj => (hf i j hj).2
            _ = (6 * B) ^ (Finset.Ioi i).card := Finset.prod_const _
            _ ≤ (6 * B) ^ N := by
                apply pow_le_pow_right₀ h6
                simpa using Finset.card_le_univ (Finset.Ioi i)
      _ = (6 * B) ^ (N * N) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, mul_comm]

end GlobalTheory.BranchBound

namespace GlobalTheory.BranchBound

theorem log_brBd_sq_le : ∀ {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (B : ℝ), 1 ≤ B →
    (N : ℝ) ≤ B → (∀ i, |((lam.w i : ℤ) : ℝ)| ≤ B) →
    Real.log (Formalism.MainNotions.PrimeDegreeVariant.brBd h lam sg ^ 2) ≤ 5 * N * B * Real.log (6 * B) := by
  intro n N h lam sg B hB hN hw
  subst h
  have hNB : ((n + 1 : ℕ) : ℝ) ≤ B := hN
  have hN0 : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by positivity
  have hL : 0 < Real.log (6 * B) := Real.log_pos (by linarith)
  have hR : 0 ≤ 5 * ((n + 1 : ℕ) : ℝ) * B * Real.log (6 * B) := by positivity

  have hsp : lam.spread = lam.w 0 - lam.w (Fin.last n) + ((n + 1 : ℕ) : ℤ) := by
    unfold DomWeight.spread
    rw [dite_eq_left (Nat.succ_pos n)]
    rfl
  have h0 := abs_le.mp (hw 0)
  have hl := abs_le.mp (hw (Fin.last n))
  have hanti : (lam.w (Fin.last n) : ℝ) ≤ lam.w 0 := by exact_mod_cast lam.anti (Fin.zero_le _)
  set s : ℝ := (((2 * lam.spread : ℤ)) : ℝ) with hs
  have hsR : s = 2 * ((lam.w 0 : ℝ) - lam.w (Fin.last n) + ((n + 1 : ℕ) : ℝ)) := by
    rw [hs, hsp]; push_cast; ring
  have hs2 : 2 ≤ s := by rw [hsR]; push_cast at hNB ⊢; linarith
  have hs6 : s ≤ 6 * B := by rw [hsR]; push_cast at hNB ⊢; linarith
  have hls0 : 0 ≤ Real.log s := Real.log_nonneg (by linarith)
  have hls : Real.log s ≤ Real.log (6 * B) := Real.log_le_log (by linarith) hs6

  have hD := branching_D1_le_weight_difference n lam sg
  have hDR : ((Formalism.MainNotions.PrimeDegreeVariant.D1 rfl lam sg : ℤ) : ℝ) ≤ 2 * B := by
    have : ((Formalism.MainNotions.PrimeDegreeVariant.D1 rfl lam sg : ℤ) : ℝ) ≤ (lam.w 0 : ℝ) - lam.w (Fin.last n) := by exact_mod_cast hD
    linarith
  set e : ℝ := ((((n + 1 : ℕ) : ℤ) * Formalism.MainNotions.PrimeDegreeVariant.D1 rfl lam sg : ℤ) : ℝ) with he
  have heR : e = ((n + 1 : ℕ) : ℝ) * ((Formalism.MainNotions.PrimeDegreeVariant.D1 rfl lam sg : ℤ) : ℝ) := by rw [he]; push_cast; ring
  have hel : e * Real.log s ≤ 2 * ((n + 1 : ℕ) : ℝ) * B * Real.log (6 * B) := by
    rcases le_or_gt e 0 with he0 | he0
    · have : e * Real.log s ≤ 0 := mul_nonpos_of_nonpos_of_nonneg he0 hls0
      have : 0 ≤ 2 * ((n + 1 : ℕ) : ℝ) * B * Real.log (6 * B) := by positivity
      linarith
    · have he2 : e ≤ 2 * ((n + 1 : ℕ) : ℝ) * B := by
        rw [heR]; nlinarith
      calc e * Real.log s ≤ (2 * ((n + 1 : ℕ) : ℝ) * B) * Real.log (6 * B) :=
            mul_le_mul he2 hls hls0 (by positivity)
        _ = _ := by ring

  have hc : Formalism.MainNotions.PrimeDegreeVariant.cBd rfl lam sg = s ^ e := rfl
  have hcpos : 0 < s ^ e := Real.rpow_pos_of_pos (by linarith) e
  set d : ℝ := (Module.finrank ℂ (delSq ℂ (n + 1) lam) : ℝ) with hd
  have hd0 : 0 ≤ d := by positivity
  have hb2 : Formalism.MainNotions.PrimeDegreeVariant.brBd rfl lam sg ^ 2 = (s ^ e) ^ 2 * d := by
    unfold Formalism.MainNotions.PrimeDegreeVariant.brBd
    rw [hc, mul_pow, Real.sq_sqrt hd0]
  rw [hb2]
  rcases eq_or_lt_of_le hd0 with hd0' | hdpos
  · rw [← hd0', mul_zero, Real.log_zero]; exact hR
  have hdle := finrank_delSq_le (n + 1) lam B hB hw
  have hlogd : Real.log d ≤ (((n + 1) * (n + 1) : ℕ) : ℝ) * Real.log (6 * B) := by
    rw [← Real.log_pow]
    exact Real.log_le_log hdpos hdle
  have hlogd' : Real.log d ≤ ((n + 1 : ℕ) : ℝ) * B * Real.log (6 * B) := by
    refine hlogd.trans ?_
    push_cast
    have : (((n : ℝ) + 1) * ((n : ℝ) + 1)) ≤ ((n : ℝ) + 1) * B := by
      push_cast at hNB hN0
      exact mul_le_mul_of_nonneg_left hNB hN0
    nlinarith
  rw [Real.log_mul (by positivity) hdpos.ne', Real.log_pow, Real.log_rpow (by linarith)]
  push_cast at hel hlogd' ⊢
  nlinarith

end GlobalTheory.BranchBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogBranchingConstantSqLeStatement
open Formalism.BasicNotions

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_branching_constant_sq_le : ∀ {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (B : ℝ), 1 ≤ B → (N : ℝ) ≤ B → (∀ i, |((lam.w i : ℤ) : ℝ)| ≤ B) → Real.log (Formalism.MainNotions.PrimeDegreeVariant.brBd h lam sg ^ 2) ≤ 5 * N * B * Real.log (6 * B) := by
  first | exact @GlobalTheory.BranchBound.log_brBd_sq_le | exact GlobalTheory.BranchBound.log_brBd_sq_le | (intros; apply GlobalTheory.BranchBound.log_brBd_sq_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanBranchingConstantBound
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.InfSize

theorem bigN_le {D : D7} {large₂ : SizeData₂ D} (hs : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂) : (bigN D : ℝ) ≤ 10 * large₂.sc.b := by
  obtain ⟨-, -, hf, hm, -, hb, -⟩ := hs
  have hd : 1 ≤ D.host.d := D.host.hyp.2.1.one_lt.le
  have hm1 : 1 ≤ D.R.m := by omega
  have hf1 : 1 ≤ D.R.f := le_trans (Nat.one_le_pow _ _ (by omega)) hf
  have hN1 : 1 ≤ D.R.N D.R.m := by unfold Ranks.N; have := D.R.m_add_three_le_k; omega
  have key : bigN D ≤ 10 * (D.R.m * D.R.f * D.R.N D.R.m ^ 2 * D.host.d) := by
    have e1 : D.R.N D.R.m ≤ D.R.N D.R.m ^ 2 := Nat.le_self_pow (by norm_num) _
    have e2 : D.R.m * D.R.N D.R.m ≤ D.R.m * D.R.f * D.R.N D.R.m ^ 2 * D.host.d := by
      calc D.R.m * D.R.N D.R.m = D.R.m * 1 * D.R.N D.R.m * 1 := by ring
        _ ≤ D.R.m * D.R.f * D.R.N D.R.m ^ 2 * D.host.d := by gcongr
    have e3 : bigN D ≤ 10 * (D.R.m * D.R.N D.R.m) := by
      have hk := D.R.m_add_three_le_k
      have s1 : bigN D ≤ D.R.k + D.R.m * (D.R.t + (D.R.k + D.R.m + 6) + 1) := by
        simp only [bigN, sLen, Ranks.r]; gcongr; omega
      have a1 : D.R.k ≤ D.R.m * D.R.k := Nat.le_mul_of_pos_left _ (by omega)
      have a2 : D.R.m * D.R.t ≤ D.R.m * (D.R.m * D.R.t) := Nat.le_mul_of_pos_left _ (by omega)
      have a3 : D.R.m ≤ D.R.m * D.R.m := Nat.le_mul_of_pos_left _ (by omega)
      refine s1.trans ?_
      simp only [Ranks.N]
      nlinarith
    omega
  have : (bigN D : ℝ) ≤ 10 * ((D.R.m * D.R.f * D.R.N D.R.m ^ 2 * D.host.d : ℕ) : ℝ) := by exact_mod_cast key
  push_cast at this
  linarith

theorem log_prod_le {ι : Type} [Fintype ι] (a : ι → ℝ) (c : ℝ) (h0 : ∀ i, 0 ≤ a i) (hc : 0 ≤ c)
    (h : ∀ i, Real.log (a i) ≤ c) : Real.log (∏ i, a i) ≤ Fintype.card ι * c := by
  by_cases hz : ∃ i, a i = 0
  · obtain ⟨i, hi⟩ := hz
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hi, Real.log_zero]
    positivity
  · push_neg at hz
    rw [Real.log_prod (fun i _ => hz i)]
    calc ∑ i, Real.log (a i) ≤ ∑ _i : ι, c := Finset.sum_le_sum fun i _ => h i
      _ = Fintype.card ι * c := by simp

end GlobalTheory.InfSize


open GlobalTheory.InfSize in
theorem GlobalTheory.InfSize.main : ∃ CF0 : ℝ, ∀ CF : ℝ, CF0 ≤ CF → ∃ K0 : ℝ, ∀ ε : ℝ, ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x →
    ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m)
      (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F →
      ∀ ch : Choice R, ch.Is → ch.AtScale CF large₂.sc.b →
        1 ≤ large₂.sc.b ∧ Real.log (∏ τ, Formalism.MainNotions.PrimeDegreeVariant.brBd ch.G.sp.topDec.rank (wt ch.G (.top D.R.m) τ)
          (listedWt ch.G (.grid D.R.m D.R.m) τ) ^ 2) ≤ K0 * D.R.f * (bigN D : ℝ) * large₂.sc.b * Real.log large₂.sc.b := by
  obtain ⟨K1, hK1⟩ := GlobalTheory.T.topNodeFormWeight_abs_le_linear
  set c : ℝ := |K1| + 10 with hc
  set c2 : ℝ := Real.log (6 * c) + 1 with hc2
  refine ⟨0, fun CF _ => ⟨5 * c * c2, fun ε => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch _ hAt => ?_⟩⟩⟩
  have hc10 : 10 ≤ c := by rw [hc]; linarith [abs_nonneg K1]
  have hc2p : 1 ≤ c2 := by
    rw [hc2]; have : 0 ≤ Real.log (6 * c) := Real.log_nonneg (by linarith)
    linarith

  have hL : 1 ≤ large₂.sc.L := by
    unfold Scale.L
    exact Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  have hlb : Real.log large₂.sc.b = large₂.sc.L := Real.log_exp _
  have hb1 : 1 ≤ large₂.sc.b := Real.one_le_exp (by linarith)
  refine ⟨hb1, ?_⟩
  have hlog1 : 1 ≤ Real.log large₂.sc.b := hlb ▸ hL

  have hcg : ch.sc.cGap = 1 := by rw [hAt]
  have hw := hK1 D large₂ hS.size ch.G hcg
  have hNb := bigN_le hS.size
  have hrk : (ch.G.V (.top D.R.m)).rank ≤ bigN D := GlobalTheory.DefRank.rank_le_bigN ch.G (.top D.R.m) (le_refl D.R.m)
  have hrkR : ((ch.G.V (.top D.R.m)).rank : ℝ) ≤ bigN D := by exact_mod_cast hrk
  set B : ℝ := c * large₂.sc.b with hB
  have hB1 : 1 ≤ B := by rw [hB]; nlinarith
  have hlogB : Real.log (6 * B) ≤ c2 * Real.log large₂.sc.b := by
    rw [hB, ← mul_assoc, Real.log_mul (by positivity) (by positivity), hc2]
    have : 0 ≤ Real.log (6 * c) := Real.log_nonneg (by linarith)
    nlinarith
  have hNB : ((ch.G.V (.top D.R.m)).rank : ℝ) ≤ B := by
    rw [hB]; nlinarith
  have hwB : ∀ τ i, |(((wt ch.G (.top D.R.m) τ).w i : ℤ) : ℝ)| ≤ B := fun τ i => by
    refine (hw τ i).trans ?_
    rw [hB]; exact mul_le_mul_of_nonneg_right (by rw [hc]; linarith [le_abs_self K1]) (by linarith)
  have hτ : ∀ τ, Real.log (Formalism.MainNotions.PrimeDegreeVariant.brBd ch.G.sp.topDec.rank (wt ch.G (.top D.R.m) τ)
      (listedWt ch.G (.grid D.R.m D.R.m) τ) ^ 2) ≤ 5 * c * c2 * (bigN D : ℝ) * large₂.sc.b * Real.log large₂.sc.b := by
    intro τ
    refine (GlobalTheory.T.log_branching_constant_sq_le _ _ _ B hB1 hNB (hwB τ)).trans ?_
    have hl6 : 0 ≤ Real.log (6 * B) := Real.log_nonneg (by linarith)
    calc 5 * ((ch.G.V (.top D.R.m)).rank : ℝ) * B * Real.log (6 * B) ≤ 5 * (bigN D : ℝ) * B * Real.log (6 * B) := by
          gcongr
      _ ≤ 5 * (bigN D : ℝ) * B * (c2 * Real.log large₂.sc.b) := by gcongr
      _ = 5 * c * c2 * (bigN D : ℝ) * large₂.sc.b * Real.log large₂.sc.b := by rw [hB]; ring
  have h0 : 0 ≤ 5 * c * c2 * (bigN D : ℝ) * large₂.sc.b * Real.log large₂.sc.b := by positivity
  refine (log_prod_le _ _ (fun τ => sq_nonneg _) h0 hτ).trans (le_of_eq ?_)
  rw [D.what₂.card_Tau]
  ring
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanBranchingConstantBoundStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_branching_constant_bound : ∃ CF0 : ℝ, ∀ CF : ℝ, CF0 ≤ CF → ∃ K0 : ℝ, ∀ ε : ℝ, ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x →
    ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m)
      (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F →
      ∀ ch : Choice R, ch.Is → ch.AtScale CF large₂.sc.b →
        1 ≤ large₂.sc.b ∧ Real.log (∏ τ, Formalism.MainNotions.PrimeDegreeVariant.brBd ch.G.sp.topDec.rank (wt ch.G (.top D.R.m) τ)
          (listedWt ch.G (.grid D.R.m D.R.m) τ) ^ 2) ≤ K0 * D.R.f * (bigN D : ℝ) * large₂.sc.b * Real.log large₂.sc.b := by
  first | exact @GlobalTheory.InfSize.main | exact GlobalTheory.InfSize.main | (intros; apply GlobalTheory.InfSize.main <;> assumption)
end
