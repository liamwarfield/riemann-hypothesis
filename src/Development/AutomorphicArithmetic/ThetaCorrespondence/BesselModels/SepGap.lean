module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.BurGapOfHyp
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomTriangleFiniteDoubleCosets

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.GapArith
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open Formalism.IndefR.Mult IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace UpperTheory.Lit.Bur.Gap

section Num

open GlobalTheory.SignedHC GlobalTheory.PairLift

variable (D : D7) (C : ℝ) (τ : D.what₂.Tau)

theorem b_spec {a : ℕ} (ha : a < D.R.m) : (D.hc τ).b ⟨a, ha⟩ = ((num D C τ).b (a + 1) : ℚ) :=
  (GlobalTheory.SignedHC.GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D C) (cen D C τ)).2.1 ⟨a, ha⟩

theorem e_spec {a : ℕ} (ha : a < D.R.m) : (D.hc τ).e ⟨a, ha⟩ = ((num D C τ).e (a + 1) : ℚ) :=
  (GlobalTheory.SignedHC.GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D C) (cen D C τ)).2.2 ⟨a, ha⟩

theorem v_spec {a : ℕ} (ha : a < D.R.k - 1) : (D.hc τ).v ⟨a, ha⟩ = ((num D C τ).v (a + 2) : ℚ) :=
  (GlobalTheory.SignedHC.GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D C) (cen D C τ)).1 ⟨a, ha⟩

theorem e_add_le_b {l : ℕ} (h1 : 1 ≤ l) (h2 : l + 1 ≤ D.R.m) :
    ((num D C τ).e l : ℚ) + ((D.R.t : ℚ) + 3) / 2 ≤ (num D C τ).b (l + 1) := by
  obtain ⟨a, rfl⟩ : ∃ a, l = a + 1 := ⟨l - 1, by omega⟩
  have h : ((D.R.t : ℚ) + 3) / 2 ≤ (D.hc τ).b ⟨a + 1, by omega⟩ - (D.hc τ).e ⟨a, by omega⟩ :=
    (D.hc τ).gap_eb ⟨a, by omega⟩ (by simpa using h2)
  rw [e_spec D C τ (by omega), b_spec D C τ (by omega)] at h
  linarith

theorem b_lt {l l' : ℕ} (h1 : 1 ≤ l) (h2 : l < l') (h3 : l' ≤ D.R.m) : ((num D C τ).b l : ℚ) < (num D C τ).b l' := by
  exact_mod_cast (num D C τ).b_mono l l' h1 h2 h3

theorem b_le {l l' : ℕ} (h1 : 1 ≤ l) (h2 : l ≤ l') (h3 : l' ≤ D.R.m) : ((num D C τ).b l : ℚ) ≤ (num D C τ).b l' := by
  rcases h2.eq_or_lt with rfl | h
  · exact le_rfl
  · exact (b_lt D C τ h1 h h3).le

theorem cloud_gt {x : ℚ} (h : x ∈ (num D C τ).cloud) : -((num D C τ).b 1 : ℚ) < x := by
  obtain ⟨i, h1, h2, rfl⟩ := GlobalTheory.SignedHC.GridData.mem_cloud.1 h
  have hk : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
  have hm : 2 ≤ D.R.m := D.R.two_le_m
  have hik : i ≤ D.R.k := h2
  have a1 := (D.hc τ).u_last_gt (by omega) (by omega)
  have a2 := (D.hc τ).v_gt_u ⟨D.R.k - 2, by omega⟩
  have e : (⟨(⟨D.R.k - 2, by omega⟩ : Fin (D.R.k - 1)).1 + 1, by simp only; omega⟩ : Fin D.R.k) = ⟨D.R.k - 1, by omega⟩ :=
    Fin.ext (by simp only; omega)
  rw [e] at a2
  rw [v_spec D C τ (by omega)] at a2
  have e0 : (D.hc τ).b ⟨0, by omega⟩ = ((num D C τ).b 1 : ℚ) := b_spec D C τ (by omega)
  rw [e0] at a1
  have e2 : D.R.k - 2 + 2 = D.R.k := by omega
  simp only [e2] at a2
  have a3 : ((num D C τ).v D.R.k : ℚ) ≤ (num D C τ).v i := by
    rcases hik.eq_or_lt with rfl | h
    · exact le_rfl
    · exact_mod_cast ((num D C τ).v_anti i D.R.k h1 h le_rfl).le
  linarith

theorem blockM_bound {a : ℕ} {x : ℚ} (h : x ∈ (num D C τ).blockM a) :
    -((num D C τ).e a : ℚ) - ((D.R.t : ℚ) - 1) / 2 ≤ x ∧ x ≤ -((num D C τ).e a : ℚ) + ((D.R.t : ℚ) - 1) / 2 := by
  have := abs_le.1 (abs_sub_le_of_mem_block (c := -((num D C τ).e a : ℚ)) (t := D.R.t) h)
  constructor <;> linarith [this.1, this.2]


variable {D} in
theorem blockC_gt {a : ℕ} (h1 : 1 ≤ a) (h2 : a ≤ D.R.m) {x : ℚ} (h : x ∈ (num D C τ).blockC a) :
    -((num D C τ).b 1 : ℚ) < x := by
  have hb := abs_le.1 (abs_sub_le_of_mem_block (c := ((num D C τ).cen a : ℚ)) (t := sLen D) h)
  have hn := abs_le.1 ((num_nearMid D C τ) a (Finset.mem_Icc.2 ⟨h1, h2⟩))
  rw [(num D C τ).mid_eq h1] at hn
  have hg : 2 * bigN D ^ 3 + 2 * sLen D + 2 < gap D C := (isLeast_gap D C).1.2.1
  have hg' : 2 * (sLen D : ℚ) + 2 ≤ (gap D C : ℚ) := by
    have : 2 * sLen D + 2 ≤ gap D C := by omega
    exact_mod_cast this
  have hs0 : (0 : ℚ) ≤ sLen D := by positivity
  have hga : ((num D C τ).ga : ℚ) = gap D C := rfl
  have ha : (num D C τ).a a = ((num D C τ).v 2 : ℚ) + 1 / 2 + (((num D C τ).m : ℚ) + 1 - a) * gap D C := by
    rw [GlobalTheory.SignedHC.GridData.a, hga]
  have hma : (a : ℚ) ≤ ((num D C τ).m : ℚ) := by exact_mod_cast h2
  have hmul : (gap D C : ℚ) ≤ (((num D C τ).m : ℚ) + 1 - a) * gap D C := by
    have : (0 : ℚ) ≤ gap D C := by positivity
    nlinarith
  have hv : -((num D C τ).b 1 : ℚ) < (num D C τ).v 2 := by
    have hk : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
    exact cloud_gt D C τ (GlobalTheory.SignedHC.GridData.mem_cloud.2 ⟨2, le_rfl, by show 2 ≤ D.R.k; omega, rfl⟩)
  rw [ha, hga] at hn
  linarith [hb.1, hn.1]

variable {D C τ} in
theorem gapOver_shift {Q : SPar} {g : ℚ} (a : ℚ) (H : GapOver Q g) : GapOver (shift a Q) g := by
  intro x hx y hy hne
  have := H _ (mem_shift.1 hx) _ (mem_shift.1 hy) hne
  simpa using this

end Num

section Gap

open GlobalTheory.SignedHC GlobalTheory.PairLift

def LowsOver (D : D7) (g : ℚ) : Prop :=
  ∀ (τ : D.what₂.Tau) (j : ℕ) (hj : j + 1 < D.R.m), g < (D.hc τ).b ⟨j + 1, hj⟩ - (D.hc τ).b ⟨j, by omega⟩

variable {D : D7} {g : ℚ}

theorem b_gap (C : ℝ) (hS : LowsOver D g) (τ : D.what₂.Tau) {l l' : ℕ} (h1 : 1 ≤ l) (h2 : l < l') (h3 : l' ≤ D.R.m) :
    g < ((num D C τ).b l' : ℚ) - (num D C τ).b l := by
  obtain ⟨a, rfl⟩ : ∃ a, l' = a + 2 := ⟨l' - 2, by omega⟩
  have h := hS τ a (by omega)
  rw [b_spec D C τ (by omega), b_spec D C τ (by omega)] at h
  have := b_le D C τ h1 (show l ≤ a + 1 by omega) (by omega)
  linarith

theorem gap_true (C : ℝ) (hS : LowsOver D g) (τ : D.what₂.Tau) {i j l : ℕ} (hi : i ≤ D.R.m) (hl1 : j + 2 ≤ l)
    (hl2 : l ≤ D.R.m) (hodd : ¬ Even (l - j - 1)) {y : ℚ} (hy : (y, true) ∈ (num D C τ).parD i j) :
    g < |y - -((num D C τ).b l : ℚ)| := by
  have top : -((num D C τ).b 1 : ℚ) < y → g < |y - -((num D C τ).b l : ℚ)| := fun h => by
    have := b_gap C hS τ (show 1 ≤ 1 by omega) (show 1 < l by omega) hl2
    exact lt_abs.2 (Or.inl (by linarith))
  rw [GlobalTheory.SignedHC.GridData.mem_parD] at hy
  rcases hy with ⟨hc, -⟩ | ⟨l', h1, h2, e⟩ | ⟨a, h1, h2, hm, -⟩ | ⟨a, h1, h2, hc, -⟩
  · exact top (cloud_gt D C τ hc)
  · obtain ⟨rfl, es⟩ := Prod.mk.inj e
    have hne : l' ≠ l := by
      rintro rfl
      have : l' ≤ j + 1 ∨ Even (l' - j - 1) := by simpa using es
      rcases this with h | h
      · omega
      · exact hodd h
    rcases lt_or_gt_of_ne hne with h | h
    · have := b_gap C hS τ h1 h hl2
      refine lt_abs.2 (Or.inl (by linarith))
    · have := b_gap C hS τ (show 1 ≤ l by omega) h h2
      refine lt_abs.2 (Or.inr (by linarith))
  · have a0 := (blockM_bound D C τ hm).1
    have a1 := e_add_le_b D C τ h1 (show a + 1 ≤ D.R.m by omega)
    have a2 := b_gap C hS τ (show 1 ≤ a + 1 by omega) (show a + 1 < l by omega) hl2
    refine lt_abs.2 (Or.inl (by linarith))
  · have h0 : (num D C τ).m = D.R.m := rfl
    rw [h0] at h1 h2
    exact top (blockC_gt C τ (by omega) h2 hc)

theorem gapOver_parD (C : ℝ) (hS : LowsOver D g) (τ : D.what₂.Tau) {i : ℕ} (j : ℕ) (hi : i ≤ D.R.m) :
    GapOver ((num D C τ).parD i j) g := by
  have key : ∀ x y : ℚ, (x, false) ∈ (num D C τ).parD i j → (y, true) ∈ (num D C τ).parD i j →
      g < |y - x| := by
    intro x y hx hy
    rw [GlobalTheory.SignedHC.GridData.mem_parD] at hx
    rcases hx with ⟨-, h⟩ | ⟨l, h1, h2, e⟩ | ⟨a, -, -, -, h⟩ | ⟨a, -, -, -, h⟩
    · exact absurd h (by simp)
    · obtain ⟨rfl, es⟩ := Prod.mk.inj e
      have hn : ¬ (l ≤ j + 1 ∨ Even (l - j - 1)) := by simpa using es.symm
      push_neg at hn
      exact gap_true C hS τ hi (by omega) h2 (by simpa using hn.2) hy
    · exact absurd h (by simp)
    · exact absurd h (by simp)
  rintro ⟨x, s⟩ hx ⟨y, s'⟩ hy hne
  cases s <;> cases s'
  · exact absurd rfl hne
  · exact (abs_sub_comm x y) ▸ key x y hx hy
  · exact key y x hy hx
  · exact absurd rfl hne

theorem gapAtLeast_of_gapOver {n : ℕ} {P : SPar} {lam : Fin n → ℝ} {ε : Fin n → Bool}
    (hE : IsEnum (dualPar P) lam ε) (hG : GapOver P g) : Formalism.QuantumDeterminants.GapAtLeast ε lam (g : ℝ) := by
  intro a b hab
  obtain ⟨-, q, hq, hS⟩ := hE
  have mem : ∀ c, (-(q c), ε c) ∈ P := fun c => by
    have h1 : (q c, ε c) ∈ dualPar P := by
      rw [hS]
      exact Finset.mem_image_of_mem (fun a => (q a, ε a)) (Finset.mem_univ c)
    obtain ⟨x, hx, e⟩ := Finset.mem_image.1 h1
    obtain ⟨e1, e2⟩ := Prod.mk.inj e
    have e3 : x = (-(q c), ε c) := Prod.ext (by simp [← e1]) e2
    rw [e3] at hx; exact hx
  have h2 : g < |(-(q a)) - (-(q b))| := by
    have h0 := hG (-(q a), ε a) (mem a) (-(q b), ε b) (mem b) hab
    simpa only using h0
  have e : (-(q a)) - (-(q b)) = -(q a - q b) := by ring
  rw [e, abs_neg] at h2
  rw [hq, hq]
  have h3 : ((g : ℚ) : ℝ) ≤ ((|q a - q b| : ℚ) : ℝ) := by exact_mod_cast h2.le
  push_cast at h3
  exact h3

end Gap

theorem size_arith {k m r : ℕ} (hr : r + 1 = k + m) (hk : m + 3 ≤ k) (hm : 44 ≤ m) {Den Del : ℝ}
    (hDel : (k : ℝ) * (m : ℝ) ^ 10 ≤ Del) (hDen : (k : ℝ) * ((k : ℝ) * (4 * Del)) ≤ Den) :
    120 * ((r + m * (r + 6) : ℕ) : ℝ) ^ 3 ≤ 12 * Den / m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have h1 : r + m * (r + 6) ≤ 6 * m * k := by
    have a1 : r + 6 ≤ 3 * k := by omega
    have a2 : m * (r + 6) ≤ m * (3 * k) := Nat.mul_le_mul_left _ a1
    have a3 : 3 * k ≤ m * (3 * k) := Nat.le_mul_of_pos_left _ (by omega)
    have e : 6 * m * k = m * (3 * k) + m * (3 * k) := by ring
    omega
  have h2 : ((r + m * (r + 6) : ℕ) : ℝ) ≤ 6 * m * k := by exact_mod_cast h1
  have h3 : ((r + m * (r + 6) : ℕ) : ℝ) ^ 3 ≤ (6 * m * k) ^ 3 := pow_le_pow_left₀ (by positivity) h2 3
  have h4 : (44 : ℝ) ≤ m := by exact_mod_cast hm
  have h5 : (44 : ℝ) ^ 6 ≤ (m : ℝ) ^ 6 := pow_le_pow_left₀ (by norm_num) h4 6
  rw [le_div_iff₀ hm0]
  have h6 : (k : ℝ) * ((k : ℝ) * (4 * ((k : ℝ) * (m : ℝ) ^ 10))) ≤ Den := by
    refine le_trans ?_ hDen
    have : (k : ℝ) * (k : ℝ) ≥ 0 := by positivity
    nlinarith
  have h7 : 0 ≤ (k : ℝ) ^ 3 * (m : ℝ) ^ 4 := by positivity
  have h8 : (0 : ℝ) ≤ ((m : ℝ) ^ 6 - 540) * ((k : ℝ) ^ 3 * (m : ℝ) ^ 4) :=
    mul_nonneg (by nlinarith) h7
  have h9 : 120 * ((r + m * (r + 6) : ℕ) : ℝ) ^ 3 * m ≤ 120 * (6 * m * k) ^ 3 * m := by
    exact mul_le_mul_of_nonneg_right (by linarith) hm0.le
  nlinarith

theorem lowsOver_of_sizeRows {D : D7} (large₂ : SizeData₂ D) (hs : SizeRows large₂) :
    LowsOver D (120 * (rankV D D.R.m 0 : ℚ) ^ 3) := by
  intro τ j hj
  obtain ⟨⟨Pm, _, _⟩, _, _, hm44, _⟩ := hs
  have hb : 0 < large₂.sc.b := Real.exp_pos _
  have hL : 0 < large₂.sc.L := Real.rpow_pos_of_pos (by linarith [large₂.sc.one_lt_alt]) _
  have hm0 : (0 : ℝ) < D.R.m := by exact_mod_cast (by omega : 0 < D.R.m)
  have hn : (1 : ℝ) ≤ D.R.n := by
    have : 1 ≤ D.R.n := by
      have h1 := D.R.m_le_f
      have h2 := D.R.two_le_m
      unfold Ranks.n
      omega
    exact_mod_cast this
  have hSc := large₂.Sc_pos
  have hkN : (D.R.k : ℝ) ≤ D.R.N D.R.m := by
    have : D.R.k ≤ D.R.N D.R.m := by unfold Ranks.N; omega
    exact_mod_cast this
  have hDel : (D.R.k : ℝ) * (D.R.m : ℝ) ^ 10 ≤ (D.s.Del : ℝ) :=
    le_trans (mul_le_mul_of_nonneg_right hkN (by positivity)) Pm.Del_ge.2.2.2
  have h1 := Pm.h0_ge.1
  have h2 := (Pm.nodes_gap τ j hj).1
  set Den : ℝ := (D.R.n : ℝ) * (D.R.t : ℝ) ^ 2 * ((D.R.N D.R.m : ℝ) + D.R.t) * large₂.sc.L ^ 2 +
    (D.R.k : ℝ) * (D.R.n : ℝ) ^ 2 * (large₂.Sc + D.R.t + large₂.sc.L) with hDen
  have hk0 : (0 : ℝ) ≤ D.R.k := by positivity
  have hDen1 : (D.R.k : ℝ) * ((D.R.k : ℝ) * (4 * (D.s.Del : ℝ))) ≤ Den := by
    rw [← large₂.Sc_eq, hDen]
    have a1 : 0 ≤ (D.R.n : ℝ) * (D.R.t : ℝ) ^ 2 * ((D.R.N D.R.m : ℝ) + D.R.t) * large₂.sc.L ^ 2 := by positivity
    have a2 : large₂.Sc ≤ (D.R.n : ℝ) ^ 2 * (large₂.Sc + D.R.t + large₂.sc.L) := by
      have : (1 : ℝ) ≤ (D.R.n : ℝ) ^ 2 := one_le_pow₀ hn
      have t0 : (0 : ℝ) ≤ D.R.t := by positivity
      nlinarith
    have a3 := mul_le_mul_of_nonneg_left a2 hk0
    nlinarith
  have hDenPos : 0 < Den := by
    rw [hDen]
    have hkp : (0 : ℝ) < D.R.k := by
      have := D.R.m_add_three_le_k
      exact_mod_cast (by omega : 0 < D.R.k)
    have : 0 < (D.R.k : ℝ) * (D.R.n : ℝ) ^ 2 * (large₂.Sc + D.R.t + large₂.sc.L) := by positivity
    have a1 : 0 ≤ (D.R.n : ℝ) * (D.R.t : ℝ) ^ 2 * ((D.R.N D.R.m : ℝ) + D.R.t) * large₂.sc.L ^ 2 := by positivity
    linarith
  have e : 12 * large₂.sc.b / LevelStarExponents.lStar large₂ = 12 * Den / D.R.m := by
    have : LevelStarExponents.lStar large₂ = (D.R.m : ℝ) * large₂.sc.b / Den := rfl
    rw [this]
    field_simp
  have hr : D.R.r + 1 = D.R.k + D.R.m := by
    have := D.R.m_add_three_le_k
    unfold Ranks.r; omega
  have key := size_arith hr D.R.m_add_three_le_k hm44 hDel hDen1
  have erank : rankV D D.R.m 0 = D.R.r + D.R.m * (D.R.r + 6) := by
    simp [rankV, sLen]
  have t0 : (0 : ℝ) ≤ D.R.t := by positivity
  have h3 : ((120 * (rankV D D.R.m 0 : ℚ) ^ 3 : ℚ) : ℝ) <
      (((D.hc τ).b ⟨j + 1, hj⟩ - (D.hc τ).b ⟨j, by omega⟩ : ℚ) : ℝ) := by
    rw [erank]
    push_cast at key ⊢
    rw [e] at h1
    push_cast at h2
    linarith
  exact_mod_cast h3

theorem fit_gap {D : D7} (large₂ : SizeData₂ D) (hs : SizeRows large₂) {T : Type} {L : LevCh D T} {μ0 : T} (hL : L.Is μ0) {sc : Consts}
    (hsc : sc.cGap = 1) (G : GridData L sc) (MB : DSModel (G.V (.grid D.R.m 0)) (GlobalTheory.SepRows.parRow D sc.cGap D.R.m))
    (τ : D.what₂.Tau) :
    Formalism.QuantumDeterminants.IsHCParam (MB.lam τ) ∧ ∃ h : ℝ, 120 * ((G.V (.grid D.R.m 0)).rank : ℝ) ^ 3 ≤ h ∧
      Formalism.QuantumDeterminants.GapAtLeast (MB.ε τ) (MB.lam τ) h := by
  have hX : (Node.grid D.R.m 0).InRange D.R.m := ⟨le_rfl, Nat.zero_le _⟩
  have hr : (G.V (.grid D.R.m 0)).rank = rankV D D.R.m 0 := (node_isV G hL hX).rank
  have hE : IsEnum (dualPar (parV D sc.cGap D.R.m 0 τ)) (MB.lam τ) (MB.ε τ) := MB.enum τ
  have hG : GlobalTheory.PairLift.GapOver (parV D sc.cGap D.R.m 0 τ) (120 * (rankV D D.R.m 0 : ℚ) ^ 3) := by
    unfold parV
    exact gapOver_shift _ (gapOver_parD sc.cGap (lowsOver_of_sizeRows large₂ hs) τ 0 le_rfl)
  have hE1 : IsEnum (dualPar (parV D 1 D.R.m 0 τ)) (MB.lam τ) (MB.ε τ) := by
    rw [← hsc]
    exact hE
  refine ⟨GlobalTheory.SepRows.isHCParam_dual_parV D D.R.m 0 τ _ _ hr hE1, _, ?_, gapAtLeast_of_gapOver hE hG⟩
  rw [hr]
  push_cast
  exact le_rfl

end UpperTheory.Lit.Bur.Gap

end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace UpperTheory.Lit.Bur

def IsPosCfg {n m : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) (J₀ : Matrix (Fin m) (Fin m) ℂ) (z : Fin n → ℂ) : Prop :=
  1 ≤ m ∧ (Formalism.QuantumDeterminants.herm J z z).re < 0 ∧ ∀ x : Fin m → ℂ, x ≠ 0 → 0 < (Formalism.QuantumDeterminants.herm J₀ x x).re

def HasGap {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) : Prop :=
  ∀ τ, Formalism.QuantumDeterminants.IsHCParam (M.lam τ) ∧ ∃ h : ℝ, 120 * (V.rank : ℝ) ^ 3 ≤ h ∧ Formalism.QuantumDeterminants.GapAtLeast (M.ε τ) (M.lam τ) h

section Model

open Matrix GlobalTheory.RealBessel

theorem burGap_model (hB : BurGapPos) {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}
    (M : DSModel V S) (τ : D.what₂.Tau) {m r : ℕ} {J₀ : Matrix (Fin m) (Fin m) ℂ} {F : Matrix (Fin V.rank) (Fin m) ℂ}
    {e : Matrix (Fin V.rank) (Fin r) ℂ} {z : Fin V.rank → ℂ} (hf : IsFrame (gramAt D V τ) J₀ F e z)
    (hc : IsPosCfg (gramAt D V τ) J₀ z)
    {χ : Matrix (Fin V.rank) (Fin V.rank) ℂ → ℂ} (hχ : IsGeneric (gramAt D V τ) e z χ)
    (hP : Formalism.QuantumDeterminants.IsHCParam (M.lam τ)) {h : ℝ} (hh : 120 * (V.rank : ℝ) ^ 3 ≤ h)
    (hg : Formalism.QuantumDeterminants.GapAtLeast (M.ε τ) (M.lam τ) h)
    {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    {π₀ : Matrix (Fin m) (Fin m) ℂ → Module.End ℂ W} (hπ : IsContIrred (Formalism.QuantumDeterminants.UH J₀) π₀) :
    Module.rank ℂ (besselForms (gramAt D V τ) J₀ F e χ (M.rep τ) π₀ (M.sm τ)) ≤ 1 := by
  have hds := M.ds τ
  obtain ⟨hc', -, hU, hI, -⟩ := id hds
  rw [GlobalTheory.SmVec.sm_eq M τ]
  have hgap : IsGapDS (gramAt D V τ) (M.rep τ) h := by
    refine ⟨M.ε τ, M.lam τ, M.fr τ, M.fr_unit τ, M.fr_gram τ, hP, hg, ?_⟩
    have e1 : (fun g => M.rep τ ((M.fr τ)⁻¹ * g * M.fr τ)) = M.σ τ := by
      funext g
      have hu : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
      show M.σ τ (M.fr τ * ((M.fr τ)⁻¹ * g * M.fr τ) * (M.fr τ)⁻¹) = M.σ τ g
      congr 1
      rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one,
        ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
    rw [e1]
    exact hds
  exact hB _ _ _ _ _ _ _ _ hf hc.1 hc.2.1 hc.2.2 χ hχ _ _ (GlobalTheory.SmVec.isURepOn_trRep (M.fr_unit τ) (M.fr_gram τ) hU)
    (GlobalTheory.SmVec.isIrredOn_trRep (M.fr_unit τ) (M.fr_gram τ) hI) h hh hgap W π₀ hπ

end Model

set_option synthInstance.maxHeartbeats 200000 in
theorem sepLine_gap (hB : BurGapPos) (D : D7) (V A : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (r : ℕ)
    (F : D.what₂.Tau → Matrix (Fin V.rank) (Fin A.rank) ℂ) (e : D.what₂.Tau → Matrix (Fin V.rank) (Fin r) ℂ)
    (z : D.what₂.Tau → Fin V.rank → ℂ) (χ : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ → ℂ) (Wt : D.what₂.Tau → Type)
    [∀ τ, AddCommGroup (Wt τ)] [∀ τ, Module ℂ (Wt τ)] [∀ τ, FiniteDimensional ℂ (Wt τ)]
    (π : ∀ τ, Matrix (Fin A.rank) (Fin A.rank) ℂ → Module.End ℂ (Wt τ))
    (h : ∀ τ, GlobalTheory.RealBessel.IsFrame (gramAt D V τ) (gramAt D A τ) (F τ) (e τ) (z τ) ∧
      GlobalTheory.RealBessel.IsGeneric (gramAt D V τ) (e τ) (z τ) (χ τ) ∧
      GlobalTheory.RealBessel.IsContIrred (Formalism.QuantumDeterminants.UH (gramAt D A τ)) (π τ))
    (hc : ∀ τ, IsPosCfg (gramAt D V τ) (gramAt D A τ) (z τ)) (hg : HasGap M) :
    ∃ ℓ : (∀ τ, Wt τ) → M.Vec → ℂ, ∀ β, SepBes M F e χ π β → ∃ l : ℂ, ∀ x v, β x v = ℓ x v * l := by
  classical
  have hr := fun τ => burGap_model hB M τ (h τ).1 (hc τ) (h τ).2.1 (hg τ).1 (hg τ).2.choose_spec.1 (hg τ).2.choose_spec.2
    (h τ).2.2
  choose b hb using fun τ => rank_le_one_iff.1 (hr τ)
  refine ⟨fun x v => ∏ τ, (b τ).1 (x τ) (v τ), fun β hβ => ?_⟩
  obtain ⟨l, hl⟩ := mul_prod_of_separately (X := fun τ => Wt τ × M.sm τ) (fun τ p => (b τ).1 p.1 p.2)
    (fun p => β (fun τ => (p τ).1) fun τ => (p τ).2) fun τ p => by
      obtain ⟨b', hb', e'⟩ := hβ τ (fun τ => (p τ).1) fun τ => (p τ).2
      obtain ⟨c, hc⟩ := hb τ ⟨b', hb'⟩
      refine ⟨c, fun y => ?_⟩
      have e1 := e' y.1 y.2
      have e2 : b' = c • (b τ).1 := (congrArg Subtype.val hc).symm
      rw [e2] at e1
      refine Eq.trans ?_ e1
      congr 1 <;> funext ρ <;> by_cases hρ : ρ = τ
      · subst hρ; simp
      · simp [Function.update, hρ]
      · subst hρ; simp
      · simp [Function.update, hρ]
  exact ⟨l, fun x v => hl fun τ => (x τ, v τ)⟩

section Cfg

open Matrix
open scoped ComplexOrder

variable {D : D7}

theorem posDef_of_hasSignature_zero_negative {n p : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (h : Formalism.UG.HasSignature G p 0) : G.PosDef := by
  have hp : p = n := by
    obtain ⟨e, _, _⟩ := h
    simpa using (Fintype.card_congr e).symm
  subst hp
  exact Formalism.IndefR.Fin.Lifts.posDef_of_sig G h

theorem besselDatum_middleVector_norm_eq {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (hε : ε ≠ 0) (ρ : ℕ)
    (h : c = 2 * ρ + 1) (τ : D.what₂.Tau) :
    Formalism.QuantumDeterminants.herm (gramAt D B τ) (fun k => tauE D τ ((d.besDat hε ρ h).z k))
      (fun k => tauE D τ ((d.besDat hε ρ h).z k)) = tauE D τ ε := by
  have h1 := congrFun (congrFun d.gram ⟨ρ, by omega⟩) ⟨ρ, by omega⟩
  have h2 : antiDiagonalSignGramMatrix c ε ⟨ρ, by omega⟩ ⟨ρ, by omega⟩ = ε := by
    simp only [antiDiagonalSignGramMatrix, if_true]
    rw [if_pos (by omega)]
  rw [h2] at h1
  refine Eq.trans ?_ (congrArg (tauE D τ) h1)
  show star _ ⬝ᵥ _ = _
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dotProduct, mulVec, gramAt, Matrix.mul_apply, Formalism.UG.cT, transpose_apply, map_apply, map_sum, map_mul,
    Pi.star_apply, HermitianOrthogonalExtensionData.besDat, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show (D.sp.cm.sig : D.host.E →+* D.host.E) (d.a j ⟨ρ, by omega⟩) = star (d.a j ⟨ρ, by omega⟩) from rfl,
    Formalism.IndefR.Eqv.tauE_star]
  simp only [RCLike.star_def]
  ring

theorem topCfg {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (τ : D.what₂.Tau) :
    IsPosCfg (gramAt D (G.V (.grid D.R.m 0)) τ) (gramAt D (G.V (.top 0)) τ) (fun k => tauE D τ (G.besTop.z k)) := by
  have hv := G.sp.P_is D.R.m le_rfl
  refine ⟨?_, ?_, ?_⟩
  · show 1 ≤ (G.sp.P D.R.m).sp.rank
    rw [hv.rank]
    simp only [rankP, nRk]
    omega
  · have e := besselDatum_middleVector_norm_eq (G.rowDec 0 (by have := D.R.two_le_m; omega)) (neg_ne_zero.2 one_ne_zero) ((D.R.m - 2) / 2)
      (by have := D.R.two_le_m; obtain ⟨a, ha⟩ := D.R.m_even; omega) τ
    have e' : (fun k => tauE D τ (G.besTop.z k)) = fun k => tauE D τ
        (((G.rowDec 0 (by have := D.R.two_le_m; omega)).besDat (neg_ne_zero.2 one_ne_zero) ((D.R.m - 2) / 2)
          (by have := D.R.two_le_m; obtain ⟨a, ha⟩ := D.R.m_even; omega)).z k) := rfl
    rw [e', e]
    simp
  · intro x hx
    have hs := hv.sigOK (tauE D τ)
    rw [hv.sig] at hs
    have hP : (gramAt D (G.V (.top 0)) τ).PosDef := posDef_of_hasSignature_zero_negative _ (by
      have e0 : (D.R.m - D.R.m + 1) / 2 = 0 := by omega
      rw [e0] at hs
      exact hs)
    exact hP.re_dotProduct_pos hx

end Cfg

theorem lastVertex_besselDatum_isFrame_isGeneric {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (τ : D.what₂.Tau) :
    GlobalTheory.RealBessel.IsFrame (gramAt D (G.V (.grid D.R.m 0)) τ) (gramAt D (G.V (.top 0)) τ)
      ((frameMat _ _ (G.rowDec 0 (by have := D.R.two_le_m; omega)).ι).map (tauE D τ)) (G.besTop.e.map (tauE D τ))
      (fun k => tauE D τ (G.besTop.z k)) ∧
    GlobalTheory.RealBessel.IsGeneric (gramAt D (G.V (.grid D.R.m 0)) τ) (G.besTop.e.map (tauE D τ)) (fun k => tauE D τ (G.besTop.z k))
      fun u => besChar W.ψ G.besTop (atTau W.θ _ τ u) := by
  refine ⟨GlobalTheory.T.isBesselFrame_of_besselDatum_realPlace D _ _ _ (G.rowDec 0 (by have := D.R.two_le_m; omega)).isom G.besTop τ, ?_⟩
  refine ⟨fun j => -(4 * Real.pi : ℂ) * tauE D τ (G.besTop.c j), fun j => ?_, fun u hu a ha => ?_⟩
  · refine mul_ne_zero (neg_ne_zero.2 (by exact_mod_cast (by positivity : (4 * Real.pi : ℝ) ≠ 0))) ?_
    exact (map_ne_zero _).2 (G.besTop.c_ne j)
  · obtain ⟨t, h1, h2, h3, h4⟩ := GlobalTheory.T.besselCharacter_realPlace_unipotent_eq_trace D W.θ W.θ_is W.ψ _ _ _ G.besTop τ u hu a ha
    show besChar W.ψ G.besTop (atTau W.θ _ τ u) = _
    rw [h4, GlobalTheory.T.standardChar_trace_single_realPlace D W.ψ W.ψ_std W.θ W.θ_is τ t h1 h2, h3, Finset.mul_sum]
    simp only [mul_assoc]


set_option maxHeartbeats 1600000 in
theorem topLine_gap (hB : BurGapPos) (hCT : CoefTensor) (hTS : TopSep) :
    All fun {D} _ _ _ {G} W M => ∀ (S : D.what₂.Tau → SPar) (MB : DSModel (G.V (.grid D.R.m 0)) S), HasGap MB →
      ∃ ℓ : Module.Dual ℂ (coefPlus G W.θ).W → SmT MB → ℂ, ∀ F' ∈ MultT W.θ MB ∅ 1, ∀ Ψ ∈ Cols G W.θ, ∃ l : ℂ,
        ∀ ξ v, Bplus W M (pairVec (coefPlus G W.θ) ξ Ψ) (F' v) = ℓ ξ v * l := by
  intro D hOff T L μ0 hL sc G W M hM S MB hgap
  classical
  have hθ : IsInfFam W.θ := W.θ_is
  obtain ⟨Wt, _, _, _, π, e, hirr, heq⟩ := hCT D (G.V (.top 0)) W.θ (coefPlus G W.θ) hθ (GlobalTheory.TopLineProof.coefPlus_is G hθ)
  obtain ⟨ℓ₀, hℓ₀⟩ := sepLine_gap hB D (G.V (.grid D.R.m 0)) (G.V (.top 0)) S MB _ _ _
    (fun τ k => tauE D τ (G.besTop.z k)) _ Wt π (fun τ => ⟨(lastVertex_besselDatum_isFrame_isGeneric W τ).1, (lastVertex_besselDatum_isFrame_isGeneric W τ).2, hirr τ⟩)
    (fun τ => topCfg G τ) hgap
  have hx : Submodule.span ℂ (Set.range fun x : ∀ τ, Wt τ => e (PiTensorProduct.tprod ℂ x)) = ⊤ := by
    have h1 : (Set.range fun x : ∀ τ, Wt τ => e (PiTensorProduct.tprod ℂ x)) =
        (e : (⨂[ℂ] τ, Wt τ) →ₗ[ℂ] Module.Dual ℂ (coefPlus G W.θ).W) '' Set.range (PiTensorProduct.tprod ℂ) :=
      Set.range_comp _ _
    rw [h1, Submodule.span_image, PiTensorProduct.span_tprod_eq_top, Submodule.map_top, LinearEquiv.range]
  have hy : Submodule.span ℂ (Set.range fun v : MB.Vec => PiTensorProduct.tprod ℂ v) = ⊤ :=
    PiTensorProduct.span_tprod_eq_top
  by_cases h : ∃ F₀ ∈ MultT W.θ MB ∅ 1, ∃ Ψ₀ ∈ Cols G W.θ, ∃ ξ v, Bplus W M (pairVec (coefPlus G W.θ) ξ Ψ₀) (F₀ v) ≠ 0
  · obtain ⟨F₀, hF₀, Ψ₀, hΨ₀, ξ₀, v₀, hne⟩ := h
    refine ⟨fun ξ v => Bplus W M (pairVec (coefPlus G W.θ) ξ Ψ₀) (F₀ v), fun F' hF' Ψ hΨ => ?_⟩
    obtain ⟨⟨b₀, hb₀⟩, hs₀⟩ := hTS D hOff T L μ0 hL sc G W M hM S MB F₀ hF₀ Ψ₀ hΨ₀
    obtain ⟨⟨b, hb⟩, hs⟩ := hTS D hOff T L μ0 hL sc G W M hM S MB F' hF' Ψ hΨ
    obtain ⟨l₀, hl₀⟩ := hℓ₀ _ (hs₀ Wt π e heq)
    obtain ⟨l, hl⟩ := hℓ₀ _ (hs Wt π e heq)
    have key := GlobalTheory.TopLineProof.bilin_prop _ _ hx hy b b₀ ℓ₀ l l₀ (fun x v => (hb _ _).symm.trans (hl x v))
      (fun x v => (hb₀ _ _).symm.trans (hl₀ x v)) fun h0 => hne (by rw [hb₀, h0]; rfl)
    refine ⟨l / l₀, fun ξ v => ?_⟩
    rw [hb]
    beta_reduce
    rw [hb₀, key, LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, mul_comm]
  · push_neg at h
    exact ⟨0, fun F' hF' Ψ hΨ => ⟨0, fun ξ v => by rw [h F' hF' Ψ hΨ ξ v, mul_zero]⟩⟩

theorem factor_gap (hB : BurGapPos) (hCT : CoefTensor) (hTS : TopSep) (hT : RowTower) (D : D7) (large₂ : SizeData₂ D)
    (hsz : SizeRows large₂) (q : OffQ D) (s : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D) (T : Type) (L : LevCh D T) (μ0 : T) (hμ : L.Is μ0)
    (sc : Consts) (hc : sc.cGap = 1) (G : GridData L sc) (W : G.Weil) (M : Vol G) (hM : M.IsRow)
    (M₀ : DSModel (Yc D 0) (parB (Ptw D) 0)) (h₀ : cart M₀ = W.cart (.grid 0 0)) (w : SmT M₀) :
    ∃ a : G.RealVec → Module.Dual ℂ (coefPlus G W.θ).W → ℂ, ∀ t ∈ Rows L W.θ M₀, ∀ Ψ ∈ Cols G W.θ, ∀ Φ,
      ∃ l : ℂ, ∀ ρ ξ, fPsiPhi W M ρ ξ Ψ Φ (t w) = a ρ ξ * l := by
  obtain ⟨S, MB, rfl, -, vec, hv⟩ := hT D q s T L μ0 hμ sc hc G W M hM M₀ h₀ D.R.m le_rfl
  obtain ⟨ℓ, hℓ⟩ := topLine_gap hB hCT hTS D q T L μ0 hμ sc G W M hM _ MB fun τ => Gap.fit_gap large₂ hsz hμ hc G MB τ
  refine ⟨fun ρ ξ => ℓ ξ (vec ρ w), fun t ht Ψ hΨ Φ => ?_⟩
  have ht' : t ∈ MultT W.θ M₀ ∅ 1 := factor_multT_le_empty _ _ _ _ ht
  obtain ⟨F', hF, hF'⟩ := hv t ht' Φ
  obtain ⟨l, hl⟩ := hℓ F' hF Ψ hΨ
  refine ⟨l, fun ρ ξ => ?_⟩
  have e : thetaChi W M ρ Φ (t w) = F' (vec ρ w) := (part_m W M ρ Φ (t w)).symm.trans (hF' ρ w).2
  rw [← hl, ← e]
  rfl

theorem separate_of_burGapPos (hB : BurGapPos) (hCT : CoefTensor) (hTS : TopSep) (hT : RowTower) :
    SizeGap → GoodRows → RowConv → WeakSep → GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.FunctionalsSeparate := by
  intro hS hG hC hW ε CF hCF
  obtain ⟨x₁, hx₁⟩ := hS ε
  obtain ⟨x₂, hx₂⟩ := hW ε CF hCF
  refine ⟨max x₁ x₂, ?_⟩
  intro D large₂ he hx hsz _ Γ _ _ Pl0 T A Ks _ _ _ R hL _ G W hO M hM w hw
  have hSz : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D := hx₁ D large₂ he (le_of_max_le_left hx) hsz
  have hQ : OffQ D := offQ_of_sizeRows hsz
  have hm : 0 < D.R.m := by have := hsz.2.2.2.1; omega
  let M₀ : DSModel (Yc D 0) (parB (Ptw D) 0) := R.MY 0
  have hc : cart M₀ = W.cart (.grid 0 0) := (eq_of_heq (hO.cartY 0 hm)).symm
  have hWS := hx₂ D large₂ he (le_of_max_le_right hx) hsz T R.toLevCh A.μ0 hL G W M hM M₀ hc
  obtain ⟨a, ha⟩ := factor_gap hB hCT hTS hT D large₂ hsz hQ hSz T R.toLevCh A.μ0 hL ⟨1, CF, large₂.sc.b⟩ rfl G W M hM M₀ hc w
  have hCo := hC D hQ hSz T R.toLevCh A.μ0 hL ⟨1, CF, large₂.sc.b⟩ rfl G W M hM M₀ hc
  have hrow : ∀ t ∈ R.EEat R.triv, PiTensorProduct.lift t ∈ Rows R.toLevCh W.θ M₀ := by
    intro t ht
    rw [hO.θ]
    exact hG D Γ Pl0 T A Ks R hL t ht
  have hlift : ∀ t : Mult.MMap (R.MY 0), t ≠ 0 → PiTensorProduct.lift t ≠ 0 := fun t hne h =>
    hne (PiTensorProduct.lift.injective (h.trans (map_zero _).symm))
  by_cases h0 : ∃ t ∈ R.EEat R.triv, t ≠ 0
  · obtain ⟨t₀, ht₀, hne⟩ := h0
    obtain ⟨ρ₀, ξ₀, Ψ₀, hΨ₀, Φ₀, hf₀⟩ := hWS _ (hrow t₀ ht₀) (hlift t₀ hne) w hw
    obtain ⟨l₀, hl₀⟩ := ha _ (hrow t₀ ht₀) Ψ₀ hΨ₀ Φ₀
    have ha0 : a ρ₀ ξ₀ ≠ 0 := fun h => hf₀ (by rw [hl₀, h, zero_mul])
    refine ⟨ρ₀, ξ₀, fun t ht htne => ?_⟩
    obtain ⟨ρ, ξ, Ψ, hΨ, Φ, hf⟩ := hWS _ (hrow t ht) (hlift t htne) w hw
    obtain ⟨l, hl⟩ := ha _ (hrow t ht) Ψ hΨ Φ
    have hl' : l ≠ 0 := fun h => hf (by rw [hl, h, mul_zero])
    refine ⟨Ψ, hΨ, Φ, hCo _ (hrow t ht) w ρ₀ ξ₀ Ψ hΨ Φ, ?_⟩
    intro h
    exact mul_ne_zero ha0 hl' ((hl ρ₀ ξ₀).symm.trans h)
  · push_neg at h0
    exact ⟨Classical.arbitrary _, 0, fun t ht htne => absurd (h0 t ht) htne⟩

end UpperTheory.Lit.Bur

end
