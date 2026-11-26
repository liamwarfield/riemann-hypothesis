module

public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BlockBoundUniformiser

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.DigitsOKOfCompat
section -- merged from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.CoarseCLower
section -- merged from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.KappaZeroNonneg
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

theorem depth_num (Y N s t r L CM C : ℝ) (hY : 1 ≤ Y) (hN : 1 ≤ N) (hs0 : 0 ≤ s) (hs : s ≤ N) (ht0 : 0 ≤ t)
    (ht : t ≤ s) (hr : 0 ≤ r) (hL : 0 ≤ L) (hCM : 0 ≤ CM) (hC : 18 * (1 + CM) + 20 ≤ C) :
    Y * (t * (Y * (3 * (s + 2) * r ^ 2 * L) + CM * (3 * (s + 2) * r ^ 2 * L)) + CM * (3 * (s + 2) * r ^ 2 * L)) +
      10 * (s + 1) * (r + 1) * L ≤ C * Y ^ 2 * N ^ 2 * (r + 1) ^ 2 * L := by
  have hA0 : 0 ≤ 3 * (s + 2) * r ^ 2 * L := by positivity
  have hB0 : 0 ≤ N * (r + 1) ^ 2 * L := by
    have : 0 ≤ N := by linarith
    positivity
  have hA : 3 * (s + 2) * r ^ 2 * L ≤ 9 * (N * (r + 1) ^ 2 * L) := by
    have h1 : s + 2 ≤ 3 * N := by linarith
    have h2 : r ^ 2 ≤ (r + 1) ^ 2 := by nlinarith
    have h3 : (s + 2) * r ^ 2 ≤ (3 * N) * (r + 1) ^ 2 := mul_le_mul h1 h2 (by positivity) (by linarith)
    have h4 := mul_le_mul_of_nonneg_right h3 hL
    linarith
  have htA : t * (3 * (s + 2) * r ^ 2 * L) ≤ N * (9 * (N * (r + 1) ^ 2 * L)) :=
    mul_le_mul (by linarith) hA hA0 (by linarith)
  have k1 := mul_le_mul_of_nonneg_left htA (sq_nonneg Y)
  have hYCM : 0 ≤ Y * CM := mul_nonneg (by linarith) hCM
  have k2 := mul_le_mul_of_nonneg_left htA hYCM
  have k3 := mul_le_mul_of_nonneg_left hA hYCM
  have k4 : 10 * (s + 1) * (r + 1) * L ≤ 20 * (N * (r + 1) ^ 2 * L) := by
    have h1 : s + 1 ≤ 2 * N := by linarith
    have h2 : r + 1 ≤ (r + 1) ^ 2 := by nlinarith
    have h3 : (s + 1) * (r + 1) ≤ (2 * N) * (r + 1) ^ 2 := mul_le_mul h1 h2 (by linarith) (by linarith)
    have h4 := mul_le_mul_of_nonneg_right h3 hL
    linarith
  have hY2 : Y ≤ Y ^ 2 := by nlinarith
  have h5 := mul_le_mul_of_nonneg_left hN (sq_nonneg Y)
  have hYN : Y * N ≤ Y ^ 2 * N := mul_le_mul_of_nonneg_right hY2 (by linarith)
  have hY1 : Y ≤ Y ^ 2 * N := by linarith
  have h1P : 1 ≤ Y ^ 2 * N := by nlinarith
  have hc0 : 0 ≤ CM * (9 * (N * (r + 1) ^ 2 * L)) := mul_nonneg hCM (by linarith)
  have m1 := mul_le_mul_of_nonneg_left hYN hc0
  have m2 := mul_le_mul_of_nonneg_left hY1 hc0
  have m3 := mul_le_mul_of_nonneg_left h1P (by linarith : (0:ℝ) ≤ 20 * (N * (r + 1) ^ 2 * L))
  have hP0 : 0 ≤ Y ^ 2 * N * (N * (r + 1) ^ 2 * L) := mul_nonneg (by linarith) hB0
  have m4 := mul_le_mul_of_nonneg_right (by linarith : 29 + 18 * CM ≤ C) hP0
  linarith [k1, k2, k3, k4, m1, m2, m3, m4]

variable {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst}

theorem p25 (hF : HIFacts C0 X) : (25 : ℝ) ≤ (X.L.p : ℝ) := by
  have hmR : (4 : ℝ) ≤ (X.L.m : ℝ) := by exact_mod_cast hF.m4
  nlinarith [hF.p_ge]

theorem lgA_ge_one_facts (hF : HIFacts C0 X) : 1 ≤ lgA X.p X.L.a X.r := by
  unfold lgA
  have h : 0 ≤ Real.logb (X.p : ℝ) (8 * (X.L.a : ℝ) + X.r) := by
    unfold Real.logb
    apply div_nonneg
    · have h' := Real.log_natCast_nonneg (8 * X.L.a + X.r)
      push_cast at h'
      exact h'
    · exact Real.log_natCast_nonneg _
  linarith

theorem kap0A_nonneg_of_hiFacts (hF : HIFacts C0 X) : 0 ≤ kappaZeroExponent X.p X.L.a X.Nt X.r := by
  unfold kappaZeroExponent
  have h : 0 ≤ Real.logb (X.p : ℝ) (X.L.a : ℝ) :=
    div_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)
  exact mul_nonneg (by positivity) h

theorem restDepth_proved {CYb Cde Ck CD Cb Cc : ℝ} (CM C : ℝ) (hCYb : 1 ≤ CYb) (hCM : 0 ≤ CM)
    (hC : 18 * (1 + CM) + 20 ≤ C) (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X) : RestDepth C0 CE1 CE2 X CM C := by
  have hF := hiFacts C0 CYb Cde Ck CD Cb Cc X hCYb hH
  have hY : (1 : ℝ) ≤ X.L.Y := hH.1.1
  have hN : (1 : ℝ) ≤ (X.N₁ : ℝ) := by exact_mod_cast hH.1.2.2.2.2.2.1
  have hs : (X.s : ℝ) ≤ (X.N₁ : ℝ) := by exact_mod_cast (hH.1.2.2.2.2.1 X.j).2
  have ht : ((X.S C0 CE1 CE2).t : ℝ) ≤ (X.s : ℝ) := by
    have : (X.S C0 CE1 CE2).t ≤ X.s := Nat.sub_le _ _
    exact_mod_cast this
  have hL := lgA_ge_one_facts hF
  have hL0 : 0 ≤ lgA X.p X.L.a X.r := by linarith
  have hk := kap0A_nonneg_of_hiFacts hF
  constructor
  · unfold D1r kapS
    positivity
  · have h := depth_num X.L.Y X.N₁ X.s ((X.S C0 CE1 CE2).t : ℝ) X.r (lgA X.p X.L.a X.r) CM C hY hN (Nat.cast_nonneg _) hs
      (Nat.cast_nonneg _) ht (Nat.cast_nonneg _) hL0 hCM hC
    unfold D1r kapS levelPassageLoss depthD
    linarith

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

variable {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst}

structure SegFacts (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst) : Prop where
  hF : HIFacts C0 X
  kP : ∀ i, ((X.r : ℝ) + 1) * ((X.S C0 CE1 CE2).P X.p i : ℝ) ≤ X.L.b'
  P1 : ∀ i, 1 ≤ (X.S C0 CE1 CE2).P X.p i
  PQ : ∀ i, (X.S C0 CE1 CE2).P X.p i ≤ (X.S C0 CE1 CE2).Qj X.p
  La4 : 4 * X.L.La C0 < (X.r : ℝ) + 1
  E0 : 0 ≤ (X.S C0 CE1 CE2).E0
  bTop : ∀ i, ((X.S C0 CE1 CE2).bTop i : ℝ) ≤ 5 / 2 * X.L.b'
  kb : ((X.r : ℝ) + 1) * X.L.b' ≤ (X.L.a : ℝ) / 4
  Y1 : 1 ≤ X.L.Y
  xa0 : 0 ≤ X.xa
  xa : X.xa ≤ 2 * X.L.J0 C0

theorem segFacts {CYb Cde Ck CD Cb Cc : ℝ} (hCYb : 2 ≤ CYb) (hCb : 1 ≤ Cb) (hCD : 0 ≤ CD) (hCE1 : 0 ≤ CE1)
    (hCE2 : 0 ≤ CE2) (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X) : SegFacts C0 CE1 CE2 X := by
  have hF := hiFacts C0 CYb Cde Ck CD Cb Cc X (by linarith) hH
  obtain ⟨h0, -, hxa0, hxa, -, -, -, -, -, -⟩ := hH
  obtain ⟨hY, hpk, ⟨s0, hs0, -⟩, -, hseg, hN1, hm, hLa8, hb0, hbl, hbh, h12, hbw, hYb, hk2, hlog, hde, hpa, hCk,
    hband, hccl0, hccl1, hDLP, hcs, hbig⟩ := h0
  have hk : X.L.k = (X.L.m : ℝ) + 1 := rfl
  have hp25 := p25 hF
  have hp1 : 1 ≤ X.L.p := by
    have : (1 : ℝ) ≤ (X.L.p : ℝ) := by linarith
    exact_mod_cast this
  have hN : (1 : ℝ) ≤ X.L.N := by
    have : 1 ≤ X.L.TT.card := Finset.card_pos.2 ⟨s0, hs0⟩
    show (1 : ℝ) ≤ (X.L.TT.card : ℝ)
    exact_mod_cast this
  have hQ1 : (1 : ℝ) ≤ X.L.Q := by
    show (1 : ℝ) ≤ (X.L.p : ℝ) ^ X.L.G'
    exact one_le_pow₀ (by linarith)
  have hk1 : (1 : ℝ) ≤ X.L.k := by rw [hk]; have : (0 : ℝ) ≤ X.L.m := Nat.cast_nonneg _; linarith
  have hlogb : 0 ≤ Real.logb X.L.p X.L.a := Real.logb_nonneg (by linarith) hF.a1
  have hDLP0 : 0 ≤ X.L.DLP := by
    refine le_trans ?_ hDLP
    have : (0 : ℝ) ≤ (X.L.N1 : ℝ) ^ 5 + X.L.k ^ 3 := by positivity
    have : 0 ≤ X.L.N := by linarith
    positivity
  have hM : (1 : ℝ) ≤ X.L.cs + X.L.N * X.L.ccl + X.L.n' * X.L.ccl := by
    have h1 : 0 ≤ X.L.N * X.L.ccl := mul_nonneg (by linarith) hccl0
    have h2 : 0 ≤ (X.L.n' : ℝ) * X.L.ccl := mul_nonneg (Nat.cast_nonneg _) hccl0
    linarith
  have hkQ : X.L.k * X.L.Q ≤ X.L.b' := by
    refine le_trans ?_ hbig
    have e1 : X.L.k ≤ X.L.k ^ 3 := le_self_pow₀ hk1 (by norm_num)
    have e2 : X.L.Q ≤ X.L.Q ^ 4 := le_self_pow₀ hQ1 (by norm_num)
    calc X.L.k * X.L.Q = 1 * X.L.k * 1 * X.L.Q * 1 * 1 := by ring
      _ ≤ Cb * X.L.k ^ 3 * X.L.N * X.L.Q ^ 4 * (X.L.cs + X.L.N * X.L.ccl + X.L.n' * X.L.ccl) * X.L.Y := by
          gcongr
  have hPQ : ∀ i, (X.S C0 CE1 CE2).P X.p i ≤ (X.S C0 CE1 CE2).Qj X.p := fun i =>
    Nat.pow_le_pow_right (lt_of_lt_of_le zero_lt_one hp1) (Nat.sub_le _ _)
  have hQj : ((X.S C0 CE1 CE2).Qj X.p : ℝ) ≤ X.L.Q := by
    show ((X.L.p ^ segG X.L.TT X.j : ℕ) : ℝ) ≤ (X.L.p : ℝ) ^ X.L.G'
    push_cast
    exact pow_le_pow_right₀ (by exact_mod_cast hp1) (hseg X.j).1
  have hE0 : 0 ≤ (X.S C0 CE1 CE2).E0 := by
    show 0 ≤ errorTermBound CE1 CE2 X.L.p X.L.k X.L.N1 X.L.Q X.L.c X.L.a X.L.b' (X.L.La C0)
    unfold errorTermBound
    have h1 := hF.La0
    have h2 := hF.b0.le
    have h3 : (0 : ℝ) ≤ X.L.k := by linarith
    have h4 : (0 : ℝ) ≤ X.L.Q := by linarith
    positivity
  refine ⟨hF, fun i => ?_, fun i => Nat.one_le_pow _ _ (lt_of_lt_of_le zero_lt_one hp1), hPQ, ?_, hE0, fun i => ?_, ?_, hY, hxa0, hxa⟩
  · have h1 : ((X.S C0 CE1 CE2).P X.p i : ℝ) ≤ X.L.Q :=
      le_trans (by exact_mod_cast hPQ i) hQj
    have h2 : X.L.k * ((X.S C0 CE1 CE2).P X.p i : ℝ) ≤ X.L.b' :=
      le_trans (mul_le_mul_of_nonneg_left h1 (by linarith)) hkQ
    exact h2
  · have hYb2 : 2 ≤ X.L.Yb := le_trans hCYb hYb
    have : 4 * X.L.La C0 ≤ 2 * X.L.Yb * X.L.N * X.L.La C0 := by
      have h0 := hF.La0
      have hYN : 2 ≤ X.L.Yb * X.L.N := by nlinarith only [hYb2, hN]
      have := mul_le_mul_of_nonneg_right hYN h0
      linarith only [this]
    have h2 : 4 * X.L.La C0 < X.L.k := by linarith
    exact h2
  · exact hF.bT_le _ (segPos_mem X.L.TT X.j i)
  · have h1 := hF.b_lt
    have h2 : ((X.r : ℝ) + 1) ^ 2 ≤ (X.L.p : ℝ) := hF.p_ge
    have hm4 : (4 : ℝ) ≤ (X.L.m : ℝ) := by exact_mod_cast hF.m4
    have hb := hF.b0
    have h4 : 4 * ((X.L.m : ℝ) + 1) ≤ (X.L.p : ℝ) := by nlinarith only [h2, hm4]
    have h5 := mul_le_mul_of_nonneg_right h4 hb.le
    have h3 : ((X.L.m : ℝ) + 1) * X.L.b' ≤ (X.L.a : ℝ) / 4 := by linarith only [h5, h1]
    exact h3

section Coarse

variable (hS : SegFacts C0 CE1 CE2 X)
include hS

theorem coarseC_lower (aTop : Fin X.s → ℕ) (b : SegBlock X.s X.r) (hD : DigitsOK X.p (X.S C0 CE1 CE2) aTop b)
    (i : Fin X.s) :
    (aTop i : ℝ) - ((X.r : ℝ) + 1) * ((X.S C0 CE1 CE2).P X.p i : ℝ) ≤
      (coarseC X.p (X.S C0 CE1 CE2) aTop b i : ℝ) * ((X.S C0 CE1 CE2).P X.p i : ℝ) := by
  set P := (X.S C0 CE1 CE2).P X.p i
  have hP : 1 ≤ P := hS.P1 i
  obtain ⟨h1, -, h3⟩ := hD
  obtain ⟨hle, hdvd⟩ := h3 i
  have e : coarseC X.p (X.S C0 CE1 CE2) aTop b i * P = aTop i - ∑ c, b.ry i c := Nat.div_mul_cancel hdvd
  have hρ : ∑ c, b.ry i c ≤ (X.r + 1) * P := by
    calc ∑ c, b.ry i c ≤ ∑ _c : Fin (X.r + 1), P := Finset.sum_le_sum fun c _ => (h1 i c).2.le
      _ = (X.r + 1) * P := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have e2 : ((coarseC X.p (X.S C0 CE1 CE2) aTop b i : ℕ) : ℝ) * (P : ℝ) = (aTop i : ℝ) - ((∑ c, b.ry i c : ℕ) : ℝ) := by
    rw [← Nat.cast_mul, e, Nat.cast_sub hle]
  rw [e2]
  have : ((∑ c, b.ry i c : ℕ) : ℝ) ≤ ((X.r : ℝ) + 1) * (P : ℝ) := by exact_mod_cast hρ
  linarith

theorem coarseA_upper (b : SegBlock X.s X.r) (i : Fin X.s) :
    (coarseA X.p (X.S C0 CE1 CE2) b i : ℝ) * ((X.S C0 CE1 CE2).P X.p i : ℝ) ≤ 5 / 2 * X.L.b' := by
  have h1 : coarseA X.p (X.S C0 CE1 CE2) b i * (X.S C0 CE1 CE2).P X.p i ≤ (X.S C0 CE1 CE2).bTop i :=
    (Nat.div_mul_le_self _ _).trans (Nat.sub_le _ _)
  have h2 : ((coarseA X.p (X.S C0 CE1 CE2) b i * (X.S C0 CE1 CE2).P X.p i : ℕ) : ℝ) ≤ ((X.S C0 CE1 CE2).bTop i : ℝ) := by
    exact_mod_cast h1
  push_cast at h2
  exact h2.trans (hS.bTop i)

theorem win_ge (aTop : Fin X.s → ℕ) (hT : aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA)) (i : Fin X.s) :
    (X.L.a : ℝ) ≤ aTop i := by
  have := (Finset.mem_Icc.1 (Fintype.mem_piFinset.1 hT i)).1
  exact_mod_cast this

end Coarse

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

section Chain

variable {s : ℕ} {p r : ℕ} (S : SegData s) (aTop : Fin s → ℕ) (b : SegBlock s r)

theorem segChain_deg_even (x : Fin (2 * s + 1)) (u : Fin s) (hx : (x : ℕ) = 2 * (u : ℕ)) (hu : S.sigma ≤ (u : ℕ)) :
    (segChain p S aTop b).deg x = b.o u := by
  have hu' := u.isLt
  have hne : (x : ℕ) ≠ 2 * s := by omega
  have ht : topOf x hne = u := Fin.ext (by simp [topOf]; omega)
  simp only [segChain]
  rw [dite_eq_right hne, if_pos (by omega), ht, if_neg (by omega)]

theorem segChain_deg_odd (x : Fin (2 * s + 1)) (u : Fin s) (hx : (x : ℕ) = 2 * (u : ℕ) + 1)
    (hu : S.sigma ≤ (u : ℕ)) : (segChain p S aTop b).deg x = coarseC p S aTop b u := by
  have hu' := u.isLt
  have hne : (x : ℕ) ≠ 2 * s := by omega
  have ht : topOf x hne = u := Fin.ext (by simp [topOf]; omega)
  simp only [segChain]
  rw [dite_eq_right hne, if_neg (by omega), ht, if_neg (by omega)]

theorem segChain_deg_last (x : Fin (2 * s + 1)) (hx : (x : ℕ) = 2 * s) : (segChain p S aTop b).deg x = b.oPlus := by
  simp only [segChain]
  rw [dite_eq_left hx]

end Chain

theorem mem_levels_iff {N : ℕ} (G : Formalism.GM.M.BlockData N) (x : (Fin G.T.t → ℕ) × ℕ) :
    x ∈ levels G ↔ G.LevelOK x.1 x.2 := by
  simp only [levels, Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    rw [Finset.mem_product, Fintype.mem_piFinset]
    refine ⟨fun i => ?_, ?_⟩
    · rw [Finset.mem_range, Nat.lt_succ_iff]
      exact (h.1 i).1.trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _))
    · rw [Finset.mem_range, Nat.lt_succ_iff]
      exact h.2.trans (min_le_right _ _)

variable {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst}

theorem uTop_ge (i : Fin (X.S C0 CE1 CE2).t) : (X.S C0 CE1 CE2).sigma ≤ ((uTop (X.S C0 CE1 CE2) i : Fin X.s) : ℕ) := by
  simp only [uTop]
  omega

theorem levelOK_gB (aTop : Fin X.s → ℕ) (aPlus : ℕ) (b : SegBlock X.s X.r) (x : Lv C0 CE1 CE2 X) :
    (gB C0 CE1 CE2 X aTop aPlus b).LevelOK x.1 x.2 ↔
      (∀ i : Fin (X.S C0 CE1 CE2).t, x.1 i ≤ b.o (uTop (X.S C0 CE1 CE2) i) ∧
        x.1 i ≤ coarseC X.p (X.S C0 CE1 CE2) aTop b (uTop (X.S C0 CE1 CE2) i)) ∧
      x.2 ≤ min b.oPlus (X.S C0 CE1 CE2).bPlus := by
  simp only [Formalism.GM.M.BlockData.LevelOK, gB, gmB, blockData, BlockData.withMargin, blockBase, gmL, gmT, segTies]
  refine and_congr (forall_congr' fun i => ?_) ?_
  · have hi := (uTop (X.S C0 CE1 CE2) i).isLt
    rw [segChain_deg_even (X.S C0 CE1 CE2) aTop b
        ⟨min (2 * ((uTop (X.S C0 CE1 CE2) i : Fin X.s) : ℕ)) (2 * X.s + 1 - 1), by omega⟩ (uTop _ i)
        (by simp only; omega) (uTop_ge i),
      segChain_deg_odd (X.S C0 CE1 CE2) aTop b
        ⟨min (2 * ((uTop (X.S C0 CE1 CE2) i : Fin X.s) : ℕ) + 1) (2 * X.s + 1 - 1), by omega⟩ (uTop _ i)
        (by simp only; omega) (uTop_ge i)]
  · rw [segChain_deg_last (X.S C0 CE1 CE2) aTop b ⟨2 * X.s, by omega⟩ rfl]

theorem mem_lv (aTop : Fin X.s → ℕ) (b : SegBlock X.s X.r) (x : Lv C0 CE1 CE2 X) :
    x ∈ lv C0 CE1 CE2 X aTop b ↔
      (∀ i : Fin (X.S C0 CE1 CE2).t, x.1 i ≤ b.o (uTop (X.S C0 CE1 CE2) i) ∧
        x.1 i ≤ coarseC X.p (X.S C0 CE1 CE2) aTop b (uTop (X.S C0 CE1 CE2) i)) ∧
      x.2 ≤ min b.oPlus (X.S C0 CE1 CE2).bPlus :=
  (mem_levels_iff (gB C0 CE1 CE2 X aTop 0 b) x).trans (levelOK_gB aTop 0 b x)

theorem digitsOK_of_compat {dl : DCl X} {aTop : Fin X.s → ℕ} (hc : Compat C0 CE1 CE2 X dl aTop)
    (b : SegBlock X.s X.r) (hb : (b.rz, b.ry) = dl) : DigitsOK X.p (X.S C0 CE1 CE2) aTop b := by
  subst hb
  simpa only [Compat, DigitsOK, ColumnSystems.digitBlock] using hc

theorem mem_cbox' {dl : DCl X} {aTop : Fin X.s → ℕ} (ha : aTop ∈ cbox C0 CE1 CE2 X dl) :
    aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA) ∧ Compat C0 CE1 CE2 X dl aTop := by
  simp only [cbox, Finset.mem_filter] at ha
  exact ha

theorem idx_sub (hS : SegFacts C0 CE1 CE2 X) (dl : DCl X) (aTop aTop' : Fin X.s → ℕ)
    (ha : aTop ∈ cbox C0 CE1 CE2 X dl) (ha' : aTop' ∈ cbox C0 CE1 CE2 X dl) :
    idx C0 CE1 CE2 X dl aTop ⊆ idx C0 CE1 CE2 X dl aTop' := by
  haveI : NeZero X.r := ⟨X.hm⟩
  have hF := hS.hF
  have hwin : ∀ i, X.L.a ≤ aTop' i := fun i =>
    (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp (mem_cbox' ha').1 i)).1
  have hp : (25:ℝ) ≤ X.L.p := by
    have h1 := hF.p_ge
    have h2 : (4:ℝ) ≤ X.L.m := by exact_mod_cast hF.m4
    nlinarith
  have hb0 := hF.b0
  have hblt := hF.b_lt
  have h25 : 25 * X.L.b' < X.L.a := by nlinarith
  rintro ⟨b, x⟩ hbx
  simp only [idx, Finset.mem_sigma, Finset.mem_filter] at hbx ⊢
  obtain ⟨⟨hk, hdl⟩, hx⟩ := hbx
  rw [mem_keptSet] at hk ⊢
  have hD' := digitsOK_of_compat (mem_cbox' ha').2 b hdl
  have hsum : ∀ i, ((∑ c, b.ry i c : ℕ) : ℝ) < X.L.b' := by
    intro i
    have h1 : ∑ c, b.ry i c < ∑ _c : Fin (X.r + 1), SegData.P X.p (X.S C0 CE1 CE2) i :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun c _ => (hD'.1 i c).2)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h1
    have h2 := hS.kP i
    have h3 : ((∑ c, b.ry i c : ℕ) : ℝ) < (((X.r + 1) * SegData.P X.p (X.S C0 CE1 CE2) i : ℕ) : ℝ) := by
      exact_mod_cast h1
    push_cast at h3 ⊢
    linarith
  have hC : ∀ i, (coarseC X.p (X.S C0 CE1 CE2) aTop' b i : ℝ) * (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ) =
      (aTop' i : ℝ) - ((∑ c, b.ry i c : ℕ) : ℝ) := by
    intro i
    have h1 := Nat.div_mul_cancel (hD'.2.2 i).2
    have h2 := (hD'.2.2 i).1
    unfold coarseC
    rw [← Nat.cast_sub h2, ← Nat.cast_mul, h1]
  have hAC : ∀ i, coarseA X.p (X.S C0 CE1 CE2) b i ≤ coarseC X.p (X.S C0 CE1 CE2) aTop' b i := by
    intro i
    have h1 := hS.bTop i
    have h2 := hsum i
    have h3 : (X.L.a : ℝ) ≤ aTop' i := by exact_mod_cast hwin i
    have h4 : (((X.S C0 CE1 CE2).bTop i + ∑ c, b.ry i c : ℕ) : ℝ) < aTop' i := by
      push_cast at h2 ⊢
      linarith
    have h5 : (X.S C0 CE1 CE2).bTop i + ∑ c, b.ry i c < aTop' i := by exact_mod_cast h4
    unfold coarseA coarseC
    exact Nat.div_le_div_right (by omega)
  have hSG : ∀ i, ((b.sg i : ℕ) : ℝ) ≤ 2 * (X.S C0 CE1 CE2).La *
      ((SegData.A0 X.p (X.S C0 CE1 CE2) : ℤ) : ℝ) / ((X.r : ℝ) + 1) →
      b.sg i ≤ coarseC X.p (X.S C0 CE1 CE2) aTop' b i := by
    intro i h
    have hP1 : (1:ℝ) ≤ (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ) := by exact_mod_cast hS.P1 i
    have hPQ : (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ) ≤ (SegData.Qj X.p (X.S C0 CE1 CE2) : ℝ) := by
      exact_mod_cast hS.PQ i
    have hQ : (0:ℝ) < (SegData.Qj X.p (X.S C0 CE1 CE2) : ℝ) := by linarith
    have hA : ((SegData.A0 X.p (X.S C0 CE1 CE2) : ℤ) : ℝ) ≤ (X.L.a : ℝ) / (SegData.Qj X.p (X.S C0 CE1 CE2) : ℝ) := by
      have h1 := Int.floor_le ((((X.S C0 CE1 CE2).a : ℝ) - (X.S C0 CE1 CE2).E0) /
        (SegData.Qj X.p (X.S C0 CE1 CE2) : ℝ))
      have h2 := hS.E0
      have h3 : (((X.S C0 CE1 CE2).a : ℝ) - (X.S C0 CE1 CE2).E0) / (SegData.Qj X.p (X.S C0 CE1 CE2) : ℝ) ≤
          (X.L.a : ℝ) / (SegData.Qj X.p (X.S C0 CE1 CE2) : ℝ) := by
        apply div_le_div_of_nonneg_right _ hQ.le
        show (X.L.a : ℝ) - (X.S C0 CE1 CE2).E0 ≤ X.L.a
        linarith
      exact h1.trans h3
    have hLa0 : 0 ≤ (X.S C0 CE1 CE2).La := hF.La0
    have hLa4 : 4 * (X.S C0 CE1 CE2).La < (X.r : ℝ) + 1 := hS.La4
    have hr : (0:ℝ) < (X.r : ℝ) + 1 := by positivity
    have hq0 : 0 ≤ (X.L.a : ℝ) / (SegData.Qj X.p (X.S C0 CE1 CE2) : ℝ) := by positivity
    have e1 : 2 * (X.S C0 CE1 CE2).La * ((SegData.A0 X.p (X.S C0 CE1 CE2) : ℤ) : ℝ) / ((X.r : ℝ) + 1) ≤
        2 * (X.S C0 CE1 CE2).La * ((X.L.a : ℝ) / (SegData.Qj X.p (X.S C0 CE1 CE2) : ℝ)) / ((X.r : ℝ) + 1) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hA (by linarith)) hr.le
    have e2 : 2 * (X.S C0 CE1 CE2).La * ((X.L.a : ℝ) / (SegData.Qj X.p (X.S C0 CE1 CE2) : ℝ)) / ((X.r : ℝ) + 1) ≤
        ((X.L.a : ℝ) / (SegData.Qj X.p (X.S C0 CE1 CE2) : ℝ)) / 2 := by
      rw [div_le_div_iff₀ hr (by norm_num)]
      nlinarith
    have e3 : ((b.sg i : ℕ) : ℝ) * (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ) ≤ (X.L.a : ℝ) / 2 := by
      have h0 : ((b.sg i : ℕ) : ℝ) ≤ ((X.L.a : ℝ) / (SegData.Qj X.p (X.S C0 CE1 CE2) : ℝ)) / 2 :=
        h.trans (e1.trans e2)
      calc ((b.sg i : ℕ) : ℝ) * (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ)
          ≤ ((X.L.a : ℝ) / (SegData.Qj X.p (X.S C0 CE1 CE2) : ℝ)) / 2 * (SegData.Qj X.p (X.S C0 CE1 CE2) : ℝ) :=
            mul_le_mul h0 hPQ (by linarith) (by positivity)
        _ = (X.L.a : ℝ) / 2 := by field_simp
    have e4 : (X.L.a : ℝ) - X.L.b' < (aTop' i : ℝ) - ((∑ c, b.ry i c : ℕ) : ℝ) := by
      have h1 := hsum i
      have h2 : (X.L.a : ℝ) ≤ aTop' i := by exact_mod_cast hwin i
      linarith
    have e5 : ((b.sg i : ℕ) : ℝ) * (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ) <
        (coarseC X.p (X.S C0 CE1 CE2) aTop' b i : ℝ) * (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ) := by
      rw [hC i]
      linarith
    have e6 : ((b.sg i : ℕ) : ℝ) < (coarseC X.p (X.S C0 CE1 CE2) aTop' b i : ℝ) :=
      lt_of_mul_lt_mul_right e5 (by linarith)
    exact_mod_cast e6.le
  refine ⟨⟨⟨hD', hk.2.1, fun i hi => ?_, hk.2.2.2⟩, hdl⟩, ?_⟩
  · obtain ⟨h1, h2, _, h4, h5⟩ := hk.2.2.1 i hi
    exact ⟨h1, h2, hSG i h5, h4, h5⟩
  · have hx' := (mem_lv aTop b x).mp hx
    refine (mem_lv aTop' b x).mpr ⟨fun i => ⟨(hx'.1 i).1, ?_⟩, hx'.2⟩
    exact (hx'.1 i).1.trans (((hk.2.1 _ (uTop_ge i)).1).trans (hAC _))

theorem restFree_proved (hS : SegFacts C0 CE1 CE2 X) : RestFree C0 CE1 CE2 X := fun dl _ aTop ha aTop' ha' =>
  Finset.Subset.antisymm (idx_sub hS dl aTop aTop' ha ha') (idx_sub hS dl aTop' aTop ha' ha)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

theorem ratio_num (x y r : ℕ) (hx : 1 ≤ x) (hxy : x ≤ y) (h : (r : ℝ) * ((y : ℝ) - x) ≤ 3 * x) :
    (((y + r).choose r : ℕ) : ℝ) ≤ Real.exp 3 * (((x + r).choose r : ℕ) : ℝ) := by
  have h1 := choose_ratio r x y hx hxy
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  have hq : (y : ℝ) / x ≤ Real.exp (((y : ℝ) - x) / x) := by
    have := Real.add_one_le_exp (((y : ℝ) - x) / x)
    have e : ((y : ℝ) - x) / x + 1 = (y : ℝ) / x := by field_simp; ring
    linarith
  have hq0 : 0 ≤ (y : ℝ) / x := by positivity
  have h2 : ((y : ℝ) / x) ^ r ≤ Real.exp 3 := by
    calc ((y : ℝ) / x) ^ r ≤ Real.exp (((y : ℝ) - x) / x) ^ r := pow_le_pow_left₀ hq0 hq r
      _ = Real.exp ((r : ℝ) * (((y : ℝ) - x) / x)) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp 3 := by
          apply Real.exp_le_exp.2
          rw [← mul_div_assoc, div_le_iff₀ hx0]
          exact h
  calc (((y + r).choose r : ℕ) : ℝ) ≤ ((y : ℝ) / x) ^ r * (((x + r).choose r : ℕ) : ℝ) := h1
    _ ≤ Real.exp 3 * (((x + r).choose r : ℕ) : ℝ) := by gcongr

variable {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst}

theorem topA_spec (dl : DCl X) (aTop : Fin X.s → ℕ) (ha : aTop ∈ cbox C0 CE1 CE2 X dl) (l : Fin X.s) :
    topA C0 CE1 CE2 X dl l ∈ X.winA ∧ ∑ c, dl.2 l c ≤ topA C0 CE1 CE2 X dl l ∧
      (X.S C0 CE1 CE2).P X.p l ∣ topA C0 CE1 CE2 X dl l - ∑ c, dl.2 l c ∧ aTop l ≤ topA C0 CE1 CE2 X dl l := by
  classical
  obtain ⟨hT, hc⟩ := mem_cbox' ha
  have hmem : aTop l ∈ X.winA.filter fun x => ∑ c, dl.2 l c ≤ x ∧ (X.S C0 CE1 CE2).P X.p l ∣ x - ∑ c, dl.2 l c := by
    simp only [Finset.mem_filter]
    exact ⟨Fintype.mem_piFinset.1 hT l, hc.2.2 l⟩
  unfold topA
  obtain ⟨x, hxF, hx⟩ := Finset.exists_mem_eq_sup _ ⟨_, hmem⟩ (id : ℕ → ℕ)
  have hle : aTop l ≤ (X.winA.filter fun x => ∑ c, dl.2 l c ≤ x ∧
      (X.S C0 CE1 CE2).P X.p l ∣ x - ∑ c, dl.2 l c).sup id := Finset.le_sup (f := id) hmem
  rw [hx] at hle ⊢
  simp only [Finset.mem_filter] at hxF
  exact ⟨hxF.1, hxF.2.1, hxF.2.2, hle⟩

theorem upd_mem (dl : DCl X) (aTop : Fin X.s → ℕ) (ha : aTop ∈ cbox C0 CE1 CE2 X dl) (i : Fin (X.S C0 CE1 CE2).t) :
    upd C0 CE1 CE2 X dl aTop i ∈ cbox C0 CE1 CE2 X dl := by
  classical
  obtain ⟨hT, hc⟩ := mem_cbox' ha
  have hs := topA_spec dl aTop ha (uTop (X.S C0 CE1 CE2) i)
  unfold cbox
  simp only [Finset.mem_filter]
  refine ⟨Fintype.mem_piFinset.2 fun l => ?_, ⟨hc.1, hc.2.1, fun l => ?_⟩⟩
  · unfold upd
    by_cases h : l = uTop (X.S C0 CE1 CE2) i
    · subst h; rw [Function.update_self]; exact hs.1
    · rw [Function.update_of_ne h]; exact Fintype.mem_piFinset.1 hT l
  · unfold upd
    by_cases h : l = uTop (X.S C0 CE1 CE2) i
    · subst h; rw [Function.update_self]; exact ⟨hs.2.1, hs.2.2.1⟩
    · rw [Function.update_of_ne h]; exact hc.2.2 l

theorem prod_ratio {ι : Type*} [DecidableEq ι] (s : Finset ι) (u : ι) (hu : u ∈ s) (f g : ι → ℝ) (K : ℝ)
    (hg : ∀ l, 0 ≤ g l) (hfg : ∀ l ∈ s, l ≠ u → f l = g l) (hK : f u ≤ K * g u) :
    ∏ l ∈ s, f l ≤ K * ∏ l ∈ s, g l := by
  rw [← Finset.mul_prod_erase s f hu, ← Finset.mul_prod_erase s g hu]
  have e : ∏ l ∈ s.erase u, f l = ∏ l ∈ s.erase u, g l :=
    Finset.prod_congr rfl fun l hl => hfg l (Finset.mem_of_mem_erase hl) (Finset.ne_of_mem_erase hl)
  rw [e]
  have hP : 0 ≤ ∏ l ∈ s.erase u, g l := Finset.prod_nonneg fun l _ => hg l
  calc f u * ∏ l ∈ s.erase u, g l ≤ (K * g u) * ∏ l ∈ s.erase u, g l := mul_le_mul_of_nonneg_right hK hP
    _ = K * (g u * ∏ l ∈ s.erase u, g l) := by ring

theorem ratioCondition_of_segFacts (hS : SegFacts C0 CE1 CE2 X) : RestRatio C0 CE1 CE2 X := by
  classical
  intro dl _ aTop ha i
  refine ⟨upd_mem dl aTop ha i, ?_⟩
  obtain ⟨hT, hc⟩ := mem_cbox' ha
  have hs := topA_spec dl aTop ha (uTop (X.S C0 CE1 CE2) i)
  have hD : DigitsOK X.p (X.S C0 CE1 CE2) aTop (Formalism.MainNotions.ColumnSystems.digitBlock dl.1 dl.2) := hc
  have hc2 := upd_mem dl aTop ha i
  have hD2 : DigitsOK X.p (X.S C0 CE1 CE2) (upd C0 CE1 CE2 X dl aTop i) (Formalism.MainNotions.ColumnSystems.digitBlock dl.1 dl.2) :=
    (mem_cbox' hc2).2
  obtain ⟨x, hx⟩ : ∃ x, x = coarseC X.p (X.S C0 CE1 CE2) aTop (Formalism.MainNotions.ColumnSystems.digitBlock dl.1 dl.2)
      (uTop (X.S C0 CE1 CE2) i) := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = coarseC X.p (X.S C0 CE1 CE2) (upd C0 CE1 CE2 X dl aTop i)
      (Formalism.MainNotions.ColumnSystems.digitBlock dl.1 dl.2) (uTop (X.S C0 CE1 CE2) i) := ⟨_, rfl⟩
  have hupdu : upd C0 CE1 CE2 X dl aTop i (uTop (X.S C0 CE1 CE2) i) = topA C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i) := by
    unfold upd
    exact Function.update_self _ _ _
  have hP1 : (1 : ℝ) ≤ ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) := by exact_mod_cast hS.P1 _
  have hkP := hS.kP (uTop (X.S C0 CE1 CE2) i)
  have hkb := hS.kb
  have hb0 := hS.hF.b0
  have hr0 : (0 : ℝ) ≤ (X.r : ℝ) := Nat.cast_nonneg _
  have hxP : (x : ℝ) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) =
      (aTop (uTop (X.S C0 CE1 CE2) i) : ℝ) -
        ((∑ c, (Formalism.MainNotions.ColumnSystems.digitBlock dl.1 dl.2 : SegBlock X.s X.r).ry (uTop (X.S C0 CE1 CE2) i) c : ℕ) : ℝ) := by
    have e := Nat.div_mul_cancel (hD.2.2 (uTop (X.S C0 CE1 CE2) i)).2
    rw [hx, ← Nat.cast_mul]
    unfold coarseC
    rw [e, Nat.cast_sub (hD.2.2 (uTop (X.S C0 CE1 CE2) i)).1]
  have hyP : (y : ℝ) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) =
      (topA C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i) : ℝ) -
        ((∑ c, (Formalism.MainNotions.ColumnSystems.digitBlock dl.1 dl.2 : SegBlock X.s X.r).ry (uTop (X.S C0 CE1 CE2) i) c : ℕ) : ℝ) := by
    have e := Nat.div_mul_cancel (hD2.2.2 (uTop (X.S C0 CE1 CE2) i)).2
    rw [hy, ← Nat.cast_mul]
    unfold coarseC
    rw [e, Nat.cast_sub (hD2.2.2 (uTop (X.S C0 CE1 CE2) i)).1, hupdu]
  have hlow := coarseC_lower hS aTop _ hD (uTop (X.S C0 CE1 CE2) i)
  rw [← hx] at hlow
  have haw := win_ge hS aTop hT (uTop (X.S C0 CE1 CE2) i)
  have hxy : x ≤ y := by
    have h1 : (x : ℝ) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) ≤
        (y : ℝ) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) := by
      rw [hxP, hyP]
      have : (aTop (uTop (X.S C0 CE1 CE2) i) : ℝ) ≤ (topA C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i) : ℝ) := by
        exact_mod_cast hs.2.2.2
      linarith
    have := le_of_mul_le_mul_right h1 (by linarith)
    exact_mod_cast this
  have hxP2 : (X.L.a : ℝ) * (3 / 4) ≤ (x : ℝ) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) := by
    nlinarith
  have hx1 : 1 ≤ x := by
    have h2 : ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) ≤ (X.L.a : ℝ) * (3 / 4) := by nlinarith
    have h4 : (1 : ℝ) ≤ (x : ℝ) := by
      by_contra hcn
      push Not at hcn
      have : (x : ℝ) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) <
          1 * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) :=
        mul_lt_mul_of_pos_right hcn (by linarith)
      linarith
    exact_mod_cast h4
  have hnum : (X.r : ℝ) * ((y : ℝ) - x) ≤ 3 * x := by
    have htop : (topA C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i) : ℝ) ≤
        (X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) + X.xa := by
      have h1 := (Finset.mem_Icc.1 hs.1).2
      have h2 : (topA C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i) : ℝ) ≤
          (⌊(X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) + X.xa⌋₊ : ℝ) := by exact_mod_cast h1
      exact h2.trans (Nat.floor_le hS.hF.win0)
    have hk : X.L.k = (X.r : ℝ) + 1 := rfl
    have hY := hS.Y1
    have ha0 : (0 : ℝ) ≤ X.L.a := Nat.cast_nonneg _
    have hrk : (X.r : ℝ) * ((X.L.a : ℝ) / (X.L.k * X.L.Y)) ≤ X.L.a := by
      rw [hk]
      have h0 : (0 : ℝ) < ((X.r : ℝ) + 1) * X.L.Y := by nlinarith
      rw [mul_div_assoc', div_le_iff₀ h0]
      have h1 : (X.L.a : ℝ) * (((X.r : ℝ) + 1) * 1) ≤ (X.L.a : ℝ) * (((X.r : ℝ) + 1) * X.L.Y) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hY (by linarith)) ha0
      linarith
    have hJ : (X.r : ℝ) * X.xa ≤ (X.L.a : ℝ) / 8 := by
      have h1 := hS.xa
      have hLa := hS.La4
      have hLa0 := hS.hF.La0
      unfold Formalism.MainNotions.ColumnSystems.Loc.J0 at h1
      rw [hk] at h1
      have hk0 : (0 : ℝ) < (X.r : ℝ) + 1 := by linarith
      have h2 : (X.r : ℝ) * X.xa ≤ ((X.r : ℝ) + 1) * X.xa := by nlinarith [hS.xa0]
      have h3 : ((X.r : ℝ) + 1) * X.xa ≤ 2 * X.L.La C0 * X.L.b' := by
        have := mul_le_mul_of_nonneg_left h1 hk0.le
        have e : ((X.r : ℝ) + 1) * (2 * (X.L.La C0 * X.L.b' / ((X.r : ℝ) + 1))) = 2 * X.L.La C0 * X.L.b' := by
          field_simp
        linarith
      have h4 : 2 * X.L.La C0 * X.L.b' ≤ ((X.r : ℝ) + 1) / 2 * X.L.b' := by nlinarith
      have h5 : ((X.r : ℝ) + 1) / 2 * X.L.b' ≤ (X.L.a : ℝ) / 8 := by nlinarith
      linarith
    have hd : ((y : ℝ) - x) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) ≤
        X.L.a / (X.L.k * X.L.Y) + X.xa := by
      have : ((y : ℝ) - x) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) =
          (topA C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i) : ℝ) - aTop (uTop (X.S C0 CE1 CE2) i) := by
        rw [sub_mul, hxP, hyP]; ring
      rw [this]
      linarith
    have h7 : (X.r : ℝ) * (((y : ℝ) - x) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ)) ≤
        (X.r : ℝ) * ((X.L.a : ℝ) / (X.L.k * X.L.Y) + X.xa) := mul_le_mul_of_nonneg_left hd hr0
    have h6 : (X.r : ℝ) * ((y : ℝ) - x) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) ≤
        3 * x * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) := by
      nlinarith
    exact le_of_mul_le_mul_right h6 (by linarith)
  have hratio := ratio_num x y X.r hx1 hxy hnum
  have hoth : ∀ l, l ≠ uTop (X.S C0 CE1 CE2) i →
      coarseC X.p (X.S C0 CE1 CE2) (upd C0 CE1 CE2 X dl aTop i) (Formalism.MainNotions.ColumnSystems.digitBlock dl.1 dl.2) l =
        coarseC X.p (X.S C0 CE1 CE2) aTop (Formalism.MainNotions.ColumnSystems.digitBlock dl.1 dl.2) l := by
    intro l hl
    unfold coarseC upd
    rw [Function.update_of_ne hl]
  unfold mCl Formalism.MainNotions.ColumnSystems.dimMM
  push_cast
  have hprod := prod_ratio Finset.univ (uTop (X.S C0 CE1 CE2) i) (Finset.mem_univ _)
    (fun l => (Formalism.MainNotions.ColumnSystems.symDim (X.L.m + 1) (coarseA X.L.p (X.S C0 CE1 CE2) (Formalism.MainNotions.ColumnSystems.digitBlock dl.1 dl.2) l : ℤ) : ℝ) *
      (Formalism.MainNotions.ColumnSystems.symDim (X.L.m + 1)
        (coarseC X.L.p (X.S C0 CE1 CE2) (upd C0 CE1 CE2 X dl aTop i) (Formalism.MainNotions.ColumnSystems.digitBlock dl.1 dl.2) l : ℤ) : ℝ))
    (fun l => (Formalism.MainNotions.ColumnSystems.symDim (X.L.m + 1) (coarseA X.L.p (X.S C0 CE1 CE2) (Formalism.MainNotions.ColumnSystems.digitBlock dl.1 dl.2) l : ℤ) : ℝ) *
      (Formalism.MainNotions.ColumnSystems.symDim (X.L.m + 1) (coarseC X.L.p (X.S C0 CE1 CE2) aTop (Formalism.MainNotions.ColumnSystems.digitBlock dl.1 dl.2) l : ℤ) : ℝ))
    (Real.exp 3) (fun l => by positivity)
    (fun l _ hl => by rw [hoth l hl])
    (by
      rw [← hx, ← hy, symDim_choose X.L.m y, symDim_choose X.L.m x]
      have h0 : (0 : ℝ) ≤ (Formalism.MainNotions.ColumnSystems.symDim (X.L.m + 1)
          (coarseA X.L.p (X.S C0 CE1 CE2) (Formalism.MainNotions.ColumnSystems.digitBlock dl.1 dl.2) (uTop (X.S C0 CE1 CE2) i) : ℤ) : ℝ) := by
        positivity
      calc _ ≤ (Formalism.MainNotions.ColumnSystems.symDim (X.L.m + 1)
              (coarseA X.L.p (X.S C0 CE1 CE2) (Formalism.MainNotions.ColumnSystems.digitBlock dl.1 dl.2) (uTop (X.S C0 CE1 CE2) i) : ℤ) : ℝ) *
            (Real.exp 3 * (((x + X.r).choose X.r : ℕ) : ℝ)) := mul_le_mul_of_nonneg_left hratio h0
        _ = _ := by ring)
  have hA : (0 : ℝ) ≤ (Formalism.MainNotions.ColumnSystems.symDim (X.L.m + 1) ((X.S C0 CE1 CE2).A0 X.L.p) : ℝ) := by positivity
  have hB : (0 : ℝ) ≤ (Formalism.MainNotions.ColumnSystems.symDim (X.L.m + 1) ((X.S C0 CE1 CE2).bPlus : ℤ) : ℝ) := by positivity
  have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod hA) hB
  calc _ ≤ _ := this
    _ = _ := by ring

end Formalism.MainNotions.G.SymmetricFormBlocks

end
