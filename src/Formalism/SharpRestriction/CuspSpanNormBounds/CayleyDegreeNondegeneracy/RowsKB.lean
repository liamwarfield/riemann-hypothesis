module

public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.DifferentIdealMapNeBot

@[expose] public section

section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsDegF
section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsDeg
noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticeCounting Formalism.MainNotions.BridgeLemma

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Deg

variable {D : D7} {large₂ : SizeData₂ D} {X : TermTie D} {u u' : D.what₂.Word} {C1 : ℝ} (Y : LoopTie D large₂ X u u' C1)


open Classical in
def rows_KZ (D : D7) (u u' : D.what₂.Word) (Z : GramM D) : ℝ :=
  ∏ τ : D.what₂.Tau, if leadMinorE Z D.R.rS = 0 then 1 else
    (1 + ‖embS D τ (leadMinorE Z (D.R.rS + 1) / leadMinorE Z D.R.rS)‖ / Real.sqrt ((Tu D u : ℝ) * (Tu D u' : ℝ))) /
      Real.sqrt ((‖embS D τ (leadMinorE Z (D.R.rS + 1) / leadMinorE Z D.R.rS)‖ /
        Real.sqrt ((Tu D u : ℝ) * (Tu D u' : ℝ))) ^ 2 - 1)

theorem rows_KZ_inv {Z Z₂ : GramM D} (h : ZEquiv Z Z₂) (u u' : D.what₂.Word) : rows_KZ D u u' Z₂ = rows_KZ D u u' Z := by
  unfold rows_KZ
  rw [rows_leadMinor_inv h D.R.rS, rows_leadMinor_inv h (D.R.rS + 1)]

theorem rows_Kt_KZ (hrd : 0 < D.host.rdE) (t : D.s.Term u u') : rows_Kt Y t = rows_KZ D u u' (termGramMatrix X t) := by
  unfold rows_Kt rows_KZ
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [rows_chRatio_eq Y hrd t τ]
  unfold onePlusChSh
  by_cases h0 : Dr (X.fl t) (X.fl' t) = 0
  · have h0' : leadMinorE (termGramMatrix X t) D.R.rS = 0 := h0
    rw [if_pos h0, if_pos h0']
  · have h0' : ¬ leadMinorE (termGramMatrix X t) D.R.rS = 0 := h0
    rw [if_neg h0, if_neg h0']
    rfl

def rows_KBound (Y : LoopTie D large₂ X u u' C1) (c : ℝ) : Prop :=
  ∀ t : D.s.Term u u', D.s.Gterm t ≠ 0 → D.s.relevant t →
    rows_Kt Y t ^ 2 ≤ 9 ^ D.R.f * HHZ D large₂.sc.b c (termGramMatrix X t) ^ 3

def rows_GamD (D : D7) (large₂ : SizeData₂ D) (Ca C2 : ℝ) : ℝ :=
  GamS D large₂ * Real.exp (C2 * (D.R.m : ℝ) ^ 6 * D.R.f * Real.log large₂.sc.b) ^ 2 * (Ca / D.R.k) ^ (D.R.k * D.R.f)

def rows_lam (D : D7) (large₂ : SizeData₂ D) (c Ca C2 Ch : ℝ) (q : ℕ) (Z : GramM D) : ℝ :=
  (HHZ D large₂.sc.b c Z ^ (c * (D.R.rS : ℝ) ^ 2)) ^ 2 *
    (GamS D large₂ * sizeZ D large₂.sc.b Ch Z ^ (C2 * (D.R.m : ℝ) ^ 2)) *
    (Real.exp (C2 * (D.R.m : ℝ) ^ 6 * D.R.f * Real.log large₂.sc.b) * sizeZ D large₂.sc.b Ch Z ^ (C2 * (D.R.m : ℝ) ^ 4)) ^ 2 *
    (Ca / D.R.k) ^ (D.R.k * D.R.f) * sizeZ D large₂.sc.b Ch Z ^ (-(2 * (q : ℝ) / ((D.R.rS : ℝ) + 1)))

theorem rows_CK_nonneg (D : D7) (Ca : ℝ) : 0 ≤ (Ca / D.R.k) ^ (D.R.k * D.R.f) :=
  (D.R.k_even.mul_right _).pow_nonneg _

theorem rows_GamD_nonneg (D : D7) (large₂ : SizeData₂ D) (Ca C2 : ℝ) : 0 ≤ rows_GamD D large₂ Ca C2 := by
  unfold rows_GamD
  have h3 : 0 < GamS D large₂ := by unfold GamS; exact Real.exp_pos _
  have := rows_CK_nonneg D Ca
  positivity

theorem rows_lam_eq (D : D7) (large₂ : SizeData₂ D) (c Ca C2 Ch : ℝ) (q : ℕ) (Z : GramM D) :
    rows_lam D large₂ c Ca C2 Ch q Z = (HHZ D large₂.sc.b c Z ^ (c * (D.R.rS : ℝ) ^ 2)) ^ 2 *
      (rows_GamD D large₂ Ca C2 * sizeZ D large₂.sc.b Ch Z ^ (C2 * (D.R.m : ℝ) ^ 2 + C2 * (D.R.m : ℝ) ^ 4 * 2)) *
      sizeZ D large₂.sc.b Ch Z ^ (-(2 * (q : ℝ) / ((D.R.rS : ℝ) + 1))) := by
  have hs : 0 < sizeZ D large₂.sc.b Ch Z := lt_of_lt_of_le one_pos (rows_one_le_sizeZ _ _ _)
  unfold rows_lam rows_GamD
  rw [Real.rpow_add hs, mul_pow, rows_rpow_pow hs]
  push_cast
  ring

theorem rows_lam_nonneg (D : D7) (large₂ : SizeData₂ D) (c Ca C2 Ch : ℝ) (q : ℕ) (Z : GramM D) : 0 ≤ rows_lam D large₂ c Ca C2 Ch q Z := by
  rw [rows_lam_eq]
  have h1 := rows_one_le_HHZ' D large₂ c Z
  have h2 := rows_one_le_sizeZ (D := D) large₂.sc.b Ch Z
  have h3 := rows_GamD_nonneg D large₂ Ca C2
  positivity

def rows_alD (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (c Ca C2 Ch : ℝ) (q : ℕ) (Z : GramM D) : ℝ :=
  Real.sqrt (rows_lam D large₂ c Ca C2 Ch q Z /
    (wordPairGramNorm D u u' Z * rows_KZ D u u' Z ^ (2 * D.R.k) * (Tr D u)⁻¹ ^ (D.R.k * D.R.f)))

def rows_DeD (D : D7) (u u' : D.what₂.Word) (s : ℕ) (x y : GramM D) : ℝ :=
  (2 / gg D) ^ ((s - 2) * D.R.f) * Real.sqrt (wordPairGramProduct D u u' x * wordPairGramProduct D u u' y) * (Tr D u)⁻¹ ^ D.R.f *
    rows_KZ D u u' x * rows_KZ D u u' y

def rows_RD (D : D7) (large₂ : SizeData₂ D) (u : D.what₂.Word) (c Ca C2 Ch : ℝ) (s : ℕ) : ℝ :=
  (2 / gg D) ^ ((s - 2) * D.R.k * D.R.f) * ((D.R.k : ℝ) * D.host.v / (Real.exp 1 * Real.pi)) ^ (D.R.k * D.R.f) *
    (XiS D u (rows_P D large₂ c Ch ^ 2) c s *
      ((rows_P D large₂ c Ch ^ pairCountExponent D c s) ^ 2 * (rows_P D large₂ c Ch ^ (c * (D.R.rS : ℝ) ^ 2)) ^ 2 *
        (c * s * D.R.f) ^ (6 * s * D.R.f) * rows_GamD D large₂ Ca C2))

def rows_degB (D : D7) (large₂ : SizeData₂ D) (u : D.what₂.Word) (c Ca C2 Ch : ℝ) (s : ℕ) : ℝ :=
  rows_RD D large₂ u c Ca C2 Ch s * rows_Phi D large₂ c Ch ^ 2

variable {C' Cl Cg cb Cu cT CT C0 A c Cpr Ca C2 Ch δ δm : ℝ} {q : ℕ}

theorem rows_KZ_pos (h : rows_Hyps Y C' Cl Cg cb Cu cT CT C0 A c Cpr Ca C2 Ch δ δm q) {Z : GramM D}
    (hZ : wordPairGramGood X u u' large₂ c Z) : 0 < rows_KZ D u u' Z := by
  obtain ⟨t, hG, hrel, hE, _⟩ := hZ
  rw [rows_KZ_inv hE, ← rows_Kt_KZ Y (d_rdE_pos h.hH.1)]
  exact rowsT_Kt_pos Y (d_rdE_pos h.hH.1) t hG hrel

theorem rows_den_pos (h : rows_Hyps Y C' Cl Cg cb Cu cT CT C0 A c Cpr Ca C2 Ch δ δm q) {Z : GramM D}
    (hZ : wordPairGramGood X u u' large₂ c Z) :
    0 < wordPairGramNorm D u u' Z * rows_KZ D u u' Z ^ (2 * D.R.k) * (Tr D u)⁻¹ ^ (D.R.k * D.R.f) := by
  have h1 := rows_nZ_pos Y h hZ
  have h2 := rows_KZ_pos Y h hZ
  have h3 := rows_Tr_pos D u
  positivity

theorem rows_deg_term (h : rows_Hyps Y C' Cl Cg cb Cu cT CT C0 A c Cpr Ca C2 Ch δ δm q) (t : D.s.Term u u')
    (hG : D.s.Gterm t ≠ 0) (hrel : D.s.relevant t) :
    aT X t / Real.sqrt (dimPi (hc := D.hcW) u) ≤ rows_alD D large₂ u u' c Ca C2 Ch q (termReducedGramMatrix Y h.hH h.hHH t) := by
  obtain ⟨hEq, hGood⟩ := rows_Zr_spec Y h.hH h.hHH t hG hrel
  have h1 := rows_term_MINdec Y h.hH h.hDEC h.ha h.hb h.hp h.hpp h.hV h.hT h.hCh t hG hrel q h.hq
  rw [rows_Kt_KZ Y (d_rdE_pos h.hH.1), ← rows_KZ_inv hEq, ← rows_nZ_inv hEq, ← rows_HHZ_inv hEq,
    ← rows_sizeZ_inv hEq] at h1
  have h2 : aT X t ^ 2 / dimPi (hc := D.hcW) u ≤ rows_lam D large₂ c Ca C2 Ch q (termReducedGramMatrix Y h.hH h.hHH t) /
      (wordPairGramNorm D u u' (termReducedGramMatrix Y h.hH h.hHH t) * rows_KZ D u u' (termReducedGramMatrix Y h.hH h.hHH t) ^ (2 * D.R.k) *
        (Tr D u)⁻¹ ^ (D.R.k * D.R.f)) := by
    rw [le_div_iff₀ (rows_den_pos Y h hGood)]
    calc aT X t ^ 2 / dimPi (hc := D.hcW) u * (wordPairGramNorm D u u' (termReducedGramMatrix Y h.hH h.hHH t) *
          rows_KZ D u u' (termReducedGramMatrix Y h.hH h.hHH t) ^ (2 * D.R.k) * (Tr D u)⁻¹ ^ (D.R.k * D.R.f))
        = wordPairGramNorm D u u' (termReducedGramMatrix Y h.hH h.hHH t) * aT X t ^ 2 * rows_KZ D u u' (termReducedGramMatrix Y h.hH h.hHH t) ^ (2 * D.R.k) *
            (Tr D u)⁻¹ ^ (D.R.k * D.R.f) / dimPi (hc := D.hcW) u := by ring
      _ ≤ _ := h1
  have h3 : aT X t / Real.sqrt (dimPi (hc := D.hcW) u) = Real.sqrt (aT X t ^ 2 / dimPi (hc := D.hcW) u) := by
    rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (aT_nonneg X t)]
  rw [h3]
  exact Real.sqrt_le_sqrt h2


include Y in
theorem rows_thmA_deg (hThA : VanishingOnXAndXPlus.adm14 D u u') (hSt : Cnt.Stand D u u') (hG0 : @LatticeDeterminantFactorization D X u u') (hrd : 0 < D.host.rdE)
    (p : D.s.Pair u u') (hG1 : D.s.Gterm (D.s.pfst p) ≠ 0) (hG2 : D.s.Gterm (D.s.psnd p) ≠ 0) (hs : 2 ≤ D.s.s0 p)
    (hnd : ¬ ndP X p) :
    pairDeterminant X p ≤ rows_DeD D u u' (D.s.s0 p) (termGramMatrix X (D.s.pfst p)) (termGramMatrix X (D.s.psnd p)) := by
  have h := ((rows_thmA Y hThA hSt p hG1 hG2 hs).2 hnd).2.2
  have e1 : G0 (X.abelian₂ (D.s.pfst p)) (gS D) (X.fl (D.s.pfst p)) (X.fl' (D.s.pfst p)) =
      wordPairGramProduct D u u' (termGramMatrix X (D.s.pfst p)) := hG0 (D.s.pfst p) hG1
  have e2 : G0 (X.abelian₂ (D.s.psnd p)) (gS D) (X.fl (D.s.psnd p)) (X.fl' (D.s.psnd p)) =
      wordPairGramProduct D u u' (termGramMatrix X (D.s.psnd p)) := hG0 (D.s.psnd p) hG2
  rw [← X.pLam p, ← X.pfl p] at e2
  rw [e1, e2, ← X.s0_eq p, ← rows_gg_eq, rows_Kpair_eq Y hrd, rows_Kt_KZ Y hrd, rows_Kt_KZ Y hrd] at h
  unfold rows_DeD
  have e3 : (Tr D u)⁻¹ ^ D.R.f = (((Tu D u : ℕ) : ℝ) ^ D.R.f)⁻¹ := by rw [inv_pow]; rfl
  rw [e3]
  calc pairDeterminant X p ≤ _ := h
    _ = _ := by ring

theorem rows_three_le (D : D7) (large₂ : SizeData₂ D) {c : ℝ} (hc : 1 ≤ c) (Z : GramM D) : (3 : ℝ) ^ D.R.f ≤ HHZ D large₂.sc.b c Z := by
  have hb := d_two_le_b D large₂
  have hb0 : 0 < large₂.sc.b := by linarith
  have hm2 : (2 : ℝ) ≤ D.R.m := by rw [rows_m_cast]; have : (0 : ℝ) ≤ D.R.rS := by positivity
                                   linarith
  have hf0 : (0 : ℝ) ≤ D.R.f := by positivity
  have h2 : 1 ≤ sizeZ D large₂.sc.b c Z ^ 4 := one_le_pow₀ (rows_one_le_sizeZ _ _ _)
  have hE : ((2 * D.R.f : ℕ) : ℝ) ≤ c * (D.R.m : ℝ) ^ 2 * D.R.f * (c * D.R.m) := by
    have e : c * (D.R.m : ℝ) ^ 2 * D.R.f * (c * D.R.m) = (c ^ 2 * (D.R.m : ℝ) ^ 3) * D.R.f := by ring
    rw [e]; push_cast
    have h8 : (2 : ℝ) ≤ c ^ 2 * (D.R.m : ℝ) ^ 3 := by
      have a1 : (1 : ℝ) ≤ c ^ 2 := one_le_pow₀ hc
      have a2 : (2 : ℝ) ≤ (D.R.m : ℝ) ^ 3 := by nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ D.R.m) (by linarith : (0:ℝ) ≤ D.R.m)]
      nlinarith
    exact mul_le_mul_of_nonneg_right h8 hf0
  have h1 : (3 : ℝ) ^ D.R.f ≤ (large₂.sc.b ^ (c * (D.R.m : ℝ) ^ 2 * D.R.f)) ^ (c * (D.R.m : ℝ)) := by
    rw [← Real.rpow_mul hb0.le]
    calc (3 : ℝ) ^ D.R.f ≤ (large₂.sc.b ^ 2) ^ D.R.f := pow_le_pow_left₀ (by norm_num) (by nlinarith) _
      _ = large₂.sc.b ^ ((2 * D.R.f : ℕ) : ℝ) := by rw [Real.rpow_natCast, pow_mul]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) hE
  unfold HHZ
  calc (3 : ℝ) ^ D.R.f ≤ (large₂.sc.b ^ (c * (D.R.m : ℝ) ^ 2 * D.R.f)) ^ (c * (D.R.m : ℝ)) * 1 := by rw [mul_one]; exact h1
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by positivity)

theorem rows_DeD_nonneg (h : rows_Hyps Y C' Cl Cg cb Cu cT CT C0 A c Cpr Ca C2 Ch δ δm q) (s : ℕ) {x y : GramM D}
    (gx : wordPairGramGood X u u' large₂ c x) (gy : wordPairGramGood X u u' large₂ c y) : 0 ≤ rows_DeD D u u' s x y := by
  have hg2 := two_le_gg_of_count_hypotheses h.hH.1
  have h1 := rows_KZ_pos Y h gx
  have h2 := rows_KZ_pos Y h gy
  have h3 := rows_Tr_pos D u
  have : 0 ≤ gg D := by linarith
  unfold rows_DeD
  positivity

theorem rows_deg_count (h : rows_Hyps Y C' Cl Cg cb Cu cT CT C0 A c Cpr Ca C2 Ch δ δm q) (hK : rows_KBound Y c)
    (hc1 : 1 ≤ c) (s : ℕ) (hs : 2 ≤ s)
    (hsk : s ≤ D.R.k) (x y : GramM D) (gx : wordPairGramGood X u u' large₂ c x) (gy : wordPairGramGood X u u' large₂ c y)
    (S' : Finset (D.s.Pair u u'))
    (hS : ∀ p ∈ S', clsDeg X s p ∧ ZEquiv (termGramMatrix X (D.s.pfst p)) x ∧ ZEquiv (termGramMatrix X (D.s.psnd p)) y) :
    ∑ p ∈ S', X.wRow p ≤ massRows D Y.F0 Y.what₂ * wordSublatticeTripleBound D large₂ u c x y s (rows_DeD D u u' s x y) := by
  have hg2 := two_le_gg_of_count_hypotheses h.hH.1
  have hrd := d_rdE_pos h.hH.1
  have hDe0 := rows_DeD_nonneg Y h s gx gy
  by_cases hne : S'.Nonempty
  · obtain ⟨p₀, hp₀⟩ := hne
    have hDe_of : ∀ p ∈ S', pairDeterminant X p ≤ rows_DeD D u u' s x y := by
      intro p hp
      obtain ⟨⟨hG1, hG2, hs0, hnd⟩, e1, e2⟩ := hS p hp
      have h' := rows_thmA_deg Y h.hThA h.hH.2.1 h.hG0 hrd p hG1 hG2 (by rw [hs0]; exact hs) hnd
      unfold rows_DeD at h' ⊢
      rw [hs0, ← gramProductG0_equiv_invariant e1, ← gramProductG0_equiv_invariant e2, ← rows_KZ_inv e1, ← rows_KZ_inv e2] at h'
      exact h'
    have h1 : 1 ≤ rows_DeD D u u' s x y :=
      le_trans (rows_DetGeOne_of h.hH.2.1 p₀ (hS p₀ hp₀).1.1 (hS p₀ hp₀).1.2.1) (hDe_of p₀ hp₀)
    have kb : ∀ Z, wordPairGramGood X u u' large₂ c Z → rows_KZ D u u' Z ^ 2 ≤ 9 ^ D.R.f * HHZ D large₂.sc.b c Z ^ 3 := by
      rintro Z ⟨t, hG, hrel, hE, _⟩
      rw [rows_KZ_inv hE, rows_HHZ_inv hE, ← rows_Kt_KZ Y hrd]
      exact hK t hG hrel
    have h9 : (9 : ℝ) ^ D.R.f ≤ HHZ D large₂.sc.b c x * HHZ D large₂.sc.b c y := by
      have e : (9 : ℝ) ^ D.R.f = 3 ^ D.R.f * 3 ^ D.R.f := by rw [← mul_pow]; norm_num
      rw [e]
      exact mul_le_mul (rows_three_le D large₂ hc1 x) (rows_three_le D large₂ hc1 y) (by positivity)
        (le_trans zero_le_one (rows_one_le_HHZ D large₂ h.hc x))
    have hT1 : 1 ≤ Tr D u := by unfold Tr; exact_mod_cast (D.mem u).A.T_prime.pos
    have h2 : rows_DeD D u u' s x y ≤ (HHZ D large₂.sc.b c x * HHZ D large₂.sc.b c y) ^ (3 : ℝ) := by
      have := Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.deDegBound D.R.f s (gg D) (Tr D u) (wordPairGramProduct D u u' x) (wordPairGramProduct D u u' y)
        (rows_KZ D u u' x) (rows_KZ D u u' y)
        (HHZ D large₂.sc.b c x) (HHZ D large₂.sc.b c y) hg2 hT1 (gramProductG0_pos Y h.hH.1 h.hT gx).le
        (gramProductG0_pos Y h.hH.1 h.hT gy).le (gramProductG0_le_height Y h.hH h.hHH h.hT gx)
        (gramProductG0_le_height Y h.hH h.hHH h.hT gy) (rows_KZ_pos Y h gx).le (rows_KZ_pos Y h gy).le (kb x gx) (kb y gy) h9
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      exact this
    obtain ⟨t1, hG1, hr1, hE1, _⟩ := gx
    obtain ⟨t2, hG2, hr2, hE2, _⟩ := gy
    refine rows_count Y h.hH h.hC3 x y (rows_RelZ_inv hE1 (rows_RelZ_term X t1 hG1 hr1))
      (rows_RelZ_inv hE2 (rows_RelZ_term X t2 hG2 hr2)) s hs hsk _ h1 h2
      (rows_c3B_nonneg D large₂ u h.hc x y s hDe0) _ ?_
    intro p hp
    exact ⟨(hS p hp).1.1, (hS p hp).1.2.1, (hS p hp).2.1, (hS p hp).2.2, (hS p hp).1.2.2.1, hDe_of p hp⟩
  · rw [Finset.not_nonempty_iff_eq_empty.1 hne, Finset.sum_empty]
    exact mul_nonneg (rows_massRows_nonneg Y) (rows_c3B_nonneg D large₂ u h.hc x y s hDe0)

theorem rows_deg_prod (h : rows_Hyps Y C' Cl Cg cb Cu cT CT C0 A c Cpr Ca C2 Ch δ δm q) (s : ℕ) (hs : 2 ≤ s)
    (hq2 : 4 * (c * D.R.k) + 4 * pairCountExponent D c s + 4 * (c * (D.R.rS : ℝ) ^ 2) +
      (C2 * (D.R.m : ℝ) ^ 2 + C2 * (D.R.m : ℝ) ^ 4 * 2) / 2 + 12 * ((D.R.rS : ℝ) + 1) ^ 2 ≤ (q : ℝ) / ((D.R.rS : ℝ) + 1))
    (x y : GramM D) (gx : wordPairGramGood X u u' large₂ c x) (gy : wordPairGramGood X u u' large₂ c y) :
    wordSublatticeTripleBound D large₂ u c x y s (rows_DeD D u u' s x y) *
        (rows_alD D large₂ u u' c Ca C2 Ch q x * rows_alD D large₂ u u' c Ca C2 Ch q y) ≤
      rows_RD D large₂ u c Ca C2 Ch s * (sizeZ D large₂.sc.b Ch x ^ (-(12 * ((D.R.rS : ℝ) + 1) ^ 2)) *
        sizeZ D large₂.sc.b Ch y ^ (-(12 * ((D.R.rS : ℝ) + 1) ^ 2))) := by
  have hrd := d_rdE_pos h.hH.1
  have hb2 := d_two_le_b D large₂
  have hg2 := two_le_gg_of_count_hypotheses h.hH.1
  have hc := h.hc
  have hv1 : 1 ≤ D.host.v := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h19, _⟩ := h.hH.1.1
    exact h19
  have hk1 : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hx1 := rows_one_le_HHZ D large₂ hc x
  have hy1 := rows_one_le_HHZ D large₂ hc y
  have sx1 := rows_one_le_sizeZ (D := D) large₂.sc.b Ch x
  have sy1 := rows_one_le_sizeZ (D := D) large₂.sc.b Ch y
  have hh0 : 0 ≤ HHZ D large₂.sc.b c x * HHZ D large₂.sc.b c y := mul_nonneg (by linarith) (by linarith)
  have hP1 := rows_P_one_le D large₂ c Ch
  have cx : HHZ D large₂.sc.b c x ≤ rows_P D large₂ c Ch * sizeZ D large₂.sc.b Ch x ^ 4 := rows_HHZ_cmp hrd (by linarith) c Ch x
  have cy : HHZ D large₂.sc.b c y ≤ rows_P D large₂ c Ch * sizeZ D large₂.sc.b Ch y ^ 4 := rows_HHZ_cmp hrd (by linarith) c Ch y
  have hαsq : ∀ Z, wordPairGramGood X u u' large₂ c Z →
      LatticeSumBounds.nTot D.R.k D.R.f D.host.v (wordPairGramProduct D u u' Z) (NT D u) * rows_alD D large₂ u u' c Ca C2 Ch q Z ^ 2 *
        rows_KZ D u u' Z ^ (2 * D.R.k) * (Tr D u)⁻¹ ^ (D.R.k * D.R.f) ≤ rows_lam D large₂ c Ca C2 Ch q Z := by
    intro Z hZ
    have e : wordPairGramNorm D u u' Z = LatticeSumBounds.nTot D.R.k D.R.f D.host.v (wordPairGramProduct D u u' Z) (NT D u) := d_nProduct h.hH.1 Z
    rw [← e]
    unfold rows_alD
    rw [Real.sq_sqrt (div_nonneg (rows_lam_nonneg D large₂ c Ca C2 Ch q Z) (rows_den_pos Y h hZ).le)]
    have hd := (rows_den_pos Y h hZ).ne'
    refine le_of_eq ?_
    calc wordPairGramNorm D u u' Z * (rows_lam D large₂ c Ca C2 Ch q Z /
          (wordPairGramNorm D u u' Z * rows_KZ D u u' Z ^ (2 * D.R.k) * (Tr D u)⁻¹ ^ (D.R.k * D.R.f))) *
          rows_KZ D u u' Z ^ (2 * D.R.k) * (Tr D u)⁻¹ ^ (D.R.k * D.R.f)
        = (wordPairGramNorm D u u' Z * rows_KZ D u u' Z ^ (2 * D.R.k) * (Tr D u)⁻¹ ^ (D.R.k * D.R.f)) *
            (rows_lam D large₂ c Ca C2 Ch q Z /
              (wordPairGramNorm D u u' Z * rows_KZ D u u' Z ^ (2 * D.R.k) * (Tr D u)⁻¹ ^ (D.R.k * D.R.f))) := by ring
      _ = _ := mul_div_cancel₀ _ hd
  have n1 := Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.degRow D.R.k D.R.f s (gg D) D.host.v (Tr D u) (NT D u) (wordPairGramProduct D u u' x)
    (wordPairGramProduct D u u' y) (rows_KZ D u u' x) (rows_KZ D u u' y)
    (XiS D u (HHZ D large₂.sc.b c x * HHZ D large₂.sc.b c y) c s)
    ((HHZ D large₂.sc.b c x * HHZ D large₂.sc.b c y) ^ pairCountExponent D c s * (c * s * D.R.f) ^ (6 * s * D.R.f))
    (wordSublatticeTripleBound D large₂ u c x y s (rows_DeD D u u' s x y)) (rows_alD D large₂ u u' c Ca C2 Ch q x)
    (rows_alD D large₂ u u' c Ca C2 Ch q y)
    (rows_lam D large₂ c Ca C2 Ch q x) (rows_lam D large₂ c Ca C2 Ch q y) hk1 hs (by linarith) (by linarith)
    (rows_Tr_pos D u) (rows_NT_pos D u) (gramProductG0_pos Y h.hH.1 h.hT gx) (gramProductG0_pos Y h.hH.1 h.hT gy)
    (rows_KZ_pos Y h gx) (rows_KZ_pos Y h gy) (rows_XiS_nonneg D u hh0 hc s)
    (by positivity) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (le_of_eq (by unfold wordSublatticeTripleBound pairCountExponent rows_DeD; ring)) (hαsq x gx) (hαsq y gy)
  have hXi : XiS D u (HHZ D large₂.sc.b c x * HHZ D large₂.sc.b c y) c s ≤
      XiS D u (rows_P D large₂ c Ch ^ 2) c s * (sizeZ D large₂.sc.b Ch x * sizeZ D large₂.sc.b Ch y) ^ (4 * (c * D.R.k)) := by
    refine rows_Xi_le D u hh0 (by positivity) (one_le_mul_of_one_le_of_one_le sx1 sy1) hc ?_ s
    calc HHZ D large₂.sc.b c x * HHZ D large₂.sc.b c y
        ≤ (rows_P D large₂ c Ch * sizeZ D large₂.sc.b Ch x ^ 4) * (rows_P D large₂ c Ch * sizeZ D large₂.sc.b Ch y ^ 4) :=
          mul_le_mul cx cy (by linarith) (by positivity)
      _ = rows_P D large₂ c Ch ^ 2 * (sizeZ D large₂.sc.b Ch x * sizeZ D large₂.sc.b Ch y) ^ 4 := by ring
  have he : 4 * (c * D.R.k) + 4 * pairCountExponent D c s + 4 * (c * (D.R.rS : ℝ) ^ 2) +
      (C2 * (D.R.m : ℝ) ^ 2 + C2 * (D.R.m : ℝ) ^ 4 * 2) / 2 -
      2 * (q : ℝ) / ((D.R.rS : ℝ) + 1) / 2 ≤ -(12 * ((D.R.rS : ℝ) + 1) ^ 2) := by
    have e : 2 * (q : ℝ) / ((D.R.rS : ℝ) + 1) / 2 = (q : ℝ) / ((D.R.rS : ℝ) + 1) := by ring
    rw [e]; linarith
  have n2 := rows_num_pair (P := rows_P D large₂ c Ch) (σ₁ := sizeZ D large₂.sc.b Ch x) (σ₂ := sizeZ D large₂.sc.b Ch y)
    (h₁ := HHZ D large₂.sc.b c x) (h₂ := HHZ D large₂.sc.b c y)
    (cr := c * (D.R.rS : ℝ) ^ 2) (Γ := rows_GamD D large₂ Ca C2) (a2 := C2 * (D.R.m : ℝ) ^ 2 + C2 * (D.R.m : ℝ) ^ 4 * 2)
    (dq := 2 * (q : ℝ) / ((D.R.rS : ℝ) + 1)) (E1 := pairCountExponent D c s) (F6 := (c * s * D.R.f) ^ (6 * s * D.R.f))
    (XiH := XiS D u (HHZ D large₂.sc.b c x * HHZ D large₂.sc.b c y) c s) (XiP := XiS D u (rows_P D large₂ c Ch ^ 2) c s)
    (ck := c * D.R.k) (e := 12 * ((D.R.rS : ℝ) + 1) ^ 2) (l₁ := rows_lam D large₂ c Ca C2 Ch q x)
    (l₂ := rows_lam D large₂ c Ca C2 Ch q y)
    hP1 sx1 sy1 hx1 hy1 cx cy (by positivity) (rows_GamD_nonneg D large₂ Ca C2) (pairCountExponent_nonneg D hc s) (by positivity)
    (rows_XiS_nonneg D u hh0 hc s) hXi (rows_lam_eq D large₂ c Ca C2 Ch q x) (rows_lam_eq D large₂ c Ca C2 Ch q y) he
  have hA0 : 0 ≤ (2 / gg D) ^ ((s - 2) * D.R.k * D.R.f) *
      ((D.R.k : ℝ) * D.host.v / (Real.exp 1 * Real.pi)) ^ (D.R.k * D.R.f) := by
    have hpi := Real.pi_pos
    have : 0 ≤ gg D := by linarith
    have : 0 ≤ D.host.v := by linarith
    positivity
  calc wordSublatticeTripleBound D large₂ u c x y s (rows_DeD D u u' s x y) *
        (rows_alD D large₂ u u' c Ca C2 Ch q x * rows_alD D large₂ u u' c Ca C2 Ch q y)
      = wordSublatticeTripleBound D large₂ u c x y s (rows_DeD D u u' s x y) * rows_alD D large₂ u u' c Ca C2 Ch q x *
          rows_alD D large₂ u u' c Ca C2 Ch q y := by ring
    _ ≤ _ := n1
    _ = (2 / gg D) ^ ((s - 2) * D.R.k * D.R.f) *
          ((D.R.k : ℝ) * D.host.v / (Real.exp 1 * Real.pi)) ^ (D.R.k * D.R.f) *
          (XiS D u (HHZ D large₂.sc.b c x * HHZ D large₂.sc.b c y) c s *
            ((HHZ D large₂.sc.b c x * HHZ D large₂.sc.b c y) ^ pairCountExponent D c s * (c * s * D.R.f) ^ (6 * s * D.R.f)) *
            Real.sqrt (rows_lam D large₂ c Ca C2 Ch q x * rows_lam D large₂ c Ca C2 Ch q y)) := by ring
    _ ≤ (2 / gg D) ^ ((s - 2) * D.R.k * D.R.f) *
          ((D.R.k : ℝ) * D.host.v / (Real.exp 1 * Real.pi)) ^ (D.R.k * D.R.f) *
          (XiS D u (rows_P D large₂ c Ch ^ 2) c s * ((rows_P D large₂ c Ch ^ pairCountExponent D c s) ^ 2 *
            (rows_P D large₂ c Ch ^ (c * (D.R.rS : ℝ) ^ 2)) ^ 2 * (c * s * D.R.f) ^ (6 * s * D.R.f) * rows_GamD D large₂ Ca C2) *
            (sizeZ D large₂.sc.b Ch x ^ (-(12 * ((D.R.rS : ℝ) + 1) ^ 2)) *
              sizeZ D large₂.sc.b Ch y ^ (-(12 * ((D.R.rS : ℝ) + 1) ^ 2)))) :=
        mul_le_mul_of_nonneg_left n2 hA0
    _ = _ := by unfold rows_RD; ring

theorem rows_RD_nonneg (h : rows_Hyps Y C' Cl Cg cb Cu cT CT C0 A c Cpr Ca C2 Ch δ δm q) (s : ℕ) :
    0 ≤ rows_RD D large₂ u c Ca C2 Ch s := by
  have hg2 := two_le_gg_of_count_hypotheses h.hH.1
  have hv1 : 1 ≤ D.host.v := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h19, _⟩ := h.hH.1.1
    exact h19
  have hP1 := rows_P_one_le D large₂ c Ch
  have hG := rows_GamD_nonneg D large₂ Ca C2
  have hXiP0 : 0 ≤ XiS D u (rows_P D large₂ c Ch ^ 2) c s := rows_XiS_nonneg D u (by positivity) h.hc s
  have hpi := Real.pi_pos
  have : 0 ≤ gg D := by linarith
  have : 0 ≤ D.host.v := by linarith
  have := h.hc
  unfold rows_RD
  positivity

theorem rows_Deg_record (h : rows_Hyps Y C' Cl Cg cb Cu cT CT C0 A c Cpr Ca C2 Ch δ δm q) (hK : rows_KBound Y c)
    (hc1 : 1 ≤ c) (s : ℕ) (hs : 2 ≤ s) (hsk : s ≤ D.R.k)
    (hq2 : 4 * (c * D.R.k) + 4 * pairCountExponent D c s + 4 * (c * (D.R.rS : ℝ) ^ 2) +
      (C2 * (D.R.m : ℝ) ^ 2 + C2 * (D.R.m : ℝ) ^ 4 * 2) / 2 + 12 * ((D.R.rS : ℝ) + 1) ^ 2 ≤ (q : ℝ) / ((D.R.rS : ℝ) + 1)) :
    RowBound X Y (clsDeg X s) (rows_degB D large₂ u c Ca C2 Ch s) := by
  refine rowBound_relevant Y (fun p hp => ⟨hp.1, hp.2.1⟩) ?_
  intro S hS
  have sp1 : ∀ p ∈ S, ZEquiv (termGramMatrix X (D.s.pfst p)) (termReducedGramMatrix Y h.hH h.hHH (D.s.pfst p)) ∧
      wordPairGramGood X u u' large₂ c (termReducedGramMatrix Y h.hH h.hHH (D.s.pfst p)) := fun p hp =>
    rows_Zr_spec Y h.hH h.hHH _ (hS p hp).1.1 (hS p hp).2.1
  have sp2 : ∀ p ∈ S, ZEquiv (termGramMatrix X (D.s.psnd p)) (termReducedGramMatrix Y h.hH h.hHH (D.s.psnd p)) ∧
      wordPairGramGood X u u' large₂ c (termReducedGramMatrix Y h.hH h.hHH (D.s.psnd p)) := fun p hp =>
    rows_Zr_spec Y h.hH h.hHH _ (hS p hp).1.2.1 (hS p hp).2.2
  have key := weighted_sum_le' S (fun p => X.wRow p) (fun p => aT X (D.s.pfst p) / Real.sqrt (dimPi (hc := D.hcW) u))
    (fun p => aT X (D.s.psnd p) / Real.sqrt (dimPi (hc := D.hcW) u)) (fun p => termReducedGramMatrix Y h.hH h.hHH (D.s.pfst p))
    (fun p => termReducedGramMatrix Y h.hH h.hHH (D.s.psnd p)) (massRows D Y.F0 Y.what₂) (rows_RD D large₂ u c Ca C2 Ch s)
    (rows_Phi D large₂ c Ch) (fun x y => wordSublatticeTripleBound D large₂ u c x y s (rows_DeD D u u' s x y))
    (rows_alD D large₂ u u' c Ca C2 Ch q) (fun Z => sizeZ D large₂.sc.b Ch Z ^ (-(12 * ((D.R.rS : ℝ) + 1) ^ 2)))
    (rows_massRows_nonneg Y) (rows_RD_nonneg Y h s)
    (fun p _ => (X.wRow_pos p).le) (fun p _ => div_nonneg (aT_nonneg _ _) (Real.sqrt_nonneg _))
    (fun p _ => div_nonneg (aT_nonneg _ _) (Real.sqrt_nonneg _))
    (fun p hp => rows_deg_term Y h _ (hS p hp).1.1 (hS p hp).2.1)
    (fun p hp => rows_deg_term Y h _ (hS p hp).1.2.1 (hS p hp).2.2)
    (by
      rintro x y ⟨p1, hp1, rfl⟩ ⟨p2, hp2, rfl⟩ S' hS' hl
      refine rows_deg_count Y h hK hc1 s hs hsk _ _ (sp1 p1 hp1).2 (sp2 p2 hp2).2 S' fun p hp => ?_
      refine ⟨(hS p (hS' hp)).1, ?_, ?_⟩
      · rw [← (hl p hp).1]; exact (sp1 p (hS' hp)).1
      · rw [← (hl p hp).2]; exact (sp2 p (hS' hp)).1)
    (by
      rintro x y ⟨p1, hp1, rfl⟩ ⟨p2, hp2, rfl⟩
      exact rows_deg_prod Y h s hs hq2 _ _ (sp1 p1 hp1).2 (sp2 p2 hp2).2)
    (fun x => Real.sqrt_nonneg _)
    (fun x => Real.rpow_nonneg (le_trans zero_le_one (rows_one_le_sizeZ _ _ _)) _)
    (fun 𝒵 h𝒵 => rows_nd_size Y h 𝒵 fun Z hZ => by obtain ⟨p, hp, rfl⟩ := h𝒵 Z hZ; exact (sp1 p hp).2)
    (fun 𝒵 h𝒵 => rows_nd_size Y h 𝒵 fun Z hZ => by obtain ⟨p, hp, rfl⟩ := h𝒵 Z hZ; exact (sp2 p hp).2)
  rw [rows_wP_sum h.hdim S]
  calc dimPi (hc := D.hcW) u * _
      ≤ dimPi (hc := D.hcW) u * (massRows D Y.F0 Y.what₂ * (rows_RD D large₂ u c Ca C2 Ch s * rows_Phi D large₂ c Ch ^ 2)) :=
        mul_le_mul_of_nonneg_left key h.hdim.le
    _ = massRows D Y.F0 Y.what₂ * dimPi (hc := D.hcW) u * rows_degB D large₂ u c Ca C2 Ch s := by
        unfold rows_degB; ring

end Deg

end Formalism.MainNotions.BridgeLemma₂

end
end

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticeCounting Formalism.MainNotions.BridgeLemma

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Rec

variable {D : D7} {large₂ : SizeData₂ D} {X : TermTie D} {u u' : D.what₂.Word} {C1 : ℝ} (Y : LoopTie D large₂ X u u' C1)

theorem rows_GamD_le (D : D7) (large₂ : SizeData₂ D) {Ca C2 C : ℝ} (hC2 : 2 * C2 ≤ C) (hCa : |Ca| ≤ C) :
    rows_GamD D large₂ Ca C2 ≤ GamS D large₂ * Real.exp (C * (D.R.m : ℝ) ^ 6 * D.R.f * Real.log large₂.sc.b) *
      (C / D.R.k) ^ (D.R.k * D.R.f) := by
  unfold rows_GamD
  have hb : Real.log large₂.sc.b = large₂.sc.L := by unfold Scale.b; exact Real.log_exp _
  have hL : 0 ≤ large₂.sc.L := by
    unfold Scale.L; exact Real.rpow_nonneg (by linarith [large₂.sc.one_lt_alt]) _
  have hk0 : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
  have hG : 0 ≤ GamS D large₂ := by unfold GamS; positivity
  have hQ : 0 ≤ (D.R.m : ℝ) ^ 6 * D.R.f * large₂.sc.L := mul_nonneg (by positivity) hL
  have hE : Real.exp (C2 * (D.R.m : ℝ) ^ 6 * D.R.f * Real.log large₂.sc.b) ^ 2 ≤
      Real.exp (C * (D.R.m : ℝ) ^ 6 * D.R.f * Real.log large₂.sc.b) := by
    rw [sq, ← Real.exp_add, Real.exp_le_exp, hb]
    have := mul_le_mul_of_nonneg_right hC2 hQ
    linarith
  have hX : (Ca / D.R.k) ^ (D.R.k * D.R.f) ≤ (C / D.R.k) ^ (D.R.k * D.R.f) := by
    calc (Ca / D.R.k) ^ (D.R.k * D.R.f) ≤ |Ca / D.R.k| ^ (D.R.k * D.R.f) := by
          rw [← abs_pow]; exact le_abs_self _
      _ ≤ (C / D.R.k) ^ (D.R.k * D.R.f) := by
          apply pow_le_pow_left₀ (abs_nonneg _)
          rw [abs_div, abs_of_nonneg hk0]
          exact div_le_div_of_nonneg_right hCa hk0
  have hX2 : 0 ≤ (C / D.R.k) ^ (D.R.k * D.R.f) :=
    pow_nonneg (div_nonneg (le_trans (abs_nonneg _) hCa) hk0) _
  calc GamS D large₂ * Real.exp (C2 * (D.R.m : ℝ) ^ 6 * D.R.f * Real.log large₂.sc.b) ^ 2 * (Ca / D.R.k) ^ (D.R.k * D.R.f)
      ≤ GamS D large₂ * Real.exp (C2 * (D.R.m : ℝ) ^ 6 * D.R.f * Real.log large₂.sc.b) ^ 2 * (C / D.R.k) ^ (D.R.k * D.R.f) :=
        mul_le_mul_of_nonneg_left hX (mul_nonneg hG (sq_nonneg _))
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE hG) hX2

theorem rows_degB_le {C' Cl Cg cb Cu cT CT C0 A c Ca C2 Ch C : ℝ} (hH : Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A)
    (hc : 0 ≤ c) (hcC : c ≤ C) (hC1 : 1 ≤ C)
    (hC : 4 + (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c + 2) ≤ C ^ 2) (hC2 : 2 * C2 ≤ C) (hCa : |Ca| ≤ C) (s : ℕ) :
    rows_degB D large₂ u c Ca C2 Ch s ≤
      LatticeSumBounds.degRow C D.R.k D.R.m D.R.f s large₂.sc.b (gg D) D.host.v (GamS D large₂) (XiB D large₂ u C) := by
  have hg2 := two_le_gg_of_count_hypotheses hH.1
  have hv1 : 1 ≤ D.host.v := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h19, _⟩ := hH.1.1
    exact h19
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast rows_f_pos D
  have hP1 := rows_P_one_le D large₂ c Ch
  have hmx : 0 ≤ max (Ch - c) 0 := le_max_right _ _
  have hexp := rows_exp_nd (m := D.R.m) (f := D.R.f) (s := s) (r := D.R.rS) (c := c) (mx := max (Ch - c) 0)
    (cf := cF D.R.f) (C := C) (rows_m_cast D) (by positivity) hf (by positivity) hc hmx (rows_cF_le hH) hC
  have hpe2 : 2 * pairCountExponentShift D c Ch ≤ C * (D.R.m : ℝ) ^ 2 * D.R.f * (C * D.R.m) := by
    have e1 : pairCountExponentShift D c Ch = (c ^ 2 + 2 * max (Ch - c) 0) * ((D.R.m : ℝ) ^ 3 * D.R.f) := by
      unfold pairCountExponentShift
      have : (D.R.rS : ℝ) + 1 = (D.R.m : ℝ) / 2 := by rw [rows_m_cast]; ring
      rw [this]; ring
    have h0 : 0 ≤ (D.R.m : ℝ) ^ 3 * D.R.f := by positivity
    have h1 : 2 * (c ^ 2 + 2 * max (Ch - c) 0) ≤ C ^ 2 := by
      have : 0 ≤ (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c) := by positivity
      nlinarith
    rw [e1]
    calc 2 * ((c ^ 2 + 2 * max (Ch - c) 0) * ((D.R.m : ℝ) ^ 3 * D.R.f))
        = (2 * (c ^ 2 + 2 * max (Ch - c) 0)) * ((D.R.m : ℝ) ^ 3 * D.R.f) := by ring
      _ ≤ C ^ 2 * ((D.R.m : ℝ) ^ 3 * D.R.f) := mul_le_mul_of_nonneg_right h1 h0
      _ = _ := by ring
  have hXs0 : 0 ≤ XiS D u (rows_P D large₂ c Ch ^ 2) c s := rows_XiS_nonneg D u (by positivity) hc s
  have hXs := rows_XiP_le D large₂ u hc hcC hpe2 s
  have core := rows_num_nd (k := D.R.k) (m := D.R.m) (f := D.R.f) (s := s) (r := D.R.rS) (b := large₂.sc.b) (g := 2)
    (v := D.host.v) (Γ := rows_GamD D large₂ Ca C2) (c := c) (C := C) (pe := pairCountExponentShift D c Ch) (E1 := pairCountExponent D c s)
    (cr := c * (D.R.rS : ℝ) ^ 2) (δ := 0) (rD := 1) (XiP := XiS D u (rows_P D large₂ c Ch ^ 2) c s)
    (Xi := XiB D large₂ u C) (d_two_le_b D large₂) (by norm_num) (by linarith) (rows_GamD_nonneg D large₂ Ca C2) hc hcC hC1 le_rfl
    zero_le_one zero_le_one hXs0 hXs (by unfold pairCountExponentShift pairCountExponent; exact hexp)
  unfold LatticeSumBounds.ndRow at core
  rw [div_self (two_ne_zero), one_pow] at core
  have hA0 : 0 ≤ (2 / gg D) ^ ((s - 2) * D.R.k * D.R.f) := by
    have : 0 ≤ gg D := by linarith
    positivity
  have hbig0 : 0 ≤ LatticeSumBounds.bigH C D.R.m D.R.f large₂.sc.b ^ (C * ((s : ℝ) + D.R.m) * (D.R.m : ℝ) ^ 2) := by
    unfold LatticeSumBounds.bigH
    have := d_two_le_b D large₂
    positivity
  have hM0 : 0 ≤ ((D.R.k : ℝ) * D.host.v) ^ (D.R.k * D.R.f) * XiB D large₂ u C s * C ^ (D.R.k * D.R.f) *
      LatticeSumBounds.bigH C D.R.m D.R.f large₂.sc.b ^ (C * ((s : ℝ) + D.R.m) * (D.R.m : ℝ) ^ 2) * (C * s * D.R.f) ^ (6 * s * D.R.f) := by
    have : 0 ≤ XiB D large₂ u C s := hXs0.trans hXs
    have : 0 ≤ D.host.v := by linarith
    positivity
  unfold rows_degB rows_RD rows_Phi LatticeSumBounds.degRow
  unfold rows_P at core ⊢
  calc (2 / gg D) ^ ((s - 2) * D.R.k * D.R.f) * ((D.R.k : ℝ) * D.host.v / (Real.exp 1 * Real.pi)) ^ (D.R.k * D.R.f) *
        (XiS D u ((large₂.sc.b ^ pairCountExponentShift D c Ch) ^ 2) c s *
          (((large₂.sc.b ^ pairCountExponentShift D c Ch) ^ pairCountExponent D c s) ^ 2 * ((large₂.sc.b ^ pairCountExponentShift D c Ch) ^ (c * (D.R.rS : ℝ) ^ 2)) ^ 2 *
            (c * s * D.R.f) ^ (6 * s * D.R.f) * rows_GamD D large₂ Ca C2)) *
        ((41 ^ D.R.f * (large₂.sc.b ^ pairCountExponentShift D c Ch) ^ 3) ^ ((D.R.rS + 1) ^ 2)) ^ 2
      = (2 / gg D) ^ ((s - 2) * D.R.k * D.R.f) *
        (1 * ((D.R.k : ℝ) * D.host.v / (Real.exp 1 * Real.pi)) ^ (D.R.k * D.R.f) *
        (XiS D u ((large₂.sc.b ^ pairCountExponentShift D c Ch) ^ 2) c s *
          (((large₂.sc.b ^ pairCountExponentShift D c Ch) ^ pairCountExponent D c s) ^ 2 * ((large₂.sc.b ^ pairCountExponentShift D c Ch) ^ (c * (D.R.rS : ℝ) ^ 2)) ^ 2 *
            (c * s * D.R.f) ^ (6 * s * D.R.f) * rows_GamD D large₂ Ca C2)) * ((1 + 0) * 1) *
        ((41 ^ D.R.f * (large₂.sc.b ^ pairCountExponentShift D c Ch) ^ 3) ^ ((D.R.rS + 1) ^ 2)) ^ 2) := by ring
    _ ≤ (2 / gg D) ^ ((s - 2) * D.R.k * D.R.f) * _ := mul_le_mul_of_nonneg_left core hA0
    _ = (2 / gg D) ^ ((s - 2) * D.R.k * D.R.f) * ((((D.R.k : ℝ) * D.host.v) ^ (D.R.k * D.R.f) * XiB D large₂ u C s *
          C ^ (D.R.k * D.R.f) * LatticeSumBounds.bigH C D.R.m D.R.f large₂.sc.b ^ (C * ((s : ℝ) + D.R.m) * (D.R.m : ℝ) ^ 2) *
          (C * s * D.R.f) ^ (6 * s * D.R.f)) * rows_GamD D large₂ Ca C2) := by ring
    _ ≤ (2 / gg D) ^ ((s - 2) * D.R.k * D.R.f) * ((((D.R.k : ℝ) * D.host.v) ^ (D.R.k * D.R.f) * XiB D large₂ u C s *
          C ^ (D.R.k * D.R.f) * LatticeSumBounds.bigH C D.R.m D.R.f large₂.sc.b ^ (C * ((s : ℝ) + D.R.m) * (D.R.m : ℝ) ^ 2) *
          (C * s * D.R.f) ^ (6 * s * D.R.f)) * (GamS D large₂ * Real.exp (C * (D.R.m : ℝ) ^ 6 * D.R.f * Real.log large₂.sc.b) *
          (C / D.R.k) ^ (D.R.k * D.R.f))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (rows_GamD_le D large₂ hC2 hCa) hM0) hA0
    _ = _ := by ring

theorem rows_RowsDeg_record {C' Cl Cg cb Cu cT CT C0 A c Cpr Ca C2 Ch δ δm C : ℝ} {q : ℕ}
    (h : rows_Hyps Y C' Cl Cg cb Cu cT CT C0 A c Cpr Ca C2 Ch δ δm q) (hK : rows_KBound Y c) (hc1 : 1 ≤ c)
    (hcC : c ≤ C) (hC1 : 1 ≤ C)
    (hC : 4 + (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c + 2) ≤ C ^ 2) (hC2 : 2 * C2 ≤ C) (hCa : |Ca| ≤ C)
    (hq2 : 4 * (c * D.R.k) + 4 * pairCountExponent D c D.R.k + 4 * (c * (D.R.rS : ℝ) ^ 2) +
      (C2 * (D.R.m : ℝ) ^ 2 + C2 * (D.R.m : ℝ) ^ 4 * 2) / 2 + 12 * ((D.R.rS : ℝ) + 1) ^ 2 ≤
        (q : ℝ) / ((D.R.rS : ℝ) + 1)) : RowsDeg X Y C := by
  intro s hs hsk
  have hsk' : (s : ℝ) ≤ D.R.k := by exact_mod_cast hsk
  have hm : (0 : ℝ) ≤ D.R.m := Nat.cast_nonneg _
  have hE : pairCountExponent D c s ≤ pairCountExponent D c D.R.k := by
    unfold pairCountExponent
    have := mul_nonneg (mul_nonneg h.hc (sub_nonneg.2 hsk')) hm
    linarith
  have hq2s : 4 * (c * D.R.k) + 4 * pairCountExponent D c s + 4 * (c * (D.R.rS : ℝ) ^ 2) +
      (C2 * (D.R.m : ℝ) ^ 2 + C2 * (D.R.m : ℝ) ^ 4 * 2) / 2 + 12 * ((D.R.rS : ℝ) + 1) ^ 2 ≤
        (q : ℝ) / ((D.R.rS : ℝ) + 1) := by linarith
  exact rows_RowBound_mono Y (rows_Deg_record Y h hK hc1 s hs hsk hq2s)
    (rows_degB_le h.hH h.hc hcC hC1 hC hC2 hCa s) h.hdim.le

end Rec

section Fam

variable {eps : ℝ} (Fm : FamP eps) (C1 : ℝ) (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
  (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
    LoopTie (Fm.D x i) (Fm.L x i) (X x hx i) u u' C1)

end Fam

end Formalism.MainNotions.BridgeLemma₂

end
end

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticeCounting Formalism.MainNotions.BridgeLemma

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section KB

variable {D : D7} {large₂ : SizeData₂ D} {X : TermTie D} {u u' : D.what₂.Word} {C1 : ℝ} (Y : LoopTie D large₂ X u u' C1)

theorem rows_HHZ_eq (D : D7) (large₂ : SizeData₂ D) (c : ℝ) (Z : GramM D) :
    HHZ D large₂.sc.b c Z = large₂.sc.b ^ (c ^ 2 * (D.R.m : ℝ) ^ 3 * D.R.f) * sizeZ D large₂.sc.b c Z ^ 4 := by
  have hb0 : 0 < large₂.sc.b := by linarith [d_two_le_b D large₂]
  unfold HHZ
  rw [← Real.rpow_mul hb0.le]
  congr 2
  ring

theorem rows_bpow_le_HHZ (D : D7) (large₂ : SizeData₂ D) {c E : ℝ} (hE : E ≤ c ^ 2 * (D.R.m : ℝ) ^ 3 * D.R.f) (Z : GramM D) :
    large₂.sc.b ^ E ≤ HHZ D large₂.sc.b c Z := by
  have hb := d_two_le_b D large₂
  rw [rows_HHZ_eq]
  have h2 : 1 ≤ sizeZ D large₂.sc.b c Z ^ 4 := one_le_pow₀ (rows_one_le_sizeZ _ _ _)
  calc large₂.sc.b ^ E ≤ large₂.sc.b ^ (c ^ 2 * (D.R.m : ℝ) ^ 3 * D.R.f) := Real.rpow_le_rpow_of_exponent_le (by linarith) hE
    _ = large₂.sc.b ^ (c ^ 2 * (D.R.m : ℝ) ^ 3 * D.R.f) * 1 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by positivity)

theorem rows_Dr_le_HHZ (D : D7) (large₂ : SizeData₂ D) (hrd : 0 < D.host.rdE) (hr : 1 ≤ D.R.rS) {c : ℝ} (hc1 : 1 ≤ c) (Z : GramM D) :
    ∏ τ, max 1 (absDl D Z D.R.rS τ ^ 2) ≤ HHZ D large₂.sc.b c Z := by
  have hb := d_two_le_b D large₂
  have hb0 : 0 < large₂.sc.b := by linarith
  set H2 : ℝ := large₂.sc.b ^ (c * (D.R.m : ℝ) ^ 2) with hH2
  have hH21 : 1 ≤ H2 := Real.one_le_rpow (by linarith) (by positivity)
  have hm2 : (2 : ℝ) ≤ D.R.m := by
    rw [rows_m_cast]; have : (0 : ℝ) ≤ D.R.rS := by positivity
    linarith
  have each : ∀ τ, max 1 (absDl D Z D.R.rS τ ^ 2) ≤ (H2 * max 1 (absDl D Z D.R.rS τ / H2)) ^ 2 := by
    intro τ
    have hD0 := rows_absDl_nonneg hrd Z D.R.rS τ
    have a1 : 1 ≤ H2 * max 1 (absDl D Z D.R.rS τ / H2) := one_le_mul_of_one_le_of_one_le hH21 (le_max_left _ _)
    have a2 : absDl D Z D.R.rS τ ≤ H2 * max 1 (absDl D Z D.R.rS τ / H2) := by
      calc absDl D Z D.R.rS τ = H2 * (absDl D Z D.R.rS τ / H2) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_right _ _) (by linarith)
    exact max_le (one_le_pow₀ a1) (pow_le_pow_left₀ hD0 a2 2)
  have single : ∀ τ, max 1 (absDl D Z D.R.rS τ / H2) ≤
      ∏ l ∈ Finset.Icc 1 (D.R.rS + 1), max 1 (absDl D Z l τ / H2) := by
    intro τ
    have hmem : D.R.rS ∈ Finset.Icc 1 (D.R.rS + 1) := Finset.mem_Icc.2 ⟨hr, Nat.le_succ _⟩
    rw [← Finset.mul_prod_erase _ _ hmem]
    exact le_mul_of_one_le_right (le_trans zero_le_one (le_max_left _ _))
      (rows_one_le_prod _ _ fun l _ => le_max_left _ _)
  have hs1 := rows_one_le_sizeZ (D := D) large₂.sc.b c Z
  calc ∏ τ, max 1 (absDl D Z D.R.rS τ ^ 2)
      ≤ ∏ τ : D.what₂.Tau, (H2 * max 1 (absDl D Z D.R.rS τ / H2)) ^ 2 :=
        Finset.prod_le_prod₀ (fun τ _ => le_trans zero_le_one (le_max_left _ _)) fun τ _ => each τ
    _ = (H2 ^ D.R.f * ∏ τ : D.what₂.Tau, max 1 (absDl D Z D.R.rS τ / H2)) ^ 2 := by
        rw [Finset.prod_pow, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, D.what₂.card_Tau]
    _ ≤ (H2 ^ D.R.f * sizeZ D large₂.sc.b c Z) ^ 2 := by
        apply pow_le_pow_left₀ (mul_nonneg (by positivity)
          (Finset.prod_nonneg fun τ _ => le_trans zero_le_one (le_max_left _ _)))
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        unfold sizeZ
        exact Finset.prod_le_prod₀ (fun τ _ => le_trans zero_le_one (le_max_left _ _)) fun τ _ => single τ
    _ = (H2 ^ D.R.f) ^ 2 * sizeZ D large₂.sc.b c Z ^ 2 := by ring
    _ ≤ large₂.sc.b ^ (c ^ 2 * (D.R.m : ℝ) ^ 3 * D.R.f) * sizeZ D large₂.sc.b c Z ^ 4 := by
        apply mul_le_mul _ (pow_le_pow_right₀ hs1 (by norm_num)) (by positivity) (by positivity)
        rw [hH2, rows_rpow_pow hb0, rows_rpow_pow hb0]
        apply Real.rpow_le_rpow_of_exponent_le (by linarith)
        push_cast
        have h0 : 0 ≤ c * (D.R.m : ℝ) ^ 2 * D.R.f := by positivity
        have h1 : (2 : ℝ) ≤ c * D.R.m := by nlinarith
        calc c * (D.R.m : ℝ) ^ 2 * D.R.f * 2 = (c * (D.R.m : ℝ) ^ 2 * D.R.f) * 2 := by ring
          _ ≤ (c * (D.R.m : ℝ) ^ 2 * D.R.f) * (c * D.R.m) := mul_le_mul_of_nonneg_left h1 h0
          _ = _ := by ring
    _ = _ := (rows_HHZ_eq D large₂ c Z).symm

theorem rows_KBound_of {C' Cl Cg cb Cu cT CT C0 A c : ℝ} (hH : Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A)
    (hHH : UnitaryVolumeMass.stHH D large₂ u u' C' Cl Cg cb Cu cT CT C0 A c) (hc1 : 1 ≤ c) (hCT : CT ≤ c) : rows_KBound Y c := by
  intro t hG hrel
  have hrd := d_rdE_pos hH.1
  have hb := d_two_le_b D large₂
  have hb0 : 0 < large₂.sc.b := by linarith
  have hHH1 := rows_one_le_HHZ D large₂ (by linarith : 0 ≤ c) (termGramMatrix X t)
  by_cases hD : Dr (X.fl t) (X.fl' t) = 0
  · have e : rows_Kt Y t = 1 := by
      unfold rows_Kt
      refine Finset.prod_eq_one fun τ _ => ?_
      unfold chRatio
      rw [if_pos ((rows_Dr_zero_iff Y hrd t τ).2 hD)]
    rw [e, one_pow]
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ hHH1)
  · have eK : rows_Kt Y t = ∏ τ, (1 + Lat.ch (Tu D u) (Tu D u') (X.fl t) (X.fl' t) (embS D τ)) /
        Lat.sh (Tu D u) (Tu D u') (X.fl t) (X.fl' t) (embS D τ) := by
      unfold rows_Kt
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [rows_chRatio_eq Y hrd t τ]
      unfold onePlusChSh
      rw [if_neg hD]
    have hT1 : 1 ≤ Tr D u := by unfold Tr; exact_mod_cast (D.mem u).A.T_prime.pos
    have hT1' : 1 ≤ Tr D u' := by unfold Tr; exact_mod_cast (D.mem u').A.T_prime.pos
    have hDpos : ∀ τ, 0 < absDl D (termGramMatrix X t) D.R.rS τ := by
      intro τ
      rw [← d_norm_Dmin Y hrd t τ D.R.rS (Nat.le_succ _)]
      exact norm_pos_iff.2 fun h => hD ((rows_Dr_zero_iff Y hrd t τ).1 h)
    have hGeq : ∀ τ, Formalism.MainNotions.S.Cnt.Gz D (Tu D u) (Tu D u') (termGramMatrix X t) τ = Tr D u * Tr D u' * absDl D (termGramMatrix X t) D.R.rS τ ^ 2 *
        Lat.sh (Tu D u) (Tu D u') (X.fl t) (X.fl' t) (embS D τ) ^ 2 := by
      intro τ
      have h := rowsT_nu_eq Y hrd t hG hrel hD τ
      unfold nuV at h
      rw [d_Gf_eq Y hrd t τ, d_norm_Dmin Y hrd t τ D.R.rS (Nat.le_succ _)] at h
      have hne : Tr D u * absDl D (termGramMatrix X t) D.R.rS τ ^ 2 ≠ 0 := by
        have := hDpos τ
        positivity
      rw [div_eq_iff hne] at h
      rw [h]; ring
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h23, _, _⟩ := hH.1.1
    have hm2 : (2 : ℝ) ≤ D.R.m := by
      rw [rows_m_cast]; have : (0 : ℝ) ≤ D.R.rS := by positivity
      linarith
    have h6 : (Tr D u * Tr D u') ^ Fintype.card D.what₂.Tau ≤ HHZ D large₂.sc.b c (termGramMatrix X t) := by
      rw [D.what₂.card_Tau]
      have a1 : Tr D u * Tr D u' ≤ large₂.sc.b ^ (2 * (c * D.R.m)) := by
        have b1 : Tr D u ≤ large₂.sc.b ^ (c * (D.R.m : ℝ)) := (h23 u).2.trans
          (Real.rpow_le_rpow_of_exponent_le (by linarith) (by gcongr))
        have b2 : Tr D u' ≤ large₂.sc.b ^ (c * (D.R.m : ℝ)) := (h23 u').2.trans
          (Real.rpow_le_rpow_of_exponent_le (by linarith) (by gcongr))
        calc Tr D u * Tr D u' ≤ large₂.sc.b ^ (c * (D.R.m : ℝ)) * large₂.sc.b ^ (c * (D.R.m : ℝ)) :=
              mul_le_mul b1 b2 (by linarith) (by positivity)
          _ = _ := by rw [← Real.rpow_add hb0]; congr 1; ring
      calc (Tr D u * Tr D u') ^ D.R.f ≤ (large₂.sc.b ^ (2 * (c * D.R.m))) ^ D.R.f :=
            pow_le_pow_left₀ (by positivity) a1 _
        _ = large₂.sc.b ^ (2 * (c * D.R.m) * D.R.f) := rows_rpow_pow hb0 _ _
        _ ≤ _ := rows_bpow_le_HHZ D large₂ (by
            have h0 : 0 ≤ c * (D.R.m : ℝ) * D.R.f := by positivity
            have h1 : (2 : ℝ) ≤ c * (D.R.m : ℝ) ^ 2 := by nlinarith
            calc 2 * (c * (D.R.m : ℝ)) * D.R.f = (c * (D.R.m : ℝ) * D.R.f) * 2 := by ring
              _ ≤ (c * (D.R.m : ℝ) * D.R.f) * (c * (D.R.m : ℝ) ^ 2) := mul_le_mul_of_nonneg_left h1 h0
              _ = _ := by ring) _
    have h8 : ∏ τ, max 1 (1 / Formalism.MainNotions.S.Cnt.Gz D (Tu D u) (Tu D u') (termGramMatrix X t) τ) ≤ HHZ D large₂.sc.b c (termGramMatrix X t) := by
      simp only [one_div]
      exact (rowsT_HH_term Y hH hHH t hG hrel).2.2.1
    have key := Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.degFactorBound D.what₂.Tau
      (fun τ => Lat.sh (Tu D u) (Tu D u') (X.fl t) (X.fl' t) (embS D τ))
      (fun τ => Lat.ch (Tu D u) (Tu D u') (X.fl t) (X.fl' t) (embS D τ))
      (fun τ => Formalism.MainNotions.S.Cnt.Gz D (Tu D u) (Tu D u') (termGramMatrix X t) τ) (fun τ => absDl D (termGramMatrix X t) D.R.rS τ)
      (Tr D u) (Tr D u') (HHZ D large₂.sc.b c (termGramMatrix X t)) (one_le_mul_of_one_le_of_one_le hT1 hT1')
      (fun τ => ⟨rowsT_sh_pos Y hrd t hG hrel hD τ, by
        unfold Lat.ch; exact div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _), rowsT_ch_sq Y hrd t hG hrel hD τ⟩)
      (fun τ => rowsT_Gz_pos Y hrd t hG hrel τ) hDpos hGeq h6
      (rows_Dr_le_HHZ D large₂ hrd hH.2.1.1 hc1 _) h8
    rw [D.what₂.card_Tau] at key
    rw [eK]
    exact key

end KB

section Fam

variable {eps : ℝ} (Fm : FamP eps) (C1 : ℝ) (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
  (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
    LoopTie (Fm.D x i) (Fm.L x i) (X x hx i) u u' C1)

end Fam

end Formalism.MainNotions.BridgeLemma₂

end
