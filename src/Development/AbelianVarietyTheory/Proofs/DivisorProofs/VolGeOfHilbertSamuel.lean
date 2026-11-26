module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodHermitianLineBundlePair
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMetricShiftIsNefPowTensAmple

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairBallsFinite
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairBallsFinite
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VolBr.BallFinite

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem exists_rep (P : Pair p) (a c : ℤ) : ∃ M : HermLB p, P.Rep a c M := by
  obtain ⟨hL, hA, -⟩ := GlobalTheory.T.represents_base_bundles_and_trivial k X p P
  have h1 : ∃ M : HermLB p, P.Rep a 0 M := by
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg a
    · have := GlobalTheory.T.represents_hermitianLineBundle_pow k X p P 1 0 P.L n hL
      rw [mul_one, mul_zero] at this
      exact ⟨_, this⟩
    · have := GlobalTheory.T.represents_hermitianLineBundle_dual k X p P _ _ _ (GlobalTheory.T.represents_hermitianLineBundle_pow k X p P 1 0 P.L n hL)
      rw [mul_one, mul_zero, neg_zero] at this
      exact ⟨_, this⟩
  have h2 : ∃ M : HermLB p, P.Rep 0 c M := by
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg c
    · have := GlobalTheory.T.represents_hermitianLineBundle_pow k X p P 0 1 P.A n hA
      rw [mul_one, mul_zero] at this
      exact ⟨_, this⟩
    · have := GlobalTheory.T.represents_hermitianLineBundle_dual k X p P _ _ _ (GlobalTheory.T.represents_hermitianLineBundle_pow k X p P 0 1 P.A n hA)
      rw [mul_one, mul_zero, neg_zero] at this
      exact ⟨_, this⟩
  obtain ⟨M₁, h₁⟩ := h1
  obtain ⟨M₂, h₂⟩ := h2
  have := GlobalTheory.T.hermPairWithSections_represents_tensor k X p P _ _ _ _ M₁ M₂ h₁ h₂
  rw [add_zero, zero_add] at this
  exact ⟨_, this⟩

theorem nu_nonneg (P : Pair p) (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField) :
    0 ≤ P.nu a b σ y f :=
  mul_nonneg (norm_nonneg _) (Real.exp_pos _).le

theorem smallSec_tens_shift (N M : HermLB p) (t : ℝ) :
    ((N.tens M).shift (fun _ => t) fun _ => rfl).smallSec ⊆ (N.tens (M.shift (fun _ => t) fun _ => rfl)).smallSec :=
  fun u hu σ y => by
    refine le_of_eq_of_le ?_ (hu σ y)
    simp only [Weight.nsq, HermLB.tens, HermLB.shift, Weight.tens, Weight.addFn]
    congr 2
    ring

theorem bl_finite : GlobalTheory.Published.ArithHilbertSamuel → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (b : ℕ) (s t : X.functionField), P.Good D b s t →
    ∀ (a c : ℤ) (R : ℝ), GlobalTheory.Published.ArCalc → (P.Bl a c R).Finite := by
  intro hHS k _ X _ p D hX P b s t hG a c R hC
  obtain ⟨M, hM⟩ := exists_rep P a c
  obtain ⟨Φ, hΦ⟩ := ((hC.arExists k X p D hX).2 Unit (fun _ => P.A)).1
  have hSI := ((hC.arIso k X p D hX).2 Unit (fun _ => P.A) Φ hΦ).1 ()
  obtain ⟨m, hm⟩ := ((hHS k X p D hX P.A (M.shift (fun _ => R) fun _ => rfl) _ hG.nef hSI).1).exists
  have hA := (GlobalTheory.T.represents_base_bundles_and_trivial k X p P).2.1
  have hAm := GlobalTheory.T.represents_hermitianLineBundle_pow k X p P 0 1 P.A m hA
  have hT := GlobalTheory.T.hermPairWithSections_represents_tensor k X p P _ _ _ _ _ _ hAm hM
  have hsm : (((P.A.pow m).tens M).shift (fun _ => R) fun _ => rfl).smallSec.Finite :=
    hm.subset (smallSec_tens_shift _ _ _)
  have hB : (P.Bl (m * 0 + a) (m * 1 + c) (Real.exp R)).Finite := by
    have e := (GlobalTheory.T.smallSections_twistedPower_encard_eq_ball k X p P _ _ _ hT R 0).2.2
    rw [← Set.encard_lt_top_iff, ← e]
    exact hsm.encard_lt_top
  have hs := hG.s_mem
  obtain ⟨hsH, hsn⟩ := GlobalTheory.T.hermPair_pow_section_mem_and_norm_pow k X p P 0 1 s hs.1 m
  refine (hB.preimage (f := fun f => s ^ m * f) (mul_right_injective₀ (pow_ne_zero m hG.s_ne)).injOn).subset ?_
  intro f hf
  obtain ⟨h1, h2⟩ := GlobalTheory.T.hermLineBundlePair_sections_mul_mem_norm_mul k X p P _ _ _ _ (s ^ m) f hsH hf.1
  refine ⟨h1, fun σ y => ?_⟩
  rw [h2, hsn]
  have n1 : P.nu 0 1 σ y s ≤ 1 := hs.2 σ y
  calc _ ≤ 1 * P.nu a c σ y f :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ (nu_nonneg P 0 1 σ y s) n1) (nu_nonneg P a c σ y f)
    _ ≤ Real.exp R := by rw [one_mul]; exact (hf.2 σ y).trans (by linarith [Real.add_one_le_exp R])

end GlobalTheory.VolBr.BallFinite
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairBallsFiniteStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermLineBundlePair_balls_finite : GlobalTheory.Published.ArithHilbertSamuel → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ (a c : ℤ) (R : ℝ), GlobalTheory.Published.ArCalc → (P.Bl a c R).Finite := by
  first | exact @GlobalTheory.VolBr.BallFinite.bl_finite | exact GlobalTheory.VolBr.BallFinite.bl_finite | (intros; apply GlobalTheory.VolBr.BallFinite.bl_finite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelLogBallCountTendsto
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLineBundleIsNefShiftMonotone
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLineBundleIsNefShiftMonotone
noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.NefShift

theorem isNef_shift_mono : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (M : HermLB p) (t t' : ℝ), t ≤ t' →
    (M.shift (fun _ => t) fun _ => rfl).IsNef D → (M.shift (fun _ => t') fun _ => rfl).IsNef D := by
  intro _ k _ X _ p D hX M t t' htt h
  refine ⟨fun σ => ?_, h.vertical, ?_⟩
  · have := (h.semiPos σ).addFn_const (2 * (t' - t))
    have e : (((M.shift (fun _ => t) fun _ => rfl).φ σ).addFn fun _ => 2 * (t' - t)) =
        (M.shift (fun _ => t') fun _ => rfl).φ σ := by
      simp only [HermLB.shift, Weight.addFn]
      congr 1
      funext a b
      ring
    exact e ▸ this
  · intro Z i _ _ _ hc hd
    obtain ⟨r, hr, h0⟩ := h.horizontal Z i hc hd
    refine ⟨r, hr, ?_⟩
    have e₁ := HtSelfInter.curveDeg_shift hX M t i hc hd (r := r) hr
    have e₂ := HtSelfInter.curveDeg_shift hX M t' i hc hd (r := r) hr
    rw [e₂]
    rw [e₁] at h0
    nlinarith [(Nat.cast_nonneg _ : (0:ℝ) ≤ Nat.card (X.residueField (i (genericPoint Z)) →+* ℂ))]

end GlobalTheory.NefShift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLineBundleIsNefShiftMonotoneStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianLineBundle_isNef_shift_monotone : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (M : HermLB p) (t t' : ℝ), t ≤ t' → (M.shift (fun _ => t) fun _ => rfl).IsNef D → (M.shift (fun _ => t') fun _ => rfl).IsNef D := by
  first | exact @GlobalTheory.NefShift.isNef_shift_mono | exact GlobalTheory.NefShift.isNef_shift_mono | (intros; apply GlobalTheory.NefShift.isNef_shift_mono <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelLogBallCountTendsto
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem lc_tendsto_of_rep : GlobalTheory.Published.ArithHilbertSamuel → GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (a b : ℤ) (M : HermLB p) (α t₀ : ℝ), P.Rep a b M → M.IsSelfInter α → (M.shift (fun _ => t₀) fun _ => rfl).IsNef D → ∀ t, t₀ ≤ t → Tendsto (fun m : ℕ => P.lc (m * a) (m * b) (Real.exp (t * m)) / (m : ℝ) ^ (D + 1)) atTop (𝓝 (α / (D + 1).factorial + ((D + 1) * gdeg M D / (D + 1).factorial) * t)) := by
  intro hHS hC k _ X _ p D hX P a b M α t₀ hRep hα hN t ht
  have hNt := GlobalTheory.T.hermitianLineBundle_isNef_shift_monotone hC k X p D hX M t₀ t ht hN
  have hSt := hC.arShift k X p D hX M α t hα
  have hT := GlobalTheory.Published.ArithHilbertSamuel.tendsto_of_triv hHS hX hNt hSt
  have hF : ((D + 1).factorial : ℝ) ≠ 0 := by positivity
  have h2 := hT.div_const ((D + 1).factorial : ℝ)
  have e (m : ℕ) : P.lc (m * a) (m * b) (Real.exp (t * m)) =
      Real.log ((((M.shift (fun _ => t) fun _ => rfl).pow m).smallSec.ncard : ℝ)) := by
    rw [Pair.lc, Set.ncard_def, Set.ncard_def, (GlobalTheory.T.smallSections_twistedPower_encard_eq_ball k X p P a b M hRep t m).1]
  convert (preTransparency := .reducible) h2 using 1
  · funext m
    rw [e]
    field_simp
  · field_simp

end GlobalTheory.VolBr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelLogBallCountTendstoStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_hilbertSamuel_log_ball_count_tendsto : GlobalTheory.Published.ArithHilbertSamuel → GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (a b : ℤ) (M : HermLB p) (α t₀ : ℝ), P.Rep a b M → M.IsSelfInter α → (M.shift (fun _ => t₀) fun _ => rfl).IsNef D → ∀ t, t₀ ≤ t → Tendsto (fun m : ℕ => P.lc (m * a) (m * b) (Real.exp (t * m)) / (m : ℝ) ^ (D + 1)) atTop (𝓝 (α / (D + 1).factorial + ((D + 1) * gdeg M D / (D + 1).factorial) * t)) := by
  first | exact @GlobalTheory.VolBr.lc_tendsto_of_rep | exact GlobalTheory.VolBr.lc_tendsto_of_rep | (intros; apply GlobalTheory.VolBr.lc_tendsto_of_rep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionCountContinuousFromAbove
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionCountLePowGoodPair
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionCountLePowGoodPair
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem lc_le_of_good {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} (P : Pair p)
    {D b : ℕ} {s t : X.functionField} (hG : P.Good D b s t) (N : ℕ) (R : ℝ)
    (hfin : (P.Bl 0 ((N : ℤ) * b) R).Finite) :
    P.lc N 0 R ≤ P.lc 0 ((N : ℤ) * b) R := by
  have nu_nonneg : ∀ (a c : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField), 0 ≤ P.nu a c σ y f :=
    fun a c σ y f => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  obtain ⟨htH, htn⟩ := hG.t_mem
  obtain ⟨hpH, hpn⟩ := GlobalTheory.T.hermPair_pow_section_mem_and_norm_pow k X p P (-1) b t htH N
  have e1 : (N : ℤ) + N * -1 = 0 := by ring
  have e2 : (0 : ℤ) + N * b = N * b := by ring
  have hmaps : ∀ f ∈ P.Bl N 0 R, f * t ^ N ∈ P.Bl 0 ((N : ℤ) * b) R := by
    rintro f ⟨hfH, hfn⟩
    obtain ⟨hH, hn⟩ := GlobalTheory.T.hermLineBundlePair_sections_mul_mem_norm_mul k X p P N 0 (N * -1) (N * b) f (t ^ N) hfH hpH
    rw [e1, e2] at hH hn
    refine ⟨hH, fun σ y => ?_⟩
    rw [hn σ y, hpn σ y]
    have h1 : P.nu (-1) b σ y t ^ N ≤ 1 := pow_le_one₀ (nu_nonneg _ _ _ _ _) (htn σ y)
    exact (mul_le_of_le_one_right (nu_nonneg _ _ _ _ _) h1).trans (hfn σ y)
  have hinj : Set.InjOn (fun f => f * t ^ N) (P.Bl N 0 R) := fun x _ y _ h =>
    mul_right_cancel₀ (pow_ne_zero N hG.t_ne) h
  have hcard := Set.ncard_le_ncard_of_injOn _ hmaps hinj hfin
  unfold Pair.lc
  rcases Nat.eq_zero_or_pos (P.Bl N 0 R).ncard with h0 | h0
  · rw [h0, Nat.cast_zero, Real.log_zero]
    exact Real.log_natCast_nonneg _
  · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hcard)

theorem crude_upper_lc : GlobalTheory.Published.ArithHilbertSamuel → GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (b : ℕ) (s t : X.functionField), P.Good D b s t → ∃ C : ℝ, ∀ᶠ N : ℕ in atTop, P.lc N 0 (Real.exp (3 * N)) ≤ C * (N : ℝ) ^ (D + 1) := by
  intro hHS hAC k _ X _ p D hX P b s t hG
  have hRep : P.Rep 0 (b : ℤ) (P.A.pow b) := by
    have := GlobalTheory.T.represents_hermitianLineBundle_pow k X p P 0 1 P.A b (GlobalTheory.T.represents_base_bundles_and_trivial k X p P).2.1
    simpa using this
  have hnef : (P.A.pow b).IsNef D := GlobalTheory.T.isNef_pow_of_isNef hAC k X p D hX P.A b hG.nef
  have hnef0 : ((P.A.pow b).shift (fun _ => (0 : ℝ)) fun _ => rfl).IsNef D :=
    GlobalTheory.T.hermitianLineBundle_isNef_shift_of_nonneg k X p D hX (P.A.pow b) 0 le_rfl hnef
  obtain ⟨Φ, hΦ⟩ := ((hAC.arExists k X p D hX).2 Unit (fun _ => P.A.pow b)).1
  have hα := ((hAC.arIso k X p D hX).2 Unit (fun _ => P.A.pow b) Φ hΦ).1 ()
  have hlim := GlobalTheory.T.arith_hilbertSamuel_log_ball_count_tendsto hHS hAC k X p D hX P 0 b (P.A.pow b) _ 0 hRep hα hnef0 3 (by norm_num)
  obtain ⟨C, hev⟩ : ∃ C : ℝ, ∀ᶠ m : ℕ in atTop,
      P.lc ((m : ℤ) * 0) ((m : ℤ) * b) (Real.exp (3 * m)) / (m : ℝ) ^ (D + 1) < C :=
    ⟨_, hlim.eventually (gt_mem_nhds (lt_add_one _))⟩
  refine ⟨C, ?_⟩
  filter_upwards [hev, eventually_ge_atTop 1] with N hN hN1
  have hpos : (0 : ℝ) < (N : ℝ) ^ (D + 1) := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    positivity
  rw [div_lt_iff₀ hpos] at hN
  simp only [mul_zero] at hN
  refine le_trans ?_ hN.le
  exact lc_le_of_good P hG N _ (GlobalTheory.T.hermLineBundlePair_balls_finite hHS k X p D hX P b s t hG 0 _ _ hAC)

end GlobalTheory.VolBr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionCountLePowGoodPairStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smallSectionCount_le_pow_goodPair : GlobalTheory.Published.ArithHilbertSamuel → GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (b : ℕ) (s t : X.functionField), P.Good D b s t → ∃ C : ℝ, ∀ᶠ N : ℕ in atTop, P.lc N 0 (Real.exp (3 * N)) ≤ C * (N : ℝ) ^ (D + 1) := by
  first | exact @GlobalTheory.VolBr.crude_upper_lc | exact GlobalTheory.VolBr.crude_upper_lc | (intros; apply GlobalTheory.VolBr.crude_upper_lc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionCountNearPowersLe
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyLeOfPolyAsymptotics
open Filter Topology GlobalTheory.VolBr

namespace GlobalTheory

theorem eventually_le_of_poly_asymptotics :
    ∀ (d b : ℕ) (f : ℝ → ℕ → ℝ) (g : ℕ → ℝ) (α β : ℝ), 0 < d → 0 < b →
      (∀ η, 0 ≤ η → Tendsto (fun j : ℕ => f η j / (j : ℝ) ^ d) atTop (𝓝 (α + β * η))) →
      (∀ η, 0 < η → ∀ᶠ j : ℕ in atTop, g j ≤ f η j) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ᶠ m : ℕ in atTop,
        g ((b * n + 1) * m) ≤ f 0 (b * n * m) + ε * ((n : ℝ) * m) ^ d := by
  intro d b f g α β _hd hb hf hg ε hε
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hc : (0 : ℝ) < (b : ℝ) ^ d := pow_pos hbR d
  obtain ⟨η, θ, hη, hθ, key⟩ : ∃ η θ : ℝ, 0 < η ∧ 0 < θ ∧ (β * η + 2 * θ) * (b : ℝ) ^ d < ε := by
    generalize (b : ℝ) ^ d = c at hc ⊢
    have hβ1 : (0 : ℝ) < |β| + 1 := by positivity
    refine ⟨ε / (4 * c * (|β| + 1)), ε / (8 * c), div_pos hε (by positivity),
      div_pos hε (by positivity), ?_⟩
    have e1 : (|β| + 1) * (ε / (4 * c * (|β| + 1))) * c = ε / 4 := by
      field_simp
    have e2 : ε / (8 * c) * c = ε / 8 := by
      field_simp
    have h1 : β * (ε / (4 * c * (|β| + 1))) * c ≤ |β| * (ε / (4 * c * (|β| + 1))) * c :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self β)
        (div_pos hε (by positivity)).le) hc.le
    have h2 : 0 < ε / (4 * c * (|β| + 1)) * c := mul_pos (div_pos hε (by positivity)) hc
    nlinarith
  set A : ℝ := α + β * η + θ with hAdef
  set B : ℝ := α - θ with hBdef
  have hlim : Tendsto (fun n : ℕ => A * ((b : ℝ) + 1 / (n : ℝ)) ^ d) atTop (𝓝 (A * (b : ℝ) ^ d)) := by
    have := ((tendsto_one_div_atTop_nhds_zero_nat.const_add (b : ℝ)).pow d).const_mul A
    simpa using this
  have hn : ∀ᶠ n : ℕ in atTop, A * ((b : ℝ) + 1 / (n : ℝ)) ^ d < B * (b : ℝ) ^ d + ε :=
    (tendsto_order.1 hlim).2 _ (by rw [hAdef, hBdef]; nlinarith)
  have hAe : ∀ᶠ j : ℕ in atTop, f η j / (j : ℝ) ^ d < A :=
    (tendsto_order.1 (hf η hη.le)).2 A (by rw [hAdef]; linarith)
  have hBe : ∀ᶠ j : ℕ in atTop, B < f 0 j / (j : ℝ) ^ d :=
    (tendsto_order.1 (hf 0 le_rfl)).1 B (by rw [hBdef, mul_zero, add_zero]; linarith)
  filter_upwards [hn, eventually_ge_atTop 1] with n hn hn1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hk : Tendsto (fun m : ℕ => (b * n + 1) * m) atTop atTop :=
    tendsto_atTop_mono (fun m => Nat.le_mul_of_pos_left m (Nat.succ_pos _)) tendsto_id
  have hk' : Tendsto (fun m : ℕ => b * n * m) atTop atTop :=
    tendsto_atTop_mono (fun m => Nat.le_mul_of_pos_left m (Nat.mul_pos hb hn1)) tendsto_id
  filter_upwards [hk.eventually (hAe.and (hg η hη)), hk'.eventually hBe, eventually_gt_atTop 0]
    with m ⟨hA1, hG1⟩ hB1 hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hj : (((b * n + 1) * m : ℕ) : ℝ) = ((b : ℝ) + 1 / (n : ℝ)) * ((n : ℝ) * m) := by
    push_cast
    rw [show ((b : ℝ) + 1 / (n : ℝ)) * ((n : ℝ) * (m : ℝ))
        = (b : ℝ) * n * m + ((n : ℝ)⁻¹ * (n : ℝ)) * m by ring, inv_mul_cancel₀ hnR.ne']
    ring
  have hj' : ((b * n * m : ℕ) : ℝ) = (b : ℝ) * ((n : ℝ) * m) := by push_cast; ring
  have hjpos : (0 : ℝ) < (((b * n + 1) * m : ℕ) : ℝ) := by
    rw [hj]; positivity
  have hj'pos : (0 : ℝ) < ((b * n * m : ℕ) : ℝ) := by
    rw [hj']; positivity
  have hnm : (0 : ℝ) < ((n : ℝ) * m) ^ d := pow_pos (mul_pos hnR hmR) d
  have hA2 := (div_lt_iff₀ (pow_pos hjpos d)).1 hA1
  have hB2 := (lt_div_iff₀ (pow_pos hj'pos d)).1 hB1
  calc g ((b * n + 1) * m) ≤ f η ((b * n + 1) * m) := hG1
    _ ≤ A * ((((b * n + 1) * m : ℕ) : ℝ)) ^ d := hA2.le
    _ = (A * ((b : ℝ) + 1 / (n : ℝ)) ^ d) * ((n : ℝ) * m) ^ d := by rw [hj, mul_pow]; ring
    _ ≤ (B * (b : ℝ) ^ d + ε) * ((n : ℝ) * m) ^ d := mul_le_mul_of_nonneg_right hn.le hnm.le
    _ = B * (((b * n * m : ℕ) : ℝ)) ^ d + ε * ((n : ℝ) * m) ^ d := by rw [hj', mul_pow]; ring
    _ ≤ f 0 (b * n * m) + ε * ((n : ℝ) * m) ^ d := by linarith

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionCountNearPowersLe
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem lc_two_le_lc_one_add (hHS : GlobalTheory.Published.ArithHilbertSamuel) (hA : GlobalTheory.Published.ArCalc) (k : Type) [CommRing k]
    (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsArithVar p D) (P : Pair p) (b : ℕ)
    (s t : X.functionField) (hG : P.Good D b s t) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ᶠ m : ℕ in atTop,
      P.lc 0 (b * (n * m : ℕ) + m) 2 ≤ P.lc 0 (b * (n * m : ℕ)) 1 + ε * ((n : ℝ) * m) ^ (D + 1) := by
  obtain ⟨h, hh⟩ := (hA.1 k X p D hX).1 P.A
  have hα : P.A.IsSelfInter (h (genericPoint X)) := ⟨h, hh, rfl⟩
  have hnef := GlobalTheory.T.hermitianLineBundle_isNef_shift_of_nonneg k X p D hX P.A 0 le_rfl hG.nef
  have hrep : P.Rep 0 1 P.A := (GlobalTheory.T.represents_base_bundles_and_trivial k X p P).2.1
  have key := GlobalTheory.eventually_le_of_poly_asymptotics (D + 1) b
    (fun η j => P.lc 0 (j : ℤ) (Real.exp (η * j))) (fun j => P.lc 0 (j : ℤ) 2)
    (h (genericPoint X) / (D + 1).factorial) ((D + 1) * gdeg P.A D / (D + 1).factorial) (Nat.succ_pos D) hG.pos
    (fun η hη => by
      have := GlobalTheory.T.arith_hilbertSamuel_log_ball_count_tendsto hHS hA k X p D hX P 0 1 P.A (h (genericPoint X)) 0 hrep hα hnef η hη
      simpa only [mul_zero, mul_one] using this)
    (fun η hη => by
      have h1 : ∀ᶠ j : ℕ in atTop, Real.log 2 ≤ η * j :=
        (tendsto_natCast_atTop_atTop.const_mul_atTop hη).eventually_ge_atTop _
      filter_upwards [h1] with j hj
      have h2 : (2 : ℝ) ≤ Real.exp (η * j) := by
        calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
          _ ≤ _ := Real.exp_le_exp.2 hj
      have hsub : P.Bl 0 (j : ℤ) 2 ⊆ P.Bl 0 (j : ℤ) (Real.exp (η * j)) :=
        fun f hf => ⟨hf.1, fun σ y => (hf.2 σ y).trans h2⟩
      have hfin := GlobalTheory.T.hermLineBundlePair_balls_finite hHS k X p D hX P b s t hG 0 (j : ℤ) (Real.exp (η * j)) hA
      have hle := Set.ncard_le_ncard hsub hfin
      simp only [Pair.lc]
      rcases Nat.eq_zero_or_pos (P.Bl 0 (j : ℤ) 2).ncard with h0 | h0
      · rw [h0, Nat.cast_zero, Real.log_zero]
        exact Real.log_natCast_nonneg _
      · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hle))
    ε hε
  filter_upwards [key] with n hn
  filter_upwards [hn] with m hm
  have e1 : (((b * n + 1) * m : ℕ) : ℤ) = (b : ℤ) * ((n * m : ℕ) : ℤ) + (m : ℤ) := by push_cast; ring
  have e2 : (((b * n * m : ℕ)) : ℤ) = (b : ℤ) * ((n * m : ℕ) : ℤ) := by push_cast; ring
  simp only [e1, e2, zero_mul, Real.exp_zero] at hm
  exact hm

end GlobalTheory.VolBr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionCountNearPowersLeStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smallSectionCount_nearPowers_le : GlobalTheory.Published.ArithHilbertSamuel → GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ᶠ m : ℕ in atTop, P.lc 0 (b * (n * m : ℕ) + m) 2 ≤ P.lc 0 (b * (n * m : ℕ)) 1 + ε * ((n : ℝ) * m) ^ (D + 1) := by
  first | exact @GlobalTheory.VolBr.lc_two_le_lc_one_add | exact GlobalTheory.VolBr.lc_two_le_lc_one_add | (intros; apply GlobalTheory.VolBr.lc_two_le_lc_one_add <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSmallSectionBallOfMulPowSection
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSmallSectionBallOfMulPowSection
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.VolBr.MpDiv

theorem mem_Bl_of_mul_pow : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ s : X.functionField, s ∈ P.H 0 1 → s ≠ 0 → ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧ ∀ (N m : ℕ) (f : X.functionField), f ∈ P.H N 0 → f * s ^ m ∈ P.Bl N m 2 → f ∈ P.Bl N 0 (2 * Real.exp (δ * N + C * m)) := by
  intro k _ X _ p D hX P s hs hs0 δ hδ
  obtain ⟨ρ, hρ, H⟩ := GlobalTheory.T.arith_global_maximum_principle_off_divisor k X p D hX P s hs hs0 δ hδ
  refine ⟨max 0 (-Real.log ρ), le_max_left _ _, fun N m f hf hfs => ?_⟩
  set C : ℝ := max 0 (-Real.log ρ) with hC
  have key := H N f (2 * Real.exp (C * m)) hf (fun σ y hy => ?_)
  · have e : Real.exp (δ * N) * (2 * Real.exp (C * m)) = 2 * Real.exp (δ * N + C * m) := by
      rw [Real.exp_add]; ring
    rwa [e] at key
  · obtain ⟨hp1, hp2⟩ := GlobalTheory.T.hermPair_pow_section_mem_and_norm_pow k X p P 0 1 s hs m
    have hm := (GlobalTheory.T.hermLineBundlePair_sections_mul_mem_norm_mul k X p P N 0 _ _ f (s ^ m) hf hp1).2 σ y
    rw [hp2 σ y] at hm
    simp only [mul_zero, add_zero, mul_one, zero_add] at hm
    have h2 := hfs.2 σ y
    rw [hm] at h2
    have hn : 0 ≤ P.nu N 0 σ y f := by unfold Pair.nu; positivity
    have h1 : 1 ≤ Real.exp C * P.nu 0 1 σ y s := by
      have : Real.exp (-Real.log ρ) ≤ Real.exp C := Real.exp_le_exp.2 (le_max_right _ _)
      rw [Real.exp_neg, Real.exp_log hρ] at this
      calc (1 : ℝ) = ρ⁻¹ * ρ := (inv_mul_cancel₀ hρ.ne').symm
        _ ≤ Real.exp C * P.nu 0 1 σ y s :=
          mul_le_mul this hy hρ.le (Real.exp_pos _).le
    have h3 : 1 ≤ Real.exp (C * m) * P.nu 0 1 σ y s ^ m := by
      rw [mul_comm C, Real.exp_nat_mul, ← mul_pow]
      exact one_le_pow₀ h1
    calc P.nu N 0 σ y f ≤ P.nu N 0 σ y f * (Real.exp (C * m) * P.nu 0 1 σ y s ^ m) :=
          le_mul_of_one_le_right hn h3
      _ = Real.exp (C * m) * (P.nu N 0 σ y f * P.nu 0 1 σ y s ^ m) := by ring
      _ ≤ Real.exp (C * m) * 2 := mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
      _ = 2 * Real.exp (C * m) := mul_comm _ _

end GlobalTheory.VolBr.MpDiv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSmallSectionBallOfMulPowSectionStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_smallSectionBall_of_mul_pow_section : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ s : X.functionField, s ∈ P.H 0 1 → s ≠ 0 → ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧ ∀ (N m : ℕ) (f : X.functionField), f ∈ P.H N 0 → f * s ^ m ∈ P.Bl N m 2 → f ∈ P.Bl N 0 (2 * Real.exp (δ * N + C * m)) := by
  first | exact @GlobalTheory.VolBr.MpDiv.mem_Bl_of_mul_pow | exact GlobalTheory.VolBr.MpDiv.mem_Bl_of_mul_pow | (intros; apply GlobalTheory.VolBr.MpDiv.mem_Bl_of_mul_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithSmallSectionsEncardMulLeFiniteLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivPowMemSectionsOfMulPowMem
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivPowMemSectionsOfMulPowMem
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem Pair.div_pow_mem_H_of_mul_pow : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (P : Pair p), ∀ (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ (N m : ℕ)
    (u : X.functionField), u ∈ P.H N m → u * t ^ N / s ^ m ∈ P.H 0 (b * N) → u / s ^ m ∈ P.H N 0 := by
  intro k _ X _ p D _ P b s t hG N m u hu hut x i j hi hj
  let O : Subring X.functionField := (algebraMap (X.presheaf.stalk x) X.functionField).range
  have hO : ∀ f, RegAt x f ↔ f ∈ O := fun f => Iff.rfl
  have hri : (P.r i : X.functionField) ≠ 0 := (P.r i).ne_zero
  have hrj : (P.r' j : X.functionField) ≠ 0 := (P.r' j).ne_zero
  have hs : P.loc 0 1 s i j ∈ O := (hO _).1 (hG.s_mem.1 x i j hi hj)
  have ht : P.loc (-1) b t i j ∈ O := (hO _).1 (hG.t_mem.1 x i j hi hj)
  have hs0 : P.loc 0 1 s i j ≠ 0 := by
    simp only [loc, zpow_zero, zpow_one, mul_one]
    exact mul_ne_zero hG.s_ne hrj
  have hreg : ∀ g ∈ O, g * P.loc (-1) b t i j / P.loc 0 1 s i j ∈ O → g / P.loc 0 1 s i j ∈ O :=
    fun g hg h => (hO _).1 (hG.reg x i j hi hj g ((hO _).2 hg) ((hO _).2 h))
  have hg : P.loc N m u i j ∈ O := (hO _).1 (hu x i j hi hj)
  have e1 : P.loc N m u i j * P.loc (-1) b t i j ^ N / P.loc 0 1 s i j ^ m =
      P.loc 0 ((b * N : ℕ) : ℤ) (u * t ^ N / s ^ m) i j := by
    simp only [loc, zpow_zero, zpow_one, mul_one, zpow_natCast, zpow_neg, mul_pow, inv_pow]
    push_cast
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast]
    simp only [zpow_natCast]
    field_simp
    ring
  have e2 : P.loc N m u i j / P.loc 0 1 s i j ^ m = P.loc N 0 (u / s ^ m) i j := by
    simp only [loc, zpow_zero, zpow_one, mul_one, zpow_natCast, mul_pow]
    field_simp
  have hgN : P.loc N m u i j * P.loc (-1) b t i j ^ N / P.loc 0 1 s i j ^ m ∈ O := by
    rw [e1]
    have := hut x i j hi hj
    push_cast at this ⊢
    exact (hO _).1 this
  have := regularPair_pow X.functionField O _ _ hs ht hs0 hreg m N _ hg hgN
  rw [e2] at this
  exact (hO _).2 (by exact_mod_cast this)

end GlobalTheory.VolBr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivPowMemSectionsOfMulPowMemStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.div_pow_mem_sections_of_mul_pow_mem : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ (N m : ℕ) (u : X.functionField), u ∈ P.H N m → u * t ^ N / s ^ m ∈ P.H 0 (b * N) → u / s ^ m ∈ P.H N 0 := by
  first | exact @GlobalTheory.VolBr.Pair.div_pow_mem_H_of_mul_pow | exact GlobalTheory.VolBr.Pair.div_pow_mem_H_of_mul_pow | (intros; apply GlobalTheory.VolBr.Pair.div_pow_mem_H_of_mul_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithSmallSectionsEncardMulLeFiniteLevel
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

namespace GlobalTheory.VolBr

theorem encard_mul_le_at_level : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (P : Pair p), ∀ (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ (N m : ℕ),
    (P.Bl N m 1).Finite → (P.Bl N m 1).encard * (P.Bl 0 (b * N) 1).encard ≤
      {f | f ∈ P.H N 0 ∧ f * s ^ m ∈ P.Bl N m 2}.encard * (P.Bl 0 (b * N + m) 2).encard := by
  intro k _ X _ p D hX P b s t hg N m hfin

  have hnu : ∀ (a c : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField), 0 ≤ P.nu a c σ y f := by
    intro a c σ y f
    unfold Pair.nu
    positivity
  have hs0 : s ^ m ≠ 0 := pow_ne_zero _ hg.s_ne

  obtain ⟨hsH, hsnu⟩ := GlobalTheory.T.hermPair_pow_section_mem_and_norm_pow k X p P 0 1 s hg.s_mem.1 m
  obtain ⟨htH, htnu⟩ := GlobalTheory.T.hermPair_pow_section_mem_and_norm_pow k X p P (-1) b t hg.t_mem.1 N
  have hsle : ∀ (σ : k →+* ℂ) (y : CxPts p σ), P.nu (↑m * 0) (↑m * 1) σ y (s ^ m) ≤ 1 := by
    intro σ y
    rw [hsnu]
    exact pow_le_one₀ (hnu _ _ _ _ _) (hg.s_mem.2 σ y)
  have htle : ∀ (σ : k →+* ℂ) (y : CxPts p σ), P.nu (↑N * (-1)) (↑N * ↑b) σ y (t ^ N) ≤ 1 := by
    intro σ y
    rw [htnu]
    exact pow_le_one₀ (hnu _ _ _ _ _) (hg.t_mem.2 σ y)

  let Λ₀ : AddSubgroup X.functionField := (P.H N 0).comap (AddMonoidHom.mulRight (s ^ m)⁻¹)
  let Λ₀' : AddSubgroup X.functionField := (P.H 0 (b * N)).comap (AddMonoidHom.mulRight (s ^ m)⁻¹)
  have key := GlobalTheory.VolBr.encard_mul_le_of_quot_embed X.functionField (P.H N m) (P.H 0 (b * N + m)) Λ₀ Λ₀'
    (P.Bl N m) (P.Bl 0 (b * N + m)) (AddMonoidHom.mulRight (t ^ N))
    (GlobalTheory.T.isSeminormBallFamily_sectionBalls k X p P N m) (GlobalTheory.T.isSeminormBallFamily_sectionBalls k X p P 0 (b * N + m)) ?_ ?_ hfin
  rotate_left
  ·
    intro u hu
    obtain ⟨hH, hn⟩ := GlobalTheory.T.hermLineBundlePair_sections_mul_mem_norm_mul k X p P N m (↑N * (-1)) (↑N * ↑b) u (t ^ N) hu.1 htH
    have e1 : (N : ℤ) + ↑N * (-1) = 0 := by ring
    have e2 : (m : ℤ) + ↑N * ↑b = ↑b * ↑N + ↑m := by ring
    rw [e1, e2] at hH hn
    refine ⟨hH, fun σ y => ?_⟩
    simp only [AddMonoidHom.coe_mulRight]
    rw [hn]
    exact mul_le_one₀ (hu.2 σ y) (hnu _ _ _ _ _) (htle σ y)
  ·
    intro u hu hT
    simp only [Λ₀, Λ₀', AddSubgroup.mem_comap, AddMonoidHom.coe_mulRight] at hT ⊢
    rw [← div_eq_mul_inv] at hT ⊢
    exact GlobalTheory.T.div_pow_mem_sections_of_mul_pow_mem k X p D hX P b s t hg N m u hu hT

  have hE : (P.Bl 0 (b * N) 1).encard ≤ (P.Bl 0 (b * N + m) 1 ∩ (Λ₀' : Set X.functionField)).encard := by
    rw [← (mul_left_injective₀ hs0).injOn.encard_image]
    apply Set.encard_le_encard
    rintro _ ⟨g, hg', rfl⟩
    obtain ⟨hH, hn⟩ := GlobalTheory.T.hermLineBundlePair_sections_mul_mem_norm_mul k X p P 0 (↑b * ↑N) (↑m * 0) (↑m * 1) g (s ^ m) hg'.1 hsH
    have e1 : (0 : ℤ) + ↑m * 0 = 0 := by ring
    have e2 : (↑b * ↑N : ℤ) + ↑m * 1 = ↑b * ↑N + ↑m := by ring
    rw [e1, e2] at hH hn
    refine ⟨⟨hH, fun σ y => ?_⟩, ?_⟩
    · rw [hn]
      exact mul_le_one₀ (hg'.2 σ y) (hnu _ _ _ _ _) (hsle σ y)
    · show g * s ^ m * (s ^ m)⁻¹ ∈ P.H 0 (↑b * ↑N)
      rw [mul_inv_cancel_right₀ hs0]
      exact hg'.1

  have hB : (P.Bl N m 2 ∩ (Λ₀ : Set X.functionField)) =
      (fun f => f * s ^ m) '' {f | f ∈ P.H N 0 ∧ f * s ^ m ∈ P.Bl N m 2} := by
    ext u
    constructor
    · rintro ⟨hu, hu0⟩
      refine ⟨u * (s ^ m)⁻¹, ⟨hu0, ?_⟩, ?_⟩
      · rw [inv_mul_cancel_right₀ hs0]
        exact hu
      · exact inv_mul_cancel_right₀ hs0 u
    · rintro ⟨f, ⟨hf, hfs⟩, rfl⟩
      refine ⟨hfs, ?_⟩
      show f * s ^ m * (s ^ m)⁻¹ ∈ P.H N 0
      rw [mul_inv_cancel_right₀ hs0]
      exact hf
  rw [hB, (mul_left_injective₀ hs0).injOn.encard_image] at key
  refine le_trans ?_ key
  gcongr

end GlobalTheory.VolBr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithSmallSectionsEncardMulLeFiniteLevelStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_small_sections_encard_mul_le_finite_level : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ (N m : ℕ), (P.Bl N m 1).Finite → (P.Bl N m 1).encard * (P.Bl 0 (b * N) 1).encard ≤ {f | f ∈ P.H N 0 ∧ f * s ^ m ∈ P.Bl N m 2}.encard * (P.Bl 0 (b * N + m) 2).encard := by
  first | exact @GlobalTheory.VolBr.encard_mul_le_at_level | exact GlobalTheory.VolBr.encard_mul_le_at_level | (intros; apply GlobalTheory.VolBr.encard_mul_le_at_level <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionCountContinuousFromAbove
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem log_add_le_of_mul_le (a b c d e : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (h : a * b ≤ c * d) (hce : c ≤ e) :
    Real.log a + Real.log b ≤ Real.log e + Real.log d := by
  have hab : 1 ≤ a * b := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hcd : 1 ≤ c * d := hab.trans h
  have hc : c ≠ 0 := by rintro rfl; simp at hcd
  have hd : d ≠ 0 := by rintro rfl; simp at hcd
  have he : e ≠ 0 := by omega
  have h1 : Real.log ((a : ℝ) * b) ≤ Real.log ((e : ℝ) * d) := by
    apply Real.log_le_log
    · have : (1 : ℝ) ≤ (a : ℝ) * b := by exact_mod_cast hab
      linarith
    · have : a * b ≤ e * d := h.trans (Nat.mul_le_mul_right d hce)
      exact_mod_cast this
  rwa [Real.log_mul (by exact_mod_cast (by omega : a ≠ 0)) (by exact_mod_cast (by omega : b ≠ 0)),
    Real.log_mul (by exact_mod_cast he) (by exact_mod_cast hd)] at h1

theorem lc_add_A_le : GlobalTheory.Published.ArithHilbertSamuel → GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0})
    [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (b : ℕ) (s t : X.functionField),
    P.Good D b s t → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ᶠ m : ℕ in atTop,
    P.lc (n * m : ℕ) m 1 ≤ P.lc (n * m : ℕ) 0 1 + ε * ((n : ℝ) * m) ^ (D + 1) := by
  intro hHS hAC k _ X _ p D hD P b s t hG ε hε
  have hfin : ∀ (a c : ℤ) (R : ℝ), (P.Bl a c R).Finite := fun a c R =>
    GlobalTheory.T.hermLineBundlePair_balls_finite hHS k X p D hD P b s t hG a c R hAC
  have hball : ∀ a c : ℤ, IsBallFam (P.H a c) (P.Bl a c) := GlobalTheory.T.isSeminormBallFamily_sectionBalls k X p P
  have hpos : ∀ (a c : ℤ) (R : ℝ), 0 ≤ R → 1 ≤ (P.Bl a c R).ncard := fun a c R hR =>
    Nat.one_le_iff_ne_zero.mpr ((Set.ncard_pos (hfin a c R)).mpr ⟨0, (hball a c).zero_mem R hR⟩).ne'
  obtain ⟨C0, hC0⟩ := GlobalTheory.T.smallSectionCount_le_pow_goodPair hHS hAC k X p D hD P b s t hG
  obtain ⟨δ, hδ, hrad⟩ := GlobalTheory.T.exists_log_ncard_seminormBall_exp_small_le X.functionField (fun N => P.H (N : ℤ) 0) (fun N => P.Bl (N : ℤ) 0) (D + 1)
    (Nat.succ_pos D) (fun N => hball N 0) (fun N R => hfin N 0 R) C0 hC0 (ε / 3) (by positivity)
  obtain ⟨C, hC, hdiv⟩ := GlobalTheory.T.mem_smallSectionBall_of_mul_pow_section k X p D hD P s hG.s_mem.1 hG.s_ne (δ / 2) (by positivity)
  have hdA := GlobalTheory.T.smallSectionCount_nearPowers_le hHS hAC k X p D hD P b s t hG (ε / 3) (by positivity)
  have hn : ∀ᶠ n : ℕ in atTop, (2 * C + 2) / δ ≤ (n : ℝ) ∧ 1 ≤ n :=
    (tendsto_natCast_atTop_atTop.eventually_ge_atTop _).and (eventually_ge_atTop 1)
  filter_upwards [hdA, hn] with n hdAn hnn
  obtain ⟨hnC, hn1⟩ := hnn
  have htend : Tendsto (fun m : ℕ => n * m) atTop atTop :=
    tendsto_atTop_mono (fun m => Nat.le_mul_of_pos_left m hn1) tendsto_id
  filter_upwards [hdAn, htend.eventually hrad, eventually_ge_atTop 1] with m hdm hradm hm1
  have hnδ : 2 * C + 2 ≤ (n : ℝ) * δ := (div_le_iff₀ hδ).mp hnC
  have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast hm1

  have hrad_le : 2 * Real.exp (δ / 2 * ((n * m : ℕ) : ℝ) + C * m) ≤ Real.exp (δ * ((n * m : ℕ) : ℝ)) := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp 1; linarith
    calc 2 * Real.exp (δ / 2 * ((n * m : ℕ) : ℝ) + C * m)
        ≤ Real.exp 1 * Real.exp (δ / 2 * ((n * m : ℕ) : ℝ) + C * m) :=
          mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
      _ = Real.exp (1 + (δ / 2 * ((n * m : ℕ) : ℝ) + C * m)) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (δ * ((n * m : ℕ) : ℝ)) := by
          apply Real.exp_le_exp.mpr
          push_cast
          nlinarith [mul_le_mul_of_nonneg_right hnδ (by linarith : (0 : ℝ) ≤ m)]
  have hSsub : {f | f ∈ P.H (n * m : ℕ) 0 ∧ f * s ^ m ∈ P.Bl (n * m : ℕ) m 2} ⊆
      P.Bl (n * m : ℕ) 0 (Real.exp (δ * ((n * m : ℕ) : ℝ))) := by
    rintro f ⟨hf1, hf2⟩
    have hf := hdiv (n * m) m f hf1 hf2
    exact ⟨hf.1, fun σ y => (hf.2 σ y).trans hrad_le⟩
  have hEfin := hfin (n * m : ℕ) 0 (Real.exp (δ * ((n * m : ℕ) : ℝ)))
  have hSfin := hEfin.subset hSsub
  have hlev := GlobalTheory.T.arith_small_sections_encard_mul_le_finite_level k X p D hD P b s t hG (n * m) m (hfin _ _ _)
  rw [← (hfin _ _ _).cast_ncard_eq, ← (hfin _ _ _).cast_ncard_eq, ← hSfin.cast_ncard_eq,
    ← (hfin _ _ _).cast_ncard_eq] at hlev
  norm_cast at hlev
  have hkey := log_add_le_of_mul_le _ _ _ _ _ (hpos _ _ _ zero_le_one) (hpos _ _ _ zero_le_one) hlev
    (Set.ncard_le_ncard hSsub hEfin)
  have hX : (0 : ℝ) ≤ ((n : ℝ) * m) ^ (D + 1) := by positivity
  have hX3 := mul_nonneg (by positivity : (0 : ℝ) ≤ ε / 3) hX
  simp only [Pair.lc] at hdm ⊢
  push_cast at hradm hkey hdm ⊢
  linarith

end GlobalTheory.VolBr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionCountContinuousFromAboveStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.small_section_count_continuous_from_above : GlobalTheory.Published.ArithHilbertSamuel → GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ᶠ m : ℕ in atTop, P.lc (n * m : ℕ) m 1 ≤ P.lc (n * m : ℕ) 0 1 + ε * ((n : ℝ) * m) ^ (D + 1) := by
  first | exact @GlobalTheory.VolBr.lc_add_A_le | exact GlobalTheory.VolBr.lc_add_A_le | (intros; apply GlobalTheory.VolBr.lc_add_A_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCardSmallSectionsGeOfShiftNef
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCardSmallSectionsGeOfShiftNef
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem log_ncard_ball_one_ge_of_shift_nef : GlobalTheory.Published.ArithHilbertSamuel → GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ (a c : ℤ) (M : HermLB p) (α t₀ : ℝ), P.Rep a c M → M.IsSelfInter α → (M.shift (fun _ => t₀) fun _ => rfl).IsNef D → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, (α / (D + 1).factorial - ε) * (m : ℝ) ^ (D + 1) ≤ P.lc (m * a) (m * c) 1 := by
  intro hHS hAC k _ X _ p D hX P b s t hG a c M α t₀ hRep hSI hNef ε hε
  exact GlobalTheory.T.eventually_log_ncard_seminormBall_one_ge X.functionField (fun m : ℕ => P.H (m * a) (m * c)) (fun m : ℕ => P.Bl (m * a) (m * c))
    (D + 1) (Nat.succ_pos D) (fun m => GlobalTheory.T.isSeminormBallFamily_sectionBalls k X p P _ _)
    (fun m R => GlobalTheory.T.hermLineBundlePair_balls_finite hHS k X p D hX P b s t hG _ _ R hAC)
    (α / (D + 1).factorial) ((D + 1) * gdeg M D / (D + 1).factorial) t₀
    (fun t ht => GlobalTheory.T.arith_hilbertSamuel_log_ball_count_tendsto hHS hAC k X p D hX P a c M α t₀ hRep hSI hNef t ht) ε hε

end GlobalTheory.VolBr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCardSmallSectionsGeOfShiftNefStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_card_smallSections_ge_of_shift_nef : GlobalTheory.Published.ArithHilbertSamuel → GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ (a c : ℤ) (M : HermLB p) (α t₀ : ℝ), P.Rep a c M → M.IsSelfInter α → (M.shift (fun _ => t₀) fun _ => rfl).IsNef D → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, (α / (D + 1).factorial - ε) * (m : ℝ) ^ (D + 1) ≤ P.lc (m * a) (m * c) 1 := by
  first | exact @GlobalTheory.VolBr.log_ncard_ball_one_ge_of_shift_nef | exact GlobalTheory.VolBr.log_ncard_ball_one_ge_of_shift_nef | (intros; apply GlobalTheory.VolBr.log_ncard_ball_one_ge_of_shift_nef <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeArithVolumeOfFrequentlySmallSectionsLower
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeArithVolumeOfFrequentlySmallSectionsLower
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VolBr

theorem le_arVol_of_frequently_le : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (L : HermLB p) (a : ℝ), (∀ ε : ℝ, 0 < ε → ∃ᶠ N : ℕ in atTop, (L.pow N).smallSec.Finite ∧ (a / (D + 1).factorial - ε) * (N : ℝ) ^ (D + 1) ≤ Real.log ((L.pow N).smallSec.ncard : ℝ)) → (a : EReal) ≤ arVol L D := by
  intro k _ X _ p D L a h
  have hc : (0 : ℝ) < ((D + 1).factorial : ℝ) := by positivity
  have key : ∀ δ : ℝ, 0 < δ → ((a - δ : ℝ) : EReal) ≤ arVol L D := by
    intro δ hδ
    refine Filter.le_limsup_of_frequently_le ?_
    have hε : 0 < δ / ((D + 1).factorial : ℝ) := div_pos hδ hc
    refine ((h _ hε).and_eventually (eventually_gt_atTop 0)).mono ?_
    rintro N ⟨⟨hfin, hle⟩, hN⟩
    have h0 : 0 < (L.pow N).smallSec.ncard := (Set.ncard_pos hfin).2 ⟨_, (L.pow N).zero_mem_smallSec⟩
    rw [← hfin.cast_ncard_eq, ENat.toENNReal_coe, ← ENNReal.ofReal_natCast,
      ENNReal.log_ofReal_of_pos (by exact_mod_cast h0), ← EReal.coe_mul, EReal.coe_le_coe_iff]
    have hNp : (0 : ℝ) < (N : ℝ) ^ (D + 1) := by positivity
    rw [mul_div_assoc', le_div_iff₀ hNp]
    have e : (a / ((D + 1).factorial : ℝ) - δ / ((D + 1).factorial : ℝ)) * ((D + 1).factorial : ℝ) = a - δ := by
      field_simp
    calc (a - δ) * (N : ℝ) ^ (D + 1)
        = ((a / ((D + 1).factorial : ℝ) - δ / ((D + 1).factorial : ℝ)) * (N : ℝ) ^ (D + 1)) * ((D + 1).factorial : ℝ) := by
          rw [← e]; ring
      _ ≤ Real.log ((L.pow N).smallSec.ncard : ℝ) * ((D + 1).factorial : ℝ) :=
          mul_le_mul_of_nonneg_right hle hc.le
  refine le_of_forall_lt_imp_le_of_dense fun z hz => ?_
  induction z using EReal.rec with
  | bot => exact bot_le
  | top => exact absurd hz (not_lt.2 le_top)
  | coe r =>
    have hr : r < a := EReal.coe_lt_coe_iff.1 hz
    have := key (a - r) (by linarith)
    rwa [sub_sub_cancel] at this

end GlobalTheory.VolBr
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeArithVolumeOfFrequentlySmallSectionsLowerStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.le_arithVolume_of_frequently_smallSections_lower : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (L : HermLB p) (a : ℝ), (∀ ε : ℝ, 0 < ε → ∃ᶠ N : ℕ in atTop, (L.pow N).smallSec.Finite ∧ (a / (D + 1).factorial - ε) * (N : ℝ) ^ (D + 1) ≤ Real.log ((L.pow N).smallSec.ncard : ℝ)) → (a : EReal) ≤ arVol L D := by
  first | exact @GlobalTheory.VolBr.le_arVol_of_frequently_le | exact GlobalTheory.VolBr.le_arVol_of_frequently_le | (intros; apply GlobalTheory.VolBr.le_arVol_of_frequently_le <;> assumption)
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

noncomputable section

namespace GlobalTheory.VolBr

theorem volGe_of_hilbertSamuel :
    GlobalTheory.Published.ArithHilbertSamuel → GlobalTheory.Published.ArCalc → GlobalTheory.Published.NefNumerics → GlobalTheory.Published.VolGe := by
  intro hHS hAC hNN k _ X _ p D hX L a hNF hSP hSI
  obtain ⟨P, b, s, t, hPL, hG⟩ := GlobalTheory.T.exists_good_hermitian_lineBundle_pair hAC k X p D hX L
  subst hPL
  obtain ⟨α, hα, hαlim⟩ := GlobalTheory.T.tendsto_selfIntersection_pow_tensor_div_pow hAC k X p D hX P.L P.A a hSI
  obtain ⟨hRL, hRA, -⟩ := GlobalTheory.T.represents_base_bundles_and_trivial k X p P
  apply GlobalTheory.T.le_arithVolume_of_frequently_smallSections_lower k X p D P.L a
  intro ε hε
  have hF1 : (1 : ℝ) ≤ ((D + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hε3 : 0 < ε / 3 := by positivity
  have hlim : ∀ᶠ n : ℕ in atTop, a - ε / 3 < α n / (n : ℝ) ^ (D + 1) :=
    hαlim.eventually (lt_mem_nhds (by linarith))
  obtain ⟨n, hn1, hnα, hcont⟩ := ((eventually_ge_atTop 1).and
    (hlim.and (GlobalTheory.T.small_section_count_continuous_from_above hHS hAC k X p D hX P b s t hG (ε / 3) hε3))).exists
  have hRn : P.Rep (n : ℤ) 1 ((P.L.pow n).tens P.A) := by
    have h1 := GlobalTheory.T.represents_hermitianLineBundle_pow k X p P 1 0 P.L n hRL
    have h2 := GlobalTheory.T.hermPairWithSections_represents_tensor k X p P _ _ 0 1 _ P.A h1 hRA
    simpa using h2
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.T.exists_metricShift_isNef_pow_tens_ample hAC hNN k X p D hX P.L P.A n hSP hNF hG.ample hG.nef
  have hstep := GlobalTheory.T.log_card_smallSections_ge_of_shift_nef hHS hAC k X p D hX P b s t hG n 1 _ (α n) t₀ hRn (hα n) ht₀ (ε / 3) hε3
  rw [Filter.frequently_atTop]
  intro N₀
  obtain ⟨m, hm, hm1, hm2⟩ := ((eventually_ge_atTop (max N₀ 1)).and (hstep.and hcont)).exists
  have hmN : N₀ ≤ m := le_of_max_le_left hm
  refine ⟨n * m, le_trans hmN (Nat.le_mul_of_pos_left m hn1), ?_⟩
  have hsm := (GlobalTheory.T.smallSections_twistedPower_encard_eq_ball k X p P 1 0 P.L hRL 0 (n * m)).2.1
  rw [mul_one, mul_zero] at hsm
  have hfin := GlobalTheory.T.hermLineBundlePair_balls_finite hHS k X p D hX P b s t hG ((n * m : ℕ) : ℤ) 0 1 hAC
  have hnc : (P.L.pow (n * m)).smallSec.ncard = (P.Bl ((n * m : ℕ) : ℤ) 0 1).ncard := by
    rw [Set.ncard_def, Set.ncard_def, hsm]
  refine ⟨Set.encard_lt_top_iff.mp (hsm ▸ Set.encard_lt_top_iff.mpr hfin), ?_⟩
  rw [hnc]
  change _ ≤ P.lc ((n * m : ℕ) : ℤ) 0 1
  have hcast : (m : ℤ) * (n : ℤ) = ((n * m : ℕ) : ℤ) := by push_cast; ring
  rw [hcast, mul_one] at hm1
  set F : ℝ := ((D + 1).factorial : ℝ)
  set x : ℝ := (n : ℝ) ^ (D + 1) with hx
  set y : ℝ := (m : ℝ) ^ (D + 1) with hy
  have hx1 : 1 ≤ x := one_le_pow₀ (by exact_mod_cast hn1)
  have hy0 : 0 ≤ y := by positivity
  have hN : ((n * m : ℕ) : ℝ) ^ (D + 1) = x * y := by push_cast; rw [mul_pow]
  rw [mul_pow] at hm2
  rw [hN]
  have hαx : (a - ε / 3) * x ≤ α n := by
    have := (lt_div_iff₀ (by linarith : (0 : ℝ) < x)).mp hnα
    linarith
  have hF0 : 0 < F := by linarith
  have e1 : (a - ε / 3) * x * y / F ≤ α n / F * y := by
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hαx hy0) hF0.le
  have e2 : ε / 3 * (x * y) / F ≤ ε / 3 * (x * y) :=
    div_le_self (by positivity) hF1
  have e3 : ε / 3 * y ≤ ε / 3 * (x * y) := by
    have : y ≤ x * y := le_mul_of_one_le_left hy0 hx1
    exact mul_le_mul_of_nonneg_left this hε3.le
  have e4 : (a / F - ε) * (x * y) = (a - ε / 3) * x * y / F + ε / 3 * (x * y) / F - ε * (x * y) := by
    field_simp
    ring
  linarith [e1, e2, e3, e4, hm1, hm2]

end GlobalTheory.VolBr
