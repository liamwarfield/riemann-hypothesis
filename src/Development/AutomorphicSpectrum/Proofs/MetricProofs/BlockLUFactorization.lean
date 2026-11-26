module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogPeriodStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.OmHeightslockG
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncModelEmbeddedLogResolution

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockLUFactorization
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockLUFactorization
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.LU

variable {N j : ℕ}

theorem mem_stepCols_stepOf (hj : j ≤ N) (a b : Fin N) :
    a ∈ stepCols N j (stepOf N j b) ↔ a ≤ b ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j) := by
  have ha := a.2
  have hb := b.2
  rw [Fin.le_def, stepCols, Finset.mem_filter]
  have hv : ((stepOf N j b : Fin N) : ℕ) = if N - j ≤ (b : ℕ) then (b : ℕ) - (N - j) else (b : ℕ) + j := rfl
  generalize ((stepOf N j b : Fin N) : ℕ) = i at hv ⊢
  simp only [Finset.mem_univ, true_and]
  split_ifs at hv ⊢ <;> omega

theorem det_subtype_eq_minorIJ (G : Matrix (Fin N) (Fin N) ℂ) (C : Finset (Fin N)) (P : Fin N → Prop)
    [Fintype {a // P a}] [DecidableEq {a // P a}] (hP : ∀ a, a ∈ C ↔ P a) :
    (G.submatrix (Subtype.val : {a // P a} → Fin N) Subtype.val).det = minorIJ G C C := by
  let e : Fin C.card ≃ {a // P a} := (C.orderIsoOfFin rfl).toEquiv.trans (Equiv.subtypeEquivRight hP)
  rw [minorIJ, dite_eq_left rfl, ← Matrix.det_submatrix_equiv_self e
    (G.submatrix (Subtype.val : {a // P a} → Fin N) Subtype.val)]
  rfl

theorem minor_stepOf_ne_zero (hj : j ≤ N) {G : Matrix (Fin N) (Fin N) ℂ} (hG : IsBlockDiag j G) (hd : G.det ≠ 0)
    (hs : ∀ i : Fin N, IsProperStep N j i → minorIJ G (stepCols N j i) (stepCols N j i) ≠ 0) (b : Fin N) :
    minorIJ G (stepCols N j (stepOf N j b)) (stepCols N j (stepOf N j b)) ≠ 0 := by
  by_cases hp : IsProperStep N j (stepOf N j b)
  · exact hs _ hp
  have hb := b.2
  have hlast : (b : ℕ) + 1 = N ∨ (b : ℕ) + 1 = N - j := by
    simp only [IsProperStep, stepOf, not_and_or, not_not] at hp
    split_ifs at hp <;> omega
  have hD := GlobalTheory.CompanionTheory.Ar.PB.CPts.detFac_ne_zero hj (⟨N - 1, by omega⟩ : Fin N) hG hd
  rw [detFac, if_pos (by simp only; omega), if_pos (by simp only; omega)] at hD
  by_cases h : N - j ≤ (b : ℕ)
  · have e : stepCols N j (stepOf N j b) = wIdx N j := by
      ext a
      have ha := a.2
      rw [mem_stepCols_stepOf hj, Fin.le_def]
      simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    rw [e]
    exact left_ne_zero_of_mul hD
  · have e : stepCols N j (stepOf N j b) = omIdx N j := by
      ext a
      have ha := a.2
      rw [mem_stepCols_stepOf hj, Fin.le_def]
      simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    rw [e]
    exact right_ne_zero_of_mul hD

theorem exists_lower_upper : ∀ (N j : ℕ) (G : Matrix (Fin N) (Fin N) ℂ), j ≤ N → IsBlockDiag j G → G.det ≠ 0 →
    (∀ i : Fin N, IsProperStep N j i → minorIJ G (stepCols N j i) (stepCols N j i) ≠ 0) →
    ∃ L U : Matrix (Fin N) (Fin N) ℂ, IsBlockDiag j L ∧ IsLowerUni L ∧ IsBlockDiag j U ∧ U.BlockTriangular id ∧
      (∀ c, U c c ≠ 0) ∧ G = L * U := by
  intro N j G hj hG hd hs
  have hu : ∀ b : Fin N, IsUnit (G.submatrix
      (Subtype.val : {a : Fin N // a ≤ b ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)} → Fin N) Subtype.val).det := fun b => by
    rw [det_subtype_eq_minorIJ G (stepCols N j (stepOf N j b)) _ fun a => mem_stepCols_stepOf hj a b]
    exact (minor_stepOf_ne_zero hj hG hd hs b).isUnit
  obtain ⟨B, hB, hBt, hL⟩ := hG.exists_upper hu
  have hdB : B.det ≠ 0 := fun h => by
    have := hL.det
    rw [Matrix.det_mul, h, mul_zero] at this
    exact zero_ne_one this
  have huB : IsUnit B.det := hdB.isUnit
  letI := Matrix.invertibleOfIsUnitDet B huB
  refine ⟨G * B, B⁻¹, hG.mul hB, hL, hB.inv huB, blockTriangular_inv_of_blockTriangular hBt, fun c => ?_, ?_⟩
  · have h1 : (B⁻¹).det ≠ 0 := (Matrix.isUnit_nonsing_inv_det B huB).ne_zero
    rw [Matrix.det_of_upperTriangular (blockTriangular_inv_of_blockTriangular hBt)] at h1
    exact (Finset.prod_ne_zero_iff.1 h1) c (Finset.mem_univ c)
  · rw [Matrix.mul_nonsing_inv_cancel_right _ _ huB]

end GlobalTheory.CompanionTheory.Ar.PB.WMan.LU
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockLUFactorizationStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_LU_factorization : ∀ (N j : ℕ) (G : Matrix (Fin N) (Fin N) ℂ), j ≤ N → IsBlockDiag j G → G.det ≠ 0 → (∀ i : Fin N, IsProperStep N j i → minorIJ G (stepCols N j i) (stepCols N j i) ≠ 0) → ∃ L U : Matrix (Fin N) (Fin N) ℂ, IsBlockDiag j L ∧ IsLowerUni L ∧ IsBlockDiag j U ∧ U.BlockTriangular id ∧ (∀ c, U c c ≠ 0) ∧ G = L * U := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.LU.exists_lower_upper | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.LU.exists_lower_upper | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.LU.exists_lower_upper <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsArithVarOfSncModel
section -- merged from Development.WeilBound.CoreStatements.PluriharmonicCharts.XCBmExistsArith
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

namespace PositivityTheory.Xgp.c_bm_exists_arith

open KaehlerDifferential

open Algebra in
theorem trdeg_int_eq_rat (L : Type) [Field L] [Algebra ℚ L] : Algebra.trdeg ℤ L = Algebra.trdeg ℚ L := by
  have : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic _ (nonZeroDivisors ℤ)
  have : FaithfulSMul ℤ ℚ := (faithfulSMul_iff_algebraMap_injective ℤ ℚ).mpr Int.cast_injective
  have : FaithfulSMul ℚ L := (faithfulSMul_iff_algebraMap_injective ℚ L).mpr (algebraMap ℚ L).injective
  rw [← trdeg_add_eq ℤ ℚ (A := L), trdeg_eq_zero, zero_add]

end PositivityTheory.Xgp.c_bm_exists_arith

theorem PositivityTheory.Xgp.t_c_bm_exists_arith : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (x : (Σ k, J k) → Ω) (n : ℕ) (bd : Ideal (MRing J)), 1 ≤ n → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, x ⟨k, c' k⟩) → Cmp.IsSncModel x n bd → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal x) (n + 1) := by
  intro X Ω _ _ ξ K _ J _ x n bd hn T hs
  classical

  obtain ⟨c, hc⟩ := T.cover ⟨genPt ξ, specializes_rfl⟩
  have hc0 : ∀ k, x ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hc.1 k (Finset.mem_univ k)
  obtain ⟨m, f, a, hf, ha, hsum, hmain⟩ := hs c hc0
  obtain ⟨l, hl⟩ : ∃ l, f l ≠ 0 := by
    by_contra h
    push_neg at h
    simp [h] at hsum
  set R : Set Ω := Set.range fun p : Σ k, J k => x p / x ⟨p.1, c p.1⟩ with hR
  set S : Subalgebra ℚ Ω := Algebra.adjoin ℚ (insert (f l)⁻¹ R) with hS
  obtain ⟨hsm, z, n', -, hli, hspan, -⟩ := hmain l hl S rfl

  have hRS : R ⊆ S := fun r hr => Algebra.subset_adjoin (Set.mem_insert_of_mem _ hr)
  have hmono : Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k =>
      (∏ k, x ⟨k, j k⟩) / ∏ k, x ⟨k, c k⟩) ≤ S.restrictScalars ℤ := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨j, rfl⟩
    show (∏ k, x ⟨k, j k⟩) / ∏ k, x ⟨k, c k⟩ ∈ S
    rw [← Finset.prod_div_distrib]
    exact Subalgebra.prod_mem _ fun k _ => hRS ⟨⟨k, j k⟩, rfl⟩
  have hfr : IsFractionRing S Ω := by
    refine IsFractionRing.of_field S Ω fun a => ?_
    obtain ⟨g, hg, h, hh, -, e⟩ := GlobalTheory.CompanionTheory.Ar.FlagBun.FracChart.exists_eq_div_adjoin X Ω ξ _ _ c T hc.1 a
    exact ⟨⟨g, hmono hg⟩, ⟨h, hmono hh⟩, e⟩
  have hfin : Module.finrank Ω (KaehlerDifferential ℚ Ω) = n :=
    GlobalTheory.CompanionTheory.Ggeo.finrank_kaehler_fractionRing_eq_of_basis ℚ S ℚ Ω n z hli hspan

  have hK : Nonempty K := by
    by_contra hK
    rw [not_nonempty_iff] at hK
    have hall : ∀ a : Ω, a ∈ Set.range (algebraMap ℚ Ω) := by
      intro a
      obtain ⟨g, hg, h, hh, -, e⟩ := GlobalTheory.CompanionTheory.Ar.FlagBun.FracChart.exists_eq_div_adjoin X Ω ξ _ _ c T hc.1 a
      have h1 : (Set.range fun j : (k : K) → J k => (∏ k, x ⟨k, j k⟩) / ∏ k, x ⟨k, c k⟩) ⊆ {1} := by
        rintro _ ⟨j, rfl⟩
        simp
      have hbot : ∀ b ∈ Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k =>
          (∏ k, x ⟨k, j k⟩) / ∏ k, x ⟨k, c k⟩), ∃ q : ℤ, b = q := by
        intro b hb
        have := Algebra.adjoin_mono h1 hb
        rw [Algebra.adjoin_singleton_one, Algebra.mem_bot] at this
        obtain ⟨q, rfl⟩ := this
        exact ⟨q, by simp⟩
      obtain ⟨q1, rfl⟩ := hbot g hg
      obtain ⟨q2, rfl⟩ := hbot h hh
      exact ⟨(q1 : ℚ) / q2, by rw [e]; simp⟩
    have hsub : Subsingleton (KaehlerDifferential ℚ Ω) := by
      have htop := KaehlerDifferential.span_range_derivation ℚ Ω
      refine subsingleton_of_forall_eq 0 fun w => ?_
      have hw : w ∈ (⊤ : Submodule Ω (KaehlerDifferential ℚ Ω)) := trivial
      rw [← htop] at hw
      have hle : Submodule.span Ω (Set.range (KaehlerDifferential.D ℚ Ω)) ≤ ⊥ := by
        rw [Submodule.span_le]
        rintro _ ⟨b, rfl⟩
        obtain ⟨q, rfl⟩ := hall b
        exact (KaehlerDifferential.D ℚ Ω).map_algebraMap q
      simpa using hle hw
    have := Module.finrank_zero_of_subsingleton (R := Ω) (M := KaehlerDifferential ℚ Ω)
    omega

  have : Algebra.EssFiniteType S Ω := .of_isLocalization Ω (nonZeroDivisors S)
  have : Algebra.EssFiniteType ℚ Ω := .comp ℚ S Ω
  have hfd : Module.Finite Ω (KaehlerDifferential ℚ Ω) := Module.finite_of_finrank_pos (by omega)
  have htr : Algebra.trdeg ℚ Ω = n := by
    rw [← GlobalTheory.rank_kaehler_eq_trdeg, ← Module.finrank_eq_rank, hfin]
  have htr' : Algebra.trdeg ℤ Ω = n := (PositivityTheory.Xgp.c_bm_exists_arith.trdeg_int_eq_rat Ω).trans htr
  exact (GlobalTheory.T.birational_of_transcendence_degree X Ω ξ K J x n T htr').2
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsArithVarOfSncModel
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.isArithVar_of_snc_model : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (x : (Σ k, J k) → Ω) (n : ℕ) (bd : Ideal (MRing J)), 1 ≤ n → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, x ⟨k, c' k⟩) → Cmp.IsSncModel x n bd → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal x) (n + 1) := by
  first | exact @PositivityTheory.Xgp.t_c_bm_exists_arith | exact PositivityTheory.Xgp.t_c_bm_exists_arith
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsArithVarOfSncModelStatement
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isArithVar_of_snc_model : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (x : (Σ k, J k) → Ω) (n : ℕ) (bd : Ideal (MRing J)), 1 ≤ n → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, x ⟨k, c' k⟩) → Cmp.IsSncModel x n bd → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal x) (n + 1) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.isArithVar_of_snc_model | exact GlobalTheory.CompanionTheory.Relay.isArithVar_of_snc_model | (intros; apply GlobalTheory.CompanionTheory.Relay.isArithVar_of_snc_model <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartEighth
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartEighth
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan

theorem continuousWithinAt_valAt_of_regAt {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type}
    [Field Ω] {x : (Σ k, ι k) → Ω} {zb : (Σ k, ι k) → ℂ} (hz : zb ∈ mcPts (mCoordIdeal x)) {s : Ω}
    (hs : RegAt x (mCoordIdeal zb) s) : ContinuousWithinAt (valAt x s) (mcPts (mCoordIdeal x)) zb := by
  obtain ⟨d, g, h, hg, hh, hn, heq⟩ := hs
  have hy := GlobalTheory.CompanionTheory.Ar.PB.ValRing.aeval_ne_zero_of_notMem hz hh hn
  have h0 := GlobalTheory.CompanionTheory.Ar.PB.ValRing.eval_ne_zero_of_notMem hh hn
  have cg : Continuous fun w : (Σ k, ι k) → ℂ => eval w (map (Int.castRingHom ℂ) g) :=
    MvPolynomial.continuous_eval _
  have ch : Continuous fun w : (Σ k, ι k) → ℂ => eval w (map (Int.castRingHom ℂ) h) :=
    MvPolynomial.continuous_eval _
  have hnear : valAt x s =ᶠ[𝓝[mcPts (mCoordIdeal x)] zb]
      fun w => eval w (map (Int.castRingHom ℂ) g) / eval w (map (Int.castRingHom ℂ) h) := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ch.continuousAt.eventually_ne h0)] with w hw hw0
    exact valAt_eq hw ⟨d, g, h, hg, hh, hy, heq, hw0, rfl⟩
  have hat : valAt x s zb = eval zb (map (Int.castRingHom ℂ) g) / eval zb (map (Int.castRingHom ℂ) h) :=
    valAt_eq hz ⟨d, g, h, hg, hh, hy, heq, h0, rfl⟩
  exact (cg.continuousAt.div ch.continuousAt h0).continuousWithinAt.congr_of_eventuallyEq hnear hat

section Flag

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem twMinor_continuousWithinAt (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) {Z : Type}
    [TopologicalSpace Z] {S : Set Z} {z₀ : Z} {β : Z → (Σ k, baseIdx ι M.blk k) → ℂ} {P : Z → (Σ k, ι k) → ℂ}
    (hβ : ContinuousWithinAt β S z₀) (hS : Set.MapsTo β S (mcPts (mCoordIdeal M.x)))
    (hz : β z₀ ∈ mcPts (mCoordIdeal M.x)) (hG : M.GoodAt F (mCoordIdeal (β z₀)))
    (hP : ContinuousWithinAt P S z₀) (i : Fin N) (k : K) (g : Matrix (Fin N) (Fin N) ℂ) (J : Finset (Fin N)) :
    ContinuousWithinAt (fun z => twMinor M F (β z) i k g (P z) J) S z₀ := by
  simp only [twMinor, pluck]
  refine tendsto_finsetSum _ fun I _ => Tendsto.const_mul _ (tendsto_finsetSum _ fun m _ => Tendsto.mul ?_ ?_)
  · exact ContinuousWithinAt.comp (g := valAt M.x (F.u' I ⟨k, m⟩))
      (continuousWithinAt_valAt_of_regAt hz (hG.2.1 _ _).2) hβ hS
  · exact ((continuous_apply (⟨k, m⟩ : Σ k, ι k)).continuousAt.comp_continuousWithinAt hP)

theorem wRho_continuousOn : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin (d + 2)), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → ContinuousOn (wRho M Rb τ k₀ ca cb F kb r h ε) (wO M Rb τ a k₀ ca cb F kb V r h) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε H
  obtain ⟨hb, hab, hk, hca, hcb, hy, hF, hB, horb, hr, hh⟩ := H
  obtain ⟨hVo, hVt, -, -, hbl⟩ := hB
  have hbase : Set.MapsTo (baseOf M k₀) (wO M Rb τ a k₀ ca cb F kb V r h) (mcPts (mCoordIdeal M.x)) := fun z hz =>
    GlobalTheory.CompanionTheory.Ar.PB.CPts.base_mem M (GlobalTheory.CompanionTheory.Ar.PB.CPts.comp_mem_mcPts (GlobalTheory.CompanionTheory.Ar.PB.WSq.Pts.isBlockMap_v₀ k₀)
      (algebraMap Φ (RatFunc Φ)) (funext fun _ => rfl) hz.1)
  have cB : Continuous (baseOf M k₀) := continuous_pi fun q => continuous_apply _
  have cF : Continuous (fstPt (ι := ι) k₀) := continuous_pi fun q => continuous_apply _
  have cS : Continuous (sndPt (ι := ι) k₀) := continuous_pi fun q => continuous_apply _
  have hgood : ∀ z ∈ wO M Rb τ a k₀ ca cb F kb V r h, M.GoodAt F (mCoordIdeal (baseOf M k₀ z)) := by
    intro z hz
    have h3 := (hbl _ hz.2.2.1).2.2
    rw [(Rb.A.chart kb).left_inv hz.2.1] at h3
    have e := orbit_trans (orbit_symm (horb _ (hbase hz))) h3.2
    rw [GlobalTheory.CompanionTheory.Ar.PB.CovMap.mCoordIdeal_eq_of_sameOrbit e]
    exact h3.1
  have cLow : ∀ (P : ((Σ o : Option K, ι (o.getD k₀)) → ℂ) → (Σ k, ι k) → ℂ), Continuous P → ∀ (τ' : Ψ) (a' b' : Fin N),
      ∀ z ∈ wO M Rb τ a k₀ ca cb F kb V r h, (∀ k, M.blk (τ', stepOf N j b') = some k →
        twMinor M F (baseOf M k₀ z) (stepOf N j b') k (h τ')⁻¹ (P z) (stepCols N j (stepOf N j b')) ≠ 0) →
      ContinuousWithinAt (fun z => lowRead M F (baseOf M k₀ z) h (P z) τ' a' b')
        (wO M Rb τ a k₀ ca cb F kb V r h) z := by
    intro P hP τ' a' b' z hz hne
    have cT := fun (k : K) (J : Finset (Fin N)) => twMinor_continuousWithinAt M F cB.continuousWithinAt hbase (hbase hz)
      (hgood z hz) hP.continuousWithinAt (stepOf N j b') k (h τ')⁻¹ J
    cases e : M.blk (τ', stepOf N j b') with
    | none =>
      simp only [lowRead, e, Option.elim_none]
      exact continuousWithinAt_const
    | some k =>
      simp only [lowRead, e, Option.elim_some]
      exact (cT k _).div (cT k _) (hne k e)
  have hst : stepOf N j ca = a := by
    apply Fin.ext
    have h1 := a.2
    have h2 := ca.2
    have h3 := M.j_le
    simp only [stepOf, lastCol] at hca ⊢
    split_ifs at hca ⊢ <;> omega
  intro z hz
  have hz₄ : ∀ p k, M.blk p = some k →
      twMinor M F (baseOf M k₀ z) p.2 k (h p.1)⁻¹ (fstPt k₀ z) (stepCols N j p.2) ≠ 0 := hz.2.2.2.1
  have hz₅ : twMinor M F (baseOf M k₀ z) a k₀ (h τ)⁻¹ (sndPt k₀ z) (stepCols N j a) ≠ 0 := hz.2.2.2.2
  refine continuousWithinAt_pi.2 fun i => ?_
  rcases e : ε.symm i with l | q | u
  · simp only [wRho, e]
    have c2 : ContinuousWithinAt (r ∘ baseOf M k₀) (wO M Rb τ a k₀ ca cb F kb V r h) z :=
      ContinuousWithinAt.comp (hr _ (hbase hz)) cB.continuousWithinAt hbase
    have c3 : ContinuousAt (fun x => Rb.A.chart kb x l) ((r ∘ baseOf M k₀) z) :=
      (continuous_apply l).continuousAt.comp ((Rb.A.chart kb).continuousAt hz.2.1)
    exact ContinuousAt.comp_continuousWithinAt (g := fun x => Rb.A.chart kb x l) c3 c2
  · simp only [wRho, e]
    exact cLow (fstPt k₀) cF q.1.1 q.1.2.1 q.1.2.2 z hz fun k e' => hz₄ (q.1.1, stepOf N j q.1.2.2) k e'
  · simp only [wRho, e]
    refine (cLow (sndPt k₀) cS τ cb ca z hz fun k e' => ?_).sub (cLow (fstPt k₀) cF τ cb ca z hz fun k e' => ?_)
    · rw [hst] at e' ⊢
      obtain rfl : k₀ = k := Option.some.inj (hk.symm.trans e')
      exact hz₅
    · exact hz₄ (τ, stepOf N j ca) k e'

end Flag

end GlobalTheory.CompanionTheory.Ar.PB.WMan
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartEighthStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_adjacent_chart_eighth : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin (d + 2)), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → ContinuousOn (wRho M Rb τ k₀ ca cb F kb r h ε) (wO M Rb τ a k₀ ca cb F kb V r h) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.wRho_continuousOn | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.wRho_continuousOn | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.wRho_continuousOn <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsWeightedHomogeneousOfIsMultiHomog
set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart

open MvPolynomial GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver segre scaleBlock)
open ReciprocityTheory.AnForm.R (conePts)

open GoodChartModel Matrix
open ReciprocityTheory.ChartRestriction.G.Geo (blkW weight_blkW segMono eval_segMono psiPoly eval_psiPoly
  comp_mul_homog diag_of_homog)

section Rel

attribute [local instance] MvPolynomial.weightedGradedAlgebra

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isWeightedHomogeneous_of_isMultiHomog [DecidableEq K] {s : MRingOver ℂ ι} {a : K → ℕ}
    (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a) : IsWeightedHomogeneous (blkW ι) s a := by
  intro d hd
  funext k
  rw [weight_blkW]
  exact hs d (mem_support_iff.2 hd) k

theorem cone_homog [DecidableEq K] {Q : Ideal (MRingOver ℂ ι)} (hQ : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q) :
    Q.IsHomogeneous (weightedHomogeneousSubmodule ℂ (blkW ι)) := by
  obtain ⟨S, hS, rfl⟩ := hQ
  refine Ideal.homogeneous_span _ _ ?_
  intro f hf
  obtain ⟨a, ha⟩ := hS f hf
  exact ⟨a, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr (isWeightedHomogeneous_of_isMultiHomog ha)⟩

theorem cone_segre_rel {e : ℕ} {Q : Ideal (MRingOver ℂ ι)} (hP : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (hΨ : CxInt.IsSetGoodProj (conePts Q) Ψ)
    (i : (k : K) → ι k) :
    ∃ r : ℕ, 0 < r ∧ ∃ G : Fin (e + 1) → MvPolynomial ((k : K) → ι k) ℂ,
      (∀ j, (G j).totalDegree ≤ r - 1) ∧
      ∀ z ∈ conePts Q, segre z i ^ r = ∑ j, Ψ (segre z) j * eval (segre z) (G j) := by
  classical
  have hsegMono (a : (k : K) → ι k) : IsWeightedHomogeneous (blkW ι) (segMono ι a) (fun _ => 1) := by
    have hprod := IsWeightedHomogeneous.prod (w := blkW ι) Finset.univ
      (fun k => (X ⟨k, a k⟩ : MvPolynomial (Σ k, ι k) ℂ))
      (fun k => blkW ι ⟨k, a k⟩) (fun k _ => isWeightedHomogeneous_X ℂ _ _)
    unfold segMono
    convert hprod using 1
    funext k
    simp [blkW, Finset.sum_apply, Pi.single_apply]
  have hpsiPoly (j : Fin (e + 1)) : IsWeightedHomogeneous (blkW ι) (psiPoly Ψ j) (fun _ => 1) := by
    unfold psiPoly
    exact IsWeightedHomogeneous.sum _ _ _ fun a _ => (hsegMono a).C_mul _
  set I := Q ⊔ Ideal.span (Set.range (psiPoly Ψ)) with hI
  have hrad : segMono ι i ∈ I.radical := by
    rw [← vanishingIdeal_zeroLocus_eq_radical (K := ℂ), mem_vanishingIdeal_iff]
    intro x hx
    have hae : ∀ p : MvPolynomial (Σ k, ι k) ℂ, aeval x p = eval x p :=
      fun _ => rfl
    rw [hae]
    by_contra h
    rw [eval_segMono, ReciprocityTheory.ChartRestriction.G.Geo.segre, ← ne_eq, Finset.prod_ne_zero_iff] at h
    have hxm : x ∈ conePts Q := ⟨fun k => ⟨i k, h k (Finset.mem_univ _)⟩, fun f hf => by
      have := hx _ (Ideal.mem_sup_left hf : f ∈ I)
      rwa [hae] at this⟩
    refine hΨ x hxm (funext fun j => ?_)
    have := hx _ (Ideal.mem_sup_right (Ideal.subset_span ⟨j, rfl⟩) : psiPoly Ψ j ∈ I)
    rwa [hae, eval_psiPoly] at this
  obtain ⟨r0, hr0⟩ := hrad
  have hmem : segMono ι i ^ (r0 + 1) ∈ I := by
    rw [pow_succ]; exact Ideal.mul_mem_right _ _ hr0
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.mp hb
  let D : K → ℕ := fun _ => r0
  let comp := weightedHomogeneousComponent (R := ℂ) (blkW ι) (D + fun _ => 1)
  have hpow : IsWeightedHomogeneous (blkW ι) (segMono ι i ^ (r0 + 1)) (D + fun _ => 1) := by
    have := (hsegMono i).pow (r0 + 1)
    convert this using 1
    funext k; simp [D]
  have hcomp := congrArg comp hab
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_add (f := _), map_sum, weightedHomogeneousComponent_eq_self hpow] at hcomp
  simp only [comp, comp_mul_homog (hpsiPoly _)] at hcomp
  have hcd : ∀ j, ∃ G : MvPolynomial ((k : K) → ι k) ℂ, G.totalDegree ≤ r0 ∧
      ∀ z : (Σ k, ι k) → ℂ, eval z (weightedHomogeneousComponent (blkW ι) D (c j)) =
        eval (segre z) G :=
    fun j => diag_of_homog r0 (weightedHomogeneousComponent_isWeightedHomogeneous _ _)
  choose G hG hGz using hcd
  refine ⟨r0 + 1, Nat.succ_pos _, G, fun j => by simpa using hG j, fun z hz => ?_⟩
  have h0 := congrArg (eval z) hcomp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_add (f := _), hz.2 _ (weightedHomogeneousComponent_mem_of_mem _ _ (cone_homog hP) ha _),
    zero_add, map_sum, map_pow, eval_segMono] at h0
  rw [← h0]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, hGz, eval_psiPoly, mul_comm]

theorem cone_pow_mem {Q : Ideal (MRingOver ℂ ι)} {e m : ℕ} {σ : Fin m ≃ ((k : K) → ι k)}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    (hP : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q) (hΨ : CxInt.IsSetGoodProj (conePts Q) Ψ)
    {J : Ideal (MvPolynomial (Fin m) ℂ)} (hJ : setChartIdeal (conePts Q) σ Ψ ≤ J) (a : Fin m) :
    ∃ r : ℕ, (X a ^ r : MvPolynomial (Fin m) ℂ) ∈ leadIdeal J ⊔ linIdeal (chartProjMatrix σ Ψ) := by
  classical
  obtain ⟨r, hr, G, hG, hrel⟩ := cone_segre_rel hP Ψ hΨ (σ a)
  set A := chartProjMatrix σ Ψ with hA
  let Gx : Fin (e + 1) → MvPolynomial (Fin m) ℂ := fun j => rename σ.symm (G j)
  have hGx : ∀ j, (Gx j).totalDegree ≤ r - 1 := fun j => (totalDegree_rename_le _ _).trans (hG j)
  let f : MvPolynomial (Fin m) ℂ := X a ^ r - (Gx 0 + ∑ j : Fin e, Gx j.succ * linPoly A j)
  have hfJ : f ∈ J := by
    refine hJ ?_
    rw [setChartIdeal, MvPolynomial.mem_vanishingIdeal_iff]
    rintro _ ⟨z, hz, hz1, rfl⟩
    have hw : ((fun a => segre z (σ a)) ∘ σ.symm) = segre z := by
      funext i'
      simp
    have h := hrel z hz
    rw [Fin.sum_univ_succ, hz1, one_mul] at h
    change eval (fun a => segre z (σ a)) f = 0
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [f, Gx, map_sub, map_add (f := _), map_pow, map_sum, map_mul, eval_X, eval_rename, hw,
      GroundTheory.Heights₂.Heights.eval_linPoly, hA, chartProjMatrix_mulVec]
    rw [h]
    simp [Equiv.apply_symm_apply, mul_comm]
  have hdeg : f.totalDegree ≤ r := by
    refine (totalDegree_sub _ _).trans (max_le (by rw [totalDegree_X_pow]) ?_)
    refine (totalDegree_add _ _).trans (max_le ((hGx 0).trans (Nat.sub_le _ _)) ?_)
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
    refine (totalDegree_mul _ _).trans ?_
    have h1 := hGx j.succ
    have h2 := (isHomogeneous_linPoly A j).totalDegree_le
    omega
  have h1 : 1 ≤ r := hr
  have hX : homogeneousComponent r (X a ^ r : MvPolynomial (Fin m) ℂ) = X a ^ r := by
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule r _).2 (isHomogeneous_X_pow a r)),
      if_pos rfl]
  have h0 : homogeneousComponent r (Gx 0) = 0 :=
    homogeneousComponent_eq_zero (n := r) (φ := Gx 0) (by have := hGx 0; omega)
  have hcomp : homogeneousComponent r f =
      X a ^ r - ∑ j : Fin e, homogeneousComponent (r - 1) (Gx j.succ) * linPoly A j := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [f, map_sub, map_add (f := _), map_sum, hX, h0, zero_add,
      homogeneousComponent_mul_of_isHomogeneous_right _ _ (isHomogeneous_linPoly A _), h1, if_true]
  have hmem : homogeneousComponent r f + ∑ j : Fin e, homogeneousComponent (r - 1) (Gx j.succ) * linPoly A j ∈
      leadIdeal J ⊔ linIdeal A :=
    add_mem (Ideal.mem_sup_left (GroundTheory.Heights₂.Heights.homogeneousComponent_mem_leadIdeal hfJ hdeg))
      (Ideal.mem_sup_right (Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)))
  rw [hcomp, sub_add_cancel] at hmem
  exact ⟨r, hmem⟩

theorem cxChartModel {Q : Ideal (MRingOver ℂ ι)} {e : ℕ} (hQ : CxInt.IsCxVar Q e) {m : ℕ}
    (σ : Fin m ≃ ((k : K) → ι k)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hΨ : CxInt.IsSetGoodProj (conePts Q) Ψ) :
    zeroSet (setChartIdeal (conePts Q) σ Ψ) = setChartSet (conePts Q) σ Ψ ∧
      ∀ J ∈ (setChartIdeal (conePts Q) σ Ψ).minimalPrimes,
        ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ J) = (e : ℕ) ∧ IsFiniteProjection J (chartProjMatrix σ Ψ) := by
  obtain ⟨hK, ⟨hQp, hQh, -⟩, hdimQ⟩ := hQ
  have hR : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q := hQh
  refine ⟨chart_zeroSet hR σ Ψ, fun J hJ => ?_⟩
  have hdim := chart_dim hQp hR hdimQ σ Ψ hJ
  have hfin : (projHom J (chartProjMatrix σ Ψ)).toRingHom.Finite := by
    have hrad : originIdeal m ≤ (leadIdeal J ⊔ linIdeal (chartProjMatrix σ Ψ)).radical := by
      refine Ideal.span_le.2 (Set.range_subset_iff.2 fun a => ?_)
      obtain ⟨r, hr⟩ := cone_pow_mem hR hΨ hJ.1.2 a
      exact ⟨r, hr⟩
    obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg_radical hrad (IsNoetherian.noetherian _)
    exact ConeAvoidsFinite.proof m e N J _ hN
  exact ⟨hdim, ⟨FiniteProjHomInjective.proof m e J _ hJ.1.1 hdim hfin, hfin⟩⟩

end Rel

end GlobalTheory.CompanionTheory.Ar.Pub.CxChart
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RingKrullDimChartComponents
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RingKrullDimChartComponents
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt
open ReciprocityTheory.AnForm.R (conePts)

theorem chartComponents_dim : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k),
    IsCxVar Q e → ∀ J ∈ chartComponents (conePts Q) σ i,
      ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ J) = (e : ℕ) := by
  intro K _ _ ι _ Q e m σ i hQ J hJ
  have hmin : J ∈ (setSegChartIdeal (conePts Q) σ i).minimalPrimes :=
    mem_chartComponents.mp hJ
  have hhom : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q := hQ.2.1.2.1
  exact segChart_dim hQ.2.1.1 hhom hQ.2.2 σ i hmin

end GlobalTheory.CompanionTheory.Ar.Pub.CxChart
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RingKrullDimChartComponentsStatement
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringKrullDim_chartComponents : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k),
    IsCxVar Q e → ∀ J ∈ chartComponents (conePts Q) σ i,
      ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ J) = (e : ℕ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.CxChart.chartComponents_dim | exact GlobalTheory.CompanionTheory.Ar.Pub.CxChart.chartComponents_dim | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.CxChart.chartComponents_dim <;> assumption)
end
end
