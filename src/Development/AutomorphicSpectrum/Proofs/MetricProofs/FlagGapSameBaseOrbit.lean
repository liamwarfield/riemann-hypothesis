module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticThird
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsPermOfRange
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GenFibreExists

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapSameBaseOrbit
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapSameBaseOrbit
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW

theorem stepGap_eq_of_base_block : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (x₀ : BM.Rb.X) (z z' : (Σ k, ι k) → ℂ), x₀ ∉ bdry BM.s → z ∈ mcPts (mCoordIdeal y) → z' ∈ mcPts (mCoordIdeal y) → SameOrbit (basePart M.blk z) (BM.Rb.lift x₀ x₀) → basePart M.blk z = basePart M.blk z' → (∀ k, M.blk p = some k → ∀ m : ι k, z ⟨k, m⟩ = z' ⟨k, m⟩) → stepGap M BM p z = stepGap M BM p z' := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM p x₀ z z' hx₀ hz hz' horb hbase hblk
  obtain ⟨l, hl⟩ := BM.O_cover x₀
  have hx : x₀ ∈ BM.O l \ ReciprocityTheory.AnForm.P.bdry BM.s := ⟨hl, hx₀⟩
  have horb' : ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit (GlobalTheory.CompanionTheory.Ar.PB.basePart M.blk z') (BM.Rb.lift x₀ x₀) := by
    rw [← hbase]
    exact horb
  have hbm : GlobalTheory.CompanionTheory.Ar.PB.StepW.baseMono M (BM.F l) p z = GlobalTheory.CompanionTheory.Ar.PB.StepW.baseMono M (BM.F l) p z' := by
    unfold GlobalTheory.CompanionTheory.Ar.PB.StepW.baseMono
    rw [hbase]
  have hfs : (GroundTheory.Heights₂.Heights.LowerBoundFree.fsHerm ι (M.dy p)).h z =
      (GroundTheory.Heights₂.Heights.LowerBoundFree.fsHerm ι (M.dy p)).h z' := by
    show GroundTheory.Heights₂.Heights.LowerBoundFree.refNorm (M.dy p) z =
      GroundTheory.Heights₂.Heights.LowerBoundFree.refNorm (M.dy p) z'
    unfold GroundTheory.Heights₂.Heights.LowerBoundFree.refNorm
    refine Finset.prod_congr rfl (fun k _ => ?_)
    by_cases h0 : M.dy p k = 0
    · simp [h0]
    · have hcoord : ∀ i, z ⟨k, i⟩ = z' ⟨k, i⟩ := by
        intro i
        by_cases hk : M.blk p = some k
        · exact hblk k hk i
        · by_cases hb : ∀ p' : Ψ × Fin N, M.blk p' ≠ some k
          · exact congrFun hbase ⟨⟨k, hb⟩, i⟩
          · exfalso
            apply h0
            unfold GlobalTheory.CompanionTheory.Ar.PB.FlagModel.dy
            rw [dite_eq_right hb, if_neg hk]
      simp only [hcoord]
  have hh : Real.log ((BM.hom p).h z) = Real.log ((BM.hom p).h z') := by
    cases hp : M.blk p with
    | none =>
      rw [GlobalTheory.T.log_block_metric_off_boundary K ι Φ y Ψ N j M n BM p l x₀ z hp hx hz horb,
        GlobalTheory.T.log_block_metric_off_boundary K ι Φ y Ψ N j M n BM p l x₀ z' hp hx hz' horb', hbm, hbase]
    | some k₀ =>
      obtain ⟨I₀, hI₀, hne⟩ := GlobalTheory.T.block_metric_row_echelon_local K ι Φ y Ψ N j M n BM p k₀ l x₀ z hp hl hz horb
      obtain ⟨C, B, hCB⟩ := GlobalTheory.CompanionTheory.Ar.PB.StepW.GrChart.exists_isGrChart N j p.2 I₀ M.j_le hI₀
      have hfun : GlobalTheory.CompanionTheory.Ar.PB.StepW.plk M (BM.F l) k₀ z = GlobalTheory.CompanionTheory.Ar.PB.StepW.plk M (BM.F l) k₀ z' := by
        funext I
        unfold GlobalTheory.CompanionTheory.Ar.PB.StepW.plk
        rw [hbase]
        simp only [hblk k₀ hp]
      have hne' : GlobalTheory.CompanionTheory.Ar.PB.StepW.plk M (BM.F l) k₀ z' I₀ ≠ 0 := by
        rw [← hfun]
        exact hne
      rw [GlobalTheory.T.block_metric_explicit_matrix_form K ι Φ y Ψ N j M n BM p k₀ l x₀ z I₀ C B hp hCB hx hz horb hne,
        GlobalTheory.T.block_metric_explicit_matrix_form K ι Φ y Ψ N j M n BM p k₀ l x₀ z' I₀ C B hp hCB hx hz' horb' hne', hfun, hbm]
  unfold GlobalTheory.CompanionTheory.Ar.PB.StepW.stepGap
  rw [hh, hfs]

end GlobalTheory.CompanionTheory.Ar.PB.StepW
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapSameBaseOrbitStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_gap_same_base_orbit : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (x₀ : BM.Rb.X) (z z' : (Σ k, ι k) → ℂ), x₀ ∉ bdry BM.s → z ∈ mcPts (mCoordIdeal y) → z' ∈ mcPts (mCoordIdeal y) → SameOrbit (basePart M.blk z) (BM.Rb.lift x₀ x₀) → basePart M.blk z = basePart M.blk z' → (∀ k, M.blk p = some k → ∀ m : ι k, z ⟨k, m⟩ = z' ⟨k, m⟩) → stepGap M BM p z = stepGap M BM p z' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.StepW.stepGap_eq_of_base_block | exact GlobalTheory.CompanionTheory.Ar.PB.StepW.stepGap_eq_of_base_block | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.StepW.stepGap_eq_of_base_block <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsLocalTwistTrivialization
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsLocalTwistTrivialization
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.RootsBase

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

theorem frame_values :
    ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) (x : κ → Ω) (L : Lat ξ E) (m r n : ℕ) (V : Submodule Ω E) (φ : Fin n → Module.Dual Ω E) (cb : Fin r → E), IsTwistGen ξ x L m φ → L.IsVB r V → LinearIndependent Ω cb → Submodule.span Ω (Set.range cb) = V → ∀ (p : Cpt ξ) (c : κ), InChart ξ x c p → ∃ (T : Matrix (Fin r) (Fin r) Ω) (C : Matrix (Fin r) (Fin n) Ω), IsUnit T.det ∧ L.IsFrameAt (colFrame cb T) p ∧ (∀ a b, ((Matrix.of fun a b => φ a (cb b)) * T) a b / x c ^ m ∈ regAt ξ p) ∧ (∀ a b, C a b ∈ regAt ξ p) ∧ ∀ a b, ∑ k, C a k * (((Matrix.of fun a b => φ a (cb b)) * T) k b / x c ^ m) = if a = b then 1 else 0 := by
  intro X Ω _ ξ E _ _ κ x L m r n V φ cb hG hV hli hsp p c hc
  obtain ⟨U, hU, b, hbsp, hb⟩ := hV p (Set.mem_univ p)
  have hf : L.IsFrameAt b p := hb p (Set.mem_univ p) hU
  have h1 : ∀ l, ∃ t : Fin r → Ω, ∑ a, t a • cb a = b l := fun l => by
    have : b l ∈ Submodule.span Ω (Set.range cb) := by
      rw [hsp, ← hbsp]; exact Submodule.subset_span ⟨l, rfl⟩
    exact (Submodule.mem_span_range_iff_exists_fun Ω).1 this
  have h2 : ∀ l, ∃ t : Fin r → Ω, ∑ a, t a • b a = cb l := fun l => by
    have : cb l ∈ Submodule.span Ω (Set.range b) := by
      rw [hbsp, ← hsp]; exact Submodule.subset_span ⟨l, rfl⟩
    exact (Submodule.mem_span_range_iff_exists_fun Ω).1 this
  choose t ht using h1
  choose t' ht' using h2
  let T : Matrix (Fin r) (Fin r) Ω := Matrix.of fun a l => t l a
  let T' : Matrix (Fin r) (Fin r) Ω := Matrix.of fun a l => t' l a
  have hT : colFrame cb T = b := by
    funext l; exact ht l
  have hT' : colFrame b T' = cb := by
    funext l; exact ht' l
  have hmul : T * T' = 1 := by
    have e : colFrame cb (T * T') = colFrame cb (1 : Matrix (Fin r) (Fin r) Ω) := by
      rw [colFrame_mul, hT, hT', colFrame_one]
    ext a l
    have h3 := congrFun e l
    simp only [colFrame] at h3
    have h0 := (Fintype.linearIndependent_iff.1 hli) (fun a => (T * T') a l - (1 : Matrix _ _ Ω) a l)
      (by simp only [sub_smul, Finset.sum_sub_distrib, h3, sub_self]) a
    exact sub_eq_zero.1 h0
  have hdet : IsUnit T.det := Matrix.isUnit_det_of_right_inverse hmul
  have hval : ∀ a l, ((Matrix.of fun a b => φ a (cb b)) * T) a l = φ a (b l) := by
    intro a l
    rw [← hT]
    simp [Matrix.mul_apply, colFrame, mul_comm]
  have hmem : ∀ l, b l ∈ L p := fun l => by
    rw [hf.2]; exact Submodule.subset_span ⟨l, rfl⟩
  have hw : ∀ l, ∃ w : Module.Dual Ω E, ∀ k, w (b k) = if l = k then 1 else 0 := fun l => by
    obtain ⟨w, h1, h0⟩ := GlobalTheory.CompanionTheory.Ar.FlagGrGen.exists_coord hf.1 l
    refine ⟨w, fun k => ?_⟩
    split_ifs with h
    · rw [← h]; exact h1
    · exact h0 k (Ne.symm h)
  choose w hw using hw
  have hwreg : ∀ l, ∀ e ∈ L p, w l e ∈ regAt ξ p := by
    intro l e he
    rw [hf.2] at he
    induction he using Submodule.span_induction with
    | mem e h =>
      obtain ⟨k, rfl⟩ := h
      rw [hw]
      split_ifs
      exacts [one_mem _, zero_mem _]
    | zero => simp [zero_mem]
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a e _ he =>
      have h4 : w l (a • e) = (a : Ω) * w l e := by rw [Subring.smul_def, map_smul, smul_eq_mul]
      rw [h4]; exact mul_mem a.2 he
  choose g hg hg' using fun l => hG.2 p c hc (w l) (hwreg l)
  refine ⟨T, Matrix.of g, hdet, ?_, ?_, ?_, ?_⟩
  · rw [hT]; exact hf
  · intro a l; rw [hval]; exact hG.1 a p c hc _ (hmem l)
  · intro a j; exact hg a j
  · intro a l
    simp only [hval, Matrix.of_apply]
    rw [← hg' a (b l) (hmem l), hw]

end GlobalTheory.CompanionTheory.Ar.PB.FMX.RootsBase
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsLocalTwistTrivializationStatement
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_twist_trivialization : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) (x : κ → Ω) (L : Lat ξ E) (m r n : ℕ) (V : Submodule Ω E) (φ : Fin n → Module.Dual Ω E) (cb : Fin r → E), IsTwistGen ξ x L m φ → L.IsVB r V → LinearIndependent Ω cb → Submodule.span Ω (Set.range cb) = V → ∀ (p : Cpt ξ) (c : κ), InChart ξ x c p → ∃ (T : Matrix (Fin r) (Fin r) Ω) (C : Matrix (Fin r) (Fin n) Ω), IsUnit T.det ∧ L.IsFrameAt (colFrame cb T) p ∧ (∀ a b, ((Matrix.of fun a b => φ a (cb b)) * T) a b / x c ^ m ∈ regAt ξ p) ∧ (∀ a b, C a b ∈ regAt ξ p) ∧ ∀ a b, ∑ k, C a k * (((Matrix.of fun a b => φ a (cb b)) * T) k b / x c ^ m) = if a = b then 1 else 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.RootsBase.frame_values | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.RootsBase.frame_values | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.RootsBase.frame_values <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsNonzeroXbOfLeftInverse
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsNonzeroXbOfLeftInverse
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.BasePt

theorem exists_rows_det_ne_zero {Ω : Type} [Field Ω] {n m : ℕ} (M : Matrix (Fin n) (Fin m) Ω)
    (B : Matrix (Fin m) (Fin n) Ω) (h : B * M = 1) :
    ∃ J : Fin m → Fin n, (M.submatrix J id).det ≠ 0 := by
  have hspan : Submodule.span Ω (Set.range fun j => M j) = ⊤ := by
    rw [eq_top_iff]
    intro w _
    have hw : w = (w ᵥ* B) ᵥ* M := by rw [Matrix.vecMul_vecMul, h, Matrix.vecMul_one]
    rw [hw, Matrix.vecMul_eq_sum]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  obtain ⟨f, hf, -, hl⟩ := Submodule.exists_fun_fin_finrank_span_eq Ω (Set.range fun j => M j)
  have e : Module.finrank Ω (Submodule.span Ω (Set.range fun j => M j)) = m := by
    rw [hspan, finrank_top, Module.finrank_fin_fun]
  choose J hJ using fun i : Fin m => hf (Fin.cast e.symm i)
  refine ⟨J, ?_⟩
  have hl' : LinearIndependent Ω (M.submatrix J id).row := by
    have : (M.submatrix J id).row = f ∘ Fin.cast e.symm := by
      funext i
      exact hJ i
    rw [this]
    exact hl.comp _ (Fin.cast_injective _)
  exact ((Matrix.isUnit_iff_isUnit_det _).1
    (Matrix.linearIndependent_rows_iff_isUnit.1 hl')).ne_zero

theorem exists_rows_castLE_det_ne_zero {Ω : Type} [Field Ω] {n m a : ℕ} (M : Matrix (Fin n) (Fin m) Ω)
    (B : Matrix (Fin m) (Fin n) Ω) (h : B * M = 1) (ha : a + 1 ≤ m) (hm : a + 1 = m) :
    ∃ J : Fin (a + 1) → Fin n, (M.submatrix J (Fin.castLE ha)).det ≠ 0 := by
  subst hm
  obtain ⟨J, hJ⟩ := exists_rows_det_ne_zero M B h
  exact ⟨J, hJ⟩

theorem step_full {Ψ : Type} {p q : ℕ} (K₀ : Type) (t : StepIx Ψ p q)
    (h : ∀ r, blkF (Ψ := Ψ) (p := p) (q := q) K₀ r ≠ some (.inr t)) :
    (t.2 : ℕ) + 1 = rk Ψ p q t.1 := by
  classical
  obtain ⟨s, a⟩ := t
  rcases s with τ | τ
  · have ha : (a : ℕ) < p := a.2
    by_contra hne
    have hne' : (a : ℕ) + 1 ≠ p := hne
    refine h (τ, ⟨a, by omega⟩) ?_
    have hp : IsProperStep (p + q) p (⟨a, by omega⟩ : Fin (p + q)) :=
      ⟨hne', by show (a : ℕ) + 1 ≠ p + q; intro h'; omega⟩
    rw [blkF, if_pos hp]
    simp [stepOf, ha]
    rfl
  · have ha : (a : ℕ) < q := a.2
    by_contra hne
    have hne' : (a : ℕ) + 1 ≠ q := hne
    refine h (τ, ⟨p + a, by omega⟩) ?_
    have hp : IsProperStep (p + q) p (⟨p + a, by omega⟩ : Fin (p + q)) := by
      constructor
      · show p + (a : ℕ) + 1 ≠ p
        omega
      · show p + (a : ℕ) + 1 ≠ p + q
        omega
    rw [blkF, if_pos hp]
    simp [stepOf]
    rfl

theorem xb_block_ne : ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (Ω : Type) [Field Ω] (n : Ψ ⊕ Ψ → ℕ)
    (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type)
    [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω), (∀ k, ∃ i, x₀ ⟨k, i⟩ ≠ 0) →
    (∀ s, ∃ B : Matrix (Fin (rk Ψ p q s)) (Fin (n s)) Ω, B * A s = 1) →
    ∀ k, ∃ i, xb A x₀ ⟨k, i⟩ ≠ 0 := by
  intro Ψ _ p q Ω _ n A K₀ _ J₀ _ x₀ hx hB k
  obtain ⟨k, hk⟩ := k
  rcases k with k | t
  · exact hx k
  · obtain ⟨B, hB⟩ := hB t.1
    exact exists_rows_castLE_det_ne_zero (A t.1) B hB t.2.2 (step_full K₀ t hk)

end GlobalTheory.CompanionTheory.Ar.PB.FMX.BasePt
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsNonzeroXbOfLeftInverseStatement
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_xb_of_left_inverse : ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (Ω : Type) [Field Ω] (n : Ψ ⊕ Ψ → ℕ) (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω), (∀ k, ∃ i, x₀ ⟨k, i⟩ ≠ 0) → (∀ s, ∃ B : Matrix (Fin (rk Ψ p q s)) (Fin (n s)) Ω, B * A s = 1) → ∀ k, ∃ i, xb A x₀ ⟨k, i⟩ ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.BasePt.xb_block_ne | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.BasePt.xb_block_ne | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.BasePt.xb_block_ne <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsTriangularRegularFrameChange
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsTriangularRegularFrameChange
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

namespace GlobalTheory.CompanionTheory.Ar.PB.FrameTrans

theorem colFrame_injective {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] {r : ℕ} {e : Fin r → V}
    (he : LinearIndependent Ω e) {T T' : Matrix (Fin r) (Fin r) Ω} (h : colFrame e T = colFrame e T') : T = T' := by
  ext a b
  have hb := congrFun h b
  simp only [colFrame] at hb
  have h0 := Fintype.linearIndependent_iff.1 he (fun a => T a b - T' a b)
    (by simp only [sub_smul, Finset.sum_sub_distrib]; exact sub_eq_zero.2 hb) a
  exact sub_eq_zero.1 h0

theorem linearIndependent_colFrame {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] {r : ℕ} {w : Fin r → V}
    (hw : LinearIndependent Ω w) {g : Matrix (Fin r) (Fin r) Ω} (hg : IsUnit g.det) :
    LinearIndependent Ω (colFrame w g) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hsum : ∑ a, (g.mulVec c a) • w a = 0 := by
    rw [← hc]
    simp only [colFrame, Matrix.mulVec, dotProduct, Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [_root_.mul_comm]
  have h0 : g.mulVec c = 0 := funext (Fintype.linearIndependent_iff.1 hw _ hsum)
  have hc0 : c = 0 := Matrix.eq_zero_of_mulVec_eq_zero hg.ne_zero h0
  intro i
  rw [hc0]
  rfl

theorem exists_regular_coeff {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type}
    [AddCommGroup E] [Module Ω E] {p : Cpt ξ} {r : ℕ} {e : Fin r → E} {v : E}
    (h : v ∈ Submodule.span (regAt ξ p) (Set.range e)) :
    ∃ c : Fin r → Ω, (∀ a, c a ∈ regAt ξ p) ∧ v = ∑ a, c a • e a := by
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h
  exact ⟨fun k => (a k : Ω), fun k => (a k).2, ha.symm⟩

theorem exists_triangular {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] {r : ℕ} {b b₀ : Fin r → V}
    (hF : ∀ i, flagStep Ω b i = flagStep Ω b₀ i) :
    ∃ U : Matrix (Fin r) (Fin r) Ω, U.BlockTriangular id ∧ b = colFrame b₀ U := by
  have hex : ∀ l : Fin r, ∃ f : Fin r → Ω, (∀ k : Fin r, ¬ (k : ℕ) < (l : ℕ) + 1 → f k = 0) ∧
      b l = ∑ k, f k • b₀ k := by
    intro l
    have h1 : b l ∈ flagStep Ω b₀ ((l : ℕ) + 1) := by
      rw [← hF]
      exact Submodule.subset_span ⟨l, Nat.lt_succ_self _, rfl⟩
    obtain ⟨f, hf, hs⟩ := (Finsupp.mem_span_image_iff_linearCombination Ω).1 h1
    refine ⟨f, fun k hk => (Finsupp.mem_supported' Ω f).1 hf k hk, ?_⟩
    rw [← hs, Finsupp.linearCombination_apply]
    exact Finsupp.sum_fintype f (fun i a => a • b₀ i) (fun k => zero_smul Ω _)
  choose f hf0 hf using hex
  refine ⟨fun k l => f l k, ?_, ?_⟩
  · intro i j hij
    have hij' : j < i := hij
    refine hf0 j i ?_
    have : (j : ℕ) < i := hij'
    omega
  · funext l
    exact hf l

theorem sub_diag_mem {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] {r : ℕ} (b₀ : Fin r → V)
    {U : Matrix (Fin r) (Fin r) Ω} (hU : U.BlockTriangular id) (l : Fin r) :
    colFrame b₀ U l - U l l • b₀ l ∈ flagStep Ω b₀ l := by
  have h : colFrame b₀ U l - U l l • b₀ l = ∑ a ∈ Finset.univ.erase l, U a l • b₀ a := by
    rw [colFrame, ← Finset.add_sum_erase _ _ (Finset.mem_univ l), add_sub_cancel_left]
  rw [h]
  refine Submodule.sum_mem _ fun a ha => ?_
  have hne : a ≠ l := Finset.ne_of_mem_erase ha
  by_cases hlt : (a : ℕ) < l
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, hlt, rfl⟩)
  · have hla : l < a := lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hne)
    rw [hU hla, zero_smul]
    exact zero_mem _

theorem exists_adapted : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (r : ℕ) (w : Fin r → E) (P g : Matrix (Fin r) (Fin r) Ω) (p : Cpt ξ), LinearIndependent Ω w → IsUnit g.det → L.IsFrameAt (colFrame w P) p → L.IsFlagVBOn Set.univ (colFrame w g) → ∃ U Rm Rm' : Matrix (Fin r) (Fin r) Ω, U.BlockTriangular id ∧ (∀ a b, Rm a b ∈ regAt ξ p) ∧ (∀ a b, Rm' a b ∈ regAt ξ p) ∧ Rm * Rm' = 1 ∧ g * U = P * Rm ∧ ∀ l, (L.gr (colFrame w g) l).IsGenAt p (U l l) := by
  intro X Ω _ ξ E _ _ L r w P g p hw hg he hFl
  obtain ⟨V, hV, b, hbF, hbL⟩ := hFl p (Set.mem_univ p)
  have hb : L.IsFrameAt b p := hbL p (Set.mem_univ p) hV
  have hb₀ := linearIndependent_colFrame hw hg
  obtain ⟨U, hU, hbU⟩ := exists_triangular hbF
  have hexR : ∀ l : Fin r, ∃ c : Fin r → Ω, (∀ a, c a ∈ regAt ξ p) ∧ b l = ∑ a, c a • colFrame w P a := by
    intro l
    refine exists_regular_coeff ?_
    rw [← he.2, hb.2]
    exact Submodule.subset_span ⟨l, rfl⟩
  have hexR' : ∀ l : Fin r, ∃ c : Fin r → Ω, (∀ a, c a ∈ regAt ξ p) ∧ colFrame w P l = ∑ a, c a • b a := by
    intro l
    refine exists_regular_coeff ?_
    rw [← hb.2, he.2]
    exact Submodule.subset_span ⟨l, rfl⟩
  choose c hc hcs using hexR
  choose c' hc' hcs' using hexR'
  obtain ⟨Rm, hRm, hbR⟩ : ∃ Rm : Matrix (Fin r) (Fin r) Ω, (∀ a l, Rm a l ∈ regAt ξ p) ∧
      b = colFrame (colFrame w P) Rm := ⟨fun a l => c l a, fun a l => hc l a, funext hcs⟩
  obtain ⟨Rm', hRm', heR⟩ : ∃ Rm' : Matrix (Fin r) (Fin r) Ω, (∀ a l, Rm' a l ∈ regAt ξ p) ∧
      colFrame w P = colFrame b Rm' := ⟨fun a l => c' l a, fun a l => hc' l a, funext hcs'⟩
  refine ⟨U, Rm, Rm', hU, hRm, hRm', ?_, ?_, ?_⟩
  · refine colFrame_injective he.1 ?_
    rw [colFrame_mul, ← hbR, ← heR, colFrame_one]
  · refine colFrame_injective hw ?_
    rw [colFrame_mul, colFrame_mul, ← hbU, ← hbR]
  · intro l
    refine FlagGrGen.gr_isGenAt X Ω ξ E L r (colFrame w g) b p l (U l l) hb₀ hbF hb ?_
    rw [hbU]
    exact sub_diag_mem _ hU l

end GlobalTheory.CompanionTheory.Ar.PB.FrameTrans
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsTriangularRegularFrameChangeStatement
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_triangular_regular_frame_change : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (r : ℕ) (w : Fin r → E) (P g : Matrix (Fin r) (Fin r) Ω) (p : Cpt ξ), LinearIndependent Ω w → IsUnit g.det → L.IsFrameAt (colFrame w P) p → L.IsFlagVBOn Set.univ (colFrame w g) → ∃ U Rm Rm' : Matrix (Fin r) (Fin r) Ω, U.BlockTriangular id ∧ (∀ a b, Rm a b ∈ regAt ξ p) ∧ (∀ a b, Rm' a b ∈ regAt ξ p) ∧ Rm * Rm' = 1 ∧ g * U = P * Rm ∧ ∀ l, (L.gr (colFrame w g) l).IsGenAt p (U l l) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FrameTrans.exists_adapted | exact GlobalTheory.CompanionTheory.Ar.PB.FrameTrans.exists_adapted | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FrameTrans.exists_adapted <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.GMatIsGenericFlag
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.GMatIsGenericFlag
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.GenMat

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

section GenU

variable (Ω : Type) [Field Ω] {S : Type} (r : S → ℕ) (s : S)

theorem genU_self (a : Fin (r s)) : genU Ω r s a a = 1 := by
  simp [genU]

theorem genU_of_lt {a b : Fin (r s)} (h : a < b) : genU Ω r s a b = 0 := by
  simp [genU, not_lt.2 h.le, h.ne]

theorem genU_of_gt {l k : Fin (r s)} (h : k < l) :
    genU Ω r s l k = algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X ⟨s, ⟨(l, k), h⟩⟩) :=
  dif_pos h

end GenU

variable {Ψ : Type} {p q : ℕ} (Ω : Type) [Field Ω]

theorem symm_omEmb (a : Fin q) : (blockEquiv p q).symm (omEmb p q a) = .inl a := by
  rw [← blockEquiv_inl, Equiv.symm_apply_apply]

theorem symm_wEmb (a : Fin p) : (blockEquiv p q).symm (wEmb p q a) = .inr a := by
  rw [← blockEquiv_inr, Equiv.symm_apply_apply]

theorem gMat_apply (τ : Ψ) (i j : Fin (p + q)) :
    gMat p q Ω τ i j = (Matrix.fromBlocks (genU Ω (rk Ψ p q) (.inr τ) : Matrix (Fin q) (Fin q) _) 0 0
      (genU Ω (rk Ψ p q) (.inl τ) : Matrix (Fin p) (Fin p) _)) ((blockEquiv p q).symm i) ((blockEquiv p q).symm j) :=
  rfl

theorem gMat_om (τ : Ψ) (a b : Fin q) :
    gMat p q Ω τ (omEmb p q a) (omEmb p q b) = genU Ω (rk Ψ p q) (.inr τ) a b := by
  rw [gMat_apply, symm_omEmb, symm_omEmb]
  rfl

theorem gMat_w (τ : Ψ) (a b : Fin p) :
    gMat p q Ω τ (wEmb p q a) (wEmb p q b) = genU Ω (rk Ψ p q) (.inl τ) a b := by
  rw [gMat_apply, symm_wEmb, symm_wEmb]
  rfl

theorem gMat_om_w (τ : Ψ) (a : Fin q) (b : Fin p) : gMat p q Ω τ (omEmb p q a) (wEmb p q b) = 0 := by
  rw [gMat_apply, symm_omEmb, symm_wEmb]
  rfl

theorem gMat_lowerUni (τ : Ψ) : IsLowerUni (gMat p q Ω τ) := by
  constructor
  · intro a
    obtain ⟨x, rfl⟩ := (blockEquiv p q).surjective a
    rcases x with x | x
    · rw [blockEquiv_inl, gMat_om]
      exact genU_self Ω (rk Ψ p q) (.inr τ) x
    · rw [blockEquiv_inr, gMat_w]
      exact genU_self Ω (rk Ψ p q) (.inl τ) x
  · intro a b hab
    obtain ⟨x, rfl⟩ := (blockEquiv p q).surjective a
    obtain ⟨y, rfl⟩ := (blockEquiv p q).surjective b
    rcases x with x | x <;> rcases y with y | y
    · rw [blockEquiv_inl, blockEquiv_inl] at hab ⊢
      rw [gMat_om]
      exact genU_of_lt Ω (rk Ψ p q) (.inr τ) ((omEmb_strictMono p q).lt_iff_lt.1 hab)
    · rw [blockEquiv_inl, blockEquiv_inr, gMat_om_w]
    · rw [blockEquiv_inr, blockEquiv_inl] at hab
      have h : q + (x : ℕ) < (y : ℕ) := hab
      have := y.2
      omega
    · rw [blockEquiv_inr, blockEquiv_inr] at hab ⊢
      rw [gMat_w]
      exact genU_of_lt Ω (rk Ψ p q) (.inl τ) ((wEmb_strictMono p q).lt_iff_lt.1 hab)

def loc (t : GenIx (rk Ψ p q)) : Ψ × Fin (p + q) × Fin (p + q) :=
  match t with
  | ⟨.inl τ, lk⟩ => (τ, wEmb p q lk.1.1, wEmb p q lk.1.2)
  | ⟨.inr τ, lk⟩ => (τ, omEmb p q lk.1.1, omEmb p q lk.1.2)

theorem exists_var (x : LowIdx Ψ (p + q) p) :
    ∃ t : GenIx (rk Ψ p q), loc t = x.1 ∧ gMat p q Ω x.1.1 x.1.2.1 x.1.2.2 =
      algebraMap (MvPolynomial (GenIx (rk Ψ p q)) Ω) (GenField Ω (rk Ψ p q)) (MvPolynomial.X t) := by
  obtain ⟨⟨τ, a, b⟩, hlt, hiff⟩ := x
  obtain ⟨a, rfl⟩ := (blockEquiv p q).surjective a
  obtain ⟨b, rfl⟩ := (blockEquiv p q).surjective b
  rcases a with a | a <;> rcases b with b | b
  · simp only [blockEquiv_inl] at hlt hiff ⊢
    have h : b < a := (omEmb_strictMono p q).lt_iff_lt.1 hlt
    exact ⟨⟨.inr τ, ⟨(a, b), h⟩⟩, rfl, by
      rw [gMat_om]; exact genU_of_gt Ω (rk Ψ p q) (.inr τ) h⟩
  · exfalso
    simp only [blockEquiv_inl, blockEquiv_inr] at hlt
    have h : q + (b : ℕ) < (a : ℕ) := hlt
    have := a.2
    omega
  · exfalso
    simp only [blockEquiv_inl, blockEquiv_inr] at hiff
    have h : (q + (a : ℕ) < p + q - p ↔ (b : ℕ) < p + q - p) := hiff
    have := b.2
    omega
  · simp only [blockEquiv_inr] at hlt hiff ⊢
    have h : b < a := (wEmb_strictMono p q).lt_iff_lt.1 hlt
    exact ⟨⟨.inl τ, ⟨(a, b), h⟩⟩, rfl, by
      rw [gMat_w]; exact genU_of_gt Ω (rk Ψ p q) (.inl τ) h⟩

theorem gMat_indep :
    AlgebraicIndependent Ω fun x : LowIdx Ψ (p + q) p => gMat p q Ω x.1.1 x.1.2.1 x.1.2.2 := by
  choose e he₁ he₂ using exists_var (Ψ := Ψ) (p := p) (q := q) Ω
  have hinj : Function.Injective e := fun x y h => Subtype.ext (by rw [← he₁ x, ← he₁ y, h])
  have hX : AlgebraicIndependent Ω fun t : GenIx (rk Ψ p q) =>
      algebraMap (MvPolynomial (GenIx (rk Ψ p q)) Ω) (GenField Ω (rk Ψ p q)) (MvPolynomial.X t) :=
    (MvPolynomial.algebraicIndependent_X (GenIx (rk Ψ p q)) Ω).map'
      (f := IsScalarTower.toAlgHom Ω (MvPolynomial (GenIx (rk Ψ p q)) Ω) (GenField Ω (rk Ψ p q)))
      (IsFractionRing.injective _ _)
  have e' : (fun x : LowIdx Ψ (p + q) p => gMat p q Ω x.1.1 x.1.2.1 x.1.2.2) =
      (fun t : GenIx (rk Ψ p q) =>
        algebraMap (MvPolynomial (GenIx (rk Ψ p q)) Ω) (GenField Ω (rk Ψ p q)) (MvPolynomial.X t)) ∘ e :=
    funext he₂
  rw [e']
  exact hX.comp e hinj

theorem gMat_isGenericFlag : ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (Ω : Type) [Field Ω],
    GlobalTheory.CompanionTheory.Ar.PB.IsGenericFlag Ω p (gMat (Ψ := Ψ) p q Ω) := fun _ _ _ _ Ω _ =>
  IsGenericFlag.of_lowerUni (fun τ => gMat_lowerUni Ω τ) (gMat_indep Ω)

end GlobalTheory.CompanionTheory.Ar.PB.FMX.GenMat
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.GMatIsGenericFlagStatement
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isGenericFlag_gMat : ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (Ω : Type) [Field Ω], GlobalTheory.CompanionTheory.Ar.PB.IsGenericFlag Ω p (gMat (Ψ := Ψ) p q Ω) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.GenMat.gMat_isGenericFlag | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.GenMat.gMat_isGenericFlag | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.GenMat.gMat_isGenericFlag <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionVerticalPerturbationBound
section -- merged from Development.WeilBound.CoreStatements.PluriharmonicCharts.X_lemma_v
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace PositivityTheory.Xgp.lemma_v

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem divCycle_of_mem {P : Ideal (MRing ι)} {s : MRing ι} {W : Ideal (MRing ι)} (h : W ∈ divSupp P s) :
    divCycle P s W = multAt (P ⊔ Ideal.span {s}) W := by
  simp [ReciprocityTheory.ChartRestriction.G.Geo.divCycle, Finsupp.ofSupportFinite_coe, h]

theorem divCycle_of_notMem {P : Ideal (MRing ι)} {s : MRing ι} {W : Ideal (MRing ι)} (h : W ∉ divSupp P s) :
    divCycle P s W = 0 := by
  simp [ReciprocityTheory.ChartRestriction.G.Geo.divCycle, Finsupp.ofSupportFinite_coe, h]

theorem finsum_eq_sum (P : Ideal (MRing ι)) (s : MRing ι) (F : Ideal (MRing ι) → ℝ) (S : Finset (Ideal (MRing ι)))
    (hS : (divSupp_finite P s).toFinset ⊆ S) :
    ∑ᶠ W ∈ divSupp P s, (multAt (P ⊔ Ideal.span {s}) W : ℝ) * F W = ∑ W ∈ S, (divCycle P s W : ℝ) * F W := by
  rw [finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite P s), ← Finset.sum_subset hS]
  · refine Finset.sum_congr rfl fun W hW => ?_
    rw [divCycle_of_mem ((Set.Finite.mem_toFinset _).1 hW)]
  · intro W _ hW
    rw [divCycle_of_notMem (fun h => hW ((Set.Finite.mem_toFinset _).2 h)), Nat.cast_zero, zero_mul]

theorem sub_eq_cycR {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ} (hI : IsIntersectionFamily I)
    {P : Ideal (MRing ι)} {D : ℕ} {L : Fin D → HermLine ι} {A B : HermLine ι} (hP : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P (D + 1))
    (hL : ∀ j, IsSmoothHerm (L j)) (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) {f g : MRing ι} {df dg : K → ℕ}
    (hf : IsMultiHomog f df) (hg : IsMultiHomog g dg) (hfP : f ∉ P) (hgP : g ∉ P)
    (hd : ∀ k, (df k : ℤ) - dg k = A.a k - B.a k)
    (hn : ∀ z ∈ mcPts P,
      ‖eval z (map (Int.castRingHom ℂ) f)‖ * B.h z = ‖eval z (map (Int.castRingHom ℂ) g)‖ * A.h z) :
    I P (D + 1) (Fin.snoc L A) - I P (D + 1) (Fin.snoc L B) = cycR I P L f - cycR I P L g := by
  obtain ⟨-, hAdd, hR⟩ := hI
  set M : HermLine ι := (HermLine.sqMetric (ι := ι) dg).tensor B.inv with hMdef
  have hM : IsSmoothHerm M :=
    ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_tensor (isSmoothHerm_sqMetric dg) (ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_inv hB)
  have hRf := hR P D L _ f df hP hL (ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_tensor hA hM) (fun k => by
    show A.a k + ((dg k : ℤ) + -B.a k) = df k
    linarith [hd k]) hf hfP
  have hRg := hR P D L _ g dg hP hL (ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_tensor hB hM) (fun k => by
    show B.a k + ((dg k : ℤ) + -B.a k) = dg k
    ring) hg hgP
  have h1 := hAdd P D L A M hP hL hA hM
  have h2 := hAdd P D L B M hP hL hB hM
  have hint : arInt P f (A.tensor M) L = arInt P g (B.tensor M) L := by
    unfold arInt
    refine GroundTheory.Heights₂.Heights.Inter.ptsIntegral_congr_pts P _ fun z hz => ?_
    have hA0 := A.pos z hz.1
    have hB0 := B.pos z hz.1
    have hM0 := M.pos z hz.1
    show Real.log (‖eval z (map (Int.castRingHom ℂ) f)‖ / (A.h z * M.h z)) =
      Real.log (‖eval z (map (Int.castRingHom ℂ) g)‖ / (B.h z * M.h z))
    congr 1
    rw [div_eq_div_iff (mul_pos hA0 hM0).ne' (mul_pos hB0 hM0).ne', ← mul_assoc, ← mul_assoc, hn z hz]
  rw [recR_eq] at hRf hRg
  linarith

theorem geoNum_nonneg (hK : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KleimanNefIntersectionNonneg) {P : Ideal (MRing ι)} {D : ℕ}
    (hP : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P (D + 1)) {p : ℕ} (hp : p.Prime) {a : Fin D → K → ℤ} (ha : ∀ j, NefAt P p (a j))
    {W : Ideal (MRing ι)} (hW : W ∈ divSupp P (C (p : ℤ))) : 0 ≤ geoNum D W a := by
  have hle : P ⊔ Ideal.span {(C (p : ℤ) : MRing ι)} ≤ W := hW.1.1.2
  have hpW : (p : MRing ι) ∈ W := by
    have := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    rwa [map_natCast] at this
  have hnot : ∀ V : Ideal (MRing ι), IsHorizontal V → (C (p : ℤ) : MRing ι) ∉ V := by
    intro V hV h
    have h1 : (p : ℤ) ∈ V.comap (C : ℤ →+* MRing ι) := h
    rw [hV, Ideal.mem_bot] at h1
    exact hp.ne_zero (by exact_mod_cast h1)
  have hsec : IsSectionOn P (oneLine (ι := ι)) (C (p : ℤ)) := by
    refine ⟨0, fun k => rfl, fun m hm k => ?_, hnot P hP.2.2.1⟩
    classical
    have hm0 : m = 0 := by
      by_contra h
      exact (mem_support_iff.1 hm) (by rw [coeff_C, if_neg (Ne.symm h)])
    simp [hm0]
  have hnh : ¬ IsHorizontal W := fun h => hnot W h (by rwa [map_natCast])
  obtain ⟨h1, h2, h3⟩ := (GlobalTheory.CompanionTheory.Ar.PB.Known.divSuppArith K ι P D (oneLine (ι := ι)) (C (p : ℤ)) W hP hsec hW).2 hnh
  refine hK K ι W D a h1 h2.ne_zero h3 fun j W' hW' hWW' hdim => ?_
  exact ha j W' hW' (le_sup_left.trans (hle.trans hWW'))
    (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.charOf_eq_of_mem hW'.1 hp (hWW' hpW)) hdim

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem not_isHorizontal {W : Ideal (MRing ι)} (h : charOf W ≠ 0) : ¬ IsHorizontal W := by
  intro hW
  apply h
  have : Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι)) = 0 :=
    (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero _).1 hW
  simp [charOf, this]

end PositivityTheory.Xgp.lemma_v

theorem PositivityTheory.Xgp.t_lemma_v : Inputs → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (D : ℕ) (L : Fin D → HermLine ι) (A B : HermLine ι) (T : Finset ℕ) (α : ℕ → ℝ), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P (D + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSmoothHerm B → (∀ p ∈ T, p.Prime ∧ 0 ≤ α p) → VertClose P T α A B → (∀ p ∈ T, ∀ j, NefAt P p (L j).a) → |II K ι P (D + 1) (Fin.snoc L A) - II K ι P (D + 1) (Fin.snoc L B)| ≤ (∑ p ∈ T, α p * Real.log p) * ptsIntegral P (pot L) fun _ => 1 := by
  intro hIn II hII K _ ι _ P D L A B T α hP hL hA hB hT hV hnef
  classical
  obtain ⟨f, g, df, dg, hf, hg, hfP, hgP, hd, hn, hout, hin⟩ := hV
  rw [PositivityTheory.Xgp.lemma_v.sub_eq_cycR (hII.1 K ι) hP hL hA hB hf hg hfP hgP hd hn]
  set S : Finset (Ideal (MRing ι)) := (divSupp_finite P f).toFinset ∪ (divSupp_finite P g).toFinset ∪
    T.biUnion fun p => (divSupp_finite P (C (p : ℤ) : MRing ι)).toFinset with hS
  have hrhs : (∑ p ∈ T, α p * Real.log p) * ptsIntegral P (pot L) (fun _ => 1) =
      ∑ W ∈ S, ∑ p ∈ T, α p * Real.log p *
        ((divCycle P (C (p : ℤ)) W : ℝ) * (geoNum D W (fun j => (L j).a) : ℝ)) := by
    rw [Finset.sum_comm, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [hIn.degree K ι P D L p hP hL (hT p hp).1, PositivityTheory.Xgp.lemma_v.finsum_eq_sum P _ _ S, Finset.mul_sum]
    exact (Finset.subset_biUnion_of_mem (fun p : ℕ => (divSupp_finite P (C (p : ℤ) : MRing ι)).toFinset) hp).trans
      Finset.subset_union_right
  have hpos : ∀ W, ∀ p ∈ T, 0 ≤ (divCycle P (C (p : ℤ)) W : ℝ) * (geoNum D W (fun j => (L j).a) : ℝ) ∧
      (divCycle P (C (p : ℤ)) W : ℝ) * |(geoNum D W (fun j => (L j).a) : ℝ)| =
        (divCycle P (C (p : ℤ)) W : ℝ) * (geoNum D W (fun j => (L j).a) : ℝ) := by
    intro W p hp
    by_cases hW : W ∈ divSupp P (C (p : ℤ))
    · have h0 : (0 : ℝ) ≤ (geoNum D W (fun j => (L j).a) : ℝ) := by
        exact_mod_cast PositivityTheory.Xgp.lemma_v.geoNum_nonneg hIn.kleimanNef hP (hT p hp).1 (hnef p hp) hW
      exact ⟨mul_nonneg (Nat.cast_nonneg _) h0, by rw [abs_of_nonneg h0]⟩
    · rw [PositivityTheory.Xgp.lemma_v.divCycle_of_notMem hW]
      simp
  have hterm : ∀ W, ∀ p ∈ T, 0 ≤ α p * Real.log p *
      ((divCycle P (C (p : ℤ)) W : ℝ) * (geoNum D W (fun j => (L j).a) : ℝ)) := fun W p hp =>
    mul_nonneg (mul_nonneg (hT p hp).2 (Real.log_natCast_nonneg p)) (hpos W p hp).1
  rw [hrhs]
  unfold cycR
  rw [PositivityTheory.Xgp.lemma_v.finsum_eq_sum P f _ S (Finset.subset_union_left.trans Finset.subset_union_left),
    PositivityTheory.Xgp.lemma_v.finsum_eq_sum P g _ S (Finset.subset_union_right.trans Finset.subset_union_left),
    ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun W _ => ?_)
  rw [← sub_mul]
  by_cases hW : charOf W ∈ T
  · refine le_trans ?_ (Finset.single_le_sum (hterm W) hW)
    rw [if_neg (PositivityTheory.Xgp.lemma_v.not_isHorizontal (hT _ hW).1.ne_zero), abs_mul, abs_mul,
      abs_of_nonneg (Real.log_natCast_nonneg _), ← (hpos W _ hW).2]
    refine (mul_le_mul_of_nonneg_right (hin W hW)
      (mul_nonneg (abs_nonneg _) (Real.log_natCast_nonneg _))).trans (le_of_eq ?_)
    ring
  · rw [hout W hW, sub_self, zero_mul, abs_zero]
    exact Finset.sum_nonneg (hterm W)
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionVerticalPerturbationBound
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem lemma_v_lines : Inputs → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (D : ℕ) (L : Fin D → HermLine ι) (A B : HermLine ι) (T : Finset ℕ) (α : ℕ → ℝ), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P (D + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSmoothHerm B → (∀ p ∈ T, p.Prime ∧ 0 ≤ α p) → VertClose P T α A B → (∀ p ∈ T, ∀ j, NefAt P p (L j).a) → |II K ι P (D + 1) (Fin.snoc L A) - II K ι P (D + 1) (Fin.snoc L B)| ≤ (∑ p ∈ T, α p * Real.log p) * ptsIntegral P (pot L) fun _ => 1 :=
  @PositivityTheory.Xgp.t_lemma_v

end GlobalTheory.CompanionTheory.Ar.PB
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionVerticalPerturbationBoundStatement
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_vertical_perturbation_bound : Inputs → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (D : ℕ) (L : Fin D → HermLine ι) (A B : HermLine ι) (T : Finset ℕ) (α : ℕ → ℝ), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P (D + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSmoothHerm B → (∀ p ∈ T, p.Prime ∧ 0 ≤ α p) → VertClose P T α A B → (∀ p ∈ T, ∀ j, NefAt P p (L j).a) → |II K ι P (D + 1) (Fin.snoc L A) - II K ι P (D + 1) (Fin.snoc L B)| ≤ (∑ p ∈ T, α p * Real.log p) * ptsIntegral P (pot L) fun _ => 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.lemma_v_lines | exact GlobalTheory.CompanionTheory.Ar.PB.lemma_v_lines | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.lemma_v_lines <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreChartFifth
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreChartFifth
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem fibre_member_potential : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (X : Type) (q : Fin 2 → X → FA.S.X) (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → X) (l : Fin BM.q) (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X), IsOpen Un → IsFibreData FA τ a ca cb q Un Gn ΦYn ΦWn l H bp → ∀ (p : Ψ × Fin N) (z : Fin (d + 1) → ℂ), Fin.tail z ∈ Un → ∃ Hh : (Fin (d + 1) → ℂ) → ℂ, AnalyticAt ℂ Hh z ∧ ∀ᶠ z' in 𝓝 z, ((FA.S.comap some).potH p).φ (ΦYn z) (ΦYn z') = potAt BM l p (bp (Fin.tail z')) (flagAt H τ ca cb (z' 0) (Fin.tail z') p.1) + (Hh z').re := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a b ca cb hb hab hca hcb X q Un Gn ΦYn ΦWn l H bp hUn hF p z hz
  have hV : IsOpen {u : Fin (d + 1) → ℂ | Fin.tail u ∈ Un} := by
    have hc : Continuous (fun u : Fin (d + 1) → ℂ => (Fin.tail u : Fin d → ℂ)) :=
      continuous_pi fun i => continuous_apply _
    exact hUn.preimage hc
  obtain ⟨zex, hzan, hzex⟩ := GlobalTheory.T.two_point_fibre_chart_first K ι Φ y Ψ N j M n d BM FA τ a ca cb X q Un Gn ΦYn ΦWn l H bp hUn hF
  have hbij := GlobalTheory.T.realisation_bijective_degree_one K ι (d + 1) (Option (Ψ × Fin N)) FA.S (mCoordIdeal y) FA.Re FA.deg_one FA.br_empty
  obtain ⟨Hh, hHh, hev⟩ := GlobalTheory.T.local_holomorphic_lift_realisation K ι (d + 1) (Option (Ψ × Fin N)) FA.S (mCoordIdeal y) FA.Re (some p) (d + 1)
    {u : Fin (d + 1) → ℂ | Fin.tail u ∈ Un} ΦYn zex z FA.J_top FA.deg_one FA.br_empty hV hz hzan
    (fun u hu => (hzex u hu).1) (fun u hu x₀ hx => ((hzex u hu).2 x₀ hx).1)
  refine ⟨Hh, hHh, ?_⟩
  filter_upwards [hev, hV.mem_nhds hz] with z' h1 hz'
  obtain ⟨x₀, hx₀⟩ := hbij.2 (ΦYn z')
  obtain ⟨h2, h3, h4⟩ := (hzex z' hz').2 x₀ hx₀
  obtain ⟨hbO, hH⟩ := hF.2.2.2.1 _ hz'
  obtain ⟨hsb, hsd, -, -⟩ := GlobalTheory.T.elementary_factor_properties N j a b ca cb (z' 0) M.j_le hb hab hca hcb
  have hflag : IsBlockDiag j (flagAt H τ ca cb (z' 0) (Fin.tail z') p.1) ∧
      (flagAt H τ ca cb (z' 0) (Fin.tail z') p.1).det ≠ 0 := by
    unfold flagAt
    split_ifs with hp
    · subst hp
      refine ⟨(hH p.1).1.mul hsb, ?_⟩
      rw [Matrix.det_mul, hsd, mul_one]
      exact (hH p.1).2
    · exact hH p.1
  have hline := GlobalTheory.T.flag_analytic_orbit_off_boundary K ι Φ y Ψ N j M n d BM FA l x₀ (zex z') (bp (Fin.tail z')) p
    (flagAt H τ ca cb (z' 0) (Fin.tail z') p.1) hbO h2 h3 (h4 p.1 p.2) hflag.1 hflag.2
  have hphi : ((FA.S.comap some).potH p).φ (ΦYn z) (ΦYn z') =
      (FA.S.th (some p)).φ (ΦYn z) (ΦYn z') + FA.S.ph (some p) (ΦYn z') := rfl
  rw [hphi, h1, FA.ref_some, ← hline, hx₀]
  ring

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreChartFifthStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_point_fibre_chart_fifth : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (X : Type) (q : Fin 2 → X → FA.S.X) (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → X) (l : Fin BM.q) (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X), IsOpen Un → IsFibreData FA τ a ca cb q Un Gn ΦYn ΦWn l H bp → ∀ (p : Ψ × Fin N) (z : Fin (d + 1) → ℂ), Fin.tail z ∈ Un → ∃ Hh : (Fin (d + 1) → ℂ) → ℂ, AnalyticAt ℂ Hh z ∧ ∀ᶠ z' in 𝓝 z, ((FA.S.comap some).potH p).φ (ΦYn z) (ΦYn z') = potAt BM l p (bp (Fin.tail z')) (flagAt H τ ca cb (z' 0) (Fin.tail z') p.1) + (Hh z').re := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.fibre_member_potential | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.fibre_member_potential | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.fibre_member_potential <;> assumption)
end
end
