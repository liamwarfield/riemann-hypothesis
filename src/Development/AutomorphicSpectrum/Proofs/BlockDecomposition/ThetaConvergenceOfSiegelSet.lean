module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBoundFiniteInfinite
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatDoubledPairSchrodingerFunction
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaRapidDecaySiegelSet

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelSetCompactReduction
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSeriesSiegelBound
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSeriesSiegelBound
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CompanionTheory.WeilMaj

theorem schwartz_col_bound {T : Type} [Fintype T] {M n : ℕ} (f : SchwartzMap (T → Fin M → Fin n → ℂ) ℂ)
    (P : ℝ) (hP : 1 ≤ P) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : T → Fin M → Fin n → ℂ, ‖b‖ ≤ P * ‖a‖ →
      ‖f a‖ ≤ C * ∏ j : Fin n, ((1 + ‖fun τ i => b τ i j‖) ^ N)⁻¹ := by
  obtain ⟨C0, hC0, hC0'⟩ : ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ a, (1 + ‖a‖) ^ (N * n) * ‖f a‖ ≤ C0 := by
    refine ⟨(2 : ℝ) ^ (N * n, 0).1 * ((Finset.Iic (N * n, 0)).sup fun m => SchwartzMap.seminorm ℂ m.1 m.2) f,
      by positivity, fun a => ?_⟩
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (N * n, 0)) (k := N * n) (n := 0)
      le_rfl le_rfl f a
    simpa using h
  refine ⟨C0 * P ^ (N * n), by positivity, fun a b hab => ?_⟩
  have hP0 : 0 < P := by linarith
  have ha : 0 < 1 + ‖a‖ := by positivity
  have hb : 0 < 1 + ‖b‖ := by positivity
  have h1 : 1 + ‖b‖ ≤ P * (1 + ‖a‖) := by nlinarith [norm_nonneg a]
  have hcol : ∀ j, ‖fun τ i => b τ i j‖ ≤ ‖b‖ := fun j => by
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun τ => ?_
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
    exact (norm_le_pi_norm (b τ i) j).trans ((norm_le_pi_norm (b τ) i).trans (norm_le_pi_norm b τ))
  have h2 : ((1 + ‖b‖) ^ (N * n))⁻¹ ≤ ∏ j : Fin n, ((1 + ‖fun τ i => b τ i j‖) ^ N)⁻¹ := by
    have e : ((1 + ‖b‖) ^ (N * n))⁻¹ = ∏ _j : Fin n, ((1 + ‖b‖) ^ N)⁻¹ := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, inv_pow, pow_mul]
    rw [e]
    refine Finset.prod_le_prod₀ (fun _ _ => by positivity) fun j _ => ?_
    have : 0 < 1 + ‖fun τ i => b τ i j‖ := by positivity
    refine inv_anti₀ (by positivity) (pow_le_pow_left₀ this.le ?_ N)
    linarith [hcol j]
  have h3 : ‖f a‖ ≤ C0 * ((1 + ‖a‖) ^ (N * n))⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm]
    exact hC0' a
  have h4 : ((1 + ‖a‖) ^ (N * n))⁻¹ ≤ P ^ (N * n) * ((1 + ‖b‖) ^ (N * n))⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_le_iff₀ (by positivity), ← mul_pow, mul_comm (1 + ‖a‖)]
    exact pow_le_pow_left₀ hb.le h1 _
  calc ‖f a‖ ≤ C0 * ((1 + ‖a‖) ^ (N * n))⁻¹ := h3
    _ ≤ C0 * (P ^ (N * n) * ((1 + ‖b‖) ^ (N * n))⁻¹) := by gcongr
    _ = C0 * P ^ (N * n) * ((1 + ‖b‖) ^ (N * n))⁻¹ := by ring
    _ ≤ _ := by gcongr

variable {D : D7}

theorem mt_mul_inv (V : HSp D) (y : GA D V) :
    (HMul.hMul (Formalism.L2.Theta.mt V y) (Formalism.L2.Theta.mt V y⁻¹) : Matrix (Fin V.rank) (Fin V.rank) (AE D)) = 1 := by
  have h : (Formalism.L2.Theta.matHom V y) * (Formalism.L2.Theta.matHom V y⁻¹) = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  exact congrArg Units.val h

theorem compAt_mul' (θ : InfFam D) (τ : D.what₂.Tau) {k m n : ℕ} (x : Mx D k m) (y : Mx D m n) :
    compAt θ τ (HMul.hMul x y : Mx D k n) = HMul.hMul (compAt θ τ x) (compAt θ τ y) :=
  Matrix.map_mul (f := (θ τ).comp (infPart D))

theorem real_compare {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (n : ℕ) (C₁ : Set (GA D V)) (hC₁ : IsCompact C₁) :
    ∃ P : ℝ, 1 ≤ P ∧ ∀ y ∈ C₁, ∀ x : Mx D V.rank n,
      ‖(fun τ i j => compAt θ τ x i j : D.what₂.Tau → Fin V.rank → Fin n → ℂ)‖ ≤
        P * ‖(fun τ i j => compAt θ τ (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) i j :
          D.what₂.Tau → Fin V.rank → Fin n → ℂ)‖ := by
  let B : GA D V → (D.what₂.Tau → Fin V.rank → Fin V.rank → ℂ) := fun y τ i k => compAt θ τ (Formalism.L2.Theta.mt V y) i k
  have hB : Continuous B := by
    refine continuous_pi fun τ => continuous_pi fun i => continuous_pi fun k => ?_
    exact ((GlobalTheory.RealWeil.continuous_compAt hθ τ _ _).comp (GlobalTheory.RealWeil.continuous_mt V).1).matrix_elem i k
  obtain ⟨R, hR⟩ := hC₁.exists_bound_of_continuousOn hB.continuousOn
  refine ⟨1 + V.rank * |R|, by have := abs_nonneg R; nlinarith [Nat.cast_nonneg (α := ℝ) V.rank, mul_nonneg (Nat.cast_nonneg (α := ℝ) V.rank) (abs_nonneg R)], fun y hy x => ?_⟩
  set u : D.what₂.Tau → Fin V.rank → Fin n → ℂ :=
    fun τ i j => compAt θ τ (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) i j with hu
  have hx : ∀ τ, compAt θ τ x = HMul.hMul (compAt θ τ (Formalism.L2.Theta.mt V y))
      (compAt θ τ (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n)) := fun τ => by
    rw [← compAt_mul', ← Matrix.mul_assoc, mt_mul_inv, Matrix.one_mul]
  have hN : 0 ≤ (1 + V.rank * |R|) * ‖u‖ := by positivity
  refine (pi_norm_le_iff_of_nonneg hN).2 fun τ => (pi_norm_le_iff_of_nonneg hN).2 fun i =>
    (pi_norm_le_iff_of_nonneg hN).2 fun j => ?_
  rw [hx τ, Matrix.mul_apply]
  have hk : ∀ k, ‖compAt θ τ (Formalism.L2.Theta.mt V y) i k * compAt θ τ (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) k j‖ ≤ |R| * ‖u‖ := fun k => by
    rw [norm_mul]
    have e1 : ‖compAt θ τ (Formalism.L2.Theta.mt V y) i k‖ ≤ |R| :=
      ((norm_le_pi_norm (B y τ i) k).trans ((norm_le_pi_norm (B y τ) i).trans (norm_le_pi_norm (B y) τ))).trans
        ((hR y hy).trans (le_abs_self R))
    have e2 : ‖compAt θ τ (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) k j‖ ≤ ‖u‖ :=
      (norm_le_pi_norm (u τ k) j).trans ((norm_le_pi_norm (u τ) k).trans (norm_le_pi_norm u τ))
    exact mul_le_mul e1 e2 (norm_nonneg _) (abs_nonneg _)
  calc _ ≤ ∑ k, ‖compAt θ τ (Formalism.L2.Theta.mt V y) i k * compAt θ τ (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) k j‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin V.rank, |R| * ‖u‖ := Finset.sum_le_sum fun k _ => hk k
    _ = V.rank * |R| * ‖u‖ := by simp [Finset.sum_const, mul_assoc]
    _ ≤ _ := by nlinarith [norm_nonneg u]


set_option synthInstance.maxHeartbeats 400000 in
theorem finite_compare (V : HSp D) (n : ℕ)
    (g : (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ)
    (hg : g ∈ GlobalTheory.WeilM.SB (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E))
    (C₁ : Set (GA D V)) (hC₁ : IsCompact C₁) :
    ∃ L : Set (Matrix (Fin V.rank) (Fin 1) (Af D.host.F ⊗[D.host.F] D.host.E)), IsCompact L ∧
      ∀ y ∈ C₁, ∀ x : Mx D V.rank n,
        g (fun i j => finPart D ((HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) i j)) ≠ 0 →
        ∀ j, (Matrix.of fun i' (_ : Fin 1) => finPart D (x i' j)) ∈ L := by
  haveI : IsTopologicalRing (Af D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.isTopologicalRing (Af D.host.F) _
  have hS : IsCompact (tsupport g) := hg.2
  let Φ : GA D V × (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) →
      (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) :=
    fun p i j => ∑ k, finPart D (Formalism.L2.Theta.mt V p.1 i k) * p.2 k j
  have hΦ : Continuous Φ := by
    refine continuous_pi fun i => continuous_pi fun j => continuous_finsetSum _ fun k _ => ?_
    refine Continuous.mul ?_ ?_
    · exact GlobalTheory.SchwartzSch.continuous_finPart'.comp
        (((GlobalTheory.RealWeil.continuous_mt V).1.comp continuous_fst).matrix_elem i k)
    · exact (continuous_apply j).comp ((continuous_apply k).comp continuous_snd)
  have hK := (hC₁.prod hS).image hΦ
  let col : Fin n → (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) →
      Matrix (Fin V.rank) (Fin 1) (Af D.host.F ⊗[D.host.F] D.host.E) :=
    fun j w => Matrix.of fun i' _ => w i' j
  have hcol : ∀ j, Continuous (col j) := fun j =>
    continuous_pi fun i => continuous_pi fun _ => (continuous_apply j).comp (continuous_apply i)
  refine ⟨⋃ j, col j '' (Φ '' (C₁ ×ˢ tsupport g)), isCompact_iUnion fun j => hK.image (hcol j),
    fun y hy x hne j => Set.mem_iUnion.2 ⟨j, fun i j => finPart D (x i j),
      ⟨(y, fun i j => finPart D ((HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) i j)),
        ⟨hy, subset_tsupport _ hne⟩, ?_⟩, rfl⟩⟩
  funext i j
  have e : (HMul.hMul (Formalism.L2.Theta.mt V y) (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) : Mx D V.rank n) = x := by
    rw [← Matrix.mul_assoc, mt_mul_inv, Matrix.one_mul]
  have e2 := congrFun (congrFun e i) j
  rw [Matrix.mul_apply] at e2
  show ∑ k, finPart D (Formalism.L2.Theta.mt V y i k) * finPart D _ = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← e2, map_sum]
  exact Finset.sum_congr rfl fun k _ => ((finPart D).map_mul _ _).symm

theorem schwartz_translate_majorant : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (n : ℕ) (f : SchwartzMap (D.what₂.Tau → Fin V.rank → Fin n → ℂ) ℂ) (g : (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ), g ∈ GlobalTheory.WeilM.SB (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ∀ (C₁ : Set (GA D V)), IsCompact C₁ → ∀ N : ℕ, ∃ (C : ℝ) (L : Set (Matrix (Fin V.rank) (Fin 1) (Af D.host.F ⊗[D.host.F] D.host.E))), IsCompact L ∧ ∀ y ∈ C₁, ∀ x : Mx D V.rank n, ‖f (fun τ i j => compAt θ τ (HMul.hMul (mt V y⁻¹) x : Matrix (Fin V.rank) (Fin n) (AE D)) i j) * g (fun i j => finPart D ((HMul.hMul (mt V y⁻¹) x : Matrix (Fin V.rank) (Fin n) (AE D)) i j))‖ₑ ≤ ENNReal.ofReal C * ∏ j : Fin n, ENNReal.ofReal (((1 + ‖fun τ i => compAt θ τ (Matrix.of fun i' (_ : Fin 1) => x i' j) i 0‖) ^ N)⁻¹ * Set.indicator L (fun _ => (1 : ℝ)) (Matrix.of fun i' (_ : Fin 1) => finPart D (x i' j))) := by
  intro D θ hθ V n f g hg C₁ hC₁ N
  obtain ⟨P, hP, hPx⟩ := real_compare hθ V n C₁ hC₁
  obtain ⟨C, hC, hf⟩ := schwartz_col_bound f P hP N
  obtain ⟨L, hL, hLx⟩ := finite_compare V n g hg C₁ hC₁
  obtain ⟨G, hG⟩ := hg.1.continuous.bounded_above_of_compact_support hg.2
  refine ⟨C * |G|, L, hL, fun y hy x => ?_⟩
  by_cases h0 : g (fun i j => finPart D ((HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) i j)) = 0
  · have e : ∀ a : ℂ, ‖a * g (fun i j => finPart D ((HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) i j))‖ₑ = 0 := fun a => by
      rw [h0, mul_zero, enorm_zero]
    exact (e _).le.trans zero_le
  · have hm := hLx y hy x h0
    have hb := hf _ _ (hPx y hy x)
    have hterm : ∀ j : Fin n, 0 ≤ ((1 + ‖fun τ i => compAt θ τ (Matrix.of fun i' (_ : Fin 1) => x i' j) i 0‖) ^ N)⁻¹ *
        Set.indicator L (fun _ => (1 : ℝ)) (Matrix.of fun i' (_ : Fin 1) => finPart D (x i' j)) := fun j => by
      rw [Set.indicator_of_mem (hm j)]
      positivity
    rw [← ENNReal.ofReal_prod_of_nonneg fun j _ => hterm j,
      ← ENNReal.ofReal_mul (mul_nonneg hC (abs_nonneg G)), ← ofReal_norm_eq_enorm]
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [Set.indicator_of_mem (hm _), mul_one]
    rw [norm_mul]
    calc _ ≤ (C * ∏ j : Fin n, ((1 + ‖fun τ i => compAt θ τ (Matrix.of fun i' (_ : Fin 1) => x i' j) i 0‖) ^ N)⁻¹) * |G| :=
          mul_le_mul hb ((hG _).trans (le_abs_self G)) (norm_nonneg _)
            (mul_nonneg hC (Finset.prod_nonneg fun j _ => by positivity))
      _ = _ := by ring

end GlobalTheory.CompanionTheory.WeilMaj
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSeriesSiegelBoundStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_series_siegel_bound : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (n : ℕ) (f : SchwartzMap (D.what₂.Tau → Fin V.rank → Fin n → ℂ) ℂ) (g : (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ), g ∈ GlobalTheory.WeilM.SB (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ∀ (C₁ : Set (GA D V)), IsCompact C₁ → ∀ N : ℕ, ∃ (C : ℝ) (L : Set (Matrix (Fin V.rank) (Fin 1) (Af D.host.F ⊗[D.host.F] D.host.E))), IsCompact L ∧ ∀ y ∈ C₁, ∀ x : Mx D V.rank n, ‖f (fun τ i j => compAt θ τ (HMul.hMul (mt V y⁻¹) x : Matrix (Fin V.rank) (Fin n) (AE D)) i j) * g (fun i j => finPart D ((HMul.hMul (mt V y⁻¹) x : Matrix (Fin V.rank) (Fin n) (AE D)) i j))‖ₑ ≤ ENNReal.ofReal C * ∏ j : Fin n, ENNReal.ofReal (((1 + ‖fun τ i => compAt θ τ (Matrix.of fun i' (_ : Fin 1) => x i' j) i 0‖) ^ N)⁻¹ * Set.indicator L (fun _ => (1 : ℝ)) (Matrix.of fun i' (_ : Fin 1) => finPart D (x i' j))) := by
  first | exact @GlobalTheory.CompanionTheory.WeilMaj.schwartz_translate_majorant | exact GlobalTheory.CompanionTheory.WeilMaj.schwartz_translate_majorant | (intros; apply GlobalTheory.CompanionTheory.WeilMaj.schwartz_translate_majorant <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsThetaLePowOfColProd
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.ColProd

theorem tsum_pow_fin {α : Type*} (f : α → ℝ≥0∞) (n : ℕ) :
    ∑' g : Fin n → α, ∏ j, f (g j) = (∑' v, f v) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← Equiv.tsum_eq (Fin.consEquiv (fun _ : Fin (n + 1) => α))]
    simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [ENNReal.tsum_prod (f := fun a (g : Fin n → α) => f a * ∏ i, f (g i))]
    simp_rw [ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_mul_right, ih, pow_succ']

theorem absTheta_le_pow_of_colProd : ∀ (D : D7) (V : HSp D) {n : ℕ} (φ : Mx D V.rank n → ℂ) (ρ : Mx D V.rank 1 → ℝ≥0∞) (C : ℝ≥0∞) (y : GA D V), (∀ x : Mx D V.rank n, ‖φ (HMul.hMul (mt V y⁻¹) x : Matrix (Fin V.rank) (Fin n) (AE D))‖ₑ ≤ C * ∏ j : Fin n, ρ (fun i (_ : Fin 1) => x i j)) → ∀ a : GA D V, absTheta V φ (a * y) ≤ C * (∑' ξ : Matrix (Fin V.rank) (Fin 1) D.host.E, ρ (invPt V a ξ)) ^ n := by
  intro D V n φ ρ C y hφ a
  have hstep : ∀ ξ : Matrix (Fin V.rank) (Fin n) D.host.E,
      ‖φ (invPt V (a * y) ξ)‖ₑ ≤ C * ∏ j : Fin n, ρ (invPt V a (fun i (_ : Fin 1) => ξ i j)) := by
    intro ξ
    have h1 : invPt V (a * y) ξ =
        (HMul.hMul (mt V y⁻¹) (invPt V a ξ) : Matrix (Fin V.rank) (Fin n) (AE D)) := by
      simp only [invPt, mul_inv_rev, Formalism.L2.Theta.mt, map_mul, Units.val_mul, Matrix.mul_assoc]
    rw [h1]
    refine (hφ (invPt V a ξ)).trans (le_of_eq ?_)
    congr 1
  let e : (Fin n → Matrix (Fin V.rank) (Fin 1) D.host.E) ≃ Matrix (Fin V.rank) (Fin n) D.host.E :=
    { toFun := fun g i j => g j i 0
      invFun := fun ξ j i _ => ξ i j
      left_inv := fun g => by
        funext j i u
        show g j i 0 = g j i u
        rw [Fin.fin_one_eq_zero u]
      right_inv := fun ξ => by rfl }
  calc absTheta V φ (a * y)
      = ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, ‖φ (invPt V (a * y) ξ)‖ₑ := by rfl
    _ ≤ ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E,
          C * ∏ j : Fin n, ρ (invPt V a (fun i (_ : Fin 1) => ξ i j)) := ENNReal.tsum_le_tsum hstep
    _ = C * ∑' g : Fin n → Matrix (Fin V.rank) (Fin 1) D.host.E, ∏ j : Fin n, ρ (invPt V a (g j)) := by
        rw [ENNReal.tsum_mul_left, ← Equiv.tsum_eq e]
        congr 1
        refine tsum_congr (fun g => Finset.prod_congr rfl (fun j _ => ?_))
        congr 2
        funext i u
        show g j i 0 = g j i u
        rw [Fin.fin_one_eq_zero u]
    _ = C * (∑' ξ : Matrix (Fin V.rank) (Fin 1) D.host.E, ρ (invPt V a ξ)) ^ n := by
        rw [tsum_pow_fin (fun v => ρ (invPt V a v)) n]

end GlobalTheory.CompanionTheory.ColProd
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelSetCompactReduction
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Pointwise

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelTheta

def colMajorant {D : D7} (θ : InfFam D) (m : ℕ) (L : Set (Matrix (Fin m) (Fin 1) (Af D.host.F ⊗[D.host.F] D.host.E)))
    (N : ℕ) (v : Mx D m 1) : ℝ≥0∞ :=
  ENNReal.ofReal (((1 + ‖fun τ i => compAt θ τ v i 0‖) ^ N)⁻¹ *
    Set.indicator L (fun _ => (1 : ℝ)) (v.map (finPart D)))

def pureT {D : D7} (θ : InfFam D) {m n : ℕ} (f : SchwartzMap (D.what₂.Tau → Fin m → Fin n → ℂ) ℂ)
    (g : (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ) (x : Mx D m n) : ℂ :=
  f (fun τ i j => compAt θ τ x i j) * g (fun i j => finPart D (x i j))

theorem pure_le_colMajorant (D : D7) (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) (n : ℕ)
    (f : SchwartzMap (D.what₂.Tau → Fin V.rank → Fin n → ℂ) ℂ)
    (g : (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ)
    (hg : g ∈ GlobalTheory.WeilM.SB (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E))
    (C₁ : Set (GA D V)) (hC₁ : IsCompact C₁) :
    ∃ L : Set (Matrix (Fin V.rank) (Fin 1) (Af D.host.F ⊗[D.host.F] D.host.E)), IsCompact L ∧ ∀ N : ℕ, ∃ C : ℝ,
      ∀ y ∈ C₁, ∀ x : Mx D V.rank n,
        ‖pureT θ f g (HMul.hMul (mt V y⁻¹) x : Matrix (Fin V.rank) (Fin n) (AE D))‖ₑ ≤
          ENNReal.ofReal C * ∏ j : Fin n, colMajorant θ V.rank L N (fun i (_ : Fin 1) => x i j) := by
  obtain ⟨C0, L, hL, h0⟩ := GlobalTheory.T.theta_series_siegel_bound D θ hθ V n f g hg C₁ hC₁ 0
  refine ⟨L, hL, fun N => ?_⟩
  obtain ⟨CN, LN, -, hN⟩ := GlobalTheory.T.theta_series_siegel_bound D θ hθ V n f g hg C₁ hC₁ N
  refine ⟨CN, fun y hy x => ?_⟩
  by_cases hall : ∀ j : Fin n, (Matrix.of fun i' (_ : Fin 1) => finPart D (x i' j)) ∈ L
  · refine (hN y hy x).trans ?_
    gcongr with j _
    unfold colMajorant
    refine ENNReal.ofReal_le_ofReal ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h1 : Set.indicator L (fun _ => (1 : ℝ)) (Matrix.of fun i' (_ : Fin 1) => finPart D (x i' j)) = 1 :=
      Set.indicator_of_mem (hall j) _
    refine le_trans ?_ (le_of_eq h1.symm)
    exact Set.indicator_le_self' (fun _ _ => zero_le_one) _ |>.trans le_rfl
  · push_neg at hall
    obtain ⟨j, hj⟩ := hall
    have hz : ‖pureT θ f g (HMul.hMul (mt V y⁻¹) x : Matrix (Fin V.rank) (Fin n) (AE D))‖ₑ = 0 := by
      refine le_antisymm ((h0 y hy x).trans (le_of_eq ?_)) bot_le
      rw [Finset.prod_eq_zero (Finset.mem_univ j), mul_zero]
      rw [Set.indicator_of_notMem hj, mul_zero, ENNReal.ofReal_zero]
    rw [hz]
    exact bot_le

theorem absTheta_pure_le (D : D7) (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) (n : ℕ)
    (f : SchwartzMap (D.what₂.Tau → Fin V.rank → Fin n → ℂ) ℂ)
    (g : (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ)
    (hg : g ∈ GlobalTheory.WeilM.SB (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E))
    {r : ℕ} (Xf Yf : Matrix (Fin V.rank) (Fin r) D.host.E)
    (hW : GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram Xf Yf) {c : ℝ} (hc : 0 < c)
    (C₁ : Set (GA D V)) (hC₁ : IsCompact C₁) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ C₁, ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∀ a,
      GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig V.gram Xf Yf t a →
      absTheta V (pureT θ f g) (a * y) ≤
        ENNReal.ofReal (C * ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) := by
  obtain ⟨L, hL, hmaj⟩ := pure_le_colMajorant D θ hθ V n f g hg C₁ hC₁
  obtain ⟨N₀, hcount⟩ := GlobalTheory.T.theta_rapid_decay_siegel_set D θ hθ V Xf Yf hW hc L hL
  obtain ⟨C', hC'⟩ := hcount N₀ le_rfl
  obtain ⟨C, hC⟩ := hmaj N₀
  refine ⟨max C 0 * max C' 0 ^ n, by positivity, fun y hy t ht a ha => ?_⟩
  have h1 := GlobalTheory.CompanionTheory.ColProd.absTheta_le_pow_of_colProd D V (pureT θ f g) (colMajorant θ V.rank L N₀)
    (ENNReal.ofReal C) y (hC y hy) a
  have hP : 0 ≤ ∏ i, t i ^ (2 * Module.finrank ℚ D.host.F) :=
    Finset.prod_nonneg fun i _ => pow_nonneg (ht.1 i).le _
  have h2 : ∑' ξ : Matrix (Fin V.rank) (Fin 1) D.host.E, colMajorant θ V.rank L N₀ (invPt V a ξ) ≤
      ENNReal.ofReal (max C' 0 * ∏ i, t i ^ (2 * Module.finrank ℚ D.host.F)) :=
    (hC' t ht a ha).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hP))
  have hpow : (∏ i, t i ^ (2 * Module.finrank ℚ D.host.F)) ^ n =
      ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n)) := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← pow_mul]
    congr 1
    ring
  calc absTheta V (pureT θ f g) (a * y)
      ≤ ENNReal.ofReal C * (∑' ξ : Matrix (Fin V.rank) (Fin 1) D.host.E, colMajorant θ V.rank L N₀ (invPt V a ξ)) ^ n := h1
    _ ≤ ENNReal.ofReal (max C 0) * ENNReal.ofReal (max C' 0 * ∏ i, t i ^ (2 * Module.finrank ℚ D.host.F)) ^ n := by
        gcongr
        exact le_max_left _ _
    _ = ENNReal.ofReal (max C 0 * max C' 0 ^ n * ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) := by
        rw [← ENNReal.ofReal_pow (mul_nonneg (le_max_right _ _) hP),
          ← ENNReal.ofReal_mul (le_max_right _ _), mul_pow, hpow, mul_assoc]

theorem absTheta_le_torus : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (n : ℕ) (Φ : Mx D V.rank n → ℂ), Φ ∈ schwartzA θ V.rank n → ∀ {r : ℕ} (Xf Yf : Matrix (Fin V.rank) (Fin r) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram Xf Yf → ∀ (Ω C₀ : Set (GA D V)) (K : Subgroup (GA D V)) (c : ℝ), IsCompact Ω → IsCompact C₀ → IsCompact (K : Set (GA D V)) → 0 < c → (∀ p ∈ Ω, ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∀ a, GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig V.gram Xf Yf t a → a⁻¹ * p * a ∈ C₀) → ∃ C : ℝ, ∀ p ∈ Ω, ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∀ a, GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig V.gram Xf Yf t a → ∀ k ∈ K, absTheta V Φ (p * a * k) ≤ ENNReal.ofReal (C * ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) := by
  intro D θ hθ V n Φ hΦ r Xf Yf hW Ω C₀ K c hΩ hC₀ hK hc hsub
  have hC₁ : IsCompact (C₀ * (K : Set (GA D V))) := hC₀.mul hK
  obtain ⟨-, m, f, g, hg, hdom⟩ := GlobalTheory.T.schwartz_bound_finite_infinite D θ hθ V.rank n Φ hΦ
  have key := fun i => absTheta_pure_le D θ hθ V n (f i) (g i) (hg i) Xf Yf hW hc _ hC₁
  choose Ci hCi0 hCi using key
  refine ⟨∑ i, Ci i, fun p hp t ht a ha k hk => ?_⟩
  have hy : a⁻¹ * p * a * k ∈ C₀ * (K : Set (GA D V)) := Set.mul_mem_mul (hsub p hp t ht a ha) hk
  have hsplit : p * a * k = a * (a⁻¹ * p * a * k) := by group
  have hP : 0 ≤ ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n)) :=
    Finset.prod_nonneg fun i _ => pow_nonneg (ht.1 i).le _
  rw [hsplit]
  calc absTheta V Φ (a * (a⁻¹ * p * a * k))
      ≤ ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, ∑ i, ‖pureT θ (f i) (g i) (invPt V (a * (a⁻¹ * p * a * k)) ξ)‖ₑ :=
        ENNReal.tsum_le_tsum fun ξ => hdom _
    _ = ∑ i, absTheta V (pureT θ (f i) (g i)) (a * (a⁻¹ * p * a * k)) :=
        Summable.tsum_finsetSum fun _ _ => ENNReal.summable
    _ ≤ ∑ i, ENNReal.ofReal (Ci i * ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) :=
        Finset.sum_le_sum fun i _ => hCi i _ hy t ht a ha
    _ = ENNReal.ofReal ((∑ i, Ci i) * ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) := by
        rw [Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg fun i _ => mul_nonneg (hCi0 i) hP]

end GlobalTheory.CompanionTheory.SiegelTheta
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelSetCompactReductionStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_set_compact_reduction : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (n : ℕ) (Φ : Mx D V.rank n → ℂ), Φ ∈ schwartzA θ V.rank n → ∀ {r : ℕ} (Xf Yf : Matrix (Fin V.rank) (Fin r) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram Xf Yf → ∀ (Ω C₀ : Set (GA D V)) (K : Subgroup (GA D V)) (c : ℝ), IsCompact Ω → IsCompact C₀ → IsCompact (K : Set (GA D V)) → 0 < c → (∀ p ∈ Ω, ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∀ a, GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig V.gram Xf Yf t a → a⁻¹ * p * a ∈ C₀) → ∃ C : ℝ, ∀ p ∈ Ω, ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∀ a, GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig V.gram Xf Yf t a → ∀ k ∈ K, absTheta V Φ (p * a * k) ≤ ENNReal.ofReal (C * ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelTheta.absTheta_le_torus | exact GlobalTheory.CompanionTheory.SiegelTheta.absTheta_le_torus | (intros; apply GlobalTheory.CompanionTheory.SiegelTheta.absTheta_le_torus <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaIntegralLeFundamentalSet
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaIntegralLeFundamentalSet
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilConv

theorem absThetaInt_le_of_meets_orbits (D : D7) (V : HSp D) (ν : Measure (GA D V)) (hν : ν.IsHaarMeasure) {n : ℕ}
    (φ : Mx D V.rank n → ℂ) (hφ : Continuous φ) (S : Set (GA D V)) (hS : MeasurableSet S)
    (hcov : ∀ g, ∃ γ ∈ GQ V, γ * g ∈ S) : absThetaInt V ν φ ≤ ∫⁻ g in S, absTheta V φ g ∂ν := by
  have hinv := leftInv_absTheta V φ
  have hfd : IsFundamentalDomain (GQ V) (stdDom (GQ V)) ν := isFundamentalDomain_stdDom _ ν
  have e : absThetaInt V ν φ = ∫⁻ g in stdDom (GQ V), absTheta V φ g ∂ν := by
    unfold absThetaInt
    show ∫⁻ q, descend (GQ V) (absTheta V φ) q ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure (GQ V) ν = _
    rw [GlobalTheory.AutomorphicL2Unitary.lintegral_quotMeasure hfd]
    exact lintegral_congr fun g => congrFun hinv.lift_descend g
  rw [e]
  exact GlobalTheory.lintegral_fundamentalDomain_le_of_meets_orbits (GQ V) ν hfd hS hcov (GlobalTheory.AbsThetaSemi.measurable_absTheta V hφ) hinv

end GlobalTheory.CompanionTheory.WeilConv

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaIntegralLeFundamentalSetStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_integral_le_fundamental_set : ∀ (D : D7) (V : HSp D) (ν : Measure (GA D V)), ν.IsHaarMeasure → ∀ {n : ℕ} (φ : Mx D V.rank n → ℂ), Continuous φ → ∀ S : Set (GA D V), MeasurableSet S → (∀ g, ∃ γ ∈ GQ V, γ * g ∈ S) → absThetaInt V ν φ ≤ ∫⁻ g in S, absTheta V φ g ∂ν := by
  first | exact @GlobalTheory.CompanionTheory.WeilConv.absThetaInt_le_of_meets_orbits | exact GlobalTheory.CompanionTheory.WeilConv.absThetaInt_le_of_meets_orbits | (intros; apply GlobalTheory.CompanionTheory.WeilConv.absThetaInt_le_of_meets_orbits <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittFrameRankLeWittIndex
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittFrameRankLeWittIndex
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.WittFrame

open Matrix

theorem length_le_wittIdx (D : D7) (V : HSp D) {r : ℕ} (Xf Yf : Matrix (Fin V.rank) (Fin r) D.host.E)
    (hW : GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram Xf Yf) : r ≤ Formalism.MainNotions.SchurIrreducible.wittIdx V := by
  have hc : ∀ {a : ℕ} (A : Matrix (Fin V.rank) (Fin a) D.host.E),
      Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) A = Aᴴ := by
    intro a A
    exact Matrix.ext fun i j => rfl
  have hxx : Xfᴴ * V.gram * Xf = 0 := by rw [← hc]; exact hW.xx
  have hxy : Xfᴴ * V.gram * Yf = 1 := by rw [← hc]; exact hW.xy
  have hG : V.gramᴴ = V.gram := by
    refine Matrix.ext fun a b => ?_
    exact V.herm.eq _ _
  have hyx : Yfᴴ * V.gram * Xf = 1 := by
    have h := congrArg conjTranspose hxy
    simpa [conjTranspose_mul, hG, Matrix.mul_assoc] using h
  let f : (Fin r → D.host.E) →ₗ[D.host.E] V.V := V.frame.equivFun.symm.toLinearMap.comp Xf.mulVecLin
  have hf : Function.Injective f := by
    refine V.frame.equivFun.symm.injective.comp (g := V.frame.equivFun.symm) (f := Xf.mulVec) fun v w hvw => ?_
    have := congrArg (Yfᴴ * V.gram).mulVec hvw
    simpa [mulVec_mulVec, hyx] using this
  refine le_csSup (GlobalTheory.SiegelFormula.Model.bddAbove_witt V) ⟨LinearMap.range f, by simpa using LinearMap.finrank_range_of_inj hf, ?_⟩
  rintro _ ⟨v, rfl⟩ _ ⟨w, rfl⟩
  change V.hT (V.frame.equivFun.symm (Xf *ᵥ v)) (V.frame.equivFun.symm (Xf *ᵥ w)) = 0
  rw [GlobalTheory.ParallelWitt.form_eq, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hxx]
  simp

end GlobalTheory.CompanionTheory.WittFrame
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittFrameRankLeWittIndexStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_frame_rank_le_witt_index : ∀ (D : D7) (V : HSp D) {r : ℕ} (Xf Yf : Matrix (Fin V.rank) (Fin r) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram Xf Yf → r ≤ Formalism.MainNotions.SchurIrreducible.wittIdx V := by
  first | exact @GlobalTheory.CompanionTheory.WittFrame.length_le_wittIdx | exact GlobalTheory.CompanionTheory.WittFrame.length_le_wittIdx | (intros; apply GlobalTheory.CompanionTheory.WittFrame.length_le_wittIdx <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeIntegralZeroVarsLtTop
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SiegelCone

theorem cone_integral_zero_vars_lt_top :
    ∀ (F : Type) [Field F] [NumberField F] (n d : ℕ) (c : ℝ),
      ∫⁻ t in GlobalTheory.SiegelSet.cone 0 c, ENNReal.ofReal (∏ i, t i ^ (Module.finrank ℚ F * d)) *
        ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus F n t * ∏ i, t i)⁻¹) < ⊤ := by
  intro F _ _ n d c
  have h : ∀ t : Fin 0 → ℝ, ENNReal.ofReal (∏ i, t i ^ (Module.finrank ℚ F * d)) *
      ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus F n t * ∏ i, t i)⁻¹) = 1 := by
    intro t
    simp [GlobalTheory.SiegelSet.modulus]
  simp_rw [h]
  rw [setLIntegral_const, one_mul]
  exact measure_lt_top _ _

end GlobalTheory.CompanionTheory.SiegelCone
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaConvergenceOfSiegelSet
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.WeilTheta

theorem weilThetaConvergence_of_siegelSet (hRT : GlobalTheory.Published.SiegelSetUnitary) : GlobalTheory.Published.WeilThetaConvergence := by
  intro D n V _hn hV θ hθ ν hν Φ
  obtain ⟨hcontΦ, -⟩ := GlobalTheory.T.schwartz_bound_finite_infinite D θ hθ V.rank n Φ.1 Φ.2
  obtain ⟨r, Xf, Yf, hW⟩ := GlobalTheory.SiegelSet.exists_isWittFrame (GlobalTheory.AdelicU.isCMExt_host D) (isHermND_gram V)
  obtain ⟨K, Ω, c, hK, hΩ, -, hc, -, hcl, hcov, ⟨C₀, hC₀, hconj⟩, hmeas, -, -⟩ :=
    hRT D.host.F D.host.E D.sp.cm.sig (GlobalTheory.AdelicU.isCMExt_host D) V.rank V.gram (isHermND_gram V) r Xf Yf hW
  obtain ⟨-, C₁, hC₁⟩ := hmeas ν hν
  obtain ⟨C, hC⟩ := GlobalTheory.T.siegel_set_compact_reduction D θ hθ V n Φ.1 Φ.2 Xf Yf hW Ω C₀ K c hΩ hC₀ hK hc hconj
  set S := GlobalTheory.SiegelSet.siegelSet D.sp.cm.sig V.gram Xf Yf Ω c K with hSdef
  have hSm : MeasurableSet S := hcl.measurableSet
  have hScov : ∀ g, ∃ γ ∈ GQ V, γ * g ∈ S := fun g => by
    obtain ⟨γ, hγ, s, hs, e⟩ := hcov g
    refine ⟨γ⁻¹, inv_mem hγ, ?_⟩
    rw [e, inv_mul_cancel_left]
    exact hs
  have hI : ∫⁻ t in GlobalTheory.SiegelSet.cone r c,
      ENNReal.ofReal (∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) *
        ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus D.host.F V.rank t * ∏ i, t i)⁻¹) < ⊤ := by
    rcases Nat.eq_zero_or_pos r with hr | hr
    · subst hr
      exact GlobalTheory.CompanionTheory.SiegelCone.cone_integral_zero_vars_lt_top D.host.F V.rank (2 * n) c
    · have hw := GlobalTheory.T.witt_frame_rank_le_witt_index D V Xf Yf hW
      have h2 : n + Formalism.MainNotions.SchurIrreducible.wittIdx V < V.rank := hV.resolve_left (by omega)
      exact GlobalTheory.T.lintegral_siegelCone_inv_modulus_lt_top_weil D.host.F V.rank r (2 * n) hc (by omega)
  calc absThetaInt V ν Φ.1 ≤ ∫⁻ g in S, absTheta V Φ.1 g ∂ν :=
        GlobalTheory.T.theta_integral_le_fundamental_set D V ν hν Φ.1 hcontΦ S hSm hScov
    _ ≤ C₁ * ∫⁻ t in GlobalTheory.SiegelSet.cone r c,
          ENNReal.ofReal (max C 0 * ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) *
            ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus D.host.F V.rank t * ∏ i, t i)⁻¹) := by
        refine hC₁ (absTheta V Φ.1) _ (by fun_prop) fun p hp t ht a ha k hk => ?_
        have ht0 : ∀ i, 0 < t i := ht.1
        have hP : 0 ≤ ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n)) :=
          Finset.prod_nonneg fun i _ => pow_nonneg (ht0 i).le _
        refine (hC p hp t ht a ha k hk).trans (ENNReal.ofReal_le_ofReal ?_)
        gcongr
        exact le_max_left _ _
    _ = C₁ * (ENNReal.ofReal (max C 0) * ∫⁻ t in GlobalTheory.SiegelSet.cone r c,
          ENNReal.ofReal (∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) *
            ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus D.host.F V.rank t * ∏ i, t i)⁻¹)) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        exact lintegral_congr fun t => by rw [ENNReal.ofReal_mul (le_max_right _ _), mul_assoc]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hI)

end GlobalTheory.CompanionTheory.WeilTheta

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaConvergenceOfSiegelSetStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_convergence_of_siegel_set : GlobalTheory.Published.SiegelSetUnitary → GlobalTheory.Published.WeilThetaConvergence := by
  first | exact @GlobalTheory.CompanionTheory.WeilTheta.weilThetaConvergence_of_siegelSet | exact GlobalTheory.CompanionTheory.WeilTheta.weilThetaConvergence_of_siegelSet | (intros; apply GlobalTheory.CompanionTheory.WeilTheta.weilThetaConvergence_of_siegelSet <;> assumption)
end
