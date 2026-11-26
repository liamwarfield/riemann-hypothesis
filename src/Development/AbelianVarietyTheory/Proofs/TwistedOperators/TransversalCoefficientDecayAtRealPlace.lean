module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealLieOperatorThetaQuotientLine
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TransversalCoefficientDecayAtRealPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TransversalCoefficientDecayAtRealPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PackLoc

theorem farClause : ∀ (D : D7) (θ : InfFam D) (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (S S' : D.what₂.Tau → SPar) (M₀ : DSModel Y S')
  (MP : DSModel V S) (τ : D.what₂.Tau) (e : Option (Fin Y.rank) ≃ Fin V.rank) (v₀ v : MP.H τ)
  (g₀ B : Matrix (Fin V.rank) (Fin V.rank) ℂ) (c₁ lam q Cb : ℝ) (k : ℕ),
  IsUnit B → Bᴴ * Formalism.REAL.Jm (MP.ε τ) * B = gramAt D V τ → B *ᵥ (fun i => tauE D τ (zv d i)) = Pi.single (e none) 1 →
  V.rank = k + 1 →
  (∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ u, GlobalTheory.PackLoc.mco MP τ g₀ v₀ (g * GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u)) =
    ⟪v, MP.σ τ (B * g * B⁻¹ * GlobalTheory.PackLoc.embOpt e (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u))) v⟫_ℂ) →
  (∀ F : Matrix (Fin Y.rank) (Fin Y.rank) ℂ → ℂ,
    Integrable (fun u : Formalism.REAL.UJ (M₀.ε τ) => F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u))) (Formalism.REAL.muG (M₀.ε τ)) ↔
      Integrable (fun h => F (Formalism.MainNotions.S.umat h)) (Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ))) →
  (∀ F : Matrix (Fin Y.rank) (Fin Y.rank) ℂ → ℝ, ∫ u, F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u)) ∂(Formalism.REAL.muG (M₀.ε τ)) =
    lam • ∫ h, F (Formalism.MainNotions.S.umat h) ∂(Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ))) →
  0 < c₁ → 0 < lam → Cb ≤ Real.exp q →
  (∀ g ∈ Formalism.MainNotions.S.UJset (MP.ε τ),
    Integrable (fun h => ⟪v, MP.σ τ (g * GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ)
      (Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ)) ∧
    ∫ h, ‖⟪v, MP.σ τ (g * GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ‖ ∂(Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ)) ≤
      c₁ * Cb * Real.sqrt (∑ a, ‖g a (e none)‖ ^ 2) ^ (-(2 * (k : ℝ) + 7))) →
  ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
    Integrable (fun u => GlobalTheory.PackLoc.mco MP τ g₀ v₀ (g * GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u)))
      (Formalism.REAL.muG (M₀.ε τ)) ∧
    (∫ u, ‖GlobalTheory.PackLoc.mco MP τ g₀ v₀ (g * GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u))‖ ∂(Formalism.REAL.muG (M₀.ε τ))) *
      eu (B *ᵥ (g *ᵥ fun i => tauE D τ (zv d i))) ^ (2 * V.rank + 5) ≤ Real.exp q * ‖((lam * c₁ : ℝ) : ℂ)‖ := by
  intro D θ Y V d S S' M₀ MP τ e v₀ v g₀ B c₁ lam q Cb k hB hBJ hBz hk hmco hint hInt hc₁ hlam hCb hb g hg
  set z : Fin V.rank → ℂ := fun i => tauE D τ (zv d i) with hz
  have hBinv : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B ((Matrix.isUnit_iff_isUnit_det B).mp hB)
  have hBinv' : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B ((Matrix.isUnit_iff_isUnit_det B).mp hB)
  have hg' : B * g * B⁻¹ ∈ Formalism.MainNotions.S.UJset (MP.ε τ) := by
    have hg0 : gᴴ * gramAt D V τ * g = gramAt D V τ := hg
    show (B * g * B⁻¹)ᴴ * Formalism.REAL.Jm (MP.ε τ) * (B * g * B⁻¹) = Formalism.REAL.Jm (MP.ε τ)
    have hBi : (B⁻¹)ᴴ * Bᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, hBinv', Matrix.conjTranspose_one]
    calc (B * g * B⁻¹)ᴴ * Formalism.REAL.Jm (MP.ε τ) * (B * g * B⁻¹)
        = (B⁻¹)ᴴ * (gᴴ * (Bᴴ * Formalism.REAL.Jm (MP.ε τ) * B) * g) * B⁻¹ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (B⁻¹)ᴴ * (Bᴴ * Formalism.REAL.Jm (MP.ε τ) * B) * B⁻¹ := by rw [hBJ, hg0]
      _ = ((B⁻¹)ᴴ * Bᴴ) * Formalism.REAL.Jm (MP.ε τ) * (B * B⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm (MP.ε τ) := by rw [hBi, hBinv']; simp
  obtain ⟨hbI, hbB⟩ := hb _ hg'
  set F : Matrix (Fin Y.rank) (Fin Y.rank) ℂ → ℂ :=
    fun x => ⟪v, MP.σ τ (B * g * B⁻¹ * GlobalTheory.PackLoc.embOpt e x) v⟫_ℂ with hF
  have hfun : (fun u => GlobalTheory.PackLoc.mco MP τ g₀ v₀ (g * GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u)))
      = fun u => F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u)) := funext (hmco g hg)
  refine ⟨?_, ?_⟩
  · rw [hfun]; exact (hint F).mpr hbI
  ·
    have hcol : B *ᵥ (g *ᵥ z) = fun a => (B * g * B⁻¹) a (e none) := by
      funext a
      have : (B * g * B⁻¹) *ᵥ (B *ᵥ z) = B *ᵥ (g *ᵥ z) := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_assoc (B * g), hBinv, Matrix.mul_one, ← Matrix.mulVec_mulVec]
      rw [← this, hBz]
      simp [Matrix.mulVec_single]
    set L := eu (B *ᵥ (g *ᵥ z)) with hL
    have hLdef : L = Real.sqrt (∑ a, ‖(B * g * B⁻¹) a (e none)‖ ^ 2) := by
      rw [hL, hcol]; rfl
    have hI : (∫ u, ‖GlobalTheory.PackLoc.mco MP τ g₀ v₀ (g * GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u))‖ ∂(Formalism.REAL.muG (M₀.ε τ)))
        = lam * ∫ h, ‖F (Formalism.MainNotions.S.umat h)‖ ∂(Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ)) := by
      have := hInt (fun x => ‖F x‖)
      rw [smul_eq_mul] at this
      rw [← this]
      congr 1
      funext u
      rw [hmco g hg u]
    have hL0 : 0 ≤ L := Real.sqrt_nonneg _
    have hexp : 2 * V.rank + 5 = 2 * k + 7 := by omega
    have hnorm : ‖((lam * c₁ : ℝ) : ℂ)‖ = lam * c₁ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mul_pos hlam hc₁)]
    rw [hI, hnorm, hexp]
    have hInn : 0 ≤ ∫ h, ‖F (Formalism.MainNotions.S.umat h)‖ ∂(Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ)) :=
      integral_nonneg (fun _ => norm_nonneg _)
    rcases hL0.lt_or_eq with hLp | hLz
    · have hbB' : ∫ h, ‖F (Formalism.MainNotions.S.umat h)‖ ∂(Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ))
          ≤ c₁ * Cb * L ^ (-(2 * (k : ℝ) + 7)) := by rw [hLdef]; exact hbB
      have hpow : L ^ (-(2 * (k : ℝ) + 7)) * L ^ (2 * k + 7) = 1 := by
        rw [Real.rpow_neg hL0, ← Real.rpow_natCast]
        push_cast
        exact inv_mul_cancel₀ (Real.rpow_pos_of_pos hLp _).ne'
      have hLn : 0 ≤ L ^ (2 * k + 7) := pow_nonneg hL0 _
      calc lam * (∫ h, ‖F (Formalism.MainNotions.S.umat h)‖ ∂(Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ))) * L ^ (2 * k + 7)
          ≤ lam * (c₁ * Cb * L ^ (-(2 * (k : ℝ) + 7))) * L ^ (2 * k + 7) := by
            gcongr
        _ = lam * c₁ * Cb * (L ^ (-(2 * (k : ℝ) + 7)) * L ^ (2 * k + 7)) := by ring
        _ = lam * c₁ * Cb := by rw [hpow, mul_one]
        _ ≤ lam * c₁ * Real.exp q := by
            exact mul_le_mul_of_nonneg_left hCb (mul_pos hlam hc₁).le
        _ = Real.exp q * (lam * c₁) := by ring
    · rw [← hLz, zero_pow (by omega), mul_zero]
      exact mul_nonneg (Real.exp_pos q).le (mul_pos hlam hc₁).le

end GlobalTheory.PackLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TransversalCoefficientDecayAtRealPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transversal_coefficient_decay_at_real_place : ∀ (D : D7) (θ : InfFam D) (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (S S' : D.what₂.Tau → SPar) (M₀ : DSModel Y S')
  (MP : DSModel V S) (τ : D.what₂.Tau) (e : Option (Fin Y.rank) ≃ Fin V.rank) (v₀ v : MP.H τ)
  (g₀ B : Matrix (Fin V.rank) (Fin V.rank) ℂ) (c₁ lam q Cb : ℝ) (k : ℕ),
  IsUnit B → Bᴴ * Formalism.REAL.Jm (MP.ε τ) * B = gramAt D V τ → B *ᵥ (fun i => tauE D τ (zv d i)) = Pi.single (e none) 1 →
  V.rank = k + 1 →
  (∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ u, GlobalTheory.PackLoc.mco MP τ g₀ v₀ (g * GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u)) =
    ⟪v, MP.σ τ (B * g * B⁻¹ * GlobalTheory.PackLoc.embOpt e (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u))) v⟫_ℂ) →
  (∀ F : Matrix (Fin Y.rank) (Fin Y.rank) ℂ → ℂ,
    Integrable (fun u : Formalism.REAL.UJ (M₀.ε τ) => F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u))) (Formalism.REAL.muG (M₀.ε τ)) ↔
      Integrable (fun h => F (Formalism.MainNotions.S.umat h)) (Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ))) →
  (∀ F : Matrix (Fin Y.rank) (Fin Y.rank) ℂ → ℝ, ∫ u, F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u)) ∂(Formalism.REAL.muG (M₀.ε τ)) =
    lam • ∫ h, F (Formalism.MainNotions.S.umat h) ∂(Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ))) →
  0 < c₁ → 0 < lam → Cb ≤ Real.exp q →
  (∀ g ∈ Formalism.MainNotions.S.UJset (MP.ε τ),
    Integrable (fun h => ⟪v, MP.σ τ (g * GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ)
      (Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ)) ∧
    ∫ h, ‖⟪v, MP.σ τ (g * GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ‖ ∂(Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ)) ≤
      c₁ * Cb * Real.sqrt (∑ a, ‖g a (e none)‖ ^ 2) ^ (-(2 * (k : ℝ) + 7))) →
  ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
    Integrable (fun u => GlobalTheory.PackLoc.mco MP τ g₀ v₀ (g * GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u)))
      (Formalism.REAL.muG (M₀.ε τ)) ∧
    (∫ u, ‖GlobalTheory.PackLoc.mco MP τ g₀ v₀ (g * GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u))‖ ∂(Formalism.REAL.muG (M₀.ε τ))) *
      eu (B *ᵥ (g *ᵥ fun i => tauE D τ (zv d i))) ^ (2 * V.rank + 5) ≤ Real.exp q * ‖((lam * c₁ : ℝ) : ℂ)‖ := by
  first | exact @GlobalTheory.PackLoc.farClause | exact GlobalTheory.PackLoc.farClause | (intros; apply GlobalTheory.PackLoc.farClause <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatrixCoefficientDecayInFrameOfTranslateDecay
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatrixCoefficientDecayInFrameOfTranslateDecay
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FrameDecay

section Frob
attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedRing

theorem hs_eq_norm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2) = ‖A‖ := by
  rw [Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  exact (Real.rpow_natCast _ 2).symm

theorem hsn_mul_le {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    GlobalTheory.SepPer.hsn (A * B) ≤ GlobalTheory.SepPer.hsn A * GlobalTheory.SepPer.hsn B := by
  unfold GlobalTheory.SepPer.hsn
  rw [hs_eq_norm, hs_eq_norm, hs_eq_norm]
  exact Matrix.frobenius_norm_mul A B

end Frob

theorem hsn_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ GlobalTheory.SepPer.hsn A := Real.sqrt_nonneg _

theorem one_le_hsn_of_mem {n : ℕ} (ε : Fin n → Bool) (i : Fin n) (y : Matrix (Fin n) (Fin n) ℂ)
    (hy : y ∈ Formalism.MainNotions.S.UJset ε) : 1 ≤ GlobalTheory.SepPer.hsn y := by
  have hy' : yᴴ * Formalism.REAL.Jm ε * y = Formalism.REAL.Jm ε := hy
  have h := congrFun (congrFun hy' i) i
  have e1 : (yᴴ * Formalism.REAL.Jm ε * y) i i = ∑ k, star (y k i) * ((if ε k then 1 else -1) * y k i) := by
    simp only [Formalism.REAL.Jm]
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
    ring
  have e2 : ‖Formalism.REAL.Jm ε i i‖ = 1 := by
    by_cases hi : ε i = true <;> simp [Formalism.REAL.Jm, hi]
  have hcol : 1 ≤ ∑ k, ‖y k i‖ ^ 2 := by
    rw [← e2, ← h, e1]
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
    by_cases hk : ε k = true <;> simp [hk, norm_mul, sq]
  have hall : ∑ k, ‖y k i‖ ^ 2 ≤ ∑ a, ∑ b, ‖y a b‖ ^ 2 :=
    Finset.sum_le_sum fun a _ =>
      Finset.single_le_sum (f := fun b => ‖y a b‖ ^ 2) (fun b _ => by positivity) (Finset.mem_univ i)
  unfold GlobalTheory.SepPer.hsn
  rw [show (1 : ℝ) = Real.sqrt 1 by simp]
  exact Real.sqrt_le_sqrt (hcol.trans hall)

end GlobalTheory.FrameDecay

namespace GlobalTheory.FrameDecay

theorem coef_frame_decay : ∀ (m N : ℕ), N = m + 1 → ∀ (ε : Fin N → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (π : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (v₀ : H) (g₀ F G : Matrix (Fin N) (Fin N) ℂ) (A₀ : ℝ),
  Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) π → g₀ ∈ Formalism.MainNotions.S.UJset ε → IsUnit F → Fᴴ * Formalism.REAL.Jm ε * F = G →
  (∀ g ∈ Formalism.MainNotions.S.UJset ε, ‖⟪π g₀ v₀, π g (π g₀ v₀)⟫_ℂ‖ ≤ A₀ * GlobalTheory.SepReal.hsn g ^ (-(20 * ((m : ℝ) + 1) ^ 2))) →
  ∃ C : ℝ, ∀ g ∈ Formalism.QuantumDeterminants.UH G, ‖⟪v₀, π (F * g * F⁻¹) v₀⟫_ℂ‖ * (1 + GlobalTheory.SepPer.hsn g) ^ (2 * N ^ 2 + 1) ≤ C := by
  intro m N hN ε H instH instI π v₀ g₀ F G A₀ hπ hg₀ hF hG hdec
  obtain ⟨⟨_, hmul⟩, hiso, -⟩ := hπ
  have hg₀' : g₀ᴴ * Formalism.REAL.Jm ε * g₀ = Formalism.REAL.Jm ε := hg₀
  have hJJ := Formalism.REAL.Jm_mul_self ε

  have hleft : (Formalism.REAL.Jm ε * g₀ᴴ * Formalism.REAL.Jm ε) * g₀ = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc g₀ᴴ, hg₀', hJJ]
  have hinv : g₀⁻¹ = Formalism.REAL.Jm ε * g₀ᴴ * Formalism.REAL.Jm ε := Matrix.inv_eq_left_inv hleft
  have hl : g₀⁻¹ * g₀ = 1 := by rw [hinv, hleft]
  have hr : g₀ * g₀⁻¹ = 1 := Matrix.mul_nonsing_inv g₀ (Matrix.isUnit_det_of_left_inverse hleft)
  have hmemMul : ∀ a ∈ Formalism.MainNotions.S.UJset ε, ∀ b ∈ Formalism.MainNotions.S.UJset ε, a * b ∈ Formalism.MainNotions.S.UJset ε := by
    intro a ha b hb
    have ha' : aᴴ * Formalism.REAL.Jm ε * a = Formalism.REAL.Jm ε := ha
    have hb' : bᴴ * Formalism.REAL.Jm ε * b = Formalism.REAL.Jm ε := hb
    show (a * b)ᴴ * Formalism.REAL.Jm ε * (a * b) = Formalism.REAL.Jm ε
    calc (a * b)ᴴ * Formalism.REAL.Jm ε * (a * b) = bᴴ * (aᴴ * Formalism.REAL.Jm ε * a) * b := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [ha', hb']
  have hinvMem : g₀⁻¹ ∈ Formalism.MainNotions.S.UJset ε := by
    show (g₀⁻¹)ᴴ * Formalism.REAL.Jm ε * g₀⁻¹ = Formalism.REAL.Jm ε
    conv_lhs => rw [← hg₀']
    rw [show (g₀⁻¹)ᴴ * (g₀ᴴ * Formalism.REAL.Jm ε * g₀) * g₀⁻¹ = (g₀ * g₀⁻¹)ᴴ * Formalism.REAL.Jm ε * (g₀ * g₀⁻¹) by
      rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc], hr]
    simp

  have hFd : IsUnit F.det := (Matrix.isUnit_iff_isUnit_det F).mp hF
  have hFl : F⁻¹ * F = 1 := Matrix.nonsing_inv_mul F hFd
  have hFr : F * F⁻¹ = 1 := Matrix.mul_nonsing_inv F hFd

  have hkeep : ∀ u w : H, ⟪π g₀ u, π g₀ w⟫_ℂ = ⟪u, w⟫_ℂ := by
    intro u w
    let T : H →ₗᵢ[ℂ] H := ⟨(π g₀ : H →ₗ[ℂ] H), fun v => hiso g₀ hg₀ v⟩
    exact T.inner_map_map u w
  set k : ℝ := 20 * ((m : ℝ) + 1) ^ 2 with hk
  set e : ℕ := 2 * N ^ 2 + 1 with he
  have hek : (e : ℝ) ≤ k := by
    have h1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    rw [he, hk, hN]; push_cast; nlinarith
  set c₁ : ℝ := GlobalTheory.SepPer.hsn (F⁻¹ * g₀⁻¹) * GlobalTheory.SepPer.hsn (g₀ * F) with hc₁
  have hc₁0 : 0 ≤ c₁ := mul_nonneg (hsn_nonneg _) (hsn_nonneg _)
  refine ⟨|A₀| * (1 + c₁) ^ e, fun g hg => ?_⟩
  have hg' : gᴴ * G * g = G := hg
  set x := F * g * F⁻¹ with hx
  have hxMem : x ∈ Formalism.MainNotions.S.UJset ε := by
    show xᴴ * Formalism.REAL.Jm ε * x = Formalism.REAL.Jm ε
    have : xᴴ * Formalism.REAL.Jm ε * x = (F⁻¹)ᴴ * (gᴴ * (Fᴴ * Formalism.REAL.Jm ε * F) * g) * F⁻¹ := by
      rw [hx, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    rw [this, hG, hg', ← hG]
    have hFH : (F⁻¹)ᴴ * Fᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hFr, Matrix.conjTranspose_one]
    calc (F⁻¹)ᴴ * (Fᴴ * Formalism.REAL.Jm ε * F) * F⁻¹ = ((F⁻¹)ᴴ * Fᴴ) * Formalism.REAL.Jm ε * (F * F⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [hFH, hFr, Matrix.one_mul, Matrix.mul_one]
  set y := g₀ * x * g₀⁻¹ with hy
  have hyMem : y ∈ Formalism.MainNotions.S.UJset ε := hmemMul _ (hmemMul _ hg₀ _ hxMem) _ hinvMem

  have hco : ⟪v₀, π x v₀⟫_ℂ = ⟪π g₀ v₀, π y (π g₀ v₀)⟫_ℂ := by
    have h1 : π y (π g₀ v₀) = π g₀ (π x v₀) := by
      have h2 : y * g₀ = g₀ * x := by rw [hy, Matrix.mul_assoc, hl, Matrix.mul_one]
      rw [← ContinuousLinearMap.comp_apply, ← hmul _ hyMem _ hg₀, h2, hmul _ hg₀ _ hxMem,
        ContinuousLinearMap.comp_apply]
    rw [h1, hkeep]

  set s := GlobalTheory.SepPer.hsn y with hs
  set t := GlobalTheory.SepPer.hsn g with ht
  have hs1 : 1 ≤ s := one_le_hsn_of_mem ε ⟨0, by omega⟩ y hyMem
  have hs0 : 0 < s := by linarith
  have hts : t ≤ c₁ * s := by
    have hgeq : g = (F⁻¹ * g₀⁻¹) * y * (g₀ * F) := by
      have : (F⁻¹ * g₀⁻¹) * y * (g₀ * F) = (F⁻¹ * F) * g * (F⁻¹ * F) := by
        rw [hy, hx]; simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc g₀⁻¹ g₀, hl, Matrix.one_mul,
          ← Matrix.mul_assoc g₀⁻¹ g₀, hl, Matrix.one_mul]
      rw [this, hFl, Matrix.one_mul, Matrix.mul_one]
    rw [ht, hgeq, hc₁]
    calc GlobalTheory.SepPer.hsn ((F⁻¹ * g₀⁻¹) * y * (g₀ * F))
        ≤ GlobalTheory.SepPer.hsn ((F⁻¹ * g₀⁻¹) * y) * GlobalTheory.SepPer.hsn (g₀ * F) := hsn_mul_le _ _
      _ ≤ (GlobalTheory.SepPer.hsn (F⁻¹ * g₀⁻¹) * s) * GlobalTheory.SepPer.hsn (g₀ * F) :=
          mul_le_mul_of_nonneg_right (hsn_mul_le _ _) (hsn_nonneg _)
      _ = GlobalTheory.SepPer.hsn (F⁻¹ * g₀⁻¹) * GlobalTheory.SepPer.hsn (g₀ * F) * s := by ring
  have hbd := hdec y hyMem
  have hsame : GlobalTheory.SepReal.hsn y = s := rfl
  rw [hsame, ← hco] at hbd
  have hpow : s ^ (-k) ≤ (s ^ e)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg hs0.le]
    exact Real.rpow_le_rpow_of_exponent_le hs1 (by linarith)
  have hz : ‖⟪v₀, π x v₀⟫_ℂ‖ ≤ |A₀| * (s ^ e)⁻¹ :=
    hbd.trans ((mul_le_mul_of_nonneg_right (le_abs_self A₀) (Real.rpow_nonneg hs0.le _)).trans
      (mul_le_mul_of_nonneg_left hpow (abs_nonneg _)))
  have hT : (1 + t) ^ e ≤ (1 + c₁) ^ e * s ^ e := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by linarith [hsn_nonneg g]) ?_ e
    nlinarith
  have hse : 0 < s ^ e := pow_pos hs0 e
  calc ‖⟪v₀, π x v₀⟫_ℂ‖ * (1 + t) ^ e ≤ (|A₀| * (s ^ e)⁻¹) * ((1 + c₁) ^ e * s ^ e) :=
        mul_le_mul hz hT (pow_nonneg (by linarith [hsn_nonneg g]) _)
          (mul_nonneg (abs_nonneg _) (inv_nonneg.mpr hse.le))
    _ = |A₀| * (1 + c₁) ^ e := by field_simp

end GlobalTheory.FrameDecay
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatrixCoefficientDecayInFrameOfTranslateDecayStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_coefficient_decay_in_frame_of_translate_decay : ∀ (m N : ℕ), N = m + 1 → ∀ (ε : Fin N → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (π : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (v₀ : H) (g₀ F G : Matrix (Fin N) (Fin N) ℂ) (A₀ : ℝ),
  Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) π → g₀ ∈ Formalism.MainNotions.S.UJset ε → IsUnit F → Fᴴ * Formalism.REAL.Jm ε * F = G →
  (∀ g ∈ Formalism.MainNotions.S.UJset ε, ‖⟪π g₀ v₀, π g (π g₀ v₀)⟫_ℂ‖ ≤ A₀ * GlobalTheory.SepReal.hsn g ^ (-(20 * ((m : ℝ) + 1) ^ 2))) →
  ∃ C : ℝ, ∀ g ∈ Formalism.QuantumDeterminants.UH G, ‖⟪v₀, π (F * g * F⁻¹) v₀⟫_ℂ‖ * (1 + GlobalTheory.SepPer.hsn g) ^ (2 * N ^ 2 + 1) ≤ C := by
  first | exact @GlobalTheory.FrameDecay.coef_frame_decay | exact GlobalTheory.FrameDecay.coef_frame_decay | (intros; apply GlobalTheory.FrameDecay.coef_frame_decay <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemLatticeOfRationalMemCompletionAllPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemLatticeOfRationalMemCompletionAllPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt intAt latV latA)

noncomputable section
namespace GlobalTheory.RatLat

theorem dual_gens {A K W : Type} [CommRing A] [IsDomain A] [IsDedekindDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] [AddCommGroup W] [Module K W] [Module A W] [IsScalarTower A K W] (M : Submodule A W)
    (hfg : M.FG) (hden : ∀ v : W, ∃ d : A, d ≠ 0 ∧ d • v ∈ M) :
    ∃ (m : ℕ) (g : Fin m → W) (Φ : Fin m → W →ₗ[K] K), (∀ i, g i ∈ M) ∧
      (∀ i, ∀ x ∈ M, Φ i x ∈ (algebraMap A K).range) ∧ ∀ x, x = ∑ i, Φ i x • g i := by
  classical
  haveI hfin : Module.Finite A M := Module.Finite.iff_fg.2 hfg
  have hcancel : ∀ (d : A) (x : W), d ≠ 0 → d • x = 0 → x = 0 := by
    intro d x hd h
    rw [← IsScalarTower.algebraMap_smul K d x] at h
    exact (smul_eq_zero.1 h).resolve_left ((map_ne_zero_iff _ (IsFractionRing.injective A K)).2 hd)
  haveI hflat : Module.Flat A M := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    rintro x ⟨d, hd⟩
    have : (d : A) • (x : W) = 0 := congrArg Subtype.val hd
    exact Subtype.ext (hcancel d x (nonZeroDivisors.coe_ne_zero d) this)
  haveI hfp : Module.FinitePresentation A M := Module.finitePresentation_of_finite _ _
  haveI hproj : Module.Projective A M := Module.Flat.projective_of_finitePresentation
  obtain ⟨m, π, hπ⟩ := Module.Finite.exists_fin' A M
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property π LinearMap.id hπ
  let g : Fin m → W := fun i => (π (Pi.single i 1) : W)
  have hg : ∀ i, g i ∈ M := fun i => (π (Pi.single i 1)).2
  have hexp : ∀ x : M, (x : W) = ∑ i, (algebraMap A K (σ x i)) • g i := by
    intro x
    have h1 : π (σ x) = x := LinearMap.congr_fun hσ x
    conv_lhs => rw [← h1, LinearMap.pi_apply_eq_sum_univ π (σ x)]
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.coe_smul, IsScalarTower.algebraMap_smul]
    congr 2
    congr 1
    funext j
    simp [Pi.single_apply, eq_comm]
  have hsp : Submodule.span K (M : Set W) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    obtain ⟨d, hd, hv⟩ := hden v
    have hd' : algebraMap A K d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A K)).2 hd
    have : v = (algebraMap A K d)⁻¹ • (d • v) := by
      rw [← IsScalarTower.algebraMap_smul K d v, smul_smul, inv_mul_cancel₀ hd', one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hv)
  have hunitW : ∀ x : nonZeroDivisors A, IsUnit (algebraMap A (Module.End A W) x) :=
    (isLocalizedModule_id (nonZeroDivisors A) W K).map_units
  have hunitK : ∀ x : nonZeroDivisors A, IsUnit (algebraMap A (Module.End A K) x) :=
    (isLocalizedModule_id (nonZeroDivisors A) K K).map_units
  haveI hloc : IsLocalizedModule (nonZeroDivisors A) M.subtype := by
    refine ⟨hunitW, fun v => ?_, fun {x y} h => ⟨1, by simpa using Subtype.ext h⟩⟩
    obtain ⟨d, hd, hv⟩ := hden v
    exact ⟨(⟨d • v, hv⟩, ⟨d, mem_nonZeroDivisors_of_ne_zero hd⟩), rfl⟩
  let φ : Fin m → M →ₗ[A] K := fun i => (Algebra.linearMap A K) ∘ₗ (LinearMap.proj i) ∘ₗ σ
  let Φ0 : Fin m → W →ₗ[A] K := fun i => IsLocalizedModule.lift (nonZeroDivisors A) M.subtype (φ i) hunitK
  have hΦ0 : ∀ i (x : M), Φ0 i (x : W) = algebraMap A K (σ x i) := fun i x =>
    IsLocalizedModule.lift_apply _ M.subtype (φ i) hunitK x
  let Φ : Fin m → W →ₗ[K] K := fun i => (Φ0 i).extendScalarsOfIsLocalization (nonZeroDivisors A) K
  have hΦ : ∀ i (x : M), Φ i (x : W) = algebraMap A K (σ x i) := fun i x => hΦ0 i x
  refine ⟨m, g, Φ, hg, fun i x hx => ⟨σ ⟨x, hx⟩ i, (hΦ i ⟨x, hx⟩).symm⟩, fun x => ?_⟩
  have hL : (LinearMap.id : W →ₗ[K] W) = ∑ i, (LinearMap.smulRight (Φ i) (g i)) := by
    refine LinearMap.ext_on hsp fun y hy => ?_
    rw [LinearMap.id_apply, LinearMap.sum_apply]
    simp only [LinearMap.smulRight_apply]
    refine (hexp ⟨y, hy⟩).trans (Finset.sum_congr rfl fun i _ => ?_)
    exact congrArg (· • g i) (hΦ i ⟨y, hy⟩).symm
  have := LinearMap.congr_fun hL x
  simpa using this

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

theorem coe_mem_int_iff {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (f : F) :
    algebraMap F (Fv F v) f ∈ v.adicCompletionIntegers F ↔ v.valuation F f ≤ 1 := by
  rw [mem_adicCompletionIntegers]
  exact Iff.of_eq (congrArg (· ≤ 1) (valuedAdicCompletion_eq_valuation' v f))

theorem int_of_intAf {F : Type} [Field F] [NumberField F] (f : F) (h : algebraMap F (Af F) f ∈ intAf F) :
    f ∈ (algebraMap (𝓞 F) F).range := by
  refine mem_integers_of_valuation_le_one F f fun v => ?_
  have := h v
  rw [AlgHom.commutes] at this
  exact (coe_mem_int_iff v f).1 this

theorem smul_intAf {F : Type} [Field F] [NumberField F] (c : 𝓞 F) {α : Af F} (hα : α ∈ intAf F) :
    (algebraMap (𝓞 F) F c) • α ∈ intAf F := by
  intro v
  rw [map_smul, Algebra.smul_def]
  refine mul_mem ((coe_mem_int_iff v _).2 (valuation_le_one v c)) (hα v)

def extF {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (ψ : E →ₗ[F] F) : AF F ⊗[F] E →ₗ[F] AF F :=
  (TensorProduct.rid F (AF F)).toLinearMap ∘ₗ LinearMap.lTensor (AF F) ψ

theorem extF_tmul {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (ψ : E →ₗ[F] F) (a : AF F) (e : E) :
    extF ψ (a ⊗ₜ[F] e) = ψ e • a := by
  simp [extF]

def extV {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} (Φ : (Fin n → E) →ₗ[F] F)
    (y : Fin n → AF F ⊗[F] E) : AF F :=
  ∑ j, extF (Φ ∘ₗ LinearMap.single F (fun _ : Fin n => E) j) (y j)

theorem extV_gen {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} (Φ : (Fin n → E) →ₗ[F] F)
    (a : AF F) (x : Fin n → E) : extV Φ (fun i => a ⊗ₜ[F] x i) = Φ x • a := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [extV, extF_tmul, LinearMap.comp_apply, ← Finset.sum_smul, ← map_sum]
  congr 2
  exact Finset.univ_sum_single x

theorem extV_add {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} (Φ : (Fin n → E) →ₗ[F] F)
    (y y' : Fin n → AF F ⊗[F] E) : extV Φ (y + y') = extV Φ y + extV Φ y' := by
  simp [extV, map_add (f := _), Finset.sum_add_distrib]

theorem extV_neg {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} (Φ : (Fin n → E) →ₗ[F] F)
    (y : Fin n → AF F ⊗[F] E) : extV Φ (-y) = -extV Φ y := by
  simp [extV, map_neg, Finset.sum_neg_distrib]

theorem extV_zero {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} (Φ : (Fin n → E) →ₗ[F] F) :
    extV Φ (0 : Fin n → AF F ⊗[F] E) = 0 := by
  simp [extV]

theorem smul_pairA {F : Type} [Field F] [NumberField F] (f : F) (α : Af F) :
    f • pairA F 0 α = pairA F 0 (f • α) :=
  Prod.ext (smul_zero f) rfl

theorem coord_int {D : D7} {S : HSp D} (L : Lat S) (Φ : (Fin S.rank → D.host.E) →ₗ[D.host.F] D.host.F)
    (hΦ : ∀ x ∈ L, Φ x ∈ (algebraMap (𝓞 D.host.F) D.host.F).range) (z : Fin S.rank → D.host.E)
    (hz : (fun i => pairA D.host.F 0 1 ⊗ₜ[D.host.F] z i) ∈ latV S L (fun _ => True)) :
    Φ z ∈ (algebraMap (𝓞 D.host.F) D.host.F).range := by
  have key : ∀ y ∈ latV S L (fun _ => True), ∃ β ∈ intAf D.host.F, extV Φ y = pairA D.host.F 0 β := by
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨α, hαi, -, a, ha, x, hx, rfl⟩ := hy
      rw [Set.mem_singleton_iff] at ha
      subst ha
      simp only [one_mul]
      obtain ⟨c, hc⟩ := hΦ x hx
      refine ⟨algebraMap (𝓞 D.host.F) D.host.F c • α, smul_intAf c hαi, ?_⟩
      rw [extV_gen, ← hc, smul_pairA]
    | zero => exact ⟨0, fun v => by rw [map_zero]; exact zero_mem _, by rw [extV_zero]; rfl⟩
    | add y y' _ _ hy hy' =>
      obtain ⟨β, hβ, e⟩ := hy
      obtain ⟨β', hβ', e'⟩ := hy'
      exact ⟨β + β', fun v => by rw [map_add]; exact add_mem (hβ v) (hβ' v),
        by rw [extV_add, e, e', GlobalTheory.FinPlLoc.pairA_add]⟩
    | neg y _ hy =>
      obtain ⟨β, hβ, e⟩ := hy
      exact ⟨-β, fun v => by rw [map_neg]; exact neg_mem (hβ v), by rw [extV_neg, e, GlobalTheory.FinPlLoc.pairA_neg]⟩
  obtain ⟨β, hβ, e⟩ := key _ hz
  rw [extV_gen, smul_pairA] at e
  have hb : Φ z • (1 : Af D.host.F) = β := congrArg Prod.snd e
  apply int_of_intAf
  rw [Algebra.algebraMap_eq_smul_one, hb]
  exact hβ

theorem mem_of_mem_latV : ∀ (D : D7) (S : HSp D) (L : Lat S), Submodule.IsFullLattice D.host.E L → ∀ z : Fin S.rank → D.host.E, (fun i => pairA D.host.F 0 1 ⊗ₜ[D.host.F] z i) ∈ latV S L (fun _ => True) → z ∈ L := by
  intro D S L hL z hz
  classical
  let M : Submodule (𝓞 D.host.F) (Fin S.rank → D.host.E) := L.restrictScalars (𝓞 D.host.F)
  obtain ⟨t, g0, hg0, hgen⟩ := GlobalTheory.FinPlLoc.exists_gens L hL.fg
  have hMfg : M.FG := by
    refine ⟨Finset.univ.image g0, ?_⟩
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact hg0 k
    · intro x hx
      obtain ⟨c, rfl⟩ := hgen x hx
      refine Submodule.sum_mem _ fun k _ => ?_
      rw [← Int.cast_smul_eq_zsmul (𝓞 D.host.F)]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  haveI hloc : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 D.host.E) (nonZeroDivisors (𝓞 D.host.F)))
      D.host.E := IsIntegralClosure.isLocalization (𝓞 D.host.F) D.host.F D.host.E (𝓞 D.host.E)
  have hden : ∀ v : Fin S.rank → D.host.E, ∃ d : 𝓞 D.host.F, d ≠ 0 ∧ d • v ∈ M := by
    intro v
    have hv : v ∈ Submodule.span D.host.E (L : Set (Fin S.rank → D.host.E)) := by
      rw [hL.span_eq_top]; trivial
    obtain ⟨⟨_, a, ha, rfl⟩, hs⟩ := multiple_mem_span_of_mem_localization_span
      (Algebra.algebraMapSubmonoid (𝓞 D.host.E) (nonZeroDivisors (𝓞 D.host.F))) D.host.E _ v hv
    rw [Submodule.span_eq] at hs
    refine ⟨a, nonZeroDivisors.coe_ne_zero ⟨a, ha⟩, ?_⟩
    show a • v ∈ L
    rw [← IsScalarTower.algebraMap_smul (𝓞 D.host.E) a v]
    exact hs
  obtain ⟨m, g, Φ, hg, hΦ, hid⟩ := dual_gens (K := D.host.F) M hMfg hden
  rw [hid z]
  refine Submodule.sum_mem _ fun k _ => ?_
  obtain ⟨c, hc⟩ := coord_int L (Φ k) (hΦ k) z hz
  rw [← hc, IsScalarTower.algebraMap_smul D.host.F c (g k)]
  exact (M.smul_mem c (hg k) : c • g k ∈ M)

end GlobalTheory.RatLat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemLatticeOfRationalMemCompletionAllPlacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt intAt latV latA)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_lattice_of_rational_mem_completion_all_places :
    ∀ (D : D7) (S : HSp D) (L : Lat S), Submodule.IsFullLattice D.host.E L →
      ∀ z : Fin S.rank → D.host.E,
        (fun i => pairA D.host.F 0 1 ⊗ₜ[D.host.F] z i) ∈ latV S L (fun _ => True) → z ∈ L :=
  GlobalTheory.RatLat.mem_of_mem_latV
end
end
