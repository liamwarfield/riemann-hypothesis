module

public import Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.ExistsIntAddConjEqOneOfBaseGood
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.ExistsRationalDarbouxCoordinatesTensorHermitian
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem Tw.RatDarboux.exists_rational_darboux_of_isGood : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E), B.IsGood σ → ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → Y.IsSkew σ B r' s' → ∃ co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J)) (Fin n × Fin d), ∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F, co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F x) = (fun k => algebraMap F (AF F) (y k), fun k => algebraMap F (AF F) (z k)) :=
  fun B hB _ _ X Y r s r' s' hX hY => Tw.RatDarboux.exists_rational_darboux _ B X Y r s r' s' hB hX hY
end

section -- merged from Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.IsLocallyConstantHeisenbergLatticeVacuumFunction
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzBilinear.PowTwoPowSubOneGrowth
namespace UpperTheory.Reformulated.B.P6.r25a

theorem sq_sub_one_lower_bound (w : ℂ) (hw : ‖w - 1‖ < 1 / 2) :
    (3 / 2 : ℝ) * ‖w - 1‖ ≤ ‖w ^ 2 - 1‖ := by
  have h1 : w ^ 2 - 1 = (w - 1) * (w + 1) := by ring
  have h2 : (w + 1) - (w - 1) = (2 : ℂ) := by ring
  have h3 : ‖(2 : ℂ)‖ ≤ ‖w + 1‖ + ‖w - 1‖ := by
    have h := norm_sub_le (w + 1) (w - 1)
    rwa [h2] at h
  have h4 : ‖(2 : ℂ)‖ = 2 := by simp
  have h5 : (3 / 2 : ℝ) ≤ ‖w + 1‖ := by linarith
  have h6 : 0 ≤ ‖w - 1‖ := norm_nonneg _
  have h7 : ‖w - 1‖ * (3 / 2) ≤ ‖w - 1‖ * ‖w + 1‖ := mul_le_mul_of_nonneg_left h5 h6
  rw [h1, norm_mul]
  linarith

theorem pow_two_pow_sub_one_growth (z : ℂ) (hz : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) :
    ∀ k : ℕ, (3 / 2 : ℝ) ^ k * ‖z - 1‖ ≤ ‖z ^ (2 ^ k) - 1‖ := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have e : z ^ (2 ^ (k + 1)) = (z ^ (2 ^ k)) ^ 2 := by
      rw [← pow_mul, ← pow_succ]
    have hs := sq_sub_one_lower_bound (z ^ (2 ^ k)) (hz _)
    calc (3 / 2 : ℝ) ^ (k + 1) * ‖z - 1‖ = (3 / 2) * ((3 / 2) ^ k * ‖z - 1‖) := by ring
      _ ≤ (3 / 2) * ‖z ^ (2 ^ k) - 1‖ := mul_le_mul_of_nonneg_left ih (by norm_num)
      _ ≤ ‖(z ^ (2 ^ k)) ^ 2 - 1‖ := hs
      _ = ‖z ^ (2 ^ (k + 1)) - 1‖ := by rw [e]

theorem Tw.HeisLatVac.lc_pow_near_one :
    ∀ {z : ℂ}, (∀ (n : ℕ), ‖z ^ n - OfNat.ofNat (nat_lit 1)‖ < OfNat.ofNat (nat_lit 1) / OfNat.ofNat (nat_lit 2)) → z = OfNat.ofNat (nat_lit 1) := by
  intro z hz
  have hz' : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2 := hz
  have hstep := pow_two_pow_sub_one_growth z hz'
  have hd : ‖z - 1‖ = 0 := by
    by_contra hne
    have hpos : 0 < ‖z - 1‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / (2 * ‖z - 1‖)) (by norm_num : (1 : ℝ) < 3 / 2)
    have h1 := hstep k
    have h2 := hz' (2 ^ k)
    have h2d : (0 : ℝ) < 2 * ‖z - 1‖ := by positivity
    rw [div_lt_iff₀ h2d] at hk
    have h3 : (3 / 2 : ℝ) ^ k * (2 * ‖z - 1‖) = 2 * ((3 / 2) ^ k * ‖z - 1‖) := by ring
    linarith
  have hz1 : z - 1 = 0 := norm_eq_zero.mp hd
  exact sub_eq_zero.mp hz1

end UpperTheory.Reformulated.B.P6.r25a
end

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open scoped GlobalTheory.VacAny

noncomputable section

namespace Tw.HeisLatVac
open _root_.GlobalTheory _root_.GlobalTheory.HeisLatVac

theorem lc_pow_near_one {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) : z = 1 :=
  _root_.UpperTheory.Reformulated.B.P6.r25a.Tw.HeisLatVac.lc_pow_near_one h

theorem lc_exists_open_ker {K : Type} [AddCommGroup K] [TopologicalSpace K] [NonarchimedeanAddGroup K]
    (ψ₀ : AddChar K ℂ) (hψ : Continuous ψ₀) : ∃ U₀ : OpenAddSubgroup K, ∀ t ∈ U₀, ψ₀ t = 1 := by
  have hV : {t : K | ‖ψ₀ t - 1‖ < 1 / 2} ∈ nhds (0 : K) :=
    (isOpen_lt (hψ.sub continuous_const).norm continuous_const).mem_nhds (by simp)
  obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ hV
  refine ⟨V, fun t ht => lc_pow_near_one fun n => ?_⟩
  rw [← AddChar.map_nsmul_eq_pow]
  exact hV (V.toAddSubgroup.nsmul_mem ht n)

end Tw.HeisLatVac
end
end
