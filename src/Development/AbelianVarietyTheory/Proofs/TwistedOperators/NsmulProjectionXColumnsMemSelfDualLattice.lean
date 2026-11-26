module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PsiPrimitiveStandardFramesBesselLevel
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertiaInvariantUnderUnramifiedTwistOfWeilDelign
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EvalModelPolynomialOnStdFramesInjective
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualFullLatticeShared

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NsmulProjectionXColumnsMemSelfDualLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NsmulProjectionXColumnsMemSelfDualLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.ProjXCols

theorem selfDual_isFullLattice {D : D7} : ∀ (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
    IsSelfDualC V Λ → Submodule.IsFullLattice D.host.E Λ := fun V Λ hΛ => _root_.DedupShared.selfDual_isFullLattice V Λ hΛ

theorem exists_nat_smul_mulVec_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (Λ : Submodule (𝓞 E) (Fin n → E)) (hΛ : Submodule.IsFullLattice E Λ) (A : Matrix (Fin n) (Fin n) E) :
    ∃ N : ℕ, 0 < N ∧ ∀ s ∈ Λ, (N : E) • (A *ᵥ s) ∈ Λ := by
  classical
  obtain ⟨gens, hg⟩ := hΛ.fg
  have key : ∀ g : Fin n → E, ∃ z : ℤ, z ≠ 0 ∧ (z : E) • (A *ᵥ g) ∈ Λ := fun g =>
    GlobalTheory.OrthDual.exists_int_smul_mem Λ (by rw [hΛ.span_eq_top]; trivial)
  choose z hz0 hz using key
  have hnat : ∀ g, ((z g).natAbs : E) • (A *ᵥ g) ∈ Λ := by
    intro g
    rcases Int.natAbs_eq (z g) with h | h
    · have h1 := hz g
      rw [h, Int.cast_natCast] at h1
      exact h1
    · have h1 := hz g
      rw [h, Int.cast_neg, Int.cast_natCast, neg_smul, Submodule.neg_mem_iff] at h1
      exact h1
  refine ⟨∏ g ∈ gens, (z g).natAbs, Finset.prod_pos fun g _ => Int.natAbs_pos.2 (hz0 g), ?_⟩
  let f : (Fin n → E) →ₗ[𝓞 E] (Fin n → E) :=
    (((∏ g ∈ gens, (z g).natAbs : ℕ) : E) • Matrix.mulVecLin A).restrictScalars (𝓞 E)
  have hle : Submodule.span (𝓞 E) (gens : Set (Fin n → E)) ≤ Λ.comap f := by
    rw [Submodule.span_le]
    intro g hgm
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun g => (z g).natAbs) hgm
    have hk' : (∏ g ∈ gens, (z g).natAbs) = (z g).natAbs * k := hk
    show ((∏ g ∈ gens, (z g).natAbs : ℕ) : E) • (A *ᵥ g) ∈ Λ
    rw [hk', Nat.cast_mul, mul_comm, mul_smul, Nat.cast_smul_eq_nsmul]
    exact nsmul_mem (hnat g) k
  rw [hg] at hle
  intro s hs
  exact hle hs

variable {D : D7}

theorem sum_mul_eq (S : HSp D) (N : ℕ) (Q M : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (hQM : S.gram * Q = M * S.gram)
    (s : Fin S.rank → D.host.E) (j : Fin S.rank) :
    ∑ l, (∑ k, star (s k) * S.gram k l) * ((N : D.host.E) • Q) l j =
      ∑ k, star (((N : D.host.E) • (Mᴴ *ᵥ s)) k) * S.gram k j := by
  have h : Matrix.vecMul (Matrix.vecMul (star s) S.gram) ((N : D.host.E) • Q) =
      Matrix.vecMul (star ((N : D.host.E) • (Mᴴ *ᵥ s))) S.gram := by
    rw [Matrix.vecMul_vecMul, Matrix.mul_smul, hQM, star_smul, star_natCast, Matrix.star_mulVec,
      Matrix.conjTranspose_conjTranspose, Matrix.vecMul_smul, Matrix.smul_vecMul, Matrix.vecMul_vecMul]
  have hj := congrFun h j
  simpa only [Matrix.vecMul, dotProduct, Pi.star_apply] using hj

theorem rat_natCast_smul {m n : ℕ} (N : ℕ) (X : Matrix (Fin m) (Fin n) D.host.E) :
    (rat ((N : D.host.E) • X) : Mx D m n) = N • (rat X : Mx D m n) := by
  ext i j
  simp [rat, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_natCast, nsmul_eq_mul]

end GlobalTheory.ProjXCols

namespace GlobalTheory.ProjXCols


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
theorem nsmul_projX_mem_latBig : OnStd fun {D} _ _ {sc} {G} _ F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∃ N : ℕ, 0 < N ∧ ∀ u ∈ latBig G (2 * ρ + 1), N • (u ⬝ (F.dB ρ h).jX ⬝ (F.dB ρ h).pX) ∈ latBig G (2 * ρ + 1) := by
  intro D hQ T L μ0 hL sc G W M hM F hF ρ h
  have hi : 2 * ρ + 1 < D.R.m := by omega
  have h0 : ∀ j, (Node.grid (2 * ρ + 1 + 1) 0 : Node) ≠ .grid 0 j := fun j hh => by
    injection hh with h'
    omega
  have hsd : IsSelfDualC (G.V (.grid (2 * ρ + 1 + 1) 0)) (G.Λ (.grid (2 * ρ + 1 + 1) 0)) :=
    (G.isV (show (Node.grid (2 * ρ + 1 + 1) 0 : Node).InRange D.R.m from ⟨hi, Nat.zero_le _⟩) h0).sd
  obtain ⟨N, hN, hNs⟩ := exists_nat_smul_mulVec_mem _ (selfDual_isFullLattice _ _ hsd)
    ((G.V (.grid (2 * ρ + 1 + 1) 0)).gram * (F.dB ρ h).e * (F.dB ρ h).e'ᴴ)ᴴ
  refine ⟨N, hN, fun u hu => ?_⟩
  have e1 : N • (u ⬝ (F.dB ρ h).jX ⬝ (F.dB ρ h).pX) =
      u ⬝ (rat ((N : D.host.E) • ((F.dB ρ h).e * (F.dB ρ h).qX)) :
        Mx D (G.V (.grid (2 * ρ + 1 + 1) 0)).rank (G.V (.grid (2 * ρ + 1 + 1) 0)).rank) := by
    rw [rat_natCast_smul, rat_mul, Matrix.mul_smul, Matrix.mul_assoc]
    rfl
  rw [e1]
  refine GlobalTheory.CoreRowLat.latO_mul_right _ (fun s hs => ⟨_, hNs s hs, fun j => ?_⟩) hu
  refine sum_mul_eq _ N _ _ ?_ s j
  simp only [HypDec.qX, Matrix.mul_assoc]

end GlobalTheory.ProjXCols
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NsmulProjectionXColumnsMemSelfDualLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nsmul_projection_xColumns_mem_selfDual_lattice : OnStd fun {D} _ _ {sc} {G} _ F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∃ N : ℕ, 0 < N ∧ ∀ u ∈ latBig G (2 * ρ + 1), N • (u ⬝ (F.dB ρ h).jX ⬝ (F.dB ρ h).pX) ∈ latBig G (2 * ρ + 1) := by
  first | exact @GlobalTheory.ProjXCols.nsmul_projX_mem_latBig | exact GlobalTheory.ProjXCols.nsmul_projX_mem_latBig | (intros; apply GlobalTheory.ProjXCols.nsmul_projX_mem_latBig <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EntireEqOfMonomialDerivationsAtZeroEq
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EntireEqOfMonomialDerivationsAtZeroEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section

namespace GlobalTheory.EntireJetUniq


open _root_.Formalism.L2.KerInert.PullbackComparison in
theorem eq_of_applyAt0_monomial_eq : ∀ {D : D7} {N N' : ℕ} (Φ Ψ : Formalism.MainNotions.TaylorLogMetric.VC D N N' → ℂ), Differentiable ℂ Φ → Differentiable ℂ Ψ → (∀ k : Formalism.MainNotions.GL3Theta.Idx D N N' →₀ ℕ, Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) Φ = Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) Ψ) → Φ = Ψ := by
  intro D N N' Φ Ψ hΦ hΨ h
  classical
  have aΦ := GlobalTheory.analyticOnNhd_of_differentiable_vc Φ hΦ
  have aΨ := GlobalTheory.analyticOnNhd_of_differentiable_vc Ψ hΨ
  have hmono : ∀ (k : Formalism.MainNotions.GL3Theta.Idx D N N' →₀ ℕ) (G : Formalism.MainNotions.TaylorLogMetric.VC D N N' → ℂ),
      Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) G =
        (k.prod fun _ n => (n.factorial : ℂ)) * Formalism.MainNotions.TaylorLogMetric.taylor D G k := by
    intro k G
    unfold Formalism.MainNotions.GL3Theta.applyAt0
    rw [MvPolynomial.support_monomial, if_neg one_ne_zero, Finset.sum_singleton, MvPolynomial.coeff_monomial,
      if_pos rfl, one_mul]
  have ht : ∀ α : Formalism.MainNotions.TaylorLogMetric.Mono D N N', Formalism.MainNotions.TaylorLogMetric.taylor D Φ α = Formalism.MainNotions.TaylorLogMetric.taylor D Ψ α := by
    intro α
    have h1 := h α
    rw [hmono, hmono] at h1
    have hne : (α.prod fun _ n => (n.factorial : ℂ)) ≠ 0 := by
      rw [Finsupp.prod]
      exact Finset.prod_ne_zero_iff.2 fun _ _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    exact mul_left_cancel₀ hne h1
  have hd : ∀ (n : ℕ) (z : Formalism.MainNotions.TaylorLogMetric.VC D N N'),
      iteratedFDeriv ℂ n Φ 0 (fun _ => z) = iteratedFDeriv ℂ n Ψ 0 (fun _ => z) := by
    intro n z
    rw [iter_expand, iter_expand]
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [iter_eq_taylor D Φ aΦ κ (ak D κ) (toMultiset_ak D κ).symm,
      iter_eq_taylor D Ψ aΨ κ (ak D κ) (toMultiset_ak D κ).symm, ht]
  obtain ⟨p, r, hp⟩ := aΦ 0 (Set.mem_univ _)
  obtain ⟨q, s, hq⟩ := aΨ 0 (Set.mem_univ _)
  refine aΦ.eq_of_eventuallyEq aΨ (z₀ := 0) ?_
  have hball : Metric.eball (0 : Formalism.MainNotions.TaylorLogMetric.VC D N N') (min r s) ∈ nhds 0 :=
    Metric.eball_mem_nhds 0 (lt_min hp.r_pos hq.r_pos)
  filter_upwards [hball] with y hy
  have hy1 : y ∈ Metric.eball (0 : Formalism.MainNotions.TaylorLogMetric.VC D N N') r :=
    Metric.eball_subset_eball (min_le_left _ _) hy
  have hy2 : y ∈ Metric.eball (0 : Formalism.MainNotions.TaylorLogMetric.VC D N N') s :=
    Metric.eball_subset_eball (min_le_right _ _) hy
  have s1 := hp.hasSum_iteratedFDeriv hy1
  have s2 := hq.hasSum_iteratedFDeriv hy2
  simp only [zero_add] at s1 s2
  simp only [hd] at s1
  exact s1.unique s2

end GlobalTheory.EntireJetUniq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EntireEqOfMonomialDerivationsAtZeroEqStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.entire_eq_of_monomial_derivations_at_zero_eq : ∀ {D : D7} {N N' : ℕ} (Φ Ψ : Formalism.MainNotions.TaylorLogMetric.VC D N N' → ℂ), Differentiable ℂ Φ → Differentiable ℂ Ψ → (∀ k : Formalism.MainNotions.GL3Theta.Idx D N N' →₀ ℕ, Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) Φ = Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) Ψ) → Φ = Ψ := by
  first | exact @GlobalTheory.EntireJetUniq.eq_of_applyAt0_monomial_eq | exact GlobalTheory.EntireJetUniq.eq_of_applyAt0_monomial_eq | (intros; apply GlobalTheory.EntireJetUniq.eq_of_applyAt0_monomial_eq <;> assumption)
end
end
