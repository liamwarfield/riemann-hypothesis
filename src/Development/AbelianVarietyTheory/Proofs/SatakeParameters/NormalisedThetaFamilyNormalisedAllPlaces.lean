module

public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.LocNormAmbOfOf
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.SelfDualComap
public import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.NormInter
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CurveIdealBaseThetaVectorNormalisedEveryPlace
public import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.NormPow
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntWAPlaces
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntEasy
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntPull
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.FinalEq

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalisedThetaFamilyNormalisedAtStandardPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalNormalisationTensorPowers
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalNormalisationTensorPowers
namespace GlobalTheory

theorem locNormPow_tensorPowers : Formalism.L2.AlgTh.LocNormPow := Formalism.L2.AlgTh.local_norm_power

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalNormalisationTensorPowersStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localNormalisation_tensorPowers : Formalism.L2.AlgTh.LocNormPow := by
  first | exact @GlobalTheory.locNormPow_tensorPowers | exact GlobalTheory.locNormPow_tensorPowers | (intros; apply GlobalTheory.locNormPow_tensorPowers <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalNormalisationIntertwinerPrimeIndex
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalNormalisationIntertwinerPrimeIndex
namespace GlobalTheory

theorem locNormInter : Formalism.L2.AlgTh.LocNormInter := Formalism.L2.AlgTh.local_norm_intertwiner

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalNormalisationIntertwinerPrimeIndexStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localNormalisation_intertwiner_prime_index : Formalism.L2.AlgTh.LocNormInter := by
  first | exact @GlobalTheory.locNormInter | exact GlobalTheory.locNormInter | (intros; apply GlobalTheory.locNormInter <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalNormalizationIntegralScalar
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalNormalizationIntegralScalar
namespace GlobalTheory

open Formalism.L2.AlgTh

theorem tensorFourthPower_smul {n : Type} [Fintype n] [DecidableEq n] (c : ℂ) (θ : (n → ℂ) → ℂ) :
    Formalism.L2.Th1.H.tens4 (c • θ) = c ^ 4 • Formalism.L2.Th1.H.tens4 θ := by
  funext z
  simp only [Formalism.L2.Th1.H.tens4, Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem locNormScale : LocNormScale := by
  intro a₀ b₀ dK ha hdK lam hlam n _ _ h Λ θ p _ ι c hc hLN
  obtain ⟨g₁, ε, hiso, hp, hidx, hε, heq⟩ := hLN
  refine ⟨g₁, c ^ 4 * ε, hiso, hp, hidx, ?_, ?_⟩
  · rw [map_mul, map_pow, norm_mul, norm_pow]
    have h0 : 0 ≤ ‖ι c‖ := norm_nonneg _
    have h4 : ‖ι c‖ ^ 4 ≤ 1 := pow_le_one₀ h0 hc
    calc ‖ι c‖ ^ 4 * ‖ι ε‖ ≤ 1 * 1 := mul_le_mul h4 hε (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · rw [tensorFourthPower_smul, heq, smul_smul]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalNormalizationIntegralScalarStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localNormalization_integral_scalar : Formalism.L2.AlgTh.LocNormScale := by
  first | exact @GlobalTheory.locNormScale | exact GlobalTheory.locNormScale | (intros; apply GlobalTheory.locNormScale <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalisedThetaFamilyNormalisedAtStandardPrime
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)

noncomputable section
open scoped BigOperators ComplexConjugate

namespace GlobalTheory.ThLoc.LocStd

open Formalism.L2.Th1.H (Sesq IsSelfDual IsHerm dualLat altE Th alphaQ blk4 pow4 slice imgLat)
open Formalism.L2.Th1.F (cmTheta)
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

theorem cmTheta_odd (b : ℤ) (hb : Odd b) (d : ℕ) : ∃ k : ℤ, cmTheta b d = cmTheta 1 d + (k : ℂ) := by
  obtain ⟨k, rfl⟩ := hb
  refine ⟨k, ?_⟩
  simp only [cmTheta]
  push_cast
  ring

theorem stable_of_one {V : Type*} [AddCommGroup V] [Module ℂ V] (Λ : AddSubgroup V) (d : ℕ)
    (h : ∀ x ∈ Λ, cmTheta 1 d • x ∈ Λ) (b : ℤ) (hb : Odd b) : ∀ x ∈ Λ, cmTheta b d • x ∈ Λ := by
  intro x hx
  obtain ⟨k, hk⟩ := cmTheta_odd b hb d
  rw [hk, add_smul]
  refine Λ.add_mem (h x hx) ?_
  rw [Int.cast_smul_eq_zsmul]
  exact Λ.zsmul_mem hx k

theorem hermitianSelfDual_of_fourfoldBlock {n : Type} [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ))
    (hsd : IsSelfDual (matH (blk4 h)) (pow4 Λ)) : IsSelfDual (matH h) Λ := by
  have key : ∀ (x : n → ℂ) (y : Fin 4 × n → ℂ),
      altE (matH (blk4 h)) (Formalism.L2.Th1.H.CmData.embA 0 x) y = altE (matH h) x (slice 0 y) := by
    intro x y
    simp only [altE, Formalism.L2.Th1.H.matrixForm_fourfoldBlock, Formalism.L2.Th1.H.CmData.slice_embA]
    rw [Finset.sum_eq_single (0 : Fin 4)]
    · simp
    · intro b _ hb
      simp [hb]
    · intro hh
      exact absurd (Finset.mem_univ _) hh
  ext x
  constructor
  · intro hx
    have h1 : Formalism.L2.Th1.H.CmData.embA 0 x ∈ dualLat (matH (blk4 h)) (pow4 Λ) := by
      intro y hy
      obtain ⟨m, hm⟩ := hx (slice 0 y) (hy 0)
      exact ⟨m, by rw [key, hm]⟩
    rw [hsd] at h1
    have h2 := h1 0
    rwa [Formalism.L2.Th1.H.CmData.slice_embA, if_pos rfl] at h2
  · intro hx y hy
    have h1 : Formalism.L2.Th1.H.CmData.embA 0 x ∈ dualLat (matH (blk4 h)) (pow4 Λ) := by
      rw [hsd]
      exact Formalism.L2.Th1.H.CmData.embA_mem Λ 0 hx
    obtain ⟨m, hm⟩ := h1 _ (Formalism.L2.Th1.H.CmData.embA_mem Λ 0 hy)
    refine ⟨m, ?_⟩
    rw [key, Formalism.L2.Th1.H.CmData.slice_embA, if_pos rfl] at hm
    exact hm

section Base

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ)

theorem selfDual_fourfold_curveIdeal_lattice (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) :
    IsSelfDual (matH (blk4 (hOne B.L D.what₂.Tau))) (pow4 B.lamM) := by
  have h := ((B.latAll hcc hδ (base_linkage_nonempty D cc δ B)).1 2 2 _ _
    (Formalism.MainNotions.GlobalTheoryTheory.Inhab.Adm_std D 2 2 even_two even_two)).1
  rw [show TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ) = _ from B.areaOK, show TaylorLogMetric.La D B.tor _ _ = _ from B.lat0OK 2 2] at h
  have h2 := SO.selfDual_img _ _ (SO.reix D.what₂.Tau) (SO.reix_isom B.L D.what₂.Tau) _ h
  rw [SO.reix_pow] at h2
  exact h2

theorem selfDual_lamM (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) :
    IsSelfDual (matH (hOne B.L D.what₂.Tau)) B.lamM :=
  hermitianSelfDual_of_fourfoldBlock _ _ (selfDual_fourfold_curveIdeal_lattice B hcc hδ)

theorem stable_lamM (b : ℤ) (hb : Odd b) : ∀ x ∈ B.lamM, cmTheta b D.host.d • x ∈ B.lamM := by
  refine stable_of_one _ _ (fun x hx => ?_) b hb
  have := SO.lamMM_smul (AR.om D) hx
  rw [← SO.theta_eq] at this
  exact this

end Base

end GlobalTheory.ThLoc.LocStd

namespace GlobalTheory.ThLoc.LocStd

open Formalism.L2.Th1.H (Sesq IsSelfDual IsHerm dualLat altE Th alphaQ blk4 pow4 slice imgLat)
open Formalism.L2.Th1.F (cmTheta)

section Reindex₂

variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (σ : n' ≃ n)

abbrev reixE : (n' → ℂ) ≃ₗ[ℂ] (n → ℂ) := LinearEquiv.funCongrLeft ℂ ℂ σ.symm

theorem matH_reix (h : Matrix n n ℂ) (h' : Matrix n' n' ℂ) (hh : ∀ i j, h' i j = h (σ i) (σ j)) (x y : n' → ℂ) :
    matH h' x y = matH h (reixE σ x) (reixE σ y) := by
  show (∑ i, ∑ j, x i * h' i j * conj (y j)) = ∑ i, ∑ j, x (σ.symm i) * h i j * conj (y (σ.symm j))
  rw [← Equiv.sum_comp σ.symm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Equiv.sum_comp σ.symm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hh, σ.apply_symm_apply, σ.apply_symm_apply]

theorem locNorm_reix (a₀ : ℕ) (b₀ c₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0)
    (hcm : CmOK a₀ b₀ c₀ dK) (h : Matrix n n ℂ) (h' : Matrix n' n' ℂ) (hh : ∀ i j, h' i j = h (σ i) (σ j))
    (Λ : AddSubgroup (n → ℂ)) (hSD : IsSelfDual (matH h) Λ) (hSt : ∀ x ∈ Λ, cmTheta b₀ dK • x ∈ Λ)
    (θ : (n → ℂ) → ℂ) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p])
    (H : LocNorm a₀ b₀ dK ha hdK lam hlam h Λ θ p ι) :
    LocNorm a₀ b₀ dK ha hdK lam hlam h' (Λ.comap (reixE σ).toLinearMap.toAddMonoidHom) (fun z => θ (reixE σ z)) p ι := by
  obtain ⟨g₁, ε, hiso, hnd, hidx, hε, hker⟩ := H
  set σ₄ : Fin 4 × n' ≃ Fin 4 × n := Equiv.prodCongr (Equiv.refl _) σ with hσ₄
  set E4 := reixE σ₄ with hE4
  set L₀ := cmL a₀ b₀ dK ha hdK lam hlam with hL₀
  have hblk : ∀ w w', blk4 h' w w' = blk4 h (σ₄ w) (σ₄ w') := by
    intro w w'
    simp only [blk4, hσ₄, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_fst, Prod.map_snd, id, hh]
  have hstd : ∀ w w' : Fin 4 × n', (((Formalism.L2.Th1.F.area L₀ : ℝ) : ℂ)⁻¹ • (1 : Matrix (Fin 4 × n') (Fin 4 × n') ℂ)) w w' =
      (((Formalism.L2.Th1.F.area L₀ : ℝ) : ℂ)⁻¹ • (1 : Matrix (Fin 4 × n) (Fin 4 × n) ℂ)) (σ₄ w) (σ₄ w') := by
    intro w w'
    simp only [Matrix.smul_apply, Matrix.one_apply, σ₄.injective.eq_iff]
  have hHs : ∀ x y, Formalism.L2.Th1.H.stdH L₀ (Fin 4 × n') x y = Formalism.L2.Th1.H.stdH L₀ (Fin 4 × n) (E4 x) (E4 y) :=
    matH_reix σ₄ _ _ hstd
  have hHb : ∀ x y, matH (blk4 h') x y = matH (blk4 h) (E4 x) (E4 y) := matH_reix σ₄ _ _ hblk
  let g₁' : (Fin 4 × n' → ℂ) ≃ₗ[ℂ] (Fin 4 × n' → ℂ) := E4.trans (g₁.trans E4.symm)
  have hg : ∀ z, E4 (g₁' z) = g₁ (E4 z) := fun z => by simp [g₁']
  have hP : pow4 (Λ.comap (reixE σ).toLinearMap.toAddMonoidHom) = (pow4 Λ).comap E4.toLinearMap.toAddMonoidHom := by
    ext z
    exact Iff.rfl
  have hS : Formalism.L2.Th1.H.stdLat L₀ (Fin 4 × n') =
      (Formalism.L2.Th1.H.stdLat L₀ (Fin 4 × n)).comap E4.toLinearMap.toAddMonoidHom := by
    ext z
    simp only [Formalism.L2.Th1.H.stdLat, AddSubgroup.mem_comap, AddSubgroup.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro hz w
      exact hz _
    · intro hz w
      have h1 := hz (σ₄ w)
      have e : (E4.toLinearMap.toAddMonoidHom z) (σ₄ w) = z w := by
        show z (σ₄.symm (σ₄ w)) = z w
        rw [σ₄.symm_apply_apply]
      rwa [e] at h1
  have hI : imgLat (g₁' : (Fin 4 × n' → ℂ) →ₗ[ℂ] (Fin 4 × n' → ℂ)) (pow4 (Λ.comap (reixE σ).toLinearMap.toAddMonoidHom)) =
      (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)).comap E4.toLinearMap.toAddMonoidHom := by
    rw [hP]
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨E4 x, hx, (hg x).symm⟩
    · rintro ⟨y, hy, hyz⟩
      refine ⟨E4.symm y, ?_, ?_⟩
      · show E4 (E4.symm y) ∈ pow4 Λ
        rw [LinearEquiv.apply_symm_apply]
        exact hy
      · show g₁' (E4.symm y) = z
        apply E4.injective
        rw [hg, LinearEquiv.apply_symm_apply]
        exact hyz
  have hnz : Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat L₀ (Fin 4 × n))
      (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) ≠ 0 := fun h0 => hnd (h0 ▸ dvd_zero p)
  have SD := Formalism.L2.Th1.H.stdDataCm a₀ b₀ c₀ dK ha hdK lam hlam hcm.1 hcm.2.1 hcm.2.2.1 n h Λ g₁ hiso hSD hSt hnz hidx
  have hF := (Formalism.L2.Th1.H.product_theta_mem L₀ (lam * a₀) (Fin 4 × n) SD.per SD.half _ SD.betaStd).1.2
  have hF0 : Formalism.L2.Th1.H.F0 L₀ (lam * a₀) (Fin 4 × n') = fun v => Formalism.L2.Th1.H.F0 L₀ (lam * a₀) (Fin 4 × n) (E4 v) := by
    funext v
    exact (Equiv.prod_comp σ₄.symm (fun w' => Formalism.L2.Th1.F.th0 L₀ (lam * a₀ / 2) (v w'))).symm
  have hHerm : IsHerm (Formalism.L2.Th1.H.stdH L₀ (Fin 4 × n)) := by
    intro x y
    show (∑ i, ∑ j, y i * _ * conj (x j)) = conj (∑ i, ∑ j, x i * _ * conj (y j))
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, map_sum, map_mul, Complex.conj_conj, map_inv₀, Complex.conj_ofReal]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hα : ∀ x, alphaQ (Real.sqrt dK / 2) (Formalism.L2.Th1.H.stdH L₀ (Fin 4 × n')) x =
      alphaQ (Real.sqrt dK / 2) (Formalism.L2.Th1.H.stdH L₀ (Fin 4 × n)) (E4 x) := by
    intro x
    simp only [alphaQ, Formalism.L2.Th1.H.qOf, hHs]
  have e1 := Formalism.L2.Ker.KS.inter_pb E4 _ _ hHs hHerm (Formalism.L2.Th1.H.stdLat L₀ (Fin 4 × n))
    (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) _ _ (fun x _ => hα x) (fun x _ => hα x) SD.betaSemi hnz _ hF
  refine ⟨g₁', ε, ?_, ?_, ?_, hε, ?_⟩
  · intro x y
    show Formalism.L2.Th1.H.stdH L₀ (Fin 4 × n') (g₁' x) (g₁' y) = matH (blk4 h') x y
    rw [hHs, hg, hg, hHb]
    exact hiso (E4 x) (E4 y)
  · rw [hS, hI, Formalism.L2.Ker.KS.relIdx_pb]
    exact hnd
  · rw [hS, hI, Formalism.L2.Ker.KS.relIdx_pb]
    exact hidx
  · funext z
    have t1 : Formalism.L2.Th1.H.tens4 (fun z => θ (reixE σ z)) z = Formalism.L2.Th1.H.tens4 θ (E4 z) := rfl
    rw [t1, hker]
    simp only [Pi.smul_apply, smul_eq_mul]
    congr 1
    unfold Formalism.L2.Th1.H.kernel4
    rw [hS, hI, hF0]
    have e2 := congrFun e1 (g₁' z)
    rw [hg] at e2
    exact e2.symm

end Reindex₂

section Main

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem hOne_reix {X : Fields} (s : Seam D X) (L : PeriodPair) (i j : X.Tau) :
    hOne L X.Tau i j = hOne L D.what₂.Tau (s.iT i) (s.iT j) := by
  simp only [hOne, Matrix.smul_apply, Matrix.one_apply, s.iT.injective.eq_iff]

theorem alphaQ_reix {X : Fields} (s : Seam D X) (L : PeriodPair) (c : ℝ) (x : X.Tau → ℂ) :
    alphaQ c (matH (hOne L X.Tau)) x = alphaQ c (matH (hOne L D.what₂.Tau)) (reixE s.iT x) := by
  simp only [alphaQ, Formalism.L2.Th1.H.qOf, matH_reix s.iT _ _ (hOne_reix s L)]

theorem latAt_std : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsChi D χ → ∀ (X : Fields) (s : Seam D X), s.Ok → ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0), CmOK a₀ b₀ c₀ D.host.d → (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), TaylorLogMetric.admitted D N N' L L' → ∀ (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]), TaylorLogMetric.EqAt D p (StandardLatticesGL3.stdL D N) L → TaylorLogMetric.EqAt D p (StandardLatticesGL3.stdL D N') L' → GlobalTheory.ThLoc.LatAt a₀ b₀ c₀ D.host.d ha hd lam hlam (Formalism.L2.AlgTh.hSc X.Tau N N' (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹) (s.laF B.tor L L') (fun z => B.eNat χ N N' L L' (s.flatV N N' z)) p ι := by
  intro D cc δ hcc hδ B χ hχ X s hok a₀ b₀ c₀ ha hd lam hlam hcm hl N N' L L' hA p _ ι hL hL'
  have hb : Odd b₀ := Formalism.L2.Ker.KS.Lat.odd_of_cmOK hcm
  set B' := Formalism.L2.Ker.KS.cmBase B a₀ b₀ c₀ ha hd lam hlam hcm hl with hB'

  have hω : (B.ω₀ - lam * a₀) / 2 ∈ (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice := by
    have e : (1 - Complex.I * (Real.sqrt D.host.d : ℂ)) / 2 = 1 - cmTheta 1 D.host.d := by
      rw [Formalism.L2.Ker.KS.theta_val']; ring
    have h := Formalism.L2.Ker.KS.half_period_unique_CM a₀ b₀ c₀ D.host.d ha hd lam hlam hcm (B.ω₀ / 2)
      ((Formalism.L2.Ker.KS.mem_lam_iff a₀ b₀ ha hd lam hlam hl _).1 B.t0.1)
      (by rw [← Formalism.L2.Ker.KS.mem_lam_iff a₀ b₀ ha hd lam hlam hl, Formalism.L2.Ker.KS.theta_val']; exact B.t0.2.1)
      (by rw [← Formalism.L2.Ker.KS.mem_lam_iff a₀ b₀ ha hd lam hlam hl, ← e]; exact B.t0.2.2)
    have e2 : (B.ω₀ - lam * a₀) / 2 = B.ω₀ / 2 - lam * a₀ / 2 := by ring
    rw [e2]
    exact h
  have hE : B.eNat χ = B'.eNat χ := Formalism.L2.Ker.KS.eNat_reBase B _ hl _ _ hω χ
  have hT : B'.tor = B.tor := rfl

  have hH : ∀ x y, matH (hOne B'.L X.Tau) x y = matH (hOne B'.L D.what₂.Tau) (reixE s.iT x) (reixE s.iT y) :=
    matH_reix s.iT _ _ (hOne_reix s B'.L)
  have hSDM : IsSelfDual (matH (hOne B'.L X.Tau)) (Formalism.L2.Ker.KS.lamM' s B') :=
    Formalism.L2.Ker.KS.selfDual_pb (reixE s.iT) _ _ hH (selfDual_lamM B' hcc hδ)
  have hStM : ∀ x ∈ Formalism.L2.Ker.KS.lamM' s B', cmTheta b₀ D.host.d • x ∈ Formalism.L2.Ker.KS.lamM' s B' := by
    intro x hx
    show reixE s.iT (cmTheta b₀ D.host.d • x) ∈ B'.lamM
    rw [map_smul]
    exact stable_lamM B' b₀ hb _ hx
  have hThM : Formalism.L2.Ker.KS.thM' s B' ∈ Th (matH (hOne B'.L X.Tau))
      (alphaQ (Real.sqrt D.host.d / 2) (matH (hOne B'.L X.Tau))) (Formalism.L2.Ker.KS.lamM' s B') :=
    Formalism.L2.Ker.KS.th_pb (reixE s.iT) _ _ hH (fun x _ => alphaQ_reix s B'.L _ x)
      (B'.thMM_spec (B'.stdOK hcc hδ)).1
  have hMM0 := GlobalTheory.T.curveIdeal_baseThetaVector_normalised_every_place D cc δ hcc hδ B' a₀ b₀ c₀ ha hd lam hlam hcm
    (Formalism.L2.Ker.KS.cmBase_isCm B a₀ b₀ c₀ ha hd lam hlam hcm hl) p ι
  have hMM : LocNorm a₀ b₀ D.host.d ha hd lam hlam (hOne B'.L X.Tau) (Formalism.L2.Ker.KS.lamM' s B')
      (Formalism.L2.Ker.KS.thM' s B') p ι :=
    locNorm_reix s.iT a₀ b₀ c₀ D.host.d ha hd lam hlam hcm _ _ (hOne_reix s B'.L) _ (selfDual_lamM B' hcc hδ)
      (stable_lamM B' b₀ hb) _ p ι hMM0

  have hχu : ‖ι (Base.chiFac χ N N' L L')‖ ≤ 1 := by
    let lm : TaylorLogMetric.Qbar →+* ℂ_[p] := (ι : ℂ →+* ℂ_[p]).comp (TaylorLogMetric.Qbar).val.toRingHom
    obtain ⟨h1, h2⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC.chiFacUnit χ hχ p lm N N' L L' hA hL hL'
    have e : TaylorLogMetric.lamC lm (Base.chiFac χ N N' L L') = ι (Base.chiFac χ N N' L L') := by
      simp only [TaylorLogMetric.lamC, dif_pos h1]
      rfl
    rw [← e, h2]
  have key := Formalism.L2.Ker.KS.locNorm_thF_of s B' GlobalTheory.T.localNormalization_integral_scalar GlobalTheory.T.localNormalisation_tensorPowers GlobalTheory.T.localNormalisation_intertwiner_prime_index χ a₀ b₀ c₀ ha hd lam hlam p ι
    hcc hδ hcm hSDM hStM hThM hMM (Formalism.L2.Ker.KS.Lat.posDef_hSc (Formalism.L2.Ker.KS.Lat.sc_pos B) N N')
    (fun L L' h => Formalism.L2.Ker.KS.Lat.isLat_laF s B' hcc hδ h)
    (fun L L' h x hx => Formalism.L2.Ker.KS.Lat.theta_laF s B' hb hx) hA hL hL' hχu
  rw [← hE, hT] at key
  exact ⟨hcm, Formalism.L2.Ker.KS.Lat.selfDual_laF s B hcc hδ hA, fun x hx => Formalism.L2.Ker.KS.Lat.theta_laF s B hb hx,
    Formalism.L2.Ker.KS.Lat.eNat_laF s B hcc hδ χ hA, key⟩

end Main

end GlobalTheory.ThLoc.LocStd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalisedThetaFamilyNormalisedAtStandardPrimeStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisedThetaFamily_normalised_at_standardPrime : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsChi D χ → ∀ (X : Fields) (s : Seam D X), s.Ok → ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0), CmOK a₀ b₀ c₀ D.host.d → (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), TaylorLogMetric.admitted D N N' L L' → ∀ (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]), TaylorLogMetric.EqAt D p (StandardLatticesGL3.stdL D N) L → TaylorLogMetric.EqAt D p (StandardLatticesGL3.stdL D N') L' → GlobalTheory.ThLoc.LatAt a₀ b₀ c₀ D.host.d ha hd lam hlam (Formalism.L2.AlgTh.hSc X.Tau N N' (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹) (s.laF B.tor L L') (fun z => B.eNat χ N N' L L' (s.flatV N N' z)) p ι := by
  first | exact @GlobalTheory.ThLoc.LocStd.latAt_std | exact GlobalTheory.ThLoc.LocStd.latAt_std | (intros; apply GlobalTheory.ThLoc.LocStd.latAt_std <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalNormalisationTransportIsometry
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalNormalisationTransportIsometry
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

noncomputable section
open scoped BigOperators ComplexConjugate

namespace GlobalTheory.ThLoc.LocPull

open Formalism.L2.Th1.H (blk4 pow4 slice imgLat tens4 kernel4)

variable {n : Type} [Fintype n] [DecidableEq n]

def diagonalPowFourEquiv (φ : (n → ℂ) ≃ₗ[ℂ] (n → ℂ)) : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ) where
  toFun z w := φ (slice w.1 z) w.2
  invFun z w := φ.symm (slice w.1 z) w.2
  map_add' x y := by
    funext w
    have e : slice w.1 (x + y) = slice w.1 x + slice w.1 y := rfl
    simp only [e, map_add (f := _), Pi.add_apply]
  map_smul' c x := by
    funext w
    have e : slice w.1 (c • x) = c • slice w.1 x := rfl
    simp only [e, map_smul, Pi.smul_apply, RingHom.id_apply]
  left_inv z := by
    funext w
    have e : slice w.1 (fun w' : Fin 4 × n => φ (slice w'.1 z) w'.2) = φ (slice w.1 z) := rfl
    simp only [e, LinearEquiv.symm_apply_apply]
    rfl
  right_inv z := by
    funext w
    have e : slice w.1 (fun w' : Fin 4 × n => φ.symm (slice w'.1 z) w'.2) = φ.symm (slice w.1 z) := rfl
    simp only [e, LinearEquiv.apply_symm_apply]
    rfl

theorem slice_pow4E (φ : (n → ℂ) ≃ₗ[ℂ] (n → ℂ)) (a : Fin 4) (z : Fin 4 × n → ℂ) :
    slice a (diagonalPowFourEquiv φ z) = φ (slice a z) := rfl

theorem fourCopiesHermitianForm_eq_sum_blocks (h : Matrix n n ℂ) (x y : Fin 4 × n → ℂ) :
    matH (blk4 h) x y = ∑ a : Fin 4, matH h (slice a x) (slice a y) := by
  show (∑ w, ∑ w', x w * blk4 h w w' * conj (y w')) = ∑ a : Fin 4, ∑ i, ∑ j, x (a, i) * h i j * conj (y (a, j))
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a]
  · simp [blk4]
  · intro b _ hb
    simp [blk4, Ne.symm hb]
  · intro hh
    exact absurd (Finset.mem_univ _) hh

theorem blockwiseActionOnFourCopies_isometry (φ : (n → ℂ) ≃ₗ[ℂ] (n → ℂ)) (h : Matrix n n ℂ)
    (hφ : IsIsom (matH h) (matH h) (φ : (n → ℂ) →ₗ[ℂ] (n → ℂ))) (x y : Fin 4 × n → ℂ) :
    matH (blk4 h) (diagonalPowFourEquiv φ x) (diagonalPowFourEquiv φ y) = matH (blk4 h) x y := by
  rw [fourCopiesHermitianForm_eq_sum_blocks, fourCopiesHermitianForm_eq_sum_blocks]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [slice_pow4E, slice_pow4E]
  exact hφ _ _

theorem imgLat_pull (φ : (n → ℂ) ≃ₗ[ℂ] (n → ℂ)) (Λ : AddSubgroup (n → ℂ))
    (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)) :
    imgLat (((diagonalPowFourEquiv φ).trans g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)) : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ))
        (pow4 (Λ.comap φ.toLinearMap.toAddMonoidHom)) =
      imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨diagonalPowFourEquiv φ x, fun a => hx a, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(diagonalPowFourEquiv φ).symm x, fun a => ?_, ?_⟩
    · show φ (slice a ((diagonalPowFourEquiv φ).symm x)) ∈ Λ
      rw [← slice_pow4E, LinearEquiv.apply_symm_apply]
      exact hx a
    · show g (diagonalPowFourEquiv φ ((diagonalPowFourEquiv φ).symm x)) = g x
      rw [LinearEquiv.apply_symm_apply]

theorem locNorm_pull : ∀ (a₀ : ℕ) (b₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0) (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)) (θ : (n → ℂ) → ℂ) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (φ : (n → ℂ) ≃ₗ[ℂ] (n → ℂ)), IsIsom (matH h) (matH h) (φ : (n → ℂ) →ₗ[ℂ] (n → ℂ)) → LocNorm a₀ b₀ dK ha hdK lam hlam h Λ θ p ι → LocNorm a₀ b₀ dK ha hdK lam hlam h (Λ.comap φ.toLinearMap.toAddMonoidHom) (fun z => θ (φ z)) p ι := by
  intro a₀ b₀ dK ha hdK lam hlam n _ _ h Λ θ p _ ι φ hφ H
  obtain ⟨g₁, ε, hiso, hnd, hidx, hε, hker⟩ := H
  have hI := imgLat_pull φ Λ g₁
  refine ⟨(diagonalPowFourEquiv φ).trans g₁, ε, ?_, ?_, ?_, hε, ?_⟩
  · intro x y
    exact (hiso (diagonalPowFourEquiv φ x) (diagonalPowFourEquiv φ y)).trans (blockwiseActionOnFourCopies_isometry φ h hφ x y)
  · rw [hI]
    exact hnd
  · rw [hI]
    exact hidx
  · funext z
    have t1 : tens4 (fun z => θ (φ z)) z = tens4 θ (diagonalPowFourEquiv φ z) := rfl
    rw [t1, hker]
    simp only [Pi.smul_apply]
    congr 1
    unfold kernel4
    rw [hI]
    rfl

end GlobalTheory.ThLoc.LocPull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalNormalisationTransportIsometryStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localNormalisation_transport_isometry : ∀ (a₀ : ℕ) (b₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0) (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)) (θ : (n → ℂ) → ℂ) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (φ : (n → ℂ) ≃ₗ[ℂ] (n → ℂ)), IsIsom (matH h) (matH h) (φ : (n → ℂ) →ₗ[ℂ] (n → ℂ)) → LocNorm a₀ b₀ dK ha hdK lam hlam h Λ θ p ι → LocNorm a₀ b₀ dK ha hdK lam hlam h (Λ.comap φ.toLinearMap.toAddMonoidHom) (fun z => θ (φ z)) p ι := by
  first | exact @GlobalTheory.ThLoc.LocPull.locNorm_pull | exact GlobalTheory.ThLoc.LocPull.locNorm_pull | (intros; apply GlobalTheory.ThLoc.LocPull.locNorm_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalisedThetaFamilyNormalisedAllPlaces
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

noncomputable section

namespace GlobalTheory.ThLoc.AllPlaces

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ}

theorem tPull_comp (γ₁ γ₂ : Matrix (Fin N) (Fin N) D.host.E) (γ₁' γ₂' : Matrix (Fin N') (Fin N') D.host.E)
    (z : TaylorLogMetric.VC D N N') :
    Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) γ₂ γ₂' (Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) γ₁ γ₁' z) =
      Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) (γ₁ * γ₂) (γ₁' * γ₂') z := by
  funext τ
  show (Matrix.conjTranspose (γ₂'.map (TaylorLogMetric.embT D τ)) *
      (Matrix.conjTranspose (γ₁'.map (TaylorLogMetric.embT D τ)) * Matrix.of (z τ) * γ₁.map (TaylorLogMetric.embT D τ)) *
      γ₂.map (TaylorLogMetric.embT D τ) : Matrix _ _ ℂ) =
    (Matrix.conjTranspose ((γ₁' * γ₂').map (TaylorLogMetric.embT D τ)) * Matrix.of (z τ) * (γ₁ * γ₂).map (TaylorLogMetric.embT D τ) : Matrix _ _ ℂ)
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem tPull_one (z : TaylorLogMetric.VC D N N') :
    Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) (1 : Matrix (Fin N) (Fin N) D.host.E)
      (1 : Matrix (Fin N') (Fin N') D.host.E) z = z := by
  funext τ
  show (Matrix.conjTranspose ((1 : Matrix (Fin N') (Fin N') D.host.E).map (TaylorLogMetric.embT D τ)) * Matrix.of (z τ) *
      (1 : Matrix (Fin N) (Fin N) D.host.E).map (TaylorLogMetric.embT D τ) : Matrix _ _ ℂ) = z τ
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.conjTranspose_one,
    Matrix.one_mul, Matrix.mul_one]
  rfl

theorem smulLat_star_smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) (hγ : star γ * γ = 1)
    (M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) :
    SDLat.smulLat (star γ) (SDLat.smulLat γ M) = M := by
  unfold SDLat.smulLat
  rw [← Submodule.map_comp]
  have h : ((Matrix.toLin' (star γ)).restrictScalars (𝓞 D.host.E)).comp ((Matrix.toLin' γ).restrictScalars (𝓞 D.host.E)) =
      LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    show Matrix.toLin' (star γ) (Matrix.toLin' γ x) = x
    rw [← Matrix.toLin'_mul_apply, hγ, Matrix.toLin'_one, LinearMap.id_apply]
  rw [h, Submodule.map_id]

theorem mem_La_smulLat_iff (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γ' : Matrix.unitaryGroup (Fin N') D.host.E)
    (M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (x : TaylorLogMetric.VC D N N') :
    x ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) M)
        (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) M') ↔
      Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) (γ : Matrix (Fin N) (Fin N) D.host.E)
        (γ' : Matrix (Fin N') (Fin N') D.host.E) x ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) M M' := by
  have h1 : star (γ : Matrix (Fin N) (Fin N) D.host.E) * γ = 1 := Matrix.mem_unitaryGroup_iff'.mp γ.2
  have h1' : star (γ' : Matrix (Fin N') (Fin N') D.host.E) * γ' = 1 := Matrix.mem_unitaryGroup_iff'.mp γ'.2
  have h2 : (γ : Matrix (Fin N) (Fin N) D.host.E) * star (γ : Matrix (Fin N) (Fin N) D.host.E) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp γ.2
  have h2' : (γ' : Matrix (Fin N') (Fin N') D.host.E) * star (γ' : Matrix (Fin N') (Fin N') D.host.E) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp γ'.2
  constructor
  · intro hx
    exact Formalism.L2.KerInert.ie_La_pull cc δ _ _ h1' M M' hx
  · intro hx
    have h3 : star (star (γ' : Matrix (Fin N') (Fin N') D.host.E)) * star (γ' : Matrix (Fin N') (Fin N') D.host.E) = 1 := by
      rw [star_star]; exact h2'
    have h := Formalism.L2.KerInert.ie_La_pull cc δ (star (γ : Matrix (Fin N) (Fin N) D.host.E))
      (star (γ' : Matrix (Fin N') (Fin N') D.host.E)) h3 (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) M)
      (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) M')
    rw [smulLat_star_smulLat _ h1, smulLat_star_smulLat _ h1'] at h
    have h4 := h hx
    rw [AddSubgroup.mem_comap] at h4
    have e : Formalism.L2.KerInert.ieTPullHom cc δ (star (γ : Matrix (Fin N) (Fin N) D.host.E))
        (star (γ' : Matrix (Fin N') (Fin N') D.host.E))
        (Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) (γ : Matrix (Fin N) (Fin N) D.host.E)
          (γ' : Matrix (Fin N') (Fin N') D.host.E) x) = x := by
      show Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) _ _ (Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) _ _ x) = x
      rw [tPull_comp, h2, h2', tPull_one]
    rw [e] at h4
    exact h4

end GlobalTheory.ThLoc.AllPlaces

namespace GlobalTheory.ThLoc.AllPlaces

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ}

theorem formV_eq_Hf (u v : TaylorLogMetric.VC D N N') :
    formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N' u v = TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) u v := rfl

def tPullLin (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (γ : Matrix (Fin N) (Fin N) D.host.E)
    (γ' : Matrix (Fin N') (Fin N') D.host.E) : TaylorLogMetric.VC D N N' →ₗ[ℂ] TaylorLogMetric.VC D N N' where
  toFun := Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) γ γ'
  map_add' := Formalism.L2.KerInert.ie_tPull_add cc δ γ γ'
  map_smul' := Formalism.L2.KerInert.ie_tPull_smul cc δ γ γ'

def tPullEquiv (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (γ : Matrix.unitaryGroup (Fin N) D.host.E)
    (γ' : Matrix.unitaryGroup (Fin N') D.host.E) : TaylorLogMetric.VC D N N' ≃ₗ[ℂ] TaylorLogMetric.VC D N N' :=
  LinearEquiv.ofLinearMap (tPullLin cc δ (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E))
    (tPullLin cc δ (star (γ : Matrix (Fin N) (Fin N) D.host.E)) (star (γ' : Matrix (Fin N') (Fin N') D.host.E)))
    (LinearMap.ext fun z => by
      show Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) _ _ (Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) _ _ z) = z
      rw [tPull_comp, Matrix.mem_unitaryGroup_iff'.mp γ.2, Matrix.mem_unitaryGroup_iff'.mp γ'.2, tPull_one])
    (LinearMap.ext fun z => by
      show Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) _ _ (Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) _ _ z) = z
      rw [tPull_comp, Matrix.mem_unitaryGroup_iff.mp γ.2, Matrix.mem_unitaryGroup_iff.mp γ'.2, tPull_one])

end GlobalTheory.ThLoc.AllPlaces


open GlobalTheory.ThLoc.AllPlaces in
attribute [local instance] Formalism.BasicNotions.Host.cmStar in
theorem GlobalTheory.ThLoc.latAt_all : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsChi D χ → ∀ (X : Fields) (s : Seam D X), s.Ok → ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0), CmOK a₀ b₀ c₀ D.host.d → (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), TaylorLogMetric.admitted D N N' L L' → ∀ (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]), GlobalTheory.ThLoc.LatAt a₀ b₀ c₀ D.host.d ha hd lam hlam (Formalism.L2.AlgTh.hSc X.Tau N N' (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹) (s.laF B.tor L L') (fun z => B.eNat χ N N' L L' (s.flatV N N' z)) p ι := by
  intro D cc δ hcc hδ B χ hχ X s hs a₀ b₀ c₀ ha hd lam hlam hcm hlat N N' L L' hA p _ ι
  have hp : p.Prime := Fact.out
  have hCM : PI.UG.IsCMUnram D.host.E := D.sp.cm.cmUnram
  obtain ⟨hN, hN', hL, hL'⟩ := hA
  obtain ⟨γ, M, hM, hEq, hLM⟩ := Formalism.L2.KerInert.wa_main Formalism.L2.KerInert.weak_approximation_places hCM p hp N L hL
  obtain ⟨γ', M', hM', hEq', hLM'⟩ := Formalism.L2.KerInert.wa_main Formalism.L2.KerInert.weak_approximation_places hCM p hp N' L' hL'
  have hAM : TaylorLogMetric.admitted D N N' M M' := ⟨hN, hN', hM, hM'⟩
  have hAL : TaylorLogMetric.admitted D N N' L L' := ⟨hN, hN', hL, hL'⟩
  have hStd := GlobalTheory.T.normalisedThetaFamily_normalised_at_standardPrime D cc δ hcc hδ B χ hχ X s hs a₀ b₀ c₀ ha hd lam hlam hcm hlat N N' M M' hAM p ι hEq hEq'

  let φ : (DVar X.Tau N N' → ℂ) ≃ₗ[ℂ] (DVar X.Tau N N' → ℂ) :=
    (s.flatV N N').trans ((tPullEquiv cc δ γ γ').trans (s.flatV N N').symm)
  have hφ : ∀ z, s.flatV N N' (φ z) = Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) (γ : Matrix (Fin N) (Fin N) D.host.E)
      (γ' : Matrix (Fin N') (Fin N') D.host.E) (s.flatV N N' z) := fun z => by
    show s.flatV N N' ((s.flatV N N').symm (tPullEquiv cc δ γ γ' (s.flatV N N' z))) = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  have hI : IsIsom (matH (Formalism.L2.AlgTh.hSc X.Tau N N' (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹))
      (matH (Formalism.L2.AlgTh.hSc X.Tau N N' (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹)) (φ : (DVar X.Tau N N' → ℂ) →ₗ[ℂ] _) := by
    intro x y
    show matH _ (φ x) (φ y) = _
    rw [KS.Lat.form_flat s, KS.Lat.form_flat s, hφ, hφ, formV_eq_Hf, formV_eq_Hf,
      Formalism.L2.KerInert.PullbackComparison.Hf_tPull cc δ _ _ (Matrix.mem_unitaryGroup_iff.mp γ.2) (Matrix.mem_unitaryGroup_iff.mp γ'.2)]
  have hloc := GlobalTheory.T.localNormalisation_transport_isometry a₀ b₀ D.host.d ha hd lam hlam (DVar X.Tau N N') _ (s.laF B.tor M M')
    (fun z => B.eNat χ N N' M M' (s.flatV N N' z)) p ι φ hI hStd.locNorm
  have hΛ : (s.laF B.tor M M').comap (φ : (DVar X.Tau N N' → ℂ) →ₗ[ℂ] _).toAddMonoidHom = s.laF B.tor L L' := by
    ext x
    show s.flatV N N' (φ x) ∈ TaylorLogMetric.La D B.tor M M' ↔ s.flatV N N' x ∈ TaylorLogMetric.La D B.tor L L'
    rw [hφ, hLM, hLM']
    exact (mem_La_smulLat_iff γ γ' M M' _).symm
  have hθ : (fun z => B.eNat χ N N' M M' (s.flatV N N' (φ z))) = fun z => B.eNat χ N N' L L' (s.flatV N N' z) := by
    funext z
    rw [hφ, hLM, hLM']
    have h := (Formalism.L2.PairingIndexBounds.Eq.SqG.eulerProduct_eq_of_curve_ideal B hcc hδ χ hχ).1 N N' ⟨M, hM⟩ ⟨M', hM'⟩ hN hN' γ γ'
    exact congrFun h (s.flatV N N' z)
  rw [hΛ] at hloc
  simp only [hθ] at hloc
  exact ⟨hcm, KS.Lat.selfDual_laF s B hcc hδ hAL, fun x hx => KS.Lat.theta_laF s B (KS.Lat.odd_of_cmOK hcm) hx,
    KS.Lat.eNat_laF s B hcc hδ χ hAL, hloc⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalisedThetaFamilyNormalisedAllPlacesStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisedThetaFamily_normalised_all_places : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsChi D χ → ∀ (X : Fields) (s : Seam D X), s.Ok → ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0), CmOK a₀ b₀ c₀ D.host.d → (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), TaylorLogMetric.admitted D N N' L L' → ∀ (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]), GlobalTheory.ThLoc.LatAt a₀ b₀ c₀ D.host.d ha hd lam hlam (Formalism.L2.AlgTh.hSc X.Tau N N' (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹) (s.laF B.tor L L') (fun z => B.eNat χ N N' L L' (s.flatV N N' z)) p ι := by
  first | exact @GlobalTheory.ThLoc.latAt_all | exact GlobalTheory.ThLoc.latAt_all | (intros; apply GlobalTheory.ThLoc.latAt_all <;> assumption)
end
