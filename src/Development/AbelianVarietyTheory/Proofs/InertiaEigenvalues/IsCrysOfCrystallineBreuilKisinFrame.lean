module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusSectionAcrisBreuilKisin
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatCastNeZeroPs

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrystallineOfInvariantUnitBcrisMatrix
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrystallineOfInvariantUnitBcrisMatrix
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim

theorem isCrys_of_bcris_matrix : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (U : Matrix (Fin d) (Fin d) (Per.Bcris l)), IsUnit U → (∀ g : ↥(GK K), (ρ g).val.map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U) → IsCrys (P.PD K) (qRep ρ) := by
  intro l _ K P AI T d ρ U hU hinv
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) := (P.PD K).finK₀
  haveI : Nontrivial P.R.B := by
    refine ⟨⟨(P.PD K).t, 0, fun h => (P.PD K).not_mem_filtration_two ?_⟩⟩
    rw [h, map_zero]
    exact Submodule.zero_mem _

  have hU' : IsUnit (U.map T.eB.symm) := by
    have := hU.map (T.eB.symm.mapMatrix (m := Fin d))
    simpa using this
  let Q : GL (Fin d) P.R.B := hU'.unit
  have hQ : (Q : Matrix (Fin d) (Fin d) P.R.B) = U.map T.eB.symm := hU'.unit_spec
  let b := Pi.basisFun ℚ_[l] (Fin d)
  have hmat : ∀ g : ↥(GK K), LinearMap.toMatrix b b (qRep ρ g) = (ρ g).val.map (algebraMap ℤ_[l] ℚ_[l]) := by
    intro g
    rw [LinearMap.toMatrix_eq_toMatrix']
    ext i j
    simp [qRep, LinearMap.toMatrix'_apply, Matrix.toLinAlgEquiv'_apply, Matrix.mulVec, dotProduct, Pi.single_apply]
  obtain ⟨e, -, -, he⟩ := GlobalTheory.tensorBasisCoords ℚ_[l] P.R.B (Fin d → ℚ_[l]) (Fin d) b
  have key := GlobalTheory.InertiaEigenvalues.finrank_invariants_eq_of_period_matrix ℚ_[l] ↥(K0 K) P.R.B ↥(GK K)
    (fun g => ((P.PD K).actB g).toRingEquiv.toRingHom) (Fin d)
    (fun g => (LinearMap.toMatrix b b (qRep ρ g)).map (algebraMap ℚ_[l] P.R.B))
    (fun x => ⟨fun h => (P.PD K).invB x h, by
      rintro ⟨c, rfl⟩ g
      exact ((P.PD K).actB g).commutes c⟩) Q
    (fun g => by
      apply (T.eB.mapMatrix (m := Fin d)).injective
      rw [map_mul, hmat g, hQ]
      have hA : T.eB.mapMatrix (((ρ g).val.map (algebraMap ℤ_[l] ℚ_[l])).map (algebraMap ℚ_[l] P.R.B)) =
          (ρ g).val.map (Per.zB l) := by
        ext i j
        simp only [RingEquiv.mapMatrix_apply, Matrix.map_apply]
        exact T.zB _
      have hB : T.eB.mapMatrix ((U.map T.eB.symm).map (((P.PD K).actB g).toRingEquiv.toRingHom)) =
          U.map (Per.σB (g : GQ l)) := by
        ext i j
        simp only [RingEquiv.mapMatrix_apply, Matrix.map_apply]
        change T.eB ((P.PD K).actB g (T.eB.symm (U i j))) = _
        rw [P.PD_actB, T.actB, RingEquiv.apply_symm_apply]
      have hC : T.eB.mapMatrix (U.map T.eB.symm) = U := by
        ext i j
        simp
      rw [hA, hB, hC]
      exact hinv g)
    ((Dcris (P.PD K) (qRep ρ)).map (e : (Fin d → ℚ_[l]) ⊗[ℚ_[l]] P.R.B →ₗ[ℚ_[l]] (Fin d → P.R.B)))
    (fun x => by
      obtain ⟨y, rfl⟩ := e.surjective x
      have h1 : e y ∈ (Dcris (P.PD K) (qRep ρ)).map (e : (Fin d → ℚ_[l]) ⊗[ℚ_[l]] P.R.B →ₗ[ℚ_[l]] (Fin d → P.R.B)) ↔
          y ∈ Dcris (P.PD K) (qRep ρ) := by
        constructor
        · rintro ⟨z, hz, hzy⟩
          have : z = y := e.injective hzy
          exact this ▸ hz
        · exact fun h => ⟨y, h, rfl⟩
      rw [h1]
      simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero]
      refine forall_congr' fun g => ?_
      have h2 := he (qRep ρ g) (((((P.PD K).actB g).toAlgHom.toLinearMap).restrictScalars ℚ_[l])) y
      have h3 : actVB (P.PD K) (qRep ρ) g y = TensorProduct.map (qRep ρ g)
          ((((P.PD K).actB g).toAlgHom.toLinearMap).restrictScalars ℚ_[l]) y := rfl
      rw [h3, ← e.injective.eq_iff, h2]
      rfl)
  rw [LinearEquiv.finrank_map_eq, Fintype.card_fin] at key
  rw [IsCrys, key, Module.finrank_fin_fun]

end GlobalTheory.BKLim
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrystallineOfInvariantUnitBcrisMatrixStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCrystalline_of_invariant_unit_bcris_matrix : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (U : Matrix (Fin d) (Fin d) (Per.Bcris l)), IsUnit U → (∀ g : ↥(GK K), (ρ g).val.map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U) → IsCrys (P.PD K) (qRep ρ) := by
  first | exact @GlobalTheory.BKLim.isCrys_of_bcris_matrix | exact GlobalTheory.BKLim.isCrys_of_bcris_matrix | (intros; apply GlobalTheory.BKLim.isCrys_of_bcris_matrix <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusEquationOfTwistedCocycleDefect
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusEquationOfTwistedCocycleDefect
namespace GlobalTheory.FrobeniusDefect

open Matrix

variable {R : Type} [CommRing R] {d : ℕ}

theorem nzd_mul {a b : R} (ha : ∀ x : R, a * x = 0 → x = 0) (hb : ∀ x : R, b * x = 0 → x = 0) :
    ∀ x : R, (a * b) * x = 0 → x = 0 :=
  fun x h => hb x (ha _ (by rw [← mul_assoc]; exact h))

theorem nzd_pow {a : R} (ha : ∀ x : R, a * x = 0 → x = 0) :
    ∀ n : ℕ, ∀ x : R, a ^ n * x = 0 → x = 0
  | 0 => fun x h => by simpa using h
  | n + 1 => by rw [pow_succ]; exact nzd_mul (nzd_pow ha n) ha

theorem nzd_unit {a : R} (ha : ∀ x : R, a * x = 0 → x = 0) (v : Rˣ) :
    ∀ x : R, (a * v) * x = 0 → x = 0 :=
  nzd_mul ha (fun x h => by simpa using congrArg (fun y => (↑v⁻¹ : R) * y) h)

theorem smul_cancel {c : R} (hc : ∀ x : R, c * x = 0 → x = 0)
    {M N : Matrix (Fin d) (Fin d) R} (h : c • M = c • N) : M = N := by
  ext i j
  have := congrArg (fun P => P i j) h
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  exact sub_eq_zero.mp (hc _ (by rw [mul_sub, this, sub_self]))

theorem mul_left_of {c : R} {P P' : Matrix (Fin d) (Fin d) R} (h : P * P' = c • 1)
    (X : Matrix (Fin d) (Fin d) R) : P * (P' * X) = c • X := by
  rw [← Matrix.mul_assoc, h, Matrix.smul_mul, Matrix.one_mul]

theorem left_cancel {c : R} (hc : ∀ x : R, c * x = 0 → x = 0)
    {P P' : Matrix (Fin d) (Fin d) R} (h : P' * P = c • 1)
    {X Y : Matrix (Fin d) (Fin d) R} (hXY : P * X = P * Y) : X = Y :=
  smul_cancel hc (by rw [← mul_left_of h X, ← mul_left_of h Y, hXY])

theorem mul_comm_of_nzd {c : R} (hc : ∀ x : R, c * x = 0 → x = 0)
    {M M' : Matrix (Fin d) (Fin d) R} (h : M * M' = c • 1) : M' * M = c • 1 := by
  have hdet : M.det * M'.det = c ^ d := by
    rw [← Matrix.det_mul, h, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  have hdM : ∀ x : R, M.det * x = 0 → x = 0 := fun x hx =>
    nzd_pow hc d x (by rw [← hdet, mul_comm M.det, mul_assoc, hx, mul_zero])
  have h0 : M * (M' * M - c • 1) = 0 := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, h, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.one_mul, sub_self]
  have h1 : M.det • (M' * M - c • 1) = M.det • (0 : Matrix (Fin d) (Fin d) R) := by
    calc M.det • (M' * M - c • 1)
          = (M.det • (1 : Matrix (Fin d) (Fin d) R)) * (M' * M - c • 1) := by
            rw [Matrix.smul_mul, Matrix.one_mul]
      _ = M.adjugate * M * (M' * M - c • 1) := by rw [Matrix.adjugate_mul]
      _ = M.det • (0 : Matrix (Fin d) (Fin d) R) := by rw [Matrix.mul_assoc, h0, Matrix.mul_zero, smul_zero]
  exact sub_eq_zero.mp (smul_cancel hdM h1)

theorem map_smul_one (f : R →+* R) (c : R) :
    (c • (1 : Matrix (Fin d) (Fin d) R)).map f = f c • (1 : Matrix (Fin d) (Fin d) R) := by
  ext i j
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

theorem map_smul' (f : R →+* R) (c : R) (M : Matrix (Fin d) (Fin d) R) :
    (c • M).map f = f c • M.map f := by
  ext i j
  simp

theorem frobenius_defect_eq (R : Type) [CommRing R] (φ σ : R →+* R) (d N k : ℕ) (lr e e₀ : R)
    (Q Q' B B' A₀ A₀' ε : Matrix (Fin d) (Fin d) R)
    (hlr : ∀ x : R, lr * x = 0 → x = 0) (hev : ∃ v : Rˣ, e = lr * v) (he₀v : ∃ v : Rˣ, e₀ = lr * v)
    (hφσ : ∀ x, φ (σ x) = σ (φ x)) (hφlr : φ lr = lr) (hσlr : σ lr = lr) (hσe₀ : σ e₀ = e₀)
    (hA₀σ : A₀.map σ = A₀)
    (hQQ' : Q * Q' = lr ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) R))
    (hBB' : B * B' = e ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) R))
    (hAA' : A₀ * A₀' = e₀ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) R))
    (hQA : e ^ N • (Q * A₀) = e₀ ^ N • (B * Q.map φ))
    (hεB : e ^ N • (ε * B.map σ) = σ e ^ N • (B * ε.map φ)) :
    e₀ ^ (2 * N) • (Q' * ε * Q.map σ - lr ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) R)) =
      A₀ * (Q' * ε * Q.map σ - lr ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) R)).map φ * A₀' := by
  obtain ⟨v, hv⟩ := hev
  obtain ⟨v₀, hv₀⟩ := he₀v
  have he : ∀ x : R, e * x = 0 → x = 0 := by rw [hv]; exact nzd_unit hlr v
  have he₀ : ∀ x : R, e₀ * x = 0 → x = 0 := by rw [hv₀]; exact nzd_unit hlr v₀
  have hσe : ∀ x : R, σ e * x = 0 → x = 0 := by
    have : σ e = lr * ((Units.map (σ : R →* R) v : Rˣ) : R) := by
      rw [hv, map_mul, hσlr]; rfl
    rw [this]; exact nzd_unit hlr _
  have hL := nzd_pow hlr (2 * k)
  have hB'B : B' * B = e ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) R) :=
    mul_comm_of_nzd (nzd_pow he _) hBB'
  have hσBB' : B.map σ * B'.map σ = σ e ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) R) := by
    rw [← Matrix.map_mul, hBB', map_smul_one, map_pow]
  have hφQ'Q : Q'.map φ * Q.map φ = lr ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) R) := by
    rw [← Matrix.map_mul, mul_comm_of_nzd hL hQQ', map_smul_one, map_pow, hφlr]

  have h1 : B' * (Q * A₀) = (e * e₀) ^ N • Q.map φ := by
    apply smul_cancel (nzd_pow he N)
    calc e ^ N • (B' * (Q * A₀)) = B' * (e ^ N • (Q * A₀)) := by rw [Matrix.mul_smul]
      _ = B' * (e₀ ^ N • (B * Q.map φ)) := by rw [hQA]
      _ = e₀ ^ N • (B' * (B * Q.map φ)) := by rw [Matrix.mul_smul]
      _ = e₀ ^ N • (e ^ (2 * N) • Q.map φ) := by rw [mul_left_of hB'B]
      _ = e ^ N • ((e * e₀) ^ N • Q.map φ) := by rw [smul_smul, smul_smul]; congr 1; ring

  have h2 : (e * e₀) ^ N • Q'.map φ = A₀' * (Q' * B) := by
    apply left_cancel hL hφQ'Q
    apply smul_cancel (nzd_pow (nzd_mul he he₀) N)
    have lhs : (e * e₀) ^ N • (Q.map φ * ((e * e₀) ^ N • Q'.map φ)) =
        ((e * e₀) ^ (2 * N) * lr ^ (2 * k)) • (1 : Matrix (Fin d) (Fin d) R) := by
      rw [Matrix.mul_smul, ← Matrix.map_mul, hQQ', map_smul_one, map_pow, hφlr, smul_smul,
        smul_smul]
      congr 1; ring
    have rhs : (e * e₀) ^ N • (Q.map φ * (A₀' * (Q' * B))) =
        ((e * e₀) ^ (2 * N) * lr ^ (2 * k)) • (1 : Matrix (Fin d) (Fin d) R) := by
      rw [← Matrix.smul_mul, ← h1, Matrix.mul_assoc, Matrix.mul_assoc, mul_left_of hAA',
        Matrix.mul_smul, Matrix.mul_smul, mul_left_of hQQ', Matrix.mul_smul, hB'B, smul_smul,
        smul_smul]
      congr 1; ring
    rw [lhs, rhs]

  have hcomm : (Q.map φ).map σ = (Q.map σ).map φ := by
    ext i j; simp [hφσ]
  have h3 : B'.map σ * (Q.map σ * A₀) = (σ e * e₀) ^ N • (Q.map σ).map φ := by
    have := congrArg (fun M => M.map σ) h1
    simp only [Matrix.map_mul, map_smul', map_pow, map_mul, hA₀σ, hσe₀, hcomm] at this
    exact this

  have h4 : B' * (ε * B.map σ) = (σ e * e) ^ N • ε.map φ := by
    apply smul_cancel (nzd_pow he N)
    calc e ^ N • (B' * (ε * B.map σ)) = B' * (e ^ N • (ε * B.map σ)) := by rw [Matrix.mul_smul]
      _ = B' * (σ e ^ N • (B * ε.map φ)) := by rw [hεB]
      _ = σ e ^ N • (B' * (B * ε.map φ)) := by rw [Matrix.mul_smul]
      _ = σ e ^ N • (e ^ (2 * N) • ε.map φ) := by rw [mul_left_of hB'B]
      _ = e ^ N • ((σ e * e) ^ N • ε.map φ) := by rw [smul_smul, smul_smul]; congr 1; ring

  have h5 : A₀ * (Q' * ε * Q.map σ).map φ * A₀' = e₀ ^ (2 * N) • (Q' * ε * Q.map σ) := by
    have hc := nzd_mul (nzd_mul (nzd_pow (nzd_mul he he₀) N) (nzd_pow (nzd_mul hσe he) N))
      (nzd_pow (nzd_mul hσe he₀) N)
    apply smul_cancel hc
    calc ((e * e₀) ^ N * (σ e * e) ^ N * (σ e * e₀) ^ N) • (A₀ * (Q' * ε * Q.map σ).map φ * A₀')
        = A₀ * (((e * e₀) ^ N • Q'.map φ) * (((σ e * e) ^ N • ε.map φ) *
            (((σ e * e₀) ^ N • (Q.map σ).map φ) * A₀'))) := by
          simp only [Matrix.map_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
          congr 1; ring
      _ = A₀ * ((A₀' * (Q' * B)) * ((B' * (ε * B.map σ)) * ((B'.map σ * (Q.map σ * A₀)) * A₀'))) := by
          rw [h2, h4, h3]
      _ = ((e * e₀) ^ N * (σ e * e) ^ N * (σ e * e₀) ^ N) • (e₀ ^ (2 * N) • (Q' * ε * Q.map σ)) := by
          simp only [Matrix.mul_assoc, mul_left_of hAA', mul_left_of hBB', mul_left_of hσBB', hAA',
            Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_smul]
          congr 1; ring
  have hLφ : A₀ * (lr ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) R)).map φ * A₀' =
      e₀ ^ (2 * N) • (lr ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) R)) := by
    rw [map_smul_one, map_pow, hφlr, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hAA',
      smul_smul, smul_smul, mul_comm]
  have hsub : (Q' * ε * Q.map σ - lr ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) R)).map φ =
      (Q' * ε * Q.map σ).map φ - (lr ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) R)).map φ := by
    ext i j; simp only [Matrix.map_apply, Matrix.sub_apply, map_sub]
  rw [hsub, Matrix.mul_sub, Matrix.sub_mul, h5, hLφ, smul_sub]

end GlobalTheory.FrobeniusDefect
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusEquationOfTwistedCocycleDefectStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_equation_of_twisted_cocycle_defect : ∀ (R : Type) [CommRing R] (φ σ : R →+* R) (d N k : ℕ) (lr e e₀ : R) (Q Q' B B' A₀ A₀' ε : Matrix (Fin d) (Fin d) R), (∀ x : R, lr * x = 0 → x = 0) → (∃ v : Rˣ, e = lr * v) → (∃ v : Rˣ, e₀ = lr * v) → (∀ x, φ (σ x) = σ (φ x)) → φ lr = lr → σ lr = lr → σ e₀ = e₀ → A₀.map σ = A₀ → Q * Q' = lr ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) R) → B * B' = e ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) R) → A₀ * A₀' = e₀ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) R) → e ^ N • (Q * A₀) = e₀ ^ N • (B * Q.map φ) → e ^ N • (ε * B.map σ) = σ e ^ N • (B * ε.map φ) → e₀ ^ (2 * N) • (Q' * ε * Q.map σ - lr ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) R)) = A₀ * (Q' * ε * Q.map σ - lr ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) R)).map φ * A₀' := by
  first | (exact @GlobalTheory.FrobeniusDefect.frobenius_defect_eq) | (exact GlobalTheory.FrobeniusDefect.frobenius_defect_eq) | (intros; apply GlobalTheory.FrobeniusDefect.frobenius_defect_eq  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysOfCrystallineBreuilKisinFrame
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.CrTop

theorem map_smul_ring {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {d : ℕ} (c : R)
    (M : Matrix (Fin d) (Fin d) R) : (c • M).map f = f c • M.map f := by
  ext i j; simp

theorem pow_cancel {R : Type} [CommRing R] {lr : R} (h : ∀ x : R, lr * x = 0 → x = 0) (n : ℕ) :
    ∀ x : R, lr ^ n * x = 0 → x = 0 := by
  induction n with
  | zero => intro x hx; simpa using hx
  | succ n ih => intro x hx; exact ih x (h _ (by rw [← mul_assoc, ← pow_succ']; exact hx))

theorem smul_cancel {R : Type} [CommRing R] {c : R} (h : ∀ x : R, c * x = 0 → x = 0) {d : ℕ}
    {M M' : Matrix (Fin d) (Fin d) R} (hM : c • M = c • M') : M = M' := by
  ext i j
  have := congrFun (congrFun hM i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  exact sub_eq_zero.1 (h _ (by rw [mul_sub, this, sub_self]))

theorem crys_of_frame : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (N : ℕ) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (F : Frame bk N d fun g => (ρ g).val), F.IsCr → IsCrys (P.PD K) (qRep ρ) := by
  intro l _ K bk τ hτ P AI T N d ρ F hcr
  obtain ⟨Y, Y', hY, hYY⟩ := GlobalTheory.T.breuilKisinPreframe_bounded_poles l K bk τ hτ N d (fun g => (ρ g).val) F.toPre
  obtain ⟨-, hR1, hE2⟩ := GlobalTheory.T.frame_ainf_matrix_frobenius_galois_eqs l K bk τ hτ N d (fun g => (ρ g).val) F Y Y' hY hYY
  obtain ⟨k, Q, Q', hQQ, hQu, hQ'u, hQφ⟩ := GlobalTheory.T.exists_frobenius_section_acris_breuilKisin l K bk N d F.A F.A' F.A_mul
  obtain ⟨htf, -, ⟨v, hv⟩, hφι, hσι⟩ := GlobalTheory.T.acris_torsionFree_complete_frobenius_properties l K bk
  set ι := algebraMap (Ainf l) (Per.Acris l) with hι

  have key : ∀ g : ↥(GK K), (F.ε g).map (fun a => ι (WittVector.frobenius a)) * Q.map (sigA (g : GQ l)) = Q := by
    intro g
    set σ := sigA (g : GQ l) with hσdef
    set fA : bk.S →+* Per.Acris l := (ι.comp bk.ev).comp (frobS l bk.a) with hfA
    set f0 : bk.S →+* Per.Acris l := fA.comp ((PowerSeries.C).comp PowerSeries.constantCoeff) with hf0
    set ε' := (F.ε g).map (fun a => ι (WittVector.frobenius a)) with hε'
    have hfr : ∀ s : bk.S, fA s = ι (WittVector.frobenius (bk.ev s)) := fun s => by
      simp only [hfA, RingHom.comp_apply, bk.ev_frob]
    have hfix : ∀ c : Wq l bk.a, σ (fA (PowerSeries.C c)) = fA (PowerSeries.C c) := fun c => by
      rw [hfr, hσdef, hσι, ← GlobalTheory.RingBasics.φA_apply, ← ActLaws.φA_σA, bk.ev_C, bk.gal_w g c]
    have hcomm : ∀ x, phiA l (σ x) = σ (phiA l x) := fun x => by
      simp only [hσdef]
      exact GlobalTheory.CrisMaps.phiA_sigA (g : GQ l) x
    have he₀ : ∃ w : (Per.Acris l)ˣ, f0 bk.E = (l : Per.Acris l) * w := by
      obtain ⟨w, hw⟩ := bk.coeff_zero
      have hc : PowerSeries.constantCoeff bk.E = (l : Wq l bk.a) * w := by
        rw [← hw]; simp
      refine ⟨((Units.map (PowerSeries.C (R := Wq l bk.a)).toMonoidHom w).map fA.toMonoidHom), ?_⟩
      simp [hf0, hc]

    have hBB : F.A.map fA * F.A'.map fA = fA bk.E ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) := by
      rw [← Matrix.map_mul, F.A_mul, map_smul_ring, map_pow, Matrix.map_one _ (map_zero _) (map_one _)]
    have hAA : F.A.map f0 * F.A'.map f0 = f0 bk.E ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) := by
      rw [← Matrix.map_mul, F.A_mul, map_smul_ring, map_pow, Matrix.map_one _ (map_zero _) (map_one _)]
    have hσA₀ : (F.A.map f0).map σ = F.A.map f0 := by
      ext i j; simp only [Matrix.map_apply, hf0, RingHom.comp_apply]; exact hfix _
    have hσe₀ : σ (f0 bk.E) = f0 bk.E := by simp only [hf0, RingHom.comp_apply]; exact hfix _
    have hσf : ∀ s : bk.S, ι (WittVector.frobenius (Per.σA (g : GQ l) (bk.ev s))) = σ (fA s) := fun s => by
      rw [hfr, hσdef, hσι, ← GlobalTheory.RingBasics.φA_apply, ← GlobalTheory.RingBasics.φA_apply, ActLaws.φA_σA]
    have h2 : fA bk.E ^ N • (ε' * (F.A.map fA).map σ) = σ (fA bk.E) ^ N • (F.A.map fA * ε'.map (phiA l)) := by
      have e := congrArg (fun M => M.map (ι.comp WittVector.frobenius)) (hE2 g)
      simp only [map_smul_ring, Matrix.map_mul, Matrix.map_map, map_pow, RingHom.comp_apply] at e
      have hfrfun : (fA : bk.S → Per.Acris l) = (fun s => ι (WittVector.frobenius (bk.ev s))) := funext hfr
      simpa only [hε', Matrix.map_map, RingHom.coe_comp, Function.comp_def, RingHom.comp_apply, hfrfun, hσf, hφι] using e
    have hL1 := GlobalTheory.T.frobenius_equation_of_twisted_cocycle_defect (Per.Acris l) (phiA l) σ d N k (l : Per.Acris l) (fA bk.E) (f0 bk.E) Q Q' (F.A.map fA) (F.A'.map fA)
      (F.A.map f0) (F.A'.map f0) ε' htf ⟨v, hv⟩ he₀ hcomm (map_natCast _ _) (map_natCast _ _) hσe₀ hσA₀ hQQ hBB hAA hQφ h2

    obtain ⟨w₀, hw₀⟩ := he₀
    set D := Q' * ε' * Q.map σ - (l : Per.Acris l) ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) with hD
    have hDeq : (l : Per.Acris l) ^ (2 * N) • D = F.A.map f0 * D.map (phiA l) * (((w₀⁻¹ : (Per.Acris l)ˣ) : Per.Acris l) ^ (2 * N) • F.A'.map f0) := by
      rw [Matrix.mul_smul, ← hL1, smul_smul, hw₀]
      congr 1
      rw [mul_pow, mul_left_comm, ← mul_pow, Units.inv_mul, one_pow, mul_one]

    set u := ι (bk.ev X) with hu
    set π := Ideal.Quotient.mk (Ideal.span {u}) with hπ
    have hz : ∀ M : Matrix (Fin d) (Fin d) (Per.Acris l), (∀ i j, u ∣ M i j) ↔ M.map π = 0 := fun M => by
      constructor
      · intro h; ext i j
        simpa [hπ, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] using h i j
      · intro h i j
        have := congrFun (congrFun h i) j
        simpa [hπ, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] using this
    have hQ1 : Q.map π = ((l : Per.Acris l) ^ k • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))).map π := by
      rw [← sub_eq_zero, ← Matrix.map_sub _ (map_sub π)]; exact (hz _).1 hQu
    have hQ'1 : Q'.map π = ((l : Per.Acris l) ^ k • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))).map π := by
      rw [← sub_eq_zero, ← Matrix.map_sub _ (map_sub π)]; exact (hz _).1 hQ'u
    have hdvdφ : bk.ev X ∣ WittVector.frobenius (bk.ev X) := by
      rw [bk.ev_X, WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]
      exact dvd_pow_self _ (Fact.out : l.Prime).ne_zero
    have hε1 : ε'.map π = 1 := by
      have : ∀ i j, u ∣ (ε' - 1) i j := fun i j => by
        obtain ⟨c, hc⟩ := hcr g i j
        have e1 : (ε' - 1) i j = ι (WittVector.frobenius ((F.ε g - 1) i j)) := by
          simp only [hε', Matrix.sub_apply, Matrix.map_apply, map_sub]
          by_cases hij : i = j
          · subst hij; simp
          · simp [Matrix.one_apply_ne hij]
        rw [e1, hc, map_mul, map_mul]
        exact dvd_mul_of_dvd_left (map_dvd ι hdvdφ) _
      rw [← sub_eq_zero, ← Matrix.map_one π (map_zero _) (map_one _), ← Matrix.map_sub _ (map_sub π)]
      exact (hz _).1 this
    have hQσ : (Q.map σ).map π = ((l : Per.Acris l) ^ k • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))).map π := by
      have hdσ : u ∣ σ u := by
        rw [hu, hσdef, hσι]; exact map_dvd ι ((galois_discMap l K bk).1 (g : GQ l))
      have : ∀ i j, u ∣ (Q.map σ - (l : Per.Acris l) ^ k • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))) i j := fun i j => by
        have e1 : (Q.map σ - (l : Per.Acris l) ^ k • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))) i j =
            σ ((Q - (l : Per.Acris l) ^ k • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))) i j) := by
          by_cases hij : i = j
          · subst hij; simp
          · simp [Matrix.one_apply_ne hij]
        obtain ⟨c, hc⟩ := hQu i j
        rw [e1, hc, map_mul]
        exact dvd_mul_of_dvd_left hdσ _
      rw [← sub_eq_zero, ← Matrix.map_sub _ (map_sub π)]; exact (hz _).1 this
    have hdiv : ∀ i j, ι (bk.ev X) ∣ D i j := by
      refine (hz D).2 ?_
      rw [hD, Matrix.map_sub _ (map_sub π), Matrix.map_mul, Matrix.map_mul, hQ'1, hε1, hQσ]
      simp only [map_smul_ring, Matrix.map_one _ (map_zero _) (map_one _), mul_one, smul_mul_smul_comm, map_pow]
      rw [← pow_add, ← two_mul, sub_self]
    have hD0 := GlobalTheory.T.acris_frobenius_matrix_eq_zero_of_dvd l K bk d (2 * N) D (F.A.map f0) _ hdiv hDeq
    have hM : Q' * ε' * Q.map σ = (l : Per.Acris l) ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) :=
      sub_eq_zero.1 hD0
    refine smul_cancel (pow_cancel htf (2 * k)) ?_
    have := congrArg (fun M => Q * M) hM
    simp only [← Matrix.mul_assoc, hQQ, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one] at this
    exact this
  obtain ⟨U, hU, hinv⟩ := GlobalTheory.T.exists_invariant_unit_matrix_bcris_frame l K bk τ hτ N d k ρ Y Y' F.ε Q Q' hYY hR1 hQQ key
  exact GlobalTheory.T.isCrystalline_of_invariant_unit_bcris_matrix l K P AI T d ρ U hU hinv

end GlobalTheory.CrTop
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysOfCrystallineBreuilKisinFrameStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCrys_of_crystallineBreuilKisinFrame : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (N : ℕ) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (F : Frame bk N d fun g => (ρ g).val), F.IsCr → IsCrys (P.PD K) (qRep ρ) := by
  first | (exact @GlobalTheory.CrTop.crys_of_frame) | (exact GlobalTheory.CrTop.crys_of_frame) | (intros; apply GlobalTheory.CrTop.crys_of_frame  <;> assumption)
end
