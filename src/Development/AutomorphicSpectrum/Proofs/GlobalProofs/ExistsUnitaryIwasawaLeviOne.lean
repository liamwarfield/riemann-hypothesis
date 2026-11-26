module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSmoothVec
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaAll
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedWhittakerNewform
public import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.THProvA

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockTriKeeps
section -- merged from Development.AutomorphicSpectrum.Proofs.JetProofs.ScalarOnComplement
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCSS
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.HCSide.CentreNone

variable {n a : ℕ} {ε : Fin n → Bool}

theorem Jm_herm (ε : Fin n → Bool) : (Jm ε)ᴴ = Jm ε := by
  simp only [Jm, diagonal_conjTranspose]; congr 1; funext i; by_cases h : ε i <;> simp [h]

theorem half_props {C J : Matrix (Fin n) (Fin n) ℂ} (hh : Cᴴ = C) (hi : C * C = C) (hJ : J * C = C * J)
    (hJJ : J * J = 1) (hJh : Jᴴ = J) {t : ℂ} (ht : t * t = 1) (hs : star t = t) :
    ((1 / 2 : ℂ) • (C * (1 + t • J)))ᴴ = (1 / 2 : ℂ) • (C * (1 + t • J)) ∧
      (1 / 2 : ℂ) • (C * (1 + t • J)) * ((1 / 2 : ℂ) • (C * (1 + t • J))) = (1 / 2 : ℂ) • (C * (1 + t • J)) ∧
      J * ((1 / 2 : ℂ) • (C * (1 + t • J))) = t • ((1 / 2 : ℂ) • (C * (1 + t • J))) := by
  have c : (1 + t • J) * C = C * (1 + t • J) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, smul_mul_assoc, mul_smul_comm, hJ]
  have s : (1 + t • J) * (1 + t • J) = (2 : ℂ) • (1 + t • J) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, smul_mul_assoc, mul_smul_comm, hJJ,
      smul_smul, ht]
    match_scalars <;> first | linear_combination ht | ring
  have e : C * (1 + t • J) * (C * (1 + t • J)) = (2 : ℂ) • (C * (1 + t • J)) := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (1 + t • J), c, Matrix.mul_assoc, s, ← Matrix.mul_assoc, hi,
      mul_smul_comm]
  refine ⟨?_, ?_, ?_⟩
  · have h2 : star (1 / 2 : ℂ) = 1 / 2 := by simp
    rw [conjTranspose_smul, conjTranspose_mul, conjTranspose_add, conjTranspose_one, conjTranspose_smul, hh, hJh,
      hs, h2, c]
  · rw [smul_mul_assoc, mul_smul_comm, e, smul_smul, smul_smul]
    norm_num
  · have e2 : J * (1 + t • J) = t • (1 + t • J) := by
      simp only [Matrix.mul_add, Matrix.mul_one, mul_smul_comm, hJJ, smul_add, smul_smul, ht]
      module
    rw [mul_smul_comm, ← Matrix.mul_assoc, hJ, Matrix.mul_assoc, e2, mul_smul_comm, smul_comm]

theorem exists_frame_J {C : Matrix (Fin n) (Fin n) ℂ} (hh : Cᴴ = C) (hi : C * C = C)
    (hJ : Jm ε * C = C * Jm ε) :
    ∃ (m : ℕ) (ε' : Fin m → Bool) (B : Matrix (Fin n) (Fin m) ℂ),
      Bᴴ * B = 1 ∧ B * Bᴴ = C ∧ Jm ε * B = B * Jm ε' := by
  have hJJ : Jm ε * Jm ε = 1 := Jm_mul_self ε
  have hJh := Jm_herm ε
  obtain ⟨p1, p2, p3⟩ := half_props hh hi hJ hJJ hJh (t := 1) (by norm_num) (by simp)
  obtain ⟨m1, m2, m3⟩ := half_props hh hi hJ hJJ hJh (t := -1) (by norm_num) (by simp)
  have hsum : (1 / 2 : ℂ) • (C * (1 + (1 : ℂ) • Jm ε)) + (1 / 2 : ℂ) • (C * (1 + (-1 : ℂ) • Jm ε)) = C := by
    simp only [Matrix.mul_add, Matrix.mul_one, mul_smul_comm]
    module
  generalize (1 / 2 : ℂ) • (C * (1 + (1 : ℂ) • Jm ε)) = Dp at p1 p2 p3 hsum
  generalize (1 / 2 : ℂ) • (C * (1 + (-1 : ℂ) • Jm ε)) = Dm at m1 m2 m3 hsum
  obtain ⟨r, Bp, a1, a2⟩ := GlobalTheory.IsoTorus.proj_frame p1 p2
  obtain ⟨s, Bm, b1, b2⟩ := GlobalTheory.IsoTorus.proj_frame m1 m2
  have hp : Jm ε * Bp = Bp := by
    have e : Bp = Dp * Bp := by rw [← a2, Matrix.mul_assoc, a1, Matrix.mul_one]
    rw [e, ← Matrix.mul_assoc, p3, one_smul]
  have hm : Jm ε * Bm = -Bm := by
    have e : Bm = Dm * Bm := by rw [← b2, Matrix.mul_assoc, b1, Matrix.mul_one]
    rw [e, ← Matrix.mul_assoc, m3, neg_one_smul, Matrix.neg_mul]
  have hpH : Bpᴴ * Jm ε = Bpᴴ := by
    have := congrArg conjTranspose hp
    rwa [conjTranspose_mul, hJh] at this
  have hX : Bpᴴ * Bm = 0 := by
    have e : Bpᴴ * Bm = -(Bpᴴ * Bm) := by
      nth_rewrite 1 [← hpH]
      rw [Matrix.mul_assoc, hm, Matrix.mul_neg]
    have e2 : (2 : ℂ) • (Bpᴴ * Bm) = 0 := by
      rw [two_smul]
      nth_rewrite 1 [e]
      simp
    exact (smul_eq_zero.1 e2).resolve_left two_ne_zero
  have hX' : Bmᴴ * Bp = 0 := by
    have := congrArg conjTranspose hX
    simpa [conjTranspose_mul] using this
  refine ⟨r + s, fun k => Sum.elim (fun _ => true) (fun _ => false) (finSumFinEquiv.symm k),
    (fromCols Bp Bm).submatrix id finSumFinEquiv.symm, ?_, ?_, ?_⟩
  · rw [conjTranspose_submatrix, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id,
      conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul_fromCols, a1, b1, hX, hX', fromBlocks_one]
    exact submatrix_one_equiv _
  · rw [conjTranspose_submatrix, Matrix.submatrix_mul_equiv, conjTranspose_fromCols_eq_fromRows_conjTranspose,
      fromCols_mul_fromRows, a2, b2, hsum]
    rfl
  · ext i k
    obtain ⟨k, rfl⟩ := finSumFinEquiv.surjective k
    have e1 := fun l => congrFun (congrFun hp i) l
    have e2 := fun l => congrFun (congrFun hm i) l
    rcases k with l | l
    · have := e1 l
      simp only [Jm, diagonal_mul] at this ⊢
      simpa [mul_diagonal] using this
    · have := e2 l
      simp only [Jm, diagonal_mul] at this ⊢
      simpa [mul_diagonal] using this

end GlobalTheory.CompanionTheory.HCSide.CentreNone

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsotropicHyperbolicComplement
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsotropicHyperbolicComplement
open Matrix

namespace GlobalTheory.CompanionTheory.Dblock.CompFrame

theorem exists_comp_frame : ∀ {n D : ℕ} (ε : Fin n → Bool) (C : Matrix (Fin n) (Fin D) ℂ),
    Cᴴ * C = 1 → Cᴴ * Formalism.REAL.Jm ε * C = 0 →
    ∃ (m : ℕ) (R : Matrix (Fin n) (Fin m) ℂ) (ε' : Fin m → Bool),
      Rᴴ * R = 1 ∧ Formalism.REAL.Jm ε * R = R * Formalism.REAL.Jm ε' ∧ Cᴴ * R = 0 ∧
      C * Cᴴ + Formalism.REAL.Jm ε * C * Cᴴ * Formalism.REAL.Jm ε + R * Rᴴ = 1 := by
  intro n D ε C h1 h2
  have hJJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := Formalism.REAL.Jm_mul_self ε
  have hJh : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := GlobalTheory.CompanionTheory.HCSide.CentreNone.Jm_herm ε
  generalize hJ : Formalism.REAL.Jm ε = J at *
  have hAA : C * Cᴴ * (C * Cᴴ) = C * Cᴴ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Cᴴ, h1, Matrix.one_mul]
  have hAB : C * Cᴴ * (J * C * Cᴴ * J) = 0 := by
    have e : C * Cᴴ * (J * C * Cᴴ * J) = C * (Cᴴ * J * C) * Cᴴ * J := by
      simp only [Matrix.mul_assoc]
    rw [e, h2]; simp
  have hBA : J * C * Cᴴ * J * (C * Cᴴ) = 0 := by
    have e : J * C * Cᴴ * J * (C * Cᴴ) = J * C * (Cᴴ * J * C) * Cᴴ := by
      simp only [Matrix.mul_assoc]
    rw [e, h2]; simp
  have hBB : J * C * Cᴴ * J * (J * C * Cᴴ * J) = J * C * Cᴴ * J := by
    have e : J * C * Cᴴ * J * (J * C * Cᴴ * J) = J * C * (Cᴴ * (J * J) * C) * Cᴴ * J := by
      simp only [Matrix.mul_assoc]
    rw [e, hJJ, Matrix.mul_one, h1, Matrix.mul_one]
  have hPh : (1 - C * Cᴴ - J * C * Cᴴ * J)ᴴ = 1 - C * Cᴴ - J * C * Cᴴ * J := by
    simp only [conjTranspose_sub, conjTranspose_one, conjTranspose_mul, conjTranspose_conjTranspose, hJh,
      Matrix.mul_assoc]
  have hPP : (1 - C * Cᴴ - J * C * Cᴴ * J) * (1 - C * Cᴴ - J * C * Cᴴ * J) =
      1 - C * Cᴴ - J * C * Cᴴ * J := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hAA, hAB, hBA, hBB]
    abel
  have hPJ : J * (1 - C * Cᴴ - J * C * Cᴴ * J) = (1 - C * Cᴴ - J * C * Cᴴ * J) * J := by
    have e1 : J * (J * C * Cᴴ * J) = C * Cᴴ * J := by
      simp only [← Matrix.mul_assoc, hJJ, Matrix.one_mul]
    have e2 : J * C * Cᴴ * J * J = J * (C * Cᴴ) := by
      rw [Matrix.mul_assoc _ J J, hJJ, Matrix.mul_one, Matrix.mul_assoc]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, e1, e2]
    abel
  subst hJ
  obtain ⟨m, ε', R, r1, r2, r3⟩ := GlobalTheory.CompanionTheory.HCSide.CentreNone.exists_frame_J hPh hPP hPJ
  refine ⟨m, R, ε', r1, r3, ?_, ?_⟩
  · have hCP : Cᴴ * (1 - C * Cᴴ - Formalism.REAL.Jm ε * C * Cᴴ * Formalism.REAL.Jm ε) = 0 := by
      have e : Cᴴ * (Formalism.REAL.Jm ε * C * Cᴴ * Formalism.REAL.Jm ε) =
          (Cᴴ * Formalism.REAL.Jm ε * C) * Cᴴ * Formalism.REAL.Jm ε := by
        simp only [Matrix.mul_assoc]
      rw [Matrix.mul_sub, Matrix.mul_sub, e, h2, ← Matrix.mul_assoc, h1]
      simp
    have e : R = (1 - C * Cᴴ - Formalism.REAL.Jm ε * C * Cᴴ * Formalism.REAL.Jm ε) * R := by
      rw [← r2, Matrix.mul_assoc, r1, Matrix.mul_one]
    rw [e, ← Matrix.mul_assoc, hCP, Matrix.zero_mul]
  · rw [r2]; abel

end GlobalTheory.CompanionTheory.Dblock.CompFrame
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsotropicHyperbolicComplementStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropic_hyperbolic_complement : ∀ {n D : ℕ} (ε : Fin n → Bool) (C : Matrix (Fin n) (Fin D) ℂ), Cᴴ * C = 1 → Cᴴ * Formalism.REAL.Jm ε * C = 0 → ∃ (m : ℕ) (R : Matrix (Fin n) (Fin m) ℂ) (ε' : Fin m → Bool), Rᴴ * R = 1 ∧ Formalism.REAL.Jm ε * R = R * Formalism.REAL.Jm ε' ∧ Cᴴ * R = 0 ∧ C * Cᴴ + Formalism.REAL.Jm ε * C * Cᴴ * Formalism.REAL.Jm ε + R * Rᴴ = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Dblock.CompFrame.exists_comp_frame | exact GlobalTheory.CompanionTheory.Dblock.CompFrame.exists_comp_frame | (intros; apply GlobalTheory.CompanionTheory.Dblock.CompFrame.exists_comp_frame <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlagOrthonormalAdaptedBasis
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlagOrthonormalAdaptedBasis
open Matrix

namespace GlobalTheory.CompanionTheory.Flag

theorem exists_frame_extension {n D : ℕ} (C : Matrix (Fin n) (Fin D) ℂ) (h1 : Cᴴ * C = 1)
    (U : Submodule ℂ (Fin n → ℂ)) (hU : ∀ v, C *ᵥ v ∈ U) :
    ∃ (r : ℕ) (B : Matrix (Fin n) (Fin r) ℂ), Bᴴ * B = 1 ∧ Cᴴ * B = 0 ∧
      ∀ y, y ∈ U ↔ ∃ u w, y = C *ᵥ u + B *ᵥ w := by
  classical
  let W' : Submodule ℂ (Fin n → ℂ) := U ⊓ LinearMap.ker (Matrix.mulVecLin Cᴴ)
  obtain ⟨r, B, hB1, hBW⟩ := GlobalTheory.IsoTorus.exists_frame W'
  have hmemW' : ∀ y, y ∈ W' ↔ y ∈ U ∧ Cᴴ *ᵥ y = 0 := fun y => by
    simp [W', Submodule.mem_inf]
  have hBin : ∀ w, B *ᵥ w ∈ W' := fun w => (hBW _).mpr (by
    rw [Matrix.mulVec_mulVec w (B * Bᴴ) B, Matrix.mul_assoc, hB1, Matrix.mul_one])
  have hCB : Cᴴ * B = 0 := by
    ext i j
    have h := congrFun ((hmemW' _).mp (hBin (Pi.single j 1))).2 i
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at h
    simpa using h
  refine ⟨r, B, hB1, hCB, fun y => ⟨fun hy => ?_, ?_⟩⟩
  · obtain ⟨z, hzdef⟩ : ∃ z, z = y - C *ᵥ (Cᴴ *ᵥ y) := ⟨_, rfl⟩
    have hCC : Cᴴ *ᵥ (C *ᵥ (Cᴴ *ᵥ y)) = Cᴴ *ᵥ y := by
      rw [Matrix.mulVec_mulVec (Cᴴ *ᵥ y) Cᴴ C, h1, Matrix.one_mulVec]
    have hz : z ∈ W' := (hmemW' z).mpr ⟨hzdef ▸ U.sub_mem hy (hU _), by
      rw [hzdef, Matrix.mulVec_sub, hCC, sub_self]⟩
    have hz' := (hBW z).mp hz
    refine ⟨Cᴴ *ᵥ y, Bᴴ *ᵥ z, ?_⟩
    rw [Matrix.mulVec_mulVec z B Bᴴ, hz', hzdef]
    abel
  · rintro ⟨u, w, rfl⟩
    exact U.add_mem (hU u) ((hmemW' _).mp (hBin w)).1

private theorem append_cols_mulVec_eq_add {n D r : ℕ} (C : Matrix (Fin n) (Fin D) ℂ) (B : Matrix (Fin n) (Fin r) ℂ)
    (v : Fin (D + r) → ℂ) :
    (Matrix.of fun i => Fin.append (C i) (B i)) *ᵥ v =
      C *ᵥ (fun j => v (Fin.castAdd r j)) + B *ᵥ (fun j => v (Fin.natAdd D j)) := by
  ext i
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_add]

private theorem append_cols_conjTranspose_mul_eq_one {n D r : ℕ} (C : Matrix (Fin n) (Fin D) ℂ) (B : Matrix (Fin n) (Fin r) ℂ)
    (h1 : Cᴴ * C = 1) (h2 : Bᴴ * B = 1) (h3 : Cᴴ * B = 0) :
    (Matrix.of fun i => Fin.append (C i) (B i))ᴴ * (Matrix.of fun i => Fin.append (C i) (B i)) = 1 := by
  have h4 : Bᴴ * C = 0 := by simpa using congrArg Matrix.conjTranspose h3
  ext c c'
  refine Fin.addCases (fun j => ?_) (fun j => ?_) c <;> refine Fin.addCases (fun j' => ?_) (fun j' => ?_) c'
  · have h := congrFun (congrFun h1 j) j'
    simpa [Matrix.mul_apply, Matrix.one_apply] using h
  · have hne : Fin.castAdd r j ≠ Fin.natAdd D j' := fun h => by
      have := congrArg Fin.val h
      simp at this
      omega
    rw [Matrix.one_apply_ne hne]
    have h := congrFun (congrFun h3 j) j'
    simpa [Matrix.mul_apply] using h
  · have hne : Fin.natAdd D j ≠ Fin.castAdd r j' := fun h => by
      have := congrArg Fin.val h
      simp at this
      omega
    rw [Matrix.one_apply_ne hne]
    have h := congrFun (congrFun h4 j) j'
    simpa [Matrix.mul_apply] using h
  · have h := congrFun (congrFun h2 j) j'
    simpa [Matrix.mul_apply, Matrix.one_apply] using h

theorem exists_flag_frame : ∀ {n a : ℕ} (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), W 0 = ⊥ →
    Monotone W → ∃ (D : ℕ) (C : Matrix (Fin n) (Fin D) ℂ) (τ : Fin D → ℕ), Cᴴ * C = 1 ∧
      Monotone τ ∧ (∀ c, τ c < a) ∧ ∀ (i : Fin (a + 1)) (y : Fin n → ℂ),
        y ∈ W i ↔ ∃ v : Fin D → ℂ, y = C *ᵥ v ∧ ∀ c, (i : ℕ) ≤ τ c → v c = 0 := by
  intro n a
  induction a with
  | zero =>
    intro W hW0 _
    refine ⟨0, 0, fun _ => 0, ?_, fun x _ _ => x.elim0, fun c => c.elim0, fun i y => ?_⟩
    · ext i j
      exact i.elim0
    · have hi : i = 0 := Fin.ext (by have := i.isLt; simp only [Fin.val_zero]; omega)
      subst hi
      rw [hW0, Submodule.mem_bot]
      constructor
      · rintro rfl
        exact ⟨0, by simp, fun c => c.elim0⟩
      · rintro ⟨v, rfl, -⟩
        simp
  | succ a ih =>
    intro W hW0 hWm
    obtain ⟨D, C, τ, hC1, hτm, hτa, hCW⟩ := ih (fun i => W i.castSucc) (by simpa using hW0)
      (fun i j hij => hWm (Fin.castSucc_le_castSucc_iff.mpr hij))
    have hU : ∀ v, C *ᵥ v ∈ W (Fin.last (a + 1)) := fun v =>
      hWm (Fin.castSucc_lt_last (Fin.last a)).le
        ((hCW (Fin.last a) _).mpr ⟨v, rfl, fun c h => absurd h (not_le.mpr (hτa c))⟩)
    obtain ⟨r, B, hB1, hCB, hBU⟩ := exists_frame_extension C hC1 (W (Fin.last (a + 1))) hU
    refine ⟨D + r, Matrix.of fun i => Fin.append (C i) (B i), Fin.append τ (fun _ => a),
      append_cols_conjTranspose_mul_eq_one C B hC1 hB1 hCB, ?_, ?_, ?_⟩
    · intro c c' hcc'
      induction c using Fin.addCases with
      | left j =>
        induction c' using Fin.addCases with
        | left j' =>
          simp only [Fin.append_left]
          exact hτm (Fin.le_iff_val_le_val.mpr (by simpa using Fin.le_iff_val_le_val.mp hcc'))
        | right j' =>
          simp only [Fin.append_left, Fin.append_right]
          exact (hτa j).le
      | right j =>
        induction c' using Fin.addCases with
        | left j' =>
          exfalso
          have h := Fin.le_iff_val_le_val.mp hcc'
          have := j'.isLt
          simp at h
          omega
        | right j' =>
          simp only [Fin.append_right]
          exact le_refl _
    · intro c
      refine Fin.addCases (fun j => ?_) (fun j => ?_) c
      · simp only [Fin.append_left]
        exact (hτa j).trans (Nat.lt_succ_self a)
      · simp only [Fin.append_right]
        exact Nat.lt_succ_self a
    · intro i y
      induction i using Fin.lastCases with
      | last =>
        rw [hBU]
        constructor
        · rintro ⟨u, w, rfl⟩
          refine ⟨Fin.append u w, ?_, fun c hc => ?_⟩
          · rw [append_cols_mulVec_eq_add]
            simp
          · exfalso
            revert hc
            refine Fin.addCases (fun j => ?_) (fun j => ?_) c
            · intro h
              simp only [Fin.append_left, Fin.val_last] at h
              have := hτa j
              omega
            · intro h
              simp only [Fin.append_right, Fin.val_last] at h
              omega
        · rintro ⟨v, rfl, -⟩
          exact ⟨_, _, append_cols_mulVec_eq_add C B v⟩
      | cast i' =>
        refine (hCW i' y).trans ?_
        constructor
        · rintro ⟨v, rfl, hv⟩
          refine ⟨Fin.append v 0, ?_, fun c hc => ?_⟩
          · rw [append_cols_mulVec_eq_add]
            simp only [Fin.append_left, Fin.append_right, Pi.zero_apply]
            rw [show (fun _ : Fin r => (0 : ℂ)) = 0 from rfl, Matrix.mulVec_zero, add_zero]
          · revert hc
            refine Fin.addCases (fun j => ?_) (fun j => ?_) c
            · intro hc
              simp only [Fin.append_left, Fin.val_castSucc] at hc ⊢
              exact hv j hc
            · intro _
              simp
        · rintro ⟨v, rfl, hv⟩
          refine ⟨fun j => v (Fin.castAdd r j), ?_, fun c hc => hv (Fin.castAdd r c) (by simpa using hc)⟩
          rw [append_cols_mulVec_eq_add]
          have hz : (fun j => v (Fin.natAdd D j)) = 0 := funext fun j => hv _ (by
            have := i'.isLt
            simp only [Fin.append_right, Fin.val_castSucc]
            omega)
          rw [hz, Matrix.mulVec_zero, add_zero]

end GlobalTheory.CompanionTheory.Flag
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlagOrthonormalAdaptedBasisStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_orthonormal_adapted_basis : ∀ {n a : ℕ} (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), W 0 = ⊥ → Monotone W → ∃ (D : ℕ) (C : Matrix (Fin n) (Fin D) ℂ) (τ : Fin D → ℕ), Cᴴ * C = 1 ∧ Monotone τ ∧ (∀ c, τ c < a) ∧ ∀ (i : Fin (a + 1)) (y : Fin n → ℂ), y ∈ W i ↔ ∃ v : Fin D → ℂ, y = C *ᵥ v ∧ ∀ c, (i : ℕ) ≤ τ c → v c = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Flag.exists_flag_frame | exact GlobalTheory.CompanionTheory.Flag.exists_flag_frame | (intros; apply GlobalTheory.CompanionTheory.Flag.exists_flag_frame <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryExtensionOfBlock
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryExtensionOfBlock
open Matrix

namespace GlobalTheory.CompanionTheory.WittFrame

abbrev FrameIdx (D m : ℕ) := Fin D ⊕ₗ (Fin m ⊕ₗ (Fin D)ᵒᵈ)

def frameEquiv (D m : ℕ) : FrameIdx D m ≃ Fin D ⊕ (Fin m ⊕ Fin D) :=
  ofLex.trans (Equiv.sumCongr (Equiv.refl _)
    (ofLex.trans (Equiv.sumCongr (Equiv.refl _) OrderDual.ofDual)))

theorem block_zero {D m : ℕ} (b b' : Matrix (Fin D) (Fin D) ℂ) (t : Matrix (Fin m) (Fin m) ℂ)
    (hb : b.BlockTriangular id) (ht : t.BlockTriangular id)
    (hb' : ∀ x y, x < y → b' x y = 0) (p q : FrameIdx D m) (hqp : q < p) :
    (fromBlocks b 0 0 (fromBlocks t 0 0 b')) (frameEquiv D m p) (frameEquiv D m q) = 0 := by
  obtain ⟨p, rfl⟩ := toLex.surjective p
  obtain ⟨q, rfl⟩ := toLex.surjective q
  rcases p with a | u <;> rcases q with c | v
  · have h : c < a := Sum.Lex.inl_lt_inl_iff.1 hqp
    simpa [frameEquiv] using hb h
  · exact absurd hqp Sum.Lex.not_inr_lt_inl
  · simp [frameEquiv]
  · have h : v < u := Sum.Lex.inr_lt_inr_iff.1 hqp
    obtain ⟨u, rfl⟩ := toLex.surjective u
    obtain ⟨v, rfl⟩ := toLex.surjective v
    rcases u with a | u <;> rcases v with c | v
    · have h' : c < a := Sum.Lex.inl_lt_inl_iff.1 h
      simpa [frameEquiv] using ht h'
    · exact absurd h Sum.Lex.not_inr_lt_inl
    · simp [frameEquiv]
    · have h' : v < u := Sum.Lex.inr_lt_inr_iff.1 h
      have h'' : OrderDual.ofDual u < OrderDual.ofDual v := h'
      simpa [frameEquiv] using hb' _ _ h''

theorem unitary_of_blocks {n D m : ℕ} (C H : Matrix (Fin n) (Fin D) ℂ)
    (G : Matrix (Fin n) (Fin m) ℂ)
    (hCC : Cᴴ * C = 1) (hCG : Cᴴ * G = 0) (hCH : Cᴴ * H = 0) (hGG : Gᴴ * G = 1)
    (hGH : Gᴴ * H = 0) (hHH : Hᴴ * H = 1) (hcard : D + (m + D) = n) :
    ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ (s : Matrix (Fin n) (Fin n) ℂ)
      (b b' : Matrix (Fin D) (Fin D) ℂ) (t : Matrix (Fin m) (Fin m) ℂ),
      s * C = C * b → s * G = G * t → s * H = H * b' → b.BlockTriangular id →
      t.BlockTriangular id → (∀ x y, x < y → b' x y = 0) → (Uᴴ * s * U).BlockTriangular id := by
  have hGC : Gᴴ * C = 0 := by
    have := congrArg conjTranspose hCG
    simpa [conjTranspose_mul] using this
  have hHC : Hᴴ * C = 0 := by
    have := congrArg conjTranspose hCH
    simpa [conjTranspose_mul] using this
  have hHG : Hᴴ * G = 0 := by
    have := congrArg conjTranspose hGH
    simpa [conjTranspose_mul] using this
  set E : Matrix (Fin n) (Fin D ⊕ (Fin m ⊕ Fin D)) ℂ := fromCols C (fromCols G H) with hEdef
  have hE : Eᴴ * E = 1 := by
    rw [hEdef, conjTranspose_fromCols_eq_fromRows_conjTranspose,
      conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul_fromCols, fromRows_mul,
      fromRows_mul, mul_fromCols, mul_fromCols, mul_fromCols, fromRows_fromCols_eq_fromBlocks,
      hCC, hCG, hCH, hGC, hGG, hGH, hHC, hHG, hHH, fromCols_zero, fromRows_zero, fromBlocks_one,
      fromBlocks_one]
  have hT : Fintype.card (FrameIdx D m) = n := by
    rw [← hcard]
    simp [Fintype.card_congr (frameEquiv D m)]
  let g : Fin n ≃ Fin D ⊕ (Fin m ⊕ Fin D) :=
    (Fintype.orderIsoFinOfCardEq (FrameIdx D m) hT).toEquiv.trans (frameEquiv D m)
  refine ⟨E.submatrix id g, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff']
    show (E.submatrix id g)ᴴ * E.submatrix id g = 1
    rw [conjTranspose_submatrix, ← submatrix_mul _ _ g id g Function.bijective_id, hE,
      submatrix_one_equiv]
  · intro s b b' t h1 h2 h3 hb ht hb'
    have hs : s * E = E * fromBlocks b 0 0 (fromBlocks t 0 0 b') := by
      rw [hEdef, mul_fromCols, mul_fromCols, h1, h2, h3, fromCols_mul_fromBlocks,
        fromCols_mul_fromBlocks]
      simp
    have hΔ : Eᴴ * s * E = fromBlocks b 0 0 (fromBlocks t 0 0 b') := by
      rw [Matrix.mul_assoc, hs, ← Matrix.mul_assoc, hE, Matrix.one_mul]
    have hM : (E.submatrix id g)ᴴ * s * E.submatrix id g =
        (fromBlocks b 0 0 (fromBlocks t 0 0 b')).submatrix g g := by
      rw [← hΔ, submatrix_mul _ _ g id g Function.bijective_id,
        submatrix_mul _ _ g id id Function.bijective_id, submatrix_id_id,
        conjTranspose_submatrix]
    rw [hM]
    intro x y hxy
    exact block_zero b b' t hb ht hb' _ _ ((Fintype.orderIsoFinOfCardEq (FrameIdx D m) hT).lt_iff_lt.2 hxy)

theorem unitary_adapted_triangularises : ∀ {n D m : ℕ} (J : Matrix (Fin n) (Fin n) ℂ)
    (J' : Matrix (Fin m) (Fin m) ℂ) (C : Matrix (Fin n) (Fin D) ℂ) (R : Matrix (Fin n) (Fin m) ℂ),
    J * J = 1 → Jᴴ = J → Cᴴ * C = 1 → Cᴴ * J * C = 0 → Rᴴ * R = 1 → J * R = R * J' →
    Cᴴ * R = 0 → C * Cᴴ + J * C * Cᴴ * J + R * Rᴴ = 1 →
    ∀ U₀ ∈ Matrix.unitaryGroup (Fin m) ℂ, ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ,
      ∀ (s : Matrix (Fin n) (Fin n) ℂ) (b b' : Matrix (Fin D) (Fin D) ℂ)
        (t : Matrix (Fin m) (Fin m) ℂ),
        s * C = C * b → s * (R * U₀) = (R * U₀) * t → s * (J * C) = (J * C) * b' →
        b.BlockTriangular id → t.BlockTriangular id → (∀ x y, x < y → b' x y = 0) →
        (Uᴴ * s * U).BlockTriangular id := by
  intro n D m J J' C R hJJ hJh hCC hCJC hRR hJR hCR hsum U₀ hU₀
  have hU : U₀ᴴ * U₀ = 1 := (Matrix.mem_unitaryGroup_iff').1 hU₀
  have hRC : Rᴴ * C = 0 := by
    have := congrArg conjTranspose hCR
    simpa [conjTranspose_mul] using this
  have hRJ : Rᴴ * J = J'ᴴ * Rᴴ := by
    have := congrArg conjTranspose hJR
    simpa [conjTranspose_mul, hJh] using this
  have t1 : trace (C * Cᴴ) = (D : ℂ) := by
    rw [trace_mul_comm, hCC, trace_one]; simp
  have t2 : trace (J * C * Cᴴ * J) = (D : ℂ) := by
    rw [trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hJJ, Matrix.one_mul, t1]
  have t3 : trace (R * Rᴴ) = (m : ℂ) := by
    rw [trace_mul_comm, hRR, trace_one]; simp
  have hcard : D + (m + D) = n := by
    have h := congrArg trace hsum
    rw [trace_add, trace_add, t1, t2, t3, trace_one] at h
    simp only [Fintype.card_fin] at h
    have h' : ((D + D + m : ℕ) : ℂ) = (n : ℂ) := by push_cast; exact h
    have h'' : D + D + m = n := by exact_mod_cast h'
    omega
  refine unitary_of_blocks C (J * C) (R * U₀) hCC ?_ ?_ ?_ ?_ ?_ hcard
  · rw [← Matrix.mul_assoc, hCR, Matrix.zero_mul]
  · rw [← Matrix.mul_assoc, hCJC]
  · rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Rᴴ, hRR, Matrix.one_mul, hU]
  · rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Rᴴ, hRJ, Matrix.mul_assoc, hRC]
    simp
  · rw [conjTranspose_mul, hJh, Matrix.mul_assoc, ← Matrix.mul_assoc J, hJJ, Matrix.one_mul, hCC]

end GlobalTheory.CompanionTheory.WittFrame
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryExtensionOfBlockStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_extension_of_block : ∀ {n D m : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) (J' : Matrix (Fin m) (Fin m) ℂ) (C : Matrix (Fin n) (Fin D) ℂ) (R : Matrix (Fin n) (Fin m) ℂ), J * J = 1 → Jᴴ = J → Cᴴ * C = 1 → Cᴴ * J * C = 0 → Rᴴ * R = 1 → J * R = R * J' → Cᴴ * R = 0 → C * Cᴴ + J * C * Cᴴ * J + R * Rᴴ = 1 → ∀ U₀ ∈ Matrix.unitaryGroup (Fin m) ℂ, ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ (s : Matrix (Fin n) (Fin n) ℂ) (b b' : Matrix (Fin D) (Fin D) ℂ) (t : Matrix (Fin m) (Fin m) ℂ), s * C = C * b → s * (R * U₀) = (R * U₀) * t → s * (J * C) = (J * C) * b' → b.BlockTriangular id → t.BlockTriangular id → (∀ x y, x < y → b' x y = 0) → (Uᴴ * s * U).BlockTriangular id := by
  first | exact @GlobalTheory.CompanionTheory.WittFrame.unitary_adapted_triangularises | exact GlobalTheory.CompanionTheory.WittFrame.unitary_adapted_triangularises | (intros; apply GlobalTheory.CompanionTheory.WittFrame.unitary_adapted_triangularises <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryLiftCommutingInvolution
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryLiftCommutingInvolution
open Matrix

namespace GlobalTheory.CompanionTheory.UnitaryAssembly

theorem exists_unitary_assemble : ∀ {n D m : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) (J' : Matrix (Fin m) (Fin m) ℂ) (C : Matrix (Fin n) (Fin D) ℂ) (R : Matrix (Fin n) (Fin m) ℂ), J * J = 1 → Jᴴ = J → Cᴴ * C = 1 → Cᴴ * J * C = 0 → Rᴴ * R = 1 → J * R = R * J' → Cᴴ * R = 0 → C * Cᴴ + J * C * Cᴴ * J + R * Rᴴ = 1 → ∀ k₀ ∈ Matrix.unitaryGroup (Fin D) ℂ, ∀ kR ∈ Matrix.unitaryGroup (Fin m) ℂ, kR * J' = J' * kR → ∃ k ∈ Matrix.unitaryGroup (Fin n) ℂ, k * J = J * k ∧ k * C = C * k₀ ∧ kᴴ * C = C * k₀ᴴ ∧ kᴴ * R = R * kRᴴ ∧ kᴴ * (J * C) = (J * C) * k₀ᴴ := by
  intro n D m J J' C R hJJ hJh hCC hCJC hRR hJR hCR hsum k₀ hk₀ kR hkR hkRJ
  rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose] at hk₀ hkR
  have hRC : Rᴴ * C = 0 := by
    have h := congrArg conjTranspose hCR
    simpa [conjTranspose_mul] using h
  have hJ'h : J'ᴴ = J' := by
    have h1 : J' = Rᴴ * (J * R) := by
      rw [hJR, ← Matrix.mul_assoc, hRR, Matrix.one_mul]
    rw [h1]
    simp [conjTranspose_mul, hJh, Matrix.mul_assoc]
  have hRJ : Rᴴ * J = J' * Rᴴ := by
    have h := congrArg conjTranspose hJR
    simpa only [conjTranspose_mul, hJh, hJ'h] using h
  have c2 : Cᴴ * (J * C) = 0 := by rw [← Matrix.mul_assoc]; exact hCJC
  have a1 : ∀ {p : Type} (X : Matrix (Fin D) p ℂ), Cᴴ * (C * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hCC, Matrix.one_mul]
  have a2 : ∀ {p : Type} (X : Matrix (Fin D) p ℂ), Cᴴ * (J * (C * X)) = 0 := fun X => by
    rw [← Matrix.mul_assoc J C X, ← Matrix.mul_assoc, c2, Matrix.zero_mul]
  have a3 : ∀ {p : Type} (X : Matrix (Fin m) p ℂ), Cᴴ * (R * X) = 0 := fun X => by
    rw [← Matrix.mul_assoc, hCR, Matrix.zero_mul]
  have a4 : ∀ {p : Type} (X : Matrix (Fin m) p ℂ), Rᴴ * (R * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hRR, Matrix.one_mul]
  have a5 : ∀ {p : Type} (X : Matrix (Fin D) p ℂ), Rᴴ * (C * X) = 0 := fun X => by
    rw [← Matrix.mul_assoc, hRC, Matrix.zero_mul]
  have a6 : ∀ {p : Type} (X : Matrix (Fin n) p ℂ), J * (J * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  have a7 : ∀ {p : Type} (X : Matrix (Fin m) p ℂ), J * (R * X) = R * (J' * X) := fun X => by
    rw [← Matrix.mul_assoc, hJR, Matrix.mul_assoc]
  have a8 : ∀ {p : Type} (X : Matrix (Fin n) p ℂ), Rᴴ * (J * X) = J' * (Rᴴ * X) := fun X => by
    rw [← Matrix.mul_assoc, hRJ, Matrix.mul_assoc]
  have a9 : ∀ {p : Type} (X : Matrix (Fin D) p ℂ), k₀ * (k₀ᴴ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hk₀, Matrix.one_mul]
  have a10 : ∀ {p : Type} (X : Matrix (Fin m) p ℂ), kR * (kRᴴ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hkR, Matrix.one_mul]
  have a11 : ∀ {p : Type} (X : Matrix (Fin m) p ℂ), kR * (J' * X) = J' * (kR * X) := fun X => by
    rw [← Matrix.mul_assoc, hkRJ, Matrix.mul_assoc]
  have hs : C * Cᴴ + J * (C * (Cᴴ * J)) + R * Rᴴ = 1 := by
    simpa only [Matrix.mul_assoc] using hsum
  refine ⟨C * k₀ * Cᴴ + J * C * k₀ * Cᴴ * J + R * kR * Rᴴ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose]
    simp only [Matrix.add_mul, Matrix.mul_add, conjTranspose_add, conjTranspose_mul,
      conjTranspose_conjTranspose, hJh, Matrix.mul_assoc, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
      hCC, c2, hCR, hRR, hRC, hJJ, hJR, hRJ, hk₀, hkR, Matrix.mul_zero, Matrix.zero_mul,
      add_zero, zero_add, Matrix.mul_one, Matrix.one_mul]
    rw [← hs]
  all_goals
    simp only [Matrix.add_mul, Matrix.mul_add, conjTranspose_add, conjTranspose_mul,
      conjTranspose_conjTranspose, hJh, Matrix.mul_assoc, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
      a11, hCC, c2, hCR, hRR, hRC, hJJ, hJR, hRJ, hk₀, hkR, hkRJ, Matrix.mul_zero, Matrix.zero_mul,
      add_zero, zero_add, Matrix.mul_one, Matrix.one_mul]
    try abel

end GlobalTheory.CompanionTheory.UnitaryAssembly
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryLiftCommutingInvolutionStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_lift_commuting_involution : ∀ {n D m : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) (J' : Matrix (Fin m) (Fin m) ℂ) (C : Matrix (Fin n) (Fin D) ℂ) (R : Matrix (Fin n) (Fin m) ℂ), J * J = 1 → Jᴴ = J → Cᴴ * C = 1 → Cᴴ * J * C = 0 → Rᴴ * R = 1 → J * R = R * J' → Cᴴ * R = 0 → C * Cᴴ + J * C * Cᴴ * J + R * Rᴴ = 1 → ∀ k₀ ∈ Matrix.unitaryGroup (Fin D) ℂ, ∀ kR ∈ Matrix.unitaryGroup (Fin m) ℂ, kR * J' = J' * kR → ∃ k ∈ Matrix.unitaryGroup (Fin n) ℂ, k * J = J * k ∧ k * C = C * k₀ ∧ kᴴ * C = C * k₀ᴴ ∧ kᴴ * R = R * kRᴴ ∧ kᴴ * (J * C) = (J * C) * k₀ᴴ := by
  first | exact @GlobalTheory.CompanionTheory.UnitaryAssembly.exists_unitary_assemble | exact GlobalTheory.CompanionTheory.UnitaryAssembly.exists_unitary_assemble | (intros; apply GlobalTheory.CompanionTheory.UnitaryAssembly.exists_unitary_assemble <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieAlgebraStarClosedBracket
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieAlgebraStarClosedBracket
open Matrix

namespace GlobalTheory.CompanionTheory.UnitaryBlock

theorem block_diagonal_of_keeps_frame : ∀ {n D m : ℕ} (J : Matrix (Fin n) (Fin n) ℂ)
    (J' : Matrix (Fin m) (Fin m) ℂ) (C : Matrix (Fin n) (Fin D) ℂ)
    (R : Matrix (Fin n) (Fin m) ℂ), J * J = 1 → Jᴴ = J → Cᴴ * C = 1 → Rᴴ * R = 1 →
    J * R = R * J' → Cᴴ * R = 0 → C * Cᴴ + J * C * Cᴴ * J + R * Rᴴ = 1 →
    ∀ (g : Matrix (Fin n) (Fin n) ℂ) (h : Matrix (Fin D) (Fin D) ℂ), gᴴ * J * g = J →
    g * C = C * h → gᴴ * C = C * hᴴ →
    IsUnit h ∧ g * (J * C) = (J * C) * (hᴴ)⁻¹ ∧ g * R = R * (Rᴴ * g * R) ∧
      (Rᴴ * g * R)ᴴ * J' * (Rᴴ * g * R) = J' := by
  intro n D m J J' C R hJJ hJh hC hR hJR hCR hsum g h hg hgC hgHC
  have hl : (J * gᴴ * J) * g = 1 := by
    calc (J * gᴴ * J) * g = J * (gᴴ * J * g) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg, hJJ]
  have hr : g * (J * gᴴ * J) = 1 := mul_eq_one_comm.mp hl
  have hgJ : g * J * gᴴ = J := by
    calc g * J * gᴴ = g * (J * gᴴ * J) * J := by
          simp only [Matrix.mul_assoc, hJJ, Matrix.mul_one]
      _ = J := by rw [hr, Matrix.one_mul]

  obtain ⟨k, hkdef⟩ : ∃ k, k = Cᴴ * (J * gᴴ * J) * C := ⟨_, rfl⟩
  have hk : k * h = 1 := by
    calc k * h = Cᴴ * (J * gᴴ * J) * (C * h) := by
          rw [hkdef]; simp only [Matrix.mul_assoc]
      _ = Cᴴ * ((J * gᴴ * J) * g) * C := by
          rw [← hgC]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hl, Matrix.mul_one, hC]
  have hk' : h * k = 1 := mul_eq_one_comm.mp hk
  have hunit : IsUnit h := ⟨⟨h, k, hk', hk⟩, rfl⟩
  have hdet : IsUnit hᴴ.det := by
    have : IsUnit hᴴ := by
      refine ⟨⟨hᴴ, kᴴ, ?_, ?_⟩, rfl⟩
      · rw [← Matrix.conjTranspose_mul, hk, Matrix.conjTranspose_one]
      · rw [← Matrix.conjTranspose_mul, hk', Matrix.conjTranspose_one]
    exact (Matrix.isUnit_iff_isUnit_det _).mp this
  have hJC : g * (J * C) * hᴴ = J * C := by
    calc g * (J * C) * hᴴ = g * J * (C * hᴴ) := by simp only [Matrix.mul_assoc]
      _ = g * J * gᴴ * C := by rw [← hgHC]; simp only [Matrix.mul_assoc]
      _ = J * C := by rw [hgJ]
  have hsecond : g * (J * C) = (J * C) * (hᴴ)⁻¹ := by
    calc g * (J * C) = g * (J * C) * (hᴴ * (hᴴ)⁻¹) := by
          rw [Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
      _ = (g * (J * C) * hᴴ) * (hᴴ)⁻¹ := by simp only [Matrix.mul_assoc]
      _ = (J * C) * (hᴴ)⁻¹ := by rw [hJC]

  have hgpC : (J * gᴴ * J) * C = C * k := by
    calc (J * gᴴ * J) * C = (J * gᴴ * J) * C * (h * k) := by rw [hk', Matrix.mul_one]
      _ = (J * gᴴ * J) * (C * h) * k := by simp only [Matrix.mul_assoc]
      _ = ((J * gᴴ * J) * g) * C * k := by rw [← hgC]; simp only [Matrix.mul_assoc]
      _ = C * k := by rw [hl, Matrix.one_mul]
  have hCgR : Cᴴ * (g * R) = 0 := by
    have hadj : Cᴴ * g = h * Cᴴ := by
      have := congrArg Matrix.conjTranspose hgHC
      simpa [Matrix.conjTranspose_mul] using this
    calc Cᴴ * (g * R) = (Cᴴ * g) * R := by simp only [Matrix.mul_assoc]
      _ = h * (Cᴴ * R) := by rw [hadj, Matrix.mul_assoc]
      _ = 0 := by rw [hCR, Matrix.mul_zero]
  have hgHJC : gᴴ * J * C = J * C * k := by
    calc gᴴ * J * C = (J * J) * (gᴴ * J * C) := by rw [hJJ, Matrix.one_mul]
      _ = J * ((J * gᴴ * J) * C) := by simp only [Matrix.mul_assoc]
      _ = J * C * k := by rw [hgpC, Matrix.mul_assoc]
  have hCJg : Cᴴ * J * g = kᴴ * Cᴴ * J := by
    have := congrArg Matrix.conjTranspose hgHJC
    simpa [Matrix.conjTranspose_mul, hJh, Matrix.mul_assoc] using this
  have hCJgR : Cᴴ * J * (g * R) = 0 := by
    calc Cᴴ * J * (g * R) = (Cᴴ * J * g) * R := by simp only [Matrix.mul_assoc]
      _ = kᴴ * Cᴴ * (J * R) := by rw [hCJg]; simp only [Matrix.mul_assoc]
      _ = kᴴ * (Cᴴ * R) * J' := by rw [hJR]; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hCR, Matrix.mul_zero, Matrix.zero_mul]
  have hthird : g * R = R * (Rᴴ * g * R) := by
    calc g * R = (C * Cᴴ + J * C * Cᴴ * J + R * Rᴴ) * (g * R) := by rw [hsum, Matrix.one_mul]
      _ = C * (Cᴴ * (g * R)) + J * C * (Cᴴ * J * (g * R)) + R * (Rᴴ * g * R) := by
          simp only [Matrix.add_mul, Matrix.mul_assoc]
      _ = R * (Rᴴ * g * R) := by rw [hCgR, hCJgR]; simp
  refine ⟨hunit, hsecond, hthird, ?_⟩
  have hRJ : R * J' = J * R := hJR.symm
  have hRhJR : Rᴴ * J * R = J' := by
    calc Rᴴ * J * R = Rᴴ * (J * R) := by rw [Matrix.mul_assoc]
      _ = Rᴴ * R * J' := by rw [hJR, Matrix.mul_assoc]
      _ = J' := by rw [hR, Matrix.one_mul]
  calc (Rᴴ * g * R)ᴴ * J' * (Rᴴ * g * R)
      = Rᴴ * gᴴ * (R * J') * (Rᴴ * g * R) := by
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    _ = Rᴴ * gᴴ * J * (R * (Rᴴ * g * R)) := by rw [hRJ]; simp only [Matrix.mul_assoc]
    _ = Rᴴ * (gᴴ * J * g) * R := by rw [← hthird]; simp only [Matrix.mul_assoc]
    _ = J' := by rw [hg, hRhJR]

end GlobalTheory.CompanionTheory.UnitaryBlock
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieAlgebraStarClosedBracketStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolic_stabilizer_block_unit : ∀ {n D m : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) (J' : Matrix (Fin m) (Fin m) ℂ) (C : Matrix (Fin n) (Fin D) ℂ) (R : Matrix (Fin n) (Fin m) ℂ), J * J = 1 → Jᴴ = J → Cᴴ * C = 1 → Rᴴ * R = 1 → J * R = R * J' → Cᴴ * R = 0 → C * Cᴴ + J * C * Cᴴ * J + R * Rᴴ = 1 → ∀ (g : Matrix (Fin n) (Fin n) ℂ) (h : Matrix (Fin D) (Fin D) ℂ), gᴴ * J * g = J → g * C = C * h → gᴴ * C = C * hᴴ → IsUnit h ∧ g * (J * C) = (J * C) * (hᴴ)⁻¹ ∧ g * R = R * (Rᴴ * g * R) ∧ (Rᴴ * g * R)ᴴ * J' * (Rᴴ * g * R) = J' := by
  first | exact @GlobalTheory.CompanionTheory.UnitaryBlock.block_diagonal_of_keeps_frame | exact GlobalTheory.CompanionTheory.UnitaryBlock.block_diagonal_of_keeps_frame | (intros; apply GlobalTheory.CompanionTheory.UnitaryBlock.block_diagonal_of_keeps_frame <;> assumption)
end
end

open Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.LeviIwa

theorem block_qr {D : ℕ} (τ : Fin D → ℕ) (hτ : Monotone τ) (h : Matrix (Fin D) (Fin D) ℂ) (hu : IsUnit h)
    (ht : h.BlockTriangular τ) : ∃ k ∈ Matrix.unitaryGroup (Fin D) ℂ, ∃ b : Matrix (Fin D) (Fin D) ℂ,
      h = k * b ∧ b.BlockTriangular id ∧ k.BlockTriangular τ ∧ kᴴ.BlockTriangular τ := by
  obtain ⟨k, hk, b, rfl, hb⟩ := GlobalTheory.T.iwasawa_unitary_upper_triangular h hu
  have hk1 : k * kᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hk
  have hk2 : kᴴ * k = 1 := Matrix.mem_unitaryGroup_iff'.1 hk
  have hbu : IsUnit b := by
    have : kᴴ * (k * b) = b := by rw [← Matrix.mul_assoc, hk2, Matrix.one_mul]
    rw [← this]
    exact (IsUnit.of_mul_eq_one _ hk2).mul hu
  have hbτ : b.BlockTriangular τ := fun i j hij => hb (by
    by_contra hc
    exact absurd (hτ (not_lt.1 hc)) (not_le.2 hij))
  haveI : Invertible b := hbu.invertible
  have hbi : (b⁻¹).BlockTriangular τ := Matrix.blockTriangular_inv_of_blockTriangular hbτ
  have hkeq : k = (k * b) * b⁻¹ := by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det b).1 hbu), Matrix.mul_one]
  have hkt : k.BlockTriangular τ := hkeq ▸ ht.mul hbi
  have hkinv : kᴴ = k⁻¹ := (Matrix.inv_eq_left_inv hk2).symm
  haveI : Invertible k := (IsUnit.of_mul_eq_one _ hk1).invertible
  exact ⟨k, hk, b, rfl, hb, hkt, hkinv ▸ Matrix.blockTriangular_inv_of_blockTriangular hkt⟩

theorem blockTri_keeps {D : ℕ} {τ : Fin D → ℕ} {M : Matrix (Fin D) (Fin D) ℂ} (hM : M.BlockTriangular τ) {i : ℕ}
    {v : Fin D → ℂ} (hv : ∀ c, i ≤ τ c → v c = 0) : ∀ c, i ≤ τ c → (M *ᵥ v) c = 0 := by
  intro c hc
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun d _ => ?_
  by_cases hd : i ≤ τ d
  · rw [hv d hd, mul_zero]
  · rw [hM (lt_of_lt_of_le (not_le.1 hd) hc), zero_mul]

theorem detOn_unitary {n : ℕ} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (V : Submodule ℂ (Fin n → ℂ)) (h : ∀ y ∈ V, k *ᵥ y ∈ V) (h' : ∀ y ∈ V, kᴴ *ᵥ y ∈ V) :
    GlobalTheory.FlagMeas.detOn k V = 1 := by
  have e := GlobalTheory.RealInd.detOn_mul h' h
  rw [Matrix.mem_unitaryGroup_iff'.1 hk |> fun x => (show kᴴ * k = 1 from x), GlobalTheory.RealInd.detOn_one,
    GlobalTheory.LeviPolar.detOn_conjTranspose n k V h h'] at e
  have h0 := GlobalTheory.LeviPolar.detOn_nonneg k V
  nlinarith


open GlobalTheory.RealInd in
theorem iwaOn_leviOne : ∀ {n a : ℕ} (ε : Fin n → Bool) (j : Fin a → ℕ) (W : GlobalTheory.RealInd.Flag n a),
    GlobalTheory.FlagMeas.IsIsoFlag ε j W → (∀ i, 1 ≤ j i) →
      PositivityTheory.Tls2.Iua.IwaOn (GlobalTheory.RealInd.mats (GlobalTheory.RealInd.leviOne ε W)) := by
  intro n a ε j W hW _
  obtain ⟨h0, hm, -, hiso⟩ := hW
  obtain ⟨D, C, τ, hC, hτ, hτa, hfl⟩ := GlobalTheory.T.flag_orthonormal_adapted_basis W h0 hm
  have hJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := PI.UpqRep.Jm_mul_self ε
  have hJh : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := PI.UpqRep.Jm_conjTranspose ε
  set J := Formalism.REAL.Jm ε with hJdef
  have hlast : ∀ v, C *ᵥ v ∈ W (Fin.last a) := fun v =>
    (hfl _ _).2 ⟨v, rfl, fun c hc => absurd (hτa c) (by simpa using hc)⟩
  have hCJ : Cᴴ * J * C = 0 := by
    ext c d
    have := hiso _ (hlast (Pi.single c 1)) _ (hlast (Pi.single d 1))
    have e : star (Pi.single c (1 : ℂ)) = (Pi.single c 1 : Fin D → ℂ) := by
      ext x
      by_cases hx : x = c
      · subst hx; simp
      · simp [hx]
    rw [star_mulVec, ← dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, e,
      Matrix.mulVec_single_one, single_one_dotProduct] at this
    simpa using this
  obtain ⟨m, R, ε', hR, hJR, hCR, hsum⟩ := GlobalTheory.T.isotropic_hyperbolic_complement ε C hC hCJ
  obtain ⟨U₀, hU₀, hI⟩ := CompanionTheory.D.gk.admitted.iwasawa_decomposition_unitary_group m ε'
  obtain ⟨U, hU, hTri⟩ := GlobalTheory.T.unitary_extension_of_block J (Formalism.REAL.Jm ε') C R hJ hJh hC hCJ hR hJR hCR hsum U₀ hU₀
  refine ⟨U, hU, fun g hg => ?_⟩
  obtain ⟨hgU, hgk, hgd⟩ := GlobalTheory.LeviPolar.mem_mats_leviOne.1 hg
  have hgU' : gᴴ * J * g = J := hgU
  have keep : ∀ x : Matrix (Fin n) (Fin n) ℂ, (∀ y ∈ W (Fin.last a), x *ᵥ y ∈ W (Fin.last a)) →
      x * C = C * (Cᴴ * x * C) := fun x hx => by
    refine Matrix.ext_iff_mulVec.2 fun v => ?_
    obtain ⟨w, hw, -⟩ := (hfl _ _).1 (hx _ (hlast v))
    have e : (Cᴴ * x * C) *ᵥ v = w := by
      rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_mulVec, hC,
        Matrix.one_mulVec]
    rw [← Matrix.mulVec_mulVec, hw, ← Matrix.mulVec_mulVec, e]
  set h := Cᴴ * g * C with hh
  have hgC : g * C = C * h := keep g fun y hy => (hgk _ y hy).1
  have hgC' : gᴴ * C = C * hᴴ := by
    have := keep gᴴ fun y hy => (hgk _ y hy).2
    rw [this, hh]
    simp [conjTranspose_mul, Matrix.mul_assoc]
  have htri : h.BlockTriangular τ := by
    intro c d hdc
    have hda : τ d + 1 < a + 1 := by have := hτa d; omega
    have h1 : C *ᵥ Pi.single d 1 ∈ W ⟨τ d + 1, hda⟩ := (hfl _ _).2 ⟨_, rfl, fun c' hc' => by
      have : c' ≠ d := by rintro rfl; simp at hc'
      simp [this]⟩
    obtain ⟨v, hv, hv0⟩ := (hfl _ _).1 ((hgk _ _ h1).1)
    have h2 : h *ᵥ Pi.single d 1 = v := by
      rw [hh, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_mulVec, hC,
        Matrix.one_mulVec]
    have h3 := congrFun h2 c
    rw [Matrix.mulVec_single_one] at h3
    simpa [hv0 c (by simpa using hdc)] using h3
  obtain ⟨hu, hgJC, hgR, hgRU⟩ := GlobalTheory.T.parabolic_stabilizer_block_unit J (Formalism.REAL.Jm ε') C R hJ hJh hC hR hJR hCR hsum g h hgU' hgC hgC'
  obtain ⟨k₀, hk₀, b, hb, hbT, hk₀T, hk₀T'⟩ := block_qr τ hτ h hu htri
  obtain ⟨kR, ⟨hkR, hkRJ⟩, sR, hsR, hgks, hsT⟩ := hI (Rᴴ * g * R) hgRU
  obtain ⟨k, hk, hkJ, hkC, hkC', hkR', hkJC⟩ := GlobalTheory.T.unitary_lift_commuting_involution J (Formalism.REAL.Jm ε') C R hJ hJh hC hCJ hR hJR hCR hsum
    k₀ hk₀ kR hkR hkRJ
  have hk1 : k * kᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hk
  have hk2 : kᴴ * k = 1 := Matrix.mem_unitaryGroup_iff'.1 hk
  have hk01 : k₀ᴴ * k₀ = 1 := Matrix.mem_unitaryGroup_iff'.1 hk₀
  have hkR1 : kRᴴ * kR = 1 := Matrix.mem_unitaryGroup_iff'.1 hkR
  have kk : ∀ (i : Fin (a + 1)) (y : Fin n → ℂ), y ∈ W i → k *ᵥ y ∈ W i := fun i y hy => by
    obtain ⟨v, rfl, hv⟩ := (hfl _ _).1 hy
    exact (hfl _ _).2 ⟨k₀ *ᵥ v, by rw [Matrix.mulVec_mulVec, hkC, ← Matrix.mulVec_mulVec], blockTri_keeps hk₀T hv⟩
  have kk' : ∀ (i : Fin (a + 1)) (y : Fin n → ℂ), y ∈ W i → kᴴ *ᵥ y ∈ W i := fun i y hy => by
    obtain ⟨v, rfl, hv⟩ := (hfl _ _).1 hy
    exact (hfl _ _).2 ⟨k₀ᴴ *ᵥ v, by rw [Matrix.mulVec_mulVec, hkC', ← Matrix.mulVec_mulVec], blockTri_keeps hk₀T' hv⟩
  have hkG : k ∈ mats (leviOne ε W) := GlobalTheory.LeviPolar.mem_mats_leviOne.2
    ⟨by change kᴴ * J * k = J; rw [Matrix.mul_assoc, ← hkJ, ← Matrix.mul_assoc, hk2, Matrix.one_mul],
      fun i y hy => ⟨kk i y hy, kk' i y hy⟩, fun i => detOn_unitary hk _ (kk i) (kk' i)⟩
  have hkhG : kᴴ ∈ mats (leviOne ε W) := GlobalTheory.LeviPolar.mem_mats_leviOne.2
    ⟨by change (kᴴ)ᴴ * J * kᴴ = J; rw [conjTranspose_conjTranspose, hkJ, Matrix.mul_assoc, hk1, Matrix.mul_one],
      fun i y hy => ⟨kk' i y hy, by simpa using kk i y hy⟩,
      fun i => detOn_unitary (Matrix.mem_unitaryGroup_iff.2 (by simpa [star_eq_conjTranspose] using hk2)) _ (kk' i)
        (by rw [conjTranspose_conjTranspose]; exact kk i)⟩
  refine ⟨k, ⟨hkG, hk⟩, kᴴ * g, GlobalTheory.LeviPolar.mats_mul hkhG hg, by rw [← Matrix.mul_assoc, hk1, Matrix.one_mul], ?_⟩
  have hbu : IsUnit b := by
    have : k₀ᴴ * h = b := by rw [hb, ← Matrix.mul_assoc, hk01, Matrix.one_mul]
    rw [← this]
    exact (IsUnit.of_mul_eq_one _ hk01).mul hu
  haveI : Invertible b := hbu.invertible
  have hci : (b⁻¹).BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hbT
  have hbb : b⁻¹ * b = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det b).1 hbu)
  have hhinv : (hᴴ)⁻¹ = k₀ * (b⁻¹)ᴴ := Matrix.inv_eq_right_inv (by
    rw [hb, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc k₀ᴴ, hk01, Matrix.one_mul,
      ← conjTranspose_mul, hbb, conjTranspose_one])
  refine hTri (kᴴ * g) b (b⁻¹)ᴴ (U₀ᴴ * sR * U₀) ?_ ?_ ?_ hbT hsT ?_
  · rw [Matrix.mul_assoc, hgC, ← Matrix.mul_assoc, hkC', Matrix.mul_assoc, hb, ← Matrix.mul_assoc k₀ᴴ, hk01,
      Matrix.one_mul]
  · have hU1 : U₀ * U₀ᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hU₀
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc g, hgR, ← Matrix.mul_assoc kᴴ, ← Matrix.mul_assoc kᴴ, hkR',
      Matrix.mul_assoc R, hgks, ← Matrix.mul_assoc kRᴴ, hkR1, Matrix.one_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U₀, hU1, Matrix.one_mul]
  · rw [Matrix.mul_assoc, hgJC, ← Matrix.mul_assoc, hkJC, Matrix.mul_assoc, hhinv, ← Matrix.mul_assoc k₀ᴴ, hk01,
      Matrix.one_mul]
  · intro x y hxy
    have := hci (show id x < id y from hxy)
    simp [Matrix.conjTranspose_apply, this]

end GlobalTheory.CompanionTheory.LeviIwa
end
end

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.IwaLevi

theorem exists_unitary_iwasawa_leviOne : ∀ {n a : ℕ} {ε : Fin n → Bool} {j : Fin a → ℕ} {W : Flag n a}
    (hW : IsIsoFlag ε j W) (hj : ∀ i, 1 ≤ j i), ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ,
      ∀ g ∈ mats (leviOne ε W), ∃ k ∈ maxCpt (mats (leviOne ε W)), ∃ s ∈ mats (leviOne ε W),
        g = k * s ∧ (Uᴴ * s * U).BlockTriangular id :=
  fun {_ _ ε j W} hW hj => GlobalTheory.CompanionTheory.LeviIwa.iwaOn_leviOne ε j W hW hj

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.IwaLevi

end
