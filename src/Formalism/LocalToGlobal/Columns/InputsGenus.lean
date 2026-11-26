module

public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BridgeFinK
public import Formalism.LocalToGlobal.Columns.RecLevelHost
public import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GenusApproximationProofs.ApproximationAdelicHolds
public import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GenusApproximationProofs.Cayley

@[expose] public section

section -- merged from Formalism.LocalToGlobal.GenusGluing.GenusApproximation.FinalW
section -- merged from Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GenusApproximationProofs.DetAddDiagonalCons
noncomputable section

namespace Formalism.L2.GenusGluing.Gen

open NumberField IsDedekindDomain Matrix Formalism.L2.Col
open scoped TensorProduct

theorem det_add_diagonal_cons {A : Type*} [CommRing A] {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) A) (a : A) (d : Fin n → A) :
    (M + diagonal (Fin.cons a d : Fin (n + 1) → A)).det =
      (M.submatrix Fin.succ Fin.succ + diagonal d).det * a +
        (M + diagonal (Fin.cons 0 d : Fin (n + 1) → A)).det := by
  set N := M + diagonal (Fin.cons 0 d : Fin (n + 1) → A) with hN
  have h1 : M + diagonal (Fin.cons a d : Fin (n + 1) → A) =
      N.updateRow 0 (N 0 + a • Pi.single 0 1) := by
    ext i j
    refine Fin.cases ?_ ?_ i
    · by_cases hj : j = 0
      · subst hj; simp [N]
      · simp [N, hj, Ne.symm hj]
    · intro i
      simp [N, Matrix.diagonal_apply]
  have h2 : (N.updateRow 0 (Pi.single 0 1)).det = (M.submatrix Fin.succ Fin.succ + diagonal d).det := by
    rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
    have hz : ∀ k : Fin n, (N.updateRow 0 (Pi.single 0 1)) 0 k.succ = 0 := by
      intro k; simp [Fin.succ_ne_zero]
    simp only [hz, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
    simp only [Matrix.updateRow_self, Pi.single_eq_same, Fin.val_zero, pow_zero, one_mul,
      Fin.succAbove_zero]
    congr 1
    ext i j
    simp [N, Matrix.diagonal_apply]
  rw [h1, Matrix.det_updateRow_add, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self, h2]
  ring

theorem shiftDiag_of (hS : ShiftOne) : ShiftDiag := by
  intro F E _ _ _ _ _ _ hc v n
  induction n with
  | zero =>
    intro M
    refine ⟨Fin.elim0, fun i => i.elim0, 1, ?_⟩
    simp [Matrix.det_isEmpty]
  | succ n ih =>
    intro M
    obtain ⟨t', ht', w', hw'⟩ := ih (M.submatrix Fin.succ Fin.succ)
    obtain ⟨t0, ht0, w, hw⟩ := hS F E hc v _
      ((M + diagonal (Fin.cons 0 (fun i => iA F E (t' i)) : Fin (n + 1) → _)).det) ⟨w', hw'⟩
    refine ⟨Fin.cons t0 t', ?_, w, ?_⟩
    · intro i
      refine Fin.cases ?_ ?_ i
      · simpa using ht0
      · intro i; simpa using ht' i
    · have hf : (fun i => iA F E ((Fin.cons t0 t' : Fin (n + 1) → E) i)) =
          (Fin.cons (iA F E t0) (fun i => iA F E (t' i)) : Fin (n + 1) → _) := by
        funext i
        refine Fin.cases ?_ ?_ i
        · simp
        · intro i; simp
      rw [hf, det_add_diagonal_cons]
      exact hw

end Formalism.L2.GenusGluing.Gen
end
end

section -- merged from Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GenusApproximationProofs.WeakApproxAllOf
noncomputable section

namespace Formalism.L2.GenusGluing.Gen

open NumberField IsDedekindDomain Matrix Formalism.L2.Col
open scoped TensorProduct

section At

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem intAt_congr {n : ℕ} (v : HeightOneSpectrum (𝓞 F))
    {Y Y' : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (h : eAt E v • Y = eAt E v • Y') :
    IntAt v Y ↔ IntAt v Y' := by
  have h' : ∀ i j, eAt E v * Y i j = eAt E v * Y' i j := fun i j => by
    have := congrFun (congrFun h i) j
    simpa only [Matrix.smul_apply, smul_eq_mul] using this
  unfold IntAt
  simp only [h']

theorem weakApproxU_at (hSD : ShiftDiag) (hCS : CayleyStep) (hII : IntAtInv) (hc : Formalism.BasicNotions.CMData F E) (n : ℕ)
    (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (hx : x ∈ UAd hc n) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ γ ∈ URat hc n,
      IntAt v (((Formalism.UG.bc (iA F E) γ)⁻¹ * x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
        Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ∧
      IntAt v ((x⁻¹ * Formalism.UG.bc (iA F E) γ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
        Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
  classical
  have he : eAt E v * eAt E v = eAt E v := by
    have h := (idempotentCalculation_holds F E).2.1 (fun w => w = v) (fun w => w = v)
    exact h.trans (eP_congr (fun u => and_self_iff))
  have hσe : Formalism.UG.sigR hc.sig (Formalism.L2.Herm.Af F) (eAt E v) = eAt E v := sigR_eP hc _
  obtain ⟨t, ht, w, hw⟩ := hSD F E hc v n (x : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
  have hts : ∀ i, t i * star (t i) = 1 := fun i => by rw [mul_comm]; exact ht i

  let γ0 : GL (Fin n) E :=
    { val := Matrix.diagonal t
      inv := Matrix.diagonal (fun i => star (t i))
      val_inv := by rw [Matrix.diagonal_mul_diagonal]; simp only [hts, Matrix.diagonal_one]
      inv_val := by rw [Matrix.diagonal_mul_diagonal]; simp only [ht, Matrix.diagonal_one] }
  have hγ0 : γ0 ∈ URat hc n := by
    show Formalism.UG.cT _ (Matrix.diagonal t) * 1 * Matrix.diagonal t = 1
    rw [Matrix.mul_one]
    unfold Formalism.UG.cT
    rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
    have h1 : ∀ i, ((hc.sig : E →ₐ[F] E) : E →+* E) (t i) * t i = 1 := fun i => ht i
    simp only [h1, Matrix.diagonal_one]
  set g0 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) := Formalism.UG.bc (iA F E) γ0 with hg0
  have hg0v : (g0 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = Matrix.diagonal fun i => iA F E (t i) := by
    rw [hg0]
    show (Matrix.diagonal t).map (iA F E) = _
    exact Matrix.diagonal_map (map_zero _)
  have hg0A : g0 ∈ UAd hc n := (ratIn hc n ⟨γ0, hγ0⟩).2
  rw [← hg0v] at hw

  set x1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) := g0⁻¹ * x with hx1
  have hx1A : x1 ∈ UAd hc n := mul_mem (inv_mem hg0A) hx
  have hJ : (1 : Matrix (Fin n) (Fin n) E).map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F)) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  have hx1U : x1 ∈ Formalism.UG.UJ (Formalism.UG.sigR hc.sig (Formalism.L2.Herm.Af F))
      (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
    have h := hx1A
    change _ ∈ Formalism.UG.UJ (Formalism.UG.sigR hc.sig (Formalism.L2.Herm.Af F))
      ((1 : Matrix (Fin n) (Fin n) E).map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F))) at h
    rwa [hJ] at h
  set x2 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) := glueU he x1 with hx2
  have hx2A : x2 ∈ UAd hc n := by
    change _ ∈ Formalism.UG.UJ (Formalism.UG.sigR hc.sig (Formalism.L2.Herm.Af F))
      ((1 : Matrix (Fin n) (Fin n) E).map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F)))
    rw [hJ]
    exact glueU_mem _ he hσe hx1U

  set P : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) :=
    (x : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) + (g0 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) with hP
  set B : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) :=
    w • (Matrix.adjugate P * (g0 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) with hB
  have h1x : (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) + (x1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
      ((g0⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) * P := by
    rw [hx1, Units.val_mul, hP, Matrix.mul_add, Units.inv_mul, add_comm]
  have hxB : ((1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) + (x1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) * B =
      (w * P.det) • (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
    rw [h1x, hB]
    calc ((g0⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) * P *
          (w • (Matrix.adjugate P * (g0 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))))
        = w • (((g0⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *
            (P * Matrix.adjugate P) * (g0 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) := by
          rw [Matrix.mul_smul]; simp only [Matrix.mul_assoc]
      _ = w • (((g0⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *
            (P.det • (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) *
            (g0 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) := by rw [Matrix.mul_adjugate]
      _ = (w * P.det) • (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
          rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Units.inv_mul, smul_smul]
  have heB : eAt E v • (((1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) +
      (x1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) * B) =
      eAt E v • (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
    rw [hxB, smul_smul, mul_comm w, hw]
  have hglue1 : glueM (eAt E v) (((1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) +
      (x1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) * B) = 1 := by
    unfold glueM
    rw [heB, ← add_smul, add_sub_cancel, one_smul]
  set c : E ⊗[F] Formalism.L2.Herm.Af F := iA F E (2⁻¹ : E) with hcdef
  have h2c : (2 : E ⊗[F] Formalism.L2.Herm.Af F) * c = 1 := by
    rw [hcdef, ← map_ofNat (iA F E) 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]
  set s : E ⊗[F] Formalism.L2.Herm.Af F := eAt E v + 2 * (1 - eAt E v) with hs
  set s' : E ⊗[F] Formalism.L2.Herm.Af F := eAt E v + c * (1 - eAt E v) with hs'
  have hss : s * s' = 1 := by
    rw [hs, hs']
    linear_combination (-c) * he + (1 - eAt E v) ^ 2 * h2c
  have h1x2 : (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) + (x2 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
      s • glueM (eAt E v) ((1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) +
        (x1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) := by
    rw [hx2, glueU_val, hs]
    ext i j
    simp only [glueM, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    linear_combination ((x1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) i j) * he
  have hright : ((1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) + (x2 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) *
      (s' • glueM (eAt E v) B) = 1 := by
    rw [h1x2, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hss, one_smul, glueM_mul he, hglue1]
  have hx2u : IsUnit ((1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) +
      (x2 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) :=
    ⟨⟨_, _, hright, mul_eq_one_comm.mp hright⟩, rfl⟩

  obtain ⟨γ1, hγ1, hI1⟩ := hCS F E hc n v x2 hx2A hx2u
  have hI1' : IntAt v ((x1⁻¹ * Formalism.UG.bc (iA F E) γ1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
      Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
    refine (intAt_congr v ?_).1 hI1
    rw [Units.val_mul, Units.val_mul]
    exact glue_smul_same he _ _
  have hγ : γ0 * γ1 ∈ URat hc n := mul_mem hγ0 hγ1
  have hprod : x1⁻¹ * Formalism.UG.bc (iA F E) γ1 = x⁻¹ * Formalism.UG.bc (iA F E) (γ0 * γ1) := by
    rw [hx1, map_mul, _root_.mul_inv_rev, inv_inv, mul_assoc]
  rw [hprod] at hI1'
  refine ⟨γ0 * γ1, hγ, ?_, hI1'⟩
  have hyA : x⁻¹ * Formalism.UG.bc (iA F E) (γ0 * γ1) ∈ UAd hc n :=
    mul_mem (inv_mem hx) (ratIn hc n ⟨γ0 * γ1, hγ⟩).2
  have hinv : (Formalism.UG.bc (iA F E) (γ0 * γ1))⁻¹ * x = (x⁻¹ * Formalism.UG.bc (iA F E) (γ0 * γ1))⁻¹ := by
    rw [_root_.mul_inv_rev, inv_inv]
  rw [hinv]
  exact hII F E hc n v _ hyA hI1'

end At

theorem weakApproxAll_of : ShiftDiag → CayleyStep → IntAtInv → WeakApproxAll := by
  intro hSD hCS hII F E _ _ _ _ _ _ hc n x hx v
  exact weakApproxU_at hSD hCS hII hc n x hx v

end Formalism.L2.GenusGluing.Gen
end
end

section -- merged from Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GenusApproximationProofs.AsmOfMemComplF
noncomputable section

namespace Formalism.L2.GenusGluing.Gen

open NumberField IsDedekindDomain Matrix Formalism.L2.Col
open scoped TensorProduct

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem glEquiv_apply_lemma {n : ℕ} (γ : GL (Fin n) E) (x : Sp E n) :
    Formalism.UG.glEquiv γ x = (γ : Matrix (Fin n) (Fin n) E) *ᵥ x := rfl

theorem asm_mem_gmap {n : ℕ} (γ : GL (Fin n) E) (L : Submodule (𝓞 E) (Sp E n)) (y : Sp E n) :
    y ∈ Formalism.HermitianLatticesTheory.gmap (Formalism.UG.glEquiv γ) L ↔ ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ y ∈ L := by
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [glEquiv_apply_lemma, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    exact hx
  · intro h
    refine ⟨_, h, ?_⟩
    rw [glEquiv_apply_lemma, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]

theorem placeIndicator_mul_self (hI : IdemCalc) (P : HeightOneSpectrum (𝓞 F) → Prop) : eP E P * eP E P = eP E P := by
  rw [(hI F E).2.1 P P]
  simp only [and_self]

theorem asm_mulVec_int {n : ℕ} (hI : IdemCalc) (P : HeightOneSpectrum (𝓞 F) → Prop)
    (M : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (w : Fin n → E ⊗[F] Formalism.L2.Herm.Af F)
    (hM : ∀ i j, eP E P * M i j ∈ Formalism.L2.Herm.intAf F E) (hw : ∀ j, eP E P * w j ∈ Formalism.L2.Herm.intAf F E)
    (i : Fin n) : eP E P * (M *ᵥ w) i ∈ Formalism.L2.Herm.intAf F E := by
  have he := placeIndicator_mul_self (E := E) hI P
  change eP E P * (∑ j, M i j * w j) ∈ Formalism.L2.Herm.intAf F E
  rw [Finset.mul_sum]
  refine sum_mem (fun j _ => ?_)
  have hj : eP E P * (M i j * w j) = (eP E P * M i j) * (eP E P * w j) := by
    calc eP E P * (M i j * w j) = (eP E P * eP E P) * (M i j * w j) := by rw [he]
      _ = (eP E P * M i j) * (eP E P * w j) := by ring
  rw [hj]
  exact mul_mem (hM i j) (hw j)

theorem asm_smul_mulVec {n : ℕ} (f : E ⊗[F] Formalism.L2.Herm.Af F) (M M' : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (h : f • M = f • M') (w : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) (i : Fin n) :
    f * (M *ᵥ w) i = f * (M' *ᵥ w) i := by
  have hij : ∀ j, f * M i j = f * M' i j := fun j => by
    have hh := congrFun (congrFun h i) j
    simpa [Matrix.smul_apply, smul_eq_mul] using hh
  change f * (∑ j, M i j * w j) = f * (∑ j, M' i j * w j)
  simp only [Finset.mul_sum, ← mul_assoc, hij]

theorem asm_iota_OF (r : 𝓞 F) :
    iA F E (algebraMap (𝓞 F) E r) = iA F E (algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) r)) := by
  first
    | rfl
    | rw [IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E r]

theorem asm_iota_OE_mem (b : 𝓞 E) : iA F E (algebraMap (𝓞 E) E b) ∈ Formalism.L2.Herm.intAf F E := by
  apply Subring.subset_closure
  refine Or.inl ⟨⟨algebraMap (𝓞 E) E b, b, rfl⟩, ?_⟩
  rfl

theorem asm_iota_OF_mem (r : 𝓞 F) : iA F E (algebraMap (𝓞 F) E r) ∈ Formalism.L2.Herm.intAf F E := by
  rw [asm_iota_OF]
  exact asm_iota_OE_mem _

theorem asm_smul_apply {n : ℕ} (c : 𝓞 E) (y : Sp E n) (i : Fin n) : (c • y) i = algebraMap (𝓞 E) E c * y i := by
  show c • y i = _
  exact Algebra.smul_def c (y i)

theorem asm_mem_std {n : ℕ} (y : Sp E n) :
    y ∈ stdLat E n ↔ ∀ i, ∃ b : 𝓞 E, algebraMap (𝓞 E) E b = y i := by
  simp [Formalism.L2.Col.stdLat, Submodule.mem_pi, Submodule.mem_one]

theorem asm_iota_std {n : ℕ} {y : Sp E n} (hy : y ∈ stdLat E n) (i : Fin n) : iA F E (y i) ∈ Formalism.L2.Herm.intAf F E := by
  obtain ⟨b, hb⟩ := (asm_mem_std y).1 hy i
  rw [← hb]
  exact asm_iota_OE_mem b

theorem asm_bc_mulVec {n : ℕ} (γ : GL (Fin n) E) (y : Sp E n) :
    ((Formalism.UG.bc (iA F E) γ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ
      (fun i => iA F E (y i)) = fun i => iA F E (((γ : Matrix (Fin n) (Fin n) E) *ᵥ y) i) := by
  funext i
  rw [RingHom.map_mulVec]
  rfl

theorem asm_mem_complF (v : HeightOneSpectrum (𝓞 F)) (r : 𝓞 F) (hr : r ∉ v.asIdeal) :
    algebraMap (𝓞 F) (𝓞 E) r ∈ complF E v := by
  unfold complF
  exact Submonoid.mem_map_of_mem _ hr

theorem asm_of_mem_complF {v : HeightOneSpectrum (𝓞 F)} {s : 𝓞 E} (hs : s ∈ complF E v) :
    ∃ r : 𝓞 F, r ∉ v.asIdeal ∧ algebraMap (𝓞 F) (𝓞 E) r = s := by
  unfold complF at hs
  obtain ⟨r, hr, rfl⟩ := Submonoid.mem_map.1 hs
  exact ⟨r, hr, rfl⟩

end SlopeTestRemainingChoices

theorem locToAd_of (hG : GenusToPoint) : LocToAd := by
  intro F E _ _ _ _ _ _ hc n hL N hN hU
  exact hG F E hc n N hN (hL hc.cmUnram N hN hU)

theorem adToLoc_of (hP : PointToGenus) : AdToLoc := by
  intro F E _ _ _ _ _ _ hc n hW hU _ N hN hUni
  obtain ⟨x, hx, rfl⟩ := hU N hN hUni
  exact hP F E hc n hW x hx

theorem bridge_of (h1 : LocToAd) (h2 : AdToLoc) : Bridge := by
  intro F E _ _ _ _ _ _ hc n hW
  exact ⟨h1 F E hc n, h2 F E hc n hW⟩

private theorem glob_lemma_2 {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    {n : ℕ} (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (y : Sp E n) :
    y ∈ Formalism.UG.CS.globLat x (stdLat E n) ↔
      ∀ i, (((x⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ (fun j => iA F E (y j))) i ∈ Formalism.L2.Herm.intAf F E := by
  change (((x⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ (fun j => iA F E (y j))) ∈
    Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (stdLat E n) ↔ _
  generalize (((x⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ (fun j => iA F E (y j))) = w
  constructor
  · intro hw i
    let Q : Submodule (Formalism.L2.Herm.intAf F E) (Fin n → E ⊗[F] Formalism.L2.Herm.Af F) :=
      { carrier := {w | ∀ i, w i ∈ Formalism.L2.Herm.intAf F E}
        add_mem' := by
          intro a b ha hb k
          exact add_mem (ha k) (hb k)
        zero_mem' := by
          intro k
          exact zero_mem _
        smul_mem' := by
          intro c a ha k
          exact mul_mem c.2 (ha k) }
    have hle : Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (stdLat E n) ≤ Q := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨z, hz, rfl⟩ j
      exact asm_iota_std hz j
    exact (hle hw : ∀ k, w k ∈ Formalism.L2.Herm.intAf F E) i
  · intro hw
    have hsum : w = ∑ i, (⟨w i, hw i⟩ : Formalism.L2.Herm.intAf F E) •
        (fun j => iA F E ((Pi.single i (1 : E) : Fin n → E) j)) := by
      funext j
      rw [Finset.sum_apply, Finset.sum_eq_single j]
      · simp [Subring.smul_def]
      · intro b _ hb
        simp [Subring.smul_def, Pi.single_apply, Ne.symm hb]
      · intro h
        exact absurd (Finset.mem_univ j) h
    rw [hsum]
    refine Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨Pi.single i (1 : E), ?_, rfl⟩))
    refine (asm_mem_std _).2 (fun k => ⟨(Pi.single i (1 : 𝓞 E) : Fin n → 𝓞 E) k, ?_⟩)
    rcases eq_or_ne k i with rfl | h
    · simp
    · simp [Pi.single_apply, h]

private theorem unit_lemma_5 {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} (g : Sp E n ≃ₗ[E] Sp E n)
    (hg : g ∈ Formalism.HermitianLatticesTheory.isom (hStd E n)) : ∃ γ ∈ URat hc n, Formalism.UG.glEquiv γ = g := by
  set γ : GL (Fin n) E := Matrix.GeneralLinearGroup.toLin.symm
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv E (Fin n → E)).symm g) with hγdef
  have hγg : Formalism.UG.glEquiv γ = g := by
    simp only [Formalism.UG.glEquiv, hγdef, MulEquiv.apply_symm_apply]
  refine ⟨γ, ?_, hγg⟩
  show Formalism.UG.cT (hc.sig : E →+* E) (γ : Matrix (Fin n) (Fin n) E) * 1 * (γ : Matrix (Fin n) (Fin n) E) = 1
  rw [Matrix.mul_one]
  change (γ : Matrix (Fin n) (Fin n) E)ᴴ * (γ : Matrix (Fin n) (Fin n) E) = 1
  ext j k
  have h := hg (Pi.single j 1) (Pi.single k 1)
  rw [← hγg] at h
  simp only [hStd, LinearMap.mk₂'ₛₗ_apply, glEquiv_apply_lemma] at h
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.conjTranspose_apply]
  convert h using 1
  · simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  · simp [Pi.single_apply, apply_ite star, ite_mul, Finset.sum_ite_eq', Finset.sum_ite_eq]
    exact if_congr eq_comm rfl rfl

private theorem over_lemma_6 {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ PP : HeightOneSpectrum (𝓞 E), Formalism.L2.DIV.underPl F PP = v := by
  haveI := v.isMaximal
  haveI : Algebra.IsIntegral (𝓞 F) (𝓞 E) := by
    first
      | infer_instance
      | exact ⟨fun x => (Algebra.IsIntegral.isIntegral (R := ℤ) x).tower_top⟩
  have hker : RingHom.ker (algebraMap (𝓞 F) (𝓞 E)) ≤ v.asIdeal := by
    intro a ha
    rw [RingHom.mem_ker] at ha
    have e : algebraMap (𝓞 F) E a = algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) a) := by
      first
        | rfl
        | exact IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E a
    rw [ha, map_zero] at e
    have e2 : algebraMap (𝓞 F) E a = algebraMap F E (algebraMap (𝓞 F) F a) := by
      first
        | rfl
        | exact IsScalarTower.algebraMap_apply (𝓞 F) F E a
    rw [e2, map_eq_zero_iff _ (algebraMap F E).injective,
      map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)] at e
    rw [e]
    exact zero_mem _
  obtain ⟨Q, hQ, hQv⟩ : ∃ Q : Ideal (𝓞 E), Q.IsMaximal ∧ Q.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal := by
    first
      | exact Ideal.exists_ideal_over_maximal_of_isIntegral v.asIdeal hker
      | exact Ideal.exists_ideal_over_maximal_of_isIntegral inferInstance v.asIdeal hker
  have hQ0 : Q ≠ ⊥ := by
    first
      | exact Ring.ne_bot_of_isMaximal_of_not_isField hQ (NumberField.RingOfIntegers.not_isField (K := E))
      | exact Ring.ne_bot_of_isMaximal_of_not_isField hQ (NumberField.RingOfIntegers.not_isField E)
      | exact Ideal.IsMaximal.ne_bot_of_isIntegral_int hQ
  exact ⟨⟨Q, hQ.isPrime, hQ0⟩, IsDedekindDomain.HeightOneSpectrum.ext hQv⟩

private theorem split_lemma_8 {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hI : IdemCalc) (T : Finset (HeightOneSpectrum (𝓞 F)))
    (u : E ⊗[F] Formalism.L2.Herm.Af F) :
    u ∈ Formalism.L2.Herm.intAf F E ↔ (∀ v ∈ T, eAt E v * u ∈ Formalism.L2.Herm.intAf F E) ∧ eP E (fun v => v ∉ T) * u ∈ Formalism.L2.Herm.intAf F E := by
  constructor
  · intro hu
    exact ⟨fun v _ => mul_mem ((hI F E).1 _) hu, mul_mem ((hI F E).1 _) hu⟩
  · rintro ⟨h1, h2⟩
    have e : u = ∑ v ∈ T, eAt E v * u + eP E (fun v => v ∉ T) * u := by
      rw [← Finset.sum_mul, ← add_mul, (hI F E).2.2 T, one_mul]
    rw [e]
    exact add_mem (sum_mem fun v hv => h1 v hv) h2

open Formalism.HermitianLatticesTheory in
private theorem fullLattice_of_sameGenus {E : Type} [Field E] [NumberField E] [StarRing E]
    {n : ℕ} {N : Submodule (𝓞 E) (Sp E n)} (hN : Submodule.IsLattice E N)
    (hG : SameGenus (hStd E n) (stdLat E n) N) : Submodule.IsFullLattice E N := by
  refine { toIsLattice := hN, span_eq_top := ?_ }
  obtain ⟨p, hp⟩ := Ideal.exists_maximal (𝓞 E)
  let _ := hp.isPrime
  obtain ⟨g, _, hg⟩ := hG p hp
  apply (Submodule.eq_top_iff_forall_basis_mem ((Pi.basisFun E (Fin n)).map g)).2
  intro i
  rw [Module.Basis.map_apply, Pi.basisFun_apply]
  have hi : (Pi.single i (1 : E) : Sp E n) ∈ stdLat E n := by
    simpa using single_mem_stdLat (E := E) i 1
  have hgi : g (Pi.single i (1 : E)) ∈ loc (K := E) p N := by
    rw [← hg, gmap, Submodule.mem_map]
    exact ⟨_, locBasic_le_locS _ _ hi, rfl⟩
  obtain ⟨s, hs, hsi⟩ := locBasic_mem_locS.mp hgi
  have hs₀ : algebraMap (𝓞 E) E s ≠ 0 := by
    intro h
    have hs_zero := (map_eq_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mp h
    exact locBasic_hcompl_not_mem (K := E) p s hs (hs_zero ▸ p.zero_mem)
  let W := Submodule.span E (N : Set (Sp E n))
  have hsmul : algebraMap (𝓞 E) E s • g (Pi.single i (1 : E)) ∈ W :=
    Submodule.subset_span (by rwa [algebraMap_smul])
  simpa only [inv_smul_smul₀ hs₀] using W.smul_mem (algebraMap (𝓞 E) E s)⁻¹ hsmul

theorem genusToPoint_of (hLoc : LocEq) (hMem : MemLocFStd) (hCof : IdemCof) (hI : IdemCalc) (hGl : GlueExists)
    (hCm : Commens) : GenusToPoint := by
  intro F E _ _ _ _ _ _ hc n N hN hG
  obtain ⟨D, hD, hD1, hD2⟩ := hCm F E n N (fullLattice_of_sameGenus hN hG)
  have hfin : {v : HeightOneSpectrum (𝓞 F) | D ∈ v.asIdeal}.Finite := by
    have h0 : Ideal.span ({D} : Set (𝓞 F)) ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact hD
    exact (Ideal.finite_factors h0).subset (fun v hv => Ideal.dvd_span_singleton.2 hv)
  set T := hfin.toFinset with hT
  have memT : ∀ v, v ∈ T ↔ D ∈ v.asIdeal := fun v => hfin.mem_toFinset
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F), ∃ γ ∈ URat hc n,
      Formalism.HermitianLatticesTheory.gmap (Formalism.UG.glEquiv γ) (locF v (stdLat E n)) = locF v N := by
    intro v
    obtain ⟨PP, hPP⟩ := over_lemma_6 (E := E) v
    obtain ⟨g, hg, hgl⟩ := hG PP.asIdeal PP.isMaximal
    obtain ⟨γ, hγ, rfl⟩ := unit_lemma_5 hc g hg
    refine ⟨γ, hγ, ?_⟩
    rw [hLoc F E hc n PP, hLoc F E hc n PP, hPP] at hgl
    exact hgl
  choose γ hγ hγl using hloc
  obtain ⟨x, hx, hx1, hx2⟩ := hGl F E hc n T (fun v => ⟨γ v, hγ v⟩)
  have hx1' : ∀ v ∈ T, eAt E v • ((x⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
      eAt E v • ((Formalism.UG.bc (iA F E) ((γ v)⁻¹) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := hx1
  have hx2' : eP E (fun v => v ∉ T) • ((x⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = eP E (fun v => v ∉ T) • (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := hx2
  refine ⟨x, hx, ?_⟩
  ext y
  rw [glob_lemma_2]
  have hTv : ∀ v ∈ T, ((∀ i, eAt E v * (((x⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ (fun j => iA F E (y j))) i ∈ Formalism.L2.Herm.intAf F E) ↔
      y ∈ locF v N) := by
    intro v hv
    rw [← hγl v, asm_mem_gmap, hMem F E n v]
    refine forall_congr' fun i => ?_
    rw [asm_smul_mulVec _ _ _ (hx1' v hv), asm_bc_mulVec]
  have hout : ∀ i, eP E (fun v => v ∉ T) * (((x⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ (fun j => iA F E (y j))) i =
      eP E (fun v => v ∉ T) * iA F E (y i) := by
    intro i
    rw [asm_smul_mulVec _ _ _ hx2', Matrix.one_mulVec]
  have hPT : eP E (fun v => v ∉ T) = eP E (fun v : HeightOneSpectrum (𝓞 F) => D ∉ v.asIdeal) := by
    congr 1
    funext v
    rw [memT]
  constructor
  · intro hy
    have hloc' : ∀ v ∈ T, y ∈ locF v N := fun v hv =>
      (hTv v hv).1 (fun i => ((split_lemma_8 hI T _).1 (hy i)).1 v hv)
    have hout' : ∀ i, eP E (fun v => v ∉ T) * iA F E (y i) ∈ Formalism.L2.Herm.intAf F E := fun i => by
      rw [← hout i]
      exact ((split_lemma_8 hI T _).1 (hy i)).2
    let J : Ideal (𝓞 F) :=
      { carrier := {a | algebraMap (𝓞 F) (𝓞 E) a • y ∈ N}
        add_mem' := by
          intro a b ha hb
          show algebraMap (𝓞 F) (𝓞 E) (a + b) • y ∈ N
          rw [map_add (f := _), add_smul]
          exact N.add_mem ha hb
        zero_mem' := by
          show algebraMap (𝓞 F) (𝓞 E) 0 • y ∈ N
          rw [map_zero, zero_smul]
          exact N.zero_mem
        smul_mem' := by
          intro c a ha
          show algebraMap (𝓞 F) (𝓞 E) (c • a) • y ∈ N
          rw [smul_eq_mul, map_mul, mul_smul]
          exact N.smul_mem _ ha }
    have hJ : J = ⊤ := by
      by_contra hne
      obtain ⟨Mx, hM, hJM⟩ := Ideal.exists_le_maximal J hne
      have hM0 : Mx ≠ ⊥ := by
        first
      | exact Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField (K := F))
      | exact Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField F)
      | exact Ideal.IsMaximal.ne_bot_of_isIntegral_int hM
      let w : HeightOneSpectrum (𝓞 F) := ⟨Mx, hM.isPrime, hM0⟩
      by_cases hw : w ∈ T
      · obtain ⟨s, hs, hsy⟩ : ∃ s ∈ complF E w, s • y ∈ N := hloc' w hw
        obtain ⟨r, hr, rfl⟩ := asm_of_mem_complF hs
        exact hr (hJM (show r ∈ J from hsy))
      · have hyw : y ∈ locF w (stdLat E n) := by
          rw [hMem F E n w]
          intro i
          have hh := mul_mem ((hI F E).1 (fun u => u = w)) (hout' i)
          rw [← mul_assoc, (hI F E).2.1] at hh
          have e : (fun u : HeightOneSpectrum (𝓞 F) => u = w ∧ u ∉ T) = (fun u => u = w) := by
            funext u
            apply propext
            constructor
            · exact fun h => h.1
            · intro h
              refine ⟨h, ?_⟩
              rw [h]
              exact hw
          rw [e] at hh
          exact hh
        obtain ⟨s, hs, hsy⟩ : ∃ s ∈ complF E w, s • y ∈ stdLat E n := hyw
        obtain ⟨r, hr, rfl⟩ := asm_of_mem_complF hs
        have hDw : D ∉ w.asIdeal := fun h => hw ((memT w).2 h)
        have hmem : D * r ∈ J := by
          show algebraMap (𝓞 F) (𝓞 E) (D * r) • y ∈ N
          rw [map_mul, mul_smul]
          exact hD2 _ hsy
        exact (w.isPrime.mem_or_mem (hJM hmem)).elim hDw hr
    have h1 : (1 : 𝓞 F) ∈ J := hJ ▸ Submodule.mem_top
    have h1' : algebraMap (𝓞 F) (𝓞 E) 1 • y ∈ N := h1
    rwa [map_one, one_smul] at h1'
  · intro hy i
    rw [split_lemma_8 hI T]
    refine ⟨fun v hv => ?_, ?_⟩
    · exact (hTv v hv).2 (⟨1, (complF E v).one_mem, by rwa [one_smul]⟩ : ∃ s ∈ complF E v, s • y ∈ N) i
    · rw [hout i, hPT]
      apply hCof F E D hD
      have hh := asm_iota_std (F := F) (hD1 y hy) i
      rw [asm_smul_apply, map_mul, ← asm_iota_OF] at hh
      exact hh

private theorem isom_lemma_3 {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} (γ : GL (Fin n) E) (hγ : γ ∈ URat hc n) :
    Formalism.UG.glEquiv γ ∈ Formalism.HermitianLatticesTheory.isom (hStd E n) := by
  have h : Formalism.UG.cT (hc.sig : E →+* E) (γ : Matrix (Fin n) (Fin n) E) * 1 * (γ : Matrix (Fin n) (Fin n) E) = 1 := hγ
  rw [Matrix.mul_one] at h
  have hU : (γ : Matrix (Fin n) (Fin n) E)ᴴ * (γ : Matrix (Fin n) (Fin n) E) = 1 := h
  intro a b
  simp only [hStd, LinearMap.mk₂'ₛₗ_apply, glEquiv_apply_lemma]
  change star ((γ : Matrix (Fin n) (Fin n) E) *ᵥ a) ⬝ᵥ ((γ : Matrix (Fin n) (Fin n) E) *ᵥ b) = star a ⬝ᵥ b
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hU, Matrix.vecMul_one]

private theorem pt_loc_lemma_4 {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hMem : MemLocFStd) (hDen : IdemDenom) (hI : IdemCalc) {n : ℕ}
    (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (γ : GL (Fin n) E) (v : HeightOneSpectrum (𝓞 F))
    (h1 : Formalism.L2.GenusGluing.Gen.IntAt v (((Formalism.UG.bc (iA F E) γ)⁻¹ * x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)))
    (h2 : Formalism.L2.GenusGluing.Gen.IntAt v ((x⁻¹ * Formalism.UG.bc (iA F E) γ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) :
    Formalism.HermitianLatticesTheory.gmap (Formalism.UG.glEquiv γ) (locF v (stdLat E n)) = locF v (Formalism.UG.CS.globLat x (stdLat E n)) := by
  have K1 : ∀ z : Sp E n, (((Formalism.UG.bc (iA F E) γ)⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ (fun j => iA F E (z j)) =
      fun i => iA F E (((((γ⁻¹ : GL (Fin n) E)) : Matrix (Fin n) (Fin n) E) *ᵥ z) i) := by
    intro z
    rw [← map_inv (Formalism.UG.bc (iA F E)) γ]
    exact asm_bc_mulVec γ⁻¹ z
  ext y
  rw [asm_mem_gmap]
  constructor
  · intro hy
    have hy' := (hMem F E n v _).1 hy
    have hu : ∀ i, eAt E v * (((x⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ (fun j => iA F E (y j))) i ∈ Formalism.L2.Herm.intAf F E := by
      intro i
      have e : ((x⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ (fun j => iA F E (y j)) =
          ((x⁻¹ * Formalism.UG.bc (iA F E) γ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ
            (fun j => iA F E (((((γ⁻¹ : GL (Fin n) E)) : Matrix (Fin n) (Fin n) E) *ᵥ y) j)) := by
        rw [← K1 y, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel_right]
      rw [e]
      exact asm_mulVec_int hI (fun w => w = v) _ _ h2 hy' i
    choose r hr hru using fun i => hDen F E v _ (hu i)
    have hR : (∏ i, r i) ∈ v.asIdeal.primeCompl := prod_mem fun i _ => hr i
    show ∃ s ∈ complF E v, s • y ∈ Formalism.UG.CS.globLat x (stdLat E n)
    refine ⟨algebraMap (𝓞 F) (𝓞 E) (∏ i, r i), asm_mem_complF v _ hR, ?_⟩
    rw [glob_lemma_2]
    intro i
    have es : (fun j => iA F E ((algebraMap (𝓞 F) (𝓞 E) (∏ i, r i) • y) j)) =
        iA F E (algebraMap (𝓞 F) E (∏ i, r i)) • (fun j => iA F E (y j)) := by
      funext j
      rw [asm_smul_apply, map_mul, asm_iota_OF]
      rfl
    rw [es, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, map_prod, map_prod,
      ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), mul_right_comm]
    exact mul_mem (hru i) (prod_mem fun j _ => asm_iota_OF_mem (r j))
  · intro hy
    obtain ⟨s, hs, hsy⟩ : ∃ s ∈ complF E v, s • y ∈ Formalism.UG.CS.globLat x (stdLat E n) := hy
    rw [glob_lemma_2] at hsy
    have hw' : ∀ j, eP E (fun w => w = v) *
        (((x⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ (fun j => iA F E ((s • y) j))) j ∈ Formalism.L2.Herm.intAf F E :=
      fun j => mul_mem ((hI F E).1 _) (hsy j)
    have hz : s • ((((γ⁻¹ : GL (Fin n) E)) : Matrix (Fin n) (Fin n) E) *ᵥ y) ∈ locF v (stdLat E n) := by
      rw [hMem F E n v]
      intro i
      have e : (fun j => iA F E ((s • ((((γ⁻¹ : GL (Fin n) E)) : Matrix (Fin n) (Fin n) E) *ᵥ y)) j)) =
          (((Formalism.UG.bc (iA F E) γ)⁻¹ * x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ
            (((x⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ (fun j => iA F E ((s • y) j))) := by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel_right, K1, Matrix.mulVec_smul]
      have hh := asm_mulVec_int hI (fun w => w = v) _ _ h1 hw' i
      rw [← e] at hh
      exact hh
    obtain ⟨t, ht, htz⟩ : ∃ t ∈ complF E v, t • (s • ((((γ⁻¹ : GL (Fin n) E)) : Matrix (Fin n) (Fin n) E) *ᵥ y)) ∈ stdLat E n := hz
    exact (⟨t * s, (complF E v).mul_mem ht hs, by rw [mul_smul]; exact htz⟩ :
      ∃ t ∈ complF E v, t • ((((γ⁻¹ : GL (Fin n) E)) : Matrix (Fin n) (Fin n) E) *ᵥ y) ∈ stdLat E n)

theorem pointToGenus_of (hLoc : LocEq) (hMem : MemLocFStd) (hDen : IdemDenom) (hI : IdemCalc) : PointToGenus := by
  intro F E _ _ _ _ _ _ hc n hW x hx p hp
  have hne : p ≠ ⊥ := by
    first
      | exact Ring.ne_bot_of_isMaximal_of_not_isField hp (NumberField.RingOfIntegers.not_isField (K := E))
      | exact Ring.ne_bot_of_isMaximal_of_not_isField hp (NumberField.RingOfIntegers.not_isField E)
      | exact Ideal.IsMaximal.ne_bot_of_isIntegral_int hp
  obtain ⟨γ, hγ, h1, h2⟩ := hW x hx (Formalism.L2.DIV.underPl F ⟨p, hp.isPrime, hne⟩)
  refine ⟨Formalism.UG.glEquiv γ, isom_lemma_3 hc γ hγ, ?_⟩
  have e1 := hLoc F E hc n ⟨p, hp.isPrime, hne⟩ (stdLat E n)
  have e2 := hLoc F E hc n ⟨p, hp.isPrime, hne⟩ (Formalism.UG.CS.globLat x (stdLat E n))
  dsimp only at e1 e2
  rw [e1, e2]
  exact pt_loc_lemma_4 hMem hDen hI x γ _ h1 h2

end Formalism.L2.GenusGluing.Gen
end
end

section -- merged from Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GenusApproximationProofs.CommensurableHolds
noncomputable section

namespace Formalism.L2.GenusGluing.Gen

open NumberField IsDedekindDomain Formalism.L2.Col Formalism.L2.DIV
open scoped TensorProduct

section LocEqSec

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

omit [NumberField F] [NumberField E] [StarRing E] in
theorem loc_coe_algebraMap (r : 𝓞 F) :
    ((algebraMap (𝓞 F) (𝓞 E) r : 𝓞 E) : E) = algebraMap F E (r : F) := rfl

theorem loc_hcompl_prop (PP : Pl E) (s : 𝓞 E) (hs : s ∈ Formalism.HermitianLatticesTheory.hcompl (K := E) PP.asIdeal) :
    s ∉ PP.asIdeal ∧ starO s ∉ PP.asIdeal := by
  induction hs using Submonoid.closure_induction with
  | mem x hx =>
    exact ⟨hx.1, hx.2 (starO x) (starO_coe x)⟩
  | one =>
    have h1 : starO (1 : 𝓞 E) = 1 := map_one (starOHom (E := E))
    rw [h1]
    exact ⟨PP.isPrime.ne_top ∘ (Ideal.eq_top_of_isUnit_mem _ · isUnit_one),
      PP.isPrime.ne_top ∘ (Ideal.eq_top_of_isUnit_mem _ · isUnit_one)⟩
  | mul x y _ _ hx hy =>
    have hm : starO (x * y) = starO x * starO y := map_mul (starOHom (E := E)) x y
    rw [hm]
    exact ⟨fun h => (PP.isPrime.mem_or_mem h).elim hx.1 hy.1,
      fun h => (PP.isPrime.mem_or_mem h).elim hx.2 hy.2⟩

end LocEqSec

theorem localEquality_holds : LocEq := by
  intro F E _ _ _ _ _ _ hc n PP L
  apply le_antisymm
  · intro x hx
    obtain ⟨s, hs, hsx⟩ := Formalism.HermitianLatticesTheory.locBasic_mem_locS.mp hx
    obtain ⟨hs1, hs2⟩ := loc_hcompl_prop PP s hs
    set m : 𝓞 E := s * starO s with hm
    have hfix : star ((m : 𝓞 E) : E) = (m : E) := by
      show star ((s : E) * ((starO s : 𝓞 E) : E)) = (s : E) * ((starO s : 𝓞 E) : E)
      rw [starO_coe, star_mul', star_star, mul_comm]
    obtain ⟨a, ha⟩ := (hc.fixed (m : E)).1 hfix
    have hint : IsIntegral ℤ a := by
      have h2 : IsIntegral ℤ (algebraMap F E a) := by rw [ha]; exact m.2
      exact (isIntegral_algebraMap_iff ).1 h2
    set r : 𝓞 F := ⟨a, hint⟩ with hr
    have hrm : algebraMap (𝓞 F) (𝓞 E) r = m := by
      apply RingOfIntegers.ext
      rw [loc_coe_algebraMap]
      exact ha
    have hmp : m ∉ PP.asIdeal := fun h => (PP.isPrime.mem_or_mem h).elim hs1 hs2
    refine Formalism.HermitianLatticesTheory.locBasic_mem_locS.mpr ⟨m, ⟨r, ?_, hrm⟩, ?_⟩
    · show r ∉ (underPl F PP).asIdeal
      rw [underPl_asIdeal, Ideal.mem_comap, hrm]
      exact hmp
    · rw [hm, mul_comm, mul_smul]
      exact L.smul_mem _ hsx
  · apply Formalism.HermitianLatticesTheory.locBasic_locS_le_of_le
    rintro _ ⟨r, hr, rfl⟩
    apply Submonoid.subset_closure
    have hr' : algebraMap (𝓞 F) (𝓞 E) r ∉ PP.asIdeal := by
      intro h
      apply hr
      show r ∈ (underPl F PP).asIdeal
      rw [underPl_asIdeal, Ideal.mem_comap]
      exact h
    refine ⟨hr', fun t ht htp => hr' ?_⟩
    have hfix : star (algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) r)) =
        algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) r) :=
      (hc.fixed _).2 ⟨(r : F), rfl⟩
    rw [hfix] at ht
    have : t = algebraMap (𝓞 F) (𝓞 E) r := FaithfulSMul.algebraMap_injective (𝓞 E) E ht
    rw [← this]
    exact htp

section CommensSec

variable {E : Type} [Field E] [NumberField E]

theorem commens_denoms (s : Finset E) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ x ∈ s, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = (d : E) * x := by
  obtain ⟨y, hy, hint⟩ := exists_integral_multiples ℤ ℚ (L := E) s
  refine ⟨y, hy, fun x hx => ⟨⟨_, hint x hx⟩, ?_⟩⟩
  show (y • x : E) = _
  rw [zsmul_eq_mul]

end CommensSec

theorem commensurable_holds :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
      (n : ℕ) (N : Submodule (𝓞 E) (Sp E n)), Submodule.IsFullLattice E N →
      ∃ D : 𝓞 F, D ≠ 0 ∧ (∀ y ∈ N, algebraMap (𝓞 F) (𝓞 E) D • y ∈ stdLat E n) ∧
        (∀ y ∈ stdLat E n, algebraMap (𝓞 F) (𝓞 E) D • y ∈ N) := by
  intro F E _ _ _ _ _ n N hN
  classical
  let _ : Submodule.IsFullLattice E N := hN
  obtain ⟨s, hs⟩ := Submodule.IsLattice.fg E N
  obtain ⟨d1, hd1, h1⟩ := commens_denoms (s.biUnion fun x => Finset.univ.image x)
  have hA : ∀ y ∈ N, ((d1 : 𝓞 E)) • y ∈ stdLat E n := by
    have hle : N ≤ (stdLat E n).comap (((d1 : 𝓞 E)) • LinearMap.id) := by
      rw [← hs, Submodule.span_le]
      intro x hx
      simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply]
      rw [stdLat, Submodule.mem_pi]
      intro i _
      rw [Submodule.mem_one]
      obtain ⟨o, ho⟩ := h1 (x i) (Finset.mem_biUnion.2 ⟨x, hx, Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩⟩)
      refine ⟨o, ?_⟩
      rw [ho, Pi.smul_apply, Algebra.smul_def, map_intCast]
    intro y hy
    have := hle hy
    simpa only [Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply] using this
  have hB : ∀ i : Fin n, Pi.single i (1 : E) ∈ Submodule.span E (N : Set (Sp E n)) := by
    intro i
    rw [Submodule.IsFullLattice.span_eq_top (A := E) (M := N)]
    exact Submodule.mem_top
  choose f t ht _ hsum using fun i => Submodule.mem_span_iff_exists_finset_subset.1 (hB i)
  obtain ⟨d2, hd2, h2⟩ := commens_denoms (Finset.univ.biUnion fun i => (t i).image (f i))
  have hsingle : ∀ i : Fin n, ((d2 : 𝓞 E)) • Pi.single i (1 : E) ∈ N := by
    intro i
    rw [← hsum i, Finset.smul_sum]
    apply Submodule.sum_mem
    intro a ha
    obtain ⟨o, ho⟩ := h2 (f i a) (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, Finset.mem_image.2 ⟨a, ha, rfl⟩⟩)
    have e : ((d2 : 𝓞 E)) • (f i a • a) = o • a := by
      rw [Int.cast_smul_eq_zsmul, ← Int.cast_smul_eq_zsmul E, smul_smul, ← ho, algebraMap_smul]
    rw [e]
    exact N.smul_mem o (ht i ha)
  have hC : ∀ y ∈ stdLat E n, ((d2 : 𝓞 E)) • y ∈ N := by
    intro y hy
    rw [stdLat, Submodule.mem_pi] at hy
    choose o ho using fun i => Submodule.mem_one.1 (hy i (Set.mem_univ i))
    have ey : y = ∑ i, o i • Pi.single i (1 : E) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply, ← ho j, Algebra.smul_def]
    rw [ey, Finset.smul_sum]
    apply Submodule.sum_mem
    intro i _
    rw [smul_comm]
    exact N.smul_mem (o i) (hsingle i)
  refine ⟨((d1 * d2 : ℤ) : 𝓞 F), ?_, ?_, ?_⟩
  · exact_mod_cast mul_ne_zero hd1 hd2
  · intro y hy
    rw [map_intCast, Int.cast_mul, mul_comm, mul_smul]
    exact (stdLat E n).smul_mem _ (hA y hy)
  · intro y hy
    rw [map_intCast, Int.cast_mul, mul_smul]
    exact N.smul_mem _ (hC y hy)
end Formalism.L2.GenusGluing.Gen
end
end

section -- merged from Formalism.LocalToGlobal.GenusGluing.GenusApproximation.LocalAdelicEquivHolds
noncomputable section

namespace Formalism.L2.GenusGluing.Gen

open NumberField IsDedekindDomain Matrix Formalism.L2.Col
open scoped TensorProduct

theorem glueExists_holds : GlueExists := glueExists_of idempotentCalculation_holds

theorem genusToPoint_holds : GenusToPoint :=
  genusToPoint_of localEquality_holds memLocalizedStd_holds idempotentCofinite_holds idempotentCalculation_holds glueExists_holds commensurable_holds

theorem pointToGenus_holds : PointToGenus :=
  pointToGenus_of localEquality_holds memLocalizedStd_holds idempotentDenominator_holds idempotentCalculation_holds

theorem localToAdelic_holds : LocToAd := locToAd_of genusToPoint_holds

theorem adelicToLocal_holds : AdToLoc := adToLoc_of pointToGenus_holds

theorem localAdelicEquiv_holds : Bridge := bridge_of localToAdelic_holds adelicToLocal_holds

end Formalism.L2.GenusGluing.Gen
end
end

noncomputable section

namespace Formalism.L2.GenusGluing.Gen

open NumberField IsDedekindDomain Matrix Formalism.L2.Col
open scoped TensorProduct

theorem shiftDiagonal_holds : ShiftDiag := shiftDiag_of shiftOne_holds

theorem cayleyApproximation_holds : CayleyStep := cayleyStep_of evaluationNeZero_holds approximationAdelic_holds unitNearOne_holds

theorem weakApproximationAll_holds : WeakApproxAll := weakApproxAll_of shiftDiagonal_holds cayleyApproximation_holds integralAtInverse_holds

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem weakApproximation_unitary (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) : WeakApproxU hc n := weakApproximationAll_holds F E hc n

theorem unimodGenus_iff (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) : UnimodGenusLoc E n ↔ UnimodGenus hc n :=
  localAdelicEquiv_holds F E hc n (weakApproximation_unitary hc n)

end Formalism.L2.GenusGluing.Gen
end
end

noncomputable section

namespace Formalism.L2.Col

open NumberField

theorem unimodGenusLocAll_holds : UnimodGenusLocAll := unimodular_genus_unique

theorem unimodGenusLoc_holds (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) : UnimodGenusLoc E n :=
  unimodGenusLocAll_holds E n

theorem unimodGenus_holds {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] : UnimodGenus hc n :=
  (Formalism.L2.GenusGluing.Gen.unimodGenus_iff hc n).1 (unimodGenusLoc_holds E n)

end Formalism.L2.Col
