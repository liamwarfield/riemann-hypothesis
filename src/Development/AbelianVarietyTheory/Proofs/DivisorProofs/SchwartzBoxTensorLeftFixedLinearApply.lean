module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumLogGaussAbsLeFractionalIdealIndex
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInertPlaceTransversalOfLocalCore

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentCornerIsUnitInertPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfSkewUnipotentMemDoubledLatticeStabilizer
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfSkewUnipotentMemDoubledLatticeStabilizer
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.DblVacUnip

open Matrix GlobalTheory.DblVac GlobalTheory.BigCell GlobalTheory.DblVacFactor

section Abstract

variable {R : Type} [CommRing R] {β : Type} [Fintype β] [DecidableEq β] [Invertible (2 : R)]

theorem mem_unitary_of_skew (f : R →+* R) (J : Matrix β β R) (K : Matrix (β ⊕ β) (β ⊕ β) R)
    (Δ N : Matrix (β ⊕ β) β R) (Δt Nt : Matrix β (β ⊕ β) R) (x : Matrix β β R)
    (hΔT : Δᵀ = Δt) (hNT : Nᵀ = Nt) (hΔf : Δ.map f = Δ) (hNtf : Nt.map f = Nt)
    (e3 : Δt * K = J * Nt) (e4 : K * Δ = N * J) (e5 : Δt * K * Δ = 0)
    (hZ : xᵀ * J + J * x.map f = 0) :
    (1 + ⅟(2 : R) • (Δ * x * Nt))ᵀ * K * (1 + ⅟(2 : R) • (Δ * x * Nt)).map f = K := by
  have hNtT : Ntᵀ = N := by rw [← hNT, transpose_transpose]
  have hMT : (Δ * x * Nt)ᵀ = N * (xᵀ * Δt) := by simp only [transpose_mul, hNtT, hΔT, Matrix.mul_assoc]
  have hMf : (Δ * x * Nt).map f = Δ * (x.map f * Nt) := by simp only [Matrix.map_mul, hΔf, hNtf, Matrix.mul_assoc]
  have hPT : (1 + ⅟(2 : R) • (Δ * x * Nt))ᵀ = 1 + ⅟(2 : R) • (N * (xᵀ * Δt)) := by
    rw [transpose_add, transpose_one, transpose_smul, hMT]
  have hPf : (1 + ⅟(2 : R) • (Δ * x * Nt)).map f = 1 + ⅟(2 : R) • (Δ * (x.map f * Nt)) := by
    rw [Matrix.map_add f (map_add f), Matrix.map_one f (map_zero f) (map_one f), Matrix.map_smul' _ _ _ (map_mul f),
      map_half, hMf]
  have A1 : N * (xᵀ * Δt) * K * (Δ * (x.map f * Nt)) = 0 := by
    simp only [Matrix.mul_assoc]
    rw [show Δt * (K * (Δ * (x.map f * Nt))) = 0 by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, e5, Matrix.zero_mul]]
    simp
  have A2 : N * (xᵀ * Δt) * K + K * (Δ * (x.map f * Nt)) = 0 := by
    calc _ = N * ((xᵀ * J + J * x.map f) * Nt) := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, e3, ← Matrix.mul_assoc K Δ, e4]
          simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
      _ = 0 := by rw [hZ]; simp
  have expand : ∀ U V : Matrix (β ⊕ β) (β ⊕ β) R, (1 + ⅟(2 : R) • U) * K * (1 + ⅟(2 : R) • V) =
      K + ⅟(2 : R) • (U * K + K * V) + (⅟(2 : R) * ⅟(2 : R)) • (U * K * V) := by
    intro U V
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
      smul_add, smul_smul]
    abel
  rw [hPT, hPf, expand, A2, A1]
  simp

end Abstract

theorem unip_mem : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ)
    (W : Spc F E d) (v : Pl (F := F)), (2 : 𝓞 F) ∉ v.asIdeal → ∀ Z : Matrix (Fin d) (Fin d) (AE F E), At (evFin F v) Z →
    (∀ z ∈ GlobalTheory.InertSph.latAt W v, Z *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
    Zᵀ * incM F W.J + incM F W.J * Z.map (cA σ) = 0 →
    ∃ u ∈ GlobalTheory.DblVac.KD σ W v, u ∈ GlobalTheory.DblVac.PDiag σ W ∧
      GlobalTheory.DblVac.matD u = 1 + (⅟(2 : AF F)) • ((diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) * Z * (GlobalTheory.DblVac.antiCols (F := F) (E := E) d)ᵀ) := by
  intro F E _ _ _ _ _ σ d W v h2 Z hZat hZlat hZskew
  letI : Invertible (2 : AE F E) := invTwoE
  set f : AE F E →+* AE F E := ((cA σ : AE F E →ₐ[AF F] AE F E) : AE F E →+* AE F E) with hf
  set J : Matrix (Fin d) (Fin d) (AE F E) := incM F W.J with hJ
  have h1 : (1 : Matrix (Fin d) (Fin d) (AE F E)).map f = 1 := Matrix.map_one f (map_zero f) (map_one f)
  have hm1 : (-1 : Matrix (Fin d) (Fin d) (AE F E)).map f = -1 := by rw [Matrix.map_neg _ (map_neg f), h1]
  have hΔT : (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E))ᵀ =
      fromCols 1 1 := by
    rw [transpose_fromRows, transpose_one]
  have hNT : (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E))ᵀ =
      fromCols 1 (-1) := by
    rw [transpose_fromRows, transpose_one, transpose_neg, transpose_one]
  have hΔf : (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)).map f =
      fromRows 1 1 := by rw [fromRows_map, h1]
  have hNtf : (fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)).map f =
      fromCols 1 (-1) := by rw [fromCols_map, h1, hm1]
  have hskew : Zᵀ * J + J * Z.map f = 0 := hZskew
  set M : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E) :=
    (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) * Z *
    (fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)) with hMdef
  have hinv := mul_inv_eq (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E))
    (fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)) e1 Z
  have hmem := mem_unitary_of_skew f J (dbl J) _ _ _ _ Z hΔT hNT hΔf hNtf (e3 J) (e4 J) (e5 J) hskew
  let P : GL (Fin d ⊕ Fin d) (AE F E) := ⟨1 + ⅟(2 : AE F E) • M, 1 - ⅟(2 : AE F E) • M, hinv.1, hinv.2⟩
  let p : UD σ W := ⟨P, hmem⟩
  have hMu : ∀ u : AF F, evFin F v u = 0 → u • M = 0 := by
    intro u hu
    have hu' : u • Z = 0 := hZat u hu
    calc u • M = (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) * (u • Z) *
        (fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)) := by
          rw [hMdef]; simp only [Matrix.mul_smul, Matrix.smul_mul]
      _ = 0 := by rw [hu']; simp
  have hpK : p ∈ KD σ W v := by
    refine ⟨fun u hu => ?_, fun z hz => ⟨?_, ?_⟩⟩
    · show u • ((1 + ⅟(2 : AE F E) • M) - 1) = 0
      rw [add_sub_cancel_left, smul_comm, hMu u hu, smul_zero]
    · show (1 + ⅟(2 : AE F E) • M) *ᵥ z ∈ latD W v
      rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hMdef]
      simp only [← Matrix.mulVec_mulVec]
      exact latD_add hz (latD_half h2 (latD_diag (hZlat _ (lat_antiT hz))))
    · show (1 - ⅟(2 : AE F E) • M) *ᵥ z ∈ latD W v
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hMdef]
      simp only [← Matrix.mulVec_mulVec]
      exact latD_sub hz (latD_half h2 (latD_diag (hZlat _ (lat_antiT hz))))
  refine ⟨p, hpK, ⟨1, ?_⟩, ?_⟩
  · have key : ((1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) + ⅟(2 : AE F E) • M) *
        (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) =
        (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) := by
      rw [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, hMdef, Matrix.mul_assoc _ _
        (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)), e1,
        Matrix.mul_zero, smul_zero, add_zero]
    show ((1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) + ⅟(2 : AE F E) • M) *
        (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) =
      (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) *
        ((1 : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E))
    rw [Units.val_one, Matrix.mul_one]
    exact key
  · have hNt : (antiCols (F := F) (E := E) d)ᵀ = fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) := by
      rw [antiCols, transpose_fromRows, transpose_one, transpose_neg, transpose_one]
    show (1 + ⅟(2 : AE F E) • M) = _
    rw [hNt, invOf_two_eq, algebraMap_smul]
    rfl

end GlobalTheory.DblVacUnip
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfSkewUnipotentMemDoubledLatticeStabilizerStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.halfSkewUnipotent_mem_doubledLatticeStabilizer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ)
    (W : Spc F E d) (v : Pl (F := F)), (2 : 𝓞 F) ∉ v.asIdeal → ∀ Z : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) Z →
    (∀ z ∈ GlobalTheory.InertSph.latAt W v, Z *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
    Zᵀ * incM F W.J + incM F W.J * Z.map (cA σ) = 0 →
    ∃ u ∈ GlobalTheory.DblVac.KD σ W v, u ∈ GlobalTheory.DblVac.PDiag σ W ∧
      GlobalTheory.DblVac.matD u = 1 + (⅟(2 : AF F)) • ((diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * Z * (GlobalTheory.DblVac.antiCols (F := F) (E := E) d)ᵀ) := by
  first | exact @GlobalTheory.DblVacUnip.unip_mem | exact GlobalTheory.DblVacUnip.unip_mem | (intros; apply GlobalTheory.DblVacUnip.unip_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicGraphUnitaryIsUnitLowerBlock
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicGraphDetLowerRowNeZeroField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSkewHermitianMulAddDetNeZeroOfPair
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianPerturbIdempotentDetNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianPerturbIdempotentDetNeZero
open scoped Matrix

namespace GlobalTheory

theorem skewHermitian_perturb_idempotent_det_ne_zero :
    ∀ (k : Type) [Field k] (σ : k →+* k), (∀ x, σ (σ x) = x) → ∀ ε : k, ε ≠ 0 → σ ε = -ε →
    ∀ (n : ℕ) (E D : Matrix (Fin n) (Fin n) k), E * E = E → (E.map σ)ᵀ = E → E * (D.map σ)ᵀ + D * E = 0 →
    (∀ a : Fin n → k, a ᵥ* E = 0 → a ᵥ* D = 0 → a = 0) →
      ∃ V : Matrix (Fin n) (Fin n) k, (V.map σ)ᵀ = -V ∧ (E * V + D).det ≠ 0 := by
  intro k _ σ hσ ε hε hσε n E D hEE hEh hED hrank
  have h1 : E * (D.map σ)ᵀ = -(D * E) := eq_neg_of_add_eq_zero_left hED
  have h2 : E * (D.map σ)ᵀ = -(E * D * E) := by
    calc E * (D.map σ)ᵀ = E * (E * (D.map σ)ᵀ) := by rw [← Matrix.mul_assoc, hEE]
      _ = E * (-(D * E)) := by rw [h1]
      _ = -(E * D * E) := by rw [Matrix.mul_neg, Matrix.mul_assoc]
  have hDE : D * E = E * D * E := by
    have := h1.symm.trans h2
    exact neg_inj.mp this
  have h3 : E * (D.map σ)ᵀ * E = -(E * D * E) := by
    rw [h2, Matrix.neg_mul, Matrix.mul_assoc (E * D) E E, hEE]
  have hV : E * (ε • (1 : Matrix (Fin n) (Fin n) k) - D) * E = ε • E - E * D * E := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hEE]
  refine ⟨E * (ε • 1 - D) * E, ?_, ?_⟩
  · rw [hV]
    have hm : ((ε • E - E * D * E).map σ)ᵀ = (σ ε) • (E.map σ)ᵀ - (E.map σ)ᵀ * (D.map σ)ᵀ * (E.map σ)ᵀ := by
      ext i j
      have hs : ((ε • E).map σ)ᵀ = σ ε • (E.map σ)ᵀ := by
        ext i j
        simp
      rw [Matrix.map_sub _ (map_sub σ), Matrix.map_mul, Matrix.map_mul, Matrix.transpose_sub, Matrix.transpose_mul,
        Matrix.transpose_mul, ← Matrix.mul_assoc, hs]
    rw [hm, hEh, h3, hσε, neg_smul, sub_neg_eq_add, neg_sub]
    abel
  · have hM : E * (E * (ε • 1 - D) * E) + D = ε • E - E * D * E + D := by
      rw [hV, Matrix.mul_sub, Matrix.mul_smul, hEE, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hEE]
    rw [hM]
    have hME : (ε • E - E * D * E + D) * E = ε • E := by
      rw [Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, hEE, Matrix.mul_assoc (E * D) E E, hEE, hDE]
      abel
    intro hdet
    obtain ⟨a, ha0, ha⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
    have haE : a ᵥ* E = 0 := by
      have : a ᵥ* ((ε • E - E * D * E + D) * E) = 0 := by rw [← Matrix.vecMul_vecMul, ha, Matrix.zero_vecMul]
      rw [hME, Matrix.vecMul_smul] at this
      exact (smul_eq_zero.mp this).resolve_left hε
    have haD : a ᵥ* D = 0 := by
      have hx : a ᵥ* (E * D * E) = 0 := by
        rw [Matrix.mul_assoc, ← Matrix.vecMul_vecMul, haE, Matrix.zero_vecMul]
      rw [Matrix.vecMul_add, Matrix.vecMul_sub, Matrix.vecMul_smul, haE, hx] at ha
      simpa using ha
    exact ha0 (hrank a haE haD)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianPerturbIdempotentDetNeZeroStatement
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_skewHermitian_det_mul_add_ne_zero_of_idempotent : ∀ (k : Type) [Field k] (σ : k →+* k), (∀ x, σ (σ x) = x) → ∀ ε : k, ε ≠ 0 → σ ε = -ε →
    ∀ (n : ℕ) (E D : Matrix (Fin n) (Fin n) k), E * E = E → (E.map σ)ᵀ = E → E * (D.map σ)ᵀ + D * E = 0 →
    (∀ a : Fin n → k, a ᵥ* E = 0 → a ᵥ* D = 0 → a = 0) →
      ∃ V : Matrix (Fin n) (Fin n) k, (V.map σ)ᵀ = -V ∧ (E * V + D).det ≠ 0 := by
  first | exact @GlobalTheory.skewHermitian_perturb_idempotent_det_ne_zero | exact GlobalTheory.skewHermitian_perturb_idempotent_det_ne_zero | (intros; apply GlobalTheory.skewHermitian_perturb_idempotent_det_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRankNormalFormMatrixField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRankNormalFormMatrixField
open scoped Matrix

namespace GlobalTheory

theorem rank_normal_form_field : ∀ (k : Type) [Field k] (n : ℕ) (C : Matrix (Fin n) (Fin n) k),
    ∃ (U P : Matrix (Fin n) (Fin n) k) (e : Fin n → k), U.det ≠ 0 ∧ P.det ≠ 0 ∧ (∀ i, e i = 0 ∨ e i = 1) ∧
      U * C * P = Matrix.diagonal e := by
  intro k _ n C
  classical
  obtain ⟨L, L', d, hd⟩ := Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal C
  refine ⟨Matrix.diagonal (fun i => if d i = 0 then 1 else (d i)⁻¹) * (L.map Matrix.TransvectionStruct.toMatrix).prod,
    (L'.map Matrix.TransvectionStruct.toMatrix).prod, fun i => if d i = 0 then 0 else 1, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.det_mul, Matrix.TransvectionStruct.det_toMatrix_prod, mul_one, Matrix.det_diagonal]
    refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
    by_cases h : d i = 0 <;> simp [h]
  · rw [Matrix.TransvectionStruct.det_toMatrix_prod]; exact one_ne_zero
  · intro i; by_cases h : d i = 0 <;> simp [h]
  · rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ C, hd, Matrix.diagonal_mul_diagonal]
    congr 1; funext i; by_cases h : d i = 0 <;> simp [h]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRankNormalFormMatrixFieldStatement
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rank_normal_form_matrix_field : ∀ (k : Type) [Field k] (n : ℕ) (C : Matrix (Fin n) (Fin n) k),
    ∃ (U P : Matrix (Fin n) (Fin n) k) (e : Fin n → k), U.det ≠ 0 ∧ P.det ≠ 0 ∧ (∀ i, e i = 0 ∨ e i = 1) ∧
      U * C * P = Matrix.diagonal e := by
  first | exact @GlobalTheory.rank_normal_form_field | exact GlobalTheory.rank_normal_form_field | (intros; apply GlobalTheory.rank_normal_form_field <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSkewHermitianMulAddDetNeZeroOfPair
open scoped Matrix

namespace GlobalTheory

theorem exists_skewHermitian_mul_add_det_ne_zero_of_pair :
    ∀ (k : Type) [Field k] (σ : k →+* k), (∀ x, σ (σ x) = x) → ∀ ε : k, ε ≠ 0 → σ ε = -ε →
    ∀ (n : ℕ) (C D : Matrix (Fin n) (Fin n) k), C * (D.map σ)ᵀ + D * (C.map σ)ᵀ = 0 →
    (∀ a : Fin n → k, a ᵥ* C = 0 → a ᵥ* D = 0 → a = 0) →
      ∃ V : Matrix (Fin n) (Fin n) k, (V.map σ)ᵀ = -V ∧ (C * V + D).det ≠ 0 := by
  intro k _ σ hσ ε hε hσε n C D hCD hrk
  obtain ⟨U, P, e, hU, hP, he, hE⟩ := GlobalTheory.T.exists_rank_normal_form_matrix_field k n C
  have hmul : ∀ A B : Matrix (Fin n) (Fin n) k,
      ((A * B).map σ)ᵀ = (B.map σ)ᵀ * (A.map σ)ᵀ := by
    intro A B
    rw [Matrix.map_mul, Matrix.transpose_mul]
  have hinv : ∀ A : Matrix (Fin n) (Fin n) k, (((A.map σ)ᵀ).map σ)ᵀ = A := by
    intro A
    ext i j
    simp [hσ]
  have hone : (((1 : Matrix (Fin n) (Fin n) k).map σ)ᵀ) = 1 := by
    rw [Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_one]
  have hPu : IsUnit P.det := isUnit_iff_ne_zero.mpr hP
  have hUu : IsUnit U.det := isUnit_iff_ne_zero.mpr hU
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hPu
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hPu
  have h3 : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv U hUu
  set E : Matrix (Fin n) (Fin n) k := Matrix.diagonal e with hEdef
  have hEE : E * E = E := by
    rw [hEdef, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rcases he i with h | h <;> simp [h]
  have hEs : (E.map σ)ᵀ = E := by
    rw [hEdef, Matrix.diagonal_map (map_zero σ), Matrix.diagonal_transpose]
    congr 1
    funext i
    rcases he i with h | h <;> simp [h]
  set Q : Matrix (Fin n) (Fin n) k := (P⁻¹.map σ)ᵀ with hQ
  set Ps : Matrix (Fin n) (Fin n) k := (P.map σ)ᵀ with hPs
  have hPQ : Ps * Q = 1 := by rw [hPs, hQ, ← hmul, h2, hone]
  have hQP : Q * Ps = 1 := by rw [hPs, hQ, ← hmul, h1, hone]
  have hQs : (Q.map σ)ᵀ = P⁻¹ := hinv _
  have hE' : E = Ps * ((C.map σ)ᵀ * (U.map σ)ᵀ) := by
    rw [← hEs, ← hE, hmul, hmul]
  have hA : E * ((U * D * Q).map σ)ᵀ = U * (C * (D.map σ)ᵀ) * (U.map σ)ᵀ := by
    rw [hmul, hmul, hQs, ← hE]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P, h1, Matrix.one_mul]
  have hB : U * D * Q * E = U * (D * (C.map σ)ᵀ) * (U.map σ)ᵀ := by
    rw [hE']
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Q, hQP, Matrix.one_mul]
  have hsum : E * ((U * D * Q).map σ)ᵀ + U * D * Q * E = 0 := by
    rw [hA, hB, ← Matrix.add_mul, ← Matrix.mul_add, hCD, Matrix.mul_zero, Matrix.zero_mul]
  have hrk' : ∀ a : Fin n → k, a ᵥ* E = 0 → a ᵥ* (U * D * Q) = 0 → a = 0 := by
    intro a ha hb
    have e1 : U * C = E * P⁻¹ := by
      rw [← hE, Matrix.mul_assoc, h1, Matrix.mul_one]
    have e2 : U * D = (U * D * Q) * Ps := by
      rw [Matrix.mul_assoc, hQP, Matrix.mul_one]
    have h0 : a ᵥ* U = 0 := by
      apply hrk
      · rw [Matrix.vecMul_vecMul, e1, ← Matrix.vecMul_vecMul, ha, Matrix.zero_vecMul]
      · rw [Matrix.vecMul_vecMul, e2, ← Matrix.vecMul_vecMul, hb, Matrix.zero_vecMul]
    have : a ᵥ* (U * U⁻¹) = 0 := by
      rw [← Matrix.vecMul_vecMul, h0, Matrix.zero_vecMul]
    rwa [h3, Matrix.vecMul_one] at this
  obtain ⟨V', hV', hdet⟩ := GlobalTheory.T.exists_skewHermitian_det_mul_add_ne_zero_of_idempotent k σ hσ ε hε hσε n E (U * D * Q) hEE hEs hsum hrk'
  refine ⟨P * V' * Ps, ?_, ?_⟩
  · have hPss : (Ps.map σ)ᵀ = P := hinv _
    rw [hmul, hmul, hV', hPss, ← hPs]
    simp [Matrix.mul_assoc]
  · intro h
    apply hdet
    have : E * V' + U * D * Q = U * (C * (P * V' * Ps) + D) * Q := by
      rw [← hE, Matrix.mul_add, Matrix.add_mul]
      simp only [Matrix.mul_assoc]
      rw [hPQ, Matrix.mul_one]
    rw [this, Matrix.det_mul, Matrix.det_mul, h, mul_zero, zero_mul]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSkewHermitianMulAddDetNeZeroOfPairStatement
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_skewHermitian_mul_add_det_ne_zero : ∀ (k : Type) [Field k] (σ : k →+* k), (∀ x, σ (σ x) = x) → ∀ ε : k, ε ≠ 0 → σ ε = -ε →
    ∀ (n : ℕ) (C D : Matrix (Fin n) (Fin n) k), C * (D.map σ)ᵀ + D * (C.map σ)ᵀ = 0 →
    (∀ a : Fin n → k, a ᵥ* C = 0 → a ᵥ* D = 0 → a = 0) →
      ∃ V : Matrix (Fin n) (Fin n) k, (V.map σ)ᵀ = -V ∧ (C * V + D).det ≠ 0 := by
  first | exact @GlobalTheory.exists_skewHermitian_mul_add_det_ne_zero_of_pair | exact GlobalTheory.exists_skewHermitian_mul_add_det_ne_zero_of_pair | (intros; apply GlobalTheory.exists_skewHermitian_mul_add_det_ne_zero_of_pair <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicGraphDetLowerRowNeZeroField
open scoped Matrix

namespace GlobalTheory

theorem exists_isotropic_graph_det_lowerRow_ne_zero_field :
    ∀ (k : Type) [Field k] (σ : k →+* k), (∀ x, σ (σ x) = x) → (∃ ε : k, ε ≠ 0 ∧ σ ε = -ε) →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) k), (∀ i j, σ (J j i) = J i j) → J.det ≠ 0 →
    ∀ g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k, g.det ≠ 0 →
      gᵀ * Matrix.fromBlocks 0 J J 0 * g.map σ = Matrix.fromBlocks 0 J J 0 →
      ∃ Z : Matrix (Fin n) (Fin n) k, Zᵀ * J + J * Z.map σ = 0 ∧
        (g.toBlocks₂₁ * Z + g.toBlocks₂₂).det ≠ 0 := by
  intro k _ σ hσ hε n J hJ hJd g hg hQ
  obtain ⟨ε, hε0, hε⟩ := hε
  have hmm : ∀ A : Matrix (Fin n) (Fin n) k, (A.map σ).map σ = A := by
    intro A; ext i j; simp [hσ]
  have hJu : IsUnit J.det := isUnit_iff_ne_zero.mpr hJd
  set K : Matrix (Fin n) (Fin n) k := J⁻¹ with hK
  have hJK : J * K = 1 := Matrix.mul_nonsing_inv J hJu
  have hKJ : K * J = 1 := Matrix.nonsing_inv_mul J hJu
  have hJh : (J.map σ)ᵀ = J := by ext i j; simp [hJ]
  have hKh : (K.map σ)ᵀ = K := by
    have h1 : (K.map σ)ᵀ * J = 1 := by
      conv_lhs => rw [← hJh]
      rw [← Matrix.transpose_mul, ← Matrix.map_mul, hJK]
      simp
    calc (K.map σ)ᵀ = (K.map σ)ᵀ * (J * K) := by rw [hJK, Matrix.mul_one]
      _ = K := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hKt : Kᵀ = K.map σ := by
    conv_lhs => rw [← hKh]
    simp
  have hQR : Matrix.fromBlocks 0 K K 0 * Matrix.fromBlocks (0 : Matrix (Fin n) (Fin n) k) J J 0
      = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k) := by
    rw [Matrix.fromBlocks_multiply]
    simp [hKJ]
  have hRQ : Matrix.fromBlocks 0 J J 0 * Matrix.fromBlocks (0 : Matrix (Fin n) (Fin n) k) K K 0
      = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k) := mul_eq_one_comm.mp hQR
  have h2 : (Matrix.fromBlocks 0 K K 0 * gᵀ * Matrix.fromBlocks 0 J J 0) * g.map σ = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᵀ, hQ, hQR]
  have h3 := mul_eq_one_comm.mp h2
  have h4 : g.map σ * Matrix.fromBlocks 0 K K 0 * gᵀ = Matrix.fromBlocks 0 K K 0 := by
    calc g.map σ * Matrix.fromBlocks 0 K K 0 * gᵀ
        = g.map σ * Matrix.fromBlocks 0 K K 0 * gᵀ *
          (Matrix.fromBlocks 0 J J 0 * Matrix.fromBlocks 0 K K 0) := by rw [hRQ, Matrix.mul_one]
      _ = (g.map σ * (Matrix.fromBlocks 0 K K 0 * gᵀ * Matrix.fromBlocks 0 J J 0)) *
          Matrix.fromBlocks 0 K K 0 := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h3, Matrix.one_mul]
  obtain ⟨A, B, C, D, rfl⟩ : ∃ A B C D, g = Matrix.fromBlocks A B C D :=
    ⟨_, _, _, _, (Matrix.fromBlocks_toBlocks g).symm⟩
  rw [Matrix.fromBlocks_map, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj] at h4
  have h5 := h4.2.2.2
  simp only [Matrix.mul_zero, zero_add, add_zero] at h5
  have h6 : D * K.map σ * (C.map σ)ᵀ + C * K.map σ * (D.map σ)ᵀ = 0 := by
    have := congrArg (fun M : Matrix (Fin n) (Fin n) k => M.map σ) h5
    simp only [Matrix.map_add σ (map_add σ), Matrix.map_mul, hmm, Matrix.map_zero σ (map_zero σ)] at this
    simpa [Matrix.transpose_map] using this
  have hJσ : K.map σ * J.map σ = 1 := by
    rw [← Matrix.map_mul, hKJ]; simp
  obtain ⟨V, hV, hdet⟩ := GlobalTheory.T.exists_skewHermitian_mul_add_det_ne_zero k σ hσ ε hε0 hε n (C * K.map σ) D
    (by
      rw [Matrix.map_mul, hmm, Matrix.transpose_mul, hKt, ← Matrix.mul_assoc, add_comm]
      exact h6)
    (by
      intro a ha hD
      have hC : a ᵥ* C = 0 := by
        have : a ᵥ* (C * K.map σ * J.map σ) = 0 := by
          rw [← Matrix.vecMul_vecMul, ha, Matrix.zero_vecMul]
        rwa [Matrix.mul_assoc, hJσ, Matrix.mul_one] at this
      have h7 : (Sum.elim 0 a) ᵥ* Matrix.fromBlocks A B C D = 0 := by
        rw [Matrix.vecMul_fromBlocks]
        simp [hC, hD]
      have h8 := Matrix.eq_zero_of_vecMul_eq_zero hg h7
      funext i
      exact congrFun h8 (Sum.inr i))
  refine ⟨K.map σ * V, ?_, ?_⟩
  · rw [Matrix.transpose_mul, hKh, Matrix.mul_assoc, hKJ, Matrix.mul_one, Matrix.map_mul, hmm,
      ← Matrix.mul_assoc, hJK, Matrix.one_mul]
    have : V.map σ = -Vᵀ := by
      rw [← Matrix.transpose_neg, ← hV, Matrix.transpose_transpose]
    rw [this, add_neg_cancel]
  · simpa [Matrix.mul_assoc] using hdet

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicGraphDetLowerRowNeZeroFieldStatement
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isotropic_graph_det_ne_zero : ∀ (k : Type) [Field k] (σ : k →+* k), (∀ x, σ (σ x) = x) → (∃ ε : k, ε ≠ 0 ∧ σ ε = -ε) →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) k), (∀ i j, σ (J j i) = J i j) → J.det ≠ 0 →
    ∀ g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k, g.det ≠ 0 →
      gᵀ * Matrix.fromBlocks 0 J J 0 * g.map σ = Matrix.fromBlocks 0 J J 0 →
      ∃ Z : Matrix (Fin n) (Fin n) k, Zᵀ * J + J * Z.map σ = 0 ∧ (g.toBlocks₂₁ * Z + g.toBlocks₂₂).det ≠ 0 := by
  first | exact @GlobalTheory.exists_isotropic_graph_det_lowerRow_ne_zero_field | exact GlobalTheory.exists_isotropic_graph_det_lowerRow_ne_zero_field | (intros; apply GlobalTheory.exists_isotropic_graph_det_lowerRow_ne_zero_field <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftModMaximalSkew
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftModMaximalSkew
open scoped Matrix

namespace GlobalTheory

theorem lift_mod_maximal_skew : ∀ (O : Type) [CommRing O] [IsLocalRing O] (c : O →+* O), (∀ x, c (c x) = x) → IsUnit (2 : O) →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) O), (∀ i j, c (J j i) = J i j) → IsUnit J.det →
    ∀ Z₀ : Matrix (Fin n) (Fin n) O, (∀ i j, (Z₀ᵀ * J + J * Z₀.map c) i j ∈ IsLocalRing.maximalIdeal O) →
      ∃ Z : Matrix (Fin n) (Fin n) O, Zᵀ * J + J * Z.map c = 0 ∧ ∀ i j, Z i j - Z₀ i j ∈ IsLocalRing.maximalIdeal O := by
  intro O _ _ c hc h2 n J hJ hdet Z₀ hZ
  obtain ⟨u, hu⟩ : ∃ u : O, u * 2 = 1 := ⟨h2.unit⁻¹.val, h2.val_inv_mul⟩
  have hcu : c u = u := by
    have h1 : c u * 2 = 1 := by
      have := congrArg c hu
      simpa [map_mul, map_ofNat] using this
    calc c u = c u * (u * 2) := by rw [hu, mul_one]
      _ = (c u * 2) * u := by ring
      _ = u := by rw [h1, one_mul]
  set E := Z₀ᵀ * J + J * Z₀.map c with hE
  have hJc : (J.map c)ᵀ = J := by
    ext i j; simp [Matrix.transpose_apply, Matrix.map_apply, hJ]
  have hEc : (E.map c)ᵀ = E := by
    ext i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hE, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, Matrix.mul_apply, map_add (f := _), map_sum, map_mul, hc, hJ]
    rw [add_comm]
    congr 1 <;> refine Finset.sum_congr rfl (fun k _ => ?_) <;> ring
  have hJinv : J * ((J⁻¹).map c)ᵀ = 1 := by
    calc J * ((J⁻¹).map c)ᵀ = (J.map c)ᵀ * ((J⁻¹).map c)ᵀ := by rw [hJc]
      _ = ((J⁻¹).map c * J.map c)ᵀ := by rw [Matrix.transpose_mul]
      _ = ((J⁻¹ * J).map c)ᵀ := by rw [Matrix.map_mul]
      _ = 1 := by rw [Matrix.nonsing_inv_mul J hdet, Matrix.map_one c c.map_zero c.map_one, Matrix.transpose_one]
  set D := (u • (E * J⁻¹))ᵀ with hD
  have hDT : Dᵀ * J = u • E := by
    rw [hD, Matrix.transpose_transpose, Matrix.smul_mul, Matrix.mul_assoc, Matrix.nonsing_inv_mul J hdet, Matrix.mul_one]
  have hDmap : D.map c = u • (((J⁻¹).map c)ᵀ * (E.map c)ᵀ) := by
    rw [← Matrix.transpose_mul, ← Matrix.map_mul, hD]
    ext i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.mul_apply, map_sum, map_mul, hcu]
  have hDc : J * D.map c = u • E := by
    rw [hDmap, Matrix.mul_smul, ← Matrix.mul_assoc, hJinv, Matrix.one_mul, hEc]
  refine ⟨Z₀ - D, ?_, ?_⟩
  · have hmap : (Z₀ - D).map c = Z₀.map c - D.map c := by
      ext i j; simp [Matrix.map_apply]
    rw [Matrix.transpose_sub, Matrix.sub_mul, hmap, Matrix.mul_sub, hDT, hDc]
    have : E - u • E - u • E = 0 := by
      rw [sub_sub, ← add_smul, ← two_mul, mul_comm, hu, one_smul, sub_self]
    rw [← this, hE]; abel
  · intro i j
    have : (Z₀ - D) i j - Z₀ i j = -(u * ∑ k, E j k * J⁻¹ k i) := by
      simp [hD, Matrix.transpose_apply, Matrix.mul_apply, Matrix.smul_apply, mul_comm]
    rw [this]
    exact neg_mem (Ideal.mul_mem_left _ _ (Ideal.sum_mem _ (fun k _ => Ideal.mul_mem_right _ _ (hZ j k))))

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftModMaximalSkewStatement
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_skew_lift_mod_maximalIdeal : ∀ (O : Type) [CommRing O] [IsLocalRing O] (c : O →+* O), (∀ x, c (c x) = x) → IsUnit (2 : O) →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) O), (∀ i j, c (J j i) = J i j) → IsUnit J.det →
    ∀ Z₀ : Matrix (Fin n) (Fin n) O, (∀ i j, (Z₀ᵀ * J + J * Z₀.map c) i j ∈ IsLocalRing.maximalIdeal O) →
      ∃ Z : Matrix (Fin n) (Fin n) O, Zᵀ * J + J * Z.map c = 0 ∧ ∀ i j, Z i j - Z₀ i j ∈ IsLocalRing.maximalIdeal O := by
  first | exact @GlobalTheory.lift_mod_maximal_skew | exact GlobalTheory.lift_mod_maximal_skew | (intros; apply GlobalTheory.lift_mod_maximal_skew <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicGraphUnitaryIsUnitLowerBlock
open scoped Matrix

namespace GlobalTheory

theorem exists_isotropic_graph_isUnit_lowerRow : ∀ (O : Type) [CommRing O] [IsLocalRing O] (c : O →+* O), (∀ x, c (c x) = x) → IsUnit (2 : O) →
    (∃ x : O, IsUnit (c x - x)) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) O), (∀ i j, c (J j i) = J i j) → IsUnit J.det →
    ∀ g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O, IsUnit g.det →
      gᵀ * Matrix.fromBlocks 0 J J 0 * g.map c = Matrix.fromBlocks 0 J J 0 →
      ∃ Z : Matrix (Fin n) (Fin n) O, Zᵀ * J + J * Z.map c = 0 ∧ IsUnit (g.toBlocks₂₁ * Z + g.toBlocks₂₂).det := by
  have hfield := GlobalTheory.T.exists_isotropic_graph_det_ne_zero
  have hlift := GlobalTheory.T.exists_skew_lift_mod_maximalIdeal

  intro O _ _ c hc h2 hx0 n J hJ hJdet g hg hgu
  obtain ⟨x, hx⟩ := hx0
  haveI : IsLocalHom c := ⟨fun a ha => by simpa [hc] using ha.map c⟩
  set π := IsLocalRing.residue O with hπ
  set σ : IsLocalRing.ResidueField O →+* IsLocalRing.ResidueField O := IsLocalRing.ResidueField.map c with hσ
  have hσπ : ∀ a, σ (π a) = π (c a) := fun a => IsLocalRing.ResidueField.map_residue c a
  have hσσ : ∀ y, σ (σ y) = y := by
    intro y; obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y; rw [hσπ, hσπ, hc]
  have hε : ∃ ε, ε ≠ 0 ∧ σ ε = -ε := ⟨π (c x - x), (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hx, by
    rw [hσπ, map_sub, hc, ← neg_sub, map_neg]⟩
  have hmapc : ∀ {m : Type} (M : Matrix m m O), (M.map c).map π = (M.map π).map σ := by
    intro m M; ext i j; simp [hσπ]
  have hJ' : ∀ i j, σ (J.map π j i) = J.map π i j := by intro i j; simp [hσπ, hJ]
  have hJdet' : (J.map π).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hJdet
  have hg' : (g.map π).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hg
  have hgu' : (g.map π)ᵀ * Matrix.fromBlocks 0 (J.map π) (J.map π) 0 * (g.map π).map σ
      = Matrix.fromBlocks 0 (J.map π) (J.map π) 0 := by
    have := congrArg (fun M => M.map π) hgu
    simpa only [Matrix.map_mul, Matrix.transpose_map, hmapc, Matrix.fromBlocks_map,
      Matrix.map_zero _ (map_zero π)] using this
  obtain ⟨Zb, hZb, hdet⟩ := hfield _ σ hσσ hε n _ hJ' hJdet' _ hg' hgu'
  obtain ⟨Z₀, hZ₀⟩ : ∃ Z₀ : Matrix (Fin n) (Fin n) O, Z₀.map π = Zb :=
    ⟨fun i j => (IsLocalRing.residue_surjective (Zb i j)).choose, by
      ext i j; exact (IsLocalRing.residue_surjective (Zb i j)).choose_spec⟩
  have hZ₀m : ∀ i j, (Z₀ᵀ * J + J * Z₀.map c) i j ∈ IsLocalRing.maximalIdeal O := by
    intro i j
    rw [← IsLocalRing.residue_eq_zero_iff]
    have := congrArg (fun M => M i j) hZb
    simp only [Matrix.zero_apply] at this
    rw [← this, ← hZ₀, ← hmapc, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add π)]
    rfl
  obtain ⟨Z, hZ, hZm⟩ := hlift O c hc h2 n J hJ hJdet Z₀ hZ₀m
  refine ⟨Z, hZ, ?_⟩
  have hZπ : Z.map π = Zb := by
    rw [← hZ₀]; ext i j
    simp only [Matrix.map_apply]
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]; exact hZm i j
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, ← hπ, RingHom.map_det, RingHom.mapMatrix_apply,
    Matrix.map_add _ (map_add π), Matrix.map_mul, hZπ]
  exact hdet

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicGraphUnitaryIsUnitLowerBlockStatement
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isotropic_graph_unitary_isUnit_lowerBlock : ∀ (O : Type) [CommRing O] [IsLocalRing O] (c : O →+* O), (∀ x, c (c x) = x) → IsUnit (2 : O) →
    (∃ x : O, IsUnit (c x - x)) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) O), (∀ i j, c (J j i) = J i j) → IsUnit J.det →
    ∀ g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O, IsUnit g.det →
      gᵀ * Matrix.fromBlocks 0 J J 0 * g.map c = Matrix.fromBlocks 0 J J 0 →
      ∃ Z : Matrix (Fin n) (Fin n) O, Zᵀ * J + J * Z.map c = 0 ∧ IsUnit (g.toBlocks₂₁ * Z + g.toBlocks₂₂).det := by
  first | exact @GlobalTheory.exists_isotropic_graph_isUnit_lowerRow | exact GlobalTheory.exists_isotropic_graph_isUnit_lowerRow | (intros; apply GlobalTheory.exists_isotropic_graph_isUnit_lowerRow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentCornerIsUnitInertPlace
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertTransv

theorem exists_unip_corner_isUnit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n r s : ℕ) (X : Spc F E n), B.IsGood σ → X.IsHerm σ B r s →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → ∀ g ∈ GlobalTheory.DblVac.KD σ X v,
    ∃ u ∈ GlobalTheory.DblVac.KD σ X v, u ∈ GlobalTheory.DblVac.PDiag σ X ∧
      IsUnit ((GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * GlobalTheory.DblVac.matD (g * u) * GlobalTheory.DblVac.antiCols n).det ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt X v,
        ((GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * GlobalTheory.DblVac.matD (g * u) * GlobalTheory.DblVac.antiCols n)⁻¹ *ᵥ z ∈
          GlobalTheory.InertSph.latAt X v := by
  intro F E _ _ _ _ _ σ B n r s X hB hX v w hvw g hg
  obtain ⟨Z, hZs, hZl, hZn, hdet, hinv⟩ := GlobalTheory.T.exists_inertPlace_transversal_of_localCore GlobalTheory.T.exists_isotropic_graph_unitary_isUnit_lowerBlock F E σ B n r s X hB hX v w hvw g hg
  have h2 : (2 : 𝓞 F) ∉ v.asIdeal := (hB.inert v w hvw).1
  obtain ⟨u, huK, huP, hu⟩ := GlobalTheory.T.halfSkewUnipotent_mem_doubledLatticeStabilizer F E σ n X v h2 Z hZs hZl hZn
  set N : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E) := GlobalTheory.DblVac.antiCols (F := F) (E := E) n with hN
  set Δ : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E) := diagCols (Fin n) with hΔ
  have hNN : Nᵀ * N = (2 : AF F) • (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
    rw [hN, GlobalTheory.DblVac.antiCols, Matrix.transpose_fromRows, Matrix.transpose_one, Matrix.transpose_neg,
      Matrix.transpose_one, Matrix.fromCols_mul_fromRows]
    simp [two_smul]
  have hmul : GlobalTheory.DblVac.matD (g * u) = GlobalTheory.DblVac.matD g * GlobalTheory.DblVac.matD u := rfl
  have key : Nᵀ * GlobalTheory.DblVac.matD (g * u) * N = Nᵀ * GlobalTheory.DblVac.matD g * N + Nᵀ * GlobalTheory.DblVac.matD g * Δ * Z := by
    rw [hmul, hu]
    have : Nᵀ * (GlobalTheory.DblVac.matD g * (1 + (⅟(2 : AF F)) • (Δ * Z * Nᵀ))) * N =
        Nᵀ * GlobalTheory.DblVac.matD g * N + (⅟(2 : AF F)) • (Nᵀ * GlobalTheory.DblVac.matD g * Δ * Z * (Nᵀ * N)) := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    rw [this, hNN, Matrix.mul_smul, smul_smul, invOf_mul_self, one_smul, Matrix.mul_one]
  refine ⟨u, huK, huP, ?_, ?_⟩
  · convert hdet using 2
    exact congrArg Matrix.det key
  · intro z hz; convert hinv z hz using 3
    exact key

end GlobalTheory.InertTransv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentCornerIsUnitInertPlaceStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unipotent_corner_isUnit_inertPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n r s : ℕ) (X : Spc F E n), B.IsGood σ → X.IsHerm σ B r s →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → ∀ g ∈ GlobalTheory.DblVac.KD σ X v,
    ∃ u ∈ GlobalTheory.DblVac.KD σ X v, u ∈ GlobalTheory.DblVac.PDiag σ X ∧
      IsUnit ((GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * GlobalTheory.DblVac.matD (g * u) * GlobalTheory.DblVac.antiCols n).det ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt X v,
        ((GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * GlobalTheory.DblVac.matD (g * u) * GlobalTheory.DblVac.antiCols n)⁻¹ *ᵥ z ∈
          GlobalTheory.InertSph.latAt X v := by
  first | exact @GlobalTheory.InertTransv.exists_unip_corner_isUnit | exact GlobalTheory.InertTransv.exists_unip_corner_isUnit | (intros; apply GlobalTheory.InertTransv.exists_unip_corner_isUnit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBoxTensorLeftFixedLinearApply
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.DblGenV

open Matrix GlobalTheory.DblVac

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem matD_mul {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} (g h : UD σ W) : matD (g * h) = matD g * matD h := rfl

theorem matD_inv_mul {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} (g : UD σ W) : matD g⁻¹ * matD g = 1 := by
  rw [← matD_mul, inv_mul_cancel]; rfl

theorem KD_mul {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} {v : Pl (F := F)} {g h : UD σ W} (hg : g ∈ KD σ W v)
    (hh : h ∈ KD σ W v) : g * h ∈ KD σ W v := by
  refine ⟨fun u hu => ?_, fun z hz => ?_⟩
  · have e : matD (g * h) - 1 = matD g * (matD h - 1) + (matD g - 1) := by
      rw [matD_mul, Matrix.mul_sub, Matrix.mul_one]; abel
    show u • (matD (g * h) - 1) = 0
    have h1 : u • (matD h - 1) = 0 := hh.1 u hu
    have h2 : u • (matD g - 1) = 0 := hg.1 u hu
    rw [e, smul_add, ← Matrix.mul_smul, h1, h2, Matrix.mul_zero, add_zero]
  · refine ⟨?_, ?_⟩
    · rw [matD_mul, ← Matrix.mulVec_mulVec]; exact (hg.2 _ (hh.2 z hz).1).1
    · rw [_root_.mul_inv_rev, matD_mul, ← Matrix.mulVec_mulVec]; exact (hh.2 _ (hg.2 z hz).2).2

theorem KD_inv {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} {v : Pl (F := F)} {g : UD σ W} (hg : g ∈ KD σ W v) :
    g⁻¹ ∈ KD σ W v := by
  refine ⟨fun u hu => ?_, fun z hz => ?_⟩
  · have e : matD g⁻¹ - 1 = -(matD g⁻¹ * (matD g - 1)) := by
      rw [Matrix.mul_sub, matD_inv_mul, Matrix.mul_one]; abel
    show u • (matD g⁻¹ - 1) = 0
    have h2 : u • (matD g - 1) = 0 := hg.1 u hu
    rw [e, smul_neg, ← Matrix.mul_smul, h2, Matrix.mul_zero, neg_zero]
  · rw [inv_inv]; exact ⟨(hg.2 z hz).2, (hg.2 z hz).1⟩

theorem PDiag_inv {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} {p : UD σ W} (hp : p ∈ PDiag σ W) :
    p⁻¹ ∈ PDiag σ W := by
  obtain ⟨t, ht⟩ := hp
  refine ⟨t⁻¹, ?_⟩
  set D : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E) := diagCols (Fin d) with hDdef
  set T : Matrix (Fin d) (Fin d) (AE F E) := (t : Matrix (Fin d) (Fin d) (AE F E)) with hT
  set Ti : Matrix (Fin d) (Fin d) (AE F E) := ((t⁻¹ : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)) with hTi
  have hTT : T * Ti = 1 := by rw [hT, hTi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have ht' : matD p * D = D * T := ht
  have key : matD p⁻¹ * (D * T) = D := by
    rw [← ht', ← Matrix.mul_assoc, matD_inv_mul, Matrix.one_mul]
  show matD p⁻¹ * D = D * Ti
  calc matD p⁻¹ * D = matD p⁻¹ * (D * T) * Ti := by
        rw [Matrix.mul_assoc (matD p⁻¹), Matrix.mul_assoc D, hTT, Matrix.mul_one]
    _ = D * Ti := by rw [key]

end GlobalTheory.DblGenV

namespace GlobalTheory.DblGenV

theorem mem_of_KD_diag_anti : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T → ∀ H : Subgroup (GlobalTheory.DblVac.UD σ G.V),
      (∀ p ∈ GlobalTheory.DblVac.KD σ G.V v, p ∈ GlobalTheory.DblVac.PDiag σ G.V → p ∈ H) →
      (∀ p ∈ GlobalTheory.DblVac.KD σ G.V v, p ∈ GlobalTheory.DblVac.PAnti σ G.V → p ∈ H) → ∀ g ∈ GlobalTheory.DblVac.KD σ G.V v, g ∈ H := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hin _ H hD hA g hg
  have h2 : (2 : 𝓞 F) ∉ v.asIdeal := (hT.base.inert v w hin).1
  obtain ⟨u, hu, huP, hdet, hlat⟩ := GlobalTheory.T.exists_unipotent_corner_isUnit_inertPlace F E σ B a (a - G.p) G.p G.V hT.base hT.geo.hV v w hin g hg
  obtain ⟨p, q, hp, hpP, hq, hqA, hpq⟩ := GlobalTheory.T.doubledVacuumLatticeStabilizer_bigCell_factorization F E σ a G.V v h2 (g * u) (KD_mul hg hu) hdet hlat
  have e : g = p * q * u⁻¹ := by rw [← hpq]; group
  rw [e]
  exact H.mul_mem (H.mul_mem (hD p hp hpP) (hA q hq hqA)) (hD _ (KD_inv hu) (PDiag_inv huP))

end GlobalTheory.DblGenV
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBoxTensorLeftFixedLinearApplyStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledStabilizer_generated_antidiag_splitPlace_V : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T → ∀ H : Subgroup (GlobalTheory.DblVac.UD σ G.V),
      (∀ p ∈ GlobalTheory.DblVac.KD σ G.V v, p ∈ GlobalTheory.DblVac.PDiag σ G.V → p ∈ H) →
      (∀ p ∈ GlobalTheory.DblVac.KD σ G.V v, p ∈ GlobalTheory.DblVac.PAnti σ G.V → p ∈ H) → ∀ g ∈ GlobalTheory.DblVac.KD σ G.V v, g ∈ H := by
  first | exact @GlobalTheory.DblGenV.mem_of_KD_diag_anti | exact GlobalTheory.DblGenV.mem_of_KD_diag_anti | (intros; apply GlobalTheory.DblGenV.mem_of_KD_diag_anti <;> assumption)
end
