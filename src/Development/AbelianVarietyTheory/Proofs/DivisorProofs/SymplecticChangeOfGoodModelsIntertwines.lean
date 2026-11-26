module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergLatticeSelfDualEveryFinitePlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasInfinityExponentOfFinitePartPower
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylElementHasRationalWeilOperatorAdelicFourier

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumEigenvalueThetaIndependent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumEigenvalueIndependentOfTheta
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.VacThetaInd

theorem psi_half_symp_theta_indep : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    ∀ (v : Pl (F := F)) (θ θ' : 𝓞 E), (θ : E) + σ θ = 1 → (θ' : E) + σ θ' = 1 → ∀ γ ∈ latAtV X W v,
      B.ψ (⅟(2 : AF F) * symp (R := AF F) (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) γ γ) =
        B.ψ (⅟(2 : AF F) * symp (R := AF F) (cA σ) (inclR (F := F) (AF F) (θ' : E)) (incM F X.J) (incM F W.J) γ γ) := by
  intro F E _ _ _ _ _ σ B n d X W r s r' s' hB hX hW v θ θ' hθ hθ' γ hγ
  have hσ : ∀ x : E, σ (σ x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star]
  have hc : ∀ z, cA σ (cA σ z) = z := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [cA, hσ]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have hi : ∀ e : E, cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := fun e => rfl
  have ht : cA σ (hTens (cA σ) (incM F X.J) (incM F W.J) γ γ) = -hTens (cA σ) (incM F X.J) (incM F W.J) γ γ :=
    GlobalTheory.VacCocycle.conj_hTens (cA σ) hc (fun i j => by simp only [incM, Matrix.map_apply, hi, hX.herm])
      (fun i j => by simp only [incM, Matrix.map_apply, hi, hW.skew, map_neg]) γ γ
  set t := hTens (cA σ) (incM F X.J) (incM F W.J) γ γ with htdef
  have htr : ∀ z, Algebra.trace (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (cA σ z) = Algebra.trace (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) z :=
    GlobalTheory.VacCocycle.trace_conj (cA σ) hc
  set a := inclR (F := F) (AF F) (θ : E) with ha
  set a' := inclR (F := F) (AF F) (θ' : E) with ha'
  have hca : cA σ a = 1 - a := by
    rw [ha, hi, eq_sub_of_add_eq' hθ, map_sub, map_one]
  have hca' : cA σ a' = 1 - a' := by
    rw [ha', hi, eq_sub_of_add_eq' hθ', map_sub, map_one]
  set z := (a - a') * t with hz
  have hcz : cA σ z = z := by
    rw [hz, map_mul, map_sub, hca, hca', ht]; ring
  have h2 : Algebra.trace (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) z = 2 * Algebra.trace (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (a * z) := by
    have e1 : Algebra.trace (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (cA σ (a * z)) = Algebra.trace (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (a * z) := htr _
    rw [map_mul, hca, hcz, sub_mul, one_mul, map_sub] at e1
    linear_combination e1
  have hmul : inclR (F := F) (AF F) (((θ * (θ - θ') : 𝓞 E)) : E) = a * (a - a') := by
    rw [ha, ha', ← map_sub, ← map_mul]; push_cast; rfl
  have key : symp (R := AF F) (cA σ) a (incM F X.J) (incM F W.J) γ γ =
      symp (R := AF F) (cA σ) a' (incM F X.J) (incM F W.J) γ γ +
        2 * symp (R := AF F) (cA σ) (inclR (F := F) (AF F) (((θ * (θ - θ') : 𝓞 E)) : E)) (incM F X.J) (incM F W.J) γ γ := by
    simp only [symp, hmul]
    rw [← htdef, mul_assoc, ← hz, ← h2, hz, sub_mul, map_sub]; ring
  have h1 := GlobalTheory.LatVacArith.psi_symp_latAtV σ B X W r s r' s' hB hX hW v (θ * (θ - θ')) 1
    (by rw [map_one]; exact one_mem _) γ hγ γ hγ
  rw [key, mul_add, ← mul_assoc, invOf_mul_self, one_mul, AddChar.map_add_eq_mul, ← one_mul (symp (R := AF F) (cA σ) (inclR (F := F) (AF F) (((θ * (θ - θ') : 𝓞 E)) : E)) (incM F X.J) (incM F W.J) γ γ), h1, mul_one]

end GlobalTheory.VacThetaInd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumEigenvalueThetaIndependent
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

noncomputable section

namespace GlobalTheory.VacThetaIndep

theorem vacuum_character_theta_indep : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    ∀ (v : Pl (F := F)) (θ θ' : 𝓞 E), (θ : E) + σ θ = 1 → (θ' : E) + σ θ' = 1 → ∀ γ ∈ latAtV X W v,
      B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) γ γ) =
        B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ' : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) γ γ) :=
  GlobalTheory.VacThetaInd.psi_half_symp_theta_indep

end GlobalTheory.VacThetaIndep

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumEigenvalueThetaIndependentStatement
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuum_eigenvalue_theta_independent : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    ∀ (v : Pl (F := F)) (θ θ' : 𝓞 E), (θ : E) + σ θ = 1 → (θ' : E) + σ θ' = 1 → ∀ γ ∈ latAtV X W v,
      B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) γ γ) =
        B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ' : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) γ γ) := by
  first | exact @GlobalTheory.VacThetaIndep.vacuum_character_theta_indep | exact GlobalTheory.VacThetaIndep.vacuum_character_theta_indep | (intros; apply GlobalTheory.VacThetaIndep.vacuum_character_theta_indep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfSchroedingerTranslatesThetaSumZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfSchroedingerTranslatesThetaSumZero
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

noncomputable section

open scoped Classical

namespace GlobalTheory.ThetaInj

theorem main : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ], ∀ Φ ∈ schA F κ,
    (∀ w : (κ → AF F) × (κ → AF F), thetaSum F (schr ψ w Φ) = 0) → Φ = 0 := by
  intro F _ _ ψ hψ κ _ Φ hΦ h
  have hn : ∀ a, ‖ψ a‖ = 1 := GlobalTheory.StdCharFromIsStd.norm_psi hψ
  obtain ⟨a₀, ha₀⟩ := GlobalTheory.StdCharFromIsStd.exists_ne_one hψ
  let ι : (κ → F) → (κ → AF F) := fun ξ i => algebraMap F (AF F) (ξ i)
  have hι0 : ι 0 = 0 := by funext i; simp [ι]
  funext x
  have hΦx : (fun z => Φ (z + x)) ∈ schA F κ := GlobalTheory.SchwartzTranslate.schA_translate F x hΦ
  have hc : Summable fun ξ => ‖Φ (ι ξ + x)‖ := by
    convert GlobalTheory.WeilM.summable_norm_of_mem_schA F hΦx using 1
  have key := GlobalTheory.SchrodingerUniq.coeff_zero_eq_zero
    (χ := fun (y : κ → AF F) (ξ : κ → F) => ψ (ι ξ ⬝ᵥ y))
    (c := fun ξ => Φ (ι ξ + x)) (fun y ξ => hn _)
    (fun y y' ξ => by simp only [dotProduct_add, AddChar.map_add_eq_mul])
    (fun ξ => by simp only [dotProduct_zero, AddChar.map_zero_eq_one])
    (fun y => by simp only [hι0, zero_dotProduct, AddChar.map_zero_eq_one])
    (fun ξ hξ => by
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hξ
      have hi' : ξ i ≠ 0 := hi
      refine ⟨Pi.single i (algebraMap F (AF F) (ξ i)⁻¹ * a₀), ?_⟩
      show ψ (ι ξ ⬝ᵥ Pi.single i (algebraMap F (AF F) (ξ i)⁻¹ * a₀)) ≠ 1
      rw [dotProduct_single]
      show ψ (algebraMap F (AF F) (ξ i) * (algebraMap F (AF F) (ξ i)⁻¹ * a₀)) ≠ 1
      rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hi', map_one, one_mul]
      exact ha₀)
    hc (fun y => ?_)
  · simpa [hι0] using key
  · have h' := h (x, y)
    simp only [GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.schr, AddChar.map_add_eq_mul] at h'
    set b := ψ (⅟(2 : AF F) * (x ⬝ᵥ y))
    have hb : b ≠ 0 := by
      intro e
      have h1 : ‖b‖ = 1 := hn _
      rw [e, norm_zero] at h1
      exact zero_ne_one h1
    have e2 : ∑' ξ : κ → F, Φ (ι ξ + x) * ψ (ι ξ ⬝ᵥ y) =
        b⁻¹ * ∑' ξ : κ → F, ψ (ι ξ ⬝ᵥ y) * b * Φ (ι ξ + x) := by
      rw [← tsum_mul_left]; congr 1; funext ξ; field_simp
    rw [e2, h', mul_zero]

end GlobalTheory.ThetaInj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfSchroedingerTranslatesThetaSumZeroStatement
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_schroedingerTranslates_thetaSum_zero : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ], ∀ Φ ∈ schA F κ,
    (∀ w : (κ → AF F) × (κ → AF F), thetaSum F (schr ψ w Φ) = 0) → Φ = 0 := by
  first | exact @GlobalTheory.ThetaInj.main | exact GlobalTheory.ThetaInj.main | (intros; apply GlobalTheory.ThetaInj.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticGroupGeneratedLeviLowerUnipotentWeyl
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticGroupGeneratedLeviLowerUnipotentWeyl
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

namespace GlobalTheory.SpGen
open Matrix

theorem upper_unipotent_eq {K : Type} [Field K] {κ : Type} [Fintype κ] [DecidableEq κ]
    (s : Matrix κ κ K) :
    (fromBlocks 1 s 0 1 : Matrix (κ ⊕ κ) (κ ⊕ κ) K) =
      fromBlocks 0 1 (-1) 0 * fromBlocks 1 0 (-s) 1 * fromBlocks 0 1 (-1) 0 *
        fromBlocks (-1) 0 0 (-1) := by
  simp [fromBlocks_multiply]

theorem symplectic_generated_levi_lower_weyl :
    ∀ (K : Type) [Field K] (κ : Type) [Fintype κ] [DecidableEq κ] (P : Matrix (κ ⊕ κ) (κ ⊕ κ) K → Prop),
    (∀ a b, P a → P b → P (a * b)) → (∀ g h : Matrix κ κ K, gᵀ * h = 1 → P (Matrix.fromBlocks g 0 0 h)) →
    (∀ b : Matrix κ κ K, bᵀ = b → P (Matrix.fromBlocks 1 0 b 1)) → P (Matrix.fromBlocks 0 1 (-1) 0) →
    ∀ a : Matrix (κ ⊕ κ) (κ ⊕ κ) K, aᵀ * Matrix.fromBlocks 0 1 (-1) 0 * a = Matrix.fromBlocks 0 1 (-1) 0 → P a := by
  intro K _ κ _ _ P hmul hlevi hlow hJ a ha
  have hup : ∀ s : Matrix κ κ K, sᵀ = s → P (fromBlocks 1 s 0 1) := by
    intro s hs
    rw [upper_unipotent_eq]
    exact hmul _ _ (hmul _ _ (hmul _ _ hJ (hlow _ (by simp [hs]))) hJ) (hlevi _ _ (by simp))
  have hJ0 : (fromBlocks 0 1 (-1) 0 : Matrix (κ ⊕ κ) (κ ⊕ κ) K) = -J κ K := by
    simp [J, fromBlocks_neg]
  have hsp : a ∈ symplecticGroup κ K := by
    rw [SymplecticGroup.mem_iff']
    rw [hJ0] at ha
    simpa [Matrix.mul_neg, Matrix.neg_mul] using ha
  obtain ⟨A, B, C, D, rfl⟩ : ∃ A B C D, a = fromBlocks A B C D :=
    ⟨_, _, _, _, a.fromBlocks_toBlocks.symm⟩
  have hExists : ∃ X : Matrix κ κ K, X.IsSymm ∧ IsUnit (A + X * C).det := by
    -- Use the field case of Mathlib's construction in LinearAlgebra/SymplecticGroup.
    have hker (x : κ → K) (hAx : A • x = 0) (hCx : C • x = 0) : x = 0 := by
      rw [smul_eq_mulVec] at hAx hCx
      have hunit := (fromBlocks A B C D).isUnit_iff_isUnit_det.2
        (SymplecticGroup.symplectic_det hsp)
      have hzero : fromBlocks A B C D *ᵥ Sum.elim x 0 =
          fromBlocks A B C D *ᵥ Sum.elim 0 0 := by
        simp [fromBlocks_mulVec, hAx, hCx]
      exact (Sum.elim_eq_iff.1 (mulVec_injective_iff_isUnit.2 hunit hzero)).1
    have hsymm := (SymplecticGroup.fromBlocks_mem_iff.1 hsp).1
    obtain ⟨V, U, e, hV, hU, heq⟩ := exists_rank_normal_form C
    set R := V * C * U with hR
    set S := Vᵀ⁻¹ * A * U with hS
    let f := fun M : Matrix κ κ K ↦ M.submatrix e.symm e.symm
    have hf (M : Matrix κ κ K) : f M = M.submatrix e.symm e.symm := rfl
    have f_unit {M} : IsUnit M → IsUnit (f M) := (isUnit_submatrix_equiv ..).2
    have f_mul (M N) : f (M * N) = f M * f N := submatrix_mul _ _ _ _ _ e.symm.bijective
    let _ : Invertible V := hV.invertible
    let _ : Invertible U := hU.invertible
    let _ : Invertible (f Vᵀ) := (f_unit (V.isUnit_transpose.2 hV)).invertible
    have hker' (x : Fin C.rank ⊕ Fin (Fintype.card κ - C.rank) → K)
        (hxS : f S • x = 0) (hxR : f R • x = 0) : x = 0 := by
      refine (f_unit hU).smul_left_cancel.1 ?_
      rw [f_mul, f_mul, mul_assoc, mul_smul, IsUnit.smul_eq_zero, mul_smul, hf,
        smul_eq_mulVec, submatrix_mulVec_equiv, Equiv.symm_symm] at hxS hxR
      · rw [Equiv.comp_symm_eq, Pi.zero_comp] at hxS hxR
        exact e.surjective.injective_comp_right <| by simpa using hker _ hxS hxR
      · exact f_unit hV
      · exact f_unit <| isUnit_nonsing_inv_iff.2 <| V.isUnit_transpose.2 hV
    have hSR : Sᵀ * R = Rᵀ * S := by
      simp only [hR, mul_assoc, transpose_mul, transpose_nonsing_inv, transpose_transpose, hS,
        inv_mul_cancel_left_of_invertible, mul_inv_cancel_left_of_invertible]
      rw [← mul_assoc Aᵀ, hsymm, mul_assoc]
    have hblocks : (f S).toBlocks₁₁ᵀ = (f S).toBlocks₁₁ ∧ (f S).toBlocks₁₂ = 0 := by
      apply_fun reindex e e at hSR
      rw [reindex_apply, reindex_apply, ← hf, ← hf, f_mul, f_mul Rᵀ, heq, hf,
        ← transpose_submatrix, ← hf S, ← (f S).fromBlocks_toBlocks, hf (_)ᵀ, hf
        ((fromBlocks 1 0 0 0).submatrix _ _)] at hSR
      simp [fromBlocks_transpose, fromBlocks_multiply] at hSR
      tauto
    have h₂₂ : IsUnit (f S).toBlocks₂₂ := by
      refine mulVec_injective_iff_isUnit.1 ?_
      rw [← coe_mulVecLin, ← LinearMap.ker_eq_bot]
      refine ker_mulVecLin_eq_bot_iff.2 fun x hx ↦ Sum.elim_injective' <|
        (hker' _ ?_ ?_).trans Sum.elim_zero_zero.symm
      · rw [← (f S).fromBlocks_toBlocks]
        simp [hx, hblocks.2, fromBlocks_mulVec]
      · simp [hf, heq, fromBlocks_mulVec]
    set Y : Matrix (Fin C.rank ⊕ Fin (Fintype.card κ - C.rank))
      (Fin C.rank ⊕ Fin (Fintype.card κ - C.rank)) K :=
      fromBlocks (1 - (f S).toBlocks₁₁) 0 0 0 with hY
    have hYsymm : Y.IsSymm := by
      rw [hY, isSymm_fromBlocks_iff]
      exact ⟨IsSymm.sub isSymm_one hblocks.1, by simp⟩
    set X := f Vᵀ * Y * f V with hX
    refine ⟨X.submatrix e e, IsSymm.submatrix ?_ e, (isUnit_iff_isUnit_det _).1
      ((isUnit_submatrix_equiv e.symm e.symm).1 ?_)⟩
    · simp_rw [hX, Matrix.IsSymm, transpose_mul, hYsymm.eq, hf, transpose_submatrix,
        transpose_transpose, mul_assoc]
    · have hsum : f (A + X.submatrix e e * C) = f Vᵀ * (f S + Y * f R) * f U⁻¹ := by
        simp_rw [hf, submatrix_add, Pi.add_apply, hS, hR, ← hf, f_mul, hf, mul_add, ← mul_assoc,
          ← inv_submatrix_equiv, add_mul, mul_assoc _ (U.submatrix _ _), mul_inv_of_invertible]
        simp [hX]
        rfl
      rw [← hf, hsum, IsUnit.mul_iff, IsUnit.mul_iff]
      refine ⟨⟨isUnit_of_invertible _, ?_⟩, f_unit (isUnit_nonsing_inv_iff.2 hU)⟩
      nth_rw 1 [hY, heq, ← (f S).fromBlocks_toBlocks, hblocks.2]
      simpa [hf, fromBlocks_multiply, fromBlocks_add] using h₂₂
  obtain ⟨X, hX, hu⟩ := hExists
  have hUX : (fromBlocks 1 X 0 1 : Matrix (κ ⊕ κ) (κ ⊕ κ) K) ∈ symplecticGroup κ K := by
    simp [SymplecticGroup.fromBlocks_mem_iff, hX.eq]
  have hprod : (fromBlocks 1 X 0 1 : Matrix (κ ⊕ κ) (κ ⊕ κ) K) * fromBlocks A B C D =
      fromBlocks (A + X * C) (B + X * D) C D := by
    simp [fromBlocks_multiply]
  generalize hc : A + X * C = c at hu hprod
  have hcT : IsUnit cᵀ.det := by rwa [det_transpose]
  have hLev : (fromBlocks c⁻¹ 0 0 cᵀ : Matrix (κ ⊕ κ) (κ ⊕ κ) K) ∈ symplecticGroup κ K := by
    rw [SymplecticGroup.fromBlocks_mem_iff]
    refine ⟨by simp, by simp, ?_⟩
    rw [transpose_nonsing_inv]
    simp [nonsing_inv_mul _ hcT]
  have hnsp := mul_mem (mul_mem hLev hUX) hsp
  have hn : (fromBlocks c⁻¹ 0 0 cᵀ : Matrix (κ ⊕ κ) (κ ⊕ κ) K) * fromBlocks 1 X 0 1 *
      fromBlocks A B C D = fromBlocks 1 (c⁻¹ * (B + X * D)) (cᵀ * C) (cᵀ * D) := by
    rw [Matrix.mul_assoc, hprod, fromBlocks_multiply]
    simp [nonsing_inv_mul _ hu]
  rw [hn] at hnsp
  generalize c⁻¹ * (B + X * D) = Z at hn hnsp
  generalize cᵀ * C = Wm at hn hnsp
  generalize cᵀ * D = V at hn hnsp
  obtain ⟨h1, h2, h3⟩ := SymplecticGroup.fromBlocks_mem_iff.1 hnsp
  simp only [transpose_one, Matrix.one_mul, Matrix.mul_one] at h1 h3
  have hW : Wmᵀ = Wm := h1.symm
  rw [hW] at h3
  have hV : V = Wm * Z + 1 := by rw [← h3]; abel
  have hZ : Zᵀ = Z := by
    rw [hV, transpose_add, transpose_mul, hW, transpose_one, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_one, Matrix.one_mul, ← Matrix.mul_assoc] at h2
    simpa using h2
  have hfac : (fromBlocks 1 Z Wm V : Matrix (κ ⊕ κ) (κ ⊕ κ) K) =
      fromBlocks 1 0 Wm 1 * fromBlocks 1 Z 0 1 := by
    rw [fromBlocks_multiply, hV]; simp
  have e2 : (fromBlocks c 0 0 cᵀ⁻¹ : Matrix (κ ⊕ κ) (κ ⊕ κ) K) * fromBlocks c⁻¹ 0 0 cᵀ = 1 := by
    rw [fromBlocks_multiply]
    simp [mul_nonsing_inv _ hu, nonsing_inv_mul _ hcT]
  have e3 : (fromBlocks 1 (-X) 0 1 : Matrix (κ ⊕ κ) (κ ⊕ κ) K) * fromBlocks 1 X 0 1 = 1 := by
    simp [fromBlocks_multiply]
  have hdec : fromBlocks A B C D = (fromBlocks 1 (-X) 0 1 : Matrix (κ ⊕ κ) (κ ⊕ κ) K) *
      fromBlocks c 0 0 cᵀ⁻¹ * (fromBlocks c⁻¹ 0 0 cᵀ * fromBlocks 1 X 0 1 * fromBlocks A B C D) := by
    rw [Matrix.mul_assoc (fromBlocks 1 (-X) 0 1), ← Matrix.mul_assoc (fromBlocks c 0 0 cᵀ⁻¹),
      ← Matrix.mul_assoc (fromBlocks c 0 0 cᵀ⁻¹), e2, Matrix.one_mul, ← Matrix.mul_assoc, e3,
      Matrix.one_mul]
  rw [hdec, hn, hfac]
  refine hmul _ _ (hmul _ _ (hup _ (by simp [hX.eq])) (hlevi _ _ ?_)) (hmul _ _ (hlow _ hW) (hup _ hZ))
  exact mul_nonsing_inv _ hcT

end GlobalTheory.SpGen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticGroupGeneratedLeviLowerUnipotentWeylStatement
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplecticGroup_generated_levi_lowerUnipotent_weyl : ∀ (K : Type) [Field K] (κ : Type) [Fintype κ] [DecidableEq κ] (P : Matrix (κ ⊕ κ) (κ ⊕ κ) K → Prop),
    (∀ a b, P a → P b → P (a * b)) → (∀ g h : Matrix κ κ K, gᵀ * h = 1 → P (Matrix.fromBlocks g 0 0 h)) →
    (∀ b : Matrix κ κ K, bᵀ = b → P (Matrix.fromBlocks 1 0 b 1)) → P (Matrix.fromBlocks 0 1 (-1) 0) →
    ∀ a : Matrix (κ ⊕ κ) (κ ⊕ κ) K, aᵀ * Matrix.fromBlocks 0 1 (-1) 0 * a = Matrix.fromBlocks 0 1 (-1) 0 → P a := by
  first | exact @GlobalTheory.SpGen.symplectic_generated_levi_lower_weyl | exact GlobalTheory.SpGen.symplectic_generated_levi_lower_weyl | (intros; apply GlobalTheory.SpGen.symplectic_generated_levi_lower_weyl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasRationalWeilOperatorLeviBlock
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasRationalWeilOperatorLeviBlock
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

noncomputable section

namespace GlobalTheory.RatWeilOp

variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem levi_transpose_mul {R : Type} [CommRing R] {g h : Matrix κ κ R} (hg : gᵀ * h = 1) : hᵀ * g = 1 := by
  rw [← Matrix.transpose_transpose (hᵀ * g), Matrix.transpose_mul, Matrix.transpose_transpose, hg, Matrix.transpose_one]

theorem levi_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {g h : Matrix κ κ R} (hg : gᵀ * h = 1) :
    (g.map f)ᵀ * h.map f = 1 := by
  rw [← Matrix.transpose_map, ← Matrix.map_mul, hg, Matrix.map_one _ (map_zero f) (map_one f)]

theorem schr_mulVec_transpose {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {g h : Matrix κ κ R}
    (hg : gᵀ * h = 1) (w : (κ → R) × (κ → R)) (Φ : (κ → R) → ℂ) (x : κ → R) :
    schr ψ w Φ (hᵀ *ᵥ x) = schr ψ (g *ᵥ w.1, h *ᵥ w.2) (fun y => Φ (hᵀ *ᵥ y)) x := by
  have h1 := levi_transpose_mul hg
  have e1 : x ⬝ᵥ h *ᵥ w.2 = (hᵀ *ᵥ x) ⬝ᵥ w.2 := by rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
  have e2 : (g *ᵥ w.1) ⬝ᵥ h *ᵥ w.2 = w.1 ⬝ᵥ w.2 := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  have e3 : hᵀ *ᵥ (x + g *ᵥ w.1) = hᵀ *ᵥ x + w.1 := by
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  simp only [schr]
  rw [e1, e2, e3]

theorem funLeft_schr_levi {F R : Type} [Field F] [CommRing R] [Algebra F R] [Invertible (2 : R)] (ψ : AddChar R ℂ)
    {g h : Matrix κ κ F} (hg : gᵀ * h = 1) (w : (κ → R) × (κ → R)) (Φ : (κ → R) → ℂ) :
    LinearMap.funLeft ℂ ℂ (fun x : κ → R => hᵀ.map (algebraMap F R) *ᵥ x) (schr ψ w Φ) =
      schr ψ (act ((Matrix.fromBlocks g 0 0 h).map (algebraMap F R)) w)
        (LinearMap.funLeft ℂ ℂ (fun x : κ → R => hᵀ.map (algebraMap F R) *ᵥ x) Φ) := by
  funext x
  rw [Matrix.fromBlocks_map, act_fromBlocks, Matrix.map_zero _ (map_zero _), Matrix.zero_mulVec, Matrix.zero_mulVec,
    add_zero, zero_add, LinearMap.funLeft_apply, Matrix.transpose_map]
  exact schr_mulVec_transpose ψ (levi_map (algebraMap F R) hg) w Φ x

theorem bijOn_funLeft_homeomorph {X : Type} [TopologicalSpace X] (T : X ≃ₜ X) :
    Set.BijOn (LinearMap.funLeft ℂ ℂ T) (SB X : Set (X → ℂ)) (SB X : Set (X → ℂ)) := by
  have mem : ∀ (S : X ≃ₜ X), ∀ φ ∈ (SB X : Set (X → ℂ)), φ ∘ S ∈ (SB X : Set (X → ℂ)) :=
    fun S φ hφ => ⟨hφ.1.comp_continuous S.continuous, hφ.2.comp_homeomorph S⟩
  refine ⟨fun φ hφ => mem T φ hφ, fun φ _ ψ _ e => LinearMap.funLeft_injective_of_surjective _ _ _ T.surjective e,
    fun φ hφ => ⟨φ ∘ T.symm, mem T.symm φ hφ, ?_⟩⟩
  funext x
  simp [LinearMap.funLeft_apply]

end GlobalTheory.RatWeilOp

noncomputable section

namespace GlobalTheory.RatWeilOp

variable {κ : Type} [Fintype κ] [DecidableEq κ]

def mulVecHomeo {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (M N : Matrix κ κ R)
    (h1 : M * N = 1) (h2 : N * M = 1) : (κ → R) ≃ₜ (κ → R) where
  toFun x := M *ᵥ x
  invFun x := N *ᵥ x
  left_inv x := by simp only [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
  right_inv x := by simp only [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  continuous_toFun := continuous_const.matrix_mulVec continuous_id
  continuous_invFun := continuous_const.matrix_mulVec continuous_id

variable {F : Type} [Field F] [NumberField F]

theorem evI_algebraMap (c : F) : evI F (algebraMap F (AF F) c) = mixedEmbedding F c := by
  rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]; rfl

def evIHom : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst _ _)

theorem evIHom_apply (a : AF F) : evIHom a = evI F a := rfl

def mulVecR (M : Matrix κ κ (mixedEmbedding.mixedSpace F)) :
    (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
  (Matrix.mulVecLin M).restrictScalars ℝ

end GlobalTheory.RatWeilOp

noncomputable section

namespace GlobalTheory.RatWeilOp

variable {κ : Type} [Fintype κ] [DecidableEq κ] {F : Type} [Field F] [NumberField F]

def mulVecCLE (M N : Matrix κ κ (mixedEmbedding.mixedSpace F)) (h1 : M * N = 1) (h2 : N * M = 1) :
    (κ → mixedEmbedding.mixedSpace F) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
  (LinearEquiv.ofLinear (mulVecR M) (mulVecR N)
    (LinearMap.ext fun x => by
      simp only [mulVecR, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply,
        Matrix.mulVec_mulVec, h1, Matrix.one_mulVec, LinearMap.id_coe, id_eq])
    (LinearMap.ext fun x => by
      simp only [mulVecR, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply,
        Matrix.mulVec_mulVec, h2, Matrix.one_mulVec, LinearMap.id_coe, id_eq])).toContinuousLinearEquiv

theorem mulVecCLE_apply (M N : Matrix κ κ (mixedEmbedding.mixedSpace F)) (h1 : M * N = 1) (h2 : N * M = 1) (x) :
    mulVecCLE M N h1 h2 x = M *ᵥ x := rfl

theorem levi_map_mul {R : Type} [CommRing R] (f : F →+* R) {g h : Matrix κ κ F} (hg : gᵀ * h = 1) :
    hᵀ.map f * g.map f = 1 ∧ g.map f * hᵀ.map f = 1 := by
  have h1 := levi_transpose_mul hg
  have h2 : g * hᵀ = 1 := (Matrix.mul_eq_one_comm_of_card_eq κ κ F rfl).mp h1
  exact ⟨by rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero f) (map_one f)],
    by rw [← Matrix.map_mul, h2, Matrix.map_one _ (map_zero f) (map_one f)]⟩

theorem mulVec_mem_integers (v : Pl (F := F)) (M : Matrix κ κ (Fv F v))
    (hM : ∀ i j, M i j ∈ v.adicCompletionIntegers F) (x : κ → Fv F v) (hx : ∀ i, x i ∈ v.adicCompletionIntegers F) :
    ∀ i, (M *ᵥ x) i ∈ v.adicCompletionIntegers F :=
  fun i => sum_mem fun j _ => mul_mem (hM i j) (hx j)

end GlobalTheory.RatWeilOp

noncomputable section
namespace GlobalTheory.RatWeilOp
variable {κ : Type} [Fintype κ] [DecidableEq κ] {F : Type} [Field F] [NumberField F]

theorem ind_mulVec (v : Pl (F := F)) (M N : Matrix κ κ (Fv F v)) (hNM : N * M = 1)
    (hM : ∀ i j, M i j ∈ v.adicCompletionIntegers F) (hN : ∀ i j, N i j ∈ v.adicCompletionIntegers F) (x : κ → Fv F v) :
    ind κ v (M *ᵥ x) = ind κ v x := by
  have key : (∀ i, (M *ᵥ x) i ∈ v.adicCompletionIntegers F) ↔ ∀ i, x i ∈ v.adicCompletionIntegers F := by
    refine ⟨fun hx => ?_, mulVec_mem_integers v M hM x⟩
    have e : x = N *ᵥ (M *ᵥ x) := by rw [Matrix.mulVec_mulVec, hNM, Matrix.one_mulVec]
    rw [e]
    exact mulVec_mem_integers v N hN _ hx
  unfold ind
  by_cases hx : ∀ i, x i ∈ v.adicCompletionIntegers F
  · have hx' := (key.2 hx)
    rw [Set.indicator_of_mem (show M *ᵥ x ∈ {y : κ → Fv F v | ∀ i, y i ∈ v.adicCompletionIntegers F} from hx'),
      Set.indicator_of_mem (show x ∈ {y : κ → Fv F v | ∀ i, y i ∈ v.adicCompletionIntegers F} from hx)]
    rfl
  · have hx' : ¬ ∀ i, (M *ᵥ x) i ∈ v.adicCompletionIntegers F := fun h' => hx (key.1 h')
    rw [Set.indicator_of_notMem (show M *ᵥ x ∉ {y : κ → Fv F v | ∀ i, y i ∈ v.adicCompletionIntegers F} from hx'),
      Set.indicator_of_notMem (show x ∉ {y : κ → Fv F v | ∀ i, y i ∈ v.adicCompletionIntegers F} from hx)]
end GlobalTheory.RatWeilOp

noncomputable section
namespace GlobalTheory.RatWeilOp
variable {κ : Type} [Fintype κ] [DecidableEq κ] {F : Type} [Field F] [NumberField F]


open scoped Classical in
theorem funLeft_pure_levi {g h : Matrix κ κ F} (hI1 : hᵀ.map (mixedEmbedding F) * g.map (mixedEmbedding F) = 1)
    (hI2 : g.map (mixedEmbedding F) * hᵀ.map (mixedEmbedding F) = 1) (f : SInf F κ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ) :
    LinearMap.funLeft ℂ ℂ (fun x : κ → AF F => hᵀ.map (algebraMap F (AF F)) *ᵥ x) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (mulVecCLE _ _ hI1 hI2) f)
        (fun v => LinearMap.funLeft ℂ ℂ (fun x : κ → Fv F v => hᵀ.map (algebraMap F (Fv F v)) *ᵥ x) (φ v)) := by
  funext x
  simp only [LinearMap.funLeft_apply, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Function.comp_apply,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, mulVecCLE_apply]
  congr 1
  · congr 1
    funext i
    rw [← evIHom_apply, RingHom.map_mulVec, Matrix.map_map]
    have e : (evIHom ∘ algebraMap F (AF F)) = mixedEmbedding F := funext fun c => evI_algebraMap c
    rw [e]
    rfl
  · refine finprod_congr fun v => congrArg (φ v) (funext fun i => ?_)
    rw [← AlgHom.coe_toRingHom, RingHom.map_mulVec, Matrix.map_map]
    have e : ((evFin F v : AF F →+* Fv F v) ∘ algebraMap F (AF F)) = algebraMap F (Fv F v) :=
      funext fun c => (evFin F v).commutes c
    rw [e]
    rfl

theorem thetaSum_funLeft_levi {g h : Matrix κ κ F} (hg : gᵀ * h = 1) (Φ : (κ → AF F) → ℂ) :
    thetaSum F (LinearMap.funLeft ℂ ℂ (fun x : κ → AF F => hᵀ.map (algebraMap F (AF F)) *ᵥ x) Φ) = thetaSum F Φ := by
  simp only [thetaSum, LinearMap.funLeft_apply]
  have e : ∀ ξ : κ → F, (hᵀ.map (algebraMap F (AF F)) *ᵥ fun i => algebraMap F (AF F) (ξ i)) =
      fun i => algebraMap F (AF F) ((hᵀ *ᵥ ξ) i) := fun ξ => funext fun i => (RingHom.map_mulVec _ _ _ _).symm
  simp only [e]
  have h1 := levi_transpose_mul hg
  have h2 : g * hᵀ = 1 := (Matrix.mul_eq_one_comm_of_card_eq κ κ F rfl).mp h1
  let eq : (κ → F) ≃ (κ → F) :=
    { toFun := fun ξ => hᵀ *ᵥ ξ, invFun := fun ξ => g *ᵥ ξ,
      left_inv := fun ξ => by
        simp only [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
      right_inv := fun ξ => by
        simp only [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] }
  exact Equiv.tsum_eq eq (fun ξ : κ → F => Φ fun i => algebraMap F (AF F) (ξ i))

end GlobalTheory.RatWeilOp

noncomputable section
namespace GlobalTheory.RatWeilOp


open scoped Classical in
theorem hasOp_levi (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (κ : Type) [Fintype κ] [DecidableEq κ]
    (g h : Matrix κ κ F) (hg : gᵀ * h = 1) : HasOp ψ (Matrix.fromBlocks g 0 0 h) := by
  obtain ⟨hI1, hI2⟩ := levi_map_mul (mixedEmbedding F) hg
  have hv : ∀ v : Pl (F := F), (hᵀ.map (algebraMap F (Fv F v))) * g.map (algebraMap F (Fv F v)) = 1 ∧
      g.map (algebraMap F (Fv F v)) * hᵀ.map (algebraMap F (Fv F v)) = 1 := fun v => levi_map_mul _ hg
  refine ⟨LinearMap.funLeft ℂ ℂ (fun x : κ → AF F => hᵀ.map (algebraMap F (AF F)) *ᵥ x), 1,
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (mulVecCLE _ _ hI1 hI2),
    fun v => LinearMap.funLeft ℂ ℂ (fun x : κ → Fv F v => hᵀ.map (algebraMap F (Fv F v)) *ᵥ x),
    one_ne_zero, ?_, fun v => bijOn_funLeft_homeomorph (mulVecHomeo _ _ (hv v).1 (hv v).2),
    fun v w φ _ => funLeft_schr_levi _ hg w φ, ?_, fun f φ _ =>
      ⟨funLeft_pure_levi hI1 hI2 f φ, fun w => funLeft_schr_levi ψ hg w _, by rw [thetaSum_funLeft_levi hg, one_mul]⟩⟩
  · intro f
    refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (mulVecCLE _ _ hI1 hI2).symm f, ?_⟩
    refine DFunLike.ext _ _ fun x => ?_
    simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
      ContinuousLinearEquiv.symm_apply_apply]
  · have hint : ∀ᶠ v : Pl F in cofinite, ∀ i j, algebraMap F (Fv F v) (h i j) ∈ v.adicCompletionIntegers F ∧
        algebraMap F (Fv F v) (g i j) ∈ v.adicCompletionIntegers F :=
      eventually_all.2 fun i => eventually_all.2 fun j =>
        (eventually_algebraMap_mem_integers _).and (eventually_algebraMap_mem_integers _)
    filter_upwards [hint] with v hv'
    funext x
    exact ind_mulVec v _ _ (hv v).2 (fun i j => (hv' j i).1) (fun i j => (hv' i j).2) x

end GlobalTheory.RatWeilOp
end
end
end
end
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasRationalWeilOperatorLeviBlockStatement
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasRationalWeilOperator_leviBlock : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (κ : Type) [Fintype κ] [DecidableEq κ] (g h : Matrix κ κ F), gᵀ * h = 1 →
    HasOp ψ (Matrix.fromBlocks g 0 0 h) := by
  first | exact @GlobalTheory.RatWeilOp.hasOp_levi | exact GlobalTheory.RatWeilOp.hasOp_levi | (intros; apply GlobalTheory.RatWeilOp.hasOp_levi <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticChangeOfGoodModelsIntertwines
noncomputable section

namespace GlobalTheory.RatWeilOp

open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F : Type} [Field F] [NumberField F]

theorem hasOp_of_symplectic (hF : IsTotallyReal F) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {κ : Type} [Fintype κ] [DecidableEq κ]
    (a : Matrix (κ ⊕ κ) (κ ⊕ κ) F) (ha : aᵀ * Matrix.fromBlocks 0 1 (-1) 0 * a = Matrix.fromBlocks 0 1 (-1) 0) : HasOp ψ a :=
  GlobalTheory.T.symplecticGroup_generated_levi_lowerUnipotent_weyl F κ (HasOp ψ) (fun _ _ => HasOp.mul) (GlobalTheory.T.hasRationalWeilOperator_leviBlock F ψ κ) (GlobalTheory.T.lowerUnipotent_hasRationalWeilOperator_quadraticChar F ψ hψ κ) (GlobalTheory.T.weylElement_hasRationalWeilOperator_adelicFourier F hF ψ hψ κ) a ha

section Pure

variable {κ : Type} [Fintype κ]

theorem pure_mem (f : SInf F κ) {φ : ∀ v : Pl F, (κ → Fv F v) → ℂ} (hφ : IsFam φ) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ schA F κ :=
  Submodule.subset_span ⟨f, fun y => ∏ᶠ v, φ v fun i => evalV F v (y i),
    ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV φ hφ.1 hφ.2, GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ hφ.1 hφ.2⟩, rfl⟩

theorem schA_le {N : Submodule ℂ ((κ → AF F) → ℂ)} (h : ∀ f φ, IsFam φ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ N) : schA F κ ≤ N := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, g, hg, rfl⟩
  replace hg := GlobalTheory.T.schwartzBruhat_finiteAdeles_mem_span_restrictedProducts F _ g hg
  induction hg using Submodule.span_induction with
  | zero => rw [show pureA F f 0 = 0 from funext fun _ => mul_zero _]; exact N.zero_mem
  | add a b _ _ ha hb =>
    rw [show pureA F f (a + b) = pureA F f a + pureA F f b from funext fun _ => mul_add _ _ _]; exact N.add_mem ha hb
  | smul c a _ ha =>
    rw [show pureA F f (c • a) = c • pureA F f a from funext fun _ => mul_left_comm _ _ _]; exact N.smul_mem c ha
  | mem p hp =>
    obtain ⟨φ, hφ, hs, rfl⟩ := hp
    exact h f φ ⟨hφ, hs⟩

theorem IsFam.finite {φ : ∀ v : Pl F, (κ → Fv F v) → ℂ} (hφ : IsFam φ) (x : κ → AF F) :
    (Function.mulSupport fun v => φ v fun i => evFin F v (x i)).Finite := by
  have h : ∀ᶠ v in cofinite, ∀ i, evFin F v (x i) ∈ v.adicCompletionIntegers F := eventually_all.2 fun i => (x i).2.2
  refine (eventually_cofinite.1 ?_)
  filter_upwards [h, hφ.2] with v h1 h2
  rw [h2, ind, Set.indicator_of_mem (show _ ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from h1)]
  rfl

theorem pure_smul (f : SInf F κ) {φ : ∀ v : Pl F, (κ → Fv F v) → ℂ} (hφ : IsFam φ) (m : Pl F → ℂ) (h0 : ∀ v, m v ≠ 0)
    (h1 : ∀ᶠ v in cofinite, m v = 1) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure ((∏ᶠ v, m v) • f) (fun v => (m v)⁻¹ • φ v) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
  funext x
  have hm : (Function.mulSupport m).Finite := eventually_cofinite.1 h1
  have hm' : (Function.mulSupport fun v => (m v)⁻¹).Finite := hm.subset fun v hv h => hv (by simp only [h, inv_one])
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Pi.smul_apply, smul_eq_mul, SchwartzMap.smul_apply]
  rw [finprod_mul_distrib hm' (hφ.finite x)]
  have : (∏ᶠ v, m v) * ∏ᶠ v, (m v)⁻¹ = 1 := by
    rw [← finprod_mul_distrib hm hm']
    exact finprod_eq_one_of_forall_eq_one fun v => mul_inv_cancel₀ (h0 v)
  linear_combination (f (fun i => evI F (x i)) * ∏ᶠ v, φ v fun i => evFin F v (x i)) * this

def schrL {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) (w : (κ → R) × (κ → R)) :
    ((κ → R) → ℂ) →ₗ[ℂ] (κ → R) → ℂ where
  toFun := schr ψ w
  map_add' φ φ' := funext fun x => by simp only [schr, Pi.add_apply]; ring
  map_smul' a φ := funext fun x => by simp only [schr, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

variable {ψ : AddChar (AF F) ℂ} {a : Matrix (κ ⊕ κ) (κ ⊕ κ) F} {e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ → AF F) → ℂ} {c : ℂ}
  {ei : SInf F κ →L[ℂ] SInf F κ} {ev : ∀ v : Pl F, ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ}

theorem IsOp.maps (h : IsOp ψ a e c ei ev) : ∀ Φ ∈ schA F κ, e Φ ∈ schA F κ := fun _ hΦ =>
  schA_le (N := (schA F κ).comap e) (fun f φ hφ => by
    rw [Submodule.mem_comap, (h.2.2.2.2.2 f φ hφ).1]
    exact pure_mem _ (h.isFam hφ)) hΦ

theorem IsOp.Heisenberg₂ (h : IsOp ψ a e c ei ev) (w : (κ → AF F) × (κ → AF F)) :
    ∀ Φ ∈ schA F κ, e (schr ψ w Φ) = schr ψ (act (a.map (algebraMap F (AF F))) w) (e Φ) := fun _ hΦ =>
  schA_le (N := LinearMap.eqLocus (e ∘ₗ schrL ψ w) (schrL ψ (act (a.map (algebraMap F (AF F))) w) ∘ₗ e))
    (fun f φ hφ => (h.2.2.2.2.2 f φ hφ).2.1 w) hΦ

theorem IsOp.theta (h : IsOp ψ a e c ei ev) : ∀ Φ ∈ schA F κ, thetaSum F (e Φ) = c * thetaSum F Φ := fun _ hΦ =>
  (schA_le (N := {
      carrier := {Φ | Φ ∈ schA F κ ∧ thetaSum F (e Φ) = c * thetaSum F Φ}
      zero_mem' := ⟨zero_mem _, by simp [thetaSum]⟩
      add_mem' := fun {x y} hx hy => ⟨add_mem hx.1 hy.1, by
        rw [map_add (f := _), thetaSum_add F (h.maps _ hx.1) (h.maps _ hy.1), thetaSum_add F hx.1 hy.1, hx.2, hy.2, mul_add]⟩
      smul_mem' := fun r x hx => ⟨Submodule.smul_mem _ r hx.1, by
        rw [map_smul, thetaSum_smul, thetaSum_smul, hx.2, mul_left_comm]⟩ })
    (fun f φ hφ => ⟨pure_mem f hφ, (h.2.2.2.2.2 f φ hφ).2.2⟩) hΦ).2

theorem IsOp.bijOn (hψ : IsStd ψ) (h : IsOp ψ a e c ei ev) : Set.BijOn e (schA F κ : Set _) (schA F κ : Set _) := by
  classical
  refine ⟨h.maps, fun Φ hΦ Φ' hΦ' he => ?_, ?_⟩
  · have hd : Φ - Φ' ∈ schA F κ := sub_mem hΦ hΦ'
    refine sub_eq_zero.1 (GlobalTheory.T.eq_zero_of_schroedingerTranslates_thetaSum_zero F ψ hψ κ _ hd fun w => ?_)
    have h1 := h.theta _ (GlobalTheory.HeisSchA.schr_mem_schA ψ hψ w _ hd)
    rw [h.Heisenberg₂ w _ hd, map_sub, he, sub_self, show schr ψ _ (0 : (κ → AF F) → ℂ) = 0 from (schrL ψ _).map_zero] at h1
    exact (mul_eq_zero.1 (h1.symm.trans (by simp [thetaSum]))).resolve_left h.1
  · refine schA_le (N := (schA F κ).map e) fun g φ' hφ' => ?_
    obtain ⟨f, rfl⟩ := h.2.1 g
    have key : ∀ v, ∃ p ∈ SB (κ → Fv F v), ev v p = φ' v ∧ (φ' v = ind κ v → ev v (ind κ v) = ind κ v → p = ind κ v) := by
      intro v
      by_cases hv : φ' v = ind κ v ∧ ev v (ind κ v) = ind κ v
      · exact ⟨ind κ v, hv.1 ▸ hφ'.1 v, hv.2.trans hv.1.symm, fun _ _ => rfl⟩
      · obtain ⟨p, hp, hp'⟩ := (h.2.2.1 v).surjOn (hφ'.1 v)
        exact ⟨p, hp, hp', fun h1 h2 => absurd ⟨h1, h2⟩ hv⟩
    choose φ h1 h2 h3 using key
    have hφ : IsFam φ := ⟨h1, by filter_upwards [hφ'.2, h.2.2.2.2.1] with v p q using h3 v p q⟩
    exact ⟨_, pure_mem f hφ, by rw [(h.2.2.2.2.2 f φ hφ).1]; simp only [h2]⟩

end Pure

section Vac

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem schr_of_acts (M : Model σ X W) (ψ : AddChar (AF F) ℂ) {v : Pl F} {γ : Matrix (Fin n) (Fin d) (AE F E)} (hγ : γ ∈ latAtV X W v)
    {φ : (Fin n × Fin d → Fv F v) → ℂ} (hφ : φ ∈ SB _) {χ : ℂ} (h : Acts (evFin F v) (M.co.rho ψ γ) φ (χ • φ)) :
    schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo M.co v γ) φ = χ • φ := by
  obtain ⟨r, hr, x₀, hx₀⟩ := GlobalTheory.RestComplement.exists_rest_ne_zero v φ hφ
  funext ξ
  have := GlobalTheory.LatVac.heis_at_local_identity v M.co ψ γ φ χ ((GlobalTheory.LatVac.latAtV_at_stable X W v).1 γ hγ) h r hr x₀ hx₀ ξ
  rw [schr, invOf_eq_inv]
  exact this

theorem vac_line (B : Base F E) {r s r' s' : ℕ} (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s')
    (M : Model σ X W) (v : Pl F) {φ φ' : (Fin n × Fin d → Fv F v) → ℂ} (h : M.IsVac B.ψ v φ) (h' : M.IsVac B.ψ v φ') :
    ∃ m : ℂ, φ' = m • φ := by
  classical
  obtain ⟨hφ, hφ0, θ, hθ, hA⟩ := h
  obtain ⟨hφ', -, θ', hθ', hA'⟩ := h'
  have hAt := (GlobalTheory.LatVac.latAtV_at_stable X W v).1
  let χ : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) → ℂ := fun l =>
    if h : ∃ γ ∈ latAtV X W v, GlobalTheory.LatVac.locCo M.co v γ = l then
      B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) h.choose h.choose) else 0
  have loc : ∀ f : (Fin n × Fin d → Fv F v) → ℂ, f ∈ SB _ →
      (∀ γ ∈ latAtV X W v, Acts (evFin F v) (M.co.rho B.ψ γ) f
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) γ γ) • f)) →
      ∀ l ∈ (latAtV X W v).map (GlobalTheory.LatVac.locCo M.co v), ∀ ξ,
        GlobalTheory.LatVac.psiAt B.ψ v (ξ ⬝ᵥ l.2 + (2 : Fv F v)⁻¹ * (l.1 ⬝ᵥ l.2)) * f (ξ + l.1) = χ l * f ξ := by
    intro f hf hA l hl ξ
    have h : ∃ γ ∈ latAtV X W v, GlobalTheory.LatVac.locCo M.co v γ = l := AddSubgroup.mem_map.mp hl
    have key := congrFun (schr_of_acts M B.ψ h.choose_spec.1 hf (hA _ h.choose_spec.1)) ξ
    simp only [χ, dif_pos h]
    rw [h.choose_spec.2, schr, invOf_eq_inv] at key
    exact key
  obtain ⟨c, hc0, hcb⟩ := GlobalTheory.LatBound.locCo_latAtV_bounded X W v M.co hX.lat.toIsLattice hW.lat.toIsLattice
  have hsd := GlobalTheory.LatVac.DualLoc.map_selfDual v M.co B.ψ _ hAt (GlobalTheory.T.heisenbergLattice_selfDual_every_finitePlace F E σ B n d X W r s r' s' hB hX hW v)
  have hfill := GlobalTheory.T.self_dual_lattice_invariant_vector F v _ (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.VacAny.continuous_psiV hB.std.1 v)
    (fun _ => GlobalTheory.StdCharFromIsStd.norm_psi hB.std _) (GlobalTheory.PsiNontriv.psiAt_ne_one B.ψ hB.std v) _ c hc0 hsd
    (fun l hl i => by
      obtain ⟨γ, hγ, rfl⟩ := AddSubgroup.mem_map.mp hl
      exact hcb γ hγ i)
  refine GlobalTheory.heisenbergEigen_proportional (GlobalTheory.LatVac.psiAt B.ψ v) _ χ φ φ' (loc φ hφ hA) (loc φ' hφ' fun γ hγ => ?_) hφ0 hfill
  have heq := GlobalTheory.T.vacuum_eigenvalue_theta_independent F E σ B n d X W r s r' s' hB hX hW v θ θ' hθ hθ' γ hγ
  change B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) γ γ) =
    B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ' : E)) (incM F X.J) (incM F W.J) γ γ) at heq
  rw [heq]
  exact hA' γ hγ

theorem IsOp.isVac {ψ : AddChar (AF F) ℂ} {a e c ei ev} (h : IsOp (κ := Fin n × Fin d) ψ a e c ei ev) (M M₁ : Model σ X W)
    (hco : ∀ u, M₁.co.e u = act (a.map (algebraMap F (AF F))) (M.co.e u)) (v : Pl F) {φ : (Fin n × Fin d → Fv F v) → ℂ}
    (hφ : M.IsVac ψ v φ) : M₁.IsVac ψ v (ev v φ) := by
  obtain ⟨h1, h0, θ, hθ, hA⟩ := hφ
  refine ⟨(h.2.2.1 v).mapsTo h1, fun h2 => h0 ((h.2.2.1 v).injOn h1 (zero_mem _) (h2.trans (map_zero _).symm)), θ, hθ,
    fun γ hγ => ?_⟩
  have e1 : GlobalTheory.LatVac.locCo M₁.co v γ = act (a.map (algebraMap F (Fv F v))) (GlobalTheory.LatVac.locCo M.co v γ) := by
    have e2 : ∀ k, evFin F v ((a.map (algebraMap F (AF F)) *ᵥ Sum.elim (M.co.e γ).1 (M.co.e γ).2) k) =
        (a.map (algebraMap F (Fv F v)) *ᵥ Sum.elim (GlobalTheory.LatVac.locCo M.co v γ).1 (GlobalTheory.LatVac.locCo M.co v γ).2) k := fun k => by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, AlgHom.commutes]
      refine Finset.sum_congr rfl fun j _ => ?_
      cases j <;> rfl
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
    · show evFin F v ((M₁.co.e γ).1 k) = _
      rw [hco]; exact e2 _
    · show evFin F v ((M₁.co.e γ).2 k) = _
      rw [hco]; exact e2 _
  have e3 := GlobalTheory.VacBridge.rho_acts_locCo M₁.co ψ v γ ((GlobalTheory.LatVac.latAtV_at_stable X W v).1 γ hγ) (ev v φ)
  rwa [e1, ← h.2.2.2.1 v _ φ h1, schr_of_acts M ψ hγ h1 (hA γ hγ), map_smul] at e3

end Vac

theorem exists_intertwiner : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M M₁ : Model σ X W) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ → M₁.IsGood B.ψ → ∀ a : Matrix ((Fin n × Fin d) ⊕ (Fin n × Fin d)) ((Fin n × Fin d) ⊕ (Fin n × Fin d)) F, aᵀ * Matrix.fromBlocks 0 1 (-1) 0 * a = Matrix.fromBlocks 0 1 (-1) 0 → (∀ u, M₁.co.e u = ((a.map (algebraMap F (AF F)) *ᵥ Sum.elim (M.co.e u).1 (M.co.e u).2) ∘ Sum.inl, (a.map (algebraMap F (AF F)) *ᵥ Sum.elim (M.co.e u).1 (M.co.e u).2) ∘ Sum.inr)) → ∃ (e : Fn F n d →ₗ[ℂ] Fn F n d) (c : ℂ), c ≠ 0 ∧ IsEv B M M₁ 1 1 ∅ e ∧ Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) ∧ ∀ Φ ∈ schA F (Fin n × Fin d), thetaSum F (e Φ) = c * thetaSum F Φ := by
  intro _ F E _ _ _ _ _ σ B n d X W M M₁ r s r' s' hB hX hW hM hM₁ a ha hco
  obtain ⟨e, c, ei, ev, h⟩ := hasOp_of_symplectic hB.cm.1 hB.std a ha
  have key : ∀ v, ∃ m : ℂ, m ≠ 0 ∧ ev v (M.vac v) = m • M₁.vac v ∧ (ev v (M.vac v) = M₁.vac v → m = 1) := fun v => by
    by_cases hv : ev v (M.vac v) = M₁.vac v
    · exact ⟨1, one_ne_zero, by rw [hv, one_smul], fun _ => rfl⟩
    · have h1 := h.isVac M M₁ hco v (hM.vac v)
      obtain ⟨m, hm⟩ := vac_line B hB hX hW M₁ v (hM₁.vac v) h1
      exact ⟨m, fun h0 => h1.2.1 (by rw [hm, h0, zero_smul]), hm, fun h2 => absurd h2 hv⟩
  choose m hm0 hm hm1 using key
  have hmc : ∀ᶠ v in cofinite, m v = 1 := by
    filter_upwards [hM.std, hM₁.std, h.2.2.2.2.1] with v h1 h2 h3
    exact hm1 v (by rw [h1, h2]; exact h3)
  have hP : (∏ᶠ v, m v) ≠ 0 := finprod_induction (fun z : ℂ => z ≠ 0) one_ne_zero (fun _ _ => mul_ne_zero) hm0
  refine ⟨e, c, h.1, ⟨h.maps, fun z Φ hΦ => ?_, fun u hu => absurd hu (Set.notMem_empty u),
    (∏ᶠ v, m v) • ei, fun v => (m v)⁻¹ • ev v, fun h0 => ?_, fun v => ⟨?_, ?_⟩, fun f φ h1 h2 => ?_⟩, h.bijOn hB.std, h.theta⟩
  · have h1 : ∀ k : ℕ, incM F (1 : Matrix (Fin k) (Fin k) E) = 1 := fun k => Matrix.map_one _ (map_zero _) (map_one _)
    rw [h1, h1, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, Darboux.rho, Darboux.rho, hco]
    exact h.Heisenberg₂ _ Φ hΦ
  · have h1 : ei = 0 := (smul_eq_zero.1 h0).resolve_left hP
    obtain ⟨Φ, hΦ, hΦ0⟩ := GlobalTheory.SchANonzero.exists_mem_schA_ne_zero F (Fin n × Fin d)
    have h2 : schA F (Fin n × Fin d) ≤ ⊥ := schA_le fun g φ _ => by
      obtain ⟨f, rfl⟩ := h.2.1 g
      rw [h1, Submodule.mem_bot]
      funext x
      simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
    exact hΦ0 (by rw [(Submodule.mem_bot ℂ).1 (h2 hΦ)]; rfl)
  · rw [LinearMap.smul_apply, hm, smul_smul, inv_mul_cancel₀ (hm0 v), one_smul]
  · rw [Submodule.map_smul _ _ _ (inv_ne_zero (hm0 v))]
    exact SetLike.coe_injective ((Submodule.map_coe _ _).trans (h.2.2.1 v).image_eq)
  · have hφ : IsFam φ := ⟨h1, by filter_upwards [h2, hM.std] with v p q using p.trans q⟩
    rw [(h.2.2.2.2.2 f φ hφ).1, ← pure_smul (ei f) (h.isFam hφ) m hm0 hmc]
    rfl

end GlobalTheory.RatWeilOp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticChangeOfGoodModelsIntertwinesStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplectic_change_of_good_models_intertwines : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M M₁ : Model σ X W) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ → M₁.IsGood B.ψ → ∀ a : Matrix ((Fin n × Fin d) ⊕ (Fin n × Fin d)) ((Fin n × Fin d) ⊕ (Fin n × Fin d)) F, aᵀ * Matrix.fromBlocks 0 1 (-1) 0 * a = Matrix.fromBlocks 0 1 (-1) 0 → (∀ u, M₁.co.e u = ((a.map (algebraMap F (AF F)) *ᵥ Sum.elim (M.co.e u).1 (M.co.e u).2) ∘ Sum.inl, (a.map (algebraMap F (AF F)) *ᵥ Sum.elim (M.co.e u).1 (M.co.e u).2) ∘ Sum.inr)) → ∃ (e : Fn F n d →ₗ[ℂ] Fn F n d) (c : ℂ), c ≠ 0 ∧ IsEv B M M₁ 1 1 ∅ e ∧ Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) ∧ ∀ Φ ∈ schA F (Fin n × Fin d), thetaSum F (e Φ) = c * thetaSum F Φ := by
  first | exact @GlobalTheory.RatWeilOp.exists_intertwiner | exact GlobalTheory.RatWeilOp.exists_intertwiner | (intros; apply GlobalTheory.RatWeilOp.exists_intertwiner <;> assumption)
end
