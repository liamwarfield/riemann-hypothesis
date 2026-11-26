module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoBarZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuumEquationsInArchimedeanDarbouxCoordinat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilIntegralPointSkewLatticeUnitVectorSameEigen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGramMatricesCmUnitaryShimuraObject
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonsplitCentraliserNormElement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePlaceComponentAdeleNormEqLocalNorm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePlaceComponentAdeleNormEqLocalNorm
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.NormAtPlace

theorem evFin_norm_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl (F := F)) (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
    evFin F v (Algebra.norm (AF F) x) = Algebra.norm (Fv F v) (compFin F E v x) := by
  intro F E _ _ _ _ _ v x
  classical
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let e := Module.finBasis F E
  let b := Algebra.TensorProduct.basis (AF F) e
  let b' := Algebra.TensorProduct.basis (Fv F v) e
  have hrepr : ∀ (z : AF F ⊗[F] E) i, b'.repr (compFin F E v z) i = evFin F v (b.repr z i) := by
    intro z i
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a y =>
      simp only [compFin, b, b', AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply, Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply,
        smul_eq_mul, map_mul, AlgHom.commutes]
    | add y z hy hz => simp only [map_add (f := _), Finsupp.add_apply, hy, hz]
  have hb : ∀ j, compFin F E v (b j) = b' j := by
    intro j
    simp [compFin, b, b', Algebra.TensorProduct.basis_apply]
  have hmat : Algebra.leftMulMatrix b' (compFin F E v x) = (Algebra.leftMulMatrix b x).map (evFin F v) := by
    ext i j
    rw [Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
      ← hb j, ← map_mul, hrepr]
  rw [Algebra.norm_eq_matrix_det b', Algebra.norm_eq_matrix_det b, hmat]
  exact AlgHom.map_det (evFin F v) (Algebra.leftMulMatrix b x)

end GlobalTheory.NormAtPlace
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePlaceComponentAdeleNormEqLocalNormStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finitePlaceComponent_adeleNorm_eq_localNorm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl (F := F)) (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
    evFin F v (Algebra.norm (AF F) x) = Algebra.norm (Fv F v) (compFin F E v x) := by
  first | exact @GlobalTheory.NormAtPlace.evFin_norm_eq | exact GlobalTheory.NormAtPlace.evFin_norm_eq | (intros; apply GlobalTheory.NormAtPlace.evFin_norm_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelParabolicLeviInverseQuotientDetNorm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelParabolicLeviInverseQuotientDetNorm
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.InertLagLevi

theorem det_sub_one_ann {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι] (e : R)
    (M : Matrix ι ι R) (h : ∀ i j, e * (M i j - (1 : Matrix ι ι R) i j) = 0) : e * (M.det - 1) = 0 := by
  set I : Ideal R := (Submodule.span R {e}).annihilator
  have hI : ∀ a, a ∈ I ↔ a * e = 0 := fun a => by
    rw [Submodule.mem_annihilator_span_singleton, smul_eq_mul]
  have h1 : (Ideal.Quotient.mk I).mapMatrix M = 1 := by
    ext i j
    rw [← map_one (Ideal.Quotient.mk I).mapMatrix, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply,
      Matrix.map_apply, Matrix.map_apply, Ideal.Quotient.eq, hI, mul_comm]
    exact h i j
  have h2 := congrArg Matrix.det h1
  rw [← RingHom.map_det, Matrix.det_one, ← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq, hI] at h2
  rw [mul_comm]; exact h2

end GlobalTheory.InertLagLevi

open GlobalTheory.InertLagLevi in
theorem GlobalTheory.InertLagLevi.levi_det : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), J.det ≠ 0 →
    ∀ (v : Pl (F := F)) (p : UG (cA σ) (dbl (incM F J))) (t : GL (Fin n) (AE F E)), At (evFin F v) ((p.1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) - 1) →
    (p.1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) * diagCols (Fin n) = diagCols (Fin n) * t.val →
    At (evFin F v) (t.val.det - 1) ∧ At (evFin F v) (Algebra.norm (AF F) t.val.det - 1) ∧
      ∃ s : GL (Fin n) (AE F E), s.val = ((p⁻¹).1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)).toBlocks₁₁ - ((p⁻¹).1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)).toBlocks₂₁ ∧
        Algebra.norm (AF F) s.val.det = Algebra.norm (AF F) t.val.det := by
  intro F E _ _ _ _ _ σ hσ n J hJ v p t hsupp hpt
  set P : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E) := p.1.1 with hP
  set Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E) := (p⁻¹).1.1 with hQ
  set D : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E) := diagCols (Fin n) with hD
  set T := t.val with hT
  set Ti := (t⁻¹).val with hTi
  have hTTi : T * Ti = 1 := by simp [T, Ti]
  have hQP : Q * P = 1 := by simp [Q, P]

  have htsupp : ∀ u : AF F, evFin F v u = 0 → u • (T - 1) = 0 := by
    intro u hu
    have h0 : u • (P - 1) = 0 := hsupp u hu
    have h1 : u • (P * D - D) = 0 := by
      rw [show P * D - D = (P - 1) * D by rw [Matrix.sub_mul, Matrix.one_mul], ← Matrix.smul_mul, h0, Matrix.zero_mul]
    rw [show P * D = D * T from hpt, show D * T - D = Matrix.fromRows (T - 1) (T - 1) by
      ext (i|i) j <;> simp [D, diagCols, Matrix.fromRows_mul]] at h1
    ext i j
    have := congrFun (congrFun h1 (Sum.inl i)) j
    simpa using this
  have hdet : ∀ u : AF F, evFin F v u = 0 → u • (T.det - 1) = 0 := by
    intro u hu
    have h := htsupp u hu
    rw [Algebra.smul_def]
    refine det_sub_one_ann _ T fun i j => ?_
    have := congrFun (congrFun h i) j
    rwa [Matrix.smul_apply, Matrix.sub_apply, Algebra.smul_def] at this
  refine ⟨hdet, ?_, ?_⟩
  · intro u hu
    have hz := hdet u hu
    let b := Module.Free.chooseBasis (AF F) (AE F E)
    rw [Algebra.norm_eq_matrix_det b, smul_eq_mul]
    refine det_sub_one_ann _ _ fun i j => ?_
    rw [← Matrix.sub_apply, ← map_one (Algebra.leftMulMatrix b), ← map_sub, Algebra.leftMulMatrix_eq_repr_mul,
      ← smul_eq_mul, ← Finsupp.smul_apply, ← map_smul, ← smul_mul_assoc, hz, zero_mul, map_zero, Finsupp.zero_apply]
  · have hpt' : P * D = D * T := hpt
    set K : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E) := Matrix.fromRows 1 (-1) with hKdef
    have hq : Qᵀ * dbl (incM F J) * Q.map (cA σ) = dbl (incM F J) := (p⁻¹).2
    have hQD : Q * D = D * Ti := by
      calc Q * D = Q * (D * T * Ti) := by rw [Matrix.mul_assoc D, hTTi, Matrix.mul_one]
        _ = Q * P * D * Ti := by
          rw [Matrix.mul_assoc Q P D, hpt']; simp only [Matrix.mul_assoc]
        _ = D * Ti := by rw [hQP, Matrix.one_mul]
    have hDc : D.map (cA σ) = D := by
      simp only [D, diagCols, Matrix.fromRows_map, Matrix.map_one _ (map_zero (cA σ)) (map_one (cA σ))]
    have hK : dbl (incM F J) * D = K * incM F J := by
      simp only [dbl, D, diagCols, Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul]
      simp [K, Matrix.fromRows_mul]
    have h2 : Qᵀ * (K * incM F J) * Ti.map (cA σ) = K * incM F J := by
      rw [← hK]
      calc Qᵀ * (dbl (incM F J) * D) * Ti.map (cA σ)
          = Qᵀ * dbl (incM F J) * (D.map (cA σ) * Ti.map (cA σ)) := by rw [hDc]; simp only [Matrix.mul_assoc]
        _ = Qᵀ * dbl (incM F J) * (Q.map (cA σ) * D.map (cA σ)) := by
          have hm1 : (Q * D).map (cA σ) = Q.map (cA σ) * D.map (cA σ) := Matrix.map_mul (f := (cA σ).toRingHom)
          have hm2 : (D * Ti).map (cA σ) = D.map (cA σ) * Ti.map (cA σ) := Matrix.map_mul (f := (cA σ).toRingHom)
          rw [← hm1, ← hm2, hQD]
        _ = dbl (incM F J) * D := by rw [hDc, ← Matrix.mul_assoc, hq]
    set X := Q.toBlocks₁₁ - Q.toBlocks₂₁ with hX
    have hQK : Qᵀ * K = Matrix.fromRows Xᵀ (Q.toBlocks₁₂ - Q.toBlocks₂₂)ᵀ := by
      rw [hKdef, ← Matrix.transpose_transpose (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1)),
        ← Matrix.transpose_mul, Matrix.transpose_fromRows]
      conv_lhs => rw [← Matrix.fromBlocks_toBlocks Q]
      rw [Matrix.fromCols_mul_fromBlocks, Matrix.transpose_fromCols]
      simp [X, sub_eq_add_neg]
    rw [← Matrix.mul_assoc, hQK, hKdef, Matrix.fromRows_mul, Matrix.fromRows_mul, Matrix.fromRows_mul] at h2
    have h3 : Xᵀ * incM F J * Ti.map (cA σ) = incM F J := by
      have := (Matrix.fromRows_inj h2).1
      rw [this, Matrix.one_mul]
    have hdJ : (incM F J).det = inclR (AF F) J.det := (RingHom.map_det _ J).symm
    have hJu : IsUnit (incM F J).det := hdJ ▸ (Ne.isUnit hJ).map _
    have hdTi : (Ti.map (cA σ)).det = cA σ Ti.det := (AlgHom.map_det (cA σ) Ti).symm
    have hx : X.det * cA σ Ti.det = 1 := by
      have := congrArg Matrix.det h3
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hdTi, mul_right_comm] at this
      exact (hJu.mul_left_inj).1 (this.trans (one_mul _).symm)
    have hTd : T.det * Ti.det = 1 := by rw [← Matrix.det_mul, hTTi, Matrix.det_one]
    have hXd : X.det = cA σ T.det := by
      calc X.det = X.det * (cA σ Ti.det * cA σ T.det) := by
            rw [← map_mul, mul_comm Ti.det, hTd, map_one, mul_one]
        _ = (X.det * cA σ Ti.det) * cA σ T.det := by ring
        _ = cA σ T.det := by rw [hx, one_mul]
    refine ⟨Matrix.nonsingInvUnit X (isUnit_iff_exists_inv.mpr ⟨_, hx⟩), rfl, ?_⟩
    show Algebra.norm (AF F) X.det = _
    have hcc : ∀ x, cA σ (cA σ x) = x := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [cA, GlobalTheory.AdelicU.cm_conj_conj hσ]
      | add x y hx hy => simp [hx, hy]
    let cE : AE F E ≃ₐ[AF F] AE F E := AlgEquiv.ofAlgHom (cA σ) (cA σ) (AlgHom.ext hcc) (AlgHom.ext hcc)
    rw [hXd]
    exact Algebra.norm_eq_of_algEquiv cE T.det
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelParabolicLeviInverseQuotientDetNormStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelParabolic_leviInverse_quotient_det_norm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), J.det ≠ 0 →
    ∀ (v : Pl (F := F)) (p : UG (cA σ) (dbl (incM F J))) (t : GL (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), At (evFin F v) ((p.1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1) →
    (p.1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * diagCols (Fin n) = diagCols (Fin n) * t.val →
    At (evFin F v) (t.val.det - 1) ∧ At (evFin F v) (Algebra.norm (AF F) t.val.det - 1) ∧
      ∃ s : GL (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), s.val = ((p⁻¹).1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))).toBlocks₁₁ - ((p⁻¹).1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))).toBlocks₂₁ ∧
        Algebra.norm (AF F) s.val.det = Algebra.norm (AF F) t.val.det := by
  first | exact @GlobalTheory.InertLagLevi.levi_det | exact GlobalTheory.InertLagLevi.levi_det | (intros; apply GlobalTheory.InertLagLevi.levi_det <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformRationalTranslateQuasiInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformRationalTranslateQuasiInvariant
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThetaQuasiRat

theorem schr_schr {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (w w' : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) :
    GlobalTheory.WeilM.schr ψ w (GlobalTheory.WeilM.schr ψ w' φ) =
      ψ (⅟(2 : R) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)) • GlobalTheory.WeilM.schr ψ (w + w') φ := by
  funext x
  simp only [GlobalTheory.WeilM.schr, Pi.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add, add_assoc, ← mul_assoc,
    ← AddChar.map_add_eq_mul, add_dotProduct, dotProduct_add]
  congr 2
  have h : ⅟(2 : R) * 2 = 1 := invOf_mul_self 2
  linear_combination (-(w.1 ⬝ᵥ w'.2)) * h

theorem thetaSum_smul' (F : Type) [Field F] [NumberField F] {κ : Type} (c : ℂ) (φ : (κ → AdeleRing (𝓞 F) F) → ℂ) :
    GlobalTheory.WeilM.thetaSum F (c • φ) = c * GlobalTheory.WeilM.thetaSum F φ := by
  simp only [GlobalTheory.WeilM.thetaSum, Pi.smul_apply, smul_eq_mul, tsum_mul_left]

theorem thetaSum_schr_rat (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : ∀ a : F, ψ (algebraMap F (AdeleRing (𝓞 F) F) a) = 1)
    {κ : Type} [Fintype κ] (y z : κ → F) (φ : (κ → AdeleRing (𝓞 F) F) → ℂ) :
    GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ
      (fun i => algebraMap F (AdeleRing (𝓞 F) F) (y i), fun i => algebraMap F (AdeleRing (𝓞 F) F) (z i)) φ) =
      GlobalTheory.WeilM.thetaSum F φ := by
  have h2 : ⅟(2 : AdeleRing (𝓞 F) F) = algebraMap F (AdeleRing (𝓞 F) F) (1 / 2) := by
    apply invOf_eq_right_inv
    rw [← map_ofNat (algebraMap F (AdeleRing (𝓞 F) F)) 2, ← map_mul]
    norm_num
  have key : ∀ ξ : κ → F, ψ ((fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) ⬝ᵥ
      (fun i => algebraMap F (AdeleRing (𝓞 F) F) (z i)) + ⅟(2 : AdeleRing (𝓞 F) F) *
      ((fun i => algebraMap F (AdeleRing (𝓞 F) F) (y i)) ⬝ᵥ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (z i)))) = 1 := by
    intro ξ
    have e : (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) ⬝ᵥ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (z i)) +
        ⅟(2 : AdeleRing (𝓞 F) F) * ((fun i => algebraMap F (AdeleRing (𝓞 F) F) (y i)) ⬝ᵥ
          (fun i => algebraMap F (AdeleRing (𝓞 F) F) (z i))) =
        algebraMap F (AdeleRing (𝓞 F) F) (ξ ⬝ᵥ z + 1 / 2 * (y ⬝ᵥ z)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [dotProduct, map_add (f := _), map_mul, map_sum, h2]
    rw [e]
    exact hψ _
  unfold GlobalTheory.WeilM.thetaSum GlobalTheory.WeilM.schr
  simp only [key, one_mul]
  rw [← (Equiv.addRight y).tsum_eq (fun ξ : κ → F => φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)))]
  congr 1
  funext ξ
  congr 1
  funext i
  exact (map_add (algebraMap F (AdeleRing (𝓞 F) F)) (ξ i) (y i)).symm

end GlobalTheory.ThetaQuasiRat

namespace GlobalTheory.ThetaQuasiRat

theorem cA_apply (D : D7) (a : AF D.host.F ⊗[D.host.F] D.host.E) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig a = cA D a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => rfl
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]

theorem symp_eq_symplO (D : D7) (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E)
    (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (hA : JA = T.gramᵀ)
    (hB : ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹)) (x y : Formalism.IndefR.Datum.WO S T) :
    GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB) x y =
      Formalism.IndefR.Datum.symplO S T x y := by
  unfold GlobalTheory.WeilM.symp Formalism.IndefR.Datum.symplO
  congr 1
  have hb : ∀ j l, ξ * incM D.host.F JB j l = incA D D.host.xi0 * incA D (S.gram⁻¹ j l) := fun j l => by
    have := congrFun (congrFun hB j) l
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    rw [this]
    simp [incM, Matrix.map_apply, Matrix.smul_apply, map_mul]
  have e : ∀ i j k l, ξ * (x i j * incM D.host.F JA i k * incM D.host.F JB j l * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig (y k l)) =
      incA D D.host.xi0 * (incA D (S.gram⁻¹ j l) * cA D (y k l) * incA D (T.gram k i) * x i j) := fun i j k l => by
    have h1 : incM D.host.F JA i k = incA D (T.gram k i) := by
      subst hA; rfl
    rw [cA_apply, h1]
    linear_combination (x i j * incA D (T.gram k i) * cA D (y k l)) * hb j l
  unfold GlobalTheory.WeilM.hTens Formalism.IndefR.Datum.hO
  simp only [Finset.mul_sum, e]
  symm
  calc _ = ∑ a, ∑ b, ∑ d, ∑ c, incA D D.host.xi0 *
        (incA D (S.gram⁻¹ a b) * cA D (y c b) * incA D (T.gram c d) * x d a) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ a, ∑ d, ∑ b, ∑ c, incA D D.host.xi0 *
        (incA D (S.gram⁻¹ a b) * cA D (y c b) * incA D (T.gram c d) * x d a) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ d, ∑ a, ∑ b, ∑ c, incA D D.host.xi0 *
        (incA D (S.gram⁻¹ a b) * cA D (y c b) * incA D (T.gram c d) * x d a) := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm

end GlobalTheory.ThetaQuasiRat

namespace GlobalTheory.ThetaQuasiRat

theorem thetaTr_ratW_add : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
      (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
      ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
      ∀ (κ : Type) [Fintype κ]
        (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
        (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
          co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
        ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (w : Formalism.IndefR.Datum.WO S T),
          GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ (ratW T S γ + w) = ψ (-(Formalism.IndefR.Datum.symplOH S T (ratW T S γ) w)) * GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ w := by
  intro D ψ hψ S T JA JB ξ hA hB κ _ co hrat Φ _ γ w
  obtain ⟨y, z, hyz⟩ := hrat γ
  have hγ : ratW T S γ = incM D.host.F γ := rfl
  have hform := co.form (incM D.host.F γ) w
  rw [symp_eq_symplO D S T JA JB ξ hA hB, hyz] at hform
  unfold GlobalTheory.WeilSchrodinger.thetaTr GlobalTheory.WeilM.Darboux.rho
  rw [map_add (f := _), hγ, hyz]
  set u : (κ → AF D.host.F) × (κ → AF D.host.F) :=
    (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i)) with hu
  set v := co.e w
  have law := schr_schr ψ u v Φ
  have hinv : ψ (-(⅟(2 : AF D.host.F) * (u.1 ⬝ᵥ v.2 - v.1 ⬝ᵥ u.2))) *
      ψ (⅟(2 : AF D.host.F) * (u.1 ⬝ᵥ v.2 - v.1 ⬝ᵥ u.2)) = 1 := by
    rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  have hsum : GlobalTheory.WeilM.schr ψ (u + v) Φ =
      ψ (-(⅟(2 : AF D.host.F) * (u.1 ⬝ᵥ v.2 - v.1 ⬝ᵥ u.2))) • GlobalTheory.WeilM.schr ψ u (GlobalTheory.WeilM.schr ψ v Φ) := by
    rw [law, smul_smul, hinv, one_smul]
  have h2 : ⅟(2 : AF D.host.F) = algebraMap D.host.F (AF D.host.F) (1 / 2) := by
    apply invOf_eq_right_inv
    rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]
    norm_num
  rw [hsum, thetaSum_smul', hu, thetaSum_schr_rat D.host.F ψ hψ.1.2.2.1 y z, ← hu,
    Formalism.IndefR.Datum.symplOH, hform, h2]

end GlobalTheory.ThetaQuasiRat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformRationalTranslateQuasiInvariantStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaTransform_rational_translate_quasiInvariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
      (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
      ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
      ∀ (κ : Type) [Fintype κ]
        (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
        (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
          co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
        ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (w : Formalism.IndefR.Datum.WO S T),
          GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ (ratW T S γ + w) = ψ (-(Formalism.IndefR.Datum.symplOH S T (ratW T S γ) w)) * GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ w := by
  first | exact @GlobalTheory.ThetaQuasiRat.thetaTr_ratW_add | exact GlobalTheory.ThetaQuasiRat.thetaTr_ratW_add | (intros; apply GlobalTheory.ThetaQuasiRat.thetaTr_ratW_add <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDiagInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DiagSiegel

open MeasureTheory Formalism.IndefR.Datum

def diagInt {F : Type} [Field F] [NumberField F] {κ : Type} (μ : @Measure (κ → AF F) (borel _))
    (Φ : (κ ⊕ κ → AF F) → ℂ) : ℂ :=
  @integral (κ → AF F) ℂ _ _ (borel _) μ (fun u => Φ (Sum.elim u u))

def diagMat {m n : ℕ} {X : Type} (w : Matrix (Fin m) (Fin n) X) : Matrix (Fin m) (Fin (n + n)) X :=
  (Matrix.fromCols w w).submatrix id finSumFinEquiv.symm

def thetaDiagInt {D : D7} {m n : ℕ} (ν : Measure (Mx D m n)) (𝓕 : Set (Mx D m n)) (f : Mx D m (n + n) → ℂ) : ℂ :=
  ∫ w in 𝓕, f (diagMat w) ∂ν

def ruleFac {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (_c : E →ₐ[R] E) (C : GlobalTheory.WeilM.TestClass R)
    (χ : Eˣ →* Circle) (a : ℕ) {ν : Type} [Fintype ν] [DecidableEq ν] (t : GL ν E) : ℂ :=
  (χ (Matrix.GeneralLinearGroup.det t) : ℂ) *
    (((C.modu (Units.map (Algebra.norm R : E →* R) (Matrix.GeneralLinearGroup.det t)) : ℝ) ^ ((a : ℝ) / 2) : ℝ) : ℂ)

end GlobalTheory.DiagSiegel

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFockVacuumLineUniqueOfHeisenbergDerivati
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFockVacuumLineUniqueOfHeisenbergDerivati
noncomputable section

open scoped TensorProduct Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.VacLn
theorem vac_ne_zero {ι : Type} [Fintype ι] {P Q R S : ℕ} :
    (PiTensorProduct.tprod ℂ fun _ : ι => (1 : Pol P Q R S)) ≠ 0 := by
  intro h
  have := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap
    fun _ => (MvPolynomial.aeval (R := ℂ) (S₁ := ℂ) (σ := Ln P Q R S) fun _ => 0).toLinearMap)) h
  simp at this

theorem vacLine_of_derEx (hD : DerEx) : VacLine := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d a b A C Φ hCM hStd hFr hΦ f₀ ε hyp
  obtain ⟨D, hDu⟩ := hD F E σ α β κ ψ JA JB d hStd
  obtain ⟨J, e, e', hJ, he, hJe, he1, he2, hy⟩ := GlobalTheory.T.fockVacuumEquations_in_archimedeanDarbouxCoordinates F E σ α β κ P Q R S τ JA JB d a b A C ε hCM hFr
  have hDx : ∀ u, At (evI F) u → ∀ (f : SInf F κ) x, D u f x = fderiv ℝ f x (coord d u).1 -
      2 * Real.pi * Complex.I * (trPair F κ x (coord d u).2 : ℝ) * f x := fun u hu f x => (hDu u hu f).2 x
  have hf : ∀ y x, fderiv ℝ f₀ x (J (y - (2 : ℝ) • e y)).1 - 2 * Real.pi * Complex.I *
      (trPair F κ x (J (y - (2 : ℝ) • e y)).2 : ℝ) * f₀ x =
      Complex.I * (fderiv ℝ f₀ x y.1 - 2 * Real.pi * Complex.I * (trPair F κ x y.2 : ℝ) * f₀ x) := by
    intro y x
    obtain ⟨u, u', u₁, c, hu, hu', -, hc, hc', -, h0, h', -⟩ := hy y
    have key := hyp u u' hu hu' c hc hc' (D u f₀) (D u' f₀) (hDu u hu f₀).1 (hDu u' hu' f₀).1
    have := congrArg (fun g : SInf F κ => g x) key
    simp only [SchwartzMap.smul_apply, smul_eq_mul] at this
    rw [hDx u hu, hDx u' hu'] at this
    rw [← h', ← h0]
    exact this
  set g₀ := Φ (PiTensorProduct.tprod ℂ fun _ => 1) with hg₀
  have hg0 : g₀ ≠ 0 := fun h => vac_ne_zero (hΦ.1 (h.trans (map_zero Φ).symm))
  have hg : ∀ y x, fderiv ℝ g₀ x (J y).1 - 2 * Real.pi * Complex.I * (trPair F κ x (J y).2 : ℝ) * g₀ x =
      Complex.I * (fderiv ℝ g₀ x y.1 - 2 * Real.pi * Complex.I * (trPair F κ x y.2 : ℝ) * g₀ x) := by
    intro y x
    obtain ⟨u, -, u₁, c, hu, -, hu₁, hc, -, hc₁, h0, -, h1⟩ := hy y
    have e0 := GlobalTheory.T.hasArchDerivativeOnPureTensor_unique_adelicOperators (hDu u hu g₀).1 (hΦ.2 u hu c hc _)
    have e1 := GlobalTheory.T.hasArchDerivativeOnPureTensor_unique_adelicOperators (hDu u₁ hu₁ g₀).1 (hΦ.2 u₁ hu₁ _ hc₁ _)
    rw [GlobalTheory.T.piTensorSumFockHeisenberg_I_smul_signConj_vacuum, map_smul, ← e0] at e1
    have := congrArg (fun g : SInf F κ => g x) e1
    simp only [SchwartzMap.smul_apply, smul_eq_mul] at this
    rw [hDx u hu, hDx u₁ hu₁] at this
    rw [← h1, ← h0]
    exact this
  obtain ⟨z, hz⟩ := GlobalTheory.T.schwartz_complexStructure_vacuum_solution_eq_smul (trPair F κ) (fun y h => GlobalTheory.T.archimedeanTracePairingBilinear_nondegenerate y h) J e e' hJ he hJe he1 he2 f₀ g₀ hg0 hg hf
  exact ⟨z, hz⟩

end GlobalTheory.VacLn
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFockVacuumLineUniqueOfHeisenbergDerivatiStatement
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives : GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.VacLine := by
  first | exact @GlobalTheory.VacLn.vacLine_of_derEx | exact GlobalTheory.VacLn.vacLine_of_derEx | (intros; apply GlobalTheory.VacLn.vacLine_of_derEx <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerGoodModels
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerGoodModels
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.EvAdm
open scoped Classical

theorem basisS : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (W : Set (κ → FiniteAdeleRing (𝓞 F) F)),
    W ∈ 𝓝 (0 : κ → FiniteAdeleRing (𝓞 F) F) → ∃ a : F, a ≠ 0 ∧ (scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)) ⊆ W :=
  GlobalTheory.T.exists_scaledIntegralFiniteAdelePoints_subset_nhds

theorem boxS : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F) (r : κ → FiniteAdeleRing (𝓞 F) F), a ≠ 0 →
    ∃ φ : ∀ v : HeightOneSpectrum (𝓞 F), (κ → Fv F v) → ℂ, (∀ v, φ v ∈ GlobalTheory.WeilM.SB (κ → Fv F v)) ∧
      (∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) ∧
      ∀ y : κ → FiniteAdeleRing (𝓞 F) F, Set.indicator {y | y - r ∈ scaledInt F κ a} (fun _ => (1 : ℂ)) y =
        ∏ᶠ v, φ v fun i => evalV F v (y i) :=
  GlobalTheory.T.indicator_coset_scaledIntegral_eq_restrictedProduct

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem exists_invariant {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ a : F, a ≠ 0 ∧ ∀ x, ∀ z ∈ scaledInt F κ a, g (x + z) = g x := by
  obtain ⟨hlc, hcs⟩ := hg
  have hW : ∀ y, {z | g (y + z) = g y} ∈ 𝓝 (0 : κ → FiniteAdeleRing (𝓞 F) F) := fun y =>
    ((hlc.isOpen_fiber (g y)).preimage (continuous_const.add continuous_id)).mem_nhds (by simp)
  choose b hb hbW using fun y => basisS F κ _ (hW y)
  have hN : ∀ y ∈ tsupport g, {x | x - y ∈ scaledInt F κ (b y)} ∈ 𝓝 y := fun y _ =>
    ((isOpen_scaledInt (b y)).preimage (continuous_id.sub continuous_const)).mem_nhds (by simp)
  obtain ⟨t, -, ht⟩ := IsCompact.elim_nhds_subcover hcs _ hN
  have hW0 : (⋂ y ∈ t, (scaledInt F κ (b y) : Set (κ → FiniteAdeleRing (𝓞 F) F))) ∈ 𝓝 (0 : κ → FiniteAdeleRing (𝓞 F) F) :=
    (Filter.biInter_finset_mem t).2 fun y _ => (isOpen_scaledInt (b y)).mem_nhds (zero_mem _)
  obtain ⟨a, ha, haW⟩ := basisS F κ _ hW0
  refine ⟨a, ha, fun x z hz => ?_⟩
  have key : ∀ y ∈ t, x - y ∈ scaledInt F κ (b y) → g (x + z) = g x := fun y hy hxy => by
    have hz' : z ∈ scaledInt F κ (b y) := Set.mem_iInter₂.1 (haW hz) y hy
    have h1 : g (y + (x - y)) = g y := hbW y hxy
    have h2 : g (y + (x - y + z)) = g y := hbW y (add_mem hxy hz')
    rw [add_sub_cancel] at h1
    rw [show y + (x - y + z) = x + z by abel] at h2
    rw [h1, h2]
  by_cases hx : x ∈ tsupport g
  · obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht hx)
    exact key y hy hxy
  by_cases hxz : x + z ∈ tsupport g
  · obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht hxz)
    have hz' : z ∈ scaledInt F κ (b y) := Set.mem_iInter₂.1 (haW hz) y hy
    refine key y hy ?_
    have := sub_mem hxy hz'
    rwa [show x + z - y - z = x - y by abel] at this
  rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hxz]

theorem exists_sum_cosets {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ a : F, a ≠ 0 ∧ ∃ R : Finset (κ → FiniteAdeleRing (𝓞 F) F),
      g = ∑ r ∈ R, g r • Set.indicator {y | y - r ∈ scaledInt F κ a} (fun _ => (1 : ℂ)) := by
  obtain ⟨a, ha, hinv⟩ := exists_invariant hg
  refine ⟨a, ha, ?_⟩
  set U := scaledInt F κ a
  have hN : ∀ y ∈ tsupport g, {x | x - y ∈ U} ∈ 𝓝 y := fun y _ =>
    ((isOpen_scaledInt a).preimage (continuous_id.sub continuous_const)).mem_nhds (by simp)
  obtain ⟨t, -, ht⟩ := IsCompact.elim_nhds_subcover hg.2 _ hN
  let R : Finset (κ → FiniteAdeleRing (𝓞 F) F) :=
    (t.image (QuotientAddGroup.mk : (κ → FiniteAdeleRing (𝓞 F) F) → _ ⧸ U)).image Quotient.out
  have hdist : ∀ r ∈ R, ∀ r' ∈ R, ∀ x, x - r ∈ U → x - r' ∈ U → r = r' := by
    intro r hr r' hr' x h h'
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hr
    obtain ⟨q', -, rfl⟩ := Finset.mem_image.1 hr'
    have e1 : (QuotientAddGroup.mk q.out : _ ⧸ U) = QuotientAddGroup.mk x :=
      QuotientAddGroup.eq.2 (by rwa [neg_add_eq_sub])
    have e2 : (QuotientAddGroup.mk q'.out : _ ⧸ U) = QuotientAddGroup.mk x :=
      QuotientAddGroup.eq.2 (by rwa [neg_add_eq_sub])
    rw [QuotientAddGroup.out_eq'] at e1 e2
    rw [e1, e2]
  have hcover : ∀ x ∈ tsupport g, ∃ r ∈ R, x - r ∈ U := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht hx)
    refine ⟨(QuotientAddGroup.mk y : _ ⧸ U).out, Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hy), ?_⟩
    have e : -(QuotientAddGroup.mk y : _ ⧸ U).out + y ∈ U :=
      QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' _)
    have := U.add_mem hxy e
    convert this using 1
    abel
  refine ⟨R, funext fun x => ?_⟩
  rw [Finset.sum_apply]
  by_cases hx : ∃ r ∈ R, x - r ∈ U
  · obtain ⟨r0, hr0, hxr0⟩ := hx
    rw [Finset.sum_eq_single_of_mem r0 hr0]
    · have h := hinv r0 (x - r0) hxr0
      rw [add_sub_cancel] at h
      simp only [Pi.smul_apply, smul_eq_mul, Set.indicator_of_mem (show x ∈ {y | y - r0 ∈ U} from hxr0), mul_one, h]
    · intro r hr hne
      have hm : x ∉ {y | y - r ∈ U} := fun h => hne (hdist r hr r0 hr0 _ h hxr0)
      simp only [Pi.smul_apply, smul_eq_mul, Set.indicator_of_notMem hm, mul_zero]
  · push Not at hx
    have hK : x ∉ tsupport g := fun h => by
      obtain ⟨r, hr, h'⟩ := hcover _ h
      exact hx r hr h'
    rw [image_eq_zero_of_notMem_tsupport hK]
    symm
    refine Finset.sum_eq_zero fun r hr => ?_
    have hm : x ∉ {y | y - r ∈ U} := hx r hr
    simp only [Pi.smul_apply, smul_eq_mul, Set.indicator_of_notMem hm, mul_zero]

theorem exists_sum_finprod {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ (m : ℕ) (c : Fin m → ℂ) (φ : Fin m → ∀ v : HeightOneSpectrum (𝓞 F), (κ → Fv F v) → ℂ),
      (∀ k v, φ k v ∈ GlobalTheory.WeilM.SB (κ → Fv F v)) ∧
      (∀ k, ∀ᶠ v in cofinite, φ k v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) ∧
      g = ∑ k, c k • fun y => ∏ᶠ v, φ k v fun i => evalV F v (y i) := by
  obtain ⟨a, ha, R, hR⟩ := exists_sum_cosets hg
  choose φ hSB hstd hφ using fun r : κ → FiniteAdeleRing (𝓞 F) F => boxS F κ a r ha
  let e := R.equivFin
  refine ⟨R.card, fun k => g (e.symm k), fun k => φ (e.symm k), fun k v => hSB _ v, fun k => hstd _, ?_⟩
  have hind : ∀ r, Set.indicator {y | y - r ∈ scaledInt F κ a} (fun _ => (1 : ℂ)) =
      fun y => ∏ᶠ v, φ r v fun i => evalV F v (y i) := fun r => funext (hφ r)
  refine hR.trans ?_
  simp only [hind]
  rw [← Finset.sum_coe_sort R]
  exact (Equiv.sum_comp e.symm (fun x : R => g x • fun y : κ → FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, φ x v fun i => evalV F v (y i))).symm

theorem comp_mem_adm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ)
    (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X₁ W₁)
    (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E) (I : Set (Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))))
    (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁), M.IsGood B.ψ → M₁.IsGood B.ψ → IsEv B M M₁ ι ι' I e →
      ∀ l ∈ (adeleClass F).adm (Fin n₁ × Fin d₁), l ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d) := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ M M₁ ι ι' I e hM hM₁ hE l hl g hg
  obtain ⟨ei, ev, -, hev, hloc⟩ := hE.loc
  obtain ⟨m, c, φ, hφSB, hφstd, hgeq⟩ := exists_sum_finprod hg
  have hφvac : ∀ k, ∀ᶠ v in cofinite, φ k v = M.vac v := fun k =>
    ((hφstd k).and hM.std).mono fun v h => h.1.trans h.2.symm
  have hψSB : ∀ k v, ev v (φ k v) ∈ GlobalTheory.WeilM.SB (Fin n₁ × Fin d₁ → Fv F v) := fun k v =>
    (hev v).2 ▸ Submodule.mem_map_of_mem (hφSB k v)
  have hψstd : ∀ k, ∀ᶠ v in cofinite, ev v (φ k v) = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := fun k =>
    ((hφvac k).and hM₁.std).mono fun v h => by rw [h.1, (hev v).1, h.2]
  have hg' : ∀ k, (fun y : Fin n₁ × Fin d₁ → FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, ev v (φ k v) fun i => evalV F v (y i)) ∈
      GlobalTheory.WeilM.SB _ := fun k =>
    ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV _ (hψSB k) (hψstd k),
      GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod _ (hψSB k) (hψstd k)⟩
  choose T hT using fun k => hl _ (hg' k)
  refine ⟨∑ k, c k • (T k).comp ei, fun f => ?_⟩
  have h1 : pureA F (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) g = ∑ k, c k • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (φ k) := by
    rw [hgeq]
    funext x
    simp only [pureA, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
    rw [mul_left_comm]
    rfl
  have h2 : ∀ k, e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (φ k)) = pureA F (ei f : (Fin n₁ × Fin d₁ → mixedEmbedding.mixedSpace F) → ℂ)
      (fun y => ∏ᶠ v, ev v (φ k v) fun i => evalV F v (y i)) := fun k =>
    hloc f (φ k) (hφSB k) (hφvac k)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.comp_apply, h1, map_sum, map_smul, h2, hT, FunLike.coe_sum, Finset.sum_apply,
    FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply]

end GlobalTheory.EvAdm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerGoodModelsStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigen_intertwiner_good_models : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ)
    (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X₁ W₁)
    (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E) (I : Set (Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))))
    (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁), M.IsGood B.ψ → M₁.IsGood B.ψ → IsEv B M M₁ ι ι' I e →
      ∀ l ∈ (adeleClass F).adm (Fin n₁ × Fin d₁), l ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d) := by
  first | exact @GlobalTheory.EvAdm.comp_mem_adm | exact GlobalTheory.EvAdm.comp_mem_adm | (intros; apply GlobalTheory.EvAdm.comp_mem_adm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatVecIff
noncomputable section

open NumberField

namespace GlobalTheory.ThetaParseval

def ratVec (F : Type) [Field F] [NumberField F] (κ : Type) : AddSubgroup (κ → AdeleRing (𝓞 F) F) :=
  (AddMonoidHom.compLeft (algebraMap F (AdeleRing (𝓞 F) F)).toAddMonoidHom κ).range

theorem mem_ratVec_iff {F : Type} [Field F] [NumberField F] {κ : Type} (x : κ → AdeleRing (𝓞 F) F) :
    x ∈ ratVec F κ ↔ ∃ ξ : κ → F, x = fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i) := by
  constructor
  · rintro ⟨ξ, rfl⟩
    exact ⟨ξ, rfl⟩
  · rintro ⟨ξ, rfl⟩
    exact ⟨ξ, rfl⟩

end GlobalTheory.ThetaParseval

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLatticeSelfDualEverywhere
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.AdelicU

noncomputable section

namespace GlobalTheory.HermSelfDualLoc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let Q : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have key : Qᵀ * M * Q.map star =
      (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm := by
    rw [← hA]
    simp only [Q]
    ext i j
    simp [Matrix.mul_apply, Matrix.submatrix_apply]
  have hN : ((Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm).det ≠ 0 := by
    rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
    simp [Matrix.det_neg]
  intro h0
  apply hN
  rw [← key, Matrix.det_mul, Matrix.det_mul, h0]
  simp

theorem det_ne_zero_of_isHerm (σ : E →ₐ[F] E) (B : Base F E) {n : ℕ} {X : Spc F E n} {r s : ℕ}
    (hX : X.IsHerm σ B r s) : X.J.det ≠ 0 := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have h := det_ne_zero_of_hasSig (hX.sig w)
  have e : (X.J.map (B.emb w).1).det = (B.emb w).1 X.J.det := (RingHom.map_det _ _).symm
  intro h0
  exact h (by rw [e, h0, map_zero])

theorem hE_transpose (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    hE σ Jᵀ x y = form σ J y x := by
  simp only [hE, Formalism.UG.hform, form, dotProduct, Matrix.mulVec, Matrix.transpose_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  simp only [AlgHom.coe_toRingHom]
  ring

theorem isIntegral_iff_mem_range (e : E) : IsIntegral ℤ e ↔ e ∈ (algebraMap (𝓞 E) E).range :=
  ⟨fun h => ⟨⟨e, h⟩, rfl⟩, fun ⟨r, hr⟩ => hr ▸ r.isIntegral_coe⟩

theorem isSelfDualAt_transpose : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (X : Spc F E n) (r s : ℕ), B.IsGood σ → X.IsHerm σ B r s →
    ∀ v : HeightOneSpectrum (𝓞 F), IsSelfDualAt σ X.Jᵀ X.L v := by
  intro F E _ _ _ _ _ σ B n X r s _ hX v
  have hJ : (X.Jᵀ).det ≠ 0 := by rw [Matrix.det_transpose]; exact det_ne_zero_of_isHerm σ B hX
  refine (GlobalTheory.AdelicU.SelfDual.forall_isSelfDualAt_iff hJ hX.lat).2 (fun y => ?_) v
  rw [hX.dual y]
  simp only [hE_transpose, isIntegral_iff_mem_range]

end GlobalTheory.HermSelfDualLoc

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergEigenProportionalLocalField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergEigenProportionalLocalField
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem GlobalTheory.heisenbergEigen_proportional : ∀ {k : Type} [Field k] {κ : Type} [Fintype κ] (ψk : AddChar k ℂ) (Λ : AddSubgroup ((κ → k) × (κ → k)))
    (χ : (κ → k) × (κ → k) → ℂ) (f g : (κ → k) → ℂ),
    (∀ l ∈ Λ, ∀ ξ, ψk (ξ ⬝ᵥ l.2 + (2 : k)⁻¹ * (l.1 ⬝ᵥ l.2)) * f (ξ + l.1) = χ l * f ξ) →
    (∀ l ∈ Λ, ∀ ξ, ψk (ξ ⬝ᵥ l.2 + (2 : k)⁻¹ * (l.1 ⬝ᵥ l.2)) * g (ξ + l.1) = χ l * g ξ) → f ≠ 0 →
    (∀ η : κ → k, (∀ b : κ → k, ((0 : κ → k), b) ∈ Λ → ψk (η ⬝ᵥ b) = 1) → ∃ y, (η, y) ∈ Λ) →
    ∃ c : ℂ, g = c • f := by
  intro k _ κ _ ψk Λ χ f g hf hg hf0 hann
  have hψ : ∀ x : k, ψk x ≠ 0 := by
    intro x hx
    have h2 : ψk (x + -x) = ψk x * ψk (-x) := AddChar.map_add_eq_mul ψk x (-x)
    rw [add_neg_cancel, AddChar.map_zero_eq_one, hx, zero_mul] at h2
    exact one_ne_zero h2
  obtain ⟨ξ₀, hξ₀⟩ : ∃ ξ₀, f ξ₀ ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hf0 (funext hc)
  refine ⟨g ξ₀ / f ξ₀, ?_⟩
  obtain ⟨h, hh⟩ : ∃ h : (κ → k) → ℂ, ∀ ξ, h ξ = g ξ - g ξ₀ / f ξ₀ * f ξ :=
    ⟨_, fun _ => rfl⟩
  have hid : ∀ l ∈ Λ, ∀ ξ, ψk (ξ ⬝ᵥ l.2 + (2 : k)⁻¹ * (l.1 ⬝ᵥ l.2)) * h (ξ + l.1) = χ l * h ξ := by
    intro l hl ξ
    have e1 := hf l hl ξ
    have e2 := hg l hl ξ
    rw [hh, hh]
    linear_combination e2 - (g ξ₀ / f ξ₀) * e1
  have h0 : h ξ₀ = 0 := by rw [hh, div_mul_cancel₀ _ hξ₀, sub_self]
  have hzero : ∀ ξ, h ξ = 0 := by
    intro ξ
    by_contra hne
    have key : ∀ b, ((0 : κ → k), b) ∈ Λ → ψk ((ξ - ξ₀) ⬝ᵥ b) = 1 := by
      intro b hb
      have e1 := hid _ hb ξ
      have e2 := hf _ hb ξ₀
      simp only [zero_dotProduct, mul_zero, add_zero] at e1 e2
      have a1 : ψk (ξ ⬝ᵥ b) = χ (0, b) := mul_right_cancel₀ hne e1
      have a2 : ψk (ξ₀ ⬝ᵥ b) = χ (0, b) := mul_right_cancel₀ hξ₀ e2
      have hχ : χ (0, b) ≠ 0 := a2 ▸ hψ _
      have hs : ψk ((ξ - ξ₀) ⬝ᵥ b) * ψk (ξ₀ ⬝ᵥ b) = ψk (ξ ⬝ᵥ b) := by
        rw [← AddChar.map_add_eq_mul, sub_dotProduct, sub_add_cancel]
      rw [a1, a2] at hs
      exact mul_right_cancel₀ hχ (hs.trans (one_mul _).symm)
    obtain ⟨y, hy⟩ := hann _ key
    have e := hid _ hy ξ₀
    have hx : ξ₀ + (ξ - ξ₀) = ξ := by abel
    simp only [h0, mul_zero, hx] at e
    exact hne ((mul_eq_zero.mp e).resolve_left (hψ _))
  funext ξ
  have := hzero ξ
  rw [hh, sub_eq_zero] at this
  rw [Pi.smul_apply, smul_eq_mul, this]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergEigenProportionalLocalFieldStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergEigen_proportional_localField : ∀ {k : Type} [Field k] {κ : Type} [Fintype κ] (ψk : AddChar k ℂ) (Λ : AddSubgroup ((κ → k) × (κ → k)))
    (χ : (κ → k) × (κ → k) → ℂ) (f g : (κ → k) → ℂ),
    (∀ l ∈ Λ, ∀ ξ, ψk (ξ ⬝ᵥ l.2 + (2 : k)⁻¹ * (l.1 ⬝ᵥ l.2)) * f (ξ + l.1) = χ l * f ξ) →
    (∀ l ∈ Λ, ∀ ξ, ψk (ξ ⬝ᵥ l.2 + (2 : k)⁻¹ * (l.1 ⬝ᵥ l.2)) * g (ξ + l.1) = χ l * g ξ) → f ≠ 0 →
    (∀ η : κ → k, (∀ b : κ → k, ((0 : κ → k), b) ∈ Λ → ψk (η ⬝ᵥ b) = 1) → ∃ y, (η, y) ∈ Λ) →
    ∃ c : ℂ, g = c • f := by
  first | exact @GlobalTheory.heisenbergEigen_proportional | exact GlobalTheory.heisenbergEigen_proportional | (intros; apply GlobalTheory.heisenbergEigen_proportional <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DOpMemDStep
noncomputable section

namespace GlobalTheory.FockKFin

open NumberField GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.EvAt0.PolD

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def dStep {κ : Type} [Fintype κ] (P : Submodule ℂ (SInf F κ)) : Submodule ℂ (SInf F κ) :=
  Submodule.span ℂ {h | ∃ a b : κ → mixedEmbedding.mixedSpace F, ∃ f ∈ P, h = dOp a b f}

theorem dOp_mem_dStep {κ : Type} [Fintype κ] (P : Submodule ℂ (SInf F κ)) (a b : κ → mixedEmbedding.mixedSpace F)
    {f : SInf F κ} (hf : f ∈ P) : dOp a b f ∈ dStep P :=
  Submodule.subset_span ⟨a, b, f, hf, rfl⟩

variable {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

def vacSp (M : Model σ X W) (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) : Submodule ℂ (SInf F (Fin n × Fin d)) :=
  Submodule.span ℂ {g | GaussD M τ g}

def polLe (M : Model σ X W) (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) (m : ℕ) :
    Submodule ℂ (SInf F (Fin n × Fin d)) :=
  Nat.rec (motive := fun _ => Submodule ℂ (SInf F (Fin n × Fin d))) (vacSp M τ) (fun _ P => P ⊔ dStep P) m

theorem polLe_zero (M : Model σ X W) (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) : polLe M τ 0 = vacSp M τ := rfl

theorem polLe_succ (M : Model σ X W) (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) (m : ℕ) :
    polLe M τ (m + 1) = polLe M τ m ⊔ dStep (polLe M τ m) := rfl

theorem polLe_mono (M : Model σ X W) (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) : Monotone (polLe M τ) :=
  monotone_nat_of_le_succ fun m => by rw [polLe_succ]; exact le_sup_left

def pureL {κ : Type} [Fintype κ] (φ : ∀ v : Pl F, (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ) : SInf F κ →ₗ[ℂ] (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ where
  toFun f := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ
  map_add' f g := by funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, add_mul]
  map_smul' c f := by funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]

end GlobalTheory.FockKFin

end
end
