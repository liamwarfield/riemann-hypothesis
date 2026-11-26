module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnimodularGramInverseInertPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceUnramifiedSkewSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedSectionChartCoords
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableSetSetOfLe

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCoordinatesActionOfIdentityOffPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCoordinatesActionOfIdentityOffPlace
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertLocFrame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]

theorem frame_mul_map (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (hmul : ∀ x y, ι (x * y) = ι x * ι y) {m k : ℕ}
    (A : Matrix (Fin m) (Fin m) L) (Y : Matrix (Fin m) (Fin k) L) :
    ((1 - ι 1) • (1 : Matrix (Fin m) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) + A.map ι) * Y.map ι = (A * Y).map ι := by
  rw [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul]
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, sub_mul, one_mul, ← hmul, one_mul, sub_self,
    zero_add, Matrix.mul_apply, Matrix.map_apply, Matrix.mul_apply, map_sum]
  simp only [Matrix.map_apply, hmul]

theorem map_mul_frame_transpose (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (hmul : ∀ x y, ι (x * y) = ι x * ι y) {m k : ℕ}
    (C : Matrix (Fin k) (Fin k) L) (Y : Matrix (Fin m) (Fin k) L) :
    Y.map ι * ((1 - ι 1) • (1 : Matrix (Fin k) (Fin k) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) + C.map ι)ᵀ = (Y * Cᵀ).map ι := by
  rw [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one]
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, sub_mul, one_mul, ← hmul, one_mul, sub_self,
    zero_add, Matrix.mul_apply, Matrix.map_apply, Matrix.mul_apply, map_sum]
  simp only [Matrix.map_apply, Matrix.transpose_apply, hmul]

theorem actAB_xm_frame (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (L : Type) [Field L]
    (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (hmul : ∀ x y, ι (x * y) = ι x * ι y)
    (PV : GL (Fin n) L) (PW : GL (Fin d) L) (A : Matrix (Fin n) (Fin n) L) (C : Matrix (Fin d) (Fin d) L)
    (g : UA σ X.J) (h : UA σ W.J)
    (hg : mat g = (1 - ι 1) • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) + A.map ι)
    (hh : mat h = (1 - ι 1) • (1 : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) + C.map ι) (x : Matrix (Fin d) (Fin n) L) :
    actAB (cA σ) (g, h) (xm ι PV PW x) =
      (A * (PV : Matrix (Fin n) (Fin n) L) * xᵀ * (PW : Matrix (Fin d) (Fin d) L)ᵀ * Cᵀ).map ι := by
  change mat g * xm ι PV PW x * (mat h)ᵀ = _
  rw [xm_apply, hg, hh, frame_mul_map ι hmul, map_mul_frame_transpose ι hmul]
  simp only [Matrix.mul_assoc]

end GlobalTheory.InertLocFrame

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCoordinatesActionOfIdentityOffPlaceStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_coordinates_action_of_identity_off_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (L : Type) [Field L]
    (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), (∀ x y, ι (x * y) = ι x * ι y) →
      ∀ (PV : GL (Fin n) L) (PW : GL (Fin d) L) (A : Matrix (Fin n) (Fin n) L) (C : Matrix (Fin d) (Fin d) L)
        (g : UA σ X.J) (h : UA σ W.J),
        mat g = (1 - ι 1) • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) + A.map ι →
        mat h = (1 - ι 1) • (1 : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) + C.map ι →
        ∀ x, actAB (cA σ) (g, h) (GlobalTheory.InertLocFrame.xm ι PV PW x) =
          (A * (PV : Matrix (Fin n) (Fin n) L) * xᵀ * (PW : Matrix (Fin d) (Fin d) L)ᵀ * Cᵀ).map ι := by
  first | exact @GlobalTheory.InertLocFrame.actAB_xm_frame | exact GlobalTheory.InertLocFrame.actAB_xm_frame | (intros; apply GlobalTheory.InertLocFrame.actAB_xm_frame <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilSymplecticFormFrameCoordinatesEqLocalTrace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilSymplecticFormFrameCoordinatesEqLocalTrace
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertLocSymp

theorem quadruple_sum_eq_trace_transpose_mul {L : Type} [CommRing L] (σL : L →+* L) {α β : Type} [Fintype α] [Fintype β]
    (X Y : Matrix α β L) (A : Matrix α α L) (B : Matrix β β L) :
    (∑ i, ∑ j, ∑ k, ∑ l, X i j * A i k * B j l * σL (Y k l)) =
      Matrix.trace (A * Y.map σL * Bᵀ * Xᵀ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem trace_coords {L : Type} [CommRing L] (σL : L →+* L) {n d : ℕ}
    (PV A : Matrix (Fin n) (Fin n) L) (PW B : Matrix (Fin d) (Fin d) L) (x y : Matrix (Fin d) (Fin n) L) :
    Matrix.trace (A * (PV * yᵀ * PWᵀ).map σL * Bᵀ * (PV * xᵀ * PWᵀ)ᵀ) =
      Matrix.trace ((PVᵀ * A * PV.map σL) * (y.map σL)ᵀ * (PWᵀ * B * PW.map σL)ᵀ * x) := by
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_map, Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm PVᵀ]
  simp only [Matrix.mul_assoc]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mul_inclR {L : Type} [Field L] (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (v : Pl (F := F))
    (hAt : ∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ↔ ∃ x, ι x = z) (hmul : ∀ x y, ι (x * y) = ι x * ι y) (a : L) (e : E) :
    ι a * inclR (F := F) (AF F) e = ι (a * GlobalTheory.InertLocFrame.pre ι (ι 1 * inclR (F := F) (AF F) e)) := by
  have hat : ∃ z, ι z = ι 1 * inclR (F := F) (AF F) e := by
    refine (hAt _).1 fun u hu => ?_
    have h1 : u • ι 1 = 0 := (hAt (ι 1)).2 ⟨1, rfl⟩ u hu
    rw [← smul_mul_assoc, h1, zero_mul]
  rw [hmul, GlobalTheory.InertLocFrame.pre_spec ι hat, ← mul_assoc, ← hmul, mul_one]

end GlobalTheory.InertLocSymp


open GlobalTheory.InertLocSymp in
theorem GlobalTheory.InertLocSymp.psi_symp_eq :
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (v : Pl (F := F)) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σL : L →+* L) (q : ℕ) (δ : L) (ψL : AddChar L ℂ) (ι : L →+ AE F E),
      Formalism.UG.IsUnramInv ϖ σL q → (Valued.v δ = 1 ∧ σL δ = -δ) → Function.Injective ι → (∀ z : AE F E, At (evFin F v) z ↔ ∃ x, ι x = z) → (∀ x y, ι (x * y) = ι x * ι y) → (∀ x, ι (σL x) = cA σ (ι x)) →
      (∀ x, B.ψ (Algebra.trace (AF F) (AE F E) (ι x)) = ψL (x + σL x)) →
      ∀ (PV JS : GL (Fin n) L) (PW JT : GL (Fin d) L),
        ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = GlobalTheory.InertLocFrame.gram σL ι PV X.J →
        (JT : Matrix (Fin d) (Fin d) L) = -δ⁻¹ • (GlobalTheory.InertLocFrame.gram σL ι PW W.J)ᵀ →
        ∀ x y, B.ψ (⅟(2 : AF F) * symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)
            (GlobalTheory.InertLocFrame.xm ι PV PW x) (GlobalTheory.InertLocFrame.xm ι PV PW y)) =
          ψL ((GlobalTheory.Hk3.locH σL δ JS JT x y + σL (GlobalTheory.Hk3.locH σL δ JS JT x y)) / 2) := by
  intro F E _ _ _ _ _ σ B v n d X W L _ _ ϖ σL q δ ψL ι _ hδ hinj hAt hmul hσ hψ PV JS PW JT hGV hGW x y
  have hδ0 : δ ≠ 0 := by
    intro h; rw [h, map_zero] at hδ; exact zero_ne_one hδ.1

  have hT : hTens (cA σ) (incM F X.J) (incM F W.J) (GlobalTheory.InertLocFrame.xm ι PV PW x) (GlobalTheory.InertLocFrame.xm ι PV PW y) =
      ι (∑ i, ∑ j, ∑ k, ∑ l, ((PV : Matrix (Fin n) (Fin n) L) * xᵀ * (PW : Matrix (Fin d) (Fin d) L)ᵀ) i j *
        GlobalTheory.InertLocFrame.tJ ι X.J i k * GlobalTheory.InertLocFrame.tJ ι W.J j l *
        σL (((PV : Matrix (Fin n) (Fin n) L) * yᵀ * (PW : Matrix (Fin d) (Fin d) L)ᵀ) k l)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hTens, map_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [GlobalTheory.InertLocFrame.xm_apply, incM, Matrix.map_apply, ← hσ]
    rw [mul_inclR ι v hAt hmul, mul_inclR ι v hAt hmul, ← hmul]
    rfl

  have hS : (∑ i, ∑ j, ∑ k, ∑ l, ((PV : Matrix (Fin n) (Fin n) L) * xᵀ * (PW : Matrix (Fin d) (Fin d) L)ᵀ) i j *
        GlobalTheory.InertLocFrame.tJ ι X.J i k * GlobalTheory.InertLocFrame.tJ ι W.J j l *
        σL (((PV : Matrix (Fin n) (Fin n) L) * yᵀ * (PW : Matrix (Fin d) (Fin d) L)ᵀ) k l)) =
      -GlobalTheory.Hk3.locH σL δ JS JT x y := by
    rw [quadruple_sum_eq_trace_transpose_mul, trace_coords]
    have e1 : (PV : Matrix (Fin n) (Fin n) L)ᵀ * GlobalTheory.InertLocFrame.tJ ι X.J * (PV : Matrix (Fin n) (Fin n) L).map σL =
        ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := hGV.symm
    have e2 : ((PW : Matrix (Fin d) (Fin d) L)ᵀ * GlobalTheory.InertLocFrame.tJ ι W.J * (PW : Matrix (Fin d) (Fin d) L).map σL)ᵀ =
        -δ • (JT : Matrix (Fin d) (Fin d) L) := by
      rw [hGW, smul_smul, neg_mul_neg, mul_inv_cancel₀ hδ0, one_smul]; rfl
    rw [e1, e2, GlobalTheory.Hk3.locH, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
      Matrix.trace_mul_comm _ x]
    simp only [Matrix.mul_assoc]; ring
  have h2 : (2 : L) ≠ 0 := by
    intro h
    have h1 : (2 : AF F) • ι 1 = 0 := by
      rw [two_smul, ← map_add (f := _), one_add_one_eq_two, h, map_zero]
    have : ι 1 = 0 := by
      rw [← one_smul (AF F) (ι 1), ← invOf_mul_self (2 : AF F), mul_smul, h1, smul_zero]
    exact one_ne_zero (hinj (this.trans (map_zero ι).symm))
  haveI : NeZero (2 : L) := ⟨h2⟩
  set z := GlobalTheory.Hk3.locH σL δ JS JT x y
  have hhalf : ⅟(2 : AF F) • ι z = ι (z / 2) := by
    have : ι z = (2 : AF F) • ι (z / 2) := by
      rw [two_smul, ← map_add (f := _), add_halves]
    rw [this, smul_smul, invOf_mul_self, one_smul]
  have hsymp : ⅟(2 : AF F) * symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)
      (GlobalTheory.InertLocFrame.xm ι PV PW x) (GlobalTheory.InertLocFrame.xm ι PV PW y) =
      Algebra.trace (AF F) (AE F E) (ι (z / 2)) := by
    rw [symp, hT, hS, map_neg, neg_one_mul, neg_neg, ← smul_eq_mul, ← LinearMap.map_smul, hhalf]
  rw [hsymp, hψ, map_div₀, map_ofNat, add_div]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilSymplecticFormFrameCoordinatesEqLocalTraceStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_symplectic_form_frame_coordinates_eq_local_trace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (v : Pl (F := F)) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σL : L →+* L) (q : ℕ) (δ : L) (ψL : AddChar L ℂ) (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      Formalism.UG.IsUnramInv ϖ σL q → (Valued.v δ = 1 ∧ σL δ = -δ) → Function.Injective ι → (∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ↔ ∃ x, ι x = z) → (∀ x y, ι (x * y) = ι x * ι y) → (∀ x, ι (σL x) = cA σ (ι x)) →
      (∀ x, B.ψ (Algebra.trace (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (ι x)) = ψL (x + σL x)) →
      ∀ (PV JS : GL (Fin n) L) (PW JT : GL (Fin d) L),
        ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = GlobalTheory.InertLocFrame.gram σL ι PV X.J →
        (JT : Matrix (Fin d) (Fin d) L) = -δ⁻¹ • (GlobalTheory.InertLocFrame.gram σL ι PW W.J)ᵀ →
        ∀ x y, B.ψ (⅟(2 : AF F) * symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)
            (GlobalTheory.InertLocFrame.xm ι PV PW x) (GlobalTheory.InertLocFrame.xm ι PV PW y)) =
          ψL ((GlobalTheory.Hk3.locH σL δ JS JT x y + σL (GlobalTheory.Hk3.locH σL δ JS JT x y)) / 2) := by
  first | exact @GlobalTheory.InertLocSymp.psi_symp_eq | exact GlobalTheory.InertLocSymp.psi_symp_eq | (intros; apply GlobalTheory.InertLocSymp.psi_symp_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupportedAdelicUnitaryPointOfLocalMatrix
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupportedAdelicUnitaryPointOfLocalMatrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.InertLocFrame

theorem uAt_of_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (v : Pl (F := F)) (n : ℕ) (X : Spc F E n) (L : Type) [Field L]
    (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), (∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ↔ ∃ x, ι x = z) →
      ∀ (g : UA σ X.J) (A : Matrix (Fin n) (Fin n) L),
        mat g = (1 - ι 1) • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) + A.map ι → g ∈ UAt σ X (evFin F v) := by
  intro F E _ _ _ _ _ σ v n X L _ ι hι g A hg u hu
  have hent : ∀ i j, (mat g - 1) i j = ι ((A - 1) i j) := by
    intro i j
    rw [hg]
    by_cases h : i = j
    · subst h
      simp [Matrix.one_apply, map_sub]
      abel
    · simp [Matrix.one_apply, h, map_sub]
  ext i j
  have h1 : At (evFin F v) ((mat g - 1) i j) := (hι _).2 ⟨_, (hent i j).symm⟩
  simpa using h1 u hu

end GlobalTheory.InertLocFrame
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupportedAdelicUnitaryPointOfLocalMatrixStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.supported_adelic_unitary_point_of_local_matrix : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (v : Pl (F := F)) (n : ℕ) (X : Spc F E n) (L : Type) [Field L]
    (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), (∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ↔ ∃ x, ι x = z) →
      ∀ (g : UA σ X.J) (A : Matrix (Fin n) (Fin n) L),
        mat g = (1 - ι 1) • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) + A.map ι → g ∈ UAt σ X (evFin F v) := by
  first | exact @GlobalTheory.InertLocFrame.uAt_of_local | exact GlobalTheory.InertLocFrame.uAt_of_local | (intros; apply GlobalTheory.InertLocFrame.uAt_of_local <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatticeStabilizerOfFrameConjIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatticeStabilizerOfFrameConjIntegral
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertKatFrame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem latAt_entry_at {n : ℕ} (X : Spc F E n) (v : Pl (F := F)) {z : Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)}
    (hz : z ∈ GlobalTheory.InertSph.latAt X v) (i : Fin n) : At (evFin F v) (z i) := by
  induction hz using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, -, y, -, rfl⟩ := hx
    intro u hu
    have h0 := ha u hu
    rw [smul_eq_mul] at h0
    simp only [Pi.smul_apply]
    rw [smul_smul, h0, zero_smul]
  | zero => intro u _; simp
  | add x y _ _ hx hy => intro u hu; simp [smul_add, hx u hu, hy u hu]
  | neg x _ hx => intro u hu; simp [smul_neg, hx u hu]

theorem mulVec_mem_latAt {n : ℕ} (X : Spc F E n) (v : Pl (F := F)) {L : Type} [Field L]
    [Valued L (WithZero (Multiplicative ℤ))] (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))
    (hsurj : ∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ↔ ∃ x, ι x = z) (hmul : ∀ x y, ι (x * y) = ι x * ι y)
    (P : GL (Fin n) L) (hP : ∀ x : Fin n → L, (∀ i, x i ∈ Formalism.UG.intL L) ↔
        (fun i => ι (((P : Matrix (Fin n) (Fin n) L) *ᵥ x) i)) ∈ GlobalTheory.InertSph.latAt X v)
    (K : Matrix (Fin n) (Fin n) L) (hK : ∀ i j, K i j ∈ Formalism.UG.intL L)
    (A : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (hA : A = (1 - ι 1) • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) +
          ((P : Matrix (Fin n) (Fin n) L) * K * ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)).map ι)
    (z : Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (hz : z ∈ GlobalTheory.InertSph.latAt X v) : A *ᵥ z ∈ GlobalTheory.InertSph.latAt X v := by
  obtain ⟨y, rfl⟩ : ∃ y : Fin n → L, z = fun i => ι (y i) :=
    ⟨fun i => GlobalTheory.InertLocFrame.pre ι (z i), funext fun i =>
      (GlobalTheory.InertLocFrame.pre_spec ι ((hsurj _).1 (latAt_entry_at X v hz i))).symm⟩
  obtain ⟨x, rfl⟩ : ∃ x : Fin n → L, y = (P : Matrix (Fin n) (Fin n) L) *ᵥ x := by
    refine ⟨((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ y, ?_⟩
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have hx := (hP x).2 hz
  have hKx : ∀ i, (K *ᵥ x) i ∈ Formalism.UG.intL L := fun i => by
    simp only [Matrix.mulVec, dotProduct]
    exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hK i j) (hx j)
  have key : A *ᵥ (fun i => ι (((P : Matrix (Fin n) (Fin n) L) *ᵥ x) i)) =
      fun i => ι (((P : Matrix (Fin n) (Fin n) L) *ᵥ (K *ᵥ x)) i) := by
    set N := (P : Matrix (Fin n) (Fin n) L) * K * ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hN
    set Y := (P : Matrix (Fin n) (Fin n) L) *ᵥ x with hY
    have h1 : (1 - ι 1) • (fun i => ι (Y i)) = 0 := by
      funext j
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [sub_mul, one_mul, ← hmul, one_mul, sub_self]
    have h2 : N.map ι *ᵥ (fun i => ι (Y i)) = fun i => ι ((N *ᵥ Y) i) := by
      funext i
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp_rw [hmul]
    have h3 : N *ᵥ Y = (P : Matrix (Fin n) (Fin n) L) *ᵥ (K *ᵥ x) := by
      rw [hY, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hN, Matrix.mul_assoc, ← Units.val_mul,
        inv_mul_cancel, Units.val_one, Matrix.mul_one]
    rw [hA, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, h1, zero_add, h2, h3]
  rw [key]
  exact (hP _).1 hKx

theorem mem_KAt_of_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (v : Pl (F := F)) (n : ℕ) (X : Spc F E n) (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      Function.Injective ι → (∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ↔ ∃ x, ι x = z) → (∀ x y, ι (x * y) = ι x * ι y) →
      (∀ x, x ∈ Formalism.UG.intL L ↔ ι x ∈ AddSubgroup.closure {z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) | ∃ a : AF F, At (evFin F v) a ∧
        evFin F v a ∈ v.adicCompletionIntegers F ∧ ∃ o : 𝓞 E, z = a • inclR (F := F) (AF F) (o : E)}) →
      ∀ P : GL (Fin n) L, (∀ x : Fin n → L, (∀ i, x i ∈ Formalism.UG.intL L) ↔
        (fun i => ι (((P : Matrix (Fin n) (Fin n) L) *ᵥ x) i)) ∈ GlobalTheory.InertSph.latAt X v) →
      ∀ (g : UA σ X.J) (K K' : Matrix (Fin n) (Fin n) L), (∀ i j, K i j ∈ Formalism.UG.intL L) →
        (∀ i j, K' i j ∈ Formalism.UG.intL L) →
        mat g = (1 - ι 1) • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) +
          ((P : Matrix (Fin n) (Fin n) L) * K * ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)).map ι →
        mat g⁻¹ = (1 - ι 1) • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) +
          ((P : Matrix (Fin n) (Fin n) L) * K' * ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)).map ι →
        g ∈ GlobalTheory.InertSph.KAt σ X v := by
  intro F E _ _ _ _ _ σ v n X L _ _ ι _hinj hsurj hmul _hint P hP g K K' hK hK' hg hg'
  refine ⟨?_, fun z hz => ⟨mulVec_mem_latAt X v ι hsurj hmul P hP K hK _ hg z hz,
    mulVec_mem_latAt X v ι hsurj hmul P hP K' hK' _ hg' z hz⟩⟩
  have hsup : ∀ w u, evFin F v u = 0 → u • ι w = 0 := fun w => (hsurj (ι w)).2 ⟨w, rfl⟩
  intro u hu
  set N := (P : Matrix (Fin n) (Fin n) L) * K * ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
  have hm : mat g - 1 = (N - 1).map ι := by
    rw [hg]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.one_apply, map_sub]
      ring
    · simp [Matrix.one_apply, hij]
  rw [hm]
  ext i j
  simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.zero_apply]
  exact hsup _ u hu

end GlobalTheory.InertKatFrame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatticeStabilizerOfFrameConjIntegralStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_latticeStabilizer_of_frame_conj_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (v : Pl (F := F)) (n : ℕ) (X : Spc F E n) (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      Function.Injective ι → (∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ↔ ∃ x, ι x = z) → (∀ x y, ι (x * y) = ι x * ι y) →
      (∀ x, x ∈ Formalism.UG.intL L ↔ ι x ∈ AddSubgroup.closure {z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) | ∃ a : AF F, At (evFin F v) a ∧
        evFin F v a ∈ v.adicCompletionIntegers F ∧ ∃ o : 𝓞 E, z = a • inclR (F := F) (AF F) (o : E)}) →
      ∀ P : GL (Fin n) L, (∀ x : Fin n → L, (∀ i, x i ∈ Formalism.UG.intL L) ↔
        (fun i => ι (((P : Matrix (Fin n) (Fin n) L) *ᵥ x) i)) ∈ GlobalTheory.InertSph.latAt X v) →
      ∀ (g : UA σ X.J) (K K' : Matrix (Fin n) (Fin n) L), (∀ i j, K i j ∈ Formalism.UG.intL L) →
        (∀ i j, K' i j ∈ Formalism.UG.intL L) →
        mat g = (1 - ι 1) • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) +
          ((P : Matrix (Fin n) (Fin n) L) * K * ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)).map ι →
        mat g⁻¹ = (1 - ι 1) • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) +
          ((P : Matrix (Fin n) (Fin n) L) * K' * ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)).map ι →
        g ∈ GlobalTheory.InertSph.KAt σ X v := by
  first | exact @GlobalTheory.InertKatFrame.mem_KAt_of_frame | exact GlobalTheory.InertKatFrame.mem_KAt_of_frame | (intros; apply GlobalTheory.InertKatFrame.mem_KAt_of_frame <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameAdelicLatticeAtFinitePlaceOfInert
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertLocBasis

open GlobalTheory.InertSph

section Alg

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

local instance valRing : ValuationRing (Formalism.UG.intL L) :=
  ValuationRing.of_integers (Valued.v : Valuation L (WithZero (Multiplicative ℤ))) (Valuation.integer.integers _)

local instance fracRing : IsFractionRing (Formalism.UG.intL L) L :=
  inferInstanceAs (IsFractionRing (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring L)

theorem exists_basis_of_fg {n : ℕ} (M : Submodule (Formalism.UG.intL L) (Fin n → L)) (hfg : M.FG)
    (hsp : Submodule.span L (M : Set (Fin n → L)) = ⊤) :
    ∃ P : GL (Fin n) L, ∀ x : Fin n → L,
      (∀ i, x i ∈ Formalism.UG.intL L) ↔ (P : Matrix (Fin n) (Fin n) L) *ᵥ x ∈ M := by
  have : Module.Finite (Formalism.UG.intL L) M := Module.Finite.iff_fg.2 hfg
  have : Module.Free (Formalism.UG.intL L) M := by
    have : Module.Flat (Formalism.UG.intL L) M := by
      rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
      intro x hx
      rw [Submodule.mem_bot]
      obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff x).1 hx
      have ha0 : ((a : Formalism.UG.intL L) : L) ≠ 0 := fun h =>
        nonZeroDivisors.ne_zero a.2 (Subtype.ext h)
      apply Subtype.ext
      funext i
      have h1 := congrFun (congrArg Subtype.val ha) i
      change ((a : Formalism.UG.intL L) : L) * (x : Fin n → L) i = 0 at h1
      exact (mul_eq_zero.1 h1).resolve_left ha0
    exact Module.free_of_flat_of_isLocalRing
  let b := Module.Free.chooseBasis (Formalism.UG.intL L) M
  let v : Module.Free.ChooseBasisIndex (Formalism.UG.intL L) M → Fin n → L := fun i => (b i : Fin n → L)
  have hR : LinearIndependent (Formalism.UG.intL L) v := b.linearIndependent.map' M.subtype (Submodule.ker_subtype _)
  have hC : LinearIndependent L v := (LinearIndependent.iff_fractionRing (Formalism.UG.intL L) L).1 hR
  have hspR : Submodule.span (Formalism.UG.intL L) (Set.range v) = M := by
    have : Set.range v = M.subtype '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
  have hspC : Submodule.span L (Set.range v) = ⊤ := by
    rw [← Submodule.span_span_of_tower (Formalism.UG.intL L), hspR, hsp]
  let bC := Module.Basis.mk hC (by rw [hspC])
  have hcard : Fintype.card (Fin n) = Fintype.card (Module.Free.ChooseBasisIndex (Formalism.UG.intL L) M) := by
    rw [← Module.finrank_fintype_fun_eq_card (R := L), Module.finrank_eq_card_basis bC]
  let e : Fin n ≃ Module.Free.ChooseBasisIndex (Formalism.UG.intL L) M := Fintype.equivOfCardEq hcard
  let B : Matrix (Fin n) (Fin n) L := Matrix.of fun i j => v (e j) i
  have hli : LinearIndependent L (fun j => v (e j)) := hC.comp e e.injective
  have hu : IsUnit B := Matrix.linearIndependent_cols_iff_isUnit.1 (by
    have hcol : B.col = fun j => v (e j) := by funext j i; rfl
    rw [hcol]; exact hli)
  have hBx : ∀ y : Fin n → L, B *ᵥ y = ∑ j, y j • v (e j) := by
    intro y; funext i; simp [B, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hrg : (Set.range fun j => v (e j)) = Set.range v := e.surjective.range_comp v
  have hspR' : Submodule.span (Formalism.UG.intL L) (Set.range fun j => v (e j)) = M := by rw [hrg, hspR]
  have key : ∀ y, y ∈ M ↔ y ∈ Submodule.span (Formalism.UG.intL L) (Set.range fun j => v (e j)) := fun y => by
    rw [hspR']
  refine ⟨hu.unit, fun x => ?_⟩
  rw [IsUnit.unit_spec, hBx, key]
  constructor
  · intro hx
    refine Submodule.sum_mem _ fun j _ => ?_
    have := Submodule.smul_mem (Submodule.span (Formalism.UG.intL L) (Set.range fun j => v (e j))) (⟨x j, hx j⟩ : (Formalism.UG.intL L))
      (Submodule.subset_span ⟨j, rfl⟩)
    exact this
  · intro hx i
    rw [Submodule.mem_span_range_iff_exists_fun] at hx
    obtain ⟨c, hc⟩ := hx
    have h0 := (Fintype.linearIndependent_iff.1 hli) (fun j => (c j : L) - x j) (by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [sub_eq_zero, ← hc]; rfl)
    have := h0 i
    rw [sub_eq_zero] at this
    rw [← this]; exact (c i).2

end Alg

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (F E) in
def genAt (v : Pl (F := F)) : Set (AE F E) := {z : AE F E | ∃ a : AF F, At (evFin F v) a ∧
  evFin F v a ∈ v.adicCompletionIntegers F ∧ ∃ o : 𝓞 E, z = a • inclR (F := F) (AF F) (o : E)}

theorem at_mul {v : Pl (F := F)} {z : AE F E} (hz : At (evFin F v) z) (y : AE F E) : At (evFin F v) (z * y) :=
  fun u hu => by rw [← smul_mul_assoc, hz u hu, zero_mul]

theorem at_smul_one {v : Pl (F := F)} {a : AF F} (ha : At (evFin F v) a) : At (evFin F v) (a • (1 : AE F E)) :=
  fun u hu => by rw [smul_smul, ← smul_eq_mul, ha u hu, zero_smul]

theorem mul_incl_mem {v : Pl (F := F)} {s : AE F E} (hs : s ∈ AddSubgroup.closure (genAt F E v)) (o : 𝓞 E) :
    s * inclR (F := F) (AF F) (o : E) ∈ AddSubgroup.closure (genAt F E v) := by
  induction hs using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, hev, o', rfl⟩ := hx
    exact AddSubgroup.subset_closure ⟨a, ha, hev, o' * o, by simp [smul_mul_assoc, map_mul]⟩
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | neg x _ hx => rw [neg_mul]; exact neg_mem hx

theorem smul_latAt_mem {n : ℕ} (X : Spc F E n) {v : Pl (F := F)} {a : AF F} (ha : At (evFin F v) a)
    (hev : evFin F v a ∈ v.adicCompletionIntegers F) {z : Fin n → AE F E} (hz : z ∈ GlobalTheory.InertSph.latAt X v) :
    a • z ∈ GlobalTheory.InertSph.latAt X v := by
  unfold GlobalTheory.InertSph.latAt at hz ⊢
  induction hz using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a', ha', hev', y, hy, rfl⟩ := hx
    refine AddSubgroup.subset_closure ⟨a * a', fun u hu => ?_, ?_, y, hy, by rw [smul_smul]⟩
    · have h0 : u * a = 0 := ha u hu
      rw [smul_eq_mul, ← mul_assoc, h0, zero_mul]
    · rw [map_mul]; exact mul_mem hev hev'
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem mul_incl_latAt {n : ℕ} (X : Spc F E n) {v : Pl (F := F)} {s : AE F E}
    (hs : s ∈ AddSubgroup.closure (genAt F E v)) {y : Fin n → E} (hy : y ∈ X.L) :
    (fun i => s * inclR (F := F) (AF F) (y i)) ∈ GlobalTheory.InertSph.latAt X v := by
  induction hs using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, hev, o, rfl⟩ := hx
    refine AddSubgroup.subset_closure ⟨a, ha, hev, o • y, X.L.smul_mem o hy, ?_⟩
    funext i
    show (a • inclR (F := F) (AF F) (o : E)) * inclR (F := F) (AF F) (y i) = a • inclR (F := F) (AF F) ((o • y) i)
    rw [smul_mul_assoc, ← map_mul]; rfl
  | zero => convert (GlobalTheory.InertSph.latAt X v).zero_mem using 1; funext i; simp
  | add x x' _ _ hx hx' => convert add_mem hx hx' using 1; funext i; simp [add_mul]
  | neg x _ hx => convert neg_mem hx using 1; funext i; simp

theorem mul_latAt {n : ℕ} (X : Spc F E n) {v : Pl (F := F)} {s : AE F E}
    (hs : s ∈ AddSubgroup.closure (genAt F E v)) {z : Fin n → AE F E} (hz : z ∈ GlobalTheory.InertSph.latAt X v) :
    (fun i => s * z i) ∈ GlobalTheory.InertSph.latAt X v := by
  unfold GlobalTheory.InertSph.latAt at hz
  induction hz using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, hev, y, hy, rfl⟩ := hx
    have h := smul_latAt_mem X ha hev (mul_incl_latAt X hs hy)
    convert h using 1
    funext i
    simp [mul_smul_comm]
  | zero => convert (GlobalTheory.InertSph.latAt X v).zero_mem using 1; funext i; simp
  | add x x' _ _ hx hx' => convert add_mem hx hx' using 1; funext i; simp [mul_add]
  | neg x _ hx => convert neg_mem hx using 1; funext i; simp

end Adelic

theorem exists_basis_at_inert : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ (n : ℕ) (X : Spc F E n), X.L.IsFullLattice E →
    ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ι : L →+ AE F E),
      Function.Injective ι → (∀ z : AE F E, At (evFin F v) z ↔ ∃ x, ι x = z) → (∀ x y, ι (x * y) = ι x * ι y) →
      (∀ x, x ∈ Formalism.UG.intL L ↔ ι x ∈ AddSubgroup.closure {z : AE F E | ∃ a : AF F, At (evFin F v) a ∧
        evFin F v a ∈ v.adicCompletionIntegers F ∧ ∃ o : 𝓞 E, z = a • inclR (F := F) (AF F) (o : E)}) →
      ∃ P : GL (Fin n) L, (∀ x : Fin n → L, (∀ i, x i ∈ Formalism.UG.intL L) ↔
        (fun i => ι (((P : Matrix (Fin n) (Fin n) L) *ᵥ x) i)) ∈ GlobalTheory.InertSph.latAt X v) := by
  intro F E _ _ _ _ _ v w _ n X hlat L _ _ ι hinj himg hmul hint
  have hint' : ∀ x, x ∈ Formalism.UG.intL L ↔ ι x ∈ AddSubgroup.closure (genAt F E v) := hint
  have h11 : ι 1 * ι 1 = ι 1 := by rw [← hmul, one_mul]
  have hAt1 : At (evFin F v) (ι 1) := (himg _).2 ⟨1, rfl⟩
  have hpre : ∀ z, At (evFin F v) z → ι (GlobalTheory.InertLocFrame.pre ι z) = z := fun z hz =>
    GlobalTheory.InertLocFrame.pre_spec ι ((himg z).1 hz)
  let κ : E → L := fun c => GlobalTheory.InertLocFrame.pre ι (ι 1 * inclR (F := F) (AF F) c)
  have hκ : ∀ c, ι (κ c) = ι 1 * inclR (F := F) (AF F) c := fun c => hpre _ (at_mul hAt1 _)
  have h1mem : ι 1 ∈ AddSubgroup.closure (genAt F E v) := (hint' 1).1 (Formalism.UG.intL L).one_mem
  have hκR : ∀ o : 𝓞 E, κ (o : E) ∈ Formalism.UG.intL L := fun o =>
    (hint' _).2 (by rw [hκ]; exact mul_incl_mem h1mem o)
  obtain ⟨s, hs⟩ := Submodule.IsLattice.fg E X.L (self := hlat.toIsLattice)
  let M : Submodule (Formalism.UG.intL L) (Fin n → L) :=
    Submodule.span (Formalism.UG.intL L) ((fun t : Fin n → E => fun i => κ (t i)) '' (s : Set (Fin n → E)))
  have key1 : ∀ t ∈ X.L, ∃ y ∈ M, ∀ i, ι (y i) = ι 1 * inclR (F := F) (AF F) (t i) := by
    intro t ht
    rw [← hs] at ht
    induction ht using Submodule.span_induction with
    | mem t ht => exact ⟨_, Submodule.subset_span ⟨t, ht, rfl⟩, fun i => hκ _⟩
    | zero => exact ⟨0, M.zero_mem, fun i => by simp⟩
    | add t t' _ _ h h' =>
      obtain ⟨y, hy, e⟩ := h
      obtain ⟨y', hy', e'⟩ := h'
      exact ⟨y + y', M.add_mem hy hy', fun i => by simp [e, e', mul_add]⟩
    | smul o t _ h =>
      obtain ⟨y, hy, e⟩ := h
      refine ⟨(⟨κ (o : E), hκR o⟩ : Formalism.UG.intL L) • y, M.smul_mem _ hy, fun i => ?_⟩
      have ho : (o • t) i = (o : E) * t i := rfl
      show ι (κ (o : E) * y i) = _
      rw [hmul, hκ, e, ho, map_mul]
      linear_combination (inclR (F := F) (AF F) (o : E) * inclR (F := F) (AF F) (t i)) * h11
  have key2 : ∀ z ∈ GlobalTheory.InertSph.latAt X v, ∃ y ∈ M, (fun i => ι (y i)) = z := by
    intro z hz
    unfold GlobalTheory.InertSph.latAt at hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, hev, t, ht, rfl⟩ := hz
      obtain ⟨y, hy, e⟩ := key1 t ht
      have hr : ι (GlobalTheory.InertLocFrame.pre ι (a • (1 : AE F E))) = a • 1 := hpre _ (at_smul_one ha)
      have hrR : GlobalTheory.InertLocFrame.pre ι (a • (1 : AE F E)) ∈ Formalism.UG.intL L :=
        (hint' _).2 (by rw [hr]; exact AddSubgroup.subset_closure ⟨a, ha, hev, 1, by simp⟩)
      refine ⟨(⟨_, hrR⟩ : Formalism.UG.intL L) • y, M.smul_mem _ hy, funext fun i => ?_⟩
      show ι (GlobalTheory.InertLocFrame.pre ι (a • (1 : AE F E)) * y i) = (a • fun i => inclR (F := F) (AF F) (t i)) i
      rw [hmul, e, ← mul_assoc, ← hmul, mul_one, hr, smul_mul_assoc, one_mul]
      rfl
    | zero => exact ⟨0, M.zero_mem, by funext i; simp⟩
    | add z z' _ _ h h' =>
      obtain ⟨y, hy, rfl⟩ := h
      obtain ⟨y', hy', rfl⟩ := h'
      exact ⟨y + y', M.add_mem hy hy', by funext i; simp⟩
    | neg z _ h =>
      obtain ⟨y, hy, rfl⟩ := h
      exact ⟨-y, M.neg_mem hy, by funext i; simp⟩
  have hMem : ∀ y : Fin n → L, y ∈ M ↔ (fun i => ι (y i)) ∈ GlobalTheory.InertSph.latAt X v := by
    intro y
    constructor
    · intro hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨t, ht, rfl⟩ := hy
        have htL : t ∈ X.L := hs ▸ Submodule.subset_span ht
        have := mul_incl_latAt X h1mem htL
        convert this using 1
        funext i
        exact hκ _
      | zero => convert (GlobalTheory.InertSph.latAt X v).zero_mem using 1; funext i; simp
      | add y y' _ _ h h' => convert add_mem h h' using 1; funext i; simp
      | smul r y _ h =>
        have := mul_latAt X ((hint' _).1 r.2) h
        convert this using 1
        funext i
        exact hmul (r : L) (y i)
    · intro h
      obtain ⟨y', hy', e⟩ := key2 _ h
      have : y' = y := funext fun i => hinj (congrFun e i)
      rwa [← this]
  have hκadd : ∀ c d, κ (c + d) = κ c + κ d := fun c d => hinj (by rw [map_add (f := _), hκ, hκ, hκ, map_add (f := _), mul_add])
  have hκmul : ∀ c d, κ (c * d) = κ c * κ d := fun c d => hinj (by
    rw [hmul, hκ, hκ, hκ, map_mul]
    linear_combination (-(inclR (F := F) (AF F) c * inclR (F := F) (AF F) d)) * h11)
  have hκ1 : κ 1 = 1 := hinj (by rw [hκ, (inclR (F := F) (AF F)).map_one, mul_one])
  have hκ0 : κ 0 = 0 := hinj (by rw [hκ, map_zero, mul_zero, map_zero])
  have hκmem : ∀ t ∈ X.L, (fun i => κ (t i)) ∈ M := fun t ht => by
    obtain ⟨y, hy, e⟩ := key1 t ht
    have : y = fun i => κ (t i) := funext fun i => hinj (by rw [e, hκ])
    rwa [← this]
  have hQ : ∀ t : Fin n → E, (fun i => κ (t i)) ∈ Submodule.span L (M : Set (Fin n → L)) := by
    intro t
    have ht : t ∈ Submodule.span E (X.L : Set (Fin n → E)) := by
      rw [hlat.span_eq_top]
      exact Submodule.mem_top
    induction ht using Submodule.span_induction with
    | mem t ht => exact Submodule.subset_span (hκmem t ht)
    | zero => convert (Submodule.span L (M : Set (Fin n → L))).zero_mem using 1; funext i; simp [hκ0]
    | add t t' _ _ h h' => convert add_mem h h' using 1; funext i; simp [hκadd]
    | smul c t _ h =>
      convert Submodule.smul_mem _ (κ c) h using 1
      funext i; simp [hκmul]
  have hsp : Submodule.span L (M : Set (Fin n → L)) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun L (Fin n)).span_eq]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    have hb : Pi.basisFun L (Fin n) i = (fun j => κ (Pi.basisFun E (Fin n) i j)) := by
      funext j
      by_cases h : j = i
      · subst j
        simp [hκ1]
      · simp [Pi.single_eq_of_ne h, hκ0]
    rw [hb]
    exact hQ _
  have hfg : M.FG := Submodule.fg_span ((s.finite_toSet).image _)
  obtain ⟨P, hP⟩ := exists_basis_of_fg M hfg hsp
  exact ⟨P, fun x => (hP x).trans (hMem _)⟩

end GlobalTheory.InertLocBasis
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupportedMatrixIffFrameCoordinatesOfInert
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupportedMatrixIffFrameCoordinatesOfInert
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem GlobalTheory.InertLocFrame.xm_bij_at : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl (F := F)) (n d : ℕ) (L : Type) [Field L] (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      Function.Injective ι → (∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ↔ ∃ x, ι x = z) → (∀ x y, ι (x * y) = ι x * ι y) →
      ∀ (PV : GL (Fin n) L) (PW : GL (Fin d) L) (z : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
        At (evFin F v) z ↔ ∃ x, GlobalTheory.InertLocFrame.xm ι PV PW x = z := by
  intro F E _ _ _ _ _ v n d L _ ι _ him _ PV PW z
  constructor
  · intro hz
    have hent : ∀ i j, ∃ y, ι y = z i j := fun i j => (him (z i j)).1 (fun u hu => by
        have := congrFun (congrFun (hz u hu) i) j
        simpa using this)
    choose y hy using hent
    refine ⟨(((PV⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.of y * ((PW⁻¹ : GL (Fin d) L) : Matrix (Fin d) (Fin d) L)ᵀ)ᵀ, ?_⟩
    rw [GlobalTheory.InertLocFrame.xm_apply, Matrix.transpose_transpose]
    have h1 : (PV : Matrix (Fin n) (Fin n) L) * ((PV⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1 := Units.mul_inv PV
    have h2 : (((PW⁻¹ : GL (Fin d) L) : Matrix (Fin d) (Fin d) L))ᵀ * (PW : Matrix (Fin d) (Fin d) L)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
    have h3 : (PV : Matrix (Fin n) (Fin n) L) * (((PV⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.of y *
        ((PW⁻¹ : GL (Fin d) L) : Matrix (Fin d) (Fin d) L)ᵀ) * (PW : Matrix (Fin d) (Fin d) L)ᵀ = Matrix.of y := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc, h2, Matrix.mul_one]
    rw [h3]
    ext i j
    simp [hy]
  · rintro ⟨x, rfl⟩ u hu
    ext i j
    rw [Matrix.smul_apply, GlobalTheory.InertLocFrame.xm_apply, Matrix.map_apply]
    exact (him _).2 ⟨_, rfl⟩ u hu
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupportedMatrixIffFrameCoordinatesOfInertStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.supported_matrix_iff_frame_coordinates_of_inert : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl (F := F)) (n d : ℕ) (L : Type) [Field L] (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      Function.Injective ι → (∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ↔ ∃ x, ι x = z) → (∀ x y, ι (x * y) = ι x * ι y) →
      ∀ (PV : GL (Fin n) L) (PW : GL (Fin d) L) (z : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
        At (evFin F v) z ↔ ∃ x, GlobalTheory.InertLocFrame.xm ι PV PW x = z := by
  first | exact @GlobalTheory.InertLocFrame.xm_bij_at | exact GlobalTheory.InertLocFrame.xm_bij_at | (intros; apply GlobalTheory.InertLocFrame.xm_bij_at <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceUnimodularHermitianFrameCoordinates
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem GlobalTheory.InertLocFrame.frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a'), B.IsGood σ → G.IsGood B → ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)),
    Formalism.UG.IsInertAt F E v w →
    ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σL : L →+* L) (q : ℕ)
      (δ : L) (ψL : AddChar L ℂ) (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      Formalism.UG.IsUnramInv ϖ σL q → Odd q → (Valued.v δ = 1 ∧ σL δ = -δ) → Function.Injective ι →
      (∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ↔ ∃ x, ι x = z) → (∀ x y, ι (x * y) = ι x * ι y) →
      (∀ x, ι (σL x) = cA σ (ι x)) →
      (∀ x, x ∈ Formalism.UG.intL L ↔ ι x ∈ AddSubgroup.closure {z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) | ∃ a : AF F, At (evFin F v) a ∧
        evFin F v a ∈ v.adicCompletionIntegers F ∧ ∃ o : 𝓞 E, z = a • inclR (F := F) (AF F) (o : E)}) →
      (∀ x, B.ψ (Algebra.trace (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (ι x)) = ψL (x + σL x)) →
      ∃ (JS : GL (Fin a) L) (JT : GL (Fin (a + a')) L)
        (Xm : Matrix (Fin (a + a')) (Fin a) L →+ Matrix (Fin a) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
        (iV : Formalism.UG.UJ σL (JS : Matrix (Fin a) (Fin a) L) →* UA σ G.V.J)
        (iW : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →* UA σ G.W.J),
        JS ∈ Formalism.UG.GLint (Fin a) (Formalism.UG.intL L) ∧ JT ∈ Formalism.UG.GLint (Fin (a + a')) (Formalism.UG.intL L) ∧
        (∀ i j, σL ((JS : Matrix (Fin a) (Fin a) L) i j) = (JS : Matrix (Fin a) (Fin a) L) j i) ∧
        (∀ i j, σL ((JT : Matrix (Fin (a + a')) (Fin (a + a')) L) i j) = (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) j i) ∧
        (∀ x y, B.ψ (⅟(2 : AF F) * symp (R := AF F) (cA σ) (-1) (incM F G.V.J) (incM F G.W.J) (Xm x) (Xm y)) =
          ψL ((GlobalTheory.Hk3.locH σL δ JS JT x y + σL (GlobalTheory.Hk3.locH σL δ JS JT x y)) / 2)) ∧
        (∀ z : Matrix (Fin a) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) z ↔ ∃ x, Xm x = z) ∧
        (∀ u : Matrix (Fin (a + a')) (Fin a) L, (∀ i j, u i j ∈ Formalism.UG.intL L) → Xm u ∈ latAtV G.V G.W v) ∧
        (∀ z ∈ latAtV G.V G.W v, ∃ u : Matrix (Fin (a + a')) (Fin a) L, (∀ i j, u i j ∈ Formalism.UG.intL L) ∧ Xm u = z) ∧
        (∀ g h x, actAB (cA σ) (iV g, iW h) (Xm x) =
          Xm (((h : GL (Fin (a + a')) L) : Matrix (Fin (a + a')) (Fin (a + a')) L) * x *
            (((g : GL (Fin a) L)⁻¹ : GL (Fin a) L) : Matrix (Fin a) (Fin a) L))) ∧
        (∀ g, iV g ∈ UAt σ G.V (evFin F v)) ∧ (∀ h, iW h ∈ UAt σ G.W (evFin F v)) ∧
        (∀ g : Formalism.UG.UJ σL (JS : Matrix (Fin a) (Fin a) L), (g : GL (Fin a) L) ∈ Formalism.UG.GLint (Fin a) (Formalism.UG.intL L) →
          iV g ∈ GlobalTheory.InertSph.KAt σ G.V v) ∧
        (∀ h : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L),
          (h : GL (Fin (a + a')) L) ∈ Formalism.UG.GLint (Fin (a + a')) (Formalism.UG.intL L) → iW h ∈ GlobalTheory.InertSph.KAt σ G.W v) := by
  intro F E _ _ _ _ _ σ B a a' G hB hG v w hin L _ _ _ ϖ σL q δ ψL ι hunr hodd hδ hinj him hmul hσ hint hψ
  have hδne : δ ≠ 0 := fun h0 => by rw [h0, map_zero] at hδ; exact zero_ne_one hδ.1
  have ent : ∀ {m : ℕ} (g : GL (Fin m) L), g ∈ Formalism.UG.GLint (Fin m) (Formalism.UG.intL L) →
      ∀ i j, (g : Matrix (Fin m) (Fin m) L) i j ∈ Formalism.UG.intL L := by
    rintro m g ⟨g0, rfl⟩ i j
    exact ((g0 : Matrix (Fin m) (Fin m) (Formalism.UG.intL L)) i j).2
  obtain ⟨PV, hPV⟩ := GlobalTheory.InertLocBasis.exists_basis_at_inert F E v w hin a G.V hG.hV.lat L ι hinj him hmul hint
  obtain ⟨PW, hPW⟩ := GlobalTheory.InertLocBasis.exists_basis_at_inert F E v w hin (a + a') G.W hG.hW.lat L ι hinj him hmul hint
  obtain ⟨JS, hJS, hJSg, hJSh⟩ := GlobalTheory.T.exists_unimodular_gram_inverse_inertPlace F E σ B hB v w hin a _ _ G.V hG.hV L ϖ σL q ι hunr hinj him hmul hσ hint
    PV hPV
  obtain ⟨JT, hJT, hJTg, hJTh⟩ := GlobalTheory.T.inert_place_unramified_skew_space F E σ B hB v w hin (a + a') _ _ G.W hG.hW L ϖ σL q δ ι hunr hodd hδ hinj
    him hmul hσ hint PW hPW
  obtain ⟨iV, hiV⟩ := GlobalTheory.T.exists_unitary_hom_conjInverseTranspose_at_place F E σ v a G.V L σL ι him hmul hσ PV JS hJSg
  obtain ⟨iW, hiW⟩ := GlobalTheory.T.exists_unitary_hom_frame_conjugation_at_place F E σ v (a + a') G.W L σL δ ι hδne him hmul hσ PW JT hJTg
  have hlat := GlobalTheory.T.mem_tensorLatticeAtPlace_iff_frame_coordinates_integral F E v a (a + a') G.V G.W L ι hinj him hmul hint PV PW hPV hPW
  have e1 : ∀ M : Matrix (Fin a) (Fin (a + a')) L,
      ((PV⁻¹ : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * ((PV : Matrix (Fin a) (Fin a) L) * M) = M := by
    intro M
    rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  have e2 : ∀ M : Matrix (Fin (a + a')) (Fin (a + a')) L,
      (PW : Matrix (Fin (a + a')) (Fin (a + a')) L)ᵀ *
        (((PW⁻¹ : GL (Fin (a + a')) L) : Matrix (Fin (a + a')) (Fin (a + a')) L)ᵀ * M) = M := by
    intro M
    rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.transpose_one, Matrix.one_mul]
  refine ⟨JS, JT, GlobalTheory.InertLocFrame.xm ι PV PW, iV, iW, hJS, hJT, hJSh, hJTh,
    GlobalTheory.T.weil_symplectic_form_frame_coordinates_eq_local_trace F E σ B v a (a + a') G.V G.W L ϖ σL q δ ψL ι hunr hδ hinj him hmul hσ hψ PV JS PW JT hJSg hJTg,
    GlobalTheory.T.supported_matrix_iff_frame_coordinates_of_inert F E v a (a + a') L ι hinj him hmul PV PW, fun u hu => (hlat _).2 ⟨u, hu, rfl⟩,
    fun z hz => (hlat z).1 hz, ?_, fun g => GlobalTheory.T.supported_adelic_unitary_point_of_local_matrix F E σ v a G.V L ι him (iV g) _ (hiV g),
    fun h => GlobalTheory.T.supported_adelic_unitary_point_of_local_matrix F E σ v (a + a') G.W L ι him (iW h) _ (hiW h), ?_, ?_⟩
  · intro g h x
    rw [GlobalTheory.T.frame_coordinates_action_of_identity_off_place F E σ a (a + a') G.V G.W L ι hmul PV PW _ _ (iV g) (iW h) (hiV g) (hiW h) x,
      GlobalTheory.InertLocFrame.xm_apply]
    congr 1
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc, e1, e2]
  · intro g hg
    refine GlobalTheory.T.mem_latticeStabilizer_of_frame_conj_integral F E σ v a G.V L ι hinj him hmul hint PV hPV (iV g)
      (((g : GL (Fin a) L)⁻¹ : GL (Fin a) L) : Matrix (Fin a) (Fin a) L)ᵀ ((g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L)ᵀ
      (fun i j => ent _ (inv_mem hg) j i) (fun i j => ent _ hg j i) (hiV g) ?_
    rw [← map_inv, hiV, Subgroup.coe_inv, inv_inv]
  · intro h hh
    refine GlobalTheory.T.mem_latticeStabilizer_of_frame_conj_integral F E σ v (a + a') G.W L ι hinj him hmul hint PW hPW (iW h)
      ((h : GL (Fin (a + a')) L) : Matrix (Fin (a + a')) (Fin (a + a')) L)
      (((h : GL (Fin (a + a')) L)⁻¹ : GL (Fin (a + a')) L) : Matrix (Fin (a + a')) (Fin (a + a')) L)
      (fun i j => ent _ hh i j) (fun i j => ent _ (inv_mem hh) i j) (hiW h) ?_
    rw [← map_inv, hiW, Subgroup.coe_inv]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceUnimodularHermitianFrameCoordinatesStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlace_unimodular_hermitianFrame_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a'), B.IsGood σ → G.IsGood B → ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)),
    Formalism.UG.IsInertAt F E v w →
    ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σL : L →+* L) (q : ℕ)
      (δ : L) (ψL : AddChar L ℂ) (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      Formalism.UG.IsUnramInv ϖ σL q → Odd q → (Valued.v δ = 1 ∧ σL δ = -δ) → Function.Injective ι →
      (∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ↔ ∃ x, ι x = z) → (∀ x y, ι (x * y) = ι x * ι y) →
      (∀ x, ι (σL x) = cA σ (ι x)) →
      (∀ x, x ∈ Formalism.UG.intL L ↔ ι x ∈ AddSubgroup.closure {z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) | ∃ a : AF F, At (evFin F v) a ∧
        evFin F v a ∈ v.adicCompletionIntegers F ∧ ∃ o : 𝓞 E, z = a • inclR (F := F) (AF F) (o : E)}) →
      (∀ x, B.ψ (Algebra.trace (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (ι x)) = ψL (x + σL x)) →
      ∃ (JS : GL (Fin a) L) (JT : GL (Fin (a + a')) L)
        (Xm : Matrix (Fin (a + a')) (Fin a) L →+ Matrix (Fin a) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
        (iV : Formalism.UG.UJ σL (JS : Matrix (Fin a) (Fin a) L) →* UA σ G.V.J)
        (iW : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →* UA σ G.W.J),
        JS ∈ Formalism.UG.GLint (Fin a) (Formalism.UG.intL L) ∧ JT ∈ Formalism.UG.GLint (Fin (a + a')) (Formalism.UG.intL L) ∧
        (∀ i j, σL ((JS : Matrix (Fin a) (Fin a) L) i j) = (JS : Matrix (Fin a) (Fin a) L) j i) ∧
        (∀ i j, σL ((JT : Matrix (Fin (a + a')) (Fin (a + a')) L) i j) = (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) j i) ∧
        (∀ x y, B.ψ (⅟(2 : AF F) * symp (R := AF F) (cA σ) (-1) (incM F G.V.J) (incM F G.W.J) (Xm x) (Xm y)) =
          ψL ((GlobalTheory.Hk3.locH σL δ JS JT x y + σL (GlobalTheory.Hk3.locH σL δ JS JT x y)) / 2)) ∧
        (∀ z : Matrix (Fin a) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) z ↔ ∃ x, Xm x = z) ∧
        (∀ u : Matrix (Fin (a + a')) (Fin a) L, (∀ i j, u i j ∈ Formalism.UG.intL L) → Xm u ∈ latAtV G.V G.W v) ∧
        (∀ z ∈ latAtV G.V G.W v, ∃ u : Matrix (Fin (a + a')) (Fin a) L, (∀ i j, u i j ∈ Formalism.UG.intL L) ∧ Xm u = z) ∧
        (∀ g h x, actAB (cA σ) (iV g, iW h) (Xm x) =
          Xm (((h : GL (Fin (a + a')) L) : Matrix (Fin (a + a')) (Fin (a + a')) L) * x *
            (((g : GL (Fin a) L)⁻¹ : GL (Fin a) L) : Matrix (Fin a) (Fin a) L))) ∧
        (∀ g, iV g ∈ UAt σ G.V (evFin F v)) ∧ (∀ h, iW h ∈ UAt σ G.W (evFin F v)) ∧
        (∀ g : Formalism.UG.UJ σL (JS : Matrix (Fin a) (Fin a) L), (g : GL (Fin a) L) ∈ Formalism.UG.GLint (Fin a) (Formalism.UG.intL L) →
          iV g ∈ GlobalTheory.InertSph.KAt σ G.V v) ∧
        (∀ h : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L),
          (h : GL (Fin (a + a')) L) ∈ Formalism.UG.GLint (Fin (a + a')) (Formalism.UG.intL L) → iW h ∈ GlobalTheory.InertSph.KAt σ G.W v) := by
  first | exact @GlobalTheory.InertLocFrame.frame | exact GlobalTheory.InertLocFrame.frame | (intros; apply GlobalTheory.InertLocFrame.frame <;> assumption)
end
