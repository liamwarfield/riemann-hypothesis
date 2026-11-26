module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.FieldSizeAdjoinKthRoot
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsConstituentHarishChandraRepIffPairingNeZero
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.SymplecticRealPartVanish
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.SymplecticRealPartVanish
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockCompare

theorem map_trace_tensor {F E A B : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    [CommRing A] [CommRing B] [Algebra F A] [Algebra F B] (p : A →ₐ[F] B) (z : A ⊗[F] E) :
    p (Algebra.trace A (A ⊗[F] E) z) =
      Algebra.trace B (B ⊗[F] E) (Algebra.TensorProduct.map p (AlgHom.id F E) z) := by
  have key : ∀ (C : Type) [CommRing C] [Algebra F C] (c : C) (e : E),
      Algebra.trace C (C ⊗[F] E) (c ⊗ₜ[F] e) = c * algebraMap F C (Algebra.trace F E e) := by
    intro C _ _ c e
    have h1 : (c ⊗ₜ[F] e : C ⊗[F] E) = c • ((1 : C) ⊗ₜ[F] e) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h1, map_smul, smul_eq_mul]
    congr 1
    rw [Algebra.trace_apply, Algebra.trace_apply, ← LinearMap.trace_baseChange]
    congr 1
    ext x
    simp
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul a e => rw [Algebra.TensorProduct.map_tmul, key, key, map_mul, AlgHom.commutes]; rfl

theorem map_sesq_sum_eq_zero {A B : Type} [CommRing A] [CommRing B] {m n : ℕ} (q : A →+* B) (σ : A →+* A)
    (hσ : ∀ z, q z = 0 → q (σ z) = 0) (a : Fin m → Fin m → A) (b : Fin n → Fin n → A)
    (x y : Matrix (Fin m) (Fin n) A) (h : x.map q = 0 ∨ y.map q = 0) :
    q (∑ i, ∑ j, ∑ k, ∑ l, σ (y i j) * a k i * b j l * x k l) = 0 := by
  have hk : ∀ i j k l (a b : A), q (σ (y i j) * a * b * x k l) = 0 := by
    intro i j k l a b
    rw [map_mul, map_mul, map_mul]
    rcases h with h | h
    · have h1 : q (x k l) = 0 := congrFun (congrFun h k) l
      rw [h1, mul_zero]
    · have h1 : q (y i j) = 0 := congrFun (congrFun h i) j
      rw [hσ _ h1, zero_mul, zero_mul, zero_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, hk, Finset.sum_const_zero]

theorem map_trace_sesq_eq_zero {F E A B : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    [CommRing A] [CommRing B] [Algebra F A] [Algebra F B] (p : A →ₐ[F] B) (s : E →ₐ[F] E) {m n : ℕ}
    (c : A ⊗[F] E) (a : Fin m → Fin m → A ⊗[F] E) (b : Fin n → Fin n → A ⊗[F] E)
    (x y : Matrix (Fin m) (Fin n) (A ⊗[F] E))
    (h : x.map (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom = 0 ∨
      y.map (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom = 0) :
    p (Algebra.trace A (A ⊗[F] E) (c * ∑ i, ∑ j, ∑ k, ∑ l, sigR A s (y i j) * a k i * b j l * x k l)) = 0 := by
  have hc : ∀ z : A ⊗[F] E, (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom (sigR A s z) =
      sigR B s ((Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [RingHom.map_zero]
    | add a b ha hb => simp only [RingHom.map_add (f := _), ha, hb]
    | tmul a e => rfl
  have hh := map_sesq_sum_eq_zero (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom (sigR A s)
    (fun z hz => by rw [hc, hz, map_zero]) a b x y h
  rw [map_trace_tensor, map_mul]
  erw [hh]
  rw [mul_zero, map_zero]

variable {D : D7}

theorem map_sympl_eq_zero {B : Type} [CommRing B] [Algebra D.host.F B] (p : AF D.host.F →ₐ[D.host.F] B)
    (V W : HSp D) (x y : WA V W)
    (h : x.map (Algebra.TensorProduct.map p (AlgHom.id D.host.F D.host.E)).toRingHom = 0 ∨
      y.map (Algebra.TensorProduct.map p (AlgHom.id D.host.F D.host.E)).toRingHom = 0) :
    p (sympl V W x y) = 0 := by
  unfold sympl hHom
  split_ifs
  · exact map_trace_sesq_eq_zero p D.sp.cm.sig _ (fun k i => incA D (V.gram k i))
      (fun j l => incA D (W.gram j l)) x y h
  · exact map_trace_sesq_eq_zero p D.sp.cm.sig _ (fun k i => incA D (V.gram i k))
      (fun j l => incA D (W.gram l j)) x y h

theorem sympl_parts (D : D7) (V W : HSp D) (x y : WA V W) :
    ((IsRealW V W x ∨ IsRealW V W y) → sndA D.host.F (sympl V W x y) = 0) ∧
      ((x.map (infPart D) = 0 ∨ y.map (infPart D) = 0) → fstA D.host.F (sympl V W x y) = 0) :=
  ⟨fun h => map_sympl_eq_zero (sndA D.host.F) V W x y h, fun h => map_sympl_eq_zero (fstA D.host.F) V W x y h⟩

end GlobalTheory.FockCompare
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.SymplecticRealPartVanishStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplectic_real_part_vanish : ∀ (D : D7) (V W : HSp D) (x y : WA V W), ((IsRealW V W x ∨ IsRealW V W y) → sndA D.host.F (sympl V W x y) = 0) ∧ ((x.map (infPart D) = 0 ∨ y.map (infPart D) = 0) → fstA D.host.F (sympl V W x y) = 0) := by
  first | exact @GlobalTheory.FockCompare.sympl_parts | exact GlobalTheory.FockCompare.sympl_parts | (intros; apply GlobalTheory.FockCompare.sympl_parts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.HeisenbergDerivativeCommutatorRelation
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.HeisenbergDerivativeCommutatorRelation
noncomputable section

open scoped ContDiff

namespace GlobalTheory.FockCompare

section

variable {G R : Type} [AddCommGroup G] [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R]
  {ι : R →+ G} {π : G →+ R} {om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ}

omit [FiniteDimensional ℝ R] in
theorem heisComm_coset (hπ : ∀ x, π (ι x) = x)
    (hf : ∀ (f : G → ℂ), Sm ι f → ∀ (u : R) (w : G), hD ι π om u f w =
      -(Real.pi * Complex.I) * (om (π w) u : ℝ) * f w + fderiv ℝ (fun x : R => f (w + ι x)) 0 u)
    (f : G → ℂ) (h : Sm ι f) (v : R) (w : G) :
    (fun x : R => hD ι π om v f (w + ι x)) = fun x : R =>
      -(Real.pi * Complex.I) * (om (π w + x) v : ℝ) * f (w + ι x) + fderiv ℝ (fun y : R => f (w + ι y)) x v := by
  funext x
  rw [hf f h, map_add (f := _), hπ]
  congr 2
  have e : (fun y : R => f (w + ι x + ι y)) = fun y : R => (fun z : R => f (w + ι z)) (x + y) := by
    funext y; simp only [map_add (f := _), add_assoc]
  rw [e, fderiv_comp_add_left (f := fun z : R => f (w + ι z)), add_zero]

theorem heisComm_hasFDerivAt_om (a v x : R) :
    HasFDerivAt (fun x : R => ((om (a + x) v : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (LinearMap.toContinuousLinearMap (om.flip v))) x := by
  have h := (Complex.ofRealCLM.comp (LinearMap.toContinuousLinearMap (om.flip v))).hasFDerivAt (x := a + x)
  have h2 := h.comp x ((hasFDerivAt_id x).const_add a)
  rw [ContinuousLinearMap.comp_id] at h2
  exact h2

theorem heisComm_contDiff_om (a v : R) : ContDiff ℝ ∞ (fun x : R => ((om (a + x) v : ℝ) : ℂ)) :=
  (Complex.ofRealCLM.comp (LinearMap.toContinuousLinearMap (om.flip v))).contDiff.comp
    (contDiff_const.add contDiff_id)

theorem heisComm_second (hπ : ∀ x, π (ι x) = x)
    (hf : ∀ (f : G → ℂ), Sm ι f → ∀ (u : R) (w : G), hD ι π om u f w =
      -(Real.pi * Complex.I) * (om (π w) u : ℝ) * f w + fderiv ℝ (fun x : R => f (w + ι x)) 0 u)
    (f : G → ℂ) (h : Sm ι f) (u v : R) (w : G) :
    hD ι π om u (hD ι π om v f) w =
      -(Real.pi * Complex.I) * (om (π w) u : ℝ) *
        (-(Real.pi * Complex.I) * (om (π w) v : ℝ) * f w + fderiv ℝ (fun x : R => f (w + ι x)) 0 v) +
      (-(Real.pi * Complex.I) * (om u v : ℝ) * f w +
        -(Real.pi * Complex.I) * (om (π w) v : ℝ) * fderiv ℝ (fun x : R => f (w + ι x)) 0 u +
        fderiv ℝ (fderiv ℝ (fun x : R => f (w + ι x))) 0 u v) := by
  have hfd : ∀ w', ContDiff ℝ ∞ (fderiv ℝ (fun x : R => f (w' + ι x))) := fun w' =>
    (h w').fderiv_right (m := ∞) (by simp)
  have hs : Sm ι (hD ι π om v f) := by
    intro w'
    rw [heisComm_coset hπ hf f h v w']
    exact ((contDiff_const.mul (heisComm_contDiff_om _ _)).mul (h w')).add
      ((hfd w').clm_apply contDiff_const)
  rw [hf _ hs, hf f h v w, heisComm_coset hπ hf f h v w]
  congr 1
  have h1 : HasFDerivAt (fun x : R => f (w + ι x)) (fderiv ℝ (fun x : R => f (w + ι x)) 0) 0 :=
    ((h w).differentiable (by simp) 0).hasFDerivAt
  have h2 : HasFDerivAt (fderiv ℝ (fun x : R => f (w + ι x))) (fderiv ℝ (fderiv ℝ (fun x : R => f (w + ι x))) 0) 0 :=
    ((hfd w).differentiable (by simp) 0).hasFDerivAt
  have h3 := ((((heisComm_hasFDerivAt_om (om := om) (π w) v 0).const_mul (-(Real.pi * Complex.I))).mul h1).add
    (h2.clm_apply (hasFDerivAt_const v 0))).fderiv
  have h4 := congrArg (fun L => L u) h3
  refine Eq.trans h4 ?_
  simp
  ring

end

theorem heisenberg_derivative_commutator :
    ∀ (G R : Type) [AddCommGroup G] [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R]
      (ι : R →+ G) (π : G →+ R) (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ), (∀ x, π (ι x) = x) →
      (∀ (f : G → ℂ), Sm ι f → ∀ (u : R) (w : G), hD ι π om u f w =
        -(Real.pi * Complex.I) * (om (π w) u : ℝ) * f w + fderiv ℝ (fun x : R => f (w + ι x)) 0 u) →
      (∀ u v, om v u = -om u v) → ∀ (f : G → ℂ), Sm ι f → ∀ u v : R,
      hD ι π om u (hD ι π om v f) - hD ι π om v (hD ι π om u f) =
        (-(2 * Real.pi * Complex.I) * (om u v : ℝ)) • f := by
  intro G R _ _ _ _ ι π om hπ hf ha f h u v
  funext w
  have hsym : IsSymmSndFDerivAt ℝ (fun x : R => f (w + ι x)) 0 :=
    (h w).contDiffAt.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
  rw [Pi.sub_apply, heisComm_second hπ hf f h u v, heisComm_second hπ hf f h v u, hsym u v, ha u v]
  simp only [Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

end GlobalTheory.FockCompare

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.HeisenbergDerivativeCommutatorRelationStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergDerivative_commutator_relation : ∀ (G R : Type) [AddCommGroup G] [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R] (ι : R →+ G) (π : G →+ R) (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ), (∀ x, π (ι x) = x) → (∀ (f : G → ℂ), Sm ι f → ∀ (u : R) (w : G), hD ι π om u f w = -(Real.pi * Complex.I) * (om (π w) u : ℝ) * f w + fderiv ℝ (fun x : R => f (w + ι x)) 0 u) → (∀ u v, om v u = -om u v) → ∀ (f : G → ℂ), Sm ι f → ∀ u v : R, hD ι π om u (hD ι π om v f) - hD ι π om v (hD ι π om u f) = (-(2 * Real.pi * Complex.I) * (om u v : ℝ)) • f := by
  first | exact @GlobalTheory.FockCompare.heisenberg_derivative_commutator | exact GlobalTheory.FockCompare.heisenberg_derivative_commutator | (intros; apply GlobalTheory.FockCompare.heisenberg_derivative_commutator <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.HeisenbergDirectionalDerivFormulaAndSmooth
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.HeisenbergDirectionalDerivFormulaAndSmooth
open GlobalTheory.FockCompare
open scoped ContDiff

namespace GlobalTheory.FockCompare

theorem hD_eq_fderiv {G R : Type} [AddCommGroup G] [NormedAddCommGroup R] [NormedSpace ℝ R]
    (ι : R →+ G) (π : G →+ R) (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ) (f : G → ℂ) (hf : Sm ι f) (u : R) (w : G) :
    hD ι π om u f w = -(Real.pi * Complex.I) * (om (π w) u : ℝ) * f w +
      fderiv ℝ (fun x : R => f (w + ι x)) 0 u := by
  have hd : DifferentiableAt ℝ (fun x : R => f (w + ι x)) ((0 : ℝ) • u) :=
    ((hf w).differentiable (by simp)).differentiableAt
  have hl : HasDerivAt (fun t : ℝ => t • u) u 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const u
  have h2 : HasDerivAt (fun t : ℝ => f (w + ι (t • u)))
      (fderiv ℝ (fun x : R => f (w + ι x)) 0 u) 0 := by
    have := hd.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl
    rw [zero_smul] at this
    exact this
  have h0 : HasDerivAt (fun t : ℝ => -(Real.pi * Complex.I) * ((om (π w) (t • u) : ℝ) : ℂ))
      (-(Real.pi * Complex.I) * ((om (π w) u : ℝ) : ℂ)) 0 := by
    refine HasDerivAt.const_mul _ (HasDerivAt.ofReal_comp ?_)
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const (om (π w) u)
  have h3 := (h0.cexp.mul h2).deriv
  unfold hD
  refine Eq.trans h3 ?_
  simp

theorem hD_formula_smooth : ∀ (G R : Type) [AddCommGroup G] [NormedAddCommGroup R] [NormedSpace ℝ R]
    [FiniteDimensional ℝ R] (ι : R →+ G) (π : G →+ R) (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ), (∀ x, π (ι x) = x) →
    ∀ (f : G → ℂ), Sm ι f → ∀ u : R,
      (∀ w, hD ι π om u f w = -(Real.pi * Complex.I) * (om (π w) u : ℝ) * f w +
        fderiv ℝ (fun x : R => f (w + ι x)) 0 u) ∧ Sm ι (hD ι π om u f) := by
  intro G R _ _ _ _ ι π om hπ f hf u
  refine ⟨hD_eq_fderiv ι π om f hf u, fun w => ?_⟩
  have e : (fun x : R => hD ι π om u f (w + ι x)) = fun x : R =>
      -(Real.pi * Complex.I) * ((om.flip u (π w + x) : ℝ) : ℂ) * f (w + ι x) +
        fderiv ℝ (fun y : R => f (w + ι y)) x u := by
    funext x
    rw [hD_eq_fderiv ι π om f hf, map_add π, hπ, LinearMap.flip_apply]
    congr 2
    have := fderiv_comp_add_left (𝕜 := ℝ) (f := fun y : R => f (w + ι y)) (x := 0) x
    rw [add_zero] at this
    rw [← this]
    congr 1
    funext y
    rw [map_add (f := _), add_assoc]
  rw [e]
  have h1 : ContDiff ℝ ∞ fun x : R => (om.flip u (π w + x) : ℝ) :=
    (LinearMap.toContinuousLinearMap (om.flip u)).contDiff.comp (contDiff_const.add contDiff_id)
  refine ContDiff.add (ContDiff.mul (ContDiff.mul contDiff_const
    (Complex.ofRealCLM.contDiff.comp h1)) (hf w)) ?_
  exact ((hf w).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

end GlobalTheory.FockCompare
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.HeisenbergDirectionalDerivFormulaAndSmoothStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergDirectionalDeriv_formula_and_smooth : ∀ (G R : Type) [AddCommGroup G] [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R] (ι : R →+ G) (π : G →+ R) (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ), (∀ x, π (ι x) = x) → ∀ (f : G → ℂ), Sm ι f → ∀ u : R, (∀ w, hD ι π om u f w = -(Real.pi * Complex.I) * (om (π w) u : ℝ) * f w + fderiv ℝ (fun x : R => f (w + ι x)) 0 u) ∧ Sm ι (hD ι π om u f) := by
  first | exact @GlobalTheory.FockCompare.hD_formula_smooth | exact GlobalTheory.FockCompare.hD_formula_smooth | (intros; apply GlobalTheory.FockCompare.hD_formula_smooth <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.RealAdeleExtAndStandardCharacterFormula
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.RealAdeleExtAndStandardCharacterFormula
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockCompare

theorem pair_fst_of_snd {F : Type} [Field F] [NumberField F] (a : AF F) (h : sndA F a = 0) :
    pairA F (fstA F a) 0 = a := Prod.ext rfl h.symm

theorem half_tmul {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (θ : Ainf F ⊗[F] E →+* ℂ)
    (a : AF F) :
    θ (fstA F (algebraMap F (AF F) (1 / 2) * a) ⊗ₜ[F] (1 : E)) = θ (fstA F a ⊗ₜ[F] (1 : E)) / 2 := by
  have h2 : algebraMap F (AF F) (1 / 2) * a + algebraMap F (AF F) (1 / 2) * a = a := by
    rw [← add_mul, ← RingHom.map_add (f := _), add_halves, RingHom.map_one, one_mul]
  conv_rhs => rw [← h2, map_add (f := _), TensorProduct.add_tmul, RingHom.map_add (f := _)]
  ring

theorem valTau_coe {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (a : AF D.host.F) :
    ((valTau θ τ a : ℝ) : ℂ) = θ τ (fstA D.host.F a ⊗ₜ[D.host.F] (1 : D.host.E)) := by
  have h := conj_tmul_one hθ τ (fstA D.host.F a)
  exact Complex.conj_eq_iff_re.1 h

theorem real_adele_ext_and_char : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), Chart θ σ → ∀ a : AF D.host.F, sndA D.host.F a = 0 → ((∀ τ, valTau θ τ a = 0) → a = 0) ∧ ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ψ (algebraMap D.host.F (AF D.host.F) (1 / 2) * a) = Complex.exp (-(Real.pi * Complex.I) * ((∑ τ, valTau θ τ a : ℝ) : ℂ)) := by
  intro D θ σ h a ha
  refine ⟨fun h0 => ?_, fun ψ hψ => ?_⟩
  · have h1 : (a ⊗ₜ[D.host.F] (1 : D.host.E) : AE D) = 0 := by
      refine h.ext _ ?_ fun τ => ?_
      · have e : finPart D (a ⊗ₜ[D.host.F] (1 : D.host.E)) = sndA D.host.F a ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
        rw [e, ha, TensorProduct.zero_tmul]
      · have e : infPart D (a ⊗ₜ[D.host.F] (1 : D.host.E)) = fstA D.host.F a ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
        rw [e, ← valTau_coe h.inf, h0, Complex.ofReal_zero]
    have hinj := Algebra.TensorProduct.includeLeft_injective (R := D.host.F) (S := D.host.F) (A := AF D.host.F)
      (B := D.host.E) (algebraMap D.host.F D.host.E).injective
    apply hinj
    rw [map_zero]
    exact h1
  · have hc := hψ.2.2 θ h.inf (fstA D.host.F (algebraMap D.host.F (AF D.host.F) (1 / 2) * a))
    rw [psiInf, pair_fst_of_snd _ (by rw [map_mul, ha, mul_zero])] at hc
    rw [hc]
    congr 1
    have e : ∀ ρ, θ ρ (fstA D.host.F (algebraMap D.host.F (AF D.host.F) (1 / 2) * a) ⊗ₜ[D.host.F] (1 : D.host.E))
        = ((valTau θ ρ a : ℝ) : ℂ) / 2 := fun ρ => by
      rw [valTau_coe h.inf]
      exact half_tmul (θ ρ) a
    rw [Finset.sum_congr rfl fun ρ _ => e ρ, ← Finset.sum_div, Complex.ofReal_sum]
    push_cast
    ring

end GlobalTheory.FockCompare
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.RealAdeleExtAndStandardCharacterFormulaStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realAdele_ext_and_standardCharacter_formula : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), Chart θ σ → ∀ a : AF D.host.F, sndA D.host.F a = 0 → ((∀ τ, valTau θ τ a = 0) → a = 0) ∧ ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ψ (algebraMap D.host.F (AF D.host.F) (1 / 2) * a) = Complex.exp (-(Real.pi * Complex.I) * ((∑ τ, valTau θ τ a : ℝ) : ℂ)) := by
  first | exact @GlobalTheory.FockCompare.real_adele_ext_and_char | exact GlobalTheory.FockCompare.real_adele_ext_and_char | (intros; apply GlobalTheory.FockCompare.real_adele_ext_and_char <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSubmoduleThetaFunctions
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSubmoduleThetaFunctions
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder

namespace GlobalTheory.FockCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D}

theorem isThetaFun_zero : IsThetaFun ψ V W 0 := {
  quasi γ w := by simp
  level := ⟨⊤, by change IsOpen (Set.univ : Set (WA V W)); exact isOpen_univ, fun u _ _ => by funext w; simp [Heisenberg₂]⟩
  cont := continuous_const
  smooth _ _ _ _ _ := contDiff_const }

theorem isThetaFun_add {f g : WA V W → ℂ} (hf : IsThetaFun ψ V W f) (hg : IsThetaFun ψ V W g) :
    IsThetaFun ψ V W (f + g) := {
  quasi γ w := by simp only [Pi.add_apply, hf.quasi γ w, hg.quasi γ w, mul_add]
  level := by
    obtain ⟨U, hUo, hU⟩ := hf.level
    obtain ⟨U', hU'o, hU'⟩ := hg.level
    refine ⟨U ⊓ U', by change IsOpen ((U : Set (WA V W)) ∩ (U' : Set (WA V W))); exact hUo.inter hU'o, fun u hu hinf => ?_⟩
    have e1 := hU u (AddSubgroup.mem_inf.1 hu).1 hinf
    have e2 := hU' u (AddSubgroup.mem_inf.1 hu).2 hinf
    funext w
    have h1 := congrFun e1 w
    have h2 := congrFun e2 w
    simp only [Heisenberg₂, Pi.add_apply] at h1 h2 ⊢
    rw [mul_add, h1, h2]
  cont := hf.cont.add hg.cont
  smooth k L hL hfin w := (hf.smooth k L hL hfin w).add (hg.smooth k L hL hfin w) }

theorem isThetaFun_smul (c : ℂ) {f : WA V W → ℂ} (hf : IsThetaFun ψ V W f) :
    IsThetaFun ψ V W (c • f) := {
  quasi γ w := by simp only [Pi.smul_apply, smul_eq_mul, hf.quasi γ w, mul_left_comm]
  level := by
    obtain ⟨U, hUo, hU⟩ := hf.level
    refine ⟨U, hUo, fun u hu hinf => ?_⟩
    funext w
    have h1 := congrFun (hU u hu hinf) w
    simp only [Heisenberg₂, Pi.smul_apply, smul_eq_mul] at h1 ⊢
    rw [mul_left_comm, h1]
  cont := continuous_const.mul hf.cont
  smooth k L hL hfin w := contDiff_const.mul (hf.smooth k L hL hfin w) }

theorem exists_thetaSubmodule : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D),
    ∃ M : Submodule ℂ (WA V W → ℂ), ∀ f, f ∈ M ↔ IsThetaFun ψ V W f := by
  intro D ψ V W
  refine ⟨{ carrier := {f | IsThetaFun ψ V W f}
            add_mem' := fun hf hg => isThetaFun_add hf hg
            zero_mem' := isThetaFun_zero
            smul_mem' := fun c _ hf => isThetaFun_smul c hf }, fun f => Iff.rfl⟩

end GlobalTheory.FockCompare
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSubmoduleThetaFunctionsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_submodule_thetaFunctions : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D), ∃ M : Submodule ℂ (WA V W → ℂ), ∀ f, f ∈ M ↔ IsThetaFun ψ V W f := by
  first | exact @GlobalTheory.FockCompare.exists_thetaSubmodule | exact GlobalTheory.FockCompare.exists_thetaSubmodule | (intros; apply GlobalTheory.FockCompare.exists_thetaSubmodule <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsHeisenbergDerivativeLinearOperators
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsHeisenbergDerivativeLinearOperators
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockCompare

attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar in
theorem _root_.GlobalTheory.FockCompare.exists_heisenberg_operators : ∀ (G R : Type) [AddCommGroup G] [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R] (ι : R →+ G) (π : G →+ R) (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ), (∀ x, π (ι x) = x) → (∀ (f : G → ℂ), _root_.GlobalTheory.FockCompare.Sm ι f → ∀ (u : R) (w : G), _root_.GlobalTheory.FockCompare.hD ι π om u f w = -(Real.pi * Complex.I) * (om (π w) u : ℝ) * f w + fderiv ℝ (fun x : R => f (w + ι x)) 0 u) → ∀ (M : Submodule ℂ (G → ℂ)), (∀ f ∈ M, _root_.GlobalTheory.FockCompare.Sm ι f) → (∀ u, ∀ f ∈ M, _root_.GlobalTheory.FockCompare.hD ι π om u f ∈ M) → ∃ Dop : R → Module.End ℂ M, (∀ u (f : M), ((Dop u f : M) : G → ℂ) = _root_.GlobalTheory.FockCompare.hD ι π om u f) ∧ (∀ u v, Dop (u + v) = Dop u + Dop v) ∧ ∀ (c : ℝ) u, Dop (c • u) = (c : ℂ) • Dop u := by
  intro G R _ _ _ _ ι π om _ hform M hSm hM
  have hdiff : ∀ f ∈ M, ∀ w : G, DifferentiableAt ℝ (fun x : R => f (w + ι x)) 0 :=
    fun f hf w => ((hSm f hf w).differentiable (by simp)).differentiableAt
  refine ⟨fun u =>
    { toFun := fun f => ⟨_root_.GlobalTheory.FockCompare.hD ι π om u f, hM u f f.2⟩
      map_add' := ?_
      map_smul' := ?_ }, fun u f => rfl, ?_, ?_⟩
  · intro f g
    ext w
    simp only [Submodule.coe_add, Pi.add_apply]
    rw [hform _ (hSm _ (M.add_mem f.2 g.2)), hform _ (hSm _ f.2), hform _ (hSm _ g.2)]
    have hfun : (fun x : R => ((f : G → ℂ) + g) (w + ι x)) =
        (fun x : R => (f : G → ℂ) (w + ι x)) + fun x : R => (g : G → ℂ) (w + ι x) := rfl
    rw [hfun, fderiv_add (hdiff _ f.2 w) (hdiff _ g.2 w)]
    simp only [Pi.add_apply, ContinuousLinearMap.add_apply]
    ring
  · intro a f
    ext w
    simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [hform _ (hSm _ (M.smul_mem a f.2)), hform _ (hSm _ f.2)]
    have hfun : (fun x : R => (a • (f : G → ℂ)) (w + ι x)) =
        a • fun x : R => (f : G → ℂ) (w + ι x) := rfl
    rw [hfun, fderiv_const_smul (hdiff _ f.2 w)]
    simp only [Pi.smul_apply, smul_eq_mul, ContinuousLinearMap.smul_apply]
    ring
  · intro u v
    ext f w
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, Submodule.coe_add,
      Pi.add_apply]
    rw [hform _ (hSm _ f.2), hform _ (hSm _ f.2), hform _ (hSm _ f.2)]
    simp only [map_add (f := _)]
    push_cast
    ring
  · intro c u
    ext f w
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, SetLike.val_smul,
      Pi.smul_apply, smul_eq_mul]
    rw [hform _ (hSm _ f.2), hform _ (hSm _ f.2)]
    simp only [map_smul, smul_eq_mul, Complex.real_smul]
    push_cast
    ring

end GlobalTheory.FockCompare
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsHeisenbergDerivativeLinearOperatorsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heisenberg_derivative_linear_operators : ∀ (G R : Type) [AddCommGroup G] [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R] (ι : R →+ G) (π : G →+ R) (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ), (∀ x, π (ι x) = x) → (∀ (f : G → ℂ), Sm ι f → ∀ (u : R) (w : G), hD ι π om u f w = -(Real.pi * Complex.I) * (om (π w) u : ℝ) * f w + fderiv ℝ (fun x : R => f (w + ι x)) 0 u) → ∀ (M : Submodule ℂ (G → ℂ)), (∀ f ∈ M, Sm ι f) → (∀ u, ∀ f ∈ M, hD ι π om u f ∈ M) → ∃ Dop : R → Module.End ℂ M, (∀ u (f : M), ((Dop u f : M) : G → ℂ) = hD ι π om u f) ∧ (∀ u v, Dop (u + v) = Dop u + Dop v) ∧ ∀ (c : ℝ) u, Dop (c • u) = (c : ℂ) • Dop u := by
  first | exact @GlobalTheory.FockCompare.exists_heisenberg_operators | exact GlobalTheory.FockCompare.exists_heisenberg_operators | (intros; apply GlobalTheory.FockCompare.exists_heisenberg_operators <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsFieldIdealsPrincipal
open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField nonZeroDivisors

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldSize.Capit

theorem coeSubmodule_pow {R K : Type} [CommRing R] [CommRing K] [Algebra R K] (I : Ideal R) (k : ℕ) :
    IsLocalization.coeSubmodule K (I ^ k) = IsLocalization.coeSubmodule K I ^ k := by
  induction k with
  | zero => simp [IsLocalization.coeSubmodule_top]
  | succ k ih => rw [pow_succ, pow_succ, IsLocalization.coeSubmodule_mul, ih]

variable {E : Type} [Field E] [NumberField E] (φ : E →+* ℂ)

def intMap (F : IntermediateField ℚ ℂ) (h : ∀ x, φ x ∈ F) : 𝓞 E →+* 𝓞 F :=
  RingOfIntegers.mapRingHom (φ.codRestrict F h)

theorem coe_intMap (F : IntermediateField ℚ ℂ) (h : ∀ x, φ x ∈ F) (a : 𝓞 E) :
    ((intMap φ F h a : F) : ℂ) = φ (a : E) := rfl

theorem intMap_injective (F : IntermediateField ℚ ℂ) (h : ∀ x, φ x ∈ F) :
    Function.Injective (intMap φ F h) := by
  intro a b hab
  have h1 : φ (a : E) = φ (b : E) := by rw [← coe_intMap φ F h, ← coe_intMap φ F h, hab]
  exact RingOfIntegers.ext (φ.injective h1)

def intIncl {F K : IntermediateField ℚ ℂ} (hFK : F ≤ K) : 𝓞 F →+* 𝓞 K :=
  RingOfIntegers.mapRingHom (IntermediateField.inclusion hFK).toRingHom

theorem map_intMap {F K : IntermediateField ℚ ℂ} (hFK : F ≤ K) (h : ∀ x, φ x ∈ F) (I : Ideal (𝓞 E)) :
    I.map (intMap φ K fun x => hFK (h x)) = (I.map (intMap φ F h)).map (intIncl hFK) := by
  rw [Ideal.map_map]; rfl

theorem sz_mono' {F : IntermediateField ℚ ℂ} {a b a' b' : ℝ} (h : Sz F a b) (ha : a ≤ a') (hb : b ≤ b') :
    Sz F a' b' := by
  obtain ⟨i, h1, h2⟩ := h
  exact ⟨i, h1.trans ha, h2.trans hb⟩

theorem step (F : IntermediateField ℚ ℂ) (a b : ℝ) (hF : Sz F a b) (h : ∀ x, φ x ∈ F) (k : ℕ) (hk : 0 < k)
    (I : Ideal (𝓞 E)) (hI : I ≠ ⊥) (hp : ((I ^ k).map (intMap φ F h)).IsPrincipal) :
    ∃ (K : IntermediateField ℚ ℂ) (hFK : F ≤ K), Sz K (a + Real.log k) (b + Real.log k) ∧
      (I.map (intMap φ K fun x => hFK (h x))).IsPrincipal := by
  obtain ⟨y, hy⟩ := hp
  have hy' : (I ^ k).map (intMap φ F h) = Ideal.span {y} := hy
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_zero, Ideal.map_eq_bot_iff_of_injective (intMap_injective φ F h)] at hy'
    exact pow_ne_zero k hI hy'
  have hyF : (y : F) ≠ 0 := fun h0 => hy0 (RingOfIntegers.ext h0)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((y : F) : ℂ) hk
  have hS := GlobalTheory.T.field_size_adjoin_kth_root F a b k (y : F) (IsLocalization.coeSubmodule F (I.map (intMap φ F h))) z hF hk hyF
    (by rw [← coeSubmodule_pow, ← Ideal.map_pow, hy', IsLocalization.coeSubmodule_span_singleton]) hz
  have hzK : z ∈ F ⊔ ℚ⟮z⟯ := (le_sup_right : ℚ⟮z⟯ ≤ F ⊔ ℚ⟮z⟯) (IntermediateField.mem_adjoin_simple_self ℚ z)
  have hFK : F ≤ F ⊔ ℚ⟮z⟯ := le_sup_left
  generalize F ⊔ ℚ⟮z⟯ = K at hS hzK hFK
  refine ⟨K, hFK, hS, ?_⟩
  haveI := finiteDimensional_of_sz hS
  haveI : NumberField K := NumberField.mk
  rw [← IsFractionRing.coeSubmodule_isPrincipal (𝓞 K) K]
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hk.ne'] at hz
    exact hyF (by exact_mod_cast hz.symm)
  refine ⟨⟨z, hzK⟩, GlobalTheory.submodule_eq_span_of_pow_eq_span_pow K _ ⟨z, hzK⟩ k hk
    (fun h0 => hz0 (congrArg Subtype.val h0)) ?_ ?_⟩
  · exact (IsLocalization.coeSubmodule_fg K (RingOfIntegers.coe_injective) _).mpr (IsNoetherian.noetherian _)
  · rw [← coeSubmodule_pow, ← Ideal.map_pow, map_intMap φ hFK h, hy', Ideal.map_span, Set.image_singleton,
      IsLocalization.coeSubmodule_span_singleton]
    congr 2
    apply Subtype.ext
    exact hz.symm

end GlobalTheory.FieldSize.Capit

namespace GlobalTheory.FieldSize

end GlobalTheory.FieldSize
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ContinuousOfIsTheta
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.CoordDnApply
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

namespace GlobalTheory.DualPairCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}
section Gen
variable {R : Type} [CommRing R] {a b : ℕ}

end Gen

open GlobalTheory.IndefiniteRowSideFullHecke

instance topRing (D : D7) : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _

end GlobalTheory.DualPairCompare

end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

namespace GlobalTheory.DualPairCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

open GlobalTheory.IndefiniteRowSideFullHecke

section Gen
variable {M N : Type} [AddCommGroup M] [TopologicalSpace M] [AddCommGroup N] [TopologicalSpace N]

def SmoothAlong (Z : M → Prop) (f : M → ℂ) : Prop :=
  ∀ (k : ℕ) (L : (Fin k → ℝ) →+ M), Continuous L → (∀ t, Z (L t)) → ∀ w, ContDiff ℝ ∞ fun t => f (w + L t)

theorem gen_smooth_iff {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] (Z : M → Prop)
    (r : P →+ M) (hr : Continuous r) (hZ : ∀ p, Z (r p)) (co : M →+ P) (hc : Continuous co)
    (h3 : ∀ z, Z z → r (co z) = z) (f : M → ℂ) :
    SmoothAlong Z f ↔ ∀ w, ContDiff ℝ ∞ fun p => f (w + r p) := by
  constructor
  · intro h w
    let e : P ≃L[ℝ] (Fin (Module.finrank ℝ P) → ℝ) := ContinuousLinearEquiv.ofFinrankEq (by simp)
    have := (h _ (r.comp e.symm.toLinearEquiv.toLinearMap.toAddMonoidHom) (hr.comp e.symm.continuous)
      (fun t => hZ _) w).comp e.contDiff
    convert this using 2 with p
    exact congrArg (fun q => f (w + r q)) (e.symm_apply_apply p).symm
  · intro h k L hL h0 w
    have := (h w).comp ((co.comp L).toRealLinearMap (hc.comp hL)).contDiff
    convert this using 2 with t
    exact congrArg (fun q => f (w + q)) (h3 _ (h0 t)).symm

end Gen

def realMat (D : D7) (m n : ℕ) :
    (Fin m → Fin n → (InfinitePlace D.host.F → ℝ) × (InfinitePlace D.host.F → ℝ)) →+ Matrix (Fin m) (Fin n) (AE D) :=
  AddMonoidHom.mk' (fun p => Matrix.of fun i j => HeisenbergWeilMatrices.realPt D (p i j)) fun p q =>
    Matrix.ext fun i j => (realPtHom D).map_add (p i j) (q i j)

theorem continuous_realMat (D : D7) (m n : ℕ) : Continuous (realMat D m n) :=
  continuous_pi fun i => continuous_pi fun j =>
    (continuous_realPt D).comp ((continuous_apply j).comp (continuous_apply i))

theorem exists_coMat (D : D7) (m n : ℕ) : ∃ co : Matrix (Fin m) (Fin n) (AE D) →+
    (Fin m → Fin n → (InfinitePlace D.host.F → ℝ) × (InfinitePlace D.host.F → ℝ)), Continuous co ∧
    (∀ z, (z - realMat D m n (co z)).map (infPart D) = 0) ∧ ∀ z, z.map (finPart D) = 0 → realMat D m n (co z) = z := by
  obtain ⟨co, h1, h2, h3⟩ := exists_co D
  exact ⟨AddMonoidHom.mk' (fun z i j => co (z i j)) fun z w => funext₂ fun i j => co.map_add _ _,
    continuous_pi fun i => continuous_pi fun j => h1.comp ((continuous_apply j).comp (continuous_apply i)),
    fun z => Matrix.ext fun i j => h2 (z i j),
    fun z hz => Matrix.ext fun i j => h3 (z i j) (congrFun₂ hz i j)⟩

theorem smoothAlong_iff {m n : ℕ} (f : Matrix (Fin m) (Fin n) (AE D) → ℂ) :
    SmoothAlong (fun z => z.map (finPart D) = 0) f ↔ ∀ w, ContDiff ℝ ∞ fun p => f (w + realMat D m n p) := by
  obtain ⟨co, c1, -, c3⟩ := exists_coMat D m n
  exact gen_smooth_iff (fun z : Matrix (Fin m) (Fin n) (AE D) => z.map (finPart D) = 0) (realMat D m n) (continuous_realMat D m n)
    (fun p => Matrix.ext fun i j => finPart_realPt D (p i j)) co c1 c3 f

theorem continuous_cA (D : D7) : Continuous (cA D) :=
  IsModuleTopology.continuous_of_linearMap
    (Algebra.TensorProduct.map (AlgHom.id (AF D.host.F) (AF D.host.F)) D.sp.cm.sig).toLinearMap

end GlobalTheory.DualPairCompare

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.SpanRealProjectionRationalPointsEqTop
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.SpanRealProjectionRationalPointsEqTop
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FockCompare

variable {D : D7}

theorem span_tauE_eq_top {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : Chart θ σ) :
    Submodule.span ℝ (Set.range fun e : D.host.E => fun τ : D.what₂.Tau => tauE D τ e) = ⊤ := by
  set S := Submodule.span ℝ (Set.range fun e : D.host.E => fun τ : D.what₂.Tau => tauE D τ e) with hS
  have hθ := h.inf
  have hcl : IsClosed (S : Set (D.what₂.Tau → ℂ)) := S.closed_of_finiteDimensional
  have key : ∀ y : Ainf D.host.F ⊗[D.host.F] D.host.E, (fun τ => θ τ y) ∈ S := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero =>
      have : (fun τ => θ τ 0) = 0 := by funext τ; exact RingHom.map_zero _
      rw [this]; exact S.zero_mem
    | add a b ha hb =>
      have : (fun τ => θ τ (a + b)) = (fun τ => θ τ a) + fun τ => θ τ b := by
        funext τ; exact RingHom.map_add _ _ _
      rw [this]; exact S.add_mem ha hb
    | tmul a x =>
      have e : ∀ (a : Ainf D.host.F) τ, θ τ (a ⊗ₜ[D.host.F] x) =
          θ τ (a ⊗ₜ[D.host.F] (1 : D.host.E)) * tauE D τ x := by
        intro a τ
        rw [← (hθ τ).1, ← RingHom.map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      have hc : Continuous fun a : Ainf D.host.F => fun τ => θ τ (a ⊗ₜ[D.host.F] x) := by
        refine continuous_pi fun τ => ?_
        simp only [e]
        exact (hθ τ).2.mul continuous_const
      refine DenseRange.induction_on (NumberField.InfiniteAdeleRing.denseRange_algebraMap D.host.F) a
        (hcl.preimage hc) fun f => ?_
      have e1 : (algebraMap D.host.F (Ainf D.host.F) f) ⊗ₜ[D.host.F] (1 : D.host.E) =
          (1 : Ainf D.host.F) ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E f) := by
        exact (Algebra.TensorProduct.includeLeft (R := D.host.F) (S := D.host.F) (A := Ainf D.host.F)
          (B := D.host.E)).commutes f |>.trans
          ((Algebra.TensorProduct.includeRight (R := D.host.F) (A := Ainf D.host.F) (B := D.host.E)).commutes f).symm
      refine Submodule.subset_span ⟨algebraMap D.host.F D.host.E f * x, ?_⟩
      funext τ
      show tauE D τ _ = θ τ ((algebraMap D.host.F (Ainf D.host.F) f) ⊗ₜ[D.host.F] x)
      rw [e, e1, (hθ τ).1, RingHom.map_mul]
  rw [eq_top_iff]
  intro z _
  have := key (infPart D (σ z))
  rwa [show (fun τ => θ τ (infPart D (σ z))) = z from funext fun τ => h.comp z τ] at this

theorem span_piW_ratW_eq_top (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D) (h : Chart θ σ) (V W : HSp D) :
    Submodule.span ℝ (Set.range fun γ : Matrix (Fin V.rank) (Fin W.rank) D.host.E =>
      piW θ V W (ratW V W γ)) = ⊤ := by
  classical
  set T := Submodule.span ℝ (Set.range fun γ : Matrix (Fin V.rank) (Fin W.rank) D.host.E =>
      piW θ V W (ratW V W γ)) with hT
  let L : Fin V.rank → Fin W.rank → (D.what₂.Tau → ℂ) →ₗ[ℝ] RW V W := fun i j =>
    { toFun := fun z τ k l => if i = k ∧ j = l then z τ else 0
      map_add' := fun x y => by funext τ k l; simp only [Pi.add_apply]; split_ifs <;> simp
      map_smul' := fun c x => by funext τ k l; simp only [Pi.smul_apply, RingHom.id_apply]; split_ifs <;> simp }
  have hL : ∀ i j z, L i j z ∈ T := by
    intro i j z
    have hz : z ∈ Submodule.comap (L i j) T := by
      refine (Submodule.span_le.2 ?_ : _ ≤ Submodule.comap (L i j) T) ((span_tauE_eq_top h).ge Submodule.mem_top)
      rintro _ ⟨e, rfl⟩
      refine Submodule.subset_span ⟨Matrix.single i j e, ?_⟩
      funext τ k l
      show θ τ (infPart D (incA D (Matrix.single i j e k l))) = if i = k ∧ j = l then tauE D τ e else 0
      rw [comp_incA h.inf, Matrix.single_apply]
      split_ifs
      · rfl
      · exact RingHom.map_zero _
    exact hz
  rw [eq_top_iff]
  intro z _
  have : z = ∑ i, ∑ j, L i j fun τ => z τ i j := by
    funext τ k l
    simp only [Finset.sum_apply]
    show z τ k l = ∑ i, ∑ j, if i = k ∧ j = l then z τ i j else 0
    simp [ite_and]
  rw [this]
  exact T.sum_mem fun i _ => T.sum_mem fun j _ => hL i j _

end GlobalTheory.FockCompare

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.SpanRealProjectionRationalPointsEqTopStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_realProjection_rationalPoints_eq_top : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), Chart θ σ → ∀ (V W : HSp D), Submodule.span ℝ (Set.range fun γ : Matrix (Fin V.rank) (Fin W.rank) D.host.E => piW θ V W (ratW V W γ)) = ⊤ := by
  first | exact @GlobalTheory.FockCompare.span_piW_ratW_eq_top | exact GlobalTheory.FockCompare.span_piW_ratW_eq_top | (intros; apply GlobalTheory.FockCompare.span_piW_ratW_eq_top <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.BddAboveOfSpanningPeriodsStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.BddAboveOfSpanningPeriods
namespace GlobalTheory

theorem bddAbove_of_spanning_periods (R : Type) [NormedAddCommGroup R] [NormedSpace ℝ R]
    [FiniteDimensional ℝ R] (g : R → ℝ) (hg : Continuous g) (S : Set R)
    (hS : Submodule.span ℝ S = ⊤)
    (hper : ∀ s ∈ S, ∃ N : ℕ, 0 < N ∧ ∀ x, g (x + (N : ℝ) • s) = g x) :
    ∃ C : ℝ, ∀ x, g x ≤ C := by
  classical
  let P : AddSubgroup R :=
    { carrier := {p | ∀ x, g (x + p) = g x}
      zero_mem' := fun x => by simp
      add_mem' := fun {a b} ha hb x => by
        rw [← add_assoc, hb, ha]
      neg_mem' := fun {a} ha x => by
        have := ha (x + -a)
        rw [← this]; simp }
  have hP : Submodule.span ℝ (P : Set R) = ⊤ := by
    rw [eq_top_iff, ← hS, Submodule.span_le]
    intro s hs
    obtain ⟨N, hN, h⟩ := hper s hs
    have h1 : (N : ℝ) • s ∈ Submodule.span ℝ (P : Set R) := Submodule.subset_span h
    have h2 := Submodule.smul_mem _ ((N : ℝ)⁻¹) h1
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    rwa [smul_smul, inv_mul_cancel₀ hN', one_smul] at h2
  obtain ⟨t, htP, hspan, hli⟩ := exists_linearIndependent ℝ (P : Set R)
  have hfin : Finite t := hli.finite
  letI : Fintype t := Fintype.ofFinite t
  let b : Module.Basis t ℝ R := Module.Basis.mk hli (by
    rw [Subtype.range_coe, hspan, hP])
  have hb : Submodule.span ℤ (Set.range b) ≤ AddSubgroup.toIntSubmodule P := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have : b i = (i : R) := by simp [b]
    rw [this]
    exact htP i.2
  have hK : IsCompact (Metric.closedBall (0 : R) (∑ i, ‖b i‖)) := isCompact_closedBall _ _
  obtain ⟨C, hC⟩ := hK.bddAbove_image hg.continuousOn
  refine ⟨C, fun x => ?_⟩
  have hfl : ((ZSpan.floor b x : R)) ∈ P := hb (ZSpan.floor b x).2
  have hx : g x = g (ZSpan.fract b x) := by
    have := hfl (ZSpan.fract b x)
    rw [← this, ZSpan.fract_apply]; simp
  rw [hx]
  apply hC
  exact ⟨_, by simpa using ZSpan.norm_fract_le b x, rfl⟩

end GlobalTheory
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_le_of_continuous_of_spanning_periods : ∀ (R : Type) [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R] (g : R → ℝ), Continuous g → ∀ S : Set R, Submodule.span ℝ S = ⊤ → (∀ s ∈ S, ∃ N : ℕ, 0 < N ∧ ∀ x, g (x + (N : ℝ) • s) = g x) → ∃ C : ℝ, ∀ x, g x ≤ C := by
  first | exact @GlobalTheory.bddAbove_of_spanning_periods | exact GlobalTheory.bddAbove_of_spanning_periods | (intros; apply GlobalTheory.bddAbove_of_spanning_periods <;> assumption)
end
