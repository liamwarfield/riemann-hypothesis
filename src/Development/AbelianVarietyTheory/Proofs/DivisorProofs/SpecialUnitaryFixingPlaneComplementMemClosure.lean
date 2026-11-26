module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrongApproximationNormOneDivisionQuaternion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartBallExtendByZeroInvariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGLLatticeSpannedByGLColumnsEqFullLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeSpannedByGLColumnsEqIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralizerRegularRationalPointFiniteAdelicComm

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuaternionMatrixEqOfUnitaryDetOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuaternionMatrixEqOfUnitaryDetOne
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.QSA GlobalTheory.PlaneSU
open scoped TensorProduct Quaternion

noncomputable section

namespace GlobalTheory.PlaneSU

section Form

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]

theorem tensor_decomp (b : Module.Basis (Fin 2) F E) (hb0 : b 0 = 1) (z : R ⊗[F] E) :
    ∃ r₀ r₁ : R, z = algebraMap R (R ⊗[F] E) r₀ + algebraMap R (R ⊗[F] E) r₁ * ((1 : R) ⊗ₜ[F] b 1) := by
  let B := Algebra.TensorProduct.basis R b
  have hB : ∀ i, B i = 1 ⊗ₜ[F] b i := fun i => Algebra.TensorProduct.basis_apply b i
  have hz := B.sum_repr z
  rw [Fin.sum_univ_two, hB, hB, hb0, Algebra.smul_def, Algebra.smul_def, ← Algebra.TensorProduct.one_def,
    mul_one] at hz
  exact ⟨B.repr z 0, B.repr z 1, hz.symm⟩

theorem sigR_algebraMap (σ : E →ₐ[F] E) (r : R) :
    sigR R σ (algebraMap R (R ⊗[F] E) r) = algebraMap R (R ⊗[F] E) r := by
  show sigR R σ (r ⊗ₜ[F] 1) = r ⊗ₜ[F] 1
  simp [sigR]

theorem sigR_theta (σ : E →ₐ[F] E) (e : E) (he : σ e = -e) :
    sigR R σ ((1 : R) ⊗ₜ[F] e) = -((1 : R) ⊗ₜ[F] e) := by
  simp [sigR, he, TensorProduct.tmul_neg]

theorem cT_mul_eq_mul_adjugate {A : Type} [CommRing A] (c : A →+* A) (H X : Matrix (Fin 2) (Fin 2) A)
    (hX : Formalism.UG.cT c X * H * X = H) (hd : X.det = 1) : Formalism.UG.cT c X * H = H * X.adjugate := by
  calc Formalism.UG.cT c X * H = Formalism.UG.cT c X * H * (X * X.adjugate) := by
        rw [Matrix.mul_adjugate, hd, one_smul, Matrix.mul_one]
    _ = H * X.adjugate := by rw [← Matrix.mul_assoc, hX]

end Form
end GlobalTheory.PlaneSU

theorem GlobalTheory.PlaneSU.exists_qm_eq_of_unitary : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (δ : F) (b : Module.Basis (Fin 2) F E), b 0 = 1 → σ (b 1) = -b 1 → b 1 * b 1 = algebraMap F E δ → ∀ f₁ f₂ : F, f₁ ≠ 0 → f₂ ≠ 0 → ∀ (R : Type) [CommRing R] [Algebra F R] (X : Matrix (Fin 2) (Fin 2) (R ⊗[F] E)), Formalism.UG.cT (sigR R σ) X * Matrix.diagonal ![algebraMap F (R ⊗[F] E) f₁, algebraMap F (R ⊗[F] E) f₂] * X = Matrix.diagonal ![algebraMap F (R ⊗[F] E) f₁, algebraMap F (R ⊗[F] E) f₂] → X.det = 1 → ∃ x : ℍ[R, algebraMap F R δ, algebraMap F R (-(f₂ / f₁))], qm (algebraMap R (R ⊗[F] E)) ((1 : R) ⊗ₜ[F] b 1) x = X := by
  intro F E _ _ _ σ δ b hb0 hσ _ f₁ f₂ hf₁ _ R _ _ X hX hd
  set ι := algebraMap R (R ⊗[F] E) with hιdef
  set θ : R ⊗[F] E := (1 : R) ⊗ₜ[F] b 1 with hθdef
  set c := sigR R σ with hcdef
  set h₁ := algebraMap F (R ⊗[F] E) f₁ with hh₁
  set h₂ := algebraMap F (R ⊗[F] E) f₂ with hh₂
  set u := algebraMap F (R ⊗[F] E) f₁⁻¹ with hudef
  have key := GlobalTheory.PlaneSU.cT_mul_eq_mul_adjugate c _ X hX hd
  have k00 : c (X 0 0) * h₁ = h₁ * X 1 1 := by
    have := congrFun (congrFun key 0) 0
    simpa [Formalism.UG.cT, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two] using this
  have k01 : c (X 1 0) * h₂ = -(h₁ * X 0 1) := by
    have := congrFun (congrFun key 0) 1
    simpa [Formalism.UG.cT, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two] using this
  have hcθ : c θ = -θ := GlobalTheory.PlaneSU.sigR_theta σ (b 1) hσ
  have hcι : ∀ r, c (ι r) = ι r := GlobalTheory.PlaneSU.sigR_algebraMap σ
  have hu : h₁ * u = 1 := by
    rw [hh₁, hudef, ← map_mul, mul_inv_cancel₀ hf₁, map_one]
  have hb : ι (algebraMap F R (-(f₂ / f₁))) = -(h₂ * u) := by
    rw [hιdef, ← IsScalarTower.algebraMap_apply, div_eq_mul_inv, map_neg, map_mul]
  obtain ⟨r₀, r₁, hα⟩ := GlobalTheory.PlaneSU.tensor_decomp (R := R) b hb0 (X 0 0)
  obtain ⟨s₀, s₁, hβ⟩ := GlobalTheory.PlaneSU.tensor_decomp (R := R) b hb0 (X 1 0)
  have hcα : c (X 0 0) = ι r₀ - ι r₁ * θ := by rw [hα, map_add (f := _), map_mul, hcι, hcι, hcθ]; ring
  have hcβ : c (X 1 0) = ι s₀ - ι s₁ * θ := by rw [hβ, map_add (f := _), map_mul, hcι, hcι, hcθ]; ring
  have e00 : ι r₀ + ι r₁ * θ = X 0 0 := hα.symm
  have e10 : ι s₀ - ι (-s₁) * θ = X 1 0 := by rw [hβ, map_neg]; ring
  have e11 : ι r₀ - ι r₁ * θ = X 1 1 := by
    linear_combination (-1 : R ⊗[F] E) * hcα + u * k00 + (X 1 1 - c (X 0 0)) * hu
  have e01 : ι (algebraMap F R (-(f₂ / f₁))) * (ι s₀ + ι (-s₁) * θ) = X 0 1 := by
    rw [hb, map_neg]
    linear_combination (-u) * k01 + X 0 1 * hu + h₂ * u * hcβ
  refine ⟨⟨r₀, r₁, s₀, -s₁⟩, ?_⟩
  show !![ι r₀ + ι r₁ * θ, ι (algebraMap F R (-(f₂ / f₁))) * (ι s₀ + ι (-s₁) * θ);
    ι s₀ - ι (-s₁) * θ, ι r₀ - ι r₁ * θ] = X
  rw [e00, e01, e10, e11]
  exact (Matrix.eta_fin_two X).symm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuaternionMatrixEqOfUnitaryDetOneStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.QSA GlobalTheory.PlaneSU
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_quaternionMatrix_eq_of_unitary_det_one : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (δ : F) (b : Module.Basis (Fin 2) F E), b 0 = 1 → σ (b 1) = -b 1 → b 1 * b 1 = algebraMap F E δ → ∀ f₁ f₂ : F, f₁ ≠ 0 → f₂ ≠ 0 → ∀ (R : Type) [CommRing R] [Algebra F R] (X : Matrix (Fin 2) (Fin 2) (R ⊗[F] E)), Formalism.UG.cT (sigR R σ) X * Matrix.diagonal ![algebraMap F (R ⊗[F] E) f₁, algebraMap F (R ⊗[F] E) f₂] * X = Matrix.diagonal ![algebraMap F (R ⊗[F] E) f₁, algebraMap F (R ⊗[F] E) f₂] → X.det = 1 → ∃ x : ℍ[R, algebraMap F R δ, algebraMap F R (-(f₂ / f₁))], qm (algebraMap R (R ⊗[F] E)) ((1 : R) ⊗ₜ[F] b 1) x = X := by
  first | exact @GlobalTheory.PlaneSU.exists_qm_eq_of_unitary | exact GlobalTheory.PlaneSU.exists_qm_eq_of_unitary | (intros; apply GlobalTheory.PlaneSU.exists_qm_eq_of_unitary <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrongApproximationQuaternionNormOneSplit
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrongApproximationNormOneSplitQuaternionAlgebra
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrongApproximationSL2Adeles
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrongApproximationSL2Adeles
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

namespace GlobalTheory.StrongApproximationSL2

section General

variable {K R : Type} [CommRing K] [CommRing R] (φ : K →+* R) (ε : R)

def prodMonoid : Submonoid (Matrix (Fin 2) (Fin 2) R) where
  carrier := {x | ∃ γ : Matrix (Fin 2) (Fin 2) K, γ.det = 1 ∧ ∃ h : Matrix (Fin 2) (Fin 2) R,
    h.det = 1 ∧ ε • (h - 1) = h - 1 ∧ x = γ.map φ * h}
  one_mem' := ⟨1, by simp, 1, by simp, by simp, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨γ, hγ, h, hh, hε, rfl⟩ ⟨γ', hγ', h', hh', hε', rfl⟩
    set G := γ'.map φ with hG
    have hGd : G.det = 1 := by
      rw [hG, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hγ', map_one]
    have h1 : G * G.adjugate = 1 := by rw [Matrix.mul_adjugate, hGd, one_smul]
    have h2 : G.adjugate * G = 1 := by rw [Matrix.adjugate_mul, hGd, one_smul]
    have h3 : G.adjugate.det = 1 := by
      have := congrArg Matrix.det h1
      rwa [det_mul, hGd, one_mul, det_one] at this
    refine ⟨γ * γ', by rw [det_mul, hγ, hγ', one_mul], G.adjugate * h * G * h', ?_, ?_, ?_⟩
    · rw [det_mul, det_mul, det_mul, h3, hh, hGd, hh']; simp
    · have e : G.adjugate * h * G * h' - 1 = G.adjugate * (h - 1) * G * h' + (h' - 1) := by
        rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h2, Matrix.sub_mul, Matrix.one_mul]
        abel
      rw [e, smul_add, hε', ← Matrix.smul_mul, ← Matrix.smul_mul, ← Matrix.mul_smul, hε]
    · rw [Matrix.map_mul, ← hG]
      calc γ.map φ * h * (G * h') = γ.map φ * (G * G.adjugate) * h * (G * h') := by rw [h1, Matrix.mul_one]
        _ = _ := by simp only [Matrix.mul_assoc]

theorem upper_mem (hε : ε * ε = ε) (t : K) (s : R) : !![1, φ t + ε * s; 0, 1] ∈ prodMonoid φ ε := by
  refine ⟨!![1, t; 0, 1], by simp [det_fin_two], !![1, ε * s; 0, 1], by simp [det_fin_two], ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [← mul_assoc, hε]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem lower_mem (hε : ε * ε = ε) (t : K) (s : R) : !![1, 0; φ t + ε * s, 1] ∈ prodMonoid φ ε := by
  refine ⟨!![1, 0; t, 1], by simp [det_fin_two], !![1, 0; ε * s, 1], by simp [det_fin_two], ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [← mul_assoc, hε]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem mem_of_elementary (M : Submonoid (Matrix (Fin 2) (Fin 2) R)) (hU : ∀ x : R, !![1, x; 0, 1] ∈ M)
    (hL : ∀ x : R, !![1, 0; x, 1] ∈ M) (g : Matrix (Fin 2) (Fin 2) R) (hg : g.det = 1) (s u : R)
    (hu : (g 1 0 + g 1 1 * s) * u = 1) : g ∈ M := by
  rw [det_fin_two] at hg
  have e : g = !![1, (g 0 0 + g 0 1 * s - 1) * u; 0, 1] * !![1, 0; g 1 0 + g 1 1 * s, 1] *
      !![1, (g 1 1 - 1) * u; 0, 1] * !![1, 0; -s, 1] := by
    have e1 : g * !![1, 0; s, 1] = !![1, (g 0 0 + g 0 1 * s - 1) * u; 0, 1] * !![1, 0; g 1 0 + g 1 1 * s, 1] *
        !![1, (g 1 1 - 1) * u; 0, 1] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
      · linear_combination (-(g 0 0 + g 0 1 * s - 1)) * hu
      · linear_combination (-(g 0 1) - (g 0 0 + g 0 1 * s - 1) * (g 1 1 - 1) * u) * hu - u * hg
      · linear_combination (-(g 1 1 - 1)) * hu
    have e2 : (!![1, 0; s, 1] * !![1, 0; -s, 1] : Matrix (Fin 2) (Fin 2) R) = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [← e1, Matrix.mul_assoc, e2, Matrix.mul_one]
  rw [e]
  exact M.mul_mem (M.mul_mem (M.mul_mem (hU _) (hL _)) (hU _)) (hL _)

theorem exists_unit_of_idem {c d a b : R} (haa : a * a = a) (hbb : b * b = b) (hab : a * b = 0) (hs : a + b = 1)
    (hw : IsUnit (a * c + b * d)) : ∃ s u : R, (c + d * s) * u = 1 := by
  obtain ⟨w, hw⟩ := hw.exists_right_inv
  have h1 : a * c * w = a := by linear_combination a * hw - c * w * haa - d * w * hab
  have h2 : b * d * w = b := by linear_combination b * hw - d * w * hbb - c * w * hab
  refine ⟨b * (1 - c) * w, a * w + b, ?_⟩
  have h3 : c + d * (b * (1 - c) * w) = a * c + b := by linear_combination (1 - c) * h2 - c * hs
  rw [h3]
  linear_combination hs + h1 + hbb + (c + w) * hab + c * w * haa

theorem mem_closure_of_dense [TopologicalSpace R] [IsTopologicalRing R] (hε : ε * ε = ε)
    (hd : ∀ (x : R) (U : Set R), U ∈ 𝓝 x → ∃ t : K, ∃ s : R, φ t + ε * s ∈ U)
    (g : Matrix (Fin 2) (Fin 2) R) (hg : g.det = 1) (s u : R) (hu : (g 1 0 + g 1 1 * s) * u = 1) :
    g ∈ closure (prodMonoid φ ε : Set (Matrix (Fin 2) (Fin 2) R)) := by
  have key : ∀ f : R → Matrix (Fin 2) (Fin 2) R, Continuous f → (∀ t s, f (φ t + ε * s) ∈ prodMonoid φ ε) →
      ∀ x, f x ∈ (prodMonoid φ ε).topologicalClosure := by
    intro f hf h x
    change f x ∈ closure _
    rw [mem_closure_iff_nhds]
    intro V hV
    obtain ⟨t, s, hts⟩ := hd x _ (hf.continuousAt.preimage_mem_nhds hV)
    exact ⟨_, hts, h t s⟩
  refine mem_of_elementary (prodMonoid φ ε).topologicalClosure ?_ ?_ g hg s u hu
  · refine key (fun x => !![1, x; 0, 1]) ?_ (upper_mem φ ε hε)
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · refine key (fun x => !![1, 0; x, 1]) ?_ (lower_mem φ ε hε)
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

end General

theorem idem_of_isPlacesIdem {F : Type} [Field F] [NumberField F] {S₁ : Finset (InfinitePlace F)}
    {S₂ : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F} (h : IsPlacesIdem S₁ S₂ ε) : ε * ε = ε := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine Prod.ext (funext fun w => ?_) (RestrictedProduct.ext _ _ fun v => ?_)
  · change fstA F ε w * fstA F ε w = fstA F ε w
    by_cases hw : w ∈ S₁
    · rw [h1 w hw, one_mul]
    · rw [h2 w hw, zero_mul]
  · change evalV F v (sndA F ε) * evalV F v (sndA F ε) = evalV F v (sndA F ε)
    by_cases hv : v ∈ S₂
    · rw [h3 v hv, one_mul]
    · rw [h4 v hv, zero_mul]

theorem strongApprox_SL2 : ∀ (F : Type) [Field F] [NumberField F], ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → ∀ g : Matrix (Fin 2) (Fin 2) (AF F), g.det = 1 → g ∈ closure {x : Matrix (Fin 2) (Fin 2) (AF F) | ∃ γ : Matrix (Fin 2) (Fin 2) F, γ.det = 1 ∧ ∃ h : Matrix (Fin 2) (Fin 2) (AF F), h.det = 1 ∧ ε • (h - 1) = h - 1 ∧ x = γ.map (algebraMap F (AF F)) * h} := by
  intro F _ _ S₁ S₂ ε hε hS g hg
  have hdet : ∑ i : Fin 2, ![-g 0 1, g 0 0] i * g 1 i = 1 := by
    rw [det_fin_two] at hg
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination hg
  obtain ⟨η, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_orthogonal_idempotents_adele_unit_combination F (Fin 2) (g 1) ![-g 0 1, g 0 0] (hdet ▸ isUnit_one)
  rw [Fin.sum_univ_two] at h3 h4
  obtain ⟨s, u, hu⟩ := exists_unit_of_idem (h1 0) (h1 1) (h2 0 1 (by decide)) h3 h4
  refine mem_closure_of_dense (algebraMap F (AF F)) ε (idem_of_isPlacesIdem hε) (fun x U hU => ?_) g hg s u hu
  obtain ⟨t, -, s, h⟩ := GlobalTheory.T.additive_strongApproximation_avoiding_finset F S₁ S₂ ε hε hS x U hU ∅
  exact ⟨t, s, h⟩

end GlobalTheory.StrongApproximationSL2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrongApproximationSL2AdelesStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strong_approximation_SL2_adeles : ∀ (F : Type) [Field F] [NumberField F], ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → ∀ g : Matrix (Fin 2) (Fin 2) (AF F), g.det = 1 → g ∈ closure {x : Matrix (Fin 2) (Fin 2) (AF F) | ∃ γ : Matrix (Fin 2) (Fin 2) F, γ.det = 1 ∧ ∃ h : Matrix (Fin 2) (Fin 2) (AF F), h.det = 1 ∧ ε • (h - 1) = h - 1 ∧ x = γ.map (algebraMap F (AF F)) * h} := by
  first | exact @GlobalTheory.StrongApproximationSL2.strongApprox_SL2 | exact GlobalTheory.StrongApproximationSL2.strongApprox_SL2 | (intros; apply GlobalTheory.StrongApproximationSL2.strongApprox_SL2 <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuaternionSplitOfIsotropicNorm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitOfIsotropic
noncomputable section

namespace GlobalTheory.MatrixHomBijective

variable {F : Type} [Field F] [CharZero F]

theorem rep_of_sq {a b s t : F} (ha : a ≠ 0) (ht : t ≠ 0) (h : s ^ 2 = a * t ^ 2) :
    ∃ p q : F, b = p ^ 2 - a * q ^ 2 := by
  have hs : s ≠ 0 := by
    rintro rfl
    have : a * t ^ 2 ≠ 0 := mul_ne_zero ha (pow_ne_zero 2 ht)
    exact this (by rw [← h]; ring)
  have ha' : a = s ^ 2 / t ^ 2 := by
    rw [h]; field_simp
  refine ⟨(b + 1) / 2, (b - 1) * t / (2 * s), ?_⟩
  rw [ha']
  field_simp
  ring

theorem rep_of_isotropic {a b : F} (ha : a ≠ 0) (x : QuaternionAlgebra F a 0 b) (hx : x ≠ 0)
    (hn : GlobalTheory.QSA.nrm x = 0) : ∃ p q : F, b = p ^ 2 - a * q ^ 2 := by
  obtain ⟨x0, x1, x2, x3⟩ := x
  simp only [GlobalTheory.QSA.nrm] at hn
  by_cases hd : x2 ^ 2 - a * x3 ^ 2 = 0
  · by_cases h3 : x3 = 0
    · subst h3
      have h2 : x2 = 0 := by
        have : x2 ^ 2 = 0 := by linear_combination hd
        exact pow_eq_zero_iff (two_ne_zero) |>.1 this
      subst h2
      have h1 : x1 ≠ 0 := by
        rintro rfl
        have : x0 ^ 2 = 0 := by linear_combination hn
        have h0 : x0 = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 this
        subst h0
        exact hx rfl
      exact rep_of_sq (s := x0) ha h1 (by linear_combination hn)
    · exact rep_of_sq (s := x2) ha h3 (by linear_combination hd)
  · refine ⟨(x0 * x2 - a * x1 * x3) / (x2 ^ 2 - a * x3 ^ 2),
      (x1 * x2 - x0 * x3) / (x2 ^ 2 - a * x3 ^ 2), ?_⟩
    obtain ⟨d, hdd⟩ : ∃ d, d = x2 ^ 2 - a * x3 ^ 2 := ⟨_, rfl⟩
    rw [← hdd] at hd ⊢
    have key : b * d ^ 2 = (x0 * x2 - a * x1 * x3) ^ 2 - a * (x1 * x2 - x0 * x3) ^ 2 := by
      rw [hdd]
      linear_combination (-(x2 ^ 2 - a * x3 ^ 2)) * hn
    field_simp
    linear_combination key

def mat {a b : F} (p q : F) (x : QuaternionAlgebra F a 0 b) : Matrix (Fin 2) (Fin 2) F :=
  !![x.re + p * x.imJ + a * q * x.imK, a * x.imI - a * q * x.imJ - a * p * x.imK;
    x.imI + q * x.imJ + p * x.imK, x.re - p * x.imJ - a * q * x.imK]

def hom {a b : F} (p q : F) (h : b = p ^ 2 - a * q ^ 2) :
    QuaternionAlgebra F a 0 b →ₐ[F] Matrix (Fin 2) (Fin 2) F where
  toFun := mat p q
  map_one' := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [mat]
  map_mul' x y := by
    subst h
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  map_zero' := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [mat]
  map_add' x y := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mat] <;> ring
  commutes' r := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [mat, QuaternionAlgebra.algebraMap_eq, Matrix.algebraMap_matrix_apply]

theorem mat_bijective {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) (p q : F) (h : b = p ^ 2 - a * q ^ 2) :
    Function.Bijective (mat (a := a) (b := b) p q) := by
  constructor
  · intro x y hxy
    have e00 := congrFun (congrFun hxy 0) 0
    have e01 := congrFun (congrFun hxy 0) 1
    have e10 := congrFun (congrFun hxy 1) 0
    have e11 := congrFun (congrFun hxy 1) 1
    simp only [mat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] at e00 e01 e10 e11
    have two : (2 : F) ≠ 0 := two_ne_zero
    ext
    · apply mul_left_cancel₀ two
      linear_combination e00 + e11
    · apply mul_left_cancel₀ (mul_ne_zero two ha)
      linear_combination e01 + a * e10
    · apply mul_left_cancel₀ (mul_ne_zero two hb)
      linear_combination p * (e00 - e11) - q * (a * e10 - e01) + 2 * (x.imJ - y.imJ) * h
    · apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero two ha) hb)
      linear_combination p * (a * e10 - e01) - a * q * (e00 - e11) + 2 * a * (x.imK - y.imK) * h
  · intro M
    refine ⟨⟨(M 0 0 + M 1 1) / 2, (M 0 1 / a + M 1 0) / 2,
      (p * (M 0 0 - M 1 1) - q * (a * M 1 0 - M 0 1)) / (2 * b),
      (p * (a * M 1 0 - M 0 1) - a * q * (M 0 0 - M 1 1)) / (2 * a * b)⟩, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mat] <;> field_simp <;> rw [h] <;> ring

theorem det_mat {a b : F} (p q : F) (h : b = p ^ 2 - a * q ^ 2) (x : QuaternionAlgebra F a 0 b) :
    (mat p q x).det = GlobalTheory.QSA.nrm x := by
  subst h
  simp only [mat, Matrix.det_fin_two_of, GlobalTheory.QSA.nrm]
  ring

theorem split_of_isotropic (F : Type) [Field F] [NumberField F] (a b : F) (ha : a ≠ 0) (hb : b ≠ 0)
    (hx : ∃ x : QuaternionAlgebra F a 0 b, x ≠ 0 ∧ GlobalTheory.QSA.nrm x = 0) :
    ∃ φ : QuaternionAlgebra F a 0 b ≃ₐ[F] Matrix (Fin 2) (Fin 2) F,
      ∀ x, Matrix.det (φ x) = GlobalTheory.QSA.nrm x := by
  obtain ⟨x, hx, hn⟩ := hx
  obtain ⟨p, q, h⟩ := rep_of_isotropic ha x hx hn
  exact ⟨AlgEquiv.ofBijective (hom p q h) (mat_bijective ha hb p q h), fun y => det_mat p q h y⟩

end GlobalTheory.MatrixHomBijective
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuaternionSplitOfIsotropicNorm
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

namespace GlobalTheory.QSA.Split

variable {F : Type} [Field F]

end GlobalTheory.QSA.Split

namespace GlobalTheory

theorem quaternion_split_of_isotropic : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 →
    (∃ x : ℍ[F, a, b], x ≠ 0 ∧ nrm x = 0) →
    ∃ φ : ℍ[F, a, b] ≃ₐ[F] Matrix (Fin 2) (Fin 2) F, ∀ x, (φ x).det = nrm x := by
  first
  | exact @_root_.GlobalTheory.MatrixHomBijective.split_of_isotropic
  | exact _root_.GlobalTheory.MatrixHomBijective.split_of_isotropic
  | (apply _root_.GlobalTheory.MatrixHomBijective.split_of_isotropic <;> assumption)
  | (intros; apply _root_.GlobalTheory.MatrixHomBijective.split_of_isotropic <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MatrixHomBijective.split_of_isotropic <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MatrixHomBijective.split_of_isotropic ..)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuaternionSplitOfIsotropicNormStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quaternion_split_of_isotropic_norm : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → (∃ x : ℍ[F, a, b], x ≠ 0 ∧ nrm x = 0) → ∃ φ : ℍ[F, a, b] ≃ₐ[F] Matrix (Fin 2) (Fin 2) F, ∀ x, (φ x).det = nrm x := by
  first | exact @GlobalTheory.quaternion_split_of_isotropic | exact GlobalTheory.quaternion_split_of_isotropic | (intros; apply GlobalTheory.quaternion_split_of_isotropic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrongApproximationNormOneSplitQuaternionAlgebra
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

noncomputable section

namespace GlobalTheory.QSA.Split

variable {F : Type} [Field F] [NumberField F] {a b : F}

def qi : ℍ[F, a, b] := ⟨0, 1, 0, 0⟩

def qj : ℍ[F, a, b] := ⟨0, 0, 1, 0⟩

def qk : ℍ[F, a, b] := ⟨0, 0, 0, 1⟩

theorem decomp (y : ℍ[F, a, b]) : y = y.re • (1 : ℍ[F, a, b]) + y.imI • qi + y.imJ • qj + y.imK • qk := by
  ext <;> simp [qi, qj, qk]

theorem map_smul_F (c : F) (M : Matrix (Fin 2) (Fin 2) F) :
    (c • M).map (algebraMap F (AF F)) = algebraMap F (AF F) c • M.map (algebraMap F (AF F)) := by
  ext i j; simp

theorem map_smul_one (c : F) :
    (c • (1 : Matrix (Fin 2) (Fin 2) F)).map (algebraMap F (AF F)) = algebraMap F (AF F) c • 1 := by
  rw [map_smul_F, Matrix.map_one _ (map_zero _) (map_one _)]

variable (φ : ℍ[F, a, b] ≃ₐ[F] Matrix (Fin 2) (Fin 2) F)

def bcBasis : QuaternionAlgebra.Basis (Matrix (Fin 2) (Fin 2) (AF F)) (algebraMap F (AF F) a) 0
    (algebraMap F (AF F) b) where
  i := (φ qi).map (algebraMap F (AF F))
  j := (φ qj).map (algebraMap F (AF F))
  k := (φ qk).map (algebraMap F (AF F))
  i_mul_i := by
    rw [← Matrix.map_mul, ← map_mul]
    have : (qi : ℍ[F, a, b]) * qi = a • 1 := by ext <;> simp [qi]
    rw [this, map_smul, map_one, map_smul_one, zero_smul, add_zero]
  j_mul_j := by
    rw [← Matrix.map_mul, ← map_mul]
    have : (qj : ℍ[F, a, b]) * qj = b • 1 := by ext <;> simp [qj]
    rw [this, map_smul, map_one, map_smul_one]
  i_mul_j := by
    rw [← Matrix.map_mul, ← map_mul]
    have : (qi : ℍ[F, a, b]) * qj = qk := by ext <;> simp [qi, qj, qk]
    rw [this]
  j_mul_i := by
    rw [← Matrix.map_mul, ← map_mul, zero_smul, zero_sub]
    have : (qj : ℍ[F, a, b]) * qi = -qk := by ext <;> simp [qi, qj, qk]
    rw [this, map_neg, Matrix.map_neg _ (map_neg _)]

def Φ : DA F a b →ₐ[AF F] Matrix (Fin 2) (Fin 2) (AF F) := (bcBasis φ).liftHom

theorem Φ_apply (x : DA F a b) : Φ φ x = x.re • (1 : Matrix (Fin 2) (Fin 2) (AF F))
    + x.imI • (φ qi).map (algebraMap F (AF F)) + x.imJ • (φ qj).map (algebraMap F (AF F))
    + x.imK • (φ qk).map (algebraMap F (AF F)) := by
  simp [Φ, QuaternionAlgebra.Basis.liftHom, QuaternionAlgebra.Basis.lift, bcBasis, Algebra.algebraMap_eq_smul_one]

def Ψ (m : Matrix (Fin 2) (Fin 2) (AF F)) : DA F a b :=
  ∑ i, ∑ j, m i j • rat (φ.symm (Matrix.single i j 1))

theorem rat_add (x y : ℍ[F, a, b]) : rat (x + y) = rat x + rat y := by ext <;> simp [rat]

theorem rat_smul (c : F) (x : ℍ[F, a, b]) : rat (c • x) = algebraMap F (AF F) c • rat x := by
  ext <;> simp [rat] <;> rw [Algebra.smul_def]

theorem rat_sum {ι : Type} (s : Finset ι) (f : ι → ℍ[F, a, b]) : rat (∑ i ∈ s, f i) = ∑ i ∈ s, rat (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => ext <;> simp [rat]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, rat_add, ih]

theorem rat_one : rat (1 : ℍ[F, a, b]) = 1 := by ext <;> simp [rat]

theorem Ψ_add (m n : Matrix (Fin 2) (Fin 2) (AF F)) : Ψ φ (m + n) = Ψ φ m + Ψ φ n := by
  simp only [Ψ, Matrix.add_apply, add_smul, Finset.sum_add_distrib]

theorem Ψ_smul (c : AF F) (m : Matrix (Fin 2) (Fin 2) (AF F)) : Ψ φ (c • m) = c • Ψ φ m := by
  simp only [Ψ, Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

theorem Ψ_map (M : Matrix (Fin 2) (Fin 2) F) : Ψ φ (M.map (algebraMap F (AF F))) = rat (φ.symm M) := by
  conv_rhs => rw [Matrix.matrix_eq_sum_single M]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Ψ, Matrix.map_apply, map_sum, rat_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show Matrix.single i j (M i j) = M i j • Matrix.single i j (1 : F) by rw [Matrix.smul_single, smul_eq_mul, mul_one],
    map_smul, rat_smul]

theorem Ψ_one : Ψ φ 1 = 1 := by
  rw [← Matrix.map_one (algebraMap F (AF F)) (map_zero _) (map_one _), Ψ_map, map_one, rat_one]

theorem Φ_rat (y : ℍ[F, a, b]) : Φ φ (rat y) = (φ y).map (algebraMap F (AF F)) := by
  conv_rhs => rw [decomp y]
  simp only [Φ_apply, map_add (f := _), map_smul, map_one, Matrix.map_add (f := _), map_smul_F, Matrix.map_one _ (map_zero _) (map_one (algebraMap F (AF F)))]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply, smul_eq_mul, map_add (f := _), map_mul, rat]
  split_ifs <;> simp

theorem Φ_Ψ (m : Matrix (Fin 2) (Fin 2) (AF F)) : Φ φ (Ψ φ m) = m := by
  conv_rhs => rw [Matrix.matrix_eq_sum_single m]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Ψ, map_sum, map_smul, Φ_rat, AlgEquiv.apply_symm_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ext k l; simp [Matrix.single_apply]

theorem Ψ_Φ (x : DA F a b) : Ψ φ (Φ φ x) = x := by
  rw [Φ_apply, Ψ_add, Ψ_add, Ψ_add, Ψ_smul, Ψ_smul, Ψ_smul, Ψ_smul, Ψ_one, Ψ_map, Ψ_map, Ψ_map]
  simp only [AlgEquiv.symm_apply_apply]
  ext <;> simp [rat, qi, qj, qk]

theorem Ψ_mul (m n : Matrix (Fin 2) (Fin 2) (AF F)) : Ψ φ (m * n) = Ψ φ m * Ψ φ n := by
  conv_lhs => rw [← Φ_Ψ φ m, ← Φ_Ψ φ n, ← map_mul, Ψ_Φ]

theorem det_four {R : Type} [CommRing R] (A₀ A₁ A₂ A₃ : Matrix (Fin 2) (Fin 2) R) (x₀ x₁ x₂ x₃ : R) :
    (x₀ • A₀ + x₁ • A₁ + x₂ • A₂ + x₃ • A₃).det = x₀ ^ 2 * A₀.det + x₁ ^ 2 * A₁.det + x₂ ^ 2 * A₂.det
      + x₃ ^ 2 * A₃.det + x₀ * x₁ * ((A₀ + A₁).det - A₀.det - A₁.det) + x₀ * x₂ * ((A₀ + A₂).det - A₀.det - A₂.det)
      + x₀ * x₃ * ((A₀ + A₃).det - A₀.det - A₃.det) + x₁ * x₂ * ((A₁ + A₂).det - A₁.det - A₂.det)
      + x₁ * x₃ * ((A₁ + A₃).det - A₁.det - A₃.det) + x₂ * x₃ * ((A₂ + A₃).det - A₂.det - A₃.det) := by
  simp [Matrix.det_fin_two]; ring

theorem det_Φ (hφ : ∀ x, (φ x).det = nrm x) (x : DA F a b) : (Φ φ x).det = nrm x := by
  have hd : ∀ y : ℍ[F, a, b], ((φ y).map (algebraMap F (AF F))).det = algebraMap F (AF F) (nrm y) := by
    intro y; rw [← hφ y, RingHom.map_det]; rfl
  have hd2 : ∀ y z : ℍ[F, a, b], ((φ y).map (algebraMap F (AF F)) + (φ z).map (algebraMap F (AF F))).det
      = algebraMap F (AF F) (nrm (y + z)) := by
    intro y z; rw [← Matrix.map_add _ (map_add _), ← map_add (f := _)]; exact hd _
  have h1 : (1 : Matrix (Fin 2) (Fin 2) (AF F)) = (φ 1).map (algebraMap F (AF F)) := by
    rw [map_one, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [Φ_apply, h1, det_four]
  simp only [hd2, hd]
  simp [nrm, qi, qj, qk]
  ring

theorem nrm_Ψ (hφ : ∀ x, (φ x).det = nrm x) (m : Matrix (Fin 2) (Fin 2) (AF F)) : nrm (Ψ φ m) = m.det := by
  rw [← det_Φ φ hφ, Φ_Ψ]

theorem Ψ_cont : Continuous (Ψ φ) := by
  have hc : ∀ x : DA F a b, coords x = QuaternionAlgebra.linearEquivTuple _ _ _ x := fun x => by
    ext k; fin_cases k <;> rfl
  apply continuous_induced_rng.2
  have : (coords ∘ Ψ φ : Matrix (Fin 2) (Fin 2) (AF F) → Fin 4 → AF F) =
      fun m => ∑ i, ∑ j, m i j • coords (rat (φ.symm (Matrix.single i j 1)) : DA F a b) := by
    funext m; simp only [Function.comp, Ψ, hc, map_sum, map_smul]
  rw [this]
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact (continuous_id.matrix_elem i j).smul continuous_const

theorem Ψ_sub_one (m : Matrix (Fin 2) (Fin 2) (AF F)) : Ψ φ (m - 1) = Ψ φ m - 1 := by
  rw [sub_eq_add_neg, Ψ_add, show -(1 : Matrix (Fin 2) (Fin 2) (AF F)) = (-1 : AF F) • 1 by simp, Ψ_smul, Ψ_one]
  simp [sub_eq_add_neg]

end GlobalTheory.QSA.Split


open GlobalTheory.QSA.Split in
theorem GlobalTheory.QSA.strongApprox_split : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → (∃ x : ℍ[F, a, b], x ≠ 0 ∧ nrm x = 0) → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → ∀ g : DA F a b, nrm g = 1 → g ∈ closure (H0 (a := a) (b := b) ε) := by
  intro F _ _ a b ha hb hiso S₁ S₂ ε hε hS g hg
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.quaternion_split_of_isotropic_norm F a b ha hb hiso
  have hdet : (Φ φ g).det = 1 := by rw [det_Φ φ hφ, hg]
  have hcl := GlobalTheory.T.strong_approximation_SL2_adeles F S₁ S₂ ε hε hS (Φ φ g) hdet
  rw [← Ψ_Φ φ g]
  refine map_mem_closure (Ψ_cont φ) hcl ?_
  rintro _ ⟨γ, hγ, h, hh, hεh, rfl⟩
  refine ⟨φ.symm γ, ?_, Ψ φ h, ?_, ?_, ?_⟩
  · rw [← hφ, AlgEquiv.apply_symm_apply, hγ]
  · rw [nrm_Ψ φ hφ, hh]
  · rw [← Ψ_sub_one, ← Ψ_smul, hεh]
  · rw [Ψ_mul, Ψ_map]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrongApproximationNormOneSplitQuaternionAlgebraStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strongApproximation_normOne_splitQuaternionAlgebra : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → (∃ x : ℍ[F, a, b], x ≠ 0 ∧ nrm x = 0) → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → ∀ g : DA F a b, nrm g = 1 → g ∈ closure (H0 (a := a) (b := b) ε) := by
  first | exact @GlobalTheory.QSA.strongApprox_split | exact GlobalTheory.QSA.strongApprox_split | (intros; apply GlobalTheory.QSA.strongApprox_split <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuaternionNormOnePrescribedReAtIdempotent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuaternionNormOnePrescribedReAtIdempotent
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

namespace GlobalTheory

theorem quat_norm_one_re_at_idem : ∀ (R : Type) [CommRing R] (a b ε p q : R), ε * ε = ε → IsUnit a → IsUnit b →
    IsUnit (2 : R) → ε * (b - (p ^ 2 - a * q ^ 2)) = 0 → ∀ t : R, ∃ h : ℍ[R, a, b], nrm h = 1 ∧ ε * h.re = ε * t := by
  intro R _ a b ε p q hε ha hb h2 hE t
  obtain ⟨c, hc⟩ := ((h2.mul ha).mul hb)
  have hu : 2 * a * b * ((c⁻¹ : Rˣ) : R) = 1 := by
    rw [← hc]; simp
  set u : R := ((c⁻¹ : Rˣ) : R) with hu_def
  set l : R := (t ^ 2 - a - 1) * u with hl
  refine ⟨⟨ε * t + (1 - ε), ε * (l * b + 1), ε * (l * a * q), ε * (l * p)⟩, ?_, ?_⟩
  · simp only [nrm]
    linear_combination ((t - 1) ^ 2 + (-a * (l * b + 1) ^ 2 - b * (l * a * q) ^ 2 + a * b * (l * p) ^ 2)) * hε
      - ε * (t ^ 2 - a - 1) * hu - l ^ 2 * a * b * hE
  · show ε * (ε * t + (1 - ε)) = ε * t
    linear_combination (t - 1) * hε

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuaternionNormOnePrescribedReAtIdempotentStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quaternion_norm_one_prescribed_re_at_idempotent : ∀ (R : Type) [CommRing R] (a b ε p q : R), ε * ε = ε → IsUnit a → IsUnit b → IsUnit (2 : R) → ε * (b - (p ^ 2 - a * q ^ 2)) = 0 → ∀ t : R, ∃ h : ℍ[R, a, b], nrm h = 1 ∧ ε * h.re = ε * t := by
  first | exact @GlobalTheory.quat_norm_one_re_at_idem | exact GlobalTheory.quat_norm_one_re_at_idem | (intros; apply GlobalTheory.quat_norm_one_re_at_idem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrongApproximationQuaternionNormOneSplit
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

namespace GlobalTheory.QSA

theorem isPlacesIdem_mul_self {F : Type} [Field F] [NumberField F] {S₁ : Finset (InfinitePlace F)}
    {S₂ : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F} (hε : IsPlacesIdem S₁ S₂ ε) : ε * ε = ε := by
  have h1 : fstA F (ε * ε) = fstA F ε := by
    rw [map_mul]
    funext w
    change fstA F ε w * fstA F ε w = fstA F ε w
    by_cases hw : w ∈ S₁
    · rw [hε.1 w hw, one_mul]
    · rw [hε.2.1 w hw, zero_mul]
  have h2 : sndA F (ε * ε) = sndA F ε := by
    rw [map_mul]
    refine RestrictedProduct.ext _ _ fun v => ?_
    change evalV F v (sndA F ε * sndA F ε) = evalV F v (sndA F ε)
    rw [map_mul]
    by_cases hv : v ∈ S₂
    · rw [hε.2.2.1 v hv, one_mul]
    · rw [hε.2.2.2 v hv, zero_mul]
  exact Prod.ext h1 h2

theorem strongApprox_nrm_one : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → (∃ p q : AF F, ε * (algebraMap F (AF F) b - (p ^ 2 - algebraMap F (AF F) a * q ^ 2)) = 0) → ∀ g : DA F a b, nrm g = 1 → g ∈ closure (H0 (a := a) (b := b) ε) := by
  intro F _ _ a b ha hb S₁ S₂ ε hε hS hpq g hg
  by_cases hiso : ∃ x : ℍ[F, a, b], x ≠ 0 ∧ nrm x = 0
  · exact GlobalTheory.T.strongApproximation_normOne_splitQuaternionAlgebra F a b ha hb hiso S₁ S₂ ε hε hS g hg
  · have hdiv : ∀ x : ℍ[F, a, b], nrm x = 0 → x = 0 := fun x hx =>
      by_contra fun h => hiso ⟨x, h, hx⟩
    obtain ⟨p, q, hpq⟩ := hpq
    refine GlobalTheory.T.mem_closure_normOne_of_strongApproximation F a b ha hb hdiv S₁ S₂ ε hε hS (fun t => ?_) g hg
    have h2 : IsUnit (2 : AF F) := by
      have : IsUnit (algebraMap F (AF F) 2) := (IsUnit.mk0 (2 : F) two_ne_zero).map _
      rwa [map_ofNat] at this
    exact GlobalTheory.T.quaternion_norm_one_prescribed_re_at_idempotent (AF F) (algebraMap F (AF F) a) (algebraMap F (AF F) b) ε p q
      (isPlacesIdem_mul_self hε) ((IsUnit.mk0 a ha).map _) ((IsUnit.mk0 b hb).map _) h2 hpq t

end GlobalTheory.QSA
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrongApproximationQuaternionNormOneSplitStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strongApproximation_quaternion_normOne_split : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → (∃ p q : AF F, ε * (algebraMap F (AF F) b - (p ^ 2 - algebraMap F (AF F) a * q ^ 2)) = 0) → ∀ g : DA F a b, nrm g = 1 → g ∈ closure (H0 (a := a) (b := b) ε) := by
  first | exact @GlobalTheory.QSA.strongApprox_nrm_one | exact GlobalTheory.QSA.strongApprox_nrm_one | (intros; apply GlobalTheory.QSA.strongApprox_nrm_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialUnitaryFixingPlaneComplementMemClosure
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.QSA GlobalTheory.PlaneSU
open scoped TensorProduct Quaternion

namespace GlobalTheory.PlaneSU

theorem plane_closure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → ∀ e₁ e₂ : Fin M → E, hE σ J e₁ e₂ = 0 → hE σ J e₁ e₁ ≠ 0 → hE σ J e₂ e₂ ≠ 0 → (∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J e₁ e₁ / hE σ J e₂ e₂)) = 0) → ∀ g ∈ SUAdelic σ J, (∀ v : Fin M → E, hE σ J e₁ v = 0 → hE σ J e₂ v = 0 → Matrix.mulVec ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) (fun i => inclR (AF F) (v i)) = (fun i => inclR (AF F) (v i))) → g ∈ closure {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h} := by
  intro F E _ _ _ _ _ σ hCM M J hJ S₁ S₂ ε hε hS e₁ e₂ h12 h11 h22 ⟨t, ht⟩ g hg hfix
  obtain ⟨hσσ, hfixF⟩ := GlobalTheory.CMConjInvol.cm_conj_invol_fixed F E σ hCM
  obtain ⟨hs1, hs2, hBA₀, h1₀, h2₀, hker⟩ := GlobalTheory.T.orthogonalAnisotropicPair_planeMatrices_facts F E σ hσσ M J hJ e₁ e₂ h12 h11 h22
  obtain ⟨f₁, hf₁⟩ := hfixF _ hs1
  obtain ⟨f₂, hf₂⟩ := hfixF _ hs2
  have hf₁0 : f₁ ≠ 0 := by rintro rfl; exact h11 (by rw [← hf₁, map_zero])
  have hf₂0 : f₂ ≠ 0 := by rintro rfl; exact h22 (by rw [← hf₂, map_zero])
  obtain ⟨δ, bs, hδ, hb0, hb1, hbb⟩ := GlobalTheory.QuadNormBase.exists_basis F E σ hCM.2.2.1 hσσ
    (GlobalTheory.HermLineZeros.exists_conj_ne hCM)
  have hδ0 : δ ≠ 0 := by rintro rfl; exact hδ ⟨0, by simp⟩
  have hbq0 : -(f₂ / f₁) ≠ 0 := neg_ne_zero.2 (div_ne_zero hf₂0 hf₁0)

  let ιR : E →+* AF F ⊗[F] E := inclR (F := F) (AF F)
  let ι : AF F →+* AF F ⊗[F] E := algebraMap (AF F) (AF F ⊗[F] E)
  let c : AF F ⊗[F] E →+* AF F ⊗[F] E := sigR (AF F) σ
  let θ : AF F ⊗[F] E := (1 : AF F) ⊗ₜ[F] bs 1
  let A := (planeA e₁ e₂).map ιR
  let B := (planeB σ J e₁ e₂).map ιR
  let H := (planeH σ J e₁ e₂).map ιR
  have hιR : ∀ r : F, ιR (algebraMap F E r) = algebraMap F (AF F ⊗[F] E) r := fun r =>
    (Algebra.TensorProduct.includeRight : E →ₐ[F] AF F ⊗[F] E).commutes r
  have hιF : ∀ r : F, ι (algebraMap F (AF F) r) = algebraMap F (AF F ⊗[F] E) r := fun r =>
    (IsScalarTower.algebraMap_apply F (AF F) (AF F ⊗[F] E) r).symm
  have hcR : ∀ x : E, c (ιR x) = ιR (σ x) := fun x => by simp [c, ιR, sigR, inclR]
  have hcι : ∀ s : AF F, c (ι s) = ι s := StrongApprox.sigR_algebraMap σ
  have hcc : ∀ x, c (c x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r y => simp [c, sigR, hσσ]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have hcT : ∀ {m p : Type} (P : Matrix m p E), Formalism.UG.cT c (P.map ιR) = (Formalism.UG.cT (σ : E →+* E) P).map ιR := by
    intro m p P; ext i j; simp [Formalism.UG.cT, hcR]
  have hBA : B * A = 1 := by
    simp only [B, A]; rw [← Matrix.map_mul, hBA₀, Matrix.map_one _ (map_zero ιR) (map_one ιR)]
  have h1 : Formalism.UG.cT c A * J.map ιR = H * B := by
    simp only [A, B, H]; rw [hcT, ← Matrix.map_mul, h1₀, Matrix.map_mul]
  have h2 : J.map ιR * A = Formalism.UG.cT c B * H := by
    simp only [A, B, H]; rw [hcT, ← Matrix.map_mul, h2₀, Matrix.map_mul]
  have hH : H = Matrix.diagonal ![algebraMap F (AF F ⊗[F] E) f₁, algebraMap F (AF F ⊗[F] E) f₂] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [H, planeH, ← hf₁, ← hf₂, hιR]
  have hJu : IsUnit (J.map ιR).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (IsUnit.mk0 _ hJ.2).map _
  have hθ : θ * θ = ι (algebraMap F (AF F) δ) := by
    rw [hιF, Algebra.TensorProduct.tmul_mul_tmul, one_mul, hbb]
    exact (hιR δ)
  have hcθ : c θ = -θ := by simp [c, θ, sigR, hb1, TensorProduct.tmul_neg]
  have hbH : ι (algebraMap F (AF F) (-(f₂ / f₁))) * algebraMap F (AF F ⊗[F] E) f₁ =
      -algebraMap F (AF F ⊗[F] E) f₂ := by
    rw [hιF, ← map_mul, ← map_neg]; congr 1; field_simp
  have hιinj : Function.Injective ι :=
    Algebra.TensorProduct.includeLeft_injective (S := F) (algebraMap F E).injective

  set G : Matrix (Fin M) (Fin M) (AF F ⊗[F] E) := ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E))
    with hGdef
  have hGu : Formalism.UG.cT c G * J.map ιR * G = J.map ιR := ((show HR (AF F) σ J from g).2)
  have hfixM : G * (1 - A * B) = 1 - A * B :=
    GlobalTheory.T.matrix_fixes_lowRankProjector_of_fixes_rationalKernel F E (AF F) M _ _ hBA₀ G (fun v hv => hfix v ((hker v).1 hv).1 ((hker v).1 hv).2)
  obtain ⟨hGemb, hXu⟩ := GlobalTheory.T.unitary_fixing_kernel_eq_oneAddLowRank_of_unitary _ c hcc M (J.map ιR) hJu A B H hBA h1 h2 G hGu hfixM
  have hdetX : (B * G * A).det = 1 := by
    rw [← det_emb hBA, ← hGemb]; exact StrongApprox.mem_SUAdelic.1 hg
  obtain ⟨x, hxX⟩ := GlobalTheory.T.exists_quaternionMatrix_eq_of_unitary_det_one F E σ δ bs hb0 hb1 hbb f₁ f₂ hf₁0 hf₂0 (AF F) (B * G * A) (hH ▸ hXu) hdetX
  have hx1 : nrm x = 1 := by
    apply hιinj
    rw [map_one, ← det_qm ι θ hθ, hxX, hdetX]
  have hpq : ∃ p q : AF F, ε * (algebraMap F (AF F) (-(f₂ / f₁)) - (p ^ 2 - algebraMap F (AF F) δ * q ^ 2)) = 0 := by
    refine GlobalTheory.T.neg_inv_ratio_isNorm_of_neg_ratio_isNorm F E σ δ bs hb0 hb1 hbb f₁ f₂ hf₁0 hf₂0 (AF F) ε t ?_
    have e : inclR (F := F) (AF F) (hE σ J e₁ e₁ / hE σ J e₂ e₂) = algebraMap F (AF F ⊗[F] E) (f₁ / f₂) := by
      rw [← hf₁, ← hf₂, ← map_div₀]; exact hιR _
    rw [← e]; exact ht
  have hxcl : x ∈ closure (H0 (a := δ) (b := -(f₂ / f₁)) ε) :=
    GlobalTheory.T.strongApproximation_quaternion_normOne_split F δ (-(f₂ / f₁)) hδ0 hbq0 S₁ S₂ ε hε hS hpq x hx1

  have hunit : ∀ y : DA F δ (-(f₂ / f₁)), nrm y = 1 →
      Formalism.UG.cT c (emb A B (qm ι θ y)) * J.map ιR * emb A B (qm ι θ y) = J.map ιR := by
    intro y hy
    refine emb_unitary c hBA h1 h2 ?_
    rw [hH]
    exact qm_unitary ι θ c hcι hcθ hθ hbH hy
  have hdet : ∀ y : DA F δ (-(f₂ / f₁)), nrm y = 1 → (emb A B (qm ι θ y)).det = 1 := by
    intro y hy
    rw [det_emb hBA, det_qm ι θ hθ, hy, map_one]
  let Φ : {y : DA F δ (-(f₂ / f₁)) // nrm y = 1} → HA (AF F) σ J := fun y =>
    (⟨Matrix.GeneralLinearGroup.mk'' (emb A B (qm ι θ y.1)) (by rw [hdet y.1 y.2]; exact isUnit_one),
      hunit y.1 y.2⟩ : HR (AF F) σ J)
  have hΦmat : ∀ y, ((HA.mat (AF F) σ J (Φ y)).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) = emb A B (qm ι θ y.1) :=
    fun y => rfl

  have hco : ∀ i, Continuous fun y : DA F δ (-(f₂ / f₁)) => coords y i := fun i =>
    (continuous_apply i).comp continuous_induced_dom
  have hstar : Continuous (star : DA F δ (-(f₂ / f₁)) → DA F δ (-(f₂ / f₁))) := by
    refine continuous_induced_rng.2 (continuous_pi fun i => ?_)
    fin_cases i
    · simpa [coords] using hco 0
    · exact ((hco 1).neg).congr fun y => by simp [coords]
    · exact ((hco 2).neg).congr fun y => by simp [coords]
    · exact ((hco 3).neg).congr fun y => by simp [coords]
  have hE0 := GlobalTheory.T.continuous_oneAddLowRankEmbedding_quaternionMatrix F E δ (-(f₂ / f₁)) M A B θ
  have hnstar : ∀ y : {y : DA F δ (-(f₂ / f₁)) // nrm y = 1}, nrm (star y.1) = 1 := fun y => by
    calc nrm (star y.1) = nrm y.1 := by simp [nrm]
      _ = 1 := y.2
  have hinv : ∀ y, ((Φ y)⁻¹ : HA (AF F) σ J) = Φ ⟨star y.1, hnstar y⟩ := by
    intro y
    refine inv_eq_of_mul_eq_one_right ?_
    apply Subtype.ext; apply Units.ext
    change emb A B (qm ι θ y.1) * emb A B (qm ι θ (star y.1)) = 1
    rw [← emb_mul hBA, ← qm_mul ι θ hθ, mul_star_eq, y.2, map_one, qm_one, emb_one]
  have hΦc : Continuous Φ := by
    have hU : Continuous fun y : {y : DA F δ (-(f₂ / f₁)) // nrm y = 1} => (Φ y : HR (AF F) σ J).1 := by
      refine Units.continuous_iff.2 ⟨hE0.comp continuous_subtype_val, ?_⟩
      have e : (fun y : {y : DA F δ (-(f₂ / f₁)) // nrm y = 1} =>
          ((((Φ y : HR (AF F) σ J).1)⁻¹ : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E))) =
          fun y => emb A B (qm ι θ (star y.1)) := by
        funext y
        have := congrArg (fun z : HA (AF F) σ J => (((z : HR (AF F) σ J).1 : GL (Fin M) (AF F ⊗[F] E)) :
          Matrix (Fin M) (Fin M) (AF F ⊗[F] E))) (hinv y)
        exact this
      rw [e]
      exact hE0.comp (hstar.comp continuous_subtype_val)
    exact continuous_induced_rng.2 hU
  have hg_eq : g = Φ ⟨x, hx1⟩ := by
    apply Subtype.ext; apply Units.ext
    change G = emb A B (qm ι θ x)
    rw [hxX]; exact hGemb
  have hH0N : H0 (a := δ) (b := -(f₂ / f₁)) ε ⊆ {y | nrm y = 1} := by
    rintro _ ⟨γ, hγ, h, hh, -, rfl⟩
    simp [nrm_mul, nrm_rat, hγ, hh]
  have hx' : (⟨x, hx1⟩ : {y : DA F δ (-(f₂ / f₁)) // nrm y = 1}) ∈ closure (Subtype.val ⁻¹' H0 ε) := by
    rw [closure_subtype, Set.image_preimage_eq_inter_range, Subtype.range_coe_subtype, Set.inter_eq_left.2 hH0N]
    exact hxcl
  have hsub : Φ '' (Subtype.val ⁻¹' H0 ε) ⊆
      {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h} := by
    rintro _ ⟨⟨y, hy1⟩, ⟨γ, hγ, h, hh, hεh, hy⟩, rfl⟩
    have hγ1 : nrm (rat γ) = 1 := by rw [nrm_rat, hγ, map_one]
    refine ⟨Φ ⟨rat γ, hγ1⟩, ?_, Φ ⟨h, hh⟩, ?_, ?_⟩
    · refine ⟨StrongApprox.mem_SUAdelic.2 (hdet _ hγ1), ?_⟩
      show HA.mat (AF F) σ J (Φ ⟨rat γ, hγ1⟩) ∈ HFin (AF F) σ J
      have hbE : algebraMap F E (-(f₂ / f₁)) * hE σ J e₁ e₁ = -hE σ J e₂ e₂ := by
        rw [← hf₁, ← hf₂, ← map_mul, ← map_neg]; congr 1; field_simp
      have hdE : IsUnit (emb (planeA e₁ e₂) (planeB σ J e₁ e₂) (qm (algebraMap F E) (bs 1) γ)).det := by
        rw [det_emb hBA₀, det_qm _ _ hbb, hγ, map_one]; exact isUnit_one
      have huE : Formalism.UG.cT (σ : E →+* E) (emb (planeA e₁ e₂) (planeB σ J e₁ e₂) (qm (algebraMap F E) (bs 1) γ)) * J *
          emb (planeA e₁ e₂) (planeB σ J e₁ e₂) (qm (algebraMap F E) (bs 1) γ) = J :=
        emb_unitary (σ : E →+* E) hBA₀ h1₀ h2₀
          (qm_unitary (algebraMap F E) (bs 1) (σ : E →+* E) (fun s => σ.commutes s) hb1 hbb hbE hγ)
      refine ⟨Matrix.GeneralLinearGroup.mk'' _ hdE, huE, ?_⟩
      apply Units.ext
      change (emb (planeA e₁ e₂) (planeB σ J e₁ e₂) (qm (algebraMap F E) (bs 1) γ)).map ιR = emb A B (qm ι θ (rat γ))
      rw [emb_map]
      congr 1
      have hcomp : ιR.comp (algebraMap F E) = ι.comp (algebraMap F (AF F)) :=
        RingHom.ext fun r => (hιR r).trans (hιF r).symm
      have e1 : (qm (algebraMap F E) (bs 1) γ).map ιR = qm (ιR.comp (algebraMap F E)) (ιR (bs 1)) γ := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [qm]
      rw [e1, hcomp]
      ext i j; fin_cases i <;> fin_cases j <;> rfl
    · refine ⟨StrongApprox.mem_SUAdelic.2 (hdet _ hh), fun i j => ?_⟩
      have hεε : ε * ε = ε := by
        have h1 : fstA F (ε * ε) = fstA F ε := by
          rw [map_mul]
          funext w
          change fstA F ε w * fstA F ε w = fstA F ε w
          by_cases hw : w ∈ S₁
          · rw [hε.1 w hw, one_mul]
          · rw [hε.2.1 w hw, zero_mul]
        have h2 : sndA F (ε * ε) = sndA F ε := by
          rw [map_mul]
          refine RestrictedProduct.ext _ _ fun v => ?_
          change evalV F v (sndA F ε * sndA F ε) = evalV F v (sndA F ε)
          rw [map_mul]
          by_cases hv : v ∈ S₂
          · rw [hε.2.2.1 v hv, one_mul]
          · rw [hε.2.2.2 v hv, zero_mul]
        exact Prod.ext h1 h2
      have e2 : qm ι θ h - 1 = ι ε • qm ι θ (h - 1) := by rw [← qm_smul, hεh, qm_sub, qm_one]
      have e : emb A B (qm ι θ h) - 1 = ι ε • (A * qm ι θ (h - 1) * B) := by
        unfold emb; rw [add_sub_cancel_left, e2, Matrix.mul_smul, Matrix.smul_mul]
      change ι ε * (emb A B (qm ι θ h) - 1) i j = (emb A B (qm ι θ h) - 1) i j
      rw [e, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, ← map_mul, hεε]
    · apply Subtype.ext; apply Units.ext
      change emb A B (qm ι θ y) = emb A B (qm ι θ (rat γ)) * emb A B (qm ι θ h)
      rw [show y = rat γ * h from hy, qm_mul ι θ hθ, emb_mul hBA]
  rw [hg_eq]
  exact closure_mono hsub (image_closure_subset_closure_image hΦc ⟨_, hx', rfl⟩)

end GlobalTheory.PlaneSU

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialUnitaryFixingPlaneComplementMemClosureStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.specialUnitary_fixing_plane_complement_mem_closure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → ∀ e₁ e₂ : Fin M → E, hE σ J e₁ e₂ = 0 → hE σ J e₁ e₁ ≠ 0 → hE σ J e₂ e₂ ≠ 0 → (∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J e₁ e₁ / hE σ J e₂ e₂)) = 0) → ∀ g ∈ SUAdelic σ J, (∀ v : Fin M → E, hE σ J e₁ v = 0 → hE σ J e₂ v = 0 → Matrix.mulVec ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) (fun i => inclR (AF F) (v i)) = (fun i => inclR (AF F) (v i))) → g ∈ closure {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h} := by
  first | exact @GlobalTheory.PlaneSU.plane_closure | exact GlobalTheory.PlaneSU.plane_closure | (intros; apply GlobalTheory.PlaneSU.plane_closure <;> assumption)
end
