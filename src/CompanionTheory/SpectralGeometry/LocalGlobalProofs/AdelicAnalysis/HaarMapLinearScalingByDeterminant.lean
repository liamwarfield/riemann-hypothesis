module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarMapLinearScalingByDeterminant
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarMapLinearScalingByDeterminant
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.DetScale

open Matrix
open scoped Pointwise

section Ring

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R]
  [BorelSpace R] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem measurable_mulVec (A : Matrix ι ι R) :
    Measurable (fun x : ι → R => A *ᵥ x) :=
  (continuous_const.matrix_mulVec continuous_id : Continuous fun x : ι → R => A *ᵥ x).measurable

theorem char_smul_map (lam : Measure R) [lam.IsAddHaarMeasure] (u : Rˣ) :
    distribHaarChar R u • lam.map (fun x => (u : R) * x) = lam := by
  have hm : Measurable fun x : R => (u : R) * x :=
    (continuous_const.mul continuous_id).measurable
  ext S hS
  rw [Measure.smul_apply, Measure.map_apply hm hS]
  have h1 := distribHaarChar_mul lam u ((fun x : R => (u : R) * x) ⁻¹' S)
  have e : u • ((fun x : R => (u : R) * x) ⁻¹' S) = S := by
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    simp [Units.smul_def]
  rw [e] at h1
  rw [ENNReal.smul_def, smul_eq_mul]
  exact h1

theorem map_transvection (lam : Measure R) [lam.IsAddHaarMeasure] (i j : ι) (c : R) (hij : i ≠ j) :
    (Measure.pi fun _ : ι => lam).map (fun x => transvection i j c *ᵥ x) =
      Measure.pi fun _ : ι => lam := by
  have ht := measurable_mulVec (transvection i j c)
  refine (Measure.pi_eq fun s hs ↦ ?_).symm
  have h2s : MeasurableSet (Set.univ.pi s) := .pi Set.countable_univ fun i _ ↦ hs i
  simp_rw [← Measure.pi_pi, ← lintegral_indicator_one h2s]
  rw [lintegral_map (measurable_one.indicator h2s) ht]
  refine lintegral_eq_of_lmarginal_eq {i} ((measurable_one.indicator h2s).comp ht)
    (measurable_one.indicator h2s) ?_
  simp_rw [lmarginal_singleton]
  ext x
  simp [transvection, add_mulVec, single_mulVec, hij.symm, ← Function.update_add,
    lintegral_add_right_eq_self fun xᵢ ↦ Set.indicator (Set.univ.pi s) 1 (Function.update x i xᵢ)]

theorem map_diagonal (lam : Measure R) [lam.IsAddHaarMeasure] (d : ι → Rˣ) :
    distribHaarChar R (∏ i, d i) •
        (Measure.pi fun _ : ι => lam).map (fun x => diagonal (fun i => (d i : R)) *ᵥ x) =
      Measure.pi fun _ : ι => lam := by
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.smul_apply, Measure.map_apply (measurable_mulVec _) (MeasurableSet.univ_pi hs)]
  have h1 : (fun x : ι → R => diagonal (fun i => (d i : R)) *ᵥ x) ⁻¹' Set.pi Set.univ s =
      Set.pi Set.univ fun i => (fun y : R => (d i : R) * y) ⁻¹' s i := by
    ext f
    simp [mulVec_diagonal]
  have hm : ∀ i, Measurable fun x : R => (d i : R) * x := fun i =>
    (continuous_const.mul continuous_id).measurable
  rw [h1, Measure.pi_pi, map_prod, ENNReal.smul_def, smul_eq_mul, ENNReal.ofNNReal_finsetProd,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h2 := congrArg (fun m : Measure R => m (s i)) (char_smul_map lam (d i))
  simp only [Measure.smul_apply, Measure.map_apply (hm i) (hs i)] at h2
  rw [← h2]
  rfl

end Ring

theorem smul_map_pi {F : Type} [Field F] {R : Type} [CommRing R] [Algebra F R]
    [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R]
    [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R]
    {ι : Type} [Fintype ι] [DecidableEq ι] (lam : Measure R) [lam.IsAddHaarMeasure]
    (A : Matrix ι ι F) (h : A.det ≠ 0) :
    distribHaarChar R (Units.map (algebraMap F R : F →* R) (Units.mk0 A.det h)) •
        (Measure.pi fun _ : ι => lam).map (fun x => A.map (algebraMap F R) *ᵥ x) =
      Measure.pi fun _ : ι => lam := by
  let u : Fˣ →* Rˣ := Units.map (algebraMap F R : F →* R)
  refine diagonal_transvection_induction_of_det_ne_zero
    (fun A : Matrix ι ι F => ∀ h : A.det ≠ 0, distribHaarChar R (u (Units.mk0 A.det h)) •
        (Measure.pi fun _ : ι => lam).map (fun x => A.map (algebraMap F R) *ᵥ x) =
      Measure.pi fun _ : ι => lam) A h ?_ ?_ ?_ h
  · intro D hD h
    have hD' : ∀ i, D i ≠ 0 := fun i => by
      rw [det_diagonal] at hD
      exact Finset.prod_ne_zero_iff.1 hD i (Finset.mem_univ i)
    have e1 : u (Units.mk0 (diagonal D).det h) = ∏ i, u (Units.mk0 (D i) (hD' i)) := by
      rw [← map_prod]
      congr 1
      ext
      simp [det_diagonal]
    have e2 : (diagonal D).map (algebraMap F R) =
        diagonal fun i => ((u (Units.mk0 (D i) (hD' i)) : Rˣ) : R) := by
      ext a b
      by_cases hab : a = b
      · subst hab
        simp [u]
      · simp [u, hab]
    rw [e1, e2]
    exact map_diagonal lam _
  · intro t h
    obtain ⟨i, j, hij, c⟩ := t
    have e1 : u (Units.mk0 (TransvectionStruct.toMatrix ⟨i, j, hij, c⟩).det h) = 1 := by
      rw [show Units.mk0 (TransvectionStruct.toMatrix ⟨i, j, hij, c⟩).det h = 1 from
        Units.ext (by simpa [TransvectionStruct.toMatrix] using det_transvection_of_ne i j hij c), map_one]
    have e2 : (TransvectionStruct.toMatrix ⟨i, j, hij, c⟩ : Matrix ι ι F).map (algebraMap F R) =
        transvection i j (algebraMap F R c) := by
      ext a b
      simp [TransvectionStruct.toMatrix, transvection, Matrix.add_apply, Matrix.one_apply,
        Matrix.single_apply, apply_ite (algebraMap F R)]
    rw [e1, e2, map_one, one_smul]
    exact map_transvection lam i j _ hij
  · intro A B hA hB IHA IHB h
    have e1 : Units.mk0 (A * B).det h = Units.mk0 A.det hA * Units.mk0 B.det hB :=
      Units.ext (by simp [det_mul])
    have e2 : (fun x : ι → R => (A * B).map (algebraMap F R) *ᵥ x) =
        (fun x => A.map (algebraMap F R) *ᵥ x) ∘ (fun x => B.map (algebraMap F R) *ᵥ x) := by
      ext1 x
      simp [Matrix.map_mul, mulVec_mulVec]
    rw [e1, e2, map_mul, map_mul, mul_smul,
      ← Measure.map_map (measurable_mulVec _) (measurable_mulVec _),
      ← Measure.map_smul _ (measurable_mulVec _).aemeasurable, IHB hB]
    exact IHA hA

theorem map_mulVec_eq_smul : ∀ (F : Type) [Field F] (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R]
    [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R] (ι : Type)
    [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F), A.det ≠ 0 → ∀ (lam : Measure R),
    lam.IsAddHaarMeasure → ∀ c : ℝ≥0, lam.map (fun x => algebraMap F R A.det * x) = c • lam →
    ∀ μ : Measure (ι → R), μ.IsAddHaarMeasure →
      μ.map (fun x => A.map (algebraMap F R) *ᵥ x) = c • μ := by
  intro F _ R _ _ _ _ _ _ _ _ _ ι _ _ A hA lam hlam c hc μ hμ
  have h1 := smul_map_pi lam A hA
  have h2 := char_smul_map lam (Units.map (algebraMap F R : F →* R) (Units.mk0 A.det hA))
  set d := distribHaarChar R (Units.map (algebraMap F R : F →* R) (Units.mk0 A.det hA))
  have h2' : d • lam.map (fun x => algebraMap F R A.det * x) = lam := h2
  rw [hc] at h2'
  obtain ⟨K, hKc, hK0⟩ : ∃ K : Set R, IsCompact K ∧ K ∈ 𝓝 (0 : R) := exists_compact_mem_nhds 0
  have hdc : d * c = 1 := by
    have h3 := congrArg (fun m : Measure R => m K) h2'
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h3
    rw [← mul_assoc, ← ENNReal.coe_mul] at h3
    have h4 : ((d * c : ℝ≥0) : ℝ≥0∞) = 1 :=
      (ENNReal.mul_left_inj (Measure.measure_pos_of_mem_nhds lam hK0).ne' hKc.measure_lt_top.ne).1
        (h3.trans (one_mul _).symm)
    exact_mod_cast h4
  have h4 : (Measure.pi fun _ : ι => lam).map (fun x => A.map (algebraMap F R) *ᵥ x) =
      c • Measure.pi fun _ : ι => lam := by
    conv_rhs => rw [← h1]
    rw [smul_smul, mul_comm c d, hdc, one_smul]
  obtain ⟨k, hk⟩ : ∃ k : ℝ≥0, μ = k • Measure.pi fun _ : ι => lam :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul_of_regular μ (Measure.pi fun _ : ι => lam)⟩
  rw [hk, Measure.map_smul _ (measurable_mulVec _).aemeasurable, h4, smul_comm]

end GlobalTheory.CompanionTheory.SW.DetScale
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarMapLinearScalingByDeterminantStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_map_linear_scaling_by_determinant : ∀ (F : Type) [Field F] (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R] (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F), A.det ≠ 0 → ∀ (lam : Measure R), lam.IsAddHaarMeasure → ∀ c : ℝ≥0, lam.map (fun x => algebraMap F R A.det * x) = c • lam → ∀ μ : Measure (ι → R), μ.IsAddHaarMeasure → μ.map (fun x => A.map (algebraMap F R) *ᵥ x) = c • μ := by
  first | exact @GlobalTheory.CompanionTheory.SW.DetScale.map_mulVec_eq_smul | exact GlobalTheory.CompanionTheory.SW.DetScale.map_mulVec_eq_smul | (intros; apply GlobalTheory.CompanionTheory.SW.DetScale.map_mulVec_eq_smul <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramMatrixLocalGlobal
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramMatrixLocalGlobal
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.GramLocal

section Ring

variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable {R S : Type} [CommRing R] [Algebra F R] [CommRing S] [Algebra F S]

abbrev bcE (E : Type) [Field E] [Algebra F E] (f : R →ₐ[F] S) : R ⊗[F] E →ₐ[F] S ⊗[F] E :=
  Algebra.TensorProduct.map f (AlgHom.id F E)

theorem bcE_inclR (f : R →ₐ[F] S) (e : E) : bcE E f (inclR R e) = inclR S e := by
  simp [inclR, bcE]

theorem bcE_sigR (f : R →ₐ[F] S) (σ : E →ₐ[F] E) (z : R ⊗[F] E) :
    bcE E f (sigR R σ z) = sigR S σ (bcE E f z) := by
  induction z with
  | tmul r e => simp [sigR, bcE]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem bcE_hR (f : R →ₐ[F] S) (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (x y : Fin M → R ⊗[F] E) :
    bcE E f (hR R σ J x y) = hR S σ J (fun i => bcE E f (x i)) (fun i => bcE E f (y i)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hR, hform, map_sum, map_mul, bcE_sigR, JR, Matrix.map_apply, bcE_inclR]

theorem bcE_gramR (f : R →ₐ[F] S) (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X : Fin n → Fin M → R ⊗[F] E) :
    gramR S σ J (fun a i => bcE E f (X a i)) = fun a b => bcE E f (gramR R σ J X a b) := by
  funext a b
  simp only [gramR, bcE_hR]

theorem repr_bcE {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E) (f : R →ₐ[F] S)
    (z : R ⊗[F] E) (k : ι) :
    (Algebra.TensorProduct.basis S b).repr (bcE E f z) k =
      f ((Algebra.TensorProduct.basis R b).repr z k) := by
  induction z with
  | tmul r e => simp [bcE, Algebra.TensorProduct.basis_repr_tmul, Algebra.smul_def]
  | add x y hx hy => simp [map_add (f := _), hx, hy]

theorem gramR_ratTup (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (Y : Fin n → Fin M → E) :
    gramR R σ J (ratTup R Y) = (gramE σ J Y).map (inclR R) := by
  funext a b
  set_option synthInstance.maxHeartbeats 100000 in
    simp [gramR, gramE, hR, hE, hform, ratTup, JR, sigR, inclR, map_sum, map_mul]

end Ring

section Adelic

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E]

theorem adele_ext (x y : AF F) (h1 : fstA F x = fstA F y)
    (h2 : ∀ v, evalV F v (sndA F x) = evalV F v (sndA F y)) : x = y := by
  refine Prod.ext h1 ?_
  exact Subtype.ext (funext h2)

theorem tensor_ext [Module.Finite F E] (z w : AF F ⊗[F] E)
    (h1 : bcE E (fstA F) z = bcE E (fstA F) w)
    (h2 : ∀ v, bcE E (evalV F v) (bcE E (sndA F) z) = bcE E (evalV F v) (bcE E (sndA F) w)) :
    z = w := by
  classical
  let b := Module.finBasis F E
  apply (Algebra.TensorProduct.basis (AF F) b).repr.injective
  ext k
  apply adele_ext
  · rw [← repr_bcE, ← repr_bcE, h1]
  · intro v
    rw [← repr_bcE, ← repr_bcE, ← repr_bcE, ← repr_bcE, h2 v]

end Adelic

theorem gram_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ) (X : (Fin n → Fin M → AF F ⊗[F] E)) (T : Matrix (Fin n) (Fin n) E), (gramR (AF F) σ J X = T.map (inclR (AF F)) ↔ gramR (Ainf F) σ J (projInf X) = T.map (inclR (Ainf F)) ∧ ∀ v, gramR (Fv F v) σ J (projV v (projFin X)) = T.map (inclR (Fv F v))) ∧ ∀ Y : Fin n → Fin M → E, gramR (AF F) σ J (ratTup (AF F) Y) = (gramE σ J Y).map (inclR (AF F)) := by
  intro F E _ _ _ _ _ σ hCM M J _ n X T
  have hfin : Module.Finite F E :=
    Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hInf : gramR (Ainf F) σ J (projInf X) =
      fun a b => bcE E (fstA F) (gramR (AF F) σ J X a b) := bcE_gramR (fstA F) σ J X
  have hFin : gramR (Af F) σ J (projFin X) =
      fun a b => bcE E (sndA F) (gramR (AF F) σ J X a b) := bcE_gramR (sndA F) σ J X
  have hV : ∀ v, gramR (Fv F v) σ J (projV v (projFin X)) =
      fun a b => bcE E (evalV F v) (bcE E (sndA F) (gramR (AF F) σ J X a b)) := by
    intro v
    have := bcE_gramR (evalV F v) σ J (projFin X : Fin n → Fin M → Af F ⊗[F] E)
    rw [hFin] at this
    exact this
  refine ⟨⟨fun h => ⟨?_, fun v => ?_⟩, fun h => ?_⟩, fun Y => gramR_ratTup σ J Y⟩
  · rw [hInf, h]
    funext a b
    simp only [Matrix.map_apply, bcE_inclR]
  · rw [hV v, h]
    funext a b
    simp only [Matrix.map_apply, bcE_inclR]
  · funext a b
    apply tensor_ext
    · have := congrFun (congrFun (hInf.symm.trans h.1) a) b
      simpa only [Matrix.map_apply, bcE_inclR] using this
    · intro v
      have := congrFun (congrFun ((hV v).symm.trans (h.2 v)) a) b
      simpa only [Matrix.map_apply, bcE_inclR] using this

end GlobalTheory.CompanionTheory.SW.GramLocal
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramMatrixLocalGlobalStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_matrix_local_global : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ) (X : (Fin n → Fin M → AF F ⊗[F] E)) (T : Matrix (Fin n) (Fin n) E), (gramR (AF F) σ J X = T.map (inclR (AF F)) ↔ gramR (Ainf F) σ J (projInf X) = T.map (inclR (Ainf F)) ∧ ∀ v, gramR (Fv F v) σ J (projV v (projFin X)) = T.map (inclR (Fv F v))) ∧ ∀ Y : Fin n → Fin M → E, gramR (AF F) σ J (ratTup (AF F) Y) = (gramE σ J Y).map (inclR (AF F)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.GramLocal.gram_local | exact GlobalTheory.CompanionTheory.SW.GramLocal.gram_local | (intros; apply GlobalTheory.CompanionTheory.SW.GramLocal.gram_local <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramRightMulActionLaws
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramRightMulActionLaws
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.RMulGram

theorem mul_regroup {A : Type} [CommRing A] {m n : Type} [Fintype m] [Fintype n]
    (P : Matrix n n A) (B : Matrix n m A) (J : Matrix m m A) (C : Matrix m n A)
    (g : Matrix n n A) :
    (P * B) * J * (C * g) = P * ((B * J : Matrix n m A) * C) * g := by
  simp only [Matrix.mul_assoc]

section
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

def colsM {M n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) : Matrix (Fin M) (Fin n) (R ⊗[F] E) :=
  fun i a => X a i

theorem colsM_injective {M n : ℕ} {X Y : Fin n → Fin M → R ⊗[F] E}
    (h : colsM R X = colsM R Y) : X = Y := by
  funext a i
  exact congrFun (congrFun h i) a

theorem gramR_eq_mul (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X : Fin n → Fin M → R ⊗[F] E) :
    gramR R σ J X =
      (cT (sigR R σ) (colsM R X) * JR R J : Matrix (Fin n) (Fin M) (R ⊗[F] E)) * colsM R X := by
  ext a b
  simp only [gramR, hR, hform, Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply,
    colsM, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_mul]
  congr 1

theorem colsM_rmul {M n : ℕ} (X : Fin n → Fin M → R ⊗[F] E)
    (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    colsM R (rmul R X g) = colsM R X * g := by
  ext i a
  simp only [rmul, colsM, Matrix.mul_apply]

theorem gramR_rmul (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X : Fin n → Fin M → R ⊗[F] E) (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    gramR R σ J (rmul R X g) = cT (sigR R σ) g * gramR R σ J X * g := by
  rw [gramR_eq_mul, gramR_eq_mul, colsM_rmul, cT_mul]
  exact mul_regroup _ _ _ _ _

theorem rmul_rmul {M n : ℕ} (X : Fin n → Fin M → R ⊗[F] E)
    (g g' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    rmul R (rmul R X g) g' = rmul R X (g * g') := by
  apply colsM_injective
  rw [colsM_rmul, colsM_rmul, colsM_rmul, Matrix.mul_assoc]

theorem rmul_one {M n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) : rmul R X 1 = X := by
  apply colsM_injective
  rw [colsM_rmul, Matrix.mul_one]

theorem actTup_rmul {M n : ℕ} (k : GL (Fin M) (R ⊗[F] E)) (X : Fin n → Fin M → R ⊗[F] E)
    (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    actTup R k (rmul R X g) = rmul R (actTup R k X) g := by
  funext a i
  simp only [actTup, rmul, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => (mul_assoc _ _ _).symm

end

theorem rmul_gram_facts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] (M n : ℕ) (J : Matrix (Fin M) (Fin M) E) (X : Fin n → Fin M → R ⊗[F] E) (g g' : Matrix (Fin n) (Fin n) (R ⊗[F] E)), gramR R σ J (rmul R X g) = cT (sigR R σ) g * gramR R σ J X * g ∧ rmul R (rmul R X g) g' = rmul R X (g * g') ∧ rmul R X 1 = X ∧ ∀ k : GL (Fin M) (R ⊗[F] E), actTup R k (rmul R X g) = rmul R (actTup R k X) g := by
  intro F E _ _ _ _ _ σ _ R _ _ M n J X g g'
  exact ⟨gramR_rmul R σ J X g, rmul_rmul R X g g', rmul_one R X, fun k => actTup_rmul R k X g⟩

end GlobalTheory.CompanionTheory.SW.RMulGram
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramRightMulActionLawsStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_right_mul_action_laws : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] (M n : ℕ) (J : Matrix (Fin M) (Fin M) E) (X : Fin n → Fin M → R ⊗[F] E) (g g' : Matrix (Fin n) (Fin n) (R ⊗[F] E)), gramR R σ J (rmul R X g) = cT (sigR R σ) g * gramR R σ J X * g ∧ rmul R (rmul R X g) g' = rmul R X (g * g') ∧ rmul R X 1 = X ∧ ∀ k : GL (Fin M) (R ⊗[F] E), actTup R k (rmul R X g) = rmul R (actTup R k X) g := by
  first | exact @GlobalTheory.CompanionTheory.SW.RMulGram.rmul_gram_facts | exact GlobalTheory.CompanionTheory.SW.RMulGram.rmul_gram_facts | (intros; apply GlobalTheory.CompanionTheory.SW.RMulGram.rmul_gram_facts <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SelfdualMeasureTwistBySymmetricAuto
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SelfdualMeasureTwistBySymmetricAuto
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.SdChange

theorem selfDual_twist : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) (χ : V → V → ℂ), SelfDual μ χ → ∀ (B : V ≃ₜ+ V),
    (∀ x y, χ x (B y) = χ (B x) y) → ∀ c : ℝ≥0, μ.map B = c • μ →
    SelfDual ((NNReal.sqrt c)⁻¹ • μ) (fun x y => χ x (B y)) := by
  intro V _ _ _ _ _ _ _ _ μ χ hsd B hsym c hc
  obtain ⟨hHaar, hinv⟩ := hsd
  have hemb : MeasurableEmbedding B := (B.toHomeomorph).measurableEmbedding
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h0 : μ.map B = 0 := by simpa using hc
    rw [Measure.map_eq_zero_iff hemb.measurable.aemeasurable] at h0
    exact (NeZero.ne μ) h0
  have hs0 : NNReal.sqrt c ≠ 0 := by simpa using hc0
  have hss : NNReal.sqrt c * NNReal.sqrt c = c := NNReal.mul_self_sqrt c
  generalize NNReal.sqrt c = s at hs0 hss ⊢
  refine ⟨Measure.IsAddHaarMeasure.nnreal_smul μ (inv_ne_zero hs0), ?_⟩
  intro Φ _ _ hint z
  let H : V → ℂ := fun y => ∫ x, Φ x * χ x y ∂μ
  have h1 : ∀ y, ∫ x, Φ x * χ x (B y) ∂(s⁻¹ • μ) = s⁻¹ • H (B y) :=
    fun y => integral_smul_nnreal_measure _ _
  simp only [h1] at hint ⊢
  have hsE : ((s⁻¹ : ℝ≥0) : ℝ≥0∞) ≠ 0 := by simpa using hs0
  have hint2 : Integrable (fun y => H (B y)) μ := by
    have h2 : Integrable (fun y => s⁻¹ • H (B y)) μ := by
      have h3 : s⁻¹ • μ = ((s⁻¹ : ℝ≥0) : ℝ≥0∞) • μ := rfl
      rw [h3] at hint
      exact (integrable_smul_measure hsE ENNReal.coe_ne_top).1 hint
    have h4 := h2.smul (s : ℝ)
    refine h4.congr (Filter.Eventually.of_forall fun y => ?_)
    have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast hs0
    have hsC : ((s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsR
    simp [NNReal.smul_def, smul_smul]
    rw [← mul_assoc, mul_inv_cancel₀ hsC, one_mul]
  have hintH : Integrable H μ := by
    have h5 : Integrable H (μ.map B) := (hemb.integrable_map_iff).2 hint2
    rw [hc] at h5
    have h6 : c • μ = (c : ℝ≥0∞) • μ := rfl
    rw [h6] at h5
    exact (integrable_smul_measure (by simpa using hc0) ENNReal.coe_ne_top).1 h5
  have hI := hinv Φ ‹_› ‹_› hintH z
  have h7 : ∫ w, H w * χ w z ∂(μ.map B) = c • ∫ w, H w * χ w z ∂μ := by
    rw [hc]; exact integral_smul_nnreal_measure _ _
  have h8 : ∫ w, H w * χ w z ∂(μ.map B) = ∫ y, H (B y) * χ (B y) z ∂μ :=
    hemb.integral_map _
  rw [integral_smul_nnreal_measure]
  have h9 : ∀ y, (s⁻¹ • H (B y)) * χ y (B z) = s⁻¹ • (H (B y) * χ (B y) z) := by
    intro y; rw [hsym, smul_mul_assoc]
  simp only [h9]
  have h10 : ∫ y, H (B y) * χ (B y) z ∂μ = c • Φ (-z) := by
    rw [← h8, h7]
    exact congrArg (c • ·) hI
  have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast hs0
  have hcR : (c : ℝ) = (s : ℝ) * s := by exact_mod_cast hss.symm
  simp only [NNReal.smul_def] at h10 ⊢
  rw [integral_smul, h10, smul_smul, smul_smul, hcR]
  have h11 : (((s⁻¹ : ℝ≥0) : ℝ)) = (s : ℝ)⁻¹ := by simp
  rw [h11]
  field_simp
  simp

end GlobalTheory.CompanionTheory.SW.SdChange
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SelfdualMeasureTwistBySymmetricAutoStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfdual_measure_twist_by_symmetric_auto : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) (χ : V → V → ℂ), SelfDual μ χ → ∀ (B : V ≃ₜ+ V), (∀ x y, χ x (B y) = χ (B x) y) → ∀ c : ℝ≥0, μ.map B = c • μ → SelfDual ((NNReal.sqrt c)⁻¹ • μ) (fun x y => χ x (B y)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.SdChange.selfDual_twist | exact GlobalTheory.CompanionTheory.SW.SdChange.selfDual_twist | (intros; apply GlobalTheory.CompanionTheory.SW.SdChange.selfDual_twist <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryIsomOfIsometry
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.HIsom

section Generic

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem conj_mem_UJ (s : A →+* A) (J : Matrix n n A) (G u : GL n A)
    (hu : u ∈ UJ s (cT s (G : Matrix n n A) * J * (G : Matrix n n A))) :
    G * u * G⁻¹ ∈ UJ s J := by
  have hu' : cT s (u : Matrix n n A) * (cT s (G : Matrix n n A) * J * (G : Matrix n n A))
      * (u : Matrix n n A) = cT s (G : Matrix n n A) * J * (G : Matrix n n A) := hu
  have hGi : (G : Matrix n n A) * ((G⁻¹ : GL n A) : Matrix n n A) = 1 := Units.mul_inv G
  change cT s (((G * u * G⁻¹ : GL n A)) : Matrix n n A) * J
    * (((G * u * G⁻¹ : GL n A)) : Matrix n n A) = J
  simp only [Units.val_mul]
  calc cT s ((G : Matrix n n A) * (u : Matrix n n A) * ((G⁻¹ : GL n A) : Matrix n n A)) * J
        * ((G : Matrix n n A) * (u : Matrix n n A) * ((G⁻¹ : GL n A) : Matrix n n A))
      = cT s ((G⁻¹ : GL n A) : Matrix n n A)
          * (cT s (u : Matrix n n A) * (cT s (G : Matrix n n A) * J * (G : Matrix n n A))
            * (u : Matrix n n A)) * ((G⁻¹ : GL n A) : Matrix n n A) := by
        simp only [cT_mul, Matrix.mul_assoc]
    _ = cT s ((G : Matrix n n A) * ((G⁻¹ : GL n A) : Matrix n n A)) * J
          * ((G : Matrix n n A) * ((G⁻¹ : GL n A) : Matrix n n A)) := by
        rw [hu']; simp only [cT_mul, Matrix.mul_assoc]
    _ = J := by rw [hGi, cT_one, Matrix.one_mul, Matrix.mul_one]

theorem conj_inv_mem_UJ (s : A →+* A) (J : Matrix n n A) (G u : GL n A) (hu : u ∈ UJ s J) :
    G⁻¹ * u * G ∈ UJ s (cT s (G : Matrix n n A) * J * (G : Matrix n n A)) := by
  have hGi : (G : Matrix n n A) * ((G⁻¹ : GL n A) : Matrix n n A) = 1 := Units.mul_inv G
  have key : cT s ((G⁻¹ : GL n A) : Matrix n n A)
      * (cT s (G : Matrix n n A) * J * (G : Matrix n n A)) * ((G⁻¹ : GL n A) : Matrix n n A) = J := by
    calc cT s ((G⁻¹ : GL n A) : Matrix n n A)
          * (cT s (G : Matrix n n A) * J * (G : Matrix n n A)) * ((G⁻¹ : GL n A) : Matrix n n A)
        = cT s ((G : Matrix n n A) * ((G⁻¹ : GL n A) : Matrix n n A)) * J
            * ((G : Matrix n n A) * ((G⁻¹ : GL n A) : Matrix n n A)) := by
          simp only [cT_mul, Matrix.mul_assoc]
      _ = J := by rw [hGi, cT_one, Matrix.one_mul, Matrix.mul_one]
  have := conj_mem_UJ s (cT s (G : Matrix n n A) * J * (G : Matrix n n A)) G⁻¹ u
    (by rw [key]; exact hu)
  simpa using this

def conjHomeo {T : Type} [Group T] [TopologicalSpace T] [ContinuousMul T] (H' H : Subgroup T) (G : T)
    (h₁ : ∀ u ∈ H', G * u * G⁻¹ ∈ H) (h₂ : ∀ u ∈ H, G⁻¹ * u * G ∈ H') : H' ≃ₜ* H where
  toFun u := ⟨G * u * G⁻¹, h₁ u u.2⟩
  invFun u := ⟨G⁻¹ * u * G, h₂ u u.2⟩
  left_inv u := by ext; simp [mul_assoc]
  right_inv u := by ext; simp [mul_assoc]
  map_mul' a b := by ext; simp [mul_assoc]
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const

end Generic

section Base

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem cT_inclR (σ : E →ₐ[F] E) {M : ℕ} (g : Matrix (Fin M) (Fin M) E) :
    cT (sigR R σ) (g.map (inclR R)) = (cT (σ : E →+* E) g).map (inclR R) := by
  ext i j
  simp [cT, sigR, inclR, Matrix.map_apply]

theorem JR_conj (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (g : GL (Fin M) E) :
    JR R (cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E)) =
      cT (sigR R σ) ((bc (inclR R) g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E))
        * JR R J * ((bc (inclR R) g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) := by
  have hG : ((bc (inclR R) g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) =
      (g : Matrix (Fin M) (Fin M) E).map (inclR R) := rfl
  rw [hG, cT_inclR]
  simp only [JR, Matrix.map_mul]

end Base

theorem isTopologicalRing_tens (F E : Type) [Field F] [Field E] [Algebra F E] [Module.Finite F E]
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] :
    IsTopologicalRing (R ⊗[F] E) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  exact IsModuleTopology.isTopologicalRing R (R ⊗[F] E)

end GlobalTheory.CompanionTheory.SW.HIsom


open GlobalTheory.CompanionTheory.SW.HIsom in
theorem GlobalTheory.CompanionTheory.SW.HIsom.unitaryIsom_of_isometry : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (g : GL (Fin M) E) (J' : Matrix (Fin M) (Fin M) E), J' = cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * g → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R], ∃ e : HA R σ J' ≃ₜ* HA R σ J, (∀ u, HA.mat R σ J (e u) = bc (inclR R) g * HA.mat R σ J' u * (bc (inclR R) g)⁻¹) ∧ ∀ u, HA.mat R σ J (e u) ∈ HFin R σ J ↔ HA.mat R σ J' u ∈ HFin R σ J' := by
  intro F E _ _ _ _ _ σ hCM M J _ g J' hJ' R _ _ _ _
  subst hJ'
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  haveI : IsTopologicalRing (R ⊗[F] E) := isTopologicalRing_tens F E R
  set G : GL (Fin M) (R ⊗[F] E) := bc (inclR R) g with hG
  have hJR := JR_conj R σ J g
  have h₁ : ∀ u ∈ HR R σ (cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E)),
      G * u * G⁻¹ ∈ HR R σ J := by
    intro u hu
    refine conj_mem_UJ (sigR R σ) (JR R J) G u ?_
    have : u ∈ UJ (sigR R σ) (JR R (cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E))) := hu
    rwa [hJR] at this
  have h₂ : ∀ u ∈ HR R σ J,
      G⁻¹ * u * G ∈ HR R σ (cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E)) := by
    intro u hu
    change G⁻¹ * u * G ∈ UJ (sigR R σ) (JR R (cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E)))
    rw [hJR]
    exact conj_inv_mem_UJ (sigR R σ) (JR R J) G u hu
  refine ⟨conjHomeo _ _ G h₁ h₂, fun u => rfl, fun u => ?_⟩
  change G * HA.mat R σ _ u * G⁻¹ ∈ HFin R σ J ↔ _
  constructor
  · rintro ⟨w, hw, hwu⟩
    refine ⟨g⁻¹ * w * g, conj_inv_mem_UJ (σ : E →+* E) J g w hw, ?_⟩
    have : bc (inclR R) w = G * HA.mat R σ _ u * G⁻¹ := hwu
    simp only [map_mul, map_inv, this, ← hG]
    group
  · rintro ⟨w, hw, hwu⟩
    refine ⟨g * w * g⁻¹, conj_mem_UJ (σ : E →+* E) J g w hw, ?_⟩
    have : bc (inclR R) w = HA.mat R σ _ u := hwu
    simp only [map_mul, map_inv, this, ← hG]
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.EtaleAwayQuotientEqLocalization
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.TraceFormGram

open HeckeCharacterZeroLocus.SiegelWeilU
open scoped TensorProduct Matrix

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem trace_tmul [FiniteDimensional F E] (R : Type) [CommRing R] [Algebra F R] (a : R) (e : E) :
    Algebra.trace R (R ⊗[F] E) (a ⊗ₜ[F] e) = a * algebraMap F R (Algebra.trace F E e) := by
  have h1 : Algebra.trace R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] e) = algebraMap F R (Algebra.trace F E e) := by
    rw [Algebra.trace_apply, Algebra.trace_apply, ← LinearMap.trace_baseChange]
    congr 1
    ext y
    simp [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.baseChange_tmul]
  have h2 : a ⊗ₜ[F] e = a • ((1 : R) ⊗ₜ[F] e) := by
    simp [TensorProduct.smul_tmul']
  rw [h2, map_smul, h1, smul_eq_mul]

theorem expand {d : ℕ} (b : Module.Basis (Fin d) F E) (R : Type) [CommRing R] [Algebra F R]
    (u : R ⊗[F] E) :
    u = ∑ k, ((Algebra.TensorProduct.basis R b).repr u k) ⊗ₜ[F] b k := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis R b).sum_repr u]
  simp [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul']

def trGram (σ : E →ₐ[F] E) {M d : ℕ} (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin d) F E) :
    Matrix (Fin M × Fin d) (Fin M × Fin d) F :=
  fun p q => Algebra.trace F E (σ (b p.2) * J p.1 q.1 * b q.2)

theorem trace_entry [FiniteDimensional F E] (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (R : Type) [CommRing R] [Algebra F R] (u v : R ⊗[F] E) (e : E) :
    Algebra.trace R (R ⊗[F] E) (sigR R σ u * ((1 : R) ⊗ₜ[F] e) * v) =
      ∑ k, ∑ l, (Algebra.TensorProduct.basis R b).repr u k *
        (algebraMap F R (Algebra.trace F E (σ (b k) * e * b l)) *
          (Algebra.TensorProduct.basis R b).repr v l) := by
  conv_lhs => rw [expand b R u, expand b R v]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  have : sigR R σ (((Algebra.TensorProduct.basis R b).repr u k) ⊗ₜ[F] b k) =
      ((Algebra.TensorProduct.basis R b).repr u k) ⊗ₜ[F] σ (b k) := by
    simp [sigR]
  rw [this, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, trace_tmul]
  simp only [mul_one]
  ring

section CM

variable [NumberField F] [NumberField E]

theorem sig_sig {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem trace_sig {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) :
    Algebra.trace F E (σ x) = Algebra.trace F E x :=
  Algebra.trace_eq_of_algEquiv
    (AlgEquiv.ofAlgHom σ σ (AlgHom.ext (sig_sig h)) (AlgHom.ext (sig_sig h))) x

theorem trGram_isSymm {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {M d : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) (b : Module.Basis (Fin d) F E) :
    (trGram σ J b).IsSymm := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [Matrix.transpose_apply, trGram]
  rw [← trace_sig h (σ (b l) * J j i * b k)]
  simp only [map_mul, sig_sig h, hJ.1]
  congr 1
  ring

theorem trGram_det_ne_zero {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {M d : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) (b : Module.Basis (Fin d) F E) :
    (trGram σ J b).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hBv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  set y : Fin M → E := fun j => ∑ l, v (j, l) • b l with hy
  have key : ∀ i k, Algebra.trace F E (σ (b k) * (J *ᵥ y) i) = 0 := by
    intro i k
    have h0 := congrFun hBv (i, k)
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, trGram, Pi.zero_apply] at h0
    rw [← h0]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, hy, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    rw [mul_smul_comm, mul_smul_comm, map_smul, smul_eq_mul, mul_comm, mul_assoc]
  have key2 : ∀ i (e : E), Algebra.trace F E (e * (J *ᵥ y) i) = 0 := by
    intro i e
    have he : e = ∑ k, (b.repr (σ e) k) • σ (b k) := by
      have h3 := congrArg σ (b.sum_repr (σ e))
      set_option synthInstance.maxHeartbeats 100000 in
        rw [sig_sig h, map_sum] at h3
      exact h3.symm.trans (Finset.sum_congr rfl fun k _ => σ.toLinearMap.map_smul _ _)
    rw [he]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finset.sum_mul, map_sum, smul_mul_assoc, map_smul, key, smul_zero,
      Finset.sum_const_zero]
  have hw : J *ᵥ y = 0 := by
    funext i
    refine (traceForm_nondegenerate F E).1 _ fun e => ?_
    rw [Algebra.traceForm_apply, mul_comm]
    exact key2 i e
  have hy0 : y = 0 := Matrix.eq_zero_of_mulVec_eq_zero hJ.2 hw
  apply hv
  funext ⟨j, l⟩
  have := congrFun hy0 j
  have h2 := Fintype.linearIndependent_iff.1 b.linearIndependent (fun l => v (j, l)) this l
  simpa using h2

end CM

end GlobalTheory.CompanionTheory.SW.TraceFormGram

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW

theorem trace_form_coords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∃ B : Matrix (Fin M × Fin d) (Fin M × Fin d) F, B.IsSymm ∧ B.det ≠ 0 ∧ ∀ (R : Type) [CommRing R] [Algebra F R] (x y : Fin M → R ⊗[F] E), Algebra.trace R (R ⊗[F] E) (hR R σ J x y) = (fun p : Fin M × Fin d => (Algebra.TensorProduct.basis R b).repr (x p.1) p.2) ⬝ᵥ (B.map (algebraMap F R) *ᵥ fun p : Fin M × Fin d => (Algebra.TensorProduct.basis R b).repr (y p.1) p.2) := by
  intro F E _ _ _ _ _ σ h M J hJ d b
  haveI : FiniteDimensional F E := Module.Basis.finiteDimensional_of_finite b
  refine ⟨TraceFormGram.trGram σ J b, TraceFormGram.trGram_isSymm h hJ b, TraceFormGram.trGram_det_ne_zero h hJ b, ?_⟩
  intro R _ _ x y
  have hh : hR R σ J x y = ∑ i, ∑ j, sigR R σ (x i) * ((1 : R) ⊗ₜ[F] J i j) * y j := rfl
  rw [hh]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, TraceFormGram.trace_entry σ b R]
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Matrix.map_apply, TraceFormGram.trGram,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

end GlobalTheory.CompanionTheory.SW
end
end
