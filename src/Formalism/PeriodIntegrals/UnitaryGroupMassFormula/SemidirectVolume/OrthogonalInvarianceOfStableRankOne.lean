module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.LocallyCompactAdelicUnitary
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.GlGeneratedTransvectionsDiag

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.CjTDefs
noncomputable section

namespace PI.VolSemiDirect.W.Cj

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
open scoped TensorProduct

def TraceBase : Prop :=
  ∀ (F E : Type) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] (R : Type) [CommRing R]
    [Algebra F R] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (x y : Fin M → E),
    Algebra.trace R (R ⊗[F] E) (hR R σ J (ratV (F := F) R x) (ratV (F := F) R y)) =
      algebraMap F R (Algebra.trace F E (hE σ J x y))

def TraceGramND : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (k : ℕ) (b : Module.Basis (Fin k) F (Fin M → E)),
      (Matrix.of fun i j => Algebra.trace F E (hE σ J (b i) (b j))).det ≠ 0

end PI.VolSemiDirect.W.Cj
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.BVRApply
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.HermitianDatumFormEq
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.NnrealEqOneOfMulSelf
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.MapPhiOfModM
noncomputable section

namespace PI.VolSemiDirect.W.Cj

open MeasureTheory Measure
open scoped NNReal

section Gen

variable {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [LocallyCompactSpace A] [SecondCountableTopology A] [T2Space A] [MeasurableSpace A]
  [BorelSpace A] {k : ℕ}

def phi (X : GL (Fin k) A) : (Fin k → A) ≃ₜ+ (Fin k → A) where
  toFun v := (X : Matrix (Fin k) (Fin k) A).mulVec v
  invFun v := ((X⁻¹ : GL (Fin k) A) : Matrix (Fin k) (Fin k) A).mulVec v
  left_inv v := by
    simp only [Matrix.mulVec_mulVec]
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  right_inv v := by
    simp only [Matrix.mulVec_mulVec]
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  map_add' v w := Matrix.mulVec_add _ v w
  continuous_toFun := continuous_const.matrix_mulVec continuous_id
  continuous_invFun := continuous_const.matrix_mulVec continuous_id

theorem phi_apply (X : GL (Fin k) A) (v : Fin k → A) :
    phi X v = (X : Matrix (Fin k) (Fin k) A).mulVec v := rfl

def modM (X : GL (Fin k) A) : ℝ≥0 := addEquivAddHaarChar (phi X)

theorem phi_mul (X Y : GL (Fin k) A) : phi (X * Y) = (phi Y).trans (phi X) := by
  apply ContinuousAddEquiv.ext
  intro v
  simp only [ContinuousAddEquiv.trans_apply, phi_apply, Units.val_mul, Matrix.mulVec_mulVec]

theorem modM_mul (X Y : GL (Fin k) A) : modM (X * Y) = modM X * modM Y := by
  simp only [modM, phi_mul, addEquivAddHaarChar_trans, mul_comm]

theorem modM_one : modM (1 : GL (Fin k) A) = 1 := by
  have h : phi (1 : GL (Fin k) A) = ContinuousAddEquiv.refl _ := by
    apply ContinuousAddEquiv.ext
    intro v
    simp [phi_apply]
  simp only [modM, h, addEquivAddHaarChar_refl]

theorem modM_inv (X : GL (Fin k) A) : modM X⁻¹ = (modM X)⁻¹ := by
  have h : modM X⁻¹ * modM X = 1 := by rw [← modM_mul, inv_mul_cancel, modM_one]
  exact eq_inv_of_mul_eq_one_left h

theorem map_phi_of_modM (X : GL (Fin k) A) (hX : modM X = 1) (μ : Measure (Fin k → A))
    [μ.IsAddHaarMeasure] : μ.map (phi X) = μ := by
  have h := addEquivAddHaarChar_smul_map μ (phi X)
  rwa [show addEquivAddHaarChar (phi X) = modM X from rfl, hX, one_smul] at h

theorem modM_of_map (X : GL (Fin k) A) (μ : Measure (Fin k → A)) [μ.IsAddHaarMeasure]
    (h : μ.map (phi X) = μ) : modM X = 1 := by
  have h1 := addEquivAddHaarChar_smul_map μ (phi X)
  rw [h] at h1
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds (0 : Fin k → A)
  have hpos : μ K ≠ 0 := (measure_pos_of_mem_nhds μ hKn).ne'
  have hfin : μ K ≠ ⊤ := hK.measure_lt_top.ne
  have h2 := congrArg (fun ν : Measure (Fin k → A) => ν K) h1
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h2
  have h3 : ((modM X : ℝ≥0) : ENNReal) = 1 := by
    have h4 : (modM X : ENNReal) * μ K / μ K = 1 * μ K / μ K := by rw [one_mul]; exact congrArg (· / μ K) h2
    rwa [ENNReal.mul_div_cancel_right hpos hfin, ENNReal.mul_div_cancel_right hpos hfin] at h4
  exact_mod_cast h3

end Gen

end PI.VolSemiDirect.W.Cj
end
end

noncomputable section

namespace PI.VolSemiDirect.W.Cj

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Measure
open scoped NNReal

section Gen

variable {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [LocallyCompactSpace A] [SecondCountableTopology A] [T2Space A] [MeasurableSpace A]
  [BorelSpace A] {k : ℕ}

def trG (X : GL (Fin k) A) : GL (Fin k) A where
  val := (X : Matrix (Fin k) (Fin k) A).transpose
  inv := ((X⁻¹ : GL (Fin k) A) : Matrix (Fin k) (Fin k) A).transpose
  val_inv := by
    rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.transpose_one]
  inv_val := by
    rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.transpose_one]

theorem trG_val (X : GL (Fin k) A) :
    ((trG X : GL (Fin k) A) : Matrix (Fin k) (Fin k) A) = (X : Matrix (Fin k) (Fin k) A).transpose :=
  rfl

theorem trG_mul (X Y : GL (Fin k) A) : trG (X * Y) = trG Y * trG X := by
  ext1
  simp [trG_val, Matrix.transpose_mul]

theorem trG_one : trG (1 : GL (Fin k) A) = 1 := by
  ext1
  simp [trG_val]

theorem trG_inv (X : GL (Fin k) A) : trG X⁻¹ = (trG X)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← trG_mul, mul_inv_cancel, trG_one]

theorem modM_transv (hT : TransvHaar) (X : GL (Fin k) A) (i j : Fin k) (hij : i ≠ j) (c : A)
    (hX : (X : Matrix (Fin k) (Fin k) A) = Matrix.transvection i j c) : modM X = 1 := by
  have h := hT A k i j hij c (addHaar : Measure (Fin k → A)) inferInstance
  have e : (phi X : (Fin k → A) → (Fin k → A)) = Matrix.mulVec (Matrix.transvection i j c) := by
    funext v
    rw [phi_apply, hX]
  apply modM_of_map X (addHaar : Measure (Fin k → A))
  rw [e]
  exact h

theorem transvection_transpose (i j : Fin k) (c : A) :
    (Matrix.transvection i j c).transpose = Matrix.transvection j i c := by
  ext a b
  simp [Matrix.transvection, Matrix.transpose_apply, Matrix.one_apply, Matrix.single_apply]
  aesop

theorem modM_tr_of_mem (hT : TransvHaar) (X : GL (Fin k) A)
    (hX : X ∈ Subgroup.closure ({g : GL (Fin k) A | ∃ i j c, i ≠ j ∧
      (g : Matrix (Fin k) (Fin k) A) = Matrix.transvection i j c} ∪
      {g | ∃ d : Fin k → A, (g : Matrix (Fin k) (Fin k) A) = Matrix.diagonal d})) :
    modM (trG X) = modM X := by
  induction hX using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨i, j, c, hij, hx⟩ | ⟨d, hx⟩
    · rw [modM_transv hT x i j hij c hx, modM_transv hT (trG x) j i hij.symm c
        (by rw [trG_val, hx, transvection_transpose])]
    · have : trG x = x := by
        ext1
        rw [trG_val, hx, Matrix.diagonal_transpose]
      rw [this]
  | one => rw [trG_one]
  | mul x y _ _ hx hy => rw [trG_mul, modM_mul, modM_mul, hx, hy, mul_comm]
  | inv x _ hx => rw [trG_inv, modM_inv, modM_inv, hx]

end Gen

theorem nnreal_eq_one_of_mul_self {x : ℝ≥0} (h : x * x = 1) : x = 1 := by
  have h' : (x : ℝ) * x = 1 := by exact_mod_cast h
  have : (x : ℝ) = 1 := by nlinarith [x.coe_nonneg]
  exact_mod_cast this

theorem orthInv_of (h1 : AdeleStableRankOne) (h2 : ElimSR1) (h3 : TransvHaar) : OrthInv := by
  intro F _ _ k G X hG hXG μ hμ
  obtain ⟨hlc, hsc, ht2⟩ := PI.VolStabSW.TopoAF.afTop_holds F
  have : BorelSpace (AF F) := ⟨rfl⟩
  have hd := congrArg Matrix.det hXG
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hd
  have hdd : X.det * X.det = 1 := by
    have : (X.det * X.det) * G.det = 1 * G.det := by
      calc (X.det * X.det) * G.det = X.det * G.det * X.det := by ring
        _ = 1 * G.det := by rw [hd, one_mul]
    exact hG.mul_left_inj.1 this
  have hX : IsUnit X.det := ⟨⟨X.det, X.det, hdd, hdd⟩, rfl⟩
  let Xu : GL (Fin k) (AF F) := Matrix.nonsingInvUnit X hX
  let Gu : GL (Fin k) (AF F) := Matrix.nonsingInvUnit G hG
  have hrel : trG Xu * Gu * Xu = Gu := by
    ext1
    exact hXG
  have hm := congrArg modM hrel
  rw [modM_mul, modM_mul, modM_tr_of_mem h3 Xu (h2 (AF F) (h1 F) k Xu)] at hm
  have hpos : 0 < modM Gu := addEquivAddHaarChar_pos (phi Gu)
  have hsq : modM Xu * modM Xu = 1 := by
    have : (modM Xu * modM Xu) * modM Gu = 1 * modM Gu := by
      calc (modM Xu * modM Xu) * modM Gu = modM Xu * modM Gu * modM Xu := by ring
        _ = 1 * modM Gu := by rw [hm, one_mul]
    exact mul_right_cancel₀ hpos.ne' this
  have hmod := nnreal_eq_one_of_mul_self hsq
  have e := map_phi_of_modM Xu hmod μ
  have e2 : (phi Xu : (Fin k → AF F) → (Fin k → AF F)) = Matrix.mulVec X := by
    funext v
    rfl
  rw [e2] at e
  exact e

end PI.VolSemiDirect.W.Cj
end
end

noncomputable section

namespace PI.VolSemiDirect.W.Cj

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub MeasureTheory Measure
open scoped TensorProduct

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] {A : Type} [CommRing A] [Algebra F A]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

def Bf (u v : Fin M → A ⊗[F] E) : A := Algebra.trace A (A ⊗[F] E) (hR A σ J u v)

theorem sigR_algebraMap (c : A) :
    sigR A σ (algebraMap A (A ⊗[F] E) c) = algebraMap A (A ⊗[F] E) c := by
  simp [sigR, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.map_tmul]

theorem trace_algebraMap_mul (c : A) (y : A ⊗[F] E) :
    Algebra.trace A (A ⊗[F] E) (algebraMap A (A ⊗[F] E) c * y) =
      c * Algebra.trace A (A ⊗[F] E) y := by
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

theorem Bf_smul_left (c : A) (u v : Fin M → A ⊗[F] E) : Bf σ J (c • u) v = c * Bf σ J u v := by
  have h : hR A σ J (c • u) v = algebraMap A (A ⊗[F] E) c * hR A σ J u v := by
    simp only [hR, Formalism.UG.hform, Pi.smul_apply, Algebra.smul_def, map_mul, sigR_algebraMap,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  unfold Bf
  rw [h, trace_algebraMap_mul]

theorem Bf_smul_right (c : A) (u v : Fin M → A ⊗[F] E) : Bf σ J u (c • v) = c * Bf σ J u v := by
  have h : hR A σ J u (c • v) = algebraMap A (A ⊗[F] E) c * hR A σ J u v := by
    simp only [hR, Formalism.UG.hform, Pi.smul_apply, Algebra.smul_def, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  unfold Bf
  rw [h, trace_algebraMap_mul]

theorem Bf_sum_left {k : ℕ} (x : Fin k → Fin M → A ⊗[F] E) (v : Fin M → A ⊗[F] E) :
    Bf σ J (∑ a, x a) v = ∑ a, Bf σ J (x a) v := by
  have h : hR A σ J (∑ a, x a) v = ∑ a, hR A σ J (x a) v := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hR, Formalism.UG.hform, Finset.sum_apply, _root_.map_sum, Finset.sum_mul]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Finset.sum_comm
  unfold Bf
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h, _root_.map_sum]

theorem Bf_sum_right {k : ℕ} (u : Fin M → A ⊗[F] E) (y : Fin k → Fin M → A ⊗[F] E) :
    Bf σ J u (∑ a, y a) = ∑ a, Bf σ J u (y a) := by
  have h : hR A σ J u (∑ a, y a) = ∑ a, hR A σ J u (y a) := by
    simp only [hR, Formalism.UG.hform, Finset.sum_apply, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Finset.sum_comm
  unfold Bf
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h, _root_.map_sum]

theorem Bf_expand {k : ℕ} (b : Fin k → Fin M → A ⊗[F] E) (x y : Fin k → A) :
    Bf σ J (∑ a, x a • b a) (∑ c, y c • b c) = ∑ a, ∑ c, x a * (Bf σ J (b a) (b c) * y c) := by
  rw [Bf_sum_left]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Bf_smul_left, Bf_sum_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Bf_smul_right]
  ring

theorem Bf_lin (g : HA A σ J) (u v : Fin M → A ⊗[F] E) :
    Bf σ J (lin A σ J g u) (lin A σ J g v) = Bf σ J u v := by
  have hf : ∀ x y : Fin M → A ⊗[F] E, hR A σ J x y =
      dotProduct (Matrix.vecMul (fun i => sigR A σ (x i)) (JR A J)) y := by
    intro x y
    simp only [hR, Formalism.UG.hform, dotProduct, Matrix.vecMul, Finset.sum_mul]
    exact Finset.sum_comm
  have hs : ∀ (P : Matrix (Fin M) (Fin M) (A ⊗[F] E)) (x : Fin M → A ⊗[F] E),
      (fun i => sigR A σ (P.mulVec x i)) =
        Matrix.vecMul (fun i => sigR A σ (x i)) (Formalism.UG.cT (sigR A σ) P) := by
    intro P x
    funext j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, Formalism.UG.cT, Matrix.transpose_apply,
      Matrix.map_apply, _root_.map_sum, map_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hg : (HA.mat A σ J g) ∈ HR A σ J := (show ↥(HR A σ J) from g).2
  have hg' : Formalism.UG.cT (sigR A σ) ((HA.mat A σ J g : GL (Fin M) (A ⊗[F] E)) : Matrix _ _ _) * JR A J *
      ((HA.mat A σ J g : GL (Fin M) (A ⊗[F] E)) : Matrix _ _ _) = JR A J := hg
  unfold Bf lin
  congr 1
  rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, hf, hf, hs, Matrix.dotProduct_mulVec,
    Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, hg']

end Alg

end PI.VolSemiDirect.W.Cj
end
end

noncomputable section

namespace PI.VolSemiDirect.W.Cj

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub MeasureTheory Measure
open scoped TensorProduct Matrix

section Bases

variable (F E : Type) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] (M : ℕ)
  (A : Type) [CommRing A] [Algebra F A]

def bV : Module.Basis (Fin (Fintype.card (Σ _ : Fin M, Fin (Module.finrank F E)))) F (Fin M → E) :=
  (Pi.basis fun _ : Fin M => Module.finBasis F E).reindex (Fintype.equivFin _)

def bVR : Module.Basis (Fin (Fintype.card (Σ _ : Fin M, Fin (Module.finrank F E)))) A
    (Fin M → A ⊗[F] E) :=
  (Pi.basis fun _ : Fin M => Algebra.TensorProduct.basis A (Module.finBasis F E)).reindex
    (Fintype.equivFin _)

theorem bVR_apply (i : Fin (Fintype.card (Σ _ : Fin M, Fin (Module.finrank F E)))) :
    bVR F E M A i = ratV (F := F) A (bV F E M i) := by
  rw [bVR, bV, Module.Basis.reindex_apply, Module.Basis.reindex_apply]
  generalize (Fintype.equivFin (Σ _ : Fin M, Fin (Module.finrank F E))).symm i = p
  obtain ⟨a, c⟩ := p
  funext j
  simp only [Pi.basis_apply, Algebra.TensorProduct.basis_apply, Formalism.L2.SG.Sub.ratV]
  by_cases hj : j = a
  · subst hj
    simp only [Pi.single_eq_same]
    first | rfl | simp
  · simp only [Pi.single_eq_of_ne hj]
    first | rfl | simp

end Bases

theorem vMod_of (hO : OrthInv) (hB : TraceBase) (hN : TraceGramND) : VMod := by
  intro F E _ _ _ _ _ σ hCM M J hJ g μ hμ
  classical
  obtain ⟨hlc, hsc, ht2⟩ := PI.VolStabSW.TopoAF.afTop_holds F
  have : BorelSpace (AF F) := ⟨rfl⟩
  have : FiniteDimensional F E := Lc.finite_nf F E
  obtain ⟨htr, ht2R, hlcR, hscR⟩ := Lc.tensor_adele_topology_holds F E
  have : BorelSpace (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  set k := Fintype.card (Σ _ : Fin M, Fin (Module.finrank F E))
  set b := bV F E M
  set bR := bVR F E M (AF F)
  set e : (Fin M → AF F ⊗[F] E) ≃ₗ[AF F] (Fin k → AF F) := bR.equivFun
  have c1 : Continuous e.toLinearMap := IsModuleTopology.continuous_of_linearMap (R := AF F) _
  have c2 : Continuous e.symm.toLinearMap :=
    IsModuleTopology.continuous_of_linearMap (R := AF F) _
  let ec : (Fin M → AF F ⊗[F] E) ≃ₜ+ (Fin k → AF F) :=
    { e.toAddEquiv with
      continuous_toFun := by simpa using c1
      continuous_invFun := by simpa using c2 }
  have hec : ∀ u, ec u = e u := fun _ => rfl
  have hecs : ∀ x, ec.symm x = e.symm x := fun _ => rfl
  set μ' := μ.map ec
  have hμ' : μ'.IsAddHaarMeasure := ec.isAddHaarMeasure_map μ
  let L : (Fin k → AF F) →ₗ[AF F] (Fin k → AF F) :=
    e.toLinearMap ∘ₗ ((lin (AF F) σ J g).restrictScalars (AF F)) ∘ₗ e.symm.toLinearMap
  set X := LinearMap.toMatrix' L
  have hX : ∀ x, X.mulVec x = e (lin (AF F) σ J g (e.symm x)) := fun x =>
    LinearMap.toMatrix'_mulVec L x
  set G0 : Matrix (Fin k) (Fin k) F := Matrix.of fun i j => Algebra.trace F E (hE σ J (b i) (b j))
  set G := G0.map (algebraMap F (AF F))
  have hGu : IsUnit G.det := by
    have hd : G.det = algebraMap F (AF F) G0.det := by
      rw [RingHom.map_det]
      rfl
    rw [hd]
    exact (isUnit_iff_ne_zero.2 (hN F E σ hCM M J hJ k b)).map _
  have hBG : ∀ i j, Bf σ J (bR i) (bR j) = G i j := by
    intro i j
    rw [bVR_apply, bVR_apply, Bf, hB F E (AF F) σ M J]
    rfl
  have key : ∀ x y : Fin k → AF F, Bf σ J (e.symm x) (e.symm y) = x ⬝ᵥ (G *ᵥ y) := by
    intro x y
    rw [Module.Basis.equivFun_symm_apply, Module.Basis.equivFun_symm_apply, Bf_expand]
    simp only [hBG, dotProduct, Matrix.mulVec, Finset.mul_sum]
    rfl
  have e1 : ∀ u w : Fin k → AF F, u ⬝ᵥ ((X.transpose * G * X) *ᵥ w) = u ⬝ᵥ (G *ᵥ w) := by
    intro u w
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_transpose, ← key, hX, hX, LinearEquiv.symm_apply_apply,
      LinearEquiv.symm_apply_apply, Bf_lin, key]
  have hXG : X.transpose * G * X = G := by
    ext i j
    simpa using e1 (Pi.single i 1) (Pi.single j 1)
  have hinv := hO F k G X hGu hXG μ' hμ'
  have hlin : (lin (AF F) σ J g : (Fin M → AF F ⊗[F] E) → (Fin M → AF F ⊗[F] E)) =
      ec.symm ∘ X.mulVec ∘ ec := by
    funext u
    simp only [Function.comp_apply, hec, hecs, hX, LinearEquiv.symm_apply_apply]
  have mec : Measurable ec := ec.continuous.measurable
  have mecs : Measurable ec.symm := ec.symm.continuous.measurable
  have mX : Measurable X.mulVec := (continuous_const.matrix_mulVec continuous_id).measurable
  rw [hlin, ← Measure.map_map mecs (mX.comp mec), ← Measure.map_map mX mec, hinv,
    Measure.map_map mecs mec]
  have : (ec.symm ∘ ec : (Fin M → AF F ⊗[F] E) → _) = id := by
    funext u
    simp
  rw [this, Measure.map_id]

end PI.VolSemiDirect.W.Cj
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.TraceGramNondegenerate
noncomputable section

namespace PI.VolSemiDirect.W.Cj

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
open scoped TensorProduct

theorem trace_one_tmul {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (R : Type) [CommRing R] [Algebra F R] (z : E) :
    Algebra.trace R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] z) = algebraMap F R (Algebra.trace F E z) := by
  have h : Algebra.lmul R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] z) = (Algebra.lmul F E z).baseChange R := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro r e
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [Algebra.trace_apply, h, LinearMap.trace_baseChange, Algebra.trace_apply]

theorem trace_basis_holds : TraceBase := by
  intro F E _ _ _ _ R _ _ σ M J x y
  rw [W.hR_ratV R σ J x y]
  exact trace_one_tmul R _

theorem hE_add_left {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (x x' y : Fin M → E) :
    hE σ J (x + x') y = hE σ J x y + hE σ J x' y := by
  simp only [hE, Formalism.UG.hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem hE_add_right {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (x y y' : Fin M → E) :
    hE σ J x (y + y') = hE σ J x y + hE σ J x y' := by
  simp only [hE, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hE_smul_left {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (c : F) (x y : Fin M → E) :
    hE σ J (c • x) y = algebraMap F E c * hE σ J x y := by
  simp only [hE, Formalism.UG.hform, Pi.smul_apply, Algebra.smul_def]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hc : (σ : E →+* E) (algebraMap F E c) = algebraMap F E c := σ.commutes c
  rw [map_mul, hc]
  ring

theorem hE_smul_right {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (c : F) (x y : Fin M → E) :
    hE σ J x (c • y) = algebraMap F E c * hE σ J x y := by
  simp only [hE, Formalism.UG.hform, Pi.smul_apply, Algebra.smul_def]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

def trForm {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) : LinearMap.BilinForm F (Fin M → E) :=
  LinearMap.mk₂ F (fun x y => Algebra.trace F E (hE σ J x y))
    (fun x x' y => by simp only [hE_add_left, map_add (f := _)])
    (fun c x y => by simp only [hE_smul_left, ← Algebra.smul_def, map_smul])
    (fun x y y' => by simp only [hE_add_right, map_add (f := _)])
    (fun c x y => by simp only [hE_smul_right, ← Algebra.smul_def, map_smul])

theorem hE_single {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (x : Fin M → E) (j : Fin M) (c : E) :
    hE σ J x (Pi.single j c) = (∑ i, σ (x i) * J i j) * c := by
  simp [hE, Formalism.UG.hform, Pi.single_apply, Finset.sum_mul]

theorem trace_gram_nondegenerate : TraceGramND := by
  intro F E _ _ _ _ _ σ hCM M J hJ k b
  have hfin : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hCM.2.2.1
  have hG : (Matrix.of fun i j => Algebra.trace F E (hE σ J (b i) (b j))) =
      LinearMap.BilinForm.toMatrix b (trForm σ J) := by
    ext i j
    simp [trForm, LinearMap.BilinForm.toMatrix_apply]
  rw [hG, ← LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b]
  refine LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft ?_
  intro x hx
  have hrow : ∀ j, ∑ i, σ (x i) * J i j = 0 := by
    intro j
    apply (traceForm_nondegenerate F E).1
    intro c
    have h1 := hx (Pi.single j c)
    simp only [trForm, LinearMap.mk₂_apply] at h1
    rw [Algebra.traceForm_apply, ← hE_single]
    exact h1
  have hv : Matrix.vecMul (fun i => σ (x i)) J = 0 := funext fun j => by
    simpa [Matrix.vecMul, dotProduct] using hrow j
  by_contra hx0
  have hne : (fun i => σ (x i)) ≠ 0 := by
    intro h
    apply hx0
    funext i
    have := congrFun h i
    simpa using this
  exact hJ.2 (Matrix.exists_vecMul_eq_zero_iff.mp ⟨_, hne, hv⟩)

end PI.VolSemiDirect.W.Cj
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.UniHaar
noncomputable section

namespace PI.VolSemiDirect.W.Cj

open MeasureTheory

def IsLowUni {A : Type} [CommRing A] {k : ℕ} (U : Matrix (Fin k) (Fin k) A) : Prop :=
  (∀ i, U i i = 1) ∧ ∀ i j : Fin k, i < j → U i j = 0

theorem mulVec_succAbove_step {A : Type} [CommRing A] [MeasurableSpace A] [MeasurableAdd₂ A]
    [MeasurableMul₂ A] (ν : Measure A) [SigmaFinite ν] [ν.IsAddLeftInvariant] {k : ℕ}
    (U : Matrix (Fin (k + 1)) (Fin (k + 1)) A) (p : Fin (k + 1)) (hpp : U p p = 1)
    (hp : ∀ i, U (p.succAbove i) p = 0)
    (hIH : MeasurePreserving (U.submatrix p.succAbove p.succAbove).mulVec
      (Measure.pi fun _ : Fin k => ν) (Measure.pi fun _ : Fin k => ν)) :
    MeasurePreserving U.mulVec (Measure.pi fun _ : Fin (k + 1) => ν)
      (Measure.pi fun _ : Fin (k + 1) => ν) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => A) p with he
  have he_mp : MeasurePreserving e (Measure.pi fun _ : Fin (k + 1) => ν)
      (ν.prod (Measure.pi fun _ : Fin k => ν)) :=
    measurePreserving_piFinSuccAbove (fun _ => ν) p
  set U' := U.submatrix p.succAbove p.succAbove with hU'
  set r : (Fin k → A) → A := fun v => ∑ i, U p (p.succAbove i) * v i with hr
  have hrm : Measurable r :=
    Finset.measurable_sum _ fun i _ => measurable_const.mul (measurable_pi_apply i)
  have hskew : MeasurePreserving (fun z : (Fin k → A) × A => (U'.mulVec z.1, r z.1 + z.2))
      ((Measure.pi fun _ : Fin k => ν).prod ν) ((Measure.pi fun _ : Fin k => ν).prod ν) :=
    hIH.skew_product (g := fun v a => r v + a) ((hrm.comp measurable_fst).add measurable_snd)
      (Filter.Eventually.of_forall fun v => map_add_left_eq_self ν (r v))
  have hT : MeasurePreserving (fun z : A × (Fin k → A) => (r z.2 + z.1, U'.mulVec z.2))
      (ν.prod (Measure.pi fun _ : Fin k => ν)) (ν.prod (Measure.pi fun _ : Fin k => ν)) :=
    (Measure.measurePreserving_swap.comp hskew).comp Measure.measurePreserving_swap
  have hmul : U.mulVec = e.symm ∘ (fun z : A × (Fin k → A) => (r z.2 + z.1, U'.mulVec z.2)) ∘ e := by
    funext x
    apply e.injective
    simp only [Function.comp_apply, MeasurableEquiv.apply_symm_apply]
    have hex : ∀ y : Fin (k + 1) → A, e y = (y p, fun i => y (p.succAbove i)) := fun y => rfl
    rw [hex, hex]
    refine Prod.ext ?_ ?_
    · show (∑ j, U p j * x j) = r (fun i => x (p.succAbove i)) + x p
      rw [Fin.sum_univ_succAbove _ p, hpp, one_mul, add_comm]
    · funext i
      show (∑ j, U (p.succAbove i) j * x j) = ∑ j, U' i j * x (p.succAbove j)
      rw [Fin.sum_univ_succAbove _ p, hp i, zero_mul, zero_add]
      rfl
  rw [hmul]
  exact (MeasurePreserving.symm e he_mp).comp (hT.comp he_mp)

theorem uni_measurePreserving {A : Type} [CommRing A] [MeasurableSpace A] [MeasurableAdd₂ A]
    [MeasurableMul₂ A] (ν : Measure A) [SigmaFinite ν] [ν.IsAddLeftInvariant] :
    ∀ (k : ℕ) (U : Matrix (Fin k) (Fin k) A), (IsLowUni U ∨ IsLowUni U.transpose) →
      MeasurePreserving U.mulVec (Measure.pi fun _ : Fin k => ν)
        (Measure.pi fun _ : Fin k => ν) := by
  intro k
  induction k with
  | zero =>
    intro U _
    have h0 : U.mulVec = id := by
      funext x i
      exact i.elim0
    rw [h0]
    exact MeasurePreserving.id _
  | succ k ih =>
    intro U hU
    rcases hU with hL | hT
    · refine mulVec_succAbove_step ν U (Fin.last k) (hL.1 _) (fun i => ?_)
        (ih _ (Or.inl ⟨fun a => ?_, fun a b hab => ?_⟩))
      · rw [Fin.succAbove_last]
        exact hL.2 _ _ (Fin.castSucc_lt_last i)
      · simp only [Matrix.submatrix_apply, Fin.succAbove_last]
        exact hL.1 _
      · simp only [Matrix.submatrix_apply, Fin.succAbove_last]
        exact hL.2 _ _ (Fin.castSucc_lt_castSucc_iff.mpr hab)
    · refine mulVec_succAbove_step ν U 0 (hT.1 0) (fun i => ?_)
        (ih _ (Or.inr ⟨fun a => ?_, fun a b hab => ?_⟩))
      · rw [Fin.succAbove_zero]
        exact hT.2 0 i.succ (Fin.succ_pos i)
      · simp only [Matrix.transpose_apply, Matrix.submatrix_apply, Fin.succAbove_zero]
        exact hT.1 _
      · simp only [Matrix.transpose_apply, Matrix.submatrix_apply, Fin.succAbove_zero]
        exact hT.2 _ _ (Fin.succ_lt_succ_iff.mpr hab)

theorem uni_haar {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [LocallyCompactSpace A] [SecondCountableTopology A] [T2Space A] [MeasurableSpace A]
    [BorelSpace A] (k : ℕ) (U : Matrix (Fin k) (Fin k) A) (hU : IsLowUni U ∨ IsLowUni U.transpose)
    (μ : Measure (Fin k → A)) [μ.IsAddHaarMeasure] : μ.map U.mulVec = μ := by
  have hpi : (Measure.pi fun _ : Fin k => (Measure.addHaar : Measure A)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  rw [Measure.isAddLeftInvariant_eq_smul μ (Measure.pi fun _ : Fin k => (Measure.addHaar : Measure A)),
    Measure.map_smul, (uni_measurePreserving (Measure.addHaar : Measure A) k U hU).map_eq]
  exact (uni_measurePreserving (Measure.addHaar : Measure A) k U hU).aemeasurable

theorem transvection_uni {A : Type} [CommRing A] {k : ℕ} (i j : Fin k) (hij : i ≠ j) (c : A) :
    IsLowUni (Matrix.transvection i j c) ∨ IsLowUni (Matrix.transvection i j c).transpose := by
  have key : ∀ a b : Fin k, (i = a ∧ j = b → False) → Matrix.single i j c a b = 0 := fun a b h => by
    rw [Matrix.single_apply, if_neg (fun hh => h hh)]
  have tac : ∀ a b : Fin k, (a < b ∧ i = a ∧ j = b → False) ∨ True := fun _ _ => Or.inr trivial
  rcases lt_or_gt_of_ne hij with h | h
  · right
    refine ⟨fun a => ?_, fun a b hab => ?_⟩
    · simp only [Matrix.transvection, Matrix.transpose_apply, Matrix.add_apply, Matrix.one_apply_eq]
      rw [key a a (fun ⟨h1, h2⟩ => hij (h1.trans h2.symm)), add_zero]
    · simp only [Matrix.transvection, Matrix.transpose_apply, Matrix.add_apply]
      rw [Matrix.one_apply_ne (ne_of_gt hab), key b a (fun ⟨h1, h2⟩ => by
        subst h1; subst h2; exact absurd (lt_trans h hab) (lt_irrefl _)), add_zero]
  · left
    refine ⟨fun a => ?_, fun a b hab => ?_⟩
    · simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply_eq]
      rw [key a a (fun ⟨h1, h2⟩ => hij (h1.trans h2.symm)), add_zero]
    · simp only [Matrix.transvection, Matrix.add_apply]
      rw [Matrix.one_apply_ne (ne_of_lt hab), key a b (fun ⟨h1, h2⟩ => by
        subst h1; subst h2; exact absurd (lt_trans h hab) (lt_irrefl _)), add_zero]

theorem transvection_preserves_haar : TransvHaar := by
  intro A _ _ _ _ _ _ _ _ k i j hij c μ hμ
  haveI := hμ
  exact uni_haar k _ (transvection_uni i j hij c) μ

end PI.VolSemiDirect.W.Cj
end
end

namespace PI.VolSemiDirect.W.Cj

theorem orthogonal_invariance_of_stable_rank_one (h1 : AdeleStableRankOne) : OrthInv :=
  orthInv_of h1 gl_generated_transvections_diag transvection_preserves_haar

theorem unipotent_modulus_of_stable_rank_one (h1 : AdeleStableRankOne) : VMod :=
  vMod_of (orthogonal_invariance_of_stable_rank_one h1) trace_basis_holds trace_gram_nondegenerate

theorem unipotent_modulus_holds : VMod := unipotent_modulus_of_stable_rank_one PI.VolSemiDirect.W.SR.stable_rank_one_adeles

end PI.VolSemiDirect.W.Cj
