module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SiegelSmall
public import Development.AutomorphicArithmetic.LocalEmbeddings.OppLagr

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SmallSB
section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SmallSA
noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def cmbE (bs : Module.Basis (Fin 2) F E) (c : Fin 2 → AF F) : AE F E := ∑ t, c t • ((1 : AF F) ⊗ₜ[F] bs t)

theorem cmbE_eq (bs : Module.Basis (Fin 2) F E) (c : Fin 2 → AF F) :
    cmbE bs c = ∑ t, c t • (Algebra.TensorProduct.basis (AF F) bs) t := by
  simp [cmbE, Algebra.TensorProduct.basis_apply]

theorem repr_cmbE_apply (bs : Module.Basis (Fin 2) F E) (c : Fin 2 → AF F) (t : Fin 2) :
    (Algebra.TensorProduct.basis (AF F) bs).repr (cmbE bs c) t = c t := by
  rw [cmbE_eq, Module.Basis.repr_sum_self]

theorem cmbE_repr (bs : Module.Basis (Fin 2) F E) (z : AE F E) :
    cmbE bs (fun t => (Algebra.TensorProduct.basis (AF F) bs).repr z t) = z := by
  rw [cmbE_eq]
  exact (Algebra.TensorProduct.basis (AF F) bs).sum_repr z

def cmbB {m n : ℕ} (bs : Module.Basis (Fin 2) F E) (y : Fin m × Fin n × Fin 2 → AF F) : Mx F E m n :=
  fun a i => cmbE bs fun t => y (a, i, t)

theorem crdB_cmbB {m n : ℕ} (bs : Module.Basis (Fin 2) F E) (y : Fin m × Fin n × Fin 2 → AF F) :
    crdB bs (cmbB bs y) = y := by
  funext k
  simp only [crdB, cmbB, repr_cmbE_apply]

theorem cmbB_crdB {m n : ℕ} (bs : Module.Basis (Fin 2) F E) (X : Mx F E m n) : cmbB bs (crdB bs X) = X := by
  funext a i
  simp only [cmbB, crdB, cmbE_repr]

def Lk {m n : ℕ} (bs : Module.Basis (Fin 2) F E) (M : Matrix (Fin m) (Fin m) (AE F E)) (y : Fin m × Fin n × Fin 2 → AF F) :
    Fin m × Fin n × Fin 2 → AF F := crdB bs (M * cmbB bs y)

theorem Lk_crdB {m n : ℕ} (bs : Module.Basis (Fin 2) F E) (M : Matrix (Fin m) (Fin m) (AE F E)) (X : Mx F E m n) :
    Lk bs M (crdB bs X) = crdB bs (M * X) := by rw [Lk, cmbB_crdB]

theorem Lk_one {m n : ℕ} (bs : Module.Basis (Fin 2) F E) (y : Fin m × Fin n × Fin 2 → AF F) : Lk bs 1 y = y := by
  rw [Lk, Matrix.one_mul, crdB_cmbB]

theorem Lk_mul {m n : ℕ} (bs : Module.Basis (Fin 2) F E) (M M' : Matrix (Fin m) (Fin m) (AE F E))
    (y : Fin m × Fin n × Fin 2 → AF F) : Lk bs (M * M') y = Lk bs M (Lk bs M' y) := by
  rw [Lk, Lk, Lk, cmbB_crdB, Matrix.mul_assoc]

theorem Lk_zero {m n : ℕ} (bs : Module.Basis (Fin 2) F E) (M : Matrix (Fin m) (Fin m) (AE F E)) :
    Lk (n := n) bs M 0 = 0 := by
  have : cmbB (m := m) (n := n) bs 0 = 0 := by
    funext a i; simp [cmbB, cmbE]
  funext k
  simp [Lk, this, crdB]

def Lc {m : ℕ} (bs : Module.Basis (Fin 2) F E) (M : Matrix (Fin m) (Fin m) (AE F E)) (v : Fin m × Fin 2 → AF F) :
    Fin m × Fin 2 → AF F :=
  fun p => (Algebra.TensorProduct.basis (AF F) bs).repr ((M *ᵥ fun a => cmbE bs fun t => v (a, t)) p.1) p.2

theorem Lc_zero {m : ℕ} (bs : Module.Basis (Fin 2) F E) (M : Matrix (Fin m) (Fin m) (AE F E)) : Lc bs M 0 = 0 := by
  funext p
  have hz : (fun _ : Fin m => (0 : AE F E)) = 0 := rfl
  simp [Lc, cmbE, hz, Matrix.mulVec_zero]

theorem triple_index_symm_embedded {m n N : ℕ} (h : n + 1 = N) (a : Fin m) (j : Fin n) (t : Fin 2) :
    (eK m h).symm (a, em0 h j, t) = Sum.inl (a, j, t) := by
  rw [Equiv.symm_apply_eq]; rfl

theorem triple_index_symm_last {m n N : ℕ} (h : n + 1 = N) (a : Fin m) (t : Fin 2) :
    (eK m h).symm (a, i0 h, t) = Sum.inr (a, t) := by
  rw [Equiv.symm_apply_eq]; rfl

theorem Lk_eK {m n N : ℕ} (h : n + 1 = N) (bs : Module.Basis (Fin 2) F E) (M : Matrix (Fin m) (Fin m) (AE F E))
    (x : K1 m n → AF F) :
    Lk bs M (x ∘ (eK m h).symm) ∘ eK m h = Sum.elim (Lk bs M (x ∘ Sum.inl)) (Lc bs M (x ∘ Sum.inr)) := by
  funext k
  rcases k with ⟨a, j, t⟩ | ⟨a, t⟩
  · have hk : eK m h (Sum.inl (a, j, t)) = (a, em0 h j, t) := rfl
    simp only [Function.comp_apply, hk, Sum.elim_inl, Lk, crdB, cmbB, Matrix.mul_apply, triple_index_symm_embedded]
  · have hk : eK m h (Sum.inr (a, t)) = (a, i0 h, t) := rfl
    simp only [Function.comp_apply, hk, Sum.elim_inr, Lk, Lc, crdB, cmbB, Matrix.mul_apply, Matrix.mulVec,
      dotProduct, triple_index_symm_last]

end PositivityTheory.SiegelWeilFormula.Ald

end
end

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem det_mul_conj {m : ℕ} {J : Matrix (Fin m) (Fin m) E} (hJ : J.det ≠ 0) (g : UA σ J) :
    ((Matrix.GeneralLinearGroup.det (g : GL (Fin m) (AE F E)) : (AE F E)ˣ) : AE F E) *
      cA σ ((Matrix.GeneralLinearGroup.det (g : GL (Fin m) (AE F E)) : (AE F E)ˣ) : AE F E) = 1 := by
  have h := congrArg Matrix.det (show ((g : GL (Fin m) (AE F E)) : Matrix (Fin m) (Fin m) (AE F E))ᵀ * incM F J *
    ((g : GL (Fin m) (AE F E)) : Matrix (Fin m) (Fin m) (AE F E)).map (cA σ) = incM F J from g.2)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    show (((g : GL (Fin m) (AE F E)) : Matrix (Fin m) (Fin m) (AE F E)).map (cA σ)).det =
      cA σ ((g : GL (Fin m) (AE F E)) : Matrix (Fin m) (Fin m) (AE F E)).det from
      ((cA σ).toRingHom.map_det _).symm] at h
  have hu : IsUnit (incM F J).det := by
    have e : (incM F J).det = (inclR (F := F) (E := E) (AF F)) J.det := by
      rw [incM]
      exact (RingHom.map_det (inclR (F := F) (E := E) (AF F) : E →+* AE F E) J).symm
    rw [e]
    exact (Ne.isUnit hJ).map _
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  refine hu.mul_left_cancel ?_
  linear_combination h

theorem norm_det_unitary (hcm : IsCMExt F E σ) {m : ℕ} {J : Matrix (Fin m) (Fin m) E} (hJ : J.det ≠ 0) (g : UA σ J) :
    Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det (g : GL (Fin m) (AE F E))) = 1 := by
  obtain ⟨ξ, hq⟩ := GlobalTheory.OppLagr.exists_isQuad hcm
  refine Units.ext (hq.algebraMap_injective ?_)
  rw [Units.coe_map, Units.val_one, map_one]
  show algebraMap (AF F) (AE F E) (Algebra.norm (AF F) _) = 1
  rw [hq.algebraMap_norm]
  exact det_mul_conj hJ g

end PositivityTheory.SiegelWeilFormula.Ald

end
end

noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def colv (m : ℕ) (bs : Module.Basis (Fin 2) F E) : (Fin m × Fin 2 → AF F) ≃ₜ+ (Fin m → AE F E) :=
  haveI : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) _
  { toFun v a := cmbE bs fun t => v (a, t)
    invFun z p := (Algebra.TensorProduct.basis (AF F) bs).repr (z p.1) p.2
    left_inv v := by
      funext p
      exact repr_cmbE_apply bs _ p.2
    right_inv z := by
      funext a
      exact cmbE_repr bs (z a)
    map_add' v w := by
      funext a
      simp only [cmbE, Pi.add_apply, add_smul, Finset.sum_add_distrib]
    continuous_toFun := by
      refine continuous_pi fun a => ?_
      have h : (fun v : Fin m × Fin 2 → AF F => cmbE bs fun t => v (a, t)) =
          (GlobalTheory.JacSubst.coordCE F E bs).symm ∘ fun v t => v (a, t) := by
        funext v
        simp only [Function.comp_apply, cmbE_eq]
        change _ = (Algebra.TensorProduct.basis (AF F) bs).equivFun.symm (fun t => v (a, t))
        rw [Module.Basis.equivFun_symm_apply]
      rw [h]
      exact (GlobalTheory.JacSubst.coordCE F E bs).symm.continuous.comp (continuous_pi fun t => continuous_apply _)
    continuous_invFun := by
      refine continuous_pi fun p => ?_
      exact (continuous_apply p.2).comp ((GlobalTheory.JacSubst.coordCE F E bs).continuous.comp (continuous_apply p.1)) }

theorem Lc_eq_colv {m : ℕ} (bs : Module.Basis (Fin 2) F E) (M : Matrix (Fin m) (Fin m) (AE F E))
    (v : Fin m × Fin 2 → AF F) : Lc bs M v = (colv m bs).symm (M *ᵥ colv m bs v) := rfl

def HaarLc : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (m : ℕ) (J : Matrix (Fin m) (Fin m) E), J.det ≠ 0 → ∀ (bs : Module.Basis (Fin 2) F E) (g : UA σ J)
    (μ : @Measure (Fin m × Fin 2 → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ f : (Fin m × Fin 2 → AF F) → ℝ≥0∞, ∫⁻ x, f (Lc bs (mat g) x) ∂μ = ∫⁻ x, f x ∂μ

end PositivityTheory.SiegelWeilFormula.Ald

end
