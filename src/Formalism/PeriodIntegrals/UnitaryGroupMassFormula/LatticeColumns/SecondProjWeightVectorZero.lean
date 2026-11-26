module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.ThetaEpsCases

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.QtoPInvMulVec
noncomputable section

namespace PIW.MassDataColumns

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets Formalism.L2.SG.Measures Formalism.L2.SG.Sub
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain Formalism.FourierDecayAlt.S3 MassDataIdxSteps MassDataIdxStIm MassDataIdxSpl
open scoped Matrix TensorProduct

variable {D : D7}

def crd (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)
    (Q : GL (Idx D.R.rS D.R.k) (FpX X p)) (v : Fin X.B.I.n → TpX X p) : Idx D.R.rS D.R.k → FpX X p :=
  ((Q⁻¹ : GL (Idx D.R.rS D.R.k) (FpX X p)) : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p)) *ᵥ
    (pr1 θ v ∘ (idxEquiv X).symm)

section Crd

variable (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)
  (Q : GL (Idx D.R.rS D.R.k) (FpX X p))

theorem crd_add (v w : Fin X.B.I.n → TpX X p) : crd X p θ Q (v + w) = crd X p θ Q v + crd X p θ Q w := by
  simp only [crd, map_add (f := _), Pi.add_comp, Matrix.mulVec_add]

theorem crd_sub (v w : Fin X.B.I.n → TpX X p) : crd X p θ Q (v - w) = crd X p θ Q v - crd X p θ Q w := by
  simp only [crd, map_sub, Pi.sub_comp, Matrix.mulVec_sub]

theorem crd_zero : crd X p θ Q 0 = 0 := by
  simp only [crd, map_zero, Pi.zero_comp, Matrix.mulVec_zero]

theorem crd_smul (t : TpX X p) (v : Fin X.B.I.n → TpX X p) :
    crd X p θ Q (t • v) = (θ t).1 • crd X p θ Q v := by
  have h : pr1 θ (t • v) = (θ t).1 • pr1 θ v := by
    funext i
    show (θ (t * v i)).1 = (θ t).1 * (θ (v i)).1
    rw [map_mul]
    rfl
  unfold crd
  rw [h, Pi.smul_comp, Matrix.mulVec_smul]

theorem crd_mulVec (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (TpX X p)) (v : Fin X.B.I.n → TpX X p) :
    crd X p θ Q (M *ᵥ v) =
      (((Q⁻¹ : GL (Idx D.R.rS D.R.k) (FpX X p)) : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p)) *
        Matrix.reindex (idxEquiv X) (idxEquiv X) (M.map fun t => (θ t).1) *
        (Q : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p))) *ᵥ crd X p θ Q v := by
  have h1 : pr1 θ (M *ᵥ v) = (M.map fun t => (θ t).1) *ᵥ pr1 θ v := by
    funext i
    show (θ ((M *ᵥ v) i)).1 = ((M.map fun t => (θ t).1) *ᵥ pr1 θ v) i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Prod.fst_sum, Prod.fst_mul, Matrix.map_apply]
    rfl
  have h2 : ((M.map fun t => (θ t).1) *ᵥ pr1 θ v) ∘ (idxEquiv X).symm =
      Matrix.reindex (idxEquiv X) (idxEquiv X) (M.map fun t => (θ t).1) *ᵥ (pr1 θ v ∘ (idxEquiv X).symm) := by
    rw [Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
    funext s
    simp [Function.comp_def]
  unfold crd
  rw [h1, h2]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

theorem reindex_inv_mulVec (w : Fin X.B.I.n → FpX X p) :
    ((reindex₂ X p Q)⁻¹ : GL (Fin X.B.I.n) (FpX X p)) *ᵥ w =
      (((Q⁻¹ : GL (Idx D.R.rS D.R.k) (FpX X p)) : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p)) *ᵥ
        (w ∘ (idxEquiv X).symm)) ∘ (idxEquiv X) := by
  unfold reindex₂
  show (Matrix.reindexAlgEquiv (FpX X p) (FpX X p) (idxEquiv X).symm
    ((Q⁻¹ : GL (Idx D.R.rS D.R.k) (FpX X p)) : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p))) *ᵥ w = _
  rw [Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Equiv.symm_symm, Matrix.submatrix_mulVec_equiv]

theorem crd_int_of_lat (hL : LatBasis X p θ (reindex₂ X p Q)) (v : Fin X.B.I.n → TpX X p)
    (hv : v ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))) (s : Idx D.R.rS D.R.k) :
    crd X p θ Q v s ∈ p.1.adicCompletionIntegers X.B.I.F := by
  have h := ((hL v).mp hv).1 ((idxEquiv X).symm s)
  rw [reindex_inv_mulVec] at h
  simp only [Function.comp_apply, Equiv.apply_symm_apply] at h
  exact h

theorem lat_of_crd (hL : LatBasis X p θ (reindex₂ X p Q)) (v : Fin X.B.I.n → TpX X p)
    (h2 : pr2 θ v = 0) (h1 : ∀ s, crd X p θ Q v s ∈ p.1.adicCompletionIntegers X.B.I.F) :
    v ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
  refine (hL v).mpr ⟨fun i => ?_, ?_⟩
  · have h := h1 ((idxEquiv X) i)
    rw [reindex_inv_mulVec, Function.comp_apply]
    exact h
  · intro i
    have hz : (fun j => th2 X p θ (v j)) = 0 := h2
    rw [hz, Matrix.mulVec_zero]
    exact zero_mem _

end Crd

end PIW.MassDataColumns
end
end

noncomputable section

namespace PIW.MassDataColumns

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets Formalism.L2.SG.Measures Formalism.L2.SG.Sub
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain Formalism.FourierDecayAlt.S3 MassDataIdxSteps MassDataIdxStIm MassDataIdxSpl
open scoped Matrix TensorProduct

variable {D : D7}

section Crd2

variable (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)
  (Q : GL (Idx D.R.rS D.R.k) (FpX X p))

theorem crd_osmul (c : p.1.adicCompletionIntegers X.B.I.F) (v : Fin X.B.I.n → TpX X p) :
    crd X p θ Q (c • v) = (c : FpX X p) • crd X p θ Q v := by
  have hcv : c • v = (c : FpX X p) • v := by
    first
      | rfl
      | exact (algebraMap_smul (FpX X p) c v).symm
  rw [hcv]
  unfold crd
  rw [map_smul]
  exact Matrix.mulVec_smul _ _ _

theorem gOf_nonunit : ¬ IsUnit ((gOf p : ℕ) : p.1.adicCompletionIntegers X.B.I.F) := by
  intro hu
  obtain ⟨w, hw⟩ := g_eq_gOf_mul_unit X p
  apply imA_g_nonunit (X := X) p
  rw [hw]
  exact hu.mul w.isUnit

theorem crd_gLam (hL : LatBasis X p θ (reindex₂ X p Q)) (v : Fin X.B.I.n → TpX X p) (hv : v ∈ gLam X p)
    (s : Idx D.R.rS D.R.k) :
    ∃ y : p.1.adicCompletionIntegers X.B.I.F, crd X p θ Q v s = ((gOf p : ℕ) : FpX X p) * (y : FpX X p) := by
  have hv' : v ∈ Ideal.span {((gOf p : ℕ) : p.1.adicCompletionIntegers X.B.I.F)} •
      latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
    rw [← imA_span_Bg (X := X) p]
    exact hv
  refine Submodule.smul_induction_on hv' ?_ ?_
  · intro r hr m hm
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    obtain ⟨y0, hy0⟩ : ∃ y0 : p.1.adicCompletionIntegers X.B.I.F, (y0 : FpX X p) = crd X p θ Q m s :=
      ⟨⟨_, crd_int_of_lat (hL := hL) (v := m) (hv := hm) (s := s)⟩, rfl⟩
    refine ⟨a * y0, ?_⟩
    rw [crd_osmul, Pi.smul_apply, smul_eq_mul, ← hy0]
    push_cast
    ring
  · rintro x y ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a + b, ?_⟩
    rw [crd_add, Pi.add_apply, ha, hb]
    push_cast
    ring

end Crd2

section W

variable (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X)
  (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p) (Q : GL (Idx D.R.rS D.R.k) (FpX X p))

theorem coords_weight_vector (hW : WClause X hb u p θ Q) (i : Fin D.R.k) :
    ∃ c : Idx D.R.rS D.R.k → p.1.adicCompletionIntegers X.B.I.F,
      crd X p θ Q (((HA.mat (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (xuP X hb u p) : GL (Fin X.B.I.n) (TpX X p)) :
          Matrix (Fin X.B.I.n) (Fin X.B.I.n) (TpX X p)) *ᵥ PI.FinKW.vecV X.B.I p.1 (X.bw i)) =
        Pi.single (wI i) 1 - ((gOf p : ℕ) : FpX X p) • (fun s => ((c s : p.1.adicCompletionIntegers X.B.I.F) : FpX X p)) := by
  obtain ⟨c, hc⟩ := hW i
  refine ⟨c, ?_⟩
  have h2 := congrArg (fun w => ((Q⁻¹ : GL (Idx D.R.rS D.R.k) (FpX X p)) :
    Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p)) *ᵥ w) hc
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Units.inv_mul,
    Matrix.one_mulVec] at h2
  unfold crd
  rw [← h2]
  exact (sub_sub_cancel _ _).symm

theorem theta_eps_one (hθ : IsSplitEquiv X p θ) (hW : WClause X hb u p θ Q) (i : Fin D.R.k) :
    θ (epsP X p) = (1, 0) := by
  have hσ : sigR (FpX X p) X.B.I.cm.sig (epsP X p) = 1 - epsP X p :=
    (psiV_sigA X p X.ew).symm.trans (imA_eps'_eq (X := X) p).symm
  have hsw := hθ (epsP X p)
  rw [hσ, map_sub, map_one] at hsw
  have key : ∀ N : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (TpX X p),
      crd X p θ Q (N *ᵥ PI.FinKW.vecV X.B.I p.1 (X.bw i)) =
        (θ (epsP X p)).1 • crd X p θ Q (N *ᵥ PI.FinKW.vecV X.B.I p.1 (X.bw i)) := by
    intro N
    rw [← crd_smul, ← Matrix.mulVec_smul, imA_bw_eps]
  obtain ⟨c, hc⟩ := coords_weight_vector X hb u p θ Q hW i
  have h2 := hc
  rw [key] at h2
  rw [hc] at h2
  have h3 := congrFun h2 (wI i)
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.single_eq_same, smul_eq_mul] at h3
  have ha : (θ (epsP X p)).1 = 1 := by
    by_contra hne
    have h5 : ((θ (epsP X p)).1 - 1) *
        (1 - ((gOf p : ℕ) : FpX X p) * ((c (wI i) : p.1.adicCompletionIntegers X.B.I.F) : FpX X p)) = 0 := by
      linear_combination h3
    rcases mul_eq_zero.1 h5 with h | h
    · exact hne (sub_eq_zero.1 h)
    · apply gOf_nonunit X p
      refine isUnit_iff_exists_inv.2 ⟨c (wI i), ?_⟩
      apply Subtype.ext
      push_cast
      linear_combination -h
  have h6 := congrArg Prod.fst hsw
  simp only [Prod.fst_sub, Prod.fst_one, Prod.fst_swap, ha, sub_self] at h6
  exact Prod.ext ha h6.symm

theorem secondProj_weight_vector_zero (hε : θ (epsP X p) = (1, 0)) (i : Fin D.R.k) :
    pr2 θ (PI.FinKW.vecV X.B.I p.1 (X.bw i)) = 0 := by
  rw [← imA_bw_eps (X := X) p i]
  funext j
  show (θ (epsP X p * PI.FinKW.vecV X.B.I p.1 (X.bw i) j)).2 = 0
  simp [map_mul, hε]

end W

end PIW.MassDataColumns
