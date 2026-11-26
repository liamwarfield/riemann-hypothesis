module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SecondCoordsMulGL
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ReductionImageOfAdaptedMod
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.SecondProjWeightVectorZero

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.PsiVIteOne
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SplitLatticeBasisExists
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.PsiVHA
noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed MassDataIdxSpl Matrix
  MassDataIdxFrA MassDataIdxAdA
open scoped TensorProduct

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)
  (Q : GL (IdxD D) (FpX X p))

theorem pair_sum (v w : Fin X.B.I.n → TpX X p) :
    crd2 X p θ Q v ⬝ᵥ crd1 X p θ Q w =
      ∑ i, ∑ j, (θ (v i)).2 * ((θ (inclR (FpX X p) (X.B.I.J i j))).1 * (θ (w j)).1) := by
  unfold crd1 crd2
  rw [Matrix.mulVec_transpose, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
  simp only [dotProduct, Matrix.mulVec, Function.comp_apply]
  rw [← Equiv.sum_comp (idxEquiv X).symm.symm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Equiv.symm_symm, Equiv.symm_apply_apply, fst_apply_alt, snd_apply_alt, jm1, JR, Matrix.map_apply]
  rw [Finset.mul_sum]

theorem pair1 (hθ : IsSplitEquiv X p θ) (v w : Fin X.B.I.n → TpX X p) :
    crd2 X p θ Q v ⬝ᵥ crd1 X p θ Q w = (θ (hR (FpX X p) X.B.I.cm.sig X.B.I.J v w)).1 := by
  rw [pair_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hR, Formalism.UG.hform, map_sum, Prod.fst_sum, map_mul, Prod.fst_mul, JR, Matrix.map_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hθ (v i), Prod.fst_swap]
  ring

theorem pair2 (hθ : IsSplitEquiv X p θ) (v w : Fin X.B.I.n → TpX X p) :
    crd1 X p θ Q v ⬝ᵥ crd2 X p θ Q w = (θ (hR (FpX X p) X.B.I.cm.sig X.B.I.J v w)).2 := by
  rw [dotProduct_comm, pair_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hR, Formalism.UG.hform, map_sum, Prod.snd_sum, map_mul, Prod.snd_mul, JR, Matrix.map_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hθ (v i), Prod.snd_swap]
  have h := secondEmbedding_eq_star X p θ hθ (X.B.I.J i j)
  rw [herm_entry] at h
  have h' : (θ (inclR (FpX X p) (X.B.I.J i j))).2 = (θ (inclR (FpX X p) (X.B.I.J j i))).1 := h
  rw [h']
  ring

theorem psiV_hA' (x y : Formalism.L2.SG.HidaSetting.VA X.B.I) :
    PI.FinKW.psiV X.B.I p.1 (hA X.B.I x y) =
      hR (FpX X p) X.B.I.cm.sig X.B.I.J (PI.FinKW.vecV X.B.I p.1 x) (PI.FinKW.vecV X.B.I p.1 y) := by
  have hi : ∀ a : X.B.I.E, PI.FinKW.psiV X.B.I p.1 (Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) a) =
      inclR (FpX X p) a := by
    intro a
    show (Algebra.TensorProduct.map (evalV X.B.I.F p.1) (AlgHom.id X.B.I.F X.B.I.E))
        ((Algebra.TensorProduct.comm X.B.I.F X.B.I.E (Formalism.MainNotions.S.Af X.B.I.F)) (a ⊗ₜ[X.B.I.F] (1 : Formalism.MainNotions.S.Af X.B.I.F))) =
      (1 : FpX X p) ⊗ₜ[X.B.I.F] a
    rw [Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.map_tmul, map_one]
    rfl
  have hs := PIW.MassDataColumns.psiV_sigA X p
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hA, hR, Formalism.UG.hform, map_sum, map_mul, Matrix.map_apply, JR, PI.FinKW.vecV]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← hs, hi]

end Loc

end MassDataIdxSteps
end
end

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed MassDataIdxSpl Matrix
  MassDataIdxFrA MassDataIdxAdA
open scoped TensorProduct

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)
  (Q : GL (IdxD D) (FpX X p))

theorem zmod_comp (hL : LatBasis X p θ (reindex₂ X p Q)) (c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)
    (hc : ZMod' X.B.I X.B.g c) :
    (∃ y : OvA X p, (θ (PI.FinKW.psiV X.B.I p.1 c)).1 = ((gOf p : ℕ) : FpX X p) * (y : FpX X p)) ∧
    (∃ y : OvA X p, (θ (PI.FinKW.psiV X.B.I p.1 c)).2 = ((gOf p : ℕ) : FpX X p) * (y : FpX X p)) := by
  obtain ⟨t, ht, rfl⟩ := hc
  have hs : PI.FinKW.psiV X.B.I p.1 t ∈ OEp X p := ⟨t, ht, rfl⟩
  obtain ⟨h1, h2⟩ := oEp_int X p θ Q hL _ hs
  rw [map_mul, map_natCast, map_mul, map_natCast, imA_g_eq_mul X p]
  refine ⟨⟨((gOth X p : ℕ) : OvA X p) * ⟨_, h1⟩, ?_⟩, ⟨((gOth X p : ℕ) : OvA X p) * ⟨_, h2⟩, ?_⟩⟩
  · simp only [Prod.fst_mul, Prod.fst_natCast]
    push_cast
    ring
  · simp only [Prod.snd_mul, Prod.snd_natCast]
    push_cast
    ring

theorem cong_dir (hθ : IsSplitEquiv X p θ) (hL : LatBasis X p θ (reindex₂ X p Q))
    (x y : Formalism.L2.SG.HidaSetting.VA X.B.I) (d : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)
    (h : ZMod' X.B.I X.B.g (hA X.B.I x y - d)) :
    ∃ z : OvA X p, crd2 X p θ Q (PI.FinKW.vecV X.B.I p.1 x) ⬝ᵥ crd1 X p θ Q (PI.FinKW.vecV X.B.I p.1 y) =
      (θ (PI.FinKW.psiV X.B.I p.1 d)).1 + ((gOf p : ℕ) : FpX X p) * (z : FpX X p) := by
  obtain ⟨z, hz⟩ := (zmod_comp X p θ Q hL _ h).1
  refine ⟨z, ?_⟩
  rw [pair1 X p θ Q hθ, ← psiV_hA']
  rw [map_sub, map_sub, Prod.fst_sub] at hz
  linear_combination hz

theorem cong_sym (hθ : IsSplitEquiv X p θ) (hL : LatBasis X p θ (reindex₂ X p Q))
    (x y : Formalism.L2.SG.HidaSetting.VA X.B.I) (d : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)
    (h : ZMod' X.B.I X.B.g (hA X.B.I y x - d)) :
    ∃ z : OvA X p, crd2 X p θ Q (PI.FinKW.vecV X.B.I p.1 x) ⬝ᵥ crd1 X p θ Q (PI.FinKW.vecV X.B.I p.1 y) =
      (θ (PI.FinKW.psiV X.B.I p.1 d)).2 + ((gOf p : ℕ) : FpX X p) * (z : FpX X p) := by
  obtain ⟨z, hz⟩ := (zmod_comp X p θ Q hL _ h).2
  refine ⟨z, ?_⟩
  rw [dotProduct_comm, pair2 X p θ Q hθ, ← psiV_hA']
  rw [map_sub, map_sub, Prod.snd_sub] at hz
  linear_combination hz

end Loc

section Orient

variable {D : D7} (X : HidaSetting D) (p : TypX X)

def swapA : (FpX X p × FpX X p) ≃ₐ[FpX X p] (FpX X p × FpX X p) :=
  AlgEquiv.ofRingEquiv (f := RingEquiv.prodComm) (fun _ => rfl)

theorem exists_split_eps : ∃ θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p,
    IsSplitEquiv X p θ ∧ θ (epsP X p) = (1, 0) := by
  obtain ⟨θ₀, h₀⟩ := splitTheta_of X p (embP_holds X p)
  rcases PIW.MassDataColumns.theta_eps_cases X p θ₀ h₀ with h | h
  · exact ⟨θ₀, h₀, h⟩
  · refine ⟨θ₀.trans (swapA X p), ?_, ?_⟩
    · intro t
      rw [AlgEquiv.trans_apply, AlgEquiv.trans_apply, h₀ t]
      rfl
    · rw [AlgEquiv.trans_apply, h]
      rfl

theorem exists_GL_latBasis_of_isSplitEquiv (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p) (hθ : IsSplitEquiv X p θ) :
    ∃ Q : GL (IdxD D) (FpX X p), LatBasis X p θ (reindex₂ X p Q) := by
  obtain ⟨P, hP⟩ := latBasisAll_holds' X p θ hθ
  refine ⟨Units.map (Matrix.reindexAlgEquiv (FpX X p) (FpX X p) (idxEquiv X)).toMonoidHom P, ?_⟩
  have e : reindex₂ X p (Units.map (Matrix.reindexAlgEquiv (FpX X p) (FpX X p) (idxEquiv X)).toMonoidHom P) = P := by
    ext i j
    simp [reindex₂]
  rw [e]
  exact hP

end Orient

end MassDataIdxSteps
end
end

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed MassDataIdxSpl Matrix
  MassDataIdxFrA MassDataIdxAdA
open scoped TensorProduct

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)
  (Q : GL (IdxD D) (FpX X p))

def colV : IdxD D → Formalism.L2.SG.HidaSetting.VA X.B.I
  | Sum.inl a => X.e0 a
  | Sum.inr (Sum.inl (Sum.inl i)) => X.bw i
  | Sum.inr (Sum.inl (Sum.inr _)) => X.z0
  | Sum.inr (Sum.inr c) => X.f0 (Fin.rev c)

def rowV : IdxD D → Formalism.L2.SG.HidaSetting.VA X.B.I
  | Sum.inl a => X.f0 a
  | Sum.inr (Sum.inl (Sum.inl i)) => X.bwd i
  | Sum.inr (Sum.inl (Sum.inr _)) => X.z0
  | Sum.inr (Sum.inr c) => X.e0 (Fin.rev c)

def sgnV : IdxD D → FpX X p
  | Sum.inr (Sum.inl (Sum.inr _)) => -1
  | _ => 1

theorem fin_dir (hθ : IsSplitEquiv X p θ) (hL : LatBasis X p θ (reindex₂ X p Q)) (x y : Formalism.L2.SG.HidaSetting.VA X.B.I)
    (h : ZMod' X.B.I X.B.g (hA X.B.I x y)) :
    ∃ z : OvA X p, crd2 X p θ Q (PI.FinKW.vecV X.B.I p.1 x) ⬝ᵥ crd1 X p θ Q (PI.FinKW.vecV X.B.I p.1 y) =
      ((gOf p : ℕ) : FpX X p) * (z : FpX X p) := by
  obtain ⟨z, hz⟩ := cong_dir X p θ Q hθ hL x y 0 (by simpa using h)
  exact ⟨z, by simpa using hz⟩

theorem fin_sym (hθ : IsSplitEquiv X p θ) (hL : LatBasis X p θ (reindex₂ X p Q)) (x y : Formalism.L2.SG.HidaSetting.VA X.B.I)
    (h : ZMod' X.B.I X.B.g (hA X.B.I y x)) :
    ∃ z : OvA X p, crd2 X p θ Q (PI.FinKW.vecV X.B.I p.1 x) ⬝ᵥ crd1 X p θ Q (PI.FinKW.vecV X.B.I p.1 y) =
      ((gOf p : ℕ) : FpX X p) * (z : FpX X p) := by
  obtain ⟨z, hz⟩ := cong_sym X p θ Q hθ hL x y 0 (by simpa using h)
  exact ⟨z, by simpa using hz⟩

theorem psiV_ite_one (c : Prop) [Decidable c] :
    θ (PI.FinKW.psiV X.B.I p.1 (if c then 1 else 0)) = if c then 1 else 0 := by
  split_ifs <;> simp

theorem rc_cong (hθ : IsSplitEquiv X p θ) (hε : θ (epsP X p) = (1, 0)) (hL : LatBasis X p θ (reindex₂ X p Q))
    (s t : IdxD D) :
    ∃ z : OvA X p, sgnV X p s * (crd2 X p θ Q (PI.FinKW.vecV X.B.I p.1 (rowV X s)) ⬝ᵥ
      crd1 X p θ Q (PI.FinKW.vecV X.B.I p.1 (colV X t))) =
      (1 : Matrix (IdxD D) (IdxD D) (FpX X p)) s t + ((gOf p : ℕ) : FpX X p) * (z : FpX X p) := by
  have hg := X.gramIntegral
  have hz := X.formsAtZero
  have hW := X.weightVectorsIntegral
  rcases s with a | ((i | u) | c) <;> rcases t with b | ((j | v) | c') <;> simp only [rowV, colV, sgnV, one_mul]
  · obtain ⟨z, e⟩ := cong_sym X p θ Q hθ hL _ _ _ (hg b a).2.2
    refine ⟨z, ?_⟩
    rw [e, psiV_ite_one]
    by_cases hab : a = b
    · subst hab; simp
    · simp [hab, Ne.symm hab]
  · obtain ⟨z, e⟩ := fin_dir X p θ Q hθ hL _ _ ((hW j).2.2 a).2.1
    exact ⟨z, by rw [e]; simp⟩
  · obtain ⟨z, e⟩ := fin_dir X p θ Q hθ hL _ _ (hz.2 a).2
    exact ⟨z, by rw [e]; simp⟩
  · obtain ⟨z, e⟩ := fin_dir X p θ Q hθ hL _ _ (hg a (Fin.rev c')).2.1
    exact ⟨z, by rw [e]; simp⟩
  · obtain ⟨z, e⟩ := fin_sym X p θ Q hθ hL _ _ ((hW i).2.2 b).2.2.1
    exact ⟨z, by rw [e]; simp⟩
  · obtain ⟨z, e⟩ := cong_dir X p θ Q hθ hL _ _ _ (X.bw_dual i j)
    refine ⟨z, ?_⟩
    rw [e]
    by_cases hij : i = j
    · subst hij
      simp only [if_true]
      have : PI.FinKW.psiV X.B.I p.1 X.ew = epsP X p := rfl
      rw [this, hε]
      simp
    · simp [hij]
  · obtain ⟨z, e⟩ := fin_sym X p θ Q hθ hL _ _ (hW i).2.1
    exact ⟨z, by rw [e]; simp⟩
  · obtain ⟨z, e⟩ := fin_sym X p θ Q hθ hL _ _ ((hW i).2.2 (Fin.rev c')).2.2.2
    exact ⟨z, by rw [e]; simp⟩
  · obtain ⟨z, e⟩ := fin_sym X p θ Q hθ hL _ _ (hz.2 b).1
    exact ⟨-z, by rw [e]; simp⟩
  · obtain ⟨z, e⟩ := fin_dir X p θ Q hθ hL _ _ (hW j).1
    exact ⟨-z, by rw [e]; simp⟩
  · obtain ⟨z, e⟩ := cong_dir X p θ Q hθ hL _ _ (-1) (by rw [sub_neg_eq_add]; exact hz.1)
    refine ⟨-z, ?_⟩
    rw [e]
    simp
    ring
  · obtain ⟨z, e⟩ := fin_sym X p θ Q hθ hL _ _ (hz.2 (Fin.rev c')).2
    exact ⟨-z, by rw [e]; simp⟩
  · obtain ⟨z, e⟩ := fin_dir X p θ Q hθ hL _ _ (hg (Fin.rev c) b).1
    exact ⟨z, by rw [e]; simp⟩
  · obtain ⟨z, e⟩ := fin_dir X p θ Q hθ hL _ _ ((hW j).2.2 (Fin.rev c)).1
    exact ⟨z, by rw [e]; simp⟩
  · obtain ⟨z, e⟩ := fin_dir X p θ Q hθ hL _ _ (hz.2 (Fin.rev c)).1
    exact ⟨z, by rw [e]; simp⟩
  · obtain ⟨z, e⟩ := cong_dir X p θ Q hθ hL _ _ _ (hg (Fin.rev c) (Fin.rev c')).2.2
    refine ⟨z, ?_⟩
    rw [e, psiV_ite_one]
    by_cases hcc : c = c'
    · subst hcc; simp
    · simp [hcc]

end Loc

end MassDataIdxSteps
end
end

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed MassDataIdxSpl Matrix
  MassDataIdxFrA MassDataIdxAdA
open scoped TensorProduct

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)
  (Q : GL (IdxD D) (FpX X p))

theorem colV_lat (t : IdxD D) :
    PI.FinKW.vecV X.B.I p.1 (colV X t) ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
  have h := X.vectorsInLattice
  have key : ∀ A ∈ X.B.I.Lf, PI.FinKW.vecV X.B.I p.1 A ∈
      latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :=
    fun A hA => PI.FinKW.LocTo.mem_local_lattice_iff X.B.I A hA p.1
  rcases t with a | ((i | _) | c)
  · exact key _ (h.1 a).1
  · exact key _ (h.2.2 i).1
  · exact key _ h.2.1
  · exact key _ (h.1 _).2

theorem rowV_lat (s : IdxD D) :
    PI.FinKW.vecV X.B.I p.1 (rowV X s) ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
  have h := X.vectorsInLattice
  have key : ∀ A ∈ X.B.I.Lf, PI.FinKW.vecV X.B.I p.1 A ∈
      latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :=
    fun A hA => PI.FinKW.LocTo.mem_local_lattice_iff X.B.I A hA p.1
  rcases s with a | ((i | _) | c)
  · exact key _ (h.1 a).2
  · exact key _ (h.2.2 i).2
  · exact key _ h.2.1
  · exact key _ (h.1 _).1

theorem sgnV_int (s : IdxD D) : sgnV X p s ∈ OvA X p := by
  unfold sgnV
  split
  · exact neg_mem (one_mem _)
  · exact one_mem _

theorem sgnV_sq (s : IdxD D) : sgnV X p s * sgnV X p s = 1 := by
  unfold sgnV
  split <;> norm_num

def matC : Matrix (IdxD D) (IdxD D) (FpX X p) := fun i t => crd1 X p θ Q (PI.FinKW.vecV X.B.I p.1 (colV X t)) i

def matR : Matrix (IdxD D) (IdxD D) (FpX X p) :=
  fun s i => sgnV X p s * crd2 X p θ Q (PI.FinKW.vecV X.B.I p.1 (rowV X s)) i

theorem matR_mul_matC (s t : IdxD D) :
    (matR X p θ Q * matC X p θ Q) s t = sgnV X p s * (crd2 X p θ Q (PI.FinKW.vecV X.B.I p.1 (rowV X s)) ⬝ᵥ
      crd1 X p θ Q (PI.FinKW.vecV X.B.I p.1 (colV X t))) := by
  simp only [Matrix.mul_apply, matR, matC, dotProduct, Finset.mul_sum, mul_assoc]

private theorem isUnit_of_mul_eq_one_add_smul_maximalIdeal {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Type*} [CommRing A]
    [IsLocalRing A] (g : A) (hg : g ∈ IsLocalRing.maximalIdeal A) (R C Z : Matrix ι ι A)
    (h : R * C = 1 + g • Z) : IsUnit C := by
  have hm : (R * C).map (IsLocalRing.residue A) = 1 := by
    rw [h]
    ext i j
    have h0 : IsLocalRing.residue A g = 0 := (IsLocalRing.residue_eq_zero_iff g).mpr hg
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _), map_mul, h0,
      zero_mul, add_zero, Matrix.one_apply]
    split_ifs <;> simp
  have h1 : IsUnit (R * C).det := by
    apply IsUnit.of_map (IsLocalRing.residue A)
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hm, Matrix.det_one]
    exact isUnit_one
  rw [Matrix.det_mul] at h1
  exact (Matrix.isUnit_iff_isUnit_det C).mpr (isUnit_of_mul_isUnit_right h1)


set_option maxHeartbeats 800000 in
theorem adapt_of_eps (hθ : IsSplitEquiv X p θ) (hε : θ (epsP X p) = (1, 0)) (hL : LatBasis X p θ (reindex₂ X p Q)) :
    ∃ Q' : GL (IdxD D) (FpX X p), LatBasis X p θ (reindex₂ X p Q') ∧ AdaptA X p θ Q' := by
  classical
  have hgA : ((gA X p : OvA X p) : FpX X p) = ((gOf p : ℕ) : FpX X p) := map_natCast (OvA X p).subtype _
  have hT : Formalism.L2.SG.TypedSets.IsTyped X.B.I.F (D.host.g 0) (D.host.g 1) p.1 := by
    have h := p.2
    unfold Formalism.L2.SG.TypedSets.typSet at h
    split_ifs at h with hf
    · exact hf.mem_toFinset.mp h
    · simp at h
  unfold Formalism.L2.SG.TypedSets.IsTyped at hT
  have hmem : ((gOf p : ℕ) : 𝓞 X.B.I.F) ∈ p.1.asIdeal := by
    unfold Formalism.L2.SG.TypedSets.gOf
    split_ifs with h0
    · exact h0
    · exact hT.resolve_left h0
  have hlt : Valued.v ((gOf p : ℕ) : FpX X p) < 1 := by
    have h2 : ((gOf p : ℕ) : FpX X p) = (((gOf p : ℕ) : X.B.I.F) : FpX X p) := by
      first
        | exact (map_natCast (algebraMap X.B.I.F (FpX X p)) _).symm
        | exact (map_natCast (IsDedekindDomain.HeightOneSpectrum.coeRingHom p.1) _).symm
        | (norm_cast; done)
        | (simp; done)
    rw [h2, IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      ← map_natCast (algebraMap (𝓞 X.B.I.F) X.B.I.F),
      IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact hmem
  have hg : (gA X p : OvA X p) ∈ IsLocalRing.maximalIdeal (OvA X p) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, hu⟩
    have hv1 : Valued.v (((u⁻¹ : (OvA X p)ˣ) : OvA X p) : FpX X p) ≤ 1 := ((u⁻¹ : (OvA X p)ˣ) : OvA X p).2
    have hmul : ((gOf p : ℕ) : FpX X p) * (((u⁻¹ : (OvA X p)ˣ) : OvA X p) : FpX X p) = 1 := by
      rw [← hgA, ← hu]
      exact congrArg Subtype.val u.mul_inv
    have h3 := congrArg Valued.v hmul
    rw [map_mul, map_one] at h3
    have h4 := (mul_le_of_le_one_right' hv1).trans_lt hlt
    rw [h3] at h4
    exact lt_irrefl _ h4
  have hC : ∀ i t, matC X p θ Q i t ∈ OvA X p := fun i t =>
    ((latCrd_of (X := X) (p := p) (θ := θ) (Q := Q) hL _).mp (colV_lat X p t)).1 i
  have hR : ∀ s i, matR X p θ Q s i ∈ OvA X p := fun s i =>
    mul_mem (sgnV_int X p s) (((latCrd_of (X := X) (p := p) (θ := θ) (Q := Q) hL _).mp (rowV_lat X p s)).2 i)
  choose zf hz using fun s t => rc_cong (X := X) (p := p) (θ := θ) (Q := Q) hθ hε hL s t
  let Ci : Matrix (IdxD D) (IdxD D) (OvA X p) := fun i t => ⟨matC X p θ Q i t, hC i t⟩
  let Ri : Matrix (IdxD D) (IdxD D) (OvA X p) := fun s i => ⟨matR X p θ Q s i, hR s i⟩
  let Zi : Matrix (IdxD D) (IdxD D) (OvA X p) := fun s t => zf s t
  have eR : Ri.map (OvA X p).subtype = matR X p θ Q := by ext; rfl
  have eC : Ci.map (OvA X p).subtype = matC X p θ Q := by ext; rfl
  have hRC : Ri * Ci = 1 + (gA X p) • Zi := by
    apply Matrix.map_injective (f := (OvA X p).subtype) (fun a b hab => Subtype.ext hab)
    show (Ri * Ci).map (OvA X p).subtype = (1 + gA X p • Zi).map (OvA X p).subtype
    rw [Matrix.map_mul, eR, eC]
    have hgA' : (OvA X p).subtype (gA X p) = ((gOf p : ℕ) : FpX X p) := hgA
    refine Matrix.ext fun s t => ?_
    rw [(matR_mul_matC X p θ Q s t).trans (hz s t)]
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _), map_mul,
      Matrix.one_apply, hgA']
    split_ifs <;> simp [Zi]
  have hU : IsUnit Ci := isUnit_of_mul_eq_one_add_smul_maximalIdeal (gA X p) hg Ri Ci Zi hRC
  let c : GL (IdxD D) (OvA X p) := hU.unit
  have hcC : ((glK (OvA X p) c : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) =
      matC X p θ Q := eC
  have hcol : ∀ t, crd1 X p θ (Q * glK (OvA X p) c) (PI.FinKW.vecV X.B.I p.1 (colV X t)) = Pi.single t 1 := by
    intro t
    rw [firstCoords_mul_GL (X := X) (p := p) (θ := θ) (Q := Q)]
    have e : crd1 X p θ Q (PI.FinKW.vecV X.B.I p.1 (colV X t)) =
        ((glK (OvA X p) c : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) *ᵥ Pi.single t 1 := by
      rw [hcC]
      funext i
      simp [Matrix.mulVec, dotProduct, Pi.single_apply, matC]
    rw [e, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have hrow : ∀ s t, crd2 X p θ (Q * glK (OvA X p) c) (PI.FinKW.vecV X.B.I p.1 (rowV X s)) t =
      sgnV X p s * ((1 : Matrix (IdxD D) (IdxD D) (FpX X p)) s t + ((gOf p : ℕ) : FpX X p) * (zf s t : FpX X p)) := by
    intro s t
    rw [secondCoords_mul_GL (X := X) (p := p) (θ := θ) (Q := Q), hcC, ← hz s t, ← mul_assoc, sgnV_sq X p s, one_mul]
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, matC]
    apply Finset.sum_congr rfl
    intro i _
    ring
  refine ⟨Q * glK (OvA X p) c, latBasis_mulGL (X := X) (p := p) (θ := θ) (Q := Q) hL c, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    exact ⟨0, fun _ => zero_mem _, by rw [show X.e0 a = colV X (Sum.inl a) from rfl, hcol]; simp⟩
  · exact ⟨0, fun _ => zero_mem _, by
      rw [show X.z0 = colV X zI from rfl, hcol]; simp⟩
  · intro i
    exact ⟨0, fun _ => zero_mem _, by
      rw [show X.bw i = colV X (wI i) from rfl, hcol]; simp⟩
  · intro a
    have hs : X.e0 a = rowV X (Sum.inr (Sum.inr (Fin.rev a)) : IdxD D) := by simp [rowV]
    refine ⟨fun t => zf (Sum.inr (Sum.inr (Fin.rev a))) t, fun t => (zf _ t).2, ?_⟩
    funext t
    rw [hs, hrow]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hgA, Matrix.one_apply, Pi.single_apply, sgnV]
    by_cases h : (Sum.inr (Sum.inr (Fin.rev a)) : IdxD D) = t
    · subst h; simp
    · rw [if_neg h, if_neg (Ne.symm h)]; ring
  · have hs : X.z0 = rowV X zI := rfl
    refine ⟨fun t => -(zf zI t : FpX X p), fun t => neg_mem (zf zI t).2, ?_⟩
    funext t
    rw [hs, hrow]
    simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, hgA, Matrix.one_apply, Pi.single_apply]
    have : sgnV X p zI = -1 := rfl
    rw [this]
    by_cases h : zI = t
    · subst h; simp; ring
    · rw [if_neg h, if_neg (Ne.symm h)]; ring
  · intro i
    exact PIW.MassDataColumns.secondProj_weight_vector_zero (X := X) (p := p) (θ := θ) hε i

theorem adaptA_holds : ∃ θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p, IsSplitEquiv X p θ ∧
    ∃ Q : GL (IdxD D) (FpX X p), LatBasis X p θ (reindex₂ X p Q) ∧ AdaptA X p θ Q := by
  obtain ⟨θ, hθ, hε⟩ := exists_split_eps X p
  obtain ⟨Q, hQ⟩ := exists_GL_latBasis_of_isSplitEquiv X p θ hθ
  obtain ⟨Q', h1, h2⟩ := adapt_of_eps X p θ Q hθ hε hQ
  exact ⟨θ, hθ, Q', h1, h2⟩

end Loc

end MassDataIdxSteps
