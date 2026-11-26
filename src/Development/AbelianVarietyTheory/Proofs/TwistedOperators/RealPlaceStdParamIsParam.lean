module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyGrpData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyFockModelUnitaryDualPair
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplexConjugationMapsMultiplicitySpace
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIrreducibleTwist

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlaceStdParamIsParam
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyFockModelOfUnitaryPairCovers
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyFockModelOfUnitaryPairCovers
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

namespace GlobalTheory

theorem nonempty_fockData_of_covers :
    ∀ (p q r s : ℕ) (T0 : GrpData (p * r + q * s) (p * s + q * r)) (T1 : GrpData p q)
      (T2 : GrpData r s), Nonempty (FockData T0 T1 T2) :=
  GlobalTheory.T.nonempty_fockModel_unitary_dual_pair

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyFockModelOfUnitaryPairCoversStatement
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_fockModel_of_unitary_pair_covers : ∀ (p q r s : ℕ) (T0 : GrpData (p * r + q * s) (p * s + q * r)) (T1 : GrpData p q) (T2 : GrpData r s), Nonempty (FockData T0 T1 T2) := by
  first | exact @GlobalTheory.nonempty_fockData_of_covers | exact GlobalTheory.nonempty_fockData_of_covers | (intros; apply GlobalTheory.nonempty_fockData_of_covers <;> assumption)
end
end

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

namespace GlobalTheory

def realPlaceStdParam (p q : ℕ) : Ix p q → ℚ :=
  Sum.elim (fun i => -((i : ℕ) : ℚ)) (fun j => -(((p + j : ℕ)) : ℚ))

theorem realPlaceStdParam_int (p q : ℕ) (a : Ix p q) :
    ∃ k : ℤ, realPlaceStdParam p q a = k := by
  rcases a with i | j
  · exact ⟨-((i : ℕ) : ℤ), by simp [realPlaceStdParam]⟩
  · exact ⟨-((p + j : ℕ) : ℤ), by simp [realPlaceStdParam]⟩

theorem realPlaceStdParam_isParam (p q : ℕ) : IsParam (realPlaceStdParam p q) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro (i | j) (i' | j') h
    · simp only [realPlaceStdParam, Sum.elim_inl, neg_inj, Nat.cast_inj] at h
      exact congrArg Sum.inl (Fin.ext h)
    · simp only [realPlaceStdParam, Sum.elim_inl, Sum.elim_inr, neg_inj, Nat.cast_inj] at h
      have := i.2
      omega
    · simp only [realPlaceStdParam, Sum.elim_inl, Sum.elim_inr, neg_inj, Nat.cast_inj] at h
      have := i'.2
      omega
    · simp only [realPlaceStdParam, Sum.elim_inr, neg_inj, Nat.cast_inj] at h
      exact congrArg Sum.inr (Fin.ext (by omega))
  · rintro (i | j) (i' | j') h
    · have h' : (i : ℕ) < i' := h
      simp only [realPlaceStdParam, Sum.elim_inl, neg_lt_neg_iff, Nat.cast_lt]
      exact h'
    · exact absurd h (by simp [posC])
    · exact absurd h (by simp [posC])
    · have h' : (j : ℕ) < j' := h
      simp only [realPlaceStdParam, Sum.elim_inr, neg_lt_neg_iff, Nat.cast_lt]
      omega
  · intro a
    obtain ⟨k, hk⟩ := realPlaceStdParam_int p q a
    exact ⟨2 * k, by rw [hk]; push_cast; ring⟩
  · intro a b
    obtain ⟨k, hk⟩ := realPlaceStdParam_int p q a
    obtain ⟨l, hl⟩ := realPlaceStdParam_int p q b
    exact ⟨k - l, by rw [hk, hl]; push_cast; ring⟩

theorem exists_provA_of_forall_exists_hasParam :
    (∀ (p q : ℕ) (T : GrpData p q) (lam : Ix p q → ℚ), IsParam lam →
      ∃ R : DSRep T, Formalism.L2.Theta.HasParam R lam) →
    ∃ X : ProvA, ∀ (p q : ℕ) (lam : Ix p q → ℚ), IsParam lam →
      Formalism.L2.Theta.HasParam (X.ds p q lam) lam := by
  intro H
  classical
  let grp : ∀ p q : ℕ, GrpData p q := fun p q => Classical.choice (GlobalTheory.DetSqrtCover.nonempty_grpData p q)
  have key : ∀ (p q : ℕ) (lam : Ix p q → ℚ), ∃ R : DSRep (grp p q),
      IsParam lam → Formalism.L2.Theta.HasParam R lam := by
    intro p q lam
    by_cases h : IsParam lam
    · obtain ⟨R, hR⟩ := H p q (grp p q) lam h
      exact ⟨R, fun _ => hR⟩
    · obtain ⟨R, -⟩ := H p q (grp p q) _ (realPlaceStdParam_isParam p q)
      exact ⟨R, fun h' => absurd h' h⟩
  choose ds hds using key
  exact ⟨⟨grp, fun p q r s => Classical.choice (GlobalTheory.T.nonempty_fockModel_of_unitary_pair_covers p q r s _ _ _), ds⟩, hds⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelativeJacquetFunctorPiTensorEquiv
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelativeJacquetFunctorPiTensorEquiv
open GlobalTheory.PRep GlobalTheory.SmGL
open GlobalTheory.JacPiTensor (qlift mk_qlift descend descend_mk)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.RelJacTensor

section Spec

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [LinearOrder β]
  {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  {c : α → β → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)]
  (e' : ∀ i, (Σ j, c i j) ≃ m i) {X : α → Type} [∀ a, AddCommGroup (X a)]
  [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (m a) k) (X a))

theorem piTensor_mulSingle (a : α) (g : GL (m a) k) (x : ∀ j, X j) :
    piTensor ρ (Pi.mulSingle a g) (PiTensorProduct.tprod ℂ x) =
      PiTensorProduct.tprod ℂ (Function.update x a (ρ a g (x a))) := by
  rw [piTensor_tprod]
  congr 1
  funext j
  by_cases h : j = a
  · subst h
    simp
  · simp [h]

def qf : (∀ a, X a) →ₘₗ[ℂ] Jacquet (piTensor ρ) (relUnip k e') :=
  (twKer (piTensor ρ) (relUnip k e') 1).mkQ.compMultilinearMap (PiTensorProduct.tprod ℂ)

theorem qf_update (v : ∀ a, X a) (i : α) (w : X i)
    (hw : w ∈ twKer (ρ i) (unipRad k (e' i)) 1) : qf e' ρ (Function.update v i w) = 0 := by
  unfold twKer at hw
  induction hw using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨n, y, rfl⟩ := hz
    have hu : (Pi.mulSingle (M := fun a => GL (m a) k) i (n : GL (m i) k)) ∈ relUnip k e' := by
      simp only [relUnip, Subgroup.mem_pi]
      intro j _
      by_cases h : j = i
      · subst h
        simpa using n.2
      · rw [Pi.mulSingle_eq_of_ne h]
        exact one_mem _
    have h1 : PiTensorProduct.tprod ℂ (Function.update v i (ρ i (n : GL (m i) k) y)) =
        piTensor ρ (Pi.mulSingle (M := fun a => GL (m a) k) i (n : GL (m i) k))
          (PiTensorProduct.tprod ℂ (Function.update v i y)) := by
      rw [piTensor_mulSingle]
      simp
    rw [qf, LinearMap.compMultilinearMap_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      MonoidHom.one_apply, Units.val_one, one_smul, MultilinearMap.map_update_sub, h1]
    exact Submodule.subset_span ⟨⟨_, hu⟩, PiTensorProduct.tprod ℂ (Function.update v i y), by simp⟩
  | zero => simp [qf]
  | add z z' _ _ hz hz' => rw [MultilinearMap.map_update_add, hz, hz', add_zero]
  | smul r z _ hz => rw [MultilinearMap.map_update_smul, hz, smul_zero]

end Spec

section Spec2

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [LinearOrder β]
  {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  {c : α → β → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)]
  (e' : ∀ i, (Σ j, c i j) ≃ m i) {X : α → Type} [∀ a, AddCommGroup (X a)]
  [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (m a) k) (X a))

def qmap : (⨂[ℂ] a, X a) →ₗ[ℂ] ⨂[ℂ] a, Jacquet (ρ a) (unipRad k (e' a)) :=
  PiTensorProduct.map fun a => (twKer (ρ a) (unipRad k (e' a)) 1).mkQ

theorem qmap_tprod (x : ∀ a, X a) :
    qmap e' ρ (PiTensorProduct.tprod ℂ x) =
      PiTensorProduct.tprod ℂ fun a => (Submodule.Quotient.mk (x a) : Jacquet (ρ a) (unipRad k (e' a))) := by
  simp only [qmap, PiTensorProduct.map_tprod, Submodule.mkQ_apply]

theorem qmap_comp (u : ∀ a, GL (m a) k) (hu : u ∈ relUnip k e') :
    qmap e' ρ ∘ₗ piTensor ρ u = qmap e' ρ := by
  have hu' : ∀ a, u a ∈ unipRad k (e' a) := by
    intro a
    have h := hu
    simp only [relUnip, Subgroup.mem_pi] at h
    exact h a (Set.mem_univ a)
  refine PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, piTensor_tprod, qmap_tprod]
  congr 1
  funext a
  rw [Submodule.Quotient.eq]
  exact Submodule.subset_span ⟨⟨u a, hu' a⟩, x a, by simp⟩

theorem twKer_le_ker : twKer (piTensor ρ) (relUnip k e') 1 ≤ LinearMap.ker (qmap e' ρ) := by
  rw [twKer, Submodule.span_le]
  rintro _ ⟨n, y, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, MonoidHom.one_apply, Units.val_one, one_smul, map_sub,
    sub_eq_zero]
  exact LinearMap.congr_fun (qmap_comp e' ρ (n : ∀ a, GL (m a) k) n.2) y

def fwd : Jacquet (piTensor ρ) (relUnip k e') →ₗ[ℂ] ⨂[ℂ] a, Jacquet (ρ a) (unipRad k (e' a)) :=
  (twKer (piTensor ρ) (relUnip k e') 1).liftQ (qmap e' ρ) (twKer_le_ker e' ρ)

def bwd : (⨂[ℂ] a, Jacquet (ρ a) (unipRad k (e' a))) →ₗ[ℂ] Jacquet (piTensor ρ) (relUnip k e') :=
  PiTensorProduct.lift (descend (qf e' ρ) (qf_update e' ρ))

theorem bwd_tprod (q : ∀ a, Jacquet (ρ a) (unipRad k (e' a))) :
    bwd e' ρ (PiTensorProduct.tprod ℂ q) = Submodule.Quotient.mk (PiTensorProduct.tprod ℂ
      fun i => qlift (fun a => twKer (ρ a) (unipRad k (e' a)) 1) i (q i)) := by
  rw [bwd, PiTensorProduct.lift.tprod]
  rfl

theorem bwd_tprod_mk (x : ∀ a, X a) :
    bwd e' ρ (PiTensorProduct.tprod ℂ fun a => (Submodule.Quotient.mk (x a) : Jacquet (ρ a) (unipRad k (e' a)))) =
      Submodule.Quotient.mk (PiTensorProduct.tprod ℂ x) := by
  rw [bwd, PiTensorProduct.lift.tprod, descend_mk]
  rfl

theorem fwd_mk_tprod' (x : ∀ a, X a) :
    fwd e' ρ (Submodule.Quotient.mk (PiTensorProduct.tprod ℂ x)) =
      PiTensorProduct.tprod ℂ fun a => (Submodule.Quotient.mk (x a) : Jacquet (ρ a) (unipRad k (e' a))) := by
  rw [fwd, Submodule.liftQ_apply, qmap_tprod]

def jacEquiv : Jacquet (piTensor ρ) (relUnip k e') ≃ₗ[ℂ] ⨂[ℂ] a, Jacquet (ρ a) (unipRad k (e' a)) :=
  LinearEquiv.ofLinear (fwd e' ρ) (bwd e' ρ)
    (by
      refine PiTensorProduct.ext (MultilinearMap.ext fun q => ?_)
      rw [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, bwd_tprod, fwd_mk_tprod']
      simp only [mk_qlift, LinearMap.compMultilinearMap_apply, LinearMap.id_apply])
    (by
      refine Submodule.linearMap_qext _ (PiTensorProduct.ext (MultilinearMap.ext fun x => ?_))
      rw [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearMap.comp_apply, Submodule.mkQ_apply,
        fwd_mk_tprod', bwd_tprod_mk, LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearMap.id_apply,
        Submodule.mkQ_apply])

theorem relJac_piTensor :
    Nonempty ((relJac e' (piTensor ρ)).Equiv (piTensor fun a => GlobalTheory.SmGL.jac (e' a) (ρ a))) := by
  refine ⟨Representation.Equiv.mk (jacEquiv e' ρ) fun g => ?_⟩
  refine Submodule.linearMap_qext _ (PiTensorProduct.ext (MultilinearMap.ext fun x => ?_))
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, Submodule.mkQ_apply,
    LinearEquiv.coe_coe, jacEquiv, LinearEquiv.ofLinear_apply, relJac_mk, piTensor_tprod, relEmb_apply,
    map_smul, fwd_mk_tprod', jac_mk, MultilinearMap.map_smul_univ, RingHom.id_apply, relDeltaHalf_apply]
  congr 1
  rw [← Finset.prod_inv_distrib, Units.coe_prod]

end Spec2

theorem relJac_piTensor_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (α β : Type) [Fintype α] [Fintype β] [LinearOrder β]
    (m : α → Type) [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
    (c : α → β → Type) [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)]
    (f : ∀ i, (Σ j, c i j) ≃ m i) (X : α → Type) [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]
    (ρ : ∀ i, Representation ℂ (GL (m i) k) (X i)),
    Nonempty ((relJac f (piTensor ρ)).Equiv (piTensor fun i => GlobalTheory.SmGL.jac (f i) (ρ i))) := by
  intro k _ _ _ _ α β _ _ _ m _ _ c _ _ f X _ _ ρ
  classical
  exact relJac_piTensor f ρ

end GlobalTheory.RelJacTensor
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelativeJacquetFunctorPiTensorEquivStatement
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relative_jacquet_functor_piTensor_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α β : Type) [Fintype α] [Fintype β] [LinearOrder β] (m : α → Type) [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (c : α → β → Type) [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)] (f : ∀ i, (Σ j, c i j) ≃ m i) (X : α → Type) [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)] (ρ : ∀ i, Representation ℂ (GL (m i) k) (X i)), Nonempty ((GlobalTheory.SmGL.relJac f (GlobalTheory.SmGL.piTensor ρ)).Equiv (GlobalTheory.SmGL.piTensor fun i => GlobalTheory.SmGL.jac (f i) (ρ i))) := by
  first | exact @GlobalTheory.RelJacTensor.relJac_piTensor_equiv | exact GlobalTheory.RelJacTensor.relJac_piTensor_equiv | (intros; apply GlobalTheory.RelJacTensor.relJac_piTensor_equiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharIsUnitaryOfUnitaryInfinityType
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharIsUnitaryOfUnitaryInfinityType
noncomputable section

open GlobalTheory.Mem.Chr hiding infDiag Ideles
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host

namespace GlobalTheory.HeckeUnitaryInf

theorem isUnitary_of_hasInf : ∀ (L : Type) [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L) {I : Type} [Fintype I]
    (φ : I → L →+* ℂ) (n : I → ℤ), χ.HasInf φ n → χ.IsUnitary := by
  intro L _ _ χ I _ φ n h
  have hinf : ∀ k : Lˣ, ‖((χ.1 (infDiag k) : ℂˣ) : ℂ)‖ = 1 := by
    intro k
    have e : ((χ.1 (infDiag k) : ℂˣ) : ℂ) = _ := h k
    rw [e, norm_prod]
    refine Finset.prod_eq_one fun i _ => ?_
    have h0 : φ i (k : L) ≠ 0 := (map_ne_zero _).2 k.ne_zero
    rw [norm_zpow, norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 h0), one_zpow]
  have hI : ∀ y : (InfiniteAdeleRing L)ˣ, ‖((χ.1 (GlobalTheory.HeckeGal.inlInf L y) : ℂˣ) : ℂ)‖ = 1 := by
    have := (GlobalTheory.HeckeGal.denseRange_units_inf L).equalizer
      (g := fun y => ‖((χ.1 (GlobalTheory.HeckeGal.inlInf L y) : ℂˣ) : ℂ)‖) (h := fun _ => (1 : ℝ))
      ((Units.continuous_val.comp (χ.2.1.comp GlobalTheory.HeckeGal.continuous_inlInf)).norm) continuous_const
      (funext fun k => by
        simp only [Function.comp_apply]
        rw [← GlobalTheory.HeckeGal.infDiag_eq]
        exact hinf k)
    exact fun y => congrFun this y
  have hF : ∀ x : Ideles L, IsFinIdele x → ‖((χ.1 x : ℂˣ) : ℂ)‖ = 1 := by
    intro x hx
    obtain ⟨m, hm, u, k, u1, u2, e⟩ := GlobalTheory.UnUnitCmp.Val.exists_pow_eq x hx
    have e1 := congrArg (fun a => ‖((χ.1 a : ℂˣ) : ℂ)‖) e
    simp only [map_mul, map_pow, Units.val_mul, Units.val_pow_eq_pow_val, norm_mul, norm_pow, hinf k,
      GlobalTheory.HeckeFin.norm_eq_one χ u u1 u2, χ.2.2 k, Units.val_one, norm_one, mul_one] at e1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 e1
  intro z
  have hz : z = GlobalTheory.HeckeGal.inlInf L (Units.map (MonoidHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)) z) *
      finPartI L z := Units.ext (Prod.ext (mul_one _).symm (one_mul _).symm)
  rw [hz, map_mul, Units.val_mul, norm_mul, hI, hF _ (fun _ => rfl), one_mul]

end GlobalTheory.HeckeUnitaryInf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharIsUnitaryOfUnitaryInfinityTypeStatement
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_isUnitary_of_unitary_infinityType : ∀ (L : Type) [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L) {I : Type} [Fintype I] (φ : I → L →+* ℂ) (n : I → ℤ), χ.HasInf φ n → χ.IsUnitary := by
  first | exact @GlobalTheory.HeckeUnitaryInf.isUnitary_of_hasInf | exact GlobalTheory.HeckeUnitaryInf.isUnitary_of_hasInf | (intros; apply GlobalTheory.HeckeUnitaryInf.isUnitary_of_hasInf <;> assumption)
end
end
