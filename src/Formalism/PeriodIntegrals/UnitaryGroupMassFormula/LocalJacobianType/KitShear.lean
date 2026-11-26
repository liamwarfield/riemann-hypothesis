module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.ContinuousTrESymm
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDualGenerator.FpDualUnram
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SplitIntLoc
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.BoxMul

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.KitSplit
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.RingTopologyInstances
noncomputable section

namespace PI.UnitaryGroupMassFormula.LocJacTyp

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacTyp
open scoped TensorProduct

attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv
attribute [local instance] Sd.finDim

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem oev_one : (1 : Fv F v ⊗[F] E) ∈ OEv (E := E) v := by
  unfold OEv
  rw [SetLike.mem_coe]
  apply Submodule.subset_span
  refine ⟨1, Set.mem_univ _, ?_⟩
  first
    | exact map_one _
    | simp

theorem sc_mul (t : Fv F v) (x : Fv F v ⊗[F] E) : sc (E := E) v t * x = t • x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sc, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.smul_tmul']
  | add x y hx hy => rw [mul_add, smul_add, hx, hy]

theorem oev_mul {x y : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) (hy : y ∈ OEv (E := E) v) :
    x * y ∈ OEv (E := E) v := by
  unfold OEv at hx hy ⊢
  rw [SetLike.mem_coe] at hx hy ⊢
  induction hx using Submodule.span_induction with
  | mem a ha =>
    induction hy using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨a', -, rfl⟩ := ha
      obtain ⟨b', -, rfl⟩ := hb
      apply Submodule.subset_span
      refine ⟨a' * b', Set.mem_univ _, ?_⟩
      first
        | exact map_mul _ _ _
        | simp
    | zero => simp
    | add y z _ _ hy hz =>
      rw [mul_add]
      exact Submodule.add_mem _ hy hz
    | smul c y _ hy =>
      first
        | rw [mul_smul_comm]
        | rw [← algebraMap_smul (Fv F v) c y, mul_smul_comm, algebraMap_smul]
      exact Submodule.smul_mem _ c hy
  | zero => simp
  | add x z _ _ hx hz =>
    rw [add_mul]
    exact Submodule.add_mem _ hx hz
  | smul c x _ hx =>
    first
      | rw [smul_mul_assoc]
      | rw [← algebraMap_smul (Fv F v) c x, smul_mul_assoc, algebraMap_smul]
    exact Submodule.smul_mem _ c hx

theorem sigR_smul (σ : E →ₐ[F] E) (c : Fv F v) (x : Fv F v ⊗[F] E) :
    sigR (Fv F v) σ (c • x) = c • sigR (Fv F v) σ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sigR, TensorProduct.smul_tmul']
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]

private theorem sigR_smulO_lemma (σ : E →ₐ[F] E) (c : v.adicCompletionIntegers F)
    (x : Fv F v ⊗[F] E) : sigR (Fv F v) σ (c • x) = c • sigR (Fv F v) σ x := by
  first
    | rw [← algebraMap_smul (Fv F v) c x, sigR_smul, algebraMap_smul]
    | (induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul a b => simp [sigR, TensorProduct.smul_tmul']
        | add y z hy hz => simp only [smul_add, map_add (f := _), hy, hz])

theorem oev_sigR (σ : E →ₐ[F] E) {x : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) :
    sigR (Fv F v) σ x ∈ OEv (E := E) v := by
  unfold OEv at hx ⊢
  rw [SetLike.mem_coe] at hx ⊢
  induction hx using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨a', -, rfl⟩ := ha
    apply Submodule.subset_span
    first
      | exact ⟨NumberField.RingOfIntegers.mapRingHom (σ : E →+* E) a', Set.mem_univ _,
          by simp [sigR, inclR]⟩
      | exact ⟨⟨σ a', (a'.isIntegral_coe.map (σ : E →+* E).toIntAlgHom)⟩, Set.mem_univ _,
          by simp [sigR, inclR]⟩
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add (f := _)]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [sigR_smulO_lemma]
    exact Submodule.smul_mem _ c hx

theorem integer_ring_topology : OTop (E := E) v :=
  ⟨Sd.isCompact_oev v, Sd.isOpen_oev v, oev_one v, fun _ hx _ hy => oev_mul v hx hy,
    fun _ hx _ hy => Sd.oev_add v hx hy, fun _ hx => Sd.oev_neg v hx,
    fun t ht x hx => by rw [sc_mul]; exact Sd.oev_smul v ht hx,
    fun σ _ hx => oev_sigR v σ hx⟩

end PI.UnitaryGroupMassFormula.LocJacTyp
end
end

noncomputable section

namespace PI.UnitaryGroupMassFormula.LocJacTyp

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacTyp
open scoped TensorProduct

attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv
attribute [local instance] Sd.finDim

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))

structure SD where
  e : Fv F v ⊗[F] E
  he : IsIdempotentElem e
  h0 : e ≠ 0
  h1 : e ≠ 1
  hr : Module.finrank (Fv F v) (Fv F v ⊗[F] E) = 2
  hσ : sigR (Fv F v) σ e = 1 - e

namespace SD

variable {σ v} (D : SD σ v)

def p (i : Fin 2) : (Fv F v ⊗[F] E) →ₐ[Fv F v] Fv F v := PI.LocDualGen.EpS.pr D.hr D.e D.he D.h0 D.h1 i

theorem decomp (z : Fv F v ⊗[F] E) : z = D.p 0 z • D.e + D.p 1 z • (1 - D.e) :=
  PI.LocDualGen.EpS.decomp D.hr D.e D.he D.h0 D.h1 z

theorem p_pair (s t : Fv F v) : D.p 0 (s • D.e + t • (1 - D.e)) = s ∧ D.p 1 (s • D.e + t • (1 - D.e)) = t :=
  PI.LocDualGen.EpS.repr_pair D.hr D.e D.he D.h0 D.h1 s t

theorem ext {z w : Fv F v ⊗[F] E} (h0 : D.p 0 z = D.p 0 w) (h1 : D.p 1 z = D.p 1 w) : z = w := by
  rw [D.decomp z, D.decomp w, h0, h1]

theorem p_e : D.p 0 D.e = 1 ∧ D.p 1 D.e = 0 := PI.LocDualGen.EpS.pr_e D.hr D.e D.he D.h0 D.h1

theorem p_f : D.p 0 (1 - D.e) = 0 ∧ D.p 1 (1 - D.e) = 1 := PI.LocDualGen.EpS.pr_f D.hr D.e D.he D.h0 D.h1

theorem p_sc (i : Fin 2) (t : Fv F v) : D.p i (sc (E := E) v t) = t := by
  have : sc (E := E) v t = algebraMap (Fv F v) (Fv F v ⊗[F] E) t := rfl
  rw [this, AlgHom.commutes]; rfl

theorem p_sig (z : Fv F v ⊗[F] E) :
    D.p 0 (sigR (Fv F v) σ z) = D.p 1 z ∧ D.p 1 (sigR (Fv F v) σ z) = D.p 0 z := by
  have h : sigR (Fv F v) σ z = D.p 1 z • D.e + D.p 0 z • (1 - D.e) := by
    conv_lhs => rw [D.decomp z]
    rw [map_add (f := _), sigR_smul, sigR_smul, map_sub, map_one, D.hσ, sub_sub_cancel, add_comm]
  rw [h]
  exact D.p_pair _ _

theorem norm_eq (z : Fv F v ⊗[F] E) : Algebra.norm (Fv F v) z = D.p 0 z * D.p 1 z := by
  rw [Algebra.norm_eq_matrix_det (PI.LocDualGen.EpS.bas D.hr D.e D.he D.h0 D.h1) z, Matrix.det_fin_two,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
    PI.LocDualGen.EpS.bas0, PI.LocDualGen.EpS.bas1]
  have h0 := congrArg (fun w => (PI.LocDualGen.EpS.bas D.hr D.e D.he D.h0 D.h1).repr w 0) (PI.LocDualGen.EpS.mul_decomp D.hr D.e D.he D.h0 D.h1 z D.e)
  have h1 := congrArg (fun w => (PI.LocDualGen.EpS.bas D.hr D.e D.he D.h0 D.h1).repr w 1) (PI.LocDualGen.EpS.mul_decomp D.hr D.e D.he D.h0 D.h1 z D.e)
  have h2 := congrArg (fun w => (PI.LocDualGen.EpS.bas D.hr D.e D.he D.h0 D.h1).repr w 0)
    (PI.LocDualGen.EpS.mul_decomp D.hr D.e D.he D.h0 D.h1 z (1 - D.e))
  have h3 := congrArg (fun w => (PI.LocDualGen.EpS.bas D.hr D.e D.he D.h0 D.h1).repr w 1)
    (PI.LocDualGen.EpS.mul_decomp D.hr D.e D.he D.h0 D.h1 z (1 - D.e))
  rw [h0, h1, h2, h3]
  simp only [(PI.LocDualGen.EpS.repr_pair D.hr D.e D.he D.h0 D.h1 _ _).1,
    (PI.LocDualGen.EpS.repr_pair D.hr D.e D.he D.h0 D.h1 _ _).2]
  have pe := D.p_e
  have pf := D.p_f
  simp only [p, PI.LocDualGen.EpS.pr_apply] at pe pf
  rw [pe.1, pe.2, pf.1, pf.2]
  simp only [p, PI.LocDualGen.EpS.pr_apply]
  ring

end SD

def oevSub : Subring (Fv F v ⊗[F] E) where
  carrier := OEv (E := E) v
  mul_mem' := fun hx hy => oev_mul v hx hy
  one_mem' := oev_one v
  add_mem' := fun hx hy => Sd.oev_add v hx hy
  zero_mem' := Sd.oev_zero v
  neg_mem' := fun hx => Sd.oev_neg v hx

theorem tens_iff (x : Fv F v ⊗[F] E) :
    (Algebra.TensorProduct.comm F E (Fv F v)).symm x ∈
        PI.SplitIntLoc.tensInt (F := F) (Fv F v) (PI.SplitIntLoc.intOE E)
          (v.adicCompletionIntegers F).toSubring ↔ x ∈ OEv (E := E) v := by
  constructor
  · intro h
    have hle : PI.SplitIntLoc.tensInt (F := F) (Fv F v) (PI.SplitIntLoc.intOE E)
        (v.adicCompletionIntegers F).toSubring ≤
        (oevSub v).comap (Algebra.TensorProduct.comm F E (Fv F v)).toRingEquiv.toRingHom := by
      apply Subring.closure_le.2
      rintro y (⟨⟨a, ha⟩, rfl⟩ | ⟨⟨t, ht⟩, rfl⟩)
      · obtain ⟨b, rfl⟩ := ha
        show Algebra.TensorProduct.comm F E (Fv F v) (((algebraMap (𝓞 E) E) b) ⊗ₜ[F] (1 : Fv F v)) ∈
          OEv (E := E) v
        simp only [Algebra.TensorProduct.comm_tmul]
        exact Sd.inclR_mem (F := F) v b
      · show Algebra.TensorProduct.comm F E (Fv F v) ((1 : E) ⊗ₜ[F] t) ∈ OEv (E := E) v
        have h1 : Algebra.TensorProduct.comm F E (Fv F v) ((1 : E) ⊗ₜ[F] t) = t • (1 : Fv F v ⊗[F] E) := by
          simp [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul']
        rw [h1]
        exact Sd.oev_smul v ht (oev_one v)
    have h2 := Subring.mem_comap.1 (hle h)
    have h3 : (Algebra.TensorProduct.comm F E (Fv F v)).toRingEquiv.toRingHom
        ((Algebra.TensorProduct.comm F E (Fv F v)).symm x) = x := by simp
    rw [h3] at h2
    exact h2
  · intro hx
    change x ∈ Submodule.span _ _ at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, -, rfl⟩ := hy
      apply Subring.subset_closure
      left
      exact ⟨⟨(a : E), ⟨a, rfl⟩⟩, by simp [inclR]⟩
    | zero => simpa using zero_mem _
    | add y z _ _ hy hz => simpa only [map_add] using add_mem hy hz
    | smul t y _ hy =>
      have h1 : t • y = ((t : Fv F v) ⊗ₜ[F] (1 : E)) * y := by
        rw [show t • y = (t : Fv F v) • y from rfl, Algebra.smul_def]
        rfl
      rw [h1, map_mul]
      refine mul_mem ?_ hy
      apply Subring.subset_closure
      right
      exact ⟨⟨t, t.2⟩, by simp⟩

variable {σ v}

namespace SD

variable (D : SD σ v)

theorem mem_iff (x : Fv F v ⊗[F] E) :
    x ∈ OEv (E := E) v ↔ D.p 0 x ∈ v.adicCompletionIntegers F ∧ D.p 1 x ∈ v.adicCompletionIntegers F := by
  let f : (Fv F v ⊗[F] E) →ₐ[Fv F v] Fv F v × Fv F v := (D.p 0).prod (D.p 1)
  have hinj : Function.Injective f := fun z w h => D.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
  have hsurj : Function.Surjective f := fun ab =>
    ⟨ab.1 • D.e + ab.2 • (1 - D.e), Prod.ext (D.p_pair _ _).1 (D.p_pair _ _).2⟩
  let spl : E ⊗[F] Fv F v ≃+* Fv F v × Fv F v :=
    (Algebra.TensorProduct.comm F E (Fv F v)).toRingEquiv.trans (RingEquiv.ofBijective f ⟨hinj, hsurj⟩)
  have hspl : ∀ a : Fv F v, spl ((1 : E) ⊗ₜ[F] a) = (a, a) := by
    intro a
    have h1 : spl ((1 : E) ⊗ₜ[F] a) = f (Algebra.TensorProduct.comm F E (Fv F v) ((1 : E) ⊗ₜ[F] a)) := rfl
    rw [h1, Algebra.TensorProduct.comm_tmul,
      show (a ⊗ₜ[F] (1 : E) : Fv F v ⊗[F] E) = algebraMap (Fv F v) (Fv F v ⊗[F] E) a from rfl,
      AlgHom.commutes]
    rfl
  have key := split_integral_local F E v spl hspl ((Algebra.TensorProduct.comm F E (Fv F v)).symm x)
  have hx : spl ((Algebra.TensorProduct.comm F E (Fv F v)).symm x) = f x := by
    show f (Algebra.TensorProduct.comm F E (Fv F v) ((Algebra.TensorProduct.comm F E (Fv F v)).symm x)) = f x
    rw [AlgEquiv.apply_symm_apply]
  rw [hx, tens_iff] at key
  exact key

end SD

theorem sigR_eq_congr (hfin : Module.finrank F E = 2) :
    ∃ τ : E ≃ₐ[F] E, ∀ z, sigR (Fv F v) σ z =
      Algebra.TensorProduct.congr (AlgEquiv.refl : Fv F v ≃ₐ[F] Fv F v) τ z := by
  have : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  refine ⟨AlgEquiv.ofBijective σ (AlgHom.bijective σ), fun z => rfl⟩

theorem exists_SD (hS : SplitHyp σ v) : Nonempty (SD σ v) := by
  obtain ⟨hfin, hσ, e, hee, he0, he1⟩ := hS
  have hr : Module.finrank (Fv F v) (Fv F v ⊗[F] E) = 2 := by
    rw [Module.finrank_baseChange]; exact hfin
  have he : IsIdempotentElem e := hee
  let P := PI.LocDualGen.EpS.pr hr e he he0 he1
  have dec := PI.LocDualGen.EpS.decomp hr e he he0 he1
  have pair := PI.LocDualGen.EpS.repr_pair hr e he he0 he1
  obtain ⟨τ, hτ⟩ := sigR_eq_congr (σ := σ) (v := v) hfin
  have hinj : Function.Injective (sigR (Fv F v) σ) := by
    intro z w h
    rw [hτ, hτ] at h
    exact (Algebra.TensorProduct.congr (AlgEquiv.refl : Fv F v ≃ₐ[F] Fv F v) τ).injective h
  set f := sigR (Fv F v) σ e with hfdef
  have hfi : f * f = f := by rw [hfdef, ← map_mul, hee]
  have h01 : ∀ i, P i f = 0 ∨ P i f = 1 := by
    intro i
    have : P i f * P i f = P i f := by rw [← map_mul, hfi]
    have h2 : P i f * (P i f - 1) = 0 := by rw [mul_sub, this, mul_one, sub_self]
    rcases mul_eq_zero.1 h2 with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.1 h)
  have hfdec : f = P 0 f • e + P 1 f • (1 - e) := dec f
  refine ⟨⟨e, he, he0, he1, hr, ?_⟩⟩
  rcases h01 0 with a0 | a1 <;> rcases h01 1 with b0 | b1
  · exfalso
    apply he0
    apply hinj
    rw [map_zero, ← hfdef, hfdec, a0, b0]; simp
  · rw [← hfdef, hfdec, a0, b1]; simp
  · exfalso
    apply hσ
    have hfe : f = e := by rw [hfdec, a1, b0]; simp
    have hfix : ∀ z, sigR (Fv F v) σ z = z := by
      intro z
      conv_lhs => rw [dec z]
      rw [map_add, sigR_smul, sigR_smul, (sigR (Fv F v) σ).map_sub,
        (sigR (Fv F v) σ).map_one, ← hfdef, hfe, ← dec z]
    ext x
    have h1 := hfix ((1 : Fv F v) ⊗ₜ[F] x)
    have h2 : sigR (Fv F v) σ ((1 : Fv F v) ⊗ₜ[F] x) = (1 : Fv F v) ⊗ₜ[F] (σ x) := by
      simp [sigR]
    rw [h2] at h1
    exact Algebra.TensorProduct.includeRight_injective (algebraMap F (Fv F v)).injective h1
  · exfalso
    apply he1
    apply hinj
    rw [map_one, ← hfdef, hfdec, a1, b1]; simp

end PI.UnitaryGroupMassFormula.LocJacTyp
end
end

noncomputable section

namespace PI.UnitaryGroupMassFormula.LocJacTyp

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacTyp
open scoped TensorProduct

attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv
attribute [local instance] Sd.finDim

section Gen

variable {W : Type} [AddCommGroup W] [TopologicalSpace W] [IsTopologicalAddGroup W]
  [LocallyCompactSpace W] [SecondCountableTopology W] [T2Space W] [MeasurableSpace W] [BorelSpace W]

theorem haar_shear (μ : Measure W) [μ.IsAddHaarMeasure] (Φ : W ≃ₜ+ W) (K : Set W)
    (hK : IsCompact K) (hKo : IsOpen K) (hK0 : K.Nonempty) (hΦ : Φ ⁻¹' K = K) (S : Set W) :
    μ (Φ ⁻¹' S) = μ S := by
  have hmap : ∀ T, (μ.map Φ) T = μ (Φ ⁻¹' T) := fun T =>
    (Φ.toHomeomorph.toMeasurableEquiv).map_apply (μ := μ) T
  have e := Measure.isAddLeftInvariant_eq_smul (μ.map Φ) μ
  have hpos : μ K ≠ 0 := hKo.measure_ne_zero μ hK0
  have hfin : μ K ≠ ⊤ := hK.measure_lt_top.ne
  have h1 := congrArg (fun ν : Measure W => ν K) e
  simp only [hmap, hΦ, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h1
  have hc : ((Measure.addHaarScalarFactor (μ.map Φ) μ : NNReal) : ENNReal) = 1 := by
    have h2 : (1 : ENNReal) * μ K = (Measure.addHaarScalarFactor (μ.map Φ) μ : ENNReal) * μ K := by
      rw [one_mul]; exact h1
    exact ((ENNReal.mul_left_inj hpos hfin).1 h2).symm
  rw [← hmap, e, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, hc, one_mul]

end Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {v : HeightOneSpectrum (𝓞 F)}

theorem continuous_sigR' (σ : E →ₐ[F] E) : Continuous (sigR (Fv F v) σ) := by
  have : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  have h : ∀ x : Fv F v ⊗[F] E, sigR (Fv F v) σ x = (σ.toLinearMap.baseChange (Fv F v)) x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r e => simp [sigR]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have : (sigR (Fv F v) σ : Fv F v ⊗[F] E → Fv F v ⊗[F] E) = (σ.toLinearMap.baseChange (Fv F v)) :=
    funext h
  rw [this]
  exact IsModuleTopology.continuous_of_linearMap _

namespace SD

variable (D : SD σ v)

theorem e_mul_f : D.e * (1 - D.e) = 0 := by
  rw [mul_sub, mul_one, D.he.eq, sub_self]

def shear {ι : Type} (τ : ι → ι) : (ι → Fv F v ⊗[F] E) ≃ₜ+ (ι → Fv F v ⊗[F] E) where
  toFun z k := z k + D.e * sigR (Fv F v) σ (z (τ k))
  invFun w k := w k - D.e * sigR (Fv F v) σ (w (τ k))
  left_inv z := by
    funext k
    simp only [map_add (f := _), map_mul, D.hσ]
    linear_combination (-(sigR (Fv F v) σ (sigR (Fv F v) σ (z (τ (τ k)))))) * D.e_mul_f
  right_inv w := by
    funext k
    simp only [map_sub, map_mul, D.hσ]
    linear_combination (-(sigR (Fv F v) σ (sigR (Fv F v) σ (w (τ (τ k)))))) * D.e_mul_f
  map_add' x y := by
    funext k
    simp only [Pi.add_apply, map_add (f := _)]
    ring
  continuous_toFun := continuous_pi fun k =>
    (continuous_apply k).add (continuous_const.mul ((continuous_sigR' σ).comp (continuous_apply (τ k))))
  continuous_invFun := continuous_pi fun k =>
    (continuous_apply k).sub (continuous_const.mul ((continuous_sigR' σ).comp (continuous_apply (τ k))))

theorem shear_apply {ι : Type} (τ : ι → ι) (z : ι → Fv F v ⊗[F] E) (k : ι) :
    D.shear τ z k = z k + D.e * sigR (Fv F v) σ (z (τ k)) := rfl

theorem shear_first_coordinate {ι : Type} (τ : ι → ι) (z : ι → Fv F v ⊗[F] E) (k : ι) :
    D.p 0 (D.shear τ z k) = D.p 0 (z k) + D.p 1 (z (τ k)) := by
  rw [shear_apply, map_add (f := _), map_mul, D.p_e.1, (D.p_sig _).1, one_mul]

theorem shear_second_coordinate {ι : Type} (τ : ι → ι) (z : ι → Fv F v ⊗[F] E) (k : ι) :
    D.p 1 (D.shear τ z k) = D.p 1 (z k) := by
  rw [shear_apply, map_add (f := _), map_mul, D.p_e.2, zero_mul, add_zero]

theorem mem_box_iff {ι : Type} (z : ι → Fv F v ⊗[F] E) :
    z ∈ Obox (E := E) v ι ↔ ∀ k, D.p 0 (z k) ∈ v.adicCompletionIntegers F ∧
      D.p 1 (z k) ∈ v.adicCompletionIntegers F := by
  simp only [Obox, Set.mem_pi, Set.mem_univ, true_implies, D.mem_iff]

theorem shear_box {ι : Type} (τ : ι → ι) : D.shear τ ⁻¹' Obox (E := E) v ι = Obox (E := E) v ι := by
  ext z
  rw [Set.mem_preimage, D.mem_box_iff, D.mem_box_iff]
  simp only [D.shear_first_coordinate, D.shear_second_coordinate]
  constructor
  · intro h k
    refine ⟨?_, (h k).2⟩
    have := sub_mem (h k).1 (h (τ k)).2
    simpa using this
  · intro h k
    exact ⟨add_mem (h k).1 (h (τ k)).2, (h k).2⟩

theorem mem_sc_mul (t : Fv F v) (c : Fv F v ⊗[F] E) :
    sc (E := E) v t * c ∈ OEv (E := E) v ↔
      t * D.p 0 c ∈ v.adicCompletionIntegers F ∧ t * D.p 1 c ∈ v.adicCompletionIntegers F := by
  rw [D.mem_iff, map_mul, map_mul, D.p_sc, D.p_sc]

def pt (s t : Fv F v) : Fv F v ⊗[F] E := s • D.e + t • (1 - D.e)

theorem p_pt (s t : Fv F v) : D.p 0 (D.pt s t) = s ∧ D.p 1 (D.pt s t) = t := D.p_pair s t

theorem isUnit_pt {s t : Fv F v} (hs : s ≠ 0) (ht : t ≠ 0) : IsUnit (D.pt s t) := by
  refine IsUnit.of_mul_eq_one (D.pt s⁻¹ t⁻¹) (D.ext ?_ ?_)
  · rw [map_mul, (D.p_pt _ _).1, (D.p_pt _ _).1, map_one, mul_inv_cancel₀ hs]
  · rw [map_mul, (D.p_pt _ _).2, (D.p_pt _ _).2, map_one, mul_inv_cancel₀ ht]

theorem mem_pt_mul (s t : Fv F v) (c : Fv F v ⊗[F] E) :
    D.pt s t * c ∈ OEv (E := E) v ↔
      s * D.p 0 c ∈ v.adicCompletionIntegers F ∧ t * D.p 1 c ∈ v.adicCompletionIntegers F := by
  rw [D.mem_iff, map_mul, map_mul, (D.p_pt _ _).1, (D.p_pt _ _).2]

theorem norm_pt (s t : Fv F v) : Algebra.norm (Fv F v) (D.pt s t) = s * t := by
  rw [D.norm_eq, (D.p_pt _ _).1, (D.p_pt _ _).2]

end SD

theorem obox_compact (ι : Type) [Finite ι] : IsCompact (Obox (E := E) v ι) :=
  isCompact_univ_pi fun _ => (integer_ring_topology (E := E) v).1

theorem obox_open (ι : Type) [Finite ι] : IsOpen (Obox (E := E) v ι) :=
  isOpen_set_pi Set.finite_univ fun _ _ => (integer_ring_topology (E := E) v).2.1

theorem obox_nonempty (ι : Type) : (Obox (E := E) v ι).Nonempty :=
  ⟨0, fun _ _ => Sd.oev_zero v⟩

end PI.UnitaryGroupMassFormula.LocJacTyp
