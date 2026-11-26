module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.FrameStd

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.LatStab
noncomputable section

namespace MassDataLevelSSteps.LatTop

open scoped TensorProduct
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets Matrix MeasureTheory NumberField IsDedekindDomain
  Topology PI.AdicCompletionValuation

section Open

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [FiniteDimensional F E] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

theorem intCast_ne_zero_Fv {N : ℤ} (hN : N ≠ 0) : (N : Fv F v) ≠ 0 := by
  rw [← map_intCast (algebraMap F (Fv F v)) N]
  exact (map_ne_zero (algebraMap F (Fv F v))).mpr (Int.cast_ne_zero.mpr hN)

theorem exists_common_mult {ι : Type} [Fintype ι] (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (x : ι → Fin n → E) :
    ∃ N : ℤ, N ≠ 0 ∧ ∀ q, N • x q ∈ L := by
  classical
  have hN : ∀ q, ∃ N : ℤ, N ≠ 0 ∧ N • x q ∈ L := fun q => exists_int_smul_mem L hL _
  choose Nf hNf hNm using hN
  refine ⟨∏ q, Nf q, Finset.prod_ne_zero_iff.2 fun q _ => hNf q, fun q => ?_⟩
  have hq : ∏ q, Nf q = (∏ q' ∈ Finset.univ.erase q, Nf q') * Nf q :=
    (Finset.prod_erase_mul _ _ (Finset.mem_univ q)).symm
  rw [hq, mul_smul]
  exact zsmul_mem (hNm q) _

theorem isOpen_latLoc (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    IsOpen (latLoc (E := E) v (L : Set (Fin n → E)) : Set (Fin n → Fv F v ⊗[F] E)) := by
  classical
  set M := latLoc (E := E) v (L : Set (Fin n → E))
  let b := Module.finBasis F E
  let Bt := Algebra.TensorProduct.basis (Fv F v) b
  obtain ⟨N, hN0, hNmem⟩ := exists_common_mult L hL
    (fun q : Fin n × Fin (Module.finrank F E) => (Pi.single q.1 (b q.2) : Fin n → E))
  have hNv : (N : Fv F v) ≠ 0 := intCast_ne_zero_Fv v hN0
  have hsingle : ∀ j k, (N : Fv F v) • (Pi.single j (Bt k) : Fin n → Fv F v ⊗[F] E) ∈ M := by
    intro j k
    rw [Algebra.TensorProduct.basis_apply, ← ratV_zsmul_single v N j (b k)]
    exact Submodule.subset_span ⟨_, hNmem (j, k), rfl⟩
  have hcoord : ∀ j (z : Fv F v ⊗[F] E), (∀ k, Bt.repr z k ∈ v.adicCompletionIntegers F) →
      (N : Fv F v) • (Pi.single j z : Fin n → Fv F v ⊗[F] E) ∈ M := by
    intro j z hz
    have hrep : (N : Fv F v) • (Pi.single j z : Fin n → Fv F v ⊗[F] E) =
        ∑ k, Bt.repr z k • ((N : Fv F v) • (Pi.single j (Bt k) : Fin n → Fv F v ⊗[F] E)) := by
      funext i
      by_cases h : i = j
      · subst h
        simp only [Pi.smul_apply, Finset.sum_apply, Pi.single_eq_same]
        conv_lhs => rw [← Bt.sum_repr z]
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [smul_comm]
      · simp [Pi.single_eq_of_ne h]
    rw [hrep]
    exact Submodule.sum_mem _ fun k _ => smul_mem_latLoc v _ (hz k) (hsingle j k)
  let U : Set (Fin n → Fv F v ⊗[F] E) := {y | ∀ j k, Bt.repr (y j) k ∈ v.adicCompletionIntegers F}
  have hUo : IsOpen U := by
    have e : U = ⋂ j, ⋂ k, (fun y : Fin n → Fv F v ⊗[F] E => Bt.coord k (y j)) ⁻¹'
        (v.adicCompletionIntegers F : Set (Fv F v)) := by
      ext y
      simp [U, Module.Basis.coord_apply]
    rw [e]
    exact isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite fun k =>
      (Valued.isOpen_valuationSubring _).preimage
        ((IsModuleTopology.continuous_of_linearMap (Bt.coord k)).comp (continuous_apply j))
  have hUM : ∀ y ∈ U, (N : Fv F v) • y ∈ M := by
    intro y hy
    rw [← Finset.univ_sum_single y, Finset.smul_sum]
    exact Submodule.sum_mem _ fun j _ => hcoord j (y j) (hy j)
  let W : Set (Fin n → Fv F v ⊗[F] E) := {y | (N : Fv F v)⁻¹ • y ∈ U}
  have hWo : IsOpen W := hUo.preimage (continuous_const_smul _)
  have hW0 : (0 : Fin n → Fv F v ⊗[F] E) ∈ W := by
    show (N : Fv F v)⁻¹ • (0 : Fin n → Fv F v ⊗[F] E) ∈ U
    rw [smul_zero]
    intro j k
    simp
  have hWM : W ⊆ M := by
    intro y hy
    have h := hUM _ hy
    rwa [smul_smul, mul_inv_cancel₀ hNv, one_smul] at h
  exact M.toAddSubgroup.isOpen_of_mem_nhds (Filter.mem_of_superset (hWo.mem_nhds hW0) hWM)

end Open

section Mat

variable {A : Type} [Ring A] [TopologicalSpace A] [IsTopologicalRing A] {n : ℕ}

def matStab (M : Set (Fin n → A)) : Set (Matrix (Fin n) (Fin n) A) := {m | ∀ x ∈ M, m *ᵥ x ∈ M}

theorem isOpen_matStab {M : Set (Fin n → A)} (hc : IsCompact M) (ho : IsOpen M) :
    IsOpen (matStab M) := by
  rw [isOpen_iff_eventually]
  intro m0 hm0
  have hcont : Continuous fun z : Matrix (Fin n) (Fin n) A × (Fin n → A) => z.1 *ᵥ z.2 :=
    continuous_fst.matrix_mulVec continuous_snd
  exact hc.eventually_forall_of_forall_eventually (P := fun m x => m *ᵥ x ∈ M)
    fun x hx => (hcont.tendsto (m0, x)).eventually (ho.mem_nhds (hm0 x hx))

theorem isClosed_matStab {M : Set (Fin n → A)} (hcl : IsClosed M) : IsClosed (matStab M) := by
  have e : matStab M = ⋂ x ∈ M, (fun m : Matrix (Fin n) (Fin n) A => m *ᵥ x) ⁻¹' M := by
    ext m
    simp [matStab]
  rw [e]
  exact isClosed_biInter fun x _ => hcl.preimage (continuous_id.matrix_mulVec continuous_const)

theorem isCompact_matStab {K : Type} [Field K] [Module K A] [SMulCommClass K A A]
    [ContinuousConstSMul K A] {M : Set (Fin n → A)} (hc : IsCompact M) (hcl : IsClosed M) (c : K)
    (hc0 : c ≠ 0) (hcol : ∀ j, c • (Pi.single j 1 : Fin n → A) ∈ M) : IsCompact (matStab M) := by
  classical
  let Q : Set (Fin n → A) := (fun y => c⁻¹ • y) '' M
  have hQ : IsCompact Q := hc.image (continuous_const_smul _)
  have hT : IsCompact ((fun m : Matrix (Fin n) (Fin n) A => mᵀ) ''
      (Set.univ.pi fun _ => Q : Set (Matrix (Fin n) (Fin n) A))) :=
    (isCompact_univ_pi fun _ => hQ).image continuous_id.matrix_transpose
  refine hT.of_isClosed_subset (isClosed_matStab hcl) ?_
  intro m hm
  refine ⟨mᵀ, fun j _ => ?_, Matrix.transpose_transpose m⟩
  refine ⟨c • mᵀ j, ?_, ?_⟩
  · have h := hm _ (hcol j)
    rw [Matrix.mulVec_smul, Matrix.mulVec_single_one] at h
    exact h
  · simp only [smul_smul, inv_mul_cancel₀ hc0, one_smul]

end Mat

section Grp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [FiniteDimensional F E] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

theorem kloc_eq (L : Set (Fin n → E)) :
    (Kloc (E := E) v L : Set (GL (Fin n) (Fv F v ⊗[F] E))) =
      {g : GL (Fin n) (Fv F v ⊗[F] E) | ((g : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))) ∈
          matStab (latLoc (E := E) v L : Set (Fin n → Fv F v ⊗[F] E)) ∧
        (((g⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))) ∈
          matStab (latLoc (E := E) v L : Set (Fin n → Fv F v ⊗[F] E))} := by
  ext g
  constructor
  · intro hg
    have hg' : g⁻¹ ∈ Kloc (E := E) v L := (Kloc (E := E) v L).inv_mem hg
    exact ⟨fun x hx => (hg x).1 hx, fun x hx => (hg' x).1 hx⟩
  · rintro ⟨h1, h2⟩
    show ∀ x, _
    intro x
    refine ⟨h1 x, fun hx => ?_⟩
    have h := h2 _ hx
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec] at h

variable (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤)
  (hfg : L.FG)
include hL hfg

theorem isOpen_kloc : IsOpen (Kloc (E := E) v (L : Set (Fin n → E)) : Set (GL (Fin n) (Fv F v ⊗[F] E))) := by
  rw [kloc_eq]
  have hS := isOpen_matStab (isCompact_latLoc v L hfg) (isOpen_latLoc v L hL)
  exact (hS.preimage Units.continuous_val).inter (hS.preimage Units.continuous_coe_inv)

theorem isCompact_kloc :
    IsCompact (Kloc (E := E) v (L : Set (Fin n → E)) : Set (GL (Fin n) (Fv F v ⊗[F] E))) := by
  classical
  set M := latLoc (E := E) v (L : Set (Fin n → E))
  have hMc := isCompact_latLoc v L hfg
  have hMo := isOpen_latLoc v L hL
  have hMcl : IsClosed (M : Set (Fin n → Fv F v ⊗[F] E)) := M.toAddSubgroup.isClosed_of_isOpen hMo
  obtain ⟨N, hN0, hNmem⟩ := exists_common_mult L hL (fun j : Fin n => (Pi.single j (1 : E) : Fin n → E))
  have hcol : ∀ j, (N : Fv F v) • (Pi.single j 1 : Fin n → Fv F v ⊗[F] E) ∈ M := by
    intro j
    rw [Algebra.TensorProduct.one_def, ← ratV_zsmul_single v N j (1 : E)]
    exact Submodule.subset_span ⟨_, hNmem j, rfl⟩
  have hSc := isCompact_matStab hMc hMcl (N : Fv F v) (intCast_ne_zero_Fv v hN0) hcol
  rw [kloc_eq]
  have e : {g : GL (Fin n) (Fv F v ⊗[F] E) | ((g : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))) ∈
          matStab (M : Set (Fin n → Fv F v ⊗[F] E)) ∧
        (((g⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))) ∈
          matStab (M : Set (Fin n → Fv F v ⊗[F] E))} =
      Units.embedProduct _ ⁻¹' (matStab (M : Set (Fin n → Fv F v ⊗[F] E)) ×ˢ
        (MulOpposite.op '' matStab (M : Set (Fin n → Fv F v ⊗[F] E)))) := by
    ext g
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, ⟨_, h2, rfl⟩⟩
    · rintro ⟨h1, y, hy, hyg⟩
      refine ⟨h1, ?_⟩
      have hy' : y = (((g⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))) :=
        MulOpposite.op_injective hyg
      rwa [hy'] at hy
  rw [e]
  exact Units.isClosedEmbedding_embedProduct.isCompact_preimage
    (hSc.prod (hSc.image MulOpposite.continuous_op))

theorem isCompact_Kv (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) :
    IsCompact (Kv σ J (L : Set (Fin n → E)) v) :=
  have : LocallyCompactSpace (Fv F v) :=
    (isCompact_adicCompletionIntegers F v).locallyCompactSpace_of_mem_nhds_of_addGroup
      ((Valued.isOpen_valuationSubring _).mem_nhds (zero_mem _))
  (isClosed_HR (Fv F v) σ J).isClosedEmbedding_subtypeVal.isCompact_preimage
    (isCompact_kloc v L hL hfg)

theorem isOpen_Kv (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) :
    IsOpen (Kv σ J (L : Set (Fin n → E)) v) :=
  (isOpen_kloc v L hL hfg).preimage continuous_subtype_val

end Grp

section Flag

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  [FiniteDimensional F E] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

theorem isClosed_submodule (W : Submodule (Fv F v ⊗[F] E) (Fin n → Fv F v ⊗[F] E)) :
    IsClosed (W : Set (Fin n → Fv F v ⊗[F] E)) := by
  classical
  let W' := W.restrictScalars (Fv F v)
  let Bq := Module.Free.chooseBasis (Fv F v) ((Fin n → Fv F v ⊗[F] E) ⧸ W')
  let f : (Fin n → Fv F v ⊗[F] E) →ₗ[Fv F v]
      (Module.Free.ChooseBasisIndex (Fv F v) ((Fin n → Fv F v ⊗[F] E) ⧸ W') → Fv F v) :=
    Bq.equivFun.toLinearMap ∘ₗ W'.mkQ
  have hf : Continuous f := IsModuleTopology.continuous_of_linearMap f
  have e : (W : Set (Fin n → Fv F v ⊗[F] E)) = f ⁻¹' {0} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, f, LinearMap.coe_comp, Function.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.map_eq_zero_iff, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, W', Submodule.restrictScalars_mem, SetLike.mem_coe]
  rw [e]
  exact isClosed_singleton.preimage hf

theorem isClosed_Ssub (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) {r : ℕ} (P : Frame E n r) :
    IsClosed (Ssub (Fv F v) σ J P : Set (HA (Fv F v) σ J)) := by
  have e : (Ssub (Fv F v) σ J P : Set (HA (Fv F v) σ J)) = ⋂ b, (fun g : HA (Fv F v) σ J =>
      lin (Fv F v) σ J g (ratV (F := F) (Fv F v) (F0 P b)) - ratV (F := F) (Fv F v) (F0 P b)) ⁻¹'
      (spanR (F := F) (Fv F v) (F0 P) {a | a < b} : Set (Fin n → Fv F v ⊗[F] E)) := by
    ext g
    simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    exact Iff.rfl
  rw [e]
  refine isClosed_iInter fun b => (isClosed_submodule v _).preimage ?_
  have hm : Continuous fun g : HA (Fv F v) σ J =>
      ((HA.mat (Fv F v) σ J g : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) :=
    Units.continuous_val.comp continuous_subtype_val
  exact (hm.matrix_mulVec continuous_const).sub continuous_const

end Flag

end MassDataLevelSSteps.LatTop
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.LatAdapted
noncomputable section

namespace MassDataLevelSSteps.LatW

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D)

abbrev crd (y : (VS D).V) : Fin X.B.I.n → X.B.I.E := crdOf X.B.I X.ιE X.bas y

theorem crd_add (y z : (VS D).V) : crd X (y + z) = crd X y + crd X z := by
  funext i; simp [crd, crdOf, map_add (f := _)]

theorem crd_zero : crd X 0 = 0 := by
  funext i; simp [crd, crdOf]

theorem crd_smul (c : D.host.E) (y : (VS D).V) : crd X (c • y) = X.ιE.symm c • crd X y := by
  funext i; simp [crd, crdOf, map_mul, smul_eq_mul]

theorem crd_mem_span {S : Set (VS D).V} {y : (VS D).V} (hy : y ∈ Submodule.span D.host.E S) :
    crd X y ∈ Submodule.span X.B.I.E (crd X '' S) := by
  induction hy using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => rw [crd_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [crd_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [crd_smul]; exact Submodule.smul_mem _ _ hx

theorem latSpanS_le {r : ℕ} (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)
    (v : Fin r → (VS D).V) {y : (VS D).V} (hy : y ∈ latSpanS aa v) :
    y ∈ Submodule.span D.host.E (Set.range v) := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, c, -, rfl⟩ := hx
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [← algebraMap_smul D.host.E c x]
    exact Submodule.smul_mem _ _ hx

theorem crd_mem_L {y : (VS D).V} (hy : y ∈ (VS D).L0) : crd X y ∈ X.B.I.L := by
  rw [X.L_eq]
  simp only [crd, crdOf, RingEquiv.apply_symm_apply]
  rw [X.bas.sum_repr y]
  exact hy

theorem L_crd {x : Fin X.B.I.n → X.B.I.E} (hx : x ∈ X.B.I.L) : ∃ y ∈ (VS D).L0, x = crd X y := by
  refine ⟨_, (X.L_eq x).1 hx, ?_⟩
  funext i
  show x i = X.ιE.symm (X.bas.repr (∑ j, X.ιE (x j) • X.bas j) i)
  rw [Module.Basis.repr_sum_self]
  simp

theorem ratV_add (R : Type) [CommRing R] [Algebra X.B.I.F R] (a b : Fin X.B.I.n → X.B.I.E) :
    ratV (F := X.B.I.F) R (a + b) = ratV (F := X.B.I.F) R a + ratV (F := X.B.I.F) R b := by
  funext i
  simp [ratV, map_add (f := _)]

def LX : Set (Fin X.B.I.n → X.B.I.E) := crd X '' (latSpanS (fun a => aaD D a) X.eX : Set (VS D).V)

def LW : Set (Fin X.B.I.n → X.B.I.E) := crd X '' (X.Lb : Set (VS D).V)

def LY : Set (Fin X.B.I.n → X.B.I.E) := crd X '' (latSpanS (fun a => (aaD D a)⁻¹) X.fY : Set (VS D).V)

theorem adapted (w : D.what₂.Word) :
    Formalism.L2.SG.Volumes.Adapted X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J (frameOf X w) (LX X) (LW X) (LY X) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    have h := crd_mem_span X (latSpanS_le _ _ hy)
    rw [← Set.range_comp] at h
    exact h
  · rintro _ ⟨y, hy, rfl⟩
    have h := crd_mem_span X (latSpanS_le _ _ hy)
    rw [← Set.range_comp] at h
    exact h
  · rintro _ ⟨y, hy, rfl⟩ a
    have h := X.Lb_perp y hy a
    constructor
    · show hE _ _ (crdOf X.B.I X.ιE X.bas (X.eX a)) (crdOf X.B.I X.ιE X.bas y) = 0
      rw [FrameW.hE_crdOf, h.1, map_zero]
    · show hE _ _ (crdOf X.B.I X.ιE X.bas (X.fY a)) (crdOf X.B.I X.ιE X.bas y) = 0
      rw [FrameW.hE_crdOf, h.2, map_zero]

theorem latLoc_eq (v : HeightOneSpectrum (𝓞 X.B.I.F)) :
    latLoc (E := X.B.I.E) v (LX X ∪ LW X ∪ LY X) = latLoc v (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
  apply le_antisymm
  · apply Submodule.span_mono
    apply Set.image_mono
    rintro _ ((⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩) | ⟨y, hy, rfl⟩)
    · exact crd_mem_L X (by rw [X.Lam_split]; exact Submodule.mem_sup_left (Submodule.mem_sup_left hy))
    · exact crd_mem_L X (by rw [X.Lam_split]; exact Submodule.mem_sup_left (Submodule.mem_sup_right hy))
    · exact crd_mem_L X (by rw [X.Lam_split]; exact Submodule.mem_sup_right hy)
  · apply Submodule.span_le.2
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, rfl⟩ := L_crd X hx
    rw [X.Lam_split] at hy
    obtain ⟨ab, hab, c, hc, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hab
    rw [crd_add, crd_add, ratV_add, ratV_add]
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
    · exact Submodule.subset_span ⟨crd X a, Or.inl (Or.inl ⟨a, ha, rfl⟩), rfl⟩
    · exact Submodule.subset_span ⟨crd X b, Or.inl (Or.inr ⟨b, hb, rfl⟩), rfl⟩
    · exact Submodule.subset_span ⟨crd X c, Or.inr ⟨c, hc, rfl⟩, rfl⟩

theorem Kf_eq :
    Kf X.B.I.cm.sig X.B.I.J (LX X ∪ LW X ∪ LY X) = Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
  have hK : ∀ v : HeightOneSpectrum (𝓞 X.B.I.F),
      Kloc (E := X.B.I.E) v (LX X ∪ LW X ∪ LY X) = Kloc v (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
    intro v
    ext g
    show (∀ x, x ∈ latLoc (E := X.B.I.E) v (LX X ∪ LW X ∪ LY X) ↔ _) ↔
      (∀ x, x ∈ latLoc (E := X.B.I.E) v (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) ↔ _)
    rw [latLoc_eq]
  simp only [Kf, hK]

end MassDataLevelSSteps.LatW

namespace MassDataLevelSSteps

theorem latAdapted_holds : LatAdapted := by
  intro D X w
  exact ⟨LatW.LX X, LatW.LW X, LatW.LY X, LatW.adapted X w, LatW.Kf_eq X⟩

end MassDataLevelSSteps
end
end
