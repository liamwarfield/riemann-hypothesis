module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.StRedOfSplit

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.StKHolds
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.IsOpenForallMulVec
noncomputable section

namespace MassDataIdxK

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain Topology
open scoped Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes TensorProduct Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : ℕ} (v : HeightOneSpectrum (𝓞 F))

theorem isOpen_forall_mulVec {Λ U : Set (Fin n → Fv F v ⊗[F] E)} (hΛ : IsCompact Λ) (hU : IsOpen U) :
    IsOpen {A : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) | ∀ y ∈ Λ, A *ᵥ y ∈ U} := by
  have := fdFE (F := F) (E := E)
  have := MassDataIdxSteps.tens_topRing (F := F) (E := E) v
  rw [isOpen_iff_mem_nhds]
  intro A0 hA0
  exact hΛ.eventually_forall_of_forall_eventually fun y hy =>
    (continuous_fst.matrix_mulVec continuous_snd).continuousAt.preimage_mem_nhds (hU.mem_nhds (hA0 y hy))

theorem isCompact_stab (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (hfg : L.FG) :
    IsCompact {A : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) | ∀ y ∈ (latLoc (E := E) v (L : Set (Fin n → E)) :
      Set (Fin n → Fv F v ⊗[F] E)), A *ᵥ y ∈ (latLoc (E := E) v (L : Set (Fin n → E)) : Set (Fin n → Fv F v ⊗[F] E))} := by
  have := fdFE (F := F) (E := E)
  have := MassDataIdxSteps.tens_topRing (F := F) (E := E) v
  set Λ : Set (Fin n → Fv F v ⊗[F] E) := (latLoc (E := E) v (L : Set (Fin n → E)) : Set (Fin n → Fv F v ⊗[F] E)) with hΛ
  obtain ⟨m, b, hbΛ, hsp, -⟩ := latImage v L hL hfg
  obtain ⟨hΛo, hΛc⟩ := latOpenCompact v L hL hfg
  have hΛcl : IsClosed Λ :=
    AddSubgroup.isClosed_of_isOpen (latLoc (E := E) v (L : Set (Fin n → E))).toAddSubgroup hΛo
  have hclosed : IsClosed {A : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) | ∀ y ∈ Λ, A *ᵥ y ∈ Λ} := by
    have : {A : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) | ∀ y ∈ Λ, A *ᵥ y ∈ Λ} =
        ⋂ y ∈ Λ, (fun A : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) => A *ᵥ y) ⁻¹' Λ := by
      ext A; simp
    rw [this]
    exact isClosed_biInter fun y _ => hΛcl.preimage (continuous_id.matrix_mulVec continuous_const)
  let Ψ : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) →ₗ[Fv F v] (Fin m → Fin n → Fv F v ⊗[F] E) :=
    { toFun := fun A i => A *ᵥ b i
      map_add' := fun A B => by funext i; exact Matrix.add_mulVec A B (b i)
      map_smul' := fun r A => by
        funext i j
        simp [Matrix.mulVec, dotProduct, Finset.smul_sum, smul_mul_assoc] }
  have hinj : LinearMap.ker Ψ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro A hA
    let Al : (Fin n → Fv F v ⊗[F] E) →ₗ[Fv F v] (Fin n → Fv F v ⊗[F] E) :=
      { toFun := fun x => A *ᵥ x
        map_add' := Matrix.mulVec_add A
        map_smul' := fun r x => Matrix.mulVec_smul A r x }
    have hAl : Al = 0 := LinearMap.ext_on_range hsp (fun i => congrFun hA i)
    ext i j
    have := congrFun (LinearMap.congr_fun hAl (Pi.single j 1)) i
    simpa [Al, Matrix.mulVec_single_one] using this
  obtain ⟨Ψ', hΨ'⟩ := LinearMap.exists_leftInverse_of_injective Ψ hinj
  have hc : Continuous Ψ' := IsModuleTopology.continuous_of_linearMap Ψ'
  have hsub : {A : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) | ∀ y ∈ Λ, A *ᵥ y ∈ Λ} ⊆
      Ψ' '' Set.pi Set.univ (fun _ => Λ) := by
    intro A hA
    exact ⟨Ψ A, fun i _ => hA _ (hbΛ i), by rw [← LinearMap.comp_apply, hΨ', LinearMap.id_apply]⟩
  exact ((isCompact_univ_pi fun _ => hΛc).image hc).of_isClosed_subset hclosed hsub

theorem kloc_open_compact (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (hfg : L.FG) :
    IsOpen (Kloc (E := E) v (L : Set (Fin n → E)) : Set (GL (Fin n) (Fv F v ⊗[F] E))) ∧
      IsCompact (Kloc (E := E) v (L : Set (Fin n → E)) : Set (GL (Fin n) (Fv F v ⊗[F] E))) := by
  have := fdFE (F := F) (E := E)
  have := MassDataIdxSteps.tens_topRing (F := F) (E := E) v
  have := t2Space_scalarTensorExt (F := F) (E := E) v
  set Λ : Set (Fin n → Fv F v ⊗[F] E) := (latLoc (E := E) v (L : Set (Fin n → E)) : Set (Fin n → Fv F v ⊗[F] E)) with hΛ
  set S := {A : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) | ∀ y ∈ Λ, A *ᵥ y ∈ Λ} with hS
  obtain ⟨hΛo, hΛc⟩ := latOpenCompact v L hL hfg
  have hSo : IsOpen S := isOpen_forall_mulVec v hΛc hΛo
  have hSc : IsCompact S := isCompact_stab v L hL hfg
  have heq : (Kloc (E := E) v (L : Set (Fin n → E)) : Set (GL (Fin n) (Fv F v ⊗[F] E))) =
      Units.embedProduct _ ⁻¹' (S ×ˢ (MulOpposite.unop ⁻¹' S)) := by
    ext g
    show (∀ x, x ∈ Λ ↔ (g : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ x ∈ Λ) ↔
      ((g : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) ∈ S ∧
        ((g⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) ∈ S)
    constructor
    · intro hg
      refine ⟨fun y hy => (hg y).1 hy, fun y hy => ?_⟩
      have := (hg (((g⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) _) *ᵥ y)).2
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec] at this
      exact this hy
    · rintro ⟨h1, h2⟩ x
      refine ⟨h1 x, fun hx => ?_⟩
      have := h2 _ hx
      rwa [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at this
  rw [heq]
  refine ⟨(hSo.prod (hSo.preimage MulOpposite.continuous_unop)).preimage
    Units.isEmbedding_embedProduct.continuous, ?_⟩
  exact Units.isClosedEmbedding_embedProduct.isCompact_preimage
    (hSc.prod ((MulOpposite.opHomeomorph.symm.isCompact_preimage).2 hSc))

def sigL (σ : E →ₐ[F] E) : (Fv F v ⊗[F] E) →ₗ[Fv F v] (Fv F v ⊗[F] E) where
  toFun := sigR (Fv F v) σ
  map_add' := map_add _
  map_smul' := fun r x => by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]
    congr 1
    rw [Algebra.TensorProduct.algebraMap_apply]
    show Algebra.TensorProduct.map (AlgHom.id F (Fv F v)) σ (algebraMap (Fv F v) (Fv F v) r ⊗ₜ 1) = _
    rw [Algebra.TensorProduct.map_tmul, map_one]
    rfl

theorem isClosed_HR (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) :
    IsClosed ((HR (Fv F v) σ J : Subgroup (GL (Fin n) (Fv F v ⊗[F] E))) : Set (GL (Fin n) (Fv F v ⊗[F] E))) := by
  have := fdFE (F := F) (E := E)
  have := MassDataIdxSteps.tens_topRing (F := F) (E := E) v
  have := t2Space_scalarTensorExt (F := F) (E := E) v
  have hσ : Continuous (sigR (F := F) (Fv F v) σ) := IsModuleTopology.continuous_of_linearMap (sigL v σ)
  have hval : Continuous (fun g : GL (Fin n) (Fv F v ⊗[F] E) => (g : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))) :=
    Units.continuous_val
  exact isClosed_eq (((hval.matrix_map hσ).matrix_transpose.matrix_mul continuous_const).matrix_mul hval)
    continuous_const

end MassDataIdxK
end
end

noncomputable section

namespace MassDataIdxK

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain Topology
open scoped Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes TensorProduct Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : ℕ} (v : HeightOneSpectrum (𝓞 F))

theorem stK_gen (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (hfg : L.FG) (g : ℕ) (hg : g ≠ 0) :
    ∃ K : Subgroup (HA (Fv F v) σ J),
      (K : Set (HA (Fv F v) σ J)) = Formalism.L2.SG.TypedSets.Kv σ J (L : Set (Fin n → E)) v ∧
      IsOpen (K : Set (HA (Fv F v) σ J)) ∧ IsCompact (K : Set (HA (Fv F v) σ J)) ∧
      IsOpen (Formalism.L2.SG.TypedSets.Kgv σ J (L : Set (Fin n → E)) g v) := by
  have := fdFE (F := F) (E := E)
  have := MassDataIdxSteps.tens_topRing (F := F) (E := E) v
  obtain ⟨hKo, hKc⟩ := kloc_open_compact v L hL hfg
  obtain ⟨hΛo, hΛc⟩ := latOpenCompact v L hL hfg
  have hHc := isClosed_HR v σ J
  let K : Subgroup (HA (Fv F v) σ J) :=
    (Kloc (E := E) v (L : Set (Fin n → E))).comap (HR (Fv F v) σ J).subtype
  have hKset : (K : Set (HA (Fv F v) σ J)) = Formalism.L2.SG.TypedSets.Kv σ J (L : Set (Fin n → E)) v := rfl
  have hKo' : IsOpen (K : Set (HA (Fv F v) σ J)) := hKo.preimage continuous_subtype_val
  refine ⟨K, hKset, hKo', hHc.isClosedEmbedding_subtypeVal.isCompact_preimage hKc, ?_⟩
  set Λ : Set (Fin n → Fv F v ⊗[F] E) := (latLoc (E := E) v (L : Set (Fin n → E)) : Set (Fin n → Fv F v ⊗[F] E)) with hΛ
  set U : Set (Fin n → Fv F v ⊗[F] E) := {w | ∃ z ∈ Λ, w = (g : v.adicCompletionIntegers F) • z} with hUdef
  have hc : ((g : v.adicCompletionIntegers F) : Fv F v) ≠ 0 := by
    have : ((g : v.adicCompletionIntegers F) : Fv F v) = algebraMap F (Fv F v) g := by simp
    rw [this]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hg)
  have hU : IsOpen U := by
    have : U = (fun z => ((g : v.adicCompletionIntegers F) : Fv F v) • z) '' Λ := by
      ext w
      constructor
      · rintro ⟨z, hz, rfl⟩; exact ⟨z, hz, rfl⟩
      · rintro ⟨z, hz, rfl⟩; exact ⟨z, hz, rfl⟩
    rw [this]
    exact isOpenMap_smul₀ hc _ hΛo
  have hS : IsOpen {h : GL (Fin n) (Fv F v ⊗[F] E) |
      ((h : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) - 1) ∈
        {A : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) | ∀ y ∈ Λ, A *ᵥ y ∈ U}} :=
    (isOpen_forall_mulVec v hΛc hU).preimage (Units.continuous_val.sub continuous_const)
  have heq : Formalism.L2.SG.TypedSets.Kgv σ J (L : Set (Fin n → E)) g v =
      (K : Set (HA (Fv F v) σ J)) ∩ (Subtype.val ⁻¹' {h : GL (Fin n) (Fv F v ⊗[F] E) |
        ((h : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) - 1) ∈
          {A : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) | ∀ y ∈ Λ, A *ᵥ y ∈ U}}) :=
    Set.ext fun x => Iff.rfl
  rw [heq]
  exact hKo'.inter (hS.preimage continuous_subtype_val)

end MassDataIdxK

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.TypedSets Formalism.L2.SG.HidaSetting

theorem stK_holds {D : Formalism.BasicNotions.D7} (X : HidaSetting D) (p : TypX X) : StK X p :=
  MassDataIdxK.stK_gen p.1 X.B.I.cm.sig X.B.I.J X.B.I.L X.B.I.L_span X.B.I.L_fg (gOf p) (gOf_prime X p).ne_zero

end MassDataIdxSteps
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.StRedOfParts
noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
open scoped TensorProduct

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X)

abbrev FpX : Type := Fv X.B.I.F p.1

abbrev TpX : Type := FpX X p ⊗[X.B.I.F] X.B.I.E

theorem card_idx : Fintype.card (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) = X.B.I.n := by
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]

  rw [X.n_eq]
  obtain ⟨a, ha⟩ := D.R.m_even
  have h2 := D.R.two_le_m
  simp only [Formalism.BasicNotions.Ranks.rS, Formalism.BasicNotions.Ranks.r]
  omega

def idxEquiv : Fin X.B.I.n ≃ Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k :=
  Fintype.equivOfCardEq (by rw [card_idx X, Fintype.card_fin])

def IsSplitEquiv (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p) : Prop :=
  ∀ t, θ (sigR (FpX X p) X.B.I.cm.sig t) = (θ t).swap

def th1 (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p) : TpX X p →+* FpX X p :=
  (RingHom.fst (FpX X p) (FpX X p)).comp θ.toAlgHom.toRingHom

def th2 (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p) : TpX X p →+* FpX X p :=
  (RingHom.snd (FpX X p) (FpX X p)).comp θ.toAlgHom.toRingHom

def J1 (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (FpX X p) :=
  X.B.I.J.map (fun e => th1 X p θ (inclR (FpX X p) e))

def LatBasis (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p) (P : GL (Fin X.B.I.n) (FpX X p)) : Prop :=
  ∀ x : Fin X.B.I.n → TpX X p, x ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) ↔
    (∀ i, (Matrix.mulVec ((P⁻¹ : GL (Fin X.B.I.n) (FpX X p)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (FpX X p))
        fun j => th1 X p θ (x j)) i ∈ p.1.adicCompletionIntegers X.B.I.F) ∧
    (∀ i, (Matrix.mulVec (Matrix.transpose ((P : GL (Fin X.B.I.n) (FpX X p)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (FpX X p)) *
        Matrix.transpose (J1 X p θ))
        fun j => th2 X p θ (x j)) i ∈ p.1.adicCompletionIntegers X.B.I.F)

def StSplitLat : Prop :=
  ∃ θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p, IsSplitEquiv X p θ ∧ ∃ P, LatBasis X p θ P

end Loc

def LatCore : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p),
    IsSplitEquiv X p θ → ∀ P, LatBasis X p θ P → StLatGL X p

theorem stRed_of_parts {D : D7} (X : HidaSetting D) (p : TypX X) (hR : StResZ X p) (hS : StSplitLat X p)
    (hC : LatCore) : StRed X p := by
  obtain ⟨θ, hθ, P, hP⟩ := hS
  have hL : StLatGL X p := hC X p θ hθ P hP
  obtain ⟨π, hπ, hker⟩ := hR
  intro K hK
  obtain ⟨ψ, hψ, hψk⟩ := hL K hK
  refine ⟨(Matrix.GeneralLinearGroup.map π).comp ψ, ?_, ?_⟩
  · intro M
    classical
    rcases subsingleton_or_nontrivial (ZMod (gOf p)) with hs | hs
    · refine ⟨1, ?_⟩
      apply Units.ext
      ext i j
      exact @Subsingleton.elim _ hs _ _

    let A : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p) :=
      fun i j => Function.surjInv hπ ((M : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p))) i j)
    have hA : ∀ i j, π (A i j) = (M : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p))) i j :=
      fun i j => Function.surjInv_eq hπ _
    have hdetM : IsUnit (M : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p))).det :=
      by
        first
          | exact Matrix.isUnits_det_units M
          | exact (Matrix.isUnit_iff_isUnit_det (M : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p)))).mp M.isUnit
    have hmap : π A.det = (M : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p))).det := by
      rw [RingHom.map_det]
      congr 1
      ext i j
      exact hA i j
    have hle : RingHom.ker π ≤ IsLocalRing.maximalIdeal (Op X p) :=
      IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top π)
    have hdet : IsUnit A.det := by
      by_contra hnu
      have hm : A.det ∈ IsLocalRing.maximalIdeal (Op X p) :=
        (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu)
      obtain ⟨v, hv⟩ := IsUnit.exists_right_inv (show IsUnit (π A.det) by rw [hmap]; exact hdetM)
      obtain ⟨b, rfl⟩ := hπ v
      have h1 : A.det * b - 1 ∈ RingHom.ker π := by
        rw [RingHom.mem_ker, RingHom.map_sub, map_mul, hv, map_one, sub_self]
      have h2 : A.det * b ∈ IsLocalRing.maximalIdeal (Op X p) := by
        first
          | exact Ideal.mul_mem_right _ _ hm
          | exact Ideal.mul_mem_right _ hm
      have h3 : (1 : Op X p) ∈ IsLocalRing.maximalIdeal (Op X p) := by
        have h4 := Ideal.sub_mem _ h2 (hle h1)
        rwa [sub_sub_cancel] at h4
      exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp h3)) isUnit_one
    obtain ⟨x, hx⟩ := hψ ((Matrix.isUnit_iff_isUnit_det A).mpr hdet).unit
    refine ⟨x, ?_⟩
    apply Units.ext
    ext i j
    rw [MonoidHom.comp_apply, hx]
    exact hA i j
  · intro x

    have key : ∀ i j, π (((ψ x : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p)) - 1) i j) =
        ((Matrix.GeneralLinearGroup.map π (ψ x) : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p))) - 1) i j := by
      intro i j
      rw [Matrix.sub_apply, Matrix.sub_apply, map_sub, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp only [map_one, map_zero] <;> rfl
    rw [← hψk x, ← hker]
    constructor
    · intro h i j
      rw [RingHom.mem_ker, key]
      have h' : (Matrix.GeneralLinearGroup.map π (ψ x) : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p))) = 1 := by
        rw [MonoidHom.comp_apply] at h
        rw [h]
        rfl
      rw [h', sub_self]
      rfl
    · intro h
      apply Units.ext
      ext i j
      have h0 := h i j
      rw [RingHom.mem_ker, key, Matrix.sub_apply, sub_eq_zero] at h0
      exact h0

end MassDataIdxSteps
end
end
