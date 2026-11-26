module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecCEApply
noncomputable section

namespace GlobalTheory.ModuLR

open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

section Gen

variable {S : Type} [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] {κ : Type} [Fintype κ] [DecidableEq κ]

def mulVecCE (M : Matrix κ κ S) (hM : IsUnit M.det) : (κ → S) ≃ₜ+ (κ → S) where
  toFun x := M *ᵥ x
  invFun x := M⁻¹ *ᵥ x
  left_inv x := by simp [mulVec_mulVec, nonsing_inv_mul M hM]
  right_inv x := by simp [mulVec_mulVec, mul_nonsing_inv M hM]
  map_add' x y := mulVec_add M x y
  continuous_toFun := continuous_const.matrix_mulVec continuous_id
  continuous_invFun := continuous_const.matrix_mulVec continuous_id

theorem mulVecCE_apply (M : Matrix κ κ S) (hM : IsUnit M.det) (x : κ → S) : mulVecCE M hM x = M *ᵥ x := rfl

end Gen

def prodCE {G₁ G₂ : Type} [AddCommGroup G₁] [TopologicalSpace G₁] [AddCommGroup G₂] [TopologicalSpace G₂]
    (e₁ : G₁ ≃ₜ+ G₁) (e₂ : G₂ ≃ₜ+ G₂) : (G₁ × G₂) ≃ₜ+ (G₁ × G₂) :=
  { AddEquiv.prodCongr e₁.toAddEquiv e₂.toAddEquiv with
    continuous_toFun := e₁.continuous.prodMap e₂.continuous
    continuous_invFun := e₁.symm.continuous.prodMap e₂.symm.continuous }

theorem prodCE_apply {G₁ G₂ : Type} [AddCommGroup G₁] [TopologicalSpace G₁] [AddCommGroup G₂]
    [TopologicalSpace G₂] (e₁ : G₁ ≃ₜ+ G₁) (e₂ : G₂ ≃ₜ+ G₂) (x : G₁ × G₂) : prodCE e₁ e₂ x = (e₁ x.1, e₂ x.2) := rfl

def lrCE {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {m n : ℕ} (g : GL (Fin m) R)
    (a : GL (Fin n) R) : Matrix (Fin m) (Fin n) R ≃ₜ+ Matrix (Fin m) (Fin n) R where
  toFun u := (g : Matrix (Fin m) (Fin m) R) * u * (a : Matrix (Fin n) (Fin n) R)
  invFun u := ((g⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) * u * ((a⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)
  left_inv u := by
    simp only [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
    rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  right_inv u := by
    simp only [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
    rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  map_add' u v := by rw [Matrix.mul_add, Matrix.add_mul]
  continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

theorem lrCE_apply {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {m n : ℕ} (g : GL (Fin m) R)
    (a : GL (Fin n) R) (u : Matrix (Fin m) (Fin n) R) :
    lrCE g a u = (g : Matrix (Fin m) (Fin m) R) * u * (a : Matrix (Fin n) (Fin n) R) := rfl

def zipHom (κ X Y : Type) [AddCommGroup X] [AddCommGroup Y] : (κ → X) × (κ → Y) →+ (κ → X × Y) where
  toFun p i := (p.1 i, p.2 i)
  map_zero' := rfl
  map_add' _ _ := rfl

section Places

variable (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))

abbrev SPart : Type := ∀ v : S, Fv F v.1

abbrev OPart : Type := ∀ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, v.1.adicCompletionIntegers F


open Classical in
def jS : SPart F S × OPart F S →+* Af F where
  toFun p := ⟨fun v => if h : v ∈ S then p.1 ⟨v, h⟩ else (p.2 ⟨v, h⟩ : Fv F v),
    Filter.eventually_cofinite.2 (S.finite_toSet.subset fun v hv => by
      by_contra h
      exact hv (by simp only [dif_neg (show v ∉ S from h)]; exact (p.2 ⟨v, h⟩).2))⟩
  map_one' := Subtype.ext (funext fun v => by
    show dite (v ∈ S) _ _ = 1
    split_ifs <;> rfl)
  map_mul' p q := Subtype.ext (funext fun v => by
    show dite (v ∈ S) _ _ = dite (v ∈ S) _ _ * dite (v ∈ S) _ _
    split_ifs <;> rfl)
  map_zero' := Subtype.ext (funext fun v => by
    show dite (v ∈ S) _ _ = 0
    split_ifs <;> rfl)
  map_add' p q := Subtype.ext (funext fun v => by
    show dite (v ∈ S) _ _ = dite (v ∈ S) _ _ + dite (v ∈ S) _ _
    split_ifs <;> rfl)

open Classical in
theorem evalV_jS (p : SPart F S × OPart F S) (v : HeightOneSpectrum (𝓞 F)) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (jS F S p) = if h : v ∈ S then p.1 ⟨v, h⟩ else (p.2 ⟨v, h⟩ : Fv F v) := rfl

end Places

end GlobalTheory.ModuLR
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SuppInd
noncomputable section

open Classical

namespace GlobalTheory.LevelVecNorm

def locH {E : Type} [Field E] [NumberField E] (Pg : Finset (Formalism.L2.DIV.Pl E)) {r : ℕ}
    (Hl : ∀ PP : ↥Pg, Subgroup (GL (Fin r) (Formalism.L2.DIV.kP PP.1))) (PP : Formalism.L2.DIV.Pl E) :
    Subgroup (GL (Fin r) (Formalism.L2.DIV.kP PP)) :=
  if h : PP ∈ Pg then Hl ⟨PP, h⟩ else ⊤


open Classical in
def suppInd {k : Type} [CommRing k] (r : ℕ) {b a : ℕ} (H : Subgroup (GL (Fin r) k)) (z : Matrix (Fin b) (Fin a) k) : ℝ :=
  if Formalism.IndefR.Datum.LowZero r z ∧ ∃ g ∈ H, ((g : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) = Formalism.IndefR.Datum.topL r z then 1 else 0

end GlobalTheory.LevelVecNorm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteAlgebraAdelicLatticeProof
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteAlgebraAdelicLatticeProof
open GlobalTheory.RegSS

open Formalism.UG NumberField Topology
open scoped TensorProduct

namespace GlobalTheory.RegSSLattice

open NumberField Topology in
open scoped TensorProduct in
private lemma finite_setOf_algebraMap_mem_of_isCompact (F : Type) [Field F] [NumberField F]
    {K : Set (AdeleRing (𝓞 F) F)} (hK : IsCompact K) :
    {c : F | algebraMap F (AdeleRing (𝓞 F) F) c ∈ K}.Finite := by
  obtain ⟨U, hU, hUF⟩ := _root_.GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero F
  have hsub : Filter.Tendsto (fun p : AdeleRing (𝓞 F) F × AdeleRing (𝓞 F) F => p.1 - p.2)
      (𝓝 (0, 0)) (𝓝 0) :=
    (continuous_fst.sub continuous_snd).tendsto' _ _ (by simp)
  have hpre : (fun p : AdeleRing (𝓞 F) F × AdeleRing (𝓞 F) F => p.1 - p.2) ⁻¹' U ∈
      𝓝 ((0 : AdeleRing (𝓞 F) F), (0 : AdeleRing (𝓞 F) F)) := hsub hU
  rw [nhds_prod_eq] at hpre
  obtain ⟨V, hV, W, hW, hVW⟩ := Filter.mem_prod_iff.mp hpre
  have hVU : ∀ v ∈ V ∩ W, ∀ w ∈ V ∩ W, v - w ∈ U := fun v hv w hw =>
    hVW (Set.mk_mem_prod hv.1 hw.2)
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun k => {y | y - k ∈ V ∩ W}) fun k _ =>
    (continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds
      (by simpa using Filter.inter_mem hV hW)
  refine (t.finite_toSet.biUnion
    (t := fun k => {c : F | algebraMap F (AdeleRing (𝓞 F) F) c - k ∈ V ∩ W})
    fun k _ => ?_).subset fun c hc => ?_
  · refine Set.Subsingleton.finite fun c hc c' hc' => ?_
    have := hUF (c - c') (by simpa [map_sub] using hVU _ hc _ hc')
    exact sub_eq_zero.mp this
  · simpa using ht hc


open NumberField Topology in
open scoped TensorProduct in
theorem _root_.GlobalTheory.RegSSLattice.tensorLattice : _root_.GlobalTheory.RegSS.TensorLattice := by
  unfold _root_.GlobalTheory.RegSS.TensorLattice
  intro F B _ _ _ _ _
  haveI := _root_.GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := _root_.GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI := _root_.GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  obtain ⟨U, hU, hUF⟩ := _root_.GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero F
  haveI : Nontrivial (AdeleRing (𝓞 F) F) := ⟨⟨0, 1, fun h01 => one_ne_zero
    (hUF 1 (by rw [map_one, ← h01]; exact mem_of_mem_nhds hU))⟩⟩
  letI : Algebra (AdeleRing (𝓞 F) F) (B ⊗[F] AdeleRing (𝓞 F) F) :=
    Algebra.TensorProduct.rightAlgebra
  letI : TopologicalSpace (B ⊗[F] AdeleRing (𝓞 F) F) := _root_.Formalism.BasicNotions.tensTopL (AdeleRing (𝓞 F) F)
  haveI : IsModuleTopology (AdeleRing (𝓞 F) F) (B ⊗[F] AdeleRing (𝓞 F) F) := ⟨rfl⟩
  haveI : ContinuousAdd (B ⊗[F] AdeleRing (𝓞 F) F) :=
    IsModuleTopology.toContinuousAdd (AdeleRing (𝓞 F) F) _
  let b := Module.finBasis F B
  let c : B ⊗[F] AdeleRing (𝓞 F) F ≃ₗ[AdeleRing (𝓞 F) F] AdeleRing (𝓞 F) F ⊗[F] B :=
    { TensorProduct.comm F B (AdeleRing (𝓞 F) F) with
      map_smul' := fun a t => by
        induction t using TensorProduct.induction_on with
        | zero => simp
        | tmul x y =>
          change TensorProduct.comm F B _ (a • (x ⊗ₜ y)) = a • TensorProduct.comm F B _ (x ⊗ₜ y)
          rw [Algebra.smul_def]
          simp [Algebra.TensorProduct.right_algebraMap_apply, TensorProduct.smul_tmul', mul_comm]
        | add x y hx hy => simp_all [smul_add] }
  let e := c.trans (Algebra.TensorProduct.basis (AdeleRing (𝓞 F) F) b).equivFun
  haveI : Module.Finite (AdeleRing (𝓞 F) F) (B ⊗[F] AdeleRing (𝓞 F) F) :=
    Module.Finite.of_basis ((Algebra.TensorProduct.basis (AdeleRing (𝓞 F) F) b).map c.symm)
  let h : B ⊗[F] AdeleRing (𝓞 F) F ≃L[AdeleRing (𝓞 F) F]
      (Fin (Module.finrank F B) → AdeleRing (𝓞 F) F) :=
    { e with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }
  have he : ∀ β : B, h (_root_.Formalism.UG.inclE (AdeleRing (𝓞 F) F) β) =
      fun i => algebraMap F (AdeleRing (𝓞 F) F) (b.equivFun β i) := by
    intro β
    ext i
    show e (β ⊗ₜ 1) i = _
    simp [e, c, Algebra.TensorProduct.basis_repr_tmul]
  refine ⟨IsModuleTopology.isTopologicalRing (AdeleRing (𝓞 F) F) _,
    h.toHomeomorph.isClosedEmbedding.locallyCompactSpace, h.toHomeomorph.isEmbedding.t2Space,
    h.toHomeomorph.secondCountableTopology, _root_.Formalism.UG.P.inclE_injective F B (AdeleRing (𝓞 F) F), ?_, ?_⟩
  · intro D hD
    have hD' : IsCompact (h '' D) := hD.image h.continuous
    refine ((Set.Finite.pi (t := fun i => {x : F | algebraMap F (AdeleRing (𝓞 F) F) x ∈
      (fun y => y i) '' (h '' D)}) fun i => finite_setOf_algebraMap_mem_of_isCompact F
        (hD'.image (continuous_apply i))).preimage b.equivFun.injective.injOn).subset ?_
    intro β hβ
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_setOf_eq]
    intro i
    exact ⟨h (_root_.Formalism.UG.inclE (AdeleRing (𝓞 F) F) β), ⟨_, hβ, rfl⟩, by rw [he]⟩
  · obtain ⟨K, hK, hKF⟩ := _root_.GlobalTheory.AdeleCocompact.exists_compact_adele F
    refine ⟨h.symm '' Set.univ.pi fun _ => K,
      (isCompact_univ_pi fun _ => hK).image h.symm.continuous, fun x => ?_⟩
    choose y hy using fun i => hKF (h x i)
    refine ⟨b.equivFun.symm y, h (x - _root_.Formalism.UG.inclE (AdeleRing (𝓞 F) F) (b.equivFun.symm y)), ?_,
      by simp⟩
    intro i _
    rw [map_sub, he, LinearEquiv.apply_symm_apply]
    simpa using hy i

end GlobalTheory.RegSSLattice
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteAlgebraAdelicLatticeProofStatement
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteAlgebraAdelicLattice_proof : GlobalTheory.RegSS.TensorLattice := by
  first | exact @GlobalTheory.RegSSLattice.tensorLattice | exact GlobalTheory.RegSSLattice.tensorLattice | (intros; apply GlobalTheory.RegSSLattice.tensorLattice <;> assumption)
end
end
