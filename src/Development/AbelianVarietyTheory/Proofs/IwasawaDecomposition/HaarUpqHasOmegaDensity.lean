module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqExpLocalChart
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KerThetaLocalizedEqSpanFontaineXiElement
public import Formalism.LocalToGlobal.Columns.GoodXgFin
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharOfIsPrimitiveRoot

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HaarUpqHasOmegaDensity
open Formalism.BasicNotions MeasureTheory Filter Topology Matrix

noncomputable section

namespace GlobalTheory.HaarDensityUpq

def toL1 (P Q : ℕ) : lieU P Q →ₗ[ℝ] PiLp 1 (fun _ : (Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q) => ℂ) where
  toFun X := WithLp.toLp 1 (entries (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem toL1_injective (P Q : ℕ) : Function.Injective (toL1 P Q) := by
  intro X Y h
  ext i j
  exact congrFun (congrArg WithLp.ofLp h) (i, j)

theorem isInducing_toL1 (P Q : ℕ) : IsInducing (toL1 P Q) := by
  have h1 : IsInducing (entries : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ → _) :=
    (Homeomorph.piCurry (X := Fin P ⊕ Fin Q) (Y := Fin P ⊕ Fin Q) (Z := ℂ)).symm.isInducing
  exact (PiLp.homeomorph 1 (fun _ : (Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q) => ℂ)).symm.isInducing.comp
    (h1.comp IsInducing.subtypeVal)

@[reducible] def sumNorm (P Q : ℕ) : NormedAddCommGroup (lieU P Q) :=
  let N := NormedAddCommGroup.induced (lieU P Q) _ (toL1 P Q) (toL1_injective P Q)
  { toNorm := N.toNorm
    toAddCommGroup := inferInstance
    toMetricSpace := N.toMetricSpace.replaceTopology (isInducing_toL1 P Q).eq_induced
    dist_eq := N.dist_eq }

theorem mat_mul {P Q : ℕ} (g h : UpqT P Q) : (g * h).mat = g.mat * h.mat := rfl

end GlobalTheory.HaarDensityUpq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CLTateInvariantsFiniteExtensionMem
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CLTateInvariantsFiniteExtensionMem
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem invariants_finExt : ∀ (l : ℕ) [Fact l.Prime], ∀ (K : FinExt l) (x : ℂ_[l]), (∀ g ∈ GK K, Per.σC g x = x) → ∃ y ∈ K.1, ((y : Om l) : ℂ_[l]) = x := by
  intro l _ K x hx
  have h := GlobalTheory.T.ax_sen_tate_complex_padic_fixed_closure l (GK K) x hx
  have hset : {y : Om l | ∀ g ∈ GK K, g y = y} = (K.1 : Set (Om l)) := by
    ext y
    have h1 := InfiniteGalois.fixedField_fixingSubgroup K.1
    constructor
    · intro hy
      have : y ∈ IntermediateField.fixedField K.1.fixingSubgroup := by
        rw [IntermediateField.mem_fixedField_iff]
        exact hy
      rwa [h1] at this
    · intro hy g hg
      exact (IntermediateField.mem_fixingSubgroup_iff K.1 g).1 hg y hy
  rw [hset] at h
  haveI : FiniteDimensional ℚ_[l] K.1 := K.2
  haveI : FiniteDimensional ℚ_[l] K.1.toSubalgebra.toSubmodule := K.2
  have hc : IsComplete (K.1 : Set (Om l)) :=
    Submodule.complete_of_finiteDimensional (𝕜 := ℚ_[l]) K.1.toSubalgebra.toSubmodule
  have hc2 : IsComplete ((fun y : Om l => (y : ℂ_[l])) '' (K.1 : Set (Om l))) :=
    (isComplete_image_iff (UniformSpace.Completion.isUniformInducing_coe (Om l))).2 hc
  rw [hc2.isClosed.closure_eq] at h
  obtain ⟨y, hy, rfl⟩ := h
  exact ⟨y, hy, rfl⟩

end GlobalTheory.MemLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CLTateInvariantsFiniteExtensionMemStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cLTate_invariants_finiteExtension_mem : ∀ (l : ℕ) [Fact l.Prime], ∀ (K : FinExt l) (x : ℂ_[l]), (∀ g ∈ GK K, Per.σC g x = x) → ∃ y ∈ K.1, ((y : Om l) : ℂ_[l]) = x := by
  first | exact @GlobalTheory.MemLoc.invariants_finExt | exact GlobalTheory.MemLoc.invariants_finExt | (intros; apply GlobalTheory.MemLoc.invariants_finExt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsIrrCharRealiseOfPrimitiveRootCard
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsIrrCharRealiseOfPrimitiveRootCard
open Formalism.L2.DIV

noncomputable section

namespace GlobalTheory.BrauerRealise

variable {G : Type} [Group G] [Fintype G]


omit [Fintype G] in
theorem isIrreducible_of_sum_char_mul_char_inv [Fintype G] {k : Type} [Field k] [CharZero k] {V : Type}
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] (ρ : Representation k G V)
    (h : ∑ x, ρ.character x * ρ.character x⁻¹ = (Nat.card G : k)) : ρ.IsIrreducible := by
  classical
  have hcard : (Nat.card G : k) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  letI : Invertible (Nat.card G : k) := invertibleOfNonzero hcard
  have h1 := Representation.card_inv_mul_sum_char_mul_char_eq_finrank ρ ρ
  rw [h, inv_mul_cancel₀ hcard] at h1
  have hfr : Module.finrank k (ρ.IntertwiningMap ρ) = 1 := by exact_mod_cast h1.symm
  have hnt : Nontrivial V := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    have h0 : ∀ g, ρ.character g = 0 := fun g => by
      rw [Representation.character, Subsingleton.elim (ρ g) 0, map_zero]
    simp only [h0, zero_mul, Finset.sum_const_zero] at h
    exact hcard h.symm
  let idI : ρ.IntertwiningMap ρ := ⟨LinearMap.id, fun g => by rw [LinearMap.id_comp, LinearMap.comp_id]⟩
  have hid0 : idI ≠ 0 := by
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    intro e
    exact hv (congrArg (fun φ : ρ.IntertwiningMap ρ => φ.toLinearMap v) e)
  have hcG : (Fintype.card G : k) ≠ 0 := by rw [← Nat.card_eq_fintype_card]; exact hcard
  refine { exists_pair_ne := ⟨⊥, ⊤, fun e => ?_⟩, eq_bot_or_eq_top := fun U => ?_ }
  · exact (top_ne_bot : (⊤ : Submodule k V) ≠ ⊥) (congrArg Subrepresentation.toSubmodule e).symm
  · by_cases hU : U.toSubmodule = ⊥
    · exact Or.inl (Subrepresentation.toSubmodule_injective hU)
    · right
      apply Subrepresentation.toSubmodule_injective
      show U.toSubmodule = ⊤
      obtain ⟨W0, hW0⟩ := Submodule.exists_isCompl U.toSubmodule
      let q : V →ₗ[k] V := U.toSubmodule.subtype ∘ₗ Submodule.projectionOnto U.toSubmodule W0 hW0
      have hqU : ∀ u ∈ U.toSubmodule, q u = u := fun u hu =>
        congrArg Subtype.val (Submodule.projectionOnto_apply_left hW0 ⟨u, hu⟩)
      have hqR : ∀ v, q v ∈ U.toSubmodule := fun v => (Submodule.projectionOnto _ _ hW0 v).2
      have hinv : ∀ g, ∀ v ∈ U.toSubmodule, ρ g v ∈ U.toSubmodule := fun g v hv => U.apply_mem_toSubmodule g hv
      have hρρ : ∀ g (v : V), ρ g (ρ g⁻¹ v) = v := fun g v => by
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      let P : V →ₗ[k] V := (Fintype.card G : k)⁻¹ • ∑ g : G, ρ g ∘ₗ q ∘ₗ ρ g⁻¹
      have hPv : ∀ v, P v = (Fintype.card G : k)⁻¹ • ∑ g : G, ρ g (q (ρ g⁻¹ v)) := fun v => by
        simp [P, LinearMap.sum_apply]
      have hPI : ∀ h, P ∘ₗ ρ h = ρ h ∘ₗ P := by
        intro h
        apply LinearMap.ext
        intro v
        set_option synthInstance.maxHeartbeats 100000 in
          rw [LinearMap.comp_apply, LinearMap.comp_apply, hPv, hPv, map_smul, map_sum]
        congr 1
        refine Fintype.sum_equiv (Equiv.mulLeft h⁻¹) _ _ (fun g => ?_)
        simp only [Equiv.coe_mulLeft, mul_inv_rev, inv_inv, map_mul, Module.End.mul_apply]
        rw [hρρ]
      obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' idI hid0).mp hfr ⟨P, hPI⟩
      have hcv : ∀ v, c • v = P v := fun v => congrArg (fun φ : ρ.IntertwiningMap ρ => φ.toLinearMap v) hc
      have hPU : ∀ u ∈ U.toSubmodule, P u = u := fun u hu => by
        rw [hPv]
        have : ∀ g : G, ρ g (q (ρ g⁻¹ u)) = u := fun g => by rw [hqU _ (hinv _ _ hu), hρρ]
        simp only [this, Finset.sum_const, Finset.card_univ]
        rw [← Nat.cast_smul_eq_nsmul k, smul_smul, inv_mul_cancel₀ hcG, one_smul]
      obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
      have hc1 : c = 1 := by
        have e1 := hcv u
        rw [hPU u hu] at e1
        have : (c - 1) • u = 0 := by rw [sub_smul, e1, one_smul, sub_self]
        rcases smul_eq_zero.mp this with h2 | h2
        · exact sub_eq_zero.mp h2
        · exact absurd h2 hu0
      rw [Submodule.eq_top_iff']
      intro v
      have e2 := hcv v
      rw [hc1, one_smul] at e2
      rw [e2, hPv]
      exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun g _ => hinv g _ (hqR _))

theorem character_eq_trace_toMatrix' {k : Type} [Field k] {n : ℕ} (ρ : Representation k G (Fin n → k)) (g : G) :
    ρ.character g = Matrix.trace (LinearMap.toMatrix' (ρ g)) := by
  rw [Representation.character, LinearMap.trace_eq_matrix_trace _ (Pi.basisFun _ (Fin n)),
    LinearMap.toMatrix_eq_toMatrix']

def mapScalars {K k : Type} [Field K] [Field k] (f : K →+* k) {n : ℕ} (ρ : Representation K G (Fin n → K)) :
    Representation k G (Fin n → k) :=
  (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) k ≃ₐ[k] Module.End k (Fin n → k)).toRingEquiv.toMonoidHom.comp
    ((f.mapMatrix : Matrix (Fin n) (Fin n) K →+* Matrix (Fin n) (Fin n) k).toMonoidHom.comp
      ((LinearMap.toMatrixAlgEquiv' : Module.End K (Fin n → K) ≃ₐ[K] Matrix (Fin n) (Fin n) K).toRingEquiv.toMonoidHom.comp ρ))

theorem character_mapScalars {K k : Type} [Field K] [Field k] (f : K →+* k) {n : ℕ}
    (ρ : Representation K G (Fin n → K)) (g : G) : (mapScalars f ρ).character g = f (ρ.character g) := by
  rw [character_eq_trace_toMatrix', character_eq_trace_toMatrix']
  set_option synthInstance.maxHeartbeats 100000 in
    simp [mapScalars, Matrix.trace, Matrix.diag, map_sum]

theorem absIrr_realise_of_isPrimitiveRoot {K : Type} [Field K] (σ : K →+* ℂ) (z : K)
    (hz : IsPrimitiveRoot z (Fintype.card G)) (ψ : G → ℂ) (hψ : ψ ∈ Formalism.L2.Col.gxIrrSet (G := G) ℂ) :
    ∃ χ : G → K, IsAbsIrrChar χ ∧ ∀ g, σ (χ g) = ψ g := by
  classical
  haveI : CharZero K := σ.charZero
  letI : Algebra K ℂ := σ.toAlgebra
  have hψC : GlobalTheory.BI.IsChar ℂ ℂ ψ := by
    obtain ⟨n, ρ, -, hρ⟩ := hψ
    exact ⟨n, ρ, fun g => by rw [← hρ]; rfl⟩
  obtain ⟨m, τ, hτ⟩ := GlobalTheory.BI.isChar_of_isPrimitiveRoot K ℂ (Fintype.card G) z Fintype.card_ne_zero hz G
    (fun g => pow_card_eq_one) ψ hψC
  have hτσ : ∀ g, σ (τ.character g) = ψ g := fun g => (hτ g).symm
  refine ⟨τ.character, ?_, hτσ⟩
  let A := AlgebraicClosure K
  let ρ' : Representation A G (Fin m → A) := mapScalars (algebraMap K A) τ
  have hch : ∀ g, ρ'.character g = algebraMap K A (τ.character g) := character_mapScalars _ τ
  refine ⟨m, ρ', isIrreducible_of_sum_char_mul_char_inv ρ' ?_, hch⟩
  have horth := Formalism.L2.Col.gx_orth (G := G) (k := ℂ) hψ hψ
  rw [if_pos rfl] at horth
  have hcardC : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hsumC : ∑ g, ψ g * ψ g⁻¹ = (Nat.card G : ℂ) := by
    rw [← mul_one (Nat.card G : ℂ), ← horth, ← mul_assoc, mul_inv_cancel₀ hcardC, one_mul]
  have hsumK : ∑ g, τ.character g * τ.character g⁻¹ = (Nat.card G : K) := by
    apply σ.injective
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_natCast, ← hsumC]
    exact Finset.sum_congr rfl fun g _ => by rw [map_mul, hτσ, hτσ]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hch, ← map_mul, ← map_sum, hsumK, map_natCast]

end GlobalTheory.BrauerRealise
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsIrrCharRealiseOfPrimitiveRootCardStatement
open Formalism.L2.DIV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absIrrChar_realise_of_primitiveRoot_card : ∀ {G : Type} [inst : Group G] [inst_1 : Fintype G] {K : Type} [inst_2 : Field K] (σ : K →+* ℂ) (z : K), IsPrimitiveRoot z (Fintype.card G) → ∀ (ψ : G → ℂ), ψ ∈ Formalism.L2.Col.gxIrrSet (G := G) ℂ → ∃ χ : G → K, IsAbsIrrChar χ ∧ ∀ g, σ (χ g) = ψ g := by
  first | exact @GlobalTheory.BrauerRealise.absIrr_realise_of_isPrimitiveRoot | exact GlobalTheory.BrauerRealise.absIrr_realise_of_isPrimitiveRoot | (intros; apply GlobalTheory.BrauerRealise.absIrr_realise_of_isPrimitiveRoot <;> assumption)
end
end
