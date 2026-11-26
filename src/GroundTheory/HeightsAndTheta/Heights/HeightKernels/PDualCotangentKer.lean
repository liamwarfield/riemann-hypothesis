module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedExcLead
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStackedExcGeoFirst

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualCotangentKer
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField Matrix

noncomputable section

namespace DualCotangentKernel

variable {K : Type} [Field K] [NumberField K] {i : ℕ}

theorem smul_mem (F : HermLattice K i) (μ : 𝓞 K) {φ : Fin i → K} (hφ : φ ∈ dualLattice F) :
    (algebraMap (𝓞 K) K μ) • φ ∈ dualLattice F := by
  intro x hx
  rw [smul_dotProduct, smul_eq_mul]
  obtain ⟨r, hr⟩ := hφ x hx
  exact ⟨μ * r, by rw [map_mul, hr]⟩

def mulMap (F : HermLattice K i) (c : 𝓞 K) : dualLattice F →ₗ[ℤ] dualLattice F where
  toFun χ := ⟨algebraMap (𝓞 K) K c • (χ : Fin i → K), smul_mem F c χ.2⟩
  map_add' χ χ' := by ext1; simp [smul_add]
  map_smul' n χ := by
    ext1
    show algebraMap (𝓞 K) K c • ((n • χ : dualLattice F) : Fin i → K) =
      n • (algebraMap (𝓞 K) K c • (χ : Fin i → K))
    rw [Submodule.coe_smul, smul_comm]

def prodSet (F : HermLattice K i) {k : Type} [Field k] (ρ : 𝓞 K →+* k) : Set (dualLattice F) :=
  {v | ∃ (μ : 𝓞 K) (φ : dualLattice F), ρ μ = 0 ∧
    (v : Fin i → K) = algebraMap (𝓞 K) K μ • (φ : Fin i → K)}

theorem mulMap_mem (F : HermLattice K i) {k : Type} [Field k] (ρ : 𝓞 K →+* k) (c : 𝓞 K)
    {χ : dualLattice F} (hχ : χ ∈ Submodule.span ℤ (prodSet F ρ)) :
    mulMap F c χ ∈ Submodule.span ℤ (prodSet F ρ) := by
  have hle : Submodule.span ℤ (prodSet F ρ) ≤ (Submodule.span ℤ (prodSet F ρ)).comap (mulMap F c) := by
    rw [Submodule.span_le]
    rintro v ⟨μ, φ, hμ, hv⟩
    refine Submodule.subset_span ⟨c * μ, φ, by rw [map_mul, hμ, mul_zero], ?_⟩
    show algebraMap (𝓞 K) K c • (v : Fin i → K) = _
    rw [hv, smul_smul, ← map_mul]
  exact hle hχ

end DualCotangentKernel


open DualCotangentKernel in
theorem DualCotangentKer.proof : DualCotangentKer.Statement := by
  intro K _ _ i F T _ _b k _ ρ σ hρ hσ hsl ψ hψ
  classical
  change ψ ∈ Submodule.span ℤ (prodSet F ρ)

  choose φ hφ using fun j : Fin i => hσ (Pi.single j 1)
  let w : Option (Fin i) → dualLattice F := fun o => o.elim ψ φ

  have hdep : ¬ LinearIndependent K (fun o => (w o : Fin i → K)) := by
    intro h
    have := h.fintype_card_le_finrank
    rw [Fintype.card_option, Fintype.card_fin, Module.finrank_fin_fun] at this
    omega
  obtain ⟨g, hg, o, ho⟩ := Fintype.not_linearIndependent_iff.mp hdep
  have hJ : RingHom.ker ρ ≠ ⊤ := RingHom.ker_ne_top ρ
  obtain ⟨a, hint, o', -, hnot⟩ :=
    Ideal.exist_integer_multiples_notMem (A := 𝓞 K) (K := K) hJ Finset.univ g (Finset.mem_univ o) ho
  choose c hc using fun x => hint x (Finset.mem_univ x)

  let χ : Option (Fin i) → dualLattice F := fun x => mulMap F (c x) (w x)
  have hsum : ∑ x, χ x = 0 := by
    ext1
    rw [Submodule.coe_sum, Submodule.coe_zero]
    calc ∑ x, ((χ x : dualLattice F) : Fin i → K) = ∑ x, algebraMap (𝓞 K) K (c x) • (w x : Fin i → K) := rfl
      _ = a • ∑ x, g x • (w x : Fin i → K) := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [hc x, smul_smul]
      _ = 0 := by rw [hg, smul_zero]
  have hσχ : ∀ x, σ (χ x) = ρ (c x) • σ (w x) := fun x => hsl (c x) (w x) (χ x) rfl
  have hσsum : ∑ x, ρ (c x) • σ (w x) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_zero σ, ← hsum, map_sum]
    exact Finset.sum_congr rfl fun x _ => (hσχ x).symm

  have hsome : ∀ j, ρ (c (some j)) = 0 := by
    intro j
    have h := congrFun hσsum j
    rw [Fintype.sum_option] at h
    simp only [w, Option.elim_none, Option.elim_some, hψ, smul_zero, zero_add, hφ, Finset.sum_apply,
      Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Pi.zero_apply] at h
    rw [Finset.sum_ite_eq] at h
    simpa using h
  have hnone : ρ (c none) ≠ 0 := by
    intro h0
    apply hnot
    rw [FractionalIdeal.mem_coeIdeal]
    refine ⟨c o', ?_, hc o'⟩
    rw [RingHom.mem_ker]
    cases o' with
    | none => exact h0
    | some j => exact hsome j

  have hgen : ∀ j, χ (some j) ∈ Submodule.span ℤ (prodSet F ρ) := fun j =>
    Submodule.subset_span ⟨c (some j), φ j, hsome j, rfl⟩
  have hχ0 : χ none ∈ Submodule.span ℤ (prodSet F ρ) := by
    have h : χ none = -∑ j, χ (some j) := by
      rw [Fintype.sum_option] at hsum
      exact eq_neg_of_add_eq_zero_left hsum
    rw [h]
    exact neg_mem (Submodule.sum_mem _ fun j _ => hgen j)

  obtain ⟨bb, hbb⟩ := hρ (ρ (c none))⁻¹
  have hm : ρ (bb * c none - 1) = 0 := by
    rw [map_sub, map_mul, hbb, inv_mul_cancel₀ hnone, map_one, sub_self]
  have h1 : mulMap F bb (χ none) ∈ Submodule.span ℤ (prodSet F ρ) := mulMap_mem F ρ bb hχ0
  have h2 : mulMap F (bb * c none - 1) ψ ∈ Submodule.span ℤ (prodSet F ρ) :=
    Submodule.subset_span ⟨_, ψ, hm, rfl⟩
  have hψeq : ψ = mulMap F bb (χ none) - mulMap F (bb * c none - 1) ψ := by
    ext1
    simp only [χ, w, Option.elim_none, mulMap, LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_sub,
      smul_smul, ← map_mul, ← sub_smul, map_sub, map_one]
    rw [sub_sub_cancel, one_smul]
  rw [hψeq]
  exact sub_mem h1 h2

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStackedExcResidueExists
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField StackedExceptionalFirstGeometric

noncomputable section

namespace StackedExceptionalResidueExists

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F F' : HermLattice K i}

theorem exists_mem_not_mem (hlt : F'.lattice < F.lattice) :
    ∃ φc ∈ dualLattice F', φc ∉ dualLattice F := by
  by_contra! h
  have h1 : (dualLattice F).toAddSubgroup.relIndex (dualLattice F').toAddSubgroup = 1 :=
    AddSubgroup.relIndex_eq_one.mpr fun φ hφ => h φ hφ
  rw [DualLatticeIndex.proof K i F F' hlt.le] at h1
  have h2 := AddSubgroup.relIndex_eq_one.mp h1
  exact hlt.not_ge fun x hx => h2 hx

def annIdeal (F : HermLattice K i) (φc : Fin i → K) : Ideal (𝓞 K) where
  carrier := {μ | algebraMap (𝓞 K) K μ • φc ∈ dualLattice F}
  add_mem' {a b} ha hb := by
    show algebraMap (𝓞 K) K (a + b) • φc ∈ dualLattice F
    rw [map_add (f := _), add_smul]
    exact add_mem ha hb
  zero_mem' := by
    show algebraMap (𝓞 K) K 0 • φc ∈ dualLattice F
    rw [map_zero, zero_smul]
    exact zero_mem _
  smul_mem' c x hx := by
    show algebraMap (𝓞 K) K (c * x) • φc ∈ dualLattice F
    rw [map_mul, mul_smul]
    exact smul_mem_dual F c hx

theorem mem_annIdeal {φc : Fin i → K} {μ : 𝓞 K} :
    μ ∈ annIdeal F φc ↔ algebraMap (𝓞 K) K μ • φc ∈ dualLattice F := Iff.rfl

theorem annIdeal_isMaximal (hlt : F'.lattice < F.lattice)
    (hcov : ∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice)
    {φc : Fin i → K} (hc : φc ∈ dualLattice F') (hc' : φc ∉ dualLattice F) : (annIdeal F φc).IsMaximal := by
  rw [Ideal.isMaximal_iff]
  refine ⟨fun h => hc' ?_, fun J x hle hx hxJ => ?_⟩
  · have := mem_annIdeal.mp h
    rwa [map_one, one_smul] at this
  obtain ⟨l, hl⟩ := exists_sub_mem_dual hlt hcov (smul_mem_dual F' x hc) (mem_annIdeal.not.mp hx) hc
  have h1 : 1 - l * x ∈ annIdeal F φc := by
    rw [mem_annIdeal, map_sub, map_one, map_mul, sub_smul, one_smul, mul_smul]
    exact hl
  have h2 := J.add_mem (hle h1) (J.mul_mem_left l hxJ)
  rwa [sub_add_cancel] at h2

theorem mk_eq_of {φc φ : Fin i → K} {l l' : 𝓞 K} (h : φ - algebraMap (𝓞 K) K l • φc ∈ dualLattice F)
    (h' : φ - algebraMap (𝓞 K) K l' • φc ∈ dualLattice F) :
    Ideal.Quotient.mk (annIdeal F φc) l = Ideal.Quotient.mk (annIdeal F φc) l' := by
  rw [Ideal.Quotient.eq, mem_annIdeal, map_sub, sub_smul]
  have e : algebraMap (𝓞 K) K l • φc - algebraMap (𝓞 K) K l' • φc =
      (φ - algebraMap (𝓞 K) K l' • φc) - (φ - algebraMap (𝓞 K) K l • φc) := by abel
  rw [e]
  exact sub_mem h' h

def coeff (hlt : F'.lattice < F.lattice)
    (hcov : ∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice)
    {φc : Fin i → K} (hc : φc ∈ dualLattice F') (hc' : φc ∉ dualLattice F) (φ : dualLattice F') : 𝓞 K :=
  (exists_sub_mem_dual hlt hcov hc hc' φ.2).choose

theorem coeff_spec (hlt : F'.lattice < F.lattice)
    (hcov : ∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice)
    {φc : Fin i → K} (hc : φc ∈ dualLattice F') (hc' : φc ∉ dualLattice F) (φ : dualLattice F') :
    (φ : Fin i → K) - algebraMap (𝓞 K) K (coeff hlt hcov hc hc' φ) • φc ∈ dualLattice F :=
  (exists_sub_mem_dual hlt hcov hc hc' φ.2).choose_spec

def rhoDual (hlt : F'.lattice < F.lattice)
    (hcov : ∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice)
    {φc : Fin i → K} (hc : φc ∈ dualLattice F') (hc' : φc ∉ dualLattice F) :
    dualLattice F' →+ 𝓞 K ⧸ annIdeal F φc where
  toFun φ := Ideal.Quotient.mk _ (coeff hlt hcov hc hc' φ)
  map_zero' := by
    rw [← map_zero (Ideal.Quotient.mk (annIdeal F φc))]
    refine mk_eq_of (coeff_spec hlt hcov hc hc' 0) ?_
    rw [map_zero, zero_smul, sub_zero]
    exact zero_mem _
  map_add' φ ψ := by
    rw [← map_add (f := _)]
    refine mk_eq_of (coeff_spec hlt hcov hc hc' (φ + ψ)) ?_
    have e : ((φ + ψ : dualLattice F') : Fin i → K) - algebraMap (𝓞 K) K
        (coeff hlt hcov hc hc' φ + coeff hlt hcov hc hc' ψ) • φc =
        ((φ : Fin i → K) - algebraMap (𝓞 K) K (coeff hlt hcov hc hc' φ) • φc) +
        ((ψ : Fin i → K) - algebraMap (𝓞 K) K (coeff hlt hcov hc hc' ψ) • φc) := by
      rw [Submodule.coe_add, map_add (f := _), add_smul]
      abel
    rw [e]
    exact add_mem (coeff_spec hlt hcov hc hc' φ) (coeff_spec hlt hcov hc hc' ψ)

theorem rhoDual_eq (hlt : F'.lattice < F.lattice)
    (hcov : ∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice)
    {φc : Fin i → K} (hc : φc ∈ dualLattice F') (hc' : φc ∉ dualLattice F) (φ : dualLattice F') (l : 𝓞 K)
    (h : (φ : Fin i → K) - algebraMap (𝓞 K) K l • φc ∈ dualLattice F) :
    rhoDual hlt hcov hc hc' φ = Ideal.Quotient.mk _ l :=
  mk_eq_of (coeff_spec hlt hcov hc hc' φ) h

end StackedExceptionalResidueExists


open StackedExceptionalResidueExists in
theorem DualStackedExcResidueExists.proof (hσ : DualLatticeModPrime.Statement) :
    DualStackedExcResidueExists.Statement := by
  intro K _ _ i F F' T _ _ b b' a _ hlt hcov _
  obtain ⟨φc, hc, hc'⟩ := exists_mem_not_mem hlt
  set 𝔭 := annIdeal F φc with h𝔭
  have hmax : 𝔭.IsMaximal := annIdeal_isMaximal hlt hcov hc hc'
  let _ : Field (𝓞 K ⧸ 𝔭) := Ideal.Quotient.field 𝔭
  obtain ⟨σ, hσs, hσl⟩ := hσ K i F 𝔭 hmax
  set ρ' := rhoDual hlt hcov hc hc' with hρ'
  have hker : ∀ φ : dualLattice F', ρ' φ = 0 ↔ (φ : Fin i → K) ∈ dualLattice F := by
    intro φ
    have hs := coeff_spec hlt hcov hc hc' φ
    change Ideal.Quotient.mk 𝔭 (coeff hlt hcov hc hc' φ) = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem, mem_annIdeal]
    constructor
    · intro h
      have := add_mem hs h
      rwa [sub_add_cancel] at this
    · intro h
      have := sub_mem h hs
      rwa [sub_sub_cancel] at this
  have hsurj : Function.Surjective ρ' := by
    intro x
    obtain ⟨l, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨⟨algebraMap (𝓞 K) K l • φc, smul_mem_dual F' l hc⟩, rhoDual_eq hlt hcov hc hc' _ l ?_⟩
    show algebraMap (𝓞 K) K l • φc - algebraMap (𝓞 K) K l • φc ∈ dualLattice F
    rw [sub_self]
    exact zero_mem _
  have hcard : Nat.card (𝓞 K ⧸ 𝔭) = F'.lattice.toAddSubgroup.relIndex F.lattice.toAddSubgroup := by
    rw [← DualLatticeIndex.proof K i F F' hlt.le]
    have hk : (dualLattice F).toAddSubgroup.addSubgroupOf (dualLattice F').toAddSubgroup = ρ'.ker := by
      ext φ
      rw [AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_ker, hker]
      rfl
    rw [AddSubgroup.relIndex, hk, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr hsurj]
    exact (Nat.card_congr (Equiv.Set.univ _)).symm
  refine ⟨𝓞 K ⧸ 𝔭, inferInstance, Fintype.ofFinite _, fun t => ρ' (b' t), fun t => σ (b t),
    ⟨Ideal.Quotient.mk 𝔭, ρ', σ, Ideal.Quotient.mk_surjective, hsurj, hσs, hker, ?_, hσl,
      fun t => rfl, fun t => rfl⟩, ?_⟩
  · intro μ φ ψ h
    rw [rhoDual_eq hlt hcov hc hc' ψ (μ * coeff hlt hcov hc hc' φ), map_mul]
    · rfl
    rw [h, map_mul, mul_smul, ← smul_sub]
    exact smul_mem_dual F μ (coeff_spec hlt hcov hc hc' φ)
  · rw [← hcard]
    exact Fintype.card_eq_nat_card

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualTopBasisChange
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial NumberField

noncomputable section

namespace TopDualBasisChange

theorem hermLine_ext {ι : Unit → Type} [∀ k, Fintype (ι k)] {A B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι}
    (ha : A.a = B.a) (hh : A.h = B.h) : A = B := by
  cases A
  cases B
  cases ha
  cases hh
  rfl

variable {T T₂ : Type} [Fintype T] [DecidableEq T] [Fintype T₂] [DecidableEq T₂]


omit [DecidableEq T₂] in
theorem subst_subst {A : Matrix T T₂ ℤ} {B : Matrix T₂ T ℤ} (hAB : A * B = 1) (f : MRing (dualBlocks T)) :
    intCoordSubst A (intCoordSubst B f) = f := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    show intCoordSubst A (intCoordSubst B (algebraMap ℤ _ a)) = algebraMap ℤ _ a
    rw [AlgHom.commutes, AlgHom.commutes]
  | add f g hf hg => rw [map_add (f := _), map_add (f := _), hf, hg]
  | mul_X f p hf =>
    rw [map_mul, map_mul, hf]
    congr 1
    obtain ⟨⟨⟩, t⟩ := p
    have hC : ∀ a : ℤ, (C a : MRing (dualBlocks T)) = (a : MRing (dualBlocks T)) := fun a => map_intCast C a
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [intCoordSubst, aeval_X, map_sum, map_mul, eq_intCast, hC, map_intCast, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [← mul_assoc, ← Int.cast_mul, ← Finset.sum_mul, ← Int.cast_sum]
    have h1 : ∀ x : T, ∑ s, B s t * A x s = (A * B) x t := by
      intro x
      simp [Matrix.mul_apply, mul_comm]
    simp_rw [h1, hAB, Matrix.one_apply]
    simp

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F : HermLattice K i}


omit [DecidableEq T] [Fintype T₂] [DecidableEq T₂] in
theorem basis_coe (b : Module.Basis T ℤ (dualLattice F)) (b₂ : Module.Basis T₂ ℤ (dualLattice F))
    (s : T₂) (j : Fin i) :
    (b₂ s : Fin i → K) j = ∑ t, (b.toMatrix b₂ t s : K) * (b t : Fin i → K) j := by
  have h := congrArg (fun φ : dualLattice F => (φ : Fin i → K) j) (b.sum_toMatrix_smul_self b₂ s)
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, zsmul_eq_mul] at h
  exact h.symm


omit [DecidableEq T] [Fintype T₂] [DecidableEq T₂] in
theorem coord_change {A : Matrix T T₂ ℤ} {b : Module.Basis T ℤ (dualLattice F)}
    {b₂ : Module.Basis T₂ ℤ (dualLattice F)}
    (hA : ∀ s j, (b₂ s : Fin i → K) j = ∑ t, (A t s : K) * (b t : Fin i → K) j) (s : T₂) :
    dualLatticeCoord b₂ ⟨(), s⟩ = ∑ t, (A t s : ProjField K i) * dualLatticeCoord b ⟨(), t⟩ := by
  have h : (∑ j, C ((b₂ s : Fin i → K) j) * X j : MvPolynomial (Fin i) K) =
      ∑ t, (A t s : MvPolynomial (Fin i) K) * ∑ j, C ((b t : Fin i → K) j) * X j := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hA, map_sum, map_mul, map_intCast, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun t _ => ?_
    ring
  simp only [dualLatticeCoord]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_mul, map_intCast]


omit [DecidableEq T] [Fintype T₂] [DecidableEq T₂] in
theorem coneMap_subst {A : Matrix T T₂ ℤ} {b : Module.Basis T ℤ (dualLattice F)}
    {b₂ : Module.Basis T₂ ℤ (dualLattice F)}
    (hA : ∀ s j, (b₂ s : Fin i → K) j = ∑ t, (A t s : K) * (b t : Fin i → K) j)
    (f : MRing (dualBlocks T₂)) :
    mConeMap (dualLatticeCoord b) (intCoordSubst A f) = mConeMap (dualLatticeCoord b₂) f := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    have hC₂ : ∀ a : ℤ, (C a : MRing (dualBlocks T₂)) = (a : MRing (dualBlocks T₂)) := fun a => map_intCast C a
    rw [hC₂, map_intCast, map_intCast, map_intCast]
  | add f g hf hg => rw [map_add (f := _), map_add (f := _), map_add (f := _), hf, hg]
  | mul_X f p hf =>
    rw [map_mul, map_mul, map_mul, hf]
    congr 1
    obtain ⟨⟨⟩, s⟩ := p
    have hC : ∀ a : ℤ, (C a : MRing (dualBlocks T)) = (a : MRing (dualBlocks T)) := fun a => map_intCast C a
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [intCoordSubst, aeval_X, map_sum, map_mul, hC, map_intCast, mConeMap, coord_change hA s,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [mul_assoc]


omit [DecidableEq T₂] in
theorem ideal_map {A : Matrix T T₂ ℤ} {B : Matrix T₂ T ℤ} (hAB : A * B = 1)
    {b : Module.Basis T ℤ (dualLattice F)} {b₂ : Module.Basis T₂ ℤ (dualLattice F)}
    (hA : ∀ s j, (b₂ s : Fin i → K) j = ∑ t, (A t s : K) * (b t : Fin i → K) j) :
    (dualIdeal b₂).map (intCoordSubst A) = dualIdeal b := by
  have hsurj : Function.Surjective (intCoordSubst A) := fun f => ⟨intCoordSubst B f, subst_subst hAB f⟩
  have hker : dualIdeal b₂ = (dualIdeal b).comap (intCoordSubst A) := by
    ext f
    simp only [dualIdeal, mCoordIdeal, Ideal.mem_comap, RingHom.mem_ker, coneMap_subst hA]
  rw [hker, Ideal.map_comap_of_surjective _ hsurj]


omit [DecidableEq T] [Fintype T₂] [DecidableEq T₂] in
theorem embMatrix_apply {A : Matrix T T₂ ℤ} {b : Module.Basis T ℤ (dualLattice F)}
    {b₂ : Module.Basis T₂ ℤ (dualLattice F)}
    (hA : ∀ s j, (b₂ s : Fin i → K) j = ∑ t, (A t s : K) * (b t : Fin i → K) j)
    (s : T₂) (p : (K →+* ℂ) × Fin i) :
    dualEmbMatrix b₂ s p = ∑ t, (A t s : ℂ) * dualEmbMatrix b t p := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dualEmbMatrix, hA, map_sum, map_mul, map_intCast]


omit [DecidableEq T] [Fintype T₂] [DecidableEq T₂] in
theorem recover_eq {A : Matrix T T₂ ℤ} {b : Module.Basis T ℤ (dualLattice F)}
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b)))
    {b₂ : Module.Basis T₂ ℤ (dualLattice F)}
    (hb₂ : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b₂)))
    (hA : ∀ s j, (b₂ s : Fin i → K) j = ∑ t, (A t s : K) * (b t : Fin i → K) j)
    (z : (Σ _ : Unit, T) → ℂ) :
    dualRecover b₂ hb₂ (fun s => intCoordPt A z ⟨(), s⟩) = dualRecover b hb (fun t => z ⟨(), t⟩) := by
  rw [dualRecover, LinearEquiv.symm_apply_eq]
  set w := dualRecover b hb (fun t => z ⟨(), t⟩)
  have hw : Matrix.mulVecLin (dualEmbMatrix b) w = fun t => z ⟨(), t⟩ := by
    simp only [w, dualRecover]
    exact LinearEquiv.apply_symm_apply (LinearEquiv.ofBijective _ hb) _
  funext s
  rw [LinearEquiv.ofBijective_apply, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
  simp only [embMatrix_apply hA, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [intCoordPt]
  refine Finset.sum_congr rfl fun t _ => ?_
  have ht := congrFun hw t
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct] at ht
  rw [← ht, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring


omit [DecidableEq T₂] in
theorem line_eq {A : Matrix T T₂ ℤ} {b : Module.Basis T ℤ (dualLattice F)}
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b)))
    {b₂ : Module.Basis T₂ ℤ (dualLattice F)}
    (hb₂ : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b₂)))
    (hA : ∀ s j, (b₂ s : Fin i → K) j = ∑ t, (A t s : K) * (b t : Fin i → K) j)
    (hAB : ∃ B : Matrix T₂ T ℤ, A * B = 1) :
    intCoordLine A hAB (dualLine F b₂ hb₂) = dualLine F b hb := by
  refine hermLine_ext rfl (funext fun z => ?_)
  show Real.sqrt (dualNormSq b₂ hb₂ fun s => intCoordPt A z ⟨(), s⟩) =
    Real.sqrt (dualNormSq b hb fun t => z ⟨(), t⟩)
  simp only [dualNormSq, recover_eq hb hb₂ hA z]

end TopDualBasisChange


open TopDualBasisChange in
theorem DualTopBasisChange.proof (hChange : IntCoordChange.Statement) : DualTopBasisChange.Statement := by
  intro K _ _ i F T T₂ _ _ _ _ b hb b₂ hb₂ II hi hII
  have hAB : b.toMatrix b₂ * b₂.toMatrix b = 1 := Module.Basis.toMatrix_mul_toMatrix_flip b b₂
  have hBA : b₂.toMatrix b * b.toMatrix b₂ = 1 := Module.Basis.toMatrix_mul_toMatrix_flip b₂ b
  have h := hChange T T₂ (b.toMatrix b₂) (b₂.toMatrix b) hAB hBA II hII (dualIdeal b₂) i
    (fun _ => dualLine F b₂ hb₂) hi (DualArithVar.full K i F T₂ b₂ hi)
    (fun _ => (DualLineSemipositive.proof K i F T₂ b₂ hb₂).1)
  rw [ideal_map hAB (basis_coe b b₂), line_eq hb hb₂ (basis_coe b b₂)] at h
  exact h.symm

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsIntCoordGeoNum
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable section

def IntCoordGeoNum.Statement : Prop :=
  ∀ (T T₂ : Type) [Fintype T] [DecidableEq T] [Fintype T₂] [DecidableEq T₂] (A : Matrix T T₂ ℤ)
    (B : Matrix T₂ T ℤ), A * B = 1 → B * A = 1 →
    ∀ (V : Ideal (MRing (dualBlocks T))) (n p : ℕ), IsMultiProjPrime V → p.Prime →
      (C (p : ℤ) : MRing (dualBlocks T)) ∈ V →
      ringKrullDim (MRing (dualBlocks T) ⧸ V) = ((n + Fintype.card Unit : ℕ) : WithBot ℕ∞) →
      ∀ a : Fin n → Unit → ℤ, geoNum n (V.comap (intCoordSubst A)) a = geoNum n V a

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsIntCoordArInt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable section

def IntCoordArInt.Statement : Prop :=
  ∀ (T T₂ : Type) [Fintype T] [DecidableEq T] [Fintype T₂] [DecidableEq T₂] (A : Matrix T T₂ ℤ)
    (B : Matrix T₂ T ℤ) (_ : A * B = 1) (hBA : B * A = 1) (Q : Ideal (MRing (dualBlocks T))) (e : ℕ)
    (L : Fin e → ReciprocityTheory.ChartRestriction.G.Geo.HermLine (dualBlocks T))
    (Ab : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (dualBlocks T)) (s : MRing (dualBlocks T)),
    IsArithVar Q (e + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm Ab → IsSectionOn Q Ab s →
    arInt (Q.comap (intCoordSubst A)) (intCoordSubst B s) (intCoordLine B ⟨A, hBA⟩ Ab)
        (fun j => intCoordLine B ⟨A, hBA⟩ (L j)) =
      arInt Q s Ab L

def intCoordSwap : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, 0]

theorem intCoordSwap_mul_self : intCoordSwap * intCoordSwap = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [intCoordSwap, Matrix.mul_apply, Fin.sum_univ_two]

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStackedExcBaseLe
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField

noncomputable section

namespace StackedExceptionalBaseBound

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F F' : HermLattice K i} {T : Type} [Fintype T]

theorem centre_mem {b : Module.Basis T ℤ (dualLattice F)} {b' : Module.Basis T ℤ (dualLattice F')} {a : T → ℤ}
    (hab : ∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) {k : Type} [Field k] {α : T → k}
    {M : T → Fin i → k} (hres : IsExcResidueData b b' α M) (t : T) :
    C (a t) * graphFirst t ∈ linPrime α M := by
  obtain ⟨ρ, ρ', σ, -, -, -, hker, -, -, hα, -⟩ := hres
  have hmem : ((a t • b' t : dualLattice F') : Fin i → K) ∈ dualLattice F := by
    rw [Submodule.coe_smul_of_tower, ← hab t]
    exact (b t).2
  have h0 : ((a t : ℤ) : k) * α t = 0 := by
    rw [hα t, ← zsmul_eq_mul, ← map_zsmul]
    exact (hker _).mpr hmem
  have h1 : linPointMap α M (C (a t)) = C ((a t : k)) := by simp [linPointMap]
  rw [linPrime, RingHom.mem_ker, map_mul, h1, LinPrimeExample.linPointMap_first, ← mul_assoc, ← C_mul, h0, C_0,
    zero_mul]

end StackedExceptionalBaseBound


open StackedExceptionalBaseBound in
theorem DualStackedExcBaseLe.proof (hBihom : DualStackedGraphBihomog.Statement)
    (hLead : DualStackedExcLeadForm.Statement) : DualStackedExcBaseLe.Statement := by
  intro K _ _ i F F' T _ _ b b' a hi hlt hcov hab k _ α M hres
  refine sup_le ?_ ?_
  · intro f hf
    obtain ⟨s, g, rfl, hg⟩ := hBihom K i F F' T b b' a hab f hf
    set_option synthInstance.maxHeartbeats 100000 in
      rw [linPrime, RingHom.mem_ker, map_sum]
    exact Finset.sum_eq_zero fun p hp =>
      hLead K i F F' T b b' a hi hlt hcov hab k α M hres p.1 p.2 (g p) (hg p hp).1 (hg p hp).2
  · rw [Ideal.span_le, Set.range_subset_iff]
    exact centre_mem hab hres

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualLatticeModPrime
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField
open scoped nonZeroDivisors

noncomputable section

namespace DualLatticeModPrimeAlt

variable {K : Type} [Field K] [NumberField K] {i : ℕ}

abbrev locAt (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] : Subalgebra (𝓞 K) K :=
  Localization.subalgebra.ofField K 𝔭.primeCompl 𝔭.primeCompl_le_nonZeroDivisors

theorem exists_smul_mem (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (L : Submodule (𝓞 K) (Fin i → K)) {x : Fin i → K}
    (hx : x ∈ Submodule.span (locAt 𝔭) (L : Set (Fin i → K))) :
    ∃ s ∈ 𝔭.primeCompl, s • x ∈ L := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨1, 𝔭.primeCompl.one_mem, by rwa [one_smul]⟩
  | zero => exact ⟨1, 𝔭.primeCompl.one_mem, by rw [smul_zero]; exact L.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨s₁, hs₁, hx⟩ := hx
    obtain ⟨s₂, hs₂, hy⟩ := hy
    refine ⟨s₁ * s₂, 𝔭.primeCompl.mul_mem hs₁ hs₂, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact L.smul_mem _ hx
    · rw [mul_smul]
      exact L.smul_mem _ hy
  | smul a x _ hx =>
    obtain ⟨s, hs, hx⟩ := hx
    obtain ⟨⟨p, q⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔭.primeCompl a
    refine ⟨q * s, 𝔭.primeCompl.mul_mem q.2 hs, ?_⟩
    have hq : (q : 𝓞 K) • (IsLocalization.mk' (locAt 𝔭) p q) = algebraMap (𝓞 K) (locAt 𝔭) p := by
      rw [Algebra.smul_def, mul_comm, IsLocalization.mk'_spec]
    have e : (q * s) • (IsLocalization.mk' (locAt 𝔭) p q • x) = p • (s • x) := by
      rw [mul_comm, mul_smul, ← smul_assoc (q : 𝓞 K), hq, algebraMap_smul, smul_comm]
    rw [e]
    exact L.smul_mem _ hx

theorem span_dual_eq_top (F : HermLattice K i) :
    Submodule.span K (DualLatticeIndexAlt.dual F.lattice : Set (Fin i → K)) = ⊤ := by
  obtain ⟨e, he0, hle⟩ := DualLatticeIndexAlt.exists_le_box F.lattice F.fg
  have heK : algebraMap (𝓞 K) K e ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr he0
  have hbox : DualLatticeIndexAlt.box (i := i) (algebraMap (𝓞 K) K e) ≤ DualLatticeIndexAlt.dual F.lattice := by
    have := DualLatticeIndexAlt.dual_anti hle
    rwa [DualLatticeIndexAlt.dual_box (inv_ne_zero heK), inv_inv] at this
  rw [eq_top_iff, ← (Pi.basisFun K (Fin i)).span_eq, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  have hj : (Pi.single j (algebraMap (𝓞 K) K e) : Fin i → K) ∈ DualLatticeIndexAlt.dual F.lattice := by
    refine hbox (DualLatticeIndexAlt.mem_box.mpr fun l => ?_)
    by_cases hl : l = j
    · subst hl
      exact ⟨1, by simp⟩
    · exact ⟨0, by simp [hl]⟩
  have e1 : Pi.basisFun K (Fin i) j = (algebraMap (𝓞 K) K e)⁻¹ • (Pi.single j (algebraMap (𝓞 K) K e) : Fin i → K) := by
    ext l
    by_cases hl : l = j
    · subst hl
      simp [heK]
    · simp [Pi.basisFun_apply, hl]
  rw [SetLike.mem_coe, e1]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hj)

theorem dual_le_span (F : HermLattice K i) :
    ∃ u : Fin i → Fin i → K, DualLatticeIndexAlt.dual F.lattice ≤ Submodule.span (𝓞 K) (Set.range u) := by
  obtain ⟨e, he0, hle⟩ := DualLatticeIndexAlt.exists_box_le F.lattice F.span_eq
  have heK : algebraMap (𝓞 K) K e ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr he0
  refine ⟨fun j => Pi.single j (algebraMap (𝓞 K) K e)⁻¹, fun x hx => ?_⟩
  have hx' := DualLatticeIndexAlt.dual_anti hle hx
  rw [DualLatticeIndexAlt.dual_box heK, DualLatticeIndexAlt.mem_box] at hx'
  choose a ha using hx'
  have e1 : x = ∑ j, a j • (Pi.single j (algebraMap (𝓞 K) K e)⁻¹ : Fin i → K) := by
    ext l
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_ite, smul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact (ha l).symm
  rw [e1]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

end DualLatticeModPrimeAlt


open DualLatticeModPrimeAlt in
theorem DualLatticeModPrime.proof : DualLatticeModPrime.Statement := by
  intro K _ _ i F 𝔭 h𝔭
  classical
  have hbot : 𝔭 ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (RingOfIntegers.not_isField K)
  have : IsDiscreteValuationRing (locAt 𝔭) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) hbot (locAt 𝔭)
  set D := DualLatticeIndexAlt.dual F.lattice
  set DA := Submodule.span (locAt 𝔭) (D : Set (Fin i → K))
  obtain ⟨u, hu⟩ := dual_le_span F
  have hDA : DA ≤ Submodule.span (locAt 𝔭) (Set.range u) :=
    Submodule.span_le.mpr fun x hx =>
      Submodule.span_le_restrictScalars (𝓞 K) (locAt 𝔭) _ (hu hx)
  have := isNoetherian_of_fg_of_noetherian _ (Submodule.fg_span (Set.finite_range u)) (R := locAt 𝔭)
  have : Module.Finite (locAt 𝔭) DA := Module.Finite.iff_fg.mpr (isNoetherian_submodule.mp this DA hDA)
  have : Module.IsTorsionFree (locAt 𝔭) DA := inferInstance
  let b := Module.Free.chooseBasis (locAt 𝔭) DA
  have hspan : Submodule.span K (Set.range fun j => (b j : Fin i → K)) = ⊤ := by
    rw [eq_top_iff, ← span_dual_eq_top F, Submodule.span_le]
    intro d hd
    have e0 : d = ∑ j, ((b.repr ⟨d, Submodule.subset_span hd⟩ j • b j : DA) : Fin i → K) := by
      rw [← Submodule.coe_sum, b.sum_repr]
    rw [e0, SetLike.mem_coe]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [Submodule.coe_smul]
    exact Submodule.span_le_restrictScalars (locAt 𝔭) K _
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
  have hcard : Fintype.card (Fin i) ≤ Fintype.card (Module.Free.ChooseBasisIndex (locAt 𝔭) DA) := by
    have := finrank_range_le_card (R := K) fun j => (b j : Fin i → K)
    rw [Set.finrank, hspan, finrank_top, Module.finrank_fin_fun] at this
    simpa using this
  obtain ⟨g⟩ := Function.Embedding.nonempty_of_card_le hcard
  let ρ : locAt 𝔭 →+* 𝓞 K ⧸ 𝔭 := IsLocalization.lift (M := 𝔭.primeCompl) (g := Ideal.Quotient.mk 𝔭)
    fun s => by
      obtain ⟨c, hc⟩ := Ideal.Quotient.exists_inv (I := 𝔭) (a := Ideal.Quotient.mk 𝔭 s)
        fun h => s.2 (Ideal.Quotient.eq_zero_iff_mem.mp h)
      exact ⟨⟨_, c, hc, by rw [mul_comm]; exact hc⟩, rfl⟩
  have hρ : ∀ a, ρ (algebraMap (𝓞 K) (locAt 𝔭) a) = Ideal.Quotient.mk 𝔭 a := fun a =>
    IsLocalization.lift_eq _ _
  have incl : ∀ φ : dualLattice F, (φ : Fin i → K) ∈ DA := fun φ => Submodule.subset_span φ.2
  let ι : dualLattice F →+ DA := AddMonoidHom.mk' (fun φ => ⟨φ, incl φ⟩) fun _ _ => rfl
  let τ : DA →+ (Fin i → 𝓞 K ⧸ 𝔭) := AddMonoidHom.mk' (fun x l => ρ (b.repr x (g l)))
    fun x y => by funext l; simp [map_add (f := _)]
  have hsmul : ∀ (μ : 𝓞 K) (x : DA), ((algebraMap (𝓞 K) (locAt 𝔭) μ • x : DA) : Fin i → K) =
      algebraMap (𝓞 K) K μ • (x : Fin i → K) := fun μ x => by
    rw [Submodule.coe_smul, algebraMap_smul, algebraMap_smul]
  refine ⟨τ.comp ι, ?_, ?_⟩
  · intro v
    let w : Module.Free.ChooseBasisIndex (locAt 𝔭) DA → 𝓞 K ⧸ 𝔭 := Function.extend g v 0
    choose a ha using fun j => Ideal.Quotient.mk_surjective (I := 𝔭) (w j)
    let x : DA := ∑ j, algebraMap (𝓞 K) (locAt 𝔭) (a j) • b j
    have hx : ∀ j, b.repr x j = algebraMap (𝓞 K) (locAt 𝔭) (a j) := by
      intro j
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [x, map_sum, map_smul, Module.Basis.repr_self, Finsupp.coe_finsetSum, Finset.sum_apply,
        Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
    obtain ⟨s, hs, hsx⟩ := exists_smul_mem 𝔭 D x.2
    have hs0 : Ideal.Quotient.mk 𝔭 s ≠ 0 := fun h => hs (Ideal.Quotient.eq_zero_iff_mem.mp h)
    obtain ⟨c, hc⟩ := Ideal.Quotient.exists_inv hs0
    obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (I := 𝔭) c
    refine ⟨⟨t • s • (x : Fin i → K), D.smul_mem t hsx⟩, ?_⟩
    have e1 : ι ⟨t • s • (x : Fin i → K), D.smul_mem t hsx⟩ = algebraMap (𝓞 K) (locAt 𝔭) (t * s) • x := by
      apply Subtype.ext
      rw [hsmul, algebraMap_smul, mul_smul]
      rfl
    funext l
    have key : ∀ y : DA, τ y l = ρ (b.repr y (g l)) := fun _ => rfl
    rw [AddMonoidHom.comp_apply, e1, key, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, hρ, hx, hρ,
      map_mul, ht, mul_comm c, hc, one_mul, ha]
    exact g.injective.extend_apply _ _ _
  · intro μ φ ψ h
    have e1 : ι ψ = algebraMap (𝓞 K) (locAt 𝔭) μ • ι φ := by
      apply Subtype.ext
      rw [hsmul]
      exact h
    funext l
    have key : ∀ x : DA, τ x l = ρ (b.repr x (g l)) := fun _ => rfl
    rw [Pi.smul_apply, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, e1, key, key, map_smul,
      Finsupp.smul_apply, smul_eq_mul, map_mul, hρ, smul_eq_mul]

end

end GroundTheory.Heights₂.Heights
end
