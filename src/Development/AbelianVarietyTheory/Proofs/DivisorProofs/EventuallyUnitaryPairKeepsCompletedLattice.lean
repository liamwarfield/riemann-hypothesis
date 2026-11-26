module

public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
public import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LocalValuationColumns
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompLinearEquivIntertwining
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsValueTiedOfIsToricElt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsThetaFunOOfThetaAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyUnitaryPairKeepsCompletedLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyUnitaryPairKeepsCompletedLattice
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatNhds

open GlobalTheory.SplitScalar

variable {D : D7}

theorem continuous_mt (V : HSp D) : Continuous (Formalism.L2.Theta.mt V) :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_mt_inv (V : HSp D) : Continuous fun g : GA D V => Formalism.L2.Theta.mt V g⁻¹ :=
  Units.continuous_coe_inv.comp continuous_subtype_val

theorem continuous_actO (S T : HSp D) (x : WO S T) :
    Continuous fun p : GA D S × GA D T => actO S T p.1 p.2 x := by
  have h1 : Continuous fun p : GA D S × GA D T => Formalism.L2.Theta.mt T p.2 := (continuous_mt T).comp continuous_snd
  have h2 : Continuous fun p : GA D S × GA D T => Formalism.L2.Theta.mt S p.1⁻¹ := (continuous_mt_inv S).comp continuous_fst
  exact (h1.matrix_mul continuous_const).matrix_mul h2

theorem actO_one (S T : HSp D) (x : WO S T) : actO S T 1 1 x = x := by
  have h : ∀ V : HSp D, Formalism.L2.Theta.mt V 1 = 1 := fun _ => rfl
  rw [actO, inv_one, h, h, Matrix.one_mul, Matrix.mul_one]

theorem actO_smul {S T : HSp D} (g : GA D S) (h : GA D T) (a : AE D) (x : WO S T) :
    actO S T g h (a • x) = a • actO S T g h x := by
  unfold actO
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem actO_add {S T : HSp D} (g : GA D S) (h : GA D T) (x y : WO S T) :
    actO S T g h (x + y) = actO S T g h x + actO S T g h y := by
  unfold actO
  rw [Matrix.mul_add, Matrix.add_mul]

theorem fin_iff {S T : HSp D} {u : WO S T} : u.map (infPart D) = 0 ↔ realIdem D • u = 0 := by
  constructor
  · exact fun h => Matrix.ext fun i j => realIdem_mul_of_fin (congrFun (congrFun h i) j)
  · intro h
    funext i j
    have h1 := congrArg (infPart D) (congrFun (congrFun h i) j)
    rw [Matrix.smul_apply, smul_eq_mul, RingHom.map_mul, infPart_realIdem, one_mul] at h1
    exact h1.trans (infPart D).map_zero

theorem actO_fin {S T : HSp D} (g : GA D S) (h : GA D T) {u : WO S T} (hu : u.map (infPart D) = 0) :
    (actO S T g h u).map (infPart D) = 0 := by
  rw [fin_iff] at hu ⊢
  rw [← actO_smul, hu, actO, Matrix.mul_zero, Matrix.zero_mul]

theorem continuous_sub_const' {X G : Type} [TopologicalSpace X] [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] {f : X → G} (hf : Continuous f) (x : G) : Continuous fun p => f p - x :=
  hf.sub continuous_const

theorem sub_nsmul_zero {G : Type} [AddCommGroup G] (x : G) (N : ℕ) : x - x - N • (0 : G) = 0 := by
  rw [sub_self, smul_zero, sub_self]

theorem eventually_move (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (x : WO S T) (hx : x.map (infPart D) = 0) (N : ℕ) (hN : 0 < N) :
    ∀ᶠ p : GA D S × GA D T in 𝓝 1, ∃ l ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E))
      (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), actO S T p.1 p.2 x = x + N • l := by
  have hO := GlobalTheory.LatOpen.isOpen_nsmul_latO D S T ΛS ΛT hS hT N hN
  have hc : Continuous fun p : GA D S × GA D T => actO S T p.1 p.2 x - x :=
    continuous_sub_const' (continuous_actO S T x) x
  have h1 := (hO.preimage hc).mem_nhds (x := 1) ⟨0, AddSubgroup.zero_mem _, by
    show (actO S T 1 1 x - x - N • (0 : WO S T)).map (finPart D) = 0
    rw [actO_one, sub_nsmul_zero]
    exact Matrix.ext fun _ _ => (finPart D).map_zero⟩
  filter_upwards [h1] with p hp
  obtain ⟨l, hl, e⟩ := hp
  refine ⟨l, hl, ?_⟩
  have hi : (actO S T p.1 p.2 x - x - N • l).map (infPart D) = 0 := by
    have a1 := fin_iff.1 (actO_fin p.1 p.2 hx)
    have a2 := fin_iff.1 hx
    have a3 := fin_iff.1 (latO_fin (AddSubgroup.nsmul_mem _ hl N))
    rw [fin_iff, smul_sub, smul_sub, a1, a2, a3, sub_zero, sub_zero]
  have hz : actO S T p.1 p.2 x - x - N • l = 0 :=
    Matrix.ext fun i j => adele_ext ((congrFun (congrFun hi i) j).trans (infPart D).map_zero.symm)
      ((congrFun (congrFun e i) j).trans (finPart D).map_zero.symm)
  rw [sub_sub, sub_eq_zero] at hz
  exact hz

theorem eventually_actO : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → (∃ G : Set (WO S T), G.Finite ∧ (∀ u ∈ G, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) ∧ ∀ U : AddSubgroup (WO S T), (∀ α ∈ intAf D.host.F, ∀ u ∈ G, algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) • u ∈ U) → ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), u ∈ U) → (∀ᶠ p : GA D S × GA D T in 𝓝 1, ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), actO S T p.1 p.2 u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) ∧ ∀ x : WO S T, x.map (infPart D) = 0 → ∀ N : ℕ, 0 < N → ∀ᶠ p : GA D S × GA D T in 𝓝 1, ∃ l ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), actO S T p.1 p.2 x = x + N • l := by
  rintro D S T ΛS ΛT hS hT ⟨G, hG, hGl, hgen⟩
  refine ⟨?_, eventually_move S T ΛS ΛT hS hT⟩
  have h := (Filter.eventually_all_finite hG).2 fun u hu =>
    eventually_move S T ΛS ΛT hS hT u (latO_fin (hGl u hu)) 1 one_pos
  filter_upwards [h] with p hp
  intro w hw
  refine hgen (AddSubgroup.comap (AddMonoidHom.mk' (actO S T p.1 p.2) (actO_add p.1 p.2))
    (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True))
    (fun α hα u hu => ?_) w hw
  obtain ⟨l, hl, e⟩ := hp u hu
  rw [AddSubgroup.mem_comap, AddMonoidHom.mk'_apply, actO_smul, e]
  refine GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ ?_ _
    (AddSubgroup.add_mem _ (hGl u hu) (AddSubgroup.nsmul_mem _ hl 1))
  exact AddSubgroup.subset_closure ⟨α, hα, 1, rfl⟩

end GlobalTheory.LatNhds

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyUnitaryPairKeepsCompletedLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_unitaryPair_keeps_completedLattice : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → (∃ G : Set (WO S T), G.Finite ∧ (∀ u ∈ G, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) ∧ ∀ U : AddSubgroup (WO S T), (∀ α ∈ intAf D.host.F, ∀ u ∈ G, algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) • u ∈ U) → ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), u ∈ U) → (∀ᶠ p : GA D S × GA D T in 𝓝 1, ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), actO S T p.1 p.2 u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) ∧ ∀ x : WO S T, x.map (infPart D) = 0 → ∀ N : ℕ, 0 < N → ∀ᶠ p : GA D S × GA D T in 𝓝 1, ∃ l ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), actO S T p.1 p.2 x = x + N • l := by
  first | exact @GlobalTheory.LatNhds.eventually_actO | exact GlobalTheory.LatNhds.eventually_actO | (intros; apply GlobalTheory.LatNhds.eventually_actO <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockParOpp
noncomputable section

open Matrix
open scoped Classical

namespace GlobalTheory.OrbDesc

section Blocks

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] {a b : ℕ}

def side (e : ι ≃ Fin a ⊕ Fin b) (i : ι) : Bool := (e i).isRight

def uMat (e : ι ≃ Fin a ⊕ Fin b) (X : Fin a → Fin b → K) : Matrix ι ι K :=
  Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)

theorem uMat_add (e : ι ≃ Fin a ⊕ Fin b) (X Y : Fin a → Fin b → K) :
    uMat e (X + Y) = uMat e X * uMat e Y := by
  simp only [uMat, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  congr 1
  simp [Matrix.of_add_of, add_comm]

theorem uMat_zero (e : ι ≃ Fin a ⊕ Fin b) : uMat e (0 : Fin a → Fin b → K) = 1 := by
  simp [uMat]

def uGL (e : ι ≃ Fin a ⊕ Fin b) (X : Fin a → Fin b → K) : GL ι K :=
  ⟨uMat e X, uMat e (-X), by rw [← uMat_add, add_neg_cancel, uMat_zero],
    by rw [← uMat_add, neg_add_cancel, uMat_zero]⟩

def uHom (e : ι ≃ Fin a ⊕ Fin b) : Multiplicative (Fin a → Fin b → K) →* GL ι K where
  toFun X := uGL e X.toAdd
  map_one' := Units.ext (uMat_zero e)
  map_mul' X Y := Units.ext (uMat_add e X.toAdd Y.toAdd)

def blockPar (e : ι ≃ Fin a ⊕ Fin b) : Subgroup (GL ι K) where
  carrier := {g | (g : Matrix ι ι K).BlockTriangular (side e)}
  one_mem' := by simpa using Matrix.blockTriangular_one
  mul_mem' := by
    intro g h hg hh
    simpa using Matrix.BlockTriangular.mul hg hh
  inv_mem' := by
    intro g hg
    have : Invertible (g : Matrix ι ι K) := Units.invertible g
    simp only [Set.mem_setOf_eq, Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hg

def blockParOpp (e : ι ≃ Fin a ⊕ Fin b) : Subgroup (GL ι K) where
  carrier := {g | (g : Matrix ι ι K).BlockTriangular (fun i => OrderDual.toDual (side e i))}
  one_mem' := by simpa using Matrix.blockTriangular_one
  mul_mem' := by
    intro g h hg hh
    simpa using Matrix.BlockTriangular.mul hg hh
  inv_mem' := by
    intro g hg
    have : Invertible (g : Matrix ι ι K) := Units.invertible g
    simp only [Set.mem_setOf_eq, Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hg

def blockLevi (e : ι ≃ Fin a ⊕ Fin b) : Subgroup (GL ι K) := blockPar e ⊓ blockParOpp e

def blockUni (e : ι ≃ Fin a ⊕ Fin b) : Subgroup (GL ι K) := (uHom e).range

end Blocks

section Sums

variable {H : Type} [Group H]

def wt (T L U : Subgroup H) (Ψ : H → ℂ) (x : H) : ℂ :=
  (GlobalTheory.LKLoc.volRat U (GlobalTheory.LKLoc.locPart T L x) : ℂ) * Ψ x

def dsum (T L U : Subgroup H) (Ψ : H → ℂ) : ℂ :=
  ∑ᶠ q : DoubleCoset.Quotient (T : Set H) (L : Set H), wt T L U Ψ (Quotient.out q)

end Sums

end GlobalTheory.OrbDesc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapRangeAdjointLeBlockSum
noncomputable section

open Polynomial Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links

namespace GlobalTheory.AdjBlock

section Linear

variable {K V H E : Type} [Field K] [AddCommGroup V] [Module K V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {σ : K →+* ℂ} {j : V →ₛₗ[σ] H} {ι : Type} [Fintype ι] {b : Module.Basis ι K V}

theorem map_eq_sum (j : V →ₛₗ[σ] H) (b : Module.Basis ι K V) (v : V) : j v = ∑ i, σ (b.repr v i) • j (b i) := by
  conv_lhs => rw [← b.sum_repr v]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smulₛₗ]

theorem exists_cx (hli : LinearIndependent ℂ fun i => j (b i)) (hsp : Submodule.span ℂ (Set.range j) = ⊤)
    (f : Module.End K V) : ∃ U : Module.End ℂ H, ∀ v, U (j v) = j (f v) := by
  have h2 : ⊤ ≤ Submodule.span ℂ (Set.range fun i => j (b i)) := by
    rw [← hsp, Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    rw [map_eq_sum j b]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨(Module.Basis.mk hli h2).constr ℂ fun i => j (f (b i)), fun v => ?_⟩
  have h3 : ∀ i, ((Module.Basis.mk hli h2).constr ℂ fun i => j (f (b i))) (j (b i)) = j (f (b i)) := fun i => by
    have := (Module.Basis.mk hli h2).constr_basis ℂ (fun i => j (f (b i))) i
    rwa [Module.Basis.mk_apply] at this
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_eq_sum j b v, map_sum]
  conv_rhs => rw [← b.sum_repr v]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, map_smulₛₗ, h3]

theorem ext_of_span {X : Type} [AddCommGroup X] [Module ℂ X] (hsp : Submodule.span ℂ (Set.range j) = ⊤)
    {f g : H →ₗ[ℂ] X} (h : ∀ v, f (j v) = g (j v)) : f = g :=
  LinearMap.ext_on_range hsp h

theorem sum_selfAdj {G : Type} [Group G] [Fintype G] (r : Representation K G V) (a : G → K)
    (ha : ∀ g, starRingEnd ℂ (σ (a g)) = σ (a g⁻¹))
    (hr : ∀ g v w, inner ℂ (j (r g v)) (j (r g w)) = inner ℂ (j v) (j w)) (v w : V) :
    inner ℂ (j ((∑ g, a g • r g) v)) (j w) = inner ℂ (j v) (j ((∑ g, a g • r g) w)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smulₛₗ, sum_inner, inner_sum, inner_smul_left,
    inner_smul_right, ha]
  refine Fintype.sum_equiv (Equiv.inv G) _ _ fun g => ?_
  rw [Equiv.inv_apply, ← hr g v, ← Module.End.mul_apply (r g) (r g⁻¹), ← map_mul, mul_inv_cancel, map_one,
    Module.End.one_apply]

end Linear

section Poly

end Poly

section Core

variable {K V H E Pl : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  {σ : K →+* ℂ} {j : V →ₛₗ[σ] H} {ι : Type} [Fintype ι] {b : Module.Basis ι K V}

end Core

section Pres

variable {G Γ W K : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [Field K] [NumberField K] [StarRing K] {ι : Γ →* G} {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W}
  {J : Subgroup G} {χ : J →* ℂˣ} (P : Bridge.ClassPres ι S σ ρ J χ) (M : HMod (G → W))
  (hM : M.Is (Bridge.AdForms ι ρ J χ) (Bridge.adInner ι J P.y)) {j : S.Forms →ₛₗ[σ] M.H}
  (hj : ∀ x, M.e (j x) = P.extL x)

include hM hj

theorem model_form : (LinearIndependent ℂ fun i => j (S.basis i)) ∧ Submodule.span ℂ (Set.range j) = ⊤ ∧
    ∀ x y, inner ℂ (j x) (j y) = σ (S.csum (x : S.Cl → S.V) (y : S.Cl → S.V)) := by
  obtain ⟨-, h2, ⟨h3, h4⟩, -⟩ := classPres_basic ι S σ ρ J χ P
  refine ⟨LinearIndependent.of_comp M.e (by simpa only [Function.comp_def, hj] using h3), ?_, fun x y => ?_⟩
  · refine Submodule.map_injective_of_injective hM.1 ?_
    rw [Submodule.map_top, hM.2.1, ← h4, Submodule.map_span, ← Set.range_comp]
    simp only [Function.comp_def, hj]
  · rw [hM.2.2, hj, hj]
    exact h2 x y

end Pres

theorem idem_idem {K G E : Type} [Field K] [CharZero K] [Group G] [Fintype G] [AddCommGroup E] [Module ℂ E]
    (σ : K →+* ℂ) {X : Finset (G → K)} (hX : ∀ c ∈ X, IsAbsIrrChar c) (ρ : Representation ℂ G E) (z : E) :
    ∑ g, σ ((idemOf X).coeff g) • ρ g (∑ h, σ ((idemOf X).coeff h) • ρ h z) = ∑ h, σ ((idemOf X).coeff h) • ρ h z := by
  conv_rhs => rw [← idemOf_mul_self X hX]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [coeff_mul_fin, map_sum, map_smul, Finset.smul_sum, Finset.sum_smul, map_mul]
  rw [Finset.sum_comm (f := fun h x => (σ ((idemOf X).coeff x) * σ ((idemOf X).coeff (x⁻¹ * h))) • ρ h z)]
  refine Finset.sum_congr rfl fun g _ => Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun h => ?_
  simp [mul_smul]

theorem mem_range_adjoint_tw {E E' : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [FiniteDimensional ℂ E'] (s : Bool) (f : E →ₗ[ℂ] E') (y : E) :
    Tw.mk s y ∈ LinearMap.range (LinearMap.adjoint (Tw.map s f)) ↔ y ∈ LinearMap.range (LinearMap.adjoint f) := by
  have : Tw.map s (LinearMap.adjoint f) = LinearMap.adjoint (Tw.map s f) := by
    rw [LinearMap.eq_adjoint_iff]
    intro x y
    rw [Tw.inner_eq, Tw.inner_eq]
    exact congrArg (cj s) (LinearMap.adjoint_inner_left f (Tw.out y) (Tw.out x))
  rw [← this]
  exact Iff.rfl

end GlobalTheory.AdjBlock

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueEqZeroIffV
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PrimePart

open NumberField MvPowerSeries IsLocalRing
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Sh
open GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes

section Hom

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)}

theorem subst_sum_smul {σ τ ι : Type} [Fintype ι] {a : σ → MvPowerSeries τ C} (ha : HasSubst a) (m : ι → C)
    (f : ι → MvPowerSeries σ C) : subst a (∑ i, m i • f i) = ∑ i, m i • (subst a (f i) : MvPowerSeries τ C) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← substAlgHom_apply ha, map_sum]
  simp only [map_smul, substAlgHom_apply]

theorem isIntHom_comp {d d' d'' : ℕ} {G : LogFGL v d} {G' : LogFGL v d'} {G'' : LogFGL v d''}
    {φ : Fin d' → MvPowerSeries (Fin d) C} {ψ : Fin d'' → MvPowerSeries (Fin d') C}
    {M : Matrix (Fin d') (Fin d) C} {N : Matrix (Fin d'') (Fin d') C}
    (hφ : IsIntHom G G' φ M) (hψ : IsIntHom G' G'' ψ N) :
    IsIntHom G G'' (fun b => subst φ (ψ b)) (N * M) := by
  obtain ⟨hφ0, hφi, hφl⟩ := hφ
  obtain ⟨hψ0, hψi, hψl⟩ := hψ
  have hφs : HasSubst φ := hasSubst_of_constantCoeff_zero hφ0
  have hψs : HasSubst ψ := hasSubst_of_constantCoeff_zero hψ0
  refine ⟨fun b => constantCoeff_subst_eq_zero hφs hφ0 (hψ0 b), fun b => ?_, fun c => ?_⟩
  · exact ptIntSer_subst hφs (fun s => hφi s) (hψi b)
  · rw [← subst_comp_subst_apply hψs hφs, hψl c, subst_sum_smul hφs]
    simp_rw [hφl, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
    exact Finset.sum_comm

end Hom

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H}

section Labels

variable {c : Coeff l} {T : CDVR} (io : c.F →+* T.Fr) {p : ℕ} [Fact p.Prime] (X : ValExt T p)

def embO (σ : E →+* ℂ) : 𝓞 E →+* X.O where
  toFun a := (X.ints.exists_of_le_one (v_embX_le_one io X σ a)).choose
  map_one' := X.ints.hom_inj (by rw [(X.ints.exists_of_le_one (v_embX_le_one io X σ _)).choose_spec, map_one, map_one])
  map_zero' := X.ints.hom_inj (by
    rw [(X.ints.exists_of_le_one (v_embX_le_one io X σ _)).choose_spec, map_zero, map_zero])
  map_mul' a b := X.ints.hom_inj (by
    rw [map_mul (algebraMap X.O X.C), (X.ints.exists_of_le_one (v_embX_le_one io X σ _)).choose_spec,
      (X.ints.exists_of_le_one (v_embX_le_one io X σ _)).choose_spec,
      (X.ints.exists_of_le_one (v_embX_le_one io X σ _)).choose_spec, map_mul])
  map_add' a b := X.ints.hom_inj (by
    rw [map_add (algebraMap X.O X.C), (X.ints.exists_of_le_one (v_embX_le_one io X σ _)).choose_spec,
      (X.ints.exists_of_le_one (v_embX_le_one io X σ _)).choose_spec,
      (X.ints.exists_of_le_one (v_embX_le_one io X σ _)).choose_spec, map_add])

theorem algebraMap_embO (σ : E →+* ℂ) (a : 𝓞 E) : algebraMap X.O X.C (embO io X σ a) = embX io X σ a :=
  (X.ints.exists_of_le_one (v_embX_le_one io X σ a)).choose_spec

def red (σ : E →+* ℂ) : 𝓞 E →+* ResidueField X.O := (residue X.O).comp (embO io X σ)

theorem residue_eq_zero_iff_v (x : X.O) : residue X.O x = 0 ↔ X.v (algebraMap X.O X.C x) < 1 := by
  rw [residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff, X.ints.isUnit_iff_valuation_eq_one]
  exact ⟨fun h => lt_of_le_of_ne (X.ints.map_le_one x) h, fun h => h.ne⟩

theorem residue_eq_iff_v (x y : X.O) :
    residue X.O x = residue X.O y ↔ X.v (algebraMap X.O X.C x - algebraMap X.O X.C y) < 1 := by
  rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff_v, map_sub]

theorem primeBelow_eq_ker (σ : E →+* ℂ) : primeBelow io X σ = RingHom.ker (red io X σ) := by
  ext a
  rw [RingHom.mem_ker]
  show X.v (embX io X σ a) < 1 ↔ residue X.O (embO io X σ a) = 0
  rw [residue_eq_zero_iff_v, algebraMap_embO]

theorem red_eq_pow_iff (σ σ' : E →+* ℂ) (a : 𝓞 E) (n : ℕ) :
    red io X σ' a = red io X σ a ^ n ↔ X.v (embX io X σ' a - embX io X σ a ^ n) < 1 := by
  show residue X.O (embO io X σ' a) = residue X.O (embO io X σ a) ^ n ↔ _
  rw [← map_pow, residue_eq_iff_v, map_pow, algebraMap_embO, algebraMap_embO]

theorem charP_residueField_of_irreducible : CharP (ResidueField X.O) p := by
  have h : ((p : ℕ) : ResidueField X.O) = 0 := by
    rw [← map_natCast (residue X.O), residue_eq_zero_iff]
    exact X.nonunit.out
  exact (CharP.charP_iff_prime_eq_zero Fact.out).2 h

theorem vX_vp_pos_iff (x : X.C) : 0 < vX_vp X x ↔ X.v x < 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hpO : ¬ IsUnit (p : X.O) := X.nonunit.out
  have hp1 : X.v (p : X.C) < 1 := by
    have h := X.ints.map_le_one (p : X.O)
    rw [map_natCast] at h
    refine lt_of_le_of_ne h fun h1 => hpO ?_
    apply X.ints.isUnit_of_one'
    rw [map_natCast]
    exact h1
  have hp0 : (0 : NNReal) < X.v (p : X.C) := by
    rw [pos_iff_ne_zero, Valuation.ne_zero_iff]
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hx0 : (0 : NNReal) < X.v x := by
    rw [pos_iff_ne_zero, Valuation.ne_zero_iff]
    exact hx
  have hlp : Real.log (X.v (p : X.C) : ℝ) < 0 :=
    Real.log_neg (by exact_mod_cast hp0) (by exact_mod_cast hp1)
  have hi : (Real.log (X.v (p : X.C) : ℝ))⁻¹ < 0 := inv_lt_zero.mpr hlp
  rw [vX_vp_apply X hx, show (0 : WithTop ℝ) = ((0 : ℝ) : WithTop ℝ) from rfl, WithTop.coe_lt_coe,
    mul_pos_iff]
  constructor
  · rintro (⟨h1, _⟩ | ⟨_, h2⟩)
    · exact absurd h1 (not_lt.mpr hi.le)
    · have h3 := (Real.log_neg_iff (by exact_mod_cast hx0)).mp h2
      exact_mod_cast h3
  · intro h
    right
    exact ⟨hi, Real.log_neg (by exact_mod_cast hx0) (by exact_mod_cast h)⟩

end Labels

variable {Dw : Datum H} {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] {T : CDVR} {io : c.F →+* T.Fr}
  {y : IntFr Xo c T io} (Ch : IntegralChartA3 Xo c T io y) {p : ℕ} [Fact p.Prime] (X : ValExt T p)

def tanX (a : 𝓞 E) : Matrix (Fin (chD Ch.ch)) (Fin (chD Ch.ch)) X.C :=
  Matrix.of fun i j => jX X (coeff (Finsupp.single ((0 : Fin 1), j) 1) (Ch.actT a i))

end GlobalTheory.PrimePart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompletedOrderIffPlacewise
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompletedOrderIffPlacewise
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler

namespace GlobalTheory.CMVal.HatPlace

variable {E : Type} [Field E] [NumberField E]

theorem isOpen_integral : IsOpen {y : Af E | ∀ w, Valued.v (y w) ≤ 1} :=
  RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
    (A := fun v => v.adicCompletionIntegers E) fun _ => Valued.isOpen_valuationSubring _

theorem exists_approx {S : Set (Af E)} {z : Af E} (hz : z ∈ closure S) {n : OF E} (hn : n ≠ 0) :
    ∃ x ∈ S, ∃ y : Af E, (∀ w, Valued.v (y w) ≤ 1) ∧ z = x + iota n * y := by
  have hn0 : algebraMap (OF E) E n ≠ 0 := fun h => hn (Subtype.ext (Subtype.ext h))
  have ho : IsOpen ((fun t : Af E => algebraMap E (Af E) (algebraMap (OF E) E n)⁻¹ * (z - t)) ⁻¹'
      {y : Af E | ∀ w, Valued.v (y w) ≤ 1}) :=
    isOpen_integral.preimage (continuous_const.mul (continuous_const.sub continuous_id))
  obtain ⟨x, hx, hxS⟩ := mem_closure_iff.1 hz _ ho (fun w => by
    simp only [sub_self, mul_zero, zero_coord, map_zero, zero_le'])
  refine ⟨x, hxS, _, hx, ?_⟩
  rw [iota, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hn0, map_one, one_mul, add_sub_cancel]

theorem mem_iff_val {J : Ideal (𝓞 E)} (hJ : J ≠ ⊥) (b : 𝓞 E) :
    b ∈ J ↔ ∀ w : HeightOneSpectrum (𝓞 E), Valued.v (algebraMap E (Af E) (algebraMap (𝓞 E) E b) w) ≤
      WithZero.exp (-(multiplicity w.asIdeal J : ℤ)) := by
  conv_lhs => rw [← Ideal.iInf_maxPowDividing_eq hJ, Ideal.mem_iInf]
  refine forall_congr' fun P => ?_
  rw [HeightOneSpectrum.maxPowDividing_eq_pow_multiplicity hJ, ← P.intValuation_le_pow_iff_mem,
    ← HeightOneSpectrum.valuation_of_algebraMap (K := E),
    ← HeightOneSpectrum.valuedAdicCompletion_eq_valuation', ← FiniteAdeleRing.algebraMap_apply]

theorem val_mul_le {c : Ideal (OF E)} (hc : c ≠ ⊥) {n : OF E} (hn : n ∈ c) {y : Af E} (hy : ∀ w, Valued.v (y w) ≤ 1)
    (w : HeightOneSpectrum (𝓞 E)) : Valued.v ((iota n * y) w) ≤
      WithZero.exp (-(multiplicity w.asIdeal (Ideal.map (algebraMap (OF E) (𝓞 E)) c) : ℤ)) := by
  rw [mul_coord, map_mul]
  exact (mul_le_mul' ((mem_iff_val (Ideal.map_ne_bot_of_ne_bot hc) _).1 (Ideal.mem_map_of_mem _ hn) w)
    (hy w)).trans_eq (mul_one _)

theorem mem_hatO_of_val {c : Ideal (OF E)} (hc : c ≠ ⊥) {z : Af E} (hz : ∀ w : HeightOneSpectrum (𝓞 E), Valued.v (z w) ≤
      WithZero.exp (-(multiplicity w.asIdeal (Ideal.map (algebraMap (OF E) (𝓞 E)) c) : ℤ))) : z ∈ hatO c := by
  have hN : 0 < Ideal.absNorm c := Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  obtain ⟨x, y, hy, hxy⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat E _ hN).2 z
    (fun P => (hz P).trans (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega))
  have hny : Ideal.absNorm c • y = iota ((Ideal.absNorm c : ℕ) : OF E) * y := by
    rw [nsmul_eq_mul, iota, map_natCast, map_natCast]
  rw [hny] at hxy
  have hx : x ∈ Ideal.map (algebraMap (OF E) (𝓞 E)) c := by
    rw [mem_iff_val (Ideal.map_ne_bot_of_ne_bot hc)]
    intro P
    have h1 : algebraMap E (Af E) (algebraMap (𝓞 E) E x) = z - iota ((Ideal.absNorm c : ℕ) : OF E) * y := by
      rw [hxy, add_sub_cancel_right]
    rw [h1, sub_coord]
    exact Valuation.map_sub_le _ (hz P) (val_mul_le hc (Ideal.absNorm_mem c) hy P)
  rw [hxy]
  exact add_mem (algebraMap_mem_hatO (mem_orderC.2 ⟨0, _, hx, by rw [map_zero, zero_add]⟩))
    (PicFin.mul_mem_hatO (Ideal.absNorm_mem c) hy)

theorem exists_integer {f : E} (hf : f ∈ maximalRealSubfield E)
    (h : ∀ w, Valued.v (algebraMap E (Af E) f w) ≤ 1) : ∃ a : OF E, algebraMap (OF E) E a = f := by
  obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E f fun w => by
    have := h w
    rwa [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at this
  have h1 : IsIntegral ℤ f := hb ▸ b.isIntegral_coe
  have h2 : IsIntegral ℤ (⟨f, hf⟩ : maximalRealSubfield E) :=
    (isIntegral_algebraMap_iff (A := maximalRealSubfield E) (B := E) ).1 h1
  exact ⟨⟨_, h2⟩, rfl⟩

theorem mem_hatO_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ z : Af E,
    z ∈ hatO c ↔ ∃ a ∈ hatF (E := E), (∀ w, Valued.v (a w) ≤ 1) ∧ ∀ (w : HeightOneSpectrum (𝓞 E)),
      Valued.v (z w - a w) ≤
        WithZero.exp (-(multiplicity w.asIdeal (Ideal.map (algebraMap (OF E) (𝓞 E)) c) : ℤ)) := by
  intro E _ _ _ c hc z
  obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
  constructor
  · intro hz
    obtain ⟨_, ⟨x, hx, rfl⟩, y, hy, rfl⟩ := exists_approx hz hn0
    obtain ⟨a, b, hb, rfl⟩ := mem_orderC.1 hx
    refine ⟨iota a, Subring.le_topologicalClosure _ ⟨_, (a : maximalRealSubfield E).2, rfl⟩,
      fun w => val_iota_le_one w a, fun w => ?_⟩
    rw [← sub_coord, map_add (f := _), add_assoc]
    erw [add_sub_cancel_left]
    rw [add_coord]
    exact Valuation.map_add_le _ ((mem_iff_val (Ideal.map_ne_bot_of_ne_bot hc) _).1 hb w) (val_mul_le hc hn hy w)
  · rintro ⟨a, ha, hai, hz⟩
    obtain ⟨_, ⟨f, hf, rfl⟩, y, hy, rfl⟩ := exists_approx ha hn0
    obtain ⟨a, rfl⟩ := exists_integer hf fun w => by
      have h1 : Valued.v ((iota n * y) w) ≤ 1 := by
        rw [mul_coord, map_mul]; exact mul_le_one' (val_iota_le_one w n) (hy w)
      have h2 := Valuation.map_sub_le _ (hai w) h1
      rwa [add_coord, add_sub_cancel_right] at h2
    have h1 : z - (algebraMap E (Af E) (algebraMap (OF E) E a) + iota n * y) ∈ hatO c := mem_hatO_of_val hc hz
    have h2 := add_mem h1 (add_mem (algebraMap_mem_hatO (algebraMap_mem_orderC c a)) (PicFin.mul_mem_hatO hn hy))
    exact sub_add_cancel z _ ▸ h2

end GlobalTheory.CMVal.HatPlace
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompletedOrderIffPlacewiseStatement
open NumberField IsDedekindDomain GlobalTheory.CMVal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_completedOrder_iff_placewise : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ z : Af E, z ∈ hatO c ↔ ∃ a ∈ hatF (E := E), (∀ w, Valued.v (a w) ≤ 1) ∧ ∀ (w : HeightOneSpectrum (𝓞 E)), Valued.v (z w - a w) ≤ WithZero.exp (-(multiplicity w.asIdeal (Ideal.map (algebraMap (OF E) (𝓞 E)) c) : ℤ)) := by
  first | exact @GlobalTheory.CMVal.HatPlace.mem_hatO_iff | exact GlobalTheory.CMVal.HatPlace.mem_hatO_iff | (intros; apply GlobalTheory.CMVal.HatPlace.mem_hatO_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatioConjOfToricRatioConjugates
noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions GlobalTheory.CMVal GlobalTheory.HeckeGal GlobalTheory.ToricDenom
open Cardinal

namespace GlobalTheory.ToricRatioBridge

abbrev algC : Subfield ℂ := (algebraicClosure ℚ ℂ).toSubfield

theorem mem_algC {z : ℂ} : z ∈ algC ↔ IsAlgebraic ℚ z := mem_algebraicClosure_iff

theorem isAlgebraic_finPart {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ} {m : I → ℤ}
    {χ : HChar E} (hm : HasInf χ φ m) {c : Ideal (OF E)} [Finite (PicO c)] (hu : ∀ y ∈ hatOUnits c, finPart χ y = 1)
    (y : (Af E)ˣ) : IsAlgebraic ℚ (finPart χ y : ℂ) := by
  let M : Subfield ℂ := algC
  let H : Subgroup (Af E)ˣ := M.toSubmonoid.units.comap (finPart χ)
  have hH : ∀ y, y ∈ H ↔ (finPart χ y : ℂ) ∈ M := fun y =>
    ⟨fun h => h.1, fun h => (Submonoid.mem_units_iff _ _).2 ⟨h, by rw [Units.val_inv_eq_inv_val]; exact M.inv_mem h⟩⟩
  have hE : ∀ (σ : E →+* ℂ) (x : E), σ x ∈ M := fun σ x =>
    mem_algC.2 ((Algebra.IsIntegral.isIntegral (R := ℚ) x).map σ.toRatAlgHom).isAlgebraic
  have hle : princ ⊔ hatOUnits c ≤ H := by
    refine sup_le ?_ fun u h => (hH u).2 (by rw [hu u h]; exact one_mem M)
    rintro _ ⟨k, rfl⟩
    rw [hH, eq_inv_of_mul_eq_one_left (finPart_mul_inf χ k), Units.val_inv_eq_inv_val, (hasInfRatio_iff χ φ m).1 hm k]
    exact inv_mem (prod_mem fun i _ => zpow_mem (div_mem (hE _ _) (hE ((starRingEnd ℂ).comp (φ i)) _)) _)
  let p : PicO c →* (Af E)ˣ ⧸ H := QuotientGroup.map _ _ (MonoidHom.id _) hle
  have : Finite ((Af E)ˣ ⧸ H) := Finite.of_surjective p fun q => by
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨QuotientGroup.mk y, rfl⟩
  have hn := pow_card_eq_one' (G := (Af E)ˣ ⧸ H) (x := (QuotientGroup.mk y))
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hH, map_pow, Units.val_pow_eq_pow_val] at hn
  exact IsAlgebraic.of_pow Nat.card_pos (mem_algC.1 hn)

theorem exists_eq_of_isAlgebraic {Ω : Type} [Field Ω] [IsAlgClosed Ω] (j : Ω →+* ℂ) {z : ℂ} (hz : IsAlgebraic ℚ z) :
    ∃ x : Ω, j x = z := by
  let _ : Algebra Ω ℂ := j.toAlgebra
  have : CharZero Ω := RingHom.charZero j
  have : IsScalarTower ℚ Ω ℂ := IsScalarTower.of_algebraMap_eq fun q => (map_ratCast j q).symm
  have hi : IsIntegral Ω z := (hz.isIntegral).tower_top
  obtain ⟨x, hx⟩ := minpoly.mem_range_of_degree_eq_one Ω z
    (IsAlgClosed.degree_eq_one_of_irreducible Ω (minpoly.irreducible hi))
  exact ⟨x, hx⟩

theorem comp_eq_of_sqrt {R : Ranks} (H : Host R) (f g : H.E →+* ℂ) (h : f H.sqrtMinusD = g H.sqrtMinusD) :
    f.comp (algebraMap H.K H.E) = g.comp (algebraMap H.K H.E) := by
  refine RingHom.ext fun x => ?_
  have hx : (x : H.E) ∈ Algebra.adjoin ℚ {H.sqrtMinusD} := by
    have h1 : IsIntegral ℚ H.sqrtMinusD := Algebra.IsIntegral.isIntegral _
    have : (x : H.E) ∈ IntermediateField.adjoin ℚ {H.sqrtMinusD} := x.2
    rw [← IntermediateField.mem_toSubalgebra,
      IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic h1.isAlgebraic] at this
    exact this
  have hle : Algebra.adjoin ℚ {H.sqrtMinusD} ≤ AlgHom.equalizer f.toRatAlgHom g.toRatAlgHom :=
    Algebra.adjoin_le (Set.singleton_subset_iff.2 h)
  show f (x : H.E) = g (x : H.E)
  exact hle hx

theorem upIdele_eq (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] (t : (Af K)ˣ) :
    GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.upIdele K E t = Units.map (GlobalTheory.AdeleBaseChange.adMap K E).toMonoidHom t :=
  Units.ext (FiniteAdeleRing.ext _ fun P => (GlobalTheory.CharTransport.locMap_eq K E P _).symm)

theorem countable_of_isAlgClosure (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] :
    Countable Ω := by
  have hK : #K ≤ ℵ₀ := by
    simpa [Cardinal.mkRat] using Algebra.IsAlgebraic.cardinalMk_le_max ℚ K
  have : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  rw [← Cardinal.mk_le_aleph0_iff]
  exact (Algebra.IsAlgebraic.cardinalMk_le_max K Ω).trans (max_le hK le_rfl)

end GlobalTheory.ToricRatioBridge

namespace GlobalTheory.ToricRatioBridge

open GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols (ToricRatioConjugates IsSymbol classOf conjChar)

theorem ratioConj_of_toricRatioConjugates (hG : ToricRatioConjugates) : GlobalTheory.ToricRational.RatioConj := by
  intro R H I _ φ s κ 𝔣 χ hD Ω _ _ _ j τ₀ hj art ha T₀ hT₀ h0 Q hQ hfin T hT
  have : IsCMField H.E := H.isCMField_hostE
  have hU : UnramFin H.E := GlobalTheory.ToricDenomBridge.host_unramFin H
  let ι : H.K →+* ℂ := (φ τ₀).comp (algebraMap H.K H.E)
  have hι : ∀ i, (φ i).comp (algebraMap H.K H.E) = ι := fun i => comp_eq_of_sqrt H _ _ (hD.2.1 i τ₀)
  let δ : H.K := ⟨H.sqrtMinusD, H.sqd_mem_K⟩
  have hδ : δ ^ 2 = -(H.d : H.K) := Subtype.ext (by push_cast; exact H.sqrtMinusD_sq)
  have hK2 : Module.finrank ℚ H.K = 2 := H.finrank_K
  obtain ⟨T₀', Tw, hT₀', -, hTw, halg, hconj⟩ := hG H.E H.K H.d δ ι I φ s κ 𝔣 Q χ hU hK2 H.hyp.2.1.pos hδ hD.1 hι
    hD.2.2.1 hD.2.2.2.1 hD.2.2.2.2.1 hQ hD.2.2.2.2.2
  have h𝔣 : condQ 𝔣 ∅ = 𝔣 := by simp [condQ]
  have hT₀'' : IsToricSum φ s κ (condQ 𝔣 ∅) χ T₀' := by rw [h𝔣]; exact hT₀'
  have e0 : T₀' = T₀ := hT₀''.unique hT₀
  subst e0
  let up : (PicO (condQ 𝔣 Q) →* Ωˣ) → (PicO (condQ 𝔣 Q) →* ℂˣ) := fun ψ => (Units.map j.toMonoidHom).comp ψ
  have hsum : ∀ ψ', Tw ψ' = ∑ᶠ q, ((ψ' q : ℂˣ) : ℂ)⁻¹ * T q := fun ψ' => by
    obtain ⟨_, S, hS, e⟩ := hTw ψ'
    rw [e]
    refine finsum_congr fun q => ?_
    obtain ⟨S', hS', e'⟩ := hT q
    rw [e', mul_assoc, (hS q).unique hS']
    rfl
  have hΩ : IsAlgClosed Ω := IsAlgClosure.isAlgClosed H.K
  choose ρ hρ using fun ψ => exists_eq_of_isAlgebraic j (halg (up ψ))
  refine ⟨ρ, fun ψ => by rw [hρ, hsum]; rfl, fun g hgE hgl t ht ψ => ?_⟩
  have : Countable Ω := countable_of_isAlgClosure H.K Ω
  obtain ⟨g', hg'⟩ := GlobalTheory.GaloisDescent.exists_complex_ringEquiv_comp_eq j (j.comp g.toRingEquiv.toRingHom)
  have hfix : ∀ z : ℂ, IsAlgebraic ℚ z → (∀ x, j x = z → g x = x) → g' z = z := fun z hz hx => by
    obtain ⟨x, rfl⟩ := exists_eq_of_isAlgebraic j hz
    rw [hg']
    exact congrArg j (hx x rfl)
  have hφ : ∀ i (x : H.E), IsAlgebraic ℚ (φ i x) := fun i x =>
    ((Algebra.IsIntegral.isIntegral (R := ℚ) x).map (φ i).toRatAlgHom).isAlgebraic
  have : Finite (PicO (condQ 𝔣 ∅)) := hT₀.1
  have hl : ∀ y, IsAlgebraic ℚ (GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.lamF χ s y) := fun y => by
    have h1 := isAlgebraic_finPart hD.2.2.2.2.2.2.2.1 (c := condQ 𝔣 ∅)
      (OrderUnits.finPart_eq_one H.E I φ hD.1 s κ 𝔣 ∅ χ hU hD.2.2.2.2.1 (fun _ h => absurd h (Finset.notMem_empty _))
        hD.2.2.2.2.2) y
    refine mem_algC.1 (mul_mem (mem_algC.2 h1) ?_)
    rw [Complex.ofReal_pow]
    exact pow_mem (GlobalTheory.ToricRational.modF_mem _ y) s
  have hσ : ∀ x, j (g x) = g' (j x) := fun x => (hg' x).symm
  have hsym : IsSymbol art t g := by rw [IsSymbol, ht, map_inv, inv_inv]
  obtain ⟨e, -⟩ := hconj Ω j art (RingHom.ext hj) ha g' g t (fun i x => hfix _ (hφ i x) fun x' hx' => hgE x' i x hx')
    (fun y => hfix _ (hl y) fun x' hx' => hgl x' y hx') hσ hsym (up ψ)
  have hc : conjChar g' (up ψ) = up ((Units.map g.toRingEquiv.toMonoidHom).comp ψ) :=
    MonoidHom.ext fun q => Units.ext (hg' _)
  have hcls : classOf H.K (condQ 𝔣 Q) t = QuotientGroup.mk (GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.upIdele H.K H.E t) := by
    rw [classOf, upIdele_eq]
  apply j.injective
  rw [hσ, hρ, e, hc, hcls, map_mul, map_inv₀, hρ]
  rfl

end GlobalTheory.ToricRatioBridge
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryDivisorDualLabel
open IsDedekindDomain NumberField Formalism.UG Formalism.IndefR.Mult GlobalTheory.SphPar Polynomial

namespace GlobalTheory.DualDivU

section Generic

variable {L : Type} [Field L] {n : ℕ}

theorem exists_glint (O : Subring L) (A B : Matrix (Fin n) (Fin n) L) (hAB : A * B = 1) (hBA : B * A = 1)
    (hA : ∀ i j, A i j ∈ O) (hB : ∀ i j, B i j ∈ O) :
    ∃ U ∈ GLint (Fin n) O, (U : Matrix (Fin n) (Fin n) L) = A := by
  let A0 : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => ⟨A i j, hA i j⟩
  let B0 : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => ⟨B i j, hB i j⟩
  have eA : RingHom.mapMatrix (m := Fin n) O.subtype A0 = A := by ext i j; rfl
  have eB : RingHom.mapMatrix (m := Fin n) O.subtype B0 = B := by ext i j; rfl
  have inj : Function.Injective (RingHom.mapMatrix (m := Fin n) O.subtype) := by
    intro X Y h
    ext i j
    simpa using congrFun (congrFun h i) j
  have h1 : A0 * B0 = 1 := inj (by rw [map_mul, map_one, eA, eB, hAB])
  have h2 : B0 * A0 = 1 := inj (by rw [map_mul, map_one, eA, eB, hBA])
  exact ⟨bc (n := Fin n) O.subtype ⟨A0, B0, h1, h2⟩, ⟨_, rfl⟩, eA⟩

theorem entry_mem (O : Subring L) {U : GL (Fin n) L} (hU : U ∈ GLint (Fin n) O) (i j : Fin n) :
    (U : Matrix (Fin n) (Fin n) L) i j ∈ O := by
  obtain ⟨U0, rfl⟩ := hU
  exact ((U0 : Matrix (Fin n) (Fin n) O) i j).2

theorem antiJ_apply (i j : Fin n) : antiJ L n i j = if j = i.rev then 1 else 0 := by
  unfold antiJ
  congr 1
  have := i.2
  have := j.2
  simp only [Fin.ext_iff, Fin.val_rev, eq_iff_iff]
  omega

theorem antiJ_mul (A : Matrix (Fin n) (Fin n) L) (i j : Fin n) : (antiJ L n * A) i j = A i.rev j := by
  simp [Matrix.mul_apply, antiJ_apply]

theorem mul_antiJ (A : Matrix (Fin n) (Fin n) L) (i j : Fin n) : (A * antiJ L n) i j = A i j.rev := by
  have : ∀ k : Fin n, (j = k.rev) = (k = j.rev) := fun k => by
    rw [eq_iff_iff, eq_comm, Fin.rev_eq_iff]
  simp [Matrix.mul_apply, antiJ_apply, this]

theorem antiJ_sq : antiJ L n * antiJ L n = 1 := by
  ext i j
  rw [antiJ_mul, antiJ_apply, Fin.rev_rev, Matrix.one_apply]
  simp [eq_comm]

theorem dual_mul (σ : L →+* L) (A B : Matrix (Fin n) (Fin n) L) (h : A * B = 1) :
    antiJ L n * cT σ B * antiJ L n * (antiJ L n * cT σ A * antiJ L n) = 1 := by
  calc _ = antiJ L n * cT σ B * (antiJ L n * antiJ L n) * cT σ A * antiJ L n := by simp only [Matrix.mul_assoc]
    _ = antiJ L n * cT σ (A * B) * antiJ L n := by
      rw [antiJ_sq, Matrix.mul_one, cT_mul]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h, cT_one, Matrix.mul_one, antiJ_sq]

theorem getD_dualLab (d : List ℤ) (hd : d.length = n) (i : Fin n) :
    (dualLab d).getD i 0 = -(d.getD i.rev 0) := by
  subst hd
  have hi := i.2
  have h1 : (i : ℕ) < (dualLab d).length := by simp [dualLab]
  rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ i.rev.2]
  simp only [dualLab, List.getElem_reverse, List.getElem_map, List.length_map, Fin.val_rev]
  congr 2
  omega

end Generic

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

theorem exists_dual (σ : L →+* L) (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {a : GL (Fin n) L}
    (ha : a ∈ GLint (Fin n) (intL L)) :
    ∃ U ∈ GLint (Fin n) (intL L), (U : Matrix (Fin n) (Fin n) L) =
      antiJ L n * cT σ ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * antiJ L n := by
  have key : ∀ b ∈ GLint (Fin n) (intL L), ∀ i j,
      (antiJ L n * cT σ ((b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * antiJ L n) i j ∈ intL L := by
    intro b hb i j
    rw [mul_antiJ, antiJ_mul]
    have := entry_mem (intL L) hb j.rev i.rev
    show Valued.v (σ _) ≤ 1
    rw [hσ]
    exact this
  exact exists_glint (intL L) _ (antiJ L n * cT σ (a : Matrix (Fin n) (Fin n) L) * antiJ L n)
    (dual_mul σ _ _ (Units.mul_inv a)) (dual_mul σ _ _ (Units.inv_mul a)) (key _ (inv_mem ha)) (key _ ha)

theorem hasDiv_dualLab : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ) (d : List ℤ) (g : GL (Fin n) L), (∀ x, Valued.v (σ x) = Valued.v x) → d.length = n → g ∈ GU σ n → HasDiv (intL L) d g → HasDiv (intL L) (dualLab d) g := by
  intro L _ _ σ n d g hσ hd hg ⟨ϖ, hϖ, a, ha, b, hb, hab⟩
  obtain ⟨a', ha', ea⟩ := exists_dual σ hσ ha
  obtain ⟨b', hb', eb⟩ := exists_dual σ hσ hb
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hϖ
    exact WithZero.zero_ne_coe hϖ
  refine ⟨σ ϖ, by rw [hσ, hϖ], a', ha', b', hb', ?_⟩
  have hg' : cT σ (g : Matrix (Fin n) (Fin n) L) * antiJ L n * (g : Matrix (Fin n) (Fin n) L) = antiJ L n := hg
  have eD : Matrix.diagonal (fun i : Fin n => σ ϖ ^ (dualLab d).getD i 0) =
      antiJ L n * cT σ (Matrix.diagonal (fun i : Fin n => ϖ ^ (-d.getD i 0))) * antiJ L n := by
    ext i j
    rw [mul_antiJ, antiJ_mul]
    simp only [cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.diagonal_apply, Fin.rev_inj]
    by_cases h : i = j
    · subst h
      simp only [if_true]
      rw [getD_dualLab d hd, map_zpow₀]
    · rw [if_neg h, if_neg (Ne.symm h), map_zero]
  have hDD : Matrix.diagonal (fun i : Fin n => ϖ ^ d.getD i 0) *
      Matrix.diagonal (fun i : Fin n => ϖ ^ (-d.getD i 0)) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [← zpow_add₀ hϖ0, add_neg_cancel, zpow_zero]
  have hinv : (g : Matrix (Fin n) (Fin n) L) * (((b⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
      Matrix.diagonal (fun i : Fin n => ϖ ^ (-d.getD i 0)) * ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) = 1 := by
    rw [hab]
    calc _ = (a : Matrix (Fin n) (Fin n) L) * (Matrix.diagonal (fun i : Fin n => ϖ ^ d.getD i 0) *
        ((b : Matrix (Fin n) (Fin n) L) * ((b⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) *
        Matrix.diagonal (fun i : Fin n => ϖ ^ (-d.getD i 0))) *
        ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [Units.mul_inv, Matrix.mul_one, hDD, Matrix.mul_one, Units.mul_inv]
  have h1 := dual_mul σ _ _ hinv
  have h2 : antiJ L n * cT σ (g : Matrix (Fin n) (Fin n) L) * antiJ L n * (g : Matrix (Fin n) (Fin n) L) = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT σ _), hg', antiJ_sq]
  have h3 : (g : Matrix (Fin n) (Fin n) L) = antiJ L n * cT σ (((b⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
      Matrix.diagonal (fun i : Fin n => ϖ ^ (-d.getD i 0)) * ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) *
      antiJ L n := by
    conv_rhs => rw [← Matrix.mul_one (_ * antiJ L n), ← h2, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [h3, ea, eb, eD, cT_mul, cT_mul]
  have hJ : ∀ X : Matrix (Fin n) (Fin n) L, antiJ L n * (antiJ L n * X) = X := fun X => by
    rw [← Matrix.mul_assoc, antiJ_sq, Matrix.one_mul]
  simp only [Matrix.mul_assoc, hJ]

end GlobalTheory.DualDivU
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemEigSp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

noncomputable section
namespace GlobalTheory.UPel.HT.LieType

def eigSp {F : Type} [Field F] [NumberField F] {g : ℕ} (φ : 𝓞 F →+* Matrix (Fin g) (Fin g) ℂ) (τ : F →+* ℂ) :
    Submodule ℂ (Fin g → ℂ) where
  carrier := {u | ∀ c : 𝓞 F, φ c *ᵥ u = τ (c : F) • u}
  add_mem' := by
    intro u v hu hv c
    rw [Matrix.mulVec_add, hu c, hv c, smul_add]
  zero_mem' := by intro c; simp
  smul_mem' := by
    intro a u hu c
    rw [Matrix.mulVec_smul, hu c, smul_comm]

theorem mem_eigSp {F : Type} [Field F] [NumberField F] {g : ℕ} (φ : 𝓞 F →+* Matrix (Fin g) (Fin g) ℂ) (τ : F →+* ℂ)
    (u : Fin g → ℂ) : u ∈ eigSp φ τ ↔ ∀ c : 𝓞 F, φ c *ᵥ u = τ (c : F) • u := Iff.rfl

end GlobalTheory.UPel.HT.LieType
end
end
