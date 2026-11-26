module

public import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums
public import Formalism.SharpRestriction.GrowthBounds.InitialMinorTransposeMemHighestWeight
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree
public import Formalism.LocalToGlobal.GroupLattices.FockModels.LoBlockActComp
public import Formalism.SharpRestriction.GrowthBounds.SizesAtRecord
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.PrvAndKernelCommutationUpToUnitsOfRests
public import Formalism.LocalToGlobal.GroupLattices.FockModels.Sandwich
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.NpDescFOfValRatF
public import Formalism.SharpRestriction.GrowthBounds.TruncatedChains
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.OrbitSumStabilizer
public import Formalism.SharpRestriction.GrowthBounds.FockGramWindow
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor
public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials
public import Formalism.SharpRestriction.GrowthBounds.AevalValuation

@[expose] public section

section -- merged from Formalism.LocalToGlobal.GroupLattices.FockModels.LPBase
section -- merged from Formalism.LocalToGlobal.GroupLattices.FockModels.NablaLTwEqMap
open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Model

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.G.LatticeSystems

def BC {R R' X X' : Type*} [CommRing R] [CommRing R'] [AddCommGroup X] [Module R X] [AddCommGroup X']
    [Module R' X'] (μ : X → X') (A : Submodule R X) (A' : Submodule R' X') : Prop :=
  A' = Submodule.span R' (μ '' (A : Set X))

theorem BC.mem {R R' X X' : Type*} [CommRing R] [CommRing R'] [AddCommGroup X] [Module R X] [AddCommGroup X']
    [Module R' X'] {μ : X → X'} {A : Submodule R X} {A' : Submodule R' X'} (h : BC μ A A') {x : X} (hx : x ∈ A) :
    μ x ∈ A' := by
  rw [h]; exact Submodule.subset_span ⟨x, hx, rfl⟩

theorem bc_span {R R' X X' : Type*} [CommRing R] [CommRing R'] [AddCommGroup X] [Module R X] [AddCommGroup X']
    [Module R' X'] {φ : R →+* R'} (μ : X →ₛₗ[φ] X') (S : Set X) :
    BC μ (Submodule.span R S) (Submodule.span R' (μ '' S)) := by
  unfold BC
  apply le_antisymm
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have h : Submodule.span R S ≤ (Submodule.span R' (μ '' S)).comap μ := by
      rw [Submodule.span_le]
      intro y hy
      exact Submodule.subset_span ⟨y, hy, rfl⟩
    exact h hx

section Maps

variable {R K R' K' : Type} [CommRing R] [CommRing K] [Algebra R K] [CommRing R'] [CommRing K'] [Algebra R' K']
  (φ : R →+* R') (φK : K →+* K') (hφ : ∀ x : R, φK (algebraMap R K x) = algebraMap R' K' (φ x))

def muS (τ : Type) : MvPolynomial τ K →ₛₗ[φ] MvPolynomial τ K' where
  toFun := MvPolynomial.map φK
  map_add' := map_add _
  map_smul' := by
    intro c P
    rw [← algebraMap_smul K c P, ← algebraMap_smul K' (φ c), smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C, hφ]

theorem muS_coe (τ : Type) : (muS φ φK hφ τ : MvPolynomial τ K → MvPolynomial τ K') = MvPolynomial.map φK := rfl

def vecS (k : ℕ) : (Fin k → K) →ₛₗ[φ] (Fin k → K') where
  toFun := fun v i => φK (v i)
  map_add' := by intro x y; funext i; simp
  map_smul' := by
    intro c x; funext i
    simp only [Pi.smul_apply, Algebra.smul_def, map_mul, hφ]

theorem map_smulK {τ : Type} (c : K) (P : MvPolynomial τ K) :
    MvPolynomial.map φK (c • P) = φK c • MvPolynomial.map φK P := by
  rw [smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C]

end Maps

theorem bc_dualWeyl {R R' : Type} [CommRing R] [CommRing R'] [IsDomain R'] (φ : R →+* R') (k n : ℕ)
    (ν : Fin n → ℕ) : BC (MvPolynomial.map φ) (dualWeyl R k n ν) (dualWeyl R' k n ν) := by
  unfold BC
  apply le_antisymm
  · obtain ⟨b', hb', h2⟩ := sSBasis R' k n ν
    rw [← hb'.2.1, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨-, -, K, sz, hsz, I, hshape, -, hbm⟩ := h2 i
    rw [hbm]
    apply Submodule.subset_span
    refine ⟨bideterminant R sz hsz I, ?_, ldlat_map_bidet φ sz hsz I⟩
    have := bidetMem R k n K sz hsz I
    rw [hshape] at this
    exact this
  · rw [Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    exact dualWeylMap R R' φ k n ν f hf

section Fields

variable {R K R' K' : Type} [CommRing R] [Field K] [Algebra R K] [CommRing R'] [IsDomain R'] [Field K']
  [Algebra R' K'] (φ : R →+* R') (φK : K →+* K')
  (hφ : ∀ x : R, φK (algebraMap R K x) = algebraMap R' K' (φ x))

include hφ in
theorem map_map_alg {τ : Type} (f : MvPolynomial τ R) :
    MvPolynomial.map (algebraMap R' K') (MvPolynomial.map φ f) =
      MvPolynomial.map φK (MvPolynomial.map (algebraMap R K) f) := by
  have h : (algebraMap R' K').comp φ = φK.comp (algebraMap R K) := RingHom.ext fun x => (hφ x).symm
  rw [MvPolynomial.map_map, MvPolynomial.map_map, h]

theorem det_map {k : ℕ} (g : Matrix (Fin k) (Fin k) K) : (g.map φK).det = φK g.det :=
  (RingHom.map_det φK g).symm

theorem inv_map {k : ℕ} (g : Matrix (Fin k) (Fin k) K) (hg : IsUnit g.det) : (g.map φK)⁻¹ = (g⁻¹).map φK := by
  apply Matrix.inv_eq_right_inv
  have h1 : g.map φK * (g⁻¹).map φK = (g * g⁻¹).map φK := (Matrix.map_mul).symm
  rw [h1, Matrix.mul_nonsing_inv g hg]
  exact Matrix.map_one φK (map_zero _) (map_one _)

def psiL (R K : Type) [CommRing R] [Field K] [Algebra R K] (m : ℕ) (lam : Fin (m + 1) → ℤ)
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) :
    MvPolynomial (Fin (m + 1) × Fin (m + 1)) R →ₗ[R] MvPolynomial (Fin (m + 1) × Fin (m + 1)) K where
  toFun := fun f => g.det ^ (-(lam (Fin.last m))) • rowAct K g⁻¹ (MvPolynomial.map (algebraMap R K) f)
  map_add' := by intro x y; rw [map_add (f := _), map_add (f := _), smul_add]
  map_smul' := by
    intro c x
    have h1 : MvPolynomial.map (algebraMap R K) (c • x) =
        algebraMap R K c • MvPolynomial.map (algebraMap R K) x := by
      rw [smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C]
    rw [RingHom.id_apply, h1, map_smul, smul_comm, algebraMap_smul]

theorem psiL_apply (R K : Type) [CommRing R] [Field K] [Algebra R K] (m : ℕ) (lam : Fin (m + 1) → ℤ)
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (f : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R) :
    psiL R K m lam g f =
      g.det ^ (-(lam (Fin.last m))) • rowAct K g⁻¹ (MvPolynomial.map (algebraMap R K) f) := rfl

theorem nablaLTw_eq_map (R K : Type) [CommRing R] [Field K] [Algebra R K] (m : ℕ) (lam : Fin (m + 1) → ℤ)
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (hg : IsUnit g.det) :
    nablaLTw R K m lam g =
      (dualWeyl R (m + 1) (m + 1) (fun t => (lam t - lam (Fin.last m)).toNat)).map (psiL R K m lam g) := by
  ext F
  rw [nablaLTwMem R K m lam g hg, Submodule.mem_map, Submodule.mem_map]
  constructor
  · rintro ⟨f, hf, hfe⟩
    refine ⟨f, hf, ?_⟩
    have h2 : (mapAlgHom (Algebra.ofId R K)).toLinearMap f = MvPolynomial.map (algebraMap R K) f := rfl
    rw [psiL_apply, ← h2, hfe, map_smul, ldlat_rowAct_inv_right rowActMul _ hg, smul_smul,
      ← zpow_add₀ hg.ne_zero, neg_add_cancel, zpow_zero, one_smul]
  · rintro ⟨f, hf, rfl⟩
    refine ⟨f, hf, ?_⟩
    have h2 : (mapAlgHom (Algebra.ofId R K)).toLinearMap f = MvPolynomial.map (algebraMap R K) f := rfl
    rw [psiL_apply, map_smul, ldlat_rowAct_inv_left rowActMul _ hg, smul_smul,
      ← zpow_add₀ hg.ne_zero, add_neg_cancel, zpow_zero, one_smul, h2]

theorem bc_map {R R' X X' Y Y' : Type*} [CommRing R] [CommRing R'] [AddCommGroup X] [Module R X] [AddCommGroup X']
    [Module R' X'] [AddCommGroup Y] [Module R Y] [AddCommGroup Y'] [Module R' Y'] {μ₁ : X → X'} {μ₂ : Y → Y'}
    {A : Submodule R X} {A' : Submodule R' X'} (h : BC μ₁ A A') (T : X →ₗ[R] Y) (T' : X' →ₗ[R'] Y')
    (hT : ∀ a, μ₂ (T a) = T' (μ₁ a)) : BC μ₂ (A.map T) (A'.map T') := by
  unfold BC at h ⊢
  rw [h, Submodule.map_span, Submodule.map_coe, ← Set.image_comp, ← Set.image_comp]
  congr 1
  exact Set.image_congr fun a _ => (hT a).symm


include hφ in
theorem bc_nablaLTw (m : ℕ) (lam : Fin (m + 1) → ℤ) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K)
    (hg : IsUnit g.det) :
    BC (MvPolynomial.map φK) (nablaLTw R K m lam g) (nablaLTw R' K' m lam (g.map φK)) := by
  have hg' : IsUnit (g.map φK).det := by rw [det_map]; exact hg.map φK
  rw [nablaLTw_eq_map R K m lam g hg, nablaLTw_eq_map R' K' m lam _ hg']
  refine bc_map (bc_dualWeyl φ (m + 1) (m + 1) _) _ _ fun f => ?_
  rw [psiL_apply, psiL_apply, map_map_alg φ φK hφ, map_smulK, ldtwist_map_rowAct, map_zpow₀, det_map,
    inv_map φK g hg]

theorem map_blockEmb {S : Type} {k n : ℕ} (s : S) (F : MvPolynomial (Fin k × Fin n) K) :
    MvPolynomial.map φK (blockEmb K s F) = blockEmb K' s (MvPolynomial.map φK F) := by
  unfold blockEmb
  exact (MvPolynomial.map_rename φK _ F)


include hφ in
theorem bc_tensorLat {S : Type} [Fintype S] {k n : ℕ} (M : S → Submodule R (MvPolynomial (Fin k × Fin n) K))
    (M' : S → Submodule R' (MvPolynomial (Fin k × Fin n) K'))
    (h : ∀ s, BC (MvPolynomial.map φK) (M s) (M' s)) :
    BC (MvPolynomial.map φK) (tensorLat R K M) (tensorLat R' K' M') := by
  classical
  have h0 := bc_span (muS φ φK hφ (S × (Fin k × Fin n)))
    {P | ∃ F : S → MvPolynomial (Fin k × Fin n) K, (∀ s, F s ∈ M s) ∧ P = ∏ s, blockEmb K s (F s)}
  rw [muS_coe] at h0
  unfold BC at h0 ⊢
  unfold tensorLat
  rw [← h0]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨F', hF', rfl⟩
    set T : S → Set (MvPolynomial (S × (Fin k × Fin n)) K') :=
      fun s => (fun F => blockEmb K' s (MvPolynomial.map φK F)) '' (M s : Set _) with hT
    have h1 : ∀ s, blockEmb K' s (F' s) ∈ Submodule.span R' (T s) := by
      intro s
      have h2 : M' s ≤ (Submodule.span R' (T s)).comap ((blockEmb K' (k := k) (n := n) s).toLinearMap.restrictScalars R') := by
        rw [h s, Submodule.span_le]
        rintro _ ⟨F, hF, rfl⟩
        exact Submodule.subset_span ⟨F, hF, rfl⟩
      exact h2 (hF' s)
    have h3 := fn_prod_mem (R := R') Finset.univ (fun s => Submodule.span R' (T s))
      (fun s => blockEmb K' s (F' s)) (fun s _ => h1 s)
    rw [Submodule.prod_span] at h3
    refine Submodule.span_mono ?_ h3
    intro P hP
    rw [Set.mem_finsetProd] at hP
    obtain ⟨gf, hgf, rfl⟩ := hP
    have h4 : ∀ s, ∃ F, F ∈ M s ∧ blockEmb K' s (MvPolynomial.map φK F) = gf s := by
      intro s
      obtain ⟨F, hF, hFe⟩ := hgf (Finset.mem_univ s)
      exact ⟨F, hF, hFe⟩
    choose F hF hFe using h4
    refine ⟨∏ s, blockEmb K s (F s), ⟨F, hF, rfl⟩, ?_⟩
    rw [map_prod]
    exact Finset.prod_congr rfl fun s _ => by rw [map_blockEmb, hFe]
  · rw [Submodule.span_le]
    rintro _ ⟨_, ⟨F, hF, rfl⟩, rfl⟩
    apply Submodule.subset_span
    refine ⟨fun s => MvPolynomial.map φK (F s), fun s => (h s).mem (hF s), ?_⟩
    rw [map_prod]
    exact Finset.prod_congr rfl fun s _ => map_blockEmb φK s (F s)


include hφ in
theorem bc_colSpan {k : ℕ} (g : Matrix (Fin k) (Fin k) K) :
    BC (vecS φ φK hφ k) (colSpan R g) (colSpan R' (g.map φK)) := by
  have h0 := bc_span (vecS φ φK hφ k) (Set.range fun c : Fin k => fun i => g i c)
  have h1 : (vecS φ φK hφ k) '' (Set.range fun c : Fin k => fun i => g i c) =
      Set.range fun c : Fin k => fun i => (g.map φK) i c := by
    rw [← Set.range_comp]; rfl
  rw [h1] at h0
  exact h0


include hφ in
theorem base_change_H0 (hinj : Function.Injective (algebraMap R K)) (hinj' : Function.Injective (algebraMap R' K'))
    (m : ℕ) (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam)
    (Λ : Submodule R (Fin (m + 1) → K)) (Λ' : Submodule R' (Fin (m + 1) → K')) (hΛ : IsLattice R Λ)
    (hb : BC (vecS φ φK hφ (m + 1)) Λ Λ') :
    BC (MvPolynomial.map φK) (H0 R m lam Λ) (H0 R' m lam Λ') := by
  obtain ⟨g, hg, rfl⟩ := hΛ
  have h1 : Λ' = colSpan R' (g.map φK) := hb.trans (bc_colSpan φ φK hφ g).symm
  have hg' : IsUnit (g.map φK).det := by rw [det_map]; exact hg.map φK
  rw [h1, H0_eq_twisted_nabla (la_indep hinj) m lam hlam g hg, H0_eq_twisted_nabla (la_indep hinj') m lam hlam _ hg']
  exact bc_nablaLTw φ φK hφ m lam g hg

end Fields

end Formalism.L2.G.Model
end
end

open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Model

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.G.LatticeSystems

section Sub

variable {R K R' K' : Type} [CommRing R] [Field K] [Algebra R K] [CommRing R'] [Field K'] [Algebra R' K']
  {φK : K →+* K'}
  {X X' : Type} [AddCommGroup X] [Module K X] [Module R X] [IsScalarTower R K X]
  [AddCommGroup X'] [Module K' X'] [Module R' X'] [IsScalarTower R' K' X']
  (μ : X →ₛₗ[φK] X') (Vs : Submodule K X) (Vs' : Submodule K' X') (hV : ∀ z ∈ Vs, μ z ∈ Vs')

def muV : Vs →ₛₗ[φK] Vs' where
  toFun := fun x => ⟨μ x.1, hV _ x.2⟩
  map_add' := by intro x y; exact Subtype.ext (map_add μ x.1 y.1)
  map_smul' := by intro c x; exact Subtype.ext (map_smulₛₗ μ c x.1)

theorem bc_comap (A : Submodule R X) (A' : Submodule R' X') (hA : ∀ z ∈ A, z ∈ Vs) (h : BC μ A A') :
    BC (muV μ Vs Vs' hV) (A.comap (Vs.subtype.restrictScalars R)) (A'.comap (Vs'.subtype.restrictScalars R')) := by
  unfold BC
  apply le_antisymm
  · intro v' hv'
    have hv2 : (v' : X') ∈ A' := hv'
    have hmap : (Submodule.span R' (muV μ Vs Vs' hV '' ((A.comap (Vs.subtype.restrictScalars R) :
        Submodule R Vs) : Set Vs))).map (Vs'.subtype.restrictScalars R') = A' := by
      rw [h, Submodule.map_span, ← Set.image_comp]
      congr 1
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x.1, hx, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨⟨z, hA z hz⟩, hz, rfl⟩
    rw [← hmap] at hv2
    obtain ⟨y, hy, hye⟩ := hv2
    have : y = v' := Subtype.ext hye
    rw [← this]
    exact hy
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact h.mem hx

theorem span_muV_top (h : BC μ Vs Vs') {I : Type} (x : Module.Basis I K Vs) :
    ⊤ ≤ Submodule.span K' (Set.range fun i => muV μ Vs Vs' hV (x i)) := by
  intro v' _
  have hv : (v' : X') ∈ Submodule.span K' (μ '' (Vs : Set X)) := by
    have h2 : Vs' ≤ Submodule.span K' (μ '' (Vs : Set X)) := le_of_eq h
    exact h2 v'.2
  have hle : Submodule.span K' (μ '' (Vs : Set X)) ≤
      (Submodule.span K' (Set.range fun i => muV μ Vs Vs' hV (x i))).map Vs'.subtype := by
    rw [Submodule.span_le]
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨muV μ Vs Vs' hV ⟨z, hz⟩, ?_, rfl⟩
    have h1 : (⟨z, hz⟩ : Vs) ∈ Submodule.span K (Set.range x) := by rw [x.span_eq]; trivial
    have h2 := (bc_span (muV μ Vs Vs' hV) (Set.range x)).mem h1
    rw [← Set.range_comp] at h2
    exact h2
  obtain ⟨y, hy, hye⟩ := hle hv
  have : y = v' := Subtype.ext hye
  rw [← this]
  exact hy

end Sub

section Dual

variable {R K R' K' : Type} [CommRing R] [Field K] [Algebra R K] [CommRing R'] [Field K'] [Algebra R' K']
  (φ : R →+* R') (φK : K →+* K') (hφ : ∀ x : R, φK (algebraMap R K x) = algebraMap R' K' (φ x))
  {V V' : Type} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  [AddCommGroup V'] [Module K' V'] [Module R' V'] [IsScalarTower R' K' V']
  (ν : V →ₛₗ[φK] V') {I : Type} [Fintype I] (x : Module.Basis I K V) (x' : Module.Basis I K' V')
  (hx : ∀ i, x' i = ν (x i))

def deltaS : Module.Dual K V →ₛₗ[φK] Module.Dual K' V' where
  toFun := fun G => x'.constr K' fun i => φK (G (x i))
  map_add' := by
    intro a b
    apply x'.ext
    intro i
    rw [LinearMap.add_apply, Module.Basis.constr_basis, Module.Basis.constr_basis, Module.Basis.constr_basis,
      LinearMap.add_apply, map_add]
  map_smul' := by
    intro c a
    apply x'.ext
    intro i
    rw [LinearMap.smul_apply, Module.Basis.constr_basis, Module.Basis.constr_basis, LinearMap.smul_apply,
      smul_eq_mul, smul_eq_mul, map_mul]

include hx in
theorem deltaS_apply (G : Module.Dual K V) (F : V) : deltaS φK x x' G (ν F) = φK (G F) := by
  have h1 : ν F = ∑ i, φK (x.repr F i) • x' i := by
    conv_lhs => rw [← x.sum_repr F]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smulₛₗ, hx]
  have h2 : G F = ∑ i, x.repr F i * G (x i) := by
    conv_lhs => rw [← x.sum_repr F]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h1, h2, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul, map_mul]
  congr 1
  exact Module.Basis.constr_basis x' K' _ i

include hφ hx in
theorem dual_mem (A : Submodule R V) (A' : Submodule R' V') (h : BC ν A A') (G : Module.Dual K V)
    (hG : G ∈ dualLat R K A) : deltaS φK x x' G ∈ dualLat R' K' A' := by
  intro v' hv'
  rw [h] at hv'
  induction hv' using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨z, hz, rfl⟩ := hy
    obtain ⟨a, ha⟩ := hG z hz
    exact ⟨φ a, by rw [deltaS_apply φK ν x x' hx, ← ha, hφ]⟩
  | zero => exact ⟨0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha⟩ := hy
    obtain ⟨b, hb⟩ := hz
    exact ⟨a + b, by rw [map_add (f := _), map_add (f := _), ha, hb]⟩
  | smul c y _ hy =>
    obtain ⟨a, ha⟩ := hy
    exact ⟨c * a, by rw [LinearMap.map_smul_of_tower, map_mul, ha, Algebra.smul_def]⟩

theorem scale_mem {A : Submodule R V} {A' : Submodule R' V'} (h : ∀ y ∈ A, ν y ∈ A') (c : K) {y : V}
    (hy : y ∈ scale c A) : ν y ∈ scale (φK c) A' := by
  obtain ⟨z, hz, rfl⟩ := hy
  exact ⟨ν z, h z hz, (map_smulₛₗ ν c z).symm⟩

end Dual

section Lat

variable {W Qq O Kf O' Kf' : Type} [CommRing W] [Field Qq] [Algebra W Qq] [CommRing O] [Field Kf] [Algebra O Kf]
  [CommRing O'] [IsDomain O'] [Field Kf'] [Algebra O' Kf']
  (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (φ : O →+* O') (φK : Kf →+* Kf')
  (hφ : ∀ x : O, φK (algebraMap O Kf x) = algebraMap O' Kf' (φ x))

theorem bc_extO (s : ℕ) {k : ℕ} (L : Submodule W (Fin k → Qq)) :
    BC (vecS φ φK hφ k) (extO O ι σ s L) (extO O' (φK.comp ι) σ s L) := by
  have h0 := bc_span (vecS φ φK hφ k) (twistVec ι σ s '' (L : Set (Fin k → Qq)))
  rw [Set.image_image] at h0
  exact h0

theorem bc_LeAt (p : ℕ) (w : O) (s : ℕ) {k : ℕ} (e : Edge W Qq k) :
    BC (vecS φ φK hφ k) (LeAt p ι σ w s e) (LeAt p (φK.comp ι) σ (φ w) s e) := by
  have h0 := bc_span (vecS φ φK hφ k) (twistVec ι σ s '' (e.src : Set (Fin k → Qq)) ∪
    (fun v => (algebraMap O Kf w)⁻¹ • twistVec ι σ s ((p : W) • v)) '' (e.tgt : Set (Fin k → Qq)))
  rw [Set.image_union, Set.image_image, Set.image_image, Submodule.span_union, Submodule.span_union] at h0
  have h1 : ∀ v : Fin k → Qq, vecS φ φK hφ k ((algebraMap O Kf w)⁻¹ • twistVec ι σ s ((p : W) • v)) =
      (algebraMap O' Kf' (φ w))⁻¹ • twistVec (φK.comp ι) σ s ((p : W) • v) := by
    intro v
    funext i
    show φK ((algebraMap O Kf w)⁻¹ * twistVec ι σ s ((p : W) • v) i) = _
    rw [map_mul, map_inv₀, hφ]
    rfl
  simp only [h1] at h0
  exact h0

theorem bc_Hten (hinj : Function.Injective (algebraMap O Kf)) (hinj' : Function.Injective (algebraMap O' Kf'))
    {n' m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ) (hd : IsDominant lam0)
    (Λ : Fin n' → Submodule O (Fin (m + 1) → Kf)) (Λ' : Fin n' → Submodule O' (Fin (m + 1) → Kf'))
    (hΛ : ∀ s, IsLattice O (Λ s)) (hb : ∀ s, BC (vecS φ φK hφ (m + 1)) (Λ s) (Λ' s)) :
    BC (MvPolynomial.map φK) (Hten O lam0 Λ) (Hten O' lam0 Λ') :=
  bc_tensorLat φ φK hφ
    (fun s => H0 O m (lamAt lam0 s) (Λ s))
    (fun s => H0 O' m (lamAt lam0 s) (Λ' s)) fun s =>
      base_change_H0 φ φK hφ hinj hinj' m (lamAt lam0 s) (kp_lamAt_antitone lam0 hd s)
        (Λ s) (Λ' s) (hΛ s) (hb s)

theorem Hten_le_V {n' m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ) (hd : IsDominant lam0)
    (Λ : Fin n' → Submodule O (Fin (m + 1) → Kf)) (hΛ : ∀ s, IsLattice O (Λ s)) :
    ∀ z ∈ Hten O lam0 Λ, z ∈ Vsp Kf lam0 := by
  have hle : Hten O lam0 Λ ≤ (Vsp Kf lam0).restrictScalars O := by
    unfold Hten tensorLat
    rw [Submodule.span_le]
    rintro _ ⟨F, hF, rfl⟩
    apply Submodule.subset_span
    refine ⟨F, fun s => ?_, rfl⟩
    have hanti := kp_lamAt_antitone lam0 hd s
    beta_reduce
    rw [if_pos hanti]
    have h1 := hF s
    beta_reduce at h1
    obtain ⟨g, hg, hge⟩ := hΛ s
    rw [hge] at h1
    exact la_nablaLTw_le _ _ _ hg _ (H0_le_twisted_nabla _ _ hanti _ hg h1)
  exact fun z hz => hle hz

theorem bc_Vsp {n' m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ) (hd : IsDominant lam0) :
    BC (MvPolynomial.map φK) (Vsp Kf lam0) (Vsp Kf' lam0) := by
  unfold Vsp
  refine bc_tensorLat φK φK (fun _ => rfl) (S := Fin n') (k := m + 1) (n := m + 1) _ _ ?_
  intro s
  have hanti := kp_lamAt_antitone lam0 hd s
  beta_reduce
  rw [if_pos hanti, if_pos hanti]
  exact bc_dualWeyl φK _ _ _

end Lat

theorem Vsp_bot (K : Type) [Field K] {n' m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ) (hd : ¬ IsDominant lam0) :
    Vsp K lam0 = ⊥ := by
  unfold IsDominant at hd
  push Not at hd
  obtain ⟨s, hs⟩ := hd
  have hs' : ¬ Antitone (lamAt lam0 s) := by
    unfold lamAt
    split_ifs with he
    · exact hs
    · intro ha
      apply hs
      intro a b hab
      have h1 := ha (Fin.rev_le_rev.2 hab)
      simp only [Fin.rev_rev] at h1
      exact neg_le_neg_iff.1 h1
  unfold Vsp tensorLat
  rw [Submodule.span_eq_bot]
  rintro _ ⟨F, hF, rfl⟩
  have h2 := hF s
  beta_reduce at h2
  rw [if_neg hs'] at h2
  apply Finset.prod_eq_zero (Finset.mem_univ s)
  rw [(Submodule.mem_bot _).1 h2, map_zero]

theorem be_sum {Kf O : Type} [Field Kf] [CommRing O] [Algebra O Kf] {n' m : ℕ} (p r : ℕ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (F : Vsp Kf lam0) {n : ℕ} (c : Fin n → O)
    (G : Fin n → Module.Dual Kf (Vsp Kf lam0)) :
    be p r lam0 F (∑ l, c l • G l) = ∑ l, algebraMap O Kf (c l) * be p r lam0 F (G l) := by
  unfold be
  rw [LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun l _ => by rw [LinearMap.smul_apply, Algebra.smul_def]

section Main

variable {p n' : ℕ} {W Qq O Kf O' Kf' : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Field Kf'] [Algebra O' Kf']
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} {φ : O →+* O'} {φK : Kf →+* Kf'}

theorem lpAt_nondom (m r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ) (hd : ¬ IsDominant lam0) (t D : ℕ) (κ : ℝ)
    (cStar : ℕ) (L : Submodule W (Fin (m + 1) → Qq)) :
    LPprimeAt (O := O) p n' ι σ w r lam0 t D κ cStar L := by
  refine ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, 0, ?_, 0, 0,
    fun _ j => j.elim0⟩
  have h0 : dimV Kf lam0 = 0 := by
    unfold dimV
    rw [Vsp_bot Kf lam0 hd]
    exact finrank_bot _ _
  rw [h0]
  simp

theorem lpAt_dom (hφ : ∀ x : O, φK (algebraMap O Kf x) = algebraMap O' Kf' (φ x))
    (hS : HidaSetting p n' W Qq O Kf ι σ j w) (hS' : HidaSetting p n' W Qq O' Kf' (φK.comp ι) σ (φ.comp j) (φ w))
    (m r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ) (hd : IsDominant lam0) (t D : ℕ) (κ : ℝ) (cStar : ℕ)
    (L : Submodule W (Fin (m + 1) → Qq)) (hL : IsLattice W L)
    (h : LPprimeAt (O := O) p n' ι σ w r lam0 t D κ cStar L) :
    LPprimeAt (O := O') p n' (φK.comp ι) σ (φ w) r lam0 t D κ cStar L := by
  classical
  have hinj : Function.Injective (algebraMap O Kf) := haveI := hS.frac_O; IsFractionRing.injective O Kf
  have hinj' : Function.Injective (algebraMap O' Kf') := haveI := hS'.frac_O; IsFractionRing.injective O' Kf'
  have bV := bc_Vsp φK lam0 hd
  set μ : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf →ₛₗ[φK]
      MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf' := muS φK φK (fun _ => rfl) _ with hμ
  have hV : ∀ z ∈ Vsp Kf lam0, μ z ∈ Vsp Kf' lam0 := fun z hz => bV.mem hz
  set ν := muV μ (Vsp Kf lam0) (Vsp Kf' lam0) hV with hν
  have hlatE : ∀ (s : ℕ) (A : Submodule W (Fin (m + 1) → Qq)), IsLattice W A → IsLattice O (extO O ι σ s A) :=
    fun s A hA => je_extO_lat (mkG hS m r lam0 hd) (0 : Fin 1) s A hA
  have hlatL : ∀ (s : ℕ) (e : Edge W Qq (m + 1)), IsEdge p n' r e → IsLattice O (LeAt p ι σ w s e) :=
    fun s e he => je_LeAt_lat (mkG hS m r lam0 hd) (0 : Fin 1) s e he
  have hHL : ∀ A : Submodule W (Fin (m + 1) → Qq), IsLattice W A →
      BC ν (HL (O := O) ι σ lam0 A) (HL (O := O') (φK.comp ι) σ lam0 A) := fun A hA =>
    bc_comap μ _ _ hV _ _ (Hten_le_V lam0 hd _ fun s => hlatE s.val A hA)
      (bc_Hten φ φK hφ hinj hinj' lam0 hd _ _ (fun s => hlatE s.val A hA) fun s => bc_extO ι σ φ φK hφ s.val A)
  have hHLe : ∀ e : Edge W Qq (m + 1), IsEdge p n' r e →
      BC ν (HLe (O := O) p ι σ w lam0 e) (HLe (O := O') p (φK.comp ι) σ (φ w) lam0 e) := fun e he =>
    bc_comap μ _ _ hV _ _ (Hten_le_V lam0 hd _ fun s => hlatL s.val e he)
      (bc_Hten φ φK hφ hinj hinj' lam0 hd _ _ (fun s => hlatL s.val e he)
        fun s => bc_LeAt ι σ φ φK hφ p w s.val e)
  obtain ⟨I0, hI0, b0, -⟩ := jm_HL_basis (mkG hS m r lam0 hd) (0 : Fin 1) L hL
  have : Module.Finite Kf (Vsp Kf lam0) := Module.Finite.of_basis b0
  have hdim : dimV Kf' lam0 = dimV Kf lam0 :=
    (jr_dim (mkG hS' m r lam0 hd) (0 : Fin 1)).symm.trans (jr_dim (mkG hS m r lam0 hd) (0 : Fin 1))
  have hcard : Fintype.card (Fin (Module.finrank Kf (Vsp Kf lam0))) = Module.finrank Kf' (Vsp Kf' lam0) := by
    rw [Fintype.card_fin]; exact hdim.symm
  set x := Module.finBasis Kf (Vsp Kf lam0) with hxdef
  set x' := basisOfTopLeSpanOfCardEqFinrank (fun i => ν (x i)) (span_muV_top μ _ _ hV bV x) hcard with hx'def
  have hx : ∀ i, x' i = ν (x i) := fun i =>
    congrFun (coe_basisOfTopLeSpanOfCardEqFinrank (fun i => ν (x i)) (span_muV_top μ _ _ hV bV x) hcard) i
  set δ := deltaS φK x x' with hδ
  have hwz : ∀ z : ℤ, φK (algebraMap O Kf w ^ z) = algebraMap O' Kf' (φ w) ^ z := fun z => by
    rw [map_zpow₀, hφ]
  have hRe : ∀ e : Edge W Qq (m + 1), IsEdge p n' r e → ∀ y ∈ Re (O := O) p ι σ w r lam0 e,
      ν y ∈ Re (O := O') p (φK.comp ι) σ (φ w) r lam0 e := by
    intro e he y hy
    have h1 := scale_mem φK ν (fun y hy => (hHLe e he).mem hy) _ hy
    rw [hwz] at h1
    exact h1
  have hRe' : ∀ e : Edge W Qq (m + 1), IsEdge p n' r e → ∀ G ∈ Re' (O := O) p ι σ w r lam0 e,
      δ G ∈ Re' (O := O') p (φK.comp ι) σ (φ w) r lam0 e := by
    intro e he G hG
    have h1 := scale_mem φK δ (fun G hG => dual_mem φ φK hφ ν x x' hx _ _ (hHLe e he) G hG) _ hG
    rw [hwz] at h1
    exact h1
  have hN : ∀ A : Submodule W (Fin (m + 1) → Qq), IsLattice W A → ∀ y ∈ Nsrc (O := O) p n' ι σ w r lam0 t A,
      ν y ∈ Nsrc (O := O') p n' (φK.comp ι) σ (φ w) r lam0 t A := by
    intro A hA y hy
    refine Submodule.mem_inf.2 ⟨?_, ?_⟩
    · have h1 := scale_mem φK ν (fun y hy => (hHL A hA).mem hy) _ (Submodule.mem_inf.1 hy).1
      rw [hwz] at h1
      exact h1
    · rw [Submodule.mem_iInf]
      intro e
      rw [Submodule.mem_iInf]
      intro he
      exact hRe e he.1 y ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 (Submodule.mem_inf.1 hy).2 e) he)
  have hN' : ∀ A : Submodule W (Fin (m + 1) → Qq), IsLattice W A → ∀ G ∈ Ntgt (O := O) p n' ι σ w r lam0 t A,
      δ G ∈ Ntgt (O := O') p n' (φK.comp ι) σ (φ w) r lam0 t A := by
    intro A hA G hG
    refine Submodule.mem_inf.2 ⟨?_, ?_⟩
    · have h1 := scale_mem φK δ (fun G hG => dual_mem φ φK hφ ν x x' hx _ _ (hHL A hA) G hG) _
        (Submodule.mem_inf.1 hG).1
      rw [hwz] at h1
      exact h1
    · rw [Submodule.mem_iInf]
      intro e
      rw [Submodule.mem_iInf]
      intro he
      exact hRe' e he.1 G ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 (Submodule.mem_inf.1 hG).2 e) he)
  obtain ⟨M, e, F, h1, h2, h3, n, hn, u, Mat, hu⟩ := h
  refine ⟨M, e, fun i => ν (F i), h1, fun i => hN _ (h1 i).1.1 _ (h2 i), ?_, n, ?_, ?_⟩
  · intro i e' he' hs hne
    have h4 := scale_mem φK ν (hRe e' he') _ (h3 i e' he' hs hne)
    rw [hwz] at h4
    exact h4
  · rw [hdim]; exact hn
  · have hbe : ∀ (i : Fin M) (Gd : Module.Dual Kf (Vsp Kf lam0)),
        be p r lam0 (ν (F i)) (δ Gd) = φK (be p r lam0 (F i) Gd) := by
      intro i Gd
      unfold be
      have h5 : ((p : Kf') ^ Ar r lam0) • ν (F i) = ν (((p : Kf) ^ Ar r lam0) • F i) := by
        rw [map_smulₛₗ, map_zpow₀, map_natCast]
      rw [h5]
      exact deltaS_apply φK ν x x' hx Gd _
    refine ⟨Fintype.linearCombination O' (fun l : Fin n =>
      (⟨δ (u (Pi.single l 1)).1, hN' L hL _ (u (Pi.single l 1)).2⟩ :
        ↥(Ntgt (O := O') p n' (φK.comp ι) σ (φ w) r lam0 t L))), Mat.map φ, ?_⟩
    intro y jj
    have e1 : ∀ i : Fin M, be p r lam0 (ν (F i)) ((Fintype.linearCombination O' (fun l : Fin n =>
        (⟨δ (u (Pi.single l 1)).1, hN' L hL _ (u (Pi.single l 1)).2⟩ :
          ↥(Ntgt (O := O') p n' (φK.comp ι) σ (φ w) r lam0 t L))) y :
          ↥(Ntgt (O := O') p n' (φK.comp ι) σ (φ w) r lam0 t L)) : Module.Dual Kf' (Vsp Kf' lam0)) =
        ∑ l, algebraMap O' Kf' (y l) * φK (be p r lam0 (F i) (u (Pi.single l 1)).1) := by
      intro i
      rw [Fintype.linearCombination_apply, Submodule.coe_sum]
      simp only [Submodule.coe_smul]
      rw [be_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [hbe]
    have e2 : ∀ l : Fin n, ∑ i, algebraMap O' Kf' (φ (Mat jj i)) * φK (be p r lam0 (F i) (u (Pi.single l 1)).1) =
        algebraMap O' Kf' (φ ((p : O) ^ D * (Pi.single l (1 : O) : Fin n → O) jj)) := by
      intro l
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hφ, ← hu (Pi.single l 1) jj, map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_mul, hφ]
    simp only [e1, Matrix.map_apply]
    calc ∑ i, algebraMap O' Kf' (φ (Mat jj i)) *
          ∑ l, algebraMap O' Kf' (y l) * φK (be p r lam0 (F i) (u (Pi.single l 1)).1)
        = ∑ l, algebraMap O' Kf' (y l) *
          ∑ i, algebraMap O' Kf' (φ (Mat jj i)) * φK (be p r lam0 (F i) (u (Pi.single l 1)).1) := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => by ring
      _ = ∑ l, algebraMap O' Kf' (y l) *
          algebraMap O' Kf' (φ ((p : O) ^ D * (Pi.single l (1 : O) : Fin n → O) jj)) := by
          simp only [e2]
      _ = algebraMap O' Kf' ((p : O') ^ D * y jj) := by
          rw [Finset.sum_eq_single jj]
          · rw [Pi.single_eq_same, mul_one, map_pow, map_natCast, ← map_mul, mul_comm]
          · intro l _ hl
            rw [Pi.single_eq_of_ne hl.symm, mul_zero, map_zero, map_zero, mul_zero]
          · intro hjj
            exact absurd (Finset.mem_univ jj) hjj

end Main

theorem lpBaseChange : Formalism.MainNotions.G.LPBaseChange := by
  intro p n' W Qq O Kf O' Kf' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ι σ j w φ φK hφ _ hS hS' m r lam0 t D κ cStar h
  refine ⟨h.1, fun L hL => ?_⟩
  by_cases hd : IsDominant lam0
  · exact lpAt_dom hφ hS hS' m r lam0 hd t D κ cStar L hL (h.2 L hL)
  · exact lpAt_nondom m r lam0 hd t D κ cStar L

end Formalism.L2.G.Model
end
end

noncomputable section

namespace Formalism.L2.G

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G

structure Loc : Prop where

  p14R : ∀ D : D7, SecondTheoremReduced D

theorem extremal_projector_tools_of_loc (h : Loc) : ExtremalProjectorTools where
  extremalProjectorAlt := ExtremalProjector.extremal_projector_statement

theorem local_model_results (h : Loc) : Loc6 := {
  p14R := h.p14R
  p39B := SelectionLemmas.Pf.secondPartClosed
  rationalPlanesClauseThree := Joints.Lit.weyl_dimension_formula_index_sets
  rationalPlanesClauseFour := Joints.Lit.branching_rule_count_form
  rationalPlanesClauseFive := Joints.Lit.pieri_rule_count_form
  dualInclusionLattices := Model.dualInclusionLattices
  bePerfect := Model.bePerfect
  lpOneEvery := Model.lPOneEvery
  flatTop := Model.flatTop
  dualHeightBasis := Model.dualHeightBasis
  hlSpans := Model.hlSpans
  testSide := Model.testSide
  wittIdent := WittPI.wittIdentity_holds
  criterionClauseElevenB := Joints.joint_types_corollary_sentences
  criterionClauseTwentyTwo := Joints.coarse_units_lemma
  criterionClauseThirtyFive := Model.fewBadOrbits
  criterionClauseThirtySix := Model.products_sections_integral }

theorem local_flatness_results (h : Loc) : Loc8 := {
  p13B := flipOneThree.Pf.theorem_I_closed_form_holds
  p13A := GramWindowAlt.theorem_A_closed_form_holds
  p15 := ColumnSystems.Pf.extendedClosedForm
  windowClauseTwo := Model.gl_branching_dimension
  windowClauseThree := Model.weyl_dual_weight_admissible
  lWeylV := Model.weylV_proved
  tFlatHH := Model.flatHH
  tCartanDomain := Model.cartanDomain_proved
  tCartanOnto := Model.cartanOnto_proved
  tKP2 := Joints.saturated_restriction_holds
  tKP3 := Joints.restriction_dimension_holds
  tRES := CountingStatementReduction.residue_division_transfer }

def LocalDataSystem {D : D7} {L : SizeData₂ D} (X : Inst D L) (Y : LatInst D) (low : D.what₂.Word → D.what₂.places.Pl → ℝ) : Prop :=
  ∀ hT : GatTies D, LatTied hT X Y → ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    ∃ (_ : Fact (D.what₂.places.resChar w).Prime) (std : _) (vp : _) (unif : _) (eO : _) (eO_spec : _) (dG : _)
      (dG_spec : _) (om : _) (Y5 : FormalGroupSystem.Pend (FormalGroupSystem.Sys.mk (D.gat u w hg) (Y.Fl u w hg) (Y.Lv u w hg)
        (Y.Ch u w hg) std vp unif eO eO_spec dG dG_spec om)),
      (FormalGroupSystem.adm1 D → FormalGroupSystem.adm6 D _ Y5 → FormalGroupSystem.admitted D _ Y5) ∧
      ∃ Fn : Fin (D.gat u w hg).P.nV → ℕ → ℝ,
        (∀ v, v ∉ (reps X (D.what₂.places.resChar w)).image (Y.vOf u w hg) → ∀ j < D.R.m, Y5.LowAt j v (Fn v (j + 1))) ∧
        low u w ≤ (∑ j ∈ Finset.Icc 1 D.R.m,
          ∑ v ∈ Finset.univ \ (reps X (D.what₂.places.resChar w)).image (Y.vOf u w hg), Fn v j) -
            ∑ j ∈ Finset.range D.R.m, (dG j : ℝ)

theorem hypIAt_ev {eps : ℝ} (Fm : FamP eps) (hLa : 0 < Fm.GK.La) (hCN : CornerGLContinuity.FamilyWindowLogBound Fm) :
    Ev Fm fun x i => Joints.HypIAt (Fm.D x i) (Fm.L x i) (Fm.Gx x i) Fm.GK := by
  obtain ⟨i0⟩ := Fm.Ix_zero
  have heps : 0 < eps := by
    have := (Fm.L 0 i0).sc.eps_pos
    rwa [Fm.L_eps] at this
  obtain ⟨C31, _, h1⟩ := TopChoiceBounds.family_uniform_constant_holds Fm
  have h1' : Ev Fm fun x i => AuxBlock8.adm1 (Fm.D x i) (Fm.L x i) (Fm.Gx x i) C31 := h1
  have h4 : Ev Fm fun x i => AuxBlock8.ArchimedeanSignatureMatching (Fm.D x i) (Fm.L x i) Fm.GK := TopChoiceBounds.family_band_ratio_statement Fm hCN
  have h5 := family_sizes_bound Fm hLa (eps / 48) (by positivity)
  have hx31 : Ev Fm fun x i => CornerGLContinuity.LargeScaleConditions (Fm.D x i) (Fm.L x i) := TopChoiceBounds.family_large_scale_conditions_hold Fm
  obtain ⟨xa, hA⟩ := Filter.eventually_atTop.1 ((AuxBlock8.Pf.numMean_ev eps Fm.GK Fm.GK_nonneg 0 le_rfl).and
    (AuxBlock8.Pf.restHypI_ev eps Fm.GK Fm.GK_nonneg 0 C31))
  obtain ⟨x0, h⟩ := ((((h1'.and h4).and h5).and hx31).and (eventually_sizes_admitted Fm)).and (Ev.x1 Fm)
  refine ⟨max x0 xa, fun x hx i => ?_⟩
  obtain ⟨⟨⟨⟨⟨a1, a4⟩, a5⟩, a31⟩, aSz⟩, hx1⟩ := h x (le_trans (le_max_left _ _) hx) i
  obtain ⟨hNM, hRH⟩ := hA x (le_trans (le_max_right _ _) hx)
  have hxx := Fm.L_x x i hx1
  have hee := Fm.L_eps x i
  have NM := hNM (Fm.D x i) (Fm.L x i) hxx hee aSz.1 a5
  have ZetaZeros := hRH (Fm.D x i) (Fm.L x i) (Fm.Gx x i) hxx hee aSz a5 a4 a1 NM
  obtain ⟨w⟩ := exists_place (Fm.D x i)
  obtain ⟨_, _, _, _, _, _, hLaG⟩ := Fm.fills x hx1 i w
  intro p hc hp0 t0 ht0
  exact ⟨a31.1, a31.2.2 _ hc.2.2.2.1, ZetaZeros p hc hp0 t0 ht0, windows_of Fm.GK (Fm.params x hx1 i) hLaG p t0⟩

structure Fam {eps : ℝ} (Fm : FamP eps) : Prop where

  gatE : Ev Fm fun x i => TrivialStabiliserFiniteClasses (Fm.D x i)

  stdSub : Ev Fm fun x i => Joints.StdSubAt (Fm.D x i)

  localSystemLowTerm : Ev Fm fun x i => LocalDataSystem (Fm.Gx x i) (Fm.Gy x i) (AuxBlock8.lowU (Fm.D x i))

  localSystemSizeLowTerm : Ev Fm fun x i => LocalDataSystem (Fm.Gx x i) (Fm.Gy x i) (lowFE (Fm.L x i))

section NoKer

variable {D : D7} {L : SizeData₂ D}

def zeroCh (Y : LatInst D) : LatInst D where
  vOf := Y.vOf
  Fl := Y.Fl
  Lv := Y.Lv
  Ch := fun _ _ _ => ⟨fun _ => 0⟩
  Vram := Y.Vram

theorem chainK_zero {p : ℕ} {G : GAtP p} {Fl : Fills G} (Lv : Levels Fl) :
    ∀ m : ℕ, 1 ≤ m → ∀ F : Lv.Fm 0, (⟨fun _ => 0⟩ : Chain Lv).chainK m F = 0
  | 0, h, _ => absurd h (by omega)
  | n + 1, _, F => by simp [Chain.chainK]

theorem vKge_zero (Y : LatInst D) (hm : 1 ≤ D.R.m) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (F : (D.gat u w hg).Fn) (g : ℝ) :
    (zeroCh Y).vKge u w hg F g := by
  have h0 : ((zeroCh Y).Ch u w hg).chainK D.R.m F = 0 := chainK_zero _ D.R.m hm F
  unfold LatInst.vKge vGeLat
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (D.gat u w hg).O
  refine ⟨ϖ, hϖ, ?_⟩
  rw [h0]
  exact Submodule.zero_mem _

theorem admissible_family_no_kernel {eps : ℝ} (Fm : FamP eps)
    (h1 : Adm1F Fm) (h2 : Adm2F Fm) (h3 : Adm3F Fm) (h4 : Adm4F Fm) (h5 : Adm5F Fm) (h6 : Adm6F Fm) (h7 : Adm7F Fm)
    (h8 : Adm8F Fm) (h9 : Adm9F Fm)
    (hE : Ev Fm fun x i => TrivialStabiliserFiniteClasses (Fm.D x i)) (hY : Ev Fm fun x i => OperatorsPreserveLattices (Fm.D x i))
    (hLP : Ev Fm fun x i => CornerGLContinuity.OrbitLatticeBounds (Fm.D x i) (Fm.L x i) (Fm.Gx x i) (Fm.Gy x i) Fm.GK)
    (hEp : Ev Fm fun x i => CornerGLContinuity.LatticeSandwich (Fm.D x i) (Fm.L x i) (Fm.Gx x i))
    (hd : NPDescF Fm) : AuxBlock8.AdmF Fm Fm.GK Fm.Gx (fun x i => zeroCh (Fm.Gy x i)) ∧
    Ev Fm fun x i => AuxBlock8.unitBoundAtTwistedPlaces (Fm.D x i) (Fm.L x i) (Fm.Gx x i) (zeroCh (Fm.Gy x i)) Fm.GK ∧
      AuxBlock8.admG1 (Fm.D x i) (Fm.L x i) (Fm.Gx x i) (zeroCh (Fm.Gy x i)) Fm.GK := by
  have hG1 : Ev Fm fun x i => AuxBlock8.unitBoundAtTwistedPlaces (Fm.D x i) (Fm.L x i) (Fm.Gx x i) (zeroCh (Fm.Gy x i)) Fm.GK ∧
      AuxBlock8.admG1 (Fm.D x i) (Fm.L x i) (Fm.Gx x i) (zeroCh (Fm.Gy x i)) Fm.GK := by
    obtain ⟨x0, h⟩ := ((((hE.and hY).and hLP).and hEp).and (eventually_large_scale_bound Fm)).and (Ev.x1 Fm)
    refine ⟨x0, fun x hx i => ?_⟩
    obtain ⟨⟨⟨⟨⟨hE, hY⟩, hLP⟩, hEp⟩, hB⟩, hx1⟩ := h x hx i
    have hU : AuxBlock8.unitBoundAtTwistedPlaces (Fm.D x i) (Fm.L x i) (Fm.Gx x i) (zeroCh (Fm.Gy x i)) Fm.GK := by
      intro _ _ u w hg _ _ _ _ _ _ _
      exact vKge_zero _ hB.1 u w hg _ _
    have hS1 : CornerGLContinuity.ServiceLowerValuation (Fm.D x i) (Fm.L x i) (Fm.Gx x i) (zeroCh (Fm.Gy x i)) Fm.GK := by
      intro _ _ u w hg _ _
      exact vKge_zero _ hB.1 u w hg _ _
    exact ⟨hU, TopChoiceBounds.gluing_statement_of_proof _ _ _ (TopChoiceBounds.gluing_statement_holds Fm.GK (Fm.Gx x i) (zeroCh (Fm.Gy x i))
      ⟨hU, stability_of_trivial_stabilisers hE, service_statement_of_stability _ _ _ (FormalGroupSystem.Pf.stmt6G _ _ _ _ _) hE hY, hLP, hEp,
        saturated_ramified_lattice _ (Fm.ex x hx1 i).cmp (Fm.ex x hx1 i).lat.vram, hB, hS1⟩).1⟩
  have hA : AuxBlock8.AdmF Fm Fm.GK Fm.Gx (fun x i => zeroCh (Fm.Gy x i)) := by
    obtain ⟨C31, hC31, h1⟩ := h1
    obtain ⟨Cm, hCm, h8⟩ := h8
    obtain ⟨Ce, hCe, h9⟩ := h9
    refine ⟨C31, Ce, Cm, hC31, hCe, hCm, fun δ hδ => ?_⟩
    obtain ⟨x0, h⟩ := ((((((((((h1.and h2).and h3).and h4).and (h5 δ hδ)).and h6).and h7).and h8).and h9).and
      hG1).and (eventually_sizes_admitted Fm))
    refine ⟨max x0 2, lt_of_lt_of_le one_lt_two (le_max_right _ _), fun x hx i => ?_⟩
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩, aU, aG⟩, aS⟩ :=
      h x (le_trans (le_max_left _ _) hx) i
    exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, aU, aG, aS⟩
  exact ⟨hA, hG1⟩

theorem linkG_without_kernels {eps : ℝ} (Fm : FamP eps)
    (h1 : Adm1F Fm) (h2 : Adm2F Fm) (h3 : Adm3F Fm) (h4 : Adm4F Fm) (h5 : Adm5F Fm) (h6 : Adm6F Fm) (h7 : Adm7F Fm)
    (h8 : Adm8F Fm) (h9 : Adm9F Fm)
    (hE : Ev Fm fun x i => TrivialStabiliserFiniteClasses (Fm.D x i)) (hY : Ev Fm fun x i => OperatorsPreserveLattices (Fm.D x i))
    (hLP : Ev Fm fun x i => CornerGLContinuity.OrbitLatticeBounds (Fm.D x i) (Fm.L x i) (Fm.Gx x i) (Fm.Gy x i) Fm.GK)
    (hEp : Ev Fm fun x i => CornerGLContinuity.LatticeSandwich (Fm.D x i) (Fm.L x i) (Fm.Gx x i))
    (hd : NPDescF Fm) : LinkG Fm := by
  obtain ⟨hA, hG1⟩ := admissible_family_no_kernel Fm h1 h2 h3 h4 h5 h6 h7 h8 h9 hE hY hLP hEp hd
  obtain ⟨C, δ, hδ, hP'⟩ := AuxBlock8.Pf.stmtF Fm Fm.GK Fm.GK_nonneg Fm.Gx _ hA
  have hP'' : Ev Fm fun x i => AuxBlock8.Conclusion₂ (Fm.D x i) (Fm.L x i) (Fm.Gx x i) Fm.GK C ((Fm.L x i).sc.b ^ δ x) := hP'
  obtain ⟨x0, h⟩ := (((((hP''.and hG1).and (servedGIdx_ev Fm)).and (svBound_ev Fm)).and (nuServed_ev Fm)).and
    (sizeDataLat_ev Fm hd)).and (Ev.x1 Fm)
  refine ⟨4 * |C| + 1, x0, δ, hδ, fun x hx i => ?_⟩
  obtain ⟨⟨⟨⟨⟨⟨hp, hg⟩, hs⟩, hv⟩, hi⟩, hf⟩, hx1⟩ := h x hx i
  exact linkG_at_of (Fm.Gx x i) (zeroCh (Fm.Gy x i)) Fm.GK Fm.GK_nonneg C _ (Fm.gatT x i) (Fm.fills x hx1 i)
    hf (Fm.supp_sat x hx1 i) (Fm.latTied x hx1 i) (Fm.nuDef x hx1 i) hp.1 hp.2.1 hp.2.2.2.2.1 hg.2 hs hv hi

theorem linkG_fam_noKer {eps : ℝ} (Fm : FamP eps) (h14 : SecondTheoremAtFamily Fm) (h13 : FirstTheoremAtFamily Fm)
    (hLa : 0 < Fm.GK.La) (hCe : 1 ≤ Fm.cX.Ce) (hCb : Ev Fm fun x i => CbLarge Fm.GK (Fm.L x i).sc)
    (hE : Ev Fm fun x i => TrivialStabiliserFiniteClasses (Fm.D x i)) (hS : Ev Fm fun x i => Joints.StdSubAt (Fm.D x i))
    (h2 : Adm2F Fm) (hd : NPDescF Fm) (hCN : CornerGLContinuity.FamilyWindowLogBound Fm) : LinkG Fm := by
  obtain ⟨C, hC0, a1, a2, a3, a4, a5, a6, hp14⟩ := h14
  obtain ⟨CH, C', b0, b1, b2, b3, b4, b5, b6, hp13⟩ := h13
  have h6 := family_second_bound_of_theorem Fm C hC0 a1 a2 a3 a4 a5 a6 hp14
  have h7 := family_kappa_bound Fm (kapIDefF Fm)
  have h8 := family_first_bound_of_theorem Fm CH C' (kapIDefF Fm) b0 b1 b2 b3 b4 b5 b6 hp13
  have hCe0 : 0 ≤ Fm.cX.Ce := le_trans zero_le_one hCe
  obtain ⟨C₅, h59⟩ := UnusedSlot33.field_lemmas_except_seven
  have hO : CornerGLContinuity.FamilyGlobalOrderEstimate Fm 100 := fun x i => (h59 (Fm.D x i) (Fm.L x i).sc).2.2.2.1
  have h9 : Adm9F Fm := by
    obtain ⟨x1, hx1⟩ := Ev.x1 Fm
    exact ⟨Fm.cX.Ce, hCe0, x1, fun x hx i => Joints.weyl_sandwich_of_factors _ _ _ Fm.cX.Ce hCe0 (Fm.ex x (hx1 x hx i) i).ep_def
      (Joints.weylSandwich_of_model _ (Model.modelSandwichG_of_ties _ (Fm.gatT x i)))
      (Joints.expBound_of _ _ _ Fm.cX.Ce hCe (Fm.ex x (hx1 x hx i) i).ep_def (Fm.params x (hx1 x hx i) i)
        (Fm.gatT x i))⟩
  have hLP : Ev Fm fun x i => CornerGLContinuity.OrbitLatticeBounds (Fm.D x i) (Fm.L x i) (Fm.Gx x i) (Fm.Gy x i) Fm.GK := by
    obtain ⟨x0, h⟩ := ((((h6.and h7).and hS).and (hypIAt_ev Fm hLa hCN)).and
      (Joints.hypIIAt_fam Fm hCN)).and hCb
    exact ⟨x0, fun x hx i => Joints.linear_programming_input_of_hypotheses _ _ _ _ _ (h x hx i).1.1.1.1.1 (h x hx i).1.1.1.1.2
        (h x hx i).1.1.1.2 Model.lpBaseChange (h x hx i).1.1.2 (h x hx i).1.2
        (rho_le_rhoB _ _ _ Fm.GK_nonneg.2.1 (La_nonneg Fm.GK_nonneg.1 _) (h x hx i).2)⟩
  have hEp : Ev Fm fun x i => CornerGLContinuity.LatticeSandwich (Fm.D x i) (Fm.L x i) (Fm.Gx x i) := by
    obtain ⟨Ce, _, x0, h⟩ := id h9
    exact ⟨x0, fun x hx i => TopChoiceBounds.sandwich_of_exponent_clause _ Ce (Fm.gatT x i) (h x hx i)⟩
  exact linkG_without_kernels Fm (family_first_lemma Fm) h2 (family_orders_first_part Fm 100 (TopChoiceBounds.family_order_bound_holds Fm 100) hO)
    (family_orders_bound_of_lemma Fm (TopChoiceBounds.family_band_ratio_holds Fm) hCN) (family_sizes_bound Fm hLa) h6 h7 h8 h9 hE
    ⟨0, fun x _ i u w hg => Model.operators_preserve_lattices _ _⟩ hLP hEp hd

theorem link_of_local_closed (𝒞 : FamClass) (h : Loc)
    (hE : Closed 𝒞 fun Fm _ => Ev Fm fun x i => TrivialStabiliserFiniteClasses (Fm.D x i))
    (hS : Closed 𝒞 fun Fm _ => Ev Fm fun x i => Joints.StdSubAt (Fm.D x i))
    (h2 : Closed 𝒞 fun Fm _ => Adm2F Fm) (hd : Closed 𝒞 fun Fm _ => NPDescF Fm) :
    Closed 𝒞 fun Fm _ => LinkG Fm :=
  ((((((((((second_theorem_closed_form 𝒞 (second_theorem_absolute_constant (extremal_projector_tools_of_loc h) (local_model_results h))).and
    (first_theorem_closed_form 𝒞 (first_theorem_threshold_functions (extremal_projector_tools_of_loc h)
      (loc8All_of (extremal_projector_tools_of_loc h) (local_model_results h) (local_flatness_results h))))).and (signs_closed 𝒞)).and
    (ones_closed 𝒞)).and (cb_closed 𝒞)).and hE).and hS).and h2).and hd).and (TopChoiceBounds.family_log_bound_closed 𝒞)).imp
    fun Fm _ _ h => linkG_fam_noKer Fm h.1.1.1.1.1.1.1.1.1 h.1.1.1.1.1.1.1.1.2 h.1.1.1.1.1.1.1.2.1
      h.1.1.1.1.1.1.2.2.2 h.1.1.1.1.1.2 h.1.1.1.1.2 h.1.1.1.2 h.1.1.2 h.1.2 h.2

theorem loc_proved : Loc := by
  exact ⟨fun D => Formalism.MainNotions.G.criterion_restricted_of_closed D (Formalism.MainNotions.TraceSpectra.stmtE D)⟩

end NoKer

end Formalism.L2.G

end
