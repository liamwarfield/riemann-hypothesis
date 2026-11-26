module

public import GroundTheory.AutomorphicForms.SupercuspidalCoefficients

@[expose] public section

section -- merged from GroundTheory.AutomorphicForms.CuspidalSplittingCoeff
section -- merged from GroundTheory.AutomorphicForms.CuspidalSplittingSums
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

namespace Parabolic

open Function
open scoped Pointwise

section Sums

variable {G : Type*} [Group G] (H : Subgroup G) {M : Type*} [AddCommMonoid M]

def quotSum (Φ : G → M) : M :=
  ∑ᶠ q : G ⧸ H, Φ q.out

variable {H}

theorem quotSum_def (Φ : G → M) : quotSum H Φ = ∑ᶠ q : G ⧸ H, Φ q.out := rfl

theorem apply_out_mk {X : Type*} {Φ : G → X} (hΦ : ∀ g, ∀ h ∈ H, Φ (g * h) = Φ g) (g : G) :
    Φ (QuotientGroup.mk g : G ⧸ H).out = Φ g := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
  rw [hh, hΦ g h h.2]

theorem quotSum_mul_left {Φ : G → M} (hΦ : ∀ g, ∀ h ∈ H, Φ (g * h) = Φ g) (x : G) :
    quotSum H (fun g => Φ (x * g)) = quotSum H Φ := by
  unfold quotSum
  calc ∑ᶠ q : G ⧸ H, Φ (x * q.out)
      = ∑ᶠ q : G ⧸ H, (fun q' : G ⧸ H => Φ q'.out) (MulAction.toPerm x q) := by
        refine finsum_congr fun q => ?_
        have hq : (MulAction.toPerm x q : G ⧸ H) = QuotientGroup.mk (x * q.out) := by
          rw [MulAction.toPerm_apply]
          conv_lhs => rw [← QuotientGroup.out_eq' q]
          rfl
        simp only [hq, apply_out_mk hΦ]
    _ = ∑ᶠ q : G ⧸ H, Φ q.out := finsum_comp_equiv (MulAction.toPerm x) (f := fun q' : G ⧸ H => Φ q'.out)

theorem quotSum_congr {Φ Ψ : G → M} (h : ∀ g, Φ g = Ψ g) : quotSum H Φ = quotSum H Ψ := by
  unfold quotSum
  exact finsum_congr fun q => h _

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem finite_support_quotSum (hH : IsOpen (H : Set G)) (hZH : Subgroup.center G ≤ H)
    {Φ : G → M} {C : Set G} (hC : IsCompact C)
    (hsupp : support Φ ⊆ (Subgroup.center G : Set G) * C) :
    (support fun q : G ⧸ H => Φ q.out).Finite := by
  have : DiscreteTopology (G ⧸ H) := QuotientGroup.discreteTopology hH
  refine ((hC.image QuotientGroup.continuous_mk).finite_of_discrete).subset ?_
  intro q hq
  obtain ⟨z, hz, c, hc, hzc⟩ := hsupp hq
  replace hzc : z * c = q.out := hzc
  refine ⟨c, hc, ?_⟩
  rw [← QuotientGroup.out_eq' q, ← hzc, QuotientGroup.eq]
  have hzc' : z * c = c * z := (Subgroup.mem_center_iff.1 hz c).symm
  rw [hzc', ← mul_assoc, inv_mul_cancel, one_mul]
  exact hZH hz

end Sums

section CompactModCenter

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}


theorem IsCompactModCenter.comp_inv {φ : GL (Fin n) F → ℂ} (hφ : IsCompactModCenter φ) :
    IsCompactModCenter fun g => φ g⁻¹ := by
  obtain ⟨C, hC, hsupp⟩ := hφ
  refine ⟨C⁻¹, hC.inv, fun g hg => ?_⟩
  obtain ⟨z, hz, c, hc, hzc⟩ := hsupp (show g⁻¹ ∈ support φ from hg)
  replace hzc : z * c = g⁻¹ := hzc
  refine ⟨z⁻¹, inv_mem hz, c⁻¹, by simpa using hc, ?_⟩
  have hzc' : z * c = c * z := (Subgroup.mem_center_iff.1 hz c).symm
  show z⁻¹ * c⁻¹ = g
  rw [← mul_inv_rev, ← hzc', hzc, inv_inv]

end CompactModCenter

end Parabolic

end GroundTheory.Automorphic
end
end

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

namespace Parabolic

open Function
open scoped Pointwise

theorem linearMap_finsum {ι M N : Type*} [AddCommMonoid M] [AddCommMonoid N] [Module ℂ M]
    [Module ℂ N] (L : M →ₗ[ℂ] N) {φ : ι → M} (h : HasFiniteSupport φ) :
    L (∑ᶠ i, φ i) = ∑ᶠ i, L (φ i) :=
  map_finsum L h

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

section CentralChar

variable {U : Type*} [AddCommGroup U] [Module ℂ U]

def HasCentralChar (ρ : Representation ℂ (GL (Fin n) F) U) (ω : GL (Fin n) F → ℂ) : Prop :=
  ∀ z ∈ Subgroup.center (GL (Fin n) F), ∀ u, ρ z u = ω z • u

variable {ρ : Representation ℂ (GL (Fin n) F) U} {ω : GL (Fin n) F → ℂ}


omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem HasCentralChar.mul (h : HasCentralChar ρ ω) {u : U} (hu : u ≠ 0)
    {z z' : GL (Fin n) F} (hz : z ∈ Subgroup.center (GL (Fin n) F))
    (hz' : z' ∈ Subgroup.center (GL (Fin n) F)) : ω (z * z') = ω z * ω z' := by
  have h1 := h _ (mul_mem hz hz') u
  rw [map_mul, Module.End.mul_apply, h z' hz', map_smul, h z hz, smul_smul] at h1
  exact (smul_left_injective ℂ hu h1).symm.trans (mul_comm _ _)


omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem HasCentralChar.one (h : HasCentralChar ρ ω) {u : U} (hu : u ≠ 0) : ω 1 = 1 := by
  have h1 : ω 1 • u = (1 : ℂ) • u := by
    rw [one_smul, ← h 1 (Subgroup.one_mem _) u, map_one, Module.End.one_apply]
  exact smul_left_injective ℂ hu h1


omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem HasCentralChar.inv_mul (h : HasCentralChar ρ ω) {u : U} (hu : u ≠ 0)
    {z : GL (Fin n) F} (hz : z ∈ Subgroup.center (GL (Fin n) F)) : ω z⁻¹ * ω z = 1 := by
  rw [← h.mul hu (inv_mem hz) hz, inv_mul_cancel, h.one hu]

end CentralChar

section CenterSup

abbrev centerSup (K : Subgroup (GL (Fin n) F)) : Subgroup (GL (Fin n) F) :=
  Subgroup.center (GL (Fin n) F) ⊔ K

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem mem_centerSup {K : Subgroup (GL (Fin n) F)} {x : GL (Fin n) F} :
    x ∈ centerSup K ↔ ∃ z ∈ Subgroup.center (GL (Fin n) F), ∃ k ∈ K, z * k = x :=
  Subgroup.mem_sup_of_normal_left


omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem rightInv_centerSup {X : Type*} {K : Subgroup (GL (Fin n) F)} {Φ : GL (Fin n) F → X}
    (hZ : ∀ g, ∀ z ∈ Subgroup.center (GL (Fin n) F), Φ (g * z) = Φ g)
    (hK : ∀ g, ∀ k ∈ K, Φ (g * k) = Φ g) : ∀ g, ∀ h ∈ centerSup K, Φ (g * h) = Φ g := by
  intro g h hh
  obtain ⟨z, hz, k, hk, rfl⟩ := mem_centerSup.1 hh
  rw [← mul_assoc, hK _ k hk, hZ g z hz]

theorem isOpen_centerSup {K : Subgroup (GL (Fin n) F)} (hKo : IsOpen (K : Set (GL (Fin n) F))) :
    IsOpen (centerSup K : Set (GL (Fin n) F)) :=
  Subgroup.isOpen_mono le_sup_right hKo

theorem finite_support_centerSup {M : Type*} [AddCommMonoid M] {K : Subgroup (GL (Fin n) F)}
    (hKo : IsOpen (K : Set (GL (Fin n) F))) {Φ : GL (Fin n) F → M} {φ : GL (Fin n) F → ℂ}
    (hφ : IsCompactModCenter φ) (h : ∀ g, φ g = 0 → Φ g = 0) :
    HasFiniteSupport fun q : GL (Fin n) F ⧸ centerSup K => Φ q.out := by
  obtain ⟨C, hC, hsupp⟩ := hφ
  exact finite_support_quotSum (isOpen_centerSup hKo) le_sup_left hC
    (fun g hg => hsupp (mt (h g) hg))

end CenterSup

section CoeffSum

variable {V U W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
  [AddCommGroup W] [Module ℂ W]
  (π : Representation ℂ (GL (Fin n) F) V) (ρ : Representation ℂ (GL (Fin n) F) U)

def coeffSum (K : Subgroup (GL (Fin n) F)) (f : Module.Dual ℂ V) (u : U) (w : V) : U :=
  quotSum (centerSup K) fun g => f (π g⁻¹ w) • ρ g u

variable {π ρ} {K : Subgroup (GL (Fin n) F)} {f : Module.Dual ℂ V} {u : U}
  {ω : GL (Fin n) F → ℂ}


omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem coeffSum_summand_rightInv (hωπ : HasCentralChar π ω) (hωρ : HasCentralChar ρ ω)
    (hω : ∀ z ∈ Subgroup.center (GL (Fin n) F), ω z⁻¹ * ω z = 1)
    (hf : ∀ k ∈ K, ∀ x, f (π k x) = f x) (hu : u ∈ fixedVectors ρ K) (w : V) :
    ∀ g, ∀ h ∈ centerSup K, f (π (g * h)⁻¹ w) • ρ (g * h) u = f (π g⁻¹ w) • ρ g u := by
  refine rightInv_centerSup (Φ := fun g => f (π g⁻¹ w) • ρ g u) (fun g z hz => ?_)
    (fun g k hk => ?_)
  · have e1 : π (g * z)⁻¹ w = ω z⁻¹ • π g⁻¹ w := by
      rw [mul_inv_rev, map_mul, Module.End.mul_apply, hωπ _ (inv_mem hz)]
    have e2 : ρ (g * z) u = ω z • ρ g u := by
      rw [map_mul, Module.End.mul_apply, hωρ z hz, map_smul]
    rw [e1, e2, map_smul, smul_eq_mul, smul_smul]
    congr 1
    linear_combination f (π g⁻¹ w) * hω z hz
  · have e1 : π (g * k)⁻¹ w = π k⁻¹ (π g⁻¹ w) := by
      rw [mul_inv_rev, map_mul, Module.End.mul_apply]
    rw [e1, hf _ (inv_mem hk), map_mul, Module.End.mul_apply, hu k hk]

theorem mem_smoothVectors_dual_of_inv (hKo : IsOpen (K : Set (GL (Fin n) F)))
    (hf : ∀ k ∈ K, ∀ x, f (π k x) = f x) : f ∈ smoothVectors (Representation.dual π) :=
  mem_smoothVectors_of_mem_fixedVectors hKo (mem_fixedVectors_dual.2 hf)

theorem finite_support_coeffSum (hπ : IsSmooth π) (hsc : IsSupercuspidal π)
    (hKo : IsOpen (K : Set (GL (Fin n) F))) (hf : ∀ k ∈ K, ∀ x, f (π k x) = f x) (w : V) :
    HasFiniteSupport fun q : GL (Fin n) F ⧸ centerSup K => f (π q.out⁻¹ w) • ρ q.out u :=
  finite_support_centerSup (Φ := fun g => f (π g⁻¹ w) • ρ g u) hKo
    (isCompactModCenter_matrixCoeff hπ hsc w (mem_smoothVectors_dual_of_inv hKo hf)).comp_inv
    fun g h0 => by
      change f (π g⁻¹ w) = 0 at h0
      simp only [h0, zero_smul]

variable (hπ : IsSmooth π) (hsc : IsSupercuspidal π) (hKo : IsOpen (K : Set (GL (Fin n) F)))
  (hωπ : HasCentralChar π ω) (hωρ : HasCentralChar ρ ω)
  (hω : ∀ z ∈ Subgroup.center (GL (Fin n) F), ω z⁻¹ * ω z = 1)
  (hf : ∀ k ∈ K, ∀ x, f (π k x) = f x) (hu : u ∈ fixedVectors ρ K)

include hπ hsc hKo hf in
theorem coeffSum_add (w₁ w₂ : V) :
    coeffSum π ρ K f u (w₁ + w₂) = coeffSum π ρ K f u w₁ + coeffSum π ρ K f u w₂ := by
  unfold coeffSum quotSum
  rw [← finsum_add_distrib (finite_support_coeffSum hπ hsc hKo hf w₁)
    (finite_support_coeffSum hπ hsc hKo hf w₂)]
  refine finsum_congr fun q => ?_
  dsimp only
  rw [map_add (f := _), map_add (f := _), add_smul]

include hπ hsc hKo hf in
theorem coeffSum_smul (c : ℂ) (w : V) :
    coeffSum π ρ K f u (c • w) = c • coeffSum π ρ K f u w := by
  unfold coeffSum quotSum
  rw [smul_finsum' c (finite_support_coeffSum hπ hsc hKo hf w)]
  refine finsum_congr fun q => ?_
  dsimp only
  rw [map_smul, map_smul, smul_eq_mul, mul_smul]


include hπ hsc hKo hωπ hωρ hω hf hu in
theorem coeffSum_act (x : GL (Fin n) F) (w : V) :
    coeffSum π ρ K f u (π x w) = ρ x (coeffSum π ρ K f u w) := by
  have hΨ := coeffSum_summand_rightInv hωπ hωρ hω hf hu w
  have hΨ' : ∀ g, ∀ h ∈ centerSup K, ρ x (f (π (g * h)⁻¹ w) • ρ (g * h) u) =
      ρ x (f (π g⁻¹ w) • ρ g u) := fun g h hh => by rw [hΨ g h hh]
  calc coeffSum π ρ K f u (π x w)
      = quotSum (centerSup K) fun g => ρ x (f (π (x⁻¹ * g)⁻¹ w) • ρ (x⁻¹ * g) u) := by
        refine quotSum_congr fun g => ?_
        have h1 : (x⁻¹ * g)⁻¹ = g⁻¹ * x := by group
        rw [map_smul, h1, map_mul π g⁻¹ x, Module.End.mul_apply, ← Module.End.mul_apply (ρ x),
          ← map_mul ρ, mul_inv_cancel_left]
    _ = quotSum (centerSup K) fun g => ρ x (f (π g⁻¹ w) • ρ g u) :=
        quotSum_mul_left (Φ := fun g => ρ x (f (π g⁻¹ w) • ρ g u)) hΨ' x⁻¹
    _ = ρ x (coeffSum π ρ K f u w) :=
        (linearMap_finsum (ρ x) (finite_support_coeffSum hπ hsc hKo hf w)).symm

def coeffMap : Representation.IntertwiningMap π ρ where
  toFun := coeffSum π ρ K f u
  map_add' := coeffSum_add hπ hsc hKo hf
  map_smul' := coeffSum_smul hπ hsc hKo hf
  isIntertwining' x := LinearMap.ext fun w => coeffSum_act hπ hsc hKo hωπ hωρ hω hf hu x w

theorem coeffMap_apply (w : V) :
    coeffMap hπ hsc hKo hωπ hωρ hω hf hu w = coeffSum π ρ K f u w := rfl


omit hωπ hωρ hω hu in
include hπ hsc hKo hf in
theorem map_coeffSum {σ : Representation ℂ (GL (Fin n) F) W}
    (p : Representation.IntertwiningMap ρ σ) (w : V) :
    p (coeffSum π ρ K f u w) = coeffSum π σ K f (p u) w := by
  unfold coeffSum quotSum
  rw [← Representation.IntertwiningMap.toLinearMap_apply,
    linearMap_finsum _ (finite_support_coeffSum hπ hsc hKo hf w)]
  refine finsum_congr fun q => ?_
  rw [Representation.IntertwiningMap.toLinearMap_apply, map_smul,
    Representation.IntertwiningMap.isIntertwining]

end CoeffSum

section Scalar

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) F) V}
  {K : Subgroup (GL (Fin n) F)} {f : Module.Dual ℂ V} {v : V} {ω : GL (Fin n) F → ℂ}

theorem exists_coeffSum_eq_smul [π.IsIrreducible] (hπ : IsSmooth π) (hsc : IsSupercuspidal π)
    (hKo : IsOpen (K : Set (GL (Fin n) F))) (hωπ : HasCentralChar π ω)
    (hf : ∀ k ∈ K, ∀ x, f (π k x) = f x) (hv : v ∈ fixedVectors π K) :
    ∃ c : ℂ, ∀ w, coeffSum π π K f v w = c • w := by
  obtain ⟨u₀, hu₀⟩ := exists_ne_zero_of_isIrreducible (ρ := π)
  obtain ⟨c, hc⟩ := (algebraMap_intertwiningMap_bijective_of_isSmooth hπ).2
    (coeffMap hπ hsc hKo hωπ hωπ (fun z hz => hωπ.inv_mul hu₀ hz) hf hv)
  refine ⟨c, fun w => ?_⟩
  have := congrArg (fun φ : Representation.IntertwiningMap π π => φ w) hc
  simpa [coeffMap_apply] using this.symm

end Scalar

end Parabolic

end GroundTheory.Automorphic
end
end

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

namespace Parabolic

open Function Topology ComplexConjugate
open scoped Pointwise

theorem quotSum_eq_zero_of_nonneg {G : Type*} [Group G] {H : Subgroup G} {Φ : G → ℝ}
    (hΦ : ∀ g, 0 ≤ Φ g) (hfin : HasFiniteSupport fun q : G ⧸ H => Φ q.out)
    (h0 : quotSum H Φ = 0) (q : G ⧸ H) : Φ q.out = 0 := by
  classical
  have hfin' : (support fun q : G ⧸ H => Φ q.out).Finite := hfin
  rw [quotSum_def, finsum_eq_sum_of_support_subset _ hfin'.coe_toFinset.symm.subset] at h0
  by_cases hq : q ∈ hfin'.toFinset
  · exact (Finset.sum_eq_zero_iff_of_nonneg fun q _ => hΦ q.out).1 h0 q hq
  · simpa using hq

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

section ScalarDet

def scalarDet : GL (Fin n) F →* GL (Fin n) F :=
  (Matrix.GeneralLinearGroup.scalar (Fin n)).comp Matrix.GeneralLinearGroup.det

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem coe_scalarDet (g : GL (Fin n) F) :
    ((scalarDet g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      Matrix.scalar (Fin n) (g : Matrix (Fin n) (Fin n) F).det := rfl

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem scalarDet_mem_center (g : GL (Fin n) F) :
    scalarDet g ∈ Subgroup.center (GL (Fin n) F) :=
  Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.2 ⟨_, (coe_scalarDet g).symm⟩


omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem scalarDet_of_mem_center {z : GL (Fin n) F} (hz : z ∈ Subgroup.center (GL (Fin n) F)) :
    scalarDet z = z ^ n := by
  obtain ⟨a, ha⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.1 hz
  have hdet : (z : Matrix (Fin n) (Fin n) F).det = a ^ n := by
    rw [← ha, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  ext1
  rw [coe_scalarDet, Units.val_pow_eq_pow_val, hdet, ← ha, map_pow]

theorem continuous_scalarDet : Continuous (scalarDet : GL (Fin n) F → GL (Fin n) F) := by
  have hval : Continuous fun g : GL (Fin n) F =>
      ((scalarDet g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
    simp only [coe_scalarDet, Matrix.scalar_apply]
    exact Continuous.matrix_diagonal (continuous_pi fun _ => Units.continuous_val.matrix_det)
  refine Units.continuous_iff.2 ⟨hval, ?_⟩
  exact (hval.comp continuous_inv).congr fun g => by simp only [Function.comp_apply, map_inv]

end ScalarDet

section NormChar

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) F) V}
  {ω : GL (Fin n) F → ℂ}

def normChar (ω : GL (Fin n) F → ℂ) (g : GL (Fin n) F) : ℝ :=
  ‖ω (scalarDet g)‖ ^ ((n : ℝ)⁻¹)

variable (hωπ : HasCentralChar π ω) {v : V} (hv : v ≠ 0)
include hωπ hv

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem HasCentralChar.ne_zero {z : GL (Fin n) F} (hz : z ∈ Subgroup.center (GL (Fin n) F)) :
    ω z ≠ 0 := fun h0 => by
  have := hωπ.inv_mul hv hz
  rw [h0, mul_zero] at this
  exact zero_ne_one this

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem normChar_pos (g : GL (Fin n) F) : 0 < normChar ω g :=
  Real.rpow_pos_of_pos (norm_pos_iff.2 (hωπ.ne_zero hv (scalarDet_mem_center g))) _

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem normChar_mul (x y : GL (Fin n) F) :
    normChar ω (x * y) = normChar ω x * normChar ω y := by
  unfold normChar
  rw [map_mul, hωπ.mul hv (scalarDet_mem_center x) (scalarDet_mem_center y), norm_mul,
    Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem normChar_one : normChar ω (1 : GL (Fin n) F) = 1 := by
  unfold normChar
  rw [map_one, hωπ.one hv, norm_one, Real.one_rpow]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem normChar_inv_mul (g : GL (Fin n) F) : normChar ω g⁻¹ * normChar ω g = 1 := by
  rw [← normChar_mul hωπ hv, inv_mul_cancel, normChar_one hωπ hv]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem map_pow_of_mem_center {z : GL (Fin n) F} (hz : z ∈ Subgroup.center (GL (Fin n) F))
    (m : ℕ) : ω (z ^ m) = ω z ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, hωπ.one hv]
  | succ m ih => rw [pow_succ, hωπ.mul hv (pow_mem hz m) hz, ih, pow_succ]


omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem normChar_of_mem_center {z : GL (Fin n) F} (hz : z ∈ Subgroup.center (GL (Fin n) F)) :
    normChar ω z = ‖ω z‖ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h1 : z = 1 := Units.ext (Subsingleton.elim _ _)
    rw [h1, normChar_one hωπ hv, hωπ.one hv, norm_one]
  · unfold normChar
    rw [scalarDet_of_mem_center hz, map_pow_of_mem_center hωπ hv hz, norm_pow,
      Real.pow_rpow_inv_natCast (norm_nonneg _) hn.ne']


omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem normChar_eq_one {k : GL (Fin n) F} (hk : π (scalarDet k) v = v) : normChar ω k = 1 := by
  have h1 : ω (scalarDet k) • v = (1 : ℂ) • v := by
    rw [one_smul, ← hωπ _ (scalarDet_mem_center k), hk]
  unfold normChar
  rw [smul_left_injective ℂ hv h1, norm_one, Real.one_rpow]

end NormChar

section Twisted

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) F) V}
  {ω : GL (Fin n) F → ℂ} {K : Subgroup (GL (Fin n) F)} {f : Module.Dual ℂ V}


variable (π ω) in
def twVec (x : V) (g : GL (Fin n) F) : V :=
  ((normChar ω g : ℂ)⁻¹) • π g x

variable (hωπ : HasCentralChar π ω) {v : V} (hv : v ≠ 0)
include hωπ hv

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem twVec_mul_center (x : V) (g : GL (Fin n) F) {z : GL (Fin n) F}
    (hz : z ∈ Subgroup.center (GL (Fin n) F)) :
    twVec π ω x (g * z) = (ω z / (‖ω z‖ : ℂ)) • twVec π ω x g := by
  unfold twVec
  have hnz : (‖ω z‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_pos_iff.2 (hωπ.ne_zero hv hz)).ne'
  have hθ : (normChar ω g : ℂ) ≠ 0 := by exact_mod_cast (normChar_pos hωπ hv g).ne'
  rw [map_mul, Module.End.mul_apply, hωπ z hz, map_smul, smul_smul, smul_smul,
    normChar_mul hωπ hv, normChar_of_mem_center hωπ hv hz]
  congr 1
  push_cast
  field_simp

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem twVec_mul_of_mem {x : V} (hx : x ∈ fixedVectors π K)
    (hK : ∀ k ∈ K, normChar ω k = 1) (g : GL (Fin n) F) {k : GL (Fin n) F} (hk : k ∈ K) :
    twVec π ω x (g * k) = twVec π ω x g := by
  unfold twVec
  rw [map_mul, Module.End.mul_apply, hx k hk, normChar_mul hωπ hv, hK k hk, mul_one]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem twVec_mul (x : V) (a g : GL (Fin n) F) :
    twVec π ω x (a * g) = ((normChar ω a : ℂ)⁻¹) • π a (twVec π ω x g) := by
  unfold twVec
  rw [map_smul, smul_smul, map_mul, Module.End.mul_apply, normChar_mul hωπ hv]
  push_cast
  rw [mul_inv, mul_comm]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem twVec_one (x : V) : twVec π ω x 1 = x := by
  unfold twVec
  rw [normChar_one hωπ hv, map_one, Module.End.one_apply]
  simp

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem conj_mul_self_unit {z : GL (Fin n) F} (hz : z ∈ Subgroup.center (GL (Fin n) F)) :
    conj (ω z / (‖ω z‖ : ℂ)) * (ω z / (‖ω z‖ : ℂ)) = 1 := by
  have h1 : ‖ω z / (‖ω z‖ : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, norm_norm,
      div_self (norm_ne_zero_iff.2 (hωπ.ne_zero hv hz))]
  rw [Complex.conj_mul', h1]
  norm_num

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem norm_twVec_unit {z : GL (Fin n) F} (hz : z ∈ Subgroup.center (GL (Fin n) F)) :
    ‖ω z / (‖ω z‖ : ℂ)‖ = 1 := by
  rw [norm_div, Complex.norm_real, norm_norm,
    div_self (norm_ne_zero_iff.2 (hωπ.ne_zero hv hz))]


omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem normSq_twVec_rightInv {x : V} (hx : x ∈ fixedVectors π K)
    (hK : ∀ k ∈ K, normChar ω k = 1) :
    ∀ g, ∀ h ∈ centerSup K, ‖f (twVec π ω x (g * h))‖ ^ 2 = ‖f (twVec π ω x g)‖ ^ 2 := by
  refine rightInv_centerSup (Φ := fun g => ‖f (twVec π ω x g)‖ ^ 2) (fun g z hz => ?_)
    (fun g k hk => ?_)
  ·     rw [twVec_mul_center hωπ hv x g hz, map_smul, smul_eq_mul, norm_mul,
      norm_twVec_unit hωπ hv hz, one_mul]
  ·     rw [twVec_mul_of_mem hωπ hv hx hK g hk]

end Twisted

section Nonvanishing

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) F) V}
  {ω : GL (Fin n) F → ℂ}

theorem quotSum_ofReal {G : Type*} [Group G] {H : Subgroup G} {Φ : G → ℝ}
    (hfin : HasFiniteSupport fun q : G ⧸ H => Φ q.out) :
    quotSum H (fun g => (Φ g : ℂ)) = ((quotSum H Φ : ℝ) : ℂ) := by
  rw [quotSum_def, quotSum_def]
  exact (map_finsum Complex.ofRealHom hfin).symm

variable (hπ : IsSmooth π) (hsc : IsSupercuspidal π) (hωπ : HasCentralChar π ω) {v : V}
  (hv : v ≠ 0) {K : Subgroup (GL (Fin n) F)} (hKo : IsOpen (K : Set (GL (Fin n) F)))
  {f : Module.Dual ℂ V} (hf : ∀ k ∈ K, ∀ x, f (π k x) = f x)

include hπ hsc hωπ hv hKo hf

omit hωπ hv in
theorem finite_support_normSq_twVec (x : V) :
    HasFiniteSupport fun q : GL (Fin n) F ⧸ centerSup K => ‖f (twVec π ω x q.out)‖ ^ 2 :=
  finite_support_centerSup (Φ := fun g => ‖f (twVec π ω x g)‖ ^ 2) hKo
    (isCompactModCenter_matrixCoeff hπ hsc x (mem_smoothVectors_dual_of_inv hKo hf))
    fun g h0 => by
      change f (π g x) = 0 at h0
      simp [twVec, h0]

theorem apply_eq_zero_of_quotSum_normSq {x : V} (hx : x ∈ fixedVectors π K)
    (hK : ∀ k ∈ K, normChar ω k = 1)
    (h0 : quotSum (centerSup K) (fun g => ‖f (twVec π ω x g)‖ ^ 2) = 0) : f x = 0 := by
  have h1 := quotSum_eq_zero_of_nonneg (fun g => by positivity)
    (finite_support_normSq_twVec hπ hsc hKo hf x) h0 (QuotientGroup.mk 1)
  rw [apply_out_mk (Φ := fun g => ‖f (twVec π ω x g)‖ ^ 2)
    (normSq_twVec_rightInv hωπ hv hx hK), twVec_one hωπ hv] at h1
  simpa using h1

end Nonvanishing

theorem exists_coeffSum_ne_zero {V : Type*} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin n) F) V} {ω : GL (Fin n) F → ℂ} [π.IsIrreducible]
    (hπ : IsSmooth π) (hsc : IsSupercuspidal π) (hωπ : HasCentralChar π ω) :
    ∃ K : Subgroup (GL (Fin n) F), IsCompact (K : Set (GL (Fin n) F)) ∧
      IsOpen (K : Set (GL (Fin n) F)) ∧ ∃ f : Module.Dual ℂ V, (∀ k ∈ K, ∀ x, f (π k x) = f x) ∧
        ∃ v ∈ fixedVectors π K, ∃ w, coeffSum π π K f v w ≠ 0 := by
  classical
  obtain ⟨v, hv0⟩ := exists_ne_zero_of_isIrreducible (ρ := π)
  have h1 : (stabilizerOf π v : Set (GL (Fin n) F)) ∈ 𝓝 (1 : GL (Fin n) F) :=
    (hπ v).mem_nhds (one_mem _)
  have hU : (stabilizerOf π v : Set (GL (Fin n) F)) ∩
      scalarDet ⁻¹' (stabilizerOf π v : Set (GL (Fin n) F)) ∈ 𝓝 (1 : GL (Fin n) F) :=
    Filter.inter_mem h1 (continuous_scalarDet.continuousAt.preimage_mem_nhds (by rwa [map_one]))
  obtain ⟨K', hKc, hKU⟩ := exists_openSubgroup_isCompact_subset hU
  let K : Subgroup (GL (Fin n) F) := K'
  have hKo : IsOpen (K : Set (GL (Fin n) F)) := K'.isOpen
  have hKc' : IsCompact (K : Set (GL (Fin n) F)) := hKc
  have hvK : v ∈ fixedVectors π K := fun k hk => (hKU hk).1
  have hθK : ∀ k ∈ K, normChar ω k = 1 := fun k hk => normChar_eq_one hωπ hv0 (hKU hk).2
  obtain ⟨f₀, hf₀⟩ : ∃ f₀ : Module.Dual ℂ V, f₀ v ≠ 0 := by
    by_contra h
    push Not at h
    exact hv0 ((Module.forall_dual_apply_eq_zero_iff ℂ v).1 h)
  let f : Module.Dual ℂ V := f₀ ∘ₗ (fixedVectors π K).subtype ∘ₗ fixedProj π hπ hKc' hKo
  have hf : ∀ k ∈ K, ∀ x, f (π k x) = f x := fun k hk x => by
    simp only [f, LinearMap.comp_apply, fixedProj_apply_act hπ hKc' hKo hk]
  have hfv : f v = f₀ v := by
    simp only [f, LinearMap.comp_apply, fixedProj_apply_of_mem hπ hKc' hKo hvK,
      Submodule.subtype_apply]
  have hfs := mem_smoothVectors_dual_of_inv hKo hf

  let P : GL (Fin n) F → V := twVec π ω v
  let S : GL (Fin n) F → V := fun g => conj (f (P g)) • P g
  have hSfin : HasFiniteSupport fun q : GL (Fin n) F ⧸ centerSup K => S q.out :=
    finite_support_centerSup (Φ := S) hKo (isCompactModCenter_matrixCoeff hπ hsc v hfs)
      fun g h0 => by
        change f (π g v) = 0 at h0
        simp [S, P, twVec, h0]
  have hSinv : ∀ g, ∀ h ∈ centerSup K, S (g * h) = S g := by
    refine rightInv_centerSup (Φ := S) (fun g z hz => ?_) (fun g k hk => ?_)
    · simp only [S, P]
      rw [twVec_mul_center hωπ hv0 v g hz, map_smul, smul_eq_mul, map_mul, smul_smul]
      congr 1
      linear_combination conj (f (twVec π ω v g)) * conj_mul_self_unit hωπ hv0 hz
    · simp only [S, P]
      rw [twVec_mul_of_mem hωπ hv0 hvK hθK g hk]
  have hPk : ∀ k ∈ K, ∀ g, P (k * g) = π k (P g) := fun k hk g => by
    simp only [P]
    rw [twVec_mul hωπ hv0 v k g, hθK k hk, Complex.ofReal_one, inv_one, one_smul]
  let v' : V := quotSum (centerSup K) S
  have hv'K : v' ∈ fixedVectors π K := by
    intro k hk
    have hSk : ∀ g, π k (S g) = S (k * g) := fun g => by
      simp only [S]
      rw [hPk k hk, hf k hk, map_smul]
    calc π k v' = quotSum (centerSup K) fun g => π k (S g) :=
          linearMap_finsum (π k) hSfin
      _ = quotSum (centerSup K) fun g => S (k * g) := quotSum_congr hSk
      _ = v' := quotSum_mul_left hSinv k

  have hΨinv : ∀ a, ∀ g, ∀ h ∈ centerSup K,
      conj (f (P (g * h))) * f (P (a * (g * h))) = conj (f (P g)) * f (P (a * g)) := by
    intro a
    refine rightInv_centerSup (Φ := fun g => conj (f (P g)) * f (P (a * g)))
      (fun g z hz => ?_) (fun g k hk => ?_)
    · simp only [P]
      rw [← mul_assoc, twVec_mul_center hωπ hv0 v g hz, twVec_mul_center hωπ hv0 v (a * g) hz,
        f.map_smul, f.map_smul, smul_eq_mul, smul_eq_mul, map_mul]
      linear_combination conj (f (twVec π ω v g)) * f (twVec π ω v (a * g)) *
        conj_mul_self_unit hωπ hv0 hz
    · simp only [P]
      rw [← mul_assoc, twVec_mul_of_mem hωπ hv0 hvK hθK g hk,
        twVec_mul_of_mem hωπ hv0 hvK hθK (a * g) hk]
  have hΨfin : ∀ a, HasFiniteSupport fun q : GL (Fin n) F ⧸ centerSup K =>
      conj (f (P q.out)) * f (P (a * q.out)) := fun a =>
    finite_support_centerSup (Φ := fun g => conj (f (P g)) * f (P (a * g))) hKo
      (isCompactModCenter_matrixCoeff hπ hsc v hfs) fun g h0 => by
        change f (π g v) = 0 at h0
        simp [P, twVec, h0]

  let k' : GL (Fin n) F → ℂ := fun x => f (twVec π ω v' x)
  have hk'eq : ∀ x, k' x = quotSum (centerSup K) fun g => conj (f (P g)) * f (P (x * g)) := by
    intro x
    let L : V →ₗ[ℂ] ℂ := ((normChar ω x : ℂ)⁻¹) • (f ∘ₗ π x)
    have hL : ∀ y, L y = f (((normChar ω x : ℂ)⁻¹) • π x y) := fun y => by
      simp [L]
    calc k' x = L v' := (hL v').symm
      _ = quotSum (centerSup K) fun g => L (S g) := linearMap_finsum L hSfin
      _ = _ := quotSum_congr fun g => by
          simp only [hL, S, P]
          rw [twVec_mul hωπ hv0 v x g]
          simp only [map_smul, smul_eq_mul]
          ring
  have hk'conj : ∀ x, conj (k' x⁻¹) = k' x := by
    intro x
    rw [hk'eq, hk'eq, ← quotSum_mul_left (Φ := fun g => conj (f (P g)) * f (P (x * g)))
      (hΨinv x) x⁻¹, quotSum_def, quotSum_def,
      map_finsum (starRingEnd ℂ) (hΨfin x⁻¹)]
    refine finsum_congr fun q => ?_
    simp only [map_mul, Complex.conj_conj, mul_inv_cancel_left]
    ring
  have hfk : ∀ g, f (π g v') = (normChar ω g : ℂ) * k' g := fun g => by
    have hθ : (normChar ω g : ℂ) ≠ 0 := by exact_mod_cast (normChar_pos hωπ hv0 g).ne'
    simp only [k', twVec, map_smul, smul_eq_mul]
    field_simp
  refine ⟨K, hKc', hKo, f, hf, v', hv'K, v', fun hzero => hf₀ ?_⟩

  have hsum : quotSum (centerSup K) (fun g => f (π g⁻¹ v') * f (π g v')) = 0 := by
    have h2 := congrArg f hzero
    rw [map_zero] at h2
    unfold coeffSum at h2
    rw [quotSum_def, linearMap_finsum f (finite_support_coeffSum hπ hsc hKo hf v')] at h2
    rw [quotSum_def]
    simpa only [map_smul, smul_eq_mul] using h2
  have hterm : ∀ g, f (π g⁻¹ v') * f (π g v') = ((‖k' g‖ ^ 2 : ℝ) : ℂ) := fun g => by
    rw [hfk, hfk, ← hk'conj g⁻¹, inv_inv]
    have h2 : (normChar ω g⁻¹ : ℂ) * (normChar ω g : ℂ) = 1 := by
      exact_mod_cast normChar_inv_mul hωπ hv0 g
    rw [Complex.ofReal_pow, ← Complex.conj_mul']
    linear_combination (conj (k' g) * k' g) * h2
  have hk'0 : f v' = 0 := by
    refine apply_eq_zero_of_quotSum_normSq hπ hsc hωπ hv0 hKo hf hv'K hθK ?_
    rw [quotSum_congr hterm, quotSum_ofReal (finite_support_normSq_twVec (ω := ω) hπ hsc hKo hf v')]
      at hsum
    exact_mod_cast hsum

  have hk'1 : f v' = ((quotSum (centerSup K) fun g => ‖f (twVec π ω v g)‖ ^ 2 : ℝ) : ℂ) := by
    have h2 := hk'eq 1
    simp only [k', twVec_one hωπ hv0, one_mul] at h2
    rw [h2, ← quotSum_ofReal (finite_support_normSq_twVec (ω := ω) hπ hsc hKo hf v)]
    refine quotSum_congr fun g => ?_
    rw [Complex.ofReal_pow, ← Complex.conj_mul']
  rw [← hfv]
  refine apply_eq_zero_of_quotSum_normSq hπ hsc hωπ hv0 hKo hf hvK hθK ?_
  rw [hk'1] at hk'0
  exact_mod_cast hk'0

end Parabolic

end GroundTheory.Automorphic
