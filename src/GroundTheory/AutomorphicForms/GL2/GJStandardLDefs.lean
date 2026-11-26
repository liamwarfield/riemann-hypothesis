module

public import GroundTheory.AutomorphicForms.GL2.GJGlobal
public import GroundTheory.AutomorphicForms.GL2.GJStandardLUnramified
public import GroundTheory.AutomorphicForms.GL2.GJLocalFEGamma
public import GroundTheory.AutomorphicForms.GL2.GJFEInducedLevi
public import GroundTheory.AutomorphicForms.GL2.GJFELeviMulti
public import GroundTheory.AutomorphicForms.RestrictedHaarProduct

@[expose] public section

section -- merged from GroundTheory.AutomorphicForms.GL2.GJFELevi
noncomputable section

namespace GroundTheory.Automorphic

namespace GodementJacquet

open Matrix GLnLocal MeasureTheory Measure Parabolic
open scoped NNReal ENNReal

set_option linter.unusedSectionVars false

section Twist

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] {W : Type*} [AddCommGroup W] [Module ℂ W]

def nnrealCharC (χ : G →* ℝ≥0) : G →* ℂ :=
  (Complex.ofRealHom.comp NNReal.toRealHom).toMonoidHom.comp χ

@[simp]
theorem nnrealCharC_apply (χ : G →* ℝ≥0) (g : G) : nnrealCharC χ g = ((χ g : ℝ) : ℂ) := rfl

theorem nnrealCharC_ne_zero (χ : G →* ℝ≥0) (g : G) : nnrealCharC χ g ≠ 0 := by
  rw [nnrealCharC_apply]
  have h := map_mul_eq_one χ (mul_inv_cancel g)
  exact_mod_cast (left_ne_zero_of_mul_eq_one h)

theorem exists_compact_open_char_eq_one (χ : G →* ℝ≥0) (hχ : Continuous χ) {U : Set G}
    (hU : U ∈ nhds (1 : G)) : ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ U ∧
      ∀ k ∈ (K : Set G), χ k = 1 := by
  obtain ⟨K, hKc, hKU⟩ := exists_openSubgroup_isCompact_subset hU
  exact ⟨K, hKc, hKU, fun k hk => eq_one_of_mem_compact χ hχ hKc hk⟩

variable (χ : G →* ℝ≥0) (hχ : Continuous χ) (ρ : Representation ℂ G W)
include hχ

theorem fixedVectors_twist {K : Subgroup G} (hKc : IsCompact (K : Set G)) :
    fixedVectors (twist (nnrealCharC χ) ρ) K = fixedVectors ρ K := by
  ext v
  simp only [mem_fixedVectors, twist_apply, nnrealCharC_apply]
  refine forall₂_congr fun k hk => ?_
  rw [eq_one_of_mem_compact χ hχ hKc hk]
  simp

theorem isSmooth_twist (hρ : IsSmooth ρ) : IsSmooth (twist (nnrealCharC χ) ρ) := by
  intro v
  obtain ⟨K, hKc, hKU, hK1⟩ := exists_compact_open_char_eq_one χ hχ
    ((hρ v).mem_nhds (one_mem (stabilizerOf ρ v)))
  refine Subgroup.isOpen_mono (H₁ := (K : Subgroup G)) (fun k hk => ?_) K.isOpen
  rw [mem_stabilizerOf, twist_apply, nnrealCharC_apply, hK1 k hk, mem_stabilizerOf.1 (hKU hk)]
  simp

theorem isAdmissible_twist (hρ : IsAdmissible ρ) : IsAdmissible (twist (nnrealCharC χ) ρ) :=
  ⟨isSmooth_twist χ hχ ρ hρ.1, fun K hKc hKo => by
    rw [fixedVectors_twist χ hχ ρ hKc]
    exact hρ.2 K hKc hKo⟩


omit hχ in
def subrepresentationTwistOrderIso :
    Subrepresentation (twist (nnrealCharC χ) ρ) ≃o Subrepresentation ρ where
  toFun S := ⟨S.toSubmodule, fun g v hv => by
    have h := S.apply_mem_toSubmodule g hv
    rw [twist_apply] at h
    have := S.toSubmodule.smul_mem (nnrealCharC χ g)⁻¹ h
    rwa [smul_smul, inv_mul_cancel₀ (nnrealCharC_ne_zero χ g), one_smul] at this⟩
  invFun S := ⟨S.toSubmodule, fun g v hv => by
    rw [twist_apply]
    exact S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule g hv)⟩
  left_inv S := rfl
  right_inv S := rfl
  map_rel_iff' := Iff.rfl

omit hχ in
theorem isIrreducible_twist [ρ.IsIrreducible] :
    (twist (nnrealCharC χ) ρ).IsIrreducible :=
  (OrderIso.isSimpleOrder_iff (subrepresentationTwistOrderIso χ ρ)).2 inferInstance

theorem mem_smoothVectors_dual_twist_iff {ℓ : Module.Dual ℂ W} :
    ℓ ∈ smoothVectors (Representation.dual (twist (nnrealCharC χ) ρ)) ↔
      ℓ ∈ smoothVectors (Representation.dual ρ) := by
  have key : ∀ (ρ₁ ρ₂ : Representation ℂ G W), (∀ g, ∀ x, χ g = 1 → ρ₁ g x = ρ₂ g x) →
      ℓ ∈ smoothVectors (Representation.dual ρ₁) → ℓ ∈ smoothVectors (Representation.dual ρ₂) := by
    intro ρ₁ ρ₂ h12 hℓ
    obtain ⟨K, hKc, hKU, hK1⟩ := exists_compact_open_char_eq_one χ hχ
      (hℓ.mem_nhds (one_mem (stabilizerOf (Representation.dual ρ₁) ℓ)))
    refine Subgroup.isOpen_mono (H₁ := (K : Subgroup G)) (fun k hk => ?_) K.isOpen
    have h1 := mem_stabilizerOf.1 (hKU hk)
    rw [mem_stabilizerOf]
    ext x
    have := LinearMap.congr_fun h1 x
    rw [dual_apply_apply] at this ⊢
    rw [← h12 k⁻¹ x (by rw [map_inv, hK1 k hk, inv_one]), this]
  constructor
  · exact key _ _ fun g x hg => by rw [twist_apply, nnrealCharC_apply, hg]; simp
  · exact key _ _ fun g x hg => by rw [twist_apply, nnrealCharC_apply, hg]; simp

end Twist

section PUnitProd

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def prodPUnitEquiv : (G × PUnit) ≃ₜ* G where
  toFun p := p.1
  invFun g := (g, 1)
  left_inv p := by ext1 <;> rfl
  right_inv g := rfl
  map_mul' p q := rfl
  continuous_toFun := continuous_fst
  continuous_invFun := continuous_id.prodMk continuous_const

end PUnitProd

section LeviBlocks

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}

theorem leviEquivPi_symm_apply_entry (x : ∀ a : Set.range β, GL (Fin (blockSize β a)) F)
    (a : Set.range β) (k l : Fin (blockSize β a)) :
    (((leviEquivPi F β).symm x : levi F n β) : GL (Fin n) F) (fiberFin β a k).1
      (fiberFin β a l).1 = ((x a : GL (Fin (blockSize β a)) F) : Matrix _ _ F) k l := by
  rw [← leviEquivPi_apply, ContinuousMulEquiv.apply_symm_apply]

theorem det_leviEquivPi (m : levi F n β) (a : Set.range β) :
    Matrix.det ((leviEquivPi F β m a : GL (Fin (blockSize β a)) F) :
      Matrix (Fin (blockSize β a)) (Fin (blockSize β a)) F) =
      Matrix.det ((leviBlock F m a : GL (Fiber β a) F) : Matrix (Fiber β a) (Fiber β a) F) := by
  show (Matrix.reindex _ _ ((leviBlock F m a : GL (Fiber β a) F) :
    Matrix (Fiber β a) (Fiber β a) F)).det = _
  exact Matrix.det_reindex_self _ _

theorem ordDet_leviEquivPi (m : levi F n β) (a : Set.range β) :
    ordDet (leviEquivPi F β m a) = blockOrd F a m := by
  rw [ordDet, det_leviEquivPi]
  rfl

theorem detPow_leviEquivPi_symm (x : ∀ a : Set.range β, GL (Fin (blockSize β a)) F) (s : ℂ) :
    detPow (((leviEquivPi F β).symm x : levi F n β) : GL (Fin n) F) s =
      ∏ a, detPow (x a) s := by
  rw [detPow_eq_qs_zpow, ordDet_eq_sum_blockOrd]
  have : ∀ a, blockOrd F a ((leviEquivPi F β).symm x) = ordDet (x a) := fun a => by
    rw [← ordDet_leviEquivPi, ContinuousMulEquiv.apply_symm_apply]
  simp_rw [this, detPow_eq_qs_zpow]
  classical
  induction (Finset.univ : Finset (Set.range β)) using Finset.induction_on with
  | empty => simp
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add₀ (qs_ne_zero s), ih]

theorem leviModulus_leviEquivPi_symm (x : ∀ a : Set.range β, GL (Fin (blockSize β a)) F) :
    leviModulus β ((leviEquivPi F β).symm x) = ∏ a, detModulusPow (x a) := by
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [detModulusPow, ← det_leviEquivPi, ContinuousMulEquiv.apply_symm_apply]

theorem leviEquivPi_symm_mulSingle (a : Set.range β) :
    (leviEquivPi F β).symm (Pi.mulSingle a (centralUnif F (blockSize β a))) = blockUnif F a := by
  classical
  apply (leviEquivPi F β).injective
  rw [ContinuousMulEquiv.apply_symm_apply]
  funext b
  ext k l
  rw [leviEquivPi_apply]
  simp only [blockUnif, Cartan.diagPow, Matrix.diagonal_apply]
  have hk : blockOf β (fiberFin β b k).1 = b := (fiberFin β b k).2
  have hkl : (fiberFin β b k).1 = (fiberFin β b l).1 ↔ k = l := by
    rw [← Subtype.ext_iff, (fiberFin β b).injective.eq_iff]
  by_cases hb : b = a
  · subst hb
    rw [Pi.mulSingle_eq_same, coe_centralUnif]
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, blockIndicator, hk, if_true,
      zpow_one, hkl]
    split_ifs <;> simp
  · rw [Pi.mulSingle_eq_of_ne hb]
    simp only [Units.val_one, Matrix.one_apply, blockIndicator, hk, if_neg hb, zpow_zero, hkl]


variable (β) in
def leviIdx (a : Set.range β) (k l : Fin (blockSize β a)) : LeviIndex n β :=
  ⟨((fiberFin β a k).1, (fiberFin β a l).1), by
    have hk := congrArg Subtype.val (fiberFin β a k).2
    have hl := congrArg Subtype.val (fiberFin β a l).2
    exact hk.trans hl.symm⟩

theorem leviIdx_bijective :
    Function.Bijective fun p : (Σ a : Set.range β, Fin (blockSize β a) × Fin (blockSize β a)) =>
      leviIdx β p.1 p.2.1 p.2.2 := by
  constructor
  · rintro ⟨a, k, l⟩ ⟨a', k', l'⟩ h
    have h1 : (fiberFin β a k).1 = (fiberFin β a' k').1 :=
      congrArg (fun ij : LeviIndex n β => ij.1.1) h
    have h2 : (fiberFin β a l).1 = (fiberFin β a' l').1 :=
      congrArg (fun ij : LeviIndex n β => ij.1.2) h
    have ha : a = a' := (fiberFin β a k).2.symm.trans (by rw [h1]; exact (fiberFin β a' k').2)
    subst ha
    have hk : k = k' := (fiberFin β a).injective (Subtype.ext h1)
    have hl : l = l' := (fiberFin β a).injective (Subtype.ext h2)
    subst hk hl
    rfl
  · rintro ⟨⟨i, j⟩, hij⟩
    have hj : blockOf β j = blockOf β i := Subtype.ext hij.symm
    refine ⟨⟨blockOf β i, ((fiberFin β (blockOf β i)).symm ⟨i, rfl⟩,
      (fiberFin β (blockOf β i)).symm ⟨j, hj⟩)⟩, ?_⟩
    simp only [leviIdx, Equiv.apply_symm_apply]

theorem prod_leviIndex {M : Type*} [CommMonoid M] (f : LeviIndex n β → M) :
    ∏ ij, f ij = ∏ a : Set.range β, ∏ p : Fin (blockSize β a) × Fin (blockSize β a),
      f (leviIdx β a p.1 p.2) := by
  rw [← Fintype.prod_equiv (Equiv.ofBijective _ leviIdx_bijective) (fun p => f (leviIdx β p.1 p.2.1 p.2.2)) f
    (fun p => rfl), Fintype.prod_sigma]


variable (β) in
def blockTensor (φ : LeviIndex n β → F → ℂ) (a : Set.range β)
    (X : Matrix (Fin (blockSize β a)) (Fin (blockSize β a)) F) : ℂ :=
  ∏ p : Fin (blockSize β a) × Fin (blockSize β a), φ (leviIdx β a p.1 p.2) (X p.1 p.2)

theorem leviTensor_leviEquivPi_symm (φ : LeviIndex n β → F → ℂ)
    (x : ∀ a : Set.range β, GL (Fin (blockSize β a)) F) :
    leviTensor β φ ((((leviEquivPi F β).symm x : levi F n β) : GL (Fin n) F) : Matrix _ _ F) =
      ∏ a, blockTensor β φ a (x a : Matrix (Fin (blockSize β a)) (Fin (blockSize β a)) F) := by
  rw [leviTensor, prod_leviIndex]
  refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun p _ => ?_
  simp only [leviIdx]
  rw [leviEquivPi_symm_apply_entry]

theorem isSchwartzBruhat_blockTensor {φ : LeviIndex n β → F → ℂ}
    (hφ : ∀ ij, φ ij ∈ LocalField.schwartzBruhat F) (a : Set.range β) :
    IsSchwartzBruhat (blockTensor β φ a) := by
  rw [GJMatrix.isSchwartzBruhat_iff_comp_symm]
  have : blockTensor β φ a ∘ (GJMatrix.matrixCoordHomeomorph (Fin (blockSize β a)) F).symm =
      GJMatrix.localTensor fun p : Fin (blockSize β a) × Fin (blockSize β a) =>
        φ (leviIdx β a p.1 p.2) := by
    funext z
    rfl
  rw [this]
  exact GJMatrix.localTensor_mem fun p => hφ _

variable [MeasurableSpace F] [BorelSpace F]

theorem localMatrixFourier_entryTensor (ψ : AddChar F Circle) {m : ℕ}
    (g : Fin m × Fin m → F → ℂ) (Y : Matrix (Fin m) (Fin m) F) :
    GJMatrix.localMatrixFourier ψ (fun X => ∏ p : Fin m × Fin m, g p (X p.1 p.2)) Y =
      ∏ p : Fin m × Fin m,
        LocalField.localFourier (LocalField.selfDualMeasure ψ) ψ (g p) (Y p.2 p.1) := by
  rw [GJMatrix.localMatrixFourier_eq]
  have : (fun X : Matrix (Fin m) (Fin m) F => ∏ p : Fin m × Fin m, g p (X p.1 p.2)) ∘
      (GJMatrix.matrixCoordHomeomorph (Fin m) F).symm = GJMatrix.localTensor g := by
    funext z
    rfl
  rw [this, GJMatrix.localFourierPi_localTensor]
  rfl

theorem leviTensorHat_leviEquivPi_symm (ψ : AddChar F Circle) (φ : LeviIndex n β → F → ℂ)
    (x : ∀ a : Set.range β, GL (Fin (blockSize β a)) F) :
    leviTensorHat β ψ φ ((((leviEquivPi F β).symm x : levi F n β) : GL (Fin n) F) : Matrix _ _ F) =
      ∏ a, GJMatrix.localMatrixFourier ψ (blockTensor β φ a)
        (x a : Matrix (Fin (blockSize β a)) (Fin (blockSize β a)) F) := by
  rw [leviTensorHat, prod_leviIndex]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [show blockTensor β φ a = fun X => ∏ p : Fin (blockSize β a) × Fin (blockSize β a),
    φ (leviIdx β a p.1 p.2) (X p.1 p.2) from rfl, localMatrixFourier_entryTensor]
  refine Finset.prod_congr rfl fun p _ => ?_
  simp only [leviIdx]
  rw [leviEquivPi_symm_apply_entry]

end LeviBlocks

section Main

universe uF u w

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] {n : ℕ} {α : Type u} [LinearOrder α] {β : Fin n → α}
  {W : Type w} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (levi F n β) W}

theorem nontrivial_of_isIrreducible {G : Type*} [Group G] (ρ : Representation ℂ G W)
    [ρ.IsIrreducible] : Nontrivial W := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  have : Subsingleton (Subrepresentation ρ) := ⟨fun S T => by
    cases S; cases T; congr 1; exact Subsingleton.elim _ _⟩
  exact bot_ne_top (Subsingleton.elim (⊥ : Subrepresentation ρ) ⊤)

theorem detPow_add (g : GL (Fin n) F) (a b : ℂ) : detPow g (a + b) = detPow g a * detPow g b := by
  rw [detPow_eq_qs_zpow, detPow_eq_qs_zpow, detPow_eq_qs_zpow, qs_add, mul_zpow]

theorem borelSpace_GL_units (m : ℕ) : BorelSpace (GL (Fin m) F) := by
  refine ⟨?_⟩
  have hM : (GJMatrix.measurableSpace_matrix : MeasurableSpace (Matrix (Fin m) (Fin m) F)) =
      _root_.borel (Matrix (Fin m) (Fin m) F) := BorelSpace.measurable_eq
  show MeasurableSpace.comap Units.val _ = _
  rw [hM, ← borel_comap, ← (Measures.isOpenEmbedding_val F m).isEmbedding.eq_induced]

theorem exists_leviFE (hσ : IsAdmissible σ) [σ.IsIrreducible] (hc : IsCuspidal σ)
    (κ : levi F n β →* ℝ≥0) (hκ : Continuous κ) (μM : Measure (levi F n β)) [μM.IsHaarMeasure]
    {ψ : AddChar F Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) :
    ∃ γ : RatFunc ℂ, LeviFE F σ κ μM ψ γ := by
  classical
  have _ : ∀ m : ℕ, BorelSpace (GL (Fin m) F) := fun m => borelSpace_GL_units m
  set e := leviEquivPi F β with he

  set κ' : (∀ a : Set.range β, GL (Fin (blockSize β a)) F) →* ℝ≥0 :=
    κ.comp e.symm.toMonoidHom with hκ'def
  have hκ' : Continuous κ' := hκ.comp e.symm.continuous
  set σ' : Representation ℂ (∀ a : Set.range β, GL (Fin (blockSize β a)) F) W :=
    σ.comp e.symm.toMonoidHom with hσ'def
  set ρ₀ := twist (nnrealCharC κ') σ' with hρ₀def
  set ρ : Representation ℂ ((∀ a : Set.range β, GL (Fin (blockSize β a)) F) × PUnit.{max u uF + 1}) W :=
    ρ₀.comp (prodPUnitEquiv (∀ a : Set.range β, GL (Fin (blockSize β a)) F)).toMulEquiv.toMonoidHom
    with hρdef
  have hρ : ∀ x (h : PUnit.{max u uF + 1}) v, ρ (x, h) v = ((κ (e.symm x) : ℝ) : ℂ) • σ (e.symm x) v :=
    fun x h v => rfl
  have hσ' : IsAdmissible σ' := (isAdmissible_comp_iff e.symm σ).2 hσ
  have hadm : IsAdmissible ρ := (isAdmissible_comp_iff
    (prodPUnitEquiv (∀ a : Set.range β, GL (Fin (blockSize β a)) F)) ρ₀).2
    (isAdmissible_twist κ' hκ' σ' hσ')
  have hirr' : σ'.IsIrreducible := (isIrreducible_comp_iff e.symm σ).2 inferInstance
  have hirr : ρ.IsIrreducible := (isIrreducible_comp_iff
    (prodPUnitEquiv (∀ a : Set.range β, GL (Fin (blockSize β a)) F)) ρ₀).2
    (isIrreducible_twist κ' σ')
  have hsm : ∀ ℓ : Module.Dual ℂ W, ℓ ∈ smoothVectors (Representation.dual ρ) ↔
      ℓ ∈ smoothVectors (Representation.dual σ) := fun ℓ => by
    rw [mem_smoothVectors_dual_comp_iff
      (prodPUnitEquiv (∀ a : Set.range β, GL (Fin (blockSize β a)) F)) ρ₀,
      mem_smoothVectors_dual_twist_iff κ' hκ' σ', mem_smoothVectors_dual_comp_iff e.symm σ]

  obtain ⟨ω, hω⟩ := exists_blockChar hσ.1 (σ := σ)
  have hW : Nontrivial W := nontrivial_of_isIrreducible σ
  have hω0 : ∀ a, ω a ≠ 0 := by
    intro a h0
    obtain ⟨v, hv⟩ := exists_ne (0 : W)
    apply hv
    have h1 : σ (blockUnif F a)⁻¹ (σ (blockUnif F a) v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [← h1, hω, h0, zero_smul, map_zero]
  set αc : Set.range β → ℂ := fun a => ((κ (blockUnif F a) : ℝ) : ℂ) * ω a with hαc
  have hα0 : ∀ a, αc a ≠ 0 := fun a =>
    mul_ne_zero (by simpa using nnrealCharC_ne_zero κ (blockUnif F a)) (hω0 a)
  have hα : ∀ a v, ρ (Pi.mulSingle a (centralUnif F (blockSize β a)), 1) v = αc a • v := by
    intro a v
    rw [hρ, leviEquivPi_symm_mulSingle, hω, smul_smul]

  have hsupp : ∀ v : W, ∀ ℓ ∈ smoothVectors (Representation.dual ρ),
      ∃ C : Set (∀ a : Set.range β, GL (Fin (blockSize β a)) F), IsCompact C ∧
        ∀ x, ℓ (ρ (x, 1) v) ≠ 0 →
          ∃ j : Set.range β → ℤ, (fun a => centralUnif F (blockSize β a) ^ j a) * x ∈ C := by
    intro v ℓ hℓ
    have hℓσ := (hsm ℓ).1 hℓ
    obtain ⟨CM, hCM, hCMs⟩ := exists_compact_of_coeff hσ.1 hc v hℓσ (fun _ => 0)
      (fun b => (blockSize β b : ℤ) - 1)
    refine ⟨e '' CM, hCM.image e.continuous, fun x hx => ?_⟩
    have hpos : ∀ b, (0 : ℤ) < blockSize β b := fun b => by exact_mod_cast blockSize_pos β b
    set j : Set.range β → ℤ := fun b => -(ordDet (x b) / blockSize β b) with hj
    refine ⟨j, e.symm ((fun a => centralUnif F (blockSize β a) ^ j a) * x), ?_, by simp⟩
    refine hCMs _ ?_ fun b => ?_
    · have hmul := apply_centralPow ρ hα0 hα j (ρ (x, 1) v)
      have h2 : ρ ((fun a => centralUnif F (blockSize β a) ^ j a) * x, 1) v =
          (∏ a, αc a ^ j a) • ρ (x, 1) v := by
        rw [← hmul, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
      have h3 := hρ ((fun a => centralUnif F (blockSize β a) ^ j a) * x) 1 v
      intro h0
      apply hx
      have hprod0 : (∏ a, αc a ^ j a) ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => zpow_ne_zero _ (hα0 a)
      have hκ0 := nnrealCharC_ne_zero κ (e.symm ((fun a => centralUnif F (blockSize β a) ^ j a) * x))
      rw [nnrealCharC_apply] at hκ0
      have : ℓ (ρ ((fun a => centralUnif F (blockSize β a) ^ j a) * x, 1) v) = 0 := by
        rw [h3, map_smul, smul_eq_mul, h0, mul_zero]
      rw [h2, map_smul, smul_eq_mul] at this
      exact (mul_eq_zero.1 this).resolve_left hprod0
    · rw [← ordDet_leviEquivPi, ContinuousMulEquiv.apply_symm_apply, Pi.mul_apply,
        ordDet_centralUnif_zpow_mul]
      have h1 := Int.emod_nonneg (ordDet (x b)) (hpos b).ne'
      have h2 := Int.emod_lt_of_pos (ordDet (x b)) (hpos b)
      have h3 := Int.emod_def (ordDet (x b)) (blockSize β b)
      simp only [hj]
      constructor <;> nlinarith

  have _ : ∀ a : Set.range β, NeZero (blockSize β a) := fun a => ⟨(blockSize_pos β a).ne'⟩
  set μb : ∀ a : Set.range β, Measure (GL (Fin (blockSize β a)) F) := fun a => Measure.haar
    with hμb
  obtain ⟨γ, hmain⟩ := multiFEStatement_all.{uF, u, w} hψ hψ1
    (Fintype.card (Set.range β)) (Set.range β) rfl (fun a => blockSize β a) μb
    PUnit.{max u uF + 1} ρ hadm hirr αc hα0 hα hsupp
  obtain ⟨s₀, hconv⟩ := exists_integrable_multi ρ hadm.1 hα0 hα hsupp μb

  set em := e.toHomeomorph.toMeasurableEquiv with hem
  have hν : (Measure.map em μM).IsHaarMeasure :=
    MulEquiv.isHaarMeasure_map μM e.toMulEquiv e.continuous e.symm.continuous
  set c := haarScalarFactor (Measure.map em μM) (Measure.pi μb) with hcdef
  have hc : Measure.map em μM = c • Measure.pi μb :=
    Measure.isMulLeftInvariant_eq_smul (Measure.map em μM) (Measure.pi μb)
  have hemx : ∀ m, e.symm (em m) = m := fun m => e.symm_apply_apply m
  have hint_eq : ∀ f : levi F n β → ℂ,
      ∫ m, f m ∂μM = ((c : ℝ) : ℂ) * ∫ x, f (e.symm x) ∂Measure.pi μb := by
    intro f
    have h1 : ∫ x, f (e.symm x) ∂(Measure.map em μM) = ∫ m, f m ∂μM := by
      rw [integral_map_equiv em]
      simp only [hemx]
    rw [← h1, hc, show (c • Measure.pi μb) = ((c : ℝ≥0∞) • Measure.pi μb) from rfl,
      integral_smul_measure, ENNReal.coe_toReal, Complex.real_smul]
  have hint_of : ∀ f : levi F n β → ℂ,
      Integrable (fun x => f (e.symm x)) (Measure.pi μb) → Integrable f μM := by
    intro f hf
    have h1 : Integrable (fun x => f (e.symm x)) (Measure.map em μM) := by
      rw [hc, show (c • Measure.pi μb) = ((c : ℝ≥0∞) • Measure.pi μb) from rfl]
      exact hf.smul_measure ENNReal.coe_ne_top
    rw [integrable_map_equiv] at h1
    exact h1.congr (Filter.Eventually.of_forall fun m => by simp only [Function.comp_apply, hemx])
  refine ⟨γ, fun φ hφ w ℓ hℓ => ?_⟩
  set Ψ : ∀ a : Set.range β, Matrix (Fin (blockSize β a)) (Fin (blockSize β a)) F → ℂ :=
    fun a => blockTensor β φ a with hΨdef
  have hΨ : ∀ a, IsSchwartzBruhat (Ψ a) := fun a => isSchwartzBruhat_blockTensor hφ a
  have hℓρ : ℓ ∈ smoothVectors (Representation.dual ρ) := (hsm ℓ).2 hℓ
  have hA_eq : ∀ s x, leviIntegrand σ κ (leviTensor β φ) w ℓ s (e.symm x) =
      multiA ρ Ψ w ℓ s x := by
    intro s x
    simp only [leviIntegrand, multiA]
    rw [leviTensor_leviEquivPi_symm, detPow_leviEquivPi_symm, hρ, map_smul, smul_eq_mul,
      Finset.prod_mul_distrib]
    ring
  have hB_eq : ∀ s x, leviIntegrandB σ κ (leviTensorHat β ψ φ) w ℓ s (e.symm x) =
      multiB ρ (fun a => GJMatrix.localMatrixFourier ψ (Ψ a)) w ℓ s x := by
    intro s x
    simp only [leviIntegrandB, multiB]
    rw [leviTensorHat_leviEquivPi_symm, leviModulus_leviEquivPi_symm, detPow_leviEquivPi_symm,
      hρ, map_smul, smul_eq_mul, map_inv e.symm x, map_inv κ]
    have hdet : ∀ a, detPow (x a) ((blockSize β a : ℂ) - s) =
        ((detModulusPow (x a) : ℝ) : ℂ) * detPow (x a) (-s) := fun a => by
      rw [sub_eq_add_neg, detPow_add, detPow_natCast]
    simp_rw [hdet]
    push_cast
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    ring
  refine ⟨⟨s₀, fun s hs => hint_of _ (((hconv Ψ hΨ w ℓ hℓρ).1 s hs).congr
      (Filter.Eventually.of_forall fun x => (hA_eq s x).symm))⟩,
    ⟨-s₀, fun s hs => hint_of _ (((hconv (fun a => GJMatrix.localMatrixFourier ψ (Ψ a))
      (fun a => (hΨ a).localMatrixFourier hψ hψ1) w ℓ hℓρ).2 s hs).congr
      (Filter.Eventually.of_forall fun x => (hB_eq s x).symm))⟩, ?_⟩
  refine ((hmain Ψ hΨ w ℓ hℓρ).const_mul ((c : ℝ) : ℂ)).congr ⟨0, fun s _ => ?_⟩ ⟨0, fun s _ => ?_⟩
  · rw [hint_eq]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => hA_eq s x)
  · rw [hint_eq]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => hB_eq s x)

end Main

end GodementJacquet

end GroundTheory.Automorphic
end
end

section -- merged from GroundTheory.AutomorphicForms.GL2.GJFEInduced
noncomputable section

namespace GroundTheory.Automorphic

namespace GodementJacquet

open Matrix GLnLocal Parabolic Iwasawa Measures MeasureTheory GJMatrix
open scoped NNReal ENNReal Pointwise

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
  {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (levi F n β) W}


variable (β) in
def leviMeasure (ψ : AddChar F Circle) : Measure (levi F n β) :=
  haarLevi β (leviCoordMeasure β ψ)

instance (ψ : AddChar F Circle) : (leviMeasure β ψ).IsHaarMeasure := by
  unfold leviMeasure
  infer_instance


omit [MeasurableSpace F] [BorelSpace F] in
theorem continuous_inducedChar : Continuous (inducedChar (F := F) β) := by
  have h3 : Continuous (leviAbsDetShift (F := F) β) := by
    refine continuous_monoidHom_of_eq_one _
      ⟨leviIntegral F n β, isOpen_leviIntegral (F := F)⟩ fun k hk => ?_
    show leviAbsDet β k ^ (((n : ℝ) - 1) / 2) = 1
    rw [leviAbsDet_of_mem_integralGL (Subgroup.mem_subgroupOf.1 hk), NNReal.one_rpow]
  exact (continuous_leviRatio.mul continuous_leviSqrtModular).mul h3

theorem iwasawa_transfer (μG : Measure (GL (Fin n) F)) [μG.IsHaarMeasure]
    (μP : Measure (blockUpper F n β)) [μP.IsHaarMeasure] (r : ℕ)
    [Fintype (integralGL F n ⧸ (congruenceSubgroup F n r).subgroupOf (integralGL F n))] :
    ∃ C : ℂ, ∀ f : GL (Fin n) F → ℂ, Continuous f →
      (∀ g, ∀ k ∈ congruenceSubgroup F n r, f (g * k) = f g) →
      (∀ q : integralGL F n ⧸ (congruenceSubgroup F n r).subgroupOf (integralGL F n),
        Integrable (fun p : blockUpper F n β =>
          f ((p : GL (Fin n) F) * ((q.out : integralGL F n) : GL (Fin n) F))) μP) →
      Integrable f μG ∧ ∫ g, f g ∂μG = C * ∑ q : integralGL F n ⧸
        (congruenceSubgroup F n r).subgroupOf (integralGL F n),
          ∫ p, f ((p : GL (Fin n) F) * ((q.out : integralGL F n) : GL (Fin n) F)) ∂μP := by
  classical
  have : BorelSpace (integralGL F n) := Subtype.borelSpace _
  have : CompactSpace (integralGL F n) :=
    isCompact_iff_compactSpace.1 (isCompact_integralGL F n)
  let μK : Measure (integralGL F n) := Measure.haar
  set κ : ℝ := μP.real (Subtype.val ⁻¹' (integralGL F n : Set (GL (Fin n) F))) * μK.real Set.univ
    with hκ
  set κ' : ℝ := μG.real (integralGL F n) * μK.real ((congruenceSubgroup F n r).subgroupOf
      (integralGL F n) : Set (integralGL F n)) with hκ'
  refine ⟨((κ⁻¹ * κ' : ℝ) : ℂ), fun f hf hr hint => ?_⟩
  have hintP : ∀ y ∈ integralGL F n,
      Integrable (fun p : blockUpper F n β => f ((p : GL (Fin n) F) * y)) μP := by
    intro y hy
    obtain ⟨h, hq⟩ := QuotientGroup.mk_out_eq_mul
      ((congruenceSubgroup F n r).subgroupOf (integralGL F n)) (⟨y, hy⟩ : integralGL F n)
    have heq : ∀ p : blockUpper F n β, f ((p : GL (Fin n) F) * y) =
        f ((p : GL (Fin n) F) * (((QuotientGroup.mk ⟨y, hy⟩ : integralGL F n ⧸
          (congruenceSubgroup F n r).subgroupOf (integralGL F n)).out : integralGL F n) :
            GL (Fin n) F)) := by
      intro p
      rw [hq, Subgroup.coe_mul, ← mul_assoc]
      exact (hr _ _ (Subgroup.mem_subgroupOf.1 h.2)).symm
    simp_rw [heq]
    exact hint _
  have hP0 : μP (Subtype.val ⁻¹' (integralGL F n : Set (GL (Fin n) F))) ≠ 0 :=
    ((isOpen_integralGL F n).preimage continuous_subtype_val).measure_ne_zero _
      ⟨1, by simp [one_mem]⟩
  have hK0 : μK Set.univ ≠ 0 := isOpen_univ.measure_ne_zero μK Set.univ_nonempty
  have hintG : Integrable f μG := by
    refine ⟨hf.aestronglyMeasurable, ?_⟩
    have hC := lintegral_eq_sum_parabolic (β := β) (r := r) μG μP μK hf.enorm.measurable
      (h := fun g => ‖f g‖ₑ) (fun g k hk => by simp only [hr g k hk])
    have hlt : μG (integralGL F n) * (μK ((congruenceSubgroup F n r).subgroupOf
        (integralGL F n)) * ∑ q : integralGL F n ⧸ (congruenceSubgroup F n r).subgroupOf
          (integralGL F n), ∫⁻ p, ‖f ((p : GL (Fin n) F) *
          ((q.out : integralGL F n) : GL (Fin n) F))‖ₑ ∂μP) < ⊤ :=
      ENNReal.mul_lt_top (isCompact_integralGL F n).measure_lt_top
        (ENNReal.mul_lt_top (measure_lt_top _ _)
          (ENNReal.sum_lt_top.2 fun q _ => (hint q).2))
    rw [hC] at hlt
    exact ENNReal.lt_top_of_mul_ne_top_right hlt.ne (mul_ne_zero hP0 hK0)
  refine ⟨hintG, ?_⟩
  have hκ0 : κ ≠ 0 := by
    rw [hκ]
    have hPc : IsCompact (Subtype.val ⁻¹' (integralGL F n : Set (GL (Fin n) F)) :
        Set (blockUpper F n β)) :=
      (Measures.isClosed_blockUpper F n β).isClosedEmbedding_subtypeVal.isCompact_preimage
        (isCompact_integralGL F n)
    exact mul_ne_zero (ENNReal.toReal_ne_zero.2 ⟨hP0, hPc.measure_lt_top.ne⟩)
      (ENNReal.toReal_ne_zero.2 ⟨hK0, measure_ne_top _ _⟩)
  have hC := integral_eq_sum_parabolic (β := β) μG μP μK hintG hr hintP
  rw [Complex.real_smul, Complex.real_smul, Complex.real_smul] at hC
  have hκC : (κ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hκ0
  rw [← hκ, ← mul_assoc, ← Complex.ofReal_mul, ← hκ'] at hC
  push_cast
  field_simp
  linear_combination hC.symm

omit [MeasurableSpace F] [BorelSpace F] in
theorem detPow_inv_mul_of_mem {y : GL (Fin n) F} (hy : y ∈ integralGL F n) (g : GL (Fin n) F)
    (s : ℂ) : detPow (y⁻¹ * g) s = detPow g s := by
  rw [detPow_mul, detPow_of_mem_integralGL ((integralGL F n).inv_mem hy), one_mul]

theorem inducedFE_of_leviFE [mG : MeasurableSpace (GL (Fin n) F)] [hGB : BorelSpace (GL (Fin n) F)]
    (μG : Measure (GL (Fin n) F)) [μG.IsHaarMeasure] {ψ : AddChar F Circle} (hψ : Continuous ψ)
    (hψ1 : ψ ≠ 1) {γ : RatFunc ℂ} (hL : LeviFE F σ (inducedChar β) (leviMeasure β ψ) ψ γ) :
    InducedFE F σ μG ψ γ := by
  classical
  obtain rfl : mG = Units.instMeasurableSpace :=
    hGB.measurable_eq.trans (borelSpace_GL (F := F) (n := n)).measurable_eq.symm
  intro Φ hΦ φ hφ ℓ hℓ

  obtain ⟨r₁, hr₁⟩ := hΦ.exists_mul_congruenceSubgroup
  obtain ⟨K', hK'o, hK'⟩ := hφ.2
  obtain ⟨r₂, -, hr₂⟩ := (hasBasis_nhds_one F n).mem_iff.1 (hK'o.mem_nhds K'.one_mem)
  set r := max r₁ r₂ with hrdef
  have hΦr : ∀ X : Matrix (Fin n) (Fin n) F, ∀ k ∈ congruenceSubgroup F n r,
      Φ (X * (k : Matrix (Fin n) (Fin n) F)) = Φ X := fun X k hk =>
    hr₁ X k (congruenceSubgroup_antitone F n (le_max_left _ _) hk)
  have hφr : ∀ g, ∀ k ∈ congruenceSubgroup F n r, φ (g * k) = φ g := fun g k hk =>
    hK' k (hr₂ (congruenceSubgroup_antitone F n (le_max_right _ _) hk)) g
  have hk₀ : ∀ k ∈ congruenceSubgroup F n r, k ∈ integralGL F n := fun k hk =>
    congruenceSubgroup_le F n r hk
  have : CompactSpace (integralGL F n) :=
    isCompact_iff_compactSpace.1 (isCompact_integralGL F n)
  have : Finite (integralGL F n ⧸ (congruenceSubgroup F n r).subgroupOf (integralGL F n)) :=
    Subgroup.quotient_finite_of_isOpen _
      ((isOpen_congruenceSubgroup F n r).preimage continuous_subtype_val)
  let _ := Fintype.ofFinite
    (integralGL F n ⧸ (congruenceSubgroup F n r).subgroupOf (integralGL F n))
  obtain ⟨C, hCf⟩ := iwasawa_transfer (β := β) μG (measureP β ψ) r
  set y : integralGL F n ⧸ (congruenceSubgroup F n r).subgroupOf (integralGL F n) →
    GL (Fin n) F := fun q => ((q.out : integralGL F n) : GL (Fin n) F) with hydef
  have hy : ∀ q, y q ∈ integralGL F n := fun q => (q.out).2

  have hD := fun q => levi_decomp hψ hψ1 hL (hΦ.comp_mulRight (y q)) (φ (y q)) hℓ
  choose sA hsA using fun q => (hD q).1
  choose sB hsB using fun q => (hD q).2.1
  have hRq := fun q => (hD q).2.2
  set s₁ : ℝ := ∑ q, (|sA q| + |sB q|) with hs₁
  have hsA' : ∀ q, sA q ≤ s₁ := fun q =>
    (le_abs_self _).trans ((le_add_of_nonneg_right (abs_nonneg _)).trans
      (Finset.single_le_sum (f := fun q => |sA q| + |sB q|)
        (fun q _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ q)))
  have hsB' : ∀ q, -s₁ ≤ sB q := fun q => by
    have h1 : |sB q| ≤ s₁ := (le_add_of_nonneg_left (abs_nonneg _)).trans
      (Finset.single_le_sum (f := fun q => |sA q| + |sB q|)
        (fun q _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ q))
    linarith [neg_abs_le (sB q)]

  have hcontA : ∀ s : ℂ, Continuous fun g : GL (Fin n) F =>
      Φ (g : Matrix (Fin n) (Fin n) F) * detPow g (s + ((n : ℂ) - 1) / 2) * ℓ (φ g) :=
    fun s => continuous_inducedIntegrand hΦ hφ.2 ℓ _
  have hrA : ∀ s : ℂ, ∀ g, ∀ k ∈ congruenceSubgroup F n r,
      Φ ((g * k : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
          detPow (g * k) (s + ((n : ℂ) - 1) / 2) * ℓ (φ (g * k)) =
        Φ (g : Matrix (Fin n) (Fin n) F) * detPow g (s + ((n : ℂ) - 1) / 2) * ℓ (φ g) := by
    intro s g k hk
    rw [Units.val_mul, hΦr _ k hk, detPow_mul_of_mem_integralGL g (hk₀ k hk), hφr g k hk]
  have hPA : ∀ s : ℂ, s₁ < s.re → ∀ q, Integrable (fun p : blockUpper F n β =>
      Φ (((p : GL (Fin n) F) * y q : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
        detPow ((p : GL (Fin n) F) * y q) (s + ((n : ℂ) - 1) / 2) *
          ℓ (φ ((p : GL (Fin n) F) * y q))) (measureP β ψ) := by
    intro s hs q
    refine ⟨((hcontA s).comp (continuous_subtype_val.mul continuous_const)).aestronglyMeasurable,
      ?_⟩
    show ∫⁻ p, ‖inducedIntegrand Φ φ ℓ (s + ((n : ℂ) - 1) / 2) ((p : GL (Fin n) F) * y q)‖ₑ
      ∂measureP β ψ < ⊤
    rw [lintegral_inducedIntegrand_mul (leviCoordMeasure β ψ) (unipMeasure β ψ) hΦ hφ ℓ _ (hy q)]
    simp_rw [leviIntegrand_shift]
    exact hsA q s (lt_of_le_of_lt (hsA' q) hs)
  have hformA : ∀ s : ℂ, s₁ < s.re →
      Integrable (fun g : GL (Fin n) F =>
        Φ (g : Matrix (Fin n) (Fin n) F) * detPow g (s + ((n : ℂ) - 1) / 2) * ℓ (φ g)) μG ∧
      ∫ g, Φ (g : Matrix (Fin n) (Fin n) F) * detPow g (s + ((n : ℂ) - 1) / 2) * ℓ (φ g) ∂μG =
        C * ∑ q, ∫ m, leviIntegrand σ (inducedChar β)
          (fun X => ∫ u, Φ ((X + unipMatrix F u) * (y q : Matrix (Fin n) (Fin n) F))
            ∂unipMeasure β ψ) (φ (y q)) ℓ s m ∂measureM β ψ := by
    intro s hs
    obtain ⟨hint, heq⟩ := hCf _ (hcontA s) (hrA s) (hPA s hs)
    refine ⟨hint, heq.trans ?_⟩
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    have := integral_inducedIntegrand_mul (leviCoordMeasure β ψ) (unipMeasure β ψ) hφ ℓ
      (s + ((n : ℂ) - 1) / 2) (hy q) (hPA s hs q)
    simp only [inducedIntegrand] at this
    rw [this]
    simp_rw [leviIntegrand_shift]

  set fB : ℂ → GL (Fin n) F → ℂ := fun s g =>
    localMatrixFourier ψ Φ (g : Matrix (Fin n) (Fin n) F) *
      detPow g (1 - s + ((n : ℂ) - 1) / 2) * ℓ (φ g⁻¹) with hfB
  have hΦh : IsSchwartzBruhat (localMatrixFourier ψ Φ) := hΦ.localMatrixFourier hψ hψ1
  have hℓφ : Continuous fun g => ℓ (φ g) := by
    refine IsLocallyConstant.continuous fun S => isOpen_iff_forall_mem_open.2 fun g hg => ?_
    refine ⟨g • (K' : Set (GL (Fin n) F)), ?_, hK'o.smul g, ⟨1, one_mem _, mul_one g⟩⟩
    rintro _ ⟨k, hk, rfl⟩
    simp only [Set.mem_preimage, smul_eq_mul, hK' k hk]
    exact hg
  have hcontB : ∀ s : ℂ, Continuous fun g : GL (Fin n) F => fB s g⁻¹ := fun s =>
    ((hΦh.1.continuous.comp (Units.continuous_val.comp continuous_inv)).mul
      ((continuous_detPow _).comp continuous_inv)).mul (hℓφ.comp (continuous_inv.comp continuous_inv))
  have hΦhr : ∀ Z : Matrix (Fin n) (Fin n) F, ∀ k ∈ congruenceSubgroup F n r,
      localMatrixFourier ψ Φ (((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * Z) =
        localMatrixFourier ψ Φ Z := by
    intro Z k hk
    rw [← localMatrixFourier_mul_right ψ Φ (hk₀ k hk) Z]
    congr 1
    funext X
    exact hΦr X k hk
  have hrB : ∀ s : ℂ, ∀ g, ∀ k ∈ congruenceSubgroup F n r, fB s (g * k)⁻¹ = fB s g⁻¹ := by
    intro s g k hk
    simp only [hfB, _root_.mul_inv_rev, inv_inv, Units.val_mul]
    rw [hΦhr _ k hk, detPow_inv_mul_of_mem (hk₀ k hk), hφr g k hk]
  have hΞ : ∀ q, IsSchwartzBruhat
      (localMatrixFourier ψ fun X => Φ (X * (y q : Matrix (Fin n) (Fin n) F))) := fun q =>
    (hΦ.comp_mulRight (y q)).localMatrixFourier hψ hψ1
  have hBeq : ∀ s : ℂ, ∀ q, ∀ p : blockUpper F n β, fB s ((p : GL (Fin n) F) * y q)⁻¹ =
      parabolicB β (localMatrixFourier ψ fun X => Φ (X * (y q : Matrix (Fin n) (Fin n) F)))
        φ ℓ s (y q) p⁻¹ := by
    intro s q p
    simp only [hfB, parabolicB, _root_.mul_inv_rev, inv_inv, Subgroup.coe_inv, Units.val_mul]
    rw [localMatrixFourier_mul_right ψ Φ (hy q), detPow_inv_mul_of_mem (hy q)]
  have hPB : ∀ s : ℂ, s.re < -s₁ → ∀ q, Integrable (fun p : blockUpper F n β =>
      fB s ((p : GL (Fin n) F) * y q)⁻¹) (measureP β ψ) := by
    intro s hs q
    simp_rw [hBeq s q]
    refine ⟨((continuous_parabolicB hφ (hΞ q) ℓ s (y q)).comp
      continuous_inv).aestronglyMeasurable, ?_⟩
    show ∫⁻ p, ‖parabolicB β (localMatrixFourier ψ fun X => Φ (X * (y q : Matrix (Fin n) (Fin n) F)))
      φ ℓ s (y q) p⁻¹‖ₑ ∂measureP β ψ < ⊤
    rw [lintegral_parabolicB_inv ψ hφ (hΞ q) ℓ s (y q)]
    exact hsB q s (lt_of_lt_of_le hs (hsB' q))
  have hinvG : μG.IsInvInvariant := ⟨inv_eq_self_GL F n μG⟩
  have hformB : ∀ s : ℂ, s.re < -s₁ → Integrable (fB s) μG ∧
      ∫ g, fB s g ∂μG = C * ∑ q, ∫ m, leviIntegrandB σ (inducedChar β)
        (fun X => ∫ u, localMatrixFourier ψ (fun X => Φ (X * (y q : Matrix (Fin n) (Fin n) F)))
          (X + unipMatrix F u) ∂unipMeasure β ψ) (φ (y q)) ℓ s m ∂measureM β ψ := by
    intro s hs
    obtain ⟨hint, heq⟩ := hCf (fun g => fB s g⁻¹) (hcontB s) (hrB s) (hPB s hs)
    refine ⟨?_, ?_⟩
    · simpa using hint.comp_inv
    · rw [← integral_inv_eq_self (fB s) μG, heq]
      congr 1
      refine Finset.sum_congr rfl fun q _ => ?_
      have hint2 : Integrable (fun p => parabolicB β
          (localMatrixFourier ψ fun X => Φ (X * (y q : Matrix (Fin n) (Fin n) F)))
            φ ℓ s (y q) p⁻¹) (measureP β ψ) := by
        have := hPB s hs q
        simp_rw [hBeq s q] at this
        exact this
      refine (integral_congr_ae (Filter.Eventually.of_forall fun p => hBeq s q p)).trans ?_
      exact integral_parabolicB_inv ψ hφ (hΞ q) ℓ s (y q) hint2
  refine ⟨⟨s₁, fun s hs => (hformA s hs).1⟩, ⟨-s₁, fun s hs => (hformB s hs).1⟩, ?_⟩
  have hR := (RatFE.sum Finset.univ fun q _ => hRq q).const_mul C
  exact hR.congr ⟨s₁, fun s hs => (hformA s hs).2⟩ ⟨-s₁, fun s hs => (hformB s hs).2⟩

end GodementJacquet

end GroundTheory.Automorphic
end
end

open MeasureTheory Filter Set Topology IsDedekindDomain NumberField NumberField.mixedEmbedding
open scoped NumberField.AdeleRing RestrictedProduct SchwartzMap Classical

namespace GroundTheory.Automorphic

noncomputable section

namespace GJStandardL

open GodementJacquet GLnLocal

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

instance measurableSpace_infiniteAdelicGL : MeasurableSpace (AdelicGLn.InfiniteAdelicGL K n) := _root_.borel _

instance borelSpace_infiniteAdelicGL : BorelSpace (AdelicGLn.InfiniteAdelicGL K n) := ⟨rfl⟩


variable (K n) in
def archComp : AdelicGLn.AdelicGL K n →* AdelicGLn.InfiniteAdelicGL K n :=
  (MonoidHom.fst _ _).comp (AdelicGLn.prodEquiv K n).toMonoidHom


variable (K n) in
def finComp : AdelicGLn.AdelicGL K n →* AdelicGLn.FiniteAdelicGL K n :=
  (MonoidHom.snd _ _).comp (AdelicGLn.prodEquiv K n).toMonoidHom


variable (n) in
def localComp (v : HeightOneSpectrum (𝓞 K)) :
    AdelicGLn.AdelicGL K n →* GL (Fin n) (v.adicCompletion K) where
  toFun g := AdelicGLn.finiteRestrictedEquiv K n (finComp K n g) v
  map_one' := by rw [map_one, map_one, RestrictedProduct.one_apply]
  map_mul' g h := by rw [map_mul, map_mul, RestrictedProduct.mul_apply]

def archMat (x : Matrix (Fin n) (Fin n) 𝔸[K]) : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K) :=
  x.map Prod.fst

def localMat (v : HeightOneSpectrum (𝓞 K)) (x : Matrix (Fin n) (Fin n) 𝔸[K]) :
    Matrix (Fin n) (Fin n) (v.adicCompletion K) :=
  x.map fun a ↦ a.2 v

theorem coe_archComp (g : AdelicGLn.AdelicGL K n) :
    ((archComp K n g : AdelicGLn.InfiniteAdelicGL K n) : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)) =
      archMat (g : Matrix (Fin n) (Fin n) 𝔸[K]) := by
  ext i j
  exact AdelicGLn.prodEquiv_apply_fst K n g i j

theorem coe_localComp (v : HeightOneSpectrum (𝓞 K)) (g : AdelicGLn.AdelicGL K n) :
    ((localComp n v g : GL (Fin n) (v.adicCompletion K)) : Matrix (Fin n) (Fin n) (v.adicCompletion K)) =
      localMat v (g : Matrix (Fin n) (Fin n) 𝔸[K]) := by
  ext i j
  rfl

theorem eventually_localComp_mem (g : AdelicGLn.AdelicGL K n) :
    ∀ᶠ v in cofinite, localComp n v g ∈ integralGL (v.adicCompletion K) n :=
  AdelicGLn.eventually_mem_integralGL K n g

def archSchwartz (φ : 𝓢(Fin n × Fin n → mixedEmbedding.mixedSpace K, ℂ))
    (x : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)) : ℂ :=
  φ fun ij ↦ GroundTheory.Global.homeomorphMixedSpace K (x ij.1 ij.2)

def matrixTensor (φ : 𝓢(Fin n × Fin n → mixedEmbedding.mixedSpace K, ℂ))
    (Φ : ∀ v : HeightOneSpectrum (𝓞 K), Matrix (Fin n) (Fin n) (v.adicCompletion K) → ℂ)
    (x : Matrix (Fin n) (Fin n) 𝔸[K]) : ℂ :=
  archSchwartz φ (archMat x) * ∏ᶠ v, Φ v (localMat v x)

def archAbsDet (x : AdelicGLn.InfiniteAdelicGL K n) : ℝ :=
  ∏ w : InfinitePlace K, ‖((x : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)).det) w‖ ^ w.mult

def archDetPow (x : AdelicGLn.InfiniteAdelicGL K n) (s : ℂ) : ℂ :=
  (archAbsDet x : ℂ) ^ s

def archIntegrand (φ : 𝓢(Fin n × Fin n → mixedEmbedding.mixedSpace K, ℂ))
    (f : AdelicGLn.InfiniteAdelicGL K n → ℂ) (s : ℂ) (x : AdelicGLn.InfiniteAdelicGL K n) : ℂ :=
  archSchwartz φ (x : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)) * f x *
    archDetPow x (s + ((n : ℂ) - 1) / 2)

def archZeta (μ : Measure (AdelicGLn.InfiniteAdelicGL K n))
    (φ : 𝓢(Fin n × Fin n → mixedEmbedding.mixedSpace K, ℂ)) (f : AdelicGLn.InfiniteAdelicGL K n → ℂ)
    (s : ℂ) : ℂ :=
  ∫ x, archIntegrand φ f s x ∂μ


variable (n) in
def integralGLPositiveCompacts (v : HeightOneSpectrum (𝓞 K)) :
    TopologicalSpace.PositiveCompacts (GL (Fin n) (v.adicCompletion K)) where
  carrier := integralGL (v.adicCompletion K) n
  isCompact' := isCompact_integralGL _ n
  interior_nonempty' := by
    rw [(isOpen_integralGL _ n).interior_eq]
    exact ⟨1, (integralGL _ n).one_mem⟩


variable (n) in
def localHaar (v : HeightOneSpectrum (𝓞 K)) : Measure (GL (Fin n) (v.adicCompletion K)) :=
  Measure.haarMeasure (integralGLPositiveCompacts n v)

instance isHaarMeasure_localHaar (v : HeightOneSpectrum (𝓞 K)) : (localHaar n v).IsHaarMeasure := by
  unfold localHaar
  infer_instance

theorem localHaar_integralGL (v : HeightOneSpectrum (𝓞 K)) :
    localHaar n v (integralGL (v.adicCompletion K) n : Set (GL (Fin n) (v.adicCompletion K))) = 1 :=
  Measure.haarMeasure_self

def partialL (S : Finset (HeightOneSpectrum (𝓞 K))) {V : HeightOneSpectrum (𝓞 K) → Type*}
    [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
    (π : ∀ v, Representation ℂ (GL (Fin n) (v.adicCompletion K)) (V v)) (s : ℂ) : ℂ :=
  ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}, LFunction (π v) s

end GJStandardL

end

end GroundTheory.Automorphic
