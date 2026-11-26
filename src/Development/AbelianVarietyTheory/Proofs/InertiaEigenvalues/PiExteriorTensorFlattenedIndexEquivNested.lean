module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientOfEquiv
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.DerivDerivNonposOfIsLocalMax
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyMeasAndReps

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PiExteriorTensorFlattenedIndexEquivNested
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PiExteriorTensorFlattenedIndexEquivNested
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.JacStages

noncomputable section

open PiTensorProduct Module
open scoped TensorProduct

namespace GlobalTheory.JacStages

section SigmaCurry

variable {α : Type} [DecidableEq α] {β : α → Type} [∀ a, DecidableEq (β a)]
  (M : (Σ a, β a) → Type) [∀ p, AddCommGroup (M p)] [∀ p, Module ℂ (M p)]

theorem tprod_tprod_update_sigma [DecidableEq (Σ a, β a)] (x : ∀ p, M p) (a₀ : α) (b₀ : β a₀)
    (v : M ⟨a₀, b₀⟩) :
    (fun a => tprod ℂ fun b => Function.update x ⟨a₀, b₀⟩ v ⟨a, b⟩) =
      Function.update (fun a => tprod ℂ fun b => x ⟨a, b⟩) a₀
        (tprod ℂ (Function.update (fun b => x ⟨a₀, b⟩) b₀ v)) := by
  funext a
  by_cases h : a = a₀
  · subst h
    rw [Function.update_self]
    congr 1
    funext b
    by_cases hb : b = b₀
    · subst hb
      simp
    · rw [Function.update_of_ne hb, Function.update_of_ne]
      intro h'
      exact hb (eq_of_heq (Sigma.mk.inj h').2)
  · rw [Function.update_of_ne h]
    congr 1
    funext b
    rw [Function.update_of_ne]
    intro h'
    exact h (congrArg Sigma.fst h')

def curryML : (∀ p, M p) →ₘₗ[ℂ] ⨂[ℂ] a, ⨂[ℂ] b, M ⟨a, b⟩ where
  toFun x := tprod ℂ fun a => tprod ℂ fun b => x ⟨a, b⟩
  map_update_add' x p v w := by
    obtain ⟨a₀, b₀⟩ := p
    simp only [tprod_tprod_update_sigma]
    rw [MultilinearMap.map_update_add, MultilinearMap.map_update_add]
  map_update_smul' x p c v := by
    obtain ⟨a₀, b₀⟩ := p
    simp only [tprod_tprod_update_sigma, MultilinearMap.map_update_smul, RingHom.id_apply]

theorem curryML_apply (x : ∀ p, M p) : curryML M x = tprod ℂ fun a => tprod ℂ fun b => x ⟨a, b⟩ := rfl

variable [Finite α] [∀ a, Finite (β a)]

def sigBasis : Basis (∀ p, Free.ChooseBasisIndex ℂ (M p)) ℂ (⨂[ℂ] p, M p) :=
  Basis.piTensorProduct fun p => Free.chooseBasis ℂ (M p)

def nestBasis : Basis (∀ a b, Free.ChooseBasisIndex ℂ (M ⟨a, b⟩)) ℂ (⨂[ℂ] a, ⨂[ℂ] b, M ⟨a, b⟩) :=
  Basis.piTensorProduct fun a => Basis.piTensorProduct fun b => Free.chooseBasis ℂ (M ⟨a, b⟩)

def sigmaCurry : (⨂[ℂ] p, M p) ≃ₗ[ℂ] ⨂[ℂ] a, ⨂[ℂ] b, M ⟨a, b⟩ :=
  (sigBasis M).equiv (nestBasis M) (Equiv.piCurry fun a b => Free.ChooseBasisIndex ℂ (M ⟨a, b⟩))

theorem sigmaCurry_eq_lift : (sigmaCurry M : (⨂[ℂ] p, M p) →ₗ[ℂ] _) = lift (curryML M) := by
  apply (sigBasis M).ext
  intro q
  rw [LinearEquiv.coe_coe, sigmaCurry, Basis.equiv_apply]
  simp only [sigBasis, nestBasis, Basis.piTensorProduct_apply, lift.tprod, curryML_apply]
  rfl

@[simp] theorem sigmaCurry_tprod (x : ∀ p, M p) :
    sigmaCurry M (tprod ℂ x) = tprod ℂ fun a => tprod ℂ fun b => x ⟨a, b⟩ := by
  have h := LinearMap.congr_fun (sigmaCurry_eq_lift M) (tprod ℂ x)
  simpa [curryML_apply] using h

end SigmaCurry

section Flat

variable {s : ℕ} {t : Fin s → ℕ}

def flatTensorEquiv (Y : ∀ a, Fin (t a) → Type) [∀ a b, AddCommGroup (Y a b)] [∀ a b, Module ℂ (Y a b)] :
    (⨂[ℂ] c : Fin (∑ a, t a), Y (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2) ≃ₗ[ℂ]
      ⨂[ℂ] a, ⨂[ℂ] b, Y a b :=
  (reindex ℂ (fun p : Σ a, Fin (t a) => Y p.1 p.2) finSigmaFinEquiv).symm.trans
    (sigmaCurry fun p : Σ a, Fin (t a) => Y p.1 p.2)

theorem flatTensorEquiv_reindex_tprod (Y : ∀ a, Fin (t a) → Type) [∀ a b, AddCommGroup (Y a b)]
    [∀ a b, Module ℂ (Y a b)] (x : ∀ p : Σ a, Fin (t a), Y p.1 p.2) :
    flatTensorEquiv Y (reindex ℂ (fun p : Σ a, Fin (t a) => Y p.1 p.2) finSigmaFinEquiv (tprod ℂ x)) =
      tprod ℂ fun a => tprod ℂ fun b => x ⟨a, b⟩ := by
  rw [flatTensorEquiv, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, sigmaCurry_tprod]

theorem flatTensorEquiv_tprod (Y : ∀ a, Fin (t a) → Type) [∀ a b, AddCommGroup (Y a b)]
    [∀ a b, Module ℂ (Y a b)] (x : ∀ p : Σ a, Fin (t a), Y p.1 p.2) :
    flatTensorEquiv Y (tprod ℂ fun c => x (finSigmaFinEquiv.symm c)) =
      tprod ℂ fun a => tprod ℂ fun b => x ⟨a, b⟩ := by
  rw [← flatTensorEquiv_reindex_tprod, reindex_tprod]

theorem piTensor_flatHom_equiv : ∀ (s : ℕ) (t : Fin s → ℕ) (Γ : ∀ a, Fin (t a) → Type) [∀ a b, Group (Γ a b)]
    (Y : ∀ a, Fin (t a) → Type) [∀ a b, AddCommGroup (Y a b)] [∀ a b, Module ℂ (Y a b)]
    (ρ : ∀ a b, Representation ℂ (Γ a b) (Y a b)),
    Nonempty (Representation.Equiv ((piTensor fun c : Fin (∑ a, t a) =>
        ρ (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2).comp (flatHom Γ))
      (piTensor fun a => piTensor (ρ a))) := by
  intro s t Γ _ Y _ _ ρ
  refine ⟨Representation.Equiv.mk (flatTensorEquiv Y) fun g => ?_⟩
  have key : ∀ w : ⨂[ℂ] p : Σ a, Fin (t a), Y p.1 p.2,
      flatTensorEquiv Y (((piTensor fun c : Fin (∑ a, t a) =>
        ρ (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2).comp (flatHom Γ)) g
          (reindex ℂ (fun p : Σ a, Fin (t a) => Y p.1 p.2) finSigmaFinEquiv w)) =
        piTensor (fun a => piTensor (ρ a)) g
          (flatTensorEquiv Y (reindex ℂ (fun p : Σ a, Fin (t a) => Y p.1 p.2) finSigmaFinEquiv w)) := by
    intro w
    induction w using PiTensorProduct.induction_on with
    | smul_tprod r x =>
      simp only [map_smul]
      congr 1
      rw [flatTensorEquiv_reindex_tprod, piTensor_tprod]
      simp only [piTensor_tprod]
      rw [reindex_tprod, MonoidHom.comp_apply, piTensor_tprod]
      exact flatTensorEquiv_tprod Y fun p => ρ p.1 p.2 (g p.1 p.2) (x p)
    | add w w' hw hw' =>
      simp only [map_add (f := _)]
      rw [hw, hw']
  refine LinearMap.ext fun v => ?_
  obtain ⟨w, rfl⟩ := (reindex ℂ (fun p : Σ a, Fin (t a) => Y p.1 p.2) finSigmaFinEquiv).surjective v
  exact key w

end Flat

end GlobalTheory.JacStages
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PiExteriorTensorFlattenedIndexEquivNestedStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.JacStages
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.piExteriorTensor_flattenedIndex_equiv_nested : ∀ (s : ℕ) (t : Fin s → ℕ) (Γ : ∀ a, Fin (t a) → Type) [∀ a b, Group (Γ a b)]
    (Y : ∀ a, Fin (t a) → Type) [∀ a b, AddCommGroup (Y a b)] [∀ a b, Module ℂ (Y a b)]
    (ρ : ∀ a b, Representation ℂ (Γ a b) (Y a b)),
    Nonempty (Representation.Equiv ((piTensor fun c : Fin (∑ a, t a) =>
        ρ (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2).comp (flatHom Γ))
      (piTensor fun a => piTensor (ρ a))) := by
  first | exact @GlobalTheory.JacStages.piTensor_flatHom_equiv | exact GlobalTheory.JacStages.piTensor_flatHom_equiv | (intros; apply GlobalTheory.JacStages.piTensor_flatHom_equiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisInvKRegularIffIsUnit
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisInvKRegularIffIsUnit
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.EtInv

section Gen
variable {F K : Type} [Field F] [CommRing K] [Algebra F K] [Module.Finite F K]

theorem eq_zero_of_trace_mul [CharZero F] [IsReduced K] (a : K)
    (h : ∀ x : K, Algebra.trace F K (x * a) = 0) : a = 0 := by
  classical
  let b := Module.finBasis F K
  have hn : IsNilpotent (Algebra.leftMulMatrix b a) := by
    apply ReciprocityTheory.L2DbarEstimates.Y.isNilpotent_of_trace_pow
    intro k hk _
    rw [← map_pow, ← Algebra.trace_eq_matrix_trace]
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [pow_succ]
    exact h _
  obtain ⟨m, hm⟩ := hn
  rw [← map_pow, ← map_zero (Algebra.leftMulMatrix b)] at hm
  exact (IsNilpotent.eq_zero ⟨m, Algebra.leftMulMatrix_injective b hm⟩)

variable {r : ℕ} {τ : K}

theorem trace_mul_eq_sum (bb : Module.Basis (Fin r) F K) (hb : ∀ i, bb i = τ ^ (i : ℕ)) (x a : K) :
    Algebra.trace F K (x * a) = ∑ j, bb.repr x j * Algebra.trace F K (τ ^ (j : ℕ) * a) := by
  conv_lhs => rw [← bb.sum_repr x]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Finset.sum_mul, smul_mul_assoc, map_sum, hb]

end Gen

section Comp
variable {F K : Type} [Field F] [CommRing K] [Algebra F K] {r : ℕ} {τ : K} {p : Fin r → F}

theorem leftMulMatrix_eq_companion (bb : Module.Basis (Fin r) F K) (hb : ∀ i, bb i = τ ^ (i : ℕ))
    (hr : τ ^ r + ∑ i, p i • τ ^ (i : ℕ) = 0) : Algebra.leftMulMatrix bb τ = companion p := by
  classical
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul, hb, ← pow_succ']
  simp only [companion, Matrix.of_apply]
  by_cases hj : (j : ℕ) + 1 = r
  · rw [if_pos hj, hj, eq_neg_of_add_eq_zero_left hr]
    have : ∑ k, p k • τ ^ (k : ℕ) = ∑ k, p k • bb k := by simp [hb]
    rw [this, map_neg, Finsupp.neg_apply, bb.repr_sum_self]
  · rw [if_neg hj]
    have hlt : (j : ℕ) + 1 < r := by omega
    have : τ ^ ((j : ℕ) + 1) = bb ⟨(j : ℕ) + 1, hlt⟩ := by rw [hb]
    rw [this, bb.repr_self, Finsupp.single_apply]
    by_cases hi : (i : ℕ) = (j : ℕ) + 1
    · rw [if_pos (Fin.ext hi.symm), if_pos hi]
    · rw [if_neg (fun h => hi (by rw [← h])), if_neg hi]

theorem companion_pow_mulVec (bb : Module.Basis (Fin r) F K) (hb : ∀ i, bb i = τ ^ (i : ℕ))
    (hr : τ ^ r + ∑ i, p i • τ ^ (i : ℕ) = 0) (n : ℕ) :
    (companion p ^ n) *ᵥ (fun i : Fin r => if (i : ℕ) = 0 then (1 : F) else 0) = ⇑(bb.repr (τ ^ n)) := by
  classical
  induction n with
  | zero =>
    rw [pow_zero, Matrix.one_mulVec, pow_zero]
    funext i
    have hr0 : 0 < r := lt_of_le_of_lt (Nat.zero_le _) i.2
    have h1 : (1 : K) = bb ⟨0, hr0⟩ := by rw [hb]; simp
    rw [h1, bb.repr_self, Finsupp.single_apply]
    by_cases hi : (i : ℕ) = 0
    · rw [if_pos hi, if_pos (Fin.ext hi.symm)]
    · rw [if_neg hi, if_neg (fun h => hi (by rw [← h]))]
  | succ n ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, ← leftMulMatrix_eq_companion bb hb hr,
      Algebra.leftMulMatrix_apply, LinearMap.toMatrix_mulVec_repr, pow_succ']
    rfl

end Comp

theorem invK_regular_iff_isUnit :
    ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
      [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (lam : F), A.IsGen τ p →
      Function.Bijective (fun (a : A.K) (i : Fin r) => Algebra.trace F A.K (τ ^ (i : ℕ) * a)) ∧
      ∀ a : A.K, (∀ i : ℕ, mom (sec (A.invK τ p lam a)) i = Algebra.trace F A.K (τ ^ i * a)) ∧
        (Delta (A.invK τ p lam a) ≠ 0 ↔ IsUnit a) := by
  intro F E _ _ _ _ hU A r τ p lam hg
  classical
  haveI : CharZero F := hU.charZero
  obtain ⟨hli, hfr, hr⟩ := hg
  let bb : Module.Basis (Fin r) F A.K :=
    basisOfLinearIndependentOfCardEqFinrank' _ hli (by rw [hfr, Fintype.card_fin])
  have hb : ∀ i, bb i = τ ^ (i : ℕ) := fun i => by
    simp [bb]
  let Ψ : A.K →ₗ[F] (Fin r → F) :=
    { toFun := fun a i => Algebra.trace F A.K (τ ^ (i : ℕ) * a)
      map_add' := fun a a' => by funext i; simp [mul_add]
      map_smul' := fun c a => by funext i; simp [mul_smul_comm] }
  have hΨ : ∀ a, Ψ a = fun i : Fin r => Algebra.trace F A.K (τ ^ (i : ℕ) * a) := fun _ => rfl
  have hinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    apply eq_zero_of_trace_mul (F := F) a
    intro x
    rw [trace_mul_eq_sum bb hb x a]
    refine Finset.sum_eq_zero fun j _ => ?_
    have := congrFun ha j
    simp only [hΨ, Pi.zero_apply] at this
    rw [this, mul_zero]
  have hbij : Function.Bijective Ψ := by
    refine ⟨hinj, ?_⟩
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [hfr])).1 hinj
  have hmom : ∀ a : A.K, ∀ i : ℕ, mom (sec (A.invK τ p lam a)) i = Algebra.trace F A.K (τ ^ i * a) := by
    intro a i
    simp only [mom, sec, Et.invK]
    rw [companion_pow_mulVec bb hb hr i, trace_mul_eq_sum bb hb (τ ^ i) a, dotProduct]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  refine ⟨hbij, fun a => ⟨hmom a, ?_⟩⟩

  have hH : ∀ v : Fin r → F, hankel (A.invK τ p lam a) *ᵥ v = Ψ (a * bb.equivFun.symm v) := by
    intro v
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hankel, Matrix.mulVec, dotProduct, Matrix.of_apply, hmom, hΨ,
      Module.Basis.equivFun_symm_apply, hb, Finset.mul_sum, map_sum, mul_smul_comm, map_smul, smul_eq_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_add]; ring_nf
  have hcomp : Function.Injective (hankel (A.invK τ p lam a)).mulVec ↔ Function.Injective (fun y : A.K => a * y) := by
    constructor
    · intro h y y' hyy
      have := h (a₁ := bb.equivFun y) (a₂ := bb.equivFun y') (by rw [hH, hH]; simp [hyy])
      exact bb.equivFun.injective this
    · intro h v v' hvv
      rw [hH, hH] at hvv
      exact bb.equivFun.symm.injective (h (hinj hvv))
  rw [Delta, ← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit, hcomp]
  constructor
  · intro h
    have hs : Function.Surjective (Algebra.lmul F A.K a) :=
      LinearMap.injective_iff_surjective.1 h
    obtain ⟨y, hy⟩ := hs 1
    exact ⟨⟨a, y, hy, by rw [mul_comm]; exact hy⟩, rfl⟩
  · intro h
    exact h.mul_right_injective

end GlobalTheory.JR.EtInv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisInvKRegularIffIsUnitStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquetRallis_invK_regular_iff_isUnit : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (lam : F), A.IsGen τ p → Function.Bijective (fun (a : A.K) (i : Fin r) => Algebra.trace F A.K (τ ^ (i : ℕ) * a)) ∧ ∀ a : A.K, (∀ i : ℕ, mom (sec (A.invK τ p lam a)) i = Algebra.trace F A.K (τ ^ i * a)) ∧ (Delta (A.invK τ p lam a) ≠ 0 ↔ IsUnit a) := by
  first | exact @GlobalTheory.JR.EtInv.invK_regular_iff_isUnit | exact GlobalTheory.JR.EtInv.invK_regular_iff_isUnit | (intros; apply GlobalTheory.JR.EtInv.invK_regular_iff_isUnit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSelfDualMeasuresAndAbsKScale
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSelfDualMeasuresAndAbsKScale
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open scoped Pointwise NNReal ENNReal

noncomputable section

namespace GlobalTheory.JR.MeasScale

theorem fourB_nnreal_smul {V : Type} [MeasurableSpace V] (μ : Measure V) (c : ℝ≥0) (B : V → V → ℂ)
    (f : V → ℂ) (y : V) : fourB (c • μ) B f y = (c : ℂ) * fourB μ B f y := by
  simp only [fourB]
  rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

theorem fourB_const_mul {V : Type} [MeasurableSpace V] (μ : Measure V) (a : ℂ) (B : V → V → ℂ)
    (g : V → ℂ) (y : V) : fourB μ B (fun z => a * g z) y = a * fourB μ B g y := by
  simp only [fourB, mul_assoc]
  exact integral_const_mul a _

theorem fourB_twice_nnreal_smul {V : Type} [MeasurableSpace V] (μ : Measure V) (c : ℝ≥0) (B : V → V → ℂ)
    (f : V → ℂ) (y : V) :
    fourB (c • μ) B (fourB (c • μ) B f) y = (c : ℂ) ^ 2 * fourB μ B (fourB μ B f) y := by
  have h : fourB (c • μ) B f = fun z => (c : ℂ) * fourB μ B f z :=
    funext fun z => fourB_nnreal_smul μ c B f z
  rw [fourB_nnreal_smul, h, fourB_const_mul]
  ring

theorem exists_test_ne_zero {V : Type} [AddCommGroup V] [TopologicalSpace V] [T2Space V]
    (h : ∃ S : Set V, IsOpen S ∧ IsCompact S ∧ S.Nonempty) : ∃ f : V → ℂ, IsTest f ∧ ∃ y, f (-y) ≠ 0 := by
  obtain ⟨S, hSo, hSc, s, hs⟩ := h
  have hcl : IsClosed S := hSc.isClosed
  refine ⟨S.indicator fun _ => (1 : ℂ), ⟨?_, ?_⟩, -s, ?_⟩
  · intro t
    have := Set.indicator_const_preimage S t (1 : ℂ)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
    rcases this with h1 | h1 | h1 | h1 <;> rw [h1]
    · exact isOpen_univ
    · exact hSo
    · exact hcl.isOpen_compl
    · exact isOpen_empty
  · exact HasCompactSupport.intro hSc fun x hx => Set.indicator_of_notMem hx _
  · simp [hs]

theorem selfDual_unique {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [LocallyCompactSpace V] [T2Space V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    (hS : ∃ S : Set V, IsOpen S ∧ IsCompact S ∧ S.Nonempty) (B : V → V → ℂ) {μ μ' : Measure V}
    (h : SelfDual μ B) (h' : SelfDual μ' B) : μ' = μ := by
  obtain ⟨hμ, hF⟩ := h
  obtain ⟨hμ', hF'⟩ := h'
  have e := Measure.isAddLeftInvariant_eq_smul μ' μ
  obtain ⟨f, hf, y, hy⟩ := exists_test_ne_zero hS
  have h1 := hF' f hf y
  rw [e, fourB_twice_nnreal_smul, hF f hf y] at h1
  have hc : ((μ'.addHaarScalarFactor μ : ℝ≥0) : ℂ) ^ 2 = 1 :=
    mul_right_cancel₀ hy (h1.trans (one_mul _).symm)
  have hc2 : ((μ'.addHaarScalarFactor μ : ℝ≥0) : ℝ) ^ 2 = 1 := by exact_mod_cast hc
  have hc0 : (0 : ℝ) ≤ (μ'.addHaarScalarFactor μ : ℝ≥0) := NNReal.coe_nonneg _
  have hc1 : ((μ'.addHaarScalarFactor μ : ℝ≥0) : ℝ) = 1 := by nlinarith
  have hc3 : μ'.addHaarScalarFactor μ = 1 := by exact_mod_cast hc1
  rw [e, hc3, one_smul]

theorem integral_units_smul {L : Type} [CommRing L] [TopologicalSpace L] [IsTopologicalRing L]
    [LocallyCompactSpace L] [T2Space L] [SecondCountableTopology L] [MeasurableSpace L] [BorelSpace L]
    (μ : Measure L) [μ.IsAddHaarMeasure] (u : Lˣ) (G : L → ℂ) :
    ∫ y, G (u • y) ∂μ = ((distribHaarChar L u : ℝ≥0) : ℂ)⁻¹ * ∫ y, G y ∂μ := by
  let φ := Homeomorph.smul (α := L) u
  have hmap : μ.map (fun y => u • y) = (distribHaarChar L u⁻¹) • μ := by
    ext s hs
    rw [Measure.map_apply (continuous_const_smul u).measurable hs, Set.preimage_smul, Measure.smul_apply,
      ← distribHaarChar_mul μ u⁻¹ s]
    rfl
  have : ∫ y, G y ∂(μ.map fun y => u • y) = ∫ y, G (u • y) ∂μ :=
    φ.measurableEmbedding.integral_map (μ := μ) G
  rw [← this, hmap, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul, map_inv]
  push_cast
  rfl

end GlobalTheory.JR.MeasScale

namespace GlobalTheory.JR.MeasScale

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

def unitL (A : Et F E) (x : A.Kˣ) : A.Lˣ := Units.map (algebraMap A.K A.L : A.K →* A.L) x

theorem unitL_smul (A : Et F E) (x : A.Kˣ) (y : A.L) : unitL A x • y = algebraMap A.K A.L x * y := rfl

theorem kerL_eq (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (y' y : A.L) :
    A.kerL ψ x y' y = A.kerL ψ ((1 : A.Kˣ) : A.K) y' (unitL A x • y) := by
  simp only [Et.kerL, unitL_smul, Units.val_one, one_mul]
  congr 1
  have : star y' * (algebraMap A.K A.L x * y) = (x : A.K) • (star y' * y) := by
    rw [Algebra.smul_def]; ring
  rw [this, map_smul, smul_eq_mul]

theorem kerL_swap (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (y' y : A.L) :
    A.kerL ψ ((1 : A.Kˣ) : A.K) y' (unitL A x • y) = A.kerL ψ ((1 : A.Kˣ) : A.K) (unitL A x • y') y := by
  simp only [Et.kerL, unitL_smul]
  rw [star_mul', A.star_K]
  congr 3
  ring

theorem selfDual_scale [U : Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L)
    (h : SelfDual μ (A.kerL ψ ((1 : A.Kˣ) : A.K))) :
    SelfDual (distribHaarChar A.K x • μ) (A.kerL ψ x) := by
  have := U.charZero; have := U.ultraF; have := U.lcF
  have := EtMeas.finite_L A
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.L
  have : IsTopologicalRing A.L := IsModuleTopology.isTopologicalRing F A.L
  have hN : distribHaarChar A.L (unitL A x) = distribHaarChar A.K x ^ 2 := by
    obtain ⟨⟨b⟩, -, -, -, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
    obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.K
    have : ContinuousStar A.L := ⟨IsModuleTopology.continuous_of_linearMap (EtMeas.starF A)⟩
    rw [← map_pow]
    refine GlobalTheory.JR.ModuleNorm.distribHaarChar_eq_norm A.K A.L b.equivFun.symm
        (IsModuleTopology.continuous_of_linearMap (b.equivFun.symm.toLinearMap.restrictScalars F))
        (IsModuleTopology.continuous_of_linearMap (b.equivFun.toLinearMap.restrictScalars F)) _ _ ?_
    simp [unitL, A.star_K, pow_two]
  obtain ⟨hμ, hF⟩ := h
  have hc : distribHaarChar A.K x ≠ 0 := distribHaarChar_pos.ne'
  refine ⟨Measure.IsAddHaarMeasure.nnreal_smul _ hc, fun f hf y => ?_⟩
  set c := distribHaarChar A.K x with hcdef
  set B1 := A.kerL ψ ((1 : A.Kˣ) : A.K)
  have h1 : ∀ g z, fourB (c • μ) (A.kerL ψ x) g z = (c : ℂ) * fourB μ B1 g (unitL A x • z) := by
    intro g z
    rw [fourB_nnreal_smul]
    simp only [fourB, kerL_eq A ψ x, B1]
  have h2 : fourB (c • μ) (A.kerL ψ x) f = fun z => (c : ℂ) * fourB μ B1 f (unitL A x • z) :=
    funext (h1 f)
  rw [h1, h2]
  have h3 : fourB μ B1 (fun z => (c : ℂ) * fourB μ B1 f (unitL A x • z)) (unitL A x • y) =
      (c : ℂ) * ((distribHaarChar A.L (unitL A x) : ℝ≥0) : ℂ)⁻¹ * fourB μ B1 (fourB μ B1 f) y := by
    rw [fourB_const_mul, mul_assoc]
    congr 1
    have e := integral_units_smul μ (unitL A x) (fun z => fourB μ B1 f z * B1 z y)
    refine Eq.trans ?_ e
    show ∫ y', fourB μ B1 f (unitL A x • y') * B1 y' (unitL A x • y) ∂μ = _
    refine integral_congr_ae (Eventually.of_forall fun y' => ?_)
    exact congrArg _ (kerL_swap A ψ x y' y)
  rw [h3, hF f hf y, hN]
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  push_cast
  field_simp

theorem meas_scale [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (m : A.Meas ψ) (x : A.Kˣ) :
    m.μL x = ENNReal.ofReal (A.absK x) • m.μL 1 := by
  have := (inferInstance : Unram F E).charZero
  have hu := ‹Unram F E›.ultraF; have := ‹Unram F E›.lcF
  have := EtMeas.finite_L A
  obtain ⟨_, _, _, _, hS⟩ := EtMeas.top_facts F A.L
  rw [EtMeas.absK_unit, ENNReal.ofReal_coe_nnreal]
  exact selfDual_unique hS _ (selfDual_scale A ψ x (m.μL 1) (m.sdL 1)) (m.sdL x)

end GlobalTheory.JR.MeasScale

theorem GlobalTheory.JR.exists_meas_and_scale : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ →
    Nonempty (A.Meas ψ) ∧ ∀ (m : A.Meas ψ) (x : A.Kˣ), m.μL x = ENNReal.ofReal (A.absK x) • m.μL 1 := by
  intro F E _ _ _ _ _ A ψ hψ
  exact ⟨(EtMeas.nonempty_meas_and_reps F E A ψ hψ).1, GlobalTheory.JR.MeasScale.meas_scale A ψ⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSelfDualMeasuresAndAbsKScaleStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_selfDual_measures_and_absK_scale : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → Nonempty (A.Meas ψ) ∧ ∀ (m : A.Meas ψ) (x : A.Kˣ), m.μL x = ENNReal.ofReal (A.absK x) • m.μL 1 := by
  first | exact @GlobalTheory.JR.exists_meas_and_scale | exact GlobalTheory.JR.exists_meas_and_scale | (intros; apply GlobalTheory.JR.exists_meas_and_scale <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelativeJacquetPiExteriorTensorEquivNormalized
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelativeJacquetPiExteriorTensorEquivNormalized
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.JacStages

noncomputable section

namespace GlobalTheory.JacPiTensor

section Gen

variable {ι : Type} [Fintype ι] [dec0 : DecidableEq ι] {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
  {N : Type} [AddCommGroup N] [Module ℂ N] (p : ∀ i, Submodule ℂ (M i))

def qlift (i : ι) (q : M i ⧸ p i) : M i := (Submodule.Quotient.mk_surjective (p i) q).choose

theorem mk_qlift (i : ι) (q : M i ⧸ p i) : Submodule.Quotient.mk (qlift p i q) = q :=
  (Submodule.Quotient.mk_surjective (p i) q).choose_spec

variable {p}

theorem position_eq (f : (∀ i, M i) →ₘₗ[ℂ] N) (hf : ∀ v i, ∀ w ∈ p i, f (Function.update v i w) = 0)
    (v : ∀ i, M i) (i : ι) {u u' : M i} (h : u - u' ∈ p i) :
    f (Function.update v i u) = f (Function.update v i u') := by
  rw [← sub_eq_zero, ← f.map_update_sub]
  exact hf v i _ h

def descend (f : (∀ i, M i) →ₘₗ[ℂ] N) (hf : ∀ v i, ∀ w ∈ p i, f (Function.update v i w) = 0) :
    (∀ i, M i ⧸ p i) →ₘₗ[ℂ] N where
  toFun q := f fun i => qlift p i (q i)
  map_update_add' {dec} q i a b := by
    obtain rfl : dec = dec0 := Subsingleton.elim _ _
    have e : ∀ c : M i ⧸ p i, (fun j => qlift p j (Function.update q i c j)) =
        Function.update (fun j => qlift p j (q j)) i (qlift p i c) := fun c =>
      funext fun j => Function.apply_update (fun j => qlift p j) q i c j
    simp only [e]
    rw [position_eq f hf _ i (u' := qlift p i a + qlift p i b), f.map_update_add]
    rw [← Submodule.Quotient.eq, Submodule.Quotient.mk_add, mk_qlift, mk_qlift, mk_qlift]
  map_update_smul' {dec} q i c a := by
    obtain rfl : dec = dec0 := Subsingleton.elim _ _
    have e : ∀ c : M i ⧸ p i, (fun j => qlift p j (Function.update q i c j)) =
        Function.update (fun j => qlift p j (q j)) i (qlift p i c) := fun c =>
      funext fun j => Function.apply_update (fun j => qlift p j) q i c j
    simp only [e]
    rw [position_eq f hf _ i (u' := c • qlift p i a), f.map_update_smul]
    rw [← Submodule.Quotient.eq, Submodule.Quotient.mk_smul, mk_qlift, mk_qlift]

theorem descend_mk (f : (∀ i, M i) →ₘₗ[ℂ] N) (hf : ∀ v i, ∀ w ∈ p i, f (Function.update v i w) = 0)
    (x : ∀ i, M i) : descend f hf (fun i => Submodule.Quotient.mk (x i)) = f x := by
  show f (fun i => qlift p i (Submodule.Quotient.mk (x i))) = f x
  have key : ∀ s : Finset ι,
      f (fun i => if i ∈ s then qlift p i (Submodule.Quotient.mk (x i)) else x i) = f x := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [← ih]
      set F : ∀ i, M i := fun i => if i ∈ s then qlift p i (Submodule.Quotient.mk (x i)) else x i
      have h1 : (fun i => if i ∈ insert a s then qlift p i (Submodule.Quotient.mk (x i)) else x i) =
          Function.update F a (qlift p a (Submodule.Quotient.mk (x a))) := by
        funext i
        by_cases hi : i = a
        · subst hi; simp
        · simp [Function.update_of_ne hi, F, Finset.mem_insert, hi]
      have h2 : F = Function.update F a (x a) := by
        funext i
        by_cases hi : i = a
        · subst hi; simp [F, ha]
        · simp [Function.update_of_ne hi]
      rw [h1]
      conv_rhs => rw [h2]
      refine position_eq f hf F a ?_
      rw [← Submodule.Quotient.eq, mk_qlift]
  simpa using key Finset.univ

end Gen

end GlobalTheory.JacPiTensor

noncomputable section

namespace GlobalTheory.JacPiTensor

open scoped TensorProduct

section Spec

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {s : ℕ} {d : Fin s → ℕ} {t : Fin s → ℕ} {d' : ∀ a, Fin (t a) → ℕ}
  (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a)) {X : Fin s → Type} [∀ a, AddCommGroup (X a)]
  [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a))

theorem piTensor_mulSingle (a : Fin s) (g : GL (Fin (d a)) k) (x : ∀ j, X j) :
    piTensor ρ (Pi.mulSingle a g) (PiTensorProduct.tprod ℂ x) =
      PiTensorProduct.tprod ℂ (Function.update x a (ρ a g (x a))) := by
  rw [piTensor_tprod]
  congr 1
  funext j
  by_cases h : j = a
  · subst h; simp
  · simp [Pi.mulSingle_eq_of_ne h, Function.update_of_ne h]

def qf : (∀ a, X a) →ₘₗ[ℂ] Jacquet (piTensor ρ) (relUnipD k e') :=
  (twKer (piTensor ρ) (relUnipD k e') 1).mkQ.compMultilinearMap (PiTensorProduct.tprod ℂ)

theorem qf_update (v : ∀ a, X a) (i : Fin s) (w : X i)
    (hw : w ∈ twKer (ρ i) (unipRad k (e' i)) 1) : qf e' ρ (Function.update v i w) = 0 := by
  have hle : twKer (ρ i) (unipRad k (e' i)) 1 ≤
      (twKer (piTensor ρ) (relUnipD k e') 1).comap ((PiTensorProduct.tprod ℂ).toLinearMap v i) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨n, y, rfl⟩
    have hmem : (Pi.mulSingle i (n : GL (Fin (d i)) k) : ∀ a, GL (Fin (d a)) k) ∈ relUnipD k e' := by
      refine (Subgroup.mem_pi _).2 fun j _ => ?_
      by_cases h : j = i
      · subst h; simpa using n.2
      · rw [Pi.mulSingle_eq_of_ne h]; exact one_mem _
    simp only [SetLike.mem_coe, Submodule.mem_comap, MultilinearMap.toLinearMap_apply,
      MonoidHom.one_apply, Units.val_one, one_smul, MultilinearMap.map_update_sub]
    refine Submodule.subset_span ⟨⟨_, hmem⟩, PiTensorProduct.tprod ℂ (Function.update v i y), ?_⟩
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    rw [piTensor_mulSingle]
    simp
  have := hle hw
  simp only [Submodule.mem_comap, MultilinearMap.toLinearMap_apply] at this
  simp [qf, (Submodule.Quotient.mk_eq_zero _).2 this]

end Spec

end GlobalTheory.JacPiTensor

noncomputable section

namespace GlobalTheory.JacPiTensor

open scoped TensorProduct

section Spec2

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {s : ℕ} {d : Fin s → ℕ} {t : Fin s → ℕ} {d' : ∀ a, Fin (t a) → ℕ}
  (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a)) {X : Fin s → Type} [∀ a, AddCommGroup (X a)]
  [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a))

def qmap : (⨂[ℂ] a, X a) →ₗ[ℂ] ⨂[ℂ] a, Jacquet (ρ a) (unipRad k (e' a)) :=
  PiTensorProduct.map fun a => (twKer (ρ a) (unipRad k (e' a)) 1).mkQ

theorem qmap_tprod (x : ∀ a, X a) :
    qmap e' ρ (PiTensorProduct.tprod ℂ x) =
      PiTensorProduct.tprod ℂ fun a => (Submodule.Quotient.mk (x a) : Jacquet (ρ a) (unipRad k (e' a))) := by
  simp [qmap, PiTensorProduct.map_tprod]

theorem qmap_comp (u : ∀ a, GL (Fin (d a)) k) (hu : u ∈ relUnipD k e') :
    qmap e' ρ ∘ₗ piTensor ρ u = qmap e' ρ := by
  refine PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, piTensor_tprod, qmap_tprod]
  congr 1
  funext a
  refine (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨⟨u a, (Subgroup.mem_pi _).1 hu a trivial⟩, x a, ?_⟩)
  simp

theorem twKer_le_ker : twKer (piTensor ρ) (relUnipD k e') 1 ≤ LinearMap.ker (qmap e' ρ) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨u, z, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, MonoidHom.one_apply, Units.val_one, one_smul, map_sub]
  rw [← LinearMap.comp_apply, qmap_comp e' ρ u u.2, sub_self]

def fwd : Jacquet (piTensor ρ) (relUnipD k e') →ₗ[ℂ] ⨂[ℂ] a, Jacquet (ρ a) (unipRad k (e' a)) :=
  (twKer (piTensor ρ) (relUnipD k e') 1).liftQ (qmap e' ρ) (twKer_le_ker e' ρ)

def bwd : (⨂[ℂ] a, Jacquet (ρ a) (unipRad k (e' a))) →ₗ[ℂ] Jacquet (piTensor ρ) (relUnipD k e') :=
  PiTensorProduct.lift (descend (qf e' ρ) (qf_update e' ρ))

theorem bwd_tprod (q : ∀ a, Jacquet (ρ a) (unipRad k (e' a))) :
    bwd e' ρ (PiTensorProduct.tprod ℂ q) = Submodule.Quotient.mk (PiTensorProduct.tprod ℂ
      fun i => qlift (fun a => twKer (ρ a) (unipRad k (e' a)) 1) i (q i)) := by
  rw [bwd, PiTensorProduct.lift.tprod]
  rfl

theorem bwd_tprod_mk (x : ∀ a, X a) :
    bwd e' ρ (PiTensorProduct.tprod ℂ fun a => (Submodule.Quotient.mk (x a) : Jacquet (ρ a) (unipRad k (e' a)))) =
      Submodule.Quotient.mk (PiTensorProduct.tprod ℂ x) := by
  rw [bwd, PiTensorProduct.lift.tprod, descend_mk]
  rfl

theorem fwd_mk_tprod' (x : ∀ a, X a) :
    fwd e' ρ (Submodule.Quotient.mk (PiTensorProduct.tprod ℂ x)) =
      PiTensorProduct.tprod ℂ fun a => (Submodule.Quotient.mk (x a) : Jacquet (ρ a) (unipRad k (e' a))) := by
  simp only [fwd, Submodule.liftQ_apply, qmap_tprod]

def jacEquiv : Jacquet (piTensor ρ) (relUnipD k e') ≃ₗ[ℂ] ⨂[ℂ] a, Jacquet (ρ a) (unipRad k (e' a)) :=
  LinearEquiv.ofLinear (fwd e' ρ) (bwd e' ρ)
    (by
      refine PiTensorProduct.ext (MultilinearMap.ext fun q => ?_)
      rw [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, bwd_tprod, fwd_mk_tprod']
      simp only [mk_qlift, LinearMap.compMultilinearMap_apply, LinearMap.id_apply])
    (by
      refine Submodule.linearMap_qext _ (PiTensorProduct.ext (MultilinearMap.ext fun x => ?_))
      rw [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearMap.comp_apply, Submodule.mkQ_apply,
        fwd_mk_tprod', bwd_tprod_mk, LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearMap.id_apply,
        Submodule.mkQ_apply])

theorem relJacD_piTensor :
    Nonempty ((relJacD e' (piTensor ρ)).Equiv (piTensor fun a => jac (e' a) (ρ a))) := by
  refine ⟨Representation.Equiv.mk (jacEquiv e' ρ) fun g => ?_⟩
  refine Submodule.linearMap_qext _ (PiTensorProduct.ext (MultilinearMap.ext fun x => ?_))
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, Submodule.mkQ_apply]
  rw [relJacD_mk]
  show fwd e' ρ _ = piTensor (fun a => jac (e' a) (ρ a)) g (fwd e' ρ _)
  rw [map_smul, piTensor_tprod, fwd_mk_tprod', fwd_mk_tprod', piTensor_tprod]
  simp only [jac_mk, relEmbD_apply]
  rw [MultilinearMap.map_smul_univ, relDeltaHalfD_apply]
  congr 1
  simp [Units.coe_prod, Finset.prod_inv_distrib]

end Spec2

end GlobalTheory.JacPiTensor

namespace GlobalTheory.JacStages

theorem relJacD_piTensor_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s : ℕ) (d : Fin s → ℕ) (t : Fin s → ℕ) (d' : ∀ a, Fin (t a) → ℕ)
    (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a)) (X : Fin s → Type) [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)),
    Nonempty ((relJacD e' (piTensor ρ)).Equiv (piTensor fun a => jac (e' a) (ρ a))) :=
  fun _ _ _ _ _ _ _ _ _ e' _ _ _ ρ => GlobalTheory.JacPiTensor.relJacD_piTensor e' ρ

end GlobalTheory.JacStages
end
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelativeJacquetPiExteriorTensorEquivNormalizedStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.JacStages
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relativeJacquet_piExteriorTensor_equiv_normalized : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s : ℕ) (d : Fin s → ℕ) (t : Fin s → ℕ) (d' : ∀ a, Fin (t a) → ℕ)
    (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a)) (X : Fin s → Type) [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)),
    Nonempty ((relJacD e' (piTensor ρ)).Equiv (piTensor fun a => jac (e' a) (ρ a))) := by
  first | exact @GlobalTheory.JacStages.relJacD_piTensor_equiv | exact GlobalTheory.JacStages.relJacD_piTensor_equiv | (intros; apply GlobalTheory.JacStages.relJacD_piTensor_equiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuadraticWeilUnipotentTorusPreserveTest
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuadraticWeilUnipotentTorusPreserveTest
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.WeilQuad

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem isLocallyConstant_of_stdChar {ψ : AddChar F ℂ} (hψ : IsStdChar ψ) : IsLocallyConstant ψ := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro a
  filter_upwards [Metric.closedBall_mem_nhds a one_pos] with b hb
  have h1 : ψ (b - a) = 1 := hψ.1 _ (by simpa [Metric.mem_closedBall, dist_eq_norm] using hb)
  calc ψ b = ψ (a + (b - a)) := by rw [add_sub_cancel]
    _ = ψ a := by rw [AddChar.map_add_eq_mul, h1, mul_one]

theorem continuous_mulLeft (A : Et F E) (c : A.L) : Continuous fun y : A.L => c * y := by
  haveI : ContinuousAdd A.L := IsModuleTopology.toContinuousAdd F A.L
  exact IsModuleTopology.continuous_of_linearMap (LinearMap.mulLeft F c)

def smulHomeo (A : Et F E) (s : A.Kˣ) : A.L ≃ₜ A.L where
  toFun y := (s : A.K) • y
  invFun y := ((s⁻¹ : A.Kˣ) : A.K) • y
  left_inv y := by simp [smul_smul]
  right_inv y := by simp [smul_smul]
  continuous_toFun := by
    simp only [Algebra.smul_def]; exact continuous_mulLeft A _
  continuous_invFun := by
    simp only [Algebra.smul_def]; exact continuous_mulLeft A _

theorem isTest_nOp [Unram F E] (A : Et F E) {ψ : AddChar F ℂ} (hψ : IsStdChar ψ) (x z : A.K) {φ : A.L → ℂ}
    (hφ : IsTest φ) : IsTest (nOp A ψ x z φ) := by
  have htr : Continuous (Algebra.trace F A.K) := IsModuleTopology.continuous_of_linearMap _
  have hc : Continuous fun y : A.L => Algebra.trace F A.K (z * x * A.NL y) :=
    htr.comp (continuous_const.mul (GlobalTheory.JR.EtMeas.continuous_NL A))
  have hl : IsLocallyConstant fun y : A.L => A.psiK ψ (z * x * A.NL y) :=
    (isLocallyConstant_of_stdChar hψ).comp_continuous hc
  exact ⟨hl.mul hφ.1, hφ.2.mul_left⟩

theorem isTest_mOp (A : Et F E) (ω : A.K → ℂ) (s : A.Kˣ) {φ : A.L → ℂ} (hφ : IsTest φ) :
    IsTest (mOp A ω s φ) := by
  have h1 : IsTest (φ ∘ smulHomeo A s) :=
    ⟨hφ.1.comp_continuous (smulHomeo A s).continuous, hφ.2.comp_homeomorph _⟩
  exact ⟨(IsLocallyConstant.const (ω s * (A.absK s : ℂ))).mul h1.1, h1.2.mul_left⟩

theorem isTest_nOp_mOp : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ),
    Hyp A ψ x μ ω → ∀ φ : A.L → ℂ, IsTest φ → (∀ z, IsTest (nOp A ψ x z φ)) ∧ ∀ s, IsTest (mOp A ω s φ) := by
  intro F E _ _ _ _ _ A ψ x μ ω h φ hφ
  exact ⟨fun z => isTest_nOp A h.2.2.1 x z hφ, fun s => isTest_mOp A ω s hφ⟩

end GlobalTheory.JR.WeilQuad
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuadraticWeilUnipotentTorusPreserveTestStatement
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadraticWeil_unipotent_torus_preserve_test : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ φ : A.L → ℂ, IsTest φ → (∀ z, IsTest (nOp A ψ x z φ)) ∧ ∀ s, IsTest (mOp A ω s φ) := by
  first | exact @GlobalTheory.JR.WeilQuad.isTest_nOp_mOp | exact GlobalTheory.JR.WeilQuad.isTest_nOp_mOp | (intros; apply GlobalTheory.JR.WeilQuad.isTest_nOp_mOp <;> assumption)
end
end
