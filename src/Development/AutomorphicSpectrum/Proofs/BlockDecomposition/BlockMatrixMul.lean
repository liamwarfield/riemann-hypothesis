module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.HeisSch
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.EisensteinGrowthForms.LocFinType
public import Development.WeilBound.ThetaLifts.LatticeBasics.EisCont
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CtGrowth
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteGeneralizedEigenspaceCofiniteDecomposition
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactOpenExhaustionStabilizes
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalOfL2CuspidalMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShiftedCapelliDeterminantSubleadingCoeffTrace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedWhittakerNewform

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockMatrixMul
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisCovar

def CovAt {D : D7} {n : ℕ} (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) {θ : InfFam D}
    (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) (γ : G D n) : Prop :=
  ∀ (v : Mx D V.rank (n + n)) (Φ Ψ : schwartzA θ V.rank n), Ψ.1 = EC.Heisenberg₂ ψ V v Φ.1 →
    (ω γ Ψ).1 = EC.Heisenberg₂ ψ V (HMul.hMul v (mat γ⁻¹)) (ω γ Φ).1

def FieldGen (K : Type) [Field K] (σ : K →+* K) (n : ℕ) : Prop :=
  ∀ T : Matrix (Fin (n + n)) (Fin (n + n)) K → Prop, (∀ g h, T g → T h → T (g * h)) →
    (∀ a : Matrix (Fin n) (Fin n) K, IsUnit a.det → T (mA σ a)) →
    (∀ b : Matrix (Fin n) (Fin n) K, cT σ b = b → T (nB b)) → T (Jm K n) →
    ∀ g, IsUnit g.det → IsUnitary σ (Jm K n) g → T g

variable {D : D7} {n : ℕ}

theorem mat_mul' (g h : G D n) : mat (g * h) = mat g * mat h := by
  unfold mat; rw [map_mul]; rfl

theorem mat_one' : mat (1 : G D n) = 1 := by
  unfold mat; rw [map_one]; rfl

theorem mat_inv_mul' (g : G D n) : mat g⁻¹ * mat g = 1 := by
  rw [← mat_mul', inv_mul_cancel, mat_one']

theorem mat_mul_inv' (g : G D n) : mat g * mat g⁻¹ = 1 := by
  rw [← mat_mul', mul_inv_cancel, mat_one']

theorem mat_injective' : Function.Injective (mat : G D n → Mx D (n + n) (n + n)) :=
  fun _ _ e => Subtype.ext (Units.ext e)

theorem x_part_mul_block {m : ℕ} (v : Mx D m (n + n)) (A B C E : Mx D n n) :
    xPart (HMul.hMul v (blk4 A B C E) : Mx D m (n + n)) = HMul.hMul (xPart v) A + HMul.hMul (yPart v) C := by
  funext i j
  simp only [xPart, yPart, blk4, Matrix.of_apply, Matrix.mul_apply, Matrix.add_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply]
  rw [← finSumFinEquiv.sum_comp]
  simp [Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁]

theorem y_part_mul_block {m : ℕ} (v : Mx D m (n + n)) (A B C E : Mx D n n) :
    yPart (HMul.hMul v (blk4 A B C E) : Mx D m (n + n)) = HMul.hMul (xPart v) B + HMul.hMul (yPart v) E := by
  funext i j
  simp only [xPart, yPart, blk4, Matrix.of_apply, Matrix.mul_apply, Matrix.add_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply]
  rw [← finSumFinEquiv.sum_comp]
  simp [Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂]

theorem submatrix_fromBlocks_mul {R : Type} [CommRing R] (A B C E A' B' C' E' : Matrix (Fin n) (Fin n) R) :
    blk4 A B C E * blk4 A' B' C' E' = blk4 (A * A' + B * C') (A * B' + B * E') (C * A' + E * C') (C * B' + E * E') := by
  simp only [blk4]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem block_matrix_one {R : Type} [CommRing R] : blk4 (1 : Matrix (Fin n) (Fin n) R) 0 0 1 = 1 := by
  simp only [blk4, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem covAt_mul {ψ : AddChar (AF D.host.F) ℂ} {V : HSp D} {θ : InfFam D}
    {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} {γ₁ γ₂ : G D n}
    (h₁ : CovAt ψ V ω γ₁) (h₂ : CovAt ψ V ω γ₂) : CovAt ψ V ω (γ₁ * γ₂) := by
  intro v Φ Ψ hΨ
  have e1 := h₁ _ (ω γ₂ Φ) (ω γ₂ Ψ) (h₂ v Φ Ψ hΨ)
  rw [map_mul, Module.End.mul_apply, Module.End.mul_apply, e1, mul_inv_rev, mat_mul', Matrix.mul_assoc]

end GlobalTheory.CompanionTheory.EisCovar
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwoSegmentNongenericQuotient
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.CompanionTheory.BZSeg.TwoSeg

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem range_le_comap (π : Representation ℂ (GL (Fin N) k) V) (σ : Representation ℂ (GL (Fin N) k) W)
    (f : σ.IntertwiningMap π) (g : GL (Fin N) k) :
    LinearMap.range f.toLinearMap ≤ (LinearMap.range f.toLinearMap).comap (π g) := by
  rintro _ ⟨w, rfl⟩
  exact ⟨σ g w, Representation.IntertwiningMap.isIntertwining _ _ f g w⟩

def quotRep (π : Representation ℂ (GL (Fin N) k) V) (σ : Representation ℂ (GL (Fin N) k) W)
    (f : σ.IntertwiningMap π) : Representation ℂ (GL (Fin N) k) (V ⧸ LinearMap.range f.toLinearMap) where
  toFun g := (LinearMap.range f.toLinearMap).mapQ _ (π g) (range_le_comap π σ f g)
  map_one' := by ext v; simp
  map_mul' a b := by ext v; simp

theorem mkQ_mem_twKer (π : Representation ℂ (GL (Fin N) k) V) (σ : Representation ℂ (GL (Fin N) k) W)
    (f : σ.IntertwiningMap π) (U : Subgroup (GL (Fin N) k)) (θ : U →* ℂˣ) {v : V} (hv : v ∈ twKer π U θ) :
    (LinearMap.range f.toLinearMap).mkQ v ∈ twKer (quotRep π σ f) U θ := by
  have hle : twKer π U θ ≤ (twKer (quotRep π σ f) U θ).comap (LinearMap.range f.toLinearMap).mkQ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨n, u, rfl⟩
    refine Submodule.subset_span ⟨n, (LinearMap.range f.toLinearMap).mkQ u, ?_⟩
    simp only [LinearMap.map_sub, LinearMap.map_smul]
    rfl
  exact hle hv

theorem isSmooth_of_injective (π : Representation ℂ (GL (Fin N) k) V) (σ : Representation ℂ (GL (Fin N) k) W)
    (f : σ.IntertwiningMap π) (hf : Function.Injective f) (hπ : IsSmooth π) : IsSmooth σ := by
  intro w
  have : {g : GL (Fin N) k | σ g w = w} = {g | π g (f w) = f w} := by
    ext g
    simp only [Set.mem_setOf_eq]
    rw [← Representation.IntertwiningMap.isIntertwining _ _ f g w, hf.eq_iff]
  rw [this]
  exact hπ _

theorem not_isGeneric_quotRep {ψ : AddChar k Circle} (hψ : Continuous ψ) (h1 : ψ ≠ 1)
    (π : Representation ℂ (GL (Fin N) k) V) (σ : Representation ℂ (GL (Fin N) k) W)
    (f : σ.IntertwiningMap π) (hf : Function.Injective f) (hπ : IsSmooth π)
    (hr : Module.rank ℂ (TwJacquet π (unipB k (Fin N)) (whitChar ψ N)) ≤ 1) (hσ : IsGeneric σ) :
    ¬ IsGeneric (quotRep π σ f) := by
  rw [isGeneric_iff_isGenericFor hψ h1] at hσ ⊢
  have hσs := isSmooth_of_injective π σ f hf hπ
  unfold IsGenericFor at hσ ⊢
  rw [not_nontrivial_iff_subsingleton]

  obtain ⟨q, hq⟩ := exists_ne (0 : TwJacquet σ (unipB k (Fin N)) (whitChar ψ N))
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have hw : w ∉ twKer σ (unipB k (Fin N)) (whitChar ψ N) := fun h => hq ((Submodule.Quotient.mk_eq_zero _).2 h)
  have hfw : f w ∉ twKer π (unipB k (Fin N)) (whitChar ψ N) := fun h =>
    hw (GlobalTheory.CompanionTheory.PRep.WhitExact.twKer_whitChar_reflect k ψ hψ N σ π hσs hπ f.toLinearMap hf
      (fun g v => Representation.IntertwiningMap.isIntertwining _ _ f g v) w h)
  obtain ⟨e, he⟩ := rank_le_one_iff.1 hr
  refine subsingleton_of_forall_eq 0 fun t => ?_
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ t
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ t
  refine (Submodule.Quotient.mk_eq_zero _).2 ?_
  obtain ⟨a, ha⟩ := he (Submodule.Quotient.mk (f w))
  obtain ⟨b, hb⟩ := he (Submodule.Quotient.mk v)
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hfw ((Submodule.Quotient.mk_eq_zero _).1 (by rw [← ha, zero_smul]))
  have hk : v - (b / a) • f w ∈ twKer π (unipB k (Fin N)) (whitChar ψ N) := by
    refine (Submodule.Quotient.mk_eq_zero _).1 ?_
    rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul, ← ha, ← hb, smul_smul,
      div_mul_cancel₀ _ ha0, sub_self]
  have h2 := mkQ_mem_twKer π σ f _ _ hk
  have h3 : (LinearMap.range f.toLinearMap).mkQ (f w) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).2 ⟨w, rfl⟩
  rw [map_sub, map_smul, h3, smul_zero, sub_zero] at h2
  exact h2

end GlobalTheory.CompanionTheory.BZSeg.TwoSeg

namespace GlobalTheory.CompanionTheory.BZSeg

open GlobalTheory.CompanionTheory.BZSeg.TwoSeg


end GlobalTheory.CompanionTheory.BZSeg
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasimirMemCenterEnveloping
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasimirMemCenterEnveloping
set_option maxSynthPendingDepth 1
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.Inh.CapelliCasimir
open Finset

theorem mem_subalgebra_of_dual {A : Type} [Ring A] [Algebra ℂ A] (S : Subalgebra ℂ A) (x : A)
    (h : ∀ f : A →ₗ[ℂ] ℂ, (∀ z ∈ S, f z = 0) → f x = 0) : x ∈ S := by
  by_contra hx
  have hx' : x ∉ Subalgebra.toSubmodule S := hx
  obtain ⟨f, hf1, hf2⟩ := Submodule.exists_le_ker_of_notMem hx'
  exact hf1 (h f fun z hz => LinearMap.mem_ker.1 (hf2 hz))

theorem cas_mem_of_qdet_mem {A : Type} [Ring A] [Algebra ℂ A] (S : Subalgebra ℂ A) (n : ℕ)
    (E : Fin n → Fin n → A) (hE : Formalism.REAL.GlRel E)
    (hcap : ∀ Y : ℂ, Formalism.REAL.qdet E (Y + ((n : ℂ) - 1) / 2) ∈ S) : Formalism.REAL.Cas E ∈ S := by
  obtain ⟨Rm, hR⟩ := _root_.GlobalTheory.qdet_top_three_orders A n E
  by_cases hn : 2 ≤ n
  swap
  · have hn' : n = 0 ∨ n = 1 := by omega
    rcases hn' with rfl | rfl
    · simp [Formalism.REAL.Cas]
    · have h0 := hcap 0
      rw [hR] at h0
      have h1 : E 0 0 ∈ S := by
        simpa [Finset.filter_singleton] using h0
      have : Formalism.REAL.Cas E = E 0 0 * E 0 0 := by simp [Formalism.REAL.Cas]
      rw [this]
      exact Subalgebra.mul_mem _ h1 h1
  set ρ : Fin n → ℂ := fun l => ((n : ℂ) - 1) / 2 - ((l : ℕ) : ℂ) with hρ
  have hρ0 : ∑ l, ρ l = 0 := by
    have h1 : ∑ l, ρ l = ∑ l, ρ (Fin.rev l) := (Equiv.sum_comp Fin.revPerm ρ).symm
    have h2 : ∑ l, ρ (Fin.rev l) = - ∑ l, ρ l := by
      rw [← sum_neg_distrib]
      refine sum_congr rfl fun l _ => ?_
      have := l.2
      simp only [hρ, Fin.val_rev]
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    linear_combination (h1.trans h2) / 2
  have core := fun (f : A →ₗ[ℂ] ℂ) (hf : ∀ z ∈ S, f z = 0) =>
    scalar_core n hn ρ (fun _ => 0) (fun i => f (E i i))
      (fun i j => f (E i i * E j j - E j i * E i j)) (fun d => f (Rm d)) (f 1)
      (((n : ℂ) - 1) / 2)
      (fun Y => by
        have h1 := hf _ (hcap Y)
        rw [hR] at h1
        have e : f 1 = 0 := hf 1 (Subalgebra.one_mem _)
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_add (f := _), map_sum, map_smul, smul_eq_mul, add_sub_assoc] at h1
        simp only [e, mul_zero] at h1 ⊢
        exact h1)
  have hT : ∑ i, E i i ∈ S := by
    refine mem_subalgebra_of_dual S _ fun f hf => ?_
    have e : f 1 = 0 := hf 1 (Subalgebra.one_mem _)
    have := (core f hf).1
    rw [hρ0, e] at this
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum]
    linear_combination this
  have hW : (2 : ℂ) • ∑ i, ∑ j ∈ univ.filter (fun j => i < j), (E i i * E j j - E j i * E i j)
        - ∑ i : Fin n, ((n : ℂ) - 1 - 2 * (i : ℕ)) • E i i ∈ S := by
    refine mem_subalgebra_of_dual S _ fun f hf => ?_
    have e : f 1 = 0 := hf 1 (Subalgebra.one_mem _)
    have h2 := (core f hf).2
    rw [e] at h2
    simp only [sum_erase_eq_sub (mem_univ _), hρ0] at h2
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sub f, map_sum, map_smul, smul_eq_mul]
    have h5 : ∑ i : Fin n, ((n : ℂ) - 1 - 2 * (i : ℕ)) * f (E i i)
        = - (2 * ∑ i, (0 - ρ i) * f (E i i)) := by
      rw [mul_sum, ← sum_neg_distrib]
      refine sum_congr rfl fun i _ => ?_
      simp only [hρ]; ring
    rw [h5]
    simp only [map_sub f] at h2
    linear_combination h2
  have h3 := sq_sub_cas E hE
  have : Formalism.REAL.Cas E = (∑ i, E i i) * (∑ i, E i i)
      - ((2 : ℂ) • ∑ i, ∑ j ∈ univ.filter (fun j => i < j), (E i i * E j j - E j i * E i j)
        - ∑ i : Fin n, ((n : ℂ) - 1 - 2 * (i : ℕ)) • E i i) := by
    rw [← h3]; abel
  rw [this]
  exact Subalgebra.sub_mem _ (Subalgebra.mul_mem _ hT hT) hW

theorem cas_mem_Zalg : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (τ : E →+* ℂ),
    Formalism.REAL.Cas (Eop (a := a) τ) ∈ Zalg E a := by
  intro F _ _ _ n τ
  have hcap : ∀ Y : ℂ, cap (a := n) τ Y ∈ Zalg F n := fun Y =>
    Algebra.subset_adjoin (show cap (a := n) τ Y ∈ {z | ∃ τ u, z = cap τ u} from ⟨τ, Y, rfl⟩)
  exact cas_mem_of_qdet_mem (Zalg F n) n (Eop τ) (glRel_Eop τ) hcap

end GlobalTheory.CompanionTheory.Inh.CapelliCasimir
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasimirMemCenterEnvelopingStatement
set_option maxSynthPendingDepth 1
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.casimir_mem_center_enveloping : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (τ : E →+* ℂ),
    Formalism.REAL.Cas (Eop (a := a) τ) ∈ Zalg E a := by
  first | exact @GlobalTheory.CompanionTheory.Inh.CapelliCasimir.cas_mem_Zalg | exact GlobalTheory.CompanionTheory.Inh.CapelliCasimir.cas_mem_Zalg | (intros; apply GlobalTheory.CompanionTheory.Inh.CapelliCasimir.cas_mem_Zalg <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousDerivFamily
noncomputable section

namespace GlobalTheory.CompanionTheory.WeakHolo

open Metric Set Filter Topology Complex Real

theorem taylor_two {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) {s₀ : ℂ} {r M : ℝ}
    (hr : 0 < r) (hb : closedBall s₀ (3 * r) ⊆ U) (hM : ∀ z ∈ closedBall s₀ (3 * r), ‖f z‖ ≤ M) {η : ℂ}
    (hη : ‖η‖ ≤ r) : ‖f (s₀ + η) - f s₀ - η * deriv f s₀‖ ≤ M / r ^ 2 * ‖η‖ ^ 2 := by
  have hdf : DifferentiableOn ℂ (deriv f) U :=
    ((hf.analyticOnNhd hU).deriv_of_isOpen hU).differentiableOn
  have h1 : ∀ z ∈ closedBall s₀ (2 * r), ‖deriv f z‖ ≤ M / r := by
    intro z hz
    have hsub : closedBall z r ⊆ closedBall s₀ (3 * r) := by
      refine closedBall_subset_closedBall' ?_
      have := mem_closedBall.1 hz
      linarith
    exact norm_deriv_le_of_forall_mem_sphere_norm_le hr (hf.diffContOnCl_ball (hsub.trans hb))
      fun w hw => hM w (hsub (sphere_subset_closedBall hw))
  have h2 : ∀ z ∈ closedBall s₀ r, ‖deriv (deriv f) z‖ ≤ M / r / r := by
    intro z hz
    have hsub : closedBall z r ⊆ closedBall s₀ (2 * r) := by
      refine closedBall_subset_closedBall' ?_
      have := mem_closedBall.1 hz
      linarith
    have hsub' : closedBall s₀ (2 * r) ⊆ closedBall s₀ (3 * r) :=
      closedBall_subset_closedBall (by linarith)
    exact norm_deriv_le_of_forall_mem_sphere_norm_le hr
      (hdf.diffContOnCl_ball ((hsub.trans hsub').trans hb))
      fun w hw => h1 w (hsub (sphere_subset_closedBall hw))
  have hin : ∀ z ∈ closedBall s₀ r, z ∈ U := fun z hz =>
    hb (closedBall_subset_closedBall (by linarith) hz)
  have hc : s₀ ∈ closedBall s₀ r := mem_closedBall_self hr.le
  have h3 : ∀ z ∈ closedBall s₀ r, ‖deriv f z - deriv f s₀‖ ≤ M / r / r * ‖z - s₀‖ := fun z hz =>
    (convex_closedBall s₀ r).norm_image_sub_le_of_norm_deriv_le
      (fun y hy => (hdf y (hin y hy)).differentiableAt (hU.mem_nhds (hin y hy))) h2 hc hz
  have hMn : 0 ≤ M := (norm_nonneg _).trans (hM s₀ (mem_closedBall_self (by positivity)))
  have hs : closedBall s₀ ‖η‖ ⊆ closedBall s₀ r := closedBall_subset_closedBall hη
  have h4 := (convex_closedBall s₀ ‖η‖).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun z => f z - z * deriv f s₀) (f' := fun z => deriv f z - deriv f s₀) (C := M / r / r * ‖η‖)
    (fun z hz => by
      have a := ((hf z (hin z (hs hz))).differentiableAt (hU.mem_nhds (hin z (hs hz)))).hasDerivAt
      have b := (hasDerivAt_id z).mul_const (deriv f s₀)
      have c : HasDerivAt (fun z => f z - z * deriv f s₀) (deriv f z - 1 * deriv f s₀) z := a.sub b
      rw [one_mul] at c
      exact c.hasDerivWithinAt)
    (fun z hz => (h3 z (hs hz)).trans (by
      have := mem_closedBall_iff_norm.1 hz
      gcongr))
    (mem_closedBall_self (norm_nonneg η)) (x := s₀) (y := s₀ + η) (by simp [mem_closedBall_iff_norm])
  have e : f (s₀ + η) - f s₀ - η * deriv f s₀ =
      (f (s₀ + η) - (s₀ + η) * deriv f s₀) - (f s₀ - s₀ * deriv f s₀) := by ring
  rw [e]
  refine h4.trans (le_of_eq ?_)
  simp only [add_sub_cancel_left]
  field_simp

theorem deriv_circle {f : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r) (hf : DiffContOnCl ℂ f (ball c r)) :
    deriv f c = (2 * π * I)⁻¹ * ∮ z in C(c, r), (1 / (z - c) ^ 2) • f z := by
  have := hf.circleIntegral_one_div_sub_center_pow_smul hr 1
  simp only [zero_add, Nat.reduceAdd, Nat.factorial_one, Nat.cast_one, div_one, iteratedDeriv_one] at this
  rw [this, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (by simp [pi_ne_zero]), one_mul]

theorem continuous_deriv_family {X : Type*} [TopologicalSpace X] {w : ℂ → X → ℂ} {S : Set ℂ} {s₀ : ℂ} {r : ℝ}
    (hr : 0 < r) (hb : closedBall s₀ r ⊆ S) (hd : ∀ x, DifferentiableOn ℂ (fun s => w s x) S)
    (hc : ContinuousOn (fun y : ℂ × X => w y.1 y.2) (S ×ˢ Set.univ)) :
    Continuous fun x => deriv (fun s => w s x) s₀ := by
  have e : (fun x => deriv (fun s => w s x) s₀) = fun x => (2 * π * I : ℂ)⁻¹ *
      ∫ θ in (0 : ℝ)..2 * π, deriv (circleMap s₀ r) θ •
        ((1 / (circleMap s₀ r θ - s₀) ^ 2) • w (circleMap s₀ r θ) x) := by
    funext x
    rw [deriv_circle hr ((hd x).diffContOnCl_ball hb)]
    rfl
  rw [e]
  refine continuous_const.mul
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ _ _)
  have hA : Continuous fun θ : ℝ => deriv (circleMap s₀ r) θ := by
    simp only [deriv_circleMap]
    exact (continuous_circleMap 0 r).mul continuous_const
  have hB : Continuous fun θ : ℝ => (1 / (circleMap s₀ r θ - s₀) ^ 2 : ℂ) :=
    continuous_const.div (((continuous_circleMap s₀ r).sub continuous_const).pow 2) fun θ =>
      pow_ne_zero 2 (sub_ne_zero.2 (circleMap_ne_center hr.ne'))
  have hC : Continuous fun p : X × ℝ => w (circleMap s₀ r p.2) p.1 :=
    hc.comp_continuous (((continuous_circleMap s₀ r).comp continuous_snd).prodMk continuous_fst)
      fun p => ⟨hb (circleMap_mem_closedBall s₀ hr.le p.2), mem_univ _⟩
  exact (hA.comp continuous_snd).smul ((hB.comp continuous_snd).smul hC)

theorem form_scale {X : Type*} {V : Submodule ℂ (X → ℂ)} (μ : V →ₗ[ℂ] ℂ) {b : X → ℝ} {K : ℝ}
    (hK : ∀ f : V, (∀ x, ‖f.1 x‖ ≤ b x) → ‖μ f‖ ≤ K) (f : V) {l : ℝ} (hl : 0 < l)
    (hf : ∀ x, ‖f.1 x‖ ≤ l * b x) : ‖μ f‖ ≤ K * l := by
  have h := hK (((l⁻¹ : ℝ) : ℂ) • f) fun x => by
    have e : ‖(((l⁻¹ : ℝ) : ℂ) • f).1 x‖ = l⁻¹ * ‖f.1 x‖ := by
      simp [abs_of_pos hl]
    rw [e, inv_mul_le_iff₀ hl]
    exact hf x
  rw [map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hl),
    inv_mul_le_iff₀ hl] at h
  linarith

theorem differentiableOn_form {X : Type*} [TopologicalSpace X] {h : X → ℝ} (hh : ∀ x, 0 ≤ h x)
    {V : Submodule ℂ (X → ℂ)}
    (hV : ∀ (g : X → ℂ) (A : ℝ) (N : ℕ), Continuous g → (∀ x, ‖g x‖ ≤ A * h x ^ N) → g ∈ V)
    (μ : V →ₗ[ℂ] ℂ) (hμ : ∀ N : ℕ, ∃ C : ℝ, ∀ f : V, (∀ x, ‖f.1 x‖ ≤ h x ^ N) → ‖μ f‖ ≤ C)
    (v : ℂ → V) {S : Set ℂ} (hS : IsOpen S)
    (hd : ∀ x, DifferentiableOn ℂ (fun s => (v s).1 x) S)
    (hc : ContinuousOn (fun y : ℂ × X => (v y.1).1 y.2) (S ×ˢ Set.univ))
    (hb : ∀ Q : Set ℂ, Q ⊆ S → IsCompact Q → ∃ (C : ℝ) (N : ℕ), ∀ s ∈ Q, ∀ x, ‖(v s).1 x‖ ≤ C * h x ^ N) :
    DifferentiableOn ℂ (fun s => μ (v s)) S := by
  intro s₀ hs₀
  obtain ⟨R, hR, hRS⟩ := nhds_basis_closedBall.mem_iff.1 (hS.mem_nhds hs₀)
  obtain ⟨C, N, hCN⟩ := hb _ hRS (isCompact_closedBall s₀ R)
  obtain ⟨r, hr, rfl⟩ : ∃ r : ℝ, 0 < r ∧ R = 3 * r := ⟨R / 3, by positivity, by ring⟩
  have hsub : closedBall s₀ r ⊆ closedBall s₀ (3 * r) := closedBall_subset_closedBall (by linarith)
  let d : X → ℂ := fun x => deriv (fun s => (v s).1 x) s₀
  have dc : Continuous d := continuous_deriv_family (w := fun s => (v s).1) hr (hsub.trans hRS) hd hc
  have dB : ∀ x, ‖d x‖ ≤ C / r * h x ^ N := fun x => by
    have := norm_deriv_le_of_forall_mem_sphere_norm_le (f := fun s => (v s).1 x) (c := s₀) hr
      ((hd x).diffContOnCl_ball (hsub.trans hRS)) (C := C * h x ^ N)
      fun z hz => hCN z (hsub (sphere_subset_closedBall hz)) x
    calc ‖d x‖ ≤ C * h x ^ N / r := this
      _ = C / r * h x ^ N := by ring
  let D : V := ⟨d, hV d _ N dc dB⟩
  obtain ⟨K, hK⟩ := hμ N
  set B : ℝ := |C| / r ^ 2 + 1 with hB
  have hBpos : 0 < B := by positivity
  have key : ∀ η : ℂ, ‖η‖ < r →
      ‖μ (v (s₀ + η)) - μ (v s₀) - η • μ D‖ ≤ K * B * ‖η ^ 2‖ := by
    intro η hη
    by_cases h0 : η = 0
    · simp [h0]
    have hηp : 0 < ‖η‖ := norm_pos_iff.2 h0
    have e : μ (v (s₀ + η)) - μ (v s₀) - η • μ D = μ (v (s₀ + η) - v s₀ - η • D) := by
      simp only [map_sub, map_smul]
    rw [e, norm_pow, mul_assoc]
    refine form_scale μ hK _ (by positivity) fun x => ?_
    have t := taylor_two hS (hd x) hr hRS (fun z hz => hCN z hz x) hη.le
    have hp : 0 ≤ h x ^ N := pow_nonneg (hh x) N
    have e2 : (v (s₀ + η) - v s₀ - η • D).1 x =
        (v (s₀ + η)).1 x - (v s₀).1 x - η * deriv (fun s => (v s).1 x) s₀ := rfl
    rw [e2]
    refine t.trans ?_
    have : C * h x ^ N / r ^ 2 * ‖η‖ ^ 2 = (C / r ^ 2) * (‖η‖ ^ 2 * h x ^ N) := by ring
    rw [this, show B * ‖η‖ ^ 2 * h x ^ N = B * (‖η‖ ^ 2 * h x ^ N) by ring]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [hB]
    have : C / r ^ 2 ≤ |C| / r ^ 2 := by gcongr; exact le_abs_self C
    linarith
  have hO : (fun η : ℂ => μ (v (s₀ + η)) - μ (v s₀) - η • μ D) =O[𝓝 0] fun η => η ^ 2 :=
    Asymptotics.IsBigO.of_bound (K * B) (Filter.eventually_of_mem (ball_mem_nhds (0 : ℂ) hr)
      fun η hη => key η (by simpa using hη))
  exact (hasDerivAt_iff_isLittleO_nhds_zero.2
    (hO.trans_isLittleO (Asymptotics.isLittleO_pow_id one_lt_two))).differentiableAt.differentiableWithinAt

end GlobalTheory.CompanionTheory.WeakHolo

namespace GlobalTheory.CompanionTheory.WeakHolo

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl SiegelEisensteinSeries
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

theorem mem_modFun {g : G2 σ Y → ℂ} {A : ℝ} {N : ℕ} (hg : Continuous g)
    (hA : ∀ x, ‖g x‖ ≤ A * (ht2 x : ℝ) ^ N) : g ∈ modFun σ Y := by
  have hp : 0 < |A| + 1 := by positivity
  have hq : (((|A| + 1 : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have h1 : ((((|A| + 1 : ℝ)) : ℂ)⁻¹ • g) ∈ modFun σ Y := by
    refine Submodule.subset_span ⟨hg.const_smul _, N, fun x => ?_⟩
    have hh : 0 ≤ (ht2 x : ℝ) ^ N := by positivity
    rw [Pi.smul_apply, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp,
      inv_mul_le_iff₀ hp]
    refine (hA x).trans (mul_le_mul_of_nonneg_right ?_ hh)
    linarith [le_abs_self A]
  have := (modFun σ Y).smul_mem (((|A| + 1 : ℝ)) : ℂ) h1
  rwa [smul_inv_smul₀ hq] at this

theorem wholo_growForms (v : ℂ → modFun σ Y) {S : Set ℂ} (hS : IsOpen S)
    (hd : ∀ x, DifferentiableOn ℂ (fun s => (v s).1 x) S)
    (hc : ContinuousOn (fun y : ℂ × G2 σ Y => (v y.1).1 y.2) (S ×ˢ Set.univ))
    (hb : ∀ Q : Set ℂ, Q ⊆ S → IsCompact Q → ∃ (C : ℝ) (N : ℕ), ∀ s ∈ Q, ∀ x, ‖(v s).1 x‖ ≤ C * (ht2 x : ℝ) ^ N) :
    WHolo {μ | IsGrowForm μ} v S := fun μ hμ =>
  differentiableOn_form (h := fun x : G2 σ Y => (ht2 x : ℝ)) (fun x => NNReal.coe_nonneg _)
    (fun _ _ _ hg hA => mem_modFun hg hA) μ hμ v hS hd hc hb

end GlobalTheory.CompanionTheory.WeakHolo

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactSpanFiniteDimStable
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactSpanFiniteDimStable
set_option maxSynthPendingDepth 1
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

noncomputable section

namespace GlobalTheory.CompanionTheory.HCRep

open AutomorphicForm GlobalTheory.CompanionTheory.ArchSmooth

theorem exists_skew_curve {E : Type} [Field E] [NumberField E] {a : ℕ} (S : Matrix (Fin a) (Fin a) (Cinf E)) :
    ∃ c : ℝ → GL (Fin a) (Cinf E), c 0 = 1 ∧ HasDerivAt (fun t => toL (c t).val) (toL S) 0 ∧
      (S.conjTranspose = -S → ∀ t, (c t).val ∈ Matrix.unitaryGroup (Fin a) (Cinf E)) := by
  refine ⟨fun t => (Matrix.isUnit_exp (t • S)).unit, Units.ext (by simp), ?_, fun hS t => ?_⟩
  · open scoped Matrix.Norms.Operator in
    have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) S (0 : ℝ)
    rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
    exact h
  · rw [IsUnit.unit_spec, Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose,
      Matrix.conjTranspose_smul, hS, star_trivial, smul_neg,
      ← Matrix.exp_add_of_commute _ _ (Commute.refl (t • S)).neg_left, neg_add_cancel, NormedSpace.exp_zero]

theorem liB_skew_mem_span : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a)
    (Z : (AutomorphicForm.isExpLieAlgebra E a).lieSubalgebra),
    Matrix.conjTranspose (AutomorphicForm.mat (Z : AutomorphicForm.ArchMatrix E a)) =
      -AutomorphicForm.mat (Z : AutomorphicForm.ArchMatrix E a) →
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)) →
    ∀ ψ ∈ Submodule.span ℂ (Set.range fun k => cptRep E a k φ),
      GlobalTheory.CompanionTheory.HCRep.liB Z ψ ∈ Submodule.span ℂ (Set.range fun k => cptRep E a k φ) := by
  intro E _ _ _ a φ Z hZ hfd ψ hψ
  set W := Submodule.span ℂ (Set.range fun k => cptRep E a k φ) with hW
  have hst : ∀ k : Kinf E a, ∀ w ∈ W, cptRep E a k w ∈ W := by
    intro k w hw
    refine Submodule.span_induction (p := fun w _ => cptRep E a k w ∈ W) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨k', rfl⟩
      refine Submodule.subset_span ⟨k * k', ?_⟩
      change cptRep E a (k * k') φ = cptRep E a k (cptRep E a k' φ)
      rw [map_mul, Module.End.mul_apply]
    · rw [map_zero]; exact W.zero_mem
    · intro x y _ _ hx hy; rw [map_add (f := _)]; exact W.add_mem hx hy
    · intro r x _ hx; rw [map_smul]; exact W.smul_mem r hx
  let S : Matrix (Fin a) (Fin a) (Cinf E) := Matrix.of (mMap E a (Z : ArchMatrix E a))
  have hS : S.conjTranspose = -S := by
    ext i j w
    have h := congrFun (congrFun hZ i) j
    have h2 := congrFun (congrArg Prod.snd h) ⟨w, IsTotallyComplex.isComplex w⟩
    exact h2
  obtain ⟨c, h0, hc, hu⟩ := exists_skew_curve S
  let W' : Submodule ℂ (GA E a → ℂ) := W.map (Sm E a).subtype
  have hW' : FiniteDimensional ℂ W' := inferInstance
  have hF : ∀ t, (fun g => ψ.1 (g * infGL E a (c t))) ∈ W' := fun t =>
    ⟨cptRep E a ⟨(c t).val, hu hS t⟩ ψ, hst _ _ hψ, funext fun g => by
      have e : Unitary.toUnits (⟨(c t).val, hu hS t⟩ : Kinf E a) = c t := Units.ext rfl
      change ψ.1 (g * infGL E a (Unitary.toUnits _)) = _
      rw [e]⟩
  have hd : ∀ g : GA E a, HasDerivAt (fun t : ℝ => ψ.1 (g * infGL E a (c t))) ((liB Z ψ).1 g) 0 :=
    fun g => hasDerivAt_curve ψ g c (toL S) h0 hc
  obtain ⟨w, hw, e⟩ := AutomorphicForm.mem_of_hasDerivAt W' hF hd
  rwa [show liB Z ψ = w from Subtype.ext e.symm]

end GlobalTheory.CompanionTheory.HCRep

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactSpanFiniteDimStableStatement
set_option maxSynthPendingDepth 1
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_span_finite_dim_stable : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a)
    (Z : (AutomorphicForm.isExpLieAlgebra E a).lieSubalgebra),
    Matrix.conjTranspose (AutomorphicForm.mat (Z : AutomorphicForm.ArchMatrix E a)) =
      -AutomorphicForm.mat (Z : AutomorphicForm.ArchMatrix E a) →
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)) →
    ∀ ψ ∈ Submodule.span ℂ (Set.range fun k => cptRep E a k φ),
      GlobalTheory.CompanionTheory.HCRep.liB Z ψ ∈ Submodule.span ℂ (Set.range fun k => cptRep E a k φ) := by
  first | exact @GlobalTheory.CompanionTheory.HCRep.liB_skew_mem_span | exact GlobalTheory.CompanionTheory.HCRep.liB_skew_mem_span | (intros; apply GlobalTheory.CompanionTheory.HCRep.liB_skew_mem_span <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPairingConductorBound
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPairingConductorBound
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.MirPair

theorem JJ_preimage_box_eq_JJ_box : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (c : kˣ) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V') (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ), Continuous ψ → HasConductor ψ c → IsSmooth T → IsSmooth T' → TwInv T T' B s → ∀ (g : GL (Fin (n + 1)) k) (v : V) (v' : V'), ∃ r : kˣ, ∀ t : kˣ, valuation k ((c * t⁻¹ : kˣ) : k) ≤ valuation k (r : k) → ∀ t' : kˣ, (∀ x ∈ box (n + 1) t, (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x ∈ box (n + 1) t') → JJ ν ψ T B {x | (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x ∈ box (n + 1) t'} v v' = JJ ν ψ T B (box (n + 1) t : Set (Fin (n + 1) → k)) v v' := by
  intro k _ _ _ _ _ _ ν _ ψ c n V V' _ _ _ _ T T' B s hψ hc hT hT' hB g v v'
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  have hmono : ∀ {a a' : kˣ}, valuation k (a : k) ≤ valuation k (a' : k) →
      ∀ b ∈ GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box (n + 1) a, b ∈ GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box (n + 1) a' := by
    intro a a' haa' b hb
    have hb' : ∀ j, valuation k (b j) ≤ valuation k (a : k) := hb
    show ∀ j, valuation k (b j) ≤ valuation k (a' : k)
    exact fun j => le_trans (hb' j) haa'
  have hmin : ∀ a a' : kˣ, ∃ r : kˣ,
      valuation k (r : k) ≤ valuation k (a : k) ∧ valuation k (r : k) ≤ valuation k (a' : k) := by
    intro a a'
    rcases le_total (valuation k (a : k)) (valuation k (a' : k)) with h | h
    exacts [⟨a, le_rfl, h⟩, ⟨a', h, le_rfl⟩]
  obtain ⟨r₁, hr₁, h₁⟩ := GlobalTheory.T.shear_preserves_box_membership g
  obtain ⟨r₂, -, h₂⟩ := GlobalTheory.T.smooth_vector_fixed_small_shear T hT v
  obtain ⟨r₃, -, h₃⟩ := GlobalTheory.T.smooth_vector_fixed_small_shear T' hT' v'
  obtain ⟨r₄, h₄₁, h₄₂⟩ := hmin r₁ r₂
  obtain ⟨r, hr₄, hr₃⟩ := hmin r₄ r₃
  refine ⟨r, fun t ht t' hgt => ?_⟩
  set M : Set (Fin (n + 1) → k) :=
    {x | (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x ∈ GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box (n + 1) t'} with hM
  have hMimage : M = (fun y => ((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)
      *ᵥ y) '' (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box (n + 1) t' : Set (Fin (n + 1) → k)) := by
    ext x
    constructor
    · intro hx
      refine ⟨_, hx, ?_⟩
      simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    · rintro ⟨y, hy, rfl⟩
      show (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ
        (((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ y) ∈
          GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box (n + 1) t'
      simpa only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, SetLike.mem_coe] using hy
  have hMc : IsCompact M := by
    rw [hMimage]
    exact (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.isCompact_box (n + 1) t').image
      (Continuous.matrix_mulVec continuous_const continuous_id)
  have hMm : MeasurableSet M := hMc.isClosed.measurableSet
  have hw : Continuous (GlobalTheory.CompanionTheory.MirPair.wt ψ n) := by
    unfold GlobalTheory.CompanionTheory.MirPair.wt
    exact continuous_subtype_val.comp (hψ.comp (continuous_apply (Fin.last n)).neg)
  have hf : Continuous fun x =>
      GlobalTheory.CompanionTheory.MirPair.wt ψ n x * GlobalTheory.CompanionTheory.MirPair.coef T B v v' x :=
    hw.mul (GlobalTheory.T.mirabolic_coefficient_continuous T B hT v v')
  have hsub : (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box (n + 1) t : Set (Fin (n + 1) → k)) ⊆ M :=
    fun x hx => hgt x hx
  have key := GlobalTheory.T.fourier_box_integral_vanishing ν ψ c hψ hc (n + 1) t M
    (fun x => GlobalTheory.CompanionTheory.MirPair.wt ψ n x * GlobalTheory.CompanionTheory.MirPair.coef T B v v' x)
    (GlobalTheory.CompanionTheory.MirPair.JJ ν ψ T B M v v') hMc hMm hf (by
      intro b hb
      have hbv : ∀ j, valuation k (b j) ≤ valuation k ((c * t⁻¹ : kˣ) : k) := hb
      have hb₁ := hmono (le_trans ht (le_trans hr₄ h₄₁)) b hb
      have hb₂ := hmono (le_trans ht (le_trans hr₄ h₄₂)) b hb
      have hb₃ := hmono (le_trans ht hr₃) b hb
      have hlast : valuation k (b (Fin.last n)) < 1 :=
        lt_of_le_of_lt (le_trans (hbv (Fin.last n)) (le_trans ht (le_trans hr₄ h₄₁))) hr₁
      have hinv : ∀ x, ((GlobalTheory.CompanionTheory.MirPair.shearGL n b : GL (Fin (n + 1)) k) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x ∈ M ↔ x ∈ M :=
        fun x => h₁ b hb₁ t' x
      have h := GlobalTheory.T.mirabolic_pairing_depth_vanishing ν ψ T T' B s hψ hT hB b M v v'
        hlast (h₂ b hb₂) hinv
      rw [h₃ b hb₃] at h
      exact h)
  rw [Set.inter_eq_right.2 hsub] at key
  exact key.symm

end GlobalTheory.CompanionTheory.MirPair
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPairingConductorBoundStatement
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_pairing_conductor_bound : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (c : kˣ) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V') (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ), Continuous ψ → HasConductor ψ c → IsSmooth T → IsSmooth T' → TwInv T T' B s → ∀ (g : GL (Fin (n + 1)) k) (v : V) (v' : V'), ∃ r : kˣ, ∀ t : kˣ, valuation k ((c * t⁻¹ : kˣ) : k) ≤ valuation k (r : k) → ∀ t' : kˣ, (∀ x ∈ box (n + 1) t, (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x ∈ box (n + 1) t') → JJ ν ψ T B {x | (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x ∈ box (n + 1) t'} v v' = JJ ν ψ T B (box (n + 1) t : Set (Fin (n + 1) → k)) v v' := by
  first | exact @GlobalTheory.CompanionTheory.MirPair.JJ_preimage_box_eq_JJ_box | exact GlobalTheory.CompanionTheory.MirPair.JJ_preimage_box_eq_JJ_box | (intros; apply GlobalTheory.CompanionTheory.MirPair.JJ_preimage_box_eq_JJ_box <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellFunctionCompactSupportUnipotent
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellFunctionCompactSupportUnipotent
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Rodier.OpenSupp

theorem isLocallyConstant_ind {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) {W : Type} [AddCommGroup W]
    [Module ℂ W] (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W) (f : IndSp (stdBlocks d hd) ρ) :
    IsLocallyConstant (fun g => f.1.1 g) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g
  have hT := f.2
  refine Filter.mem_of_superset
    ((IsOpen.preimage (f := fun y => g⁻¹ * y) (continuous_const.mul continuous_id) hT).mem_nhds ?_) ?_
  · show _ = _
    simp
  · intro y hy
    have h1 := congrFun (congrArg Subtype.val hy) g
    have h2 : f.1.1 (g * (g⁻¹ * y)) = f.1.1 g := h1
    simpa using h2

theorem support_stable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) {W : Type} [AddCommGroup W]
    [Module ℂ W] (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W) (f : IndSp (stdBlocks d hd) ρ)
    (p : GL (Fin N) k) (hp : p ∈ parab k (stdBlocks d hd)) (g : GL (Fin N) k) (hg : f.1.1 g ≠ 0) :
    f.1.1 (p * g) ≠ 0 := by
  intro h0
  apply hg
  have := parInd_law (stdBlocks d hd) ρ f (⟨p, hp⟩⁻¹) (p * g)
  rw [h0, map_zero, smul_zero] at this
  simpa using this

theorem cell_eq {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (g : GL (Fin N) k)
    (hg : g ∈ cell k d hd (wOpen d hd)) :
    ∃ p ∈ parab k (stdBlocks d hd), ∃ u ∈ unipU k d hd, g = p * pm k (wOpen d hd) * u := by
  obtain ⟨p, hp, n, hn, rfl⟩ := hg
  let w := pm k (wOpen d hd)
  let e := stdBlocks d hd
  have hnLower : w * n * w⁻¹ ∈ parab k (opp e) := OpenFactor.conj_mem_parabLower k d hd hn
  let nLower : parab k (opp e) := ⟨w * n * w⁻¹, hnLower⟩
  obtain ⟨v, hv, hnv⟩ := GlobalTheory.SmGL.exists_levi_mul_unip k (opp e) nLower
  let m := leviProj k (opp e) nLower
  have hfactor : w * n * w⁻¹ = leviEmb k e m * v := hnv
  refine ⟨p * leviEmb k e m, mul_mem hp (leviEmb_mem_parab k e m), w⁻¹ * v * w,
    LowerOpen.inv_conj_mem_unipU k d hd hv, ?_⟩
  change p * w * n = p * leviEmb k e m * w * (w⁻¹ * v * w)
  calc
    p * w * n = p * (w * n * w⁻¹) * w := by group
    _ = p * leviEmb k e m * w * (w⁻¹ * v * w) := by rw [hfactor]; group

theorem exists_open_of_le {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G] (U L L₀ : Subgroup G)
    (hL : L ≤ U) (h0 : L₀ ≤ L) (O₀ : Set G) (hO : IsOpen O₀) (hOU : O₀ ∩ (U : Set G) = L₀) :
    ∃ O : Set G, IsOpen O ∧ O ∩ (U : Set G) = L := by
  refine ⟨⋃ l ∈ (L : Set G), (fun x => l⁻¹ * x) ⁻¹' O₀, isOpen_biUnion fun l _ =>
    hO.preimage (continuous_const.mul continuous_id), ?_⟩
  ext x
  simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe, exists_prop]
  constructor
  · rintro ⟨⟨l, hl, hx⟩, hxU⟩
    have : l⁻¹ * x ∈ (L₀ : Set G) := by
      rw [← hOU]
      exact ⟨hx, mul_mem (inv_mem (hL hl)) hxU⟩
    have h2 := mul_mem hl (h0 this)
    simpa using h2
  · intro hx
    have h1 : (1 : G) ∈ (L₀ : Set G) := one_mem L₀
    rw [← hOU] at h1
    exact ⟨⟨x, hx, by simpa using h1.1⟩, hL hx⟩

end GlobalTheory.CompanionTheory.Rodier.OpenSupp


open GlobalTheory.CompanionTheory.Rodier.OpenSupp in
theorem GlobalTheory.CompanionTheory.Rodier.exists_compact_open_support :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W), IsSmooth ρ → ∀ f ∈ openFns d hd ρ, ∃ L : Subgroup (GL (Fin N) k), L ≤ unipU k d hd ∧ IsCompact (L : Set (GL (Fin N) k)) ∧ (∃ O : Set (GL (Fin N) k), IsOpen O ∧ O ∩ (unipU k d hd : Set (GL (Fin N) k)) = L) ∧ ∀ g, f.1.1 g ≠ 0 → ∃ p ∈ parab k (stdBlocks d hd), ∃ u ∈ L, g = p * pm k (wOpen d hd) * u := by
  intro k _ _ _ _ h N d hd W _ _ ρ hρ f hf
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have : LocallyCompactSpace (GL (Fin N) k) := GlobalTheory.SplitFlip.locallyCompact_GL
  set w := pm k (wOpen d hd) with hw
  set U := unipU k d hd with hU
  set P := parab k (stdBlocks d hd) with hP
  have hUB : U ≤ unipB k (Fin N) := inf_le_left
  have hUc : IsClosed (U : Set (GL (Fin N) k)) := (GlobalTheory.CompanionTheory.Rodier.unipU_open_cell k h N d hd).2.2
  obtain ⟨Lj, hmono, hcpt, hle, hexh⟩ := GlobalTheory.CompanionTheory.UnipExhaust.exists_monotone_compact_exhaustion k N U hUB hUc
  have hlc := isLocallyConstant_ind d hd ρ f
  let S : Set (GL (Fin N) k) := {g | f.1.1 g ≠ 0}
  have hSo : IsOpen S := hlc ({0}ᶜ)
  have hSc : IsClosed S := by
    rw [← isOpen_compl_iff]
    have : Sᶜ = (fun g => f.1.1 g) ⁻¹' {0} := by
      ext g; simp [S]
    rw [this]; exact hlc {0}
  have hcov : ∀ g ∈ S, ∃ p ∈ P, ∃ j, ∃ n ∈ Lj j, g = p * w * n := by
    intro g hg
    obtain ⟨p, hp, u, hu, rfl⟩ := cell_eq d hd g (hf g hg)
    obtain ⟨j, hj⟩ := hexh u hu
    exact ⟨p, hp, j, u, hj, rfl⟩
  have hSeq : S ∩ {g | ∃ p ∈ P, ∃ j, ∃ n ∈ Lj j, g = p * w * n} = S :=
    Set.inter_eq_left.2 hcov
  obtain ⟨j, hj⟩ := GlobalTheory.CompanionTheory.BaireCoset.baire_double_coset P (GlobalTheory.WhitHered.CellLoc.isClosed_parab _) (GlobalTheory.SplitWeil.KO k (Fin N) : Set (GL (Fin N) k))
    GlobalTheory.SplitFlip.isCompact_KO (fun g => by
      obtain ⟨p, c, hc, e⟩ := GlobalTheory.SmGL.MultiIrr.exists_parab_mul (stdBlocks d hd) g
      exact ⟨p, p.2, c, hc, e⟩) Lj hmono hcpt w S hSo
    (fun p hp g hg => support_stable d hd ρ f p hp g hg) (by rw [hSeq]; exact hSc)
  obtain ⟨L₀, hL₀U, hL₀c, ⟨O₀, hO₀, hO₀U⟩, -⟩ :=
    GlobalTheory.T.exists_bump_section_on_compact_unipotent k (1 : AddChar k Circle) (by simpa using (continuous_one : Continuous (1 : k → Circle))) h N d hd ρ hρ 0
  obtain ⟨U₀, hU₀c, hU₀⟩ := GlobalTheory.UnipCptSub.exists_compact_subgroup_of_isCompact
    ((L₀ : Set (GL (Fin N) k)) ∪ (Lj j : Set (GL (Fin N) k))) (hL₀c.union (hcpt j)) (by
      rintro x (hx | hx)
      · exact hUB (hL₀U hx)
      · exact hUB (hle j hx))
  refine ⟨U₀ ⊓ U, inf_le_right, ?_, ?_, ?_⟩
  · rw [Subgroup.coe_inf]; exact hU₀c.inter_right hUc
  · exact exists_open_of_le U (U₀ ⊓ U) L₀ inf_le_right
      (fun x hx => ⟨hU₀ (Or.inl hx), hL₀U hx⟩) O₀ hO₀ hO₀U
  · intro g hg
    obtain ⟨p, hp, n, hn, e⟩ := hj g hg (hcov g hg)
    exact ⟨p, hp, n, ⟨hU₀ (Or.inr hn), hle j hn⟩, e⟩
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellFunctionCompactSupportUnipotentStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.open_cell_function_compact_support_unipotent : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W), IsSmooth ρ → ∀ f ∈ openFns d hd ρ, ∃ L : Subgroup (GL (Fin N) k), L ≤ unipU k d hd ∧ IsCompact (L : Set (GL (Fin N) k)) ∧ (∃ O : Set (GL (Fin N) k), IsOpen O ∧ O ∩ (unipU k d hd : Set (GL (Fin N) k)) = L) ∧ ∀ g, f.1.1 g ≠ 0 → ∃ p ∈ parab k (stdBlocks d hd), ∃ u ∈ L, g = p * pm k (wOpen d hd) * u := by
  first | exact @GlobalTheory.CompanionTheory.Rodier.exists_compact_open_support | exact GlobalTheory.CompanionTheory.Rodier.exists_compact_open_support | (intros; apply GlobalTheory.CompanionTheory.Rodier.exists_compact_open_support <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteAdelicLatticeOpenCompact
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteAdelicLatticeOpenCompact
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows PositivityTheory.AdelicQuotientData GroundTheory.Automorphic.FourierWhittaker GlobalTheory.CompanionTheory.CutOff
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.CutOff

theorem latS_isOpen_isCompact : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (S : Finset (Pl E)) (B : ∀ w : Pl E, AddSubgroup (w.adicCompletion E)), (∀ w ∈ S, IsOpen (B w : Set (w.adicCompletion E))) → (∀ w ∈ S, (B w : Set (w.adicCompletion E)) ⊆ (Formalism.UG.Ov E w : Set (w.adicCompletion E))) → IsOpen (latS S B : Set (Af E)) ∧ IsCompact (latS S B : Set (Af E)) := by
  intro E _ _ _ S B hO hI
  have hc : ∀ w : Pl E, Continuous (pLoc E w) := fun w => RestrictedProduct.continuous_eval w
  have heq : (latS S B : Set (Af E)) =
      (GroundTheory.Global.integralFiniteAdeles (𝓞 E) E : Set (Af E)) ∩
        ⋂ w ∈ S, (pLoc E w) ⁻¹' (B w : Set (w.adicCompletion E)) := by
    ext a
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨GroundTheory.Global.mem_integralFiniteAdeles.2 fun w => ?_, ?_⟩
      · by_cases hw : w ∈ S
        · exact hI w hw (h2 w hw)
        · exact h1 w hw
      · exact Set.mem_iInter₂.2 fun w hw => h2 w hw
    · rintro ⟨h1, h2⟩
      exact ⟨fun w _ => GroundTheory.Global.mem_integralFiniteAdeles.1 h1 w,
        fun w hw => Set.mem_iInter₂.1 h2 w hw⟩
  rw [heq]
  constructor
  · exact GroundTheory.Global.isOpen_integralFiniteAdeles.inter
      (isOpen_biInter_finset fun w hw => (hO w hw).preimage (hc w))
  · refine (GroundTheory.Global.isCompact_integralFiniteAdeles E).inter_right ?_
    refine isClosed_biInter fun w hw => IsClosed.preimage (hc w) ?_
    exact AddSubgroup.isClosed_of_isOpen (B w) (hO w hw)

end GlobalTheory.CompanionTheory.CutOff
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteAdelicLatticeOpenCompactStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows PositivityTheory.AdelicQuotientData GroundTheory.Automorphic.FourierWhittaker GlobalTheory.CompanionTheory.CutOff
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_adelic_lattice_open_compact : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (S : Finset (Pl E)) (B : ∀ w : Pl E, AddSubgroup (w.adicCompletion E)), (∀ w ∈ S, IsOpen (B w : Set (w.adicCompletion E))) → (∀ w ∈ S, (B w : Set (w.adicCompletion E)) ⊆ (Formalism.UG.Ov E w : Set (w.adicCompletion E))) → IsOpen (latS S B : Set (Af E)) ∧ IsCompact (latS S B : Set (Af E)) := by
  first | exact @GlobalTheory.CompanionTheory.CutOff.latS_isOpen_isCompact | exact GlobalTheory.CompanionTheory.CutOff.latS_isOpen_isCompact | (intros; apply GlobalTheory.CompanionTheory.CutOff.latS_isOpen_isCompact <;> assumption)
end
end
