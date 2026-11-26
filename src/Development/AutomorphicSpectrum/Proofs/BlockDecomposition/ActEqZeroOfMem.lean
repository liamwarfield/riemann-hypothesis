module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
public import GroundTheory.AutomorphicForms.HarishChandraCentre.VermaCoordEqZeroOfMemNPlusU
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneCharpolyTwistSpecial
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixCoefficientHeckeDecay
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CartanDecompositionCongruence
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleCosetVolumeFormula
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FixedEqFixedVectors
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RationalTuplesDiscreteCocompactAdelic
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.ResVq
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothModelRestrictionBijective

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActEqZeroOfMem
set_option maxSynthPendingDepth 1

noncomputable section

open GroundTheory.Automorphic.HarishChandra

namespace GlobalTheory.CompanionTheory.PresRho

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ}

theorem rhoVec_sub {i j : Fin n} (h : (j : ℕ) = i + 1) : rhoVec n i - rhoVec n j = 1 := by
  have : (j : ℂ) = (i : ℂ) + 1 := by exact_mod_cast h
  simp only [rhoVec, this]; ring

def sqSpan (n : ℕ) : Submodule ℂ (U n) :=
  Submodule.span ℂ {x | ∃ (u : U n) (i j : Fin n), (j : ℕ) = i + 1 ∧ u * e (j, i) ^ 2 = x}

def Jp (n : ℕ) : Submodule ℂ (U n) := vermaIdeal (rhoVec n) ⊔ sqSpan n

theorem vermaIdeal_le_Jp : vermaIdeal (rhoVec n) ≤ Jp n := le_sup_left

theorem sqSpan_le_Jp : sqSpan n ≤ Jp n := le_sup_right

theorem mul_mem_sqSpan (v : U n) {x : U n} (hx : x ∈ sqSpan n) : v * x ∈ sqSpan n := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, i, j, hij, rfl⟩ := hx
    exact Submodule.subset_span ⟨v * u, i, j, hij, mul_assoc _ _ _⟩
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hx

theorem mul_mem_Jp (v : U n) {x : U n} (hx : x ∈ Jp n) : v * x ∈ Jp n := by
  obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.1 hx
  rw [mul_add]
  exact Submodule.add_mem _ (vermaIdeal_le_Jp (mul_mem_vermaIdeal _ v hy))
    (sqSpan_le_Jp (mul_mem_sqSpan v hw))

theorem mul_sq_mem_Jp (u : U n) {i j : Fin n} (hij : (j : ℕ) = i + 1) :
    u * e (j, i) ^ 2 ∈ Jp n :=
  sqSpan_le_Jp (Submodule.subset_span ⟨u, i, j, hij, rfl⟩)

def IsAdW (μ : Fin n → ℤ) (x : U n) : Prop :=
  ∀ k, e (k, k) * x - x * e (k, k) = (μ k : ℂ) • x

def LowExp (m : Fin n × Fin n →₀ ℕ) : Prop := ∀ a ∈ m.support, IsLower a

def lowSpan (n : ℕ) : Submodule ℂ (U n) :=
  Submodule.span ℂ {x | ∃ m : Fin n × Fin n →₀ ℕ, LowExp m ∧ canon m = x}

def lowSpanW (μ : Fin n → ℤ) : Submodule ℂ (U n) :=
  Submodule.span ℂ {x | ∃ m : Fin n × Fin n →₀ ℕ, LowExp m ∧ wt m = μ ∧ canon m = x}

def casC (τ : Fin n → ℂ) : ℂ :=
  ∑ a, τ a ^ 2 + ∑ a, ∑ b, if a < b then τ a - τ b else 0

def ht (μ : Fin n → ℤ) : ℤ := ∑ k : Fin n, ((n : ℤ) - 1 - 2 * (k : ℕ)) * μ k

theorem exists_act {A : Type} [AddCommGroup A] [Module ℂ A] (G : Fin n → Fin n → Module.End ℂ A)
    (h : Formalism.REAL.GlRel G) : ∃ φ : U n →ₐ[ℂ] Module.End ℂ A, ∀ i j, φ (e (i, j)) = G i j := by
  let L : gl n →ₗ[ℂ] Module.End ℂ A :=
    { toFun := fun X => ∑ a : Fin n × Fin n, X a.1 a.2 • G a.1 a.2
      map_add' := fun X Y => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun r X => by simp [Finset.smul_sum, smul_smul] }
  have hL : ∀ a : Fin n × Fin n, L (E a) = G a.1 a.2 := by
    intro a
    show ∑ b : Fin n × Fin n, (E a) b.1 b.2 • G b.1 b.2 = _
    rw [Finset.sum_eq_single a]
    · simp [E]
    · intro b _ hb
      have : ¬ (a.1 = b.1 ∧ a.2 = b.2) := fun h => hb (Prod.ext h.1 h.2).symm
      simp [E, Matrix.single_apply, this]
    · simp
  have hE : ∀ a b : Fin n × Fin n, L ⁅E a, E b⁆ = ⁅L (E a), L (E b)⁆ := by
    intro a b
    rw [LieRing.of_associative_ring_bracket, LieRing.of_associative_ring_bracket, E_mul_sub_mul,
      hL, hL, h, map_sub, apply_ite L, apply_ite L, hL, hL, map_zero]
  let ρ : gl n →ₗ⁅ℂ⁆ Module.End ℂ A :=
    { L with
      map_lie' := fun {X Y} => by
        show L ⁅X, Y⁆ = ⁅L X, L Y⁆
        rw [eq_sum_E X, eq_sum_E Y]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [sum_lie, lie_sum, smul_lie, lie_smul, map_sum, map_smul, hE] }
  refine ⟨UniversalEnvelopingAlgebra.lift ℂ ρ, fun i j => ?_⟩
  rw [e, UniversalEnvelopingAlgebra.lift_ι_apply]
  exact hL (i, j)

theorem act_word {A : Type} [AddCommGroup A] [Module ℂ A] {G : Fin n → Fin n → Module.End ℂ A}
    (φ : U n →ₐ[ℂ] Module.End ℂ A) (hφ : ∀ i j, φ (e (i, j)) = G i j)
    (l : List (Fin n × Fin n)) : φ (word l) = (l.map fun p => G p.1 p.2).prod := by
  induction l with
  | nil => simp
  | cons a l ih => rw [word_cons, map_mul, ih, List.map_cons, List.prod_cons, hφ]

theorem glRel_e (n : ℕ) : Formalism.REAL.GlRel (fun i j : Fin n => e (i, j)) :=
  fun a b c d => e_mul_sub_mul (a, b) (c, d)

theorem IsAdW.e_mul {μ : Fin n → ℤ} {x : U n} (hx : IsAdW μ x) (a : Fin n × Fin n) :
    IsAdW (fun k => μ k + rootAt a k) (e a * x) := by
  intro k
  have h1 := e_diag_mul_sub k a
  have h2 := hx k
  have : e (k, k) * (e a * x) - e a * x * e (k, k) =
      (e (k, k) * e a - e a * e (k, k)) * x + e a * (e (k, k) * x - x * e (k, k)) := by
    noncomm_ring
  rw [this, h1, h2, smul_mul_assoc, mul_smul_comm, ← add_smul]
  push_cast; ring_nf

theorem ht_rootAt (a : Fin n × Fin n) :
    ht (rootAt a) = 2 * ((a.2 : ℕ) : ℤ) - 2 * ((a.1 : ℕ) : ℤ) := by
  simp only [ht, rootAt, mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

theorem ht_add_rootAt (μ : Fin n → ℤ) (a : Fin n × Fin n) :
    ht (fun k => μ k + rootAt a k) = ht μ + ht (rootAt a) := by
  simp only [ht, mul_add, Finset.sum_add_distrib]

theorem ht_wt (m : Fin n × Fin n →₀ ℕ) :
    ht (wt m) = m.sum fun a c => (c : ℤ) * ht (rootAt a) := by
  simp only [ht, wt, Finsupp.sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem ht_wt_nonpos {m : Fin n × Fin n →₀ ℕ} (hm : LowExp m) : ht (wt m) ≤ 0 := by
  rw [ht_wt]
  refine Finset.sum_nonpos fun a ha => ?_
  have h : (a.2 : ℕ) < a.1 := hm a ha
  show (m a : ℤ) * ht (rootAt a) ≤ 0
  rw [ht_rootAt]
  have : (0 : ℤ) ≤ (m a : ℤ) := by positivity
  nlinarith

theorem act_eq_zero_of_mem {A : Type} [AddCommGroup A] [Module ℂ A]
    (φ : U n →ₐ[ℂ] Module.End ℂ A) (t : A) (hd : ∀ k, φ (e (k, k)) t = rhoVec n k • t)
    (hu : ∀ a : Fin n × Fin n, IsUpper a → φ (e a) t = 0) {x : U n}
    (hx : x ∈ vermaIdeal (rhoVec n)) : φ x t = 0 := by
  obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.1 hx
  clear hx
  have h1 : φ y t = 0 := by
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, a, ha, rfl⟩ := hx
      simp [hu a ha]
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul r x _ hx => simp [hx]
  have h2 : φ w t = 0 := by
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, k, rfl⟩ := hx
      simp [hd k, Algebra.algebraMap_eq_smul_one]
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul r x _ hx => simp [hx]
  simp [h1, h2]

end GlobalTheory.CompanionTheory.PresRho
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusExponentTail
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstEqOne
noncomputable section

open GlobalTheory.SmGL ValuativeRel

namespace GlobalTheory.CompanionTheory.ExtCharU

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem pw_add {n : ℕ} (ξ : Fin n → ℂˣ) (x y : Fin n → ℤ) :
    GlobalTheory.BCT.pw ξ (x + y) = GlobalTheory.BCT.pw ξ x * GlobalTheory.BCT.pw ξ y := by
  simp only [GlobalTheory.BCT.pw, Pi.add_apply, zpow_add, Units.val_mul, Finset.prod_mul_distrib]

theorem pw_ne_zero {n : ℕ} (ξ : Fin n → ℂˣ) (x : Fin n → ℤ) : GlobalTheory.BCT.pw ξ x ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun i _ => Units.ne_zero _

def dg {n : ℕ} (ϖ : kˣ) (e : Fin n → ℤ) : Fin n → kˣ := fun i => ϖ ^ e i

theorem dg_add {n : ℕ} (ϖ : kˣ) (x y : Fin n → ℤ) : dg ϖ (x + y) = dg ϖ x * dg ϖ y := by
  funext i; simp [dg, zpow_add]

theorem ord_zpow (ϖ : kˣ) (m : ℤ) : ord k (ϖ ^ m) = m * ord k ϖ := by
  let o : kˣ →* Multiplicative ℤ := MonoidHom.mk' (fun x => .ofAdd (ord k x)) fun x y => by
    rw [ord_mul, ofAdd_add]
  have h := map_zpow o ϖ m
  have h2 : ord k (ϖ ^ m) = m • ord k ϖ := by
    have := congrArg Multiplicative.toAdd h
    simpa [o] using this
  simpa using h2

def rr (n : ℕ) : Fin n → ℤ := fun i => (n : ℤ) - 1 - (i : ℕ)

theorem rr_anti (n : ℕ) : StrictAnti (rr n) := fun i j h => by
  have : (i : ℕ) < j := h
  simp only [rr]; omega

theorem rr_smul_anti (n : ℕ) {N : ℤ} (hN : 0 < N) : StrictAnti (N • rr n) := fun i j h => by
  have := rr_anti n h
  simp only [Pi.smul_apply, smul_eq_mul]
  exact mul_lt_mul_of_pos_left this hN

theorem add_anti {n : ℕ} (e : Fin n → ℤ) :
    ∃ N : ℤ, 0 < N ∧ StrictAnti (e + N • rr n) := by
  refine ⟨1 + 2 * ∑ i, |e i|, by positivity, fun i j h => ?_⟩
  have hij : (i : ℕ) < j := h
  have hi : |e i| ≤ ∑ l, |e l| :=
    Finset.single_le_sum (f := fun l => |e l|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have hj : |e j| ≤ ∑ l, |e l| :=
    Finset.single_le_sum (f := fun l => |e l|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
  have h1 := abs_le.1 (le_refl |e i|)
  have h2 := abs_le.1 (le_refl |e j|)
  set S := ∑ l, |e l|
  have hd : (1 : ℤ) ≤ rr n i - rr n j := by simp only [rr]; omega
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  nlinarith

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem const_eq_one (R : Representation ℂ (Fin n → kˣ) M) {z : M} {ϖ : kˣ} {ξ : Fin n → ℂˣ} {c : ℂ}
    (hz : z ≠ 0)
    (hx : ∀ x : Fin n → ℤ, StrictAnti x → R (fun i => ϖ ^ x i) z = (c * GlobalTheory.BCT.pw ξ x) • z) :
    c = 1 := by
  have hr := hx (rr n) (rr_anti n)
  have h2 := hx (rr n + rr n) (by
    simpa [two_smul] using rr_smul_anti n (N := 2) (by norm_num))
  have hd : (fun i => ϖ ^ (rr n + rr n) i) = (fun i => ϖ ^ rr n i) * (fun i => ϖ ^ rr n i) :=
    dg_add ϖ (rr n) (rr n)
  rw [hd, map_mul, Module.End.mul_apply, hr, map_smul, hr, smul_smul, pw_add] at h2
  set p := GlobalTheory.BCT.pw ξ (rr n)
  have hp : p ≠ 0 := pw_ne_zero ξ _
  have h3 : c * p * (c * p) = c * (p * p) := smul_left_injective ℂ hz h2
  have hc : c ≠ 0 := by
    rintro rfl
    apply hz
    have h4 : R (fun i => ϖ ^ rr n i) z = 0 := by simpa using hr
    have h5 := congrArg (R (fun i => ϖ ^ rr n i)⁻¹) h4
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, map_zero] at h5
    simpa using h5
  have hpp : p * p ≠ 0 := mul_ne_zero hp hp
  apply mul_left_cancel₀ (mul_ne_zero hc hpp)
  linear_combination h3

theorem eig_all (R : Representation ℂ (Fin n → kˣ) M) {z : M} {ϖ : kˣ} {ξ : Fin n → ℂˣ}
    (hx : ∀ x : Fin n → ℤ, StrictAnti x → R (fun i => ϖ ^ x i) z = GlobalTheory.BCT.pw ξ x • z)
    (e : Fin n → ℤ) : R (dg ϖ e) z = GlobalTheory.BCT.pw ξ e • z := by
  obtain ⟨N, hN, ha⟩ := add_anti e
  have hy := hx _ (rr_smul_anti n hN)
  have hxy := hx _ ha
  have hd : (fun i => ϖ ^ (e + N • rr n) i) = dg ϖ e * (fun i => ϖ ^ (N • rr n) i) :=
    dg_add ϖ e _
  rw [hd, map_mul, Module.End.mul_apply, hy, map_smul, pw_add, mul_comm, mul_smul] at hxy
  exact smul_right_injective M (pw_ne_zero ξ (N • rr n)) hxy

theorem extChar : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M]
    (R : Representation ℂ (Fin n → kˣ) M) (z : M) (ϖ : kˣ) (ξ : Fin n → ℂˣ) (c : ℂ),
    z ≠ 0 → ord k ϖ = 1 → (∀ t ∈ torusO k (Fin n), R t z = z) →
    (∀ x : Fin n → ℤ, StrictAnti x → R (fun i => ϖ ^ x i) z = (c * GlobalTheory.BCT.pw ξ x) • z) →
    ∀ t : Fin n → kˣ,
      R t z = (((GlobalTheory.SmGL.torusChar fun i => unrChar k (ξ i)) t : ℂˣ) : ℂ) • z := by
  intro k _ _ _ _ n M _ _ R z ϖ ξ c hz hϖ hO hx t
  have hc : c = 1 := const_eq_one R hz hx
  subst hc
  simp only [one_mul] at hx
  set e : Fin n → ℤ := fun i => ord k (t i) with he
  have hu : t * (dg ϖ e)⁻¹ ∈ torusO k (Fin n) := by
    intro i
    apply ord_eq_zero_iff.1
    have h1 : ord k (t i * (ϖ ^ e i)⁻¹) = 0 := by
      have h2 := ord_mul k (t i * (ϖ ^ e i)⁻¹) (ϖ ^ e i)
      rw [inv_mul_cancel_right, ord_zpow, hϖ, mul_one] at h2
      have h3 : e i = ord k (t i) := rfl
      omega
    simpa [dg] using h1
  have ht : t = dg ϖ e * (t * (dg ϖ e)⁻¹) := by simp
  have h1 : R t z = R (dg ϖ e) z := by
    conv_lhs => rw [ht]
    rw [map_mul, Module.End.mul_apply, hO _ hu]
  rw [h1, eig_all R hx e, GlobalTheory.SmGL.torusChar_apply]
  congr 1
  simp [GlobalTheory.BCT.pw, he, unrChar_apply]

end GlobalTheory.CompanionTheory.ExtCharU
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusExponentTail
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel

namespace GlobalTheory.CompanionTheory.TorusExpU

theorem torusExp : PositivityTheory.Rg.BcB.F.Tail.PExp.TorusExp := by
  unfold PositivityTheory.Rg.BcB.F.Tail.PExp.TorusExp
  intro k _ _ _ _ n V _ _ π ϖ hϖ ξ c y hy hfix hx t
  have hord : ord k ϖ = 1 := by
    exact GlobalTheory.SmGL.ord_eq_one hϖ
  refine GlobalTheory.CompanionTheory.ExtCharU.extChar k n _ (jacB π) y ϖ ξ c hy hord ?_ ?_ t
  · intro s hs
    have h1 : ((deltaHalf k fun _ : Fin n => Unit).comp (leviTorus k (Fin n)).toMonoidHom) s = 1 := by
      simpa using GlobalTheory.SmGL.UnramFixed.deltaHalf_torusO k hs
    have h2 : jacBU π s y = y := by simpa using hfix ⟨s, hs⟩
    rw [GlobalTheory.SmGL.UnramFixed.jacB_apply, h1, h2]
    simp
  · intro x hxa
    have hD : ((deltaHalf k fun _ : Fin n => Unit).comp (leviTorus k (Fin n)).toMonoidHom)
        (fun i => ϖ ^ x i) = deltaHalf k (fun _ : Fin n => Unit) (leviTorus k (Fin n) fun i => ϖ ^ x i) := rfl
    have hne : ((deltaHalf k (fun _ : Fin n => Unit) (leviTorus k (Fin n) fun i => ϖ ^ x i) : ℂˣ) : ℂ) ≠ 0 :=
      Units.ne_zero _
    rw [GlobalTheory.SmGL.UnramFixed.jacB_apply, hD, hx x hxa, smul_smul]
    congr 1
    rw [Units.val_inv_eq_inv_val, mul_comm, mul_assoc, mul_inv_cancel₀ hne, mul_one]
    rfl

end GlobalTheory.CompanionTheory.TorusExpU

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusExponentTailStatement
namespace PositivityTheory.Rg.BcB.F.Tail.PExp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_exponent_tail : PositivityTheory.Rg.BcB.F.Tail.PExp.TorusExp := by
  first | exact @GlobalTheory.CompanionTheory.TorusExpU.torusExp | exact GlobalTheory.CompanionTheory.TorusExpU.torusExp | (intros; apply GlobalTheory.CompanionTheory.TorusExpU.torusExp <;> assumption)
end PositivityTheory.Rg.BcB.F.Tail.PExp
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SquareIntegrableOfHeckeSpectral
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SummableProdPowMultiIndex
namespace GlobalTheory.CompanionTheory.Summability

theorem summable_prod_pow_multiIndex : ∀ (r : ℕ) (x : Fin r → ℝ), (∀ i, 0 ≤ x i) → (∀ i, x i < 1) →
    Summable (fun j : Fin r → ℕ => ∏ i, x i ^ j i) := by
  intro r
  induction r with
  | zero =>
    intro x _ _
    exact (hasSum_fintype _).summable
  | succ r ih =>
    intro x h0 h1
    let e : ℕ × (Fin r → ℕ) ≃ (Fin (r + 1) → ℕ) :=
      { toFun := fun p => Fin.cons p.1 p.2
        invFun := fun j => (j 0, Fin.tail j)
        left_inv := fun p => by simp
        right_inv := fun j => by simp }
    rw [← e.summable_iff]
    have hA : Summable (fun n : ℕ => x 0 ^ n) := summable_geometric_of_lt_one (h0 0) (h1 0)
    have hB : Summable (fun j : Fin r → ℕ => ∏ i, x i.succ ^ j i) :=
      ih (fun i => x i.succ) (fun i => h0 _) (fun i => h1 _)
    have hM := hA.mul_of_nonneg hB (fun n => pow_nonneg (h0 0) n)
      (fun j => Finset.prod_nonneg (fun i _ => pow_nonneg (h0 _) _))
    refine hM.congr ?_
    rintro ⟨n, j⟩
    simp [e, Fin.prod_univ_succ]

end GlobalTheory.CompanionTheory.Summability
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SquareIntegrableOfHeckeSpectral
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.SqIntHecke

theorem lintegral_sq_lt_top_of_cover {X ι κ : Type*} [MeasurableSpace X] (μ : Measure X) (F : X → ℝ) [Finite ι]
    [Countable κ] (A : ι → κ → Set X) (hcov : ∀ x, ∃ i j, x ∈ A i j) (b w : ι → κ → ℝ) (hw : ∀ i j, 0 ≤ w i j)
    (E : ENNReal) (hE : E < ⊤) (hF : ∀ i j, ∀ x ∈ A i j, ‖F x‖ ≤ b i j)
    (hμ : ∀ i j, μ (A i j) ≤ ENNReal.ofReal (w i j) * E)
    (hsum : ∀ i, Summable fun j => b i j ^ 2 * w i j) :
    ∫⁻ x, ‖F x‖ₑ ^ (2 : ℝ) ∂μ < ⊤ := by
  classical
  have := Fintype.ofFinite ι
  have hu : (⋃ p : ι × κ, A p.1 p.2) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨i, j, h⟩ := hcov x
    exact ⟨(i, j), h⟩
  have h1 : ∫⁻ x, ‖F x‖ₑ ^ (2 : ℝ) ∂μ ≤ ∑' p : ι × κ, ∫⁻ x in A p.1 p.2, ‖F x‖ₑ ^ (2 : ℝ) ∂μ := by
    conv_lhs => rw [← setLIntegral_univ, ← hu]
    exact lintegral_iUnion_le _ _
  have h2 : ∀ p : ι × κ, ∫⁻ x in A p.1 p.2, ‖F x‖ₑ ^ (2 : ℝ) ∂μ ≤
      ENNReal.ofReal (b p.1 p.2 ^ 2 * w p.1 p.2) * E := by
    rintro ⟨i, j⟩
    have h3 : ∫⁻ x in A i j, ‖F x‖ₑ ^ (2 : ℝ) ∂μ ≤ ∫⁻ x in A i j, ENNReal.ofReal (b i j ^ 2) ∂μ := by
      refine setLIntegral_mono measurable_const fun x hx => ?_
      rw [ENNReal.rpow_two, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (hF i j x hx) 2)
    refine h3.trans ?_
    rw [setLIntegral_const, ENNReal.ofReal_mul (sq_nonneg _), mul_assoc]
    gcongr
    exact hμ i j
  refine (h1.trans (ENNReal.tsum_le_tsum h2)).trans_lt ?_
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_prod (f := fun i j => ENNReal.ofReal (b i j ^ 2 * w i j))]
  refine ENNReal.mul_lt_top ?_ hE
  rw [tsum_fintype]
  refine ENNReal.sum_lt_top.2 fun i _ => ?_
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg (sq_nonneg _) (hw i j)) (hsum i)]
  exact ENNReal.ofReal_lt_top

theorem sq_mul_pow_eq {r : ℕ} (q : ℝ) (e g : Fin r → ℕ) (ρ : Fin r → ℝ) (C : ℝ) :
    (C * ∏ j, ρ j ^ g j) ^ 2 * q ^ (∑ j, g j * e j) = C ^ 2 * ∏ j, (q ^ e j * ρ j ^ 2) ^ g j := by
  have h1 : ∏ j, (q ^ e j) ^ g j = q ^ (∑ j, g j * e j) := by
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_congr rfl fun j _ => by rw [← pow_mul, mul_comm]
  have h2 : ∏ j, (ρ j ^ 2) ^ g j = (∏ j, ρ j ^ g j) ^ 2 := by
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl fun j _ => by rw [← pow_mul, ← pow_mul, mul_comm]
  simp only [mul_pow _ _ (g _)]
  rw [Finset.prod_mul_distrib, h1, h2, mul_pow C, mul_assoc, mul_comm (q ^ _)]

theorem isSqIntCoeff_of_heckeSpectral : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → π.IsIrreducible → IsAdmissible π → Zls.UnitaryCentral π →
    Zls.HeckeSpectral π → IsSqIntCoeff π := by
  intro k _ _ _ _ N V _ _ π hs hi ha hu hH
  unfold IsSqIntCoeff CoeffLp
  intro _ _ μ hμ v l hl
  have hcen : ∀ z ∈ Subgroup.center (GL (Fin N) k), ∀ w, ‖l (π z w)‖ = ‖l w‖ := by
    intro z hz w
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
    obtain ⟨t, rfl⟩ := hz
    obtain ⟨c, hc⟩ := GlobalTheory.T.admissible_irreducible_central_scalar k N V π hs hi ha t
    rw [hc, map_smul, norm_smul, hu t c hc, one_mul]
  have hF : ∀ g : GL (Fin N) k, ‖l (π (QuotientGroup.mk g : AdGL k N).out v)‖ = ‖l (π g v)‖ := by
    intro g
    obtain ⟨z, hz⟩ := QuotientGroup.mk_out_eq_mul (Subgroup.center (GL (Fin N) k)) g
    rw [hz, Subgroup.mem_center_iff.1 z.2 g, map_mul, Module.End.mul_apply, hcen _ z.2]
  have hmeas : AEStronglyMeasurable (fun q : AdGL k N => ‖l (π q.out v)‖) μ := by
    refine Continuous.aestronglyMeasurable ((QuotientGroup.isQuotientMap_mk _).continuous_iff.2 ?_)
    rw [show (fun q : AdGL k N => ‖l (π q.out v)‖) ∘ QuotientGroup.mk = fun g => ‖l (π g v)‖ from funext hF]
    exact ((SqIntBridge.isLocallyConstant_orbit hs v).comp fun w => ‖l w‖).continuous
  refine ⟨fun q => ‖l (π q.out v)‖, hF, ?_⟩
  unfold MemLp
  rw [show ENNReal.ofReal 2 = 2 by simp, eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top hmeas]
  simp only [ENNReal.toReal_ofNat]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have : Subsingleton (GL (Fin 0) k) := inferInstance
    have h1 : Subsingleton (AdGL k 0) := ⟨fun x y => by
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
      rw [Subsingleton.elim a b]⟩
    have h2 : μ Set.univ < ⊤ := isCompact_univ.measure_lt_top
    refine lintegral_sq_lt_top_of_cover μ _ (fun _ _ : Unit => Set.univ) (fun _ => ⟨(), (), trivial⟩)
      (fun _ _ => ‖l (π (1 : AdGL k 0).out v)‖) (fun _ _ => 1) (fun _ _ => zero_le_one) _ h2 ?_ (by simp)
      (fun _ => (hasSum_fintype _).summable)
    intro _ _ x _
    rw [Subsingleton.elim x 1, norm_norm]
  obtain ⟨m1, hm1, hK1⟩ := GlobalTheory.T.congruence_subgroup_basis_nhds k N _ (hs v) (by simp)
  obtain ⟨m2, hm2, hK2⟩ := GlobalTheory.T.congruence_subgroup_basis_nhds k N _ hl (by simp [Module.End.one_eq_id])
  have hm : 1 ≤ max m1 m2 := hm1.trans (le_max_left _ _)
  obtain ⟨m, hmm⟩ : ∃ m, m = max m1 m2 := ⟨_, rfl⟩
  rw [← hmm] at hm
  have hv : v ∈ fixed π (Zls.Km k N m) := by
    rintro ⟨x, hx⟩
    have : π x v = v := hK1 (GlobalTheory.T.congruence_subgroup_antitone k N m1 m (hmm ▸ le_max_left _ _) hx)
    simpa using this
  have hlK : ∀ x ∈ Zls.Km k N m, l ∘ₗ π x = l := fun x hx =>
    hK2 (GlobalTheory.T.congruence_subgroup_antitone k N m2 m (hmm ▸ le_max_right _ _) hx)
  obtain ⟨s, hsK, hcov⟩ := GlobalTheory.T.cartan_decomposition_congruence k N m hm hN
  have key : ∀ p : s, ∃ (C : ℝ) (ρ : Fin (N - 1) → ℝ), (∀ j, 0 ≤ ρ j) ∧
      (∀ j : Fin (N - 1), (Nat.card 𝓀[k] : ℝ) ^ (((j : ℕ) + 1) * (N - ((j : ℕ) + 1))) * ρ j ^ 2 < 1) ∧
      ∀ g : Fin (N - 1) → ℕ, ∀ x ∈ Zls.Km k N m, ∀ y ∈ Zls.Km k N m,
        ‖l (π (p.1.1 * x * Zls.diagPow k N (Zls.lamOf g) * y * p.1.2) v)‖ ≤ C * ∏ j, ρ j ^ g j := by
    rintro ⟨p, hp⟩
    obtain ⟨h1, h2⟩ := hsK p hp
    obtain ⟨hf, hli, heq⟩ := GlobalTheory.T.matrix_coefficient_cartan_translate k N V π m v hv l hlK p.1 p.2 h1 h2
    obtain ⟨C, ρ, hρ0, hρ1, hb⟩ := GlobalTheory.T.matrix_coefficient_hecke_decay k N V π hs ha hH m hm (π p.2 v) hf (l ∘ₗ π p.1) hli
    refine ⟨C, ρ, hρ0, hρ1, fun g x hx y hy => ?_⟩
    rw [heq _ x hx y hy]
    exact hb g
  choose C ρ hρ0 hρ1 hbound using key
  refine lintegral_sq_lt_top_of_cover μ _
    (fun (p : s) (g : Fin (N - 1) → ℕ) => (QuotientGroup.mk : GL (Fin N) k → AdGL k N) ''
      {h | ∃ x ∈ Zls.Km k N m, ∃ y ∈ Zls.Km k N m, h = p.1.1 * x * Zls.diagPow k N (Zls.lamOf g) * y * p.1.2})
    ?_ (fun p g => C p * ∏ j, ρ p j ^ g j)
    (fun _ g => (Nat.card 𝓀[k] : ℝ) ^ (∑ j : Fin (N - 1), g j * (((j : ℕ) + 1) * (N - ((j : ℕ) + 1)))))
    (fun _ _ => by positivity)
    (μ ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' (Zls.Km k N m : Set (GL (Fin N) k))))
    (GlobalTheory.T.congruence_subgroup_finite_volume k N μ hμ m) ?_ ?_ ?_
  · intro x
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨p, hp, g, a, ha', b, hb, z, hz, rfl⟩ := hcov h
    exact ⟨⟨p, hp⟩, g, _, ⟨a, ha', b, hb, rfl⟩, (QuotientGroup.mk_mul_of_mem _ hz).symm⟩
  · rintro p g _ ⟨h, ⟨a, ha', b, hb, rfl⟩, rfl⟩
    show ‖‖l (π (QuotientGroup.mk _ : AdGL k N).out v)‖‖ ≤ _
    rw [norm_norm, hF]
    exact hbound p g a ha' b hb
  · intro p g
    obtain ⟨h1, h2⟩ := hsK p.1 p.2
    refine (GlobalTheory.T.double_coset_volume_le k N μ hμ m hm p.1.1 p.1.2 h1 h2 g).trans_eq ?_
    rw [ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  · intro p
    have h := GlobalTheory.CompanionTheory.Summability.summable_prod_pow_multiIndex (N - 1)
      (fun j => (Nat.card 𝓀[k] : ℝ) ^ (((j : ℕ) + 1) * (N - ((j : ℕ) + 1))) * ρ p j ^ 2)
      (fun j => by positivity) (hρ1 p)
    exact (h.mul_left (C p ^ 2)).congr fun g => (sq_mul_pow_eq _ _ g _ _).symm

end GlobalTheory.CompanionTheory.SqIntHecke
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SquareIntegrableOfHeckeSpectralStatement
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.square_integrable_of_hecke_spectral : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → π.IsIrreducible → IsAdmissible π → Zls.UnitaryCentral π → Zls.HeckeSpectral π → IsSqIntCoeff π := by
  first | exact @GlobalTheory.CompanionTheory.SqIntHecke.isSqIntCoeff_of_heckeSpectral | exact GlobalTheory.CompanionTheory.SqIntHecke.isSqIntCoeff_of_heckeSpectral | (intros; apply GlobalTheory.CompanionTheory.SqIntHecke.isSqIntCoeff_of_heckeSpectral <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VectorLengthFormulaOfParts
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VectorLengthFormulaOfParts
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.Mass.One

open PositivityTheory.Rg.Mass

theorem finite_rat_compact {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (n M : ℕ) (K : Set (Fin n → Fin M → AF F ⊗[F] E)) (hK : IsCompact K) :
    {X : Fin n → Fin M → E | ratTup (AF F) X ∈ K}.Finite := by
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  obtain ⟨_, _, _, _, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (AF F)
  have hinj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
    Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective _ _)
  have hri : Function.Injective (ratTup (F := F) (AF F) : (Fin n → Fin M → E) → _) := fun X Y h =>
    funext fun a => funext fun i => hinj (congrFun (congrFun h a) i)
  let f : (Fin n → Fin M → E) →+ (Fin n → Fin M → AF F ⊗[F] E) :=
    AddMonoidHom.mk' (ratTup (F := F) (AF F)) (fun X Y => by funext a i; simp [ratTup, map_add (f := _)])
  have hdisc : DiscreteTopology f.range := Formalism.IndefR.Eqv.G5.tup_disc (F := F) (E := E) M n
  have hcl : IsClosed (f.range : Set (Fin n → Fin M → AF F ⊗[F] E)) := AddSubgroup.isClosed_of_discrete
  have hfin : (K ∩ (f.range : Set (Fin n → Fin M → AF F ⊗[F] E))).Finite :=
    (hK.inter_right hcl).finite ⟨DiscreteTopology.of_subset (s := (f.range : Set (Fin n → Fin M → AF F ⊗[F] E))) hdisc Set.inter_subset_right⟩
  refine (hfin.preimage hri.injOn).subset fun X hX => ⟨hX, X, rfl⟩

theorem theta_locFin {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)) (hμ : IsHaarH F E σ M J μ) (h𝓕 : IsFDH F E σ M J μ 𝓕)
    (C : Set (HA (AF F) σ J)) (hC : IsCompact C) (hcov : ∀ h, ∃ γ : HFinIn (AF F) σ J, ∃ c ∈ C, h = γ • c)
    (hμ0 : μ 𝓕 ≠ 0) (hμt : μ 𝓕 ≠ ⊤) (n : ℕ) (S : Set (Fin n → Fin M → E)) :
    IsLocallyFiniteMeasure (thetaMeas σ J μ 𝓕 S) := by
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  obtain ⟨_, _, _, _, -, -, -, hB, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (AF F)
  have := hB n M
  obtain ⟨_, _, _, _, _, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hcm M J hJ (AF F)
  obtain ⟨ac, a1, a2, -⟩ := hact n
  have hinj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
    Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective _ _)
  have hri : Function.Injective (ratTup (F := F) (AF F) : (Fin n → Fin M → E) → _) := fun X Y h =>
    funext fun a => funext fun i => hinj (congrFun (congrFun h a) i)
  refine ⟨fun X₀ => ?_⟩
  obtain ⟨K, hK, hX⟩ := exists_compact_mem_nhds X₀
  have hK' : IsCompact ((fun p : HA (AF F) σ J × (Fin n → Fin M → AF F ⊗[F] E) => actW (AF F) σ J p.1 p.2) '' (C ×ˢ K)) :=
    (hC.prod hK).image ac
  have hP := finite_rat_compact σ hcm n M _ hK'
  set P := {X : Fin n → Fin M → E | ratTup (AF F) X ∈
    ((fun p : HA (AF F) σ J × (Fin n → Fin M → AF F ⊗[F] E) => actW (AF F) σ J p.1 p.2) '' (C ×ˢ K))} with hPdef
  let Γ : Subgroup (HA (AF F) σ J) := HFinIn (AF F) σ J
  have hcov' : ∀ h : HA (AF F) σ J, ∃ γ : Γ, ∃ c ∈ C, h = (γ : HA (AF F) σ J) * c := fun h => by
    obtain ⟨γ, c, hc, e⟩ := hcov h
    exact ⟨γ, c, hc, e⟩
  have hbound : ∀ h : HA (AF F) σ J, ∑' X : S, K.indicator (1 : (Fin n → Fin M → AF F ⊗[F] E) → ℝ≥0∞)
      (actW (AF F) σ J h⁻¹ (ratTup (AF F) (X : Fin n → Fin M → E))) ≤ (P.encard : ℝ≥0∞) := fun h => by
    obtain ⟨γ, c, hc, rfl⟩ := hcov' h
    choose t ht using fun X : Fin n → Fin M → E => PositivityTheory.PlacePermOperatorBicommutantSpan.act_rat (n := n) γ⁻¹ X
    have ht' : ∀ X, actW (AF F) σ J (γ : HA (AF F) σ J)⁻¹ (ratTup (AF F) X) = ratTup (AF F) (t X) := ht
    have hti : Function.Injective t := fun X Y e => by
      have h1 := congrArg (actW (AF F) σ J (γ : HA (AF F) σ J)) ((ht' X).trans ((congrArg (ratTup (AF F)) e).trans (ht' Y).symm))
      simp only [← a2, mul_inv_cancel, a1] at h1
      exact hri h1
    let A : Set S := {X | actW (AF F) σ J ((γ : HA (AF F) σ J) * c)⁻¹ (ratTup (AF F) (X : Fin n → Fin M → E)) ∈ K}
    have e1 : ∑' X : S, K.indicator (1 : (Fin n → Fin M → AF F ⊗[F] E) → ℝ≥0∞)
        (actW (AF F) σ J ((γ : HA (AF F) σ J) * c)⁻¹ (ratTup (AF F) (X : Fin n → Fin M → E))) = (A.encard : ℝ≥0∞) := by
      rw [← ENNReal.tsum_set_one, tsum_subtype A (fun _ => (1 : ℝ≥0∞))]
      refine tsum_congr fun X => ?_
      by_cases hx : X ∈ A
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show _ ∈ K from hx)]; rfl
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (show _ ∉ K from hx)]
    rw [e1]
    refine ENat.toENNReal_le.2 (Set.encard_le_encard_of_injOn (f := fun X : S => t X.1) ?_ ?_)
    · intro X hX
      refine ⟨(c, _), ⟨hc, hX⟩, ?_⟩
      change actW (AF F) σ J c (actW (AF F) σ J ((γ : HA (AF F) σ J) * c)⁻¹ (ratTup (AF F) (X : Fin n → Fin M → E))) = ratTup (AF F) (t X.1)
      rw [← a2, mul_inv_rev, mul_inv_cancel_left, ht']
    · intro X _ Y _ e
      exact Subtype.ext (hti e)
  refine ⟨K, hX, ?_⟩
  have hm : Measurable (K.indicator (1 : (Fin n → Fin M → AF F ⊗[F] E) → ℝ≥0∞)) :=
    measurable_one.indicator hK.measurableSet
  rw [← lintegral_indicator_one hK.measurableSet, PositivityTheory.PlacePermOperatorBicommutantSpan.theta_lint F E σ hcm M J hJ μ 𝓕 hμ h𝓕 _ _ _ hm]
  have hle : ∫⁻ h in 𝓕, ∑' X : S, K.indicator (1 : (Fin n → Fin M → AF F ⊗[F] E) → ℝ≥0∞)
      (actW (AF F) σ J h⁻¹ (ratTup (AF F) (X : Fin n → Fin M → E))) ∂μ ≤ (P.encard : ℝ≥0∞) * μ 𝓕 := by
    refine (lintegral_mono hbound).trans ?_
    simp
  have hPt : (P.encard : ℝ≥0∞) ≠ ⊤ := by
    simpa using hP.encard_lt_top.ne
  exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (pos_iff_ne_zero.2 hμ0))
    (lt_of_le_of_lt hle (ENNReal.mul_lt_top hPt.lt_top hμt.lt_top))

theorem euler_of_summable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ)
    (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b) (hdet : T.det ≠ 0) (d : ℕ)
    (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v))
    (hinf : IsStdInf laminf) (hlam : ∀ v, IsStdV v (lam v))
    (minf : HermR (Ainf F) σ n → Measure (Fin n → Fin M → Ainf F ⊗[F] E))
    (hminf : IsGramFib (Ainf F) σ J n (coordW (Ainf F) b laminf n M) (coordHerm (Ainf F) σ b laminf n) minf)
    (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E))
    (hm : ∀ v, IsGramFib (Fv F v) σ J n (coordW (Fv F v) b (lam v) n M) (coordHerm (Fv F v) σ b (lam v) n) (m v))
    (hfin : ∀ v, m v (hermOf (Fv F v) σ T hT) (latV b v) < ⊤)
    (hsum : Summable fun v => |(m v (hermOf (Fv F v) σ T hT) (latV b v)).toReal - 1|)
    (I : Measure (Fin n → Fin M → AF F ⊗[F] E)) (hIf : IsLocallyFiniteMeasure I)
    (hIinv : ∀ h : HA (AF F) σ J, I.map (actW (AF F) σ J h) = I)
    (hIsupp : I {X | gramR (AF F) σ J X = T.map (inclR (AF F))}ᶜ = 0) :
    ∃ c : ℝ≥0, IsEulerProd b I c (minf (hermOf (Ainf F) σ T hT)) (fun v => m v (hermOf (Fv F v) σ T hT)) := by
  classical
  have hLi : IsLocR (Ainf F) := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hCM.1
  have hLv : ∀ v, IsLocR (Fv F v) := GlobalTheory.T.completion_is_local_ring F
  haveI hBi : BorelSpace (Ainf F) := ⟨rfl⟩
  have hFi := GlobalTheory.CompanionTheory.SW.Fact.fib_facts σ hCM J hJ (Ainf F) hLi T hT hdet b laminf hinf.1 minf hminf
  have hFv : ∀ v, SigmaFinite (m v (hermOf (Fv F v) σ T hT)) ∧
      (m v (hermOf (Fv F v) σ T hT) = 0 →
        ∀ X, gramR (Fv F v) σ J X ≠ T.map (inclR (Fv F v))) := fun v => by
    haveI : BorelSpace (Fv F v) := ⟨rfl⟩
    exact GlobalTheory.CompanionTheory.SW.Fact.fib_facts σ hCM J hJ (Fv F v) (hLv v) T hT hdet b (lam v) (hlam v).1 (m v) (hm v)
  by_cases h0 : minf (hermOf (Ainf F) σ T hT) = 0 ∨ ∃ v, m v (hermOf (Fv F v) σ T hT) = 0
  · have hempty : {X | gramR (AF F) σ J X = T.map (inclR (AF F))} = ∅ := by
      ext X
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hX
      have hloc := (GlobalTheory.T.gram_matrix_local_global F E σ hCM M J hJ n X T).1.1 hX
      rcases h0 with h | ⟨v, h⟩
      · exact hFi.2 h _ hloc.1
      · exact (hFv v).2 h _ (hloc.2 v)
    rw [hempty, Set.compl_empty] at hIsupp
    rw [Measure.measure_univ_eq_zero.mp hIsupp]
    exact ⟨0, (GlobalTheory.T.euler_product_measure_zero F E σ hCM d b n M 0 0 _ _).2.2 hfin hsum h0⟩
  · push Not at h0
    obtain ⟨hinf0, hv0⟩ := h0
    choose c hc using GlobalTheory.T.siegel_weil_orbital_measure F E σ hCM M J hJ n T hT hdet d b laminf lam hinf hlam minf hminf m hm
      I hIf hIinv hIsupp
    obtain ⟨A, hAm, hA0, hAt⟩ := @GlobalTheory.CompanionTheory.SW.Fact.exists_test_set _ _ (minf (hermOf (Ainf F) σ T hT)) hFi.1 hinf0
    choose B hBm hB0 hBt using fun v =>
      @GlobalTheory.CompanionTheory.SW.Fact.exists_test_set _ _ (m v (hermOf (Fv F v) σ T hT)) (hFv v).1 (hv0 v)
    have hstep : ∀ S : Finset (HeightOneSpectrum (𝓞 F)), ∅ ⊆ S → ∀ v, v ∉ S →
        (c S : ℝ) = c (insert v S) * (m v (hermOf (Fv F v) σ T hT) (latV b v)).toReal := by
      intro S _ v hv
      have hlatm : MeasurableSet (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) := by
        haveI := GlobalTheory.CompanionTheory.SW.Fact.borel_tup σ hCM (Fv F v) (hLv v) n M
        exact ((GlobalTheory.T.adelic_tuple_projections F E σ hCM d b n M).2.2.2.1 v).2.measurableSet
      let φ0 : ∀ w : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F w ⊗[F] E) → ℝ≥0∞ :=
        fun w => (B w).indicator 1
      let φ1 := Function.update φ0 v ((latV b v).indicator 1)
      have hφ0 : ∀ w, Measurable (φ0 w) := fun w => measurable_one.indicator (hBm w)
      have hφ1 : ∀ w, Measurable (φ1 w) := by
        intro w
        by_cases hw : w = v
        · subst hw
          simpa [φ1] using measurable_one.indicator hlatm
        · simpa [φ1, Function.update_of_ne hw] using hφ0 w
      have hAφ : Measurable (A.indicator (1 : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞)) := measurable_one.indicator hAm
      have e1 := hc S _ φ0 hAφ hφ0
      have e2 := hc (insert v S) _ φ1 hAφ hφ1
      have e3 : ∫⁻ X, pureL b (insert v S) (A.indicator 1) φ1 X ∂I =
          ∫⁻ X, pureL b S (A.indicator 1) φ0 X ∂I :=
        lintegral_congr fun X => GlobalTheory.CompanionTheory.SW.Fact.pureL_insert b S v hv _ φ0 X
      rw [e3, e1, Finset.prod_insert hv] at e2
      have hp : ∏ w ∈ S, ∫⁻ X, φ1 w X ∂(m w (hermOf (Fv F w) σ T hT)) =
          ∏ w ∈ S, ∫⁻ X, φ0 w X ∂(m w (hermOf (Fv F w) σ T hT)) :=
        Finset.prod_congr rfl fun w hw => by
          have hne : w ≠ v := fun h => hv (h ▸ hw)
          simp only [φ1, Function.update_of_ne hne]
      have hL : ∫⁻ X, φ1 v X ∂(m v (hermOf (Fv F v) σ T hT)) =
          m v (hermOf (Fv F v) σ T hT) (latV b v) := by
        simp only [φ1, Function.update_self]
        exact lintegral_indicator_one hlatm
      have hB : ∀ w, ∫⁻ X, φ0 w X ∂(m w (hermOf (Fv F w) σ T hT)) =
          m w (hermOf (Fv F w) σ T hT) (B w) := fun w => lintegral_indicator_one (hBm w)
      have hA : ∫⁻ X, A.indicator (1 : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞) X ∂(minf (hermOf (Ainf F) σ T hT)) =
          minf (hermOf (Ainf F) σ T hT) A := lintegral_indicator_one hAm
      rw [hp, hL, hA] at e2
      simp only [hB] at e2
      set Q := ∏ w ∈ S, m w (hermOf (Fv F w) σ T hT) (B w) with hQ
      set a := minf (hermOf (Ainf F) σ T hT) A with ha
      set L := m v (hermOf (Fv F v) σ T hT) (latV b v) with hLdef
      have hQ0 : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr fun w _ => hB0 w
      have hQt : Q ≠ ⊤ := ENNReal.prod_ne_top fun w _ => hBt w
      have hP0 : a * Q ≠ 0 := mul_ne_zero hA0 hQ0
      have hPt : a * Q ≠ ⊤ := ENNReal.mul_ne_top hAt hQt
      have e4 : (c S : ℝ≥0∞) * (a * Q) = ((c (insert v S) : ℝ≥0∞) * L) * (a * Q) := by
        rw [e2]; ring
      have e5 := (ENNReal.mul_left_inj hP0 hPt).mp e4
      have e6 := congrArg ENNReal.toReal e5
      simpa [ENNReal.toReal_mul] using e6
    obtain ⟨c₀, S₀, -, hS₀⟩ := GlobalTheory.T.infinite_product_renormalization _ (fun v => (m v (hermOf (Fv F v) σ T hT) (latV b v)).toReal) c ∅
      (fun _ => ENNReal.toReal_nonneg) hsum hstep
    refine ⟨c₀, hfin, hsum, S₀, fun S hS φinf φ hφi hφ => ?_⟩
    rw [hc S φinf φ hφi hφ]
    have hcS : (c S : ℝ≥0∞) = (c₀ : ℝ≥0∞) *
        ENNReal.ofReal (∏' v : {v // v ∉ S}, (m v.1 (hermOf (Fv F v.1) σ T hT) (latV b v.1)).toReal) := by
      rw [← ENNReal.ofReal_coe_nnreal (p := c S), (hS₀ S hS).2, ENNReal.ofReal_mul (NNReal.coe_nonneg _),
        ENNReal.ofReal_coe_nnreal]
    rw [hcS]
    ring

theorem vector_length_formula_up_to_constant : CoCpt → LocMass → Prop1 := by
  intro hCo hLoc F E _ _ _ _ _ σ J d b li lam μ 𝓕 mi m hcm hJ hA hli hlam hμ h𝓕 hmi hm β hβ
  obtain ⟨⟨C, hC, hcov⟩, hμ0, hμt⟩ := hCo F E σ J d b li lam μ 𝓕 mi m hcm hJ hA hli hlam hμ h𝓕 hmi hm
  obtain ⟨C₁, hC₁⟩ := hLoc F E σ J d b li lam μ 𝓕 mi m hcm hJ hA hli hlam hμ h𝓕 hmi hm
  have hE : algebraMap F E β ≠ 0 := fun h => hβ ((map_eq_zero _).1 h)
  let T : Matrix (Fin 1) (Fin 1) E := fun _ _ => algebraMap F E β
  have hT : ∀ a b, σ (T b a) = T a b := fun _ _ => σ.commutes β
  have hd : T.det ≠ 0 := by
    rw [Matrix.det_unique]
    exact hE
  obtain ⟨β', e, -, hh⟩ := GlobalTheory.T.hermitian_one_by_one_is_scalar F E σ hcm T hT
  have hββ : β' = β := (algebraMap F E).injective (congrFun (congrFun e 0) 0).symm
  rw [hββ] at hh
  obtain ⟨t1, t2⟩ := PositivityTheory.PlacePermOperatorBicommutantSpan.theta_inv F E σ hcm 2 J hJ μ 𝓕 hμ h𝓕 1 T
  have hlf : IsLocallyFiniteMeasure (thetaMeas σ J μ 𝓕 {X : Fin 1 → Fin 2 → E | gramE σ J X = T}) :=
    theta_locFin σ hcm 2 J hJ μ 𝓕 hμ h𝓕 C hC hcov hμ0 hμt 1 _
  have hfin : ∀ v, m v (hermOf (Fv F v) σ T hT) (latV b v) < ⊤ := fun v => by
    have hloc : IsLocR (Fv F v) := GlobalTheory.T.completion_is_local_ring F v
    obtain ⟨hTR, hLC, hSC, hT2, -⟩ := id hloc
    haveI := hTR
    haveI := hLC
    haveI := hSC
    haveI := hT2
    haveI : BorelSpace (Fv F v) := ⟨rfl⟩
    have hh' := GlobalTheory.T.coordinate_haar_measure F E σ hcm (Fv F v) d b (lam v) (hlam v).1
    haveI hW := hh'.2.1 1 2
    haveI hH := hh'.2.2 1
    have hl := (GlobalTheory.T.gram_fiber_measure_locallyFinite_and_ne_zero_of_isOpen F E σ hcm 2 J hJ (Fv F v) hloc 1 _ _ (m v) hW hH (hm v)
      (hermOf (Fv F v) σ T hT)).1
    exact ((GlobalTheory.T.adelic_tuple_projections F E σ hcm d b 1 2).2.2.2.1 v).1.measure_lt_top
  have hsum : Summable fun v => |(m v (hermOf (Fv F v) σ T hT) (latV b v)).toReal - 1| := by
    refine Summable.of_norm_bounded_eventually
      (g := fun v : HeightOneSpectrum (𝓞 F) => C₁ * (1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2))
      ((GlobalTheory.CompanionTheory.SW.Primes.summable_one_div_absNorm_sq F).mul_left C₁) ?_
    filter_upwards [hC₁, (GlobalTheory.T.integral_almost_all_places F E σ hcm d b).2 β hβ] with v h1 h2
    have h3 := h1.2.2 _ h2
    rw [Real.norm_eq_abs, abs_abs, hh]
    simpa [div_eq_mul_inv] using h3
  obtain ⟨c, hc⟩ := euler_of_summable σ hcm 2 J hJ 1 T hT hd d b li lam hli hlam mi hmi m hm hfin hsum _ hlf t1 t2
  simp only [hh] at hc
  exact ⟨c, hc⟩

end GlobalTheory.CompanionTheory.Mass.One
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VectorLengthFormulaOfPartsStatement
open PositivityTheory.Rg.Mass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vector_length_formula_of_parts : CoCpt → LocMass → Prop1 := by
  first | exact @GlobalTheory.CompanionTheory.Mass.One.vector_length_formula_up_to_constant | exact GlobalTheory.CompanionTheory.Mass.One.vector_length_formula_up_to_constant | (intros; apply GlobalTheory.CompanionTheory.Mass.One.vector_length_formula_up_to_constant <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittSiteRestrictBijective
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittSiteRestrictBijective
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsG CrystallineSemistableComparison.Pb.SubquotientResolution

noncomputable section

namespace GlobalTheory.CompanionTheory.FlatZar

section Main
variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O] {X : Scheme.{0}}

def resG (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) (m : ℕ)
    (P Q : ObjectProperty (Thick (Wc.L l (B.schFn q) ρ m))) (h : Q ≤ P) :
    CH.Mor (P.ι ⋙ Wc.OM l (B.schFn q) ρ m) (Q.ι ⋙ Wc.OM l (B.schFn q) ρ m) (RingHom.id (WittVector l k)) where
  G := ObjectProperty.ιOfLE h
  τ _ := LinearMap.id
  nat _ _ := rfl

set_option maxHeartbeats 1600000 in
theorem resG_bij (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) (m : ℕ) (𝒱 : Set X.Opens) (hU : sSup 𝒱 = ⊤)
    (P : ObjectProperty (Thick (Wc.L l (B.schFn q) ρ m))) (hP : P = stF q ρ m {⊤}) (h : stF q ρ m 𝒱 ≤ P) (j : ℕ) :
    Function.Bijective ((resG q ρ m P (stF q ρ m 𝒱) h).pull j) := by
  subst hP
  have z := (zar (γ := Wc.pd l k m) (p := l) (q := q) (κ := (Wc.res l k m).comp ρ) FlatT
    (Or.inr ⟨(Fact.out : l.Prime).ne_zero, Or.inr rfl⟩) 𝒱 {⊤} h
    (fun W _ => by rw [hU]; exact le_top) j).2.2
  have c1 := GlobalTheory.CompanionTheory.FlatRes.scM_bij q ρ m (stF q ρ m {⊤}) j
  have c2 := GlobalTheory.CompanionTheory.FlatRes.scM_bij q ρ m (stF q ρ m 𝒱) j
  refine (Function.Bijective.of_comp_iff' c2 _).1 ?_
  have e : ⇑((GlobalTheory.CompanionTheory.FlatRes.scM q ρ m (stF q ρ m 𝒱)).pull j) ∘ ⇑((resG q ρ m _ (stF q ρ m 𝒱) h).pull j) =
      ⇑((incl h).o.pull j) ∘ ⇑((GlobalTheory.CompanionTheory.FlatRes.scM q ρ m (stF q ρ m {⊤})).pull j) := by
    funext x
    obtain ⟨a, ha, rfl⟩ := CrystallineSemistableComparison.CechClassBoundaries.clsSurj x
    rfl
  rw [e]
  exact z.comp c1

theorem resV_bij : ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) (m : ℕ) (𝒱 : Set X.Opens), sSup 𝒱 = ⊤ → ∀ j, Function.Bijective ((resV q ρ m 𝒱).pull j) := by
  intro l _ k _ _ _ O _ X q ρ m 𝒱 hU j
  exact resG_bij q ρ m 𝒱 hU (fl l (B.schFn q) ρ m)
    (GlobalTheory.CompanionTheory.FlatRes.st_top_eq (γ := Wc.pd l k m) (p := l) (q := q) (κ := (Wc.res l k m).comp ρ) FlatT).symm
    (fun _ h => h.1) j

end Main

end GlobalTheory.CompanionTheory.FlatZar

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittSiteRestrictBijectiveStatement
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsG CrystallineSemistableComparison.Pb.SubquotientResolution
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_site_restrict_bijective : ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) (m : ℕ) (𝒱 : Set X.Opens), sSup 𝒱 = ⊤ → ∀ j, Function.Bijective ((resV q ρ m 𝒱).pull j) := by
  first | exact @GlobalTheory.CompanionTheory.FlatZar.resV_bij | exact GlobalTheory.CompanionTheory.FlatZar.resV_bij | (intros; apply GlobalTheory.CompanionTheory.FlatZar.resV_bij <;> assumption)
end
end
