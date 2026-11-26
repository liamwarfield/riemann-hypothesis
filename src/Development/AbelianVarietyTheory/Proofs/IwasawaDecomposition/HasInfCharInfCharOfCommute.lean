module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIrreducibleSmallRepUnitary
public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResEqIff
public import Formalism.LocalToGlobal.Columns.RecLevelLoc

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasInfCharInfCharOfCommute
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep
open Polynomial

namespace GlobalTheory.CuspRep

theorem exists_multiset_qdet {M : Type} [AddCommGroup M] [Module ℂ M] {n : ℕ} (F : Fin n → Fin n → Module.End ℂ M)
    (s : ℂ) (φ : M) (f : M →ₗ[ℂ] ℂ) (hf : f φ = 1) :
    ∃ m : Multiset ℂ, Multiset.card m = n ∧ ∀ u, f (Formalism.REAL.qdet F (u + s) φ) = (m.map (u + ·)).prod := by
  classical
  let Q : Finset (Fin n) → ℂ[X] := fun S => ∏ k ∈ Sᶜ, (X - C ((k : ℂ) - s))
  have hQm : ∀ S, (Q S).Monic := fun S => monic_prod_of_monic _ _ fun k _ => monic_X_sub_C _
  have hQd : ∀ S, (Q S).natDegree = Sᶜ.card := fun S => by
    simp only [Q]
    rw [natDegree_prod_of_monic _ _ fun k _ => monic_X_sub_C _]
    simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one]
  let R : ℂ[X] := ∑ S ∈ Finset.univ.erase (∅ : Finset (Fin n)), C (f (GlobalTheory.CapelliTop.subdet F S φ)) * Q S
  have h0 : (Q ∅).degree = n := by
    rw [degree_eq_natDegree (hQm _).ne_zero, hQd]; simp
  have hR : R.degree < (Q ∅).degree := by
    rw [h0]
    refine (degree_sum_le _ _).trans_lt ((Finset.sup_lt_iff (WithBot.bot_lt_coe _)).2 fun S hS => ?_)
    refine degree_le_natDegree.trans_lt ?_
    have h1 : (C (f (GlobalTheory.CapelliTop.subdet F S φ)) * Q S).natDegree < n := by
      refine (natDegree_C_mul_le _ _).trans_lt ?_
      rw [hQd, Finset.card_compl, Fintype.card_fin]
      have h2 := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 (Finset.ne_of_mem_erase hS))
      have h3 : S.card ≤ n := by simpa using Finset.card_le_univ S
      omega
    exact_mod_cast h1
  have hm : (Q ∅ + R).Monic := (hQm _).add_of_left hR
  have hd : (Q ∅ + R).natDegree = n := by
    rw [natDegree_eq_of_degree_eq_some ((degree_add_eq_left_of_degree_lt hR).trans h0)]
  have hc : Multiset.card (Q ∅ + R).roots = (Q ∅ + R).natDegree := IsAlgClosed.card_roots_eq_natDegree
  refine ⟨(Q ∅ + R).roots.map Neg.neg, by rw [Multiset.card_map, hc, hd], fun u => ?_⟩
  have e := congrArg (eval u) (prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm hc)
  have e2 : ((Q ∅ + R).roots.map Neg.neg |>.map (u + ·)).prod = eval u (Q ∅ + R) := by
    rw [← e]
    simp [eval_multiset_prod, Multiset.map_map, sub_eq_add_neg]
  have hQe : ∀ S, eval u (Q S) = ∏ k ∈ Sᶜ, (u + s - (k : ℂ)) := fun S => by
    simp only [Q, eval_prod, eval_sub, eval_X, eval_C]
    exact Finset.prod_congr rfl fun k _ => by ring
  rw [e2, GlobalTheory.CapelliTop.qdet_expand, ← Finset.add_sum_erase _ _ (Finset.mem_univ (∅ : Finset (Fin n))),
    GlobalTheory.CapelliTop.subdet_empty]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [R, eval_add, eval_finsetSum, eval_mul, eval_C, hQe, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, map_add, map_sum, map_smul, Module.End.one_apply, hf, smul_eq_mul, mul_one]
  congr 1
  exact Finset.sum_congr rfl fun S _ => mul_comm _ _

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem CuspSub.exists_scalar (π : CuspSub E a) {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a)
    (hc : ∀ o : Op E a, Commute z (act o)) : ∃ c : ℂ, ∀ φ ∈ π.V, z φ = c • φ := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  set U := Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a) with hU
  have hfin : FiniteDimensional ℂ U := (π.cusp φ hφ).1.zfin
  have hle : U ≤ π.V := Submodule.span_le.2 (by
    rintro _ ⟨y, hy, rfl⟩
    exact Zalg_stable (fun X => π.stable (.lie X)) hy φ hφ)
  have hst : ∀ x ∈ U, z x ∈ U := fun x hx => by
    have : U ≤ U.comap z := Submodule.span_le.2 (by
      rintro _ ⟨y, hy, rfl⟩
      exact Submodule.subset_span ⟨z * y, mul_mem hz hy, rfl⟩)
    exact this hx
  have hφU : φ ∈ U := Submodule.subset_span ⟨1, one_mem _, rfl⟩
  have : Nontrivial U := ⟨⟨φ, hφU⟩, 0, fun h => h0 (congrArg Subtype.val h)⟩
  obtain ⟨c, hc'⟩ := Module.End.exists_eigenvalue (z.restrict hst)
  obtain ⟨v, hv⟩ := hc'.exists_hasEigenvector
  have hv1 : z v.1 = c • v.1 := congrArg Subtype.val hv.apply_eq_smul
  refine ⟨c, fun ψ hψ => ?_⟩
  rcases π.irred (π.V ⊓ z.eigenspace c) inf_le_left (fun o x hx => ⟨π.stable o x hx.1, by
    have h1 : z x = c • x := Module.End.mem_eigenspace_iff.1 hx.2
    refine Module.End.mem_eigenspace_iff.2 ?_
    rw [← map_smul, ← h1]
    exact LinearMap.congr_fun (hc o).eq x⟩) with h | h
  · have : v.1 ∈ π.V ⊓ z.eigenspace c := ⟨hle v.2, Module.End.mem_eigenspace_iff.2 hv1⟩
    rw [h] at this
    exact absurd (Subtype.ext ((Submodule.mem_bot ℂ).1 this)) hv.2
  · rw [← h] at hψ
    exact Module.End.mem_eigenspace_iff.1 hψ.2

theorem hasInfChar_infChar_of_commute : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), (∀ (τ : E →+* ℂ) (u : ℂ) (o : Op E a), Commute (cap (a := a) τ u) (act o)) → ∀ (π : CG E a) (τ : E →+* ℂ), π.HasInfChar τ (π.infChar τ) := by
  intro E _ _ _ a hc π τ
  suffices h : ∃ m, π.HasInfChar τ m by
    obtain ⟨m, h⟩ := h
    rwa [h.infChar_eq]
  induction π using Quotient.inductionOn with
  | h π =>
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℂ h0
  obtain ⟨m, hm, h⟩ := exists_multiset_qdet (Eop (a := a) τ) (((a : ℂ) - 1) / 2) φ f hf
  refine ⟨m, hm, fun u ψ hψ => ?_⟩
  obtain ⟨c, h1⟩ := π.exists_scalar (z := cap τ u) (Algebra.subset_adjoin ⟨τ, u, rfl⟩) (hc τ u)
  have h2 : f (cap τ u φ) = _ := h u
  rw [h1 φ hφ, map_smul, hf, smul_eq_mul, mul_one] at h2
  rw [h1 ψ hψ, h2]

end GlobalTheory.CuspRep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqBotOrTopOfTensor
open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Branching

noncomputable section

namespace GlobalTheory.CoefIrred

theorem eq_bot_or_top_of_tensor {K ι : Type} [Field K] [Fintype ι] {V κ G : ι → Type}
    [∀ τ, AddCommGroup (V τ)] [∀ τ, Module K (V τ)] [Fintype (∀ τ, κ τ)] {W : Type} [AddCommGroup W] [Module K W]
    (b : ∀ τ, Module.Basis (κ τ) K (V τ)) (t : (∀ τ, V τ) →ₘₗ[K] W)
    (B : Module.Basis (∀ τ, κ τ) K W)
    (hB : ∀ i, B i = t fun τ => b τ (i τ)) (ρ : ∀ τ, G τ → Module.End K (V τ))
    (hρ : ∀ τ, Submodule.span K (Set.range (ρ τ)) = ⊤) (U : Submodule K W)
    (hU : ∀ g : ∀ τ, G τ, ∃ L : Module.End K W,
      (∀ f, L (t f) = t fun τ => ρ τ (g τ) (f τ)) ∧ ∀ x ∈ U, L x ∈ U) :
    U = ⊥ ∨ U = ⊤ := by
  classical
  rw [or_iff_not_imp_left]
  intro hne
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨i₀, hi₀⟩ : ∃ i, B.repr x i ≠ 0 := by
    by_contra h
    push Not at h
    exact hx0 (B.repr.map_eq_zero_iff.1 (Finsupp.ext h))
  let Φ : (∀ τ, Module.End K (V τ)) →ₘₗ[K] W :=
    ∑ i, B.repr x i • t.compLinearMap fun τ => LinearMap.applyₗ (b τ (i τ))
  have hΦ : ∀ T, Φ T = ∑ i, B.repr x i • t fun τ => T τ (b τ (i τ)) := by
    intro T
    simp [Φ]
  have h0 : U.mkQ.compMultilinearMap Φ = 0 := by
    refine MultilinearMap.ext_of_span_eq_top hρ fun g => ?_
    obtain ⟨L, hL, hLU⟩ := hU g
    have : Φ (fun τ => ρ τ (g τ)) = L x := by
      rw [hΦ]
      conv_rhs => rw [← B.sum_repr x]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, hB, hL]
    simpa [this] using hLU x hx
  have hmem : ∀ T, Φ T ∈ U := fun T => by
    simpa using congrArg (fun m => m T) h0
  have hj : ∀ j, B j ∈ U := by
    intro j
    have h1 := hmem fun τ => ((b τ).coord (i₀ τ)).smulRight (b τ (j τ))
    rw [hΦ, Finset.sum_eq_single i₀] at h1
    · simp only [LinearMap.smulRight_apply, Module.Basis.coord_apply, Module.Basis.repr_self,
        Finsupp.single_eq_same, one_smul, ← hB] at h1
      exact (U.smul_mem_iff hi₀).1 h1
    · intro i _ hi
      obtain ⟨τ, hτ⟩ := Function.ne_iff.1 hi
      rw [t.map_coord_zero τ, smul_zero]
      simp [Finsupp.single_eq_of_ne hτ.symm]
    · simp
  rw [eq_top_iff, ← B.span_eq, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  exact hj j

variable {K ι : Type} [Field K] [Fintype ι] {n : ℕ}

def tenMul (lam : ι → DomWeight n) : (∀ τ, nablaSq K n (lam τ)) →ₘₗ[K] VV K lam :=
  haveI := Classical.decEq ι
  ((MultilinearMap.mkPiAlgebra K ι (Pol K ι n)).compLinearMap fun τ =>
    (Formalism.GradedWeylDivisibility.blockEmb K τ).toLinearMap ∘ₗ (nablaSq K n (lam τ)).subtype).codRestrict (VV K lam)
    fun f => Submodule.subset_span ⟨fun τ => f τ, fun τ => (f τ).2, by simp⟩

theorem tenMul_coe (lam : ι → DomWeight n) (f : ∀ τ, nablaSq K n (lam τ)) :
    (tenMul lam f : Pol K ι n) = ten fun τ => (f τ : MvPolynomial (Fin n × Fin n) K) := by
  classical
  exact (MultilinearMap.mkPiAlgebra_apply (R := K) _).trans rfl

def ssBasis (K : Type) [Field K] (mu : DomWeight n) :
    Module.Basis (Formalism.GradedWeylDivisibility.ssIdx n n mu.natW) K (nablaSq K n mu) :=
  (Module.Basis.span (Formalism.GradedWeylDivisibility.sSBasis K n n mu.natW).choose_spec.1.1).map
    (LinearEquiv.ofEq _ _ (Formalism.GradedWeylDivisibility.sSBasis K n n mu.natW).choose_spec.1.2.1)

theorem ssBasis_coe (mu : DomWeight n) (i : Formalism.GradedWeylDivisibility.ssIdx n n mu.natW) :
    (ssBasis K mu i : MvPolynomial (Fin n × Fin n) K) = ssB K mu.natW i := by
  simp only [ssBasis, ssB, Module.Basis.map_apply, Module.Basis.span_apply]
  rfl

theorem vv_irreducible_unitary :
    ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → Formalism.BasicNotions.DomWeight n) (U : Submodule ℂ (Formalism.L2.DIV.VV ℂ lam)), (∀ g : ι → GL (Fin n) ℂ, (∀ τ, (g τ : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ) → ∀ x ∈ U, Formalism.L2.DIV.rhoK lam g x ∈ U) → U = ⊥ ∨ U = ⊤ := by
  intro ι _ n lam U hU
  refine eq_bot_or_top_of_tensor (G := fun _ => Matrix.unitaryGroup (Fin n) ℂ)
    (fun τ => ssBasis ℂ (lam τ)) (tenMul lam) (bVV ℂ lam) (fun i => ?_)
    (fun τ => smallRep (unitaryIncl n) (lam τ))
    (fun τ => GlobalTheory.ClassFin.span_range_eq_top_of_isIrreducible _ _ _ (isIrreducible_smallRep_unitary n (lam τ)))
    U fun g => ⟨rhoK lam fun τ => unitaryIncl n (g τ), fun f => ?_, hU _ fun τ => (g τ).2⟩
  · apply Subtype.ext
    rw [bVV_coe, tenMul_coe, bVVfun]
    simp only [ssBasis_coe]
  · apply Subtype.ext
    rw [tenMul_coe]
    change actP lam _ (tenMul lam f : Pol ℂ ι n) = _
    rw [tenMul_coe, actTen]
    rfl

end GlobalTheory.CoefIrred
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DirichletLZerosInWindowFiniteAndPosOrder
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DirichletLZerosInWindowFiniteAndPosOrder
noncomputable section

namespace GlobalTheory.Mem.An.ZeroWindow

open Complex DirichletCharacter

theorem analyticOff {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    AnalyticOnNhd ℂ (LFunction χ) ({1}ᶜ : Set ℂ) := by
  refine DifferentiableOn.analyticOnNhd ?_ isOpen_compl_singleton
  intro s hs
  exact (χ.differentiableAt_LFunction s (Or.inl hs)).differentiableWithinAt

theorem exists_entire {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ F 1 ≠ 0 ∧ ∀ s, s ≠ 1 → LFunction χ s = 0 → F s = 0 := by
  by_cases h : χ = 1
  · subst h
    refine ⟨LFunctionTrivChar₁ q, differentiable_LFunctionTrivChar₁ q,
      LFunctionTrivChar₁_apply_one_ne_zero q, fun s hs h0 => ?_⟩
    rw [LFunctionTrivChar₁, Function.update_of_ne hs, LFunctionTrivChar, h0, mul_zero]
  · exact ⟨LFunction χ, differentiable_LFunction h, LFunction_apply_one_ne_zero h,
      fun _ _ h0 => h0⟩

theorem ne_one_of_mem {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {t T : ℝ} {ρ : ℂ}
    (h : ρ ∈ zerosIn χ t T) : ρ ≠ 1 := by
  rintro rfl
  have h2 := h.2.1
  simp at h2

theorem finite_zeros {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t T : ℝ) :
    (zerosIn χ t T).Finite := by
  obtain ⟨F, hF, h1, h0⟩ := exists_entire χ
  have hA : AnalyticOnNhd ℂ F Set.univ := hF.differentiableOn.analyticOnNhd isOpen_univ
  by_contra hinf
  have hinf : (zerosIn χ t T).Infinite := hinf
  have hsub : zerosIn χ t T ⊆ Metric.closedBall (0 : ℂ) (1 + |t| + T) := by
    rintro ρ ⟨h0, h1, h2, -⟩
    rw [mem_closedBall_zero_iff]
    have := Complex.norm_le_abs_re_add_abs_im ρ
    have h3 : |ρ.re| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    have h4 : |ρ.im| ≤ |t| + T := by
      have := abs_sub_abs_le_abs_sub ρ.im t
      linarith
    linarith
  obtain ⟨z, -, hz⟩ := hinf.exists_accPt_of_subset_isCompact (isCompact_closedBall _ _) hsub
  have hfr : ∃ᶠ w in nhdsWithin z {z}ᶜ, F w = 0 := by
    rw [accPt_iff_frequently_nhdsNE] at hz
    exact hz.mono fun w hw => h0 w (ne_one_of_mem hw) hw.2.2.2
  have := hA.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
    (Set.mem_univ z) hfr
  exact h1 (this (Set.mem_univ 1))

theorem order_ne_top {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {ρ : ℂ} (hρ : ρ ≠ 1) :
    analyticOrderAt (LFunction χ) ρ ≠ ⊤ := by
  intro ht
  rw [analyticOrderAt_eq_top] at ht
  have hc : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
  have h2 : (2 : ℂ) ≠ 1 := by norm_num
  have := (analyticOff χ).eqOn_zero_of_preconnected_of_eventuallyEq_zero hc hρ ht
  exact χ.LFunction_ne_zero_of_one_le_re (s := 2) (Or.inr h2) (by simp) (this h2)

theorem one_le_zmult {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {t T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ zerosIn χ t T) : 1 ≤ zmult χ ρ := by
  unfold zmult analyticOrderNatAt
  have h1 := order_ne_top χ (ne_one_of_mem hρ)
  have h2 : analyticOrderAt (LFunction χ) ρ ≠ 0 := by
    rw [analyticOrderAt_ne_zero]
    exact ⟨analyticOff χ ρ (ne_one_of_mem hρ), hρ.2.2.2⟩
  rw [Nat.one_le_iff_ne_zero]
  simp [h1, h2]

theorem finite_and_one_le_zmult : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t T : ℝ),
    (zerosIn χ t T).Finite ∧ ∀ ρ ∈ zerosIn χ t T, 1 ≤ zmult χ ρ :=
  fun _ _ χ t T => ⟨finite_zeros χ t T, fun _ hρ => one_le_zmult χ hρ⟩

end GlobalTheory.Mem.An.ZeroWindow
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DirichletLZerosInWindowFiniteAndPosOrderStatement
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dirichletLZerosInWindow_finite_and_pos_order : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t T : ℝ), (zerosIn χ t T).Finite ∧ ∀ ρ ∈ zerosIn χ t T, 1 ≤ zmult χ ρ := by
  first | exact @GlobalTheory.Mem.An.ZeroWindow.finite_and_one_le_zmult | exact GlobalTheory.Mem.An.ZeroWindow.finite_and_one_le_zmult | (intros; apply GlobalTheory.Mem.An.ZeroWindow.finite_and_one_le_zmult <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KroneckerTwoNegEqJacobiSymTwo
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.JacobiSymNegEqOfThreeModFour
namespace GlobalTheory

theorem jacobiSym_neg_eq_of_three_mod_four (q n : ℕ) (hq : q % 4 = 3) (hn : Odd n) :
    jacobiSym (-(q : ℤ)) n = jacobiSym (n : ℤ) q := by
  have hqo : Odd q := Nat.odd_iff.mpr (by omega)
  have hn2 : n % 2 = 1 := Nat.odd_iff.mp hn
  rw [jacobiSym.neg _ hn]
  have h4 : n % 4 = 1 ∨ n % 4 = 3 := by omega
  rcases h4 with h | h
  · rw [ZMod.χ₄_nat_one_mod_four h, one_mul,
      jacobiSym.quadratic_reciprocity_one_mod_four h hqo]
  · rw [ZMod.χ₄_nat_three_mod_four h,
      jacobiSym.quadratic_reciprocity_three_mod_four hq h]
    ring

end GlobalTheory
end

open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors

namespace GlobalTheory

theorem kroneckerTwo_neg_eq_jacobiSym_two (q : ℕ) (hq : q % 4 = 3) :
    GlobalTheoryTheory.kron2 (-(q : ℤ)) = jacobiSym 2 q := by
  have hodd : Odd q := Nat.odd_iff.mpr (by omega)
  rw [jacobiSym.at_two hodd, ZMod.χ₈_nat_eq_if_mod_eight]
  unfold GlobalTheoryTheory.kron2
  split_ifs <;> omega

theorem kronSym_neg_eq_jacobiSym_and_two :
    (∀ q n : ℕ, q % 4 = 3 → 0 < n → GlobalTheoryTheory.kronSym (-(q : ℤ)) n = jacobiSym (n : ℤ) q) ∧
      ∀ n : ℕ, Odd n → GlobalTheoryTheory.kronSym 2 n = ZMod.χ₈ (n : ZMod 8) := by
  refine ⟨fun q n hq hn => ?_, fun n hn => ?_⟩
  · unfold GlobalTheoryTheory.kronSym
    have hodd : Odd (n / 2 ^ n.factorization 2) := by
      have h := Nat.not_dvd_ordCompl Nat.prime_two hn.ne'
      exact Nat.odd_iff.mpr (by omega)
    have hmul : 2 ^ n.factorization 2 * (n / 2 ^ n.factorization 2) = n :=
      Nat.ordProj_mul_ordCompl_eq_self n 2
    rw [jacobiSym_neg_eq_of_three_mod_four q _ hq hodd, kroneckerTwo_neg_eq_jacobiSym_two q hq,
      ← jacobiSym.pow_left, ← jacobiSym.mul_left]
    congr 1
    rw [mul_comm]
    exact_mod_cast hmul
  · unfold GlobalTheoryTheory.kronSym
    have h0 : n.factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by have := Nat.odd_iff.mp hn; omega)
    rw [h0, pow_zero, pow_zero, Nat.div_one, mul_one, jacobiSym.at_two hn]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumVonMangoldtLeTwoMul
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.An

theorem lcmUpto_le_four_pow_small : ∀ n : ℕ, n ≤ 100 → Nat.lcmUpto n ≤ 4 ^ n := by
  decide +kernel

theorem psi_le_two_mul_small {y : ℝ} (h0 : 0 ≤ y) (h : y ≤ 100) : Chebyshev.psi y ≤ 2 * y := by
  rw [Chebyshev.psi_eq_psi_coe_floor, Chebyshev.psi_eq_log_lcmUpto]
  have hn : ⌊y⌋₊ ≤ 100 := Nat.floor_le_of_le (by exact_mod_cast h)
  have h1 : ((Nat.lcmUpto ⌊y⌋₊ : ℕ) : ℝ) ≤ 4 ^ ⌊y⌋₊ := by
    exact_mod_cast lcmUpto_le_four_pow_small _ hn
  have h2 : (0 : ℝ) < (Nat.lcmUpto ⌊y⌋₊ : ℕ) := by exact_mod_cast Nat.lcmUpto_pos _
  have h3 := Real.log_le_log h2 h1
  rw [Real.log_pow] at h3
  have h4 : Real.log 4 ≤ 2 := by
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_lt_d9
    linarith
  have h5 : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le h0
  have h6 : (0 : ℝ) ≤ (⌊y⌋₊ : ℝ) := Nat.cast_nonneg _
  nlinarith

theorem psi_le_of_le_sqrt {C x : ℝ} (hC : 0 ≤ C) (hx : 1 ≤ x)
    (h : ∀ y : ℝ, 0 ≤ y → y ≤ √x → Chebyshev.psi y ≤ C * y) :
    Chebyshev.psi x ≤ 1.4 * x + 3 * C * √x := by
  have key : ∀ n : ℝ, 2 ≤ n → Chebyshev.psi (x ^ n⁻¹) ≤ C * √x := by
    intro n hn
    have hle : x ^ n⁻¹ ≤ √x := by
      rw [Real.sqrt_eq_rpow, one_div]
      exact Real.rpow_le_rpow_of_exponent_le hx (inv_anti₀ (by norm_num) hn)
    exact (h _ (by positivity) hle).trans (mul_le_mul_of_nonneg_left hle hC)
  have h1 := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
  have h2 := Chebyshev.theta_le_log4_mul_x (x := x) (by linarith)
  have h4 : Real.log 4 ≤ 1.4 := by
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_lt_d9
    linarith
  have h5 : Real.log 4 * x ≤ 1.4 * x := mul_le_mul_of_nonneg_right h4 (by linarith)
  linarith [key 2 le_rfl, key 3 (by norm_num), key 5 (by norm_num)]

theorem psi_le_two_mul {y : ℝ} (h0 : 0 ≤ y) : Chebyshev.psi y ≤ 2 * y := by
  rcases le_total y 100 with h | h
  · exact psi_le_two_mul_small h0 h
  have hs : √y * √y = y := Real.mul_self_sqrt h0
  have h10 : 10 ≤ √y := Real.le_sqrt_of_sq_le (by linarith)
  rcases le_total (√y) 100 with h' | h'
  · have := psi_le_of_le_sqrt (C := 2) (by norm_num) (by linarith : 1 ≤ y)
      (fun z hz hz' => psi_le_two_mul_small hz (hz'.trans h'))
    nlinarith
  · have h4 : Real.log 4 ≤ 2 := by
      have : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      have := Real.log_two_lt_d9
      linarith
    have := psi_le_of_le_sqrt (C := 6) (by norm_num) (by linarith : 1 ≤ y)
      (fun z hz _ => (Chebyshev.psi_le_const_mul_self hz).trans
        (mul_le_mul_of_nonneg_right (by linarith) hz))
    nlinarith

theorem sum_vonMangoldt_le_two_mul : ∀ y : ℝ, 0 ≤ y → ∑ n ∈ Icc 1 ⌊y⌋₊, Λ n ≤ 2 * y := by
  intro y hy
  have h := psi_le_two_mul hy
  rw [Chebyshev.psi] at h
  rwa [show Icc 1 ⌊y⌋₊ = Ioc 0 ⌊y⌋₊ from Finset.Icc_add_one_left_eq_Ioc 0 _]

end GlobalTheory.Mem.An
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormOneIffOfSqrt
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRatAddMulOfMemAdjoin
namespace GlobalTheory.RatCoordsAdjoin

theorem exists_rat_add_mul_of_mem_adjoin {E : Type} [Field E] [NumberField E] (d : ℕ) (s : E)
    (hs : s ^ 2 = -(d : E)) {x : E} (hx : x ∈ IntermediateField.adjoin ℚ ({s} : Set E)) :
    ∃ a b : ℚ, x = (a : E) + (b : E) * s := by
  have halg : IsAlgebraic ℚ s := Algebra.IsAlgebraic.isAlgebraic s
  have hx' : x ∈ Algebra.adjoin ℚ ({s} : Set E) := by
    rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic (F := ℚ) (S := ({s} : Set E))
      (by intro y hy; rw [Set.mem_singleton_iff.mp hy]; exact halg)]
    exact hx
  clear hx
  induction hx' using Algebra.adjoin_induction with
  | mem y hy => exact ⟨0, 1, by rw [Set.mem_singleton_iff.mp hy]; simp⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, b, rfl⟩ := hy
    obtain ⟨c, e, rfl⟩ := hz
    exact ⟨a + c, b + e, by push_cast; ring⟩
  | mul y z _ _ hy hz =>
    obtain ⟨a, b, rfl⟩ := hy
    obtain ⟨c, e, rfl⟩ := hz
    exact ⟨a * c - b * e * d, a * e + b * c, by
      push_cast; linear_combination ((b : E) * (e : E)) * hs⟩

end GlobalTheory.RatCoordsAdjoin
end

open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.An

theorem half_int_coords {E : Type} [Field E] [NumberField E] (d : ℕ) (hd : d.Prime) (h4 : d % 4 = 3)
    (s : E) (hs : s ^ 2 = -(d : E)) (c : E ≃ₐ[ℚ] E) (hc : c s = -s) (a b : ℚ)
    (hy : IsIntegral ℤ ((a : E) + (b : E) * s)) :
    ∃ t u : ℤ, (2 : ℤ) ∣ t - u ∧ 2 * a = t ∧ 2 * b = u := by
  have hcy : IsIntegral ℤ ((a : E) - (b : E) * s) := by
    have := hy.map (c.toRingEquiv.toRingHom.toIntAlgHom)
    simpa [hc, sub_eq_add_neg] using this
  have key : ∀ q : ℚ, IsIntegral ℤ (q : E) → ∃ n : ℤ, q = n := by
    intro q hq
    have h1 : IsIntegral ℤ q := by
      have : (q : E) = algebraMap ℚ E q := by simp
      rw [this] at hq
      exact (isIntegral_algebraMap_iff ).1 hq
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 h1
    exact ⟨n, by simpa using hn.symm⟩
  obtain ⟨t, ht⟩ := key (2 * a) (by
    have e : ((2 * a : ℚ) : E) = ((a : E) + (b : E) * s) + ((a : E) - (b : E) * s) := by
      push_cast; ring
    rw [e]; exact hy.add hcy)
  obtain ⟨n, hn⟩ := key (a ^ 2 + d * b ^ 2) (by
    have e : ((a ^ 2 + d * b ^ 2 : ℚ) : E) = ((a : E) + (b : E) * s) * ((a : E) - (b : E) * s) := by
      push_cast; linear_combination (b : E) ^ 2 * hs
    rw [e]; exact hy.mul hcy)
  have hm : (d : ℚ) * (2 * b) ^ 2 = ((4 * n - t ^ 2 : ℤ) : ℚ) := by
    push_cast; rw [← ht, ← hn]; ring
  obtain ⟨k, hk⟩ : ∃ k : ℤ, (d : ℚ) * (2 * b) = k := by
    have h1 : IsIntegral ℤ (((d : ℚ) * (2 * b)) ^ 2) := by
      have : ((d : ℚ) * (2 * b)) ^ 2 = algebraMap ℤ ℚ (d * (4 * n - t ^ 2)) := by
        rw [eq_intCast, Int.cast_mul, ← hm]; push_cast; ring
      rw [this]; exact isIntegral_algebraMap
    have h2 := IsIntegral.of_pow (by norm_num : 0 < 2) h1
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
    exact ⟨n, by simpa using hn.symm⟩
  have hk2 : k ^ 2 = (d : ℤ) * (4 * n - t ^ 2) := by
    have : (k : ℚ) ^ 2 = (d : ℚ) * ((4 * n - t ^ 2 : ℤ) : ℚ) := by
      rw [← hm, ← hk]; ring
    exact_mod_cast this
  have hdk : (d : ℤ) ∣ k := (Nat.prime_iff_prime_int.1 hd).dvd_of_dvd_pow (hk2 ▸ dvd_mul_right _ _)
  obtain ⟨u, rfl⟩ := hdk
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne_zero
  have hu : 2 * b = u := by
    apply mul_left_cancel₀ hd0
    rw [hk]; push_cast; ring
  refine ⟨t, u, ?_, ht, hu⟩
  have h5 : (d : ℤ) * u ^ 2 = 4 * n - t ^ 2 := by
    rw [hu] at hm; exact_mod_cast hm
  obtain ⟨e, he⟩ : ∃ e : ℤ, (d : ℤ) = 4 * e + 3 := ⟨(d : ℤ) / 4, by omega⟩
  have h6 : (2 : ℤ) ∣ (t - u) ^ 2 := ⟨2 * n - (2 * e + 1) * u ^ 2 - t * u, by
    rw [he] at h5; linear_combination h5⟩
  exact Int.prime_two.dvd_of_dvd_pow h6

theorem exists_rat_coords {E : Type} [Field E] [NumberField E] (d : ℕ)
    (s : E) (hs : s ^ 2 = -(d : E)) {x : E} (hx : x ∈ IntermediateField.adjoin ℚ {s}) :
    ∃ a b : ℚ, x = (a : E) + (b : E) * s :=
  _root_.GlobalTheory.RatCoordsAdjoin.exists_rat_add_mul_of_mem_adjoin d s hs hx

theorem normOne_iff_of_sqrt {E : Type} [Field E] [NumberField E] (d : ℕ) (hd : d.Prime) (h4 : d % 4 = 3)
    (s : E) (hs : s ^ 2 = -(d : E)) (c : E ≃ₐ[ℚ] E) (hc : c s = -s) (M p : ℕ) :
    NormOne d M p ↔ ∃ π : 𝓞 E, (π : E) ∈ IntermediateField.adjoin ℚ {s} ∧ (π : E) * c (π : E) = (p : E) ∧
      (π - 1) ∈ Ideal.span {((M : ℕ) : 𝓞 E)} := by
  have hsK : s ∈ IntermediateField.adjoin ℚ {s} := IntermediateField.mem_adjoin_simple_self ℚ _
  constructor
  · rintro ⟨A, B, hN, ⟨u, hu⟩, ⟨v, hv⟩⟩
    obtain ⟨e, he⟩ : ∃ e : ℤ, (d : ℤ) + 1 = 4 * e := ⟨((d : ℤ) + 1) / 4, by omega⟩
    have heE : (d : E) + 1 = 4 * e := by exact_mod_cast congrArg (Int.cast : ℤ → E) he
    have hω : IsIntegral ℤ ((1 + s) / 2) := by
      refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C e, by monicity!, ?_⟩
      rw [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_C, eq_intCast]
      linear_combination (1 / 4 : E) * hs - (1 / 4 : E) * heE
    let ω : 𝓞 E := ⟨(1 + s) / 2, hω⟩
    have hA : (A : E) = 2 + M * u + 2 * M * v := by
      have : A = 2 + M * u + 2 * M * v := by linear_combination hv + hu
      rw [this]; push_cast; ring
    have hB : (B : E) = M * u := by rw [hu]; push_cast; ring
    have hπ : ((1 + (M : 𝓞 E) * ((v : 𝓞 E) + (u : 𝓞 E) * ω) : 𝓞 E) : E) = ((A : E) + B * s) / 2 := by
      have h0 : algebraMap (𝓞 E) E ω = (1 + s) / 2 := rfl
      change algebraMap (𝓞 E) E _ = _
      simp only [map_add (f := _), map_mul, map_one, map_natCast, map_intCast]
      rw [h0, hA, hB]; ring
    refine ⟨1 + (M : 𝓞 E) * ((v : 𝓞 E) + (u : 𝓞 E) * ω), ?_, ?_, ?_⟩
    · rw [hπ]
      exact div_mem (add_mem (intCast_mem _ _) (mul_mem (intCast_mem _ _) hsK)) (ofNat_mem _ 2)
    · rw [hπ]
      have hNE : (A : E) ^ 2 + d * B ^ 2 = 4 * p := by exact_mod_cast congrArg (Int.cast : ℤ → E) hN
      rw [map_div₀, map_add (f := _), map_mul, map_intCast, map_intCast, hc, map_ofNat]
      linear_combination (1 / 4 : E) * hNE - (B : E) ^ 2 / 4 * hs
    · rw [add_sub_cancel_left]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  · rintro ⟨π, hK, hN, hM⟩
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.1 hM
    have hyE : (π : E) = 1 + M * (y : E) := by
      have : π = 1 + M * y := by linear_combination hy
      rw [this]; push_cast; rfl
    rcases Nat.eq_zero_or_pos M with rfl | hM0
    · rw [hyE] at hN
      simp only [Nat.cast_zero, zero_mul, add_zero, map_one, mul_one] at hN
      have : p = 1 := by exact_mod_cast hN.symm
      exact ⟨2, 0, by simp [this], by simp, by simp⟩
    · have hME : (M : E) ≠ 0 := by exact_mod_cast hM0.ne'
      have hyK : (y : E) ∈ IntermediateField.adjoin ℚ {s} := by
        have : (y : E) = ((π : E) - 1) / M := by rw [hyE]; field_simp; ring
        rw [this]
        exact div_mem (sub_mem hK (one_mem _)) (natCast_mem _ _)
      obtain ⟨a, b, hab⟩ := exists_rat_coords d s hs hyK
      obtain ⟨t, u, ⟨w, hw⟩, ht, hu⟩ := half_int_coords d hd h4 s hs c hc a b (hab ▸ y.isIntegral_coe)
      have htE : 2 * (a : E) = t := by exact_mod_cast congrArg (Rat.cast : ℚ → E) ht
      have huE : 2 * (b : E) = u := by exact_mod_cast congrArg (Rat.cast : ℚ → E) hu
      refine ⟨2 + M * t, M * u, ?_, dvd_mul_right _ _, ⟨w, by linear_combination (M : ℤ) * hw⟩⟩
      rw [hyE, hab] at hN
      simp only [map_add (f := _), map_mul, map_one, map_natCast, map_ratCast, hc] at hN
      have : (2 + M * t : E) ^ 2 + d * (M * u) ^ 2 = 4 * p := by
        rw [← htE, ← huE]
        linear_combination 4 * hN + 4 * (M : E) ^ 2 * (b : E) ^ 2 * hs
      exact_mod_cast this

theorem normOne_iff_host : ∀ (R : Ranks) (H : Host R) (M p : ℕ), NormOne H.d M p ↔ ∃ π : 𝓞 H.E, (π : H.E) ∈ H.K ∧ (π : H.E) * H.conj (π : H.E) = (p : H.E) ∧ (π - 1) ∈ Ideal.span {((M : ℕ) : 𝓞 H.E)} := by
  intro R H M p
  have hs : H.sqrtMinusD ^ 2 = -(H.d : H.E) := H.sqd_sq
  have hc : H.conj H.sqrtMinusD = -H.sqrtMinusD := by
    apply H.φ₀.injective
    have h1 : H.φ₀ H.sqrtMinusD = Complex.I * (Real.sqrt H.d : ℂ) := H.φ₀_mem
    have h2 : H.φ₀ (H.conj H.sqrtMinusD) = starRingEnd ℂ (H.φ₀ H.sqrtMinusD) :=
      H.conjE_apply _ _
    rw [h2, map_neg, h1]
    simp
  exact normOne_iff_of_sqrt H.d H.hyp.2.1 (by have := H.hyp.2.2.2.1; omega) H.sqrtMinusD hs H.conj hc M p

end GlobalTheory.Mem.An
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHFrameDtPackPre
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyHostHeckeCharacterFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyHostHeckeCharacterFrame
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host Classical
open GlobalTheory.Mem.Chr hiding Ideles localIdele diagUnits infIdele HChar IsUnitAt ordF upF aboveF atFin atInf infDiag unif etaInf etaFin aboveInf OverP embPsi PiBar Omg EtaTExists Mu0Exists IsMu0 IsChiPsi IsDelta IsEtaT DeltaExists

namespace GlobalTheory

theorem nonempty_hFrame : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (e : Fin R.m → R.Psi → ℚ), (∀ k, SplitsC H.E (H.g k)) → SplitsC H.E H.pde → SplitsC H.E H.pde' → (∀ j τ, ∃ z : ℤ, e j τ = z) → (∀ j, UpperTheory.MUQ (embPsi H) (e j)) → Nonempty (HFrame H e) := by
  intro R H e hg hp hp' he hs
  obtain ⟨⟨P⟩, ⟨W⟩⟩ := GlobalTheory.nonempty_piBar_and_omg R H
  have hmu : ∀ j : Fin R.m, ∃ χ : HChar H.E, IsMu0 P W (e j) j.1 χ := fun j =>
    GlobalTheory.T.mu0Exists_of_splits_of_integral_of_MUQ R H P W (e j) j.1 hg (he j) (hs j)
  choose mu hmu using hmu
  obtain ⟨eta, heta⟩ := GlobalTheory.T.host_etaTilde_character_exists R H
  obtain ⟨chi, hchi⟩ := GlobalTheory.T.exists_unramified_cmType_heckeChar_on_host R H
  obtain ⟨d, hd⟩ := GlobalTheory.T.host_delta_character_inertial_order_fifteen_exists R H H.pde H.pde_prime H.pde_mod.1 hp
  obtain ⟨d', hd'⟩ := GlobalTheory.T.host_delta_character_inertial_order_fifteen_exists R H H.pde' H.pde'_prime H.pde_mod.2 hp'
  exact ⟨⟨P, W, mu, eta, chi, d, d', hmu, ⟨heta.unitary, heta.unr, heta.res, heta.inf⟩, hchi, hd, hd'⟩⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyHostHeckeCharacterFrameStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host Classical
open GlobalTheory.Mem.Chr hiding Ideles localIdele diagUnits infIdele HChar IsUnitAt ordF upF aboveF atFin atInf infDiag unif etaInf etaFin aboveInf OverP embPsi PiBar Omg EtaTExists Mu0Exists IsMu0 IsChiPsi IsDelta IsEtaT DeltaExists
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_hostHeckeCharacterFrame : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (e : Fin R.m → R.Psi → ℚ), (∀ k, SplitsC H.E (H.g k)) → SplitsC H.E H.pde → SplitsC H.E H.pde' → (∀ j τ, ∃ z : ℤ, e j τ = z) → (∀ j, UpperTheory.MUQ (embPsi H) (e j)) → Nonempty (HFrame H e) := by
  first | exact @GlobalTheory.nonempty_hFrame | exact GlobalTheory.nonempty_hFrame | (intros; apply GlobalTheory.nonempty_hFrame <;> assumption)
end
end

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host Classical
open GlobalTheory.Mem.Chr hiding Ideles localIdele diagUnits infIdele HChar IsUnitAt ordF upF aboveF atFin atInf infDiag unif etaInf etaFin aboveInf OverP embPsi PiBar Omg EtaTExists Mu0Exists IsMu0 IsChiPsi IsDelta IsEtaT DeltaExists

namespace GlobalTheory.Mem.Pre

variable (B : Pre)

theorem splitsC_level {p : ℕ} (hp : p ∈ B.host.levelPrimes) : SplitsC B.host.E p :=
  (GlobalTheory.HostSplit.split_of_one_mod B.R B.host p (B.level_cond p hp).1 (B.level_cond p hp).2).1

theorem splitsC_g (k : Fin 2) : SplitsC B.host.E (B.host.g k) := B.splitsC_level (B.host.g_level k)

theorem splitsC_pde : SplitsC B.host.E B.host.pde := B.splitsC_level B.host.pde_level.1

theorem splitsC_pde' : SplitsC B.host.E B.host.pde' := B.splitsC_level B.host.pde_level.2

def EvenExp : Prop := ∀ j, UpperTheory.MUQ (embPsi B.host) (fun τ : B.R.Psi => (B.hc τ).e j)

theorem nonempty_hframe (h : B.EvenExp) : Nonempty (HFrame B.host fun j τ => (B.hc τ).e j) :=
  GlobalTheory.T.nonempty_hostHeckeCharacterFrame B.R B.host _ B.splitsC_g B.splitsC_pde B.splitsC_pde' (fun j τ => (B.hc τ).e_int j) h

end GlobalTheory.Mem.Pre

namespace GlobalTheory.Mem.Chr

end GlobalTheory.Mem.Chr

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemIdSOfResSEqZero
open NumberField IsDedekindDomain Formalism.UG
open scoped TensorProduct

namespace GlobalTheory.SplitResidue

open Formalism.L2.DIV HeightOneSpectrum

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mem_maximalIdeal_iff (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletionIntegers F) :
    x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) ↔
      Valued.v (x : v.adicCompletion F) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact Valuation.Integer.not_isUnit_iff_valuation_lt_one (x := (x : Valued.integer (v.adicCompletion F)))

theorem integral_image (v : HeightOneSpectrum (𝓞 F))
    (φ : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F) (b : 𝓞 E) :
    φ ((algebraMap (𝓞 E) E b) ⊗ₜ[F] (1 : v.adicCompletion F)) ∈ v.adicCompletionIntegers F := by
  have h0 : IsIntegral ℤ b := Algebra.IsIntegral.isIntegral b
  let ψ : 𝓞 E →+* v.adicCompletion F :=
    φ.comp ((inclE (F := F) (v.adicCompletion F)).comp (algebraMap (𝓞 E) E))
  have h1 : IsIntegral (v.adicCompletionIntegers F) (ψ b) :=
    IsIntegral.map_of_comp_eq (Int.castRingHom _) ψ (RingHom.ext_int _ _) h0
  exact (adicCompletionIntegers.integers F v).mem_of_integral h1

theorem comp_mem (v : HeightOneSpectrum (𝓞 F))
    (φ : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F)
    (hφ : ∀ a : v.adicCompletion F, φ ((1 : E) ⊗ₜ[F] a) = a) (s : Formalism.L2.Herm.intAf F E) :
    φ (prV (E := E) v s.1) ∈ v.adicCompletionIntegers F := by
  have hle : Formalism.L2.Herm.intAf F E ≤
      Subring.comap (φ.comp (prV (E := E) v)) (v.adicCompletionIntegers F).toSubring := by
    refine Subring.closure_le.2 ?_
    rintro x (⟨b, rfl⟩ | ⟨y, rfl⟩)
    · obtain ⟨b0, hb0⟩ := b.2
      show φ (prV (E := E) v ((b : E) ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F))) ∈ v.adicCompletionIntegers F
      rw [Formalism.UG.P.afsplit_prV_tmul, ← hb0]
      exact integral_image v φ b0
    · show φ (prV (E := E) v ((1 : E) ⊗ₜ[F] (y : Formalism.L2.Herm.Af F))) ∈ v.adicCompletionIntegers F
      rw [Formalism.UG.P.afsplit_prV_tmul, hφ]
      exact y.2 v
  exact hle s.2

theorem mem_idS_of_resS_eq_zero (w : HeightOneSpectrum (𝓞 E)) {t : Formalism.L2.Herm.intAf F E}
    (h : resS F w t = 0) : t ∈ idS F w.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  unfold resS at h
  rw [RingHom.comp_apply] at h
  exact (map_eq_zero_iff _ (RingEquiv.injective _)).1 h

theorem exists_residue_equiv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    (φ : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F) (p : 𝓞 E),
    (∀ a : v.adicCompletion F, φ ((1 : E) ⊗ₜ[F] a) = a) →
    Valued.v (φ (inclE (F := F) (v.adicCompletion F) (p : E))) < 1 →
    (∀ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) = v → p ∈ P.asIdeal → P = w) →
    ∃ (ρ : Formalism.L2.Herm.intAf F E →+* v.adicCompletionIntegers F)
      (e : (𝓞 E ⧸ w.asIdeal) ≃+* Formalism.L2.Forms.kv F v),
      (∀ s, ((ρ s : v.adicCompletionIntegers F) : v.adicCompletion F) = φ (prV (E := E) v s.1)) ∧
      ∀ s, IsLocalRing.residue _ (ρ s) = e (Formalism.L2.DIV.resS F w s) := by
  intro F E _ _ _ _ _ v w φ p hφ hp hw
  let ρ : Formalism.L2.Herm.intAf F E →+* v.adicCompletionIntegers F :=
    (φ.comp ((prV (E := E) v).comp (Formalism.L2.Herm.intAf F E).subtype)).codRestrict
      (v.adicCompletionIntegers F) (fun s => comp_mem v φ hφ s)
  have hρ : ∀ s, ((ρ s : v.adicCompletionIntegers F) : v.adicCompletion F) = φ (prV (E := E) v s.1) :=
    fun _ => rfl
  let r : Formalism.L2.Herm.intAf F E →+* Formalism.L2.Forms.kv F v := (IsLocalRing.residue _).comp ρ
  let g : 𝓞 E →+* Formalism.L2.Forms.kv F v := r.comp (oToS F E)
  have hg0 : ∀ b : 𝓞 E, Valued.v (φ (inclE (F := F) (v.adicCompletion F) (b : E))) < 1 → g b = 0 := by
    intro b hb
    show IsLocalRing.residue _ (ρ (oToS F E b)) = 0
    rw [IsLocalRing.residue_eq_zero_iff, mem_maximalIdeal_iff, hρ]
    exact hb
  have hv : ∀ x ∈ v.asIdeal, g (algebraMap (𝓞 F) (𝓞 E) x) = 0 := by
    intro x hx
    refine hg0 _ ?_
    have e1 : ((algebraMap (𝓞 F) (𝓞 E) x : 𝓞 E) : E) = algebraMap F E (algebraMap (𝓞 F) F x) := by
      show algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) x) = _
      rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    have e2 : inclE (F := F) (v.adicCompletion F) (algebraMap F E (algebraMap (𝓞 F) F x)) =
        (1 : E) ⊗ₜ[F] (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F x)) := by
      show (algebraMap F E (algebraMap (𝓞 F) F x)) ⊗ₜ[F] (1 : v.adicCompletion F) = _
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one]
    rw [e1, e2, hφ]
    refine lt_of_eq_of_lt (valuedAdicCompletion_eq_valuation' v _) ?_
    exact (valuation_lt_one_iff_mem v x).2 hx
  have hne : RingHom.ker g ≠ ⊥ := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
    intro hb
    have h1 : algebraMap (𝓞 F) (𝓞 E) x ∈ RingHom.ker g := hv x hx
    rw [hb, Ideal.mem_bot] at h1
    exact hx0 (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E) (h1.trans (map_zero _).symm))
  let P : HeightOneSpectrum (𝓞 E) := ⟨RingHom.ker g, RingHom.ker_isPrime g, hne⟩
  have hunder : P.under (𝓞 F) = v := by
    refine HeightOneSpectrum.ext (v.isMaximal.eq_of_le (P.under (𝓞 F)).isPrime.ne_top ?_).symm
    intro x hx
    exact hv x hx
  have hk : RingHom.ker g = w.asIdeal := congrArg HeightOneSpectrum.asIdeal (hw P hunder (hg0 p hp))
  have hz : idS F w.asIdeal ≤ RingHom.ker r := by
    refine Ideal.map_le_iff_le_comap.2 fun a ha => ?_
    rw [← hk] at ha
    exact ha
  have hfac : ∀ s (b : 𝓞 E), resS F w s = Ideal.Quotient.mk w.asIdeal b → r s = g b := by
    intro s b h
    have h0 : resS F w (s - oToS F E b) = 0 := by rw [map_sub, resS_oToS, h, sub_self]
    have h1 : r (s - oToS F E b) = 0 := hz (mem_idS_of_resS_eq_zero w h0)
    rw [map_sub] at h1
    exact sub_eq_zero.1 h1
  have hs : Function.Surjective g := by
    intro κ
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective κ
    let s : Formalism.L2.Herm.intAf F E := ⟨(1 : E) ⊗ₜ[F] Formalism.UG.P.afsplitI v (a : v.adicCompletion F),
      Subring.subset_closure (Or.inr ⟨⟨_, Formalism.UG.P.afsplitI_mem_intAd v _ a.2⟩, rfl⟩)⟩
    have hρs : ρ s = a := Subtype.ext (by
      rw [hρ]
      show φ (prV (E := E) v ((1 : E) ⊗ₜ[F] Formalism.UG.P.afsplitI v (a : v.adicCompletion F))) = _
      rw [Formalism.UG.P.afsplit_prV_tmul, Formalism.UG.P.afsplitI_self, hφ])
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (resS F w s)
    refine ⟨b, (hfac s b hb.symm).symm.trans ?_⟩
    show IsLocalRing.residue _ (ρ s) = _
    rw [hρs]
  refine ⟨ρ, (Ideal.quotEquivOfEq hk.symm).trans (RingHom.quotientKerEquivOfSurjective hs), hρ, ?_⟩
  intro s
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (resS F w s)
  rw [← hb]
  exact hfac s b hb.symm

end GlobalTheory.SplitResidue
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsNormEqOfNcardPlacesOver
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors

namespace GlobalTheory.HostSplit

theorem absNorm_eq_of_ncard_placesOver (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] {p : ℕ}
    (hp : p.Prime) (h : (placesOver E p).ncard = Module.finrank ℚ E) :
    ∀ v ∈ placesOver E p, Ideal.absNorm v.asIdeal = p := by
  intro v hv
  have : IsGaloisGroup (E ≃ₐ[ℚ] E) ℤ (𝓞 E) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ E
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have hPp := v.isPrime
  have hlo : v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := by
    refine ⟨hmax.eq_of_le (Ideal.IsPrime.under ℤ v.asIdeal).ne_top ?_⟩
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show algebraMap ℤ (𝓞 E) ((p : ℕ) : ℤ) ∈ v.asIdeal
    rw [map_natCast]
    exact hv
  have hf := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (Ideal.span {(p : ℤ)}) (𝓞 E)
    (E ≃ₐ[ℚ] E)
  rw [← ncard_placesOver E hp, h, IsGalois.card_aut_eq_finrank,
    Ideal.inertiaDegIn_eq_inertiaDeg (Ideal.span {(p : ℤ)}) v.asIdeal (E ≃ₐ[ℚ] E)] at hf
  have hpos : 0 < Module.finrank ℚ E := Module.finrank_pos
  have h1 := Nat.eq_of_mul_eq_mul_left hpos (hf.trans (mul_one _).symm)
  have h2 := Nat.eq_one_of_mul_eq_one_left h1
  have h3 := Ideal.absNorm_pow_inertiaDeg (Ideal.span {(p : ℤ)}) v.asIdeal
  rw [h2, pow_one] at h3
  rw [← h3]
  simp

theorem split_completely_of_modEq_one : ∀ (R : Ranks) (H : Host R) (p : ℕ), p.Prime →
    p ≡ 1 [MOD H.QS * H.q * H.d] →
    (placesOver H.E p).ncard = Module.finrank ℚ H.E ∧ H.cls p = PrimeClass.splitK ∧
      ∀ v ∈ placesOver H.E p, Ideal.absNorm v.asIdeal = p := by
  intro R H p hp hc
  have hn : 0 < H.QS := H.QS_pos
  have hq : 0 < H.q := H.hyp.1.pos
  have hd : 1 < H.d := H.hyp.2.1.one_lt
  have hlt : 1 < H.QS * H.q * H.d := by
    have : 0 < H.QS * H.q := by positivity
    nlinarith
  have hm : p % (H.QS * H.q * H.d) = 1 := by
    rw [Nat.ModEq] at hc
    rw [hc, Nat.mod_eq_of_lt hlt]
  obtain ⟨h1, h2⟩ := split_of_one_mod R H p hp hm
  have hG : IsGalois ℚ H.E := H.galois
  exact ⟨h1, h2, absNorm_eq_of_ncard_placesOver H.E hp h1⟩

end GlobalTheory.HostSplit
end
