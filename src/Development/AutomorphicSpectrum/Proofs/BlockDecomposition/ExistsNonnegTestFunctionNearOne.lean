module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdConsA

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsNonnegTestFunctionNearOne
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsNonnegTestFunctionNearOne
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.SmoothRep

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def hsq (x : Lie E a) : ℝ :=
  ∑ i, ∑ j, ∑ w, ‖(Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2

theorem hsq_nonneg (x : Lie E a) : 0 ≤ hsq x :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

theorem sq_le_hsq (x : Lie E a) (i j : Fin a) (w : InfinitePlace E) :
    ‖(Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2 ≤ hsq x := by
  have h1 : ‖(Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2 ≤
      ∑ w, ‖(Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2 :=
    Finset.single_le_sum (f := fun w => ‖(Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2)
      (fun _ _ => by positivity) (Finset.mem_univ w)
  have h2 : ∑ w, ‖(Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2 ≤
      ∑ j, ∑ w, ‖(Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2 :=
    Finset.single_le_sum (f := fun j => ∑ w, ‖(Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ j)
  have h3 : ∑ j, ∑ w, ‖(Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2 ≤ hsq x :=
    Finset.single_le_sum (f := fun i => ∑ j, ∑ w, ‖(Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ i)
  exact h1.trans (h2.trans h3)

theorem hsq_oneL : hsq (oneL E a) = 0 := by
  simp [hsq, oneL, toL]

theorem dist_oneL_lt {x : Lie E a} {δ : ℝ} (hδ : 0 < δ) (h : hsq x < δ ^ 2) : dist x (oneL E a) < δ := by
  refine (dist_pi_lt_iff hδ).2 fun i => (dist_pi_lt_iff hδ).2 fun j => (dist_pi_lt_iff hδ).2 fun w => ?_
  have h1 := (sq_le_hsq x i j w).trans_lt h
  rw [dist_eq_norm]
  exact lt_of_pow_lt_pow_left₀ 2 hδ.le h1

theorem contDiff_hsq : ContDiff ℝ ∞ (hsq : Lie E a → ℝ) := by
  unfold hsq
  refine ContDiff.sum fun i _ => ContDiff.sum fun j _ => ContDiff.sum fun w _ => ContDiff.norm_sq ℝ ?_
  change ContDiff ℝ ∞ fun x : Lie E a => x i j w - (1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w
  fun_prop

theorem ofReal_hsq (x : Lie E a) :
    (hsq x : ℂ) = ∑ w, Matrix.trace ((Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E)) *
      star (Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E))) w := by
  simp only [hsq, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.star_apply, Finset.sum_apply, Pi.mul_apply,
    Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow, Complex.star_def, Complex.mul_conj']
  refine Eq.trans ?_ Finset.sum_comm
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Eq.trans ?_ Finset.sum_comm
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun w _ => rfl

theorem hsq_conj (k : Kinf E a) (x : Lie E a) : hsq (toL (k.1 * Matrix.of x * star k.1)) = hsq x := by
  apply Complex.ofReal_injective
  rw [ofReal_hsq, ofReal_hsq]
  have hk : k.1 * star k.1 = 1 := Matrix.mem_unitaryGroup_iff.1 k.2
  have hk' : star k.1 * k.1 = 1 := Matrix.mem_unitaryGroup_iff'.1 k.2
  set Y : Matrix (Fin a) (Fin a) (Cinf E) := Matrix.of x - 1 with hY
  have e1 : (Matrix.of (toL (k.1 * Matrix.of x * star k.1)) - 1 : Matrix (Fin a) (Fin a) (Cinf E)) = k.1 * Y * star k.1 := by
    rw [hY, mul_sub, sub_mul, mul_one, hk]
    rfl
  have e2 : Matrix.trace ((k.1 * Y * star k.1) * star (k.1 * Y * star k.1)) = Matrix.trace (Y * star Y) := by
    have : (k.1 * Y * star k.1) * star (k.1 * Y * star k.1) = k.1 * ((Y * star Y) * star k.1) := by
      simp only [star_mul, star_star]
      calc k.1 * Y * star k.1 * (k.1 * (star Y * star k.1))
          = k.1 * Y * (star k.1 * k.1) * (star Y * star k.1) := by simp only [mul_assoc]
        _ = k.1 * ((Y * star Y) * star k.1) := by rw [hk']; simp only [mul_one, mul_assoc]
    rw [this, Matrix.trace_mul_comm, mul_assoc, hk', mul_one]
  rw [e1, e2]

end GlobalTheory.CompanionTheory.SmoothRep

namespace GlobalTheory.CompanionTheory.SmoothRep


attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
theorem val_image_mem_nhds_one {E : Type} [Field E] [NumberField E] {a : ℕ} {N : Set (GL (Fin a) (Cinf E))} (hN : N ∈ 𝓝 1) :
    (Units.val '' N) ∈ 𝓝 (1 : Matrix (Fin a) (Fin a) (Cinf E)) := by
  letI : NormedAddCommGroup (Matrix (Fin a) (Fin a) (Cinf E)) := Matrix.linftyOpNormedAddCommGroup
  letI : NormedSpace ℝ (Matrix (Fin a) (Fin a) (Cinf E)) := Matrix.linftyOpNormedSpace
  letI : NormedRing (Matrix (Fin a) (Fin a) (Cinf E)) := Matrix.linftyOpNormedRing
  haveI : CompleteSpace (Matrix (Fin a) (Fin a) (Cinf E)) := FiniteDimensional.complete ℝ _
  exact (Units.isOpenEmbedding_val (R := Matrix (Fin a) (Fin a) (Cinf E))).isOpenMap.image_mem_nhds hN

theorem exists_bump_conjInv : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (N : Set (GL (Fin a) (Cinf E))), N ∈ 𝓝 1 → ∃ β₀ : Lie E a → ℝ, 0 ≤ β₀ ∧ 0 < β₀ (oneL E a) ∧
      IsTest (fun x => (β₀ x : ℂ)) ∧ ConjInv (fun x => (β₀ x : ℂ)) ∧ ∀ x, β₀ x ≠ 0 → ∃ y ∈ N, toL y.val = x := by
  intro E _ _ _ a N hN
  have h := val_image_mem_nhds_one hN
  have e : (toL '' (Units.val '' N) : Set (Lie E a)) = Units.val '' N := Set.image_id _
  have hV : (toL '' (Units.val '' N) : Set (Lie E a)) ∈ 𝓝 (oneL E a) := by
    rw [e]; exact h
  obtain ⟨δ, hδ, hb⟩ := Metric.mem_nhds_iff.1 hV
  have hδ2 : 0 < δ ^ 2 := by positivity
  let f : ContDiffBump (0 : ℝ) := ⟨δ ^ 2 / 4, δ ^ 2 / 2, by positivity, by linarith⟩
  have hsupp : ∀ x : Lie E a, f (hsq x) ≠ 0 → hsq x < δ ^ 2 / 2 := fun x hx => by
    have : hsq x ∈ Function.support f := hx
    rw [f.support_eq, Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg (hsq_nonneg x)] at this
    exact this
  have hmem : ∀ x : Lie E a, hsq x ≤ δ ^ 2 / 2 → ∃ y ∈ N, toL y.val = x := fun x hx => by
    have : x ∈ Metric.ball (oneL E a) δ := dist_oneL_lt hδ (by linarith)
    obtain ⟨_, ⟨y, hy, rfl⟩, rfl⟩ := hb this
    exact ⟨y, hy, rfl⟩
  have hKc : IsClosed {x : Lie E a | hsq x ≤ δ ^ 2 / 2} :=
    isClosed_le contDiff_hsq.continuous continuous_const
  have hts : tsupport (fun x => (f (hsq x) : ℂ)) ⊆ {x : Lie E a | hsq x ≤ δ ^ 2 / 2} :=
    closure_minimal (fun x hx => (hsupp x (fun h0 => hx (by simp [h0]))).le) hKc
  have hKb : {x : Lie E a | hsq x ≤ δ ^ 2 / 2} ⊆ Metric.closedBall (oneL E a) δ := fun x hx =>
    (dist_oneL_lt hδ (by simp only [Set.mem_setOf_eq] at hx; linarith)).le
  refine ⟨fun x => f (hsq x), fun x => f.nonneg, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · show 0 < f (hsq (oneL E a))
    rw [hsq_oneL]
    exact f.pos_of_mem_ball (Metric.mem_ball_self f.rOut_pos)
  · exact Complex.ofRealCLM.contDiff.comp (f.contDiff.comp contDiff_hsq)
  · exact (isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _) (hts.trans hKb)
  · intro x hx
    obtain ⟨y, _, rfl⟩ := hmem x (hts hx)
    exact y.isUnit
  · intro k x
    show (f (hsq (toL (k.1 * Matrix.of x * star k.1))) : ℂ) = f (hsq x)
    rw [hsq_conj]
  · exact fun x hx => hmem x (hsupp x hx).le

end GlobalTheory.CompanionTheory.SmoothRep
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsNonnegTestFunctionNearOneStatement
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonneg_test_function_near_one : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (N : Set (GL (Fin a) (Cinf E))), N ∈ 𝓝 1 → ∃ β₀ : Lie E a → ℝ, 0 ≤ β₀ ∧ 0 < β₀ (oneL E a) ∧ IsTest (fun x => (β₀ x : ℂ)) ∧ ConjInv (fun x => (β₀ x : ℂ)) ∧ ∀ x, β₀ x ≠ 0 → ∃ y ∈ N, toL y.val = x := by
  first | exact @GlobalTheory.CompanionTheory.SmoothRep.exists_bump_conjInv | exact GlobalTheory.CompanionTheory.SmoothRep.exists_bump_conjInv | (intros; apply GlobalTheory.CompanionTheory.SmoothRep.exists_bump_conjInv <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubquotientOfExtension
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubquotientOfExtension
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.CompanionTheory.BZNuPair

namespace GlobalTheory.CompanionTheory.SubquotExt

theorem isSubquotient_sub_or_quot :
    ∀ (G V W : Type) [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (A B : Subrepresentation ρ), A ≤ B → σ.IsIrreducible → IsSubquotient σ B.toRepresentation →
    IsSubquotient σ A.toRepresentation ∨ IsSubquotient σ (subQuot B A) := by
  intro G V W _ _ _ _ _ ρ σ A B hAB hσ hB
  haveI : IsSimpleOrder (Subrepresentation σ) := hσ
  unfold GlobalTheory.SmGL.IsSubquotient at hB ⊢
  obtain ⟨S, f, hf⟩ := hB
  let P : Submodule ℂ S.toSubmodule :=
    (A.toSubmodule.comap B.toSubmodule.subtype).comap S.toSubmodule.subtype
  have hNinv : ∀ (g : G) ⦃w : W⦄, w ∈ P.map f.toLinearMap → σ g w ∈ P.map f.toLinearMap := by
    intro g w hw
    rw [Submodule.mem_map] at hw ⊢
    obtain ⟨s, hs, rfl⟩ := hw
    have hs' : ((s : B.toSubmodule) : V) ∈ A.toSubmodule := hs
    refine ⟨S.toRepresentation g s, A.apply_mem_toSubmodule g hs', ?_⟩
    exact f.isIntertwining _ _ g s
  let N : Subrepresentation σ := ⟨P.map f.toLinearMap, hNinv⟩
  let Z : Subrepresentation σ := ⟨⊥, by
    intro g w hw
    rw [Submodule.mem_bot] at hw ⊢
    rw [hw, map_zero]⟩
  let Fu : Subrepresentation σ := ⟨⊤, by
    intro g w _
    exact Submodule.mem_top⟩
  rcases IsSimpleOrder.eq_bot_or_eq_top N with hN | hN
  · right
    have hle : N ≤ Z := by
      rw [hN]
      exact bot_le
    have hfP : P ≤ LinearMap.ker f.toLinearMap := by
      intro s hs
      have h0 : f.toLinearMap s ∈ (⊥ : Submodule ℂ W) := hle (Submodule.mem_map_of_mem hs)
      exact LinearMap.mem_ker.2 ((Submodule.mem_bot ℂ).1 h0)
    let A' : Submodule ℂ B.toSubmodule := A.toSubmodule.comap B.toSubmodule.subtype
    have hQ : ∀ (g : G) (b : B.toSubmodule), GlobalTheory.SmGL.subQuot B A g (A'.mkQ b) =
        A'.mkQ (B.toRepresentation g b) := by
      intro g b
      first
      | rfl
      | (unfold GlobalTheory.SmGL.subQuot
         rw [Representation.quotient_apply]
         rfl)
    have hSinv : ∀ (g : G) ⦃x : B.toSubmodule ⧸ A'⦄, x ∈ S.toSubmodule.map A'.mkQ →
        GlobalTheory.SmGL.subQuot B A g x ∈ S.toSubmodule.map A'.mkQ := by
      intro g x hx
      rw [Submodule.mem_map] at hx ⊢
      obtain ⟨b, hb, rfl⟩ := hx
      exact ⟨B.toRepresentation g b, S.apply_mem_toSubmodule g hb, (hQ g b).symm⟩
    let S'' : Subrepresentation (GlobalTheory.SmGL.subQuot B A) := ⟨S.toSubmodule.map A'.mkQ, hSinv⟩
    let ψ0 : S.toSubmodule →ₗ[ℂ] (S.toSubmodule.map A'.mkQ) :=
      LinearMap.codRestrict _ (A'.mkQ ∘ₗ S.toSubmodule.subtype) (fun s => Submodule.mem_map_of_mem s.2)
    have hPker : P ≤ LinearMap.ker ψ0 := by
      intro s hs
      have hs' : (s : B.toSubmodule) ∈ A' := hs
      rw [LinearMap.mem_ker]
      exact Subtype.ext ((Submodule.Quotient.mk_eq_zero A').2 hs')
    have hkerP : LinearMap.ker ψ0 ≤ P := by
      intro s hs
      rw [LinearMap.mem_ker] at hs
      have h2 : (Submodule.Quotient.mk (s : B.toSubmodule) : B.toSubmodule ⧸ A') = 0 := congrArg Subtype.val hs
      exact (Submodule.Quotient.mk_eq_zero A').1 h2
    have hinj : Function.Injective (P.liftQ ψ0 hPker) :=
      LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot P ψ0 hPker hkerP)
    have hsurj : Function.Surjective (P.liftQ ψ0 hPker) := by
      intro x
      obtain ⟨y, hy⟩ := x
      rw [Submodule.mem_map] at hy
      obtain ⟨b, hb, rfl⟩ := hy
      exact ⟨Submodule.Quotient.mk ⟨b, hb⟩, rfl⟩
    let e := LinearEquiv.ofBijective (P.liftQ ψ0 hPker) ⟨hinj, hsurj⟩
    let F'' : (S.toSubmodule.map A'.mkQ) →ₗ[ℂ] W := P.liftQ f.toLinearMap hfP ∘ₗ e.symm.toLinearMap
    have key : ∀ s, F'' (ψ0 s) = f s := by
      intro s
      have he : ψ0 s = e (Submodule.Quotient.mk s) := rfl
      show P.liftQ f.toLinearMap hfP (e.symm (ψ0 s)) = f s
      rw [he, LinearEquiv.symm_apply_apply]
      rfl
    have hrep : ∀ (g : G) (s : S.toSubmodule), S''.toRepresentation g (ψ0 s) = ψ0 (S.toRepresentation g s) :=
      fun g s => Subtype.ext (hQ g s)
    have hψ0 : ∀ x : S.toSubmodule.map A'.mkQ, ∃ s, ψ0 s = x := by
      intro x
      obtain ⟨y, rfl⟩ := hsurj x
      obtain ⟨s, rfl⟩ := Submodule.mkQ_surjective P y
      exact ⟨s, rfl⟩
    let f'' : S''.toRepresentation.IntertwiningMap σ := ⟨F'', fun g => LinearMap.ext fun x => by
      obtain ⟨s, rfl⟩ := hψ0 x
      show F'' (S''.toRepresentation g (ψ0 s)) = σ g (F'' (ψ0 s))
      rw [hrep, key, key]
      exact f.isIntertwining _ _ g s⟩
    refine ⟨S'', f'', fun w => ?_⟩
    obtain ⟨s, rfl⟩ := hf w
    exact ⟨ψ0 s, key s⟩
  · left
    have hge : Fu ≤ N := by
      rw [hN]
      exact le_top
    have hAB' : A.toSubmodule ≤ B.toSubmodule := fun x hx => hAB hx
    have hS'inv : ∀ (g : G) ⦃a : A.toSubmodule⦄, a ∈ S.toSubmodule.comap (Submodule.inclusion hAB') →
        A.toRepresentation g a ∈ S.toSubmodule.comap (Submodule.inclusion hAB') := by
      intro g a ha
      exact S.apply_mem_toSubmodule g ha
    let S' : Subrepresentation A.toRepresentation := ⟨S.toSubmodule.comap (Submodule.inclusion hAB'), hS'inv⟩
    let r : (S.toSubmodule.comap (Submodule.inclusion hAB')) →ₗ[ℂ] S.toSubmodule :=
      (Submodule.inclusion hAB').restrict (fun a ha => ha)
    let f' : S'.toRepresentation.IntertwiningMap σ := ⟨f.toLinearMap ∘ₗ r, fun g => LinearMap.ext fun x => by
      show f.toLinearMap (r (S'.toRepresentation g x)) = σ g (f.toLinearMap (r x))
      exact f.isIntertwining _ _ g (r x)⟩
    refine ⟨S', f', fun w => ?_⟩
    have hw : w ∈ P.map f.toLinearMap := hge (Submodule.mem_top : w ∈ (⊤ : Submodule ℂ W))
    rw [Submodule.mem_map] at hw
    obtain ⟨s, hs, rfl⟩ := hw
    have hs' : ((s : B.toSubmodule) : V) ∈ A.toSubmodule := hs
    have ha : (⟨((s : B.toSubmodule) : V), hs'⟩ : A.toSubmodule) ∈ S.toSubmodule.comap (Submodule.inclusion hAB') := by
      first
      | exact s.2
      | simpa using s.2
    exact ⟨⟨⟨((s : B.toSubmodule) : V), hs'⟩, ha⟩, rfl⟩

end GlobalTheory.CompanionTheory.SubquotExt

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubquotientOfExtensionStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.CompanionTheory.BZNuPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_subquotient_of_extension : ∀ (G V W : Type) [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (A B : Subrepresentation ρ), A ≤ B → σ.IsIrreducible → IsSubquotient σ B.toRepresentation →
    IsSubquotient σ A.toRepresentation ∨ IsSubquotient σ (subQuot B A) := by
  first | exact @GlobalTheory.CompanionTheory.SubquotExt.isSubquotient_sub_or_quot | exact GlobalTheory.CompanionTheory.SubquotExt.isSubquotient_sub_or_quot | (intros; apply GlobalTheory.CompanionTheory.SubquotExt.isSubquotient_sub_or_quot <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerSubquotientEquiv
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerTwoBlockIntertwinersSpan
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerTwoBlockIntertwinersSpan
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir GlobalTheory.CompanionTheory.BZNuPair

noncomputable section

namespace GlobalTheory.CompanionTheory.BZNuPair

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def whitFirstLin (ψ : AddChar k Circle) (d : Fin 2 → ℕ) {X : Fin 2 → Type}
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a))
    (v : ∀ a, X a) : X 0 →ₗ[ℂ] (PiTensorProduct ℂ X ⧸ whitKer ψ d (piTensor ρ)) :=
  (whitKer ψ d (piTensor ρ)).mkQ ∘ₗ (PiTensorProduct.tprod ℂ).toLinearMap v 0

theorem whitFirstLin_apply (ψ : AddChar k Circle) (d : Fin 2 → ℕ) {X : Fin 2 → Type}
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a))
    (v : ∀ a, X a) (x : X 0) :
    whitFirstLin ψ d ρ v x = Submodule.Quotient.mk (PiTensorProduct.tprod ℂ (Function.update v 0 x)) := rfl

def whitFirstMap (ψ : AddChar k Circle) (d : Fin 2 → ℕ) {X : Fin 2 → Type}
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a))
    (v : ∀ a, X a) : (ρ 0).IntertwiningMap (whit2 ψ d (piTensor ρ)) :=
  .mk (whitFirstLin ψ d ρ v) (fun g => by
    ext x
    have h : ∀ a, Function.update v 0 (ρ 0 g x) a = ρ a (firstEmb d g a) (Function.update v 0 x a) :=
      Fin.forall_fin_two.2 ⟨by simp [firstEmb], by simp [firstEmb]⟩
    simp only [LinearMap.comp_apply, whitFirstLin_apply, whit2_mk, piTensor_tprod]
    rw [funext h])

theorem whit_iSup_range_eq_top : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (d : Fin 2 → ℕ) (X : Fin 2 → Type)
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)),
    ⨆ f : (ρ 0).IntertwiningMap (whit2 ψ d (piTensor ρ)), LinearMap.range f.toLinearMap = ⊤ := by
  intro k _ _ _ _ ψ d X _ _ ρ
  rw [eq_top_iff]
  rintro y -
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    have hmem : Submodule.Quotient.mk (PiTensorProduct.tprod ℂ v) ∈
        ⨆ f : (ρ 0).IntertwiningMap (whit2 ψ d (piTensor ρ)), LinearMap.range f.toLinearMap := by
      refine Submodule.mem_iSup_of_mem (whitFirstMap ψ d ρ v) (LinearMap.mem_range.2 ⟨v 0, ?_⟩)
      show whitFirstLin ψ d ρ v (v 0) = _
      rw [whitFirstLin_apply, Function.update_eq_self]
    rw [Submodule.Quotient.mk_smul]
    exact Submodule.smul_mem _ r hmem
  | add a b ha hb =>
    rw [Submodule.Quotient.mk_add]
    exact Submodule.add_mem _ ha hb

end GlobalTheory.CompanionTheory.BZNuPair
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerTwoBlockIntertwinersSpanStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir GlobalTheory.CompanionTheory.BZNuPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_two_block_intertwiners_span : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (d : Fin 2 → ℕ) (X : Fin 2 → Type)
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)),
    ⨆ f : (ρ 0).IntertwiningMap (whit2 ψ d (piTensor ρ)), LinearMap.range f.toLinearMap = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.BZNuPair.whit_iSup_range_eq_top | exact GlobalTheory.CompanionTheory.BZNuPair.whit_iSup_range_eq_top | (intros; apply GlobalTheory.CompanionTheory.BZNuPair.whit_iSup_range_eq_top <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerSubquotientEquiv
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.CompanionTheory.BZNuPair

namespace GlobalTheory.CompanionTheory.BZNuPair.WhitCover

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Y : Type} [AddCommGroup Y] [Module ℂ Y]

def toImg (ψ : AddChar k Circle) (d : Fin 2 → ℕ) (J : Representation ℂ (Levi k fun a => Fin (d a)) Y)
    (T : Subrepresentation J) : T.toSubmodule →ₗ[ℂ] (whitImg ψ d J T).toSubmodule :=
  LinearMap.codRestrict _ ((whitKer ψ d J).mkQ ∘ₗ T.toSubmodule.subtype) fun t => ⟨t, t.2, rfl⟩

def stepMap (ψ : AddChar k Circle) (d : Fin 2 → ℕ) (J : Representation ℂ (Levi k fun a => Fin (d a)) Y)
    (T T' : Subrepresentation J) :
    (T.toSubmodule ⧸ T'.toSubmodule.comap T.toSubmodule.subtype) →ₗ[ℂ]
      ((whitImg ψ d J T).toSubmodule ⧸
        (whitImg ψ d J T').toSubmodule.comap (whitImg ψ d J T).toSubmodule.subtype) :=
  Submodule.liftQ _ (Submodule.mkQ _ ∘ₗ toImg ψ d J T) fun t ht => by
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    exact ⟨t, ht, rfl⟩

theorem stepMap_surjective (ψ : AddChar k Circle) (d : Fin 2 → ℕ)
    (J : Representation ℂ (Levi k fun a => Fin (d a)) Y) (T T' : Subrepresentation J) :
    Function.Surjective (stepMap ψ d J T T') := by
  intro y
  obtain ⟨⟨_, t, ht, rfl⟩, rfl⟩ := Submodule.mkQ_surjective _ y
  exact ⟨Submodule.Quotient.mk ⟨t, ht⟩, rfl⟩

theorem whitKer_subQuot_le (ψ : AddChar k Circle) (d : Fin 2 → ℕ)
    (J : Representation ℂ (Levi k fun a => Fin (d a)) Y) (T T' : Subrepresentation J) :
    whitKer ψ d (subQuot T T') ≤ LinearMap.ker (stepMap ψ d J T T') := by
  refine Submodule.span_le.2 ?_
  rintro w ⟨u, v, rfl⟩
  obtain ⟨t, rfl⟩ := Submodule.mkQ_surjective _ v
  let s : T.toSubmodule := T.toRepresentation (secondEmb d (u : GL (Fin (d 1)) k)) t - ((whitChar ψ (d 1) u : ℂˣ) : ℂ) • t
  have h0 : toImg ψ d J T s = 0 := by
    apply Subtype.ext
    exact (Submodule.Quotient.mk_eq_zero _).2 (Submodule.subset_span ⟨u, (t : Y), rfl⟩)
  show stepMap ψ d J T T' (Submodule.Quotient.mk s) = 0
  show Submodule.mkQ _ (toImg ψ d J T s) = 0
  rw [h0, map_zero]

def coverMap (ψ : AddChar k Circle) (d : Fin 2 → ℕ) (J : Representation ℂ (Levi k fun a => Fin (d a)) Y)
    (T T' : Subrepresentation J) :
    (whit2 ψ d (subQuot T T')).IntertwiningMap (subQuot (whitImg ψ d J T) (whitImg ψ d J T')) :=
  .mk ((whitKer ψ d (subQuot T T')).liftQ (stepMap ψ d J T T') (whitKer_subQuot_le ψ d J T T')) fun g => by
    ext v
    rfl

theorem coverMap_surjective (ψ : AddChar k Circle) (d : Fin 2 → ℕ)
    (J : Representation ℂ (Levi k fun a => Fin (d a)) Y) (T T' : Subrepresentation J) :
    Function.Surjective (coverMap ψ d J T T') := by
  intro y
  obtain ⟨x, rfl⟩ := stepMap_surjective ψ d J T T' y
  exact ⟨Submodule.Quotient.mk x, rfl⟩

theorem iSup_range_of_surjective {G A B C : Type} [Group G] [AddCommGroup A] [Module ℂ A] [AddCommGroup B]
    [Module ℂ B] [AddCommGroup C] [Module ℂ C] {α : Representation ℂ G A} {β : Representation ℂ G B}
    {γ : Representation ℂ G C} (p : β.IntertwiningMap γ) (hp : Function.Surjective p)
    (h : ⨆ f : α.IntertwiningMap β, LinearMap.range f.toLinearMap = ⊤) :
    ⨆ f : α.IntertwiningMap γ, LinearMap.range f.toLinearMap = ⊤ := by
  rw [eq_top_iff]
  have h1 : (⊤ : Submodule ℂ C) = (⊤ : Submodule ℂ B).map p.toLinearMap := by
    rw [Submodule.map_top]
    exact (LinearMap.range_eq_top.2 hp).symm
  rw [h1, ← h, Submodule.map_iSup]
  refine iSup_le fun f => ?_
  refine le_trans ?_ (le_iSup _ (p.comp f))
  rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
  exact ⟨v, rfl⟩

theorem main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (d : Fin 2 → ℕ) (Y : Type) [AddCommGroup Y] [Module ℂ Y]
    (J : Representation ℂ (Levi k fun a => Fin (d a)) Y) (T T' : Subrepresentation J) (X : Fin 2 → Type)
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)),
    T' ≤ T → (subQuot T T').Equiv (piTensor ρ) →
    ⨆ f : (ρ 0).IntertwiningMap (subQuot (whitImg ψ d J T) (whitImg ψ d J T')), LinearMap.range f.toLinearMap = ⊤ := by
  intro k _ _ _ _ ψ d Y _ _ J T T' X _ _ ρ _ E
  have hE : Function.Surjective (whitMap ψ d E.symm.toIntertwiningMap) := by
    intro y
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ y
    exact ⟨Submodule.Quotient.mk (E x), by
      show Submodule.Quotient.mk (E.symm (E x)) = _
      rw [E.symm_apply_apply]; rfl⟩
  exact iSup_range_of_surjective ((coverMap ψ d J T T').comp (whitMap ψ d E.symm.toIntertwiningMap))
    ((coverMap_surjective ψ d J T T').comp hE) (GlobalTheory.T.whittaker_two_block_intertwiners_span k ψ d X ρ)

end GlobalTheory.CompanionTheory.BZNuPair.WhitCover

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerSubquotientEquivStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.CompanionTheory.BZNuPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_subquotient_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (d : Fin 2 → ℕ) (Y : Type) [AddCommGroup Y] [Module ℂ Y]
    (J : Representation ℂ (Levi k fun a => Fin (d a)) Y) (T T' : Subrepresentation J) (X : Fin 2 → Type)
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)),
    T' ≤ T → (subQuot T T').Equiv (piTensor ρ) →
    ⨆ f : (ρ 0).IntertwiningMap (subQuot (whitImg ψ d J T) (whitImg ψ d J T')), LinearMap.range f.toLinearMap = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.BZNuPair.WhitCover.main | exact GlobalTheory.CompanionTheory.BZNuPair.WhitCover.main | (intros; apply GlobalTheory.CompanionTheory.BZNuPair.WhitCover.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormInductionOfEstimates
noncomputable section

open MeasureTheory Finset
open scoped InnerProductSpace ENNReal ComplexOrder

namespace GlobalTheory.CompanionTheory.RgFdNorm

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 PositivityTheory.RgFd

variable {n : ℕ}

theorem cK_le_one {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (k : KG ε) : cK T k ≤ 1 := by
  have h1 := norm_inner_le_norm (𝕜 := ℂ) T.w (T.op k T.w)
  have h2 : ‖T.op k T.w‖ = ‖T.w‖ := ContinuousLinearMap.norm_map_of_mem_unitary (T.τ k).2 _
  rw [h2, T.w_norm] at h1
  simpa [cK] using h1

theorem finrank_pos_KType {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) :
    0 < Module.finrank ℂ T.V := by
  have hw : T.w ≠ 0 := fun h => by simpa [h] using T.w_norm
  have : Nontrivial T.V := ⟨T.w, 0, hw⟩
  exact Module.finrank_pos

abbrev IP (n : ℕ) : Type := {p : Fin n × Fin n // p.1 < p.2}

theorem prod_pairs (f : Fin n → Fin n → ℝ) :
    ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), f a b = ∏ p : IP n, f p.1.1 p.1.2 := by
  simp_rw [Finset.prod_filter]
  rw [← Fintype.prod_prod_type' (fun a b => if a < b then f a b else 1)]
  rw [← Finset.prod_subtype (univ.filter fun p : Fin n × Fin n => p.1 < p.2) (by simp)
    (fun p => f p.1 p.2), Finset.prod_filter]

def al (lam : Fin n → ℝ) (p : IP n) : ℝ := lam p.1.1 - lam p.1.2

def be (p : IP n) : ℝ := ((p.1.2 : ℕ) : ℝ) - ((p.1.1 : ℕ) : ℝ)

theorem al_pos {lam : Fin n → ℝ} (hlam : StrictAnti lam) (p : IP n) : 0 < al lam p :=
  sub_pos.2 (hlam p.2)

theorem be_nonneg (p : IP n) : 0 ≤ be p := by
  have : ((p.1.1 : ℕ) : ℝ) ≤ ((p.1.2 : ℕ) : ℝ) := by exact_mod_cast p.2.le
  exact sub_nonneg.2 this

theorem dimVlam_eq {lam : Fin n → ℝ} (hlam : StrictAnti lam) :
    dimVlam lam = (∏ p : IP n, al lam p) / ∏ p : IP n, be p := by
  unfold dimVlam
  rw [prod_pairs (fun a b => |lam a - lam b|), prod_pairs (fun a b => ((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))]
  congr 1
  exact Finset.prod_congr rfl fun p _ => abs_of_pos (al_pos hlam p)

theorem one_div_dimVlam_lamT {lam : Fin n → ℝ} (hlam : StrictAnti lam) (t : ℕ) :
    1 / dimVlam (lamT lam t) = (∏ p : IP n, be p) / ∏ p : IP n, (al lam p + t * be p) := by
  rw [dimVlam_eq (strictAnti_lamT hlam t), one_div_div]
  congr 1
  exact Finset.prod_congr rfl fun p _ => by simp only [al, be, lamT_sub]

theorem one_div_dimVlam {lam : Fin n → ℝ} (hlam : StrictAnti lam) :
    1 / dimVlam lam = (∏ p : IP n, be p) / ∏ p : IP n, al lam p := by
  rw [dimVlam_eq hlam, one_div_div]

theorem isMu_step {lam : Fin n → ℝ} {μ : Fin n → ℤ} (hμ : IsMu lam μ) (t : ℕ) :
    IsMu (lamT lam t) (μ + (t : ℤ) • Dz n) := by
  intro a
  have := hμ a
  rw [lamT_apply]
  simp only [Pi.add_apply, Pi.smul_apply, Dz, smul_eq_mul]
  push_cast
  linarith

theorem hI_nonneg (hM : PhiMul) {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (μ : Fin n → ℤ)
    {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) (p : KG ε × KG ε) : 0 ≤ hI T μ x p := by
  have h1 := (hM n ε μ 0 x hx p.1).1
  have h2 := (hM n ε μ 0 x hx p.2).1
  unfold hI
  positivity

theorem hI_step (hM : PhiMul) (hC : CoefPow) {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : IsHCParam lam)
    (T : KType ε (lowK ε lam)) (TD : KType ε (Dvec n)) (t : ℕ) (Tt : KType ε (lowK ε (lamT lam t)))
    (μ : Fin n → ℤ) {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) (p : KG ε × KG ε) :
    hI Tt (μ + (t : ℤ) • Dz n) x p = hI T μ x p * hI TD (Dz n) x p ^ t := by
  unfold hI
  rw [(hM n ε μ t x hx p.1).2, (hM n ε μ t x hx p.2).2, hC n ε lam hlam T TD t Tt]
  ring

def muS (ε : Fin n → Bool) : Measure (UJ ε) := muCD ε

def PP (ε : Fin n → Bool) : Measure (UJ ε × (KG ε × KG ε)) := (muS ε).prod ((dk ε).prod (dk ε))

theorem lintegral_hs (hS : HsInt) {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (μ : Fin n → ℤ) :
    ∫⁻ g : Formalism.REAL.UJ ε, ENNReal.ofReal (hsOp (PsiM T μ (Formalism.MainNotions.S.umat g))) ∂(muCD ε) =
      ENNReal.ofReal ((Module.finrank ℂ T.V : ℝ) ^ 2) *
        ∫⁻ z, ENNReal.ofReal (hI T μ (pP (toM z.1)) z.2) ∂(PP ε) := by
  obtain ⟨hm, hg⟩ := hS n ε Λ T μ
  have hm' := hm.ennreal_ofReal
  rw [PP, lintegral_prod _ hm'.aemeasurable, ← lintegral_const_mul _ hm'.lintegral_prod_right']
  exact lintegral_congr fun g => hg g

theorem posDef_pP (hP : HsPol) {ε : Fin n → Bool} (g : UJ ε) : (pP (toM g)).PosDef := by
  obtain ⟨X, hX, e⟩ := (hP n ε (toM g) g.2).1
  rw [e]
  exact exp_noncompactPart_posDef hX

theorem phiK_le_one (hP : HsPol) (hL : PhiLe) {ε : Fin n → Bool} (g : UJ ε) (k : KG ε) :
    phiK (Dz n) (pP (toM g)) k ≤ 1 := by
  obtain ⟨X, hX, e⟩ := (hP n ε (toM g) g.2).1
  rw [e]
  exact hL n ε X hX k

theorem hI_le_one (hP : HsPol) (hM : PhiMul) (hL : PhiLe) {ε : Fin n → Bool} {Λ : Fin n → ℝ}
    (T : KType ε Λ) (g : UJ ε) (p : KG ε × KG ε) : hI T (Dz n) (pP (toM g)) p ≤ 1 := by
  have hx := posDef_pP hP g
  have a1 := (hM n ε (Dz n) 0 _ hx p.1).1
  have a2 := (hM n ε (Dz n) 0 _ hx p.2).1
  have b1 := phiK_le_one hP hL g p.1
  have b2 := phiK_le_one hP hL g p.2
  have c0 : 0 ≤ cK T (p.1⁻¹ * p.2) := norm_nonneg _
  have c1 := cK_le_one T (p.1⁻¹ * p.2)
  unfold hI
  have e1 : phiK (Dz n) (pP (toM g)) p.1 * phiK (Dz n) (pP (toM g)) p.2 ≤ 1 :=
    mul_le_one₀ b1 a2.le b2
  have e2 : cK T (p.1⁻¹ * p.2) ^ 2 ≤ 1 := pow_le_one₀ c0 c1
  exact mul_le_one₀ e1 (by positivity) e2

theorem mass_of_normAt (hS : HsInt) {ε : Fin n → Bool} {lam : Fin n → ℝ} (hN : NormAt ε lam)
    (T : KType ε (lowK ε lam)) (μ : Fin n → ℤ) (hμ : IsMu lam μ) :
    ∫⁻ z, ENNReal.ofReal (hI T μ (pP (toM z.1)) z.2) ∂(PP ε) = ENNReal.ofReal (1 / dimVlam lam) := by
  have h := hN T μ hμ
  rw [lintegral_hs hS] at h
  have hd : (0 : ℝ) < (Module.finrank ℂ T.V : ℝ) ^ 2 := by
    have := finrank_pos_KType T
    positivity
  have e : (Module.finrank ℂ T.V : ℝ) ^ 2 / dimVlam lam =
      (Module.finrank ℂ T.V : ℝ) ^ 2 * (1 / dimVlam lam) := by ring
  rw [e, ENNReal.ofReal_mul hd.le] at h
  exact (ENNReal.mul_right_inj (ENNReal.ofReal_pos.2 hd).ne' ENNReal.ofReal_ne_top).1 h

theorem gap_of_le {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : StrictAnti lam) {h0 : ℝ} {t : ℕ}
    (ht : ⌈h0⌉₊ ≤ t) : GapAtLeast ε (lamT lam t) h0 := by
  have g0 : GapAtLeast ε lam 0 := fun a b _ => abs_nonneg _
  have g1 := gap_lamT hlam g0 t
  intro a b hab
  have h1 := g1 a b hab
  have h2 : h0 ≤ (t : ℝ) := (Nat.le_ceil h0).trans (by exact_mod_cast ht)
  linarith

theorem ae_eq_indicator (hP : HsPol) (hM : PhiMul) (hK : KNull) {ε : Fin n → Bool} {lam : Fin n → ℝ}
    (hlam : IsHCParam lam) (T : KType ε (lowK ε lam)) (TD : KType ε (Dvec n)) (μ : Fin n → ℤ) :
    (fun z : UJ ε × (KG ε × KG ε) => ENNReal.ofReal (hI T μ (pP (toM z.1)) z.2)) =ᵐ[PP ε]
      ({z : UJ ε × (KG ε × KG ε) | 0 < hI TD (Dz n) (pP (toM z.1)) z.2}).indicator
        (fun z => ENNReal.ofReal (hI T μ (pP (toM z.1)) z.2)) := by
  have h1 := hK n ε lam hlam T TD
  have h2 : ∀ᵐ p ∂((dk ε).prod (dk ε)), cK TD (p.1⁻¹ * p.2) = 0 → cK T (p.1⁻¹ * p.2) = 0 :=
    (measurePreserving_prod_inv_mul (dk ε) (dk ε)).quasiMeasurePreserving.ae
      (Measure.quasiMeasurePreserving_snd.ae h1)
  have h3 : ∀ᵐ z ∂(PP ε), cK TD (z.2.1⁻¹ * z.2.2) = 0 → cK T (z.2.1⁻¹ * z.2.2) = 0 :=
    Measure.quasiMeasurePreserving_snd.ae h2
  filter_upwards [h3] with z hz
  by_cases hz0 : 0 < hI TD (Dz n) (pP (toM z.1)) z.2
  · rw [Set.indicator_of_mem (by exact hz0)]
  · rw [Set.indicator_of_notMem (by exact hz0)]
    have hx := posDef_pP hP z.1
    have a1 := (hM n ε (Dz n) 0 _ hx z.2.1).1
    have a2 := (hM n ε (Dz n) 0 _ hx z.2.2).1
    have hc : cK TD (z.2.1⁻¹ * z.2.2) = 0 := by
      by_contra hne
      have : 0 < cK TD (z.2.1⁻¹ * z.2.2) := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
      exact hz0 (by unfold hI; positivity)
    have hT := hz hc
    simp [hI, hT]

theorem norm_induction_of_estimates : MomW → CoefPow → KNull → HsPol → PhiMul → PhiLe → PhiCont → HsInt → GapNorm → NormInd := by
  intro hMom hC hK hP hM hL _ hS hG n ε hp hq lam hlam T μ hμ
  obtain ⟨h0, hg⟩ := hG n ε hp hq
  obtain ⟨TD⟩ := HW.kType_exists_of_dom ε (Dvec n) (fun a => ⟨Dz n a, by simp [Dvec, Dz]⟩)
    (fun a b hab _ => dvec_antitone hab.le)
  have hUm : Measurable fun z : UJ ε × (KG ε × KG ε) => hI TD (Dz n) (pP (toM z.1)) z.2 :=
    (hS n ε _ TD (Dz n)).1
  have hhm : Measurable fun z : UJ ε × (KG ε × KG ε) => ENNReal.ofReal (hI T μ (pP (toM z.1)) z.2) :=
    (hS n ε _ T μ).1.ennreal_ofReal
  have hmom : ∀ t : ℕ, ⌈h0⌉₊ ≤ t →
      ∫⁻ z, ENNReal.ofReal (hI T μ (pP (toM z.1)) z.2) *
          ENNReal.ofReal (hI TD (Dz n) (pP (toM z.1)) z.2 ^ t) ∂(PP ε) =
        ENNReal.ofReal ((∏ p : IP n, be p) / ∏ p : IP n, (al lam p + t * be p)) := by
    intro t ht
    obtain ⟨Tt⟩ := HW.kType_exists ε (lamT lam t) (isHCParam_lamT hlam t)
    rw [← one_div_dimVlam_lamT hlam.1 t,
      ← mass_of_normAt hS (hg _ (isHCParam_lamT hlam t) (gap_of_le hlam.1 ht)) Tt _ (isMu_step hμ t)]
    refine lintegral_congr fun z => ?_
    rw [hI_step hM hC hlam T TD t Tt μ (posDef_pP hP z.1),
      ENNReal.ofReal_mul (hI_nonneg hM T μ (posDef_pP hP z.1) z.2)]
  have key := hMom _ (PP ε) _ _ (IP n) (al lam) be (∏ p : IP n, be p) ⌈h0⌉₊ hhm hUm
    (fun z => ⟨hI_nonneg hM TD _ (posDef_pP hP z.1) z.2, hI_le_one hP hM hL TD z.1 z.2⟩)
    (al_pos hlam.1) be_nonneg (Finset.prod_nonneg fun p _ => be_nonneg p) hmom
  rw [← one_div_dimVlam hlam.1] at key
  have hmass : ∫⁻ z, ENNReal.ofReal (hI T μ (pP (toM z.1)) z.2) ∂(PP ε) =
      ENNReal.ofReal (1 / dimVlam lam) := by
    rw [lintegral_congr_ae (ae_eq_indicator hP hM hK hlam T TD μ),
      lintegral_indicator (measurableSet_lt measurable_const hUm)]
    exact key
  rw [lintegral_hs hS, hmass, ← ENNReal.ofReal_mul (sq_nonneg _), mul_one_div]

end GlobalTheory.CompanionTheory.RgFdNorm
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinitePlaceMinorHeightBound
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinitePlaceMinorHeightBound
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH

namespace GlobalTheory.CompanionTheory.GodementH

theorem absFin_minor_mul_le (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (ι : Type) [Fintype ι] [DecidableEq ι] (v : Pl (F := F)) (X : GL ι (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (κ : Matrix ι ι (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (hκ : ∀ i j, absFin F v (compFin F E v (κ i j)) ≤ 1) (f e : Fin n → ι) :
    absFin F v (compFin F E v ((X.1 * κ).submatrix f e).det) ≤ htFin F v (Formalism.UG.bc (compFin F E v) X) ^ n := by
  have hent : ∀ i j, absFin F v (compFin F E v ((X.1 * κ) i j)) ≤ htFin F v (Formalism.UG.bc (compFin F E v) X) := by
    intro i j
    have h1 : compFin F E v ((X.1 * κ) i j) = ((X.1.map (compFin F E v)) * (κ.map (compFin F E v))) i j := by
      rw [← Matrix.map_mul]; rfl
    rw [h1]
    refine (absFin_le_normFin F v _ i j).trans ((normFin_mul_le F v _ _).trans ?_)
    have h2 : normFin F v (κ.map (compFin F E v)) ≤ 1 := (normFin_le_iff F v).2 fun a b => hκ a b
    exact (mul_le_of_le_one_right' h2).trans (le_htOf (normFin F v) (Formalism.UG.bc (compFin F E v) X))
  rw [RingHom.map_det, Matrix.det_apply]
  refine absFin_sum_le F v _ _ fun σ _ => ?_
  have hprod : absFin F v (∏ i : Fin n, ((compFin F E v).mapMatrix ((X.1 * κ).submatrix f e)) (σ i) i)
      ≤ htFin F v (Formalism.UG.bc (compFin F E v) X) ^ n := by
    calc _ ≤ ∏ i : Fin n, absFin F v (((compFin F E v).mapMatrix ((X.1 * κ).submatrix f e)) (σ i) i) :=
          Finset.le_prod_of_submultiplicative _ (absFin_one F v).le (absFin_mul_le F v) _ _
      _ ≤ ∏ _i : Fin n, htFin F v (Formalism.UG.bc (compFin F E v) X) :=
          Finset.prod_le_prod' fun i _ => hent _ _
      _ = _ := by simp
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · rw [h, one_smul]; exact hprod
  · rw [h, Units.neg_smul, one_smul, absFin_neg]; exact hprod

end GlobalTheory.CompanionTheory.GodementH
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinitePlaceMinorHeightBoundStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_place_minor_height_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (v : Pl (F := F)) (X : GL ι (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (κ : Matrix ι ι (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
    (∀ i j, absFin F v (compFin F E v (κ i j)) ≤ 1) → ∀ f e : Fin n → ι,
    absFin F v (compFin F E v ((X.1 * κ).submatrix f e).det) ≤ htFin F v (Formalism.UG.bc (compFin F E v) X) ^ n := by
  first | exact @GlobalTheory.CompanionTheory.GodementH.absFin_minor_mul_le | exact GlobalTheory.CompanionTheory.GodementH.absFin_minor_mul_le | (intros; apply GlobalTheory.CompanionTheory.GodementH.absFin_minor_mul_le <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalNormInfinitePlaceBound
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalNormInfinitePlaceBound
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH

noncomputable section

namespace GlobalTheory.CompanionTheory.GodementH

theorem absEw_mul_locInf_le (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (J : Type) [Fintype J] (w : InfinitePlace F) (e : EmbOver E w)
    (u : J → E) (δ : (w.Completion ⊗[F] E)ˣ) (z : J → w.Completion ⊗[F] E) (c : ℝ≥0)
    (hz : ∀ f, z f = ((1 : w.Completion) ⊗ₜ[F] u f) * δ.1) (hc : ∀ f, ‖infEmb e (z f)‖₊ ≤ c) :
    GlobalTheory.Doubling.absEw F E w δ * locInf w u ≤ c ^ 2 := by
  classical
  have hnorm : ∀ (τ : EmbOver E w) (y : w.Completion ⊗[F] E), ‖infEmb τ y‖₊ = ‖infEmb e y‖₊ := by
    intro τ y
    rcases infEmb_eq_or_conj hσ e τ with h | h
    · rw [h]
    · rw [h, RingHom.comp_apply, RCLike.nnnorm_conj]
  have hterm : ∀ p : EmbOver E w × J, ‖infEmb e δ.1‖₊ * ‖p.1.1 (u p.2)‖₊ ≤ c := by
    rintro ⟨τ, f⟩
    have h1 : infEmb τ (z f) = τ.1 (u f) * infEmb τ δ.1 := by
      rw [hz f, map_mul, infEmb_tmul, map_one, one_mul]
    calc ‖infEmb e δ.1‖₊ * ‖τ.1 (u f)‖₊ = ‖infEmb τ δ.1‖₊ * ‖τ.1 (u f)‖₊ := by rw [hnorm τ]
      _ = ‖infEmb τ (z f)‖₊ := by rw [h1, nnnorm_mul, mul_comm]
      _ = ‖infEmb e (z f)‖₊ := hnorm τ _
      _ ≤ c := hc f
  have hsup : ‖infEmb e δ.1‖₊ * (Finset.univ.sup fun p : EmbOver E w × J => ‖p.1.1 (u p.2)‖₊) ≤ c := by
    rw [Finset.mul_sup₀]
    exact Finset.sup_le fun p _ => hterm p
  unfold locInf
  rw [GlobalTheory.Doubling.absEw_eq_sq hσ e, ← mul_pow]
  convert pow_le_pow_left' hsup 2
end GlobalTheory.CompanionTheory.GodementH

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalNormInfinitePlaceBoundStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_norm_infinite_place_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (J : Type) [Fintype J] (w : InfinitePlace F) (e : EmbOver E w) (u : J → E) (δ : (w.Completion ⊗[F] E)ˣ) (z : J → w.Completion ⊗[F] E) (c : ℝ≥0),
    (∀ f, z f = ((1 : w.Completion) ⊗ₜ[F] u f) * δ.1) → (∀ f, ‖infEmb e (z f)‖₊ ≤ c) →
    GlobalTheory.Doubling.absEw F E w δ * locInf w u ≤ c ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.GodementH.absEw_mul_locInf_le | exact GlobalTheory.CompanionTheory.GodementH.absEw_mul_locInf_le | (intros; apply GlobalTheory.CompanionTheory.GodementH.absEw_mul_locInf_le <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalNormFinitePlaceBound
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalNormFinitePlaceBound
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH

noncomputable section

namespace GlobalTheory.CompanionTheory.GodementH

theorem absEv_mul_locFin_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (J : Type) [Fintype J] (v : Pl (F := F)) (u : J → E) (δ : (Fv F v ⊗[F] E)ˣ) (z : J → Fv F v ⊗[F] E) (c : ℝ≥0),
    (∀ f, z f = ((1 : Fv F v) ⊗ₜ[F] u f) * δ.1) → (∀ f, absFin F v (z f) ≤ c) →
    GlobalTheory.Doubling.absEv F E v δ * locFin σ v u ≤ c ^ 2 := by
  intro F E _ _ _ _ _ σ hσ J _ v u δ z c hz hc
  have e2 : ∀ (τ : E →ₐ[F] FvBar F v) (w : Fv F v ⊗[F] E),
      finEmb F v τ (sigR (Fv F v) σ w) = finEmb F v (τ.comp σ) w := by
    intro τ w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [sigR]
    | add y z hy hz => simp only [map_add (f := _), hy, hz]
  have hN := congrArg (fun y => absBar F v (finEmb F v (embBar F E v) y))
    (GlobalTheory.Doubling.algebraMap_norm_eq hσ (R := Fv F v) δ.1)
  simp only [map_mul, absBar_mul, e2, AlgHom.commutes, absBar_algebraMap] at hN
  have key : ∀ τ : E →ₐ[F] FvBar F v, absBar F v (finEmb F v τ δ.1) * supBar v τ u ≤ c := by
    intro τ
    unfold supBar
    rw [NNReal.mul_finset_sup]
    refine Finset.sup_le fun f _ => ?_
    refine le_trans (le_of_eq ?_) ((le_absFin F v τ (z f)).trans (hc f))
    rw [hz f, map_mul, absBar_mul, finEmb_tmul, map_one, one_mul, mul_comm]
  rw [GlobalTheory.Doubling.absEv_apply, hN]
  unfold locFin
  calc _ = (absBar F v (finEmb F v (embBar F E v) δ.1) * supBar v (embBar F E v) u) *
        (absBar F v (finEmb F v ((embBar F E v).comp σ) δ.1) * supBar v ((embBar F E v).comp σ) u) := by ring
    _ ≤ c * c := mul_le_mul' (key _) (key _)
    _ = c ^ 2 := (sq c).symm

end GlobalTheory.CompanionTheory.GodementH

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalNormFinitePlaceBoundStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_norm_finite_place_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (J : Type) [Fintype J] (v : Pl (F := F)) (u : J → E) (δ : (Fv F v ⊗[F] E)ˣ) (z : J → Fv F v ⊗[F] E) (c : ℝ≥0),
    (∀ f, z f = ((1 : Fv F v) ⊗ₜ[F] u f) * δ.1) → (∀ f, absFin F v (z f) ≤ c) →
    GlobalTheory.Doubling.absEv F E v δ * locFin σ v u ≤ c ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.GodementH.absEv_mul_locFin_le | exact GlobalTheory.CompanionTheory.GodementH.absEv_mul_locFin_le | (intros; apply GlobalTheory.CompanionTheory.GodementH.absEv_mul_locFin_le <;> assumption)
end
end
