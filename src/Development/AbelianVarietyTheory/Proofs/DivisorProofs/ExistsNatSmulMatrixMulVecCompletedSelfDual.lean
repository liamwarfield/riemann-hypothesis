module

public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryMatchingLatticesMatchesSphericalOps
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.MemIntegersOfMemIntAd
public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsAlgebraicIndependentGenericPoint
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteAdeleVectorAnnihilatorsCompactOpenBasis
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CtxExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatSmulMatrixMulVecCompletedSelfDual
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatSmulMatrixMulVecCompletedSelfDual
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

noncomputable section

set_option synthInstance.maxHeartbeats 160000

namespace GlobalTheory.LatMatch

theorem exists_nat_mul_intAf' {F : Type} [Field F] [NumberField F] (t : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) :
    ∃ m : ℕ, 0 < m ∧ (m : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) * t ∈ intAf F := by
  obtain ⟨m, hm, h⟩ := Formalism.L2.SG.Pf.Tau.TraceIntegralityAlt.exists_nat_mul_intAd t
  exact ⟨m, hm, fun v => h v⟩

set_option maxHeartbeats 1000000 in
theorem exists_nat_smul_intAE {D : D7} (w : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :
    ∃ k : ℕ, 0 < k ∧ k • w ∈ intAE D := by
  induction w using TensorProduct.induction_on with
  | zero => exact ⟨1, one_pos, by rw [smul_zero]; exact zero_mem _⟩
  | tmul β z =>
    obtain ⟨m, hm, hβ⟩ := exists_nat_mul_intAf' β
    obtain ⟨M, hM, o, ho⟩ := Formalism.L2.SG.Pf.Tau.TraceIntegralityAlt.exists_nat_mul_mem z
    refine ⟨m * M, Nat.mul_pos hm hM, ?_⟩
    have e : (m * M) • (β ⊗ₜ[D.host.F] z) = ((m : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) * β) ⊗ₜ[D.host.F] ((o : 𝓞 D.host.E) : D.host.E) := by
      have ho' : ((o : 𝓞 D.host.E) : D.host.E) = (M : D.host.E) * z := ho
      rw [ho', mul_smul, ← TensorProduct.tmul_smul, TensorProduct.smul_tmul', nsmul_eq_mul, nsmul_eq_mul]
    rw [e]
    exact AddSubgroup.subset_closure ⟨_, hβ, o, rfl⟩
  | add w w' h h' =>
    obtain ⟨k, hk, m⟩ := h
    obtain ⟨k', hk', m'⟩ := h'
    refine ⟨k * k', Nat.mul_pos hk hk', ?_⟩
    have e : (k * k') • (w + w') = k' • (k • w) + k • (k' • w') := by
      rw [smul_add, ← mul_smul, ← mul_smul, mul_comm k' k]
    rw [e]
    exact add_mem (nsmul_mem m k') (nsmul_mem m' k)

theorem exists_nat_smul_single {D : D7} (V : HSp D) :
    ∃ b : ℕ, 0 < b ∧ ∀ j : Fin V.rank, (Pi.single j (b : D.host.E) : Fin V.rank → D.host.E) ∈ GlobalTheory.Member.latC V := by
  classical
  have hspan := (GlobalTheory.Member.latHat_eq_hat_and_gram D V).2.2.2.1
  have key : ∀ v : Fin V.rank → D.host.E, ∃ m : ℕ, 0 < m ∧ (m : D.host.E) • v ∈ GlobalTheory.Member.latC V := by
    intro v
    have hv : v ∈ Submodule.span D.host.E (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) := by
      rw [hspan]; trivial
    induction hv using Submodule.span_induction with
    | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
    | zero => exact ⟨1, one_pos, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨m, hm, hmx⟩ := hx
      obtain ⟨k, hk, hky⟩ := hy
      refine ⟨m * k, Nat.mul_pos hm hk, ?_⟩
      have e : ((m * k : ℕ) : D.host.E) • (x + y) = k • ((m : D.host.E) • x) + m • ((k : D.host.E) • y) := by
        simp only [smul_add, Nat.cast_mul, ← Nat.cast_smul_eq_nsmul D.host.E, smul_smul]
        rw [mul_comm (k : D.host.E) (m : D.host.E)]
      rw [e]
      exact add_mem (Submodule.smul_of_tower_mem _ k hmx) (Submodule.smul_of_tower_mem _ m hky)
    | smul c x _ hx =>
      obtain ⟨m, hm, hmx⟩ := hx
      obtain ⟨d, hd, hdc⟩ := GlobalTheory.SmoothForms.Reduce.exists_nat_integral (fun _ : Unit => c)
      refine ⟨d * m, Nat.mul_pos hd hm, ?_⟩
      have e : ((d * m : ℕ) : D.host.E) • (c • x) = (⟨(d : D.host.E) * c, (mem_integralClosure_iff _ _).2 (hdc ())⟩ : 𝓞 D.host.E) • ((m : D.host.E) • x) := by
        funext i
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [Algebra.smul_def]
        change (((d * m : ℕ) : D.host.E)) * (c * x i) = ((d : D.host.E) * c) * ((m : D.host.E) * x i)
        push_cast
        ring
      rw [e]
      exact (GlobalTheory.Member.latC V).smul_mem _ hmx
  choose m hm hmv using fun j : Fin V.rank => key (Pi.single j 1)
  refine ⟨∏ j, m j, Finset.prod_pos fun j _ => hm j, fun j => ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
  have : (Pi.single j (((∏ i ∈ Finset.univ.erase j, m i) * m j : ℕ) : D.host.E) : Fin V.rank → D.host.E) =
      (∏ i ∈ Finset.univ.erase j, m i) • ((m j : D.host.E) • Pi.single j 1) := by
    funext i
    rcases eq_or_ne i j with rfl | h
    · simp
    · simp [Pi.single_apply, h]
  rw [this]
  exact Submodule.smul_of_tower_mem _ _ (hmv j)

theorem mul_mem_intAE' (D : D7) {x y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (hy : y ∈ intAE D) :
    x * y ∈ intAE D := by
  refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intAE D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, v, rfl⟩
    refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, u * v, ?_⟩
    · rw [map_mul]; exact mul_mem (ha w) (hb w)
    · rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl
  · intro x _; rw [zero_mul]; exact zero_mem _
  · intro x _; rw [mul_zero]; exact zero_mem _
  · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
  · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
  · intro x y _ _ h; rw [mul_neg]; exact neg_mem h

theorem mulVec_lamHat_bound : ∀ {D : D7} (V V' : HSp D) (X : Matrix (Fin V'.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)), ∃ N : ℕ, 0 < N ∧ ∀ y ∈ Formalism.L2.NTheta.LamHat V, ((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • X.mulVec y ∈ Formalism.L2.NTheta.LamHat V' := by
  intro D V V' X
  classical
  obtain ⟨m, hm, hden⟩ := GlobalTheory.SmoothForms.Reduce.den_hat (D := D) (GlobalTheory.Member.latC V)
    (GlobalTheory.Member.latHat_eq_hat_and_gram D V).2.2.1
  choose k hk hkX using fun p : Fin V'.rank × Fin V.rank => exists_nat_smul_intAE (D := D) (X p.1 p.2)
  have hc : 0 < ∏ p, k p := Finset.prod_pos fun p _ => hk p
  have hcX : ∀ j i, (∏ p, k p) • X j i ∈ intAE D := by
    intro j i
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (j, i)), mul_smul]
    exact nsmul_mem (hkX (j, i)) _
  obtain ⟨b, hb, hbs⟩ := exists_nat_smul_single V'
  refine ⟨b * ((∏ p, k p) * m), Nat.mul_pos hb (Nat.mul_pos hc hm), fun y hy => ?_⟩
  have hy' : ∀ i, m • y i ∈ intAE D := hden y (by rw [← GlobalTheory.LatDual.lamHat_eq_hat]; exact hy)
  have hw : ∀ j, ((∏ p, k p) * m) • X.mulVec y j ∈ intAE D := by
    intro j
    simp only [Matrix.mulVec, dotProduct, Finset.smul_sum]
    refine sum_mem fun i _ => ?_
    have := mul_mem_intAE' D (hcX j i) (hy' i)
    convert this using 1
    simp only [nsmul_eq_mul]
    push_cast
    ring
  have hV' : ∀ w : Fin V'.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E, (∀ j, w j ∈ intAE D) →
      (fun j => (b : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) * w j) ∈ Formalism.L2.NTheta.LamHat V' := by
    intro w hw
    have e : (fun j => (b : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) * w j) = ∑ l, (fun j => w l *
        ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (Pi.single l (b : D.host.E) : Fin V'.rank → D.host.E) j)) := by
      funext j
      rw [Finset.sum_apply, Finset.sum_eq_single j]
      · rw [Pi.single_eq_same, ← Algebra.TensorProduct.natCast_def', mul_comm]
      · intro l _ hl
        rw [Pi.single_eq_of_ne (Ne.symm hl), TensorProduct.tmul_zero, mul_zero]
      · intro h; exact absurd (Finset.mem_univ j) h
    rw [e]
    refine sum_mem fun l _ => GlobalTheory.LatDual.smul_mem_lamHat V' _ (hw l) _ ?_
    refine AddSubgroup.subset_closure ⟨1, fun v => by rw [map_one]; exact one_mem _, _, ?_, rfl⟩
    have h := (GlobalTheory.Member.mem_latC V' _).1 (hbs l)
    rw [Module.Basis.equivFun_symm_apply] at h
    exact h
  have := hV' _ hw
  convert this using 1
  funext j
  simp only [Pi.smul_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_mul]
  ring

end GlobalTheory.LatMatch
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatSmulMatrixMulVecCompletedSelfDualStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nat_smul_matrix_mulVec_completedSelfDual : ∀ {D : D7} (V V' : HSp D) (X : Matrix (Fin V'.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)), ∃ N : ℕ, 0 < N ∧ ∀ y ∈ Formalism.L2.NTheta.LamHat V, ((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • X.mulVec y ∈ Formalism.L2.NTheta.LamHat V' := by
  first | exact @GlobalTheory.LatMatch.mulVec_lamHat_bound | exact GlobalTheory.LatMatch.mulVec_lamHat_bound | (intros; apply GlobalTheory.LatMatch.mulVec_lamHat_bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FieldDegreeLeChowFormDegreeAlgebraicPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FieldDegreeLeChowFormDegreeAlgebraicPoint
set_option autoImplicit false

noncomputable section

open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt

namespace GlobalTheory.CompHt.PointLow

set_option autoImplicit false in
open MvPolynomial in
private lemma natDegree_aeval_le_totalDegree_of_natDegree_le_one {R S σ : Type} [CommRing R] [CommRing S] [Algebra R S]
    (p : MvPolynomial σ R) (s : σ → Polynomial S) (hs : ∀ i, (s i).natDegree ≤ 1) :
    (MvPolynomial.aeval s p).natDegree ≤ p.totalDegree := by
  conv_lhs => rw [p.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun d hd => ?_
  rw [MvPolynomial.aeval_monomial]
  refine Polynomial.natDegree_mul_le.trans ?_
  have h0 : (algebraMap R (Polynomial S) (p.coeff d)).natDegree = 0 := by
    rw [Polynomial.algebraMap_apply]; exact Polynomial.natDegree_C _
  rw [h0, zero_add, Finsupp.prod]
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  refine le_trans ?_ (MvPolynomial.le_totalDegree hd)
  refine Finset.sum_le_sum fun i _ => ?_
  refine Polynomial.natDegree_pow_le.trans ?_
  simpa using Nat.mul_le_mul_left (d i) (hs i)


set_option autoImplicit false in
open MvPolynomial in
theorem _root_.GlobalTheory.CompHt.PointLow.finrank_le_of_isChowFormInt : ∀ (K : Type) [Field K] [CharZero K] (N δ : ℕ) (y : Fin N → AlgebraicClosure K)
    (j : Fin N) (f : MvPolynomial (Fin (0 + 1) × Fin N) K), y j = 1 → _root_.GlobalTheory.ChowHt.IsChowFormInt (_root_.GlobalTheory.CompHt.coneIdeal K y) 0 δ f →
    Module.finrank K (IntermediateField.adjoin K (Set.range y)) ≤ δ := by
  intro K _ _ N δ y j f hyj hf
  classical
  set E := IntermediateField.adjoin K (Set.range y) with hE
  haveI : FiniteDimensional K E :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  rw [← AlgHom.card K E (AlgebraicClosure K)]
  let yE : Fin N → E := fun k => ⟨y k, IntermediateField.subset_adjoin K _ ⟨k, rfl⟩⟩
  let pt : (E →ₐ[K] AlgebraicClosure K) → Fin N → AlgebraicClosure K := fun σ k => σ (yE k)
  have hpj : ∀ σ, pt σ j = 1 := by
    intro σ
    have : yE j = 1 := Subtype.ext hyj
    simp only [pt, this, map_one]
  have hzero : ∀ σ, ∀ g ∈ _root_.GlobalTheory.CompHt.coneIdeal K y, MvPolynomial.aeval (pt σ) g = 0 := by
    intro σ g hg
    have hy := _root_.GlobalTheory.CompHt.aeval_eq_zero_of_mem_coneIdeal hg
    have hE0 : MvPolynomial.aeval yE g = 0 := by
      apply Subtype.ext
      have := MvPolynomial.comp_aeval_apply yE E.val g
      show E.val (MvPolynomial.aeval yE g) = E.val 0
      rw [this, map_zero]
      exact hy
    have := MvPolynomial.comp_aeval_apply yE σ g
    rw [hE0, map_zero] at this
    exact this.symm
  have hinj : Function.Injective pt := by
    intro σ τ h
    refine IntermediateField.adjoin_algHom_ext K fun x hx => ?_
    obtain ⟨k, rfl⟩ := hx
    exact congrFun h k
  set fΩ := MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f with hfΩ
  have hfΩ0 : fΩ ≠ 0 := by
    intro h
    exact hf.ne_zero (MvPolynomial.map_injective _ (algebraMap K (AlgebraicClosure K)).injective
      (by rw [← hfΩ, h, map_zero]))
  let lin : (E →ₐ[K] AlgebraicClosure K) → (E →ₐ[K] AlgebraicClosure K) →
      MvPolynomial (Fin (0 + 1) × Fin N) (AlgebraicClosure K) :=
    fun σ τ => ∑ k, X (0, k) * C (pt σ k - pt τ k)
  have hlin_eval : ∀ σ τ (a : Fin (0 + 1) × Fin N → AlgebraicClosure K),
      eval a (lin σ τ) = ∑ k, a (0, k) * pt σ k - ∑ k, a (0, k) * pt τ k := by
    intro σ τ a
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [lin, map_sum, eval_mul, eval_X, eval_C, ← Finset.sum_sub_distrib, mul_sub]
  set pairs := Finset.univ.filter fun st : (E →ₐ[K] AlgebraicClosure K) × (E →ₐ[K] AlgebraicClosure K) =>
    st.1 ≠ st.2 with hpairs
  set Q := fΩ * ∏ st ∈ pairs, lin st.1 st.2 with hQ
  have hQ0 : Q ≠ 0 := by
    refine mul_ne_zero hfΩ0 (Finset.prod_ne_zero_iff.mpr fun st hst => ?_)
    have hne : st.1 ≠ st.2 := (Finset.mem_filter.mp hst).2
    have hpne : pt st.1 ≠ pt st.2 := fun h => hne (hinj h)
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hpne
    intro h0
    have := congrArg (eval (Pi.single (0, k) 1)) h0
    rw [hlin_eval, map_zero] at this
    simp only [Pi.single_apply, Prod.mk.injEq, true_and, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    exact hk (sub_eq_zero.mp this)
  obtain ⟨a, ha⟩ : ∃ a, eval a Q ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hQ0 (MvPolynomial.funext fun x => by rw [hcon x, map_zero])
  have hfa : eval a fΩ ≠ 0 := fun h => ha (by rw [hQ, eval_mul, h, zero_mul])
  let c : (E →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K := fun σ => ∑ k, a (0, k) * pt σ k
  have hdist : Function.Injective c := by
    intro σ τ h
    by_contra hne
    apply ha
    rw [hQ, eval_mul, map_prod]
    refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (i := (σ, τ))
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩) ?_)
    rw [hlin_eval]
    exact sub_eq_zero.mpr h
  let s : Fin (0 + 1) × Fin N → Polynomial (AlgebraicClosure K) :=
    fun ik => Polynomial.C (a ik) + if ik.2 = j then Polynomial.X else 0
  set g := MvPolynomial.aeval s f with hg
  have heval : ∀ t, g.eval t = MvPolynomial.aeval (fun ik => a ik + if ik.2 = j then t else 0) f := by
    intro t
    have := MvPolynomial.comp_aeval_apply s
      ((Polynomial.aeval t).restrictScalars K : Polynomial (AlgebraicClosure K) →ₐ[K] AlgebraicClosure K) f
    rw [hg, ← Polynomial.coe_aeval_eq_eval, show (Polynomial.aeval t) (MvPolynomial.aeval s f) =
      ((Polynomial.aeval t).restrictScalars K : Polynomial (AlgebraicClosure K) →ₐ[K] AlgebraicClosure K)
        (MvPolynomial.aeval s f) from rfl, this]
    refine congrArg (fun v => MvPolynomial.aeval v f) (funext fun ik => ?_)
    simp only [s]
    split_ifs <;> simp
  have hg0 : g ≠ 0 := by
    intro h
    have := heval 0
    rw [h, Polynomial.eval_zero] at this
    have h2 : (fun ik : Fin (0 + 1) × Fin N => a ik + if ik.2 = j then (0 : AlgebraicClosure K) else 0) = a := by
      funext ik; split_ifs <;> simp
    rw [h2] at this
    apply hfa
    rw [hfΩ, MvPolynomial.eval_map, ← MvPolynomial.aeval_def]
    exact this.symm
  have hroot : ∀ σ, g.eval (-c σ) = 0 := by
    intro σ
    rw [heval]
    refine (hf.zero_iff _).mpr
      ⟨pt σ, fun h => by simpa [hpj σ] using congrFun h j, hzero σ, fun i => ?_⟩
    obtain rfl : i = 0 := Fin.ext (Nat.lt_one_iff.mp i.isLt)
    simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, hpj σ, mul_one]
    simp [c]
  have hcard : Fintype.card (E →ₐ[K] AlgebraicClosure K) ≤ g.roots.toFinset.card := by
    rw [← Finset.card_univ]
    refine Finset.card_le_card_of_injOn (fun σ => -c σ) (fun σ _ => ?_) ?_
    · simp only [Finset.mem_coe, Multiset.mem_toFinset]
      rw [Polynomial.mem_roots hg0]
      exact hroot σ
    · intro σ _ τ _ h
      exact hdist (neg_injective h)
  have hhom := ((_root_.GlobalTheory.ChowHt.isMultiHomogeneous_iff_block.mp
    hf.homog).isHomogeneous)
  have htot : f.totalDegree = δ := by
    rw [hhom.totalDegree hf.ne_zero]
    simp
  calc Fintype.card (E →ₐ[K] AlgebraicClosure K) ≤ g.roots.toFinset.card := hcard
    _ ≤ Multiset.card g.roots := Multiset.toFinset_card_le _
    _ ≤ g.natDegree := Polynomial.card_roots' g
    _ ≤ f.totalDegree := natDegree_aeval_le_totalDegree_of_natDegree_le_one f s fun ik => by
        simp only [s]
        split_ifs
        · exact (Polynomial.natDegree_add_le _ _).trans (by simp)
        · simp
    _ = δ := htot

end GlobalTheory.CompHt.PointLow
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FieldDegreeLeChowFormDegreeAlgebraicPointStatement
open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.field_degree_le_chowForm_degree_algebraic_point : ∀ (K : Type) [Field K] [CharZero K] (N δ : ℕ) (y : Fin N → AlgebraicClosure K) (j : Fin N) (f : MvPolynomial (Fin (0 + 1) × Fin N) K), y j = 1 → IsChowFormInt (coneIdeal K y) 0 δ f → Module.finrank K (IntermediateField.adjoin K (Set.range y)) ≤ δ := by
  first | exact @GlobalTheory.CompHt.PointLow.finrank_le_of_isChowFormInt | exact GlobalTheory.CompHt.PointLow.finrank_le_of_isChowFormInt | (intros; apply GlobalTheory.CompHt.PointLow.finrank_le_of_isChowFormInt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFixedBySchroedingerOpenFiniteSubgr
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFixedBySchroedingerOpenFiniteSubgr
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical Topology

noncomputable section

namespace GlobalTheory.WeilLevel

variable {F : Type} [Field F] [NumberField F] {N : ℕ}

theorem eventually_invariant {M : Type} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M] {Φ : M → ℂ}
    (h1 : IsLocallyConstant Φ) (h2 : HasCompactSupport Φ) : ∀ᶠ u in 𝓝 (0 : M), ∀ x, Φ (x + u) = Φ x := by
  have h : ∀ᶠ u in 𝓝 (0 : M), ∀ x ∈ tsupport Φ, Φ (x + u) = Φ x ∧ Φ (x - u) = Φ x := by
    apply h2.isCompact.eventually_forall_of_forall_eventually
    intro x _
    have a1 := (h1.comp_continuous (show Continuous fun z : M × M => z.2 + z.1 by fun_prop)).eventually_eq (0, x)
    have a2 := (h1.comp_continuous (show Continuous fun z : M × M => z.2 - z.1 by fun_prop)).eventually_eq (0, x)
    have a3 := (h1.comp_continuous (show Continuous fun z : M × M => z.2 by fun_prop)).eventually_eq (0, x)
    filter_upwards [a1, a2, a3] with z b1 b2 b3
    simp only [Function.comp, add_zero, sub_zero] at b1 b2 b3
    exact ⟨b1.trans b3.symm, b2.trans b3.symm⟩
  filter_upwards [h] with u hu x
  by_cases hx : x ∈ tsupport Φ
  · exact (hu x hx).1
  · by_cases hx' : x + u ∈ tsupport Φ
    · have := (hu _ hx').2
      rw [add_sub_cancel_right] at this
      exact this.symm
    · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']

theorem Bd_half_f (u y : Fin N → Af F) : Bd (Af F) (half F N) u y = u ⬝ᵥ y := by
  simp [Bd, half, dotProduct]

theorem annih_basis (hF : IsTotallyReal F) (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ) :
    (∀ K : Set (Fin N → Af F), IsCompact K → {y : Fin N → Af F | ∀ u ∈ K, ψ (pairA F 0 (u ⬝ᵥ y)) = 1} ∈ 𝓝 0) ∧
    ∀ U ∈ 𝓝 (0 : Fin N → Af F), ∃ L : AddSubgroup (Af F), IsOpen (L : Set (Af F)) ∧ IsCompact (L : Set (Af F)) ∧
      ∀ u : Fin N → Af F, (∀ l, u l ∈ L) → u ∈ U := by
  obtain ⟨lam, ν, hc⟩ := ctx_exists F hF ψ hψ N (half F N) (fun l => half_ne_zero l)
  obtain ⟨-, h2, h3⟩ := GlobalTheory.T.finiteAdeleVector_annihilators_compact_open_basis F N ψ lam ν (half F N) hc
  refine ⟨fun K hK => ?_, h3⟩
  have := h2 K hK
  simpa only [Bd_half_f] using this

def levelSub (L : AddSubgroup (Af F)) : AddSubgroup (VA F N) where
  carrier := {u | ∀ l, sndA F (u.1 l) ∈ L ∧ sndA F (u.2 l) ∈ L}
  zero_mem' := fun l => by simp
  add_mem' := fun ha hb l => by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, map_add (f := _)]
    exact ⟨L.add_mem (ha l).1 (hb l).1, L.add_mem (ha l).2 (hb l).2⟩
  neg_mem' := fun ha l => by
    simp only [Prod.fst_neg, Prod.snd_neg, Pi.neg_apply, map_neg]
    exact ⟨L.neg_mem (ha l).1, L.neg_mem (ha l).2⟩

theorem isOpen_levelSub {L : AddSubgroup (Af F)} (hL : IsOpen (L : Set (Af F))) :
    IsOpen (levelSub (N := N) L : Set (VA F N)) := by
  have hs : Continuous fun z : AF F => sndA F z := continuous_snd
  have e : (levelSub (N := N) L : Set (VA F N)) =
      ⋂ l, ((fun u : VA F N => sndA F (u.1 l)) ⁻¹' L ∩ (fun u : VA F N => sndA F (u.2 l)) ⁻¹' L) := by
    ext u; simp [levelSub]
  rw [e]
  refine isOpen_iInter_of_finite fun l => IsOpen.inter ?_ ?_
  · exact hL.preimage (hs.comp ((continuous_apply l).comp continuous_fst))
  · exact hL.preimage (hs.comp ((continuous_apply l).comp continuous_snd))

end GlobalTheory.WeilLevel

namespace GlobalTheory.WeilLevel

variable {F : Type} [Field F] [NumberField F] {N : ℕ}

theorem adele_ext {z z' : AF F} (h1 : fstA F z = fstA F z') (h2 : sndA F z = sndA F z') : z = z' := Prod.ext h1 h2

theorem pure_level [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ) (hF : IsTotallyReal F) (hψ : IsCharAF F ψ)
    (f : SchwartzMap (Fin N → mixedEmbedding.mixedSpace F) ℂ) (g : (Fin N → Af F) → ℂ)
    (hg : g ∈ GlobalTheory.WeilM.SB (Fin N → Af F)) :
    ∃ U : AddSubgroup (VA F N), IsOpen (U : Set (VA F N)) ∧ ∀ u ∈ U, inf u.1 = 0 → inf u.2 = 0 →
      GlobalTheory.WeilM.schr ψ u (GlobalTheory.WeilM.pureA F f g) = GlobalTheory.WeilM.pureA F f g := by
  obtain ⟨hann, hbas⟩ := annih_basis (N := N) hF ψ hψ
  have hV := eventually_invariant hg.1 hg.2
  obtain ⟨L0, hL0o, hL0c, hL0V⟩ := hbas _ hV
  set c : Af F := algebraMap F (Af F) (1 / 2)
  have hK2 : IsCompact ((fun a : Fin N → Af F => c • a) '' {a | ∀ l, a l ∈ L0}) := by
    have : IsCompact {a : Fin N → Af F | ∀ l, a l ∈ L0} := by
      have := isCompact_univ_pi (fun _ : Fin N => hL0c)
      simpa [Set.pi] using this
    exact this.image (continuous_const_smul c)
  have hA1 := hann _ hg.2.isCompact
  have hA2 := hann _ hK2
  obtain ⟨L1, hL1o, -, hL1⟩ := hbas _ (Filter.inter_mem (Filter.inter_mem hV hA1) hA2)
  refine ⟨levelSub (L0 ⊓ L1), isOpen_levelSub (by rw [AddSubgroup.coe_inf]; exact hL0o.inter hL1o),
    fun u hu h1 h2 => ?_⟩
  set a : Fin N → Af F := fun l => sndA F (u.1 l)
  set b : Fin N → Af F := fun l => sndA F (u.2 l)
  have ha0 : ∀ l, a l ∈ L0 := fun l => (AddSubgroup.mem_inf.mp (hu l).1).1
  have ha1 : ∀ l, a l ∈ L1 := fun l => (AddSubgroup.mem_inf.mp (hu l).1).2
  have hb1 : ∀ l, b l ∈ L1 := fun l => (AddSubgroup.mem_inf.mp (hu l).2).2
  obtain ⟨⟨hVa, -⟩, -⟩ := hL1 a ha1
  obtain ⟨⟨-, hAb⟩, hA2b⟩ := hL1 b hb1
  have i1 : ∀ l, fstA F (u.1 l) = 0 := fun l => congrFun h1 l
  have i2 : ∀ l, fstA F (u.2 l) = 0 := fun l => congrFun h2 l
  funext x
  set xf : Fin N → Af F := fun i => (x i).2
  have ex : (fun i => ((x + u.1) i).2) = xf + a := by
    funext i; rfl
  have ex' : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((x + u.1) i).1) =
      fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1 := by
    funext i
    have : ((x + u.1) i).1 = (x i).1 := by
      show (x i).1 + (u.1 i).1 = (x i).1
      rw [show (u.1 i).1 = fstA F (u.1 i) from rfl, i1 i, add_zero]
    rw [this]
  simp only [GlobalTheory.WeilM.schr, GlobalTheory.WeilM.pureA]
  rw [ex, ex', hVa xf]
  by_cases hg0 : g xf = 0
  · rw [hg0]; simp
  have hxK : xf ∈ tsupport g := subset_tsupport g hg0
  have e : x ⬝ᵥ u.2 + ⅟(2 : AF F) * (u.1 ⬝ᵥ u.2) = pairA F 0 (xf ⬝ᵥ b) + pairA F 0 ((c • a) ⬝ᵥ b) := by
    apply adele_ext
    · simp only [map_add (f := _), map_mul]
      rw [show fstA F (x ⬝ᵥ u.2) = (fstA F).toRingHom (x ⬝ᵥ u.2) from rfl,
        show fstA F (u.1 ⬝ᵥ u.2) = (fstA F).toRingHom (u.1 ⬝ᵥ u.2) from rfl, RingHom.map_dotProduct, RingHom.map_dotProduct]
      have : (fstA F).toRingHom ∘ u.2 = 0 := funext i2
      rw [this, dotProduct_zero, dotProduct_zero, mul_zero, add_zero]
      rw [show ∀ p, fstA F (pairA F 0 p) = 0 from fun _ => rfl, show ∀ p, fstA F (pairA F 0 p) = 0 from fun _ => rfl, add_zero]
    · simp only [map_add (f := _), map_mul]
      rw [show sndA F (x ⬝ᵥ u.2) = (sndA F).toRingHom (x ⬝ᵥ u.2) from rfl,
        show sndA F (u.1 ⬝ᵥ u.2) = (sndA F).toRingHom (u.1 ⬝ᵥ u.2) from rfl, RingHom.map_dotProduct, RingHom.map_dotProduct,
        invOf_two_eq, AlgHom.commutes, smul_dotProduct, smul_eq_mul]
      rw [show ∀ p, sndA F (pairA F 0 p) = p from fun _ => rfl, show ∀ p, sndA F (pairA F 0 p) = p from fun _ => rfl]
      rfl
  rw [e, AddChar.map_add_eq_mul, hAb _ hxK, hA2b _ ⟨a, ha0, rfl⟩]
  ring

end GlobalTheory.WeilLevel

namespace GlobalTheory.WeilLevel

theorem schA_level : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ),
    IsTotallyReal F → IsCharAF F ψ → ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin N), ∃ U : AddSubgroup (VA F N),
      IsOpen (U : Set (VA F N)) ∧ ∀ u ∈ U, inf u.1 = 0 → inf u.2 = 0 → GlobalTheory.WeilM.schr ψ u Φ = Φ := by
  intro F _ _ N _ ψ hF hψ Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    exact pure_level ψ hF hψ f g hg
  | zero =>
    exact ⟨⊤, isOpen_univ, fun u _ _ _ => by funext x; simp [GlobalTheory.WeilM.schr]⟩
  | add Φ Φ' _ _ h h' =>
    obtain ⟨U, hU, hUΦ⟩ := h
    obtain ⟨U', hU', hUΦ'⟩ := h'
    refine ⟨U ⊓ U', by rw [AddSubgroup.coe_inf]; exact hU.inter hU', fun u hu h1 h2 => ?_⟩
    funext x
    have e1 := congrFun (hUΦ u (AddSubgroup.mem_inf.mp hu).1 h1 h2) x
    have e2 := congrFun (hUΦ' u (AddSubgroup.mem_inf.mp hu).2 h1 h2) x
    simp only [GlobalTheory.WeilM.schr, Pi.add_apply] at e1 e2 ⊢
    rw [mul_add, e1, e2]
  | smul c Φ _ h =>
    obtain ⟨U, hU, hUΦ⟩ := h
    refine ⟨U, hU, fun u hu h1 h2 => ?_⟩
    funext x
    have e1 := congrFun (hUΦ u hu h1 h2) x
    simp only [GlobalTheory.WeilM.schr, Pi.smul_apply, smul_eq_mul] at e1 ⊢
    rw [mul_left_comm, e1]

end GlobalTheory.WeilLevel

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFixedBySchroedingerOpenFiniteSubgrStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicSchwartz_fixed_by_schroedinger_open_finite_subgroup : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ), IsTotallyReal F → IsCharAF F ψ → ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin N), ∃ U : AddSubgroup (VA F N), IsOpen (U : Set (VA F N)) ∧ ∀ u ∈ U, inf u.1 = 0 → inf u.2 = 0 → GlobalTheory.WeilM.schr ψ u Φ = Φ := by
  first | exact @GlobalTheory.WeilLevel.schA_level | exact GlobalTheory.WeilLevel.schA_level | (intros; apply GlobalTheory.WeilLevel.schA_level <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockAct2EqSymmetrisedHeisenbergQuadratic
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockAct2EqSymmetrisedHeisenbergQuadratic
open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil

noncomputable section
namespace GlobalTheory.FockHeisQuad

variable {P Q R S : ℕ}

theorem heisOp_single (a : Ix P Q) (b : Ix R S) (z : ℂ) :
    heisOp (Matrix.single a b z) = ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) •
      (z • raiB (a, b) - (lineSign a b * star z) • lowB (a, b)) := by
  unfold heisOp
  congr 1
  rw [Fintype.sum_eq_single (a, b)]
  · simp
  · rintro ⟨a', b'⟩ h
    have : ¬ (a = a' ∧ b = b') := fun ⟨h1, h2⟩ => h (by subst h1; subst h2; rfl)
    simp [Matrix.single_apply, this]

theorem single_mul_tr_apply (a : Ix P Q) (b : Ix R S) (z : ℂ) (Y : Mat R S) (a' : Ix P Q) (b' : Ix R S) :
    (Matrix.single a b z * Yᵀ) a' b' = if a' = a then z * Y b' b else 0 := by
  by_cases h : a' = a
  · subst h; simp [Matrix.mul_apply, Matrix.single_apply]
  · simp [Matrix.mul_apply, Matrix.single_apply, Ne.symm h, h]

theorem heisOp_single_mul (a : Ix P Q) (b : Ix R S) (z : ℂ) (Y : Mat R S) :
    heisOp (Matrix.single a b z * Yᵀ) = ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) •
      ∑ b' : Ix R S, ((z * Y b' b) • raiB (a, b') - (lineSign a b' * star (z * Y b' b)) • lowB (a, b')) := by
  unfold heisOp
  congr 1
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a]
  · simp [single_mul_tr_apply]
  · intro a' _ h
    simp [single_mul_tr_apply, h]
  · simp

end GlobalTheory.FockHeisQuad

noncomputable section
namespace GlobalTheory.FockHeisQuad

theorem quad {A : Type} [Ring A] [Algebra ℂ A] (U V X L : A) (c p ε : ℂ) (hc : c * c = 2 * p) (hp : p ≠ 0)
    (hε : ε = 1 ∨ ε = -1) :
    (4 * p * Complex.I)⁻¹ • ((ε / 4) • (((c • (U - V)) * (c • (Complex.I • (X + ε • L))) +
        (c • (Complex.I • (X + ε • L))) * (c • (U - V))) -
      ((c • (Complex.I • (U + V))) * (c • (X - ε • L)) + (c • (X - ε • L)) * (c • (Complex.I • (U + V)))))) =
      (1 / 4 : ℂ) • ((U * L + L * U) - ε • (V * X + X * V)) := by
  have hp' : p = c * c / 2 := by linear_combination -hc / 2
  subst hp'
  have hc0 : c ≠ 0 := by rintro rfl; simp at hp
  rcases hε with rfl | rfl <;>
  · simp only [mul_add, add_mul, mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, smul_add, smul_sub, smul_smul]
    match_scalars <;> field_simp <;> ring_nf

variable {R S : ℕ}
theorem upq_entry (Y : Mat R S) (hY : Y ∈ upq R S) {P Q : ℕ} (a : Ix P Q) (b b' : Ix R S) :
    lineSign a b * (lineSign a b' * star (Y b' b)) = - Y b b' := by
  have hJ : Jm R S = Matrix.diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1)) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Jm, Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply] <;> split_ifs <;> simp
  have h := congrFun (congrFun hY b) b'
  rw [hJ] at h
  simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply,
    Matrix.zero_apply] at h
  rcases a with a | a <;> rcases b with b | b <;> rcases b' with b' | b' <;>
    simp [lineSign] at h ⊢ <;> first | linear_combination h | linear_combination -h

end GlobalTheory.FockHeisQuad

noncomputable section
namespace GlobalTheory.FockHeisQuad
variable {P Q R S : ℕ}

theorem fockAct2_expand (Y : Mat R S) :
    fockAct2 P Q R S Y = ∑ a : Ix P Q, ∑ b : Ix R S, ∑ b' : Ix R S, Y b' b • omE (a, b') (a, b) := by
  simp only [fockAct2, LinearMap.comp_apply, omAct_apply,
    Matrix.kroneckerMapBilinear_apply_apply, Matrix.kroneckerMap_apply, LinearMap.mul_apply',
    Fintype.sum_prod_type, Matrix.one_apply]
  simp [ite_smul, Finset.sum_ite_eq, -Fintype.sum_sum_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]

theorem lineSign_cases (a : Ix P Q) (b : Ix R S) : lineSign a b = 1 ∨ lineSign a b = -1 := by
  rcases a with a | a <;> rcases b with b | b <;> simp [lineSign]

theorem term_eq (Y : Mat R S) (hY : Y ∈ upq R S) (a : Ix P Q) (b : Ix R S) :
    (4 * Real.pi * Complex.I : ℂ)⁻¹ • ((lineSign a b / 4) •
      ((heisOp (Matrix.single a b (1 : ℂ) * Yᵀ) * heisOp (Matrix.single a b Complex.I) +
          heisOp (Matrix.single a b Complex.I) * heisOp (Matrix.single a b (1 : ℂ) * Yᵀ)) -
        (heisOp (Matrix.single a b Complex.I * Yᵀ) * heisOp (Matrix.single a b (1 : ℂ)) +
          heisOp (Matrix.single a b (1 : ℂ)) * heisOp (Matrix.single a b Complex.I * Yᵀ)))) =
    ∑ b' : Ix R S, ((1 / 4 : ℂ) * Y b' b) • (raiB (a, b') * lowB (a, b) + lowB (a, b) * raiB (a, b')) +
      ∑ b' : Ix R S, ((1 / 4 : ℂ) * Y b b') • (lowB (a, b') * raiB (a, b) + raiB (a, b) * lowB (a, b')) := by
  set U : Module.End ℂ (Pol P Q R S) := ∑ b' : Ix R S, Y b' b • raiB (a, b') with hU
  set V : Module.End ℂ (Pol P Q R S) := ∑ b' : Ix R S, (lineSign a b' * star (Y b' b)) • lowB (a, b') with hV
  have h1 : heisOp (Matrix.single a b (1 : ℂ) * Yᵀ) = ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) • (U - V) := by
    rw [heisOp_single_mul, hU, hV, ← Finset.sum_sub_distrib]
    simp
  have h2 : heisOp (Matrix.single a b Complex.I * Yᵀ) =
      ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) • (Complex.I • (U + V)) := by
    rw [heisOp_single_mul, hU, hV, ← Finset.sum_add_distrib]
    congr 1
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun b' _ => ?_
    simp only [star_mul', Complex.star_def, Complex.conj_I, smul_add, smul_smul]
    match_scalars <;> ring
  have h3 : heisOp (Matrix.single a b (1 : ℂ)) =
      ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) • (raiB (a, b) - lineSign a b • lowB (a, b)) := by
    rw [heisOp_single]; simp
  have h4 : heisOp (Matrix.single a b Complex.I) =
      ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) • (Complex.I • (raiB (a, b) + lineSign a b • lowB (a, b))) := by
    rw [heisOp_single]
    congr 1
    simp only [Complex.star_def, Complex.conj_I, smul_add, smul_smul]
    match_scalars <;> ring
  have hc : ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) = 2 * (Real.pi : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]; push_cast; ring
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [h1, h2, h3, h4, quad U V (raiB (a, b)) (lowB (a, b)) _ _ _ hc hπ (lineSign_cases a b)]
  simp only [hU, hV, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, ← Finset.sum_add_distrib,
    Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b' _ => ?_
  have e := upq_entry Y hY a b b'
  clear h1 h2 h3 h4 hc hπ hU hV
  simp only [smul_add, smul_sub, smul_smul]
  match_scalars <;> first | ring1 | linear_combination (-1 / 4 : ℂ) * e

end GlobalTheory.FockHeisQuad

noncomputable section
namespace GlobalTheory.FockHeisQuad

theorem fockAct2_eq_heisOp_quad : ∀ (P Q R S : ℕ) (Y : Mat R S), Y ∈ upq R S →
    fockAct2 P Q R S Y = (4 * Real.pi * Complex.I : ℂ)⁻¹ • ∑ a : Ix P Q, ∑ b : Ix R S, (lineSign a b / 4) •
      ((heisOp (Matrix.single a b (1 : ℂ) * Yᵀ) * heisOp (Matrix.single a b Complex.I) +
          heisOp (Matrix.single a b Complex.I) * heisOp (Matrix.single a b (1 : ℂ) * Yᵀ)) -
        (heisOp (Matrix.single a b Complex.I * Yᵀ) * heisOp (Matrix.single a b (1 : ℂ)) +
          heisOp (Matrix.single a b (1 : ℂ)) * heisOp (Matrix.single a b Complex.I * Yᵀ))) := by
  intro P Q R S Y hY
  rw [fockAct2_expand, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.smul_sum]
  simp only [term_eq Y hY a]
  rw [Finset.sum_add_distrib]
  conv_rhs => arg 2; rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b' _ => ?_
  rw [omE, GlobalTheory.FockCasimir.lowB_mul_raiB (a, b) (a, b')]
  by_cases h : b' = b
  · subst h
    simp only [if_true]
    module
  · have h1 : ((a, b') : Ln P Q R S) ≠ (a, b) := by simp [h]
    simp only [h1, Ne.symm h1, if_false, add_zero]
    module

end GlobalTheory.FockHeisQuad
end
end
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockAct2EqSymmetrisedHeisenbergQuadraticStatement
open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockAct2_eq_symmetrised_heisenbergQuadratic : ∀ (P Q R S : ℕ) (Y : Mat R S), Y ∈ upq R S →
    fockAct2 P Q R S Y = (4 * Real.pi * Complex.I : ℂ)⁻¹ • ∑ a : Ix P Q, ∑ b : Ix R S, (lineSign a b / 4) •
      ((heisOp (Matrix.single a b (1 : ℂ) * Yᵀ) * heisOp (Matrix.single a b Complex.I) +
          heisOp (Matrix.single a b Complex.I) * heisOp (Matrix.single a b (1 : ℂ) * Yᵀ)) -
        (heisOp (Matrix.single a b Complex.I * Yᵀ) * heisOp (Matrix.single a b (1 : ℂ)) +
          heisOp (Matrix.single a b (1 : ℂ)) * heisOp (Matrix.single a b Complex.I * Yᵀ))) := by
  first | exact @GlobalTheory.FockHeisQuad.fockAct2_eq_heisOp_quad | exact GlobalTheory.FockHeisQuad.fockAct2_eq_heisOp_quad | (intros; apply GlobalTheory.FockHeisQuad.fockAct2_eq_heisOp_quad <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzRestrictTranslatedDiagonalMem
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzRestrictTranslatedDiagonalMem
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct FourierTransform
open MeasureTheory GroundTheory.Automorphic.GJMatrix

noncomputable section
namespace GlobalTheory.DiagShift

open scoped Classical

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

attribute [local instance] GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele
  GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField


variable (F κ) in
def diagA : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] (κ ⊕ κ → mixedEmbedding.mixedSpace F) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => Sum.elim x x
      map_add' := fun x x' => by funext i; cases i <;> simp
      map_smul' := fun c x => by funext i; cases i <;> simp }

theorem diagA_apply (x : κ → mixedEmbedding.mixedSpace F) : diagA F κ x = Sum.elim x x := rfl

theorem norm_le_diagA (x : κ → mixedEmbedding.mixedSpace F) : ‖x‖ ≤ ‖diagA F κ x‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => by
    simpa [diagA_apply] using norm_le_pi_norm (diagA F κ x) (Sum.inl j)


variable (F κ) in
def restrA : SchwartzMap (κ ⊕ κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ :=
  SchwartzMap.compCLM ℂ (diagA F κ).hasTemperateGrowth
    ⟨1, 1, fun x => by
      have := norm_le_diagA x
      have h0 := norm_nonneg (diagA F κ x)
      rw [pow_one, one_mul]; linarith⟩

theorem restrA_apply (f : SchwartzMap (κ ⊕ κ → mixedEmbedding.mixedSpace F) ℂ) (x : κ → mixedEmbedding.mixedSpace F) :
    restrA F κ f x = f (Sum.elim x x) := rfl

theorem shift_mem_finite {g : (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hg : g ∈ SB (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F)) (b : κ → FiniteAdeleRing (𝓞 F) F) :
    (fun y : κ → FiniteAdeleRing (𝓞 F) F => g (Sum.elim (y + b) y)) ∈ finiteSchwartzBruhatPi F := by
  have hd : Continuous fun y : κ → FiniteAdeleRing (𝓞 F) F =>
      (Sum.elim (y + b) y : κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) :=
    continuous_pi fun i => by
      cases i with
      | inl j => exact (continuous_apply j).add continuous_const
      | inr j => exact continuous_apply j
  have hr : Continuous fun z : κ ⊕ κ → FiniteAdeleRing (𝓞 F) F => fun j => z (Sum.inr j) :=
    continuous_pi fun j => continuous_apply _
  refine ⟨hg.1.comp_continuous hd, ?_⟩
  refine HasCompactSupport.intro (hg.2.isCompact.image hr) fun y hy => ?_
  by_contra h
  exact hy ⟨Sum.elim (y + b) y, subset_tsupport _ h, rfl⟩

theorem shift_pureA_mem (f : SchwartzMap (κ ⊕ κ → mixedEmbedding.mixedSpace F) ℂ)
    {g : (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ SB (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F))
    (u : κ → AdeleRing (𝓞 F) F) :
    (fun t : κ → AdeleRing (𝓞 F) F => pureA F f g (Sum.elim (t + u) t)) ∈ schwartzBruhatPi (K := F) (ι := κ) := by
  have key : (fun t : κ → AdeleRing (𝓞 F) F => pureA F f g (Sum.elim (t + u) t)) =
      schwartzBruhatTensorPi
        (restrA F κ (SchwartzMap.compSubConstCLM ℂ (-Sum.elim (infPartPi u) 0) f))
        (fun y : κ → FiniteAdeleRing (𝓞 F) F => g (Sum.elim (y + finPartPi u) y)) := by
    funext t
    simp only [schwartzBruhatTensorPi, restrA_apply, SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add]
    unfold pureA
    congr 1
    · congr 1
      funext i
      cases i with
      | inl j => exact map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) (t j).1 (u j).1
      | inr j => exact (add_zero _).symm
    · congr 1
      funext i
      cases i <;> rfl
  rw [key]
  exact schwartzBruhatTensorPi_mem _ (shift_mem_finite hg _)

theorem shift_mem_schwartzBruhatPi (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (φ : (κ ⊕ κ → AF F) → ℂ) (hφ : φ ∈ schA F (κ ⊕ κ)) (u : κ → AF F) :
    (fun t : κ → AF F => φ (Sum.elim (t + u) t)) ∈ schwartzBruhatPi (K := F) (ι := κ) := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    exact shift_pureA_mem f hg u
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul c x _ hx => exact Submodule.smul_mem _ c hx

end GlobalTheory.DiagShift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzRestrictTranslatedDiagonalMemStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct FourierTransform
open MeasureTheory GroundTheory.Automorphic.GJMatrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicSchwartz_restrict_translated_diagonal_mem : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (φ : (κ ⊕ κ → AF F) → ℂ), φ ∈ schA F (κ ⊕ κ) → ∀ u : κ → AF F, (fun t : κ → AF F => φ (Sum.elim (t + u) t)) ∈ schwartzBruhatPi (K := F) (ι := κ) := by
  first | exact @GlobalTheory.DiagShift.shift_mem_schwartzBruhatPi | exact GlobalTheory.DiagShift.shift_mem_schwartzBruhatPi | (intros; apply GlobalTheory.DiagShift.shift_mem_schwartzBruhatPi <;> assumption)
end
end
