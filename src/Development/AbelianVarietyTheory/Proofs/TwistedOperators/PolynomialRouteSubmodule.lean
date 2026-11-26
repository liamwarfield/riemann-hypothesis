module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSBOfIsNatDatum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Zact
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TripleFrameBaseExists
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilGlobalFactor

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRelOfLocalMatching
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.ChiGrid GlobalTheory.FunObj
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SquareRel

section Rel

variable {P Q Pr : Type*} [AddCommGroup P] [Module ℂ P] [AddCommGroup Q] [Module ℂ Q] [AddCommGroup Pr] [Module ℂ Pr]

def relOf (q : P →ₗ[ℂ] Pr) (q' : Q →ₗ[ℂ] Pr) : Submodule ℂ (P × Q) :=
  LinearMap.eqLocus (q ∘ₗ LinearMap.fst ℂ P Q) (q' ∘ₗ LinearMap.snd ℂ P Q)

theorem mem_relOf {q : P →ₗ[ℂ] Pr} {q' : Q →ₗ[ℂ] Pr} {x : P × Q} : x ∈ relOf q q' ↔ q x.1 = q' x.2 := Iff.rfl

theorem relOf_fst {q : P →ₗ[ℂ] Pr} {q' : Q →ₗ[ℂ] Pr} (hq' : Function.Surjective q') (a : P) : ∃ b, (a, b) ∈ relOf q q' := by
  obtain ⟨b, hb⟩ := hq' (q a)
  exact ⟨b, hb.symm⟩

theorem relOf_snd {q : P →ₗ[ℂ] Pr} {q' : Q →ₗ[ℂ] Pr} (hq : Function.Surjective q) (b : Q) : ∃ a, (a, b) ∈ relOf q q' := by
  obtain ⟨a, ha⟩ := hq (q' b)
  exact ⟨a, ha⟩

theorem relOf_ne_top [Nontrivial Pr] {q : P →ₗ[ℂ] Pr} {q' : Q →ₗ[ℂ] Pr} (hq : Function.Surjective q) : relOf q q' ≠ ⊤ := by
  intro h
  obtain ⟨y, hy⟩ := exists_ne (0 : Pr)
  obtain ⟨a, rfl⟩ := hq y
  have h1 : (a, (0 : Q)) ∈ relOf q q' := h ▸ Submodule.mem_top
  rw [mem_relOf, map_zero] at h1
  exact hy h1

end Rel

section Pol

variable {σ₁ σ₂ ν : Type} (e : σ₁ ⊕ σ₂ ≃ ν)

def polTens : MvPolynomial σ₁ ℂ ⊗[ℂ] MvPolynomial σ₂ ℂ ≃ₗ[ℂ] MvPolynomial ν ℂ :=
  ((MvPolynomial.basisMonomials σ₁ ℂ).tensorProduct (MvPolynomial.basisMonomials σ₂ ℂ)).equiv
    (MvPolynomial.basisMonomials ν ℂ) (Finsupp.sumFinsuppEquivProdFinsupp.symm.trans (Finsupp.domCongr e).toEquiv)

theorem finsupp_sum_eq (m : σ₁ →₀ ℕ) (n : σ₂ →₀ ℕ) :
    Finsupp.domCongr e (Finsupp.sumElim m n) = m.mapDomain (e ∘ Sum.inl) + n.mapDomain (e ∘ Sum.inr) := by
  ext x
  obtain ⟨s, rfl⟩ := e.surjective x
  have h1 : Function.Injective (e ∘ Sum.inl) := e.injective.comp Sum.inl_injective
  have h2 : Function.Injective (e ∘ Sum.inr) := e.injective.comp Sum.inr_injective
  rcases s with s | s
  · rw [Finsupp.add_apply, Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply,
      Finsupp.sumElim_inl]
    rw [show e (Sum.inl s) = (e ∘ Sum.inl) s from rfl, Finsupp.mapDomain_apply_of_injective h1, Finsupp.mapDomain_notin_range]
    · simp
    · rintro ⟨u, hu⟩
      exact Sum.inl_ne_inr (e.injective hu).symm
  · rw [Finsupp.add_apply, Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply,
      Finsupp.sumElim_inr]
    rw [show e (Sum.inr s) = (e ∘ Sum.inr) s from rfl, Finsupp.mapDomain_apply_of_injective h2, Finsupp.mapDomain_notin_range]
    · simp
    · rintro ⟨u, hu⟩
      exact Sum.inl_ne_inr (e.injective hu)

theorem polTens_tmul (p₁ : MvPolynomial σ₁ ℂ) (p₂ : MvPolynomial σ₂ ℂ) :
    polTens e (p₁ ⊗ₜ p₂) = MvPolynomial.rename (e ∘ Sum.inl) p₁ * MvPolynomial.rename (e ∘ Sum.inr) p₂ := by
  have key : (TensorProduct.mk ℂ _ _).compr₂ (polTens e).toLinearMap =
      (LinearMap.mul ℂ (MvPolynomial ν ℂ)).compl₁₂ (MvPolynomial.rename (R := ℂ) (e ∘ Sum.inl)).toLinearMap
        (MvPolynomial.rename (R := ℂ) (e ∘ Sum.inr)).toLinearMap := by
    refine (MvPolynomial.basisMonomials σ₁ ℂ).ext fun m => (MvPolynomial.basisMonomials σ₂ ℂ).ext fun n => ?_
    simp only [LinearMap.compr₂_apply, TensorProduct.mk_apply, LinearMap.compl₁₂_apply, LinearMap.mul_apply',
      AlgHom.toLinearMap_apply, MvPolynomial.coe_basisMonomials]
    have h : (MvPolynomial.monomial m (1 : ℂ)) ⊗ₜ[ℂ] (MvPolynomial.monomial n (1 : ℂ)) =
        ((MvPolynomial.basisMonomials σ₁ ℂ).tensorProduct (MvPolynomial.basisMonomials σ₂ ℂ)) (m, n) := by
      rw [Module.Basis.tensorProduct_apply, MvPolynomial.coe_basisMonomials, MvPolynomial.coe_basisMonomials]
    rw [h, polTens]
    erw [Module.Basis.equiv_apply]
    simp only [MvPolynomial.coe_basisMonomials, MvPolynomial.rename_monomial, MvPolynomial.monomial_mul, mul_one,
      Equiv.trans_apply, AddEquiv.toEquiv_eq_coe, AddEquiv.coe_toEquiv, Finsupp.sumFinsuppEquivProdFinsupp_symm_apply]
    rw [finsupp_sum_eq]
  exact LinearMap.congr_fun₂ key p₁ p₂

end Pol

end GlobalTheory.SquareRel

namespace GlobalTheory.SquareRel

section Route

variable {D : D7} {a b c d b' : ℕ}

end Route

section Grid

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (i j : ℕ) {d b' b₁ : ℕ}

theorem hasInfExp_alpha {μ₀ : T} (hL : L.Is μ₀) (t t' : T) (τ : D.what₂.Tau) {a : ℚ}
    (h : HasInfExp D (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) τ a) : HasInfExp D (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t' i j) τ a := by
  obtain ⟨-, -, ⟨θ, hθ⟩, -⟩ := id h
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  obtain ⟨n', hn', ho'⟩ := hL.xi_fin t'
  have h0 := GlobalTheory.Chain.StepVac.hasInfExp_of_order hθ (hL.xi t) hn ho τ
  have h0' := GlobalTheory.Chain.StepVac.hasInfExp_of_order hθ (hL.xi t') hn' ho' τ
  have hK : ∀ s, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G s i j = (L.mu0 (j + 1) * L.eta ^ GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps G i j) * L.xi s := fun s => by
    show L.mu0 (j + 1) * L.xi s * L.eta ^ GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps G i j = _
    exact mul_right_comm _ _ _
  have e : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t' i j = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j * (L.xi t)⁻¹ * L.xi t' := by
    rw [hK t', hK t, mul_inv_cancel_right]
  have := GlobalTheory.Chain.StepVac.hasInfExp_mul (GlobalTheory.Chain.StepVac.hasInfExp_mul h (GlobalTheory.Chain.StepVac.hasInfExp_inv h0)) h0'
  rw [e]
  simpa using this

end Grid

theorem nontrivial_of_tensor {Pr Pf Pi : Type*} [AddCommGroup Pr] [Module ℂ Pr] [AddCommGroup Pf] [Module ℂ Pf]
    [AddCommGroup Pi] [Module ℂ Pi] [Nontrivial Pi] (e : Pr ⊗[ℂ] Pf ≃ₗ[ℂ] Pi) : Nontrivial Pr := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  have hz : ∀ z : Pr ⊗[ℂ] Pf, z = 0 := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | tmul x y => rw [Subsingleton.elim x 0, TensorProduct.zero_tmul]
    | add x y hx hy => rw [hx, hy, add_zero]
  obtain ⟨u, hu⟩ := exists_ne (0 : Pi)
  apply hu
  rw [← e.apply_symm_apply u, hz (e.symm u), map_zero]

end GlobalTheory.SquareRel

namespace GlobalTheory.SquareRel

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (alpha beta)

variable {D : D7} {Pr Pf Pi : Type*} [AddCommGroup Pr] [Module ℂ Pr] [AddCommGroup Pf] [Module ℂ Pf]
  [AddCommGroup Pi] [Module ℂ Pi]

end GlobalTheory.SquareRel

namespace GlobalTheory.SquareRel

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (alpha beta)

variable {D : D7}

end GlobalTheory.SquareRel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorProductMulPolynomials
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.ChainFr Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.SquareIdent

section Real

open GlobalTheory.FockAdjoint GlobalTheory.SquareDict.AlgSmall GlobalTheory.RouteSeesaw

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S U U' : HSp D}

def sumVar (U U' : HSp D) (n : ℕ) : FVar D U.rank n ⊕ FVar D U'.rank n ≃ FVar D (GlobalTheory.Doubling.hsum U U').rank n where
  toFun := Sum.elim (fun v => (v.1, Fin.castAdd U'.rank v.2.1, v.2.2)) fun v => (v.1, Fin.natAdd U.rank v.2.1, v.2.2)
  invFun w := Sum.map (fun x => (w.1, x, w.2.2)) (fun z => (w.1, z, w.2.2)) (finSumFinEquiv.symm w.2.1)
  left_inv := by rintro (⟨τ, x, y⟩ | ⟨τ, y, z⟩) <;> simp
  right_inv := by
    rintro ⟨τ, k, y⟩
    obtain ⟨s, rfl⟩ := (finSumFinEquiv (m := U.rank) (n := U'.rank)).surjective k
    rcases s with s | s <;> simp

theorem fockVector_product_mul_polynomials (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (A : Fr S) (B : Fr U) (B' : Fr U') {f : WO S U → ℂ}
    {g : WO S U' → ℂ} (hf : IsThetaFunO ψ S U f) (hg : IsThetaFunO ψ S U' g) (P : PolF D U.rank S.rank)
    (Q : PolF D U'.rank S.rank) :
    box2 (ptF ψ θ A B f P) (ptF ψ θ A B' g Q) = ptF ψ θ A (GlobalTheory.SquareComm.frSum B B') (box2 f g)
      (GlobalTheory.SquareRel.polTens (sumVar U U' S.rank) (P ⊗ₜ Q)) := by
  have hfg := isThetaFunction_externalProductOnHermitianSum hf hg
  rw [GlobalTheory.SquareRel.polTens_tmul]
  have H : box2 f (ptF ψ θ A B' g Q) = ptF ψ θ A (GlobalTheory.SquareComm.frSum B B') (box2 f g)
      (MvPolynomial.rename (sumVar U U' S.rank ∘ Sum.inr) Q) := by
    induction Q using MvPolynomial.induction_on with
    | C a =>
      rw [MvPolynomial.rename_C, ← mul_one (MvPolynomial.C a), ptF_C, ptF_one, ← mul_one (MvPolynomial.C a), ptF_C, ptF_one]
      funext x; simp only [box2, Pi.smul_apply, smul_eq_mul]; ring
    | add p q hp hq =>
      rw [map_add (f := _), ptF_add, ptF_add, ← hp, ← hq]
      funext x; simp only [box2, Pi.add_apply]; ring
    | mul_X p v hp =>
      obtain ⟨τ, i, j⟩ := v
      rw [map_mul, MvPolynomial.rename_X, mul_comm (MvPolynomial.rename _ p), ptF_X_mul hψ hθ A _ hfg, ← hp, mul_comm p,
        ptF_X_mul hψ hθ A B' hg, show (sumVar U U' S.rank ∘ Sum.inr) (τ, i, j) = (τ, Fin.natAdd _ i, j) from rfl]
      dsimp only
      rw [creationOperator_externalProductOnHermitianSum B B' τ hψ hθ A _ hf (ptF_theta hψ hθ A B' hg p)]
      erw [((pr_unit B B' τ _ j).2 i).1, ((pr_unit B B' τ _ j).2 i).2]
      rw [aPlus_zero τ hψ hθ hf]
      funext x; simp [box2]
  have hg' := ptF_theta hψ hθ A B' hg Q
  induction P using MvPolynomial.induction_on with
  | C a => rw [MvPolynomial.rename_C, ptF_C, ← H, ← mul_one (MvPolynomial.C a), ptF_C, ptF_one, externalProductOnHermitianSum_smul_left]
  | add p q hp hq => rw [map_add (f := _), add_mul, ptF_add, ptF_add, ← hp, ← hq, externalProductOnHermitianSum_add_left]
  | mul_X p v hp =>
    obtain ⟨τ, i, j⟩ := v
    rw [map_mul, MvPolynomial.rename_X, mul_comm (MvPolynomial.rename _ p), mul_assoc, ptF_X_mul hψ hθ A _ hfg, ← hp,
      mul_comm p, ptF_X_mul hψ hθ A B hf, show (sumVar U U' S.rank ∘ Sum.inl) (τ, i, j) = (τ, Fin.castAdd _ i, j) from rfl]
    dsimp only
    rw [creationOperator_externalProductOnHermitianSum B B' τ hψ hθ A _ (ptF_theta hψ hθ A B hf p) hg']
    erw [((pr_unit B B' τ _ j).1 i).1, ((pr_unit B B' τ _ j).1 i).2]
    rw [aPlus_zero τ hψ hθ hg']
    funext x; simp [box2]

theorem ptF_sum (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (A : Fr S) (B : Fr U) {ι : Type} (s : Finset ι) (c : ι → ℂ)
    (f : ι → WO S U → ℂ) (hf : ∀ i ∈ s, IsThetaFunO ψ S U (f i)) (P : PolF D U.rank S.rank) :
    IsThetaFunO ψ S U (∑ i ∈ s, c i • f i) ∧ ptF ψ θ A B (∑ i ∈ s, c i • f i) P = ∑ i ∈ s, c i • ptF ψ θ A B (f i) P := by
  classical
  have lin : ∀ (a : ℂ) (g g' : WO S U → ℂ), IsThetaFunO ψ S U g → IsThetaFunO ψ S U g' →
      ptF ψ θ A B (a • g + g') P = a • ptF ψ θ A B g P + ptF ψ θ A B g' P := by
    intro a g g' hg hg'
    induction P using MvPolynomial.induction_on with
    | C b =>
      rw [← mul_one (MvPolynomial.C b), ptF_C, ptF_C, ptF_C, ptF_one, ptF_one, ptF_one, smul_add, smul_comm]
    | add p q hp hq => rw [ptF_add, ptF_add, ptF_add, hp, hq, smul_add]; abel
    | mul_X p v hp =>
      rw [mul_comm p, ptF_X_mul hψ hθ A B (GlobalTheory.OrientedHeis.theta_add (GlobalTheory.OrientedHeis.theta_smul a hg) hg'),
        ptF_X_mul hψ hθ A B hg, ptF_X_mul hψ hθ A B hg', hp,
        GlobalTheory.FockSubst.aPlus_add hψ hθ _ _ _ (GlobalTheory.OrientedHeis.theta_smul a (ptF_theta hψ hθ A B hg p))
          (ptF_theta hψ hθ A B hg' p), GlobalTheory.FockSubst.aPlus_smul hψ hθ _ _ _ a (ptF_theta hψ hθ A B hg p)]
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by rw [Finset.sum_empty]; exact GlobalTheory.OrientedHeis.theta_zero, ?_⟩
    have := lin (-1) 0 0 GlobalTheory.OrientedHeis.theta_zero GlobalTheory.OrientedHeis.theta_zero
    rw [Finset.sum_empty, Finset.sum_empty]
    simpa using this
  | insert i s hi ih =>
    obtain ⟨h1, h2⟩ := ih fun k hk => hf k (Finset.mem_insert_of_mem hk)
    have h3 := hf i (Finset.mem_insert_self _ _)
    rw [Finset.sum_insert hi, Finset.sum_insert hi, lin _ _ _ h3 h1, h2]
    exact ⟨GlobalTheory.OrientedHeis.theta_add (GlobalTheory.OrientedHeis.theta_smul _ h3) h1, rfl⟩

theorem exists_adj_equiv (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (A : Fr S) (B : Fr U) :
    ∃ J : PolF D S.rank U.rank →ₗ[ℂ] PolF D U.rank S.rank, Function.Surjective J ∧ ∀ g, IsVacF ψ θ B A g → ∀ P,
      (fun y => ptF ψ θ B A g P (adjM S U y)) = ptF ψ θ (GlobalTheory.SquareComm.frSgn true A) B (fun y => g (adjM S U y)) (J P) := by
  obtain ⟨j, hjs, hj⟩ := fock_dag D ψ θ hψ hθ U S B A
  have cc : (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ := RingHom.ext fun z => Complex.conj_conj z
  refine ⟨⟨⟨fun P => MvPolynomial.map (starRingEnd ℂ) (j P), fun P Q => by rw [map_add (f := _), map_add (f := _)]⟩, fun c P => ?_⟩,
    fun Q => ⟨j.symm (MvPolynomial.map (starRingEnd ℂ) Q), ?_⟩, fun g hg P => ?_⟩
  · show MvPolynomial.map _ (j (c • P)) = c • MvPolynomial.map _ (j P)
    rw [hjs, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, Complex.conj_conj, MvPolynomial.smul_eq_C_mul]
  · show MvPolynomial.map _ (j (j.symm _)) = _
    rw [AddEquiv.apply_symm_apply, MvPolynomial.map_map, cc, MvPolynomial.map_id]
  obtain ⟨hv, hP⟩ := hj g hg
  have e : ∀ φ : WO U S → ℂ, (fun y => φ (adjM S U y)) = GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (GlobalTheory.PairLift.dag U S φ) := fun φ => by
    funext y
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, id_eq, GlobalTheory.PairLift.dag, Complex.conj_conj]
    rfl
  have hc := GlobalTheory.SquareAlg.isVacF_cj hψ hθ A B hv
  have h := GlobalTheory.FockConjNeg.cj_ptF_neg hψ hθ A B hc.1 (MvPolynomial.map (starRingEnd ℂ) (j P))
  rw [GlobalTheory.CjNeg.cj_id_cj_id, MvPolynomial.map_map, cc, MvPolynomial.map_id, hP] at h
  rw [e g, e, ← h, GlobalTheory.CjNeg.cj_id_cj_id]
  rfl

theorem exists_rd_equiv (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (A : Fr S) (B : Fr U) :
    ∃ J : PolF D S.rank U.rank →ₗ[ℂ] PolF D U.rank S.rank, Function.Surjective J ∧ ∀ g, IsThetaFunO ψ (negSp U) S g → ∀ P,
      rd S U (ptF ψ θ (negFr B) A g P) = ptF ψ θ A B (rd S U g) (J P) := by
  let J : PolF D S.rank U.rank →ₐ[ℂ] PolF D U.rank S.rank := MvPolynomial.aeval fun v =>
    MvPolynomial.C (sgv (negFr B) A v.1 v.2.1 v.2.2) * MvPolynomial.X (v.1, v.2.2, v.2.1)
  have hX : ∀ τ i j, J (MvPolynomial.X (τ, i, j)) = MvPolynomial.C (sgv (negFr B) A τ i j) * MvPolynomial.X (τ, j, i) :=
    fun τ i j => MvPolynomial.aeval_X _ _
  refine ⟨J.toLinearMap, fun Q => ?_, fun g hg P => ?_⟩
  · show Q ∈ J.range
    induction Q using MvPolynomial.induction_on with
    | C a => exact J.range.algebraMap_mem a
    | add p q hp hq => exact add_mem hp hq
    | mul_X p v hp =>
      refine mul_mem hp ⟨MvPolynomial.C (sgv (negFr B) A v.1 v.2.2 v.2.1) * MvPolynomial.X (v.1, v.2.2, v.2.1), ?_⟩
      show J _ = _
      rw [map_mul, hX, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq, ← mul_assoc, ← map_mul, sgv_mul_self, map_one, one_mul]
  show _ = ptF ψ θ A B (rd S U g) (J P)
  induction P using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq, ← mul_one (MvPolynomial.C a : PolF D U.rank S.rank), ptF_C, ptF_one]
    erw [← mul_one (MvPolynomial.C a), ptF_C, ptF_one]
    rfl
  | add p q hp hq =>
    rw [map_add (f := _), ptF_add, ptF_add, ← hp, ← hq]
    rfl
  | mul_X p v hp =>
    obtain ⟨τ, i, j⟩ := v
    rw [map_mul, hX, mul_comm (J p), mul_assoc, ptF_C, ptF_X_mul hψ hθ A B (rd_theta hψ hg), ← hp, mul_comm p]
    erw [ptF_X_mul hψ hθ (negFr B) A hg]
    dsimp only
    have e := cdag_unitMap (negFr B) A τ i j
    have e' : (negFr B).onb τ = B.onb τ := rfl
    rw [aPlus_rd hψ hθ, ← e', e, aPlus_real_smul hψ hθ (ptF_theta hψ hθ (negFr B) A hg p)]
    funext x
    have := sgv_mul_self (negFr B) A τ i j
    simp only [rd, Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc]
    change _ = (sgv (negFr B) A τ i j * sgv (negFr B) A τ i j) * _
    rw [this, one_mul]

theorem exists_iota (S U U' : HSp D) (J : PolF D S.rank U'.rank →ₗ[ℂ] PolF D U'.rank S.rank) (hJ : Function.Surjective J) :
    ∃ ι : PolF D U.rank S.rank ⊗[ℂ] PolF D S.rank U'.rank →ₗ[ℂ] PolF D (GlobalTheory.Doubling.hsum U U').rank S.rank,
      Function.Surjective ι ∧ ∀ P Q, ι (P ⊗ₜ Q) = GlobalTheory.SquareRel.polTens (sumVar U U' S.rank) (P ⊗ₜ J Q) :=
  ⟨(GlobalTheory.SquareRel.polTens (sumVar U U' S.rank)).toLinearMap ∘ₗ LinearMap.lTensor _ J, fun x => by
    obtain ⟨y, rfl⟩ := (GlobalTheory.SquareRel.polTens (sumVar U U' S.rank)).surjective x
    obtain ⟨z, rfl⟩ := LinearMap.lTensor_surjective _ hJ y
    exact ⟨z, rfl⟩, fun _ _ => rfl⟩

theorem sum_tens {P Q Z Y Pl : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup Q] [Module ℂ Q] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Pl] [Module ℂ Pl] (zip : Z → (Unit × P) × Q → Z) (F : Z → Y) (ι : P ⊗[ℂ] Q →ₗ[ℂ] Pl) (Ψ : Pl →ₗ[ℂ] Y)
    (τ : Z →₀ ℂ) (h : ∀ d : (Unit × P) × Q, Ψ (ι (d.1.2 ⊗ₜ d.2)) = τ.sum fun z c => c • F (zip z d)) (a : (Unit × P) × Q →₀ ℂ) :
    (a.sum fun d c => τ.sum fun z c' => Finsupp.single (zip z d) (c * c')).sum (fun z c => c • F z) = Ψ (ι (toTens a)) := by
  rw [Finsupp.sum_sum_index (h := fun z (c : ℂ) => c • F z) (fun _ => zero_smul _ _) fun _ _ _ => add_smul _ _ _, toTens, Finsupp.linearCombination_apply,
    map_finsuppSum, map_finsuppSum]
  refine Finset.sum_congr rfl fun d _ => ?_
  dsimp only
  rw [Finsupp.sum_sum_index (h := fun z (c : ℂ) => c • F z) (fun _ => zero_smul _ _) fun _ _ _ => add_smul _ _ _, map_smul, map_smul, h, Finsupp.smul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  dsimp only
  rw [Finsupp.sum_single_index (h := fun z (c : ℂ) => c • F z) (zero_smul _ _), mul_smul]

end Real


open GlobalTheory.FockAdjoint GlobalTheory.RouteSeesaw in
theorem realA : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (i j : Fin D.R.m)
    (A : Fr (G.V (.grid (↑i + 1) (↑j + 1)))) (AV : Fr (G.V (.grid ↑i (↑j + 1)))) (AV₁ : Fr (G.V (.grid (↑i + 1) ↑j))),
    GlobalTheory.SquareDict.IsGridFr W _ A → GlobalTheory.SquareDict.IsGridFr W _ AV → GlobalTheory.SquareDict.IsGridFr W _ AV₁ →
    ∃ ι : PolRoute G (.grid i (j + 1)) (.grid (i + 1) (j + 1)) (.grid (i + 1) j) →ₗ[ℂ] PolF D (GlobalTheory.Doubling.hsum (G.V (.grid ↑i (↑j + 1))) (G.V (.grid (↑i + 1) ↑j))).rank (G.V (.grid (↑i + 1) (↑j + 1))).rank,
      Function.Surjective ι ∧ ∀ (t : T) (B : Frames G) (ρ : RealMatch W) n Φ (τ : TotT G (routeBig t i j)) τ', HasFlip B t ρ i j n Φ τ τ' →
        ∀ a : PolT G (routeBig t i j) →₀ ℂ, GlobalTheory.SquareDict.datumA W (tensT W a τ) =
          GlobalTheory.SquareComm.fockF W.ψ W.θ true A (GlobalTheory.SquareComm.frSum AV AV₁) (GlobalTheory.SquareDict.datumA W τ) (ι (toTens a)) := by
  intro D T L sc G μ₀ _ W i j A AV AV₁ hA hV hV₁
  obtain ⟨J, hJ, hJ'⟩ := exists_adj_equiv W.ψ_std W.θ_is A AV₁
  obtain ⟨ι, hι, hι'⟩ := exists_iota (G.V (.grid (↑i + 1) (↑j + 1))) (G.V (.grid ↑i (↑j + 1))) (G.V (.grid (↑i + 1) ↑j)) J hJ
  refine ⟨ι, hι, fun t B ρ n Φ τ τ' hF a => ?_⟩
  obtain ⟨e, he, -, φ₁, φ₂, hφ, -⟩ := hF
  have v₁ := (ρ.vX_is i (j + 1) i.2 j.2).2
  have v₂ := (ρ.vT_is t (i + 1) j i.2 j.2).2
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he
  have cA : (GlobalTheory.SquareComm.frSgn true A).cart = fun τ => -W.cart (.grid (↑i + 1) (↑j + 1)) τ := funext fun τ =>
    (GlobalTheory.PairLift.cart_frSgn true A τ).trans (congrArg Neg.neg (hA τ).2)
  have cA' : A.cart = W.cart _ := funext fun τ => (hA τ).2
  have cV : AV.cart = W.cart _ := funext fun τ => (hV τ).2
  have cV₁ : AV₁.cart = W.cart _ := funext fun τ => (hV₁ τ).2
  have oA : A.onb = W.onb _ := funext fun τ => (hA τ).1
  have oV : AV.onb = W.onb _ := funext fun τ => (hV τ).1
  have oV₁ : AV₁.onb = W.onb _ := funext fun τ => (hV₁ τ).1
  have t₁ := fun d hd => GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is (hφ d hd).1.2 v₁.2
  have t₂ := fun d hd => GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is (hφ d hd).2.2 v₂.2
  have w₂ : ∀ d ∈ τ.support, IsVacF W.ψ W.θ AV₁ A d.2 := fun d hd => ⟨t₂ d hd, fun τ => by
    rw [cA', cV₁]
    exact GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt W.ψ_std.1.1 W.θ_is ho.infPart_eq ho.conj.infPart_eq (hφ d hd).2.2 v₂.theta
      (t₂ d hd) (v₂.fock τ)⟩
  have t₃ := fun d hd => (GlobalTheory.SquareAlg.adj_ptF W.ψ_std W.θ_is A AV₁ (w₂ d hd)).1.1
  refine sum_tens (Z := PureT G (routeBig t i j)) (fun d (P : PolT G (routeBig t i j)) =>
      Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d P)
    (fun d => box2 (S := negSp (G.V (.grid (↑i + 1) (↑j + 1)))) (A := (G.V (.grid ↑i (↑j + 1)))) (B := (G.V (.grid (↑i + 1) ↑j))) d.1.2 fun y => d.2 (adjM (G.V (.grid (↑i + 1) (↑j + 1))) (G.V (.grid (↑i + 1) ↑j)) y)) ι
    (GlobalTheory.SquareComm.fockF W.ψ W.θ true A (GlobalTheory.SquareComm.frSum AV AV₁) (GlobalTheory.SquareDict.datumA W τ)) τ (fun P => ?_) a
  rw [hι']
  refine (ptF_sum W.ψ_std W.θ_is (GlobalTheory.SquareComm.frSgn true A) (GlobalTheory.SquareComm.frSum AV AV₁) τ.support τ _
    (fun d hd => GlobalTheory.SquareDict.AlgSmall.isThetaFunction_externalProductOnHermitianSum (t₁ d hd) (t₃ d hd)) _).2.trans (Finset.sum_congr rfl fun d hd => ?_)
  have e₁ : W.fock (.chi i (j + 1)) d.1.2 P.1.2 = ptF W.ψ W.θ (GlobalTheory.SquareComm.frSgn true A) AV d.1.2 P.1.2 := by
    unfold ptF
    rw [cA, cV, oV, show (GlobalTheory.SquareComm.frSgn true A).onb = W.onb _ from oA]
    rfl
  have e₂ : W.fock (.mu t (i + 1) j) d.2 P.2 = ptF W.ψ W.θ AV₁ A d.2 P.2 := by
    unfold ptF
    rw [cA', cV₁, oA, oV₁]
    rfl
  have key := fockVector_product_mul_polynomials W.ψ_std W.θ_is (GlobalTheory.SquareComm.frSgn true A) AV AV₁ (t₁ d hd) (t₃ d hd) P.1.2 (J P.2)
  rw [← hJ' _ (w₂ d hd), ← e₁, ← e₂] at key
  exact congrArg (τ d • ·) key.symm


open GlobalTheory.FockAdjoint GlobalTheory.RouteSeesaw GlobalTheory.SquareDict.AlgSmall in
theorem realB : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (i j : Fin D.R.m)
    (A₁ : Fr (G.V (.grid ↑i ↑j))) (AV : Fr (G.V (.grid ↑i (↑j + 1)))) (AV₁ : Fr (G.V (.grid (↑i + 1) ↑j))),
    GlobalTheory.SquareDict.IsGridFr W _ A₁ → GlobalTheory.SquareDict.IsGridFr W _ AV → GlobalTheory.SquareDict.IsGridFr W _ AV₁ →
    ∃ ι : PolRoute G (.grid i (j + 1)) (.grid i j) (.grid (i + 1) j) →ₗ[ℂ] PolF D (GlobalTheory.Doubling.hsum (G.V (.grid ↑i (↑j + 1))) (G.V (.grid (↑i + 1) ↑j))).rank (G.V (.grid ↑i ↑j)).rank,
      Function.Surjective ι ∧ ∀ (t : T) (B : Frames G) (ρ : RealMatch W) n Φ τ (τ' : TotT G (routeSmall t i j)), HasFlip B t ρ i j n Φ τ τ' →
        ∀ b : PolT G (routeSmall t i j) →₀ ℂ, GlobalTheory.SquareDict.datumB W (tensT W b τ') =
          GlobalTheory.SquareComm.fockF W.ψ W.θ false A₁ (GlobalTheory.SquareComm.frSum AV AV₁) (GlobalTheory.SquareDict.datumB W τ') (ι (toTens b)) := by
  intro D T L sc G μ₀ _ W i j A₁ AV AV₁ h₁ hV hV₁
  obtain ⟨J, hJ, hJ'⟩ := exists_rd_equiv W.ψ_std W.θ_is A₁ AV₁
  obtain ⟨ι, hι, hι'⟩ := exists_iota (G.V (.grid ↑i ↑j)) (G.V (.grid ↑i (↑j + 1))) (G.V (.grid (↑i + 1) ↑j)) J hJ
  refine ⟨ι, hι, fun t B ρ n Φ τ τ' hF a => ?_⟩
  obtain ⟨e, he, ⟨φ₁, φ₂, hφ, -⟩, -⟩ := hF
  have v₁ := ρ.vT_is t i j i.2.le j.2
  have v₂ := ρ.vX_is i j i.2 j.2.le
  have t₁ := fun d hd => GlobalTheory.VecTheta.isThetaFunO_of_thetaAt W.ψ_std W.θ_is (hφ d hd).1.2 v₁.2.theta
  have t₂ := fun d hd => GlobalTheory.VecTheta.isThetaFunO_of_thetaAt W.ψ_std W.θ_is (hφ d hd).2.2 v₂.2.theta
  have c₁ : A₁.cart = W.cart _ := funext fun s => (h₁ s).2
  have cV : AV.cart = W.cart _ := funext fun s => (hV s).2
  have cV₁ : (negFr AV₁).cart = fun s => -W.cart (.grid (i + 1) j) s := funext fun s => by rw [negFr_cart, (hV₁ s).2]
  have o₁ : A₁.onb = W.onb _ := funext fun s => (h₁ s).1
  have oV : AV.onb = W.onb _ := funext fun s => (hV s).1
  have oV₁ : (negFr AV₁).onb = W.onb (.grid (i + 1) j) := funext fun s => (hV₁ s).1
  have ec : (GlobalTheory.SquareComm.frSgn false A₁).cart = A₁.cart := funext (frSgn_false_cart A₁)
  have t₃ := fun d hd => rd_theta W.ψ_std (t₂ d hd)
  refine sum_tens (Z := PureT G (routeSmall t i j)) (fun d (P : PolT G (routeSmall t i j)) =>
      Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d P)
    (fun d => box2 (S := (G.V (.grid ↑i ↑j))) (A := (G.V (.grid ↑i (↑j + 1)))) (B := (G.V (.grid (↑i + 1) ↑j))) d.1.2 fun y => d.2 (adjM (G.V (.grid ↑i ↑j)) (negSp (G.V (.grid (↑i + 1) ↑j))) y)) ι
    (GlobalTheory.SquareComm.fockF W.ψ W.θ false A₁ (GlobalTheory.SquareComm.frSum AV AV₁) (GlobalTheory.SquareDict.datumB W τ')) τ' (fun P => ?_) a
  have ef : ∀ f Q, GlobalTheory.SquareComm.fockF W.ψ W.θ false A₁ (GlobalTheory.SquareComm.frSum AV AV₁) f Q =
      ptF W.ψ W.θ A₁ (GlobalTheory.SquareComm.frSum AV AV₁) f Q := fun f Q => by
    unfold GlobalTheory.SquareComm.fockF
    rw [ec]; rfl
  rw [hι', ef]
  refine (ptF_sum W.ψ_std W.θ_is A₁ (GlobalTheory.SquareComm.frSum AV AV₁) τ'.support τ' _
    (fun d hd => isThetaFunction_externalProductOnHermitianSum (t₁ d hd) (t₃ d hd)) _).2.trans (Finset.sum_congr rfl fun d hd => ?_)
  have key := fockVector_product_mul_polynomials W.ψ_std W.θ_is A₁ AV AV₁ (t₁ d hd) (t₃ d hd) P.1.2 (J P.2)
  rw [← hJ' _ (t₂ d hd)] at key
  refine congrArg (τ' d • ·) (key.symm.trans ?_)
  unfold ptF
  rw [c₁, cV, cV₁, o₁, oV, oV₁]
  rfl

section Fock

open GlobalTheory.SquareComm GlobalTheory.SquareAgree GlobalTheory.Grid GlobalTheory.FockAdjoint
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (SInf)

variable {D : D7} {S X : HSp D} {d : ℕ} {Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank}
  {Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d}

def FockRel (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (ε : Bool) (A : Fr S)
    (B : Fr X) (cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X) (f₀ : SInf D.host.F (Fin S.rank × Fin d))
    (P : PolF D X.rank S.rank) (f : SInf D.host.F (Fin S.rank × Fin d)) : Prop :=
  ∀ φ : ∀ v : HeightOneSpectrum (𝓞 D.host.F), (Fin S.rank × Fin d → v.adicCompletion D.host.F) → ℂ,
    (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) → ∀ F : WO S X → ℂ,
      IsDatum M ψ cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ φ) F → IsDatum M ψ cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) (fockF ψ θ ε A B F P)

theorem fock_datum {θ : InfFam D} (hθ : IsInfFam θ) (ε : Bool) (A : Fr S) (B : Fr X) (e : Fin X.rank ≃ Fin d)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (hBs : Bs.IsGood D.sp.cm.sig) {r s r' s' : ℕ}
    (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ)
    (hV : Vs.IsHerm D.sp.cm.sig Bs r s) (hW : Ws.IsSkew D.sp.cm.sig Bs r' s')
    (hemb : ∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
      Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ))
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws) (hM : M.IsGood Bs.ψ) (cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X)
    (hcS : ∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) :
      Matrix (Fin X.rank) (Fin S.rank) (AE D)))
    {f₀ : SInf D.host.F (Fin S.rank × Fin d)} (hG : M.IsGauss Bs.ψ Bs.emb f₀) :
    (∀ φ, (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) → ∀ F : WO S X → ℂ,
      IsDatum M Bs.ψ cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ φ) F → IsFinF Bs.ψ θ ε A B F) ∧
    (∀ P, ∃ f ∈ M.Pol Bs.ψ Bs.emb, FockRel M Bs.ψ θ ε A B cS f₀ P f) ∧
    ((∀ g, M.IsGauss Bs.ψ Bs.emb g → ∃ c : ℂ, g = c • f₀) → ∀ f ∈ M.Pol Bs.ψ Bs.emb, ∃ P, FockRel M Bs.ψ θ ε A B cS f₀ P f) := by
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd Bs.ψ := hBs.std
  have hψ : IsStdChar D Bs.ψ (-1) := GlobalTheory.StdCharFromIsStd.isStdChar_of_isStd D Bs.ψ hstd
  have fin : ∀ φ, (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) → ∀ F : WO S X → ℂ,
      IsDatum M Bs.ψ cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ φ) F → IsFinF Bs.ψ θ ε A B F := fun φ h1 h2 F hF => by
    obtain ⟨F', a, b⟩ := GlobalTheory.T.thetaTransform_gaussianVacuum_isFiniteDatum D Bs.ψ θ hθ ε S X A B e Bs hBs rfl Vs Ws r s r' s' hJ hJW hV hW hemb M hM cS hcS f₀ φ hG h1 h2
    obtain rfl : F = F' := funext fun x => by
      obtain ⟨u, rfl⟩ := cS.surjective x
      exact (hF.2 u).symm.trans (b.2 u)
    exact a
  have L := GlobalTheory.SquareAgree.isDatum_linear M Bs.ψ hstd cS
  have lin : ∀ (c : ℂ) P f P' f', FockRel M Bs.ψ θ ε A B cS f₀ P f → FockRel M Bs.ψ θ ε A B cS f₀ P' f' →
      FockRel M Bs.ψ θ ε A B cS f₀ (P + c • P') (f + c • f') := fun c P f P' f' h h' φ h1 h2 F hF => by
    rw [GlobalTheory.BigNZ.DatReal.pure_add, GlobalTheory.BigNZ.DatReal.pure_smul, map_add (f := _), map_smul]
    exact L.2 _ _ _ _ c (h φ h1 h2 F hF) (h' φ h1 h2 F hF)
  have zero : FockRel M Bs.ψ θ ε A B cS f₀ 0 0 := fun φ _ _ F _ => by
    rw [GlobalTheory.BigNZ.DatReal.pure_zero, map_zero]; exact L.1
  have one : FockRel M Bs.ψ θ ε A B cS f₀ 1 f₀ := fun φ _ _ F hF => by
    rw [show fockF Bs.ψ θ ε A B F 1 = F from ptF_one (frSgn ε A) B F]; exact hF
  have h0 : f₀ ∈ M.Pol Bs.ψ Bs.emb := Submodule.mem_sInf.2 fun N hN => hN.1 _ hG
  refine ⟨fin, fun P => ?_, fun hu => ?_⟩
  · induction P using MvPolynomial.induction_on with
    | C a =>
      refine ⟨0 + a • f₀, add_mem (zero_mem _) (Submodule.smul_mem _ a h0), ?_⟩
      have := lin a _ _ _ _ zero one
      rwa [zero_add, ← MvPolynomial.C_eq_smul_one] at this
    | add p q hp hq =>
      obtain ⟨f, a, b⟩ := hp
      obtain ⟨f', a', b'⟩ := hq
      refine ⟨f + f', add_mem a a', ?_⟩
      simpa only [one_smul] using lin 1 _ _ _ _ b b'
    | mul_X p v hp =>
      obtain ⟨f, a, b⟩ := hp
      have der : ∀ z : Matrix (Fin X.rank) (Fin S.rank) ℂ, ∃ g ∈ M.Pol Bs.ψ Bs.emb, ∀ φ, (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) →
          (∀ᶠ v in Filter.cofinite, φ v = M.vac v) → ∀ F : WO S X → ℂ, IsDatum M Bs.ψ cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) F →
          IsDatum M Bs.ψ cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) (dRho (heisO Bs.ψ (sgn ε S) X) θ v.1 z F) := fun z => by
        have hat := GlobalTheory.T.archimedean_preimage_realPlace_line D θ hθ ε S X e cS hcS v.1 z
        obtain ⟨g, hg⟩ := GlobalTheory.T.exists_heisenberg_derivative_archimedean_direction M Bs.ψ hstd f _ hat
        exact ⟨g, Submodule.mem_sInf.2 fun N hN => hN.2 _ hat f (Submodule.mem_sInf.1 a N hN) g hg, fun φ h1 h2 F hF =>
          GlobalTheory.T.heisenbergDerivative_realPlace_pureDatum D Bs.ψ θ hθ ε S X A B e Bs hBs rfl Vs Ws r s r' s' hJ hJW hV hW hemb M hM cS hcS f φ h1 h2 F hF v.1 z g hg⟩
      obtain ⟨g₁, a₁, b₁⟩ := der (unitMap (A.onb v.1) (B.onb v.1) v.2.1 v.2.2)
      obtain ⟨g₂, a₂, b₂⟩ := der (cplxO ((frSgn ε A).cart v.1) (B.cart v.1) (unitMap (A.onb v.1) (B.onb v.1) v.2.1 v.2.2))
      refine ⟨0 + (fockScale D v.1 : ℂ)⁻¹ • (g₁ + (-Complex.I) • g₂), add_mem (zero_mem _) (Submodule.smul_mem _ _
        (add_mem a₁ (Submodule.smul_mem _ _ a₂))), fun φ h1 h2 F hF => ?_⟩
      have k := L.2 _ _ _ _ (fockScale D v.1 : ℂ)⁻¹ L.1
        (L.2 _ _ _ _ (-Complex.I) (b₁ φ h1 h2 _ (b φ h1 h2 F hF)) (b₂ φ h1 h2 _ (b φ h1 h2 F hF)))
      rw [GlobalTheory.BigNZ.DatReal.pure_add, GlobalTheory.BigNZ.DatReal.pure_smul, GlobalTheory.BigNZ.DatReal.pure_add, GlobalTheory.BigNZ.DatReal.pure_smul,
        GlobalTheory.BigNZ.DatReal.pure_zero, mul_comm p, show fockF Bs.ψ θ ε A B F (MvPolynomial.X v * p) = _ from
          ptF_X_mul hψ hθ (frSgn ε A) B (fin φ h1 h2 F hF).1 p v, aPlus, crea, sub_eq_add_neg, ← neg_smul]
      rw [zero_add (M := WO S X → ℂ)] at k
      exact k
  · let N : Submodule ℂ (SInf D.host.F (Fin S.rank × Fin d)) :=
      { carrier := {f | ∃ P, FockRel M Bs.ψ θ ε A B cS f₀ P f}
        zero_mem' := ⟨0, zero⟩
        add_mem' := by
          rintro f f' ⟨P, h⟩ ⟨P', h'⟩
          exact ⟨_, by simpa only [one_smul] using lin 1 _ _ _ _ h h'⟩
        smul_mem' := by
          rintro c f ⟨P, h⟩
          exact ⟨_, by simpa only [zero_add] using lin c _ _ _ _ zero h⟩ }
    have hle : M.Pol Bs.ψ Bs.emb ≤ N := sInf_le ⟨fun g hg => ?_, fun u hu f ⟨P, hP⟩ f₁ h₁ => ?_⟩
    · exact fun f hf => hle hf
    · obtain ⟨c, rfl⟩ := hu g hg
      exact N.smul_mem c ⟨1, one⟩
    choose Lp hLp using fun τ => GlobalTheory.SquareComm.AlgDeriv.exists_dRho_pure_all (S := sgn ε S) (T := X) hψ hθ (frSgn ε A).cart
      (frSgn ε A).fr (frSgn ε A).ε B.cart B.fr B.ε (fun ρ => ⟨(frSgn ε A).fr_unit ρ, (frSgn ε A).fr_gram ρ, rfl⟩)
      (fun ρ => ⟨B.fr_unit ρ, B.fr_gram ρ, rfl⟩) τ (compAt θ τ (cS u))
    have hsm : ∀ (a : AF D.host.F) (v : Matrix (Fin S.rank) (Fin d) (AE D)), cS (a • v) = a • cS v := by
      intro a v
      rw [hcS, hcS]
      ext i j
      simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.smul_apply, Finset.smul_sum,
        smul_mul_assoc, id]
    have hAt : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (cS u) := by
      intro a ha
      rw [← hsm, hu a ha, map_zero]
    refine ⟨∑ τ, Lp τ P, fun φ hφ hvac F hF => ⟨?_, fun u' => ?_⟩⟩
    · exact GlobalTheory.TensUniq.pure_mem_schA f₁ φ hφ ((hvac.and hM.std).mono fun v hv => hv.1.trans hv.2)
    have hF' := fin φ hφ hvac F hF
    have hD := hP φ hφ hvac F hF
    have h2 := GlobalTheory.T.hasDerivAt_thetaSum_archimedeanHeisenbergLine M Bs.ψ hstd hM u hu f f₁ φ hφ hvac h₁ u'
    have h3 := GlobalTheory.T.hasDerivAt_heisenbergOp_archimedean_sum_realPlaces D Bs.ψ θ hψ hθ (sgn ε S) X _ (ptF_theta hψ hθ (frSgn ε A) B hF'.1 P) (cS u) hAt (cS u')
    have heq : (fun t : ℝ => GlobalTheory.WeilM.thetaSum D.host.F (M.co.rho Bs.ψ u' (M.heisLine Bs.ψ u t (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ)))) =
        fun t : ℝ => heisO Bs.ψ (sgn ε S) X (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • cS u) (ptF Bs.ψ θ (frSgn ε A) B F P) (cS u') := by
      funext t
      have h4 := (GlobalTheory.T.schrodingerThetaDatum_heisenberg_oriented D Bs.ψ θ hθ ε S X A B e Bs hBs rfl Vs Ws r s r' s' hJ hJW hV hW hemb M hM cS hcS
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) _ hD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u)).2 u'
      rw [hsm] at h4
      exact h4
    rw [heq] at h2
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h2.unique h3, map_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun τ _ => congrFun (hLp τ F hF'.1 (hF'.2 τ) P) _

end Fock

end GlobalTheory.SquareIdent

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.ChainFr Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.SquareIdent

section Core

open GlobalTheory.SquareComm GlobalTheory.SquareAgree GlobalTheory.Grid GlobalTheory.TripleRead GlobalTheory.TripleAssembly GlobalTheory.RouteSeesaw
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (incM)

variable {D : D7}

theorem eq_thO {S X : HSp D} {d : ℕ} {Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank}
    {Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws) (ψ : AddChar (AF D.host.F) ℂ)
    (e : Fin d ≃ Fin X.rank) {Gm : Matrix (Fin S.rank) (Fin S.rank) D.host.E} (hG : Gm.det ≠ 0)
    (cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X)
    (hcS : ∀ u, cS u = (HMul.hMul (uᵀ.submatrix e.symm id) (incM Gm) : Matrix (Fin X.rank) (Fin S.rank) (AE D)))
    {Φ} {F : WO S X → ℂ} (h : IsDatum M ψ cS Φ F) : F = thO M ψ Gm e Φ := by
  funext x
  obtain ⟨u, rfl⟩ := cS.surjective x
  have e1 : incM Gm * incM Gm⁻¹ = 1 := by
    show Gm.map (incA D) * (Gm⁻¹).map (incA D) = 1
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (Ne.isUnit hG), Matrix.map_one _ (map_zero _) (map_one _)]
  have e2 : ptO Gm e (cS u) = u := by
    rw [hcS, ptO, Matrix.mul_assoc, e1, Matrix.mul_one]
    ext a b
    simp
  rw [thO, e2, h.2]

theorem adjM_coord (S B : HSp D) (y : Matrix (Fin S.rank) (Fin B.rank) (AE D)) :
    adjM S B (HMul.hMul yᵀ (incM S.gram) : Matrix (Fin B.rank) (Fin S.rank) (AE D)) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mulG B (y.map (cA D)) := by
  have e0 : ((incM S.gram).map (cA D))ᵀ = incM S.gram := by
    ext a b
    exact congrArg (incA D) (GlobalTheory.TripleSpace.star_gram S b a)
  have e1 : (S.gram⁻¹).map (incA D) * incM S.gram = 1 := by
    show (S.gram⁻¹).map (incA D) * S.gram.map (incA D) = 1
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (Ne.isUnit (GlobalTheory.RouteCoords.gram_det_ne S)),
      Matrix.map_one _ (map_zero _) (map_one _)]
  unfold adjM GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mulG
  rw [Matrix.map_mul, Matrix.transpose_mul, e0, ← Matrix.mul_assoc, e1, Matrix.one_mul]
  rfl

theorem adjM_neg (S B : HSp D) (y : Mx D B.rank S.rank) : adjM S B (-y) = -adjM S B y :=
  eq_neg_of_add_eq_zero_left (by rw [← adjM_add, neg_add_cancel, adjM_zero])

theorem thetaLift_pure {m k d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E m} {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E k}
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Y Z) {ψ : AddChar (AF D.host.F) ℂ} (hM : Mo.IsGood ψ) (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ)
    (hY : Y.J.det ≠ 0) (hZ : Z.J.det ≠ 0) {Gm : Matrix (Fin m) (Fin m) D.host.E} (hG : Gm.det ≠ 0) (e : Fin k ≃ Fin d) (τ)
    {P : Type} [AddCommGroup P] [Module ℂ P] (pr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin m × Fin k) →ₗ[ℂ] P)
    {N : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F) → Type} [∀ v, AddCommGroup (N v)] [∀ v, Module ℂ (N v)]
    (pv : ∀ v, ((Fin m × Fin k → Fv D.host.F v) → ℂ) →ₗ[ℂ] N v) (s : ∀ v, N v)
    (hs : ∀ᶠ v in Filter.cofinite, pv v (Mo.vac v) = s v) {f} (hf : f ∈ Mo.Pol ψ τ) {φ} (h1 : ∀ v, φ v ∈ GlobalTheory.WeilM.SB _)
    (h2 : ∀ᶠ v in Filter.cofinite, φ v = Mo.vac v) :
    thetaLift Mo ψ Gm e (darbAlg Mo ψ τ) (liftPure Mo pr pv s) (thO Mo ψ Gm e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ)) =
      pr f ⊗ₜ GlobalTheory.SmallThetaModules.pureT s fun v => pv v (φ v) := by
  obtain ⟨T, hT, hinj⟩ := GlobalTheory.T.thetaTransform_darbouxModel_linear_injective D Mo ψ Gm e hM hψ hY hZ hG
  have hS := GlobalTheory.T.darbouxModelAlgebraicVectors_le_adelicSchwartz _ _ _ Mo ψ τ hM
  have H : ∃ q : (Matrix (Fin d) (Fin m) (AE D) → ℂ) →ₗ[ℂ] _, ∀ Ψ ∈ darbAlg Mo ψ τ,
      q (thO Mo ψ Gm e Ψ) = liftPure Mo pr pv s Ψ := by
    obtain ⟨q, hq⟩ := GlobalTheory.TripleAssembly.Onto.exists_factor T _ (fun x hx => hinj x (hS hx)) (liftPure Mo pr pv s)
    exact ⟨q, fun Ψ hΨ => by rw [← hT Ψ (hS hΨ)]; exact hq Ψ hΨ⟩
  have H' := GlobalTheory.T.weil_model_projection_factorisation _ Y Z Mo ψ hM P pr N pv s hs
  rw [thetaLift, dite_eq_left H, H.choose_spec _ (Submodule.subset_span ⟨f, φ, hf, h1, h2, rfl⟩), liftPure, dite_eq_left H']
  exact H'.choose_spec f φ h1 h2

theorem blkMat_submatrix {R : Type} [CommRing R] {p q d : ℕ} (e : Fin p ⊕ Fin q ≃ Fin d) (A : Matrix (Fin p) (Fin p) R)
    (B : Matrix (Fin q) (Fin q) R) : (GlobalTheory.Doubling.blkMat finSumFinEquiv A B).submatrix (e.symm.trans finSumFinEquiv)
      (e.symm.trans finSumFinEquiv) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e A B := by
  ext a b
  simp [GlobalTheory.Doubling.blkMat, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk]

theorem rows_coord {U U' : HSp D} {n d : ℕ} (e : Fin U.rank ⊕ Fin U'.rank ≃ Fin d) (u : Matrix (Fin n) (Fin d) (AE D))
    (Gm : Matrix (Fin n) (Fin n) (AE D)) :
    topR (A := U) (B := U') (HMul.hMul (uᵀ.submatrix (e.symm.trans finSumFinEquiv).symm id) Gm) =
      (HMul.hMul (u.submatrix id fun k => e (.inl k))ᵀ Gm : Matrix (Fin U.rank) (Fin n) (AE D)) ∧
    botR (A := U) (B := U') (HMul.hMul (uᵀ.submatrix (e.symm.trans finSumFinEquiv).symm id) Gm) =
      (HMul.hMul (u.submatrix id fun k => e (.inr k))ᵀ Gm : Matrix (Fin U'.rank) (Fin n) (AE D)) := by
  constructor <;> ext a b <;> simp [topR, botR, Matrix.mul_apply]

theorem gauss_small {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    {B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E} {Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a'} (hb : B.IsGood σ) (hgeo : Γ.IsGood B) {f₀} (hf₀ : f₀ ≠ 0)
    (hG₀ : Γ.M'.IsGauss B.ψ B.emb f₀) (g) (hg : Γ.M'.IsGauss B.ψ B.emb g) : ∃ c : ℂ, g = c • f₀ := by
  choose A hA hAθ using fun w => GlobalTheory.T.cartanEigen_orthonormalFrame_exists _ _ _ _ _ (hgeo.hV'.sig w) (hgeo.hV'.cartan w)
  choose C hC hCθ using fun w => GlobalTheory.T.cartanEigen_orthonormalFrame_exists _ _ _ _ _ (hgeo.hW.sig w) (hgeo.hW.cartan w)
  have fr : GlobalTheory.RealLift.Framed B.emb (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Γ.V'.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Γ.W.J) 1 Complex.I A C :=
    ⟨one_mul _, fun w => by rw [GlobalTheory.GaussLine.incM_map_piInf', one_smul]; exact hA w,
      fun w => by rw [GlobalTheory.GaussLine.incM_map_piInf']; exact hC w⟩
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.fockToSchrodingerMapExists_of_archHeisenbergDerivatives GlobalTheory.T.archHeisenbergDerivatives_exist F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ Γ.M'.co 1 Complex.I A C hb.cm hb.std fr
  have toD : ∀ u (f f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a'))),
      GlobalTheory.RealLift.SD (fun t => Γ.M'.co.rho B.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd F t • u)) f f₁ →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (Γ.M'.heisLine B.ψ u) f f₁ :=
    fun u f f₁ h => (GlobalTheory.T.archActionReadings_compatible F (Fin a' × Fin (a + a')) f f₁ f₁).1 _
      (fun t => by funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.heisLine, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]) h
  have line : ∀ f, Γ.M'.IsGauss B.ψ B.emb f → ∃ z : ℂ, f = z • Φ (PiTensorProduct.tprod ℂ fun _ => 1) := by
    rintro f ⟨ε, hε⟩
    refine GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives GlobalTheory.T.archHeisenbergDerivatives_exist F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ Γ.M'.co 1 Complex.I A C Φ hb.cm hb.std fr hΦ f ε
      (fun u u' hu hu' c hc hc' f1 f1' hf hf' => hε u u' hu hu' (fun w => ?_) f1 f1' (toD _ _ _ hf) (toD _ _ _ hf'))
    have h2 := congrArg Matrix.transpose (hCθ w)
    rw [Matrix.transpose_mul, Matrix.transpose_mul, GlobalTheory.GaussLine.Jm_transpose''] at h2
    rw [hc' w, hc w]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, h2]
    rw [← Matrix.mul_assoc (Γ.V'.θ w), hAθ w, Matrix.mul_assoc]
  obtain ⟨z, hz⟩ := line f₀ hG₀
  obtain ⟨z', hz'⟩ := line g hg
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact hf₀ (by rw [hz, zero_smul])
  exact ⟨z' / z, by rw [hz', hz, smul_smul, div_mul_cancel₀ _ hz0]⟩


end Core

section Read

open GlobalTheory.SquareAgree GlobalTheory.TripleRead GlobalTheory.RouteSeesaw
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (incM IsDatumA IsDatumB Num mulG colV adjV₁)

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {t : T} {i j : ℕ} {e : Num G i j}
  {Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j}

theorem isDatum_of_isDatumA {τ : TotT G (routeBig t i j)} {Φ} (h : IsDatumA W e Γ τ Φ) :
    IsDatum Γ.M W.ψ (fun u => (HMul.hMul (uᵀ.submatrix (e.symm.trans finSumFinEquiv).symm id)
      (incM (GlobalTheory.Grid.sgn true (G.V (.grid (i + 1) (j + 1)))).gram) : Matrix (Fin (_ + _)) (Fin _) (AE D))) Φ
      (GlobalTheory.SquareDict.datumA W τ) := by
  refine ⟨h.1, fun u => (h.2 u).trans (Eq.symm ((Finset.sum_apply _ _ _).trans (Finset.sum_congr rfl fun d _ => ?_)))⟩
  have e3 : incM (GlobalTheory.Grid.sgn true (G.V (.grid (i + 1) (j + 1)))).gram = -incM (G.V (.grid (i + 1) (j + 1))).gram :=
    Matrix.ext fun a b => map_neg (incA D) _
  have e2 : adjM (G.V (.grid (i + 1) (j + 1))) (G.V (.grid (i + 1) j)) (HMul.hMul (u.submatrix id fun k => e (.inr k))ᵀ
      (incM (GlobalTheory.Grid.sgn true (G.V (.grid (i + 1) (j + 1)))).gram) :
        Matrix (Fin (G.V (.grid (i + 1) j)).rank) (Fin (G.V (.grid (i + 1) (j + 1))).rank) (AE D)) = adjV₁ e u := by
    rw [adjV₁, ← adjM_coord, ← adjM_neg, e3]
    exact congrArg _ (Matrix.mul_neg _ _)
  dsimp only
  rw [Pi.smul_apply, box2, (rows_coord e u _).1, (rows_coord e u _).2, e2]
  rfl

theorem isDatum_of_isDatumB {τ : TotT G (routeSmall t i j)} {Φ} (h : IsDatumB W e Γ τ Φ) :
    IsDatum Γ.M' W.ψ (fun u => (HMul.hMul (uᵀ.submatrix (e.symm.trans finSumFinEquiv).symm id)
      (incM (G.V (.grid i j)).gram) : Matrix (Fin (_ + _)) (Fin _) (AE D))) Φ (GlobalTheory.SquareDict.datumB W τ) := by
  refine ⟨h.1, fun u => (h.2 u).trans (Eq.symm ((Finset.sum_apply _ _ _).trans (Finset.sum_congr rfl fun d _ => ?_)))⟩
  have e2 : adjM (G.V (.grid i j)) (negSp (G.V (.grid (i + 1) j))) (HMul.hMul (u.submatrix id fun k => e (.inr k))ᵀ
      (incM (G.V (.grid i j)).gram) : Matrix (Fin (G.V (.grid (i + 1) j)).rank) (Fin _) (AE D)) = adjV₁ e u := by
    refine (adjM_coord _ (negSp (G.V (.grid (i + 1) j))) _).trans ?_
    rw [adjV₁, mulG, mulG, ← Matrix.mul_neg]
    congr 1
    ext a b
    exact map_neg (incA D) _
  dsimp only
  rw [Pi.smul_apply, box2, (rows_coord e u _).1, (rows_coord e u _).2, e2]
  rfl

end Read


theorem thetaKO_left_neg {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) {M X : HSp D} (A : Fr M) (B : Fr X)
    {χ χ' : (AE D)ˣ →* Circle} {ω : GlobalTheory.Grid.WRep M X} (hω : GlobalTheory.Grid.IsWeil ψ true M X χ χ' ω) {Φ : WO M X → ℂ}
    (hΦ : Φ ∈ GlobalTheory.SquareComm.algF ψ θ true A B) : ∀ γ ∈ GQ M, ∀ (g : GA D M) (h : GA D X),
    thetaKO ω (γ * g) h Φ = thetaKO ω g h Φ := by
  intro γ hγ g h
  have hω' : IsWeilDatumO ψ (GlobalTheory.Grid.sgn true M) X χ χ' (ω.toSgn true) := hω
  have hth : IsThetaFunO ψ (GlobalTheory.Grid.sgn true M) X Φ := by
    induction hΦ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, P, hf, rfl⟩ := hx
      exact GlobalTheory.GalLift.Vec.theta_pureTensorO hω'.std hθ _ _ _ _ hf.1 P
    | zero => exact GlobalTheory.OrientedHeis.theta_zero
    | add x y _ _ hx hy => exact GlobalTheory.OrientedHeis.theta_add hx hy
    | smul c x _ hx => exact GlobalTheory.OrientedHeis.theta_smul c hx
  unfold thetaKO
  have e : (γ * g, h) = (γ, (1 : GA D X)) * (g, h) := by simp
  rw [e, map_mul, Module.End.mul_apply]
  exact hω'.om_aut ((GlobalTheory.Grid.ofSgn true M).symm γ) ((GlobalTheory.SgnIdent.mem_GQ_sgn true M _).2 hγ) _ (Subgroup.one_mem _) _
    (hω'.om_pres ((GlobalTheory.Grid.ofSgn true M).symm g, h) _ hth)

theorem exists_scalar {P Q : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup Q] [Module ℂ Q] {x : P} (hx : x ≠ 0) (y : P) :
    ∃ c : ℂ, ∀ u u' : Q, x ⊗ₜ[ℂ] u = y ⊗ₜ[ℂ] u' → u = c • u' := by
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one ℂ hx
  refine ⟨l y, fun u u' h => ?_⟩
  have := congrArg (TensorProduct.lid ℂ Q ∘ LinearMap.rTensor Q l) h
  simpa [hl] using this

end GlobalTheory.SquareIdent

end
