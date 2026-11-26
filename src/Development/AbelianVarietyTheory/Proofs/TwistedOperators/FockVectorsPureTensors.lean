module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PureTensorLinearInFactorAndHeisenbergDerivReal
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelThetaSpan
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsAdelicMatrix
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ClassSumEvalComplexPointEqClassical
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompAtOfFin
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ConjScalarAtOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateFreeOfCard

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsPureTensors
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsPureTensors
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockPureTensor

section Generic

variable {ι κ V : Type} [DecidableEq κ] [AddCommGroup V] [Module ℂ V] {Pu : (κ → V) → V → Prop}


omit [DecidableEq κ] in
def IsMultiLin (Pu : (κ → V) → V → Prop) : Prop :=
  ∀ (x y z : κ → V) (f g : V) (q : κ) (c : ℂ), Pu x f → Pu y g → (∀ p, p ≠ q → y p = x p) → (∀ p, p ≠ q → z p = x p) →
    z q = c • x q + y q → Pu z (c • f + g)

theorem IsMultiLin.upd (h : IsMultiLin Pu) {x : κ → V} {q : κ} {a b f g : V} (c : ℂ)
    (h1 : Pu (Function.update x q a) f) (h2 : Pu (Function.update x q b) g) :
    Pu (Function.update x q (c • a + b)) (c • f + g) := by
  refine h _ _ _ f g q c h1 h2 (fun p hp => ?_) (fun p hp => ?_) ?_
  · simp [hp]
  · simp [hp]
  · simp

theorem IsMultiLin.upd_smul (h : IsMultiLin Pu) {x : κ → V} {q : κ} {a f : V} (c : ℂ)
    (h1 : Pu (Function.update x q a) f) : Pu (Function.update x q (c • a)) (c • f) := by
  have h0 : Pu (Function.update x q 0) 0 := by
    simpa using h.upd (-1) h1 h1
  simpa using h.upd c h1 h0

theorem poly_step (h : IsMultiLin Pu) (L L₀ : MvPolynomial ι ℂ →ₗ[ℂ] V) (q : κ) (s : Set ι)
    (hX : ∀ y ∈ s, ∀ x R Q, Pu (Function.update x q (L₀ Q)) (L R) →
      Pu (Function.update x q (L₀ (MvPolynomial.X y * Q))) (L (MvPolynomial.X y * R)))
    {P : MvPolynomial ι ℂ} (hP : P ∈ MvPolynomial.supported ℂ s) :
    ∀ x R Q, Pu (Function.update x q (L₀ Q)) (L R) → Pu (Function.update x q (L₀ (P * Q))) (L (P * R)) := by
  have hP' : P ∈ Algebra.adjoin ℂ (MvPolynomial.X '' s) := by
    rwa [← MvPolynomial.supported_eq_adjoin_X]
  clear hP
  induction hP' using Algebra.adjoin_induction with
  | mem P hPs =>
    obtain ⟨y, hy, rfl⟩ := hPs
    exact hX y hy
  | algebraMap r =>
    intro x R Q hRQ
    rw [← Algebra.smul_def, ← Algebra.smul_def, map_smul, map_smul]
    exact h.upd_smul r hRQ
  | add P₁ P₂ _ _ ih₁ ih₂ =>
    intro x R Q hRQ
    simpa [add_mul] using h.upd 1 (ih₁ x R Q hRQ) (ih₂ x R Q hRQ)
  | mul P₁ P₂ _ _ ih₁ ih₂ =>
    intro x R Q hRQ
    simpa [mul_assoc] using ih₁ x (P₂ * R) (P₂ * Q) (ih₂ x R Q hRQ)

theorem prod_step {α β : Type} [DecidableEq (α ⊕ β)] {Pu : (α ⊕ β → V) → V → Prop} (h : IsMultiLin Pu) (L L₀ : MvPolynomial ι ℂ →ₗ[ℂ] V)
    (s : β → Set ι)
    (hX : ∀ τ, ∀ y ∈ s τ, ∀ x R Q, Pu (Function.update x (.inr τ) (L₀ Q)) (L R) →
      Pu (Function.update x (.inr τ) (L₀ (MvPolynomial.X y * Q))) (L (MvPolynomial.X y * R)))
    {P : β → MvPolynomial ι ℂ} (hP : ∀ τ, P τ ∈ MvPolynomial.supported ℂ (s τ)) {x : α ⊕ β → V}
    (hx : Pu x (L 1)) (hx0 : ∀ τ, x (.inr τ) = L₀ 1) (t : Finset β) :
    Pu (Sum.elim (fun v => x (.inl v)) fun τ => if τ ∈ t then L₀ (P τ) else L₀ 1) (L (∏ τ ∈ t, P τ)) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    have e : (Sum.elim (fun v => x (.inl v)) fun τ => if τ ∈ (∅ : Finset β) then L₀ (P τ) else L₀ 1) = x := by
      funext p
      rcases p with v | τ
      · rfl
      · simp [hx0]
    rw [e, Finset.prod_empty]
    exact hx
  | @insert a t ha ih =>
    rw [Finset.prod_insert ha]
    set G := (Sum.elim (fun v => x (.inl v)) fun τ => if τ ∈ t then L₀ (P τ) else L₀ 1) with hG
    have hGa : G (.inr a) = L₀ 1 := by simp [hG, ha]
    have hfix : Function.update G (.inr a) (L₀ 1) = G := by
      rw [← hGa, Function.update_eq_self]
    have key := poly_step h L L₀ (.inr a) (s a) (hX a) (hP a) G (∏ τ ∈ t, P τ) 1 (by rw [hfix]; exact ih)
    have e : Function.update G (.inr a) (L₀ (P a * 1)) =
        Sum.elim (fun v => x (.inl v)) (fun τ => if τ ∈ insert a t then L₀ (P τ) else L₀ 1) := by
      funext p
      rcases p with v | τ
      · simp [hG]
      · by_cases hτ : τ = a
        · subst hτ
          simp
        · simp [hG, hτ]
    rw [← e]
    exact key

private theorem foldr_mem_of_invariant {X ι : Type} (A : ι → X → X) (Pth : X → Prop)
    (hth : ∀ i x, Pth x → Pth (A i x)) (l : List ι) {x : X} (hx : Pth x) :
    Pth (l.foldr (fun i g => A i g) x) := by
  induction l with
  | nil => exact hx
  | cons a l ih => exact hth a _ ih

private theorem foldr_eq_of_perm_of_commute {X ι : Type} (A : ι → X → X) (Pth : X → Prop)
    (hth : ∀ i x, Pth x → Pth (A i x)) (hc : ∀ i j x, Pth x → A i (A j x) = A j (A i x))
    {l l' : List ι} (hp : l.Perm l') {x : X} (hx : Pth x) :
    l.foldr (fun i g => A i g) x = l'.foldr (fun i g => A i g) x := by
  induction hp with
  | nil => rfl
  | cons a _ ih => simp only [List.foldr_cons, ih]
  | swap a b l => exact hc b a _ (foldr_mem_of_invariant A Pth hth l hx)
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem opPow_single_one_add {X ι : Type} (A : ι → (X → ℂ) → (X → ℂ)) (Pth : (X → ℂ) → Prop)
    (hth : ∀ i x, Pth x → Pth (A i x)) (hc : ∀ i j x, Pth x → A i (A j x) = A j (A i x))
    (y : ι) (u : ι →₀ ℕ) {x : X → ℂ} (hx : Pth x) :
    opPow A (Finsupp.single y 1 + u) x = A y (opPow A u x) := by
  unfold opPow
  have hp : ((Finsupp.toMultiset (Finsupp.single y 1 + u)).toList).Perm (y :: (Finsupp.toMultiset u).toList) := by
    rw [← Multiset.coe_eq_coe, Multiset.coe_toList, ← Multiset.cons_coe, Multiset.coe_toList,
      map_add, Finsupp.toMultiset_single, one_nsmul, Multiset.singleton_add]
  rw [foldr_eq_of_perm_of_commute A Pth hth hc hp hx]
  rfl

private theorem constr_opPow_X_mul {X σ : Type} (A : σ → (X → ℂ) → (X → ℂ)) (Pth : (X → ℂ) → Prop)
    (hadd : ∀ f f', Pth f → Pth f' → Pth (f + f')) (hsm : ∀ (c : ℂ) f, Pth f → Pth (c • f))
    (hth : ∀ i f, Pth f → Pth (A i f)) (hc : ∀ i j f, Pth f → A i (A j f) = A j (A i f))
    (hA : ∀ i f f', Pth f → Pth f' → A i (f + f') = A i f + A i f')
    (hAs : ∀ i (c : ℂ) f, Pth f → A i (c • f) = c • A i f)
    {g : X → ℂ} (hg : Pth g) (y : σ) (Q : MvPolynomial σ ℂ) :
    ((MvPolynomial.basisMonomials σ ℂ).constr ℂ fun k => opPow A k g) (MvPolynomial.X y * Q) =
      A y (((MvPolynomial.basisMonomials σ ℂ).constr ℂ fun k => opPow A k g) Q) := by
  set Φ := (MvPolynomial.basisMonomials σ ℂ).constr ℂ fun k => opPow A k g with hΦ
  have hmono : ∀ m a, Φ (MvPolynomial.monomial m a) = a • opPow A m g := by
    intro m a
    have e : MvPolynomial.monomial m a = a • MvPolynomial.basisMonomials σ ℂ m := by
      simp [MvPolynomial.smul_monomial]
    rw [e, map_smul, hΦ, Module.Basis.constr_basis]
  have hpow : ∀ m, Pth (opPow A m g) := fun m => by
    unfold opPow
    exact foldr_mem_of_invariant A Pth hth _ hg
  have hall : ∀ P, Pth (Φ P) := fun P =>
    MvPolynomial.induction_on' P (fun m a => by rw [hmono]; exact hsm a _ (hpow m))
      (fun p q hp hq => by rw [map_add (f := _)]; exact hadd _ _ hp hq)
  refine MvPolynomial.induction_on' Q (fun u a => ?_) (fun p q hp hq => ?_)
  · rw [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul, hmono, hmono,
      opPow_single_one_add A Pth hth hc y u hg, hAs y a _ (hpow u)]
  · rw [mul_add, map_add (f := _), map_add (f := _), hp, hq, hA y _ _ (hall p) (hall q)]

end Generic

section Theta

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
  {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
  {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
  {f₀ : WO S T → ℂ} {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}

theorem pureTensorO_X_mul (hb : IsBase ψ θ S T sS sT ΛS ΛT f₀) (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) {g : WO S T → ℂ} (hg : IsThetaFunO ψ S T g)
    (Q : MvPolynomial (FVar D T.rank S.rank) ℂ) (y : FVar D T.rank S.rank) :
    pureTensorO ψ θ S T sS sT BS BT g (MvPolynomial.X y * Q) =
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT y (pureTensorO ψ θ S T sS sT BS BT g Q) := by
  have hψ := base_std hb
  have hθ := base_inf hb
  have hS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ) := hb.1
  have hT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ) := hb.2.1
  unfold pureTensorO pureTensorL aPlusAll
  exact constr_opPow_X_mul
    (fun k : FVar D T.rank S.rank => aPlus (heisO ψ S T) θ k.1 (cplxO (sS k.1) (sT k.1)) (unitMap (BS k.1) (BT k.1) k.2.1 k.2.2))
    (IsThetaFunO ψ S T)
    (fun f f' hf hf' => GlobalTheory.OrientedHeis.theta_add hf hf')
    (fun c f hf => GlobalTheory.OrientedHeis.theta_smul c hf)
    (fun k f hf => GlobalTheory.FockSubst.aPlus_th (hψ := hψ) (hθ := hθ) (τ := k.1) (J := _) (z := _) hf)
    (fun i j f hf => GlobalTheory.FockSubst.aPlus_comm (hψ := hψ) (hθ := hθ) (τ := i.1) (z := _) (hS := hS) (hT := hT)
      (τ' := j.1) (z' := _) hf)
    (fun k f f' hf hf' => GlobalTheory.FockSubst.aPlus_add (hψ := hψ) (hθ := hθ) (τ := k.1) (J := _) (z := _) hf hf')
    (fun k c f hf => GlobalTheory.FockSubst.aPlus_smul (hψ := hψ) (hθ := hθ) (τ := k.1) (J := _) (z := _) c hf)
    hg y Q

theorem isPure_aPlus (hb : IsBase ψ θ S T sS sT ΛS ΛT f₀) (hμ : IsCovolOne (ratL T S) μ 𝓕)
    (y : Place D → WO S T → ℂ) (τ : D.what₂.Tau) (a g : WO S T → ℂ)
    (J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ)
    (h : IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ (Function.update y (.inr τ) a) g) :
    IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀
      (Function.update y (.inr τ) (Formalism.IndefR.Datum.aPlus (heisO ψ S T) θ τ J z a))
      (Formalism.IndefR.Datum.aPlus (heisO ψ S T) θ τ J z g) := by
  have hlin := GlobalTheory.T.pureTensor_linear_in_factor_and_heisenbergDeriv_real D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hb hμ
  have hML : IsMultiLin (IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀) := hlin.1
  have hd : ∀ w : Matrix (Fin T.rank) (Fin S.rank) ℂ,
      IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀
        (Function.update y (.inr τ) (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ w a))
        (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ w g) := by
    intro w
    refine hlin.2 _ _ g τ w h (fun p hp => ?_) ?_
    · simp [hp]
    · simp
  have h4 := hML.upd_smul ((fockScale D τ : ℂ)⁻¹) (hML.upd (-Complex.I) (hd (J z)) (hd z))
  rw [GlobalTheory.FockSubst.aPlus_eq, GlobalTheory.FockSubst.aPlus_eq,
    add_comm (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z a), add_comm (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z g)]
  exact h4

end Theta

theorem fockPure : ∀ D : D7, FockPure D := by
  intro D
  unfold FockPure
  intro ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 BS BT pS pT hb hμ _ _ x f hx hx0 P hP
  have hth0 : IsThetaFunO ψ S T f₀ := base_theta hb
  have hthf : IsThetaFunO ψ S T f := hx.2.1
  have hlin := GlobalTheory.T.pureTensor_linear_in_factor_and_heisenbergDeriv_real D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hb hμ
  have hone : ∀ g : WO S T → ℂ, pureTensorO ψ θ S T sS sT BS BT g 1 = g := by
    intro g
    have e1 : (1 : MvPolynomial (FVar D T.rank S.rank) ℂ) = MvPolynomial.basisMonomials (FVar D T.rank S.rank) ℂ 0 := by
      rw [MvPolynomial.coe_basisMonomials]
      rfl
    unfold pureTensorO pureTensorL
    rw [e1, Module.Basis.constr_basis]
    unfold opPow
    simp
  have hX : ∀ τ, ∀ y ∈ (fun τ : D.what₂.Tau => {y : FVar D T.rank S.rank | y.1 = τ}) τ,
      ∀ x' R Q, IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀
          (Function.update x' (.inr τ) (pureTensorO ψ θ S T sS sT BS BT f₀ Q)) (pureTensorO ψ θ S T sS sT BS BT f R) →
        IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀
          (Function.update x' (.inr τ) (pureTensorO ψ θ S T sS sT BS BT f₀ (MvPolynomial.X y * Q)))
          (pureTensorO ψ θ S T sS sT BS BT f (MvPolynomial.X y * R)) := by
    intro τ y hy x' R Q h
    have hy' : y.1 = τ := hy
    subst hy'
    rw [pureTensorO_X_mul hb BS BT hth0 Q y, pureTensorO_X_mul hb BS BT hthf R y]
    exact isPure_aPlus hb hμ x' y.1 _ _ (cplxO (sS y.1) (sT y.1)) (unitMap (BS y.1) (BT y.1) y.2.1 y.2.2) h
  have key := prod_step hlin.1 (pureTensorO ψ θ S T sS sT BS BT f) (pureTensorO ψ θ S T sS sT BS BT f₀)
    (fun τ : D.what₂.Tau => {y : FVar D T.rank S.rank | y.1 = τ}) hX hP (x := x)
    (by rw [hone]; exact hx) (fun τ => by rw [hone]; exact hx0 τ) Finset.univ
  simpa using key

end GlobalTheory.FockPureTensor
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsPureTensorsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVectors_pureTensors : ∀ D : D7, FockPure D := by
  first | exact @GlobalTheory.FockPureTensor.fockPure | exact GlobalTheory.FockPureTensor.fockPure | (intros; apply GlobalTheory.FockPureTensor.fockPure <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelGroupCongruentOfTwoLatticeMoves
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelGroupCongruentOfTwoLatticeMoves
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Ker.LevMove

section General

open Formalism.MainNotions.StandardLattice (latHat intAf)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}


omit [NumberField E] in
theorem int_smul_mem (L : Submodule (𝓞 E) (Fin n → E)) {f : FiniteAdeleRing (𝓞 F) F} (hf : f ∈ intAf F)
    {z : Fin n → FiniteAdeleRing (𝓞 F) F ⊗[F] E} (hz : z ∈ latHat F E (L : Set (Fin n → E))) :
    (f ⊗ₜ[F] (1 : E)) • z ∈ latHat F E (L : Set (Fin n → E)) := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨f * a, fun v => ?_, x, hx, ?_⟩
    · rw [map_mul]; exact mul_mem (hf v) (ha v)
    · funext i
      change (f ⊗ₜ[F] (1 : E)) * a ⊗ₜ x i = (f * a) ⊗ₜ x i
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx


omit [NumberField E] in
theorem ideal_smul_mem (L : Submodule (𝓞 E) (Fin n → E)) (𝔪 : Ideal (𝓞 E)) {c : 𝓞 E} (hc : c ∈ 𝔪)
    {z : Fin n → FiniteAdeleRing (𝓞 F) F ⊗[F] E} (hz : z ∈ latHat F E (L : Set (Fin n → E))) :
    ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (c : E)) • z ∈ latHat F E ((𝔪 • L : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a, ha, c • x, Submodule.smul_mem_smul hc hx, ?_⟩
    funext i
    change ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (c : E)) * a ⊗ₜ x i = a ⊗ₜ ((c : E) * x i)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem inv_int_at {c : 𝓞 F} (v : HeightOneSpectrum (𝓞 F)) (hv : c ∉ v.asIdeal) :
    evalV F v (algebraMap F (FiniteAdeleRing (𝓞 F) F) ((c : F)⁻¹)) ∈ v.adicCompletionIntegers F := by
  rw [AlgHom.commutes, HeightOneSpectrum.mem_adicCompletionIntegers]
  have h1 : v.valuation F (algebraMap (𝓞 F) F c) = 1 := (v.valuation_eq_one_iff_notMem (K := F)).2 hv
  have h2 : Valued.v (algebraMap F (v.adicCompletion F) (c : F)) = v.valuation F (c : F) :=
    v.valuedAdicCompletion_eq_valuation' (K := F) (c : F)
  have h3 : algebraMap F (Fv F v) ((c : F)⁻¹) = (algebraMap F (v.adicCompletion F) (c : F))⁻¹ := map_inv₀ _ _
  rw [h3, map_inv₀, h2]
  change (v.valuation F (algebraMap (𝓞 F) F c))⁻¹ ≤ 1
  rw [h1, inv_one]

theorem vanish_smul_mem (L : Submodule (𝓞 E) (Fin n → E)) (𝔪 : Ideal (𝓞 E)) {c : 𝓞 F} (hc0 : c ≠ 0)
    (hc : algebraMap (𝓞 F) (𝓞 E) c ∈ 𝔪) {f : FiniteAdeleRing (𝓞 F) F} (hf : f ∈ intAf F)
    (hfc : ∀ v : HeightOneSpectrum (𝓞 F), c ∈ v.asIdeal → evalV F v f = 0)
    {z : Fin n → FiniteAdeleRing (𝓞 F) F ⊗[F] E} (hz : z ∈ latHat F E (L : Set (Fin n → E))) :
    (f ⊗ₜ[F] (1 : E)) • z ∈ latHat F E ((𝔪 • L : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) := by
  set b : FiniteAdeleRing (𝓞 F) F := algebraMap F (FiniteAdeleRing (𝓞 F) F) ((c : F)⁻¹) * f with hbdef
  have hb : b ∈ intAf F := fun v => by
    by_cases hv : c ∈ v.asIdeal
    · rw [hbdef, map_mul, hfc v hv, mul_zero]; exact zero_mem _
    · rw [hbdef, map_mul]; exact mul_mem (inv_int_at v hv) (hf v)
  have hcF : (c : F) ≠ 0 := fun h => hc0 (RingOfIntegers.coe_injective (by simpa using h))
  have hfb : (f ⊗ₜ[F] (1 : E) : FiniteAdeleRing (𝓞 F) F ⊗[F] E) =
      ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] ((algebraMap (𝓞 F) (𝓞 E) c : 𝓞 E) : E)) * (b ⊗ₜ[F] (1 : E)) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    change f ⊗ₜ[F] (1 : E) = b ⊗ₜ[F] (algebraMap F E (c : F))
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul', hbdef,
      Algebra.smul_def, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hcF, map_one, one_mul]
  rw [hfb, mul_smul]
  exact ideal_smul_mem L 𝔪 hc (int_smul_mem L hb hz)

end General

end GlobalTheory.Ker.LevMove

namespace GlobalTheory.Ker.LevMove

section Core

open Formalism.MainNotions.StandardLattice (latHat intAf)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem exists_ind (v : HeightOneSpectrum (𝓞 F)) : ∃ α : FiniteAdeleRing (𝓞 F) F,
    evalV F v α = 1 ∧ ∀ w, w ≠ v → evalV F w α = 0 := by
  obtain ⟨e, h1, h0⟩ := GlobalTheory.UnRep.SmallMat.exists_indicator ({v} : Finset (HeightOneSpectrum (𝓞 F)))
  exact ⟨e, h1 v (Finset.mem_singleton_self v), fun w hw => h0 w (by simpa using hw)⟩

theorem ind_int {v : HeightOneSpectrum (𝓞 F)} {α : FiniteAdeleRing (𝓞 F) F} (h1 : evalV F v α = 1)
    (h0 : ∀ w, w ≠ v → evalV F w α = 0) : α ∈ intAf F := fun w => by
  by_cases hw : w = v
  · subst hw; rw [h1]; exact one_mem _
  · rw [h0 w hw]; exact zero_mem _

theorem mem_of_vanish (L : Submodule (𝓞 E) (Fin n → E)) (𝔪 : Ideal (𝓞 E)) (h𝔪 : 𝔪 ≠ ⊥)
    {x : Fin n → FiniteAdeleRing (𝓞 F) F ⊗[F] E} (hx : x ∈ latHat F E (L : Set (Fin n → E)))
    (hloc : ∀ v : HeightOneSpectrum (𝓞 F), 𝔪.comap (algebraMap (𝓞 F) (𝓞 E)) ≤ v.asIdeal →
      ∀ α : FiniteAdeleRing (𝓞 F) F, evalV F v α = 1 → (∀ w, w ≠ v → evalV F w α = 0) →
        (α ⊗ₜ[F] (1 : E)) • x = 0) :
    x ∈ latHat F E ((𝔪 • L : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) := by
  classical
  set N := Ideal.absNorm 𝔪 with hNdef
  have hN0 : N ≠ 0 := fun h => h𝔪 (Ideal.absNorm_eq_zero_iff.1 h)
  have hNE : ((N : 𝓞 E)) ∈ 𝔪 := Ideal.absNorm_mem 𝔪
  set c₁ : 𝓞 F := (N : 𝓞 F) with hc₁
  have hc₁0 : c₁ ≠ 0 := Nat.cast_ne_zero.2 hN0
  have hc₁m : algebraMap (𝓞 F) (𝓞 E) c₁ ∈ 𝔪 := by rw [hc₁, map_natCast]; exact hNE
  have hfin : {v : HeightOneSpectrum (𝓞 F) | v.asIdeal ∣ Ideal.span {c₁}}.Finite :=
    Ideal.finite_factors (by rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot])
  set P := hfin.toFinset with hP
  have hmemP : ∀ v, v ∈ P ↔ c₁ ∈ v.asIdeal := fun v => by
    rw [hP, Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  choose ind hind1 hind0 using (exists_ind (F := F))
  set e₁ : FiniteAdeleRing (𝓞 F) F := ∑ v ∈ P, ind v with he₁
  have hev : ∀ w, evalV F w e₁ = if w ∈ P then 1 else 0 := fun w => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [he₁, map_sum]
    split_ifs with hw
    · rw [Finset.sum_eq_single w (fun b _ hb => hind0 b w (Ne.symm hb)) (fun h => absurd hw h), hind1]
    · exact Finset.sum_eq_zero fun b hb => hind0 b w (fun h => hw (h ▸ hb))
  have hsplit : x = ((1 - e₁) ⊗ₜ[F] (1 : E)) • x + ∑ v ∈ P, (ind v ⊗ₜ[F] (1 : E)) • x := by
    rw [← Finset.sum_smul, ← TensorProduct.sum_tmul, ← he₁, ← add_smul, ← TensorProduct.add_tmul, sub_add_cancel,
      Algebra.TensorProduct.one_def.symm, one_smul]
  rw [hsplit]
  refine add_mem ?_ (sum_mem fun v hv => ?_)
  · refine vanish_smul_mem L 𝔪 hc₁0 hc₁m (fun w => ?_) (fun w hw => ?_) hx
    · rw [map_sub, map_one, hev]; split_ifs
      · rw [sub_self]; exact zero_mem _
      · rw [sub_zero]; exact one_mem _
    · rw [map_sub, map_one, hev, if_pos ((hmemP w).2 hw), sub_self]
  · by_cases hI : 𝔪.comap (algebraMap (𝓞 F) (𝓞 E)) ≤ v.asIdeal
    · rw [hloc v hI (ind v) (hind1 v) (hind0 v)]; exact zero_mem _
    · obtain ⟨c, hc, hcv⟩ := SetLike.not_le_iff_exists.1 hI
      have hc0 : c ≠ 0 := fun h => hcv (h ▸ zero_mem _)
      refine vanish_smul_mem L 𝔪 hc0 hc (ind_int (hind1 v) (hind0 v)) (fun w hw => hind0 v w ?_) hx
      rintro rfl; exact hcv hw

end Core

end GlobalTheory.Ker.LevMove

namespace GlobalTheory.Ker.LevMove

variable {D : D7}

theorem fmt_mul' (V : HSp D) (g g' : GA D V) : fmt V (g * g') = fmt V g * fmt V g' := by
  simp only [fmt, Formalism.L2.Theta.mt, map_mul, Units.val_mul, Matrix.map_mul]

theorem fmt_one' (V : HSp D) : fmt V 1 = 1 := by
  simp only [fmt, Formalism.L2.Theta.mt, map_one, Units.val_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem smul_fmt_sub_one {T : HSp D} {I : Ideal (𝓞 D.host.F)} {g : GA D T} (h : TrivAt T I g)
    {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : I ≤ v.asIdeal) {α : Af D.host.F} (h1 : evalV D.host.F v α = 1)
    (h0 : ∀ w, w ≠ v → evalV D.host.F w α = 0) :
    ((α ⊗ₜ[D.host.F] (1 : D.host.E) : AfE D)) • (fmt T g - 1) = 0 := by
  ext i j
  have := congrArg (finPart D) (h v hv (pairA D.host.F 0 α) ⟨α, rfl, h1, h0⟩ i j)
  rw [map_mul, map_zero] at this
  have e1 : finPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) =
    α ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
  have e2 : finPart D ((mt T g - 1) i j) = (fmt T g - 1) i j := by
    rw [Matrix.sub_apply, Matrix.sub_apply, map_sub]
    congr 1
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij]
  rw [e1, e2] at this
  rw [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
  exact this

theorem smul_algebra {R : Type} [CommRing R] {k : ℕ} (P : R) (A A' B : Matrix (Fin k) (Fin k) R)
    (hA : P • A = P • 1) (hB : P • B = P • 1) (e : A * A' = 1) : P • (A' * B - 1) = 0 := by
  have h' : P • A' = P • 1 := by
    calc P • A' = (P • 1) * A' := by rw [Matrix.smul_mul, one_mul]
      _ = (P • A) * A' := by rw [hA]
      _ = P • 1 := by rw [Matrix.smul_mul, e]
  rw [smul_sub, ← Matrix.smul_mul, h', Matrix.smul_mul, one_mul, hB, sub_self]

theorem smul_vec {R : Type} [CommRing R] {k : ℕ} (P : R) (M : Matrix (Fin k) (Fin k) R) (u : Fin k → R)
    (h : P • (M - 1) = 0) : P • (M *ᵥ u - u) = 0 := by
  have : M *ᵥ u - u = (M - 1) *ᵥ u := by rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  rw [this, ← Matrix.smul_mulVec, h, Matrix.zero_mulVec]

end GlobalTheory.Ker.LevMove

theorem GlobalTheory.Ker.LevMove.levK_of_two_moves : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (Lv : SW.Level C.X) (g₁ g₂ : GA D T) (L : Lt D.host.E T.rank), g₁ ∈ GfC T → g₂ ∈ GfC T → TrivAt T (C.under Lv) g₁ → TrivAt T (C.under Lv) g₂ → L.FG → IsMov (fmt T g₁) C.X.Λ L → IsMov (fmt T g₂) C.X.Λ L → C.LevK Lv (g₁⁻¹ * g₂) 1 := by
  intro D S T C Lv g₁ g₂ L h1 h2 t1 t2 hL m1 m2
  have hfull : C.X.Λ.FG ∧ Submodule.span D.host.E (C.X.Λ : Set (Fin T.rank → D.host.E)) = ⊤ :=
    ⟨C.X.Λ_fg, C.X.Λ_span⟩
  have e1 : fmt T g₁ * fmt T g₁⁻¹ = 1 := by
    rw [← GlobalTheory.Ker.LevMove.fmt_mul', mul_inv_cancel, GlobalTheory.Ker.LevMove.fmt_one']
  have e2 : fmt T g₂ * fmt T g₂⁻¹ = 1 := by
    rw [← GlobalTheory.Ker.LevMove.fmt_mul', mul_inv_cancel, GlobalTheory.Ker.LevMove.fmt_one']
  obtain ⟨-, -, -, laws⟩ := GlobalTheory.Ker.isMov_laws D T.rank C.X.Λ hfull
  obtain ⟨-, hb1, -, -, -⟩ := (laws _ _ e1).2 L hL m1
  obtain ⟨-, -, -, hcomp, -⟩ := (laws _ _ e2).2 L hL m2
  have hk : IsMov (fmt T (g₁⁻¹ * g₂)) C.X.Λ C.X.Λ := by
    rw [GlobalTheory.Ker.LevMove.fmt_mul']; exact hcomp _ _ hb1
  refine ⟨mul_mem (inv_mem h1) h2, hk, 1, ?_, fun i => ?_⟩
  · rw [OneMemClass.coe_one, Units.val_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  · have hs : ∑ j, (1 : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E)) j i • Lv.β j = Lv.β i := by
      simp [Matrix.one_apply]
    rw [hs]
    have hb : toAf (Lv.β i) ∈ hatV C.X.Λ :=
      AddSubgroup.subset_closure ⟨1, fun v => by rw [map_one]; exact one_mem _, Lv.β i, Lv.β_mem i, rfl⟩
    refine GlobalTheory.Ker.LevMove.mem_of_vanish (F := D.host.F) C.X.Λ Lv.𝔪 Lv.ne_bot
      (sub_mem ((hk _).2 ⟨_, hb, rfl⟩) hb) ?_
    intro v hv α a1 a0
    have P1 := GlobalTheory.Ker.LevMove.smul_fmt_sub_one t1 hv a1 a0
    have P2 := GlobalTheory.Ker.LevMove.smul_fmt_sub_one t2 hv a1 a0
    set P : AfE D := α ⊗ₜ[D.host.F] (1 : D.host.E) with hPdef
    have q1 : P • fmt T g₁ = P • 1 := by rw [smul_sub] at P1; exact sub_eq_zero.1 P1
    have q2 : P • fmt T g₂ = P • 1 := by rw [smul_sub] at P2; exact sub_eq_zero.1 P2
    have q : P • (fmt T (g₁⁻¹ * g₂) - 1) = 0 := by
      rw [GlobalTheory.Ker.LevMove.fmt_mul']
      exact GlobalTheory.Ker.LevMove.smul_algebra P _ _ _ q1 q2 e1
    exact GlobalTheory.Ker.LevMove.smul_vec P _ _ q
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelGroupCongruentOfTwoLatticeMovesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_group_congruent_of_two_lattice_moves : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (Lv : SW.Level C.X) (g₁ g₂ : GA D T) (L : Lt D.host.E T.rank), g₁ ∈ GfC T → g₂ ∈ GfC T → TrivAt T (C.under Lv) g₁ → TrivAt T (C.under Lv) g₂ → L.FG → IsMov (fmt T g₁) C.X.Λ L → IsMov (fmt T g₂) C.X.Λ L → C.LevK Lv (g₁⁻¹ * g₂) 1 := by
  first | exact @GlobalTheory.Ker.LevMove.levK_of_two_moves | exact GlobalTheory.Ker.LevMove.levK_of_two_moves | (intros; apply GlobalTheory.Ker.LevMove.levK_of_two_moves <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FramedPointDescendsFiniteSubextension
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FramedPointDescendsFiniteSubextension
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

namespace GlobalTheory.HkIntegral

theorem exists_finite_factor {F R K L : Type} [Field F] [CommRing R] [Field K] [Field L] [Algebra F R]
    [Algebra F K] [Algebra F L] [Algebra.FiniteType F R] (φ : K →ₐ[F] L) (hφ : φ.toRingHom.IsIntegral)
    (ψ : R →ₐ[F] L) :
    ∃ (M : Type) (_ : Field M) (_ : Algebra F M) (i : K →ₐ[F] M) (j : M →ₐ[F] L) (χ : R →ₐ[F] M),
      j.comp i = φ ∧ i.toRingHom.Finite ∧ j.comp χ = ψ := by
  classical
  letI : Algebra K L := φ.toRingHom.toAlgebra
  haveI : IsScalarTower F K L := IsScalarTower.of_algebraMap_eq fun a => (φ.commutes a).symm
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType F R).out
  let M : IntermediateField K L := IntermediateField.adjoin K ((s.image ψ : Finset L) : Set L)
  haveI hM : FiniteDimensional K M :=
    IntermediateField.finiteDimensional_adjoin fun x _ => hφ x
  have hmem : ∀ r : R, ψ r ∈ M.toSubalgebra.restrictScalars F := by
    intro r
    have hr : r ∈ Algebra.adjoin F (s : Set R) := hs ▸ Algebra.mem_top
    have : Algebra.adjoin F (s : Set R) ≤ (M.toSubalgebra.restrictScalars F).comap ψ := by
      refine Algebra.adjoin_le fun x hx => ?_
      exact IntermediateField.subset_adjoin K _ (by simpa using ⟨x, hx, rfl⟩)
    exact this hr
  refine ⟨M, inferInstance, inferInstance, IsScalarTower.toAlgHom F K M, M.val.restrictScalars F,
    ψ.codRestrict (M.toSubalgebra.restrictScalars F) hmem, ?_, ?_, ?_⟩
  · ext a; rfl
  · exact RingHom.finite_algebraMap.2 hM
  · ext a; rfl

theorem frPt_descends_finite :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K L : Type) [Field K] [Field L] [Algebra c.F K] [Algebra c.F L] (φ : K →ₐ[c.F] L) (z : FrPt Xo c L), φ.toRingHom.IsIntegral → ∃ (M : Type) (_ : Field M) (_ : Algebra c.F M) (i : K →ₐ[c.F] M) (j : M →ₐ[c.F] L) (z₁ : FrPt Xo c M), j.comp i = φ ∧ i.toRingHom.Finite ∧ FrMap j z₁ z := by
  intro E _ _ _ H Dw l Xo c K L _ _ _ _ φ z hφ
  obtain ⟨p, ψ, u, hu⟩ := GlobalTheory.FlagTan.fromTest_of_isLocalRing z
  haveI : Algebra.FiniteType c.F p.R := inferInstance
  obtain ⟨M, _, _, i, j, χ, h1, h2, h3⟩ := exists_finite_factor φ hφ ψ
  obtain ⟨z₁, hz⟩ := GlobalTheory.FlagTan.exists_frMap χ u
  exact ⟨M, inferInstance, inferInstance, i, j, z₁, h1, h2,
    GlobalTheory.FlagTan.frMap_of_comp hz hu fun a => DFunLike.congr_fun h3 a⟩

end GlobalTheory.HkIntegral
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FramedPointDescendsFiniteSubextensionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.framedPoint_descends_finite_subextension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K L : Type) [Field K] [Field L] [Algebra c.F K] [Algebra c.F L] (φ : K →ₐ[c.F] L) (z : FrPt Xo c L), φ.toRingHom.IsIntegral → ∃ (M : Type) (_ : Field M) (_ : Algebra c.F M) (i : K →ₐ[c.F] M) (j : M →ₐ[c.F] L) (z₁ : FrPt Xo c M), j.comp i = φ ∧ i.toRingHom.Finite ∧ FrMap j z₁ z := by
  first | exact @GlobalTheory.HkIntegral.frPt_descends_finite | exact GlobalTheory.HkIntegral.frPt_descends_finite | (intros; apply GlobalTheory.HkIntegral.frPt_descends_finite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicLiftDatumOfConjugateLiftDatum
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicLiftDatumOfConjugateLiftDatum
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ConjLiftData

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem exists_galConj_mu (R : RealDat D A Ks) (hL : R.Is A.μ0) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ)
    (hσ : GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsEmbOverK D σ s) (μ' : (AE D)ˣ →* Circle) (hμ : ChiAt R i σ μ') :
    ∃ μH : Formalism.L2.Host.HChar D.host.E, GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsGalConj s 0 (R.C.mu0 i * R.xiH A.μ0) μH ∧ ChrEq μ' μH := by
  obtain ⟨μH, hH⟩ := GlobalTheory.HeckeTensorRead.exists_hchar_chrEq D μ' hμ.1
  refine ⟨μH, fun P k => ?_, hH⟩
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨e, he, hinf, -⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3 P
  have hx : infPart D ((Formalism.L2.JoinChr.locU he.1 k : (AE D)ˣ) : AE D) = 1 := by
    rw [Formalism.L2.JoinChr.locU_val, Formalism.L2.JoinChr.locE, RingHom.map_add (f := _), RingHom.map_mul, hinf, zero_mul, add_zero,
      RingHom.map_one]
  obtain ⟨y, hy0, hy⟩ := hμ.2.2.2.1 _ hx
  have a1 := hH.2 P e he k _ (Formalism.L2.JoinChr.locU_val he.1 k)
  have a2 := (hL.mu0 i).2 P e he k _ (Formalism.L2.JoinChr.locU_val he.1 k)
  rw [hL.xi_base, mul_one]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.twVal
  simp only [Complex.ofReal_zero, zero_mul, neg_zero, Complex.cpow_zero, mul_one]
  rw [← a1, ← a2, hy, hy0, hσ.1]

theorem exists_galConj_eta (R : RealDat D A Ks) (hL : R.Is A.μ0) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ)
    (hσ : GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsEmbOverK D σ s) (η' : (AE D)ˣ →* Circle) (hη : GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsEtaConj σ R.eta η') :
    ∃ ηH : Formalism.L2.Host.HChar D.host.E, GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsGalConj s (1 / 2) R.C.eta ηH ∧ ChrEq η' ηH := by
  obtain ⟨ηH, hH⟩ := GlobalTheory.HeckeTensorRead.exists_hchar_chrEq D η' hη.1
  refine ⟨ηH, fun P k => ?_, hH⟩
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨e, he, -⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3 P
  obtain ⟨y, hy1, hy2⟩ := hη.2.2 P e he (Formalism.L2.JoinChr.locU he.1 (Formalism.L2.Host.unif P)) rfl
  have h0 : ∀ u : D.host.Eˣ, P.valuation D.host.E (u : D.host.E) = 1 → R.C.eta.locK P u = 1 := fun u hu =>
    R.C.isEta.unr P _ ((P.valuedAdicCompletion_eq_valuation' (u : D.host.E)).trans hu)
  rw [GlobalTheory.EtaConjChar.twVal_half _ P (GlobalTheory.EtaConjChar.locK_eq_one hH hη.2.1 P), GlobalTheory.EtaConjChar.twVal_half _ P h0, map_zpow₀,
    ← hH.2 P e he _ (Formalism.L2.JoinChr.locU he.1 (Formalism.L2.Host.unif P)) rfl,
    ← hL.eta.2 P e he _ (Formalism.L2.JoinChr.locU he.1 (Formalism.L2.Host.unif P)) rfl, ← hy1, ← hy2, hσ.1]

theorem levFn_conj {n : ℕ} (β : GL (Fin n) (Lev.EAf D)) {r : ℕ} (hr : r ≤ n) (t : ℕ) (Pg : Finset (Pl D.host.E))
    {Q : Finset (Pl D.host.E)} (hQ : Q = ∅) (s : ℂ →+* ℂ) (χ ξ ξ' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (x) :
    s ((levFn β ⟨r, hr, t, 1, Pg, Q, LevelP.triv Pg r ℂ, fun _ => χ, ξ⟩ x : ℂˣ) : ℂ) =
      ((levFn β ⟨r, hr, t, 1, Pg, Q, LevelP.triv Pg r ℂ, fun _ PP => (Units.map s.toMonoidHom).comp (χ PP), ξ'⟩ x : ℂˣ) : ℂ) := by
  subst hQ
  have h1 : ∀ y, ext1 (LevelP.triv Pg r ℂ).H (LevelP.triv Pg r ℂ).chi y = 1 := fun y => Lev.subgroupCharExtension_one_apply _ _
  unfold levFn
  simp [h1]

theorem is_congr {Γ Gr W : Type} [Group Γ] [Group Gr] [NormedAddCommGroup W] [InnerProductSpace ℂ W] {ι : Γ →* Gr}
    {ρ : Γ →* Module.End ℂ W} {J J' : Subgroup Gr} (hJ : J = J') {χ : J →* ℂˣ} {χ' : J' →* ℂˣ}
    (h : ∀ x hx hx', χ ⟨x, hx⟩ = χ' ⟨x, hx'⟩) {I : Type} [Fintype I] {y : I → Gr} {H : HMod (Gr → W)}
    (hH : H.Is (Bridge.AdForms ι ρ J χ) (Bridge.adInner ι J y)) : H.Is (Bridge.AdForms ι ρ J' χ') (Bridge.adInner ι J' y) := by
  subst hJ
  obtain rfl : χ = χ' := MonoidHom.ext fun x => h x.1 x.2 x.2
  exact hH


set_option maxHeartbeats 1000000 in
theorem isLiftDataC_of_liftData : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ gramR c0R c0L, GlobalTheory.GalLift.Comparison₂ R gramR c0R c0L → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsConjForms R i σ (c0L i) c c₁ H j → ∀ μ' η', ChiAt R i σ μ' → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsEtaConj σ R.eta η' → ∀ ω f₀ f B io thP, GlobalTheory.GalLift.LiftData R i σ μ' η' c H ω f₀ f B io thP → ∃ s m, GlobalTheory.LiftRows.IsLiftDataC R F i A.μ0 σ s R.triv μ' η' m ω B f₀ f c io ∧ IsMeasDef (Vc D i) (GlobalTheory.AdelicScalar.levV R i A.μ0 R.triv m) (R.νV i A.μ0) (R.fdV i A.μ0) ∧ Bridge.IsReps (Bridge.ratF (Vc D i)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (R.B.L i A.μ0).pres.y ∧ H.Is (Bridge.AdForms (Bridge.ratF (Vc D i)) c.coef.ρ (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.chrOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m))) (Bridge.adInner (Bridge.ratF (Vc D i)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (R.B.L i A.μ0).pres.y) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC gramR c0R c0L _ i σ c c₁ H j hσ hf μ' η' hμ hη ω f₀ f B io thP hL
  classical
  have : Countable D.what₂.LL := Countable.of_equiv _ (Module.finBasis ℚ D.what₂.LL).equivFun.toEquiv.symm
  obtain ⟨s, hs⟩ := GlobalTheory.CompRat.exists_ringEquiv_complex_comp_eq D.what₂.LL D.what₂.embLL σ
  have hE : GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsEmbOverK D σ s := ⟨fun a => (hs a).symm, hσ⟩
  obtain ⟨hω, hvec, hio, -⟩ := hL
  obtain ⟨μH, hμ1, hμ2⟩ := exists_galConj_mu R hC.lev i σ s hE μ' hμ
  obtain ⟨ηH, hη1, hη2⟩ := exists_galConj_eta R hC.lev σ s hE η' hη
  have hQ := GlobalTheory.LiftLower.Q_base hC.lev
  let m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ := fun PP =>
    (Units.map (s : ℂ →+* ℂ).toMonoidHom).comp (R.chi ((i : ℕ) + 1) PP)⁻¹
  have hp : GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.PrimeToHost R A.μ0 := by
    intro PP hPP
    rcases hPP with hPP | hPP
    · exact GlobalTheory.LiftScalarCompare.primeToHost hC.lev PP hPP
    · rw [hQ] at hPP
      exact absurd hPP (Finset.notMem_empty _)
  have hm : GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsConjChars R i A.μ0 s μ' η' m := by
    refine ⟨μH, ηH, hμ1, hη1, hμ2, hη2, fun PP hPP a k u hk hu => ?_⟩
    have hg : PP ∈ R.Pg := hPP.resolve_right (by simp [hQ])
    have h1 := hμ1 PP k
    have h2 := hC.lev.chi i PP hg a k u hk hu
    rw [hC.lev.xi_base, mul_one] at h1
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.twVal, Complex.ofReal_zero, zero_mul, neg_zero, Complex.cpow_zero, mul_one] at h1
    apply Units.ext
    rw [h1, ← h2]
    rfl
  have hlv : GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsLevelVec R.ψ R.θ (Vc D i) (Wc D i) (cart (R.MW i σ)) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i)
      (R.datWp i R.triv) (R.Q A.μ0) m f₀ f := by
    have hv := hvec.vec
    rw [hQ]
    unfold Datum.IsThPVecOf at hv
    unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsLevelVec
    have hq : ∀ y : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP),
        Datum.omegaQ ∅ (Wc D i).rank m (-1) y = Datum.omegaQ ∅ (Wc D i).rank (fun _ => 1) (-1) y := by
      intro y
      simp [Datum.omegaQ]
    simp only [GlobalTheory.Survey.LevelVectorSizeBounds.omegaG_triv, hq]
    exact hv
  obtain ⟨χ', hχ, hH⟩ := hf.model
  have key : ∀ k : levJ R i A.μ0, χ' k = levFn (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)
      (Formalism.UG.bc (Lev.swapAE D) k.1.1) := fun k => Units.ext <| (hχ k).elim fun y hy =>
    hy.2.symm.trans ((hs y).symm.trans ((congrArg s hy.1).trans
      (levFn_conj (R.βV i) (r_le_V i) D.R.t R.Pg hQ (s : ℂ →+* ℂ) (fun PP => (R.chi ((i : ℕ) + 1) PP)⁻¹) (R.xiR A.μ0) m _)))
  have hH' := is_congr (GlobalTheory.Survey.LevelVectorSizeBounds.grp_triv R i A.μ0 m).symm
    (χ' := GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.chrOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (fun x hx _ => key ⟨x, hx⟩) hH
  refine ⟨s, m, ⟨hC, hp, hE, GlobalTheory.Survey.LevelVectorSizeBounds.isLocal_triv R, hm, hω, hvec.onb, hlv, fun P => hvec.theta P, hf.coef, hio⟩,
    hC.models.νV i A.μ0, (R.B.L i A.μ0).pres.reps, hH'⟩

end GlobalTheory.ConjLiftData

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicLiftDatumOfConjugateLiftDatumStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicLiftDatum_of_conjugate_liftDatum : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ gramR c0R c0L, GlobalTheory.GalLift.Comparison₂ R gramR c0R c0L → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsConjForms R i σ (c0L i) c c₁ H j → ∀ μ' η', ChiAt R i σ μ' → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsEtaConj σ R.eta η' → ∀ ω f₀ f B io thP, GlobalTheory.GalLift.LiftData R i σ μ' η' c H ω f₀ f B io thP → ∃ s m, GlobalTheory.LiftRows.IsLiftDataC R F i A.μ0 σ s R.triv μ' η' m ω B f₀ f c io ∧ IsMeasDef (Vc D i) (GlobalTheory.AdelicScalar.levV R i A.μ0 R.triv m) (R.νV i A.μ0) (R.fdV i A.μ0) ∧ Bridge.IsReps (Bridge.ratF (Vc D i)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (R.B.L i A.μ0).pres.y ∧ H.Is (Bridge.AdForms (Bridge.ratF (Vc D i)) c.coef.ρ (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.chrOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m))) (Bridge.adInner (Bridge.ratF (Vc D i)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (R.B.L i A.μ0).pres.y) := by
  first | exact @GlobalTheory.ConjLiftData.isLiftDataC_of_liftData | exact GlobalTheory.ConjLiftData.isLiftDataC_of_liftData | (intros; apply GlobalTheory.ConjLiftData.isLiftDataC_of_liftData <;> assumption)
end
end
