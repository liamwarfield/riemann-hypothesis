module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteLastStepRealIntertwiner
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaLiftMultiplicitySpacesOfPublishedStatement
public import Lean.LibrarySuggestions.Basic
public import Lean.Elab.Command
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMultiplicityLiftLastChainStep

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerStepsOfStepsOK
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.IndefR.Cx GlobalTheory.Chain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.InnerLift

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

def InnerSteps : Prop :=
  ∀ t (k : Fin D.R.m), (k : ℕ) + 1 < D.R.m → IsStepWeil k R.ψ (Yc D k) (Yc D (k + 1)) (R.ωY t k) ∧
    IsVacVec R.ψ R.θ (R.MY k) (R.MY (k + 1)) (R.vY t k)

def InnerLaws : Prop :=
  ∀ t k, k + 1 < D.R.m → ∀ κ ∈ levS _ (R.βY k) (R.datYt t k R.triv), κ ∈ GfC (Yc D k) ∧
    R.ωY t k (κ, 1) (R.vY t k) = levChi _ (R.βY k) (R.datYt t k R.triv) κ • R.vY t k

theorem haar_fund (hν : R.models_νY) (hν' : R.models_νY') (t : T) (j : ℕ) (hj : j < D.R.m) :
    (R.νY t j).IsHaarMeasure ∧ MeasureTheory.IsFundamentalDomain (GQ (Yc D j)) (R.fdY t j) (R.νY t j) := by
  by_cases h : j + 1 < D.R.m
  · exact ⟨(hν t j h).1.1, (hν t j h).2⟩
  · have e : j = D.R.m - 1 := by omega
    subst e
    exact ⟨(hν' t).1.1, (hν' t).2⟩

theorem ioYSt_of_inner (hP : IoPair D) (hC : ∀ k, ChainPar D k) (hθ : IsInfFam R.θ) (hS : InnerSteps R)
    (hL : InnerLaws R) (hν : R.models_νY) (hν' : R.models_νY') (hI : R.chain_ItY) : IoYSt R := by
  intro t k hk
  have hk0 : k < D.R.m := by omega
  obtain ⟨hW, hV⟩ := hS t ⟨k, hk0⟩ hk
  exact hP.of_index_eq ⟨k, hk0⟩ (min k D.R.m) (min (k + 1) D.R.m) (min_eq_left hk0.le) (min_eq_left hk.le)
    (Yc D k) (Yc D (k + 1)) (R.MY k) (R.MY (k + 1)) R.θ R.ψ hθ (hC _) (R.ωY t k) (R.vY t k) hW hV
    (R.ItY k) (hI t k hk) _ _ (hL t k hk) _ _ (haar_fund R hν hν' t _ hk).1 (haar_fund R hν hν' t _ hk).2
    _ _ (R.CC t (k + 1)) le_rfl

theorem exists_ioY_of_ioYSt (h : IoYSt R) : ∃ io, ({ R with ioY := io } : RealDat D A Ks).chain_ioY := by
  classical
  have key : ∀ t k, ∃ io : R.CC t (k + 1) →ₗ[ℂ] R.CC t k, k + 1 < D.R.m →
      Lift.IsIo (R.νY t (k + 1)) (R.fdY t (k + 1)) (thetaKO (R.ωY t k)) (R.ptY t k) (R.ItY k)
        (R.CC t (k + 1)) (R.CC t k) io := by
    intro t k
    by_cases hk : k + 1 < D.R.m
    · obtain ⟨io, hio⟩ := h t k hk
      exact ⟨io, fun _ => hio⟩
    · exact ⟨0, fun h' => absurd h' hk⟩
  choose io hio using key
  exact ⟨io, fun t k hk => hio t k (by omega)⟩

theorem exists_ioY_of_pair (hP : IoPair D) (hC : ∀ k, ChainPar D k) (hS : InnerSteps R) (hL : InnerLaws R)
    (hM : R.IsModels) (hI : R.chain_ItY) : ∃ io, ({ R with ioY := io } : RealDat D A Ks).chain_ioY :=
  exists_ioY_of_ioYSt R (ioYSt_of_inner R hP hC hM.inf hS hL hM.νY hM.νY' hI)

end GlobalTheory.Chain.InnerLift

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LastStepIntertwinerOneTupleAllTuples
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LastStepIntertwinerOneTupleAllTuples
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.Chain GlobalTheory.CompactHowe GlobalTheory.CompactHowe.LastStep
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IntertwinerTransfer

variable {D : D7} {V W : HSp D} {S S' : D.what₂.Tau → SPar}

theorem isItW_transfer (θ : InfFam D) (M : DSModel V S) (M' : DSModel W S')
    (ρ : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ → PolF D W.rank V.rank → PolF D W.rank V.rank)
    (ρ' : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ → PolF D W.rank V.rank → PolF D W.rank V.rank)
    (hd : ∀ τ g φ, (ρ τ g φ).totalDegree ≤ φ.totalDegree) (hd' : ∀ τ h φ, (ρ' τ h φ).totalDegree ≤ φ.totalDegree)
    (ω ω₁ : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (pt pt₁ : PolF D W.rank V.rank →ₗ[ℂ] (WO V W → ℂ))
    (hpt : Function.Injective pt) (hpt₁ : Function.Injective pt₁)
    (hω : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ φ, ω (atTau θ V τ g, 1) (pt φ) = pt (ρ τ g φ))
    (hω' : ∀ τ, ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D W τ), ∀ φ, ω (1, atTau θ W τ h) (pt φ) = pt (ρ' τ h φ))
    (hω₁ : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ φ, ω₁ (atTau θ V τ g, 1) (pt₁ φ) = pt₁ (ρ τ g φ))
    (hω₁' : ∀ τ, ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D W τ), ∀ φ, ω₁ (1, atTau θ W τ h) (pt₁ φ) = pt₁ (ρ' τ h φ))
    (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M) (hIt : IsItW θ M M' ω pt It) :
    IsItW θ M M' ω₁ pt₁ It := by
  refine ⟨hIt.ne, hIt.bdd, ?_, ?_, ?_, ?_⟩
  · intro τ g hg φ φ' h v
    rw [hω₁ τ g hg] at h
    refine hIt.eqK τ g hg φ φ' ?_ v
    rw [hω τ g hg, hpt₁ h]
  · intro τ X hX φ φ' h v
    have hm : ∀ t : ℝ, NormedSpace.exp (t • X) ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) :=
      fun t => GlobalTheory.GardingVec.exp_mem (GlobalTheory.CompactIntertwiner.isUnit_gram M τ) hX t
    simp only [oneP, hω₁ τ _ (hm _)] at h
    refine hIt.eqg τ X hX φ φ' (fun z => ?_) v
    simp only [oneP, hω τ _ (hm _)]
    exact GlobalTheory.CompactIntertwiner.hasDerivAt_pol pt₁ hpt₁ (fun t : ℝ => ρ τ (NormedSpace.exp (t • X)) φ) _
      (fun t => hd τ _ φ) φ' h (LinearMap.proj z ∘ₗ pt)
  · intro τ h hh φ φ' v v' e e'
    rw [hω₁' τ h hh] at e
    refine hIt.invK τ h hh φ φ' v v' ?_ e'
    rw [hω' τ h hh, hpt₁ e]
  · intro τ X hX φ φ' v v' h h'
    have hm : ∀ t : ℝ, NormedSpace.exp (t • X) ∈ Formalism.QuantumDeterminants.UH (gramAt D W τ) :=
      fun t => GlobalTheory.GardingVec.exp_mem (GlobalTheory.CompactIntertwiner.isUnit_gram M' τ) hX t
    simp only [oneP, hω₁' τ _ (hm _)] at h
    refine hIt.invg τ X hX φ φ' v v' (fun z => ?_) h'
    simp only [oneP, hω' τ _ (hm _)]
    exact GlobalTheory.CompactIntertwiner.hasDerivAt_pol pt₁ hpt₁ (fun t : ℝ => ρ' τ (NormedSpace.exp (t • X)) φ) _
      (fun t => hd' τ _ φ) φ' h (LinearMap.proj z ∘ₗ pt)


open Classical in
theorem isItW_lastStep_transfer (k : Fin D.R.m) (hk : (k : ℕ) + 1 = D.R.m) (a : ℕ) (ha : a = k) (hV : V.SigOK)
    (hW : W.SigOK) (rV : V.rank = D.R.r + k * D.R.t) (rW : W.rank = V.rank + D.R.t)
    (M : DSModel V (parB (Ptw D) a)) (M' : DSModel W (parB (Ptw D) D.R.m)) (θ : InfFam D) (hθ : IsInfFam θ)
    (ψ : AddChar (AF D.host.F) ℂ) (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M)
    (ω ω₁ : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f f₁ : WO V W → ℂ)
    (hω : IsStepWeil k ψ V W ω) (hf : IsVacVec ψ θ M M' f) (hω₁ : IsStepWeil k ψ V W ω₁) (hf₁ : IsVacVec ψ θ M M' f₁)
    (hIt : IsItW θ M M' ω (ptOf ψ θ M M' f) It) : IsItW θ M M' ω₁ (ptOf ψ θ M M' f₁) It := by
  subst ha
  have hp := fun τ => GlobalTheory.T.lastStep_parameters_partition_extended_by_zeros D k τ V.rank W.rank (M.lam τ) (M.ε τ) (M'.lam τ) (M'.ε τ) hk rV rW (M.enum τ) (M'.enum τ)
  have hε := fun τ => (hp τ).1
  have hε' := fun τ => (hp τ).2.1
  choose x₁ x₃ h1 h3 _ using fun τ => (hp τ).2.2
  have act : ∀ (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f : WO V W → ℂ), IsStepWeil k ψ V W ω →
      IsVacVec ψ θ M M' f →
      (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ φ, ω (atTau θ V τ g, 1) (ptOf ψ θ M M' f φ) =
        ptOf ψ θ M M' f (polAct M M' x₁ x₃ (Function.update (fun _ => 1) τ g) (fun _ => 1) φ)) ∧
      (∀ τ, ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D W τ), ∀ φ, ω (1, atTau θ W τ h) (ptOf ψ θ M M' f φ) =
        ptOf ψ θ M M' f (polAct M M' x₁ x₃ (fun _ => 1) (Function.update (fun _ => 1) τ h) φ)) := by
    intro ω f hω hf
    refine ⟨fun τ g hg φ => ?_, fun τ h hh φ => ?_⟩
    · have := om_ptOf hθ hV hW M M' hε hε' x₁ x₃ h1 h3 hω hf (GlobalTheory.PointAtPlaceHom.atTau_mem (θ := θ) V τ g) (one_mem _) φ
      rwa [compAt_atTau hθ τ hg, compAt_one] at this
    · have := om_ptOf hθ hV hW M M' hε hε' x₁ x₃ h1 h3 hω hf (one_mem _) (GlobalTheory.PointAtPlaceHom.atTau_mem (θ := θ) W τ h) φ
      rwa [compAt_atTau hθ τ hh, compAt_one] at this
  have a0 := act ω f hω hf
  have a1 := act ω₁ f₁ hω₁ hf₁
  exact isItW_transfer θ M M' (fun τ g => polAct M M' x₁ x₃ (Function.update (fun _ => 1) τ g) fun _ => 1)
    (fun τ h => polAct M M' x₁ x₃ (fun _ => 1) (Function.update (fun _ => 1) τ h))
    (fun _ _ _ => totalDegree_polAct _ _ _ _ _ _ _) (fun _ _ _ => totalDegree_polAct _ _ _ _ _ _ _) ω ω₁
    (pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') f)
    (pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') f₁)
    (GlobalTheory.T.fockVectorsOfThetaDatum_injective D V W _ _ ψ θ M M' f hω.choose_spec.choose_spec.1.std hθ hf)
    (GlobalTheory.T.fockVectorsOfThetaDatum_injective D V W _ _ ψ θ M M' f₁ hω₁.choose_spec.choose_spec.1.std hθ hf₁)
    a0.1 a0.2 a1.1 a1.2 It hIt

theorem pItX_of_one : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsModels → R.chain_ωX → R.chain_vX → ∀ (t₀ : T) (y : PolF D D.sp.X'.rank (Yc D (D.R.m - 1)).rank →ₗ[ℂ] SmT R.MX →ₗ[ℂ] SmT (R.MY (D.R.m - 1))), IsItW R.θ (R.MY (D.R.m - 1)) R.MX (R.ωX t₀) (R.ptX t₀) y → R.PItX y := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hL hM hω hv t₀ y hy t
  have hm := D.R.two_le_m
  let k : Fin D.R.m := ⟨D.R.m - 1, by omega⟩
  have hk : (k : ℕ) = D.R.m - 1 := rfl
  have hS := fun t => GlobalTheory.T.lastThetaChainStep_exponents_and_nonzero_vacuum D G Pl0 T A Ks R hL hM.inf hω hv t k hk
  have rV : (Yc D (D.R.m - 1)).rank = D.R.r + k * D.R.t := by
    rw [D.sp.Y_rank _ (min_le_right _ _), min_eq_left (Nat.sub_le _ _)]; rfl
  have rW : D.sp.X'.rank = (Yc D (D.R.m - 1)).rank + D.R.t := by
    rw [rV, D.sp.X'_rank, Ranks.rankX', add_assoc, ← Nat.succ_mul]
    congr 2
    omega
  exact isItW_lastStep_transfer k (by omega) (min (D.R.m - 1) D.R.m) (by omega) (D.sp.Y_sig _) D.sp.X'_sig rV rW
    (R.MY (D.R.m - 1)) R.MX R.θ hM.inf R.ψ y (R.ωX t₀) (R.ωX t) (R.vX t₀) (R.vX t) (hS t₀).1 (hS t₀).2 (hS t).1 (hS t).2 hy

end GlobalTheory.IntertwinerTransfer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LastStepIntertwinerOneTupleAllTuplesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastStep_intertwiner_one_tuple_all_tuples : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsModels → R.chain_ωX → R.chain_vX → ∀ (t₀ : T) (y : PolF D D.sp.X'.rank (Yc D (D.R.m - 1)).rank →ₗ[ℂ] SmT R.MX →ₗ[ℂ] SmT (R.MY (D.R.m - 1))), IsItW R.θ (R.MY (D.R.m - 1)) R.MX (R.ωX t₀) (R.ptX t₀) y → R.PItX y := by
  first | exact @GlobalTheory.IntertwinerTransfer.pItX_of_one | exact GlobalTheory.IntertwinerTransfer.pItX_of_one | (intros; apply GlobalTheory.IntertwinerTransfer.pItX_of_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PItYOfOne
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Chain.ItAllTuples

variable {D : D7}

theorem isItW_smul {V W : HSp D} {S S' : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {M' : DSModel W S'}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {pt : PolF D W.rank V.rank → (WO V W → ℂ)}
    {It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M} (h : IsItW θ M M' ω pt It) {c : ℂ} (hc : c ≠ 0) :
    IsItW θ M M' ω pt (c • It) := by
  refine { ne := smul_ne_zero hc h.ne, bdd := ?_, eqK := ?_, eqg := ?_, invK := ?_, invg := ?_ }
  · intro φ w
    obtain ⟨b, hb⟩ := h.bdd φ w
    refine ⟨‖c‖ * b, fun v => ?_⟩
    have e : ellT M w (inclT M ((c • It) φ (PiTensorProduct.tprod ℂ v))) =
        c * ellT M w (inclT M (It φ (PiTensorProduct.tprod ℂ v))) := by
      rw [LinearMap.smul_apply, LinearMap.smul_apply, map_smul, map_smul, smul_eq_mul]
    rw [e, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hb v) (norm_nonneg _)
  · intro τ g hg φ φ' hφ v
    rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply, map_smul, map_smul,
      map_smul, h.eqK τ g hg φ φ' hφ v]
  · intro τ X hX φ φ' hφ v w
    have := (h.eqg τ X hX φ φ' hφ v w).const_mul c
    simp only [LinearMap.smul_apply, map_smul, smul_eq_mul]
    exact this
  · intro τ g hg φ φ' v v' hφ hv
    rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply,
      h.invK τ g hg φ φ' v v' hφ hv]
  · intro τ X hX φ φ' v v' hφ hv
    rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply, ← smul_add,
      h.invg τ X hX φ φ' v v' hφ hv, smul_zero]

theorem pItY_of_one : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), (∀ k, GlobalTheory.Chain.ChainPar D k) → R.toLevCh.Is A.μ0 → R.IsModels → R.chain_ωY → R.chain_ωX → R.chain_vY → R.chain_vX → ∀ (k : ℕ), k + 1 < D.R.m → ∀ (t₀ : T) (y : PolF D (Yc D (k + 1)).rank (Yc D k).rank →ₗ[ℂ] SmT (R.MY (k + 1)) →ₗ[ℂ] SmT (R.MY k)), IsItW R.θ (R.MY k) (R.MY (k + 1)) (R.ωY t₀ k) (R.ptY t₀ k) y → R.PItY k y := by
  intro h1 h2 D G _ _ Pl0 T A Ks _ _ _ R hC hL hM hωY hωX hvY hvX k hk t₀ y hy
  have hk0 : k < D.R.m := by omega
  have hSt := GlobalTheory.Chain.StepVac.stepsOK D G Pl0 T A Ks R hL hM.inf hωY hωX hvY hvX
  obtain ⟨y₀, hy₀⟩ := GlobalTheory.Chain.innerIntertwiners_of_pair D G Pl0 T A Ks R (GlobalTheory.T.exists_uniformRealThetaIntertwiner_chainStep h1 h2 D) hC hM.inf hSt k hk
  have hS := hSt.1 t₀ ⟨k, hk0⟩ hk
  have key : ∀ (V W : HSp D) (a b : ℕ) (_ : a = k) (_ : b = k + 1) (M : DSModel V (parB (Ptw D) a))
      (M' : DSModel W (parB (Ptw D) b)) ω f, GlobalTheory.Chain.IsStepWeil ⟨k, hk0⟩ R.ψ V W ω → GlobalTheory.Chain.IsVacVec R.ψ R.θ M M' f →
      ∀ It It' : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M, IsItW R.θ M M' ω (GlobalTheory.Chain.ptOf R.ψ R.θ M M' f) It →
        IsItW R.θ M M' ω (GlobalTheory.Chain.ptOf R.ψ R.θ M M' f) It' → ∃ c : ℂ, It' = c • It := by
    intro V W a b ha hb M M' ω f
    subst ha hb
    exact GlobalTheory.T.realThetaIntertwiners_proportional_of_discreteSeries h1 h2 D ⟨a, hk0⟩ V W M M' R.θ R.ψ hM.inf (hC _) ω f
  obtain ⟨c, hc⟩ := key _ _ _ _ (min_eq_left hk0.le) (min_eq_left hk.le) (R.MY k) (R.MY (k + 1)) _ _ hS.1 hS.2 y₀ y
    (hy₀ t₀) hy
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hy.ne (by rw [hc, zero_smul])
  intro t
  rw [hc]
  exact isItW_smul (hy₀ t) hc0

end GlobalTheory.Chain.ItAllTuples

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ConjExt

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

set_option maxHeartbeats 4000000 in
theorem models_with (h : R.IsModels) (ioY ioX Th thF thG) :
    ({ R with ioY := ioY, ioX := ioX, Th := Th, thF := thF, thG := thG } : RealDat D A Ks).IsModels :=
  ⟨h.inf, h.vpos, h.cX, h.cV, h.prX, h.HX, h.HV, h.HE, h.HW, h.gE, h.gW, h.jX, h.jV, h.νY, h.νY', h.ν0, h.νX, h.νV, h.νW, h.BV,
    h.order⟩

set_option maxHeartbeats 4000000 in
theorem fam_with (h : R.IsFam) (ioY ioX Th thF thG) :
    ({ R with ioY := ioY, ioX := ioX, Th := Th, thF := thF, thG := thG } : RealDat D A Ks).IsFam :=
  ⟨h.tie, h.Sb, h.roots, h.pl_onto, h.degR, h.degL, h.muVal, h.etaVal⟩

theorem chain_with (hωY : R.chain_ωY) (hωX : R.chain_ωX) (hvY : R.chain_vY) (hvX : R.chain_vX) (a : R.chain_ptY)
    (b : R.chain_ptX) (c : R.chain_ItY) (d : R.chain_ItX) (ioY ioX Th) (e : ({ R with ioY := ioY } : RealDat D A Ks).chain_ioY)
    (f : ({ R with ioX := ioX } : RealDat D A Ks).chain_ioX)
    (g : ({ R with ioY := ioY, ioX := ioX, Th := Th } : RealDat D A Ks).chain_Th) :
    ({ R with ioY := ioY, ioX := ioX, Th := Th } : RealDat D A Ks).IsChain :=
  ⟨hωY, hωX, hvY, hvX, a, b, c, d, e, f, g⟩

theorem exists_th (hL : R.toLevCh.Is A.μ0) (hr : R.grp_record) (hF : R.IsFam) (hM : R.IsModels) (ioY ioX) :
    ∃ Th, ({ R with ioY := ioY, ioX := ioX, Th := Th } : RealDat D A Ks).chain_Th :=
  GlobalTheory.ProjectedLift.exists_chain_Th D G Pl0 T A Ks { R with ioY := ioY, ioX := ioX } hL
    (fam_with hF ioY ioX R.Th R.thF R.thG) (models_with hM ioY ioX R.Th R.thF R.thG) hr


set_option maxHeartbeats 800000 in
theorem exists_chain (h₁ : GlobalTheory.Published.DiscreteSeriesCover) (h₂ : GlobalTheory.Published.HarishChandraModules) (h₃ : GlobalTheory.Published.CuspRapidDecay)
    (h₄ : GlobalTheory.Published.CasselmanWallach) (hP : ∀ k, GlobalTheory.Chain.ChainPar D k) (hL : R.toLevCh.Is A.μ0) (hr : R.grp_record)
    (hF : R.IsFam) (hM : R.IsModels) (hωY : R.chain_ωY) (hωX : R.chain_ωX) (hvY : R.chain_vY) (hvX : R.chain_vX) (t₀ : T)
    (hY : ∀ k, k + 1 < D.R.m → IsItW R.θ (R.MY k) (R.MY (k + 1)) (R.ωY t₀ k) (R.ptY t₀ k) (R.ItY k))
    (hX : IsItW R.θ (R.MY (D.R.m - 1)) R.MX (R.ωX t₀) (R.ptX t₀) R.ItX) :
    ∃ ioY ioX Th, ({ R with ioY := ioY, ioX := ioX, Th := Th } : RealDat D A Ks).IsChain := by
  have hS := GlobalTheory.Chain.StepVac.stepsOK D G Pl0 T A Ks R hL hM.inf hωY hωX hvY hvX
  have hW := GlobalTheory.T.chainSteps_levelCharacter_conditions_hold D G Pl0 T A Ks R hL hM.inf hωY hωX hvY hvX
  have hIY : R.chain_ItY := fun t k hk =>
    GlobalTheory.Chain.ItAllTuples.pItY_of_one h₁ h₂ D G Pl0 T A Ks R hP hL hM hωY hωX hvY hvX k hk t₀ _ (hY k hk) t
  have hIX : R.chain_ItX := GlobalTheory.T.lastStep_intertwiner_one_tuple_all_tuples D G Pl0 T A Ks R hL hM hωX hvX t₀ _ hX
  have hpY : R.chain_ptY := fun t k hk P =>
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO (hωY t k hk).std hM.inf _ _ _ _ (hS.1 t ⟨k, by omega⟩ hk).2.theta P
  have hpX : R.chain_ptX := (GlobalTheory.T.definite_lastStep_real_intertwiner D G Pl0 T A Ks R hL hF hM hωX hvX).1
  exact (GlobalTheory.Chain.InnerLift.exists_ioY_of_pair R (GlobalTheory.T.exists_thetaLift_multiplicitySpaces_of_hypotheses h₁ h₂ h₃ h₄ D) hP hS.1 hW.1 hM hIY).elim fun ioY hioY =>
    (GlobalTheory.T.exists_multiplicityLift_lastChainStep D G Pl0 T A Ks R hL hF hM hωX hvX hpX hIX).elim fun ioX hioX =>
    (exists_th hL hr hF hM ioY ioX).elim fun Th hTh =>
    ⟨ioY, ioX, Th, chain_with hωY hωX hvY hvX hpY hpX hIY hIX ioY ioX Th hioY hioX hTh⟩


set_option maxHeartbeats 4000000 in
theorem exists_thP (h₃ : GlobalTheory.Published.CuspRapidDecay) (hL : R.toLevCh.Is A.μ0) (hF : R.IsFam) (hM : R.IsModels) (hω : R.thP_ωP)
    (hv : R.thP_vP) (t₀ : T)
    (hI : ∀ i, IsIoW R.θ (R.MW i (sg0 D A)) (R.cV i) (R.ωP i t₀) (R.ptP i t₀) (RealDat.Delta i) (R.ioP i)) :
    ∃ thF thG, ({ R with thF := thF, thG := thG } : RealDat D A Ks).IsThP := by
  have hp : R.thP_pt_theta := (GlobalTheory.T.exists_lowestKType_fockMap_thetaVectors D G Pl0 T A Ks R hL hF hM hω hv).1
  have hio : R.thP_ioP := fun i => GlobalTheory.IoAllTuples.ioP_of_isIoW_at D G Pl0 T A Ks R hL hF hM hω hv i t₀ _ (hI i)
  obtain ⟨thF, h1, h2⟩ := GlobalTheory.T.exists_thetaLift_linearMap_cuspFormMultiplicity h₃ D G Pl0 T A Ks R hL hF hM hω hv hp hio
  obtain ⟨thG, h3⟩ := GlobalTheory.GoodProjLift.exists_thG D G Pl0 T A Ks { R with thF := thF } hL
    (fam_with hF R.ioY R.ioX R.Th thF R.thG) (models_with hM R.ioY R.ioX R.Th thF R.thG) h1
  exact ⟨thF, thG, hω, hv, hp, hio, h1, h2, h3⟩

end GlobalTheory.ConjExt

end
