module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsContinuousLeftInvariantRepConjugateTensor
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaTensorRuleOrthogonalSumSource
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AnisotropicTermsMeanZeroUnipotentRadical
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegrableOfRapidDecay

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatAdelicMatrixOfMemAdelicSchwartz
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatAdelicMatrixOfMemAdelicSchwartz
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW
open scoped ContDiff
open scoped TensorProduct Topology

noncomputable section

namespace GlobalTheory.SchwartzPure

open GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies

variable {D : D7} {m n : ℕ}

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

def periods {M : Type} [AddCommGroup M] (Φ : M → ℂ) : AddSubgroup M where
  carrier := {u | ∀ x, Φ (x + u) = Φ x}
  zero_mem' := fun x => by rw [add_zero]
  add_mem' := fun {a b} ha hb x => by rw [← add_assoc, hb, ha]
  neg_mem' := fun {a} ha x => by
    have := ha (x + -a)
    rw [neg_add_cancel_right] at this
    exact this.symm

theorem isOpen_periods {M : Type} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M] {Φ : M → ℂ}
    (h1 : IsLocallyConstant Φ) (h2 : HasCompactSupport Φ) : IsOpen (periods Φ : Set M) :=
  AddSubgroup.isOpen_of_mem_nhds _ (eventually_invariant h1 h2)

theorem zero : IsSchwartzBruhat (0 : Mx D m n → ℂ) := by
  exact
    { level := ⟨⊤, isOpen_univ, fun _ _ _ _ => rfl⟩
      supp := ⟨∅, isCompact_empty, fun _ h => absurd rfl h⟩
      schwartz := fun _ _ _ _ _ => ⟨0, fun _ => rfl⟩ }

theorem add {φ ψ : Mx D m n → ℂ} (hφ : IsSchwartzBruhat φ) (hψ : IsSchwartzBruhat ψ) : IsSchwartzBruhat (φ + ψ) := by
  refine { level := ?_, supp := ?_, schwartz := ?_ }
  · obtain ⟨U, hU, h⟩ := hφ.level
    obtain ⟨U', hU', h'⟩ := hψ.level
    refine ⟨U ⊓ U', hU.inter hU', fun u hu h0 x => ?_⟩
    simp only [Pi.add_apply, h u hu.1 h0, h' u hu.2 h0]
  · obtain ⟨K, hK, h⟩ := hφ.supp
    obtain ⟨K', hK', h'⟩ := hψ.supp
    refine ⟨K ∪ K', hK.union hK', fun x hx => ?_⟩
    by_cases h1 : φ x = 0
    · exact Or.inr (h' x fun h2 => hx (by simp [h1, h2]))
    · exact Or.inl (h x h1)
  · intro k L hL hi x
    obtain ⟨g, hg⟩ := hφ.schwartz k L hL hi x
    obtain ⟨g', hg'⟩ := hψ.schwartz k L hL hi x
    exact ⟨g + g', fun t => by simp [hg, hg']⟩

theorem smul (c : ℂ) {φ : Mx D m n → ℂ} (hφ : IsSchwartzBruhat φ) : IsSchwartzBruhat (c • φ) := by
  refine { level := ?_, supp := ?_, schwartz := ?_ }
  · obtain ⟨U, hU, h⟩ := hφ.level
    exact ⟨U, hU, fun u hu h0 x => by simp only [Pi.smul_apply, h u hu h0]⟩
  · obtain ⟨K, hK, h⟩ := hφ.supp
    exact ⟨K, hK, fun x hx => h x fun h1 => hx (by simp [h1])⟩
  · intro k L hL hi x
    obtain ⟨g, hg⟩ := hφ.schwartz k L hL hi x
    exact ⟨c • g, fun t => by simp [hg]⟩

theorem compAt_add (θ : InfFam D) (τ : D.what₂.Tau) (x y : Mx D m n) :
    compAt θ τ (x + y) = compAt θ τ x + compAt θ τ y := by
  ext i j
  simp only [compAt, Matrix.map_apply, Matrix.add_apply]
  rw [map_add (infPart D), map_add (θ τ)]

def realVec {k : ℕ} (θ : InfFam D) (L : (Fin k → ℝ) →+ Mx D m n) : (Fin k → ℝ) →+ (D.what₂.Tau → Fin m → Fin n → ℂ) where
  toFun t := fun τ i j => compAt θ τ (L t) i j
  map_zero' := by ext τ i j; simp [compAt]
  map_add' a b := by ext τ i j; simp [compAt_add]

theorem norm_compAt_le (θ : InfFam D) (x : Mx D m n) (τ : D.what₂.Tau) (i : Fin m) (j : Fin n) :
    ‖compAt θ τ x i j‖ ≤ GlobalTheory.Unf.realSize θ x := by
  unfold GlobalTheory.Unf.realSize
  calc ‖compAt θ τ x i j‖ ≤ ∑ j', ‖compAt θ τ x i j'‖ :=
        Finset.single_le_sum (f := fun j' => ‖compAt θ τ x i j'‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', ‖compAt θ τ x i' j'‖ :=
        Finset.single_le_sum (f := fun i' => ∑ j', ‖compAt θ τ x i' j'‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)
    _ ≤ _ := Finset.single_le_sum (f := fun τ' => ∑ i', ∑ j', ‖compAt θ τ' x i' j'‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ τ)

theorem realSize_nonneg (θ : InfFam D) (x : Mx D m n) : 0 ≤ GlobalTheory.Unf.realSize θ x :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem norm_vec_le (θ : InfFam D) (x : Mx D m n) :
    ‖(fun τ i j => compAt θ τ x i j : D.what₂.Tau → Fin m → Fin n → ℂ)‖ ≤ GlobalTheory.Unf.realSize θ x :=
  (pi_norm_le_iff_of_nonneg (realSize_nonneg θ x)).2 fun τ =>
    (pi_norm_le_iff_of_nonneg (realSize_nonneg θ x)).2 fun i =>
      (pi_norm_le_iff_of_nonneg (realSize_nonneg θ x)).2 fun j => norm_compAt_le θ x τ i j

theorem realSize_le (θ : InfFam D) (x : Mx D m n) :
    GlobalTheory.Unf.realSize θ x ≤ (Fintype.card D.what₂.Tau * (m * n) : ℝ) *
      ‖(fun τ i j => compAt θ τ x i j : D.what₂.Tau → Fin m → Fin n → ℂ)‖ := by
  set v : D.what₂.Tau → Fin m → Fin n → ℂ := fun τ i j => compAt θ τ x i j with hv
  unfold GlobalTheory.Unf.realSize
  calc ∑ τ, ∑ i, ∑ j, ‖compAt θ τ x i j‖ ≤ ∑ τ : D.what₂.Tau, ∑ i : Fin m, ∑ j : Fin n, ‖v‖ :=
        Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          (norm_le_pi_norm (v τ i) j).trans ((norm_le_pi_norm (v τ) i).trans (norm_le_pi_norm v τ))
    _ = _ := by simp [Finset.sum_const]; ring

theorem realSize_zero (θ : InfFam D) : GlobalTheory.Unf.realSize θ (0 : Mx D m n) = 0 := by
  simp [GlobalTheory.Unf.realSize, compAt]

def finVec : Mx D m n →+ (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) where
  toFun x := fun i j => finPart D (x i j)
  map_zero' := by ext i j; exact (finPart D).map_zero
  map_add' a b := by ext i j; exact (finPart D).map_add _ _

theorem continuous_finVec : Continuous (finVec (D := D) (m := m) (n := n)) :=
  continuous_pi fun i => continuous_pi fun j =>
    (GlobalTheory.Member.continuous_finPart D).comp ((continuous_apply j).comp (continuous_apply i))

theorem pure (θ : InfFam D) (hθ : IsInfFam θ) (f : SchwartzMap (D.what₂.Tau → Fin m → Fin n → ℂ) ℂ)
    (g : (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ)
    (hg : g ∈ GlobalTheory.WeilM.SB (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E)) :
    IsSchwartzBruhat fun x : Mx D m n => f (fun τ i j => compAt θ τ x i j) * g (fun i j => finPart D (x i j)) := by
  refine { level := ?_, supp := ?_, schwartz := ?_ }
  · have : IsModuleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
    have : IsTopologicalAddGroup (Af D.host.F ⊗[D.host.F] D.host.E) :=
      IsModuleTopology.isTopologicalAddGroup (Af D.host.F) _
    set P := (finVec : Mx D m n →+ (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E)) with hP
    refine ⟨(periods g).comap P, (isOpen_periods hg.1 hg.2).preimage continuous_finVec, fun u hu h0 x => ?_⟩
    have e1 : ∀ τ, compAt θ τ (x + u) = compAt θ τ x := fun τ => by
      rw [compAt_add]
      ext i j
      have h := congrFun (congrFun h0 i) j
      simp only [Matrix.map_apply, Matrix.zero_apply] at h
      simp only [Matrix.add_apply, compAt, Matrix.map_apply, h, (θ τ).map_zero, add_zero]
    have e2 : (fun i j => finPart D ((x + u) i j)) = (fun i j => finPart D (x i j)) + P u :=
      P.map_add x u
    simp only [e1, e2]
    rw [show g ((fun i j => finPart D (x i j)) + P u) = g (fun i j => finPart D (x i j)) from hu _]
  · exact ⟨tsupport g, hg.2.isCompact, fun x hx => subset_tsupport g (right_ne_zero_of_mul hx)⟩
  · intro k L hL hi x
    obtain ⟨⟨C₁, hC₁⟩, hlow⟩ := GlobalTheory.T.adelicMatrixRealSize_bounds_along_real_parametrisation D θ hθ m n k L hL
    obtain ⟨C₂, hC₂⟩ := hlow hi
    have hAb : ∀ t, ‖realVec θ L t‖ ≤ C₁ * ‖t‖ := fun t => (norm_vec_le θ (L t)).trans (hC₁ t)
    have hAc : Continuous (realVec θ L) := AddMonoidHomClass.continuous_of_bound (realVec θ L) C₁ hAb
    set Al := (realVec θ L).toRealLinearMap hAc with hAl
    have hAlt : ∀ t, Al t = realVec θ L t := fun t => rfl
    have hker : (Al : (Fin k → ℝ) →ₗ[ℝ] (D.what₂.Tau → Fin m → Fin n → ℂ)).ker = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro t ht
      have h0 : realVec θ L t = 0 := by rw [← hAlt]; exact ht
      have h1 := hC₂ 0 t
      rw [zero_add, realSize_zero, add_zero] at h1
      have h2 := realSize_le θ (L t)
      have h3 : (fun τ i j => compAt θ τ (L t) i j : D.what₂.Tau → Fin m → Fin n → ℂ) = 0 := h0
      rw [h3, norm_zero, mul_zero] at h2
      have h4 : GlobalTheory.Unf.realSize θ (L t) = 0 := le_antisymm h2 (realSize_nonneg θ _)
      rw [h4, mul_zero] at h1
      exact norm_le_zero_iff.mp h1
    obtain ⟨K, -, hK⟩ := (Al : (Fin k → ℝ) →ₗ[ℝ] (D.what₂.Tau → Fin m → Fin n → ℂ)).exists_antilipschitzWith hker
    set a : D.what₂.Tau → Fin m → Fin n → ℂ := fun τ i j => compAt θ τ x i j with ha
    have hgr : Function.HasTemperateGrowth (fun t => a + Al t) :=
      (Function.HasTemperateGrowth.const a).add Al.hasTemperateGrowth
    have hanti : AntilipschitzWith K (fun t => a + Al t) :=
      AntilipschitzWith.of_le_mul_dist fun s t => by rw [dist_add_left]; exact hK.le_mul_dist s t
    refine ⟨g (fun i j => finPart D (x i j)) • SchwartzMap.compCLMOfAntilipschitz ℂ hgr hanti f, fun t => ?_⟩
    have e1 : (fun τ i j => compAt θ τ (x + L t) i j : D.what₂.Tau → Fin m → Fin n → ℂ) = a + Al t := by
      ext τ i j
      rw [hAlt, compAt_add]
      rfl
    have e2 : (fun i j => finPart D ((x + L t) i j)) = (fun i j => finPart D (x i j)) := by
      ext i j
      have h := congrFun (congrFun (hL.2 t) i) j
      simp only [Matrix.map_apply, Matrix.zero_apply] at h
      rw [Matrix.add_apply, map_add (finPart D), h, add_zero]
    simp only [e1, e2, smul_apply, SchwartzMap.compCLMOfAntilipschitz_apply, Function.comp_apply, smul_eq_mul]
    ring

theorem isSchwartzBruhat_of_mem_schwartzA : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n : ℕ),
    ∀ φ ∈ GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ m n, GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ := by
  intro D θ hθ m n φ hφ
  induction hφ using Submodule.span_induction with
  | mem φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    exact pure θ hθ f g hg
  | zero => exact zero
  | add _ _ _ _ h1 h2 => exact add h1 h2
  | smul c _ _ h => exact smul c h

end GlobalTheory.SchwartzPure
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatAdelicMatrixOfMemAdelicSchwartzStatement
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW
open scoped ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSchwartzBruhatAdelicMatrix_of_mem_adelicSchwartz : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n : ℕ), ∀ φ ∈ GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ m n, GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ := by
  first | exact @GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA | exact GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA | (intros; apply GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaTensorRuleTargetOrthogonalSum
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaTensorRuleTargetOrthogonalSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.TensorTargetRule

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger

variable {D : D7}

theorem heisO_zero' (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ) : heisO ψ S T 0 f = f := by
  funext w
  simp [heisO, symplOH, symplO, hO]

theorem dagger_resT_symm {T A B : HSp D} (d : OrthDec T A B) (S : HSp D) (u : WO S A) (v : WO S B) :
    dagger S T ((d.resT S).symm (u, v)) = (d.resS S).symm (dagger S A u, dagger S B v) := by
  rw [d.resT_symm_apply, d.resS_symm_apply, d.pA_eq, d.pB_eq]
  simp only [dagger, adj_add, adj_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, cancel₂ (gA_mul_giA A),
    cancel₂ (gA_mul_giA B), Matrix.one_mul]

theorem dagger_resS_symm {T A B : HSp D} (d : OrthDec T A B) (S : HSp D) (u : WO A S) (v : WO B S) :
    dagger T S ((d.resS S).symm (u, v)) = (d.resT S).symm (dagger A S u, dagger B S v) := by
  have h := dagger_resT_symm d S (dagger A S u) (dagger B S v)
  rw [dagger_dagger, dagger_dagger] at h
  rw [← h, dagger_dagger]

theorem resT_dagger {T A B : HSp D} (d : OrthDec T A B) (S : HSp D) (y : WO T S) :
    d.resT S (dagger T S y) = (dagger A S (d.resS S y).1, dagger B S (d.resS S y).2) := by
  have h := dagger_resS_symm d S (d.resS S y).1 (d.resS S y).2
  rw [Prod.mk.eta, AddEquiv.symm_apply_apply] at h
  rw [h, AddEquiv.apply_symm_apply]

theorem resS_dagger {T A B : HSp D} (d : OrthDec T A B) (S : HSp D) (x : WO S T) :
    d.resS S (dagger S T x) = (dagger S A (d.resT S x).1, dagger S B (d.resT S x).2) := by
  have h := dagger_resT_symm d S (d.resT S x).1 (d.resT S x).2
  rw [Prod.mk.eta, AddEquiv.symm_apply_apply] at h
  rw [h, AddEquiv.apply_symm_apply]

theorem cj_boxT {T A B : HSp D} (d : OrthDec T A B) (S : HSp D) (fA : WO S A → ℂ) (fB : WO S B → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger T S) (d.boxT S fA fB) = d.boxS S (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger A S) fA) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger B S) fB) := by
  funext y
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, OrthDec.boxT, OrthDec.boxS, resT_dagger, map_mul]

theorem conjAdjoint_cj {S T : HSp D} (om : Rep S T) (g : GA D S) (h : GA D T) (f : WO S T → ℂ) :
    conjAdjoint om (h, g) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger T S) f) = GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger T S) (om (g, h) f) :=
  cjEnd_cj (daggerEquiv S T) (om (g, h)) f

theorem cj_mem_span {X Y : Type} (e : Y → X) {s : Set (X → ℂ)} {s' : Set (Y → ℂ)} (h : ∀ g ∈ s, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj e g ∈ s')
    {g : X → ℂ} (hg : g ∈ Submodule.span ℂ s) : GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj e g ∈ Submodule.span ℂ s' := by
  induction hg using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span (h x hx)
  | zero =>
    have e0 : GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj e (0 : X → ℂ) = 0 := by funext y; simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]
    rw [e0]; exact zero_mem _
  | add x y _ _ hx hy =>
    have e1 : GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj e (x + y) = GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj e x + GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj e y := by funext z; simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]
    rw [e1]; exact add_mem hx hy
  | smul c x _ hx =>
    have e1 : GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj e (c • x) = starRingEnd ℂ c • GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj e x := by funext z; simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]
    rw [e1]; exact Submodule.smul_mem _ _ hx

theorem tensorTarget : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (T A B : HSp D) (d : OrthDec T A B) (S : HSp D), GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.TensorTarget ψ d S := by
  intro D ψ hψ T A B d S
  have thd : ∀ (S T : HSp D) (f : WO S T → ℂ), IsThetaFunO ψ T S (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger T S) f) ↔ IsThetaFunO ψ S T f :=
    fun S T => (GlobalTheory.T.hermitianAdjoint_symplectic_action_theta_heisenberg D ψ hψ S T).2.2.1
  have src := GlobalTheory.T.thetaTensorRule_orthogonalSum_source D ψ hψ T A B d S
  have cc : ∀ f : WO S T → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger S T) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger T S) f) = f := fun f => cj_cj _ _ (dagger_dagger S T) f
  refine
    { box_theta := fun fA fB hA hB => d.isThetaFunO_boxT hA hB
      box_zero := fun fA fB => d.boxT_zero S fA fB
      heis_box := fun fA fB => ⟨fun u => ?_, fun v => ?_⟩
      slice_theta := fun f hf => ⟨fun v => ?_, fun u => ?_⟩
      dense := fun f hf => ?_
      om_box := ?_
      om_slice := ?_ }
  · rw [d.heisO_boxT, AddEquiv.apply_symm_apply, heisO_zero']
  · rw [d.heisO_boxT, AddEquiv.apply_symm_apply, heisO_zero']
  · have h1 := (src.slice_theta (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger T S) f) ((thd S T f).2 hf)).1 (dagger S B v)
    rw [← thd S A]
    convert h1 using 1
    funext u
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, dagger_resS_symm, dagger_dagger]
  · have h1 := (src.slice_theta (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger T S) f) ((thd S T f).2 hf)).2 (dagger S A u)
    rw [← thd S B]
    convert h1 using 1
    funext v
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, dagger_resS_symm, dagger_dagger]
  · intro ε hε
    obtain ⟨g, hg, hgε⟩ := src.dense _ ((thd S T f).2 hf) ε hε
    refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger S T) g, cj_mem_span _ ?_ hg, fun x => ?_⟩
    · rintro _ ⟨f1, f2, h1, h2, rfl⟩
      refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger S A) f1, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger S B) f2, (thd A S f1).2 h1, (thd B S f2).2 h2, ?_⟩
      funext x
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, resS_dagger, map_mul]
    · have h := hgε (dagger S T x)
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, dagger_dagger] at h ⊢
      rw [← Complex.norm_conj, map_sub, Complex.conj_conj]
      exact h
  · intro χS χA χB omT omA omB hT hA hB g a b fA fB hfA hfB
    have key := src.om_box χA χB χS (conjAdjoint omT) (conjAdjoint omA) (conjAdjoint omB)
      (GlobalTheory.T.conj_weil_datum_via_adjoint_exchanged_pair D ψ S T χS (χA * χB) omT hT) (GlobalTheory.T.conj_weil_datum_via_adjoint_exchanged_pair D ψ S A χS χA omA hA)
      (GlobalTheory.T.conj_weil_datum_via_adjoint_exchanged_pair D ψ S B χS χB omB hB) a b g (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger A S) fA) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger B S) fB)
      ((thd S A fA).2 hfA) ((thd S B fB).2 hfB)
    rw [conjAdjoint_cj, conjAdjoint_cj, ← cj_boxT, ← cj_boxT, conjAdjoint_cj] at key
    have := congrArg (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger S T)) key
    rwa [cc, cc] at this
  · intro χS χA χB omT omA omB hT hA hB g a b f hf v
    have key := src.om_slice χA χB χS (conjAdjoint omT) (conjAdjoint omA) (conjAdjoint omB)
      (GlobalTheory.T.conj_weil_datum_via_adjoint_exchanged_pair D ψ S T χS (χA * χB) omT hT) (GlobalTheory.T.conj_weil_datum_via_adjoint_exchanged_pair D ψ S A χS χA omA hA)
      (GlobalTheory.T.conj_weil_datum_via_adjoint_exchanged_pair D ψ S B χS χB omB hB) a b g (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger T S) f) ((thd S T f).2 hf) (dagger S B v)
    have e1 : (fun u'' => conjAdjoint omB (b, g) (fun v'' => GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger T S) f ((d.resS S).symm (u'', v''))) (dagger S B v)) =
        GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger A S) (fun u' => omB (g, b) (fun v' => f ((d.resT S).symm (u', v'))) v) := by
      funext u''
      have hfun : (fun v'' => GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger T S) f ((d.resS S).symm (u'', v''))) =
          GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger B S) (fun v' => f ((d.resT S).symm (dagger A S u'', v'))) := by
        funext v''
        simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, dagger_resS_symm]
      rw [hfun, conjAdjoint_cj]
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, dagger_dagger]
    obtain ⟨k1, k2⟩ := key
    rw [e1] at k1 k2
    refine ⟨(thd S A _).1 k1, fun u => ?_⟩
    have h := k2 (dagger S A u)
    rw [conjAdjoint_cj, conjAdjoint_cj] at h
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, dagger_resS_symm, dagger_dagger] at h
    exact (starRingEnd ℂ).injective h

end GlobalTheory.TensorTargetRule

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaTensorRuleTargetOrthogonalSumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaTensorRule_targetOrthogonalSum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (T A B : HSp D) (d : OrthDec T A B) (S : HSp D), GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.TensorTarget ψ d S := by
  first | exact @GlobalTheory.TensorTargetRule.tensorTarget | exact GlobalTheory.TensorTargetRule.tensorTarget | (intros; apply GlobalTheory.TensorTargetRule.tensorTarget <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierBesselThetaCharIntegrandLaws
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierBesselThetaCharIntegrandLaws
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

noncomputable section

namespace GlobalTheory.Unf.FB.ThLaws

variable {D : D7}

theorem heisO_zero_apply (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (p : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T p f 0 = f p := by
  rw [heisO, GlobalTheory.MixModel.symplOH_zero_left, AddChar.map_zero_eq_one, one_mul, zero_add]

theorem jacS_zero_apply (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (x : Mx D T.rank ρ) (n : GA D S) (f : WO S₀ T → ℂ) :
    jacS ψ d T x n f 0 = ψ (cenS d T x n) * f (ptS d T x n) := by
  rw [jacS, Pi.smul_apply, smul_eq_mul, heisO_zero_apply]

theorem jacS_nC (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (x : Mx D T.rank ρ) (c : skewA D ρ) (f : WO S₀ T → ℂ) : jacS ψ d T x (d.nC c) f = ψ (d.qS T c x) • f := by
  have h := ptS_nB_mul_nC d T x 0 c
  rw [d.nB_zero, one_mul, Matrix.mul_zero] at h
  rw [jacS, h, cenS_nC, heisO_zero]

theorem continuous_psiE {ψ : AddChar (AF D.host.F) ℂ} (hψ : Continuous ψ) : Continuous (psiE ψ) := by
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) := IsModuleTopology.continuous_of_linearMap _
  exact hψ.comp ht

theorem continuous_upSum {X : Type} [TopologicalSpace X] {ρ : ℕ} {T : X → Mx D ρ ρ} (hT : Continuous T) :
    Continuous fun t => upSum (T t) := by
  unfold upSum
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  by_cases h : j.1 = i.1 + 1
  · simp only [h, if_true]; exact (continuous_apply j).comp ((continuous_apply i).comp hT)
  · simp only [h, if_false]; exact continuous_const

theorem continuous_psiFlag {ψ : AddChar (AF D.host.F) ℂ} (hψ : Continuous ψ) {S S₀ : HSp D} {ρ : ℕ}
    (d : HypDec S S₀ ρ) : Continuous (psiFlag ψ d) := by
  unfold psiFlag blockX
  exact (continuous_psiE hψ).comp
    (continuous_upSum (continuous_const.matrix_mul ((GlobalTheory.MixModel.continuous_mt S).matrix_mul continuous_const)))

theorem continuous_ptS {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D) (x : Mx D T.rank ρ) :
    Continuous (ptS d T x) := by
  unfold ptS
  exact (continuous_const.matrix_mul (GlobalTheory.MixModel.continuous_mt S)).matrix_mul continuous_const

theorem continuous_cenS {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D) (x : Mx D T.rank ρ) :
    Continuous (cenS d T x) := by
  unfold cenS
  exact GlobalTheory.OrientedHeis.continuous_symplOH continuous_const
    (continuous_const.matrix_mul (GlobalTheory.MixModel.continuous_mt S))

theorem exists_bound_quasi {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {S L : HSp D}
    {y : WO S L → ℂ} (hy : Quasi ψ S L y) : ∃ M : ℝ, ∀ w, ‖y w‖ ≤ M := by
  obtain ⟨-, -, -, -, -, K, hK, hKc⟩ := GlobalTheory.MixModel.lattice_Mx D L.rank S.rank
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hy.2.continuousOn
  refine ⟨C, fun w => ?_⟩
  obtain ⟨γ, ⟨γ0, rfl⟩, hγ⟩ := hKc w
  have h2 : ‖y w‖ = ‖y (ratW L S γ0 + w)‖ := by rw [hy.1 γ0 w, norm_mul, hψ.2.1, one_mul]
  rw [h2]
  exact hC _ hγ

theorem zl_rat {σ : ℕ} (B : BesLev D σ) :
    ∃ z0 : Matrix (Fin B.L.rank) (Fin (σ + 1)) D.host.E, zl B = rat z0 := by
  refine ⟨Matrix.vecMulVec B.ζ (fun i : Fin (σ + 1) => if i.1 + 1 = σ + 1 then (1 : D.host.E) else 0), ?_⟩
  funext i j
  simp only [zl, zEll, rat, Matrix.map_apply, Matrix.vecMulVec_apply, ell, map_mul, ratV]
  congr 1
  split_ifs <;> simp

theorem ptS_rat {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D) (x0 : Matrix (Fin T.rank) (Fin ρ) D.host.E)
    {γ : GA D S} (hγ : γ ∈ GQ S) : ∃ g0, ptS d T (rat x0) γ = ratW T S₀ g0 := by
  obtain ⟨g, hg⟩ := (GlobalTheory.MixModel.mem_GQ_iff S γ).1 hγ
  refine ⟨x0 * d.qX * g * d.i₀, ?_⟩
  rw [ratW_eq, ptS, HypDec.extX_apply, ← hg]
  simp only [rat_mul]
  rfl

theorem psi_cenS_rat {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {S S₀ : HSp D} {ρ : ℕ}
    (d : HypDec S S₀ ρ) (T : HSp D) (x0 : Matrix (Fin T.rank) (Fin ρ) D.host.E) {γ : GA D S} (hγ : γ ∈ GQ S) :
    ψ (cenS d T (rat x0) γ) = 1 := by
  obtain ⟨g, hg⟩ := (GlobalTheory.MixModel.mem_GQ_iff S γ).1 hγ
  have e : cenS d T (rat x0) γ = symplOH S T ((x0 * d.qX).map (incA D)) ((x0 * d.qX * g).map (incA D)) := by
    rw [cenS, HypDec.extX_apply, ← hg]
    change _ = symplOH S T (rat (x0 * d.qX)) (rat (x0 * d.qX * g))
    simp only [rat_mul]
    rfl
  rw [e]
  exact GlobalTheory.AnisoMean.psi_rat hψ S T _ _

theorem upSum_rat {ρ : ℕ} (M : Matrix (Fin ρ) (Fin ρ) D.host.E) :
    upSum (rat M : Mx D ρ ρ) = incA D (∑ i, ∑ j, if j.1 = i.1 + 1 then M i j else 0) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [upSum, map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp [rat]

theorem psiE_incA {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (t : D.host.E) : psiE ψ (incA D t) = 1 := by
  rw [psiE, show Algebra.trace (AF D.host.F) (AE D) (incA D t) =
    algebraMap D.host.F (AF D.host.F) (Algebra.trace D.host.F D.host.E t) from GlobalTheory.AnisoMean.trace_one_tmul (AF D.host.F) t]
  exact hψ.2.2.1 _

theorem psiFlag_rat {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {S S₀ : HSp D} {ρ : ℕ}
    (d : HypDec S S₀ ρ) {γ : GA D S} (hγ : γ ∈ GQ S) : psiFlag ψ d γ = 1 := by
  obtain ⟨g, hg⟩ := (GlobalTheory.MixModel.mem_GQ_iff S γ).1 hγ
  have e : blockX d γ = rat (d.qX * (g * d.e)) := by
    rw [blockX, ← hg]
    simp only [rat_mul]
    rfl
  rw [psiFlag, e, upSum_rat, psiE_incA hψ]

theorem psiFlag_nC (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (c : skewA D ρ) :
    psiFlag ψ d (d.nC c) = 1 := by
  rw [psiFlag, blockX_of_fix d (d.nC_jX c), upSum_one, psiE_zero]

theorem psiFlag_nB (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (b : Mx D ρ S₀.rank) :
    psiFlag ψ d (d.nB b) = 1 := by
  rw [psiFlag, blockX_of_fix d (d.nB_jX b), upSum_one, psiE_zero]

theorem psiFlag_levi (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (u : GL (Fin ρ) (AE D)) :
    psiFlag ψ d (d.levi u) = psiUni ψ u := by
  rw [psiFlag_eq, psiBes_levi]

theorem th_laws : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (y : WO J.W₀ B.L → ℂ), Quasi ψ J.W₀ B.L y → Continuous (th J ψ B y) ∧ (∃ M : ℝ, (∀ w, ‖y w‖ ≤ M) ∧ ∀ n, ‖th J ψ B y n‖ ≤ M) ∧ (∀ γ ∈ flagN J.d, γ ∈ GQ J.W → ∀ n ∈ flagN J.d, th J ψ B y (γ * n) = th J ψ B y n) ∧ (∀ c, ∀ n ∈ flagN J.d, th J ψ B y (J.d.nC c * n) = star (ψ (J.d.qS B.L c (zl B))) * th J ψ B y n) ∧ (∀ n ∈ flagN J.d, ∀ u ∈ UX D (σ + 1), th J ψ B y (n * J.d.levi u) = th J ψ B y n * star (psiUni ψ u)) ∧ ∀ b, ∀ u ∈ UX D (σ + 1), th J ψ B y (J.d.nB b * J.d.levi u) = star (psiUni ψ u) * star (y (zl B ⬝ b)) := by
  intro D ψ hψs σ J B y hy
  have hψ : IsCharAF D.host.F ψ := hψs.1
  have hx : ∀ u ∈ UX D (σ + 1), zl B ⬝ u.1 = zl B := fun u hu => zEll_mul B.L B.ζ hu
  obtain ⟨hcen, hmul, hlevi, -⟩ := GlobalTheory.JacHom.jacS_hom D ψ J.W J.W₀ B.L (σ + 1) J.d (zl B) hx
  obtain ⟨M, hM⟩ := exists_bound_quasi hψ hy
  have hval : ∀ n, th J ψ B y n =
      star (ψ (cenS J.d B.L (zl B) n) * y (ptS J.d B.L (zl B) n)) * star (psiFlag ψ J.d n) := fun n => by
    rw [th, jacS_zero_apply]
  have hnorm : ∀ a, ‖ψ a‖ = 1 := hψ.2.1
  have hflag1 : ∀ n, ‖psiFlag ψ J.d n‖ = 1 := fun n => hnorm _
  refine ⟨?_, ⟨M, hM, fun n => ?_⟩, ?_, ?_, ?_, ?_⟩
  · have e : th J ψ B y = fun n =>
        star (ψ (cenS J.d B.L (zl B) n) * y (ptS J.d B.L (zl B) n)) * star (psiFlag ψ J.d n) := funext hval
    rw [e]
    exact (((hψ.1.comp (continuous_cenS _ _ _)).mul (hy.2.comp (continuous_ptS _ _ _))).star).mul
      (continuous_psiFlag hψ.1 _).star
  · rw [hval, norm_mul, norm_star, norm_star, norm_mul, hnorm, hflag1, one_mul, mul_one]
    exact hM _
  · intro γ hγN hγQ n hn
    obtain ⟨z0, hz0⟩ := zl_rat B
    have hp := hmul γ hγN n hn
    obtain ⟨g0, hg0⟩ := ptS_rat J.d B.L z0 hγQ
    rw [← hz0] at hg0
    have hc : ψ (cenS J.d B.L (zl B) γ) = 1 := by rw [hz0]; exact psi_cenS_rat hψ J.d B.L z0 hγQ
    rw [hval, hval, hp.1, hp.2.1, psiFlag_mul J.d ψ hγN hn, psiFlag_rat hψ J.d hγQ, one_mul, hg0, hy.1 g0]
    congr 2
    rw [← mul_assoc, ← AddChar.map_add_eq_mul, add_neg_cancel_right, AddChar.map_add_eq_mul, hc, one_mul]
  · intro c n hn
    have hc : J.d.nC c ∈ flagN J.d := J.d.nC_mem_NFlag c
    rw [th, (hmul _ hc n hn).2.2, th, psiFlag_mul J.d ψ hc hn, psiFlag_nC, jacS_nC]
    simp only [Pi.smul_apply, smul_eq_mul, star_mul', one_mul, star_one]
    ring
  · intro n hn u hu
    have hl : J.d.levi u ∈ flagN J.d := J.d.levi_mem_NFlag hu
    rw [th, hlevi n hn u hu, psiFlag_mul J.d ψ hn hl, psiFlag_levi, th, star_mul', mul_assoc]
  · intro b u hu
    have hb : J.d.nB b ∈ flagN J.d := J.d.nB_mem_NFlag b
    have hl : J.d.levi u ∈ flagN J.d := J.d.levi_mem_NFlag hu
    have hp : ptS J.d B.L (zl B) (J.d.nB b) = zl B ⬝ b := by
      have := ptS_nB_mul_nC J.d B.L (zl B) b 0
      rwa [J.d.nC_zero, mul_one] at this
    have hc : cenS J.d B.L (zl B) (J.d.nB b) = 0 := by
      have := hcen b 0
      rw [J.d.nC_zero, mul_one] at this
      rw [this, HypDec.qS]
      simp [GlobalTheory.MixModel.symplOH_zero_right]
    rw [th, hlevi _ hb u hu, psiFlag_mul J.d ψ hb hl, jacS_zero_apply, hp, hc, AddChar.map_zero_eq_one, one_mul,
      psiFlag_nB, one_mul, psiFlag_levi]
    ring

end GlobalTheory.Unf.FB.ThLaws

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierBesselThetaCharIntegrandLawsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierBesselThetaCharIntegrand_laws : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (y : WO J.W₀ B.L → ℂ), Quasi ψ J.W₀ B.L y → Continuous (th J ψ B y) ∧ (∃ M : ℝ, (∀ w, ‖y w‖ ≤ M) ∧ ∀ n, ‖th J ψ B y n‖ ≤ M) ∧ (∀ γ ∈ flagN J.d, γ ∈ GQ J.W → ∀ n ∈ flagN J.d, th J ψ B y (γ * n) = th J ψ B y n) ∧ (∀ c, ∀ n ∈ flagN J.d, th J ψ B y (J.d.nC c * n) = star (ψ (J.d.qS B.L c (zl B))) * th J ψ B y n) ∧ (∀ n ∈ flagN J.d, ∀ u ∈ UX D (σ + 1), th J ψ B y (n * J.d.levi u) = th J ψ B y n * star (psiUni ψ u)) ∧ ∀ b, ∀ u ∈ UX D (σ + 1), th J ψ B y (J.d.nB b * J.d.levi u) = star (psiUni ψ u) * star (y (zl B ⬝ b)) := by
  first | exact @GlobalTheory.Unf.FB.ThLaws.th_laws | exact GlobalTheory.Unf.FB.ThLaws.th_laws | (intros; apply GlobalTheory.Unf.FB.ThLaws.th_laws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPolynomialFockThetaVectorWeilOperatorCartan
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPolynomialFockThetaVectorWeilOperatorCartan
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FockMove

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem theta_annih (hθ : IsInfFam θ) (hψ : IsStdChar D ψ (-1)) (τ : D.what₂.Tau)
    (J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    IsThetaFunO ψ S T (annih (heisO ψ S T) θ τ J z f) :=
  GlobalTheory.OrientedHeis.theta_add (GlobalTheory.OrientedHeis.theta_dRho hθ hψ τ z hf)
    (GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.OrientedHeis.theta_dRho hθ hψ τ _ hf))

theorem om_annih (hW : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ) (g : GA D S) (h : GA D T) (τ : D.what₂.Tau)
    {sS sS' : Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT sT' : Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (hS : sS' * compAt θ τ (mt S g) = compAt θ τ (mt S g) * sS)
    (hT : sT' * compAt θ τ (mt T h) = compAt θ τ (mt T h) * sT) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    om (g, h) (annih (heisO ψ S T) θ τ (cplxO sS sT) z f) =
      annih (heisO ψ S T) θ τ (cplxO sS' sT') (compAt θ τ (mt T h) * z * compAt θ τ (mt S g⁻¹)) (om (g, h) f) := by
  unfold annih
  rw [map_add (f := _), map_smul, GlobalTheory.WeilVacMove.om_dRho hW hθ g h τ _ hf, GlobalTheory.WeilVacMove.om_dRho hW hθ g h τ _ hf,
    GlobalTheory.WeilVacMove.cplxO_move θ τ g h hS hT]

theorem om_foldr (hW : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ) (g : GA D S) (h : GA D T)
    {sS sS' : RealMat S} {sT sT' : RealMat T}
    (hS : ∀ τ, sS' τ * compAt θ τ (mt S g) = compAt θ τ (mt S g) * sS τ)
    (hT : ∀ τ, sT' τ * compAt θ τ (mt T h) = compAt θ τ (mt T h) * sT τ) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin S.rank) ℂ)) :
    IsThetaFunO ψ S T (l.foldr (fun p F => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 F) f) ∧
      om (g, h) (l.foldr (fun p F => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 F) f) =
        (l.map fun p => (p.1, compAt θ p.1 (mt T h) * p.2 * compAt θ p.1 (mt S g⁻¹))).foldr
          (fun p F => annih (heisO ψ S T) θ p.1 (cplxO (sS' p.1) (sT' p.1)) p.2 F) (om (g, h) f) := by
  induction l with
  | nil => exact ⟨hf, rfl⟩
  | cons p l ih =>
    rw [List.map_cons, List.foldr_cons, List.foldr_cons, ← ih.2]
    exact ⟨theta_annih hθ hW.std p.1 _ p.2 ih.1, om_annih hW hθ g h p.1 (hS p.1) (hT p.1) p.2 ih.1⟩

end GlobalTheory.FockMove

namespace GlobalTheory.FockMove

theorem isFockVec_om : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → ∀ (sS sS' : RealMat S) (sT : RealMat T) (g : GA D S), (∀ τ, sS' τ * compAt θ τ (mt S g) = compAt θ τ (mt S g) * sS τ) → ∀ f, IsFockVec ψ θ S T sS sT f → IsFockVec ψ θ S T sS' sT (om (g, 1) f) := by
  intro D ψ S T χS χT om hW θ hθ sS sS' sT g hS f hf
  obtain ⟨hth, N, hN⟩ := hf
  have hT : ∀ τ, sT τ * compAt θ τ (mt T 1) = compAt θ τ (mt T 1) * sT τ := by
    intro τ
    rw [GlobalTheory.WeilVacMove.mt_one, GlobalTheory.WeilVacMove.compAt_one, Matrix.mul_one, Matrix.one_mul]
  refine ⟨hW.om_pres _ _ hth, N, fun l hl => ?_⟩
  let l₀ : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin S.rank) ℂ) :=
    l.map fun p => (p.1, compAt θ p.1 (mt T (1 : GA D T)⁻¹) * p.2 * compAt θ p.1 (mt S g))
  have e : (l₀.map fun p => (p.1, compAt θ p.1 (mt T (1 : GA D T)) * p.2 * compAt θ p.1 (mt S g⁻¹))) = l := by
    simp only [l₀, List.map_map]
    conv_rhs => rw [← List.map_id l]
    refine List.map_congr_left fun p _ => ?_
    simp only [Function.comp_apply, id]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, GlobalTheory.WeilVacMove.compAt_mt_mul_inv, Matrix.one_mul, Matrix.mul_assoc,
      GlobalTheory.WeilVacMove.compAt_mt_mul_inv, Matrix.mul_one]
  have key := (om_foldr hW hθ g 1 hS hT hth l₀).2
  rw [e] at key
  rw [← key, hN l₀ (by simp [l₀, hl]), map_zero]

end GlobalTheory.FockMove

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPolynomialFockThetaVectorWeilOperatorCartanStatement
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPolynomialFockThetaVector_weilOperator_cartan : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → ∀ (sS sS' : RealMat S) (sT : RealMat T) (g : GA D S), (∀ τ, sS' τ * compAt θ τ (mt S g) = compAt θ τ (mt S g) * sS τ) → ∀ f, IsFockVec ψ θ S T sS sT f → IsFockVec ψ θ S T sS' sT (om (g, 1) f) := by
  first | exact @GlobalTheory.FockMove.isFockVec_om | exact GlobalTheory.FockMove.isFockVec_om | (intros; apply GlobalTheory.FockMove.isFockVec_om <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodLinearAndTranslationCombination
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodLinearAndTranslationCombination
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.TrcProof

variable {D : D7}

theorem contAut_add {V : HSp D} {f g : GA D V → ℂ} (hf : IsContAut V f) (hg : IsContAut V g) :
    IsContAut V (f + g) :=
  ⟨fun γ hγ x => by simp only [Pi.add_apply, hf.1 γ hγ x, hg.1 γ hγ x], hf.2.add hg.2⟩

theorem contAut_smul {V : HSp D} {f : GA D V → ℂ} (hf : IsContAut V f) (c : ℂ) : IsContAut V (c • f) :=
  ⟨fun γ hγ x => by simp only [Pi.smul_apply, hf.1 γ hγ x], hf.2.const_smul c⟩

theorem contAut_rTrans {V : HSp D} {f : GA D V → ℂ} (h : GA D V) (hf : IsContAut V f) : IsContAut V (rTrans h f) :=
  ⟨fun γ hγ x => by simp only [rTrans, mul_assoc, hf.1 γ hγ], hf.2.comp (continuous_mul_const h)⟩

theorem contAut_sum {V : HSp D} {I : Type} (s : Finset I) (a : I → ℂ) (f : I → GA D V → ℂ)
    (hf : ∀ i ∈ s, IsContAut V (f i)) : IsContAut V (∑ i ∈ s, a i • f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ _ _ => by simp, continuous_const⟩
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact contAut_add (contAut_smul (hf i (Finset.mem_insert_self i s)) (a i))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem per_sum_right {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {ρ : ℕ} (B : BesLev D ρ)
    {φ : GA D B.A → ℂ} (hφ : IsContAut B.A φ) {I : Type} (s : Finset I) (a : I → ℂ) (f : I → GA D B.V → ℂ)
    (hf : ∀ i ∈ s, IsContAut B.V (f i)) :
    B.per ψ φ (∑ i ∈ s, a i • f i) = ∑ i ∈ s, a i * B.per ψ φ (f i) := by
  have hconv := fun i (hi : i ∈ s) => PerSumProof.conv hψ B (hf i hi) hφ
  simp only [BesLev.per, besPer]
  have e1 : ∀ h n, besFun ψ 1 B.d B.o B.ζ φ (∑ i ∈ s, a i • f i) h n =
      ∑ i ∈ s, a i * besFun ψ 1 B.d B.o B.ζ φ (f i) h n := by
    intro h n
    simp only [besFun, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [e1]
  have e2 : (fun h => ∫ n in B.vN.𝓝, ∑ i ∈ s, a i * besFun ψ 1 B.d B.o B.ζ φ (f i) h n ∂B.vN.ν) =
      fun h => ∑ i ∈ s, a i * ∫ n in B.vN.𝓝, besFun ψ 1 B.d B.o B.ζ φ (f i) h n ∂B.vN.ν := by
    funext h
    rw [integral_finsetSum s fun i hi => ((hconv i hi).1 h).const_mul (a i)]
    exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  rw [e2, integral_finsetSum s fun i hi => (hconv i hi).2.const_mul (a i)]
  exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _

end GlobalTheory.SeeSaw.TrcProof

namespace GlobalTheory.SeeSaw

theorem per_linear_trc : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ρ : ℕ) (B : BesLev D ρ) (φ : GA D B.A → ℂ), IsContAut B.A φ → (∀ (I : Type) (s : Finset I) (a : I → ℂ) (f : I → GA D B.V → ℂ), (∀ i ∈ s, IsContAut B.V (f i)) → B.per ψ φ (∑ i ∈ s, a i • f i) = ∑ i ∈ s, a i * B.per ψ φ (f i)) ∧ ∀ (e : GA D B.V →₀ ℂ) (f : GA D B.V → ℂ), IsContAut B.V f → IsContAut B.V (trc e f) ∧ B.per ψ φ (trc e f) = ∑ g ∈ e.support, e g * B.per ψ φ (rTrans g f) := by
  intro D ψ hψ ρ B φ hφ
  refine ⟨fun I s a f hf => TrcProof.per_sum_right hψ B hφ s a f hf, fun e f hf => ?_⟩
  have hT : ∀ g ∈ e.support, IsContAut B.V (rTrans g f) := fun g _ => TrcProof.contAut_rTrans g hf
  exact ⟨TrcProof.contAut_sum e.support e (fun g => rTrans g f) hT,
    TrcProof.per_sum_right hψ B hφ e.support e (fun g => rTrans g f) hT⟩

end GlobalTheory.SeeSaw

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodLinearAndTranslationCombinationStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselPeriod_linear_and_translationCombination : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ρ : ℕ) (B : BesLev D ρ) (φ : GA D B.A → ℂ), IsContAut B.A φ → (∀ (I : Type) (s : Finset I) (a : I → ℂ) (f : I → GA D B.V → ℂ), (∀ i ∈ s, IsContAut B.V (f i)) → B.per ψ φ (∑ i ∈ s, a i • f i) = ∑ i ∈ s, a i * B.per ψ φ (f i)) ∧ ∀ (e : GA D B.V →₀ ℂ) (f : GA D B.V → ℂ), IsContAut B.V f → IsContAut B.V (trc e f) ∧ B.per ψ φ (trc e f) = ∑ g ∈ e.support, e g * B.per ψ φ (rTrans g f) := by
  first | exact @GlobalTheory.SeeSaw.per_linear_trc | exact GlobalTheory.SeeSaw.per_linear_trc | (intros; apply GlobalTheory.SeeSaw.per_linear_trc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsClopenCompactNbhdZero
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AfTensNbhd

variable (F : Type) [Field F] [NumberField F]

def intAf : Set (FiniteAdeleRing (𝓞 F) F) :=
  {a | ∀ v, a v ∈ HeightOneSpectrum.adicCompletionIntegers F v}

theorem isOpen_intAf : IsOpen (intAf F) := by
  unfold intAf
  exact RestrictedProduct.isOpen_forall_mem (fun v => by
    exact Valued.isOpen_integer _)

theorem isCompact_intAf : IsCompact (intAf F) :=
  (GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties F).1

theorem isClosed_intAf : IsClosed (intAf F) := by
  haveI := GlobalTheory.IntegralFinAdele.t2Space_finiteAdeleRing' F
  exact (isCompact_intAf F).isClosed

theorem zero_mem_intAf : (0 : FiniteAdeleRing (𝓞 F) F) ∈ intAf F := fun v => by
  exact zero_mem _

end GlobalTheory.AfTensNbhd

namespace GlobalTheory.AfTensNbhd

section Tens

variable (F : Type) [Field F] [NumberField F] (E : Type) [Field E] [Algebra F E] [FiniteDimensional F E]

noncomputable def coordEquiv : ((Af F) ⊗[F] E) ≃ₗ[(Af F)] (Module.Free.ChooseBasisIndex F E → (Af F)) :=
  (Algebra.TensorProduct.basis (Af F) (Module.Free.chooseBasis F E)).equivFun

local instance : IsModuleTopology (Af F) ((Af F) ⊗[F] E) := ⟨rfl⟩

theorem continuous_coordEquiv : Continuous (coordEquiv F E) :=
  IsModuleTopology.continuous_of_linearMap (coordEquiv F E).toLinearMap

theorem continuous_coordEquiv_symm : Continuous (coordEquiv F E).symm := by
  haveI : ContinuousAdd ((Af F) ⊗[F] E) := IsModuleTopology.toContinuousAdd (Af F) _
  haveI : ContinuousSMul (Af F) ((Af F) ⊗[F] E) := IsModuleTopology.toContinuousSMul (Af F) _
  exact IsModuleTopology.continuous_of_linearMap (coordEquiv F E).symm.toLinearMap

noncomputable def intTens : Set ((Af F) ⊗[F] E) := coordEquiv F E ⁻¹' Set.univ.pi (fun _ => intAf F)

theorem isClopen_intTens : IsClopen (intTens F E) :=
  ⟨(isClosed_set_pi fun _ _ => isClosed_intAf F).preimage (continuous_coordEquiv F E),
   (isOpen_set_pi Set.finite_univ fun _ _ => isOpen_intAf F).preimage (continuous_coordEquiv F E)⟩

theorem isCompact_intTens : IsCompact (intTens F E) := by
  have h := (isCompact_univ_pi fun _ => isCompact_intAf F).image (continuous_coordEquiv_symm F E)
  convert h using 1
  ext x
  constructor
  · intro hx
    exact ⟨coordEquiv F E x, hx, (coordEquiv F E).symm_apply_apply x⟩
  · rintro ⟨y, hy, rfl⟩
    change coordEquiv F E ((coordEquiv F E).symm y) ∈ Set.univ.pi (fun _ => intAf F)
    rw [LinearEquiv.apply_symm_apply]
    exact hy

theorem zero_mem_intTens : (0 : (Af F) ⊗[F] E) ∈ intTens F E := by
  intro i _
  rw [map_zero]
  exact zero_mem_intAf F

end Tens

end GlobalTheory.AfTensNbhd

namespace GlobalTheory.AfTensNbhd

theorem exists_clopen_compact_nbhd_zero : ∀ (D : D7) (m n : ℕ), ∃ U : Set (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E), IsClopen U ∧ IsCompact U ∧ (0 : Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) ∈ U := by
  intro D m n
  refine ⟨Set.univ.pi (fun _ => Set.univ.pi (fun _ => intTens D.host.F D.host.E)), ⟨?_, ?_⟩, ?_, ?_⟩
  · exact isClosed_set_pi fun _ _ => isClosed_set_pi fun _ _ => (isClopen_intTens D.host.F D.host.E).1
  · exact isOpen_set_pi Set.finite_univ fun _ _ =>
      isOpen_set_pi Set.finite_univ fun _ _ => (isClopen_intTens D.host.F D.host.E).2
  · exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_intTens D.host.F D.host.E
  · intro i _ j _
    exact zero_mem_intTens D.host.F D.host.E

end GlobalTheory.AfTensNbhd
end
