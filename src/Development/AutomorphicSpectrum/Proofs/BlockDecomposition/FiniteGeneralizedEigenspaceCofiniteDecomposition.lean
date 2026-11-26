module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.CuspInvariantsFinite.CuspInvFin
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermAutomorphicCriterion
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantPairingMirabolicVanishing
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ExistsEigv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClsLocEqOfIsLocComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvUAbsU
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuliLawsCoefficientFieldChange
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBoundFiniteInfinite
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeTwistedIso

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteGeneralizedEigenspaceCofiniteDecomposition
section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FiniteRankZero
noncomputable section

open NumberField GlobalTheory.CuspRep Formalism.L2.Host

namespace GlobalTheory.Published.AutFinGL.Model

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def kerL (a : ℕ) (χ : HChar E) : Subgroup (GL (Fin a) (Af E)) := ((chiDet a χ).comp (finGL E a)).ker

theorem isOpen_kerL (χ : HChar E) : IsOpen (kerL a χ : Set (GL (Fin a) (Af E))) := isOpen_ker_chiDet χ

end GlobalTheory.Published.AutFinGL.Model

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteGeneralizedEigenspaceCofiniteDecomposition
noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl Formalism.L2.Host

namespace GlobalTheory.CompanionTheory.CuspTwist

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def conjChi (a : ℕ) (χ : HChar E) : Module.End ℂ (Sm E a) ≃ₐ[ℂ] Module.End ℂ (Sm E a) :=
  LinearEquiv.conjAlgEquiv ℂ (mulChi a χ)

theorem conjChi_apply (χ : HChar E) (z : Module.End ℂ (Sm E a)) (φ : Sm E a) :
    conjChi a χ z (mulChi a χ φ) = mulChi a χ (z φ) := by
  simp [conjChi, LinearEquiv.conjAlgEquiv_apply]

theorem conjChi_cap (χ : HChar E) (τ : E →+* ℂ) (u : ℂ) :
    conjChi a χ (cap τ (u + expo χ τ)) = cap τ u := by
  refine LinearMap.ext fun ψ => ?_
  obtain ⟨φ, rfl⟩ := (mulChi a χ).surjective ψ
  rw [conjChi_apply, cap_mulChi]

theorem map_Zalg (χ : HChar E) : (Zalg E a).map (conjChi a χ : _ →ₐ[ℂ] _) = Zalg E a := by
  rw [Zalg, AlgHom.map_adjoin]
  congr 1
  ext z
  constructor
  · rintro ⟨_, ⟨τ, u, rfl⟩, rfl⟩
    exact ⟨τ, u - expo χ τ, by
      have := conjChi_cap (a := a) χ τ (u - expo χ τ)
      rw [sub_add_cancel] at this
      exact this⟩
  · rintro ⟨τ, u, rfl⟩
    exact ⟨_, ⟨τ, u + expo χ τ, rfl⟩, conjChi_cap χ τ u⟩

theorem cofin_conj (χ : HChar E) {J : Set (Module.End ℂ (Sm E a))} (hJ : Cofin J) :
    Cofin (conjChi a χ '' J) := by
  obtain ⟨hsub, V, hV, hz⟩ := hJ
  have hm : ∀ z ∈ Zalg E a, conjChi a χ z ∈ Zalg E a := fun z h => by
    rw [← map_Zalg (a := a) χ]
    exact ⟨z, h, rfl⟩
  refine ⟨?_, V.map (conjChi a χ).toLinearMap, inferInstance, fun z h => ?_⟩
  · rintro _ ⟨j, hj, rfl⟩
    exact hm _ (hsub hj)
  · rw [← map_Zalg (a := a) χ] at h
    obtain ⟨w, hw, rfl⟩ := h
    have h1 := Submodule.mem_map_of_mem (f := (conjChi a χ).toLinearMap) (hz w hw)
    rw [Submodule.map_sup, Submodule.map_span] at h1
    obtain ⟨y, hy, y', hy', e⟩ := Submodule.mem_sup.1 h1
    refine Submodule.mem_sup.2 ⟨y, hy, y', Submodule.span_mono ?_ hy', e⟩
    rintro _ ⟨_, ⟨x, hx, j, hj, rfl⟩, rfl⟩
    exact ⟨conjChi a χ x, hm _ hx, conjChi a χ j, ⟨j, hj, rfl⟩, map_mul (conjChi a χ) x j⟩

theorem chiDet_absC_cpt (s : ℂ) (k : Kinf E a) :
    chiDet a (Model.absC E s) (infGL E a (Unitary.toUnits k)) = 1 := by
  have h1 : chiDet a (Model.absC E s) (infGL E a (Unitary.toUnits k)) =
      (Model.absC E s).1 (infId E (Matrix.GeneralLinearGroup.det (Unitary.toUnits k))) :=
    congrArg (Model.absC E s).1 (det_infGL _)
  rw [h1]
  refine Units.ext ?_
  change Complex.exp (s * GlobalTheory.Mem.Chr.CharModel.logNorm E (infId E _)) = 1
  rw [Model.logNorm_infId]
  have hd : star (k.1.det) * k.1.det = 1 := (Matrix.det_of_mem_unitary k.2).1
  have hn : ∀ w, ‖(k.1.det : Cinf E) w‖ = 1 := fun w => by
    have := congrFun hd w
    have h2 : ‖(k.1.det : Cinf E) w‖ * ‖(k.1.det : Cinf E) w‖ = 1 := by
      have h3 := congrArg norm this
      simpa using h3
    nlinarith [norm_nonneg ((k.1.det : Cinf E) w)]
  have e : ∀ w, ‖((Matrix.GeneralLinearGroup.det (Unitary.toUnits k) : (Cinf E)ˣ) : Cinf E) w‖ = 1 := hn
  simp [hn]

theorem dchi_absC_trace (s : ℂ) :
    dchi (Model.absC E s) (Matrix.of (oneL E a)).trace = s * (a * (2 * Fintype.card (InfinitePlace E))) := by
  have e : (Matrix.of (oneL E a)).trace = a • (1 : Cinf E) := by
    change Matrix.trace (1 : Matrix (Fin a) (Fin a) (Cinf E)) = _
    simp
  rw [e, map_nsmul, GlobalTheory.GKCoh.Tests.dchi_absC_one]
  simp
  ring

theorem twist_central : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 0 < a →
    ∀ (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) →
    ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (Kinf E a) W),
    GlobalTheory.Published.AutFin.IsContRep ρ → ∀ J : Set (Module.End ℂ (Sm E a)), Cofin J → ∀ c : ℂ,
    ∃ (χ : Formalism.L2.Host.HChar E) (L' : Subgroup (GL (Fin a) (Af E))) (J' : Set (Module.End ℂ (Sm E a))),
      IsOpen (L' : Set (GL (Fin a) (Af E))) ∧ Cofin J' ∧ ∀ φ : Sm E a, φ ∈ genSpace L ρ J → IsCuspidal φ.1 →
        lie E a (oneL E a) φ = c • φ →
        mulChi a χ φ ∈ genSpace L' ρ J' ∧ IsCuspidal (mulChi a χ φ).1 ∧ lie E a (oneL E a) (mulChi a χ φ) = 0 := by
  intro E _ _ _ a ha L hL W _ _ _ ρ _ J hJ c
  have hn : (Fintype.card (InfinitePlace E) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  set s : ℂ := -c / (a * (2 * Fintype.card (InfinitePlace E))) with hs
  have hd : dchi (Model.absC E s) (Matrix.of (oneL E a)).trace = -c := by
    rw [dchi_absC_trace, hs]
    field_simp
  refine ⟨Model.absC E s, L ⊓ GlobalTheory.Published.AutFinGL.Model.kerL a (Model.absC E s), conjChi a (Model.absC E s) '' J,
    ?_, cofin_conj _ hJ, fun φ hφ hc he => ⟨⟨(IsCuspForm.mulChi (⟨hφ.1, hc⟩ : IsCuspForm φ) _).1, fun k hk => ?_, fun g => ?_, ?_⟩, ?_, ?_⟩⟩
  · exact hL.inter (GlobalTheory.Published.AutFinGL.Model.isOpen_kerL _)
  · have h2 : chiDet a (Model.absC E s) (finGL E a k) = 1 := hk.2
    change rt E a (finGL E a k) _ = _
    rw [rt_mulChi, h2, Units.val_one, one_smul]
    exact congrArg (mulChi a (Model.absC E s)) (hφ.2.1 k hk.1)
  · have h3 := hφ.2.2.1 g
    have e : (fun k : Kinf E a => (cptRep E a k (mulChi a (Model.absC E s) φ)).1 g) =
        ((chiDet a (Model.absC E s) g : ℂˣ) : ℂ) • fun k : Kinf E a => (cptRep E a k φ).1 g := by
      funext k
      change (mulChi a (Model.absC E s) φ).1 (g * infGL E a (Unitary.toUnits k)) =
        ((chiDet a (Model.absC E s) g : ℂˣ) : ℂ) * φ.1 (g * infGL E a (Unitary.toUnits k))
      rw [mulChi_apply, map_mul, chiDet_absC_cpt, mul_one, mul_comm]
    rw [e]
    exact Submodule.smul_mem _ _ h3
  · rintro _ ⟨j, hj, rfl⟩
    rw [conjChi_apply, hφ.2.2.2 j hj, map_zero]
  · exact (IsCuspForm.mulChi (⟨hφ.1, hc⟩ : IsCuspForm φ) _).2
  · rw [lie_mulChi, he, hd, neg_smul, add_neg_cancel, map_zero]

end GlobalTheory.CompanionTheory.CuspTwist

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteGeneralizedEigenspaceCofiniteDecompositionStatement
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_char_twist_cuspidal_lie_eigenvalue_zero : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 0 < a → ∀ (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (Kinf E a) W), GlobalTheory.Published.AutFin.IsContRep ρ → ∀ J : Set (Module.End ℂ (Sm E a)), Cofin J → ∀ c : ℂ, ∃ (χ : Formalism.L2.Host.HChar E) (L' : Subgroup (GL (Fin a) (Af E))) (J' : Set (Module.End ℂ (Sm E a))), IsOpen (L' : Set (GL (Fin a) (Af E))) ∧ Cofin J' ∧ ∀ φ : Sm E a, φ ∈ genSpace L ρ J → IsCuspidal φ.1 → lie E a (oneL E a) φ = c • φ → mulChi a χ φ ∈ genSpace L' ρ J' ∧ IsCuspidal (mulChi a χ φ).1 ∧ lie E a (oneL E a) (mulChi a χ φ) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.CuspTwist.twist_central | exact GlobalTheory.CompanionTheory.CuspTwist.twist_central | (intros; apply GlobalTheory.CompanionTheory.CuspTwist.twist_central <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearOdeValueDeterminedByShifts
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearOdeValueDeterminedByShifts
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl

namespace GlobalTheory.CompanionTheory.LinearODE

noncomputable def companion (p : Polynomial ℂ) (n : ℕ) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
  LinearMap.pi fun i =>
    if h : (i : ℕ) + 1 < n then LinearMap.proj ⟨i + 1, h⟩
    else - ∑ k : Fin n, p.coeff k • LinearMap.proj k

theorem top_eq {p : Polynomial ℂ} (hp : p.Monic) {F : ℕ → ℝ → ℂ}
    (hrel : ∀ s : ℝ, ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * F k s = 0) (s : ℝ) :
    F p.natDegree s = - ∑ k : Fin p.natDegree, p.coeff k * F k s := by
  have h := hrel s
  rw [Finset.sum_range_succ, hp.coeff_natDegree, one_mul] at h
  have e : ∑ k : Fin p.natDegree, p.coeff k * F k s =
      ∑ k ∈ Finset.range p.natDegree, p.coeff k * F k s :=
    (Finset.sum_range (fun k => p.coeff k * F k s)).symm
  rw [e]
  linear_combination h

theorem lower_eq_zero {p : Polynomial ℂ} (hp : p.Monic) {F : ℕ → ℝ → ℂ}
    (hF : ∀ (k : ℕ) (s : ℝ), HasDerivAt (F k) (F (k + 1) s) s)
    (hrel : ∀ s : ℝ, ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * F k s = 0)
    (h0 : ∀ k < p.natDegree, F k 0 = 0) : ∀ k < p.natDegree, F k = 0 := by
  let X : ℝ → (Fin p.natDegree → ℂ) := fun s i => F i s
  have hX : ∀ s, HasDerivAt X (companion p p.natDegree (X s)) s := by
    intro s
    rw [hasDerivAt_pi]
    intro i
    have e : companion p p.natDegree (X s) i = F (i + 1) s := by
      simp only [companion, LinearMap.pi_apply]
      split_ifs with h
      · rfl
      · have hi : (i : ℕ) + 1 = p.natDegree := by
          have := i.isLt
          omega
        rw [hi, top_eq hp hrel s]
        simp [X, LinearMap.sum_apply, smul_eq_mul]
    rw [e]
    exact hF i s
  have hA : LipschitzWith ‖LinearMap.toContinuousLinearMap (companion p p.natDegree)‖₊
      (companion p p.natDegree) := by
    have := (LinearMap.toContinuousLinearMap (companion p p.natDegree)).lipschitz
    simpa using this
  have hzero : ∀ s, X s = 0 := by
    intro s
    have key := ODE_solution_unique_of_mem_Icc (v := fun _ => companion p p.natDegree)
      (s := fun _ => Set.univ) (a := -(|s| + 1)) (b := |s| + 1) (t₀ := 0)
      (fun t _ => hA.lipschitzOnWith)
      ⟨by linarith [abs_nonneg s], by linarith [abs_nonneg s]⟩
      (fun t _ => (hX t).continuousAt.continuousWithinAt) (fun t _ => hX t)
      (fun _ _ => Set.mem_univ _)
      (continuousOn_const (c := (0 : Fin p.natDegree → ℂ)))
      (fun t _ => by simpa using hasDerivAt_const t (0 : Fin p.natDegree → ℂ))
      (fun _ _ => Set.mem_univ _)
      (by funext i; simpa [X] using h0 i i.isLt)
    exact key ⟨by linarith [neg_abs_le s], by linarith [le_abs_self s]⟩
  intro k hk
  funext s
  simpa [X] using congrFun (hzero s) ⟨k, hk⟩

theorem chain_zero {F : ℕ → ℝ → ℂ} (hF : ∀ (k : ℕ) (s : ℝ), HasDerivAt (F k) (F (k + 1) s) s)
    {m : ℕ} (h : F m = 0) : ∀ k, m ≤ k → F k = 0 := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact h
  | succ k hmk ih =>
    funext s
    have h1 := hF k s
    rw [ih] at h1
    show F (k + 1) s = 0
    exact h1.unique (hasDerivAt_const s (0 : ℂ))

theorem eq_zero_of_initial {p : Polynomial ℂ} (hp : p.Monic) {F : ℕ → ℝ → ℂ}
    (hF : ∀ (k : ℕ) (s : ℝ), HasDerivAt (F k) (F (k + 1) s) s)
    (hrel : ∀ s : ℝ, ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * F k s = 0)
    (h0 : ∀ k < p.natDegree, F k 0 = 0) : ∀ k, F k = 0 := by
  have hlow := lower_eq_zero hp hF hrel h0
  have htop : F p.natDegree = 0 := by
    funext s
    rw [top_eq hp hrel s]
    have hz : ∀ k : Fin p.natDegree, p.coeff k * F k s = 0 := fun k => by
      rw [hlow k k.isLt]
      simp
    simp [hz]
  intro k
  rcases lt_or_ge k p.natDegree with hk | hk
  · exact hlow k hk
  · exact chain_zero hF htop k hk

def solSpace (p : Polynomial ℂ) : Submodule ℂ (ℕ → ℝ → ℂ) where
  carrier := {F | (∀ (k : ℕ) (s : ℝ), HasDerivAt (F k) (F (k + 1) s) s) ∧
    ∀ s : ℝ, ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * F k s = 0}
  add_mem' := by
    rintro F G ⟨hF, rF⟩ ⟨hG, rG⟩
    refine ⟨fun k s => (hF k s).add (hG k s), fun s => ?_⟩
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, rF s, rG s, add_zero]
  zero_mem' := ⟨fun k s => hasDerivAt_const s (0 : ℂ), fun s => by simp⟩
  smul_mem' := by
    rintro c F ⟨hF, rF⟩
    refine ⟨fun k s => (hF k s).const_mul c, fun s => ?_⟩
    have h : ∀ k, p.coeff k * (c • F) k s = c * (p.coeff k * F k s) := fun k => by
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    simp only [h, ← Finset.mul_sum, rF s, mul_zero]

theorem finiteDimensional_solSpace {p : Polynomial ℂ} (hp : p.Monic) :
    FiniteDimensional ℂ (solSpace p) := by
  let Φ : solSpace p →ₗ[ℂ] (Fin p.natDegree → ℂ) :=
    { toFun := fun F i => (F : ℕ → ℝ → ℂ) i 0
      map_add' := fun F G => rfl
      map_smul' := fun c F => rfl }
  refine Module.Finite.of_injective Φ ((injective_iff_map_eq_zero Φ).2 fun F hF => ?_)
  obtain ⟨hFd, hFr⟩ := F.2
  have hz := eq_zero_of_initial hp hFd hFr (fun k hk => congrFun hF ⟨k, hk⟩)
  exact Subtype.ext (funext hz)

theorem deriv_zero_eq_sum :
    ∀ p : Polynomial ℂ, p.Monic → ∃ (T : Finset ℝ) (w : ℝ → ℂ), ∀ F : ℕ → ℝ → ℂ,
      (∀ (k : ℕ) (s : ℝ), HasDerivAt (F k) (F (k + 1) s) s) →
      (∀ s : ℝ, ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * F k s = 0) →
      F 1 0 = ∑ t ∈ T, w t * F 0 t := by
  intro p hp
  haveI := finiteDimensional_solSpace hp
  let ev : ℝ → Module.Dual ℂ (solSpace p) := fun t =>
    { toFun := fun F => (F : ℕ → ℝ → ℂ) 0 t
      map_add' := fun F G => rfl
      map_smul' := fun c F => rfl }
  let φ : Module.Dual ℂ (solSpace p) :=
    { toFun := fun F => (F : ℕ → ℝ → ℂ) 1 0
      map_add' := fun F G => rfl
      map_smul' := fun c F => rfl }
  have hco : (Submodule.span ℂ (Set.range ev)).dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro F hF
    rw [Submodule.mem_dualCoannihilator] at hF
    have h0 : (F : ℕ → ℝ → ℂ) 0 = 0 :=
      funext fun t => hF (ev t) (Submodule.subset_span ⟨t, rfl⟩)
    obtain ⟨hFd, -⟩ := F.2
    have hall := chain_zero hFd h0
    rw [Submodule.mem_bot]
    exact Subtype.ext (funext fun k => hall k (Nat.zero_le k))
  have hspan : Submodule.span ℂ (Set.range ev) = ⊤ := by
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span ℂ (Set.range ev)), hco,
      Submodule.dualAnnihilator_bot]
  have hφ : φ ∈ Submodule.span ℂ (Set.range ev) := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hφ
  refine ⟨c.support, c, fun F hFd hFr => ?_⟩
  have hmem : F ∈ solSpace p := ⟨hFd, hFr⟩
  have key := LinearMap.congr_fun hc ⟨F, hmem⟩
  simp only [Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply] at key
  exact key.symm

end GlobalTheory.CompanionTheory.LinearODE
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearOdeValueDeterminedByShiftsStatement
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_ode_value_determined_by_shifts : ∀ p : Polynomial ℂ, p.Monic → ∃ (T : Finset ℝ) (w : ℝ → ℂ), ∀ F : ℕ → ℝ → ℂ, (∀ (k : ℕ) (s : ℝ), HasDerivAt (F k) (F (k + 1) s) s) → (∀ s : ℝ, ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * F k s = 0) → F 1 0 = ∑ t ∈ T, w t * F 0 t := by
  first | exact @GlobalTheory.CompanionTheory.LinearODE.deriv_zero_eq_sum | exact GlobalTheory.CompanionTheory.LinearODE.deriv_zero_eq_sum | (intros; apply GlobalTheory.CompanionTheory.LinearODE.deriv_zero_eq_sum <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetProjectionHeckeHolds
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetProjectionHeckeHolds
open GlobalTheory.PRep PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.Cass

theorem jacquet_projection_hecke_intertwines : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G],
    PositivityTheory.SphericalProduct.A2 G := by
  intro G _ _ _ D V _ _ π hπ t ht U hU v
  obtain ⟨r, hr, x, hxJN, hx⟩ := GlobalTheory.T.dominant_coset_reps_unipotent G D t ht
  have hUv := GlobalTheory.T.hecke_operator_coset_formula G D.J D.isOpen_J D.isCompact_J V π hπ (t : G) U hU r x hr
    (fun i => (hxJN i).1) hx v
  have hstep : ∀ i, (Submodule.Quotient.mk (π (x i * (t : G)) (v : V)) : GlobalTheory.PRep.Jacquet π D.N) =
      Submodule.Quotient.mk (π (t : G) (v : V)) := by
    intro i
    refine (Submodule.Quotient.eq _).mpr (Submodule.subset_span ⟨⟨x i, (hxJN i).2⟩, π (t : G) (v : V), ?_⟩)
    simp
  have hsum := map_sum (Submodule.mkQ (GlobalTheory.PRep.twKer π D.N 1))
    (fun i => π (x i * (t : G)) (v : V)) Finset.univ
  simp only [Submodule.mkQ_apply] at hsum
  show (Submodule.Quotient.mk (↑(U v)) : GlobalTheory.PRep.Jacquet π D.N) =
    (D.piN π t) (Submodule.Quotient.mk (v : V))
  rw [hUv, Submodule.Quotient.mk_smul, hsum]
  simp only [hstep]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hr.ne'), one_smul]
  rfl

end GlobalTheory.CompanionTheory.Cass
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetProjectionHeckeHoldsStatement
open GlobalTheory.PRep PositivityTheory.SphericalProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_projection_hecke_holds : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G], PositivityTheory.SphericalProduct.A2 G := by
  first | exact @GlobalTheory.CompanionTheory.Cass.jacquet_projection_hecke_intertwines | exact GlobalTheory.CompanionTheory.Cass.jacquet_projection_hecke_intertwines | (intros; apply GlobalTheory.CompanionTheory.Cass.jacquet_projection_hecke_intertwines <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteSphNe
noncomputable section

open NumberField IsDedekindDomain Matrix Filter Function
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.CompanionTheory.UnitaryWord

open PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.F.U

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

abbrev unitFn (n : ℕ) (w : Pl E) : UL n w → ℂ := (KL n w : Set (UL n w)).indicator 1

theorem isHecke_zero {w : Pl E} (K' : Subgroup (UL n w)) : IsHecke K' (0 : UL n w → ℂ) :=
  ⟨HasCompactSupport.zero, fun _ _ _ => ⟨rfl, rfl⟩⟩

theorem isHecke_lone (hL : LocAlg) {w : Pl E} {K' : Subgroup (UL n w)} (hK : IsLevel (MonoidHom.id _) (KL n w) K') :
    IsHecke K' (lone K') :=
  (hL E n w (SmIrr.triv _) K' hK 0 0 (isHecke_zero K') (isHecke_zero K')).2.2.2.2.2.2.1

theorem isHecke_lconv (hL : LocAlg) {w : Pl E} {K' : Subgroup (UL n w)} (hK : IsLevel (MonoidHom.id _) (KL n w) K')
    {f₁ f₂ : UL n w → ℂ} (h₁ : IsHecke K' f₁) (h₂ : IsHecke K' f₂) : IsHecke K' (lconv f₁ f₂) :=
  (hL E n w (SmIrr.triv _) K' hK f₁ f₂ h₁ h₂).2.2.1

theorem lone_KL (w : Pl E) : lone (KL n w) = unitFn n w := by
  simp [lone, unitFn, Subgroup.relIndex_self]
  rfl

theorem isHecke_lpow (hL : LocAlg) {w : Pl E} {K' : Subgroup (UL n w)} (hK : IsLevel (MonoidHom.id _) (KL n w) K')
    {g : UL n w → ℂ} (hg : IsHecke K' g) (k : ℕ) : IsHecke K' (lpow K' g k) := by
  induction k with
  | zero => exact isHecke_lone hL hK
  | succ k ih => exact isHecke_lconv hL hK hg ih

section Fam

variable {S : Set (Pl E)} {lam : InfinitePlace E → DomWeight n} {K' : ∀ w : Pl E, Subgroup (UL n w)}
  (F : UFam S lam K') {B : Finset (Pl E)}

end Fam

end GlobalTheory.CompanionTheory.UnitaryWord

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriDoubleCosetTorusNilpotent
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL Matrix ValuativeRel GlobalTheory.CompanionTheory.IwJac
open scoped Classical

namespace GlobalTheory.CompanionTheory.IwJac.DCoset

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem tor_inv (ϖ : kˣ) (x : Fin n → ℤ) : (tor ϖ x)⁻¹ = tor ϖ (fun i => - x i) := by
  unfold tor
  rw [← map_inv]
  congr 1
  funext i
  simp [_root_.zpow_neg]

theorem conj_apply (ϖ : kˣ) (x : Fin n → ℤ) (l : GL (Fin n) k) (i j : Fin n) :
    (((tor ϖ x)⁻¹ * l * tor ϖ x : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j =
      ((ϖ ^ (x j - x i) : kˣ) : k) * (l : Matrix (Fin n) (Fin n) k) i j := by
  rw [tor_inv, Units.val_mul, Units.val_mul]
  unfold tor
  rw [val_diagT, val_diagT, Matrix.mul_diagonal, Matrix.diagonal_mul, sub_eq_add_neg, add_comm (x j),
    _root_.zpow_add, Units.val_mul]
  ring

theorem val_zpow_lt_one {ϖ : kˣ} (hϖ : ord k ϖ = 1) {m : ℤ} (hm : 0 < m) :
    valuation k ((ϖ ^ m : kˣ) : k) < 1 := by
  have h := GlobalTheory.OrdShellInt.val_le_iff_ord (k := k) 1 (ϖ ^ m)
  have h_one : ord k (1 : kˣ) = 0 := ord_eq_zero (k := k) (by simp)
  rw [GlobalTheory.OrdShellInt.ord_zpow, hϖ, h_one] at h
  rw [Units.val_one, map_one] at h
  exact not_le.1 fun h' => absurd (h.1 h') (by omega)

theorem conj_entries {ϖ : kˣ} (hϖ : ord k ϖ = 1) {x : Fin n → ℤ} (hx : StrictAnti x) {l : GL (Fin n) k}
    (hl : l ∈ iwahori k (Fin n) ⊓ unipBLower k (Fin n)) (i j : Fin n) :
    valuation k ((((tor ϖ x)⁻¹ * l * tor ϖ x : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j) ≤ 1 ∧
      (j < i → valuation k ((((tor ϖ x)⁻¹ * l * tor ϖ x : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j) < 1) := by
  obtain ⟨h0, h1⟩ := GlobalTheory.IwahoriTraceProof.mem_unipBLower.1 hl.2
  have hint : valuation k ((l : Matrix (Fin n) (Fin n) k) i j) ≤ 1 :=
    (Valuation.mem_integer_iff _ _).1 (((GlobalTheory.SplitFlip.mem_KO_iff l).1 (iwahori_le_KO k (Fin n) hl.1)).1 i j)
  rw [conj_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · rw [h0 i j h, mul_zero, map_zero]
    exact ⟨zero_le', fun h' => absurd h' h.not_gt⟩
  · rw [h1, sub_self]
    simp
  · have hlt : valuation k (((ϖ ^ (x j - x i) : kˣ) : k) * (l : Matrix (Fin n) (Fin n) k) i j) < 1 := by
      rw [map_mul]
      refine lt_of_le_of_lt (mul_le_mul' le_rfl hint) ?_
      rw [mul_one]
      exact val_zpow_lt_one hϖ (sub_pos.2 (hx h))
    exact ⟨hlt.le, fun _ => hlt⟩

theorem conj_mem_iwahori {ϖ : kˣ} (hϖ : ord k ϖ = 1) {x : Fin n → ℤ} (hx : StrictAnti x) {l : GL (Fin n) k}
    (hl : l ∈ iwahori k (Fin n) ⊓ unipBLower k (Fin n)) :
    (tor ϖ x)⁻¹ * l * tor ϖ x ∈ iwahori k (Fin n) := by
  refine mem_iwahori.2 ⟨(GlobalTheory.SplitFlip.mem_KO_iff _).2 ⟨fun i j => ?_, fun i j => ?_⟩,
    fun i j hij => (conj_entries hϖ hx hl i j).2 hij⟩
  · exact (Valuation.mem_integer_iff _ _).2 (conj_entries hϖ hx hl i j).1
  · have e : ((tor ϖ x)⁻¹ * l * tor ϖ x)⁻¹ = (tor ϖ x)⁻¹ * l⁻¹ * tor ϖ x := by group
    rw [e]
    exact (Valuation.mem_integer_iff _ _).2 (conj_entries hϖ hx (inv_mem hl) i j).1

theorem diagT_conj_tor (ϖ : kˣ) (x : Fin n → ℤ) (s : Fin n → kˣ) :
    tor ϖ x * diagT k (Fin n) s * (tor ϖ x)⁻¹ = diagT k (Fin n) s := by
  have e : tor ϖ x * diagT k (Fin n) s = diagT k (Fin n) s * tor ϖ x := by
    unfold tor
    rw [← map_mul, ← map_mul, mul_comm]
  rw [e]
  group

end GlobalTheory.CompanionTheory.IwJac.DCoset

namespace GlobalTheory.CompanionTheory.IwJac

end GlobalTheory.CompanionTheory.IwJac

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousBlkOneVal
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.UnipLevel

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem blk_one_inv {a b n : ℕ} (h : a + b = n) (w : Pl E) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    (blk h w 1 X)⁻¹ = blk h w 1 (-X) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [GlobalTheory.LeviFubini.blk_mul_blk]
  simpa using GlobalTheory.LeviFubini.blk_one_zero h w

theorem blk_one_corner {a b n : ℕ} (h : a + b = n) (w : Pl E) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E))
    (i : Fin a) (j : Fin b) :
    (blk h w 1 X).val (CtLevel.blkEq h (Sum.inl i)) (CtLevel.blkEq h (Sum.inr j)) = X i j := by
  rw [CtLevel.blk_val]
  simp

theorem continuous_blk_one_val {a b n : ℕ} (h : a + b = n) (w : Pl E) :
    Continuous fun X : Matrix (Fin a) (Fin b) (w.adicCompletion E) => (blk h w 1 X).val := by
  refine continuous_matrix fun i j => ?_
  obtain ⟨i, rfl⟩ := (CtLevel.blkEq h).surjective i
  obtain ⟨j, rfl⟩ := (CtLevel.blkEq h).surjective j
  simp only [CtLevel.blk_val, reindex_apply, submatrix_apply, Equiv.symm_apply_apply]
  rcases i with i | i <;> rcases j with j | j
  · simpa using continuous_const
  · simpa using continuous_id.matrix_elem i j
  · simpa using continuous_const
  · simpa using continuous_const

theorem continuous_blk_one {a b n : ℕ} (h : a + b = n) (w : Pl E) :
    Continuous fun X : Matrix (Fin a) (Fin b) (w.adicCompletion E) => blk h w 1 X := by
  refine Units.continuous_iff.2 ⟨continuous_blk_one_val h w, ?_⟩
  have e : (fun X : Matrix (Fin a) (Fin b) (w.adicCompletion E) => (((blk h w 1 X)⁻¹ : GLw n w)).val) =
      (fun X => (blk h w 1 X).val) ∘ fun X => -X := by
    funext X
    simp [blk_one_inv]
  exact e ▸ (continuous_blk_one_val h w).comp continuous_neg

def intSub (a b : ℕ) (w : Pl E) : Subgroup (Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E))) where
  carrier := {X | ∀ i j, Valued.v (Multiplicative.toAdd X i j) ≤ 1}
  one_mem' := fun i j => by simp
  mul_mem' := fun {X Y} hX hY i j => by
    simpa using (Valued.v.map_add _ _).trans (max_le (hX i j) (hY i j))
  inv_mem' := fun {X} hX i j => by simpa using hX i j

theorem intMat_eq_intSub (a b : ℕ) (w : Pl E) : intMat a b w = intSub a b w := by
  refine le_antisymm ((Subgroup.closure_le _).2 fun X hX => hX) fun X hX => Subgroup.subset_closure hX

theorem isCompact_intSub (a b : ℕ) (w : Pl E) :
    IsCompact (intSub a b w : Set (Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)))) := by
  have e : (intSub a b w : Set (Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)))) =
      Multiplicative.toAdd ⁻¹' (Set.pi Set.univ fun _ : Fin a => Set.pi Set.univ
        fun _ : Fin b => ((w.adicCompletionIntegers E : Set (w.adicCompletion E)))) := by
    ext X
    exact ⟨fun hX i _ j _ => hX i j, fun hX i j => hX i trivial j trivial⟩
  rw [e]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers w

theorem unip_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b n : ℕ) (h : a + b = n) (w : Pl E) (K' : Subgroup (GLw n w)), IsOpen (K' : Set (GLw n w)) → K' ≤ GlobalTheory.LFun.KGL w (n := n) → (K'.subgroupOf (GlobalTheory.LeviFubini.parB h w)).comap (GlobalTheory.LeviFubini.uN h w) ≤ intMat a b w ∧ ((K'.subgroupOf (GlobalTheory.LeviFubini.parB h w)).comap (GlobalTheory.LeviFubini.uN h w)).relIndex (intMat a b w) ≠ 0 := by
  intro E _ _ _ a b n h w K' hK' hKK
  have hmem : ∀ X, X ∈ (K'.subgroupOf (GlobalTheory.LeviFubini.parB h w)).comap (GlobalTheory.LeviFubini.uN h w) ↔
      blk h w 1 (Multiplicative.toAdd X) ∈ K' := fun X => Iff.rfl
  refine ⟨fun X hX => ?_, ?_⟩
  · rw [intMat_eq_intSub]
    intro i j
    obtain ⟨u, hu⟩ := hKK ((hmem X).1 hX)
    have h1 : Valued.v ((blk h w 1 (Multiplicative.toAdd X)).val (CtLevel.blkEq h (Sum.inl i))
        (CtLevel.blkEq h (Sum.inr j))) ≤ 1 := by
      rw [← hu]
      exact (u.val (CtLevel.blkEq h (Sum.inl i)) (CtLevel.blkEq h (Sum.inr j))).2
    rwa [blk_one_corner] at h1
  · have hopen : IsOpen (((K'.subgroupOf (GlobalTheory.LeviFubini.parB h w)).comap (GlobalTheory.LeviFubini.uN h w) :
        Subgroup _) : Set (Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)))) :=
      hK'.preimage ((continuous_blk_one h w).comp continuous_toAdd)
    rw [intMat_eq_intSub]
    haveI : CompactSpace (intSub a b w) := isCompact_iff_compactSpace.1 (isCompact_intSub a b w)
    haveI : Finite ((intSub a b w) ⧸ ((K'.subgroupOf (GlobalTheory.LeviFubini.parB h w)).comap (GlobalTheory.LeviFubini.uN h w)).subgroupOf (intSub a b w)) :=
      Subgroup.quotient_finite_of_isOpen _ (hopen.preimage continuous_subtype_val)
    exact Subgroup.index_ne_zero_of_finite

end GlobalTheory.CompanionTheory.UnipLevel
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedUnipotentCompactExhaustion
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.UnipExhaust

theorem exists_compact_subgroup_between {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {N : ℕ} {U : Subgroup (GL (Fin N) k)}
    (hU : U ≤ unipB k (Fin N)) (hcl : IsClosed (U : Set (GL (Fin N) k)))
    (Q : Set (GL (Fin N) k)) (hQ : IsCompact Q) (hQU : Q ⊆ (U : Set (GL (Fin N) k))) :
    ∃ L : {L : Subgroup (GL (Fin N) k) // IsCompact (L : Set (GL (Fin N) k)) ∧ L ≤ U},
      Q ⊆ (L.1 : Set (GL (Fin N) k)) := by
  have hQU' : Q ⊆ (unipB k (Fin N) : Set (GL (Fin N) k)) := fun g hg => hU (hQU hg)
  have hbase : ∃ U₀ : Subgroup (GL (Fin N) k), IsCompact (U₀ : Set (GL (Fin N) k)) ∧ Q ⊆ (U₀ : Set (GL (Fin N) k)) := by
    set c : Fin N → ℤ := fun i => ((i : ℕ) : ℤ)
    have heq : unipB k (Fin N) = GlobalTheory.InertSupp.unipOf k c := by
      ext g
      rw [mem_unipB, GlobalTheory.InertSupp.mem_unipOf]
      constructor
      · rintro ⟨h1, h2⟩ i j hij
        have hji : j ≤ i := by
          dsimp [c] at hij
          rw [not_lt] at hij
          exact Fin.le_def.2 (by exact_mod_cast hij)
        rcases hji.lt_or_eq with h | h
        · rw [h1 i j h, Matrix.one_apply_ne (ne_of_gt h)]
        · subst h; rw [h2 j, Matrix.one_apply_eq]
      · intro h
        refine ⟨fun i j hji => ?_, fun i => ?_⟩
        · have : ¬ ((i : ℕ) : ℤ) < ((j : ℕ) : ℤ) := by
            have := Fin.lt_def.1 hji
            omega
          rw [h i j this, Matrix.one_apply_ne (ne_of_gt hji)]
        · rw [h i i (lt_irrefl _), Matrix.one_apply_eq]
    rw [heq] at hQU'
    let V : ℕ → Set (GL (Fin N) k) := fun m =>
      (GlobalTheory.IwahoriInj.grp k (GlobalTheory.UnipCompact.conc_mul_sub c m) : Set (GL (Fin N) k)) ∪ (GlobalTheory.InertSupp.unipOf k c : Set _)ᶜ
    have hVo : ∀ m, IsOpen (V m) := fun m =>
      (GlobalTheory.UnipCptSub.isOpen_grp c m).union (GlobalTheory.UnipCompact.isClosed_unipOf c).isOpen_compl
    have hVmono : Monotone V := by
      intro m M hmM g hg
      rcases hg with hg | hg
      · by_cases hu : g ∈ GlobalTheory.InertSupp.unipOf k c
        · apply Or.inl
          have key : ∀ x : GL (Fin N) k, x ∈ GlobalTheory.InertSupp.unipOf k c →
              (∀ i j, GlobalTheory.IwahoriInj.Deep ((m : ℤ) * (c i - c j)) (x.val i j)) →
              ∀ i j, GlobalTheory.IwahoriInj.Deep ((M : ℤ) * (c i - c j)) (x.val i j) := by
            intro x hx hd i j
            by_cases hij : c i < c j
            · refine (hd i j).mono ?_
              have : (m : ℤ) ≤ M := by exact_mod_cast hmM
              nlinarith
            · rw [GlobalTheory.InertSupp.mem_unipOf.1 hx i j hij]
              by_cases e : i = j
              · subst e
                simp [GlobalTheory.IwahoriInj.deep_zero_iff]
              · simp [Matrix.one_apply_ne e, GlobalTheory.IwahoriInj.deep_zero]
          exact ⟨key g hu hg.1, key g⁻¹ (inv_mem hu) hg.2⟩
        · exact Or.inr hu
      · exact Or.inr hg
    have hcov : Q ⊆ ⋃ m, V m := fun g hg =>
      Set.mem_iUnion.2 (((GlobalTheory.UnipCompact.eventually_mem_grp (hQU' hg)).exists).imp fun _ h => Or.inl h)
    obtain ⟨M, hM⟩ := hQ.elim_directed_cover V hVo hcov hVmono.directed_le
    refine ⟨GlobalTheory.IwahoriInj.grp k (GlobalTheory.UnipCompact.conc_mul_sub c M) ⊓ GlobalTheory.InertSupp.unipOf k c, ?_, fun g hg => ?_⟩
    · rw [Subgroup.coe_inf]
      exact (GlobalTheory.IwahoriInj.isCompact_grp _).inter_right (GlobalTheory.UnipCompact.isClosed_unipOf c)
    · rcases hM hg with h | h
      · exact ⟨h, hQU' hg⟩
      · exact absurd (hQU' hg) h
  obtain ⟨U₀, hc, hs⟩ := hbase
  refine ⟨⟨U₀ ⊓ U, ?_, inf_le_right⟩, fun g hg => ⟨hs hg, hQU hg⟩⟩
  rw [Subgroup.coe_inf]
  exact hc.inter_right hcl

theorem exists_monotone_compact_exhaustion :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ)
      (U : Subgroup (GL (Fin N) k)), U ≤ unipB k (Fin N) → IsClosed (U : Set (GL (Fin N) k)) →
      ∃ L : ℕ → Subgroup (GL (Fin N) k), Monotone L ∧ (∀ j, IsCompact (L j : Set (GL (Fin N) k))) ∧
        (∀ j, L j ≤ U) ∧ ∀ n ∈ U, ∃ j, n ∈ L j := by
  intro k _ _ _ _ N U hU hcl
  haveI : SecondCountableTopology (GL (Fin N) k) := GlobalTheory.SplitFlip.secondCountable_GL
  haveI : LocallyCompactSpace (GL (Fin N) k) := GlobalTheory.SplitFlip.locallyCompact_GL
  haveI : SigmaCompactSpace (GL (Fin N) k) := inferInstance
  let S := {L : Subgroup (GL (Fin N) k) // IsCompact (L : Set (GL (Fin N) k)) ∧ L ≤ U}
  let K : ℕ → Set (GL (Fin N) k) := compactCovering (GL (Fin N) k)
  have hstep : ∀ (j : ℕ) (A : S), ∃ B : S,
      (K j ∩ (U : Set (GL (Fin N) k))) ∪ (A.1 : Set (GL (Fin N) k)) ⊆ (B.1 : Set (GL (Fin N) k)) :=
    fun j A => exists_compact_subgroup_between hU hcl _
      (((isCompact_compactCovering _ j).inter_right hcl).union A.2.1)
      (Set.union_subset Set.inter_subset_right A.2.2)
  choose next hnext using hstep
  let b : S := ⟨⊥, by rw [Subgroup.coe_bot]; exact isCompact_singleton, bot_le⟩
  let f : ℕ → S := fun j => Nat.rec b (fun i A => next i A) j
  have hsucc : ∀ j, f (j + 1) = next j (f j) := fun _ => rfl
  refine ⟨fun j => (f j).1, monotone_nat_of_le_succ fun j g hg => ?_, fun j => (f j).2.1,
    fun j => (f j).2.2, fun n hn => ?_⟩
  · rw [hsucc]
    exact hnext j (f j) (Or.inr hg)
  · obtain ⟨j, hj⟩ := Set.mem_iUnion.1
      ((iUnion_compactCovering (GL (Fin N) k)).symm ▸ Set.mem_univ n : n ∈ ⋃ i, K i)
    refine ⟨j + 1, ?_⟩
    show n ∈ (f (j + 1)).1
    rw [hsucc]
    exact hnext j (f j) (Or.inl ⟨hj, hn⟩)

end GlobalTheory.CompanionTheory.UnipExhaust
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedBoxIntegralIdentity
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedBoxIntegralIdentity
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology

namespace GlobalTheory.CompanionTheory.MirPair

theorem setIntegral_inter_box_of_twists {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]
    (ψ : AddChar k Circle) (c : kˣ) (hψ : Continuous ψ) (hc : HasConductor ψ c) (m : ℕ) (t : kˣ)
    (M : Set (Fin m → k)) (f : (Fin m → k) → ℂ) (A : ℂ) (hM : IsCompact M) (hMm : MeasurableSet M)
    (hf : Continuous f)
    (h : ∀ b ∈ box m (c * t⁻¹), ∫ x in M, ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) * f x ∂(piHaar ν m) = A) :
    ∫ x in M ∩ (box m t : Set (Fin m → k)), f x ∂(piHaar ν m) = A := by
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  haveI : (GlobalTheory.CompanionTheory.MirPair.piHaar ν m).IsAddHaarMeasure := by
    unfold GlobalTheory.CompanionTheory.MirPair.piHaar
    infer_instance
  haveI : SigmaFinite (GlobalTheory.CompanionTheory.MirPair.piHaar ν m) := by
    unfold GlobalTheory.CompanionTheory.MirPair.piHaar
    infer_instance
  haveI : (GlobalTheory.CompanionTheory.MirPair.piHaar ν m).IsAddRightInvariant := inferInstance
  set μ := GlobalTheory.CompanionTheory.MirPair.piHaar ν m with hμ
  have hbox : ∀ s : kˣ, GlobalTheory.SplitWeil.FourierPi.box (Fin m) s = (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box m s : Set (Fin m → k)) := by
    intro s
    rw [GlobalTheory.CompanionTheory.BZOnto.PerpSmall.coe_box]
    rfl
  set B' : Set (Fin m → k) := (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box m (c * t⁻¹) : Set (Fin m → k)) with hB'
  set Bt : Set (Fin m → k) := (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box m t : Set (Fin m → k)) with hBt
  have hB'c : IsCompact B' := GlobalTheory.CompanionTheory.BZOnto.PerpSmall.isCompact_box m _
  have hB'm : MeasurableSet B' := hB'c.isClosed.measurableSet
  have hBtm : MeasurableSet Bt := (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.isCompact_box m t).isClosed.measurableSet
  have hpos : 0 < μ.real B' := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (μ.measure_pos_of_mem_nhds (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box_mem_nhds m _)).ne'
      hB'c.measure_lt_top.ne
  have hfour : ∀ x, ∫ b, B'.indicator (fun _ => (1 : ℂ)) b * ((ψ (b ⬝ᵥ x) : Circle) : ℂ) ∂μ =
      Bt.indicator (fun _ => ((μ.real B' : ℝ) : ℂ)) x := by
    intro x
    have e := GlobalTheory.SplitWeil.FourierPi.fourier_indicator_pi μ hc t x
    rw [hbox, hbox] at e
    exact e
  have hcc : Continuous (fun z : Circle => (z : ℂ)) := continuous_induced_dom
  have hdot : Continuous fun q : (Fin m → k) × (Fin m → k) => q.1 ⬝ᵥ q.2 :=
    GlobalTheory.SplitWeil.FourierPi.continuous_dot
  have hψc : Continuous fun q : (Fin m → k) × (Fin m → k) => ((ψ (-(q.1 ⬝ᵥ q.2)) : Circle) : ℂ) :=
    hcc.comp (hψ.comp hdot.neg)
  have hg1 : Integrable (B'.indicator fun _ => (1 : ℂ)) μ :=
    (integrable_indicator_iff hB'm).2 (continuousOn_const.integrableOn_compact' hB'c hB'm)
  have hg2 : Integrable (M.indicator f) μ :=
    (integrable_indicator_iff hMm).2 (hf.continuousOn.integrableOn_compact' hM hMm)
  have hint : Integrable (fun z : (Fin m → k) × (Fin m → k) => ((ψ (-(z.1 ⬝ᵥ z.2)) : Circle) : ℂ) *
      (B'.indicator (fun _ => (1 : ℂ)) z.1 * M.indicator f z.2)) (μ.prod μ) := by
    refine (hg1.mul_prod hg2).bdd_mul (c := 1) hψc.aestronglyMeasurable (ae_of_all _ fun z => ?_)
    simp [Circle.norm_coe]
  have hswap : ∫ b, (∫ x, ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) *
        (B'.indicator (fun _ => (1 : ℂ)) b * M.indicator f x) ∂μ) ∂μ =
      ∫ x, (∫ b, ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) *
        (B'.indicator (fun _ => (1 : ℂ)) b * M.indicator f x) ∂μ) ∂μ :=
    integral_integral_swap hint
  have hD : (fun b => ∫ x, ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) *
      (B'.indicator (fun _ => (1 : ℂ)) b * M.indicator f x) ∂μ) = B'.indicator (fun _ => A) := by
    funext b
    by_cases hb : b ∈ B'
    · simp only [Set.indicator_of_mem hb, one_mul]
      have hx : (fun x => ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) * M.indicator f x) =
          M.indicator (fun x => ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) * f x) := by
        funext x
        by_cases hxM : x ∈ M
        · simp only [Set.indicator_of_mem hxM]
        · simp only [Set.indicator_of_notMem hxM, mul_zero]
      rw [hx, integral_indicator hMm]
      exact h b hb
    · simp [Set.indicator_of_notMem hb]
  have hE : (fun x => ∫ b, ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) *
      (B'.indicator (fun _ => (1 : ℂ)) b * M.indicator f x) ∂μ) =
      fun x => ((μ.real B' : ℝ) : ℂ) * (M ∩ Bt).indicator f x := by
    funext x
    have e : ∀ b, ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) * (B'.indicator (fun _ => (1 : ℂ)) b * M.indicator f x) =
        B'.indicator (fun _ => (1 : ℂ)) b * ((ψ (b ⬝ᵥ -x) : Circle) : ℂ) * M.indicator f x := by
      intro b
      rw [dotProduct_neg]
      ring
    simp only [e]
    rw [integral_mul_const, hfour (-x)]
    have hneg : -x ∈ Bt ↔ x ∈ Bt := by
      simp only [hBt, SetLike.mem_coe, neg_mem_iff]
    by_cases hxB : x ∈ Bt
    · by_cases hxM : x ∈ M
      · simp only [Set.indicator_of_mem (hneg.2 hxB), Set.indicator_of_mem hxM,
          Set.indicator_of_mem (Set.mem_inter hxM hxB)]
      · simp only [Set.indicator_of_mem (hneg.2 hxB), Set.indicator_of_notMem hxM,
          Set.indicator_of_notMem (fun hx : x ∈ M ∩ Bt => hxM hx.1), mul_zero]
    · simp only [Set.indicator_of_notMem (fun hx : -x ∈ Bt => hxB (hneg.1 hx)),
        Set.indicator_of_notMem (fun hx : x ∈ M ∩ Bt => hxB hx.2), zero_mul, mul_zero]
  rw [hD, hE, integral_indicator_const _ hB'm, integral_const_mul,
    integral_indicator (hMm.inter hBtm), Complex.real_smul] at hswap
  exact (mul_left_cancel₀ (Complex.ofReal_ne_zero.2 hpos.ne') hswap).symm

end GlobalTheory.CompanionTheory.MirPair
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedBoxIntegralIdentityStatement
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_box_integral_vanishing : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (c : kˣ), Continuous ψ → HasConductor ψ c → ∀ (m : ℕ) (t : kˣ) (M : Set (Fin m → k)) (f : (Fin m → k) → ℂ) (A : ℂ), IsCompact M → MeasurableSet M → Continuous f → (∀ b ∈ box m (c * t⁻¹), ∫ x in M, ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) * f x ∂(piHaar ν m) = A) → ∫ x in M ∩ (box m t : Set (Fin m → k)), f x ∂(piHaar ν m) = A := by
  first | exact @GlobalTheory.CompanionTheory.MirPair.setIntegral_inter_box_of_twists | exact GlobalTheory.CompanionTheory.MirPair.setIntegral_inter_box_of_twists | (intros; apply GlobalTheory.CompanionTheory.MirPair.setIntegral_inter_box_of_twists <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothVectorFixedParabolicNearOne
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothVectorFixedParabolicNearOne
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.OntoO

theorem sigX_fix_nhds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ)
    (v : τ.V ⊗[ℂ] σ.V), ∃ O ∈ 𝓝 (1 : Mir k ((i + 1) + t + 1)), ∀ a : HPG k (i + 1) (t + 1),
      (a : Mir k ((i + 1) + (t + 1))) ∈ O → sigX τ σ a v = v :=
  GlobalTheory.CompanionTheory.BZPhiPG.Onto.sigX_fix

end GlobalTheory.CompanionTheory.BZPhiPG.OntoO
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothVectorFixedParabolicNearOneStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_vector_fixed_parabolic_near_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ)
    (v : τ.V ⊗[ℂ] σ.V), ∃ O ∈ 𝓝 (1 : Mir k ((i + 1) + t + 1)), ∀ a : HPG k (i + 1) (t + 1),
      (a : Mir k ((i + 1) + (t + 1))) ∈ O → sigX τ σ a v = v := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.OntoO.sigX_fix_nhds | exact GlobalTheory.CompanionTheory.BZPhiPG.OntoO.sigX_fix_nhds | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.OntoO.sigX_fix_nhds <;> assumption)
end
end
