module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfEig
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalMod
public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.MirabolicColumnBlock
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UfamConst
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.lift_levelP_alt₂
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFundamentalDomainMassOneCocompactLattice

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleOfFiniteLengthSubquotients
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleOfFiniteLengthSubquotients
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.AdmFL

variable {G X Y Z : Type} [Group G] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
  [AddCommGroup Z] [Module ℂ Z]

theorem mem_fixed_iff {α : Representation ℂ G X} {K : Subgroup G} {x : X} :
    x ∈ fixed α K ↔ ∀ g ∈ K, α g x = x := by
  change (∀ h : K, α h x = ((1 : K →* ℂˣ) h : ℂ) • x) ↔ _
  simp only [MonoidHom.one_apply, Units.val_one, one_smul]
  exact ⟨fun h g hg => h ⟨g, hg⟩, fun h g => h g g.2⟩

private theorem finiteDimensional_fixed_of_exact_lemma {α : Representation ℂ G X}
    {β : Representation ℂ G Y} (i : α.IntertwiningMap β) (g : G) (x : X) :
    i (α g x) = β g (i x) := by
  have h := LinearMap.congr_fun (i.isIntertwining' g) x
  simpa [LinearMap.comp_apply] using h

theorem finiteDimensional_fixed_of_exact {α : Representation ℂ G X} {β : Representation ℂ G Y}
    {γ : Representation ℂ G Z} (i : α.IntertwiningMap β) (p : β.IntertwiningMap γ)
    (hi : Function.Injective i) (hker : ∀ y, p y = 0 → ∃ x, i x = y) (K : Subgroup G)
    [FiniteDimensional ℂ (fixed α K)] [FiniteDimensional ℂ (fixed γ K)] :
    FiniteDimensional ℂ (fixed β K) := by
  let j : fixed α K →ₗ[ℂ] fixed β K :=
    { toFun := fun x => ⟨i x, mem_fixed_iff.2 fun g hg => by
        rw [← finiteDimensional_fixed_of_exact_lemma i g x, mem_fixed_iff.1 x.2 g hg]⟩
      map_add' := fun x y => by ext; simp
      map_smul' := fun c x => by ext; simp }
  let q : fixed β K →ₗ[ℂ] fixed γ K :=
    { toFun := fun y => ⟨p y, mem_fixed_iff.2 fun g hg => by
        rw [← finiteDimensional_fixed_of_exact_lemma p g y, mem_fixed_iff.1 y.2 g hg]⟩
      map_add' := fun x y => by ext; simp
      map_smul' := fun c x => by ext; simp }
  have hK : LinearMap.ker q ≤ LinearMap.range j := by
    intro y hy
    rw [LinearMap.mem_ker] at hy
    have hpy : p (y : Y) = 0 := congrArg Subtype.val hy
    obtain ⟨x, hx⟩ := hker _ hpy
    have hxfix : x ∈ fixed α K := mem_fixed_iff.2 fun g hg => hi (by
      rw [finiteDimensional_fixed_of_exact_lemma i, hx, mem_fixed_iff.1 y.2 g hg])
    exact ⟨⟨x, hxfix⟩, Subtype.ext hx⟩
  refine ⟨?_⟩
  apply Submodule.fg_of_fg_map_of_fg_inf_ker (f := q)
  · exact IsNoetherian.noetherian _
  · rw [Submodule.fg_iff_finiteDimensional]
    exact Submodule.finiteDimensional_of_le (le_trans inf_le_right hK)

private theorem isAdmissible_of_hasFiniteLength_lemma_3 {M : Type} [AddCommGroup M] [Module ℂ M]
    [Module (MonoidAlgebra ℂ G) M] [IsScalarTower ℂ (MonoidAlgebra ℂ G) M] (g : G) (x : M) :
    Representation.ofModule' (k := ℂ) (G := G) M g x = MonoidAlgebra.single g (1 : ℂ) • x := by
  first
  | rfl
  | simp only [Representation.ofModule', MonoidAlgebra.lift_symm_apply, Algebra.lsmul_coe]

private theorem isAdmissible_of_hasFiniteLength_lemma_2 {M₁ M₂ : Type} [AddCommGroup M₁] [Module ℂ M₁]
    [Module (MonoidAlgebra ℂ G) M₁] [IsScalarTower ℂ (MonoidAlgebra ℂ G) M₁] [AddCommGroup M₂] [Module ℂ M₂]
    [Module (MonoidAlgebra ℂ G) M₂] [IsScalarTower ℂ (MonoidAlgebra ℂ G) M₂]
    (f : M₁ →ₗ[MonoidAlgebra ℂ G] M₂) :
    ∃ φ : (Representation.ofModule' (k := ℂ) (G := G) M₁).IntertwiningMap
        (Representation.ofModule' (k := ℂ) (G := G) M₂), ∀ x, φ x = f x := by
  refine ⟨⟨f.restrictScalars ℂ, fun g => ?_⟩, fun x => rfl⟩
  ext x
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, isAdmissible_of_hasFiniteLength_lemma_3,
    map_smul]

private theorem isAdmissible_of_hasFiniteLength_lemma_5 {M : Type} [AddCommGroup M] [Module ℂ M]
    [Module (MonoidAlgebra ℂ G) M] [IsScalarTower ℂ (MonoidAlgebra ℂ G) M]
    [IsSimpleModule (MonoidAlgebra ℂ G) M] :
    (Representation.ofModule' (k := ℂ) (G := G) M).IsIrreducible := by
  have e : Subrepresentation (Representation.ofModule' (k := ℂ) (G := G) M) ≃o
      Submodule (MonoidAlgebra ℂ G) M :=
    { toFun := fun S =>
        { carrier := S.toSubmodule
          add_mem' := fun hx hy => S.toSubmodule.add_mem hx hy
          zero_mem' := S.toSubmodule.zero_mem
          smul_mem' := fun a x hx => by
            induction a using MonoidAlgebra.induction_on with
            | of g =>
              rw [MonoidAlgebra.of_apply, ← isAdmissible_of_hasFiniteLength_lemma_3]
              exact S.apply_mem_toSubmodule g hx
            | add a b ha hb =>
              rw [add_smul]
              exact S.toSubmodule.add_mem ha hb
            | smul r a ha =>
              rw [smul_assoc]
              exact S.toSubmodule.smul_mem r ha }
      invFun := fun P => ⟨P.restrictScalars ℂ, fun g v hv => by
        rw [Submodule.restrictScalars_mem, isAdmissible_of_hasFiniteLength_lemma_3]
        exact P.smul_mem _ hv⟩
      left_inv := fun S => by
        apply Subrepresentation.ext
        rfl
      right_inv := fun P => by
        ext x
        rfl
      map_rel_iff' := by
        intro S T
        exact Iff.rfl }
  exact e.isSimpleOrder

private theorem isAdmissible_of_hasFiniteLength_lemma_4 [TopologicalSpace G] (K : Subgroup G) :
    ∀ {M : Type} [AddCommGroup M] [Module (MonoidAlgebra ℂ G) M], IsFiniteLength (MonoidAlgebra ℂ G) M →
    ∀ [Module ℂ M] [IsScalarTower ℂ (MonoidAlgebra ℂ G) M],
    (∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G W),
      IsSubquotient σ (Representation.ofModule' (k := ℂ) (G := G) M) → σ.IsIrreducible → IsAdmissible σ) →
    IsOpen (K : Set G) → IsCompact (K : Set G) →
    FiniteDimensional ℂ (fixed (Representation.ofModule' (k := ℂ) (G := G) M) K) := by
  intro M _ _ hM
  induction hM with
  | of_subsingleton =>
    intro _ _ _ _ _
    infer_instance
  | @of_simple_quotient M _ _ N _ hN ih =>
    intro _ _ hsub hKo hKc
    obtain ⟨i, hi⟩ := isAdmissible_of_hasFiniteLength_lemma_2 (G := G) N.subtype
    obtain ⟨p, hp⟩ := isAdmissible_of_hasFiniteLength_lemma_2 (G := G) N.mkQ
    have hinj : Function.Injective i := by
      intro x y hxy
      rw [hi, hi] at hxy
      exact Subtype.ext hxy
    have hker : ∀ y, p y = 0 → ∃ x, i x = y := by
      intro y hy
      rw [hp, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hy
      exact ⟨⟨y, hy⟩, by rw [hi]; rfl⟩
    have hsurj : Function.Surjective p := by
      intro z
      obtain ⟨m, hm⟩ := Submodule.mkQ_surjective N z
      exact ⟨m, by rw [hp]; exact hm⟩
    have hNsub : IsSubquotient (Representation.ofModule' (k := ℂ) (G := G) N)
        (Representation.ofModule' (k := ℂ) (G := G) M) := IsSubquotient.of_injective i hinj
    haveI : FiniteDimensional ℂ (fixed (Representation.ofModule' (k := ℂ) (G := G) N) K) :=
      ih (fun W _ _ σ hσ hirr => hsub W σ (hσ.trans hNsub) hirr) hKo hKc
    haveI : FiniteDimensional ℂ (fixed (Representation.ofModule' (k := ℂ) (G := G) (M ⧸ N)) K) := by
      have hirr : (Representation.ofModule' (k := ℂ) (G := G) (M ⧸ N)).IsIrreducible :=
        isAdmissible_of_hasFiniteLength_lemma_5
      have hadm := hsub _ _ (IsSubquotient.of_surjective p hsurj) hirr
      unfold IsAdmissible at hadm
      exact hadm.2 K hKo hKc
    exact finiteDimensional_fixed_of_exact i p hinj hker K

theorem isAdmissible_of_hasFiniteLength : ∀ {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), IsSmooth ρ → HasFiniteLength ρ → (∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G W), IsSubquotient σ ρ → σ.IsIrreducible → IsAdmissible σ) → IsAdmissible ρ := by
  intro G V _ _ _ _ _ ρ hsm hfl hirr
  unfold IsAdmissible
  refine ⟨hsm, fun K hKo hKc => ?_⟩
  letI instA : Module (MonoidAlgebra ℂ G) V := Module.compHom V ρ.asAlgebraHom.toRingHom
  haveI instT : IsScalarTower ℂ (MonoidAlgebra ℂ G) V := ⟨fun c a v => by
    show ρ.asAlgebraHom (c • a) v = c • ρ.asAlgebraHom a v
    rw [map_smul]
    rfl⟩
  have hρ : Representation.ofModule' (k := ℂ) (G := G) V = ρ := by
    ext g v
    rw [isAdmissible_of_hasFiniteLength_lemma_3]
    show ρ.asAlgebraHom (MonoidAlgebra.single g 1) v = ρ g v
    rw [Representation.asAlgebraHom_single_one]
  have hfl' : IsFiniteLength (MonoidAlgebra ℂ G) V := hfl
  have h := @isAdmissible_of_hasFiniteLength_lemma_4 G _ _ K V _ instA hfl' _ instT
    (fun W _ _ σ hσ h => hirr W σ (hρ ▸ hσ) h) hKo hKc
  rw [hρ] at h
  exact h

end GlobalTheory.CompanionTheory.AdmFL

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleOfFiniteLengthSubquotientsStatement
open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissible_of_finite_length_subquotients : ∀ {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), IsSmooth ρ → HasFiniteLength ρ → (∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G W), IsSubquotient σ ρ → σ.IsIrreducible → IsAdmissible σ) → IsAdmissible ρ := by
  first | exact @GlobalTheory.CompanionTheory.AdmFL.isAdmissible_of_hasFiniteLength | exact GlobalTheory.CompanionTheory.AdmFL.isAdmissible_of_hasFiniteLength | (intros; apply GlobalTheory.CompanionTheory.AdmFL.isAdmissible_of_hasFiniteLength <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteSubquotients
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteSubquotients
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.JHMult
open PositivityTheory.Rg.BcN.F2 (FinSubq)

namespace GlobalTheory.CompanionTheory.RepFinSubq

variable {F G V W : Type} [Field F] [Group G] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]

theorem exists_series {ρ : Representation F G V} (h : HasFiniteLength ρ) :
    ∃ (N : ℕ) (S : Fin (N + 1) → Subrepresentation ρ), Monotone S ∧ S 0 = ⊥ ∧ S (Fin.last N) = ⊤ ∧
      ∀ t : Fin N, S t.castSucc ⋖ S t.succ := by
  obtain ⟨s, h0, h1⟩ := isFiniteLength_iff_exists_compositionSeries.1 h
  let e := (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)).symm
  refine ⟨s.length, fun i => e (s i), ?_, ?_, ?_, fun t => ?_⟩
  · exact e.monotone.comp s.strictMono.monotone
  · show e s.head = ⊥
    rw [h0, map_bot]
  · show e s.last = ⊤
    rw [h1, map_top]
  · exact (apply_covBy_apply_iff e).2 (s.step t)

theorem isSubquotient_subQuot {ρ : Representation F G V} (S T : Subrepresentation ρ) :
    IsSubquotient (subQuot S T) ρ :=
  ⟨S, ⟨Submodule.mkQ _, fun _ => rfl⟩, Submodule.mkQ_surjective _⟩

theorem exists_factor_equiv {ρ : Representation F G V} {N : ℕ} {S : Fin (N + 1) → Subrepresentation ρ}
    (hS : Monotone S) (h0 : S 0 = ⊥) (h1 : S (Fin.last N) = ⊤) (hc : ∀ t : Fin N, S t.castSucc ⋖ S t.succ)
    {τ : Representation F G W} (hτ : τ.IsIrreducible) (hq : IsSubquotient τ ρ) :
    ∃ t : Fin N, Nonempty (τ.Equiv (subQuot (S t.succ) (S t.castSucc))) := by
  have hne : jhMult τ ρ ≠ 0 := jhMult_ne_zero_iff.2 hq
  rw [jhMult_filtration hτ S hS h0 h1] at hne
  obtain ⟨t, -, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨e⟩ := (jhMult_ne_zero_iff.1 ht).nonempty_equiv hτ (isIrreducible_subQuot (hc t))
  exact ⟨t, ⟨e.symm⟩⟩

theorem finSubq : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (ι : Type) [Fintype ι] [DecidableEq ι], FinSubq F ι := by
  intro F _ _ _ _ ι _ _ U _ _ ρ hρ hfl
  obtain ⟨N, S, hS, h0, h1, hc⟩ := exists_series hfl
  refine ⟨Fin N, inferInstance, fun t => _, fun _ => inferInstance, fun _ => inferInstance,
    fun t => subQuot (S t.succ) (S t.castSucc), fun t => ?_, fun W' _ _ τ' hτ hq => ?_⟩
  · exact ⟨(isSubquotient_subQuot _ _).isSmooth hρ, isIrreducible_subQuot (hc t), isSubquotient_subQuot _ _⟩
  · exact exists_factor_equiv hS h0 h1 hc hτ hq

end GlobalTheory.CompanionTheory.RepFinSubq
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteSubquotientsStatement
theorem _root_.GlobalTheory.T.finite_subquotients :
    ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
      (ι : Type) [Fintype ι] [DecidableEq ι], PositivityTheory.Rg.BcN.F2.FinSubq F ι :=
  GlobalTheory.CompanionTheory.RepFinSubq.finSubq
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedDerivativeSystemSmooth
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContDiffOnOfFderivFamily
noncomputable section

open PositivityTheory.jumpWindows
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.SmoothVectors

theorem contDiffOn_of_fderiv_family {E F P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ} {U : Set E} (hU : IsOpen U)
    (o : P → E → F) (S : Set P) (A : Fin n → E → E →L[ℝ] ℝ)
    (hA : ∀ i, ContDiffOn ℝ ∞ (A i) U)
    (h : ∀ v ∈ S, ∃ w : Fin n → P, (∀ i, w i ∈ S) ∧
      ∀ M ∈ U, HasFDerivAt (o v) (∑ i, (A i M).smulRight (o (w i) M)) M) :
    ∀ v ∈ S, ContDiffOn ℝ ∞ (o v) U := by
  have key : ∀ m : ℕ, ∀ v ∈ S, ContDiffOn ℝ m (o v) U := by
    intro m
    induction m with
    | zero =>
      intro v hv
      obtain ⟨w, -, hw⟩ := h v hv
      rw [Nat.cast_zero, contDiffOn_zero]
      exact fun M hM => (hw M hM).continuousAt.continuousWithinAt
    | succ m ih =>
      intro v hv
      obtain ⟨w, hwS, hw⟩ := h v hv
      rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hU]
      refine ⟨fun M hM => (hw M hM).differentiableAt.differentiableWithinAt, fun hm => ?_, ?_⟩
      · exact absurd hm (by simp)
      · refine ContDiffOn.congr (f := fun M => ∑ i, (A i M).smulRight (o (w i) M)) ?_
          fun M hM => (hw M hM).fderiv
        exact ContDiffOn.sum fun i _ =>
          (contDiffOn_infty.1 (hA i) m).smulRight (ih (w i) (hwS i))
  intro v hv
  exact contDiffOn_infty.2 fun m => key m v hv

section Chart

variable {ι : Type} [Fintype ι] {a : ℕ}

section Norm

attribute [-instance] instTopologicalSpaceMatrix

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
  Matrix.linftyOpNormedSpace

end Norm

end Chart

section Orbit

variable {ι : Type} [Fintype ι] {a : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

end Orbit

end GlobalTheory.CompanionTheory.SmoothVectors

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedDerivativeSystemSmooth
open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

namespace GlobalTheory.CompanionTheory.PresSobA

theorem contDiffOn_of_right_family : ∀ (n : ℕ) (V P : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (o : P → Mat n → V) (d : (Bool × Fin n × Fin n) → P → P), (∀ v, ∀ z ∈ GLs n, DifferentiableAt ℝ (o v) z) → (∀ v p, ∀ z ∈ GLs n, Rd (bs p) (o v) z = o (d p v) z) → ∀ v, ContDiffOn ℝ ∞ (o v) (GLs n) := by
  intro n V P _ _ o d hdiff hR v
  obtain ⟨A, hA, hfr⟩ := GlobalTheory.T.derivative_right_basis_expansion n
  let e := Fintype.equivFin (Bool × Fin n × Fin n)
  refine GlobalTheory.CompanionTheory.SmoothVectors.contDiffOn_of_fderiv_family isOpen_GLs o Set.univ
    (fun i => A (e.symm i)) (fun i => hA _) ?_ v (Set.mem_univ v)
  intro u _
  refine ⟨fun i => d (e.symm i) u, fun i => Set.mem_univ _, fun z hz => ?_⟩
  have hD := hfr V (fderiv ℝ (o u) z) z hz
  have hsum : (∑ i, (A (e.symm i) z).smulRight (o (d (e.symm i) u) z))
      = ∑ p, (A p z).smulRight (o (d p u) z) :=
    e.symm.sum_comp (fun p => (A p z).smulRight (o (d p u) z))
  have hval : ∀ p, fderiv ℝ (o u) z (z * bs p) = o (d p u) z := fun p => hR u p z hz
  have h2 : fderiv ℝ (o u) z = ∑ p, (A p z).smulRight (o (d p u) z) :=
    hD.trans (Finset.sum_congr rfl fun p _ => congrArg (fun y : V => (A p z).smulRight y) (hval p))
  exact (hdiff u z hz).hasFDerivAt.congr_fderiv (h2.trans hsum.symm)

end GlobalTheory.CompanionTheory.PresSobA
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedDerivativeSystemSmoothStatement
open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closed_derivative_system_smooth : ∀ (n : ℕ) (V P : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (o : P → Mat n → V) (d : (Bool × Fin n × Fin n) → P → P), (∀ v, ∀ z ∈ GLs n, DifferentiableAt ℝ (o v) z) → (∀ v p, ∀ z ∈ GLs n, Rd (bs p) (o v) z = o (d p v) z) → ∀ v, ContDiffOn ℝ ∞ (o v) (GLs n) := by
  first | exact @GlobalTheory.CompanionTheory.PresSobA.contDiffOn_of_right_family | exact GlobalTheory.CompanionTheory.PresSobA.contDiffOn_of_right_family | (intros; apply GlobalTheory.CompanionTheory.PresSobA.contDiffOn_of_right_family <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalLiftSectionsGenerate
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalLiftSectionsGenerate
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

theorem mem_smul_top_of_redL {R : Type} [CommRing R] (I : Ideal R)
    (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
    (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left)
    (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e))
    (L : ∀ e, LB (Y e).left) (w : ∀ e, LB.Iso (L e) ((L (e + 1)).pull (β e)))
    (hL : ∀ e, (L e).IsLB ∧ (w e).IsGen) (e : ℕ) (V : (Y (e + 1)).left.Opens)
    (V' : (Y e).left.Opens) (h : β e ⁻¹ᵁ V = V') (hV : IsAffineOpen V)
    (x : SecOnR (toR I Y (e + 1)) (L (e + 1)) V)
    (hx : redL I Y β hβ L w hL e V V' h.ge x ∈
      I • (⊤ : Submodule R (SecOnR (toR I Y e) (L e) V'))) :
    x ∈ I • (⊤ : Submodule R (SecOnR (toR I Y (e + 1)) (L (e + 1)) V)) := by
  obtain ⟨hsurj, hker⟩ := GlobalTheory.T.thickening_affine_preimage R I Y β hβ L w hL e V V' h hV
  have hmap : Submodule.map (redL I Y β hβ L w hL e V V' h.ge)
      (I • (⊤ : Submodule R (SecOnR (toR I Y (e + 1)) (L (e + 1)) V))) =
      I • (⊤ : Submodule R (SecOnR (toR I Y e) (L e) V')) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2 hsurj]
  rw [← hmap] at hx
  obtain ⟨z, hz, hzx⟩ := hx
  have hk : x - z ∈ LinearMap.ker (redL I Y β hβ L w hL e V V' h.ge) := by
    rw [LinearMap.mem_ker, map_sub, hzx, sub_self]
  rw [hker] at hk
  have hk' : x - z ∈ I • (⊤ : Submodule R (SecOnR (toR I Y (e + 1)) (L (e + 1)) V)) :=
    Submodule.smul_mono_left (Ideal.pow_le_self (Nat.succ_ne_zero e)) hk
  simpa using Submodule.add_mem _ hk' hz

theorem map_mul_sub_mul {A B : Type} [CommRing A] [CommRing B] (ρ : A →+* B) (x y : A) (z : B) :
    ρ (x * y) - ρ x * z = (ρ y - z) * ρ x := by
  rw [map_mul]; ring

theorem map_mem_smul_top {R M M' : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] (I : Ideal R) (φ : M →ₗ[R] M') {x : M}
    (hx : x ∈ I • (⊤ : Submodule R M)) : φ x ∈ I • (⊤ : Submodule R M') := by
  have h := Submodule.mem_map_of_mem (f := φ) hx
  rw [Submodule.map_smul''] at h
  exact Submodule.smul_mono le_rfl le_top h

theorem resT_mulT_sub_mem : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))) (hN : ∀ e, (N e).IsLB ∧ (v e).IsGen) (d : ℕ) (m : ℕ) (s : Fin (m + 1) → LB.Sec (pw (N 0) (d : ℤ))) (hs : VeryAmpleBy (Y 0).hom (pw (N 0) (d : ℤ)) s) (D : ∀ e, Finset (Fin (m + 1)) → (Y e).left.Opens) (hD0 : ∀ S, D 0 S = ⨅ i ∈ S, nonzeroLocus (s i)) (hDβ : ∀ e S, β e ⁻¹ᵁ D (e + 1) S = D e S) (hDm : ∀ e (S S' : Finset (Fin (m + 1))), S ⊆ S' → D e S' ≤ D e S) (hDi : ∀ e S j, D e (insert j S) = D e S ⊓ D e {j}) (hDc : ∀ e, ⨆ i, D e {i} = ⊤) (hDa : ∀ e S, S.Nonempty → IsAffineOpen (D e S)) (sh : ∀ e (j : Fin (m + 1)) (S : Finset (Fin (m + 1))), SecOn (pw (N e) (d : ℤ)) (D e S)) (hsh0 : ∀ j S, S.Nonempty → sh 0 j S = GlobalTheory.LB.ofSec (s j) (D 0 S)) (hshp : ∀ e j S, S.Nonempty → red I Y N D β hβ v hN (fun e S => (hDβ e S).ge) (d : ℤ) e S (SecOnR.of _ _ _ (sh (e + 1) j S)) = SecOnR.of _ _ _ (sh e j S)) (hshu : ∀ e i S, i ∈ S → ∃ y : SecOn (pw (N e) (-(d : ℤ))) (D e S), secMulOn rfl (sh e i S) y = oneOn (N e) (add_neg_cancel (d : ℤ)) (D e S)) (j : Fin (m + 1)) (e : ℕ) (t : ℤ) (S S' : Finset (Fin (m + 1))) (h : S ⊆ S') (a : Tm I Y N D (d : ℤ) e t S), S.Nonempty → resT I Y N D (d : ℤ) hDm e (t + 1) h (mulT I Y N D (d : ℤ) e t S (sh e j S) a) - mulT I Y N D (d : ℤ) e t S' (sh e j S') (resT I Y N D (d : ℤ) hDm e t h a) ∈ I • (⊤ : Submodule R (Tm I Y N D (d : ℤ) e (t + 1) S')) := by
  intro R _ I Y β hβ N v hN d m s hs D hD0 hDβ hDm hDi hDc hDa sh hsh0 hshp hshu j e t S S' h a hS
  have hS' : S'.Nonempty := hS.mono h

  have key : ∀ e : ℕ, SecOnR.restrict (toR I Y e) (pw (N e) (d : ℤ)) (hDm e S S' h)
        (SecOnR.of _ _ _ (sh e j S)) - SecOnR.of (toR I Y e) _ _ (sh e j S') ∈
      I • (⊤ : Submodule R (SecOnR (toR I Y e) (pw (N e) (d : ℤ)) (D e S'))) := by
    intro e
    induction e with
    | zero =>
      have : SecOnR.restrict (toR I Y 0) (pw (N 0) (d : ℤ)) (hDm 0 S S' h)
          (SecOnR.of _ _ _ (sh 0 j S)) - SecOnR.of (toR I Y 0) _ _ (sh 0 j S') = 0 := by
        rw [hsh0 j S hS, hsh0 j S' hS', sub_eq_zero]
        exact GlobalTheory.LB.map_ofSec (s j) (hDm 0 S S' h)
      rw [this]
      exact Submodule.zero_mem _
    | succ e ih =>
      refine mem_smul_top_of_redL I Y β hβ (fun e => pw (N e) (d : ℤ))
        (fun e => pullPow (v e) (d : ℤ))
        (fun e => ⟨isLB_pw (hN e).1 _, pullPow_isGen (v e) _ (hN e).2⟩) e (D (e + 1) S')
        (D e S') (hDβ e S') (hDa (e + 1) S' hS') _ ?_
      rw [map_sub]
      have h1 := GlobalTheory.T.thickening_restriction_compatible_opens R I Y β hβ (fun e => pw (N e) (d : ℤ))
        (fun e => pullPow (v e) (d : ℤ))
        (fun e => ⟨isLB_pw (hN e).1 _, pullPow_isGen (v e) _ (hN e).2⟩) e (D (e + 1) S)
        (D (e + 1) S') (D e S) (D e S') (hDβ e S).ge (hDβ e S').ge (hDm (e + 1) S S' h)
        (hDm e S S' h) (SecOnR.of _ _ _ (sh (e + 1) j S))
      have h2 := hshp e j S hS
      have h3 := hshp e j S' hS'
      rw [h1]
      erw [h2, h3]
      exact ih
  have hmem := map_mem_smul_top I
    (mulRight (toR I Y e) (show (d : ℤ) + (d : ℤ) * t = (d : ℤ) * (t + 1) by ring)
      ((SecOnR.of _ _ _).symm (resT I Y N D (d : ℤ) hDm e t h a))) (key e)
  convert hmem using 1
  refine SecOnR.ext fun (i : (N e).ι) => ?_
  exact map_mul_sub_mul (rs (Y e).left (inf_le_inf_right ((N e).U i) (hDm e S S' h)))
    (SecOnR.coord a i) (GlobalTheory.LB.coord (sh e j S) i) (GlobalTheory.LB.coord (sh e j S') i)

end GlobalTheory.CompanionTheory.FormalAlg.Lift
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalLiftSectionsGenerateStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_lift_sections_generate : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))) (hN : ∀ e, (N e).IsLB ∧ (v e).IsGen) (d : ℕ) (m : ℕ) (s : Fin (m + 1) → LB.Sec (pw (N 0) (d : ℤ))) (hs : VeryAmpleBy (Y 0).hom (pw (N 0) (d : ℤ)) s) (D : ∀ e, Finset (Fin (m + 1)) → (Y e).left.Opens) (hD0 : ∀ S, D 0 S = ⨅ i ∈ S, nonzeroLocus (s i)) (hDβ : ∀ e S, β e ⁻¹ᵁ D (e + 1) S = D e S) (hDm : ∀ e (S S' : Finset (Fin (m + 1))), S ⊆ S' → D e S' ≤ D e S) (hDi : ∀ e S j, D e (insert j S) = D e S ⊓ D e {j}) (hDc : ∀ e, ⨆ i, D e {i} = ⊤) (hDa : ∀ e S, S.Nonempty → IsAffineOpen (D e S)) (sh : ∀ e (j : Fin (m + 1)) (S : Finset (Fin (m + 1))), SecOn (pw (N e) (d : ℤ)) (D e S)) (hsh0 : ∀ j S, S.Nonempty → sh 0 j S = GlobalTheory.LB.ofSec (s j) (D 0 S)) (hshp : ∀ e j S, S.Nonempty → red I Y N D β hβ v hN (fun e S => (hDβ e S).ge) (d : ℤ) e S (SecOnR.of _ _ _ (sh (e + 1) j S)) = SecOnR.of _ _ _ (sh e j S)) (hshu : ∀ e i S, i ∈ S → ∃ y : SecOn (pw (N e) (-(d : ℤ))) (D e S), secMulOn rfl (sh e i S) y = oneOn (N e) (add_neg_cancel (d : ℤ)) (D e S)) (j : Fin (m + 1)) (e : ℕ) (t : ℤ) (S S' : Finset (Fin (m + 1))) (h : S ⊆ S') (a : Tm I Y N D (d : ℤ) e t S), S.Nonempty → resT I Y N D (d : ℤ) hDm e (t + 1) h (mulT I Y N D (d : ℤ) e t S (sh e j S) a) - mulT I Y N D (d : ℤ) e t S' (sh e j S') (resT I Y N D (d : ℤ) hDm e t h a) ∈ I • (⊤ : Submodule R (Tm I Y N D (d : ℤ) e (t + 1) S')) := by
  first | exact @GlobalTheory.CompanionTheory.FormalAlg.Lift.resT_mulT_sub_mem | exact GlobalTheory.CompanionTheory.FormalAlg.Lift.resT_mulT_sub_mem | (intros; apply GlobalTheory.CompanionTheory.FormalAlg.Lift.resT_mulT_sub_mem <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsTranslateNeZero
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.LFun PositivityTheory.JacquetShalikaLocal

namespace GlobalTheory.CompanionTheory.SatakeBound

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def IsFix (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) (v : π.V) : Prop :=
  ∀ k ∈ KGL w (n := a), π.locRep w k v = v

def sphSpan (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) : Submodule ℂ (Sm E a) :=
  Submodule.span ℂ {φ | ∃ (g : GL (Fin a) (w.adicCompletion E)) (v : π.V), IsFix π w v ∧ φ = (π.locRep w g v).1}

theorem locRep_val (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin a) (w.adicCompletion E)) (v : π.V) :
    (π.locRep w g v).1 = finRep E a (locGL E a w g) v.1 := rfl

theorem mem_sphSpan (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin a) (w.adicCompletion E)) {v : π.V}
    (hv : IsFix π w v) : (π.locRep w g v).1 ∈ sphSpan π w :=
  Submodule.subset_span ⟨g, v, hv, rfl⟩

theorem isFix_op (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) (o : Op E a)
    (hc : ∀ g, act o * finRep E a (locGL E a w g) = finRep E a (locGL E a w g) * act o) {v : π.V} (hv : IsFix π w v) :
    IsFix π w (π.op o v) := fun k hk => by
  refine Subtype.ext ?_
  rw [locRep_val, CuspSub.op_val]
  have e := LinearMap.congr_fun (hc k) v.1
  simp only [Module.End.mul_apply] at e
  rw [← e, ← locRep_val, hv k hk]

theorem act_translate (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) (o : Op E a)
    (hc : ∀ g, act o * finRep E a (locGL E a w g) = finRep E a (locGL E a w g) * act o)
    (g : GL (Fin a) (w.adicCompletion E)) {v : π.V} (hv : IsFix π w v) :
    act o (π.locRep w g v).1 ∈ sphSpan π w := by
  have e := LinearMap.congr_fun (hc g) v.1
  simp only [Module.End.mul_apply] at e
  rw [locRep_val, e]
  exact mem_sphSpan π w g (isFix_op π w o hc hv)

theorem cpt_comm (y : Kinf E a) (k : GL (Fin a) (Af E)) :
    act (.cpt y : Op E a) * finRep E a k = finRep E a k * act (.cpt y : Op E a) := by
  change rt E a _ * rt E a _ = rt E a _ * rt E a _
  rw [← map_mul, ← map_mul]
  exact congrArg (rt E a) (infGL_comm _ _)

theorem lie_comm' (X : Lie E a) (k : GL (Fin a) (Af E)) :
    act (.lie X : Op E a) * finRep E a k = finRep E a k * act (.lie X : Op E a) :=
  lie_rt_fin X k

theorem fin_translate (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) (k : GL (Fin a) (Af E))
    (g : GL (Fin a) (w.adicCompletion E)) {v : π.V} (hv : IsFix π w v) :
    finRep E a k (π.locRep w g v).1 ∈ sphSpan π w := by
  obtain ⟨h, gw, e, hc⟩ := GlobalTheory.T.exists_split_adelicMatrix_localComponent E a w (finGL E a (k * locGL E a w g))
  obtain ⟨h', hh'⟩ : ∃ h' : GL (Fin a) (Af E), h' = k * locGL E a w g * (locGL E a w gw)⁻¹ := ⟨_, rfl⟩
  have hh : h = finGL E a h' := by
    rw [hh', map_mul, map_inv, e, mul_inv_cancel_right]
  have hcomm : ∀ u, finRep E a h' * finRep E a (locGL E a w u) = finRep E a (locGL E a w u) * finRep E a h' := fun u => by
    have h2 := congrArg (rt E a) (hc u)
    rw [hh, map_mul, map_mul] at h2
    exact h2
  have hfix : IsFix π w (π.op (.fin h') v) := isFix_op π w (.fin h') (fun u => hcomm u) hv
  have e2 : finRep E a k (π.locRep w g v).1 = (π.locRep w gw (π.op (.fin h') v)).1 := by
    rw [locRep_val, locRep_val, CuspSub.op_val]
    change (finRep E a k * finRep E a (locGL E a w g)) v.1 = (finRep E a (locGL E a w gw) * finRep E a h') v.1
    rw [← hcomm, ← map_mul, ← map_mul, hh', inv_mul_cancel_right]
  rw [e2]
  exact mem_sphSpan π w gw hfix

theorem isStable_sphSpan (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) : _root_.GlobalTheory.CuspRep.IsStable (sphSpan π w) := by
  intro o φ hφ
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, v, hv, rfl⟩ := hx
    cases o with
    | fin k => exact fin_translate π w k g hv
    | cpt y => exact act_translate π w _ (fun u => cpt_comm y _) g hv
    | lie X => exact act_translate π w _ (fun u => lie_comm' X _) g hv
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem sphSpan_le (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) : sphSpan π w ≤ π.V :=
  Submodule.span_le.2 fun _ ⟨g, v, _, e⟩ => e ▸ (π.locRep w g v).2

theorem exists_translate_ne_zero : G2 := by
  intro E _ _ _ a π w B hB l hl
  by_contra hcon
  push_neg at hcon
  obtain ⟨x, hx⟩ := hB.exists_vec
  have hfix : ∀ v : π.V, IsFix π w v → v ≠ 0 → IsSatVecGL w (π.locRep w) v B := fun v hv h0 =>
    hB.2 v (GlobalTheory.LGrp.mem_fixed.2 hv) h0
  have hxf : IsFix π w x := GlobalTheory.LGrp.mem_fixed.1 hx.2.1
  have hker : sphSpan π w ≤ (LinearMap.ker l).map π.V.subtype := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, v, hv, rfl⟩
    refine ⟨π.locRep w g v, ?_, rfl⟩
    by_cases h0 : v = 0
    · simp [h0]
    · exact hcon v g (hfix v hv h0)
  rcases π.irred _ (sphSpan_le π w) (isStable_sphSpan π w) with h | h
  · have h1 := mem_sphSpan π w 1 hxf
    rw [h, Submodule.mem_bot] at h1
    exact hx.1 (Subtype.ext (by simpa using h1))
  · refine hl (LinearMap.ext fun u => ?_)
    have h1 : u.1 ∈ sphSpan π w := by rw [h]; exact u.2
    obtain ⟨y, hy, e⟩ := hker h1
    rw [LinearMap.zero_apply, ← Subtype.ext (a1 := y) (a2 := u) e]
    exact hy

end GlobalTheory.CompanionTheory.SatakeBound

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousIdealLeThickening
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.GE

variable {R : Type} [CommRing R] {N : ℕ}

theorem exists_eq_formOn (k : Fin (N + 1)) (s : Γ(PSpace R N, GlobalTheory.ProjSpace.chart R N k)) :
    ∃ (n : ℕ) (a : MvPolynomial (Fin (N + 1)) R) (ha : a.IsHomogeneous n),
      s = GlobalTheory.ProjSpace.formOn (GlobalTheory.ProjSpace.chart R N k) k le_rfl n a ha := by
  obtain ⟨x, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    (Proj.basicOpenIsoAway (GlobalTheory.ProjSpace.grading R N) (X k) (GlobalTheory.ProjSpace.X_mem R N k) one_pos).hom).2 s
  obtain ⟨n, f, hf, rfl⟩ := HomogeneousLocalization.Away.mk_surjective _ (GlobalTheory.ProjSpace.X_mem R N k) x
  have hf' : f.IsHomogeneous n := by simpa using hf
  refine ⟨n, f, hf', ?_⟩
  exact (GlobalTheory.ProjFrac.awayToSection_mk _ _ _).trans (GlobalTheory.ProjFrac.frac_eq rfl)

theorem homogeneousComponent_mem_map_C {K : Ideal R} {d : ℕ} {v : MvPolynomial (Fin (N + 1)) R}
    (hv : v ∈ K.map (C : R →+* MvPolynomial (Fin (N + 1)) R)) :
    homogeneousComponent d v ∈ K.map (C : R →+* MvPolynomial (Fin (N + 1)) R) := by
  rw [mem_map_C_iff] at hv ⊢
  intro m
  rw [coeff_homogeneousComponent]
  split_ifs
  · exact hv m
  · exact zero_mem _

def homogOf (J : Ideal (MvPolynomial (Fin (N + 1)) R)) (hJ : HomogIdeal J) :
    HomogeneousIdeal (GlobalTheory.ProjSpace.grading R N) :=
  ⟨J, fun d f hf => by
    have := hJ d f hf
    rwa [← decomposition.decompose'_apply f d] at this⟩

theorem ker_le_sup_chart {Y : Scheme.{0}} (I : Ideal R) (e : ℕ)
    (J : Ideal (MvPolynomial (Fin (N + 1)) R)) (hJ : HomogIdeal J)
    (φ : Y ⟶ PSpace R N) [QuasiCompact φ]
    (hge : ∀ f ∈ vanIdeal φ, ∀ k, ∃ m : ℕ, X k ^ m * f ∈
      J ⊔ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R))
    (k : Fin (N + 1)) :
    (Scheme.Hom.ker φ).ideal ⟨GlobalTheory.ProjSpace.chart R N k, GlobalTheory.ProjSpace.isAffineOpen_chart R N k⟩ ≤
      (Scheme.Hom.ker (GlobalTheory.ProjSpace.vPlusι (homogOf J hJ))).ideal
          ⟨GlobalTheory.ProjSpace.chart R N k, GlobalTheory.ProjSpace.isAffineOpen_chart R N k⟩ ⊔
        (Scheme.Hom.ker (thickι R I N e)).ideal
          ⟨GlobalTheory.ProjSpace.chart R N k, GlobalTheory.ProjSpace.isAffineOpen_chart R N k⟩ := by
  intro s hs
  obtain ⟨n, a, ha, rfl⟩ := exists_eq_formOn k s
  rw [Scheme.Hom.ker_apply] at hs
  obtain ⟨m, h, hK⟩ := GlobalTheory.T.chart_vanishing_kills_form_mul_pow φ n a ha k hs
  obtain ⟨m', hm'⟩ := hge _ ((GlobalTheory.T.mem_vanishing_ideal_iff_kills_form φ _ _ h).2 hK) k
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 hm'
  have hb : (X k ^ m' * (X k ^ m * a) : MvPolynomial (Fin (N + 1)) R).IsHomogeneous (m' + (m + n)) :=
    (isHomogeneous_X_pow k m').mul h
  have hcu := homogeneousComponent_isHomogeneous (m' + (m + n)) u
  have hcv := homogeneousComponent_isHomogeneous (m' + (m + n)) v
  have hsum : homogeneousComponent (m' + (m + n)) u + homogeneousComponent (m' + (m + n)) v =
      X k ^ m' * (X k ^ m * a) := by
    rw [← map_add (f := _), huv, homogeneousComponent_of_mem hb, if_pos rfl]
  have e1 : GlobalTheory.ProjSpace.formOn (GlobalTheory.ProjSpace.chart R N k) k le_rfl n a ha =
      GlobalTheory.ProjSpace.formOn (GlobalTheory.ProjSpace.chart R N k) k le_rfl (m' + (m + n)) _ (hcu.add hcv) :=
    GlobalTheory.ProjFrac.frac_eq (by rw [hsum]; ring)
  rw [e1, GlobalTheory.ProjSpace.formOn_add hcu hcv]
  refine Submodule.add_mem_sup ?_ ?_
  · rw [Scheme.Hom.ker_apply]
    exact (GlobalTheory.ProjSpace.vPlusι_app_formOn_eq_zero_iff (homogOf J hJ) k hcu).2
      ⟨0, by rw [pow_zero, one_mul]; exact hJ _ _ hu⟩
  · exact (GlobalTheory.T.thickening_section_homogeneous_form I N e k).2 _ _ hcv (homogeneousComponent_mem_map_C hv)

instance isClosedImmersion_thickι (I : Ideal R) (e : ℕ) : IsClosedImmersion (thickι R I N e) := by
  have : IsClosedImmersion (thick R I e) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  infer_instance

theorem thickMap_thickι (I : Ideal R) (e : ℕ) :
    thickMap R I e (PO R N) ≫ thickι R I N (e + 1) = thickι R I N e :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

theorem exists_closed_of_homogIdeal : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (N : ℕ)
    (Cs : ℕ → Scheme.{0}) (i : ∀ e, Cs e ⟶ (thickObj R I e (PO R N)).left)
    (β : ∀ e, Cs e ⟶ Cs (e + 1)),
    (∀ e, IsClosedImmersion (i e)) →
    (∀ e, IsPullback (β e) (i e) (i (e + 1)) (thickMap R I e (PO R N))) →
    ∀ (J : Ideal (MvPolynomial (Fin (N + 1)) R)), HomogIdeal J →
    (∀ e, J ≤ vanIdeal (i e ≫ thickι R I N e)) →
    (∀ e, ∀ f ∈ vanIdeal (i e ≫ thickι R I N e), ∀ k, ∃ m : ℕ, X k ^ m * f ∈
      J ⊔ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R)) →
    ∃ (C' : Scheme.{0}) (j : C' ⟶ (PO R N).left) (b : ∀ e, Cs e ⟶ C'),
      IsClosedImmersion j ∧
      (∀ e, IsPullback (b e) (i e) j (pullback.fst (PO R N).hom (thick R I e))) ∧
      ∀ e, β e ≫ b (e + 1) = b e := by
  intro R _ _ I N Cs i β hi hsq J hJ hle hge
  have hcl : ∀ e, IsClosedImmersion (i e ≫ thickι R I N e) := fun e => by
    have := hi e
    infer_instance
  have hfac : ∀ e, ∃ ψ : Cs e ⟶ GlobalTheory.ProjSpace.VPlus (homogOf J hJ),
      ψ ≫ GlobalTheory.ProjSpace.vPlusι (homogOf J hJ) = i e ≫ thickι R I N e := fun e =>
    (GlobalTheory.ProjSpace.exists_comp_vPlusι_iff (homogOf J hJ) _).2 fun k n f hf hfJ =>
      (GlobalTheory.T.mem_vanishing_ideal_iff_kills_form _ n f hf).1 (hle e hfJ) k
  choose b hb using hfac
  refine ⟨GlobalTheory.ProjSpace.VPlus (homogOf J hJ), GlobalTheory.ProjSpace.vPlusι (homogOf J hJ), b, inferInstance,
    fun e => ?_, fun e => ?_⟩
  · have hc : IsClosedImmersion (b e ≫ GlobalTheory.ProjSpace.vPlusι (homogOf J hJ)) := by
      rw [hb]
      exact hcl e
    refine GlobalTheory.T.is_pullback_of_kernel_sup _ _ _ _ (hb e) ?_
    rw [hb]
    have := hcl e
    have h1 : Scheme.Hom.ker (GlobalTheory.ProjSpace.vPlusι (homogOf J hJ)) ≤
        Scheme.Hom.ker (i e ≫ thickι R I N e) := by
      rw [← hb e]
      exact Scheme.Hom.le_ker_comp _ _
    have h2 : Scheme.Hom.ker (thickι R I N e) ≤ Scheme.Hom.ker (i e ≫ thickι R I N e) :=
      Scheme.Hom.le_ker_comp _ _
    refine Scheme.IdealSheafData.ext_of_iSup_eq_top
      (fun k => ⟨GlobalTheory.ProjSpace.chart R N k, GlobalTheory.ProjSpace.isAffineOpen_chart R N k⟩)
      (GlobalTheory.ProjSpace.iSup_chart R N) fun k => le_antisymm ?_ ?_
    · exact ker_le_sup_chart I e J hJ _ (hge e) k
    · exact (Scheme.IdealSheafData.le_def.1 (sup_le h1 h2)) _
  · refine (cancel_mono (GlobalTheory.ProjSpace.vPlusι (homogOf J hJ))).1 ?_
    rw [Category.assoc, hb, hb, ← Category.assoc, (hsq e).w, Category.assoc, thickMap_thickι]

end GlobalTheory.CompanionTheory.GE
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalLiftProjectiveEmbeddingCompatible
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalLiftProjectiveEmbeddingCompatible
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

variable {X X' : Scheme.{0}}

theorem pullLE_ofSec {M : LB X} (π : X' ⟶ X) (V : X.Opens) (V' : X'.Opens) (e : V' ≤ π ⁻¹ᵁ V)
    (s : LB.Sec M) :
    SecOn.pullLE M π V V' e (GlobalTheory.LB.ofSec s V) = GlobalTheory.LB.ofSec (secPull s π) V' := by
  refine GlobalTheory.LB.sec_ext fun j => ?_
  rw [SecOn.coord_pullLE, GlobalTheory.LB.coord_ofSec, GlobalTheory.LB.coord_ofSec, GlobalTheory.LB.appLE_resG]
  change _ = resG X' _ ((π.appLE _ _ (GlobalTheory.LB.pull_U_le π j)).hom (s.f (j PUnit.unit)))
  rw [GlobalTheory.LB.resG_appLE]

theorem secMaps_of_cover {A B : LB X} (hA : A.IsLB) (hB : B.IsLB) (w : LB.Iso A B) (hw : w.IsGen)
    {κ : Type} (O : κ → X.Opens) (hO : ⨆ a, O a = ⊤) (s : LB.Sec A) (t : LB.Sec B)
    (h : ∀ a, SecOn.congr hA hB w hw (O a) (GlobalTheory.LB.ofSec s (O a)) = GlobalTheory.LB.ofSec t (O a)) :
    SecMaps w s t := by
  rintro ⟨p, q⟩
  refine ext_germ fun x hx => ?_
  obtain ⟨a, ha⟩ : ∃ a, x ∈ O a := by
    have hx' : x ∈ (⨆ a, O a) := by rw [hO]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 hx'
  have hp : O a ⊓ (B.U p ⊓ A.U q) ≤ O a ⊓ B.U p := inf_le_inf_left _ inf_le_left
  have hq : O a ⊓ (B.U p ⊓ A.U q) ≤ O a ⊓ A.U q := inf_le_inf_left _ inf_le_right
  have hh : O a ⊓ (B.U p ⊓ A.U q) ≤ B.U p ⊓ A.U q := inf_le_right
  have e := SecOn.coord_congr hA hB w hw (GlobalTheory.LB.ofSec s (O a)) p q hp hq hh
  rw [h a, GlobalTheory.LB.coord_ofSec, GlobalTheory.LB.coord_ofSec] at e
  have hxW : x ∈ O a ⊓ (B.U p ⊓ A.U q) := ⟨ha, hx⟩
  change resG X hp (resG X _ (t.f p)) = resG X hh _ * resG X hq (resG X _ (s.f q)) at e
  rw [resG_resG, resG_resG] at e
  refine (germ_resG hh x hxW _).symm.trans ((congrArg _ ?_).trans (germ_resG hh x hxW _))
  rw [map_mul, resG_resG, resG_resG]
  exact e

section Tower

variable {R : Type} [CommRing R] (I : Ideal R)
  (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
  (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left)
  (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e))
  (L : ∀ e, LB (Y e).left) (w : ∀ e, LB.Iso (L e) ((L (e + 1)).pull (β e)))
  (hL : ∀ e, (L e).IsLB ∧ (w e).IsGen)


include hL in
theorem congr_ofSec_of_redL (e : ℕ) (V : (Y (e + 1)).left.Opens) (V' : (Y e).left.Opens)
    (h : V' ≤ β e ⁻¹ᵁ V) (τ : LB.Sec (L (e + 1))) (σ : LB.Sec (L e))
    (hr : redL I Y β hβ L w hL e V V' h (SecOnR.of _ _ _ (GlobalTheory.LB.ofSec τ V)) =
      SecOnR.of _ _ _ (GlobalTheory.LB.ofSec σ V')) :
    SecOn.congr (hL e).1 (LB.isLB_pull (hL (e + 1)).1 (β e)) (w e) (hL e).2 V'
      (GlobalTheory.LB.ofSec σ V') = GlobalTheory.LB.ofSec (secPull τ (β e)) V' := by
  have h1 := (LinearEquiv.symm_apply_eq _).1 hr
  rw [SecOnR.pull_of, SecOnR.linEquiv_of] at h1
  exact h1.symm.trans (pullLE_ofSec (β e) V V' h τ)

end Tower

theorem lift_of_cech_pairs : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))) (hN : ∀ e, (N e).IsLB ∧ (v e).IsGen) (d : ℕ) (m : ℕ) (s : Fin (m + 1) → LB.Sec (pw (N 0) (d : ℤ))) (hs : VeryAmpleBy (Y 0).hom (pw (N 0) (d : ℤ)) s) (D : ∀ e, Finset (Fin (m + 1)) → (Y e).left.Opens) (hD0 : ∀ S, D 0 S = ⨅ i ∈ S, nonzeroLocus (s i)) (hDβ : ∀ e S, β e ⁻¹ᵁ D (e + 1) S = D e S) (hDm : ∀ e (S S' : Finset (Fin (m + 1))), S ⊆ S' → D e S' ≤ D e S) (hDi : ∀ e S j, D e (insert j S) = D e S ⊓ D e {j}) (hDc : ∀ e, ⨆ i, D e {i} = ⊤) (hDa : ∀ e S, S.Nonempty → IsAffineOpen (D e S)) (t : ℤ) (e : ℕ), (∀ (c : ∀ i j : Fin (m + 1), Tm I Y N D (d : ℤ) (e + 1) t {i, j}), (∀ i j, red I Y N D β hβ v hN (fun e S => (hDβ e S).ge) ((d : ℤ) * t) e {i, j} (c i j) = 0) → (∀ i j k, resT I Y N D (d : ℤ) hDm (e + 1) t (sub_triple_ij i j k) (c i j) + resT I Y N D (d : ℤ) hDm (e + 1) t (sub_triple_jk i j k) (c j k) = resT I Y N D (d : ℤ) hDm (e + 1) t (sub_triple_ik i j k) (c i k)) → ∃ b : ∀ i, Tm I Y N D (d : ℤ) (e + 1) t {i}, (∀ i, red I Y N D β hβ v hN (fun e S => (hDβ e S).ge) ((d : ℤ) * t) e {i} (b i) = 0) ∧ ∀ i j, c i j = resT I Y N D (d : ℤ) hDm (e + 1) t (sub_pair_left i j) (b i) - resT I Y N D (d : ℤ) hDm (e + 1) t (sub_pair_right i j) (b j)) → ∀ σ : LB.Sec (pw (N e) ((d : ℤ) * t)), ∃ σ' : LB.Sec (pw (N (e + 1)) ((d : ℤ) * t)), SecMaps (pullPow (v e) ((d : ℤ) * t)) σ (GlobalTheory.secPull σ' (β e)) := by
  intro R _ I Y β hβ N v hN d m s hs D hD0 hDβ hDm hDi hDc hDa t e hc σ
  have hLp : ∀ e, (pw (N e) ((d : ℤ) * t)).IsLB ∧ (pullPow (v e) ((d : ℤ) * t)).IsGen :=
    fun e => ⟨isLB_pw (hN e).1 _, pullPow_isGen (v e) _ (hN e).2⟩

  have hres : ∀ (S S' : Finset (Fin (m + 1))) (h : S ⊆ S') (x : Tm I Y N D (d : ℤ) (e + 1) t S),
      red I Y N D β hβ v hN (fun e S => (hDβ e S).ge) ((d : ℤ) * t) e S'
          (resT I Y N D (d : ℤ) hDm (e + 1) t h x) =
        resT I Y N D (d : ℤ) hDm e t h
          (red I Y N D β hβ v hN (fun e S => (hDβ e S).ge) ((d : ℤ) * t) e S x) :=
    fun S S' h x => GlobalTheory.T.thickening_restriction_compatible_opens R I Y β hβ (fun e => pw (N e) ((d : ℤ) * t))
      (fun e => pullPow (v e) ((d : ℤ) * t)) hLp e (D (e + 1) S) (D (e + 1) S') (D e S) (D e S')
      (hDβ e S).ge (hDβ e S').ge (hDm (e + 1) S S' h) (hDm e S S' h) x
  have hrr : ∀ (e : ℕ) (S S' S'' : Finset (Fin (m + 1))) (h : S ⊆ S') (h' : S' ⊆ S'')
      (x : Tm I Y N D (d : ℤ) e t S),
      resT I Y N D (d : ℤ) hDm e t h' (resT I Y N D (d : ℤ) hDm e t h x) =
        resT I Y N D (d : ℤ) hDm e t (h.trans h') x :=
    fun e S S' S'' h h' x => SecOnR.restrict_restrict _ _ _ x

  let σS : ∀ S, Tm I Y N D (d : ℤ) e t S := fun S => SecOnR.of _ _ _ (GlobalTheory.LB.ofSec σ (D e S))
  have hσS : ∀ (S S' : Finset (Fin (m + 1))) (h : S ⊆ S'),
      resT I Y N D (d : ℤ) hDm e t h (σS S) = σS S' :=
    fun S S' h => SecOn.restrict_ofSec σ (hDm e S S' h)

  have hlift : ∀ i, ∃ b : Tm I Y N D (d : ℤ) (e + 1) t {i},
      red I Y N D β hβ v hN (fun e S => (hDβ e S).ge) ((d : ℤ) * t) e {i} b = σS {i} :=
    fun i => (GlobalTheory.T.thickening_affine_preimage R I Y β hβ (fun e => pw (N e) ((d : ℤ) * t))
      (fun e => pullPow (v e) ((d : ℤ) * t)) hLp e (D (e + 1) {i}) (D e {i}) (hDβ e {i})
      (hDa (e + 1) {i} (Finset.singleton_nonempty i))).1 (σS {i})
  choose b hb using hlift
  obtain ⟨b', hb'0, hb'c⟩ := hc
    (fun i j => resT I Y N D (d : ℤ) hDm (e + 1) t (sub_pair_left i j) (b i) -
      resT I Y N D (d : ℤ) hDm (e + 1) t (sub_pair_right i j) (b j))
    (fun i j => by
      rw [map_sub, hres, hres, hb, hb, hσS, hσS, sub_self])
    (fun i j k => by
      simp only [map_sub, hrr]
      abel)

  have hf : ∀ i j, resT I Y N D (d : ℤ) hDm (e + 1) t (sub_pair_left i j) (b i - b' i) =
      resT I Y N D (d : ℤ) hDm (e + 1) t (sub_pair_right i j) (b j - b' j) := fun i j => by
    rw [map_sub, map_sub]
    exact sub_eq_sub_iff_sub_eq_sub.1 (hb'c i j)
  have hfr : ∀ i, red I Y N D β hβ v hN (fun e S => (hDβ e S).ge) ((d : ℤ) * t) e {i}
      (b i - b' i) = σS {i} := fun i => by rw [map_sub, hb, hb'0, sub_zero]

  obtain ⟨τ, hτ, -⟩ := SecOnR.existsUnique_glue (toR I Y (e + 1)) (M := pw (N (e + 1)) ((d : ℤ) * t))
    (V := ⊤) (fun i => D (e + 1) {i}) (fun _ => le_top) (hDc (e + 1)).ge (fun i => b i - b' i)
    (fun i j => by
      have hij : D (e + 1) {i} ⊓ D (e + 1) {j} ≤ D (e + 1) {i, j} := by
        rw [show ({i, j} : Finset (Fin (m + 1))) = insert i {j} from rfl, hDi (e + 1) {j} i,
          inf_comm]
      have h1 := congrArg (SecOnR.restrict (toR I Y (e + 1)) (pw (N (e + 1)) ((d : ℤ) * t)) hij)
        (hf i j)
      exact (SecOnR.restrict_restrict _ _ _ _).symm.trans
        (h1.trans (SecOnR.restrict_restrict _ _ _ _)))
  let σ' : LB.Sec (pw (N (e + 1)) ((d : ℤ) * t)) := SecOnR.topEquiv _ _ τ
  have hτσ : τ = SecOnR.of _ _ _ (GlobalTheory.LB.ofSec σ' ⊤) :=
    ((SecOn.topEquiv (pw (N (e + 1)) ((d : ℤ) * t))).symm_apply_apply τ).symm
  refine ⟨σ', secMaps_of_cover (hLp e).1 (LB.isLB_pull (hLp (e + 1)).1 (β e)) _ (hLp e).2
    (fun i => D e {i}) (hDc e) σ (secPull σ' (β e)) fun i => ?_⟩
  refine congr_ofSec_of_redL I Y β hβ (fun e => pw (N e) ((d : ℤ) * t))
    (fun e => pullPow (v e) ((d : ℤ) * t)) hLp e (D (e + 1) {i}) (D e {i}) (hDβ e {i}).ge σ' σ ?_
  have h2 : SecOnR.of (toR I Y (e + 1)) _ _ (GlobalTheory.LB.ofSec σ' (D (e + 1) {i})) = b i - b' i := by
    rw [← hτ i, hτσ]
    exact (SecOn.restrict_ofSec σ' le_top).symm
  rw [h2]
  exact hfr i

end GlobalTheory.CompanionTheory.FormalAlg.Lift
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalLiftProjectiveEmbeddingCompatibleStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_lift_projective_embedding_compatible : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))) (hN : ∀ e, (N e).IsLB ∧ (v e).IsGen) (d : ℕ) (m : ℕ) (s : Fin (m + 1) → LB.Sec (pw (N 0) (d : ℤ))) (hs : VeryAmpleBy (Y 0).hom (pw (N 0) (d : ℤ)) s) (D : ∀ e, Finset (Fin (m + 1)) → (Y e).left.Opens) (hD0 : ∀ S, D 0 S = ⨅ i ∈ S, nonzeroLocus (s i)) (hDβ : ∀ e S, β e ⁻¹ᵁ D (e + 1) S = D e S) (hDm : ∀ e (S S' : Finset (Fin (m + 1))), S ⊆ S' → D e S' ≤ D e S) (hDi : ∀ e S j, D e (insert j S) = D e S ⊓ D e {j}) (hDc : ∀ e, ⨆ i, D e {i} = ⊤) (hDa : ∀ e S, S.Nonempty → IsAffineOpen (D e S)) (t : ℤ) (e : ℕ), (∀ (c : ∀ i j : Fin (m + 1), Tm I Y N D (d : ℤ) (e + 1) t {i, j}), (∀ i j, red I Y N D β hβ v hN (fun e S => (hDβ e S).ge) ((d : ℤ) * t) e {i, j} (c i j) = 0) → (∀ i j k, resT I Y N D (d : ℤ) hDm (e + 1) t (sub_triple_ij i j k) (c i j) + resT I Y N D (d : ℤ) hDm (e + 1) t (sub_triple_jk i j k) (c j k) = resT I Y N D (d : ℤ) hDm (e + 1) t (sub_triple_ik i j k) (c i k)) → ∃ b : ∀ i, Tm I Y N D (d : ℤ) (e + 1) t {i}, (∀ i, red I Y N D β hβ v hN (fun e S => (hDβ e S).ge) ((d : ℤ) * t) e {i} (b i) = 0) ∧ ∀ i j, c i j = resT I Y N D (d : ℤ) hDm (e + 1) t (sub_pair_left i j) (b i) - resT I Y N D (d : ℤ) hDm (e + 1) t (sub_pair_right i j) (b j)) → ∀ σ : LB.Sec (pw (N e) ((d : ℤ) * t)), ∃ σ' : LB.Sec (pw (N (e + 1)) ((d : ℤ) * t)), SecMaps (pullPow (v e) ((d : ℤ) * t)) σ (GlobalTheory.secPull σ' (β e)) := by
  first | exact @GlobalTheory.CompanionTheory.FormalAlg.Lift.lift_of_cech_pairs | exact GlobalTheory.CompanionTheory.FormalAlg.Lift.lift_of_cech_pairs | (intros; apply GlobalTheory.CompanionTheory.FormalAlg.Lift.lift_of_cech_pairs <;> assumption)
end
end
