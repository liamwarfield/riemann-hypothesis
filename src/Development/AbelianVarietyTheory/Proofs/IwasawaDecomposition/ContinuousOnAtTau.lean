module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.AtPlaceIffEqAtTau
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteClassSetHermitianUnitaryOpenLevel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCovolumeLatticeStabiliserUnitaryRealPoints
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocallyCompactSecondCountableT2
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrincipalIdealSt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PointAtPlaceHom

open GlobalTheory.PointAtPlace

variable {D : D7} {θ : InfF D}

theorem infMat_mul (V : HSp D) (φ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (a b : GA D V) :
    infMat D.sp.cm.sig V.gram φ (a * b) = infMat D.sp.cm.sig V.gram φ a * infMat D.sp.cm.sig V.gram φ b :=
  archM_mul V φ a b

theorem infMat_one (V : HSp D) (φ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) :
    infMat D.sp.cm.sig V.gram φ 1 = 1 := archM_one V φ

theorem atTau_spec (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) : IsAtTau θ V τ g (atTau θ V τ g) := by
  have hu := existsUnique_isAtTau V τ θ hθ g hg
  unfold atTau
  rw [dite_eq_left hu.exists]
  exact hu.exists.choose_spec

theorem atTau_mem (V : HSp D) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    atTau θ V τ g ∈ GinfC V := by
  unfold atTau
  split_ifs with h
  · exact h.choose_spec.1
  · exact one_mem _

theorem one_mem_UH {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Formalism.QuantumDeterminants.UH H := by
  show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * H * 1 = H
  simp

theorem mul_mem_UH {n : ℕ} {H g g' : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH H)
    (hg' : g' ∈ Formalism.QuantumDeterminants.UH H) : g * g' ∈ Formalism.QuantumDeterminants.UH H := by
  have h1 : gᴴ * H * g = H := hg
  have h2 : g'ᴴ * H * g' = H := hg'
  show (g * g')ᴴ * H * (g * g') = H
  calc (g * g')ᴴ * H * (g * g') = g'ᴴ * (gᴴ * H * g) * g' := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = H := by rw [h1, h2]

theorem atTau_one (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau) : atTau θ V τ 1 = 1 :=
  (existsUnique_isAtTau V τ θ hθ 1 (one_mem_UH _)).unique (atTau_spec hθ V τ (one_mem_UH _))
    ⟨one_mem _, infMat_one V _, fun _ _ => infMat_one V _⟩

theorem atTau_mul (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau) {g g' : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (hg' : g' ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) :
    atTau θ V τ (g * g') = atTau θ V τ g * atTau θ V τ g' := by
  have a := atTau_spec hθ V τ hg
  have b := atTau_spec hθ V τ hg'
  refine (existsUnique_isAtTau V τ θ hθ _ (mul_mem_UH hg hg')).unique (atTau_spec hθ V τ (mul_mem_UH hg hg'))
    ⟨mul_mem a.1 b.1, ?_, fun τ' h => ?_⟩
  · rw [infMat_mul, a.2.1, b.2.1]
  · rw [infMat_mul, a.2.2 τ' h, b.2.2 τ' h, Matrix.one_mul]

theorem comm_of_mem (V : HSp D) {a k : GA D V} (ha : a ∈ GinfC V) (hk : k ∈ GfC V) : a * k = k * a := by
  have a2 : finHom V a = 1 := ha
  have k1 : infHom V k = 1 := hk
  refine mul_inv_eq_one.1 (eq_one_of_mem V _ ?_ ?_)
  · show infHom V _ = 1
    simp only [map_mul, map_inv, k1, mul_one, one_mul, mul_inv_cancel]
  · show finHom V _ = 1
    simp only [map_mul, map_inv, a2, mul_one, one_mul, mul_inv_cancel]


open Classical in
theorem entry_eq {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) (V : HSp D) (τ : D.what₂.Tau)
    {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} {h : GA D V} (hh : IsAtTau θ V τ g h) (i j : Fin V.rank) :
    (matHom V h).1 i j = (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j +
      σ (Pi.single τ (g i j - (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) i j)) := by
  refine sub_eq_zero.1 (hσ.ext _ ?_ fun τ' => ?_)
  · have a2 : (finHom V h).1 = (finHom V 1).1 := by rw [map_one]; exact congrArg Units.val hh.1
    have e : finPart D ((matHom V h).1 i j) = finPart D ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) :=
      congrFun (congrFun a2 i) j
    rw [RingHom.map_sub, RingHom.map_add (f := _), hσ.fin, e, add_zero, sub_self]
  · have e1 : θ τ' (infPart D ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j)) =
        (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) i j := congrFun (congrFun (infMat_one V (θ τ')) i) j
    have e2 : θ τ' (infPart D ((matHom V h).1 i j)) = infMat D.sp.cm.sig V.gram (θ τ') h i j := rfl
    rw [RingHom.map_sub, RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_add (f := _), hσ.comp, e1, e2]
    by_cases c : τ' = τ
    · subst c
      rw [hh.2.1, Pi.single_eq_same]; ring
    · rw [hh.2.2 τ' c, Pi.single_eq_of_ne c]; ring

theorem isAtTau_inv (V : HSp D) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) {h : GA D V} (hh : IsAtTau θ V τ g h) :
    IsAtTau θ V τ ((gramAt D V τ)⁻¹ * gᴴ * gramAt D V τ) h⁻¹ := by
  have hu : IsUnit (gramAt D V τ).det := by
    have : (gramAt D V τ).det = tauE D τ V.gram.det := (RingHom.map_det (tauE D τ) V.gram).symm
    rw [this]
    exact ((_root_.map_ne_zero _).2 (Formalism.L2.Theta.gram_det_ne V)).isUnit
  have h1 : gᴴ * gramAt D V τ * g = gramAt D V τ := hg
  have h2 : (gramAt D V τ)⁻¹ * gᴴ * gramAt D V τ * g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, h1, Matrix.nonsing_inv_mul _ hu]
  have k : ∀ φ, infMat D.sp.cm.sig V.gram φ h * infMat D.sp.cm.sig V.gram φ h⁻¹ = 1 := fun φ => by
    rw [← infMat_mul, mul_inv_cancel, infMat_one]
  refine ⟨inv_mem hh.1, ?_, fun τ' c => ?_⟩
  · have := k (θ τ)
    rw [hh.2.1] at this
    rw [← Matrix.one_mul (infMat _ _ _ h⁻¹), ← h2, Matrix.mul_assoc _ g, this, Matrix.mul_one]
  · have := k (θ τ')
    rwa [hh.2.2 τ' c, Matrix.one_mul] at this

theorem continuousOn_atTau (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau) :
    ContinuousOn (atTau θ V τ) (Formalism.QuantumDeterminants.UH (gramAt D V τ)) := by
  classical
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : ContinuousAdd (AE D) := IsModuleTopology.toContinuousAdd (AF D.host.F) _
  have key : ∀ (i j : Fin V.rank), Continuous fun g : Matrix (Fin V.rank) (Fin V.rank) ℂ =>
      (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j +
        σ (Pi.single τ (g i j - (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) i j)) := fun i j =>
    continuous_const.add (hσ.cont.comp ((continuous_single (A := fun _ : D.what₂.Tau => ℂ) τ).comp
      ((continuous_id.matrix_elem i j).sub continuous_const)))
  rw [continuousOn_iff_continuous_restrict]
  refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    refine ((key i j).comp continuous_subtype_val).congr fun g => ?_
    exact (entry_eq hσ V τ (atTau_spec hθ V τ g.2) i j).symm
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    have c : Continuous fun g : Formalism.QuantumDeterminants.UH (gramAt D V τ) => (gramAt D V τ)⁻¹ * g.1ᴴ * gramAt D V τ :=
      (continuous_const.matrix_mul continuous_subtype_val.matrix_conjTranspose).matrix_mul continuous_const
    refine ((key i j).comp c).congr fun g => ?_
    exact (entry_eq hσ V τ (isAtTau_inv V τ g.2 (atTau_spec hθ V τ g.2)) i j).symm

theorem atTau_laws : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D) (τ : D.what₂.Tau), (∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∃! h, IsAtTau θ V τ g h) ∧ atTau θ V τ 1 = 1 ∧ (∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ g' ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), atTau θ V τ (g * g') = atTau θ V τ g * atTau θ V τ g') ∧ (∀ g, ∀ k ∈ GfC V, atTau θ V τ g * k = k * atTau θ V τ g) ∧ ContinuousOn (atTau θ V τ) (Formalism.QuantumDeterminants.UH (gramAt D V τ)) :=
  fun _ θ hθ V τ => ⟨fun g hg => existsUnique_isAtTau V τ θ hθ g hg, atTau_one hθ V τ,
    fun _ hg _ hg' => atTau_mul hθ V τ hg hg', fun g _ hk => comm_of_mem V (atTau_mem V τ g) hk,
    continuousOn_atTau hθ V τ⟩

end GlobalTheory.PointAtPlaceHom

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.AdelicGroupTop

theorem isTopologicalGroup_HA {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : IsTopologicalGroup (HA (AF F) σ J) := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := F) (E := E)
  exact inferInstanceAs (IsTopologicalGroup (HR (AF F) σ J))

theorem adelic_unitary_topology : ∀ (D : D7) (V : HSp D), LocallyCompactSpace (GA D V) ∧ SecondCountableTopology (GA D V) ∧ T2Space (GA D V) ∧ BorelSpace (GA D V) ∧ IsTopologicalGroup (GA D V) ∧ DiscreteTopology (GQ V) ∧ Countable (GQ V) := by
  intro D V
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary D.host.F D.host.E D.sp.cm.sig V.rank V.gram
  have hd : DiscreteTopology (GQ V) := GlobalTheory.RationalDiscrete.discreteTopology_GQ D V
  have h2' : SecondCountableTopology (GA D V) := h2
  exact ⟨h1, h2, h3, ⟨rfl⟩, isTopologicalGroup_HA D.sp.cm.sig V.gram, hd,
    TopologicalSpace.separableSpace_iff_countable.1 inferInstance⟩

end GlobalTheory.Mem.AdelicGroupTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.AutSpace

variable {D : D7} (θ : InfF D) (V : HSp D)

def SmFun : Submodule ℂ (GA D V → ℂ) where
  carrier := {φ | ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ),
    (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g,
      ContDiff ℝ ∞ fun t : Fin k → ℝ => φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod)}
  add_mem' := fun ha hb k τs Xs h g => (ha k τs Xs h g).add (hb k τs Xs h g)
  zero_mem' := fun _ _ _ _ _ => contDiff_const
  smul_mem' := fun c _ ha k τs Xs h g => (ha k τs Xs h g).const_smul c

variable {θ V}

theorem differentiable_oneP {φ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) {τ : D.what₂.Tau}
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) (g : GA D V) :
    Differentiable ℝ fun t : ℝ => φ (g * oneP θ V τ X t) := by
  have h := hφ 1 (fun _ => τ) (fun _ => X) (fun _ => hX) g
  have h2 : ContDiff ℝ ∞ fun t : ℝ => (fun _ : Fin 1 => t) := contDiff_pi.2 fun _ => contDiff_id
  have h3 := (h.comp h2).differentiable (by simp)
  simpa [Function.comp_def] using h3

theorem Rder_add {φ ψ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) (hψ : ψ ∈ SmFun θ V) {τ : D.what₂.Tau}
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) :
    Rder θ V τ X (φ + ψ) = Rder θ V τ X φ + Rder θ V τ X ψ := by
  funext g
  exact deriv_fun_add (differentiable_oneP hφ hX g 0) (differentiable_oneP hψ hX g 0)

theorem Rder_smul (c : ℂ) (φ : GA D V → ℂ) (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    Rder θ V τ X (c • φ) = c • Rder θ V τ X φ := by
  funext g
  exact deriv_const_mul_field c

theorem Rder_mem {φ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) {τ : D.what₂.Tau}
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) : Rder θ V τ X φ ∈ SmFun θ V := by
  intro k τs Xs h g
  have h1 := hφ (k + 1) (Fin.snoc (α := fun _ => D.what₂.Tau) τs τ)
    (Fin.snoc (α := fun _ => Matrix (Fin V.rank) (Fin V.rank) ℂ) Xs X)
    (fun i => by
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hX
      · simpa using h j) g
  have h2 : ContDiff ℝ ∞ fun p : (Fin k → ℝ) × ℝ => (Fin.snoc (α := fun _ => ℝ) p.1 p.2 : Fin (k + 1) → ℝ) := by
    refine contDiff_pi.2 fun i => ?_
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using contDiff_snd
    · simp only [Fin.snoc_castSucc]
      fun_prop
  have h3 : ContDiff ℝ ∞ (Function.uncurry fun (t : Fin k → ℝ) (s : ℝ) =>
      φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod * oneP θ V τ X s)) := by
    convert h1.comp h2 using 1
    funext p
    simp [Function.uncurry, List.ofFn_succ', mul_assoc, -List.ofFn_succ]
  have h4 := ContDiff.fderiv (n := ∞) h3 (contDiff_const (c := (0 : ℝ))) (by simp)
  exact h4.clm_apply (contDiff_const (c := (1 : ℝ)))


variable (θ V) in
structure LinOnSm (T : (GA D V → ℂ) → (GA D V → ℂ)) : Prop where
  mem : ∀ φ ∈ SmFun θ V, T φ ∈ SmFun θ V
  add : ∀ φ ∈ SmFun θ V, ∀ ψ ∈ SmFun θ V, T (φ + ψ) = T φ + T ψ
  smul : ∀ (c : ℂ) φ, T (c • φ) = c • T φ

theorem linOnSm_Rder {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) :
    LinOnSm θ V (Rder θ V τ X) :=
  ⟨fun _ h => Rder_mem h hX, fun _ h _ h' => Rder_add h h' hX, fun c φ => Rder_smul c φ τ X⟩

theorem linOnSm_RderC (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) : LinOnSm θ V (RderC θ V τ Z) := by
  obtain ⟨h1, h2⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ Z
  refine ⟨fun φ h => ?_, fun φ h ψ h' => ?_, fun c φ => ?_⟩
  · exact add_mem (Rder_mem h h1) (Submodule.smul_mem _ _ (Rder_mem h h2))
  · simp only [RderC]
    rw [Rder_add h h' h1, Rder_add h h' h2, smul_add Complex.I, add_add_add_comm]
  · simp only [RderC]
    rw [Rder_smul, Rder_smul, smul_add c, smul_comm c Complex.I]

theorem linOnSm_foldr {α : Type} (T : α → (GA D V → ℂ) → (GA D V → ℂ)) (l : List α)
    (hl : ∀ a ∈ l, LinOnSm θ V (T a)) : LinOnSm θ V fun φ => l.foldr (fun a f => T a f) φ := by
  induction l with
  | nil => exact ⟨fun _ h => h, fun _ _ _ _ => rfl, fun _ _ => rfl⟩
  | cons a l ih =>
    have h1 := hl a (by simp)
    have h2 := ih fun b hb => hl b (by simp [hb])
    refine ⟨fun φ h => h1.mem _ (h2.mem φ h), fun φ h ψ h' => ?_, fun c φ => ?_⟩
    · simp only [List.foldr_cons]
      rw [h2.add φ h ψ h', h1.add _ (h2.mem φ h) _ (h2.mem ψ h')]
    · simp only [List.foldr_cons]
      rw [h2.smul, h1.smul]

theorem linOnSm_gelf (τ : D.what₂.Tau) (k : ℕ) : LinOnSm θ V (gelf θ V τ k) := by
  have h : ∀ idx : Fin (k + 1) → Fin V.rank, LinOnSm θ V fun φ =>
      (List.ofFn fun a : Fin (k + 1) => RderC θ V τ (Matrix.single (idx a) (idx (a + 1)) 1)).foldr
        (fun f acc => f acc) φ := fun idx =>
    linOnSm_foldr (fun f => f) _ fun f hf => by
      obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hf
      exact linOnSm_RderC τ _
  refine ⟨fun φ hφ => Submodule.sum_mem _ fun idx _ => (h idx).mem φ hφ, fun φ hφ ψ hψ => ?_, fun c φ => ?_⟩
  · simp only [gelf]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun idx _ => (h idx).add φ hφ ψ hψ
  · simp only [gelf]
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun idx _ => (h idx).smul c φ

theorem one_le_sum_norm {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (h : A * B = 1) (i : Fin n) :
    1 ≤ ∑ a, ∑ b, (‖A a b‖ + ‖B a b‖) := by
  set S := ∑ a, ∑ b, (‖A a b‖ + ‖B a b‖) with hS
  have hS0 : 0 ≤ S := by positivity
  have hle : ∀ a b, ‖A a b‖ + ‖B a b‖ ≤ S := fun a b =>
    (Finset.single_le_sum (f := fun b => ‖A a b‖ + ‖B a b‖) (fun _ _ => by positivity) (Finset.mem_univ b)).trans
      (Finset.single_le_sum (f := fun a => ∑ b, (‖A a b‖ + ‖B a b‖)) (fun _ _ => by positivity) (Finset.mem_univ a))
  have hrow : ∑ b, ‖A i b‖ ≤ S :=
    (Finset.sum_le_sum fun b _ => le_add_of_nonneg_right (norm_nonneg (B i b))).trans
      (Finset.single_le_sum (f := fun a => ∑ b, (‖A a b‖ + ‖B a b‖)) (fun _ _ => by positivity) (Finset.mem_univ i))
  have h1 : (1 : ℝ) ≤ S * S := by
    have e : (1 : ℂ) = ∑ b, A i b * B b i := by rw [← Matrix.mul_apply, h, Matrix.one_apply_eq]
    calc (1 : ℝ) = ‖∑ b, A i b * B b i‖ := by rw [← e, norm_one]
      _ ≤ ∑ b, ‖A i b‖ * S := (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left ((le_add_of_nonneg_left (norm_nonneg (A b i))).trans (hle b i))
            (norm_nonneg _))
      _ ≤ S * S := by rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right hrow hS0
  nlinarith

variable (θ V) in
theorem infMat_mul_inv (τ : D.what₂.Tau) (g : GA D V) :
    infMat D.sp.cm.sig V.gram (θ τ) g * infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ = 1 := by
  have e : ∀ h : GA D V, infMat D.sp.cm.sig V.gram (θ τ) h = (infHom V h).1.map (θ τ) := fun _ => rfl
  rw [e, e, ← Matrix.map_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
    Matrix.map_one _ (map_zero _) (map_one _)]


variable (θ V) in
theorem normInf_dichotomy : (∀ g, normInf θ V g = 0) ∨ ∀ g, 1 ≤ normInf θ V g := by
  by_cases h : Nonempty D.what₂.Tau ∧ Nonempty (Fin V.rank)
  · obtain ⟨⟨τ⟩, ⟨i⟩⟩ := h
    refine Or.inr fun g => (one_le_sum_norm _ _ (infMat_mul_inv θ V τ g) i).trans ?_
    exact Finset.single_le_sum (f := fun τ => ∑ i, ∑ j, (‖infMat D.sp.cm.sig V.gram (θ τ) g i j‖ +
      ‖infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖)) (fun _ _ => by positivity) (Finset.mem_univ τ)
  · refine Or.inl fun g => Finset.sum_eq_zero fun τ _ => Finset.sum_eq_zero fun i _ => ?_
    exact (h ⟨⟨τ⟩, ⟨i⟩⟩).elim

variable (θ V) in
theorem exists_pow_ge (a b : ℕ) :
    ∃ N : ℕ, ∀ g, normInf θ V g ^ a ≤ normInf θ V g ^ N ∧ normInf θ V g ^ b ≤ normInf θ V g ^ N := by
  rcases normInf_dichotomy θ V with h | h
  · refine ⟨0, fun g => ?_⟩
    rw [h g, pow_zero]
    exact ⟨pow_le_one₀ le_rfl zero_le_one, pow_le_one₀ le_rfl zero_le_one⟩
  · exact ⟨max a b, fun g => ⟨pow_le_pow_right₀ (h g) (le_max_left _ _), pow_le_pow_right₀ (h g) (le_max_right _ _)⟩⟩

theorem normInf_nonneg (g : GA D V) : 0 ≤ normInf θ V g := by
  unfold normInf
  positivity

theorem isAutFunSm_smul (c : ℂ) {φ : GA D V → ℂ} (h : IsAutFunSm θ V φ) : IsAutFunSm θ V (c • φ) := by
  refine ⟨⟨fun γ hγ g => ?_, ?_, h.cont.const_smul c⟩, (SmFun θ V).smul_mem c h.smooth, ?_, ?_⟩
  · simp only [Pi.smul_apply, h.left γ hγ g]
  · obtain ⟨U, hU, hk⟩ := h.level
    exact ⟨U, hU, fun k h1 h2 g => by simp only [Pi.smul_apply, hk k h1 h2 g]⟩
  · obtain ⟨W, hW, h1, h2⟩ := h.zfin
    exact ⟨W, hW, W.smul_mem c h1, h2⟩
  · obtain ⟨N, hN⟩ := h.growth
    refine ⟨N, fun l hl x => ?_⟩
    obtain ⟨C, hC⟩ := hN l hl x
    refine ⟨‖c‖ * C, fun g hg => ?_⟩
    have := (linOnSm_foldr (θ := θ) (fun p : D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ => Rder θ V p.1 p.2) l
      fun p hp => linOnSm_Rder (hl p hp)).smul c φ
    rw [this, Pi.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC g hg) (norm_nonneg c)

variable (θ V) in
theorem isAutFunSm_zero : IsAutFunSm θ V 0 := by
  refine ⟨⟨fun _ _ _ => rfl, ⟨⊤, isOpen_univ, fun _ _ _ _ => rfl⟩, continuous_const⟩, (SmFun θ V).zero_mem,
    ⟨⊥, inferInstance, zero_mem _, fun τ k f hf => ?_⟩, ⟨0, fun l hl x => ⟨0, fun g _ => ?_⟩⟩⟩
  · have := (linOnSm_gelf (θ := θ) (V := V) τ k).smul 0 f
    rw [(Submodule.mem_bot ℂ).1 hf, zero_smul, zero_smul] at this
    rw [(Submodule.mem_bot ℂ).1 hf, this]
    exact zero_mem _
  · have := (linOnSm_foldr (θ := θ) (fun p : D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ => Rder θ V p.1 p.2) l
      fun p hp => linOnSm_Rder (hl p hp)).smul 0 0
    rw [zero_smul, zero_smul] at this
    rw [this]
    simp

theorem isAutFunSm_add {φ ψ : GA D V → ℂ} (h : IsAutFunSm θ V φ) (h' : IsAutFunSm θ V ψ) :
    IsAutFunSm θ V (φ + ψ) := by
  refine ⟨⟨fun γ hγ g => ?_, ?_, h.cont.add h'.cont⟩, (SmFun θ V).add_mem h.smooth h'.smooth, ?_, ?_⟩
  · simp only [Pi.add_apply, h.left γ hγ g, h'.left γ hγ g]
  · obtain ⟨U, hU, hk⟩ := h.level
    obtain ⟨U', hU', hk'⟩ := h'.level
    exact ⟨U ⊓ U', hU.inter hU', fun k h1 h2 g => by simp only [Pi.add_apply, hk k h1.1 h2 g, hk' k h1.2 h2 g]⟩
  · obtain ⟨W, hW, h1, h2⟩ := h.zfin
    obtain ⟨W', hW', h1', h2'⟩ := h'.zfin
    refine ⟨(W ⊓ SmFun θ V) ⊔ (W' ⊓ SmFun θ V), inferInstance,
      Submodule.add_mem_sup ⟨h1, h.smooth⟩ ⟨h1', h'.smooth⟩, fun τ k f hf => ?_⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hf
    have hg := linOnSm_gelf (θ := θ) (V := V) τ k
    rw [hg.add a ha.2 b hb.2]
    exact Submodule.add_mem_sup ⟨h2 τ k a ha.1, hg.mem a ha.2⟩ ⟨h2' τ k b hb.1, hg.mem b hb.2⟩
  · obtain ⟨N, hN⟩ := h.growth
    obtain ⟨N', hN'⟩ := h'.growth
    obtain ⟨M, hM⟩ := exists_pow_ge θ V N N'
    refine ⟨M, fun l hl x => ?_⟩
    obtain ⟨C, hC⟩ := hN l hl x
    obtain ⟨C', hC'⟩ := hN' l hl x
    refine ⟨|C| + |C'|, fun g hg => ?_⟩
    have := (linOnSm_foldr (θ := θ) (fun p : D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ => Rder θ V p.1 p.2) l
      fun p hp => linOnSm_Rder (hl p hp)).add φ h.smooth ψ h'.smooth
    rw [this, Pi.add_apply, add_mul]
    have h0 := normInf_nonneg (θ := θ) g
    refine (norm_add_le _ _).trans (add_le_add ((hC g hg).trans ?_) ((hC' g hg).trans ?_))
    · exact mul_le_mul (le_abs_self _) (hM g).1 (pow_nonneg h0 _) (abs_nonneg _)
    · exact mul_le_mul (le_abs_self _) (hM g).2 (pow_nonneg h0 _) (abs_nonneg _)

theorem mem_AFs_iff : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D) (φ : GA D V → ℂ),
    φ ∈ AFs θ V ↔ IsAutFunSm θ V φ := by
  intro D θ _ V φ
  refine ⟨fun h => ?_, fun h => Submodule.subset_span h⟩
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact isAutFunSm_zero θ V
  | add x y _ _ hx hy => exact isAutFunSm_add hx hy
  | smul c x _ hx => exact isAutFunSm_smul c hx

end GlobalTheory.Mem.AutSpace

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open Formalism.MainNotions.S hiding Af
open scoped TensorProduct Pointwise

namespace GlobalTheory.Mem.VolFin

theorem measure_lt_top_of_cover {G A B : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G]
    [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [LocallyCompactSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A]
    [Group B] [TopologicalSpace B] [IsTopologicalGroup B] [LocallyCompactSpace B] [SecondCountableTopology B]
    [MeasurableSpace B] [BorelSpace B]
    (e : G ≃ₜ* A × B) (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsHaarMeasure]
    (S : Finset B) (K : Set B) (hK : IsCompact K) (Ω : B → Set A)
    (hΩ : ∀ s, (Measure.haar : Measure A) (Ω s) < ⊤)
    (hcov : ∀ g : G, ∃ γ : Γ, ∃ s ∈ S, (e (γ • g)).1 ∈ Ω s ∧ (e (γ • g)).2 ∈ s • K)
    (𝓕 : Set G) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) : μ 𝓕 < ⊤ := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup Γ
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup Γ μ
  have h1 : (μ.map e).IsHaarMeasure := e.isHaarMeasure_map μ
  have h2 := Measure.isMulLeftInvariant_eq_smul (μ.map e)
    ((Measure.haar : Measure A).prod (Measure.haar : Measure B))
  have hle : μ 𝓕 ≤ μ (⋃ s ∈ S, e ⁻¹' (Ω s ×ˢ (s • K))) := by
    refine GlobalTheory.measure_le_of_isFundamentalDomain_of_ae_covers h𝓕 (.of_forall fun g => ?_)
    obtain ⟨γ, s, hs, h⟩ := hcov g
    exact ⟨γ, Set.mem_biUnion hs h⟩
  refine hle.trans_lt ((measure_biUnion_finset_le _ _).trans_lt (ENNReal.sum_lt_top.2 fun s _ => ?_))
  refine (Measure.le_map_apply (map_continuous e).measurable.aemeasurable _).trans_lt ?_
  rw [h2, Measure.smul_apply, Measure.prod_prod]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.mul_lt_top (hΩ s) (hK.smul s).measure_lt_top)

section Rat

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem sigR_inclR (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (x : E) :
    sigR R σ (inclR (F := F) R x) = inclR (F := F) R (σ x) := by
  simp [sigR, inclR]

noncomputable def ratPt (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) : Formalism.UG.UJ (σ : E →+* E) J →* HA R σ J where
  toFun γ := (⟨Formalism.UG.bc (inclR (F := F) R) γ.1, by
    have := congrArg (fun N => N.map (inclR (F := F) R)) (show Formalism.UG.cT _ _ * _ * _ = _ from γ.2)
    simp only [Matrix.map_mul] at this
    change Formalism.UG.cT _ _ * _ * _ = _
    refine Eq.trans ?_ this
    refine congrArg₂ (· * ·) (congrArg₂ (· * ·) ?_ rfl) rfl
    ext i j
    exact sigR_inclR R σ _⟩ : HR R σ J)
  map_one' := Subtype.ext (map_one (Formalism.UG.bc (inclR (F := F) R)))
  map_mul' a b := Subtype.ext (map_mul (Formalism.UG.bc (inclR (F := F) R)) _ _)

theorem topGroup_HA [FiniteDimensional F E] (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    IsTopologicalGroup (HA R σ J) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _
  exact inferInstanceAs (IsTopologicalGroup (HR R σ J))

theorem countable_HFinIn [Countable E] (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) : Countable (HFinIn R σ J) := by
  haveI : Countable (Matrix (Fin M) (Fin M) E) := inferInstanceAs (Countable (Fin M → Fin M → E))
  haveI : Countable (GL (Fin M) E) := Units.val_injective.countable
  refine Function.Surjective.countable
    (f := fun γ : Formalism.UG.UJ (σ : E →+* E) J => (⟨ratPt R σ J γ, γ.1, γ.2, rfl⟩ : HFinIn R σ J)) ?_
  rintro ⟨g, γ, hγ, h⟩
  exact ⟨⟨γ, hγ⟩, Subtype.ext (Subtype.ext h)⟩

variable [NumberField F]

theorem mulVec_fv {M : ℕ} (m : Matrix (Fin M) (Fin M) E) (x : Fin M → E) :
    (m.map (inclR (F := F) (Af F))).mulVec (GlobalTheory.AdLat.fv F x) = GlobalTheory.AdLat.fv F (m.mulVec x) := by
  ext i
  exact (RingHom.map_mulVec (inclR (F := F) (Af F)) m x i).symm

theorem mulVec_mem_hat_of_rat {M : ℕ} (m : Matrix (Fin M) (Fin M) E) (Λ : Submodule (𝓞 E) (Fin M → E))
    (h : ∀ x ∈ Λ, m.mulVec x ∈ Λ) {z : Fin M → Af F ⊗[F] E} (hz : z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin M → E))) :
    (m.map (inclR (F := F) (Af F))).mulVec z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin M → E)) := by
  refine GlobalTheory.AdLat.Translate.mulVec_mem_hat (fun x hx => ?_) hz
  rw [SetLike.mem_coe, GlobalTheory.AdLat.Translate.mem_pre, mulVec_fv]
  exact GlobalTheory.AdLat.Translate.fv_mem_hat (h x hx)

theorem stabHat_conj {M : ℕ} (δ : GL (Fin M) E) (L Λ : Submodule (𝓞 E) (Fin M → E))
    (s : GL (Fin M) (Af F ⊗[F] E))
    (hΛ : (GlobalTheory.AdLat.hat F (Λ : Set (Fin M → E)) : Set (Fin M → Af F ⊗[F] E)) =
      (s : Matrix (Fin M) (Fin M) (Af F ⊗[F] E)).mulVec '' (GlobalTheory.AdLat.hat F (L : Set (Fin M → E))))
    (h : ∀ x, x ∈ Λ ↔ (δ : Matrix (Fin M) (Fin M) E).mulVec x ∈ Λ) :
    StabHat F (L : Set (Fin M → E))
      ((s⁻¹ * Formalism.UG.bc (inclR (F := F) (Af F)) δ * s : GL (Fin M) (Af F ⊗[F] E)) :
        Matrix (Fin M) (Fin M) (Af F ⊗[F] E)) := by
  have him : ∀ y, y ∈ latHat F E (L : Set (Fin M → E)) ↔
      (s : Matrix (Fin M) (Fin M) (Af F ⊗[F] E)).mulVec y ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin M → E)) := by
    intro y
    rw [← SetLike.mem_coe (p := GlobalTheory.AdLat.hat F (Λ : Set (Fin M → E))), hΛ]
    constructor
    · exact fun hy => ⟨y, hy, rfl⟩
    · rintro ⟨u, hu, huy⟩
      have := congrArg ((s⁻¹ : GL (Fin M) (Af F ⊗[F] E)) : Matrix (Fin M) (Fin M) (Af F ⊗[F] E)).mulVec huy
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Matrix.one_mulVec] at this
      exact this ▸ hu
  intro y
  rw [him, him, Matrix.mulVec_mulVec y, ← Units.val_mul, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul,
    Units.val_mul, ← Matrix.mulVec_mulVec]
  refine ⟨mulVec_mem_hat_of_rat _ Λ fun x hx => (h x).1 hx, fun hz => ?_⟩
  have := mulVec_mem_hat_of_rat ((δ⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) Λ (fun x hx => by
    rw [h, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]; exact hx) hz
  change ((Formalism.UG.bc (inclR (F := F) (Af F)) δ⁻¹ : GL (Fin M) (Af F ⊗[F] E)) :
    Matrix (Fin M) (Fin M) (Af F ⊗[F] E)).mulVec _ ∈ _ at this
  rwa [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
    Matrix.one_mulVec] at this

end Rat

theorem finVol : FiniteVolume₂ := by
  intro F E _ _ _ _ _ σ hCM M J hJ μ hμ 𝓕 h𝓕
  classical
  haveI := topGroup_HA (AF F) σ J
  haveI := topGroup_HA (Ainf F) σ J
  haveI := topGroup_HA (Af F) σ J
  haveI : BorelSpace (HA (AF F) σ J) := ⟨rfl⟩
  haveI : BorelSpace (HA (Ainf F) σ J) := ⟨rfl⟩
  haveI : BorelSpace (HA (Af F) σ J) := ⟨rfl⟩
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_infiniteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_infiniteAdeleRing_of_numberField_field F
  obtain ⟨_, _, -⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_HA (Ainf F) σ M J
  obtain ⟨_, _, -⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_HA (Af F) σ M J
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  let Γ : Subgroup (HA (AF F) σ J) := HFinIn (AF F) σ J
  haveI : Countable Γ := countable_HFinIn (AF F) σ J
  obtain ⟨e, he⟩ := GlobalTheory.Mem.VolSplit.exists_adelic_split F E σ M J
  have herat : ∀ γ, e (ratPt (AF F) σ J γ) = (ratPt (Ainf F) σ J γ, ratPt (Af F) σ J γ) := by
    intro γ
    refine Prod.ext (Subtype.ext (Units.ext ((he _).2.trans ?_))) (Subtype.ext (Units.ext ((he _).1.trans ?_)))
    · ext i j
      change Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (inclR (F := F) (AF F) _) = inclR (F := F) (Ainf F) _
      simp [inclR]
    · ext i j
      change Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (inclR (F := F) (AF F) _) = inclR (F := F) (Af F) _
      simp [inclR]
  let b := Pi.basisFun E (Fin M)
  let L : Submodule (𝓞 E) (Fin M → E) := Submodule.span (𝓞 E) (Set.range b)
  have hL : L.FG := Submodule.fg_span (Set.finite_range b)
  have hLs : Submodule.span E (L : Set (Fin M → E)) = ⊤ := by
    rw [eq_top_iff, ← b.span_eq]
    exact Submodule.span_mono Submodule.subset_span
  obtain ⟨K, hK, hKo, hKc⟩ := GlobalTheory.T.completedLattice_stabilizer_compact_open F E σ M J L hL hLs
  obtain ⟨S, hS⟩ := GlobalTheory.T.finite_classSet_hermitianUnitary_openLevel F E σ hCM M J hJ K hKo
  choose Λ _ hΛ1 hΛ2 hΛ3 using fun s : HA (Af F) σ J =>
    GlobalTheory.AdLat.exists_lattice_latOf F E M L (HA.mat (Af F) σ J s) hL hLs
  choose Ω _ hΩ1 hΩ2 using fun s : HA (Af F) σ J =>
    GlobalTheory.T.finite_covolume_latticeStabiliser_unitaryRealPoints F E σ hCM M J hJ (Λ s) (hΛ1 s) (hΛ2 s) Measure.haar inferInstance
  refine measure_lt_top_of_cover e Γ μ S K hKc Ω hΩ1 (fun g => ?_) 𝓕 h𝓕
  obtain ⟨⟨γ', γ, hγ, hγγ⟩, s, hs, k, hk, hg⟩ := hS (e g).2
  have hg2 : (e g).2 = ratPt (Af F) σ J ⟨γ, hγ⟩ * (s * k) := by
    rw [hg]
    exact congrArg (· * (s * k)) (Subtype.ext hγγ.symm : (γ' : HA (Af F) σ J) = ratPt (Af F) σ J ⟨γ, hγ⟩)
  obtain ⟨δ, hδ, hδΛ, w, hw, hwe⟩ := hΩ2 s ((ratPt (Ainf F) σ J ⟨γ, hγ⟩)⁻¹ * (e g).1)
  have hw1 : (ratPt (Ainf F) σ J ⟨γ, hγ⟩)⁻¹ * (e g).1 = ratPt (Ainf F) σ J ⟨δ, hδ⟩ * w := Subtype.ext hwe
  have hkδ : s⁻¹ * ratPt (Af F) σ J ⟨δ, hδ⟩ * s ∈ K :=
    (hK _).2 (stabHat_conj δ L (Λ s) (HA.mat (Af F) σ J s) (hΛ3 s) hδΛ)
  let η : Formalism.UG.UJ (σ : E →+* E) J := (⟨δ, hδ⟩ : Formalism.UG.UJ (σ : E →+* E) J)⁻¹ * (⟨γ, hγ⟩ : Formalism.UG.UJ (σ : E →+* E) J)⁻¹
  refine ⟨⟨ratPt (AF F) σ J η, η.1, η.2, rfl⟩, s, hs, ?_, ?_⟩
  · change (e (ratPt (AF F) σ J η * g)).1 ∈ _
    rw [map_mul, herat, Prod.fst_mul, map_mul, map_inv, map_inv, mul_assoc, hw1, inv_mul_cancel_left]
    exact hw
  · change (e (ratPt (AF F) σ J η * g)).2 ∈ _
    rw [map_mul, herat, Prod.snd_mul]
    dsimp only
    rw [map_mul, map_inv, map_inv, mul_assoc, hg2, inv_mul_cancel_left]
    refine ⟨_, K.mul_mem (K.inv_mem hkδ) hk, ?_⟩
    simp only [smul_eq_mul]
    group

end GlobalTheory.Mem.VolFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotientStatement
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open Formalism.MainNotions.S hiding Af
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteVolume_adelicUnitaryQuotient : FiniteVolume₂ := by
  first | exact @GlobalTheory.Mem.VolFin.finVol | exact GlobalTheory.Mem.VolFin.finVol | (intros; apply GlobalTheory.Mem.VolFin.finVol <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsFundamentalDomain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Datum
open Formalism.MainNotions.S hiding Af
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FundDomDiscrete


open Topology Filter in
theorem exists_measurable_section {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [OpensMeasurableSpace G]
    (Γ : Subgroup G) [DiscreteTopology Γ] :
    ∃ F : Set G, MeasurableSet F ∧ ∀ x : G, ∃! γ : Γ, γ • x ∈ F := by
  classical
  obtain ⟨W, hWo, hW⟩ : ∃ W : Set G, IsOpen W ∧ ((↑) : Γ → G) ⁻¹' W = {1} :=
    isOpen_induced_iff.1 (isOpen_discrete ({1} : Set Γ))
  have h1W : (1 : G) ∈ W := by
    have : (1 : Γ) ∈ ((↑) : Γ → G) ⁻¹' W := by rw [hW]; rfl
    simpa using this
  obtain ⟨V0, hV0, hVW⟩ := exists_nhds_split_inv (hWo.mem_nhds h1W)
  obtain ⟨V, hVV0, hVo, h1V⟩ := mem_nhds_iff.1 hV0
  let U : G → Set G := fun g => {x | x * g⁻¹ ∈ V}
  have hUo : ∀ g, IsOpen (U g) := fun g => hVo.preimage (by fun_prop)
  have hUinj : ∀ g (γ : Γ) (x : G), x ∈ U g → (γ : G) * x ∈ U g → γ = 1 := by
    intro g γ x hx hγ
    have h := hVW _ (hVV0 hγ) _ (hVV0 hx)
    have h2 : (γ : G) * x * g⁻¹ / (x * g⁻¹) = γ := by
      rw [div_eq_mul_inv]; group
    rw [h2] at h
    have : γ ∈ ((↑) : Γ → G) ⁻¹' W := h
    rw [hW] at this
    exact this
  obtain ⟨s, hsc, hs⟩ := TopologicalSpace.countable_cover_nhds (f := U)
    (fun g => (hUo g).mem_nhds (by simpa [U] using h1V))
  have hsne : s.Nonempty := by
    have : (1 : G) ∈ ⋃ x ∈ s, U x := by rw [hs]; trivial
    simp only [Set.mem_iUnion] at this
    obtain ⟨i, hi, -⟩ := this
    exact ⟨i, hi⟩
  obtain ⟨e, rfl⟩ := hsc.exists_eq_range hsne
  have hcov : ∀ x : G, ∃ n, x ∈ U (e n) := by
    intro x
    have : x ∈ ⋃ y ∈ Set.range e, U y := by rw [hs]; trivial
    simp only [Set.mem_iUnion] at this
    obtain ⟨_, ⟨n, rfl⟩, hn⟩ := this
    exact ⟨n, hn⟩
  let S : ℕ → Set G := fun n => ⋃ γ : Γ, {x | (γ : G) * x ∈ U (e n)}
  have hSo : ∀ n, IsOpen (S n) := fun n =>
    isOpen_iUnion fun γ => (hUo _).preimage (continuous_const.mul continuous_id)
  have hSmem : ∀ n x, x ∈ S n ↔ ∃ γ : Γ, (γ : G) * x ∈ U (e n) := by
    intro n x; simp [S]
  have hSinv : ∀ n (δ : Γ) x, (δ : G) * x ∈ S n ↔ x ∈ S n := by
    intro n δ x
    rw [hSmem, hSmem]
    constructor
    · rintro ⟨γ, h⟩
      exact ⟨γ * δ, by simpa [mul_assoc] using h⟩
    · rintro ⟨γ, h⟩
      exact ⟨γ * δ⁻¹, by simpa [mul_assoc] using h⟩
  refine ⟨⋃ n, (U (e n) ∩ ⋂ k, ⋂ _ : k < n, (S k)ᶜ), ?_, ?_⟩
  · exact MeasurableSet.iUnion fun n => (hUo _).measurableSet.inter
      (MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ => (hSo k).measurableSet.compl)
  · intro x
    have hex : ∃ n, x ∈ S n := by
      obtain ⟨n, hn⟩ := hcov x
      exact ⟨n, (hSmem n x).2 ⟨1, by simpa using hn⟩⟩
    have key : ∀ γ : Γ, γ • x ∈ (⋃ n, (U (e n) ∩ ⋂ k, ⋂ _ : k < n, (S k)ᶜ)) ↔
        (γ : G) * x ∈ U (e (Nat.find hex)) := by
      intro γ
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff,
        Subgroup.smul_def, smul_eq_mul, hSinv]
      constructor
      · rintro ⟨n, hn, hk⟩
        have : Nat.find hex = n := by
          rw [Nat.find_eq_iff]
          exact ⟨(hSmem n x).2 ⟨γ, hn⟩, hk⟩
        rw [this]; exact hn
      · intro h
        exact ⟨_, h, fun k hk => Nat.find_min hex hk⟩
    obtain ⟨γ, hγ⟩ := (hSmem _ x).1 (Nat.find_spec hex)
    refine ⟨γ, (key γ).2 hγ, fun δ hδ => ?_⟩
    have hδ' := (key δ).1 hδ
    have := hUinj _ (δ * γ⁻¹) _ hγ (by simpa [mul_assoc] using hδ')
    exact mul_inv_eq_one.1 this

theorem exists_isFundamentalDomain {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [OpensMeasurableSpace G]
    (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) :
    ∃ F : Set G, IsFundamentalDomain Γ F μ := by
  obtain ⟨F, hF, h⟩ := exists_measurable_section Γ
  exact ⟨F, IsFundamentalDomain.mk' hF.nullMeasurableSet h⟩

theorem exists_fundDom : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)), μ.IsHaarMeasure →
    ∃ 𝓕 : Set (GA D V), IsFundamentalDomain (GQ V) 𝓕 μ := by
  intro D V μ _
  have := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V).2.1
  have := (GlobalTheory.RationalCountable.discrete_countable_GQ D V).1
  have : BorelSpace (GA D V) := ⟨rfl⟩
  have : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (AF D.host.F) _
  have : IsTopologicalGroup (GA D V) :=
    inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  exact exists_isFundamentalDomain (GQ V) μ

end GlobalTheory.FundDomDiscrete
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeLAdicCharacterAndPrincipalIdealSt
namespace GlobalTheory.Published

theorem GlobalArtinReciprocity.heckeLAdicCharacter_and_principalIdealSt :
    GlobalArtinReciprocity → HeckeLAdicCharacter ∧ PrincipalIdealSt :=
  fun h => ⟨h.heckeLAdicCharacter, h.principalIdealSt⟩

end GlobalTheory.Published
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousAdelicUnitaryEmbedding
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousAdelicUnitaryEmbedding
noncomputable section

namespace GlobalTheory.Mem.UnitaryEmb

open scoped TensorProduct
open NumberField Matrix

section General

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : CMData F E) (B A : HSpace E) (ι : B.V →ₗ[E] A.V) (h : HSpace.IsIsomEmb B A ι)

theorem continuous_embA : Continuous (embA hc B A ι h) := by
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  refine Continuous.subtype_mk (Continuous.comp (g := Units.map _) ?_ continuous_subtype_val) _
  exact Continuous.units_map _ (continuous_const.add
    ((continuous_const.matrix_mul (continuous_id.sub continuous_const)).matrix_mul continuous_const))

theorem embA_ratA (γ : GRat hc B) : embA hc B A ι h (ratA hc B γ) = ratA hc A (embRat hc B A ι h γ) := by
  refine Subtype.ext (Units.ext ?_)
  show 1 + (embMat B A ι).map (inclR (F := F) (AF F)) *
      (((γ : GL (Fin B.rank) E) : Matrix (Fin B.rank) (Fin B.rank) E).map (inclR (F := F) (AF F)) - 1) *
        (projMat hc B A ι).map (inclR (F := F) (AF F)) =
    (1 + embMat B A ι * (((γ : GL (Fin B.rank) E) : Matrix (Fin B.rank) (Fin B.rank) E) - 1) *
      projMat hc B A ι).map (inclR (F := F) (AF F))
  rw [Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_mul, Matrix.map_sub _ (map_sub _),
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _)]

end General

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_embHom (D : D7) (A B : HSp D) (ι : B.V →ₗ[D.host.E] A.V) (hι : HSpace.IsIsomEmb B A ι) :
    ∃ s : GA D B →* GA D A, Continuous s ∧ (∀ h g, EmbRel A B ι g h ↔ g = s h) ∧ ∀ γ ∈ GQ B, s γ ∈ GQ A := by
  refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.embA D.sp.cm B A ι hι, continuous_embA D.sp.cm B A ι hι,
    fun h g => GlobalTheory.AutFunCompare.embRel_iff A B ι hι g h, ?_⟩
  rw [GlobalTheory.AutFunCompare.GQ_eq, GlobalTheory.AutFunCompare.GQ_eq]
  rintro _ ⟨γ, rfl⟩
  exact ⟨_, (embA_ratA D.sp.cm B A ι hι γ).symm⟩

end GlobalTheory.Mem.UnitaryEmb

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousAdelicUnitaryEmbeddingStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_adelicUnitaryEmbedding : ∀ (D : D7) (A B : HSp D) (ι : B.V →ₗ[D.host.E] A.V), HSpace.IsIsomEmb B A ι → ∃ s : GA D B →* GA D A, Continuous s ∧ (∀ h g, EmbRel A B ι g h ↔ g = s h) ∧ ∀ γ ∈ GQ B, s γ ∈ GQ A := by
  first | exact @GlobalTheory.Mem.UnitaryEmb.exists_embHom | exact GlobalTheory.Mem.UnitaryEmb.exists_embHom | (intros; apply GlobalTheory.Mem.UnitaryEmb.exists_embHom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteNormalFlatClosure
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.GraphClosure

theorem exists_normalisation_of_locallyClosed : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] (P U : Scheme.{0}) (s : P ⟶ Sp O) (Ω : P.Opens) (j : U ⟶ Ω.toScheme), IsProjOver s → IsClosedImmersion j → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme U → Flat (j ≫ Ω.ι ≫ s) → ∃ (Z' : Scheme.{0}) (ν : Z' ⟶ P) (e : U ⟶ Z'), IsFinite ν ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z' ∧ IsProjOver (ν ≫ s) ∧ Flat (ν ≫ s) ∧ IsPullback e j ν Ω.ι ∧ Dense (Set.range e) := by
  intro O _ _ _ P U s Ω j hs _ hn hfl
  have : IsProper s := ((isProjOver_iff_isProper_and_exists_isAmpleLB s).mp hs).1
  have := GlobalTheory.IsNormalScheme.of_pred hn
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian s
  have : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian (j ≫ Ω.ι)
  obtain ⟨h, eh⟩ : ∃ h : U ⟶ P, h = j ≫ Ω.ι := ⟨_, rfl⟩
  have : QuasiCompact h := eh ▸ inferInstance
  have : IsSeparated h := eh ▸ inferInstance
  have : LocallyOfFiniteType h := eh ▸ inferInstance
  have : Flat (h ≫ s) := by rw [eh, Category.assoc]; exact hfl
  have : IsFinite h.fromNormalization :=
    isFinite_fromNormalization_of_locallyOfFiniteType (o := CommRingCat.of O) h s
      fun x hx => charZero_residueField_of_flat (h ≫ s) hx
  have : Flat (h.toNormalization ≫ h.fromNormalization ≫ s) := by
    rw [Scheme.Hom.toNormalization_fromNormalization_assoc]
    infer_instance
  exact ⟨h.normalization, h.fromNormalization, h.toNormalization, inferInstance,
    IsNormalScheme.pred _, isProjOver_comp_of_isFinite _ hs, flat_normalization h _,
    isPullback_toNormalization_of_mono j Ω.ι h eh, h.toNormalization.denseRange⟩

end GlobalTheory.GraphClosure
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCuspFunctionClosedUnderOperations
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCuspFunctionClosedUnderOperations
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Th

theorem isCuspFun_closed : ∀ (D : D7) (V : HSp D) (φ φ' : GA D V → ℂ), IsAutFun V φ → IsAutFun V φ' → IsCuspFun V φ → IsCuspFun V φ' → IsCuspFun V (φ + φ') ∧ (∀ c : ℂ, IsCuspFun V (c • φ)) ∧ (∀ k, IsCuspFun V (rTr V k φ)) ∧ IsCuspFun V (fun g => star (φ g)) := by
  intro D V φ φ' h h' c c'
  refine ⟨?_, fun a r C hC μ 𝓕 hμ h𝓕 g => ?_, fun k r C hC μ 𝓕 hμ h𝓕 g => ?_, fun r C hC μ 𝓕 hμ h𝓕 g => ?_⟩
  · refine (GlobalTheory.AutFunCompare.isCuspFun_iff V (φ + φ') (h.cont.add h'.cont) fun γ hγ g => ?_).2
      (add_mem ((GlobalTheory.AutFunCompare.isCuspFun_iff V φ h.cont h.left).1 c)
        ((GlobalTheory.AutFunCompare.isCuspFun_iff V φ' h'.cont h'.left).1 c'))
    rw [Pi.add_apply, Pi.add_apply, h.left γ hγ, h'.left γ hγ]
  · simp only [Pi.smul_apply]
    rw [integral_smul, c r C hC μ 𝓕 hμ h𝓕 g, smul_zero]
  · simp only [rTr, mul_assoc]
    exact c r C hC μ 𝓕 hμ h𝓕 (g * k)
  · have e := integral_conj (𝕜 := ℂ) (μ := μ.restrict 𝓕) (f := fun n : NI V C => φ ((n : GA D V) * g))
    rw [c r C hC μ 𝓕 hμ h𝓕 g, map_zero] at e
    exact e

end GlobalTheory.Mem.Th
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCuspFunctionClosedUnderOperationsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCuspFunction_closed_under_operations : ∀ (D : D7) (V : HSp D) (φ φ' : GA D V → ℂ), IsAutFun V φ → IsAutFun V φ' → IsCuspFun V φ → IsCuspFun V φ' → IsCuspFun V (φ + φ') ∧ (∀ c : ℂ, IsCuspFun V (c • φ)) ∧ (∀ k, IsCuspFun V (rTr V k φ)) ∧ IsCuspFun V (fun g => star (φ g)) := by
  first | exact @GlobalTheory.Mem.Th.isCuspFun_closed | exact GlobalTheory.Mem.Th.isCuspFun_closed | (intros; apply GlobalTheory.Mem.Th.isCuspFun_closed <;> assumption)
end
end
