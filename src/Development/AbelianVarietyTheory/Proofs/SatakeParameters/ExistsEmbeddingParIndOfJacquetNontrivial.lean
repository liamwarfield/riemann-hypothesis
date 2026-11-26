module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteClass
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThCLeftStab
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LabelSettingTameGenerator

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsEmbeddingParIndOfJacquetNontrivial
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsEmbeddingParIndOfJacquetNontrivial
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace GlobalTheory

theorem injective_of_jacquet_surjective {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} (π : Irr k n) {s : ℕ} {d : Fin s → ℕ}
    (e : (Σ a, Fin (d a)) ≃ Fin n) {Y : Type} [AddCommGroup Y] [Module ℂ Y]
    {τ : Representation ℂ (Levi k fun a => Fin (d a)) Y} (hirr : τ.IsIrreducible)
    (q : (GlobalTheory.SmGL.jac e π.π).IntertwiningMap τ) (hq : Function.Surjective q) :
    ∃ φ : π.π.IntertwiningMap (parInd e τ), Function.Injective φ := by
  obtain ⟨φ, hφ⟩ := (Model.evalOne_bijective e π.smooth τ).2 q
  refine ⟨φ, (injective_iff_map_eq_zero _).2 fun v hv => ?_⟩
  have hK : φ.ker ≠ ⊤ := by
    intro hK
    haveI := Model.nontrivial_of_isIrreducible hirr
    obtain ⟨y, hy⟩ := exists_ne (0 : Y)
    obtain ⟨x, rfl⟩ := hq y
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    apply hy
    have hw : φ w = 0 := (show w ∈ φ.ker from hK ▸ trivial)
    have h1 : q (Submodule.Quotient.mk w) = (φ w).1.1 1 :=
      (congrArg (fun F => F (Submodule.Quotient.mk w)) hφ).symm
    rw [h1, hw]
    rfl
  have hv' : v ∈ φ.ker := hv
  haveI := π.irr
  rw [(eq_bot_or_eq_top φ.ker).resolve_right hK] at hv'
  exact hv'

theorem exists_embedding_parInd_of_jacquet_nontrivial : GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (π : Irr k n) (s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n), ¬ Subsingleton (Jacquet π.π (unipRad k e)) → ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (τ : Representation ℂ (Levi k fun a => Fin (d a)) Y), τ.IsIrreducible ∧ IsSmooth τ ∧ IsSubquotient τ (GlobalTheory.SmGL.jac e π.π) ∧ ∃ φ : π.π.IntertwiningMap (parInd e τ), Function.Injective φ := by
  intro hBZ k _ _ _ _ n π s d e hJ
  have hfl : HasFiniteLength (GlobalTheory.SmGL.jac e π.π) :=
    (hBZ k).2.1 (Fin s) (Fin n) (fun a => Fin (d a)) e π.V π.π π.smooth
      (hasFiniteLength_of_isIrreducible π.irr)
  haveI : WellFoundedGT (Subrepresentation (GlobalTheory.SmGL.jac e π.π)) :=
    ((hasFiniteLength_iff_wellFounded _).1 hfl).1
  have hne : (⊥ : Subrepresentation (GlobalTheory.SmGL.jac e π.π)) ≠ ⊤ := by
    intro h
    apply hJ
    constructor
    intro x y
    have hx : x ∈ (⊥ : Subrepresentation (GlobalTheory.SmGL.jac e π.π)) := h ▸ trivial
    have hy : y ∈ (⊥ : Subrepresentation (GlobalTheory.SmGL.jac e π.π)) := h ▸ trivial
    exact (hx : x = 0).trans (hy : y = 0).symm
  obtain ⟨M, hM, -⟩ :=
    (eq_top_or_exists_le_coatom (⊥ : Subrepresentation (GlobalTheory.SmGL.jac e π.π))).resolve_left hne
  let q : (GlobalTheory.SmGL.jac e π.π).IntertwiningMap (subQuot ⊤ M) :=
    ⟨(Submodule.mkQ _) ∘ₗ LinearMap.codRestrict (⊤ : Subrepresentation (GlobalTheory.SmGL.jac e π.π)).toSubmodule
      LinearMap.id (fun v => trivial), fun g => rfl⟩
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨⟨v, hv⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨v, rfl⟩
  have hirr : (subQuot ⊤ M).IsIrreducible := isIrreducible_subQuot hM.covBy_top
  have hsq : IsSubquotient (subQuot ⊤ M) (GlobalTheory.SmGL.jac e π.π) := .of_surjective q hq
  refine ⟨_, _, _, subQuot ⊤ M, hirr, hsq.isSmooth (isSmooth_jac e π.smooth), hsq, ?_⟩
  exact injective_of_jacquet_surjective π e hirr q hq

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsEmbeddingParIndOfJacquetNontrivialStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_injective_parInd_of_jacquet_nontrivial : GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (π : Irr k n) (s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n), ¬ Subsingleton (Jacquet π.π (unipRad k e)) → ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (τ : Representation ℂ (Levi k fun a => Fin (d a)) Y), τ.IsIrreducible ∧ IsSmooth τ ∧ IsSubquotient τ (GlobalTheory.SmGL.jac e π.π) ∧ ∃ φ : π.π.IntertwiningMap (parInd e τ), Function.Injective φ := by
  first | exact @GlobalTheory.exists_embedding_parInd_of_jacquet_nontrivial | exact GlobalTheory.exists_embedding_parInd_of_jacquet_nontrivial | (intros; apply GlobalTheory.exists_embedding_parInd_of_jacquet_nontrivial <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCompletionEmbeddingInducingHostEmbedding
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCompletionEmbeddingInducingHostEmbedding
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open Formalism.BasicNotions.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.EmbExt

variable {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E]

def scalarLift (φ : E →+* Om l) : ℚ_[l] ⊗[ℚ] E →ₐ[ℚ_[l]] Om l :=
  Algebra.TensorProduct.lift (Algebra.ofId ℚ_[l] (Om l)) φ.toRatAlgHom (fun _ _ => Commute.all _ _)

theorem scalarLift_tmul (φ : E →+* Om l) (a : ℚ_[l]) (y : E) :
    scalarLift φ (a ⊗ₜ y) = algebraMap ℚ_[l] (Om l) a * φ y := by
  simp [scalarLift]

theorem exists_near (φ ψ : E →+* Om l) (t : ℚ_[l] ⊗[ℚ] E) :
    ∀ ε : ℝ, 0 < ε → ∃ x : E, ‖scalarLift φ t - φ x‖ < ε ∧ ‖scalarLift ψ t - ψ x‖ < ε := by
  induction t using TensorProduct.inductionOn with
  | tmul a y =>
    intro ε hε
    have hM : 0 < ‖φ y‖ + ‖ψ y‖ + 1 := by positivity
    obtain ⟨q, hq⟩ := Padic.rat_dense l a (div_pos hε hM)
    refine ⟨(q : E) * y, ?_, ?_⟩
    · rw [scalarLift_tmul, map_mul, map_ratCast, ← map_ratCast (algebraMap ℚ_[l] (Om l)) q, ← sub_mul,
        ← map_sub, norm_mul, PadicAlgCl.norm_extends]
      calc ‖a - (q : ℚ_[l])‖ * ‖φ y‖ ≤ ‖a - (q : ℚ_[l])‖ * (‖φ y‖ + ‖ψ y‖ + 1) := by
            gcongr; linarith [norm_nonneg (ψ y)]
        _ < ε / (‖φ y‖ + ‖ψ y‖ + 1) * (‖φ y‖ + ‖ψ y‖ + 1) := by gcongr
        _ = ε := div_mul_cancel₀ _ hM.ne'
    · rw [scalarLift_tmul, map_mul, map_ratCast, ← map_ratCast (algebraMap ℚ_[l] (Om l)) q, ← sub_mul,
        ← map_sub, norm_mul, PadicAlgCl.norm_extends]
      calc ‖a - (q : ℚ_[l])‖ * ‖ψ y‖ ≤ ‖a - (q : ℚ_[l])‖ * (‖φ y‖ + ‖ψ y‖ + 1) := by
            gcongr; linarith [norm_nonneg (φ y)]
        _ < ε / (‖φ y‖ + ‖ψ y‖ + 1) * (‖φ y‖ + ‖ψ y‖ + 1) := by gcongr
        _ = ε := div_mul_cancel₀ _ hM.ne'
  | add t₁ t₂ h₁ h₂ =>
    intro ε hε
    obtain ⟨x₁, a₁, b₁⟩ := h₁ (ε / 2) (half_pos hε)
    obtain ⟨x₂, a₂, b₂⟩ := h₂ (ε / 2) (half_pos hε)
    refine ⟨x₁ + x₂, ?_, ?_⟩
    · have e : scalarLift φ (t₁ + t₂) - φ (x₁ + x₂) = (scalarLift φ t₁ - φ x₁) + (scalarLift φ t₂ - φ x₂) := by
        rw [map_add (f := _), map_add (f := _)]; ring
      rw [e]; linarith [norm_add_le (scalarLift φ t₁ - φ x₁) (scalarLift φ t₂ - φ x₂)]
    · have e : scalarLift ψ (t₁ + t₂) - ψ (x₁ + x₂) = (scalarLift ψ t₁ - ψ x₁) + (scalarLift ψ t₂ - ψ x₂) := by
        rw [map_add (f := _), map_add (f := _)]; ring
      rw [e]; linarith [norm_add_le (scalarLift ψ t₁ - ψ x₁) (scalarLift ψ t₂ - ψ x₂)]

theorem norm_scalarLift_le (φ ψ : E →+* Om l) (h : ∀ x, ‖φ x‖ = ‖ψ x‖) (t : ℚ_[l] ⊗[ℚ] E) :
    ‖scalarLift ψ t‖ ≤ ‖scalarLift φ t‖ := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨x, h₁, h₂⟩ := exists_near φ ψ t (ε / 2) (half_pos hε)
  have e1 : ‖scalarLift ψ t‖ ≤ ‖scalarLift ψ t - ψ x‖ + ‖ψ x‖ := by
    simpa using norm_add_le (scalarLift ψ t - ψ x) (ψ x)
  have e2 : ‖φ x‖ ≤ ‖φ x - scalarLift φ t‖ + ‖scalarLift φ t‖ := by
    simpa using norm_add_le (φ x - scalarLift φ t) (scalarLift φ t)
  rw [norm_sub_rev] at e2
  rw [← h x] at e1
  linarith

theorem norm_eq_of_same_place (τ φ : E →+* Om l) (w : HeightOneSpectrum (𝓞 E)) (hw : w ∈ placesOver E l)
    (hτ : ∀ x : 𝓞 E, ‖τ (x : E)‖ < 1 ↔ x ∈ w.asIdeal) (hφ : ∀ x : 𝓞 E, ‖φ (x : E)‖ < 1 ↔ x ∈ w.asIdeal)
    (x : E) : ‖τ x‖ = ‖φ x‖ := by
  have e1 := PI.CompDegEF.isEquiv_adicAbv_normAbv τ w hw
    (fun x => ⟨PI.CompDegEF.norm_le_one_of_integer τ x, hτ x⟩)
  have e2 := PI.CompDegEF.isEquiv_adicAbv_normAbv φ w hw
    (fun x => ⟨PI.CompDegEF.norm_le_one_of_integer φ x, hφ x⟩)
  obtain ⟨c, hc, hce⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.1 (e1.symm.trans e2)
  have hl := congrFun hce ((l : ℕ) : E)
  simp only [PI.CompDegEF.normAbv_apply, map_natCast] at hl
  have hpos := PI.CompDegEF.norm_natCast_pos l
  have hlt := PI.CompDegEF.norm_natCast_lt_one l
  have hL : Real.log ‖((l : ℕ) : Om l)‖ ≠ 0 := (Real.log_neg hpos hlt).ne
  have hc1 : c = 1 := by
    have := congrArg Real.log hl
    rw [Real.log_rpow hpos] at this
    exact (mul_eq_right₀ hL).1 this
  have hx := congrFun hce x
  simp only [PI.CompDegEF.normAbv_apply, hc1, Real.rpow_one] at hx
  exact hx

theorem main : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (w : PlE D.host) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) O), GlobalTheory.Pst.Induces Bw → ∀ τ : D.host.E →+* Qbar l, (∀ x : 𝓞 D.host.E, ‖τ (x : D.host.E)‖ < 1 ↔ x ∈ w.asIdeal) → ∀ LL' : FinExt l, Bw.LL.1 ≤ LL'.1 → ∃ τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1, GlobalTheory.Pst.IsInduced Bw τ τ' := by
  intro D l _ w O _ _ _ Bw hj τ hτ LL' hLL
  let jE : D.host.E →+* Om l := Bw.j.comp (algebraMap D.host.E D.nd.Om)
  have hA := D.nd.plOm.2 w
  have hw := hj.mem_placesOver hA
  have hjE : ∀ x : 𝓞 D.host.E, ‖jE (x : D.host.E)‖ < 1 ↔ x ∈ w.asIdeal := fun x =>
    (hj.valuation_lt_one_iff _).symm.trans (hA x)
  have iso := norm_eq_of_same_place τ jE w hw hτ hjE
  have hker : ∀ t ∈ RingHom.ker (scalarLift jE), scalarLift τ t = 0 := fun t ht =>
    norm_eq_zero.1 (le_antisymm ((norm_scalarLift_le jE τ (fun x => (iso x).symm) t).trans
      (by rw [RingHom.mem_ker.1 ht, norm_zero])) (norm_nonneg _))
  have hrange : (scalarLift jE).range ≤ Bw.Kw.1.toSubalgebra := by
    rintro _ ⟨t, rfl⟩
    induction t using TensorProduct.inductionOn with
    | tmul a y =>
      change scalarLift jE (a ⊗ₜ y) ∈ _
      rw [scalarLift_tmul]
      exact mul_mem (Bw.Kw.1.algebraMap_mem a) (Bw.j_E y)
    | add t₁ t₂ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
  have hfin : FiniteDimensional ℚ_[l] (Subalgebra.toSubmodule (scalarLift jE).range) := by
    have : FiniteDimensional ℚ_[l] (Subalgebra.toSubmodule Bw.Kw.1.toSubalgebra) := Bw.Kw.2
    exact Submodule.finiteDimensional_of_le (Subalgebra.toSubmodule.monotone hrange)
  have hclosed : IsClosed ((scalarLift jE).range : Set (Om l)) :=
    Submodule.isClosed_of_finiteDimensional (Subalgebra.toSubmodule (scalarLift jE).range)
  have hle : Bw.Kw.1.toSubalgebra ≤ (scalarLift jE).range := by
    intro y hy
    refine closure_minimal ?_ hclosed (Bw.j_dense hy)
    rintro _ ⟨x, rfl⟩
    exact ⟨1 ⊗ₜ x, by change scalarLift jE (1 ⊗ₜ x) = jE x; rw [scalarLift_tmul, map_one, one_mul]⟩
  let σ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] Om l :=
    ((Ideal.Quotient.liftₐ (RingHom.ker (scalarLift jE)) (scalarLift τ) hker).comp
      (Ideal.quotientKerEquivRange (scalarLift jE)).symm.toAlgHom).comp (Subalgebra.inclusion hle)
  refine ⟨σ.codRestrict LL'.1.toSubalgebra (fun y => hLL (Bw.LL_split σ y)), fun x => ?_⟩
  have key : (Ideal.quotientKerEquivRange (scalarLift jE)).symm
      (Subalgebra.inclusion hle ⟨jE x, Bw.j_E x⟩) = Ideal.Quotient.mk _ (1 ⊗ₜ x) := by
    rw [AlgEquiv.symm_apply_eq]
    apply Subtype.ext
    change jE x = scalarLift jE (1 ⊗ₜ x)
    rw [scalarLift_tmul, map_one, one_mul]
  change τ x = σ ⟨jE x, Bw.j_E x⟩
  change τ x = Ideal.Quotient.liftₐ _ (scalarLift τ) hker ((Ideal.quotientKerEquivRange (scalarLift jE)).symm
    (Subalgebra.inclusion hle ⟨jE x, Bw.j_E x⟩))
  rw [key, Ideal.Quotient.liftₐ_apply]
  change τ x = scalarLift τ (1 ⊗ₜ x)
  rw [scalarLift_tmul, map_one, one_mul]

end GlobalTheory.EmbExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCompletionEmbeddingInducingHostEmbeddingStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open Formalism.BasicNotions.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_completionEmbedding_inducing_hostEmbedding : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (w : PlE D.host) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) O), GlobalTheory.Pst.Induces Bw → ∀ τ : D.host.E →+* Qbar l, (∀ x : 𝓞 D.host.E, ‖τ (x : D.host.E)‖ < 1 ↔ x ∈ w.asIdeal) → ∀ LL' : FinExt l, Bw.LL.1 ≤ LL'.1 → ∃ τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1, GlobalTheory.Pst.IsInduced Bw τ τ' := by
  first | exact @GlobalTheory.EmbExt.main | exact GlobalTheory.EmbExt.main | (intros; apply GlobalTheory.EmbExt.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRealSubfieldPlaceInRamifiedSet
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRealSubfieldPlaceInRamifiedSet
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GeoUnder

theorem exists_under_in_qPl : ∀ (D : D7) (χ : HChar D.host.E) (w : PlE D.host), (∀ k, w ∉ placesOver D.host.E (D.host.g k)) → ¬ χ.UnrAt w → ∃ v, NG.OverPl w v ∧ v ∈ qPl D χ := by
  intro D χ w hg hχ
  have hne : w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) ≠ ⊥ := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
    have hint : IsIntegral ℤ x := Algebra.IsIntegral.isIntegral x
    exact Ideal.comap_ne_bot_of_integral_mem hx0 hx (hint.tower_top)
  let v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) :=
    { asIdeal := w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E))
      isPrime := Ideal.comap_isPrime _ _
      ne_bot := hne }
  refine ⟨v, rfl, ?_, w, rfl, hχ⟩
  rintro ⟨w', hw', k, hk⟩
  apply hg k
  have h1 : ((D.host.g k : ℕ) : 𝓞 (maximalRealSubfield D.host.E)) ∈ v.asIdeal := by
    rw [← hw']
    show algebraMap _ _ _ ∈ w'.asIdeal
    rw [map_natCast]; exact hk
  show ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal
  have h2 := h1
  change algebraMap _ _ _ ∈ w.asIdeal at h2
  rwa [map_natCast] at h2

end GlobalTheory.GeoUnder
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRealSubfieldPlaceInRamifiedSetStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_realSubfield_place_in_ramified_set : ∀ (D : D7) (χ : HChar D.host.E) (w : PlE D.host), (∀ k, w ∉ placesOver D.host.E (D.host.g k)) → ¬ χ.UnrAt w → ∃ v, NG.OverPl w v ∧ v ∈ qPl D χ := by
  first | exact @GlobalTheory.GeoUnder.exists_under_in_qPl | exact GlobalTheory.GeoUnder.exists_under_in_qPl | (intros; apply GlobalTheory.GeoUnder.exists_under_in_qPl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleSubquotientCommonEigenvector
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleSubquotientCommonEigenvector
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace GlobalTheory.EigenSubquot

open GlobalTheory.SmGL

theorem exists_irreducible_subquotient_eigen : ∀ (G : Type) [Group G] (V : Type) [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ G V) (S : Set G) (θ : G → ℂ) (x : V), x ≠ 0 →
    (∀ g ∈ S, ρ g x = θ g • x) → ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y)
      (τ : Representation ℂ G Y), τ.IsIrreducible ∧ IsSubquotient τ ρ ∧
        ∃ y : Y, y ≠ 0 ∧ ∀ g ∈ S, τ g y = θ g • y := by
  intro G _ V _ _ ρ S θ x hx hθ
  let S0 : Submodule ℂ V := Submodule.span ℂ (Set.range fun g : G => ρ g x)
  have hS0 : ∀ (g : G) ⦃v : V⦄, v ∈ S0 → ρ g v ∈ S0 := by
    intro g v hv
    have : S0 ≤ S0.comap (ρ g) := Submodule.span_le.2 (by
      rintro _ ⟨h, rfl⟩
      exact Submodule.subset_span ⟨g * h, by simp [map_mul]⟩)
    exact this hv
  have hxS0 : x ∈ S0 := Submodule.subset_span ⟨1, by simp⟩
  have hgen : ∀ R : Submodule ℂ V, (∀ (g : G) ⦃v : V⦄, v ∈ R → ρ g v ∈ R) → x ∈ R → S0 ≤ R := by
    intro R hR hxR
    exact Submodule.span_le.2 (by rintro _ ⟨h, rfl⟩; exact hR h hxR)
  let P : Set (Submodule ℂ V) := {T | T ≤ S0 ∧ x ∉ T ∧ ∀ (g : G) ⦃v : V⦄, v ∈ T → ρ g v ∈ T}
  have hbot : (⊥ : Submodule ℂ V) ∈ P := ⟨bot_le, by simpa using hx, fun g v hv => by
    rw [(Submodule.mem_bot ℂ).1 hv, map_zero]; exact zero_mem _⟩
  obtain ⟨T, -, hT⟩ := zorn_le_nonempty₀ P (fun c hcP hc y hy => by
    have hne : c.Nonempty := ⟨y, hy⟩
    have hdir : DirectedOn (· ≤ ·) c := hc.directedOn
    refine ⟨sSup c, ⟨sSup_le fun z hz => (hcP hz).1, fun hmem => ?_, fun g v hv => ?_⟩,
      fun z hz => le_sSup hz⟩
    · obtain ⟨z, hz, hxz⟩ := (Submodule.mem_sSup_of_directed hne hdir).1 hmem
      exact (hcP hz).2.1 hxz
    · obtain ⟨z, hz, hvz⟩ := (Submodule.mem_sSup_of_directed hne hdir).1 hv
      exact (Submodule.mem_sSup_of_directed hne hdir).2 ⟨z, hz, (hcP hz).2.2 g hvz⟩) ⊥ hbot
  obtain ⟨hTS, hxT, hTst⟩ := hT.prop
  let Sr : Subrepresentation ρ := ⟨S0, hS0⟩
  let Tr : Subrepresentation ρ := ⟨T, hTst⟩
  have hcov : Tr ⋖ Sr := by
    refine ⟨lt_of_le_of_ne (fun v hv => hTS hv) fun h => hxT ?_, fun R h1 h2 => ?_⟩
    · have : x ∈ Sr := hxS0
      rw [← h] at this
      exact this
    by_cases hxR : x ∈ R.toSubmodule
    · exact h2.not_ge fun v hv => hgen R.toSubmodule R.apply_mem_toSubmodule hxR hv
    · have hRP : R.toSubmodule ∈ P := ⟨fun v hv => h2.le hv, hxR, R.apply_mem_toSubmodule⟩
      have hle : T ≤ R.toSubmodule := fun v hv => h1.le hv
      exact h1.not_ge fun v hv => hT.2 hRP hle hv
  refine ⟨_, _, _, subQuot Sr Tr, isIrreducible_subQuot hcov,
    ⟨Sr, ⟨Submodule.mkQ _, fun _ => rfl⟩, Submodule.Quotient.mk_surjective _⟩,
    Submodule.Quotient.mk ⟨x, hxS0⟩, ?_, fun g hg => ?_⟩
  · intro h0
    have h1 := (Submodule.Quotient.mk_eq_zero (T.comap S0.subtype) (x := (⟨x, hxS0⟩ : S0))).1 h0
    exact hxT h1
  · show Submodule.Quotient.mk (Sr.toRepresentation g ⟨x, hxS0⟩) = _
    rw [← Submodule.Quotient.mk_smul]
    congr 1
    exact Subtype.ext (hθ g hg)

end GlobalTheory.EigenSubquot
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleSubquotientCommonEigenvectorStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_irreducible_subquotient_common_eigenvector : ∀ (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (S : Set G) (θ : G → ℂ) (x : V), x ≠ 0 → (∀ g ∈ S, ρ g x = θ g • x) → ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (τ : Representation ℂ G Y), τ.IsIrreducible ∧ IsSubquotient τ ρ ∧ ∃ y : Y, y ≠ 0 ∧ ∀ g ∈ S, τ g y = θ g • y := by
  first | exact @GlobalTheory.EigenSubquot.exists_irreducible_subquotient_eigen | exact GlobalTheory.EigenSubquot.exists_irreducible_subquotient_eigen | (intros; apply GlobalTheory.EigenSubquot.exists_irreducible_subquotient_eigen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivariantIsoOfTranslationStableGraph
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivariantIsoOfTranslationStableGraph
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem isoRep_of_stable_graph : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] (ρa : Representation ℂ (GQ L n) A) (ρb : Representation ℂ (GQ L n) B) (S₁ : Submodule ℂ (GAf L n → A)) (S₂ : Submodule ℂ (GAf L n → B)) (W : Submodule ℂ ((GAf L n → A) × (GAf L n → B))), NG.IsIrrRep ρa S₁ → NG.IsIrrRep ρb S₂ → (∀ w ∈ W, w.1 ∈ S₁ ∧ w.2 ∈ S₂) → (∀ h, ∀ w ∈ W, (NG.rt L n h w.1, NG.rt L n h w.2) ∈ W) → (∀ u, ((0 : GAf L n → A), u) ∈ W → u = 0) → (∀ u, (u, (0 : GAf L n → B)) ∈ W → u = 0) → W ≠ ⊥ → NG.IsoRep S₁ S₂ := by
  intro L _ _ _ n A B _ _ _ _ ρa ρb S₁ S₂ W h₁ h₂ hW hst h0 h0' hne
  have inj1 : ∀ w ∈ W, w.1 = 0 → w = 0 := by
    intro w hw e
    have : w = (0, w.2) := Prod.ext e rfl
    have h2 := h0 w.2 (this ▸ hw)
    exact Prod.ext e h2
  have inj2 : ∀ w ∈ W, w.2 = 0 → w = 0 := by
    intro w hw e
    have : w = (w.1, 0) := Prod.ext rfl e
    have h2 := h0' w.1 (this ▸ hw)
    exact Prod.ext h2 e
  obtain ⟨w₀, hw₀, hw₀ne⟩ := (Submodule.ne_bot_iff W).1 hne
  have le1 : W.map (LinearMap.fst ℂ _ _) ≤ S₁ := by
    rintro _ ⟨w, hw, rfl⟩; exact (hW w hw).1
  have le2 : W.map (LinearMap.snd ℂ _ _) ≤ S₂ := by
    rintro _ ⟨w, hw, rfl⟩; exact (hW w hw).2
  have e1 : W.map (LinearMap.fst ℂ _ _) = S₁ := by
    refine (h₁.2.2 _ ⟨le1.trans h₁.1.1, ?_⟩ le1).resolve_left ?_
    · rintro h _ ⟨w, hw, rfl⟩
      exact ⟨_, hst h w hw, rfl⟩
    · intro hb
      have : w₀.1 ∈ W.map (LinearMap.fst ℂ _ _) := ⟨w₀, hw₀, rfl⟩
      rw [hb, Submodule.mem_bot] at this
      exact hw₀ne (inj1 w₀ hw₀ this)
  have e2 : W.map (LinearMap.snd ℂ _ _) = S₂ := by
    refine (h₂.2.2 _ ⟨le2.trans h₂.1.1, ?_⟩ le2).resolve_left ?_
    · rintro h _ ⟨w, hw, rfl⟩
      exact ⟨_, hst h w hw, rfl⟩
    · intro hb
      have : w₀.2 ∈ W.map (LinearMap.snd ℂ _ _) := ⟨w₀, hw₀, rfl⟩
      rw [hb, Submodule.mem_bot] at this
      exact hw₀ne (inj2 w₀ hw₀ this)
  let p₁ : W →ₗ[ℂ] S₁ := ((LinearMap.fst ℂ _ _).comp W.subtype).codRestrict S₁ (fun w => (hW w.1 w.2).1)
  let p₂ : W →ₗ[ℂ] S₂ := ((LinearMap.snd ℂ _ _).comp W.subtype).codRestrict S₂ (fun w => (hW w.1 w.2).2)
  have b₁ : Function.Bijective p₁ := by
    refine ⟨(injective_iff_map_eq_zero p₁).2 fun w hw => ?_, fun f => ?_⟩
    · exact Subtype.ext (inj1 w.1 w.2 (congrArg Subtype.val hw))
    · have : f.1 ∈ W.map (LinearMap.fst ℂ _ _) := by rw [e1]; exact f.2
      obtain ⟨w, hw, e⟩ := this
      exact ⟨⟨w, hw⟩, Subtype.ext e⟩
  have b₂ : Function.Bijective p₂ := by
    refine ⟨(injective_iff_map_eq_zero p₂).2 fun w hw => ?_, fun f => ?_⟩
    · exact Subtype.ext (inj2 w.1 w.2 (congrArg Subtype.val hw))
    · have : f.1 ∈ W.map (LinearMap.snd ℂ _ _) := by rw [e2]; exact f.2
      obtain ⟨w, hw, e⟩ := this
      exact ⟨⟨w, hw⟩, Subtype.ext e⟩
  refine ⟨(LinearEquiv.ofBijective p₁ b₁).symm.trans (LinearEquiv.ofBijective p₂ b₂), ?_⟩
  intro h f f' hf
  obtain ⟨w, rfl⟩ := b₁.2 f
  have hf' : f' = p₁ ⟨_, hst h w.1 w.2⟩ := Subtype.ext hf
  subst hf'
  have key : ∀ v : W, ((LinearEquiv.ofBijective p₁ b₁).symm.trans (LinearEquiv.ofBijective p₂ b₂)) (p₁ v) = p₂ v := by
    intro v
    have : (LinearEquiv.ofBijective p₁ b₁).symm (p₁ v) = v :=
      (LinearEquiv.ofBijective p₁ b₁).symm_apply_apply v
    rw [LinearEquiv.trans_apply, this]; rfl
  rw [key, key]
  rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivariantIsoOfTranslationStableGraphStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equivariant_iso_of_translationStable_graph : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] (ρa : Representation ℂ (GQ L n) A) (ρb : Representation ℂ (GQ L n) B) (S₁ : Submodule ℂ (GAf L n → A)) (S₂ : Submodule ℂ (GAf L n → B)) (W : Submodule ℂ ((GAf L n → A) × (GAf L n → B))), NG.IsIrrRep ρa S₁ → NG.IsIrrRep ρb S₂ → (∀ w ∈ W, w.1 ∈ S₁ ∧ w.2 ∈ S₂) → (∀ h, ∀ w ∈ W, (NG.rt L n h w.1, NG.rt L n h w.2) ∈ W) → (∀ u, ((0 : GAf L n → A), u) ∈ W → u = 0) → (∀ u, (u, (0 : GAf L n → B)) ∈ W → u = 0) → W ≠ ⊥ → NG.IsoRep S₁ S₂ := by
  first | exact @GlobalTheory.isoRep_of_stable_graph | exact GlobalTheory.isoRep_of_stable_graph | (intros; apply GlobalTheory.isoRep_of_stable_graph <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFinitePlaceOverLOfHostEmbeddingQbar
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFinitePlaceOverLOfHostEmbeddingQbar
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open Formalism.BasicNotions.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.PlaceOfEmb

theorem norm_le_one_of_isIntegral' {K : Type} [NormedField K] [IsUltrametricDist K] {x : K}
    (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  have := (Valuation.integer.integers (NormedField.valuation (K := K))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at this
  exact_mod_cast this

variable {E : Type} [Field E] [NumberField E] {C : Type} [NormedField C] [IsUltrametricDist C]

theorem norm_map_le_one (τ : E →+* C) (x : 𝓞 E) : ‖τ (x : E)‖ ≤ 1 :=
  norm_le_one_of_isIntegral' ((x.isIntegral_coe).map (τ.toIntAlgHom))

def ballIdeal (τ : E →+* C) : Ideal (𝓞 E) where
  carrier := {x | ‖τ (x : E)‖ < 1}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    change ‖τ (a : E)‖ < 1 at ha
    change ‖τ (b : E)‖ < 1 at hb
    change ‖τ ((a : E) + (b : E))‖ < 1
    rw [map_add (f := _)]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
  smul_mem' := by
    intro c x hx
    change ‖τ (x : E)‖ < 1 at hx
    change ‖τ ((c : E) * (x : E))‖ < 1
    rw [map_mul, norm_mul]
    calc ‖τ (c : E)‖ * ‖τ (x : E)‖ ≤ 1 * ‖τ (x : E)‖ :=
          mul_le_mul_of_nonneg_right (norm_map_le_one τ c) (norm_nonneg _)
      _ < 1 := by rw [one_mul]; exact hx

theorem mem_ballIdeal (τ : E →+* C) (x : 𝓞 E) : x ∈ ballIdeal τ ↔ ‖τ (x : E)‖ < 1 := Iff.rfl

theorem ballIdeal_isPrime (τ : E →+* C) : (ballIdeal τ).IsPrime := by
  refine ⟨?_, ?_⟩
  · rw [Ideal.ne_top_iff_one, mem_ballIdeal]; simp
  · intro a b hab
    change ‖τ ((a : E) * (b : E))‖ < 1 at hab
    rw [map_mul, norm_mul] at hab
    by_contra h
    push_neg at h
    rw [mem_ballIdeal, mem_ballIdeal] at h
    have ha : ‖τ (a : E)‖ = 1 := le_antisymm (norm_map_le_one τ a) (not_lt.1 h.1)
    have hb : ‖τ (b : E)‖ = 1 := le_antisymm (norm_map_le_one τ b) (not_lt.1 h.2)
    rw [ha, hb] at hab; norm_num at hab

end GlobalTheory.PlaceOfEmb

open GlobalTheory.PlaceOfEmb in
theorem GlobalTheory.PlaceOfEmb.exists_place_of_emb : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (τ : D.host.E →+* Qbar l), ∃ w : PlE D.host, w ∈ placesOver D.host.E l ∧ ∀ x : 𝓞 D.host.E, ‖τ (x : D.host.E)‖ < 1 ↔ x ∈ w.asIdeal := by
  intro D l _ τ
  have hl : ((l : 𝓞 D.host.E)) ∈ ballIdeal τ := by
    rw [mem_ballIdeal]
    simp only [map_natCast]
    rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends, Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  have hne : ballIdeal τ ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hl
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) hl
  refine ⟨⟨ballIdeal τ, ballIdeal_isPrime τ, hne⟩, hl, fun x => Iff.rfl⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFinitePlaceOverLOfHostEmbeddingQbarStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open Formalism.BasicNotions.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finitePlace_over_l_of_hostEmbedding_qbar : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (τ : D.host.E →+* Qbar l), ∃ w : PlE D.host, w ∈ placesOver D.host.E l ∧ ∀ x : 𝓞 D.host.E, ‖τ (x : D.host.E)‖ < 1 ↔ x ∈ w.asIdeal := by
  first | exact @GlobalTheory.PlaceOfEmb.exists_place_of_emb | exact GlobalTheory.PlaceOfEmb.exists_place_of_emb | (intros; apply GlobalTheory.PlaceOfEmb.exists_place_of_emb <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLeviBlockEigenvectorAtIdentity
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLeviBlockEigenvectorAtIdentity
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
open Matrix ValuativeRel

noncomputable section

namespace GlobalTheory.SphBlock

theorem exists_eigen_at_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α : Type) [Fintype α] [LinearOrder α] (m : α → Type) [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] (n : Type) [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) (X : α → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (σ : ∀ a, Representation ℂ (GL (m a) k) (X a)) (χ : kˣ →* ℂˣ) (x : IndSp e (piTensor σ)), x ≠ 0 → (∀ g ∈ KO k n, multiProd e σ g x = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • x) → ∃ w : PiTensorProduct ℂ X, w ≠ 0 ∧ ∀ a, ∀ h ∈ KO k (m a), piTensor σ (Pi.mulSingle a h) w = (χ (Matrix.GeneralLinearGroup.det h) : ℂ) • w := by
  intro k _ _ _ _ α _ _ m _ _ n _ _ e X _ _ σ χ x hx hK
  classical
  set f := x.1.1 with hf
  have hval : ∀ {d : Type} [Fintype d] [DecidableEq d] {g : GL d k}, g ∈ KO k d →
      valuation k (GeneralLinearGroup.det g : k) = 1 := by
    intro d _ _ g hg
    obtain ⟨g, rfl⟩ := hg
    have h1 : ((GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap 𝒪[k] k) g) : kˣ) : k) =
        algebraMap 𝒪[k] k (GeneralLinearGroup.det g : 𝒪[k]ˣ) :=
      ((algebraMap 𝒪[k] k).map_det _).symm
    rw [h1]
    exact (Valuation.integer.integers (valuation k)).one_of_isUnit (Units.isUnit _)
  have hfK : ∀ κ ∈ KO k n, f κ = (χ (GeneralLinearGroup.det κ) : ℂ) • f 1 := by
    intro κ hκ
    have h := congrArg (fun y : IndSp e (piTensor σ) => y.1.1 1) (hK κ hκ)
    have h2 : (multiProd e σ κ x).1.1 1 = f (1 * κ) := parInd_apply e (piTensor σ) κ 1 x
    rw [h2, one_mul] at h
    exact h
  refine ⟨f 1, ?_, ?_⟩
  · intro h0
    apply hx
    have hall : ∀ g, f g = 0 := by
      intro g
      obtain ⟨u, l, κ, hκ, rfl⟩ := UnitInd.exists_iwasawa e g
      let p : parab k e := ⟨(u : GL n k) * leviEmb k e l,
        mul_mem (unipRad_le_parab k e u.2) (leviEmb_mem_parab k e l)⟩
      have := parInd_law e (piTensor σ) x p κ
      change f ((u : GL n k) * leviEmb k e l * κ) = _ at this
      rw [this, show x.1.1 κ = f κ from rfl, hfK κ hκ, h0, smul_zero, map_zero, smul_zero]
    apply Subtype.ext; apply Subtype.ext; funext g
    exact hall g
  · intro a h hh
    set l : Levi k m := Pi.mulSingle a h with hl
    have hlK : ∀ b, l b ∈ KO k (m b) := by
      intro b
      by_cases hb : b = a
      · subst hb; simp [l, hh]
      · simp [l, Pi.mulSingle_eq_of_ne hb, one_mem]
    have hemb : leviEmb k e l ∈ KO k n := by
      have := (UnitInd.unip_mul_levi_mem_KO e (1 : unipRad k e) l).2 ⟨one_mem _, hlK⟩
      simpa using this
    have hdet : GeneralLinearGroup.det (leviEmb k e l) = GeneralLinearGroup.det h := by
      rw [det_leviEmb, Finset.prod_eq_single a]
      · simp [l]
      · intro b _ hb; simp [l, Pi.mulSingle_eq_of_ne hb]
      · simp
    have hδ : deltaHalf k m l = 1 := by
      rw [deltaHalf_apply]
      refine Finset.prod_eq_one fun b _ => isUnram_absPow k _ _ (hval (hlK b))
    let p : parab k e := ⟨leviEmb k e l, leviEmb_mem_parab k e l⟩
    have hlaw := parInd_law e (piTensor σ) x p 1
    have hp : leviProj k e p = l := leviProj_leviEmb k e l
    rw [mul_one, hp, hδ, Units.val_one, one_smul] at hlaw
    change f (leviEmb k e l) = piTensor σ l (f 1) at hlaw
    rw [hfK _ hemb, hdet] at hlaw
    exact hlaw.symm

end GlobalTheory.SphBlock
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLeviBlockEigenvectorAtIdentityStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_levi_block_eigenvector_at_identity : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α : Type) [Fintype α] [LinearOrder α] (m : α → Type) [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] (n : Type) [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) (X : α → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (σ : ∀ a, Representation ℂ (GL (m a) k) (X a)) (χ : kˣ →* ℂˣ) (x : IndSp e (piTensor σ)), x ≠ 0 → (∀ g ∈ KO k n, multiProd e σ g x = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • x) → ∃ w : PiTensorProduct ℂ X, w ≠ 0 ∧ ∀ a, ∀ h ∈ KO k (m a), piTensor σ (Pi.mulSingle a h) w = (χ (Matrix.GeneralLinearGroup.det h) : ℂ) • w := by
  first | exact @GlobalTheory.SphBlock.exists_eigen_at_one | exact GlobalTheory.SphBlock.exists_eigen_at_one | (intros; apply GlobalTheory.SphBlock.exists_eigen_at_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaPairingOfInvariantTrilinearForm
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaPairingOfInvariantTrilinearForm
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [local instance] GlobalTheory.NPin.ThetaMod.acg GlobalTheory.NPin.ThetaMod.mod

namespace GlobalTheory.ThetaRiesz

theorem thetaPair_of_invariant_form : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r n : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (μ : kˣ →* ℂˣ) (σ : Representation ℂ (GL (Fin r) k) V) (π : Representation ℂ (GL (Fin n) k) W), IsAdmissible σ → IsUnitarisable σ → IsOpen (μ.ker : Set kˣ) → ∀ (b : SB (Matrix (Fin n) (Fin r) k) →ₗ[ℂ] W →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ), b ≠ 0 → (∀ (g : GL (Fin r) k) (h : GL (Fin n) k) (Φ Φ' : SB (Matrix (Fin n) (Fin r) k)), (Φ' : Matrix (Fin n) (Fin r) k → ℂ) = om μ g h Φ → ∀ a c, b Φ' (π h a) (σ g c) = b Φ a c) → ThetaPair μ σ π := by
  intro k _ _ _ _ r n V W _ _ _ _ μ σ π hadm hunit hμ b hb hb_inv
  obtain ⟨Bf, hsym, hpos, hinv⟩ := hunit
  obtain ⟨hone, hmul, -, -, hop⟩ := om_isSmoothRepresentation k (Fin r) (Fin n) μ hμ

  have huniq : ∀ u u' : V, (∀ w, Bf u w = Bf u' w) → u = u' := by
    intro u u' h
    by_contra hne
    have hne' : u - u' ≠ 0 := sub_ne_zero.2 hne
    have hfun : Bf (u - u') = 0 := by rw [map_sub, LinearMap.ext h, sub_self]
    have h0 : Bf (u - u') (u - u') = 0 := by rw [hfun, LinearMap.zero_apply]
    have := hpos _ hne'
    rw [h0] at this
    simp at this

  let S : SB (Matrix (Fin n) (Fin r) k) → Subgroup (GL (Fin r) k) := fun Φ =>
    { carrier := {g | om μ g 1 (Φ : Matrix (Fin n) (Fin r) k → ℂ) = Φ}
      one_mem' := hone _
      mul_mem' := by
        intro x y hx hy
        show om μ (x * y) 1 _ = _
        have := hmul x y 1 1 (Φ : Matrix (Fin n) (Fin r) k → ℂ)
        rw [mul_one] at this
        rw [this]
        have hy' : om μ y 1 (Φ : Matrix (Fin n) (Fin r) k → ℂ) = Φ := hy
        have hx' : om μ x 1 (Φ : Matrix (Fin n) (Fin r) k → ℂ) = Φ := hx
        rw [hy', hx']
      inv_mem' := by
        intro x hx
        have hx' : om μ x 1 (Φ : Matrix (Fin n) (Fin r) k → ℂ) = Φ := hx
        show om μ x⁻¹ 1 _ = _
        have := hmul x⁻¹ x 1 1 (Φ : Matrix (Fin n) (Fin r) k → ℂ)
        rw [inv_mul_cancel, mul_one, hx', hone] at this
        exact this.symm }
  have hSo : ∀ Φ, IsOpen ((S Φ : Subgroup _) : Set (GL (Fin r) k)) := by
    intro Φ
    have h1 := hop _ Φ.2
    have hc : Continuous (fun g : GL (Fin r) k => (g, (1 : GL (Fin n) k))) :=
      continuous_id.prodMk continuous_const
    exact h1.preimage hc
  have hL : ∀ Φ a, ∀ s ∈ S Φ, ∀ w, b Φ a (σ s w) = b Φ a w := by
    intro Φ a s hs w
    have hs' : om μ s 1 (Φ : Matrix (Fin n) (Fin r) k → ℂ) = Φ := hs
    have := hb_inv s 1 Φ Φ hs'.symm a w
    simpa using this
  have hex : ∀ Φ a, ∃ u : V, ∀ w, b Φ a w = Bf u w := fun Φ a =>
    exists_vector_of_smooth_antilinear k r V σ Bf hadm hsym hpos hinv (b Φ a) (S Φ) (hSo Φ) (hL Φ a)
  choose f hf using hex
  have hadd1 : ∀ Φ Ψ a, f (Φ + Ψ) a = f Φ a + f Ψ a := fun Φ Ψ a =>
    huniq _ _ fun w => by rw [← hf, map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, hf, hf, map_add (f := _), LinearMap.add_apply]
  have hsmul1 : ∀ (z : ℂ) Φ a, f (z • Φ) a = z • f Φ a := fun z Φ a =>
    huniq _ _ fun w => by rw [← hf, map_smul, LinearMap.smul_apply, LinearMap.smul_apply, hf, map_smul, LinearMap.smul_apply]
  have hadd2 : ∀ Φ a a', f Φ (a + a') = f Φ a + f Φ a' := fun Φ a a' =>
    huniq _ _ fun w => by rw [← hf, map_add (f := _), LinearMap.add_apply, hf, hf, map_add (f := _), LinearMap.add_apply]
  have hsmul2 : ∀ (z : ℂ) Φ a, f Φ (z • a) = z • f Φ a := fun z Φ a =>
    huniq _ _ fun w => by rw [← hf, map_smul, LinearMap.smul_apply, hf, map_smul, LinearMap.smul_apply]
  let B : SB (Matrix (Fin n) (Fin r) k) →ₗ[ℂ] W →ₗ[ℂ] V :=
    LinearMap.mk₂ ℂ f hadd1 hsmul1 hadd2 hsmul2
  have hB : ∀ Φ a, B Φ a = f Φ a := fun _ _ => rfl
  refine ⟨B, ?_, ?_⟩
  · intro h0
    apply hb
    ext Φ a w
    rw [hf, ← hB, h0]
    simp
  · intro g h Φ Φ' hΦ F
    rw [hB, hB]
    apply huniq
    intro c
    have hc : σ g (σ g⁻¹ c) = c := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
    rw [← hf, ← hc, hb_inv g h Φ Φ' hΦ F, hf, ← hinv g (f Φ F) (σ g⁻¹ c)]

end GlobalTheory.ThetaRiesz
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaPairingOfInvariantTrilinearFormStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [local instance] GlobalTheory.NPin.ThetaMod.acg GlobalTheory.NPin.ThetaMod.mod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaPairing_of_invariant_trilinear_form : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r n : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (μ : kˣ →* ℂˣ) (σ : Representation ℂ (GL (Fin r) k) V) (π : Representation ℂ (GL (Fin n) k) W), IsAdmissible σ → IsUnitarisable σ → IsOpen (μ.ker : Set kˣ) → ∀ (b : SB (Matrix (Fin n) (Fin r) k) →ₗ[ℂ] W →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ), b ≠ 0 → (∀ (g : GL (Fin r) k) (h : GL (Fin n) k) (Φ Φ' : SB (Matrix (Fin n) (Fin r) k)), (Φ' : Matrix (Fin n) (Fin r) k → ℂ) = om μ g h Φ → ∀ a c, b Φ' (π h a) (σ g c) = b Φ a c) → ThetaPair μ σ π := by
  first | exact @GlobalTheory.ThetaRiesz.thetaPair_of_invariant_form | exact GlobalTheory.ThetaRiesz.thetaPair_of_invariant_form | (intros; apply GlobalTheory.ThetaRiesz.thetaPair_of_invariant_form <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairKernelLawOfFiniteDatumLaw
section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.LevelNeQ
noncomputable section

namespace GlobalTheory.ShortOwnCompare

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

variable {D : D7}

theorem level_ne_q (D : D7) (i : Fin 2) : D.host.g i ≠ D.host.q := by
  intro e
  have hc := D.ntypes.g_cond i
  have hq := D.host.hyp.1
  have h1 : D.host.g i % D.host.q = 1 % D.host.q := by
    rw [← Nat.mod_mod_of_dvd _ (show D.host.q ∣ D.host.QS * D.host.q * D.host.d from
      ⟨D.host.QS * D.host.d, by ring⟩), hc]
  rw [e, Nat.mod_self, Nat.mod_eq_of_lt hq.one_lt] at h1
  exact zero_ne_one h1

end GlobalTheory.ShortOwnCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairKernelLawOfFiniteDatumLaw
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms Formalism.L2.Col Formalism.L2.DIV Formalism.HermitianLatticesTheory GlobalTheory.KerJ NumberField IsDedekindDomain Classical

namespace GlobalTheory.KFiDat

theorem termLaw_of_xi : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.X.Ok → IsSel t.X t.sel → (∀ i, t.Pr.g i ∈ t.S) → (∀ v, t.Pr.T v ∈ t.S) → (∀ l ∈ D.host.small, l ∈ t.S) → D.host.q ∈ t.S → (∃ eta, t.Ch.Tied t.glob.σ₀ (fun j τ => (D.hc (t.seam.iT τ)).e j) t.glob.mu0 eta) → ∀ u μ i, i < D.R.m → ∀ (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)) (γ : UF t.X.E (D.R.N (i + 1))) (k : t.X.K), gmap γ.1 ((t.rd u μ).N (i + 1) c') = (t.rd u μ).N (i + 1) c' → (∀ x, ∀ z ∈ mulLat (t.rd u μ).lev (homAt (t.rd u μ).SS ((t.rd u μ).N i c) ((t.rd u μ).N (i + 1) c')), (t.rd u μ).Xi i c c' (x + z) = (t.rd u μ).Xi i c c' x) → (∀ x, (t.rd u μ).Xi i c c' (γ.1.toLinearMap ∘ₗ x) * t.seam.σ₀ (∏ P : rowSG t.Pr t.sel (t.tup μ), muAt t.Ch t.sel (t.tup μ) (t.cst μ) i P ((LinearEquiv.det γ.1 : t.X.Eˣ) : t.X.E)) = t.seam.σ₀ k * (t.rd u μ).Xi i c c' x) → TermLaw (t.O u μ) i c c' (matE t.seam γ.1, t.seam.σ₀ k) := by
  intro D L hT Gi Gl K Y cX ex t hX hsel hgS hTS h2S hqS hTied u μ i hi c c' γ k hγ hΞ hXi
  obtain ⟨eta, hTied⟩ := hTied
  have hok := t.seam_ok
  obtain ⟨hSS, hlev, -⟩ := t.rd_chain u μ
  set z : t.X.E := ((LinearEquiv.det γ.1 : t.X.Eˣ) : t.X.E) with hz
  have hz0 : z ≠ 0 := Units.ne_zero _
  have hSD' : IsSDLat D.host.E _ (t.seam.lat ((t.rd u μ).N (i + 1) c')) :=
    t.O_lat u μ (i + 1) c' ▸ ((t.O u μ).lat (i + 1) c').2
  obtain ⟨hzs, hzi, hprod1⟩ := GlobalTheory.T.det_unitaryStabiliser_selfDualLattice_normOne D t.X t.seam t.χ hok t.χ_ok _ _ hSD' γ hγ
  let eZ : Fin D.R.m → t.X.Tau → ℤ := fun j τ => (D.chTw u μ).sDiv j (t.seam.iT τ) + ((D.R.N j / 2 : ℕ) : ℤ)
  have heZ : ∀ j τ, ((eZ j τ : ℤ) : ℚ) = (D.hc (t.seam.iT τ)).e j := by
    intro j τ
    have h1 := (D.chTw u μ).sDiv_eq j j.2 (t.seam.iT τ)
    rw [D.hcW_e] at h1
    obtain ⟨m, hm⟩ := rank_even D.R j
    have h2 : ((D.R.N j / 2 : ℕ) : ℚ) = (D.R.N j : ℚ) / 2 := by
      rw [hm]; push_cast; rw [show m + m = 2 * m by ring, Nat.mul_div_cancel_left _ two_pos]; push_cast; ring
    simp only [eZ]
    rw [Int.cast_add, h1, Int.cast_natCast, h2, sExp, Nat.add_sub_cancel]
    ring
  have hTied' : t.Ch.Tied t.glob.σ₀ (fun j τ => ((eZ j τ : ℤ) : ℚ)) t.glob.mu0 eta := by
    have e : (fun j τ => ((eZ j τ : ℤ) : ℚ)) = (fun j τ => (D.hc (t.seam.iT τ)).e j) := funext fun j => funext fun τ => heZ j τ
    rw [e]; exact hTied
  have hP := GlobalTheory.NormOneUnit.prod_muAt t.Ch t.sel (t.tup μ) (t.cst μ) t.glob.σ₀ eZ t.glob.mu0 eta hX t.pr_ok hsel hgS
    (GlobalTheory.T.columnField_ramificationIdxIn_eq_one D t.X t.seam hX hok) hTied' ⟨i, hi⟩ z hzs hzi
  rw [t.glob_σ] at hP
  set M := t.seam.σ₀ (∏ P : rowSG t.Pr t.sel (t.tup μ), muAt t.Ch t.sel (t.tup μ) (t.cst μ) i P z) with hMdef
  have hw0 : ∀ τ, t.X.embC t.seam.σ₀ τ z ≠ 0 := fun τ => (map_ne_zero _).2 hz0
  have hP' : M = ∏ τ, t.X.embC t.seam.σ₀ τ z ^ (-(eZ ⟨i, hi⟩ τ)) := hP
  have hM0 : M ≠ 0 := by
    rw [hP']
    exact Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ (hw0 τ)
  have hk : ∀ x, (t.rd u μ).Xi i c c' (γ.1.toLinearMap ∘ₗ x) = (t.seam.σ₀ k / M) * (t.rd u μ).Xi i c c' x := by
    intro x
    have := hXi x
    field_simp
    linear_combination this
  have hA : TaylorLogMetric.admitted D _ _ (t.seam.lat ((t.rd u μ).N i c)) (t.seam.lat ((t.rd u μ).N (i + 1) c')) := by
    rw [← t.O_lat, ← t.O_lat]
    exact ⟨rank_even _ _, rank_even _ _, ((t.O u μ).lat i c).2, ((t.O u μ).lat (i + 1) c').2⟩
  have hSSc : ∀ P ∈ (t.rd u μ).SS, conjPrime₂ P ∉ (t.rd u μ).SS := by
    rw [hSS]
    exact GlobalTheory.T.memberBadPrimes_no_conjugatePair t.sel (t.tup μ) hX t.pr_ok hsel (t.word u) (hTS _) hgS
  have h2q : ∀ P ∈ (t.rd u μ).SS, ((D.host.QS : ℕ) : 𝓞 t.X.E) ∉ P.asIdeal ∧ ((D.host.q : ℕ) : 𝓞 t.X.E) ∉ P.asIdeal := by
    intro P hP
    rw [hSS] at hP
    obtain ⟨p, hp, hpP, hk⟩ := sall_nat t.sel (t.tup μ) t.pr_ok hsel (t.word u) hP
    have hp2 : p ∉ D.host.small ∧ p ≠ D.host.q := by
      rcases hk with e | ⟨j, e⟩ | hn
      · rw [e, t.T_rec]; exact ⟨UpperTheory.Small.not_mem_of_mod D.host (D.T_mod_cond u), D.T_ne_q u⟩
      · rw [e, t.g_rec]; exact ⟨UpperTheory.Ram.g_notMem_small D j, GlobalTheory.ShortOwnCompare.level_ne_q D j⟩
      · exact ⟨fun e => hn (h2S _ e), fun e => hn (e ▸ hqS)⟩
    have key : ∀ l : ℕ, l.Prime → l ≠ p → ((l : ℕ) : 𝓞 t.X.E) ∉ P.asIdeal := by
      intro l hl hlp hlP
      have hc : IsCoprime ((p : ℕ) : 𝓞 t.X.E) ((l : ℕ) : 𝓞 t.X.E) := by
        have h1 := (Nat.coprime_primes hp hl).2 (Ne.symm hlp)
        have h2 := (Nat.isCoprime_iff_coprime.2 h1).map (Int.castRingHom (𝓞 t.X.E))
        simpa using h2
      obtain ⟨a, b, hab⟩ := hc
      exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
        (hab ▸ add_mem (P.asIdeal.mul_mem_left a hpP) (P.asIdeal.mul_mem_left b hlP)))
    exact ⟨UpperTheory.Ram.natCast_notMem_of_coprime P.isPrime.ne_top hpP
      ((Nat.Prime.coprime_iff_not_dvd hp).2 (UpperTheory.Small.not_dvd_QS D.host hp hp2.1)).symm, key _ D.host.hyp.1 hp2.2.symm⟩
  have hlev0 : 0 < (t.rd u μ).lev := by
    rw [hlev]
    exact modulus_pos t.sel (t.tup μ) (t.cst μ) (t.word u) (t.pr_ok.T_prime _).pos
  have key := GlobalTheory.KerLaw.thC_left_stab D t.X t.seam t.cc t.δ t.B t.χ t.cD hok t.cc_ok t.δ_ok t.χ_ok _ _ _ _ hA
    (t.rd u μ).SS (t.rd u μ).lev ((t.rd u μ).Xi i c c') hlev0 hSSc h2q hΞ γ hγ _ hk
  have hdet : (matE t.seam γ.1).det = t.seam.iE z := by
    rw [matE]
    change ((t.seam.iE : t.X.E →+* D.host.E).mapMatrix (LinearMap.toMatrix' γ.1.toLinearMap)).det = _
    rw [← RingHom.map_det, LinearMap.det_toMatrix', hz, LinearEquiv.coe_det]
    rfl
  refine ⟨by rw [hdet]; exact (map_ne_zero _).2 hz0, t.seam.σ₀ k / M, fun w => ?_, ?_⟩
  · rw [t.O_Th]
    unfold KerRead.Th Seam.push
    refine (congrArg _ ?_).trans (key (fun τ => w (t.seam.iT τ)))
    funext τ
    refine congrArg (· * Matrix.of (w (t.seam.iT τ))) ?_
    ext a b
    simp only [matE, Matrix.map_apply]
    exact (hok.1 τ _).symm
  · show t.seam.σ₀ k = t.seam.σ₀ k / M * ∏ τ, TaylorLogMetric.embT D τ (matE t.seam γ.1).det ^ (-(D.chTw u μ).sDiv i τ)
    rw [hdet]
    have hw : ∀ τ, t.X.embC t.seam.σ₀ τ z = TaylorLogMetric.embT D (t.seam.iT τ) (t.seam.iE z) := fun τ => hok.1 τ z
    have hR : ∏ τ, TaylorLogMetric.embT D τ (t.seam.iE z) ^ (-(D.chTw u μ).sDiv i τ) =
        ∏ τ, t.X.embC t.seam.σ₀ τ z ^ (-(D.chTw u μ).sDiv i (t.seam.iT τ)) :=
      (Fintype.prod_equiv t.seam.iT _ _ fun τ => by rw [hw]).symm
    have h1 : ∏ τ, t.X.embC t.seam.σ₀ τ z = 1 := by
      rw [← hprod1]
      exact Fintype.prod_equiv t.seam.iT _ _ fun τ => hw τ
    have hM' : M = ∏ τ, t.X.embC t.seam.σ₀ τ z ^ (-(D.chTw u μ).sDiv i (t.seam.iT τ)) := by
      rw [hP']
      simp only [eZ]
      have e1 : ∀ τ, t.X.embC t.seam.σ₀ τ z ^ (-((D.chTw u μ).sDiv i (t.seam.iT τ) + ((D.R.N i / 2 : ℕ) : ℤ))) =
          t.X.embC t.seam.σ₀ τ z ^ (-(D.chTw u μ).sDiv i (t.seam.iT τ)) * t.X.embC t.seam.σ₀ τ z ^ (-((D.R.N i / 2 : ℕ) : ℤ)) :=
        fun τ => by rw [neg_add, zpow_add₀ (hw0 τ)]
      rw [Finset.prod_congr rfl fun τ _ => e1 τ, Finset.prod_mul_distrib, Finset.prod_zpow, h1, one_zpow, mul_one]
    rw [hR, ← hM']
    field_simp

end GlobalTheory.KFiDat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairKernelLawOfFiniteDatumLawStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms Formalism.L2.Col Formalism.L2.DIV Formalism.HermitianLatticesTheory GlobalTheory.KerJ NumberField IsDedekindDomain Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairKernelLaw_of_finiteDatumLaw : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.X.Ok → IsSel t.X t.sel → (∀ i, t.Pr.g i ∈ t.S) → (∀ v, t.Pr.T v ∈ t.S) → (∀ l ∈ D.host.small, l ∈ t.S) → D.host.q ∈ t.S → (∃ eta, t.Ch.Tied t.glob.σ₀ (fun j τ => (D.hc (t.seam.iT τ)).e j) t.glob.mu0 eta) → ∀ u μ i, i < D.R.m → ∀ (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)) (γ : UF t.X.E (D.R.N (i + 1))) (k : t.X.K), gmap γ.1 ((t.rd u μ).N (i + 1) c') = (t.rd u μ).N (i + 1) c' → (∀ x, ∀ z ∈ mulLat (t.rd u μ).lev (homAt (t.rd u μ).SS ((t.rd u μ).N i c) ((t.rd u μ).N (i + 1) c')), (t.rd u μ).Xi i c c' (x + z) = (t.rd u μ).Xi i c c' x) → (∀ x, (t.rd u μ).Xi i c c' (γ.1.toLinearMap ∘ₗ x) * t.seam.σ₀ (∏ P : rowSG t.Pr t.sel (t.tup μ), muAt t.Ch t.sel (t.tup μ) (t.cst μ) i P ((LinearEquiv.det γ.1 : t.X.Eˣ) : t.X.E)) = t.seam.σ₀ k * (t.rd u μ).Xi i c c' x) → TermLaw (t.O u μ) i c c' (matE t.seam γ.1, t.seam.σ₀ k) := by
  first | exact @GlobalTheory.KFiDat.termLaw_of_xi | exact GlobalTheory.KFiDat.termLaw_of_xi | (intros; apply GlobalTheory.KFiDat.termLaw_of_xi <;> assumption)
end
end
