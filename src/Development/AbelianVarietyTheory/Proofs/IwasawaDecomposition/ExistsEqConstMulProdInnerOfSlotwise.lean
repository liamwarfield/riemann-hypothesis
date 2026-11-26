module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselDatumAuxiliaryVectorOrthogonalImage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerOfNormEq
public import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsThetaFunOOfThetaAt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqConstMulProdInnerOfSlotwise
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqConstMulProdInnerOfSlotwise
open scoped InnerProductSpace

namespace GlobalTheory

theorem exists_eq_const_mul_prod_inner_of_positionwise (ι : Type) [Fintype ι] [DecidableEq ι]
    (Hs : ι → Type) [∀ i, NormedAddCommGroup (Hs i)] [∀ i, InnerProductSpace ℂ (Hs i)]
    (B : (∀ i, Hs i) → (∀ i, Hs i) → ℂ)
    (h : ∀ i v v', ∃ c : ℂ, ∀ w w' : Hs i,
      B (Function.update v i w) (Function.update v' i w') = c * ⟪w, w'⟫_ℂ) :
    ∃ c : ℂ, ∀ v v', B v v' = c * ∏ i, ⟪v i, v' i⟫_ℂ := by
  by_cases h0 : ∃ i, ∀ w : Hs i, w = 0
  · obtain ⟨i, hi⟩ := h0
    refine ⟨0, fun v v' => ?_⟩
    obtain ⟨c, hc⟩ := h i v v'
    have h1 := hc (v i) (v' i)
    rw [Function.update_eq_self, Function.update_eq_self, hi (v i)] at h1
    simpa using h1
  · have h1 : ∀ i, ∃ e : Hs i, ⟪e, e⟫_ℂ = 1 := by
      intro i
      have : ∃ w : Hs i, w ≠ 0 := by
        by_contra hn
        exact h0 ⟨i, fun w => by_contra fun hw => hn ⟨w, hw⟩⟩
      obtain ⟨w, hw⟩ := this
      refine ⟨((‖w‖ : ℂ))⁻¹ • w, ?_⟩
      have hn : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hw
      rw [inner_smul_left, inner_smul_right, inner_self_eq_norm_sq_to_K]
      simp only [map_inv₀, Complex.conj_ofReal]
      change ((‖w‖ : ℂ))⁻¹ * (((‖w‖ : ℂ))⁻¹ * (‖w‖ : ℂ) ^ 2) = 1
      field_simp
    choose e he using h1
    have step : ∀ i v v', B v v' =
        B (Function.update v i (e i)) (Function.update v' i (e i)) * ⟪v i, v' i⟫_ℂ := by
      intro i v v'
      obtain ⟨c, hc⟩ := h i v v'
      have h2 := hc (v i) (v' i)
      rw [Function.update_eq_self, Function.update_eq_self] at h2
      rw [h2, hc, he, mul_one]
    have key : ∀ (s : Finset ι) v v', B v v' =
        B (s.piecewise e v) (s.piecewise e v') * ∏ i ∈ s, ⟪v i, v' i⟫_ℂ := by
      intro s
      induction s using Finset.induction_on with
      | empty => intro v v'; simp
      | insert a s ha ih =>
        intro v v'
        rw [ih v v', step a (s.piecewise e v) (s.piecewise e v'), Finset.prod_insert ha,
          Finset.piecewise_insert, Finset.piecewise_insert,
          Finset.piecewise_eq_of_notMem _ _ _ ha, Finset.piecewise_eq_of_notMem _ _ _ ha,
          mul_assoc]
    refine ⟨B e e, fun v v' => ?_⟩
    have := key Finset.univ v v'
    rwa [Finset.piecewise_univ, Finset.piecewise_univ] at this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqConstMulProdInnerOfSlotwiseStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eq_const_mul_prod_inner_of_slotwise' : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Hs : ι → Type) [∀ i, NormedAddCommGroup (Hs i)] [∀ i, InnerProductSpace ℂ (Hs i)] (B : (∀ i, Hs i) → (∀ i, Hs i) → ℂ), (∀ i v v', ∃ c : ℂ, ∀ w w' : Hs i, B (Function.update v i w) (Function.update v' i w') = c * ⟪w, w'⟫_ℂ) → ∃ c : ℂ, ∀ v v', B v v' = c * ∏ i, ⟪v i, v' i⟫_ℂ := by
  first | exact @GlobalTheory.exists_eq_const_mul_prod_inner_of_positionwise | exact GlobalTheory.exists_eq_const_mul_prod_inner_of_positionwise | (intros; apply GlobalTheory.exists_eq_const_mul_prod_inner_of_positionwise <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffIntegrableContinuous
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffIntegrableContinuousOf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RootExch.CoefInt

variable {D : D7} {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

theorem continuous_psiN (d : BesselDatum A B ι) {ψ : AddChar (AF D.host.F) ℂ} (hψ : Continuous ψ) :
    Continuous (d.psiN ψ) := by
  have i0 : IsTopologicalRing (AE D) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := D.host.F) (E := D.host.E)
  have i1 : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have hm : Continuous (mt B) := Units.continuous_val.comp continuous_subtype_val
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) := IsModuleTopology.continuous_of_linearMap _
  have ha : ∀ v, Continuous fun g => actV B g v := fun v => hm.matrix_mulVec continuous_const
  refine hψ.comp (ht.comp (continuous_const.mul (continuous_finsetSum _ fun i _ => ?_)))
  exact continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
    continuous_const.mul ((continuous_apply b).comp (ha _))

def FlagCocompact : Prop :=
  ∀ (D : D7) (B : HSp D) (ρ : ℕ) (e : Matrix (Fin B.rank) (Fin ρ) D.host.E), IsIsoSub B e →
    ∃ K : Set (NFlag B e), IsCompact K ∧ ∀ n, ∃ γ ∈ NFlagQ B e, ∃ k ∈ K, n = γ * k

theorem exists_compact (H : FlagCocompact) (d : BesselDatum A B ι) :
    ∃ K : Set (GA D B), IsCompact K ∧ ∀ n ∈ d.N, ∃ γ ∈ GQ B, ∃ k ∈ K, n = γ * k := by
  obtain ⟨K, hK, h⟩ := H D B _ (GlobalTheory.BesselCompare.toBes d).e (GlobalTheory.BesselCompare.toBes d).e_iso
  have hN := (GlobalTheory.BesselCompare.same_toBes d).2.2.1
  refine ⟨Subtype.val '' K, hK.image continuous_subtype_val, fun n hn => ?_⟩
  obtain ⟨γ, hγ, k, hk, e⟩ := h ⟨n, hN ▸ hn⟩
  exact ⟨γ, hγ, k, ⟨k, hk, rfl⟩, congrArg Subtype.val e⟩

theorem coeff_integrable_continuous_of (H : FlagCocompact) : ∀ (D : D7) (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesselDatum A B ι) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ ν 𝓝, d.IsUnitPair ν 𝓝 → ∀ F : GA D B → ℂ, Continuous F → (∀ γ ∈ GQ B, ∀ g, F (γ * g) = F g) → (∀ g, IntegrableOn (fun n : d.N => F ((n : GA D B) * g) * star (d.psiN ψ (n : GA D B))) 𝓝 ν) ∧ Continuous (d.coeff ψ ν 𝓝 F) ∧ ∀ C : Set (GA D B), IsCompact C → ∃ M : ℝ, ∀ n ∈ d.N, ∀ g ∈ C, ‖F (n * g)‖ ≤ M := by
  intro D A B ι d ψ hψ ν 𝓝 hν F hF hinv
  obtain ⟨b1, b2, b3, b4, b5, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  have hbd : ∀ C : Set (GA D B), IsCompact C → ∃ M : ℝ, ∀ n ∈ d.N, ∀ g ∈ C, ‖F (n * g)‖ ≤ M := by
    intro C hC
    obtain ⟨K, hK, h⟩ := exists_compact H d
    obtain ⟨M, hM⟩ := (hK.mul hC).exists_bound_of_continuousOn hF.continuousOn
    refine ⟨M, fun n hn g hg => ?_⟩
    obtain ⟨γ, hγ, k, hk, rfl⟩ := h n hn
    rw [mul_assoc, hinv γ hγ]
    exact hM _ (Set.mul_mem_mul hk hg)
  have hfin : ν 𝓝 ≠ ⊤ := by rw [hν.2.2]; exact ENNReal.one_ne_top
  have : SecondCountableTopology d.N := TopologicalSpace.Subtype.secondCountableTopology _
  have hχ : Continuous fun n : d.N => star (d.psiN ψ (n : GA D B)) :=
    ((continuous_psiN d hψ.1).comp continuous_subtype_val).star
  have hc : ∀ g, Continuous fun n : d.N => F ((n : GA D B) * g) * star (d.psiN ψ (n : GA D B)) := fun g =>
    (hF.comp (continuous_subtype_val.mul continuous_const)).mul hχ
  have hn : ∀ g (n : d.N), ‖F ((n : GA D B) * g) * star (d.psiN ψ (n : GA D B))‖ = ‖F ((n : GA D B) * g)‖ :=
    fun g n => by rw [norm_mul, norm_star, BesselDatum.psiN, hψ.2.1, mul_one]
  refine ⟨fun g => ?_, ?_, hbd⟩
  · obtain ⟨M, hM⟩ := hbd {g} isCompact_singleton
    exact Measure.integrableOn_of_bounded (M := M) hfin (hc g).measurable.aestronglyMeasurable
      (.of_forall fun n => (hn g n).trans_le (hM n n.2 g rfl))
  · refine continuous_iff_continuousAt.2 fun g => ?_
    obtain ⟨C, hC, hCg⟩ := exists_compact_mem_nhds g
    obtain ⟨M, hM⟩ := hbd C hC
    have : IsFiniteMeasure (ν.restrict 𝓝) := isFiniteMeasure_restrict.2 hfin
    refine continuousAt_of_dominated (bound := fun _ => M)
      (.of_forall fun x => (hc x).measurable.aestronglyMeasurable) ?_ (integrable_const M)
      (.of_forall fun n => ?_)
    · filter_upwards [hCg] with x hx
      exact .of_forall fun n => (hn x n).trans_le (hM n n.2 x hx)
    · exact ((hF.comp (continuous_const.mul continuous_id)).mul continuous_const).continuousAt

end GlobalTheory.RootExch.CoefInt
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RootExch.CoefInt

theorem coeff_integrable_continuous : ∀ (D : D7) (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesselDatum A B ι) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ ν 𝓝, d.IsUnitPair ν 𝓝 → ∀ F : GA D B → ℂ, Continuous F → (∀ γ ∈ GQ B, ∀ g, F (γ * g) = F g) → (∀ g, IntegrableOn (fun n : d.N => F ((n : GA D B) * g) * star (d.psiN ψ (n : GA D B))) 𝓝 ν) ∧ Continuous (d.coeff ψ ν 𝓝 F) ∧ ∀ C : Set (GA D B), IsCompact C → ∃ M : ℝ, ∀ n ∈ d.N, ∀ g ∈ C, ‖F (n * g)‖ ≤ M :=
  coeff_integrable_continuous_of fun D B ρ e he => (GlobalTheory.Mem.UnipCocompact.radicals_cocompact D B ρ e he).1

end GlobalTheory.RootExch.CoefInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchurInnerEqPairClosableNormInvariantStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchurInnerEqPairClosableNormInvariant
open Filter
open scoped InnerProductSpace Topology

namespace GlobalTheory.ClosableSchur

theorem inner_eq_of_diag {H E : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (D : Submodule ℂ H) (A A' : H →ₗ[ℂ] E) (c : ℂ)
    (h : ∀ w ∈ D, ⟪A w, A' w⟫_ℂ = c * ⟪w, w⟫_ℂ) :
    ∀ w ∈ D, ∀ w' ∈ D, ⟪A w, A' w'⟫_ℂ = c * ⟪w, w'⟫_ℂ := by
  intro w hw w' hw'
  have h1 := h (w + w') (D.add_mem hw hw')
  have h2 := h (w + Complex.I • w') (D.add_mem hw (D.smul_mem _ hw'))
  have h3 := h w hw
  have h4 := h w' hw'
  simp only [map_add (f := _), map_smul, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, Complex.conj_I] at h1 h2
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination (1 / 2 : ℂ) * h1 - (Complex.I / 2) * h2 - (1 / 2 - Complex.I / 2) * h3
    - (1 / 2 - Complex.I / 2) * h4
    + (1 / 2 : ℂ) * (⟪A w, A' w'⟫_ℂ - c * ⟪w, w'⟫_ℂ - ⟪A w', A' w⟫_ℂ + c * ⟪w', w⟫_ℂ
      - Complex.I * (⟪A w', A' w'⟫_ℂ - c * ⟪w', w'⟫_ℂ)) * hI

theorem tendsto_zero_of_norm_sq {H E : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (D : Submodule ℂ H) (A : H →ₗ[ℂ] E) (a : ℝ)
    (h : ∀ w ∈ D, ‖A w‖ ^ 2 = a * ‖w‖ ^ 2) (u : ℕ → H) (hu : ∀ i, u i ∈ D)
    (h0 : Tendsto u atTop (𝓝 0)) : Tendsto (fun i => A (u i)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero] at h0 ⊢
  have h1 : Tendsto (fun i => a * ‖u i‖ ^ 2) atTop (𝓝 0) := by
    simpa using (h0.pow 2).const_mul a
  have h2 := h1.sqrt
  rw [Real.sqrt_zero] at h2
  refine h2.congr fun i => ?_
  rw [← h _ (hu i), Real.sqrt_sq (norm_nonneg _)]

theorem inner_eq_pair : ∀ (ι H E : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] (ρ : ι → (H →L[ℂ] H)) (D : Submodule ℂ H), (∀ i v, ‖ρ i v‖ = ‖v‖) → (∀ i, ∃ j, (∀ v, ρ j (ρ i v) = v) ∧ ∀ v, ρ i (ρ j v) = v) → (∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ i, ∀ v ∈ S, ρ i v ∈ S) → S = ⊥ ∨ S = ⊤) → (∀ i, ∀ v ∈ D, ρ i v ∈ D) → ∀ A A' : H →ₗ[ℂ] E, (∀ i, ∀ w ∈ D, ‖A (ρ i w)‖ = ‖A w‖) → (∀ i, ∀ w ∈ D, ‖A' (ρ i w)‖ = ‖A' w‖) → (∀ i, ∀ w ∈ D, ⟪A (ρ i w), A' (ρ i w)⟫_ℂ = ⟪A w, A' w⟫_ℂ) → (∀ (u : ℕ → H) (f : E), (∀ i, u i ∈ D) → Tendsto u atTop (𝓝 0) → Tendsto (fun i => A (u i)) atTop (𝓝 f) → f = 0) → (∀ (u : ℕ → H) (f : E), (∀ i, u i ∈ D) → Tendsto u atTop (𝓝 0) → Tendsto (fun i => A' (u i)) atTop (𝓝 f) → f = 0) → ∃ c : ℂ, ∀ w ∈ D, ∀ w' ∈ D, ⟪A w, A' w'⟫_ℂ = c * ⟪w, w'⟫_ℂ := by
  intro ι H E _ _ _ _ _ _ ρ D hn hinv hirr hD A A' hA hA' hAA' hc hc'
  obtain ⟨a, ha⟩ := norm_sq_eq ι H E ρ D hn hinv hirr hD A hA hc
  obtain ⟨a', ha'⟩ := norm_sq_eq ι H E ρ D hn hinv hirr hD A' hA' hc'
  have hexp : ∀ (z : ℂ) (w : H), ‖(z • A + A') w‖ ^ 2 =
      ‖z‖ ^ 2 * ‖A w‖ ^ 2 + 2 * ((starRingEnd ℂ) z * ⟪A w, A' w⟫_ℂ).re + ‖A' w‖ ^ 2 := by
    intro z w
    rw [LinearMap.add_apply, LinearMap.smul_apply, @norm_add_sq ℂ, inner_smul_left, norm_smul,
      mul_pow]
    rfl
  have key : ∀ z : ℂ, ∃ b : ℝ, ∀ w ∈ D, ‖(z • A + A') w‖ ^ 2 = b * ‖w‖ ^ 2 := by
    intro z
    refine norm_sq_eq ι H E ρ D hn hinv hirr hD (z • A + A') ?_ ?_
    · intro i w hw
      rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), hexp, hexp, hA i w hw, hA' i w hw,
        hAA' i w hw]
    · intro u f hu h0 hf
      have h1 := tendsto_zero_of_norm_sq D A a ha u hu h0
      have h2 := tendsto_zero_of_norm_sq D A' a' ha' u hu h0
      have h3 := (h1.const_smul z).add h2
      rw [smul_zero, add_zero] at h3
      exact tendsto_nhds_unique hf h3
  obtain ⟨b, hb⟩ := key 1
  obtain ⟨b', hb'⟩ := key Complex.I
  refine ⟨⟨(b - a - a') / 2, (b' - a - a') / 2⟩, inner_eq_of_diag D A A' _ fun w hw => ?_⟩
  have e1 := hb w hw
  have e2 := hb' w hw
  rw [hexp, ha w hw, ha' w hw] at e1 e2
  have e3 : ⟪w, w⟫_ℂ = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; simp
  rw [e3]
  simp only [map_one, one_mul, norm_one, one_pow, Complex.norm_I, Complex.conj_I, Complex.mul_re,
    Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im] at e1 e2
  apply Complex.ext
  · rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]; linarith
  · rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]; linarith

end GlobalTheory.ClosableSchur
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schur_inner_eq_pair_closable_normInvariant : ∀ (ι H E : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] (ρ : ι → (H →L[ℂ] H)) (D : Submodule ℂ H), (∀ i v, ‖ρ i v‖ = ‖v‖) → (∀ i, ∃ j, (∀ v, ρ j (ρ i v) = v) ∧ ∀ v, ρ i (ρ j v) = v) → (∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ i, ∀ v ∈ S, ρ i v ∈ S) → S = ⊥ ∨ S = ⊤) → (∀ i, ∀ v ∈ D, ρ i v ∈ D) → ∀ A A' : H →ₗ[ℂ] E, (∀ i, ∀ w ∈ D, ‖A (ρ i w)‖ = ‖A w‖) → (∀ i, ∀ w ∈ D, ‖A' (ρ i w)‖ = ‖A' w‖) → (∀ i, ∀ w ∈ D, ⟪A (ρ i w), A' (ρ i w)⟫_ℂ = ⟪A w, A' w⟫_ℂ) → (∀ (u : ℕ → H) (f : E), (∀ i, u i ∈ D) → Tendsto u atTop (𝓝 0) → Tendsto (fun i => A (u i)) atTop (𝓝 f) → f = 0) → (∀ (u : ℕ → H) (f : E), (∀ i, u i ∈ D) → Tendsto u atTop (𝓝 0) → Tendsto (fun i => A' (u i)) atTop (𝓝 f) → f = 0) → ∃ c : ℂ, ∀ w ∈ D, ∀ w' ∈ D, ⟪A w, A' w'⟫_ℂ = c * ⟪w, w'⟫_ℂ := by
  first | exact @GlobalTheory.ClosableSchur.inner_eq_pair | exact GlobalTheory.ClosableSchur.inner_eq_pair | (intros; apply GlobalTheory.ClosableSchur.inner_eq_pair <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GardingVectorDerivativeEqGardingVector
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GardingVectorDerivativeEqGardingVector
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SmVec

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}

def fieldDeriv (φ : Matrix (Fin n) (Fin n) ℂ → ℝ) (P : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] (Matrix (Fin n) (Fin n) ℂ → ℝ) where
  toFun X g := fderiv ℝ φ g (-(P * X * P⁻¹) * g)
  map_add' X Y := by
    funext g
    simp only [Pi.add_apply, ← map_add (f := _), Matrix.mul_add, Matrix.add_mul, neg_add]
  map_smul' c X := by
    funext g
    simp only [Pi.smul_apply, RingHom.id_apply, ← map_smul, Matrix.mul_smul, Matrix.smul_mul, ← smul_neg]

theorem isTest_fderiv {φ : Matrix (Fin n) (Fin n) ℂ → ℝ} (hφ : IsTest φ) (Y : Matrix (Fin n) (Fin n) ℂ) :
    IsTest fun g => fderiv ℝ φ g (Y * g) := by
  refine ⟨(hφ.1.fderiv_right (m := ∞) (le_of_eq rfl)).clm_apply (contDiff_const.mul contDiff_id), ?_⟩
  refine HasCompactSupport.intro hφ.2 fun g hg => ?_
  rw [fderiv_of_notMem_tsupport ℝ hg]; rfl

variable {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem hasDerivAt_integral_translate (hσ : IsURepOn (UJset ε) σ) {φ : Matrix (Fin n) (Fin n) ℂ → ℝ}
    (hφ : IsTest φ) (Y : Matrix (Fin n) (Fin n) ℂ) (w : H) :
    HasDerivAt (fun t : ℝ => ∫ g : Formalism.REAL.UJ ε, φ (NormedSpace.exp (t • Y) * umat g) • σ (umat g) w
      ∂(Formalism.REAL.muG ε)) (gard ε σ (fun g => fderiv ℝ φ g (Y * g)) w) 0 := by
  obtain ⟨hemb, -⟩ := Formalism.REAL.isClosedEmbeddingMatrix n ε
  have hu : Continuous fun g : Formalism.REAL.UJ ε => umat g := continuous_umat
  have hb := continuous_orbit hσ w
  have he : ∀ (Z : Matrix (Fin n) (Fin n) ℂ) (t : ℝ),
      HasDerivAt (fun t : ℝ => NormedSpace.exp (t • Z)) (Z * NormedSpace.exp (t • Z)) t :=
    fun Z t => hasDerivAt_exp_smul_const' Z t
  have hc : ∀ Z : Matrix (Fin n) (Fin n) ℂ, Continuous fun t : ℝ => NormedSpace.exp (t • Z) :=
    fun Z => continuous_iff_continuousAt.2 fun t => (he Z t).continuousAt
  have hxy : ∀ t : ℝ, NormedSpace.exp (t • (-Y)) * NormedSpace.exp (t • Y) = 1 := fun t => by
    rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl Y).neg_left.smul_left t).smul_right t), ← smul_add]
    simp
  have hC : IsCompact (Set.image2 (· * ·) ((fun t : ℝ => NormedSpace.exp (t • (-Y))) '' Metric.closedBall 0 1)
      (tsupport φ)) := ((isCompact_closedBall (0 : ℝ) 1).image (hc _)).mul hφ.2
  have hK := hemb.isCompact_preimage hC
  set K := (fun g : Formalism.REAL.UJ ε => umat g) ⁻¹' (Set.image2 (· * ·)
    ((fun t : ℝ => NormedSpace.exp (t • (-Y))) '' Metric.closedBall 0 1) (tsupport φ)) with hKdef
  replace hK : IsCompact K := hK
  have hout : ∀ t ∈ Metric.closedBall (0 : ℝ) 1, ∀ g ∉ K, NormedSpace.exp (t • Y) * umat g ∉ tsupport φ :=
    fun t ht g hg hm => hg ⟨_, ⟨t, ht, rfl⟩, _, hm, by
      show _ * (_ * _) = umat g
      rw [← Matrix.mul_assoc, hxy, Matrix.one_mul]⟩
  set μ := Formalism.REAL.muG ε
  let F' : ℝ → Formalism.REAL.UJ ε → H := fun t g =>
    fderiv ℝ φ (NormedSpace.exp (t • Y) * umat g) (Y * NormedSpace.exp (t • Y) * umat g) • σ (umat g) w
  have hF'c : Continuous fun p : ℝ × Formalism.REAL.UJ ε => F' p.1 p.2 := by
    have h1 : Continuous fun p : ℝ × Formalism.REAL.UJ ε => NormedSpace.exp (p.1 • Y) := (hc Y).comp continuous_fst
    have h2 : Continuous fun p : ℝ × Formalism.REAL.UJ ε => umat p.2 := hu.comp continuous_snd
    exact (((hφ.1.continuous_fderiv (by simp)).comp (h1.mul h2)).clm_apply
      ((continuous_const.mul h1).mul h2)).smul (hb.comp continuous_snd)
  obtain ⟨C, hCb⟩ := ((isCompact_closedBall (0 : ℝ) 1).prod hK).exists_bound_of_continuousOn hF'c.continuousOn
  have hint : ∀ t ∈ Metric.closedBall (0 : ℝ) 1, Integrable
      (fun g : Formalism.REAL.UJ ε => φ (NormedSpace.exp (t • Y) * umat g) • σ (umat g) w) μ := fun t ht =>
    Continuous.integrable_of_hasCompactSupport ((hφ.continuous.comp (continuous_const.mul hu)).smul hb)
      (HasCompactSupport.intro hK fun g hg => by
        rw [image_eq_zero_of_notMem_tsupport (hout t ht g hg), zero_smul])
  have e0 : F' 0 = fun g : Formalism.REAL.UJ ε => fderiv ℝ φ (umat g) (Y * umat g) • σ (umat g) w := by
    funext g; simp [F']
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := (0 : ℝ))
    (F := fun t g => φ (NormedSpace.exp (t • Y) * umat g) • σ (umat g) w) (F' := F')
    (bound := K.indicator fun _ => C) (Metric.closedBall_mem_nhds (0 : ℝ) one_pos)
    (by filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) one_pos] with t ht
        exact (hint t ht).aestronglyMeasurable)
    (hint 0 (Metric.mem_closedBall_self zero_le_one))
    (by rw [e0]; exact ((isTest_fderiv hφ Y).integrable hb).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun g t ht => by
      by_cases hg : g ∈ K
      · rw [Set.indicator_of_mem hg]; exact hCb (t, g) ⟨ht, hg⟩
      · rw [Set.indicator_of_notMem hg]
        simp [F', fderiv_of_notMem_tsupport ℝ (hout t ht g hg)])
    ((integrable_indicator_iff hK.measurableSet).2 (integrableOn_const hK.measure_lt_top.ne))
    (Filter.Eventually.of_forall fun g t _ =>
      (((hφ.1.differentiable (by simp)) _).hasFDerivAt.comp_hasDerivAt t ((he Y t).mul_const (umat g))).smul_const _)
  rw [e0] at key
  exact key.2

theorem dRep_gard : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → ∀ φ, IsTest φ → ∃ ψ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] (Matrix (Fin n) (Fin n) ℂ → ℝ), ∀ X, IsTest (ψ X) ∧ (X ∈ lieG G → ∀ w, dRep (trRep σ P) X (gard ε σ φ w) = gard ε σ (ψ X) w) := by
  intro n ε H _ _ _ σ P G hP h hσ φ hφ
  refine ⟨fieldDeriv φ P, fun X => ⟨isTest_fderiv hφ _, fun hX w => ?_⟩⟩
  refine Eq.trans ?_ (hasDerivAt_integral_translate hσ hφ (-(P * X * P⁻¹)) w).deriv
  unfold dRep
  congr 1
  funext t
  rw [gard_eq hσ hφ]
  refine GlobalTheory.LowTypeRestriction.garding_translate hσ hφ.continuous hφ.2 w
    (conj_mem_UJ hP h (exp_mem_UH (gram_unit hP h) hX t)) ?_
  rw [← Matrix.exp_conj _ _ hP, Matrix.mul_smul, Matrix.smul_mul,
    ← Matrix.exp_add_of_commute _ _ (((Commute.refl (P * X * P⁻¹)).neg_left.smul_left t).smul_right t), ← smul_add]
  simp

end GlobalTheory.SmVec

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GardingVectorDerivativeEqGardingVectorStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gardingVector_derivative_eq_gardingVector : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → ∀ φ, IsTest φ → ∃ ψ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] (Matrix (Fin n) (Fin n) ℂ → ℝ), ∀ X, IsTest (ψ X) ∧ (X ∈ lieG G → ∀ w, dRep (trRep σ P) X (gard ε σ φ w) = gard ε σ (ψ X) w) := by
  first | exact @GlobalTheory.SmVec.dRep_gard | exact GlobalTheory.SmVec.dRep_gard | (intros; apply GlobalTheory.SmVec.dRep_gard <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousUnitaryRootExchangeMap
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousUnitaryRootExchangeMap
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RootUnip

open GlobalTheory.BesselCompare (hA_add hA_smul hA_smul_right)

variable {D : D7} {B : HSp D}

def kMat (B : HSp D) (v y : Fin B.rank → AE D) : Matrix (Fin B.rank) (Fin B.rank) (AE D) :=
  1 + vecMulVec v ((fun i => cA D (y i)) ᵥ* B.gram.map (incA D)) -
    vecMulVec y ((fun i => cA D (v i)) ᵥ* B.gram.map (incA D))

theorem kMat_mulVec (v y x : Fin B.rank → AE D) :
    (kMat B v y).mulVec x = x + hA B x y • v - hA B x v • y := by
  rw [kMat, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec,
    Matrix.vecMulVec_mulVec, hA_eq, hA_eq, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec]
  simp only [op_smul_eq_smul]

theorem continuous_rankTwo {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {n : ℕ}
    {c : R → R} (hc : Continuous c) (J : Matrix (Fin n) (Fin n) R) (v w : Fin n → R) :
    Continuous fun y : Fin n → R => 1 + vecMulVec v ((fun i => c (y i)) ᵥ* J) - vecMulVec y w := by
  have hc' : Continuous fun y : Fin n → R => fun i => c (y i) :=
    continuous_pi fun i => hc.comp (continuous_apply i)
  have h1 := continuous_const (y := v).matrix_vecMulVec (hc'.matrix_vecMul (continuous_const (y := J)))
  have h2 := (continuous_id (X := Fin n → R)).matrix_vecMulVec (continuous_const (y := w))
  refine continuous_matrix fun i j => ?_
  simp only [Matrix.sub_apply, Matrix.add_apply]
  exact (continuous_const.add (h1.matrix_elem i j)).sub (h2.matrix_elem i j)

theorem continuous_kMat (v : Fin B.rank → AE D) : Continuous (kMat B v) :=
  have : IsTopologicalRing (AE D) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing
  continuous_rankTwo GlobalTheory.FockCompare.ThetaCont.continuous_conj _ _ _

section

variable {η : AE D} (hη : η * cA D η = 0) {v y : Fin B.rank → AE D} (hy : η • y = y) (hv : hA B v y = 0)

include hη hy in
theorem hA_smul_self (x : Fin B.rank → AE D) : hA B x y • y = 0 := by
  have e : hA B x y = cA D η * hA B x y := by rw [← hA_smul_right, hy]
  rw [e, ← hy, smul_smul, hy, mul_assoc, mul_comm (hA B x y), ← mul_assoc, mul_comm (cA D η), hη, zero_mul,
    zero_smul]

include hη hy in
theorem hA_mul_hA (x x' : Fin B.rank → AE D) : hA B x y * hA B y x' = 0 := by
  rw [← hA_smul, hA_smul_self hη hy, hA_zero]

include hη hy in
theorem hA_self : hA B y y = 0 := by
  have e : hA B y y = η * (cA D η * hA B y y) := by rw [← hA_smul_right, ← hA_smul, hy]
  rw [e, ← mul_assoc, hη, zero_mul]

include hv in
theorem hA_yv : hA B y v = 0 := by rw [← hA_herm, hv, map_zero]

include hη hy hv in
theorem kMat_neg_mul : kMat B v (-y) * kMat B v y = 1 := by
  refine Matrix.mulVec_injective (funext fun x => ?_)
  show (kMat B v (-y) * kMat B v y).mulVec x = (1 : Matrix _ _ _).mulVec x
  rw [← Matrix.mulVec_mulVec, kMat_mulVec, kMat_mulVec, Matrix.one_mulVec, hA_neg_right]
  simp only [hA_sub, hA_add, hA_smul, hv, hA_yv hv, hA_self hη hy, mul_zero, add_zero, sub_zero]
  have h0 : (hA B x y * hA B v v) • y = 0 := by
    rw [mul_comm, mul_smul, hA_smul_self hη hy, smul_zero]
  rw [smul_neg, add_smul, h0, neg_smul]
  abel

include hη hy hv in
theorem kMat_mul_neg : kMat B v y * kMat B v (-y) = 1 := by
  have := kMat_neg_mul (y := -y) (v := v) hη (by rw [smul_neg, hy]) (by rw [hA_neg_right, hv, neg_zero])
  rwa [neg_neg] at this

include hη hy hv in
theorem hA_kMat (x x' : Fin B.rank → AE D) :
    hA B ((kMat B v y).mulVec x) ((kMat B v y).mulVec x') = hA B x x' := by
  rw [kMat_mulVec, kMat_mulVec]
  simp only [hA_sub, hA_add, hA_smul, hA_sub_right, hA_add_right, hA_smul_right, hA_herm, hv, hA_yv hv,
    hA_self hη hy]
  linear_combination hA B v v * hA_mul_hA hη hy x x'

end

theorem unitary_of_hA {M : Matrix (Fin B.rank) (Fin B.rank) (AE D)}
    (h : ∀ x y, hA B (M.mulVec x) (M.mulVec y) = hA B x y) :
    (M.map (cA D))ᵀ * B.gram.map (incA D) * M = B.gram.map (incA D) := by
  have key : ∀ x y : Fin B.rank → AE D,
      (fun i => cA D (y i)) ⬝ᵥ ((M.map (cA D))ᵀ * B.gram.map (incA D) * M).mulVec x =
        (fun i => cA D (y i)) ⬝ᵥ (B.gram.map (incA D)).mulVec x := fun x y => by
    have e : (fun i => cA D (M.mulVec y i)) = (M.map (cA D)).mulVec fun i => cA D (y i) :=
      funext fun i => RingHom.map_mulVec (cA D) _ y i
    have := h x y
    rwa [hA_eq, hA_eq, e, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec] at this
  refine Matrix.mulVec_injective (funext fun x => funext fun i => ?_)
  have := key x (Pi.single i 1)
  rwa [show (fun j => cA D ((Pi.single i 1 : Fin B.rank → AE D) j)) = Pi.single i 1 from
    funext fun j => by by_cases e : j = i <;> simp [e], single_one_dotProduct, single_one_dotProduct] at this

theorem exists_continuous_isK (D : D7) (B : HSp D) (η : AE D) (hη : η * cA D η = 0) (v : Fin B.rank → AE D) :
    ∃ K : {y : Fin B.rank → AE D // η • y = y ∧ hA B v y = 0} → GA D B,
      Continuous K ∧ ∀ y, IsK B v y.1 (K y) := by
  refine ⟨fun y => ⟨⟨kMat B v y.1, kMat B v (-y.1), kMat_mul_neg hη y.2.1 y.2.2, kMat_neg_mul hη y.2.1 y.2.2⟩,
    unitary_of_hA (hA_kMat hη y.2.1 y.2.2)⟩, ?_, fun y x => kMat_mulVec v y.1 x⟩
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact (continuous_kMat v).comp continuous_subtype_val
  · exact (continuous_kMat v).comp continuous_subtype_val.neg

end GlobalTheory.RootUnip

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousUnitaryRootExchangeMapStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_unitaryRootExchangeMap : ∀ (D : D7) (B : HSp D) (η : AE D), η * cA D η = 0 → ∀ v : Fin B.rank → AE D, ∃ K : {y : Fin B.rank → AE D // η • y = y ∧ hA B v y = 0} → GA D B, Continuous K ∧ ∀ y, IsK B v y.1 (K y) := by
  first | exact @GlobalTheory.RootUnip.exists_continuous_isK | exact GlobalTheory.RootUnip.exists_continuous_isK | (intros; apply GlobalTheory.RootUnip.exists_continuous_isK <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselDatumAdelicVectorDecomposition
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselDatumAdelicVectorDecomposition
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BesselDecomp

open GlobalTheory.BesselCompare (hA_add hA_smul hA_sum hA_vec hD_swap_zero)

variable {D : D7} {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

theorem hD_basis_dual (d : BesselDatum A B ι) (i l) : B.hD (d.aux l) (dual d i) = if l = i then 1 else 0 := by
  have hz : star (B.hT d.z d.z) = B.hT d.z d.z := (hT_swap rfl).symm
  have zz : B.hT d.z d.z ≠ 0 := d.zz
  unfold BesselDatum.aux dual
  refine Fin.lastCases ?_ (fun j => ?_) i <;> refine Fin.lastCases ?_ (fun k => ?_) l
  · simp [HSpace.hD, starRingEnd_apply, hz, zz]
  · have : B.hT d.z (d.e k) = 0 := d.ez k
    simp [HSpace.hD, this, Fin.castSucc_ne_last]
  · rw [Fin.snoc_last, Fin.snoc_castSucc, hD_swap_zero (d.fz j), if_neg (Fin.castSucc_ne_last j).symm]
  · rw [Fin.snoc_castSucc, Fin.snoc_castSucc, d.ef]
    simp

theorem f_dual (d : BesselDatum A B ι) (i l) : B.hD (d.f l) (dual d i) = 0 := by
  unfold dual
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have : B.hT d.z (d.f l) = 0 := d.fz l
    simp [HSpace.hD, this]
  · rw [Fin.snoc_castSucc, d.ff]

theorem hD_basis_e (d : BesselDatum A B ι) (i l) : B.hD (d.aux i) (d.e l) = 0 := by
  unfold BesselDatum.aux
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Fin.snoc_last, hD_swap_zero (d.ez l)]
  · rw [Fin.snoc_castSucc, d.ee]

theorem f_e (d : BesselDatum A B ι) (k l) : B.hD (d.f k) (d.e l) = if k = l then 1 else 0 := by
  have h : B.hT (d.e l) (d.f k) = star (if l = k then 1 else 0) := hT_swap (d.ef l k)
  unfold HSpace.hD
  rw [h]
  by_cases e : k = l
  · simp [e]
  · simp [e, Ne.symm e]

def comb (d : BesselDatum A B ι) :
    (A.V × (Fin (d.ρ + 1) → D.host.E) × (Fin d.ρ → D.host.E)) →ₗ[D.host.E] B.V :=
  ι.coprod ((Fintype.linearCombination D.host.E d.aux).coprod (Fintype.linearCombination D.host.E d.f))

theorem comb_inj (d : BesselDatum A B ι) : Function.Injective (comb d) := by
  refine (injective_iff_map_eq_zero _).2 ?_
  rintro ⟨a, s, r⟩ h
  simp only [comb, LinearMap.coprod_apply, Fintype.linearCombination_apply] at h
  have h1 : ∀ i l, B.hT (dual d i) (d.aux l) = if l = i then 1 else 0 := hD_basis_dual d
  have h2 : ∀ i l, B.hT (dual d i) (d.f l) = 0 := f_dual d
  have h3 : ∀ i l, B.hT (d.e l) (d.aux i) = 0 := hD_basis_e d
  have h4 : ∀ k l, B.hT (d.e l) (d.f k) = if k = l then 1 else 0 := f_e d
  have h5 : ∀ i, B.hT (dual d i) (ι a) = 0 := fun i => hD_swap_zero (dual_perp d i a)
  have h6 : ∀ l, B.hT (d.e l) (ι a) = 0 := fun l => hD_swap_zero (d.eA l a)
  have hs : s = 0 := by
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [map_sum, h1, h2, h5] using congrArg (B.hT (dual d i)) h
  have hr : r = 0 := by
    funext l
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [map_sum, h3, h4, h6] using congrArg (B.hT (d.e l)) h
  subst hs hr
  have ha : ι a = 0 := by simpa using h
  have : a = 0 := by
    refine A.nondeg.1 a fun y => ?_
    rw [← d.isom a y, ha]; simp
  subst this
  rfl

theorem comb_surj (d : BesselDatum A B ι) : Function.Surjective (comb d) := by
  have := Module.Finite.of_basis A.frame
  have := Module.Finite.of_basis B.frame
  refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 (comb_inj d)
  rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_fin_fun, A.rank_eq, B.rank_eq,
    d.rank_eq]
  omega

theorem vecA_add (v w : B.V) : vecA B (v + w) = vecA B v + vecA B w := by
  funext k; simp [vecA]

theorem vecA_sum {n : ℕ} (c : Fin n → D.host.E) (v : Fin n → B.V) :
    vecA B (∑ i, c i • v i) = ∑ i, incA D (c i) • vecA B (v i) := by
  funext k; simp [vecA, map_sum, Finset.sum_apply]

theorem vecA_iota (a : A.V) : vecA B (ι a) = iA ι (vecA A a) := by
  rw [iA, GlobalTheory.BesselCompare.frameMat_eq, GlobalTheory.BesselCompare.eMat_mulVec]
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [← A.frame.sum_repr a, map_sum]
  simp only [map_smul]
  rw [vecA_sum]
  rfl

theorem exists_comb (d : BesselDatum A B ι) (x : Fin B.rank → AE D) :
    ∃ (t : Fin A.rank → AE D) (s : Fin (d.ρ + 1) → AE D) (r : Fin d.ρ → AE D),
      x = iA ι t + ∑ i, s i • vecA B (d.aux i) + ∑ l, r l • vecA B (d.f l) := by
  have hx : x = ∑ k, x k • vecA B (B.frame k) := by
    funext j
    simp [vecA, Finset.sum_apply, Finsupp.single_apply, apply_ite (incA D)]
  rw [hx]
  refine Finset.sum_induction _ (fun y => ∃ (t : Fin A.rank → AE D) (s : Fin (d.ρ + 1) → AE D) (r : Fin d.ρ → AE D),
      y = iA ι t + ∑ i, s i • vecA B (d.aux i) + ∑ l, r l • vecA B (d.f l)) ?_ ?_ ?_
  · rintro _ _ ⟨t, s, r, rfl⟩ ⟨t', s', r', rfl⟩
    refine ⟨t + t', s + s', r + r', ?_⟩
    simp only [iA_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
    abel
  · exact ⟨0, 0, 0, by simp [iA]⟩
  · intro k _
    obtain ⟨⟨a, s, r⟩, h⟩ := comb_surj d (B.frame k)
    simp only [comb, LinearMap.coprod_apply, Fintype.linearCombination_apply] at h
    refine ⟨x k • vecA A a, fun i => x k * incA D (s i), fun l => x k * incA D (r l), ?_⟩
    rw [← h, vecA_add, vecA_add, vecA_sum, vecA_sum, vecA_iota, iA_smul]
    simp only [smul_add, Finset.smul_sum, smul_smul, add_assoc]

theorem iA_vec {v : B.V} (h : ∀ x, B.hD v (ι x) = 0) (t : Fin A.rank → AE D) : hA B (iA ι t) (vecA B v) = 0 := by
  rw [← hA_herm, hA_vec_iA h, map_zero]

theorem decomp : ∀ (D : D7) (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesselDatum A B ι),
    (∀ i l, B.hD (d.aux l) (dual d i) = if l = i then 1 else 0) ∧ (∀ i l, B.hD (d.f l) (dual d i) = 0) ∧
    ∀ x : Fin B.rank → AE D, ∃ t, x = iA ι t + ∑ i, hA B x (vecA B (dual d i)) • vecA B (d.aux i) +
      ∑ l, hA B x (vecA B (d.e l)) • vecA B (d.f l) := by
  intro D A B ι d
  refine ⟨hD_basis_dual d, f_dual d, fun x => ?_⟩
  obtain ⟨t, s, r, h⟩ := exists_comb d x
  have hs : ∀ i, hA B x (vecA B (dual d i)) = s i := fun i => by
    rw [h, hA_add, hA_add, hA_sum, hA_sum, iA_vec (dual_perp d i)]
    simp [hA_smul, hA_vec, hD_basis_dual, f_dual, apply_ite (incA D)]
  have hr : ∀ l, hA B x (vecA B (d.e l)) = r l := fun l => by
    rw [h, hA_add, hA_add, hA_sum, hA_sum, iA_vec (d.eA l)]
    simp [hA_smul, hA_vec, hD_basis_e, f_e, apply_ite (incA D)]
  exact ⟨t, by simp only [hs, hr]; exact h⟩

end GlobalTheory.BesselDecomp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselDatumAdelicVectorDecompositionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselDatum_adelicVector_decomposition : ∀ (D : D7) (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesselDatum A B ι), (∀ i l, B.hD (d.aux l) (dual d i) = if l = i then 1 else 0) ∧ (∀ i l, B.hD (d.f l) (dual d i) = 0) ∧ ∀ x : Fin B.rank → AE D, ∃ t, x = iA ι t + ∑ i, hA B x (vecA B (dual d i)) • vecA B (d.aux i) + ∑ l, hA B x (vecA B (d.e l)) • vecA B (d.f l) := by
  first | exact @GlobalTheory.BesselDecomp.decomp | exact GlobalTheory.BesselDecomp.decomp | (intros; apply GlobalTheory.BesselDecomp.decomp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowestWeightMatrixCoefficientDependsOnWeight
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowestWeightMatrixCoefficientDependsOnWeight
open Matrix Formalism.MainNotions.S GlobalTheory.JointHarm

noncomputable section

namespace GlobalTheory.JointHarm.Sph

variable {n : ℕ} {ε : Fin n → Bool} {μ : Fin n → ℝ}

theorem entire_eq_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h : ∀ t : ℝ, f t = 0) (z : ℂ) : f z = 0 := by
  have ha : AnalyticOnNhd ℂ f Set.univ := hf.differentiableOn.analyticOnNhd isOpen_univ
  refine ha.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ (Set.mem_univ 0) ?_
    (Set.mem_univ z)
  have ht : Filter.Tendsto (fun t : ℝ => (t : ℂ)) (nhdsWithin 0 {0}ᶜ) (nhdsWithin 0 {0}ᶜ) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := Complex.continuous_ofReal.tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simpa using ht
  exact ht.frequently (Filter.Eventually.of_forall h).frequently

theorem diag_mem {d : Fin n → ℂ} (hd : ∀ a, d a ≠ 0) : Matrix.diagonal d ∈ GlobalTheory.Dec.KC ε := by
  refine ⟨?_, by simp [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, mul_comm]⟩
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_diagonal, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
  exact fun a _ => hd a

theorem mul_mem {a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ GlobalTheory.Dec.KC ε) (hb : b ∈ GlobalTheory.Dec.KC ε) :
    a * b ∈ GlobalTheory.Dec.KC ε :=
  ⟨ha.1.mul hb.1, by rw [Matrix.mul_assoc, hb.2, ← Matrix.mul_assoc, ha.2, Matrix.mul_assoc]⟩

theorem ct_mem {a : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ GlobalTheory.Dec.KC ε) : aᴴ ∈ GlobalTheory.Dec.KC ε := by
  refine ⟨by simpa [Matrix.star_eq_conjTranspose] using ha.1.star, ?_⟩
  have := congrArg Matrix.conjTranspose ha.2
  simp only [Matrix.conjTranspose_mul, Formalism.REAL.Jm_conjTranspose] at this
  exact this.symm

section One

variable {P : Type} [AddCommGroup P] [Module ℂ P] {B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ}
  {π : Matrix (Fin n) (Fin n) ℂ → Module.End ℂ P}

theorem diff_curve (h : IsHolRep ε B π) {c : ℂ → Matrix (Fin n) (Fin n) ℂ}
    (hc : ∀ i j, Differentiable ℂ fun z => c z i j) (hm : ∀ z, c z ∈ GlobalTheory.Dec.KC ε) (x y : P) :
    Differentiable ℂ fun z => B x (π (c z) y) := by
  have h1 : Differentiable ℂ fun z => (fun i j => c z i j : Fin n → Fin n → ℂ) :=
    differentiable_pi.2 fun i => differentiable_pi.2 fun j => hc i j
  have := (h.2.2.2.2 x y).comp (s := Set.univ) h1.differentiableOn (fun z _ => hm z)
  exact differentiableOn_univ.1 this

theorem real_torus (h : IsHolRep ε B π) {x : P} (hx : IsBottom ε π μ x) (s : Fin n → ℝ) :
    π (Matrix.diagonal fun a => Complex.exp (s a : ℂ)) x = Complex.exp ((∑ a, μ a * s a : ℝ) : ℂ) • x := by
  rw [← sub_eq_zero]
  apply h.1
  generalize hw : π (Matrix.diagonal fun a => Complex.exp (s a : ℂ)) x -
    Complex.exp ((∑ a, μ a * s a : ℝ) : ℂ) • x = w
  have hd := diff_curve h (c := fun z => Matrix.diagonal fun a => Complex.exp (z * s a * Complex.I))
    (fun i j => by
      by_cases e : i = j
      · subst e; simp only [Matrix.diagonal_apply_eq]; fun_prop
      · simp only [Matrix.diagonal_apply_ne _ e]; fun_prop)
    (fun z => diag_mem fun a => Complex.exp_ne_zero _) w x
  have h0 := entire_eq_zero (f := fun z => B w (π (Matrix.diagonal fun a => Complex.exp (z * s a * Complex.I)) x) -
      Complex.exp (z * ((∑ a, μ a * s a : ℝ) : ℂ) * Complex.I) * B w x) (hd.sub (by fun_prop))
    (fun t => by
      have := hx.2 (fun a => t * s a)
      have e : (∑ a, μ a * (t * s a)) = t * ∑ a, μ a * s a := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => by ring
      rw [e] at this
      simp only [Complex.ofReal_mul] at this
      simp only [this, map_smul, smul_eq_mul, sub_self]) (-Complex.I)
  have e : ∀ u : ℂ, -Complex.I * u * Complex.I = u := fun u => by
    linear_combination (-u) * Complex.I_mul_I
  simp only [e] at h0
  conv_lhs => enter [2]; rw [← hw]
  rw [map_sub, map_smul, smul_eq_mul, h0]

theorem borel {b : Matrix (Fin n) (Fin n) ℂ} (hb : b ∈ GlobalTheory.Dec.KC ε) (hl : GlobalTheory.Dec.IsLo b)
    (hp : ∀ i, b i i = Complex.exp (Real.log (b i i).re : ℝ))
    (h : IsHolRep ε B π) {x : P} (hx : IsBottom ε π μ x) :
    π b x = Complex.exp ((∑ a, μ a * Real.log (b a a).re : ℝ) : ℂ) • x := by
  have hne : ∀ i, b i i ≠ 0 := fun i => by rw [hp i]; exact Complex.exp_ne_zero _
  have hu : Matrix.diagonal (fun a => (b a a)⁻¹) * b ∈ GlobalTheory.Dec.KC ε :=
    mul_mem (diag_mem fun a => inv_ne_zero (hne a)) hb
  have hlu : IsLoUni (Matrix.diagonal (fun a => (b a a)⁻¹) * b) := fun i j =>
    ⟨fun hij => by rw [Matrix.diagonal_mul, hl i j hij, mul_zero],
      fun hij => by subst hij; rw [Matrix.diagonal_mul, inv_mul_cancel₀ (hne i)]⟩
  have e : b = Matrix.diagonal (fun a => Complex.exp (Real.log (b a a).re : ℝ)) *
      (Matrix.diagonal (fun a => (b a a)⁻¹) * b) := by
    ext i j
    rw [Matrix.diagonal_mul, Matrix.diagonal_mul, ← hp i, mul_inv_cancel_left₀ (hne i)]
  conv_lhs => rw [e]
  rw [h.2.2.1 _ (diag_mem fun a => Complex.exp_ne_zero _) _ hu, Module.End.mul_apply, hx.1 _ hu hlu,
    real_torus h hx]

end One


open scoped ComplexOrder in
theorem gram {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ GlobalTheory.Dec.KC ε) (μ : Fin n → ℝ) :
    ∃ c : ℂ, ∀ (P : Type) [AddCommGroup P] [Module ℂ P] (B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ)
      (π : Matrix (Fin n) (Fin n) ℂ → Module.End ℂ P) (x y : P), IsHolRep ε B π → IsBottom ε π μ x →
      IsBottom ε π μ y → B x (π (gᴴ * g) y) = c * B x y := by
  obtain ⟨k, b, hk, hb, hl, hp, rfl⟩ := GlobalTheory.Dec.IwKC.exists_decomp ε hg
  have hp' : ∀ i, b i i = Complex.exp (Real.log (b i i).re : ℝ) := fun i => by
    have := Complex.pos_iff.1 (hp i)
    rw [← Complex.ofReal_exp, Real.exp_log this.1]
    exact Complex.ext rfl (by simpa using this.2.symm)
  refine ⟨star (Complex.exp ((∑ a, μ a * Real.log (b a a).re : ℝ) : ℂ)) *
    Complex.exp ((∑ a, μ a * Real.log (b a a).re : ℝ) : ℂ), fun P _ _ B π x y h hx hy => ?_⟩
  rw [GlobalTheory.Dec.IwKC.gram_unitary_mul hk.1, h.2.2.1 _ (ct_mem hb) _ hb, Module.End.mul_apply,
    ← h.2.2.2.1 _ hb, borel hb hl hp' h hx, borel hb hl hp' h hy]
  simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, starRingEnd_apply]
  ring

section Exp

open scoped Matrix.Norms.Operator

theorem exp_mem {H : Matrix (Fin n) (Fin n) ℂ} (hJ : H * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * H) (z : ℂ) :
    NormedSpace.exp (z • H) ∈ GlobalTheory.Dec.KC ε := by
  refine ⟨Matrix.isUnit_exp _, ?_⟩
  have : Commute (z • H) (Formalism.REAL.Jm ε) := Commute.smul_left hJ z
  exact this.exp_left.eq

theorem exp_diff (H : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    Differentiable ℂ fun z : ℂ => NormedSpace.exp (z • H) i j := by
  have h1 : Differentiable ℂ fun z : ℂ => NormedSpace.exp (z • H) :=
    fun z => (hasDerivAt_exp_smul_const H z).differentiableAt
  exact (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ i j)).differentiable.comp h1

theorem exp_gram {H : Matrix (Fin n) (Fin n) ℂ} (hH : Hᴴ = H) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • H) =
      (NormedSpace.exp (((t : ℂ) / 2) • H))ᴴ * NormedSpace.exp (((t : ℂ) / 2) • H) := by
  rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hH]
  have e : star ((t : ℂ) / 2) = (t : ℂ) / 2 := by simp
  rw [e, ← Matrix.exp_add_of_commute _ _ (Commute.refl _), ← add_smul, add_halves]

end Exp

theorem coeff_eq (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (P : Type) [AddCommGroup P] [Module ℂ P]
    (B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ) (π : Matrix (Fin n) (Fin n) ℂ → Module.End ℂ P) (P' : Type) [AddCommGroup P']
    [Module ℂ P'] (B' : P' →ₗ⋆[ℂ] P' →ₗ[ℂ] ℂ) (π' : Matrix (Fin n) (Fin n) ℂ → Module.End ℂ P') (x y : P)
    (x' y' : P') (h : IsHolRep ε B π) (h' : IsHolRep ε B' π') (hx : IsBottom ε π μ x) (hy : IsBottom ε π μ y)
    (hx' : IsBottom ε π' μ x') (hy' : IsBottom ε π' μ y') :
    ∀ k ∈ Formalism.REAL.Kset ε, B x (π k y) * B' x' y' = B x y * B' x' (π' k y') := by
  intro k hk
  obtain ⟨Y, ⟨hG, hY⟩, rfl, -⟩ := Formalism.REAL.compact_exists_log_bounded ε k hk
  have hs : Yᴴ = -Y := by
    have h1 : (Yᴴ + Y) * Formalism.REAL.Jm ε = 0 := by
      rw [Matrix.add_mul, hY]; exact hG
    have h2 := congrArg (· * Formalism.REAL.Jm ε) h1
    simp only [Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.mul_one, Matrix.zero_mul] at h2
    exact eq_neg_of_add_eq_zero_left h2
  have hH : ((-Complex.I) • Y)ᴴ = (-Complex.I) • Y := by
    rw [Matrix.conjTranspose_smul, hs]; simp
  have hJ : ((-Complex.I) • Y) * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * ((-Complex.I) • Y) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hY]
  have h0 := entire_eq_zero (f := fun z => B x (π (NormedSpace.exp (z • (-Complex.I) • Y)) y) * B' x' y' -
      B x y * B' x' (π' (NormedSpace.exp (z • (-Complex.I) • Y)) y'))
    (((diff_curve h (exp_diff _) (exp_mem hJ) x y).mul_const _).sub
      ((diff_curve h' (exp_diff _) (exp_mem hJ) x' y').const_mul _))
    (fun t => by
      obtain ⟨c, hc⟩ := gram (exp_mem hJ ((t : ℂ) / 2)) μ
      simp only [exp_gram hH t, hc P B π x y h hx hy, hc P' B' π' x' y' h' hx' hy']
      ring) Complex.I
  have e : Complex.I • (-Complex.I) • Y = Y := by rw [smul_smul]; simp
  simp only [e] at h0
  exact sub_eq_zero.1 h0

end GlobalTheory.JointHarm.Sph

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowestWeightMatrixCoefficientDependsOnWeightStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowestWeight_matrixCoefficient_depends_on_weight : ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (P : Type) [AddCommGroup P] [Module ℂ P] (B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ) (π : Matrix (Fin n) (Fin n) ℂ → Module.End ℂ P) (P' : Type) [AddCommGroup P'] [Module ℂ P'] (B' : P' →ₗ⋆[ℂ] P' →ₗ[ℂ] ℂ) (π' : Matrix (Fin n) (Fin n) ℂ → Module.End ℂ P') (x y : P) (x' y' : P'), IsHolRep ε B π → IsHolRep ε B' π' → IsBottom ε π μ x → IsBottom ε π μ y → IsBottom ε π' μ x' → IsBottom ε π' μ y' → ∀ k ∈ Formalism.REAL.Kset ε, B x (π k y) * B' x' y' = B x y * B' x' (π' k y') := by
  first | exact @GlobalTheory.JointHarm.Sph.coeff_eq | exact GlobalTheory.JointHarm.Sph.coeff_eq | (intros; apply GlobalTheory.JointHarm.Sph.coeff_eq <;> assumption)
end
end
