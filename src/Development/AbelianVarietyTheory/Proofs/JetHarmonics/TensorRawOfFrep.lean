module

public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesUnitarySmoothBasic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliDetFrameIndep
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DualTensorCayleyCompatible
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSubgroupProductMeasureIsHaar
public import Development.AbelianVarietyTheory.Definitions.Jets.ColValMonomial
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.GermEvalOneStandardPointSelf
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
public import ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.LogDetSt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorRawOfFrep
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorRawOfFrep
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.TensorKFinite

variable {k r : ℕ} {ι : Type} [Fintype ι]

theorem smMap_zero {R R' : Rep k r} {T : R.H → R'.H} (hT : SmMap R R' T) : T 0 = 0 := by
  have h := hT.smul 0 0 R.smSub.zero_mem
  simpa using h

theorem kfin_of_family {R R' : Rep k r} (T : ι → R.H → R'.H) (hT : ∀ c, SmMap R R' (T c))
    (hK : ∀ v, R.KFin v → v ∈ R.sm)
    (hA : ∀ g ∈ GG k r, ∀ c, ∀ y ∈ R.sm, ∃ a : ι → ℂ, R'.σ g (T c y) = ∑ i, a i • T i (R.σ g y))
    (c : ι) (y : R.H) (hy : R.KFin y) : R'.KFin (T c y) := by
  obtain ⟨S, hfd, hyS, hst⟩ := hy
  have hsm : ∀ x ∈ S, x ∈ R.sm := fun x hx => hK x ⟨S, hfd, hx, hst⟩
  let L : ι → (S →ₗ[ℂ] R'.H) := fun i =>
    { toFun := fun x => T i x
      map_add' := fun x x' => (hT i).add _ (hsm _ x.2) _ (hsm _ x'.2)
      map_smul' := fun a x => (hT i).smul a _ (hsm _ x.2) }
  have hmem : ∀ i, ∀ x ∈ S, T i x ∈ ⨆ i, LinearMap.range (L i) := fun i x hx =>
    Submodule.mem_iSup_of_mem i ⟨⟨x, hx⟩, rfl⟩
  refine ⟨⨆ i, LinearMap.range (L i), inferInstance, hmem c y hyS, fun g hg x hx => ?_⟩
  have hle : (⨆ i, LinearMap.range (L i)) ≤
      (⨆ i, LinearMap.range (L i)).comap (R'.σ g : R'.H →ₗ[ℂ] R'.H) := by
    refine iSup_le fun i => ?_
    rintro _ ⟨z, rfl⟩
    obtain ⟨a, ha⟩ := hA g hg.1 i z (hsm _ z.2)
    have : R'.σ g (T i z) ∈ ⨆ i, LinearMap.range (L i) := by
      rw [ha]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hmem j _ (hst g hg _ z.2))
    exact this
  exact hle hx

theorem tk_of_family {R R' : Rep k r} (T : ι → R.H → R'.H) (hT : ∀ c, SmMap R R' (T c))
    (hK : ∀ v, R.KFin v → v ∈ R.sm) (hTK : ∀ v ∈ R.TK, v ∈ R.sm)
    (hF : ∀ c y, R.KFin y → R'.KFin (T c y))
    (hB : ∀ g ∈ GG k r, ∀ c, ∀ y ∈ R.sm, ∃ a : ι → ℂ, T c (R.σ g y) = ∑ i, a i • R'.σ g (T i y))
    (c : ι) (y : R.H) (hy : y ∈ R.TK) : T c y ∈ R'.TK := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, hg, v, hv, rfl⟩ := hx
    obtain ⟨a, ha⟩ := hB g hg c v (hK v hv)
    rw [ha]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨g, hg, _, hF j v hv, rfl⟩)
  | zero => rw [smMap_zero (hT c)]; exact Submodule.zero_mem _
  | add x x' hx hx' h1 h2 =>
    rw [(hT c).add _ (hTK _ hx) _ (hTK _ hx')]; exact Submodule.add_mem _ h1 h2
  | smul a x hx h1 =>
    rw [(hT c).smul a _ (hTK _ hx)]; exact Submodule.smul_mem _ _ h1

theorem inv_rows [DecidableEq ι] {V : Type} [AddCommGroup V] [Module ℂ V] (A B : Matrix ι ι ℂ) (h : A * B = 1)
    (u v : ι → V) (huv : ∀ i, u i = ∑ j, B i j • v j) (c : ι) : v c = ∑ i, A c i • u i := by
  simp_rw [huv, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, ← Matrix.mul_apply, h, Matrix.one_apply]
  simp

end GlobalTheory.TensorKFinite


open GlobalTheory.TensorKFinite in
theorem GlobalTheory.tensor_decomposition_kfinite : PI.KFinSmooth → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ), R.IsDS ε mu → (∀ I, (RI I).IsDS ε (muI I)) → IsFRep ρ Γ d → TensRaw ρ R RI io pr → (∀ I c y, (RI I).KFin y → R.KFin (io I c y)) ∧ (∀ I c x, R.KFin x → (RI I).KFin (pr I c x)) ∧ (∀ I c, ∀ y ∈ (RI I).TK, io I c y ∈ R.TK) ∧ (∀ I c, ∀ x ∈ R.TK, pr I c x ∈ (RI I).TK) := by
  intro hKS k r ι κ _ _ _ _ ρ Γ d R RI io pr ε mu muI hR hRI hF hT
  obtain ⟨-, -, -, hRσ, hRT, -, hRK, -, -⟩ := GlobalTheory.T.discreteSeries_unitary_smooth_basic hKS k r ε mu R hR
  have hIT : ∀ I, ∀ v ∈ (RI I).TK, v ∈ (RI I).sm := fun I =>
    (GlobalTheory.T.discreteSeries_unitary_smooth_basic hKS k r ε (muI I) (RI I) (hRI I)).2.2.2.2.1
  have hIK : ∀ I, ∀ v, (RI I).KFin v → v ∈ (RI I).sm := fun I v hv =>
    hIT I v ((GlobalTheory.T.discreteSeries_unitary_smooth_basic hKS k r ε (muI I) (RI I) (hRI I)).2.2.2.2.2.2.1 v hv)
  have hRK' : ∀ v, R.KFin v → v ∈ R.sm := fun v hv => hRT v (hRK v hv)
  obtain ⟨-, -, h1, hmul, -⟩ := hF
  have hinv : ∀ g ∈ GG k r, ρ g⁻¹ * ρ g = 1 ∧ ρ g * ρ g⁻¹ = 1 := fun g hg => by
    obtain ⟨a, b, c⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv hg
    exact ⟨by rw [← hmul _ a _ hg, c, h1], by rw [← hmul _ hg _ a, b, h1]⟩
  have ioB : ∀ I, ∀ g ∈ GG k r, ∀ c, ∀ y ∈ (RI I).sm,
      io I c ((RI I).σ g y) = ∑ i, ρ g c i • R.σ g (io I i y) := fun I g hg c y hy =>
    congrFun (hT.io_eq I g hg y hy) c
  have ioA : ∀ I, ∀ g ∈ GG k r, ∀ c, ∀ y ∈ (RI I).sm,
      R.σ g (io I c y) = ∑ i, ρ g⁻¹ c i • io I i ((RI I).σ g y) := fun I g hg c y hy =>
    inv_rows _ _ (hinv g hg).1 (fun i => io I i ((RI I).σ g y)) (fun i => R.σ g (io I i y))
      (fun i => ioB I g hg i y hy) c
  have prA : ∀ I, ∀ g ∈ GG k r, ∀ c, ∀ x ∈ R.sm,
      (RI I).σ g (pr I c x) = ∑ i, (ρ g)ᵀ c i • pr I i (R.σ g x) := fun I g hg c x hx => by
    have hs : ∀ e, (Pi.single c x : ι → R.H) e ∈ R.sm := fun e => by
      by_cases he : e = c
      · subst he; simpa using hx
      · rw [Pi.single_eq_of_ne he]; exact R.smSub.zero_mem
    have h := hT.pr_eq I g hg (Pi.single c x) hs
    have e1 : ∑ e, pr I e ((Pi.single c x : ι → R.H) e) = pr I c x := by
      rw [Finset.sum_eq_single c]
      · simp
      · intro e _ he
        rw [Pi.single_eq_of_ne he, smMap_zero (hT.pr_sm I e)]
      · simp
    have e2 : ∀ i, act ρ R g (Pi.single c x) i = ρ g i c • R.σ g x := fun i => by
      unfold act
      rw [Finset.sum_eq_single c]
      · simp
      · intro e _ he
        simp [Pi.single_eq_of_ne he]
      · simp
    rw [e1] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [e2, (hT.pr_sm I i).smul _ _ (hRσ g hg x hx), Matrix.transpose_apply]
  have prB : ∀ I, ∀ g ∈ GG k r, ∀ c, ∀ x ∈ R.sm,
      pr I c (R.σ g x) = ∑ i, (ρ g⁻¹)ᵀ c i • (RI I).σ g (pr I i x) := fun I g hg c x hx =>
    inv_rows _ _ (by rw [← Matrix.transpose_mul, (hinv g hg).2, Matrix.transpose_one])
      (fun i => (RI I).σ g (pr I i x)) (fun i => pr I i (R.σ g x)) (fun i => prA I g hg i x hx) c
  have K1 : ∀ I c y, (RI I).KFin y → R.KFin (io I c y) := fun I =>
    kfin_of_family (io I) (hT.io_sm I) (hIK I) fun g hg c y hy => ⟨_, ioA I g hg c y hy⟩
  have K2 : ∀ I c x, R.KFin x → (RI I).KFin (pr I c x) := fun I =>
    kfin_of_family (pr I) (hT.pr_sm I) hRK' fun g hg c y hy => ⟨_, prA I g hg c y hy⟩
  exact ⟨K1, K2,
    fun I => tk_of_family (io I) (hT.io_sm I) (hIK I) (hIT I) (K1 I) fun g hg c y hy => ⟨_, ioB I g hg c y hy⟩,
    fun I => tk_of_family (pr I) (hT.pr_sm I) hRK' hRT (K2 I) fun g hg c y hy => ⟨_, prB I g hg c y hy⟩⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorRawOfFrepStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_raw_of_frep : PI.KFinSmooth → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ), R.IsDS ε mu → (∀ I, (RI I).IsDS ε (muI I)) → IsFRep ρ Γ d → TensRaw ρ R RI io pr → (∀ I c y, (RI I).KFin y → R.KFin (io I c y)) ∧ (∀ I c x, R.KFin x → (RI I).KFin (pr I c x)) ∧ (∀ I c, ∀ y ∈ (RI I).TK, io I c y ∈ R.TK) ∧ (∀ I c, ∀ x ∈ R.TK, pr I c x ∈ (RI I).TK) := by
  first | exact @GlobalTheory.tensor_decomposition_kfinite | exact GlobalTheory.tensor_decomposition_kfinite | (intros; apply GlobalTheory.tensor_decomposition_kfinite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsTypeOfIrreducibleStable
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)
namespace GlobalTheory

theorem isType_of_irreducible_stable : ∀ (Y : Type) [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π : Mx k r → (Y →L[ℂ] Y)) (B : Fin k → (Fin (2 * r + k + 1) → ℂ)) (S : Submodule ℂ Y) (u : ℕ → ℝ), inWb k r z → 0 < Tz k r z → IsRepW k r z π → (∀ h ∈ UWset k r z, ∀ v, ‖π h v‖ = ‖v‖) → IsFrameOf k r [z] B → Stab (EB π B) S → S ≠ ⊥ → (∀ S' : Submodule ℂ Y, S' ≤ S → Stab (EB π B) S' → S' = ⊥ ∨ S' = S) → (∀ (w : ℂ), ∀ y ∈ S, qdet (EB π B) w y = (∏ i ∈ Finset.Icc 1 k, (w - (k : ℂ) / 2 + 1 / 2 + (u i : ℂ))) • y) → ∃ πS : Mx k r → (S →L[ℂ] S), IsType k r z πS u ∧ ∀ h ∈ UWset k r z, ∀ y : S, ((πS h y : S) : Y) = π h y := by
  intro Y _ _ _ k r z π B S u hz hT hπ hn hB hS hne hirr hcap
  have hst : ∀ h ∈ UWset k r z, ∀ v ∈ S, π h v ∈ S :=
    Formalism.FourierDecayAlt.P.lie_stabilizer Y k r z π B hz hT hπ hB S hS
  have hfr0 : ∀ {m : ℕ} (C : Fin m → (Fin (2 * r + k + 1) → ℂ)), IsFrameOf k r [z] C → IsFrameOf k r [z, 0] C := by
    intro m C hC
    refine ⟨hC.1, hC.2.1, fun a v hv => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact hC.2.2 a _ (by simp)
    · simp [herm]
  let πS : Mx k r → (S →L[ℂ] S) := fun h => (S.orthogonalProjection).comp ((π h).comp S.subtypeL)
  have hcoe : ∀ h ∈ UWset k r z, ∀ y : S, ((πS h y : S) : Y) = π h y := by
    intro h hh y
    have := Submodule.orthogonalProjection_mem_subspace_eq_self (K := S) ⟨π h y, hst h hh y y.2⟩
    exact congrArg Subtype.val this
  have hrep : IsRepW k r z πS := by
    refine ⟨⟨?_, fun a _ b hb => ?_⟩, ?_⟩
    · ext y
      simp [πS, hπ.1.1]
    · ext y
      have h1 := hcoe b hb y
      simp only [πS, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply] at h1 ⊢
      rw [h1, hπ.1.2 a ‹_› b hb]
      rfl
    · exact continuousOn_const.clm_comp (hπ.2.clm_comp continuousOn_const)
  refine ⟨πS, ⟨Submodule.nontrivial_iff_ne_bot.2 hne, hrep.1, hrep.2, ?_, ?_, ?_⟩, hcoe⟩
  · intro h hh v
    rw [Submodule.coe_norm, Submodule.coe_norm, hcoe h hh, hn h hh]
  · intro S'' hS''
    have hstab : Stab (EB π B) (S''.map S.subtype) := by
      refine Formalism.FourierDecayAlt.P.stabilizer_lie_algebra Y k r k z 0 π B hπ (hfr0 B hB) _ ?_
      rintro h hh - _ ⟨y, hy, rfl⟩
      exact ⟨πS h y, hS'' h hh y hy, hcoe h hh y⟩
    rcases hirr _ (Submodule.map_subtype_le S S'') hstab with h | h
    · left
      exact Submodule.map_injective_of_injective S.injective_subtype (by rw [h, Submodule.map_bot])
    · right
      exact Submodule.map_injective_of_injective S.injective_subtype (by rw [h, Submodule.map_subtype_top])
  · intro B' hB' w v
    rw [(Formalism.FourierDecayAlt.P.frame_general_linear S k r k z πS B' hrep hB').2 w v]
    apply Subtype.ext
    have h1 := GlobalTheory.intertwiner_EB_of_stabiliser S Y k r k z 0 πS π S.subtypeL B' hrep hπ (hfr0 B' hB') (fun h hh _ v => hcoe h hh v)
    have h2 := GlobalTheory.qminor_intertwine Y S k k (EB π B') (EB πS B') S.subtype h1 id id w v
    have h3 := GlobalTheory.capelli_det_frame_indep Y k r z π B B' hz hT hπ hB hB' w
    refine h2.trans ?_
    have h4 := hcap w v v.2
    rw [h3] at h4
    exact h4

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorBesselTransfer
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorBesselTransfer
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem map_sum_of_add_on_sm {k r : ℕ} (R : Rep k r) {Wp : Type} [AddCommGroup Wp] [Module ℂ Wp] (l : R.H → Wp)
    (hadd : ∀ v ∈ R.sm, ∀ w ∈ R.sm, l (v + w) = l v + l w) (hsmul : ∀ (a : ℂ), ∀ v ∈ R.sm, l (a • v) = a • l v)
    {α : Type} (s : Finset α) (f : α → R.H) (hf : ∀ i, f i ∈ R.sm) : l (∑ i ∈ s, f i) = ∑ i ∈ s, l (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h0 : (0 : R.H) ∈ R.sm := R.smSub.zero_mem
    simpa using hsmul 0 0 h0
  | insert a s ha ih =>
    have hs : ∑ i ∈ s, f i ∈ R.sm := R.smSub.sum_mem fun i _ => hf i
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd _ (hf a) _ hs, ih]

theorem herm_smul_eq_sum_of_tensRaw : PI.KFinSmooth → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (om : ι → ℂ) (l : R.H → Wp) (lI : ∀ I, (RI I).H → Wp) (β : κ → ℂ), R.IsDS ε mu → (∀ I, (RI I).IsDS ε (muI I)) → TensRaw ρ R RI io pr → (∀ v ∈ R.sm, ∀ w ∈ R.sm, l (v + w) = l v + l w) → (∀ (a : ℂ), ∀ v ∈ R.sm, l (a • v) = a • l v) → (∀ I, ∀ y ∈ (RI I).sm, l (ev Γ R om (fun c => io I c y)) = β I • lI I y) → ∀ (a : ι → ℂ), ∀ w ∈ R.sm, ∀ g ∈ GG k r, Formalism.QuantumDeterminants.herm Γ (ρ g *ᵥ a) om • l (R.σ g w) = ∑ I, β I • lI I ((RI I).σ g (∑ c, pr I c (tm R a w c))) := by
  intro hK k r ι κ _ _ _ _ ρ Γ d R RI io pr ε mu muI Wp _ _ _ _ om l lI β hR hRI hT hadd hsmul hl a w hw g hg
  have hσw : R.σ g w ∈ R.sm := (rep_basic_of_isDS hK k r ε mu R hR).2.2.2.1 g hg w hw
  have htm : ∀ c, tm R a w c ∈ R.sm := fun c => R.smSub.smul_mem (a c) hw
  have hact : ∀ c, act ρ R g (tm R a w) c = (ρ g *ᵥ a) c • R.σ g w := by
    intro c
    simp only [act, tm, map_smul, smul_smul, Matrix.mulVec, dotProduct, Finset.sum_smul]
  have hx : ∀ c, act ρ R g (tm R a w) c ∈ R.sm := fun c => by
    rw [hact]; exact R.smSub.smul_mem _ hσw
  set y : ∀ I, (RI I).H := fun I => (RI I).σ g (∑ c, pr I c (tm R a w c)) with hy
  have hyeq : ∀ I, ∑ c, pr I c (act ρ R g (tm R a w) c) = y I := fun I => hT.pr_eq I g hg _ htm
  have hysm : ∀ I, y I ∈ (RI I).sm := fun I => by
    rw [← hyeq]
    exact (RI I).smSub.sum_mem fun c _ => (hT.pr_sm I c).mem _ (hx c)
  have hdec : ∀ c, ∑ I, io I c (y I) = (ρ g *ᵥ a) c • R.σ g w := fun c => by
    rw [← hact, ← hT.sum_io_pr _ hx c]
    simp only [hyeq]
  have hev : ∀ I, ev Γ R om (fun c => io I c (y I)) ∈ R.sm := fun I =>
    R.smSub.sum_mem fun i _ => R.smSub.sum_mem fun j _ => R.smSub.smul_mem _ ((hT.io_sm I j).mem _ (hysm I))
  have hsum : ∑ I, ev Γ R om (fun c => io I c (y I)) = Formalism.QuantumDeterminants.herm Γ (ρ g *ᵥ a) om • R.σ g w := by
    simp only [ev]
    rw [Finset.sum_comm]
    have : ∀ i, ∑ I, ∑ j, (star (om i) * Γ i j) • io I j (y I)
        = ∑ j, (star (om i) * Γ i j * (ρ g *ᵥ a) j) • R.σ g w := fun i => by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.smul_sum, hdec, smul_smul]
    simp only [this, ← Finset.sum_smul]
    congr 1
    generalize ρ g *ᵥ a = b
    simp only [Formalism.QuantumDeterminants.herm, Matrix.mulVec, dotProduct, Finset.mul_sum, Pi.star_apply, mul_assoc]
  rw [← hsmul _ _ hσw, ← hsum, map_sum_of_add_on_sm R l hadd hsmul _ _ hev]
  exact Finset.sum_congr rfl fun I _ => hl I _ (hysm I)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorBesselTransferStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_bessel_transfer : PI.KFinSmooth → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (om : ι → ℂ) (l : R.H → Wp) (lI : ∀ I, (RI I).H → Wp) (β : κ → ℂ), R.IsDS ε mu → (∀ I, (RI I).IsDS ε (muI I)) → TensRaw ρ R RI io pr → (∀ v ∈ R.sm, ∀ w ∈ R.sm, l (v + w) = l v + l w) → (∀ (a : ℂ), ∀ v ∈ R.sm, l (a • v) = a • l v) → (∀ I, ∀ y ∈ (RI I).sm, l (ev Γ R om (fun c => io I c y)) = β I • lI I y) → ∀ (a : ι → ℂ), ∀ w ∈ R.sm, ∀ g ∈ GG k r, Formalism.QuantumDeterminants.herm Γ (ρ g *ᵥ a) om • l (R.σ g w) = ∑ I, β I • lI I ((RI I).σ g (∑ c, pr I c (tm R a w c))) := by
  first | exact @GlobalTheory.herm_smul_eq_sum_of_tensRaw | exact GlobalTheory.herm_smul_eq_sum_of_tensRaw | (intros; apply GlobalTheory.herm_smul_eq_sum_of_tensRaw <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DualTensorCayleyWeighted
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DualTensorCayleyWeighted
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CayleyTens

theorem gram_symm (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    PI.UpqRep.Hpk k r j i = Formalism.QuantumDeterminants.Hpk k r i j := by
  unfold PI.UpqRep.Hpk Formalism.QuantumDeterminants.Hpk
  by_cases hij : i = j
  · subst hij; rfl
  · have hji : ¬ j = i := fun h => hij h.symm
    have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
    simp only [hij, hji, and_false, if_false]
    split_ifs <;> first | rfl | omega

theorem gram_cayley {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {Q : Mx k r}
    (hQ : PI.UpqRep.IsCayleyU k r ε Q) (i j : Fin (2 * r + k + 1)) :
    ∑ d, (if ε d then (1 : ℂ) else -1) * ((starRingEnd ℂ) (Q⁻¹ i d) * Q⁻¹ j d) = Formalism.QuantumDeterminants.Hpk k r i j := by
  have hinv : Q⁻¹ = Qᴴ := Matrix.inv_eq_left_inv (by
    have := (Matrix.mem_unitaryGroup_iff').1 hQ.2
    simpa [Matrix.star_eq_conjTranspose] using this)
  rw [← gram_symm, ← hQ.1.2, hinv, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp only [PI.UpqRep.Jm, Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  by_cases h : ε d <;> simp [h, mul_comm]

theorem hhJ_eq {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {Q : Mx k r}
    (hQ : PI.UpqRep.IsCayleyU k r ε Q) (R : Rep k r) (x y : Fin (2 * r + k + 1) → R.smSub)
    (u v : Fin (2 * r + k + 1) → R.H)
    (hx : ∀ d, ((x d : R.smSub) : R.H) = ∑ c, Q⁻¹ c d • u c)
    (hy : ∀ d, ((y d : R.smSub) : R.H) = ∑ c, Q⁻¹ c d • v c) :
    hhJ ε x y = hh (Formalism.QuantumDeterminants.Hpk k r) R u v := by
  unfold hhJ hh
  simp only [← gram_cayley hQ, Submodule.coe_inner, hx, hy, sum_inner, inner_sum, inner_smul_left,
    inner_smul_right, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun d _ => ?_
  ring

theorem algTens_cayley : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ (RI : Fin (2 * r + k + 1) → Rep k r) (muI : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℝ) (io : ∀ s, Fin (2 * r + k + 1) → (RI s).H → R.H) (pr : ∀ s, Fin (2 * r + k + 1) → R.H → (RI s).H) (ep : Fin (2 * r + k + 1) → ℝ) (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)) (F : ∀ s, Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (RI s).smSub), (∀ s, (RI s).IsDS ε (muI s)) → TensH dualM (Formalism.QuantumDeterminants.Hpk k r) R RI io pr ep → PI.UpqRep.IsCayleyU k r ε Q → R.IsE Q E → (∀ s, (RI s).IsE Q (F s)) → ∃ (io' : ∀ s, (RI s).smSub →ₗ[ℂ] (Fin (2 * r + k + 1) → R.smSub)) (pr' : ∀ s, (Fin (2 * r + k + 1) → R.smSub) →ₗ[ℂ] (RI s).smSub), AlgTens ε E (fun s => (RI s).smSub) F io' pr' ∧ ∀ s x, ((pr' s x : (RI s).smSub) : (RI s).H) = ∑ c, pr s c (∑ d, Q d c • ((x d : R.smSub) : R.H)) := by
  intro hK k r ε mu R hR RI muI io pr ep Q E F hRI hT hQ hE hF
  obtain ⟨io', pr', h1, h2, h3, h4, h5, h6, h7⟩ :=
    GlobalTheory.T.dual_tensor_cayley_compatible hK k r ε mu R hR RI muI io pr Q E F hRI hT.raw hQ.1.1 hE hF
  refine ⟨io', pr', ⟨h1, h2, h3, h4, h5, ?_, ?_⟩, h7⟩
  · intro s t hst y y'
    rw [hhJ_eq hQ R _ _ _ _ (h6 s y) (h6 t y')]
    exact hT.orth s t hst _ y.2 _ y'.2
  · intro s
    refine ⟨ep s, hT.ep_sq s, fun y y' => ?_⟩
    rw [hhJ_eq hQ R _ _ _ _ (h6 s y) (h6 s y'), Submodule.coe_inner]
    exact hT.iso s _ y.2 _ y'.2

end GlobalTheory.CayleyTens
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DualTensorCayleyWeightedStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_tensor_cayley_weighted : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ (RI : Fin (2 * r + k + 1) → Rep k r) (muI : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℝ) (io : ∀ s, Fin (2 * r + k + 1) → (RI s).H → R.H) (pr : ∀ s, Fin (2 * r + k + 1) → R.H → (RI s).H) (ep : Fin (2 * r + k + 1) → ℝ) (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)) (F : ∀ s, Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (RI s).smSub), (∀ s, (RI s).IsDS ε (muI s)) → TensH dualM (Formalism.QuantumDeterminants.Hpk k r) R RI io pr ep → PI.UpqRep.IsCayleyU k r ε Q → R.IsE Q E → (∀ s, (RI s).IsE Q (F s)) → ∃ (io' : ∀ s, (RI s).smSub →ₗ[ℂ] (Fin (2 * r + k + 1) → R.smSub)) (pr' : ∀ s, (Fin (2 * r + k + 1) → R.smSub) →ₗ[ℂ] (RI s).smSub), AlgTens ε E (fun s => (RI s).smSub) F io' pr' ∧ ∀ s x, ((pr' s x : (RI s).smSub) : (RI s).H) = ∑ c, pr s c (∑ d, Q d c • ((x d : R.smSub) : R.H)) := by
  first | exact @GlobalTheory.CayleyTens.algTens_cayley | exact GlobalTheory.CayleyTens.algTens_cayley | (intros; apply GlobalTheory.CayleyTens.algTens_cayley <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuotientMeasureIntegralRmulBesselGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuotientMeasureIntegralRmulBesselGroup
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem quot_integral_rmul_of_measurable (hQ : PI.QuotInv) {m : ℕ} {G S : Set (Matrix (Fin m) (Fin m) ℂ)}
    {μG μS ν : Measure (PI.MtM m)} (h : PI.QuotientSetting G S μG μS ν) (F : PI.MtM m → ℂ) (hF : Measurable F)
    (hinv : ∀ s ∈ S, ∀ x : PI.MtM m, Matrix.of x ∈ G → F (fun i j => (s * Matrix.of x) i j) = F x)
    {g : Matrix (Fin m) (Fin m) ℂ} (hg : g ∈ G) :
    ∫ x, F (fun i j => (Matrix.of x * g) i j) ∂ν = ∫ x, F x ∂ν := by
  have hc : Continuous (fun x : PI.MtM m => (fun i j => (Matrix.of x * g) i j : PI.MtM m)) := by
    have h1 : Continuous (fun x : PI.MtM m => (Matrix.of x : Matrix (Fin m) (Fin m) ℂ)) := continuous_id
    exact h1.matrix_mul continuous_const
  have hF' : Measurable (fun x : PI.MtM m => F (fun i j => (Matrix.of x * g) i j)) := hF.comp hc.measurable
  have hmap : ν.map (fun x : PI.MtM m => F (fun i j => (Matrix.of x * g) i j)) = ν.map F := by
    ext A hA
    rw [Measure.map_apply hF' hA, Measure.map_apply hF hA, ← lintegral_indicator_one (hF' hA),
      ← lintegral_indicator_one (hF hA)]
    have key := hQ m G S μG μS ν h (fun x => A.indicator (1 : ℂ → ℝ≥0∞) (F x))
      ((measurable_one.indicator hA).comp hF) (fun s hs x hx => by simp only [hinv s hs x hx]) g hg
    exact key
  have e1 := integral_map (μ := ν) hF'.aemeasurable (f := fun y : ℂ => y) aestronglyMeasurable_id
  have e2 := integral_map (μ := ν) hF.aemeasurable (f := fun y : ℂ => y) aestronglyMeasurable_id
  rw [← e1, ← e2, hmap]

theorem quot_integral_rmul : ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (F : Mx k r → ℂ), SideG k r z π u μW μN μG νq → ContinuousOn F (GG k r) → (∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, ∀ x ∈ GG k r, F (s * x) = F x) → Integrable (fun x : Formalism.QuantumDeterminants.Mt k r => F (Matrix.of x)) νq → ∀ g ∈ GG k r, ∫ x, F ((Matrix.of x) * g) ∂νq = ∫ x, F (Matrix.of x) ∂νq := by
  classical
  intro k r Wp _ _ _ _ z π u μW μN μG νq F hS hF hinv _ g hg
  obtain ⟨hz, hT, -, -, hW, hN, hG, hq⟩ := hS
  obtain ⟨hGG, hGH⟩ := GlobalTheory.T.isMatGroup_GG_and_haar_right_invariant k r
  obtain ⟨hGH1, hGH2⟩ := hGH μG hG
  obtain ⟨hSG, hsub, hS1, hS2⟩ := GlobalTheory.T.besselSubgroup_product_measure_isHaar k r z μW μN hz hT hW hN
  have hset : PI.QuotientSetting (GG k r) (Formalism.QuantumDeterminants.Sset k r z) μG (muSof μW μN) νq :=
    ⟨hGG, hSG, hsub, hGH1, hS1, hGH2, hS2, hq⟩
  obtain ⟨h0, h1⟩ := Formalism.FourierDecayAlt.P.DDSmoothness.muSof_facts hW hN
  have hae := Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hG.2.2.1 h0 h1 hq
  set A : Set (Formalism.QuantumDeterminants.Mt k r) := {x | Matrix.of x ∈ GG k r} with hA
  have hAm : MeasurableSet A := by
    have := (Formalism.FourierDecayAlt.P.DDSmoothness.uh_measurableSet (k := k) (r := r)).compl
    convert this using 1
    ext x
    simp [hA]
  have hc : ContinuousOn (fun x : Formalism.QuantumDeterminants.Mt k r => F (Matrix.of x)) A := hF
  have hm : Measurable (A.piecewise (fun x : Formalism.QuantumDeterminants.Mt k r => F (Matrix.of x)) (fun _ => 0)) :=
    hc.measurable_piecewise continuousOn_const hAm
  have hval : ∀ x : Formalism.QuantumDeterminants.Mt k r, Matrix.of x ∈ GG k r →
      A.piecewise (fun x : Formalism.QuantumDeterminants.Mt k r => F (Matrix.of x)) (fun _ => 0) x = F (Matrix.of x) :=
    fun x hx => Set.piecewise_eq_of_mem _ _ _ hx
  have key := quot_integral_rmul_of_measurable GlobalTheory.T.quotientMeasure_right_invariant hset _ hm (fun s hs x hx => by
    rw [hval x hx]
    exact (hval (fun i j => (s * Matrix.of x) i j) (hGG.2.2.1 s (hsub hs) _ hx)).trans (hinv s hs _ hx)) hg
  calc ∫ x, F ((Matrix.of x) * g) ∂νq
      = ∫ x, A.piecewise (fun x : Formalism.QuantumDeterminants.Mt k r => F (Matrix.of x)) (fun _ => 0)
          (fun i j => (Matrix.of x * g) i j) ∂νq := by
        refine integral_congr_ae (hae.mono fun x hx => ?_)
        exact (hval (fun i j => (Matrix.of x * g) i j) (hGG.2.2.1 _ hx g hg)).symm
    _ = ∫ x, A.piecewise (fun x : Formalism.QuantumDeterminants.Mt k r => F (Matrix.of x)) (fun _ => 0) x ∂νq := key
    _ = ∫ x, F (Matrix.of x) ∂νq := integral_congr_ae (hae.mono fun x hx => hval x hx)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuotientMeasureIntegralRmulBesselGroupStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotientMeasure_integral_rmul_besselGroup : ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (F : Mx k r → ℂ), SideG k r z π u μW μN μG νq → ContinuousOn F (GG k r) → (∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, ∀ x ∈ GG k r, F (s * x) = F x) → Integrable (fun x : Formalism.QuantumDeterminants.Mt k r => F (Matrix.of x)) νq → ∀ g ∈ GG k r, ∫ x, F ((Matrix.of x) * g) ∂νq = ∫ x, F (Matrix.of x) ∂νq := by
  first | exact @GlobalTheory.quot_integral_rmul | exact GlobalTheory.quot_integral_rmul | (intros; apply GlobalTheory.quot_integral_rmul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLieCoordinates
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionCharacter

open ReciprocityTheory.ChartRestriction.G.Chart GlobalTheory.JetSer GlobalTheory.ChartBaseChange ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (IsGrpPullback isGrpPullback_pullback)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (Pt comp1)
open ReciprocityTheory.ChartRestriction.G.TB (dLin)

abbrev specV {V O : Type} [CommRing V] [CommRing O] (f : V →+* O) (A : Type) [CommRing A] [Algebra O A] :
    Over (Spec (CommRingCat.of V)) :=
  Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap O A).comp f)))

theorem isMapOf_baseChange {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G']
    {π : G'.left ⟶ G.left} (hπ : IsGrpPullback G' G (Spec.map (CommRingCat.ofHom (algebraMap R R'))) π)
    (hJ : JetAlgSt) {d : ℕ} {x : JetSer.Fam G (Fin d)} {x' : JetSer.Fam G' (Fin d)}
    (hx' : ∀ m, push hπ (x' m) = Chart.spMap (jetCoeff R R' (Fin d) m) ≫ x m)
    (f : G ⟶ G) (f' : G' ⟶ G') (α : Pt R 1 d) (hf : f'.left ≫ π = π ≫ f.left) (hα : IsMapOf x x f α) :
    IsMapOf x' x' f' (fun i => MvPowerSeries.map (algebraMap R R') (α i)) := by
  refine ⟨fun i => const_map (hα.1 i), fun n a y hy => ?_⟩
  obtain ⟨Θ, t, hΘ, ht, e⟩ := exists_move hπ hJ hx' ![a] ![y] (fun i => by fin_cases i; exact hy)
  have H := hα.2 1 _ _ (ht 0)
  have hFe : comp1 α (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt R (n := 1) d 0) = α := funext fun i => germEval_oneStandardPoint_self _
  rw [hFe] at H
  refine (rep_iff hπ hJ hx' (single_point_zero_constant hy.1) hΘ H _).2 fun m => ?_
  rw [← Category.assoc, ← e 0 m]
  apply Over.OverMorphism.ext
  show ((y m).left ≫ f'.left) ≫ π = ((y m).left ≫ π) ≫ f.left
  rw [Category.assoc, Category.assoc, hf]

section Transfer
variable {O : Type} [CommRing O] {Gt G' : Over (Spec (CommRingCat.of O))} [GrpObj Gt] [GrpObj G']
  (K : (specO O (DualNumber O) ⟶ Gt) → (specO O (DualNumber O) ⟶ G'))
  (hmul : ∀ w w', K (w * w') = K w * K w') (hinj : Function.Injective K)
  (hnat : ∀ (φ : DualNumber O →ₐ[O] DualNumber O) w, K (ptMap φ ≫ w) = ptMap φ ≫ K w)

include hmul hinj hnat in
theorem isTan_iff (w : specO O (DualNumber O) ⟶ Gt) : IsTan w ↔ IsTan (K w) := by
  have h1 : K 1 = 1 := by
    have := hmul 1 1
    rw [_root_.mul_one] at this
    exact left_eq_mul.mp this
  have key : ∀ {G : Over (Spec (CommRingCat.of O))} [GrpObj G] (z : specO O (DualNumber O) ⟶ G),
      IsTan z ↔ ptMap (scaleD (0 : O)) ≫ z = 1 := fun z => ⟨fun h => spMap_scaleD_zero h, fun h => by
    have e : (fstD O).comp (scaleD (0 : O)) = fstD O := by
      ext
      exact TrivSqZeroExt.fst_map _ _
    have := congrArg (Chart.spMap (fstD O) ≫ ·) h
    simp only [MonObj.comp_one] at this
    refine Eq.trans ?_ this
    show _ = Chart.spMap (fstD O) ≫ Chart.spMap (scaleD (0 : O)) ≫ z
    rw [← Category.assoc, Chart.spMap_comp, e]⟩
  rw [key, key, ← hnat, ← h1]
  exact hinj.eq_iff.symm

end Transfer

theorem exists_lie_coordinates (hJ : JetAlgSt) (hD : DLinSt) {V O : Type} [CommRing V] [IsLocalRing V] [CommRing O]
    (f : V →+* O) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] {d : ℕ} (x : JetSer.Fam G (Fin d))
    (hx : IsUnivChart G d x) (Gt : Over (Spec (CommRingCat.of O))) [GrpObj Gt]
    (J : (specO O (DualNumber O) ⟶ Gt) → (specV f (DualNumber O) ⟶ G))
    (hmul : ∀ w w', J (w * w') = J w * J w') (hinj : Function.Injective J)
    (hnat : ∀ (φ : DualNumber O →ₐ[O] DualNumber O) w,
      (J (ptMap φ ≫ w)).left = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (J w).left)
    (hsurj : ∀ g : specV f (DualNumber O) ⟶ G, Spec.map (CommRingCat.ofHom (fstD O).toRingHom) ≫ g.left =
      Spec.map (CommRingCat.ofHom (fstD O).toRingHom) ≫ (1 : specV f (DualNumber O) ⟶ G).left → ∃ w, J w = g) :
    ∃ (co : LieG Gt → Fin d → O) (tv : (Fin d → O) → LieG Gt), (∀ s, (fun w => co w s) ∈ omega Gt) ∧
      (∀ b, co (tv b) = b) ∧
      (∀ b, ∃ φ : JetR V (Fin d) 1 →+* DualNumber O, (∀ i, φ (zR 1 i) = TrivSqZeroExt.inr (b i)) ∧
        (J (tv b).1).left = Spec.map (CommRingCat.ofHom φ) ≫ (x 1).left) ∧
      ∀ (u : G ⟶ G) [IsMonHom u] (ut : Gt ⟶ Gt) (α : Pt V 1 d), IsMapOf x x u α → (∀ w, J (w ≫ ut) = J w ≫ u) →
        ∀ (b : Fin d → O) (a : O), ((dLin α).map f).mulVec b = a • b →
          (tv b).1 ≫ ut = ptMap (dualScale a) ≫ (tv b).1 := by
  letI : Algebra V O := f.toAlgebra
  letI alg : Algebra V (DualNumber O) := ((algebraMap O (DualNumber O)).comp f).toAlgebra
  haveI tow : @IsScalarTower V O (DualNumber O) _ _ alg.toSMul :=
    IsScalarTower.of_algebraMap_eq (R := V) (S := O) (A := DualNumber O) fun _ => rfl
  let j := Spec.map (CommRingCat.ofHom (algebraMap V O))
  let G' := (Over.pullback j).obj G
  have hπ : IsGrpPullback G' G j (pullback.fst G.hom j) := isGrpPullback_pullback G j
  choose x' hx' using fun m => push_surjective hπ (Chart.spMap (jetCoeff V O (Fin d) m) ≫ x m)
  have hu := isUnivChart_baseChange hπ hx hx'
  choose K hK using fun w => push_surjective (A := DualNumber O) hπ (J w)
  have hK' : ∀ w, (K w).left ≫ pullback.fst G.hom j = (J w).left := fun w => congrArg (·.left) (hK w)
  have Kmul : ∀ w w', K (w * w') = K w * K w' := fun w w' =>
    push_injective hπ (by rw [push_mul, hK, hK, hK]; exact hmul w w')
  have Kinj : Function.Injective K := fun w w' h => hinj (by rw [← hK, ← hK, h])
  have Knat : ∀ (φ : DualNumber O →ₐ[O] DualNumber O) w, K (ptMap φ ≫ w) = ptMap φ ≫ K w := fun φ w =>
    push_injective hπ (Over.OverMorphism.ext (by
      rw [push_left, push_left, hK', hnat, Over.comp_left, Category.assoc, hK']; rfl))
  have htan := isTan_iff K Kmul Kinj Knat
  have lie : ∀ w : specO O (DualNumber O) ⟶ Gt,
      (ptMap (TrivSqZeroExt.fstHom O O O) ≫ w = toUnit (specO O O) ≫ η[Gt]) ↔ IsTan w := fun w => Iff.rfl
  have ex : ∀ b : Fin d → O, ∃ w : LieG Gt, K w.1 = Chart.spMap (dualLift b) ≫ x' 1 := fun b => by
    obtain ⟨w, hw⟩ := hsurj (push hπ (Chart.spMap (dualLift b) ≫ x' 1)) (by
      have h := congrArg (·.left ≫ pullback.fst G.hom j) (isTan_dualLift hu b)
      have h1 := congrArg (·.left) (push_one (A := DualNumber O) hπ)
      have h2 : Chart.spMap (fstD O) ≫ (1 : sp (R₀ := O) (DualNumber O) ⟶ G') = 1 := MonObj.comp_one _
      rw [← h2] at h
      simp only [Over.comp_left, Category.assoc] at h
      rw [push_left] at h1
      rw [h1] at h
      exact h)
    have e : K w = Chart.spMap (dualLift b) ≫ x' 1 := push_injective hπ ((hK w).trans hw)
    exact ⟨⟨w, (lie w).2 ((htan w).2 (e ▸ isTan_dualLift hu b))⟩, e⟩
  choose tv htv using ex
  let co : LieG Gt → Fin d → O := fun w => tcoord hu (K w.1) ((htan _).1 ((lie _).1 w.2))
  have hco : ∀ b, co (tv b) = b := fun b => tcoord_eq hu _ _ b (htv b)
  refine ⟨co, tv, fun s => ⟨fun w w' h => ?_, fun a w h => ?_⟩, hco, fun b => ?_, ?_⟩
  · have := tcoord_mul hu ((htan _).1 ((lie _).1 w.2)) ((htan _).1 ((lie _).1 w'.2))
    exact (congrFun (Chart.tcoord_congr hu (Kmul _ _) _ _) s).trans (congrFun this s)
  · have := tcoord_scale hu a ((htan _).1 ((lie _).1 w.2))
    exact (congrFun (Chart.tcoord_congr hu (Knat _ _) _ _) s).trans (congrFun this s)
  · refine ⟨(dualLift b).toRingHom.comp (jetCoeff V O (Fin d) 1).toRingHom, fun i => ?_, ?_⟩
    · show dualLift b (jetCoeff V O (Fin d) 1 (zR 1 i)) = _
      rw [jetCoeff_zR, dualLift_zR]
    · have h : (x' 1).left ≫ pullback.fst G.hom j = _ := congrArg (·.left) (hx' 1)
      rw [← hK', htv, Over.comp_left, Category.assoc, h, Over.comp_left, ← Category.assoc, Chart.spMap_left, Chart.spMap_left, ← Spec.map_comp]
      rfl
  · intro u _ ut α hα hut b a hb
    let u' : G' ⟶ G' := (Over.pullback j).map u
    have hu' : u'.left ≫ pullback.fst G.hom j = pullback.fst G.hom j ≫ u.left := pullback.lift_fst _ _ _
    have hm := isMapOf_baseChange hπ hJ hx' u u' α hu' hα
    have ht := (htan _).1 ((lie _).1 (tv b).2)
    have h := hD O G' G' d x' x' hu hu u' _ hm (K (tv b).1) ht (Chart.isTan_comp ht u')
    have h2 : dLin (fun i => MvPowerSeries.map (algebraMap V O) (α i)) = (dLin α).map f := by
      ext i k
      simp [dLin, RingHom.algebraMap_toAlgebra]
    have h3 : tcoord hu (K (tv b).1) ht = b := hco b
    rw [h2, h3, hb] at h
    have h4 := tcoord_scale hu a ht
    rw [h3] at h4
    apply Kinj
    rw [Knat]
    have e1 : K ((tv b).1 ≫ ut) = K (tv b).1 ≫ u' := push_injective hπ (Over.OverMorphism.ext (by
      rw [push_left, push_left, hK', hut, Over.comp_left, Over.comp_left, Category.assoc, hu', ← Category.assoc, hK']))
    rw [e1, tcoord_spec hu _ (Chart.isTan_comp ht u'), h, ← h4]
    exact (tcoord_spec hu _ _).symm

end GlobalTheory.TorsionCharacter
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormSubRight
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

noncomputable section

namespace GlobalTheory.WigSh.OmgNorm

open Formalism.FourierDecayAlt.P.Dx2.DF

section form

variable {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ)

theorem form_add_left (u v w : Fin m → ℂ) : herm H (u + v) w = herm H u w + herm H v w := by
  simp only [herm, mulVec_add, dotProduct_add]

theorem form_add_right (u v w : Fin m → ℂ) : herm H w (u + v) = herm H w u + herm H w v := by
  simp only [herm, star_add, add_dotProduct]

theorem form_sub_left (u v w : Fin m → ℂ) : herm H (u - v) w = herm H u w - herm H v w := by
  simp only [herm, mulVec_sub, dotProduct_sub]

theorem form_sub_right (u v w : Fin m → ℂ) : herm H w (u - v) = herm H w u - herm H w v := by
  simp only [herm, star_sub, sub_dotProduct]

theorem form_smul_left (c : ℂ) (u w : Fin m → ℂ) : herm H (c • u) w = c * herm H u w := by
  simp only [herm, mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem form_smul_right (c : ℂ) (u w : Fin m → ℂ) : herm H w (c • u) = star c * herm H w u := by
  simp only [herm, star_smul, smul_dotProduct, smul_eq_mul]

end form

variable {k r : ℕ}

theorem inWb_Wb (v : Fin (2 * r + k + 1) → ℂ) : inWb k r (Wb v) := by
  intro i hi
  show (if r ≤ i.val ∧ i.val ≤ r + k then v i else 0) = 0
  rw [if_neg (by omega)]

theorem split_of_free {v : Fin (2 * r + k + 1) → ℂ} (hv : ∀ a : Fin r, v (esI k r a) = 0) :
    v = (∑ a : Fin r, v (eI k r a) • ee k r a) + Wb v := by
  funext i
  have hval : ∀ a : Fin r, (eI k r a).val = a.val := fun a => rfl
  have hsum : (∑ a : Fin r, v (eI k r a) • ee k r a) i = if i.val < r then v i else 0 := by
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, ee, bvec, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    split_ifs with h
    · have hi : i = eI k r ⟨i.val, h⟩ := Fin.ext (hval ⟨i.val, h⟩).symm
      rw [Finset.sum_eq_single ⟨i.val, h⟩]
      · rw [if_pos hi, ← hi]
      · intro b _ hb
        rw [if_neg]
        intro hib
        apply hb
        apply Fin.ext
        show b.val = i.val
        rw [hib, hval]
      · intro h'
        exact absurd (Finset.mem_univ _) h'
    · apply Finset.sum_eq_zero
      intro b _
      rw [if_neg]
      intro hib
      apply h
      rw [hib, hval]
      exact b.isLt
  rw [Pi.add_apply, hsum]
  show v i = (if i.val < r then v i else 0) + (if r ≤ i.val ∧ i.val ≤ r + k then v i else 0)
  have hlt := i.isLt
  by_cases h1 : i.val < r
  · rw [if_pos h1, if_neg (by omega), add_zero]
  · rw [if_neg h1, zero_add]
    by_cases h2 : i.val ≤ r + k
    · rw [if_pos ⟨by omega, h2⟩]
    · rw [if_neg (by omega)]
      have hi : i = esI k r ⟨2 * r + k - i.val, by omega⟩ :=
        Fin.ext (by show i.val = 2 * r + k - (2 * r + k - i.val); omega)
      rw [hi]
      exact hv _

theorem form_Wb_right {v w : Fin (2 * r + k + 1) → ℂ} (hv : ∀ a : Fin r, v (esI k r a) = 0) (hw : inWb k r w) :
    herm (Hpk k r) (Wb v) w = herm (Hpk k r) v w := by
  conv_rhs => rw [split_of_free hv]
  rw [form_add_left, herm_sum_left]
  simp only [form_smul_left, h_ee_w hw, mul_zero, Finset.sum_const_zero, zero_add]

theorem form_Wb_self {v : Fin (2 * r + k + 1) → ℂ} (hv : ∀ a : Fin r, v (esI k r a) = 0) :
    herm (Hpk k r) (Wb v) (Wb v) = herm (Hpk k r) v v := by
  rw [form_Wb_right hv (inWb_Wb v)]
  have hs := split_of_free hv
  calc herm (Hpk k r) v (Wb v)
      = herm (Hpk k r) v ((∑ a : Fin r, v (eI k r a) • ee k r a) + Wb v) := by
        rw [form_add_right, herm_sum_right]
        simp [form_smul_right, herm_ee, hv]
    _ = herm (Hpk k r) v v := by rw [← hs]

theorem mul_adj {g : Mx k r} (hg : g ∈ UH (Hpk k r)) : g * (Hpk k r * gᴴ * Hpk k r) = 1 := by
  have h1 : gᴴ * Hpk k r * g = Hpk k r := hg
  have hl : (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, h1, Formalism.QuantumDeterminants.GBasic.Hpk_sq]
  exact mul_eq_one_comm.mp hl

theorem adj_last (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mx k r) :
    (Zhat k r z z' g).adjugate (Fin.last r) (Fin.last r) = Dmin k r z z' g ⟨r, by omega⟩ := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last]
  have hs : ((-1 : ℂ)) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ)) = 1 := by
    rw [Fin.val_last, ← two_mul, pow_mul]
    simp
  rw [hs, one_mul]
  rfl

theorem det_last (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mx k r) :
    (Zhat k r z z' g).det = Dmin k r z z' g (Fin.last (r + 1)) := by
  show _ = Matrix.det ((Zhat k r z z' g).submatrix (Fin.castLE le_rfl) (Fin.castLE le_rfl))
  rw [Fin.castLE_rfl, Matrix.submatrix_id_id]

private theorem herm_adjoint_mulVec_eq (g : Mx k r) (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) ((Hpk k r * gᴴ * Hpk k r) *ᵥ x) y = herm (Hpk k r) x (g *ᵥ y) := by
  unfold herm
  rw [mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Formalism.QuantumDeterminants.GBasic.Hpk_sq, Matrix.one_mul,
    star_mulVec, ← dotProduct_mulVec, mulVec_mulVec]

theorem omg_norm : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (g : Mx k r), inWb k r z → 0 < Tz k r z →
    inWb k r z' → 0 < Tz k r z' → g ∈ UH (Hpk k r) →
    inWb k r (GlobalTheory.WigSh.omg k r z z' g) ∧ herm (Hpk k r) (GlobalTheory.WigSh.omg k r z z' g) z' = 0 ∧
      (herm (Hpk k r) (GlobalTheory.WigSh.omg k r z z' g) (GlobalTheory.WigSh.omg k r z z' g)).re = Gf k r z z' g / Tz k r z' := by
  intro k r z z' g hz _ hz' hT' hg
  have hTne : (Tz k r z' : ℂ) ≠ 0 := by exact_mod_cast hT'.ne'
  have hss : herm (Hpk k r) z' z' = -((Tz k r z' : ℝ) : ℂ) := herm_self_alt
  have hsz : herm (Hpk k r) z z = -((Tz k r z : ℝ) : ℂ) := herm_self_alt
  have hs0 : herm (Hpk k r) z' z' ≠ 0 := by rw [hss]; exact neg_ne_zero.mpr hTne
  obtain ⟨u, hu⟩ : ∃ u : Fin (2 * r + k + 1) → ℂ,
      u = ∑ a, star ((Zhat k r z z' g).adjugate (Fin.last r) a) • fvec k r z a := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : Fin (2 * r + k + 1) → ℂ, v = (Hpk k r * gᴴ * Hpk k r) *ᵥ u := ⟨_, rfl⟩
  have homg : GlobalTheory.WigSh.omg k r z z' g = Formalism.FourierDecayAlt.D.prW k r z' v := by
    rw [hv, hu]; rfl
  have hkey : ∀ b : Fin (r + 1), herm (Hpk k r) v (fvec k r z' b) =
      star ((Zhat k r z z' g).det * (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (Fin.last r) b) := by
    intro b
    have hsym : ∀ a, herm (Hpk k r) (fvec k r z a) (g *ᵥ fvec k r z' b) = star (Zhat k r z z' g a b) := by
      intro a
      rw [herm_symm']
      rfl
    rw [hv, herm_adjoint_mulVec_eq, hu, herm_sum_left]
    simp only [form_smul_left, hsym, ← star_mul', ← star_sum]
    rw [← Matrix.mul_apply, Matrix.adjugate_mul, Matrix.smul_apply, smul_eq_mul]
  have hfree : ∀ a : Fin r, v (esI k r a) = 0 := by
    intro a
    rw [← herm_ee v a, ← fvec_cs z' a, hkey, Matrix.one_apply_ne (Fin.castSucc_lt_last a).ne', mul_zero,
      star_zero]
  have hlast : ∀ w : Fin (2 * r + k + 1) → ℂ, fvec k r w (Fin.last r) = w := by
    intro w
    simp [fvec]
  have hvz' : herm (Hpk k r) v z' = star (Zhat k r z z' g).det := by
    have h := hkey (Fin.last r)
    rw [hlast, Matrix.one_apply_eq, mul_one] at h
    exact h
  have hWv : herm (Hpk k r) (Wb v) z' = star (Zhat k r z z' g).det := by
    rw [form_Wb_right hfree hz', hvz']
  have hWW : herm (Hpk k r) (Wb v) (Wb v) =
      star ((Zhat k r z z' g).adjugate (Fin.last r) (Fin.last r)) *
        ((Zhat k r z z' g).adjugate (Fin.last r) (Fin.last r)) * herm (Hpk k r) z z := by
    rw [form_Wb_self hfree, hv, herm_adjoint_mulVec_eq, mulVec_mulVec, mul_adj hg, one_mulVec, hu,
      Fin.sum_univ_castSucc]
    simp only [fvec_cs, hlast]
    simp [herm_sum_left, herm_sum_right, form_add_left, form_add_right, form_smul_left, form_smul_right,
      h_ee_w hz, h_w_ee hz]
    ring
  rw [homg, prW_eq]
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    simp only [Pi.sub_apply, Pi.smul_apply, inWb_Wb v i hi, hz' i hi, smul_zero, sub_zero]
  · rw [form_sub_left, form_smul_left, div_mul_cancel₀ _ hs0, sub_self]
  · rw [form_sub_left, form_sub_right, form_sub_right, form_smul_left, form_smul_left, form_smul_right,
      form_smul_right, herm_symm' (Wb v) z', hWv, hWW, hss, hsz]
    unfold Gf
    rw [← det_last, ← adj_last]
    set d := (Zhat k r z z' g).det
    set A := (Zhat k r z z' g).adjugate (Fin.last r) (Fin.last r)
    have hT'0 : Tz k r z' ≠ 0 := hT'.ne'
    rw [Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.star_def, map_div₀, map_neg, Complex.conj_ofReal, Complex.conj_conj]
    simp only [Complex.sub_re, Complex.mul_re, Complex.div_re, Complex.neg_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.conj_re, Complex.conj_im, Complex.mul_im, Complex.div_im, Complex.neg_im,
      Complex.normSq_neg, Complex.normSq_ofReal]
    field_simp
    ring

end GlobalTheory.WigSh.OmgNorm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LeibnizDetFrameMatrixMatrixUnit
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LeibnizDetFrameMatrixMatrixUnit
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF.DetLeibniz

open Matrix QnYLeibnizW

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem trace_adjugate_mul_eq_sum_cramer {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    (A.adjugate * B).trace = ∑ j, A.cramer (fun i => B i j) j := by
  simp only [Matrix.trace, Matrix.diag]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [cramer_eq_adjugate_mulVec]
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem hasDerivAt_det_Zhat (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g X : Q.Mx k r) :
    HasDerivAt (fun t : ℝ => (Zhat k r z z' (g * NormedSpace.exp ((t : ℂ) • X))).det)
      ((Zhat k r z z' g).adjugate * Zhat k r z z' (g * X)).trace 0 := by
  have h := ReciprocityTheory.GeometryOfNumbersTheory.hasDerivAt_det (fun t : ℝ => Zhat k r z z' (g * NormedSpace.exp ((t : ℂ) • X)))
    (Zhat k r z z' (g * X)) 0 (fun i j =>
      (hermL (Hpk k r) (fvec k r z' j) (fvec k r z i)).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
        (hasDerivAt_mul_exp_smul_zero g X))
  simp only [curve_zero] at h
  exact h

theorem Zhat_add_smul (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (A B : Q.Mx k r) (c : ℂ) :
    Zhat k r z z' (A + c • B) = Zhat k r z z' A + c • Zhat k r z z' B := by
  ext i j
  simp [Zhat, herm, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add,
    dotProduct_smul]

theorem Zhat_mul_single (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Q.Mx k r)
    (p q : Fin (2 * r + k + 1)) (j : Fin (r + 1)) :
    (fun i => Zhat k r z z' (g * Matrix.single p q 1) i j) =
      fvec k r z' j q • fun i => herm (Hpk k r) (g *ᵥ bvec p) (fvec k r z i) := by
  have hv : Matrix.single p q (1 : ℂ) *ᵥ fvec k r z' j = fvec k r z' j q • bvec p := by
    rw [Matrix.single_mulVec]
    funext l
    by_cases h : l = p
    · subst h; simp [bvec]
    · simp [bvec, h]
  funext i
  simp only [Zhat, Pi.smul_apply, ← Matrix.mulVec_mulVec, hv, herm, Matrix.mulVec_smul, dotProduct_smul]

theorem det_leibniz : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (D : Set (Q.Mx k r)) (a b : Fin (Q.mdim k r 0)) (f : Q.Mx k r → E), Q.SmoothLev k r 0 D f → ∀ g ∈ Q.Glev k r 0 ∩ D, Q.EH k r (Q.posL k r 0 a) (Q.posL k r 0 b) (fun x => (Zhat k r z z' x).det • f x) g = (Zhat k r z z' g).det • Q.EH k r (Q.posL k r 0 a) (Q.posL k r 0 b) f g + (∑ j : Fin (r + 1), fvec k r z' j (Q.posL k r 0 b) * (Zhat k r z z' g).cramer (fun i => herm (Hpk k r) (g.mulVec (bvec (Q.posL k r 0 a))) (fvec k r z i)) j) • f g := by
  intro E _ _ k r z z' D a b f hf g hg
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g hg
  have hgG : g ∈ Q.Glev k r 0 := hg.1
  obtain ⟨hX1, hX2⟩ := hpart_mem (k := k) (r := r) (i := 0) a b
  set Z : Q.Mx k r := Matrix.single (Q.posL k r 0 a) (Q.posL k r 0 b) 1 with hZdef
  set X1 := hpart1 (Hpk k r) Z with hX1def
  set X2 := hpart2 (Hpk k r) Z with hX2def
  have hf1 := hasDerivAt_f f F U g X1 hU hgU hgG hF hfF hX1
  have hf2 := hasDerivAt_f f F U g X2 hU hgU hgG hF hfF hX2
  have hEf : Q.EH k r (Q.posL k r 0 a) (Q.posL k r 0 b) f g =
      fderiv ℝ F g (g * X1) + Complex.I • fderiv ℝ F g (g * X2) := by
    show RdV X1 f g + Complex.I • RdV X2 f g = _
    rw [rdV_of_hasDerivAt X1 g f _ hf1, rdV_of_hasDerivAt X2 g f _ hf2]
  have key : ∀ (φ : Q.Mx k r → ℂ) (d1 d2 : ℂ),
      HasDerivAt (fun t : ℝ => φ (g * NormedSpace.exp ((t : ℂ) • X1))) d1 0 →
      HasDerivAt (fun t : ℝ => φ (g * NormedSpace.exp ((t : ℂ) • X2))) d2 0 →
      Q.EH k r (Q.posL k r 0 a) (Q.posL k r 0 b) (fun x => φ x • f x) g =
        φ g • Q.EH k r (Q.posL k r 0 a) (Q.posL k r 0 b) f g + (d1 + Complex.I * d2) • f g := by
    intro φ d1 d2 h1 h2
    rw [hEf]
    show RdV X1 (fun x => φ x • f x) g + Complex.I • RdV X2 (fun x => φ x • f x) g = _
    rw [rdV_smul_of X1 g φ f d1 _ h1 hf1, rdV_smul_of X2 g φ f d2 _ h2 hf2]
    module
  rw [key (fun x => (Zhat k r z z' x).det) _ _ (hasDerivAt_det_Zhat k r z z' g X1)
    (hasDerivAt_det_Zhat k r z z' g X2)]
  have hsum : g * X1 + Complex.I • (g * X2) = g * Z := by
    rw [← Matrix.mul_smul, ← Matrix.mul_add, hX1def, hX2def, hpart_sum]
  have hd : ((Zhat k r z z' g).adjugate * Zhat k r z z' (g * X1)).trace +
      Complex.I * ((Zhat k r z z' g).adjugate * Zhat k r z z' (g * X2)).trace =
      ((Zhat k r z z' g).adjugate * Zhat k r z z' (g * Z)).trace := by
    rw [← hsum, Zhat_add_smul, Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
  rw [hd, trace_adjugate_mul_eq_sum_cramer]
  congr 2
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [hZdef, Zhat_mul_single, map_smul, Pi.smul_apply, smul_eq_mul]

end GlobalTheory.HatNF.DetLeibniz
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LeibnizDetFrameMatrixMatrixUnitStatement
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leibniz_det_frameMatrix_matrixUnit : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (D : Set (Q.Mx k r)) (a b : Fin (Q.mdim k r 0)) (f : Q.Mx k r → E), Q.SmoothLev k r 0 D f → ∀ g ∈ Q.Glev k r 0 ∩ D, Q.EH k r (Q.posL k r 0 a) (Q.posL k r 0 b) (fun x => (Zhat k r z z' x).det • f x) g = (Zhat k r z z' g).det • Q.EH k r (Q.posL k r 0 a) (Q.posL k r 0 b) f g + (∑ j : Fin (r + 1), fvec k r z' j (Q.posL k r 0 b) * (Zhat k r z z' g).cramer (fun i => herm (Hpk k r) (g.mulVec (bvec (Q.posL k r 0 a))) (fvec k r z i)) j) • f g := by
  first | exact @GlobalTheory.HatNF.DetLeibniz.det_leibniz | exact GlobalTheory.HatNF.DetLeibniz.det_leibniz | (intros; apply GlobalTheory.HatNF.DetLeibniz.det_leibniz <;> assumption)
end
end
