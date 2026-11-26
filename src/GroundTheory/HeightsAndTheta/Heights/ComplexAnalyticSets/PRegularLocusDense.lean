module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.OsgoodSeparate
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSerreRFlatAscent
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PInjectiveHolomorphicJacobianNeZero

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegularLocusDense
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Module
open scoped ContDiff

section Germs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem eventually_zero_of_iteratedFDeriv_diag {ψ : E → ℂ} {y₀ : E} (hψ : AnalyticAt ℂ ψ y₀)
    (h0 : ∀ (n : ℕ) (v : E), iteratedFDeriv ℂ n ψ y₀ (fun _ => v) = 0) :
    ∀ᶠ u in 𝓝 y₀, ψ u = 0 := by
  obtain ⟨p, r, hp⟩ := hψ
  filter_upwards [Metric.eball_mem_nhds y₀ hp.r_pos] with u hu
  have hmem : u - y₀ ∈ Metric.eball (0 : E) r := by
    simpa [Metric.mem_eball, edist_eq_enorm_sub] using hu
  have hs := hp.hasSum_iteratedFDeriv hmem
  simp only [h0, smul_zero, add_sub_cancel] at hs
  exact hs.unique hasSum_zero

theorem iteratedFDeriv_succ_diag_eq {ψ : E → ℂ} {y₀ : E} (hψ : AnalyticAt ℂ ψ y₀) (n : ℕ) (v : E) :
    iteratedFDeriv ℂ (n + 1) ψ y₀ (fun _ => v) =
      iteratedFDeriv ℂ n (fun y => fderiv ℂ ψ y v) y₀ (fun _ => v) := by
  rw [iteratedFDeriv_succ_apply_right]
  have hc : ContDiffAt ℂ ω (fderiv ℂ ψ) y₀ := hψ.fderiv.contDiffAt
  have h1 := (ContinuousLinearMap.apply ℂ ℂ v).iteratedFDeriv_comp_left hc (i := n) le_top
  have h2 : (fun y => fderiv ℂ ψ y v) = (ContinuousLinearMap.apply ℂ ℂ v) ∘ fderiv ℂ ψ := rfl
  rw [h2, h1]
  rfl

theorem eventually_zero_of_conormal_zero {C : Set E} {y₀ : E} (hy₀ : y₀ ∈ C) {U : Set E} (hU : U ∈ 𝓝 y₀)
    (hC : ∀ c ∈ C ∩ U, ∀ ψ : E → ℂ, AnalyticAt ℂ ψ c → (∀ᶠ u in 𝓝 c, u ∈ C → ψ u = 0) →
      fderiv ℂ ψ c = 0)
    {ψ : E → ℂ} (hψ : AnalyticAt ℂ ψ y₀) (hψC : ∀ᶠ u in 𝓝 y₀, u ∈ C → ψ u = 0) :
    ∀ᶠ u in 𝓝 y₀, ψ u = 0 := by
  have step : ∀ φ : E → ℂ, AnalyticAt ℂ φ y₀ → (∀ᶠ u in 𝓝 y₀, u ∈ C → φ u = 0) → ∀ v : E,
      AnalyticAt ℂ (fun y => fderiv ℂ φ y v) y₀ ∧ ∀ᶠ u in 𝓝 y₀, u ∈ C → fderiv ℂ φ u v = 0 := by
    intro φ hφ hφC v
    refine ⟨((ContinuousLinearMap.apply ℂ ℂ v).analyticAt _).comp hφ.fderiv, ?_⟩
    filter_upwards [hφ.eventually_analyticAt, hφC.eventually_nhds, hU] with c hca hcC hcU hc
    rw [hC c ⟨hc, hcU⟩ φ hca hcC]
    rfl
  have key : ∀ n : ℕ, ∀ φ : E → ℂ, AnalyticAt ℂ φ y₀ → (∀ᶠ u in 𝓝 y₀, u ∈ C → φ u = 0) →
      ∀ v : E, iteratedFDeriv ℂ n φ y₀ (fun _ => v) = 0 := by
    intro n
    induction n with
    | zero => intro φ _ hφC v; simpa using hφC.self_of_nhds hy₀
    | succ n ih =>
      intro φ hφ hφC v
      rw [iteratedFDeriv_succ_diag_eq hφ]
      obtain ⟨h1, h2⟩ := step φ hφ hφC v
      exact ih _ h1 h2 v
  exact eventually_zero_of_iteratedFDeriv_diag hψ fun n v => key n ψ hψ hψC v

end Germs

noncomputable def conormalSpan {σ : Type} [Fintype σ] (Y : Set (σ → ℂ)) (z : σ → ℂ) :
    Submodule ℂ ((σ → ℂ) →L[ℂ] ℂ) :=
  Submodule.span ℂ {ℓ | ∃ h : (σ → ℂ) → ℂ, AnalyticAt ℂ h z ∧ (∀ᶠ u in 𝓝 z, u ∈ Y → h u = 0) ∧
    fderiv ℂ h z = ℓ}

theorem exists_maxRank_equations {σ : Type} [Fintype σ] (Y : Set (σ → ℂ)) {U : Set (σ → ℂ)}
    (hU : IsOpen U) (hne : (Y ∩ U).Nonempty) :
    ∃ a ∈ Y, ∃ (ι : Type) (_ : Fintype ι) (h : ι → (σ → ℂ) → ℂ) (W : Set (σ → ℂ)),
      IsOpen W ∧ a ∈ W ∧ W ⊆ U ∧ (∀ j, ∀ z ∈ W, AnalyticAt ℂ (h j) z) ∧
      (∀ j, ∀ z ∈ W, z ∈ Y → h j z = 0) ∧ LinearIndependent ℂ (fun j => fderiv ℂ (h j) a) ∧
      ∀ z ∈ W ∩ Y, ∀ ψ : (σ → ℂ) → ℂ, AnalyticAt ℂ ψ z → (∀ᶠ u in 𝓝 z, u ∈ Y → ψ u = 0) →
        fderiv ℂ ψ z ∈ Submodule.span ℂ (Set.range fun j => fderiv ℂ (h j) z) := by
  classical
  set rk : (σ → ℂ) → ℕ := fun z => finrank ℂ (conormalSpan Y z) with hrk
  have hbdd : BddAbove (rk '' (Y ∩ U)) :=
    ⟨finrank ℂ ((σ → ℂ) →L[ℂ] ℂ), by rintro _ ⟨z, -, rfl⟩; exact Submodule.finrank_le _⟩
  obtain ⟨a, haYU, har⟩ := Nat.sSup_mem (hne.image rk) hbdd
  have hmax : ∀ z ∈ Y ∩ U, rk z ≤ rk a := fun z hz => har ▸ le_csSup hbdd ⟨z, hz, rfl⟩
  obtain ⟨b, hbS, hbspan, hbli⟩ := exists_linearIndependent ℂ
    {ℓ : (σ → ℂ) →L[ℂ] ℂ | ∃ h : (σ → ℂ) → ℂ, AnalyticAt ℂ h a ∧ (∀ᶠ u in 𝓝 a, u ∈ Y → h u = 0) ∧
      fderiv ℂ h a = ℓ}
  have : Finite b := hbli.finite
  let _ : Fintype b := Fintype.ofFinite b
  have hb' : ∀ ℓ : b, ∃ h : (σ → ℂ) → ℂ, AnalyticAt ℂ h a ∧ (∀ᶠ u in 𝓝 a, u ∈ Y → h u = 0) ∧
      fderiv ℂ h a = ℓ := fun ℓ => hbS ℓ.2
  choose h hha hhY hhd using hb'
  have hfun : (fun j : b => fderiv ℂ (h j) a) = ((↑) : b → (σ → ℂ) →L[ℂ] ℂ) := funext hhd
  have hli_a : LinearIndependent ℂ (fun j => fderiv ℂ (h j) a) := hfun ▸ hbli
  have hcard : rk a = Fintype.card b := by
    have hsp : conormalSpan Y a = Submodule.span ℂ (Set.range fun j : b => fderiv ℂ (h j) a) := by
      rw [hfun, Subtype.range_coe, hbspan]
      rfl
    show finrank ℂ (conormalSpan Y a) = _
    rw [hsp]
    exact finrank_span_eq_card hli_a
  have E3 : ∀ᶠ z in 𝓝 a, LinearIndependent ℂ (fun j => fderiv ℂ (h j) z) := by
    have ht : Tendsto (fun z => fun j => fderiv ℂ (h j) z) (𝓝 a) (𝓝 fun j => fderiv ℂ (h j) a) :=
      tendsto_pi_nhds.2 fun j => (hha j).fderiv.continuousAt.tendsto
    exact ht.eventually hli_a.eventually
  have E : ∀ᶠ z in 𝓝 a, z ∈ U ∧ (∀ j, AnalyticAt ℂ (h j) z) ∧ (∀ j, z ∈ Y → h j z = 0) ∧
      LinearIndependent ℂ (fun j => fderiv ℂ (h j) z) :=
    (show ∀ᶠ z in 𝓝 a, z ∈ U from hU.mem_nhds haYU.2).and ((eventually_all.2 fun j => (hha j).eventually_analyticAt).and
      ((eventually_all.2 hhY).and E3))
  obtain ⟨W, hWP, hWo, haW⟩ := eventually_nhds_iff.1 E
  refine ⟨a, haYU.1, b, inferInstance, h, W, hWo, haW, fun z hz => (hWP z hz).1,
    fun j z hz => (hWP z hz).2.1 j, fun j z hz => (hWP z hz).2.2.1 j, hli_a, ?_⟩
  rintro z ⟨hzW, hzY⟩ ψ hψ hψY
  obtain ⟨hzU, hza, -, hzli⟩ := hWP z hzW
  have hle : Submodule.span ℂ (Set.range fun j => fderiv ℂ (h j) z) ≤ conormalSpan Y z := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨j, rfl⟩
    refine Submodule.subset_span ⟨h j, hza j, ?_, rfl⟩
    filter_upwards [hWo.mem_nhds hzW] with u hu huY using (hWP u hu).2.2.1 j huY
  have heq : Submodule.span ℂ (Set.range fun j => fderiv ℂ (h j) z) = conormalSpan Y z :=
    Submodule.eq_of_le_of_finrank_le hle
      (by rw [finrank_span_eq_card hzli, ← hcard]; exact hmax z ⟨hzY, hzU⟩)
  rw [heq]
  exact Submodule.subset_span ⟨ψ, hψ, hψY, rfl⟩

theorem RegularLocusDense.proof (hIFT : AnalyticImplicitChart.Statement) : RegularLocusDense.Statement := by
  intro σ _ X w hX
  obtain ⟨N, k, f, hNo, hwN, hf, hXN⟩ := hX
  refine ⟨N, hNo, hwN, fun B hBo hBN x hx => ?_⟩
  rw [mem_closure_iff_nhds]
  intro t ht
  have hU : IsOpen (interior t ∩ B) := isOpen_interior.inter hBo
  obtain ⟨a, haY, ι, hι, h, W, hWo, haW, hWU, hha, hhY, hli, hspan⟩ :=
    exists_maxRank_equations (X ∩ B) hU ⟨x, hx, mem_interior_iff_mem_nhds.2 ht, hx.2⟩
  obtain ⟨d, A, O, V, g, -, hOo, hVo, haV, hVW, hg, hAg, hVO⟩ :=
    hIFT σ ι h a W (fun j => hha j a haW) (fun j => hhY j a haW haY) hli (hWo.mem_nhds haW)

  have hgV : ∀ y ∈ O, g y ∈ V ∧ ∀ j, h j (g y) = 0 := fun y hy =>
    (show g y ∈ {z | z ∈ V ∧ ∀ j, h j z = 0} from hVO ▸ Set.mem_image_of_mem g hy)
  have hYV : ∀ z ∈ X ∩ B, z ∈ V → g (A z) = z ∧ A z ∈ O := by
    intro z hzY hzV
    have hz : z ∈ g '' O := hVO ▸ (⟨hzV, fun j => hhY j z (hVW hzV) hzY⟩ : z ∈ {z | z ∈ V ∧ ∀ j, h j z = 0})
    obtain ⟨y, hy, rfl⟩ := hz
    rw [hAg y hy]
    exact ⟨rfl, hy⟩
  obtain ⟨hga, hy₀O⟩ := hYV a haY haV

  have hAD : ∀ y ∈ O, A.comp (fderiv ℂ g y) = ContinuousLinearMap.id ℂ _ := by
    intro y hy
    have h3 : HasFDerivAt (fun y => A (g y)) (A.comp (fderiv ℂ g y)) y :=
      A.hasFDerivAt.comp y (hg y hy).differentiableAt.hasFDerivAt
    have h4 : HasFDerivAt (fun y => A (g y)) (ContinuousLinearMap.id ℂ (Fin d → ℂ)) y :=
      (hasFDerivAt_id y).congr_of_eventuallyEq (by filter_upwards [hOo.mem_nhds hy] with u hu using hAg u hu)
    exact h3.unique h4
  have hhD : ∀ y ∈ O, ∀ j, (fderiv ℂ (h j) (g y)).comp (fderiv ℂ g y) = 0 := by
    intro y hy j
    have h3 : HasFDerivAt (fun y => h j (g y)) ((fderiv ℂ (h j) (g y)).comp (fderiv ℂ g y)) y :=
      (hha j (g y) (hVW (hgV y hy).1)).differentiableAt.hasFDerivAt.comp y
        (hg y hy).differentiableAt.hasFDerivAt
    have h4 : HasFDerivAt (fun y => h j (g y)) (0 : (Fin d → ℂ) →L[ℂ] ℂ) y :=
      (hasFDerivAt_const 0 y).congr_of_eventuallyEq
        (by filter_upwards [hOo.mem_nhds hy] with u hu using (hgV u hu).2 j)
    exact h3.unique h4

  have hC : ∀ c ∈ {y | y ∈ O ∧ g y ∈ X ∩ B} ∩ O, ∀ ψ : (Fin d → ℂ) → ℂ, AnalyticAt ℂ ψ c →
      (∀ᶠ u in 𝓝 c, u ∈ {y | y ∈ O ∧ g y ∈ X ∩ B} → ψ u = 0) → fderiv ℂ ψ c = 0 := by
    rintro c ⟨⟨hcO, hcY⟩, -⟩ ψ hψ hψC
    have hzV := (hgV c hcO).1
    have hAz : A (g c) = c := hAg c hcO
    have hψ' : AnalyticAt ℂ ψ (A (g c)) := by rw [hAz]; exact hψ
    have hH : AnalyticAt ℂ (fun u => ψ (A u)) (g c) := hψ'.comp (A.analyticAt (g c))
    have hHY : ∀ᶠ u in 𝓝 (g c), u ∈ X ∩ B → ψ (A u) = 0 := by
      have hAt : Tendsto A (𝓝 (g c)) (𝓝 c) := by
        have h0 := A.continuous.tendsto (g c)
        rwa [hAz] at h0
      filter_upwards [hVo.mem_nhds hzV, hAt hψC] with u huV huψ huY
      obtain ⟨hgu, huO⟩ := hYV u huY huV
      exact huψ ⟨huO, hgu.symm ▸ huY⟩
    have hmem := hspan (g c) ⟨hVW hzV, hcY⟩ _ hH hHY
    have hchain : fderiv ℂ (fun u => ψ (A u)) (g c) = (fderiv ℂ ψ c).comp A := by
      have hψd : HasFDerivAt ψ (fderiv ℂ ψ c) (A (g c)) := by
        rw [hAz]; exact hψ.differentiableAt.hasFDerivAt
      exact (hψd.comp (g c) A.hasFDerivAt).fderiv
    have hkill : ∀ ℓ ∈ Submodule.span ℂ (Set.range fun j => fderiv ℂ (h j) (g c)),
        ℓ.comp (fderiv ℂ g c) = 0 := by
      intro ℓ hℓ
      induction hℓ using Submodule.span_induction with
      | mem x hx => obtain ⟨j, rfl⟩ := hx; exact hhD c hcO j
      | zero => simp
      | add x y _ _ hx hy => rw [ContinuousLinearMap.add_comp, hx, hy, add_zero]
      | smul r x _ hx =>
        rw [ContinuousLinearMap.smul_comp, hx]
        ext v
        simp
    have hk := hkill _ hmem
    rw [hchain, ContinuousLinearMap.comp_assoc, hAD c hcO, ContinuousLinearMap.comp_id] at hk
    exact hk

  have hvan : ∀ i, ∀ᶠ y in 𝓝 (A a), f i (g y) = 0 := by
    intro i
    refine eventually_zero_of_conormal_zero (C := {y | y ∈ O ∧ g y ∈ X ∩ B})
      ⟨hy₀O, hga.symm ▸ haY⟩ (hOo.mem_nhds hy₀O) hC ?_ ?_
    · have hfa : AnalyticAt ℂ (f i) (g (A a)) := hga.symm ▸ hf i a (hBN haY.2)
      exact hfa.comp (hg (A a) hy₀O)
    · refine Eventually.of_forall fun y hy => ?_
      have hgy : g y ∈ X ∩ N := ⟨hy.2.1, hBN hy.2.2⟩
      rw [hXN] at hgy
      exact hgy.2 i
  obtain ⟨O', hO'P, hO'o, hy₀O'⟩ :=
    eventually_nhds_iff.1 ((eventually_all.2 hvan).and (hOo.mem_nhds hy₀O))
  refine ⟨a, interior_subset (hWU haW).1, haY, d, A, O', V ∩ A ⁻¹' O', g, hO'o,
    hVo.inter (hO'o.preimage A.continuous), ⟨haV, hy₀O'⟩, hg.mono fun y hy => (hO'P y hy).2,
    fun y hy => hAg y (hO'P y hy).2, ?_⟩
  ext z
  constructor
  · rintro ⟨hzY, hzV, hzO'⟩
    exact ⟨A z, hzO', (hYV z hzY hzV).1⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hf0, hyO⟩ := hO'P y hy
    have hgyV := (hgV y hyO).1
    have hgB : g y ∈ B := (hWU (hVW hgyV)).2
    have hgX : g y ∈ X := by
      have hz : g y ∈ {z | z ∈ N ∧ ∀ i, f i z = 0} := ⟨hBN hgB, hf0⟩
      rw [← hXN] at hz
      exact hz.1
    refine ⟨⟨hgX, hgB⟩, hgyV, ?_⟩
    show A (g y) ∈ O'
    rw [hAg y hyO]
    exact hy

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHolGermsUFD
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

noncomputable section

def HolGermsUFD.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (w : σ → ℂ), UniqueFactorizationMonoid (holGerms w)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StProjectionInjectiveOffHypersurface
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

def ProjectionInjectiveOffHypersurface.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (k : ℕ),
    I.IsPrime → ringKrullDim (MvPolynomial σ ℂ ⧸ I) = (k : ℕ) →
    ∃ h : MvPolynomial σ ℂ, h ∉ I ∧ ∀ z ∈ zeroSetIn I, eval z h ≠ 0 →
      ∃ W : Set (σ → ℂ), IsOpen W ∧ z ∈ W ∧
        ∃ A : (σ → ℂ) →L[ℂ] (Fin k → ℂ), Set.InjOn A (zeroSetIn I ∩ W)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchInverseOffHypersurface
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

def BranchInverseOffHypersurface.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (k : ℕ),
    I.IsPrime → ringKrullDim (MvPolynomial σ ℂ ⧸ I) = (k : ℕ) →
    ∃ h' : MvPolynomial σ ℂ, h' ∉ I ∧
      ∀ (U : Set (Fin k → ℂ)) (φ : (Fin k → ℂ) → σ → ℂ) (ψ : (σ → ℂ) → Fin k → ℂ),
        IsOpen U → DifferentiableOn ℂ φ U → Set.InjOn φ U → Set.MapsTo φ U (zeroSetIn I) →
        (∀ t ∈ U, ψ (φ t) = t) →
        HolomorphicOnSubset ψ ((φ '' U) \ {z | eval z h' = 0})

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteProjectionOffZerosDense
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def FiniteProjectionOffZerosDense.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear X w → GermIrreducibleAt X w →
    (∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w) →
    (∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ X → h (A z) = 0) →
        ∀ᶠ y in 𝓝 (A w), h y = 0) →
    ∀ δ : (Fin d → ℂ) → ℂ, AnalyticAt ℂ δ (A w) → (¬ ∀ᶠ y in 𝓝 (A w), δ y = 0) →
      ∃ N ∈ 𝓝 w, X ∩ N ⊆ closure {z | z ∈ X ∧ δ (A z) ≠ 0}

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIrreducibleGermRegularConnected
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem IrreducibleGermRegularConnected.proof (hpar : LocalParametrisation.Statement)
    (hsheets : ParametrisationSheetsConnected.Statement) :
    IrreducibleGermRegularConnected.Statement := by
  intro σ _ X w hX hirr U hU
  obtain ⟨d, A, B, D, δ, N, hBU, hP⟩ := hpar σ X w hX hirr U hU
  have hS := hsheets σ X w B d A D δ N hP hirr
  obtain ⟨hBo, hwXB, -, -, -, -, -, -, -, -, hchart, hdense⟩ := hP

  have hSreg : {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} ⊆ regLocus (X ∩ B) := by
    rintro x ⟨hxXB, hx⟩
    obtain ⟨O, V, g, hO, hV, hxV, hg, hAg, hXV⟩ := hchart x hxXB hx
    exact ⟨hxXB, d, A, O, V, g, hO, hV, hxV, hg, hAg, hXV⟩
  exact ⟨B, hBo, hwXB.2, hBU, hS.subset_closure hSreg ((regLocus_subset _).trans hdense)⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteProjectionSheetedClosureEquations
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def FiniteProjectionSheetedClosureEquations.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear X w →
    (∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w) →
    (∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ X → h (A z) = 0) →
        ∀ᶠ y in 𝓝 (A w), h y = 0) →
    ∀ δ : (Fin d → ℂ) → ℂ, AnalyticAt ℂ δ (A w) →
      (∃ M ∈ 𝓝 w, ∀ y ∈ X ∩ M, δ (A y) ≠ 0 → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ))
        (g : (Fin d → ℂ) → σ → ℂ), IsOpen O ∧ IsOpen V ∧ y ∈ V ∧ AnalyticOnNhd ℂ g O ∧
          (∀ t ∈ O, A (g t) = t) ∧ X ∩ V = g '' O) →
      ∃ (m : ℕ) (c : Fin m → (σ → ℂ) → ℂ), (∀ k, AnalyticAt ℂ (c k) w) ∧
        (∀ᶠ z in 𝓝 w, z ∈ X → δ (A z) ≠ 0 → ∀ k, c k z = 0) ∧
        (∀ᶠ z in 𝓝 w, z ∈ X → (∀ k, c k z = 0) → z ∈ closure {x | x ∈ X ∧ δ (A x) ≠ 0})

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimeGermCanonicalCover
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

def PrimeGermCanonicalCover.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (w : σ → ℂ) (k : ℕ) (p : Fin k → (σ → ℂ) → ℂ),
    (∀ i, AnalyticAt ℂ (p i) w) → (holGermIdeal w p).IsPrime →
    ∃ (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (ℓ : (σ → ℂ) →L[ℂ] ℂ) (N : ℕ) (δ : (Fin d → ℂ) → ℂ),
      AnalyticAt ℂ δ (A w) ∧
      (¬ ∃ h : Fin k → (σ → ℂ) → ℂ, (∀ i, AnalyticAt ℂ (h i) w) ∧
          ∀ᶠ z in 𝓝 w, δ (A z) = ∑ i, h i z * p i z) ∧
      (∀ g : (σ → ℂ) → ℂ, AnalyticAt ℂ g w →
        ∃ (M : ℕ) (a : Fin N → (Fin d → ℂ) → ℂ) (h : Fin k → (σ → ℂ) → ℂ),
          (∀ j, AnalyticAt ℂ (a j) (A w)) ∧ (∀ i, AnalyticAt ℂ (h i) w) ∧
          ∀ᶠ z in 𝓝 w, δ (A z) ^ M * g z - ∑ j, a j (A z) * ℓ z ^ (j : ℕ) = ∑ i, h i z * p i z) ∧
      ∀ W ∈ 𝓝 w, ∀ᶠ y in 𝓝 (A w), δ y ≠ 0 →
        ∃ x : Fin N → σ → ℂ, (∀ j, x j ∈ W ∧ (∀ i, p i (x j) = 0) ∧ A (x j) = y) ∧
          Function.Injective fun j => ℓ (x j)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PUnbranchedProperCountConstant
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem UnbranchedProperCountConstant.proof (hloc : UnbranchedProperCountLocallyConstant.Statement)
    (hconn : ManifoldZerosComplementConnected.Statement) : UnbranchedProperCountConstant.Statement := by
  intro σ _ Y d A D δ hD hDc hmap hprop hδ hsec
  by_cases hne : ∃ y ∈ D, δ y ≠ 0
  swap
  · push Not at hne
    exact ⟨0, fun y hy hy' => absurd (hne y hy) hy'⟩
  obtain ⟨y₀, hy₀D, hy₀⟩ := hne
  have hreg : ∀ y ∈ D, IsRegularPointOf D y := fun y hy =>
    ⟨hy, d, ContinuousLinearMap.id ℂ _, D, D, id, hD, hD, hy, analyticOnNhd_id, fun _ _ => rfl, by simp⟩
  have hS : IsPreconnected (D \ {z | δ z = 0}) := hconn (Fin d) D δ hDc hreg hδ ⟨y₀, hy₀D, hy₀⟩
  have hL := hloc σ Y d A D δ hD hmap hprop hsec
  let f : (Fin d → ℂ) → ℕ := fun y => {x | x ∈ Y ∧ A x = y}.ncard
  have hcont : ContinuousOn f (D \ {z | δ z = 0}) := by
    intro y hy
    refine ContinuousAt.continuousWithinAt ((continuousAt_const (y := f y)).congr ?_)
    filter_upwards [(hL y hy.1 hy.2).2] with y' hy'
    simp only [f, Set.ncard_def, hy']
  refine ⟨f y₀, fun y hy hyδ => ?_⟩
  rw [← (hL y hy hyδ).1.cast_ncard_eq]
  exact congrArg _ (hS.constant hcont ⟨hy, hyδ⟩ ⟨hy₀D, hy₀⟩)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSerreCriterion
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing

theorem isRegularLocalRing_of_isIntegrallyClosed_of_ringKrullDim_le_one (B : Type*) [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] [IsDomain B] [IsIntegrallyClosed B] (h : ringKrullDim B ≤ 1) : IsRegularLocalRing B := by
  by_cases hf : IsField B
  · let := hf.toField
    infer_instance
  · have : Ring.KrullDimLE 1 B := Ring.krullDimLE_iff.mpr (by exact_mod_cast h)
    have hm : maximalIdeal B ≠ ⊥ := fun hm => hf (isField_iff_maximalIdeal_eq.mpr hm)
    have h3 : IsIntegrallyClosed B ∧ ∃! P : Ideal B, P ≠ ⊥ ∧ P.IsPrime :=
      ⟨inferInstance, maximalIdeal B, ⟨hm, inferInstance⟩, fun P ⟨hP, hPp⟩ =>
        IsLocalRing.eq_maximalIdeal (hPp.isMaximal_of_ne_bot hP)⟩
    have hdvr : IsDiscreteValuationRing B := ((IsDiscreteValuationRing.TFAE B hf).out 1 4).mpr h3
    infer_instance

theorem SerreCriterion.proof (hS : NormalLocalDepthTwo.Statement) (hN : SerreNormalOfRegularDepth.Statement) :
    SerreCriterion.Statement := by
  intro A _ hA
  refine ⟨fun h => ⟨fun P _ hdim => ?_, fun P _ => ?_⟩, fun h => hN A hA h.1 h.2⟩
  · obtain ⟨hd, hi⟩ := h P
    exact isRegularLocalRing_of_isIntegrallyClosed_of_ringKrullDim_le_one _ (by exact_mod_cast hdim)
  · obtain ⟨hd, hi⟩ := h P
    exact hS _

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteGermProjectionCover
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem FiniteGermProjectionCover.proof (hopen : IrreducibleGermProjectionOpenNear.Statement)
    (hcov : ProperOpenProjectionCover.Statement) : FiniteGermProjectionCover.Statement := by
  intro σ _ X w d A hX hirr hiso hinj
  obtain ⟨N₀, hN₀, hop⟩ := hopen σ X w d A hX hirr hiso hinj
  obtain ⟨N, k, f, hNo, hwN, hf, hXN⟩ := hX
  refine ⟨interior N₀ ∩ N, Filter.inter_mem (interior_mem_nhds.2 hN₀) (hNo.mem_nhds hwN), ?_⟩
  intro B D hBo hBN hwB hDo hDc hmaps hprop hisoB
  have hBN' : B ⊆ N := fun x hx => (hBN hx).2

  have hzero : X ∩ B = {z | z ∈ B ∧ ∀ i, f i z = 0} := by
    ext z
    constructor
    · rintro ⟨hzX, hzB⟩
      have h1 : z ∈ X ∩ N := ⟨hzX, hBN' hzB⟩
      rw [hXN] at h1
      exact ⟨hzB, h1.2⟩
    · rintro ⟨hzB, hz⟩
      have h2 : z ∈ {z | z ∈ N ∧ ∀ i, f i z = 0} := ⟨hBN' hzB, hz⟩
      rw [← hXN] at h2
      exact ⟨h2.1, hzB⟩

  have hopB : ∀ x ∈ X ∩ B, ∀ V ∈ 𝓝 x, A '' (X ∩ B ∩ V) ∈ 𝓝 (A x) := by
    intro x hx V hV
    have h1 := hop x ⟨hx.1, interior_subset (hBN hx.2).1⟩ (V ∩ B)
      (Filter.inter_mem hV (hBo.mem_nhds hx.2))
    have h2 : X ∩ (V ∩ B) = X ∩ B ∩ V := by
      ext z
      simp only [Set.mem_inter_iff]
      tauto
    rwa [h2] at h1
  obtain ⟨δ, M, hδ, hδne, hcount, hgraph, hdense⟩ :=
    hcov σ X B k f d A D hBo (fun i => (hf i).mono hBN') hzero hDo hDc ⟨A w, hmaps hwB⟩ hmaps hprop hopB
  exact ⟨δ, M, hBo, hwB, hDo, hDc, hmaps, hprop, hisoB, hδ, hδne, hcount, hgraph, hdense⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIrreducibleGermComplementConnected
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

theorem IrreducibleGermComplementConnected.proof (hdense : RegularLocusDense.Statement)
    (hconn : IrreducibleGermRegularConnected.Statement)
    (hzeros : ManifoldZerosComplementConnected.Statement) :
    IrreducibleGermComplementConnected.Statement := by
  intro σ _ X w h hX hirr hh hnot U hU
  obtain ⟨N, hNo, hwN, hN⟩ := hdense σ X w hX
  have hU' : U ∩ N ∩ {z | AnalyticAt ℂ h z} ∈ 𝓝 w :=
    inter_mem (inter_mem hU (hNo.mem_nhds hwN)) hh.eventually_analyticAt
  obtain ⟨B, hBo, hwB, hBU, hR⟩ := hconn σ X w hX hirr _ hU'
  have hBh : ∀ z ∈ B, AnalyticAt ℂ h z := fun z hz => (hBU hz).2
  have hcl : X ∩ B ⊆ closure (regLocus (X ∩ B)) := hN B hBo fun z hz => (hBU hz).1.2

  have hcl' : (X ∩ B) \ {z | h z = 0} ⊆ closure (regLocus (X ∩ B) \ {z | h z = 0}) := by
    rintro z ⟨hzXB, hz0⟩
    rw [mem_closure_iff_nhds]
    intro t ht
    have hne : {y | h y ≠ 0} ∈ 𝓝 z := (hBh z hzXB.2).continuousAt.eventually_ne hz0
    obtain ⟨y, ⟨hyt, hyh⟩, hyR⟩ := mem_closure_iff_nhds.1 (hcl hzXB) _ (inter_mem ht hne)
    exact ⟨y, hyt, hyR, hyh⟩

  have hex : ∃ x ∈ regLocus (X ∩ B), h x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hnot
    filter_upwards [hBo.mem_nhds hwB] with z hzB hzX
    by_contra hz0
    obtain ⟨y, hyR, hyh⟩ := closure_nonempty_iff.1 ⟨z, hcl' ⟨⟨hzX, hzB⟩, hz0⟩⟩
    exact hyh (hcon y hyR)
  have hRc : IsPreconnected (regLocus (X ∩ B) \ {z | h z = 0}) :=
    hzeros σ _ h hR (fun x hx => isRegularPointOf_regLocus hx)
      (fun x hx => hBh x (regLocus_subset _ hx).2) hex
  exact ⟨B, hBo, hwB, fun z hz => (hBU hz).1.1,
    hRc.subset_closure (Set.sdiff_subset_sdiff_left (regLocus_subset _)) hcl'⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIsolatedPointsCount
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology ComplexSets

noncomputable section

theorem exists_minimalPrime_mem_zeroSet {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) {x : Fin n → ℂ}
    (hx : x ∈ zeroSet J) : ∃ P ∈ J.minimalPrimes, x ∈ zeroSet P := by
  have hJ : J ≤ RingHom.ker (eval x) := fun q hq => (RingHom.mem_ker).2 (hx q hq)
  have : (RingHom.ker (eval x : MvPolynomial (Fin n) ℂ →+* ℂ)).IsPrime := RingHom.ker_isPrime _
  obtain ⟨P, hP, hPle⟩ := Ideal.exists_minimalPrimes_le hJ
  exact ⟨P, hP, fun q hq => (RingHom.mem_ker).1 (hPle hq)⟩

theorem mem_isolatedFibrePts_of_le {n m : ℕ} {J P : Ideal (MvPolynomial (Fin n) ℂ)} (hJP : J ≤ P)
    (Q : Fin m → MvPolynomial (Fin n) ℂ) (z : Fin m → ℂ) {x : Fin n → ℂ}
    (hx : x ∈ isolatedFibrePts J Q z) (hxP : x ∈ zeroSet P) : x ∈ isolatedFibrePts P Q z := by
  obtain ⟨-, hQ, V, hV, hiso⟩ := hx
  exact ⟨hxP, hQ, V, hV, fun x' hx' hQ' => hiso x' ⟨fun q hq => hx'.1 q (hJP hq), hx'.2⟩ hQ'⟩

theorem encard_biUnion_finset_le {ι α : Type*} (S : Finset ι) (f : ι → Set α) :
    (⋃ i ∈ S, f i).encard ≤ ∑ i ∈ S, (f i).encard := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.set_biUnion_insert]
    exact (Set.encard_union_le _ _).trans (add_le_add_right ih _)

theorem IsolatedPointsCount.proof (hPrime : IsolatedPointsCountPrime.Statement) :
    IsolatedPointsCount.Statement := by
  classical
  intro n m J Q
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin n) ℂ) J
  have hN : ∀ P ∈ J.minimalPrimes, ∃ N : ℕ, ∀ z : Fin m → ℂ, (isolatedFibrePts P Q z).encard ≤ N :=
    fun P hP => hPrime n m P hP.1.1 Q
  choose! N hN using hN
  refine ⟨∑ P ∈ hfin.toFinset, N P, fun z => ?_⟩
  have hsub : isolatedFibrePts J Q z ⊆ ⋃ P ∈ hfin.toFinset, isolatedFibrePts P Q z := by
    intro x hx
    obtain ⟨P, hP, hxP⟩ := exists_minimalPrime_mem_zeroSet J hx.1
    exact Set.mem_biUnion (hfin.mem_toFinset.2 hP) (mem_isolatedFibrePts_of_le hP.1.2 Q z hx hxP)
  calc (isolatedFibrePts J Q z).encard
      ≤ (⋃ P ∈ hfin.toFinset, isolatedFibrePts P Q z).encard := Set.encard_le_encard hsub
    _ ≤ ∑ P ∈ hfin.toFinset, (isolatedFibrePts P Q z).encard := encard_biUnion_finset_le _ _
    _ ≤ ∑ P ∈ hfin.toFinset, ((N P : ℕ) : ℕ∞) :=
        Finset.sum_le_sum fun P hP => hN P (hfin.mem_toFinset.1 hP) z
    _ = ((∑ P ∈ hfin.toFinset, N P : ℕ) : ℕ∞) := by push_cast; rfl

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFlatNormalFibres
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing RingTheory.Sequence

theorem SerreRAt.of_ringEquiv {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B) {k : ℕ}
    (h : SerreRAt A k) : SerreRAt B k := fun hd => by
  have := h (by rwa [ringKrullDim_eq_of_ringEquiv e])
  exact IsRegularLocalRing.of_ringEquiv e

theorem SerreSAt.of_ringEquiv {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (e : A ≃+* B) {k : ℕ} (h : SerreSAt A k) : SerreSAt B k := by
  obtain ⟨rs, hmem, hreg, hlen⟩ := h
  refine ⟨rs.map e, ?_, ?_, ?_⟩
  · intro r hr
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
    have := hmem s hs
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at this ⊢
    exact fun hu => this ((isUnit_map_iff e s).mp hu)
  · refine (AddEquiv.isWeaklyRegular_congr (e := e.toAddEquiv) ?_).mp hreg
    exact List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun r _ x => by
      simp [smul_eq_mul])
  · rwa [List.length_map, ← ringKrullDim_eq_of_ringEquiv e]

noncomputable def localizationAtMaximalEquiv (B : Type*) [CommRing B] [IsLocalRing B] :
    Localization.AtPrime (maximalIdeal B) ≃+* B :=
  (IsLocalization.atUnits B (maximalIdeal B).primeCompl (fun x hx => by
    simpa [Ideal.primeCompl, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, IsUnit.mem_submonoid_iff] using hx)).toRingEquiv.symm

theorem normalRing_of_isIntegrallyClosed (B : Type*) [CommRing B] [IsDomain B] [IsIntegrallyClosed B] :
    NormalRing B := fun P _ =>
  ⟨inferInstance, isIntegrallyClosed_of_isLocalization (Localization.AtPrime P) P.primeCompl
    P.primeCompl_le_nonZeroDivisors⟩

theorem serreAt_of_isIntegrallyClosed (hC : SerreCriterion.Statement) (B : Type) [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] [IsDomain B] [IsIntegrallyClosed B] : SerreRAt B 1 ∧ SerreSAt B 2 := by
  obtain ⟨h1, h2⟩ := (hC B inferInstance).mp (normalRing_of_isIntegrallyClosed B)
  exact ⟨(h1 (maximalIdeal B)).of_ringEquiv (localizationAtMaximalEquiv B),
    (h2 (maximalIdeal B)).of_ringEquiv (localizationAtMaximalEquiv B)⟩

theorem FlatNormalFibres.proof (hC : SerreCriterion.Statement) (hR : SerreRFlatAscent.Statement)
    (hS : SerreSFlatAscent.Statement) : FlatNormalFibres.Statement := by
  intro R S _ _ _ hRn hSn hloc hflat hdom hic hfib
  obtain ⟨hR1, hR2⟩ := (hC R hRn).mp (normalRing_of_isIntegrallyClosed R)
  have hfib' : ∀ (P : Ideal S) [P.IsPrime],
      SerreRAt (primeFibreLocalRing R P) 1 ∧ SerreSAt (primeFibreLocalRing R P) 2 := fun P _ => by
    obtain ⟨h1, h2⟩ := hfib P
    exact serreAt_of_isIntegrallyClosed hC _
  have hN : NormalRing S := (hC S hSn).mpr
    ⟨hR R S hRn hSn hflat 1 hR1 fun P _ => (hfib' P).1, hS R S hRn hSn hflat 2 hR2 fun P _ => (hfib' P).2⟩
  obtain ⟨hd, hi⟩ := hN (maximalIdeal S)
  exact ⟨(localizationAtMaximalEquiv S).symm.toMulEquiv.isDomain,
    IsIntegrallyClosed.of_equiv (localizationAtMaximalEquiv S)⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegularLocusIdentity
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology Filter

theorem IsRegularPointOf.exists_ball_chart {σ : Type} [Fintype σ] {Y : Set (σ → ℂ)} {z : σ → ℂ}
    (hz : IsRegularPointOf Y z) {W : Set (σ → ℂ)} (hW : W ∈ 𝓝 z) :
    ∃ (d : ℕ) (V : Set (σ → ℂ)) (B : Set (Fin d → ℂ)) (g : (Fin d → ℂ) → σ → ℂ),
      IsOpen V ∧ z ∈ V ∧ V ⊆ W ∧ IsOpen B ∧ IsPreconnected B ∧ AnalyticOnNhd ℂ g B ∧
        Y ∩ V = g '' B := by
  obtain ⟨hzY, d, A, O, V, g, hO, hV, hzV, hg, hAg, hYV⟩ := hz
  have hzO : z ∈ g '' O := by rw [← hYV]; exact ⟨hzY, hzV⟩
  obtain ⟨y₀, hy₀O, rfl⟩ := hzO
  have hN : interior W ∩ V ∈ 𝓝 (g y₀) := inter_mem (interior_mem_nhds.2 hW) (hV.mem_nhds hzV)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1
    (inter_mem (hO.mem_nhds hy₀O) ((hg y₀ hy₀O).continuousAt.preimage_mem_nhds hN))
  refine ⟨d, V ∩ interior W ∩ A ⁻¹' Metric.ball y₀ r, Metric.ball y₀ r, g,
    (hV.inter isOpen_interior).inter (Metric.isOpen_ball.preimage A.continuous),
    ⟨⟨hzV, mem_interior_iff_mem_nhds.2 hW⟩, ?_⟩, fun x hx => interior_subset hx.1.2,
    Metric.isOpen_ball, (convex_ball y₀ r).isPreconnected, fun y hy => hg y (hball hy).1, ?_⟩
  · show A (g y₀) ∈ Metric.ball y₀ r
    rw [hAg y₀ hy₀O]
    exact Metric.mem_ball_self hr
  · ext x
    constructor
    · rintro ⟨hxY, ⟨hxV, -⟩, hxB⟩
      have hx : x ∈ g '' O := by rw [← hYV]; exact ⟨hxY, hxV⟩
      obtain ⟨y, hyO, rfl⟩ := hx
      have hyB : A (g y) ∈ Metric.ball y₀ r := hxB
      rw [hAg y hyO] at hyB
      exact ⟨y, hyB, rfl⟩
    · rintro ⟨y, hyB, rfl⟩
      have hyO : y ∈ O := (hball hyB).1
      have hyN : g y ∈ interior W ∩ V := (hball hyB).2
      have hgy : g y ∈ Y ∩ V := by rw [hYV]; exact ⟨y, hyO, rfl⟩
      refine ⟨hgy.1, ⟨hyN.2, hyN.1⟩, ?_⟩
      show A (g y) ∈ Metric.ball y₀ r
      rw [hAg y hyO]
      exact hyB

theorem eq_zero_on_chart_of_eventually_eq_zero {σ : Type} [Fintype σ] {Y V : Set (σ → ℂ)} {d : ℕ}
    {B : Set (Fin d → ℂ)} {g : (Fin d → ℂ) → σ → ℂ} (hBo : IsOpen B) (hBc : IsPreconnected B)
    (hg : AnalyticOnNhd ℂ g B) (hYV : Y ∩ V = g '' B) (F : (σ → ℂ) → ℂ) (hF : AnalyticOnNhd ℂ F V)
    (h0 : ∃ y ∈ Y ∩ V, ∀ᶠ u in 𝓝 y, u ∈ Y → F u = 0) : ∀ u ∈ Y ∩ V, F u = 0 := by
  obtain ⟨y, hy, hyF⟩ := h0
  have hgB : ∀ t ∈ B, g t ∈ Y ∩ V := fun t ht => by rw [hYV]; exact ⟨t, ht, rfl⟩
  have hy' : y ∈ g '' B := by rw [← hYV]; exact hy
  obtain ⟨t₀, ht₀, rfl⟩ := hy'
  have hFg : AnalyticOnNhd ℂ (F ∘ g) B := fun t ht => (hF (g t) (hgB t ht).2).comp (hg t ht)
  have hev : F ∘ g =ᶠ[𝓝 t₀] 0 := by
    filter_upwards [(hg t₀ ht₀).continuousAt.tendsto.eventually hyF, hBo.mem_nhds ht₀] with t ht htB
    exact ht (hgB t htB).1
  have hzero := hFg.eqOn_zero_of_preconnected_of_eventuallyEq_zero hBc ht₀ hev
  intro u hu
  have hu' : u ∈ g '' B := by rw [← hYV]; exact hu
  obtain ⟨t, ht, rfl⟩ := hu'
  exact hzero ht

theorem RegularLocusIdentity.proof (hreg : RegularOffHypersurface.Statement) :
    RegularLocusIdentity.Statement := by
  intro σ _ I hI
  obtain ⟨h, hhI, hh⟩ := hreg σ I hI
  refine ⟨h, hhI, fun z hz hhz W hW => ?_⟩
  obtain ⟨d, V, B, g, hVo, hzV, hVW, hBo, hBc, hg, hYV⟩ := (hh z hz hhz).exists_ball_chart hW
  exact ⟨V, hVo, hzV, hVW, fun F hF h0 => eq_zero_on_chart_of_eventually_eq_zero hBo hBc hg hYV F hF h0⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLocalParametrisation
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem exists_proper_projection_nbhd {σ : Type} [Fintype σ] {X : Set (σ → ℂ)} {w : σ → ℂ} {d : ℕ}
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (hX : IsAnalyticNear X w) (hw : w ∈ X)
    (hiso : ∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w) {U : Set (σ → ℂ)} (hU : U ∈ 𝓝 w) :
    ∃ (B : Set (σ → ℂ)) (D : Set (Fin d → ℂ)), IsOpen B ∧ B ⊆ U ∧ w ∈ X ∩ B ∧ IsOpen D ∧
      IsPreconnected D ∧ Set.MapsTo A (X ∩ B) D ∧
      (∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ X ∩ B ∧ A x ∈ K}) ∧
      (∀ x ∈ X ∩ B, A x = A w → x = w) := by
  obtain ⟨N, k, f, hNo, hwN, hf, hXN⟩ := hX
  obtain ⟨W, hW, hisoW⟩ := hiso
  obtain ⟨r₀, hr₀, hball⟩ :=
    Metric.mem_nhds_iff.1 (Filter.inter_mem (Filter.inter_mem hU (hNo.mem_nhds hwN)) hW)
  set r := r₀ / 2 with hr
  have hr0 : 0 < r := half_pos hr₀
  have hcb : Metric.closedBall w r ⊆ U ∩ N ∩ W :=
    (Metric.closedBall_subset_ball (half_lt_self hr₀)).trans hball

  set Z : Set (σ → ℂ) := Metric.closedBall w r ∩ ⋂ i, (Metric.closedBall w r ∩ f i ⁻¹' {0}) with hZ
  have hZc : IsClosed Z := by
    refine Metric.isClosed_closedBall.inter (isClosed_iInter fun i => ?_)
    exact ((hf i).continuousOn.mono fun z hz => (hcb hz).1.2).preimage_isClosed_of_isClosed
      Metric.isClosed_closedBall isClosed_singleton
  have hZk : IsCompact Z := (isCompact_closedBall w r).of_isClosed_subset hZc Set.inter_subset_left
  have hZX : ∀ z ∈ Metric.closedBall w r, (z ∈ X ↔ z ∈ Z) := by
    intro z hz
    have hzN : z ∈ N := (hcb hz).1.2
    constructor
    · intro hzX
      have h1 : z ∈ X ∩ N := ⟨hzX, hzN⟩
      rw [hXN] at h1
      exact ⟨hz, Set.mem_iInter.2 fun i => ⟨hz, h1.2 i⟩⟩
    · intro hzZ
      have h2 : z ∈ {z | z ∈ N ∧ ∀ i, f i z = 0} := ⟨hzN, fun i => (Set.mem_iInter.1 hzZ.2 i).2⟩
      rw [← hXN] at h2
      exact h2.1

  have hSk : IsCompact (Z ∩ Metric.sphere w r) := hZk.inter_right Metric.isClosed_sphere
  have hAS : A w ∉ A '' (Z ∩ Metric.sphere w r) := by
    rintro ⟨x, ⟨hxZ, hxs⟩, hxA⟩
    have hxcb : x ∈ Metric.closedBall w r := Metric.sphere_subset_closedBall hxs
    have hxw := hisoW x ⟨(hZX x hxcb).2 hxZ, (hcb hxcb).2⟩ hxA
    rw [hxw, Metric.mem_sphere, dist_self] at hxs
    exact hr0.ne hxs
  obtain ⟨ε, hε, hεS⟩ :=
    Metric.mem_nhds_iff.1 ((hSk.image A.continuous).isClosed.isOpen_compl.mem_nhds hAS)
  refine ⟨Metric.ball w r ∩ A ⁻¹' Metric.ball (A w) ε, Metric.ball (A w) ε,
    Metric.isOpen_ball.inter (Metric.isOpen_ball.preimage A.continuous), ?_,
    ⟨hw, Metric.mem_ball_self hr0, Set.mem_preimage.mpr (Metric.mem_ball_self hε)⟩, Metric.isOpen_ball,
    (convex_ball _ _).isPreconnected, fun x hx => hx.2.2, ?_, ?_⟩
  · exact fun x hx => (hcb (Metric.ball_subset_closedBall hx.1)).1.1
  · intro K hKD hK
    have heq : {x | x ∈ X ∩ (Metric.ball w r ∩ A ⁻¹' Metric.ball (A w) ε) ∧ A x ∈ K} =
        Z ∩ A ⁻¹' K := by
      ext x
      constructor
      · rintro ⟨⟨hxX, hxb, -⟩, hxK⟩
        exact ⟨(hZX x (Metric.ball_subset_closedBall hxb)).1 hxX, hxK⟩
      · rintro ⟨hxZ, hxK⟩
        have hxcb : x ∈ Metric.closedBall w r := hxZ.1
        refine ⟨⟨(hZX x hxcb).2 hxZ, ?_, hKD hxK⟩, hxK⟩
        by_contra hxb
        have hxs : x ∈ Metric.sphere w r :=
          Metric.mem_sphere.2 (le_antisymm (Metric.mem_closedBall.1 hxcb)
            (not_lt.1 fun h => hxb (Metric.mem_ball.2 h)))
        exact hεS (hKD hxK) ⟨x, ⟨hxZ, hxs⟩, rfl⟩
    rw [heq]
    exact hZk.inter_right (hK.isClosed.preimage A.continuous)
  · exact fun x hx hxA => hisoW x ⟨hx.1, (hcb (Metric.ball_subset_closedBall hx.2.1)).2⟩ hxA

theorem LocalParametrisation.proof (hproj : GermFiniteProjection.Statement)
    (hcov : FiniteGermProjectionCover.Statement) : LocalParametrisation.Statement := by
  intro σ _ X w hX hirr U hU
  obtain ⟨d, A, hiso, hinj⟩ := hproj σ X w hX hirr
  obtain ⟨N₀, hN₀, hcovB⟩ := hcov σ X w d A hX hirr hiso hinj
  obtain ⟨B, D, hBo, hBU, hwB, hDo, hDc, hmaps, hprop, hisoB⟩ :=
    exists_proper_projection_nbhd A hX hirr.1 hiso (Filter.inter_mem hU hN₀)
  obtain ⟨δ, N, hP⟩ :=
    hcovB B D hBo (hBU.trans Set.inter_subset_right) hwB hDo hDc hmaps hprop hisoB
  exact ⟨d, A, B, D, δ, N, hBU.trans Set.inter_subset_left, hP⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFormalFibresRegular
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

theorem FormalFibresRegular.proof (hQ : FormalFibreQuotient.Statement)
    (hP : FormalFibresRegularPolynomial.Statement) : FormalFibresRegular.Statement := by
  intro k A _ _ _ hA m hm P _
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hA
  have hfs : Function.Surjective (f : MvPolynomial (Fin n) k →+* A) := hf
  obtain ⟨P', -, ⟨e⟩⟩ :=
    hQ (MvPolynomial (Fin n) k) A (f : MvPolynomial (Fin n) k →+* A) hfs inferInstance m P
  have hM : (m.comap (f : MvPolynomial (Fin n) k →+* A)).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ hfs (H := hm)
  have := hP k n _ hM P'.asIdeal
  exact IsRegularLocalRing.of_ringEquiv e.symm

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end
