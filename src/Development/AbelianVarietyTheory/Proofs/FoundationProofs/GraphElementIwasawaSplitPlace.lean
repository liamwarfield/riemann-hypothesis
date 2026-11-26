module

public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.GraphHeightLattice
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelIteratedIntegralsSwap
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDoubledHermitianSpaceNonsplitPlace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitMulPowOfKummerVanishesOnInertiaCurve

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GraphElementIwasawaSplitPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GraphElementIwasawaSplitPlace
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.IndefiniteRowSideFullHecke.GraphHeightLattice
open Formalism.UG (GLint)

namespace GlobalTheory.GraphIwSplit

theorem isHermND_dblGram {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) : IsHermND σ (dblGram finSumFinEquiv J) := by
  refine ⟨fun i j => ?_, ?_⟩
  · obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective j
    simp only [dblGram, blkMat, Matrix.submatrix_apply, Equiv.symm_apply_apply]
    rcases a with a | a <;> rcases b with b | b <;> simp [hJ.1]
  · rw [dblGram, det_blkMat]
    exact mul_ne_zero hJ.2 (by rw [Matrix.det_neg]; exact mul_ne_zero (pow_ne_zero _ (by simp)) hJ.2)

theorem graph_iwasawa_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J) (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsFullLattice E L] (v : HeightOneSpectrum (𝓞 F)), IsSelfDualAt σ J L v → Nonempty (E →ₐ[F] Fv F v) → ∀ g : GLoc σ J v, ∃ p : siegelH (Fv F v) σ (dblGram finSumFinEquiv J), ∃ k ∈ KFin σ (dblGram finSumFinEquiv J) L v, ioH (Fv F v) σ rfl (g, 1) = (p : GLoc σ (dblGram finSumFinEquiv J) v) * k := by
  intro F E _ _ _ _ _ σ h n J hJ L _ v hL ⟨τ⟩ g
  exact GlobalTheory.Core.Rk.IwSplit.hasIwasawa_of_algHom h rfl hJ (isHermND_dblGram σ hJ) τ L hL _

end GlobalTheory.GraphIwSplit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GraphElementIwasawaSplitPlaceStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.IndefiniteRowSideFullHecke.GraphHeightLattice
open Formalism.UG (GLint)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graph_element_iwasawa_split_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J) (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsFullLattice E L] (v : HeightOneSpectrum (𝓞 F)), IsSelfDualAt σ J L v → Nonempty (E →ₐ[F] Fv F v) → ∀ g : GLoc σ J v, ∃ p : siegelH (Fv F v) σ (dblGram finSumFinEquiv J), ∃ k ∈ KFin σ (dblGram finSumFinEquiv J) L v, ioH (Fv F v) σ rfl (g, 1) = (p : GLoc σ (dblGram finSumFinEquiv J) v) * k := by
  first | exact @GlobalTheory.GraphIwSplit.graph_iwasawa_split | exact GlobalTheory.GraphIwSplit.graph_iwasawa_split | (intros; apply GlobalTheory.GraphIwSplit.graph_iwasawa_split <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GraphElementIwasawaInertPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GraphElementIwasawaInertPlace
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.IndefiniteRowSideFullHecke.GraphHeightLattice
open Formalism.UG (GLint)

noncomputable section
namespace GlobalTheory.InertIwasawaGen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_trace_one_loc {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {v : HeightOneSpectrum (𝓞 F)}
    {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w) :
    ∃ τ ∈ intLoc F E v, τ + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ τ = 1 := by
  have hu := (GlobalTheory.LFun.InertChart.under_eq_iff hw w).2 rfl
  obtain ⟨x, hx⟩ := GlobalTheory.LFun.InertChart.exists_conj_sub_unit h hw
  have hσ := GlobalTheory.LFun.InertChart.conj_conj h
  have h0 : σ (x : E) - x ≠ 0 := by
    intro e; rw [e, map_zero] at hx; exact zero_ne_one hx
  set t : E := σ x / (σ x - x) with ht
  have hsum : t + σ t = 1 := by
    rw [ht, map_div₀, map_sub, hσ, ← neg_sub (σ (x : E)) x, div_neg, ← sub_eq_add_neg, ← sub_div, div_self h0]
  refine ⟨(1 : Fv F v) ⊗ₜ[F] t, ?_, ?_⟩
  · rw [GlobalTheory.LFun.InertChart.mem_intLoc_iff hw hu, GlobalTheory.LFun.toCompl_tmul, map_one, one_mul]
    have hval : ∀ a : E, Valued.v (algebraMap E (w.adicCompletion E) a) = w.valuation E a := fun a =>
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
    change Valued.v (algebraMap E (w.adicCompletion E) t) ≤ 1
    rw [hval, ht, map_div₀, hx, div_one]
    exact w.valuation_le_one (RingOfIntegers.mapRingHom (σ : E →+* E) x)
  · change (1 : Fv F v) ⊗ₜ[F] t + 1 ⊗ₜ[F] σ t = 1
    rw [← TensorProduct.tmul_add, hsum]; rfl

open GlobalTheory.LFun GlobalTheory.InertIwasawa in
theorem hasIwasawa_of_inertAt {σ : E →ₐ[F] E} (hC : IsCMExt F E σ) {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) {Q : Matrix (Fin (n + n)) (Fin (n + n)) E}
    (hQ : Q = dblGram finSumFinEquiv J) {L : Submodule (𝓞 E) (Fin n → E)} [Submodule.IsFullLattice E L]
    {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w)
    (hL : IsSelfDualAt σ J L v) : HasIwasawa σ Q (KFin σ Q L v) := fun g => by
  have h := (InertChart.under_eq_iff hw w).2 rfl
  obtain ⟨τ, hτO, hτ⟩ := exists_trace_one_loc hC hw
  obtain ⟨a, ha⟩ := Frames.exists_isLatticeFrame (F := F) L
  have eQ : JR (F := F) (Fv F v) Q = dblGram finSumFinEquiv (JR (Fv F v) J) := hQ ▸ JR_dblGram _ J
  obtain ⟨k, h1, h2, h3⟩ := exists_stab finSumFinEquiv (intLoc F E v)
    (hasFrames_of_equiv _ (w.adicCompletionIntegers E) (InertChart.complEquiv hw h) (InertChart.mem_intLoc_iff hw h))
    (σ := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ) (fun _ => sigR_mem_intLoc σ) (sigR_invol (InertChart.conj_conj hC))
    hτO hτ
    (J := JR (Fv F v) J) (by ext i j; exact congrArg (fun x => (1 : Fv F v) ⊗ₜ[F] x) (hJ.1 i j))
    ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_det_JR hJ.2)) (Λ := latLoc F L v)
    (fun y => Submodule.ext_iff.1 hL y) (ha v) (g := matHom _ σ Q g) (eQ ▸ g.2)
  let κ : GLoc σ Q v := ⟨k, (eQ ▸ h1 : k ∈ Formalism.UG.UJ _ (JR (Fv F v) Q))⟩
  have hκ : κ ∈ KFin σ Q L v := by
    change k ∈ Formalism.UG.stabGL _
    rwa [latLoc_sumLat]
  exact ⟨⟨g * κ, h3⟩, κ⁻¹, inv_mem hκ, (mul_inv_cancel_right g κ).symm⟩

theorem ioH_mem_siegel_mul_KFin : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J)
    (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsFullLattice E L] (v : HeightOneSpectrum (𝓞 F)),
    IsSelfDualAt σ J L v → ∀ P : HeightOneSpectrum (𝓞 E), IsInertUnder v P → ∀ g : GLoc σ J v,
      ∃ p : siegelH (Fv F v) σ (dblGram finSumFinEquiv J), ∃ k ∈ KFin σ (dblGram finSumFinEquiv J) L v,
        ioH (Fv F v) σ rfl (g, 1) = (p : GLoc σ (dblGram finSumFinEquiv J) v) * k := by
  intro F E _ _ _ _ _ σ h n J hJ L _ v hL P hP g
  exact hasIwasawa_of_inertAt h hJ rfl (w := P) hP hL _

end GlobalTheory.InertIwasawaGen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GraphElementIwasawaInertPlaceStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.IndefiniteRowSideFullHecke.GraphHeightLattice
open Formalism.UG (GLint)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graph_element_iwasawa_inert_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J) (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsFullLattice E L] (v : HeightOneSpectrum (𝓞 F)), IsSelfDualAt σ J L v → ∀ P : HeightOneSpectrum (𝓞 E), IsInertUnder v P → ∀ g : GLoc σ J v, ∃ p : siegelH (Fv F v) σ (dblGram finSumFinEquiv J), ∃ k ∈ KFin σ (dblGram finSumFinEquiv J) L v, ioH (Fv F v) σ rfl (g, 1) = (p : GLoc σ (dblGram finSumFinEquiv J) v) * k := by
  first | exact @GlobalTheory.InertIwasawaGen.ioH_mem_siegel_mul_KFin | exact GlobalTheory.InertIwasawaGen.ioH_mem_siegel_mul_KFin | (intros; apply GlobalTheory.InertIwasawaGen.ioH_mem_siegel_mul_KFin <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EdgeClassEqKummerCharacterOfChosenRootFunctionFi
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EdgeClassEqKummerCharacterOfChosenRootFunctionFi
open GlobalTheory.K4 GlobalTheory.KEdge GlobalTheory.NeedB Polynomial

namespace GlobalTheory.K4.TopSpec

variable {F K Ω : Type} [Field F] [Field K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω]

theorem _root_.GlobalTheory.K4.TopSpec.res_mem_geo (g : Ω ≃ₐ[K] Ω) :
    AlgEquiv.restrictScalarsHom F g ∈ _root_.GlobalTheory.K4.geo F K Ω := by
  rw [_root_.GlobalTheory.K4.TopW.mem_geo]
  intro z
  exact g.commutes z

theorem _root_.GlobalTheory.K4.TopSpec.exists_res {g : Ω ≃ₐ[F] Ω}
    (hg : g ∈ _root_.GlobalTheory.K4.geo F K Ω) :
    ∃ g' : Ω ≃ₐ[K] Ω, AlgEquiv.restrictScalarsHom F g' = g := by
  rw [_root_.GlobalTheory.K4.TopW.mem_geo] at hg
  refine ⟨{ g.toRingEquiv with commutes' := hg }, ?_⟩
  ext y
  rfl

theorem _root_.GlobalTheory.K4.TopSpec.continuous_res [Algebra.IsAlgebraic K Ω] :
    Continuous (AlgEquiv.restrictScalarsHom F : (Ω ≃ₐ[K] Ω) →* (Ω ≃ₐ[F] Ω)) := by
  classical
  apply continuous_of_continuousAt_one
  rw [ContinuousAt, map_one]
  intro s hs
  rw [krullTopology_mem_nhds_one_iff] at hs
  obtain ⟨E, hE, hEs⟩ := hs
  rw [Filter.mem_map, krullTopology_mem_nhds_one_iff]
  let b := Module.finBasis F E
  refine ⟨IntermediateField.adjoin K (Set.range fun i => (b i : Ω)), ?_, ?_⟩
  · exact IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  · intro g hg
    apply hEs
    have hfix : ∀ i, g (b i : Ω) = b i := fun i =>
      (IntermediateField.mem_fixingSubgroup_iff _ _).mp hg _
        (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    have key : ∀ z : E, AlgEquiv.restrictScalarsHom F g (z : Ω) = z := by
      intro z
      induction (b.mem_span z) using Submodule.span_induction with
      | mem u hu =>
        obtain ⟨i, rfl⟩ := hu
        exact hfix i
      | zero => simp
      | add u v _ _ hu hv => rw [IntermediateField.coe_add, map_add (f := _), hu, hv]
      | smul a u _ hu => rw [IntermediateField.coe_smul, map_smul, hu]
    exact key ⟨y, hy⟩

end GlobalTheory.K4.TopSpec

theorem _root_.GlobalTheory.K4.isTopW_topW : ∀ (k K Ω F : Type) [Field k]
    [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Algebra (RatFunc k) K]
    [IsScalarTower k[X] (RatFunc k) K] [FiniteDimensional (RatFunc k) K] [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] [Field F] [Algebra F K] [Algebra F Ω] [IsScalarTower F K Ω] [Normal F K]
    (N : ℕ) (ζ : Ω), 0 < N → IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[F] Ω, g ζ = ζ) →
    (∀ τ : K ≃ₐ[F] K, ∀ x ∈ FunctionField.ringOfIntegers k K,
      τ x ∈ FunctionField.ringOfIntegers k K) →
    ∀ (a b : F) (α β : Ω), a ≠ 0 → b ≠ 0 → algebraMap F K a ∈ FunctionField.ringOfIntegers k K →
      (algebraMap F K a)⁻¹ ∈ FunctionField.ringOfIntegers k K →
      algebraMap F K b ∈ FunctionField.ringOfIntegers k K →
      (algebraMap F K b)⁻¹ ∈ FunctionField.ringOfIntegers k K →
      α ^ N = algebraMap F Ω a → β ^ N = algebraMap F Ω b →
    ∀ (x y : (Ω ≃ₐ[F] Ω) →* Multiplicative (ZMod N)),
      (∀ g, (x g).toAdd = _root_.GlobalTheory.NeedB.kum (N := N) ζ α g) →
      (∀ g, (y g).toAdd = _root_.GlobalTheory.NeedB.kum (N := N) ζ β g) →
    ∀ η : (Ω ≃ₐ[F] Ω) → ZMod N,
      _root_.GlobalTheory.KEdge.CobOn (_root_.GlobalTheory.K4.geo F K Ω) x y η →
      IsLocallyConstant (fun g : _root_.GlobalTheory.K4.geo F K Ω => η g) →
      (∀ (B : ValuationSubring Ω) (g : Ω ≃ₐ[F] Ω),
        _root_.GlobalTheory.NeedB.Over (FunctionField.ringOfIntegers k K).toSubring B →
        (∀ z, B.valuation z ≤ 1 → B.valuation (g z - z) < 1) →
        g ∈ _root_.GlobalTheory.K4.geo F K Ω → η g = 0) →
    ∀ σ : Ω ≃ₐ[F] Ω, _root_.GlobalTheory.K4.IsTopW (K := K) ζ x y η σ
      (_root_.GlobalTheory.K4.topW (K := K) ζ x y η σ) := by
  intro k K Ω F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ N ζ hN hζ hfix _ a b α β ha hb _ _ _ _ hα hβ
    x y hx hy η hcob hη _ σ
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : CharZero (RatFunc k) :=
    charZero_of_injective_algebraMap (algebraMap k (RatFunc k)).injective
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap (RatFunc k) K).injective
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  haveI : Algebra.IsAlgebraic F Ω := Algebra.IsAlgebraic.trans F K Ω
  set H := _root_.GlobalTheory.K4.geo F K Ω with hH
  haveI : H.Normal := ⟨fun h hh g => _root_.GlobalTheory.K4.TopW.conj_mem_geo g hh⟩
  obtain ⟨hhom, -, -⟩ := _root_.GlobalTheory.KEdge.edge_cup_props _ N H x y η hcob
  have hres := _root_.GlobalTheory.K4.TopSpec.continuous_res (F := F) (K := K) (Ω := Ω)
  have hmem : ∀ g : Ω ≃ₐ[K] Ω, AlgEquiv.restrictScalarsHom F g ∈ H :=
    _root_.GlobalTheory.K4.TopSpec.res_mem_geo
  have hne : ∀ {γ : Ω} {c : F}, c ≠ 0 → γ ^ N = algebraMap F Ω c → γ ≠ 0 := by
    intro γ c hc hγ h0
    rw [h0, zero_pow hN.ne'] at hγ
    exact hc ((algebraMap F Ω).injective (hγ.symm.trans (map_zero _).symm))
  have hkum : ∀ {γ : Ω} {c : F}, c ≠ 0 → γ ^ N = algebraMap F Ω c →
      IsLocallyConstant (_root_.GlobalTheory.NeedB.kum (K := F) (N := N) ζ γ) :=
    fun hc hγ => (_root_.GlobalTheory.NeedB.KumLemma.kummer_character_main F Ω N ζ _ hN hζ hfix
      (hne hc hγ) ⟨_, hγ.symm⟩).1
  have hx_lc : IsLocallyConstant fun g : Ω ≃ₐ[K] Ω =>
      Multiplicative.toAdd (x (AlgEquiv.restrictScalarsHom F g)) := by
    have hfun : (fun g : Ω ≃ₐ[K] Ω => Multiplicative.toAdd (x (AlgEquiv.restrictScalarsHom F g))) =
        _root_.GlobalTheory.NeedB.kum ζ α ∘ AlgEquiv.restrictScalarsHom F := funext fun g => hx _
    rw [hfun]
    exact (hkum ha hα).comp_continuous hres
  have hy_lc : IsLocallyConstant fun g : Ω ≃ₐ[K] Ω =>
      Multiplicative.toAdd (y (AlgEquiv.restrictScalarsHom F g)) := by
    have hfun : (fun g : Ω ≃ₐ[K] Ω => Multiplicative.toAdd (y (AlgEquiv.restrictScalarsHom F g))) =
        _root_.GlobalTheory.NeedB.kum ζ β ∘ AlgEquiv.restrictScalarsHom F := funext fun g => hy _
    rw [hfun]
    exact (hkum hb hβ).comp_continuous hres
  have hη₁ : IsLocallyConstant fun g : Ω ≃ₐ[K] Ω => η (AlgEquiv.restrictScalarsHom F g) :=
    hη.comp_continuous (f := fun g : Ω ≃ₐ[K] Ω => (⟨AlgEquiv.restrictScalarsHom F g, hmem g⟩ : H))
      (hres.subtype_mk _)
  have hη₂ : IsLocallyConstant fun g : Ω ≃ₐ[K] Ω => η (σ * AlgEquiv.restrictScalarsHom F g * σ⁻¹) :=
    hη.comp_continuous (f := fun g : Ω ≃ₐ[K] Ω =>
      (⟨σ * AlgEquiv.restrictScalarsHom F g * σ⁻¹,
        _root_.GlobalTheory.K4.TopW.conj_mem_geo σ (hmem g)⟩ : H))
      (((continuous_const.mul hres).mul continuous_const).subtype_mk _)
  let χ : (Ω ≃ₐ[K] Ω) → ZMod N := fun g =>
    _root_.GlobalTheory.KEdge.edge x y η σ (AlgEquiv.restrictScalarsHom F g)
  have hlc : IsLocallyConstant χ := by
    have hfun : χ = fun g => η (σ * AlgEquiv.restrictScalarsHom F g * σ⁻¹) -
        η (AlgEquiv.restrictScalarsHom F g) -
        Multiplicative.toAdd (x (AlgEquiv.restrictScalarsHom F g)) * Multiplicative.toAdd (y σ) +
        Multiplicative.toAdd (x σ) * Multiplicative.toAdd (y (AlgEquiv.restrictScalarsHom F g)) :=
      rfl
    rw [hfun]
    exact ((hη₂.comp₂ hη₁ (· - ·)).comp₂ (hx_lc.comp (· * Multiplicative.toAdd (y σ))) (· - ·)).comp₂
      (hy_lc.comp (Multiplicative.toAdd (x σ) * ·)) (· + ·)
  have hadd : ∀ g ∈ (⊥ : IntermediateField K Ω).fixingSubgroup,
      ∀ h ∈ (⊥ : IntermediateField K Ω).fixingSubgroup, χ (g * h) = χ g + χ h := by
    intro g _ h _
    simp only [χ, map_mul]
    exact hhom σ _ (hmem g) _ (hmem h)
  obtain ⟨θ, hθ0, hθN, hθ⟩ :=
    _root_.GlobalTheory.kummer_generator_of_char K Ω N ζ hN hζ (fun g => hfix (AlgEquiv.restrictScalarsHom F g)) ⊥ χ hlc hadd
  obtain ⟨w, hw⟩ := IntermediateField.mem_bot.mp hθN
  apply _root_.GlobalTheory.K4.TopW.isTopW_topW_of_exists
  refine ⟨w, ?_, θ, hw.symm, ?_⟩
  · rintro rfl
    rw [map_zero] at hw
    exact hθ0 ((pow_eq_zero_iff hN.ne').mp hw.symm)
  · intro g hg
    obtain ⟨g', rfl⟩ := _root_.GlobalTheory.K4.TopSpec.exists_res hg
    apply _root_.GlobalTheory.NeedB.kum_eq_of hζ hθ0
    exact hθ g' (by rw [IntermediateField.fixingSubgroup_bot]; exact Subgroup.mem_top _)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EdgeClassEqKummerCharacterOfChosenRootFunctionFiStatement
open GlobalTheory.K4 GlobalTheory.KEdge GlobalTheory.NeedB Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.edgeClass_eq_kummerCharacter_of_chosen_root_function_field : ∀ (k K Ω F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Algebra (RatFunc k) K]
    [IsScalarTower k[X] (RatFunc k) K] [FiniteDimensional (RatFunc k) K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    [Field F] [Algebra F K] [Algebra F Ω] [IsScalarTower F K Ω] [Normal F K]
    (N : ℕ) (ζ : Ω), 0 < N → IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[F] Ω, g ζ = ζ) →
  (∀ τ : K ≃ₐ[F] K, ∀ x ∈ FunctionField.ringOfIntegers k K, τ x ∈ FunctionField.ringOfIntegers k K) →
  ∀ (a b : F) (α β : Ω), a ≠ 0 → b ≠ 0 → algebraMap F K a ∈ FunctionField.ringOfIntegers k K → (algebraMap F K a)⁻¹ ∈ FunctionField.ringOfIntegers k K →
    algebraMap F K b ∈ FunctionField.ringOfIntegers k K → (algebraMap F K b)⁻¹ ∈ FunctionField.ringOfIntegers k K →
    α ^ N = algebraMap F Ω a → β ^ N = algebraMap F Ω b →
  ∀ (x y : (Ω ≃ₐ[F] Ω) →* Multiplicative (ZMod N)), (∀ g, (x g).toAdd = kum (N := N) ζ α g) → (∀ g, (y g).toAdd = kum (N := N) ζ β g) →
  ∀ η : (Ω ≃ₐ[F] Ω) → ZMod N, CobOn (geo F K Ω) x y η →
    IsLocallyConstant (fun g : geo F K Ω => η g) →
    (∀ (B : ValuationSubring Ω) (g : Ω ≃ₐ[F] Ω), Over (FunctionField.ringOfIntegers k K).toSubring B →
      (∀ z, B.valuation z ≤ 1 → B.valuation (g z - z) < 1) → g ∈ geo F K Ω → η g = 0) →
  ∀ σ : Ω ≃ₐ[F] Ω, IsTopW (K := K) ζ x y η σ (topW (K := K) ζ x y η σ) := by
  first | exact @GlobalTheory.K4.isTopW_topW | exact GlobalTheory.K4.isTopW_topW | (intros; apply GlobalTheory.K4.isTopW_topW <;> assumption)
end
end
