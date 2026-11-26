module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaIntegrationFormulaUpToConstant
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RedMFrMapAdjZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralTsumOfFactor

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InclTprodUpdate
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.IoLift.FinTensor

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}

theorem inclK_injective (h : KSm M) : Function.Injective (inclK h) := by
  choose r hr using fun τ =>
    LinearMap.exists_leftInverse_of_injective (Submodule.inclusion (h τ))
      (LinearMap.ker_eq_bot.mpr (Submodule.inclusion_injective (h τ)))
  have key : PiTensorProduct.map r ∘ₗ inclK h = LinearMap.id := by
    unfold inclK
    rw [← PiTensorProduct.map_comp]
    simp only [hr, PiTensorProduct.map_id]
  intro x y hxy
  calc x = (PiTensorProduct.map r ∘ₗ inclK h) x := by rw [key, LinearMap.id_apply]
    _ = (PiTensorProduct.map r ∘ₗ inclK h) y := by rw [LinearMap.comp_apply, hxy, ← LinearMap.comp_apply]
    _ = y := by rw [key, LinearMap.id_apply]

theorem incl_tprod (h : KSm M) (v : ∀ ρ, kFin M ρ) :
    inclT M (inclK h (PiTensorProduct.tprod ℂ v)) = PiTensorProduct.tprod ℂ fun ρ => (v ρ : M.H ρ) := by
  simp [inclT, inclK]

theorem incl_tprod_update (h : KSm M) (v : ∀ ρ, kFin M ρ) (τ : D.what₂.Tau) (u : kFin M τ) :
    inclT M (inclK h (PiTensorProduct.tprod ℂ (Function.update v τ u))) =
      PiTensorProduct.tprod ℂ (Function.update (fun ρ => (v ρ : M.H ρ)) τ (u : M.H τ)) := by
  rw [incl_tprod]
  congr 1
  funext ρ
  rcases eq_or_ne ρ τ with rfl | hρ
  · simp
  · simp [Function.update_of_ne hρ]

theorem act_tprod (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (v : ∀ ρ, M.H ρ) :
    actT M τ g (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ (Function.update v τ (M.rep τ g (v τ))) := by
  simp only [actT, PiTensorProduct.map_tprod]
  congr 1
  funext ρ
  rcases eq_or_ne ρ τ with rfl | hρ
  · simp
  · simp [Function.update_of_ne hρ]

theorem ell_update (w v : ∀ ρ, M.H ρ) (τ : D.what₂.Tau) (u : M.H τ) :
    ellT M w (PiTensorProduct.tprod ℂ (Function.update v τ u)) =
      ⟪w τ, u⟫_ℂ * ∏ ρ ∈ Finset.univ.erase τ, ⟪w ρ, v ρ⟫_ℂ := by
  have hs : ∀ ρ ∈ Finset.univ.erase τ, ⟪w ρ, Function.update v τ u ρ⟫_ℂ = ⟪w ρ, v ρ⟫_ℂ := fun ρ hρ => by
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hρ)]
  simp only [ellT, PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply]
  show ∏ ρ, ⟪w ρ, Function.update v τ u ρ⟫_ℂ = _
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ τ), Function.update_self]
  congr 1
  exact Finset.prod_congr rfl hs

private theorem hasDerivAt_ellT_actT_exp_tprod (h : KSm M) (τ : D.what₂.Tau)
    (a : Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (kFin M τ)) (ha : IsKAct M τ a)
    (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hX : X ∈ lieAt V τ) (w : ∀ ρ, M.H ρ) (v : ∀ ρ, kFin M ρ) :
    HasDerivAt (fun t : ℝ => ellT M w (actT M τ (NormedSpace.exp (t • X)) (inclT M (inclK h (PiTensorProduct.tprod ℂ v)))))
      (ellT M w (inclT M (inclK h (intersection_update_fsHerm_neg_one τ (a X) (PiTensorProduct.tprod ℂ v))))) 0 := by
  have hd := ha.der X hX (v τ)
  have hi : HasDerivAt (fun t : ℝ => ⟪w τ, M.rep τ (NormedSpace.exp (t • X)) (v τ : M.H τ)⟫_ℂ)
      ⟪w τ, (a X (v τ) : M.H τ)⟫_ℂ 0 := by
    have hc := ((innerSL ℂ (w τ)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
    simpa [Function.comp_def] using hc
  have e2 : ellT M w (inclT M (inclK h (intersection_update_fsHerm_neg_one τ (a X) (PiTensorProduct.tprod ℂ v)))) =
      ⟪w τ, (a X (v τ) : M.H τ)⟫_ℂ * ∏ ρ ∈ Finset.univ.erase τ, ⟪w ρ, (v ρ : M.H ρ)⟫_ℂ := by
    rw [position_tprod, incl_tprod_update, ell_update]
  have e1 : (fun t : ℝ => ellT M w (actT M τ (NormedSpace.exp (t • X)) (inclT M (inclK h (PiTensorProduct.tprod ℂ v))))) =
      fun t : ℝ => ⟪w τ, M.rep τ (NormedSpace.exp (t • X)) (v τ : M.H τ)⟫_ℂ *
        ∏ ρ ∈ Finset.univ.erase τ, ⟪w ρ, (v ρ : M.H ρ)⟫_ℂ := by
    funext t
    rw [incl_tprod, act_tprod, ell_update]
  rw [e1, e2]
  exact hi.mul_const _

theorem derT_mapFactor (h : KSm M) (τ : D.what₂.Tau) (a : Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (kFin M τ))
    (ha : IsKAct M τ a) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hX : X ∈ lieAt V τ) (x : KT M) :
    DerT M τ X (inclK h x) (inclK h (intersection_update_fsHerm_neg_one τ (a X) x)) := by
  delta DerT
  intro w
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    simp only [map_smul, smul_eq_mul]
    exact (hasDerivAt_ellT_actT_exp_tprod h τ a ha X hX w v).const_mul r
  | add x y hx hy =>
    simp only [map_add (f := _)]
    exact hx.add hy

theorem incl_mapFactor_kOp (h : KSm M) (τ : D.what₂.Tau) (k : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hk : k ∈ maxCpt M τ)
    (x : KT M) : inclT M (inclK h (intersection_update_fsHerm_neg_one τ (kOp M τ hk) x)) = actT M τ k (inclT M (inclK h x)) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    simp only [map_smul]
    congr 1
    rw [position_tprod, incl_tprod_update, incl_tprod, act_tprod] <;> rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem kFinTensor : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau) (h : KSm M), Function.Injective (inclK h) ∧ (∀ a : Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (kFin M τ), IsKAct M τ a → ∀ X ∈ lieAt V τ, ∀ x : KT M, DerT M τ X (inclK h x) (inclK h (intersection_update_fsHerm_neg_one τ (a X) x))) ∧ ∀ (k : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hk : k ∈ maxCpt M τ) (x : KT M), inclT M (inclK h (intersection_update_fsHerm_neg_one τ (kOp M τ hk) x)) = actT M τ k (inclT M (inclK h x)) := by
  intro D V S M τ h
  refine ⟨inclK_injective h, ?_, ?_⟩
  · intro a ha X hX x
    exact derT_mapFactor h τ a ha X hX x
  · intro k hk x
    exact incl_mapFactor_kOp h τ k hk x

end GlobalTheory.Chain.IoLift.FinTensor

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicMeasureModulus
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate

namespace GlobalTheory.ParabModulus

section General

open scoped Pointwise

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

noncomputable def prodMul (μM μN : Measure G) : Measure G := (μM.prod μN).map (fun z => z.1 * z.2)

theorem lintegral_prodMul (μM μN : Measure G) [SFinite μN] (f : G → ENNReal) (hf : Measurable f) :
    ∫⁻ x, f x ∂prodMul μM μN = ∫⁻ m, ∫⁻ u, f (m * u) ∂μN ∂μM := by
  rw [prodMul, lintegral_map hf measurable_mul]
  exact lintegral_prod (fun z : G × G => f (z.1 * z.2)) (hf.comp measurable_mul).aemeasurable

theorem measurable_inner (μN : Measure G) [SFinite μN] (f : G → ENNReal) (hf : Measurable f) :
    Measurable fun m => ∫⁻ u, f (m * u) ∂μN :=
  Measurable.lintegral_prod_right' (f := fun z : G × G => f (z.1 * z.2)) (hf.comp measurable_mul)

theorem prodMul_left_fst (M : Subgroup G) (μM μN : Measure G) [SFinite μN]
    (iM : ∀ s ∈ M, μM.map (fun g => s * g) = μM) (s : G) (hs : s ∈ M) :
    (prodMul μM μN).map (fun g => s * g) = prodMul μM μN := by
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [lintegral_map hf (measurable_const_mul s), lintegral_prodMul _ _ (fun x => f (s * x)) (hf.comp (measurable_const_mul s)),
    lintegral_prodMul _ _ _ hf]
  have := GlobalTheory.IwasawaShape.lintegral_mul_left_of_map (iM s hs) _ (measurable_inner μN f hf)
  simpa only [mul_assoc] using this

theorem prodMul_left_snd (M N : Subgroup G) (hnorm : ∀ m ∈ M, ∀ u ∈ N, m⁻¹ * u * m ∈ N)
    (μM μN : Measure G) [SFinite μN] (h1 : μM (M : Set G)ᶜ = 0)
    (iN : ∀ s ∈ N, μN.map (fun g => s * g) = μN) (s : G) (hs : s ∈ N) :
    (prodMul μM μN).map (fun g => s * g) = prodMul μM μN := by
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [lintegral_map hf (measurable_const_mul s), lintegral_prodMul _ _ (fun x => f (s * x)) (hf.comp (measurable_const_mul s)),
    lintegral_prodMul _ _ _ hf]
  have aM : ∀ᵐ m ∂μM, m ∈ M := mem_ae_iff.2 h1
  refine lintegral_congr_ae (aM.mono fun m hm => ?_)
  have := GlobalTheory.IwasawaShape.lintegral_mul_left_of_map (iN _ (hnorm m hm s hs)) (fun u => f (m * u))
    (hf.comp (measurable_const_mul m))
  show ∫⁻ u, f (s * (m * u)) ∂μN = ∫⁻ u, f (m * u) ∂μN
  rw [← this]
  refine lintegral_congr fun u => ?_
  rw [show m * (m⁻¹ * s * m * u) = s * (m * u) by group]

theorem prodMul_facts (M N P : Subgroup G) (hM : IsClosed (M : Set G)) (hN : IsClosed (N : Set G))
    (hPm : MeasurableSet (P : Set G)) (hMN : ∀ m ∈ M, m ∈ N → m = 1)
    (hMP : ∀ m ∈ M, ∀ u ∈ N, m * u ∈ P) (hdec : ∀ p ∈ P, ∃ m ∈ M, ∃ u ∈ N, p = m * u)
    (μM μN : Measure G) [SigmaFinite μN] [IsFiniteMeasureOnCompacts μM] [IsFiniteMeasureOnCompacts μN]
    (hM0 : μM ≠ 0) (hN0 : μN ≠ 0) (h1 : μM (M : Set G)ᶜ = 0) (h2 : μN (N : Set G)ᶜ = 0) :
    prodMul μM μN (P : Set G)ᶜ = 0 ∧ SigmaFinite (prodMul μM μN) ∧
      ∃ T : Set G, MeasurableSet T ∧ prodMul μM μN T ≠ 0 ∧ prodMul μM μN T ≠ ⊤ := by
  set ρ₀ := prodMul μM μN with hρ₀
  have aM : ∀ᵐ m ∂μM, m ∈ M := mem_ae_iff.2 h1
  have aN : ∀ᵐ u ∂μN, u ∈ N := mem_ae_iff.2 h2
  have hP0 : ρ₀ (P : Set G)ᶜ = 0 := by
    rw [← lintegral_indicator_one hPm.compl, hρ₀, lintegral_prodMul _ _ _ (measurable_one.indicator hPm.compl)]
    refine lintegral_eq_zero_of_ae_eq_zero ?_
    filter_upwards [aM] with m hm
    refine lintegral_eq_zero_of_ae_eq_zero ?_
    filter_upwards [aN] with u hu
    rw [Set.indicator_of_notMem (show m * u ∉ (P : Set G)ᶜ from fun h => h (hMP m hm u hu))]
    simp
  set Q : ℕ → Set G := fun i => (compactCovering G i ∩ M) * (compactCovering G i ∩ N) with hQ
  have hQc : ∀ i, IsCompact (Q i) := fun i =>
    ((isCompact_compactCovering G i).inter_right hM).mul ((isCompact_compactCovering G i).inter_right hN)
  have uniq : ∀ i, ∀ m ∈ M, ∀ u ∈ N, m * u ∈ Q i → m ∈ compactCovering G i ∧ u ∈ compactCovering G i := by
    rintro i m hm u hu ⟨m', ⟨hm'C, hm'M⟩, u', ⟨hu'C, hu'N⟩, e⟩
    have e : m' * u' = m * u := e
    have e' : m'⁻¹ * m = u' * u⁻¹ := by
      calc m'⁻¹ * m = m'⁻¹ * (m * u) * u⁻¹ := by group
        _ = m'⁻¹ * (m' * u') * u⁻¹ := by rw [e]
        _ = u' * u⁻¹ := by group
    have h := hMN _ (M.mul_mem (M.inv_mem hm'M) hm) (by rw [e']; exact N.mul_mem hu'N (N.inv_mem hu))
    have hm' : m = m' := (inv_mul_eq_one.1 h).symm
    rw [h] at e'
    have hu' : u = u' := (mul_inv_eq_one.1 e'.symm).symm
    exact ⟨hm' ▸ hm'C, hu' ▸ hu'C⟩
  have hQ1 : ∀ i, ρ₀ (Q i) < ⊤ := by
    intro i
    have hC := isCompact_compactCovering G i
    rw [← lintegral_indicator_one (hQc i).measurableSet, hρ₀,
      lintegral_prodMul _ _ _ (measurable_one.indicator (hQc i).measurableSet)]
    calc _ ≤ ∫⁻ m, (compactCovering G i).indicator (fun _ => μN (compactCovering G i)) m ∂μM := by
          refine lintegral_mono_ae ?_
          filter_upwards [aM] with m hm
          by_cases hmC : m ∈ compactCovering G i
          · rw [Set.indicator_of_mem hmC, ← lintegral_indicator_one hC.measurableSet]
            refine lintegral_mono_ae ?_
            filter_upwards [aN] with u hu
            by_cases hq : m * u ∈ Q i
            · simp [Set.indicator_of_mem hq, Set.indicator_of_mem (uniq i m hm u hu hq).2]
            · simp [Set.indicator_of_notMem hq]
          · rw [Set.indicator_of_notMem hmC]
            refine (lintegral_eq_zero_of_ae_eq_zero ?_).le
            filter_upwards [aN] with u hu
            rw [Set.indicator_of_notMem (fun h => hmC (uniq i m hm u hu h).1)]
            simp
      _ < ⊤ := by
          rw [lintegral_indicator_const hC.measurableSet]
          exact ENNReal.mul_lt_top hC.measure_lt_top hC.measure_lt_top
  have hS : ⋃ i, (Q i ∪ (P : Set G)ᶜ) = Set.univ := by
    refine Set.eq_univ_of_forall fun g => Set.mem_iUnion.2 ?_
    by_cases hg : g ∈ P
    · obtain ⟨m, hm, u, hu, rfl⟩ := hdec g hg
      obtain ⟨i, hi⟩ := exists_mem_compactCovering m
      obtain ⟨k, hk⟩ := exists_mem_compactCovering u
      exact ⟨max i k, Or.inl (Set.mul_mem_mul ⟨compactCovering_subset G (le_max_left _ _) hi, hm⟩
        ⟨compactCovering_subset G (le_max_right _ _) hk, hu⟩)⟩
    · exact ⟨0, Or.inr hg⟩
  have hS1 : ∀ i, ρ₀ (Q i ∪ (P : Set G)ᶜ) < ⊤ := fun i =>
    lt_of_le_of_lt (measure_union_le _ _) (by rw [hP0, add_zero]; exact hQ1 i)
  have sf : SigmaFinite ρ₀ := ⟨⟨⟨fun i => Q i ∪ (P : Set G)ᶜ, fun _ => trivial, hS1, hS⟩⟩⟩
  have huniv : ρ₀ Set.univ ≠ 0 := by
    rw [hρ₀, prodMul, Measure.map_apply measurable_mul MeasurableSet.univ, Set.preimage_univ,
      ← Set.univ_prod_univ, Measure.prod_prod]
    exact mul_ne_zero (fun h => hM0 (Measure.measure_univ_eq_zero.1 h))
      (fun h => hN0 (Measure.measure_univ_eq_zero.1 h))
  obtain ⟨i, hi⟩ : ∃ i, ρ₀ (Q i ∪ (P : Set G)ᶜ) ≠ 0 := by
    by_contra h
    push_neg at h
    exact huniv (by rw [← hS]; exact measure_iUnion_null h)
  refine ⟨hP0, sf, Q i, (hQc i).measurableSet, fun h => hi ?_, (hQ1 i).ne⟩
  exact measure_union_null h hP0

theorem eq_smul_of_left_inv (P : Subgroup G) (hPm : MeasurableSet (P : Set G)) (ρ ρ₀ : Measure G)
    [SigmaFinite ρ] [SigmaFinite ρ₀] (h0 : ρ (P : Set G)ᶜ = 0) (h0' : ρ₀ (P : Set G)ᶜ = 0)
    (hi : ∀ s ∈ P, ρ.map (fun g => s * g) = ρ) (hi' : ∀ s ∈ P, ρ₀.map (fun g => s * g) = ρ₀)
    (T : Set G) (hT : MeasurableSet T) (hT0 : ρ₀ T ≠ 0) (hT1 : ρ₀ T ≠ ⊤) :
    ∃ c : ENNReal, ρ = c • ρ₀ := by
  have hemb : MeasurableEmbedding (Subtype.val : P → G) := MeasurableEmbedding.subtype_coe hPm
  haveI : MeasurableMul₂ P := ⟨Measurable.subtype_mk
    ((hemb.measurable.comp measurable_fst).mul (hemb.measurable.comp measurable_snd))⟩
  haveI : MeasurableInv P := ⟨Measurable.subtype_mk hemb.measurable.inv⟩
  have hmap : ∀ τ : Measure G, τ (P : Set G)ᶜ = 0 → (τ.comap Subtype.val).map (Subtype.val : P → G) = τ := by
    intro τ h
    rw [hemb.map_comap, Subtype.range_coe]
    exact Measure.restrict_eq_self_of_ae_mem h
  have hinv : ∀ τ : Measure G, τ (P : Set G)ᶜ = 0 → (∀ s ∈ P, τ.map (fun g => s * g) = τ) →
      (τ.comap (Subtype.val : P → G)).IsMulLeftInvariant := by
    intro τ h hτ
    refine ⟨fun s => ?_⟩
    rw [← hemb.comap_map ((τ.comap Subtype.val).map (fun g => s * g)),
      Measure.map_map hemb.measurable (measurable_const_mul s)]
    have : (Subtype.val : P → G) ∘ (fun g => s * g) = (fun g => (s : G) * g) ∘ Subtype.val := rfl
    rw [this, ← Measure.map_map (measurable_const_mul _) hemb.measurable, hmap τ h, hτ s s.2]
  haveI := hinv ρ h0 hi
  haveI := hinv ρ₀ h0' hi'
  haveI : SigmaFinite (ρ.comap (Subtype.val : P → G)) :=
    SigmaFinite.of_map _ hemb.measurable.aemeasurable (by rw [hmap ρ h0]; infer_instance)
  haveI : SigmaFinite (ρ₀.comap (Subtype.val : P → G)) :=
    SigmaFinite.of_map _ hemb.measurable.aemeasurable (by rw [hmap ρ₀ h0']; infer_instance)
  have hT' : ρ₀.comap (Subtype.val : P → G) (Subtype.val ⁻¹' T) = ρ₀ T := by
    rw [← hmap ρ₀ h0', Measure.map_apply hemb.measurable hT, hmap ρ₀ h0']
  set c : ENNReal := ρ.comap (Subtype.val : P → G) (Subtype.val ⁻¹' T) /
    ρ₀.comap (Subtype.val : P → G) (Subtype.val ⁻¹' T) with hc
  have key : ρ.comap (Subtype.val : P → G) = c • ρ₀.comap (Subtype.val : P → G) :=
    measure_eq_div_smul (ρ.comap (Subtype.val : P → G)) (ρ₀.comap (Subtype.val : P → G))
      (s := Subtype.val ⁻¹' T) (by rw [hT']; exact hT0) (by rw [hT']; exact hT1)
  refine ⟨c, ?_⟩
  conv_lhs => rw [← hmap ρ h0, key]
  rw [Measure.map_smul, hmap ρ₀ h0']
  exact hemb.measurable.aemeasurable

end General

end GlobalTheory.ParabModulus
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralFundamentalDomainEqIteratedDecomp
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralFundamentalDomainEqIteratedDecomp
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix

open scoped Pointwise

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoordUnfold

theorem isAddFundamentalDomain_prod {A B : Type} [AddGroup A] [AddGroup B] [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} [SFinite μ] [SigmaFinite ν]
    {Γ : AddSubgroup A} {Δ : AddSubgroup B} {s : Set A} {t : Set B}
    (hs : IsAddFundamentalDomain Γ s μ) (ht : IsAddFundamentalDomain Δ t ν) :
    IsAddFundamentalDomain (Γ.prod Δ) (s ×ˢ t) (μ.prod ν) := by
  refine ⟨hs.nullMeasurableSet.prod ht.nullMeasurableSet, ?_, ?_⟩
  · have h1 : ∀ᵐ p ∂(μ.prod ν), ∃ g : Γ, g +ᵥ p.1 ∈ s :=
      Measure.quasiMeasurePreserving_fst.ae hs.ae_covers
    have h2 : ∀ᵐ p ∂(μ.prod ν), ∃ d : Δ, d +ᵥ p.2 ∈ t :=
      Measure.quasiMeasurePreserving_snd.ae ht.ae_covers
    filter_upwards [h1, h2] with p hg hd
    obtain ⟨g, hg⟩ := hg
    obtain ⟨d, hd⟩ := hd
    exact ⟨⟨((g : A), (d : B)), g.2, d.2⟩, hg, hd⟩
  · rintro ⟨⟨g, d⟩, hg, hd⟩ ⟨⟨g', d'⟩, hg', hd'⟩ hne
    have key : ((⟨(g, d), hg, hd⟩ : Γ.prod Δ) +ᵥ s ×ˢ t) ∩ ((⟨(g', d'), hg', hd'⟩ : Γ.prod Δ) +ᵥ s ×ˢ t) =
        (((⟨g, hg⟩ : Γ) +ᵥ s) ∩ ((⟨g', hg'⟩ : Γ) +ᵥ s)) ×ˢ (((⟨d, hd⟩ : Δ) +ᵥ t) ∩ ((⟨d', hd'⟩ : Δ) +ᵥ t)) := by
      ext ⟨x, y⟩
      simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_vadd_set_iff_neg_vadd_mem]
      exact ⟨fun ⟨⟨a1, a2⟩, a3, a4⟩ => ⟨⟨a1, a3⟩, a2, a4⟩, fun ⟨⟨a1, a3⟩, a2, a4⟩ => ⟨⟨a1, a2⟩, a3, a4⟩⟩
    show (μ.prod ν) (_ ∩ _) = 0
    rw [key, Measure.prod_prod]
    by_cases h : g = g'
    · subst h
      have hdd : (⟨d, hd⟩ : Δ) ≠ ⟨d', hd'⟩ := fun e => hne (by
        have := congrArg Subtype.val e
        simp only at this
        subst this; rfl)
      have := ht.aedisjoint hdd
      rw [show ν _ = 0 from this, mul_zero]
    · have hgg : (⟨g, hg⟩ : Γ) ≠ ⟨g', hg'⟩ := fun e => h (congrArg Subtype.val e)
      have := hs.aedisjoint hgg
      rw [show μ _ = 0 from this, zero_mul]


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem integral_fundamentalDomain_eq_iterated : ∀ (D : D7) (V W : HSp D) (a b k : ℕ) (f₁ f₃ : Mx D a b → WO V W) (f₂ : Mx D 1 k → WO V W), Continuous f₁ → Continuous f₂ → Continuous f₃ → (∀ s s', f₁ (s + s') = f₁ s + f₁ s') → (∀ z z', f₂ (z + z') = f₂ z + f₂ z') → (∀ y y', f₃ (y + y') = f₃ y + f₃ y') → (∀ x : WO V W, ∃ s z y, x = f₁ s + f₂ z + f₃ y) → (∀ s z y, f₁ s + f₂ z + f₃ y = 0 → s = 0 ∧ z = 0 ∧ y = 0) → (∀ s z y, f₁ s + f₂ z + f₃ y ∈ ratL W V ↔ s ∈ GlobalTheory.MixModel.ratMx D a b ∧ z ∈ GlobalTheory.MixModel.ratMx D 1 k ∧ y ∈ GlobalTheory.MixModel.ratMx D a b) → ∀ (μ : Measure (Mx D a b)) (𝓨 : Set (Mx D a b)), IsCovolOne (GlobalTheory.MixModel.ratMx D a b) μ 𝓨 → ∀ (η : Measure (Mx D 1 k)) (𝓩 : Set (Mx D 1 k)), η.IsAddHaarMeasure → IsAddFundamentalDomain (GlobalTheory.MixModel.ratMx D 1 k) 𝓩 η → ∀ (ν : Measure (WO V W)) (𝓕 : Set (WO V W)), ν.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 ν → ∃ κ : ℝ, 0 < κ ∧ ∀ T : WO V W → ℂ, Continuous T → (∀ γ ∈ ratL W V, ∀ u, T (γ + u) = T u) → ∫ u in 𝓕, T u ∂ν = κ * ∫ s in 𝓨, (∫ z in 𝓩, (∫ y in 𝓨, T (f₁ s + f₂ z + f₃ y) ∂μ) ∂η) ∂μ := by
  intro D V W a b k f₁ f₃ f₂ hc₁ hc₂ hc₃ ha₁ ha₂ ha₃ hsurj hinj hrat μ 𝓨 hμ η 𝓩 hη h𝓩 ν 𝓕 hν h𝓕
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.MixModel.lattice_Mx D a b
  obtain ⟨j1, j2, j3, j4, j5, KZ, hKZ, hKZc⟩ := GlobalTheory.MixModel.lattice_Mx D 1 k
  obtain ⟨l1, l2, l3, l4, l5, K, hK, hKc⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank V.rank
  haveI : BorelSpace (Mx D a b) := ⟨rfl⟩
  haveI : BorelSpace (Mx D 1 k) := ⟨rfl⟩
  haveI : BorelSpace (WO V W) := ⟨rfl⟩
  haveI : Countable (GlobalTheory.MixModel.ratMx D a b) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI : Countable (GlobalTheory.MixModel.ratMx D 1 k) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI : IsTopologicalAddGroup (WO V W) := l1
  haveI : LocallyCompactSpace (WO V W) := l2
  haveI : SecondCountableTopology (WO V W) := l3
  haveI : T2Space (WO V W) := l4
  haveI : BaireSpace (WO V W) := BaireSpace.of_t2Space_locallyCompactSpace
  haveI : Countable (ratL W V) := by
    have : Countable (GlobalTheory.MixModel.ratMx D W.rank V.rank) :=
      TopologicalSpace.separableSpace_iff_countable.1 inferInstance
    exact this
  haveI := hμ.1

  have hZfin : η 𝓩 < ⊤ := by
    have hcov : 𝓩 ⊆ ⋃ γ : GlobalTheory.MixModel.ratMx D 1 k, ((γ +ᵥ KZ) ∩ 𝓩) := by
      intro x hx
      obtain ⟨γ, hγ, hγx⟩ := hKZc x
      refine Set.mem_iUnion.2 ⟨⟨-γ, neg_mem hγ⟩, Set.mem_vadd_set.2 ⟨γ + x, hγx, ?_⟩, hx⟩
      show -γ + (γ + x) = x
      abel
    calc η 𝓩 ≤ ∑' γ : GlobalTheory.MixModel.ratMx D 1 k, η ((γ +ᵥ KZ) ∩ 𝓩) :=
          (measure_mono hcov).trans (measure_iUnion_le _)
      _ = η KZ := (h𝓩.measure_eq_tsum KZ).symm
      _ < ⊤ := hKZ.measure_lt_top
  haveI : IsFiniteMeasure (μ.restrict 𝓨) := ⟨by rw [Measure.restrict_apply_univ, hμ.2.2]; exact ENNReal.one_lt_top⟩
  haveI : IsFiniteMeasure (η.restrict 𝓩) := ⟨by rw [Measure.restrict_apply_univ]; exact hZfin⟩

  let Ehom : (Mx D a b × (Mx D 1 k × Mx D a b)) →+ WO V W :=
    AddMonoidHom.mk' (fun p => f₁ p.1 + f₂ p.2.1 + f₃ p.2.2) (fun p q => by
      simp only [Prod.fst_add, Prod.snd_add, ha₁, ha₂, ha₃]; abel)
  have hEc : Continuous Ehom :=
    ((hc₁.comp continuous_fst).add (hc₂.comp (continuous_fst.comp continuous_snd))).add
      (hc₃.comp (continuous_snd.comp continuous_snd))
  have hEi : Function.Injective Ehom := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    rintro ⟨s, z, y⟩ h
    obtain ⟨h1, h2, h3⟩ := hinj s z y h
    simp [h1, h2, h3]
  have hEs : Function.Surjective Ehom := fun x => by
    obtain ⟨s, z, y, rfl⟩ := hsurj x
    exact ⟨(s, z, y), rfl⟩
  have hEo : IsOpenMap Ehom := AddMonoidHom.isOpenMap_of_sigmaCompact Ehom hEs hEc
  let Eq : (Mx D a b × (Mx D 1 k × Mx D a b)) ≃+ WO V W := AddEquiv.ofBijective Ehom ⟨hEi, hEs⟩
  let H : (Mx D a b × (Mx D 1 k × Mx D a b)) ≃ₜ WO V W := Eq.toEquiv.toHomeomorphOfContinuousOpen hEc hEo
  let Ec : (Mx D a b × (Mx D 1 k × Mx D a b)) ≃ₜ+ WO V W :=
    { Eq with continuous_toFun := hEc, continuous_invFun := H.symm.continuous }
  have hEapp : ∀ s z y, Ec (s, z, y) = f₁ s + f₂ z + f₃ y := fun _ _ _ => rfl
  let Me : (Mx D a b × (Mx D 1 k × Mx D a b)) ≃ᵐ WO V W := H.toMeasurableEquiv
  have hMe : ∀ p, Me p = Ec p := fun _ => rfl

  set lam : Measure (Mx D a b × (Mx D 1 k × Mx D a b)) := μ.prod (η.prod μ) with hlam
  haveI : lam.IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  set m : Measure (WO V W) := lam.map Me with hm
  haveI : m.IsAddHaarMeasure := Ec.isAddHaarMeasure_map lam
  have hνm := Measure.isAddLeftInvariant_eq_smul ν m
  set c := Measure.addHaarScalarFactor ν m with hcdef
  have hc : 0 < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure ν m
  have hcne : (c : ENNReal) ≠ 0 := by exact_mod_cast hc.ne'

  set Γ : AddSubgroup (Mx D a b × (Mx D 1 k × Mx D a b)) :=
    (GlobalTheory.MixModel.ratMx D a b).prod ((GlobalTheory.MixModel.ratMx D 1 k).prod (GlobalTheory.MixModel.ratMx D a b)) with hΓ
  have hmemΓ : ∀ p, p ∈ Γ ↔ Ec p ∈ ratL W V := by
    rintro ⟨s, z, y⟩
    rw [hEapp, hrat]
    simp [Γ, AddSubgroup.mem_prod]
  have hFDP : IsAddFundamentalDomain Γ (𝓨 ×ˢ (𝓩 ×ˢ 𝓨)) lam :=
    isAddFundamentalDomain_prod hμ.2.1 (isAddFundamentalDomain_prod h𝓩 hμ.2.1)
  have hac : lam.map Me ≪ ν := by
    intro s hs
    rw [hνm, Measure.smul_apply] at hs
    exact (smul_eq_zero.1 hs).resolve_left hc.ne'
  have hqmp : QuasiMeasurePreserving Me lam ν := ⟨Me.measurable.aemeasurable, hac⟩
  let eΓ : ratL W V → Γ := fun g => ⟨Ec.symm g, (hmemΓ _).2 (by simpa using g.2)⟩
  have heΓ : Function.Bijective eΓ := by
    refine ⟨fun g g' h => Subtype.ext ?_, fun p => ⟨⟨Ec p, (hmemΓ p).1 p.2⟩, Subtype.ext ?_⟩⟩
    · have := congrArg (fun q : Γ => Ec q.1) h
      simpa [eΓ] using this
    · simp [eΓ]
  haveI : Countable Γ := heΓ.2.countable
  have hFDE : IsAddFundamentalDomain Γ (Me ⁻¹' 𝓕) lam :=
    h𝓕.preimage_of_equiv hqmp heΓ (fun g p => by
      show Me ((Ec.symm g : _) + p) = (g : WO V W) + Me p
      rw [hMe, hMe, map_add (f := _), Ec.apply_symm_apply])
  refine ⟨(c : ℝ), by exact_mod_cast hc, fun T hT hper => ?_⟩
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hT.continuousOn
  have hbd : ∀ x, ‖T x‖ ≤ C := fun x => by
    obtain ⟨γ, hγ, hx⟩ := hKc x
    rw [← hper γ hγ x]
    exact hC _ hx
  have hTE : Continuous fun p => T (Me p) := hT.comp Ec.continuous
  have e1 : ∫ u in 𝓕, T u ∂ν = (c : ℝ) • ∫ u in 𝓕, T u ∂m := by
    rw [hνm, Measure.restrict_smul, integral_smul_nnreal_measure, NNReal.smul_def]
  have e2 : ∫ u in 𝓕, T u ∂m = ∫ p in Me ⁻¹' 𝓕, T (Me p) ∂lam := setIntegral_map_equiv Me T 𝓕
  haveI : VAddInvariantMeasure Γ _ lam :=
    ⟨fun g _ hs => Measure.measure_preimage_of_map_eq_self (map_add_left_eq_self lam g.1)
      (measurable_const_vadd g).aemeasurable hs.nullMeasurableSet⟩
  have e3 : ∫ p in Me ⁻¹' 𝓕, T (Me p) ∂lam = ∫ p in 𝓨 ×ˢ (𝓩 ×ˢ 𝓨), T (Me p) ∂lam :=
    hFDE.setIntegral_eq hFDP (fun g p => by
      show T (Me ((g : _) + p)) = T (Me p)
      rw [hMe, hMe, map_add (f := _)]
      exact hper _ ((hmemΓ _).1 g.2) _)
  have e4 : lam.restrict (𝓨 ×ˢ (𝓩 ×ˢ 𝓨)) = (μ.restrict 𝓨).prod ((η.restrict 𝓩).prod (μ.restrict 𝓨)) := by
    rw [Measure.prod_restrict, Measure.prod_restrict]
  rw [e1, e2, e3, e4, integral_prod _ (Integrable.of_bound hTE.aestronglyMeasurable C (ae_of_all _ fun p => hbd _)),
    Complex.real_smul]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun s => ?_)
  have hs : Continuous fun q : Mx D 1 k × Mx D a b => T (Me (s, q)) := hTE.comp (Continuous.prodMk_right s)
  dsimp only
  rw [integral_prod _ (Integrable.of_bound hs.aestronglyMeasurable C (ae_of_all _ fun p => hbd _))]
  rfl

end GlobalTheory.CoordUnfold

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralFundamentalDomainEqIteratedDecompStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_fundamentalDomain_eq_iterated_decomp : ∀ (D : D7) (V W : HSp D) (a b k : ℕ) (f₁ f₃ : Mx D a b → WO V W) (f₂ : Mx D 1 k → WO V W), Continuous f₁ → Continuous f₂ → Continuous f₃ → (∀ s s', f₁ (s + s') = f₁ s + f₁ s') → (∀ z z', f₂ (z + z') = f₂ z + f₂ z') → (∀ y y', f₃ (y + y') = f₃ y + f₃ y') → (∀ x : WO V W, ∃ s z y, x = f₁ s + f₂ z + f₃ y) → (∀ s z y, f₁ s + f₂ z + f₃ y = 0 → s = 0 ∧ z = 0 ∧ y = 0) → (∀ s z y, f₁ s + f₂ z + f₃ y ∈ ratL W V ↔ s ∈ GlobalTheory.MixModel.ratMx D a b ∧ z ∈ GlobalTheory.MixModel.ratMx D 1 k ∧ y ∈ GlobalTheory.MixModel.ratMx D a b) → ∀ (μ : Measure (Mx D a b)) (𝓨 : Set (Mx D a b)), IsCovolOne (GlobalTheory.MixModel.ratMx D a b) μ 𝓨 → ∀ (η : Measure (Mx D 1 k)) (𝓩 : Set (Mx D 1 k)), η.IsAddHaarMeasure → IsAddFundamentalDomain (GlobalTheory.MixModel.ratMx D 1 k) 𝓩 η → ∀ (ν : Measure (WO V W)) (𝓕 : Set (WO V W)), ν.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 ν → ∃ κ : ℝ, 0 < κ ∧ ∀ T : WO V W → ℂ, Continuous T → (∀ γ ∈ ratL W V, ∀ u, T (γ + u) = T u) → ∫ u in 𝓕, T u ∂ν = κ * ∫ s in 𝓨, (∫ z in 𝓩, (∫ y in 𝓨, T (f₁ s + f₂ z + f₃ y) ∂μ) ∂η) ∂μ := by
  first | exact @GlobalTheory.CoordUnfold.integral_fundamentalDomain_eq_iterated | exact GlobalTheory.CoordUnfold.integral_fundamentalDomain_eq_iterated | (intros; apply GlobalTheory.CoordUnfold.integral_fundamentalDomain_eq_iterated <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PrimeToHostCore
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows

namespace GlobalTheory.LiftScalarL

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

section Base

open GlobalTheory.Survey.LevelVectorSizeBounds GlobalTheory.BaseScalar

theorem g_mem_core {F : Face D A} (h : GlobalTheory.Hk3.Core R F) {PP : Pl D.host.E} (hP : PP ∈ R.Pg) : ∃ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
  obtain ⟨k, hk⟩ := (h.lev.Pg PP).1 hP
  refine ⟨k, ?_⟩
  have h1 := R.C.P.pb_over k
  rw [← hk] at h1
  have h2 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) (D.host.g k : ℕ) ∈ PP.asIdeal := h1
  simpa using h2


open Classical in
theorem isConjChars_core {F : Face D A} (h : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T) :
    IsConjChars R i t (RingEquiv.refl ℂ) (R.toLevCh.mu t ((i : ℕ) + 1)) R.eta
      (fun PP => if PP ∈ R.Pg then (R.chi ((i : ℕ) + 1) PP)⁻¹ else R.xiR t PP) := by
  refine ⟨_, _, isGalConj_refl _ _, isGalConj_refl _ _, ⟨(h.thP.ωP i t).hecS, ?_⟩, h.lev.eta, ?_⟩
  · intro P e he k x hx
    have a := (h.lev.mu0 i).2 P e he k x hx
    have b := (h.lev.xi t).2 P e he k x hx
    show (((R.mu0 ((i : ℕ) + 1) x * R.xi t x : Circle)) : ℂ) = (((R.C.mu0 i).locK P k * (R.xiH t).locK P k : ℂˣ) : ℂ)
    rw [Circle.coe_mul, a, b, Units.val_mul]
  · intro PP hPP a k u hk hu
    have ha : a ∉ PP.asIdeal := fun ha => u.ne_zero (hu.trans (Ideal.Quotient.eq_zero_iff_mem.2 ha))
    show _ = (R.C.mu0 i).locK PP k * (R.xiH t).locK PP k
    by_cases hg : PP ∈ R.Pg
    · obtain ⟨l, hl⟩ := g_mem_core R h hg
      have hun : (R.xiH t).UnrAt PP := by
        by_contra hn
        rcases (h.lev.Q_ram t PP).1 hn with hq | ⟨PP', hq, hc⟩
        · obtain ⟨⟨q, hq1, hq2, -, hq4⟩, -⟩ := h.lev.Q_pl t PP hq
          exact not_both (D.host.g_prime l) hq1 (hq4 l) hl (q_mem hq2)
        · obtain ⟨⟨q, hq1, hq2, -, hq4⟩, -⟩ := h.lev.Q_pl t PP' hq
          obtain ⟨c', hc1, hc2⟩ := hc _ (q_mem hq2)
          have : c' = (q : 𝓞 D.host.E) := by
            apply NumberField.RingOfIntegers.coe_injective
            rw [map_natCast]
            have h3 : (c' : D.host.E) = (q : D.host.E) := by simpa using hc2
            exact h3
          exact not_both (D.host.g_prime l) hq1 (hq4 l) hl (this ▸ hc1)
      simp only [if_pos hg]
      rw [locK_eq_one hun a k hk ha, mul_one]
      exact h.lev.chi i PP hg a k u hk hu
    · have hq : PP ∈ R.Q t := hPP.resolve_left hg
      obtain ⟨⟨q, hq1, hq2, -, hq4⟩, -⟩ := h.lev.Q_pl t PP hq
      have hun : (R.C.mu0 i).UnrAt PP := (R.C.isMu0 i).unr PP fun l hl =>
        not_both (D.host.g_prime l) hq1 (hq4 l) hl (q_mem hq2)
      simp only [if_neg hg]
      rw [locK_eq_one hun a k hk ha, one_mul]
      exact h.lev.xiR t PP hq a k u hk hu


open Classical in
theorem isLevelVec_core {F : Face D A} (h : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T) :
    IsLevelVec R.ψ R.θ (Vc D i) (Wc D i) (cart (R.MW i (sg0 D A))) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i) (R.datWp i R.triv) (R.Q t)
      (fun PP => if PP ∈ R.Pg then (R.chi ((i : ℕ) + 1) PP)⁻¹ else R.xiR t PP) (R.vacP i) (R.vP i t) := by
  have h1 := h.thP.vP i t
  unfold Datum.IsThPVecOf at h1
  unfold IsLevelVec
  have hQ : ∀ y : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP),
      Datum.omegaQ (R.Q t) (Wc D i).rank (fun PP => if PP ∈ R.Pg then (R.chi ((i : ℕ) + 1) PP)⁻¹ else R.xiR t PP) (-1) y =
        Datum.omegaQ (R.Q t) (Wc D i).rank (R.xiR t) (-1) y := by
    intro y
    unfold Datum.omegaQ
    split_ifs with hy
    · refine Finset.prod_congr rfl fun PP _ => ?_
      have hn : PP.1 ∉ R.Pg := fun hg => by
        obtain ⟨l, hl⟩ := g_mem_core R h hg
        obtain ⟨⟨q, hq1, hq2, -, hq4⟩, -⟩ := h.lev.Q_pl t PP.1 PP.2
        exact not_both (D.host.g_prime l) hq1 (hq4 l) hl (q_mem hq2)
      simp only [if_neg hn]
    · rfl
  simp only [omegaG_triv, hQ]
  exact h1


open Classical in
theorem chr_core {F : Face D A} (h : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T) :
    chrOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) R.triv
      (fun PP => if PP ∈ R.Pg then (R.chi ((i : ℕ) + 1) PP)⁻¹ else R.xiR t PP)) = (levEnv _ (R.βV i) (R.datVt i t)).χ := by
  ext1 x
  refine levFn_congr (R.βV i) D.R.r (r_le_V i) D.R.t 1 R.Pg (R.Q t) R.triv
    (fun _ PP => if PP ∈ R.Pg then (R.chi ((i : ℕ) + 1) PP)⁻¹ else R.xiR t PP) (fun _ PP => (R.chi ((i : ℕ) + 1) PP)⁻¹)
    (fun PP => if PP ∈ R.Pg then (R.chi ((i : ℕ) + 1) PP)⁻¹ else R.xiR t PP) (R.xiR t) ?_ ?_ _
  · intro c PP hP
    simp only [if_pos hP]
  · intro PP hP
    have hn : PP ∉ R.Pg := fun hg => by
      obtain ⟨l, hl⟩ := g_mem_core R h hg
      obtain ⟨⟨q, hq1, hq2, -, hq4⟩, -⟩ := h.lev.Q_pl t PP hP
      exact not_both (D.host.g_prime l) hq1 (hq4 l) hl (q_mem hq2)
    simp only [if_neg hn]

theorem exists_lift_core {F : Face D A} (h : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T) :
    ∃ th : (R.HV i t).H →ₗ[ℂ] (R.HW i (sg0 D A)).H, ∀ x, (R.HW i (sg0 D A)).e (th x) = R.thF i t x :=
  exists_factor (R.HW i (sg0 D A)).e (R.thF i t) (R.Wall i (sg0 D A)) (h.models.HW i (sg0 D A)).1
    (h.models.HW i (sg0 D A)).2.1 (h.thP.thF_mem i t)

theorem isLift_core {F : Face D A} (h : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T)
    (th : (R.HV i t).H →ₗ[ℂ] (R.HW i (sg0 D A)).H) (hth : ∀ x, (R.HW i (sg0 D A)).e (th x) = R.thF i t x) :
    IsLift R i (sg0 D A) (R.ωP i t) (R.ptP i t) (R.cV i) (R.ioP i) (R.νV i t) (R.fdV i t) (R.HV i t) th := by
  refine (h.thP.thF i t).elim fun thP hP => ?_
  unfold IsLift
  intro x v g
  have a := integrableOn_of_isThetaLift hP.1 x (PiTensorProduct.tprod ℂ v) g
  have c := (congrFun (hP.2 x v) g).trans a.2
  refine ⟨a.1, ?_⟩
  rw [hth x]
  exact c

theorem primeToHost_core {F : Face D A} (h : GlobalTheory.Hk3.Core R F) (hc : D.host.ccK = ⊤) (t : T) : PrimeToHost R t := by
  intro PP hP
  rw [hc, Ideal.absNorm_top, mul_one]
  rcases hP with hP | hP
  · obtain ⟨k, hk⟩ := g_mem_core R h hP
    have h1 : Nat.Coprime (D.host.g k) (D.host.QS * D.host.q * D.host.d) := by
      rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, D.ntypes.g_cond k, Nat.gcd_one_left]
    have h2 : Nat.Coprime (D.host.g k) (D.host.QS * D.host.q * D.host.d) := h1
    intro h3
    obtain ⟨x, y, hxy⟩ : IsCoprime ((D.host.g k : ℕ) : 𝓞 D.host.E) ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) := h2.cast
    exact PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (hxy ▸ PP.asIdeal.add_mem (PP.asIdeal.mul_mem_left _ hk) (PP.asIdeal.mul_mem_left _ h3)))
  · intro h3
    refine (h.lev.Q_off t PP hP).1 ?_
    rw [Nat.cast_mul _ D.sp.T]
    exact PP.asIdeal.mul_mem_right _ h3


open Classical in
theorem isLiftDataC_base {F : Face D A} (h : GlobalTheory.Hk3.Core R F) (hc : D.host.ccK = ⊤) (i : Fin D.R.m) (t : T) :
    IsLiftDataC R F i t (sg0 D A) (RingEquiv.refl ℂ) R.triv (R.toLevCh.mu t ((i : ℕ) + 1)) R.eta
      (fun PP => if PP ∈ R.Pg then (R.chi ((i : ℕ) + 1) PP)⁻¹ else R.xiR t PP) (R.ωP i t) (onb (R.MW i (sg0 D A)))
      (R.vacP i) (R.vP i t) (R.cV i) (R.ioP i) := by
  have hσ : IsEmbOverK D (sg0 D A) (RingEquiv.refl ℂ) := by
    rw [show sg0 D A = D.what₂.embLL from sgAt_mk _ R.hv0]; exact isEmbOverK_base
  exact ⟨h, primeToHost_core R h hc t, hσ, isLocal_triv R, isConjChars_core R h i t, h.thP.ωP i t,
    fun ρ => GlobalTheory.IndefiniteRowSideFullHecke.LiftFormsMainTerm.isONBasis_onb _ ρ _ (h.models.order i ρ), isLevelVec_core R h i t, h.thP.pt_theta i t,
    h.models.cV i, by rw [delta_base R]; exact h.thP.ioP i t⟩

end Base

theorem adjoint_eH (hM : R.IsModels) (hX : ∀ χ ∈ A.X, IsAbsIrrChar χ) (i : Fin D.R.m) :
    LinearMap.adjoint (GlobalTheory.Hk3.eH R i) = GlobalTheory.Hk3.eH R i := by
  have hu : ∀ g x y, ⟪R.gW i (sg0 D A) g x, R.gW i (sg0 D A) g y⟫_ℂ = ⟪x, y⟫_ℂ := fun g x y =>
    LinearIsometry.inner_map_map ⟨R.gW i (sg0 D A) g, GlobalTheory.gW_norm_eq R hM.HW hM.gW hM.νW i _ g⟩ x y
  have hc : ∀ g, starRingEnd ℂ (RealDat.eC (A := A) (sg0 D A) g) = RealDat.eC (A := A) (sg0 D A) g⁻¹ := by
    intro g
    unfold RealDat.eC
    set_option synthInstance.maxHeartbeats 100000 in
      rw [coeff_idemOf, coeff_idemOf, map_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    have h1 := (hX χ hχ).map_inv (sg0 D A) 1
    have h2 := (hX χ hχ).map_inv (sg0 D A) g⁻¹
    rw [inv_one] at h1
    simp only [map_mul, map_div₀, map_natCast]
    rw [h2, ← h1]
  symm
  rw [LinearMap.eq_adjoint_iff]
  intro x y
  unfold GlobalTheory.Hk3.eH
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, sum_inner, inner_sum, inner_smul_left, inner_smul_right, hc]
  refine Finset.sum_nbij' (fun g => g⁻¹) (fun g => g⁻¹) (by simp) (by simp) (by simp) (by simp) fun g _ => ?_
  rw [← hu g⁻¹, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem e_eH (hM : R.IsModels) (i : Fin D.R.m) (x : (R.HW i (sg0 D A)).H) :
    (R.HW i _).e (GlobalTheory.Hk3.eH R i x) = postOn _ (R.eWf i (sg0 D A)) ((R.HW i _).e x) := by
  unfold GlobalTheory.Hk3.eH RealDat.eWf gaL
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, hM.gW i]
  ext v g
  simp [postOn]
  rfl

theorem Wcc_spec (hM : R.IsModels) {SF} (hSF : GlobalTheory.Hk3.IsSF R SF) (i : Fin D.R.m) (t : T) (c : Eig D) {x}
    (hx : x ∈ GlobalTheory.Hk3.Wcc R SF i c) : x ∈ typePart R i (sg0 D A) t R.triv c ∧ GlobalTheory.Hk3.eH R i x = x := by
  classical
  have h1 := (Submodule.mem_inf.1 (Submodule.mem_comap.1 hx)).1
  have h2 := (mem_partFull _ _ _ _ _ _ _).1 (Submodule.mem_inf.1 (Submodule.mem_comap.1 hx)).2
  constructor
  · refine Submodule.mem_comap.2 ((mem_partFull _ _ _ _ _ _ _).2 ⟨h2.1, fun P d Rp hR => h2.2 P d Rp ?_⟩)
    refine hR.elim fun e hR => hR.elim fun f hR => hR.elim fun ϖ hR => hR.elim fun α hR => ⟨e, f, ϖ, α, fun v hv => hR.1 v ?_, hR.2⟩
    obtain ⟨PP, hP, e⟩ := (hSF v).1 hv
    unfold finS
    exact Finset.mem_image.2 ⟨PP, by simp [hP], HeightOneSpectrum.ext e⟩
  · apply (hM.HW i _).1
    rw [e_eH R hM]
    exact MultilinearMap.ext ((mem_goodPart _ _ _ _ _ _).1 h1).2

theorem proj_scalar {X Y : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y] (th thG : X →ₗ[ℂ] Y) (e : Y →ₗ[ℂ] Y)
    (he : LinearMap.adjoint e = e) (h : ∀ x, thG x = e (th x)) {y : Y} (hy : e y = y) {l : ℂ}
    (hl : th (LinearMap.adjoint th y) = l • y) : thG (LinearMap.adjoint thG y) = l • y := by
  obtain rfl : thG = e ∘ₗ th := LinearMap.ext h
  rw [LinearMap.adjoint_comp, he, LinearMap.comp_apply, LinearMap.comp_apply, hy, hl, map_smul, hy]

theorem thG_eq {F : Face D A} (h : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T) (th : (R.HV i t).H →ₗ[ℂ] (R.HW i (sg0 D A)).H)
    (hth : ∀ x, (R.HW i (sg0 D A)).e (th x) = R.thF i t x) (y : (R.HV i t).H) : R.thG i t y = GlobalTheory.Hk3.eH R i (th y) :=
  (h.models.HW i _).1 ((h.thP.thG i t y).trans ((e_eH R h.models i (th y)).trans (congrArg _ (hth y))).symm)

theorem card_triv : Nat.card (R.triv).H = 1 := Subgroup.card_bot

theorem scalar_base {F : Face D A} (hS : SourceLevelLawC R F) (hI : InnerProductFormulaC R F) (hFo : FockCoefficientC R F)
    (hZ : FiniteZetaL R F) (hL : LevelIndexNormC R F) (hδ : RealLowestKTypeCoeffSquareIntegrable R) (h : GlobalTheory.Hk3.Core R F) (hc : D.host.ccK = ⊤) :
    ∃ a : Fin D.R.m → ℝ, (∀ i, 0 < a i) ∧ ∀ i t (th : (R.HV i t).H →ₗ[ℂ] (R.HW i (sg0 D A)).H),
      (∀ x, (R.HW i (sg0 D A)).e (th x) = R.thF i t x) → ∀ c, typePart R i (sg0 D A) t R.triv c ≠ ⊥ →
      ∃ z : ℝ, IsLval R i t c z ∧
        ∀ x ∈ typePart R i (sg0 D A) t R.triv c, th (LinearMap.adjoint th x) = ((a i * z : ℝ) : ℂ) • x := by
  refine (scalar_of_data R hS hI hFo hZ hL hδ h.models.vpos).elim fun a ha => ?_
  refine ⟨fun i => a i (sg0 D A) * Module.finrank ℂ (R.cV i).W * Nat.card (R.triv).H, fun i => ?_, fun i t th hth c hne => ?_⟩
  · haveI : Nontrivial (R.cV i).W := (h.models.cV i).2.2.2.1
    exact mul_pos (mul_pos (ha.1 i _) (by exact_mod_cast Module.finrank_pos)) (by rw [card_triv, Nat.cast_one]; exact one_pos)
  have key := ha.2 i t _ _ _ _ _ _ _ _ _ _ _ _ (isLiftDataC_base R h hc i t) (R.νV i t) (R.fdV i t) (h.models.νV i t) _
    (R.B.L i t).pres.y (R.B.L i t).pres.reps (R.HV i t) (by rw [chr_core R h]; exact h.models.HV i t) th
    (isLift_core R h i t th hth) c hne
  exact key.elim fun B hB => hB.elim fun z hz => ⟨z, ⟨B, hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1⟩, hz.2.2.2.2⟩

theorem aForm : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), SourceLevelLawC R F → InnerProductFormulaC R F → FockCoefficientC R F → FiniteZetaL R F → LevelIndexNormC R F → RealLowestKTypeCoeffSquareIntegrable R → Given R F → D.host.ccK = ⊤ → ∀ SF, GlobalTheory.Hk3.IsSF R SF → AForm R SF := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hS hI hFo hZ hL hδ hG hc SF hSF
  have h := hG.core
  refine (scalar_base R hS hI hFo hZ hL hδ h hc).elim fun a ha => ⟨a, ha.1, fun i t c hne => ?_⟩
  refine (exists_lift_core R h i t).elim fun th hth => ?_
  have hle : GlobalTheory.Hk3.Wcc R SF i c ≤ typePart R i (sg0 D A) t R.triv c := fun x hx => (Wcc_spec R h.models hSF i t c hx).1
  refine (ha.2 i t th hth c fun h0 => hne (le_bot_iff.1 (hle.trans h0.le))).elim fun z hz => ⟨z, hz.1, fun x hx => ?_⟩
  exact proj_scalar th _ _ (adjoint_eH R h.models hG.irr i) (thG_eq R h i t th hth) (Wcc_spec R h.models hSF i t c hx).2
    (hz.2 x (hle hx))

end GlobalTheory.LiftScalarL

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaModelsEqCoverDiscreteSeries
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaModelsEqCoverDiscreteSeries
open Formalism.BasicNotions

namespace GlobalTheory

theorem modelsAreCoverSeries_of_hypotheses :
    GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules →
      ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.ModelsAreCoverSeries D :=
  GlobalTheory.T.thetaModels_are_coverDiscreteSeries_of_harishChandra

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaModelsEqCoverDiscreteSeriesStatement
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaModels_eq_coverDiscreteSeries : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.ModelsAreCoverSeries D := by
  first | exact @GlobalTheory.modelsAreCoverSeries_of_hypotheses | exact GlobalTheory.modelsAreCoverSeries_of_hypotheses | (intros; apply GlobalTheory.modelsAreCoverSeries_of_hypotheses <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorIdeleAbsDetUnitaryAdelicEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorIdeleAbsDetUnitaryAdelicEqOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.UnitaryDetAbs

open GlobalTheory.MixModel

theorem absE_det_matHom (D : D7) (W : HSp D) (h : GA D W) :
    GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det (matHom W h)) = 1 := by
  have hM := GlobalTheory.MixModel.mt_unitary W h
  have hdet := congrArg Matrix.det hM
  rw [Matrix.det_mul, Matrix.det_mul] at hdet
  have hadj : (GlobalTheory.MixModel.adj (mt W h)).det = cA D (mt W h).det := by
    rw [GlobalTheory.MixModel.adj, Matrix.det_transpose, RingHom.map_det]; rfl
  have hG : IsUnit (GlobalTheory.MixModel.gA W).det := by
    have e : (GlobalTheory.MixModel.gA W).det = incA D W.gram.det := by
      rw [GlobalTheory.MixModel.gA, GlobalTheory.MixModel.rat, RingHom.map_det]; rfl
    rw [e]
    exact (GlobalTheory.MixModel.gram_isUnit_det W).map _
  rw [hadj] at hdet
  have key : cA D (mt W h).det * (mt W h).det = 1 := by
    have e2 : cA D (mt W h).det * (mt W h).det * (GlobalTheory.MixModel.gA W).det = 1 * (GlobalTheory.MixModel.gA W).det := by
      rw [one_mul]; nth_rewrite 2 [← hdet]; ring
    exact hG.mul_right_cancel e2
  have hu : GlobalTheory.Doubling.conjUnit D.sp.cm.sig (Matrix.GeneralLinearGroup.det (matHom W h)) *
      Matrix.GeneralLinearGroup.det (matHom W h) = 1 := by
    ext
    exact key
  have h2 := congrArg (GlobalTheory.Doubling.absE D.host.F D.host.E) hu
  rw [map_mul, GlobalTheory.Doubling.absE_conjUnit, map_one, ← sq] at h2
  exact (pow_eq_one_iff_of_nonneg (by positivity) two_ne_zero).1 h2

end GlobalTheory.UnitaryDetAbs
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorIdeleAbsDetUnitaryAdelicEqOneStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorIdeleAbs_det_unitaryAdelic_eq_one : ∀ (D : D7) (W : HSp D) (h : GA D W), GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det (matHom W h)) = 1 := by
  first | exact @GlobalTheory.UnitaryDetAbs.absE_det_matHom | exact GlobalTheory.UnitaryDetAbs.absE_det_matHom | (intros; apply GlobalTheory.UnitaryDetAbs.absE_det_matHom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionPeriodicNormFiniteSqIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionPeriodicNormFiniteSqIntegral
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaSqInt

theorem thetaO_norm_fin : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ F : WO S T → ℂ, IsThetaFunO ψ S T F → (∀ γ ∈ ratL T S, ∀ w, ‖F (γ + w)‖ = ‖F w‖) ∧ ∫⁻ x in 𝓕, ‖F x‖ₑ ^ 2 ∂μ ≠ ⊤ ∧ ∫ x in 𝓕, F x * starRingEnd ℂ (F x) ∂μ = (((∫⁻ x in 𝓕, ‖F x‖ₑ ^ 2 ∂μ).toReal : ℝ) : ℂ) := by
  intro D ψ hψ S T μ 𝓕 hC F hF
  haveI hB : BorelSpace (WO S T) := ⟨rfl⟩
  haveI hO : OpensMeasurableSpace (WO S T) := BorelSpace.opensMeasurable
  have hn : ∀ x, ‖ψ x‖ = 1 := hψ.1.2.1
  refine ⟨?_, ?_, ?_⟩
  · intro γ hγ w
    obtain ⟨ξ, rfl⟩ := hγ
    have hq := hF.quasi ξ w
    have e : ((incA D).toAddMonoidHom.mapMatrix ξ : WO S T) = ratW T S ξ := rfl
    rw [e, hq, norm_mul, hn, one_mul]
  · obtain ⟨M, hM⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ hF
    have hle : ∫⁻ x in 𝓕, ‖F x‖ₑ ^ 2 ∂μ ≤ ∫⁻ _x in 𝓕, ENNReal.ofReal M ^ 2 ∂μ := by
      refine lintegral_mono fun x => ?_
      gcongr
      rw [← ofReal_norm_eq_enorm]
      exact ENNReal.ofReal_le_ofReal (hM x)
    rw [setLIntegral_const, hC.2.2, mul_one] at hle
    exact ne_top_of_le_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hle
  · have h1 : ∀ x, F x * starRingEnd ℂ (F x) = (((‖F x‖ ^ 2 : ℝ)) : ℂ) := fun x => by
      rw [Complex.mul_conj']; push_cast; rfl
    simp_rw [h1]
    rw [integral_complex_ofReal]
    congr 1
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => sq_nonneg ‖F x‖)
      ((hF.cont.norm.pow 2).measurable.aestronglyMeasurable)]
    congr 1
    refine lintegral_congr fun x => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]

end GlobalTheory.ThetaSqInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionPeriodicNormFiniteSqIntegralStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFunction_periodicNorm_finite_sqIntegral : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ F : WO S T → ℂ, IsThetaFunO ψ S T F → (∀ γ ∈ ratL T S, ∀ w, ‖F (γ + w)‖ = ‖F w‖) ∧ ∫⁻ x in 𝓕, ‖F x‖ₑ ^ 2 ∂μ ≠ ⊤ ∧ ∫ x in 𝓕, F x * starRingEnd ℂ (F x) ∂μ = (((∫⁻ x in 𝓕, ‖F x‖ₑ ^ 2 ∂μ).toReal : ℝ) : ℂ) := by
  first | exact @GlobalTheory.ThetaSqInt.thetaO_norm_fin | exact GlobalTheory.ThetaSqInt.thetaO_norm_fin | (intros; apply GlobalTheory.ThetaSqInt.thetaO_norm_fin <;> assumption)
end
end
