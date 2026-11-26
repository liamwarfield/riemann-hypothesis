module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTransformDarbouxModelLinearInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
public import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormAvgTypeOtherPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteThetaLiftLocalVector
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspAlongOfPairLifts

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanOneParameterFamilyContinuous
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanOneParameterFamilyContinuous
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.ArchUniq MeasureTheory
open scoped SchwartzMap Classical
noncomputable section

namespace GlobalTheory.ArchFamilyCont

theorem continuous_family : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    M.IsWeil ψ χX χW om → ∀ γ ∈ Lines σ W, ∀ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
    (∀ t (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) ⇑f ⇑(T t f)) →
    (∀ (f : SInf F (Fin n × Fin d)) y, Continuous fun t => T t f y) ∧
    ∀ (μ : Measure (Fin n × Fin d → mixedEmbedding.mixedSpace F)), μ.IsAddHaarMeasure → ∀ f φ : SInf F (Fin n × Fin d),
      Continuous fun t => ∫ x, T t f x * starRingEnd ℂ (φ x) ∂μ := by
  intro F E _ _ _ _ _ σ n d X W M ψ χX χW om hW γ hγ T hT
  classical
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.ArchRest.exists_rest_arch (F := F) (Fin n × Fin d)
  have hc : IsContOn (adeleClass F) om := hW.2.2
  have hline : Continuous fun t : ℝ => ((1 : UA σ X.J), γ (Multiplicative.ofAdd t)) :=
    continuous_const.prodMk (hγ.1.comp continuous_ofAdd)
  have key : ∀ t (f : SInf F (Fin n × Fin d)),
      om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) ⇑f R) = tens (evI F) ⇑(T t f) R :=
    fun t f => hT t f R (hR f)
  have hRl : ∀ y : Fin n × Fin d → mixedEmbedding.mixedSpace F, R (liftV y) = R 0 := by
    intro y
    have hat : At (evI F) (liftV y) := by
      intro u hu
      have hu1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
      funext i
      show u * liftV y i = 0
      exact Prod.ext (show u.1 * _ = 0 by rw [hu1, zero_mul]) (show u.2 * 0 = 0 from mul_zero _)
    have := (hR 0).1 0 (liftV y) hat
    simpa using this
  have hev : ∀ y : Fin n × Fin d → mixedEmbedding.mixedSpace F, (fun i => evI F (liftV y i)) = y := by
    intro y; funext i
    show InfiniteAdeleRing.ringEquiv_mixedSpace F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i)) = y i
    exact RingEquiv.apply_symm_apply _ _
  have hfin : ∀ y : Fin n × Fin d → mixedEmbedding.mixedSpace F, (fun i => (liftV y i).2) = 0 := by
    intro y; funext i; rfl
  have htl : ∀ (f : SInf F (Fin n × Fin d)) y, tens (evI F) ⇑f R (liftV y) = f y * R 0 := by
    intro f y
    show f (fun i => evI F (liftV y i)) * R (liftV y) = _
    rw [hev, hRl]
  refine ⟨fun f y => ?_, fun μ hμ f φ => ?_⟩
  ·
    let l : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ := LinearMap.proj (R := ℂ) (φ := fun _ => ℂ) (liftV y)
    have hl : l ∈ (adeleClass F).adm (Fin n × Fin d) := by
      intro g _
      refine ⟨g 0 • ((BoundedContinuousFunction.evalCLM ℂ y).comp
        (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)), fun f' => ?_⟩
      show pureA F (⇑f') g (liftV y) = _
      simp only [pureA, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
        BoundedContinuousFunction.evalCLM_apply, SchwartzMap.toBoundedContinuousFunctionCLM_apply, smul_eq_mul]
      have e1 := hev y
      have e2 := hfin y
      simp only [evI] at e1
      rw [e1, e2, mul_comm]
    have h1 := hc l hl _ (hR f).2
    have h2 : Continuous fun t : ℝ => l (om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) ⇑f R)) := h1.comp hline
    have h3 : (fun t : ℝ => T t f y) = fun t => l (om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) ⇑f R)) / R 0 := by
      funext t
      rw [key]
      show _ = tens (evI F) ⇑(T t f) R (liftV y) / R 0
      rw [htl, mul_div_cancel_right₀ _ hR0]
    rw [h3]
    exact h2.div_const _
  ·
    haveI : BorelSpace (Fin n × Fin d → mixedEmbedding.mixedSpace F) := inferInstance
    haveI : μ.HasTemperateGrowth := MeasureTheory.Measure.IsAddHaarMeasure.instHasTemperateGrowth
    let Tφ : SInf F (Fin n × Fin d) →L[ℂ] ℂ :=
      (innerSL ℂ (φ.toLp 2 μ)).comp (SchwartzMap.toLpCLM ℂ ℂ 2 μ)
    have hTφ : ∀ g : SInf F (Fin n × Fin d), Tφ g = ∫ x, g x * starRingEnd ℂ (φ x) ∂μ := by
      intro g
      show inner ℂ (φ.toLp 2 μ) (g.toLp 2 μ) = _
      rw [MeasureTheory.L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [SchwartzMap.coeFn_toLp φ 2 μ, SchwartzMap.coeFn_toLp g 2 μ] with x hx1 hx2
      rw [hx1, hx2, RCLike.inner_apply, mul_comm]
    let cL : SInf F (Fin n × Fin d) →ₗ[ℂ] ((Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) :=
      { toFun := fun g => ⇑g, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have hinj : Function.Injective cL := fun a b h => DFunLike.coe_injective h
    let eq := LinearEquiv.ofInjective cL hinj
    obtain ⟨L, hL⟩ := LinearMap.exists_extend (Tφ.toLinearMap ∘ₗ eq.symm.toLinearMap)
    have hLc : ∀ g : SInf F (Fin n × Fin d), L ⇑g = Tφ g := by
      intro g
      have := LinearMap.congr_fun hL (eq g)
      simp at this
      exact this
    let l : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ := L ∘ₗ LinearMap.funLeft ℂ ℂ liftV
    have hl : l ∈ (adeleClass F).adm (Fin n × Fin d) := by
      intro g _
      refine ⟨g 0 • Tφ, fun f' => ?_⟩
      have e : (LinearMap.funLeft ℂ ℂ liftV (pureA F (⇑f') g) : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ)
          = ⇑(g 0 • f') := by
        funext x
        have e1 := hev x
        have e2 := hfin x
        simp only [evI] at e1
        simp only [LinearMap.funLeft_apply, Function.comp_apply, pureA, SchwartzMap.smul_apply, smul_eq_mul]
        rw [e1, e2, mul_comm]
      show L (LinearMap.funLeft ℂ ℂ liftV (pureA F (⇑f') g)) = _
      rw [e, hLc, map_smul]
      rfl
    have h1 := hc l hl _ (hR f).2
    have h2 : Continuous fun t : ℝ => l (om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) ⇑f R)) := h1.comp hline
    have h3 : (fun t : ℝ => ∫ x, T t f x * starRingEnd ℂ (φ x) ∂μ) =
        fun t => l (om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) ⇑f R)) / R 0 := by
      funext t
      rw [key]
      have e : (LinearMap.funLeft ℂ ℂ liftV (tens (evI F) ⇑(T t f) R) :
          (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) = ⇑(R 0 • T t f) := by
        funext x
        simp only [LinearMap.funLeft_apply, Function.comp_apply, SchwartzMap.smul_apply, smul_eq_mul]
        rw [htl, mul_comm]
      show _ = L (LinearMap.funLeft ℂ ℂ liftV (tens (evI F) ⇑(T t f) R)) / R 0
      rw [e, hLc, map_smul, smul_eq_mul, hTφ, mul_div_cancel_left₀ _ hR0]
    rw [h3]
    exact h2.div_const _

end GlobalTheory.ArchFamilyCont
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanOneParameterFamilyContinuousStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.ArchUniq MeasureTheory
open scoped SchwartzMap Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanOneParameterFamily_continuous : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    M.IsWeil ψ χX χW om → ∀ γ ∈ Lines σ W, ∀ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
    (∀ t (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) ⇑f ⇑(T t f)) →
    (∀ (f : SInf F (Fin n × Fin d)) y, Continuous fun t => T t f y) ∧
    ∀ (μ : Measure (Fin n × Fin d → mixedEmbedding.mixedSpace F)), μ.IsAddHaarMeasure → ∀ f φ : SInf F (Fin n × Fin d),
      Continuous fun t => ∫ x, T t f x * starRingEnd ℂ (φ x) ∂μ := by
  first | exact @GlobalTheory.ArchFamilyCont.continuous_family | exact GlobalTheory.ArchFamilyCont.continuous_family | (intros; apply GlobalTheory.ArchFamilyCont.continuous_family <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanPointPureTensorKeepsFiniteFactor
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanPointPureTensorKeepsFiniteFactor
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Filter Topology
open GlobalTheory.AdelicU
open scoped Classical

noncomputable section

namespace GlobalTheory.ArchPure

theorem acts_arch_of_weil {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n d : ℕ} {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d}
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (hW : M.IsWeil ψ χX χW om)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J) (hh : h ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ W (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F))
    (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) :
    ∃ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (om (1, h)) f f₁ := by
  have hS := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hW
  set T := om (1, h) with hTdef
  have hpres : ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), T Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d) :=
    fun Φ hΦ => hS.pres (1, h) Φ hΦ
  have hcomm := GlobalTheory.ArchLocality.comm_fin M ψ χX χW om hW h hh
  obtain ⟨r₀, hr₀1, hr₀⟩ := GlobalTheory.ArchLocality.ref_fun (F := F) (Fin n × Fin d)
  set Φ₀ := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F)
    (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) r₀ with hΦ₀
  have hm₀ : Φ₀ ∈ GlobalTheory.WeilM.schA F _ := (hr₀ f).2
  obtain ⟨f₁, hf₁⟩ := GlobalTheory.ArchLocality.res_arch (T Φ₀) (hpres Φ₀ hm₀)
  refine ⟨f₁, fun r hr => ?_⟩
  funext y
  set u : AF F := (0, 1) with hu
  have hu0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F u = 0 := GlobalTheory.ArchLocality.evI_fin
  have htr : ∀ Ψ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d),
      T (fun w => Ψ (w + u • (-y))) = fun w => T Ψ (w + u • (-y)) := by
    intro Ψ hΨ
    have e := hcomm u hu0 (-y) 0 Ψ hΨ
    have hs0 : ∀ G : (Fin n × Fin d → AF F) → ℂ,
        GlobalTheory.WeilM.schr ψ (u • (-y), u • (0 : Fin n × Fin d → AF F)) G = fun w => G (w + u • (-y)) := by
      intro G; funext w; simp [GlobalTheory.WeilM.schr]
    rw [hs0, hs0] at e
    exact e
  set Φ₁ := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F)
    (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) r with hΦ₁
  set Φ₂ : (Fin n × Fin d → AF F) → ℂ := r y • (fun w => Φ₀ (w + u • (-y))) with hΦ₂
  have hm₂ : Φ₂ ∈ GlobalTheory.WeilM.schA F _ :=
    Submodule.smul_mem _ _ (GlobalTheory.SchwartzTranslation.schA_add_const _ _ hm₀)
  have hz2 : ∀ z : Fin n × Fin d → AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) z → ∀ i, (z i).2 = 0 := by
    intro z hz i
    have := congrArg Prod.snd (congrFun (hz u hu0) i)
    change (u * z i).2 = (0 : AF F).2 at this
    have e : (u * z i).2 = (z i).2 := one_mul _
    rw [e] at this
    exact this
  have hvan : ∀ z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) z → (Φ₁ - Φ₂) (y + z) = 0 := by
    intro z hz
    have e1 : r (y + z) = r y := hr.1 y z hz
    have e2 : (fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F ((y + z + u • (-y)) i)) =
        fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F ((y + z) i) := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, GlobalTheory.ArchLocality.evI_add, GlobalTheory.ArchLocality.evI_mul,
        hu0, zero_mul, add_zero]
    have e3 : r₀ (y + z + u • (-y)) = 1 := by
      refine hr₀1 _ fun i => ?_
      change ((y i + z i) + u * -(y i)).2 = 0
      change (y i).2 + (z i).2 + 1 * -(y i).2 = 0
      rw [hz2 z hz i]
      ring
    simp only [Pi.sub_apply, hΦ₂, hΦ₁, hΦ₀, Pi.smul_apply, smul_eq_mul, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens]
    rw [e2, e3, e1]
    ring
  have h0 := GlobalTheory.ArchLocality.fibre ψ hψ T hcomm (Φ₁ - Φ₂) (sub_mem hr.2 hm₂) y hvan
  rw [map_sub, Pi.sub_apply, sub_eq_zero] at h0
  have hy0 : y + u • (-y) = fun i =>
      (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (y i)), 0) : AF F) := by
    funext i
    refine Prod.ext ?_ ?_
    · change (y i).1 + 0 * -(y i).1 = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
        (InfiniteAdeleRing.ringEquiv_mixedSpace F (y i).1)
      rw [RingEquiv.symm_apply_apply]
      ring
    · change (y i).2 + 1 * -(y i).2 = 0
      ring
  have h2 : T Φ₂ y = r y * f₁ (fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (y i)) := by
    rw [hΦ₂, map_smul, htr Φ₀ hm₀, Pi.smul_apply, smul_eq_mul, hy0, hf₁]
  rw [h0, h2]
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens]
  ring

theorem pure_arch : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsGood ψ → M.IsWeil ψ χX χW om →
    ∀ g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ Wd (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F), ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
      (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
    (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
    ∃ c : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
      om (1, g) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure c φ := by
  intro F E _ _ _ _ _ σ n d Y Wd M ψ χX χW om hψ hM hW g hg f φ hSB hvac
  obtain ⟨c, hc⟩ := acts_arch_of_weil M ψ χX χW om hψ hW g hg f
  refine ⟨c, ?_⟩
  have hstd : ∀ᶠ v in Filter.cofinite,
      φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
    (hvac.and hM.std).mono fun v h => h.1.trans h.2
  set r : (Fin n × Fin d → AF F) → ℂ :=
    fun x => ∏ᶠ v, φ v fun i => evFin F v (x i) with hr
  have hRest : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F)
      (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) r := by
    refine ⟨fun x z hz => ?_, GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd⟩
    have hz0 : ∀ v i, evFin F v (z i) = 0 := by
      intro v i
      set u : AF F := (0, 1) with hu
      have h1 := congrFun (hz u GlobalTheory.ArchLocality.evI_fin) i
      have h2 : evFin F v u = 1 := map_one (evFin F v)
      have h3 := congrArg (evFin F v) h1
      simp only [Pi.zero_apply, map_zero] at h3
      change evFin F v (u * z i) = 0 at h3
      rw [map_mul, h2, one_mul] at h3
      exact h3
    simp only [hr, Pi.add_apply, map_add (f := _), hz0, add_zero]
  exact hc r hRest

end GlobalTheory.ArchPure
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanPointPureTensorKeepsFiniteFactorStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Filter Topology
open GlobalTheory.AdelicU
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanPoint_pureTensor_keeps_finiteFactor : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsGood ψ → M.IsWeil ψ χX χW om →
    ∀ g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ Wd (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F), ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
      (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
    (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
    ∃ c : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
      om (1, g) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure c φ := by
  first | exact @GlobalTheory.ArchPure.pure_arch | exact GlobalTheory.ArchPure.pure_arch | (intros; apply GlobalTheory.ArchPure.pure_arch <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdelicUnitaryFactorFiniteSetOfPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdelicUnitaryFactorFiniteSetOfPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.PlaceCut

section Alg

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {ι : Type} [Fintype ι] [DecidableEq ι]


omit [DecidableEq ι] in
theorem glue_mul {e : R} (he : e * e = e) (a b c d : Matrix ι ι A) :
    (e • a + (1 - e) • b) * (e • c + (1 - e) • d) = e • (a * c) + (1 - e) • (b * d) := by
  have h1 : e * (1 - e) = 0 := by rw [mul_sub, he, mul_one, sub_self]
  have h2 : (1 - e) * e = 0 := by rw [mul_comm, h1]
  have h3 : (1 - e) * (1 - e) = 1 - e := by rw [mul_sub, h2, mul_one, sub_zero]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, he, h1, h2, h3,
    zero_smul, add_zero, zero_add]

omit [Fintype ι] [DecidableEq ι] in
theorem glue_self (e : R) (a : Matrix ι ι A) : e • a + (1 - e) • a = a := by
  rw [← add_smul, add_sub_cancel, one_smul]

theorem exists_glue (c : A →ₐ[R] A) (J : Matrix ι ι A) {e : R} (he : e * e = e) (g h : GlobalTheory.WeilM.UG c J) :
    ∃ p : GlobalTheory.WeilM.UG c J, (p.1.1 : Matrix ι ι A) = e • g.1.1 + (1 - e) • h.1.1 ∧
      ((p⁻¹).1.1 : Matrix ι ι A) = e • (g⁻¹).1.1 + (1 - e) • (h⁻¹).1.1 := by
  let q : GL ι A :=
    { val := e • g.1.1 + (1 - e) • h.1.1
      inv := e • g.1.2 + (1 - e) • h.1.2
      val_inv := by rw [glue_mul he, g.1.3, h.1.3, glue_self]
      inv_val := by rw [glue_mul he, g.1.4, h.1.4, glue_self] }
  have hq : q ∈ GlobalTheory.WeilM.UG c J := by
    have hg : (g.1.1)ᵀ * J * (g.1.1).map c = J := g.2
    have hh : (h.1.1)ᵀ * J * (h.1.1).map c = J := h.2
    show (e • g.1.1 + (1 - e) • h.1.1)ᵀ * J * (e • g.1.1 + (1 - e) • h.1.1).map c = J
    have m : (e • g.1.1 + (1 - e) • h.1.1).map c = e • (g.1.1).map c + (1 - e) • (h.1.1).map c := by
      ext i j
      simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, map_add (f := _), map_smul]
    rw [m, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul]
    have k := glue_mul he (g.1.1)ᵀ (h.1.1)ᵀ J J
    rw [glue_self] at k
    rw [k, glue_mul he, hg, hh, glue_self]
  exact ⟨⟨q, hq⟩, rfl, rfl⟩

end Alg

theorem exists_idem {F : Type} [Field F] [NumberField F] (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))) :
    ∃ e : AF F, e * e = e ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F e = 0 ∧ (∀ w ∈ S, GlobalTheory.AdelicU.evFin F w e = 1) ∧
      (∀ w ∉ S, GlobalTheory.AdelicU.evFin F w e = 0) ∧
      ∀ u : AF F, (∀ w ∈ S, GlobalTheory.AdelicU.evFin F w u = 0) → u * e = 0 := by
  classical
  let b : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F := ∑ v ∈ S, GlobalTheory.AdelicU.singleFin v 1
  have hb1 : ∀ w ∈ S, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w b = 1 := by
    intro w hw
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_eq_single_of_mem w hw, GlobalTheory.AdelicU.evalV_singleFin_self]
    intro v _ hv
    exact GlobalTheory.AdelicU.evalV_singleFin_ne hv.symm 1
  have hb0 : ∀ w ∉ S, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w b = 0 := by
    intro w hw
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_eq_zero fun v hv => GlobalTheory.AdelicU.evalV_singleFin_ne ?_ 1
    rintro rfl
    exact hw hv
  refine ⟨((0 : Ainf F), b), ?_, ?_, hb1, hb0, ?_⟩
  · refine Prod.ext (by change (0 : Ainf F) * 0 = 0; exact mul_zero _) ?_
    change b * b = b
    apply GlobalTheory.AdelicU.af_ext
    intro w
    rw [map_mul]
    by_cases hw : w ∈ S
    · rw [hb1 w hw, mul_one]
    · rw [hb0 w hw, mul_zero]
  · show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
    exact map_zero _
  · intro u hu
    refine Prod.ext (by change u.1 * 0 = 0; exact mul_zero _) ?_
    change u.2 * b = 0
    apply GlobalTheory.AdelicU.af_ext
    intro w
    rw [map_mul, map_zero]
    by_cases hw : w ∈ S
    · have : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w u.2 = 0 := hu w hw
      rw [this, zero_mul]
    · rw [hb0 w hw, mul_zero]

theorem exists_cut : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J) (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))),
    ∃ gS k : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J, g = gS * k ∧
      (∀ u : AF F, (∀ w ∈ S, GlobalTheory.AdelicU.evFin F w u = 0) → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat gS - 1) = 0) ∧
      (∀ w ∈ S, ∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = 0) ∧
      (∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u →
        u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g - 1)) ∧
      (∀ w ∉ S, ∀ z ∈ GlobalTheory.InertSph.latAt X w, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k *ᵥ z = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g *ᵥ z ∧
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k⁻¹ *ᵥ z = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g⁻¹ *ᵥ z) := by
  intro F E _ _ _ _ _ σ n X g S
  obtain ⟨e, he, heI, he1, he0, heu⟩ := exists_idem S
  obtain ⟨gS, hS, -⟩ := exists_glue (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) he g 1
  obtain ⟨k, hk, hk'⟩ := exists_glue (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) he 1 g
  have hS2 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat gS = e • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g + (1 - e) • 1 := hS
  have hk2 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k = e • 1 + (1 - e) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g := hk
  have hk3 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k⁻¹ = e • 1 + (1 - e) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g⁻¹ := by
    rw [inv_one] at hk'
    exact hk'
  have hoff : ∀ (u : AF F) (M : Matrix (Fin n) (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), u * e = 0 →
      u • (e • (1 : Matrix (Fin n) (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) + (1 - e) • M) = u • M := by
    intro u M hu
    rw [smul_add, smul_smul, smul_smul, mul_sub, hu, mul_one, sub_zero, zero_smul, zero_add]
  refine ⟨gS, k, ?_, ?_, ?_, ?_, ?_⟩
  · apply Subtype.ext
    apply Units.ext
    show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat gS * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k
    rw [hS2, hk2, glue_mul he, Matrix.mul_one, Matrix.one_mul, glue_self]
  · intro u hu
    rw [hS2, smul_sub, smul_add, smul_smul, smul_smul, mul_sub, heu u hu, mul_one, sub_zero, zero_smul, zero_add,
      sub_self]
  · intro w hw u hu
    have h1 : (1 - e) * u = 0 := hu (1 - e) (by rw [map_sub, map_one, he1 w hw, sub_self])
    have h2 : u * (1 - e) = 0 := by rw [mul_comm, h1]
    have h3 : u * e = u := by rw [mul_sub, mul_one, sub_eq_zero] at h2; exact h2.symm
    rw [hk2, smul_sub, smul_add, smul_smul, smul_smul, h2, h3, zero_smul, add_zero, sub_self]
  · intro u hu
    have h1 : e * u = 0 := hu e heI
    rw [hk2, smul_sub, smul_sub, hoff u _ (by rw [mul_comm, h1])]
  · intro w hw z hz
    have key : ∀ M : Matrix (Fin n) (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
        (e • (1 : Matrix (Fin n) (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) + (1 - e) • M) *ᵥ z = M *ᵥ z := by
      intro M
      induction hz using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨a, ha, -, y, -, rfl⟩ := hz
        have h1 : e * a = 0 := ha e (he0 w hw)
        rw [Matrix.mulVec_smul, Matrix.mulVec_smul, ← Matrix.smul_mulVec, ← Matrix.smul_mulVec,
          hoff a M (by rw [mul_comm, h1])]
      | zero => rw [Matrix.mulVec_zero, Matrix.mulVec_zero]
      | add x y _ _ hx hy => rw [Matrix.mulVec_add, Matrix.mulVec_add, hx, hy]
      | neg x _ hx => rw [Matrix.mulVec_neg, Matrix.mulVec_neg, hx]
    rw [hk2, hk3]
    exact ⟨key _, key _⟩

end GlobalTheory.PlaceCut
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdelicUnitaryFactorFiniteSetOfPlacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelicUnitary_factor_finiteSetOfPlaces : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J) (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))),
    ∃ gS k : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J, g = gS * k ∧
      (∀ u : AF F, (∀ w ∈ S, GlobalTheory.AdelicU.evFin F w u = 0) → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat gS - 1) = 0) ∧
      (∀ w ∈ S, ∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = 0) ∧
      (∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u →
        u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g - 1)) ∧
      (∀ w ∉ S, ∀ z ∈ GlobalTheory.InertSph.latAt X w, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k *ᵥ z = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g *ᵥ z ∧
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k⁻¹ *ᵥ z = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g⁻¹ *ᵥ z) := by
  first | exact @GlobalTheory.PlaceCut.exists_cut | exact GlobalTheory.PlaceCut.exists_cut | (intros; apply GlobalTheory.PlaceCut.exists_cut <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemLevelOfLevelDatumNeZeroTranslate
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemLevelOfLevelDatumNeZeroTranslate
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SuppLev

theorem supp_level : ∀ (D : D7) (S T : HSp D) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (LT : LevDat D.host.E ℂ T.rank) (Q : Finset (Pl D.host.E)) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Z : Finset (Pl D.host.E)) (e : AE D), IsSelfDualC T ΛT → IsFrame βT ΛT → T.rank ≤ S.rank → LT.Q = ∅ → IsIdemSum e Z → (∀ PP, PP ∈ Z ↔ PP ∈ LT.Pg ∨ PP ∈ Q) → ∀ g ∈ GfC T, ∀ x, levDatum S T βS βT LT Q m e x ≠ 0 → levDatum S T βS βT LT Q m e (actO S T 1 g x) ≠ 0 → ∃ k ∈ levG T βT LT, ∀ PP ∈ Z, projV T ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) g = projV T ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) k := by
  classical
  intro D S T ΛT βS βT LT Q m Z e hsd hfr hrk hQ hZe hZ g hg x hx hx'
  have hu' := GlobalTheory.T.frameMatrixAdjoint_jointAction S T βS βT g x
  obtain ⟨hh, hI, hU, a, ha1, ha2, ha3⟩ := GlobalTheory.T.levelFiniteThetaDatum_ne_zero_frameAdjoint_spec S T βS βT LT Q m e x hx
  obtain ⟨-, hI', hU', b, hb1, hb2, hb3⟩ := GlobalTheory.T.levelFiniteThetaDatum_ne_zero_frameAdjoint_spec S T βS βT LT Q m e _ hx'
  simp only [hu'] at hI' hU' hb1
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self hZe
  have hsupp := GlobalTheory.T.frameMatrixAdjoint_supported_of_conjHalf S T βS βT e x hee hh
  obtain ⟨h1, h2, hred⟩ := GlobalTheory.T.integral_idempotent_mul_of_unit_topBlock_reductions S.rank T.rank hrk Z e hZe _ _ hI hI' hsupp
    (fun PP hP => hU PP ((hZ PP).1 hP)) (fun PP hP => hU' PP ((hZ PP).1 hP))
  have hUA := GlobalTheory.LevSplit.finE_mem_UA T g
  obtain ⟨h3, h4⟩ := GlobalTheory.T.selfDualFrame_conj_integral_smul_of_integral T ΛT βT hsd hfr _ hUA _ rfl e h1 h2
  obtain ⟨hεε, hεc⟩ := GlobalTheory.T.idempotentSum_add_conj_idempotent_conj_fixed Z e hZe
  obtain ⟨k, hk, hmt⟩ := GlobalTheory.T.exists_idempotent_component_of_group_element T g (e + cA D e) hg hεε hεc
  refine ⟨k, ?_, fun PP hP => (GlobalTheory.T.localProjection_eq_of_idempotent_patch T _ g k _ (GlobalTheory.T.adeleTensorComponent_idempotentSum_add_conj_eq_one Z e hZe PP hP) hmt).symm⟩
  have hfk := GlobalTheory.T.finiteEmbedding_idempotent_patch_in_frame T βT g k (e + cA D e) hmt
  obtain ⟨hSt, hR⟩ := GlobalTheory.T.frameIdempotentCutMatrix_mem_stabiliser_reduction T.rank βT _ _ Z e hZe h1 h2 h3 h4 hfk
  refine ⟨hk, ?_⟩
  refine GlobalTheory.T.mem_level_of_type_place_reductions T βT LT _ hQ (GlobalTheory.LevSplit.finE_mem_UA T k) hSt a b ha2 hb2 ha3 hb3 fun PP => ?_
  apply Units.ext
  rw [Units.val_mul, hR PP.1 ((hZ PP.1).2 (Or.inl PP.2)), ha1, hb1]
  exact hred PP.1 ((hZ PP.1).2 (Or.inl PP.2))

end GlobalTheory.SuppLev
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemLevelOfLevelDatumNeZeroTranslateStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_level_of_levelDatum_ne_zero_translate : ∀ (D : D7) (S T : HSp D) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (LT : LevDat D.host.E ℂ T.rank) (Q : Finset (Pl D.host.E)) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Z : Finset (Pl D.host.E)) (e : AE D), IsSelfDualC T ΛT → IsFrame βT ΛT → T.rank ≤ S.rank → LT.Q = ∅ → IsIdemSum e Z → (∀ PP, PP ∈ Z ↔ PP ∈ LT.Pg ∨ PP ∈ Q) → ∀ g ∈ GfC T, ∀ x, levDatum S T βS βT LT Q m e x ≠ 0 → levDatum S T βS βT LT Q m e (actO S T 1 g x) ≠ 0 → ∃ k ∈ levG T βT LT, ∀ PP ∈ Z, projV T ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) g = projV T ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) k := by
  first | exact @GlobalTheory.SuppLev.supp_level | exact GlobalTheory.SuppLev.supp_level | (intros; apply GlobalTheory.SuppLev.supp_level <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointFrameMatrixReductionEqZeroOffPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointFrameMatrixReductionEqZeroOffPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical

namespace GlobalTheory.AdjRedOff

theorem resS_idemSum_eq_zero {D : D7} {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P)
    (hI : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) {PP : Pl D.host.E} (hPP : PP ∉ P) :
    Formalism.L2.DIV.resS D.host.F PP ⟨toEAf D e, hI⟩ = 0 := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  choose hi _ using fun Q : P => GlobalTheory.IdemRes.resS_idem_eq_one D (es Q) Q (hes Q Q.2)
  let t : P → Formalism.L2.Herm.intAf D.host.F D.host.E := fun Q => ⟨toEAf D (es Q), hi Q⟩
  have e1 : (⟨toEAf D (∑ Q ∈ P, es Q), hI⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ∑ Q, t Q := by
    apply Subtype.ext
    change toEAf D (∑ Q ∈ P, es Q) = _
    rw [← Finset.sum_coe_sort P]
    refine (GlobalTheory.TameProd.map_sum_ringHom (toEAf D) _ _).trans ?_
    exact (map_sum (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype t Finset.univ).symm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e1, map_sum]
  refine Finset.sum_eq_zero fun Q _ => ?_
  exact GlobalTheory.TameProd.resS_idem_eq_zero (hes Q Q.2) (fun h => hPP (by rw [← h]; exact Q.2)) _

end GlobalTheory.AdjRedOff

theorem GlobalTheory.AdjRedOff.redM_frMapAdj_off : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.PlaceModels D → ∀ i t σ s P cμ cη m ω BW f₀ f c io, GlobalTheory.LiftRows.IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → ∀ e : AE D, IsIdemSum e (R.Pg ∪ R.Q t) → ∀ x : WO (Vc D i) (Wc D i), IsHalf (cA D e) x → IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) →
  ∀ PP : Pl D.host.E, PP ∉ R.Pg ∪ R.Q t → redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) = 0 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F _ i t σ s P cμ cη m ω BW f₀ f c io _ e he x hx hint PP hPP
  obtain ⟨hI, -⟩ := GlobalTheory.TameProd.resS_idemSum he
  ext a b
  have hm := hint a b
  simp only [redM, dif_pos hm, Matrix.zero_apply]
  have e1 : (⟨frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x a b, hm⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) =
      ⟨toEAf D e, hI⟩ * ⟨frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x a b, hm⟩ :=
    Subtype.ext (GlobalTheory.AdjVecLocal.frMapAdj_half _ _ _ _ hx a b).symm
  rw [e1, map_mul, GlobalTheory.AdjRedOff.resS_idemSum_eq_zero he hI hPP, zero_mul]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointFrameMatrixReductionEqZeroOffPlacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjointFrameMatrix_reduction_eq_zero_off_places : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.PlaceModels D → ∀ i t σ s P cμ cη m ω BW f₀ f c io, GlobalTheory.LiftRows.IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → ∀ e : AE D, IsIdemSum e (R.Pg ∪ R.Q t) → ∀ x : WO (Vc D i) (Wc D i), IsHalf (cA D e) x → IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) →
  ∀ PP : Pl D.host.E, PP ∉ R.Pg ∪ R.Q t → redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) = 0 := by
  first | exact @GlobalTheory.AdjRedOff.redM_frMapAdj_off | exact GlobalTheory.AdjRedOff.redM_frMapAdj_off | (intros; apply GlobalTheory.AdjRedOff.redM_frMapAdj_off <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSumOfMemFockSpan
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FockApprox

section

open GlobalTheory.RealWeil GlobalTheory.Mem.Lift GlobalTheory.Size GlobalTheory.ChainFr GlobalTheory.FockCompare GlobalTheory.OrientedHeis GlobalTheory.FockDensity GlobalTheory.SquareComm
open scoped ENNReal

variable {D : D7}

theorem cart_frSgn (ε : Bool) (S : GlobalTheory.Grid.Node D) :
    (frSgn ε (Fr.ofModel S.M)).cart = GlobalTheory.Grid.cartS ε S := by
  funext τ
  cases ε
  · show (S.M.fr τ)⁻¹ * Formalism.REAL.Jm (fun a => xor false (S.M.ε τ a)) * S.M.fr τ = (S.M.fr τ)⁻¹ * Formalism.REAL.Jm (S.M.ε τ) * S.M.fr τ
    simp only [Bool.false_xor]
  · have e' : Formalism.REAL.Jm (fun a => xor true (S.M.ε τ a)) = -Formalism.REAL.Jm (S.M.ε τ) := by
      ext a b
      by_cases h : a = b
      · subst h; cases h' : S.M.ε τ a <;> simp [Formalism.REAL.Jm, h']
      · simp [Formalism.REAL.Jm, h]
    show (S.M.fr τ)⁻¹ * Formalism.REAL.Jm (fun a => xor true (S.M.ε τ a)) * S.M.fr τ = -((S.M.fr τ)⁻¹ * Formalism.REAL.Jm (S.M.ε τ) * S.M.fr τ)
    rw [e', Matrix.mul_neg, Matrix.neg_mul]

theorem ptF_eq_fock (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (ε : Bool) (S T : GlobalTheory.Grid.Node D)
    (f : WO S.V T.V → ℂ) (P : GlobalTheory.Grid.Pol S T) :
    ptF ψ θ (frSgn ε (Fr.ofModel S.M)) (Fr.ofModel T.M) f P = GlobalTheory.Grid.fock ψ θ ε S T f P := by
  unfold ptF GlobalTheory.Grid.fock
  rw [cart_frSgn]
  rfl

theorem isVacF_iff (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (ε : Bool) (S T : GlobalTheory.Grid.Node D)
    (f : WO S.V T.V → ℂ) :
    IsVacF ψ θ (frSgn ε (Fr.ofModel S.M)) (Fr.ofModel T.M) f ↔ GlobalTheory.Grid.IsFinVec ψ θ ε S T f := by
  unfold IsVacF GlobalTheory.Grid.IsFinVec
  rw [cart_frSgn]
  rfl

end

end GlobalTheory.FockApprox

namespace GlobalTheory.FockApprox

section

open GlobalTheory.RealWeil GlobalTheory.Mem.Lift GlobalTheory.Size GlobalTheory.ChainFr GlobalTheory.FockCompare GlobalTheory.OrientedHeis GlobalTheory.FockDensity GlobalTheory.SquareComm
open scoped ENNReal

theorem exists_sum_of_mem_fockSpan {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (ε : Bool) (S T : GlobalTheory.Grid.Node D)
    (U : AddSubgroup (WO S.V T.V)) {g : WO S.V T.V → ℂ}
    (hg : g ∈ fockSpan ψ θ (frSgn ε (Fr.ofModel S.M)) (Fr.ofModel T.M) U) :
    ∃ (n : ℕ) (f : Fin n → (WO S.V T.V → ℂ)) (p : Fin n → GlobalTheory.Grid.Pol S T),
      (∀ l, GlobalTheory.Grid.IsFinVec ψ θ ε S T (f l)) ∧ g = ∑ l, GlobalTheory.Grid.fock ψ θ ε S T (f l) (p l) := by
  obtain ⟨n, c, x, hx⟩ := Submodule.mem_span_set'.1 hg
  choose f₀ P h1 _ h3 using fun l => (x l).2
  refine ⟨n, f₀, fun l => c l • P l, fun l => (isVacF_iff ψ θ ε S T _).1 (h1 l), ?_⟩
  rw [← hx]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [h3 l, map_smul, ptF_eq_fock]

end

end GlobalTheory.FockApprox

namespace GlobalTheory.FockApprox

section

open Formalism.IndefR.Mult GlobalTheory.RealWeil GlobalTheory.Mem.Lift GlobalTheory.Size GlobalTheory.ChainFr GlobalTheory.FockCompare GlobalTheory.OrientedHeis GlobalTheory.FockDensity
open scoped ENNReal

theorem dense_level {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D} (A : Fr V) (B : Fr W)
    (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {μ : Measure (WO V W)} {𝓕 : Set (WO V W)}
    (hm : IsCovolOne (ratL W V) μ 𝓕) {U : AddSubgroup (WO V W)} (hU : IsOpen (U : Set (WO V W)))
    {f : WO V W → ℂ} (hf : f ∈ GlobalTheory.Size.thetaLevel ψ V W U) (d : ℕ) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ g ∈ fockSpan ψ θ A B U, g ∈ GlobalTheory.Size.thetaLevel ψ V W U ∧ sobO ψ θ μ 𝓕 d (f - g) < δ := by
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨-, i2, i3, i4, i5, -⟩ := GlobalTheory.AdelicMatrixLattice.lattice D W V
  haveI : BorelSpace (WO V W) := ⟨rfl⟩
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, hm.2.2]; exact ENNReal.one_lt_top⟩
  have e0 : coeL ψ V W (toB hψ f hf.1) = f := coe_toB hψ f hf.1
  have hF : toB hψ f hf.1 ∈ (GlobalTheory.Size.thetaLevel ψ V W U).comap (coeL ψ V W) := by
    rw [Submodule.mem_comap, e0]
    exact hf
  obtain ⟨g, h1, h2, h3⟩ := dense_vec h hψ A B hU (toL2 _ _ (μ.restrict 𝓕))
    (fun v G => by
      rw [← enorm_sq_inj, ← lintegral_norm_sq_eq_toL2, ← lintegral_norm_sq_eq_toL2]
      exact lintegral_rhoB hψ μ 𝓕 hm.1 hm.2.1 _ G)
    (fun a : D.what₂.Tau × Fin W.rank × Fin V.rank × Bool =>
      atPl a.1 (Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1))) d hF hδ
  refine ⟨coeL ψ V W g, h1, h2, lt_of_eq_of_lt ?_ h3⟩
  have e1 : ∀ G : BB ψ V W, l2O μ 𝓕 (coeL ψ V W G) = ‖toL2 _ _ (μ.restrict 𝓕) G‖ₑ := fun G =>
    (eLpNorm_congr_ae (BoundedContinuousFunction.coeFn_toLp 2 (μ.restrict 𝓕) ℂ G.1)).symm.trans (Lp.enorm_def _).symm
  have e2 : f - coeL ψ V W g = coeL ψ V W (toB hψ f hf.1 - g) := by rw [LinearMap.map_sub, e0]
  simp only [sobO, wordSum, e2, coe_word h hψ hU _ (sub_mem hF h2), e1]

end

end GlobalTheory.FockApprox


open scoped ENNReal in
theorem GlobalTheory.FockApprox.theta_approx_fock : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → IsStdChar D ψ (-1) → ∀ (ε : Bool) (S T : GlobalTheory.Grid.Node D) (U : AddSubgroup (WO S.V T.V)), IsOpen (U : Set (WO S.V T.V)) → ∀ Φ, Φ ∈ GlobalTheory.Size.thetaLevel ψ (GlobalTheory.Grid.sgn ε S.V) T.V U → ∀ (μ : Measure (WO S.V T.V)) (𝓕 : Set (WO S.V T.V)), IsCovolOne (ratL T.V (GlobalTheory.Grid.sgn ε S.V)) μ 𝓕 → ∀ (d : ℕ) (δ : ℝ), 0 < δ → ∃ (n : ℕ) (f : Fin n → (WO S.V T.V → ℂ)) (p : Fin n → GlobalTheory.Grid.Pol S T), (∀ l, GlobalTheory.Grid.IsFinVec ψ θ ε S T (f l)) ∧ (Φ - ∑ l, GlobalTheory.Grid.fock ψ θ ε S T (f l) (p l)) ∈ GlobalTheory.Size.thetaLevel ψ (GlobalTheory.Grid.sgn ε S.V) T.V U ∧ @GlobalTheory.Size.sobO D ψ θ (GlobalTheory.Grid.sgn ε S.V) T.V μ 𝓕 d (Φ - ∑ l, GlobalTheory.Grid.fock ψ θ ε S T (f l) (p l)) < ENNReal.ofReal δ := by
  intro D ψ θ hθ hψ ε S T U hU Φ hΦ μ 𝓕 hm d δ hδ
  obtain ⟨g, h1, h2, h3⟩ := GlobalTheory.FockApprox.dense_level (ψ := ψ) (θ := θ) (V := GlobalTheory.Grid.sgn ε S.V) (W := T.V)
    (GlobalTheory.SquareComm.frSgn ε (GlobalTheory.ChainFr.Fr.ofModel S.M)) (GlobalTheory.ChainFr.Fr.ofModel T.M) hψ hθ hm hU hΦ d
    (ENNReal.ofReal_pos.2 hδ)
  obtain ⟨n, f, p, hf, hg⟩ := GlobalTheory.FockApprox.exists_sum_of_mem_fockSpan ψ θ ε S T U h1
  refine ⟨n, f, p, hf, ?_, ?_⟩
  · rw [← hg]
    exact sub_mem hΦ h2
  · rw [← hg]
    exact h3

end
end
