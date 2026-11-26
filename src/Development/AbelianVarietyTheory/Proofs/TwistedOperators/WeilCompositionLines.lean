module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EmbeddingColumnLatticeIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemAdelicLatticeAtPlaceOfTensorWithLattice
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoUnitaryGroupIdempotentLocalizationFiniteS
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorEqTopOrLeKerFiniteLengthModules
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactElementGaussianList
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormKFiniteApprox
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsKFiniteIteratedCompactAverageApprox

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilCompositionLines
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzTendstoOperatorCurveOfPointwise
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzTendstoOperatorCurveOfPointwise
open Filter Topology
open scoped Uniformity

namespace GlobalTheory

theorem schwartz_tendsto_apply_of_tendsto_pointwise :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (S : ℝ → SchwartzMap V ℂ →L[ℂ] SchwartzMap V ℂ),
    (∀ f, Filter.Tendsto (fun t => S t f) (nhdsWithin 0 {0}ᶜ) (nhds f)) →
    ∀ (g : ℝ → SchwartzMap V ℂ) (g₀ : SchwartzMap V ℂ), Filter.Tendsto g (nhdsWithin 0 {0}ᶜ) (nhds g₀) →
      Filter.Tendsto (fun t => S t (g t)) (nhdsWithin 0 {0}ᶜ) (nhds g₀) := by
  intro V _ _ _ S hS g g₀ hg
  haveI : BarrelledSpace ℂ (SchwartzMap V ℂ) := schwartzMap_barrelledSpace V
  rw [tendsto_iff_seq_tendsto]
  intro u hu
  have hq := schwartz_withSeminorms ℂ V ℂ
  have hUE : UniformEquicontinuous ((↑) ∘ fun n => S (u n)) := by
    refine hq.banach_steinhaus (𝓕 := fun n => S (u n)) ?_
    intro k f
    exact ((hq.continuous_seminorm k).tendsto f).comp ((hS f).comp hu) |>.bddAbove_range
  have hE := hUE.equicontinuous g₀
  have h1 : Tendsto (fun n => (S (u n) g₀, S (u n) (g (u n)))) atTop (𝓤 (SchwartzMap V ℂ)) := by
    intro U hU
    have := (hg.comp hu).eventually (hE U hU)
    rw [Filter.mem_map]
    exact this.mono fun n hn => hn n
  exact ((hS g₀).comp hu).congr_uniformity h1

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzTendstoOperatorCurveOfPointwiseStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_tendsto_operatorCurve_of_pointwise : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (S : ℝ → SchwartzMap V ℂ →L[ℂ] SchwartzMap V ℂ),
    (∀ f, Filter.Tendsto (fun t => S t f) (nhdsWithin 0 {0}ᶜ) (nhds f)) →
    ∀ (g : ℝ → SchwartzMap V ℂ) (g₀ : SchwartzMap V ℂ), Filter.Tendsto g (nhdsWithin 0 {0}ᶜ) (nhds g₀) →
      Filter.Tendsto (fun t => S t (g t)) (nhdsWithin 0 {0}ᶜ) (nhds g₀) := by
  first | exact @GlobalTheory.schwartz_tendsto_apply_of_tendsto_pointwise | exact GlobalTheory.schwartz_tendsto_apply_of_tendsto_pointwise | (intros; apply GlobalTheory.schwartz_tendsto_apply_of_tendsto_pointwise <;> assumption)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.ArchProdRule

open Filter Topology

theorem slope_prod {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] :
    ∀ (k : ℕ) (T : Fin k → ℝ → SchwartzMap V ℂ →ₗ[ℂ] SchwartzMap V ℂ) (Q : Fin k → SchwartzMap V ℂ → SchwartzMap V ℂ),
    (∀ i t, Continuous (T i t)) → (∀ i f, T i 0 f = f) →
    (∀ i f, Tendsto (fun t : ℝ => t⁻¹ • (T i t f - f)) (𝓝[≠] 0) (𝓝 (Q i f))) →
    ∀ f, Tendsto (fun t : ℝ => t⁻¹ • ((List.ofFn fun i => T i t).prod f - f)) (𝓝[≠] 0) (𝓝 (∑ i, Q i f)) := by
  intro k
  induction k with
  | zero =>
    intro T Q _ _ _ f
    simpa using (tendsto_const_nhds (x := (0 : SchwartzMap V ℂ)) (f := 𝓝[≠] (0 : ℝ)))
  | succ k ih =>
    intro T Q hc h0 hQ f
    have ht := ih (fun i => T i.succ) (fun i => Q i.succ) (fun i => hc i.succ) (fun i => h0 i.succ)
      (fun i => hQ i.succ) f
    let S : ℝ → SchwartzMap V ℂ →L[ℂ] SchwartzMap V ℂ := fun t => ⟨T 0 t, hc 0 t⟩
    have hS1 : ∀ g, Tendsto (fun t => S t g) (𝓝[≠] 0) (𝓝 g) := by
      intro g
      have h2 : Tendsto (fun t : ℝ => t • (t⁻¹ • (T 0 t g - g)) + g) (𝓝[≠] 0) (𝓝 ((0 : ℝ) • Q 0 g + g)) :=
        ((tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).smul (hQ 0 g)).add_const g
      rw [zero_smul, zero_add] at h2
      refine h2.congr' (eventually_nhdsWithin_of_forall fun t ht => ?_)
      rw [smul_smul, mul_inv_cancel₀ ht, one_smul, sub_add_cancel]
      rfl
    have h1 := GlobalTheory.T.schwartz_tendsto_operatorCurve_of_pointwise V S hS1 _ _ ht
    have h3 := h1.add (hQ 0 f)
    rw [Fin.sum_univ_succ, add_comm (Q 0 f)]
    refine h3.congr fun t => ?_
    have e : (List.ofFn fun i => T i t).prod f = T 0 t ((List.ofFn fun i : Fin k => T i.succ t).prod f) := by
      rw [List.ofFn_succ, List.prod_cons]
      rfl
    rw [e]
    show T 0 t (t⁻¹ • ((List.ofFn fun i : Fin k => T i.succ t).prod f - f)) + _ = _
    rw [LinearMap.map_smul_of_tower, map_sub, ← smul_add, sub_add_sub_cancel]


end GlobalTheory.ArchProdRule
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeStabilizersFixVacuaFixesPureTensor
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeStabilizersFixVacuaFixesPureTensor
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.FinDecomp

namespace GlobalTheory.SphGlob

theorem loc_mem_KAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ)
    (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (K : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J),
    (∀ z ∈ GlobalTheory.InertSph.latAt W v, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat K *ᵥ z ∈ GlobalTheory.InertSph.latAt W v ∧
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat K⁻¹ *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
    GlobalTheory.FinDecomp.loc (GlobalTheory.FinDecomp.idem F v) (GlobalTheory.FinDecomp.idem_mul_self v) K ∈ GlobalTheory.InertSph.KAt σ W v := by
  intro F E _ _ _ _ _ σ d W v K hK

  have hfix : ∀ z ∈ GlobalTheory.InertSph.latAt W v, GlobalTheory.FinDecomp.idem F v • z = z := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, -, y, -, rfl⟩ := hz
      rw [smul_smul, GlobalTheory.FinDecomp.idem_mul_of_at ha]
    | zero => simp
    | add z z' _ _ h h' => rw [smul_add, h, h']
    | neg z _ h => rw [smul_neg, h]
  have hphi : ∀ (M : Matrix (Fin d) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), ∀ z ∈ GlobalTheory.InertSph.latAt W v,
      GlobalTheory.FinDecomp.phi (GlobalTheory.FinDecomp.idem F v) M *ᵥ z = M *ᵥ z := by
    intro M z hz
    have h1 : (1 - GlobalTheory.FinDecomp.idem F v) • z = 0 := by rw [sub_smul, one_smul, hfix z hz, sub_self]
    rw [GlobalTheory.FinDecomp.phi, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, h1, zero_add,
      ← Matrix.mulVec_smul, hfix z hz]
  refine ⟨fun u hu => ?_, fun z hz => ?_⟩
  · show u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.FinDecomp.loc _ _ K) - 1) = 0
    rw [GlobalTheory.FinDecomp.mat_loc, GlobalTheory.FinDecomp.phi_sub_one, smul_smul, GlobalTheory.FinDecomp.mul_idem_of_evFin hu, zero_smul]
  · rw [GlobalTheory.FinDecomp.mat_loc, GlobalTheory.FinDecomp.mat_loc_inv, hphi _ z hz, hphi _ z hz]
    exact hK z hz

end GlobalTheory.SphGlob

namespace GlobalTheory.SphGlob


open scoped Classical in
theorem ev_mem_adm {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (x : κ → AF F) :
    (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (GlobalTheory.WeilM.adeleClass F).adm κ := by
  intro g _
  refine ⟨g (fun i => (x i).2) • (BoundedContinuousFunction.evalCLM ℂ (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1)).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ), fun f => ?_⟩
  simp only [LinearMap.proj_apply, GlobalTheory.WeilM.pureA, ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_comp',
    Function.comp_apply, Pi.smul_apply, SchwartzMap.toBoundedContinuousFunctionCLM_apply,
    BoundedContinuousFunction.evalCLM_apply, smul_eq_mul]
  rw [mul_comm]

end GlobalTheory.SphGlob


open GlobalTheory.SphGlob in
theorem GlobalTheory.SphGlob.fixes_pure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ)
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))),
    0 < n → X.L.IsFullLattice E → W.L.IsLattice E → M.IsGood ψ → M.IsWeil ψ χX χW om →
    (∀ v, v ∉ S → ∀ k ∈ GlobalTheory.InertSph.KAt σ W v,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om (1, k)) (M.vac v) (M.vac v)) →
    ∀ k : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J,
    (∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = 0) →
    (∀ w ∈ S, ∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = 0) →
    (∀ w, w ∉ S → ∀ γ, γ * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k)ᵀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X W w ↔ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X W w) →
    ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F w) → ℂ),
      (∀ w, φ w ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F w)) → (∀ w, w ∉ S → φ w = M.vac w) →
      om (1, k) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
  classical
  intro F E _ _ _ _ _ σ n d X W M ψ χX χW om S hn hXL hWL hM hw hAct k hinf hS hlat f φ hSB hφ

  have hstd : ∀ᶠ w in Filter.cofinite, φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := by
    filter_upwards [hM.std, S.finite_toSet.eventually_cofinite_notMem] with w hw hwS
    rw [hφ w hwS, hw]
  set Φ := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ with hΦ

  have hloc : ∀ v, v ∉ S → ∀ h ∈ GlobalTheory.InertSph.KAt σ W v, om (1, h) Φ = Φ := by
    intro v hv h hh
    obtain ⟨r, hr, hrt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ hstd
    have e1 : Φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) (φ v) r := by rw [hΦ, hrt, Function.update_eq_self]
    have hRest : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F v) (φ v) r :=
      ⟨hr, by rw [← e1]; exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd⟩
    have hA := hAct v hv h hh
    rw [← hφ v hv] at hA
    rw [e1, hA r hRest]

  have hcut : ∀ v, v ∉ S → loc (idem F v) (idem_mul_self v) k ∈ GlobalTheory.InertSph.KAt σ W v := by
    intro v hv
    refine loc_mem_KAt F E σ d W v k fun z hz => ⟨?_, ?_⟩
    · refine GlobalTheory.T.mem_adelicLatticeAtPlace_of_tensor_with_lattice F E n d X W v _ hn (by letI := hXL; infer_instance) fun x hx => ?_
      have h0 := GlobalTheory.InertSphStab.vecMulVec_mem X W v hx hz
      rw [← GlobalTheory.InertSphStab.vecMulVec_mul_transpose]
      exact (hlat v hv _).2 h0
    · refine GlobalTheory.T.mem_adelicLatticeAtPlace_of_tensor_with_lattice F E n d X W v _ hn (by letI := hXL; infer_instance) fun x hx => ?_
      have h0 := GlobalTheory.InertSphStab.vecMulVec_mem X W v hx hz
      refine (hlat v hv _).1 ?_
      rw [GlobalTheory.InertSphStab.vecMulVec_mul_transpose, Matrix.mulVec_mulVec, mat_mul_inv, Matrix.one_mulVec]
      exact h0
  have hcutS : ∀ v ∈ S, loc (idem F v) (idem_mul_self v) k = 1 := by
    intro v hv
    apply ua_ext
    rw [mat_loc, mat_one, ← sub_eq_zero, phi_sub_one]
    exact hS v hv _ fun u hu => by rw [smul_eq_mul, mul_idem_of_evFin hu]
  have hone : ∀ v, om (1, loc (idem F v) (idem_mul_self v) k) Φ = Φ := by
    intro v
    by_cases hv : v ∈ S
    · rw [hcutS v hv]; show om 1 Φ = Φ; rw [map_one]; rfl
    · exact hloc v hv _ (hcut v hv)
  have hlist : ∀ l : List (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)),
      om (1, (l.map fun v => loc (idem F v) (idem_mul_self v) k).prod) Φ = Φ := by
    intro l
    induction l with
    | nil => show om 1 Φ = Φ; rw [map_one]; rfl
    | cons v t ih =>
      rw [List.map_cons, List.prod_cons]
      have : ((1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J), loc (idem F v) (idem_mul_self v) k *
          (t.map fun v => loc (idem F v) (idem_mul_self v) k).prod) =
          (1, loc (idem F v) (idem_mul_self v) k) * (1, (t.map fun v => loc (idem F v) (idem_mul_self v) k).prod) := by
        simp
      rw [this, map_mul, Module.End.mul_apply, ih, hone]
  have hT : ∀ T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), om (1, loc (idemS F T) (idemS_mul_self T) k) Φ = Φ := by
    intro T
    have e : loc (idemS F T) (idemS_mul_self T) k = (T.toList.map fun v => loc (idem F v) (idem_mul_self v) k).prod := by
      apply ua_ext
      rw [mat_prod_loc k _ T.nodup_toList, Finset.toList_toFinset, mat_loc]
    rw [e]; exact hlist _

  have hcont := hw.2.2
  have hΦA : Φ ∈ (GlobalTheory.WeilM.adeleClass F).sp (Fin n × Fin d) := GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd
  funext x
  have hc := hcont _ (ev_mem_adm x) Φ hΦA
  have ht : Filter.Tendsto (fun T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) =>
      ((1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J), loc (idemS F T) (idemS_mul_self T) k)) Filter.atTop (nhds (1, k)) :=
    tendsto_const_nhds.prodMk_nhds (GlobalTheory.T.tendsto_unitaryGroupIdempotentLocalization_finiteSets F E σ d W.J k hinf)
  have hlim : Filter.Tendsto (fun T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) =>
      (LinearMap.proj x : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ) (om (1, loc (idemS F T) (idemS_mul_self T) k) Φ))
      Filter.atTop (nhds ((LinearMap.proj x : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ) (om (1, k) Φ))) :=
    (hc.tendsto _).comp ht
  have hconst : (fun T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) =>
      (LinearMap.proj x : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ) (om (1, loc (idemS F T) (idemS_mul_self T) k) Φ)) =
      fun _ => Φ x := by
    funext T; rw [hT T]; rfl
  rw [hconst] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeStabilizersFixVacuaFixesPureTensorStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeStabilizers_fix_vacua_fixes_pureTensor : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ)
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))),
    0 < n → X.L.IsFullLattice E → W.L.IsLattice E → M.IsGood ψ → M.IsWeil ψ χX χW om →
    (∀ v, v ∉ S → ∀ k ∈ GlobalTheory.InertSph.KAt σ W v,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om (1, k)) (M.vac v) (M.vac v)) →
    ∀ k : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J,
    (∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = 0) →
    (∀ w ∈ S, ∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = 0) →
    (∀ w, w ∉ S → ∀ γ, γ * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k)ᵀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X W w ↔ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X W w) →
    ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F w) → ℂ),
      (∀ w, φ w ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F w)) → (∀ w, w ∉ S → φ w = M.vac w) →
      om (1, k) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
  exact @_root_.GlobalTheory.SphGlob.fixes_pure
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsIntertwining
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.HoweGlobal

theorem decomp {M₀ : Type} [AddCommGroup M₀] [Module ℂ M₀] {ι : Type} [Fintype ι] {M : ι → Type}
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)] (t : M₀ ⊗[ℂ] (⨂[ℂ] i, M i)) :
    ∃ (m : ℕ) (f : Fin m → M₀) (φ : Fin m → ∀ i, M i), t = ∑ j, f j ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (φ j) := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  | tmul x y =>
    induction y using PiTensorProduct.induction_on with
    | smul_tprod c φ =>
      refine ⟨1, fun _ => c • x, fun _ => φ, ?_⟩
      rw [Fin.sum_univ_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    | add y₁ y₂ h₁ h₂ =>
      obtain ⟨m₁, f₁, φ₁, e₁⟩ := h₁
      obtain ⟨m₂, f₂, φ₂, e₂⟩ := h₂
      refine ⟨m₁ + m₂, Fin.append f₁ f₂, Fin.append φ₁ φ₂, ?_⟩
      rw [TensorProduct.tmul_add, e₁, e₂, Fin.sum_univ_add]
      simp
  | add t₁ t₂ h₁ h₂ =>
    obtain ⟨m₁, f₁, φ₁, e₁⟩ := h₁
    obtain ⟨m₂, f₂, φ₂, e₂⟩ := h₂
    refine ⟨m₁ + m₂, Fin.append f₁ f₂, Fin.append φ₁ φ₂, ?_⟩
    rw [e₁, e₂, Fin.sum_univ_add]
    simp

end GlobalTheory.HoweGlobal

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingInnerProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open scoped ComplexConjugate

noncomputable section

namespace GlobalTheory.KInvData

theorem hasDerivAt_linear {Z Q : Type} [NormedAddCommGroup Q] [NormedSpace ℂ Q] (U : Submodule ℂ (Z → ℂ))
    [FiniteDimensional ℂ U] (φ : (Z → ℂ) →ₗ[ℂ] Q) {u : ℝ → Z → ℂ} {u' : Z → ℂ} {t : ℝ} (hu : ∀ s, u s ∈ U) (hu' : u' ∈ U)
    (hd : ∀ z, HasDerivAt (fun s => u s z) (u' z) t) : HasDerivAt (fun s => φ (u s)) (φ u') t := by
  rw [hasDerivAt_iff_tendsto_slope]
  have h1 : Filter.Tendsto (slope u t) (nhdsWithin t {t}ᶜ) (nhds u') := by
    rw [tendsto_pi_nhds]
    intro z
    exact hasDerivAt_iff_tendsto_slope.1 (hd z)
  have hm : ∀ s, slope u t s ∈ U := fun s => U.smul_of_tower_mem _ (U.sub_mem (hu s) (hu t))
  have h2 : Filter.Tendsto (fun s => (⟨slope u t s, hm s⟩ : U)) (nhdsWithin t {t}ᶜ) (nhds ⟨u', hu'⟩) :=
    tendsto_subtype_rng.2 h1
  have h3 := ((φ ∘ₗ U.subtype).continuous_of_finiteDimensional.tendsto _).comp h2
  refine h3.congr fun s => ?_
  simp [slope, LinearMap.map_smul_of_tower]

theorem kapX_one {D : D7} (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • reindex e e X.gramᵀ) : kapX X e hJ 1 = 1 := by
  apply Subtype.ext
  show Units.map (Matrix.reindexAlgEquiv (AE D) (AE D) e).toMonoidHom (matHom X 1) = 1
  rw [map_one, map_one]

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {W W₁ X : HSp D} {A : Fr W} {A₁ : Fr W₁} {B : Fr X}
  {α β : (AE D)ˣ →* Circle} {ν : Measure (GA D W)} {𝓕 : Set (GA D W)} {ν₁ : Measure (GA D W₁)} {𝓕₁ : Set (GA D W₁)}
  {ωA : WRep W X} {ωB : WRep W₁ X} {e : Fin X.rank ≃ Fin (W.rank + W₁.rank)}
  {Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E} {Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank}
  {Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E} {om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W}
  {om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W}
  {cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X}
  {cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X}
  {Pi : ModuleCat.{0} ℂ} {rf : GA D X → Module.End ℂ Pi}
  {rl : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ → Module.End ℂ Pi} {p : (WO W X → ℂ) →ₗ[ℂ] Pi}

theorem line_step (hθ : IsInfFam θ) (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ)
    (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB)
    (hmap : IsCoinvMap θ ωA (algF ψ θ true A B) Pi rf rl p)
    {τ : D.what₂.Tau} {Y : Matrix (Fin W.rank) (Fin W.rank) ℂ} (hY : Y ∈ lieAt W τ)
    (U : Submodule ℂ ((Fin W.rank × Fin (W.rank + W₁.rank) → AF D.host.F) → ℂ)) [FiniteDimensional ℂ U]
    (hU : U ≤ algD Γ.M Bs.ψ Bs.emb)
    (hUt : ∀ t : ℝ, ∀ x ∈ U, om (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hO.JW (oneP θ W τ Y t), 1) x ∈ U)
    {ΦD : (Fin W.rank × Fin (W.rank + W₁.rank) → AF D.host.F) → ℂ} (hΦD : ΦD ∈ U) {Φ Φ₁ : WO W X → ℂ}
    (h0 : IsDatum Γ.M ψ cA ΦD Φ)
    (h1 : IsDatum Γ.M ψ cA (om (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hO.JW (oneP θ W τ Y 1), 1) ΦD) Φ₁) : p Φ₁ = p Φ := by
  classical
  have huniq : ∀ {x : (Fin W.rank × Fin (W.rank + W₁.rank) → AF D.host.F) → ℂ} {f g : WO W X → ℂ},
      IsDatum Γ.M ψ cA x f → IsDatum Γ.M ψ cA x g → f = g := fun hf hg =>
    GlobalTheory.SquareAgree.CoinvPass.isDatum_unique cA.surjective hf hg
  let G : Submodule ℂ (((Fin W.rank × Fin (W.rank + W₁.rank) → AF D.host.F) → ℂ) × (WO W X → ℂ)) :=
    { carrier := {q | q.1 ∈ U ∧ IsDatum Γ.M ψ cA q.1 q.2}
      add_mem' := fun ha hb => ⟨U.add_mem ha.1 hb.1, GlobalTheory.SquareAgree.CoinvPass.isDatum_add hψ ha.2 hb.2⟩
      zero_mem' := ⟨U.zero_mem, GlobalTheory.SquareAgree.CoinvPass.isDatum_zero⟩
      smul_mem' := fun c _ ha => ⟨U.smul_mem c ha.1, GlobalTheory.SquareAgree.CoinvPass.isDatum_smul c ha.2⟩ }
  let fG : G →ₗ[ℂ] U := ((LinearMap.fst ℂ _ _).comp G.subtype).codRestrict U (fun q => q.2.1)
  have hfG : Function.Injective fG := by
    intro q q' hq
    have e1 : q.1.1 = q'.1.1 := congrArg Subtype.val hq
    have e2 : q.1.2 = q'.1.2 := huniq q.2.2 (e1 ▸ q'.2.2)
    exact Subtype.ext (Prod.ext e1 e2)
  haveI : FiniteDimensional ℂ G := Module.Finite.of_injective fG hfG
  let Uf : Submodule ℂ (WO W X → ℂ) := G.map (LinearMap.snd ℂ _ _)
  let Φt : ℝ → WO W X → ℂ := fun t => ωA (oneP θ W τ Y t, 1) Φ
  have hdat : ∀ t, IsDatum Γ.M ψ cA (om (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hO.JW (oneP θ W τ Y t), 1) ΦD) (Φt t) := by
    intro t
    have h := hO.weilA ΦD Φ h0 (oneP θ W τ Y t) 1
    rwa [kapX_one] at h
  have hmemU : ∀ t, Φt t ∈ Uf := fun t => ⟨(_, Φt t), ⟨hUt t ΦD hΦD, hdat t⟩, rfl⟩
  have halg : ∀ t, Φt t ∈ algF ψ θ true A B := by
    intro t
    obtain ⟨Φ', hΦ', hD'⟩ := hO.algA' _ (hU (hUt t ΦD hΦD))
    rwa [huniq hD' (hdat t)] at hΦ'
  have hshift : ∀ s t, ωA (oneP θ W τ Y s, 1) (Φt t) = Φt (s + t) := by
    intro s t
    simp only [Φt]
    rw [GlobalTheory.Mem.Lift.oneP_add hθ hY s t, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]
  have hzero : ∀ t, ∀ l : Module.Dual ℂ Pi, HasDerivAt (fun s => l (p (Φt s))) 0 t := by
    intro t l
    obtain ⟨Φ', hΦ', hder⟩ := hmap.stabM.2 τ Y hY (Φt t) (halg t)
    have hp := hmap.invl τ Y hY (Φt t) (halg t) Φ' hΦ' hder
    have hd : ∀ z, HasDerivAt (fun s => Φt s z) (Φ' z) t := by
      intro z
      have h := HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact hder z)
      refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
      show Φt s z = ωA (oneP θ W τ Y (s - t), 1) (Φt t) z
      rw [hshift, sub_add_cancel]
    have h := hasDerivAt_linear (Uf ⊔ Submodule.span ℂ {Φ'}) (l.comp p) (u := Φt)
      (fun s => Submodule.mem_sup_left (hmemU s)) (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)) hd
    simpa [hp] using h
  have hconst : ∀ l : Module.Dual ℂ Pi, l (p (Φt 1)) = l (p (Φt 0)) := fun l =>
    is_const_of_deriv_eq_zero (fun t => (hzero t l).differentiableAt) (fun t => (hzero t l).deriv) 1 0
  have e1 : Φt 1 = Φ₁ := huniq (hdat 1) h1
  have e0 : Φt 0 = Φ := by
    simp only [Φt]
    rw [GlobalTheory.Mem.Lift.oneP_zero hθ, Prod.mk_one_one, map_one, Module.End.one_apply]
  rw [← e1, ← e0, ← sub_eq_zero]
  exact (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun l => by rw [map_sub, hconst l, sub_self]

end GlobalTheory.KInvData
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AlgebraicDataUnitaryRelationsFinitePlacePolZero
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AlgebraicDataUnitaryRelationsFinitePlacePolZero
open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PolKer

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem RelV.exists_decomp_of_mem_algD {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} (M : Model σ Y W) (ψ : AddChar (AF F) ℂ)
    (emb : ∀ w : InfinitePlace F, EmbOver E w) {Φ : (Fin n × Fin d → AF F) → ℂ}
    (hΦ : Φ ∈ GlobalTheory.SquareAgree.algD M ψ emb) :
    ∃ (T : Finset (Pl F)) (m : ℕ) (f : Fin m → SInf F (Fin n × Fin d))
      (φ : Fin m → ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ),
      (∀ i, f i ∈ M.Pol ψ emb ∧ (∀ v, φ i v ∈ SB _) ∧ ∀ v ∉ T, φ i v = M.vac v) ∧ Φ = ∑ i, pure (f i) (φ i) := by
  classical
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, φ, hf, hSB, hev, rfl⟩ := hx
    refine ⟨(Filter.eventually_cofinite.1 hev).toFinset, 1, fun _ => f, fun _ => φ, fun _ => ⟨hf, hSB, fun v hv => ?_⟩, ?_⟩
    · by_contra hc
      exact hv ((Set.Finite.mem_toFinset _).2 hc)
    · simp
  | zero => exact ⟨∅, 0, Fin.elim0, Fin.elim0, fun i => Fin.elim0 i, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨T₁, m₁, f₁, φ₁, h₁, rfl⟩ := hx
    obtain ⟨T₂, m₂, f₂, φ₂, h₂, rfl⟩ := hy
    refine ⟨T₁ ∪ T₂, m₁ + m₂, Fin.append f₁ f₂, Fin.append φ₁ φ₂, fun k => ?_, ?_⟩
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) k
      · simp only [Fin.append_left]
        exact ⟨(h₁ i).1, (h₁ i).2.1, fun v hv => (h₁ i).2.2 v fun h => hv (Finset.mem_union_left _ h)⟩
      · simp only [Fin.append_right]
        exact ⟨(h₂ i).1, (h₂ i).2.1, fun v hv => (h₂ i).2.2 v fun h => hv (Finset.mem_union_right _ h)⟩
    · rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
  | smul c x _ hx =>
    obtain ⟨T, m, f, φ, h, rfl⟩ := hx
    refine ⟨T, m, fun i => c • f i, φ, fun i => ⟨(M.Pol ψ emb).smul_mem c (h i).1, (h i).2.1, (h i).2.2⟩, ?_⟩
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    funext x
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Pi.smul_apply, SchwartzMap.smul_apply, smul_eq_mul, mul_assoc]

theorem RelV.pure_neg {κ : Type} [Fintype κ] (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) :
    pure (-f) φ = -pure f φ := by
  funext x
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, SchwartzMap.neg_apply, Pi.neg_apply, neg_mul]

theorem polZero_relV : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf → ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), ∀ g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ G.V (GlobalTheory.AdelicU.evFin F v),
    ∀ Φ ∈ GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb, GlobalTheory.PolKer.PolZero Bs G Xc R Rf (om (g, 1) Φ - Φ) := by
  classical
  intro F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM v g hg Φ hΦ
  obtain ⟨T₀, m, f, φ, hφ, rfl⟩ := RelV.exists_decomp_of_mem_algD G.M Bs.ψ Bs.emb hΦ
  have hT := hM.triple
  have hP := GlobalTheory.ThK.Inhab.pairV hT
  have h1W : (1 : UA σ G.W.J) ∈ UAt σ G.W (evFin F v) := by
    intro u _
    show u • ((1 : Matrix _ _ _) - 1) = 0
    simp
  choose ψ hψ using fun i => GlobalTheory.ThK.LocalOps.acts_exists hP v (g, 1) hg h1W (φ i v) ((hφ i).2.1 v)
  have hpv : ∀ i, Rf.p v (ψ i) = Rf.p v (φ i v) := by
    intro i
    have hmem : ψ i - φ i v ∈ augAt om v :=
      Submodule.subset_span ⟨g, hg, φ i v, (hφ i).2.1 v, ψ i, (hψ i).1, (hψ i).2, rfl⟩
    have := hM.fin.inv v hmem
    rwa [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
  have hstd : ∀ i, ∀ᶠ w in Filter.cofinite, φ i w = Set.indicator {x | ∀ j, x j ∈ w.adicCompletionIntegers F} 1 := by
    intro i
    have e0 : ∀ᶠ w in Filter.cofinite, φ i w = G.M.vac w :=
      Filter.eventually_cofinite.2 ((T₀.finite_toSet).subset fun w hw => by
        by_contra hc; exact hw ((hφ i).2.2 w hc))
    filter_upwards [e0, hT.geo.hM.std] with w e1 e2
    rw [e1, e2]
  set T : Finset (Pl F) := insert v (Xc.T ∪ T₀) with hTdef
  have hvT : ∀ w, w ∉ T → w ≠ v := fun w hw e => hw (e ▸ Finset.mem_insert_self _ _)
  have hT₀ : ∀ w, w ∉ T → w ∉ T₀ := fun w hw h =>
    hw (Finset.mem_insert_of_mem (Finset.mem_union_right _ h))
  refine ⟨T, fun w hw => Finset.mem_insert_of_mem (Finset.mem_union_left _ hw), m + m,
    Fin.append f fun i => -f i, Fin.append (fun i => Function.update (φ i) v (ψ i)) φ, fun k => ?_, ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · simp only [Fin.append_left]
      refine ⟨(hφ i).1, fun w => ?_, fun w hw => ?_⟩
      · by_cases hw : w = v
        · subst hw; rw [Function.update_self]; exact (hψ i).1
        · rw [Function.update_of_ne hw]; exact (hφ i).2.1 w
      · rw [Function.update_of_ne (hvT w hw)]; exact (hφ i).2.2 w (hT₀ w hw)
    · simp only [Fin.append_right]
      exact ⟨neg_mem (hφ i).1, (hφ i).2.1, fun w hw => (hφ i).2.2 w (hT₀ w hw)⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_sum, Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, RelV.pure_neg, Finset.sum_neg_distrib, ← sub_eq_add_neg]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      exact GlobalTheory.ThK.PolMatchStep.pure_update v (om (g, 1)) (f i) (φ i) (hφ i).2.1 (hstd i) (hψ i).2
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, map_neg, TensorProduct.neg_tmul, Finset.sum_neg_distrib]
    have e : ∀ i, (fun w : T => Rf.p w (Function.update (φ i) v (ψ i) w)) = fun w : T => Rf.p w (φ i w) := by
      intro i
      funext w
      obtain ⟨w, hw⟩ := w
      by_cases hwv : w = v
      · subst hwv
        simp only [Function.update_self]
        exact hpv i
      · simp only [Function.update_of_ne hwv]
    simp only [e, add_neg_cancel]

end GlobalTheory.PolKer

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AlgebraicDataUnitaryRelationsFinitePlacePolZeroStatement
open NumberField IsDedekindDomain
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicData_unitaryRelations_finitePlace_polZero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf → ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), ∀ g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ G.V (GlobalTheory.AdelicU.evFin F v),
    ∀ Φ ∈ GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb, GlobalTheory.PolKer.PolZero Bs G Xc R Rf (om (g, 1) Φ - Φ) := by
  first | exact @GlobalTheory.PolKer.polZero_relV | exact GlobalTheory.PolKer.polZero_relV | (intros; apply GlobalTheory.PolKer.polZero_relV <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsFiniteIdentity
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAlgebraicDatumNotMatchedZeroByLocalMaps
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAlgebraicDatumNotMatchedZeroByLocalMaps
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

namespace GlobalTheory.SquareAgree


open GlobalTheory.SmallThetaModules in
theorem exists_algD_not_polMatch_zero : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf →
    ∃ Φ ∈ GlobalTheory.SquareAgree.algD G.M' B.ψ B.emb, ¬ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch B G X R Rf 0 Φ := by
  intro F E _ _ _ _ _ σ a a' B G X om om' R Rf h
  classical
  let s : ∀ v, Rf.Pi v := fun v => Rf.p' v (G.M'.vac v)
  have hsph : ∀ v ∉ X.T, Rf.p v (G.M.vac v) = s v := fun v hv => (h.fin.sph v hv).1
  have hs0 : ∀ v ∉ X.T, s v ≠ 0 := fun v hv => by
    rw [← hsph v hv]; exact (h.fin.sph v hv).2
  have hXT : (X.T : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))).Finite := X.T.finite_toSet
  obtain ⟨q, hq⟩ := GlobalTheory.T.weil_model_projection_factorisation σ G.V G.W G.M B.ψ h.triple.geo.hM R.Pi R.p Rf.Pi Rf.p s
    (Filter.eventually_cofinite.2 (hXT.subset fun v hv => by by_contra hn; exact hv (hsph v hn)))
  obtain ⟨q', hq'⟩ := GlobalTheory.T.weil_model_projection_factorisation σ G.V' G.W G.M' B.ψ h.triple.geo.hM' R.Pi R.p' Rf.Pi Rf.p' s
    (Filter.Eventually.of_forall fun v => rfl)
  haveI := h.real.nontriv
  obtain ⟨x, hx⟩ := exists_ne (0 : R.Pi)
  have hx' : x ∈ (G.M'.Pol B.ψ B.emb).map R.p' := by rw [h.real.quot'.onto]; trivial
  obtain ⟨f, hf, hfx⟩ := hx'
  have hloc : ∀ v, ∃ φv, φv ∈ GlobalTheory.WeilM.SB _ ∧ Rf.p' v φv ≠ 0 ∧ (v ∉ X.T → φv = G.M'.vac v) := by
    intro v
    by_cases hv : v ∈ X.T
    · haveI := h.fin.nontriv v
      obtain ⟨y, hy⟩ := exists_ne (0 : Rf.Pi v)
      have hy' : y ∈ (GlobalTheory.WeilM.SB _).map (Rf.p' v) := by rw [h.fin.onto' v]; trivial
      obtain ⟨φv, h1, h2⟩ := hy'
      exact ⟨φv, h1, h2 ▸ hy, fun hn => absurd hv hn⟩
    · exact ⟨G.M'.vac v, (h.triple.geo.hM'.vac v).1, hs0 v hv, fun _ => rfl⟩
  choose φ hφSB hφ0 hφvac using hloc
  have hφev : ∀ᶠ v in Filter.cofinite, φ v = G.M'.vac v :=
    Filter.eventually_cofinite.2 (hXT.subset fun v hv => by by_contra hn; exact hv (hφvac v hn))
  have hΦ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ algD G.M' B.ψ B.emb :=
    Submodule.subset_span ⟨f, φ, hf, hφSB, hφev, rfl⟩
  obtain ⟨l₀, hl₀⟩ := Module.Projective.exists_dual_eq_one ℂ hx
  choose l hl using fun v => Module.Projective.exists_dual_eq_one ℂ (hφ0 v)
  have hls : ∀ v ∉ X.T, l v (s v) = 1 := fun v hv => by
    have := hl v
    rwa [hφvac v hv] at this
  have hadm : {v | l v (s v) ≠ 1}.Finite := hXT.subset fun v hv => by by_contra hn; exact hv (hls v hn)
  obtain ⟨Λ, hΛ⟩ := pureT_sep s (fun v => l v) hadm
  let LL : R.Pi ⊗[ℂ] RTens s →ₗ[ℂ] ℂ := TensorProduct.lift ((LinearMap.mul ℂ ℂ).compl₁₂ l₀ Λ)
  have hLL : ∀ x y, LL (x ⊗ₜ y) = l₀ x * Λ y := fun x y => by simp [LL]
  refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ, hΦ, ?_⟩
  rintro ⟨T, hT, m, m', fs, φs, fs', φs', hfam, hfam', h0, hΦe, htens⟩
  let LT : (⨂[ℂ] v : T, Rf.Pi v) →ₗ[ℂ] ℂ := PiTensorProduct.dualDistrib (⨂ₜ[ℂ] v : T, l v)
  let Ltot : R.Pi ⊗[ℂ] (⨂[ℂ] v : T, Rf.Pi v) →ₗ[ℂ] ℂ := TensorProduct.lift ((LinearMap.mul ℂ ℂ).compl₁₂ l₀ LT)
  have hLtot : ∀ x y, Ltot (x ⊗ₜ y) = l₀ x * LT y := fun x y => by simp [Ltot]
  have key : ∀ g : ∀ v, Rf.Pi v, (∀ v ∉ T, g v = s v) →
      Λ (pureT s g) = LT (PiTensorProduct.tprod ℂ fun v : T => g v) := by
    intro g hg
    have hr : Formalism.MainNotions.KudlaSiegelWeil.Restr s g := T.finite_toSet.subset fun v hv => by by_contra hn; exact hv (hg v hn)
    rw [hΛ g hr]
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := T) (fun v hv => by
      by_contra hn
      exact hv (by show l v (g v) = 1; rw [hg v hn]; exact hls v fun h' => hn (hT h')))]
    simp only [LT, PiTensorProduct.dualDistrib_apply]
    exact (Finset.prod_coe_sort T fun v => l v (g v)).symm
  have hP : ∀ i, LL (q (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (fs i) (φs i))) =
      Ltot (R.p (fs i) ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ fun v : T => Rf.p v (φs i v)) := by
    intro i
    have ev : ∀ᶠ v in Filter.cofinite, φs i v = G.M.vac v :=
      Filter.eventually_cofinite.2 (T.finite_toSet.subset fun v hv => by by_contra hn; exact hv ((hfam i).2.2 v hn))
    rw [hq _ _ (hfam i).2.1 ev, hLL, hLtot]
    congr 1
    exact key _ fun v hv => by rw [(hfam i).2.2 v hv]; exact hsph v fun h' => hv (hT h')
  have hP' : ∀ j, LL (q' (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (fs' j) (φs' j))) =
      Ltot (R.p' (fs' j) ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ fun v : T => Rf.p' v (φs' j v)) := by
    intro j
    have ev : ∀ᶠ v in Filter.cofinite, φs' j v = G.M'.vac v :=
      Filter.eventually_cofinite.2 (T.finite_toSet.subset fun v hv => by by_contra hn; exact hv ((hfam' j).2.2 v hn))
    rw [hq' _ _ (hfam' j).2.1 ev, hLL, hLtot]
    congr 1
    exact key _ fun v hv => by rw [(hfam' j).2.2 v hv]
  have h1 : LL (q' (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ)) = 1 := by
    rw [hq' _ _ hφSB hφev, hLL, hfx, hl₀, one_mul]
    have hr : Formalism.MainNotions.KudlaSiegelWeil.Restr s (fun v => Rf.p' v (φ v)) :=
      hXT.subset fun v hv => by by_contra hn; exact hv (congrArg (Rf.p' v) (hφvac v hn))
    rw [hΛ _ hr]
    exact finprod_eq_one_of_forall_eq_one fun v => hl v
  have h2 : LL (q' (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ)) =
      Ltot (∑ j, R.p' (fs' j) ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ fun v : T => Rf.p' v (φs' j v)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hΦe, map_sum, map_sum, map_sum]
    exact Finset.sum_congr rfl fun j _ => hP' j
  have h3 : Ltot (∑ i, R.p (fs i) ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ fun v : T => Rf.p v (φs i v)) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← Finset.sum_congr rfl fun i _ => hP i, ← map_sum, ← map_sum, ← h0, map_zero, map_zero]
  rw [htens, ← h2, h1] at h3
  exact one_ne_zero h3

end GlobalTheory.SquareAgree
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAlgebraicDatumNotMatchedZeroByLocalMapsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algebraicDatum_not_matched_zero_by_localMaps : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf →
    ∃ Φ ∈ GlobalTheory.SquareAgree.algD G.M' B.ψ B.emb, ¬ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch B G X R Rf 0 Φ := by
  first | exact @GlobalTheory.SquareAgree.exists_algD_not_polMatch_zero | exact GlobalTheory.SquareAgree.exists_algD_not_polMatch_zero | (intros; apply GlobalTheory.SquareAgree.exists_algD_not_polMatch_zero <;> assumption)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.KerDSub

open Filter GlobalTheory.WeilM GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}

theorem polMatch_mem_algD (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a') {Φ Φ'}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch B G X R Rf Φ Φ') : Φ' ∈ algD G.M' B.ψ B.emb := by
  obtain ⟨T, -, m, m', f, φ, f', φ', -, hf', -, rfl, -⟩ := h
  refine Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨f' j, φ' j, (hf' j).1, (hf' j).2.1, ?_, rfl⟩
  exact Filter.eventually_cofinite.mpr (T.finite_toSet.subset fun v hv => by
    by_contra h'
    exact hv ((hf' j).2.2 v h'))

theorem polMatch_zero_pure (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a')
    (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a'))) (hf : f ∈ G.M'.Pol B.ψ B.emb)
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin a' × Fin (a + a') → Fv F v) → ℂ) (hφ : ∀ v, φ v ∈ SB _)
    (hv : ∀ᶠ v in cofinite, φ v = G.M'.vac v) (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)))
    (hz : ∀ T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), S ⊆ T →
      R.p' f ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => Rf.p' v (φ v)) = 0) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch B G X R Rf 0 (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) := by
  classical
  have hfin := Filter.eventually_cofinite.mp hv
  refine ⟨X.T ∪ S ∪ hfin.toFinset, fun x hx => Finset.mem_union_left _ (Finset.mem_union_left _ hx), 0, 1,
    Fin.elim0, Fin.elim0, fun _ => f, fun _ => φ, fun i => i.elim0, fun _ => ⟨hf, hφ, fun v hv' => ?_⟩, ?_, ?_, ?_⟩
  · by_contra h'
    exact hv' (Finset.mem_union_right _ (hfin.mem_toFinset.mpr h'))
  · simp
  · simp
  · rw [Finset.univ_eq_empty, Finset.sum_empty, Fin.sum_univ_one, hz _ fun x hx =>
      Finset.mem_union_left _ (Finset.mem_union_right _ hx)]

theorem polMatch_kInf (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a') (hMt : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf)
    (k : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J) (hk : k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ G.W B.emb) (Φ Φ')
    (hPM : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch B G X R Rf Φ Φ') :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch B G X R Rf (om (1, k) Φ) (om' (1, k) Φ') := by
  obtain ⟨A, hA⟩ := GlobalTheory.T.exists_archOperator_compact_unitaryW F E σ B a (a + a') G.V G.W G.M om _ _ hMt.triple.base hMt.triple.geo.hM hMt.triple.weil k hk
  obtain ⟨A', hA'⟩ := GlobalTheory.T.exists_archOperator_compact_unitaryW F E σ B a' (a + a') G.V' G.W G.M' om' _ _ hMt.triple.base hMt.triple.geo.hM'
    hMt.triple.weil' k hk
  have hpure : ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M.vac v) →
      om (1, k) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (A f) φ := fun f φ h1 h2 =>
    hA f _ (GlobalTheory.T.restricted_finprod_pure_tensor_adelic_schwartz F _ φ h1 ((h2.and hMt.triple.geo.hM.std).mono fun v h => h.1.trans h.2) f)
  have hpure' : ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M'.vac v) →
      om' (1, k) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (A' f) φ := fun f φ h1 h2 =>
    hA' f _ (GlobalTheory.T.restricted_finprod_pure_tensor_adelic_schwartz F _ φ h1 ((h2.and hMt.triple.geo.hM'.std).mono fun v h => h.1.trans h.2) f)
  obtain ⟨T, hT, m, m', f, φ, f', φ', hf, hf', rfl, rfl, heq⟩ := hPM
  have hR := hMt.real
  set P := G.M.Pol B.ψ B.emb with hP
  let pP : P →ₗ[ℂ] R.Pi := R.p ∘ₗ P.subtype
  have hsurj : Function.Surjective pP := by
    rw [← LinearMap.range_eq_top, LinearMap.range_comp, Submodule.range_subtype]
    exact hR.quot.onto
  let g : P →ₗ[ℂ] R.Pi := R.p ∘ₗ A ∘ₗ P.subtype
  have hker : LinearMap.ker pP ≤ LinearMap.ker g := by
    intro x hx
    simp only [LinearMap.mem_ker] at hx ⊢
    have := hR.cpt k hk x.1 x.2 0 (zero_mem _) (A x.1) (A' 0) (hA x.1) (hA' 0)
      (by simpa [pP] using hx)
    simpa [g] using this
  let L : R.Pi →ₗ[ℂ] R.Pi :=
    (LinearMap.ker pP).liftQ g hker ∘ₗ (pP.quotKerEquivOfSurjective hsurj).symm.toLinearMap
  have hL : ∀ x ∈ P, L (R.p x) = R.p (A x) := by
    intro x hx
    have e : (pP.quotKerEquivOfSurjective hsurj).symm (R.p x) = Submodule.Quotient.mk ⟨x, hx⟩ := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    simp only [L, LinearMap.comp_apply, LinearEquiv.coe_coe, e, Submodule.liftQ_apply]
    rfl
  have hL' : ∀ x ∈ G.M'.Pol B.ψ B.emb, L (R.p' x) = R.p' (A' x) := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := (Submodule.eq_top_iff'.mp hR.quot.onto (R.p' x))
    rw [← hyx, hL y hy]
    exact hR.cpt k hk y hy x hx (A y) (A' x) (hA y) (hA' x) hyx
  have hcof : ∀ {κ : Type} (ψs vac : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ), (∀ v ∉ T, ψs v = vac v) →
      ∀ᶠ v in cofinite, ψs v = vac v := fun ψs vac h =>
    Filter.eventually_cofinite.mpr (T.finite_toSet.subset fun v hv => by
      by_contra h'
      exact hv (h v h'))
  refine ⟨T, hT, m, m', fun i => A (f i), φ, fun j => A' (f' j), φ',
    fun i => ⟨GlobalTheory.T.polynomialFockSpace_stable_archimedeanMaximalCompact F E σ B a (a + a') G.V G.W G.M om _ _ hMt.triple.base hMt.triple.geo.hM hMt.triple.weil k hk
      (f i) (hf i).1 (A (f i)) (hA (f i)), (hf i).2.1, (hf i).2.2⟩,
    fun j => ⟨GlobalTheory.T.polynomialFockSpace_stable_archimedeanMaximalCompact F E σ B a' (a + a') G.V' G.W G.M' om' _ _ hMt.triple.base hMt.triple.geo.hM' hMt.triple.weil' k hk
      (f' j) (hf' j).1 (A' (f' j)) (hA' (f' j)), (hf' j).2.1, (hf' j).2.2⟩, ?_, ?_, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => hpure (f i) (φ i) (hf i).2.1 (hcof _ _ (hf i).2.2)
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => hpure' (f' j) (φ' j) (hf' j).2.1 (hcof _ _ (hf' j).2.2)
  · have := congrArg (LinearMap.rTensor _ L) heq
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.rTensor_tmul] at this
    simpa only [hL _ (hf _).1, hL' _ (hf' _).1] using this

theorem pure_sub {κ : Type} [Fintype κ] (f g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f - g) φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ - GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ := by
  funext x
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, sub_mul]

end GlobalTheory.KerDSub
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HorizontalThetaLevelFifth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ThetaLiftTypeTh

theorem sigOK_vert {D : D7} {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (G : GlobalTheory.Grid.GridPre R)
    (hG : G.Is) {i j : ℕ} (hi : i ≤ D.R.m) (hj : j ≤ D.R.m) : (G.V i j).V.SigOK := by
  cases i with
  | succ i => exact (hG.spaces.vert i j hi hj).sigOK
  | zero =>
    show (GlobalTheory.Grid.row0 R j).V.SigOK
    cases j with
    | zero => exact D.sp.Y_sig 0
    | succ j =>
      simp only [GlobalTheory.Grid.row0]
      split_ifs
      · exact D.sp.Y_sig _
      · exact D.sp.X'_sig

end GlobalTheory.ThetaLiftTypeTh
end
end
