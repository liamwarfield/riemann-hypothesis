module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.LatVac

variable {F : Type} [Field F] [NumberField F]

def liftV (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) : Fv F v →ₗ[F] AF F :=
  (LinearMap.inr F (Ainf F) (Af F)).comp (GlobalTheory.AdelicU.singleFin v)

def psiAt (ψ : AddChar (AF F) ℂ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) : AddChar (Fv F v) ℂ :=
  ψ.compAddMonoidHom (liftV v).toAddMonoidHom

theorem psiAt_apply (ψ : AddChar (AF F) ℂ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (x : Fv F v) :
    psiAt ψ v x = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.psiLoc ψ v x := rfl

def locCo {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux B κ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) : W →+ (κ → Fv F v) × (κ → Fv F v) where
  toFun w := (fun k => GlobalTheory.AdelicU.evFin F v ((co.e w).1 k), fun k => GlobalTheory.AdelicU.evFin F v ((co.e w).2 k))
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp

theorem evFin_liftV (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (a : Fv F v) : GlobalTheory.AdelicU.evFin F v (liftV v a) = a :=
  GlobalTheory.AdelicU.evalV_singleFin_self v a

theorem at_liftV (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (a : Fv F v) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (liftV v a) := by
  intro u hu
  refine Prod.ext (by change u.1 * 0 = 0; exact mul_zero _) ?_
  change u.2 * GlobalTheory.AdelicU.singleFin v a = 0
  apply GlobalTheory.AdelicU.af_ext
  intro w
  rw [map_mul, map_zero]
  by_cases hw : w = v
  · subst hw
    have : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w u.2 = 0 := hu
    rw [this, zero_mul]
  · rw [GlobalTheory.AdelicU.evalV_singleFin_ne hw, mul_zero]

end GlobalTheory.LatVac

namespace GlobalTheory.LatVac

theorem symp_smul_smul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n d : ℕ} (JA : Matrix (Fin n) (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (JB : Matrix (Fin d) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (ξ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (a a' : AF F)
    (x y : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :
    GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) ξ JA JB (a • x) (a' • y) =
      a * a' * GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) ξ JA JB x y := by
  unfold GlobalTheory.WeilM.symp GlobalTheory.WeilM.hTens
  have h : ξ * ∑ i, ∑ j, ∑ k, ∑ l, (a • x) i j * JA i k * JB j l * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) ((a' • y) k l)
      = (a * a') • (ξ * ∑ i, ∑ j, ∑ k, ∑ l, x i j * JA i k * JB j l * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (y k l)) := by
    simp only [Matrix.smul_apply, map_smul, Finset.mul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    simp only [Algebra.smul_def, map_mul]
    ring
  rw [h, map_smul, smul_eq_mul]

end GlobalTheory.LatVac

namespace GlobalTheory.LatVac

theorem latAtV_at_stable : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)),
    (∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) γ) ∧
    ∀ a ∈ v.adicCompletionIntegers F, ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v,
      GlobalTheory.LatVac.liftV v a • γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v := by
  intro F E _ _ _ _ _ n d X Y v
  constructor
  · intro γ hγ
    induction hγ using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, -, x, -, y, -, rfl⟩ := hz
      intro u hu
      rw [smul_smul, ← smul_eq_mul u a, ha u hu, zero_smul]
    | zero => intro u _; exact smul_zero u
    | add x y _ _ hx hy => intro u hu; rw [smul_add, hx u hu, hy u hu, add_zero]
    | neg x _ hx => intro u hu; rw [smul_neg, hx u hu, neg_zero]
  · intro a ha γ hγ
    induction hγ using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a', ha', hv, x, hx, y, hy, rfl⟩ := hz
      rw [smul_smul]
      refine AddSubgroup.subset_closure ⟨GlobalTheory.LatVac.liftV v a • a', ?_, ?_, x, hx, y, hy, rfl⟩
      · intro u hu
        rw [smul_eq_mul, smul_eq_mul, mul_left_comm, ← smul_eq_mul u a', ha' u hu, mul_zero]
      · rw [smul_eq_mul, map_mul, evFin_liftV]
        exact mul_mem ha hv
    | zero => rw [smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | neg x _ hx => rw [smul_neg]; exact neg_mem hx

end GlobalTheory.LatVac
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (incM)

namespace GlobalTheory.WeilSchrodinger

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem symp_transpose (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α β E) :
    GlobalTheory.WeilM.symp c ξ JB JA xᵀ yᵀ = GlobalTheory.WeilM.symp c ξ JA JB x y := by
  unfold GlobalTheory.WeilM.symp GlobalTheory.WeilM.hTens
  congr 2
  simp only [Matrix.transpose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

variable [Invertible (2 : R)]

def transD {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {κ : Type} [Fintype κ]
    (d : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JA JB) κ) : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JB JA) κ where
  e := (Matrix.transposeLinearEquiv β α R E).trans d.e
  form w w' := by
    rw [← symp_transpose c ξ JB JA w w', d.form]
    rfl

variable {c}

theorem transD_e {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {κ : Type} [Fintype κ]
    (d : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JA JB) κ) (x : Matrix α β E) : (transD c d).e xᵀ = d.e x := by
  simp [transD]

theorem transD_rho {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {κ : Type} [Fintype κ]
    (d : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JA JB) κ) (ψ : AddChar R ℂ) (w : Matrix β α E) :
    (transD c d).rho ψ w = d.rho ψ wᵀ := by
  simp [GlobalTheory.WeilM.Darboux.rho, transD]

variable [TopologicalSpace R] [TopologicalSpace E] {C : GlobalTheory.WeilM.TestClass R} {ψ : AddChar R ℂ} {ξ : E}
  {JA : Matrix α α E} {JB : Matrix β β E} {κ : Type} [Fintype κ] {d : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JA JB) κ}
  {om : GlobalTheory.WeilM.UG c JA × GlobalTheory.WeilM.UG c JB →* Module.End ℂ ((κ → R) → ℂ)}

theorem isUSplitting_inr (h : GlobalTheory.WeilM.IsUSplitting C ψ d (GlobalTheory.WeilM.actAB c) om) :
    GlobalTheory.WeilM.IsUSplitting C ψ d (GlobalTheory.WeilM.actB c) (om.comp (MonoidHom.inr _ _)) := by
  refine ⟨⟨fun g φ hφ => h.pres _ φ hφ, fun g w φ hφ => ?_, fun g l hl => h.adm _ l hl⟩, h.unit.comp _,
    h.cont.comp (f := MonoidHom.inr _ _) (continuous_const.prodMk continuous_id)⟩
  have := h.impl (1, g) w φ hφ
  simpa [GlobalTheory.WeilM.actAB, GlobalTheory.WeilM.actB] using this

theorem isUSplitting_inl (h : GlobalTheory.WeilM.IsUSplitting C ψ d (GlobalTheory.WeilM.actAB c) om) :
    GlobalTheory.WeilM.IsUSplitting C ψ (transD c d) (GlobalTheory.WeilM.actB c) (om.comp (MonoidHom.inl _ _)) := by
  refine ⟨⟨fun g φ hφ => h.pres _ φ hφ, fun g w φ hφ => ?_, fun g l hl => h.adm _ l hl⟩, h.unit.comp _,
    h.cont.comp (f := MonoidHom.inl _ _) (continuous_id.prodMk continuous_const)⟩
  have := h.impl (g, 1) wᵀ φ hφ
  simp only [MonoidHom.comp_apply, MonoidHom.inl_apply, transD_rho]
  convert this using 2
  simp [GlobalTheory.WeilM.actAB, GlobalTheory.WeilM.actB, Matrix.transpose_mul]

end Gen

section Theta

variable (F : Type) [Field F] [NumberField F] [Invertible (2 : AF F)]

def thetaTr {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ]
    (d : GlobalTheory.WeilM.Darboux B κ) (ψ : AddChar (AF F) ℂ) (Φ : (κ → AF F) → ℂ) : W → ℂ :=
  fun w => GlobalTheory.WeilM.thetaSum F (d.rho ψ w Φ)

end Theta

section Transport

def IsTransport {D : D7} (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {ξ : AE D}
    {JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E} {JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E}
    {κ : Type} [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ)
    (ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ))
    (om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ)) :
    Prop :=
  ∀ (a : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA))
    (b : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB)) (g : GA D S) (h : GA D T),
    mt T h = a.1.1 → mt S g = (b⁻¹).1.1ᵀ →
    ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, om (a, b) Φ ∈ GlobalTheory.WeilM.schA D.host.F κ ∧
      thetaTr D.host.F co ψ (om (a, b) Φ) = ω (g, h) (thetaTr D.host.F co ψ Φ)

end Transport

end GlobalTheory.WeilSchrodinger

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
noncomputable section

namespace GlobalTheory.ThK.SquareIntegrability

open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def toGAd {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {c : E} (hc : c ≠ 0) :
    UA σ J ≃* GlobalTheory.AdelicU.GAd σ (c • J.map σ) :=
  MulEquiv.subgroupCongr (GlobalTheory.SiegelSet.ug_eq_hr (J := J) hσ hc)

end GlobalTheory.ThK.SquareIntegrability
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped Classical

namespace GlobalTheory.PureFactor

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem mulSupport_finite (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ)
    (hφ : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (x : κ → AF F) : (Function.mulSupport fun v => φ v fun i => evFin F v (x i)).Finite := by
  have hx : ∀ᶠ v in Filter.cofinite, ∀ i, evFin F v (x i) ∈ v.adicCompletionIntegers F := by
    rw [Filter.eventually_all]
    intro i
    exact (x i).2.2
  refine Set.Finite.subset (Filter.eventually_cofinite.1 (hφ.and hx)) ?_
  intro v hv hv'
  apply hv
  obtain ⟨h1, h2⟩ := hv'
  simp only [h1]
  rw [Set.indicator_of_mem (show (fun i => evFin F v (x i)) ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from h2)]
  rfl

theorem update_eventually (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ) (v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (g : (κ → Fv F v₁) → ℂ)
    (hφ : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) :
    ∀ᶠ v in Filter.cofinite, Function.update φ v₁ g v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
  filter_upwards [hφ, Filter.eventually_cofinite_ne v₁] with v hv hne
  rw [Function.update_of_ne hne]; exact hv

theorem finprod_update (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ) (v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (g : (κ → Fv F v₁) → ℂ)
    (hφ : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (x : κ → AF F) :
    (∏ᶠ v, Function.update φ v₁ g v fun i => evFin F v (x i)) =
      g (fun i => evFin F v₁ (x i)) * ∏ᶠ v, Function.update φ v₁ (fun _ => 1) v fun i => evFin F v (x i) := by
  rw [← mul_finprod_cond_ne v₁ (mulSupport_finite _ (update_eventually φ v₁ g hφ) x),
    ← mul_finprod_cond_ne v₁ (mulSupport_finite _ (update_eventually φ v₁ (fun _ => 1) hφ) x)]
  simp only [Function.update_self, one_mul]
  congr 1
  refine finprod_congr fun v => finprod_congr fun hv => ?_
  rw [Function.update_of_ne hv, Function.update_of_ne hv]

theorem comp_add_of_at (v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (z : κ → AF F) (hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v₁) z) (i : κ) :
    (z i).1 = 0 ∧ ∀ v, v ≠ v₁ → evFin F v (z i) = 0 := by
  set u : AF F := 1 - GlobalTheory.EmbChart.atPlace v₁ 1 with hu
  have h0 : evFin F v₁ u = 0 := by
    rw [hu, map_sub, map_one, GlobalTheory.EmbChart.evFin_atPlace, sub_self]
  have hzi : u * z i = 0 := by
    have := congrFun (hz u h0) i
    simpa using this
  refine ⟨?_, fun v hv => ?_⟩
  · have h1 : (u * z i).1 = (z i).1 := by
      have : u.1 = 1 := by
        rw [hu]
        show (1 : Ainf F) - (0 : Ainf F) = 1
        exact sub_zero 1
      show u.1 * (z i).1 = (z i).1
      rw [this, one_mul]
    rw [← h1, hzi]; rfl
  · have h2 : evFin F v u = 1 := by
      rw [hu, map_sub, map_one]
      have : evFin F v (GlobalTheory.EmbChart.atPlace v₁ 1) = 0 := evalV_singleFin_ne hv 1
      rw [this, sub_zero]
    have := congrArg (evFin F v) hzi
    rwa [map_mul, h2, one_mul, map_zero] at this

end GlobalTheory.PureFactor


open GlobalTheory.PureFactor in
theorem GlobalTheory.PureFactor.exists_rest_factor : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ),
    (∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    ∃ r : (κ → AF F) → ℂ, (∀ x z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v₁) z → r (x + z) = r x) ∧
      ∀ ψ₀ : (κ → Fv F v₁) → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v₁) ψ₀ r = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (Function.update φ v₁ ψ₀) := by
  intro F _ _ κ _ v₁ f φ hφ
  refine ⟨fun x => f (fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (x i)) *
    ∏ᶠ v, Function.update φ v₁ (fun _ => 1) v fun i => evFin F v (x i), ?_, ?_⟩
  · intro x z hz
    have hI : (fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F ((x + z) i)) = fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (x i) := by
      funext i
      have h := (comp_add_of_at v₁ z hz i).1
      show (InfiniteAdeleRing.ringEquiv_mixedSpace F) ((x i).1 + (z i).1) = (InfiniteAdeleRing.ringEquiv_mixedSpace F) (x i).1
      rw [h, add_zero]
    simp only
    rw [hI]
    congr 1
    refine finprod_congr fun v => ?_
    by_cases hv : v = v₁
    · subst hv; simp only [Function.update_self]
    · rw [Function.update_of_ne hv]
      congr 1
      funext i
      rw [Pi.add_apply, map_add (f := _), (comp_add_of_at v₁ z hz i).2 v hv, add_zero]
  · intro ψ₀
    funext x
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
    rw [finprod_update φ v₁ ψ₀ hφ x]
    ring
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_factor_pureTensor_component_at_place : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ),
    (∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    ∃ r : (κ → AF F) → ℂ, (∀ x z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v₁) z → r (x + z) = r x) ∧
      ∀ ψ₀ : (κ → Fv F v₁) → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v₁) ψ₀ r = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (Function.update φ v₁ ψ₀) := by
  first | exact @GlobalTheory.PureFactor.exists_rest_factor | exact GlobalTheory.PureFactor.exists_rest_factor | (intros; apply GlobalTheory.PureFactor.exists_rest_factor <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistContinuousInvolutionIntegralProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistContinuousInvolutionIntegralProperties
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

namespace GlobalTheory.BCT.ThBasic

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cj_mem_integers (hU : Unr E) (w : Pl E) (x : w.adicCompletion E) (hx : x ∈ Ov E w) : cj w x ∈ Ov E w := by
  have h := (GlobalTheory.T.placeConjugation_properties_cmField E hU w).2.2.1 x
  change Valued.v (cj w x) ≤ 1
  rw [h]; exact hx

theorem thL_thL (hU : Unr E) (n : ℕ) (w : Pl E) (g : GLw n w) : thL n w (thL n w g) = g := by
  unfold thL
  split_ifs
  · rfl
  · exact GlobalTheory.ThetaPull.thetaGL_thetaGL _ (GlobalTheory.T.placeConjugation_properties_cmField E hU w).2.1 g

theorem continuous_thL (hU : Unr E) (n : ℕ) (w : Pl E) : Continuous (thL n w) := by
  unfold thL
  split_ifs
  · exact continuous_id
  · exact GlobalTheory.ThetaPull.continuous_thetaGL _ (GlobalTheory.T.placeConjugation_properties_cmField E hU w).1

theorem thL_mem_KGL (hU : Unr E) (n : ℕ) (w : Pl E) (k : GLw n w) (hk : k ∈ GlobalTheory.LFun.KGL w (n := n)) :
    thL n w k ∈ GlobalTheory.LFun.KGL w (n := n) := by
  unfold thL
  split_ifs
  · exact hk
  · obtain ⟨k', rfl⟩ := hk
    let c' : Ov E w →+* Ov E w := (cj w).restrict (Ov E w) (Ov E w) (cj_mem_integers hU w)
    refine ⟨thetaGL n c' k', ?_⟩
    exact GlobalTheory.ThetaPull.map_thetaGL (Ov E w).subtype c' (cj w) (fun x => rfl) k'

theorem nrmL_twist (hU : Unr E) (n : ℕ) (w : Pl E) (g y : GLw n w) :
    nrmL n w (g⁻¹ * y * thL n w g) = g⁻¹ * nrmL n w y * g := by
  unfold nrmL
  have h2 := thL_thL hU n w g
  unfold thL at h2 ⊢
  split_ifs with hs
  · simp [hs] at *
  · simp only [hs, if_false] at h2 ⊢
    rw [map_mul, map_mul, map_inv, h2]
    group

theorem isClosed_UL (hU : Unr E) (n : ℕ) (w : Pl E) : IsClosed (UL n w : Set (GLw n w)) := by
  unfold UL
  split_ifs
  · exact isClosed_univ
  · have hc := (GlobalTheory.T.placeConjugation_properties_cmField E hU w).1
    have : Continuous fun g : GLw n w => cT (cj w) (g : Matrix (Fin n) (Fin n) _) * 1 * (g : Matrix (Fin n) (Fin n) _) := by
      refine Continuous.mul (Continuous.mul ?_ continuous_const) Units.continuous_val
      exact continuous_matrix fun i j => hc.comp (Units.continuous_val.matrix_elem _ _)
    exact isClosed_singleton.preimage this

theorem charpoly_nrmL (hU : Unr E) (n : ℕ) (w : Pl E) (δ : GL (Fin n) E) :
    (nrmL n w (locEl n w δ)).val.charpoly = atPl w (δ * thE E n δ).val.charpoly := by
  unfold nrmL locEl
  split_ifs with hs
  · exact (Matrix.charpoly_map _ _)
  · have hm : thetaGL n (cj w) (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ) =
        GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) (thE E n δ) :=
      (GlobalTheory.ThetaPull.map_thetaGL _ _ _ (fun x => ((GlobalTheory.T.placeConjugation_properties_cmField E hU w).2.2.2.1 hs).1 x |>.symm) δ).symm
    rw [hm, ← map_mul]
    exact (Matrix.charpoly_map _ _)

theorem cLoc_mem_UL (hU : Unr E) (n : ℕ) (w : Pl E) (x : UA E n) : cLoc w x ∈ UL n w := by
  unfold UL
  split_ifs with hs
  · exact Subgroup.mem_top _
  · have hp := ((GlobalTheory.T.placeConjugation_properties_cmField E hU w).2.2.2.1 hs).2.2.1
    have hx := x.2
    change cT (conjAd E) (x.1 : Matrix (Fin n) (Fin n) (Ad E)) * 1 * (x.1 : Matrix (Fin n) (Fin n) (Ad E)) = 1 at hx
    change cT (cj w) ((cLoc w x : GLw n w) : Matrix (Fin n) (Fin n) _) * 1 * ((cLoc w x : GLw n w) : Matrix (Fin n) (Fin n) _) = 1
    have := congrArg (((pLoc E w).comp (pFin E)).mapMatrix) hx
    rw [map_one, map_mul, map_mul, map_one] at this
    convert this using 3
    · refine Matrix.ext fun i j => ?_
      show cj w (pLoc E w (pFin E ((x.1 : Matrix (Fin n) (Fin n) (Ad E)) j i))) =
        pLoc E w (pFin E (conjAd E ((x.1 : Matrix (Fin n) (Fin n) (Ad E)) j i)))
      rw [← hp]
      rfl
    · rfl

theorem twist_basic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E), Continuous (thL n w) ∧ (∀ g, thL n w (thL n w g) = g) ∧ (∀ k ∈ GlobalTheory.LFun.KGL w (n := n), thL n w k ∈ GlobalTheory.LFun.KGL w (n := n)) ∧ (∀ g y, nrmL n w (g⁻¹ * y * thL n w g) = g⁻¹ * nrmL n w y * g) ∧ IsOpen (GlobalTheory.LFun.KGL w (n := n) : Set (GLw n w)) ∧ IsCompact (GlobalTheory.LFun.KGL w (n := n) : Set (GLw n w)) ∧ IsOpen (KL n w : Set (UL n w)) ∧ IsCompact (KL n w : Set (UL n w)) ∧ (∀ δ : GL (Fin n) E, (nrmL n w (locEl n w δ)).val.charpoly = atPl w (δ * thE E n δ).val.charpoly) ∧ ∀ x ∈ locU n w, cLoc w x ∈ UL n w := by
  intro E _ _ _ hU n w
  have hK := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n
  refine ⟨continuous_thL hU n w, thL_thL hU n w, thL_mem_KGL hU n w, nrmL_twist hU n w, hK.1, hK.2, ?_, ?_,
    charpoly_nrmL hU n w, fun x _ => cLoc_mem_UL hU n w x⟩
  · rw [KL, Subgroup.coe_subgroupOf]
    exact hK.1.preimage continuous_subtype_val
  · rw [KL, Subgroup.coe_subgroupOf]
    exact (isClosed_UL hU n w).isClosedEmbedding_subtypeVal.isCompact_preimage hK.2

end GlobalTheory.BCT.ThBasic
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistContinuousInvolutionIntegralPropertiesStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localTwist_continuous_involution_integral_properties : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E), Continuous (thL n w) ∧ (∀ g, thL n w (thL n w g) = g) ∧ (∀ k ∈ GlobalTheory.LFun.KGL w (n := n), thL n w k ∈ GlobalTheory.LFun.KGL w (n := n)) ∧ (∀ g y, nrmL n w (g⁻¹ * y * thL n w g) = g⁻¹ * nrmL n w y * g) ∧ IsOpen (GlobalTheory.LFun.KGL w (n := n) : Set (GLw n w)) ∧ IsCompact (GlobalTheory.LFun.KGL w (n := n) : Set (GLw n w)) ∧ IsOpen (KL n w : Set (UL n w)) ∧ IsCompact (KL n w : Set (UL n w)) ∧ (∀ δ : GL (Fin n) E, (nrmL n w (locEl n w δ)).val.charpoly = atPl w (δ * thE E n δ).val.charpoly) ∧ ∀ x ∈ locU n w, cLoc w x ∈ UL n w := by
  first | exact @GlobalTheory.BCT.ThBasic.twist_basic | exact GlobalTheory.BCT.ThBasic.twist_basic | (intros; apply GlobalTheory.BCT.ThBasic.twist_basic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairingStdP
noncomputable section

open scoped SchwartzMap

namespace GlobalTheory.ArchUniq

section Real

variable {V V₁ : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup V₁] [NormedSpace ℝ V₁]

def schrF (P : V → V → ℝ) (w : V × V) (f : V → ℂ) : V → ℂ :=
  fun y => Complex.exp (-(2 * Real.pi * Complex.I) * ((P y w.2 + P w.1 w.2 / 2 : ℝ) : ℂ)) * f (y + w.1)

def omega (P : V → V → ℝ) (w w' : V × V) : ℝ := P w.1 w'.2 - P w'.1 w.2

structure IsPairing (P : V → V → ℝ) : Prop where
  addL : ∀ x x' y, P (x + x') y = P x y + P x' y
  addR : ∀ x y y', P x (y + y') = P x y + P x y'
  smulL : ∀ (c : ℝ) x y, P (c • x) y = c * P x y
  smulR : ∀ (c : ℝ) x y, P x (c • y) = c * P x y
  nondegL : ∀ x, (∀ y, P x y = 0) → x = 0
  nondegR : ∀ y, (∀ x, P x y = 0) → y = 0

structure Setup (P : V → V → ℝ) (P₁ : V₁ → V₁ → ℝ) (j : V₁ × V₁ → V × V) (L : Set (V × V)) : Prop where
  pair : IsPairing P
  pair₁ : IsPairing P₁
  add : ∀ w w', j (w + w') = j w + j w'
  smul : ∀ (c : ℝ) w, j (c • w) = c • j w
  symp : ∀ w w', omega P (j w) (j w') = omega P₁ w w'
  iso : ∀ l ∈ L, ∀ l' ∈ L, omega P l l' = 0
  orth : ∀ l ∈ L, ∀ w, omega P l (j w) = 0
  max : ∀ v, (∀ l ∈ L, omega P v l = 0) → (∀ w, omega P v (j w) = 0) → v ∈ L

def stdP (P₁ : V₁ → V₁ → ℝ) (k : ℕ) (x y : V₁ × (Fin k → ℝ)) : ℝ := P₁ x.1 y.1 + ∑ i, x.2 i * y.2 i

def jStd (k : ℕ) (w : V₁ × V₁) : (V₁ × (Fin k → ℝ)) × (V₁ × (Fin k → ℝ)) := ((w.1, 0), (w.2, 0))


variable (V₁) in
def LStd (k : ℕ) : Set ((V₁ × (Fin k → ℝ)) × (V₁ × (Fin k → ℝ))) :=
  {l | ∃ b : Fin k → ℝ, l = ((0, 0), (0, b))}

theorem isPairing_stdP {P₁ : V₁ → V₁ → ℝ} (h : IsPairing P₁) (k : ℕ) : IsPairing (stdP P₁ k) := by
  exact {
    addL x x' y := by
      simp only [stdP, Prod.fst_add, Prod.snd_add, h.addL, Pi.add_apply, add_mul, Finset.sum_add_distrib]; ring
    addR x y y' := by
      simp only [stdP, Prod.fst_add, Prod.snd_add, h.addR, Pi.add_apply, mul_add, Finset.sum_add_distrib]; ring
    smulL c x y := by
      simp only [stdP, Prod.smul_fst, Prod.smul_snd, h.smulL, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
      ring
    smulR c x y := by
      simp only [stdP, Prod.smul_fst, Prod.smul_snd, h.smulR, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c,
        ← Finset.mul_sum]
      ring
    nondegL x hx := by
      have h1 : x.1 = 0 := h.nondegL _ fun y => by simpa [stdP] using hx (y, 0)
      have h2 : ∑ i, x.2 i * x.2 i = 0 := by
        have := hx (0, x.2)
        simp only [stdP] at this
        rwa [show P₁ x.1 0 = 0 by simpa using h.smulR 0 x.1 0, zero_add] at this
      have h3 : x.2 = 0 := by
        funext i
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_self_nonneg (x.2 i))).1 h2 i (Finset.mem_univ _)
        simpa using this
      exact Prod.ext h1 h3
    nondegR y hy := by
      have h1 : y.1 = 0 := h.nondegR _ fun x => by simpa [stdP] using hy (x, 0)
      have h2 : ∑ i, y.2 i * y.2 i = 0 := by
        have := hy (0, y.2)
        simp only [stdP] at this
        rwa [show P₁ 0 y.1 = 0 by simpa using h.smulL 0 0 y.1, zero_add] at this
      have h3 : y.2 = 0 := by
        funext i
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_self_nonneg (y.2 i))).1 h2 i (Finset.mem_univ _)
        simpa using this
      exact Prod.ext h1 h3
  }

theorem IsPairing.zero_left {P : V → V → ℝ} (h : IsPairing P) (y : V) : P 0 y = 0 := by
  simpa using h.smulL 0 0 y

theorem IsPairing.zero_right {P : V → V → ℝ} (h : IsPairing P) (x : V) : P x 0 = 0 := by
  simpa using h.smulR 0 x 0

theorem setup_std {P₁ : V₁ → V₁ → ℝ} (h : IsPairing P₁) (k : ℕ) : Setup (stdP P₁ k) P₁ (jStd k) (LStd V₁ k) := by
  exact {
    pair := isPairing_stdP h k
    pair₁ := h
    add w w' := by simp [jStd]
    smul c w := by simp [jStd]
    symp w w' := by simp [omega, stdP, jStd]
    iso := by
      rintro _ ⟨b, rfl⟩ _ ⟨b', rfl⟩
      simp [omega, stdP, h.zero_left]
    orth := by
      rintro _ ⟨b, rfl⟩ w
      simp [omega, stdP, jStd, h.zero_left, h.zero_right]
    max := by
      rintro ⟨⟨a₁, a₂⟩, ⟨b₁, b₂⟩⟩ hL hj
      have e2 : a₂ = 0 := by
        have := hL ((0, 0), (0, a₂)) ⟨a₂, rfl⟩
        simp only [omega, stdP, h.zero_right, h.zero_left, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
          zero_add, sub_zero] at this
        funext i
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_self_nonneg (a₂ i))).1 this i (Finset.mem_univ _)
        simpa using this
      have e1 : a₁ = 0 := h.nondegL _ fun y => by
        have := hj (0, y)
        simpa [omega, stdP, jStd, h.zero_left] using this
      have e3 : b₁ = 0 := h.nondegR _ fun x => by
        have := hj (x, 0)
        simpa [omega, stdP, jStd, h.zero_right] using this
      exact ⟨b₂, by simp [e1, e2, e3]⟩
  }

theorem isPairing_mul : IsPairing (fun x y : ℝ => x * y) := by
  exact {
    addL x x' y := add_mul x x' y
    addR x y y' := mul_add x y y'
    smulL c x y := by simp [mul_assoc]
    smulR c x y := by simp only [smul_eq_mul]; ring
    nondegL x hx := by simpa using hx 1
    nondegR y hy := by simpa using hy 1
  }

end Real

section Adelic

open scoped Matrix
open NumberField GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F : Type} [Field F] [NumberField F]


variable (F) in
def trP (κ : Type) [Fintype κ] (y b : κ → mixedEmbedding.mixedSpace F) : ℝ :=
  Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * b i)

def locV {κ : Type} (x : κ → AF F) : κ → mixedEmbedding.mixedSpace F := fun i => evI F (x i)

def liftV {κ : Type} (y : κ → mixedEmbedding.mixedSpace F) : κ → AF F :=
  fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i), 0)

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁}

end Adelic

end GlobalTheory.ArchUniq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolActs
noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.RealActs

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def DerOn (N : Submodule ℂ (SInf F κ)) (T : ℝ → ((κ → AF F) → ℂ) → (κ → AF F) → ℂ) : Prop :=
  ∃ D : SInf F κ →ₗ[ℂ] SInf F κ, (∀ f ∈ N, D f ∈ N) ∧ ∀ f ∈ N, ∀ f₁ : SInf F κ, ActsD (evI F) T f f₁ ↔ f₁ = D f

def OpOn (N : Submodule ℂ (SInf F κ)) (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ) : Prop :=
  ∃ D : SInf F κ →ₗ[ℂ] SInf F κ, (∀ f ∈ N, D f ∈ N) ∧ ∀ f ∈ N, ∀ f₁ : SInf F κ, Acts (evI F) T f f₁ ↔ f₁ = D f

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def PolActs (B : Base F E) {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (om : Rep σ X W) : Prop :=
  (∀ γ ∈ Lines σ X, DerOn (M.Pol B.ψ B.emb) (fun t => om (γ (Multiplicative.ofAdd t), 1))) ∧
  (∀ k ∈ KInf σ X B.emb, OpOn (M.Pol B.ψ B.emb) (om (k, 1))) ∧
  (∀ γ ∈ Lines σ W, DerOn (M.Pol B.ψ B.emb) (fun t => om (1, γ (Multiplicative.ofAdd t)))) ∧
  ∀ k ∈ KInf σ W B.emb, OpOn (M.Pol B.ψ B.emb) (om (1, k))

def KerStab (B : Base F E) {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (om : Rep σ X W) {P : Type}
    [AddCommGroup P] [Module ℂ P] (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) : Prop :=
  (∀ γ ∈ Lines σ W, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
    ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ → p f = 0 → p f₁ = 0) ∧
  ∀ k ∈ KInf σ W B.emb, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
    Acts (evI F) (om (1, k)) f f₁ → p f = 0 → p f₁ = 0

def Irred (B : Base F E) {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (om : Rep σ X W) {P : Type}
    [AddCommGroup P] [Module ℂ P] (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) : Prop :=
  ∀ N : Submodule ℂ P,
    (∀ γ ∈ Lines σ W, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
      ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ → p f ∈ N → p f₁ ∈ N) →
    (∀ k ∈ KInf σ W B.emb, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
      Acts (evI F) (om (1, k)) f f₁ → p f ∈ N → p f₁ ∈ N) → N = ⊥ ∨ N = ⊤

end GlobalTheory.RealActs

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFinprodSchwartzBruhatFiniteAdel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFinprodSchwartzBruhatFiniteAdel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

namespace GlobalTheory.AdelicCoordSupport

theorem hasCompactSupport_finprod : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), (κ → Fv F v) → ℂ), (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) →
    (∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    HasCompactSupport (fun y : κ → FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) := by
  intro F _ _ κ _ φ hSB hae
  classical
  let L : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), Set (κ → Fv F v) :=
    fun v => {x | ∀ i, x i ∈ v.adicCompletionIntegers F}
  have hLc : ∀ v, IsClosed (L v) := fun v => by
    have e : L v = Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v)) := by
      ext x; simp [L]
    rw [e]
    exact isClosed_set_pi fun _ _ => (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v).isClosed
  have hint : ∀ y : κ → FiniteAdeleRing (𝓞 F) F, ∀ᶠ v in Filter.cofinite,
      (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) ∈ L v := fun y =>
    Filter.eventually_all.2 fun i => (y i).2
  have hfac : ∀ y : κ → FiniteAdeleRing (𝓞 F) F,
      (∏ᶠ v, φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) ≠ 0 →
      ∀ v, φ v (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) ≠ 0 := by
    intro y h v
    have hfin : (Function.mulSupport fun v => φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)).Finite := by
      refine (Filter.eventually_cofinite.1 (hae.and (hint y))).subset ?_
      intro w hw h'
      apply hw
      simp only
      rw [h'.1, Set.indicator_of_mem h'.2]
      rfl
    rw [finprod_eq_prod _ hfin] at h
    by_cases hv : v ∈ hfin.toFinset
    · exact Finset.prod_ne_zero_iff.1 h v hv
    · rw [Set.Finite.mem_toFinset, Function.mem_mulSupport, not_not] at hv
      rw [hv]
      exact one_ne_zero
  let D : κ → ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), Set (Fv F v) := fun i v =>
    ((fun Z : κ → Fv F v => Z i) '' tsupport (φ v)) ∪ (v.adicCompletionIntegers F : Set (Fv F v))
  have hD : ∀ i v, IsCompact (D i v) := fun i v =>
    ((hSB v).2.isCompact.image (continuous_apply i)).union (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v)
  have hDe : ∀ i, ∀ᶠ v in Filter.cofinite,
      D i v = (v.adicCompletionIntegers F : Set (Fv F v)) := by
    intro i
    filter_upwards [hae] with v hv
    refine Set.union_eq_right.2 ?_
    rintro _ ⟨Z, hZ, rfl⟩
    have hsub : tsupport (φ v) ⊆ L v := by
      rw [hv]
      exact closure_minimal Set.support_indicator_subset (hLc v)
    exact hsub hZ i
  let Box : Set (κ → FiniteAdeleRing (𝓞 F) F) :=
    Set.pi Set.univ fun i => {x | ∀ v, x v ∈ D i v}
  have hbox : IsCompact Box :=
    isCompact_univ_pi fun i => PI.VolStabS.AdmissibleCompactSupport.isCompact_finBox (hD i) (hDe i)
  refine HasCompactSupport.intro hbox fun y hy => ?_
  by_contra h
  apply hy
  intro i _ v
  exact Or.inl ⟨_, subset_tsupport _ (hfac y h v), rfl⟩

end GlobalTheory.AdelicCoordSupport
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFinprodSchwartzBruhatFiniteAdelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasCompactSupport_finprod_schwartzBruhat_finiteAdeles : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), (κ → Fv F v) → ℂ), (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) →
    (∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    HasCompactSupport (fun y : κ → FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) := by
  first | exact @GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod | exact GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod | (intros; apply GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulusOfNormEqAbs
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ModuAdele

open scoped Pointwise

theorem distribHaarChar_adeleRing (K : Type) [Field K] [NumberField K] (a : (AdeleRing (𝓞 K) K)ˣ) :
    (distribHaarChar (AdeleRing (𝓞 K) K) a : ℝ) = (GroundTheory.Global.IdeleGroup.ideleModule K a : ℝ) := by
  letI : MeasurableSpace (AdeleRing (𝓞 K) K) := GroundTheory.Global.measurableSpace_adeleRing K
  obtain ⟨s, hsc, hs0⟩ : ∃ s : Set (AdeleRing (𝓞 K) K), IsCompact s ∧ s ∈ nhds (0 : AdeleRing (𝓞 K) K) :=
    exists_compact_mem_nhds 0
  have hpos : 0 ≤ (GroundTheory.Global.IdeleGroup.ideleModule K a : ℝ) := (GroundTheory.Global.IdeleGroup.ideleModule K a).2.le
  set r : NNReal := ⟨_, hpos⟩ with hr
  set μ := GroundTheory.Global.adeleMeasure K with hμ
  set ν : Measure (AdeleRing (𝓞 K) K) := Measure.addHaar with hν
  have e1 := Measure.measure_isAddInvariant_eq_smul_of_isCompact_closure μ ν hsc.closure
  have e2 := Measure.measure_isAddInvariant_eq_smul_of_isCompact_closure μ ν (hsc.smul a).closure
  have hm := GroundTheory.Global.adeleMeasure_smul a s
  set c := μ.addHaarScalarFactor ν
  have hμs : μ s ≠ 0 := (Measure.measure_pos_of_mem_nhds _ hs0).ne'
  have hνs : ν s ≠ 0 := (Measure.measure_pos_of_mem_nhds _ hs0).ne'
  have hνs' : ν s ≠ ⊤ := hsc.measure_lt_top.ne
  have hc : (c : ENNReal) ≠ 0 := by
    intro h0
    apply hμs
    rw [e1, ENNReal.smul_def, smul_eq_mul, h0, zero_mul]
  have h := distribHaarChar_eq_of_measure_smul_eq_mul (g := a) (μ := ν) (s := s) hνs hνs'
    (r := r) (by
      rw [e1, e2, ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul,
        ENNReal.ofReal_eq_coe_nnreal hpos] at hm
      have hm' : (c : ENNReal) * ν (a • s) = (c : ENNReal) * ((r : ENNReal) * ν s) := by
        calc (c : ENNReal) * ν (a • s) = (r : ENNReal) * ((c : ENNReal) * ν s) := hm
          _ = (c : ENNReal) * ((r : ENNReal) * ν s) := by ring
      exact (ENNReal.mul_right_inj hc ENNReal.coe_ne_top).1 hm')
  rw [h]
  rfl

end GlobalTheory.ModuAdele

theorem GlobalTheory.ModuAdele.modu_norm_eq_absE : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (x : (AE F E)ˣ),
    (adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F) x) = absE F E x := by
  intro F E _ _ _ _ _ x
  have hf : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      ‖evFin F v (Algebra.norm (AF F) x.1)‖₊).Finite := by
    simpa only [GlobalTheory.Doubling.absEv_unitFin] using GlobalTheory.Doubling.finite_mulSupport_absEv x
  apply NNReal.eq
  change (distribHaarChar (AdeleRing (𝓞 F) F) (Units.map (Algebra.norm (AF F) : AE F E →* AF F) x) : ℝ) = _
  rw [GlobalTheory.ModuAdele.distribHaarChar_adeleRing, GroundTheory.Global.IdeleGroup.ideleModule_eq, GlobalTheory.Doubling.absE_apply]
  simp only [GlobalTheory.Doubling.absEv_unitFin, GlobalTheory.Doubling.absEw_unitInf]
  rw [NNReal.coe_mul, NNReal.coe_prod]
  congr 1
  rw [show ((∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖evFin F v (Algebra.norm (AF F) x.1)‖₊ : ℝ≥0) : ℝ) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 F), ((‖evFin F v (Algebra.norm (AF F) x.1)‖₊ : ℝ≥0) : ℝ) from
      NNReal.toRealHom.toMonoidHom.map_finprod hf]
  rfl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockScaledIntegralOfLocal
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.ThKTorus.IntegralOfAdic

theorem evFin_realAd (F : Type) [Field F] [NumberField F] (v : Pl F) (x : ℝ) :
    evFin F v (realAd F x) = 0 := by
  show evalV F v 0 = 0
  exact map_zero _

end GlobalTheory.ThKTorus.IntegralOfAdic
end
