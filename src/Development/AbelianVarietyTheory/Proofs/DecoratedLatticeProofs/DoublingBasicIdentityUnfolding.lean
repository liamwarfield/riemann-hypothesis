module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawScalarFormsLawsOnClassData
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingNegligibleOrbitUnfoldedIntegralEqZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingIntegralNegligibleOrbitsEqZeroCuspForm
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingIntegralNegligibleOrbitsEqZeroCuspForm
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section
namespace GlobalTheory.Core.Rk.NegOrbit
open GlobalTheory.Eis GlobalTheory.AutomorphicL2Unitary

variable {D : D7} (V : HSp D)

def IsNeg (x : GA D (dblSp V)) : Prop := ¬ ∃ δ ∈ GQ V, x * (io V (δ, 1))⁻¹ ∈ siegel V

variable {V}

theorem isNeg_siegel_mul {p x : GA D (dblSp V)} (hp : p ∈ siegel V) : IsNeg V (p * x) ↔ IsNeg V x := by
  unfold IsNeg
  refine not_congr ⟨fun ⟨δ, hδ, h⟩ => ⟨δ, hδ, ?_⟩, fun ⟨δ, hδ, h⟩ => ⟨δ, hδ, ?_⟩⟩
  · have := (siegel V).mul_mem ((siegel V).inv_mem hp) h
    simpa [mul_assoc] using this
  · simpa [mul_assoc] using (siegel V).mul_mem hp h

theorem isNeg_mul_io {x : GA D (dblSp V)} {γ₁ γ₂ : GA D V} (h₁ : γ₁ ∈ GQ V) (h₂ : γ₂ ∈ GQ V) :
    IsNeg V (x * io V (γ₁, γ₂)) → IsNeg V x := by
  intro h ⟨δ, hδ, hx⟩
  refine h ⟨γ₂⁻¹ * δ * γ₁, (GQ V).mul_mem ((GQ V).mul_mem ((GQ V).inv_mem h₂) hδ) h₁, ?_⟩
  have e : x * io V (γ₁, γ₂) * (io V (γ₂⁻¹ * δ * γ₁, 1))⁻¹ = x * (io V (δ, 1))⁻¹ * io V (γ₂, γ₂) := by
    simp only [mul_assoc, ← map_inv, ← map_mul]
    congr 2
    ext <;> simp [mul_assoc]
  rw [e]
  exact (siegel V).mul_mem hx ((io_mem_siegel V).2 rfl)

theorem isNeg_mul_io_iff {x : GA D (dblSp V)} {γ₁ γ₂ : GA D V} (h₁ : γ₁ ∈ GQ V) (h₂ : γ₂ ∈ GQ V) :
    IsNeg V (x * io V (γ₁, γ₂)) ↔ IsNeg V x := by
  refine ⟨isNeg_mul_io h₁ h₂, fun h => isNeg_mul_io ((GQ V).inv_mem h₁) ((GQ V).inv_mem h₂) ?_⟩
  have e : ((γ₁, γ₂) * (γ₁⁻¹, γ₂⁻¹) : GA D V × GA D V) = 1 := by ext <;> simp
  rw [mul_assoc, ← map_mul, e, map_one, mul_one]
  exact h

theorem exists_out_rmul (q : SiegelCosets V) (g : GQ (dblSp V)) : ∃ p ∈ siegelQ V,
    (((rmul _ g q).out : GQ (dblSp V)) : GA D (dblSp V)) = p * (q.out : GQ (dblSp V)) * g := by
  have e : mk ((siegel V).subgroupOf (GQ (dblSp V))) (q.out * g) = mk _ (rmul _ g q).out :=
    ((rmul_mk g q.out).symm.trans (congrArg (rmul _ g) (Quotient.out_eq q))).trans (Quotient.out_eq _).symm
  obtain ⟨p, hp⟩ := mk_eq_iff.1 e
  refine ⟨((p : GQ (dblSp V)) : GA D (dblSp V)), ⟨Subgroup.mem_subgroupOf.1 p.2, (p : GQ (dblSp V)).2⟩, ?_⟩
  rw [← hp]
  simp [mul_assoc]

theorem isNeg_out_rmul_iff (q : SiegelCosets V) {γ₁ γ₂ : GA D V} (h₁ : γ₁ ∈ GQ V) (h₂ : γ₂ ∈ GQ V) :
    IsNeg V ((rmul _ ⟨io V (γ₁, γ₂), io_mem_GQ V h₁ h₂⟩ q).out : GQ (dblSp V)) ↔ IsNeg V (q.out : GQ (dblSp V)) := by
  obtain ⟨p, hp, e⟩ := exists_out_rmul q ⟨io V (γ₁, γ₂), io_mem_GQ V h₁ h₂⟩
  rw [e, mul_assoc, isNeg_siegel_mul hp.1]
  exact isNeg_mul_io_iff h₁ h₂

theorem apply_out_rmul {a : GL (Fin V.rank) (AE D)} {μ : (AE D)ˣ →* Circle} (hμ : IsHeckeChar D μ) {s : ℂ}
    {φ : GA D (dblSp V) → ℂ} (hφ : φ ∈ degPS V a μ s) (q : SiegelCosets V) (g : GQ (dblSp V)) (y : GA D (dblSp V)) :
    φ ((((rmul _ g q).out : GQ (dblSp V)) : GA D (dblSp V)) * y) = φ ((q.out : GQ (dblSp V)) * g * y) := by
  obtain ⟨p, hp, e⟩ := exists_out_rmul q g
  rw [e, mul_assoc, mul_assoc, apply_siegelQ_mul V a hμ hφ hp, mul_assoc]

abbrev NegCosets (V : HSp D) : Type := {q : SiegelCosets V // IsNeg V (q.out : GQ (dblSp V))}

def ioEquiv {γ₁ γ₂ : GA D V} (h₁ : γ₁ ∈ GQ V) (h₂ : γ₂ ∈ GQ V) : NegCosets V ≃ NegCosets V where
  toFun q := ⟨rmul _ ⟨io V (γ₁, γ₂), io_mem_GQ V h₁ h₂⟩ q.1, (isNeg_out_rmul_iff q.1 h₁ h₂).2 q.2⟩
  invFun q := ⟨rmul _ ⟨io V (γ₁⁻¹, γ₂⁻¹), io_mem_GQ V (inv_mem h₁) (inv_mem h₂)⟩ q.1,
    (isNeg_out_rmul_iff q.1 (inv_mem h₁) (inv_mem h₂)).2 q.2⟩
  left_inv q := Subtype.ext (by
    show rmul _ _ (rmul _ _ q.1) = q.1
    rw [← rmul_mul]
    convert rmul_one q.1 using 2
    ext1; simp [← map_mul]; exact map_one (io V))
  right_inv q := Subtype.ext (by
    show rmul _ _ (rmul _ _ q.1) = q.1
    rw [← rmul_mul]
    convert rmul_one q.1 using 2
    ext1; simp [← map_mul]; exact map_one (io V))

def negAction (V : HSp D) : MulAction (GQ V) (NegCosets V) where
  smul δ q := ioEquiv (inv_mem δ.2) (one_mem (GQ V)) q
  one_smul q := Subtype.ext (by
    show rmul _ _ q.1 = q.1
    convert rmul_one q.1 using 2
    ext1; simp; exact map_one (io V))
  mul_smul δ₁ δ₂ q := Subtype.ext (by
    show rmul _ _ q.1 = rmul _ _ (rmul _ _ q.1)
    rw [← rmul_mul]
    congr 1
    ext1; simp [← map_mul])

attribute [local instance] negAction

@[simp] theorem io_one_one : io V (1, 1) = 1 := map_one (io V)

theorem smul_val (δ : GQ V) (q : NegCosets V) : (δ • q).1 =
    rmul _ ⟨io V ((δ : GA D V)⁻¹, 1), io_mem_GQ V (inv_mem δ.2) (one_mem _)⟩ q.1 := rfl

theorem mem_map_stabilizer_iff (y : NegCosets V) (x : GA D V) :
    x ∈ (MulAction.stabilizer (GQ V) y).map (GQ V).subtype ↔
      x ∈ GQ V ∧ ((y.1.out : GQ (dblSp V)) : GA D (dblSp V)) * io V (x, 1) *
        ((y.1.out : GQ (dblSp V)) : GA D (dblSp V))⁻¹ ∈ siegel V := by
  constructor
  · rintro ⟨δ, hδ, rfl⟩
    refine ⟨δ.2, ?_⟩
    obtain ⟨p, hp, e⟩ := exists_out_rmul y.1 ⟨io V ((δ : GA D V)⁻¹, 1), io_mem_GQ V (inv_mem δ.2) (one_mem _)⟩
    have hv : rmul _ ⟨io V ((δ : GA D V)⁻¹, 1), io_mem_GQ V (inv_mem δ.2) (one_mem _)⟩ y.1 = y.1 :=
      (smul_val δ y).symm.trans (congrArg Subtype.val (MulAction.mem_stabilizer_iff.1 hδ))
    rw [hv] at e
    have e' : ((y.1.out : GQ (dblSp V)) : GA D (dblSp V)) =
        p * ((y.1.out : GQ (dblSp V)) : GA D (dblSp V)) * io V ((δ : GA D V)⁻¹, 1) := e
    have h' : p * ((y.1.out : GQ (dblSp V)) : GA D (dblSp V)) * io V ((δ : GA D V)⁻¹, 1) * io V ((δ : GA D V), 1) *
        ((y.1.out : GQ (dblSp V)) : GA D (dblSp V))⁻¹ = p := by
      rw [mul_assoc (p * _), ← map_mul]
      simp [io_one_one]
    rw [← e'] at h'
    rw [Subgroup.coe_subtype, h']
    exact hp.1
  · rintro ⟨hx, hs⟩
    refine ⟨⟨x, hx⟩, MulAction.mem_stabilizer_iff.2 (Subtype.ext ?_), rfl⟩
    rw [smul_val]
    conv_lhs => rw [← Quotient.out_eq y.1]
    have hr : ((y.1.out : GQ (dblSp V)) : GA D (dblSp V)) * io V (x, 1) *
        ((y.1.out : GQ (dblSp V)) : GA D (dblSp V))⁻¹ ∈ GQ (dblSp V) :=
      mul_mem (mul_mem (y.1.out).2 (io_mem_GQ V hx (one_mem _))) (inv_mem (y.1.out).2)
    refine ((rmul_mk _ _).trans (mk_eq_iff.2 ⟨⟨⟨_, hr⟩, Subgroup.mem_subgroupOf.2 hs⟩, ?_⟩)).trans (Quotient.out_eq _)
    apply Subtype.ext
    simp only [Subgroup.coe_mul, mul_assoc, inv_mul_cancel_left, ← map_mul]
    simp [io_one_one]

theorem leftInv_negIntegrand {a : GL (Fin V.rank) (AE D)} {μ : (AE D)ˣ →* Circle} (hμ : IsHeckeChar D μ) {s : ℂ}
    {φ : GA D (dblSp V) → ℂ} (hφ : φ ∈ degPS V a μ s) {f₁ f₂ : GA D V → ℂ} (hf₁ : LeftInv (GQ V) f₁)
    (hf₂ : LeftInv (GQ V) f₂) : LeftInv ((GQ V).prod (GQ V))
      (dblIntegrand V μ (fun y => ∑' q : NegCosets V, φ (((q.1.out : GQ (dblSp V)) : GA D (dblSp V)) * y)) f₁ f₂) := by
  rintro ⟨γ₁, γ₂⟩ ⟨h₁, h₂⟩ ⟨g₁, g₂⟩
  have hE : (∑' q : NegCosets V, φ (((q.1.out : GQ (dblSp V)) : GA D (dblSp V)) * io V ((γ₁, γ₂) * (g₁, g₂)))) =
      ∑' q : NegCosets V, φ (((q.1.out : GQ (dblSp V)) : GA D (dblSp V)) * io V (g₁, g₂)) := by
    refine (tsum_congr fun q => ?_).trans ((ioEquiv h₁ h₂).tsum_eq
      (fun q : NegCosets V => φ (((q.1.out : GQ (dblSp V)) : GA D (dblSp V)) * io V (g₁, g₂))))
    show _ = φ ((((rmul _ ⟨io V (γ₁, γ₂), io_mem_GQ V h₁ h₂⟩ q.1).out : GQ (dblSp V)) : GA D (dblSp V)) *
      io V (g₁, g₂))
    rw [apply_out_rmul hμ hφ, map_mul, mul_assoc]
  show (∑' q : NegCosets V, φ (((q.1.out : GQ (dblSp V)) : GA D (dblSp V)) * io V ((γ₁, γ₂) * (g₁, g₂)))) *
      conj (f₁ (γ₁ * g₁)) * f₂ (γ₂ * g₂) * (μ (detA V (γ₂ * g₂)) : ℂ)⁻¹ =
    (∑' q : NegCosets V, φ (((q.1.out : GQ (dblSp V)) : GA D (dblSp V)) * io V (g₁, g₂))) *
      conj (f₁ g₁) * f₂ g₂ * (μ (detA V g₂) : ℂ)⁻¹
  rw [hE, hf₁ γ₁ h₁, hf₂ γ₂ h₂, map_mul, map_mul, apply_detA hμ h₂, one_mul]

theorem integral_neg_eq_zero : ∀ (D : D7) (V : HSp D) (a : GL (Fin V.rank) (AE D)), IsMaj V a → ∀ (μ : (AE D)ˣ →* Circle), IsHeckeChar D μ → ∀ s : ℂ, (V.rank : ℝ) / 2 < s.re → ∀ φ ∈ degPS V a μ s, GlobalTheory.Grow.ModGrowth (dblSp V) (GlobalTheory.Eis.eis V (GlobalTheory.Eis.sph V a (s.re : ℂ))) → ∀ m : Measure (GA D V), m.IsHaarMeasure → ∀ f₁ f₂ : GA D V → ℂ, GlobalTheory.Grow.RapidDec V f₁ → GlobalTheory.Grow.RapidDec V f₂ → IsCuspFun V f₁ → ∫ x, GlobalTheory.Eis.dblIntegrandQ V μ (fun y => ∑' q : {q : GlobalTheory.Eis.SiegelCosets V // ¬ ∃ δ ∈ GQ V, ((q.out : GQ (dblSp V)) : GA D (dblSp V)) * (io V (δ, 1))⁻¹ ∈ siegel V}, φ (((q.1.out : GQ (dblSp V)) : GA D (dblSp V)) * y)) f₁ f₂ x ∂(autMeasure V m).prod (autMeasure V m) = 0 := by
  intro D V a ha μ hμ s hs φ hφ hgrow m hm f₁ f₂ h₁ h₂ hc
  haveI := hm
  show ∫ x, dblIntegrandQ V μ (fun y => ∑' q : NegCosets V, φ (((q.1.out : GQ (dblSp V)) : GA D (dblSp V)) * y)) f₁ f₂ x
    ∂(autMeasure V m).prod (autMeasure V m) = 0
  set E : GA D (dblSp V) → ℂ := fun y => ∑' q : NegCosets V, φ (((q.1.out : GQ (dblSp V)) : GA D (dblSp V)) * y)
    with hEdef
  by_cases hI : Integrable (dblIntegrandQ V μ E f₁ f₂) ((autMeasure V m).prod (autMeasure V m))
  swap
  · exact integral_undef hI
  have hli : LeftInv ((GQ V).prod (GQ V)) (dblIntegrand V μ E f₁ f₂) := leftInv_negIntegrand hμ hφ h₁.1 h₂.1
  have hconv : DblConv V μ m E f₁ f₂ := ⟨hli, hI⟩
  have h𝓕 : IsFundamentalDomain (GQ V) (stdDom (GQ V)) m := isFundamentalDomain_stdDom _ m
  set 𝓕 := stdDom (GQ V)
  obtain ⟨hint, heq⟩ := hconv.dblInt_eq h𝓕
  refine (heq : dblInt V μ m E f₁ f₂ = _).trans ?_
  rw [IntegrableOn, ← Measure.prod_restrict] at hint
  rw [← Measure.prod_restrict, integral_prod_symm _ hint]
  have hφc : Continuous φ := hφ.2.1
  have hcont : ∀ q : SiegelCosets V, Continuous
      (dblIntegrand V μ (fun x => φ (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * x)) f₁ f₂) := fun q =>
    continuous_dblIntegrand hμ (hφc.comp (continuous_const.mul continuous_id)) h₁.continuous h₂.continuous
  set G : SiegelCosets V → GA D V × GA D V → ENNReal := fun q x =>
    ‖dblIntegrand V μ (fun x => φ (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * x)) f₁ f₂ x‖ₑ with hGdef
  have hGm : ∀ q, Measurable (G q) := fun q => (hcont q).measurable.enorm
  have hfin := (GlobalTheory.Core.Rk.AbsConv.absConv_unfolded D V a ha μ hμ s hs φ hφ hgrow m hm f₁ f₂ h₁ h₂).1 𝓕 h𝓕
  rw [← Measure.prod_restrict, ← lintegral_tsum fun q => (hGm q).aemeasurable,
    lintegral_prod_symm _ (Measurable.tsum hGm).aemeasurable] at hfin
  have hae := ae_lt_top (Measurable.tsum hGm).lintegral_prod_left' hfin
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hae] with g₂ hg₂
  set Φ : NegCosets V → GA D V → ℂ := fun y h =>
    dblIntegrand V μ (fun x => φ (((y.1.out : GQ (dblSp V)) : GA D (dblSp V)) * x)) f₁ f₂ (h, g₂) with hΦdef
  have hpt : ∀ g₁, dblIntegrand V μ E f₁ f₂ (g₁, g₂) = ∑' y, Φ y g₁ := fun g₁ => by
    simp only [hΦdef, dblIntegrand, hEdef]
    rw [← tsum_mul_right, ← tsum_mul_right, ← tsum_mul_right]
  have hΦm : ∀ y, Measurable (Φ y) := fun y =>
    ((hcont y.1).comp (continuous_id.prodMk continuous_const)).measurable
  have hsum : ∑' y, ∫⁻ h, ‖Φ y h‖ₑ ∂(m.restrict 𝓕) ≠ ⊤ := by
    refine ne_top_of_le_ne_top hg₂.ne ?_
    have hl := lintegral_tsum (μ := m.restrict 𝓕) (f := fun q h => G q (h, g₂))
      fun q => ((hGm q).comp measurable_prodMk_right).aemeasurable
    rw [hl]
    exact ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective
      (fun q => ∫⁻ h, G q (h, g₂) ∂(m.restrict 𝓕))
  rw [integral_congr_ae (.of_forall hpt), integral_tsum (fun y => (hΦm y).aestronglyMeasurable) hsum]
  refine GlobalTheory.OrbitUnfold.tsum_setIntegral_eq_zero (GA D V) m (GQ V) (NegCosets V) 𝓕 h𝓕 Φ hΦm ?_ hsum ?_
  · intro γ y h
    have e : io V ((γ : GA D V)⁻¹, 1) * io V (γ * h, g₂) = io V (h, g₂) := by
      rw [← map_mul]; simp
    simp only [hΦdef, dblIntegrand]
    rw [h₁.1 _ γ.2, smul_val, apply_out_rmul hμ hφ, mul_assoc _ _ (io V _)]
    erw [e]
  · intro y 𝓖 h𝓖 hi
    exact GlobalTheory.T.doublingNegligibleOrbit_unfoldedIntegral_eq_zero D V a μ hμ s φ hφ _ (y.1.out).2 y.2 f₁ f₂ h₁.continuous h₂.continuous h₁.1 hc g₂ _
      (mem_map_stabilizer_iff y) m hm 𝓖 h𝓖 hi

end GlobalTheory.Core.Rk.NegOrbit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingIntegralNegligibleOrbitsEqZeroCuspFormStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubling_integral_negligible_orbits_eq_zero_cuspForm : ∀ (D : D7) (V : HSp D) (a : GL (Fin V.rank) (AE D)), IsMaj V a → ∀ (μ : (AE D)ˣ →* Circle), IsHeckeChar D μ → ∀ s : ℂ, (V.rank : ℝ) / 2 < s.re → ∀ φ ∈ degPS V a μ s, GlobalTheory.Grow.ModGrowth (dblSp V) (GlobalTheory.Eis.eis V (GlobalTheory.Eis.sph V a (s.re : ℂ))) → ∀ m : Measure (GA D V), m.IsHaarMeasure → ∀ f₁ f₂ : GA D V → ℂ, GlobalTheory.Grow.RapidDec V f₁ → GlobalTheory.Grow.RapidDec V f₂ → IsCuspFun V f₁ → ∫ x, GlobalTheory.Eis.dblIntegrandQ V μ (fun y => ∑' q : {q : GlobalTheory.Eis.SiegelCosets V // ¬ ∃ δ ∈ GQ V, ((q.out : GQ (dblSp V)) : GA D (dblSp V)) * (io V (δ, 1))⁻¹ ∈ siegel V}, φ (((q.1.out : GQ (dblSp V)) : GA D (dblSp V)) * y)) f₁ f₂ x ∂(autMeasure V m).prod (autMeasure V m) = 0 := by
  first | exact @GlobalTheory.Core.Rk.NegOrbit.integral_neg_eq_zero | exact GlobalTheory.Core.Rk.NegOrbit.integral_neg_eq_zero | (intros; apply GlobalTheory.Core.Rk.NegOrbit.integral_neg_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingOpenOrbitUnfoldsToAdelicIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingOpenOrbitUnfoldsToAdelicIntegral
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

namespace GlobalTheory.Core.Rk.OpenOrbit

open Set Filter GlobalTheory.Eis

variable {D : D7} {V : HSp D}

theorem io_one_mul (δ : GA D V) (x : GA D V × GA D V) : io V (δ, 1) * io V x = io V (δ * x.1, x.2) := by
  rw [← map_mul]; congr 1; ext <;> simp

section Terms

variable {μ : (AE D)ˣ →* Circle} {φ : GA D (dblSp V) → ℂ} {f₁ f₂ : GA D V → ℂ}

theorem term_eq (hf₁ : ∀ γ ∈ GQ V, ∀ g, f₁ (γ * g) = f₁ g) (δ : GQ V) (x : GA D V × GA D V) :
    dblIntegrand V μ (fun y => φ (io V (δ, 1) * y)) f₁ f₂ x =
      dblIntegrand V μ φ f₁ f₂ ((δ : GA D V) * x.1, x.2) := by
  simp only [dblIntegrand, io_one_mul, hf₁ _ δ.2]

theorem tsum_open_ne_top (hμ : IsHeckeChar D μ) {a : GL (Fin V.rank) (AE D)} {s : ℂ} (hφ : φ ∈ degPS V a μ s)
    {m : Measure (GA D V)} [SFinite m] {𝓕 : Set (GA D V)}
    (h : ∑' q : SiegelCosets V, ∫⁻ x in 𝓕 ×ˢ 𝓕,
      ‖dblIntegrand V μ (fun x => φ (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * x)) f₁ f₂ x‖ₑ ∂m.prod m ≠ ⊤) :
    ∑' δ : GQ V, ∫⁻ x, ‖dblIntegrand V μ (fun y => φ (io V (δ, 1) * y)) f₁ f₂ x‖ₑ
      ∂(m.restrict 𝓕).prod (m.restrict 𝓕) ≠ ⊤ := by
  rw [Measure.prod_restrict]
  refine ne_top_of_le_ne_top h (le_trans (le_of_eq (tsum_congr fun δ => ?_))
    (ENNReal.tsum_comp_le_tsum_of_injective (injective_mk_io (V := V)) (fun q : SiegelCosets V => ∫⁻ x in 𝓕 ×ˢ 𝓕,
      ‖dblIntegrand V μ (fun x => φ (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * x)) f₁ f₂ x‖ₑ ∂m.prod m)))
  set q : SiegelCosets V := mk _ ⟨io V (δ, 1), io_mem_GQ V δ.2 (one_mem _)⟩ with hq
  have e : (mk _ q.out : SiegelCosets V) = mk _ ⟨io V (δ, 1), io_mem_GQ V δ.2 (one_mem _)⟩ := Quotient.out_eq q
  obtain ⟨p, hp⟩ := mk_eq_iff.1 e
  have hE : (fun y => φ (io V (δ, 1) * y)) = fun x => φ (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * x) := by
    funext y
    have h1 : io V (δ, 1) = ((p : GQ (dblSp V)) : GA D (dblSp V)) * ((q.out : GQ (dblSp V)) : GA D (dblSp V)) :=
      (congrArg Subtype.val hp).symm
    rw [h1, mul_assoc]
    exact apply_siegelQ_mul V a hμ hφ ⟨Subgroup.mem_subgroupOf.1 p.2, (p : GQ (dblSp V)).2⟩ _
  beta_reduce
  rw [hE]

theorem leftInv_open (hμ : IsHeckeChar D μ) {a : GL (Fin V.rank) (AE D)} {s : ℂ} (hφ : φ ∈ degPS V a μ s)
    (hf₁ : ∀ γ ∈ GQ V, ∀ g, f₁ (γ * g) = f₁ g) (hf₂ : ∀ γ ∈ GQ V, ∀ g, f₂ (γ * g) = f₂ g) :
    LeftInv ((GQ V).prod (GQ V)) (dblIntegrand V μ (fun y => ∑' δ : GQ V, φ (io V (δ, 1) * y)) f₁ f₂) := by
  rintro ⟨γ₁, γ₂⟩ ⟨h1, h2⟩ ⟨x₁, x₂⟩
  have hs : ∑' δ : GQ V, φ (io V (δ, 1) * io V ((γ₁, γ₂) * (x₁, x₂))) =
      ∑' δ : GQ V, φ (io V (δ, 1) * io V (x₁, x₂)) := by
    let e : GQ V ≃ GQ V := (Equiv.mulLeft (⟨γ₂, h2⟩ : GQ V)⁻¹).trans (Equiv.mulRight ⟨γ₁, h1⟩)
    conv_rhs => rw [← e.tsum_eq]
    refine tsum_congr fun δ => ?_
    simp only [io_one_mul, Prod.mk_mul_mk]
    have := apply_io_mul V a hφ γ₂ ((e δ : GA D V) * x₁) x₂
    rw [apply_detA hμ h2, Circle.coe_one, one_mul] at this
    rw [← this]
    congr 3
    simp [e, mul_assoc]
  simp only [dblIntegrand]
  rw [hs]
  simp only [Prod.mk_mul_mk, hf₁ _ h1, hf₂ _ h2, map_mul, apply_detA hμ h2, one_mul]

end Terms

theorem open_orbit : ∀ (D : D7) (V : HSp D) (a : GL (Fin V.rank) (AE D)), IsMaj V a → ∀ (μ : (AE D)ˣ →* Circle), IsHeckeChar D μ → ∀ s : ℂ, (V.rank : ℝ) / 2 < s.re → ∀ φ ∈ degPS V a μ s, GlobalTheory.Grow.ModGrowth (dblSp V) (GlobalTheory.Eis.eis V (GlobalTheory.Eis.sph V a (s.re : ℂ))) → ∀ m : Measure (GA D V), m.IsHaarMeasure → ∀ f₁ f₂ : GA D V → ℂ, GlobalTheory.Grow.RapidDec V f₁ → GlobalTheory.Grow.RapidDec V f₂ → ZetaConvH D.sp.cm.sig (gram_hdbl V) m φ (GlobalTheory.Eis.petCoef V m f₁ f₂) ∧ ∫ x, GlobalTheory.Eis.dblIntegrandQ V μ (fun y => ∑' δ : GQ V, φ (io V (δ, 1) * y)) f₁ f₂ x ∂(autMeasure V m).prod (autMeasure V m) = zetaH D.sp.cm.sig (gram_hdbl V) m φ (GlobalTheory.Eis.petCoef V m f₁ f₂) := by
  intro D V a ha μ hμ s hs φ hφ hgrow m hm f₁ f₂ h₁ h₂
  haveI := hm
  have hF : IsFundamentalDomain (GQ V) (stdDom (GQ V)) m := isFundamentalDomain_stdDom _ m
  set 𝓕 := stdDom (GQ V) with h𝓕
  have hφc : Continuous φ := hφ.2.1
  set E : GA D (dblSp V) → ℂ := fun y => ∑' δ : GQ V, φ (io V (δ, 1) * y) with hEdef
  set H : GA D V × GA D V → ℂ := dblIntegrand V μ φ f₁ f₂ with hHdef
  set T : GQ V → GA D V × GA D V → ℂ := fun δ => dblIntegrand V μ (fun y => φ (io V (δ, 1) * y)) f₁ f₂ with hTdef
  set K : GA D V × GA D V → ℂ := fun p => H (p.1 * p.2, p.1) with hKdef
  have hHc : Continuous H := continuous_dblIntegrand hμ hφc h₁.continuous h₂.continuous
  have hT : ∀ (δ : GQ V) (x : GA D V × GA D V), T δ x = H ((δ : GA D V) * x.1, x.2) := fun δ x => term_eq h₁.1 δ x
  have hTc : ∀ δ : GQ V, Continuous (T δ) := fun δ => by
    rw [show T δ = fun x => H ((δ : GA D V) * x.1, x.2) from funext (hT δ)]
    exact hHc.comp ((continuous_const.mul continuous_fst).prodMk continuous_snd)
  have hTm : ∀ δ : GQ V, Measurable fun x => ‖T δ x‖ₑ := fun δ => (hTc δ).measurable.enorm
  have hKc : Continuous K := hHc.comp ((continuous_fst.mul continuous_snd).prodMk continuous_fst)

  have hbd : ∑' δ : GQ V, ∫⁻ x, ‖T δ x‖ₑ ∂(m.restrict 𝓕).prod (m.restrict 𝓕) ≠ ⊤ :=
    tsum_open_ne_top hμ hφ ((GlobalTheory.Core.Rk.AbsConv.absConv_unfolded D V a ha μ hμ s hs φ hφ hgrow m hm f₁ f₂ h₁ h₂).1 𝓕 hF)
  have hTint : ∀ δ : GQ V, Integrable (T δ) ((m.restrict 𝓕).prod (m.restrict 𝓕)) := fun δ =>
    ⟨(hTc δ).aestronglyMeasurable, lt_of_le_of_lt
      (ENNReal.le_tsum (f := fun δ : GQ V => ∫⁻ x, ‖T δ x‖ₑ ∂(m.restrict 𝓕).prod (m.restrict 𝓕)) δ)
      (lt_top_iff_ne_top.2 hbd)⟩

  have hlin : ∀ x₂, ∫⁻ x₁, ‖H (x₁, x₂)‖ₑ ∂m = ∑' δ : GQ V, ∫⁻ x₁ in 𝓕, ‖T δ (x₁, x₂)‖ₑ ∂m := fun x₂ => by
    rw [hF.lintegral_eq_tsum'' (fun x₁ => ‖H (x₁, x₂)‖ₑ)]
    refine tsum_congr fun δ => ?_
    simp only [hT, Subgroup.smul_def, smul_eq_mul]
  have hlK : ∫⁻ p, ‖K p‖ₑ ∂(m.restrict 𝓕).prod m =
      ∑' δ : GQ V, ∫⁻ x, ‖T δ x‖ₑ ∂(m.restrict 𝓕).prod (m.restrict 𝓕) := by
    rw [lintegral_prod _ hKc.measurable.enorm.aemeasurable]
    have h1 : ∀ x₂, ∫⁻ g, ‖K (x₂, g)‖ₑ ∂m = ∫⁻ x₁, ‖H (x₁, x₂)‖ₑ ∂m := fun x₂ =>
      lintegral_mul_left_eq_self (fun x₁ => ‖H (x₁, x₂)‖ₑ) x₂
    simp_rw [h1, hlin]
    rw [lintegral_tsum (fun δ => ((hTm δ).lintegral_prod_left').aemeasurable)]
    refine tsum_congr fun δ => ?_
    rw [lintegral_prod_symm _ (hTm δ).aemeasurable]
  have hKint : Integrable K ((m.restrict 𝓕).prod m) :=
    ⟨hKc.aestronglyMeasurable, show ∫⁻ p, ‖K p‖ₑ ∂(m.restrict 𝓕).prod m < ⊤ by rw [hlK]; exact lt_top_iff_ne_top.2 hbd⟩
  have hHint : ∀ᵐ x₂ ∂(m.restrict 𝓕), Integrable (fun x₁ => H (x₁, x₂)) m := by
    filter_upwards [hKint.prod_right_ae] with x₂ hx
    have := hx.comp_mul_left x₂⁻¹
    simpa [hKdef, mul_inv_cancel_left] using this

  have hli : LeftInv ((GQ V).prod (GQ V)) (dblIntegrand V μ E f₁ f₂) := leftInv_open hμ hφ h₁.1 h₂.1
  have hQ : dblIntegrandQ V μ E f₁ f₂ = dblIntegrand V μ E f₁ f₂ ∘ Prod.map (sec (GQ V)) (sec (GQ V)) :=
    funext fun q => (congrArg _ (Prod.ext (mk_sec q.1) (mk_sec q.2)).symm).trans (dblIntegrandQ_mk hli _ _)
  have hmp : MeasurePreserving (Prod.map (sec (GQ V)) (sec (GQ V))) ((autMeasure V m).prod (autMeasure V m))
      ((m.restrict 𝓕).prod (m.restrict 𝓕)) := measurePreserving_sec.prod measurePreserving_sec
  have S3 : ∫ q, dblIntegrandQ V μ E f₁ f₂ q ∂(autMeasure V m).prod (autMeasure V m) =
      ∫ x, dblIntegrand V μ E f₁ f₂ x ∂(m.restrict 𝓕).prod (m.restrict 𝓕) := by
    rw [hQ]; exact hmp.integral_comp (measurableEmbedding_sec.prodMap measurableEmbedding_sec) _
  have S4 : ∫ x, dblIntegrand V μ E f₁ f₂ x ∂(m.restrict 𝓕).prod (m.restrict 𝓕) =
      ∑' δ : GQ V, ∫ x, T δ x ∂(m.restrict 𝓕).prod (m.restrict 𝓕) := by
    rw [← integral_tsum (fun δ => (hTc δ).aestronglyMeasurable) hbd]
    congr 1; funext x
    simp only [hTdef, hEdef, dblIntegrand, mul_assoc]
    exact tsum_mul_right.symm
  have S5 : ∀ δ : GQ V, ∫ x, T δ x ∂(m.restrict 𝓕).prod (m.restrict 𝓕) =
      ∫ x₂ in 𝓕, ∫ x₁ in 𝓕, T δ (x₁, x₂) ∂m ∂m := fun δ => integral_prod_symm _ (hTint δ)
  have S6 : ∑' δ : GQ V, ∫ x₂ in 𝓕, ∫ x₁ in 𝓕, T δ (x₁, x₂) ∂m ∂m =
      ∫ x₂ in 𝓕, ∑' δ : GQ V, ∫ x₁ in 𝓕, T δ (x₁, x₂) ∂m ∂m := by
    refine (integral_tsum (fun δ => ?_) ?_).symm
    · exact (((hTc δ).comp continuous_swap).aestronglyMeasurable
        (μ := (m.restrict 𝓕).prod (m.restrict 𝓕))).integral_prod_right'
    · refine ne_top_of_le_ne_top hbd (ENNReal.tsum_le_tsum fun δ => ?_)
      rw [lintegral_prod_symm _ (hTm δ).aemeasurable]
      exact lintegral_mono fun x₂ => enorm_integral_le_lintegral_enorm _
  have S7 : ∀ᵐ x₂ ∂(m.restrict 𝓕), ∑' δ : GQ V, ∫ x₁ in 𝓕, T δ (x₁, x₂) ∂m = ∫ x₁, H (x₁, x₂) ∂m := by
    filter_upwards [hHint] with x₂ hx
    rw [hF.integral_eq_tsum'' _ hx]
    refine tsum_congr fun δ => ?_
    simp only [hT, Subgroup.smul_def, smul_eq_mul]
  have S8 : ∀ x₂, ∫ x₁, H (x₁, x₂) ∂m = ∫ g, K (x₂, g) ∂m := fun x₂ =>
    (integral_mul_left_eq_self (fun x₁ => H (x₁, x₂)) x₂).symm
  have S9 : ∫ x₂ in 𝓕, ∫ g, K (x₂, g) ∂m ∂m = ∫ g, ∫ x₂ in 𝓕, K (x₂, g) ∂m ∂m := by
    rw [← integral_prod _ hKint, integral_prod_symm _ hKint]
  have MirabolicColumnBlock : ∀ g, ∫ x₂ in 𝓕, K (x₂, g) ∂m = φ (io V (g, 1)) * conj (petCoef V m f₁ f₂ g) := fun g => by
    have hl1 : LeftInv (GQ V) (rTr V g f₁) := fun γ hγ x => (h₁.mul_right g).1 γ hγ x
    have hl2 : LeftInv (GQ V) f₂ := h₂.1
    simp only [petCoef]
    rw [petersson_eq hF hl1 hl2, ← integral_conj, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x₂ => ?_)
    simp only [hKdef, hHdef, dblIntegrand_mul hφ, rTr, map_mul, Complex.conj_conj]
    ring
  refine ⟨?_, ?_⟩
  · rw [zetaConvH_iff]
    exact hKint.integral_prod_right.congr (Eventually.of_forall fun g => MirabolicColumnBlock g)
  · calc ∫ q, dblIntegrandQ V μ E f₁ f₂ q ∂(autMeasure V m).prod (autMeasure V m)
        = ∫ x, dblIntegrand V μ E f₁ f₂ x ∂(m.restrict 𝓕).prod (m.restrict 𝓕) := S3
      _ = ∑' δ : GQ V, ∫ x, T δ x ∂(m.restrict 𝓕).prod (m.restrict 𝓕) := S4
      _ = ∑' δ : GQ V, ∫ x₂ in 𝓕, ∫ x₁ in 𝓕, T δ (x₁, x₂) ∂m ∂m := tsum_congr S5
      _ = ∫ x₂ in 𝓕, ∑' δ : GQ V, ∫ x₁ in 𝓕, T δ (x₁, x₂) ∂m ∂m := S6
      _ = ∫ x₂ in 𝓕, ∫ x₁, H (x₁, x₂) ∂m ∂m := integral_congr_ae S7
      _ = ∫ x₂ in 𝓕, ∫ g, K (x₂, g) ∂m ∂m := integral_congr_ae (Eventually.of_forall S8)
      _ = ∫ g, ∫ x₂ in 𝓕, K (x₂, g) ∂m ∂m := S9
      _ = ∫ g, φ (io V (g, 1)) * conj (petCoef V m f₁ f₂ g) ∂m := integral_congr_ae (Eventually.of_forall MirabolicColumnBlock)
      _ = zetaH D.sp.cm.sig (gram_hdbl V) m φ (petCoef V m f₁ f₂) := (zetaH_eq _ _ _ _).symm

end GlobalTheory.Core.Rk.OpenOrbit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingOpenOrbitUnfoldsToAdelicIntegralStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubling_open_orbit_unfolds_to_adelic_integral : ∀ (D : D7) (V : HSp D) (a : GL (Fin V.rank) (AE D)), IsMaj V a → ∀ (μ : (AE D)ˣ →* Circle), IsHeckeChar D μ → ∀ s : ℂ, (V.rank : ℝ) / 2 < s.re → ∀ φ ∈ degPS V a μ s, GlobalTheory.Grow.ModGrowth (dblSp V) (GlobalTheory.Eis.eis V (GlobalTheory.Eis.sph V a (s.re : ℂ))) → ∀ m : Measure (GA D V), m.IsHaarMeasure → ∀ f₁ f₂ : GA D V → ℂ, GlobalTheory.Grow.RapidDec V f₁ → GlobalTheory.Grow.RapidDec V f₂ → ZetaConvH D.sp.cm.sig (gram_hdbl V) m φ (GlobalTheory.Eis.petCoef V m f₁ f₂) ∧ ∫ x, GlobalTheory.Eis.dblIntegrandQ V μ (fun y => ∑' δ : GQ V, φ (io V (δ, 1) * y)) f₁ f₂ x ∂(autMeasure V m).prod (autMeasure V m) = zetaH D.sp.cm.sig (gram_hdbl V) m φ (GlobalTheory.Eis.petCoef V m f₁ f₂) := by
  first | exact @GlobalTheory.Core.Rk.OpenOrbit.open_orbit | exact GlobalTheory.Core.Rk.OpenOrbit.open_orbit | (intros; apply GlobalTheory.Core.Rk.OpenOrbit.open_orbit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingBasicIdentityUnfolding
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

namespace GlobalTheory.Core.Rk.BasicId

open Filter Set GlobalTheory.Eis

theorem measurable_tsum_of_summable' {X I : Type} [MeasurableSpace X] [Countable I]
    (F : I → X → ℂ) (hF : ∀ i, Measurable (F i)) (hs : ∀ x, Summable fun i => F i x) :
    Measurable fun x => ∑' i, F i x :=
  measurable_of_tendsto_metrizable' (atTop : Filter (Finset I))
    (f := fun s x => ∑ i ∈ s, F i x) (fun s => Finset.measurable_sum s fun i _ => hF i)
    (tendsto_pi_nhds.2 fun x => (hs x).hasSum)

theorem out_mul_inv_mem {D : D7} (V : HSp D) (x : GQ (dblSp V)) :
    (((mk ((siegel V).subgroupOf (GQ (dblSp V))) x).out : GQ (dblSp V)) : GA D (dblSp V)) *
      ((x : GA D (dblSp V)))⁻¹ ∈ siegel V := by
  obtain ⟨γ, e⟩ := mk_eq_iff.1 (Quotient.out_eq (mk ((siegel V).subgroupOf (GQ (dblSp V))) x))
  have e' := congrArg (fun z : GQ (dblSp V) => (z : GA D (dblSp V))) e
  simp only [Subgroup.coe_mul] at e'
  rw [← e', mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul]
  exact inv_mem (Subgroup.mem_subgroupOf.1 γ.2)

theorem basicIdentity_unfold : ∀ (D : D7) (V : HSp D) (a : GL (Fin V.rank) (AE D)), IsMaj V a → ∀ (μ : (AE D)ˣ →* Circle), IsHeckeChar D μ → ∀ s : ℂ, (V.rank : ℝ) / 2 < s.re → ∀ φ ∈ degPS V a μ s, GlobalTheory.Grow.ModGrowth (dblSp V) (GlobalTheory.Eis.eis V (GlobalTheory.Eis.sph V a (s.re : ℂ))) → ∀ m : Measure (GA D V), m.IsHaarMeasure → ∀ f₁ f₂ : GA D V → ℂ, GlobalTheory.Grow.RapidDec V f₁ → GlobalTheory.Grow.RapidDec V f₂ → IsCuspFun V f₁ → GlobalTheory.Eis.BasicIdentity V μ m φ f₁ f₂ := by
  intro D V a ha μ hμ s hs φ hφ hgrow m hm f₁ f₂ h₁ h₂ hcusp
  haveI := hm
  haveI : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram
  have hL : LeftInv (siegelQ V) φ := leftInv_of_mem hμ hφ
  have hφc : Continuous φ := hφ.2.1

  have hI : HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a) :=
    GlobalTheory.T.adelicIwasawa_doubledGroup_selfDualLattice D V (frameLat V) a (GlobalTheory.Core.Rk.AbsConv.isSelfDualC_frameLat V) ha
  have hS : SphConv V a := GlobalTheory.Eis.sphConv D V a hI
  have hσ : (V.rank : ℝ) / 2 < ((s.re : ℂ)).re := by simpa using hs
  have hconvS : ∀ g, EisConv V (sph V a (s.re : ℂ)) g := fun g => (((sphConv_iff hI).1 hS).1 _ hσ).2 g
  have h2 : ∀ g, sph V a (s.re : ℂ) g = (((hgt V a g : ℝ) ^ (s.re + (V.rank : ℝ) / 2) : ℝ) : ℂ) := fun g => by
    rw [Complex.ofReal_cpow (NNReal.coe_nonneg _)]; push_cast; rfl
  have hr0 : ∀ g, 0 ≤ (hgt V a g : ℝ) ^ (s.re + (V.rank : ℝ) / 2) := fun g =>
    Real.rpow_nonneg (NNReal.coe_nonneg _) _
  have hn : ∀ g, ‖sph V a (s.re : ℂ) g‖ = (hgt V a g : ℝ) ^ (s.re + (V.rank : ℝ) / 2) := fun g => by
    rw [h2, Complex.norm_real, Real.norm_of_nonneg (hr0 g)]
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C * (hgt V a g : ℝ) ^ (s.re + (V.rank : ℝ) / 2) := by
    haveI := t2Space_adeleRing' (F := D.host.F)
    exact hI.exists_norm_le continuous_absE (isCompact_Khat V a) hφ
  have hsum : ∀ y, Summable fun q : SiegelCosets V => φ (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * y) :=
    fun y => Summable.of_norm (((hconvS y).of_norm_le (C := max C 0) fun g =>
      (hC g).trans (by rw [hn]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) (hr0 g))) : EisConv V φ y)

  set P : Set (SiegelCosets V) := {q | ∃ δ ∈ GQ V, ((q.out : GQ (dblSp V)) : GA D (dblSp V)) * (io V (δ, 1))⁻¹ ∈ siegel V}
    with hP
  let e0 : GQ V → P := fun δ => ⟨mk _ ⟨io V ((δ : GA D V), 1), io_mem_GQ V δ.2 (one_mem _)⟩,
    ⟨δ, δ.2, out_mul_inv_mem V ⟨io V ((δ : GA D V), 1), io_mem_GQ V δ.2 (one_mem _)⟩⟩⟩
  have hbij : Function.Bijective e0 := by
    refine ⟨fun δ δ' h => injective_mk_io (congrArg Subtype.val h), fun q => ?_⟩
    obtain ⟨δ, hδ, hq⟩ := q.2
    refine ⟨⟨δ, hδ⟩, Subtype.ext ?_⟩
    have hm' : (q.1.out : GQ (dblSp V)) * (⟨io V (δ, 1), io_mem_GQ V hδ (one_mem _)⟩ : GQ (dblSp V))⁻¹ ∈
        (siegel V).subgroupOf (GQ (dblSp V)) := Subgroup.mem_subgroupOf.2 (by simpa using hq)
    exact (mk_eq_iff.2 ⟨⟨_, hm'⟩, by simp⟩).trans q.1.out_eq
  have hterm : ∀ (δ : GQ V) y, φ ((((e0 δ).1.out : GQ (dblSp V)) : GA D (dblSp V)) * y) = φ (io V ((δ : GA D V), 1) * y) :=
    fun δ y => term_mk hL y ⟨io V ((δ : GA D V), 1), io_mem_GQ V δ.2 (one_mem _)⟩
  obtain ⟨Eo, hEo⟩ : ∃ Eo : GA D (dblSp V) → ℂ, Eo = fun y => ∑' δ : GQ V, φ (io V (δ, 1) * y) := ⟨_, rfl⟩
  obtain ⟨En, hEn⟩ : ∃ En : GA D (dblSp V) → ℂ, En = fun y => ∑' q : {q : GlobalTheory.Eis.SiegelCosets V // ¬ ∃ δ ∈ GQ V,
      ((q.out : GQ (dblSp V)) : GA D (dblSp V)) * (io V (δ, 1))⁻¹ ∈ siegel V},
      φ (((q.1.out : GQ (dblSp V)) : GA D (dblSp V)) * y) := ⟨_, rfl⟩
  have hEoP : ∀ y, Eo y = ∑' q : P, φ (((q.1.out : GQ (dblSp V)) : GA D (dblSp V)) * y) := fun y => by
    rw [hEo, ← (Equiv.ofBijective e0 hbij).tsum_eq]
    exact tsum_congr fun δ => (hterm δ y).symm
  have hsumO : ∀ y, Summable fun δ : GQ V => φ (io V ((δ : GA D V), 1) * y) := fun y => by
    have := ((Equiv.ofBijective e0 hbij).summable_iff (f := fun q : P =>
      φ (((q.1.out : GQ (dblSp V)) : GA D (dblSp V)) * y))).2 ((hsum y).subtype (fun q => q ∈ P))
    exact this.congr fun δ => hterm δ y
  have hsplit : ∀ y, eis V φ y = Eo y + En y := fun y => by
    rw [hEoP, hEn]
    exact ((hsum y).tsum_subtype_add_tsum_subtype_compl P).symm

  have hEoInv : ∀ γ ∈ (GQ V).prod (GQ V), ∀ y, Eo (io V γ * y) = Eo y := by
    rintro ⟨γ₁, γ₂⟩ ⟨h1, h2⟩ y
    let e : GQ V ≃ GQ V := (Equiv.mulLeft (⟨γ₂, h2⟩ : GQ V)⁻¹).trans (Equiv.mulRight ⟨γ₁, h1⟩)
    rw [hEo]
    show ∑' δ : GQ V, φ (io V ((δ : GA D V), 1) * (io V (γ₁, γ₂) * y)) = ∑' δ : GQ V, φ (io V ((δ : GA D V), 1) * y)
    rw [← e.tsum_eq (fun δ : GQ V => φ (io V ((δ : GA D V), 1) * y))]
    refine tsum_congr fun δ => ?_
    have hd : io V ((δ : GA D V), 1) * (io V (γ₁, γ₂) * y) = io V (γ₂, γ₂) * (io V (((e δ : GQ V) : GA D V), 1) * y) := by
      rw [← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul]
      congr 2
      refine Prod.ext ?_ ?_
      · simp [e, mul_assoc]
      · simp
    rw [hd, hL _ ⟨(io_mem_siegel V).2 rfl, io_mem_GQ V h2 h2⟩]
  have hi : LeftInv ((GQ V).prod (GQ V)) (dblIntegrand V μ Eo f₁ f₂) := fun γ hγ g => by
    simp only [dblIntegrand, map_mul (io V), hEoInv γ hγ, Prod.fst_mul, Prod.snd_mul, h₁.1 _ hγ.1, h₂.1 _ hγ.2,
      map_mul (detA V), map_mul μ, apply_detA hμ hγ.2, one_mul]

  have hEom : Measurable Eo := by
    rw [hEo]
    exact measurable_tsum_of_summable' (fun δ : GQ V => fun y => φ (io V ((δ : GA D V), 1) * y))
      (fun δ => (hφc.comp (continuous_const.mul continuous_id)).measurable) hsumO
  have hDm : Measurable (dblIntegrand V μ Eo f₁ f₂) := by
    have e : dblIntegrand V μ Eo f₁ f₂ = fun g => Eo (io V g) * dblIntegrand V μ (fun _ => 1) f₁ f₂ g :=
      funext fun g => by simp only [dblIntegrand]; ring
    rw [e]
    exact (hEom.comp (continuous_io V).measurable).mul
      (continuous_dblIntegrand hμ continuous_const h₁.continuous h₂.continuous).measurable

  have h𝓕 := isFundamentalDomain_stdDom (GQ V) m
  have habs := GlobalTheory.Core.Rk.AbsConv.absConv_unfolded D V a ha μ hμ s hs φ hφ hgrow m hm f₁ f₂ h₁ h₂
  have hfin := habs.1 _ h𝓕
  have hmeasq : ∀ q : SiegelCosets V, AEMeasurable (fun x =>
      ‖dblIntegrand V μ (fun x => φ (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * x)) f₁ f₂ x‖ₑ)
      ((m.prod m).restrict (stdDom (GQ V) ×ˢ stdDom (GQ V))) := fun q =>
    (continuous_dblIntegrand hμ (hφc.comp (continuous_const.mul continuous_id)) h₁.continuous
      h₂.continuous).measurable.enorm.aemeasurable
  have hpt : ∀ x, ‖dblIntegrand V μ Eo f₁ f₂ x‖ₑ ≤ ∑' q : SiegelCosets V,
      ‖dblIntegrand V μ (fun x => φ (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * x)) f₁ f₂ x‖ₑ := fun x => by
    simp only [GlobalTheory.Core.Rk.AbsConv.enorm_dblIntegrand]
    rw [ENNReal.tsum_mul_right]
    gcongr ?_ * _
    rw [hEoP]
    exact enorm_tsum_le_tsum_enorm.trans (tsum_comp_le_tsum_of_injective (f := fun q : P => q.1) Subtype.val_injective
      (fun q : SiegelCosets V => ‖φ (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * io V x)‖ₑ))
  have hOn : IntegrableOn (dblIntegrand V μ Eo f₁ f₂) (stdDom (GQ V) ×ˢ stdDom (GQ V)) (m.prod m) := by
    refine ⟨hDm.aestronglyMeasurable, ?_⟩
    show ∫⁻ x in stdDom (GQ V) ×ˢ stdDom (GQ V), ‖dblIntegrand V μ Eo f₁ f₂ x‖ₑ ∂m.prod m < ⊤
    calc _ ≤ ∫⁻ x in stdDom (GQ V) ×ˢ stdDom (GQ V), ∑' q : SiegelCosets V,
          ‖dblIntegrand V μ (fun x => φ (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * x)) f₁ f₂ x‖ₑ ∂m.prod m :=
          lintegral_mono hpt
      _ = _ := lintegral_tsum hmeasq
      _ < ⊤ := hfin.lt_top
  have hEoC : DblConv V μ m Eo f₁ f₂ := (dblConv_iff hi hDm h𝓕).2 hOn

  have hQ : ∀ q, dblIntegrandQ V μ (eis V φ) f₁ f₂ q = dblIntegrandQ V μ Eo f₁ f₂ q + dblIntegrandQ V μ En f₁ f₂ q :=
    fun q => by simp only [dblIntegrandQ, dblIntegrand, hsplit]; ring
  have hEnI : Integrable (dblIntegrandQ V μ En f₁ f₂) ((autMeasure V m).prod (autMeasure V m)) :=
    (habs.2.2.sub hEoC.2).congr (Eventually.of_forall fun q => by simp only [Pi.sub_apply, hQ]; ring)
  have h6 := GlobalTheory.T.doubling_integral_negligible_orbits_eq_zero_cuspForm D V a ha μ hμ s hs φ hφ hgrow m hm f₁ f₂ h₁ h₂ hcusp
  have h7 := GlobalTheory.T.doubling_open_orbit_unfolds_to_adelic_integral D V a ha μ hμ s hs φ hφ hgrow m hm f₁ f₂ h₁ h₂
  rw [← hEn] at h6
  rw [← hEo] at h7
  refine ⟨habs.2, h7.1, ?_⟩
  show ∫ q, dblIntegrandQ V μ (eis V φ) f₁ f₂ q ∂(autMeasure V m).prod (autMeasure V m) = _
  rw [integral_congr_ae (Eventually.of_forall hQ), integral_add hEoC.2 hEnI, h7.2, h6, add_zero]

end GlobalTheory.Core.Rk.BasicId

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingBasicIdentityUnfoldingStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubling_basicIdentity_unfolding : ∀ (D : D7) (V : HSp D) (a : GL (Fin V.rank) (AE D)), IsMaj V a → ∀ (μ : (AE D)ˣ →* Circle), IsHeckeChar D μ → ∀ s : ℂ, (V.rank : ℝ) / 2 < s.re → ∀ φ ∈ degPS V a μ s, GlobalTheory.Grow.ModGrowth (dblSp V) (GlobalTheory.Eis.eis V (GlobalTheory.Eis.sph V a (s.re : ℂ))) → ∀ m : Measure (GA D V), m.IsHaarMeasure → ∀ f₁ f₂ : GA D V → ℂ, GlobalTheory.Grow.RapidDec V f₁ → GlobalTheory.Grow.RapidDec V f₂ → IsCuspFun V f₁ → GlobalTheory.Eis.BasicIdentity V μ m φ f₁ f₂ := by
  first | exact @GlobalTheory.Core.Rk.BasicId.basicIdentity_unfold | exact GlobalTheory.Core.Rk.BasicId.basicIdentity_unfold | (intros; apply GlobalTheory.Core.Rk.BasicId.basicIdentity_unfold <;> assumption)
end
