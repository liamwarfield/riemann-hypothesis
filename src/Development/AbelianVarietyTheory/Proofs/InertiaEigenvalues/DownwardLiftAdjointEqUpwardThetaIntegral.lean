module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictionLineOperatorSum

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjointFormulaOfKernel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.AdjUp

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def upVec (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℂ (R.cV i).W) (y : (R.HW i (sg0 D A)).H) : GA D (Vc D i) → (R.cV i).W :=
  fun h => ∑ k, upLift (R.ωP i t) (R.νW i) (R.fdW i) (jointVec R i t v (b k)) (val R i v y) h • b k

theorem val_zero (R : RealDat D A Ks) (i : Fin D.R.m) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) :
    val R i v 0 = 0 := by
  funext g
  simp [val]

theorem upLift_zero {V W : HSp D} (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ν : Measure (GA D W))
    (𝓖 : Set (GA D W)) (f : WO V W → ℂ) (h : GA D V) : upLift om ν 𝓖 f 0 h = 0 := by
  simp [upLift]

end GlobalTheory.AdjUp

end

namespace GlobalTheory.AdjUp

theorem adjoint_formula_of_kernel {H₁ H₂ W Gv Gw : Type} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    [FiniteDimensional ℂ H₁] [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [FiniteDimensional ℂ H₂]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [MeasurableSpace Gv] [MeasurableSpace Gw]
    (th : H₁ →ₗ[ℂ] H₂) {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ W) (μW : Measure Gw) (μV : Measure Gv)
    (φ : H₂ → Gw → ℂ) (ψ : H₁ → Gw → ℂ) (ext : H₁ →ₗ[ℂ] (Gv → W)) (K : Fin n → H₂ → Gv → ℂ) (P c : ℝ)
    (hP0 : 0 ≤ P) (hc : 0 < c)
    (hPW : ∀ y z, ⟪y, z⟫_ℂ = (P : ℂ) * ∫ g, star (φ y g) * φ z g ∂μW)
    (hφ : ∀ u, φ (th u) = ψ u) (hφ0 : φ 0 = 0) (hK0 : ∀ k h, K k 0 h = 0)
    (hcV : ∀ u u', ⟪u, u'⟫_ℂ = (c : ℂ) * ∫ h, ⟪ext u h, ext u' h⟫_ℂ ∂μV ∧
      ∀ a a' : W, Integrable (fun h => star ⟪a, ext u h⟫_ℂ * ⟪a', ext u' h⟫_ℂ) μV)
    (h3 : ∀ y u, ∫ g, star (φ y g) * ψ u g ∂μW = ∫ h, ⟪∑ k, K k y h • b k, ext u h⟫_ℂ ∂μV)
    (h4 : ∀ y, ∃ u, ext u = fun h => ∑ k, K k y h • b k) :
    ∃ a : ℝ, 0 < a ∧ ∀ x y, ⟪LinearMap.adjoint th x, LinearMap.adjoint th y⟫_ℂ =
      (a : ℂ) * ∑ k, ∫ h, star (K k x h) * K k y h ∂μV := by
  choose U hU using h4
  have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  have hcoord : ∀ y k h, ⟪b k, ext (U y) h⟫_ℂ = K k y h := fun y k h => by
    rw [hU y]; exact b.orthonormal.inner_right_fintype _ k
  have hadj : ∀ y u, ⟪LinearMap.adjoint th y, u⟫_ℂ = (((P / c : ℝ)) : ℂ) * ⟪U y, u⟫_ℂ := by
    intro y u
    rw [LinearMap.adjoint_inner_left, hPW, hφ, h3, (hcV (U y) u).1, hU y, Complex.ofReal_div]
    field_simp
  have hsum : ∀ x y h, ⟪ext (U x) h, ext (U y) h⟫_ℂ = ∑ k, star (K k x h) * K k y h := by
    intro x y h
    rw [← b.sum_inner_mul_inner]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hcoord, ← hcoord, ← inner_conj_symm]
    rfl
  by_cases hzero : P = 0
  · refine ⟨1, one_pos, fun x y => ?_⟩
    have h0 : ∀ z : H₂, z = 0 := fun z => by
      have := hPW z z
      rw [hzero, Complex.ofReal_zero, zero_mul] at this
      exact inner_self_eq_zero.1 this
    rw [h0 x, h0 y, map_zero, inner_zero_left]
    simp [hK0]
  · have hpos : 0 < P := lt_of_le_of_ne hP0 (Ne.symm hzero)
    refine ⟨P ^ 2 / c, by positivity, fun x y => ?_⟩
    have hint : ∀ k ∈ Finset.univ, Integrable (fun h => star (K k x h) * K k y h) μV := by
      intro k _
      have := (hcV (U x) (U y)).2 (b k) (b k)
      simpa only [hcoord] using this
    have e1 : ⟪LinearMap.adjoint th x, LinearMap.adjoint th y⟫_ℂ =
        (((P / c : ℝ)) : ℂ) * (((P / c : ℝ)) : ℂ) * ⟪U x, U y⟫_ℂ := by
      rw [hadj x, ← inner_conj_symm, hadj y, map_mul, Complex.conj_ofReal, inner_conj_symm, mul_assoc]
    have e2 : ⟪U x, U y⟫_ℂ = (c : ℂ) * ∑ k, ∫ h, star (K k x h) * K k y h ∂μV := by
      rw [(hcV (U x) (U y)).1, ← integral_finsetSum _ hint]
      simp only [hsum]
    rw [e1, e2]
    push_cast
    field_simp

end GlobalTheory.AdjUp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UpwardVectorLiftMemRangeCoefficientExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UpwardVectorLiftMemRangeCoefficientExtension
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.AdjUp

noncomputable section

namespace GlobalTheory.AdjRange

open GlobalTheory.TraceIncl

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem inner_sum_eq {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℂ W) (Φ : W → ℂ) (hadd : ∀ w w', Φ (w + w') = Φ w + Φ w')
    (hsmul : ∀ (c : ℂ) w, Φ (c • w) = star c * Φ w) (w : W) :
    ⟪w, ∑ k, Φ (b k) • b k⟫_ℂ = Φ w := by
  have hsum : ∀ s : Finset (Fin n), Φ (∑ k ∈ s, ⟪b k, w⟫_ℂ • b k) = ∑ k ∈ s, star ⟪b k, w⟫_ℂ * Φ (b k) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have h0 := hsmul 0 0
      simp only [zero_smul, star_zero, zero_mul] at h0
      simpa using h0
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, hsmul, ih]
  conv_rhs => rw [← b.sum_repr' w]
  rw [hsum, inner_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [inner_smul_right, mul_comm]
  congr 1
  exact (inner_conj_symm (𝕜 := ℂ) w (b k)).symm

theorem star_inv_of_finOrder (u : ℂˣ) (hu : IsOfFinOrder u) : star (((u⁻¹ : ℂˣ) : ℂ)) = (u : ℂ) := by
  obtain ⟨n, hn, hpow⟩ := hu.exists_pow_eq_one
  have h1 : ‖(u : ℂ)‖ = 1 := by
    have : ‖(u : ℂ)‖ ^ n = 1 := by
      rw [← norm_pow, ← Units.val_pow_eq_pow_val, hpow, Units.val_one, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 this
  have hne : (u : ℂ) ≠ 0 := u.ne_zero
  rw [Units.val_inv_eq_inv_val, star_inv₀, Complex.star_def, Complex.inv_def, Complex.normSq_eq_norm_sq,
    Complex.norm_conj, h1]
  simp

variable (R : RealDat D A Ks) (i : Fin D.R.m) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (y : (R.HW i (sg0 D A)).H)

def phi (K : (R.cV i).W →ₗ[ℂ] Ser R i) (w : (R.cV i).W) : ℂ :=
  ∫ g in R.fdW i, star (K w v g) * val R i v y g ∂(R.νW i)

def coVec {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ (R.cV i).W) (K : (R.cV i).W →ₗ[ℂ] Ser R i) : (R.cV i).W :=
  ∑ k, phi R i v y K (b k) • b k

theorem inner_coVec {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ (R.cV i).W) (K : (R.cV i).W →ₗ[ℂ] Ser R i)
    (hI : ∀ w, IntegrableOn (fun g => star (K w v g) * val R i v y g) (R.fdW i) (R.νW i)) (w : (R.cV i).W) :
    ⟪w, coVec R i v y b K⟫_ℂ = phi R i v y K w := by
  refine inner_sum_eq b _ (fun w w' => ?_) (fun c w => ?_) w
  · unfold phi
    rw [← integral_add (hI w) (hI w')]
    refine integral_congr_ae (.of_forall fun g => ?_)
    simp only [map_add (f := _), Pi.add_apply, star_add, add_mul]
  · unfold phi
    rw [← integral_const_mul]
    refine integral_congr_ae (.of_forall fun g => ?_)
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, star_mul', mul_assoc]

end GlobalTheory.AdjRange

namespace GlobalTheory.AdjRange

open GlobalTheory.TraceIncl

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem integrable_kernA (hP : GlobalTheory.Published.CuspRapidDecay) (R : RealDat D A Ks) (F : Face D A) (hL : Laws R F)
    (i : Fin D.R.m) (t : T) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (y : (R.HW i (sg0 D A)).H) (h : GA D (Vc D i))
    (w : (R.cV i).W) :
    IntegrableOn (fun g => star (kernA R i t h w v g) * val R i v y g) (R.fdW i) (R.νW i) := by
  have hω := hL.thP.ωP i t
  have hf := hL.thP.pt_theta i t (R.ioP i (PiTensorProduct.tprod ℂ v) ((R.cV i).ρ h⁻¹ w))
  have hMem : (R.HW i (sg0 D A)).e y ∈ R.Wall i (sg0 D A) := by
    rw [← (hL.models.HW i (sg0 D A)).2.1]
    exact LinearMap.mem_range_self _ y
  have hMM := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 hMem
  have hR : GlobalTheory.Grow.RapidDec (Wc D i) (val R i v y) :=
    GlobalTheory.Grow.rapidDec_of_cuspForm hP hL.models.inf (hMM.aut _) (hMM.cusp _)
  have : BorelSpace (GA D (Wc D i)) := ⟨rfl⟩
  have hm : GlobalTheory.Grow.ModGrowth (Wc D i) (fun g => star (thetaKO (R.ωP i t) h g
      (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) ((R.cV i).ρ h⁻¹ w))))) :=
    ((GlobalTheory.Core.Rk.ThetaGrowthBoth.thetaKO_modGrowth₂ D _ _ _ _ _ _ hω _ hf).right h).of_le
      (fun g => (norm_star _).le)
  have hl : ∀ γ ∈ GQ (Wc D i), ∀ g, star (thetaKO (R.ωP i t) h (γ * g)
      (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) ((R.cV i).ρ h⁻¹ w)))) =
      star (thetaKO (R.ωP i t) h g (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) ((R.cV i).ρ h⁻¹ w)))) :=
    fun γ hγ g => by rw [GlobalTheory.Chain.LiftConv.thetaKO_left hω hf h γ hγ g]
  have hms := ((GlobalTheory.Chain.LiftConv.thetaKO_continuous hω hf h).star).measurable.aestronglyMeasurable
    (μ := (R.νW i).restrict (R.fdW i))
  exact hR.integrableOn_modGrowth_mul (hL.models.νW i).1.1 (hL.models.νW i).2 hm hl hms

theorem integrable_kern (hP : GlobalTheory.Published.CuspRapidDecay) (R : RealDat D A Ks) (F : Face D A) (hL : Laws R F)
    (i : Fin D.R.m) (t : T) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (y : (R.HW i (sg0 D A)).H)
    (x : Formalism.IndefR.Bridge.Gf (Vc D i)) (w : (R.cV i).W) :
    IntegrableOn (fun g => star (kern R i t x w v g) * val R i v y g) (R.fdW i) (R.νW i) := by
  obtain ⟨h, -, rfl⟩ := KernLaws.exists_finite_lift _ x
  rw [KernLaws.kern_fin R i t hL.thP.ioP]
  exact integrable_kernA hP R F hL i t v y h w

theorem inner_rho (R : RealDat D A Ks) (F : Face D A) (hL : Laws R F) (i : Fin D.R.m) (h : GA D (Vc D i))
    (x z : (R.cV i).W) : ⟪x, (R.cV i).ρ h z⟫_ℂ = ⟪(R.cV i).ρ h⁻¹ x, z⟫_ℂ := by
  rw [← (hL.models.cV i).2.1 h⁻¹ x ((R.cV i).ρ h z), ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
    Module.End.one_apply]

theorem upVec_eq (hP : GlobalTheory.Published.CuspRapidDecay) (R : RealDat D A Ks) (F : Face D A) (hL : Laws R F)
    (i : Fin D.R.m) (t : T) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℂ (R.cV i).W) (y : (R.HW i (sg0 D A)).H) (h : GA D (Vc D i)) :
    upVec R i t v b y h = (R.cV i).ρ h⁻¹ (coVec R i v y b (kern R i t (Formalism.IndefR.FWT.fin (Vc D i) h))) := by
  have hinv : ∀ x : (R.cV i).W, (R.cV i).ρ h⁻¹ ((R.cV i).ρ h x) = x := fun x => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hin := inner_coVec R i v y b (kernA R i t h) (integrable_kernA hP R F hL i t v y h)
  apply ext_inner_left ℂ
  intro w
  rw [inner_rho R F hL, inv_inv, KernLaws.kern_fin R i t hL.thP.ioP, hin]
  have e2 : upVec R i t v b y h = ∑ k, phi R i v y (kernA R i t h) ((R.cV i).ρ h (b k)) • b k := by
    unfold upVec
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    unfold upLift phi
    refine integral_congr_ae (.of_forall fun g => ?_)
    dsimp only
    rw [KernLaws.kernA_apply, hinv]
    rfl
  rw [e2]
  refine inner_sum_eq b (fun w => phi R i v y (kernA R i t h) ((R.cV i).ρ h w)) (fun w w' => ?_) (fun c w => ?_) w
  · simp only [map_add (f := _), ← hin, inner_add_left]
  · simp only [map_smul, ← hin, inner_smul_left, Complex.star_def]


set_option maxHeartbeats 1000000 in
theorem coVec_level (R : RealDat D A Ks) (F : Face D A) (hL : Laws R F) (i : Fin D.R.m) (t : T)
    (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ (R.cV i).W)
    (y : (R.HW i (sg0 D A)).H) (hT : DatumType R i t) (z : Formalism.IndefR.Bridge.Gf (Vc D i))
    (k : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).J) :
    coVec R i v y b (kern R i t (z * k)) =
      (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ k : ℂˣ) : ℂ) • coVec R i v y b (kern R i t z) := by
  have hlev := (kern_laws R i t hL.models.inf hL.models.cV hL.thP.ωP hL.thP.pt_theta hL.thP.ioP hT).2.2.1
  unfold coVec
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul]
  congr 1
  unfold phi
  rw [← integral_const_mul]
  refine integral_congr_ae (.of_forall fun g => ?_)
  rw [hlev]
  simp only [Pi.smul_apply, smul_eq_mul, star_mul']
  rw [star_inv_of_finOrder _ (GlobalTheory.LevelCharOrder.levEnv_chi_isOfFinOrder (Vc D i) (R.βV i) (R.datVt i t) k), mul_assoc]

theorem coVec_rat (hP : GlobalTheory.Published.CuspRapidDecay) (R : RealDat D A Ks) (F : Face D A) (hL : Laws R F)
    (i : Fin D.R.m) (t : T) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ (R.cV i).W)
    (y : (R.HW i (sg0 D A)).H) (hT : DatumType R i t) (γ : GQ (Vc D i)) (x : Formalism.IndefR.Bridge.Gf (Vc D i)) :
    coVec R i v y b (kern R i t (Formalism.IndefR.Bridge.ratF (Vc D i) γ * x)) =
      (R.cV i).ρ (γ : GA D (Vc D i)) (coVec R i v y b (kern R i t x)) := by
  have hrat := (kern_laws R i t hL.models.inf hL.models.cV hL.thP.ωP hL.thP.pt_theta hL.thP.ioP hT).2.1
  apply ext_inner_left ℂ
  intro w
  rw [inner_coVec R i v y b _ (integrable_kern hP R F hL i t v y _), inner_rho R F hL,
    inner_coVec R i v y b _ (integrable_kern hP R F hL i t v y x)]
  unfold phi
  have e := hrat γ x ((R.cV i).ρ (γ : GA D (Vc D i))⁻¹ w)
  have e' : (R.cV i).coef.ρ γ ((R.cV i).ρ (γ : GA D (Vc D i))⁻¹ w) = w := by
    show (R.cV i).ρ (γ : GA D (Vc D i)) ((R.cV i).ρ (γ : GA D (Vc D i))⁻¹ w) = w
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [e'] at e
  rw [e]

theorem coefExt_apply {V : HSp D} (c : CoefA V) (f : Formalism.IndefR.Bridge.Gf V → c.W) (h : GA D V) :
    c.ext f h = c.ρ h⁻¹ (f (Formalism.IndefR.FWT.fin V h)) := rfl


set_option maxHeartbeats 2000000 in
theorem upVec_mem_range : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ (R.cV i).W) (y : (R.HW i (sg0 D A)).H), ∃ u : (R.HV i t).H, R.extV i t u = upVec R i t v b y := by
  intro hP D G _ _ Pl0 T A Ks _ _ _ R F hL _ i t v n b y
  have hT : DatumType R i t := fun g0 κ κ' h1 h2 =>
    GlobalTheory.VecInv.omega_lifts_vP R hL.lev hL.models.inf hL.thP.ωP hL.thP.vP i t g0 κ κ' h1 h2
  obtain ⟨f, hfd⟩ : ∃ f : Formalism.IndefR.Bridge.Gf (Vc D i) → (R.cV i).W, ∀ x, f x = coVec R i v y b (kern R i t x) :=
    ⟨_, fun _ => rfl⟩
  have hext : (R.cV i).ext f = upVec R i t v b y := by
    funext h
    rw [coefExt_apply, upVec_eq hP R F hL i t v b y h, hfd]
  have hmem : ∀ (γ : GQ (Vc D i)) (x : Formalism.IndefR.Bridge.Gf (Vc D i)) (k : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).J),
      f (Formalism.IndefR.Bridge.ratF (Vc D i) γ * x * k) =
        (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ k : ℂˣ) : ℂ) • (R.cV i).ρ (γ : GA D (Vc D i)) (f x) := by
    intro γ x k
    rw [hfd, hfd]
    exact (coVec_level R F hL i t v b y hT (Formalism.IndefR.Bridge.ratF (Vc D i) γ * x) k).trans
      (congrArg _ (coVec_rat hP R F hL i t v b y hT γ x))
  obtain ⟨u, hu⟩ : f ∈ LinearMap.range (R.HV i t).e := by
    rw [(hL.models.HV i t).2.1]
    exact hmem
  refine ⟨u, ?_⟩
  show (R.cV i).ext ((R.HV i t).e u) = _
  rw [hu, hext]

end GlobalTheory.AdjRange
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UpwardVectorLiftMemRangeCoefficientExtensionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.AdjUp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.upwardVectorLift_mem_range_coefficientExtension : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ (R.cV i).W) (y : (R.HW i (sg0 D A)).H), ∃ u : (R.HV i t).H, R.extV i t u = upVec R i t v b y := by
  first | exact @GlobalTheory.AdjRange.upVec_mem_range | exact GlobalTheory.AdjRange.upVec_mem_range | (intros; apply GlobalTheory.AdjRange.upVec_mem_range <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjointPairingUnfoldingDownwardLift
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjointPairingUnfoldingDownwardLift
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.AdjUp
open GlobalTheory.Grow
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.AdjUnfold


set_option maxHeartbeats 4000000 in
theorem integral_val_thF_eq : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ (R.cV i).W) (y : (R.HW i (sg0 D A)).H) (u : (R.HV i t).H), ∫ g in R.fdW i, star (val R i v y g) * R.thF i t u (fun ρ => v ρ) g ∂(R.νW i) = ∫ h in R.fdV i t, ⟪upVec R i t v b y h, R.extV i t u h⟫_ℂ ∂(R.νV i t) := by
  intro hP D G _ _ Pl0 T A Ks _ _ _ R F hL _ i t v n b y u
  have hm := hL.models
  have hθ : IsInfFam R.θ := hm.inf
  have hω := hL.thP.ωP i t
  have hpt := hL.thP.pt_theta i t
  have hp : (Vc D i).IsPosDef := hm.vpos i
  have hpd : ∀ τ, (gramAt D (Vc D i) τ).PosDef := fun τ =>
    GlobalTheory.RepsObj.gramAt_posDef hp (D.sp.V_sig ((i : ℕ) + 1)) τ
  have hHV : (R.νV i t).IsHaarMeasure := (hm.νV i t).1.1
  have hfdV : IsFundamentalDomain (GQ (Vc D i)) (R.fdV i t) (R.νV i t) := (hm.νV i t).2
  have hHW : (R.νW i).IsHaarMeasure := (hm.νW i).1.1
  have hfdW : IsFundamentalDomain (GQ (Wc D i)) (R.fdW i) (R.νW i) := (hm.νW i).2
  have hJt : ∀ k, IsThetaFunO R.ψ (Vc D i) (Wc D i) (jointVec R i t v (b k)) := fun k => hpt _
  have hx := (hm.HV i t).2.1.le (LinearMap.mem_range_self _ u)
  have hFc : Continuous (R.extV i t u) :=
    GlobalTheory.ThetaIntegrand.ext_continuous (R.cV i) (hm.cV i) (R.βV i) (R.datVt i t) hx
  have hFi : ∀ γ ∈ GQ (Vc D i), ∀ h, R.extV i t u (γ * h) = R.extV i t u h :=
    GlobalTheory.ThetaIntegrand.ext_invariant (R.cV i) hx
  obtain ⟨K, hK, hKc⟩ := GlobalTheory.definite_unitary_cocompact (Vc D i) hpd
  have hGk : ∀ k, RapidDec (Vc D i) (fun h => ⟪R.extV i t u h, b k⟫_ℂ) := fun k =>
    RapidDec.of_isCompact (fun γ hγ h => by simp only [hFi γ hγ h]) (hFc.inner continuous_const) hK
      (fun g => by
        obtain ⟨γ, hγ, c', hc', e⟩ := hKc g
        exact ⟨γ⁻¹, inv_mem hγ, by rw [e, inv_mul_cancel_left]; exact hc'⟩)
  obtain ⟨-, hr, -⟩ := hm.HW i (sg0 D A)
  have hTm : IsMultMap R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv))
      (levChi _ (R.βW i) (R.datWp i R.triv)) ((R.HW i (sg0 D A)).e y) :=
    (GlobalTheory.MultMem.mem_mult_iff ..).1 (by
      have : (R.HW i (sg0 D A)).e y ∈ R.Wall i (sg0 D A) := hr ▸ LinearMap.mem_range_self _ y
      exact this)
  have hF : RapidDec (Wc D i) (fun g => starRingEnd ℂ (val R i v y g)) :=
    (rapidDec_of_cuspForm hP hθ (hTm.aut fun ρ => v ρ) (hTm.cusp fun ρ => v ρ)).conj
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Fin n → GA D (Wc D i) → GA D (Vc D i) → ℂ, Φ = fun k g h =>
      thetaKO (R.ωP i t) h g (jointVec R i t v (b k)) * starRingEnd ℂ (val R i v y g) *
        starRingEnd ℂ ⟪R.extV i t u h, b k⟫_ℂ := ⟨_, rfl⟩
  have hint : ∀ k, Integrable (Function.uncurry (Φ k))
      (((R.νW i).restrict (R.fdW i)).prod ((R.νV i t).restrict (R.fdV i t))) := fun k => by
    rw [hΦ]
    exact GlobalTheory.ChainOnto.ThetaSwap.integrable_prod hθ hω (hJt k) hHV hfdV hHW hfdW (hGk k) hF
  have hthF : ∀ g, R.thF i t u (fun ρ => v ρ) g = ∫ h in R.fdV i t, thetaKO (R.ωP i t) h g
      (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) ((R.cV i).ext ((R.HV i t).e u) h))) ∂(R.νV i t) :=
    fun g => (hL.thP.thF i t).elim fun _ h => (congrFun (h.2 u v) g).trans
      (h.1.eq ((R.extV i t).rangeRestrict u) (PiTensorProduct.tprod ℂ v) g)
  have hexp : ∀ g h, thetaKO (R.ωP i t) h g
      (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) ((R.cV i).ext ((R.HV i t).e u) h))) =
      ∑ k, ⟪b k, R.extV i t u h⟫_ℂ * thetaKO (R.ωP i t) h g (jointVec R i t v (b k)) := by
    intro g h
    have e : (R.cV i).ext ((R.HV i t).e u) h = ∑ k, ⟪b k, R.extV i t u h⟫_ℂ • b k := (b.sum_repr' _).symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e, map_sum]
    unfold jointVec RealDat.ptP
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, thetaKO, LinearMap.sum_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
  have hL1 : ∀ᵐ g ∂((R.νW i).restrict (R.fdW i)), star (val R i v y g) * R.thF i t u (fun ρ => v ρ) g =
      ∑ k, ∫ h in R.fdV i t, Φ k g h ∂(R.νV i t) := by
    have hae : ∀ᵐ g ∂((R.νW i).restrict (R.fdW i)), ∀ k,
        Integrable (fun h => Φ k g h) ((R.νV i t).restrict (R.fdV i t)) :=
      ae_all_iff.2 fun k => (hint k).prod_right_ae
    filter_upwards [hae] with g hg
    rw [hthF g, ← integral_const_mul]
    have e : ∀ h, star (val R i v y g) * thetaKO (R.ωP i t) h g
        (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) ((R.cV i).ext ((R.HV i t).e u) h))) = ∑ k, Φ k g h := by
      intro h
      rw [hexp g h, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hΦ, inner_conj_symm, Complex.star_def]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall e)]
    exact integral_finsetSum _ fun k _ => hg k
  have hR : ∀ h, ⟪upVec R i t v b y h, R.extV i t u h⟫_ℂ = ∑ k, ∫ g in R.fdW i, Φ k g h ∂(R.νW i) := by
    intro h
    simp only [upVec, sum_inner, inner_smul_left]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hΦ, upLift]
    rw [integral_mul_const, ← integral_conj, inner_conj_symm]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [map_mul, Complex.star_def, Complex.conj_conj]
  calc ∫ g in R.fdW i, star (val R i v y g) * R.thF i t u (fun ρ => v ρ) g ∂(R.νW i)
      = ∫ g in R.fdW i, ∑ k, ∫ h in R.fdV i t, Φ k g h ∂(R.νV i t) ∂(R.νW i) := integral_congr_ae hL1
    _ = ∑ k, ∫ g in R.fdW i, ∫ h in R.fdV i t, Φ k g h ∂(R.νV i t) ∂(R.νW i) :=
        integral_finsetSum _ fun k _ => (hint k).integral_prod_left
    _ = ∑ k, ∫ h in R.fdV i t, ∫ g in R.fdW i, Φ k g h ∂(R.νW i) ∂(R.νV i t) :=
        Finset.sum_congr rfl fun k _ => integral_integral_swap (hint k)
    _ = ∫ h in R.fdV i t, ∑ k, ∫ g in R.fdW i, Φ k g h ∂(R.νW i) ∂(R.νV i t) :=
        (integral_finsetSum _ fun k _ => (hint k).integral_prod_right).symm
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun h => (hR h).symm)

end GlobalTheory.AdjUnfold
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjointPairingUnfoldingDownwardLiftStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.AdjUp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjoint_pairing_unfolding_downward_lift : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ (R.cV i).W) (y : (R.HW i (sg0 D A)).H) (u : (R.HV i t).H), ∫ g in R.fdW i, star (val R i v y g) * R.thF i t u (fun ρ => v ρ) g ∂(R.νW i) = ∫ h in R.fdV i t, ⟪upVec R i t v b y h, R.extV i t u h⟫_ℂ ∂(R.νV i t) := by
  first | exact @GlobalTheory.AdjUnfold.integral_val_thF_eq | exact GlobalTheory.AdjUnfold.integral_val_thF_eq | (intros; apply GlobalTheory.AdjUnfold.integral_val_thF_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeterssonIntegralFormula
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeterssonIntegralFormula
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.AdjUp

noncomputable section

namespace GlobalTheory.AdjUp

theorem ip_eq_mul_integral_val : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type)
    (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ (i : Fin D.R.m) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ),
    IsUnitVec R i v → ∃ P : ℝ, 0 ≤ P ∧ ∀ y z : (R.HW i (sg0 D A)).H,
      ⟪y, z⟫_ℂ = (P : ℂ) * ∫ g in R.fdW i, star (val R i v y g) * val R i v z g ∂(R.νW i) := by
  intro hC D G _ _ Pl0 T A Ks _ _ _ R F hL i v hv
  obtain ⟨-, hr, hip⟩ := hL.models.HW i (sg0 D A)
  have hmem : ∀ x, (R.HW i (sg0 D A)).e x ∈ R.Wall i (sg0 D A) := fun x => hr ▸ LinearMap.mem_range_self _ x
  have hS := (GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hC R).2.2 i

  set Q : ℝ := ∏ ρ, ((dimK _ _ (kapAt (Wc D i) (sg0 D A) ρ) : ℚ) : ℝ) with hQ
  have hQc : (∏ ρ, ((dimK _ _ (kapAt (Wc D i) (sg0 D A) ρ) : ℚ) : ℂ)) = (Q : ℂ) := by
    rw [hQ, Complex.ofReal_prod]; rfl

  have key : ∀ y z : (R.HW i (sg0 D A)).H,
      ⟪y, z⟫_ℂ = (Q : ℂ) * ∫ g in R.fdW i, star (val R i v y g) * val R i v z g ∂(R.νW i) := by
    intro y z
    obtain ⟨c, hc⟩ := hS hL.models.inf (hL.models.νW i).1.1 (hL.models.νW i).2 _ (hmem y) _ (hmem z)
    have hex : ∃ c, IsMultIP (R.MW i (sg0 D A)) (R.νW i) (R.fdW i) ((R.HW i (sg0 D A)).e y)
        ((R.HW i (sg0 D A)).e z) c := ⟨c, hc⟩
    have hv1 := (hex.choose_spec (fun ρ => v ρ) (fun ρ => v ρ)).2
    have hprod : (∏ ρ, ⟪((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ),
        ((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ)⟫_ℂ) = 1 := by
      refine Finset.prod_eq_one fun ρ _ => ?_
      rw [inner_self_eq_norm_sq_to_K, hv ρ]
      norm_num
    rw [hip, ipAt, hQc, ipM, dite_eq_left hex]
    unfold val
    rw [hv1, hprod, mul_one]
  by_cases h0 : 0 ≤ Q
  · exact ⟨Q, h0, key⟩
  ·
    refine ⟨0, le_rfl, fun y z => ?_⟩
    have hy : y = 0 := by
      have e1 := key y y
      have hnn : 0 ≤ ∫ g in R.fdW i, ‖val R i v y g‖ ^ 2 ∂(R.νW i) :=
        MeasureTheory.setIntegral_nonneg_of_ae (Filter.Eventually.of_forall fun _ => by positivity)
      have hI : (∫ g in R.fdW i, star (val R i v y g) * val R i v y g ∂(R.νW i)) =
          ((∫ g in R.fdW i, ‖val R i v y g‖ ^ 2 ∂(R.νW i) : ℝ) : ℂ) := by
        rw [← integral_complex_ofReal]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        simp only
        rw [Complex.ofReal_pow, ← Complex.conj_mul']
        rfl
      rw [hI] at e1
      have e2 : ‖y‖ ^ 2 = Q * ∫ g in R.fdW i, ‖val R i v y g‖ ^ 2 ∂(R.νW i) := by
        have := congrArg Complex.re e1
        rw [inner_self_eq_norm_sq_to_K] at this
        simpa [← Complex.ofReal_pow, Complex.re_ofReal_mul] using this
      have hle : ‖y‖ ^ 2 ≤ 0 := by
        rw [e2]; exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt (not_le.1 h0)) hnn
      have : ‖y‖ = 0 := by nlinarith [norm_nonneg y]
      exact norm_eq_zero.1 this
    rw [hy, inner_zero_left, Complex.ofReal_zero, zero_mul]

end GlobalTheory.AdjUp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeterssonIntegralFormulaStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.AdjUp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.petersson_integral_formula : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ (i : Fin D.R.m) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ), IsUnitVec R i v → ∃ P : ℝ, 0 ≤ P ∧ ∀ y z : (R.HW i (sg0 D A)).H, ⟪y, z⟫_ℂ = (P : ℂ) * ∫ g in R.fdW i, star (val R i v y g) * val R i v z g ∂(R.νW i) := by
  first | exact @GlobalTheory.AdjUp.ip_eq_mul_integral_val | exact GlobalTheory.AdjUp.ip_eq_mul_integral_val | (intros; apply GlobalTheory.AdjUp.ip_eq_mul_integral_val <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InnerProductIntegralFormula
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InnerProductIntegralFormula
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.AdjUp

noncomputable section

namespace GlobalTheory.AdelicL2Norm

theorem adInner_eq_mul_integral {G H W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [Group H] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (ν : Measure G) [ν.IsMulLeftInvariant]
    [ν.IsOpenPosMeasure] (π : G →* H) (hπ : Function.Surjective π) (Γ : Subgroup G) [Countable Γ] {𝓖 : Set G}
    (h𝓖 : IsFundamentalDomain Γ 𝓖 ν) (J₀ J : Subgroup H) (hle : J ≤ J₀) (ho : IsOpen (J.comap π : Set G))
    (h1 : ν (J₀.comap π) = 1) (ρ : G →* Module.End ℂ W) (hρ : ∀ h x y, inner ℂ (ρ h x) (ρ h y) = inner ℂ x y)
    (χ : J →* ℂˣ) (hχ : ∀ k, ‖(χ k : ℂ)‖ = 1) {I : Type} [Fintype I] (y : I → H)
    (hy : Formalism.IndefR.Bridge.IsReps (π.comp Γ.subtype) J y) :
    ∃ c : ℝ, 0 < c ∧ ∀ f ∈ Formalism.IndefR.Bridge.AdForms (π.comp Γ.subtype) (ρ.comp Γ.subtype) J χ,
      ∀ f' ∈ Formalism.IndefR.Bridge.AdForms (π.comp Γ.subtype) (ρ.comp Γ.subtype) J χ,
        IntegrableOn (fun h => inner ℂ (ρ h⁻¹ (f (π h))) (ρ h⁻¹ (f' (π h)))) 𝓖 ν ∧
        Formalism.IndefR.Bridge.adInner (π.comp Γ.subtype) J y f f' =
          (c : ℂ) * ∫ h in 𝓖, inner ℂ (ρ h⁻¹ (f (π h))) (ρ h⁻¹ (f' (π h))) ∂ν := by
  set m := ν (J.comap π) with hmdef
  have hm0 : m ≠ 0 := ho.measure_ne_zero ν ⟨1, by simp⟩
  have hmt : m ≠ ⊤ := ne_top_of_le_ne_top (h1 ▸ ENNReal.one_ne_top) (measure_mono (Subgroup.comap_mono hle))
  have h𝓖' : IsFundamentalDomain Γ 𝓖 (m⁻¹ • ν) := h𝓖.mono Measure.smul_absolutelyContinuous
  have h1' : (m⁻¹ • ν) (J.comap π) = 1 := by
    rw [Measure.smul_apply, smul_eq_mul, ← hmdef, ENNReal.inv_mul_cancel hm0 hmt]
  obtain ⟨-, key⟩ := GlobalTheory.InnerClassSum.integral_inner_eq_adInner (m⁻¹ • ν) π hπ Γ h𝓖' J ho h1' ρ hρ χ hχ y hy
  refine ⟨m.toReal⁻¹, inv_pos.2 (ENNReal.toReal_pos hm0 hmt), fun f hf f' hf' => ?_⟩
  obtain ⟨hi, he⟩ := key f hf f' hf'
  refine ⟨?_, ?_⟩
  · unfold IntegrableOn at hi ⊢
    rw [Measure.restrict_smul] at hi
    exact (integrable_smul_measure (ENNReal.inv_ne_zero.2 hmt) (ENNReal.inv_ne_top.2 hm0)).1 hi
  · rw [← he, Measure.restrict_smul, integral_smul_measure, ENNReal.toReal_inv, Complex.real_smul]

theorem integrableOn_coord {G H W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [Group H] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (ν : Measure G) (π : G →* H)
    (J : Subgroup H) (ho : IsOpen (J.comap π : Set G)) (ρ : G →* Module.End ℂ W)
    (hρc : ∀ x, Continuous fun h => ρ h x) (χ : J →* ℂˣ) (hχ : ∀ k, ‖(χ k : ℂ)‖ = 1) (Γ : Subgroup G) (f f' : H → W)
    (hF : f ∈ Formalism.IndefR.Bridge.AdForms (π.comp Γ.subtype) (ρ.comp Γ.subtype) J χ)
    (hF' : f' ∈ Formalism.IndefR.Bridge.AdForms (π.comp Γ.subtype) (ρ.comp Γ.subtype) J χ)
    {𝓖 : Set G} (hi : IntegrableOn (fun h => inner ℂ (ρ h⁻¹ (f (π h))) (ρ h⁻¹ (f (π h)))) 𝓖 ν)
    (hi' : IntegrableOn (fun h => inner ℂ (ρ h⁻¹ (f' (π h))) (ρ h⁻¹ (f' (π h)))) 𝓖 ν) (a a' : W) :
    IntegrableOn (fun h => star (inner ℂ a (ρ h⁻¹ (f (π h)))) * inner ℂ a' (ρ h⁻¹ (f' (π h)))) 𝓖 ν := by
  have hr : ∀ g ∈ Formalism.IndefR.Bridge.AdForms (π.comp Γ.subtype) (ρ.comp Γ.subtype) J χ, ∀ (x : H) (k : J),
      g (x * k) = (χ k : ℂ) • g x := fun g hg x k => by
    have := hg 1 x k
    simpa using this
  have hf := hr f hF
  have hf' := hr f' hF'
  have hcont : Continuous fun h => star (inner ℂ a (ρ h⁻¹ (f (π h)))) * inner ℂ a' (ρ h⁻¹ (f' (π h))) := by
    refine continuous_iff_continuousAt.2 fun h₀ => ?_
    have hψ : Continuous fun h : G => star (inner ℂ a (ρ h⁻¹ (f (π h₀)))) * inner ℂ a' (ρ h⁻¹ (f' (π h₀))) :=
      (continuous_star.comp (continuous_const.inner ((hρc _).comp continuous_inv))).mul
        (continuous_const.inner ((hρc _).comp continuous_inv))
    refine hψ.continuousAt.congr ?_
    have hU : {h : G | h₀⁻¹ * h ∈ J.comap π} ∈ nhds h₀ :=
      (ho.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp)
    filter_upwards [hU] with h hh
    have e : π h = π h₀ * ((⟨π (h₀⁻¹ * h), hh⟩ : J) : H) := by
      simp [← map_mul]
    rw [e, hf, hf', map_smul, map_smul, inner_smul_right, inner_smul_right, star_mul']
    have hn : star ((χ ⟨π (h₀⁻¹ * h), hh⟩ : ℂˣ) : ℂ) * ((χ ⟨π (h₀⁻¹ * h), hh⟩ : ℂˣ) : ℂ) = 1 := by
      rw [show star _ = (starRingEnd ℂ) _ from rfl, Complex.conj_mul', hχ]; simp
    linear_combination -(star (inner ℂ a (ρ h⁻¹ (f (π h₀)))) * inner ℂ a' (ρ h⁻¹ (f' (π h₀)))) * hn
  have hsq : ∀ x : W, ‖inner ℂ x x‖ = ‖x‖ ^ 2 := fun x => by
    rw [inner_self_eq_norm_sq_to_K]; simp
  refine Integrable.mono' ((hi.norm.add hi'.norm).const_mul (‖a‖ * ‖a'‖)) hcont.aestronglyMeasurable.restrict ?_
  refine Filter.Eventually.of_forall fun h => ?_
  simp only [Pi.add_apply, hsq, norm_mul, norm_star]
  have h1 := norm_inner_le_norm (𝕜 := ℂ) a (ρ h⁻¹ (f (π h)))
  have h2 := norm_inner_le_norm (𝕜 := ℂ) a' (ρ h⁻¹ (f' (π h)))
  have hx := norm_nonneg (ρ h⁻¹ (f (π h)))
  have hy := norm_nonneg (ρ h⁻¹ (f' (π h)))
  have ha := norm_nonneg a
  have ha' := norm_nonneg a'
  have hxy : ‖ρ h⁻¹ (f (π h))‖ * ‖ρ h⁻¹ (f' (π h))‖ ≤ ‖ρ h⁻¹ (f (π h))‖ ^ 2 + ‖ρ h⁻¹ (f' (π h))‖ ^ 2 := by
    nlinarith [sq_nonneg (‖ρ h⁻¹ (f (π h))‖ - ‖ρ h⁻¹ (f' (π h))‖)]
  calc ‖inner ℂ a (ρ h⁻¹ (f (π h)))‖ * ‖inner ℂ a' (ρ h⁻¹ (f' (π h)))‖
      ≤ (‖a‖ * ‖ρ h⁻¹ (f (π h))‖) * (‖a'‖ * ‖ρ h⁻¹ (f' (π h))‖) := mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = ‖a‖ * ‖a'‖ * (‖ρ h⁻¹ (f (π h))‖ * ‖ρ h⁻¹ (f' (π h))‖) := by ring
    _ ≤ ‖a‖ * ‖a'‖ * (‖ρ h⁻¹ (f (π h))‖ ^ 2 + ‖ρ h⁻¹ (f' (π h))‖ ^ 2) := by gcongr

end GlobalTheory.AdelicL2Norm

noncomputable section

namespace GlobalTheory.AdelicL2Norm


set_option maxHeartbeats 2000000 in
theorem norm_eq_integral : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ (i : Fin D.R.m) (t : T), ∃ c : ℝ, 0 < c ∧ ∀ u u' : (R.HV i t).H, ⟪u, u'⟫_ℂ = (c : ℂ) * ∫ h in R.fdV i t, ⟪R.extV i t u h, R.extV i t u' h⟫_ℂ ∂(R.νV i t) ∧ ∀ a a' : (R.cV i).W, IntegrableOn (fun h => star ⟪a, R.extV i t u h⟫_ℂ * ⟪a', R.extV i t u' h⟫_ℂ) (R.fdV i t) (R.νV i t) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL i t
  have hν := hL.models.νV i t
  have hH := hL.models.HV i t
  have hc := hL.models.cV i
  haveI : IsTopologicalGroup (GA D (Vc D i)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : BorelSpace (GA D (Vc D i)) := ⟨rfl⟩
  haveI : Countable (GQ (Vc D i)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig (Vc D i).gram
  haveI := hν.1.1
  have ho : IsOpen (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).J.comap (finHom (Vc D i)).rangeRestrict :
      Subgroup (GA D (Vc D i))) : Set (GA D (Vc D i))) := by
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    filter_upwards [GlobalTheory.ThetaIntegrand.eventually_level (Vc D i) (R.βV i) (R.datVt i t)] with κ hκ
    exact hκ.1
  have h1 : R.νV i t ((GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (R.datVt i t)).comap (finHom (Vc D i)).rangeRestrict) = 1 :=
    GlobalTheory.Mass.Levels.measure_comap_finE hν.1
  have hle : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).J ≤ GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (R.datVt i t) := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    have e : rTup (R.βV i) (R.datVt i t) (Formalism.UG.bc (Formalism.IndefR.Lev.swapAE D) x.1) = 1 := Subgroup.mem_bot.1 hx.2
    exact e ▸ one_mem _
  have hχ : ∀ k, ‖((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ k : ℂ)‖ = 1 := fun k =>
    GlobalTheory.InnerClassSum.norm_levFn (R.βV i) (flag1L (R.datVt i t)) (Formalism.UG.bc (Formalism.IndefR.Lev.swapAE D) k.1.1)
  obtain ⟨c, hc0, hcl⟩ := adInner_eq_mul_integral (R.νV i t) (finHom (Vc D i)).rangeRestrict
    (finHom (Vc D i)).rangeRestrict_surjective (GQ (Vc D i)) hν.2 _ _ hle ho h1 (R.cV i).ρ hc.2.1
    (levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ hχ (R.B.L i t).pres.y (R.B.L i t).pres.reps
  have hmem := fun u => hH.2.1.le (LinearMap.mem_range_self (R.HV i t).e u)
  have hx : ∀ u h, R.extV i t u h = (R.cV i).ρ h⁻¹ ((R.HV i t).e u ((finHom (Vc D i)).rangeRestrict h)) :=
    fun _ _ => rfl
  refine ⟨c, hc0, fun u u' => ⟨?_, fun a a' => ?_⟩⟩
  · simp only [hx]
    exact (hH.2.2 u u').trans (hcl _ (hmem u) _ (hmem u')).2
  · simp only [hx]
    exact integrableOn_coord (R.νV i t) (finHom (Vc D i)).rangeRestrict _ ho (R.cV i).ρ hc.2.2.1 _ hχ (GQ (Vc D i)) _ _ (hmem u) (hmem u')
      (hcl _ (hmem u) _ (hmem u)).1 (hcl _ (hmem u') _ (hmem u')).1 a a'

end GlobalTheory.AdelicL2Norm
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InnerProductIntegralFormulaStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.AdjUp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inner_product_integral_formula : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ (i : Fin D.R.m) (t : T), ∃ c : ℝ, 0 < c ∧ ∀ u u' : (R.HV i t).H, ⟪u, u'⟫_ℂ = (c : ℂ) * ∫ h in R.fdV i t, ⟪R.extV i t u h, R.extV i t u' h⟫_ℂ ∂(R.νV i t) ∧ ∀ a a' : (R.cV i).W, IntegrableOn (fun h => star ⟪a, R.extV i t u h⟫_ℂ * ⟪a', R.extV i t u' h⟫_ℂ) (R.fdV i t) (R.νV i t) := by
  first | exact @GlobalTheory.AdelicL2Norm.norm_eq_integral | exact GlobalTheory.AdelicL2Norm.norm_eq_integral | (intros; apply GlobalTheory.AdelicL2Norm.norm_eq_integral <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DownwardLiftAdjointEqUpwardThetaIntegral
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.AdjUp

namespace GlobalTheory.AdjUp


set_option maxHeartbeats 1000000 in
theorem adjFormula_holds : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ i t, AdjFormula R i t := by
  intro hP D G _ _ Pl0 T A Ks _ _ _ R F hL hF i t th hth v hv n b
  refine (GlobalTheory.T.petersson_integral_formula hP D G Pl0 T A Ks R F hL i v hv).elim fun P hPx => ?_
  refine (GlobalTheory.T.inner_product_integral_formula D G Pl0 T A Ks R F hL i t).elim fun c hcx => ?_
  have hval : ∀ u, val R i v (th u) = R.thF i t u (fun ρ => v ρ) := fun u => by
    show (R.HW i (sg0 D A)).e (th u) (fun ρ => v ρ) = _
    rw [hth u]
  have hK0 : ∀ k h, upLift (R.ωP i t) (R.νW i) (R.fdW i) (jointVec R i t v (b k)) (val R i v 0) h = 0 := fun k h => by
    rw [val_zero]; exact upLift_zero _ _ _ _ h
  exact adjoint_formula_of_kernel th b ((R.νW i).restrict (R.fdW i)) ((R.νV i t).restrict (R.fdV i t)) (val R i v)
    (fun u => R.thF i t u (fun ρ => v ρ)) (R.extV i t)
    (fun k y h => upLift (R.ωP i t) (R.νW i) (R.fdW i) (jointVec R i t v (b k)) (val R i v y) h) P c hPx.1 hcx.1 hPx.2
    hval (val_zero R i v) hK0 hcx.2 (fun y u => GlobalTheory.T.adjoint_pairing_unfolding_downward_lift hP D G Pl0 T A Ks R F hL hF i t v n b y u)
    (fun y => GlobalTheory.T.upwardVectorLift_mem_range_coefficientExtension hP D G Pl0 T A Ks R F hL hF i t v n b y)

end GlobalTheory.AdjUp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DownwardLiftAdjointEqUpwardThetaIntegralStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.downwardLift_adjoint_eq_upwardThetaIntegral : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ i t, AdjFormula R i t := by
  first | exact @GlobalTheory.AdjUp.adjFormula_holds | exact GlobalTheory.AdjUp.adjFormula_holds | (intros; apply GlobalTheory.AdjUp.adjFormula_holds <;> assumption)
end
