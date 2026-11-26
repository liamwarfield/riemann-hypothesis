module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadNatZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidKernelSmoothSpanSmoothCuspidalBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TsumRsPsiEqTsumNeZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMulSupSFinGL
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff

noncomputable section

namespace GlobalTheory.CellDec

variable {E : Type} [Field E] [NumberField E]

open Classical

def idemOff (S : Finset (HeightOneSpectrum (𝓞 E))) : Af E :=
  ⟨fun v => if v ∈ S then 0 else 1, Filter.Eventually.of_forall fun v => by
    by_cases h : v ∈ S
    · simp only [h, if_true]; exact zero_mem _
    · simp only [h, if_false]; exact one_mem _⟩

theorem pLoc_idemOff (S : Finset (HeightOneSpectrum (𝓞 E))) (v : HeightOneSpectrum (𝓞 E)) :
    pLoc E v (idemOff S) = if v ∈ S then 0 else 1 := rfl

theorem idemOff_mul_self (S : Finset (HeightOneSpectrum (𝓞 E))) : idemOff S * idemOff S = idemOff S :=
  FiniteAdeleRing.ext _ fun v => by
    change pLoc E v (idemOff S) * pLoc E v (idemOff S) = pLoc E v (idemOff S)
    rw [pLoc_idemOff]; split_ifs <;> simp

def cutS (S : Finset (HeightOneSpectrum (𝓞 E))) : Af E →ₙ+* Af E where
  toFun x := idemOff S * x
  map_mul' x y := by
    calc idemOff S * (x * y) = (idemOff S * idemOff S) * (x * y) := by rw [idemOff_mul_self]
      _ = idemOff S * x * (idemOff S * y) := by ring
  map_zero' := mul_zero _
  map_add' x y := mul_add _ _ _

theorem pLoc_cutS (S : Finset (HeightOneSpectrum (𝓞 E))) (v : HeightOneSpectrum (𝓞 E)) (x : Af E) :
    pLoc E v (cutS S x) = (if v ∈ S then 0 else 1) * pLoc E v x := by
  change pLoc E v (idemOff S * x) = _
  rw [map_mul, pLoc_idemOff]

theorem map_pLoc_pFin_finGL {a : ℕ} (v : HeightOneSpectrum (𝓞 E)) (k : GL (Fin a) (Af E)) :
    Matrix.GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) (finGL E a k) = Matrix.GeneralLinearGroup.map (pLoc E v) k := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  exact congrArg (fun x : GL (Fin a) (Af E) => pLoc E v (x i j)) (pFin_finGL k)

theorem exists_mul_supS_finGL : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (g : GA E a),
    g ∈ GlobalTheory.CellDec.C0 E a S →
    ∃ u ∈ GlobalTheory.CellDec.NA E a, ∃ h ∈ GlobalTheory.JSW.supS (E := E) (a := a) S, ∃ k : GL (Fin a) (Af E),
      (∀ v, Matrix.GeneralLinearGroup.map (pLoc E v) k ∈ KGL v (n := a)) ∧ (∀ v ∈ S, Matrix.GeneralLinearGroup.map (pLoc E v) k = 1) ∧
      g = u * h * finGL E a k := by
  intro E _ _ a S g hg
  obtain ⟨u, hu, k₁, hk₁, rfl⟩ := hg
  set k : GL (Fin a) (Af E) := cornerGL a (cutS S) (Matrix.GeneralLinearGroup.map (pFin E) k₁) with hk
  have hkv : ∀ v, v ∉ S → Matrix.GeneralLinearGroup.map (pLoc E v) k =
      Matrix.GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) k₁ := by
    intro v hv
    rw [hk, map_cornerGL_of_hom _ _ (pLoc E v) (fun x => by rw [pLoc_cutS, if_neg hv, one_mul])]
    exact Units.ext (Matrix.ext fun i j => rfl)
  have hkS : ∀ v ∈ S, Matrix.GeneralLinearGroup.map (pLoc E v) k = 1 := fun v hv =>
    map_cornerGL_of_zero _ _ (fun x => by rw [pLoc_cutS, if_pos hv, zero_mul]) _
  have hK : ∀ v, v ∉ S → Matrix.GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) k₁ ∈ KGL v (n := a) := by
    intro v hv
    exact Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hk₁ v) hv
  refine ⟨u, hu, k₁ * (finGL E a k)⁻¹, ?_, k, fun v => ?_, hkS, ?_⟩
  · intro w hw
    rw [map_mul, map_inv, map_pLoc_pFin_finGL, hkv w hw, mul_inv_cancel]
  · by_cases hv : v ∈ S
    · rw [hkS v hv]; exact one_mem _
    · rw [hkv v hv]; exact hK v hv
  · group

end GlobalTheory.CellDec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousIntegralOfCompact
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ApplyScalar
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.JSW.Central

def centralFns (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ω : HChar E) :
    Submodule ℂ (GA E a → ℂ) where
  carrier := {F | ∀ (z : Neutral.B1.Ideles E) (g : GA E a),
    F (GeneralLinearGroup.scalar (Fin a) z * g) = ((ω.1 z : ℂˣ) : ℂ) * F g}
  add_mem' hF hG z g := by simp [hF z g, hG z g, mul_add]
  zero_mem' _ _ := by simp
  smul_mem' c F hF z g := by simp [hF z g, mul_left_comm]

end GlobalTheory.JSW.Central
end
end

noncomputable section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host
open GlobalTheory.RSTheta GlobalTheory.ShortVecDecay GlobalTheory.Petersson GlobalTheory.CuspQuot GlobalTheory.ThetaPoisson GroundTheory.Global GlobalTheory.RSThetaLow
open GroundTheory.Automorphic.GJMatrix
open scoped nonZeroDivisors ComplexConjugate

namespace GlobalTheory.RSResidue

theorem continuous_integral_of_compact {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y]
    [OpensMeasurableSpace Y] (ν : Measure Y) [IsFiniteMeasureOnCompacts ν] {K : Set Y} (hK : IsCompact K)
    {F : X → Y → ℂ} (hF : Continuous fun p : X × Y => F p.1 p.2) (h0 : ∀ x, ∀ y ∉ K, F x y = 0) :
    Continuous fun x => ∫ y, F x y ∂ν := by
  have hI : (fun x => ∫ y, F x y ∂ν) = fun x => ∫ y in K, F x y ∂ν :=
    funext fun x => (setIntegral_eq_integral_of_forall_compl_eq_zero (h0 x)).symm
  rw [hI]
  have hc : ∀ x, Continuous (F x) := fun x => hF.comp (continuous_const.prodMk continuous_id)
  have hint : ∀ x, IntegrableOn (F x) K ν := fun x => (hc x).continuousOn.integrableOn_compact hK
  set m : ℝ := ν.real K with hm
  have hm0 : 0 ≤ m := measureReal_nonneg
  refine continuous_iff_continuousAt.2 fun x₀ => Metric.tendsto_nhds.2 fun ε hε => ?_
  have hδ : 0 < ε / (m + 1) := by positivity
  have hev : ∀ᶠ x in 𝓝 x₀, ∀ y ∈ K, dist (F x y) (F x₀ y) < ε / (m + 1) := by
    refine hK.eventually_forall_of_forall_eventually fun y _ => ?_
    have h1 := Metric.tendsto_nhds.1 (hF.continuousAt (x := (x₀, y))) (ε / (m + 1) / 2) (by positivity)
    have h2 := Metric.tendsto_nhds.1 ((hc x₀).comp continuous_snd |>.continuousAt (x := (x₀, y)))
      (ε / (m + 1) / 2) (by positivity)
    filter_upwards [h1, h2] with z hz1 hz2
    calc dist (F z.1 z.2) (F x₀ z.2) ≤ dist (F z.1 z.2) (F x₀ y) + dist (F x₀ z.2) (F x₀ y) :=
          dist_triangle_right _ _ _
      _ < ε / (m + 1) / 2 + ε / (m + 1) / 2 := add_lt_add hz1 hz2
      _ = ε / (m + 1) := by ring
  filter_upwards [hev] with x hx
  rw [dist_eq_norm, ← integral_sub (hint x) (hint x₀)]
  have h3 : ‖∫ y in K, (F x y - F x₀ y) ∂ν‖ ≤ ε / (m + 1) * m :=
    norm_setIntegral_le_of_norm_le_const hK.measure_lt_top fun y hy => by
      rw [← dist_eq_norm]; exact (hx y hy).le
  refine h3.trans_lt ?_
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
  nlinarith

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem rsHat_zero_eq {ℓ : Fin a} {Φ : (Fin a → Cinf E) → ℂ} (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E)
    (F F' : Sm E a) (hΦ : IsTest (rowSet E ℓ) Φ) : ∃ c : ℂ, ∀ g : GA E a,
      adelicFourierPi E (rsPsi ℓ F.1 F'.1 Φ J η g) 0 = (∫ u, rsInf ℓ F.1 F'.1 Φ g u ∂infMeasure E a) * c := by
  refine ⟨(finiteAdelicChar E (∑ i, η i * pFin E ((0 : Fin a → Ad E) i)) : ℂ) *
        (latt a (traceDualIdeal E J)).indicator 1 (fun i => pFin E ((0 : Fin a → Ad E) i)) *
        ((finiteMeasurePi E (latt a J)).toReal : ℂ), fun g => ?_⟩
  have h := rsHat_eq (ℓ := ℓ) J η F F' hΦ g 0
  have e : (fun i => pInf E ((0 : Fin a → Ad E) i)) = 0 := funext fun _ => map_zero _
  have hF : infFourier (rsInf ℓ F.1 F'.1 Φ g) (fun i => pInf E ((0 : Fin a → Ad E) i)) =
      ∫ u, rsInf ℓ F.1 F'.1 Φ g u ∂infMeasure E a := by
    rw [e, infFourier]
    simp
  change rsHat ℓ F.1 F'.1 Φ J η g 0 = _
  rw [h, hF]
  ring

variable {ω : HChar E}

theorem rsHat_zero_props (hω : ω.IsUnitary) {φ φ' : Sm E a} (h : φ.1 ∈ bddForms E a ω) (h' : φ'.1 ∈ bddForms E a ω)
    {ℓ : Fin a} {Φ : (Fin a → Cinf E) → ℂ} (hΦ : IsTest (rowSet E ℓ) Φ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ)
    (η : Fin a → Af E) :
    Continuous (fun g : GA E a => adelicFourierPi E (rsPsi ℓ φ.1 φ'.1 Φ J η g) 0) ∧
    (∃ C : ℝ, ∀ g : GA E a, ‖adelicFourierPi E (rsPsi ℓ φ.1 φ'.1 Φ J η g) 0‖ ≤ C) ∧
    ∀ γ ∈ latticeGL E a, ∀ g : GA E a,
      adelicFourierPi E (rsPsi ℓ φ.1 φ'.1 Φ J η (γ * g)) 0 = adelicFourierPi E (rsPsi ℓ φ.1 φ'.1 Φ J η g) 0 := by
  obtain ⟨c, hc⟩ := rsHat_zero_eq J η φ φ' hΦ
  have hj : Continuous fun p : GA E a × (Fin a → Cinf E) => rsInf ℓ φ.1 φ'.1 Φ p.1 p.2 :=
    continuous_rsInf h.1 h'.1 hΦ.1.continuous hΦ.2.2
  have h0 : ∀ g, ∀ u ∉ tsupport Φ, rsInf ℓ φ.1 φ'.1 Φ g u = 0 := fun g u hu => by
    rw [rsInf, image_eq_zero_of_notMem_tsupport hu, mul_zero]
  refine ⟨?_, ?_, ?_⟩
  · simp only [hc]
    exact (continuous_integral_of_compact (infMeasure E a) hΦ.2.1 hj h0).mul continuous_const
  · obtain ⟨C, hC⟩ := h.2.2.2
    obtain ⟨C', hC'⟩ := h'.2.2.2
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 1)
    have hi : Integrable (fun u => C * C' * ‖Φ u‖) (infMeasure E a) :=
      (integrable_infMeasure hΦ.1.continuous hΦ.2.1).norm.const_mul _
    refine ⟨(∫ u, C * C' * ‖Φ u‖ ∂infMeasure E a) * ‖c‖, fun g => ?_⟩
    rw [hc, norm_mul]
    refine mul_le_mul_of_nonneg_right (norm_integral_le_of_norm_le hi (.of_forall fun u => ?_)) (norm_nonneg _)
    rw [rsInf, norm_mul, norm_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_right (mul_le_mul (hC _) (hC' _) (norm_nonneg _) hC0) (norm_nonneg _)
  · intro γ hγ g
    have hL : ∀ x, φ.1 (γ * x) * conj (φ'.1 (γ * x)) = φ.1 x * conj (φ'.1 x) := fun x =>
      leftInv_mul_conj hω h h' γ hγ x
    have e : rsInf ℓ φ.1 φ'.1 Φ (γ * g) = rsInf ℓ φ.1 φ'.1 Φ g := funext fun u => by
      rw [rsInf, rsInf, mul_assoc γ g, hL]
    have e' : rsPsi ℓ φ.1 φ'.1 Φ J η (γ * g) = rsPsi ℓ φ.1 φ'.1 Φ J η g := funext fun y => by
      rw [rsPsi, rsPsi, e]
    rw [e']

end GlobalTheory.RSResidue

namespace GlobalTheory.RSResidue

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

end GlobalTheory.RSResidue

namespace GlobalTheory.RSResidue

end GlobalTheory.RSResidue

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTwistedCharacterCocycleOfTorsionLocalCocyc
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTwistedCharacterCocycleOfTorsionLocalCocyc
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases

noncomputable section
namespace GlobalTheory.UseLoc.Cases

section Gen1
variable {O : Type} [CommRing O]

def evOneQ (LL : Type) [Field LL] [Algebra O LL] : ((Fin 1 → LL) ⧸ stdG O LL 1) →ₗ[O] (LL ⧸ intO (O := O) LL) :=
  (stdG O LL 1).mapQ (intO (O := O) LL) (LinearMap.proj (R := O) (φ := fun _ : Fin 1 => LL) 0) (by
    rintro _ ⟨u, rfl⟩
    exact ⟨u 0, rfl⟩)

variable {LL : Type} [Field LL] [Algebra O LL]

theorem evOneQ_mk (v : Fin 1 → LL) :
    evOneQ (O := O) LL (Submodule.Quotient.mk v) = Submodule.Quotient.mk (v 0) := rfl

theorem evOneQ_mem {lam : O} {a : ℕ} {q : (Fin 1 → LL) ⧸ stdG O LL 1} (h : lam ^ a • q = 0) :
    evOneQ LL q ∈ Xq LL lam a := by
  show (lam ^ a • (LinearMap.id : (LL ⧸ intO (O := O) LL) →ₗ[O] _)) (evOneQ LL q) = 0
  rw [LinearMap.smul_apply, LinearMap.id_apply, ← map_smul, h, map_zero]

def oneO : ↥(intO (O := O) LL) := ⟨1, 1, map_one (algebraMap O LL)⟩

theorem iotaC_oneO (lam : O) (a : ℕ) (q : (Fin 1 → LL) ⧸ stdG O LL 1) (h : evOneQ LL q ∈ Xq LL lam a) :
    iotaC LL lam a (oneO ⊗ₜ ⟨evOneQ LL q, h⟩) = q := by
  induction q using Submodule.Quotient.induction_on with
  | H v =>
    show iotaG (intO LL) (stdG O LL 1) (constOne LL) (constOne_mem LL) (oneO ⊗ₜ (evOneQ LL (Submodule.Quotient.mk v))) = _
    rw [evOneQ_mk, iotaG_tmul]
    congr 1
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    simp [constOne, oneO]

def oneT (hinj : Function.Injective (algebraMap O LL)) {G : Type} [Group G] (ψ : G →* Oˣ) : ↥(latOne hinj ψ).T :=
  oneO

theorem actT_latOne_oneT (hinj : Function.Injective (algebraMap O LL)) {G : Type} [Group G] (ψ : G →* Oˣ) (g : G) :
    actT (latOne hinj ψ) g (oneT hinj ψ) = ((ψ g : Oˣ) : O) • oneT hinj ψ := by
  apply Subtype.ext
  show ((tableLineDegreeTwo.charL (LL := LL) ψ g : LLˣ) : LL) • (1 : LL) = ((ψ g : Oˣ) : O) • (1 : LL)
  simp [tableLineDegreeTwo.charL, Algebra.smul_def]

end Gen1

section Gen2
variable {O : Type} [CommRing O] {LL : Type} [Field LL] [Algebra O LL]

theorem actTw_oneO (hinj : Function.Injective (algebraMap O LL)) {G : Type} [Group G] [TopologicalSpace G]
    (X : Type) [AddCommGroup X] [Module O X] (χ ψ : G →* Oˣ) (g : G) (x : X) :
    tableLineDegreeTwo.actTw (latOne hinj ψ) X χ g (oneT hinj ψ ⊗ₜ x) = oneT hinj ψ ⊗ₜ ((((χ g)⁻¹ * ψ g : Oˣ) : O) • x) := by
  rw [tableLineDegreeTwo.actTw, LinearMap.smul_apply, LinearMap.rTensor_tmul, actT_latOne_oneT, TensorProduct.smul_tmul,
    ← TensorProduct.tmul_smul, Units.val_mul, mul_smul]

theorem evOneQ_actD (hinj : Function.Injective (algebraMap O LL)) {G : Type} [Group G] [TopologicalSpace G]
    (N : G →* Matrix (Fin 1) (Fin 1) O) (g : G) (q : (Fin 1 → LL) ⧸ stdG O LL 1) :
    evOneQ LL (actD (stdLatG hinj N) g q) = N g 0 0 • evOneQ LL q := by
  induction q using Submodule.Quotient.induction_on with
  | H v =>
    show evOneQ LL (Submodule.Quotient.mk (matRep (mapM (algebraMap O LL) N) g v)) = _
    rw [evOneQ_mk, evOneQ_mk, ← Submodule.Quotient.mk_smul]
    congr 1
    simp [matRep, mapM, Matrix.mulVec, dotProduct, Algebra.smul_def]

end Gen2

section Gen3
variable {O : Type} [CommRing O] {LL : Type} [Field LL] [Algebra O LL]

theorem liftC_gen (hinj : Function.Injective (algebraMap O LL)) {G : Type} [Group G] [TopologicalSpace G]
    (N : G →* Matrix (Fin 1) (Fin 1) O) (χ ψ : G →* Oˣ) (hN : ∀ g, (((χ g)⁻¹ * ψ g : Oˣ) : O) = N g 0 0)
    (lam : O) (a : ℕ) (f : G → (Fin 1 → LL) ⧸ stdG O LL 1) (hf : f ∈ divisibleCocycles (stdLatG hinj N))
    (htor : ∀ g, lam ^ a • f g = 0) :
    ∃ z' : G → ↥(latOne hinj ψ).T ⊗[O] ↥(Xq LL lam a),
      tableLineDegreeTwo.IsCoc (latOne hinj ψ) ↥(Xq LL lam a) χ z' ∧ ∀ g, iotaC LL lam a (z' g) = f g := by
  classical
  obtain ⟨hlc, hco⟩ := hf
  let F : ((Fin 1 → LL) ⧸ stdG O LL 1) → ↥(latOne hinj ψ).T ⊗[O] ↥(Xq LL lam a) :=
    fun q => if hq : lam ^ a • q = 0 then oneT hinj ψ ⊗ₜ ⟨evOneQ LL q, evOneQ_mem hq⟩ else 0
  refine ⟨fun g => oneT hinj ψ ⊗ₜ ⟨evOneQ LL (f g), evOneQ_mem (htor g)⟩, ⟨?_, ?_⟩, ?_⟩
  · have hF : (fun g => oneT hinj ψ ⊗ₜ[O]
        (⟨evOneQ LL (f g), evOneQ_mem (htor g)⟩ : ↥(Xq LL lam a))) = F ∘ f := by
      funext g
      simp only [F, Function.comp_apply, dif_pos (htor g)]
    rw [hF]
    exact hlc.comp F
  · intro g h
    beta_reduce
    rw [actTw_oneO, ← TensorProduct.tmul_add]
    congr 1
    apply Subtype.ext
    simp only [Submodule.coe_add, Submodule.coe_smul]
    rw [hco g h, hN g]
    exact ((evOneQ LL).map_add _ _).trans (congrArg (evOneQ LL (f g) + ·) (evOneQ_actD hinj N g (f h)))
  · intro g
    exact iotaC_oneO lam a (f g) _

end Gen3

section AtW
variable {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}

theorem locOC_chiRatO_apply (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (c : ℕ) (g : Br.G D.nbr i w hw) :
    locOC C (chiRatO D.nd i c) g 0 0 =
      ((chiOC C (chiU D.nd i c * (chiU D.nd i 1)⁻¹) g : (↥(OL C.LL))ˣ) : ↥(OL C.LL)) := by
  simp [locOC, chiOC, Br.locO, Br.iota, mapM, chiRatO, twistM]

theorem chiT_one_eq_theta (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) : chiT C θ 1 = θ := by
  simp [chiT, chiOC]

theorem chiT_ratio (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (c : ℕ)
    (g : Br.G D.nbr i w hw) :
    (((chiT C θ 1 g)⁻¹ * chiT C θ c g : (↥(OL C.LL))ˣ) : ↥(OL C.LL)) = locOC C (chiRatO D.nd i c) g 0 0 := by
  rw [locOC_chiRatO_apply, chiT_one_eq_theta]
  congr 1
  simp only [chiT, MonoidHom.mul_apply]
  rw [mul_comm, mul_assoc, mul_inv_cancel, mul_one]

end AtW

theorem liftC_main : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (lam : ↥(OL C.LL)), Irreducible lam →
    ∀ (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (c a : ℕ) (f : Br.G D.nbr i w hw → (Fin 1 → ↥C.LL.1) ⧸ stdG ↥(OL C.LL) ↥C.LL.1 1),
    f ∈ divisibleCocycles (latC C (locOC C (chiRatO D.nd i c))) → (∀ g, lam ^ a • f g = 0) →
    ∃ z' : Br.G D.nbr i w hw → ↥(latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ c)).T ⊗[↥(OL C.LL)] ↥(Xq ↥C.LL.1 lam a),
      tableLineDegreeTwo.IsCoc (latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ c)) ↥(Xq ↥C.LL.1 lam a) (chiT C θ 1) z' ∧
      ∀ g, iotaC ↥C.LL.1 lam a (z' g) = f g := by
  intro D i w hw C lam _ θ c a f hf htor
  exact liftC_gen Subtype.val_injective (locOC C (chiRatO D.nd i c)) (chiT C θ 1) (chiT C θ c) (chiT_ratio C θ c)
    lam a f hf htor

end GlobalTheory.UseLoc.Cases

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTwistedCharacterCocycleOfTorsionLocalCocycStatement
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_twistedCharacter_cocycle_of_torsion_localCocycle : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (lam : ↥(OL C.LL)), Irreducible lam →
    ∀ (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (c a : ℕ) (f : Br.G D.nbr i w hw → (Fin 1 → ↥C.LL.1) ⧸ stdG ↥(OL C.LL) ↥C.LL.1 1),
    f ∈ divisibleCocycles (latC C (locOC C (chiRatO D.nd i c))) → (∀ g, lam ^ a • f g = 0) →
    ∃ z' : Br.G D.nbr i w hw → ↥(latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ c)).T ⊗[↥(OL C.LL)] ↥(Xq ↥C.LL.1 lam a),
      tableLineDegreeTwo.IsCoc (latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ c)) ↥(Xq ↥C.LL.1 lam a) (chiT C θ 1) z' ∧
      ∀ g, iotaC ↥C.LL.1 lam a (z' g) = f g := by
  first | exact @GlobalTheory.UseLoc.Cases.liftC_main | exact GlobalTheory.UseLoc.Cases.liftC_main | (intros; apply GlobalTheory.UseLoc.Cases.liftC_main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBlochKatoReadOfTensorSelmerAddCoboundary
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBlochKatoReadOfTensorSelmerAddCoboundary
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases

noncomputable section

namespace GlobalTheory.UseLoc.Cases

theorem chiT_one_eq {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) : chiT C θ 1 = θ := by
  simp [chiT, chiOC]

section GenRead

variable {O : Type} [CommRing O] {LL : Type} [Field LL] [Algebra O LL] {k : ℕ}

def iotaL (hinj : Function.Injective (algebraMap O LL)) {G : Type} [Group G]
    (M N : G →* Matrix (Fin k) (Fin k) O) (lam : O) (a : ℕ) :
    ↥(stdLatG (LL := LL) hinj M).T ⊗[O] ↥(Xq LL lam a) →ₗ[O] (Fin k → LL) ⧸ (stdLatG (LL := LL) hinj N).T :=
  iotaW LL lam a k

theorem iotaL_tmul (hinj : Function.Injective (algebraMap O LL)) {G : Type} [Group G]
    (M N : G →* Matrix (Fin k) (Fin k) O) (lam : O) (a : ℕ) (t : ↥(stdLatG (LL := LL) hinj M).T)
    (x : ↥(Xq LL lam a)) (s : LL) (hs : Submodule.Quotient.mk s = (x : LL ⧸ intO (O := O) LL)) :
    iotaL hinj M N lam a (t ⊗ₜ x) = Submodule.Quotient.mk (s • (t : Fin k → LL)) := by
  obtain ⟨x, hx⟩ := x
  change Submodule.Quotient.mk s = x at hs
  subst hs
  rfl

theorem matRep_twistM_apply {G : Type} [Group G] (N : G →* Matrix (Fin k) (Fin k) O) (θ : G →* Oˣ) (g : G)
    (v : Fin k → LL) :
    matRep (mapM (algebraMap O LL) (twistM N θ)) g v = ((θ g : Oˣ) : O) • matRep (mapM (algebraMap O LL) N) g v := by
  have hM : (mapM (algebraMap O LL) (twistM N θ)) g =
      algebraMap O LL ((θ g : Oˣ) : O) • (mapM (algebraMap O LL) N) g := by
    ext p q
    simp [mapM, twistM, Matrix.smul_apply, smul_eq_mul, map_mul]
  change ((mapM (algebraMap O LL) (twistM N θ)) g).mulVec v = ((θ g : Oˣ) : O) • ((mapM (algebraMap O LL) N) g).mulVec v
  rw [hM, Matrix.smul_mulVec, algebraMap_smul]

theorem actD_iotaL (hinj : Function.Injective (algebraMap O LL)) {G : Type} [Group G] [TopologicalSpace G]
    (N : G →* Matrix (Fin k) (Fin k) O) (θ χ : G →* Oˣ) (hχ : ∀ g, (((χ g)⁻¹ : Oˣ) : O) * ((θ g : Oˣ) : O) = 1)
    (lam : O) (a : ℕ) (g : G) (y : ↥(stdLatG (LL := LL) hinj (twistM N θ)).T ⊗[O] ↥(Xq LL lam a)) :
    actD (stdLatG hinj N) g (iotaL hinj (twistM N θ) N lam a y) =
      iotaL hinj (twistM N θ) N lam a (tableLineDegreeTwo.actTw (stdLatG hinj (twistM N θ)) ↥(Xq LL lam a) χ g y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add u v hu hv => simp only [map_add (f := _), hu, hv]
  | tmul t x =>
    obtain ⟨s, hs⟩ := Submodule.Quotient.mk_surjective _ (x : LL ⧸ intO (O := O) LL)
    rw [tableLineDegreeTwo.actTw, LinearMap.smul_apply, LinearMap.rTensor_tmul, map_smul, iotaL_tmul hinj _ N lam a _ x s hs,
      iotaL_tmul hinj _ N lam a _ x s hs, ← Submodule.Quotient.mk_smul]
    change Submodule.Quotient.mk (matRep (mapM (algebraMap O LL) N) g (s • (t : Fin k → LL))) =
      Submodule.Quotient.mk ((((χ g)⁻¹ : Oˣ) : O) • s • matRep (mapM (algebraMap O LL) (twistM N θ)) g (t : Fin k → LL))
    congr 1
    rw [matRep_twistM_apply, LinearMap.map_smul, smul_comm _ s, ← mul_smul, hχ g, one_smul]

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] [Algebra Qp LL]
    [TopologicalSpace (Fin k → LL)] [ContinuousAdd (Fin k → LL)] [ContinuousConstSMul LL (Fin k → LL)]

theorem readW_gen (PD : PeriodData G Qp K₀ K B BdR) (hinj : Function.Injective (algebraMap O LL))
    (N : G →* Matrix (Fin k) (Fin k) O) (θ χ : G →* Oˣ) (hχ : ∀ g, (((χ g)⁻¹ : Oˣ) : O) * ((θ g : Oˣ) : O) = 1)
    (lam : O) (a : ℕ) (z' : G → ↥(stdLatG (LL := LL) hinj (twistM N θ)).T ⊗[O] ↥(Xq LL lam a))
    (hz : tableLineDegreeTwo.InHfX PD (stdLatG (LL := LL) hinj (twistM N θ)) (stdLatG hinj N) ↥(Xq LL lam a) χ z') :
    (fun g => iotaL hinj (twistM N θ) N lam a (z' g)) ∈ HfD PD (stdLatG (LL := LL) hinj N) := by
  obtain ⟨n, c, x, m, hc, hz⟩ := hz
  choose s hs using fun j => Submodule.Quotient.mk_surjective _ (x j : LL ⧸ intO (O := O) LL)
  have e : (fun g => iotaL hinj (twistM N θ) N lam a (z' g)) =
      (∑ j, LinearMap.compLeft (stdLatG (LL := LL) hinj N).T.mkQ G (s j • fun g => (c j g : Fin k → LL))) +
        LinearMap.pi (fun g => actD (stdLatG (LL := LL) hinj N) g - LinearMap.id)
          (iotaL hinj (twistM N θ) N lam a m) := by
    funext g
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hz g, map_add (f := _), map_sum, map_sub, ← actD_iotaL hinj N θ χ hχ lam a g m]
    simp only [Pi.add_apply, Finset.sum_apply, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [iotaL_tmul hinj _ N lam a _ (x j) (s j) (hs j)]
    rfl
  rw [e]
  refine add_mem (Submodule.sum_mem _ fun j _ => Submodule.mem_sup_left (Submodule.mem_map_of_mem ?_))
    (Submodule.mem_sup_right (LinearMap.mem_range_self _ _))
  exact (Submodule.restrictScalars_mem O _ _).2 ((finiteCocycles PD _).smul_mem (s j) (hc j).2)

end GenRead

theorem chiT_one_inv_mul {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : w ∈ placesOver D.host.E (D.nd.l i)} (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ)
    (g : Br.G D.nbr i w hw) :
    (((chiT C θ 1 g)⁻¹ : (↥(OL C.LL))ˣ) : ↥(OL C.LL)) * ((θ g : (↥(OL C.LL))ˣ) : ↥(OL C.LL)) = 1 := by
  rw [chiT_one_eq]
  simp

theorem readW_main : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (lam : ↥(OL C.LL)) {k : ℕ} (N : Br.G D.nbr i w hw →* Matrix (Fin k) (Fin k) ↥(OL C.LL))
    (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (a : ℕ) (z' : Br.G D.nbr i w hw → ↥(latC C (twistM N θ)).T ⊗[↥(OL C.LL)] ↥(Xq ↥C.LL.1 lam a)),
    tableLineDegreeTwo.InHfX (Br.PD D.loc D.nbr i w hw) (latC C (twistM N θ)) (latC C N) ↥(Xq ↥C.LL.1 lam a) (chiT C θ 1) z' →
    (fun g => iotaW ↥C.LL.1 lam a k (z' g)) ∈ HfD (Br.PD D.loc D.nbr i w hw) (latC C N) := by
  intro D i w hw C lam k N θ a z' hz
  exact readW_gen (Br.PD D.loc D.nbr i w hw) Subtype.val_injective N θ (chiT C θ 1) (chiT_one_inv_mul C θ) lam a z' hz

end GlobalTheory.UseLoc.Cases

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBlochKatoReadOfTensorSelmerAddCoboundaryStatement
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isBlochKato_read_of_tensor_selmer_add_coboundary : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (lam : ↥(OL C.LL)) {k : ℕ} (N : Br.G D.nbr i w hw →* Matrix (Fin k) (Fin k) ↥(OL C.LL))
    (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (a : ℕ) (z' : Br.G D.nbr i w hw → ↥(latC C (twistM N θ)).T ⊗[↥(OL C.LL)] ↥(Xq ↥C.LL.1 lam a)),
    tableLineDegreeTwo.InHfX (Br.PD D.loc D.nbr i w hw) (latC C (twistM N θ)) (latC C N) ↥(Xq ↥C.LL.1 lam a) (chiT C θ 1) z' →
    (fun g => iotaW ↥C.LL.1 lam a k (z' g)) ∈ HfD (Br.PD D.loc D.nbr i w hw) (latC C N) := by
  first | exact @GlobalTheory.UseLoc.Cases.readW_main | exact GlobalTheory.UseLoc.Cases.readW_main | (intros; apply GlobalTheory.UseLoc.Cases.readW_main <;> assumption)
end
end
