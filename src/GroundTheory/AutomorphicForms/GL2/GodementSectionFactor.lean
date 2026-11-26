module

public import GroundTheory.AutomorphicForms.GL2.GodementSection
public import GroundTheory.AutomorphicForms.GL2.FiniteIdeleDecomp
public import GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
public import GroundTheory.AutomorphicForms.GL2.GJMatrixLocal

@[expose] public section

section -- merged from GroundTheory.AutomorphicForms.GL2.GodementSectionFactor
section -- merged from GroundTheory.AutomorphicForms.GL2.GodementSectionSplit
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology NumberField.mixedEmbedding
open scoped NumberField.AdeleRing SchwartzMap Classical

namespace GroundTheory.Automorphic.GodementSection

open GroundTheory.Global GroundTheory.Automorphic.Adele2 IdeleGroup

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

def infChar (χ : HeckeCharacter K) : (InfiniteAdeleRing K)ˣ →* Circle :=
  χ.toIdele.comp ofInfinite

def infMod (a : (InfiniteAdeleRing K)ˣ) : ℝ :=
  ∏ w : InfinitePlace K, ‖(a : InfiniteAdeleRing K) w‖ ^ w.mult

def infVec (y : Fin 2 → InfiniteAdeleRing K) : Fin 2 → mixedSpace K :=
  fun i ↦ homeomorphMixedSpace K (y i)

def archSection (χ₁ χ₂ : HeckeCharacter K) (s : ℂ) (φ : (Fin 2 → mixedSpace K) → ℂ)
    (g : GL (Fin 2) (InfiniteAdeleRing K)) : ℂ :=
  (infChar χ₁ (Matrix.GeneralLinearGroup.det g) : ℂ) *
    ((infMod (Matrix.GeneralLinearGroup.det g) : ℝ) : ℂ) ^ s *
      ∫ a, φ (infVec (![0, (a : InfiniteAdeleRing K)] ᵥ*
        (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)))) *
        (infChar (χ₁ * χ₂⁻¹) a : ℂ) * ((infMod a : ℝ) : ℂ) ^ (2 * s) ∂infiniteIdeleMeasure K

theorem toInfinite_symm (p : (InfiniteAdeleRing K)ˣ × (FiniteAdeleRing (𝓞 K) K)ˣ) :
    toInfinite K ((IdeleGroup.prodEquiv K).symm p) = p.1 := by
  change (IdeleGroup.prodEquiv K ((IdeleGroup.prodEquiv K).symm p)).1 = p.1
  rw [ContinuousMulEquiv.apply_symm_apply]

theorem toFinite_symm (p : (InfiniteAdeleRing K)ˣ × (FiniteAdeleRing (𝓞 K) K)ˣ) :
    toFinite K ((IdeleGroup.prodEquiv K).symm p) = p.2 := by
  change (IdeleGroup.prodEquiv K ((IdeleGroup.prodEquiv K).symm p)).2 = p.2
  rw [ContinuousMulEquiv.apply_symm_apply]

end

end GroundTheory.Automorphic.GodementSection
end

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum MeasureTheory Matrix Filter
  Topology
open scoped NumberField.AdeleRing Classical nonZeroDivisors

namespace GroundTheory.Automorphic.GodementSection

open GroundTheory.Global GroundTheory.Automorphic.Adele2 IdeleGroup

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

def adeleAt (v : HeightOneSpectrum (𝓞 K)) : FiniteAdeleRing (𝓞 K) K →+* v.adicCompletion K :=
  RestrictedProduct.evalRingHom (fun w : HeightOneSpectrum (𝓞 K) ↦ w.adicCompletion K) v

def glAt (v : HeightOneSpectrum (𝓞 K)) :
    GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) →* GL (Fin 2) (v.adicCompletion K) :=
  Matrix.GeneralLinearGroup.map (adeleAt v)

theorem glAt_apply (v : HeightOneSpectrum (𝓞 K)) (g : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))
    (i j : Fin 2) :
    (glAt v g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j =
      (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j v := rfl

def vecAt (v : HeightOneSpectrum (𝓞 K)) (x : Fin 2 → FiniteAdeleRing (𝓞 K) K) :
    Fin 2 → v.adicCompletion K :=
  fun i ↦ x i v

def awayIntegral (S : Finset (HeightOneSpectrum (𝓞 K))) :
    AddSubgroup (FiniteAdeleRing (𝓞 K) K) where
  carrier := {a | ∀ v ∉ S, a v ∈ v.adicCompletionIntegers K}
  add_mem' ha hb v hv := add_mem (ha v hv) (hb v hv)
  zero_mem' v _ := zero_mem (v.adicCompletionIntegers K)
  neg_mem' ha v hv := neg_mem (ha v hv)

theorem mem_awayIntegral {S : Finset (HeightOneSpectrum (𝓞 K))} {a : FiniteAdeleRing (𝓞 K) K} :
    a ∈ awayIntegral S ↔ ∀ v ∉ S, a v ∈ v.adicCompletionIntegers K := Iff.rfl

theorem isOpen_awayIntegral (S : Finset (HeightOneSpectrum (𝓞 K))) :
    IsOpen (awayIntegral S : Set (FiniteAdeleRing (𝓞 K) K)) := by
  refine AddSubgroup.isOpen_mono (H₁ := (integralFiniteAdeles (𝓞 K) K).toAddSubgroup)
    (fun a ha v _ ↦ mem_integralFiniteAdeles.1 ha v) isOpen_integralFiniteAdeles

def awayBox (S : Finset (HeightOneSpectrum (𝓞 K))) : Set (Fin 2 → FiniteAdeleRing (𝓞 K) K) :=
  {x | ∀ i, x i ∈ awayIntegral S}

def restrictedTensor2 (S : Finset (HeightOneSpectrum (𝓞 K)))
    (Ψ : ∀ v : S, (Fin 2 → v.1.adicCompletion K) → ℂ) :
    (Fin 2 → FiniteAdeleRing (𝓞 K) K) → ℂ :=
  (awayBox S).indicator fun x ↦ ∏ v : S, Ψ v (vecAt v.1 x)

theorem valued_le_exp_of_norm_le {v : HeightOneSpectrum (𝓞 K)} {y : v.adicCompletion K} {n : ℕ}
    (hy : ‖y‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ n) :
    Valued.v y ≤ WithZero.exp (n : ℤ) := by
  by_cases h0 : y = 0
  · rw [h0, map_zero]; exact zero_le
  have hN : (1 : ℝ) < Ideal.absNorm v.asIdeal := by
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hv0 : Valued.v y ≠ 0 := (Valued.v).ne_zero_iff.2 h0
  have h1 := normalizedAbv_eq_zpow v h0
  rw [normalizedAbv_apply] at h1
  rw [h1, ← zpow_natCast] at hy
  have h2 : WithZero.log (Valued.v y) ≤ n := (zpow_le_zpow_iff_right₀ hN).1 hy
  exact (WithZero.log_le_iff_le_exp hv0).1 h2

def localChar (χ : HeckeCharacter K) (v : HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletion K)ˣ →* ℂˣ :=
  Circle.toUnits.comp (χ.localComponent v : (v.adicCompletion K)ˣ →* Circle)

@[simp]
theorem coe_localChar (χ : HeckeCharacter K) (v : HeightOneSpectrum (𝓞 K))
    (a : (v.adicCompletion K)ˣ) : ((localChar χ v a : ℂˣ) : ℂ) = (χ.localComponent v a : ℂ) :=
  rfl

theorem continuous_localChar (χ : HeckeCharacter K) (v : HeightOneSpectrum (𝓞 K)) :
    Continuous (localChar χ v) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact continuous_subtype_val.comp (χ.localComponent v).continuous
  · have h : (fun a ↦ (((localChar χ v a)⁻¹ : ℂˣ) : ℂ)) =
        fun a ↦ ((χ.localComponent v a⁻¹ : Circle) : ℂ) := by
      funext a
      rw [← map_inv, coe_localChar]
    rw [h]
    exact continuous_subtype_val.comp ((χ.localComponent v).continuous.comp continuous_inv)

theorem modulus_adicCompletion (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K) :
    (LocalField.modulus x : ℝ) = ‖x‖ := by
  by_cases hx : x = 0
  · simp [hx, LocalField.modulus]
  rw [LocalField.modulus_of_ne_zero hx, norm_eq_absNorm_zpow_neg_ord v hx, NNReal.coe_zpow]
  congr 1
  rw [LocalField.residueCard, natCard_residueField_adicCompletion]
  rfl

def partAt (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (FiniteAdeleRing (𝓞 K) K)ˣ →* (FiniteAdeleRing (𝓞 K) K)ˣ :=
  ∏ v ∈ S, (finiteUnitsSingle v).comp (finiteComponent v)

theorem partAt_apply (S : Finset (HeightOneSpectrum (𝓞 K))) (b : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    partAt S b = ∏ v ∈ S, finiteUnitsSingle v (finiteComponent v b) := by
  simp [partAt]

theorem finiteComponent_partAt (S : Finset (HeightOneSpectrum (𝓞 K)))
    (b : (FiniteAdeleRing (𝓞 K) K)ˣ) (w : HeightOneSpectrum (𝓞 K)) :
    finiteComponent w (partAt S b) = if w ∈ S then finiteComponent w b else 1 := by
  rw [partAt_apply, map_prod]
  split_ifs with hw
  · rw [Finset.prod_eq_single w (fun u _ huw ↦ finiteComponent_finiteUnitsSingle_of_ne
      (Ne.symm huw) _) (fun h ↦ absurd hw h), finiteComponent_finiteUnitsSingle]
  · refine Finset.prod_eq_one fun u hu ↦ finiteComponent_finiteUnitsSingle_of_ne ?_ _
    rintro rfl
    exact hw hu

def awayPart (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (FiniteAdeleRing (𝓞 K) K)ˣ →* (FiniteAdeleRing (𝓞 K) K)ˣ :=
  MonoidHom.id _ / partAt S

theorem awayPart_apply (S : Finset (HeightOneSpectrum (𝓞 K))) (b : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    awayPart S b = b * (partAt S b)⁻¹ := by
  simp [awayPart, div_eq_mul_inv]

theorem finiteComponent_awayPart (S : Finset (HeightOneSpectrum (𝓞 K)))
    (b : (FiniteAdeleRing (𝓞 K) K)ˣ) (w : HeightOneSpectrum (𝓞 K)) :
    finiteComponent w (awayPart S b) = if w ∈ S then 1 else finiteComponent w b := by
  rw [awayPart_apply, map_mul, map_inv, finiteComponent_partAt]
  split_ifs
  · exact mul_inv_cancel _
  · rw [inv_one, mul_one]

theorem partAt_mul_awayPart (S : Finset (HeightOneSpectrum (𝓞 K))) (b : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    partAt S b * awayPart S b = b := by
  rw [awayPart_apply, mul_comm b, ← mul_assoc, mul_inv_cancel, one_mul]

theorem toIdele_ofFinite_partAt (χ : HeckeCharacter K) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (b : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    (χ.toIdele (ofFinite (partAt S b)) : ℂ) =
      ∏ v ∈ S, (χ.localComponent v (finiteComponent v b) : ℂ) := by
  rw [partAt_apply, map_prod, map_prod]
  exact (map_prod Circle.coeHom _ _).trans
    (Finset.prod_congr rfl fun v _ ↦ by rw [ofFinite_finiteUnitsSingle]; rfl)

theorem ofReal_prod_cpow {ι : Type*} (T : Finset ι) (r : ι → ℝ) (hr : ∀ i, 0 ≤ r i) (s : ℂ) :
    ((∏ i ∈ T, r i : ℝ) : ℂ) ^ s = ∏ i ∈ T, ((r i : ℝ) : ℂ) ^ s := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (hr a) (Finset.prod_nonneg fun i _ ↦ hr i), ih]

def partialLFunction (χ : HeckeCharacter K) (S : Finset (HeightOneSpectrum (𝓞 K))) (z : ℂ) : ℂ :=
  ∑' I : Ideal (𝓞 K), (if ∀ v ∈ S, ¬ v.asIdeal ∣ I then χ.coeff I else 0) *
    (Ideal.absNorm I : ℂ) ^ (-z)

end

end GroundTheory.Automorphic.GodementSection
end

section -- merged from GroundTheory.AutomorphicForms.GL2.GJMatrixSchwartz
namespace GroundTheory.Automorphic.GJMatrix

open GroundTheory.Global NumberField NumberField.mixedEmbedding MeasureTheory Matrix
open scoped NumberField.AdeleRing

noncomputable section

variable (K : Type*) [Field K] [NumberField K] (n : ℕ)


variable {K n} in
def matrixCoordEquiv {X : Type*} : Matrix (Fin n) (Fin n) X ≃ (Fin n × Fin n → X) where
  toFun := matrixCoord
  invFun z := Matrix.of fun i j ↦ z (i, j)
  left_inv _ := rfl
  right_inv _ := rfl


variable {K n} in
def matrixCoordTEquiv {X : Type*} : Matrix (Fin n) (Fin n) X ≃ (Fin n × Fin n → X) where
  toFun := matrixCoordT
  invFun z := Matrix.of fun i j ↦ z (j, i)
  left_inv _ := rfl
  right_inv _ := rfl

theorem trace_mul_eq_sum' {R : Type*} [CommRing R] (x y : Matrix (Fin n) (Fin n) R) :
    Matrix.trace (y * x) = ∑ p, matrixCoordT y p * matrixCoord x p := by
  rw [trace_mul_comm, trace_mul_eq_sum]
  exact Finset.sum_congr rfl fun p _ ↦ mul_comm _ _

section Perm

variable {K} {ι : Type*} [Fintype ι]

theorem comp_perm_mem_schwartzBruhatPi (σ : ι ≃ ι) {F : (ι → 𝔸[K]) → ℂ}
    (hF : F ∈ schwartzBruhatPi (K := K) (ι := ι)) : (fun z ↦ F (fun i ↦ z (σ i))) ∈ schwartzBruhatPi (K := K) (ι := ι) := by
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, g, hg, rfl⟩ := hG
    set L : (ι → mixedSpace K) ≃L[ℝ] (ι → mixedSpace K) :=
      (LinearEquiv.funCongrLeft ℝ (mixedSpace K) σ).toContinuousLinearEquiv
    have hL : ∀ u, L u = fun i ↦ u (σ i) := fun u ↦ rfl
    have hcont : Continuous fun z : ι → 𝔸ᶠ[K] ↦ fun i ↦ z (σ i) :=
      continuous_pi fun i ↦ continuous_apply (σ i)
    have hcont' : Continuous fun z : ι → 𝔸ᶠ[K] ↦ fun i ↦ z (σ.symm i) :=
      continuous_pi fun i ↦ continuous_apply (σ.symm i)
    have hemb : Topology.IsClosedEmbedding fun z : ι → 𝔸ᶠ[K] ↦ fun i ↦ z (σ i) :=
      Function.LeftInverse.isClosedEmbedding (f := fun z : ι → 𝔸ᶠ[K] ↦ fun i ↦ z (σ.symm i))
        (fun z ↦ funext fun i ↦ by simp) hcont' hcont
    have hg' : (fun z : ι → 𝔸ᶠ[K] ↦ g fun i ↦ z (σ i)) ∈ finiteSchwartzBruhatPi K :=
      ⟨hg.1.comp_continuous hcont, hg.2.comp_isClosedEmbedding hemb⟩
    convert schwartzBruhatTensorPi_mem (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L φ) hg'
      using 1
    funext z
    simp only [schwartzBruhatTensorPi, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
      Function.comp_apply, hL]
    rfl
  | zero => exact zero_mem _
  | add G H _ _ hG hH => exact add_mem hG hH
  | smul c G _ hG => exact Submodule.smul_mem _ c hG

end Perm

def adelicMatrixMeasure : Measure (Matrix (Fin n) (Fin n) 𝔸[K]) :=
  matrixMeasure (adeleMeasure K)

def matrixSchwartzBruhat : Submodule ℂ (Matrix (Fin n) (Fin n) 𝔸[K] → ℂ) :=
  (schwartzBruhatPi (K := K) (ι := Fin n × Fin n)).comap
    (LinearMap.funLeft ℂ ℂ (matrixCoordEquiv (n := n) (X := 𝔸[K])).symm)

variable {K n}

theorem mem_matrixSchwartzBruhat {Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ} :
    Φ ∈ matrixSchwartzBruhat K n ↔
      (fun z : Fin n × Fin n → 𝔸[K] ↦ Φ (Matrix.of fun i j ↦ z (i, j))) ∈
        schwartzBruhatPi (K := K) (ι := Fin n × Fin n) :=
  Iff.rfl


variable (K) in
def adelicMatrixFourier (Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ) (y : Matrix (Fin n) (Fin n) 𝔸[K]) :
    ℂ :=
  ∫ x, Φ x * (adelicChar K (Matrix.trace (x * y)) : ℂ) ∂adelicMatrixMeasure K n

def coordFun (Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ) : (Fin n × Fin n → 𝔸[K]) → ℂ :=
  fun z ↦ Φ (Matrix.of fun i j ↦ z (i, j))

theorem coordFun_matrixCoord (Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ)
    (x : Matrix (Fin n) (Fin n) 𝔸[K]) : coordFun Φ (matrixCoord x) = Φ x := rfl

theorem integral_matrixCoord (g : (Fin n × Fin n → 𝔸[K]) → ℂ) :
    ∫ x, g (matrixCoord x) ∂adelicMatrixMeasure K n = ∫ z, g z ∂adeleMeasurePi K :=
  (measurePreserving_matrixCoord (n := Fin n) (adeleMeasure K)).integral_comp
    (MeasurableEquiv.curry (Fin n) (Fin n) 𝔸[K]).symm.measurableEmbedding g

theorem integral_matrixCoordT (g : (Fin n × Fin n → 𝔸[K]) → ℂ) :
    ∫ x, g (matrixCoordT x) ∂adelicMatrixMeasure K n = ∫ z, g z ∂adeleMeasurePi K := by
  have hT : matrixCoordT (n := Fin n) (X := 𝔸[K]) =
      ⇑(MeasurableEquiv.piCongrLeft (fun _ ↦ 𝔸[K]) (Equiv.prodComm (Fin n) (Fin n))) ∘
        ⇑(MeasurableEquiv.curry (Fin n) (Fin n) 𝔸[K]).symm := by
    funext x p
    simp only [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, MeasurableEquiv.coe_mk, matrixCoordT]
    rfl
  have hemb : MeasurableEmbedding (matrixCoordT (n := Fin n) (X := 𝔸[K])) := by
    rw [hT]
    exact (MeasurableEquiv.piCongrLeft (fun _ ↦ 𝔸[K])
      (Equiv.prodComm (Fin n) (Fin n))).measurableEmbedding.comp
      (MeasurableEquiv.curry (Fin n) (Fin n) 𝔸[K]).symm.measurableEmbedding
  exact (measurePreserving_matrixCoordT (n := Fin n) (adeleMeasure K)).integral_comp hemb g

theorem adelicMatrixFourier_eq (Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ)
    (y : Matrix (Fin n) (Fin n) 𝔸[K]) :
    adelicMatrixFourier K Φ y = adelicFourierPi K (coordFun Φ) (matrixCoordT y) := by
  rw [adelicMatrixFourier, adelicFourierPi, ← integral_matrixCoord]
  simp only [trace_mul_eq_sum, coordFun_matrixCoord]

theorem coordFun_adelicMatrixFourier (Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ) :
    coordFun (adelicMatrixFourier K Φ) =
      fun z ↦ adelicFourierPi K (coordFun Φ) (fun p ↦ z p.swap) := by
  funext z
  rw [coordFun, adelicMatrixFourier_eq]
  rfl

theorem adelicMatrixFourier_mem {Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ}
    (hΦ : Φ ∈ matrixSchwartzBruhat K n) : adelicMatrixFourier K Φ ∈ matrixSchwartzBruhat K n := by
  rw [mem_matrixSchwartzBruhat]
  change coordFun (adelicMatrixFourier K Φ) ∈ _
  rw [coordFun_adelicMatrixFourier]
  exact comp_perm_mem_schwartzBruhatPi (Equiv.prodComm (Fin n) (Fin n))
    (adelicFourierPi_mem_schwartzBruhatPi (F := coordFun Φ) hΦ)

theorem adelicMatrixFourier_adelicMatrixFourier {Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ}
    (hΦ : Φ ∈ matrixSchwartzBruhat K n) :
    adelicMatrixFourier K (adelicMatrixFourier K Φ) = fun x ↦ Φ (-x) := by
  funext x
  have h : adelicFourierPi K (adelicFourierPi K (coordFun Φ)) (matrixCoord x) =
      coordFun Φ (-matrixCoord x) :=
    congrFun (adelicFourierPi_adelicFourierPi (F := coordFun Φ) hΦ) (matrixCoord x)
  rw [adelicMatrixFourier, ← coordFun_matrixCoord Φ (-x), matrixCoord_neg, ← h, adelicFourierPi,
    ← integral_matrixCoordT]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
  simp only [adelicMatrixFourier_eq, trace_mul_eq_sum']

theorem poisson_matrix {Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ} (hΦ : Φ ∈ matrixSchwartzBruhat K n) :
    Summable (fun ξ : Matrix (Fin n) (Fin n) K ↦ ‖Φ (ξ.map (algebraMap K 𝔸[K]))‖) ∧
      Summable (fun ξ : Matrix (Fin n) (Fin n) K ↦
        ‖adelicMatrixFourier K Φ (ξ.map (algebraMap K 𝔸[K]))‖) ∧
      ∑' ξ : Matrix (Fin n) (Fin n) K, Φ (ξ.map (algebraMap K 𝔸[K])) =
        ∑' ξ : Matrix (Fin n) (Fin n) K, adelicMatrixFourier K Φ (ξ.map (algebraMap K 𝔸[K])) := by
  obtain ⟨h1, h2, h3⟩ := poisson_of_mem_schwartzBruhatPi (F := coordFun Φ) hΦ
  have eL : ∀ ξ : Matrix (Fin n) (Fin n) K, Φ (ξ.map (algebraMap K 𝔸[K])) =
      coordFun Φ (fun p ↦ algebraMap K 𝔸[K] (matrixCoordEquiv ξ p)) := fun _ ↦ rfl
  have eR : ∀ ξ : Matrix (Fin n) (Fin n) K, adelicMatrixFourier K Φ (ξ.map (algebraMap K 𝔸[K])) =
      adelicFourierPi K (coordFun Φ) (fun p ↦ algebraMap K 𝔸[K] (matrixCoordTEquiv ξ p)) :=
    fun ξ ↦ by rw [adelicMatrixFourier_eq]; rfl
  simp only [eL, eR]
  refine ⟨(matrixCoordEquiv.summable_iff (f := fun z : Fin n × Fin n → K ↦
      ‖coordFun Φ (fun p ↦ algebraMap K 𝔸[K] (z p))‖)).mpr h1,
    (matrixCoordTEquiv.summable_iff (f := fun z : Fin n × Fin n → K ↦
      ‖adelicFourierPi K (coordFun Φ) (fun p ↦ algebraMap K 𝔸[K] (z p))‖)).mpr h2, ?_⟩
  rw [matrixCoordEquiv.tsum_eq (fun z : Fin n × Fin n → K ↦
      coordFun Φ (fun p ↦ algebraMap K 𝔸[K] (z p))),
    matrixCoordTEquiv.tsum_eq (fun z : Fin n × Fin n → K ↦
      adelicFourierPi K (coordFun Φ) (fun p ↦ algebraMap K 𝔸[K] (z p)))]
  exact h3

end

end GroundTheory.Automorphic.GJMatrix
end
