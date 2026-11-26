module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsScalarTowerCenAlgebra
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChosenSeries
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TupPrimeEmpty
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RayFieldTheta
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QuotVolumeNeZeroNeTop

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergEquivariantIsometry
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergEquivariantIsometry
open MeasureTheory
open scoped SchwartzMap

noncomputable section

namespace GlobalTheory.HeisenbergL2

section Real

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def heisS (a : V) (L : V →L[ℝ] ℝ) (c t : ℝ) (f : 𝓢(V, ℂ)) : 𝓢(V, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ
    (fun x => Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L x + t ^ 2 * c : ℝ) : ℂ)))
    (SchwartzMap.compSubConstCLM ℂ (-(t • a)) f)

def derS (a : V) (L : V →L[ℝ] ℝ) (f : 𝓢(V, ℂ)) : 𝓢(V, ℂ) :=
  LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a f -
    (2 * Real.pi * Complex.I) • SchwartzMap.smulLeftCLM ℂ (fun x => ((L x : ℝ) : ℂ)) f

theorem heisS_apply (a : V) (L : V →L[ℝ] ℝ) (c t : ℝ) (f : 𝓢(V, ℂ)) (x : V) :
    heisS a L c t f x =
      Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L x + t ^ 2 * c : ℝ) : ℂ)) * f (x + t • a) := by
  rw [heisS, SchwartzMap.smulLeftCLM_apply_apply (by
      rw [GlobalTheory.LinPhaseSeminorm.phase_eq]; exact GlobalTheory.LinPhaseSeminorm.hasTemperateGrowth_phase L c t),
    SchwartzMap.compSubConstCLM_apply, smul_eq_mul, sub_neg_eq_add]

theorem derS_apply (a : V) (L : V →L[ℝ] ℝ) (f : 𝓢(V, ℂ)) (x : V) :
    derS a L f x = fderiv ℝ f x a - 2 * Real.pi * Complex.I * ((L x : ℝ) : ℂ) * f x := by
  have hL : Function.HasTemperateGrowth (fun x => ((L x : ℝ) : ℂ)) :=
    (Complex.ofRealCLM.comp L).hasTemperateGrowth
  rw [derS, SchwartzMap.sub_apply, SchwartzMap.smul_apply, SchwartzMap.smulLeftCLM_apply_apply hL,
    LineDeriv.lineDerivOpCLM_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv, smul_eq_mul, smul_eq_mul]
  ring

theorem seminorm_heisS_sub_le (a : V) (L : V →L[ℝ] ℝ) (c : ℝ) (f : 𝓢(V, ℂ)) (k n : ℕ) :
    ∃ C : ℝ, ∀ t : ℝ, |t| ≤ 1 →
      SchwartzMap.seminorm ℂ k n (heisS a L c t f - f - (t : ℂ) • derS a L f) ≤ C * t ^ 2 := by
  set P : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ) := SchwartzMap.smulLeftCLM ℂ (fun x => ((L x : ℝ) : ℂ)) with hP
  set d := LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a f with hd
  obtain ⟨C3, hC3⟩ := GlobalTheory.LinPhaseSeminorm.seminorm_smulLeft_phase_le L c k n
  choose C1 hC1 using fun m => GlobalTheory.SchwartzTranslate.seminorm_translate_sub_le a f k m
  obtain ⟨C2, hC2⟩ := GlobalTheory.LinearPhase.seminorm_phase_sub_le L c d k n
  obtain ⟨C0, hC0⟩ := GlobalTheory.LinearPhase.seminorm_phase_sub_le L c f k n
  set p := SchwartzMap.seminorm ℂ k n (E := V) (F := ℂ) with hp
  refine ⟨|C3| * ∑ m ∈ Finset.range (n + 1), |C1 m| + |C2| + 2 * Real.pi * p (P d) + |C0|, fun t ht => ?_⟩
  set M : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ) := SchwartzMap.smulLeftCLM ℂ
    (fun x => Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L x + t ^ 2 * c : ℝ) : ℂ))) with hM
  set X := SchwartzMap.compSubConstCLM ℂ (-(t • a)) f - f - (t : ℂ) • d with hX
  set Y := M d - d + ((t : ℂ) * (2 * Real.pi * Complex.I)) • P d with hY
  set Z := M f - f + ((t : ℂ) * (2 * Real.pi * Complex.I)) • P f with hZ
  have e : heisS a L c t f - f - (t : ℂ) • derS a L f =
      M X + (t : ℂ) • Y - ((t : ℂ) ^ 2 * (2 * Real.pi * Complex.I)) • P d + Z := by
    rw [heisS, derS, ← hM, ← hP, ← hd, hX, hY, hZ, map_sub, map_sub, map_smul]
    module
  rw [e]
  have t1 : p (M X) ≤ |C3| * (∑ m ∈ Finset.range (n + 1), |C1 m|) * t ^ 2 := by
    refine (hC3 t ht X).trans ?_
    calc C3 * ∑ m ∈ Finset.range (n + 1), SchwartzMap.seminorm ℂ k m X
        ≤ |C3| * ∑ m ∈ Finset.range (n + 1), SchwartzMap.seminorm ℂ k m X :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (Finset.sum_nonneg fun _ _ => apply_nonneg _ _)
      _ ≤ |C3| * ∑ m ∈ Finset.range (n + 1), |C1 m| * t ^ 2 :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun m _ =>
            (hC1 m t ht).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _))) (abs_nonneg _)
      _ = |C3| * (∑ m ∈ Finset.range (n + 1), |C1 m|) * t ^ 2 := by rw [← Finset.sum_mul]; ring
  have t2 : p ((t : ℂ) • Y) ≤ |C2| * t ^ 2 := by
    rw [map_smul_eq_mul, Complex.norm_real, Real.norm_eq_abs]
    have h2 := hC2 t ht
    calc |t| * p Y ≤ 1 * (C2 * t ^ 2) := mul_le_mul ht h2 (apply_nonneg _ _) zero_le_one
      _ ≤ |C2| * t ^ 2 := by rw [one_mul]; exact mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)
  have t3 : p (((t : ℂ) ^ 2 * (2 * Real.pi * Complex.I)) • P d) = 2 * Real.pi * p (P d) * t ^ 2 := by
    rw [map_smul_eq_mul]
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat, Complex.norm_I,
      abs_of_pos Real.pi_pos, sq_abs]
    ring
  have t4 : p Z ≤ |C0| * t ^ 2 := (hC0 t ht).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _))
  have tri : p (M X + (t : ℂ) • Y - ((t : ℂ) ^ 2 * (2 * Real.pi * Complex.I)) • P d + Z) ≤
      p (M X) + p ((t : ℂ) • Y) + p (((t : ℂ) ^ 2 * (2 * Real.pi * Complex.I)) • P d) + p Z := by
    refine (map_add_le_add p _ _).trans (add_le_add ?_ le_rfl)
    refine (map_sub_le_add p _ _).trans (add_le_add ?_ le_rfl)
    exact map_add_le_add p _ _
  rw [t3] at tri
  nlinarith [t1, t2, t4, tri]

end Real

section L2

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V]

theorem toLp_heisS_sub_le (μ : Measure V) [μ.HasTemperateGrowth] (a : V) (L : V →L[ℝ] ℝ) (c : ℝ)
    (f : 𝓢(V, ℂ)) : ∃ K : ℝ, ∀ t : ℝ, |t| ≤ 1 →
      ‖(heisS a L c t f - f - (t : ℂ) • derS a L f).toLp 2 μ‖ ≤ K * t ^ 2 := by
  obtain ⟨k, C, hC0, hC⟩ := SchwartzMap.norm_toLp_le_seminorm ℂ ℂ 2 μ
  choose K hK using fun p : ℕ × ℕ => seminorm_heisS_sub_le a L c f p.1 p.2
  refine ⟨C * ∑ p ∈ Finset.Iic (k, 0), |K p|, fun t ht => ?_⟩
  refine (hC _).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hC0
  rw [Finset.sum_mul]
  refine Seminorm.finset_sup_apply_le (Finset.sum_nonneg fun _ _ => by positivity) fun p hp => ?_
  refine ((hK p t ht).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg t))).trans ?_
  exact Finset.single_le_sum (f := fun q => |K q| * t ^ 2) (fun _ _ => by positivity) hp

theorem norm_toLp_two (μ : Measure V) [μ.HasTemperateGrowth] (u : 𝓢(V, ℂ)) :
    ‖u.toLp 2 μ‖ = Real.sqrt (∫ x, ‖u x‖ ^ 2 ∂μ) := by
  rw [SchwartzMap.norm_toLp' (by norm_num) (by norm_num), ENNReal.toReal_ofNat]
  simp only [Real.rpow_two]
  rw [Real.sqrt_eq_rpow, one_div]

theorem map_dHeis_of_isometry : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (T : SchwartzMap V ℂ →ₗ[ℂ] SchwartzMap V ℂ), (∀ f, ∫ x, ‖T f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ) →
    ∀ w w' : V × V, (∀ (s : ℝ) (f g : SchwartzMap V ℂ), ⇑g = GlobalTheory.GaussLine.heisFun β (s • w).1 (s • w).2 ⇑f →
      ⇑(T g) = GlobalTheory.GaussLine.heisFun β (s • w').1 (s • w').2 ⇑(T f)) →
    ∀ f g : SchwartzMap V ℂ, (∀ x, g x = GlobalTheory.GaussLine.dHeis β w ⇑f x) →
    ∀ x, T g x = GlobalTheory.GaussLine.dHeis β w' ⇑(T f) x := by
  intro V _ _ _ _ _ μ _ β T hT w w' hw f g hg x
  haveI : μ.HasTemperateGrowth := MeasureTheory.Measure.IsAddHaarMeasure.instHasTemperateGrowth
  let Lf : V × V → (V →L[ℝ] ℝ) := fun p => LinearMap.toContinuousLinearMap (β.flip p.2)
  have hLf : ∀ p y, Lf p y = β y p.2 := fun p y => rfl
  have hheis : ∀ (p : V × V) (F : 𝓢(V, ℂ)) (t : ℝ),
      ⇑(heisS p.1 (Lf p) (β p.1 p.2 / 2) t F) = GlobalTheory.GaussLine.heisFun β (t • p).1 (t • p).2 ⇑F := by
    intro p F t
    funext y
    rw [heisS_apply, GlobalTheory.GaussLine.heisFun_apply, hLf, Prod.smul_fst, Prod.smul_snd]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    congr 3
    ring_nf
  have hder : ∀ (p : V × V) (F : 𝓢(V, ℂ)) y, derS p.1 (Lf p) F y = GlobalTheory.GaussLine.dHeis β p ⇑F y := by
    intro p F y
    rw [derS_apply, GlobalTheory.GaussLine.dHeis, hLf]
  have hgS : g = derS w.1 (Lf w) f := by
    ext y
    rw [hg, hder]
  set G := derS w'.1 (Lf w') (T f) with hG
  set c := β w.1 w.2 / 2
  set c' := β w'.1 w'.2 / 2
  have hHT : ∀ t : ℝ, T (heisS w.1 (Lf w) c t f) = heisS w'.1 (Lf w') c' t (T f) := fun t =>
    DFunLike.coe_injective ((hw t f _ (hheis w f t)).trans (hheis w' (T f) t).symm)
  obtain ⟨K, hK⟩ := toLp_heisS_sub_le μ w.1 (Lf w) c f
  obtain ⟨K', hK'⟩ := toLp_heisS_sub_le μ w'.1 (Lf w') c' (T f)
  set ℓ := SchwartzMap.toLpCLM ℂ ℂ 2 μ with hℓ
  have hiso : ∀ u, ‖ℓ (T u)‖ = ‖ℓ u‖ := by
    intro u
    rw [hℓ, SchwartzMap.toLpCLM_apply, SchwartzMap.toLpCLM_apply, norm_toLp_two, norm_toLp_two, hT]
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 → ‖ℓ (T g - G)‖ ≤ (K + K') * t := by
    intro t ht0 ht1
    have hta : |t| ≤ 1 := by rw [abs_of_pos ht0]; exact ht1
    have e1 : (t : ℂ) • (T g - G) = (heisS w'.1 (Lf w') c' t (T f) - T f - (t : ℂ) • G) -
        T (heisS w.1 (Lf w) c t f - f - (t : ℂ) • g) := by
      rw [map_sub, map_sub, map_smul, hHT, smul_sub]
      abel
    have h1 : ‖ℓ ((t : ℂ) • (T g - G))‖ = t * ‖ℓ (T g - G)‖ := by
      rw [map_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg ht0.le]
    have h2 : ‖ℓ ((t : ℂ) • (T g - G))‖ ≤ K' * t ^ 2 + K * t ^ 2 := by
      rw [e1, map_sub]
      refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
      · have := hK' t hta
        rw [hℓ, SchwartzMap.toLpCLM_apply]
        exact this
      · rw [hiso, hgS, hℓ, SchwartzMap.toLpCLM_apply]
        exact hK t hta
    rw [h1] at h2
    have h3 : t * ‖ℓ (T g - G)‖ ≤ t * ((K + K') * t) := by nlinarith
    exact le_of_mul_le_mul_left h3 ht0
  have ha : ‖ℓ (T g - G)‖ = 0 := by
    by_contra hne
    have hpos : 0 < ‖ℓ (T g - G)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    set a := ‖ℓ (T g - G)‖
    set M := |K + K'| + 1 with hMdef
    have hM : 0 < M := by positivity
    set t := min 1 (a / (2 * M)) with htdef
    have ht0 : 0 < t := lt_min one_pos (by positivity)
    have h1 := key t ht0 (min_le_left _ _)
    have h2 : t ≤ a / (2 * M) := min_le_right _ _
    have h3 : (K + K') * t ≤ M * t := mul_le_mul_of_nonneg_right ((le_abs_self _).trans (by linarith)) ht0.le
    have h4 : M * t ≤ M * (a / (2 * M)) := mul_le_mul_of_nonneg_left h2 hM.le
    have h5 : M * (a / (2 * M)) = a / 2 := by field_simp
    linarith
  have h0 : (T g - G).toLp 2 μ = (0 : 𝓢(V, ℂ)).toLp 2 μ := by
    have := norm_eq_zero.1 ha
    rw [hℓ, SchwartzMap.toLpCLM_apply] at this
    rw [this]
    exact ((map_zero ℓ).symm.trans (SchwartzMap.toLpCLM_apply))
  have h00 : T g - G = 0 := SchwartzMap.injective_toLp 2 μ h0
  have := congrArg (fun u : 𝓢(V, ℂ) => u x) (sub_eq_zero.1 h00)
  rw [this, hG, hder]

end L2

end GlobalTheory.HeisenbergL2
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergEquivariantIsometryStatement
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenberg_equivariant_isometry : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (T : SchwartzMap V ℂ →ₗ[ℂ] SchwartzMap V ℂ), (∀ f, ∫ x, ‖T f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ) →
    ∀ w w' : V × V, (∀ (s : ℝ) (f g : SchwartzMap V ℂ), ⇑g = GlobalTheory.GaussLine.heisFun β (s • w).1 (s • w).2 ⇑f →
      ⇑(T g) = GlobalTheory.GaussLine.heisFun β (s • w').1 (s • w').2 ⇑(T f)) →
    ∀ f g : SchwartzMap V ℂ, (∀ x, g x = GlobalTheory.GaussLine.dHeis β w ⇑f x) →
    ∀ x, T g x = GlobalTheory.GaussLine.dHeis β w' ⇑(T f) x := by
  first | exact @GlobalTheory.HeisenbergL2.map_dHeis_of_isometry | exact GlobalTheory.HeisenbergL2.map_dHeis_of_isometry | (intros; apply GlobalTheory.HeisenbergL2.map_dHeis_of_isometry <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameMatrixAdjointSupportedOfConjHalf
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameMatrixAdjointSupportedOfConjHalf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfSupp

theorem smul_mul_mul_of_smul_eq {R : Type} [CommRing R] {a b c d : Type} [Fintype b] [Fintype c]
    (r : R) (A : Matrix a b R) (N : Matrix b c R) (B : Matrix c d R) (h : r • N = N) :
    r • (A * N * B) = A * N * B := by
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, h]

theorem map_smul_of_smul_eq {R S : Type} [CommRing R] [CommRing S] {a b : Type} (f : R →+* S)
    (r : R) (N : Matrix a b R) (h : r • N = N) : f r • N.map f = N.map f := by
  ext k l
  simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  rw [← map_mul]
  congr 1
  simpa [Matrix.smul_apply, smul_eq_mul] using congrFun (congrFun h k) l

theorem frMapAdj_supp : ∀ {D : D7} (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D) (x : WO S T), e * e = e → IsHalf (cA D e) x → ∀ i j, toEAf D e * frMapAdj S T βS βT x i j = frMapAdj S T βS βT x i j := by
  intro D S T βS βT e x he hx i j
  have hN : e • (x.map (cA D))ᵀ = (x.map (cA D))ᵀ := by
    ext k l
    simp only [Matrix.smul_apply, Matrix.transpose_apply, Matrix.map_apply, smul_eq_mul]
    have h1 := hx l k
    have h2 : cA D (x l k) = e * cA D (x l k) := by
      conv_lhs => rw [← h1]
      rw [map_mul, cA_cA]
    exact h2.symm
  have hM := smul_mul_mul_of_smul_eq e ((S.gram⁻¹).map (incA D)) _ (T.gram.map (incA D)) hN
  have hM' := map_smul_of_smul_eq (toEAf D) e _ hM
  have hF := smul_mul_mul_of_smul_eq (toEAf D e) (βS⁻¹).val _ βT.val hM'
  have := congrFun (congrFun hF i) j
  rw [Matrix.smul_apply, smul_eq_mul] at this
  exact this

end GlobalTheory.HalfSupp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameMatrixAdjointSupportedOfConjHalfStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameMatrixAdjoint_supported_of_conjHalf : ∀ {D : D7} (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D) (x : WO S T), e * e = e → IsHalf (cA D e) x → ∀ i j, toEAf D e * frMapAdj S T βS βT x i j = frMapAdj S T βS βT x i j := by
  first | exact @GlobalTheory.HalfSupp.frMapAdj_supp | exact GlobalTheory.HalfSupp.frMapAdj_supp | (intros; apply GlobalTheory.HalfSupp.frMapAdj_supp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IndexNormalizationInertNormEqNeg
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IndexNormalizationInertNormEqNeg
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LamInert

theorem lam_qV_inert : ∀ (D : D7) (lam : ℕ →* ℂ), GlobalTheory.FinWeil.GoodNorm (GlobalTheory.FinWeil.sgO D) lam → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), IsInertAt D.host.F D.host.E v w → lam (qV D.host.E w) = -((qV D.host.F v : ℕ) : ℂ) := by
  intro D lam hl v w hw
  have hmap : Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) v.asIdeal = w.asIdeal := hw
  have hfix : ∀ x : 𝓞 D.host.F, GlobalTheory.FinWeil.sgO D (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) =
      algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x := fun x => by
    apply RingOfIntegers.coe_injective
    refine (GlobalTheory.FinWeil.coe_sgO D _).trans ?_
    exact (D.host.conjE_mem_hostF_iff _).1 (by
      change ((x : D.host.F) : D.host.E) ∈ _
      exact (x : D.host.F).2)
  have hstab : ∀ r ∈ w.asIdeal, GlobalTheory.FinWeil.sgO D r ∈ w.asIdeal := by
    rw [← hmap]
    have : Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) v.asIdeal ≤
        (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) v.asIdeal).comap (GlobalTheory.FinWeil.sgO D) := by
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      rw [Ideal.mem_comap, Ideal.mem_comap, hfix]
      exact Ideal.mem_map_of_mem _ hx
    exact fun r hr => this hr
  have hfin : Finite (𝓞 D.host.E ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot
  have h1 := ((hl.2 w.asIdeal w.isMaximal hfin).2 hstab).1
  have hcard : Nat.card (𝓞 D.host.E ⧸ w.asIdeal) = qV D.host.E w := by
    change _ = Ideal.absNorm w.asIdeal
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hsq : qV D.host.E w = qV D.host.F v ^ 2 :=
    GlobalTheory.LFun.InertChart.absNorm_eq (GlobalTheory.AdelicU.isCMExt_host D).2.2.1 hw
  rw [hcard, hsq] at h1
  rw [hsq, h1]
  congr 1
  push_cast
  rw [Real.sqrt_sq (Nat.cast_nonneg _)]
  push_cast
  rfl

end GlobalTheory.LamInert
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IndexNormalizationInertNormEqNegStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indexNormalization_inert_norm_eq_neg : ∀ (D : D7) (lam : ℕ →* ℂ), GlobalTheory.FinWeil.GoodNorm (GlobalTheory.FinWeil.sgO D) lam → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), IsInertAt D.host.F D.host.E v w → lam (qV D.host.E w) = -((qV D.host.F v : ℕ) : ℂ) := by
  first | exact @GlobalTheory.LamInert.lam_qV_inert | exact GlobalTheory.LamInert.lam_qV_inert | (intros; apply GlobalTheory.LamInert.lam_qV_inert <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedQuadraticCharSignSplitEqOneInertEqNeg
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedQuadraticCharSignSplitEqOneInertEqNeg
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QuadSignLocal

theorem primesOver_eq_image (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    Ideal.primesOver v.asIdeal (𝓞 D.host.E) =
      HeightOneSpectrum.asIdeal '' {u : HeightOneSpectrum (𝓞 D.host.E) | u.under (𝓞 D.host.F) = v} := by
  ext P
  constructor
  · rintro ⟨hP, hlo⟩
    refine ⟨⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩, ?_, rfl⟩
    ext1
    simp only [HeightOneSpectrum.under_asIdeal]
    exact (Ideal.LiesOver.over (P := P) (p := v.asIdeal)).symm
  · rintro ⟨u, hu, rfl⟩
    refine ⟨u.isPrime, ⟨?_⟩⟩
    have := congrArg HeightOneSpectrum.asIdeal hu
    simp only [HeightOneSpectrum.under_asIdeal] at this
    exact this.symm

theorem ncard_primesOver (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    (Ideal.primesOver v.asIdeal (𝓞 D.host.E)).ncard =
      {u : HeightOneSpectrum (𝓞 D.host.E) | u.under (𝓞 D.host.F) = v}.ncard := by
  rw [primesOver_eq_image]
  exact Set.ncard_image_of_injective _ (fun a b h => HeightOneSpectrum.ext h)

theorem quadSign_split_inert : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)), (∀ w w' : HeightOneSpectrum (𝓞 D.host.E), w ≠ w' → (∀ u : HeightOneSpectrum (𝓞 D.host.E), u.under (𝓞 D.host.F) = v ↔ u = w ∨ u = w') → quadSign D v = 1) ∧ (∀ w : HeightOneSpectrum (𝓞 D.host.E), (∀ u : HeightOneSpectrum (𝓞 D.host.E), u.under (𝓞 D.host.F) = v ↔ u = w) → quadSign D v = -1) := by
  intro D v
  constructor
  · intro w w' hne h
    have hs : {u : HeightOneSpectrum (𝓞 D.host.E) | u.under (𝓞 D.host.F) = v} = {w, w'} := by
      ext u; simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]; exact h u
    have h2 : (Ideal.primesOver v.asIdeal (𝓞 D.host.E)).ncard = 2 := by
      rw [ncard_primesOver, hs, Set.ncard_pair hne]
    unfold quadSign
    rw [if_pos h2]
  · intro w h
    have hs : {u : HeightOneSpectrum (𝓞 D.host.E) | u.under (𝓞 D.host.F) = v} = {w} := by
      ext u; simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]; exact h u
    have h1 : (Ideal.primesOver v.asIdeal (𝓞 D.host.E)).ncard = 1 := by
      rw [ncard_primesOver, hs, Set.ncard_singleton]
    unfold quadSign
    rw [if_neg (by rw [h1]; decide)]

end GlobalTheory.QuadSignLocal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedQuadraticCharSignSplitEqOneInertEqNegStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedQuadraticCharSign_split_eq_one_inert_eq_neg : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)), (∀ w w' : HeightOneSpectrum (𝓞 D.host.E), w ≠ w' → (∀ u : HeightOneSpectrum (𝓞 D.host.E), u.under (𝓞 D.host.F) = v ↔ u = w ∨ u = w') → quadSign D v = 1) ∧ (∀ w : HeightOneSpectrum (𝓞 D.host.E), (∀ u : HeightOneSpectrum (𝓞 D.host.E), u.under (𝓞 D.host.F) = v ↔ u = w) → quadSign D v = -1) := by
  first | exact @GlobalTheory.QuadSignLocal.quadSign_split_inert | exact GlobalTheory.QuadSignLocal.quadSign_split_inert | (intros; apply GlobalTheory.QuadSignLocal.quadSign_split_inert <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PosAtBase
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.PosAtBase

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem Wp3_eq {R : RealDat3 D A3 Ks}
    (hU : ∀ p c c', R.Carries p c → R.Carries p c' → R.EEc c = R.EEc c' ∧ ∀ i, R.Wc' i c = R.Wc' i c')
    {p : A3.fam3.base3.Ix} {c0 : Pl D.host.E → List ℤ → ℂ} (h0 : R.Carries p c0) (i : Fin D.R.m) :
    R.Wp3 i p = R.Wc' i c0 := by
  apply le_antisymm
  · exact iSup₂_le fun c hc ↦ ((hU p c c0 hc h0).2 i).le
  · exact le_iSup₂_of_le (f := fun c (_ : R.Carries p c) ↦ R.Wc' i c) c0 h0 le_rfl

theorem EEp3_eq {R : RealDat3 D A3 Ks}
    (hU : ∀ p c c', R.Carries p c → R.Carries p c' → R.EEc c = R.EEc c' ∧ ∀ i, R.Wc' i c = R.Wc' i c')
    {p : A3.fam3.base3.Ix} {c0 : Pl D.host.E → List ℤ → ℂ} (h0 : R.Carries p c0) :
    R.EEp3 p = R.EEc c0 := by
  apply le_antisymm
  · exact iSup₂_le fun c hc ↦ (hU p c c0 hc h0).1.le
  · exact le_iSup₂_of_le (f := fun c (_ : R.Carries p c) ↦ R.EEc c) c0 h0 le_rfl

theorem Wp3_bot {R : RealDat3 D A3 Ks} {p : A3.fam3.base3.Ix} (h : ∀ c, ¬ R.Carries p c) (i : Fin D.R.m) :
    R.Wp3 i p = ⊥ := by
  unfold RealDat3.Wp3
  simp [h]

theorem EEp3_bot {R : RealDat3 D A3 Ks} {p : A3.fam3.base3.Ix} (h : ∀ c, ¬ R.Carries p c) :
    R.EEp3 p = ⊥ := by
  unfold RealDat3.EEp3
  simp [h]

end GlobalTheory.PosAtBase

namespace GlobalTheory.PosAtBase


set_option maxHeartbeats 1000000 in
theorem pos_at_base {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ} (_hOk : A3.fam3.Ok3 s) (hC : R.WeakCharacterisation F) (_hE : R.toRealDat.ExAt)
    (hS : Scal R.toRealDat R.SF) (hM : MatchUp R.toRealDat R.SF)
    (hU : ∀ p c c', R.Carries p c → R.Carries p c' → R.EEc c = R.EEc c' ∧ ∀ i, R.Wc' i c = R.Wc' i c')
    (hex : ∃ p, R.EEp3 p ≠ ⊥) :
    0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0 := by
  obtain ⟨lam, κ, hκ, hl, hA, hB⟩ := hS
  have hlam : ∀ i t p c, R.Carries p c → R.Wc' i c ≠ ⊥ → R.lam3 i t p A3.A.v0 = lam i t c := by
    intro i t p c hc hne
    have hW := Wp3_eq hU hc i
    refine hC.scal.lam0 i t p _ (by rw [hW]; exact hne) fun x hx ↦ hA i t c x ?_
    rw [hW] at hx
    exact hx
  have hpos : ∀ i t p, 0 < R.lam3 i t p A3.A.v0 := by
    intro i t p
    by_cases hW : R.Wp3 i p = ⊥
    · rw [hC.scal.abs0 i t p hW]
      exact Real.exp_pos _
    · by_cases hc : ∃ c, R.Carries p c
      · obtain ⟨c, hc⟩ := hc
        rw [hlam i t p c hc (by rw [← Wp3_eq hU hc i]; exact hW)]
        exact hl i t c
      · exact absurd (Wp3_bot (not_exists.1 hc) i) hW
  refine ⟨?_, hpos⟩
  have hK : Lift.IsKap D.R.m (fun t ↦ R.Th t ∘ₗ LinearMap.adjoint (R.Th t)) R.EEp3 R.lamN κ := by
    intro t p x hx
    by_cases hc : ∃ c, R.Carries p c
    · obtain ⟨c, hc⟩ := hc
      have hx' : x ∈ R.EEc c := EEp3_eq hU hc ▸ hx
      have hpr : ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN t j p = ∏ j, lam j t c :=
        (RealDat3.prod_lamN t p).trans (Finset.prod_congr rfl fun j _ ↦ hlam j t p c hc (hM c hc.1 j))
      have h1 := hB t c x hx'
      calc (R.Th t ∘ₗ LinearMap.adjoint (R.Th t)) x = R.Th t (LinearMap.adjoint (R.Th t) x) := rfl
        _ = ((κ * ∏ i, lam i t c : ℝ) : ℂ) • x := h1
        _ = ((κ * ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN t j p : ℝ) : ℂ) • x := by rw [hpr]
    · have hb : R.EEp3 p = ⊥ := EEp3_bot (not_exists.1 hc)
      have hx0 : x = 0 := (Submodule.mem_bot ℂ).1 (hb ▸ hx)
      subst hx0
      rw [map_zero, smul_zero]
  obtain ⟨p, hp⟩ := hex
  rw [hC.scal.kap κ hK ⟨A3.A.μ0, p, hp, ?_⟩]
  · exact hκ
  · rw [RealDat3.prod_lamN]
    exact (Finset.prod_pos fun j _ ↦ hpos j _ p).ne'

end GlobalTheory.PosAtBase
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqMulProdOfPartial
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.RealLine

structure CoverW {p q r s : ℕ} {T₁ : GrpData p q} {T₂ : GrpData r s} (R₁ : DSRep T₁) (R₂ : DSRep T₂)
    (B : Pol p q r s →ₗ[ℂ] R₂.HK.V →ₛₗ[starRingEnd ℂ] R₁.HK.V) : Prop where
  adj : ∀ P x, ∃ b, ∀ y, ⟪R₁.ι x, R₁.ι (B P y)⟫_ℂ = ⟪R₂.ι y, R₂.ι b⟫_ℂ
  src : ∀ Z ∈ upq p q, ∀ P y, B (fockAct1 p q r s Z P) y = R₁.HK.act Z (B P y)
  tgt : ∀ Z ∈ upq r s, ∀ P y, B (fockAct2 p q r s Z P) y + B P (R₂.HK.act Z y) = 0

variable {D : D7} {V W : HSp D} {S S' : D.what₂.Tau → SPar} (M : DSModel V S) (M' : DSModel W S')

structure SemiW (τ : D.what₂.Tau) (aS aT : ℚ) (A : PolF D W.rank V.rank →ₗ[ℂ] M'.sm τ →ₗ[ℂ] M.H τ) : Prop where
  bdd : ∀ φ u, ∃ c : ℝ, ∀ y : M'.sm τ, ‖⟪u, A φ y⟫_ℂ‖ ≤ c * ‖(y : M'.H τ)‖
  eqK : ∀ h ∈ Formalism.REAL.Kset (M.ε τ), ∀ φ, ∃ φ', φ'.totalDegree ≤ φ.totalDegree ∧ ∀ y, A φ' y = M.σ τ h (A φ y)
  invK : ∀ k ∈ Formalism.REAL.Kset (M'.ε τ), ∀ φ, ∃ φ', φ'.totalDegree ≤ φ.totalDegree ∧
    ∀ y y' : M'.sm τ, (y' : M'.H τ) = M'.σ τ k y → A φ' y' = A φ y
  src : ∀ X ∈ lieAt V τ, ∀ φ y u, HasDerivAt (fun t : ℝ => ⟪u, M.rep τ (NormedSpace.exp (t • X)) (A φ y)⟫_ℂ)
    ⟪u, A (srcOp M M' τ aT X φ) y⟫_ℂ 0
  tgt : ∀ Y ∈ lieAt W τ, ∀ φ (y y' : M'.sm τ),
    HasDerivAt (fun t : ℝ => M'.rep τ (NormedSpace.exp (t • Y)) y) (y' : M'.H τ) 0 →
      A (tgtOp M M' τ aS Y φ) y + A φ y' = 0

structure LocW (τ : D.what₂.Tau) (aS aT : ℚ) (A : LPol W.rank V.rank →ₗ[ℂ] M'.sm τ →ₗ[ℂ] M.H τ) : Prop where
  kS : ∀ P y, Formalism.MainNotions.S.IsKFin (M.ε τ) (M.σ τ) (A P y)
  kT : ∀ P u, ∃ b : M'.H τ, Formalism.MainNotions.S.IsKFin (M'.ε τ) (M'.σ τ) b ∧ ∀ y : M'.sm τ, ⟪u, A P y⟫_ℂ = ⟪b, (y : M'.H τ)⟫_ℂ
  src : ∀ X ∈ lieAt V τ, ∀ P y u, HasDerivAt (fun t : ℝ => ⟪u, M.rep τ (NormedSpace.exp (t • X)) (A P y)⟫_ℂ)
    ⟪u, A (locS (M.ε τ) (M'.ε τ) ((M.fr τ * X * (M.fr τ)⁻¹).map (starRingEnd ℂ)) P - ((aT : ℂ) * X.trace) • P) y⟫_ℂ 0
  tgt : ∀ Y ∈ lieAt W τ, ∀ P (y y' : M'.sm τ),
    HasDerivAt (fun t : ℝ => M'.rep τ (NormedSpace.exp (t • Y)) y) (y' : M'.H τ) 0 →
      A (locT (M.ε τ) (M'.ε τ) (M'.fr τ * Y * (M'.fr τ)⁻¹) P + ((aS : ℂ) * Y.trace) • P) y + A P y' = 0

theorem eq_mul_prod_of_partial {ι : Type} [Fintype ι] [DecidableEq ι] {A : ι → Type} (l : ∀ i, A i → ℂ)
    (F : (∀ i, A i) → ℂ) (h : ∀ i a, ∃ c : ℂ, ∀ x, F (Function.update a i x) = c * l i x) :
    ∃ c : ℂ, ∀ a, F a = c * ∏ i, l i (a i) := by

  have key : ∀ (a : ∀ i, A i) (i : ι) (x : A i),
      F (Function.update a i x) * l i (a i) = F a * l i x := by
    intro a i x
    obtain ⟨c, hc⟩ := h i a
    have h1 := hc (a i)
    rw [Function.update_eq_self] at h1
    rw [hc x, h1]
    ring
  by_cases hF : ∀ a, F a = 0
  · exact ⟨0, fun a => by simp [hF a]⟩
  push_neg at hF
  obtain ⟨a₀, ha₀⟩ := hF
  have hl : ∀ i, l i (a₀ i) ≠ 0 := by
    intro i hi
    obtain ⟨c, hc⟩ := h i a₀
    have h1 := hc (a₀ i)
    rw [Function.update_eq_self, hi, mul_zero] at h1
    exact ha₀ h1

  have main : ∀ s : Finset ι, ∀ a : ∀ i, A i, (∀ j, j ∉ s → a j = a₀ j) →
      F a * ∏ j ∈ s, l j (a₀ j) = F a₀ * ∏ j ∈ s, l j (a j) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro a ha
      rw [show a = a₀ from funext fun j => ha j (by simp)]
    | @insert i s hi ih =>
      intro a ha
      have hoff : ∀ j, j ∉ s → Function.update a i (a₀ i) j = a₀ j := by
        intro j hj
        by_cases hji : j = i
        · subst hji
          simp
        · rw [Function.update_of_ne hji]
          exact ha j (by simp [hji, hj])
      have e1 := ih _ hoff
      have e2 := key (Function.update a i (a₀ i)) i (a i)
      simp only [Function.update_idem, Function.update_eq_self, Function.update_self] at e2
      have hprod : ∏ j ∈ s, l j (Function.update a i (a₀ i) j) = ∏ j ∈ s, l j (a j) :=
        Finset.prod_congr rfl fun j hj => by
          have hji : j ≠ i := fun e => hi (e ▸ hj)
          rw [Function.update_of_ne hji]
      rw [hprod] at e1
      rw [Finset.prod_insert hi, Finset.prod_insert hi]
      calc F a * (l i (a₀ i) * ∏ j ∈ s, l j (a₀ j))
          = (F a * l i (a₀ i)) * ∏ j ∈ s, l j (a₀ j) := by ring
        _ = (F (Function.update a i (a₀ i)) * l i (a i)) * ∏ j ∈ s, l j (a₀ j) := by rw [e2]
        _ = l i (a i) * (F (Function.update a i (a₀ i)) * ∏ j ∈ s, l j (a₀ j)) := by ring
        _ = l i (a i) * (F a₀ * ∏ j ∈ s, l j (a j)) := by rw [e1]
        _ = F a₀ * (l i (a i) * ∏ j ∈ s, l j (a j)) := by ring
  have hP : ∏ j, l j (a₀ j) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hl j
  refine ⟨F a₀ / ∏ j, l j (a₀ j), fun a => ?_⟩
  rw [div_mul_eq_mul_div, eq_div_iff hP]
  exact main Finset.univ a fun j hj => absurd (Finset.mem_univ j) hj

end GlobalTheory.Chain.RealLine

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatOfOneMapOverL
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistField.Read

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

theorem mult_inv {V : HSp D} {S : D.what₂.Tau → _} (θ) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) {Φ : MMap M}
    (hΦ : Φ ∈ Mult θ M J χ) (v : M.Vec) : ∀ γ ∈ GQ V, ∀ g, Φ v (γ * g) = Φ v g := by
  intro γ hγ g
  induction hΦ using Submodule.span_induction with
  | mem x hx => exact (hx.aut v).left γ hγ g
  | zero => rfl
  | add x y _ _ hx hy => simp only [_root_.add_apply, Pi.add_apply, hx, hy]
  | smul a x _ hx => simp only [_root_.smul_apply, Pi.smul_apply, hx]

theorem eq_of_out {W : HSp D} {Φ Ψ : GA D W → ℂ} (hΦ : ∀ γ ∈ GQ W, ∀ g, Φ (γ * g) = Φ g)
    (hΨ : ∀ γ ∈ GQ W, ∀ g, Ψ (γ * g) = Ψ g) (h : ∀ q : AutQ W, Φ q.out = Ψ q.out) : Φ = Ψ := by
  funext g
  let q : AutQ W := Quotient.mk _ g
  have hr : g * q.out⁻¹ ∈ GQ W := QuotientGroup.rightRel_apply.1 (Quotient.exact (Quotient.out_eq q))
  have h1 := hΦ _ hr q.out
  have h2 := hΨ _ hr q.out
  rw [inv_mul_cancel_right] at h1 h2
  rw [h1, h2, h q]

theorem ev_sum {L H Y : Type} [Field L] [AddCommGroup H] [Module ℂ H] [AddCommGroup Y] [Module L Y] {σ : L →+* ℂ}
    (j : Y →ₛₗ[σ] H) {V : HSp D} {S : D.what₂.Tau → _} {M : DSModel V S} (e : H →ₗ[ℂ] MMap M) (v : M.Vec) (g : GA D V) {m : ℕ}
    (a : Fin m → L) (y : Fin m → Y) : e (j (∑ l, a l • y l)) v g = ∑ l, σ (a l) * e (j (y l)) v g := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, _root_.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_smulₛₗ, map_smul]
  rfl

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

theorem ev_base (fw : FWTie T R κ v₀) (hev : fw.Evaluates) {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}
    (O : OMDat T.toCore R i Tp tup) (f : Cu T κ i) (h : GA D (Wc D i)) :
    (R.HW i (sg0 D A)).e (fw.jK i (sg0 D A) f) (v₀ i (sg0 D A)) h =
      (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) *
        O.phi (T.cE ((i : ℕ) + 1) O.s0) (f : T.R ((i : ℕ) + 1)) h := by
  have e : res T (sg0 D A) = O.s0 :=
    ((congrArg (res T) (show sg0 D A = D.what₂.embLL from sgAt_mk _ R.hv0)).trans
      (res_embLL T fw.alg_eq fw.laws.pins.2.2.1)).trans (sOv_eq T.toCore O.c' O.hle).symm
  have hV : T.V ((i : ℕ) + 1) (res T (sg0 D A)) = Wc D i := (congrArg (T.V ((i : ℕ) + 1)) e).trans O.hV
  have h1 := hev i (sg0 D A) (base_embedding_good T R fw.alg_eq fw.laws.pins.2.2.1) hV f
  have key : ∀ (σ σ' : T.Q.c.F →+* ℂ) (_ : σ' = σ) (W : HSp D) (hV : T.V ((i : ℕ) + 1) σ = W)
      (hV' : T.V ((i : ℕ) + 1) σ' = W) (g : GA D W), phiC T hV' (wtA (κ i)) (f : T.R ((i : ℕ) + 1)) g =
      (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) * adel W (castDict hV (T.dict ((i : ℕ) + 1) σ))
        (muPin W (castDict hV (T.dict ((i : ℕ) + 1) σ)) (castDict hV (T.mu ((i : ℕ) + 1) σ)) (T.cE ((i : ℕ) + 1) σ))
        (rdU (T.U ((i : ℕ) + 1) σ) (f : T.R ((i : ℕ) + 1))) g := by
    intro σ σ' e W hV hV' g
    subst e
    subst hV
    rfl
  exact (congrFun h1 h).trans (key _ _ e _ O.hV hV h)


set_option maxHeartbeats 1000000 in
theorem exists_comb {i : Fin D.R.m} {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {v : (R.MW i (sg0 D A)).Vec} {ι x₀} {ph : ℂ}
    (hn : κ.n = (Vc D i).rank) (O : OMDat T.toCore R i T0 id) (hP : O.Pins κ v ι x₀)
    (hrow : O.OneMapOf κ v (T.cE ((i : ℕ) + 1) O.s0) ph) (t : T0) (y : A.fam.amb.FL i t) :
    ∃ ze ∈ D.what₂.embLL.toRatAlgHom.fieldRange, ∃ (m : ℕ) (as : Fin m → O.c'.F) (fs : Fin m → T.cuspA ((i : ℕ) + 1) (wtA κ) κ.n),
      ∀ q : AutQ (Wc D i), ph * R.thF i t (R.jV i t y) v q.out =
        ∑ l, ze * (as l : ℂ) * ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) *
          O.phi (T.cE ((i : ℕ) + 1) O.s0) (fs l : T.R ((i : ℕ) + 1)) q.out) := by
  obtain ⟨hE, ⟨-, hC, hA, -, -, z, -, h1⟩, -⟩ := hrow
  have aux1 := h1 t
  obtain ⟨ze, a1, -, h1⟩ := aux1
  have aux2 := (hP.tuple t).reps
  obtain ⟨h, J', -, p2, p3, p4⟩ := aux2
  have aux3 := p2 y
  obtain ⟨x, hx⟩ := aux3
  have e := p3 _ x hx
  have aux4 := h1 x ((p4 x).2 ⟨y, hx⟩)
  obtain ⟨⟨f, hf, hf'⟩, h2⟩ := aux4
  have hs := ((mem_cusp _ _ _ _ _ _).1 hf).1
  have h4 := h2 f hs hf'
  rw [← hn] at hf
  have aux5 := hC _ _ f hf
  obtain ⟨m, as, fs, hfs, hBC⟩ := aux5
  have aux6 := hP.lift.lev z
  obtain ⟨k, hk, -⟩ := aux6
  have h5 := rdU_unfBC O.hle (T.U ((i : ℕ) + 1)) (inC O.c') (hA _ _ z m as fs f ((mem_cusp _ _ _ _ _ _).1 hf).1
    (fun l => ((mem_cusp _ _ _ _ _ _).1 (hfs l)).1) hBC)
  refine ⟨ze, a1, m, as, fun l => ⟨_, (hE z k hk (fs l) (hfs l)).1⟩, fun q => ?_⟩
  have h6 : ph * R.thF i t (R.jV i t y) v q.out = ze * T.cE ((i : ℕ) + 1) O.s0 (O.dict q.out).1 *
      (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * (O.mu q.out *
        rdU (unfBC O.hle (T.U ((i : ℕ) + 1)) (inC O.c')) (actLev O.c' O.lev2 z f) (O.dict q.out).1 (O.dict q.out).2) :=
    (congrArg (ph * ·) (congrFun e q)).symm.trans (h4 q)
  rw [h6, h5]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  show _ = ze * (as l : ℂ) * (_ * (T.cE ((i : ℕ) + 1) O.s0 (O.dict q.out).1 * O.mu q.out *
    rdU (T.U ((i : ℕ) + 1) O.s0) (actLev T.Q.c O.lev2 z (fs l)) (O.dict q.out).1 (O.dict q.out).2))
  show _ * (_ * ((as l : ℂ) * _)) = _
  ring


set_option maxHeartbeats 1000000 in
theorem ratAt_of_oneMap (fw : FWTie T R κ v₀) {ph : ℂ} {i : Fin D.R.m} (hW : R.models_HW) (hP : R.IsThP) (hU : R.LUnif)
    (hev : fw.Evaluates) (hinj : EvInj T R v₀) (h : OneMapOverL T R κ v₀ ph i) (t : T0) : GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.RatAt R i ph t := by
  intro x₀
  obtain ⟨O, hF, hpin, hrow⟩ := h
  have hn : (κ i).n = (Vc D i).rank :=
    (fw.kap i (D.eTau.symm 1)).2.2.trans (D.sp.V_rank ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2).symm
  have aux7 := exists_comb hn O hpin hrow t x₀
  obtain ⟨ze, hze, m, as, fs, hq⟩ := aux7
  have hs : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0
  have ha : ∀ l, ∃ a : D.what₂.LL, sg0 D A a = ze * (as l : ℂ) := fun l => by
    have aux8 := AlgHom.mem_fieldRange.1 (mul_mem hze (hF.le (as l).2))
    obtain ⟨a, ha⟩ := aux8
    exact ⟨a, (RingHom.congr_fun hs a).trans ha⟩
  choose a ha using ha
  have hmem := (hW i (sg0 D A)).2.1.ge (hP.thF_mem i t (R.jV i t x₀))
  obtain ⟨w, hw⟩ := hmem
  have hinv : ∀ u : (R.HW i (sg0 D A)).H, ∀ γ ∈ GQ (Wc D i), ∀ g,
      evAt R i _ (v₀ i _) u (γ * g) = evAt R i _ (v₀ i _) u g := fun u =>
    mult_inv R.θ _ _ _ ((hW i _).2.1.le (LinearMap.mem_range_self _ u)) _
  have e0 : (R.HW i (sg0 D A)).e (ph • w) = ph • R.thF i t (R.jV i t x₀) :=
    (map_smul (R.HW i (sg0 D A)).e ph w).trans (congrArg (ph • ·) hw)
  have key : (R.FW i).j (sg0 D A) (∑ l, a l • ((fw.e i (fs l) : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL)) = ph • w := by
    refine hinj i _ (base_embedding_good T R fw.alg_eq fw.laws.pins.2.2.1) (eq_of_out (hinv _) (hinv _) fun q => ?_)
    have e1 : evAt R i _ (v₀ i _) (ph • w) q.out = ph * R.thF i t (R.jV i t x₀) (v₀ i _) q.out :=
      congrArg (fun Φ : MMap (R.MW i (sg0 D A)) => Φ (v₀ i _) q.out) e0
    refine (ev_sum _ _ _ _ _ _).trans (Eq.trans ?_ ((hq q).symm.trans e1.symm))
    exact Finset.sum_congr rfl fun l _ => congrArg₂ (· * ·) (ha l) (ev_base fw hev O (fs l) q.out)
  have h1 := (congrArg (R.HW i (sg0 D A)).e key).trans e0
  exact ⟨_, h1, GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.proj_clause R i ph t hP.thG (hW i _).1 (hU i _).2.2 _ _ h1⟩

theorem rat_of_oneMapOverL : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T R κ v₀) (ph : ℂ) (i : Fin D.R.m), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → R.IsThP → R.LUnif → fw.Evaluates → EvInj T R v₀ → GlobalTheory.TwistField.OneMapOverL T R κ v₀ ph i → ∀ t : T0, GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.RatAt R i ph t :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ fw _ _ _ _ hM hP hU hev hinj h t => ratAt_of_oneMap fw hM.HW hP hU hev hinj h t

end GlobalTheory.TwistField.Read
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EquivariantOfGeneratorOneParameterGroupStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EquivariantOfGeneratorOneParameterGroup
noncomputable section

namespace GlobalTheory.OneParamEquivariance

theorem hasDerivAt_apply {F : Type*} [AddCommGroup F] [Module ℂ F] [FiniteDimensional ℂ F]
    (A : ℝ → F →ₗ[ℂ] ℂ) (A' : F →ₗ[ℂ] ℂ) (c : ℝ → F) (c' : F)
    (hA : ∀ x, HasDerivAt (fun t => A t x) (A' x) 0)
    (hc : ∀ f : F →ₗ[ℂ] ℂ, HasDerivAt (fun t => f (c t)) (f c') 0) :
    HasDerivAt (fun t => A t (c t)) (A' (c 0) + A 0 c') 0 := by
  let b := Module.finBasis ℂ F
  have e : ∀ (a : F →ₗ[ℂ] ℂ) u, a u = ∑ i, a (b i) * b.coord i u := by
    intro a u
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [← b.sum_repr u, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
    rfl
  have := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => (hA (b i)).fun_mul (hc (b.coord i))
  have e1 : (fun t => A t (c t)) = fun t => ∑ i, A t (b i) * b.coord i (c t) := funext fun t => e _ _
  rw [e1, e A' (c 0), e (A 0) c', ← Finset.sum_add_distrib]
  exact this

theorem equivariant_of_generator : ∀ (σ Z H : Type) [Finite σ] [AddCommGroup H] [Module ℂ H] (pt : MvPolynomial σ ℂ →ₗ[ℂ] (Z → ℂ)) (R : ℝ → Module.End ℂ (Z → ℂ)) (L : Module.End ℂ (MvPolynomial σ ℂ)) (U : ℝ → Module.End ℂ H) (B : MvPolynomial σ ℂ →ₗ[ℂ] H) (Λ : Set (H →ₗ[ℂ] ℂ)), Function.Injective pt → R 0 = 1 → (∀ s t, R (s + t) = R s * R t) → (∀ t φ, ∃ ψ, ψ.totalDegree ≤ φ.totalDegree ∧ R t (pt φ) = pt ψ) → (∀ φ z, HasDerivAt (fun t : ℝ => R t (pt φ) z) (pt (L φ) z) 0) → U 0 = 1 → (∀ s t, U (s + t) = U s * U t) → (∀ x, (∀ l ∈ Λ, l x = 0) → x = 0) → (∀ l ∈ Λ, ∀ t, l ∘ₗ U t ∈ Λ) → (∀ l ∈ Λ, ∀ φ, HasDerivAt (fun t : ℝ => l (U t (B φ))) (l (B (L φ))) 0) → ∀ φ φ', pt φ' = R 1 (pt φ) → B φ' = U 1 (B φ) := by
  intro σ Z H _ _ _ pt R L U B Λ hpt hR0 hR hdeg hder hU0 hU hsep hΛ hB φ φ' hφ
  choose ρ hρd hρ using hdeg
  have hρ0 : ∀ ψ, ρ 0 ψ = ψ := fun ψ => hpt (by rw [← hρ, hR0]; rfl)
  have hρadd : ∀ s t ψ, ρ (s + t) ψ = ρ s (ρ t ψ) := fun s t ψ => hpt (by
    rw [← hρ, ← hρ, ← hρ, hR]; rfl)
  have key : ∀ l ∈ Λ, ∀ ψ, HasDerivAt (fun s : ℝ => l (U (-s) (B (ρ s ψ)))) 0 0 := by
    intro l hl ψ
    let F := MvPolynomial.restrictTotalDegree σ ℂ (max ψ.totalDegree (L ψ).totalDegree)
    have hc : ∀ s, ρ s ψ ∈ F := fun s =>
      (MvPolynomial.mem_restrictTotalDegree _ _ _).2 ((hρd s ψ).trans (le_max_left _ _))
    have hy : L ψ ∈ F := (MvPolynomial.mem_restrictTotalDegree _ _ _).2 (le_max_right _ _)
    have h1 := GlobalTheory.CompactIntertwiner.hasDerivAt_dual_of_sep (F := F)
      (fun z => (LinearMap.proj z ∘ₗ pt) ∘ₗ F.subtype)
      (fun x hx => Subtype.ext (hpt (by rw [Submodule.coe_zero, map_zero]; exact funext hx)))
      (fun s => ⟨ρ s ψ, hc s⟩) ⟨L ψ, hy⟩ (fun z => by
        have := hder ψ z
        simp only [hρ] at this
        exact this)
    have h2 : ∀ x : F, HasDerivAt (fun s : ℝ => (l ∘ₗ U (-s) ∘ₗ B ∘ₗ F.subtype) x)
        ((-(l ∘ₗ B ∘ₗ L ∘ₗ F.subtype)) x) 0 := by
      intro x
      have h3 : HasDerivAt (fun t : ℝ => l (U t (B x))) (l (B (L x))) (-0) := by
        rw [neg_zero]; exact hB l hl x
      have h4 := h3.scomp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
      rw [neg_one_smul] at h4
      exact h4
    have h5 := hasDerivAt_apply _ _ _ _ h2 h1
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.neg_apply, hρ0, neg_zero, hU0,
      Module.End.one_apply, neg_add_cancel] at h5
    exact h5
  have hconst : ∀ l ∈ Λ, l (U (-1) (B (ρ 1 φ))) = l (B φ) := by
    intro l hl
    have hd : ∀ t₀ : ℝ, HasDerivAt (fun t : ℝ => l (U (-t) (B (ρ t φ)))) 0 t₀ := by
      intro t₀
      have h1 : HasDerivAt (fun s : ℝ => (l ∘ₗ U (-t₀)) (U (-s) (B (ρ s (ρ t₀ φ))))) 0 (t₀ - t₀) := by
        rw [sub_self]; exact key _ (hΛ l hl _) _
      have h2 := h1.comp_sub_const t₀ t₀
      refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
      have e : -t₀ + -(t - t₀) = -t := by ring
      beta_reduce
      rw [← hρadd, sub_add_cancel, LinearMap.comp_apply, ← Module.End.mul_apply, ← hU, e]
    have := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) 1 0
    simpa [hρ0, hU0] using this
  have h1 : U (-1) (B (ρ 1 φ)) = B φ :=
    sub_eq_zero.1 (hsep _ fun l hl => by rw [map_sub, hconst l hl, sub_self])
  have h2 : φ' = ρ 1 φ := hpt (by rw [hφ, hρ])
  rw [← h1, ← Module.End.mul_apply, ← hU, add_neg_cancel, hU0, h2]
  rfl

end GlobalTheory.OneParamEquivariance

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equivariant_of_generator_oneParameterGroup : ∀ (σ Z H : Type) [Finite σ] [AddCommGroup H] [Module ℂ H] (pt : MvPolynomial σ ℂ →ₗ[ℂ] (Z → ℂ)) (R : ℝ → Module.End ℂ (Z → ℂ)) (L : Module.End ℂ (MvPolynomial σ ℂ)) (U : ℝ → Module.End ℂ H) (B : MvPolynomial σ ℂ →ₗ[ℂ] H) (Λ : Set (H →ₗ[ℂ] ℂ)), Function.Injective pt → R 0 = 1 → (∀ s t, R (s + t) = R s * R t) → (∀ t φ, ∃ ψ, ψ.totalDegree ≤ φ.totalDegree ∧ R t (pt φ) = pt ψ) → (∀ φ z, HasDerivAt (fun t : ℝ => R t (pt φ) z) (pt (L φ) z) 0) → U 0 = 1 → (∀ s t, U (s + t) = U s * U t) → (∀ x, (∀ l ∈ Λ, l x = 0) → x = 0) → (∀ l ∈ Λ, ∀ t, l ∘ₗ U t ∈ Λ) → (∀ l ∈ Λ, ∀ φ, HasDerivAt (fun t : ℝ => l (U t (B φ))) (l (B (L φ))) 0) → ∀ φ φ', pt φ' = R 1 (pt φ) → B φ' = U 1 (B φ) := by
  first | exact @GlobalTheory.OneParamEquivariance.equivariant_of_generator | exact GlobalTheory.OneParamEquivariance.equivariant_of_generator | (intros; apply GlobalTheory.OneParamEquivariance.equivariant_of_generator <;> assumption)
end
