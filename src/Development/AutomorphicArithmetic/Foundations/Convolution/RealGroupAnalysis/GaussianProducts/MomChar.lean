module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.HatSt

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.MomChar
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

theorem UpperTheory.ConvolutionTheory.R2.G.momChar :
    ∀ (Ω ι : Type) [MeasurableSpace Ω] [Fintype ι] (ν : Measure Ω) (X : Ω → ι → ℝ) (ρ : Ω → ℂ), Measurable X →
    (∀ R : ℝ, Integrable (fun ω => ((Real.exp (R * ∑ i, |X ω i|) : ℝ) : ℂ) * ρ ω) ν) →
    (∀ (n : ℕ) (t : ι → ℝ), ∫ ω, ((∑ i, t i * X ω i : ℝ) : ℂ) ^ n * ρ ω ∂ν = 0) →
    ∀ t : ι → ℝ, ∫ ω, Complex.exp (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) * ρ ω ∂ν = 0 := by
  intro Ω ι _ _ ν X ρ hX hint hmom t
  have hym : Measurable (fun ω => ∑ i, t i * X ω i) :=
    Finset.measurable_sum _ (fun i _ => ((measurable_pi_apply i).comp hX).const_mul (t i))
  have hρ : Integrable ρ ν := by simpa using hint 0
  have hbound : ∀ ω, |∑ i, t i * X ω i| ≤ (∑ i, |t i|) * ∑ i, |X ω i| := by
    intro ω
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun i _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (f := fun j => |X ω j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i))
      (abs_nonneg _)
  have hdom : Integrable (fun ω => Real.exp |∑ i, t i * X ω i| * ‖ρ ω‖) ν := by
    refine (hint (∑ i, |t i|)).norm.mono'
      (((Real.measurable_exp.comp (continuous_abs.measurable.comp hym)).aestronglyMeasurable).mul hρ.norm.aestronglyMeasurable)
      (Eventually.of_forall fun ω => ?_)
    simp only [norm_mul, norm_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [abs_norm]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (hbound ω)) (norm_nonneg (ρ ω))
  have hsum := hasSum_integral_of_dominated_convergence (μ := ν)
    (F := fun (n : ℕ) ω => (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) ^ n / (n.factorial : ℂ) * ρ ω)
    (f := fun ω => Complex.exp (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) * ρ ω)
    (fun (n : ℕ) ω => |∑ i, t i * X ω i| ^ n / (n.factorial : ℝ) * ‖ρ ω‖)
    (fun n => ?_) (fun n => ?_) ?_ ?_ ?_
  · have hz : (fun n : ℕ => ∫ ω, (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) ^ n / (n.factorial : ℂ) * ρ ω ∂ν)
        = fun _ => 0 := by
      funext n
      have : ∀ ω, (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) ^ n / (n.factorial : ℂ) * ρ ω
          = (Complex.I ^ n / (n.factorial : ℂ)) * (((∑ i, t i * X ω i : ℝ) : ℂ) ^ n * ρ ω) := by
        intro ω; rw [mul_pow]; ring
      simp_rw [this]
      rw [integral_const_mul, hmom n t, mul_zero]
    rw [hz] at hsum
    exact hsum.unique hasSum_zero |>.symm ▸ rfl
  · have hc : Measurable (fun ω => ((∑ i, t i * X ω i : ℝ) : ℂ)) := Complex.measurable_ofReal.comp hym
    exact ((((hc.mul_const Complex.I).pow_const n).div_const _).aestronglyMeasurable).mul hρ.aestronglyMeasurable
  · refine Eventually.of_forall fun ω => ?_
    rw [norm_mul, norm_div, norm_pow, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Complex.norm_natCast, Real.norm_eq_abs]
  · exact Eventually.of_forall fun ω =>
      (Real.summable_pow_div_factorial _).mul_right _
  · have : (fun ω => ∑' n : ℕ, |∑ i, t i * X ω i| ^ n / (n.factorial : ℝ) * ‖ρ ω‖)
        = fun ω => Real.exp |∑ i, t i * X ω i| * ‖ρ ω‖ := by
      funext ω
      rw [tsum_mul_right, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    rw [this]; exact hdom
  · refine Eventually.of_forall fun ω => ?_
    have := (NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℂ) (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I)).mul_right (ρ ω)
    rwa [← Complex.exp_eq_exp_ℂ] at this
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.CoefBd
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

theorem UpperTheory.ConvolutionTheory.R2.G.coefBd :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (φ : S4 F) (C : Set (G1 F)) (U : Submodule ℂ (S4 F)), IsCompact C → FiniteDimensional ℂ U → (∀ k ∈ C, W.Om k φ ∈ U) →
    ∃ (n : ℕ) (b : Fin n → S4 F) (c : Fin n → G1 F → ℂ) (B : ℝ), (∀ i, b i ∈ U) ∧ (∀ i, ContinuousOn (c i) C) ∧
    ∀ k ∈ C, (∀ i, ‖c i k‖ ≤ B) ∧ W.Om k φ = ∑ i, c i k • b i := by
  intro F E _ _ _ _ _ _ _ D W φ C U hC hU hmem
  haveI := hU
  let b := Module.finBasis ℂ U
  let ev : V4 F → Module.Dual ℂ U := fun v =>
    { toFun := fun u => (u.1).1 v, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have htop : Submodule.span ℂ (Set.range ev) = ⊤ := by
    have hb : (Submodule.span ℂ (Set.range ev)).dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro u hu
      rw [Submodule.mem_dualCoannihilator] at hu
      have : u = 0 := by
        apply Subtype.ext
        apply Subtype.ext
        funext v
        exact hu (ev v) (Submodule.subset_span ⟨v, rfl⟩)
      simpa using this
    have h2 := Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span ℂ (Set.range ev))
    rw [← h2, hb]
    simp
  have hco : ∀ i, ∃ a : V4 F →₀ ℂ, a.sum (fun v x => x • ev v) = b.coord i := by
    intro i
    have h3 : b.coord i ∈ Submodule.span ℂ (Set.range ev) := by
      rw [htop]
      trivial
    exact (Finsupp.mem_span_range_iff_exists_finsupp).1 h3
  choose a ha using hco
  let c : Fin (Module.finrank ℂ U) → G1 F → ℂ := fun i k => ∑ v ∈ (a i).support, a i v * (W.Om k φ).1 v
  have hc : ∀ i, Continuous (c i) := by
    intro i
    refine continuous_finsetSum _ fun v _ => continuous_const.mul ?_
    exact (W.cont φ).comp (continuous_id.prodMk continuous_const)
  have hB : ∀ i, ∃ B : ℝ, ∀ k ∈ C, ‖c i k‖ ≤ B := fun i =>
    hC.exists_bound_of_continuousOn (hc i).continuousOn
  choose B hB using hB
  refine ⟨Module.finrank ℂ U, fun i => (b i).1, c, ∑ i, |B i|, fun i => (b i).2,
    fun i => (hc i).continuousOn, ?_⟩
  intro k hk
  refine ⟨fun i => ?_, ?_⟩
  · calc ‖c i k‖ ≤ B i := hB i k hk
      _ ≤ |B i| := le_abs_self _
      _ ≤ ∑ i, |B i| := Finset.single_le_sum (f := fun i => |B i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  · have hck : ∀ i, b.repr ⟨W.Om k φ, hmem k hk⟩ i = c i k := by
      intro i
      have h4 : b.coord i ⟨W.Om k φ, hmem k hk⟩ = c i k := by
        rw [← ha i, Finsupp.sum, LinearMap.sum_apply]
        rfl
      simpa using h4
    have h5 := b.sum_repr ⟨W.Om k φ, hmem k hk⟩
    have h6 := congrArg Subtype.val h5
    simp only [hck, Submodule.coe_sum, Submodule.coe_smul] at h6
    exact h6.symm
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.TransN
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

private theorem nu_nE {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (D : Dat F E) (u : Fin 2 → A F) (h : GL (Fin 2) (A E)) :
    nu F (nE D u * h) = nu F h := by
  have hd : Matrix.GeneralLinearGroup.det (nE D u) = 1 := by
    exact Units.ext (nU (D.mkE (u 0) (u 1))).2
  simp only [nu, map_mul, hd, one_mul]

private theorem cD_unit {F : Type} [Field F] [NumberField F] (g : G1 F) : cD (1 : (A F)ˣ) g = g := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cD]

private theorem om_L {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] {D : Dat F E} (W : Weil D)
    (u : Fin 2 → A F) (h : GL (Fin 2) (A E)) (φ : S4 F) (g : G1 F) :
    W.Om g (W.L (nE D u * h) φ) = W.L (nE D u) (W.Om g (W.L h φ)) := by
  have hn : nu F (nE D u) = 1 := by
    have := nu_nE D u 1
    rw [mul_one] at this
    rw [this]
    simp [nu]
  have hc := W.comm (nE D u) g
  rw [hn, cD_unit] at hc
  rw [map_mul, Module.End.mul_apply]
  exact (LinearMap.congr_fun hc (W.L h φ)).symm

theorem UpperTheory.ConvolutionTheory.R2.G.transN :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (f : GL (Fin 2) (A F) → ℂ) (φ : S4 F) (h : GL (Fin 2) (A E)) (u : Fin 2 → A F), T0 W M f φ (nE D u * h) = T0 W M f φ h ∧
    ∀ ξ, Wx W M f φ (nE D u * h) ξ = chi D.δ ξ u * Wx W M f φ h ξ := by
  intro F E _ _ _ _ _ _ _ D W M f φ h u
  have hH : St.Hat W := hatSt F E D W
  have hnu := nu_nE D u h
  constructor
  · unfold T0
    refine setIntegral_congr_fun M.meas fun g _ => ?_
    have hrow : ThRow 0 0 (W.Om g (W.L (nE D u * h) φ)).1 = ThRow 0 0 (W.Om g (W.L h φ)).1 := by
      rw [om_L]
      unfold ThRow
      refine tsum_congr fun ξ => ?_
      have := hH.nE (u 0) (u 1) (W.Om g (W.L h φ)) 0 (rt (ξ 0)) (rt (ξ 1))
      simpa [nE, zero_mul, neg_zero, ψ] using this
    simp only [hnu, hrow]
  · intro ξ
    have hpt : ∀ g, wx W f φ (nE D u * h) ξ g = chi D.δ ξ u * wx W f φ h ξ g := by
      intro g
      unfold wx
      rw [hnu, om_L]
      have := hH.nE (u 0) (u 1) (W.Om g (W.L h φ)) 1 (rt (ξ 0)) (rt (ξ 1))
      have e : hat (W.L (nE D u) (W.Om g (W.L h φ))).1 (pt ξ) =
          chi D.δ ξ u * hat (W.Om g (W.L h φ)).1 (pt ξ) := by
        simpa only [one_mul, chi, pt, nE] using this
      rw [e]
      ring
    unfold Wx Meas.I0
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp only [iw, hpt]
    ring
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.FockMul
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

private theorem poly_pull {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
    {p : (Fin 2 → A F) → ℂ} (hp : p ∈ polyOn F (Fin 2)) :
    (fun v : V4 F => p ![v 0, v 1]) ∈ polyFn (F := F) := by
  induction hp using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, w, rfl⟩ := hx
    refine Algebra.subset_adjoin ?_
    fin_cases i
    · exact ⟨0, w, rfl⟩
    · exact ⟨1, w, rfl⟩
  | algebraMap r => exact Subalgebra.algebraMap_mem _ r
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem hx hy

private theorem ind_mul_mem {F : Type} [Field F] [NumberField F]
    {T : Set (Fin 2 → FiniteAdeleRing (𝓞 F) F)} (hc : IsCompact T) (ho : IsOpen T)
    {g : (Fin 4 → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ finiteSchwartzBruhatPi F (ι := Fin 4)) :
    (fun y : Fin 4 → FiniteAdeleRing (𝓞 F) F =>
      (T.indicator (1 : (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ) ![y 0, y 1]) * g y) ∈
        finiteSchwartzBruhatPi F (ι := Fin 4) := by
  obtain ⟨h1, h2⟩ := (mem_finiteSchwartzBruhatPi F).1 hg
  have hcl : IsClopen T := ⟨hc.isClosed, ho⟩
  have hi : IsLocallyConstant (T.indicator (1 : (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ)) := by
    exact ((LocallyConstant.const (Fin 2 → FiniteAdeleRing (𝓞 F) F) (1 : ℂ)).indicator hcl).isLocallyConstant
  have hcont : Continuous fun y : Fin 4 → FiniteAdeleRing (𝓞 F) F => (![y 0, y 1] : Fin 2 → _) := by
    refine continuous_pi fun i => ?_
    fin_cases i
    · exact continuous_apply 0
    · exact continuous_apply 1
  exact (mem_finiteSchwartzBruhatPi F).2 ⟨(hi.comp_continuous hcont).mul h1, h2.mul_left⟩

theorem UpperTheory.ConvolutionTheory.R2.G.fockMul :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (δ : F), (∀ χ ∈ FockFn δ, ∀ p ∈ polyOn F (Fin 2), ∀ T : Set (Fin 2 → FiniteAdeleRing (𝓞 F) F), IsCompact T → IsOpen T →
    (fun v : V4 F => p ![v 0, v 1] * T.indicator 1 (finPartPi ![v 0, v 1]) * χ v) ∈ FockFn δ) ∧ ∀ v₀ : V4 F, ∃ χ ∈ FockFn δ, χ v₀ ≠ 0 := by
  intro F _ _ _ δ
  refine ⟨?_, ?_⟩
  · intro χ hχ p hp T hc ho
    induction hχ using Submodule.span_induction with
    | mem φ hφ =>
      obtain ⟨q, hq, g, hg, rfl⟩ := hφ
      refine Submodule.subset_span ⟨_, mul_mem (poly_pull hp) hq, _, ind_mul_mem hc ho hg, ?_⟩
      funext v
      have hfin : finPartPi ![v 0, v 1] = ![finPartPi v 0, finPartPi v 1] := by
        funext i
        fin_cases i <;> rfl
      simp only [hfin, Pi.mul_apply]
      ring
    | zero =>
      have : (fun v : V4 F => p ![v 0, v 1] * T.indicator 1 (finPartPi ![v 0, v 1]) * (0 : V4 F → ℂ) v) = 0 := by
        funext v
        simp
      rw [this]
      exact zero_mem _
    | add x y _ _ hx hy =>
      have := add_mem hx hy
      convert this using 1
      funext v
      simp only [Pi.add_apply]
      ring
    | smul a x _ hx =>
      have := Submodule.smul_mem _ a hx
      convert this using 1
      funext v
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
  · intro v₀
    refine ⟨_, Submodule.subset_span ⟨1, one_mem _,
      finiteTensor fun i => cosetIndicator (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (v₀ i).2,
      finiteTensor_mem fun i => cosetIndicator_mem_finiteSchwartzBruhat _ _, rfl⟩, ?_⟩
    have hone : finiteTensor (fun i => cosetIndicator (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (v₀ i).2)
        (finPartPi v₀) = 1 := by
      have hself : ∀ a : FiniteAdeleRing (𝓞 F) F,
          cosetIndicator (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) a a = 1 := fun a => by
        rw [cosetIndicator_apply, if_pos]
        rw [sub_self]
        exact zero_mem _
      exact Finset.prod_eq_one fun i _ => hself _
    simp only [hone, Pi.one_apply, one_mul, mul_one]
    exact Complex.exp_ne_zero _
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.CuspOf
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Fb in
private theorem setIntegral_haar {E : Type} [Field E] [NumberField E] {a r : ℕ} {φ : GA E a → ℂ}
    (hl : IsLeftInvariant φ) (g : GA E a) (h : constantTerm r φ g = 0) (ν : Measure (UPos a r → Ad E))
    [ν.IsAddHaarMeasure] {D : Set (UPos a r → Ad E)} (hD : IsAddFundamentalDomain (unipLattice E a r) D ν) :
    ∫ x in D, φ (unipGL x * g) ∂ν = 0 := by
  have hD' : IsAddFundamentalDomain (unipLattice E a r) D (unipMeasure E a r) :=
    hD.mono (Measure.absolutelyContinuous_isAddHaarMeasure _ _)
  rw [constantTerm_eq_setIntegral hl hD'] at h
  rw [Measure.isAddLeftInvariant_eq_smul ν (unipMeasure E a r), Measure.restrict_smul, integral_smul_nnreal_measure, h,
    smul_zero]

open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Fb in
private def ixEq (a r : ℕ) : UPos a r ≃ BlockIx a r where
  toFun p := ⟨p.1, p.2.1, p.2.2⟩
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Fb in
private theorem unipGL_ixEq {R : Type} [CommRing R] {a r : ℕ} (x : BlockIx a r → R) :
    unipGL (fun p => x (ixEq a r p)) = unip x := by
  refine Units.ext ?_
  change 1 + blockEntry (fun p => x (ixEq a r p)) = 1 + nilM x
  congr 1

open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Fb in
private theorem cusp_of {E : Type} [Field E] [NumberField E] {a : ℕ} {φ : GA E a → ℂ}
    (hl : IsLeftInvariant φ) (hφ : AutomorphicForm.IsCuspidal φ) : GlobalTheory.CuspRep.IsCuspidal φ := by
  intro r h0 h1 i1 i2 μ 𝓕 hμ hF g
  obtain rfl : i1 = MeasurableSpace.pi :=
    (@BorelSpace.measurable_eq _ _ i1 i2).trans (@BorelSpace.measurable_eq _ _ _ Pi.borelSpace).symm
  let β : (BlockIx a r → Ad E) ≃ₜ+ (UPos a r → Ad E) :=
    { toFun := fun x p => x (ixEq a r p)
      invFun := fun x p => x ((ixEq a r).symm p)
      left_inv := fun x => rfl
      right_inv := fun x => rfl
      map_add' := fun x y => rfl
      continuous_toFun := continuous_pi fun p => continuous_apply _
      continuous_invFun := continuous_pi fun p => continuous_apply _ }
  let e : unipLattice E a r ≃ ratN E a r :=
    { toFun := fun y => ⟨β.symm y, by
        obtain ⟨_, y, rfl⟩ := y
        exact ⟨fun p => y ((ixEq a r).symm p), rfl⟩⟩
      invFun := fun x => ⟨β x, by
        obtain ⟨_, y, rfl⟩ := x
        exact ⟨fun p => y (ixEq a r p), rfl⟩⟩
      left_inv := fun y => Subtype.ext (β.apply_symm_apply y)
      right_inv := fun x => Subtype.ext (β.symm_apply_apply x) }
  let m := β.toHomeomorph.toMeasurableEquiv
  haveI : (μ.map m).IsAddHaarMeasure := β.isAddHaarMeasure_map μ
  have h2 := setIntegral_haar hl g (hφ r h0 h1 g) (μ.map m) (D := m '' 𝓕)
    (hF.image_of_equiv m.toEquiv (MeasurePreserving.symm m ⟨m.measurable, rfl⟩).quasiMeasurePreserving e fun y x => by
      change β (β.symm y + x) = y + β x
      rw [map_add (f := _), β.apply_symm_apply])
  rw [m.measurableEmbedding.setIntegral_map, m.injective.preimage_image] at h2
  rw [← h2]
  congr 1
  funext x
  exact congrArg (fun u => φ (u * g)) (unipGL_ixEq x).symm

open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.ConvolutionTheory.R2.Pp in
private theorem found_cusp {E : Type} [Field E] [NumberField E] {Φ : GL (Fin 2) (A E) → ℂ}
    (h0 : ∀ h, ∫ b in fundamentalSet E, Φ (gl (nU b) * h) ∂(adeleMeasure E) = 0) :
    AutomorphicForm.IsCuspidal Φ := by
  intro r hr hr2 g
  obtain rfl : r = 1 := by omega
  letI : Unique (UPos 2 1) := ⟨⟨⟨(0, 1), by decide⟩⟩, by decide⟩
  rw [← h0 g, ← int_one (ι := UPos 2 1)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  have : gl (nU (x default)) = unipGL x := by
    refine Units.ext ?_
    change (nU (x default)).1 = unipMatrix x
    ext i j
    fin_cases i <;> fin_cases j <;> simp [nU, unipMatrix, blockEntry_apply]
    rfl
  simp only [this]

theorem UpperTheory.ConvolutionTheory.R2.G.cuspOf :
    ∀ (E : Type) [Field E] [NumberField E] (Φ : GL (Fin 2) (A E) → ℂ), (∀ γ h, Φ (ratGL E 2 γ * h) = Φ h) →
    (∀ h, ∫ b in fundamentalSet E, Φ (gl (nU b) * h) ∂(adeleMeasure E) = 0) → GlobalTheory.CuspRep.IsCuspidal Φ := by
  intro E _ _ Φ hl h0
  exact cusp_of hl (found_cusp h0)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ZetaFin
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

private theorem adelicWeightFour_eq_product {F : Type} [Field F] [NumberField F] (L : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (N : ℕ) (x y z : A F) :
    wt4 L N ![0, x, y, z] = GlobalTheory.CompanionTheory.EpConvB.adeleWeight L N x * (GlobalTheory.CompanionTheory.EpConvB.adeleWeight L N y * GlobalTheory.CompanionTheory.EpConvB.adeleWeight L N z) := by
  simp [wt4, Fin.prod_univ_four, GlobalTheory.CompanionTheory.EpConvB.adeleWeight_zero, mul_assoc]

private theorem tsum_pi_fin_two_product {F : Type} (f : F → ℝ≥0∞) :
    ∑' ξ : Fin 2 → F, f (ξ 0) * f (ξ 1) = (∑' x, f x) * ∑' x, f x := by
  rw [← (finTwoArrowEquiv F).symm.tsum_eq, ENNReal.tsum_prod' ]
  simp only [finTwoArrowEquiv_symm_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  simp_rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]

private theorem real_bound {w b T c : ℝ} (hw : 0 ≤ w) (hb : 0 < b) (hT0 : 0 ≤ T) (hT : T ≤ c * (1 + b)) :
    b ^ 2 * (w * (T * T)) ≤ 2 * c ^ 2 * (w * b ^ 2 + w * b ^ 4) := by
  have h1 : T * T ≤ (c * (1 + b)) * (c * (1 + b)) := mul_le_mul hT hT hT0 (hT0.trans hT)
  have h2 : (c * (1 + b)) * (c * (1 + b)) ≤ 2 * c ^ 2 * (1 + b ^ 2) := by
    nlinarith [mul_nonneg (sq_nonneg c) (sq_nonneg (1 - b))]
  have h3 : b ^ 2 * w ≥ 0 := by positivity
  calc b ^ 2 * (w * (T * T)) = (b ^ 2 * w) * (T * T) := by ring
    _ ≤ (b ^ 2 * w) * (2 * c ^ 2 * (1 + b ^ 2)) := mul_le_mul_of_nonneg_left (h1.trans h2) h3
    _ = _ := by ring

theorem UpperTheory.ConvolutionTheory.R2.G.zetaFin :
    ∀ (F : Type) [Field F] [NumberField F], ∃ N : ℕ, ∀ L : (FractionalIdeal (𝓞 F)⁰ F)ˣ, ∫⁻ a : IdeleGroup F, M.wt a * ∑' ξ : Fin 2 → F,
    ENNReal.ofReal (wt4 L N ![0, ((a⁻¹ : (A F)ˣ) : A F), (a : A F) * rt (ξ 0), (a : A F) * rt (ξ 1)]) ∂(ideleMeasure F) ≠ ⊤ := by
  intro F _ _
  obtain ⟨A2, h2⟩ := GlobalTheory.CompanionTheory.EpConvB.integrable_weight (K := F) (σ := 2) (by norm_num)
  obtain ⟨A4, h4⟩ := GlobalTheory.CompanionTheory.EpConvB.integrable_weight (K := F) (σ := 4) (by norm_num)
  refine ⟨max (max A2 A4) (Module.finrank ℚ F + 1), fun L => ?_⟩
  set N := max (max A2 A4) (Module.finrank ℚ F + 1) with hN
  have hfr : Module.finrank ℚ F < N := lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
  obtain ⟨c, hc0, hc⟩ := GlobalTheory.CompanionTheory.EpConvB.theta_bound L hfr
  have I2 := h2 L N ((le_max_left _ _).trans (le_max_left _ _))
  have I4 := h4 L N ((le_max_right _ _).trans (le_max_left _ _))
  let w : IdeleGroup F → ℝ := fun b => GlobalTheory.CompanionTheory.EpConvB.adeleWeight L N (b : A F)
  let G : IdeleGroup F → ℝ := fun b => 2 * c ^ 2 * (w b * UpperTheory.ConvolutionTheory.R2.ab b ^ 2 + w b * UpperTheory.ConvolutionTheory.R2.ab b ^ 4)
  have hG : Integrable G (ideleMeasure F) := by
    have e2 : (fun t : IdeleGroup F => w t * UpperTheory.ConvolutionTheory.R2.ab t ^ 2) = fun t : IdeleGroup F =>
        GlobalTheory.CompanionTheory.EpConvB.adeleWeight L N (t : A F) * ((IdeleGroup.ideleModule F t : ℝ)) ^ (2 : ℝ) := by
      funext t
      simp only [w, UpperTheory.ConvolutionTheory.R2.ab]
      rw [← Real.rpow_natCast]
      norm_num
    have e4 : (fun t : IdeleGroup F => w t * UpperTheory.ConvolutionTheory.R2.ab t ^ 4) = fun t : IdeleGroup F =>
        GlobalTheory.CompanionTheory.EpConvB.adeleWeight L N (t : A F) * ((IdeleGroup.ideleModule F t : ℝ)) ^ (4 : ℝ) := by
      funext t
      simp only [w, UpperTheory.ConvolutionTheory.R2.ab]
      rw [← Real.rpow_natCast]
      norm_num
    have J2 : Integrable (fun t : IdeleGroup F => w t * UpperTheory.ConvolutionTheory.R2.ab t ^ 2) (ideleMeasure F) := e2 ▸ I2
    have J4 : Integrable (fun t : IdeleGroup F => w t * UpperTheory.ConvolutionTheory.R2.ab t ^ 4) (ideleMeasure F) := e4 ▸ I4
    exact (J2.add J4).const_mul (2 * c ^ 2)
  have key : ∀ a : IdeleGroup F, M.wt a * ∑' ξ : Fin 2 → F,
      ENNReal.ofReal (wt4 L N ![0, ((a⁻¹ : (A F)ˣ) : A F), (a : A F) * rt (ξ 0), (a : A F) * rt (ξ 1)]) ≤ ENNReal.ofReal (G a⁻¹) := by
    intro a
    obtain ⟨hs, hb⟩ := hc a
    have hf0 : ∀ x : F, 0 ≤ GlobalTheory.CompanionTheory.EpConvB.adeleWeight L N ((a : A F) * rt x) :=
      fun x => GlobalTheory.CompanionTheory.EpConvB.adeleWeight_nonneg _ _ _
    set T : ℝ := ∑' x : F, GlobalTheory.CompanionTheory.EpConvB.adeleWeight L N ((a : A F) * rt x) with hTdef
    have hT0 : 0 ≤ T := tsum_nonneg hf0
    have hw0 : 0 ≤ w a⁻¹ := GlobalTheory.CompanionTheory.EpConvB.adeleWeight_nonneg _ _ _
    have e : ∑' ξ : Fin 2 → F,
        ENNReal.ofReal (wt4 L N ![0, ((a⁻¹ : (A F)ˣ) : A F), (a : A F) * rt (ξ 0), (a : A F) * rt (ξ 1)]) =
        ENNReal.ofReal (w a⁻¹ * (T * T)) := by
      have e1 : ∀ ξ : Fin 2 → F,
          ENNReal.ofReal (wt4 L N ![0, ((a⁻¹ : (A F)ˣ) : A F), (a : A F) * rt (ξ 0), (a : A F) * rt (ξ 1)]) =
          ENNReal.ofReal (w a⁻¹) * ((fun x : F => ENNReal.ofReal (GlobalTheory.CompanionTheory.EpConvB.adeleWeight L N ((a : A F) * rt x))) (ξ 0) *
            (fun x : F => ENNReal.ofReal (GlobalTheory.CompanionTheory.EpConvB.adeleWeight L N ((a : A F) * rt x))) (ξ 1)) := by
        intro ξ
        rw [adelicWeightFour_eq_product, ENNReal.ofReal_mul hw0, ENNReal.ofReal_mul (hf0 _)]
      have t2 := tsum_pi_fin_two_product (fun x : F => ENNReal.ofReal (GlobalTheory.CompanionTheory.EpConvB.adeleWeight L N ((a : A F) * rt x)))
      beta_reduce at t2
      simp_rw [e1]
      rw [ENNReal.tsum_mul_left, t2, ← ENNReal.ofReal_tsum_of_nonneg hf0 hs,
        ENNReal.ofReal_mul hw0, ENNReal.ofReal_mul hT0]
    have hbpos : 0 < (UpperTheory.ConvolutionTheory.R2.ab a)⁻¹ := inv_pos.mpr (M.ab_pos a)
    have hr := real_bound hw0 hbpos hT0 hb
    rw [e, M.wt, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    simpa only [G, M.ab_inv] using hr
  haveI : (ideleMeasure F).IsInvInvariant := Measure.IsHaarMeasure.isInvInvariant_of_regular _
  have h3 : ∫⁻ a : IdeleGroup F, ENNReal.ofReal (G a⁻¹) ∂(ideleMeasure F) = ∫⁻ b : IdeleGroup F, ENNReal.ofReal (G b) ∂(ideleMeasure F) :=
    lintegral_inv_eq_self (fun b => ENNReal.ofReal (G b))
  exact ne_top_of_le_ne_top (h3 ▸ hG.lintegral_lt_top.ne) (lintegral_mono key)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.HatLin
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

namespace UpperTheory.ConvolutionTheory.R2.G

variable {F : Type} [Field F] [NumberField F]

private def eQ : Fin 3 ⊕ Unit ≃ Fin 4 where
  toFun := Sum.elim ![0, 2, 3] fun _ => 1
  invFun := ![.inl 0, .inr (), .inl 1, .inl 2]
  left_inv := by
    rintro (i | ⟨⟩)
    · fin_cases i <;> rfl
    · rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

private theorem reindex_mem {φ : V4 F → ℂ} (hφ : φ ∈ schwartzBruhatPi (K := F) (ι := Fin 4)) :
    (fun z : Fin 3 ⊕ Unit → A F => φ fun i => z (eQ.symm i)) ∈ schwartzBruhatPi (K := F) (ι := Fin 3 ⊕ Unit) := by
  let M : Matrix (Fin 4) (Fin 3 ⊕ Unit) F := (1 : Matrix (Fin 4) (Fin 4) F).submatrix id eQ
  let N : Matrix (Fin 3 ⊕ Unit) (Fin 4) F := (1 : Matrix (Fin 4) (Fin 4) F).submatrix eQ id
  have hNM : N * M = 1 := by
    have h := Matrix.submatrix_mul (1 : Matrix (Fin 4) (Fin 4) F) (1 : Matrix (Fin 4) (Fin 4) F)
      eQ id eQ Function.bijective_id
    rw [Matrix.mul_one, Matrix.submatrix_one_equiv] at h
    exact h.symm
  have hMN : M * N = 1 := by
    have h := Matrix.submatrix_mul (1 : Matrix (Fin 4) (Fin 4) F) (1 : Matrix (Fin 4) (Fin 4) F)
      id eQ id eQ.bijective
    rw [Matrix.mul_one, Matrix.submatrix_id_id] at h
    exact h.symm
  have h := GroundTheory.Heights₂.Theta.comp_mulVec_mem_schwartzBruhatPi M N hNM hMN hφ
  have hx : ∀ x : Fin 3 ⊕ Unit → A F, (M.map (algebraMap F (A F)) *ᵥ x) = fun i => x (eQ.symm i) := by
    intro x
    funext i
    have hM : ∀ j k, M j k = if j = eQ k then (1 : F) else 0 := fun j k => by
      change (1 : Matrix (Fin 4) (Fin 4) F) j (eQ k) = _
      exact Matrix.one_apply
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, hM]
    rw [Finset.sum_eq_single (eQ.symm i)]
    · simp
    · intro b _ hb
      have : i ≠ eQ b := fun h => hb (by simp [h])
      simp [this]
    · simp
  simpa only [hx] using h

private theorem integrable_slice (φ : S4 F) (v : V4 F) :
    Integrable (fun s : A F => φ.1 (Function.update v 1 s)) (adeleMeasure F) := by
  have h := GroundTheory.Heights₂.Theta.integrable_partialFourierPi_slice (reindex_mem φ.2)
    (fun i : Fin 3 => v (eQ (.inl i)))
  have hmp := measurePreserving_funUnique (adeleMeasure F) Unit
  refine (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).1 ?_
  refine h.congr (Eventually.of_forall fun y => ?_)
  have : (fun i => (Sum.elim (fun i : Fin 3 => v (eQ (.inl i))) y : Fin 3 ⊕ Unit → A F) (eQ.symm i)) =
      Function.update v 1 (MeasurableEquiv.funUnique Unit (A F) y) := by
    funext i
    fin_cases i <;> simp [eQ]
  simp only [Function.comp]
  rw [this]

private theorem integrable_term (φ : S4 F) (v : V4 F) :
    Integrable (fun s : A F => φ.1 (Function.update v 1 s) * ψ (-(s * v 1))) (adeleMeasure F) := by
  have hs := integrable_slice φ v
  have hc : Continuous fun s : A F => ψ (-(s * v 1)) :=
    continuous_subtype_val.comp ((continuous_adelicChar (K := F)).comp
      (continuous_id.mul continuous_const).neg)
  exact hs.mono (hs.1.mul hc.aestronglyMeasurable)
    (Eventually.of_forall fun s => by rw [norm_mul, ψ, Circle.norm_coe, mul_one])

end UpperTheory.ConvolutionTheory.R2.G

theorem UpperTheory.ConvolutionTheory.R2.G.hatLin :
    ∀ (F : Type) [Field F] [NumberField F], ∃ H : S4 F →ₗ[ℂ] S4 F, ∀ φ, (H φ).1 = hat φ.1 := by
  intro F _ _
  have hadd : ∀ φ χ : S4 F, hat (φ + χ).1 = hat φ.1 + hat χ.1 := by
    intro φ χ
    funext v
    simp only [hat, Submodule.coe_add, Pi.add_apply, add_mul]
    exact integral_add (integrable_term φ v) (integrable_term χ v)
  have hsmul : ∀ (c : ℂ) (φ : S4 F), hat (c • φ).1 = c • hat φ.1 := by
    intro c φ
    funext v
    simp only [hat, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact integral_const_mul c _
  refine ⟨{ toFun := fun φ => ⟨hat φ.1, (UpperTheory.ConvolutionTheory.R2.D.hatMem F φ).1⟩
            map_add' := fun φ χ => Subtype.ext (hadd φ χ)
            map_smul' := fun c φ => Subtype.ext (hsmul c φ) }, fun φ => rfl⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ProdExt
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

theorem UpperTheory.ConvolutionTheory.R2.G.prodExt :
    ∀ (Ω X Z : Type) [MeasurableSpace Ω] [MeasurableSpace X] [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    [SecondCountableTopology Z] [T2Space Z] (ν : Measure Ω) (r : Ω → X) (s : Ω → Z) (ρ : Ω → ℂ),
    TopologicalSpace.IsTopologicalBasis {T : Set Z | IsCompact T ∧ IsOpen T} → Measurable r → Measurable s → Integrable ρ ν →
    (∀ (S : Set X) (T : Set Z), MeasurableSet S → IsCompact T → IsOpen T → ∫ ω, S.indicator 1 (r ω) * (T.indicator 1 (s ω) * ρ ω) ∂ν = 0) →
    ∀ Q : X × Z → ℂ, Measurable Q → (∀ x, ‖Q x‖ ≤ 1) → ∫ ω, Q (r ω, s ω) * ρ ω ∂ν = 0 := by
  intro Ω X Z _ _ _ _ _ _ _ ν r s ρ hB hr hs hρ H Q hQ hQ1
  have hφ : Measurable (fun ω => (r ω, s ω)) := hr.prodMk hs

  obtain ⟨e, he, heU⟩ : ∃ e : ℕ → Set Z, (∀ n, IsCompact (e n) ∧ IsOpen (e n)) ∧ ⋃ n, e n = Set.univ := by
    obtain ⟨T, hTc, hTs, hTU⟩ := TopologicalSpace.isOpen_sUnion_countable
      {T : Set Z | IsCompact T ∧ IsOpen T} (fun t ht => ht.2)
    have hne : (insert ∅ T).Nonempty := Set.insert_nonempty _ _
    obtain ⟨e, he⟩ := (hTc.insert ∅).exists_eq_range hne
    refine ⟨e, fun n => ?_, ?_⟩
    · have hn : e n ∈ insert ∅ T := he ▸ Set.mem_range_self n
      rcases hn with hn | hn
      · rw [hn]; exact ⟨isCompact_empty, isOpen_empty⟩
      · exact hTs hn
    · rw [← Set.sUnion_range, ← he, Set.sUnion_insert, Set.empty_union, hTU, hB.sUnion_eq]

  have hmass : ∫ ω, ρ ω ∂ν = 0 := by
    have hF : ∀ n, ∫ ω, (Set.accumulate e n).indicator (1 : Z → ℂ) (s ω) * ρ ω ∂ν = 0 := by
      intro n
      have hc : IsCompact (Set.accumulate e n) := isCompact_accumulate (fun i => (he i).1) n
      have ho : IsOpen (Set.accumulate e n) := by
        rw [Set.accumulate_def]
        exact isOpen_iUnion (fun i => isOpen_iUnion (fun _ => (he i).2))
      have := H Set.univ (Set.accumulate e n) MeasurableSet.univ hc ho
      simpa using this
    have hlim : Tendsto (fun n => ∫ ω, (Set.accumulate e n).indicator (1 : Z → ℂ) (s ω) * ρ ω ∂ν)
        atTop (𝓝 (∫ ω, ρ ω ∂ν)) := by
      refine tendsto_integral_of_dominated_convergence (fun ω => ‖ρ ω‖) ?_ hρ.norm ?_ ?_
      · intro n
        have hm : MeasurableSet (Set.accumulate e n) :=
          (isCompact_accumulate (fun i => (he i).1) n).isClosed.measurableSet
        exact (((measurable_one.indicator hm).comp hs).aestronglyMeasurable).mul hρ.1
      · intro n
        refine Eventually.of_forall (fun ω => ?_)
        by_cases h : s ω ∈ Set.accumulate e n <;> simp [h]
      · refine Eventually.of_forall (fun ω => ?_)
        have hmem : s ω ∈ ⋃ n, e n := heU ▸ Set.mem_univ _
        obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hmem
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop n] with m hm
        have : s ω ∈ Set.accumulate e m := Set.mem_accumulate.2 ⟨n, hm, hn⟩
        simp [this]
    have := tendsto_nhds_unique hlim (by simp only [hF]; exact tendsto_const_nhds)
    exact this

  have hgen : (inferInstance : MeasurableSpace (X × Z)) =
      MeasurableSpace.generateFrom (Set.image2 (· ×ˢ ·) {S : Set X | MeasurableSet S}
        {T : Set Z | IsCompact T ∧ IsOpen T}) := by
    have hD : IsCountablySpanning {T : Set Z | IsCompact T ∧ IsOpen T} := ⟨e, he, heU⟩
    have h1 : ‹MeasurableSpace Z› = MeasurableSpace.generateFrom {T : Set Z | IsCompact T ∧ IsOpen T} :=
      (BorelSpace.measurable_eq).trans hB.borel_eq_generateFrom
    have := generateFrom_prod_eq (isCountablySpanning_measurableSet (α := X)) hD
    rw [MeasurableSpace.generateFrom_measurableSet, ← h1] at this
    exact this
  have hpi : IsPiSystem (Set.image2 (· ×ˢ ·) {S : Set X | MeasurableSet S}
      {T : Set Z | IsCompact T ∧ IsOpen T}) :=
    MeasurableSpace.isPiSystem_measurableSet.prod
      (fun a ha b hb _ => ⟨ha.1.inter hb.1, ha.2.inter hb.2⟩)
  have hset : ∀ A : Set (X × Z), MeasurableSet A → ∫ ω in (fun ω => (r ω, s ω)) ⁻¹' A, ρ ω ∂ν = 0 := by
    intro A hA
    induction A, hA using MeasurableSpace.induction_on_inter hgen hpi with
    | empty => simp
    | basic t ht =>
      obtain ⟨S, hS, T, hT, rfl⟩ := ht
      have hTm : MeasurableSet T := hT.2.measurableSet
      have hm : MeasurableSet ((fun ω => (r ω, s ω)) ⁻¹' (S ×ˢ T)) := hφ (hS.prod hTm)
      rw [← integral_indicator hm, ← H S T hS hT.1 hT.2]
      congr 1
      funext ω
      by_cases h1 : r ω ∈ S <;> by_cases h2 : s ω ∈ T <;> simp [Set.indicator, h1, h2]
    | compl t htm ih =>
      rw [Set.preimage_compl, setIntegral_compl (hφ htm) hρ, ih, hmass, sub_zero]
    | iUnion f hd hm ih =>
      rw [Set.preimage_iUnion, integral_iUnion (fun i => hφ (hm i))
        (fun i j hij => (hd hij).preimage _) hρ.integrableOn]
      simp [ih]

  have hint : ∀ (f : Ω → ℂ) (C : ℝ), Measurable f → (∀ ω, ‖f ω‖ ≤ C) →
      Integrable (fun ω => f ω * ρ ω) ν := fun f C hf hC =>
    hρ.bdd_mul hf.aestronglyMeasurable (Eventually.of_forall hC)
  have hsimple : ∀ g : SimpleFunc (X × Z) ℂ, ∫ ω, g (r ω, s ω) * ρ ω ∂ν = 0 := by
    intro g
    induction g using SimpleFunc.induction with
    | const c hA =>
      rename_i A
      have hm : MeasurableSet ((fun ω => (r ω, s ω)) ⁻¹' A) := hφ hA
      have h0 := hset A hA
      rw [← integral_indicator hm] at h0
      have : (fun ω => (SimpleFunc.piecewise A hA (SimpleFunc.const _ c) (SimpleFunc.const _ 0)) (r ω, s ω) * ρ ω)
          = fun ω => c * ((fun ω => (r ω, s ω)) ⁻¹' A).indicator ρ ω := by
        funext ω
        by_cases h : (r ω, s ω) ∈ A <;> simp [Set.indicator, h, Set.piecewise]
      rw [this, integral_const_mul, h0, mul_zero]
    | add hd hf hg =>
      rename_i f g
      obtain ⟨Cf, hCf⟩ := f.exists_forall_norm_le
      obtain ⟨Cg, hCg⟩ := g.exists_forall_norm_le
      have hif := hint (fun ω => f (r ω, s ω)) Cf (f.measurable.comp hφ) (fun ω => hCf _)
      have hig := hint (fun ω => g (r ω, s ω)) Cg (g.measurable.comp hφ) (fun ω => hCg _)
      simp only [SimpleFunc.coe_add, Pi.add_apply, add_mul]
      rw [integral_add hif hig, hf, hg, add_zero]

  have hSM : StronglyMeasurable Q := hQ.stronglyMeasurable
  have hlim : Tendsto (fun n => ∫ ω, hSM.approxBounded 1 n (r ω, s ω) * ρ ω ∂ν) atTop
      (𝓝 (∫ ω, Q (r ω, s ω) * ρ ω ∂ν)) := by
    refine tendsto_integral_of_dominated_convergence (fun ω => ‖ρ ω‖) ?_ hρ.norm ?_ ?_
    · intro n
      exact (((hSM.approxBounded 1 n).measurable.comp hφ).aestronglyMeasurable).mul hρ.1
    · intro n
      refine Eventually.of_forall (fun ω => ?_)
      rw [norm_mul]
      have := hSM.norm_approxBounded_le zero_le_one n (r ω, s ω)
      calc _ ≤ 1 * ‖ρ ω‖ := by gcongr
        _ = ‖ρ ω‖ := one_mul _
    · refine Eventually.of_forall (fun ω => ?_)
      exact (hSM.tendsto_approxBounded_of_norm_le (hQ1 _)).mul_const _
  exact tendsto_nhds_unique hlim (by simp only [hsimple]; exact tendsto_const_nhds)
end
