module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.UnfL
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsTer

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Iwa
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.iwa :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], ∀ g : G1 F, ∃ (b : A F) (a : (A F)ˣ), ∃ k ∈ KK F, g = nU b * mD a * k := by
  intro F _ _ _ g
  obtain ⟨b, hb, k, hk, e⟩ := Reduction.exists_adelicBorel_mul_maxCompact (K := F) (n := 2) (gl g)
  obtain ⟨x, a, k', hk', hg, -, -⟩ := UpperTheory.ConvolutionTheory.R2.M.fromGL F g b hb k hk e
  exact ⟨x, a, k', hk', hg⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Unimod
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.unimod :
    ∀ (F : Type) [Field F] [NumberField F], ∀ (μ : Measure (G1 F)) [μ.IsHaarMeasure], μ.IsMulRightInvariant := by
  intro F _ _ μ _
  have h0 : ∀ g : G1 F, (Measure.modularCharacter g : ℝ≥0) ≠ 0 := fun g h => by
    have e := map_mul (Measure.modularCharacter (G := G1 F)) g g⁻¹
    rw [mul_inv_cancel, map_one, h, zero_mul] at e
    exact one_ne_zero e
  have h2F : (2 : F) ≠ 0 := two_ne_zero
  have h3F : (3 : F) ≠ 0 := by norm_num
  let two : (A F)ˣ := Units.map (algebraMap F (A F)).toMonoidHom (Units.mk0 2 h2F)
  have h2 : (two : A F) = 2 := map_ofNat (algebraMap F (A F)) 2
  have h4 : ∀ b : A F, (Measure.modularCharacter (nU (4 * b)) : ℝ≥0) = Measure.modularCharacter (nU b) := by
    intro b
    have e := congrArg (Measure.modularCharacter (G := G1 F)) (M.mD_mul_nU two b)
    rw [map_mul, map_mul, mul_comm] at e
    have c := mul_right_cancel₀ (h0 _) e
    rw [h2] at c
    norm_num at c
    exact c.symm
  have hn : ∀ c : A F, (Measure.modularCharacter (nU c) : ℝ≥0) = 1 := by
    intro c
    have h3 : (3 : A F) * (rt (3⁻¹ : F) * c) = c := by
      have : (3 : A F) * rt (3⁻¹ : F) = 1 := by
        rw [show (3 : A F) = rt (3 : F) from (map_ofNat (algebraMap F (A F)) 3).symm, ← map_mul, mul_inv_cancel₀ h3F, map_one]
      rw [← mul_assoc, this, one_mul]
    set b : A F := rt (3⁻¹ : F) * c with hb
    have e := h4 b
    rw [show (4 : A F) * b = 3 * b + b by ring, M.nU_add, map_mul, h3] at e
    exact mul_right_cancel₀ (h0 (nU b)) (e.trans (one_mul _).symm)
  have hw : (Measure.modularCharacter (wW F) : ℝ≥0) = 1 := by
    have e : wW F * wW F * (wW F * wW F) = 1 := by
      refine Subtype.ext ?_
      rw [M.val_mul, M.val_mul]
      ext i j; fin_cases i <;> fin_cases j <;> simp [wW, Matrix.mul_apply, Fin.sum_univ_two]
    have e' := congrArg (Measure.modularCharacter (G := G1 F)) e
    rw [map_mul, map_mul, map_one] at e'
    have e4 : (Measure.modularCharacter (wW F) : ℝ≥0) ^ 4 = 1 := by rw [← e']; ring
    exact (pow_eq_one_iff.1 e4).resolve_right (by norm_num)
  have hall : ∀ g : G1 F, (Measure.modularCharacter g : ℝ≥0) = 1 := by
    intro g
    have hg : g ∈ Subgroup.closure (Set.range (nU (F := F)) ∪ {wW F}) := by
      rw [(gen F).1]; exact Subgroup.mem_top g
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with ⟨c, rfl⟩ | hx
      · exact hn c
      · rw [Set.mem_singleton_iff.1 hx]; exact hw
    | one => exact map_one _
    | mul x y _ _ hx hy => rw [map_mul, hx, hy, one_mul]
    | inv x _ hx =>
      have e := map_mul (Measure.modularCharacter (G := G1 F)) x x⁻¹
      rw [mul_inv_cancel, map_one, hx, one_mul] at e
      exact e.symm
  haveI : μ.InnerRegular := inferInstance
  refine ⟨fun g => ?_⟩
  rw [Measure.map_right_mul_eq_modularCharacterFun_smul μ g,
    show Measure.modularCharacterFun g = 1 from hall g, one_smul]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.MeasMul
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

private theorem absUnf {G P B ι : Type} [MeasurableSpace G] [MeasurableSpace P] [MeasurableSpace B] [Countable ι]
    (m₀ : Measure G) (e : ι → G → G) (he : ∀ i, Measurable (e i)) (ρ : Measure P) [SFinite ρ]
    (β : Measure B) [SFinite β] (s : P × B → G) (hs : Measurable s) (u : G → ℂ) (hu : Measurable u)
    (hL : ∀ φ : ℂ → ℝ≥0∞, Measurable φ →
      ∫⁻ x, ∑' i, φ (u (e i x)) ∂m₀ = ∫⁻ q, φ (u (s q)) ∂(ρ.prod β))
    (hfin : ∫⁻ q, ‖u (s q)‖ₑ ∂(ρ.prod β) ≠ ⊤) :
    (∀ᵐ x ∂m₀, Summable fun i => ‖u (e i x)‖) ∧ Integrable (fun x => ∑' i, u (e i x)) m₀ ∧
      Integrable (fun p => ∫ b, u (s (p, b)) ∂β) ρ ∧
      ∫ x, ∑' i, u (e i x) ∂m₀ = ∫ p, ∫ b, u (s (p, b)) ∂β ∂ρ := by
  have hS := M.sumSide G ι m₀ e he
  have hv : Measurable fun q => u (s q) := hu.comp hs
  have hvi : Integrable (fun q => u (s q)) (ρ.prod β) :=
    ⟨hv.aestronglyMeasurable, lt_top_iff_ne_top.2 hfin⟩
  have hT := M.transfer (m := Measure.sum fun i => m₀.map (e i)) (n := ρ.prod β) hu hv
    (fun φ hφ => (hS.1 _ (hφ.comp hu)).trans (hL φ hφ))
  obtain ⟨h1, h2, h3⟩ := hS.2 u hu (hT.1.2 hvi)
  refine ⟨h1, h2, hvi.integral_prod_left, h3.trans (hT.2.trans ?_)⟩
  exact integral_prod _ hvi

private theorem meas_mul (F : Type) [Field F] [NumberField F] : Measurable fun q : G1 F × G1 F => q.1 * q.2 :=
  (continuous_fst.mul continuous_snd).measurable

private theorem meas_nU (F : Type) [Field F] [NumberField F] : Measurable (nU : A F → G1 F) :=
  M.continuous_nU.measurable

private theorem meas_mD (F : Type) [Field F] [NumberField F] : Measurable (mD : IdeleGroup F → G1 F) :=
  M.continuous_mD.measurable

private theorem measMul {G X : Type} [Mul G] [MeasurableSpace G] [MeasurableSpace X] {a b : X → G}
    (hm : Measurable fun q : G × G => q.1 * q.2) (ha : Measurable a) (hb : Measurable b) :
    Measurable fun x => a x * b x := hm.comp (ha.prodMk hb)

private theorem meas_g (F : Type) [Field F] [NumberField F] :
    Measurable fun q : G1 F × A F => nU q.2 * q.1 :=
  measMul (a := fun q : G1 F × A F => nU q.2) (b := fun q => q.1) (meas_mul F)
    ((meas_nU F).comp measurable_snd) measurable_fst

private theorem meas_m (F : Type) [Field F] [NumberField F] :
    Measurable fun p : IdeleGroup F × G1 F => mD p.1 * p.2 :=
  measMul (a := fun p : IdeleGroup F × G1 F => mD p.1) (b := fun p => p.2) (meas_mul F)
    ((meas_mD F).comp measurable_fst) measurable_snd

private theorem meas_q (F : Type) [Field F] [NumberField F] :
    Measurable fun q : (IdeleGroup F × G1 F) × A F => nU q.2 * (mD q.1.1 * q.1.2) :=
  measMul (a := fun q : (IdeleGroup F × G1 F) × A F => nU q.2)
    (b := fun q => mD q.1.1 * q.1.2) (meas_mul F)
    ((meas_nU F).comp measurable_snd) ((meas_m F).comp measurable_fst)

private theorem meas_l (F : Type) [Field F] [NumberField F] (x : G1 F) :
    Measurable fun g : G1 F => x * g :=
  measMul (a := fun _ : G1 F => x) (b := fun g => g) (meas_mul F) measurable_const measurable_id

private theorem key (F : Type) [Field F] [NumberField F] (M₀ : Meas F) (ρ : Measure (IdeleGroup F × G1 F)) [SFinite ρ]
    (hρ : ∀ u : G1 F → ℝ≥0∞, Measurable u → ∫⁻ p, u (mD p.1 * p.2) ∂ρ = M.J0 M₀ u)
    (w : G1 F → ℝ≥0∞) (hw : Measurable w) :
    ∫⁻ q, w (nU q.2 * (mD q.1.1 * q.1.2)) ∂(ρ.prod ((adeleMeasure F).restrict (fundamentalSet F))) =
      M.J0 M₀ fun g => ∫⁻ b in fundamentalSet F, w (nU b * g) ∂(adeleMeasure F) := by
  refine (lintegral_prod (fun q : (IdeleGroup F × G1 F) × A F => w (nU q.2 * (mD q.1.1 * q.1.2)))
    (hw.comp (meas_q F)).aemeasurable).trans ?_
  exact hρ _ (Measurable.lintegral_prod_right' (f := fun q : G1 F × A F => w (nU q.2 * q.1)) (hw.comp (meas_g F)))

theorem UpperTheory.ConvolutionTheory.R2.M.unfC :
    ∀ (F : Type) [Field F] [NumberField F] (M₀ : Meas F) (σ) (u : G1 F → ℂ), M.RowSec (F := F) σ → Measurable u → (∀ (ξ : F) g, u (nU (rt ξ) * g) = u g) → (M.J0 M₀ fun g => ∫⁻ b in fundamentalSet F, ‖u (nU b * g)‖ₑ ∂(adeleMeasure F)) ≠ ⊤ → (∀ᵐ g ∂(M₀.μ.restrict M₀.D), Summable fun r => ‖u (ratS F (σ r) * g)‖) ∧ IntegrableOn (fun g => ∑' r, u (ratS F (σ r) * g)) M₀.D M₀.μ ∧ Integrable (iw fun g => ∫ b in fundamentalSet F, u (nU b * g) ∂(adeleMeasure F)) M₀.ν ∧ ∫ g in M₀.D, ∑' r, u (ratS F (σ r) * g) ∂M₀.μ = M₀.I0 fun g => ∫ b in fundamentalSet F, u (nU b * g) ∂(adeleMeasure F) := by
  intro F _ _ M₀ σ u hσ hu hinv hfin
  haveI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  obtain ⟨ρ, hρs, hρ1, hρ2⟩ := M.iwDens F M₀
  have hk := key F M₀ ρ hρ1
  obtain ⟨h1, h2, h3, h4⟩ := absUnf (M₀.μ.restrict M₀.D) (fun (r : {r : Fin 2 → F // r ≠ 0}) g => ratS F (σ r) * g)
    (fun r => meas_l F _) ρ ((adeleMeasure F).restrict (fundamentalSet F))
    (fun q => nU q.2 * (mD q.1.1 * q.1.2)) (meas_q F) u hu
    (fun φ hφ => (M.unfL F M₀ σ (fun g => φ (u g)) hσ (hφ.comp hu)
        (fun ξ g => by simp only [hinv])).trans (hk _ (hφ.comp hu)).symm)
    (by rw [hk (fun g => ‖u g‖ₑ) hu.enorm]; exact hfin)
  refine ⟨h1, h2, ((hρ2 _).1).1 h3, h4.trans ((hρ2 _).2)⟩
end
