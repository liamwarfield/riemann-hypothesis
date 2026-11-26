module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalVolumeRankOneIsotropic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanVolumeRankOneIsotropic
public import Development.WeilBound.CoreStatements.ThetaDilations.BoundedA

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussianFourierSelfDualAdelic
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussianFourierSelfDualAdelic
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.Core0

section Theta

open GlobalTheory.CompanionTheory.SW.CoefTheta

theorem fourier_coefficient_any : ∀ (F : Type) [Field F] [NumberField F], ∀ [MeasurableSpace (A F)] [BorelSpace (A F)], ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) (gf : Ω → Matrix ι ι (A F)) (gi : Ω → InfinitePlace F → Matrix ι ι ℝ), CountData M B ρ Pr gf gi → ∀ a : ℕ, 0 < a → ∀ β : F, ∀ N : ℕ, 0 < N → (∃ r : 𝓞 F, (r : F) = (N : F) * β) → (∀ y : ι → A F, (∀ i, (a : A F) * y i ∈ Oh F) → (N : A F) * qf (hf F) (Bf B) y ∈ Oh F) → ∀ D : Set (InfinitePlace F → ℝ), IsAddFundamentalDomain (latR ρ N) D volume → ∃ I : ℝ≥0, ∫⁻ ω, ∑' x : {x : ι → F // qf (1 / 2 : F) B x = β}, ‖thTerm B ρ P (gf ω) (gi ω) (indL a) (fun _ => Complex.I) x.1‖ₑ ∂Pr = (I : ℝ≥0∞) ∧ IntegrableOn (fun x : InfinitePlace F → ℝ => (∫ ω, theta B ρ P (gf ω) (gi ω) (indL a) (fun w => (x w : ℂ) + Complex.I) ∂Pr) * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ))) D volume ∧ ∫ x in D, (∫ ω, theta B ρ P (gf ω) (gi ω) (indL a) (fun w => (x w : ℂ) + Complex.I) ∂Pr) * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ)) = ((volume D).toReal : ℂ) * ((I : ℝ) : ℂ) := by
  intro F _ _ _ _ ι _ _ M B ρ P hQ Ω _ Pr gf gi hC a ha β N hN hNβ hint D hD
  haveI : Countable F := countable_field
  obtain ⟨hTR, -, -, -, hρ, -, -⟩ := id hQ
  obtain ⟨hprob, -, -, hOrth, -⟩ := id hC
  obtain ⟨-, -, hT2, hOc, hOo, -, hmem, -, -, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  obtain ⟨-, -, -, hfd⟩ := GlobalTheory.T.lattice_fundamental_domain_volume F hTR ρ hρ N hN
  obtain ⟨hvol, horth⟩ := hfd D hD
  have hsb : SB (indL a : (ι → A F) → ℂ) := sb_indL hT2 hOc hOo ha
  obtain ⟨C, hCb⟩ := GlobalTheory.T.weighted_theta_average_le_of_countData F ι M B ρ P hQ Ω Pr gf gi hC (indL a) hsb 1 1 one_pos one_pos
  obtain ⟨hmeas, hbound⟩ := hCb (fun _ => Complex.I) (by simp) (by simp)
  set s : (ι → F) → Ω → ℂ :=
    fun z ω => thTerm B ρ P (gf ω) (gi ω) (indL a) (fun _ => Complex.I) z with hs
  have hm : ∀ z, Measurable (s z) := hmeas
  have hwt : wt M (fun _ : InfinitePlace F => Complex.I) = 1 := by simp [wt]
  have hnz : ∫⁻ ω, ∑' x : {x : ι → F // x ≠ 0}, ‖s x.1 ω‖ₑ ∂Pr ≠ ∞ := by
    rw [hwt, ENNReal.ofReal_one, one_mul] at hbound
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound
  have hfin : ∫⁻ ω, ∑' z, ‖s z ω‖ₑ ∂Pr ≠ ∞ := by
    have hle : ∀ ω, ∑' z, ‖s z ω‖ₑ ≤ 1 + ∑' x : {x : ι → F // x ≠ 0}, ‖s x.1 ω‖ₑ := by
      intro ω
      rw [ENNReal.tsum_eq_add_tsum_ite 0]
      refine add_le_add (thTerm_zero_le B ρ P (gf ω) (gi ω) a) (le_of_eq ?_)
      have := tsum_subtype {x : ι → F | x ≠ 0} (fun z => ‖s z ω‖ₑ)
      refine Eq.trans ?_ this.symm
      refine tsum_congr fun z => ?_
      by_cases h : z = 0 <;> simp [h]
    refine ne_top_of_le_ne_top ?_ (lintegral_mono hle)
    rw [lintegral_add_left measurable_const]
    simp only [lintegral_const, measure_univ, mul_one]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, hnz⟩
  have hpos : ∀ z ω, s z ω = ((‖s z ω‖ : ℝ) : ℂ) := fun z ω => thTerm_nonneg B ρ P (gf ω) (gi ω) a z
  set Sel : Set (ι → F) := {z | qf (1 / 2 : F) B z = β} with hSel
  haveI : IsFiniteMeasure ((volume : Measure (InfinitePlace F → ℝ)).restrict D) :=
    ⟨by rw [Measure.restrict_apply_univ, hvol]; exact ENNReal.ofReal_lt_top⟩
  have hv : Continuous fun x : InfinitePlace F → ℝ =>
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ)) := by
    simp_rw [ph_neg]
    exact ph_continuous ρ _
  have hvn : ∀ x : InfinitePlace F → ℝ,
      ‖Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ))‖ = 1 := by
    intro x
    rw [ph_neg, ph_norm]
  have hres := fourier_series hm hfin (μ := (volume : Measure (InfinitePlace F → ℝ)).restrict D)
    (u := fun z => ph ρ (qf (1 / 2 : F) B z)) (fun z => ph_continuous ρ _) (fun z x => ph_norm ρ _ x)
    hv hvn Sel ((volume D).toReal : ℂ)
    (by
      intro z hz
      have hz' : qf (1 / 2 : F) B z = β := hz
      have : ∀ x : InfinitePlace F → ℝ, ph ρ (qf (1 / 2 : F) B z) x *
          Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ)) = 1 := by
        intro x
        rw [ph_neg, ph_mul, hz', add_neg_cancel, ph_zero]
      simp_rw [this]
      simp [setIntegral_const, Measure.real])
    (by
      intro z hz
      by_cases hall : ∀ ω, s z ω = 0
      · exact Or.inr hall
      left
      push_neg at hall
      obtain ⟨ω, hω⟩ := hall
      obtain ⟨r, hr⟩ := integral_of_ne_zero (hOrth ω) hint hmem hω
      obtain ⟨r₀, hr₀⟩ := hNβ
      have hne : qf (1 / 2 : F) B z + -β ≠ 0 := fun h => hz (add_neg_eq_zero.mp h)
      have := horth _ hne ⟨r - r₀, by
        have hsub : ((r - r₀ : 𝓞 F) : F) = (r : F) - (r₀ : F) := map_sub (algebraMap (𝓞 F) F) r r₀
        rw [hsub, hr, hr₀]
        ring⟩
      have hx : ∀ x : InfinitePlace F → ℝ, ph ρ (qf (1 / 2 : F) B z) x *
          Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ)) =
          ph ρ (qf (1 / 2 : F) B z + -β) x := by
        intro x
        rw [ph_neg, ph_mul]
      simp_rw [hx]
      exact this)
  have hth : ∀ (x : InfinitePlace F → ℝ) (ω : Ω),
      theta B ρ P (gf ω) (gi ω) (indL a) (fun w => (x w : ℂ) + Complex.I) =
        ∑' z, ph ρ (qf (1 / 2 : F) B z) x * s z ω := fun x ω =>
    tsum_congr fun z => thTerm_shift P (hOrth ω) _ x z
  have hI : ∫⁻ ω, ∑' x : {x : ι → F // qf (1 / 2 : F) B x = β}, ‖s x.1 ω‖ₑ ∂Pr ≠ ∞ :=
    ne_top_of_le_ne_top hfin (lintegral_mono fun ω =>
      ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective fun z => ‖s z ω‖ₑ)
  refine ⟨_, (ENNReal.coe_toNNReal hI).symm, ?_, ?_⟩
  · simp_rw [hth]
    exact hres.1
  · simp_rw [hth]
    rw [hres.2, sum_selected hm hfin hpos Sel]
    rfl

end Theta

section Eis

open GlobalTheory.CompanionTheory.SW.CoefEis

theorem fourier_coeff_eis_any : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → 3 ≤ M → ∀ φ : (ι → A F) → ℂ, SB φ → Integrable (fstar ψ (hf F) (Bf B) (muF B lf) φ) lf → Integrable (fun x : InfinitePlace F → ℝ => cG B ρ P (fun w => (x w : ℂ) + Complex.I)) → ∀ β : F, ∀ N : ℕ, 0 < N → (∃ r : 𝓞 F, (r : F) = (N : F) * β) → (∀ x ∈ Oh F, ∀ y : A F, fstar ψ (hf F) (Bf B) (muF B lf) φ (y + (N : A F) * x) = fstar ψ (hf F) (Bf B) (muF B lf) φ y) → ∀ D : Set (InfinitePlace F → ℝ), IsAddFundamentalDomain (latR ρ N) D volume → IntegrableOn (fun x : InfinitePlace F → ℝ => eis ψ lf B ρ P φ (fun w => (x w : ℂ) + Complex.I) * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ))) D volume ∧ ∫ x in D, eis ψ lf B ρ P φ (fun w => (x w : ℂ) + Complex.I) * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ)) = φ 0 * (∫ x in D, Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ))) + ((N : ℂ) ^ Module.finrank ℚ F * ∫ y, fstar ψ (hf F) (Bf B) (muF B lf) φ y * ψ (-(algebraMap F (A F) β) * y) ∂lf) * ∫ x : InfinitePlace F → ℝ, cG B ρ P (fun w => (x w : ℂ) + Complex.I) * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ)) := by
  intro F _ _ _ _ lf hlf h1 ψ hψ ι _ _ M B ρ P hQ hM φ hφ hΦ hc β N hN hNβ hper D hD
  obtain ⟨hTR, -, -, -, hρ, -, -⟩ := id hQ
  have hcount : Countable F := (Module.finBasis ℚ F).equivFun.toEquiv.injective.countable
  obtain ⟨-, hLcount, hLmem, hLD⟩ := GlobalTheory.T.lattice_fundamental_domain_volume F hTR ρ hρ N hN
  obtain ⟨hvol, -⟩ := hLD D hD
  obtain ⟨-, -, -, -, hOopen, -, hOint, -, -, hWopen⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  obtain ⟨-, hψ'⟩ := GlobalTheory.T.standard_adelic_character F
  obtain ⟨hψ1, hψO, -⟩ := hψ' ψ hψ
  obtain ⟨C, hC⟩ := GlobalTheory.T.summable_norm_eiTerm_and_wt_mul_tsum_le F lf hlf h1 ψ hψ ι M B ρ P hQ hM φ hφ 1 one_pos
  haveI := hLcount
  haveI : lf.IsAddHaarMeasure := hlf

  set Φ := fstar ψ (hf F) (Bf B) (muF B lf) φ with hΦdef
  set c : (InfinitePlace F → ℝ) → ℂ := fun x => cG B ρ P (fun w => (x w : ℂ) + Complex.I) with hcdef
  set e : (InfinitePlace F → ℝ) → ℂ := fun x =>
    Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ)) with hedef
  let j : F →+ (InfinitePlace F → ℝ) :=
    { toFun := fun b w => ρ w b
      map_zero' := by ext w; simp
      map_add' := fun a b => by ext w; simp }
  have hj : ∀ b w, j b w = ρ w b := fun _ _ => rfl
  have hjinj : Function.Injective j := by
    intro a b hab
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    exact (ρ w).injective (congrFun hab w)
  set al : F →+* A F := algebraMap F (A F) with hal

  have hecont : Continuous e := by
    simp only [hedef]
    fun_prop
  have henorm : ∀ x, ‖e x‖ = 1 := by
    intro x
    simp only [hedef]
    have : -(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ)
        = ((-(2 * Real.pi * ∑ w, ρ w β * x w) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  have headd : ∀ x y, e (x + y) = e x * e y := by
    intro x y
    simp only [hedef, ← Complex.exp_add]
    congr 1
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    push_cast
    ring
  have hechar : ∀ b : F, e (-(j b)) = ψ (-(al β) * al b) := by
    intro b
    have h2 : -(al β) * al b = al (-(β * b)) := by simp [hal]
    rw [h2, hψ.2]
    simp only [hedef]
    congr 1
    have h3 : (∑ w, ρ w β * (-(j b)) w) = -((Algebra.trace ℚ F (β * b) : ℚ) : ℝ) := by
      rw [← sum_places_eq_trace F hTR ρ hρ (β * b), ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun w _ => ?_
      simp [hj]
    rw [h3, map_neg]
    push_cast
    ring

  let H : AddSubgroup F := (latR ρ N).comap j
  have hHmem : ∀ b, b ∈ H ↔ ∃ r : 𝓞 F, b = (N : F) * (r : F) := by
    intro b
    rw [AddSubgroup.mem_comap, hLmem]
    constructor
    · rintro ⟨r, hr⟩
      refine ⟨r, hjinj ?_⟩
      rw [hr]
      rfl
    · rintro ⟨r, rfl⟩
      exact ⟨r, rfl⟩
  have hNal : ∀ n : ℕ, al (n : F) = (n : A F) := fun n => map_natCast _ n

  have hOr : ∀ r : 𝓞 F, al (r : F) ∈ Oh F := fun r => (hOint _).2 ⟨r, rfl⟩
  have heLat : ∀ l ∈ latR ρ N, e l = 1 := by
    intro l hl
    obtain ⟨r, rfl⟩ := (hLmem l).1 hl
    obtain ⟨r0, hr0⟩ := hNβ
    have h4 : (fun w => ρ w ((N : F) * (r : F))) = -(j (-((N : F) * (r : F)))) := by
      ext w
      simp [hj]
    rw [h4, hechar]
    have h5 : -(al β) * al (-((N : F) * (r : F))) = al ((r0 * r : 𝓞 F) : F) := by
      rw [← map_neg, ← map_mul]
      congr 1
      rw [show ((r0 * r : 𝓞 F) : F) = (r0 : F) * (r : F) from map_mul (algebraMap (𝓞 F) F) r0 r, hr0]
      ring
    rw [h5]
    exact hψO _ (hOr _)
  have hap : ∀ b, ∀ h ∈ H, Φ (al (b + h)) = Φ (al b) := by
    intro b h hh
    obtain ⟨r, rfl⟩ := (hHmem h).1 hh
    have : al (b + (N : F) * (r : F)) = al b + (N : A F) * al (r : F) := by
      rw [map_add (f := _), map_mul, hNal]
    rw [this]
    exact hper _ (hOr r) _
  have hterm : ∀ (x : InfinitePlace F → ℝ) (b : F),
      eiTerm ψ lf B ρ P φ (fun w => (x w : ℂ) + Complex.I) b = Φ (al b) * c (x + j b) := by
    intro x b
    simp only [eiTerm, hcdef]
    congr 2
    ext w
    simp only [Pi.add_apply, hj]
    push_cast
    ring
  have hbd : ∀ x : InfinitePlace F → ℝ, Summable (fun b => ‖Φ (al b) * c (x + j b)‖) ∧
      ∑' b, ‖Φ (al b) * c (x + j b)‖ ≤ C := by
    intro x
    have h6 := hC (fun w => (x w : ℂ) + Complex.I) (fun w => by simp)
    simp only [hterm] at h6
    have h7 : wt M (fun w => (x w : ℂ) + Complex.I) = 1 := by simp [wt]
    rw [h7, one_mul] at h6
    exact h6
  have hDfin : volume D ≠ ⊤ := by rw [hvol]; exact ENNReal.ofReal_ne_top
  haveI : IsFiniteMeasure (volume.restrict D) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hDfin⟩
  set T : F → (InfinitePlace F → ℝ) → ℂ := fun b x => Φ (al b) * c (x + j b) * e x with hT
  have hTnorm : ∀ b x, ‖T b x‖ = ‖Φ (al b) * c (x + j b)‖ := by
    intro b x
    simp only [hT, norm_mul, henorm, mul_one]
  have hTmeas : ∀ b, AEStronglyMeasurable (T b) (volume.restrict D) := by
    intro b
    have h8 : AEStronglyMeasurable (fun x => c (x + j b)) volume :=
      (hc.comp_add_right (j b)).aestronglyMeasurable
    exact ((h8.const_mul _).mul hecont.aestronglyMeasurable).restrict
  obtain ⟨hInt, hSum, hEq⟩ := tsum_integral_swap F (InfinitePlace F → ℝ) (volume.restrict D) T C hTmeas
    (fun x => by simpa only [hTnorm] using (hbd x).1)
    (fun x => by simpa only [hTnorm] using (hbd x).2)
  have heInt : Integrable e (volume.restrict D) :=
    Integrable.of_bound hecont.aestronglyMeasurable 1 (ae_of_all _ fun x => (henorm x).le)
  have Heisenberg₂ : ∀ x : InfinitePlace F → ℝ,
      eis ψ lf B ρ P φ (fun w => (x w : ℂ) + Complex.I) * e x = φ 0 * e x + ∑' b, T b x := by
    intro x
    simp only [eis, add_mul, hT, hterm, tsum_mul_right]
  refine ⟨?_, ?_⟩
  · have : (fun x : InfinitePlace F → ℝ => eis ψ lf B ρ P φ (fun w => (x w : ℂ) + Complex.I) * e x)
        = fun x => φ 0 * e x + ∑' b, T b x := funext Heisenberg₂
    rw [IntegrableOn, this]
    exact (heInt.const_mul _).add hInt
  · change ∫ x in D, eis ψ lf B ρ P φ (fun w => (x w : ℂ) + Complex.I) * e x =
      φ 0 * (∫ x in D, e x) + ((N : ℂ) ^ Module.finrank ℚ F * ∫ y, Φ y * ψ (-(al β) * y) ∂lf) * ∫ x, c x * e x
    set Ch : ℂ := ∫ x, c x * e x with hCh
    simp only [Heisenberg₂]
    rw [integral_add (heInt.const_mul _) hInt, integral_const_mul, hEq, tsum_cosets F H _ hSum]
    congr 1

    let eH : H ≃ latR ρ N := Equiv.ofBijective (fun h => ⟨j h, h.2⟩) (by
      constructor
      · intro a b hab
        exact Subtype.ext (hjinj (congrArg Subtype.val hab))
      · rintro ⟨l, hl⟩
        obtain ⟨r, rfl⟩ := (hLmem l).1 hl
        exact ⟨⟨(N : F) * (r : F), (hHmem _).2 ⟨r, rfl⟩⟩, rfl⟩)
    have hcoset : ∀ q : F ⧸ H, ∑' h : H, ∫ x in D, T (q.out + (h : F)) x =
        Φ (al q.out) * e (-(j q.out)) * Ch := by
      intro q
      have h10 : ∀ h : H, ∫ x in D, T (q.out + (h : F)) x =
          Φ (al q.out) * ∫ x in D, c (x + (j q.out + ((eH h : latR ρ N) : InfinitePlace F → ℝ))) * e x := by
        intro h
        rw [← integral_const_mul]
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp only [hT]
        rw [hap _ _ h.2, map_add j, mul_assoc]
        rfl
      simp only [h10]
      rw [tsum_mul_left, eH.tsum_eq (fun l : latR ρ N =>
        ∫ x in D, c (x + (j q.out + (l : InfinitePlace F → ℝ))) * e x),
        unfold_char (InfinitePlace F) (latR ρ N) D hD c e hc hecont henorm headd heLat (j q.out)]
      ring
    simp only [hcoset]
    rw [tsum_mul_right]
    congr 1

    set W : Set (A F) := {x : A F | ∃ z ∈ Oh F, x = (N : A F) * z} with hW
    obtain ⟨hcov, hdis⟩ := cosets_of_multiples F N hN H hHmem
    set G : A F → ℂ := fun y => Φ y * ψ (-(al β) * y) with hG
    have hGint : Integrable G lf := by
      refine hΦ.mono ?_ (ae_of_all _ fun y => ?_)
      · refine hΦ.aestronglyMeasurable.mul (Continuous.aestronglyMeasurable ?_)
        exact hψ.1.comp (by fun_prop)
      · simp only [hG, norm_mul, hψ1, mul_one, le_refl]
    have hGper : ∀ y, ∀ w ∈ W, G (y + w) = G y := by
      rintro y w ⟨z, hz, rfl⟩
      obtain ⟨r0, hr0⟩ := hNβ
      have h11 : -(al β) * (y + (N : A F) * z) = -(al β) * y + al (-(r0 : F)) * z := by
        rw [hr0, ← hNal]
        simp only [map_neg, map_mul]
        ring
      have h12 : al (-(r0 : F)) * z ∈ Oh F := by
        rw [show -(r0 : F) = ((-r0 : 𝓞 F) : F) from (map_neg (algebraMap (𝓞 F) F) r0).symm]
        exact Oh_mul_mem F _ _ (hOr _) hz
      simp only [hG]
      rw [hper z hz y, h11, AddChar.map_add_eq_mul, hψO _ h12, mul_one]
    haveI : Countable (F ⧸ H) := Function.Surjective.countable (f := fun b : F => (b : F ⧸ H))
      (fun q => ⟨q.out, QuotientAddGroup.out_eq' q⟩)
    have hsum := hasSum_integral_cosets (A F) (F ⧸ H) lf (fun q => al q.out) W (hWopen N hN) hcov hdis G hGint hGper
    have h13 : ∀ q : F ⧸ H, G (al q.out) = Φ (al q.out) * e (-(j q.out)) := by
      intro q
      simp only [hG, hechar]
    have h14 := hsum.tsum_eq
    simp only [h13] at h14
    rw [tsum_mul_left] at h14
    rw [← h14, ← mul_assoc]
    have h15 := mass_multiples F lf hlf h1 N hN
    have h16 : (((N : ℂ) ^ Module.finrank ℚ F) * (((lf W).toReal : ℝ) : ℂ)) = 1 := by
      rw [mul_comm]
      exact_mod_cast h15
    rw [h16, one_mul]

end Eis

lemma tsum_split {α : Type} (f : α → ℝ≥0∞) (p : α → Prop) (z : α) (hz : p z) :
    ∑' x : {x // p x}, f x.1 = f z + ∑' x : {x // x ≠ z ∧ p x}, f x.1 := by
  classical
  have a1 := tsum_subtype {x | p x} f
  have a2 := tsum_subtype {x | x ≠ z ∧ p x} f
  change ∑' x : ({x | p x} : Set α), f x.1 = f z + ∑' x : ({x | x ≠ z ∧ p x} : Set α), f x.1
  rw [a1, a2, ENNReal.tsum_eq_add_tsum_ite z, Set.indicator_of_mem (show z ∈ {x | p x} from hz)]
  congr 1
  refine tsum_congr fun x => ?_
  by_cases h : x = z
  · simp [h]
  · by_cases hp : p x <;> simp [h, hp, Set.indicator]

lemma thTerm_zero {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ)
    (gf : Matrix ι ι (A F)) (gi : InfinitePlace F → Matrix ι ι ℝ) (a : ℕ) :
    thTerm B ρ P gf gi (indL a) (fun _ => Complex.I) 0 = 1 := by
  have hz : (gf *ᵥ fun j => algebraMap F (A F) ((0 : ι → F) j)) = 0 := by
    funext i
    simp [Matrix.mulVec, dotProduct]
  have hg : gauss B ρ P (fun _ => Complex.I) (fun w => gi w *ᵥ fun j => ρ w ((0 : ι → F) j)) = 1 := by
    have : ∀ w, (gi w *ᵥ fun j => ρ w ((0 : ι → F) j)) = 0 := by
      intro w
      funext i
      simp [Matrix.mulVec, dotProduct]
    simp only [gauss, this]
    simp
  have hm : (0 : ι → A F) ∈ {x : ι → A F | ∀ i, (a : A F) * x i ∈ Oh F} := fun i v => by
    simp only [Pi.zero_apply, mul_zero]
    exact zero_mem _
  unfold thTerm
  rw [hz, hg, mul_one]
  simp only [indL, Set.indicator_of_mem hm]

theorem core_zero : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ), Fintype.card ι = 2 * M → 3 ≤ M → ∀ (B : Matrix ι ι F), B.IsSymm → B.det ≠ 0 → ∀ (ρ : InfinitePlace F → (F →+* ℝ)), (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) → ∀ (Pm : InfinitePlace F → Matrix ι ι ℝ), (∀ w, (Pm w).PosDef) → (∀ w, Pm w * (B.map (ρ w))⁻¹ * Pm w = B.map (ρ w)) → ∀ [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)] (lf : Measure (FiniteAdeleRing (𝓞 F) F)), lf.IsAddHaarMeasure → lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1 → ∀ (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr] (ginf : Ω → InfinitePlace F → Matrix ι ι ℝ) (gf : Ω → Matrix ι ι (FiniteAdeleRing (𝓞 F) F)), (∀ w i j, Measurable fun ω => ginf ω w i j) → (∀ i j, Measurable fun ω => gf ω i j) → (∀ ω w, (ginf ω w)ᵀ * B.map (ρ w) * ginf ω w = B.map (ρ w)) → (∀ ω, (gf ω)ᵀ * B.map (algebraMap F (FiniteAdeleRing (𝓞 F) F)) * gf ω = B.map (algebraMap F (FiniteAdeleRing (𝓞 F) F))) → (∀ N : ℕ, 0 < N → ∃ C : ℝ, ∀ R : ℝ, 0 < R → ∫⁻ ω, ∑' x : {x : ι → F // x ≠ 0}, Set.indicator {x : ι → F | (∀ i v, ((N : FiniteAdeleRing (𝓞 F) F) * (gf ω *ᵥ fun j => algebraMap F (FiniteAdeleRing (𝓞 F) F) (x j)) i) v ∈ v.adicCompletionIntegers F) ∧ ∀ w, ‖ginf ω w *ᵥ fun j => ρ w (x j)‖ ≤ R} (fun _ => (1 : ℝ≥0∞)) x.1 ∂Pr ≤ ENNReal.ofReal (C * (R ^ (Module.finrank ℚ F * M) + R ^ (2 * Module.finrank ℚ F * M)))) → ∃ (C : ℝ) (Df : ℕ → FiniteAdeleRing (𝓞 F) F → ℝ) (Dinf : (InfinitePlace F → ℝ) → ℝ), (∀ a : ℕ, 0 < a → Continuous (Df a) ∧ (∀ y, 0 ≤ Df a y) ∧ ∀ U : Set (FiniteAdeleRing (𝓞 F) F), MeasurableSet U → (Measure.pi fun _ : ι => lf) {x | (∀ i v, ((a : FiniteAdeleRing (𝓞 F) F) * x i) v ∈ v.adicCompletionIntegers F) ∧ algebraMap F (FiniteAdeleRing (𝓞 F) F) (1 / 2) * (x ⬝ᵥ (B.map (algebraMap F (FiniteAdeleRing (𝓞 F) F)) *ᵥ x)) ∈ U} = ∫⁻ y in U, ENNReal.ofReal (Df a y) ∂lf) ∧ (Continuous Dinf ∧ (∀ y, 0 ≤ Dinf y) ∧ ∀ U : Set (InfinitePlace F → ℝ), MeasurableSet U → ∫⁻ x in {x : InfinitePlace F → ι → ℝ | (fun w => (1 / 2 : ℝ) * (x w ⬝ᵥ (B.map (ρ w) *ᵥ x w))) ∈ U}, ENNReal.ofReal (Real.exp (-Real.pi * ∑ w, x w ⬝ᵥ (Pm w *ᵥ x w))) = ∫⁻ y in U, ENNReal.ofReal (Dinf y)) ∧ ∀ a : ℕ, 0 < a → ∃ I : ℝ≥0, ∫⁻ ω, ∑' x : {x : ι → F // x ≠ 0 ∧ (1 / 2 : F) * (x ⬝ᵥ (B *ᵥ x)) = 0}, Set.indicator {x : ι → F | ∀ i v, ((a : FiniteAdeleRing (𝓞 F) F) * (gf ω *ᵥ fun j => algebraMap F (FiniteAdeleRing (𝓞 F) F) (x j)) i) v ∈ v.adicCompletionIntegers F} (fun x => ENNReal.ofReal (Real.exp (-Real.pi * ∑ w, (ginf ω w *ᵥ fun j => ρ w (x j)) ⬝ᵥ (Pm w *ᵥ (ginf ω w *ᵥ fun j => ρ w (x j)))))) x.1 ∂Pr = (I : ℝ≥0∞) ∧ |(I : ℝ) - (Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (2 * M - 1) * Df a 0 * Dinf (fun _ => 0)| ≤ C * (a : ℝ) ^ (Module.finrank ℚ F * M) := by
  intro F _ _ hF ι _ _ M hc hM B hB hdet ρ hρ P hP hPP _ _ lf hlf h1 Ω _ Pr _ gi gf m1 m2 o1 o2 hcnt
  have hQ : QSetup M B ρ P := ⟨hF, hc, hB, hdet, hρ, hP, hPP⟩
  have hC : CountData M B ρ Pr gf gi := ⟨inferInstance, m1, m2, fun ω => ⟨o2 ω, o1 ω⟩, hcnt⟩
  obtain ⟨ψ, hψ⟩ := (GlobalTheory.T.standard_adelic_character F).1
  obtain ⟨C, hb⟩ := PositivityTheory.PlacePermOperatorBicommutantSpan.bounded_a F lf hlf h1 ψ hψ ι M B ρ P hQ hM Ω Pr gf gi hC
  choose! Df d1 d2 d3 d4 d5 using GlobalTheory.T.schur_function_whittaker_equivariant F lf hlf h1 ψ hψ ι M B ρ P hQ hM
  obtain ⟨Di, i1, i2, i3, i4, i5⟩ := GlobalTheory.T.quadratic_level_set_density F ι M B ρ P hQ hM
  refine ⟨C, Df, Di, fun a ha => ⟨d1 a ha, d2 a ha, d3 a ha⟩, ⟨i1, i2, i3⟩, fun a ha => ?_⟩
  obtain ⟨-, -, -, -, -, -, hint, -, hK, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  have hs := PositivityTheory.PlacePermOperatorBicommutantSpan.sb_indL (F := F) (ι := ι) ha
  obtain ⟨N₁, p1, n1⟩ := GlobalTheory.T.weil_operator_integral_invariance F lf hlf h1 ψ hψ ι M B ρ P hQ _ hs
  have hq : Continuous (qf (hf F) (Bf B) : (ι → A F) → A F) := by unfold qf; fun_prop
  obtain ⟨N₂, p2, n2⟩ := hK _ ((hs.2.isCompact.image hq).insert (algebraMap F (A F) 0))
  have hN : 0 < N₁ * N₂ := Nat.mul_pos p1 p2
  have hβN : ∃ r : 𝓞 F, (r : F) = ((N₁ * N₂ : ℕ) : F) * 0 := ⟨0, by simp⟩
  obtain ⟨⟨D, hD⟩, -, -, hvol⟩ := GlobalTheory.T.lattice_fundamental_domain_volume F hF ρ hρ _ hN
  obtain ⟨I, e1, j1, e2⟩ := fourier_coefficient_any F ι M B ρ P hQ Ω Pr gf gi hC a ha 0 _ hN hβN (fun y hy => by
    rw [Nat.cast_mul, mul_assoc]
    refine PositivityTheory.PlacePermOperatorBicommutantSpan.oh_mul (PositivityTheory.PlacePermOperatorBicommutantSpan.oh_nat N₁) (n2 _ (Set.mem_insert_of_mem _ ⟨y, subset_tsupport _ ?_, rfl⟩))
    rw [Function.mem_support, indL, Set.indicator_of_mem (s := {x : ι → A F | ∀ i, (a : A F) * x i ∈ Oh F}) hy]
    exact one_ne_zero) D hD
  obtain ⟨j2, e3⟩ := fourier_coeff_eis_any F lf hlf h1 ψ hψ ι M B ρ P hQ hM _ hs (d4 a ha) i4 0 _ hN hβN
    (fun x hx y => by
      rw [Nat.cast_mul, mul_assoc]
      exact (n1 _ (PositivityTheory.PlacePermOperatorBicommutantSpan.oh_mul (PositivityTheory.PlacePermOperatorBicommutantSpan.oh_nat N₂) hx)).2 y) D hD
  haveI : IsProbabilityMeasure Pr := hC.1

  have hsplit : ∀ ω, ∑' x : {x : ι → F // qf (1 / 2 : F) B x = 0},
      ‖thTerm B ρ P (gf ω) (gi ω) (indL a) (fun _ => Complex.I) x.1‖ₑ =
      1 + ∑' x : {x : ι → F // x ≠ 0 ∧ qf (1 / 2 : F) B x = 0},
        ‖thTerm B ρ P (gf ω) (gi ω) (indL a) (fun _ => Complex.I) x.1‖ₑ := fun ω => by
    rw [tsum_split (fun x => ‖thTerm B ρ P (gf ω) (gi ω) (indL a) (fun _ => Complex.I) x‖ₑ)
      (fun x => qf (1 / 2 : F) B x = 0) 0 (by simp [qf]), thTerm_zero]
    simp
  have e1' : 1 + ∫⁻ ω, ∑' x : {x : ι → F // x ≠ 0 ∧ qf (1 / 2 : F) B x = 0},
      ‖thTerm B ρ P (gf ω) (gi ω) (indL a) (fun _ => Complex.I) x.1‖ₑ ∂Pr = (I : ℝ≥0∞) := by
    rw [← e1]
    simp_rw [hsplit]
    rw [lintegral_add_left measurable_const]
    simp
  have hJtop : ∫⁻ ω, ∑' x : {x : ι → F // x ≠ 0 ∧ qf (1 / 2 : F) B x = 0},
      ‖thTerm B ρ P (gf ω) (gi ω) (indL a) (fun _ => Complex.I) x.1‖ₑ ∂Pr ≠ ∞ := by
    intro h
    rw [h] at e1'
    simp at e1'
  obtain ⟨J, hJ⟩ : ∃ J : ℝ≥0, ∫⁻ ω, ∑' x : {x : ι → F // x ≠ 0 ∧ qf (1 / 2 : F) B x = 0},
      ‖thTerm B ρ P (gf ω) (gi ω) (indL a) (fun _ => Complex.I) x.1‖ₑ ∂Pr = (J : ℝ≥0∞) :=
    ⟨_, (ENNReal.coe_toNNReal hJtop).symm⟩
  have hIJ : (I : ℝ) = 1 + (J : ℝ) := by
    rw [hJ] at e1'
    have : (1 + J : ℝ≥0) = I := by exact_mod_cast e1'
    rw [← this]
    push_cast
    rfl
  refine ⟨J, Eq.trans (lintegral_congr fun ω => tsum_congr fun x => ?_) hJ, ?_⟩
  · by_cases hx : ∀ i, (a : A F) * (gf ω *ᵥ fun j => algebraMap F (A F) (x.1 j)) i ∈ Oh F
    · rw [Set.indicator_of_mem (by exact hx), thTerm, indL,
        Set.indicator_of_mem (s := {x : ι → A F | ∀ i, (a : A F) * x i ∈ Oh F}) hx, one_mul, ← ofReal_norm, gauss,
        Complex.norm_exp]
      congr 2
      simp [Finset.mul_sum]
    · rw [Set.indicator_of_notMem (by exact hx), thTerm, indL,
        Set.indicator_of_notMem (s := {x : ι → A F | ∀ i, (a : A F) * x i ∈ Oh F}) hx, zero_mul, enorm_zero]
  · have hk : 0 < kap F := inv_pos.2 (Real.sqrt_pos.2 (abs_pos.2 (by exact_mod_cast discr_ne_zero F)))
    have hsq : 0 < Real.sqrt |((Algebra.norm ℚ B.det : ℚ) : ℝ)| :=
      Real.sqrt_pos.2 (abs_pos.2 (by exact_mod_cast Algebra.norm_ne_zero_iff.2 hdet))
    set v : ℝ := ((N₁ * N₂ : ℕ) : ℝ) ^ Module.finrank ℚ F * (kap F)⁻¹ with hv
    have hv0 : 0 < v := by positivity
    have hvD : volume.real D = v := by rw [Measure.real, (hvol D hD).1, ENNReal.toReal_ofReal hv0.le]
    have hph : ∀ x : InfinitePlace F → ℝ,
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w (0 : F) * x w : ℝ) : ℂ)) = 1 := fun x => by simp
    have hind : indL (F := F) (ι := ι) a 0 = 1 := by
      have hm : (0 : ι → A F) ∈ {x : ι → A F | ∀ i, (a : A F) * x i ∈ Oh F} := fun i v => by
        simp only [Pi.zero_apply, mul_zero]
        exact zero_mem _
      simp only [indL, Set.indicator_of_mem hm]
    have h2 := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := D)
      (f := fun x : InfinitePlace F → ℝ => (∫ ω, theta B ρ P (gf ω) (gi ω) (indL a) (fun w => (x w : ℂ) + Complex.I) ∂Pr) *
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w (0 : F) * x w : ℝ) : ℂ)) -
        eis ψ lf B ρ P (indL a) (fun w => (x w : ℂ) + Complex.I) *
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w (0 : F) * x w : ℝ) : ℂ)))
      (C := C * (a : ℝ) ^ (Module.finrank ℚ F * M)) (by rw [(hvol D hD).1]; exact ENNReal.ofReal_lt_top) fun x _ => by
        rw [hph, mul_one, mul_one]
        exact (hb a ha x).2
    have hi0 : (fun w => ρ w (0 : F)) = fun _ => (0 : ℝ) := by
      funext w
      exact map_zero _
    have hz0 : algebraMap F (A F) 0 = 0 := map_zero _
    have hD1 : ∫ x in D, Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w (0 : F) * x w : ℝ) : ℂ)) = (v : ℂ) := by
      simp_rw [hph]
      simp [setIntegral_const, hvD]
    rw [integral_sub j1 j2, e2, e3, hD1, hind, d5 a ha, i5, hvD, show (volume D).toReal = v from hvD, hi0, hz0] at h2
    have e4 : ((v : ℝ) : ℂ) * ((I : ℝ) : ℂ) - (1 * ((v : ℝ) : ℂ) + ((N₁ * N₂ : ℕ) : ℂ) ^ Module.finrank ℚ F *
        ((kap F ^ (2 * M - 2) * (Real.sqrt |((Algebra.norm ℚ B.det : ℚ) : ℝ)|)⁻¹ * Df a 0 : ℝ) : ℂ) *
        ((Real.sqrt |((Algebra.norm ℚ B.det : ℚ) : ℝ)| * Di (fun _ => 0) : ℝ) : ℂ)) =
        ((v * ((J : ℝ) - kap F ^ (2 * M - 1) * Df a 0 * Di fun _ => 0) : ℝ) : ℂ) := by
      rw [hIJ, ← Complex.ofReal_natCast, ← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
        ← Complex.ofReal_mul, ← Complex.ofReal_one, ← Complex.ofReal_mul, ← Complex.ofReal_add,
        ← Complex.ofReal_sub, show 2 * M - 1 = 2 * M - 2 + 1 by omega, pow_succ, hv]
      congr 1
      field_simp
      ring
    rw [e4, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hv0, mul_comm v] at h2
    exact le_of_mul_le_mul_right h2 hv0

end GlobalTheory.CompanionTheory.SW.Core0
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussianFourierSelfDualAdelicStatement
open NumberField IsDedekindDomain MeasureTheory Matrix
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussian_fourier_self_dual_adelic : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ), Fintype.card ι = 2 * M → 3 ≤ M → ∀ (B : Matrix ι ι F), B.IsSymm → B.det ≠ 0 → ∀ (ρ : InfinitePlace F → (F →+* ℝ)), (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) → ∀ (Pm : InfinitePlace F → Matrix ι ι ℝ), (∀ w, (Pm w).PosDef) → (∀ w, Pm w * (B.map (ρ w))⁻¹ * Pm w = B.map (ρ w)) → ∀ [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)] (lf : Measure (FiniteAdeleRing (𝓞 F) F)), lf.IsAddHaarMeasure → lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1 → ∀ (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr] (ginf : Ω → InfinitePlace F → Matrix ι ι ℝ) (gf : Ω → Matrix ι ι (FiniteAdeleRing (𝓞 F) F)), (∀ w i j, Measurable fun ω => ginf ω w i j) → (∀ i j, Measurable fun ω => gf ω i j) → (∀ ω w, (ginf ω w)ᵀ * B.map (ρ w) * ginf ω w = B.map (ρ w)) → (∀ ω, (gf ω)ᵀ * B.map (algebraMap F (FiniteAdeleRing (𝓞 F) F)) * gf ω = B.map (algebraMap F (FiniteAdeleRing (𝓞 F) F))) → (∀ N : ℕ, 0 < N → ∃ C : ℝ, ∀ R : ℝ, 0 < R → ∫⁻ ω, ∑' x : {x : ι → F // x ≠ 0}, Set.indicator {x : ι → F | (∀ i v, ((N : FiniteAdeleRing (𝓞 F) F) * (gf ω *ᵥ fun j => algebraMap F (FiniteAdeleRing (𝓞 F) F) (x j)) i) v ∈ v.adicCompletionIntegers F) ∧ ∀ w, ‖ginf ω w *ᵥ fun j => ρ w (x j)‖ ≤ R} (fun _ => (1 : ℝ≥0∞)) x.1 ∂Pr ≤ ENNReal.ofReal (C * (R ^ (Module.finrank ℚ F * M) + R ^ (2 * Module.finrank ℚ F * M)))) → ∃ (C : ℝ) (Df : ℕ → FiniteAdeleRing (𝓞 F) F → ℝ) (Dinf : (InfinitePlace F → ℝ) → ℝ), (∀ a : ℕ, 0 < a → Continuous (Df a) ∧ (∀ y, 0 ≤ Df a y) ∧ ∀ U : Set (FiniteAdeleRing (𝓞 F) F), MeasurableSet U → (Measure.pi fun _ : ι => lf) {x | (∀ i v, ((a : FiniteAdeleRing (𝓞 F) F) * x i) v ∈ v.adicCompletionIntegers F) ∧ algebraMap F (FiniteAdeleRing (𝓞 F) F) (1 / 2) * (x ⬝ᵥ (B.map (algebraMap F (FiniteAdeleRing (𝓞 F) F)) *ᵥ x)) ∈ U} = ∫⁻ y in U, ENNReal.ofReal (Df a y) ∂lf) ∧ (Continuous Dinf ∧ (∀ y, 0 ≤ Dinf y) ∧ ∀ U : Set (InfinitePlace F → ℝ), MeasurableSet U → ∫⁻ x in {x : InfinitePlace F → ι → ℝ | (fun w => (1 / 2 : ℝ) * (x w ⬝ᵥ (B.map (ρ w) *ᵥ x w))) ∈ U}, ENNReal.ofReal (Real.exp (-Real.pi * ∑ w, x w ⬝ᵥ (Pm w *ᵥ x w))) = ∫⁻ y in U, ENNReal.ofReal (Dinf y)) ∧ ∀ a : ℕ, 0 < a → ∃ I : ℝ≥0, ∫⁻ ω, ∑' x : {x : ι → F // x ≠ 0 ∧ (1 / 2 : F) * (x ⬝ᵥ (B *ᵥ x)) = 0}, Set.indicator {x : ι → F | ∀ i v, ((a : FiniteAdeleRing (𝓞 F) F) * (gf ω *ᵥ fun j => algebraMap F (FiniteAdeleRing (𝓞 F) F) (x j)) i) v ∈ v.adicCompletionIntegers F} (fun x => ENNReal.ofReal (Real.exp (-Real.pi * ∑ w, (ginf ω w *ᵥ fun j => ρ w (x j)) ⬝ᵥ (Pm w *ᵥ (ginf ω w *ᵥ fun j => ρ w (x j)))))) x.1 ∂Pr = (I : ℝ≥0∞) ∧ |(I : ℝ) - (Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (2 * M - 1) * Df a 0 * Dinf (fun _ => 0)| ≤ C * (a : ℝ) ^ (Module.finrank ℚ F * M) := by
  first | exact @GlobalTheory.CompanionTheory.SW.Core0.core_zero | exact GlobalTheory.CompanionTheory.SW.Core0.core_zero | (intros; apply GlobalTheory.CompanionTheory.SW.Core0.core_zero <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalVolumeRankOneNormalised
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free
open GlobalTheory.CompanionTheory.SW.BB GlobalTheory.CompanionTheory.SW.EulerDens

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Free.EstZero

attribute [local instance] GlobalTheory.CompanionTheory.SW.EulerDens.instLCv GlobalTheory.CompanionTheory.SW.EulerDens.instSCv GlobalTheory.CompanionTheory.SW.EulerDens.instBorv
  GlobalTheory.CompanionTheory.SW.EulerDens.instBorf GlobalTheory.CompanionTheory.SW.EulerDens.instLCf GlobalTheory.CompanionTheory.SW.EulerDens.instSCf

theorem hasProd_free_mass_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (h₀ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b), ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), (∀ v, IsStdV v (lam v)) → ∀ (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), (∀ v, IsGramFibFree (Fv F v) σ J 1 (coordW (Fv F v) b (lam v) 1 M) (coordHerm (Fv F v) σ b (lam v) 1) (m v)) → ∀ (lf : Measure (Af F)), lf.IsAddHaarMeasure → lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1 → ∀ a : ℕ, 0 < a → ∀ D : Af F → ℝ, Continuous D → (∀ y, 0 ≤ D y) → (∀ U : Set (Af F), MeasurableSet U → coordW (Af F) b lf 1 M {X | (∀ v, projV v X ∈ {X : (Fin 1 → Fin M → Fv F v ⊗[F] E) | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v}) ∧ algebraMap F (Af F) (1 / 2) * Algebra.trace (Af F) (Af F ⊗[F] E) (gramR (Af F) σ J X 0 0) ∈ U} = ∫⁻ y in U, ENNReal.ofReal (D y) ∂lf) → HasProd (fun v => (m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) {X : (Fin 1 → Fin M → Fv F v ⊗[F] E) | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v}).toReal) (D 0) := by
  intro F E _ _ _ _ _ σ hcm M J hJ hM h₀ d b lam hlam m hm lf hlf hlf1 a ha D hDc hD0 hUD
  classical
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  have hUD' : ∀ U : Set (Af F), MeasurableSet U →
      coordW (Af F) b lf 1 M {X | (∀ v, projV v X ∈ sA b v a) ∧ qF (Af F) σ J X ∈ U} =
        ∫⁻ y in U, ENNReal.ofReal (D y) ∂lf := hUD
  rw [HasProd, SummationFilter.unconditional_filter, Metric.tendsto_atTop]
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  have hWn : {y : Af F | |D y - D 0| < ε / 3} ∈ 𝓝 (0 : Af F) :=
    (isOpen_lt (hDc.sub continuous_const).abs continuous_const).mem_nhds (by simpa using hε3)
  obtain ⟨S₀, N, hN, hNoff, hNW⟩ := exists_box F _ hWn
  have hev := (q_int_ev (M := M) b σ J).and (scale_ev (M := M) b ha)
  have hbad := Filter.eventually_cofinite.1 hev
  refine ⟨S₀ ∪ hbad.toFinset, fun S hS => ?_⟩
  have hS' : ∀ v, v ∉ S → v ∉ S₀ ∧ ((∀ X : Fin 1 → Fin M → Fv F v ⊗[F] E, X ∈ latV b v →
        qF (Fv F v) σ J X ∈ v.adicCompletionIntegers F) ∧
      ∀ X : Fin 1 → Fin M → Fv F v ⊗[F] E, X ∈ sA b v a ↔ X ∈ latV b v) := fun v hv => by
    refine ⟨fun h => hv (hS (Finset.mem_union_left _ h)), ?_⟩
    by_contra hc
    exact hv (hS (Finset.mem_union_right _ (hbad.mem_toFinset.2 hc)))
  obtain ⟨δ, hδ, hclose⟩ := prod_close S
    (fun v => (m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) (sA b v a)).toReal) hε3
  have hloc := fun v => (GlobalTheory.T.local_volume_rank_one_isotropic F E σ hcm M J hJ hM h₀ d b v (lam v) (hlam v) (m v) (hm v)
    (sA b v a) (sA_cpt_open σ hcm b v ha).1 (sA_cpt_open σ hcm b v ha).2).2 δ hδ
  choose Uv hUv hUv' using hloc
  have hVex := fun v => nice_nbhd (hlam v) (Filter.inter_mem (hUv v) (hN v))
  choose V hVo hVs hVpos hVfin using hVex
  have hUW : ∀ y ∈ box S V, |D y - D 0| ≤ ε / 3 := fun y hy => by
    refine le_of_lt (hNW y fun v => ?_)
    by_cases hv : v ∈ S
    · exact (hVs v (hy.1 v hv)).2
    · rw [hNoff v (hS' v hv).1]
      exact hy.2 v hv
  have hBo := box_open S V hVo
  have hL := box_meas lam hlam lf hlf hlf1 S V hVo
  have hP := box_tuple σ hcm J b lam hlam lf hlf hlf1 ha S V hVo (fun v hv => (hS' v hv).2.2)
    (fun v hv => (hS' v hv).2.1)
  rw [hUD' _ hBo.measurableSet] at hP
  have hLv : ∀ v, 0 < (lam v (V v)).toReal := fun v =>
    ENNReal.toReal_pos (hVpos v).ne' (hVfin v).ne
  have hLf : (lf (box S V)).toReal = ∏ v ∈ S, (lam v (V v)).toReal := by
    rw [hL, ENNReal.toReal_prod]
  have hLfpos : 0 < (lf (box S V)).toReal := by
    rw [hLf]
    exact Finset.prod_pos fun v _ => hLv v
  have hfin : lf (box S V) ≠ ∞ := by
    rw [hL]
    exact ENNReal.prod_ne_top fun v _ => (hVfin v).ne
  have hI : (∫⁻ y in box S V, ENNReal.ofReal (D y) ∂lf).toReal =
      ∏ v ∈ S, (coordW (Fv F v) b (lam v) 1 M (sA b v a ∩ {X | qF (Fv F v) σ J X ∈ V v})).toReal := by
    rw [hP, ENNReal.toReal_prod]
  have havg := avg_bound lf hBo.measurableSet hfin D (hD0 _) hε3.le hUW
  have hcl := hclose (fun v =>
    (coordW (Fv F v) b (lam v) 1 M (sA b v a ∩ {X | qF (Fv F v) σ J X ∈ V v})).toReal /
      (lam v (V v)).toReal) (fun v _ => by
    have h1 := hUv' v (V v) (hVo v).measurableSet (fun y hy => (hVs v hy).1)
    have h2 : (coordW (Fv F v) b (lam v) 1 M (sA b v a ∩ {X | qF (Fv F v) σ J X ∈ V v})).toReal /
        (lam v (V v)).toReal - (m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) (sA b v a)).toReal =
        ((coordW (Fv F v) b (lam v) 1 M (sA b v a ∩ {X | qF (Fv F v) σ J X ∈ V v})).toReal -
          (m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) (sA b v a)).toReal * (lam v (V v)).toReal) /
          (lam v (V v)).toReal := by
      have := (hLv v).ne'
      field_simp
    show |_ - _| ≤ δ
    rw [h2, abs_div, abs_of_pos (hLv v), div_le_iff₀ (hLv v)]
    exact h1)
  rw [Finset.prod_div_distrib, ← hI, ← hLf] at hcl
  have h3 : |(∫⁻ y in box S V, ENNReal.ofReal (D y) ∂lf).toReal / (lf (box S V)).toReal -
      D 0| ≤ ε / 3 := by
    have h4 : (∫⁻ y in box S V, ENNReal.ofReal (D y) ∂lf).toReal / (lf (box S V)).toReal -
        D 0 = ((∫⁻ y in box S V, ENNReal.ofReal (D y) ∂lf).toReal -
          D 0 * (lf (box S V)).toReal) / (lf (box S V)).toReal := by
      have := hLfpos.ne'
      field_simp
    rw [h4, abs_div, abs_of_pos hLfpos, div_le_iff₀ hLfpos]
    exact havg
  change dist (∏ v ∈ S, (m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) (sA b v a)).toReal) _ < ε
  rw [Real.dist_eq]
  have h5 := abs_le.1 hcl
  have h6 := abs_le.1 h3
  rw [abs_lt]
  constructor <;> linarith

theorem ofF_mem_framesE_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    {d : ℕ} (b : Module.Basis (Fin d) F E) (B : Matrix (Fin M × Fin d) (Fin M × Fin d) F)
    (hB : ∀ x : Fin M → E, Algebra.trace F E (hE σ J x x) = (fun p : Fin M × Fin d => b.repr (x p.1) p.2) ⬝ᵥ (B *ᵥ fun p : Fin M × Fin d => b.repr (x p.1) p.2))
    (x : Fin M × Fin d → F) :
    ofF b x ∈ framesE σ J (0 : Matrix (Fin 1) (Fin 1) E) ↔
      x ≠ 0 ∧ (1 / 2 : F) * (x ⬝ᵥ (B *ᵥ x)) = 0 := by
  obtain ⟨-, h2, h3⟩ := GlobalTheory.T.coordinate_bijection_trace_form F E σ hσ M J hJ d b
  have hg : gramE σ J (ofF b x) = (0 : Matrix (Fin 1) (Fin 1) E) ↔
      (1 / 2 : F) * (x ⬝ᵥ (B *ᵥ x)) = 0 := by
    rw [← h3 B hB 0 x]
    simp only [map_zero]
    rfl
  have hl : LinearIndependent E (ofF b x : Fin 1 → Fin M → E) ↔ x ≠ 0 := by
    rw [linearIndependent_unique_iff, ← h2 x]
    constructor
    · intro h h0
      exact h (congrFun h0 _)
    · intro h h0
      exact h (funext fun i => by rw [Subsingleton.elim i default]; exact h0)
  exact and_congr hl hg

theorem lintegral_thetaMeas_gauss_frames : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (B : Matrix (Fin M × Fin d) (Fin M × Fin d) F), (∀ x : Fin M → E, Algebra.trace F E (hE σ J x x) = (fun p : Fin M × Fin d => b.repr (x p.1) p.2) ⬝ᵥ (B *ᵥ fun p : Fin M × Fin d => b.repr (x p.1) p.2)) → ∀ (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), IsHomeomorph e → (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) → ∀ (Pm : InfinitePlace F → Matrix (Fin M × Fin d) (Fin M × Fin d) ℝ) (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (a : ℕ), 0 < a → ∫⁻ X in {X | ∀ v, projV v (projFin X) ∈ {X : (Fin 1 → Fin M → Fv F v ⊗[F] E) | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v}}, ENNReal.ofReal (gaussQ e b Pm (projInf X)) ∂(thetaMeas σ J μ 𝓕 (framesE σ J (0 : Matrix (Fin 1) (Fin 1) E))) = ∫⁻ ω, ∑' x : {x : Fin M × Fin d → F // x ≠ 0 ∧ (1 / 2 : F) * (x ⬝ᵥ (B *ᵥ x)) = 0}, Set.indicator {x : Fin M × Fin d → F | ∀ i v, ((a : Af F) * (gfin σ J b ω *ᵥ fun j => algebraMap F (Af F) (x j)) i) v ∈ v.adicCompletionIntegers F} (fun x => ENNReal.ofReal (Real.exp (-Real.pi * ∑ w, (ginf e σ J b ω w *ᵥ fun j => ρ w (x j)) ⬝ᵥ (Pm w *ᵥ (ginf e σ J b ω w *ᵥ fun j => ρ w (x j)))))) x.1 ∂(prH μ 𝓕) := by
  intro F E _ _ _ _ _ σ hσ M J hJ d b B hB ρ e hom hρ Pm μ 𝓕 hμ h𝓕 a ha
  obtain ⟨⟨h1, h2, h3⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  obtain ⟨hR, -, -, -, -, -, -, hBor, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (AF F)
  haveI := hBor 1 M
  have hA := GlobalTheory.T.measurable_finite_level_lattice_set F E σ hσ d M b a
  have hproj : Continuous (projInf : (Fin 1 → Fin M → AF F ⊗[F] E) → _) :=
    (GlobalTheory.T.adelic_tuple_projections F E σ hσ d b 1 M).1
  have hG : Continuous fun X : Fin 1 → Fin M → AF F ⊗[F] E =>
      ENNReal.ofReal (gaussQ e b Pm (projInf X)) :=
    ENNReal.continuous_ofReal.comp
      ((GlobalTheory.CompanionTheory.SW.BB.ThetaGauss.continuous_gaussQ σ hσ b e hom Pm).comp hproj)
  rw [← lintegral_indicator hA]
  rw [GlobalTheory.T.theta_integral_over_coordinates F E σ hσ M J hJ d b μ 𝓕 hμ h𝓕
    {x | x ≠ 0 ∧ (1 / 2 : F) * (x ⬝ᵥ (B *ᵥ x)) = 0}
    (framesE σ J (0 : Matrix (Fin 1) (Fin 1) E))
    (fun x => ofF_mem_framesE_zero σ hσ J hJ b B hB x) _
    (hG.measurable.indicator hA)]
  refine lintegral_congr fun ω => tsum_congr fun x => ?_
  obtain ⟨hinf, hfin⟩ := GlobalTheory.T.infinite_component_coordinates_action F E σ hσ M J hJ d b ρ e hρ ω x.1
  have hmem := GlobalTheory.T.finite_adelic_lattice_membership_iff F E d M b a (projFin (actW (AF F) σ J ω⁻¹ (ratTup (AF F) (ofF b x.1))))
  rw [hfin] at hmem
  have hgauss : gaussQ e b Pm (projInf (actW (AF F) σ J ω⁻¹ (ratTup (AF F) (ofF b x.1)))) =
      Real.exp (-Real.pi * ∑ w, (ginf e σ J b ω w *ᵥ fun j => ρ w (x.1 j)) ⬝ᵥ
        (Pm w *ᵥ (ginf e σ J b ω w *ᵥ fun j => ρ w (x.1 j)))) := by
    simp only [gaussQ, hinf]
  by_cases hx : ∀ i v, ((a : Af F) * (gfin σ J b ω *ᵥ fun j => algebraMap F (Af F) (x.1 j)) i) v ∈
      v.adicCompletionIntegers F
  · rw [Set.indicator_of_mem (by exact hmem.2 hx), Set.indicator_of_mem (by exact hx), hgauss]
  · rw [Set.indicator_of_notMem, Set.indicator_of_notMem]
    all_goals first | exact hx | exact fun h => hx (hmem.1 h)

theorem estimate_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (h₀ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b), ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (minf : HermR (Ainf F) σ 1 → Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)), IsGramFibFree (Ainf F) σ J 1 (coordW (Ainf F) b laminf 1 M) (coordHerm (Ainf F) σ b laminf 1) minf → ∀ (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), (∀ v, IsGramFibFree (Fv F v) σ J 1 (coordW (Fv F v) b (lam v) 1 M) (coordHerm (Fv F v) σ b (lam v) 1) (m v)) → ∃ (φ : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ) (C : ℝ), Continuous φ ∧ (∀ X, 0 < φ X) ∧ ∫⁻ X, ENNReal.ofReal (φ X) ∂(minf (hermOf (Ainf F) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀)) < ⊤ ∧ ∀ a : ℕ, 0 < a → ∃ I : ℝ≥0, ∫⁻ X in {X | ∀ v, projV v (projFin X) ∈ {X : Fin 1 → Fin M → Fv F v ⊗[F] E | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v}}, ENNReal.ofReal (φ (projInf X)) ∂(thetaMeas σ J μ 𝓕 (framesE σ J (0 : Matrix (Fin 1) (Fin 1) E))) = (I : ℝ≥0∞) ∧ |(I : ℝ) - (∫⁻ X, ENNReal.ofReal (φ X) ∂(minf (hermOf (Ainf F) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀))).toReal * ∏' v, (m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) {X : Fin 1 → Fin M → Fv F v ⊗[F] E | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v}).toReal| ≤ C * (a : ℝ) ^ (Module.finrank ℚ F * M) := by
  intro F E _ _ _ _ _ σ hCM M J hJ hM h₀ d b laminf lam hinf hlam μ 𝓕 hμ h𝓕 minf hminf m hm
  obtain ⟨hF, hEc, hfin, hconj⟩ := id hCM
  have hd : d = 2 := by
    have h := Module.finrank_eq_card_basis b
    simpa [hfin] using h.symm
  obtain ⟨B, hBs, hBd, hBE, hBR⟩ := GlobalTheory.T.exists_trace_form_gram_matrix_in_basis F E σ hCM M J hJ d b
  obtain ⟨ρ, e, hρ, he, heρ, hen, hem⟩ := GlobalTheory.T.infinite_adele_haar_map_eq_scaled_volume F hF
  have hP : ∀ w, ∃ P : Matrix (Fin M × Fin d) (Fin M × Fin d) ℝ,
      P.PosDef ∧ P * (B.map (ρ w))⁻¹ * P = B.map (ρ w) := by
    intro w
    refine GlobalTheory.T.symmetric_invertible_exists_posdef_congruence _ _ ?_ ?_
    · exact hBs.map _
    · have h := RingHom.map_det (ρ w) B
      rw [RingHom.mapMatrix_apply] at h
      rw [← h]
      exact (map_ne_zero _).2 hBd
  choose Pm hPd hPm using hP
  obtain ⟨lf, hlf, hlf1⟩ := GlobalTheory.T.exists_finite_adele_haar_normalized F
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  haveI := GlobalTheory.T.quotient_probability_measure F E σ hCM M J hJ μ 𝓕 hμ h𝓕
  obtain ⟨hgi, hgf⟩ := GlobalTheory.T.gram_coordinates_measurable F E σ hCM M J hJ d b e he
  obtain ⟨hii, hif⟩ := GlobalTheory.T.trace_form_invariance_under_unitary F E σ M J d b B ρ e heρ
    (fun h => ((hBR (AF F)).2 h _ (fun p q => rfl)).1)
  have hcard : Fintype.card (Fin M × Fin d) = 2 * M := by simp [hd, mul_comm]
  obtain ⟨C, Df, Dinf, hDf, ⟨hDc, hD0, hDd⟩, hmain⟩ :=
    GlobalTheory.T.gaussian_fourier_self_dual_adelic F hF (Fin M × Fin d) M hcard hM B hBs hBd ρ hρ Pm hPd hPm lf hlf hlf1
      (HA (AF F) σ J) (prH μ 𝓕) (ginf e σ J b) (gfin σ J b) hgi hgf hii hif
      (fun N hN => GlobalTheory.T.average_rational_vector_count_ball_bound F E σ hCM M J hJ hM d b ρ e he heρ hen μ 𝓕 hμ h𝓕 N hN)
  obtain ⟨hgc, hgr⟩ := GlobalTheory.T.gaussian_continuous_rapid_decay F E σ hCM M d b e he hen Pm
  have hinfint : ∫⁻ X, ENNReal.ofReal (gaussQ e b Pm X)
      ∂(minf (hermOf (Ainf F) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀)) =
      ENNReal.ofReal ((Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (2 * M - 1) * Dinf (fun _ => 0)) := by
    obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hF
    haveI : BorelSpace (Ainf F) := ⟨rfl⟩
    obtain ⟨hK1, hK2, hK3⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hCM (Ainf F) d b laminf hinf.1
    obtain ⟨t1, t2, t3, t4, t5, t6, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (Ainf F)
    have hDcont : Continuous fun S : HermR (Ainf F) σ 1 =>
        (Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (2 * M - 1) * Dinf (e (algebraMap F (Ainf F) (1 / 2) *
          Algebra.trace (Ainf F) (Ainf F ⊗[F] E) ((S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) 0 0))) := by
      refine continuous_const.mul (hDc.comp (he.continuous.comp (continuous_const.mul (t6.comp ?_))))
      exact (continuous_apply_apply 0 0).comp continuous_subtype_val
    have h := GlobalTheory.T.archimedean_volume_rank_one_isotropic F E σ hCM M J hJ hM h₀ d b (coordW (Ainf F) b laminf 1 M)
      (coordHerm (Ainf F) σ b laminf 1) minf (hK2 1 M) (hK3 1) hminf (gaussQ e b Pm) hgc
      (fun X => (Real.exp_pos _).le) (hgr hPd) _ hDcont
      (GlobalTheory.T.archimedean_local_density_formula F E σ hCM M J hJ hM d b B (hBR (Ainf F)).1 ρ e he heρ Pm laminf hinf.1
        (hem laminf hinf) Dinf hDc hD0 hDd)
    have hz : ((hermOf (Ainf F) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀ : HermR (Ainf F) σ 1) :
        Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) 0 0 = 0 := by
      simp [hermOf, inclR]
    rw [h, hz, map_zero, mul_zero, map_zero]
    rfl
  have hκ : 0 ≤ (Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (2 * M - 1) * Dinf (fun _ => 0) :=
    mul_nonneg (pow_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _)) _) (hD0 _)
  refine ⟨gaussQ e b Pm, C, hgc, fun X => Real.exp_pos _, ?_, ?_⟩
  · rw [hinfint]; exact ENNReal.ofReal_lt_top
  · intro a ha
    obtain ⟨I, hI, hIb⟩ := hmain a ha
    obtain ⟨c1, c2, c3⟩ := hDf a ha
    have hprod := hasProd_free_mass_zero F E σ hCM M J hJ hM h₀ d b lam hlam m hm lf hlf hlf1 a ha
      (Df a) c1 c2 (fun U hU => by
        rw [GlobalTheory.T.finite_adelic_trace_form_coordinates F E σ hCM M J hJ d b B (hBR (Af F)).1 lf hlf a U]
        exact c3 U hU)
    refine ⟨I, ?_, ?_⟩
    · rw [lintegral_thetaMeas_gauss_frames F E σ hCM M J hJ d b B hBE ρ e he heρ Pm μ 𝓕 hμ h𝓕 a ha]
      exact hI
    · rw [hinfint, hprod.tprod_eq, ENNReal.toReal_ofReal hκ]
      convert hIb using 3
      ring

end GlobalTheory.CompanionTheory.WeilSiegel.Free.EstZero
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalVolumeRankOneNormalisedStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.global_volume_rank_one_normalised : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (h₀ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b), ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (minf : HermR (Ainf F) σ 1 → Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)), IsGramFibFree (Ainf F) σ J 1 (coordW (Ainf F) b laminf 1 M) (coordHerm (Ainf F) σ b laminf 1) minf → ∀ (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), (∀ v, IsGramFibFree (Fv F v) σ J 1 (coordW (Fv F v) b (lam v) 1 M) (coordHerm (Fv F v) σ b (lam v) 1) (m v)) → ∃ (φ : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ) (C : ℝ), Continuous φ ∧ (∀ X, 0 < φ X) ∧ ∫⁻ X, ENNReal.ofReal (φ X) ∂(minf (hermOf (Ainf F) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀)) < ⊤ ∧ ∀ a : ℕ, 0 < a → ∃ I : ℝ≥0, ∫⁻ X in {X | ∀ v, projV v (projFin X) ∈ {X : Fin 1 → Fin M → Fv F v ⊗[F] E | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v}}, ENNReal.ofReal (φ (projInf X)) ∂(thetaMeas σ J μ 𝓕 (framesE σ J (0 : Matrix (Fin 1) (Fin 1) E))) = (I : ℝ≥0∞) ∧ |(I : ℝ) - (∫⁻ X, ENNReal.ofReal (φ X) ∂(minf (hermOf (Ainf F) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀))).toReal * ∏' v, (m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) {X : Fin 1 → Fin M → Fv F v ⊗[F] E | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v}).toReal| ≤ C * (a : ℝ) ^ (Module.finrank ℚ F * M) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Free.EstZero.estimate_zero | exact GlobalTheory.CompanionTheory.WeilSiegel.Free.EstZero.estimate_zero | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Free.EstZero.estimate_zero <;> assumption)
end
