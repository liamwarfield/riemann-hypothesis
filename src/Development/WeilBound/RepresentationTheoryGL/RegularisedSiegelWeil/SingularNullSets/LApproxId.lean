module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LApproxIdS
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LIdemEx
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumMeas
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordinateFormSymmetricNondegenerate

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LApproxIdC
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LApproxId

open scoped RestrictedProduct

theorem rp_nhds {ι : Type} {R : ι → Type} [∀ i, TopologicalSpace (R i)] {A : ∀ i, Set (R i)}
    (hA : ∀ i, IsOpen (A i)) (x : ∀ i, A i) (W : Set (Πʳ i, [R i, A i]))
    (hW : W ∈ 𝓝 (RestrictedProduct.structureMap R A cofinite x)) :
    ∃ V : ∀ i, Set (R i), (∀ i, V i ∈ 𝓝 (x i : R i)) ∧ ∀ z : Πʳ i, [R i, A i], (∀ i, z i ∈ V i) → z ∈ W := by
  rw [RestrictedProduct.nhds_eq_map_structureMap hA, Filter.mem_map, nhds_pi, Filter.mem_pi] at hW
  obtain ⟨I, -, t, ht, hIt⟩ := hW
  have ht' : ∀ i, ∃ u ∈ 𝓝 (x i : R i), Subtype.val ⁻¹' u ⊆ t i := fun i => mem_nhds_subtype _ _ _ |>.1 (ht i)
  choose u hu hut using ht'
  refine ⟨fun i => u i ∩ A i, fun i => Filter.inter_mem (hu i) ((hA i).mem_nhds (x i).2), fun z hz => ?_⟩
  let y : ∀ i, A i := fun i => ⟨z i, (hz i).2⟩
  have hyz : RestrictedProduct.structureMap R A cofinite y = z := Subtype.ext rfl
  rw [← hyz]
  exact hIt fun i _ => hut i (hz i).1

theorem af_nhds {F : Type} [Field F] [NumberField F] (W : Set (Af F)) (hW : W ∈ 𝓝 (0 : Af F)) :
    ∃ V : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v), (∀ v, V v ∈ 𝓝 (0 : Fv F v)) ∧
      ∀ z : Af F, (∀ v, z v ∈ V v) → z ∈ W := by
  have hA : ∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := fun v => Valued.isOpen_valuationSubring _
  have h0 : RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite (fun _ => ⟨0, zero_mem _⟩) =
      (0 : Af F) := rfl
  rw [← h0] at hW
  exact rp_nhds hA _ W hW

theorem top1 {F : Type} [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F) (hε : IsIdF S ε)
    (A : ℕ → Set (Ainf F)) (U : ℕ → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v))
    (hA : Tendsto A atTop (𝓝 0).smallSets) (hU : ∀ v, Tendsto (fun k => U k v) atTop (𝓝 0).smallSets) :
    Tendsto (fun k => {a : AF F | ε * a = a ∧ fstA F a ∈ A k ∧ ∀ v ∈ S, (sndA F a) v ∈ U k v}) atTop
      (𝓝 (0 : AF F)).smallSets := by
  rw [Filter.tendsto_smallSets_iff]
  intro W hW
  obtain ⟨W1, hW1, W2, hW2, hsub⟩ := mem_nhds_prod_iff.1 (show W ∈ 𝓝 ((0, 0) : Ainf F × Af F) from hW)
  obtain ⟨V, hV, hVW⟩ := af_nhds W2 hW2
  have e1 := Filter.tendsto_smallSets_iff.1 hA W1 hW1
  have e2 : ∀ᶠ k in atTop, ∀ v ∈ S, U k v ⊆ V v :=
    (Filter.eventually_all_finset S).2 fun v _ => Filter.tendsto_smallSets_iff.1 (hU v) (V v) (hV v)
  filter_upwards [e1, e2] with k h1 h2
  rintro a ⟨hεa, haA, haU⟩
  apply hsub
  refine ⟨h1 haA, hVW (sndA F a) fun v => ?_⟩
  by_cases hv : v ∈ S
  · exact h2 v hv (haU v hv)
  · have h3 : sndA F a = sndA F ε * sndA F a := by rw [← map_mul, hεa]
    have h4 : (sndA F a) v = (sndA F ε) v * (sndA F a) v := congrArg (fun z : Af F => z v) h3
    rw [hε.2 v, if_neg hv, zero_mul] at h4
    rw [h4]
    exact mem_of_mem_nhds (hV v)

end PositivityTheory.Rg.Rsw.L.LApproxId

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LApproxIdB
section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Kdata
section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.AddMemIffOfZero
section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.FixMulKer
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LApproxId

variable {F : Type} [Field F] [NumberField F]

theorem fst_eq (x : AF F) : fstA F x = x.1 := rfl
theorem snd_eq (x : AF F) : sndA F x = x.2 := rfl

theorem idF_fst {S : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F} (hε : IsIdF S ε) : ε.1 = 1 := hε.1

open Classical in
theorem idF_snd {S : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F} (hε : IsIdF S ε) (v : HeightOneSpectrum (𝓞 F)) :
    ε.2 v = if v ∈ S then 1 else 0 := hε.2 v

theorem idF_mul {S : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F} (hε : IsIdF S ε) : ε * ε = ε := by
  classical
  refine Prod.ext ?_ (FiniteAdeleRing.ext _ fun v => ?_)
  · change ε.1 * ε.1 = ε.1
    rw [idF_fst hε, one_mul]
  · change ε.2 v * ε.2 v = ε.2 v
    rw [idF_snd hε v]
    split_ifs <;> simp

theorem ker_fst {S : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F} (hε : IsIdF S ε) {y : AF F} (hy : ε * y = 0) :
    y.1 = 0 := by
  have h : (ε * y).1 = 0 := by rw [hy]; rfl
  change ε.1 * y.1 = 0 at h
  rwa [idF_fst hε, one_mul] at h

theorem ker_snd {S : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F} (hε : IsIdF S ε) {y : AF F} (hy : ε * y = 0)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ S) : y.2 v = 0 := by
  classical
  have h : (ε * y).2 v = 0 := by rw [hy]; rfl
  change ε.2 v * y.2 v = 0 at h
  rwa [idF_snd hε v, if_pos hv, one_mul] at h

theorem fix_snd {S : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F} (hε : IsIdF S ε) {h : AF F} (hh : ε * h = h)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) : h.2 v = 0 := by
  classical
  have h' : (ε * h).2 v = h.2 v := by rw [hh]
  change ε.2 v * h.2 v = h.2 v at h'
  rw [idF_snd hε v, if_neg hv, zero_mul] at h'
  exact h'.symm

theorem fix_mul_ker {ε h y : AF F} (hε : ε * ε = ε) (hh : ε * h = h) (hy : ε * y = 0) : h * y = 0 := by
  calc h * y = (ε * h) * y := by rw [hh]
    _ = h * (ε * y) := by ring
    _ = 0 := by rw [hy, mul_zero]

end PositivityTheory.Rg.Rsw.L.LApproxId

end
end

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LApproxId

open GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef (testT boxA fouA intF)

variable {F : Type} [Field F] [NumberField F]

theorem add_mem_iff_of_zero {X : Type} [AddCommGroup X] {P : Set X} (h0 : (0 : X) ∈ P) {a b : X} (hab : a = 0 ∨ b = 0) :
    a + b ∈ P ↔ a ∈ P ∧ b ∈ P := by
  rcases hab with h | h <;> subst h <;> simp [h0]

theorem box_split {S S' : Finset (HeightOneSpectrum (𝓞 F))} (hSS : S ⊆ S') {ε : AF F} (hε : IsIdF S ε)
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (hU : ∀ v, (0 : Fv F v) ∈ U v) {h y : AF F} (hh : ε * h = h)
    (hy : ε * y = 0) : sndA F (h + y) ∈ boxA S' U ↔ sndA F h ∈ boxA S' U ∧ sndA F y ∈ boxA S' U := by
  have hz : ∀ v, h.2 v = 0 ∨ y.2 v = 0 := fun v => by
    by_cases hv : v ∈ S
    · exact Or.inr (ker_snd hε hy hv)
    · exact Or.inl (fix_snd hε hh hv)
  have hadd : ∀ v, (sndA F (h + y)) v = h.2 v + y.2 v := fun v => rfl
  simp only [boxA, Set.mem_ofPred_eq, hadd]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨fun v hv => ((add_mem_iff_of_zero (hU v) (hz v)).1 (h1 v hv)).1,
      fun v hv => ((add_mem_iff_of_zero (zero_mem _) (hz v)).1 (h2 v hv)).1⟩,
      ⟨fun v hv => ((add_mem_iff_of_zero (hU v) (hz v)).1 (h1 v hv)).2,
      fun v hv => ((add_mem_iff_of_zero (zero_mem _) (hz v)).1 (h2 v hv)).2⟩⟩
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    exact ⟨fun v hv => (add_mem_iff_of_zero (hU v) (hz v)).2 ⟨h1 v hv, h3 v hv⟩,
      fun v hv => (add_mem_iff_of_zero (zero_mem _) (hz v)).2 ⟨h2 v hv, h4 v hv⟩⟩

def tR (ρ : Ainf F → ℝ) (S : Finset (HeightOneSpectrum (𝓞 F))) (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v))
    (y : AF F) : ℝ :=
  ρ (fstA F y) * (boxA S U).indicator (fun _ => (1 : ℝ)) (sndA F y)

theorem testT_eq (ρ : Ainf F → ℝ) (S : Finset (HeightOneSpectrum (𝓞 F))) (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v))
    (y : AF F) : testT ρ S U y = ((tR ρ S U y : ℝ) : ℂ) := by
  simp only [testT, tR, Set.indicator]
  split_ifs <;> simp

theorem tR_nonneg {ρ : Ainf F → ℝ} (hρ : ∀ y, 0 ≤ ρ y) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (y : AF F) : 0 ≤ tR ρ S U y :=
  mul_nonneg (hρ _) (Set.indicator_nonneg (fun _ _ => zero_le_one) _)

def bR (S : Finset (HeightOneSpectrum (𝓞 F))) (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (y : AF F) : ℝ :=
  (boxA S U).indicator (fun _ => (1 : ℝ)) (sndA F y)

theorem tR_split {S S' : Finset (HeightOneSpectrum (𝓞 F))} (hSS : S ⊆ S') {ε : AF F} (hε : IsIdF S ε) (ρ : Ainf F → ℝ)
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (hU : ∀ v, (0 : Fv F v) ∈ U v) {h y : AF F} (hh : ε * h = h)
    (hy : ε * y = 0) : tR ρ S' U (h + y) = tR ρ S' U h * bR S' U y := by
  have hf : fstA F (h + y) = fstA F h := by
    rw [map_add (f := _), fst_eq y, ker_fst hε hy, add_zero]
  have hb := box_split hSS hε U hU hh hy
  unfold tR bR
  rw [hf]
  by_cases h1 : sndA F h ∈ boxA S' U <;> by_cases h2 : sndA F y ∈ boxA S' U
  · rw [Set.indicator_of_mem (hb.2 ⟨h1, h2⟩), Set.indicator_of_mem h1, Set.indicator_of_mem h2]; ring
  · rw [Set.indicator_of_notMem (fun h' => h2 (hb.1 h').2), Set.indicator_of_notMem h2]; ring
  · rw [Set.indicator_of_notMem (fun h' => h1 (hb.1 h').1), Set.indicator_of_notMem h1]; ring
  · rw [Set.indicator_of_notMem (fun h' => h1 (hb.1 h').1), Set.indicator_of_notMem h1]; ring

end PositivityTheory.Rg.Rsw.L.LApproxId

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.KappaReal
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LApproxId

theorem kappa_real {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ) {ε : AF F}
    (ν : Measure (fixE ε)) [SFinite ν] (τ : fixE ε → ℝ) (hτ0 : ∀ h, 0 ≤ τ h) (hτI : Integrable τ ν)
    (hτpos : 0 < ∫ h, τ h ∂ν) (M : ℝ) (hτM : ∀ h, τ h ≤ M) (A : fixE ε → ℂ)
    (hA : ∀ s, A s = ∫ h, (τ h : ℂ) * ψ (h.1 * s.1) ∂ν) (hAI : Integrable A ν) (κ : ℂ)
    (hκ : ∀ s : fixE ε, ∫ h, A h * ψ (h.1 * s.1) ∂ν = κ * τ (-s)) :
    κ.im = 0 ∧ 0 ≤ κ.re := by
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  haveI : SecondCountableTopology (fixE ε) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : OpensMeasurableSpace (fixE ε × fixE ε) := inferInstance
  have hψn : ∀ x, ‖ψ x‖ = 1 := hψ.2.1
  have hconj : ∀ x, (starRingEnd ℂ) (ψ x) = ψ (-x) := by
    intro x
    rw [AddChar.map_neg_eq_inv, Complex.inv_def, Complex.normSq_eq_norm_sq, hψn x]
    simp
  have hτC : Integrable (fun h => (τ h : ℂ)) ν := hτI.ofReal

  have hA' : ∀ h : fixE ε, (starRingEnd ℂ) (A h) = ∫ h', (τ h' : ℂ) * ψ (h.1 * (-h').1) ∂ν := by
    intro h
    rw [hA, ← integral_conj]
    congr 1
    funext h'
    rw [map_mul, Complex.conj_ofReal, hconj]
    congr 2
    change -(h'.1 * h.1) = h.1 * -h'.1
    ring

  set f : fixE ε → fixE ε → ℂ := fun h h' => A h * ((τ h' : ℂ) * ψ (h.1 * (-h').1)) with hf
  have hcont : Continuous fun z : fixE ε × fixE ε => ψ (z.1.1 * (-z.2).1) :=
    hψ.1.comp ((continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp
      (continuous_neg.comp continuous_snd)))
  have hfI : Integrable (Function.uncurry f) (ν.prod ν) := by
    refine Integrable.mono' (hAI.norm.mul_prod hτI) ?_ (Filter.Eventually.of_forall fun z => ?_)
    · exact hAI.aestronglyMeasurable.comp_fst.mul (hτC.aestronglyMeasurable.comp_snd.mul hcont.aestronglyMeasurable)
    · simp only [Function.uncurry, hf, norm_mul, hψn, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hτ0 _)]
      exact le_rfl
  have hsw := integral_integral_swap hfI
  have hL : ∫ h, A h * (starRingEnd ℂ) (A h) ∂ν = ∫ h, ∫ h', f h h' ∂ν ∂ν := by
    congr 1
    funext h
    rw [hA', ← integral_const_mul]
  have hR : ∫ h', ∫ h, f h h' ∂ν ∂ν = κ * ∫ h', ((τ h' * τ h' : ℝ) : ℂ) ∂ν := by
    rw [← integral_const_mul]
    congr 1
    funext h'
    have h1 : ∫ h, f h h' ∂ν = (τ h' : ℂ) * ∫ h, A h * ψ (h.1 * (-h').1) ∂ν := by
      rw [← integral_const_mul]
      congr 1
      funext h
      dsimp [f]
      ring
    rw [h1, hκ, neg_neg]
    push_cast
    ring

  have hLr : ∫ h, A h * (starRingEnd ℂ) (A h) ∂ν = ((∫ h, Complex.normSq (A h) ∂ν : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1
    funext h
    exact Complex.mul_conj _
  have hL0 : 0 ≤ ∫ h, Complex.normSq (A h) ∂ν := integral_nonneg fun h => Complex.normSq_nonneg _
  have hQI : Integrable (fun h => τ h * τ h) ν := by
    refine Integrable.mono' (hτI.const_mul M) (hτI.aestronglyMeasurable.mul hτI.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun h => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hτ0 h) (hτ0 h)), mul_comm M]
    exact mul_le_mul_of_nonneg_left (hτM h) (hτ0 h)
  have hQ0 : 0 < ∫ h, τ h * τ h ∂ν := by
    refine lt_of_le_of_ne (integral_nonneg fun h => mul_nonneg (hτ0 h) (hτ0 h)) fun h0 => ?_
    have hz := (integral_eq_zero_iff_of_nonneg (fun h => mul_nonneg (hτ0 h) (hτ0 h)) hQI).1 h0.symm
    have hz' : τ =ᵐ[ν] 0 := hz.mono fun h hh => by
      simpa using (mul_self_eq_zero.1 hh)
    rw [integral_congr_ae hz'] at hτpos
    simp at hτpos
  have hmain : ((∫ h, Complex.normSq (A h) ∂ν : ℝ) : ℂ) = κ * ((∫ h, τ h * τ h ∂ν : ℝ) : ℂ) := by
    rw [← hLr, hL, hsw, hR, integral_complex_ofReal]
  have hκe : κ = (((∫ h, Complex.normSq (A h) ∂ν) / ∫ h, τ h * τ h ∂ν : ℝ) : ℂ) := by
    have hq : ((∫ h, τ h * τ h ∂ν : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hQ0.ne'
    rw [Complex.ofReal_div, hmain, mul_div_assoc, div_self hq, mul_one]
  rw [hκe, Complex.ofReal_im, Complex.ofReal_re]
  exact ⟨rfl, div_nonneg hL0 hQ0.le⟩

end PositivityTheory.Rg.Rsw.L.LApproxId

end
end

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LApproxId

open GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef (testT boxA fouA intF)

variable {F : Type} [Field F] [NumberField F]

theorem memH {ε : AF F} (h : fixE ε) : ε * h.1 = h.1 := h.2

theorem memY {ε : AF F} (y : (AddMonoidHom.mulLeft ε).ker) : ε * y.1 = 0 := y.2

theorem kdata (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ) {S S' : Finset (HeightOneSpectrum (𝓞 F))} (hSS : S ⊆ S')
    {ε : AF F} (hε : IsIdF S ε) (db : Measure (AF F)) (ν : Measure (fixE ε)) [SFinite ν]
    (νY : Measure (AddMonoidHom.mulLeft ε).ker) [SFinite νY] (c : ℝ≥0) (hc : 0 < c)
    (hdec : ∀ f : AF F → ℂ,
      (Integrable f db ↔ Integrable (fun z : fixE ε × (AddMonoidHom.mulLeft ε).ker => f (z.1.1 + z.2.1)) (ν.prod νY)) ∧
      ∫ x, f x ∂db = (c : ℂ) * ∫ z : fixE ε × (AddMonoidHom.mulLeft ε).ker, f (z.1.1 + z.2.1) ∂(ν.prod νY))
    (ρ : Ainf F → ℝ) (hρc : Continuous ρ) (hρs : HasCompactSupport ρ) (hρ0 : ∀ y, 0 ≤ ρ y)
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (hU0 : ∀ v, (0 : Fv F v) ∈ U v)
    (hI : Integrable (fouA ψ db (testT ρ S' U)) db)
    (hinv : ∀ z, ∫ b, fouA ψ db (testT ρ S' U) b * ψ (b * z) ∂db = testT ρ S' U (-z))
    (hne : ∫ y, testT ρ S' U y ∂db ≠ 0) :
    ∃ (g : fixE ε → ℂ) (Gc : ℝ), 0 ≤ Gc ∧ Integrable g ν ∧ (∀ h, ‖g h‖ ≤ 1) ∧
      (∀ s, ∫ h, g h * ψ (h.1 * s) ∂ν = ((Gc * tR ρ S' U (-(ε * s)) : ℝ) : ℂ)) ∧
      ∀ h : fixE ε, g h = fouA ψ db (testT ρ S' U) h.1 / ∫ y, testT ρ S' U y ∂db := by
  classical
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  have hεε := idF_mul hε
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  set τH : fixE ε → ℂ := fun h => ((tR ρ S' U h.1 : ℝ) : ℂ) with hτH
  set τY : (AddMonoidHom.mulLeft ε).ker → ℂ := fun y => ((bR S' U y.1 : ℝ) : ℂ) with hτY
  set A : AF F → ℂ := fun s => ∫ h, τH h * ψ (h.1 * s) ∂ν with hA
  set Bf : AF F → ℂ := fun s => ∫ y, τY y * ψ (y.1 * s) ∂νY with hBf
  have hsplit : ∀ (h : fixE ε) (y : (AddMonoidHom.mulLeft ε).ker), testT ρ S' U (h.1 + y.1) = τH h * τY y := by
    intro h y
    rw [testT_eq, tR_split hSS hε ρ U hU0 (memH h) (memY y)]
    push_cast
    rfl
  have hpm : ∀ (h h0 : fixE ε) (y y0 : (AddMonoidHom.mulLeft ε).ker),
      (h.1 + y.1) * (h0.1 + y0.1) = h.1 * h0.1 + y.1 * y0.1 := by
    intro h h0 y y0
    have h1 : h.1 * y0.1 = 0 := fix_mul_ker hεε (memH h) (memY y0)
    have h2 : y.1 * h0.1 = 0 := by rw [mul_comm]; exact fix_mul_ker hεε (memH h0) (memY y)
    rw [add_mul, mul_add, mul_add, h1, h2, add_zero, zero_add]
  have hfou : ∀ (h0 : fixE ε) (y0 : (AddMonoidHom.mulLeft ε).ker),
      fouA ψ db (testT ρ S' U) (h0.1 + y0.1) = (c : ℂ) * (A h0.1 * Bf y0.1) := by
    intro h0 y0
    simp only [fouA]
    rw [(hdec _).2]
    congr 1
    rw [← integral_prod_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [hsplit, hpm, AddChar.map_add_eq_mul]
    ring
  have hint : ∫ y, testT ρ S' U y ∂db = (c : ℂ) * ((∫ h, τH h ∂ν) * ∫ y, τY y ∂νY) := by
    rw [(hdec _).2, ← integral_prod_mul]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => hsplit z.1 z.2)
  set IH := ∫ h, τH h ∂ν with hIH
  set IY := ∫ y, τY y ∂νY with hIY
  have hIH0 : IH ≠ 0 := fun h0 => hne (by rw [hint, h0, zero_mul, mul_zero])
  have hIY0 : IY ≠ 0 := fun h0 => hne (by rw [hint, h0, mul_zero, mul_zero])
  have hτHI : Integrable τH ν := by
    by_contra hn
    exact hIH0 (integral_undef hn)
  have hτR : Integrable (fun h : fixE ε => tR ρ S' U h.1) ν := by
    have := hτHI.norm
    refine this.congr (Filter.Eventually.of_forall fun h => ?_)
    simp only [hτH, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (tR_nonneg hρ0 S' U _)
  set IHr := ∫ h, tR ρ S' U h.1 ∂ν with hIHr
  have hIHc : IH = (IHr : ℂ) := integral_ofReal
  have hIHr0 : 0 < IHr := by
    refine lt_of_le_of_ne (integral_nonneg fun h => tR_nonneg hρ0 S' U _) fun h0 => hIH0 ?_
    rw [hIHc, ← h0, Complex.ofReal_zero]
  have hA0 : A 0 = IH := by
    simp only [hA, mul_zero, AddChar.map_zero_eq_one, mul_one]
    exact hIH.symm
  have hB0 : Bf 0 = IY := by
    simp only [hBf, mul_zero, AddChar.map_zero_eq_one, mul_one]
    exact hIY.symm
  have hψn : ∀ x, ‖ψ x‖ = 1 := hψ.2.1

  have hAc : Continuous A := by
    refine continuous_of_dominated (bound := fun h => ‖τH h‖) (fun s => ?_) (fun s => ?_) hτHI.norm ?_
    · exact hτHI.aestronglyMeasurable.mul
        (hψ.1.comp (continuous_subtype_val.mul continuous_const)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun h => by rw [norm_mul, hψn, mul_one]
    · exact Filter.Eventually.of_forall fun h => continuous_const.mul (hψ.1.comp (continuous_const.mul continuous_id))

  set IB := ∫ y, Bf y.1 ∂νY with hIB
  have hinvH : ∀ s, ε * s = s →
      ((tR ρ S' U (-s) : ℝ) : ℂ) = (c : ℂ) ^ 2 * IB * ∫ h, A h.1 * ψ (h.1 * s) ∂ν := by
    intro s hs
    have h1 := hinv s
    rw [(hdec _).2, testT_eq] at h1
    have h2 : ∀ z : fixE ε × (AddMonoidHom.mulLeft ε).ker,
        fouA ψ db (testT ρ S' U) (z.1.1 + z.2.1) * ψ ((z.1.1 + z.2.1) * s) =
          ((c : ℂ) * (A z.1.1 * ψ (z.1.1 * s))) * Bf z.2.1 := by
      intro z
      have hz : z.2.1 * s = 0 := by rw [mul_comm]; exact fix_mul_ker hεε hs (memY z.2)
      rw [hfou, add_mul, hz, add_zero]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall h2),
      integral_prod_mul (fun h : fixE ε => (c : ℂ) * (A h.1 * ψ (h.1 * s))) (fun y : (AddMonoidHom.mulLeft ε).ker => Bf y.1),
      integral_const_mul] at h1
    rw [← h1]
    ring

  obtain ⟨h₀, hh₀⟩ : ∃ h₀ : fixE ε, tR ρ S' U h₀.1 ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply hIHr0.ne'
    rw [hIHr]
    simp [hn]
  have hIB0 : IB ≠ 0 := by
    intro h0
    have h1 := hinvH (-h₀.1) (by rw [mul_neg, memH h₀])
    rw [neg_neg, h0, mul_zero, zero_mul] at h1
    exact hh₀ (by exact_mod_cast h1)
  set κ : ℂ := ((c : ℂ) ^ 2 * IB)⁻¹ with hκ
  have hcB : (c : ℂ) ^ 2 * IB ≠ 0 := mul_ne_zero (pow_ne_zero _ hc0) hIB0
  have hinvG : ∀ s, ∫ h, A h.1 * ψ (h.1 * s) ∂ν = κ * ((tR ρ S' U (-(ε * s)) : ℝ) : ℂ) := by
    intro s
    have hes : ε * (ε * s) = ε * s := by rw [← mul_assoc, hεε]
    have h1 : ∀ h : fixE ε, h.1 * s = h.1 * (ε * s) := fun h => by
      conv_lhs => rw [← memH h]
      ring
    simp only [h1]
    rw [hinvH _ hes, hκ, ← mul_assoc, inv_mul_cancel₀ hcB, one_mul]

  have hAI : Integrable (fun h : fixE ε => A h.1) ν := by
    have h1 := (hdec (fouA ψ db (testT ρ S' U))).1.1 hI
    have h2 : (fun z : fixE ε × (AddMonoidHom.mulLeft ε).ker => fouA ψ db (testT ρ S' U) (z.1.1 + z.2.1)) =
        fun z => (c : ℂ) * (A z.1.1 * Bf z.2.1) := funext fun z => hfou z.1 z.2
    rw [h2] at h1
    have hBI : Integrable (fun y : (AddMonoidHom.mulLeft ε).ker => Bf y.1) νY := by
      by_contra hn
      exact hIB0 (integral_undef hn)
    have hK : 0 < ∫ y, ‖Bf y.1‖ ∂νY :=
      lt_of_lt_of_le (norm_pos_iff.2 hIB0) (norm_integral_le_integral_norm _)
    have h3 := ((integrable_prod_iff h1.aestronglyMeasurable).1 h1).2
    have h4 : ∀ h : fixE ε, ∫ y, ‖(c : ℂ) * (A h.1 * Bf y.1)‖ ∂νY =
        (‖(c : ℂ)‖ * ∫ y, ‖Bf y.1‖ ∂νY) * ‖A h.1‖ := by
      intro h
      simp_rw [norm_mul]
      rw [integral_const_mul, integral_const_mul]
      ring
    simp only [h4] at h3
    have hcK : ‖(c : ℂ)‖ * ∫ y, ‖Bf y.1‖ ∂νY ≠ 0 := mul_ne_zero (norm_ne_zero_iff.2 hc0) hK.ne'
    have h5 : Integrable (fun h : fixE ε => ‖A h.1‖) ν := by
      refine (h3.const_mul (‖(c : ℂ)‖ * ∫ y, ‖Bf y.1‖ ∂νY)⁻¹).congr (Filter.Eventually.of_forall fun h => ?_)
      simp only
      rw [← mul_assoc, inv_mul_cancel₀ hcK, one_mul]
    exact (integrable_norm_iff (hAc.comp continuous_subtype_val).aestronglyMeasurable).1 h5

  obtain ⟨M, hM⟩ := hρc.bddAbove_range_of_hasCompactSupport hρs
  have hτM : ∀ h : fixE ε, tR ρ S' U h.1 ≤ M := by
    intro h
    have hρM : ρ (fstA F h.1) ≤ M := hM ⟨_, rfl⟩
    unfold tR
    by_cases hb : sndA F h.1 ∈ boxA S' U
    · rw [Set.indicator_of_mem hb, mul_one]; exact hρM
    · rw [Set.indicator_of_notMem hb, mul_zero]; exact (hρ0 _).trans hρM
  have hk := kappa_real ψ hψ ν (fun h => tR ρ S' U h.1) (fun h => tR_nonneg hρ0 S' U _) hτR hIHr0 M hτM
    (fun h => A h.1) (fun s => rfl) hAI κ (fun s => by
      have := hinvG s.1
      rw [memH s] at this
      exact this)
  have hAb : ∀ s, ‖A s‖ ≤ IHr := by
    intro s
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    rw [hIHr]
    congr 1
    funext h
    rw [norm_mul, hψn, mul_one, Complex.norm_real, Real.norm_of_nonneg (tR_nonneg hρ0 S' U _)]
  have hκr : κ = (κ.re : ℂ) := Complex.ext (by simp) (by simp [hk.1])
  have hIHr0' : (IHr : ℂ) ≠ 0 := by exact_mod_cast hIHr0.ne'
  refine ⟨fun h => A h.1 / IH, κ.re / IHr, div_nonneg hk.2 hIHr0.le, hAI.div_const _, fun h => ?_, fun s => ?_,
    fun h => ?_⟩
  · rw [norm_div, hIHc, Complex.norm_real, Real.norm_of_nonneg hIHr0.le]
    exact (div_le_one hIHr0).2 (hAb _)
  · simp_rw [div_mul_eq_mul_div]
    rw [integral_div, hinvG, hIHc, hκr]
    push_cast
    field_simp
    rw [Complex.ofReal_re]
    ring
  · have h1 := hfou h 0
    rw [ZeroMemClass.coe_zero, add_zero, hB0] at h1
    simp only
    rw [h1, hint]
    field_simp

end PositivityTheory.Rg.Rsw.L.LApproxId

end
end

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LApproxId

open GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef (testT boxA fouA intF)

theorem oneD : OneD := by
  intro F _ _ hF ψ hψ S ε hε ν hν
  classical
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  obtain ⟨db, hdb⟩ := GlobalTheory.T.exists_adelic_haar_covolume_one F
  obtain ⟨⟨laminf, hinf⟩, hlamex⟩ := GlobalTheory.T.exists_standard_local_measures F
  choose lam hlam using hlamex
  obtain ⟨S₁, hS₁⟩ := GlobalTheory.T.exists_local_approximate_identity F hF ψ hψ db hdb laminf lam hinf hlam
  obtain ⟨ρ, U, hρ, hρt, hU, hUt, hinv, hint, -, hlim⟩ := hS₁ (S ∪ S₁) Finset.subset_union_right
  haveI : db.IsAddHaarMeasure := hdb.1
  have hεε := idF_mul hε
  have hp : Continuous (AddMonoidHom.mulLeft ε) := continuous_const.mul continuous_id
  have hpp : ∀ x, AddMonoidHom.mulLeft ε (AddMonoidHom.mulLeft ε x) = AddMonoidHom.mulLeft ε x := fun x => by
    simp only [AddMonoidHom.coe_mulLeft, ← mul_assoc, hεε]
  have hcY : IsClosed (((AddMonoidHom.mulLeft ε).ker : Set (AF F))) := isClosed_eq hp continuous_const
  haveI : LocallyCompactSpace (AddMonoidHom.mulLeft ε).ker := hcY.locallyCompactSpace
  haveI : LocallyCompactSpace (fixE ε) := (isClosed_eq hp continuous_id).locallyCompactSpace
  haveI := hν
  haveI : SecondCountableTopology (fixE ε) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SecondCountableTopology (AddMonoidHom.mulLeft ε).ker := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SigmaCompactSpace (fixE ε) := inferInstance
  haveI : SigmaCompactSpace (AddMonoidHom.mulLeft ε).ker := inferInstance
  haveI : SigmaFinite ν := inferInstance
  obtain ⟨c, hc, hdec⟩ := decomp (AddMonoidHom.mulLeft ε) hp hpp db ν (Measure.addHaar)
  have hloc := fun v => GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), IsTopologicalRing (Fv F v) := fun v => (hloc v).1
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  haveI : ∀ v, (lam v).IsAddHaarMeasure := fun v => (hlam v).1
  have hne : ∀ k, ∫ y, testT (ρ k) (S ∪ S₁) (U k) y ∂db ≠ 0 := by
    intro k
    rw [hint k]
    refine mul_ne_zero (by exact_mod_cast (hρ k).2.2.2.ne') (Finset.prod_ne_zero_iff.2 fun v _ => ?_)
    have h1 : 0 < (lam v) (U k v) := (hU k v).2.1.measure_pos (lam v) ⟨0, (hU k v).2.2⟩
    have h2 : (lam v) (U k v) ≠ ⊤ := (hU k v).1.measure_lt_top.ne
    exact_mod_cast (ENNReal.toReal_pos h1.ne' h2).ne'
  choose g Gc hGc hgI hgb hgint hgeq using fun k => kdata ψ hψ Finset.subset_union_left hε db ν Measure.addHaar c hc
    hdec (ρ k) (hρ k).1 (hρ k).2.1 (hρ k).2.2.1 (U k) (fun v => (hU k v).2.2) (hinv k).1 (hinv k).2 (hne k)
  refine ⟨g, fun k s => Gc k * tR (ρ k) (S ∪ S₁) (U k) (-(ε * s)),
    fun k => {a | ε * a = a ∧ fstA F a ∈ tsupport (ρ k) ∧ ∀ v ∈ S, (sndA F a) v ∈ U k v},
    fun k => ⟨hgI k, hgb k, fun s => ⟨mul_nonneg (hGc k) (tR_nonneg (hρ k).2.2.1 _ _ _), hgint k s⟩⟩,
    fun h => ?_, fun k s hs => ?_, top1 S ε hε _ U hρt hUt⟩
  · have hl := hlim h.1
    have hm : sndA F h.1 ∈ intF (S ∪ S₁) := fun v hv => by
      rw [snd_eq, fix_snd hε (memH h) (fun h' => hv (Finset.mem_union_left _ h'))]
      exact zero_mem _
    rw [Set.indicator_of_mem hm] at hl
    simp only [hgeq]
    exact hl
  · have ht : tR (ρ k) (S ∪ S₁) (U k) (-(ε * s)) ≠ 0 := fun h0 => hs (by simp only [h0, mul_zero])
    unfold tR at ht
    have hρne : ρ k (fstA F (-(ε * s))) ≠ 0 := fun h0 => ht (by rw [h0, zero_mul])
    have hbox : sndA F (-(ε * s)) ∈ boxA (S ∪ S₁) (U k) := by
      by_contra hn
      exact ht (by rw [Set.indicator_of_notMem hn, mul_zero])
    exact ⟨by rw [mul_neg, ← mul_assoc, hεε], subset_tsupport _ hρne,
      fun v hv => hbox.1 v (Finset.mem_union_left _ hv)⟩

end PositivityTheory.Rg.Rsw.L.LApproxId

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LApproxIdD
section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.MemOfCoord
section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.CharSum
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LApproxId

theorem transfer {H K ι : Type} [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H] [MeasurableSpace H]
    [BorelSpace H] [AddCommGroup K] [TopologicalSpace K] [IsTopologicalAddGroup K] [LocallyCompactSpace K]
    [SecondCountableTopology K] [T2Space K] [MeasurableSpace K] [BorelSpace K] [Fintype ι]
    (Θ : H ≃ₜ+ (ι → K)) (lam : Measure H) [lam.IsAddHaarMeasure] (ν : Measure K) [ν.IsAddHaarMeasure] :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ f : ι → K → ℂ, (∫ x, ∏ i, f i (Θ x i) ∂lam = (c : ℂ) * ∏ i, ∫ y, f i y ∂ν) ∧
      ((∀ i, Integrable (f i) ν) → Integrable (fun x => ∏ i, f i (Θ x i)) lam) := by
  have : (Measure.pi fun _ : ι => ν).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  obtain ⟨c, hc, hmap⟩ := haar_map_eq Θ lam (Measure.pi fun _ : ι => ν)
  have hemb : MeasurableEmbedding Θ := Θ.toHomeomorph.measurableEmbedding
  refine ⟨c, hc, fun f => ⟨?_, fun hf => ?_⟩⟩
  · have h1 := hemb.integral_map (μ := lam) (fun v : ι → K => ∏ i, f i (v i))
    rw [← h1, hmap, integral_smul_nnreal_measure, integral_fintype_prod_eq_prod, NNReal.smul_def, Complex.real_smul]
  · have h2 : Integrable (fun v : ι → K => ∏ i, f i (v i)) (lam.map Θ) := by
      rw [hmap]
      exact (Integrable.fintype_prod (μ := fun _ => ν) hf).smul_measure ENNReal.coe_ne_top
    exact hemb.integrable_map_iff.mp h2


open GlobalTheory.CompanionTheory.SiegelND.Coef.TestN in
theorem hCo_smul {F E R : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)
    {d n : ℕ} (b : Module.Basis (Fin d) F E) (r : R) (X X' : HermR R σ n)
    (h : X'.1 = algebraMap R (R ⊗[F] E) r • X.1) (i : Idx n d) : hCo R σ b X' i = r * hCo R σ b X i := by
  rcases i with i | q
  · simp only [hCo, Sum.elim_inl, h, Matrix.smul_apply, smul_eq_mul, ← Algebra.smul_def, map_smul]
    exact (mul_smul_comm _ _ _).symm
  · simp only [hCo, Sum.elim_inr, h, Matrix.smul_apply, smul_eq_mul, ← Algebra.smul_def, map_smul,
      Finsupp.smul_apply]

theorem char_sum {A ι : Type} [AddCommMonoid A] (ψ : AddChar A ℂ) (s : Finset ι) (a : ι → A) :
    ψ (∑ i ∈ s, a i) = ∏ i ∈ s, ψ (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, AddChar.map_add_eq_mul, ih]

end PositivityTheory.Rg.Rsw.L.LApproxId

end
end

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LApproxId

open GlobalTheory.CompanionTheory.SiegelND.Coef.TestN

theorem memHA (D : D7) (t : ℕ) (X : Mx D t t) : X ∈ hermA D t ↔ X ∈ HermR (AF D.host.F) D.sp.cm.sig t := by
  constructor
  · intro h a c
    have h' : GlobalTheory.MixModel.adj X = X := h
    have := congrFun (congrFun h' a) c
    simpa [GlobalTheory.MixModel.adj, Matrix.transpose_apply, Matrix.map_apply] using this
  · intro h
    change GlobalTheory.MixModel.adj X = X
    ext a c
    simpa [GlobalTheory.MixModel.adj, Matrix.transpose_apply, Matrix.map_apply] using h a c

theorem smul_memA (D : D7) (t : ℕ) (e : AE D) (he : cA D e = e) (X : Mx D t t) (h : X ∈ hermA D t) :
    e • X ∈ hermA D t := by
  have h' : GlobalTheory.MixModel.adj X = X := h
  change GlobalTheory.MixModel.adj (e • X) = e • X
  ext a c
  have := congrFun (congrFun h' a) c
  simp only [GlobalTheory.MixModel.adj, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
    map_mul, he] at this ⊢
  rw [this]

theorem pch_eq (D : D7) (t : ℕ) (ψ : AddChar (AF D.host.F) ℂ) (X T : Mx D t t) (hX : X ∈ hermA D t)
    (hT : T ∈ hermA D t) :
    pch ψ X T = ψ (pairHerm (AF D.host.F) D.sp.cm.sig t ⟨X, (memHA D t X).1 hX⟩ ⟨T, (memHA D t T).1 hT⟩) := by
  simp only [pch, halfTr, trA, pairHerm, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]

theorem coord_fix (D : D7) (t : ℕ) (e : AE D) (ε : AF D.host.F) (heS : e = algebraMap (AF D.host.F) (AE D) ε)
    {d : ℕ} (b : Module.Basis (Fin d) D.host.F D.host.E)
    (X : HermR (AF D.host.F) D.sp.cm.sig t) (hX : e • X.1 = X.1) (i : Idx t d) :
    ε * hCo (AF D.host.F) D.sp.cm.sig b X i = hCo (AF D.host.F) D.sp.cm.sig b X i :=
  (hCo_smul _ b ε X X (by rw [← heS, hX]) i).symm

theorem mem_of_coord (D : D7) (t : ℕ) (e : AE D) (ε : AF D.host.F) (heS : e = algebraMap (AF D.host.F) (AE D) ε)
    (hcA : cA D e = e) {d : ℕ} (b : Module.Basis (Fin d) D.host.F D.host.E)
    (eA : HermR (AF D.host.F) D.sp.cm.sig t ≃ₜ+ (Idx t d → AF D.host.F))
    (heA : ∀ X, eA X = hCo (AF D.host.F) D.sp.cm.sig b X) (y : HermR (AF D.host.F) D.sp.cm.sig t)
    (hw : ∀ i, ε * eA y i = eA y i) : e • y.1 = y.1 := by
  have hyA : y.1 ∈ hermA D t := (memHA D t y.1).2 y.2
  have hY := (memHA D t _).1 (smul_memA D t e hcA y.1 hyA)
  have h1 : eA ⟨e • y.1, hY⟩ = eA y := by
    funext i
    rw [heA, hCo_smul _ b ε y ⟨e • y.1, hY⟩ (by rw [← heS]) i, ← heA, hw]
  exact congrArg Subtype.val (eA.injective h1)


set_option synthInstance.maxHeartbeats 200000 in
theorem exTheta' (D : D7) (t : ℕ) (e : AE D) (ε : AF D.host.F) (heS : e = algebraMap (AF D.host.F) (AE D) ε)
    (hcA : cA D e = e) {d : ℕ} (b : Module.Basis (Fin d) D.host.F D.host.E)
    (eA : HermR (AF D.host.F) D.sp.cm.sig t ≃ₜ+ (Idx t d → AF D.host.F))
    (heA : ∀ X, eA X = hCo (AF D.host.F) D.sp.cm.sig b X) :
    ∃ Θ : hermS D t e ≃ₜ+ (Idx t d → fixE ε),
      ∀ x i, ((Θ x i) : AF D.host.F) = eA ⟨x.1.1, (memHA D t x.1.1).1 x.1.2⟩ i := by
  have hfix : ∀ (x : hermS D t e) i, ε * eA ⟨x.1.1, (memHA D t x.1.1).1 x.1.2⟩ i =
      eA ⟨x.1.1, (memHA D t x.1.1).1 x.1.2⟩ i := fun x i => by
    rw [heA]; exact coord_fix D t e ε heS b ⟨x.1.1, (memHA D t x.1.1).1 x.1.2⟩ x.2 i
  have hinv : ∀ v : Idx t d → fixE ε, e • (eA.symm (fun i => (v i).1)).1 = (eA.symm (fun i => (v i).1)).1 :=
    fun v => mem_of_coord D t e ε heS hcA b eA heA _ (fun i => by rw [eA.apply_symm_apply]; exact (v i).2)
  refine ⟨{ toFun := fun x i => ⟨eA ⟨x.1.1, (memHA D t x.1.1).1 x.1.2⟩ i, hfix x i⟩
            invFun := fun v => ⟨⟨(eA.symm (fun i => (v i).1)).1, (memHA D t _).2 (eA.symm _).2⟩, hinv v⟩
            left_inv := fun x => by
              apply Subtype.ext; apply Subtype.ext
              simp
            right_inv := fun v => by
              funext i
              apply Subtype.ext
              simp
            map_add' := fun x y => by
              funext i
              apply Subtype.ext
              change eA _ i = eA _ i + eA _ i
              exact congrFun (map_add eA ⟨x.1.1, (memHA D t x.1.1).1 x.1.2⟩ ⟨y.1.1, (memHA D t y.1.1).1 y.1.2⟩) i
            continuous_toFun := continuous_pi fun i => Continuous.subtype_mk ((continuous_apply i).comp
              (eA.continuous.comp ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _))) _
            continuous_invFun := ((continuous_subtype_val.comp (eA.symm.continuous.comp
              (continuous_pi fun i => continuous_subtype_val.comp (continuous_apply i)))).subtype_mk _).subtype_mk _ },
    fun x i => rfl⟩

theorem e_eq (D : D7) (S : Finset (Pl D)) (e : AE D) (he : IsIdem S e) :
    e = algebraMap (AF D.host.F) (AE D) ((1, LIdemEx.indS S) : AF D.host.F) := by
  have h : e = LIdemEx.eS S := LIdemEx.ae_ext _ _ (fun w => by rw [he.1 w, (LIdemEx.isIdem_eS S).1 w])
    (fun v => by rw [he.2 v, (LIdemEx.isIdem_eS S).2 v])
  exact h.trans rfl

end PositivityTheory.Rg.Rsw.L.LApproxId

end
end

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LApproxId

theorem small_eventually {ι A M : Type} [Finite ι] [TopologicalSpace A] [Zero A] [TopologicalSpace M]
    (R : (ι → A) → M) (hR : Continuous R) (U : Set M) (hU : IsOpen U) (h0 : R 0 ∈ U) (Sp : ℕ → Set A)
    (hSp : Tendsto Sp atTop (𝓝 0).smallSets) : ∀ᶠ k in atTop, ∀ w : ι → A, (∀ i, w i ∈ Sp k) → R w ∈ U := by
  have hW : R ⁻¹' U ∈ 𝓝 (0 : ι → A) := hR.continuousAt.preimage_mem_nhds (hU.mem_nhds h0)
  rw [nhds_pi, Filter.mem_pi] at hW
  obtain ⟨I, -, tt, htt, hsub⟩ := hW
  have hN : (⋂ i, tt i) ∈ 𝓝 (0 : A) := Filter.iInter_mem.mpr htt
  filter_upwards [tendsto_smallSets_iff.mp hSp _ hN] with k hk w hw
  exact hsub (fun i _ => Set.mem_iInter.mp (hk (hw i)) i)

open GlobalTheory.CompanionTheory.SiegelND.Coef.TestN in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem approxId_of (h1 : OneD) : ApproxId := by
  classical
  intro D t ψ hψ S e he lam hlam
  have hCM : IsCMExt D.host.F D.host.E D.sp.cm.sig := isCMExt_host D
  have : Module.Finite D.host.F D.host.E := Module.finite_of_finrank_eq_succ (n := 1) hCM.2.2.1
  have : BorelSpace (AF D.host.F) := ⟨rfl⟩
  have : BorelSpace (Mx D t t) := ⟨rfl⟩
  obtain ⟨eA, heA⟩ := GlobalTheory.T.exists_homeomorph_hermR_coordinates D.host.F D.host.E D.sp.cm.sig hCM (AF D.host.F) _ (Module.finBasis D.host.F D.host.E) t
  obtain ⟨-, hBd⟩ := GlobalTheory.T.coordinate_form_symmetric_nondegenerate D.host.F D.host.E D.sp.cm.sig hCM _ (Module.finBasis D.host.F D.host.E) t
  have hpair := GlobalTheory.T.hermitian_pairing_in_coordinates D.host.F D.host.E D.sp.cm.sig hCM (AF D.host.F) _ (Module.finBasis D.host.F D.host.E) t
  generalize Module.finBasis D.host.F D.host.E = b at heA hBd hpair
  have hε0 : IsIdF S ((1, LIdemEx.indS S) : AF D.host.F) := ⟨rfl, fun v => rfl⟩
  obtain ⟨ε, hε, heS⟩ : ∃ ε : AF D.host.F, IsIdF S ε ∧ e = algebraMap (AF D.host.F) (AE D) ε :=
    ⟨_, hε0, e_eq D S e he⟩
  have hcA : cA D e = e := (LIdemEx.idem_props S e he).2
  obtain ⟨Θ, hΘ⟩ := exTheta' D t e ε heS hcA b eA heA
  have hcl : IsClosed ((fixE ε : AddSubgroup (AF D.host.F)) : Set (AF D.host.F)) :=
    isClosed_eq (continuous_const.mul continuous_id) continuous_id
  have : LocallyCompactSpace (fixE ε) := hcl.locallyCompactSpace
  have : SecondCountableTopology (fixE ε) := TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨g1, G1, Sp, hg, hlim, hsupp, hSp⟩ := h1 D.host.F hCM.1 ψ hψ S ε hε (Measure.addHaar) inferInstance
  obtain ⟨c, -, hTr⟩ := transfer Θ lam (Measure.addHaar : Measure (fixE ε))
  set Bm := (coordForm D.sp.cm.sig b t).map (algebraMap D.host.F (AF D.host.F)) with hBm
  let sT : Mx D t t → _ := fun T => if hT : T ∈ hermA D t then
    Bm *ᵥ hCo (AF D.host.F) D.sp.cm.sig b ⟨T, (memHA D t T).1 hT⟩ else 0
  refine ⟨fun k x => ∏ i, g1 k (Θ x i), fun k T => if T ∈ hermA D t then (c : ℝ) * ∏ i, G1 k (sT T i) else 0,
    fun k => ⟨?_, ?_, fun T hT => ⟨?_, ?_⟩⟩, fun x => ?_, ?_⟩
  · exact (hTr (fun _ => g1 k)).2 (fun _ => (hg k).1)
  · intro x
    rw [norm_prod]
    exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun i _ => (hg k).2.1 _)
  · beta_reduce
    rw [if_pos hT]
    exact mul_nonneg c.2 (Finset.prod_nonneg fun i _ => ((hg k).2.2 _).1)
  · beta_reduce
    have hpt : ∀ x : hermS D t e, pch ψ x.1.1 T = ∏ i, ψ ((Θ x i).1 * sT T i) := by
      intro x
      rw [pch_eq D t ψ x.1.1 T x.1.2 hT, hpair, dotProduct, char_sum]
      refine Finset.prod_congr rfl fun i _ => ?_
      simp only [sT, dif_pos hT, hΘ, heA]
    calc ∫ x, (∏ i, g1 k (Θ x i)) * pch ψ x.1.1 T ∂lam
        = ∫ x, ∏ i, (fun i h => g1 k h * ψ (h.1 * sT T i)) i (Θ x i) ∂lam := by
          congr 1; funext x; rw [hpt, ← Finset.prod_mul_distrib]
      _ = (c : ℂ) * ∏ i, ∫ h, g1 k h * ψ (h.1 * sT T i) ∂(Measure.addHaar : Measure (fixE ε)) :=
          (hTr (fun i h => g1 k h * ψ (h.1 * sT T i))).1
      _ = _ := by
          rw [if_pos hT]
          push_cast
          congr 1
          exact Finset.prod_congr rfl fun i _ => ((hg k).2.2 _).2
  · have := tendsto_finsetProd Finset.univ (fun i _ => hlim (Θ x i))
    simpa using this
  · intro C hC hCT ε' hε'
    have hunit : IsUnit Bm.det := by
      have h := (RingHom.map_det (algebraMap D.host.F (AF D.host.F)) (coordForm D.sp.cm.sig b t)).symm
      rw [hBm]
      exact h ▸ (isUnit_iff_ne_zero.mpr hBd).map _
    let R : (Idx t (Module.finrank D.host.F D.host.E) → AF D.host.F) → Mx D t t := fun w => (eA.symm (Bm⁻¹ *ᵥ w)).1
    have hRc : Continuous R :=
      continuous_subtype_val.comp (eA.symm.continuous.comp (continuous_const.matrix_mulVec continuous_id))
    have hU : IsOpen {M : Mx D t t | -M ∉ C} := hC.isOpen_compl.preimage continuous_neg
    have h0 : R 0 ∈ {M : Mx D t t | -M ∉ C} := by
      have : R 0 = 0 := by simp [R, Matrix.mulVec_zero]
      simp only [Set.mem_ofPred_eq, this, neg_zero]
      exact fun h => (hCT 0 h).2.2 rfl
    filter_upwards [small_eventually R hRc _ hU h0 Sp hSp] with k hk T hTC
    obtain ⟨hTA, heT, -⟩ := hCT T hTC
    by_contra hlt
    have hpos := lt_trans hε' (not_le.mp hlt)
    beta_reduce at hpos
    rw [if_pos hTA] at hpos
    have hprod : ∀ i, G1 k (sT T i) ≠ 0 := fun i =>
      Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hpos.ne') i (Finset.mem_univ i)
    have hfixT : ∀ i, ε * sT T i = sT T i := by
      intro i
      simp only [sT, dif_pos hTA, Matrix.mulVec, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_left_comm, coord_fix D t e ε heS b _ heT j]
    have hw : ∀ i, -(sT T i) ∈ Sp k := fun i => by
      have := hsupp k (sT T i) (hprod i)
      rwa [hfixT] at this
    have hmem := hk (fun i => -(sT T i)) hw
    have hR : R (fun i => -(sT T i)) = -T := by
      have h2 : (fun i => -(sT T i)) = -(Bm *ᵥ hCo (AF D.host.F) D.sp.cm.sig b ⟨T, (memHA D t T).1 hTA⟩) := by
        funext i; simp only [sT, dif_pos hTA, Pi.neg_apply]
      simp only [R, h2, Matrix.mulVec_neg, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec,
        map_neg, ← heA, eA.symm_apply_apply]
      rfl
    simp only [hR, neg_neg] at hmem
    exact hmem hTC

end PositivityTheory.Rg.Rsw.L.LApproxId

end
end

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L

theorem approxId : IdemEx → ApproxId := fun _ => LApproxId.approxId_of LApproxId.oneD

end PositivityTheory.Rg.Rsw.L

end
