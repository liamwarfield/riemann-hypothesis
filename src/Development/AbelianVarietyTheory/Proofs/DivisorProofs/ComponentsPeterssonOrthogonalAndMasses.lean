module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupLiftTangentPhiLinear
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothRayQuotient
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeepsCuspLatticeNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassesAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjRootOfExp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalTranslationEquivariantStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearFunctionalGoodPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalGoodPlaceEquivariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalLocalUniqueness
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalDeterminedByUnramified
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxGraphGraphHeis

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentsPeterssonOrthogonalAndMasses
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NullMeasurableSetClassesOverFramesOn
open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

namespace GlobalTheory.ClassesMeas

theorem nullMeasurableSet_classesOver_framesOn : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r), IsComplexData U V dict → ∀ σ, GoodEmb c σ → ∀ Z : Comp Xo c, NullMeasurableSet (classesOver (V σ) (dict σ) (framesOn (U σ) Z)) (muQ1 (V σ)) := by
  intro D H Dw l Xo c r U V dict hC σ hσ Z
  obtain ⟨hU, ⟨Kf, th, hr, hK, _, hd⟩, _, _⟩ := hC.2 σ hσ
  obtain ⟨d1, d2, ⟨x0, _, d3⟩, d4, _, _⟩ := hd
  haveI : BorelSpace (GA D (V σ)) := ⟨rfl⟩
  let S : Set (U σ).Comp := {k | ∃ y, (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z}
  have key : ∀ g, dict σ g ∈ framesOn (U σ) Z ↔ (dict σ g).1 ∈ S := by
    intro g
    constructor
    · intro h
      exact ⟨(dict σ g).2, h⟩
    · rintro ⟨y, hy⟩
      exact GlobalTheory.T.framePointsOverComponent_open_set D.host.E H Dw l Xo c r U σ hU Z _ y _ (d4 g) hy
  have hP : IsOpen {g : GA D (V σ) | (dict σ g).1 ∈ S} := by
    rw [isOpen_iff_mem_nhds]
    intro g₀ hg₀
    refine Filter.mem_of_superset
      (GlobalTheory.LevelOpen.level_mem_nhds D (V σ) l.M Kf (by have := l.three_le; omega) hK g₀) ?_
    rintro g ⟨k, hk, h, hh, rfl⟩
    obtain ⟨γ, _, e1⟩ := d2 k hk g₀
    obtain ⟨γ', _, e2⟩ := d3 (g₀ * k) h hh
    have f1 := congrArg Sigma.fst e1
    have f2 := congrArg Sigma.fst e2
    show (dict σ (g₀ * k * h)).1 ∈ S
    rw [f2, f1]
    exact hg₀
  have hpre : (Quotient.mk'' ⁻¹' classesOver (V σ) (dict σ) (framesOn (U σ) Z) : Set (GA D (V σ))) =
      {g : GA D (V σ) | (dict σ g).1 ∈ S} := by
    ext g
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    show dict σ (Quotient.mk'' g : AutQ (V σ)).out ∈ framesOn (U σ) Z ↔ _
    rw [key]
    have hrel : QuotientGroup.rightRel (GQ (V σ)) (Quotient.mk'' g : AutQ (V σ)).out g :=
      Quotient.exact (Quotient.out_eq _)
    rw [QuotientGroup.rightRel_apply] at hrel
    obtain ⟨γ', _, e⟩ := d1 _ (inv_mem hrel) g
    have f := congrArg Sigma.fst e
    simp only [mul_inv_rev, inv_inv, inv_mul_cancel_right] at f
    rw [f]
  refine MeasurableSet.nullMeasurableSet ?_
  show MeasurableSet (Quotient.mk'' ⁻¹' classesOver (V σ) (dict σ) (framesOn (U σ) Z) : Set (GA D (V σ)))
  rw [hpre]
  exact hP.measurableSet

end GlobalTheory.ClassesMeas
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentsPeterssonOrthogonalAndMasses
open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.CompPetOrth

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c : Coeff l} {r : ℕ}

section One

variable {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (V : HSp D) (dict : GA D V → Σ k, Frame (U.X k).Ψ r)

theorem framesOn_disjoint {Z Z' : Comp Xo c} (h : Z ≠ Z') : Disjoint (framesOn U Z) (framesOn U Z') := by
  rw [Set.disjoint_left]
  rintro z ⟨_, hz⟩ ⟨_, hz'⟩
  have s₀ : Sp (CAt σ) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
  exact Set.disjoint_left.1 (CompSplitPfD.cspD_comp_disj Xo c Z Z' h) (hz s₀) (hz' s₀)

def sqN (la : ∀ k, Wt (U.X k).Ψ r) (f : Rul Xo c) : AutQ V → ENNReal :=
  fun q => ‖ptN la (rdU U f) (dict q.out)‖ₑ ^ (2 : ℝ)

theorem ptN_rdU_of_not_dom (la : ∀ k, Wt (U.X k).Ψ r) (f : Rul Xo c) {z : Σ k, Frame (U.X k).Ψ r}
    (hz : z.2 ∉ (U.X z.1).dom) : ptN la (rdU U f) z = 0 := by
  have h0 : rdU U f z.1 z.2 = 0 := by simp [rdU, hz]
  simp only [ptN, Data.pnorm, h0, norm_zero, zero_mul]

theorem sqN_support (la : ∀ k, Wt (U.X k).Ψ r) {Z : Comp Xo c} {f : Rul Xo c} (hf : f ∈ suppOn Z) :
    Function.support (sqN U V dict la f) ⊆ classesOver V dict (framesOn U Z) := by
  intro q hq
  by_contra hn
  apply hq
  have h0 : ptN la (rdU U f) (dict q.out) = 0 := by
    simp only [ptN, Data.pnorm, rdU_eq_zero U hf hn, norm_zero, zero_mul]
  simp [sqN, h0]

theorem petAt_sq (x : ℝ) (μ : Measure (AutQ V)) (G : WTZ D.host.E) (f : Rul Xo c) :
    petAt U x V dict μ G f ^ 2 = lieFacZ Dw x G ^ 2 * (∫⁻ q, sqN U V dict (modelWt U G) f q ∂μ).toReal := by
  unfold petAt petE
  rw [eLpNorm'_eq_lintegral_eNorm,
    ← ENNReal.toReal_rpow, mul_pow]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul ENNReal.toReal_nonneg]
  norm_num [sqN]

theorem petE_rdU_ne_top (μ : Measure (AutQ V)) [IsProbabilityMeasure μ] (la : ∀ k, Wt (U.X k).Ψ r)
    {f : Rul Xo c} (hP : rdU U f ∈ holSub U.X la) : petE V dict μ la (rdU U f) ≠ ⊤ := by
  have h : ∀ q : AutQ V, ‖ptN la (rdU U f) (dict q.out)‖ₑ ≤ supE U.X la (rdU U f) := fun q => by
    rw [Real.enorm_eq_ofReal (ptN_nonneg _ _ _)]
    by_cases hd : (dict q.out).2 ∈ (U.X (dict q.out).1).dom
    · exact le_iSup (fun p : FPt U.X => ENNReal.ofReal ((U.X p.1).pnorm (la p.1) (rdU U f p.1) p.2))
        ⟨(dict q.out).1, ⟨(dict q.out).2, hd⟩⟩
    · rw [ptN_rdU_of_not_dom U la f hd, ENNReal.ofReal_zero]
      exact bot_le
  have hle : petE V dict μ la (rdU U f) ≤ eLpNorm' (fun _ : AutQ V => supE U.X la (rdU U f)) 2 μ :=
    eLpNorm'_mono_eNorm_ae (by norm_num) (Filter.Eventually.of_forall h)
  apply ne_top_of_le_ne_top (supE_ne_top U.X la hP)
  refine hle.trans ?_
  rw [eLpNorm'_const _ (by norm_num), eNorm_eq_self, measure_univ]
  simp

theorem lint_sqN_ne_top (μ : Measure (AutQ V)) [IsProbabilityMeasure μ] (la : ∀ k, Wt (U.X k).Ψ r)
    {f : Rul Xo c} (hP : rdU U f ∈ holSub U.X la) : ∫⁻ q, sqN U V dict la f q ∂μ ≠ ⊤ := by
  have h := petE_rdU_ne_top U V dict μ la hP
  rw [petE, eLpNorm'_eq_lintegral_eNorm] at h
  intro ht
  apply h
  simp only [sqN] at ht
  norm_num at ht ⊢
  rw [ht]

theorem lint_sqN_sum [Fintype (Comp Xo c)] (μ : Measure (AutQ V))
    (hm : ∀ Z : Comp Xo c, NullMeasurableSet (classesOver V dict (framesOn U Z)) μ) (la : ∀ k, Wt (U.X k).Ψ r)
    (f : Comp Xo c → Rul Xo c) (hf : ∀ Z, f Z ∈ suppOn Z) :
    ∫⁻ q, sqN U V dict la (∑ Z, f Z) q ∂μ = ∑ Z, ∫⁻ q, sqN U V dict la (f Z) q ∂μ := by
  have hdisj : Pairwise (Function.onFun Disjoint fun Z => classesOver V dict (framesOn U Z)) :=
    fun Z Z' h => Set.disjoint_left.2 fun q h1 h2 => Set.disjoint_left.1 (framesOn_disjoint U h) h1 h2
  have hpt : ∀ Z, ∀ q ∈ classesOver V dict (framesOn U Z),
      sqN U V dict la (∑ Z, f Z) q = sqN U V dict la (f Z) q := by
    intro Z q hq
    have e : rdU U (∑ Z', f Z') (dict q.out).1 (dict q.out).2 = rdU U (f Z) (dict q.out).1 (dict q.out).2 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.sum_apply, Finset.sum_apply, Finset.sum_eq_single Z]
      · intro Z' _ hZ'
        exact rdU_eq_zero U (hf Z') fun h => Set.disjoint_left.1 (framesOn_disjoint U hZ') h hq
      · intro h; exact absurd (Finset.mem_univ Z) h
    simp only [sqN, ptN, Data.pnorm, e]
  have hsupp : Function.support (sqN U V dict la (∑ Z, f Z)) ⊆ ⋃ Z, classesOver V dict (framesOn U Z) := by
    intro q hq
    by_contra hn
    simp only [Set.mem_iUnion, not_exists] at hn
    apply hq
    have e : rdU U (∑ Z', f Z') (dict q.out).1 (dict q.out).2 = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.sum_apply, Finset.sum_apply]
      exact Finset.sum_eq_zero fun Z _ => rdU_eq_zero U (hf Z) (hn Z)
    have h0 : ptN la (rdU U (∑ Z', f Z')) (dict q.out) = 0 := by
      simp only [ptN, Data.pnorm, e, norm_zero, zero_mul]
    simp only [sqN, h0]
    simp
  rw [← setLIntegral_eq_of_support_subset hsupp, lintegral_iUnion₀ hm (fun Z Z' h => (hdisj h).aedisjoint),
    tsum_fintype]
  refine Finset.sum_congr rfl fun Z _ => ?_
  rw [← setLIntegral_eq_of_support_subset (sqN_support U V dict la (hf Z))]
  exact lintegral_congr_ae ((ae_restrict_mem₀ (hm Z)).mono fun q hq => hpt Z q hq)

theorem petAt_muOn_sq (x : ℝ) (G : WTZ D.host.E) {Z : Comp Xo c} {f : Rul Xo c} (hf : f ∈ suppOn Z) :
    (muQ1 V (classesOver V dict (framesOn U Z))).toReal * petAt U x V dict (muOn U V dict Z) G f ^ 2 =
      petAt U x V dict (muQ1 V) G f ^ 2 := by
  rw [petAt_sq, petAt_sq]
  unfold muOn muPart ProbabilityTheory.cond
  have key := setLIntegral_eq_of_support_subset (μ := muQ1 V) (sqN_support U V dict (modelWt U G) hf)
  rw [lintegral_smul_measure, key]
  by_cases h0 : muQ1 V (classesOver V dict (framesOn U Z)) = 0
  · have hI : ∫⁻ q, sqN U V dict (modelWt U G) f q ∂muQ1 V = 0 := by
      rw [← key, Measure.restrict_eq_zero.2 h0, lintegral_zero_measure]
    simp [h0, hI]
  · have ha : (muQ1 V (classesOver V dict (framesOn U Z))).toReal ≠ 0 :=
      ENNReal.toReal_ne_zero.2 ⟨h0, measure_ne_top _ _⟩
    rw [smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_inv]
    field_simp

theorem petAt_idem_le (x : ℝ) (μ : Measure (AutQ V)) [IsProbabilityMeasure μ] (G : WTZ D.host.E) (Z : Comp Xo c)
    {f : Rul Xo c} (hP : rdU U f ∈ holSub U.X (modelWt U G)) :
    petAt U x V dict μ G (GlobalTheory.FlatLine.idem Z * f) ≤ petAt U x V dict μ G f := by
  unfold petAt
  refine mul_le_mul_of_nonneg_left ?_ (lieFacZ_pos _ _).le
  refine ENNReal.toReal_mono (petE_rdU_ne_top U V dict μ _ hP) ?_
  unfold petE
  refine eLpNorm'_mono_ae (by norm_num) (Filter.Eventually.of_forall fun q => ?_)
  rw [Real.norm_of_nonneg (ptN_nonneg _ _ _), Real.norm_of_nonneg (ptN_nonneg _ _ _)]
  simp only [ptN, Data.pnorm]
  refine mul_le_mul_of_nonneg_right ?_ (pnorm_fac_nonneg _ _ _)
  rw [GlobalTheory.AllWt.rdU_mul, Pi.mul_apply, Pi.mul_apply, norm_mul]
  refine mul_le_of_le_one_left (norm_nonneg _) ?_
  have he : IsIdempotentElem (rdU U (GlobalTheory.FlatLine.idem Z) (dict q.out).1 (dict q.out).2) := by
    have := congrFun (congrFun (GlobalTheory.AllWt.rdU_mul U (GlobalTheory.FlatLine.idem Z) (GlobalTheory.FlatLine.idem Z)) (dict q.out).1)
      (dict q.out).2
    rw [GlobalTheory.FlatLine.idem_mul_idem] at this
    exact this.symm
  rcases IsIdempotentElem.iff_eq_zero_or_one.1 he with h | h <;> rw [h] <;> simp

end One

theorem orthogonal_mass_idem : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r), IsComplexData U V dict → ∀ G : WTZ D.host.E, Orthogonal U V dict G ∧ (∀ Z σ, 0 ≤ mass U V dict Z σ ∧ mass U V dict Z σ ≤ 1) ∧ ∀ (Z : Comp Xo c) (σ : c.F →+* ℂ) (f : cuspW Xo c U G), petW U (xiR D) V dict G σ (idem Z * (f : Rul Xo c)) ≤ petW U (xiR D) V dict G σ (f : Rul Xo c) := by
  intro D H Dw l Xo c r U V dict hc G
  haveI := CompFin.finite_comp Xo c
  letI : Fintype (Comp Xo c) := Fintype.ofFinite _
  have hm : ∀ (σ : c.F →+* ℂ) (Z : Comp Xo c), NullMeasurableSet
      (classesOver (V (goodOf c σ)) (dict (goodOf c σ)) (framesOn (U (goodOf c σ)) Z)) (muQ1 (V (goodOf c σ))) :=
    fun σ Z => GlobalTheory.ClassesMeas.nullMeasurableSet_classesOver_framesOn D H Dw l Xo c r U V dict hc _
      (goodEmb_goodOf c σ) Z
  refine ⟨fun σ => ⟨fun f => ?_, fun Z f => ?_⟩, fun Z σ => ⟨ENNReal.toReal_nonneg, ?_⟩, fun Z σ f => ?_⟩
  · rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
    simp only [normRes, petW]
    rw [petAt_sq, lint_sqN_sum _ _ _ _ (hm σ) _ _ fun Z => (Submodule.mem_inf.1 (f Z).2).2,
      ENNReal.toReal_sum fun Z _ => lint_sqN_ne_top _ _ _ _ _
        ((mem_cuspW.1 (Submodule.mem_inf.1 (f Z).2).1).2 _ (goodEmb_goodOf c σ)), Finset.mul_sum]
    exact Finset.sum_congr rfl fun Z _ => (petAt_sq _ _ _ _ _ _ _).symm
  · simp only [normRes, normOn, petW, petOn, mass]
    exact (petAt_muOn_sq _ _ _ _ _ (Submodule.mem_inf.1 f.2).2).symm
  · simp only [mass]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)
  · simp only [petW]
    exact petAt_idem_le _ _ _ _ _ _ _ ((mem_cuspW.1 f.2).2 _ (goodEmb_goodOf c σ))

end GlobalTheory.CompPetOrth
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentsPeterssonOrthogonalAndMassesStatement
open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.components_peterssonOrthogonal_and_masses : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r), IsComplexData U V dict → ∀ G : WTZ D.host.E, Orthogonal U V dict G ∧ (∀ Z σ, 0 ≤ mass U V dict Z σ ∧ mass U V dict Z σ ≤ 1) ∧ ∀ (Z : Comp Xo c) (σ : c.F →+* ℂ) (f : cuspW Xo c U G), petW U (xiR D) V dict G σ (idem Z * (f : Rul Xo c)) ≤ petW U (xiR D) V dict G σ (f : Rul Xo c) := by
  first | exact @GlobalTheory.CompPetOrth.orthogonal_mass_idem | exact GlobalTheory.CompPetOrth.orthogonal_mass_idem | (intros; apply GlobalTheory.CompPetOrth.orthogonal_mass_idem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformLowerBoundOfSums
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop

namespace GlobalTheory.CovTop.FromComp

theorem core (ι : Type) [Finite ι] [Nonempty ι] (T D A cs X cc z ρ R Bn δ' E C1 C2 mu : ℝ) (h sl δ dc degc : ι → ℝ)
    (hD : 0 ≤ D) (hT : 3 * D + 5 ≤ T) (hA : 0 < A) (hcs : 0 ≤ cs) (hX : 0 ≤ X) (hcc : 0 ≤ cc) (hz0 : 0 ≤ z) (hz1 : z < 1)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hR : 0 ≤ R) (hBn : 0 < Bn) (hδ : 0 < δ') (hE : 1 ≤ E)
    (h1 : ∀ c, δ' ≤ δ c ∧ δ c ≤ δ' / (1 - ρ)) (h2 : ∀ c, Bn * δ c ≤ dc c ∧ (1 - z) * dc c ≤ Bn * δ c)
    (h3 : ∀ c, 0 ≤ h c + cs) (h4 : ∀ c, (1 - ρ) * max 0 (sl c + cs) ≤ h c + cs + cc)
    (h5 : -X ≤ (∑ᶠ c, sl c) / (Nat.card ι : ℝ))
    (h6 : ∀ c, Bn * δ c * (T * h c - 3 * (D + 1) * |h c| - A * Real.log (2 + |h c|) - R) ≤ degc c)
    (h7 : T * X ≤ C1 * E) (h8 : T * cc ≤ C1 * E) (h9 : cs * (6 * D + 10 + T * (z + 2 * ρ)) ≤ C1 * E)
    (h10 : A * Real.log (max A 1) + R ≤ C2 * E)
    (h11 : 2 * ((∑ᶠ c, degc c) / ∑ᶠ c, dc c) ≤ mu) : -((2 * (3 * C1 + C2 + 4)) * E) ≤ mu := by
  letI := Fintype.ofFinite ι
  rw [finsum_eq_sum_of_fintype] at h5
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype] at h11
  rw [Nat.card_eq_fintype_card] at h5
  have := Formalism.ExtensionFiltration.mean_height_sum_bound ι T D A cs X cc z ρ R 0 Bn δ' h sl δ dc degc 0 0 (4 * ((3 * C1 + C2 + 4) * E)) 0 0 0
    (C1 * E) (C1 * E) mu hD hT hA hcs hX hcc hz0 hz1 hρ0 hρ1 hR le_rfl hBn hδ h1 h2 h3 h4 h5
    (fun c => by simpa using h6 c) (by linarith) (by linarith) (by linarith) (by linarith)
  linarith

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem atPoint (Y : Cov p i) (PP A C1 C2 : ℝ) (hi : (i : ℕ) + 1 < D.R.m) (hg : DeepGoodAt p i Y) (hs : SizeAt p i PP A)
    (hd : ∀ u1, Quo p i PP u1 → DegAt p i Y u1) (hsh : ∀ u1, Quo p i PP u1 → ShareAt p i Y PP u1)
    (hh : ∀ u1, Quo p i PP u1 → HeightAt p i Y PP C1 u1) (hhs : ∀ u1, Quo p i PP u1 → HSAt p i Y PP C2 u1)
    (hsum : SumAt p i Y) : UAt p i Y (2 * (3 * C1 + C2 + 4)) := by
  obtain ⟨-, -, -, -, -, hfin, hne, -⟩ := hg
  obtain ⟨hb1, hbE, -, -, -, -, hq⟩ := hs
  obtain ⟨⟨u1, hu⟩, hq⟩ := hq hi
  obtain ⟨hTD, hρ0, hρ1, hz1⟩ := hq u1 hu
  obtain ⟨δ', hδ, h1⟩ := hd u1 hu
  obtain ⟨cs, cc, X, sl, hcs, hcc, hX, h3, h4, h5, h7, h8, h9⟩ := hh u1 hu
  obtain ⟨B, R, hB, hR, h10, h6⟩ := hhs u1 hu
  have hz0 : 0 ≤ zed p i PP u1 := by
    unfold zed
    positivity
  have hBn : 0 < binT p i PP := by
    unfold binT
    exact_mod_cast Nat.choose_pos (by omega)
  exact core (Comp Y.d.Xo₂ Y.d.c₂) (lenT p i PP) (dimFlag (dat p i)) B cs X cc (zed p i PP u1) (rhoB (dat p i) u1) R
    (binT p i PP) δ' (unitE p) C1 C2 _ (fun Z => Y.ht u1 Z) sl (fun Z => Y.dg u1 Z) (fun Z => Y.rkC (uM p i) Z)
    (fun Z => Y.degC (uM p i) Z) (Nat.cast_nonneg _) (by exact_mod_cast hTD) hB hcs hX hcc hz0 hz1 hρ0 hρ1 hR hBn hδ
    (hb1.trans hbE) h1 (hsh u1 hu) h3 h4 h5 h6 h7 h8 h9 h10 hsum

end GlobalTheory.CovTop.FromComp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveQuasiCompactQ
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveQuasiCompactQ
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RayEv

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RayEv

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O D.X]

theorem Ray.surjective_quasiCompact_q {oa : D.OAct O} (Y : Ray oa) :
    Surjective Y.q.left ∧ QuasiCompact Y.q.left := by
  obtain ⟨c⟩ := GlobalTheory.TorusModel.nonempty_gtCoord GlobalTheory.allSixLaws.1.globalFns Y.isGt ⊥ 0
  have := c.q_surj
  have := c.q_affine
  let F := fstG (⊥ : Ideal R) 0 Y.H
  let j := inv F.left
  have hF : F.left ≫ Y.H.hom = (thickObj R ⊥ 0 Y.H).hom ≫ thick R ⊥ 0 := Over.w F
  let ξ := Y.Φ Y.H (𝟙 _)
  obtain ⟨x, hx⟩ := GlobalTheory.TorusCoord.exists_point c (T := Y.H) (Y.H.hom ≫ inv (thick R ⊥ 0)) (by simp) ξ
  obtain ⟨ξ', hξ'⟩ := GlobalTheory.TorusCoord.exists_isPointOf c (T := Y.H) j (by
    rw [← hF]; exact IsIso.inv_hom_id_assoc _ _)
  let b : Y.H ⟶ Y.H := (Y.Φ Y.H).symm ξ'
  have hb : Y.Φ Y.H b = ξ' := Equiv.apply_symm_apply _ _
  let a := x ≫ F.left
  have ha : a ≫ Y.H.hom = Y.H.hom := by
    rw [Category.assoc, hF]
    exact GlobalTheory.TorusCoord.IsPointOf.comp_hom c hx
  let a' : Y.H ⟶ Y.H := Over.homMk a ha
  have haj : a ≫ j = x := by simp [a, j]
  have e1 : b.left ≫ x = j := by
    have h1 : GtPt.IsPull b.left ξ (Y.Φ Y.H (b ≫ 𝟙 _)) := Y.rep.1 Y.H Y.H b (𝟙 _)
    rw [Category.comp_id, hb] at h1
    exact (GlobalTheory.TorusCoord.IsPointOf.pull c hx h1).unique_left c hξ'
  have e1' : b.left ≫ a = 𝟙 _ := by
    rw [← Category.assoc, e1]; simp [j]
  have e2 : a' ≫ b = 𝟙 _ := by
    have h2 : GtPt.IsPull a (Y.Φ Y.H b) (Y.Φ Y.H (a' ≫ b)) := Y.rep.1 Y.H Y.H a' b
    rw [hb] at h2
    have h3 := GlobalTheory.TorusCoord.IsPointOf.pull c hξ' h2
    rw [haj] at h3
    exact (Y.Φ Y.H).injective (h3.unique_right c hx)
  have e2' : a ≫ b.left = 𝟙 _ := congrArg (·.left) e2
  have : IsIso a := ⟨⟨b.left, e2', e1'⟩⟩
  have hq : Y.q.left = a ≫ j ≫ c.q.left ≫ pullback.fst D.P.A.hom (thick R ⊥ 0) := by
    rw [← Category.assoc a j, haj, ← GlobalTheory.TorusCoord.pG_left]
    exact hx.1
  rw [hq]
  exact ⟨inferInstance, inferInstance⟩

end GlobalTheory.RayEv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveQuasiCompactQStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RayEv
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ray_q_surjective_and_quasiCompact : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O D.X] {oa : D.OAct O} (Y : Ray oa), Surjective Y.q.left ∧ QuasiCompact Y.q.left := by
  first | exact @GlobalTheory.RayEv.Ray.surjective_quasiCompact_q | exact GlobalTheory.RayEv.Ray.surjective_quasiCompact_q | (intros; apply GlobalTheory.RayEv.Ray.surjective_quasiCompact_q <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneLeIntersectionNumberSubvarietyThroughPositive
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneLeIntersectionNumberSubvarietyThroughPositive
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PosThrough

theorem one_le_interNumRed : GlobalTheory.Published.NefNumerics → ∀ (k : Type) [Field k] (X : Scheme.{0}) (q : X ⟶ Sp k), IsProjOver q → letI := algebraΓOfHom q; ∀ (N N₁ N₂ : LB X) (hN : N.IsLB) (h₁ : N₁.IsLB) (h₂ : N₂.IsLB) (a : ℕ) (x : X), IsNef k N → 0 < a → a • cls N hN = cls N₁ h₁ + cls N₂ h₂ → AmpleAt N₁ x → IsNef k N₂ → ∀ (Z : Closeds X) (e : ℕ), IsIrreducible (Z : Set X) → x ∈ Z → 1 ≤ e → topologicalKrullDim (Z : Set X) = e → 1 ≤ interNumRed k Z (fun _ : Fin e => N) := by
  intro hNN k _ X q hq
  letI := algebraΓOfHom q
  intro N N₁ N₂ hN h₁ h₂ a x hNef ha hcls hamp hN₂ Z e hZ hx he hdim
  have hBig : ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp k), IsProjOver q →
      letI := algebraΓOfHom q; ∀ (N N₁ N₂ : LB X) (hN : N.IsLB) (h₁ : N₁.IsLB) (h₂ : N₂.IsLB) (a : ℕ) (x : X),
      IsNef k N → 0 < a → a • cls N hN = cls N₁ h₁ + cls N₂ h₂ → AmpleAt N₁ x → IsNef k N₂ → IsBig k N :=
    GlobalTheory.T.isBigLineBundle_of_smul_class_eq_ampleAt_add_nef hNN
  have hAmp : ∀ (Y X : Scheme.{0}) (π : X ⟶ Y) [IsAffineHom π] (N : LB Y), N.IsLB → ∀ x : X,
      AmpleAt N (π x) → AmpleAt (N.pull π) x := GlobalTheory.T.ampleModuloEffectiveAwayFromPoint_pull_affine
  have : IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := isIntegral_red hZ
  set q' := redι Z ≫ q with hq'
  letI := algebraΓOfHom q'
  have hi : ∀ r : k, (redι Z).appTop (algebraMap k Γ(X, ⊤) r) = algebraMap k Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) r :=
    fun r => rfl
  have hpq : IsProjOver q' := by
    obtain ⟨n, f, hf, hs⟩ := hq
    exact ⟨n, redι Z ≫ f, inferInstance, by rw [Category.assoc, hs]⟩
  obtain ⟨w, rfl⟩ : x ∈ Set.range (redι Z) := by rw [range_redι]; exact hx
  have hb := hBig k _ q' hpq (N.pull (redι Z)) (N₁.pull (redι Z)) (N₂.pull (redι Z))
    (LB.isLB_pull hN _) (LB.isLB_pull h₁ _) (LB.isLB_pull h₂ _) a w
    (hNef.pull_of_isClosedImmersion _ hi) ha
    (by rw [cls_pull hN, cls_pull h₁, cls_pull h₂, ← map_nsmul, hcls, map_add (f := _)])
    (hAmp _ _ _ N₁ h₁ w hamp) (hN₂.pull_of_isClosedImmersion _ hi)
  have hstr : strHom k (Scheme.IdealSheafData.vanishingIdeal Z).subscheme = q' :=
    strHom_eq (f := q') fun _ => rfl
  have hD : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal Z).subscheme = e :=
    (topologicalKrullDim_red Z).trans hdim
  have hpos := ((hNN.2.2.isBig_iff (hstr ▸ hpq) hD (hNef.pull_of_isClosedImmersion _ hi)).1 hb)
  have heq : interNumRed k Z (fun _ : Fin e => N) = topSelfIntersection k (N.pull (redι Z)) e :=
    interNumOn_const_eq_topSelf hi hN e
  omega

end GlobalTheory.PosThrough
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneLeIntersectionNumberSubvarietyThroughPositiveStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_le_intersectionNumber_subvariety_through_positive : GlobalTheory.Published.NefNumerics → ∀ (k : Type) [Field k] (X : Scheme.{0}) (q : X ⟶ Sp k), IsProjOver q → letI := algebraΓOfHom q; ∀ (N N₁ N₂ : LB X) (hN : N.IsLB) (h₁ : N₁.IsLB) (h₂ : N₂.IsLB) (a : ℕ) (x : X), IsNef k N → 0 < a → a • cls N hN = cls N₁ h₁ + cls N₂ h₂ → AmpleAt N₁ x → IsNef k N₂ → ∀ (Z : Closeds X) (e : ℕ), IsIrreducible (Z : Set X) → x ∈ Z → 1 ≤ e → topologicalKrullDim (Z : Set X) = e → 1 ≤ interNumRed k Z (fun _ : Fin e => N) := by
  first | exact @GlobalTheory.PosThrough.one_le_interNumRed | exact GlobalTheory.PosThrough.one_le_interNumRed | (intros; apply GlobalTheory.PosThrough.one_le_interNumRed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicCoordinatesEvalZeroFormMemAdmissible
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.MixUniq

open scoped Classical

abbrev ev0 {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ] : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ :=
  LinearMap.proj (R := ℂ) (φ := fun _ : (κ → AF F) => ℂ) 0

theorem adelicCoordinatesEvalZeroForm_mem_admissible {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ] : ev0 (F := F) κ ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g 0 • (BoundedContinuousFunction.evalCLM ℂ 0).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ), fun f => ?_⟩
  simp only [ev0, LinearMap.proj_apply, pureA, ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_comp',
    Function.comp_apply, Pi.smul_apply, SchwartzMap.toBoundedContinuousFunctionCLM_apply,
    BoundedContinuousFunction.evalCLM_apply, smul_eq_mul]
  have h1 : (fun i : κ => InfiniteAdeleRing.ringEquiv_mixedSpace F ((0 : κ → AdeleRing (𝓞 F) F) i).1) = 0 := by
    funext i; exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  have h2 : (fun i : κ => ((0 : κ → AdeleRing (𝓞 F) F) i).2) = 0 := by
    funext i; rfl
  rw [h1, h2, mul_comm]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁}

theorem rho_zero_first (M₁ : Model σ X W₁) (ψ : AddChar (AF F) ℂ) (z : Matrix (Fin n) (Fin d₁) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (hz : (M₁.co.e z).1 = 0) (Ψ : Fn F n d₁) : M₁.co.rho ψ z Ψ 0 = Ψ 0 := by
  simp [Darboux.rho, schr, hz]

theorem rho_first (M₁ : Model σ X W₁) (ψ : AddChar (AF F) ℂ) (y : Fin n × Fin d₁ → AF F) (Ψ : Fn F n d₁) :
    M₁.co.rho ψ (M₁.co.e.symm (y, 0)) Ψ 0 = Ψ y := by
  simp [Darboux.rho, schr]

end GlobalTheory.MixUniq

namespace GlobalTheory.MixUniq

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁}

theorem apply_eq_evaluation_zero (M : Model σ X W) (M₁ : Model σ X W₁) (ψ : AddChar (AF F) ℂ) (ι' : Matrix (Fin d) (Fin d₁) E)
    (S : Fn F n d →ₗ[ℂ] Fn F n d₁)
    (hS : ∀ z, ∀ Φ ∈ schA F (Fin n × Fin d), S (M.co.rho ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F ι')ᵀ) Φ) =
      M₁.co.rho ψ z (S Φ)) (Φ : Fn F n d) (hΦ : Φ ∈ schA F (Fin n × Fin d)) (y : Fin n × Fin d₁ → AF F) :
    S Φ y = ev0 (Fin n × Fin d₁) (S (M.co.rho ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * M₁.co.e.symm (y, 0) * (incM F ι')ᵀ) Φ)) := by
  rw [hS _ Φ hΦ]
  simp only [ev0, LinearMap.proj_apply]
  rw [rho_first]

theorem evAt_zero_comp_eq_of_exp_phase_mul (M : Model σ X W) (M₁ : Model σ X W₁) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (H' : Plane E d d₁)
    (S : Fn F n d →ₗ[ℂ] Fn F n d₁)
    (hS : ∀ z, ∀ Φ ∈ schA F (Fin n × Fin d), S (M.co.rho ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) Φ) =
      M₁.co.rho ψ z (S Φ))
    (hI : ∀ u ∈ (iso0 n H' : Set (Matrix (Fin n) (Fin d) (AE F E))), ∀ Φ ∈ schA F (Fin n × Fin d), S (M.co.rho ψ u Φ) = S Φ)
    (w : (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F))
    (hw : ∃ u ∈ (iso0 n H' : Set (Matrix (Fin n) (Fin d) (AE F E))), ∃ z : Matrix (Fin n) (Fin d₁) (AE F E),
          (M₁.co.e z).1 = 0 ∧ ∀ φ : Fn F n d,
            schr ψ w φ = M.co.rho ψ u (M.co.rho ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) φ))
    (Φ : Fn F n d) (hΦ : Φ ∈ schA F (Fin n × Fin d)) :
    (ev0 (Fin n × Fin d₁) ∘ₗ S) (schr ψ w Φ) = (ev0 (Fin n × Fin d₁) ∘ₗ S) Φ := by
  obtain ⟨u, hu, z, hz, he⟩ := hw
  have h1 := GlobalTheory.HeisSchA.rho_mem_schA M ψ hψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) Φ hΦ
  simp only [LinearMap.comp_apply, ev0, LinearMap.proj_apply]
  rw [he, hI u hu _ h1, hS z Φ hΦ, rho_zero_first M₁ ψ z hz]

end GlobalTheory.MixUniq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjCmHostRootNeSelf
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop

noncomputable section

namespace GlobalTheory.CovTop.WtRead

theorem conj_cmHostRoot_ne_self {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) :
    (starRingEnd ℂ) H.rt0 ≠ H.rt0 := by
  intro h
  have him : H.rt0.im = 0 := Complex.conj_eq_iff_im.1 h
  have hre := congrArg Complex.re H.sqrt_neg_disc_sq
  simp only [pow_two, Complex.mul_re, him, mul_zero, sub_zero, Complex.neg_re, Complex.natCast_re] at hre
  have : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  nlinarith [mul_self_nonneg H.rt0.re]

theorem exists_of_places (D : D7) (τ : D.host.E →+* ℂ) :
    ∃ t, DV.tauEmb D t = τ ∨ conjEmb (DV.tauEmb D t) = τ := by
  have hb : Function.Bijective fun t => InfinitePlace.mk (DV.tauEmb D t) :=
    (Fintype.bijective_iff_injective_and_card _).2
      ⟨Formalism.L2.Geo.Rec.StarEmbeddingNorm.mk_tauEmb_injective D, (Formalism.L2.Geo.Rec.StarEmbeddingNorm.card_places D).symm⟩
  obtain ⟨t, ht⟩ := hb.2 (InfinitePlace.mk τ)
  refine ⟨t, ?_⟩
  rcases InfinitePlace.mk_eq_iff.1 ht with h | h
  · exact Or.inl h
  · right
    rw [← h]
    ext x
    simp [conjEmb, ComplexEmbedding.conjugate_coe_eq]

theorem tauEmb_bijective (D : D7) (Q : Par D) (hQ : Q.PinHost) :
    Function.Bijective (fun t : D.what₂.Tau => (⟨DV.tauEmb D t, hQ.2.2.2 t⟩ : Psi Q.H)) := by
  refine ⟨fun s t h => GlobalTheory.WeightExponents.tauEmb_injective D (congrArg Subtype.val h), fun τ => ?_⟩
  obtain ⟨t, h | h⟩ := exists_of_places D τ.1
  · exact ⟨t, Subtype.ext h⟩
  · exfalso
    have h1 : conjEmb (DV.tauEmb D t) (Q.H.rt : D.host.E) = (starRingEnd ℂ) Q.H.rt0 := by
      simp only [conjEmb, RingHom.coe_comp, Function.comp_apply, hQ.2.2.2 t]
    exact conj_cmHostRoot_ne_self Q.H (h1.symm.trans ((congrArg (fun σ : D.host.E →+* ℂ => σ (Q.H.rt : D.host.E)) h).trans τ.2))

def tauPsi (D : D7) (Q : Par D) (hQ : Q.PinHost) : D.what₂.Tau ≃ Psi Q.H :=
  Equiv.ofBijective _ (tauEmb_bijective D Q hQ)

theorem sigW_add (D : D7) (i : Fin D.R.m) :
    (D.R.sigW ((i : ℕ) + 1)).1 + (D.R.sigW ((i : ℕ) + 1)).2 = D.R.r := by
  have := i.2
  unfold Ranks.sigW Ranks.r
  simp only
  omega

theorem laOf_big (D : D7) (T : CoreJ D) (hT : LawsJ T) (i : Fin D.R.m) (κ : WeightFamilies.Wt D ((i : ℕ) + 1))
    (t : D.what₂.Tau) (τ : Psi T.Q.H) (hτ : τ.1 = DV.tauEmb D t)
    (k : Fin ((T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q)) (a : Fin (D.R.sigW ((i : ℕ) + 1)).1)
    (ha : (a : ℕ) = k) :
    laOf (T.Q.Dw ((i : ℕ) + 1)) (wtA κ) κ.n τ k = (κ.aP t a : ℤ) + ((κ.n / 2 : ℕ) : ℤ) := by
  have hD := hT.pins.2.2.2 ((i : ℕ) + 1) ⟨by omega, i.2⟩
  have hk : (k : ℕ) < (T.Q.Dw ((i : ℕ) + 1)).p := by have := hD.1; have := a.2; omega
  simp only [laOf, weightOf, if_pos hk, hτ]
  rw [GlobalTheory.WeightExponents.wtA_tauEmb hT.pins.1, Formalism.L2.Pj.ext0, dite_eq_left (by omega)]
  have : (⟨(k : ℕ), by omega⟩ : Fin (D.R.sigW ((i : ℕ) + 1)).1) = a := Fin.ext ha.symm
  rw [this]

theorem laOf_small (D : D7) (T : CoreJ D) (hT : LawsJ T) (i : Fin D.R.m) (κ : WeightFamilies.Wt D ((i : ℕ) + 1))
    (t : D.what₂.Tau) (τ : Psi T.Q.H) (hτ : τ.1 = DV.tauEmb D t)
    (k : Fin ((T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q)) (a : Fin (D.R.sigW ((i : ℕ) + 1)).2)
    (ha : (a : ℕ) + k + 1 = D.R.r) :
    laOf (T.Q.Dw ((i : ℕ) + 1)) (wtA κ) κ.n τ k = -(κ.aM t a : ℤ) - ((κ.n / 2 : ℕ) : ℤ) := by
  have hD := hT.pins.2.2.2 ((i : ℕ) + 1) ⟨by omega, i.2⟩
  have hs := sigW_add D i
  have hp := hD.1
  have hq := hD.2.1
  have hk : ¬ (k : ℕ) < (T.Q.Dw ((i : ℕ) + 1)).p := by omega
  simp only [laOf, weightOf, if_neg hk, hτ]
  rw [GlobalTheory.Shares.WtDic.wtA_conj, Formalism.L2.Pj.ext0, dite_eq_left (by omega)]
  have : (⟨(T.Q.Dw ((i : ℕ) + 1)).q - 1 - ((k : ℕ) - (T.Q.Dw ((i : ℕ) + 1)).p), by omega⟩ :
      Fin (D.R.sigW ((i : ℕ) + 1)).2) = a := Fin.ext (by simp only; omega)
  rw [this]

theorem main : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ (i : Fin D.R.m) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)), (T.Q.Dw ((i : ℕ) + 1)).p = (D.R.sigW ((i : ℕ) + 1)).1 ∧ (T.Q.Dw ((i : ℕ) + 1)).q = (D.R.sigW ((i : ℕ) + 1)).2 ∧ Nat.card (Psi T.Q.H) = D.R.f ∧ dimFlag (T.Q.Dw ((i : ℕ) + 1)) = D.R.f * D.R.r.choose 2 ∧ Dom (wtA κ) κ.n ∧ ∃ e : D.what₂.Tau ≃ Psi T.Q.H, (∀ t, (e t).1 = DV.tauEmb D t) ∧ ∀ t (k : Fin ((T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q)), (∀ a : Fin (D.R.sigW ((i : ℕ) + 1)).1, (a : ℕ) = k → laOf (T.Q.Dw ((i : ℕ) + 1)) (wtA κ) κ.n (e t) k = (κ.aP t a : ℤ) + ((κ.n / 2 : ℕ) : ℤ)) ∧ (∀ a : Fin (D.R.sigW ((i : ℕ) + 1)).2, (a : ℕ) + k + 1 = D.R.r → |laOf (T.Q.Dw ((i : ℕ) + 1)) (wtA κ) κ.n (e t) k + (κ.aM t a : ℤ)| ≤ (κ.n : ℤ)) := by
  intro D T hT i κ
  have hP := hT.pins
  have hD := hP.2.2.2 ((i : ℕ) + 1) ⟨by omega, i.2⟩
  have hs := sigW_add D i
  have hcard : Fintype.card (Psi T.Q.H) = D.R.f :=
    (Fintype.card_congr (tauPsi D T.Q hP.1)).symm.trans (Formalism.MainNotions.Lnk.card_Tau D)
  refine ⟨hD.1, hD.2.1, ?_, ?_, Formalism.L2.Pj.dom_wtA κ, tauPsi D T.Q hP.1, fun t => rfl, fun t k => ⟨?_, ?_⟩⟩
  · rw [Nat.card_eq_fintype_card, hcard]
  · rw [dimFlag, Formalism.DegreeFormula.dimFl, hcard, hD.1, hD.2.1, hs, Nat.choose_two_right]
  · exact fun a ha => laOf_big D T hT i κ t _ rfl k a ha
  · intro a ha
    rw [laOf_small D T hT i κ t _ rfl k a ha]
    have h0 : (0 : ℤ) ≤ ((κ.n / 2 : ℕ) : ℤ) := Int.natCast_nonneg _
    have h1 : ((κ.n / 2 : ℕ) : ℤ) ≤ (κ.n : ℤ) := by exact_mod_cast Nat.div_le_self _ _
    rw [show -(κ.aM t a : ℤ) - ((κ.n / 2 : ℕ) : ℤ) + (κ.aM t a : ℤ) = -((κ.n / 2 : ℕ) : ℤ) by ring, abs_neg,
      abs_of_nonneg h0]
    exact h1

end GlobalTheory.CovTop.WtRead

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicOfPowEqOne
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp

theorem exists_algExp {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
    (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw)
    (j : Fin D.R.m) (b : Bool) (hU : Rl.toRealDat.LUnif) (hW : Rl.toRealDat.models_HW)
    (hv : FWT.IsChosenExtremalVector Rl.toRealDat j (sg0 D A3.A) (v₀ j _)) (hK : (S.A ((j : ℕ) + 1)).IsKsForm)
    (x : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1)) {n : ℕ} (z : Fin n → ℂ) (g : Fin n → NX.FmK S ((j : ℕ) + 1))
    (hz : ∀ l, IsAlgebraic ℚ (z l)) (hx : evK YS v₀ hρ i j b x = ∑ l, z l • evW YS v₀ j (g l).val) :
    ∃ (m : ℕ) (a : Fin m → NX.KB S i b) (g' : Fin m → NX.FmK S ((j : ℕ) + 1)),
      x = ∑ k, a k ⊗ₜ[S.Ks] g' k ∧ ∀ k, IsAlgebraic ℚ (ρ.e i b (a k)) := by
  classical
  let L : (Rl.HW j (sg0 D A3.A)).H →ₗ[ℂ] (GA D (Wc D j) → ℂ) :=
    { toFun := fun x => (Rl.HW j (sg0 D A3.A)).e x (v₀ j _)
      map_add' := fun x y => by rw [map_add (f := _)]; rfl
      map_smul' := fun c x => by rw [map_smul]; rfl }
  have hL : LinearMap.ker L = ⊥ :=
    LinearMap.ker_eq_bot.2 fun x y h => GlobalTheory.LiftScalarCompare.eval_inj hW hv h
  obtain ⟨m, bb, -, hKs, hspan, hLL, -⟩ := hK
  let bK : Module.Basis (Fin m) S.Ks ↥(S.A ((j : ℕ) + 1)).WK :=
    (Module.Basis.span hKs).map (LinearEquiv.ofEq _ _ hspan)
  have hbK : ∀ k, ((bK k : ↥(S.A ((j : ℕ) + 1)).WK) : S.WL ((j : ℕ) + 1)) = bb k := fun k => by
    simp [bK, Module.Basis.span_apply]
  let φ : Fin m → (GA D (Wc D j) → ℂ) := fun k => evW YS v₀ j (bb k)
  have hφ : LinearIndependent ℂ φ := by
    have h1 : LinearIndependent D.what₂.LL fun k => (YS.fi j).e (bb k) :=
      hLL.map' (YS.fi j).e.toLinearMap (YS.fi j).e.ker
    exact ((hU j (sg0 D A3.A)).1 m _ h1).map' L hL
  let B : Module.Basis (Fin m) (NX.KB S i b) (NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1)) :=
    Algebra.TensorProduct.basis (NX.KB S i b) bK
  have hB : ∀ k, B k = ((1 : NX.KB S i b) ⊗ₜ[S.Ks] (bK k : NX.FmK S ((j : ℕ) + 1))) := fun k =>
    Algebra.TensorProduct.basis_apply _ _
  have hxe : x = ∑ k, B.equivFun x k ⊗ₜ[S.Ks] (bK k : NX.FmK S ((j : ℕ) + 1)) := by
    conv_lhs => rw [← B.sum_equivFun x]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hB]
    change (B.equivFun x k • (1 : NX.KB S i b)) ⊗ₜ[S.Ks] (bK k : NX.FmK S ((j : ℕ) + 1)) = _
    rw [smul_eq_mul, mul_one]
  refine ⟨m, B.equivFun x, fun k => bK k, hxe, ?_⟩

  have h1 : evK YS v₀ hρ i j b x = ∑ k, ρ.e i b (B.equivFun x k) • φ k := by
    conv_lhs => rw [hxe]
    refine (map_sum (evK YS v₀ hρ i j b) _ _).trans ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    exact (evK_tmul YS v₀ hρ i j b _ _).trans (congrArg _ (congrArg (evW YS v₀ j) (hbK k)))

  let emb : S.Ks →+* ℂ := D.what₂.embLL.comp (algebraMap S.Ks D.what₂.LL)
  let c : Fin n → Fin m → S.Ks := fun l => bK.equivFun (g l)
  have h2 : ∀ l, evW YS v₀ j (g l).val = ∑ k, emb (c l k) • φ k := fun l => by
    have e : (g l).val = ∑ k, algebraMap S.Ks D.what₂.LL (c l k) • bb k := by
      conv_lhs => rw [← bK.sum_equivFun (g l)]
      rw [Submodule.coe_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Submodule.coe_smul, hbK, algebraMap_smul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [evW_smul]
    rfl
  have h3 : ∑ l, z l • evW YS v₀ j (g l).val = ∑ k, (∑ l, z l * emb (c l k)) • φ k := by
    simp_rw [h2, Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  have h4 : ∀ k, ρ.e i b (B.equivFun x k) = ∑ l, z l * emb (c l k) := by
    have h5 : ∑ k, (ρ.e i b (B.equivFun x k) - ∑ l, z l * emb (c l k)) • φ k = 0 := by
      simp_rw [sub_smul, Finset.sum_sub_distrib]
      rw [← h1, hx, h3, sub_self]
    intro k
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hφ _ h5 k)
  intro k
  rw [h4 k]
  have hemb : ∀ y : S.Ks, IsAlgebraic ℚ (emb y) := fun y =>
    (Algebra.IsAlgebraic.isAlgebraic y).algHom emb.toRatAlgHom
  have hmem : ∀ y : ℂ, y ∈ algebraicClosure ℚ ℂ ↔ IsAlgebraic ℚ y := fun y => mem_algebraicClosure_iff
  refine (hmem _).1 ?_
  refine sum_mem fun l _ => mul_mem ?_ ?_
  · exact (hmem _).2 (hz l)
  · exact (hmem _).2 (hemb _)

end GlobalTheory.BigOn.Exp

namespace GlobalTheory.BigOn.Exp

end GlobalTheory.BigOn.Exp

namespace GlobalTheory.BigOn.Exp

end GlobalTheory.BigOn.Exp

namespace GlobalTheory.BigOn.Exp

theorem isAlgebraic_of_pow_eq_one {ζ : ℂ} {n : ℕ} (hn : n ≠ 0) (h : ζ ^ n = 1) : IsAlgebraic ℚ ζ :=
  ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero hn) 1, by simp [h]⟩

end GlobalTheory.BigOn.Exp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalCharactersLinearBar
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalCharactersLinearBar
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.WeilLinA

theorem omA_h_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {A D : Type}
    [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ν β : kˣ →* ℂˣ) (g : GL A k) (Φ : Matrix A D k → ℂ) :
    GlobalTheory.SplitFlip.omA ν β g 1 Φ = GlobalTheory.SplitFlip.omA ν 1 g 1 Φ := by
  funext X; simp [GlobalTheory.SplitFlip.omA]

theorem omA_g_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {A D : Type}
    [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ν β : kˣ →* ℂˣ) (h : GL D k) (Φ : Matrix A D k → ℂ) :
    GlobalTheory.SplitFlip.omA ν β 1 h Φ = GlobalTheory.SplitFlip.omA 1 β 1 h Φ := by
  funext X; simp [GlobalTheory.SplitFlip.omA]

theorem one_mem_UAt {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (Y : Spc F E n) {R : Type} [Zero R] (ev : AF F → R) : (1 : UA σ Y.J) ∈ UAt σ Y ev := by
  intro u _
  simp [mat]

theorem isSmoothChar_inv {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (χ : kˣ →* ℂˣ) (h : GlobalTheory.SmGL.IsSmoothChar χ) : GlobalTheory.SmGL.IsSmoothChar χ⁻¹ := by
  have e : (χ⁻¹).ker = χ.ker := by ext x; simp [MonoidHom.mem_ker]
  unfold GlobalTheory.SmGL.IsSmoothChar at h ⊢
  rw [e]; exact h

theorem isUnitaryChar_inv {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (χ : kˣ →* ℂˣ) (h : GlobalTheory.SmGL.IsUnitaryChar χ) : GlobalTheory.SmGL.IsUnitaryChar χ⁻¹ := by
  intro x
  have := h x
  simp [this]

theorem localOps_eq_omA : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v →
    ∃ (ν₀ β₀ : (Fv F v)ˣ →* ℂˣ) (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ)),
      (∃ t : E →ₐ[F] Fv F v, ν₀ = chrW X.ν t ∨ ν₀ = (chrW X.ν t)⁻¹) ∧
      GlobalTheory.SmGL.IsSmoothChar ν₀ ∧ GlobalTheory.SmGL.IsUnitaryChar ν₀ ∧ GlobalTheory.SmGL.IsSmoothChar β₀ ∧ GlobalTheory.SmGL.IsUnitaryChar β₀ ∧
      Set.BijOn ι (SB (Fin a × Fin (a + a') → Fv F v) : Set _) (SB (Matrix (Fin a) (Fin (a + a')) (Fv F v)) : Set _) ∧
      (∀ g ∈ UAt σ G.V (evFin F v), ∃ g' : GL (Fin a) (Fv F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
        ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (g, 1)) φ φ₁ →
          ι φ₁ = GlobalTheory.SplitFlip.omA ν₀ β₀ g' 1 (ι φ)) ∧
      (∀ g' : GL (Fin a) (Fv F v), ∃ g ∈ UAt σ G.V (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
        ∃ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (g, 1)) φ φ₁ ∧
          ι φ₁ = GlobalTheory.SplitFlip.omA ν₀ β₀ g' 1 (ι φ)) ∧
      (∀ h' : GL (Fin (a + a')) (Fv F v), ∃ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
        ∃ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁ ∧
          ι φ₁ = GlobalTheory.SplitFlip.omA ν₀ β₀ 1 h' (ι φ)) := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hTr v hv
  obtain ⟨t, ι, hι⟩ := GlobalTheory.T.exists_linear_functional_good_place hP F E σ B a a' G X om om' hTr v hv
  obtain ⟨ν₀, hV⟩ := GlobalTheory.T.linear_weil_functional_spherical_value hP F E σ B a a' G X om om' hTr v hv t ι hι (GlobalTheory.T.linear_weil_functional_good_place_equivariant hP F E σ B a a' G X om om' hTr v hv t ι hι)
  obtain ⟨t', ht'⟩ := GlobalTheory.T.linear_weil_functional_local_uniqueness hP F E σ B a a' G X om om' hTr v hv t ι hι ν₀ hV
  obtain ⟨β₀, hW⟩ := GlobalTheory.T.linear_weil_functional_translation_equivariant hP F E σ B a a' G X om om' hTr v hv t ι hι (GlobalTheory.T.linear_weil_functional_unramified_vector hP F E σ B a a' G X om om' hTr v hv t ι hι)
  obtain ⟨hβs, hβu⟩ := GlobalTheory.T.linear_weil_functional_determined_by_unramified hP F E σ B a a' G X om om' hTr v hv t ι hι β₀ hW
  obtain ⟨hs, hu⟩ := GlobalTheory.T.local_character_smooth_unitary hP F E σ B a a' G X om om' hTr v hv t'
  have hνs : GlobalTheory.SmGL.IsSmoothChar ν₀ := by
    rcases ht' with h | h
    · rw [h]; exact hs
    · rw [h]; exact isSmoothChar_inv _ hs
  have hνu : GlobalTheory.SmGL.IsUnitaryChar ν₀ := by
    rcases ht' with h | h
    · rw [h]; exact hu
    · rw [h]; exact isUnitaryChar_inv _ hu
  have hloc := ((GlobalTheory.T.theta_action_exists hP) F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _
    (GlobalTheory.ThK.Check.isPair_of_isTriple hTr).1 v).1
  refine ⟨ν₀, β₀, ι, ⟨t', ht'⟩, hνs, hνu, hβs, hβu, hι.bij, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g', -, hg'⟩ := hV g hg
    exact ⟨g', fun φ hφ φ₁ hφ₁ hA => by rw [hg' φ hφ φ₁ hφ₁ hA, omA_h_one ν₀ β₀]⟩
  · intro g'
    obtain ⟨g, hg, hgt⟩ := GlobalTheory.T.local_unitary_group_surjects_general_linear hP F E σ B a a' G X om om' hTr v hv t g'
    refine ⟨g, hg, fun φ hφ => ?_⟩
    obtain ⟨φ₁, ⟨hφ₁, hA⟩, -⟩ := hloc g hg 1 (one_mem_UAt σ G.W _) φ hφ
    obtain ⟨g'', hg'', hgeq⟩ := hV g hg
    have : g'' = g' := Units.ext (hg''.symm.trans hgt)
    subst this
    exact ⟨φ₁, hφ₁, hA, by rw [hgeq φ hφ φ₁ hφ₁ hA, omA_h_one ν₀ β₀]⟩
  · intro h'
    obtain ⟨h, hh, hht⟩ := GlobalTheory.T.local_unitary_group_surjects_general_linear_right hP F E σ B a a' G X om om' hTr v hv t h'
    refine ⟨h, hh, fun φ hφ => ?_⟩
    obtain ⟨φ₁, ⟨hφ₁, hA⟩, -⟩ := hloc 1 (one_mem_UAt σ G.V _) h hh φ hφ
    obtain ⟨h'', hh'', hheq⟩ := hW h hh
    have : h'' = h' := Units.ext (hh''.symm.trans hht)
    subst this
    exact ⟨φ₁, hφ₁, hA, by rw [hheq φ hφ φ₁ hφ₁ hA, omA_g_one ν₀ β₀]⟩

end GlobalTheory.WeilLinA
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalCharactersLinearBarStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_characters_linear_bar : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v →
    ∃ (ν₀ β₀ : (Fv F v)ˣ →* ℂˣ) (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ)),
      (∃ t : E →ₐ[F] Fv F v, ν₀ = chrW X.ν t ∨ ν₀ = (chrW X.ν t)⁻¹) ∧
      GlobalTheory.SmGL.IsSmoothChar ν₀ ∧ GlobalTheory.SmGL.IsUnitaryChar ν₀ ∧ GlobalTheory.SmGL.IsSmoothChar β₀ ∧ GlobalTheory.SmGL.IsUnitaryChar β₀ ∧
      Set.BijOn ι (SB (Fin a × Fin (a + a') → Fv F v) : Set _) (SB (Matrix (Fin a) (Fin (a + a')) (Fv F v)) : Set _) ∧
      (∀ g ∈ UAt σ G.V (evFin F v), ∃ g' : GL (Fin a) (Fv F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
        ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (g, 1)) φ φ₁ →
          ι φ₁ = GlobalTheory.SplitFlip.omA ν₀ β₀ g' 1 (ι φ)) ∧
      (∀ g' : GL (Fin a) (Fv F v), ∃ g ∈ UAt σ G.V (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
        ∃ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (g, 1)) φ φ₁ ∧
          ι φ₁ = GlobalTheory.SplitFlip.omA ν₀ β₀ g' 1 (ι φ)) ∧
      (∀ h' : GL (Fin (a + a')) (Fv F v), ∃ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
        ∃ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁ ∧
          ι φ₁ = GlobalTheory.SplitFlip.omA ν₀ β₀ 1 h' (ι φ)) := by
  first | exact @GlobalTheory.WeilLinA.localOps_eq_omA | exact GlobalTheory.WeilLinA.localOps_eq_omA | (intros; apply GlobalTheory.WeilLinA.localOps_eq_omA <;> assumption)
end
end
