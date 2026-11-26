module

public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDeltaDatumHigherLevel
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsEquivariantFunOnSpanningFamilies
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ShortThetaSeriesDominantWeightIsCuspForm
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLevelMulSplit
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSectionOneClassSeriesDescends
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaClassSumDominantWeightIsCuspForm
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RuleBaseChangeSectionValuesSemilinear
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsReducedIntegralBasisHarmonicPolynomials

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UnfoldingConstantTermsAgreeAtGoodEmbeddings
open AlgebraicGeometry CategoryTheory NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.ClsVal
open scoped Classical

namespace GlobalTheory.Dict


set_option maxHeartbeats 1000000 in
theorem holSub0_le_span_cusp : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), 1 ≤ r → l.A = 1 → (∀ σ, GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ σ, GoodEmb c σ → (∀ k k', ((U σ).X k).Gm = ((U σ).X k').Gm ∧ ((U σ).X k).ξ0 = ((U σ).X k').ξ0) → (∀ k, HasPrinc ((U σ).X k) l.M) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → LastPos Dw a → 4 * (Module.finrank ℚ E * r) + 4 ≤ n → (∀ k, ChiOne ((U σ).X k) (Formalism.L2.PjFree.laU (U σ) a n k)) → GlobalTheory.Dict.holSub0 (U σ).X (Formalism.L2.PjFree.laU (U σ) a n) ≤ Submodule.span ℂ (Formalism.L2.PjFree.rdU (U σ) '' (Formalism.L2.PjFree.cusp Xo c U a n : Set (Rul Xo c))) := by
  intro hC E _ _ _ H Dw l Xo c r U hr hA hU σ hσ hG hP a n hdom hlast hn hχ
  have hrk : r = Dw.p + Dw.q := (hU σ hσ).1
  have h1 : 1 ≤ Dw.p + Dw.q := hrk ▸ hr
  have hL : Out.Laws := GlobalTheory.firstFiveLaws.1
  have hB : Out.SecBaseChangeSt := hL.secBaseChange
  have hnr : Dw.p + Dw.q ≤ n := by
    have h0 : 0 < Module.finrank ℚ E := Module.finrank_pos
    have : r ≤ Module.finrank ℚ E * r := Nat.le_mul_of_pos_left r h0
    omega
  have hd : ∃ d : DeltaDat Xo c n, d.IsLev ∧ (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) ∧ d.cδ = 1 ∧
      d.pd = 1 ∧ d.l₂.A = l.A ∧ ∃ ph x₀, d.PhiPin ph 1 x₀ := by
    obtain ⟨d, e1, -, e2, -, -, hδ, hlev, hnab⟩ :=
      GlobalTheory.LevelCover.exists_deltaDat_isLev E H Dw l Xo c h1 n 1 ⊤ l Xo c rfl
        ⟨dvd_rfl, le_rfl, dvd_rfl⟩ (Nat.mul_one _).symm (Nat.coprime_one_left _) (Ideal.mul_top _).symm
        (top_sup_eq _)
    obtain ⟨f, ph, x₀, hpin⟩ := GlobalTheory.exists_phiPin_of_character E H Dw l Xo c n d hlev hnr 1
    exact ⟨{ d with φδ := f }, hlev, hnab, hδ, e1, congrArg (·.A) e2, ph, x₀, hpin⟩
  obtain ⟨d, hlev, hnab, hδ, hpe, hAe, ph, x₀, hpin⟩ := hd
  have hT : AllTest d.Xo₂ d.c₂ := GlobalTheory.Frames.allTest_of_secBaseChange hB E H Dw d.l₂ d.Xo₂ d.c₂
  obtain ⟨_, nab, -⟩ := GlobalTheory.CanonConn.exists_isNab hL E H Dw l Xo c
  have hunit : UnitC d := fun A y => by
    have : evR d.Xo₂ d.c₂ d.cδ y = 1 := by
      rw [hδ]
      exact evalAt_one _ _ _ (hT _ _)
    rw [this, norm_one]
  have h3 : ¬ 3 ∣ d.pd := by rw [hpe]; decide
  have htie : d.PsiTie 1 := by
    intro k g ρ _ _ _ _ K _ _ _ y y' _
    have h : ∀ z : FrPt d.Xo₂ d.c₂ K, evR d.Xo₂ d.c₂ d.cδ z = 1 := fun z => by
      rw [hδ]
      exact evalAt_one _ _ _ (hT _ _)
    change evR d.Xo₂ d.c₂ d.cδ y' =
      algebraMap d.c₂.F K (d.eF ((1 : c.Fˣ) : c.F)) * evR d.Xo₂ d.c₂ d.cδ y
    rw [h y, h y']
    simp
  have htot : ShortValTot Xo c nab 1 0 a n d :=
    GlobalTheory.shortValTot_of_pinned hL hC E H Dw l Xo c n d (GlobalTheory.levelMaps_closed hL E H Dw h1)
      (GlobalTheory.Frames.algebraic_laws hB E H Dw l Xo c).2.2.1 (GlobalTheory.Frames.allTest_of_secBaseChange hB E H Dw l Xo c)
      (GlobalTheory.Frames.algebraic_laws hB E H Dw _ _ _).2.2.1 hT hlev hAe hnab (fun _ => ⟨ph, 1, x₀, hpin, htie⟩)
      nab 1 0 a
  refine (GlobalTheory.T.cuspForms_vanishing_off_frames_le_span_shortTheta hC E H Dw l Xo c n d σ r (U σ) hσ (hU σ hσ) hr hA hG hP hlev hnab hunit h3
    (fun _ => ⟨ph, 1, x₀, hpin⟩) nab 1 0 a Nat.one_pos hdom hn hχ htot).trans
    (Submodule.span_mono (Set.image_mono ?_))
  exact GlobalTheory.T.short_thetaSeries_dominant_weight_isCuspForm hC E H Dw l Xo c n d r U hr hU hlev hnab hunit (fun _ => ⟨ph, 1, x₀, hpin⟩) nab 1 0 a hdom hlast

end GlobalTheory.Dict
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSpanningHypotheses
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.SpanInhab

theorem exists_imag_neg {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    ∃ ξ : E, cc ξ = -ξ ∧ ξ ≠ 0 ∧ ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → (τ ξ).im < 0 := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have key : ∀ z : ℂ, z ^ 2 = -(H.d : ℂ) → z.re = 0 ∧ z.im ≠ 0 := by
    intro z hz
    have h1 := congrArg Complex.re hz
    have h2 := congrArg Complex.im hz
    simp [sq] at h1 h2
    have him : z.im ≠ 0 := by
      intro h; rw [h] at h1; nlinarith [mul_self_nonneg z.re]
    refine ⟨?_, him⟩
    have : z.re * z.im = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_right him
  have hE : ((H.rt : E)) ^ 2 = -(H.d : E) := by
    have := congrArg (fun z : 𝓞 E => (z : E)) H.rt_sq
    simpa using this
  have hcc : cc (H.rt : E) = -(H.rt : E) := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    have hk := key (τ (H.rt : E)) (by rw [← map_pow, hE, map_neg, map_natCast])
    have : τ (cc (H.rt : E)) = starRingEnd ℂ (τ (H.rt : E)) := IsCMField.complexEmbedding_complexConj E τ _
    rw [this, map_neg]
    apply Complex.ext <;> simp [hk.1]
  have h0 : (H.rt : E) ≠ 0 := by
    intro h
    rw [h] at hE
    have : (H.d : E) = 0 := by linear_combination hE
    exact H.d_prime.ne_zero (by exact_mod_cast this)
  rcases lt_or_gt_of_ne (key _ H.sqrt_neg_disc_sq).2 with h | h
  · exact ⟨H.rt, hcc, h0, fun τ hτ => hτ ▸ h⟩
  · refine ⟨-(H.rt : E), ?_, neg_ne_zero.2 h0, fun τ hτ => by rw [map_neg, hτ]; simpa using h⟩
    have : cc (-(H.rt : E)) = -cc (H.rt : E) := by simp [cc]
    rw [this, hcc]

end GlobalTheory.SpanInhab
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsCuspIsThClsDUnique
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EvRSumSmulFin
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FieldBC

namespace GlobalTheory

theorem evR_sum_smul_fin {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    (Xo : Moduli Dw l) (c : Coeff l) {ι : Type} (s : Finset ι) (t : ι → c.F) (f : ι → Rul Xo c)
    {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    evR Xo c (∑ i ∈ s, t i • f i) y = ∑ i ∈ s, algebraMap c.F S (t i) * evR Xo c (f i) y := by
  classical
  have hL : ∑ i ∈ s, t i • f i = ∑ j : Fin s.card, t (s.equivFin.symm j) • f (s.equivFin.symm j) := by
    rw [← Finset.sum_coe_sort s]
    exact (Equiv.sum_comp s.equivFin.symm (fun i : s => t i • f i)).symm
  have hR : ∑ i ∈ s, algebraMap c.F S (t i) * evR Xo c (f i) y =
      ∑ j : Fin s.card, algebraMap c.F S (t (s.equivFin.symm j)) * evR Xo c (f (s.equivFin.symm j)) y := by
    rw [← Finset.sum_coe_sort s]
    exact (Equiv.sum_comp s.equivFin.symm (fun i : s => algebraMap c.F S (t i) * evR Xo c (f i) y)).symm
  rw [hL, hR]
  exact Formalism.L2.Pj.evR_sum_smul y (fun j => t (s.equivFin.symm j)) (fun j => f (s.equivFin.symm j))

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSectionOfLevelCoverThetaClassSum
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSectionOfLevelCoverThetaClassSum
open AlgebraicGeometry CategoryTheory NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.ClsVal
open scoped Classical

theorem GlobalTheory.exists_sec_isThClsD : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), d.IsLev → d.l₂.A = l.A → (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → ∀ (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ), d.PsiTie ψ → ∀ (Cl : Type) [Fintype Cl] (w : Cl → (Fin n → LevQ Dw d.l₂) → c.F) (La : Cl → GenLat E n) (Nc gam : Cl → ℕ) (vol : c.F) (ep : Cl → c.F) (Vs : Type) [AddCommGroup Vs] [Module c.F Vs] (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (xs : Cl → Vs) (a : (E →+* ℂ) × ℕ → ℕ), (∀ j, DatEq d ψ (w j)) → LatsOK d.l₂.M La Nc → (∀ j, io (xs j) ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) → ∃ f ∈ sec Xo c a n, IsThClsD Xo c d w La Nc gam vol ep io xs f := by
  intro hCI E _ _ _ H Dw l Xo c n d hlev hA hN ψ hψ Cl _ w La Nc gam vol ep Vs _ _ io xs a hw hL hio
  choose f hf hth using fun j : Cl => GlobalTheory.T.exists_section_oneClass_series_descends hCI E H Dw l Xo c n d hlev hA hN ψ hψ (w j) (hw j) (La j) (Nc j)
    (hL j).1 (hL j).2.1 (hL j).2.2 a (io (xs j)) (hio j)
  refine ⟨∑ j, (vol * ((gam j : c.F))⁻¹ * ep j) • f j,
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hf j), ?_⟩
  intro k _ _ _ _ hk y y₂ hy
  choose vc hvc hev using fun j => hth j k hk y y₂ hy
  refine ⟨fun j => vc j (), fun j => hvc j (), ?_⟩
  rw [GlobalTheory.evR_sum_smul_fin, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hev j]
  simp only [Finset.univ_unique, Finset.sum_singleton, Nat.cast_one, inv_one, mul_one, map_one, one_mul]
  ring
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSectionOfLevelCoverThetaClassSumStatement
open AlgebraicGeometry CategoryTheory NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.ClsVal
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_of_levelCover_thetaClassSum : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), d.IsLev → d.l₂.A = l.A → (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → ∀ (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ), d.PsiTie ψ → ∀ (Cl : Type) [Fintype Cl] (w : Cl → (Fin n → LevQ Dw d.l₂) → c.F) (La : Cl → GenLat E n) (Nc gam : Cl → ℕ) (vol : c.F) (ep : Cl → c.F) (Vs : Type) [AddCommGroup Vs] [Module c.F Vs] (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (xs : Cl → Vs) (a : (E →+* ℂ) × ℕ → ℕ), (∀ j, DatEq d ψ (w j)) → LatsOK d.l₂.M La Nc → (∀ j, io (xs j) ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) → ∃ f ∈ sec Xo c a n, IsThClsD Xo c d w La Nc gam vol ep io xs f := by
  first | exact @GlobalTheory.exists_sec_isThClsD | exact GlobalTheory.exists_sec_isThClsD | (intros; apply GlobalTheory.exists_sec_isThClsD <;> assumption)
end
end

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ClsVal

namespace GlobalTheory.ClsVal

theorem exists_cusp_isThClsD_unique : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.Pj.Unf Xo c σ r), 1 ≤ r → (∀ σ, GoodEmb c σ → Formalism.L2.Pj.IsUnf (U σ)) → l.A = 1 → CovPin Xo c (fun _ : Unit => d) → GlobalTheory.Dict.UnitC d → ∀ (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ), d.PsiTie ψ → ∀ (Cl : Type) [Fintype Cl] (w : Cl → (Fin n → LevQ Dw d.l₂) → c.F) (La : Cl → GenLat E n) (Nc gam : Cl → ℕ) (bad : ℕ) (vol : c.F) (ep : Cl → c.F) (Vs : Type) [AddCommGroup Vs] [Module c.F Vs] (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (a : (E →+* ℂ) × ℕ → ℕ), Dom a n → LastPos Dw a → (∀ j, DatEq d ψ (w j)) → RepsOK (l := d.l₂) bad La Nc gam → LinearMap.range io ≤ Submodule.span c.F (HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) → ∀ xs : Cl → Vs, ∃ f ∈ Formalism.L2.Pj.cusp Xo c U a n, IsThClsD Xo c d w La Nc gam vol ep io xs f ∧ ∀ f' ∈ sec Xo c a n, IsThClsD Xo c d w La Nc gam vol ep io xs f' → f' = f := by
  intro hci E _ _ _ H Dw l Xo c n d r U hr hU hA hcov hunit ψ hψ Cl _ w La Nc gam bad vol ep Vs _ _ io a hD hL hw hreps
    hio xs
  obtain ⟨hlev, hA₂, hnab⟩ := hcov ()
  have hLat : LatsOK d.l₂.M La Nc := fun k => ⟨(hreps k).1, (hreps k).2.2.1, (hreps k).2.2.2.1⟩
  have hP : ∀ v, io v ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) := fun v =>
    GlobalTheory.HarmBasis.mem_HHa_of_mem_span subset_rfl (hio (LinearMap.mem_range_self io v))
  obtain ⟨f, hf, hcls⟩ := GlobalTheory.T.exists_section_of_levelCover_thetaClassSum hci E H Dw l Xo c n d hlev (hA₂.trans hA.symm) hnab ψ hψ Cl w La Nc gam vol ep
    Vs io xs a hw hLat fun j => hP _
  refine ⟨f, ?_, hcls, fun f' hf' hcls' => ?_⟩
  · rw [← Formalism.L2.PjFree.cusp_ofPj]
    exact GlobalTheory.T.thetaClassSum_dominant_weight_isCuspForm hci E H Dw l Xo c n d r (fun σ => Formalism.L2.PjFree.Unf.ofPj (U σ)) hr
      (fun σ hσ => (Formalism.L2.PjFree.isUnf_ofPj (U σ)).2 (hU σ hσ)) hA hlev hA₂ hnab hunit Cl w La Nc gam vol ep Vs io xs a
      hD hL hLat (fun j => hP _) f hf hcls
  · exact GlobalTheory.ClassSumUnique.isThClsD_unique hci E H Dw l Xo c n d Cl w La Nc gam vol ep Vs io hlev hnab hLat a hP xs a n
      f' hf' f hf hcls' hcls

end GlobalTheory.ClsVal
end
