module

public import Development.WeilBound.CoreStatements.NefModelVolumes.NormGenValLe
public import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.FiniteTypeSections
public import Development.WeilBound.CoreStatements.NefModelVolumes.InjectivityWeightSectionsOf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.WeilHeightArchimedeanContribution
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.LocalUnitMapSurjective
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
theorem PositivityTheory.Xj7N.local_unit_map_surjective : PositivityTheory.Xj7N.NV → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : GlobalTheory.CompHS.TorFlag Y.d.Xo₂ Y.d.c₂) (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)), GoodOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) → GlobalTheory.DegVal.BirOn Y.U Z (wtOf (T.Q.Dw j) u 0) → ∀ σ : Y.d.c₂.F →+* ℂ, GoodEmb Y.d.c₂ σ → ∀ P ∈ holSub (Y.U σ).X (modelWt (Y.U σ) (wtOf (T.Q.Dw j) u 0)), ∃ (m : ℕ) (as : Fin m → ℂ) (fs : Fin m → Rul Y.d.Xo₂ Y.d.c₂), (∀ i, fs i ∈ GlobalTheory.CompanionTheory.Ar.OntoDef.extVanZ TF.X (exOf (T.Q.Dw j) u 0)) ∧ ∀ w ∈ framesOn (Y.U σ) Z, P w.1 w.2 = ∑ i, as i * rdU (Y.U σ) (fs i) w.1 w.2 := by
  intro hNV _ D T j Y e o hY _ Z TF u _ hB σ hσ P hP
  have hU := hY.unf σ hσ
  obtain ⟨κ⟩ := GlobalTheory.HSApp.VanishingBound.keySec D T j Y e o hY σ hσ
  have hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by
    have hr := hU.1
    have h1 : 1 ≤ D.R.r := by
      have := D.R.two_le_m
      unfold Formalism.BasicNotions.Ranks.r
      omega
    omega
  have hdec : ∀ (τ : D.host.E →+* ℂ) (i j' : ℕ), i ≤ j' → j' < (T.Q.Dw j).mult τ →
      (wtOf (T.Q.Dw j) u 0).1 (τ, j') ≤ (wtOf (T.Q.Dw j) u 0).1 (τ, i) := by
    have hne : ∀ (τ : D.host.E →+* ℂ) (m : ℕ), m + 1 < (T.Q.Dw j).mult τ →
        (wtOf (T.Q.Dw j) u 0).1 (τ, m + 1) ≤ (wtOf (T.Q.Dw j) u 0).1 (τ, m) := fun τ m hm => by
      by_contra hlt
      refine hB.1 (LinearMap.ext fun f => ?_)
      have h0 : (f : Rul Y.d.Xo₂ Y.d.c₂) = 0 :=
        GlobalTheory.NonDomVanish.eq_zero_of_lt f.2.1.1 τ ⟨m, by omega⟩ ⟨m + 1, hm⟩ rfl (not_le.1 hlt)
      rw [show f = 0 from Subtype.ext h0, map_zero, map_zero]
    intro τ i j' hij hj'
    induction j', hij using Nat.le_induction with
    | base => exact le_refl _
    | succ n hn ih => exact (hne τ n hj').trans (ih (by omega))
  obtain ⟨m, as, fs, h1, h2⟩ := PositivityTheory.UnitarySelfGeneration.VuOnto.exists_comb hσ hU TF (e := exOf (T.Q.Dw j) u 0) rfl
    (PositivityTheory.UnitarySelfGeneration.VuOnto.tw_of_dec hσ hU κ (fun a n hD => hNV _ _ _ _ _ _ σ hpq a n hD) (wtOf (T.Q.Dw j) u 0) rfl hdec)
    (GlobalTheory.CuspSecFin.mem_SS_of_mem_holSub _ _ hP)
  exact ⟨m, as, fs, h1, fun w hw => h2 w.1 w.2 hw.1⟩
end
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace PositivityTheory.Xj7N
open GlobalTheory GlobalTheory.CompHS GlobalTheory.Adelic
section Generic
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}
variable {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} {D : D7} {V : (c.F →+* ℂ) → HSp D}
  {dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r}
end Generic
section Main
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}
  {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} {D : D7} {V : (c.F →+* ℂ) → HSp D}
  {dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r}
end Main
theorem weil_height_archimedean_contribution : NV → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)) (t : ℝ), GoodOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) → GlobalTheory.DegVal.BirOn Y.U Z (wtOf (T.Q.Dw j) u 0) → NoBase Y.U Z (wtOf (T.Q.Dw j) u 0) → 0 < Y.dg u Z → ∀ (N m : ℕ) (b : Module.Basis (Fin N) Y.d.c₂.F (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) (g : Matrix (Fin N) (Fin m) Y.d.c₂.F) (A : (Y.d.c₂.F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ), IsFrame (normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0)) (latOn Y.U Z (wtOf (T.Q.Dw j) u 0)) b g A → ∀ (σ : Y.d.c₂.F →+* ℂ) (ρ : Om Z →+* ℂ), ρ.comp (algebraMap Y.d.c₂.F (Om Z)) = σ → ∀ τ : ℕ, 0 < τ → ∀ f ∈ smallL Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) τ t, ‖ρ (genVal Z (f : Rul Y.d.Xo₂ Y.d.c₂))‖ ≤ Real.exp (τ * t) * GlobalTheory.Adelic.archSize (A σ) (fun i => ρ (genVal Z ((b i : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) : Rul Y.d.Xo₂ Y.d.c₂))) ^ τ := by
  intro hNV hP D T j Y e o hY hf Z u t hG hB _ _ N m b g A hF σ ρ hρ τ _ f hfs
  have hd : ∀ σ, GoodEmb Y.d.c₂ σ → ∀ g, (Y.dict σ g).2 ∈ ((Y.U σ).X (Y.dict σ g).1).dom := fun σ hσ => by
    obtain ⟨th, hr, hth, hdU⟩ := hY.dictU σ hσ
    exact hdU.2.2.2.1
  have hD : 1 ≤ GlobalTheory.FlagTan.dimFlag (T.Q.Dw j) := by
    have h2 : D.R.r = (T.Q.Dw j).p + (T.Q.Dw j).q :=
      (hY.unf _ (goodEmb_goodOf Y.d.c₂ Y.d.c₂.F.val.toRingHom)).1
    have hm := D.R.two_le_m
    have hk := D.R.m_add_three_le_k
    have h3 : 2 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by
      rw [← h2]; unfold Formalism.BasicNotions.Ranks.r; omega
    exact Nat.mul_pos (by omega) (Nat.choose_pos h3)
  obtain ⟨TF⟩ := DifferentiableLines.nonempty_toroidal_flag_bundle hP.p1 _ _ _ _ Y.d.Xo₂ Y.d.c₂ (GlobalTheory.CompHS.TorFlagEx.one_le_of_dimFlag hD)
  have hspan : ∀ σ, GoodEmb Y.d.c₂ σ → ∀ P ∈ holSub (Y.U σ).X (modelWt (Y.U σ) (wtOf (T.Q.Dw j) u 0)),
      ∃ Q ∈ Submodule.span ℂ (rdU (Y.U σ) '' (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0) : Set (Rul Y.d.Xo₂ Y.d.c₂))),
        ∀ w ∈ framesOn (Y.U σ) Z, P w.1 w.2 = Q w.1 w.2 := fun σ hσ P hPh => by
    obtain ⟨m', as, fs, hfs', hPQ⟩ := _root_.PositivityTheory.Xj7N.local_unit_map_surjective hNV hP D T j Y e o hY hf Z TF u hG hB σ hσ P hPh
    choose g' hg hgf using fun i => GlobalTheory.T.extVan_section_has_cusp_form_match D T j Y e o hY hf Z TF u (fs i) (hfs' i)
    refine ⟨∑ i, as i • rdU (Y.U σ) (g' i), Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨g' i, hg i, rfl⟩), fun w hw => ?_⟩
    rw [hPQ w hw]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => by rw [hgf i σ hσ w hw]
  exact norm_small_le hY.unf hd (AllWt.even_wtOf u 0) hspan hF σ ρ hρ τ t f hfs
end PositivityTheory.Xj7N
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.SmallSectionsInjectiveOfSelfIntersectionBound
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
namespace PositivityTheory.Xj7N.Inj
open GlobalTheory
section Generic
variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
end Generic
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 100000 in
theorem small_sections_injective_of_self_intersection_bound (hK : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 Y.d.c₂.F)) (L : GlobalTheory.HermLB p) (ψ : Om Z →+* X.functionField) (s : latOn Y.U Z (wtOf (T.Q.Dw j) u 0) → L.B.Sec) (t : ℝ), GoodOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) → GlobalTheory.DegVal.BirOn Y.U Z (wtOf (T.Q.Dw j) u 0) → NoBase Y.U Z (wtOf (T.Q.Dw j) u 0) → 0 < Y.dg u Z → GlobalTheory.ImageModel.IsModelOf (normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0)) (latOn Y.U Z (wtOf (T.Q.Dw j) u 0)) (genPoint Z (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) (dimFlag (T.Q.Dw j)) p L ψ s → ∀ i : ℕ, 1 ≤ i → ∀ f ∈ smallL Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) (8 * i) t, ∀ w : latOn Y.U Z (wtOf (T.Q.Dw j) u 0), genVal Z ((w : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) : Rul Y.d.Xo₂ Y.d.c₂) ≠ 0 → ∀ (σ : 𝓞 Y.d.c₂.F →+* ℂ) (y : GlobalTheory.CxPts p σ) (k : L.B.ι) (hy : y ∈ GlobalTheory.CxPts.ptsIn p σ (L.B.U k)), GlobalTheory.Cartier.RegAt (GlobalTheory.Cartier.under y) (ψ (genVal Z (f : Rul Y.d.Xo₂ Y.d.c₂)) * (ψ (genVal Z ((w : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) : Rul Y.d.Xo₂ Y.d.c₂)))⁻¹ ^ (8 * i) * fnOf (L.B.U k) (gen_mem (GlobalTheory.CxPts.mem_ptsIn.1 hy)) ((s w).f k) ^ (8 * i)) → ‖GlobalTheory.Cartier.ratVal (ψ (genVal Z (f : Rul Y.d.Xo₂ Y.d.c₂)) * (ψ (genVal Z ((w : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) : Rul Y.d.Xo₂ Y.d.c₂)))⁻¹ ^ (8 * i) * fnOf (L.B.U k) (gen_mem (GlobalTheory.CxPts.mem_ptsIn.1 hy)) ((s w).f k) ^ (8 * i)) y‖ ^ 2 * Real.exp (-(((8 * i : ℕ) : ℝ) * (L.φ σ).φ k y)) ≤ Real.exp (2 * ((8 * i : ℕ) : ℝ) * t)) : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 Y.d.c₂.F)) (L : GlobalTheory.HermLB p) (ψ : Om Z →+* X.functionField) (s : latOn Y.U Z (wtOf (T.Q.Dw j) u 0) → L.B.Sec) (t : ℝ), GoodOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) → GlobalTheory.DegVal.BirOn Y.U Z (wtOf (T.Q.Dw j) u 0) → NoBase Y.U Z (wtOf (T.Q.Dw j) u 0) → 0 < Y.dg u Z → GlobalTheory.ImageModel.IsModelOf (normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0)) (latOn Y.U Z (wtOf (T.Q.Dw j) u 0)) (genPoint Z (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) (dimFlag (T.Q.Dw j)) p L ψ s → ∀ i : ℕ, 1 ≤ i → (smallL Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) (8 * i) t).encard ≤ ((L.shift (fun _ => t) (fun _ => rfl)).pow (8 * i)).smallSec.encard := by
  intro hP D T j Y e o hY hE Z u X _ p L ψ s t hGood hBir hNB hdg hM i hi
  have hex : ∃ w : latOn Y.U Z (wtOf (T.Q.Dw j) u 0),
      genVal Z ((w : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) : Rul Y.d.Xo₂ Y.d.c₂) ≠ 0 := by
    by_contra hno
    push Not at hno
    have hz : genPoint Z (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) = 0 := by
      have hle : Submodule.span Y.d.c₂.F (latOn Y.U Z (wtOf (T.Q.Dw j) u 0) : Set (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) ≤
          LinearMap.ker (genPoint Z (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) :=
        Submodule.span_le.2 fun v hv => by
          simpa [genPoint] using hno ⟨v, hv⟩
      rw [hGood.2.2] at hle
      exact LinearMap.ext fun v => hle Submodule.mem_top
    have h0 : Y.dg u Z = 0 := by
      show ((compDeg Y.U Z (wtOf (T.Q.Dw j) u 0) : ℕ) : ℝ) = 0
      rw [compDeg, hz, GlobalTheory.CompHt.Test.imageDeg_zero, Nat.cast_zero]
    exact absurd hdg (by rw [h0]; exact lt_irrefl 0)
  obtain ⟨w, hw⟩ : ∃ w, genericPoint X ∈ nonzeroLocus (s w) := by
    have h : genericPoint X ∈ (⨆ w, nonzeroLocus (s w) : X.Opens) := by
      rw [hM.bpf]; trivial
    rw [← SetLike.mem_coe, TopologicalSpace.Opens.coe_iSup, Set.mem_iUnion] at h
    exact h
  obtain ⟨k₀, hk₀⟩ := exists_chart L.isLB (genericPoint X)
  have hw0 : genVal Z ((w : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) : Rul Y.d.Xo₂ Y.d.c₂) ≠ 0 := by
    intro h0
    obtain ⟨w₁, hw₁⟩ := hex
    have hr := hM.ratio w₁ w k₀ hk₀
    have e0 : ψ ((genPoint Z (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) (w : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) = 0 := by
      have : (genPoint Z (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) (w : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) = 0 := h0
      rw [this, map_zero]
    have h1 : ψ ((genPoint Z (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) (w₁ : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) ≠ 0 :=
      (map_ne_zero_iff ψ hM.bij.1).2 hw₁
    exact mul_ne_zero h1 (fnOf_sec_ne_zero hw hk₀) (hr.trans (by rw [e0, zero_mul]))
  have hψinj : Function.Injective ψ := hM.bij.1
  obtain ⟨R, hRinj, hR⟩ := exists_rat_small L (s w) hw (8 * i) t
  have key : ∀ f ∈ smallL Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) (8 * i) t,
      ∃ S ∈ ((L.shift (fun _ => t) (fun _ => rfl)).pow (8 * i)).smallSec, R S = ψ (genVal Z (f : Rul Y.d.Xo₂ Y.d.c₂)) *
          (ψ (genVal Z ((w : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) : Rul Y.d.Xo₂ Y.d.c₂)))⁻¹ ^ (8 * i) := by
    intro f hf
    have hreg := _root_.ChowFormHeightComparison₂.RegularPointExistence.reg_of_val
      hM (8 * i) (genVal Z (f : Rul Y.d.Xo₂ Y.d.c₂))
      (fun la O h1 h2 => _root_.ChowFormHeightComparison₂.RegularPointExistence.fin_small_gen
        Y.U Z _ hGood.2.1 hGood.2.2 hBir la O.valuation h1 h2 (8 * i) f fun v hv => hf.1 la v hv)
      w hw0
    exact hR _ hreg (hK hP D T j Y e o hY hE Z u X p L ψ s t hGood hBir hNB hdg hM i hi f hf w hw0)
  choose! Sf hSf hRf using key
  have hinj : Set.InjOn Sf (smallL Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) (8 * i) t) := by
    intro f hf g hg hfg
    have h1 := (hRf f hf).symm.trans ((congrArg R hfg).trans (hRf g hg))
    have hψw : ψ (genVal Z ((w : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) : Rul Y.d.Xo₂ Y.d.c₂)) ≠ 0 :=
      (map_ne_zero_iff ψ hψinj).2 hw0
    have hc : (ψ (genVal Z ((w : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) : Rul Y.d.Xo₂ Y.d.c₂)))⁻¹ ^ (8 * i) ≠ 0 :=
      pow_ne_zero _ (inv_ne_zero hψw)
    have h2 := hψinj (mul_right_cancel₀ hc h1)
    have h3 : genVal Z ((f : Rul Y.d.Xo₂ Y.d.c₂) - (g : Rul Y.d.Xo₂ Y.d.c₂)) = 0 := by
      rw [map_sub, h2, sub_self]
    exact Subtype.ext (sub_eq_zero.1 (eq_zero_of_genVal' (Submodule.sub_mem _ f.2 g.2) h3))
  rw [← hinj.encard_image]
  exact Set.encard_le_encard (Set.image_subset_iff.2 fun f hf => hSf f hf)
end PositivityTheory.Xj7N.Inj
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.WeilHeightComparisonOfDegreeBound
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 1000000 in
theorem PositivityTheory.Xj7N.weil_height_comparison_of_degree_bound (hA : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)) (t : ℝ), GoodOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) → GlobalTheory.DegVal.BirOn Y.U Z (wtOf (T.Q.Dw j) u 0) → NoBase Y.U Z (wtOf (T.Q.Dw j) u 0) → 0 < Y.dg u Z → ∀ (N m : ℕ) (b : Module.Basis (Fin N) Y.d.c₂.F (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) (g : Matrix (Fin N) (Fin m) Y.d.c₂.F) (A : (Y.d.c₂.F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ), IsFrame (normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0)) (latOn Y.U Z (wtOf (T.Q.Dw j) u 0)) b g A → ∀ (σ : Y.d.c₂.F →+* ℂ) (ρ : Om Z →+* ℂ), ρ.comp (algebraMap Y.d.c₂.F (Om Z)) = σ → ∀ τ : ℕ, 0 < τ → ∀ f ∈ smallL Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) τ t, ‖ρ (genVal Z (f : Rul Y.d.Xo₂ Y.d.c₂))‖ ≤ Real.exp (τ * t) * GlobalTheory.Adelic.archSize (A σ) (fun i => ρ (genVal Z ((b i : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) : Rul Y.d.Xo₂ Y.d.c₂))) ^ τ) : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 Y.d.c₂.F)) (L : GlobalTheory.HermLB p) (ψ : Om Z →+* X.functionField) (s : latOn Y.U Z (wtOf (T.Q.Dw j) u 0) → L.B.Sec) (t : ℝ), GoodOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) → GlobalTheory.DegVal.BirOn Y.U Z (wtOf (T.Q.Dw j) u 0) → NoBase Y.U Z (wtOf (T.Q.Dw j) u 0) → 0 < Y.dg u Z → GlobalTheory.ImageModel.IsModelOf (normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0)) (latOn Y.U Z (wtOf (T.Q.Dw j) u 0)) (genPoint Z (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) (dimFlag (T.Q.Dw j)) p L ψ s → ∀ i : ℕ, 1 ≤ i → ∀ f ∈ smallL Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) (8 * i) t, ∀ w : latOn Y.U Z (wtOf (T.Q.Dw j) u 0), genVal Z ((w : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) : Rul Y.d.Xo₂ Y.d.c₂) ≠ 0 → ∀ (σ : 𝓞 Y.d.c₂.F →+* ℂ) (y : GlobalTheory.CxPts p σ) (k : L.B.ι) (hy : y ∈ GlobalTheory.CxPts.ptsIn p σ (L.B.U k)), GlobalTheory.Cartier.RegAt (GlobalTheory.Cartier.under y) (ψ (genVal Z (f : Rul Y.d.Xo₂ Y.d.c₂)) * (ψ (genVal Z ((w : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) : Rul Y.d.Xo₂ Y.d.c₂)))⁻¹ ^ (8 * i) * fnOf (L.B.U k) (gen_mem (GlobalTheory.CxPts.mem_ptsIn.1 hy)) ((s w).f k) ^ (8 * i)) → ‖GlobalTheory.Cartier.ratVal (ψ (genVal Z (f : Rul Y.d.Xo₂ Y.d.c₂)) * (ψ (genVal Z ((w : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) : Rul Y.d.Xo₂ Y.d.c₂)))⁻¹ ^ (8 * i) * fnOf (L.B.U k) (gen_mem (GlobalTheory.CxPts.mem_ptsIn.1 hy)) ((s w).f k) ^ (8 * i)) y‖ ^ 2 * Real.exp (-(((8 * i : ℕ) : ℝ) * (L.φ σ).φ k y)) ≤ Real.exp (2 * ((8 * i : ℕ) : ℝ) * t) := by
  intro hP D T j Y e o hY hE Z u X _ p L ψ s t hGood hBir hNB hdg hM i hi f hf w hw σ y k hy hr
  exact ChowFormHeightComparison₂.GenericDenseBound.norm_le_of_emb hM (genVal Z (f : Rul Y.d.Xo₂ Y.d.c₂)) (8 * i) t
    (fun N m b g A hF σ' ρ hρ => hA hP D T j Y e o hY hE Z u t hGood hBir hNB hdg N m b g A hF σ' ρ hρ
      (8 * i) (by omega) f hf) w hw σ y k hy hr
end
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
theorem PositivityTheory.Xj7N.small_sections_injective : PositivityTheory.Xj7N.NV → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 Y.d.c₂.F)) (L : GlobalTheory.HermLB p) (ψ : Om Z →+* X.functionField) (s : latOn Y.U Z (wtOf (T.Q.Dw j) u 0) → L.B.Sec) (t : ℝ), GoodOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) → GlobalTheory.DegVal.BirOn Y.U Z (wtOf (T.Q.Dw j) u 0) → NoBase Y.U Z (wtOf (T.Q.Dw j) u 0) → 0 < Y.dg u Z → GlobalTheory.ImageModel.IsModelOf (normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0)) (latOn Y.U Z (wtOf (T.Q.Dw j) u 0)) (genPoint Z (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) (dimFlag (T.Q.Dw j)) p L ψ s → ∀ i : ℕ, 1 ≤ i → (smallL Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) (8 * i) t).encard ≤ ((L.shift (fun _ => t) (fun _ => rfl)).pow (8 * i)).smallSec.encard :=
  fun hNV => _root_.PositivityTheory.Xj7N.Inj.small_sections_injective_of_self_intersection_bound (_root_.PositivityTheory.Xj7N.weil_height_comparison_of_degree_bound (_root_.PositivityTheory.Xj7N.weil_height_archimedean_contribution hNV))
end
