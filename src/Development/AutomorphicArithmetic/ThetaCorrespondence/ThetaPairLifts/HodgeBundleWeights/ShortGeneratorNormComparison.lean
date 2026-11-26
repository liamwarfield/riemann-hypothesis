module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsGoodCoverAtMinimalLevel
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ProportionalityPrincipleCompactification

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ShortSpanCompositionClosed
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.LogSumBadPrimesBoundOfCovering
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions.TH
set_option maxHeartbeats 400000
noncomputable section
namespace GlobalTheory.BadLogCov
theorem log_sum_bad_primes_le_sq : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ Lb : ℝ, 1 ≤ Lb → Real.log Y.d.l₂.M ≤ 30 * Lb → fieldSz D.host.E ≤ 3 * Lb → Real.log (D.R.f * D.R.r) ≤ Lb → GlobalTheory.FlatTw.logSum (GlobalTheory.FlatTw.badPrimes T.Q.H Y.d.l₂) ≤ C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 := by
  intro _
  refine ⟨37, by norm_num, fun D T hT j hj Y e o hY Lb hL hM hE hfr => ?_⟩
  have hQ := hT.pins
  have hM0 : Y.d.l₂.M ≠ 0 := by have := Y.d.l₂.three_le; omega
  have h1 := UpperTheory.KR.sum_log_bad_le D.host.toHostAx Y.d.l₂.M (badPrimes T.Q.H Y.d.l₂) hM0 fun p hp => by
    obtain ⟨hp, h'⟩ := mem_badPrimes.1 hp
    refine ⟨hp, ?_⟩
    rcases h' with h' | h' | h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl (h'.trans hQ.1.1))
    · exact Or.inr (Or.inr (Or.inl h'))
    · exact Or.inr (Or.inr (Or.inr h'))
    · rw [hY.lev.2] at h'
      exact absurd (Nat.dvd_one.1 h') hp.ne_one
  have hrd : Real.log D.host.rd ≤ fieldSz D.host.E := by
    refine le_trans (le_of_eq ?_) (log_rd_le_fieldSz D.host.E)
    unfold Formalism.HC.HostRaw.rd
    rw [Real.log_rpow (abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero D.host.E))]; ring
  have hsum : GlobalTheory.FlatTw.logSum (GlobalTheory.FlatTw.badPrimes T.Q.H Y.d.l₂) ≤ 37 * Lb := by
    refine le_trans h1 ?_; linarith
  have hn : 0 < D.R.n := D.R.ord_pos
  have h1' := D.R.two_le_m
  have h2' := D.R.m_add_three_le_k
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast (by unfold Ranks.f; omega : 1 ≤ D.R.f)
  have hr : (1 : ℝ) ≤ D.R.r := by exact_mod_cast (by unfold Ranks.r; omega : 1 ≤ D.R.r)
  have hfr1 : (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.r := one_le_mul_of_one_le_of_one_le hf hr
  have hX : Lb ≤ ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 := by
    have a : Lb ≤ (D.R.f : ℝ) * D.R.r * Lb := le_mul_of_one_le_left (by linarith) hfr1
    have b : (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.r * Lb := hL.trans a
    nlinarith
  linarith
end GlobalTheory.BadLogCov
end
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions.TH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_sum_bad_primes_bound_of_covering : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ Lb : ℝ, 1 ≤ Lb → Real.log Y.d.l₂.M ≤ 30 * Lb → fieldSz D.host.E ≤ 3 * Lb → Real.log (D.R.f * D.R.r) ≤ Lb → GlobalTheory.FlatTw.logSum (GlobalTheory.FlatTw.badPrimes T.Q.H Y.d.l₂) ≤ C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 := by
  first | exact @_root_.GlobalTheory.BadLogCov.log_sum_bad_primes_le_sq | exact _root_.GlobalTheory.BadLogCov.log_sum_bad_primes_le_sq | (intros; apply _root_.GlobalTheory.BadLogCov.log_sum_bad_primes_le_sq <;> assumption)
end
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions.TH
namespace GlobalTheory.ShortSpanComp
end GlobalTheory.ShortSpanComp
namespace GlobalTheory.ShortSpanComp
set_option maxHeartbeats 2000000 in
theorem short_span_comp_mem : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ Lb : ℝ, 1 ≤ Lb → Real.log Y.d.l₂.M ≤ 30 * Lb → fieldSz D.host.E ≤ 3 * Lb → Real.log (D.R.f * D.R.r) ≤ Lb → o ≤ 391 * (D.R.f * D.R.r * Lb) ^ 2 → ∀ c₁ : ℝ, GlobalTheory.FlatLine.FlatExistsAt Y.U (xiR D) c₁ → |c₁| ≤ 9 * D.R.r * Lb → ∀ la : AllWt.Weight (T.Q.Dw j), (∀ τ, Antitone (la τ)) → (∀ τ, ((8 * D.R.f * D.R.r + 10 : ℕ) : ℤ) ≤ gap (la τ) ((T.Q.Dw j).p - 1)) → Real.log (∑ τ, ∑ k, |(la τ k : ℝ)|) ≤ 10 * Lb → ∀ Z, ∃ s : Set (cuspOn Y.U Z (wtOf (T.Q.Dw j) la 0)), s ⊆ (latOn Y.U Z (wtOf (T.Q.Dw j) la 0) : Set (cuspOn Y.U Z (wtOf (T.Q.Dw j) la 0))) ∧ Submodule.span Y.d.c₂.F s = ⊤ ∧ ∀ y ∈ s, ∀ σ, normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) la 0) σ y ≤ Real.exp (C * (((D.R.f : ℝ) * D.R.r * Lb) ^ 3 * (∑ τ, ∑ k, |(la τ k : ℝ)|) + ((D.R.f : ℝ) * D.R.r * Lb) ^ 5)) := by
  intro hP
  obtain ⟨CG, hCG0, hGM⟩ := _root_.GlobalTheory.CovGmin.minimal_level_cover_is_good hP
  obtain ⟨CB, hCB0, hBad⟩ := _root_.GlobalTheory.T.log_sum_bad_primes_bound_of_covering hP
  refine ⟨11 * CG + CB + 500, by positivity, ?_⟩
  intro D T hT j hp hq hE hj Y e o hY Lb hLb hM hEs hfr ho c₁ hc₁ hc₁b la hanti hgap hla Z
  have hL := GlobalTheory.LawsDeep.laws_deep D T j Y e o hT hj hY
  have hrk : (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r := by
    obtain ⟨h1, h2, -⟩ := hT.pins.2.2.2 j hj
    obtain ⟨hj1, hj2⟩ := hj
    rw [h1, h2]; unfold Formalism.BasicNotions.Ranks.sigW Formalism.BasicNotions.Ranks.r; simp only; omega
  have hcard : Nat.card (Psi T.Q.H) = D.R.f := by
    have hpin := hT.pins.1
    have hb : Function.Bijective (fun t : D.what₂.Tau => (⟨DV.tauEmb D t, hpin.2.2.2 t⟩ : Psi T.Q.H)) :=
      ⟨fun s t h => GlobalTheory.WeightExponents.tauEmb_injective D (congrArg Subtype.val h), fun τ => by
        obtain ⟨t, ht⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.exists_tau_of_inPsi T.Q hpin τ.1 τ.2
        exact ⟨t, Subtype.ext ht.symm⟩⟩
    rw [← Nat.card_eq_of_bijective _ hb, Nat.card_eq_fintype_card, D.what₂.card_Tau]
  have hf1 : 1 ≤ D.R.f := by
    have hn : 0 < D.R.ord := D.R.ord_pos
    show 1 ≤ 2 * D.R.ord
    omega
  have hr1 : 1 ≤ D.R.r := by omega
  set m : ℕ := D.R.f * D.R.r + 1 with hm
  have hgap' : ∀ τ, ((2 * (4 * m) + 2 : ℕ) : ℤ) ≤ gap (la τ) ((T.Q.Dw j).p - 1) := fun τ => by
    have h := hgap τ
    have e8 : 2 * (4 * m) + 2 = 8 * D.R.f * D.R.r + 10 := by rw [hm]; ring
    rw [e8]; exact h
  obtain ⟨a, hDom, hlaOf, hbig⟩ := GlobalTheory.T.exists_thetaWeight_exponents_of_large_gap D.host.E T.Q.H (T.Q.Dw j) (4 * m) la hp hanti hgap'
  have hn2 : 2 * (4 * m) / 2 = 4 * m := by omega
  set n₀ : Psi T.Q.H → ℤ := fun τ => 1 + ((4 * m : ℕ) : ℤ) - la τ ⟨(T.Q.Dw j).p - 1, by omega⟩ with hn₀
  obtain ⟨hsizeK, hN0⟩ := GlobalTheory.T.thetaWeight_and_flatExponent_size_bound D.host.E T.Q.H (T.Q.Dw j) a (2 * (4 * m)) la n₀ hp hlaOf
    (fun τ => by rw [hn2])
  have hrkR : (((T.Q.Dw j).p + (T.Q.Dw j).q : ℕ) : ℝ) = D.R.r := by exact_mod_cast hrk
  rw [hrkR, hcard, hn2] at hsizeK
  rw [hcard, hn2] at hN0
  have hcast : ((4 * m : ℕ) : ℝ) + 1 = 4 * ((D.R.f : ℝ) * D.R.r + 1) + 1 := by rw [hm]; push_cast; ring
  rw [hcast] at hsizeK hN0
  have hS : ∃ N : ℕ, (∑ τ, ∑ k, |(la τ k : ℝ)|) = N :=
    ⟨∑ τ, ∑ k, (la τ k).natAbs, by push_cast [Nat.cast_natAbs]; rfl⟩
  have hsz0 : 0 ≤ sizeK (T.Q.Dw j) a (2 * (4 * m)) := sizeK_nonneg _ _ _
  have hsz : Real.log (sizeK (T.Q.Dw j) a (2 * (4 * m))) ≤ 20 * Lb :=
    GlobalTheory.T.log_le_twenty_mul_of_bounds D.R.f D.R.r Lb _ _ (by exact_mod_cast hf1) (by exact_mod_cast hr1) hLb hfr hS hla hsz0
      (by rw [mul_comm (D.R.r : ℝ) (D.R.f : ℝ)] at hsizeK ⊢; linarith)
  obtain ⟨s₀, hs₀lat, hs₀span, hs₀bd⟩ := hGM D T hT j hp hq hE hj Y e o hY Lb hLb hM hEs hfr ho a (2 * (4 * m))
    hDom ⟨4 * m, by ring⟩ (by rw [hm]; nlinarith) hbig hsz
  obtain ⟨hKey, hth⟩ := GlobalTheory.T.exists_keyUnit_pow_twistingSection_on_component D.host.E T.Q.H (T.Q.Dw j) Y.d.l₂ Y.d.Xo₂ Y.d.c₂ D.R.r Y.U (xiR D) hL.unf hL.xi hL.geo
    hL.pos hL.good
  obtain ⟨t₁, ht₁lo, ht₁c⟩ := hth Z m
  have hUn := _root_.GlobalTheory.T.unramified_points_of_deep_cover hP D T j Y e o hT hj hY
  have hPts : HasPts Y.U Z := GlobalTheory.FlatLine.hasPts Y.U hL.pos hL.good hL.unf Z
  obtain ⟨t₂, ht₂lo, ht₂c⟩ := GlobalTheory.T.exists_short_integral_flatLine_twistingSection D.host.E T.Q.H (T.Q.Dw j) Y.d.l₂ Y.d.Xo₂ Y.d.c₂ D.R.r Y.U (xiR D)
    (badPrimes T.Q.H Y.d.l₂) hKey hL.unf hL.pos badPrimes_prime hUn c₁ hc₁ Z hPts (fun τ => -n₀ τ)
  have hW := cuspW_laOf (Dw := T.Q.Dw j) Y.U hL.unf a (2 * (4 * m)) ⟨4 * m, by ring⟩
  have hs₀c : Subtype.val '' s₀ ⊆ (cuspW Y.d.Xo₂ Y.d.c₂ Y.U (wtOf (T.Q.Dw j) (laOf (T.Q.Dw j) a (2 * (4 * m)))
      ((2 * (4 * m) / 2 : ℕ) : ℤ)) : Set (Rul Y.d.Xo₂ Y.d.c₂)) := by
    rintro _ ⟨f, -, rfl⟩
    rw [SetLike.mem_coe, ← hW]
    exact f.2
  have hs₀i : ∀ f ∈ Subtype.val '' s₀, ∀ la, ∀ v ∈ valSet Y.d.Xo₂ Y.d.c₂ (algCls Y.d.Xo₂ Y.d.c₂) la, 0 ≤ v f := by
    rintro _ ⟨f, hf, rfl⟩
    exact (AllWt.mem_supLat).1 (hs₀lat hf)
  have hs₀s : cuspW Y.d.Xo₂ Y.d.c₂ Y.U (wtOf (T.Q.Dw j) (laOf (T.Q.Dw j) a (2 * (4 * m)))
      ((2 * (4 * m) / 2 : ℕ) : ℤ)) ≤ Submodule.span Y.d.c₂.F (Subtype.val '' s₀) := by
    rw [← hW]
    intro g hg
    set_option synthInstance.maxHeartbeats 400000 in
    have h1 : (⟨g, hg⟩ : Y.V (wtZ a (2 * (4 * m)))) ∈ Submodule.span Y.d.c₂.F s₀ := by
      rw [hs₀span]; exact Submodule.mem_top
    exact Submodule.apply_mem_span_image_of_mem_span (Y.V (wtZ a (2 * (4 * m)))).subtype h1
  have hlo : ∀ w, 0 ≤ (t₁.mul t₂).lo w := fun w => add_nonneg (ht₁lo w) (ht₂lo w)
  have hGG : wtOf (T.Q.Dw j) (laOf (T.Q.Dw j) a (2 * (4 * m))) ((2 * (4 * m) / 2 : ℕ) : ℤ) +
      (wtOf (T.Q.Dw j) 0 (-(4 * (m : ℤ))) + wtOf (T.Q.Dw j) (parWt (T.Q.Dw j) fun τ => -n₀ τ) 0) =
      wtOf (T.Q.Dw j) la 0 := by
    rw [← AllWt.wtOf_add, ← AllWt.wtOf_add, hlaOf, hn2]
    congr 1
    · funext τ k; simp [parWt]
    · push_cast; ring
  have key := GlobalTheory.T.exists_spanning_family_mul_twistingSection D T.Q.H (T.Q.Dw j) Y.d.l₂ Y.d.Xo₂ Y.d.c₂ D.R.r Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z _ _
    (t₁.mul t₂) hL.unf (AllWt.even_wtOf _ _) hlo _ hs₀c hs₀i hs₀s
  rw [hGG] at key
  obtain ⟨s, hslat, hsspan, hsbd⟩ := key
  refine ⟨s, hslat, hsspan, fun y hy σ => ?_⟩
  obtain ⟨f, ⟨f₀, hf₀, rfl⟩, hfbd⟩ := hsbd y hy
  have hP1 : petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) (laOf (T.Q.Dw j) a (2 * (4 * m)))
      ((2 * (4 * m) / 2 : ℕ) : ℤ)) σ (f₀ : Rul Y.d.Xo₂ Y.d.c₂) ≤
      Real.exp (CG * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 * sizeK (T.Q.Dw j) a (2 * (4 * m))) := by
    rw [petOn_congr Y.U (xiR D) (fun _ => D.sp.W j) Y.dict hL.unf Z
      (exZ_laOf (T.Q.Dw j) a (2 * (4 * m)) ⟨4 * m, by ring⟩)]
    exact (hs₀bd f₀ hf₀ σ).2 Z
  have hc1 : t₁.cInf σ ≤
      Real.exp (((D.R.f : ℝ) * D.R.r + 1) * (2 * ((D.R.f : ℝ) * D.R.r) * Real.log (2 * Real.pi))) := by
    have h := ht₁c σ
    have hNR : ((Nat.card (Psi T.Q.H) * ((T.Q.Dw j).p + (T.Q.Dw j).q) : ℕ) : ℝ) = (D.R.f : ℝ) * D.R.r := by
      rw [hcard, hrk]; push_cast; ring
    rw [hNR, Real.log_le_iff_le_exp (t₁.cInf_pos σ)] at h
    refine h.trans (le_of_eq ?_)
    congr 1
    rw [hm]; push_cast; ring
  have hc2 : t₂.cInf σ ≤ Real.exp ((|c₁| + ((T.Q.Dw j).q : ℝ) * lrd D.host.E) * ∑ τ, |(n₀ τ : ℝ)| +
      logSum (badPrimes T.Q.H Y.d.l₂) + Real.log |(discr Y.d.c₂.F : ℝ)| / (2 * (Module.finrank ℚ Y.d.c₂.F : ℝ)) + 1) := by
    have h := ht₂c σ
    simp only [Int.cast_neg, abs_neg] at h
    rwa [Real.log_le_iff_le_exp (t₂.cInf_pos σ)] at h
  have hdd : Real.log |(discr Y.d.c₂.F : ℝ)| / (2 * (Module.finrank ℚ Y.d.c₂.F : ℝ)) ≤
      391 / 2 * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 := by
    have h := hY.rd
    have hpos : (0 : ℝ) < Module.finrank ℚ Y.d.c₂.F := by exact_mod_cast Module.finrank_pos
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hlrd := lrd_bounds D.host.E
  have hq_r : ((T.Q.Dw j).q : ℝ) ≤ D.R.r := by exact_mod_cast (show (T.Q.Dw j).q ≤ D.R.r by omega)
  have hSnn : 0 ≤ ∑ τ, ∑ k, |(la τ k : ℝ)| := by positivity
  have hNnn : 0 ≤ ∑ τ, |(n₀ τ : ℝ)| := by positivity
  have hfin := GlobalTheory.T.covolume_numerical_bounds_collect CG CB D.R.f D.R.r Lb (∑ τ, ∑ k, |(la τ k : ℝ)|) (∑ τ, |(n₀ τ : ℝ)|)
    (sizeK (T.Q.Dw j) a (2 * (4 * m))) c₁ ((T.Q.Dw j).q) (lrd D.host.E) (logSum (badPrimes T.Q.H Y.d.l₂))
    (Real.log |(discr Y.d.c₂.F : ℝ)| / (2 * (Module.finrank ℚ Y.d.c₂.F : ℝ))) hCG0 hCB0 (by exact_mod_cast hf1)
    (by exact_mod_cast hr1) hLb hSnn (Nat.cast_nonneg _) hq_r hlrd.1 (hlrd.2.trans hEs) hc₁b hNnn (by linarith [hN0])
    hsz0 (by linarith [hsizeK]) (hBad D T hT j hj Y e o hY Lb hLb hM hEs hfr) hdd
  refine (hfbd σ).trans ?_
  show t₁.cInf σ * t₂.cInf σ * _ ≤ _
  have hpet0 : 0 ≤ petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) (laOf (T.Q.Dw j) a (2 * (4 * m)))
      ((2 * (4 * m) / 2 : ℕ) : ℤ)) σ (f₀ : Rul Y.d.Xo₂ Y.d.c₂) := AllWt.petAt_nonneg _ _ _ _ _ _ _
  calc t₁.cInf σ * t₂.cInf σ * _ ≤ Real.exp (((D.R.f : ℝ) * D.R.r + 1) * (2 * ((D.R.f : ℝ) * D.R.r) * Real.log (2 * Real.pi))) *
        Real.exp ((|c₁| + ((T.Q.Dw j).q : ℝ) * lrd D.host.E) * ∑ τ, |(n₀ τ : ℝ)| +
          logSum (badPrimes T.Q.H Y.d.l₂) + Real.log |(discr Y.d.c₂.F : ℝ)| / (2 * (Module.finrank ℚ Y.d.c₂.F : ℝ)) + 1) *
        Real.exp (CG * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 * sizeK (T.Q.Dw j) a (2 * (4 * m))) := by
        have h1 := (t₁.cInf_pos σ).le
        have h2 := (t₂.cInf_pos σ).le
        gcongr
    _ = Real.exp (_ + _ + _) := by rw [← Real.exp_add, ← Real.exp_add]
    _ ≤ _ := Real.exp_le_exp.2 hfin
end GlobalTheory.ShortSpanComp
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.short_span_composition_closed : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ Lb : ℝ, 1 ≤ Lb → Real.log Y.d.l₂.M ≤ 30 * Lb → fieldSz D.host.E ≤ 3 * Lb → Real.log (D.R.f * D.R.r) ≤ Lb → o ≤ 391 * (D.R.f * D.R.r * Lb) ^ 2 → ∀ c₁ : ℝ, GlobalTheory.FlatLine.FlatExistsAt Y.U (xiR D) c₁ → |c₁| ≤ 9 * D.R.r * Lb → ∀ la : AllWt.Weight (T.Q.Dw j), (∀ τ, Antitone (la τ)) → (∀ τ, ((8 * D.R.f * D.R.r + 10 : ℕ) : ℤ) ≤ gap (la τ) ((T.Q.Dw j).p - 1)) → Real.log (∑ τ, ∑ k, |(la τ k : ℝ)|) ≤ 10 * Lb → ∀ Z, ∃ s : Set (cuspOn Y.U Z (wtOf (T.Q.Dw j) la 0)), s ⊆ (latOn Y.U Z (wtOf (T.Q.Dw j) la 0) : Set (cuspOn Y.U Z (wtOf (T.Q.Dw j) la 0))) ∧ Submodule.span Y.d.c₂.F s = ⊤ ∧ ∀ y ∈ s, ∀ σ, normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) la 0) σ y ≤ Real.exp (C * (((D.R.f : ℝ) * D.R.r * Lb) ^ 3 * (∑ τ, ∑ k, |(la τ k : ℝ)|) + ((D.R.f : ℝ) * D.R.r * Lb) ^ 5)) := by
  first | exact @_root_.GlobalTheory.ShortSpanComp.short_span_comp_mem | exact _root_.GlobalTheory.ShortSpanComp.short_span_comp_mem | (intros; apply _root_.GlobalTheory.ShortSpanComp.short_span_comp_mem <;> assumption)
end
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option autoImplicit false
namespace GlobalTheory.ShortGenComp
set_option maxHeartbeats 1000000 in
theorem short_generator_comparison : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ Lb : ℝ, 1 ≤ Lb → Real.log Y.d.l₂.M ≤ 30 * Lb → fieldSz D.host.E ≤ 3 * Lb → Real.log (D.R.f * D.R.r) ≤ Lb → o ≤ 391 * (D.R.f * D.R.r * Lb) ^ 2 → ∀ c₁ : ℝ, GlobalTheory.FlatLine.FlatExistsAt Y.U (xiR D) c₁ → |c₁| ≤ 9 * D.R.r * Lb → ∀ la : AllWt.Weight (T.Q.Dw j), (∀ τ, Antitone (la τ)) → (∀ τ, ((8 * D.R.f * D.R.r + 10 : ℕ) : ℤ) ≤ gap (la τ) ((T.Q.Dw j).p - 1)) → Real.log (∑ τ, ∑ k, |(la τ k : ℝ)|) ≤ 10 * Lb → ∀ Z, ∃ (n : ℕ) (w : Fin n → cuspOn Y.U Z (wtOf (T.Q.Dw j) la 0)) (abelian₂ : ℝ), CompHt.IsShortGen (normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) la 0)) (latOn Y.U Z (wtOf (T.Q.Dw j) la 0)) w abelian₂ ∧ Real.log abelian₂ ≤ C * (((D.R.f : ℝ) * D.R.r * Lb) ^ 3 * (∑ τ, ∑ k, |(la τ k : ℝ)|) + ((D.R.f : ℝ) * D.R.r * Lb) ^ 5) ∧ Real.log n ≤ C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 3 := by
  intro hP
  obtain ⟨C2, hC2, h2⟩ := _root_.GlobalTheory.T.short_span_composition_closed hP
  obtain ⟨Cb, hCb, hb⟩ := _root_.UpperTheory.Lit.Tam.tamagawa_number_formula hP
  refine ⟨2000 + Cb + C2, by positivity, ?_⟩
  intro D T hT j hp hq hE hj Y e o hY Lb hLb hM hfs hfr ho c₁ hc₁ hc₁b la hla hgap hsz Z
  have hgood := (_root_.GlobalTheory.T.covering_domain_lattice_regularity hP D T hT j hp hq hE hj Y e o hY la hla fun τ =>
    le_trans (by exact_mod_cast (by omega : 1 ≤ 8 * D.R.f * D.R.r + 10)) (hgap τ)).2 Z
  obtain ⟨s, hsL, hsp, hsn⟩ := h2 D T hT j hp hq hE hj Y e o hY Lb hLb hM hfs hfr ho c₁ hc₁ hc₁b la hla hgap hsz Z
  haveI : FiniteDimensional Y.d.c₂.F (cuspOn Y.U Z (wtOf (T.Q.Dw j) la 0)) :=
    hgood.1.some.2.1.1.finiteDimensional_of_finite
  obtain ⟨n, w, abelian₂, hsg, hLam, hn⟩ := GlobalTheory.T.exists_short_generators_of_short_spanning_family Y.d.c₂.F _
    (normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) la 0)) (latOn Y.U Z (wtOf (T.Q.Dw j) la 0)) s _
    hgood.2.1 (fun σ f => AllWt.petAt_nonneg _ _ _ _ _ _ _)
    (fun σ a f => AllWt.petOn_smul _ _ _ _ Z _ σ a f) (GlobalTheory.T.petersson_norm_component_add_le_of_gramFrame _ _ _ _ Z _ hgood) hsL hsp hsn
  refine ⟨n, w, abelian₂, hsg, ?_⟩
  have hf1 : 1 ≤ D.R.f ∧ 1 ≤ D.R.r := by
    have hn : 1 ≤ D.R.ord := D.R.ord_pos
    have hf : D.R.f = 2 * D.R.ord := rfl
    have hk := D.R.f_le_k
    have ht := D.R.rank_add_five_le
    exact ⟨by omega, by unfold Ranks.r; omega⟩
  have hfR : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf1.1
  have hrR : (1 : ℝ) ≤ D.R.r := by exact_mod_cast hf1.2
  set X : ℝ := (D.R.f : ℝ) * D.R.r * Lb with hXdef
  set S : ℝ := ∑ τ, ∑ k, |(la τ k : ℝ)| with hSdef
  have hX : 1 ≤ X := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hfR hrR) hLb
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hX2 : X ^ 2 ≤ X ^ 5 := pow_le_pow_right₀ hX (by norm_num)
  have hX3 : X ^ 3 ≤ X ^ 5 := pow_le_pow_right₀ hX (by norm_num)
  have hX23 : X ^ 2 ≤ X ^ 3 := pow_le_pow_right₀ hX (by norm_num)
  have hX1 : 1 ≤ X ^ 3 := one_le_pow₀ hX
  have hXS : 0 ≤ X ^ 3 * S := mul_nonneg (by positivity) hS
  have hrhs : 0 ≤ (2000 + Cb + C2) * (X ^ 3 * S + X ^ 5) := by positivity
  have hlogd : Real.log (Module.finrank ℚ Y.d.c₂.F : ℝ) ≤ o := hY.deg
  have hdpos : (0 : ℝ) < Module.finrank ℚ Y.d.c₂.F := by exact_mod_cast Module.finrank_pos
  have hdisc : (0 : ℝ) < |((NumberField.discr Y.d.c₂.F : ℤ) : ℝ)| :=
    abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero Y.d.c₂.F)
  have hlrd : Real.log (|((NumberField.discr Y.d.c₂.F : ℤ) : ℝ)| ^ (1 / (Module.finrank ℚ Y.d.c₂.F : ℝ))) ≤ o := by
    rw [Real.log_rpow hdisc, one_div, inv_mul_le_iff₀ hdpos, mul_comm]
    exact hY.rd
  have hberg := (hb D T hT j hp hq hE hj Y e o hY Lb hLb hM hfs hfr ho la hla (by linarith) Z).2.2
  have hm : Real.log (Formalism.HN.rkK (latOn Y.U Z (wtOf (T.Q.Dw j) la 0)) : ℝ) ≤ Cb * X ^ 3 := hberg
  have ho' : o ≤ 391 * X ^ 2 := ho
  have hCbX : Cb * X ^ 3 ≤ Cb * X ^ 5 := mul_le_mul_of_nonneg_left hX3 hCb
  constructor
  · have hL1 : 1 ≤ abelian₂ := hsg.one_le
    rcases le_or_gt ((Module.finrank ℚ Y.d.c₂.F : ℝ) ^ 4 * (Formalism.HN.rkK (latOn Y.U Z (wtOf (T.Q.Dw j) la 0)) : ℝ) *
        |((NumberField.discr Y.d.c₂.F : ℤ) : ℝ)| ^ (1 / (Module.finrank ℚ Y.d.c₂.F : ℝ)) *
        Real.exp (C2 * (X ^ 3 * S + X ^ 5))) 1 with hB | hB
    · have : abelian₂ = 1 := le_antisymm (hLam.trans (max_le le_rfl hB)) hL1
      rw [this, Real.log_one]; exact hrhs
    · have hLB := hLam.trans (le_of_eq (max_eq_right hB.le))
      have hmpos : (0 : ℝ) < (Formalism.HN.rkK (latOn Y.U Z (wtOf (T.Q.Dw j) la 0)) : ℝ) := by
        rcases (Nat.cast_nonneg (α := ℝ) (Formalism.HN.rkK (latOn Y.U Z (wtOf (T.Q.Dw j) la 0)))).lt_or_eq with h | h
        · exact h
        · rw [← h] at hB; simp at hB; linarith
      have hrd : 0 < |((NumberField.discr Y.d.c₂.F : ℤ) : ℝ)| ^ (1 / (Module.finrank ℚ Y.d.c₂.F : ℝ)) :=
        Real.rpow_pos_of_pos hdisc _
      have hlog := Real.log_le_log (by linarith) hLB
      rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_mul (by positivity) hrd.ne',
        Real.log_mul (by positivity) hmpos.ne', Real.log_pow, Real.log_exp] at hlog
      have hC2X : C2 * (X ^ 3 * S + X ^ 5) ≤ C2 * (X ^ 3 * S + X ^ 5) := le_rfl
      nlinarith
  · rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.log_zero]; positivity
    · have hnR : (n : ℝ) ≤ 2 * (Module.finrank ℚ Y.d.c₂.F : ℝ) * (Formalism.HN.rkK (latOn Y.U Z (wtOf (T.Q.Dw j) la 0)) : ℝ) := by
        exact_mod_cast hn
      have hmpos : (0 : ℝ) < (Formalism.HN.rkK (latOn Y.U Z (wtOf (T.Q.Dw j) la 0)) : ℝ) := by
        have : 0 < Formalism.HN.rkK (latOn Y.U Z (wtOf (T.Q.Dw j) la 0)) := by
          rcases Nat.eq_zero_or_pos (Formalism.HN.rkK (latOn Y.U Z (wtOf (T.Q.Dw j) la 0))) with h | h
          · rw [h] at hn; omega
          · exact h
        exact_mod_cast this
      have hlog := Real.log_le_log (by exact_mod_cast hpos) hnR
      rw [Real.log_mul (by positivity) hmpos.ne', Real.log_mul (by norm_num) hdpos.ne'] at hlog
      have h2 : Real.log 2 ≤ 1 := by
        have := Real.log_two_lt_d9; linarith
      have hC2X3 : 0 ≤ C2 * X ^ 3 := by positivity
      nlinarith
end GlobalTheory.ShortGenComp
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.short_generator_norm_comparison : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ Lb : ℝ, 1 ≤ Lb → Real.log Y.d.l₂.M ≤ 30 * Lb → fieldSz D.host.E ≤ 3 * Lb → Real.log (D.R.f * D.R.r) ≤ Lb → o ≤ 391 * (D.R.f * D.R.r * Lb) ^ 2 → ∀ c₁ : ℝ, GlobalTheory.FlatLine.FlatExistsAt Y.U (xiR D) c₁ → |c₁| ≤ 9 * D.R.r * Lb → ∀ la : AllWt.Weight (T.Q.Dw j), (∀ τ, Antitone (la τ)) → (∀ τ, ((8 * D.R.f * D.R.r + 10 : ℕ) : ℤ) ≤ gap (la τ) ((T.Q.Dw j).p - 1)) → Real.log (∑ τ, ∑ k, |(la τ k : ℝ)|) ≤ 10 * Lb → ∀ Z, ∃ (n : ℕ) (w : Fin n → cuspOn Y.U Z (wtOf (T.Q.Dw j) la 0)) (abelian₂ : ℝ), CompHt.IsShortGen (normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) la 0)) (latOn Y.U Z (wtOf (T.Q.Dw j) la 0)) w abelian₂ ∧ Real.log abelian₂ ≤ C * (((D.R.f : ℝ) * D.R.r * Lb) ^ 3 * (∑ τ, ∑ k, |(la τ k : ℝ)|) + ((D.R.f : ℝ) * D.R.r * Lb) ^ 5) ∧ Real.log n ≤ C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 3 := by
  first | exact @_root_.GlobalTheory.ShortGenComp.short_generator_comparison | exact _root_.GlobalTheory.ShortGenComp.short_generator_comparison | (intros; apply _root_.GlobalTheory.ShortGenComp.short_generator_comparison <;> assumption)
end
