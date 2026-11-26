module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLocusExponentLeOscillationNonTypePrime
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
public import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsStdMulShift
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyLocIsoSquareZeroSmoothLiftSystems
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianImage
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLatticeStabilizerFixesVacuumStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceStabilizerFixesVacuumLeft
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniversalSectionBasesShrunkAffineChart
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReferenceCoreOfSumPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupLatticeReferenceExponentThetaWeightLevelLeOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupLatticeReferenceExponentThetaWeightLevelLeOne
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.RefLevel

theorem lattice_terms_le {κ R s N d g' V r φ cst : ℝ} (hκ : 0 ≤ κ) (hR : 0 ≤ R) (hs : 0 ≤ s) (hsN : s ≤ N) (hV : 0 < V)
    (hr : 0 < r) (hφ : 0 ≤ φ) (hg' : 0 < g') (hc : κ * N ^ 3 * (R * N / 4 + 2 * d ^ 2) / g' ≤ cst) :
    (R * s * (κ * s ^ 3 * (r * φ)) / (4 * g') + 2 * d ^ 2 * (κ * s ^ 3 * (r * φ)) / g') / (r * V) ≤ cst * φ / V := by
  have hN : 0 ≤ N := hs.trans hsN
  calc (R * s * (κ * s ^ 3 * (r * φ)) / (4 * g') + 2 * d ^ 2 * (κ * s ^ 3 * (r * φ)) / g') / (r * V)
      = κ * s ^ 3 * (R * s / 4 + 2 * d ^ 2) / g' * φ / V := by field_simp
    _ ≤ κ * N ^ 3 * (R * N / 4 + 2 * d ^ 2) / g' * φ / V := by gcongr
    _ ≤ cst * φ / V := by gcongr

theorem not_isUnit_of_vV_ne_zero (S : CDVR) (N : ℕ) (h : vV S.V ((N : ℕ) : S.Fr) ≠ 0) : ¬ IsUnit ((N : ℕ) : S.V) := by
  intro hu
  apply h
  have h2 : valV S.V (algebraMap S.V S.Fr ((N : ℕ) : S.V)) = 1 := by
    unfold valV
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact fun h => (mem_nonunits_iff.1 h) hu
  rw [map_natCast] at h2
  unfold vV
  rw [h2]
  simp

theorem vV_pos {K : Type} [Field K] [NumberField K] {p : ℕ} (hp : p ≠ 0) {la : HeightOneSpectrum (𝓞 K)}
    (hla : (p : 𝓞 K) ∈ la.asIdeal) {T : CDVR} {io : K →+* T.Fr} {k : ℕ} (ho : OverLa la T.V io k) :
    0 < vV T.V (p : T.Fr) := by
  have h := ho.2 (p : K)
  rw [map_natCast] at h
  rw [h]
  refine mul_pos (by exact_mod_cast ho.1) ?_
  have h1 : la.valuation K (p : K) < 1 := by
    have := (la.valuation_lt_one_iff_mem (K := K) (p : 𝓞 K)).2 hla
    have e : ((p : 𝓞 K) : K) = (p : K) := map_natCast (algebraMap (𝓞 K) K) p
    rw [← e]
    exact this
  have h0 : la.valuation K (p : K) ≠ 0 := (Valuation.ne_zero_iff _).2 (Nat.cast_ne_zero.2 hp)
  have := (WithZero.log_lt_log h0 one_ne_zero).2 h1
  rw [WithZero.log_one] at this
  unfold vLa
  omega

theorem coprime_level (D : D7) (k : Fin 2) : Nat.Coprime (D.host.g k) (D.host.QS * D.host.q * D.host.d) := by
  have hc : D.host.g k % (D.host.QS * D.host.q * D.host.d) = 1 := D.ntypes.g_cond k
  rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, hc]
  simp

theorem refExp_le_of_halfSplit (D : D7) (T : Core D) (hM : LawsM T) (j : ℕ) (hj : InR D j)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (cst : ℝ) (hDom : Dom a n) (hLast : LastPos (T.Q.Dw j) a)
    (hrn : 2 * D.R.r ≤ n) (g g' : ℕ) (ρ ρ' : 𝓞 D.host.E) (hH : HalfSplit T.Q.l g g' ρ ρ')
    (hcop : Nat.Coprime (g * g') (D.host.QS * D.host.q * D.host.d)) (hg : 4 * DF (T.Q.Dw j) a + 4 ≤ g)
    (hg' : 4 * DF (T.Q.Dw j) a + 4 ≤ g') (hM0 : (DF (T.Q.Dw j) a : ℝ) * (2 * Real.sqrt (2 * D.R.f * D.R.m)) < g')
    (hc : rr0 D * (2 * D.R.f * D.R.m : ℝ) ^ 3 *
      ((D.R.r : ℝ) * (2 * D.R.f * D.R.m) / 4 + 2 * (DF (T.Q.Dw j) a : ℝ) ^ 2) / g' ≤ cst) :
    refExp_vp (T.U j) cst (wtZ a n) g ≤ ((1 : ℝ) : EReal) := by
  rw [refExp_vp_le_iff]
  intro la S io e ho y hy φ hφ
  obtain ⟨st, nab, hn⟩ :=
    GlobalTheory.CanonConn.exists_isNab_uncond D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c
  have hst := GlobalTheory.PowGerm.starSt _ T.Q.H st hn.1
  subst hst
  letI := T.Q.H.starRing
  obtain ⟨-, -, -, -, -, hE, hnum⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q hM.pins
  obtain ⟨hpq, hr1, -⟩ := hnum j hj
  have hq : (T.Q.Dw j).q = D.R.m - j := (hM.pins.2.2.2 j hj).2.1
  obtain ⟨hTot, hcusp⟩ := GlobalTheory.thetaRules_exist_and_cusp D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c D.R.r (T.U j) hr1
    (hM.unf j hj) nab hn
  obtain ⟨S', io', y', r, C, P, hy', hr, hFT, hTI, hφ', hOv, hvv, hnv⟩ :=
    GlobalTheory.T.exists_finiteExtension_uniformisedChart_scale D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c S io y hy φ hφ
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S'.V
  obtain ⟨⟨Q, hQ⟩, -⟩ :=
    GlobalTheory.PowData.exists_powData D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c S' io' y' C P ϖ hϖ
  obtain ⟨s, hs, hΦ, b, hb1, hb2⟩ :=
    GlobalTheory.T.exists_short_periodLattice_basis_balanced_slope D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c S' io' y' _ hφ' C P ϖ hϖ Q hQ
  obtain ⟨m, hmfin, hmle, hmeq⟩ :=
    GlobalTheory.ThetaLow.thetaRule_bounded_below D T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c nab hn g g' ρ ρ' hH hcop a n
  obtain ⟨hgp, hgp', hne, hMl, hρ, hρ', hMb, hsp, -⟩ := hH
  have hρs : ρ * star ρ = (g : 𝓞 D.host.E) := hρ
  have hρs' : ρ' * star ρ' = (g' : 𝓞 D.host.E) := hρ'
  have hV : 0 < vV S.V (g : S.Fr) := vV_pos hgp.ne_zero la.2 ho
  have hV' := hvv g hgp.ne_zero
  have hrZ : (0 : ℤ) < r := by exact_mod_cast hr
  have hsN : (s : ℝ) ≤ 2 * D.R.f * D.R.m := by
    rw [hE, hq] at hs
    exact_mod_cast hs.trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
  obtain ⟨e₀, he₀⟩ : ∃ e₀ : ℕ, vV S.V (g : S.Fr) = e₀ := ⟨_, (Int.toNat_of_nonneg hV.le).symm⟩
  have he₀0 : 0 < e₀ := by omega
  have hA := GlobalTheory.LevelPrimePoint.least_value_le GlobalTheory.ChF.hodgeTate_inclusion_chart D.host.E T.Q.H (T.Q.Dw j) T.Q.l
    (T.Q.Xo j) T.Q.c nab hn hTot S' io' y' C hFT P hTI hy' ϖ hϖ Q hQ _ _ s b hΦ hb1 hb2 g g' hgp hgp' hne hMl ρ ρ'
    hρs hρs' hMb hsp.1 hsp.2 (not_isUnit_of_vV_ne_zero S' g (by rw [hV']; exact (mul_pos hrZ hV).ne')) a n (r * e₀)
    hDom.1 (by rw [hpq]; exact hrn) (by omega) (Nat.mul_pos hr he₀0) (by omega) hg'
    (lt_of_le_of_lt (by gcongr) hM0)
  have hν : (∏ τ : D.host.E →+* ℂ, (io' (embK T.Q.c τ (star ρ * star ρ'))) ^ (∑ i : Fin ((T.Q.Dw j).mult τ), a (τ, i))) =
      io' (nrm (T.Q.Dw j) T.Q.c a (star ρ * star ρ')) := by
    unfold nrm
    simp only [map_prod, map_pow]
  have hν0 : nrm (T.Q.Dw j) T.Q.c a (star ρ * star ρ') ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ fun h0 => ?_
    have h1 : (star ρ * star ρ') * (ρ * ρ') = ((g * g' : ℕ) : 𝓞 D.host.E) := by
      rw [Nat.cast_mul, ← hρs, ← hρs']; ring
    have h2 := congrArg (embK T.Q.c τ) h1
    rw [map_mul, h0, zero_mul, map_natCast] at h2
    exact (Nat.cast_ne_zero.2 (Nat.mul_ne_zero hgp.ne_zero hgp'.ne_zero)) h2.symm
  rw [hν, hpq, hV', he₀, nval_of_ne ((map_ne_zero io').2 hν0)] at hA
  generalize nrm (T.Q.Dw j) T.Q.c a (star ρ * star ρ') = ν at hA hν0 hmeq
  generalize hN : ((vV S'.V (io' ν) : ℝ) / ((r * e₀ : ℕ) : ℝ) : ℝ) = N at hA
  have hlt : (⨅ f ∈ thGen (T.Q.Xo j) T.Q.c nab a n, nval S'.V (r * e₀) (evI y' f)) <
      ((1 + cst * φ / e₀ - N : ℝ) : EReal) := by
    rw [← EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _)), ← EReal.coe_sub] at hA
    refine hA.trans_lt (EReal.coe_lt_coe_iff.2 (sub_lt_sub_right ?_ _))
    have hrR : (0 : ℝ) < r := by exact_mod_cast hr
    have heR : (0 : ℝ) < e₀ := by exact_mod_cast he₀0
    have hgR : (4 : ℝ) * DF (T.Q.Dw j) a + 4 ≤ g := by exact_mod_cast hg
    have hd0 : (0 : ℝ) ≤ DF (T.Q.Dw j) a := Nat.cast_nonneg _
    rw [add_assoc, add_div]
    push_cast
    refine add_lt_add_of_lt_of_le ?_ (lattice_terms_le (by positivity) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hsN heR hrR
      hφ.nonneg (by exact_mod_cast hgp'.pos) hc)
    rw [mul_div_assoc, mul_div_cancel_left₀ _ (mul_pos hrR heR).ne', div_lt_one (by linarith)]
    linarith
  simp only [iInf_lt_iff] at hlt
  obtain ⟨f, hf, hlt⟩ := hlt
  obtain ⟨t, ht0, htv, w, hw, hwe⟩ := GlobalTheory.T.cuspForm_clear_denominators_away_from_place D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c D.R.r (T.U j)
    (wtZ a n) ⟨f, hcusp a n hDom hLast f hf⟩ m hmfin (hmle f hf) la.1 (-vLa la.1 ν) fun v hv => by
      have h := hmle f hf la.1 v hv
      rw [hmeq la.1 (Or.inl la.2)] at h
      rw [Int.cast_neg]
      exact h
  have ho' := hOv la.1 e ho
  refine (iInf₂_le w hw).trans ?_
  show nval S.V (vV S.V (g : S.Fr)).toNat (evI y (w : Rul (T.Q.Xo j) T.Q.c)) ≤ _
  rw [hwe, evI_smul, he₀, Int.toNat_natCast, ← hnv nab hn a n e₀ t f hf, nval_mul, nval_of_ne ((map_ne_zero io').2 ht0),
    ho'.2 t, htv, neg_neg, ← ho'.2 ν, hN]
  refine (add_le_add le_rfl hlt.le).trans (le_of_eq ?_)
  rw [← EReal.coe_add, ← EReal.coe_add]
  congr 1
  push_cast
  ring

theorem refExp_level_le_one : ∀ (D : D7) (T : Core D), LawsM T → ∀ (_ : ErrX D) (j : ℕ), InR D j → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (cst : ℝ), Dom a n → LastPos (T.Q.Dw j) a → ∑ f : Lt1 (T.Q.Dw j), 2 * rk f ≤ n → 2 * D.R.r ≤ n → JetNum D (DF (T.Q.Dw j) a) cst → ∀ k : Fin 2, refExp_vp (T.U j) cst (wtZ a n) (D.host.g k) ≤ ((1 : ℝ) : EReal) := by
  intro D T hM EX j hj a n cst hDom hLast _ hrn hJ k
  obtain ⟨π, π', hH⟩ := GlobalTheory.SplitLevel.level_halfSplit D T hM EX
  obtain ⟨k', ρ, ρ', hk⟩ : ∃ (k' : Fin 2) (ρ ρ' : 𝓞 D.host.E), HalfSplit T.Q.l (D.host.g k) (D.host.g k') ρ ρ' := by
    fin_cases k
    · exact ⟨1, π, π', hH⟩
    · exact ⟨0, π', π, hH.symm⟩
  exact refExp_le_of_halfSplit D T hM j hj a n cst hDom hLast hrn _ _ ρ ρ' hk
    (Nat.Coprime.mul_left (coprime_level D k) (coprime_level D k')) (hJ k).1 (hJ k').1 (hJ k').2.1 (hJ k').2.2

end GlobalTheory.RefLevel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupLatticeReferenceExponentThetaWeightLevelLeOneStatement
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.supLatticeReferenceExponent_thetaWeight_level_le_one : ∀ (D : D7) (T : Core D), LawsM T → ∀ (_ : ErrX D) (j : ℕ), InR D j → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (cst : ℝ), Dom a n → LastPos (T.Q.Dw j) a → ∑ f : Lt1 (T.Q.Dw j), 2 * rk f ≤ n → 2 * D.R.r ≤ n → JetNum D (DF (T.Q.Dw j) a) cst → ∀ k : Fin 2, refExp_vp (T.U j) cst (wtZ a n) (D.host.g k) ≤ ((1 : ℝ) : EReal) := by
  first | exact @GlobalTheory.RefLevel.refExp_level_le_one | exact GlobalTheory.RefLevel.refExp_level_le_one | (intros; apply GlobalTheory.RefLevel.refExp_level_le_one <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.RefSum.primeSum_add_pair {S : Finset ℕ} {e : ℕ → ℝ} {s : ℝ} (h : PrimeSum S e s) (g : Fin 2 → ℕ)
    (hg : ∀ k, (g k).Prime) :
    PrimeSum (S ∪ Finset.univ.image g) (fun q => e q + if q ∈ Finset.univ.image g then 1 else 0)
      (s + (Real.log (g 0) + Real.log (g 1))) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun q hq => ?_, fun q => add_nonneg (h2 q) (by split_ifs <;> norm_num), fun q hq => ?_, ?_⟩
  · rcases Finset.mem_union.1 hq with hq | hq
    · exact h1 q hq
    · obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hq
      exact hg k
  · rw [Finset.mem_union, not_or] at hq
    simp only [h3 q hq.1, if_neg hq.2, add_zero]
  · have a : ∑ q ∈ S ∪ Finset.univ.image g, e q * Real.log q = ∑ q ∈ S, e q * Real.log q :=
      (Finset.sum_subset Finset.subset_union_left fun q _ hq => by rw [h3 q hq, zero_mul]).symm
    have b : ∑ q ∈ S ∪ Finset.univ.image g, (if q ∈ Finset.univ.image g then (1 : ℝ) else 0) * Real.log q =
        ∑ q ∈ Finset.univ.image g, Real.log q := by
      rw [← Finset.sum_subset Finset.subset_union_right fun q _ hq => by rw [if_neg hq, zero_mul]]
      exact Finset.sum_congr rfl fun q hq => by rw [if_pos hq, one_mul]
    have c : ∑ q ∈ Finset.univ.image g, Real.log (q : ℕ) ≤ ∑ k : Fin 2, Real.log (g k) :=
      Finset.sum_image_le_of_nonneg (f := fun q : ℕ => Real.log q) fun q _ => Real.log_natCast_nonneg q
    rw [Fin.sum_univ_two] at c
    simp only [add_mul, Finset.sum_add_distrib]
    linarith
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeDivisorCentreThroughImage
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeDivisorCentreThroughImage
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

namespace GlobalTheory.Discrepancy

theorem DivOver.Over.through_image : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s] (E' : DivOver (s ≫ p)) (E : DivOver p), DivOver.Over s E' E → ∀ y : Y, E'.Through y → E.Through (s y) := by
  intro k _ X Y _ _ p s _ E' E hO y hy f hf
  obtain ⟨a, rfl⟩ := hf
  refine (hO _).2 (hy _ ⟨s.stalkMap y a, ?_⟩)
  exact (GlobalTheory.functionFieldMap_algebraMap s y a).symm

end GlobalTheory.Discrepancy
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeDivisorCentreThroughImageStatement
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primeDivisorCentre_through_image : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s] (E' : DivOver (s ≫ p)) (E : DivOver p), DivOver.Over s E' E → ∀ y : Y, E'.Through y → E.Through (s y) := by
  first | exact @GlobalTheory.Discrepancy.DivOver.Over.through_image | exact GlobalTheory.Discrepancy.DivOver.Over.through_image | (intros; apply GlobalTheory.Discrepancy.DivOver.Over.through_image <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationPartBaseChange
open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mean4 GlobalTheory.Mean4O
attribute [local instance] Over.cartesianMonoidalCategory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.PolPartPull

def oActIso {O : Type} [CommRing O] {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] (e : A ≅ B) [IsMonHom e.hom]
    (a : OAct O A) : OAct O B where
  act x := e.inv ≫ a.act x ≫ e.hom
  hom x := by have := a.hom x; infer_instance
  one := by rw [a.one]; simp
  mul x y := by rw [a.mul]; simp
  add x y := by rw [a.add, MonObj.mul_comp, MonObj.comp_mul]

theorem pbMap_fst {S S' : Scheme.{0}} (f : S' ⟶ S) {X Y : Over S} (a : X ⟶ Y) :
    ((Over.pullback f).map a).left ≫ pullback.fst Y.hom f = pullback.fst X.hom f ≫ a.left :=
  pullback.lift_fst _ _ _

end GlobalTheory.PolPartPull

namespace GlobalTheory.PolPartPull

end GlobalTheory.PolPartPull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcCompFinAwayPtOfNotMem
open scoped Matrix NNReal TensorProduct
open MeasureTheory NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.WeilM GlobalTheory.LocIntw
open GlobalTheory GlobalTheory.LFun GlobalTheory.ThK GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.SWLit

noncomputable section
namespace GlobalTheory.AwayFix.Chart

open GlobalTheory.AwayFix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem compFin_smul_away (v : HeightOneSpectrum (𝓞 F)) (a : AF F) (z : AF F ⊗[F] E) :
    compFin F E v (a • z) = evFin F v a • compFin F E v z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b x => exact congrArg (· ⊗ₜ[F] x) (map_mul (evFin F v) a b)
  | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, smul_add]

theorem compInf_smul_away (w : InfinitePlace F) (a : AF F) (z : AF F ⊗[F] E) :
    compInf F E w (a • z) = evInf F w a • compInf F E w z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b x => exact congrArg (· ⊗ₜ[F] x) (map_mul (evInf F w) a b)
  | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, smul_add]

variable {σ : E →ₐ[F] E} {N : ℕ} {Q : Matrix (Fin N) (Fin N) E}

end GlobalTheory.AwayFix.Chart

namespace GlobalTheory.AwayFix

open GlobalTheory.AwayFix.Chart

end GlobalTheory.AwayFix
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodRel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TChart

def isoVal {S S₁ S' : Scheme.{0}} {B : Over S} {B₁ : Over S₁} {B' : Over S'} [GrpObj B] [IsCommMonObj B] [GrpObj B₁]
    [IsCommMonObj B₁] [GrpObj B'] {M : LB B.left} {M₁ : LB B₁.left} {β₂ : (G2 B').left ⟶ (G2 B).left}
    {β₂' : (G2 B').left ⟶ (G2 B₁).left} (w : LB.Iso ((abelian₂ B M).pull β₂) ((abelian₂ B₁ M₁).pull β₂'))
    {Z : Scheme.{0}} (p : Z ⟶ (G2 B').left) (z : Z) (J : (Z ⟶ B₁.left) → M₁.ι) (J' : (Z ⟶ B.left) → M.ι) :
    (Z.presheaf.stalk z)ˣ :=
  gm p z _ (w.s (fun _ I => J (p ≫ β₂' ≫ (psum B₁ (x2 B₁) I.down).left),
    fun _ I => J' (p ≫ β₂ ≫ (psum B (x2 B) I.down).left)))

def IsNormIso {R : Type} [CommRing R] [IsDomain R] {S S₁ : Scheme.{0}} {B : Over S} {B₁ : Over S₁} {B' : Over (Sp R)}
    [GrpObj B] [IsCommMonObj B] [GrpObj B₁] [IsCommMonObj B₁] [GrpObj B'] {M : LB B.left} {M₁ : LB B₁.left}
    {β₂ : (G2 B').left ⟶ (G2 B).left} {β₂' : (G2 B').left ⟶ (G2 B₁).left}
    (w : LB.Iso ((abelian₂ B M).pull β₂) ((abelian₂ B₁ M₁).pull β₂')) : Prop :=
  ∀ z J J', Good M₁ z J → Good M z J' → isoVal w (lift (1 : TK R ⟶ B') (1 : TK R ⟶ B')).left z J J' = 1

def PeriodRel {o V V₁ W : Type} [CommRing o] [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [CommRing W]
    [IsLocalRing W] (D : DegPre V) (T : TautBase o W) (f₁ : V →+* V₁) (κ₁ : W →+* V₁) {B' : Over (Sp V₁)} [GrpObj B']
    {β₂ : (G2 B').left ⟶ (G2 D.P.A).left} {β₂' : (G2 B').left ⟶ (G2 T.B).left}
    (w : LB.Iso ((abelian₂ D.P.A D.P.L).pull β₂) ((abelian₂ T.B T.M.L).pull β₂')) (c : (Fin T.r → ℤ) ≃+ D.X)
    (x : (Fin T.r → ℤ) → (𝟙_ (Over (Sp V₁)) ⟶ B')) (n : ℕ) (q : (Fin T.r → ℤ) → (Fin T.r → ℤ) → (FractionRing V₁)ˣ) :
    Prop :=
  ∀ κK : (TK V₁).left ⟶ (TK V).left, κK ≫ jK V = jK V₁ ≫ spMap f₁ → ∀ a b z J J', Good T.M.L z J → Good D.P.L z J' →
    val (D.tau (c a) (c b)) κK z J' = gm (𝟙 (TK V₁).left) z ⊤ (unitOn (q a b)) *
      (isoVal w (lift (toUnit (TK V₁) ≫ x a) (toUnit (TK V₁) ≫ x b)).left z J J' *
        val (T.τ₀ ((n : ℤ) • a) ((n : ℤ) • b)) ((TK V₁).hom ≫ spMap κ₁) z J)

end GlobalTheory.TChart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ISupNonzeroLocusEmbH
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.SecEmb

def TraitRed {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (M : Modif R) (G : Over M.S) [GrpObj G]
    {B L : LB G.left} {N : ℕ} (s : Fin (N + 1) → B.Sec) (θ : L.Sec) (Y : Over (Sp (ResidueField R))) [GrpObj Y]
    (j : Y.left ⟶ PSpace R N) (O : Y.left.Opens) : Prop :=
  ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W) (ξ : Sp W ⟶ M.S),
    Function.Injective φ → IsLocalHom φ → ξ ≫ M.π = spMap φ →
    ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsLocalRing W') (io : W →+* W') (G' : Over (Sp W'))
      (_ : GrpObj G') (β : G'.left ⟶ G.left) (κ : ResidueField R →+* ResidueField W')
      (e : (Over.pullback (spMap (residue W'))).obj G' ≅ (Over.pullback (spMap κ)).obj Y),
      GlobalTheory.LN.CDvr W' ∧ Function.Injective io ∧ io.Finite ∧ IsGrpPullback G' G (spMap io ≫ ξ) β ∧
      κ.comp (residue R) = (residue W').comp (io.comp φ) ∧ IsMonHom e.hom ∧
      ∀ (Ω : Type) [Field Ω] (p : Sp Ω ⟶ ((Over.pullback (spMap (residue W'))).obj G').left) (p' : Sp Ω ⟶ G'.left)
        (y : Sp Ω ⟶ Y.left), p' = p ≫ pullback.fst G'.hom (spMap (residue W')) →
        y = p ≫ e.hom.left ≫ pullback.fst Y.hom (spMap κ) →
        (∃ hs, GlobalTheory.ProjSpace.toProj (p' ≫ G'.hom ≫ spMap (io.comp φ)) (fun i => GlobalTheory.secPull (s i) (p' ≫ β)) hs = y ≫ j) ∧
        ∀ x : Sp Ω, y x ∈ O → (p' ≫ β) x ∈ nonzeroLocus θ

def embH {X : Scheme.{0}} {B : LB X} {N : ℕ} (s : Fin (N + 1) → B.Sec) : X.Opens := ⨆ i, nonzeroLocus (s i)

theorem iSup_nonzeroLocus_embH {X : Scheme.{0}} {B : LB X} {N : ℕ} (s : Fin (N + 1) → B.Sec) :
    ⨆ i, nonzeroLocus (GlobalTheory.secPull (s i) (embH s).ι) = ⊤ := by
  simp only [GlobalTheory.nonzeroLocus_secPull]
  rw [← Scheme.Hom.preimage_iSup]
  exact Scheme.Opens.ι_preimage_self _

def embF {R : Type} [CommRing R] {X : Scheme.{0}} {B : LB X} {N : ℕ} (q : X ⟶ Sp R) (s : Fin (N + 1) → B.Sec) :
    (embH s).toScheme ⟶ PSpace R N :=
  GlobalTheory.ProjSpace.toProj ((embH s).ι ≫ q) (fun i => GlobalTheory.secPull (s i) (embH s).ι) (iSup_nonzeroLocus_embH s)

end GlobalTheory.Mum.SecEmb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOrdEqMultOfIsCartierDivisorOfRationalForm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOrdEqMultOfIsCartierDivisorOfRationalForm
set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy

theorem DivOver.formOrd_eq_mult_of_isDivOfForm : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q] (η : RatForms q n), η ≠ 0 → ∀ K : CartierDiv Y, IsDivOfForm K η → ∀ (E : DivOver q) (w : Y), E.IsAt w → (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) η = K.mult w := by
  intro k _ _ Y _ _ q n _ η hη K hK E w hE
  haveI := SmoothOfRelativeDimension.smooth n q
  have hn : topologicalKrullDim Y = n := GlobalTheory.HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth q n ‹_›
  obtain ⟨U, ω, hU, hω⟩ := exists_isFrame q n w
  have hgen := isFreeGen_formOf (gen_mem hU) hω
  have h0 : formOf U (gen_mem hU) ω ≠ 0 := fun h =>
    one_ne_zero (hgen.1 (a₁ := 1) (a₂ := 0) (by simp [h]))
  obtain ⟨c, hc⟩ := hgen.2 η
  have hc0 : c ≠ 0 := fun e => hη (by rw [← hc, e]; exact zero_smul _ _)
  have h1 := hK U ω hω w hU (Units.mk0 c hc0) hc.symm
  have h2 := E.formOrd_smul hn h0 (Units.mk0 c hc0)
  rw [DivOver.formOrd_formOf_eq_zero hU hE hω, add_zero] at h2
  replace h2 : E.formOrd η = E.ord (Units.mk0 c hc0) := hc ▸ h2
  change E.formOrd η = K.mult w
  rw [h2, h1.mult_eq, hE.ord_eq]

end GlobalTheory.Discrepancy
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOrdEqMultOfIsCartierDivisorOfRationalFormStatement
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formOrd_eq_mult_of_isCartierDivisorOfRationalForm : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q] (η : RatForms q n), η ≠ 0 → ∀ K : CartierDiv Y, IsDivOfForm K η → ∀ (E : DivOver q) (w : Y), E.IsAt w → (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) η = K.mult w := by
  first | exact @GlobalTheory.Discrepancy.DivOver.formOrd_eq_mult_of_isDivOfForm | exact GlobalTheory.Discrepancy.DivOver.formOrd_eq_mult_of_isDivOfForm | (intros; apply GlobalTheory.Discrepancy.DivOver.formOrd_eq_mult_of_isDivOfForm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftHomOfReductionSquareZeroSmooth
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftHomOfReductionSquareZeroSmooth
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Obs

theorem homLift : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (B B₀ : Type) [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] (p : B →+* B₀) (hs : SemiHom π p) (hp : Function.Surjective p) (hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) (B' B₀' : Type) [CommRing B'] [Algebra R B'] [CommRing B₀'] [Algebra R₀ B₀'] (p' : B' →+* B₀') (hs' : SemiHom π p') (hp' : Function.Surjective p') (hker' : ∀ b, p' b = 0 ↔ b ∈ I.map (algebraMap R B')) [Algebra.FormallySmooth R B] (φ : B₀ →ₐ[R₀] B₀'), ∃ ρ : B →ₐ[R] B', ∀ b, p' (ρ b) = φ (p b) := by
  intro R R₀ _ _ I hI π _ _ B B₀ _ _ _ _ p hs _ _ B' B₀' _ _ _ _ p' hs' hp' hker' _ φ
  letI : Algebra R B₀ := ((algebraMap R₀ B₀).comp π).toAlgebra
  letI : Algebra R B₀' := ((algebraMap R₀ B₀').comp π).toAlgebra
  let P : B →ₐ[R] B₀' := { (φ : B₀ →+* B₀').comp p with
    commutes' := fun r ↦ by
      show φ (p (algebraMap R B r)) = algebraMap R₀ B₀' (π r)
      rw [hs.map_algebraMap r]
      exact φ.commutes (π r) }
  let P' : B' →ₐ[R] B₀' := { p' with commutes' := fun r ↦ hs'.map_algebraMap r }
  have hn := LocalIsomorphism.nil I P' hker' (map_sq hI B')
  exact ⟨Algebra.FormallySmooth.liftOfSurjective P P' hp' hn,
    fun b ↦ Algebra.FormallySmooth.liftOfSurjective_apply P P' hp' hn b⟩

end GlobalTheory.Obs
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftHomOfReductionSquareZeroSmoothStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_hom_of_reduction_squareZero_smooth : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (B B₀ : Type) [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] (p : B →+* B₀) (hs : SemiHom π p) (hp : Function.Surjective p) (hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) (B' B₀' : Type) [CommRing B'] [Algebra R B'] [CommRing B₀'] [Algebra R₀ B₀'] (p' : B' →+* B₀') (hs' : SemiHom π p') (hp' : Function.Surjective p') (hker' : ∀ b, p' b = 0 ↔ b ∈ I.map (algebraMap R B')) [Algebra.FormallySmooth R B] (φ : B₀ →ₐ[R₀] B₀'), ∃ ρ : B →ₐ[R] B', ∀ b, p' (ρ b) = φ (p b) := by
  first | exact @GlobalTheory.Obs.homLift | exact GlobalTheory.Obs.homLift | (intros; apply GlobalTheory.Obs.homLift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapFactorResidueFieldOfClosedPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapFactorResidueFieldOfClosedPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

theorem spMap_factor_residueField_of_closedPoint (R : Type) [CommRing R] [IsLocalRing R] (Ω : Type) [Field Ω]
    (g : Sp Ω ⟶ Sp R) (hg : ∀ w, g w = closedPoint R) :
    ∃ κ : ResidueField R →+* Ω, g = spMap (κ.comp (residue R)) := by
  set φ : R →+* Ω := (Spec.preimage g).hom with hφ
  have hgφ : g = spMap φ := by
    simp only [spMap, hφ, CommRingCat.ofHom_hom, Spec.map_preimage]
  have hker : ∀ x ∈ maximalIdeal R, φ x = 0 := by
    intro x hx
    let w : Sp Ω := ⟨⊥, Ideal.isPrime_bot⟩
    have h1 := hg w
    rw [hgφ] at h1
    have h2 : (spMap φ w).asIdeal = Ideal.comap φ ⊥ := rfl
    rw [h1, closedPoint] at h2
    have : x ∈ Ideal.comap φ ⊥ := h2 ▸ hx
    simpa using this
  refine ⟨Ideal.Quotient.lift (maximalIdeal R) φ hker, ?_⟩
  rw [hgφ]
  congr 2

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapFactorResidueFieldOfClosedPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_spMap_residueField_of_forall_eq_closedPoint : ∀ (R : Type) [CommRing R] [IsLocalRing R] (Ω : Type) [Field Ω] (g : Sp Ω ⟶ Sp R), (∀ w, g w = closedPoint R) → ∃ κ : ResidueField R →+* Ω, g = spMap (κ.comp (residue R)) := by
  first | exact @GlobalTheory.Mum.spMap_factor_residueField_of_closedPoint | exact GlobalTheory.Mum.spMap_factor_residueField_of_closedPoint | (intros; apply GlobalTheory.Mum.spMap_factor_residueField_of_closedPoint <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleArithHilbertSamuelLargeRadiusPair
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleArithHilbertSamuelLargeRadiusPair
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem ampleHS_pair : AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (P : Pair p) (a b a' b' : ℤ) (M : HermLB p) (α : ℝ), P.Rep a b M → IsAmpleLB M.B →
    M.SemiPos D → M.IsSelfInter α → ∃ t₀ : ℝ, ∀ t, t₀ ≤ t →
      Tendsto (fun m : ℕ => P.lc (m * a + a') (m * b + b') (Real.exp (t * m)) / (m : ℝ) ^ (D + 1)) atTop
        (𝓝 (α / (D + 1).factorial + (((D : ℝ) + 1) * gdeg M D / (D + 1).factorial) * t)) := by
  intro hHS k _ X _ p D hX P a b a' b' M α hM hamp hsemi hself
  obtain ⟨N, hN⟩ := GlobalTheory.T.exists_hermitianRepresentative_integerCombination k X p P a' b'
  obtain ⟨Q, hQL, hQA, hQB⟩ := GlobalTheory.T.exists_hermPairSections_change_of_isometric_combinations k X p P a b a' b' M N hM hN
  have hamp' : IsAmpleLB Q.L.B := by rw [hQL]; exact hamp
  have hsemi' : Q.L.SemiPos D := by rw [hQL]; exact hsemi
  have hself' : Q.L.IsSelfInter α := by rw [hQL]; exact hself
  obtain ⟨t₀, ht⟩ := hHS k X p D hX Q α hamp' hsemi' hself'
  refine ⟨t₀, fun t htt => ?_⟩
  have hlc : ∀ m : ℕ, Q.lc m 1 (Real.exp (t * m)) = P.lc (m * a + a') (m * b + b') (Real.exp (t * m)) := by
    intro m
    simp only [Pair.lc]
    rw [hQB, one_mul, one_mul]
  have e : (α + ((D : ℝ) + 1) * t * gdeg Q.L D) / ((D + 1).factorial : ℝ) =
      α / (D + 1).factorial + (((D : ℝ) + 1) * gdeg M D / (D + 1).factorial) * t := by
    rw [hQL]; ring
  have h := ht t htt
  rw [e] at h
  simpa only [hlc] using h

end GlobalTheory.HSNef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleArithHilbertSamuelLargeRadiusPairStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ampleArithHilbertSamuel_largeRadius_pair : AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (a b a' b' : ℤ) (M : HermLB p) (α : ℝ), P.Rep a b M → IsAmpleLB M.B → M.SemiPos D → M.IsSelfInter α → ∃ t₀ : ℝ, ∀ t, t₀ ≤ t → Tendsto (fun m : ℕ => P.lc (m * a + a') (m * b + b') (Real.exp (t * m)) / (m : ℝ) ^ (D + 1)) atTop (𝓝 (α / (D + 1).factorial + (((D : ℝ) + 1) * gdeg M D / (D + 1).factorial) * t)) := by
  first | exact @GlobalTheory.HSNef.ampleHS_pair | exact GlobalTheory.HSNef.ampleHS_pair | (intros; apply GlobalTheory.HSNef.ampleHS_pair <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinExtIntegralClosure
open IsLocalRing ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.Mum

namespace GlobalTheory.GalClosure

variable {R : Type} [CommRing R] [IsDomain R] {E : Type} [Field E] [Algebra (FractionRing R) E]

abbrev baseMap (R : Type) [CommRing R] [IsDomain R] (E : Type) [Field E] [Algebra (FractionRing R) E] : R →+* E :=
  (algebraMap (FractionRing R) E).comp (algebraMap R (FractionRing R))

end GlobalTheory.GalClosure

namespace GlobalTheory.GalClosure

variable {R : Type} [CommRing R] [IsDomain R] {E : Type} [Field E] [Algebra (FractionRing R) E]

theorem finExt_integralClosure [IsLocalRing R] (hR : Base R) [FiniteDimensional (FractionRing R) E]
    [IsGalois (FractionRing R) E] :
    letI := (baseMap R E).toAlgebra
    ∃ _ : IsLocalRing (integralClosure R E), FinExt (algebraMap R (integralClosure R E)) := by
  letI := (baseMap R E).toAlgebra
  haveI : IsScalarTower R (FractionRing R) E := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨⟨hN, -, hI, hC⟩, -⟩ := hR
  set R₂ := integralClosure R E
  haveI : Module.Finite R R₂ := IsIntegralClosure.finite R (FractionRing R) E R₂
  haveI : HenselianLocalRing R := GlobalTheory.henselianLocalRing_of_isAdicComplete R
  haveI : IsLocalRing R₂ := GlobalTheory.TameKummer.isLocalRing_of_finite R R₂
  refine ⟨inferInstance, ⟨IsNoetherianRing.of_finite R R₂, inferInstance,
    integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing R),
    GlobalTheory.CompleteFiniteExtension.isAdicComplete_of_finite_local R R₂⟩, ?_, ?_⟩
  · intro a b h
    have := congrArg (algebraMap R₂ E) h
    exact IsFractionRing.injective R (FractionRing R) ((algebraMap (FractionRing R) E).injective this)
  · exact RingHom.finite_algebraMap.2 inferInstance

end GlobalTheory.GalClosure

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.GalClosure

end GlobalTheory.GalClosure
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceIntegralUnitaryPointsFixVacuum
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertBridge

theorem fix_vac : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σL : L →+* L) (q : ℕ) (δ : L)
      (JS : GL (Fin a') L) (JT : GL (Fin (a + a')) L) (ψL : AddChar L ℂ)
      (κ : Matrix (Fin (a + a')) (Fin a') L →+ Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
      (ιS : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) →* UA σ G.V'.J)
      (ιT : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →* UA σ G.W.J),
      GlobalTheory.InertBridge.Chart σ B G v ϖ σL q δ JS JT ψL κ ιS ιT →
    ∀ ω : (Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) × Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →*
        Module.End ℂ (SB (Fin a' × Fin (a + a') → Fv F v))),
      (∀ g h (m : SB (Fin a' × Fin (a + a') → Fv F v)) (φ₁ : (Fin a' × Fin (a + a') → Fv F v) → ℂ),
        φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v) →
        (Acts (evFin F v) (om' (ιS g, ιT h)) (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ) φ₁ ↔
          ((ω (g, h) m : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ) = φ₁)) →
    ∀ s : SB (Fin a' × Fin (a + a') → Fv F v), (s : (Fin a' × Fin (a + a') → Fv F v) → ℂ) = G.M'.vac v →
    ∀ (g : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L)) (h : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L)),
      (g : GL (Fin a') L) ∈ Formalism.UG.GLint (Fin a') (Formalism.UG.intL L) →
      (h : GL (Fin (a + a')) L) ∈ Formalism.UG.GLint (Fin (a + a')) (Formalism.UG.intL L) → ω (g, h) s = s := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v w hI hT L _ _ ϖ σL q δ JS JT ψL κ ιS ιT hC ω hω s hs g h hg hh
  obtain ⟨unr, odd, intS, intT, hermS, hermT, hδ, psiInt, psiNe, hAt, hSurj, hLat, hPsi, hEq, hιS, hιT, hKS, hKT⟩ := hC
  have hvac : G.M'.vac v ∈ SB (Fin a' × Fin (a + a') → Fv F v) := hs ▸ s.2
  have h1 : ω (1, h) s = s := by
    have hA : Acts (evFin F v) (om' (ιS 1, ιT h)) (s : (Fin a' × Fin (a + a') → Fv F v) → ℂ) (G.M'.vac v) := by
      rw [map_one, hs]
      exact GlobalTheory.T.inertPlace_latticeStabilizer_fixes_vacuum F E σ B a a' G X om om' hTr v w hI hT (ιT h) (hKT h hh)
    exact Subtype.ext (((hω 1 h s _ hvac).mp hA).trans hs.symm)
  have h2 : ω (g, 1) s = s := by
    have hA : Acts (evFin F v) (om' (ιS g, ιT 1)) (s : (Fin a' × Fin (a + a') → Fv F v) → ℂ) (G.M'.vac v) := by
      rw [map_one, hs]
      exact GlobalTheory.T.inertPlace_stabilizer_fixes_vacuum_left F E σ B a a' G X om om' hTr v w hI hT (ιS g) (hKS g hg)
    exact Subtype.ext (((hω g 1 s _ hvac).mp hA).trans hs.symm)
  have hgh : ((g, h) : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) × Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L)) = (g, 1) * (1, h) := by
    simp
  rw [hgh, map_mul, Module.End.mul_apply, h1, h2]

end GlobalTheory.InertBridge

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedNullSetCharts
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.Mean4 GlobalTheory.Mean4O
open MeasureTheory GlobalTheory.ChartGlue GlobalTheory.Mean4O.CoverInt
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.Points (PtsOver)

namespace GlobalTheory.Mean4O.CoverExc

section Model

variable {F : Type} [Field F] [NumberField F] {X G : Scheme.{0}} {p : X ⟶ Sp (𝓞 F)} {q : G ⟶ Sp F} {j : G ⟶ X}


end Model

section Fibre

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} (π : Y ⟶ X) (hπ : π ≫ p = q)


include hπ in
theorem app_algX (U : X.Opens) (a : k) : algX q (π ⁻¹ᵁ U) a = (π.app U).hom (algX p U a) := by
  have hw : π ≫ p = q ≫ spMap (RingHom.id k) := by
    rw [hπ, show spMap (RingHom.id k) = 𝟙 _ from Spec.map_id _, Category.comp_id]
  have := RingHom.congr_fun (TopForm.appLE_comp_algX (p := p) (p' := q) (φ := π)
    (σ := RingHom.id k) hw (V := U) (W := π ⁻¹ᵁ U) le_rfl) a
  simpa [Scheme.Hom.app_eq_appLE] using this.symm


include hπ in
theorem etale_app {U : X.Opens} {e : ℕ} {x : Fin e → Γ(X, U)} (hx : (MvPolynomial.eval₂Hom (algX p U) x).Etale)
    (het : (π.app U).hom.Etale) :
    (MvPolynomial.eval₂Hom (algX q (π ⁻¹ᵁ U)) fun a => (π.app U).hom (x a)).Etale := by
  have hcx : (MvPolynomial.eval₂Hom (algX q (π ⁻¹ᵁ U)) fun a => (π.app U).hom (x a)) =
      (π.app U).hom.comp (MvPolynomial.eval₂Hom (algX p U) x) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) fun a => ?_
    · simp [app_algX π hπ]
    · simp
  rw [hcx]
  exact RingHom.Etale.stableUnderComposition _ _ hx het

end Fibre

end GlobalTheory.Mean4O.CoverExc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianHeightBoundedBelow
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt

namespace GlobalTheory.AmpleHtLow

theorem nsq_shift_pow {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} (L : HermLB p) (t : (k →+* ℂ) → ℝ)
    (ht : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) (m : ℕ) (σ : k →+* ℂ) (f : (L.pow m).B.ι → CxPts p σ → ℂ)
    (y : CxPts p σ) :
    (((L.shift t ht).pow m).φ σ).nsq f y = ((L.pow m).φ σ).nsq f y * Real.exp (-(2 * m * t σ)) := by
  simp only [Weight.nsq, HermLB.pow, HermLB.shift, Weight.pow]
  erw [Weight.zpow_φ, Weight.zpow_φ]
  rw [mul_assoc, ← Real.exp_add]
  simp only [Weight.addFn]
  congr 2
  push_cast
  ring

theorem small_of_shift : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
    ∀ (L : HermLB p) (m : ℕ), 1 ≤ m → ∀ (s : (L.pow m).B.Sec), ∃ c : ℝ,
      s ∈ ((L.shift (fun _ => -c) fun _ => rfl).pow m).smallSec := by
  intro k _ X p D hX L m hm s
  have := hX.finite_emb
  have hb : ∀ σ : k →+* ℂ, ∃ K : ℝ, ∀ y, ((L.pow m).φ σ).nsq (CxPts.secVal p σ s) y ≤ K := fun σ => by
    have := hX.compactSpace σ
    obtain ⟨K, hK⟩ := (isCompact_range (((L.pow m).cInf σ).continuous_nsq s)).bddAbove
    exact ⟨K, fun y => hK ⟨y, rfl⟩⟩
  choose K hK using hb
  have := Fintype.ofFinite (k →+* ℂ)
  have hK' : ∀ σ, K σ ≤ ∑ τ, |K τ| + 1 := fun σ => by
    have := Finset.single_le_sum (fun τ (_ : τ ∈ Finset.univ) => abs_nonneg (K τ)) (Finset.mem_univ σ)
    linarith [le_abs_self (K σ)]
  have h1 : (1 : ℝ) ≤ ∑ τ, |K τ| + 1 := by
    linarith [Finset.sum_nonneg fun τ (_ : τ ∈ Finset.univ) => abs_nonneg (K τ)]
  set K' : ℝ := ∑ τ, |K τ| + 1
  have hl : 0 ≤ Real.log K' := Real.log_nonneg h1
  have hpos : 0 < K' := by linarith
  refine ⟨-(Real.log K' / 2), fun σ y => ?_⟩
  refine (le_of_eq (nsq_shift_pow L (fun _ => -(-(Real.log K' / 2))) (fun _ => rfl) m σ (CxPts.secVal p σ s) y)).trans ?_
  have h0 : 0 ≤ ((L.pow m).φ σ).nsq (CxPts.secVal p σ s) y := by unfold Weight.nsq; positivity
  have h2 : Real.exp (-(2 * (m : ℝ) * -(-(Real.log K' / 2)))) ≤ K'⁻¹ := by
    rw [show -(2 * (m : ℝ) * -(-(Real.log K' / 2))) = -((m : ℝ) * Real.log K') by ring,
      ← Real.exp_log hpos, ← Real.exp_neg, Real.exp_log hpos]
    refine Real.exp_le_exp.2 (neg_le_neg ?_)
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  calc ((L.pow m).φ σ).nsq (CxPts.secVal p σ s) y * Real.exp (-(2 * (m : ℝ) * -(-(Real.log K' / 2))))
      ≤ K' * K'⁻¹ := mul_le_mul ((hK σ y).trans (hK' σ)) h2 (Real.exp_pos _).le hpos.le
    _ = 1 := mul_inv_cancel₀ hpos.ne'

end GlobalTheory.AmpleHtLow

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupportPullbackEqPreimage
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.Twist

namespace GlobalTheory.QCoh


open TensorProduct in
theorem nontrivial_fibre_of_isBaseChange {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    {l : M →ₗ[R] N} (hl : IsBaseChange S l) (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    (hpq : p = q.comap (algebraMap R S)) :
    Nontrivial (q.ResidueField ⊗[S] N) ↔ Nontrivial (p.ResidueField ⊗[R] M) := by
  letI : Algebra p.ResidueField q.ResidueField :=
    (Ideal.ResidueField.map p q (algebraMap R S) hpq).toAlgebra
  haveI : IsScalarTower R p.ResidueField q.ResidueField :=
    .of_algebraMap_eq fun r =>
      (IsScalarTower.algebraMap_apply R S q.ResidueField r).trans
        (Ideal.ResidueField.map_algebraMap _ _ _ hpq r).symm
  have e₁ : q.ResidueField ⊗[S] N ≃ₗ[S] q.ResidueField ⊗[S] (S ⊗[R] M) :=
    LinearEquiv.lTensor q.ResidueField hl.equiv.symm
  have e₂ : q.ResidueField ⊗[S] (S ⊗[R] M) ≃ₗ[q.ResidueField] q.ResidueField ⊗[R] M :=
    AlgebraTensorModule.cancelBaseChange R S q.ResidueField q.ResidueField M
  have e₃ : q.ResidueField ⊗[p.ResidueField] (p.ResidueField ⊗[R] M) ≃ₗ[q.ResidueField]
      q.ResidueField ⊗[R] M :=
    AlgebraTensorModule.cancelBaseChange R p.ResidueField q.ResidueField q.ResidueField M
  rw [e₁.toEquiv.nontrivial_congr, e₂.toEquiv.nontrivial_congr, ← e₃.toEquiv.nontrivial_congr]
  exact Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right p.ResidueField q.ResidueField

theorem mem_support_of_isBaseChange {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {M N : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    {l : M →ₗ[R] N} (hl : IsBaseChange S l) (q : PrimeSpectrum S) :
    q ∈ Module.support S N ↔ PrimeSpectrum.comap (algebraMap R S) q ∈ Module.support R M := by
  haveI : Module.Finite S N := Module.Finite.equiv hl.equiv
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct,
    Module.mem_support_iff_nontrivial_residueField_tensorProduct]
  exact nontrivial_fibre_of_isBaseChange hl _ _ rfl

theorem support_pullback {X Y : Scheme.{0}} (f : Y ⟶ X) (G : X.Modules) [IsFiniteQC G] :
    support ((Scheme.Modules.pullback f).obj G) = f.base ⁻¹' support G := by
  ext y
  obtain ⟨U, V, hU, hV, hy, -, e⟩ := exists_affine_pair f y (W := ⊤) trivial
  have hfy : f y ∈ V := e hy
  rw [Set.mem_preimage, mem_support_iff_primeIdealOf hU ⟨y, hy⟩,
    mem_support_iff_primeIdealOf hV ⟨f y, hfy⟩]
  letI := appLEAlgebra f e
  letI := appLEModule f ((Scheme.Modules.pullback f).obj G) e
  haveI := appLE_isScalarTower f ((Scheme.Modules.pullback f).obj G) e
  have := finite_sections G hV
  rw [mem_support_of_isBaseChange (isBaseChange_pullbackSections f G hU hV e)]
  have h := IsAffineOpen.comap_primeIdealOf_appLE V hV U hU e hy
  convert Iff.rfl using 2
  exact h.symm

end GlobalTheory.QCoh
end
