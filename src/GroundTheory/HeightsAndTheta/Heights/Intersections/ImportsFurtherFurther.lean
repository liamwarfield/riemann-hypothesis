module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiProjPrimeImageZ
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFIntZero
public import GroundTheory.HeightsAndTheta.Heights.Intersections.ThmIExistsFamily
public import GroundTheory.HeightsAndTheta.Heights.Intersections.FunFieldLeLocRing

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsFurtherFurther
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M

def PullbackDegreeCount.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' J' : Ideal (MRing ι')) (n : ℕ)
    (G : GenFibre v P') (J : IFamily G.Φ (fibreIdx ι' κ)) (R : AnLogRes P' J' n)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)),
    IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') (n + 1) → IsFieldIntersection J →
    IsGoodProj (imageZ v P') Ψ →
    ∀ᵐ y : Fin n → ℂ, ∀ w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre (imageZ v P') Ψ y,
      (({x | pullQ R v Ψ x = y ∧ pullW R v Ψ x = w} \ pullBad R v Ψ).ncard : ℤ) =
        J (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G) 0 Fin.elim0

section Inhabitants

open IndefiniteRowSideFullHecke.Inter

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PPFVert
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace ProjectionFormulaVertical

open PointVertical

theorem geoNum_mixed_eq_zero
    (hGeo : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], GeoNumStatement ι)
    (hR4 : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι)
    (hCMF : ContractMixedFieldStatement)
    {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
    {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v) {P' : Ideal (MRing ι')} {d r : ℕ}
    (hP : IsArithVar (imageZ v P') d) {W : Ideal (MRing ι')} (hPW : P' ≤ W)
    (hWm : IsMultiProjPrime W) (hpr : (charOf W).Prime)
    (hWd : ringKrullDim (MRing ι' ⧸ W) = ((d + r + Fintype.card K' : ℕ) : WithBot ℕ∞))
    (L : Fin d → K → ℤ) (N : Fin r → K' → ℤ) :
    geoNum (d + r) W (Fin.append (fun j => pullDeg κ (L j)) N) = 0 := by
  set p := charOf W with hpdef
  have : Fact p.Prime := ⟨hpr⟩
  have hpW : ((p : ℕ) : MRing ι') ∈ W := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.natCast_mem_of_charOf W
  have hWp : IsProjVarF (W.map (red p)) (d + r) :=
    ⟨isMultiProjPrime_red p hWm hpW, by rw [ringKrullDim_red p hpW, hWd]⟩
  have hImm : IsMultiProjPrime (imageZ v W) := isMultiProjPrime_imageZ hv hWm
  have hpI : ((p : ℕ) : MRing ι) ∈ imageZ v W := by
    show rename v ((p : ℕ) : MRing ι) ∈ W
    simpa using hpW
  have hVm := isMultiProjPrime_red p hImm hpI
  obtain ⟨D, hKD, hD⟩ := exists_dim_F p _ hVm
  obtain ⟨-, ⟨hQp, -, -⟩, hQh, hQd⟩ := hP
  have := hQp
  have hle : imageZ v P' ≤ imageZ v W := Ideal.comap_mono hPW
  have hpQ : ((p : ℕ) : MRing ι) ∉ imageZ v P' := by
    intro h
    have h2 : ((p : ℕ) : ℤ) ∈ (imageZ v P').comap (C : ℤ →+* MRing ι) := by
      rw [Ideal.mem_comap, map_natCast]
      exact h
    rw [hQh, Ideal.mem_bot] at h2
    exact hpr.ne_zero (by exact_mod_cast h2)
  have hdim := krullDim_quot_add_one_le hle hpI hpQ
  rw [← ringKrullDim_red p hpI, hD, hQd] at hdim
  have hD' : D + 1 ≤ d + Fintype.card K := by exact_mod_cast hdim
  have hVi : IsProjVarF (imageVar (ZMod p) v (W.map (red p))) (D - Fintype.card K) := by
    rw [imageVar_red p v hpW]
    refine ⟨hVm, ?_⟩
    rw [hD, Nat.sub_add_cancel hKD]
  obtain ⟨I, hI, -⟩ := hR4 (ZMod p) K' ι'
  rw [hGeo K' ι' p I hI W (d + r) _ hWm hpW hWp]
  unfold ContractMixedFieldStatement at hCMF
  exact hCMF (ZMod p) K ι K' ι' I hI κ v _ (D - Fintype.card K) d r L N hv hWp hVi (by omega)

end ProjectionFormulaVertical


open ProjectionFormulaVertical in
theorem PFVert.proof
    (hGeo : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], GeoNumStatement ι)
    (hR4 : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι)
    (hCMF : ContractMixedFieldStatement) :
    PFVert.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' d r L L' N s a W hv hP' hP hL hs hsP hW hh
  classical
  have hsec : IsSectionOn P' (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.sqMetric (ι := ι') a) s := ⟨a, fun _ => rfl, hs, hsP⟩
  obtain ⟨hWm, hpr, hWd⟩ :=
    (divSuppArith K' ι' P' (d + r) (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.sqMetric (ι := ι') a) s W hP' hsec hW).2 hh
  have hPW : P' ≤ W := le_sup_left.trans hW.1.1.2
  have e : (fun j => (Fin.append L' N j).a) =
      Fin.append (fun j => pullDeg κ (L j).a) (fun j => (N j).a) := by
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp [(hL i).1]
    · simp
  rw [e]
  exact geoNum_mixed_eq_zero hGeo hR4 hCMF hv hP hPW hWm hpr hWd _ _

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsBisAlt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem RegularityDenominator.isMultiHomog_C {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] (n : ℤ) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (C n : MRing ι) 0 := by
  intro m hm k
  rw [C_apply] at hm
  have : m = 0 := by simpa using support_monomial_subset hm
  simp [this]

theorem RegularityDenominator.proof (hD : RegularityDivisorSupportClosed.Statement) (hPow : LocRingPow.Statement) :
    RegularityDenominator.Statement := by
  intro K _ ι _ P x hP
  have hPp : P.IsPrime := hP.2.1.1
  have hFL : (x : FractionRing (MRing ι ⧸ P)) ∈ locRing P P := by
    have hx := x.2
    unfold funField at hx
    unfold locRing
    refine Subring.closure_mono ?_ hx
    rintro _ ⟨u, v, a, hv, hu, hva, rfl⟩
    refine ⟨u, v, a, hv, fun h => ?_, hu, hva, rfl⟩
    have h0 : Ideal.Quotient.mk P v = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr h
    exact zero_notMem_nonZeroDivisors (h0 ▸ hv)
  obtain ⟨u, v, a, hu, hva, hvP, hxv⟩ := LocRingFrac.proof K ι P P hPp hPp le_rfl _ hFL

  have key : ∀ W ∈ divSupp P v, ∃ m : ℤ, m ≠ 0 ∧
      (x : FractionRing (MRing ι ⧸ P)) * (m : FractionRing (MRing ι ⧸ P)) ∈ locRing P W := by
    intro W hW
    obtain ⟨hWc, hPW, -⟩ := (hD K ι P v a W hP hva hvP).1 hW
    have hWp : W.IsPrime := hWc.1.1
    have hvert : W.comap (C : ℤ →+* MRing ι) ≠ ⊥ := fun hh =>
      arithVarZero K ι W ⟨hP.1, hWc.1, hh, by rw [zero_add]; exact hWc.2⟩
    obtain ⟨n, hnW, hn0⟩ := (Submodule.ne_bot_iff _).mp hvert
    choose c hc using hW.2
    set t : MRing ι := ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ a k
    have ht : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog t a := AvoidRing.isMultiHomog_coordProd c a
    have htW : t ∉ W := AvoidRing.coordProd_not_mem hWp c hc a
    have ht0 : algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P t) ≠ 0 := by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
      exact fun h => htW (hPW h)
    have h1W : (1 : MRing ι) ∉ W := fun h => hWp.ne_top ((Ideal.eq_top_iff_one _).mpr h)
    obtain ⟨N, z, hz, hNz⟩ := hPow K ι P v t a W _ (C n) 1 0 (n : FractionRing (MRing ι ⧸ P)) hPp hP.2.1.2.1 hva
      hvP hW ht htW (div_mul_cancel₀ _ ht0) (RegularityDenominator.isMultiHomog_C n) AvoidRing.isMultiHomog_one hnW h1W
      (by rw [map_one, map_one, mul_one, eq_intCast C n, map_intCast, map_intCast])
    refine ⟨n ^ N, pow_ne_zero _ hn0, ?_⟩
    have hut : algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u) /
        algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P t) ∈ locRing P W :=
      frac_mem_locRing hPW hu ht htW (div_mul_cancel₀ _ ht0)
    rw [Int.cast_pow, hNz, ← mul_assoc, mul_div_assoc', hxv]
    exact mul_mem hut hz
  classical
  have hfin := divSupp_finite P v
  let mW : Ideal (MRing ι) → ℤ := fun W => if h : W ∈ divSupp P v then (key W h).choose else 1
  let M : ℤ := ∏ W ∈ hfin.toFinset, mW W
  have hM0 : M ≠ 0 := Finset.prod_ne_zero_iff.mpr fun W hW => by
    have hW' := hfin.mem_toFinset.mp hW
    simp only [mW, dif_pos hW']
    exact (key W hW').choose_spec.1
  refine ⟨(M : funField P), fun h => hM0 ?_, fun W hWc hPW => ⟨?_, ?_⟩⟩
  · have h' : ((M : funField P) : FractionRing (MRing ι ⧸ P)) = 0 := by rw [h]; rfl
    have h2 : algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P (C M)) = 0 := by
      rw [eq_intCast C M, map_intCast, map_intCast]
      simp at h'
      exact h'
    rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at h2
    have h3 : M ∈ P.comap (C : ℤ →+* MRing ι) := h2
    rw [hP.2.2.1] at h3
    exact Ideal.mem_bot.mp h3
  · have hc : ((M : funField P) : FractionRing (MRing ι ⧸ P)) = (M : FractionRing (MRing ι ⧸ P)) := by simp
    rw [hc]
    exact intCast_mem (locRing P W) M
  · have hc : ((x * (M : funField P) : funField P) : FractionRing (MRing ι ⧸ P)) =
        (x : FractionRing (MRing ι ⧸ P)) * (M : FractionRing (MRing ι ⧸ P)) := by simp
    rw [hc]
    by_cases hvW : v ∈ W
    · have hW : W ∈ divSupp P v := (hD K ι P v a W hP hva hvP).2 ⟨hWc, hPW, hvW⟩
      obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem mW (hfin.mem_toFinset.mpr hW)
      have hm := (key W hW).choose_spec.2
      rw [show M = mW W * r from hr, Int.cast_mul, ← mul_assoc]
      simp only [mW, dif_pos hW]
      exact mul_mem hm (intCast_mem _ r)
    · exact mul_mem (frac_mem_locRing hPW hu hva hvW hxv) (intCast_mem _ M)

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.IsHorizontalImageZ
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace ArithmeticIntersectionHorizontal

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]


omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem isHorizontal_imageZ {v : (Σ k, ι k) → (Σ k', ι' k')} {W' : Ideal (MRing ι')} (h : IsHorizontal W') :
    IsHorizontal (imageZ v W') := by
  have h' : W'.comap (C : ℤ →+* MRing ι') = ⊥ := h
  show (imageZ v W').comap (C : ℤ →+* MRing ι) = ⊥
  rw [← h']
  ext c
  simp [imageZ, Ideal.mem_comap]

theorem dim_eq {P : Ideal (MRing ι)} {d d' : ℕ} (h : IsArithVar P d) (h' : IsArithVar P d') : d = d' := by
  have e := h.2.2.2.symm.trans h'.2.2.2
  have e2 : d + Fintype.card K = d' + Fintype.card K := by exact_mod_cast e
  omega

theorem dim_add_one_le {R : Type*} [CommRing R] {Q Q₂ : Ideal R} [Q.IsPrime] (hle : Q ≤ Q₂)
    {x : R} (hx : x ∈ Q₂) (hxQ : x ∉ Q) : ringKrullDim (R ⧸ Q₂) + 1 ≤ ringKrullDim (R ⧸ Q) := by
  have hr : Ideal.Quotient.mk Q x ∈ nonZeroDivisors (R ⧸ Q) :=
    mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  refine le_trans ?_ (ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr)
  gcongr
  refine ringKrullDim_le_of_surjective (Ideal.Quotient.lift _ (Ideal.Quotient.factor hle) ?_)
    (Ideal.Quotient.lift_surjective_of_surjective _ _ (Ideal.Quotient.factor_surjective hle))
  intro y hy
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  rw [map_mul]
  obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
  simp only [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem.2 hx, mul_zero]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem isRelevant_of_le {Y Z : Ideal (MRing ι)} (hZ : ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant Z) (hY : Y ≤ Z) : ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant Y :=
  fun k => let ⟨i, hi⟩ := hZ k; ⟨i, fun h => hi (hY h)⟩

theorem mem_minimalPrimes {J Q : Ideal (MRing ι)} {n : ℕ} (hQ : IsArithVar Q n) (hJQ : J ≤ Q)
    (hdim : ∀ M ∈ J.minimalPrimes, ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant M → IsHorizontal M → IsArithVar M n) :
    Q ∈ J.minimalPrimes := by
  have hQp : Q.IsPrime := hQ.2.1.1
  refine ⟨⟨hQp, hJQ⟩, fun q hq hqQ => ?_⟩
  have : q.IsPrime := hq.1
  obtain ⟨M, hM, hMq⟩ := Ideal.exists_minimalPrimes_le hq.2
  have hMQ : M ≤ Q := hMq.trans hqQ
  have hQh : Q.comap (C : ℤ →+* MRing ι) = ⊥ := hQ.2.2.1
  have hMh : IsHorizontal M := by
    show M.comap (C : ℤ →+* MRing ι) = ⊥
    rw [eq_bot_iff, ← hQh]
    exact Ideal.comap_mono hMQ
  have hMn := hdim M hM (isRelevant_of_le hQ.2.1.2.2 hMQ) hMh
  have : M.IsPrime := hM.1.1
  refine le_trans ?_ hMq
  by_contra hQM
  obtain ⟨x, hxQ, hxM⟩ := Set.not_subset.1 hQM
  have h := dim_add_one_le hMQ hxQ hxM
  rw [hQ.2.2.2, hMn.2.2.2] at h
  have h2 : n + Fintype.card K + 1 ≤ n + Fintype.card K := by exact_mod_cast h
  omega


open Classical in
theorem sum_block (F : (Σ k', ι' k') → ℕ) (k' : K') :
    ∑ i, F ⟨k', i⟩ = ∑ q, if q.1 = k' then F q else 0 := by
  classical
  rw [Fintype.sum_sigma, Finset.sum_eq_single k']
  · simp
  · intro b _ hb
    simp [hb]
  · simp

theorem isMultiHomog_rename {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {s : MRing ι} {α : K → ℕ} (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s α) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (rename v s) (Function.extend κ α 0) := by
  classical
  intro m' hm' k'
  rw [support_rename_of_injective hv.2.1, Finset.mem_image] at hm'
  obtain ⟨m, hm, rfl⟩ := hm'
  rw [sum_block]
  have h1 : (∑ q, if q.1 = k' then Finsupp.mapDomain v m q else 0) =
      ∑ p, if κ p.1 = k' then m p else 0 := by
    have := Finsupp.sum_mapDomain_index_inj (h := fun (q : Σ k', ι' k') (n : ℕ) => if q.1 = k' then n else 0)
      (s := m) hv.2.1
    rw [Finsupp.sum_fintype _ _ (by simp), Finsupp.sum_fintype _ _ (by simp)] at this
    simpa [hv.2.2.1] using this
  have h2 : (∑ p : Σ k, ι k, if κ p.1 = k' then m p else 0) = ∑ k, if κ k = k' then α k else 0 := by
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs with hk
    · exact hs m hm k
    · simp
  convert h1.trans h2
  by_cases h : ∃ k, κ k = k'
  · obtain ⟨k, rfl⟩ := h
    rw [hv.1.extend_apply, Finset.sum_eq_single k]
    · simp
    · intro b _ hb
      simp [hv.1.ne hb]
    · simp
  · rw [Function.extend_apply' _ _ _ h]
    refine (Finset.sum_eq_zero fun k _ => ?_).symm
    rw [if_neg fun hk => h ⟨k, hk⟩]

end ArithmeticIntersectionHorizontal


open ArithmeticIntersectionHorizontal in
theorem ArithmeticIntersectionHorizontal.proof (hDiv : DivSuppArithStatement) (hIm : ImageArithStatement)
    (hP0 : GroundTheory.Heights₂.Heights.Inter.PushforwardProjectivePoint.Statement) : ArithmeticIntersectionHorizontal.Statement := by
  intro I hI n hn K _ ι _ K' _ ι' _ κ v P' L L' s α W' hv hP' hP hL hLL' hs hsP hW' hh
  classical

  let A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofMetrics (fun k => maxMetric (C := ℂ) (ι := ι k)) (fun k => (α k : ℤ))
  let A' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι' :=
    ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofMetrics (fun k => maxMetric (C := ℂ) (ι := ι' k)) (fun k => ((Function.extend κ α 0 : K' → ℕ) k : ℤ))
  have hsec : IsSectionOn (imageZ v P') A s := ⟨α, fun _ => rfl, hs, hsP⟩
  have hsec' : IsSectionOn P' A' (rename v s) :=
    ⟨Function.extend κ α 0, fun _ => rfl, isMultiHomog_rename hv hs, fun h => hsP (Ideal.mem_comap.mpr h)⟩
  have hW'n : IsArithVar W' n := (hDiv K' ι' P' n A' (rename v s) W' hP' hsec' hW').1 hh
  have hhQ : IsHorizontal (imageZ v W') := isHorizontal_imageZ hh
  obtain ⟨d, hdn, hQd⟩ := hIm K ι K' ι' κ v W' n hP.1 hv hW'n
  rcases hdn.lt_or_eq with hlt | heq
  ·
    right
    refine ⟨fun hm => ?_, hP0 I hI K ι K' ι' κ v W' d n L L' hv hW'n hQd hlt hL hLL'⟩
    have := dim_eq hQd ((hDiv K ι (imageZ v P') n A s _ hP hsec hm).1 hhQ)
    omega
  ·
    left
    rw [heq] at hQd
    have hle := hW'.1.1.2
    have hm : imageZ v W' ∈ divSupp (imageZ v P') s := by
      refine ⟨mem_minimalPrimes hQd ?_ fun M hM hMr hMh => (hDiv K ι (imageZ v P') n A s M hP hsec ⟨hM, hMr⟩).1 hMh,
        hQd.2.1.2.2⟩
      refine sup_le (Ideal.comap_mono (le_sup_left.trans hle)) ?_
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.mem_comap.mpr (hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
    exact ⟨hm, fun G' J' hJ' => hn K ι K' ι' κ v W' G' J' L L' hv hW'n hQd hJ' hL hLL'⟩

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PPFHoriz
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace PFHoriz

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')}

def genMap (G : GenFibre v P') : MRing ι ⧸ imageZ v P' →+* G.Φ :=
  Ideal.Quotient.lift _ (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom
    (fun a ha => by rw [← G.ker_x] at ha; exact RingHom.mem_ker.mp ha)

theorem genMap_mk (G : GenFibre v P') (f : MRing ι) :
    genMap G (Ideal.Quotient.mk _ f) = aeval G.x f := rfl

theorem genMap_injective (G : GenFibre v P') : Function.Injective (genMap G) := by
  refine (injective_iff_map_eq_zero (genMap G).toAddMonoidHom).2 fun a ha => ?_
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
  change genMap G (Ideal.Quotient.mk _ f) = 0 at ha
  rw [genMap_mk] at ha
  rw [Ideal.Quotient.eq_zero_iff_mem, ← G.ker_x]
  exact RingHom.mem_ker.mpr ha

theorem isFractionRing_genMap (G : GenFibre v P') :
    @IsFractionRing (MRing ι ⧸ imageZ v P') _ G.Φ _ (genMap G).toAlgebra := by
  letI := (genMap G).toAlgebra
  haveI : FaithfulSMul (MRing ι ⧸ imageZ v P') G.Φ :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (genMap_injective G)
  refine IsFractionRing.of_field _ _ fun z => ?_
  obtain ⟨f, g, -, rfl⟩ := G.gen z
  exact ⟨Ideal.Quotient.mk _ f, Ideal.Quotient.mk _ g, rfl⟩

def quotIncl (W : Ideal (MRing ι')) [W.IsPrime] (hW : imageZ v W = imageZ v P') :
    MRing ι ⧸ imageZ v P' →+* FractionRing (MRing ι' ⧸ W) :=
  (algebraMap (MRing ι' ⧸ W) (FractionRing (MRing ι' ⧸ W))).comp
    (Ideal.quotientMap W (rename v : MRing ι →ₐ[ℤ] MRing ι').toRingHom hW.symm.le)

theorem quotIncl_injective (W : Ideal (MRing ι')) [W.IsPrime] (hW : imageZ v W = imageZ v P') :
    Function.Injective (quotIncl W hW) :=
  (IsFractionRing.injective (MRing ι' ⧸ W) (FractionRing (MRing ι' ⧸ W))).comp
    (Ideal.quotientMap_injective' (H := hW.symm.le) hW.le)

def genAlg (G : GenFibre v P') (W : Ideal (MRing ι')) [W.IsPrime] (hW : imageZ v W = imageZ v P') :
    G.Φ →+* FractionRing (MRing ι' ⧸ W) :=
  letI := (genMap G).toAlgebra
  haveI := isFractionRing_genMap G
  IsFractionRing.lift (quotIncl_injective W hW)

theorem genAlg_alt (G : GenFibre v P') (W : Ideal (MRing ι')) [W.IsPrime] (hW : imageZ v W = imageZ v P')
    (p : Σ k, ι k) :
    genAlg G W hW (G.x p) =
      algebraMap (MRing ι' ⧸ W) (FractionRing (MRing ι' ⧸ W)) (Ideal.Quotient.mk W (X (v p))) := by
  letI := (genMap G).toAlgebra
  haveI := isFractionRing_genMap G
  have hx : G.x p = algebraMap (MRing ι ⧸ imageZ v P') G.Φ (Ideal.Quotient.mk _ (X p)) := by
    show G.x p = genMap G (Ideal.Quotient.mk _ (X p))
    rw [genMap_mk, aeval_X]
  rw [hx]
  exact (IsFractionRing.lift_algebraMap (quotIncl_injective W hW) _).trans (by
    simp [quotIncl, Ideal.quotientMap_mk])

def xW (W : Ideal (MRing ι')) [W.IsPrime] (q : Σ k', ι' k') : FractionRing (MRing ι' ⧸ W) :=
  algebraMap (MRing ι' ⧸ W) (FractionRing (MRing ι' ⧸ W)) (Ideal.Quotient.mk W (X q))

theorem aeval_xW (W : Ideal (MRing ι')) [W.IsPrime] (f : MRing ι') :
    aeval (R := ℤ) (xW W) f =
      algebraMap (MRing ι' ⧸ W) (FractionRing (MRing ι' ⧸ W)) (Ideal.Quotient.mk W f) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [aeval_C, eq_intCast (algebraMap ℤ (FractionRing (MRing ι' ⧸ W))) a]
    exact (eq_intCast (((algebraMap (MRing ι' ⧸ W) (FractionRing (MRing ι' ⧸ W))).comp
      (Ideal.Quotient.mk W)).comp C) a).symm
  | add p q hp hq =>
    change (aeval (R := ℤ) (xW W)).toRingHom (p + q) = _
    change (aeval (R := ℤ) (xW W)).toRingHom p = _ at hp
    change (aeval (R := ℤ) (xW W)).toRingHom q = _ at hq
    rw [(aeval (R := ℤ) (xW W)).map_add, (Ideal.Quotient.mk W).map_add,
      (algebraMap (MRing ι' ⧸ W) (FractionRing (MRing ι' ⧸ W))).map_add, hp, hq]
  | mul_X p n hp => rw [map_mul, map_mul, map_mul, hp, aeval_X, xW]

theorem ker_aeval_xW (W : Ideal (MRing ι')) [W.IsPrime] :
    RingHom.ker (aeval (R := ℤ) (xW W)) = W := by
  ext f
  rw [RingHom.mem_ker, aeval_xW, map_eq_zero_iff _ (IsFractionRing.injective _ _),
    Ideal.Quotient.eq_zero_iff_mem]

def genFibreOf (G : GenFibre v P') (W : Ideal (MRing ι')) [W.IsPrime] (hW : imageZ v W = imageZ v P') :
    GenFibre v W where
  Φ := G.Φ
  Φ' := FractionRing (MRing ι' ⧸ W)
  alg := (genAlg G W hW).toAlgebra
  x := G.x
  x' := xW W
  ker_x := by rw [hW]; exact G.ker_x
  gen := G.gen
  genericFibre_ker_target := by
    refine Eq.trans ?_ (ker_aeval_xW W)
    ext f
    simp only [RingHom.mem_ker, aeval_def, algebraMap_int_eq]
    rw [RingHom.ext_int (algebraMap ℤ (FractionRing (MRing ι' ⧸ W))) (Int.castRingHom _)]
  compat p := (genAlg_alt G W hW p).symm

theorem baseSubst_rename (hκv : IsBlockMap κ v) (G : GenFibre v P') (f : MRing ι) :
    baseSubst κ G (rename v f) = C (aeval G.x f) := by
  have e : (baseSubst κ G).comp (rename v : MRing ι →ₐ[ℤ] MRing ι').toRingHom =
      (C : G.Φ →+* MRingOver G.Φ (fibreIdx ι' κ)).comp (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun p => ?_)
    · exact RingHom.congr_fun (RingHom.ext_int (((baseSubst κ G).comp
        (rename v : MRing ι →ₐ[ℤ] MRing ι').toRingHom).comp C)
        (((C : G.Φ →+* MRingOver G.Φ (fibreIdx ι' κ)).comp
          (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom).comp C)) a
    · have h1 : (v p).1 ∈ Set.range κ := ⟨p.1, (hκv.2.2.1 p).symm⟩
      have h2 : v p ∈ Set.range v := ⟨p, rfl⟩
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X, aeval_X]
      rw [baseSubst, eval₂Hom_X', dite_eq_left h1, dite_eq_left h2, hκv.2.1 h2.choose_spec]
  exact RingHom.congr_fun e f

theorem exists_clear (hκv : IsBlockMap κ v) (G : GenFibre v P') (g : MRingOver G.Φ (fibreIdx ι' κ)) :
    ∃ (b : MRing ι) (F : MRing ι'), aeval G.x b ≠ 0 ∧ C (aeval G.x b) * g = baseSubst κ G F := by
  induction g using MvPolynomial.induction_on with
  | C a =>
    obtain ⟨f, b, hb, rfl⟩ := G.gen a
    refine ⟨b, rename v f, hb, ?_⟩
    rw [baseSubst_rename hκv, ← C_mul, mul_div_cancel₀ _ hb]
  | add p q hp hq =>
    obtain ⟨b₁, F₁, h₁, e₁⟩ := hp
    obtain ⟨b₂, F₂, h₂, e₂⟩ := hq
    refine ⟨b₁ * b₂, rename v b₂ * F₁ + rename v b₁ * F₂, by rw [map_mul]; exact mul_ne_zero h₁ h₂, ?_⟩
    simp only [map_add (f := _), map_mul, baseSubst_rename hκv, ← e₁, ← e₂]
    ring
  | mul_X p n hp =>
    obtain ⟨b, F, h, e⟩ := hp
    refine ⟨b, F * X ⟨n.1.1, n.2⟩, h, ?_⟩
    rw [map_mul, ← e, mul_assoc]
    congr 2
    rw [baseSubst, eval₂Hom_X', dite_eq_right n.1.2]

theorem ker_eq_map {σ τ Φ Φ' : Type} [Field Φ] [Field Φ'] [Algebra Φ Φ']
    (β : MvPolynomial τ ℤ →+* MvPolynomial σ Φ) (y : σ → Φ') (φ : MvPolynomial τ ℤ →+* Φ')
    (W : Ideal (MvPolynomial τ ℤ)) (hφ : RingHom.ker φ = W) (hcomp : ∀ F, aeval y (β F) = φ F)
    (hclear : ∀ g, ∃ c : Φ, c ≠ 0 ∧ ∃ F, C c * g = β F) :
    RingHom.ker (aeval y : MvPolynomial σ Φ →ₐ[Φ] Φ') = Ideal.map β W := by
  apply le_antisymm
  · intro g hg
    obtain ⟨c, hc, F, e⟩ := hclear g
    have hF : F ∈ W := by
      rw [← hφ, RingHom.mem_ker, ← hcomp, ← e, map_mul, RingHom.mem_ker.mp hg, mul_zero]
    have hg' : g = C c⁻¹ * β F := by
      rw [← e, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hc, C_1, one_mul]
    rw [hg']
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hF)
  · rw [Ideal.map_le_iff_le_comap]
    intro F hF
    rw [Ideal.mem_comap, RingHom.mem_ker, hcomp, ← RingHom.mem_ker, hφ]
    exact hF

variable {W : Ideal (MRing ι')} [W.IsPrime] (hW : imageZ v W = imageZ v P')

theorem aeval_baseSubst (hκv : IsBlockMap κ v) (G : GenFibre v P') (f : MRing ι') :
    letI := (genAlg G W hW).toAlgebra
    aeval (fun q : Σ k : FibreBlock κ, ι' k.1 => xW W ⟨q.1.1, q.2⟩) (baseSubst κ G f) =
      aeval (R := ℤ) (xW W) f := by
  letI := (genAlg G W hW).toAlgebra
  have e : (aeval (fun q : Σ k : FibreBlock κ, ι' k.1 => xW W ⟨q.1.1, q.2⟩) :
        MRingOver G.Φ (fibreIdx ι' κ) →ₐ[G.Φ] FractionRing (MRing ι' ⧸ W)).toRingHom.comp (baseSubst κ G) =
      (aeval (R := ℤ) (xW W)).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun q => ?_)
    · rw [RingHom.comp_apply, baseSubst, eval₂Hom_C,
        eq_intCast (algebraMap ℤ (MRingOver G.Φ (fibreIdx ι' κ))) a, eq_intCast (C : ℤ →+* MRing ι') a,
        map_intCast, map_intCast]
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
      rw [baseSubst, eval₂Hom_X']
      by_cases h : q.1 ∈ Set.range κ
      · have h' : q ∈ Set.range v := hκv.2.2.2 q h
        rw [dite_eq_left h, dite_eq_left h', aeval_C, RingHom.algebraMap_toAlgebra, genAlg_alt, h'.choose_spec]
        rfl
      · rw [dite_eq_right h, aeval_X]
  exact RingHom.congr_fun e f

theorem fibreIdeal_genFibreOf (hκv : IsBlockMap κ v) (G : GenFibre v P') :
    ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ (genFibreOf G W hW) = fibreOf κ G W := by
  letI := (genAlg G W hW).toAlgebra
  exact ker_eq_map (baseSubst κ G) (fun q : Σ k : FibreBlock κ, ι' k.1 => xW W ⟨q.1.1, q.2⟩)
    (aeval (R := ℤ) (xW W)).toRingHom W (ker_aeval_xW W) (aeval_baseSubst hW hκv G)
    (fun g => let ⟨_, F, hb, e⟩ := exists_clear hκv G g; ⟨_, hb, F, e⟩)

end PFHoriz

theorem PFHoriz.proof : PFHoriz.Statement := by
  intro I r hPF K _ ι _ K' _ ι' _ κ v P' W d G J L L' N hκv hW hWP hP hJ hL hLL hN
  haveI : W.IsPrime := hW.2.1.1
  have h := hPF K ι K' ι' κ v W d (PFHoriz.genFibreOf G W hWP) J L L' N hκv hW (by rw [hWP]; exact hP)
    hJ hL hLL hN
  rw [PFHoriz.fibreIdeal_genFibreOf hWP hκv G, hWP] at h
  exact h

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsPFFibreSum
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section


open Classical in
def PFFibreSum.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (d r : ℕ)
    (G : GenFibre v P') (J : IFamily G.Φ (fibreIdx ι' κ))
    (N : Fin (r + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι') (s : MRing ι') (a : K' → ℕ),
    IsBlockMap κ v → IsArithVar P' (d + r + 1) → IsArithVar (imageZ v P') d → IsFieldIntersection J →
    (∀ k, (N (Fin.last r)).a k = a k) → ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a → s ∉ P' →
    ∑ᶠ W ∈ divSupp P' s, (multAt (P' ⊔ Ideal.span {s}) W : ℝ) *
        (if IsHorizontal W ∧ imageZ v W = imageZ v P' then
          (J (fibreOf κ G W) r (fun j => fibreDeg κ (N (Fin.castSucc j)).a) : ℝ) else 0) =
      (J (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G) (r + 1) (fun j => fibreDeg κ (N j).a) : ℝ)

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.NotIsHorizontalSpanTwo
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

def ArithmeticIntersectionVertical.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ)
    (a : Fin n → K → ℤ) (s : MRing ι) (α : K → ℕ) (W' : Ideal (MRing ι')),
    IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') (n + 1) →
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s α → s ∉ imageZ v P' → W' ∈ divSupp P' (rename v s) → ¬ IsHorizontal W' →
    (imageZ v W' ∈ divSupp (imageZ v P') s ∧
        ∀ (G' : GenFibre v W') (J' : IFamily G'.Φ (fibreIdx ι' κ)), IsFieldIntersection J' →
          geoNum n W' (fun j => pullDeg κ (a j)) =
            J' (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G') 0 Fin.elim0 * geoNum n (imageZ v W') a) ∨
      (imageZ v W' ∉ divSupp (imageZ v P') s ∧ geoNum n W' (fun j => pullDeg κ (a j)) = 0)

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.IdDeg
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

def ArithmeticIntersectionDivisorPushforward.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ)
    (G : GenFibre v P') (J : IFamily G.Φ (fibreIdx ι' κ)) (s : MRing ι) (α : K → ℕ)
    (W : Ideal (MRing ι)) (E : Ideal (MRing ι') → ℤ),
    IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') (n + 1) → IsFieldIntersection J →
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s α → s ∉ imageZ v P' → W ∈ divSupp (imageZ v P') s →
    (∀ W' ∈ divSupp P' (rename v s), imageZ v W' = W →
      ∃ (G' : GenFibre v W') (J' : IFamily G'.Φ (fibreIdx ι' κ)),
        IsFieldIntersection J' ∧ E W' = J' (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G') 0 Fin.elim0) →
    ∑ᶠ W' ∈ {W' | W' ∈ divSupp P' (rename v s) ∧ imageZ v W' = W},
        (multAt (P' ⊔ Ideal.span {rename v s}) W' : ℤ) * E W' =
      J (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G) 0 Fin.elim0 * multAt (imageZ v P' ⊔ Ideal.span {s}) W

section Inhabitants


end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsMoreExtra
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def RegularityRelativeClosedPoint.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P W : Ideal (MRing ι)),
    IsArithVar P 1 → IsMultiProjPrime W → P ≤ W → W ≠ P → IsClosedPt W

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PThmIExists
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ThmIExists

theorem ThmIExists.proof (hD1 : RegularityIndependence.Statement) (hMul : RMulStatement) (hWD : WellDefined.Statement)
    (hSymm : ThmISymm.Statement) : ThmIExists.Statement := by
  refine ⟨fun K _ ι _ => famI (K := K) (ι := ι), fun K _ ι _ => ?_⟩
  have hRF : IsRFamily (famI (K := K) (ι := ι)) :=
    isRFamily_famI hD1 hMul fun n hR hA P L B s t hP hL hB hs ht =>
      hWD K ι famI P n L B s t hR hA hP hL hB hs ht
  exact ⟨hSymm K ι _ hRF, hRF.1, hRF.2⟩

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsBlockGenFinite
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def BlockGenFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ),
    IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') (n + 1) →
    ∃ (f₀ : MRing ι') (a : K' → ℕ), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f₀ a ∧ f₀ ∉ P' ∧
      ∀ u : (Σ k, ι k) → ℂ, ∃ T : Finset ((Σ k', ι' k') → ℂ),
        ∀ z' ∈ mcPts P', eval z' (map (Int.castRingHom ℂ) f₀) ≠ 0 →
          SameOrbit (fun p => z' (v p)) u → ∃ t ∈ T, SameOrbit z' t

section Inhabitants

open IndefiniteRowSideFullHecke.Inter

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreIsolFinite
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def FibreIsolFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ),
    IsBlockMap κ v → IsArithVar P' (n + 1) →
    ∀ u : (Σ k, ι k) → ℂ, ∃ T : Finset ((Σ k', ι' k') → ℂ),
      ∀ z' ∈ mcPts P', SameOrbit (fun p => z' (v p)) u →
        (∃ ε > 0, ∀ z'' ∈ mcPts P', SameOrbit (fun p => z'' (v p)) u → dist z'' z' < ε →
          SameOrbit z'' z') →
        ∃ t ∈ T, SameOrbit z' t

section Inhabitants

open IndefiniteRowSideFullHecke.Inter

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.ExistsIntValuationLtOne
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def RegularityValuationCentre.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)),
    IsMultiProjPrime P → ∀ (Γ : Type) [LinearOrderedCommGroupWithZero Γ] (v : Valuation (funField P) Γ) (n : ℤ),
    v (n : funField P) < 1 →
    ∃ W : Ideal (MRing ι), IsMultiProjPrime W ∧ P ≤ W ∧ C n ∈ W ∧
      ∀ z : funField P, (z : FractionRing (MRing ι ⧸ P)) ∈ locRing P W → v z ≤ 1

theorem RegularityValuationCentre.exists_int_valuation_lt_one {F : Type*} [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    ∃ n : ℤ, n ≠ 0 ∧ v.valuation F (n : F) < 1 := by
  obtain ⟨x, hxv, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  have hc : v.asIdeal.comap (algebraMap ℤ (NumberField.RingOfIntegers F)) ≠ ⊥ :=
    Ideal.comap_ne_bot_of_integral_mem hx0 hxv (Algebra.IsIntegral.isIntegral x)
  obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
  refine ⟨n, hn0, ?_⟩
  have e : (n : F) = algebraMap (NumberField.RingOfIntegers F) F (algebraMap ℤ _ n) := by simp
  rw [e, IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem]
  exact hn

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsBisSide
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem RegularityFormula.proof (hN : RegularityFunctionFieldNumber.Statement) (hO : RegularityOrder.Statement)
    (hL : RegularityLocal.Statement) : RegularityFormula.Statement := by
  classical
  intro K _ ι _ P b hP hb hbW
  obtain ⟨hF, hNF⟩ := hN K ι P hP
  let _ := hF.toField
  have := hNF
  obtain ⟨hfree, hfin, hrank⟩ := hO K ι P hP
  let b' : regRing P := ⟨b, hbW⟩
  have hb' : b' ≠ 0 := fun h => hb (congrArg Subtype.val h)
  obtain ⟨hfs, hsum⟩ := hL K ι P b' hP hb'
  refine ⟨hfs, hsum.trans ?_⟩
  have hI := (ReciprocityTheory.ChartRestriction.G.AI.index_thm (funField P) (regRing P) hfree hfin (hrank hF) b' hb').2
  exact hI.trans (finsum_eq_sum_of_fintype _).symm

end

end GroundTheory.Heights₂.Heights.Inter
end
