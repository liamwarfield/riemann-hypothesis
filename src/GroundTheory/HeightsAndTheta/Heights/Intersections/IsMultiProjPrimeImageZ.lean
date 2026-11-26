module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.TableDegreeThreeBase
public import GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiHomogRenameCoordPow
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PZeroSetNull

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiProjPrimeImageZ
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace PointVertical

section Reduction

variable {K : Type} {ι : K → Type} (p : ℕ)

abbrev red : MRing ι →+* MRingOver (ZMod p) ι := MvPolynomial.map (Int.castRingHom (ZMod p))

theorem red_surjective : Function.Surjective (red (ι := ι) p) :=
  MvPolynomial.map_surjective _ (fun x => ZMod.intCast_surjective x)

theorem ker_red_le {J : Ideal (MRing ι)} (hp : ((p : ℕ) : MRing ι) ∈ J) :
    RingHom.ker (red (ι := ι) p) ≤ J := by
  rw [MvPolynomial.ker_map, ZMod.ker_intCastRingHom, Ideal.map_span, Set.image_singleton, Ideal.span_le,
    Set.singleton_subset_iff]
  simpa using hp

theorem mem_map_red_iff {J : Ideal (MRing ι)} (hp : ((p : ℕ) : MRing ι) ∈ J) (g : MRing ι) :
    red p g ∈ J.map (red p) ↔ g ∈ J := by
  rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective _ (red_surjective p), sup_eq_left.mpr]
  rw [← RingHom.ker_eq_comap_bot]
  exact ker_red_le p hp

theorem ringKrullDim_red {J : Ideal (MRing ι)} (hp : ((p : ℕ) : MRing ι) ∈ J) :
    ringKrullDim (MRingOver (ZMod p) ι ⧸ J.map (red p)) = ringKrullDim (MRing ι ⧸ J) := by
  have e : J = RingHom.ker ((Ideal.Quotient.mk (J.map (red p))).comp (red p)) := by
    ext g
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, mem_map_red_iff p hp]
  exact (ringKrullDim_eq_of_ringEquiv ((Ideal.quotEquivOfEq e).trans
    (RingHom.quotientKerEquivOfSurjective (Ideal.Quotient.mk_surjective.comp (red_surjective p))))).symm

theorem isMultiProjPrime_red [∀ k, Fintype (ι k)] {J : Ideal (MRing ι)} (hJ : IsMultiProjPrime J)
    (hp : ((p : ℕ) : MRing ι) ∈ J) : IsMultiProjPrime (J.map (red p)) := by
  obtain ⟨hJp, ⟨S, hS, hJS⟩, hJr⟩ := hJ
  refine ⟨Ideal.map_isPrime_of_surjective (red_surjective p) (ker_red_le p hp),
    ⟨red p '' S, ?_, by rw [hJS, Ideal.map_span]⟩, fun k => ?_⟩
  · rintro _ ⟨f, hf, rfl⟩
    obtain ⟨a, ha⟩ := hS f hf
    exact ⟨a, fun m hm => ha m (support_map_subset _ _ hm)⟩
  · obtain ⟨i, hi⟩ := hJr k
    refine ⟨i, fun h => hi ((mem_map_red_iff p hp _).mp ?_)⟩
    rw [map_X]
    exact h

variable {K' : Type} {ι' : K' → Type}

theorem imageVar_red [Fact p.Prime] (v : (Σ k, ι k) → (Σ k', ι' k')) {W : Ideal (MRing ι')}
    (hp : ((p : ℕ) : MRing ι') ∈ W) :
    imageVar (ZMod p) v (W.map (red p)) = (imageZ v W).map (red p) := by
  have hp' : ((p : ℕ) : MRing ι) ∈ imageZ v W := by
    show rename v ((p : ℕ) : MRing ι) ∈ W
    simpa using hp
  ext f
  obtain ⟨g, rfl⟩ := red_surjective p f
  rw [mem_map_red_iff p hp' g]
  show rename v (red p g) ∈ W.map (red p) ↔ rename v g ∈ W
  rw [← map_rename, mem_map_red_iff p hp]

theorem isMultiHomog_rename [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {t : MRing ι} {a : K → ℕ} (ht : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog t a) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (rename v t) (Function.extend κ a 0) := by
  classical
  have ht' := (Bridge.isMultiHomog_iff t a).mpr ht
  refine (Bridge.isMultiHomog_iff _ _).mp ?_
  have e := FieldNumbers.ContractRelevant.rename_weightedHomogeneousComponent hv.2.2.1 hv.1 hv.2.1 a t
  rw [IsWeightedHomogeneous.weightedHomogeneousComponent_same ht'] at e
  rw [e]
  exact weightedHomogeneousComponent_isWeightedHomogeneous _ _

theorem isMultiProjPrime_imageZ [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {W : Ideal (MRing ι')} (hW : IsMultiProjPrime W) : IsMultiProjPrime (imageZ v W) := by
  classical
  have h := FieldNumbers.ContractRelevant.isMultiProjPrime_comap_rename (R := ℤ) hv.2.2.1 hv.1 hv.2.1
    (fun w hw => hv.2.2.2 w hw) ((Bridge.isMultiProjPrime_iff W).mpr hW)
  exact (Bridge.isMultiProjPrime_iff _).mp h

end Reduction

theorem exists_dim_F {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (p : ℕ) [Fact p.Prime]
    (V : Ideal (MRingOver (ZMod p) ι)) (hV : IsMultiProjPrime V) :
    ∃ D : ℕ, Fintype.card K ≤ D ∧ ringKrullDim (MRingOver (ZMod p) ι ⧸ V) = D := by
  classical
  have := hV.1
  have hmh := (Bridge.isMultiHomogIdeal_iff V).mpr hV.2.1
  exact FieldNumbers.PFContracted.exists_ringKrullDim_eq
    (fun T q hq => FieldNumbers.PFContracted.killBlocks_mem_of_isMultiHomogIdeal hmh T hq) hV.2.2

theorem geoNum_eq_zero
    (hGeo : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], GeoNumStatement ι)
    (hR4 : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι)
    (hPC : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)], ProjContractStatement F ι ι')
    {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
    {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v) {P' : Ideal (MRing ι')} {d n : ℕ}
    (hP : IsArithVar (imageZ v P') d) (hdn : d < n + 1) {W : Ideal (MRing ι')} (hPW : P' ≤ W)
    (hWm : IsMultiProjPrime W) (hpr : (charOf W).Prime)
    (hWd : ringKrullDim (MRing ι' ⧸ W) = ((n + Fintype.card K' : ℕ) : WithBot ℕ∞)) (L : Fin n → K → ℤ) :
    geoNum n W (fun j => pullDeg κ (L j)) = 0 := by
  set p := charOf W with hpdef
  have : Fact p.Prime := ⟨hpr⟩
  have hpW : ((p : ℕ) : MRing ι') ∈ W := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.natCast_mem_of_charOf W
  have hWp : IsProjVarF (W.map (red p)) n := ⟨isMultiProjPrime_red p hWm hpW, by rw [ringKrullDim_red p hpW, hWd]⟩
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
  rw [hGeo K' ι' p I hI W n _ hWm hpW hWp]
  exact hPC (ZMod p) K ι K' ι' I hI κ v _ n _ L hv hWp hVi (by omega)

end PointVertical


open PointVertical in
theorem ProjectivePointVertical.proof
    (hGeo : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], GeoNumStatement ι)
    (hR4 : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι)
    (hPC : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)], ProjContractStatement F ι ι') :
    ProjectivePointVertical.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' d n L L' t a hv hP' hP hdn hL ht htQ
  classical
  have hs : IsSectionOn P' (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.sqMetric (ι := ι') (Function.extend κ a 0)) (rename v t) :=
    ⟨Function.extend κ a 0, fun _ => rfl, isMultiHomog_rename hv ht, htQ⟩
  unfold vertR
  refine finsum_mem_eq_zero_of_forall_eq_zero fun W hW => ?_
  obtain ⟨-, hvert⟩ := divSuppArith K' ι' P' n _ _ W hP' hs hW
  by_cases hh : IsHorizontal W
  · simp [hh]
  · obtain ⟨hWm, hpr, hWd⟩ := hvert hh
    have hPW : P' ≤ W := le_sup_left.trans hW.1.1.2
    have e : (fun j => (L' j).a) = fun j => pullDeg κ (L j).a := funext fun j => (hL j).1
    simp only [if_neg hh, e, geoNum_eq_zero hGeo hR4 hPC hv hP hdn hPW hWm hpr hWd (fun j => (L j).a)]
    simp

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.QuotientMapImageZInjective
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

section GenPt

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]


omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem quotientMap_imageZ_injective (v : (Σ k, ι k) → (Σ k', ι' k')) (W' : Ideal (MRing ι')) :
    Function.Injective (Ideal.quotientMap W' (rename v : MRing ι →ₐ[ℤ] MRing ι').toRingHom
      (le_refl (imageZ v W'))) :=
  Ideal.quotientMap_injective' le_rfl


omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in
instance imageZ_isPrime (v : (Σ k, ι k) → (Σ k', ι' k')) (W' : Ideal (MRing ι')) [W'.IsPrime] :
    (imageZ v W').IsPrime :=
  Ideal.IsPrime.comap _

def genFibreOf (v : (Σ k, ι k) → (Σ k', ι' k')) (W' : Ideal (MRing ι')) [W'.IsPrime] : GenFibre v W' :=
  letI g : MRing ι ⧸ imageZ v W' →+* FnField W' :=
    (algebraMap (MRing ι' ⧸ W') (FnField W')).comp
      (Ideal.quotientMap W' (rename v : MRing ι →ₐ[ℤ] MRing ι').toRingHom (le_refl (imageZ v W')))
  have hg : Function.Injective g :=
    (IsFractionRing.injective (MRing ι' ⧸ W') (FnField W')).comp (quotientMap_imageZ_injective v W')
  letI alg : Algebra (FnField (imageZ v W')) (FnField W') :=
    (IsFractionRing.lift (K := FnField (imageZ v W')) hg).toAlgebra
  { Φ := FnField (imageZ v W')
    Φ' := FnField W'
    alg := alg
    x := IndefiniteRowSideFullHecke.Inter.genPt (imageZ v W')
    x' := IndefiniteRowSideFullHecke.Inter.genPt W'
    ker_x := by
      ext f
      rw [RingHom.mem_ker, aeval_genPt]
      exact SetLike.ext_iff.1 (ker_algebraMap_comp_mk (imageZ v W')) f
    gen := fun c => by
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := MRing ι ⧸ imageZ v W') c
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective b
      refine ⟨f, g, ?_, ?_⟩
      · rw [aeval_genPt]
        exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
      · rw [aeval_genPt, aeval_genPt]
    genericFibre_ker_target := by
      ext f
      rw [RingHom.mem_ker, aeval_genPt]
      exact SetLike.ext_iff.1 (ker_algebraMap_comp_mk W') f
    compat := fun p => by
      show IndefiniteRowSideFullHecke.Inter.genPt W' (v p) = IsFractionRing.lift hg (IndefiniteRowSideFullHecke.Inter.genPt (imageZ v W') p)
      rw [IndefiniteRowSideFullHecke.Inter.genPt, IndefiniteRowSideFullHecke.Inter.genPt, IsFractionRing.lift_algebraMap]
      simp [g, Ideal.quotientMap_mk] }

theorem GenericPointExists.proof : GenericPointExists.Statement := by
  intro K _ ι _ K' _ ι' _ v W' hW'
  exact ⟨genFibreOf v W'⟩

end GenPt

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PtsIntegralLogNormRat
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2
  ReciprocityTheory.ChartRestriction.G.AI.I4

namespace ArithmeticIntersectionIntegral

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

theorem ae_eval_ne_zero {P : Ideal (MRing ι)} {e : ℕ} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) {h : MRing ι} (hh : ∃ a, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog h a)
    (hhP : h ∉ P) :
    ∀ᵐ y : Fin e → ℂ, ∀ z ∈ mcPts P, Ψ (segre z) = Fin.cons 1 y →
      eval z (map (Int.castRingHom ℂ) h) ≠ 0 := by
  have hJ : IsMultiHomogIdeal (Ideal.span {h} : Ideal (MRing ι)) :=
    ⟨{h}, fun f hf => by rw [Set.mem_singleton_iff.mp hf]; exact hh, rfl⟩
  have hJP : ¬ (Ideal.span {h} : Ideal (MRing ι)) ≤ P := by
    rwa [Ideal.span_singleton_le_iff_mem]
  have hnull := projB_null Ψ hP hΨ hJ hJP
  refine ae_iff.mpr (measure_mono_null (fun y hy => ?_) hnull)
  simp only [Set.mem_ofPred_eq, not_forall, not_not] at hy
  obtain ⟨z, hz, hzy, hz0⟩ := hy
  refine ⟨z, hz, ⟨hz.1, fun q hq => ?_⟩, hzy⟩
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hq
  simp [hz0]

theorem ptsIntegral_logNormRat (hInt : PtsIntegrableStatement) {P : Ideal (MRing ι)} {n : ℕ}
    {L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {A B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {f g : MRing ι} (hP : IsArithVar P (n + 1))
    (hL : ∀ j, IsSmoothHerm (L j)) (hA : IsSmoothHerm A) (hB : IsSmoothHerm B)
    (hf : IsSectionOn P (A.tensor B) f) (hg : IsSectionOn P B g) :
    ptsIntegral P (pot L) (logNormRat A f g) =
      ptsIntegral P (pot L) (logNorm (A.tensor B) f) - ptsIntegral P (pot L) (logNorm B g) := by
  have hAB := isSmoothHerm_tensor hA hB
  obtain ⟨α, -, hfα, hfP⟩ := id hf
  obtain ⟨β, -, hgβ, hgP⟩ := id hg
  unfold ptsIntegral
  split_ifs with hΨ
  · have hΨg : IsGoodProj P hΨ.choose := hΨ.choose_spec
    unfold ptsIntegralAt
    rw [← integral_sub (hInt K ι P n _ L _ f hP hΨg hL hAB hf) (hInt K ι P n _ L _ g hP hΨg hL hB hg)]
    refine integral_congr_ae ?_
    filter_upwards [ae_eval_ne_zero hP hΨg ⟨α, hfα⟩ hfP, ae_eval_ne_zero hP hΨg ⟨β, hgβ⟩ hgP]
      with y hyf hyg
    rw [← finsum_mem_sub_distrib _ _ (fibreFinite K ι P n _ hP hΨg y)]
    refine finsum_mem_congr rfl fun w _ => ?_
    unfold sheetDensity
    split_ifs with hγ
    · have hs := hγ.choose_spec.2.self_of_nhds
      set z := hγ.choose y
      have hz : z ∈ mcPts P := hs.2.1
      have hf0 := norm_pos_iff.mpr (hyf z hz hs.2.2)
      have hg0 := norm_pos_iff.mpr (hyg z hz hs.2.2)
      have hA0 := A.pos z hz.1
      have hB0 := B.pos z hz.1
      rw [← sub_mul]
      congr 1
      show Real.log (‖eval z (map (Int.castRingHom ℂ) f)‖ / ‖eval z (map (Int.castRingHom ℂ) g)‖ / A.h z) =
        Real.log (‖eval z (map (Int.castRingHom ℂ) f)‖ / (A.h z * B.h z)) -
          Real.log (‖eval z (map (Int.castRingHom ℂ) g)‖ / B.h z)
      rw [Real.log_div hf0.ne' (mul_pos hA0 hB0).ne', Real.log_mul hA0.ne' hB0.ne',
        Real.log_div hg0.ne' hB0.ne', Real.log_div (div_pos hf0 hg0).ne' hA0.ne',
        Real.log_div hf0.ne' hg0.ne']
      ring
    · simp
  · simp

theorem isSmoothHerm_pull {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {A' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι'} (hA : IsSmoothHerm A) (h : IsPullHerm κ v A A') :
    IsSmoothHerm A' := by
  have e : A'.h = A.h ∘ fun z' p => z' (v p) := funext h.2
  unfold IsSmoothHerm
  rw [e]
  refine hA.comp (contDiff_pi.2 fun p => contDiff_apply ℝ (fun _ => ℂ) (v p)).contDiffOn ?_
  intro z' hz'
  simp only [Set.mem_ofPred_eq] at hz' ⊢
  intro k
  obtain ⟨i', hi'⟩ := hz' (κ k)
  obtain ⟨p, hp⟩ := hv.2.2.2 ⟨κ k, i'⟩ ⟨k, rfl⟩
  have h2 : p.1 = k := hv.1 (by rw [← hv.2.2.1 p, hp])
  obtain ⟨pk, pi⟩ := p
  simp only at h2
  subst h2
  exact ⟨pi, by rw [hp]; exact hi'⟩


omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem pullDeg_add (κ : K → K') (a b : K → ℤ) : pullDeg κ (a + b) = pullDeg κ a + pullDeg κ b := by
  funext k'
  simp only [pullDeg, Pi.add_apply]
  unfold Function.extend
  split_ifs <;> simp


omit [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] in
theorem isPullHerm_tensor {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {A B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι}
    {A' B' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι'} (hA : IsPullHerm κ v A A') (hB : IsPullHerm κ v B B') :
    IsPullHerm κ v (A.tensor B) (A'.tensor B') := by
  refine ⟨?_, fun z' => ?_⟩
  · show A'.a + B'.a = pullDeg κ (A.a + B.a)
    rw [pullDeg_add, hA.1, hB.1]
  · show A'.h z' * B'.h z' = A.h _ * B.h _
    rw [hA.2, hB.2]


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

end ArithmeticIntersectionIntegral


open ArithmeticIntersectionIntegral in
theorem ArithmeticIntersectionIntegral.proof (hInt : PtsIntegrableStatement) (hSec : IntersectionWithSection.Statement) : ArithmeticIntersectionIntegral.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n G J L L' A A' f g hv hP' hP hJ hL hLL' hA hAA' hfg
  obtain ⟨α, β, hf, hg, hfP, hgP, hαβ⟩ := hfg
  have hB : IsSmoothHerm (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.sqMetric (ι := ι) β) := isSmoothHerm_sqMetric β
  have hBB' := IndefiniteRowSideFullHecke.Inter.isPullHerm_pullHerm hv (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.sqMetric (ι := ι) β)
  have hB' := isSmoothHerm_pull hv hB hBB'
  have hA' := isSmoothHerm_pull hv hA hAA'
  have hL' : ∀ j, IsSmoothHerm (L' j) := fun j => isSmoothHerm_pull hv (hL j) (hLL' j)
  have hfs : IsSectionOn (imageZ v P') (A.tensor (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.sqMetric β)) f := by
    refine ⟨α, fun k => ?_, hf, hfP⟩
    show A.a k + (β k : ℤ) = α k
    rw [← hαβ k]
    ring
  have hgs : IsSectionOn (imageZ v P') (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.sqMetric (ι := ι) β) g := ⟨β, fun k => rfl, hg, hgP⟩
  have hfs' : IsSectionOn P' (A'.tensor (IndefiniteRowSideFullHecke.Inter.pullHerm hv (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.sqMetric β))) (rename v f) := by
    refine ⟨Function.extend κ α 0, fun k' => ?_, isMultiHomog_rename hv hf,
      fun h => hfP (Ideal.mem_comap.mpr h)⟩
    show A'.a k' + pullDeg κ (fun k => (β k : ℤ)) k' = _
    rw [hAA'.1, pullDeg, pullDeg]
    by_cases h : ∃ k, κ k = k'
    · obtain ⟨k, rfl⟩ := h
      rw [hv.1.extend_apply, hv.1.extend_apply, hv.1.extend_apply, ← hαβ k]
      ring
    · rw [Function.extend_apply' _ _ _ h, Function.extend_apply' _ _ _ h, Function.extend_apply' _ _ _ h]
      simp
  have hgs' : IsSectionOn P' (IndefiniteRowSideFullHecke.Inter.pullHerm hv (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.sqMetric (ι := ι) β)) (rename v g) := by
    refine ⟨Function.extend κ β 0, fun k' => ?_, isMultiHomog_rename hv hg,
      fun h => hgP (Ideal.mem_comap.mpr h)⟩
    show pullDeg κ (fun k => (β k : ℤ)) k' = _
    rw [pullDeg]
    by_cases h : ∃ k, κ k = k'
    · obtain ⟨k, rfl⟩ := h
      rw [hv.1.extend_apply, hv.1.extend_apply]
    · rw [Function.extend_apply' _ _ _ h, Function.extend_apply' _ _ _ h]
      simp
  rw [ptsIntegral_logNormRat hInt hP' hL' hA' hB' hfs' hgs', ptsIntegral_logNormRat hInt hP hL hA hB hfs hgs,
    hSec K ι K' ι' κ v P' n G J L L' _ _ f hv hP' hP hJ hL hLL' (isSmoothHerm_tensor hA hB)
      (isPullHerm_tensor hAA' hBB') hfs,
    hSec K ι K' ι' κ v P' n G J L L' _ _ g hv hP' hP hJ hL hLL' hB hBB' hgs, mul_sub]

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PSheetHessPSD
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open scoped ComplexOrder

theorem analyticAt_of_eventually_differentiableAt {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {e : ℕ} {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {y : Fin e → ℂ}
    (h : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ γ y') : AnalyticAt ℂ γ y := by
  obtain ⟨U, hU, hUo, hyU⟩ := eventually_nhds_iff.mp h
  rw [analyticAt_pi_iff]
  intro p
  exact osgood e U (fun y' => γ y' p) hUo
    (fun y' hy' => ((differentiableAt_pi.mp (hU y' hy')) p).differentiableWithinAt) y hyU

theorem SheetHessPSD.proof : SheetHessPSD.Statement := by
  intro K _ ι _ P e Ψ M y w γ hM hPos hγ
  have hev := hγ.2
  have hγy : γ y ∈ mcPts P := hev.self_of_nhds.2.1
  have hz : ∀ k, ∃ i, γ y ⟨k, i⟩ ≠ 0 := hγy.1
  have han : AnalyticAt ℂ γ y :=
    analyticAt_of_eventually_differentiableAt (hev.mono fun _ h => h.1)
  have hUo := SemipositiveTwist.isOpen_noZeroBlock (ι := ι)
  have hlog : ContDiffAt ℝ 2 (fun z => Real.log (M.h z)) (γ y) :=
    ((hM.contDiffAt (hUo.mem_nhds hz)).of_le (WithTop.coe_le_coe.2 le_top)).log (M.pos _ hz).ne'
  have hcomp : (fun y' => Real.log (M.h (γ y'))) = (fun z => Real.log (M.h z)) ∘ γ := rfl
  have hC2 : ContDiffAt ℝ 2 (fun y' => Real.log (M.h (γ y'))) y := by
    rw [hcomp]
    exact hlog.comp y (han.restrictScalars.contDiffAt)
  show (ReciprocityTheory.AnForm.hessC (fun y' => Real.log (M.h (γ y'))) y).PosSemidef
  refine ReciprocityTheory.AnForm.M.hessC_posSemidef _ y hC2 fun x => ?_
  rw [hcomp, ReciprocityTheory.AnForm.levi_comp x han hlog]
  have hL := SemipositiveTwist.laplacian_line_eq_levi hlog (fderiv ℂ γ y x)
  have hΔ := hPos (γ y) hz (fderiv ℂ γ y x)
  linarith

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PullBad
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M

section Pull

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {P' J' : Ideal (MRing ι')} {n : ℕ}

def pullPt (R : AnLogRes P' J' n) (v : (Σ k, ι k) → (Σ k', ι' k')) (x : R.X) : (Σ k, ι k) → ℂ :=
  fun p => R.lift x x (v p)

def pullQ (R : AnLogRes P' J' n) (v : (Σ k, ι k) → (Σ k', ι' k'))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (x : R.X) : Fin n → ℂ :=
  fun i => Ψ (segre (pullPt R v x)) i.succ / Ψ (segre (pullPt R v x)) 0

def pullW (R : AnLogRes P' J' n) (v : (Σ k, ι k) → (Σ k', ι' k'))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (x : R.X) : ((k : K) → ι k) → ℂ :=
  (Ψ (segre (pullPt R v x)) 0)⁻¹ • segre (pullPt R v x)

def pullBad (R : AnLogRes P' J' n) (v : (Σ k, ι k) → (Σ k', ι' k'))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) : Set R.X :=
  {x | R.lift x x ∈ mcPts J'} ∪ {x | Ψ (segre (pullPt R v x)) 0 = 0} ∪
    {x | ∃ j, x ∈ (R.A.chart j).source ∧
      ¬ (AnalyticAt ℂ (pullQ R v Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) ∧
        LinearMap.det (fderiv ℂ (pullQ R v Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) :
          (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ≠ 0)}

end Pull

def pullbackPushforward_holds.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' J' : Ideal (MRing ι')) (n : ℕ)
    (R : AnLogRes P' J' n) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)),
    IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') (n + 1) →
    IsGoodProj (imageZ v P') Ψ →
    (∀ j, volume ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' pullBad R v Ψ) = 0) ∧
      ∀ y, (pullQ R v Ψ ⁻¹' {y} \ pullBad R v Ψ).Finite

section Inhabitants

open IndefiniteRowSideFullHecke.Inter

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.IsHorizontalSpanXb
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

def ArithmeticIntersectionHorizontal.Statement : Prop :=
  ∀ (I : AllFam), I.IsFamily → ∀ n : ℕ, GenDegAt I n →
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
      (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι'))
      (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (L' : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι') (s : MRing ι) (α : K → ℕ) (W' : Ideal (MRing ι')),
      IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') (n + 1) →
      (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) →
      ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s α → s ∉ imageZ v P' → W' ∈ divSupp P' (rename v s) → IsHorizontal W' →
      (imageZ v W' ∈ divSupp (imageZ v P') s ∧
          ∀ (G' : GenFibre v W') (J' : IFamily G'.Φ (fibreIdx ι' κ)), IsFieldIntersection J' →
            I K' ι' W' n L' = (J' (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G') 0 Fin.elim0 : ℝ) * I K ι (imageZ v W') n L) ∨
        (imageZ v W' ∉ divSupp (imageZ v P') s ∧ I K' ι' W' n L' = 0)

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.LogCardLocIdealUnitMul
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem card_quot_span_mul {S : Type*} [CommRing S] [IsDomain S] (u v : S) (hu : u ≠ 0) :
    Nat.card (S ⧸ Ideal.span {u * v}) = Nat.card (S ⧸ Ideal.span {u}) * Nat.card (S ⧸ Ideal.span {v}) := by
  let f : S →+ S := AddMonoidHom.mulLeft u
  have hf : Function.Injective f := fun a b h => mul_left_cancel₀ hu h
  have e1 : (Ideal.span {v}).toAddSubgroup.map f = (Ideal.span {u * v}).toAddSubgroup := by
    ext z
    simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨_, ⟨r, rfl⟩, rfl⟩
      exact ⟨r, by simp only [f, AddMonoidHom.coe_mulLeft]; ring⟩
    · rintro ⟨r, rfl⟩
      exact ⟨r * v, ⟨r, rfl⟩, by simp only [f, AddMonoidHom.coe_mulLeft]; ring⟩
  have e2 : (⊤ : AddSubgroup S).map f = (Ideal.span {u}).toAddSubgroup := by
    ext z
    simp only [AddSubgroup.mem_map, AddSubgroup.mem_top, true_and, Submodule.mem_toAddSubgroup,
      Ideal.mem_span_singleton', f, AddMonoidHom.coe_mulLeft]
    exact ⟨fun ⟨y, hy⟩ => ⟨y, by rw [← hy, mul_comm]⟩, fun ⟨r, hr⟩ => ⟨r, by rw [← hr, mul_comm]⟩⟩
  have hle : (Ideal.span {u * v}).toAddSubgroup ≤ (Ideal.span {u}).toAddSubgroup :=
    fun z hz => Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_right u v) hz
  have h2 : (Ideal.span {u * v}).toAddSubgroup.relIndex (Ideal.span {u}).toAddSubgroup =
      (Ideal.span {v}).toAddSubgroup.index := by
    rw [← e1, ← e2, AddSubgroup.relIndex_map_map_of_injective _ _ hf, AddSubgroup.relIndex_top_right]
  have hc : ∀ I : Ideal S, Nat.card (S ⧸ I) = I.toAddSubgroup.index :=
    fun I => (AddSubgroup.index_eq_card _).symm
  rw [hc, hc, hc, ← AddSubgroup.relIndex_mul_index hle, h2, mul_comm]

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem log_card_locIdeal_mul {P W : Ideal (MRing ι)} [P.IsPrime] {y₁ y₂ : FractionRing (MRing ι ⧸ P)}
    (h₁ : y₁ ∈ locRing P W) (h₂ : y₂ ∈ locRing P W) (hne : y₁ ≠ 0)
    (hf₁ : Finite (locRing P W ⧸ locIdeal P W y₁)) (hf₂ : Finite (locRing P W ⧸ locIdeal P W y₂)) :
    Real.log (Nat.card (locRing P W ⧸ locIdeal P W (y₁ * y₂))) =
      Real.log (Nat.card (locRing P W ⧸ locIdeal P W y₁)) + Real.log (Nat.card (locRing P W ⧸ locIdeal P W y₂)) := by
  rw [locIdeal_eq_span h₁] at hf₁ ⊢
  rw [locIdeal_eq_span h₂] at hf₂ ⊢
  rw [locIdeal_eq_span (mul_mem h₁ h₂)]
  have : (⟨y₁ * y₂, mul_mem h₁ h₂⟩ : locRing P W) = ⟨y₁, h₁⟩ * ⟨y₂, h₂⟩ := rfl
  rw [this, card_quot_span_mul _ _ (fun h => hne (congrArg Subtype.val h)), Nat.cast_mul,
    Real.log_mul (Nat.cast_ne_zero.mpr Nat.card_pos.ne') (Nat.cast_ne_zero.mpr Nat.card_pos.ne')]

theorem log_card_locIdeal_unit {P W : Ideal (MRing ι)} [P.IsPrime] {y z : FractionRing (MRing ι ⧸ P)}
    (hy : y ∈ locRing P W) (hz : z ∈ locRing P W) (h : y * z = 1) :
    Real.log (Nat.card (locRing P W ⧸ locIdeal P W y)) = 0 := by
  rw [locIdeal_eq_span hy, Ideal.span_singleton_eq_top.mpr
    (IsUnit.of_mul_eq_one (⟨z, hz⟩ : locRing P W) (Subtype.ext h))]
  have : Subsingleton (locRing P W ⧸ (⊤ : Ideal (locRing P W))) := Ideal.Quotient.subsingleton_iff.mpr rfl
  rw [Nat.card_of_subsingleton (0 : locRing P W ⧸ (⊤ : Ideal (locRing P W)))]
  simp

theorem log_card_locIdeal_unit_mul {P W : Ideal (MRing ι)} [P.IsPrime] {y z c : FractionRing (MRing ι ⧸ P)}
    (hy : y ∈ locRing P W) (hz : z ∈ locRing P W) (h : y * z = 1) (hc : c ∈ locRing P W) :
    Real.log (Nat.card (locRing P W ⧸ locIdeal P W (y * c))) =
      Real.log (Nat.card (locRing P W ⧸ locIdeal P W c)) := by
  rw [locIdeal_eq_span (mul_mem hy hc), locIdeal_eq_span hc]
  have : (⟨y * c, mul_mem hy hc⟩ : locRing P W) = ⟨y, hy⟩ * ⟨c, hc⟩ := rfl
  rw [this, Ideal.span_singleton_mul_left_unit (IsUnit.of_mul_eq_one (⟨z, hz⟩ : locRing P W) (Subtype.ext h))]

theorem frac_mem_locRing {P W : Ideal (MRing ι)} (hPW : P ≤ W) {u v : MRing ι} {a : K → ℕ}
    (hu : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog u a) (hv : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog v a) (hvW : v ∉ W) [P.IsPrime] {y : FractionRing (MRing ι ⧸ P)}
    (hy : y * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P v) =
      algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u)) :
    y ∈ locRing P W := by
  have hvP : Ideal.Quotient.mk P v ∈ nonZeroDivisors (MRing ι ⧸ P) :=
    mem_nonZeroDivisors_of_ne_zero (by rw [Ne, Ideal.Quotient.eq_zero_iff_mem]; exact fun h => hvW (hPW h))
  exact Subring.subset_closure ⟨u, v, a, hvP, hvW, hu, hv, IsLocalization.eq_mk'_iff_mul_eq.mpr hy⟩

theorem frac_unit_locRing {P W : Ideal (MRing ι)} (hPW : P ≤ W) {u v : MRing ι} {a : K → ℕ}
    (hu : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog u a) (hv : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog v a) (huW : u ∉ W) (hvW : v ∉ W) [P.IsPrime]
    {y : FractionRing (MRing ι ⧸ P)}
    (hy : y * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P v) =
      algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u)) :
    y ∈ locRing P W ∧ ∃ z ∈ locRing P W, y * z = 1 := by
  have hu0 : algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u) ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
    exact fun h => huW (hPW h)
  have hv0 : algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P v) ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
    exact fun h => hvW (hPW h)
  set z := algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P v) /
    algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u)
  refine ⟨frac_mem_locRing hPW hu hv hvW hy, z, frac_mem_locRing hPW hv hu huW (div_mul_cancel₀ _ hu0), ?_⟩
  rw [mul_div_assoc', hy, div_self hu0]

theorem RegularityLocalProduct.proof (hN : RegularityFunctionFieldNumber.Statement) (hR : RegularityFormula.Statement)
    (hD : RegularityDenominator.Statement) (hC : RegularityDivisorSupportClosed.Statement) (hF : RegularityLocalFinite.Statement) :
    RegularityLocalProduct.Statement := by
  classical
  intro K _ ι _ P f g a x t yf yg hP hf hg hfP hgP hx ht
  have : P.IsPrime := hP.2.1.1
  obtain ⟨c, hc0, hcW⟩ := hD K ι P x hP
  have hφ : ∀ s, s ∉ P → algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P s) ≠ 0 :=
    fun s hs => by rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]; exact hs
  have hx0 : x ≠ 0 := fun h => hφ f hfP (by rw [← hx, h]; simp)
  have hb0 : x * c ≠ 0 := mul_ne_zero hx0 hc0
  have hxc : ((x * c : funField P) : FractionRing (MRing ι ⧸ P)) = x * c := rfl
  have hmem : ∀ {s : MRing ι} {W}, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a → s ∉ P → IsClosedPt W → P ≤ W → (W ∈ divSupp P s ↔ s ∈ W) :=
    fun hs hsP hWc hPW => (hC K ι P _ a _ hP hs hsP).trans ⟨fun h => h.2.2, fun h => ⟨hWc, hPW, h⟩⟩
  have key : ∀ W, IsClosedPt W → P ≤ W →
      (if W ∈ divSupp P f then Real.log (Nat.card (locRing P W ⧸ locIdeal P W (yf W))) else 0) -
          (if W ∈ divSupp P g then Real.log (Nat.card (locRing P W ⧸ locIdeal P W (yg W))) else 0) =
        Real.log (Nat.card (locRing P W ⧸ locIdeal P W ((x * c : funField P) : FractionRing (MRing ι ⧸ P)))) -
          Real.log (Nat.card (locRing P W ⧸ locIdeal P W (c : FractionRing (MRing ι ⧸ P)))) := by
    intro W hWc hPW
    obtain ⟨hcS, hbS⟩ := hcW W hWc hPW
    by_cases hU : W ∈ divSupp P f ∪ divSupp P g
    · obtain ⟨htW, htn, hyf, hyg⟩ := ht W hU
      have hyfS := frac_mem_locRing hPW hf htW htn hyf
      have hygS := frac_mem_locRing hPW hg htW htn hyg
      have hyf0 : yf W ≠ 0 := fun h => hφ f hfP (by rw [← hyf, h, zero_mul])
      have hyg0 : yg W ≠ 0 := fun h => hφ g hgP (by rw [← hyg, h, zero_mul])
      have hrel : yf W = x * yg W :=
        mul_right_cancel₀ (hφ _ fun h => htn (hPW h)) (by rw [hyf, mul_assoc, hyg, hx])
      obtain ⟨s, hs, hsP, hWs⟩ : ∃ s, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a ∧ s ∉ P ∧ W ∈ divSupp P s := by
        rcases hU with h | h
        exacts [⟨f, hf, hfP, h⟩, ⟨g, hg, hgP, h⟩]
      have fin : ∀ y, y ∈ locRing P W → y ≠ 0 → Finite (locRing P W ⧸ locIdeal P W y) :=
        fun y hy hy0 => hF K ι P s a W y hP hs hsP hWs hy hy0
      have hc0' : (c : FractionRing (MRing ι ⧸ P)) ≠ 0 := fun h => hc0 (Subtype.ext h)
      have hb0' : ((x * c : funField P) : FractionRing (MRing ι ⧸ P)) ≠ 0 := fun h => hb0 (Subtype.ext h)
      have e : yf W * c = ((x * c : funField P) : FractionRing (MRing ι ⧸ P)) * yg W := by
        rw [hrel, hxc]; ring
      have hm := log_card_locIdeal_mul hyfS hcS hyf0 (fin _ hyfS hyf0) (fin _ hcS hc0')
      have hm' := log_card_locIdeal_mul hbS hygS hb0' (fin _ hbS hb0') (fin _ hygS hyg0)
      rw [e] at hm
      by_cases h1 : W ∈ divSupp P f <;> by_cases h2 : W ∈ divSupp P g
      · rw [if_pos h1, if_pos h2]; linarith
      · obtain ⟨-, z, hz, hz1⟩ := frac_unit_locRing hPW hg htW (fun h => h2 ((hmem hg hgP hWc hPW).mpr h)) htn hyg
        have := log_card_locIdeal_unit hygS hz hz1
        rw [if_pos h1, if_neg h2]; linarith
      · obtain ⟨-, z, hz, hz1⟩ := frac_unit_locRing hPW hf htW (fun h => h1 ((hmem hf hfP hWc hPW).mpr h)) htn hyf
        have := log_card_locIdeal_unit hyfS hz hz1
        rw [if_neg h1, if_pos h2]; linarith
      · exact absurd hU (by simp [h1, h2])
    · have h1 : W ∉ divSupp P f := fun h => hU (Or.inl h)
      have h2 : W ∉ divSupp P g := fun h => hU (Or.inr h)
      obtain ⟨hxS, z, hz, hz1⟩ := frac_unit_locRing hPW hf hg (fun h => h1 ((hmem hf hfP hWc hPW).mpr h))
        (fun h => h2 ((hmem hg hgP hWc hPW).mpr h)) hx
      rw [if_neg h1, if_neg h2, hxc, log_card_locIdeal_unit_mul hxS hz hz1 hcS]
      ring
  obtain ⟨hbfin, hbsum⟩ := hR K ι P (x * c) hP hb0 (fun W h1 h2 => (hcW W h1 h2).2)
  obtain ⟨hcfin, hcsum⟩ := hR K ι P c hP hc0 (fun W h1 h2 => (hcW W h1 h2).1)
  have eq1 : ∀ (s : MRing ι) (y : Ideal (MRing ι) → FractionRing (MRing ι ⧸ P)),
      ∑ᶠ W ∈ divSupp P s, Real.log (Nat.card (locRing P W ⧸ locIdeal P W (y W))) =
        ∑ᶠ W, (if W ∈ divSupp P s then Real.log (Nat.card (locRing P W ⧸ locIdeal P W (y W))) else 0) := by
    intro s y
    rw [finsum_mem_def]
    rfl
  have fsA : ∀ (s : MRing ι) (y : Ideal (MRing ι) → FractionRing (MRing ι ⧸ P)),
      (Function.support fun W =>
        if W ∈ divSupp P s then Real.log (Nat.card (locRing P W ⧸ locIdeal P W (y W))) else 0).Finite :=
    fun s y => (divSupp_finite P s).subset fun W hW => by
      by_contra h
      exact hW (if_neg h)
  have fsB : ∀ z : FractionRing (MRing ι ⧸ P),
      {W | IsClosedPt W ∧ P ≤ W ∧ Nat.card (locRing P W ⧸ locIdeal P W z) ≠ 1}.Finite →
      (Function.support ({W : Ideal (MRing ι) | IsClosedPt W ∧ P ≤ W}.indicator
        fun W => Real.log (Nat.card (locRing P W ⧸ locIdeal P W z)))).Finite :=
    fun z hz => hz.subset fun W hW => by
      rw [Function.mem_support] at hW
      by_cases hWC : W ∈ {W : Ideal (MRing ι) | IsClosedPt W ∧ P ≤ W}
      · rw [Set.indicator_of_mem hWC] at hW
        exact ⟨hWC.1, hWC.2, fun h1 => hW (by rw [h1]; simp)⟩
      · rw [Set.indicator_of_notMem hWC] at hW
        exact absurd rfl hW
  obtain ⟨hFld, hNF⟩ := hN K ι P hP
  let _ := hFld.toField
  have hσ : ∀ y : funField P, y ≠ 0 → ∀ σ : funField P →+* ℂ, σ y ≠ 0 := fun y hy σ h => by
    obtain ⟨z, hz⟩ := hFld.mul_inv_cancel hy
    have := congrArg σ hz
    rw [map_mul, h, zero_mul, map_one] at this
    exact zero_ne_one this
  calc _ = ∑ᶠ W, ((if W ∈ divSupp P f then Real.log (Nat.card (locRing P W ⧸ locIdeal P W (yf W))) else 0) -
          (if W ∈ divSupp P g then Real.log (Nat.card (locRing P W ⧸ locIdeal P W (yg W))) else 0)) := by
        rw [eq1 f yf, eq1 g yg, finsum_sub_distrib (fsA f yf) (fsA g yg)]
    _ = ∑ᶠ W, ({W : Ideal (MRing ι) | IsClosedPt W ∧ P ≤ W}.indicator
            (fun W => Real.log (Nat.card (locRing P W ⧸
              locIdeal P W ((x * c : funField P) : FractionRing (MRing ι ⧸ P))))) W -
          {W : Ideal (MRing ι) | IsClosedPt W ∧ P ≤ W}.indicator
            (fun W => Real.log (Nat.card (locRing P W ⧸ locIdeal P W (c : FractionRing (MRing ι ⧸ P))))) W) := by
        refine finsum_congr fun W => ?_
        by_cases hWC : W ∈ {W : Ideal (MRing ι) | IsClosedPt W ∧ P ≤ W}
        · rw [Set.indicator_of_mem hWC, Set.indicator_of_mem hWC]
          exact key W hWC.1 hWC.2
        · rw [Set.indicator_of_notMem hWC, Set.indicator_of_notMem hWC,
            if_neg fun h => hWC ⟨((hC K ι P f a W hP hf hfP).mp h).1, ((hC K ι P f a W hP hf hfP).mp h).2.1⟩,
            if_neg fun h => hWC ⟨((hC K ι P g a W hP hg hgP).mp h).1, ((hC K ι P g a W hP hg hgP).mp h).2.1⟩]
    _ = ∑ᶠ σ : funField P →+* ℂ, Real.log ‖σ (x * c)‖ - ∑ᶠ σ : funField P →+* ℂ, Real.log ‖σ c‖ := by
        rw [finsum_sub_distrib (fsB _ hbfin) (fsB _ hcfin), ← finsum_mem_def, ← finsum_mem_def, hbsum, hcsum]
    _ = _ := by
        rw [← finsum_sub_distrib (Set.toFinite _) (Set.toFinite _)]
        refine finsum_congr fun σ => ?_
        rw [map_mul, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr (hσ x hx0 σ)) (norm_ne_zero_iff.mpr (hσ c hc0 σ))]
        ring

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsTerLast
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def RegularityIntegral.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)),
    IsArithVar P 1 → ∀ x : regRing P, IsIntegral ℤ ((x : funField P) : FractionRing (MRing ι ⧸ P))

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsMoreAlt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def RegularityLocalPrime.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (p : ℤ) (y : funField P),
    IsArithVar P 1 → Prime p →
    (∀ W, IsClosedPt W → P ≤ W → C p ∈ W → (y : FractionRing (MRing ι ⧸ P)) ∈ locRing P W) →
    ∃ n : ℤ, ¬ p ∣ n ∧ (n : funField P) * y ∈ regRing P

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsPFVert
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

def PFVert.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (d r : ℕ)
    (L : Fin d → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (L' : Fin d → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι') (N : Fin r → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι')
    (s : MRing ι') (a : K' → ℕ) (W : Ideal (MRing ι')),
    IsBlockMap κ v → IsArithVar P' (d + r + 1) → IsArithVar (imageZ v P') d →
    (∀ j, IsPullHerm κ v (L j) (L' j)) → ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a → s ∉ P' →
    W ∈ divSupp P' s → ¬ IsHorizontal W →
    geoNum (d + r) W (fun j => (Fin.append L' N j).a) = 0

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights.Inter
end
