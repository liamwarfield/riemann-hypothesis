module

public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.BcRigidAtOfIntModel
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RecordAtOfIsArcFr

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsLiftOpen
noncomputable section

namespace GlobalTheory.ArcQ

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

section Units

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem arcιR_isUnit_mul (Dw : Datum H) (V : Type) [CommRing V] (ϖ : V) :
    IsUnit (arcιR Dw V ϖ (PowerSeries.C ϖ * PowerSeries.X)) := by
  have h := IsLocalization.Away.algebraMap_isUnit (S := ArcSR Dw V ϖ)
    (MvPolynomial.C (PowerSeries.C ϖ * PowerSeries.X) * arcDetR Dw V)
  rw [map_mul (algebraMap (MvPolynomial (ArcLt Dw) (PowerSeries V)) (ArcSR Dw V ϖ))] at h
  exact isUnit_of_mul_isUnit_left h

theorem letMR_det_isUnit (Dw : Datum H) (V : Type) [CommRing V] (ϖ : V) (τ : E →+* ℂ) :
    IsUnit (letMR Dw V ϖ τ).det := by
  classical
  have h := IsLocalization.Away.algebraMap_isUnit (S := ArcSR Dw V ϖ)
    (MvPolynomial.C (PowerSeries.C ϖ * PowerSeries.X) * arcDetR Dw V)
  rw [map_mul (algebraMap (MvPolynomial (ArcLt Dw) (PowerSeries V)) (ArcSR Dw V ϖ))] at h
  have h2 := isUnit_of_mul_isUnit_right h
  have h3 := isUnit_of_dvd_unit (map_dvd (algebraMap (MvPolynomial (ArcLt Dw) (PowerSeries V)) (ArcSR Dw V ϖ))
    (Finset.dvd_prod_of_mem (fun τ : E →+* ℂ => Matrix.det (Matrix.of fun i k : Fin (Dw.mult τ) =>
      (MvPolynomial.X (⟨τ, i, k⟩ : ArcLt Dw) : MvPolynomial (ArcLt Dw) (PowerSeries V)))) (Finset.mem_univ τ))) h2
  rw [RingHom.map_det] at h3
  exact h3

theorem arcιR_C_isUnit (Dw : Datum H) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
    (hϖ : Irreducible ϖ) {v : V} (hv : v ≠ 0) : IsUnit (arcιR Dw V ϖ (PowerSeries.C v)) := by
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hv hϖ
  have h := arcιR_isUnit_mul Dw V ϖ
  rw [map_mul (arcιR Dw V ϖ)] at h
  rw [map_mul (PowerSeries.C (R := V)), map_pow (PowerSeries.C (R := V)), map_mul (arcιR Dw V ϖ),
    map_pow (arcιR Dw V ϖ)]
  exact ((u.isUnit.map _).map _).mul ((isUnit_of_mul_isUnit_left h).pow n)

end Units

theorem exists_lift_open {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β)
    {S : Type} [CommRing S] (g : c.F →+* S) (χ : Sp S ⟶ Y.X) (hcond : χ ≫ Y.s = spMap g ≫ spMap β)
    (hj : ∀ q : Sp S, χ q ∈ Set.range Y.j) :
    ∃ z : Sp S ⟶ Xo.XF c, z ≫ Y.j = χ ∧ z ≫ pullback.snd _ _ = spMap g := by
  let p : Sp S ⟶ pullback Y.s (spMap β) := pullback.lift χ (spMap g) hcond
  have hr : Set.range p ⊆ Set.range Y.jQ := by
    rintro _ ⟨q, rfl⟩
    rw [← Y.ab_gen, Set.mem_preimage, ← Scheme.Hom.comp_apply, pullback.lift_fst]
    obtain ⟨w, hw⟩ := hj q
    rw [← hw]
    have h2 : Y.jQ w ∈ (pullback.fst Y.s (spMap β)) ⁻¹' abLocus Y.t.G := by
      rw [Y.ab_gen]; exact ⟨w, rfl⟩
    simpa only [Model.j, Scheme.Hom.comp_apply, Set.mem_preimage] using h2
  have := Y.jQ_open
  refine ⟨IsOpenImmersion.lift Y.jQ p hr, ?_, ?_⟩
  · show IsOpenImmersion.lift Y.jQ p hr ≫ Y.jQ ≫ pullback.fst _ _ = _
    rw [← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_fst]
  · rw [← Y.jQ_over, ← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_snd]

theorem exists_dvr_frPt : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Tv : CDVR) (ϖ : Tv.V) (f : c.F →+* Tv.Fr) (b : O →+* Tv.V) (a : ArcIn Dw l β Tv.V b) (χ : Sp (PowerSeries Tv.V) ⟶ Y.X) (W : Wit Y a χ) (ρ : (E →+* ℂ) → (𝓞 E →+* Tv.V)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR Tv.V)) (th : a.D₀.P.L.Sec), Irreducible ϖ → f.comp β = (algebraMap Tv.V Tv.Fr).comp b → (∀ τ x, algebraMap Tv.V Tv.Fr (ρ τ x) = f (embK c τ x)) → χ ≫ Y.s = spMap (PowerSeries.C (R := Tv.V)) ≫ spMap b → (∀ x : Sp (PowerSeries Tv.V), PowerSeries.C ϖ * PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → Mono (spMap β) → PushInvertible Y.t.G Y.t.PP.L → ArcBasis W ρ e → ThNZ th → ∃ (_ : Algebra c.F (ArcSR Dw Tv.V ϖ)), (∀ (x : c.F) (v : Tv.V) (n : ℕ), f x * algebraMap Tv.V Tv.Fr ϖ ^ n = algebraMap Tv.V Tv.Fr v → algebraMap c.F (ArcSR Dw Tv.V ϖ) x * arcιR Dw Tv.V ϖ (PowerSeries.C (R := Tv.V) ϖ) ^ n = arcιR Dw Tv.V ϖ (PowerSeries.C (R := Tv.V) v)) ∧ ∃ y₀ yR : FrPt Xo c (ArcSR Dw Tv.V ϖ), IsArcFr W e th (arcιR Dw Tv.V ϖ) y₀ ∧ FrChg (letMR Dw Tv.V ϖ) 1 y₀ yR := by
  intro L1 L2 E _ _ _ H Dw l Xo c O _ β Y Tv ϖ f b a χ W ρ e th hϖ hfb hρ hχ hj _ hpush hbasis hth
  let ι := arcιR Dw Tv.V ϖ
  let κ : Tv.V →+* ArcSR Dw Tv.V ϖ := ι.comp (PowerSeries.C (R := Tv.V))
  have hκ : ∀ y : nonZeroDivisors Tv.V, IsUnit (κ y) := fun y =>
    arcιR_C_isUnit Dw Tv.V hϖ (nonZeroDivisors.ne_zero y.2)
  let g : Tv.Fr →+* ArcSR Dw Tv.V ϖ := IsLocalization.lift hκ
  have hg : ∀ v, g (algebraMap Tv.V Tv.Fr v) = κ v := fun v => IsLocalization.lift_eq hκ v
  letI alg : Algebra c.F (ArcSR Dw Tv.V ϖ) := (g.comp f).toAlgebra
  have halg : ∀ x, algebraMap c.F (ArcSR Dw Tv.V ϖ) x = g (f x) := fun _ => rfl
  refine ⟨alg, ?_, ?_⟩
  · intro x v n h
    have h2 := congrArg g h
    rw [map_mul, map_pow, hg, hg] at h2
    exact h2
  · have hcomp : (algebraMap c.F (ArcSR Dw Tv.V ϖ)).comp β = ι.comp ((PowerSeries.C (R := Tv.V)).comp b) := by
      ext1 x
      have h1 : f (β x) = algebraMap Tv.V Tv.Fr (b x) := RingHom.congr_fun hfb x
      show g (f (β x)) = κ (b x)
      rw [h1, hg]
    have hcond : (spMap ι ≫ χ) ≫ Y.s = spMap (algebraMap c.F (ArcSR Dw Tv.V ϖ)) ≫ spMap β := by
      rw [Category.assoc, hχ, ← spMap_comp, ← spMap_comp, ← spMap_comp, hcomp]
    obtain ⟨z, hz1, hz2⟩ := exists_lift_open Y (algebraMap c.F (ArcSR Dw Tv.V ϖ)) (spMap ι ≫ χ) hcond (by
      intro q
      rw [Scheme.Hom.comp_apply]
      refine hj _ fun h => ?_
      have h' : ι (PowerSeries.C ϖ * PowerSeries.X) ∈ q.asIdeal := h
      exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h' (arcιR_isUnit_mul Dw Tv.V ϖ)))
    have hflat := (GlobalTheory.LetterDenom.main E H Dw Tv ϖ hϖ.ne_zero).2.2.1
    obtain ⟨y₀, -, hy₀⟩ := exists_isArcFr L1 L2 E H Dw l Xo c O β Y Tv.V b a χ W ρ e th hbasis hth (Or.inr hpush)
      (ArcSR Dw Tv.V ϖ) ι z hflat hz1
      (by rw [pullback.condition, ← Category.assoc, hz2, ← spMap_comp]; rfl)
      (fun τ x => by rw [halg, ← hρ, hg]; rfl)
    obtain ⟨yR, hyR⟩ := (frChg_exists_unique_units E H Dw l Xo c (ArcSR Dw Tv.V ϖ) (letMR Dw Tv.V ϖ) 1 y₀).1
      (letMR_det_isUnit Dw Tv.V ϖ) isUnit_one
    exact ⟨y₀, yR, hy₀, hyR⟩

end GlobalTheory.ArcQ
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LcoeffPolyConstMul
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsEvalArcLetterRingOverDVRDisc
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsEvalArcLetterRingOverDVRDisc
namespace GlobalTheory.LetterEval

open GlobalTheory.DiscEval

section General

variable {K : Type} [NormedField K] [CompleteSpace K] {V F : Type} [CommRing V] [Field F]
  (a : V →+* F) (ι : F →+* K) (hi : ∀ v, ‖(ι.comp a) v‖ ≤ 1) {ϖ : V} (hϖ : a ϖ ≠ 0)
  {t : K} (ht0 : t ≠ 0) (ht : ‖t‖ < 1)


include hϖ ht0 in
theorem hasSum_laurent_of_mul_eq {q : LaurentSeries F} {g : PowerSeries V} {N : ℕ}
    (h : q * (HahnSeries.ofPowerSeries ℤ F (PowerSeries.C (R := F) (a ϖ) * PowerSeries.X)) ^ N =
      HahnSeries.ofPowerSeries ℤ F (PowerSeries.map a g)) :
    HasSum (fun k : ℤ => ι (q.coeff k) * t ^ k)
      (((ι (a ϖ) * t) ^ N)⁻¹ * discEval (ι.comp a) hi ht g) := by
  have h2 : (HahnSeries.ofPowerSeries ℤ F (PowerSeries.C (R := F) (a ϖ) * PowerSeries.X)) ^ N =
      HahnSeries.single (N : ℤ) (a ϖ ^ N) := by
    rw [← map_pow, mul_pow, ← map_pow PowerSeries.C, map_mul, HahnSeries.ofPowerSeries_C,
      HahnSeries.ofPowerSeries_X_pow, HahnSeries.C_apply, HahnSeries.single_mul_single]
    simp
  have h4 : a ϖ ^ N ≠ 0 := pow_ne_zero _ hϖ
  have hc : ∀ n : ℤ, q.coeff n = if n + N < 0 then 0 else
      (a ϖ ^ N)⁻¹ * a (PowerSeries.coeff (n + N).natAbs g) := fun n => by
    have h3 := congrArg (fun g : LaurentSeries F => g.coeff (n + N)) h
    simp only [h2, HahnSeries.coeff_mul_single_add] at h3
    rw [PowerSeries.coeff_coe, PowerSeries.coeff_map] at h3
    split_ifs at h3 ⊢
    · exact (mul_eq_zero.1 h3).resolve_right h4
    · rw [← h3]
      field_simp
  have hinj : Function.Injective fun k : ℕ => (k : ℤ) - N := fun k l hkl => by simpa using hkl
  rw [← hinj.hasSum_iff]
  · refine Eq.mpr (congrArg (HasSum · _) (funext fun k => ?_))
      ((hasSum_discEval (ι.comp a) hi ht g).mul_left (((ι (a ϖ) * t) ^ N)⁻¹))
    rw [Function.comp_apply, hc, sub_add_cancel, if_neg (by omega), Int.natAbs_natCast,
      zpow_sub₀ ht0, zpow_natCast, zpow_natCast, map_mul, map_inv₀, map_pow, RingHom.comp_apply,
      mul_pow, mul_inv]
    ring
  · intro n hn
    rw [hc, if_pos, map_zero, zero_mul]
    by_contra h0
    exact hn ⟨(n + N).toNat, by simp only; omega⟩


include hϖ ht0 in
theorem hasSum_lcoeffPoly {σ : Type} (Y : σ → K) {P : MvPolynomial σ (LaurentSeries F)}
    {G : MvPolynomial σ (PowerSeries V)} {N : ℕ}
    (h : P * MvPolynomial.C
        (HahnSeries.ofPowerSeries ℤ F (PowerSeries.C (R := F) (a ϖ) * PowerSeries.X)) ^ N =
      MvPolynomial.map ((HahnSeries.ofPowerSeries ℤ F).comp (PowerSeries.map a)) G) :
    HasSum (fun k : ℤ => MvPolynomial.eval Y (MvPolynomial.map ι (GlobalTheory.ArcQ.lcoeffPoly P k)) * t ^ k)
      (((ι (a ϖ) * t) ^ N)⁻¹ * MvPolynomial.eval₂ (discEval (ι.comp a) hi ht) Y G) := by
  classical
  have hμ : ∀ μ, P.coeff μ *
      (HahnSeries.ofPowerSeries ℤ F (PowerSeries.C (R := F) (a ϖ) * PowerSeries.X)) ^ N =
      HahnSeries.ofPowerSeries ℤ F (PowerSeries.map a (G.coeff μ)) := fun μ => by
    have := congrArg (AddMonoidAlgebra.coeff · μ) h
    rwa [← map_pow, mul_comm, MvPolynomial.coeff_C_mul, mul_comm, MvPolynomial.coeff_map] at this
  set s := P.support ∪ G.support
  have hP : ∀ k : ℤ, GlobalTheory.ArcQ.lcoeffPoly P k =
      ∑ μ ∈ s, MvPolynomial.monomial μ ((P.coeff μ).coeff k) := fun k =>
    Finset.sum_subset Finset.subset_union_left fun μ _ hμ => by
      simp [MvPolynomial.notMem_support_iff.1 hμ]
  have hG : MvPolynomial.eval₂ (discEval (ι.comp a) hi ht) Y G =
      ∑ μ ∈ s, discEval (ι.comp a) hi ht (G.coeff μ) * ∏ k ∈ μ.support, Y k ^ μ k := by
    rw [MvPolynomial.eval₂_eq]
    exact Finset.sum_subset Finset.subset_union_right fun μ _ hμ => by
      simp [MvPolynomial.notMem_support_iff.1 hμ]
  rw [hG, Finset.mul_sum]
  simp_rw [← mul_assoc]
  refine Eq.mpr (congrArg (HasSum · _) (funext fun m => ?_))
    (hasSum_sum fun μ (_ : μ ∈ s) =>
      (hasSum_laurent_of_mul_eq a ι hi hϖ ht0 ht (hμ μ)).mul_right (∏ k ∈ μ.support, Y k ^ μ k))
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hP, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [MvPolynomial.map_monomial, MvPolynomial.eval_monomial, Finsupp.prod]
  ring

end General

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

theorem exists_eval : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (Tv : CDVR) (ϖ : Tv.V) (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (ιT : Tv.Fr →+* K), ϖ ≠ 0 → (∀ v : Tv.V, ‖ιT (algebraMap Tv.V Tv.Fr v)‖ ≤ 1) → ∀ (t : K) (Y : ArcLt Dw → K), 0 < ‖t‖ → ‖t‖ < 1 → (∏ τ : E →+* ℂ, (Matrix.of fun i k : Fin (Dw.mult τ) => Y ⟨τ, i, k⟩).det) ≠ 0 → ∃ ev : ArcSR Dw Tv.V ϖ →+* K, (∀ p : PowerSeries Tv.V, ev (arcιR Dw Tv.V ϖ p) = ∑' k : ℕ, ιT (algebraMap Tv.V Tv.Fr (PowerSeries.coeff k p)) * t ^ k) ∧ (∀ x, ev (arcXR Dw Tv.V ϖ x) = Y x) ∧ ∀ (f : ArcSR Dw Tv.V ϖ) (N : ℕ) (G : MvPolynomial (ArcLt Dw) (PowerSeries Tv.V)) (P : MvPolynomial (ArcLt Dw) (LaurentSeries Tv.Fr)), f * arcιR Dw Tv.V ϖ (PowerSeries.C (R := Tv.V) ϖ * PowerSeries.X) ^ N = algebraMap _ (ArcSR Dw Tv.V ϖ) G → P * MvPolynomial.C (HahnSeries.ofPowerSeries ℤ Tv.Fr (PowerSeries.C (R := Tv.Fr) (algebraMap Tv.V Tv.Fr ϖ) * PowerSeries.X)) ^ N = MvPolynomial.map ((HahnSeries.ofPowerSeries ℤ Tv.Fr).comp (PowerSeries.map (algebraMap Tv.V Tv.Fr))) G → Filter.Tendsto (fun k : ℤ => ‖MvPolynomial.eval Y (MvPolynomial.map ιT (lcoeffPoly P k)) * t ^ k‖) Filter.cofinite (nhds 0) ∧ ev f = ∑' k : ℤ, MvPolynomial.eval Y (MvPolynomial.map ιT (lcoeffPoly P k)) * t ^ k := by
  intro E _ _ _ H Dw Tv ϖ K _ _ _ ιT hϖ hi t Y ht0 ht hY
  have ht0' : t ≠ 0 := norm_pos_iff.1 ht0
  have hϖ' : algebraMap Tv.V Tv.Fr ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective Tv.V Tv.Fr)).2 hϖ
  have hϖ'' : ιT (algebraMap Tv.V Tv.Fr ϖ) ≠ 0 := (map_ne_zero ιT).2 hϖ'
  have hi' : ∀ v, ‖(ιT.comp (algebraMap Tv.V Tv.Fr)) v‖ ≤ 1 := hi
  let g : MvPolynomial (ArcLt Dw) (PowerSeries Tv.V) →+* K :=
    MvPolynomial.eval₂Hom (discEval _ hi' ht) Y
  have hgC : ∀ p, g (MvPolynomial.C p) = discEval _ hi' ht p := fun p =>
    MvPolynomial.eval₂Hom_C _ _ _
  have hgX : ∀ x, g (MvPolynomial.X x) = Y x := fun x => MvPolynomial.eval₂Hom_X' _ _ _
  have hϖX : discEval _ hi' ht (PowerSeries.C (R := Tv.V) ϖ * PowerSeries.X) =
      ιT (algebraMap Tv.V Tv.Fr ϖ) * t := by
    rw [map_mul, discEval_C, discEval_X, RingHom.comp_apply]
  have hu : IsUnit (g (MvPolynomial.C (PowerSeries.C ϖ * PowerSeries.X) * arcDetR Dw Tv.V)) := by
    rw [isUnit_iff_ne_zero, map_mul, hgC, hϖX]
    refine mul_ne_zero (mul_ne_zero hϖ'' ht0') ?_
    convert hY using 1
    rw [arcDetR, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [RingHom.map_det]
    congr 1
    ext i k
    exact hgX _
  let ev : ArcSR Dw Tv.V ϖ →+* K := IsLocalization.Away.lift _ hu
  have hev : ∀ G, ev (algebraMap _ (ArcSR Dw Tv.V ϖ) G) = g G := fun G =>
    IsLocalization.Away.lift_eq _ hu G
  have hevι : ∀ p, ev (arcιR Dw Tv.V ϖ p) = discEval _ hi' ht p := fun p =>
    (hev _).trans (hgC p)
  refine ⟨ev, fun p => ?_, fun x => (hev _).trans (hgX x), fun f N G P hf hP => ?_⟩
  · rw [hevι, ← (hasSum_discEval _ hi' ht p).tsum_eq]
    rfl
  · have hs := hasSum_lcoeffPoly _ ιT hi' hϖ' ht0' ht Y hP
    refine ⟨by simpa using hs.summable.tendsto_cofinite_zero.norm, ?_⟩
    rw [hs.tsum_eq]
    have h1 := congrArg ev hf
    rw [map_mul, map_pow, hevι, hϖX, hev] at h1
    have h2 : (ιT (algebraMap Tv.V Tv.Fr ϖ) * t) ^ N ≠ 0 := pow_ne_zero _ (mul_ne_zero hϖ'' ht0')
    rw [eq_inv_mul_iff_mul_eq₀ h2, mul_comm]
    exact h1

end GlobalTheory.LetterEval
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsEvalArcLetterRingOverDVRDiscStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eval_arcLetterRingOverDVR_disc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (Tv : CDVR) (ϖ : Tv.V) (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (ιT : Tv.Fr →+* K), ϖ ≠ 0 → (∀ v : Tv.V, ‖ιT (algebraMap Tv.V Tv.Fr v)‖ ≤ 1) → ∀ (t : K) (Y : ArcLt Dw → K), 0 < ‖t‖ → ‖t‖ < 1 → (∏ τ : E →+* ℂ, (Matrix.of fun i k : Fin (Dw.mult τ) => Y ⟨τ, i, k⟩).det) ≠ 0 → ∃ ev : ArcSR Dw Tv.V ϖ →+* K, (∀ p : PowerSeries Tv.V, ev (arcιR Dw Tv.V ϖ p) = ∑' k : ℕ, ιT (algebraMap Tv.V Tv.Fr (PowerSeries.coeff k p)) * t ^ k) ∧ (∀ x, ev (arcXR Dw Tv.V ϖ x) = Y x) ∧ ∀ (f : ArcSR Dw Tv.V ϖ) (N : ℕ) (G : MvPolynomial (ArcLt Dw) (PowerSeries Tv.V)) (P : MvPolynomial (ArcLt Dw) (LaurentSeries Tv.Fr)), f * arcιR Dw Tv.V ϖ (PowerSeries.C (R := Tv.V) ϖ * PowerSeries.X) ^ N = algebraMap _ (ArcSR Dw Tv.V ϖ) G → P * MvPolynomial.C (HahnSeries.ofPowerSeries ℤ Tv.Fr (PowerSeries.C (R := Tv.Fr) (algebraMap Tv.V Tv.Fr ϖ) * PowerSeries.X)) ^ N = MvPolynomial.map ((HahnSeries.ofPowerSeries ℤ Tv.Fr).comp (PowerSeries.map (algebraMap Tv.V Tv.Fr))) G → Filter.Tendsto (fun k : ℤ => ‖MvPolynomial.eval Y (MvPolynomial.map ιT (lcoeffPoly P k)) * t ^ k‖) Filter.cofinite (nhds 0) ∧ ev f = ∑' k : ℤ, MvPolynomial.eval Y (MvPolynomial.map ιT (lcoeffPoly P k)) * t ^ k := by
  first | exact @GlobalTheory.LetterEval.exists_eval | exact GlobalTheory.LetterEval.exists_eval | (intros; apply GlobalTheory.LetterEval.exists_eval <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

noncomputable section

namespace GlobalTheory.ArcQ.FrameCut

theorem lcoeffPoly_coeff {ι K₁ : Type} [Field K₁] (P : MvPolynomial ι (LaurentSeries K₁)) (m : ℤ)
    (μ : ι →₀ ℕ) : (GlobalTheory.ArcQ.lcoeffPoly P m).coeff μ = (P.coeff μ).coeff m := by
  classical
  simp only [GlobalTheory.ArcQ.lcoeffPoly, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp h]; rfl

theorem lcoeffPoly_add {ι K₁ : Type} [Field K₁] (P Q : MvPolynomial ι (LaurentSeries K₁)) (m : ℤ) :
    GlobalTheory.ArcQ.lcoeffPoly (P + Q) m = GlobalTheory.ArcQ.lcoeffPoly P m + GlobalTheory.ArcQ.lcoeffPoly Q m := by
  ext μ
  simp only [lcoeffPoly_coeff, MvPolynomial.coeff_add, HahnSeries.coeff_add]

theorem lcoeffPoly_monomial {ι K₁ : Type} [Field K₁] (μ : ι →₀ ℕ) (f : LaurentSeries K₁) (m : ℤ) :
    GlobalTheory.ArcQ.lcoeffPoly (MvPolynomial.monomial μ f) m = MvPolynomial.monomial μ (f.coeff m) := by
  classical
  ext ν
  simp only [lcoeffPoly_coeff, MvPolynomial.coeff_monomial]
  split_ifs
  · rfl
  · rfl

theorem lcoeffPoly_C_mul_map {ι L : Type} [Field L] (g : LaurentSeries L) (Q : MvPolynomial ι L) (m : ℤ) :
    GlobalTheory.ArcQ.lcoeffPoly (MvPolynomial.C g * MvPolynomial.map (HahnSeries.C (Γ := ℤ)) Q) m =
      MvPolynomial.C (g.coeff m) * Q := by
  ext ν
  rw [lcoeffPoly_coeff, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map, mul_comm g,
    HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul, mul_comm]

theorem lcoeffPoly_const_mul {ι L : Type} [Field L] (x : L) (P : MvPolynomial ι (LaurentSeries L)) (m : ℤ) :
    GlobalTheory.ArcQ.lcoeffPoly (MvPolynomial.C (HahnSeries.C (Γ := ℤ) x) * P) m =
      MvPolynomial.C x * GlobalTheory.ArcQ.lcoeffPoly P m := by
  ext ν
  rw [lcoeffPoly_coeff, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_C_mul, lcoeffPoly_coeff,
    HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]

theorem exists_subst {ι K₁ L S : Type} [Field K₁] [Field L] [CommRing S] (io : K₁ →+* L)
    (Φ : MvPolynomial ι (LaurentSeries K₁) →+* S) (j : MvPolynomial ι (LaurentSeries L) →+* S)
    (q : ι → MvPolynomial ι L)
    (hC : ∀ f : LaurentSeries K₁, ∃ g : LaurentSeries L, (∀ m, g.coeff m = io (f.coeff m)) ∧
      Φ (MvPolynomial.C f) = j (MvPolynomial.C g))
    (hX : ∀ x, Φ (MvPolynomial.X x) = j (MvPolynomial.map (HahnSeries.C (Γ := ℤ)) (q x)))
    (P : MvPolynomial ι (LaurentSeries K₁)) :
    ∃ P₁ : MvPolynomial ι (LaurentSeries L), j P₁ = Φ P ∧ ∀ m, GlobalTheory.ArcQ.lcoeffPoly P₁ m =
      MvPolynomial.eval₂Hom (MvPolynomial.C.comp io) q (GlobalTheory.ArcQ.lcoeffPoly P m) := by
  induction P using MvPolynomial.induction_on' with
  | monomial μ f =>
    obtain ⟨g, hg, hΦ⟩ := hC f
    refine ⟨MvPolynomial.C g * MvPolynomial.map (HahnSeries.C (Γ := ℤ)) (μ.prod fun x e => q x ^ e), ?_, fun m => ?_⟩
    · rw [MvPolynomial.monomial_eq, map_mul, map_mul, hΦ]
      simp only [Finsupp.prod, map_prod, map_pow, hX]
    · rw [lcoeffPoly_C_mul_map, lcoeffPoly_monomial, MvPolynomial.eval₂Hom_monomial, hg]
      rfl
  | add P Q hP hQ =>
    obtain ⟨P₁, h1, h2⟩ := hP
    obtain ⟨Q₁, h3, h4⟩ := hQ
    exact ⟨P₁ + Q₁, by rw [map_add (f := _), map_add (f := _), h1, h3], fun m => by
      rw [lcoeffPoly_add, lcoeffPoly_add, map_add (f := _), h2, h4]⟩

theorem eval_subst {ι K₁ L K : Type} [Field K₁] [Field L] [Field K] (io : K₁ →+* L) (ιT : L →+* K)
    (q : ι → MvPolynomial ι L) (Y : ι → K) (R : MvPolynomial ι K₁) :
    MvPolynomial.eval Y (MvPolynomial.map ιT (MvPolynomial.eval₂Hom (MvPolynomial.C.comp io) q R)) =
      MvPolynomial.eval (fun x => MvPolynomial.eval Y (MvPolynomial.map ιT (q x)))
        (MvPolynomial.map (ιT.comp io) R) := by
  induction R using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p x hp => simp only [map_mul, hp, MvPolynomial.eval₂Hom_X', MvPolynomial.map_X, MvPolynomial.eval_X]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}

theorem arcNum_of_poly {K₁ : Type} [Field K₁] (P : MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) :
    arcNum (algebraMap _ (ArcS Dw K₁) P) = P := by
  have hs : ∃ Q, algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) (ArcS Dw K₁) Q =
      algebraMap _ (ArcS Dw K₁) P := ⟨P, rfl⟩
  rw [arcNum, dite_eq_left hs]
  exact GlobalTheory.ArcConst.algebraMap_injective Dw K₁ hs.choose_spec

theorem wchar_gen {S : Type} [CommRing S] (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (t : Ix Dw → Sˣ)
    (h : ∀ x, t (some x) = 1) : wchar (ex Dw a n) t = (t none : S) ^ n := by
  rw [wchar, Fintype.prod_option]
  simp [h, ex]


set_option maxHeartbeats 1600000 in
theorem frameBound_of_cut (hL : Out.Laws) (hL2 : Out.Laws2) {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
    (hev : GlobalTheory.Reg.EvLaws Xo c) {K₁ : Type} [Field K₁] [NumberField K₁] [Algebra c.F K₁] {d : ArcDatum Xo c K₁}
    {w : HeightOneSpectrum (𝓞 K₁)} {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {Fs : Set (Rul Xo c)}
    (hFs : ∀ F ∈ Fs, F ∈ sec Xo c a n) (Z : FinSite K₁ w) (Dv : DvrFrame d w Z) (γ : Dv.Tv.Fr)
    (lam : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Dv.Tv.Fr)
    (Bm : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Dv.Tv.Fr) (hγ : γ ≠ 0)
    (hBc : BcRigidAt Dv γ lam Bm) (hRec : RecordAt Dv Fs) :
    FrameBound Z (Dv.ιT γ) (fun τ k => Dv.ιT (lam τ k)) (fun τ => (Bm τ).map Dv.ιT) n d Fs := by
  intro F hF t ht Y hY hdet
  obtain ⟨φ, ψ, z₁, z₂, tγ, hφC, hφX, hψC, hψX, htγ, htγ', hm1, hm2, hb⟩ := hBc
  have hϖ : Dv.ϖ ≠ 0 := Dv.ϖ_irr.ne_zero
  obtain ⟨hdomR, -, -, -, hdiv⟩ := GlobalTheory.T.arcLetterRingOverDVR_polynomial_denominators E H Dw Dv.Tv Dv.ϖ hϖ
  have hdom1 := GlobalTheory.ArcConst.isDomain Dw K₁
  have hdom2 := GlobalTheory.ArcConst.isDomain Dw Dv.Tv.Fr
  have hinj := GlobalTheory.ArcConst.algebraMap_injective Dw Dv.Tv.Fr
  have hsec := hFs F hF
  obtain ⟨P, hP, -⟩ := GlobalTheory.T.arcFramedPoint_value_isHomogeneous_letters hL hL2 E H Dw l Xo c hev K₁ d a n F hsec
  have e1 := (GlobalTheory.T.framedPoint_eval_natural_weight_scaling E H Dw l Xo c hev a n F hsec (ArcS Dw K₁)).1 _ φ _ _ hm1
  have e2 := (GlobalTheory.T.framedPoint_eval_natural_weight_scaling E H Dw l Xo c hev a n F hsec (ArcSR Dw Dv.Tv.V Dv.ϖ)).1 _ ψ _ _ hm2
  have e3 := ((GlobalTheory.T.framedPoint_eval_natural_weight_scaling E H Dw l Xo c hev a n F hsec (ArcS Dw Dv.Tv.Fr)).2 hdom2).1 tγ _ _ hb
  rw [wchar_gen a n tγ htγ', e1, e2, htγ, ← hP] at e3
  set f := evR Xo c F Dv.yR with hf
  let q : ArcLt Dw → MvPolynomial (ArcLt Dw) Dv.Tv.Fr := fun x =>
    ∑ l : Fin (Dw.mult x.1), MvPolynomial.X ⟨x.1, x.2.1, l⟩ * MvPolynomial.C (Bm x.1 l x.2.2 * (lam x.1 x.2.2)⁻¹)
  obtain ⟨P₁, hP₁, hco⟩ := exists_subst Dv.io (φ.toRingHom.comp (algebraMap _ (ArcS Dw K₁)))
    (algebraMap _ (ArcS Dw Dv.Tv.Fr)) q hφC (fun x => by
      refine (hφX x).trans ?_
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [q, map_sum, map_mul, MvPolynomial.map_X, MvPolynomial.map_C, arcX]) P
  have hγn : γ ^ n ≠ 0 := pow_ne_zero _ hγ
  let P₂ : MvPolynomial (ArcLt Dw) (LaurentSeries Dv.Tv.Fr) :=
    MvPolynomial.C (HahnSeries.C (Γ := ℤ) (γ ^ n)⁻¹) * P₁
  have hP₂ : algebraMap _ (ArcS Dw Dv.Tv.Fr) P₂ = ψ.toRingHom f := by
    have : algebraMap _ (ArcS Dw Dv.Tv.Fr) P₁ = _ := hP₁.trans e3
    simp only [P₂]
    rw [map_mul, this, ← mul_assoc, ← map_pow, ← map_mul, ← map_pow, ← map_mul, ← map_pow, ← map_mul,
      inv_mul_cancel₀ hγn, map_one, map_one, map_one, one_mul]
    rfl
  have hψι : ψ.toRingHom.comp (arcιR Dw Dv.Tv.V Dv.ϖ) =
      (arcι Dw Dv.Tv.Fr).comp (PowerSeries.map (algebraMap Dv.Tv.V Dv.Tv.Fr)) := RingHom.ext fun p => hψC p
  obtain ⟨N, G, hG⟩ := hdiv ψ.toRingHom hψι hψX f ⟨P₂, hP₂⟩
  have hψalg : ψ.toRingHom.comp (algebraMap (MvPolynomial (ArcLt Dw) (PowerSeries Dv.Tv.V)) _) =
      (algebraMap _ (ArcS Dw Dv.Tv.Fr)).comp (MvPolynomial.map ((HahnSeries.ofPowerSeries ℤ Dv.Tv.Fr).comp
        (PowerSeries.map (algebraMap Dv.Tv.V Dv.Tv.Fr)))) := by
    refine MvPolynomial.ringHom_ext (fun p => ?_) (fun x => ?_)
    · simp only [RingHom.comp_apply, MvPolynomial.map_C]
      exact hψC p
    · simp only [RingHom.comp_apply, MvPolynomial.map_X]
      exact hψX x
  have hPG : P₂ * MvPolynomial.C (HahnSeries.ofPowerSeries ℤ Dv.Tv.Fr (PowerSeries.C (R := Dv.Tv.Fr)
      (algebraMap Dv.Tv.V Dv.Tv.Fr Dv.ϖ) * PowerSeries.X)) ^ N =
      MvPolynomial.map ((HahnSeries.ofPowerSeries ℤ Dv.Tv.Fr).comp
        (PowerSeries.map (algebraMap Dv.Tv.V Dv.Tv.Fr))) G := by
    apply hinj
    have h1 := congrArg ψ.toRingHom hG
    have h2 := RingHom.congr_fun hψalg G
    have h3 := RingHom.congr_fun hψι (PowerSeries.C (R := Dv.Tv.V) Dv.ϖ * PowerSeries.X)
    simp only [RingHom.comp_apply] at h2 h3
    rw [h2, map_mul, map_pow, h3, ← hP₂, map_mul (PowerSeries.map _), PowerSeries.map_C, PowerSeries.map_X] at h1
    rw [← h1, map_mul, map_pow]
    rfl
  have hdet0 : (∏ τ : E →+* ℂ, (Matrix.of fun i k : Fin (Dw.mult τ) => Y ⟨τ, i, k⟩).det) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hdet
    exact zero_ne_one hdet
  obtain ⟨ev, hevC, hevX, hevf⟩ := GlobalTheory.T.exists_eval_arcLetterRingOverDVR_disc E H Dw Dv.Tv Dv.ϖ Z.K Dv.ιT hϖ Dv.norm_le t Y
    (Z.S_disc t ht).1 (Z.S_disc t ht).2 hdet0
  obtain ⟨hT, hS⟩ := hevf f N G P₂ hG hPG
  have hbd := hRec F hF t ht Y hY hdet ev hevC hevX
  have hq : (fun x => MvPolynomial.eval Y (MvPolynomial.map Dv.ιT (q x))) =
      frameSub (fun τ => (Bm τ).map Dv.ιT) (fun τ k => Dv.ιT (lam τ k)) Y := by
    funext x
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [q, frameSub, map_sum, map_mul, MvPolynomial.map_X, MvPolynomial.map_C, MvPolynomial.eval_X,
      MvPolynomial.eval_C, Matrix.map_apply, map_inv₀, Finset.sum_mul, mul_assoc]
  have hterm : ∀ k : ℤ, MvPolynomial.eval Y (MvPolynomial.map Dv.ιT (GlobalTheory.ArcQ.lcoeffPoly P₂ k)) * t ^ k =
      (Dv.ιT γ ^ n)⁻¹ * (MvPolynomial.eval (frameSub (fun τ => (Bm τ).map Dv.ιT) (fun τ k => Dv.ιT (lam τ k)) Y)
        (MvPolynomial.map Z.ι (GlobalTheory.ArcQ.lcoeffPoly P k)) * t ^ k) := fun k => by
    simp only [P₂]
    rw [lcoeffPoly_const_mul, map_mul, map_mul, MvPolynomial.map_C, MvPolynomial.eval_C, hco, eval_subst, hq,
      Dv.ιT_io, map_inv₀, map_pow, mul_assoc]
  have hγK : Dv.ιT γ ^ n ≠ 0 := pow_ne_zero _ ((map_ne_zero _).2 hγ)
  rw [← hP, arcNum_of_poly]
  simp only [hterm] at hT hS
  refine ⟨?_, ?_⟩
  · have := hT.const_mul ‖Dv.ιT γ ^ n‖
    rw [mul_zero] at this
    refine this.congr fun k => ?_
    rw [← norm_mul, mul_inv_cancel_left₀ hγK]
  · rw [tsum_mul_left] at hS
    rw [← hS]
    exact hbd

theorem frame_of_cut : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), GlobalTheory.Reg.EvLaws Xo c → ∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (w : HeightOneSpectrum (𝓞 K₁)) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (Fs : Set (Rul Xo c)), (∀ F ∈ Fs, F ∈ sec Xo c a n) → (∀ (Z : FinSite K₁ w) (Dv : DvrFrame d w Z) (γ : Dv.Tv.Fr) (lam : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Dv.Tv.Fr) (Bm : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Dv.Tv.Fr), γ ≠ 0 → (∀ τ k, lam τ k ≠ 0) → BcRigidAt Dv γ lam Bm → RecordAt Dv Fs → FrameBound Z (Dv.ιT γ) (fun τ k => Dv.ιT (lam τ k)) (fun τ => (Bm τ).map Dv.ιT) n d Fs) ∧ ∀ (vth : ℤ) (vη : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → ℤ) (m : ℕ), FinLocalCutAt d w vth vη m Fs → FinLocalAt d w n vth vη m Fs := by
  intro hL hL2 E _ _ _ H Dw l Xo c hev K₁ _ _ _ d w a n Fs hFs
  refine ⟨fun Z Dv γ lam Bm hγ _ hBc hRec => frameBound_of_cut hL hL2 hev hFs Z Dv γ lam Bm hγ hBc hRec, ?_⟩
  rintro vth vη m ⟨Z, Dv, γ, lam, A, Bm, ⟨hγ, hγn⟩, hlam, ⟨hAB, hA⟩, hBc, hRec⟩
  refine ⟨Z, Dv.ιT γ, fun τ k => Dv.ιT (lam τ k), fun τ => (A τ).map Dv.ιT, fun τ => (Bm τ).map Dv.ιT,
    ⟨(map_ne_zero _).2 hγ, hγn⟩, fun τ k => ⟨(map_ne_zero _).2 (hlam τ k).1, (hlam τ k).2⟩,
    ⟨fun τ => ?_, fun τ k l => hA τ k l⟩, frameBound_of_cut hL hL2 hev hFs Z Dv γ lam Bm hγ hBc hRec⟩
  beta_reduce
  rw [← Matrix.map_mul, hAB, Matrix.map_one _ (map_zero _) (map_one _)]

end GlobalTheory.ArcQ.FrameCut
end
end

noncomputable section

namespace GlobalTheory.FinLocalTan

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
  Formalism.L2.Pj.QAt GlobalTheory.ArcQ
open scoped CategoryTheory.Obj

def origin (R : Type) [CommRing R] : Over.mk (𝟙 (Sp R)) ⟶ epsR R :=
  Over.homMk (spMap (TrivSqZeroExt.fstHom R R R).toRingHom)
    ((spMap_comp _ _).symm.trans ((congrArg spMap (RingHom.ext fun _ => rfl)).trans (Spec.map_id (CommRingCat.of R))))

section

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}

theorem gtTanR_iff (ν : GtPt D (epsR R)) : GtTanR ν ↔ origin R ≫ ν.b = 1 ∧
    ∀ χ y J, Good D.P.L y J → val (ν.s χ) (origin R).left y J = 1 := by
  constructor
  · rintro ⟨g₀, h₀, h⟩
    obtain ⟨h₁, h₂⟩ := (ConstLie.isZero_iff_zeroAlong (ρ := origin R) h).1 h₀
    refine ⟨h₁, fun χ y J hJ => ?_⟩
    have := h₂ χ _ (𝟙 _) y J hJ
    rwa [Category.id_comp] at this
  · rintro ⟨h₁, h₂⟩
    obtain ⟨g₀, h⟩ := ConstLie.exists_isPullGt (origin R) ν
    obtain ⟨b, v⟩ := (TorusModel.isPull_iff _ _ _).1 h
    exact ⟨g₀, ⟨b.trans h₁, fun χ => corr_of_val D.P.isLB fun y J hJ =>
      (v χ y J hJ).trans ((h₂ χ y J hJ).trans (val_one _).symm)⟩, h⟩

theorem gtTanR_of_isZero {ν : GtPt D (epsR R)} (h : ν.IsZero) : GtTanR ν := by
  have hb : ν.b = 1 := h.1
  exact (gtTanR_iff ν).2 ⟨by rw [hb, MonObj.comp_one], fun χ y J hJ => (val_corr hJ (h.2 χ) _).trans (val_one _)⟩

theorem gtTanR_of_scale {a : R} {ν ν' : GtPt D (epsR R)} (h : GtPt.IsPull (spMap (epsScaleR a)) ν ν')
    (ht : GtTanR ν) : GtTanR ν' := by
  obtain ⟨h₁, h₂⟩ := (gtTanR_iff ν).1 ht
  have s : (origin R).left ≫ spMap (epsScaleR a) = (origin R).left :=
    (spMap_comp _ _).symm.trans (congrArg spMap (RingHom.ext fun x => by simp [epsScaleR]))
  refine (gtTanR_iff ν').2 ⟨Over.OverMorphism.ext ?_, fun χ y J hJ => ?_⟩
  · rw [← h₁, Over.comp_left, Over.comp_left, h.1, ← Category.assoc, s]
  · refine (val_corr hJ (h.2 χ) _).trans ((val_pull hJ _ _ _).trans ?_)
    rw [s]
    exact h₂ χ y J hJ

theorem gtTanR_of_isAdd {ν ν' ν'' : GtPt D (epsR R)} (h : ν.IsAdd ν' ν'') (ht : GtTanR ν) (ht' : GtTanR ν') :
    GtTanR ν'' := by
  obtain ⟨h₁, h₂⟩ := (gtTanR_iff ν).1 ht
  obtain ⟨h₁', h₂'⟩ := (gtTanR_iff ν').1 ht'
  have hb : ν''.b = ν.b * ν'.b := h.1
  refine (gtTanR_iff ν'').2 ⟨by rw [hb, MonObj.comp_mul, h₁, h₁', _root_.mul_one], fun χ y J hJ => ?_⟩
  have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (h.2 χ) (origin R).left).trans (val_mul hJ _ _ _))
  have c := val_cub D.cub (origin R) hJ (DegPre.cT D (epsR R) χ) ν.b ν'.b
  have c' := congrArg (fun z => cubV D.cub y J ((origin R) ≫ DegPre.cT D (epsR R) χ)
    ((origin R) ≫ ν.b) z) h₁'
  have cz (x x' : Over.mk (𝟙 (Sp R)) ⟶ D.P.A) : cubV D.cub y J x x' 1 = 1 := by
    have hm : lift x (lift x' 1) = lift x x' ≫ faceMap (G := D.P.A) 2 := by
      simp [faceMap, x2, pzero, Hom.one_def]
    refine Eq.trans ?_ ((val_corr (hJ := hJ) (D.cub.face 2) (lift x x').left).trans (val_one _))
    refine Eq.trans ?_ (val_pull (hJ := hJ) ..).symm
    show val D.cub.t (lift x (lift x' 1)).left y J = _
    rw [hm, Over.comp_left]
    all_goals rfl
  have c := c.trans (c'.trans (cz _ _))
  have e' := (congrArg₂ (· * ·) rfl c).symm.trans (e.trans (congrArg₂ (· * ·) (h₂ χ y J hJ) (h₂' χ y J hJ)))
  simpa using e'

theorem gtTanR_of_gtComb {m : ℕ} {cf : Fin m → R} {e : Fin m → GtPt D (epsR R)} {ν : GtPt D (epsR R)}
    (h : GtComb cf e ν) (he : ∀ i, GtTanR (e i)) : GtTanR ν := by
  obtain ⟨u, p, hu, h₀, ha, rfl⟩ := h
  have : ∀ i, GtTanR (p i) := fun i => Fin.induction (gtTanR_of_isZero h₀)
    (fun j ih => gtTanR_of_isAdd (ha j) ih (gtTanR_of_scale (hu j) (he j))) i
  exact this _

end

theorem gtTanR_of_letBC {K K' : Type} [Field K] [Field K'] {f : K →+* K'} {D : DegPre K} {D' : DegPre K'}
    {p : IsPullDeg f D D'} {ν : GtPt D (epsR K)} {ν' : GtPt D' (epsR K')} (h : LetBC p ν ν') (ht : GtTanR ν') :
    GtTanR ν := by
  obtain ⟨h₁, h₂⟩ := (gtTanR_iff ν').1 ht
  have h : ν'.b.left ≫ prj p = spMap (Formalism.L2.Pj.dualMap f) ≫ ν.b.left ∧ ∀ χ,
      (∀ i, DegPre.gtφT D' (epsR K') ν'.b χ i ≫ prj p = spMap (Formalism.L2.Pj.dualMap f) ≫ DegPre.gtφT D (epsR K) ν.b (p.xe χ) i) ∧
      PMaps p.w _ _ DegPre.gtε (ν'.s χ) (ν.s (p.xe χ)) (spMap (Formalism.L2.Pj.dualMap f)) := ⟨h.1, fun χ => ⟨(h.2 χ).1, (maps_iff p.w _ _ _ (ν'.s χ) (ν.s (p.xe χ)) _ _
    (GeneratorPullback.pullAlong_le _ _ _ _ _ (h.2 χ).1) (fun _ => rfl)).1 (h.2 χ).2⟩⟩
  have sq : (origin K').left ≫ spMap (Formalism.L2.Pj.dualMap f) = spMap f ≫ (origin K).left := by
    refine (spMap_comp _ _).symm.trans (Eq.trans (congrArg spMap ?_) (spMap_comp _ _))
    exact RingHom.ext fun x => by simp [Formalism.L2.Pj.dualMap]
  have : Flat (spMap f) := by
    refine (HasRingHomProperty.Spec_iff (P := @Flat)).2 ?_
    exact RingHom.Flat.of_isField (Field.toIsField K) _
  have : Surjective (spMap f) := by
    have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
    exact ⟨fun y => ⟨(default : PrimeSpectrum K'), Subsingleton.elim _ _⟩⟩
  have : Epi (spMap f) := Flat.epi_of_flat_of_surjective _
  have hb : origin K ≫ ν.b = 1 := by
    refine Over.OverMorphism.ext ((cancel_epi (spMap f)).1 ?_)
    have o : (origin K').left ≫ ν'.b.left = eSec D'.P.A := (congrArg (fun q => q.left) h₁).trans (Category.id_comp _)
    have o' : (1 : Over.mk (𝟙 (Sp K)) ⟶ D.P.A).left = eSec D.P.A := Category.id_comp _
    rw [o', Over.comp_left]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) sq.symm).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) h.1.symm).trans ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) o).trans p.he)))))
  refine (gtTanR_iff ν).2 ⟨hb, fun χ y J hJ => ?_⟩
  obtain ⟨x, rfl⟩ := p.xe.surjective χ
  have C := corr_of_val_flat_surjective (spMap f) D.P.isLB
    (t := LB.pullGen D.P.L _ _ (ν.s (p.xe x)) (origin K).left) (t' := LB.oneGen D.P.L) fun z I hI => by
      obtain ⟨I', hI'⟩ := DegPull.exists_good' D'.P.isLB z
      have e := (ConstFam.pmaps_val (h.2 x).1 (h.2 x).2 (origin K').left hI hI').trans (congrArg (· * _)
        (FormalPoint.prod_gtφT (origin K') ν'.b x (ConstFam.wVal p.w z I I')))
      rw [h₁, _root_.mul_one, inv_mul_cancel, _root_.one_mul, mul_inv_cancel, _root_.one_mul, sq] at e
      exact (val_pull hI _ _ _).trans (e.trans ((h₂ x z I' hI').trans (val_one _).symm))
  have v := (val_pull hJ _ _ _).symm.trans ((val_corr hJ C (𝟙 _)).trans (val_one _))
  rwa [Category.id_comp] at v

end GlobalTheory.FinLocalTan

namespace GlobalTheory.ArcQ

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

theorem finLocal_vV_nonneg {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K]
    [Algebra V K] [IsFractionRing V K] {v : V} (hv : algebraMap V K v ≠ 0) : 0 ≤ vV V (algebraMap V K v) := by
  have h1 : valV V (algebraMap V K v) ≤ 1 := HeightOneSpectrum.valuation_le_one _ v
  have h2 := (WithZero.log_le_log (valV_ne_zero (V := V) hv) one_ne_zero).2 h1
  rw [WithZero.log_one] at h2
  simp only [vV]
  omega

theorem finLocal_vV_pos {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K]
    [Algebra V K] [IsFractionRing V K] {v : V} (hv : Irreducible v) : 0 < vV V (algebraMap V K v) := by
  have h0 : algebraMap V K v ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective V K)).2 hv.ne_zero
  have h1 : valV V (algebraMap V K v) < 1 :=
    (HeightOneSpectrum.valuation_lt_one_iff_mem _ v).2 ((IsLocalRing.mem_maximalIdeal v).2 hv.not_isUnit)
  have h2 := (WithZero.log_lt_log (valV_ne_zero (V := V) h0) one_ne_zero).2 h1
  rw [WithZero.log_one] at h2
  simp only [vV]
  omega

theorem finLocalAt_of_intModel :
    Out.Laws → Out.Laws2 → Out.UnifBaseChangeSt → Out.Laws5 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), GlobalTheory.Reg.EvLaws Xo c → ∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (w : HeightOneSpectrum (𝓞 K₁)) (Tv : CDVR) (io : K₁ →+* Tv.Fr) (Wl : ValuationSubring ℂ) (Yw : Model Xo c (c.V Wl).subtype) (M : IntModel d Tv io Wl) (la : HeightOneSpectrum (𝓞 c.F)) (eL : ℕ) (lam : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Tv.Fr) (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Tv.Fr) (vth : ℤ) (vη : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → ℤ) (m : ℕ), d.OverBase → Tv.FinRes → OverLa w Tv.V io 1 → OverLa la Tv.V (io.comp (algebraMap c.F K₁)) eL → Yw.N4 → PushInvertible Yw.t.G Yw.t.PP.L → (∀ (χ : Sp (PowerSeries Tv.V) ⟶ Yw.X) (W : Wit Yw M.aw χ), ArcBasis W M.ρ M.ew) → (M.γ ≠ 0 ∧ vV Tv.V M.γ = vth) → (∀ τ k, lam τ k ≠ 0 ∧ vV Tv.V (lam τ k) = vη τ k) → (∀ τ, (A τ).det ≠ 0) → (∀ τ k l, M.g τ k l = lam τ k * A τ k l) → (∀ τ k l, A τ k l = 0 ∨ -(m : ℤ) ≤ vV Tv.V (A τ k l)) → ∀ a n, FinLocalAt d w n vth vη m (intAt Xo c a n la) := by
  intro h1 h2 hU h5 E _ _ _ H Dw l Xo c hev K₁ _ _ _ d w Tv io Wl Yw M la eL lam A vth vη m hob hfin how hola h4
    hpush hbas hγ hlam hdet hg hA a n
  obtain ⟨Z, ιT, hc, hn, hs⟩ := (exists_finSite_norm_eq_zpow_siteAlg K₁ w).2 Tv io hfin how
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible Tv.V
  have hcpl : IsAdicComplete (Ideal.span {ϖ}) Tv.V := by
    rw [← hϖ.maximalIdeal_eq]
    infer_instance
  obtain ⟨χ, hχ, -⟩ := h4 Tv.V M.b ϖ M.aw (Or.inr ⟨inferInstance, hϖ, hcpl⟩)
  obtain ⟨hbase, -, hgen, t, mm, P, φ, he, ww, e, hspec⟩ := (hχ χ).1 rfl
  let W : Wit Yw M.aw χ := ⟨t, mm, P, φ, he, ww, e, hspec⟩
  obtain ⟨algR, halg, y₀, yR, hfr, hchg⟩ := exists_dvr_frPt h1 h2 E H Dw l Xo c (c.V Wl) (c.V Wl).subtype Yw Tv ϖ
    (io.comp (algebraMap c.F K₁)) M.b M.aw χ W M.ρ M.ew M.thw hϖ
    (RingHom.ext fun x => (M.b_eq x).symm) M.ρ_eq hbase hgen (mono_spMap_subtype _) hpush (hbas χ W) M.thw_nz
  have hle : ∀ v : Tv.V, ‖ιT (algebraMap Tv.V Tv.Fr v)‖ ≤ 1 := by
    intro v
    by_cases hv : algebraMap Tv.V Tv.Fr v = 0
    · rw [hv, map_zero, norm_zero]
      exact zero_le_one
    · rw [hn _ hv]
      exact zpow_le_one₀ Z.r_pos Z.r_lt.le (finLocal_vV_nonneg hv)
  have hlt : ‖ιT (algebraMap Tv.V Tv.Fr ϖ)‖ < 1 := by
    rw [hn _ ((map_ne_zero_iff _ (IsFractionRing.injective Tv.V Tv.Fr)).2 hϖ.ne_zero)]
    exact zpow_lt_one₀ Z.r_pos Z.r_lt (finLocal_vV_pos hϖ)
  let Dv : DvrFrame d w Z :=
    { Tv := Tv, io := io, ιT := ιT, ιT_io := hc, norm_le := hle, ϖ := ϖ, ϖ_irr := hϖ, norm_ϖ := hlt
      algR := algR
      algW := ((arcι Dw Tv.Fr).comp ((PowerSeries.C (R := Tv.Fr)).comp (io.comp (algebraMap c.F K₁)))).toAlgebra
      algW_eq := fun _ => rfl
      yR := yR }
  have htan : ∀ τ k, GtTanR (d.e τ k) := fun τ k => by
    obtain ⟨e₁, e₂, -, l₂, t₁, hc⟩ := M.e_tie
    exact FinLocalTan.gtTanR_of_letBC (l₂ τ k) (FinLocalTan.gtTanR_of_gtComb (hc τ k) (t₁ τ))
  obtain ⟨ζ, N, hN, hζ, hnorm', -⟩ := exists_normalForm h1 h2 E H Dw l Xo c K₁ d
  have hnorm := hnorm' htan
  have hAB : ∀ τ, A τ * (A τ)⁻¹ = 1 := fun τ => Matrix.mul_nonsing_inv _ (Ne.isUnit (hdet τ))
  have hbc : BcRigidAt Dv (io ζ * M.γ) lam (fun τ => (A τ)⁻¹) :=
    GlobalTheory.ArcRigidity.bcRigidAt_of_intModel h1 h2 hU h5 E H Dw l Xo c K₁ d w Z Dv Wl Yw M χ W y₀ ζ lam A (fun τ => (A τ)⁻¹) hob hnorm hbase
      halg hfr hchg hγ.1 (fun τ k => (hlam τ k).1) hAB hg
  have hmono : Mono Yw.j := by
    have := mono_spMap_subtype (c.V Wl)
    have := Yw.jQ_open
    unfold Model.j
    infer_instance
  have hrec : RecordAt Dv (intAt Xo c a n la) :=
    recordAt_of_isArcFr h1 h2 E H Dw l Xo c hev K₁ d w Z Dv (c.V Wl) (c.V Wl).subtype Yw M.b M.aw χ W M.ρ M.ew M.thw y₀ la eL
      hs hola M.ρ_eq halg hpush (hbas χ W) M.thw_nz hmono hfr hchg a n
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at hζ
    exact zero_ne_one hζ
  have hζ1 : ‖ιT (io ζ)‖ = 1 := by
    have : ‖ιT (io ζ)‖ ^ N = 1 := by
      rw [← norm_pow, ← map_pow, ← map_pow, hζ, map_one, map_one, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hN.ne').1 this
  refine (GlobalTheory.ArcQ.FrameCut.frame_of_cut h1 h2 E H Dw l Xo c hev K₁ d w a n (intAt Xo c a n la) (fun F hF => hF.1)).2 vth vη m
    ⟨Z, Dv, io ζ * M.γ, lam, A, fun τ => (A τ)⁻¹, ⟨mul_ne_zero ((map_ne_zero io).2 hζ0) hγ.1, ?_⟩,
      fun τ k => ⟨(hlam τ k).1, ?_⟩, ⟨hAB, fun τ k l => ?_⟩, hbc, hrec⟩
  · change ‖ιT (io ζ * M.γ)‖ = _
    rw [map_mul, norm_mul, hζ1, one_mul, hn _ hγ.1, hγ.2]
  · change ‖ιT (lam τ k)‖ = _
    rw [hn _ (hlam τ k).1, (hlam τ k).2]
  · change ‖ιT (A τ k l)‖ ≤ _
    by_cases h0 : A τ k l = 0
    · rw [h0, map_zero, norm_zero]
      exact (zpow_pos Z.r_pos _).le
    · rw [hn _ h0]
      exact zpow_le_zpow_right_of_le_one₀ Z.r_pos Z.r_lt.le ((hA τ k l).resolve_left h0)

end GlobalTheory.ArcQ
