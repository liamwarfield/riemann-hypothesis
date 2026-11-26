module

public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MetricDataUnique
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralFrameAfterExtIffAnd

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegralGeneratorBaseChangeValuationRing
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegralGeneratorBaseChangeValuationRing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT

theorem secInt_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l), ∀ (T T' : CDVR) (ψ : T.V →+* T'.V) (i : T.Fr →+* T'.Fr), (algebraMap T'.V T'.Fr).comp ψ = i.comp (algebraMap T.V T.Fr) → ∀ (x : Sp T.Fr ⟶ Xo.X) (x' : Sp T'.Fr ⟶ Xo.X) (G : PAT H (Sp T.V)) (G' : PAT H (Sp T'.V)) (t : SAB H (Sp T.Fr)) (t' : SAB H (Sp T'.Fr)) (m1 : SABMap t Xo.univ.t x) (m2 : SABMap t G.t (spMap (algebraMap T.V T.Fr))) (m1' : SABMap t' Xo.univ.t x') (m2' : SABMap t' G'.t (spMap (algebraMap T'.V T'.Fr))) (n : SABMap G'.t G.t (spMap ψ)) (n' : SABMap t' t (spMap i)), x' = spMap i ≫ x → m1'.φ = n'.φ ≫ m1.φ → m2'.φ ≫ n.φ = n'.φ ≫ m2.φ → ∀ (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx x')), SecBC i 1 x x' s s' → SecInt T m1 m2 s → SecInt T' m1' m2' s' := by
  intro E _ _ _ H Dw l Xo T T' ψ i hψ x x' G G' t t' m1 m2 m1' m2' n n' hx h1 h2 s s' hb
  have isoMaps_iff {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F))
      (σ : LB.Sec L') (s : LB.Sec (L.pull F)) :
      IsoMaps w σ s ↔ ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (j : L.ι) (k : L'.ι), F (r z) ∈ L.U j → r z ∈ L'.U k →
        gs r z _ (s.f (fun _ => j)) = (gw w r z j k).val * gs r z _ (σ.f k) := by
    constructor
    · intro h Z r z j k hj hk
      have hz : r z ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k := ⟨mem_pull.2 hj, hk⟩
      have a := congrArg (gs r z _) (h (fun _ => j) k)
      exact (gs_res _ z _ hz _).symm.trans (a.trans ((gs_mul _ z _ hz _ _).trans
          (congrArg₂ (· * ·) (gs_unit _ z _ hz _) (gs_res _ z _ hz _))))
    · intro h (i : PUnit → L.ι) k
      exact fn_ext fun p hp =>
        (gs_res _ p _ hp _).trans ((h _ (𝟙 _) p (i PUnit.unit) k (mem_pull.1 hp.1) hp.2).trans
          (Eq.symm ((gs_mul _ p _ hp _ _).trans (congrArg₂ (· * ·) (gs_unit (𝟙 _) p _ hp _) (gs_res _ p _ hp _)))))

  rintro ⟨θ, hθ, w2, σ, θ2, r2, i2, p2, tie⟩
  have hS : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  obtain ⟨wn, gn, rn, -⟩ := n.lin
  obtain ⟨wn', gn', rn', -⟩ := n'.lin
  obtain ⟨w2', g2', r2', -⟩ := m2'.lin
  have Rn : RigIso n wn := ⟨gn, rn⟩
  have Rn' : RigIso n' wn' := ⟨gn', rn'⟩
  have R2' : RigIso m2' w2' := ⟨g2', r2'⟩
  obtain ⟨θ', hθ'⟩ := sec_pull_down ((isGen_iff wn).1 gn) G.t.PP.isLB G'.t.PP.isLB θ
  obtain ⟨σ', hσ'⟩ := sec_pull_down ((isGen_iff w2').1 g2') G'.t.PP.isLB t'.PP.isLB θ'
  have nz : ∀ y : Sp T.V, ∃ z : G.t.G.left, G.t.G.hom z = y ∧ z ∈ Out.nonzeroLocus θ := fun y => by
    obtain ⟨b, hb, -⟩ := GlobalTheory.KeyOnPol.exists_generator hS G.pol
    obtain ⟨z, hz, hm⟩ := hb y
    obtain ⟨a, ha, -⟩ := hθ b
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hm
    rw [ha k, Scheme.basicOpen_mul] at hk
    exact ⟨z, hz, TopologicalSpace.Opens.mem_iSup.2 ⟨k, hk.2⟩⟩
  have nz' := SectionBaseChange.fibre_nonzero_of_pull G'.t.PP.isLB hθ' n.cart.1 nz
  refine ⟨θ', SectionBaseChange.generates hS G.pol n.cart.1 G'.t.PP.isLB ⟨wn, gn⟩ θ' nz', w2', σ',
    thfPull G'.t.PP.L m2'.φ θ', R2', ?_, fun _ _ => rfl, ?_⟩
  · refine (isoMaps_iff _ _ _).2 fun Z r z j k hj hk => ?_
    exact (gs_appLE m2'.φ _ _ _ r z (mem_pull.2 hj) _).trans (hσ' Z r z j k hj hk)
  · refine (TieCalc.secTie_baseChange m1 tie i m1' n' s' wn' (thfPull t.PP.L n'.φ σ) σ' hx h1 hb Rn'
      (fun _ _ => rfl)).2 ((isoMaps_iff _ _ _).2 fun Z r z j k hj hk => ?_)
    have hbase : spMap (algebraMap T'.V T'.Fr) ≫ spMap ψ = spMap i ≫ spMap (algebraMap T.V T.Fr) := by
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hψ]
    obtain ⟨N, hN⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ n m2'
    have hN' : N.φ = m2'.φ ≫ n.φ := hN
    obtain ⟨wa, ra, Ta⟩ := GlobalTheory.LiftBaseChange.rigIso_comp n m2' N rfl hN' Rn R2'
    obtain ⟨wb, rb, Tb⟩ := GlobalTheory.LiftBaseChange.rigIso_comp m2 n' N hbase (hN'.trans h2) r2 Rn'
    have hp : IsProper t'.G.hom := MorphismProperty.of_isPullback (P := @IsProper) m2'.cart.1 G'.ab.proper
    have hab : IsAbelianScheme t'.G := ⟨t'.semi.comm, t'.semi.smooth, hp, t'.semi.geomConnected⟩
    obtain rfl : wa = wb := iso_unique_of_rig GlobalTheory.globalFns_holds t'.G hab t'.PP.isLB G.t.PP.isLB ra.1 rb.1 ra.2 rb.2
    obtain ⟨a, ha⟩ := exists_chart G.t.PP.isLB (m2.φ (n'.φ (r z)))
    obtain ⟨b, hb'⟩ := exists_chart G'.t.PP.isLB (m2'.φ (r z))
    have ha' : n.φ (m2'.φ (r z)) ∈ G.t.PP.L.U a := (congrArg (fun q => q (r z) ∈ G.t.PP.L.U a) h2).mpr ha
    have e1 := hθ' Z (r ≫ m2'.φ) z a b ha' hb'
    have e2 := hσ' Z r z b k hb' hk
    have le : (G.t.PP.L.pull m2.φ).U (fun _ => a) ≤ m2.φ ⁻¹ᵁ G.t.PP.L.U a := fun q hq => mem_pull.1 hq
    have e3 := (isoMaps_iff _ _ _).1 i2 Z (r ≫ n'.φ) z a j ha hj
    rw [p2 (fun _ => a) le, gs_appLE m2.φ _ _ le (r ≫ n'.φ) z (mem_pull.2 ha), Category.assoc, ← h2,
      ← Category.assoc, e1, e2, ← _root_.mul_assoc, ← Units.val_mul, ← Ta Z r z a b k ha' hb' hk,
      Tb Z r z a j k ha hj hk, Units.val_mul, _root_.mul_assoc] at e3
    exact (gs_appLE n'.φ _ _ _ r z (mem_pull.2 hj) _).trans ((Units.mul_right_inj _).1 e3).symm

end GlobalTheory.LamT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegralGeneratorBaseChangeValuationRingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_generator_baseChange_valuationRing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l), ∀ (T T' : CDVR) (ψ : T.V →+* T'.V) (i : T.Fr →+* T'.Fr), (algebraMap T'.V T'.Fr).comp ψ = i.comp (algebraMap T.V T.Fr) → ∀ (x : Sp T.Fr ⟶ Xo.X) (x' : Sp T'.Fr ⟶ Xo.X) (G : PAT H (Sp T.V)) (G' : PAT H (Sp T'.V)) (t : SAB H (Sp T.Fr)) (t' : SAB H (Sp T'.Fr)) (m1 : SABMap t Xo.univ.t x) (m2 : SABMap t G.t (spMap (algebraMap T.V T.Fr))) (m1' : SABMap t' Xo.univ.t x') (m2' : SABMap t' G'.t (spMap (algebraMap T'.V T'.Fr))) (n : SABMap G'.t G.t (spMap ψ)) (n' : SABMap t' t (spMap i)), x' = spMap i ≫ x → m1'.φ = n'.φ ≫ m1.φ → m2'.φ ≫ n.φ = n'.φ ≫ m2.φ → ∀ (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx x')), SecBC i 1 x x' s s' → SecInt T m1 m2 s → SecInt T' m1' m2' s' := by
  first | exact @GlobalTheory.LamT.secInt_baseChange | exact GlobalTheory.LamT.secInt_baseChange | (intros; apply GlobalTheory.LamT.secInt_baseChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RuleValueIntegralOfSupLatticeValuesNonneg
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RuleValueIntegralOfSupLatticeValuesNonneg
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

noncomputable section

namespace GlobalTheory.LamT

theorem mem_range_of_nval_nonneg {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K']
    [Algebra V K'] [IsFractionRing V K'] {e : ℕ} (he : 0 < e) {x : K'} (h : 0 ≤ Formalism.L2.Pj.nval V e x) :
    x ∈ Set.range (algebraMap V K') := by
  by_cases hx : x = 0
  · exact ⟨0, by rw [map_zero, hx]⟩
  rw [nval_of_ne hx, EReal.coe_nonneg] at h
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  have h1 : (0 : ℝ) ≤ vV V x := by
    have := mul_nonneg h he'.le
    rwa [div_mul_cancel₀ _ he'.ne'] at this
  have h2 : 0 ≤ vV V x := by exact_mod_cast h1
  have h3 : valV V x ≤ 1 := by
    refine (WithZero.log_le_log (valV_ne_zero (V := V) hx) one_ne_zero).1 ?_
    simp only [WithZero.log_one]
    simp only [vV] at h2
    omega
  exact IsDiscreteValuationRing.exists_lift_of_le_one (A := V) (K := K') h3

theorem evR_mem_range_of_valSet_nonneg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (F : Rul Xo c), (∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v F) → ∀ (T : CDVR) (io : c.F →+* T.Fr), T.FinRes → letI := io.toAlgebra; ∀ y : FrPt Xo c T.Fr, Integral T io y → evR Xo c F y ∈ Set.range (algebraMap T.V T.Fr) := by
  intro E _ _ _ H Dw l Xo c F hF T io hT y hy
  let := io.toAlgebra
  have valV_le_one' (v : T.V) : valV T.V (algebraMap T.V T.Fr v) ≤ 1 := HeightOneSpectrum.valuation_le_one _ v
  have valV_lt_one_iff' (v : T.V) : valV T.V (algebraMap T.V T.Fr v) < 1 ↔ v ∈ IsLocalRing.maximalIdeal T.V :=
    HeightOneSpectrum.valuation_lt_one_iff_mem _ v
  have valV_eq_one_iff_isUnit' (v : T.V) : valV T.V (algebraMap T.V T.Fr v) = 1 ↔ IsUnit v := by
    rw [← IsLocalRing.notMem_maximalIdeal, ← valV_lt_one_iff', not_lt]
    exact ⟨fun h => h.ge, fun h => le_antisymm (valV_le_one' v) h⟩
  have vV_pos' {v : T.V} (h0 : v ≠ 0) (h : v ∈ IsLocalRing.maximalIdeal T.V) : 0 < vV T.V (algebraMap T.V T.Fr v) := by
    have h1 : algebraMap T.V T.Fr v ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective T.V T.Fr)).2 h0
    have := (WithZero.log_lt_log (valV_ne_zero (V := T.V) h1) one_ne_zero).2 ((valV_lt_one_iff' v).2 h)
    simp only [WithZero.log_one] at this
    simp only [vV]; omega
  open IsLocalRing in
  have hex : ∃ (la : HeightOneSpectrum (𝓞 c.F)) (e : ℕ), OverLa la T.V io e := by
    have hint : ∀ a : 𝓞 c.F, ∃ v : T.V, algebraMap T.V T.Fr v = io a := fun a =>
      IsIntegrallyClosed.algebraMap_eq_of_integral (R := T.V) (K := T.Fr)
        (IsIntegral.map_of_comp_eq (Int.castRingHom T.V) io (RingHom.ext_int _ _) a.isIntegral_coe)
    choose g0 hg0 using hint
    have hinj := IsFractionRing.injective T.V T.Fr
    let g : 𝓞 c.F →+* T.V :=
      { toFun := g0
        map_one' := hinj (by simp [hg0])
        map_mul' := fun a b => hinj (by simp [hg0])
        map_zero' := hinj (by simp [hg0])
        map_add' := fun a b => hinj (by simp [hg0]) }
    have hg : ∀ a, algebraMap T.V T.Fr (g a) = io (algebraMap (𝓞 c.F) c.F a) := hg0
    have hne : (maximalIdeal T.V).comap g ≠ ⊥ := by
      have : Finite (ResidueField T.V) := hT
      have hc : Nat.card (ResidueField T.V) ≠ 0 := Nat.card_pos.ne'
      intro h
      have h1 : ((Nat.card (ResidueField T.V) : ℕ) : 𝓞 c.F) ∈ (maximalIdeal T.V).comap g := by
        rw [Ideal.mem_comap, map_natCast, ← residue_eq_zero_iff, map_natCast, ← nsmul_one]
        exact card_nsmul_eq_zero'
      rw [h, Ideal.mem_bot] at h1
      exact hc (by exact_mod_cast h1)
    let la : HeightOneSpectrum (𝓞 c.F) := ⟨(maximalIdeal T.V).comap g, Ideal.comap_isPrime _ _, hne⟩
    have hun : ∀ a : 𝓞 c.F, a ∉ la.asIdeal → valV T.V (io (algebraMap (𝓞 c.F) c.F a)) = 1 := fun a ha => by
      rw [← hg, valV_eq_one_iff_isUnit']
      exact notMem_maximalIdeal.1 ha
    have hone : ∀ x : c.F, la.valuation c.F x = 1 → valV T.V (io x) = 1 := fun x hx => by
      obtain ⟨n, d, h⟩ := la.exists_primeCompl_mul_eq_of_integer x hx.le
      have hd : la.valuation c.F (algebraMap (𝓞 c.F) c.F d) = 1 := (la.valuation_eq_one_iff_notMem).2 d.2
      have hn : la.valuation c.F (algebraMap (𝓞 c.F) c.F n) = 1 := by rw [← h, map_mul, hx, hd, _root_.one_mul]
      have h2 := hun n ((la.valuation_eq_one_iff_notMem).1 hn)
      rwa [← h, map_mul, map_mul, hun d d.2, _root_.mul_one] at h2
    obtain ⟨π, hπ⟩ := la.intValuation_exists_uniformizer
    have hπK : la.valuation c.F (algebraMap (𝓞 c.F) c.F π) = WithZero.exp (-1 : ℤ) := by
      rw [HeightOneSpectrum.valuation_of_algebraMap, hπ]
    have hπ0 : algebraMap (𝓞 c.F) c.F π ≠ 0 := fun h => by simp [h] at hπK; exact WithZero.exp_ne_zero hπK.symm
    have hπm : π ∈ la.asIdeal := by
      rw [← la.valuation_lt_one_iff_mem (K := c.F), hπK, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
    have hpos : 0 < vV T.V (io (algebraMap (𝓞 c.F) c.F π)) := by
      rw [← hg]
      refine vV_pos' (fun h => ?_) hπm
      have := hg π
      rw [h, map_zero] at this
      exact (map_ne_zero io).2 hπ0 this.symm
    refine ⟨la, (vV T.V (io (algebraMap (𝓞 c.F) c.F π))).toNat, by omega, fun a => ?_⟩
    rw [Int.toNat_of_nonneg hpos.le]
    by_cases ha : a = 0
    · simp [ha, vV, vLa]
    have hva : la.valuation c.F a ≠ 0 := (Valuation.ne_zero_iff _).2 ha
    have h1 := hone (a * (algebraMap (𝓞 c.F) c.F π) ^ (-vLa la a)) (by
      rw [map_mul, map_zpow₀, hπK, ← WithZero.exp_zsmul, ← WithZero.exp_log hva, ← WithZero.exp_add]
      simp [vLa])
    have h2 := congrArg WithZero.log h1
    rw [map_mul, map_mul, map_zpow₀, map_zpow₀, WithZero.log_mul (valV_ne_zero ((map_ne_zero io).2 ha))
      (zpow_ne_zero _ (valV_ne_zero ((map_ne_zero io).2 hπ0))), WithZero.log_zpow, WithZero.log_one] at h2
    simp only [vV, smul_eq_mul] at h2 ⊢
    linarith

  obtain ⟨la, e, ho⟩ := hex
  have ht := GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c T.Fr y
  have h := hF la _ ⟨PtV.mk (cls := algCls Xo c) la ho ⟨y, ht, hy⟩ hT () trivial, rfl⟩
  exact mem_range_of_nval_nonneg ho.1 h

end GlobalTheory.LamT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RuleValueIntegralOfSupLatticeValuesNonnegStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ruleValue_integral_of_supLattice_values_nonneg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (F : Rul Xo c), (∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v F) → ∀ (T : CDVR) (io : c.F →+* T.Fr), T.FinRes → letI := io.toAlgebra; ∀ y : FrPt Xo c T.Fr, Integral T io y → evR Xo c F y ∈ Set.range (algebraMap T.V T.Fr) := by
  first | exact @GlobalTheory.LamT.evR_mem_range_of_valSet_nonneg | exact GlobalTheory.LamT.evR_mem_range_of_valSet_nonneg | (intros; apply GlobalTheory.LamT.evR_mem_range_of_valSet_nonneg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegralEigenbasisBaseChangeDvr
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegralEigenbasisBaseChangeDvr
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT.LieIntBC

open Matrix
open ReciprocityTheory.ChartRestriction.G.Chart (tvec tmap tvec_inj isTan_tvec univChartLoc tanBC_alg tvec_tmap fB IsUnivChart sp JetR)
open Formalism.L2.Pj.LieRel
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

theorem flat_of_inj {A B : Type} [CommRing A] [IsDomain A] [IsBezout A] [CommRing B] [IsDomain B] [Algebra A B]
    (hi : Function.Injective (algebraMap A B)) : Module.Flat A B := by
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
  rintro x ⟨⟨a, ha⟩, hx⟩
  have hx' : algebraMap A B a * x = 0 := (Algebra.smul_def a x).symm.trans hx
  have ha' : algebraMap A B a ≠ 0 := fun h => nonZeroDivisors.ne_zero ha (hi (h.trans (map_zero _).symm))
  exact (mul_eq_zero.mp hx').resolve_left ha'

theorem eig_flat {V V' : Type} [CommRing V] [IsNoetherianRing V] [CommRing V'] [Algebra V V'] [Module.Flat V V']
    {n m : ℕ} {J : Type} (L : J → (Fin n → V) →ₗ[V] (Fin n → V)) (χ : J → V)
    (L' : J → (Fin n → V') →ₗ[V'] (Fin n → V'))
    (hL : ∀ a c, L' a (algebraMap V V' ∘ c) = algebraMap V V' ∘ L a c)
    (b : Fin m → Fin n → V) (hb : ∀ k a, L a (b k) = χ a • b k)
    (hbb : ∀ c, (∀ a, L a c = χ a • c) → ∃! r : Fin m → V, c = ∑ k, r k • b k)
    (w : Fin n → V') (hw : ∀ a, L' a w = algebraMap V V' (χ a) • w) :
    ∃! r : Fin m → V', w = ∑ k, r k • (algebraMap V V' ∘ b k) := by
  let M : J → Matrix (Fin n) (Fin n) V := fun a => Matrix.of fun j => L a (Pi.single j 1)
  have hM : ∀ a c, c ᵥ* M a = L a c := fun a c => by
    funext j
    rw [LinearMap.pi_apply_eq_sum_univ (L a) c]
    simp only [M, Matrix.vecMul, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.of_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    refine congrArg (fun q => c k * L a q j) ?_
    funext s
    simp [Pi.single_apply, eq_comm]
  have hM' : ∀ a c, c ᵥ* (M a).map (algebraMap V V') = L' a c := fun a c => by
    funext j
    rw [LinearMap.pi_apply_eq_sum_univ (L' a) c]
    simp only [M, Matrix.vecMul, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.of_apply,
      Matrix.map_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    refine (congrFun (hL a (Pi.single k 1)) j).symm.trans ?_
    refine congrArg (fun q => L' a q j) ?_
    funext s
    by_cases h : k = s <;> simp [Pi.single_apply, h, eq_comm]
  refine (GlobalTheory.commonEigenvectors_flat_baseChange V J n m M χ).1 V b (fun k a => (hM a _).trans (hb k a))
    (fun z hz => ?_) V' w (fun a => (hM' a w).trans (hw a))
  simp only [Algebra.algebraMap_self, RingHom.id_apply, RingHom.coe_id, Matrix.map_id] at hz ⊢
  exact hbb z fun a => (hM a z).symm.trans (hz a)

theorem univChart_iso {S : Type} [CommRing S] {G G' : Over (Spec (CommRingCat.of S))} [GrpObj G] [GrpObj G']
    (e : G' ≅ G) [IsMonHom e.hom] {n : ℕ}
    {x : ∀ m : ℕ, sp (R₀ := S) (Chart.JetR S (Fin n) m) ⟶ G} (hx : IsUnivChart G n x) :
    IsUnivChart G' n (fun m => x m ≫ e.inv) := by
  have one : ∀ T : Over (Spec (CommRingCat.of S)), (1 : T ⟶ G') ≫ e.hom = 1 := fun T =>
    map_one (IsMonHom.monoidHom e.hom T)
  have one' : ∀ T : Over (Spec (CommRingCat.of S)), (1 : T ⟶ G) ≫ e.inv = 1 := fun T => by
    rw [← one, Category.assoc, e.hom_inv_id, Category.comp_id]
  refine ⟨fun m => ?_, fun m => ?_, fun A _ _ aug m hm y hy => ?_⟩
  · rw [← Category.assoc, hx.1]
  · rw [← Category.assoc, hx.2.1, one']
  · have := hx.2.2 A aug m hm (y ≫ e.hom) (by rw [← Category.assoc, hy, one])
    simpa only [← Category.assoc, Iso.eq_comp_inv] using this

theorem exists_charts {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S] {G₀ : Over (Sp R)} [GrpObj G₀]
    [Smooth G₀.hom] {G : Over (Sp S)} [GrpObj G] (f : R →+* S) {φ : G.left ⟶ G₀.left}
    (h : IsGrpPullback G G₀ (spMap f) φ) :
    ∃ (n : ℕ) (x : ∀ m : ℕ, sp (R₀ := R) (Chart.JetR R (Fin n) m) ⟶ G₀) (x' : ∀ m : ℕ, sp (R₀ := S) (Chart.JetR S (Fin n) m) ⟶ G),
      IsUnivChart G₀ n x ∧ IsUnivChart G n x' ∧ ∀ c : Fin n → R,
        (tvec (x := x') (f ∘ c)).left ≫ φ = spMap (Formalism.L2.Pj.dualMap f) ≫ (tvec (x := x) c).left := by
  let _ := f.toAlgebra
  obtain ⟨n, x, hx⟩ := univChartLoc G₀
  obtain ⟨x', hx', hc⟩ := tanBC_alg (R' := S) G₀ n x hx
  obtain ⟨e, he, heφ⟩ := grpPullback_iso h (isGrpPullback_pullback G₀ (fB R S))
  refine ⟨n, x, _, hx, univChart_iso e hx', fun c => ?_⟩
  have e1 : tvec (x := fun m => x' m ≫ e.inv) (f ∘ c) = tvec (x := x') (f ∘ c) ≫ e.inv := (Category.assoc _ _ _).symm
  rw [e1, ← heφ, ← Category.assoc, ← Over.comp_left, Category.assoc, e.inv_hom_id, Category.comp_id]
  exact hc c

theorem sp_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R' →+* R'')
    (g : R →+* R') : spMap f ≫ spMap g = spMap (f.comp g) := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

theorem dual_alg {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) :
    spMap (Formalism.L2.Pj.dualMap ψ) ≫ spMap (algebraMap S (DualNumber S)) =
      spMap (algebraMap T (DualNumber T)) ≫ spMap ψ := by
  rw [sp_comp, sp_comp]
  congr 1
  ext s <;> simp [Formalism.L2.Pj.dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dual_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : S →+* T) (g : R →+* S) :
    spMap (Formalism.L2.Pj.dualMap f) ≫ spMap (Formalism.L2.Pj.dualMap g) = spMap (Formalism.L2.Pj.dualMap (f.comp g)) := by
  rw [sp_comp]
  congr 1
  refine RingHom.ext fun s => ?_
  ext <;> simp [Formalism.L2.Pj.dualMap]

end GlobalTheory.LamT.LieIntBC

namespace GlobalTheory.LamT

open LieIntBC Formalism.L2.Pj.LieRel
open ReciprocityTheory.ChartRestriction.G.Chart (tvec tmap tvec_inj isTan_tvec tvec_tmap)

theorem lieInt_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (T T' : CDVR) (ψ : T.V →+* T'.V) (i : T.Fr →+* T'.Fr), (algebraMap T'.V T'.Fr).comp ψ = i.comp (algebraMap T.V T.Fr) → ∀ (x : Sp T.Fr ⟶ Xo.X) (x' : Sp T'.Fr ⟶ Xo.X) (G : PAT H (Sp T.V)) (G' : PAT H (Sp T'.V)) (t : SAB H (Sp T.Fr)) (t' : SAB H (Sp T'.Fr)) (m1 : SABMap t Xo.univ.t x) (m2 : SABMap t G.t (spMap (algebraMap T.V T.Fr))) (m1' : SABMap t' Xo.univ.t x') (m2' : SABMap t' G'.t (spMap (algebraMap T'.V T'.Fr))) (n : SABMap G'.t G.t (spMap ψ)) (n' : SABMap t' t (spMap i)), x' = spMap i ≫ x → m1'.φ = n'.φ ≫ m1.φ → m2'.φ ≫ n.φ = n'.φ ≫ m2.φ → ∀ (io : c.F →+* T.Fr) (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber T.Fr) ⟶ Xo.univ.t.G.left)), LieInt T io m1 m2 u → LieInt T' (i.comp io) m1' m2' (fun τ k => spMap (Formalism.L2.Pj.dualMap i) ≫ u τ k) := by
  intro E _ _ _ H Dw l Xo c T T' ψ i hψ x x' G G' t t' m1 m2 m1' m2' n n' hx h1 h2 io u hu
  obtain ⟨ub, ht, he, hb, hu⟩ := hu
  have := G.t.semi.smooth
  have : ∀ a, IsMonHom (G.t.act.act a) := G.t.act.hom
  have : ∀ a, IsMonHom (G'.t.act.act a) := G'.t.act.hom
  have hψ' : ∀ z, algebraMap T'.V T'.Fr (ψ z) = i (algebraMap T.V T.Fr z) := fun z => RingHom.congr_fun hψ z
  have hinj : Function.Injective ψ := fun a b hab =>
    IsFractionRing.injective T.V T.Fr (i.injective (by rw [← hψ', ← hψ', hab]))
  let _ := ψ.toAlgebra
  have : Module.Flat T.V T'.V := flat_of_inj hinj
  obtain ⟨N, xc, xc', hxc, hxc', hcomp⟩ := exists_charts ψ n.cart
  have hM : ∀ (a : 𝓞 E) (cc : Fin N → T.V),
      tmap hxc' (G'.t.act.act a) (ψ ∘ cc) = ψ ∘ tmap hxc (G.t.act.act a) cc := by
    intro a cc
    apply tvec_inj hxc'
    rw [tvec_tmap hxc']
    refine Over.OverMorphism.ext (n.cart.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
    rw [hcomp, tvec_tmap hxc, Over.comp_left, Over.comp_left, Category.assoc, n.act, ← Category.assoc, hcomp,
      Category.assoc]
  choose χ hχ using fun τ a => int_val c T io τ a
  have hχ' : ∀ τ a, algebraMap T'.V T'.Fr (ψ (χ τ a)) = (i.comp io) (embK c τ a) := fun τ a => by
    rw [hψ', hχ]; rfl
  have eig : ∀ τ cc, IsEigV c io G.t τ (cvV (tvec (x := xc) cc)) ↔
      ∀ a, tmap hxc (G.t.act.act a) cc = χ τ a • cc := fun τ cc =>
    ⟨fun h a => (eigV_iff hxc _ cc _).1 (h a _ (hχ τ a)), fun h a z hz => by
      obtain rfl : z = χ τ a := IsFractionRing.injective T.V T.Fr (hz.trans (hχ τ a).symm)
      exact (eigV_iff hxc _ cc _).2 (h a)⟩
  have eig' : ∀ τ cc, IsEigV c (i.comp io) G'.t τ (cvV (tvec (x := xc') cc)) ↔
      ∀ a, tmap hxc' (G'.t.act.act a) cc = ψ (χ τ a) • cc := fun τ cc =>
    ⟨fun h a => (eigV_iff hxc' _ cc _).1 (h a _ (hχ' τ a)), fun h a z hz => by
      obtain rfl : z = ψ (χ τ a) := IsFractionRing.injective T'.V T'.Fr (hz.trans (hχ' τ a).symm)
      exact (eigV_iff hxc' _ cc _).2 (h a)⟩
  choose b hbe using fun τ k => tan_eq_cvV hxc (ht τ k)
  obtain rfl : ub = fun τ k => cvV (tvec (x := xc) (b τ k)) := funext fun τ => funext fun k => hbe τ k
  have hbe' : ∀ τ k a, tmap hxc (G.t.act.act a) (b τ k) = χ τ a • b τ k := fun τ k => (eig τ _).1 (he τ k)
  refine ⟨fun τ k => cvV (tvec (x := xc') (ψ ∘ b τ k)), fun τ k => isTan_cvV (isTan_tvec hxc' _),
    fun τ k => (eig' τ _).2 fun a => ?_, fun τ w hw hwe => ?_, fun τ k => ?_⟩
  · rw [hM, hbe']
    funext j
    simp
  · obtain ⟨cc, rfl⟩ := tan_eq_cvV hxc' hw
    simp only [comb_iff hxc']
    refine eig_flat (fun a => tmap hxc (G.t.act.act a)) (χ τ) (fun a => tmap hxc' (G'.t.act.act a)) hM (b τ)
      (hbe' τ) (fun z hz => ?_) cc ((eig' τ cc).1 hwe)
    have := hb τ _ (isTan_cvV (isTan_tvec hxc z)) ((eig τ z).2 hz)
    simpa only [comb_iff hxc] using this
  · obtain ⟨u', hu1, hu2⟩ := hu τ k
    have w0 : u' ≫ t.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := by
      have : Mono (spMap (algebraMap T.V T.Fr)) := by
        have : Epi (CommRingCat.ofHom (algebraMap T.V T.Fr)) :=
          IsLocalization.epi (nonZeroDivisors T.V) T.Fr
        exact inferInstanceAs (Mono (Scheme.Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)).op))
      rw [← cancel_mono (spMap (algebraMap T.V T.Fr)), Category.assoc, ← m2.cart.1.w, ← Category.assoc]
      erw [hu2]
      rw [Category.assoc, Over.w]
      exact dual_alg _
    have w1 : (spMap (Formalism.L2.Pj.dualMap i) ≫ u') ≫ t.G.hom =
        spMap (algebraMap T'.Fr (DualNumber T'.Fr)) ≫ spMap i := by
      rw [Category.assoc, w0, dual_alg]
    have l1 : n'.cart.1.lift _ _ w1 ≫ n'.φ = spMap (Formalism.L2.Pj.dualMap i) ≫ u' := n'.cart.1.lift_fst _ _ _
    have l2 := n'.cart.1.lift_snd _ _ w1
    refine ⟨n'.cart.1.lift _ _ w1, ?_, n.cart.1.hom_ext ?_ ?_⟩
    · rw [h1, ← Category.assoc, l1, Category.assoc, hu1]
    · change (_ ≫ m2'.φ) ≫ n.φ = (_ ≫ _) ≫ n.φ
      rw [Category.assoc, h2, ← Category.assoc, l1, Category.assoc, hu2, cvV_left, cvV_left, Category.assoc, hcomp,
        ← Category.assoc, ← Category.assoc, dual_comp, dual_comp, hψ]
    · rw [Category.assoc, m2'.cart.1.w, ← Category.assoc, l2, Category.assoc, Over.w]
      exact (dual_alg _).symm

end GlobalTheory.LamT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegralEigenbasisBaseChangeDvrStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_eigenbasis_baseChange_dvr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (T T' : CDVR) (ψ : T.V →+* T'.V) (i : T.Fr →+* T'.Fr), (algebraMap T'.V T'.Fr).comp ψ = i.comp (algebraMap T.V T.Fr) → ∀ (x : Sp T.Fr ⟶ Xo.X) (x' : Sp T'.Fr ⟶ Xo.X) (G : PAT H (Sp T.V)) (G' : PAT H (Sp T'.V)) (t : SAB H (Sp T.Fr)) (t' : SAB H (Sp T'.Fr)) (m1 : SABMap t Xo.univ.t x) (m2 : SABMap t G.t (spMap (algebraMap T.V T.Fr))) (m1' : SABMap t' Xo.univ.t x') (m2' : SABMap t' G'.t (spMap (algebraMap T'.V T'.Fr))) (n : SABMap G'.t G.t (spMap ψ)) (n' : SABMap t' t (spMap i)), x' = spMap i ≫ x → m1'.φ = n'.φ ≫ m1.φ → m2'.φ ≫ n.φ = n'.φ ≫ m2.φ → ∀ (io : c.F →+* T.Fr) (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber T.Fr) ⟶ Xo.univ.t.G.left)), LieInt T io m1 m2 u → LieInt T' (i.comp io) m1' m2' (fun τ k => spMap (Formalism.L2.Pj.dualMap i) ≫ u τ k) := by
  first | exact @GlobalTheory.LamT.lieInt_baseChange | exact GlobalTheory.LamT.lieInt_baseChange | (intros; apply GlobalTheory.LamT.lieInt_baseChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LocalLowerBoundCmPointFramePolynomialEveryPrime
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT.LocClause

theorem exists_isLocGen {K : Type} [Field K] [NumberField K] (p : HeightOneSpectrum (𝓞 K))
    (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : ∃ c : K, IsLocGen p c I := by
  obtain ⟨π, hπ⟩ := p.valuation_exists_uniformizer K
  refine ⟨π ^ FractionalIdeal.count K p I, (GlobalTheory.LamF.isLocGen_iff_valuation_eq p _ _).2 ?_⟩
  rw [map_zpow₀, hπ, ← WithZero.exp_zsmul]
  simp

theorem map_evalFr {B : Type} {m : B → ℕ} {R S : Type} [CommRing R] [CommRing S] (κ : R →+* S)
    (P : MvPolynomial (FrVar m) R) (Y : ∀ b, Matrix (Fin (m b)) (Fin (m b)) R) :
    κ (evalFr P Y) = evalFr (MvPolynomial.map κ P) (fun b => (Y b).map κ) := by
  unfold evalFr
  induction P using MvPolynomial.induction_on <;> simp_all

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem secBC_one_of_frMap {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] {φ : S →ₐ[c.F] T}
    {y : FrPt Xo c S} {y' : FrPt Xo c T} (h : FrMap φ y y') : SecBC φ.toRingHom 1 y.x y'.x y.s y'.s := by
  obtain ⟨-, -, pm, h₁, h₂, h₃⟩ := h
  refine ⟨pm, h₁, h₂, fun i hi => Eq.trans (congrArg _ ?_) (h₃ i hi)⟩
  have h1 := ((GlobalTheory.Frames.SecCalc.sec_calc E H Dw l Xo S S S (RingHom.id S) (RingHom.id S) y.x y.x y.x
    (by simp [spMap]) (by simp [spMap])).2.2.2 1 1 i).2.2
  rw [h1, _root_.one_mul]

theorem evR_scale {S : Type} [Field S] [Algebra c.F S] {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {F : Rul Xo c}
    (hF : F ∈ sec Xo c a n) (s : Sˣ) {y y' : FrPt Xo c S} (h : FrChg (fun _ => 1) (s : S) y y') :
    evR Xo c F y' = (s : S) ^ n * evR Xo c F y := by
  let t : Ix Dw → Sˣ := fun i => i.elim s (fun _ => 1)
  have hb : FrBor t y y' := ((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c S y y' y').1 t).2
    ⟨fun _ => 1, fun τ i j hij => Matrix.one_apply_ne hij.ne, fun τ i => by simp [t], h⟩
  rw [(GlobalTheory.Frames.algebraic_laws GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c).2.2.2.2.2.2 S inferInstance a n F hF t y y' hb]
  congr 1
  simp [wchar, Fintype.prod_option, t, ex]

theorem integral_of_eq (T : CDVR) (io : c.F →+* T.Fr) (y : letI := io.toAlgebra; FrPt Xo c T.Fr)
    {G : SAB H (Sp T.V)} {t' : SAB H (Sp T.Fr)} {x : Sp T.Fr ⟶ Xo.X} :
    letI := io.toAlgebra
    y.x = x → ∀ (m1 : SABMap t' Xo.univ.t x) (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr))),
      LieInt T io m1 m2 y.u → SecInt T m1 m2 y.s → Integral T io y := by
  intro h
  subst h
  exact integral_of T io y

theorem secInt_baseChange (T T' : CDVR) (ψ : T.V →+* T'.V) (i : T.Fr →+* T'.Fr)
    (hψ : (algebraMap T'.V T'.Fr).comp ψ = i.comp (algebraMap T.V T.Fr))
    {x x₁ : Sp T.Fr ⟶ Xo.X} {x' x₁' : Sp T'.Fr ⟶ Xo.X} {G : PAT H (Sp T.V)} {G' : PAT H (Sp T'.V)}
    {t : SAB H (Sp T.Fr)} {t' : SAB H (Sp T'.Fr)} (m1 : SABMap t Xo.univ.t x)
    (m2 : SABMap t G.t (spMap (algebraMap T.V T.Fr))) (m1' : SABMap t' Xo.univ.t x')
    (m2' : SABMap t' G'.t (spMap (algebraMap T'.V T'.Fr))) (n : SABMap G'.t G.t (spMap ψ))
    (n' : SABMap t' t (spMap i)) (hx : x' = spMap i ≫ x) (h1 : m1'.φ = n'.φ ≫ m1.φ)
    (h2 : m2'.φ ≫ n.φ = n'.φ ≫ m2.φ) (e : x₁ = x) (e' : x₁' = x') (s : LB.Sec (PPx x₁)) (s' : LB.Sec (PPx x₁'))
    (hs : SecBC i 1 x₁ x₁' s s') (h : SecInt T m1 m2 s) : SecInt T' m1' m2' s' := by
  subst e e'
  exact GlobalTheory.T.integral_generator_baseChange_valuationRing E H Dw l Xo T T' ψ i hψ _ _ G G' t t' m1 m2 m1' m2' n n' hx h1 h2 s s' hs h

theorem integral_baseChange_chg [StarRing (𝓞 E)] (z : CMPt Xo c) (T T' : CDVR) (iK : z.K →+* T.Fr)
    (M : LocMod z T iK) (ψ : T.V →+* T'.V) (i : T.Fr →+* T'.Fr)
    (hψ : (algebraMap T'.V T'.Fr).comp ψ = i.comp (algebraMap T.V T.Fr)) (io : c.F →+* T.Fr) :
    letI := io.toAlgebra
    letI := (i.comp io).toAlgebra
    ∀ (iA : T.Fr →ₐ[c.F] T'.Fr) (y : FrPt Xo c T.Fr) (y' w : FrPt Xo c T'.Fr)
      (X : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) T'.V),
      iA.toRingHom = i → y.x = spMap iK ≫ z.x → LieInt T io M.m1 M.m2 y.u → SecInt T M.m1 M.m2 y.s →
      FrMap iA y y' → (∀ b, IsUnit (X b).det) → FrChg (fun b => (X b).map (algebraMap T'.V T'.Fr)) 1 y' w →
      Integral T' (i.comp io) w := by
  letI := io.toAlgebra
  letI := (i.comp io).toAlgebra
  intro iA y y' w X hi hy hL hS hm hX hw
  obtain ⟨M', n, n', h1, h2⟩ := (GlobalTheory.T.exists_cmPoint_localModel_over_dvr E H Dw l Xo c z T iK).2 M T' ψ i hψ
  have hx : spMap (i.comp iK) ≫ z.x = spMap i ≫ spMap iK ≫ z.x := by
    rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp, Category.assoc]
  have hy' : y'.x = spMap (i.comp iK) ≫ z.x := by rw [hm.1, hi, hy, hx]
  have hL' : LieInt T' (i.comp io) M'.m1 M'.m2 y'.u := by
    have := GlobalTheory.T.integral_eigenbasis_baseChange_dvr E H Dw l Xo c T T' ψ i hψ _ _ M.G M'.G M.t'.t M'.t'.t M.m1 M.m2 M'.m1 M'.m2 n n' hx h1 h2
      io y.u hL
    have hu : y'.u = fun τ k => spMap (Formalism.L2.Pj.dualMap i) ≫ y.u τ k := by
      funext τ k
      rw [hm.2.1 τ k, hi]
    rw [hu]
    exact this
  have hLw : LieInt T' (i.comp io) M'.m1 M'.m2 w.u :=
    (GlobalTheory.T.exists_integralEigenbasis_of_frame_at_localModel E H Dw l Xo c T' (i.comp io) M'.G.t M'.t'.t _ M'.m1 M'.m2 y' hy').2 hL' X 1 w hX hw
  have hs1 : SecBC i 1 y.x y'.x y.s y'.s := by
    have := secBC_one_of_frMap hm
    rwa [hi] at this
  have hs2 : SecBC i 1 y.x w.x y.s w.s := by
    have := ((GlobalTheory.Frames.SecCalc.sec_calc E H Dw l Xo _ _ _ i (RingHom.id _) y.x y'.x w.x
      (by rw [hm.1, hi]) (by rw [hw.1]; simp [spMap])).1 1 _ _ _ hs1).1 hw.2.2
    rwa [RingHom.id_comp] at this
  have hwx : w.x = spMap (i.comp iK) ≫ z.x := hw.1.trans hy'
  exact integral_of_eq T' (i.comp io) w hwx M'.m1 M'.m2 hLw
    (secInt_baseChange T T' ψ i hψ M.m1 M.m2 M'.m1 M'.m2 n n' hx h1 h2 hy hwx _ _ hs2 hS)

theorem evR_chg {K S : Type} [Field K] [Algebra c.F K] [Field S] [Algebra c.F S] {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    {F : Rul Xo c} (hF : F ∈ sec Xo c a n) {y₀ : FrPt Xo c K} {G : MvPolynomial (FrVar Dw.mult) K}
    (hG : IsFrPoly F y₀ G) (φ : K →ₐ[c.F] S) {y y' w : FrPt Xo c S} (hy : FrMap φ y₀ y)
    {g X Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) S} {s : S} (hs : s ≠ 0)
    (hY : ∀ b, IsUnit (Y b).det) (hXY : ∀ b, (Y b).transpose = X b * g b)
    (h : FrChg g s y y') (hw : FrChg X 1 y' w) :
    evR Xo c F w = s ^ n * evalFr (MvPolynomial.map φ.toRingHom G) Y := by
  have hYt : ∀ b, IsUnit ((Y b).transpose).det := fun b => by rw [Matrix.det_transpose]; exact hY b
  obtain ⟨w₀, hw₀, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c S y (fun b => (Y b).transpose) 1 hYt
  obtain ⟨w₁, hw₁, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c S w₀ (fun _ => 1) (Units.mk0 s hs)
    (fun _ => by simp)
  have c1 := (GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c S y w₀ w₁).2 _ _ _ _ hw₀ hw₁
  have c2 := (GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c S y y' w).2 _ _ _ _ h hw
  have e : w₁ = w := by
    refine (GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c S y (fun b => (Y b).transpose) (Units.mk0 s hs) hYt).unique
      ?_ ?_
    · simpa using c1
    · simpa [hXY] using c2
  rw [← e, evR_scale hF _ hw₁, hG S φ y w₀ Y hY hy hw₀]
  rfl

theorem step5Loc_cmPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ F ∈ sec Xo c a n, (∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v F) → ∀ G : MvPolynomial (FrVar Dw.mult) z.K, IsFrPoly F z.y G → ∀ p, Step5Loc z.e z.Tl.dual z.LamL z.ℓ z.U G n p := by
  intro E _ _ _ H Dw l Xo c _ z f La hz a n F hF hv G hG p
  obtain ⟨ca, hca⟩ := exists_isLocGen p z.Tl.I
  obtain ⟨cd, hcd⟩ := exists_isLocGen p z.LamL.I
  choose cl hcl using fun j => exists_isLocGen p (z.ℓ j).I
  refine ⟨ca⁻¹, cd, cl, isLocGen_inv hca, hcd, hcl,
    GlobalTheory.LamF.letters_det_valuation_le E H l c _ _ f z.obj La hz.1 z.letters hz.2.1 p cd cl hcd hcl, ?_⟩
  obtain ⟨T, iK, hT, hiK⟩ := GlobalTheory.T.exists_completeDVR_completion_integral_iff z.K p
  obtain ⟨M⟩ := (GlobalTheory.T.exists_cmPoint_localModel_over_dvr E H Dw l Xo c z T iK).1 fun a => (hiK _).2 (p.valuation_le_one a)
  let io : c.F →+* T.Fr := iK.comp (algebraMap c.F z.K)
  letI := io.toAlgebra
  let φ : z.K →ₐ[c.F] T.Fr := { iK with commutes' := fun _ => rfl }
  obtain ⟨yT, hyT⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c _ _ φ z.y
  have hyx : yT.x = spMap iK ≫ z.x := by rw [hyT.1, hz.2.2.2.1]
  obtain ⟨g, hg, hgL⟩ := (GlobalTheory.T.exists_integralEigenbasis_of_frame_at_localModel E H Dw l Xo c T io M.G.t M.t'.t _ M.m1 M.m2 yT hyx).1
  obtain ⟨s, hsS⟩ := GlobalTheory.T.exists_unit_integral_generator_principal_local_model E H Dw l Xo c T io M.G M.t'.t _ M.m1 M.m2 yT hyx
  obtain ⟨y', hy', -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c T.Fr yT g s hg
  have hL := hgL _ _ hy'
  have hS := hsS _ _ hy'
  obtain ⟨u, hu⟩ := GlobalTheory.T.integralGenerator_associated_localGenerator_CM_line E H Dw l Xo c z f La hz p T iK M hiK φ yT y' g s rfl hyT hy' hS ca hca
  refine ⟨T.V, T.Fr, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, iK,
    fun b => (g b)⁻¹, inferInstance, hT, hiK, fun b => (Matrix.isUnit_nonsing_inv_det _ (hg b)).ne_zero,
    fun b j k => GlobalTheory.T.lieLetter_integral_in_integral_eigenbasis E H Dw l Xo c z f La hz p T iK M hiK φ yT y' g s rfl hyT hy' hg hL b j k _ (hcl _), ?_⟩
  intro W KW _ _ _ _ _ _ _ fW hW hWf _ hfW Y X hX hXY
  have hinj : Function.Injective (algebraMap T.V W) := by
    intro x y h
    apply IsFractionRing.injective T.V T.Fr
    apply fW.injective
    rw [hfW, hfW, h]
  haveI : CharZero W := charZero_of_injective_ringHom hinj
  let T' : CDVR := ⟨W⟩
  let κ : KW →+* T'.Fr := ((FractionRing.algEquiv W KW).symm : KW ≃ₐ[W] FractionRing W).toRingEquiv.toRingHom
  have hκ : ∀ w : W, κ (algebraMap W KW w) = algebraMap T'.V T'.Fr w := fun w =>
    (FractionRing.algEquiv W KW).symm.commutes w
  let i : T.Fr →+* T'.Fr := κ.comp fW
  have hψ : (algebraMap T'.V T'.Fr).comp (algebraMap T.V W) = i.comp (algebraMap T.V T.Fr) := by
    ext x
    show _ = κ (fW _)
    rw [hfW, hκ]
    rfl
  letI := (i.comp io).toAlgebra
  let iA : T.Fr →ₐ[c.F] T'.Fr := { i with commutes' := fun _ => rfl }
  obtain ⟨yW, hyW⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c _ _ iA yT
  obtain ⟨y'', hy''⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c _ _ iA y'
  have hc := (GlobalTheory.Frames.ChgBC.frChg_baseChange E H Dw l Xo c _ _ iA yT y' yW y'' g s hy' hyW).1 hy''
  have hXt : ∀ b, IsUnit ((X b).transpose : Matrix _ _ T'.V).det := fun b => by
    rw [Matrix.det_transpose]; exact hX b
  have hXu : ∀ b, IsUnit (((X b).transpose : Matrix _ _ T'.V).map (algebraMap T'.V T'.Fr)).det := fun b => by
    have := (hXt b).map (algebraMap T'.V T'.Fr)
    rwa [RingHom.map_det] at this
  obtain ⟨w, hw, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c T'.Fr y'' _ 1 hXu
  have hint := integral_baseChange_chg z T T' iK M (algebraMap T.V W) i hψ io iA y' y'' w
    (fun b => (X b).transpose) rfl (hy'.1.trans hyx) hL hS hy'' hXt hw
  obtain ⟨w₀, hw₀⟩ := GlobalTheory.T.ruleValue_integral_of_supLattice_values_nonneg E H Dw l Xo c F hv T' (i.comp io) hWf w hint
  have hYX : ∀ b, (Y b).transpose = ((X b).map (algebraMap W KW)).transpose * (g b).map fW := fun b => by
    rw [← hXY b, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc, ← Matrix.map_mul,
      Matrix.nonsing_inv_mul _ (hg b)]
    simp
  have hYX' : ∀ b, ((Y b).map κ).transpose =
      ((X b).transpose : Matrix _ _ T'.V).map (algebraMap T'.V T'.Fr) * (g b).map iA := fun b => by
    rw [← Matrix.transpose_map, hYX b, Matrix.map_mul]
    congr 1
    ext j k
    exact hκ _
  have hYu : ∀ b, IsUnit ((Y b).map κ).det := fun b => by
    rw [← Matrix.det_transpose, hYX' b, Matrix.det_mul]
    refine (hXu b).mul ?_
    have := (hg b).map i
    rwa [RingHom.map_det] at this
  have hval := evR_chg hF hG (iA.comp φ) (ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans φ iA hyT hyW)
    ((map_ne_zero iA).2 s.ne_zero) hYu hYX' hc hw
  refine ⟨algebraMap T.V W ↑u⁻¹ ^ n * w₀, κ.injective ?_⟩
  have hP : MvPolynomial.map κ (MvPolynomial.map fW (MvPolynomial.map iK G)) =
      MvPolynomial.map (iA.comp φ).toRingHom G := by
    rw [MvPolynomial.map_map, MvPolynomial.map_map]
    rfl
  have hsn : (iA s : T'.Fr) ≠ 0 := (map_ne_zero iA).2 s.ne_zero
  have hu' : κ (fW (iK ca⁻¹)) * κ (algebraMap W KW (algebraMap T.V W ↑u⁻¹)) * iA s = 1 := by
    rw [← hfW]
    show i _ * i _ * i _ = 1
    rw [← map_mul, ← map_mul, hu, map_inv₀, _root_.mul_mul_mul_comm, inv_mul_cancel₀ ((map_ne_zero iK).2 hca.1),
      ← map_mul, Units.inv_mul, map_one, _root_.one_mul, map_one]
  rw [map_evalFr, hP]
  simp only [map_mul, map_pow]
  rw [hκ w₀, hw₀, hval, ← _root_.mul_assoc, ← _root_.mul_assoc, ← mul_pow, ← mul_pow, hu', one_pow, _root_.one_mul]

end GlobalTheory.LamT.LocClause
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LocalLowerBoundCmPointFramePolynomialEveryPrimeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localLowerBound_cmPoint_framePolynomial_every_prime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ F ∈ sec Xo c a n, (∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v F) → ∀ G : MvPolynomial (FrVar Dw.mult) z.K, IsFrPoly F z.y G → ∀ p, Step5Loc z.e z.Tl.dual z.LamL z.ℓ z.U G n p := by
  first | exact @GlobalTheory.LamT.LocClause.step5Loc_cmPt | exact GlobalTheory.LamT.LocClause.step5Loc_cmPt | (intros; apply GlobalTheory.LamT.LocClause.step5Loc_cmPt <;> assumption)
end
