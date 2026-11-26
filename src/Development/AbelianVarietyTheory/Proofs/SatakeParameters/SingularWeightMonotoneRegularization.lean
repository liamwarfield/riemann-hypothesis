module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSolvableCmExtensionSplitPlace

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SingularWeightMonotoneRegularization
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open Neutral.B1 hiding G Dec IsPlaceOver
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RoadU.CharSupport

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem charPol_seg {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a}
    {rc : IrrGL (k := w.adicCompletion E) → WD h} (H : UpperTheory.Zero.LLC.LawsT a ha rc) (Δ : Segment (w.adicCompletion E))
    (σ : Weil h) :
    (((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp (h := h) Δ.len)).charPol σ
      = (Δ.ms.map fun y => (rc y).charPol σ).prod := by
  rw [(GlobalTheory.WeilDeligne.charPol_lpTw_lpChar_lpSp E Ω A w h (rc Δ.first)).2 Δ.len σ, Segment.ms, Multiset.map_map]
  have h1 : ∀ j : Fin Δ.len, (rc (Δ.term j)).charPol σ = ((rc Δ.first).lpTw ((j : ℕ) : ℝ)).charPol σ := by
    intro j
    rw [Segment.term, show (((j : ℕ) : ℂ)) = ((((j : ℕ) : ℝ)) : ℂ) by push_cast; rfl, H.nu]
  change _ = ∏ j : Fin Δ.len, (fun y => (rc y).charPol σ) (Δ.term j)
  simp only [h1]
  rw [Fin.prod_univ_eq_prod_range (fun j => ((rc Δ.first).lpTw (j : ℝ)).charPol σ) Δ.len]
  rfl

end GlobalTheory.RoadU.CharSupport

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RcUnlinkedChars
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open Neutral.B1 hiding G Dec IsPlaceOver
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RoadU.UnlinkedChars

theorem rc_unlinked_chars : Inputs → ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [Algebra E Ω] [IsAlgClosure E Ω] (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w), ∀ (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (rc : IrrGL (k := w.adicCompletion E) → WD h), UpperTheory.Zero.LLC.LawsT a ha rc → ∀ (x : IrrGL (k := w.adicCompletion E)) (n : ℕ), ∀ (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)), HasSupport x.rep (chars ξ hξ) → Unlinked (chars ξ hξ) → (rc x).mono0 ∧ ∀ g : Weil h, (rc x).charPol g = ∏ j, (X - C ((ξ j (a g) : ℂˣ) : ℂ)) := by
  intro hI Ω _ E _ _ _ _ w A h a ha rc H x n ξ hξ hs hu
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨𝔪, hm⟩ := hI.exh (w.adicCompletion E) x
  have hs' : HasSupport x.rep (msupp 𝔪) := GlobalTheory.LocGL.hasSupport_msupp_of_isL hI.zel _ 𝔪 x hm
  have he : chars ξ hξ = msupp 𝔪 :=
    GlobalTheory.LocGL.SupportUnique.hasSupport_unique GlobalTheory.RecT.geometricLemma_holds GlobalTheory.bernsteinZelevinskyFiniteness_holds
      hI.zel _ x _ _ hs hs'
  have hL := H.langlands 𝔪.toList x (by rw [Multiset.coe_toList]; exact hm)
  have hmem : ∀ Δ ∈ 𝔪, ∀ i : Fin Δ.len, Δ.term i ∈ chars ξ hξ := fun Δ hΔ i => by
    rw [he, msupp]
    exact Multiset.mem_bind.2 ⟨Δ, hΔ, Multiset.mem_map.2 ⟨i, Finset.mem_univ_val _, rfl⟩⟩

  have hlen : ∀ Δ ∈ 𝔪, Δ.len = 1 := by
    intro Δ hΔ
    by_contra hne
    have h2 : 1 < Δ.len := lt_of_le_of_ne Δ.len_pos (Ne.symm hne)
    refine hu _ (hmem Δ hΔ ⟨1, h2⟩) _ (hmem Δ hΔ ⟨0, Δ.len_pos⟩) ?_
    simp only [Segment.term, IrrGL.nu_nu]
    norm_num
  have hms : ∀ Δ ∈ 𝔪, Δ.ms = {Δ.first} := by
    intro Δ hΔ
    have e : Δ = Segment.single Δ.first Δ.isCusp_first := Segment.ext_first rfl (by rw [hlen Δ hΔ]; rfl)
    rw [e, Segment.ms_single]
    rfl
  have hsupp : msupp 𝔪 = 𝔪.map Segment.first := by
    rw [msupp, ← Multiset.bind_singleton]
    exact Multiset.bind_congr hms
  have hchar : ∀ y ∈ chars ξ hξ, ∃ j, y = IrrGL.ofChar (ξ j) (hξ j) := fun y hy => by
    obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hy
    exact ⟨j, rfl⟩
  have hfirst : ∀ Δ ∈ 𝔪, ∃ j, Δ.first = IrrGL.ofChar (ξ j) (hξ j) := fun Δ hΔ =>
    hchar _ (by rw [he, hsupp]; exact Multiset.mem_map_of_mem _ hΔ)
  have hsum : rc x = sumList (𝔪.toList.map fun Δ => rc Δ.first) := by
    rw [hL, segSum]
    congr 1
    apply List.map_congr_left
    intro Δ hΔ
    rw [hlen Δ (Multiset.mem_toList.1 hΔ)]
    simp only [Nat.cast_one, sub_self, zero_div]
    exact (GlobalTheory.WeilDeligne.charPol_lpTw_lpChar_lpSp E Ω A w h _).1
  have hpol1 : ∀ j (g : Weil h), (rc (IrrGL.ofChar (ξ j) (hξ j))).charPol g = X - C ((ξ j (a g) : ℂˣ) : ℂ) := by
    intro j g
    rw [H.one, WD.lpOfChar, WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd]
    simp
  refine ⟨?_, fun g => ?_⟩
  · rw [hsum]
    have key : ∀ L : List (Segment (w.adicCompletion E)), (∀ Δ ∈ L, Δ ∈ 𝔪) →
        (sumList (L.map fun Δ => rc Δ.first)).mono0 := by
      intro L
      induction L with
      | nil =>
        intro _
        show (WD.lpZero (h := h)).mono0
        exact (WD.monodromyZero_ofWeilDeligneRepClass_iff _).2 rfl
      | cons Δ L ih =>
        intro hL'
        obtain ⟨j, hj⟩ := hfirst Δ (hL' Δ List.mem_cons_self)
        show (WD.lpSum _ _).mono0
        refine (WD.monomial_sum_iff _ _).2 ⟨?_, ih fun Δ' h' => hL' Δ' (List.mem_cons_of_mem _ h')⟩
        change (rc Δ.first).mono0
        rw [hj]
        exact WD.mono0_of_lpDim_eq_one (by rw [H.dim]; rfl)
    exact key _ fun Δ hΔ => Multiset.mem_toList.1 hΔ
  · rw [hsum, GlobalTheory.LocLanglands.CuspExt.charPol_sumList, List.map_map]
    have r1 : (∏ j, (X - C ((ξ j (a g) : ℂˣ) : ℂ))) = ((chars ξ hξ).map fun y => (rc y).charPol g).prod := by
      rw [chars, Multiset.map_map, Finset.prod_eq_multiset_prod]
      exact congrArg Multiset.prod (Multiset.map_congr rfl fun j _ => (hpol1 j g).symm)
    rw [r1, he, hsupp, Multiset.map_map, ← Multiset.prod_coe, ← Multiset.map_coe, Multiset.coe_toList]
    rfl

end GlobalTheory.RoadU.UnlinkedChars
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiAMemRange
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

noncomputable section

namespace GlobalTheory.TwV.Xc.OrdA

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n p : ℕ} {G : GAtP p}

theorem phiA_mem_range (A : LocAt F E n G) (hI : LocInt A) (hS : SplAlg A) (v : Fin G.P.nV)
    {x : AfE F E} (hx : x ∈ RInt F E) : phiA A v x ∈ (algebraMap (G.P.W v) (G.P.Qq v)).range := by
  haveI := (G.P.setting v).frac_alt
  have key : RInt F E ≤ (algebraMap (G.P.W v) (G.P.Qq v)).range.comap (phiA A v) := by
    show Subring.closure _ ≤ _
    rw [Subring.closure_le]
    rintro _ (⟨⟨e, he⟩, rfl⟩ | ⟨⟨c, hc⟩, rfl⟩)
    · obtain ⟨a, rfl⟩ := he
      show phiA A v ((algebraMap (𝓞 E) E a) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) ∈ (algebraMap (G.P.W v) (G.P.Qq v)).range
      rw [phiA_incl]
      have hint : IsIntegral ℤ (A.iw v (algebraMap (𝓞 E) E a)) :=
        (RingOfIntegers.isIntegral_coe a).map (A.iw v).toIntAlgHom
      obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 (hint.tower_top (A := G.P.W v))
      exact ⟨y, hy⟩
    · show phiA A v ((1 : E) ⊗ₜ[F] c) ∈ (algebraMap (G.P.W v) (G.P.Qq v)).range
      have h1 : phiA A v ((1 : E) ⊗ₜ[F] c) = (A.eQ v).symm (c (A.pl v).1) := by
        have h2 : prV (E := E) (A.pl v).1 ((1 : E) ⊗ₜ[F] c) = (1 : E) ⊗ₜ[F] c (A.pl v).1 := rfl
        have h3 : A.ph v ((1 : E) ⊗ₜ[F] c (A.pl v).1) = c (A.pl v).1 := by
          show (A.spl v ((1 : E) ⊗ₜ[F] c (A.pl v).1)).1 = _
          rw [hS v]
        show (A.eQ v).symm (A.ph v (prV (E := E) (A.pl v).1 ((1 : E) ⊗ₜ[F] c))) = _
        rw [h2, h3]
      rw [h1]
      exact (hI v _).2 (by rw [RingEquiv.apply_symm_apply]; exact hc (A.pl v).1)
  exact key hx

theorem phiA_intU (A : LocAt F E n G) (hI : LocInt A) (hS : SplAlg A) (v : Fin G.P.nV) {k : (AfE F E)ˣ}
    (hk : k ∈ intU F E) : ∃ u : (G.P.W v)ˣ, phiA A v (k : AfE F E) = algebraMap (G.P.W v) (G.P.Qq v) u := by
  haveI := (G.P.setting v).frac_alt
  obtain ⟨a, ha⟩ := phiA_mem_range A hI hS v (x := (k : AfE F E)) hk.1
  obtain ⟨b, hb⟩ := phiA_mem_range A hI hS v (x := ((k⁻¹ : (AfE F E)ˣ) : AfE F E)) hk.2
  have hab : a * b = 1 := by
    apply IsFractionRing.injective (G.P.W v) (G.P.Qq v)
    rw [map_mul, ha, hb, ← map_mul, Units.mul_inv, map_one, map_one]
  exact ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, ha.symm⟩

theorem ordA_mul (A : LocAt F E n G) (v : Fin G.P.nV) (x y : (AfE F E)ˣ) :
    ordA A v (x * y) = ordA A v x + ordA A v y := by
  haveI := (G.P.setting v).frac_alt
  have hp := (G.P.setting v).p_unif
  obtain ⟨a, u, ha⟩ := exists_eq_unit_mul_zpow₂ hp (x.isUnit.map (phiA A v)).ne_zero
  obtain ⟨b, u', hb⟩ := exists_eq_unit_mul_zpow₂ hp (y.isUnit.map (phiA A v)).ne_zero
  unfold ordA
  rw [Units.val_mul, map_mul, ha, hb, ordP_eq hp, ordP_eq hp, ← ordP_eq (Qq := G.P.Qq v) hp (a + b) (u * u')]
  congr 1
  rw [zpow_add₀ (pQ_ne hp), Units.val_mul, map_mul]; ring

theorem ordP_unit (v : Fin G.P.nV) (u : (G.P.W v)ˣ) :
    ordP (G.P.W v) p (algebraMap (G.P.W v) (G.P.Qq v) u) = 0 := by
  haveI := (G.P.setting v).frac_alt
  have := ordP_eq (Qq := G.P.Qq v) (G.P.setting v).p_unif 0 u
  simpa using this

theorem ordA_props : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n p : ℕ) [Fact p.Prime]
    (G : GAtP p) (A : LocAt F E n G), LocInt A → SplAlg A → ∀ v, (∀ x y, ordA A v (x * y) = ordA A v x + ordA A v y) ∧
    (∀ k ∈ intU F E, ordA A v k = 0) ∧ (∀ z : Eˣ, ordA A v (ratId F E z) = ordP (G.P.W v) p (A.iw v (z : E))) ∧
    ∀ v', v' ≠ v → ∀ x, OneOff (A.pl v').1 x → ordA A v x = 0 := by
  intro F E _ _ _ _ _ n p _ G A hI hS v
  refine ⟨ordA_mul A v, fun k hk => ?_, fun z => ?_, fun v' hv x hx => ?_⟩
  · obtain ⟨u, hu⟩ := phiA_intU A hI hS v hk
    unfold ordA
    rw [hu]
    exact ordP_unit v u
  · unfold ordA
    rw [← phiA_incl A v (z : E)]
    rfl
  · have hne : (A.pl v).1 ≠ (A.pl v').1 := fun h => hv (A.pl.injective (Subtype.ext h)).symm
    have h1 : phiA A v (x : AfE F E) = 1 := by
      simp only [phiA, RingHom.comp_apply, hx _ hne, map_one]
    unfold ordA
    rw [h1, ← map_one (algebraMap (G.P.W v) (G.P.Qq v)), ← Units.val_one]
    exact ordP_unit v 1

end GlobalTheory.TwV.Xc.OrdA
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralAtOfComponentZeroUnderPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralAtOfComponentZeroUnderPrime
open NumberField IsDedekindDomain Formalism.UG Formalism.L2.Col
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.VanishAwayInt

theorem exists_away {F : Type} [Field F] [NumberField F] (p : Ideal (𝓞 F)) [hp : p.IsPrime] (N : 𝓞 F) (hN : N ≠ 0) :
    ∃ t : 𝓞 F, t ∉ p ∧ ∀ w : HeightOneSpectrum (𝓞 F), w.asIdeal ≠ p →
      ∃ c y : 𝓞 F, y ∉ w.asIdeal ∧ y * t = N * c := by
  classical
  have hI : Ideal.span {N} ≠ ⊥ := by simpa using hN
  have hpu : ¬ IsUnit p := by
    rw [Ideal.isUnit_iff]; exact hp.ne_top
  obtain ⟨b, hb, hnd⟩ := (FiniteMultiplicity.of_not_isUnit hpu hI).exists_eq_pow_mul_and_not_dvd
  have hbp : ¬ b ≤ p := fun h => hnd (Ideal.dvd_iff_le.2 h)
  obtain ⟨t, htb, htp⟩ := SetLike.not_le_iff_exists.1 hbp
  refine ⟨t, htp, fun w hw => ?_⟩
  have hpw : ¬ p ^ multiplicity p (Ideal.span {N}) ≤ w.asIdeal := by
    intro h
    rcases Nat.eq_zero_or_pos (multiplicity p (Ideal.span {N})) with h0 | hm
    · rw [h0, pow_zero, Ideal.one_eq_top, top_le_iff] at h
      exact w.isPrime.ne_top h
    · have hle : p ≤ w.asIdeal := w.isPrime.le_of_pow_le h
      have hpb : p ≠ ⊥ := by
        intro h'
        apply hI
        rw [eq_bot_iff]
        calc Ideal.span {N} = p ^ multiplicity p (Ideal.span {N}) * b := hb
          _ ≤ p ^ multiplicity p (Ideal.span {N}) := Ideal.mul_le_left
          _ ≤ p := Ideal.pow_le_self hm.ne'
          _ = ⊥ := h'
      have hmax : p.IsMaximal := hp.isMaximal hpb
      exact hw (hmax.eq_of_le w.isPrime.ne_top hle).symm
  obtain ⟨y, hy, hyw⟩ := SetLike.not_le_iff_exists.1 hpw
  have hyt : y * t ∈ Ideal.span {N} := by
    rw [hb]; exact Ideal.mul_mem_mul hy htb
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hyt
  exact ⟨c, y, hyw, by rw [← hc, mul_comm]⟩

theorem intAtA_of_prV_eq_zero : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : HeightOneSpectrum (𝓞 E)) (z : E ⊗[F] FiniteAdeleRing (𝓞 F) F),
    (∀ v : HeightOneSpectrum (𝓞 F), IsOver v P → prV (E := E) v z = 0) → IntAtA (F := F) P z := by
  intro F E _ _ _ _ _ P z hz
  obtain ⟨m, hm, hmz⟩ := GlobalTheory.St.G.IntAd.exists_nat_denom (F := F) (E := E) z
  haveI : (P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))).IsPrime := Ideal.comap_isPrime _ _
  have hm0 : (m : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  obtain ⟨t, htp, ht⟩ := exists_away (P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))) (m : 𝓞 F) hm0
  refine ⟨algebraMap (𝓞 F) (𝓞 E) t, htp, ?_⟩
  have key : iA F E (algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) t)) =
      algebraMap F (E ⊗[F] FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F t) := rfl
  apply GlobalTheory.St.G.IntAd.mem_of_local
  intro w
  by_cases hw : w.asIdeal = P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))
  · rw [map_mul, hz w hw, mul_zero]; exact zero_mem _
  · obtain ⟨c, y, hyw, hyc⟩ := ht w hw
    have hmF : (m : F) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
    have hy0 : algebraMap (𝓞 F) F y ≠ 0 := by
      intro h0
      apply hyw
      rw [(FaithfulSMul.algebraMap_eq_zero_iff (𝓞 F) F).1 h0]
      exact zero_mem _
    set q : F := algebraMap (𝓞 F) F t / (m : F) with hqdef
    have e : iA F E (algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) t)) * z =
        algebraMap F (E ⊗[F] FiniteAdeleRing (𝓞 F) F) q * ((m : E ⊗[F] FiniteAdeleRing (𝓞 F) F) * z) := by
      rw [key, ← mul_assoc, ← map_natCast (algebraMap F (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) m, ← map_mul, hqdef,
        div_mul_cancel₀ _ hmF]
    rw [e, map_mul]
    refine mul_mem ?_ (Formalism.UG.P.afsplit_prV_int w _ hmz)
    have hc : prV (E := E) w (algebraMap F (E ⊗[F] FiniteAdeleRing (𝓞 F) F) q) =
        algebraMap F (E ⊗[F] w.adicCompletion F) q :=
      (Algebra.TensorProduct.map (AlgHom.id F E) (evalV F w)).commutes q
    rw [hc, Algebra.TensorProduct.algebraMap_apply']
    have hq' : q = algebraMap (𝓞 F) F c / algebraMap (𝓞 F) F y := by
      rw [hqdef, div_eq_div_iff hmF hy0]
      have := congrArg (algebraMap (𝓞 F) F) hyc
      rw [map_mul, map_mul, map_natCast] at this
      linear_combination this
    have hq : algebraMap F (w.adicCompletion F) q ∈ w.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      erw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w q]
      rw [hq', map_div₀, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
      have hy1 : w.intValuation y = 1 :=
        le_antisymm (w.intValuation_le_one y) (not_lt.1 fun h => hyw ((w.intValuation_lt_one_iff_mem y).1 h))
      rw [hy1, div_one]
      exact w.intValuation_le_one c
    exact Subring.subset_closure (Or.inr ⟨⟨_, hq⟩, rfl⟩)

end GlobalTheory.VanishAwayInt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralAtOfComponentZeroUnderPrimeStatement
open NumberField IsDedekindDomain Formalism.UG Formalism.L2.Col
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralAt_of_component_zero_under_prime : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (P : HeightOneSpectrum (𝓞 E)) (z : E ⊗[F] FiniteAdeleRing (𝓞 F) F), (∀ v : HeightOneSpectrum (𝓞 F), IsOver v P → prV (E := E) v z = 0) → IntAtA (F := F) P z := by
  first | exact @GlobalTheory.VanishAwayInt.intAtA_of_prV_eq_zero | exact GlobalTheory.VanishAwayInt.intAtA_of_prV_eq_zero | (intros; apply GlobalTheory.VanishAwayInt.intAtA_of_prV_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPowNormOneIdeleEqPrincipalMulIntegralUnit
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

noncomputable section
namespace GlobalTheory.TwV.Xc.ClsPow

variable {E : Type} [Field E] [NumberField E]

theorem exists_pow_eq_diag_mul (y : (FiniteAdeleRing (𝓞 E) E)ˣ) :
    ∃ (k : Eˣ) (u : (FiniteAdeleRing (𝓞 E) E)ˣ),
      (∀ P : HeightOneSpectrum (𝓞 E), Valued.v ((u : FiniteAdeleRing (𝓞 E) E) P) = 1) ∧
      y ^ Fintype.card (ClassGroup (𝓞 E)) = Units.map (algebraMap E (FiniteAdeleRing (𝓞 E) E)).toMonoidHom k * u := by
  classical
  let a : Neutral.B1.Ideles E := ⟨((1 : InfiniteAdeleRing E), (y : FiniteAdeleRing (𝓞 E) E)),
    ((1 : InfiniteAdeleRing E), ((y⁻¹ : (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E)),
    Prod.ext (mul_one _) y.mul_inv, Prod.ext (mul_one _) y.inv_mul⟩
  have hc : ReciprocityTheory.Neutral.Bridge.HCFR.classOf E (a ^ Fintype.card (ClassGroup (𝓞 E))) = 1 := by
    rw [map_pow, pow_card_eq_one]
  obtain ⟨k, u, hu, he⟩ := (ReciprocityTheory.Neutral.Bridge.HCFR.classOf_eq_one_iff E _).1 hc
  refine ⟨k, ⟨(u : AdeleRing (𝓞 E) E).2, ((u⁻¹ : Neutral.B1.Ideles E) : AdeleRing (𝓞 E) E).2, ?_, ?_⟩, fun P => (hu.2 P).1, ?_⟩
  · exact congrArg Prod.snd u.mul_inv
  · exact congrArg Prod.snd u.inv_mul
  · apply Units.ext
    have h2 : ((a ^ Fintype.card (ClassGroup (𝓞 E)) : Neutral.B1.Ideles E) : AdeleRing (𝓞 E) E).2 =
        ((Neutral.B1.diagUnits E k * u : Neutral.B1.Ideles E) : AdeleRing (𝓞 E) E).2 := by rw [he]
    have h3 : ∀ (t : Neutral.B1.Ideles E) (n : ℕ), ((t ^ n : Neutral.B1.Ideles E) : AdeleRing (𝓞 E) E).2 = ((t : AdeleRing (𝓞 E) E).2) ^ n := by
      intro t n
      induction n with
      | zero => rfl
      | succ n ih => rw [pow_succ, pow_succ, ← ih]; rfl
    rw [h3] at h2
    rw [Units.val_pow_eq_pow_val]
    exact h2.trans rfl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_pow_eq_ratId_mul (x : (AfE F E)ˣ) :
    ∃ (a : Eˣ) (k : (AfE F E)ˣ), k ∈ intU F E ∧ x ^ Fintype.card (ClassGroup (𝓞 E)) = ratId F E a * k := by
  obtain ⟨ι, h1, h2⟩ := GlobalTheory.TwU.exists_isAdIso F E
  obtain ⟨a, u, hu, he⟩ := exists_pow_eq_diag_mul (Units.map ι.toRingHom.toMonoidHom x)
  have hinv : ∀ P : HeightOneSpectrum (𝓞 E), Valued.v (((u⁻¹ : (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E) P) = 1 := by
    intro P
    have e : (((u⁻¹ : (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E) P) * ((u : FiniteAdeleRing (𝓞 E) E) P) = 1 := by
      exact congrArg (fun t : FiniteAdeleRing (𝓞 E) E => t P) (Units.inv_mul u)
    have e2 := congrArg Valued.v e
    rw [map_mul, hu P, mul_one, map_one] at e2
    exact e2
  refine ⟨a, Units.map ι.symm.toRingHom.toMonoidHom u, ?_, ?_⟩
  · rw [intU, Submonoid.mem_units_iff]
    constructor
    · show ι.symm (u : FiniteAdeleRing (𝓞 E) E) ∈ RInt F E
      rw [h2]
      intro P
      rw [RingEquiv.apply_symm_apply, hu P]
    · show ι.symm ((u⁻¹ : (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E) ∈ RInt F E
      rw [h2]
      intro P
      rw [RingEquiv.apply_symm_apply, hinv P]
  · apply Units.ext
    apply ι.injective
    have e := congrArg (fun t : (FiniteAdeleRing (𝓞 E) E)ˣ => (t : FiniteAdeleRing (𝓞 E) E)) he
    simp only [Units.val_pow_eq_pow_val, Units.val_mul, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe,
      RingEquiv.toRingHom_eq_coe, RingHom.coe_coe] at e
    rw [Units.val_pow_eq_pow_val, map_pow, e, Units.val_mul, map_mul]
    simp only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      RingEquiv.apply_symm_apply]
    congr 1
    rw [ratId, Units.coe_map]
    show _ = ι (inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F) (a : E))
    rw [inclE, Algebra.TensorProduct.includeLeftRingHom_apply, h1]

theorem conjId_ratId (σ : E →ₐ[F] E) (a : Eˣ) :
    conjId σ (ratId F E a) = ratId F E (Units.map (σ : E →+* E).toMonoidHom a) := by
  apply Units.ext
  simp [conjId, ratId, sigR, inclE]

theorem sigR_mem_RInt (σ : E →ₐ[F] E) {y : AfE F E} (hy : y ∈ RInt F E) :
    sigR σ (FiniteAdeleRing (𝓞 F) F) y ∈ RInt F E := by
  have hle : RInt F E ≤ (RInt F E).comap (sigR σ (FiniteAdeleRing (𝓞 F) F)) := by
    refine (Subring.closure_le).2 ?_
    rintro g (⟨⟨e, ⟨b, rfl⟩⟩, rfl⟩ | ⟨c, rfl⟩)
    · refine Subring.subset_closure (Or.inl ⟨⟨σ (algebraMap (𝓞 E) E b), ⟨RingOfIntegers.mapRingHom (σ : E →+* E) b, ?_⟩⟩, ?_⟩)
      · rfl
      · simp [sigR]
    · refine Subring.subset_closure (Or.inr ⟨c, ?_⟩)
      simp [sigR]
  exact hle hy

theorem conjId_mem_intU (σ : E →ₐ[F] E) {k : (AfE F E)ˣ} (hk : k ∈ intU F E) : conjId σ k ∈ intU F E := by
  rw [intU, Submonoid.mem_units_iff] at hk ⊢
  refine ⟨sigR_mem_RInt σ hk.1, ?_⟩
  rw [← map_inv]
  exact sigR_mem_RInt σ hk.2

theorem conjId_conjId (σ : E →ₐ[F] E) (hσ : ∀ a, σ (σ a) = a) (k : (AfE F E)ˣ) : conjId σ (conjId σ k) = k := by
  apply Units.ext
  show sigR σ (FiniteAdeleRing (𝓞 F) F) (sigR σ (FiniteAdeleRing (𝓞 F) F) (k : AfE F E)) = k
  induction (k : AfE F E) using TensorProduct.induction_on with
  | zero => simp
  | tmul e c => simp [sigR, hσ]
  | add s t hs ht => rw [map_add (f := _), map_add (f := _), hs, ht]

theorem normOne_idele_pow_eq_normOne_principal_mul_unit (σ : E →ₐ[F] E) (hσ : ∀ a, σ (σ a) = a) (x : (AfE F E)ˣ) (hx : x ∈ U1 σ) :
    ∃ (m : ℕ) (z : Eˣ) (k : (AfE F E)ˣ), 0 < m ∧ (z : E) * σ (z : E) = 1 ∧ k ∈ U1 σ ∧ k ∈ intU F E ∧
      x ^ m = ratId F E z * k := by
  classical
  obtain ⟨a, k₀, hk₀, he⟩ := exists_pow_eq_ratId_mul (F := F) x
  set h := Fintype.card (ClassGroup (𝓞 E))
  have hx' : x * conjId σ x = 1 := by
    rw [U1, MonoidHom.mem_ker] at hx
    exact hx
  have hw : x ^ h * conjId σ (x ^ h) = 1 := by rw [map_pow, ← mul_pow, hx', one_pow]
  have hw' : x ^ h = (conjId σ (x ^ h))⁻¹ := eq_inv_of_mul_eq_one_left hw
  let sa : Eˣ := Units.map (σ : E →+* E).toMonoidHom a
  refine ⟨2 * h, a * sa⁻¹, k₀ * (conjId σ k₀)⁻¹, Nat.mul_pos two_pos Fintype.card_pos, ?_, ?_, ?_, ?_⟩
  · have ha : (a : E) ≠ 0 := a.ne_zero
    have hsa : σ (a : E) ≠ 0 := by
      intro h0
      apply ha
      rw [← hσ (a : E), h0, map_zero]
    simp only [sa, Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe,
      AlgHom.coe_toRingHom, RingHom.coe_coe, map_mul, map_inv₀, hσ]
    field_simp
  · rw [U1, MonoidHom.mem_ker, MonoidHom.mul_apply, MonoidHom.id_apply, map_mul, map_inv, conjId_conjId σ hσ]
    rw [mul_assoc, inv_mul_cancel_left, mul_inv_cancel]
  · exact mul_mem hk₀ (inv_mem (conjId_mem_intU σ hk₀))
  · have hc : conjId σ (x ^ h) = ratId F E sa * conjId σ k₀ := by rw [he, map_mul, conjId_ratId]
    rw [mul_comm 2 h, pow_mul, sq]
    calc x ^ h * x ^ h = x ^ h * (conjId σ (x ^ h))⁻¹ := by rw [← hw']
      _ = ratId F E (a * sa⁻¹) * (k₀ * (conjId σ k₀)⁻¹) := by
        rw [hc, he, map_mul, map_inv, mul_inv]
        ac_rfl

theorem _root_.GlobalTheory.TwV.Xc.exists_pow_normOne_idele_eq_principal_mul_integralUnit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), (∀ a, σ (σ a) = a) → ∀ x ∈ U1 σ, ∃ (m : ℕ) (z : Eˣ) (k : (AfE F E)ˣ), 0 < m ∧ (z : E) * σ (z : E) = 1 ∧ k ∈ U1 σ ∧ k ∈ intU F E ∧ x ^ m = ratId F E z * k :=
  fun _ _ _ _ _ _ _ σ hσ x hx => normOne_idele_pow_eq_normOne_principal_mul_unit σ hσ x hx

end GlobalTheory.TwV.Xc.ClsPow
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUnitaryOneFiniteAdelicOfDetNormOne
noncomputable section
namespace GlobalTheory.TwU
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section OneByOne
variable {R : Type} [CommRing R]

end OneByOne

variable {D : D7}

theorem det_mem_normOne_of_mem_unitaryPoints {n : ℕ} {J : Matrix (Fin n) (Fin n) D.host.E} (hJ : IsUnit J.det)
    {g : GL (Fin n) (AfE D.host.F D.host.E)} (hg : g ∈ UPts (sigD D) J (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
    Matrix.GeneralLinearGroup.det g ∈ U1 (sigD D) := by
  set σR := Formalism.UG.sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
  have h0 : Formalism.UG.cT σR (g : Matrix (Fin n) (Fin n) (AfE D.host.F D.host.E)) * J.map (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) *
      (g : Matrix (Fin n) (Fin n) (AfE D.host.F D.host.E)) = J.map (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := hg
  have h1 := congrArg Matrix.det h0
  simp only [Matrix.det_mul, Formalism.UG.cT, Matrix.det_transpose] at h1
  have e1 : ((g : Matrix (Fin n) (Fin n) (AfE D.host.F D.host.E)).map σR).det = σR (g : Matrix (Fin n) (Fin n) (AfE D.host.F D.host.E)).det := by
    rw [RingHom.map_det]; rfl
  have e2 : (J.map (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))).det = Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) J.det := by
    rw [RingHom.map_det]; rfl
  rw [e1, e2] at h1
  have hu : IsUnit (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) J.det) := hJ.map _
  have h2 : σR (g : Matrix (Fin n) (Fin n) (AfE D.host.F D.host.E)).det * (g : Matrix (Fin n) (Fin n) (AfE D.host.F D.host.E)).det = 1 := by
    have : (σR (g : Matrix (Fin n) (Fin n) (AfE D.host.F D.host.E)).det * (g : Matrix (Fin n) (Fin n) (AfE D.host.F D.host.E)).det) *
        Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) J.det = 1 * Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) J.det := by
      linear_combination h1
    exact hu.mul_right_cancel this
  show _ = _
  apply Units.ext
  simp only [MonoidHom.mul_apply, MonoidHom.id_apply, Units.val_mul, conjId, Units.coe_map, Units.val_one,
    Matrix.GeneralLinearGroup.val_det_apply]
  rw [mul_comm]
  exact h2

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup}


end GlobalTheory.TwU
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamDescends
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open Neutral.B1 hiding G Dec IsPlaceOver
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.DRDescent

theorem deRham_descends : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (l : ℕ) [Fact l.Prime], ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (a : ℕ) (r : G K Ω →* GL (Fin a) (Qbar l)), Continuous r → ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l K Ω (Dec (F := K) A) O), GlobalTheory.Pst.Induces Bw → ∃ (O' : Type) (_ : CommRing O') (_ : Algebra ℤ_[l] O') (_ : TopologicalSpace O') (Bw' : LocBridge l L Ω (Dec (F := L) A) O'), GlobalTheory.Pst.Induces Bw' ∧ Bw'.j = Bw.j ∧ (IsdRAt P Bw' ((resTo L r).comp (Dec (F := L) A).subtype) → IsdRAt P Bw (r.comp (Dec (F := K) A).subtype)) := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ A v v' h h' l _ P AI hT a r hr O _ _ _ Bw hj
  obtain ⟨T⟩ := hT
  obtain ⟨LL₀, Bw', hjj, hS, hKle⟩ := GlobalTheory.AboveLRes.exists_bridge (L := L) Bw hj Bw.LL
  have hj' : GlobalTheory.Pst.Induces Bw' := fun x => by rw [hjj]; exact hj x
  refine ⟨_, _, _, _, Bw', hj', hjj, fun hc => ?_⟩
  have hcont : Continuous (fun g => (r g : Matrix (Fin a) (Fin a) (Om l))) := Units.continuous_val.comp hr
  obtain ⟨M, hM, hmem⟩ := GlobalTheory.CompactRepField.exists_finExt_entries_mem l (G K Ω) a r hcont Bw'.LL
  obtain ⟨r₁, -, hr₁⟩ := GlobalTheory.DeRhamRead.exists_model_of_mem r hcont M hmem
  set rE : ↥(Dec (F := K) A) →* GL (Fin a) ↥M.1 := r₁.comp (Dec (F := K) A).subtype with hrE
  have hmodE : IsModel Bw (r.comp (Dec (F := K) A).subtype) M rE := by
    refine ⟨hS.trans hM, ?_⟩
    ext g i k
    exact congrArg (fun f : G K Ω →* GL (Fin a) (Om l) =>
      ((f (g : G K Ω) : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i k) hr₁
  have hmodL : IsModel Bw' ((resTo L r).comp (Dec (F := L) A).subtype) M (rE.comp (GlobalTheory.AboveLRes.decRes A)) := by
    refine ⟨hM, ?_⟩
    ext g i k
    exact congrArg (fun f : G K Ω →* GL (Fin a) (Om l) =>
      ((f ((GlobalTheory.AboveLRes.decRes (K := K) A g : ↥(Dec (F := K) A)) : G K Ω) : GL (Fin a) (Om l)) :
        Matrix (Fin a) (Fin a) (Om l)) i k) hr₁
  have hrep := GlobalTheory.AboveLRes.repE_decRes Bw Bw' hjj hKle M rE
  have hdL : Bw'.IsdRE P M (rE.comp (GlobalTheory.AboveLRes.decRes A)) := (hmodL.isdRAt_iff P).1 hc
  have hdR' : IsDR (P.PD Bw'.Kw) (GlobalTheory.Pst.resTo (Bw.repE M rE) hKle) := by
    unfold IsDR
    rw [← hrep, Module.finrank_fin_fun]
    exact hdL
  have hdR : IsDR (P.PD Bw.Kw) (Bw.repE M rE) :=
    (GlobalTheory.Per.TiedRestrict.isDR_restrict_iff hKle (Bw.repE M rE) T).2 hdR'
  have hdK : Bw.IsdRE P M rE := by
    have := hdR
    unfold IsDR at this
    rw [Module.finrank_fin_fun] at this
    exact this
  exact ⟨M, rE, hmodE, hdK⟩

end GlobalTheory.DRDescent
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JumpsDescend
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open Neutral.B1 hiding G Dec IsPlaceOver
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.JumpsDescend

theorem jumps_descend : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (l : ℕ) [Fact l.Prime], ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (a : ℕ) (r : G K Ω →* GL (Fin a) (Qbar l)), Continuous r → ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l K Ω (Dec (F := K) A) O) (O' : Type) [CommRing O'] [Algebra ℤ_[l] O'] [TopologicalSpace O'] (Bw' : LocBridge l L Ω (Dec (F := L) A) O'), GlobalTheory.Pst.Induces Bw → GlobalTheory.Pst.Induces Bw' → Bw'.j = Bw.j → ∀ (τ : K →+* Qbar l) (τL : L →+* Qbar l), τL.comp (algebraMap K L) = τ → ∀ J : Multiset ℤ, IsJumpsAt P Bw' ((resTo L r).comp (Dec (F := L) A).subtype) τL J → IsJumpsAt P Bw (r.comp (Dec (F := K) A).subtype) τ J := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ A v v' _ _ l _ P AI hT a r hr O _ _ _ Bw O' _ _ _ Bw' hj hj' hjj τ τL hτL J hJ
  obtain ⟨T⟩ := hT

  have hle : Bw.Kw.1 ≤ Bw'.Kw.1 := by
    rw [BridgeInd.kw_eq_adjoin Bw, BridgeInd.kw_eq_adjoin Bw', IntermediateField.adjoin_le_iff]
    rintro _ ⟨x, rfl⟩
    refine IntermediateField.subset_adjoin _ _ ⟨algebraMap K L x, ?_⟩
    show Bw'.j (algebraMap L Ω (algebraMap K L x)) = Bw.j (algebraMap K Ω x)
    rw [hjj, ← IsScalarTower.algebraMap_apply]
  have hJ0 := hJ
  obtain ⟨LL', r', hmod', hdR', τ₁, hi₁, -⟩ := hJ
  have hcont : Continuous (fun g => (r g : Matrix (Fin a) (Fin a) (Om l))) := Units.continuous_val.comp hr
  obtain ⟨L₁, hL₁, hmem⟩ := GlobalTheory.CompactRepField.exists_finExt_entries_mem l (G K Ω) a r hcont (supExt Bw.LL LL')
  have hBL : Bw.LL.1 ≤ L₁.1 := (le_sup_left : Bw.LL.1 ≤ (supExt Bw.LL LL').1).trans hL₁
  have hLL : LL'.1 ≤ L₁.1 := (le_sup_right : LL'.1 ≤ (supExt Bw.LL LL').1).trans hL₁
  obtain ⟨r₁, -, hr₁⟩ := GlobalTheory.DeRhamRead.exists_model_of_mem r hcont L₁ hmem
  set rE : ↥(Dec (F := K) A) →* GL (Fin a) ↥L₁.1 := r₁.comp (Dec (F := K) A).subtype with hrE
  have hmodE : IsModel Bw (r.comp (Dec (F := K) A).subtype) L₁ rE := by
    refine ⟨hBL, ?_⟩
    ext g i k
    exact congrArg (fun f : G K Ω →* GL (Fin a) (Om l) => ((f (g : G K Ω) : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i k) hr₁
  have hmodM : IsModel Bw' ((GlobalTheory.AboveL.resTo L r).comp (Dec (F := L) A).subtype) L₁ (rE.comp (GlobalTheory.AboveLRes.decRes A)) := by
    refine ⟨hmod'.1.trans hLL, ?_⟩
    ext g i k
    exact congrArg (fun f : G K Ω →* GL (Fin a) (Om l) => ((f ((GlobalTheory.AboveLRes.decRes (K := K) A g : ↥(Dec (F := K) A)) : G K Ω) : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i k) hr₁
  have hrep := GlobalTheory.AboveLRes.repE_decRes Bw Bw' hjj hle L₁ rE
  have hdM : Bw'.IsdRE P L₁ (rE.comp (GlobalTheory.AboveLRes.decRes A)) := (hmodM.isdRAt_iff P).1 ⟨LL', r', hmod', hdR'⟩
  have hdR2 : IsDR (P.PD Bw'.Kw) (GlobalTheory.Pst.resTo (Bw.repE L₁ rE) hle) := by
    unfold IsDR
    rw [← hrep, Module.finrank_fin_fun]
    exact hdM
  have hdR : IsDR (P.PD Bw.Kw) (Bw.repE L₁ rE) := (GlobalTheory.Per.TiedRestrict.isDR_restrict_iff hle (Bw.repE L₁ rE) T).2 hdR2
  have hdE : Bw.IsdRE P L₁ rE := by
    have := hdR
    unfold IsDR at this
    rw [Module.finrank_fin_fun] at this
    exact this

  let τ'' : ↥Bw'.Kw.1 →ₐ[ℚ_[l]] ↥L₁.1 := (IntermediateField.inclusion hLL).comp τ₁
  have hiM : IsInduced Bw' τL τ'' := fun x => hi₁ x
  let τ₂ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥L₁.1 := τ''.comp (IntermediateField.inclusion hle)
  have hτ₂ : IsInduced Bw τ τ₂ := by
    intro x
    have e1 : (IntermediateField.inclusion hle ⟨Bw.j (algebraMap K Ω x), Bw.j_E x⟩ : ↥Bw'.Kw.1) =
        ⟨Bw'.j (algebraMap L Ω (algebraMap K L x)), Bw'.j_E (algebraMap K L x)⟩ := by
      apply Subtype.ext
      show Bw.j (algebraMap K Ω x) = Bw'.j (algebraMap L Ω (algebraMap K L x))
      rw [hjj, ← IsScalarTower.algebraMap_apply]
    show τ x = ((τ'' (IntermediateField.inclusion hle ⟨Bw.j (algebraMap K Ω x), Bw.j_E x⟩) : ↥L₁.1) : Om l)
    rw [e1, ← hτL]
    exact hiM (algebraMap K L x)
  refine ⟨L₁, rE, hmodE, hdE, τ₂, hτ₂, fun n => ?_⟩
  rw [IsJumpsAt.count_eq P hmodM hiM hJ0 n]
  unfold LocBridge.multE
  rw [hrep]
  exact GlobalTheory.JumpRestrict.multV_restrict l P AI T Bw.Kw Bw'.Kw L₁ hle (Fin a → ↥L₁.1) (Bw.repE L₁ rE) hdR τ'' n

end GlobalTheory.JumpsDescend
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOtherSplitPlaceWithDistinctRealPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOtherSplitPlaceWithDistinctRealPlace
open NumberField IsDedekindDomain Formalism.L2.Host
open Neutral.B1 hiding G Dec IsPlaceOver
open GlobalTheory.HeckeUnrExt
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap ideleConj)

namespace GlobalTheory.OtherSplitPlace

theorem exists_isSplitAt_under_ne : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (w₀ : HeightOneSpectrum (𝓞 E)), ∃ w₁ : HeightOneSpectrum (𝓞 E), GlobalTheory.UnitaryBC.IsSplitAt w₁ ∧
      w₁.under (𝓞 (maximalRealSubfield E)) ≠ w₀.under (𝓞 (maximalRealSubfield E)) := by
  intro E _ _ _ w₀
  obtain ⟨p, hp, hmp, hs⟩ := GlobalTheory.LargeSplitPrime.exists_splitsCompl E (Ideal.absNorm w₀.asIdeal)
  have h2 : Module.finrank (maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _

  have hsplit : ∀ w : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ w.asIdeal → GlobalTheory.UnitaryBC.IsSplitAt w := by
    intro w hw
    have hv : (p : 𝓞 (maximalRealSubfield E)) ∈ (w.under (𝓞 (maximalRealSubfield E))).asIdeal := by
      show algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) (p : 𝓞 (maximalRealSubfield E)) ∈ w.asIdeal
      rwa [map_natCast]
    obtain ⟨a, b, hab, ha, hb⟩ :=
      GlobalTheory.SplitPlace.isSplit_of_norm h2 hp (fun u hu => hs u.asIdeal u.isMaximal hu) _ hv
    by_cases h : a = w
    · exact ⟨b, fun e => hab (h.trans e.symm), HeightOneSpectrum.ext hb⟩
    · exact ⟨a, h, HeightOneSpectrum.ext ha⟩

  haveI hPmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have hinj : Function.Injective (algebraMap ℤ (𝓞 E)) := (algebraMap ℤ (𝓞 E)).injective_int
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 E)
    (Ideal.span {(p : ℤ)}) (by rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]; exact bot_le)
  have hpQ : (p : 𝓞 E) ∈ Q := by
    have : (p : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 E)) := by
      change (p : ℤ) ∈ Ideal.under ℤ Q
      rw [hQ]
      exact Ideal.subset_span rfl
    simpa using this
  have hp0 : (p : 𝓞 E) ≠ 0 := by exact_mod_cast hp.ne_zero
  let w₁ : HeightOneSpectrum (𝓞 E) := ⟨Q, hQmax.isPrime, fun h => hp0 (by rw [h] at hpQ; simpa using hpQ)⟩
  refine ⟨w₁, hsplit w₁ hpQ, fun heq => ?_⟩

  have hp₀ : (p : 𝓞 E) ∈ w₀.asIdeal := by
    have hv : (p : 𝓞 (maximalRealSubfield E)) ∈ (w₁.under (𝓞 (maximalRealSubfield E))).asIdeal := by
      show algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) (p : 𝓞 (maximalRealSubfield E)) ∈ w₁.asIdeal
      rw [map_natCast]; exact hpQ
    rw [heq] at hv
    have : algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) (p : 𝓞 (maximalRealSubfield E)) ∈ w₀.asIdeal := hv
    rwa [map_natCast] at this
  have hN : ((Ideal.absNorm w₀.asIdeal : ℕ) : 𝓞 E) ∈ w₀.asIdeal := Ideal.absNorm_mem _
  have hN0 : 0 < Ideal.absNorm w₀.asIdeal :=
    Nat.pos_of_ne_zero (fun h => w₀.ne_bot (Ideal.absNorm_eq_zero_iff.mp h))
  have hcop : Nat.Coprime p (Ideal.absNorm w₀.asIdeal) :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr (fun h => absurd (Nat.le_of_dvd hN0 h) (not_le.mpr hmp))
  obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.mpr hcop).map (Int.castRingHom (𝓞 E))
  apply w₀.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ ?_) (Ideal.mul_mem_left _ _ ?_)
  · simpa using hp₀
  · simpa using hN

end GlobalTheory.OtherSplitPlace
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOtherSplitPlaceWithDistinctRealPlaceStatement
open NumberField IsDedekindDomain Formalism.L2.Host
open Neutral.B1 hiding G Dec IsPlaceOver
open GlobalTheory.HeckeUnrExt
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap ideleConj)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_other_split_place_with_distinct_real_place : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w₀ : HeightOneSpectrum (𝓞 E)), ∃ w₁ : HeightOneSpectrum (𝓞 E), GlobalTheory.UnitaryBC.IsSplitAt w₁ ∧ w₁.under (𝓞 (maximalRealSubfield E)) ≠ w₀.under (𝓞 (maximalRealSubfield E)) := by
  first | exact @GlobalTheory.OtherSplitPlace.exists_isSplitAt_under_ne | exact GlobalTheory.OtherSplitPlace.exists_isSplitAt_under_ne | (intros; apply GlobalTheory.OtherSplitPlace.exists_isSplitAt_under_ne <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNormOneIdeleOrderOneTrivialElsewhere
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNormOneIdeleOrderOneTrivialElsewhere
noncomputable section

namespace GlobalTheory.TwV.Xc.Unif

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV
  Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

section OneAt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def oneAt (w : HeightOneSpectrum (𝓞 F)) (a : E ⊗[F] w.adicCompletion F) : AfE F E :=
  Formalism.UG.P.afsplitIE w a + (1 - Formalism.UG.P.afsplitEps E w)

theorem prV_oneAt_self (w : HeightOneSpectrum (𝓞 F)) (a : E ⊗[F] w.adicCompletion F) :
    prV (E := E) w (oneAt w a) = a := by
  rw [oneAt, map_add (f := _), map_sub, map_one, Formalism.UG.P.afsplit_prV_IE, Formalism.UG.P.afsplit_prV_eps, sub_self, add_zero]

theorem prV_oneAt_ne (w w' : HeightOneSpectrum (𝓞 F)) (h : w' ≠ w) (a : E ⊗[F] w.adicCompletion F) :
    prV (E := E) w' (oneAt w a) = 1 := by
  rw [oneAt, map_add (f := _), map_sub, map_one, Formalism.UG.P.afsplit_prV_IE_ne w w' h, Formalism.UG.P.afsplit_prV_eps_ne w w' h,
    sub_zero, zero_add]

theorem ext_prV {x y : AfE F E} (h : ∀ w : HeightOneSpectrum (𝓞 F), prV (E := E) w x = prV (E := E) w y) : x = y := by
  rw [← sub_eq_zero]
  exact Formalism.UG.P.afsplit_inj _ fun w => by rw [map_sub, h, sub_self]

theorem oneAt_mul (w : HeightOneSpectrum (𝓞 F)) (a b : E ⊗[F] w.adicCompletion F) :
    oneAt w a * oneAt w b = oneAt w (a * b) := ext_prV fun w' => by
  by_cases h : w' = w
  · subst h; rw [map_mul, prV_oneAt_self, prV_oneAt_self, prV_oneAt_self]
  · rw [map_mul, prV_oneAt_ne w w' h, prV_oneAt_ne w w' h, prV_oneAt_ne w w' h, one_mul]

theorem oneAt_one (w : HeightOneSpectrum (𝓞 F)) : oneAt (E := E) w 1 = 1 := ext_prV fun w' => by
  by_cases h : w' = w
  · subst h; rw [prV_oneAt_self, map_one]
  · rw [prV_oneAt_ne w w' h, map_one]

theorem sigR_oneAt (σ : E →ₐ[F] E) (w : HeightOneSpectrum (𝓞 F)) (a : E ⊗[F] w.adicCompletion F) :
    sigR σ (FiniteAdeleRing (𝓞 F) F) (oneAt w a) = oneAt w (sigR σ (w.adicCompletion F) a) := by
  rw [oneAt, oneAt, map_add (f := _), map_sub, map_one, Formalism.UG.P.afsplit_sigR_IE, Formalism.UG.P.afsplit_sigR_eps]

def oneAtU (w : HeightOneSpectrum (𝓞 F)) (a : (E ⊗[F] w.adicCompletion F)ˣ) : (AfE F E)ˣ :=
  ⟨oneAt w a, oneAt w (a⁻¹ : (E ⊗[F] w.adicCompletion F)ˣ),
    by rw [oneAt_mul, Units.mul_inv, oneAt_one], by rw [oneAt_mul, Units.inv_mul, oneAt_one]⟩

theorem oneAtU_coe (w : HeightOneSpectrum (𝓞 F)) (a : (E ⊗[F] w.adicCompletion F)ˣ) :
    (oneAtU w a : AfE F E) = oneAt w a := rfl

end OneAt

theorem exists_unif : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n p : ℕ) (G : GAtP p) (A : LocAt F E n G) (J : Matrix (Fin n) (Fin n) E) [Fact p.Prime],
    LocGood σ J A → ∀ v, ∃ π ∈ U1 σ, OneOff (A.pl v).1 π ∧ ordA A v π = 1 := by
  intro F E _ _ _ _ _ σ n p G A J _ H v
  have hp0 : (p : (A.pl v).1.adicCompletion F) ≠ 0 := by
    rw [← map_natCast (algebraMap F ((A.pl v).1.adicCompletion F))]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  let c : ((A.pl v).1.adicCompletion F × (A.pl v).1.adicCompletion F)ˣ :=
    ⟨((p : (A.pl v).1.adicCompletion F), (p : (A.pl v).1.adicCompletion F)⁻¹),
      ((p : (A.pl v).1.adicCompletion F)⁻¹, (p : (A.pl v).1.adicCompletion F)),
      Prod.ext (mul_inv_cancel₀ hp0) (inv_mul_cancel₀ hp0), Prod.ext (inv_mul_cancel₀ hp0) (mul_inv_cancel₀ hp0)⟩
  let a : (E ⊗[F] (A.pl v).1.adicCompletion F)ˣ := Units.map (A.spl v).symm.toMonoidHom c
  have ha : A.spl v (a : E ⊗[F] (A.pl v).1.adicCompletion F) =
      ((p : (A.pl v).1.adicCompletion F), (p : (A.pl v).1.adicCompletion F)⁻¹) := by
    show A.spl v ((A.spl v).symm _) = _
    rw [RingEquiv.apply_symm_apply]
  refine ⟨oneAtU (A.pl v).1 a, ?_, fun w' hw' => prV_oneAt_ne _ w' hw' _, ?_⟩
  · rw [U1, MonoidHom.mem_ker]
    apply Units.ext
    show oneAt (A.pl v).1 (a : E ⊗[F] (A.pl v).1.adicCompletion F) *
        sigR σ (FiniteAdeleRing (𝓞 F) F) (oneAt (A.pl v).1 (a : E ⊗[F] (A.pl v).1.adicCompletion F)) = 1
    rw [sigR_oneAt, oneAt_mul, ← oneAt_one (E := E) (A.pl v).1]
    congr 1
    apply (A.spl v).injective
    rw [map_mul, H.sig v, ha, map_one]
    show (((p : (A.pl v).1.adicCompletion F), (p : (A.pl v).1.adicCompletion F)⁻¹) *
      ((p : (A.pl v).1.adicCompletion F)⁻¹, (p : (A.pl v).1.adicCompletion F)) :
        (A.pl v).1.adicCompletion F × (A.pl v).1.adicCompletion F) = 1
    exact Prod.ext (mul_inv_cancel₀ hp0) (inv_mul_cancel₀ hp0)
  · have := (G.P.setting v).frac_alt
    have hp := (G.P.setting v).p_unif
    have h1 := ordP_eq (Qq := G.P.Qq v) hp 1 1
    have h2 : phiA A v (oneAtU (A.pl v).1 a : AfE F E) = (p : G.P.Qq v) := by
      simp only [phiA, RingHom.comp_apply, oneAtU_coe, prV_oneAt_self]
      show (A.eQ v).symm ((A.spl v (a : E ⊗[F] (A.pl v).1.adicCompletion F)).1) = _
      rw [ha, map_natCast]
    unfold ordA
    rw [h2]
    simpa using h1

end GlobalTheory.TwV.Xc.Unif

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNormOneIdeleOrderOneTrivialElsewhereStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normOne_idele_order_one_trivial_elsewhere : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n p : ℕ) (G : GAtP p) (A : LocAt F E n G) (J : Matrix (Fin n) (Fin n) E) [Fact p.Prime], LocGood σ J A → ∀ v, ∃ π ∈ U1 σ, OneOff (A.pl v).1 π ∧ ordA A v π = 1 := by
  first | exact @GlobalTheory.TwV.Xc.Unif.exists_unif | exact GlobalTheory.TwV.Xc.Unif.exists_unif | (intros; apply GlobalTheory.TwV.Xc.Unif.exists_unif <;> assumption)
end
end
