module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwistBaseCoefficientRingResidueFieldFinite
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCMValueHeckeCharacterAuxiliarySetOfEmpty

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LambdaDataAtSide
noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie GlobalTheory.ToricRational GlobalTheory.ToricDistribution

namespace GlobalTheory.LamTie

attribute [local instance 10000] GlobalTheory.GalChar.isTorsionFree_field

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem exists_th_of (hA : GlobalTheory.Published.GlobalArtinReciprocity) (hG : RatioConj) (hL : ToricSumFormula) {i : X.Tw} {ι : ℂ →+* Kbar X i}
    (hE : ∀ (σ : D.host.E →+* ℂ) (x : D.host.E), ι (σ x) ∈ (algebraMap (FractionRing (X.O i)) (Kbar X i)).range)
    {lam : X.abelian₂ i} {I : Type} [Fintype I] {φ : I → D.host.E →+* ℂ} {s : ℕ} {κ : I → ℕ} {𝔣 : Ideal (OF D.host.E)} {χ : HChar D.host.E}
    (hD : IsHostDatum D.host φ s κ 𝔣 χ) (h𝔣 : ∀ P, (below P).asIdeal ∣ 𝔣 → P ∈ X.S0 i)
    (hX : ∀ P, P ∉ X.S0 i → algebraMap (X.O i) (Kbar X i) (X.Xv i lam P) * ι (χ.val P : ℂ) = 1) :
    ∃ t : ∀ Q, X.RCG i Q → FractionRing (X.O i), ∀ th : ∀ i Q, X.abelian₂ i → X.RCG i Q → FractionRing (X.O i),
      (∀ Q, th i Q lam = t Q) → IsThOf (setTh X th) i ι lam φ s κ 𝔣 χ := by
  obtain ⟨T₀, hT₀, h0⟩ := exists_toricSum_ne_zero hL host_unramFin hD
  have := X.O_complete i
  have key : ∀ Q, ∃ t : X.RCG i Q → FractionRing (X.O i), BlochKatoReduction.Gen.QOk X i Q → Finite (PicO (condQ 𝔣 (belowSet Q))) ∧
      ∃ (π : PicO (condQ 𝔣 (belowSet Q)) →* X.RCG i Q) (T : PicO (condQ 𝔣 (belowSet Q)) → ℂ),
        IsRecMap X i Q π ∧ (∀ q, IsClassTerm φ s κ (condQ 𝔣 (belowSet Q)) χ q.out (T q)) ∧
        ∀ δ, algebraMap (FractionRing (X.O i)) (Kbar X i) (t δ) = (ι T₀)⁻¹ * ι (∑ᶠ q ∈ {q | π q⁻¹ = δ}, T q) := fun Q => by
    by_cases hQ : BlochKatoReduction.Gen.QOk X i Q
    · obtain ⟨hfin, T, hT⟩ := exists_classTerms hL host_unramFin hD (placesBelow_splitCoprimeConductor_of_admissible hQ h𝔣).1
      obtain ⟨π, hπ, hπl⟩ := exists_isRecMap hA hQ 𝔣
      choose t ht using partialSum_mem hA hG host_unramFin hD (X.resO_ac i) (X.lPrime i).out.ne_zero (X.O_l i) ι hE (X.S0 i)
        (fun P hP => ⟨(algebraMap (X.O i) _ (X.Xv i lam P))⁻¹, by
          rw [map_inv₀, ← IsScalarTower.algebraMap_apply]
          exact (eq_inv_of_mul_eq_one_right (hX P hP)).symm⟩) hT₀ h0 (placesBelow_splitCoprimeConductor_of_admissible hQ h𝔣).1 hT π hπl
      exact ⟨t, fun _ => ⟨hfin, π, T, hπ, hT, ht⟩⟩
    · exact ⟨0, fun h => absurd h hQ⟩
  choose t ht using key
  refine ⟨t, fun th e => ⟨(ι T₀)⁻¹, inv_ne_zero ((map_ne_zero ι).2 h0), fun Q hQ => ?_⟩⟩
  obtain ⟨h1, π, T, h2, h3, h4⟩ := ht Q hQ
  exact ⟨h1, π, T, h2, h3, fun δ => (congrArg _ (congrFun (e Q) δ)).trans (h4 δ)⟩

end GlobalTheory.LamTie
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTwoReadings
noncomputable section

namespace GlobalTheory.LamTie.TrueList

section Local

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler GlobalTheory.CMVal.Euler.SplitPair GlobalTheory.LamTie.ConjLevel

variable {E : Type} [Field E] [NumberField E]

theorem exists_unit_conj [IsCMField E] {χ : HChar E} (hF : TrivOnF χ) {v : HeightOneSpectrum (OF E)} (hs : Splits v)
    {P P' : HeightOneSpectrum (𝓞 E)} (hP : Over P v) (hP' : Over P' v) (hne : P ≠ P') (u : (P'.adicCompletion E)ˣ)
    (hu : Valued.v (u : P'.adicCompletion E) = 1) :
    ∃ u' : (P.adicCompletion E)ˣ, Valued.v (u' : P.adicCompletion E) = 1 ∧ χ.loc P u' * χ.loc P' u = 1 := by
  obtain ⟨h2, hef⟩ := GlobalTheory.CMVal.Euler.SplitPlace.split_place E v hs
  have hmul := loc_mul_loc hF hP hP' hne (h2 P P' hP hP' hne)
  obtain ⟨m, hm⟩ := GlobalTheory.Mem.UnrAe.exists_levelLe χ P'
  obtain ⟨a, h4⟩ := exists_cong hs hP' (m + 1) u hu.le
  have hlt : WithZero.exp (-((m + 1 : ℕ) : ℤ)) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have hlt1 : WithZero.exp (-((1 : ℕ) : ℤ)) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have h5 : Valued.v (iota a P') = 1 := by
    rw [Valuation.map_eq_of_sub_lt _ (hu ▸ h4.trans_lt hlt), hu]
  have hav : a ∉ v.asIdeal ^ 1 := fun h => (h5 ▸ val_iota_le_of_mem hP' 1 h).not_gt hlt1
  have ha0 : a ≠ 0 := fun h => hav (h ▸ zero_mem _)
  have hunit : Valued.v (iota a P) = 1 := by
    have := eq_exp_of_le (m := 0) (by simpa using val_iota_le_one P a) fun h3 => hav (by
      rw [← (hef P hP).2.1, ← val_iota_le_iff]
      simpa using h3)
    simpa using this
  have h8 : χ.loc P' (locF P' a ha0 / u) = 1 := by
    refine hm _ ?_ ?_
    · show Valued.v ((locF P' a ha0 / u : (P'.adicCompletion E)ˣ) : P'.adicCompletion E) = 1
      rw [Units.val_div_eq_div_val, map_div₀, coe_locF, h5, hu, div_one]
    · rw [Units.val_div_eq_div_val, div_sub_one u.ne_zero, map_div₀, hu, div_one, coe_locF]
      exact h4.trans (WithZero.exp_le_exp.2 (by omega))
  rw [map_div, div_eq_one] at h8
  exact ⟨locF P a ha0, hunit, h8 ▸ hmul a ha0⟩

def TeichTriv (χ : Formalism.L2.Host.HChar E) (v : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ x : (v.adicCompletion E)ˣ, x ^ (Ideal.absNorm v.asIdeal - 1) = 1 → χ.loc v x = 1

theorem teichTriv_of_split [IsCMField E] {χ : HChar E} (hF : TrivOnF χ) {v : HeightOneSpectrum (OF E)} (hs : Splits v)
    {P P' : HeightOneSpectrum (𝓞 E)} (hP : Over P v) (hP' : Over P' v) {p : ℕ} (hp : p.Prime)
    (hN : Ideal.absNorm P.asIdeal = p) (hN' : Ideal.absNorm P'.asIdeal = p) (h : TeichTriv χ P) : TeichTriv χ P' := by
  by_cases hne : P = P'
  · exact hne ▸ h
  intro x hx
  rw [hN'] at hx
  have h1 : p - 1 ≠ 0 := by have := hp.two_le; omega
  have hu : Valued.v (x : P'.adicCompletion E) = 1 := by
    have := congrArg (fun y : (P'.adicCompletion E)ˣ => Valued.v (y : P'.adicCompletion E)) hx
    simp only [Units.val_pow_eq_pow_val, map_pow, Units.val_one, map_one] at this
    exact (pow_eq_one_iff_left h1).1 this
  obtain ⟨u, hu', e⟩ := exists_unit_conj hF hs hP hP' hne x hu
  obtain ⟨n, hn⟩ := (GlobalTheory.Mem.WildChar.orders_on_units _ χ P).2 h u hu'
  have e1 : χ.loc P' x ^ (p ^ n) = 1 := by
    have := congrArg (· ^ (p ^ n)) e
    rw [hN] at hn
    simpa only [mul_pow, hn, one_mul, one_pow] using this
  have e2 : χ.loc P' x ^ (p - 1) = 1 := by rw [← map_pow, hx, map_one]
  have hc : Nat.Coprime (p ^ n) (p - 1) := Nat.Coprime.pow_left _ (by
    obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by have := hp.two_le; omega⟩
    simp)
  have := pow_gcd_eq_one.2 ⟨e1, e2⟩
  rwa [hc, pow_one] at this

end Local

section Global

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.ToricRational
open GlobalTheory.HeckeGal GlobalTheory.GalChar GlobalTheory.HeightCounting

attribute [local instance 10000] GlobalTheory.GalChar.isTorsionFree_field

theorem exists_two_readings {L : Type} [Field L] (φ : L →+* ℂ) :
    ∃ (K : Subfield ℂ) (f f' : K →+* L), (∀ x, φ (f x) = K.subtype x) ∧ (∀ x, φ (f' x) = starRingEnd ℂ (K.subtype x)) ∧
      ∀ z, z ∈ φ.fieldRange → starRingEnd ℂ z ∈ φ.fieldRange → z ∈ K := by
  let K : Subfield ℂ := φ.fieldRange ⊓ φ.fieldRange.comap (starRingEnd ℂ)
  let e := φ.rangeRestrictFieldEquiv
  have he : ∀ y, φ (e.symm y) = y := fun y => congrArg Subtype.val (e.apply_symm_apply y)
  exact ⟨K, e.symm.toRingHom.comp (K.subtype.codRestrict φ.fieldRange fun x => x.2.1),
    e.symm.toRingHom.comp (((starRingEnd ℂ).comp K.subtype).codRestrict φ.fieldRange fun x => x.2.2),
    fun x => he _, fun x => he _, fun z h h' => ⟨h, h'⟩⟩

theorem valuesIn_of_unitary {E L : Type} [Field E] [NumberField E] [Field L] {φ : L →+* ℂ} {K : Subfield ℂ}
    (hK : ∀ z, z ∈ φ.fieldRange → starRingEnd ℂ z ∈ φ.fieldRange → z ∈ K) {χ : Formalism.L2.Host.HChar E} (hu : χ.IsUnitary)
    (h : χ.ValuesIn 0 φ) : χ.ValuesIn 0 K.subtype := fun v hv => by
  obtain ⟨y, hy⟩ := h v hv
  have h1 : ‖χ.valTw 0 v‖ = 1 := by
    simp only [HChar.valTw, Complex.ofReal_zero, neg_zero, Complex.cpow_zero, mul_one]
    exact hu _
  exact ⟨⟨_, hK _ ⟨y, hy⟩ ⟨y⁻¹, by rw [map_inv₀, hy, Complex.inv_eq_conj h1]⟩⟩, rfl⟩

theorem valuesIn_of_isGal {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime]
    {O : Type} [CommRing O] [IsDomain O] [TopologicalSpace O] {art : Ideles E →* Gab E Ω} (ha : IsGlobalArtin art)
    {κ : FractionRing O →+* Qbar l} {ι : Qbar l ≃+* ℂ} {χ : Formalism.L2.Host.HChar E} {r : G E Ω →* Oˣ} (h : IsGal art κ ι χ 0 r) :
    χ.ValuesIn 0 (ι.toRingHom.comp κ) := fun v hv => by
  have e := h.frob ha (Or.inr rfl) hv (isPlaceOver_placeOf Ω v) (isFrob_frobOf Ω v)
  refine ⟨(algebraMap O _ (r (frobOf Ω v) : Oˣ))⁻¹, ?_⟩
  rw [map_inv₀]
  simp only [HChar.valTw, Complex.ofReal_zero, neg_zero, Complex.cpow_zero, mul_one]
  exact inv_eq_iff_eq_inv.2 e

variable {D : D7} {N : NData D.R D.host D.what₂}

theorem chi_unr {Z : LamDat D} (hZ : Z.Ok) (a : Fin D.R.m) {P : HeightOneSpectrum (𝓞 D.host.E)}
    (h : ¬ (below P).asIdeal ∣ cond0 D.host Z.w0) : (Z.chi a).UnrAt P := by
  refine (hZ.aux a).unr P (fun h4 => h ?_) fun e => h (e ▸ dvd_mul_left _ _)
  refine (dvd_pow ?_ two_ne_zero).mul_right _
  rw [Ideal.dvd_span_singleton, ExpCond.mem_below]
  push_cast
  rcases h4 with ⟨k, hk⟩ | hk | hk
  · fin_cases k
    · exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hk))
    · exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hk))
  · exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hk)
  · exact Ideal.mul_mem_left _ _ hk

theorem chi_teich {Z : LamDat D} (hZ : Z.Ok) (a : Fin D.R.m) {w w' : HeightOneSpectrum (𝓞 D.host.E)}
    (hw : OverP D.host D.host.pde w ∨ OverP D.host D.host.pde' w) (e : below w' = below w) (h : TeichTriv (Z.chi a) w') :
    TeichTriv (Z.chi a) w := by
  have : IsCMField D.host.E := D.host.isCMField_hostE
  obtain ⟨p, hp, hw⟩ : ∃ p ∈ [D.host.g 0, D.host.g 1, D.host.pde, D.host.pde', Z.q0], (p : 𝓞 D.host.E) ∈ w.asIdeal :=
    hw.elim (fun h => ⟨_, by simp, h⟩) fun h => ⟨_, by simp, h⟩
  obtain ⟨h1, -, h2, h3⟩ := hZ.places.splits p hp
  have hw' : (p : 𝓞 D.host.E) ∈ w'.asIdeal := by rwa [← ExpCond.mem_below, e, ExpCond.mem_below]
  exact teichTriv_of_split (hZ.aux a).triv (SplitBelow.splits_below_of_absNorm _ p h1 h2 h3 w hw) (e ▸ over_below w')
    (over_below w) h1 (h3 w' hw') (h3 w hw) h

theorem exists_reading (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) (e : FractionRing (X.O0 i) →+* Qbar (X.l i))
    (ι : Qbar (X.l i) ≃+* ℂ) (he : ∀ z : ℤ_[X.l i], e (algebraMap (X.O0 i) _ (algebraMap ℤ_[X.l i] (X.O0 i) z)) =
      algebraMap ℚ_[X.l i] (Qbar (X.l i)) (z : ℚ_[X.l i])) :
    ∃ ι' : ℂ →+* Kbar X i, ∀ b x, atSide X b ι' (sideIso ι b (e x)) = toBar X i x := by
  let _ : Algebra (FractionRing (X.O0 i)) (Qbar (X.l i)) := e.toAlgebra
  let _ : Algebra (FractionRing (X.O0 i)) (Kbar X i) := (toBar X i).toAlgebra
  have : Algebra.IsAlgebraic (FractionRing (X.O0 i)) (Qbar (X.l i)) := ⟨fun x => by
    have h1 : IsAlgebraic ℤ_[X.l i] x :=
      (IsFractionRing.isAlgebraic_iff ℤ_[X.l i] ℚ_[X.l i] _).2 (Algebra.IsAlgebraic.isAlgebraic x)
    refine h1.ringHom_of_comp_eq ((algebraMap (X.O0 i) _).comp (algebraMap ℤ_[X.l i] (X.O0 i))) (RingHom.id _)
      (fun a b hab => ?_) (RingHom.ext he)
    have := congrArg e hab
    rw [RingHom.comp_apply, RingHom.comp_apply, he, he] at this
    exact Subtype.ext ((algebraMap ℚ_[X.l i] (Qbar (X.l i))).injective this)⟩
  let J : Qbar (X.l i) →ₐ[FractionRing (X.O0 i)] Kbar X i := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hJ : ∀ x, J (e x) = toBar X i x := J.commutes
  refine ⟨J.toRingHom.comp ι.symm.toRingHom, fun b x => ?_⟩
  rw [← hJ]
  cases b
  · show J (ι.symm (starRingEnd ℂ (starRingEnd ℂ (ι _)))) = _
    rw [Complex.conj_conj, ι.symm_apply_apply]
  · exact congrArg J (ι.symm_apply_apply _)

theorem xv_mul_val (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) {e : FractionRing (X.O0 i) →+* Qbar (X.l i)}
    {ι : Qbar (X.l i) ≃+* ℂ} {ι' : ℂ →+* Kbar X i} (hι : ∀ x, ι' (ι (e x)) = toBar X i x)
    {art : Ideles D.host.E →* Gab D.host.E N.Om} (ha : IsGlobalArtin art) {χ : Formalism.L2.Host.HChar D.host.E}
    {n : (D.host.E →+* ℂ) → ℤ} {r : G D.host.E N.Om →* (X.O0 i)ˣ} (hr : IsGal art e ι χ n r) {lam : X.abelian₂ i}
    (hG : X.lamG i lam = (Units.map (algebraMap (X.O0 i) (X.O i)).toMonoidHom).comp r)
    {P : HeightOneSpectrum (𝓞 D.host.E)} (hP : P ∉ X.S0 i) (hu : χ.UnrAt P) :
    algebraMap (X.O i) (Kbar X i) (X.Xv i lam P) * ι' ((χ.val P : ℂˣ) : ℂ) = 1 := by
  obtain ⟨σ, hσ⟩ := exists_isFrob (N.plOm.2 P)
  have h3 := congrArg ι' (hr.frob ha (Or.inl fun h => hP (X.twistExcludedPlaces_contains_residueChar i h)) hu (N.plOm.2 P) hσ)
  rw [map_inv₀, toQ, RingHom.comp_apply, hι, toBar_algebraMap] at h3
  rw [X.Xv_def i lam P hP σ hσ, hG]
  exact (congrArg (· * _) h3).trans (inv_mul_cancel₀ ((map_ne_zero _).2 (Units.ne_zero _)))

abbrev Idx (R : Ranks) : Type := Fin R.m × Fin R.m × {s : ℕ // 1 ≤ s ∧ s ≤ BlochKatoReduction.Gen.NFun R + 1} × Bool

instance (n : ℕ) : Fintype {s : ℕ // 1 ≤ s ∧ s ≤ n} := Fintype.subtype (Finset.Icc 1 n) fun _ => Finset.mem_Icc

end Global

end GlobalTheory.LamTie.TrueList
end
end

noncomputable section

namespace GlobalTheory.LamTie.TrueList

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.ToricRational
open GlobalTheory.HeckeGal GlobalTheory.GalChar GlobalTheory.HeightCounting GlobalTheory.ToricDistribution

attribute [local instance 10000] GlobalTheory.GalChar.isTorsionFree_field

theorem exists_twL_full (hA : GlobalTheory.Published.GlobalArtinReciprocity) (hR : RatioConj) (D : D7) (N : NData D.R D.host D.what₂)
    (hE : IsEmpty N.Loc) (T : TwR D.LL0 N) (Z : LamDat D) (hZ : Z.Ok)
    (art : Ideles D.host.E →* Gab D.host.E N.Om) (ha : IsGlobalArtin art)
    (κ : ∀ i, FractionRing (T.O0 i) →+* Qbar (T.l i)) (ι : ∀ i, Qbar (T.l i) ≃+* ℂ)
    (hκ : ∀ i (z : ℤ_[T.l i]), κ i (algebraMap (T.O0 i) _ (algebraMap ℤ_[T.l i] (T.O0 i) z)) =
      algebraMap ℚ_[T.l i] (Qbar (T.l i)) (z : ℚ_[T.l i]))
    (hι : ∀ i (x : D.LL0), ι i (κ i (T.emb0 i x)) = D.what₂.embLL (x : D.what₂.LL))
    (hμ : ∀ i j, (Z.C.mu0 j).ValuesIn 0 ((ι i).toRingHom.comp (κ i)))
    (hχ : ∀ i a, (Z.chi a).ValuesIn 0 ((ι i).toRingHom.comp (κ i)))
    (hδ : ∀ i, IsGal art (κ i) (ι i) (Z.C.delAt (T.l i)) 0 (T.delta i))
    (hS : ∀ i P, (below P).asIdeal ∣ cond0 D.host Z.w0 → P ∈ T.S0 i)
    (hT : ∀ a w, OverP D.host D.host.pde w ∨ OverP D.host D.host.pde' w → ∃ w', below w' = below w ∧ TeichTriv (Z.chi a) w') :
    ∃ (L : TwL T) (e : ∀ i, L.abelian₂ i ≃ Idx D.R),
      (∀ i lam, L.jL i lam = (e i lam).1.1 + 1 ∧ L.sideL i lam = (e i lam).2.2.2 ∧ L.s2 i lam = 2 * ((e i lam).2.2.1.1 : ℤ) ∧
        (∃ n r, IsGal art (κ i) (sideIso (ι i) (e i lam).2.2.2) (Z.lam0 (T.l i) (e i lam).1 (e i lam).2.1) n r ∧
          L.lamG i lam = (Units.map (algebraMap (T.O0 i) (T.O i)).toMonoidHom).comp r) ∧
        ∀ P, L.qs i lam P = ((Ideal.absNorm P.asIdeal : ℕ) : FractionRing (T.O i)) ^ (-((e i lam).2.2.1.1 : ℤ))) ∧
      ∀ F : TwF T, IsLamTieFull (T.ntw hE F L) Z := by
  let C : GlobalTheory.Mem.Chr.HFrame D.host (fun j => eExp D j) :=
    ⟨Z.C.P, Z.C.W, Z.C.mu0, Z.C.eta, Z.C.chiPsi, Z.C.del, Z.C.del', Z.C.isMu0, Z.C.isEta, Z.C.isChi, Z.C.isDel, Z.C.isDel'⟩
  have hcu : ∀ i a P, P ∉ T.S0 i → (Z.chi a).UnrAt P := fun i a P hP => chi_unr hZ a fun h => hP (hS i P h)
  have hpD : ∀ i v, v ∈ T.pD i ↔ OverP D.host (if T.l i = D.host.pde then D.host.pde' else D.host.pde) v := fun i v => by
    rw [← Finset.mem_coe, T.pD_eq]; rfl
  have hlu : ∀ i j a P, P ∉ T.S0 i → (Z.lam0 (T.l i) j a).UnrAt P := fun i j a P hP =>
    (((Z.C.isMu0 j).unr P fun k hk => hP (T.placesOver_subset_exceptional i k hk)).mul
      ((inertialOrderFifteenChar_auxiliaryPrime_spec C (l := T.l i)).2.2.2.2.unr P fun hk => hP (T.primes_subset_exceptional i ((hpD i P).2 hk)))).mul (hcu i a P hP).inv
  choose K f f' hf hf' hK using fun i => exists_two_readings ((ι i).toRingHom.comp (κ i))
  have key := fun (i : T.Tw) (j a : Fin D.R.m) (b : Bool) =>
    hostHeckeFrame_toric_quotient_character C T.cc_cm ha (fun j τ => (D.hc _).e_int j) (T.l i) (T.O0 i) (T.twistBaseCoefficientRing_isAdic i) (κ i) (hκ i) (ι i) (K i)
      (K i).subtype (f i) (f' i) (hf i) (hf' i) (T.pD i) (T.pD_eq i) (T.delta i) (hδ i) (T.O i) (T.O_adic i) (T.O_l i) j b (Z.chi a) (Z.c a) (hZ.aux a).triv
      (by
        obtain ⟨n, hn, h⟩ := (hZ.aux a).inf
        have : n = fun τ => 2 * Z.c a τ := funext fun τ => by have := hn τ; beta_reduce at this; exact_mod_cast this
        exact this ▸ h)
      (fun v hv => by
        have h4 : OverP D.host D.host.pde v ∨ OverP D.host D.host.pde' v := by
          have := (hpD i v).1 hv
          split_ifs at this
          exacts [Or.inr this, Or.inl this]
        obtain ⟨w', e, h⟩ := hT a v h4
        exact chi_teich hZ a h4 e h)
      (valuesIn_of_unitary (hK i) (Z.C.isMu0 j).unitary (hμ i j))
      (valuesIn_of_unitary (hK i) (delAt_unitary_triv Z.C _).1 (valuesIn_of_isGal ha (hδ i)))
      (valuesIn_of_unitary (hK i) (hZ.aux a).unitary (hχ i a)) (T.S0 i) (T.twistExcludedPlaces_contains_residueChar i) (T.placesOver_subset_exceptional i) (T.primes_subset_exceptional i) (hcu i a)
  choose r g Xv h1 h2 h3 h4 h5 h6 h7 using key
  let L : (∀ i Q, Idx D.R → T.RCG i Q → FractionRing (T.O i)) → TwL T := fun th =>
    { abelian₂ := fun _ => Idx D.R
      jL := fun _ x => x.1.1 + 1
      sideL := fun _ x => x.2.2.2
      s2 := fun _ x => 2 * (x.2.2.1.1 : ℤ)
      jL_range := fun _ x => ⟨by omega, x.1.2⟩
      lamG := fun i x => g i x.1 x.2.1 x.2.2.2
      lamG_cont := fun i x => h3 i _ _ _
      lamG_unr := fun i x => h4 i _ _ _
      lamG_pD := fun i x => h5 i _ _ _
      lamG_anti := fun i x => h6 i _ _ _
      Xv := fun i x => Xv i x.1 x.2.1 x.2.2.2
      Xv_def := fun i x P hP => h7 i _ _ _ P hP _ (N.plOm.2 P)
      qs := fun i x P => ((Ideal.absNorm P.asIdeal : ℕ) : FractionRing (T.O i)) ^ (-(x.2.2.1.1 : ℤ))
      qs_sq := fun i x P _ => by rw [← zpow_natCast, ← zpow_mul]; congr 1; push_cast; ring
      qs_conj := fun i x P P' h => by
        rw [show Ideal.absNorm P'.asIdeal = Ideal.absNorm P.asIdeal from by
          simpa [Ideal.absNorm_eq_natCard, Formalism.ConjugateSelfDual.normV] using
            GlobalTheory.TwistDet.normV_conj h]
      th := th }
  have hcl : ∀ th i (x : Idx D.R), (L th).jL i x = x.1.1 + 1 ∧ (L th).sideL i x = x.2.2.2 ∧
      (L th).s2 i x = 2 * (x.2.2.1.1 : ℤ) ∧
      (∃ n r, IsGal art (κ i) (sideIso (ι i) x.2.2.2) (Z.lam0 (T.l i) x.1 x.2.1) n r ∧
        (L th).lamG i x = (Units.map (algebraMap (T.O0 i) (T.O i)).toMonoidHom).comp r) ∧
      ∀ P, (L th).qs i x P = ((Ideal.absNorm P.asIdeal : ℕ) : FractionRing (T.O i)) ^ (-(x.2.2.1.1 : ℤ)) := fun th i x => by
    refine ⟨rfl, rfl, rfl, ?_, fun _ => rfl⟩
    obtain ⟨n, hn⟩ := h1 i x.1 x.2.1 x.2.2.2
    exact ⟨n, _, hn, h2 i _ _ _⟩
  rcases isEmpty_or_nonempty (TwF T) with hF | ⟨⟨F₀⟩⟩
  · exact ⟨L fun _ _ _ _ => 0, fun _ => Equiv.refl _, hcl _, fun F => hF.elim F⟩
  let X₀ := T.ntw hE F₀ (L fun _ _ _ _ => 0)
  choose ι₀ hι₀ using fun i => exists_reading X₀ i (κ i) (ι i) (hκ i)
  have m0 : ∀ i, (∀ x : D.LL0, ι₀ i (D.what₂.embLL (x : D.what₂.LL)) = toBar X₀ i (T.emb0 i x)) ∧
      ∀ x : Idx D.R, IsLam X₀ Z i (atSide X₀ x.2.2.2 (ι₀ i)) x x.1 x.2.1 x.2.2.1.1 := fun i => by
    refine ⟨fun x => by rw [← hι i x]; exact hι₀ i true _, fun x => ⟨rfl, ⟨rfl, ?_, ?_⟩, fun P hP => ?_⟩⟩
    · exact_mod_cast x.2.2.1.2.1
    · exact_mod_cast x.2.2.1.2.2
    · obtain ⟨n, hn⟩ := h1 i x.1 x.2.1 x.2.2.2
      exact xv_mul_val X₀ i (hι₀ i x.2.2.2) ha hn (h2 i _ _ _) hP (hlu i _ _ P hP)
  have hL : ToricSumFormula := GlobalTheory.T.toric_sum_eq_hecke_L_value_mul_auxiliary_factors exists_isHeckeL_of_hasInf
  have tkey : ∀ i (x : Idx D.R), ∃ t : ∀ Q, T.RCG i Q → FractionRing (T.O i),
      ∀ th : ∀ i Q, X₀.abelian₂ i → X₀.RCG i Q → FractionRing (X₀.O i), (∀ Q, th i Q x = t Q) →
        IsThOf (setTh X₀ th) i (atSide X₀ x.2.2.2 (ι₀ i)) x (phi D.host) x.2.2.1.1 (Z.kap x.1 x.2.1 x.2.2.1.1)
          (cond0 D.host Z.w0) (Z.lam0 (T.l i) x.1 x.2.1) := fun i x => by
    have hl := (m0 i).2 x
    have hD := GlobalTheory.T.isHostDatum_kap_lam0_of_ok D Z hZ (T.l i) x.1 x.2.1 x.2.2.1.1 (by exact_mod_cast hl.2.1.2.1) hl.2.1.2.2
    exact exists_th_of hA hR hL (atSide_emb_mem (m0 i).1 _) hD (hS i) hl.2.2
  choose t ht using tkey
  let th : ∀ i Q, Idx D.R → T.RCG i Q → FractionRing (T.O i) := fun i Q x => t i x Q
  refine ⟨L th, fun _ => Equiv.refl _, hcl th, fun F => ?_⟩
  refine isLamTieFull_of_labels (fun _ x => x.1) (fun _ x => x.2.1) (fun _ x => x.2.2.1.1) (fun i _ => hS i)
    (fun i _ => ⟨ι₀ i, (m0 i).1, fun x => ⟨(m0 i).2 x, ht i x th fun _ => rfl⟩⟩)
    (fun i _ j a s b hs hs' => ⟨(j, a, ⟨s, hs, hs'⟩, b), rfl, rfl, rfl, rfl⟩)

end GlobalTheory.LamTie.TrueList
