module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.GaloisRepExistsTotallyRealGL2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.PlainRec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PAdicTorsionHoms.SplitTr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.ExtraV
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.ExistsPlaceCompletionIso
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PAdicTorsionHoms.PlainOf

@[expose] public section
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.fin UpperTheory.V.Pr.IsCD.isLocalHom
attribute [local instance 10000] DivisionSemiring.to_moduleIsTorsionFree

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.PsForm
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
open UpperTheory.Zero.LLC UpperTheory.V.Z.Win

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter ValuativeRel

namespace UpperTheory.Gal.SV

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem psForm {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a} {rc : IrrGL (k := w.adicCompletion E) → WD h}
    (L : LawsT a ha rc) {n : ℕ} (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (ξ : Fin n → (w.adicCompletion E)ˣ →* ℂˣ)
    (hξ : ∀ i, IsSmoothChar (ξ i)) (hs' : HasSupport σ.ρ (GlobalTheory.RoadU.chars ξ hξ)) (hu : GlobalTheory.RoadU.Unlinked (GlobalTheory.RoadU.chars ξ hξ)) :
    rc (algNorm σ) = (sumList (List.ofFn fun i => WD.lpOfChar h ((ξ i).comp a) (ha.smooth (hξ i)))).lpTw ((1 - (n : ℝ)) / 2) := by
  have : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  let k := w.adicCompletion E
  have hl : Unl (GroundTheory.LocalField.residueCard k) (GlobalTheory.RoadU.chars ξ hξ) := by
    intro χ ⟨c, hc⟩ χ' ⟨b, hb⟩ h1 hv
    apply hu _ hb _ hc
    rw [IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj]
    obtain ⟨⟨h₁, h₂⟩, eq_of_unram, -⟩ := polFacts k
    have hval : valuation k (unif k : k) = uniformizer k := by
      obtain ⟨y, hy⟩ := valuation_surjective (uniformizer k : ValueGroupWithZero k)
      exact le_antisymm (le_uniformizer_iff.2 h₁) (hy ▸ h₂ y (hy ▸ uniformizer_lt_one))
    have hA : ((absPow k 1 (unif k) : ℂˣ) : ℂ) * (resCard k : ℂ) = 1 := by
      have hq : (resCard k : ℂ) ≠ 0 := by
        have := Nat.card_pos (α := IsLocalRing.ResidueField 𝒪[k])
        exact_mod_cast this.ne'
      rw [val_absPow, Complex.cpow_one, GlobalTheory.GLDoubling.nabs_unif hval]
      push_cast
      exact inv_mul_cancel₀ hq
    refine eq_of_unram χ' (χ * absPow k 1) ?_ ?_
    · have he : χ' * (χ * absPow k 1)⁻¹ = (χ * χ'⁻¹)⁻¹ * (absPow k 1)⁻¹ := by
        simp only [mul_inv, inv_inv]
        rw [← mul_assoc, mul_comm χ' χ⁻¹]
      rw [he]
      exact isUnram_mul (isUnram_inv h1) (isUnram_inv (isUnram_absPow k 1))
    · refine Units.ext ?_
      change _ = (resCard k : ℂ) at hv
      rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val] at hv
      rw [← hv] at hA
      rw [MonoidHom.mul_apply, Units.val_mul]
      have h0 : ((χ' (unif k) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
      field_simp at hA
      rw [mul_comm, hA]
  obtain ⟨e⟩ := unlFull (w.adicCompletion E) n σ.V σ.ρ ξ hξ hs' hl
  let y : Fin n → IrrGL (k := k) := fun i => IrrGL.ofChar (ξ i) (hξ i)
  have hy : ∀ i, (y i).IsCusp := fun i => IrrGL.isCusp_ofChar _ _
  have hL : IsL ((List.ofFn fun i => Segment.single (y i) (hy i) : List (Segment k)) :
      Multiset (Segment k)) σ.ρ := by
    have hd : ∑ i, (y i).1 = n := by simp [y, IrrGL.ofChar]
    have hmem : ∀ i, y i ∈ GlobalTheory.RoadU.chars ξ hξ := fun i =>
      Multiset.mem_map_of_mem _ (Finset.mem_univ i)
    have hnl : ∀ i j, ¬ (Segment.single (y i) (hy i)).Linked (Segment.single (y j) (hy j)) := fun i j =>
      GlobalTheory.CompanionTheory.BZPair.not_linked_single (hy i) (hy j)
        (hu _ (hmem j) _ (hmem i)) (hu _ (hmem i) _ (hmem j))
    have hP : (prodIrr y hd).IsIrreducible :=
      GlobalTheory.RgGu.Holds.lUnlinkedIrr_holds k n n (fun i => Segment.single (y i) (hy i)) y hd hnl
        (fun i => (single_spec (hy i)).2.1)
    obtain ⟨p⟩ := (Placing.parInd_jac_placing k _ _ _ (Equiv.sigmaUnique (Fin n) fun _ => Fin 1)
      (stdBlocks (fun i => (y i).1) hd) _).1 (piTensor fun i => detRep (Fin 1) (ξ i))
    let q := multiProdEquiv (stdBlocks (fun i => (y i).1) hd) fun i =>
      equivRep (IrrRep.det (Fin 1) (ξ i) (hξ i))
    have hM : (multiProd (Equiv.sigmaUnique (Fin n) fun _ => Fin 1)
        fun i => detRep (Fin 1) (ξ i)).IsIrreducible :=
      GlobalTheory.Parabolic.isIrreducible_of_equiv (p.trans q).symm hP
    have hprin : (prinSeries ξ).IsIrreducible := GlobalTheory.Parabolic.isIrreducible_of_equiv e σ.irred
    obtain ⟨e₁⟩ := (GlobalTheory.PermPrin.isSubquotient_multiProd_prinSeries
      (Equiv.sigmaUnique (Fin n) fun _ => Fin 1) ξ).nonempty_equiv hM hprin
    have φ : σ.ρ.Equiv (prodIrr y hd) := (e.trans e₁).trans (p.trans q)
    exact ⟨n, y, hd, ⟨fun i => Segment.single (y i) (hy i), ⟨Fin.univ_val_map _, fun i j _ hp => hnl i j hp.1⟩,
      fun i => (single_spec (hy i)).2.1⟩, (isCosocle_self σ.irred).of_equiv (.refl _) φ⟩
  have hL' := hL.of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred)
  have hr : rc (IrrGL.of σ.ρ σ.smooth σ.irred) =
      sumList (List.ofFn fun i => WD.lpOfChar h ((ξ i).comp a) (ha.smooth (hξ i))) := by
    rw [L.langlands _ _ hL', segSum, List.map_ofFn]
    congr 1
    refine List.ofFn_inj.mpr (funext fun i => ?_)
    simp only [Function.comp_apply, y, Segment.single, Segment.first_ofFirst, Segment.len_ofFirst, Nat.cast_one, sub_self,
      zero_div, WD.lpTw_zero, GlobalTheory.LocLanglands.Test.lpChar_lpSp_one, L.one]
  rw [algNorm, L.nu, hr]

open scoped commutatorElement in
theorem gdOf : GdOf := by
  intro E Ω _ _ _ _ _ A w h rc ⟨a, ha, L⟩ n σ hP
  obtain ⟨ξ, hξ, hs, hu⟩ := GlobalTheory.RoadU.plainTor_exists_chars _ _ hP
  have hA := psForm L σ ξ hξ (hs.of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred).symm) hu
  refine ⟨?_, ?_⟩
  · have hd : (rc (algNorm σ)).lpDim = n := by
      rw [L.dim]
      rfl
    intro s t
    have comm_one {G H : Type} [Group G] [CommGroup H] (f : G →* H) (s t : G) :
        f ⁅s, t⁆ = 1 := by
      rw [map_commutatorElement]
      exact (Commute.all _ _).commutator_eq
    show WD.charPol _ _ = _
    rw [hd, hA, GlobalTheory.GalCut.AwayMono.charPol_lpTw, comm_one,
      GlobalTheory.LocLanglands.CuspExt.charPol_sumList, List.map_ofFn]
    have hchar (i : Fin n) :
        (WD.lpOfChar h ((ξ i).comp a) (ha.smooth (hξ i))).charPol ⁅s, t⁆ = X - 1 := by
      rw [WD.lpOfChar, WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd]
      simp only [comm_one]
      simp
    simp [hchar, List.prod_ofFn]
  · rw [hA, WD.monomial_twist_iff]
    have sum_mono0 (l : List (WD h)) (hl : ∀ z ∈ l, z.mono0) : (sumList l).mono0 := by
      induction l with
      | nil =>
        show (WD.lpZero (h := h)).mono0
        rw [WD.lpZero, WD.monodromyZero_ofWeilDeligneRepClass_iff]
        rfl
      | cons b l ih =>
        show (WD.lpSum b (sumList l)).mono0
        exact (WD.monomial_sum_iff _ _).2 ⟨hl b (by simp), ih fun z hz => hl z (by simp [hz])⟩
    refine sum_mono0 _ fun z hz => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hz
    rw [WD.lpOfChar, WD.monodromyZero_ofWeilDeligneRepClass_iff]
    rfl

theorem recTr (hG : GlobalTheory.Published.GlobalArtinReciprocity) {K : Type} [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
    {u : HeightOneSpectrum (𝓞 K)} {h' : IsPlaceOver A u} {j : E →+* K} {i : w.adicCompletion E ≃+* u.adicCompletion K}
    (P : PlaceIso A w A u (RingEquiv.refl Ω) j i) {n : ℕ} (σ : SmIrr (GL (Fin n) (w.adicCompletion E)))
    (σ' : SmIrr (GL (Fin n) (u.adicCompletion K))) (e : σ.V ≃ₗ[ℂ] σ'.V)
    (he : ∀ g x, e (σ.ρ g x) = σ'.ρ (Matrix.GeneralLinearGroup.map i.toRingHom g) (e x))
    {rc : IrrGL (k := w.adicCompletion E) → WD h} {rc' : IrrGL (k := u.adicCompletion K) → WD h'} (hrc : IsRecT h rc) (hrc' : IsRecT h' rc')
    (hP : GlobalTheory.RoadU.PlainTor (IrrGL.of σ.ρ σ.smooth σ.irred)) :
    WDRel (RingEquiv.refl Ω) (rc (algNorm σ)) (rc' (algNorm σ')) := by
  obtain ⟨a, ha, L⟩ := hrc
  obtain ⟨a', ha', L'⟩ := hrc'
  have hi := P.cont
  have hi' : Continuous i.symm := GlobalTheory.LocalFieldIso.continuous_symm i hi
  obtain ⟨ξ, hξ, hs, hu⟩ := GlobalTheory.RoadU.plainTor_exists_chars _ _ hP
  have hρ : HasSupport σ.ρ (GlobalTheory.RoadU.chars ξ hξ) := hs.of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred).symm
  let ξ' : Fin n → (u.adicCompletion K)ˣ →* ℂˣ := fun k => (ξ k).comp (Units.map i.symm.toRingHom.toMonoidHom)
  have hξ' : ∀ k, IsSmoothChar (ξ' k) := fun k =>
    IsOpen.preimage (f := Units.map i.symm.toRingHom.toMonoidHom) (Continuous.units_map _ hi') (hξ k)
  have h5 : ∀ t, Units.map i.symm.toRingHom.toMonoidHom (Units.map i.toRingHom.toMonoidHom t) = t := fun t =>
    Units.ext (i.symm_apply_apply _)
  have hg : ∀ g : GL (Fin n) (u.adicCompletion K),
      Matrix.GeneralLinearGroup.map i.toRingHom (Matrix.GeneralLinearGroup.map i.symm.toRingHom g) = g := fun g =>
    Units.ext (Matrix.ext fun _ _ => i.apply_symm_apply _)
  let φ : Representation.Equiv (σ.ρ.comp (Matrix.GeneralLinearGroup.map (n := Fin n) i.symm.toRingHom)) σ'.ρ :=
    GlobalTheory.LocGL.equivOfBijective ⟨e.toLinearMap, fun g => LinearMap.ext fun x => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply]
      change e (σ.ρ (Matrix.GeneralLinearGroup.map i.symm.toRingHom g) x) = σ'.ρ g (e x)
      rw [he, hg]⟩ e.bijective
  have h3 := (GlobalTheory.SuppIne.hasSupport_comp i hi hi' hρ).of_equiv φ
  have h4 : (GlobalTheory.RoadU.chars ξ hξ).map (GlobalTheory.SuppIne.trGL i hi') = GlobalTheory.RoadU.chars ξ' hξ' := by
    rw [GlobalTheory.RoadU.chars, GlobalTheory.RoadU.chars, Multiset.map_map]
    exact Multiset.map_congr rfl fun k _ => GlobalTheory.DegOneChar.trGL_ofChar i hi' (ξ k) (hξ k) (hξ' k)
  rw [h4] at h3
  have hu' : GlobalTheory.RoadU.Unlinked (GlobalTheory.RoadU.chars ξ' hξ') := by
    intro y hy z hz heq
    obtain ⟨k, -, rfl⟩ := Multiset.mem_map.1 hy
    obtain ⟨m, -, rfl⟩ := Multiset.mem_map.1 hz
    rw [IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj] at heq
    refine hu _ (Multiset.mem_map_of_mem _ (Finset.mem_univ_val k)) _ (Multiset.mem_map_of_mem _ (Finset.mem_univ_val m)) ?_
    rw [IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj]
    refine MonoidHom.ext fun t => ?_
    have h6 := DFunLike.congr_fun heq (Units.map i.toRingHom.toMonoidHom t)
    rw [MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, h5, GlobalTheory.LocalFieldIso.absPow_map i hi] at h6
    exact h6
  obtain ⟨S, hS, -, h0, hsum, -, hSt, -, -, hch⟩ := GlobalTheory.WDTransport.exists_equiv_wd E Ω A w h K Ω A u h' (RingEquiv.refl Ω) j i P
  have hl : ∀ l : List (WD h), S (sumList l) = sumList (l.map S) := fun l => by
    induction l with
    | nil => exact h0
    | cons b l ih => exact (hsum b (sumList l)).trans (congrArg (WD.lpSum (S b)) ih)
  refine (hS _ _).2 ?_
  rw [psForm L σ ξ hξ hρ hu, psForm L' σ' ξ' hξ' h3 hu', hSt, hl, List.map_ofFn]
  congr 2
  refine List.ofFn_inj.mpr (funext fun k => hch _ _ _ _ fun s s' hss => ?_)
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply,
    GlobalTheory.T.localArtinMap_unique_transport_placeIso hG GlobalTheory.Published.chevalleyUnits' E Ω A w h K Ω A u h' _ j i P a a' ha ha' s s' hss]
  exact (congrArg (ξ k) (h5 _)).symm

def RatioT : Prop :=
  ∀ (K Ω : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 K)) (h : IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion K) → WD h), IsRecT h rc →
    ∀ (a : ℕ) (π : CuspSub K a) (t : ℝ), WinAt π t w → ∀ σ, π.IsLocComp w σ → UpperTheory.GalN.V.RatioW (rc (algNorm σ))

end UpperTheory.Gal.SV
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.UnrAtOfIsoTwist
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
open UpperTheory.Zero.LLC UpperTheory.V.Z.Win

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace UpperTheory.Gal.SV

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

private theorem sat_equiv {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V} {σ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) W}
    {α : Fin n → ℂˣ} (φ : π.Equiv σ) (h : HasSatake π α) : HasSatake σ α := by
  refine ⟨GlobalTheory.Parabolic.isIrreducible_of_equiv φ h.1, ?_,
    (IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective).trans h.2.2⟩
  obtain ⟨v, hv, h0⟩ := (Submodule.ne_bot_iff _).1 h.2.1
  refine (Submodule.ne_bot_iff _).2 ⟨φ v, fun g => ?_, fun e => h0 (φ.toLinearEquiv.injective (by simpa using e))⟩
  have e : φ (π g v) = σ g (φ v) := φ.toIntertwiningMap.isIntertwining _ _ g v
  rw [← e, hv g, map_smul]

theorem hasSatake_of {n : ℕ} (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) {B : Multiset ℂˣ} (hB : GlobalTheory.LFun.HasSatGL w σ.ρ B) :
    ∃ α : Fin n → ℂˣ, B = Finset.univ.val.map α ∧ HasSatake σ.ρ α := by
  obtain ⟨l, rfl⟩ := Quot.exists_rep B
  have hl : l.length = n := by simpa using hB.card
  subst hl
  have e : (Quot.mk _ l : Multiset ℂˣ) = Finset.univ.val.map l.get := by
    rw [Fin.univ_val_map, List.ofFn_get]; rfl
  obtain ⟨x, hx⟩ := hB.exists_vec
  exact ⟨l.get, e, GlobalTheory.CompanionTheory.SatComp.hasSatake_of_isSatVecGL ⟨σ.smooth, σ.irred⟩ _ (e ▸ hx)⟩

theorem rec_diag {rc : IrrGL (k := w.adicCompletion E) → WD h} (H : IsRecT h rc) {n : ℕ}
    (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (B : Multiset ℂˣ) (hB : GlobalTheory.LFun.HasSatGL w σ.ρ B) :
    ∃ α : Fin n → ℂˣ, B = Finset.univ.val.map α ∧
      rc (algNorm σ) = WD.mk (WDRep.diag h fun i => (α i)⁻¹ * qPow w ((1 - (n : ℝ)) / 2)) := by
  obtain ⟨α, e0, hα⟩ := hasSatake_of σ hB
  obtain ⟨a, ha, ε, L⟩ := extraV E Ω A w h rc H
  have q := IrrGL.equivOf σ.ρ σ.smooth σ.irred
  have e : rc (IrrGL.of σ.ρ σ.smooth σ.irred) = WD.mk (WDRep.diag h fun i => (α i)⁻¹) :=
    L.sat (IrrGL.of σ.ρ σ.smooth σ.irred) α (sat_equiv q hα)
  refine ⟨α, e0, ?_⟩
  rw [algNorm, L.nu_eq, e, WD.lpTw_mk]
  refine WD.sound ⟨.refl _ _, fun g v => funext fun i => ?_, fun v => rfl⟩
  simp [mul_zpow, mul_comm, mul_left_comm, mul_assoc]

theorem frob_of {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {n : ℕ} {r : G E Ω →* GL (Fin n) (Qbar l)}
    (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) {B : Multiset ℂˣ}
    (hB : GlobalTheory.LFun.HasSatGL w σ.ρ B)
    (H : ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion E) → WD h), IsRecT h rc →
      IsWDOf ι r (rc (algNorm σ))) : FrobEig ι r w (algSat n (normV w) B) := by
  intro A h
  obtain ⟨rc, hrec⟩ := recTExists E Ω A w h
  obtain ⟨α, rfl, e⟩ := rec_diag hrec σ B hB
  have hx := H A h rc hrec
  have hw := (hx.wdOf_eq hl).trans e
  obtain ⟨t, ht, φ, hφ, N, a, hN, -⟩ := hx
  refine ⟨(hN.unr_wdOf_iff hl ht ι).1 (by rw [hw, WD.unr_mk]; exact WDRep.unr_diag _), fun s hs => ?_⟩
  have hd : deg (⟨s, mem_Weil_of_isFrob h hs⟩ : Weil h) = 1 := deg_eq_one_iff.2 hs
  have := hN.charPol_wdOf hl ht ι (⟨s, mem_Weil_of_isFrob h hs⟩ : Weil h)⁻¹
  rw [hw, WD.charPol_mk, WDRep.diag_ρ, charpoly_diagEnd, deg_inv, hd] at this
  refine this.symm.trans ?_
  simp only [GlobalTheory.SatFrobLit.val_inv_eq, algSat, Multiset.map_map, Multiset.pure_def, Multiset.bind_def, Multiset.bind_singleton]
  rfl

theorem good_of_fixed {n : ℕ} (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (hf : HasFixed σ.ρ (GlobalTheory.LFun.KGL w (n := n))) :
    Good (IrrGL.of σ.ρ σ.smooth σ.irred) ∧ IsSpherical (IrrGL.of σ.ρ σ.smooth σ.irred).rep := by
  obtain ⟨B, hB⟩ := (GlobalTheory.T.satakeParameters_local E n w σ).1 hf
  obtain ⟨α, -, hα⟩ := hasSatake_of σ hB
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  have q := IrrGL.equivOf σ.ρ σ.smooth σ.irred
  have k := GlobalTheory.LocLanglands.hasSupport_of_isSubquotient_prinSeries (w.adicCompletion E) n (fun i => unrChar _ (α i))
    (fun i => isSmoothChar_of_isUnram (isUnram_unrChar _ (α i))) ⟨σ.V, σ.ρ, σ.smooth, σ.irred⟩ hα.2.2
  refine ⟨⟨_, HasSupport.of_equiv k q, fun y hy => Or.inl ?_⟩, (sat_equiv q hα).2.1⟩
  obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hy
  rfl


open GlobalTheory.RealGal.TwistUnr in
theorem unrAt_of_isoTwist (hA : AdmissibleReal) (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ) (ha : 1 ≤ a)
    (π : TR.CuspSub F a) (η : HChar F) (hT : IsoTwist π η) (u : HeightOneSpectrum (𝓞 F)) (B : Multiset ℂˣ) (hB : π.HasSat u B) :
    η.UnrAt u := by
  have hL := GlobalTheory.T.local_global_compatibility_real hA
  obtain ⟨σ, hσ⟩ := (hL F a π u).1
  have hσ' := isLocComp_twist hT hσ
  obtain ⟨A, hAu⟩ := exists_isPlaceOver (AlgebraicClosure F) u
  obtain ⟨rc, H⟩ := recTExists F (AlgebraicClosure F) A u hAu
  obtain ⟨ar, har, ε, LL⟩ := extraV _ _ A u hAu rc H
  obtain ⟨g1, s1⟩ := good_of_fixed σ (hasFixed_of_hasSat hL hB hσ)
  have u1 := (LL.sph _).1 s1
  have u2 := (LL.sph _).1 (good_of_fixed _ (hasFixed_of_hasSat hL hB hσ')).2
  have hs := GlobalTheory.HeckeComp.smooth_loc η u
  have e : rc (cls (ParLaws.toRep (σ.twist (GlobalTheory.CuspRep.CuspSub.locDet a η u) (TR.CuspSub.isOpen_ker_locDet η u)))) =
      (rc (cls (ParLaws.toRep σ))).lpChar (rc (.ofChar (η.loc u) hs)) := by
    refine Eq.trans ?_ (LL.twist _ _ hs g1)
    exact congrArg _ (IrrGL.tw_of σ.ρ σ.smooth σ.irred _ _).symm
  replace u2 : (rc (cls (ParLaws.toRep (σ.twist (GlobalTheory.CuspRep.CuspSub.locDet a η u) (TR.CuspSub.isOpen_ker_locDet η u))))).unr := u2
  rw [e, LL.one] at u2
  have hd : 1 ≤ (rc (cls (ParLaws.toRep σ))).lpDim := by rw [LL.dim]; exact ha
  have hi := ine_trivial u1 hd _ u2
  have hU : (WD.lpOfChar hAu ((η.loc u).comp ar) (har.smooth hs)).unr := by
    rw [WD.lpOfChar, WD.unr_mk]
    refine ⟨rfl, fun s => LinearMap.ext fun v => funext fun i => ?_⟩
    have := hi s
    simp [this]
  have hU' := (GlobalTheory.LocLanglands.Test.unr_lpOfChar_iff har hs).1 hU
  intro x hx
  refine hU' x ?_
  have h0 : Valued.v (x : u.adicCompletion F) ≠ 0 := by simp
  rw [← GlobalTheory.SmGL.ord_eq_zero_iff, GlobalTheory.SmGL.SphCompletion.ord_completion, neg_eq_zero]
  unfold IsUnitAt at hx
  rw [hx, WithZero.log_one]

end UpperTheory.Gal.SV
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.RatioT
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
open UpperTheory.Zero.LLC UpperTheory.V.Z.Win

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter ValuativeRel

namespace UpperTheory.Gal.SV.GlobalSectionsBijection

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem ord_unif : GlobalTheory.SmGL.ord k (UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.unif k) = 1 := by
  have hs := (UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.polFacts k).1
  obtain ⟨p, hp⟩ := valuation_surjective (uniformizer k : ValueGroupWithZero k)
  exact ord_eq_one (le_antisymm (le_uniformizer_iff.2 hs.1) (hp ▸ hs.2 p (hp ▸ uniformizer_lt_one)))

private theorem norm_neg_one (ξ : kˣ →* ℂˣ) (hξ : IsSmoothChar ξ) {x : kˣ} (hx : GlobalTheory.SmGL.ord k x = -1) :
    ‖((ξ x : ℂˣ) : ℂ)‖ = ‖((ξ (UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.unif k) : ℂˣ) : ℂ)‖⁻¹ := by
  have hu : GlobalTheory.SmGL.ord k (x * UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.unif k) = 0 := by
    rw [ord_mul, hx, ord_unif]
    simp
  have h1 := PositivityTheory.RgUd.Exp.Rpow.norm_eq_one_of_valuation_eq_one ξ hξ (ord_eq_zero_iff.1 hu)
  rw [map_mul, Units.val_mul, norm_mul] at h1
  exact eq_inv_of_mul_eq_one_left h1

end Loc

section WD

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

private theorem eig_sum {n : ℕ} (c : Fin n → Weil h →* ℂˣ) (hc : ∀ i, GlobalTheory.WeilDeligne.IsSmooth (c i)) (s : ℝ)
    {φ : ↥(Weil h)} (hφ : deg φ = 1) {α : ℂ}
    (hα : α ∈ ((sumList (List.ofFn fun i => WD.lpOfChar h (c i) (hc i))).lpTw s).eig φ) :
    ∃ i, α = ((c i φ : ℂˣ) : ℂ) * ((normV w : ℕ) : ℂ) ^ ((s : ℝ) : ℂ) := by
  rw [GlobalTheory.RowTie.EigTwist.eig_lpTw _ hφ s, Multiset.mem_map] at hα
  obtain ⟨y, hy, rfl⟩ := hα
  have h1 : ∀ i, (WD.lpOfChar h (c i) (hc i)).charPol φ = X - C ((c i φ : ℂˣ) : ℂ) := fun i => by
    rw [WD.lpOfChar, WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd]
    simp
  have h2 := Polynomial.isRoot_of_mem_roots hy
  rw [GlobalTheory.LocLanglands.CuspExt.charPol_sumList, List.map_ofFn] at h2
  have h3 : (List.ofFn ((fun y : WD h => y.charPol φ) ∘ fun i => WD.lpOfChar h (c i) (hc i))).prod =
      ∏ i, (X - C ((c i φ : ℂˣ) : ℂ)) := by
    rw [List.prod_ofFn]
    exact Finset.prod_congr rfl fun i _ => h1 i
  rw [h3, Polynomial.IsRoot.def, Polynomial.eval_prod, Finset.prod_eq_zero_iff] at h2
  obtain ⟨i, -, hi⟩ := h2
  refine ⟨i, ?_⟩
  simp only [eval_sub, eval_X, eval_C] at hi
  rw [sub_eq_zero.1 hi]

end WD

end UpperTheory.Gal.SV.GlobalSectionsBijection

open UpperTheory.Gal.SV.GlobalSectionsBijection in
theorem UpperTheory.Gal.SV.ratioT :
    UpperTheory.Gal.SV.RatioT := by
  intro K Ω _ _ _ _ _ _ A w h rc ⟨a, ha, L⟩ n π t hw σ hσ φ hφ α hα β hβ
  have hP := (UpperTheory.V.Z.Win.plainRec K Ω A w h rc ⟨a, ha, L⟩ n π t hw σ hσ).1
  obtain ⟨ξ, hξ, hs, hu⟩ := GlobalTheory.RoadU.plainTor_exists_chars _ _ hP
  have hs' : HasSupport σ.ρ (GlobalTheory.RoadU.chars ξ hξ) := hs.of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred).symm
  have hA := psForm L σ ξ hξ hs' hu
  rw [hA] at hα hβ
  obtain ⟨i, rfl⟩ := eig_sum _ _ _ hφ hα
  obtain ⟨j, rfl⟩ := eig_sum _ _ _ hφ hβ
  have hq : ((normV w : ℕ) : ℝ) = (Ideal.absNorm w.asIdeal : ℝ) := by
    simp [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hq1 : (1 : ℝ) < ((normV w : ℕ) : ℝ) := by exact_mod_cast GlobalTheory.WeilDeligne.one_lt_normV w
  have hord : GlobalTheory.SmGL.ord (w.adicCompletion K) (a φ) = -1 := by rw [ha.ord_eq φ, hφ]
  have hwin : ∀ m, ((normV w : ℕ) : ℝ) ^ (t - 1 / 2) < ‖((ξ m (UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.unif (w.adicCompletion K)) : ℂˣ) : ℂ)‖ ∧
      ‖((ξ m (UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.unif (w.adicCompletion K)) : ℂˣ) : ℂ)‖ < ((normV w : ℕ) : ℝ) ^ (t + 1 / 2) := fun m => by
    rw [hq]
    exact hw.2 _ ⟨σ, hσ, hs'⟩ (ξ m) ⟨hξ m, Multiset.mem_map_of_mem _ (Finset.mem_univ_val m)⟩
  have hbi := (Real.rpow_pos_of_pos (by linarith) _).trans (hwin i).1
  have hbj := (Real.rpow_pos_of_pos (by linarith) _).trans (hwin j).1
  have hlt : ‖((ξ j (UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.unif (w.adicCompletion K)) : ℂˣ) : ℂ)‖ <
      ‖((ξ i (UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.unif (w.adicCompletion K)) : ℂˣ) : ℂ)‖ * ((normV w : ℕ) : ℝ) := by
    have e : ((normV w : ℕ) : ℝ) ^ (t + 1 / 2) = ((normV w : ℕ) : ℝ) ^ (t - 1 / 2) * ((normV w : ℕ) : ℝ) := by
      rw [← Real.rpow_add_one (by linarith)]
      congr 1
      ring
    calc _ < _ := (hwin j).2
      _ = _ := e
      _ < _ := mul_lt_mul_of_pos_right (hwin i).1 (by linarith)
  have hc : 0 < ‖((normV w : ℕ) : ℂ) ^ ((((1 - (n : ℝ)) / 2 : ℝ)) : ℂ)‖ := by
    refine norm_pos_iff.2 ?_
    rw [Ne, Complex.cpow_eq_zero_iff]
    intro e
    have : ((normV w : ℕ) : ℝ) = 0 := by exact_mod_cast e.1
    linarith
  simp only [MonoidHom.comp_apply]
  rw [norm_mul, norm_mul, norm_neg_one _ (hξ i) hord, norm_neg_one _ (hξ j) hord, ← mul_assoc]
  refine mul_lt_mul_of_pos_right ?_ hc
  rw [← div_eq_mul_inv, lt_div_iff₀ hbj, inv_mul_lt_iff₀ hbi]
  exact hlt
end
end
