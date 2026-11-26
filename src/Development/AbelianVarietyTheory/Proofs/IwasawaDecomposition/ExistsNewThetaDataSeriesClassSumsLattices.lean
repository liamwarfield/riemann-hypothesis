module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.YsOfFi
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSetup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReadingRealSide

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSetupPinnedCh
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodSetupCountEqZeroOffBadPlaces
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin IsAlgPos)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.TwInputs.SetupPin

variable {D : D7}

theorem goodSetup_badPlaces_conj (F : TwFrameC D) {low : Finset ℕ} (T : TwistFrameLowIndexCompatibility D F low) :
    ∀ i, ∀ P ∈ D.ntw.S0 i, ∀ P', Formalism.BasicNotions.IsConjPl D.host P P' → P' ∈ D.ntw.S0 i := by
  intro i P hP P' hc
  have hP' : P ∈ (D.ntw.S0 i : Set (HeightOneSpectrum (𝓞 D.host.E))) := hP
  rw [T.ringSpec_excludedPlaces_eq i] at hP'
  show P' ∈ (D.ntw.S0 i : Set (HeightOneSpectrum (𝓞 D.host.E)))
  rw [T.ringSpec_excludedPlaces_eq i]
  rcases hP' with (((h | h) | h) | h) | h
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Formalism.L2.placesOver_conj D _ h hc))))
  · obtain ⟨k, hk⟩ := Set.mem_iUnion.1 h
    exact Or.inl (Or.inl (Or.inl (Or.inr (Set.mem_iUnion.2 ⟨k, Formalism.L2.placesOver_conj D _ hk hc⟩))))
  · exact Or.inl (Or.inl (Or.inr (Formalism.L2.placesOver_conj D _ h hc)))
  · exact Or.inl (Or.inr (Formalism.L2.placesOver_conj D _ h hc))
  · exact Or.inr (T.concreteTwistFrame_extraExcludedPlaces_conj i P P' h hc)

theorem goodSetup_placesOverTwo_subset (F : TwFrameC D) {low : Finset ℕ} (T : TwistFrameLowIndexCompatibility D F low) (h2 : 2 ∈ low) :
    ∀ i, placesOver D.host.E 2 ⊆ ↑(D.ntw.S0 i) := by
  intro i P hP
  show P ∈ (D.ntw.S0 i : Set (HeightOneSpectrum (𝓞 D.host.E)))
  rw [T.ringSpec_excludedPlaces_eq i]
  exact Or.inr (T.concreteTwistFrame_extraExcluded_over_smallPrimes i 2 h2 hP)

theorem q_dvd_discr (D : D7) : D.host.q ∣ (NumberField.discr D.host.E).natAbs :=
  Int.natCast_dvd.1 D.host.q_dvd_discr

theorem goodSetup_count_eq_zero_off_badPlaces (F : TwFrameC D) {low : Finset ℕ} (T : TwistFrameLowIndexCompatibility D F low) (h2 : 2 ∈ low)
    (hd : (NumberField.discr D.host.E).natAbs.primeFactors ⊆ low) (hc : (Ideal.absNorm D.host.ccK).primeFactors ⊆ low) :
    ∀ i P, P ∉ D.ntw.S0 i → FractionalIdeal.count D.host.E P D.host.AA = 0 := by
  intro i P hP
  by_contra hA
  have hb : ((GlobalTheory.HalfCompare.badInt D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
    by_contra hb
    exact hA (GlobalTheory.HalfCompare.primeToAA_of_not_mem hb)
  obtain ⟨p, hp, hpP⟩ := GlobalTheory.HalfCompare.exists_prime_under P
  have hdiv : p ∣ GlobalTheory.HalfCompare.badInt D := (hpP _).1 hb
  have hlow : p ∈ low := by
    unfold GlobalTheory.HalfCompare.badInt at hdiv
    rcases hp.dvd_mul.1 hdiv with h | h
    · exact hd (Nat.mem_primeFactors.2 ⟨hp,
        Int.natCast_dvd.1 ((D.host.dvd_discr_iff_dvd_condN hp).2 (h.mul_right D.host.d)),
        Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero _)⟩)
    · exact hc (Nat.mem_primeFactors.2 ⟨hp, h, by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact D.host.ccK_ne_bot⟩)
  apply hP
  show P ∈ (D.ntw.S0 i : Set (HeightOneSpectrum (𝓞 D.host.E)))
  rw [T.ringSpec_excludedPlaces_eq i]
  exact Or.inr (T.concreteTwistFrame_extraExcluded_over_smallPrimes i p hlow ((hpP p).2 dvd_rfl))

theorem mk_fractionRing_le {R : Type} [CommRing R] [IsDomain R] (h : Cardinal.mk R ≤ Cardinal.continuum) :
    Cardinal.mk (FractionRing R) ≤ Cardinal.continuum := by
  have hs : Function.Surjective
      (fun p : R × nonZeroDivisors R => IsLocalization.mk' (FractionRing R) p.1 p.2) := fun z => by
    obtain ⟨⟨x, y⟩, hxy⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) z
    exact ⟨(x, y), hxy⟩
  refine (Cardinal.mk_le_of_surjective hs).trans ?_
  rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
  calc Cardinal.mk R * Cardinal.mk (nonZeroDivisors R) ≤ Cardinal.continuum * Cardinal.continuum :=
        mul_le_mul' h ((Cardinal.mk_subtype_le _).trans h)
    _ = Cardinal.continuum := Cardinal.continuum_mul_self

theorem mk_frac_Ok (F : TwFrameC D) : ∀ i k, Cardinal.mk (FractionRing (D.ntw.Ok i k)) ≤ Cardinal.continuum := by
  intro i k
  haveI := D.ntw.lPrime i
  apply mk_fractionRing_le
  have hinj : Function.Injective (fun x : D.ntw.Ok i k => ((F.eOk i k x : _) : ℂ_[D.ntw.l i])) :=
    Subtype.val_injective.comp (F.eOk i k).injective
  refine (Cardinal.mk_le_of_injective hinj).trans ?_
  rw [(GlobalTheory.PadicCard.card_padicAlgCl_padicComplex (D.ntw.l i)).2, Cardinal.mk_complex]

theorem continuous_comp_of_isOpen_ker {Γ B Y : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group B]
    [TopologicalSpace Y] (φ : Γ →* B) (f : B → Y) (h : IsOpen (φ.ker : Set Γ)) : Continuous (f ∘ φ) := by
  have hloc : IsLocallyConstant (f ∘ φ) := by
    intro s
    rw [isOpen_iff_forall_mem_open]
    intro g hg
    refine ⟨(fun g' => g⁻¹ * g') ⁻¹' (φ.ker : Set Γ), fun g' hg' => ?_,
      h.preimage (continuous_const.mul continuous_id), ?_⟩
    · have h1 : φ (g⁻¹ * g') = 1 := hg'
      rw [map_mul, map_inv, inv_mul_eq_one] at h1
      show f (φ g') ∈ s
      rw [← h1]
      exact hg
    · show φ (g⁻¹ * g) = 1
      rw [inv_mul_cancel, map_one]
  exact hloc.continuous

theorem delAt_alg (C : CharFrame D) (l : ℕ) : IsAlgPos (C.delAt l) 0 := by
  unfold CharFrame.delAt
  split_ifs
  · obtain ⟨n, h0, h⟩ := C.isDel'.fin
    exact GlobalTheory.HeckeGal.isAlgPos_zero_of_orderDvd h0 h
  · obtain ⟨n, h0, h⟩ := C.isDel.fin
    exact GlobalTheory.HeckeGal.isAlgPos_zero_of_orderDvd h0 h

end GlobalTheory.TwInputs.SetupPin

namespace GlobalTheory.TwInputs.SetupPin

variable {D : D7}

theorem exists_art_gal (hA : GlobalTheory.Published.GlobalArtinReciprocity) (cf : CharFrame D) (hR : DeltaRead D cf) :
    ∃ art : Ideles D.host.E →* Gab D.host.E D.nd.Om, IsGlobalArtin art ∧ ∀ i b,
      ∃ (κ : FractionRing (D.ntw.O0 i) →+* Qbar (D.ntw.l i)) (ι : Qbar (D.ntw.l i) ≃+* ℂ),
        (∀ x, ι (κ ((if b then D.ntw.emb0 i else D.ntw.emb0b i) x)) = embLL0 D x) ∧
        GlobalTheory.GalChar.IsGal art κ ι (cf.delAt (D.ntw.l i)) (fun _ => 0) (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)) := by
  obtain ⟨art, hart⟩ := hA D.host.E D.nd.Om
  refine ⟨art, hart, fun i b => ?_⟩
  haveI := D.ntw.lPrime i
  obtain ⟨ρ⟩ := GlobalTheory.Triple.Reading.nonempty (X := D.ntw) i b
  have hker : IsOpen ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker : Set (G D.host.E D.nd.Om)) := by
    have e : ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker : Set (G D.host.E D.nd.Om)) = (D.ntw.delta i).ker := by
      ext g
      cases b <;> simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, MonoidHom.mem_ker]
    rw [e]
    exact D.ntw.delta_open i
  have hχ : IsAlgPos (cf.delAt (D.ntw.l i)) 0 := delAt_alg cf _
  obtain ⟨r0, hr0, hL⟩ := hart.exists_isLAdicOf ρ.ι hχ
  have hc : Continuous (GlobalTheory.GalChar.inQ ρ.κ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i))) :=
    continuous_comp_of_isOpen_ker (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i))
      (Units.map (GlobalTheory.GalChar.toQ ρ.κ).toMonoidHom) hker
  have hz : ∀ v, ‖(((cf.delAt (D.ntw.l i)).val v : ℂˣ) : ℂ)‖ = 1 := fun v => cf.delAt_unitary _ _
  have heq : GlobalTheory.GalChar.inQ ρ.κ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)) = r0 := by
    refine GlobalTheory.GalChar.eq_of_frob hart hc hr0 ?_
    filter_upwards [GlobalTheory.GalChar.away_ae (E := D.host.E) (D.ntw.l i) (Fact.out : (D.ntw.l i).Prime).ne_zero,
      GlobalTheory.GalChar.unr_ae (cf.delAt (D.ntw.l i))] with v hv hu A hA σ hσ
    obtain ⟨x, hx, hd⟩ := hR i v hv hu A σ hA hσ
    have hx' : D.what₂.embLL (x : D.what₂.LL) = (((cf.delAt (D.ntw.l i)).val v : ℂˣ) : ℂ)⁻¹ := by
      rw [hx, Units.val_inv_eq_inv_val]
    apply Units.ext
    rw [hL.frob_unr hart (Or.inr rfl) hu hA hσ, GlobalTheory.GalChar.inQ_val]
    cases b
    · have hstar : (x : D.what₂.LL) = star ((x⁻¹ : D.LL0) : D.what₂.LL) := by
        apply D.what₂.embLL.injective
        rw [D.starLL_cx, IntermediateField.coe_inv, map_inv₀, hx', inv_inv, ← Complex.inv_eq_conj (hz v)]
      have h1 : ρ.ι (ρ.κ (D.ntw.emb0 i x)) = (((cf.delAt (D.ntw.l i)).val v : ℂˣ) : ℂ) := by
        rw [← D.ntw.restX_coefficientEmbedding_conj i x⁻¹ x hstar]
        have := ρ.read x⁻¹
        simp only [GlobalTheory.Triple.embSide, Bool.false_eq_true, if_false] at this
        rw [this]
        show D.what₂.embLL ((x⁻¹ : D.LL0) : D.what₂.LL) = _
        rw [IntermediateField.coe_inv, map_inv₀, hx', inv_inv]
      show GlobalTheory.GalChar.toQ ρ.κ (((D.ntw.delta i)⁻¹ σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) = _
      rw [MonoidHom.inv_apply, map_units_inv]
      congr 1
      show ρ.κ (algebraMap _ _ _) = _
      rw [hd, ← h1, ρ.ι.symm_apply_apply]
    · have h1 : ρ.ι (ρ.κ (D.ntw.emb0 i x)) = (((cf.delAt (D.ntw.l i)).val v : ℂˣ) : ℂ)⁻¹ := by
        have := ρ.read x
        simp only [GlobalTheory.Triple.embSide, if_true] at this
        rw [this]
        exact hx'
      show ρ.κ (algebraMap _ _ ((D.ntw.delta i σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)) = _
      rw [hd, ← map_inv₀, ← h1, ρ.ι.symm_apply_apply]
  refine ⟨ρ.κ, ρ.ι, fun x => ?_, hχ, ?_, ?_⟩
  · have := ρ.read x
    cases b <;> simpa [GlobalTheory.Triple.embSide] using this
  · exact continuous_comp_of_isOpen_ker (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)) Units.val hker
  · rw [heq]
    exact hL

end GlobalTheory.TwInputs.SetupPin

namespace GlobalTheory.TwInputs.SetupPin

end GlobalTheory.TwInputs.SetupPin
end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeriesTie.ComplexCh

variable {D : D7}

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

open GlobalTheory.SeriesTie.Complex (eGc levOf castG levOf_mem levOf_chi)

theorem exists_setup_ch (Rl : RealDat3 D A3 Ks) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (F3 : Face3 D A3) (hC : Rl.Char3 F3)
    (hW : GlobalTheory.Published.WeilRepresentationUnitaryPair)
    (hS0c : ∀ i, ∀ P ∈ D.ntw.S0 i, ∀ P', Formalism.BasicNotions.IsConjPl D.host P P' → P' ∈ D.ntw.S0 i)
    (hS02 : ∀ i, placesOver D.host.E 2 ⊆ ↑(D.ntw.S0 i))
    (hS0A : ∀ i P, P ∉ D.ntw.S0 i → FractionalIdeal.count D.host.E P D.host.AA = 0)
    (hδ : ∃ art : Ideles D.host.E →* Gab D.host.E D.nd.Om, IsGlobalArtin art ∧ ∀ i b,
      ∃ (κ : FractionRing (D.ntw.O0 i) →+* Qbar (D.ntw.l i)) (ι : Qbar (D.ntw.l i) ≃+* ℂ),
        (∀ x, ι (κ ((if b then D.ntw.emb0 i else D.ntw.emb0b i) x)) = embLL0 D x) ∧
        GlobalTheory.GalChar.IsGal art κ ι (Rl.C.delAt (D.ntw.l i)) (fun _ => 0) (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)))
    (hcard : ∀ i k, Cardinal.mk (FractionRing (D.ntw.Ok i k)) ≤ Cardinal.continuum)
    (hspl : (Ideal.primesOver (Ideal.span {(D.host.pde : ℤ)}) (𝓞 D.host.E)).ncard = Module.finrank ℚ D.host.E ∧
      (Ideal.primesOver (Ideal.span {(D.host.pde' : ℤ)}) (𝓞 D.host.E)).ncard = Module.finrank ℚ D.host.E)
    (hq : D.host.pde ≠ D.host.q ∧ D.host.pde' ≠ D.host.q)
    (ch : D.ntw.Tw → Set (PlE D.host)) (hch1 : ∀ i, IsChoice (D := D) (ch i))
    (hch2 : ∀ i, {P : Pl D.host.E | ∃ t, P ∈ Rl.Q t ∧ P ∈ D.ntw.pD i} ⊆ ch i) :
    ∃ ρ : Setup D.ntw, ρ.Good ∧ RealPin Rl cG ρ ∧ ρ.LevelOf D.nexp ∧ ρ.ch = ch ∧
      ∀ i, ρ.bad i = GlobalTheory.SeriesTie.normProd (D.ntw.S0 i) := by
  classical
  obtain ⟨art, hart, hδ⟩ := hδ
  choose κ ι hκι hG using hδ
  obtain ⟨κA, hκ1, hκ2, hκ3⟩ := GlobalTheory.CharTransport.exists_hom D
  let rc : Recip D D.nd.Om := ⟨κA, art⟩
  have hrc : rc.Good := ⟨hκ1, hκ2, hκ3, hart⟩
  obtain ⟨e, ek, he1, he2, he3⟩ := GlobalTheory.T.exists_ladicCoefficientField_embeddings_complex D D.nd D.ntw (fun i b => (ι i b).toRingHom.comp (κ i b)) hκι hcard
  choose F hF hFstd hFψ hFθ hFsT hFBS hFBT hFΛS hFΛT hFβS hFβT hFf hFlS hFlT using GlobalTheory.T.exists_good_frame_realisation D Γ Pl0 I0 T A3 Ks Rl F3 hC
  let f : ∀ i, Bool → (D.ntw.O0 i →+* ℂ) := fun i b =>
    ((e i b).comp (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)))).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i))
  have hfi : ∀ i b, Function.Injective (f i b) := fun i b =>
    ((e i b).injective.comp (IsFractionRing.injective (D.ntw.O i) (FractionRing (D.ntw.O i)))).comp (D.ntw.O_inj i)
  let de : D.ntw.Tw → Bool → Twist D Circle := fun i b =>
    twistOf rc (f i b) (ch i) (D.ntw.pD i) (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i))
  have hde : ∀ i b, (de i b).Good := fun i b => GlobalTheory.T.artin_twisting_character_delta_good D rc hrc i (ch i) (hch1 i) (f i b) (hfi i b) b
  have hpl : ∀ i b, PlacesOK Rl.Pg (de i b).Q := fun i _ =>
    GlobalTheory.T.typePlaces_twistPlaces_goodPosition D Γ Pl0 I0 T A3 Ks Rl A3.A.μ0 hC.lev hspl hq i (ch i) (hch1 i)
  have hB := fun i j b => GlobalTheory.T.liftBaseData_isGood_twist D Γ Pl0 I0 T A3 Ks Rl F3 hC j (F j) (hF j) (de i b) (hde i b) (hpl i b)
  choose w mu hwp hwm hBg using hB
  let P : D.ntw.Tw → ∀ j : Fin D.R.m, Bool → LevelP Rl.Pg (Wc D j).rank ℂ := fun i j b =>
    ⟨(levOf (eGc Rl cG j) D.nexp.U ((Units.map (e i b).toMonoidHom).comp (D.nexp.psiU i b))).1,
      (levOf (eGc Rl cG j) D.nexp.U ((Units.map (e i b).toMonoidHom).comp (D.nexp.psiU i b))).2⟩
  let B : D.ntw.Tw → ∀ j : Fin D.R.m, Bool → Base (Vc D j) (Wc D j) := fun i j b =>
    ⟨(hF j).rank_le, F j, ⟨Rl.Pg, P i j b, mu i j b⟩, de i b, w i j b, Rl.mu0 ((j : ℕ) + 1), Rl.eta⟩
  have hBG : ∀ i j b, (B i j b).Good := fun i j b => hBg i j b (P i j b)
  have hom : ∀ i j b (χ : (AE D)ˣ →* Circle), ∃ ω : PairRep (Vc D j) (Wc D j),
      ∀ t : Twist D Circle, t.Good → t.chi = χ → (B i j b).IsWeil χ ω := by
    intro i j b χ
    by_cases h : ∃ t : Twist D Circle, t.Good ∧ t.chi = χ
    · obtain ⟨t, ht, rfl⟩ := h
      obtain ⟨ω, hω⟩ := GlobalTheory.T.exists_weilRep_good_twist D _ _ (B i j b) hW (hBG i j b) (hFstd j) t ht
      exact ⟨ω, fun _ _ _ => hω⟩
    · exact ⟨1, fun t ht h' => absurd ⟨t, ht, h'⟩ h⟩
  choose om hom using hom
  have hcl : ∀ i j b (t : Twist D Circle), ∃ (m : ℕ) (h : Fin m → GA D (Vc D j)),
      IsClassSystem (Vc D j) ((B i j b).levJ t) h := fun i j b t =>
    exists_isClassSystem (B i j b) (hBG i j b).frame t
  choose m rep hrep using hcl
  let ρ : Setup D.ntw :=
    { rc := rc
      ch := ch
      bad := fun i => ∏ P ∈ D.ntw.S0 i, Ideal.absNorm P.asIdeal
      e := e
      ek := ek
      B := B
      om := om
      Cl := fun i j b t => Fin (m i j b t)
      rep := rep
      β := fun j P => DetBases.std _ _ _
      eG := fun _ j _ => eGc Rl cG j }
  refine ⟨ρ, ?_, ?_, ?_, rfl, fun _ => rfl⟩
  · exact
      { rc := hrc
        ch := hch1
        bad_ne := fun i => Finset.prod_ne_zero_iff.2 fun P _ h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
        goodSetup_bad_mem_badPlaces := fun i P hP => by
          obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun Q : Pl D.host.E => Ideal.absNorm Q.asIdeal) hP
          change ((∏ P ∈ D.ntw.S0 i, Ideal.absNorm P.asIdeal : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal
          rw [hc, Nat.cast_mul]
          exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)
        goodSetup_badPlaces_conj := hS0c
        goodSetup_placesOverTwo_subset := hS02
        goodSetup_count_eq_zero_off_badPlaces := hS0A
        e_LL0 := he1
        ek_e := fun i b k x => he2 i b k x
        base := hBG
        latS := fun _ j _ => hFlS j
        latT := fun _ j _ => hFlT j
        Pg := fun _ _ _ P hP => GlobalTheory.T.typePlaces_mem_placesOver_generators D Γ Pl0 I0 T A3 Ks Rl F3 hC P hP
        delta := fun _ _ _ => rfl
        weil := fun i j b t ht => hom i j b t.chi t ht rfl
        classes := fun i j b t _ _ => hrep i j b t }
  · exact
      { psi := fun _ j _ => hFψ j
        inf := fun _ j _ => hFθ j
        cartT := fun _ j _ => hFsT j
        onbS := fun _ j _ τ => hFBS j τ
        onbT := fun _ j _ => hFBT j
        latS := fun _ j _ => hFΛS j
        latT := fun _ j _ => hFΛT j
        frS := fun _ j _ => hFβS j
        frT := fun _ j _ => hFβT j
        vac := fun _ j _ => hFf j
        Pg := fun _ _ _ => rfl
        grp := fun _ j _ g P h h' a c => rfl
        mu0 := fun _ _ _ => rfl
        eta := fun _ _ _ => rfl
        delta := fun i j b => by
          exact GlobalTheory.T.twistingCharacter_ladicGaloisCharacter_eq_hecke D rc i (κ i b) (ι i b) (Rl.C.delAt (D.ntw.l i)) (D.ntw.delta i) b hrc (D.ntw.delta_open i) (hG i b)
            (f i b) (fun y hy => he3 i b y hy) (ch i) (D.ntw.pD i)
        deltaPl := fun i t P hP hPD => hch2 i ⟨t, hP, hPD⟩
        ap := fun i j b τ => hwp i j b τ
        am := fun i j b τ => hwm i j b τ }
  · exact
      { U_eq := fun i j b g => levOf_mem (eGc Rl cG j) D.nexp.U ((Units.map (e i b).toMonoidHom).comp (D.nexp.psiU i b)) g
        psiU_eq := fun i j b u hu => congrArg Units.val
          (levOf_chi (eGc Rl cG j) D.nexp.U ((Units.map (e i b).toMonoidHom).comp (D.nexp.psiU i b)) u hu) }

end GlobalTheory.SeriesTie.ComplexCh

end

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.TwInputs.SetupPinCh

end GlobalTheory.TwInputs.SetupPinCh

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MtLatFgOfReps
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeriesTie

theorem fg_of_eval {R G W I : Type} [CommRing R] [IsNoetherianRing R] [AddCommGroup W] [Module R W] [Finite I]
    (L : Submodule R (G → W)) (y : I → G) (C : I → Submodule R W) (hC : ∀ c, (C c).FG)
    (hmem : ∀ f ∈ L, ∀ c, f (y c) ∈ C c) (hinj : ∀ f ∈ L, (∀ c, f (y c) = 0) → f = 0) : L.FG := by
  haveI : ∀ c, IsNoetherian R (C c) := fun c => isNoetherian_of_fg_of_noetherian _ (hC c)
  let ev : L →ₗ[R] ∀ c, C c :=
    { toFun := fun f c => ⟨f.1 (y c), hmem f.1 f.2 c⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hev : Function.Injective ev := by
    refine (injective_iff_map_eq_zero ev).2 fun f hf => ?_
    exact Subtype.ext (hinj f.1 f.2 fun c => congrArg Subtype.val (congrFun hf c))
  haveI : IsNoetherian R L := isNoetherian_of_injective ev hev
  exact Module.Finite.iff_fg.1 inferInstance

section Eval

variable {D : D7} {S T : HSp D} {K : Type} [Field K] [NumberField K] {σ : K →+* ℂ}
  {emb : D.what₂.Tau → (D.host.E →+* K)} {O : Subring ℂ}

theorem eq_zero_of_reps (B : Base S T) (t : Twist D Circle) {I : Type} {y : I → Bridge.Gf S}
    (hy : Bridge.IsReps (Bridge.ratF S) (B.levJ t) y) {f : Bridge.Gf S → PolF D T.rank S.rank} (hf : f ∈ B.formsC t)
    (h0 : ∀ c, f (y c) = 0) : f = 0 := by
  have hlaw : B.HasLaw t f := ((B.mem_formsC).1 hf).2
  funext h
  obtain ⟨c, ⟨γ, k, e⟩, -⟩ := hy h
  have h1 := hlaw γ (y c) k
  rw [h0 c, map_zero, smul_zero, ← e] at h1
  exact h1

theorem mtLat_fg_of_reps [IsNoetherianRing O] (B : Base S T) (t : Twist D Circle) {I : Type} [Finite I] {y : I → Bridge.Gf S}
    (hy : Bridge.IsReps (Bridge.ratF S) (B.levJ t) y) (hfg : ∀ c, (B.coefLat σ emb O (y c)).FG) :
    (B.mtLat σ emb O t).FG :=
  fg_of_eval _ y (fun c => B.coefLat σ emb O (y c)) hfg (fun _ hf c => ((B.mem_mtLat σ emb O).1 hf).2 (y c))
    fun _ hf h0 => eq_zero_of_reps B t hy ((B.mem_mtLat σ emb O).1 hf).1 h0

end Eval

theorem latFG_of_good : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (ρ : Setup X), ρ.Good → ρ.LatFG := by
  intro D N X ρ hρ i j b k Q ψ hT
  obtain ⟨hg, ha, -⟩ := GlobalTheory.T.twistingCharacter_admissibleGaloisTwist_good D N X ρ hρ i j b k Q ψ hT
  have hc := hρ.classes i j b _ hg ha
  haveI : IsNoetherianRing (ρ.eOk i b k).range :=
    isNoetherianRing_of_surjective (X.Ok i k) _ (ρ.eOk i b k).rangeRestrict (ρ.eOk i b k).rangeRestrict_surjective
  have hB := hρ.base i j b
  refine mtLat_fg_of_reps _ _ hc.reps fun c => ?_
  refine (GlobalTheory.T.fockHarmonicLattice_fg_and_spans_value_space D _ _ _ _ _ _ _ _ _ hB.wt (fun τ => ?_) (hρ.isCoefRing_k i b k) ?_).1
  · have h1 := hB.sig τ
    have h2 := Formalism.BasicNotions.sig_sum _ hB.sigOK (tauE D τ)
    rw [← h1] at h2
    exact h2.le
  · classical
    have hfull : ∀ (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
        IsSelfDualC V Λ → Submodule.IsFullLattice D.host.E Λ := by
      intro V Λ hΛ
      haveI : Submodule.IsLattice D.host.E Λ := hΛ.1
      refine ⟨?_⟩
      obtain ⟨s, hs⟩ := hΛ.1.fg
      apply eq_top_iff.mpr
      intro y _
      let f : (Fin V.rank → D.host.E) → D.host.E := fun x =>
        ∑ i, ∑ j, star (x i) * V.gram i j * y j
      obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 D.host.E)) s f
      have ha0 : (algebraMap (𝓞 D.host.E) D.host.E a) ≠ 0 := by
        exact (FaithfulSMul.algebraMap_injective _ _).ne (mem_nonZeroDivisors_iff_ne_zero.mp a.2)
      let P : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := {
        carrier := {x | ∃ b : 𝓞 D.host.E, (b : D.host.E) = (algebraMap (𝓞 D.host.E) D.host.E a) * f x}
        zero_mem' := by refine ⟨0, ?_⟩; simp [f]
        add_mem' := by
          rintro x z ⟨b, hb⟩ ⟨c, hc⟩
          refine ⟨b + c, ?_⟩
          change (b : D.host.E) + c = _
          rw [hb, hc]
          simp [f, map_add, add_mul, Finset.sum_add_distrib, mul_add]
        smul_mem' := by
          rintro c x ⟨b, hb⟩
          refine ⟨RingOfIntegers.mapRingHom (starRingEnd D.host.E) c * b, ?_⟩
          simp only [map_mul, hb, f, Pi.smul_apply, Algebra.smul_def, map_mul, RingOfIntegers.mapRingHom_apply, star_mul]
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          change star (c : D.host.E) * _ = _
          ring }
      have hsP : (s : Set (Fin V.rank → D.host.E)) ⊆ P := by
        intro x hx
        obtain ⟨b, hb⟩ := ha x hx
        exact ⟨b, by simpa [Algebra.smul_def] using hb⟩
      have hy : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Λ := by
        apply (hΛ.2 _).2
        intro x hx
        have hxP : x ∈ P := (hs ▸ Submodule.span_le.mpr hsP) hx
        obtain ⟨b, hb⟩ := hxP
        refine ⟨b, ?_⟩
        rw [hb]
        dsimp only [f, Pi.smul_apply]
        simp only [smul_eq_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      have hy' : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) :=
        Submodule.subset_span hy
      have := (Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E))).smul_mem
        (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ hy' 
      change (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ •
        ((algebraMap (𝓞 D.host.E) D.host.E a) • y) ∈ _ at this
      rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ ha0, one_smul] at this
      exact this
    haveI : Submodule.IsFullLattice D.host.E (ρ.B i j b).F.ΛS := hfull _ _ hB.frame.sdS
    haveI : Submodule.IsFullLattice D.host.E
        ((ρ.B i j b).latAt (finPt (Vc D j) (ρ.rep i j b (ρ.tw i b k Q ψ) c))) :=
      Formalism.UG.P.csGlob_lattice (F := D.host.F) (ρ.B i j b).F.ΛS (Module.Finite.iff_fg.2 hB.frame.sdS.1.fg)
        (Submodule.IsFullLattice.span_eq_top (A := D.host.E) (M := (ρ.B i j b).F.ΛS)) _
    infer_instance

end GlobalTheory.SeriesTie

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTieWithSeries
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SeriesInstall

variable {D : D7} {ρ : Setup D.ntw}

abbrev RdV (D : D7) (ρ : Setup D.ntw) : Type :=
  ∀ i (j : Fin D.R.m) b k Q ψ, D.nexp.MtV i ((j : ℕ) + 1) b k Q ψ →ₛₗ[ρ.ek i b k]
    (Bridge.Gf (Vc D j) → PolF D (Wc D j).rank (Vc D j).rank)

def rdVLin (rdV : RdV D ρ) (i) (j : Fin D.R.m) (b k Q ψ) :
    D.nexp.MtV i ((j : ℕ) + 1) b k Q ψ →ₗ[D.ntw.Ok i k]
      Via (D.ntw.Ok i k) (ρ.ek i b k) (Bridge.Gf (Vc D j) → PolF D (Wc D j).rank (Vc D j).rank) where
  toFun f := rdV i j b k Q ψ f
  map_add' f g := map_add _ f g
  map_smul' c f := by
    rw [← algebraMap_smul (FractionRing (D.ntw.Ok i k)) c f, map_smulₛₗ]
    rfl


open Classical in
def latI (rdV : RdV D ρ) (i) : ∀ n b k Q ψ, Submodule (D.ntw.Ok i k) (D.nexp.MtV i n b k Q ψ)
  | 0, b, k, Q, ψ => D.nexp.MtLat i 0 b k Q ψ
  | n + 1, b, k, Q, ψ => if h : n < D.R.m ∧ TwOK i k Q ψ then
      (Via.lat (ρ.mt i ⟨n, h.1⟩ b k Q ψ)).comap (rdVLin rdV i ⟨n, h.1⟩ b k Q ψ) else D.nexp.MtLat i (n + 1) b k Q ψ

def Onto (ρ : Setup D.ntw) (rdV : RdV D ρ) : Prop :=
  ∀ i j b k Q ψ, TwOK i k Q ψ → Function.Injective (rdV i j b k Q ψ) ∧ (∀ F ∈ ρ.mt i j b k Q ψ, F ∈ Set.range (rdV i j b k Q ψ)) ∧
    Submodule.span (FractionRing (D.ntw.Ok i k)) {f | rdV i j b k Q ψ f ∈ ρ.mt i j b k Q ψ} = ⊤

theorem latI_eq (rdV : RdV D ρ) {i} (j : Fin D.R.m) {b k Q ψ} (h : TwOK i k Q ψ) :
    latI rdV i ((j : ℕ) + 1) b k Q ψ = (Via.lat (ρ.mt i j b k Q ψ)).comap (rdVLin rdV i j b k Q ψ) :=
  dif_pos ⟨j.2, h⟩

theorem mem_latI (rdV : RdV D ρ) {i} (j : Fin D.R.m) {b k Q ψ} (h : TwOK i k Q ψ) (f) :
    f ∈ latI rdV i ((j : ℕ) + 1) b k Q ψ ↔ rdV i j b k Q ψ f ∈ ρ.mt i j b k Q ψ := by
  rw [latI_eq rdV j h]; exact Iff.rfl

theorem latI_fg (rdV : RdV D ρ) (hV : Onto ρ rdV) (hL : ρ.LatFG) (i) :
    ∀ n b k Q ψ, (latI rdV i n b k Q ψ).FG
  | 0, b, k, Q, ψ => D.nexp.MtLat_fg i 0 b k Q ψ
  | n + 1, b, k, Q, ψ => by
    rw [latI]
    split_ifs with h
    · rcases hV i ⟨n, h.1⟩ b k Q ψ h.2 with ⟨hinj, hon, _⟩
      refine Submodule.fg_of_fg_map_injective (rdVLin rdV i ⟨n, h.1⟩ b k Q ψ) hinj ?_
      rw [Submodule.map_comap_eq_self (f := rdVLin rdV i ⟨n, h.1⟩ b k Q ψ) (q := Via.lat (ρ.mt i ⟨n, h.1⟩ b k Q ψ))
        fun x (hx : x ∈ Via.lat (ρ.mt i ⟨n, h.1⟩ b k Q ψ)) => by obtain ⟨y, hy⟩ := hon (Via.out _ _ x) hx; exact ⟨y, hy⟩]
      exact Via.lat_fg (hL i ⟨n, h.1⟩ b k Q ψ h.2)
    · exact D.nexp.MtLat_fg i (n + 1) b k Q ψ

theorem latI_span (rdV : RdV D ρ) (hV : Onto ρ rdV) (i) :
    ∀ n b k Q ψ, Submodule.span (FractionRing (D.ntw.Ok i k)) (latI rdV i n b k Q ψ : Set (D.nexp.MtV i n b k Q ψ)) = ⊤
  | 0, b, k, Q, ψ => D.nexp.MtLat_span i 0 b k Q ψ
  | n + 1, b, k, Q, ψ => by
    rw [latI]
    split_ifs with h
    · exact (hV i ⟨n, h.1⟩ b k Q ψ h.2).2.2
    · exact D.nexp.MtLat_span i (n + 1) b k Q ψ

variable (hρ : ρ.Good) (rd : Rds D.nexp ρ) (hF : ∀ i j b, Faithful (rd i j b))

include hF in
theorem exists_thPI (rdV : RdV D ρ) (i) (j : Fin D.R.m) (b k Q ψ) :
    ∃ φ : D.nexp.MtV i ((j : ℕ) + 1) b k Q ψ →ₗ[D.ntw.Ok i k] D.ntw.Ok i k ⊗[D.ntw.O i] D.nexp.Fm i ((j : ℕ) + 1) b,
      ∀ f, ρ.sum i j b k Q ψ (rdV i j b k Q ψ f) ∈ Set.range (rdK (rd i j b) hρ k) →
        rdK (rd i j b) hρ k (φ f) = ρ.sum i j b k Q ψ (rdV i j b k Q ψ f) :=
  exists_lift ((ρ.sum i j b k Q ψ).comp (rdV i j b k Q ψ)) (rdK (rd i j b) hρ k) ((hF i j b).injective_rdK hρ k)
    (divisible_baseChange D.nexp i _ b k)

def thPI (rdV : RdV D ρ) (i) : ∀ n b k Q ψ,
    D.nexp.MtV i n b k Q ψ →ₗ[D.ntw.Ok i k] D.ntw.Ok i k ⊗[D.ntw.O i] D.nexp.Fm i n b
  | 0, _, _, _, _ => 0
  | n + 1, b, k, Q, ψ => if h : n < D.R.m then (exists_thPI hρ rd hF rdV i ⟨n, h⟩ b k Q ψ).choose else 0

theorem exists_tie_withSeries : ∀ (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (rd : Rds D.nexp ρ), (∀ i j b, Faithful (rd i j b)) → ρ.LevelOf D.nexp → ρ.LatFG → ∀ rdV : ∀ i (j : Fin D.R.m) b k Q ψ, D.nexp.MtV i ((j : ℕ) + 1) b k Q ψ →ₛₗ[ρ.ek i b k] (Bridge.Gf (Vc D j) → PolF D (Wc D j).rank (Vc D j).rank), (∀ i j b k Q ψ, TwOK i k Q ψ → Function.Injective (rdV i j b k Q ψ) ∧ (∀ F ∈ ρ.mt i j b k Q ψ, F ∈ Set.range (rdV i j b k Q ψ)) ∧ Submodule.span (FractionRing (D.ntw.Ok i k)) {f | rdV i j b k Q ψ f ∈ ρ.mt i j b k Q ψ} = ⊤) → ∃ Dat th lev thPsi h1 thU thP MtLat h2 h3, (∀ i j, j ∉ Finset.Icc 1 D.R.m → ∀ b, IsEmpty (Dat i j b)) ∧ ∃ t : Comparison₂ hρ (Y := { D.nexp with Dat := Dat, th := th, lev := lev, thPsi := thPsi, thPsi_one := h1, thU := thU, thP := thP, MtLat := MtLat, MtLat_fg := h2, MtLat_span := h3 }) rd, ∀ i j b, (t i j b).rdV = rdV i j b := by
  intro D ρ hρ rd hF hU hL rdV hV
  refine ⟨Model.Dat rd, Model.th rd, Model.lev rd, Model.thPsi hρ rd, Model.thPsi_one hρ rd hF, Model.thU rd,
    thPI hρ rd hF rdV, latI rdV, latI_fg rdV hV hL, latI_span rdV hV, ?_, ?_⟩
  · intro i n hn b
    cases n with
    | zero => exact ⟨fun d => d.elim⟩
    | succ n =>
      refine ⟨fun d => hn (Finset.mem_Icc.2 ⟨Nat.succ_pos n, d.1⟩)⟩
  · refine ⟨fun i j b =>
      { supp := fun d => d.2.s
        cls := fun d => d.2.h
        coef := fun d => d.2.P
        rdV := rdV i j b
        U_eq := hU.U_eq i j b
        psiU_eq := hU.psiU_eq i j b
        dat := fun d => d.2.isDatum
        dat_onto := fun s h P h1 h2 => ⟨⟨j.2, s, h, P, h1, h2⟩, rfl, rfl, rfl⟩
        lev_iff := fun _ _ => Set.Finite.mem_toFinset _
        th_eq := fun d => d.2.rat.choose_spec
        thPsi_iff := fun _ _ _ _ _ _ => Iff.rfl
        thU_eq := fun Q M d hQ x hx => by
          have h : InRange D.ntw i Q ∧ ∀ a, ρ.xi i j b D.nexp Q M d.2.h d.2.P a ∈ Set.range (rd i j b) :=
            ⟨hQ, fun a => ⟨x a, hx a⟩⟩
          refine (dif_pos h).trans (congrArg (grpSum D.nexp (ρ.ch i) Q M) (funext fun a => (hF i j b).injective ?_))
          exact (h.2 a).choose_spec.trans (hx a).symm
        thU_off := fun _ _ _ h => dif_neg h
        rdV_inj := fun k Q ψ h => (hV i j b k Q ψ h).1
        mtLat_iff := fun k Q ψ h F => by
          refine ⟨fun hF' => ?_, fun ⟨f, hf, e'⟩ => ?_⟩
          · obtain ⟨f, rfl⟩ := (hV i j b k Q ψ h).2.1 F hF'
            exact ⟨f, (mem_latI rdV j h f).2 hF', rfl⟩
          · exact e' ▸ (mem_latI rdV j h f).1 hf
        thP_eq := fun k Q ψ _ f hf => by
          have e : thPI hρ rd hF rdV i ((j : ℕ) + 1) b k Q ψ = (exists_thPI hρ rd hF rdV i j b k Q ψ).choose := dif_pos j.2
          exact (congrArg (fun φ => rdK (rd i j b) hρ k (φ f)) e).trans
            ((exists_thPI hρ rd hF rdV i j b k Q ψ).choose_spec f hf) }, fun _ _ _ => rfl⟩

end GlobalTheory.SeriesInstall
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SecondStepHeckeOperatorsNormalisedSums
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SecondStepHeckeOperatorsNormalisedSums
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.HeightCounting.SerCopy

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem hkAd_step (R : RealDat3 D A3 Ks) (Sb : Finset (PlE D.host)) (i' i : Fin D.R.m) (h : i' = i) (k : ℕ) (P : PlE D.host)
    (f : Module.End D.what₂.LL (Fin (R.nW i') → D.what₂.LL))
    (hAd : ∀ α Rr, HkDat R Sb i' k P α Rr → ∀ x : Fin (R.nW i') → D.what₂.LL,
      (R.HW i' (sg0 D A3.A)).e ((R.FW i').j (sg0 D A3.A) (f x)) =
        hkNorm R i' k P • Mult.heckeOn (R.MW i' (sg0 D A3.A)) Rr ((R.HW i' (sg0 D A3.A)).e ((R.FW i').j (sg0 D A3.A) x)))
    (α : GA D (Wc D i)) (Rr : Finset (GA D (Wc D i))) (hd : HkDat R Sb i k P α Rr) (x : Fin (R.nW i') → D.what₂.LL) :
    (R.HW i (sg0 D A3.A)).e ((R.FW i).j (sg0 D A3.A) ((SideTies.fiOf R i' i h).e (f x))) =
      hkNorm R i k P • Mult.heckeOn (R.MW i (sg0 D A3.A)) Rr
        ((R.HW i (sg0 D A3.A)).e ((R.FW i).j (sg0 D A3.A) ((SideTies.fiOf R i' i h).e x))) := by
  subst h
  exact hAd α Rr hd x

variable {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw}

theorem heckeAt_of_scaledAt (YS : NX.NExpRealS Rl cG S) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)
    {ρ : Setup D.ntw} (hpin : RealPin Rl cG ρ) (hIs : Rl.toRealDat.toLevCh.Is A3.A.μ0)
    (hA : Rl.AllPlaces) (hρ : ρ.Good) {hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)}
    {u} (hδ : IsDeltaInv ρ u) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (ν : ℂ)
    (hs : NX.HeckeStabR S ((j : ℕ) + 1) (hL ((j : ℕ) + 1))) {k : ℕ} {P : PlE D.host} (hk : HkIdx i k P)
    (hr : ∀ (α : GA D (Wc D j)) (R : Finset (GA D (Wc D j))), IsHeckeAt (Wc D j) P k α →
      Bridge.IsDC (Formalism.IndefR.Lev.levG (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv)) α R → ∀ x : S.WL ((j : ℕ) + 1),
        (Rl.HW j (sg0 D A3.A)).e ((Rl.FW j).j (sg0 D A3.A) ((YS.fi j).e (hL ((j : ℕ) + 1) k P x))) =
          ((((Rl.C.mu0 j).val P : ℂˣ) : ℂ)⁻¹ ^ k * (((Nat.card (Formalism.L2.DIV.kP P) : ℕ) : ℂ) ^ (k * (D.R.nV / 2)))⁻¹) •
            Mult.heckeOn (Rl.MW j (sg0 D A3.A)) R ((Rl.HW j (sg0 D A3.A)).e ((Rl.FW j).j (sg0 D A3.A) ((YS.fi j).e x))))
    {f g : D.nexp.Fm i ((j : ℕ) + 1) b}
    (e1 : YS.eF i _ b (Nat.le_add_left _ _) j.2 g = (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (u i b P)) ^ k •
      NX.hkFR S i _ b (hL _) hs k P (YS.eF i _ b (Nat.le_add_left _ _) j.2 f)) :
    HeckeAt (realRd YS v₀ hρ i j b ν) k P f g := by
  rintro α R z ⟨hα, hR, hz⟩
  funext x
  rw [Setup.hecke_apply]
  have hδ' := hδ i j b k P hk α z hα hz
  obtain ⟨hk1, hkr, hsp, hP⟩ := hk
  have ho := GlobalTheory.ExportPin.Model.covered_of_allPlaces Rl hIs hA i P hP hsp
  have hR' : Bridge.IsDC (Formalism.IndefR.Lev.levG (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv)) α R :=
    GlobalTheory.PrincipalLevel.levK_eq_levG hpin i j b ▸ hR
  have hw : ∀ w, evW YS v₀ j (hL ((j : ℕ) + 1) k P w) =
      ((((Rl.C.mu0 j).val P : ℂˣ) : ℂ)⁻¹ ^ k * (((Nat.card (Formalism.L2.DIV.kP P) : ℕ) : ℂ) ^ (k * (D.R.nV / 2)))⁻¹) •
        fun x => ∑ γ ∈ R, evW YS v₀ j w (x * γ) := by
    intro w
    have := hr α R hα hR' w
    exact congrArg (fun T => T (v₀ j _)) this
  have hmu : (((ρ.B i j b).mu0 z : Circle) : ℂ) = (((Rl.C.mu0 j).val P : ℂˣ) : ℂ) ^ k := by
    rw [hpin.mu0 i j b]
    refine GlobalTheory.HeckeDetChar.chi_detAt (hIs.mu0 j) (Q := Rl.Pg) ?_ ?_ ?_ hα hz
    · have := (hρ.base i j b).unram
      rwa [hpin.Pg i j b, hpin.mu0 i j b] at this
    · obtain ⟨Q, h1, -, h3⟩ := (hρ.base i j b).places.split
      exact hpin.Pg i j b ▸ h3.mono h1
    · have hA' : Rl.Sb = Rl.Pg := hA
      rw [← hA']; exact ho
  have hrk : (Vc D j).rank = D.R.nV := D.sp.V_rank _ (Nat.le_add_left _ _) j.2
  change ν⁻¹ • evK YS v₀ hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2 g) x = _
  rw [e1]
  erw [evK_smul YS v₀ hρ i j b ((algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (u i b P)) ^ k)]
  erw [evK_hkFR YS v₀ hρ i j b (hL ((j : ℕ) + 1)) hs k P R _ hw]
  have he : ρ.e i b ((algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (u i b P)) ^ k) = ρ.eO i b (u i b P) ^ k := by
    rw [map_pow]; rfl
  have hm : (((ρ.B i j b).mu z : Circle) : ℂ) =
      (((ρ.B i j b).mu0 z : Circle) : ℂ) * (((ρ.B i j b).de.chi z : Circle) : ℂ) := by
    rw [Base.mu, MonoidHom.mul_apply, Circle.coe_mul]
  have hr1 : ∀ y, realRd YS v₀ hρ i j b ν f y =
      ν⁻¹ * evK YS v₀ hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2 f) y := fun _ => rfl
  have hq : normV P = Nat.card (Formalism.L2.DIV.kP P) := rfl
  simp only [hr1, Pi.smul_apply, smul_eq_mul, he, hδ', hm, hmu, hrk, hq]
  rw [← Finset.mul_sum]
  ring

theorem heckeRead_ysOf : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (kKs : Ks →+* ↥D.LL0) (hk : ∀ x : Ks, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap Ks D.what₂.LL x) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) hL eig θ (Bs : SideB D cf Rw low Pq (ratDatR R cG kKs hk) hL eig θ) (Sb : Finset (PlE D.host)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW j σ).Vec) (ρ : Setup D.ntw) (hρ : ρ.Good), RealPin R cG ρ → R.toRealDat.toLevCh.Is A3.A.μ0 → R.AllPlaces → GlobalTheory.HeightCounting.SerCopy.HkAd R Sb hL → (∀ i, Sb ⊆ D.ntw.S0 i) → ∀ i j b ν, HeckeRead (realRd (GlobalTheory.HeightCounting.SerCopy.ysOf Bs) v₀ hρ i j b ν) := by
  intro D Γ _ _ Pl0 I0 T A3 Ks _ _ _ R cG kKs hk cf Rw low Pq hL eig θ Bs Sb v₀ ρ hρ hpin hIs hA hAd hSb i j b ν
  refine heckeRead_iff.2 fun k P hk' f => ?_
  refine heckeAt_of_scaledAt (ysOf Bs) v₀ hpin hIs hA hρ (HeckePinRead.isDeltaInv_uD hρ hpin) i j b ν
    (Bs.hs _ (Nat.le_add_left _ _) j.2) hk' ?_ ?_
  · intro α Rr hα hR x
    obtain ⟨hk1, hkr, hsp, hP⟩ := hk'
    have hd : HkDat R Sb j k P α Rr :=
      { split := hsp
        offS := fun h => hP (hSb i h)
        odd := fun h2 => hP (hρ.goodSetup_placesOverTwo_subset i h2)
        le := hkr
        elt := hα
        reps := hR }
    exact hkAd_step R Sb _ j (idxOf_succ D j) k P (hL ((j : ℕ) + 1) k P)
      (fun α' Rr' hd' x' => hAd ((j : ℕ) + 1) k P α' Rr' (Nat.le_add_left _ _) j.2 hd' x') α Rr hd x
  · have hu : Bs.cHk i b P = HeckePinRead.uD D i b P := by
      rw [Bs.cHk_del i b P hk'.2.2.2 (HeckePinRead.frobU D P) (HeckePinRead.frobU_spec D P)]
      cases b <;> rfl
    rw [← hu]
    exact Bs.hkEq i _ b (Nat.le_add_left _ _) j.2 k P f hk'.2.2.2 hk'.2.2.1 hk'.2.1

end GlobalTheory.HeightCounting.SerCopy

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SecondStepHeckeOperatorsNormalisedSumsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.secondStep_heckeOperators_normalisedSums : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (kKs : Ks →+* ↥D.LL0) (hk : ∀ x : Ks, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap Ks D.what₂.LL x) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) hL eig θ (Bs : SideB D cf Rw low Pq (ratDatR R cG kKs hk) hL eig θ) (Sb : Finset (PlE D.host)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW j σ).Vec) (ρ : Setup D.ntw) (hρ : ρ.Good), RealPin R cG ρ → R.toRealDat.toLevCh.Is A3.A.μ0 → R.AllPlaces → GlobalTheory.HeightCounting.SerCopy.HkAd R Sb hL → (∀ i, Sb ⊆ D.ntw.S0 i) → ∀ i j b ν, HeckeRead (realRd (GlobalTheory.HeightCounting.SerCopy.ysOf Bs) v₀ hρ i j b ν) := by
  first | exact @GlobalTheory.HeightCounting.SerCopy.heckeRead_ysOf | exact GlobalTheory.HeightCounting.SerCopy.heckeRead_ysOf | (intros; apply GlobalTheory.HeightCounting.SerCopy.heckeRead_ysOf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteHomEqOfFramesKeepMatrices
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteHomEqOfFramesKeepMatrices
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.FrameFinPart

theorem finHom_eq_of_idFrame : ∀ (D : D7) (V : HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (P P' : principalLevelFrame.RowPsi V n), GlobalTheory.MtRead.IdFrame hF P → GlobalTheory.MtRead.IdFrame hF P' → ∀ g, (finHom V).rangeRestrict (P.ψ g) = (finHom V).rangeRestrict (P'.ψ g) := by
  intro D V n hF P P' hP hP' g
  obtain ⟨hn, h⟩ := hP
  obtain ⟨hn', h'⟩ := hP'
  apply Subtype.ext
  apply Units.ext
  ext a b
  change finMat D.sp.cm.sig V.gram (P.ψ g) a b = finMat D.sp.cm.sig V.gram (P'.ψ g) a b
  rw [h, h']

end GlobalTheory.FrameFinPart
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteHomEqOfFramesKeepMatricesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteHom_eq_of_frames_keep_matrices : ∀ (D : D7) (V : HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (P P' : principalLevelFrame.RowPsi V n), GlobalTheory.MtRead.IdFrame hF P → GlobalTheory.MtRead.IdFrame hF P' → ∀ g, (finHom V).rangeRestrict (P.ψ g) = (finHom V).rangeRestrict (P'.ψ g) := by
  first | exact @GlobalTheory.FrameFinPart.finHom_eq_of_idFrame | exact GlobalTheory.FrameFinPart.finHom_eq_of_idFrame | (intros; apply GlobalTheory.FrameFinPart.finHom_eq_of_idFrame <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNewThetaDataSeriesClassSumsLattices
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.HeightCounting.SerCopy

theorem ncard_eq_of_splits {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) (hd : ¬ (p : ℤ) ∣ discr E)
    (h : ∀ P : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ P.asIdeal → Ideal.absNorm P.asIdeal = p) :
    (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E := by
  refine GlobalTheory.ncard_primesOver_eq_finrank_of_absNorm_eq_of_not_mem_sq E p hp fun P hP hpP => ?_
  have := hP.isPrime
  refine ⟨h ⟨P, hP.isPrime, fun h0 => ?_⟩ hpP, GlobalTheory.Mem.RaySplit.not_mem_sq hp hpP
    ((GlobalTheory.Mem.RaySplit.not_dvd_discr_iff_ramificationIdx E hp).1 hd P hP.isPrime hpP)⟩
  rw [h0] at hpP
  exact hp.ne_zero (by simpa using hpP)

theorem exists_preTie : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (kKs : Ks →+* ↥D.LL0) (hk : ∀ x : Ks, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap Ks D.what₂.LL x) (Rw : RowSide D) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) hL eig θ (Bs : SideB D R.C Rw (lowAll D) Pq (ratDatR R cG kKs hk) hL eig θ) (Sb : Finset (PlE D.host)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW j σ).Vec) (hF : D.host.F = maximalRealSubfield D.host.E), GlobalTheory.Mem.R3.Pins R F cG → GlobalTheory.Mem.R3.Holds R F → (∀ j, FWT.IsChosenExtremalVector R.toRealDat j (sg0 D A3.A) (v₀ j _)) → (∀ j : Fin D.R.m, (R.FW j).IsKsForm) → GlobalTheory.HeightCounting.SerCopy.HkAd R Sb hL → (∀ i, Sb ⊆ D.ntw.S0 i) → TauTrue Bs.exp → CharSide D R.C → ValLL0 D R.C → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → (∀ v, NG.OverPl (Pq v) v) → IsChoice (D := D) (Set.range Pq) → (∀ t, ∀ P ∈ R.Q t, P ∈ Set.range Pq) → (∃ Z : GlobalTheory.LamTie.LamDat D, Z.Ok) → (∀ j, FWT.VStd D j) → Nonempty (GlobalTheory.HeightCounting.SerCopy.PreTie (GlobalTheory.HeightCounting.SerCopy.ysOf Bs) v₀ Bs.exp hF Pq) := by
  intro hA D Γ _ _ Pl0 I0 T A3 Ks _ _ _ R F cG kKs hk Rw Pq hL eig θ Bs Sb v₀ hF pins intersectionNumber_baseChange hv hK hH hSb hτ cs hV hsp hPq hch hQ
    ⟨Z, hZ⟩ hstd
  have hC : R.Char3 F := RealDat3.characterisation_of_weak pins.char intersectionNumber_baseChange.aux.ex
  obtain ⟨p1, -, d1, n1⟩ := hZ.places.splits D.host.pde (by simp)
  obtain ⟨p2, -, d2, n2⟩ := hZ.places.splits D.host.pde' (by simp)
  have hq : ∀ p : ℕ, ¬ (p : ℤ) ∣ discr D.host.E → p ≠ D.host.q := fun p h e =>
    h (Int.natCast_dvd.2 (e ▸ SetupPin.q_dvd_discr D))
  have h2 : 2 ∈ lowAll D := by simp [lowAll, lowPr]
  have hd : (discr D.host.E).natAbs.primeFactors ⊆ lowAll D := fun p hp =>
    Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_right _ hp)))
  have hc : (Ideal.absNorm D.host.ccK).primeFactors ⊆ lowAll D := fun p hp =>
    Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_left _ hp)))
  obtain ⟨ρ, hρ, hp, hlv, hρch, hbad⟩ := GlobalTheory.SeriesTie.ComplexCh.exists_setup_ch R cG F hC GlobalTheory.weilRepresentationUnitaryPair
    (SetupPin.goodSetup_badPlaces_conj _ Bs.tw) (SetupPin.goodSetup_placesOverTwo_subset _ Bs.tw h2) (SetupPin.goodSetup_count_eq_zero_off_badPlaces _ Bs.tw h2 hd hc)
    (SetupPin.exists_art_gal hA _ Bs.deltaRead) (SetupPin.mk_frac_Ok Bs.twF)
    ⟨ncard_eq_of_splits p1 d1 n1, ncard_eq_of_splits p2 d2 n2⟩ ⟨hq _ d1, hq _ d2⟩ (fun _ => Set.range Pq) (fun _ => hch)
    (fun i P ⟨t, h1, _⟩ => hQ t P h1)
  have hch' : ∀ i P, IsSplitPl D.host P → (P ∈ ρ.ch i ↔ P ∈ Set.range Pq) := fun i P _ => by rw [hρch]
  choose ν hν using fun i j b => exists_isScalar (ysOf Bs) v₀ hρ i j b
  have hFa : ∀ i j b, Faithful (realRd (ysOf Bs) v₀ hρ i j b (ν i j b)) := fun i j b =>
    GlobalTheory.SeriesTie.realRd_faithful D _ _ _ _ _ _ R cG _ (ysOf Bs) v₀ ρ hρ i j b _ (hν i j b).ne intersectionNumber_baseChange.prim.unif hC.models.HW
      (hv j) (hK (idxOf D ((j : ℕ) + 1)))
  choose PV₀ hPV₀ _ using fun j => GlobalTheory.MtRead.exists_idFrame D hF j (hstd j)
  obtain ⟨rdV, hon, hjoin⟩ := GlobalTheory.MtRead.exists_reading hA D R.C Rw (lowAll D) Pq _ hL eig θ Bs hτ cs hV hsp hPq Γ Pl0 I0 T A3 Ks R F
    cG hC.lev rfl pins.keep hF PV₀ hPV₀ ρ hρ hp hlv hch'
  obtain ⟨Dat, th, lev, thPsi, h1, thU, thP, MtLat, g2, g3, -, t, ht⟩ := GlobalTheory.SeriesInstall.exists_tie_withSeries D ρ hρ
    (fun i j b => realRd (ysOf Bs) v₀ hρ i j b (ν i j b)) hFa hlv (GlobalTheory.SeriesTie.latFG_of_good D _ _ ρ hρ) rdV hon
  refine ⟨{
    Dat := Dat, th := th, lev := lev, thPsi := thPsi, h1 := h1, thU := thU, thP := thP, MtLat := MtLat, h2 := g2, h3 := g3
    ρ := ρ, good := hρ, pin := hp, vec := hv, ν := ν, scalar := hν, tie := t
    hecke := fun i j b => (heckeRead_iff_tie.1 (GlobalTheory.T.secondStep_heckeOperators_normalisedSums D Γ Pl0 I0 T A3 Ks R cG kKs hk R.C Rw (lowAll D) Pq hL eig θ Bs Sb v₀
      ρ hρ hp hC.lev hC.allPl hH hSb i j b (ν i j b))).1
    bad := hbad, ch := hch'
    join := fun PV hPV i j b k Q ψ hAd hT => ?_ }⟩
  obtain ⟨ω, hω, he⟩ := hjoin i j b k Q ψ hAd hT
  refine ⟨ω, hω, fun f g => ?_⟩
  rw [← he f g, GlobalTheory.T.finiteHom_eq_of_frames_keep_matrices D _ _ hF (PV j) (PV₀ j) (hPV j) (hPV₀ j) g]
  exact congrFun (congrArg (fun r => r k Q ψ f) (ht i j b)) _

end GlobalTheory.HeightCounting.SerCopy
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNewThetaDataSeriesClassSumsLatticesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_newThetaData_series_classSums_lattices : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (kKs : Ks →+* ↥D.LL0) (hk : ∀ x : Ks, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap Ks D.what₂.LL x) (Rw : RowSide D) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) hL eig θ (Bs : SideB D R.C Rw (lowAll D) Pq (ratDatR R cG kKs hk) hL eig θ) (Sb : Finset (PlE D.host)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW j σ).Vec) (hF : D.host.F = maximalRealSubfield D.host.E), GlobalTheory.Mem.R3.Pins R F cG → GlobalTheory.Mem.R3.Holds R F → (∀ j, FWT.IsChosenExtremalVector R.toRealDat j (sg0 D A3.A) (v₀ j _)) → (∀ j : Fin D.R.m, (R.FW j).IsKsForm) → GlobalTheory.HeightCounting.SerCopy.HkAd R Sb hL → (∀ i, Sb ⊆ D.ntw.S0 i) → TauTrue Bs.exp → CharSide D R.C → ValLL0 D R.C → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → (∀ v, NG.OverPl (Pq v) v) → IsChoice (D := D) (Set.range Pq) → (∀ t, ∀ P ∈ R.Q t, P ∈ Set.range Pq) → (∃ Z : GlobalTheory.LamTie.LamDat D, Z.Ok) → (∀ j, FWT.VStd D j) → Nonempty (GlobalTheory.HeightCounting.SerCopy.PreTie (GlobalTheory.HeightCounting.SerCopy.ysOf Bs) v₀ Bs.exp hF Pq) := by
  first | exact @GlobalTheory.HeightCounting.SerCopy.exists_preTie | exact GlobalTheory.HeightCounting.SerCopy.exists_preTie | (intros; apply GlobalTheory.HeightCounting.SerCopy.exists_preTie <;> assumption)
end
