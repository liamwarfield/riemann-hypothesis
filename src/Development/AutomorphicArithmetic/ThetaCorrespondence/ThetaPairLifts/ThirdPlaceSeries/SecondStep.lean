module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGaloisRepFamilyBounded
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStepLevelConjBaseLatticeUnitary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingHomExtAdicCompletion
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HighestWeightDoubleDualCoefficientSpaceUnique
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeStableRationalLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TranslatedStdLatticeEqDecoratedLatticeReindexed
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTwistIndexOfCoefficientFieldPlace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorusCharacterRestrictionTraitSurjective
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlacesOverRealSubfieldSplit
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.EtaPiece

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevDatumForms
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevDatumForms
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.LevForms
theorem levDatum_forms_alt : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb)
    (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (S : RatDat D.ntw) (In : RatIn D S)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (b0 b1 : Big D)
    (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T),
    (∀ v, NG.OverPl (Pq v) v) →
    (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) →
    ∀ (wt : WtData D T), (∀ i j b, 1 ≤ j → j ≤ D.R.m → (wt.rhoW i j b).IsIrreducible ∧
      NX.IsAlgWeightF D.host.E D.R.nV (FractionRing (T.O i)) (wt.rhoW i j b)) →
    ∀ (hE : IsEmpty D.nd.Loc) (F : TwF T) (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
      (ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (T.Ok i k)ˣ), 1 ≤ j → j ≤ D.R.m →
      Formalism.MainNotions.NAdm.TWSet (T.ntw hE F (TwL.empty T)) i Q →
      (∀ P ∈ Q, P ∉ T.pD i ∧ ∀ k' : Fin 2, P ∉ placesOver D.host.E (D.host.g k')) →
      IsOpen (ψ.ker : Set (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om)) → AntiHom T.cc ψ → (∀ σ, ∃ N : ℕ, ψ σ ^ (T.l i ^ N) = 1) →
      (∀ P, P ∉ Q → ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P → ∀ σ ∈ Ine (F := D.host.E) A, ψ σ = 1) →
      ∃ L : LevT D T i k, LevLawsT D T Pq In.θ i j b k Q ψ L ∧
        FiniteDimensional (FractionRing (T.Ok i k))
          ↥(NX.TypeSpF D.host.E D.R.nV (FractionRing (T.Ok i k)) (rhoKT D T wt i j b k) L.J L.χ) := by
  intro hA D cf jE A S In Pq b0 b1 Sx T Sp hPq hsplit wt hwt hE F i j b k Q ψ hj1 hj2 hQ hQ2 hopen hanti hl hunr
  classical
  have hQs : ∀ P ∈ Q, IsSplitPl D.host P := fun P hP => (hQ P hP).1
  have hQl : ∀ P ∈ Q, P ∉ placesOver D.host.E (T.l i) := fun P hP => (hQ P hP).2
  have hDs : ∀ P ∈ T.pD i, IsSplitPl D.host P := by
    intro P hP
    have h := T.pD_eq i
    have hP' : P ∈ placesOver D.host.E (if T.l i = D.host.pde then D.host.pde' else D.host.pde) := by
      rw [← h]; exact hP
    split_ifs at hP' with hh
    · exact hsplit P (Or.inr hP')
    · exact hsplit P (Or.inl hP')
  obtain ⟨P₀, hP₀⟩ := GlobalTheory.T.auxiliaryPrimePlaces_nonempty D T i
  haveI : Nonempty (SplitPlace D.host.E) := ⟨(GlobalTheory.T.exists_splitPlace_of_isSplitPlace_cmField D P₀ (hDs P₀ hP₀)).choose⟩
  let sp : PlE D.host → SplitPlace D.host.E := fun P =>
    if h : IsSplitPl D.host P then (GlobalTheory.T.exists_splitPlace_of_isSplitPlace_cmField D P h).choose else Classical.arbitrary _
  have hsp : ∀ P, IsSplitPl D.host P → (sp P).w = P := fun P h => by
    simp only [sp, dif_pos h]; exact (GlobalTheory.T.exists_splitPlace_of_isSplitPlace_cmField D P h).choose_spec
  have hspw : ∀ P, (P ∈ qpOf D Pq Q ∨ P ∈ qpOf D Pq (T.pD i) ∨ ∃ kv, P = NX.pG D kv) → (sp P).w = P := by
    rintro P (h | h | ⟨kv, rfl⟩)
    · exact hsp P (hQs P (qpOf_sub D Pq Q h))
    · exact hsp P (hDs P (qpOf_sub D Pq _ h))
    · exact hsp _ (GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D kv.1 kv.2)
  obtain ⟨hv, hdisj1, hdisj2, hpG⟩ := GlobalTheory.T.split_places_avoid_auxiliary D T i Q Pq sp hPq hQs hQ2 hDs hspw
  let redG : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk),
      (sp (NX.pG D kv)).v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* ZMod (D.host.g kv.1) := fun kv =>
    (GlobalTheory.T.exists_residueHom_zmod_at_typePlace D kv (sp (NX.pG D kv)) (hspw _ (Or.inr (Or.inr ⟨kv, rfl⟩)))).some
  have hψt := fun P (hP : P ∈ qpOf D Pq Q) =>
    GlobalTheory.T.tameValues_galoisChar_form_residue_unit_character ψ P 1 (T.l i) hopen (by simpa [placesOver] using hQl P (qpOf_sub D Pq Q hP)) (fun A _ σ _ => hl σ)
  have hδt := fun P (hP : P ∈ qpOf D Pq (T.pD i)) =>
    GlobalTheory.T.tameValues_galoisChar_form_residue_unit_character (T.delta i) P (if b then 1 else -1) 15 (T.delta_open i) (GlobalTheory.T.fifteen_not_mem_and_delta_inertia_order_divides_fifteen_pow D T i P (qpOf_sub D Pq _ hP)).1
      (GlobalTheory.T.fifteen_not_mem_and_delta_inertia_order_divides_fifteen_pow D T i P (qpOf_sub D Pq _ hP)).2
  obtain ⟨J, χ, hJo, hhyp, hJm, hchi⟩ := GlobalTheory.T.exists_levelGroup_with_character_at_type_places D T In.θ i j b k Q ψ (qpOf D Pq Q) (qpOf D Pq (T.pD i)) sp redG
    hspw hv hdisj1 hdisj2 hpG (qpOf_sub D Pq Q) (qpOf_sub D Pq _) hψt hδt
  obtain ⟨hQc, hQn⟩ := GlobalTheory.T.chosenHalf_splitPlaces_meets_conjugatePair_once D Pq hPq Q hQs
  obtain ⟨hDc, hDn⟩ := GlobalTheory.T.chosenHalf_splitPlaces_meets_conjugatePair_once D Pq hPq (T.pD i) hDs
  refine ⟨⟨J, χ, qpOf D Pq Q, qpOf D Pq (T.pD i), sp, redG⟩,
    ⟨hJo, hhyp, rfl, rfl, qpOf_sub D Pq Q, hQc, hQn, qpOf_sub D Pq _, hDc, hDn, hspw, hJm, hchi⟩, ?_⟩
  exact typeSpF_finiteDimensional D.host.E D.R.nV _ (rhoKT D T wt i j b k) J χ hJo
end GlobalTheory.LevForms
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevDatumFormsStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.places_over_real_subfield_split_alt : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb)
    (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (S : RatDat D.ntw) (In : RatIn D S)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (b0 b1 : Big D)
    (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T),
    (∀ v, NG.OverPl (Pq v) v) →
    (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) →
    ∀ (wt : WtData D T), (∀ i j b, 1 ≤ j → j ≤ D.R.m → (wt.rhoW i j b).IsIrreducible ∧
      NX.IsAlgWeightF D.host.E D.R.nV (FractionRing (T.O i)) (wt.rhoW i j b)) →
    ∀ (hE : IsEmpty D.nd.Loc) (F : TwF T) (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
      (ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (T.Ok i k)ˣ), 1 ≤ j → j ≤ D.R.m →
      Formalism.MainNotions.NAdm.TWSet (T.ntw hE F (TwL.empty T)) i Q →
      (∀ P ∈ Q, P ∉ T.pD i ∧ ∀ k' : Fin 2, P ∉ placesOver D.host.E (D.host.g k')) →
      IsOpen (ψ.ker : Set (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om)) → AntiHom T.cc ψ → (∀ σ, ∃ N : ℕ, ψ σ ^ (T.l i ^ N) = 1) →
      (∀ P, P ∉ Q → ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P → ∀ σ ∈ Ine (F := D.host.E) A, ψ σ = 1) →
      ∃ L : LevT D T i k, LevLawsT D T Pq In.θ i j b k Q ψ L ∧
        FiniteDimensional (FractionRing (T.Ok i k))
          ↥(NX.TypeSpF D.host.E D.R.nV (FractionRing (T.Ok i k)) (rhoKT D T wt i j b k) L.J L.χ) := by
  first | exact @_root_.GlobalTheory.LevForms.levDatum_forms_alt | exact _root_.GlobalTheory.LevForms.levDatum_forms_alt | (intros; apply _root_.GlobalTheory.LevForms.levDatum_forms_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PickSpec
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PickSpec
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.HeightCounting.RowRhoInt
end GlobalTheory.HeightCounting.RowRhoInt
namespace GlobalTheory.HeightCounting.RowRhoInt
theorem twistEx_alt : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE),
    GalEx D → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (π : D.naut.CG D.R.r), D.naut.csd π → D.naut.ralg π →
      ∃ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.r) (Qbar l),
        IsRepOf D l ι (D.naut.tw π D.naut.etaTinv) ((1 - (D.R.nV : ℝ)) / 2) ρ := _root_.GlobalTheory.T.exists_galois_rep_of_cuspidal_alt
end GlobalTheory.HeightCounting.RowRhoInt
namespace GlobalTheory.HeightCounting.RowRhoInt
theorem core_data_of_point (hA : GlobalTheory.Published.GlobalArtinReciprocity) (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb)
    (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (hG : GalEx D) (hR : RowCusp D A.row) (hC : GlobalTheory.RowTie.ChebSplit D.nd)
    (l : ℕ) [Fact l.Prime] (j : ↥D.LL0 →+* PadicAlgCl l) (σ : D.what₂.FT)
    (hσ : ∃ k, 1 ≤ k ∧ k ≤ D.R.m ∧ D.what₂.isot k σ ≠ ⊥) (hg : D.nd.goodRow σ) :
    ∃ (L : Loc.FinExt l) (ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.r) (PadicAlgCl l)),
      Continuous (fun g => ((ρ g : GL (Fin D.R.r) (PadicAlgCl l)) : Matrix (Fin D.R.r) (Fin D.R.r) (PadicAlgCl l))) ∧
      (∀ g i k, ((ρ g : GL (Fin D.R.r) (PadicAlgCl l)) : Matrix (Fin D.R.r) (Fin D.R.r) (PadicAlgCl l)) i k ∈
        Formalism.L2.TwC.intOf l L.1) ∧
      ∀ π : D.naut.CG D.R.r, D.naut.csd π → D.naut.ralg π → (∀ w, IsSplitPl D.host w → D.naut.locG π w = A.row.locR σ w) →
        ∀ ι : Qbar l ≃+* ℂ, (∀ x, ι (j x) = embLL0 D x) →
          IsRepOf D l ι (D.naut.tw π D.naut.etaTinv) ((1 - (D.R.nV : ℝ)) / 2) ρ := by
  obtain ⟨k, hk1, hk2, hk⟩ := hσ
  obtain ⟨π₀, hc₀, hr₀, hl₀, hp₀⟩ := hR k hk1 hk2 σ hk hg
  obtain ⟨ι₀, hι₀⟩ := GlobalTheory.exists_padicAlgCl_ringEquiv_complex_comp_eq l ↥D.LL0 j (embLL0 D)
  have h0 : ∀ x, ι₀ (j x) = embLL0 D x := fun x => RingHom.congr_fun hι₀ x
  obtain ⟨ρG, hρG⟩ := _root_.GlobalTheory.HeightCounting.RowRhoInt.twistEx_alt hA D cf jE A hG l ι₀ π₀ hc₀ hr₀
  obtain ⟨L, P, hP⟩ := conjIntegral l (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om) D.R.r ρG hρG.1
  let ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.r) (PadicAlgCl l) := (MulAut.conj P⁻¹).toMonoidHom.comp ρG
  have hρ : ∀ g, ρ g = P⁻¹ * ρG g * P := fun g => by simp [ρ, MulAut.conj_apply]
  have hρ0 : IsRepOf D l ι₀ (D.naut.tw π₀ D.naut.etaTinv) ((1 - (D.R.nV : ℝ)) / 2) ρ :=
    isRepOf_conj D l ι₀ _ _ ρG ρ P hρ hρG
  refine ⟨L, ρ, hρ0.1, fun g i k => by rw [hρ]; exact hP g i k, fun π hc hr hl ι hι => ?_⟩
  have h1 := isRepOf_of_read D l ι₀ ι j h0 hι _ _ ρ hρ0 hp₀
  obtain ⟨ρ', hρ'⟩ := _root_.GlobalTheory.HeightCounting.RowRhoInt.twistEx_alt hA D cf jE A hG l ι π hc hr
  refine isRepOf_of_split D hC l ι _ _ _ ρ ρ' h1 hρ' (fun w hw => ?_)
  rw [D.naut.locG_tw, D.naut.locG_tw, hl₀ w hw, hl w hw]
end GlobalTheory.HeightCounting.RowRhoInt
namespace GlobalTheory.HeightCounting.RowRhoInt
section Pick
variable (hA : GlobalTheory.Published.GlobalArtinReciprocity) (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE)
  (hG : GalEx D) (hR : RowCusp D A.row) (hC : GlobalTheory.RowTie.ChebSplit D.nd)
open Classical in
def pickL_alt (l : ℕ) [Fact l.Prime] (j : ↥D.LL0 →+* PadicAlgCl l) (σ : D.what₂.FT) : Loc.FinExt l :=
  if h : GoodOcc D σ then (_root_.GlobalTheory.HeightCounting.RowRhoInt.core_data_of_point hA D cf jE A hG hR hC l j σ h.1 h.2).choose else ⟨⊥, inferInstance⟩
open Classical in
def padicRepresentationOfEmbedding (l : ℕ) [Fact l.Prime] (j : ↥D.LL0 →+* PadicAlgCl l) (σ : D.what₂.FT) :
    Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.r) (PadicAlgCl l) :=
  if h : GoodOcc D σ then (_root_.GlobalTheory.HeightCounting.RowRhoInt.core_data_of_point hA D cf jE A hG hR hC l j σ h.1 h.2).choose_spec.choose else 1
theorem pick_spec_alt (l : ℕ) [Fact l.Prime] (j : ↥D.LL0 →+* PadicAlgCl l) (σ : D.what₂.FT) (h : GoodOcc D σ) :
    Continuous (fun g => ((_root_.GlobalTheory.HeightCounting.RowRhoInt.padicRepresentationOfEmbedding hA D cf jE A hG hR hC l j σ g : GL (Fin D.R.r) (PadicAlgCl l)) :
      Matrix (Fin D.R.r) (Fin D.R.r) (PadicAlgCl l))) ∧
    (∀ g i k, ((_root_.GlobalTheory.HeightCounting.RowRhoInt.padicRepresentationOfEmbedding hA D cf jE A hG hR hC l j σ g : GL (Fin D.R.r) (PadicAlgCl l)) :
      Matrix (Fin D.R.r) (Fin D.R.r) (PadicAlgCl l)) i k ∈ Formalism.L2.TwC.intOf l (_root_.GlobalTheory.HeightCounting.RowRhoInt.pickL_alt hA D cf jE A hG hR hC l j σ).1) ∧
    ∀ π : D.naut.CG D.R.r, D.naut.csd π → D.naut.ralg π → (∀ w, IsSplitPl D.host w → D.naut.locG π w = A.row.locR σ w) →
      ∀ ι : Qbar l ≃+* ℂ, (∀ x, ι (j x) = embLL0 D x) →
        IsRepOf D l ι (D.naut.tw π D.naut.etaTinv) ((1 - (D.R.nV : ℝ)) / 2) (_root_.GlobalTheory.HeightCounting.RowRhoInt.padicRepresentationOfEmbedding hA D cf jE A hG hR hC l j σ) := by
  simp only [_root_.GlobalTheory.HeightCounting.RowRhoInt.pickL_alt, _root_.GlobalTheory.HeightCounting.RowRhoInt.padicRepresentationOfEmbedding, dif_pos h]
  exact (_root_.GlobalTheory.HeightCounting.RowRhoInt.core_data_of_point hA D cf jE A hG hR hC l j σ h.1 h.2).choose_spec.choose_spec
def bigOfStarStable (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) : Big D := fun l _ j =>
  ⟨⨆ σ : D.what₂.FT, ⨆ b : Bool, (_root_.GlobalTheory.HeightCounting.RowRhoInt.pickL_alt hA D cf jE A hG hR hC l (jSide D hstar l j b) σ).1, by
    haveI : ∀ σ b, FiniteDimensional ℚ_[l] ↥(_root_.GlobalTheory.HeightCounting.RowRhoInt.pickL_alt hA D cf jE A hG hR hC l (jSide D hstar l j b) σ).1 :=
      fun σ b => (_root_.GlobalTheory.HeightCounting.RowRhoInt.pickL_alt hA D cf jE A hG hR hC l (jSide D hstar l j b) σ).2
    haveI : ∀ σ : D.what₂.FT, FiniteDimensional ℚ_[l]
        ↥(⨆ b : Bool, (_root_.GlobalTheory.HeightCounting.RowRhoInt.pickL_alt hA D cf jE A hG hR hC l (jSide D hstar l j b) σ).1) :=
      fun σ => IntermediateField.finiteDimensional_iSup_of_finite
    exact IntermediateField.finiteDimensional_iSup_of_finite⟩
theorem pickL_jSide_le_cBig (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (l : ℕ) [Fact l.Prime]
    (j : ↥D.LL0 →+* PadicAlgCl l) (σ : D.what₂.FT) (b : Bool) :
    (_root_.GlobalTheory.HeightCounting.RowRhoInt.pickL_alt hA D cf jE A hG hR hC l (jSide D hstar l j b) σ).1 ≤ (_root_.GlobalTheory.HeightCounting.RowRhoInt.bigOfStarStable hA D cf jE A hG hR hC hstar l j).1 :=
  (le_iSup (fun b : Bool => (_root_.GlobalTheory.HeightCounting.RowRhoInt.pickL_alt hA D cf jE A hG hR hC l (jSide D hstar l j b) σ).1) b).trans
    (le_iSup (fun σ : D.what₂.FT => ⨆ b : Bool, (_root_.GlobalTheory.HeightCounting.RowRhoInt.pickL_alt hA D cf jE A hG hR hC l (jSide D hstar l j b) σ).1) σ)
end Pick
end GlobalTheory.HeightCounting.RowRhoInt
namespace GlobalTheory.HeightCounting.RowRhoInt
section HidaSetting
variable {D : D7} {cf : CharFrame D} {b0 b1 : Big D} {Sx : Finset (PlE D.host)} {T : TwR D.LL0 D.nd}
end HidaSetting
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem rho_rows_alt : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE),
    GalEx D → RowCusp D A.row → GlobalTheory.RowTie.ChebSplit D.nd → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) →
    ∃ c1 : Big D, ∀ (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T),
      (∀ (l : ℕ) [Fact l.Prime] j, (c1 l j).1 ≤ (b0 l j).1) →
      ∃ rho : RhoFam D T, (∀ i σ b, Continuous fun g =>
          ((rho i σ b g : GL (Fin D.R.r) (T.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (T.O0 i))) ∧
        ∀ i σ b, (∃ j, 1 ≤ j ∧ j ≤ D.R.m ∧ D.what₂.isot j σ ≠ ⊥) → D.nd.goodRow σ →
        ∀ π : D.naut.CG D.R.r, D.naut.csd π → D.naut.ralg π → (∀ w, IsSplitPl D.host w → D.naut.locG π w = A.row.locR σ w) →
        ∀ (φ : FractionRing (T.O0 i) →+* Qbar (T.l i)) (ι : Qbar (T.l i) ≃+* ℂ),
          (∀ z : ℤ_[T.l i], φ (algebraMap (T.O0 i) _ (algebraMap ℤ_[T.l i] (T.O0 i) z)) =
            algebraMap ℚ_[T.l i] (Qbar (T.l i)) (z : ℚ_[T.l i])) →
          (∀ x : ↥D.LL0, ι (φ ((if b then T.emb0 i else T.emb0b i) x)) = embLL0 D x) →
          IsRepOf D (T.l i) ι (D.naut.tw π D.naut.etaTinv) ((1 - (D.R.nV : ℝ)) / 2)
            (mapRep (φ.comp (algebraMap (T.O0 i) (FractionRing (T.O0 i)))) (rho i σ b)) := by
  intro hA D cf jE A hG hR hC hstar
  refine ⟨_root_.GlobalTheory.HeightCounting.RowRhoInt.bigOfStarStable hA D cf jE A hG hR hC hstar, fun b0 b1 Sx T Sp hc => ?_⟩
  classical
  have hmem : ∀ (i : T.Tw) (σ : D.what₂.FT) (b : Bool) (h : GoodOcc D σ) g k k',
      ((_root_.GlobalTheory.HeightCounting.RowRhoInt.padicRepresentationOfEmbedding hA D cf jE A hG hR hC (T.l i) (jSide D hstar (T.l i) (Sp.j0 i) b) σ g : GL (Fin D.R.r) (PadicAlgCl (T.l i))) :
        Matrix (Fin D.R.r) (Fin D.R.r) (PadicAlgCl (T.l i))) k k' ∈ Formalism.L2.TwC.intOf (T.l i) (Sp.K0 i).1 := by
    intro i σ b h g k k'
    exact intOf_mono (((_root_.GlobalTheory.HeightCounting.RowRhoInt.pickL_jSide_le_cBig hA D cf jE A hG hR hC hstar (T.l i) (Sp.j0 i) σ b).trans
      (hc (T.l i) (Sp.j0 i))).trans (Sp.ringSpec_baseExtension_lowerBound i))
      ((_root_.GlobalTheory.HeightCounting.RowRhoInt.pick_spec_alt hA D cf jE A hG hR hC (T.l i) _ σ h).2.1 g k k')
  let rho : RhoFam D T := fun i σ b =>
    if h : GoodOcc D σ then
      mapRep (Sp.eO0 i).symm.toRingHom (restrictRep (Formalism.L2.TwC.intOf (T.l i) (Sp.K0 i).1)
        (_root_.GlobalTheory.HeightCounting.RowRhoInt.padicRepresentationOfEmbedding hA D cf jE A hG hR hC (T.l i) (jSide D hstar (T.l i) (Sp.j0 i) b) σ) (hmem i σ b h))
    else 1
  have hemb : ∀ i, Topology.IsEmbedding (fun x : T.O0 i => kap Sp i (algebraMap (T.O0 i) (FractionRing (T.O0 i)) x)) :=
    fun i => (GlobalTheory.CoefEmbed.embedding_closed_integral (T.l i) (T.O0 i) (T.twistBaseCoefficientRing_isAdic i) (kap Sp i) (twistFractionFieldToPadicAlgebraicClosure_padicInt Sp i)).1
  have hks : ∀ i (y : Formalism.L2.TwC.intOf (T.l i) (Sp.K0 i).1),
      kap Sp i (algebraMap (T.O0 i) (FractionRing (T.O0 i)) ((Sp.eO0 i).symm y)) = (y : PadicAlgCl (T.l i)) := by
    intro i y; rw [kap_alg, RingEquiv.apply_symm_apply]
  refine ⟨rho, fun i σ b => ?_, fun i σ b hocc hgood π hc hr hloc φ ι hφ hι => ?_⟩
  · by_cases h : GoodOcc D σ
    · have e : rho i σ b = mapRep (Sp.eO0 i).symm.toRingHom (restrictRep (Formalism.L2.TwC.intOf (T.l i) (Sp.K0 i).1)
          (_root_.GlobalTheory.HeightCounting.RowRhoInt.padicRepresentationOfEmbedding hA D cf jE A hG hR hC (T.l i) (jSide D hstar (T.l i) (Sp.j0 i) b) σ) (hmem i σ b h)) := dif_pos h
      rw [e]
      refine continuous_pi fun k => continuous_pi fun k' => ?_
      refine (hemb i).continuous_iff.mpr ?_
      have hc0 := (_root_.GlobalTheory.HeightCounting.RowRhoInt.pick_spec_alt hA D cf jE A hG hR hC (T.l i) (jSide D hstar (T.l i) (Sp.j0 i) b) σ h).1.matrix_elem k k'
      refine hc0.congr fun g => ?_
      exact (hks i ⟨_, hmem i σ b h g k k'⟩).symm
    · have e : rho i σ b = 1 := dif_neg h
      rw [e]
      simp only [MonoidHom.one_apply, Units.val_one]
      exact continuous_const
  · have h : GoodOcc D σ := ⟨hocc, hgood⟩
    have e : rho i σ b = mapRep (Sp.eO0 i).symm.toRingHom (restrictRep (Formalism.L2.TwC.intOf (T.l i) (Sp.K0 i).1)
        (_root_.GlobalTheory.HeightCounting.RowRhoInt.padicRepresentationOfEmbedding hA D cf jE A hG hR hC (T.l i) (jSide D hstar (T.l i) (Sp.j0 i) b) σ) (hmem i σ b h)) := dif_pos h
    rw [e]
    have hstd : ∀ z : ℤ_[T.l i], algebraMap ℤ_[T.l i] (PadicAlgCl (T.l i)) z =
        algebraMap ℚ_[T.l i] (PadicAlgCl (T.l i)) (z : ℚ_[T.l i]) :=
      fun z => IsScalarTower.algebraMap_apply ℤ_[T.l i] ℚ_[T.l i] (PadicAlgCl (T.l i)) z
    haveI : FaithfulSMul ℤ_[T.l i] (T.O0 i) := by
      rw [faithfulSMul_iff_algebraMap_injective]
      intro z z' hzz
      have h3 := congrArg (fun y => kap Sp i (algebraMap (T.O0 i) (FractionRing (T.O0 i)) y)) hzz
      simp only [twistFractionFieldToPadicAlgebraicClosure_padicInt] at h3
      exact Subtype.ext ((algebraMap ℚ_[T.l i] (PadicAlgCl (T.l i))).injective h3)
    have h₀ : ((kap Sp i).comp (algebraMap (T.O0 i) (FractionRing (T.O0 i)))).comp (algebraMap ℤ_[T.l i] (T.O0 i)) =
        algebraMap ℤ_[T.l i] (PadicAlgCl (T.l i)) := RingHom.ext fun z => (twistFractionFieldToPadicAlgebraicClosure_padicInt Sp i z).trans (hstd z).symm
    have h₁ : (φ.comp (algebraMap (T.O0 i) (FractionRing (T.O0 i)))).comp (algebraMap ℤ_[T.l i] (T.O0 i)) =
        algebraMap ℤ_[T.l i] (PadicAlgCl (T.l i)) := RingHom.ext fun z => (hφ z).trans (hstd z).symm
    obtain ⟨τ, hτ⟩ := GlobalTheory.EmbConj.exists_algEquiv _ _ h₀ h₁
    have hφτ : ∀ q, φ q = τ (kap Sp i q) := by
      have : φ = (τ.toRingEquiv.toRingHom).comp (kap Sp i) :=
        IsLocalization.ringHom_ext (nonZeroDivisors (T.O0 i)) (RingHom.ext fun y => (hτ y).symm)
      intro q; rw [this]; rfl
    have hrep : mapRep (φ.comp (algebraMap (T.O0 i) (FractionRing (T.O0 i))))
        (mapRep (Sp.eO0 i).symm.toRingHom (restrictRep (Formalism.L2.TwC.intOf (T.l i) (Sp.K0 i).1)
          (_root_.GlobalTheory.HeightCounting.RowRhoInt.padicRepresentationOfEmbedding hA D cf jE A hG hR hC (T.l i) (jSide D hstar (T.l i) (Sp.j0 i) b) σ) (hmem i σ b h))) =
        mapRep τ.toRingEquiv.toRingHom (_root_.GlobalTheory.HeightCounting.RowRhoInt.padicRepresentationOfEmbedding hA D cf jE A hG hR hC (T.l i) (jSide D hstar (T.l i) (Sp.j0 i) b) σ) := by
      ext g k k'
      change φ (algebraMap (T.O0 i) (FractionRing (T.O0 i)) ((Sp.eO0 i).symm ⟨_, hmem i σ b h g k k'⟩)) = τ _
      rw [hφτ, hks]
    rw [hrep]
    apply isRepOf_map D (T.l i) ι _ _ _ τ
    refine (_root_.GlobalTheory.HeightCounting.RowRhoInt.pick_spec_alt hA D cf jE A hG hR hC (T.l i) (jSide D hstar (T.l i) (Sp.j0 i) b) σ h).2.2 π hc hr hloc _ (fun x => ?_)
    have hx := hι x
    cases b
    · have e1 : T.emb0b i x = T.emb0 i (starRestrictSubfield D hstar x) := T.restX_coefficientEmbedding_conj i x _ rfl
      simp only [Bool.false_eq_true, if_false] at hx
      rw [e1, hφτ, kap_emb0] at hx
      exact hx
    · simp only [if_true] at hx
      rw [hφτ, kap_emb0] at hx
      exact hx
end GlobalTheory.HeightCounting.RowRhoInt
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PickSpecStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galois_rep_family_bounded_alt : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE),
    GalEx D → RowCusp D A.row → GlobalTheory.RowTie.ChebSplit D.nd → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) →
    ∃ c1 : Big D, ∀ (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T),
      (∀ (l : ℕ) [Fact l.Prime] j, (c1 l j).1 ≤ (b0 l j).1) →
      ∃ rho : RhoFam D T, (∀ i σ b, Continuous fun g =>
          ((rho i σ b g : GL (Fin D.R.r) (T.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (T.O0 i))) ∧
        ∀ i σ b, (∃ j, 1 ≤ j ∧ j ≤ D.R.m ∧ D.what₂.isot j σ ≠ ⊥) → D.nd.goodRow σ →
        ∀ π : D.naut.CG D.R.r, D.naut.csd π → D.naut.ralg π → (∀ w, IsSplitPl D.host w → D.naut.locG π w = A.row.locR σ w) →
        ∀ (φ : FractionRing (T.O0 i) →+* Qbar (T.l i)) (ι : Qbar (T.l i) ≃+* ℂ),
          (∀ z : ℤ_[T.l i], φ (algebraMap (T.O0 i) _ (algebraMap ℤ_[T.l i] (T.O0 i) z)) =
            algebraMap ℚ_[T.l i] (Qbar (T.l i)) (z : ℚ_[T.l i])) →
          (∀ x : ↥D.LL0, ι (φ ((if b then T.emb0 i else T.emb0b i) x)) = embLL0 D x) →
          IsRepOf D (T.l i) ι (D.naut.tw π D.naut.etaTinv) ((1 - (D.R.nV : ℝ)) / 2)
            (mapRep (φ.comp (algebraMap (T.O0 i) (FractionRing (T.O0 i)))) (rho i σ b)) := by
  first | exact @_root_.GlobalTheory.HeightCounting.RowRhoInt.rho_rows_alt | exact _root_.GlobalTheory.HeightCounting.RowRhoInt.rho_rows_alt | (intros; apply _root_.GlobalTheory.HeightCounting.RowRhoInt.rho_rows_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WtWeights
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ShHalf
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ShHalf
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
namespace GlobalTheory.EtaTildeShift
theorem sh_half_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (t : D.what₂.Tau) (sh : ℂ),
    D.naut.infG D.naut.etaT (embT D t) = {sh} → ∃ z : ℤ, sh = (z : ℂ) + 1 / 2 := by
  intro D cf jE A t sh h
  have hE : (A.chr.e1 D.naut.etaT).1.HasInfQ (embPsi D.host) (fun _ => (1 / 2 : ℚ)) :=
    ⟨fun _ => 1, fun _ => by norm_num, by rw [A.chr.etaT]; exact cf.isEta.inf⟩
  have h2 := (A.chr.infG _ _ hE (D.eTau t)).1
  have h3 : D.naut.infG D.naut.etaT (embT D t) = {((1 / 2 : ℚ) : ℂ)} := h2
  rw [h3] at h
  have := (Multiset.singleton_inj.1 h).symm
  refine ⟨0, ?_⟩
  rw [this]; push_cast; ring
end GlobalTheory.EtaTildeShift
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ShHalfStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infG_eq_half_integer : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (t : D.what₂.Tau) (sh : ℂ),
    D.naut.infG D.naut.etaT (embT D t) = {sh} → ∃ z : ℤ, sh = (z : ℂ) + 1 / 2 := by
  first | exact @_root_.GlobalTheory.EtaTildeShift.sh_half_alt | exact _root_.GlobalTheory.EtaTildeShift.sh_half_alt | (intros; apply _root_.GlobalTheory.EtaTildeShift.sh_half_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WtWeights
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
namespace GlobalTheory.HeightCounting.FormsStep
attribute [local instance] algKkT
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem wt_weights_alt : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE),
    (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) →
    ∃ c2 : Big D, ∀ (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T),
      (∀ (l : ℕ) [Fact l.Prime] j, (c2 l j).1 ≤ (b0 l j).1) →
      ∃ wt : WtData D T, ∀ i j b (hj : 1 ≤ j) (hjm : j ≤ D.R.m),
        (wt.rhoW i j b).IsIrreducible ∧ NX.IsAlgWeightF D.host.E D.R.nV (FractionRing (T.O i)) (wt.rhoW i j b) ∧
        (∀ k, (rhoKT D T wt i j b k).IsIrreducible) ∧
        (∀ t, ∃ lam : Fin D.R.nV → ℤ, NX.HWAtF (NX.cE D) (wt.rhoW i j b).dual (kEmbT D T i b t) lam) ∧
        ∀ (t : D.what₂.Tau) (sh : ℂ) (lam : Fin D.R.nV → ℤ),
          D.naut.infG D.naut.etaT (embT D t) = {sh} → NX.HWAtF (NX.cE D) (wt.rhoW i j b).dual (kEmbT D T i b t) lam →
          NG.infOf lam = NG.paramV D.R (D.hc t) ⟨j - 1, by omega⟩ sh := by
  intro _ D cf jE A _ _
  refine ⟨fun l _ j => ⟨⊥, inferInstance⟩, fun b0 b1 Sx T Sp _ => ?_⟩
  have hlam : ∀ (j : Fin D.R.m) (t : D.what₂.Tau), ∃ lam : DomWeight D.R.nV, ∀ sh : ℂ,
      D.naut.infG D.naut.etaT (embT D t) = {sh} → NG.infOf lam.w = NG.paramV D.R (D.hc t) j sh := by
    intro j t
    by_cases h : ∃ sh, D.naut.infG D.naut.etaT (embT D t) = {sh}
    · obtain ⟨sh, hs⟩ := h
      obtain ⟨lam, hl⟩ := GlobalTheory.T.liftWeightParam_eq_infinitesimalCharacter_of_halfInt D.R (D.hc t) j sh (_root_.GlobalTheory.T.infG_eq_half_integer D cf jE A t sh hs)
      refine ⟨lam, fun sh' hs' => ?_⟩
      rw [hs, Multiset.singleton_inj] at hs'
      rw [← hs']
      exact hl
    · exact ⟨⟨fun _ => 0, antitone_const⟩, fun sh hs => absurd ⟨sh, hs⟩ h⟩
  choose lamF hlamF using hlam
  let lamD : ℕ → D.what₂.Tau → DomWeight D.R.nV := fun j t =>
    if h : 1 ≤ j ∧ j ≤ D.R.m then lamF ⟨j - 1, by omega⟩ t else ⟨fun _ => 0, antitone_const⟩
  have hc : NX.cE D = (IsCMField.complexConj D.host.E : D.host.E →+* D.host.E) :=
    RingHom.ext fun x => (Formalism.BasicNotions.Examples₂.star_eq_conj D.host x).symm
  refine ⟨{ Wt := fun i j _ => Module.Dual (FractionRing (T.O i)) (Formalism.L2.DIV.VV (FractionRing (T.O i)) (lamD j))
            fd := fun i j _ => GlobalTheory.AlgWtF.finDualVV (lamD j)
            rhoW := fun i j b => GlobalTheory.AlgWtF.wtRepF (kEmbT D T i b) (lamD j) }, fun i j b hj hjm => ?_⟩
  haveI := GlobalTheory.T.charZero_fractionRing_coefficientRing D T i
  have hE := GlobalTheory.T.cmTypeEmbeddingAtSide_distinct_nonconjugate D T i b
  have hl : lamD j = lamF ⟨j - 1, by omega⟩ := by
    simp only [lamD, dif_pos (And.intro hj hjm)]
  refine ⟨GlobalTheory.T.contragredient_isIrreducible_finiteDimensional _ _ _ _ (GlobalTheory.T.weightTensorRepOfEmbeddings_isIrreducible _ _ _ _ _ _ hE), GlobalTheory.T.isAlgWeightF_weightTensorDualRepOfEmbeddings _ _ _ _ _ _,
    fun k => @GlobalTheory.T.isIrreducible_baseChange_weightTensorDualRepOfEmbeddings _ _ _ _ _ _ _ _ _ _ _ _ hE (FractionRing (T.Ok i k)) _ (algKkT D T i k),
    fun t => ⟨_, hc ▸ GlobalTheory.T.weightTensorDualRep_dual_highestWeight_at_embedding _ _ _ _ _ _ hE t⟩, fun t sh lam hs hw => ?_⟩
  rw [hc] at hw
  have h1 := GlobalTheory.T.highestWeight_doubleDual_coefficientSpace_unique _ _ _ _ _ _ hE t lam hw
  rw [h1]
  show NG.infOf (lamD j t).w = _
  rw [hl]
  exact hlamF _ t sh hs
end GlobalTheory.HeightCounting.FormsStep
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WtWeightsStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weight_data_integral_alt : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE),
    (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) →
    ∃ c2 : Big D, ∀ (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T),
      (∀ (l : ℕ) [Fact l.Prime] j, (c2 l j).1 ≤ (b0 l j).1) →
      ∃ wt : WtData D T, ∀ i j b (hj : 1 ≤ j) (hjm : j ≤ D.R.m),
        (wt.rhoW i j b).IsIrreducible ∧ NX.IsAlgWeightF D.host.E D.R.nV (FractionRing (T.O i)) (wt.rhoW i j b) ∧
        (∀ k, (rhoKT D T wt i j b k).IsIrreducible) ∧
        (∀ t, ∃ lam : Fin D.R.nV → ℤ, NX.HWAtF (NX.cE D) (wt.rhoW i j b).dual (kEmbT D T i b t) lam) ∧
        ∀ (t : D.what₂.Tau) (sh : ℂ) (lam : Fin D.R.nV → ℤ),
          D.naut.infG D.naut.etaT (embT D t) = {sh} → NX.HWAtF (NX.cE D) (wt.rhoW i j b).dual (kEmbT D T i b t) lam →
          NG.infOf lam = NG.paramV D.R (D.hc t) ⟨j - 1, by omega⟩ sh := by
  first | exact @_root_.GlobalTheory.HeightCounting.FormsStep.wt_weights_alt | exact _root_.GlobalTheory.HeightCounting.FormsStep.wt_weights_alt | (intros; apply _root_.GlobalTheory.HeightCounting.FormsStep.wt_weights_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HkBCharpolySplits
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.V0TLeISupEigenspace
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.V0TLeISupEigenspace
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
namespace GlobalTheory.HeightCounting.FormsStep
theorem v0t_le_supr_eigenspace : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (S : RatDat D.ntw)
    (In : RatIn D S) (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T),
    In.Sb ⊆ Sx → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) →
    ∀ (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ) (P : PlE D.host), HkCond D T i j k P →
      V0T D T S In.rho In.chi In.θ i j b ≤
        ⨆ σ ∈ {σ : D.what₂.FT | D.what₂.isot j σ ≠ ⊥ ∧ D.nd.goodRow σ},
          Module.End.eigenspace (hkT D T S In i j b k P)
            (algebraMap (T.O i) (FractionRing (T.O i)) (cHkT D T i b P : T.O i) ^ k * readT D T i b (In.eig j σ k P)) := by
  intro D cf jE A S In b0 b1 Sx T Sp hSb _ i j b k P hk
  obtain ⟨hj1, hj2, hk1, hk2, hsp, hP0⟩ := hk
  have hPSb : P ∉ In.Sb := by
    intro h
    apply hP0
    have h1 : P ∈ (T.S0 i : Set (PlE D.host)) := by
      rw [Sp.ringSpec_excludedPlaces_eq i]
      exact Or.inr (hSb h)
    exact h1
  have hZ := GlobalTheory.T.heckeIdempotentProjector_vanishing_baseChange_twistSide D T S In i j b k P hj1 hj2 (GlobalTheory.T.heckePoly_mul_centralIdempotent_mul_genericProjector D S In j k P hj1 hj2 hk1 hk2 hsp hPSb)
  have hker : V0T D T S In.rho In.chi In.θ i j b ≤ LinearMap.ker (phiKop D T S In i j b k P) := by
    rintro x ⟨y, hy, rfl⟩
    rw [LinearMap.mem_ker]
    have := LinearMap.congr_fun hZ y
    rw [Module.End.mul_apply, Module.End.mul_apply, GlobalTheory.T.genericCharacterProjectorOnTwistForms_fix D T S In i j b y hy] at this
    exact this
  refine hker.trans ?_
  classical
  have hinj : Function.Injective (readT D T i b) := (readT D T i b).injective
  have hpol : (evPol D S In j k P).map (readT D T i b) =
      ∏ r ∈ (evRoots D S In j k P).image (readT D T i b), (X - C r) := by
    rw [evPol, Polynomial.map_prod, Finset.prod_image (fun x _ y _ h => hinj h)]
    simp
  rw [phiKop, hpol, GlobalTheory.JointDiag.ker_prod]
  refine iSup₂_le fun r hr => ?_
  obtain ⟨r0, hr0, rfl⟩ := Finset.mem_image.mp hr
  obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hr0
  have hσ' : σ ∈ {σ : D.what₂.FT | D.what₂.isot j σ ≠ ⊥ ∧ D.nd.goodRow σ} := (Finset.mem_filter.mp hσ).2
  refine le_trans ?_ (le_iSup₂_of_le σ hσ' le_rfl)
  intro x hx
  rw [Module.End.mem_eigenspace_iff] at hx ⊢
  rw [hkT_eq, LinearMap.smul_apply, hx, smul_smul]
end GlobalTheory.HeightCounting.FormsStep
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.V0TLeISupEigenspaceStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixed_space_le_iSup_eigenspace_of_goodness : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (S : RatDat D.ntw)
    (In : RatIn D S) (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T),
    In.Sb ⊆ Sx → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) →
    ∀ (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ) (P : PlE D.host), HkCond D T i j k P →
      V0T D T S In.rho In.chi In.θ i j b ≤
        ⨆ σ ∈ {σ : D.what₂.FT | D.what₂.isot j σ ≠ ⊥ ∧ D.nd.goodRow σ},
          Module.End.eigenspace (hkT D T S In i j b k P)
            (algebraMap (T.O i) (FractionRing (T.O i)) (cHkT D T i b P : T.O i) ^ k * readT D T i b (In.eig j σ k P)) := by
  first | exact @_root_.GlobalTheory.HeightCounting.FormsStep.v0t_le_supr_eigenspace | exact _root_.GlobalTheory.HeightCounting.FormsStep.v0t_le_supr_eigenspace | (intros; apply _root_.GlobalTheory.HeightCounting.FormsStep.v0t_le_supr_eigenspace <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HkBCharpolySplits
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX
  GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
namespace GlobalTheory.HeightCounting.FormsStep
end GlobalTheory.HeightCounting.FormsStep
namespace GlobalTheory.HeightCounting.FormsStep
theorem hkB_charpoly_splits_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (S : RatDat D.ntw)
    (In : RatIn D S) (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T),
    In.Sb ⊆ Sx → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) →
    ∀ (hst : HkStab D T S In) (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ) (P : PlE D.host)
      [hfr : Module.Free (T.O i) ↥(BI D T S In i j b)] [hfi : Module.Finite (T.O i) ↥(BI D T S In i j b)], P ∉ T.S0 i →
      ∃ s : Multiset (FractionRing (T.O i)),
        (LinearMap.charpoly (hkB D T S In hst i j b k P)).map
          (algebraMap (T.O i) (FractionRing (T.O i))) = (s.map fun a => X - C a).prod := by
  classical
  intro D cf jE A S In b0 b1 Sx T Sp hSb hstar hst i j b k P hfr hfi hP
  by_cases hc : HkCond D T i j k P
  · have hB : ∀ x ∈ BI D T S In i j b, x ∈ V0T D T S In.rho In.chi In.θ i j b := fun x hx => hx.2
    have hL1 := _root_.GlobalTheory.T.fixed_space_le_iSup_eigenspace_of_goodness D cf jE A S In b0 b1 Sx T Sp hSb hstar i j b k P hc
    let ev : D.what₂.FT → FractionRing (T.O i) := fun σ =>
      algebraMap (T.O i) (FractionRing (T.O i)) (cHkT D T i b P : T.O i) ^ k * readT D T i b (In.eig j σ k P)
    let sG : Finset D.what₂.FT := Finset.univ.filter fun σ : D.what₂.FT => D.what₂.isot j σ ≠ ⊥ ∧ D.nd.goodRow σ
    have hle : (⨆ σ ∈ {σ : D.what₂.FT | D.what₂.isot j σ ≠ ⊥ ∧ D.nd.goodRow σ},
        Module.End.eigenspace (hkT D T S In i j b k P) (ev σ)) ≤
        ⨆ r ∈ sG.image ev, Module.End.eigenspace (hkT D T S In i j b k P) r :=
      iSup₂_le fun σ hσ => le_iSup₂_of_le (ev σ) (Finset.mem_image_of_mem ev (by simpa [sG] using hσ)) le_rfl
    obtain ⟨m, hm⟩ := charpoly_restrict_map_eq_prod (BI D T S In i j b) (hkT D T S In i j b k P)
      (fun x hx => hst i j b k P hc x hx) (sG.image ev) (fun x hx => hle (hL1 (hB x hx)))
    refine ⟨m, ?_⟩
    have he : hkB D T S In hst i j b k P = ((hkT D T S In i j b k P).restrictScalars (T.O i)).restrict
        (fun x hx => hst i j b k P hc x hx) := by
      unfold hkB
      rw [dite_eq_left hc]
    rw [he]
    exact hm
  · have he : hkB D T S In hst i j b k P = 1 := by
      unfold hkB
      rw [dite_eq_right hc]
    refine ⟨Multiset.replicate (Module.finrank (T.O i) ↥(BI D T S In i j b)) 1, ?_⟩
    rw [he, LinearMap.charpoly_one, Multiset.map_replicate, Multiset.prod_replicate, Polynomial.map_pow,
      Polynomial.map_sub, Polynomial.map_X, Polynomial.map_one, map_one]
end GlobalTheory.HeightCounting.FormsStep
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HkBCharpolySplitsStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_basis_free_module_place_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (S : RatDat D.ntw)
    (In : RatIn D S) (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T),
    In.Sb ⊆ Sx → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) →
    ∀ (hst : HkStab D T S In) (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ) (P : PlE D.host)
      [hfr : Module.Free (T.O i) ↥(BI D T S In i j b)] [hfi : Module.Finite (T.O i) ↥(BI D T S In i j b)], P ∉ T.S0 i →
      ∃ s : Multiset (FractionRing (T.O i)),
        (LinearMap.charpoly (hkB D T S In hst i j b k P)).map
          (algebraMap (T.O i) (FractionRing (T.O i))) = (s.map fun a => X - C a).prod := by
  first | exact @_root_.GlobalTheory.HeightCounting.FormsStep.hkB_charpoly_splits_alt | exact _root_.GlobalTheory.HeightCounting.FormsStep.hkB_charpoly_splits_alt | (intros; apply _root_.GlobalTheory.HeightCounting.FormsStep.hkB_charpoly_splits_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HkStabAll
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HkStabAll
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.HeightCounting.HeckeLat
end GlobalTheory.HeightCounting.HeckeLat
open GlobalTheory.HeightCounting.HeckeLat in
theorem GlobalTheory.HeightCounting.FormsStep.hkStab_of_ringSpec_of_subset : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (S : RatDat D.ntw)
    (In : RatIn D S) (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T),
    In.Sb ⊆ Sx → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → HkStab D T S In := by
  intro D cf jE A S In b0 b1 Sx T Sp hSb _ i j b k P ⟨h1, h2, hk1, hk2, hsp, hP⟩ x hx
  obtain ⟨Φ, hc, hf, hw, hint, W0, hW0, hW0c, hrel⟩ := descend_integral D T S In i j b h1 h2
  have ha := descend_actL D T S In i j b h1 h2 Φ hc hf
  have he := descend_eSum D T S In i j b Φ hc ha
  have hPb : P ∉ In.Sb := fun h => hP (by
    rw [← Finset.mem_coe, Sp.ringSpec_excludedPlaces_eq i]
    exact Or.inr (Finset.mem_coe.mpr (hSb h)))
  have hMW : ∀ y ∈ (S.A j).MK, y ∈ WKr D S j := fun y hy => by
    rw [WKr_of D S h1 h2]; exact hy.1
  have hML : ∀ y ∈ Submodule.span (𝓞 D.what₂.LL) ((S.A j).MK : Set (S.WL j)), Φ y ∈ BsupT D T S i j b := by
    have key : ∀ y ∈ Submodule.span (𝓞 D.what₂.LL) ((S.A j).MK : Set (S.WL j)), ∀ a : 𝓞 D.what₂.LL,
        Φ (a • y) ∈ BsupT D T S i j b := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        intro a
        obtain ⟨o, ho⟩ := hint a ⟨y, hMW y hy⟩
        rw [← algebraMap_smul D.what₂.LL a y]
        refine ho ▸ Submodule.smul_mem _ o ?_
        exact Submodule.subset_span ⟨⟨y, hMW y hy⟩, hy, hw _⟩
      | zero => intro a; rw [smul_zero, map_zero]; exact zero_mem _
      | add y z _ _ hy hz => intro a; rw [smul_add, map_add (f := _)]; exact add_mem (hy a) (hz a)
      | smul a' y _ hy => intro a; rw [smul_smul]; exact hy _
    intro y hy
    simpa using key y hy 1
  have hhr : ∀ w : ↥(WKr D S j), (hLr D S In j k P w : S.WL j) = In.hL j k P w := by
    intro w
    unfold hLr
    rw [dite_eq_left ⟨h1, h2⟩]
    rfl
  have hkΦ : ∀ y, hkT D T S In i j b k P (Φ y) = ((cHkT D T i b P : T.O i) ^ k) • Φ (In.hL j k P y) := by
    intro y
    rw [← algebraMap_smul (FractionRing (T.O i)), map_pow, hf _ _ hhr]
    rfl
  obtain ⟨n, hn⟩ := In.hL_int j k P h1 h2 hsp hPb hk2
  obtain ⟨u, hu⟩ := (normV_isUnit D T i P hP).pow n
  have hstep : ∀ y ∈ Submodule.span (𝓞 D.what₂.LL) ((S.A j).MK : Set (S.WL j)), y ∈ goodL D S In.θ j →
      hkT D T S In i j b k P (Φ y) ∈ BI D T S In i j b := by
    intro y hy hg
    rw [hkΦ]
    refine Submodule.smul_mem _ _ ⟨?_, ?_⟩
    · have h3 := hML _ (hn y hy hg)
      rw [map_nsmul, ← Nat.cast_smul_eq_nsmul (T.O i), Nat.cast_pow, ← hu] at h3
      have h4 := Submodule.smul_mem _ (↑u⁻¹ : T.O i) h3
      rwa [smul_smul, Units.inv_mul, one_smul] at h4
    · exact descend_mem_V0T D T S In i j b Φ hc ha he _ (hL_goodL D S In j k P h1 h2 ⟨hk1, hk2, hsp, hPb⟩ y hg)
  have hET : ∀ a y, Φ (eqL D S In.θ j a y) = eqT D T S In i j b a (Φ y) := by
    intro a y
    cases a with
    | none => simp only [eqL, eqT, LinearMap.sub_apply, Module.End.one_apply, map_sub, he]
    | some u =>
      simp only [eqL, eqT, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, ha, hc,
        LinearEquiv.coe_coe]
  have hx0 : ∀ a, eqT D T S In i j b a x = 0 := by
    intro a
    have h3 := goodTwistSideForms_le_span_goodLiftForms D S In T i j b h1 h2 (eIdem_all D) Φ hc ha he hw hx.2
    refine (Submodule.span_le (p := LinearMap.ker (eqT D T S In i j b a))).mpr ?_ h3
    rintro _ ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, ← hET, (mem_goodL_iff D S In.θ j y).mp hy a, map_zero]
  obtain ⟨m, o, g, rfl⟩ := Submodule.mem_span_set'.mp hx.1
  choose w hwM hwg using fun t => (g t).2
  have hg : ∀ t, (g t : FmT D T S i j b) = Φ (w t) := fun t => (hwg t).trans (hw _).symm
  simp only [hg] at hx0 ⊢
  haveI : Fintype ↥(Formalism.IndefR.NX.U D.nd) := Fintype.ofFinite _
  have hsol := hrel (fun t a => eqL D S In.θ j a (w t)) (fun t a => eqL_rational D S In j h1 h2 W0 hW0 hW0c a (w t)) o (by
    intro a
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hx0 a, map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [hET, LinearMap.map_smul_of_tower])
  clear hx0 hx
  induction hsol using Submodule.span_induction with
  | mem o ho =>
    obtain ⟨c, hc0, hco⟩ := ho
    have h3 : ∑ t, o t • Φ (w t) = Φ (∑ t, ((c t : ↥D.LL0) : D.what₂.LL) • (w t : S.WL j)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [hc, ← hco, algebraMap_smul]
    rw [h3]
    refine hstep _ (Submodule.sum_mem _ fun t _ => ?_) ((mem_goodL_iff D S In.θ j _).mpr fun a => ?_)
    · let a : 𝓞 D.what₂.LL := ⟨((c t : ↥D.LL0) : D.what₂.LL),
        (RingOfIntegers.isIntegral_coe (c t)).map (algebraMap ↥D.LL0 D.what₂.LL).toIntAlgHom⟩
      have h4 := Submodule.smul_mem _ a (Submodule.subset_span (R := 𝓞 D.what₂.LL) (s := ((S.A j).MK : Set (S.WL j))) (hwM t))
      rwa [← algebraMap_smul D.what₂.LL a] at h4
    · set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simpa only [map_smul] using hc0 a
  | zero => simp
  | add o o' _ _ ho ho' =>
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, map_add (f := _)]
    exact add_mem ho ho'
  | smul r o _ ho =>
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, LinearMap.map_smul_of_tower]
    exact Submodule.smul_mem _ _ ho
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HkStabAllStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hkStab_of_subset_of_star_closed : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (S : RatDat D.ntw)
    (In : RatIn D S) (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T),
    In.Sb ⊆ Sx → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → HkStab D T S In := by
  first | exact @_root_.GlobalTheory.HeightCounting.FormsStep.hkStab_of_ringSpec_of_subset | exact _root_.GlobalTheory.HeightCounting.FormsStep.hkStab_of_ringSpec_of_subset | (intros; apply _root_.GlobalTheory.HeightCounting.FormsStep.hkStab_of_ringSpec_of_subset <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SecondStep
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
namespace GlobalTheory.HeightCounting.FormsStep
attribute [local instance] algKkT
set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem second_step_alt : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (S : RatDat D.ntw) (In : RatIn D S) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (M : MtFam D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E) (Q : D.what₂.places.Pl → Finset (PlE D.host)), MtInput D M tup Q → (∀ v, NG.OverPl (Pq v) v) → GalEx D → RowCusp D A.row → GlobalTheory.RowTie.ChebSplit D.nd → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → ∃ c0 : Big D, ∀ (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T), (∀ (l : ℕ) [Fact l.Prime] j, (c0 l j).1 ≤ (b0 l j).1) → In.Sb ⊆ Sx → (∀ P P', P ∈ Sx → IsConjPl D.host P P' → P' ∈ Sx) → (∀ p ∈ low, placesOver D.host.E p ⊆ ↑Sx) → ∃ (F : TwF T) (ex : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw A.bare F (TwL.empty T))) (h0 : _), (∀ i j b, (ex.Bsup i j b).FG ∧ Submodule.span (FractionRing ((T.ntw A.bare F (TwL.empty T)).O i)) (ex.Bsup i j b : Set (ex.Fm i j b)) = ⊤) ∧ ∀ th, Nonempty (SideB (⟨T.ntw A.bare F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩ : TwNew D).toD7 ((⟨T.ntw A.bare F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩ : TwNew D).cf cf) ((⟨T.ntw A.bare F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩ : TwNew D).row A.row) low Pq ((⟨T.ntw A.bare F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩ : TwNew D).rat S) In.hL In.eig In.θ) := by
  intro hGAR D cf jE A S In low Pq M tup Q hM hPq hGal hRC hCh hstar hexp hsplit
  obtain ⟨c1, hc1⟩ := _root_.GlobalTheory.T.exists_galois_rep_family_bounded_alt hGAR D cf jE A hGal hRC hCh hstar
  obtain ⟨c2, hc2⟩ := _root_.GlobalTheory.T.exists_weight_data_integral_alt hGAR D cf jE A hstar hexp
  refine ⟨fun l _ j => ⟨(c1 l j).1 ⊔ (c2 l j).1, by haveI := (c1 l j).2; haveI := (c2 l j).2; infer_instance⟩,
    fun b0 b1 Sx T Sp hc0 hSb hconj hlow => ?_⟩
  have hb1 : ∀ (l : ℕ) [Fact l.Prime] j, (c1 l j).1 ≤ (b0 l j).1 := fun l _ j => le_trans le_sup_left (hc0 l j)
  have hb2 : ∀ (l : ℕ) [Fact l.Prime] j, (c2 l j).1 ≤ (b0 l j).1 := fun l _ j => le_trans le_sup_right (hc0 l j)
  obtain ⟨rho, hrho, hrhoS⟩ := hc1 b0 b1 Sx T Sp hb1
  obtain ⟨wt, hwt⟩ := hc2 b0 b1 Sx T Sp hb2
  have hfg := GlobalTheory.T.twisted_lattice_finitely_generated_spanning D S In T
  have hfg' : ∀ i j b, (BsupT D T S i j b).FG := fun i j b => (hfg i j b).1
  have hst := _root_.GlobalTheory.T.hkStab_of_subset_of_star_closed D cf jE A S In b0 b1 Sx T Sp hSb hstar
  obtain ⟨sd, hsd1, hsd2, hsd3, hsd4, hsd5⟩ := _root_.GlobalTheory.T.exists_signature_data_span_alt D cf jE A S In b0 b1 Sx T Sp hst hSb hstar
  have he := GlobalTheory.T.isCentralGroupAlgebraIdempotent_universal D
  have hpsi := GlobalTheory.T.genericUnipotentCharacterAtSide_eq_thetaSide D S In T hstar
  refine ⟨mkF D T S In hfg' hst sd rho hrho, mkEx D T S In A.bare hfg' hst sd rho hrho he Pq wt, D.nStage_trivialCharacter_coeff_eq,
    fun i j b => hfg i j b, fun th => ⟨?_⟩⟩
  let N : TwNew D := ⟨T.ntw A.bare (mkF D T S In hfg' hst sd rho hrho) (TwL.empty T),
    mkEx D T S In A.bare hfg' hst sd rho hrho he Pq wt, D.nStage_trivialCharacter_coeff_eq, th, Sp.br, Sp.br_ind⟩
  have hU := tied_U_clauses N.toD7 (fun (i : T.Tw) k => (Units.map (readT D T i true).toMonoidHom).comp (In.θ k))
    (fun _ => xiRedNZ N.toD7) (fun h i k => hpsi.2 h i k) rfl (fun i b u => hpsi.1 i b u)
  have hLev : ∀ (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
      (ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (T.Ok i k)ˣ), 1 ≤ j → j ≤ D.R.m → NX.AdmTw N.toD7 i k Q ψ →
      ∃ L : LevT D T i k, LevLawsT D T Pq In.θ i j b k Q ψ L ∧
        FiniteDimensional (FractionRing (T.Ok i k))
          ↥(NX.TypeSpF D.host.E D.R.nV (FractionRing (T.Ok i k)) (rhoKT D T wt i j b k) L.J L.χ) :=
    fun i j b k Q ψ h1 h2 hadm => _root_.GlobalTheory.T.places_over_real_subfield_split_alt hGAR D cf jE A S In Pq b0 b1 Sx T Sp hPq hsplit wt
      (fun i j b h1 h2 => ⟨(hwt i j b h1 h2).1, (hwt i j b h1 h2).2.1⟩) A.bare (mkF D T S In hfg' hst sd rho hrho)
      i j b k Q ψ h1 h2 hadm.1 hadm.2.1 hadm.2.2.1 hadm.2.2.2.1 hadm.2.2.2.2.1 hadm.2.2.2.2.2
  let E : NExpTied N.toD7 :=
    { U_eq := hU.1
      psiU_gen := hU.2.1
      psiU_side := hU.2.2.1
      psiU_xi := hU.2.2.2
      delU_cont := fun (i : T.Tw) Q M => (GlobalTheory.GalChar.universal_anticyclotomic_character_laws D.host T.cc (T.l i)).2.2.2.1 Q M
      delU_ine := fun i Q M hQ P hP =>
        GlobalTheory.T.inertia_surjective_of_admQ hGAR D cf b0 b1 Sx T Sp A.bare (mkF D T S In hfg' hst sd rho hrho) i Q M hQ P hP
      thU_empty := fun i j b M d => PEmpty.elim d
      sgnT := 1
      sgnT_one := rfl
      Wt := wt.Wt
      acgWt := fun (i : T.Tw) j b => wt.acg i j b
      modWt := fun (i : T.Tw) j b => wt.mod i j b
      fdWt := fun (i : T.Tw) j b => wt.fd i j b
      rhoW := fun (i : T.Tw) j b => wt.rhoW i j b
      rhoW_irr := fun i j b h1 h2 => (hwt i j b h1 h2).1
      rhoW_alg := fun i j b h1 h2 => (hwt i j b h1 h2).2.1
      tauG := fun (i : T.Tw) j b kv => tauT D T i j b kv
      sgnG := 1
      sgnG_one := rfl
      tau_galois_first_character := fun (i : T.Tw) j b kv x u h1 h2 hl hu => by
        have h := GlobalTheory.T.hasTameBlockCharacter_typePlace_not_over_l hGAR D cf b0 b1 Sx T Sp i j b kv h1 h2 hl
        show ((tauT D T i j b kv x : (FractionRing (T.O i))ˣ) : FractionRing (T.O i)) =
          baseCoeffToFractionRing D T i (NX.tameVal (T.chi1 i j b) (NX.pG D kv) ((1 : ℤ) * 1) u).1
        rw [show ((1 : ℤ) * 1) = 1 from rfl]
        unfold tauT
        rw [dite_eq_left h]
        exact h.choose_spec x u hu
      mtV := fun (i : T.Tw) j b k Q ψ h1 h2 hadm =>
        @NX.MtVReal.mk N.toD7 i j b k Q ψ 1 (wt.Wt i j b) (wt.acg i j b) (wt.mod i j b) (wt.rhoW i j b) (tauT D T i j b)
          (WkT D T wt i j b k)
          (inferInstance : AddCommGroup (WkT D T wt i j b k))
          (inferInstance : Module (FractionRing (T.Ok i k)) (WkT D T wt i j b k))
          (inferInstance : FiniteDimensional (FractionRing (T.Ok i k)) (WkT D T wt i j b k))
          (rhoKT D T wt i j b k)
          ((hwt i j b h1 h2).2.2.1 k)
          (isAlgWeightF_bc (K' := FractionRing (T.Ok i k)) (wt.rhoW i j b) (hwt i j b h1 h2).2.1)
          ⟨_, inferInstance, inferInstance, Module.finBasis (FractionRing (T.O i)) (wt.Wt i j b),
            Algebra.TensorProduct.basis (FractionRing (T.Ok i k)) (Module.finBasis (FractionRing (T.O i)) (wt.Wt i j b)),
            fun γ => toMatrix_bcRep (K' := FractionRing (T.Ok i k)) _ (wt.rhoW i j b) γ⟩
          (hLev i j b k Q ψ h1 h2 hadm).choose.J
          (hLev i j b k Q ψ h1 h2 hadm).choose.χ
          (hLev i j b k Q ψ h1 h2 hadm).choose_spec.1.1
          (hLev i j b k Q ψ h1 h2 hadm).choose_spec.1.2.1
          (hLev i j b k Q ψ h1 h2 hadm).choose.QP
          (hLev i j b k Q ψ h1 h2 hadm).choose_spec.1.2.2.2.2.1
          (hLev i j b k Q ψ h1 h2 hadm).choose_spec.1.2.2.2.2.2.1
          (hLev i j b k Q ψ h1 h2 hadm).choose_spec.1.2.2.2.2.2.2.1
          (hLev i j b k Q ψ h1 h2 hadm).choose.DP
          (hLev i j b k Q ψ h1 h2 hadm).choose_spec.1.2.2.2.2.2.2.2.1
          (hLev i j b k Q ψ h1 h2 hadm).choose_spec.1.2.2.2.2.2.2.2.2.1
          (hLev i j b k Q ψ h1 h2 hadm).choose_spec.1.2.2.2.2.2.2.2.2.2.1
          (hLev i j b k Q ψ h1 h2 hadm).choose.sp
          (hLev i j b k Q ψ h1 h2 hadm).choose_spec.1.2.2.2.2.2.2.2.2.2.2.1
          (hLev i j b k Q ψ h1 h2 hadm).choose.redG
          (hLev i j b k Q ψ h1 h2 hadm).choose_spec.1.2.2.2.2.2.2.2.2.2.2.2.1
          (fun κ h => by
            refine ((hLev i j b k Q ψ h1 h2 hadm).choose_spec.1.2.2.2.2.2.2.2.2.2.2.2.2 κ h).trans ?_
            have hg : ∀ (kv : Σ kk : Fin 2, D.nd.PlG kk),
                gValT D T In.θ i k b kv ((hLev i j b k Q ψ h1 h2 hadm).choose.sp (NX.pG D kv))
                  ((hLev i j b k Q ψ h1 h2 hadm).choose.redG kv) (tauT D T i j b kv)
                  (NX.locM ((hLev i j b k Q ψ h1 h2 hadm).choose.sp (NX.pG D kv)) κ) =
                NX.gVal N.toD7 i k b kv ((hLev i j b k Q ψ h1 h2 hadm).choose.sp (NX.pG N.toD7 kv))
                  ((hLev i j b k Q ψ h1 h2 hadm).choose.redG kv) (tauT D T i j b kv)
                  (NX.locM ((hLev i j b k Q ψ h1 h2 hadm).choose.sp (NX.pG N.toD7 kv)) κ) := by
              intro kv
              unfold gValT NX.gVal
              congr 1
              have hgp : (D.host.g kv.1).Prime := D.host.g_prime kv.1
              have hzmod : ∀ (n : ℕ) (hn : n.Prime) (s : SplitPlace D.host.E)
                  (red : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* ZMod n)
                  (τ : (ZMod n)ˣ →* (FractionRing (T.O i))ˣ)
                  (x : Matrix (Fin D.R.nV) (Fin D.R.nV) (s.v.adicCompletion (maximalRealSubfield D.host.E)))
                  (d₁ : Decidable (@IsUnit (ZMod n) (@ZMod.instField n ⟨hn⟩).toMonoid
                    (red (NX.intLift s.v (NX.detT D.R.r x)))))
                  (d₂ : Decidable (@IsUnit (ZMod n) (ZMod.commRing n).toMonoid
                    (red (NX.intLift s.v (NX.detT D.R.r x))))),
                  (@dite _ _ d₁ (fun h =>
                    toKkT D T i k ((τ (@IsUnit.unit (ZMod n) (@ZMod.instField n ⟨hn⟩).toMonoid _ h) :
                      (FractionRing (T.O i))ˣ) : FractionRing (T.O i))) (fun _ => 1)) =
                  (@dite _ _ d₂ (fun h =>
                    toKkT D T i k ((τ (@IsUnit.unit (ZMod n) (ZMod.commRing n).toMonoid _ h) :
                      (FractionRing (T.O i))ˣ) : FractionRing (T.O i))) (fun _ => 1)) := by
                intro n hn s red τ x d₁ d₂
                cases n with
                | zero => exact absurd hn Nat.not_prime_zero
                | succ m =>
                  cases d₁ with
                  | isFalse h₁ =>
                    cases d₂ with
                    | isFalse _ => rfl
                    | isTrue h₂ => exact absurd h₂ h₁
                  | isTrue h₁ =>
                    cases d₂ with
                    | isFalse h₂ => exact absurd h₁ h₂
                    | isTrue _ => rfl
              exact hzmod (D.host.g kv.1) hgp ((hLev i j b k Q ψ h1 h2 hadm).choose.sp (NX.pG D kv))
                ((hLev i j b k Q ψ h1 h2 hadm).choose.redG kv) (tauT D T i j b kv)
                (NX.locM ((hLev i j b k Q ψ h1 h2 hadm).choose.sp (NX.pG D kv)) κ) _ _
            exact congrArg₂ (· * ·) (congrArg₂ (· * ·) (Finset.prod_congr rfl fun kv _ => hg kv) rfl) rfl)
          (LinearEquiv.ofEq (MtSubT D T wt i j b k (LevLawsT D T Pq In.θ i j b k Q ψ))
            (NX.TypeSpF D.host.E D.R.nV (FractionRing (T.Ok i k)) (rhoKT D T wt i j b k)
              (hLev i j b k Q ψ h1 h2 hadm).choose.J (hLev i j b k Q ψ h1 h2 hadm).choose.χ)
            (by rw [MtSubT, dite_eq_left (hLev i j b k Q ψ h1 h2 hadm)]))
      rhoW_hw := fun i j b t h1 h2 => (hwt i j b h1 h2).2.2.2.1 t
      rhoW_wt := fun i j b t hj hjm sh lam h1 h2 => (hwt i j b hj hjm).2.2.2.2 t sh lam h1 h2 }
  exact
    { twF := { K0 := Sp.K0, eO0 := Sp.eO0, j0 := Sp.j0, Lw := Sp.Lw, eO := Sp.eO, eOk := Sp.eOk, iCq := Sp.iCq,
               S0x := fun _ => Sx }
      tw := { pl_emb := fun i => ⟨Sp.eTw i, Sp.pl_emb i⟩
              ringSpec_baseIntegersEquiv_algebraMap := Sp.ringSpec_baseIntegersEquiv_algebraMap
              ringSpec_baseEmbedding_compatible := Sp.ringSpec_baseEmbedding_compatible
              eO_alg := Sp.eO_alg
              eOk_alg := Sp.eOk_alg
              mu_g := Sp.mu_g
              hk_split := fun i j b k P hP => _root_.GlobalTheory.T.lattice_basis_free_module_place_alt D cf jE A S In b0 b1 Sx T Sp hSb hstar hst i j b k P
                (hfr := (mkF D T S In hfg' hst sd rho hrho).freeB i j b)
                (hfi := (mkF D T S In hfg' hst sd rho hrho).finB i j b) hP
              ringSpec_excludedPlaces_eq := Sp.ringSpec_excludedPlaces_eq
              concreteTwistFrame_extraExcludedPlaces_conj := fun i P P' h h' => hconj P P' h h'
              B_range := fun (i : T.Tw) j b => by
                show LinearMap.range (BI D T S In i j b).subtype = _
                rw [Submodule.range_subtype]
                rfl
              sig_inj := hsd2
              qs_pos := fun i lam => PEmpty.elim lam
              concreteTwistFrame_extraExcluded_over_smallPrimes := fun i => hlow }
      cover := fun w => GlobalTheory.T.exists_twistIndex_of_coefficientField_place D cf b0 b1 Sx T Sp w
      chiD := { mu0 := Sp.mu0H, etaT := Sp.etaH, del := Sp.delH, psi := fun a => A.bare.elim a,
                chiI := fun s lam => PEmpty.elim lam, embO := Sp.embO }
      chi := { psi := fun a => A.bare.elim a, del_fix := Sp.del_fix, delta := Sp.delta, chi1 := Sp.chi1,
               ringSpec_sidedEmbedding_fixedField := Sp.ringSpec_sidedEmbedding_fixedField, etaT_unr := Sp.etaT_unr, etaT_inf := Sp.etaT_inf,
               lamG := fun s lam => PEmpty.elim lam }
      eta_eq := Sp.eta_eq
      ringSpec_normalisedCharacter_eq := Sp.ringSpec_normalisedCharacter_eq
      del_eq := Sp.del_eq
      iCq_embO := Sp.iCq_embO
      embO_star := Sp.embO_star
      deltaRead := Sp.deltaRead
      exp := E
      pq := fun (i : T.Tw) j b k Q ψ h1 h2 hadm =>
        ⟨(hLev i j b k Q ψ h1 h2 hadm).choose_spec.1.2.2.1, (hLev i j b k Q ψ h1 h2 hadm).choose_spec.1.2.2.2.1⟩
      psiU := fun i b u hu hu' => rfl
      rho := In.rho
      chiL := In.chi
      hs := In.hs
      eF := fun i j b h1 h2 => (GlobalTheory.T.twistLiftForms_eq_baseChange_rationalDatumForms D S In T A.bare hfg' hst sd rho hrho he Pq wt i j b h1 h2).choose
      bsup := fun i j b h1 h2 => (GlobalTheory.T.twistLiftForms_eq_baseChange_rationalDatumForms D S In T A.bare hfg' hst sd rho hrho he Pq wt i j b h1 h2).choose_spec.1
      act := fun i j b h1 h2 => (GlobalTheory.T.twistLiftForms_eq_baseChange_rationalDatumForms D S In T A.bare hfg' hst sd rho hrho he Pq wt i j b h1 h2).choose_spec.2.1
      cHk := fun (i : T.Tw) b P => cHkT D T i b P
      hkEq := fun i j b h1 h2 k P x _ _ _ =>
        (GlobalTheory.T.twistLiftForms_eq_baseChange_rationalDatumForms D S In T A.bare hfg' hst sd rho hrho he Pq wt i j b h1 h2).choose_spec.2.2 k P x
      cHk_del := fun i b P hP σ hσ => GlobalTheory.T.heckeComparisonUnitAtFrobenius_eq_delta D T i b P hP σ hσ
      hk_emb := fun (i : T.Tw) j b k P x h1 h2 hP hs hk => by
        rcases Nat.eq_zero_or_pos k with rfl | hk0
        · show ((hkB D T S In hst i j b 0 P x : ↥(BI D T S In i j b)) : FmT D T S i j b) =
            hkT D T S In i j b 0 P (x : ↥(BI D T S In i j b)).1
          rw [show hkB D T S In hst i j b 0 P = 1 from hkB_zero D T S In hst i j b P,
            show hkT D T S In i j b 0 P = 1 from hkT_zero D T S In i j b P]
          rfl
        · show ((hkB D T S In hst i j b k P x : ↥(BI D T S In i j b)) : FmT D T S i j b) =
            hkT D T S In i j b k P (x : ↥(BI D T S In i j b)).1
          unfold hkB
          rw [dite_eq_left ⟨h1, h2, hk0, hk, hs, hP⟩]
          rfl
      sigSpan := fun i j b h1 h2 => hsd1 i j b h1 h2
      rowS := sd.rowS
      rowS_eig := hsd4
      hEig_zero := hsd5
      rhoS := fun i s => ⟨(hsd3 i s).1, (hsd3 i s).2, fun π hc hr hl φ ι hz hι =>
        hrhoS i (sd.rowS i s) (sd.side i s) ⟨sd.jS i s, (sd.jS_range i s).1, (sd.jS_range i s).2, (hsd3 i s).1⟩
          (hsd3 i s).2 π hc hr hl φ ι hz hι⟩ }
end GlobalTheory.HeightCounting.FormsStep
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SecondStepStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.row_cusp_multiplicity_input_alt : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (S : RatDat D.ntw) (In : RatIn D S) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (M : MtFam D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E) (Q : D.what₂.places.Pl → Finset (PlE D.host)), MtInput D M tup Q → (∀ v, NG.OverPl (Pq v) v) → GalEx D → RowCusp D A.row → GlobalTheory.RowTie.ChebSplit D.nd → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → ∃ c0 : Big D, ∀ (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T), (∀ (l : ℕ) [Fact l.Prime] j, (c0 l j).1 ≤ (b0 l j).1) → In.Sb ⊆ Sx → (∀ P P', P ∈ Sx → IsConjPl D.host P P' → P' ∈ Sx) → (∀ p ∈ low, placesOver D.host.E p ⊆ ↑Sx) → ∃ (F : TwF T) (ex : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw A.bare F (TwL.empty T))) (h0 : _), (∀ i j b, (ex.Bsup i j b).FG ∧ Submodule.span (FractionRing ((T.ntw A.bare F (TwL.empty T)).O i)) (ex.Bsup i j b : Set (ex.Fm i j b)) = ⊤) ∧ ∀ th, Nonempty (SideB (⟨T.ntw A.bare F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩ : TwNew D).toD7 ((⟨T.ntw A.bare F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩ : TwNew D).cf cf) ((⟨T.ntw A.bare F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩ : TwNew D).row A.row) low Pq ((⟨T.ntw A.bare F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩ : TwNew D).rat S) In.hL In.eig In.θ) := by
  first | exact @_root_.GlobalTheory.HeightCounting.FormsStep.second_step_alt | exact _root_.GlobalTheory.HeightCounting.FormsStep.second_step_alt | (intros; apply _root_.GlobalTheory.HeightCounting.FormsStep.second_step_alt <;> assumption)
end
end
