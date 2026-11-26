module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EventuallyUnr
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.RankGrowthBoundSmallScale
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HermitianPairingBilinearOnPair

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsConj
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open UpperTheory.GalN (Ab)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.GalS
section Local
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
end Local
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}
  [IsAlgClosure E Ω] [IsCMField E]
def NiceAlt (π : CuspSub E a) {w : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω} (h : IsPlaceOver A w) : Prop :=
  ∃ σ, π.IsLocComp w σ ∧ ∃ rc : IrrGL (k := w.adicCompletion E) → WD h, _root_.UpperTheory.Zero.LLC.IsRecT h rc ∧ NcW (rc (algNorm σ))
structure LocalConditionsAbovePrime (π : CuspSub E a) (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l))
    (HT : (E →+* Qbar l) → Multiset ℤ) (P : LocPrime l) {w : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}
    (h : IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw) : Prop where
  deRham : _root_.UpperTheory.GalS.NiceAlt π h → IsdRAt P Bw (r.comp (Dec (F := E) A).subtype)
  jumps : _root_.UpperTheory.GalS.NiceAlt π h → ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
    IsJumpsAt P Bw (r.comp (Dec (F := E) A).subtype) τ (HT τ)
  crys : ∀ σ, π.IsLocComp w σ → SmGL.IsSpherical σ.ρ → IsCrysAt P Bw (r.comp (Dec (F := E) A).subtype)
structure IsGalUAlt (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)) (ι : Qbar l ≃+* ℂ)
    (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ) : Prop where
  cont : Continuous r
  ss : IsSSRep r
  away : ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (rc : IrrGL (k := w.adicCompletion E) → WD h), _root_.UpperTheory.Zero.LLC.IsRecT h rc → ∀ σ, π.IsLocComp w σ → Aw (wdOf h hl ι r) (rc (algNorm σ))
  weights : ∀ τ : E →+* Qbar l, (HT τ).map (fun n : ℤ => (n : ℂ)) =
    ((CG.mk π).infChar (ι.toRingHom.comp τ)).map fun z => ((a : ℂ) - 1) / 2 - z
  weights_conj : ∀ τ : E →+* Qbar l,
    HT (τ.comp (IsCMField.complexConj E).toRingEquiv.toRingHom) = (HT τ).map (wt - ·)
  above : ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw), _root_.UpperTheory.GalS.LocalConditionsAbovePrime π ι r HT P h Bw hj
def PairUAlt : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)), (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.PolarizedPair π χ →
      ∃ (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ), _root_.UpperTheory.GalS.IsGalUAlt π χ ι r wt HT
def CuspUAlt : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)), (CG.mk π).IsRegAlg → IsPolarized π χ →
      ∃ (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ), _root_.UpperTheory.GalS.IsGalUAlt π χ ι r wt HT
def CarUAlt : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 2 ≤ a → ∀ π : CuspSub E a, π.IsCsd → (CG.mk π).IsRegAlg →
    ∃ (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ),
      _root_.UpperTheory.GalS.IsGalUAlt π (quadChar E ^ a) ι r wt HT ∧
    ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)), w ∈ placesOver E l → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw)
      (σ : SmIrr (GL (Fin a) (w.adicCompletion E))), π.IsLocComp w σ →
      ∀ rc : IrrGL (k := w.adicCompletion E) → WD h, _root_.UpperTheory.Zero.LLC.IsRecT h rc → NcW (rc (algNorm σ)) →
        Ab (wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)) (rc (algNorm σ))
theorem CuspUAlt.of_isCsd (H : _root_.UpperTheory.GalS.CuspUAlt) {E : Type} (Ω : Type) [Field E]
    [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    {a : ℕ} (ha : 1 ≤ a) {π : CuspSub E a} (hr : (CG.mk π).IsRegAlg) (hc : π.IsCsd) :
    ∃ (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ),
      _root_.UpperTheory.GalS.IsGalUAlt π (quadChar E ^ a) ι r wt HT :=
  H E Ω l ι a ha π _ hr (isPolarized_of_isCsd hc)
theorem IsGalUAlt.aw {π : CuspSub E a} {χ : HChar (maximalRealSubfield E)} {ι : Qbar l ≃+* ℂ}
    {r : G E Ω →* GL (Fin a) (Qbar l)} {wt : ℤ} {HT : (E →+* Qbar l) → Multiset ℤ}
    (H : _root_.UpperTheory.GalS.IsGalUAlt π χ ι r wt HT) {w : HeightOneSpectrum (𝓞 E)}
    (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) {A : ValuationSubring Ω} {h : IsPlaceOver A w}
    {rc : IrrGL (k := w.adicCompletion E) → WD h} (hrc : _root_.UpperTheory.Zero.LLC.IsRecT h rc) {σ : SmIrr (GL (Fin a) (w.adicCompletion E))}
    (hσ : π.IsLocComp w σ) :
    Aw (wdOf h hl ι r) ((rc (IrrGL.of σ.ρ σ.smooth σ.irred)).lpTw ((1 - (a : ℝ)) / 2)) :=
  _root_.GlobalTheory.GalOfCusp.rec_algNorm_alt hrc σ ▸ H.away w hl A h rc hrc σ hσ
theorem mergeP'_alt (_ : GlobalTheory.Published.AutomorphicFormsFiniteGL) (_ : _root_.UpperTheory.Zero.LLC.RecTExists) (_ : _root_.UpperTheory.GalS.CuspUAlt) (h : _root_.UpperTheory.GalS.CarUAlt)
    (_ : GlobalTheory.Published.RegularAlgebraicPurity) : _root_.UpperTheory.GalS.CarUAlt := h
end UpperTheory.GalS
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocParOfCharUnrIff
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocParOfCharUnrIff
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.RankOneComp
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP _root_.Formalism.L2 _root_.Formalism.L2.Host _root_.Formalism.L2.NT NumberField
  IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
section Char
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [_root_.NumberField.IsTotallyComplex E]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
theorem locParT_ofChar_unr_iff_unrAt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (χ : HChar E) (h : IsPlaceOver A w) :
    (_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.ofChar χ) h).unr ↔ χ.UnrAt w := by
  first | (have hOpn := UpperTheory.One.M.opn _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h); obtain ⟨a, ha, ε, H⟩ := hOpn) | obtain ⟨a, ha, ε, -, H⟩ := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h
  rw [_root_.GlobalTheory.CuspRep.ParLaws.local_parameter_of_hecke_character_eq_reciprocity, H.one, Test.unr_lpOfChar_iff ha (ParLaws.isSmoothChar_loc χ w)]
  refine forall_congr' fun x => imp_congr_left ?_
  have h0 : Valued.v (x : w.adicCompletion E) ≠ 0 := by simp
  rw [← ord_eq_zero_iff, SphCompletion.ord_completion, neg_eq_zero, IsUnitAt]
  constructor
  · intro hl
    rw [← WithZero.exp_log h0, hl, WithZero.exp_zero]
  · intro hv
    rw [hv, WithZero.log_one]
theorem frobEig_locParT_ofChar_of_unrAt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (χ : HChar E) (h : IsPlaceOver A w) (hu : χ.UnrAt w) :
    (_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.ofChar χ) h).frobEig = {(((χ.val w)⁻¹ : ℂˣ) : ℂ)} := by
  have e : χ.loc w = SmGL.unrChar (w.adicCompletion E) (χ.val w) := by
    refine MonoidHom.ext fun x => ?_
    have h2 := unif_spec w
    have h0 : Valued.v (x : w.adicCompletion E) ≠ 0 := by simp
    have h1 : IsUnitAt w (x * (atFin w (unif w) ^ ord (w.adicCompletion E) x)⁻¹) := by
      unfold IsUnitAt IsUnifAt at *
      rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, map_mul,
        map_inv₀, map_zpow₀, h2, ← WithZero.exp_zsmul, SphCompletion.ord_completion]
      simp only [smul_eq_mul, mul_neg, mul_one, neg_neg]
      rw [WithZero.exp_log h0, mul_inv_cancel₀ h0]
    have h3 := hu _ h1
    rw [map_mul, map_inv, map_zpow, mul_inv_eq_one] at h3
    exact h3
  first | (have hOpn := UpperTheory.One.M.opn _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h); obtain ⟨a, ha, ε, H⟩ := hOpn) | obtain ⟨a, ha, ε, -, H⟩ := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h
  have e2 : _root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.ofChar χ) h = WD.mk (WDRep.diag h fun _ : Fin 1 => (χ.val w)⁻¹) := by
    rw [_root_.GlobalTheory.CuspRep.ParLaws.local_parameter_of_hecke_character_eq_reciprocity, H.one]
    have : ∀ (ξ : (w.adicCompletion E)ˣ →* ℂˣ) (hξ : WeilDeligne.IsSmooth (ξ.comp a)),
        ξ = SmGL.unrChar (w.adicCompletion E) (χ.val w) →
        WD.lpOfChar h (ξ.comp a) hξ = WD.mk (WDRep.diag h fun _ : Fin 1 => (χ.val w)⁻¹) := by
      rintro ξ hξ rfl
      exact Test.lpOfChar_unrChar ha _ _
    exact this _ _ e
  rw [e2, WD.frobEig_diag]
  simp
end Char
theorem e_locG_eq_rcAt_ofDet_of_isComp : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D),
    ∀ (π : D.naut.CG 1) (w : PlE D.host) (ξ : (w.adicCompletion D.host.E)ˣ →* ℂˣ) (h : IsComp (P.chr.e1 π).1 w ξ),
    P.T.e w (D.naut.locG π w) = _root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D w 1 (Irr.ofDet 1 ξ h.1) := by
  intro _ hL D P π w ξ h
  haveI := host_isCMField D.host
  set χ' := (CGu.equivChar D.host.E (P.cg.e 1 π)).1 with hχ'
  set χ := (P.chr.e1 π).1 with hχ
  have hloc : ∀ v, P.T.e v (D.naut.locG π v) = _root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.ofChar χ') (D.nd.plOm.2 v) := fun v => by
    rw [P.cg.loc, hχ', CGu.ofChar_equivChar]; rfl
  have unr' : ∀ v, D.naut.unr (D.naut.locG π v) ↔ χ'.UnrAt v := fun v => by
    rw [P.T.unr, hloc v]; exact _root_.GlobalTheory.RankOneComp.locParT_ofChar_unr_iff_unrAt hL χ' _
  have hchar : χ' = χ := by
    rw [← mul_inv_eq_one]
    apply GlobalTheory.HeckeSplitRow.eq_one_of_split D.host
    filter_upwards [D.naut.locG_unr_ae π] with v hv _
    have u1 := (P.chr.unr_iff π v).1 hv
    have u2 := (unr' v).1 hv
    refine ⟨fun x hx => ?_, ?_⟩
    · change χ'.loc v x * (χ.loc v x)⁻¹ = 1
      rw [u2 x hx, u1 x hx, inv_one, mul_one]
    · have hf := P.chr.frob π v u1
      have hf' : D.naut.frobEig (D.naut.locG π v) = {(((χ'.val v)⁻¹ : ℂˣ) : ℂ)} := by
        rw [P.T.frobEig _ _ hv, hloc v]; exact _root_.GlobalTheory.RankOneComp.frobEig_locParT_ofChar_of_unrAt hL χ' _ u2
      rw [hf', Multiset.singleton_inj, Units.val_inj, inv_inj] at hf
      rw [HChar.val_mul, HChar.val_inv, hf, mul_inv_cancel]
  have hcomp : IsComp χ w (χ.loc w) := ⟨ParLaws.isSmoothChar_loc χ w, fun x => rfl⟩
  obtain ⟨ξ₀, -, huniq, -⟩ := GlobalTheory.T.heckeChar_localComponent_exists_unique_unitary D.host.E χ w
  have hξ : ξ = χ.loc w := (huniq _ h).trans (huniq _ hcomp).symm
  subst hξ
  rw [hloc, _root_.GlobalTheory.CuspRep.ParLaws.local_parameter_of_hecke_character_eq_reciprocity, _root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep]
  rw [hchar]
  rfl
end GlobalTheory.RankOneComp
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocParOfCharUnrIffStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.T_e_locG_eq_rcAt_ofDet : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (π : D.naut.CG 1) (w : PlE D.host) (ξ : (w.adicCompletion D.host.E)ˣ →* ℂˣ) (h : IsComp (P.chr.e1 π).1 w ξ), P.T.e w (D.naut.locG π w) = _root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D w 1 (Irr.ofDet 1 ξ h.1) := by
  first | exact @_root_.GlobalTheory.RankOneComp.e_locG_eq_rcAt_ofDet_of_isComp | exact _root_.GlobalTheory.RankOneComp.e_locG_eq_rcAt_ofDet_of_isComp | (intros; apply _root_.GlobalTheory.RankOneComp.e_locG_eq_rcAt_ofDet_of_isComp <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocParTwistAbsPow
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.HeightCounting.Blocks
open NumberField IsDedekindDomain Polynomial Filter
section Satake
open GlobalTheory.LFun GlobalTheory.PRep GlobalTheory.CuspRep Formalism.UG
variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
variable [_root_.NumberField.IsTotallyComplex E]
end Satake
section Local
open GlobalTheory.CuspRep GlobalTheory.CuspRep.ParLaws GlobalTheory.WeilDeligne GlobalTheory.LocLanglands Formalism.ConjugateSelfDual ReciprocityTheory.Gal _root_.Formalism.L2.Host
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {a : ℕ}
variable [_root_.NumberField.IsTotallyComplex E] (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL)
include hF in
theorem local_parameter_twist_abs_pow (π : CG E a) {ν : HChar E} {s : ℝ} (hν : ν.IsAbsPow s) (h : IsPlaceOver A w) :
    _root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (π.twist ν) h = (_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL π h).lpTw s := by
  induction π using Quotient.inductionOn with | _ π =>
  obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp hF E a π w
  first | (have hOpn := UpperTheory.One.M.opn _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h); obtain ⟨_, _, _, H⟩ := hOpn) | obtain ⟨_, _, _, -, H⟩ := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h
  refine (_root_.GlobalTheory.CuspRep.ParLaws.local_parameter_eq_reciprocity_of_is_local_component hL (hσ.twist ν) h).trans ?_
  rw [show _root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (Quotient.mk _ π) h = _ from _root_.GlobalTheory.CuspRep.ParLaws.local_parameter_eq_reciprocity_of_is_local_component hL hσ h, ← H.nu_eq]
  refine congrArg _ ((GlobalTheory.LocGL.IrrGL.tw_of σ.ρ σ.smooth σ.irred _ (isSmoothChar_loc ν w)).symm.trans ?_)
  unfold GlobalTheory.LocGL.IrrGL.nu
  congr 1
  exact loc_of_isAbsPow hν w
end Local
section Polar
end Polar
section Record
end Record
section True
end True
end GlobalTheory.HeightCounting.Blocks
namespace GlobalTheory.HeightCounting
end GlobalTheory.HeightCounting
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BotOfPlacedBy
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BotOfPlacedBy
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.LevZero
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
theorem pg_isTypePlaces_alt (W : _root_.GlobalTheory.MiS.RealPackAlt ex) : GlobalTheory.Core.Mi.IsTypePlaces (_root_.GlobalTheory.Fam.pk_z W).Pg := by
  have H := W.Q.charW.base.lev
  let M := (_root_.GlobalTheory.Fam.pk_z W).toLevCh
  let μ := W.P.A3.A.μ0
  let M' : LevCh D Unit := { M with xiH := fun _ => M.xiH μ, xi := fun _ => M.xi μ, Q := fun _ => M.Q μ, xiR := fun _ => M.xiR μ }
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩ := H
  exact GlobalTheory.SeeSaw.ComCols.isTypePlaces_of_levCh (L := M') ⟨h1, h2, fun _ => h3 _, fun _ _ _ => rfl, h5, fun _ => h6 _, fun _ => h7 _,
    fun _ => h8 _, h9, fun _ => h10 _, fun _ => h11 _, fun p hp => (h12 p hp).imp fun _ e _ => e _, fun _ => h13 _, h14, fun _ => h15 _,
    h16, h17, h18, h19⟩
set_option maxHeartbeats 1000000 in
theorem stZero_is_com_zero_of_pkHyp (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (hP : _root_.GlobalTheory.Fam.PackageHypotheses W) (hm : 0 < D.R.m) : (_root_.GlobalTheory.LevZero.levelZeroState W).st.Is (_root_.GlobalTheory.BaseChain.com_z W) 0 := by
  have h := _root_.GlobalTheory.BaseChain.stage_y_is W hP 0 hm
  exact ⟨h.rank, h.sigOK, h.sig, h.par, h.selfDual, h.frame, h.base, ⟨r_le_Y 0, fun _ => 1, rfl⟩, h.haar, h.fund⟩
set_option maxHeartbeats 1000000 in
theorem bot_stZero_of_gRead (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (hP : _root_.GlobalTheory.Fam.PackageHypotheses W) (hm : 0 < D.R.m) {u : D.what₂.Word} (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (v : VCom f.c) (hv : v.Is)
    (ht : _root_.GlobalTheory.Fam.CommutingVectorTie f v) {n : ℕ} (G : (_root_.GlobalTheory.Fam.pk_z W).Pg → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg) (hR : _root_.GlobalTheory.Fam.LocalGroupReading f (fun i => G (pl i)) pl) :
    Bot (c := f.c) (_root_.GlobalTheory.BaseChain.com_z W) (_root_.GlobalTheory.LevZero.levelZeroState W) (f.g.b 0) G := by
  refine ⟨_root_.GlobalTheory.BaseChain.com_is_alt W hP, rfl, _root_.GlobalTheory.LevZero.stZero_is_com_zero_of_pkHyp W hP hm, ?_, _root_.GlobalTheory.LevZero.pg_isTypePlaces_alt W, ?_, ?_, ?_⟩
  · have h := hv.b 0
    rw [ht.b 0] at h
    exact h
  · intro PP
    obtain ⟨i, rfl⟩ := pl.surjective PP
    exact ⟨(hR.idem i).1, (hR.idem i).2, fun a ha => hR.frame i 0 a ha⟩
  · intro g
    refine (hR.lev g).1.trans ⟨fun h PP => ?_, fun h i => h (pl i)⟩
    obtain ⟨i, rfl⟩ := pl.surjective PP
    exact h i
  · intro g x hx
    have h := (hR.lev g.1).2 g.2 (fun i => x (pl i)) (fun i => hx (pl i))
    exact h.trans (Equiv.prod_comp pl (fun PP => (G PP).S.P.lam (x PP)))
set_option maxHeartbeats 1000000 in
theorem bot_of_placedBy_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom f.c) (o : TDat f.c k ι) (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), _root_.GlobalTheory.LevZero.PlacedByLocalGroups f B v o G pl → GlobalTheory.LevZero.Bot (c := f.c) (_root_.GlobalTheory.BaseChain.com_z W) (_root_.GlobalTheory.LevZero.levelZeroState W) (f.g.b 0) (fun PP => G (pl.symm PP)) := by
  intro D L hT Gi Gl Kc Yd cX ex W hP u f B k _ _ _ _ ι v o n G pl h
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have e : (fun i => G (pl.symm (pl i))) = G := funext fun i => by rw [Equiv.symm_apply_apply]
  have hR : _root_.GlobalTheory.Fam.LocalGroupReading f (fun i => G (pl.symm (pl i))) pl := by rw [e]; exact h.read
  exact _root_.GlobalTheory.LevZero.bot_stZero_of_gRead W hP hm f v h.vis h.tie (fun PP => G (pl.symm PP)) pl hR
end GlobalTheory.LevZero
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BotOfPlacedByStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_local_type_data_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom f.c) (o : TDat f.c k ι) (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), _root_.GlobalTheory.LevZero.PlacedByLocalGroups f B v o G pl → GlobalTheory.LevZero.Bot (c := f.c) (_root_.GlobalTheory.BaseChain.com_z W) (_root_.GlobalTheory.LevZero.levelZeroState W) (f.g.b 0) (fun PP => G (pl.symm PP)) := by
  first | exact @_root_.GlobalTheory.LevZero.bot_of_placedBy_alt | exact _root_.GlobalTheory.LevZero.bot_of_placedBy_alt | (intros; apply _root_.GlobalTheory.LevZero.bot_of_placedBy_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RankGrowthBoundSmallScale
set_option synthInstance.maxHeartbeats 200000

section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace GlobalTheory.CovTop.HodgeSteps
theorem rk_le_alt_alt : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoverDegree → _root_.GlobalTheory.CovTop.ShareCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ s : ℕ, 1 ≤ s → s ≤ 2 → (Y.rk (Gs p i (s * cZero (Fm.D x ι) ((i : ℕ) + 1))) : ℝ) ≤ (1 + min (1 / 2) ((Fm.L x ι).sc.b / (PP * kap p i))) * Y.rk (Gs p i (-(cZero (Fm.D x ι) ((i : ℕ) + 1)))) := by
  intro hX hP hSi hTo hG hQ hN hDG hS hFD hDeg hSh
  refine ((((((((((hDG.and hS).and hFD).and hDeg).and hSh).and (_root_.GlobalTheory.T.weight_parameter_strict_antitone_alt hS)).and (_root_.GlobalTheory.T.size_bounds_for_family_alt hS)).and
    (_root_.GlobalTheory.T.valuation_multiplicity_run_estimate_alt hP hG hQ hSi hTo hN hDG hS hFD)).and (_root_.GlobalTheory.T.abs_flat_c1_add_logOm_le_and_logSum_badPrimes_le hFD)).and _root_.GlobalTheory.HSApp.wtBig_run_alt).and _root_.GlobalTheory.CovTop.WtShape.wtN_z).imp fun Fm CH _ h => ?_
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, -, a1⟩, A, -, a2⟩, _, -, a3⟩, _, -, a4⟩, _, -, a5⟩, _, -, a6⟩, _, -, a7⟩, _, -, a8⟩, _, -, a9⟩,
    _, -, a10⟩, _, -, a11⟩ := h
  obtain ⟨x0, h⟩ := (((((((((a1.and a2).and a3).and a4).and a5).and a6).and a7).and a8).and a9).and a10).and a11
  refine ⟨0, le_rfl, x0, fun x hx hle ι p hp i hi Y hY s hs1 hs2 => ?_⟩
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, b5⟩, b6⟩, b7⟩, b8⟩, b9⟩, b10⟩, b11⟩ := h x hx hle ι p hp
  clear h a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
  obtain ⟨-, g1, -, -, -, hfin, -, -⟩ := b1 i hi Y hY
  obtain ⟨hb1, -, -, -, -, hbk, hq⟩ := b2 i
  obtain ⟨⟨u1, hu⟩, hq⟩ := hq hi
  obtain ⟨-, hρ0, hρ1, -⟩ := hq u1 hu
  obtain ⟨δ, hδ, hdg⟩ := b4 i hi Y hY u1 hu
  have hsh := b5 i hi Y hY u1 hu
  obtain ⟨hp1, hq1, hf, hu1, hA, -, hanti⟩ := b6 i hi
  obtain ⟨hL, hj, hL1, -, -, -, -, -, hf8, hr100, -, -, hPP, -, hz1, hz2, -⟩ := b7 i hi Y hY
  have hval := b8 i hi Y hY
  obtain ⟨hC, hl, hF, -⟩ := b9 i hi Y hY
  have hgap := (b10 i hi).gaps
  have hdom := (b11 i).dom
  have hfl := b3 i hi Y hY
  clear b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 hq
  rw [← hu1 u1 hu] at hA hanti hz1 hz2 hval hgap
  clear hu1
  generalize (Fm.parT x hx ι).PP = PP at *
  rw [← CompHS.dimFlag_eq] at hgap
  have hd3 : 3 ≤ CompHt.dimFlag (dat p i) := by
    rw [CompHS.dimFlag_eq, FlagTan.dimFlag]
    exact le_trans hf (Nat.le_mul_of_pos_right _ (Nat.choose_pos (by omega)))
  have hPP100 : 100 ≤ PP := by
    refine le_trans ?_ hPP
    have c1 : (8 : ℝ) ≤ (Fm.D x ι).R.f := by exact_mod_cast hf8
    have c2 : (100 : ℝ) ≤ (Fm.D x ι).R.r := by exact_mod_cast hr100
    have c3 : (8 * 100 * 1 : ℝ) ≤ zBase (Fm.L x ι) := by
      unfold zBase
      gcongr
    exact le_trans (by linarith) (le_self_pow₀ (by linarith) (by norm_num))
  have hT : 1000 * (CompHt.dimFlag (dat p i) : ℝ) ^ 2 ≤ lenT p i PP := by
    refine le_trans ?_ (Nat.le_ceil _)
    have c1 := (Fm.D x ι).R.two_le_m
    have c2 := (Fm.D x ι).R.m_add_three_le_k
    have c3 : (0 : ℝ) < (Fm.D x ι).R.m := by exact_mod_cast (by omega : 0 < (Fm.D x ι).R.m)
    have c4 : ((Fm.D x ι).R.m : ℝ) ≤ (Fm.D x ι).R.k := by exact_mod_cast (by omega : (Fm.D x ι).R.m ≤ (Fm.D x ι).R.k)
    have c5 : 1000 ≤ PP ^ 2 := by nlinarith
    rw [le_div_iff₀ c3]
    gcongr
  obtain ⟨a, ha1, ha2⟩ := exists_jet_order _ _ _ (by omega) hT hρ0 hz2
  have hbir := _root_.GlobalTheory.T.birOn_wtOf_of_consecutive_gap_bound hX hG hQ hSi (_root_.GlobalTheory.T.covering_topology_refinement hP) hP.q15 hP.q16 _ p.T hL _ hp1 hq1 Y _ _ hY.1 u1 fun τ a b hb => by
    rw [← gap_eq _ hb]
    refine le_trans ?_ (hgap τ a (hb ▸ b.2))
    exact_mod_cast bir_gap_le _ _ hd3
  have hboth := GlobalTheory.T.componentImageDegree_between_of_proportionality _ _ _ _ _ _ _ Y.U hY.1.unf (_root_.GlobalTheory.T.proportionality_principle_compactification hP hSi hTo hN _ p.T hL _ hp1 hq1 hf hj Y _ _ hY.1).1
    (_root_.GlobalTheory.T.compactification_top_chern_eq_volume hP hSi hTo hN _ p.T hL _ hp1 hq1 hf hj Y _ _ hY.1) u1 (fun τ => (hA τ).1) (fun τ => (hA τ).2) hbir hval
  have hc0 : 1 ≤ cZero (Fm.D x ι) ((i : ℕ) + 1) := by
    have := (cZeroN_isLeast (Fm.D x ι) ((i : ℕ) + 1)).1.2.2
    unfold cZero
    omega
  have ew : uW p i + (s * cZero (Fm.D x ι) ((i : ℕ) + 1)) • hodgeWt (dat p i) =
      fun τ => uM p i τ + (((s + 1 : ℕ) : ℤ) * cZero (Fm.D x ι) ((i : ℕ) + 1)) • hodgeWt (dat p i) τ := by
    funext τ k
    simp only [uM, uW, uMinus, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  have em : uW p i + (-(cZero (Fm.D x ι) ((i : ℕ) + 1))) • hodgeWt (dat p i) = uM p i := by
    rw [neg_smul, ← sub_eq_add_neg]
    rfl
  have hl1 : ∀ τ, Antitone ((uW p i + (s * cZero (Fm.D x ι) ((i : ℕ) + 1)) • hodgeWt (dat p i)) τ) := fun τ => by
    rw [ew]
    exact (hanti (s + 1) (by omega) τ).1
  have hl2 : ∀ τ, Antitone (((lenT p i PP + CompHt.dimFlag (dat p i) + 4 : ℕ) : ℤ) • u1 τ -
      (uW p i + (s * cZero (Fm.D x ι) ((i : ℕ) + 1)) • hodgeWt (dat p i)) τ) := fun τ => by
    rw [ew]
    have := (hanti (s + 1) (by omega) τ).2
    rwa [if_neg (Nat.succ_ne_zero s)] at this
  have hl3 : ∀ τ, 1 ≤ gap ((uW p i + (s * cZero (Fm.D x ι) ((i : ℕ) + 1)) • hodgeWt (dat p i)) τ) ((dat p i).p - 1) :=
    fun τ => by
      rw [ew]
      refine le_trans ?_ (le_gap_bar (dat p i) hp1 hq1 (uM p i) τ ?_ _)
      · push_cast
        nlinarith [Int.natCast_nonneg s]
      · simpa using (hanti 0 (by omega) τ).1
  have hev : Even (p.κ i).n := (p.κ i).n_even
  have g2 : Y.GoodAt (Gs p i (s * cZero (Fm.D x ι) ((i : ℕ) + 1))) :=
    _root_.GlobalTheory.CovTop.HodgeSteps.covering_goodAt_shift hP _ p.T hL _ hj Y _ _ hY.1 (le_add_right hp1) hC hl hF _ _ ((Fm.D x ι).R.k - 1) _ hev
      (_root_.GlobalTheory.T.covering_domain_lattice_regularity hP _ p.T hL _ hp1 hq1 hf hj Y _ _ hY.1 _ hl1 hl3).1
  have htw := ((_root_.GlobalTheory.T.twisted_flat_bundle_ranks hP _ p.T hL _ hp1 hq1 hf hj Y _ _ hY.1 _ hfl).2 _ (p.κ i).n ((Fm.D x ι).R.k - 1) · hdom hev)
  rw [htw _ g1, htw _ g2]
  have hk : 0 < PP * kap p i := by linarith
  have hz : zed p i PP u1 ≤ min (1 / 2) ((Fm.L x ι).sc.b / (PP * kap p i)) := le_min hz2 ((le_div_iff₀ hk).2 hz1)
  have hz0 : 0 ≤ zed p i PP u1 := by
    unfold zed
    positivity
  first
    | have hJ := _root_.GlobalTheory.T.jet_rank_complex_le hX hP hSi hTo hG hQ hN
    | have hJ := _root_.GlobalTheory.T.jet_rank_complex_le hP hSi hTo hG hQ hN
  letI := Fintype.ofFinite (Comp Y.d.Xo₂ Y.d.c₂)
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.mul_sum]
  refine Finset.sum_le_sum fun Z _ => ?_
  have d0 : 0 < Y.dg u1 Z := hδ.trans_le (hdg Z).1
  have d1 : (1 - CompHt.rhoB (dat p i) u1) * CompHt.topDeg Y.U Z u1 ≤ Y.dg u1 Z :=
    (CompHt.delPrime_eq Y.U Z (CompHt.vdm_pos fun τ => (hA τ).1).ne').ge.trans (hboth Z Z).1
  have d2 := hJ _ p.T hL _ hp1 hq1 hf hj Y _ _ hY.1 Z u1 _ _ a hgap hl1 hl2 (by
    have h1 : 0 < 1 - CompHt.rhoB (dat p i) u1 := by linarith
    refine lt_of_mul_lt_mul_left ?_ h1.le
    have e1 := mul_le_mul_of_nonneg_left d1 (Nat.cast_nonneg (lenT p i PP + CompHt.dimFlag (dat p i) + 4))
    have e2 := mul_lt_mul_of_pos_right ha1 d0
    linarith)
  calc _ ≤ _ := d2
    _ ≤ (1 + zed p i PP u1) * binT p i PP * Y.dg u1 Z := mul_le_mul_of_nonneg_right ha2 d0.le
    _ ≤ (1 + zed p i PP u1) * Y.rkC (uM p i) Z := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (hsh Z).1 (by linarith)
    _ ≤ _ := by
      rw [← em]
      exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
end GlobalTheory.CovTop.HodgeSteps
end
end
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_growth_bound_small_scale_alt_alt : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoverDegree → _root_.GlobalTheory.CovTop.ShareCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ s : ℕ, 1 ≤ s → s ≤ 2 → (Y.rk (Gs p i (s * cZero (Fm.D x ι) ((i : ℕ) + 1))) : ℝ) ≤ (1 + min (1 / 2) ((Fm.L x ι).sc.b / (PP * kap p i))) * Y.rk (Gs p i (-(cZero (Fm.D x ι) ((i : ℕ) + 1)))) := by
  first | exact @_root_.GlobalTheory.CovTop.HodgeSteps.rk_le_alt_alt | exact _root_.GlobalTheory.CovTop.HodgeSteps.rk_le_alt_alt | (intros; apply _root_.GlobalTheory.CovTop.HodgeSteps.rk_le_alt_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ShareStatementOfKnownTheorems
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftsAndAlt
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
namespace GlobalTheory.CovTop.ShareRowsNef
section Weights
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
end Weights
theorem lifts_and_alt {Q Q' : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x) (p : Pt Fm x hx ι)
    (_i : Fin (Fm.D x ι).R.m) (_PP _C : ℝ), Prop} (h : _root_.GlobalTheory.CovTop.LiftsCondition Q) (h' : _root_.GlobalTheory.CovTop.LiftsCondition Q') :
    _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x hx ι p i PP _ => (∃ C, Q Fm x hx ι p i PP C) ∧ ∃ C, Q' Fm x hx ι p i PP C :=
  Closed.imp (Closed.and h h') fun _ _ _ ⟨⟨C, _, a⟩, C', _, b⟩ => ⟨0, le_rfl, (a.and b).imp fun _ h x hx hle ι p hp i =>
    ⟨⟨C, (h x hx hle ι p hp).1 i⟩, C', (h x hx hle ι p hp).2 i⟩⟩
end GlobalTheory.CovTop.ShareRowsNef
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
namespace GlobalTheory.CovTop.ShareRowsNef
section Weights
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
end Weights
theorem share_alt_alt : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS →
    GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SemiAbelianLieSeminegative →
    _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoverDegree → _root_.GlobalTheory.CovTop.ShareCondition := by
  intro hX hP hSI hKS hG hQ hSL hDG hS hF hD
  have h1 := hS
  have h2 := hF
  have h3 := hD
  have h4 := _root_.GlobalTheory.T.size_bounds_for_family_alt hS
  have h5 := _root_.GlobalTheory.T.valuation_multiplicity_run_estimate_alt hP hG hQ hSI hKS hSL hDG hS hF
  have h6 := _root_.GlobalTheory.T.birOn_weightPair_both_components_alt hX hG hQ hSI hP hS
  unfold _root_.GlobalTheory.CovTop.SizeCondition at h1
  unfold _root_.GlobalTheory.CovTop.FlatDegreeCondition _root_.GlobalTheory.CovTop.CoversCondition at h2
  unfold _root_.GlobalTheory.CovTop.CoverDegree _root_.GlobalTheory.CovTop.CoversCondition at h3
  unfold _root_.GlobalTheory.CovTop.CoversCondition at h4 h5 h6
  have all := _root_.GlobalTheory.CovTop.ShareRowsNef.lifts_and_alt (_root_.GlobalTheory.CovTop.ShareRowsNef.lifts_and_alt (_root_.GlobalTheory.CovTop.ShareRowsNef.lifts_and_alt (_root_.GlobalTheory.CovTop.ShareRowsNef.lifts_and_alt h1 h2) (_root_.GlobalTheory.CovTop.ShareRowsNef.lifts_and_alt h3 _root_.GlobalTheory.HSApp.wtBig_run_alt))
    (_root_.GlobalTheory.CovTop.ShareRowsNef.lifts_and_alt (_root_.GlobalTheory.T.weight_parameter_strict_antitone_alt hS) h4)) (_root_.GlobalTheory.CovTop.ShareRowsNef.lifts_and_alt h5 h6)
  clear h1 h2 h3 h4 h5 h6
  refine Closed.imp all fun Fm _ _ ⟨C, hC, x0, h⟩ => ⟨C, hC, x0, fun x hx hle ι p hp i hi Y hY u1 hu Z => ?_⟩
  obtain ⟨⟨_, ⟨_, ⟨_, ⟨_, hs⟩, _, hfl⟩, _, ⟨_, hdg⟩, _, hB⟩, _, ⟨_, hq⟩, _, hz⟩, _, ⟨_, hv⟩, _, hbi⟩ := h x hx hle ι p hp i
  obtain ⟨hp1, hq1, hf, hqu, hsa, ⟨w, -, hw⟩, hdom⟩ := hq hi
  obtain ⟨hT, hj, -⟩ := hz hi Y hY
  obtain ⟨-, h0, -, hz1⟩ := (hs.2.2.2.2.2.2 hi).2 u1 hu
  obtain ⟨δ, hδ, hδ2⟩ := hdg hi Y hY u1 hu
  obtain rfl := hqu u1 hu
  have htw := (_root_.GlobalTheory.T.twisted_flat_bundle_ranks hP _ p.T hT _ hp1 hq1 hf hj Y _ _ hY.1 _ (hfl hi Y hY)).1
  refine ⟨?_, ?_⟩
  · rw [hw, htw]
    exact _root_.GlobalTheory.CovTop.ShareRowsNef.nef_share_lower_bound hP hSI hKS hG hQ hSL hT hp1 hq1 hf hj Y hY.1 _ (hB hi) Z (hbi hi Y hY Z).1
  · have hD2 : (2 : ℝ) ≤ CompHt.dimFlag (dat p i) := by
      rw [GlobalTheory.CompHS.dimFlag_eq]; exact_mod_cast two_le_dimFlag hp1 hq1 hf
    refine _root_.GlobalTheory.CovTop.ShareRowsNef.nef_share_upper_bound hX hP hSI hKS hG hQ hSL hT hp1 hq1 hf hj Y hY.1 _ (hB hi) hsa (fun Z => (hbi hi Y hY Z).1) (hv hi Y hY) h0 ?_ (uM p i) (fun τ => ?_) (fun τ => ?_) Z
      (hδ.trans_le (hδ2 Z).1)
    · unfold zed at hz1
      have : 0 ≤ (CompHt.dimFlag (dat p i) : ℝ) ^ 2 / lenT p i (Fm.parT x hx ι).PP := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hD2 h0]
    · simpa using (hdom 0 (by norm_num) τ).1
    · simpa using (hdom 0 (by norm_num) τ).2
end GlobalTheory.CovTop.ShareRowsNef
end
end
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.share_of_deep_good_size_flat_deg_cover_degree : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoverDegree → _root_.GlobalTheory.CovTop.ShareCondition := by
  first | exact @_root_.GlobalTheory.CovTop.ShareRowsNef.share_alt_alt | exact _root_.GlobalTheory.CovTop.ShareRowsNef.share_alt_alt | (intros; apply _root_.GlobalTheory.CovTop.ShareRowsNef.share_alt_alt <;> assumption)
end
end
end
