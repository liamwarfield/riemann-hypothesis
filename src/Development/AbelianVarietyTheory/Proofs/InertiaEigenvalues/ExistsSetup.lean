module

public import Formalism.LocalToGlobal.PairingIndexBounds.LatticeNormPowers.CloseUnitNorms.TestVectorMemSchwartzBruhat
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelChoiceMuUnramifiedOutsideTypePlaces
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ArtinTwistingCharacterDeltaGood
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsotypicRealNonzero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftBaseDataIsGoodTwist
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameResidueCharTrivialSplitPlaceOffUnramified
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameResidueCharTrivialSplitPlaceOffUnramified
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjTwist

theorem isResAt_one_of_unram : ∀ (D : D7) (M : Type) [CommGroup M] (χ : (AE D)ˣ →* M) (Q P : Finset (Pl D.host.E)), UnramOutside χ Q → SplitSet P → Q ⊆ P → ∀ PP ∈ P, PP ∉ Q → IsResAt χ PP 1 := by
  intro D M _ χ Q P hχ hP hQ PP hPP hn x hoff hi u hu
  have he : Formalism.L2.NTheta.IsIdemAt (idemAt PP) PP := hP.isIdemAt hPP
  have hinf : infPart D (idemAt PP) = 0 :=
    GlobalTheory.PlaceVec.idemSum_infPart (P := {PP}) ⟨⟨idemAt, by simpa using he, by simp⟩, he.1.2.1⟩
  obtain ⟨hei, -⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D _ PP he
  have hx : (x : AE D) = (1 - idemAt PP) + idemAt PP * (x : AE D) := by
    linear_combination hoff
  have hxI : (⟨_, hi⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = (1 - ⟨_, hei⟩) + ⟨_, hei⟩ * ⟨_, hi⟩ := by
    apply Subtype.ext
    have := congrArg (toEAf D) hx
    simp only [map_add (f := _), map_sub, map_mul, map_one] at this
    exact this.trans rfl

  have hres : ∀ PP' : Pl D.host.E, resS D.host.F PP' ⟨_, hi⟩ ≠ 0 := by
    intro PP'
    by_cases hq : PP' = PP
    · subst hq
      rw [hu]
      exact u.ne_zero
    · have := PP'.isPrime
      have hr0 : resS D.host.F PP' ⟨_, hei⟩ = 0 := by
        have hnle : ¬ PP'.asIdeal ≤ PP.asIdeal := fun hle =>
          hq (HeightOneSpectrum.ext (PP'.isMaximal.eq_of_le PP.isPrime.ne_top hle))
        obtain ⟨a, ha', ha⟩ := SetLike.not_le_iff_exists.1 hnle
        have ha0 : a ≠ 0 := fun h0 => ha (h0 ▸ zero_mem _)
        have ha0' : (a : D.host.E) ≠ 0 := fun h0 => ha0 (RingOfIntegers.coe_eq_zero_iff.1 h0)
        have hint : finPart D (idemAt PP * incA D ((a : D.host.E)⁻¹)) ∈ intAE D := by
          by_contra k
          exact ha ((he.2 a ha0).2 k)
        have hint' := GlobalTheory.IdemRes.toEAf_mem_of_finPart hint
        have hb : toEAf D (incA D (a : D.host.E)) =
            ((Formalism.L2.DIV.oToS D.host.F D.host.E a : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) := rfl
        have hm : (⟨_, hei⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ⟨_, hint'⟩ * Formalism.L2.DIV.oToS D.host.F D.host.E a := by
          apply Subtype.ext
          change toEAf D (idemAt PP) = toEAf D (idemAt PP * incA D ((a : D.host.E)⁻¹)) * _
          rw [← hb, ← RingHom.map_mul, mul_assoc, ← RingHom.map_mul, inv_mul_cancel₀ ha0', RingHom.map_one, mul_one]
        rw [hm, map_mul, resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 ha', mul_zero]
      rw [hxI, map_add (f := _), map_sub, map_mul, hr0, map_one, zero_mul, sub_zero, add_zero]
      exact one_ne_zero
  obtain ⟨w, hw⟩ := Formalism.L2.DIV.isUnit_of_resS_ne_zero D.sp.cm ⟨_, hi⟩ hres
  have hinv : toEAf D ((x⁻¹ : (AE D)ˣ) : AE D) = (((w⁻¹ : (Formalism.L2.Herm.intAf D.host.F D.host.E)ˣ) :
      Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) := by
    have h1 : toEAf D ((x⁻¹ : (AE D)ˣ) : AE D) * toEAf D (x : AE D) = 1 := by
      rw [← RingHom.map_mul, Units.inv_mul, RingHom.map_one]
    have h2 : toEAf D (x : AE D) * (((w⁻¹ : (Formalism.L2.Herm.intAf D.host.F D.host.E)ˣ) :
        Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) = 1 := by
      have := congrArg Subtype.val (Units.mul_inv w)
      rw [hw] at this
      exact this
    calc _ = toEAf D ((x⁻¹ : (AE D)ˣ) : AE D) * (toEAf D (x : AE D) * (((w⁻¹ : (Formalism.L2.Herm.intAf D.host.F D.host.E)ˣ) :
          Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D)) := by rw [h2, mul_one]
      _ = _ := by rw [← mul_assoc, h1, one_mul]
  have hl : IsLocUnit PP u x := by
    refine ⟨hoff, ?_, GlobalTheory.PlaceDatum.finPart_mem_of_toEAf hi, GlobalTheory.PlaceDatum.finPart_mem_of_toEAf ?_, hi, hu⟩
    · have := congrArg (infPart D) hx
      rw [map_add (f := _), map_sub, map_mul, map_one, hinf, zero_mul, sub_zero, add_zero] at this
      exact this
    · rw [hinv]
      exact Subtype.property _
  rw [hl.eq_one hχ hP hQ hPP hn, MonoidHom.one_apply]

end GlobalTheory.ConjTwist
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameResidueCharTrivialSplitPlaceOffUnramifiedStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_residue_char_trivial_split_place_off_unramified : ∀ (D : D7) (M : Type) [CommGroup M] (χ : (AE D)ˣ →* M) (Q P : Finset (Pl D.host.E)), UnramOutside χ Q → SplitSet P → Q ⊆ P → ∀ PP ∈ P, PP ∉ Q → IsResAt χ PP 1 := by
  first | exact @GlobalTheory.ConjTwist.isResAt_one_of_unram | exact GlobalTheory.ConjTwist.isResAt_one_of_unram | (intros; apply GlobalTheory.ConjTwist.isResAt_one_of_unram <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftBaseDataIsGoodTwist
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeriesTie.BaseGood

theorem base_good : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks) (F3 : Face3 D A3), Rl.Char3 F3 → ∀ (j : Fin D.R.m) (F : Frame (Vc D j) (Wc D j)) (hF : F.Good) (de : Twist D Circle), de.Good → PlacesOK Rl.Pg de.Q → ∃ (w : GlobalTheory.ExportSeries.Weight D (Vc D j).rank) (mu : ResChars D Circle), (∀ τ, w.ap τ = aPl D j ((Wc D j).sig (tauE D τ)).1 τ) ∧ (∀ τ, w.am τ = aMi D j ((Wc D j).sig (tauE D τ)).1 ((Wc D j).sig (tauE D τ)).2 τ) ∧ ∀ P : LevelP Rl.Pg (Wc D j).rank ℂ, (⟨hF.rank_le, F, ⟨Rl.Pg, P, mu⟩, de, w, Rl.mu0 ((j : ℕ) + 1), Rl.eta⟩ : Base (Vc D j) (Wc D j)).Good := by
  intro D Γ _ _ Pl0 I0 T A3 Ks _ _ _ Rl F3 hC j F hF de hde hpl
  have hL := hC.lev
  have hS : SplitSet Rl.Pg := by
    obtain ⟨P, h1, -, hP⟩ := hpl.split
    exact hP.mono h1
  have hr : Odd D.R.r := Formalism.L2.NTheta.odd_r D.R
  have rV : (Vc D j).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) j.2
  have rW : (Wc D j).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) j.2
  obtain ⟨Pa, hPa1, hPa2, hPa⟩ := hpl.split
  refine ⟨GlobalTheory.ConjTwist.liftWeight D j, fun PP => GlobalTheory.ConjTwist.toCircle (Rl.chi ((j : ℕ) + 1) PP)⁻¹,
    fun _ => rfl, fun _ => rfl, fun P => ?_⟩
  exact
    { even := rV ▸ hr.add_odd D.R.t_odd
      odd := rW ▸ hr
      frame := hF
      de := hde
      places := hpl
      wt := GlobalTheory.ConjTwist.liftWeight_good D j
      sig := fun _ => rfl
      sigOK := D.sp.W_sig _
      eta := GlobalTheory.EtaTildeOfComponents.isEtaTilde_of_chrEq D Rl.C Rl.eta hL.eta (GlobalTheory.HeckeCharacterRestriction.resEta_eta hL)
      hecke := (hL.mu0 j).1
      real := GlobalTheory.GridWeil.triv_base (hL.mu0 j) (Rl.C.isMu0 j).triv
      unram := GlobalTheory.T.levelChoice_mu_unramified_outside_type_places D _ _ _ hL hS j
      tame := fun PP hPP x hx hi u hu => by
        have e1 := GlobalTheory.ConjTwist.eq_res_of_chrEq (hL.mu0 j) (hS.isIdemAt hPP) ((Rl.C.isMu0 j).tame PP) (hL.chi j PP hPP) x hx hi u hu
        have e2 := GlobalTheory.T.tame_residue_char_trivial_split_place_off_unramified D Circle de.chi de.Q Pa hde.unram hPa hPa2 PP (hPa1 hPP)
          (Finset.disjoint_left.1 hpl.disj hPP) x hx hi u hu
        show Rl.mu0 ((j : ℕ) + 1) x * de.chi x = GlobalTheory.ConjTwist.toCircle (Rl.chi ((j : ℕ) + 1) PP)⁻¹ u
        rw [e2, MonoidHom.one_apply, mul_one]
        exact Circle.ext e1
      inf := fun τ => by
        have e : ((GlobalTheory.ConjTwist.liftWeight D j).c τ : ℚ) - (((GlobalTheory.ConjTwist.liftWeight D j).p τ : ℚ) -
            (GlobalTheory.ConjTwist.liftWeight D j).q τ) / 2 + 1 / 2 = -(D.hc τ).e j := by
          have h := GlobalTheory.ConjTwist.liftC_cast D j τ
          simp only [GlobalTheory.ConjTwist.liftWeight]
          linarith
        rw [e]
        exact GlobalTheory.ConjRefChar.reference_lift_character_exponent_neg_base hL j τ }

end GlobalTheory.SeriesTie.BaseGood

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftBaseDataIsGoodTwistStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftBaseData_isGood_twist : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks) (F3 : Face3 D A3), Rl.Char3 F3 → ∀ (j : Fin D.R.m) (F : Frame (Vc D j) (Wc D j)) (hF : F.Good) (de : Twist D Circle), de.Good → PlacesOK Rl.Pg de.Q → ∃ (w : GlobalTheory.ExportSeries.Weight D (Vc D j).rank) (mu : ResChars D Circle), (∀ τ, w.ap τ = aPl D j ((Wc D j).sig (tauE D τ)).1 τ) ∧ (∀ τ, w.am τ = aMi D j ((Wc D j).sig (tauE D τ)).1 ((Wc D j).sig (tauE D τ)).2 τ) ∧ ∀ P : LevelP Rl.Pg (Wc D j).rank ℂ, (⟨hF.rank_le, F, ⟨Rl.Pg, P, mu⟩, de, w, Rl.mu0 ((j : ℕ) + 1), Rl.eta⟩ : Base (Vc D j) (Wc D j)).Good := by
  first | exact @GlobalTheory.SeriesTie.BaseGood.base_good | exact GlobalTheory.SeriesTie.BaseGood.base_good | (intros; apply GlobalTheory.SeriesTie.BaseGood.base_good <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistingCharacterLadicGaloisCharacterEqHecke
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistingCharacterLadicGaloisCharacterEqHecke
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeriesTie

theorem charOf_psiAt_chrEq : ∀ (D : D7) (a : Recip D D.nd.Om) (i : D.ntw.Tw) (κ : FractionRing (D.ntw.O0 i) →+* Qbar (D.ntw.l i)) (ι : Qbar (D.ntw.l i) ≃+* ℂ) (χ : Formalism.L2.Host.HChar D.host.E) (r : G D.host.E D.nd.Om →* (D.ntw.O0 i)ˣ) (b : Bool), a.Good → IsOpen (r.ker : Set (G D.host.E D.nd.Om)) → GlobalTheory.GalChar.IsGal a.art κ ι χ (fun _ => 0) (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b r) → ∀ (f : D.ntw.O0 i →+* ℂ), (∀ y, IsIntegral ℤ y → f y = ι (κ (algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) y))) → ∀ (ch : Set (Pl D.host.E)) (Q : Finset (Pl D.host.E)), ChrEq (twistOf a f ch Q (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b r)).chi χ := by
  intro D a i κ ι χ r b ha hr hg f hf ch Q
  set ψ := Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b r with hψdef
  have hker : ψ.ker = r.ker := by
    cases b
    · ext σ
      simp [hψdef, Formalism.MainNotions.BlochKatoReduction.Gen.psiAt]
    · simp [hψdef, Formalism.MainNotions.BlochKatoReduction.Gen.psiAt]
  have hop : IsOpen (ψ.ker : Set (G D.host.E D.nd.Om)) := hker ▸ hr
  have hfi : ψ.ker.FiniteIndex := by
    let H : OpenNormalSubgroup (G D.host.E D.nd.Om) := { toSubgroup := ψ.ker, isOpen' := hop, isNormal' := inferInstance }
    exact inferInstanceAs (OpenNormalSubgroup.toFiniteIndexNormalSubgroup H).toSubgroup.FiniteIndex
  have hn : ψ.ker.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have hpow : ∀ σ, ψ σ ^ ψ.ker.index = 1 := fun σ => by
    rw [← map_pow]
    exact ψ.mem_ker.1 (Subgroup.pow_index_mem _ σ)
  have key : ∀ (x : (AE D)ˣ) (σ : G D.host.E D.nd.Om), a.sym x = toAb D.host.E D.nd.Om σ →
      ((charOf a f ψ x : Circle) : ℂ) = ((χ.1 (Units.map a.κ.toMonoidHom x) : ℂˣ) : ℂ) := by
    intro x σ hx
    rw [charOf_eq a f hop hx hn (hpow σ)]
    have hint : IsIntegral ℤ ((ψ σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) :=
      IsIntegral.of_pow (Nat.pos_of_ne_zero hn) (by
        rw [← Units.val_pow_eq_pow_val, hpow σ, Units.val_one]
        exact isIntegral_one)
    rw [hf _ hint]
    have h1 := hg.2.2 (Units.map a.κ.toMonoidHom x) σ hx
    simp [GlobalTheory.GalChar.inQ, GlobalTheory.GalChar.toQ, GlobalTheory.HeckeGal.infPow, GlobalTheory.HeckeGal.lPow, GlobalTheory.HeckeGal.locPow] at h1
    rw [h1]
    simp

  have hsymc : Continuous a.sym :=
    ha.artin.quot.continuous.comp (Continuous.units_map _ ha.cont)
  have hdesc : IsOpen (((descend ψ : Gab D.host.E D.nd.Om →* (D.ntw.O0 i)ˣ).ker : Set (Gab D.host.E D.nd.Om))) := by
    have hpre : (toAb D.host.E D.nd.Om) ⁻¹' ((descend ψ).ker : Set (Gab D.host.E D.nd.Om)) = (ψ.ker : Set _) := by
      ext σ
      simp [descend_toAb hop]
    have hs : Function.Surjective (toAb D.host.E D.nd.Om) := QuotientGroup.mk'_surjective _
    rw [← Set.image_preimage_eq ((descend ψ).ker : Set (Gab D.host.E D.nd.Om)) hs, hpre]
    exact QuotientGroup.isOpenMap_coe _ hop
  have hpullo : IsOpen (((a.pull ψ).ker : Set (AE D)ˣ)) := by
    have : ((a.pull ψ).ker : Set (AE D)ˣ) = a.sym ⁻¹' ((descend ψ).ker : Set _) := by
      ext x
      simp [Recip.pull]
    rw [this]
    exact hdesc.preimage hsymc
  refine ⟨⟨?_, fun k => ?_⟩, fun P e he k x hx => ?_⟩
  · refine continuous_of_continuousAt_one (charOf a f ψ) ?_
    refine ContinuousAt.congr (continuousAt_const (y := (1 : Circle))) (Filter.eventuallyEq_of_mem (hpullo.mem_nhds (map_one _)) fun x hx => ?_)
    change (1 : Circle) = charOf a f ψ x
    rw [charOf, MonoidHom.comp_apply, MonoidHom.comp_apply, (a.pull ψ).mem_ker.1 hx, map_one, map_one]
  · have hs : a.sym (Units.map (incA D).toMonoidHom k) = 1 := by
      change a.art (Units.map a.κ.toMonoidHom (Units.map (incA D).toMonoidHom k)) = 1
      rw [← MonoidHom.mem_ker, ha.artin.ker]
      apply Subgroup.le_topologicalClosure
      apply Subgroup.mem_sup_left
      exact ⟨k, Units.ext (ha.rat k).symm⟩
    change unitPart (Units.map f.toMonoidHom (descend ψ (a.sym (Units.map (incA D).toMonoidHom k)))) = 1
    rw [hs, map_one, map_one, map_one]
  · obtain ⟨σ, hσ⟩ := a.exists_sym x
    have hy : Units.map a.κ.toMonoidHom x =
        Neutral.B1.localIdele D.host.E P (Formalism.L2.Host.atFin P k) :=
      Units.ext ((congrArg a.κ hx).trans (ha.loc P e he k))
    change ((charOf a f ψ x : Circle) : ℂ) = _
    rw [key x σ hσ, hy]
    rfl
end GlobalTheory.SeriesTie

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistingCharacterLadicGaloisCharacterEqHeckeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistingCharacter_ladicGaloisCharacter_eq_hecke : ∀ (D : D7) (a : Recip D D.nd.Om) (i : D.ntw.Tw) (κ : FractionRing (D.ntw.O0 i) →+* Qbar (D.ntw.l i)) (ι : Qbar (D.ntw.l i) ≃+* ℂ) (χ : Formalism.L2.Host.HChar D.host.E) (r : G D.host.E D.nd.Om →* (D.ntw.O0 i)ˣ) (b : Bool), a.Good → IsOpen (r.ker : Set (G D.host.E D.nd.Om)) → GlobalTheory.GalChar.IsGal a.art κ ι χ (fun _ => 0) (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b r) → ∀ (f : D.ntw.O0 i →+* ℂ), (∀ y, IsIntegral ℤ y → f y = ι (κ (algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) y))) → ∀ (ch : Set (Pl D.host.E)) (Q : Finset (Pl D.host.E)), ChrEq (twistOf a f ch Q (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b r)).chi χ := by
  first | exact @GlobalTheory.SeriesTie.charOf_psiAt_chrEq | exact GlobalTheory.SeriesTie.charOf_psiAt_chrEq | (intros; apply GlobalTheory.SeriesTie.charOf_psiAt_chrEq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGoodFrameRealisation
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGoodFrameRealisation
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameOfReal

theorem exists_frame_real : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks) (F3 : Face3 D A3), Rl.Char3 F3 → ∀ j : Fin D.R.m, ∃ F : Frame (Vc D j) (Wc D j), F.Good ∧ IsStdChar D F.ψ (-1) ∧ F.ψ = Rl.ψ ∧ F.θ = Rl.θ ∧ F.sT = cart (Rl.MW j (sg0 D A3.A)) ∧ (∀ τ, (F.BS τ).val = Rl.BV j τ) ∧ F.BT = onb (Rl.MW j (sg0 D A3.A)) ∧ F.ΛS = Rl.ΛV j ∧ F.ΛT = Rl.ΛW j ∧ F.βS = Rl.βV j ∧ F.βT = Rl.βW j ∧ F.f₀ = Rl.vacP j ∧ Lev.IsBaseFrame (Vc D j) F.βS F.ΛS 1 ∧ Lev.IsBaseFrame (Wc D j) F.βT F.ΛT 1 := by
  intro D Γ _ _ Pl0 I0 T A3 Ks _ _ _ Rl F3 hC j
  have hBV := hC.models.BV j
  have hu : ∀ τ, IsUnit (Rl.BV j τ) := fun τ => by
    obtain ⟨ε, hε, h2, -⟩ := hBV τ
    have hd : (Matrix.diagonal fun a => (ε a : ℂ)) * Matrix.diagonal (fun a => (ε a : ℂ)) = 1 := by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext a
      rcases hε a with h | h <;> simp [h.1]
    refine IsUnit.of_mul_eq_one_right (Matrix.diagonal (fun a => (ε a : ℂ)) * (Matrix.conjTranspose (Rl.BV j τ) * gramAt D (Vc D j) τ)) ?_
    rw [Matrix.mul_assoc, h2, hd]
  have sdV := hC.lev.βV j
  have sdW := hC.lev.βW j
  have bV : Lev.IsBaseFrame (Vc D j) (Rl.βV j) (Rl.ΛV j) 1 := by
    obtain ⟨c, hc⟩ := sdV
    rwa [one_pow] at hc
  have bW : Lev.IsBaseFrame (Wc D j) (Rl.βW j) (Rl.ΛW j) 1 := by
    obtain ⟨c, hc⟩ := sdW
    rwa [one_pow] at hc
  have hv := (hC.thP.vP j A3.A.μ0).1
  have hstd := (hC.thP.ωP j A3.A.μ0).std
  refine ⟨⟨Rl.ψ, Rl.θ, cart (Rl.MW j (sg0 D A3.A)), fun τ => (hu τ).unit, onb (Rl.MW j (sg0 D A3.A)), Rl.ΛV j, Rl.ΛW j,
    Rl.βV j, Rl.βW j, Rl.vacP j⟩, ?_, hstd, rfl, rfl, rfl, fun _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, bV, bW⟩
  exact
    { rank_le := (D.sp.W_rank _ (Nat.le_add_left _ _) j.2).le.trans (r_le_V j)
      onbS := hBV
      cartT := fun τ => GlobalTheory.AdTh.VecFock.isCartanInv_cart _ τ
      onbT := fun τ => GlobalTheory.AdTh.VecFock.isONBasis_onb _ τ _ (hC.models.order j τ)
      sdS := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ sdV
      sdT := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ sdW
      frS := bV.1
      frT := bW.1
      vac := hv }

end GlobalTheory.FrameOfReal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGoodFrameRealisationStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_good_frame_realisation : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks) (F3 : Face3 D A3), Rl.Char3 F3 → ∀ j : Fin D.R.m, ∃ F : Frame (Vc D j) (Wc D j), F.Good ∧ IsStdChar D F.ψ (-1) ∧ F.ψ = Rl.ψ ∧ F.θ = Rl.θ ∧ F.sT = cart (Rl.MW j (sg0 D A3.A)) ∧ (∀ τ, (F.BS τ).val = Rl.BV j τ) ∧ F.BT = onb (Rl.MW j (sg0 D A3.A)) ∧ F.ΛS = Rl.ΛV j ∧ F.ΛT = Rl.ΛW j ∧ F.βS = Rl.βV j ∧ F.βT = Rl.βW j ∧ F.f₀ = Rl.vacP j ∧ Lev.IsBaseFrame (Vc D j) F.βS F.ΛS 1 ∧ Lev.IsBaseFrame (Wc D j) F.βT F.ΛT 1 := by
  first | exact @GlobalTheory.FrameOfReal.exists_frame_real | exact GlobalTheory.FrameOfReal.exists_frame_real | (intros; apply GlobalTheory.FrameOfReal.exists_frame_real <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLadicCoefficientFieldEmbeddingsComplex
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLadicCoefficientFieldEmbeddingsComplex
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.EmbExt

open Cardinal

theorem exists_extend_of_countable {A K : Type} [Field A] [Field K] [Algebra A K] [Countable A]
    (hK : #K ≤ 𝔠) (φ : A →+* ℂ) : ∃ ψ : K →+* ℂ, ∀ a, ψ (algebraMap A K a) = φ a := by
  letI : Algebra A ℂ := φ.toAlgebra
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis A K
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis A ℂ
  have hA : #A ≤ ℵ₀ := Cardinal.mk_le_aleph0
  have hC : ℵ₀ < #ℂ := by rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum
  have ht' : #ℂ = #t := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ ht hA hC
  have hst : #s ≤ #t := by
    rw [← ht', Cardinal.mk_complex]
    exact (Cardinal.mk_le_mk_of_subset (Set.subset_univ _)).trans (by simpa using hK)
  obtain ⟨f⟩ := hst
  have hw : AlgebraicIndependent A (fun x : s => ((f x : t) : ℂ)) :=
    ht.1.comp (fun x => f x) f.injective
  let S := Algebra.adjoin A (Set.range ((↑) : s → K))
  let g : S →ₐ[A] ℂ := (MvPolynomial.aeval (fun x : s => ((f x : t) : ℂ))).comp hs.1.aevalEquiv.symm.toAlgHom
  have hg : Function.Injective g := (show Function.Injective (MvPolynomial.aeval (fun x : s => ((f x : t) : ℂ))) from hw).comp
    hs.1.aevalEquiv.symm.injective
  letI : Algebra S ℂ := g.toRingHom.toAlgebra
  haveI : Module.IsTorsionFree S ℂ := Module.isTorsionFree_iff_algebraMap_injective.2 hg
  haveI : Module.IsTorsionFree S K := Module.isTorsionFree_iff_algebraMap_injective.2 Subtype.val_injective
  haveI : Algebra.IsAlgebraic S K := hs.isAlgebraic
  let ψ : K →ₐ[S] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨ψ.toRingHom, fun a => ?_⟩
  have h1 : algebraMap A K a = algebraMap S K (algebraMap A S a) := rfl
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h1, ψ.commutes]
  exact g.commutes a

end GlobalTheory.EmbExt

namespace GlobalTheory.EmbExt

theorem isAlgebraic_rat_of_isIntegral_int {R F : Type} [CommRing R] [Field F] [CharZero F] (g : R →+* F)
    {y : R} (hy : IsIntegral ℤ y) : IsAlgebraic ℚ (g y) := by
  obtain ⟨p, hp, hev⟩ := hy
  refine ⟨p.map (Int.castRingHom ℚ), (hp.map _).ne_zero, ?_⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_map]
  have h : (algebraMap ℚ F).comp (Int.castRingHom ℚ) = g.comp (algebraMap ℤ R) := RingHom.ext_int _ _
  rw [h, ← Polynomial.hom_eval₂, hev, map_zero]

end GlobalTheory.EmbExt

namespace GlobalTheory.EmbExt

theorem exists_side_embeddings : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (f0 : ∀ i, Bool → (FractionRing (X.O0 i) →+* ℂ)), (∀ i b x, f0 i b ((if b then X.emb0 i else X.emb0b i) x) = embLL0 D x) → (∀ i k, Cardinal.mk (FractionRing (X.Ok i k)) ≤ Cardinal.continuum) → ∃ (e : ∀ i, Bool → (FractionRing (X.O i) →+* ℂ)) (ek : ∀ i, Bool → ∀ k, FractionRing (X.Ok i k) →+* ℂ), (∀ i b x, e i b (sideEmb X i b x) = embLL0 D x) ∧ (∀ i b k (x : X.O i), ek i b k (algebraMap (X.Ok i k) (FractionRing (X.Ok i k)) (algebraMap (X.O i) (X.Ok i k) x)) = e i b (algebraMap (X.O i) (FractionRing (X.O i)) x)) ∧ (∀ i b (y : X.O0 i), IsIntegral ℤ y → e i b (algebraMap (X.O i) (FractionRing (X.O i)) (algebraMap (X.O0 i) (X.O i) y)) = f0 i b (algebraMap (X.O0 i) (FractionRing (X.O0 i)) y)) := by
  intro D N X f0 hf0 hcard
  have hcz : ∀ i, CharZero (FractionRing (X.O0 i)) := fun i => charZero_of_injective_ringHom (X.emb0 i).injective
  have key : ∀ i b, ∃ e : FractionRing (X.O i) →+* ℂ, letI := hcz i; ∀ z : FractionRing (X.O0 i), IsAlgebraic ℚ z →
      e (IsFractionRing.map (A := X.O0 i) (B := X.O i) (K := FractionRing (X.O0 i))
        (L := FractionRing (X.O i)) (X.O_inj i) z) = f0 i b z := by
    intro i b
    letI := hcz i
    let A := algebraicClosure ℚ (FractionRing (X.O0 i))
    haveI : Algebra.IsAlgebraic ℚ A := ⟨fun a => IntermediateField.isAlgebraic_iff.2 (mem_algebraicClosure_iff.1 a.2)⟩
    haveI : Countable A := by
      rw [← Cardinal.mk_le_aleph0_iff]
      exact (Algebra.IsAlgebraic.cardinalMk_le_max ℚ A).trans (by simp)
    let m := IsFractionRing.map (A := X.O0 i) (B := X.O i) (K := FractionRing (X.O0 i))
        (L := FractionRing (X.O i)) (X.O_inj i)
    letI : Algebra A (FractionRing (X.O i)) := (m.comp (algebraMap A (FractionRing (X.O0 i)))).toAlgebra
    have hK : Cardinal.mk (FractionRing (X.O i)) ≤ Cardinal.continuum :=
      (Cardinal.mk_le_of_injective (IsFractionRing.map (A := X.O i) (B := X.Ok i 0) (K := FractionRing (X.O i))
        (L := FractionRing (X.Ok i 0)) (X.Ok_inj i 0)).injective).trans (hcard i 0)
    obtain ⟨ψ, hψ⟩ := exists_extend_of_countable hK ((f0 i b).comp (algebraMap A (FractionRing (X.O0 i))))
    refine ⟨ψ, fun z hz => ?_⟩
    have hzA : z ∈ A := mem_algebraicClosure_iff.2 hz
    exact hψ ⟨z, hzA⟩
  choose e he using key
  have keyk : ∀ i b k, ∃ ek : FractionRing (X.Ok i k) →+* ℂ, ∀ x : X.O i,
      ek (algebraMap (X.Ok i k) (FractionRing (X.Ok i k)) (algebraMap (X.O i) (X.Ok i k) x)) =
        e i b (algebraMap (X.O i) (FractionRing (X.O i)) x) := by
    intro i b k
    letI : Algebra (X.O i) ℂ := ((e i b).comp (algebraMap (X.O i) (FractionRing (X.O i)))).toAlgebra
    haveI : Module.IsTorsionFree (X.O i) ℂ := Module.isTorsionFree_iff_algebraMap_injective.2
      ((e i b).injective.comp (IsFractionRing.injective (X.O i) (FractionRing (X.O i))))
    haveI : Module.IsTorsionFree (X.O i) (FractionRing (X.Ok i k)) := by
      refine Module.isTorsionFree_iff_algebraMap_injective.2 ?_
      rw [IsScalarTower.algebraMap_eq (X.O i) (X.Ok i k) (FractionRing (X.Ok i k))]
      exact (IsFractionRing.injective (X.Ok i k) (FractionRing (X.Ok i k))).comp (X.Ok_inj i k)
    haveI := X.Ok_fin i k
    haveI : Algebra.IsAlgebraic (X.O i) (X.Ok i k) := Algebra.IsIntegral.isAlgebraic
    haveI : Algebra.IsAlgebraic (X.O i) (FractionRing (X.Ok i k)) :=
      (IsFractionRing.isAlgebraic_iff' (X.O i) (X.Ok i k) (FractionRing (X.Ok i k))).1 inferInstance
    let ψ : FractionRing (X.Ok i k) →ₐ[X.O i] ℂ := (by
      refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
      solve_by_elim* (maxDepth := 2) only [*,
        @_root_.DivisionSemiring.to_moduleIsTorsionFree,
        @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
    refine ⟨ψ.toRingHom, fun x => ?_⟩
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ← IsScalarTower.algebraMap_apply, ψ.commutes]
    rfl
  choose ek hek using keyk
  refine ⟨e, ek, fun i b x => ?_, hek, fun i b y hy => ?_⟩
  · letI := hcz i
    have hx : IsAlgebraic ℚ x := Algebra.IsAlgebraic.isAlgebraic x
    have h2 : IsAlgebraic ℚ ((if b then X.emb0 i else X.emb0b i) x) :=
      hx.algHom ((if b then X.emb0 i else X.emb0b i).toRatAlgHom)
    rw [← hf0 i b x, ← he i b _ h2]
    rfl
  · letI := hcz i
    have h2 : IsAlgebraic ℚ (algebraMap (X.O0 i) (FractionRing (X.O0 i)) y) :=
      isAlgebraic_rat_of_isIntegral_int _ hy
    rw [← he i b _ h2]
    simp [IsFractionRing.map, IsLocalization.map_eq]

end GlobalTheory.EmbExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLadicCoefficientFieldEmbeddingsComplexStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ladicCoefficientField_embeddings_complex : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (f0 : ∀ i, Bool → (FractionRing (X.O0 i) →+* ℂ)), (∀ i b x, f0 i b ((if b then X.emb0 i else X.emb0b i) x) = embLL0 D x) → (∀ i k, Cardinal.mk (FractionRing (X.Ok i k)) ≤ Cardinal.continuum) → ∃ (e : ∀ i, Bool → (FractionRing (X.O i) →+* ℂ)) (ek : ∀ i, Bool → ∀ k, FractionRing (X.Ok i k) →+* ℂ), (∀ i b x, e i b (sideEmb X i b x) = embLL0 D x) ∧ (∀ i b k (x : X.O i), ek i b k (algebraMap (X.Ok i k) (FractionRing (X.Ok i k)) (algebraMap (X.O i) (X.Ok i k) x)) = e i b (algebraMap (X.O i) (FractionRing (X.O i)) x)) ∧ (∀ i b (y : X.O0 i), IsIntegral ℤ y → e i b (algebraMap (X.O i) (FractionRing (X.O i)) (algebraMap (X.O0 i) (X.O i) y)) = f0 i b (algebraMap (X.O0 i) (FractionRing (X.O0 i)) y)) := by
  first | exact @GlobalTheory.EmbExt.exists_side_embeddings | exact GlobalTheory.EmbExt.exists_side_embeddings | (intros; apply GlobalTheory.EmbExt.exists_side_embeddings <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeilRepGoodTwist
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeilRepGoodTwist
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.WeilTwistExists

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem isHeckeChar_mul' {χ χ' : (AE D)ˣ →* Circle} (h : IsHeckeChar D χ) (h' : IsHeckeChar D χ') :
    IsHeckeChar D (χ * χ') :=
  ⟨h.1.mul h'.1, fun x => by rw [MonoidHom.mul_apply, h.2 x, h'.2 x, mul_one]⟩

theorem isHeckeChar_inv' {χ : (AE D)ˣ →* Circle} (h : IsHeckeChar D χ) : IsHeckeChar D χ⁻¹ :=
  ⟨h.1.inv, fun x => by rw [MonoidHom.inv_apply, h.2 x, inv_one]⟩

theorem resEta_zero_of_real {χ ξ : (AE D)ˣ →* Circle} {n : ℕ} (h : ResEta D ξ n) (hr : ∀ a, χ (idF D a) = 1) :
    ResEta D χ 0 :=
  ⟨h.1, fun η _ a => by rw [hr, pow_zero]⟩

theorem exists_isWeil : ∀ (D : D7) (S T : HSp D) (B : Base S T), GlobalTheory.Published.WeilRepresentationUnitaryPair → B.Good →
    IsStdChar D B.F.ψ (-1) → ∀ t : Twist D Circle, t.Good → ∃ ω, B.IsWeil t.chi ω := by
  intro D S T B hW hB hψ t ht
  have hEta : ResEta D B.eta 1 := hB.eta.2.2.1
  have h0 : ResEta D (B.mu * t.chi) 0 := by
    refine resEta_zero_of_real hEta fun a => ?_
    rw [MonoidHom.mul_apply, Base.mu, MonoidHom.mul_apply, hB.real, ht.real, hB.de.real, one_mul, one_mul]
  have hH : IsHeckeChar D (B.mu * t.chi) :=
    isHeckeChar_mul' (isHeckeChar_mul' hB.hecke hB.de.isHeckeChar) ht.isHeckeChar
  have hS : ResEta D (B.mu * t.chi) S.rank :=
    Formalism.L2.Theta.resEta_parity h0 (by rw [Nat.even_iff.1 hB.even])
  have hT : ResEta D (B.mu * t.chi * B.eta⁻¹) T.rank := by
    have h1 := Formalism.L2.Theta.resEta_mul h0 (Formalism.L2.Theta.resEta_inv hEta)
    exact Formalism.L2.Theta.resEta_parity h1 (by rw [Nat.odd_iff.1 hB.odd])
  exact hW D B.F.ψ S T _ _ hψ hH (isHeckeChar_mul' hH (isHeckeChar_inv' hB.eta.1)) hS hT

end GlobalTheory.WeilTwistExists

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeilRepGoodTwistStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weilRep_good_twist : ∀ (D : D7) (S T : HSp D) (B : Base S T), GlobalTheory.Published.WeilRepresentationUnitaryPair → B.Good → IsStdChar D B.F.ψ (-1) → ∀ t : Twist D Circle, t.Good → ∃ ω, B.IsWeil t.chi ω := by
  first | exact @GlobalTheory.WeilTwistExists.exists_isWeil | exact GlobalTheory.WeilTwistExists.exists_isWeil | (intros; apply GlobalTheory.WeilTwistExists.exists_isWeil <;> assumption)
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

namespace GlobalTheory.SeriesTie.Complex

variable {D : D7}

def castG (Pg : Finset (Pl D.host.E)) {r r' : ℕ} (h : r' = r) : G0 Pg r ≃* G0 Pg r' :=
  MulEquiv.piCongrRight fun P => Units.mapEquiv
    (Matrix.reindexAlgEquiv (kP P.1) (kP P.1) (finCongr h.symm)).toMulEquiv

def levOf {G H : Type} [Group G] [Group H] (eG : G ≃* H) (U : Subgroup G) (χ : U →* ℂˣ) : Subgroup H × (U.map eG.toMonoidHom →* ℂˣ) :=
  (U.map eG.toMonoidHom, χ.comp (eG.subgroupMap U).symm.toMonoidHom)

theorem levOf_mem {G H : Type} [Group G] [Group H] (eG : G ≃* H) (U : Subgroup G) (χ : U →* ℂˣ) (g : G) :
    eG g ∈ (levOf eG U χ).1 ↔ g ∈ U := by
  simp [levOf, Subgroup.mem_map]

theorem levOf_chi {G H : Type} [Group G] [Group H] (eG : G ≃* H) (U : Subgroup G) (χ : U →* ℂˣ) (u : U)
    (hu : eG u ∈ (levOf eG U χ).1) : (levOf eG U χ).2 ⟨eG u, hu⟩ = χ u := by
  change χ ((eG.subgroupMap U).symm ⟨eG u, hu⟩) = χ u
  congr 1
  apply (eG.subgroupMap U).injective
  rw [MulEquiv.apply_symm_apply]
  rfl

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def eGc (Rl : RealDat3 D A3 Ks) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (j : Fin D.R.m) : G0g D.nd ≃* G0 Rl.Pg (Wc D j).rank :=
  cG.symm.trans (castG Rl.Pg (FWT.rank_Wc j))

end GlobalTheory.SeriesTie.Complex

end
