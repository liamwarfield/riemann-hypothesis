module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLatticeConditionOfSeriesComparisonUniversal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameGenAtTransport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UniversalTwistedSeriesDistributionOfCompatibilit
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupLawsOfSides
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCommutationRealExpansion

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.XiType
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodTwistDetCharEqOneOfSupportedTypePlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodTwistDetCharEqOneOfSupportedTypePlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistTypeDet


open Classical in
theorem detChar_eq_one_of_suppAt : ∀ (D : D7) (S T : HSp D) (B : Base S T), B.Good → S.SigOK → ∀ (A : Type) [CommGroup A] (t : Twist D A), t.Good → B.admitted t.Q → ∀ (u : G0 B.G.Pg T.rank) (κ : GA D T), Lev.IsLevelLift T B.F.βT B.G.levT u κ → SuppAt (idem B.G.Pg) T κ → detChar T t.chi κ = 1 := by
  intro D S T B hB _ A _ t ht hadm u κ hlift hsupp
  have hst : Lev.finE T κ ∈ St B.F.βT := Formalism.L2.DIV.parLev_St hlift.2.1
  rw [GlobalTheory.TwistDetStabAll.detChar_eq_prod_res B hB t ht hlift.1 hst]
  refine Finset.prod_eq_one fun PP hPP => ?_
  obtain ⟨P, hPg, hQ, hsplit⟩ := hadm.1.split
  have hnot : PP ∉ B.G.Pg := fun h => Finset.disjoint_left.mp hadm.1.disj h (Finset.mem_union_right _ hPP)
  rw [GlobalTheory.ExportSeries.redFn_eq_one_of_suppAt B.F.βT hsplit hPg (hQ (Finset.mem_union_right _ hPP)) hnot hst hsupp,
    map_one, map_one]

end GlobalTheory.TwistTypeDet
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodTwistDetCharEqOneOfSupportedTypePlacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodTwist_detChar_eq_one_of_supported_typePlaces : ∀ (D : D7) (S T : HSp D) (B : Base S T), B.Good → S.SigOK → ∀ (A : Type) [CommGroup A] (t : Twist D A), t.Good → B.admitted t.Q → ∀ (u : G0 B.G.Pg T.rank) (κ : GA D T), Lev.IsLevelLift T B.F.βT B.G.levT u κ → SuppAt (idem B.G.Pg) T κ → detChar T t.chi κ = 1 := by
  first | exact @GlobalTheory.TwistTypeDet.detChar_eq_one_of_suppAt | exact GlobalTheory.TwistTypeDet.detChar_eq_one_of_suppAt | (intros; apply GlobalTheory.TwistTypeDet.detChar_eq_one_of_suppAt <;> assumption)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.XiTypeProof

theorem xiType : ∀ (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (rd : Rds D.nexp ρ), (∀ i j b, Faithful (rd i j b)) →
    (∀ i j b, ActRead (rd i j b)) → ρ.LevelOf D.nexp → XiType rd := by
  intro D ρ hρ rd hF hA hL i _ j b Q M hQ s h P _ _ a x hx
  unfold Formalism.MainNotions.IntegralHeckeForms.Fm0
  rw [Submodule.mem_iInf]
  intro u
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
  have hadm : (ρ.B i j b).admitted (half (ρ.ch i) (admissibleConjugatePairPlaces D.ntw i Q M)) :=
    GlobalTheory.ChoiceAdm.adm_half_of_good_of_split_disjoint D _ D.ntw ρ hρ i j b _ (fun _ h => isSplit_of_mem_admissibleConjugatePairPlaces h) (hQ.2.2.mono_left (admissibleConjugatePairPlaces_subset i Q M))
  have hu : ρ.eG i j b u ∈ (ρ.B i j b).G.P.H := (hL.U_eq i j b u).2 u.2
  obtain ⟨κ, hlift, hsupp, hser⟩ := GlobalTheory.T.thetaSeries_type_under_supported_lifts D _ _ (ρ.B i j b) (hρ.base i j b) (D.sp.V_sig _) _ (hρ.weil_base i j b) _ hu
  have hg := GlobalTheory.UnivGood.univOf_good D _ D.ntw ρ hρ D.nexp i Q M
  have hdet : detChar (Wc D j) ((univOf D.nexp i (admissibleConjugatePairPlaces D.ntw i Q M) M ρ.rc).delQ (half (ρ.ch i) (admissibleConjugatePairPlaces D.ntw i Q M))) κ = 1 := by
    apply Multiplicative.toAdd.injective
    funext PP
    have := GlobalTheory.T.goodTwist_detChar_eq_one_of_supported_typePlaces D _ _ (ρ.B i j b) (hρ.base i j b) (D.sp.V_sig _) _ ⟨{PP.1}, _, _⟩ (hg.2 PP.1 PP.2)
      (hadm.mono (by simpa using PP.2)) _ κ hlift hsupp
    exact congrArg Multiplicative.toAdd this
  apply (hF i j b).injective
  funext g
  change rd i j b (D.nexp.actG i _ b u x) g = rd i j b (((D.nexp.psiU i b u : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) • x) g
  rw [hA i j b u κ hlift, map_smulₛₗ, Pi.smul_apply, hx]
  unfold Setup.xi
  rw [Base.xiCoef_apply, Base.xiCoef_apply, detChar_mul hg.delQ_real, hdet, mul_one]
  refine (hser _ hadm _ h P g).trans ?_
  rw [hL.psiU_eq i j b u hu, smul_eq_mul]
  rfl

end GlobalTheory.XiTypeProof
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LawsOfSerSide
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RatHeckeRealRd
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.Lev Formalism.L2.DIV Formalism.IndefR.Mult
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SeriesTie.HkRat

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {Rl : RealDat3 D A3 Ks}
  {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)

theorem evK_hkFR {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    (hL : ℕ → PlE D.host → Module.End D.what₂.LL (S.WL ((j : ℕ) + 1)))
    (hs : NX.HeckeStabR S ((j : ℕ) + 1) hL) (k : ℕ) (P : PlE D.host) (R : Finset (GA D (Wc D j))) (s : ℂ)
    (hR : ∀ x : S.WL ((j : ℕ) + 1), evW YS v₀ j (hL k P x) = s • heckeLin (Wc D j) R (evW YS v₀ j x))
    (y : NX.Fm S i ((j : ℕ) + 1) b) :
    evK YS v₀ hρ i j b (NX.hkFR S i ((j : ℕ) + 1) b hL hs k P y) = s • heckeLin (Wc D j) R (evK YS v₀ hρ i j b y) := by
  induction y using TensorProduct.induction_on with
  | zero => erw [LinearMap.map_zero, map_zero, map_zero, smul_zero]
  | add y z hy hz => erw [LinearMap.map_add, map_add, hy, hz, map_add, map_add, smul_add]
  | tmul a f0 =>
    have e1 : NX.hkFR S i ((j : ℕ) + 1) b hL hs k P (a ⊗ₜ f0) =
        a ⊗ₜ (((hL k P).restrictScalars S.Ks).restrict (p := (S.A ((j : ℕ) + 1)).WK) (q := (S.A ((j : ℕ) + 1)).WK)
          fun x hx => hs k P x hx) f0 := rfl
    erw [e1, evK_tmul, evK_tmul]
    change ρ.e i b a • evW YS v₀ j (hL k P f0.1) = _
    rw [hR, map_smul, smul_comm]

end GlobalTheory.SeriesTie.HkRat

namespace GlobalTheory.SeriesTie.HkRat

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {Rl : RealDat3 D A3 Ks}
  {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)

theorem evW_reads (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (hR : GlobalTheory.ExportPin.Reads Rl cG S YS hL)
    (j : Fin D.R.m) (k : ℕ) (P : PlE D.host) (hPs : IsSplitPl D.host P)
    (hso : Bridge.SplitOff P (Rl.Sb : Set (Pl D.host.E))) (hk : k ≤ D.R.r) (α : GA D (Wc D j)) (R : Finset (GA D (Wc D j)))
    (hα : IsHeckeAt (Wc D j) P k α) (hdc : Bridge.IsDC (levG (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv)) α R)
    (x : S.WL ((j : ℕ) + 1)) :
    evW YS v₀ j (hL ((j : ℕ) + 1) k P x) =
      ((((Rl.C.mu0 j).val P : ℂˣ) : ℂ)⁻¹ ^ k * (((Nat.card (kP P) : ℕ) : ℂ) ^ (k * (D.R.nV / 2)))⁻¹) •
        heckeLin (Wc D j) R (evW YS v₀ j x) := by
  have h := congrArg (fun F => F (v₀ j (sg0 D A3.A))) (hR j k P hPs hso hk α R hα hdc x)
  exact h

end GlobalTheory.SeriesTie.HkRat

namespace GlobalTheory.SeriesTie.HkRat
open GlobalTheory.SeriesTie.Setup

theorem ratHecke_realRd : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (ρ : Setup D.ntw) (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (ν : ℂ), RealPin Rl cG ρ → ChrEq (Rl.mu0 ((j : ℕ) + 1)) (Rl.C.mu0 j) → (∀ P, IsSplitPl D.host P → P ∉ D.ntw.S0 i → Bridge.SplitOff P (Rl.Sb : Set (Pl D.host.E))) → ∀ hL : ∀ n, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL n), NX.HeckeStabR S ((j : ℕ) + 1) (hL ((j : ℕ) + 1)) → GlobalTheory.ExportPin.Reads Rl cG S YS hL → RatHecke (realRd YS v₀ hρ i j b ν) := by
  intro D Γ _ _ Pl0 I0 T A3 Ks _ _ _ Rl cG S YS v₀ ρ hρ i j b ν hp hchr hsplit hL hs hR k P hk f
  obtain ⟨hk1, hkr, hPs, hPS0⟩ := hk
  have hso := hsplit P hPs hPS0
  have hPg : Bridge.SplitOff P (((ρ.B i j b).G.Pg : Finset _) : Set (Pl D.host.E)) :=
    GlobalTheory.T.split_off_outside_S0 hρ i _ (fun P' hP' => by
      obtain ⟨k', hk'⟩ := hρ.Pg i j b P' hP'
      exact D.ntw.placesOver_subset_exceptional i k' hk') P hPs hPS0
  have hdQ : Bridge.SplitOff P (((ρ.B i j b).de.Q : Finset _) : Set (Pl D.host.E)) :=
    GlobalTheory.T.split_off_outside_S0 hρ i _ (fun P' hP' => by
      rw [hρ.delta i j b] at hP'
      exact D.ntw.primes_subset_exceptional i (mem_half.1 hP').1) P hPs hPS0
  by_cases hd : ∃ α R z, ρ.IsHeckeDatum i j b k P α R z
  swap
  · exact ⟨0, fun α R z d => absurd ⟨α, R, z, d⟩ hd⟩
  obtain ⟨α₀, R₀, z₀, d₀⟩ := hd
  obtain ⟨a, ha⟩ := GlobalTheory.T.twisting_char_values_mem_coeff_field_range hρ i j b z₀
  have hde : ∀ α R z, ρ.IsHeckeDatum i j b k P α R z → (((ρ.B i j b).de.chi z : Circle) : ℂ) = ρ.e i b a :=
    fun α R z d => by
      rw [ha, GlobalTheory.T.heckeCharacter_value_at_splitPlace_determinant _ _ _ _ P k α z (hp.delta i j b) (hρ.base i j b).de.unram (hρ.base i j b).de.split hdQ d.elt d.det,
        GlobalTheory.T.heckeCharacter_value_at_splitPlace_determinant _ _ _ _ P k α₀ z₀ (hp.delta i j b) (hρ.base i j b).de.unram (hρ.base i j b).de.split hdQ d₀.elt d₀.det]
  have hchr' : ChrEq (ρ.B i j b).mu0 (Rl.C.mu0 j) := by rw [hp.mu0 i j b]; exact hchr
  have hmu0 : ∀ α R z, ρ.IsHeckeDatum i j b k P α R z →
      (((ρ.B i j b).mu0 z : Circle) : ℂ) = (((Rl.C.mu0 j).val P : ℂˣ) : ℂ) ^ k :=
    fun α R z d => GlobalTheory.T.heckeCharacter_value_at_splitPlace_determinant _ _ _ _ P k α z hchr' (hρ.base i j b).unram
      ((hρ.base i j b).places.split.elim fun _ h => h.2.2.mono h.1) hPg d.elt d.det
  refine ⟨a⁻¹ • (YS.eF i _ b (Nat.le_add_left _ _) j.2).symm
    (NX.hkFR S i ((j : ℕ) + 1) b (hL _) hs k P (YS.eF i _ b (Nat.le_add_left _ _) j.2 f)), ?_⟩
  rcases eq_or_ne ν 0 with rfl | hν
  · intro α R z d
    rw [realRd_apply, realRd_apply YS v₀ hρ i j b 0 f, inv_zero, zero_smul, zero_smul, map_zero]
  rw [heckeAt_realRd YS v₀ hρ i j b hν]
  intro α R z d
  have hdc := d.reps
  rw [GlobalTheory.T.complex_principal_level_eq_realisation_principal_level Rl hp i j b] at hdc
  have key := evK_hkFR YS v₀ hρ i j b (hL _) hs k P R _
    (evW_reads YS v₀ hL hR j k P hPs hso hkr α R d.elt hdc) (YS.eF i _ b (Nat.le_add_left _ _) j.2 f)
  funext x
  rw [Setup.hecke_apply, map_smulₛₗ]
  change ρ.e i b a⁻¹ * ((1 : ℂ)⁻¹ • evK YS v₀ hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2
    ((YS.eF i _ b (Nat.le_add_left _ _) j.2).symm _))) x = _ * _ *
      ∑ γ ∈ R, ((1 : ℂ)⁻¹ • evK YS v₀ hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2 f)) (x * γ)
  rw [LinearEquiv.apply_symm_apply, key]
  simp only [inv_one, one_smul, Pi.smul_apply, smul_eq_mul, heckeLin, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Base.mu, MonoidHom.mul_apply, Circle.coe_mul, hmu0 α R z d, hde α R z d, map_inv₀]
  rw [show normV P = Nat.card (kP P) from rfl, D.sp.V_rank _ (Nat.le_add_left _ _) j.2]
  simp only [one_mul]
  ring

end GlobalTheory.SeriesTie.HkRat
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.TwInputs

theorem laws_of_serSide : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), (∀ i, D.ntw.NonzeroIndexPlace i → ∀ j b, RatRow Y.YS X.geo.v₀ Y.Z.good i j b) → Laws Y.Z.good Y.Z.rd := by
  intro D X E Y hR
  refine ⟨fun i j b => ?_, fun i j b => ?_, fun i j b => ?_, fun i hi j b => Y.Z.rat (hR i hi j b)⟩
  · exact GlobalTheory.SeriesTie.realRd_faithful D _ _ _ _ _ _ X.R X.cG Y.S Y.YS X.geo.v₀ Y.Z.ρ Y.Z.good i j b _
      (Y.Z.scalar i j b).ne X.unif X.char.models.HW (Y.Z.vec j)
      ((GlobalTheory.T.rational_datum_small_field_form_hecke_scalar_unit D X E Y).1 _ (Nat.le_add_left _ _) j.2)
  · exact GlobalTheory.SeriesTie.actRead_realRd D _ _ _ _ _ _ X.R X.cG Y.S Y.YS X.geo.v₀ Y.Z.ρ Y.Z.good i j b _
      Y.Z.pin X.unif X.char.models.HW
  · exact Y.Z.heckeRead (GlobalTheory.SeriesTie.HkRat.ratHecke_realRd D _ _ _ _ _ _ X.R X.cG Y.S Y.YS X.geo.v₀ Y.Z.ρ Y.Z.good i j b _
      Y.Z.pin (X.char.lev.mu0 j) (GlobalTheory.SplitOffS0.main Y.Z.good i _ (Y.Sb i)) Y.H.hL
      (Y.H.hs _ (Nat.le_add_left _ _) j.2) Y.reads)

end GlobalTheory.TwInputs
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnivSupOfXi
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.TwInputs

theorem univSup_of_xi : ∀ (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (rd : Rds D.nexp ρ), FullTie hρ rd → Laws hρ rd → XiType rd → XiBdd rd → ∀ E : IntegralHeckeForms.XD D, UnivSup D E := by
  intro D ρ hρ rd F L hT hB E i hi j hj b a _
  obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.1 hj
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hj1
  let j' : Fin D.R.m := ⟨n, hj2⟩
  have T := F.tie i j' b
  obtain ⟨c, hc⟩ := hB i hi j' b _ _ _ (T.dat a)
  refine ⟨c, fun Q M hs hcl hS hlev => ?_⟩
  have hQ : InRange D.ntw i Q := ⟨hs, hcl, hS⟩
  have hnp : ∀ v ∈ Q, ((normProd (T.supp a) : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal :=
    fun v hv h => Finset.disjoint_left.1 hlev hv ((T.lev_iff a v).2 h)
  obtain ⟨x, hx, he⟩ := T.thU_of_rat (L.rat i hi j' b).2.2 M hQ hlev
  classical
  refine ⟨∑ a', Finsupp.single (spread D.nexp i Q M (ρ.ch i) a') (x a'), ?_, fun δ => ?_⟩
  · rw [he, grpSum, ← Finsupp.sum_finsetSum_index (fun _ => by rw [TensorProduct.zero_tmul])
      (fun _ _ _ => by rw [TensorProduct.add_tmul])]
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [Finsupp.sum_single_index (by rw [TensorProduct.zero_tmul])]
  · have h0 : ∀ a', x a' ∈ Fm0 D.nexp i ((j' : ℕ) + 1) b :=
      fun a' => hT i hi j' b Q M hQ _ _ _ (T.dat a) hnp a' (x a') (hx a')
    have h1 : ∀ a', ((D.ntw.l i : D.ntw.O i) ^ c) • x a' ∈ D.nexp.Bsup i ((j' : ℕ) + 1) b :=
      fun a' => hc Q M hQ hnp a' (x a') (hx a')
    rw [Finsupp.finsetSum_apply]
    refine ⟨Submodule.sum_mem _ fun a' _ => ?_, ?_⟩
    · rw [Finsupp.single_apply]; split_ifs
      · exact h0 a'
      · exact zero_mem _
    · rw [Finset.smul_sum]
      refine Submodule.sum_mem _ fun a' _ => ?_
      rw [Finsupp.single_apply]; split_ifs
      · exact h1 a'
      · rw [smul_zero]; exact zero_mem _

end GlobalTheory.TwInputs
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HkSSOfSides
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HkSSOfRowsGuarded
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeparableCompSmul
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangePolynomialAnnihilatesDescent
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangePolynomialAnnihilatesDescent
open Polynomial
open scoped TensorProduct

namespace GlobalTheory

theorem baseChange_polynomial_kills_descent (Ks L0 KB WK ι : Type) [Field Ks] [Field L0] [Field KB]
    [Algebra Ks L0] [Algebra Ks KB] [AddCommGroup WK]
    [Module Ks WK] (rd : L0 →+* KB) (hrd : ∀ a : Ks, rd (algebraMap Ks L0 a) = algebraMap Ks KB a)
    (T0 : Module.End Ks WK) (s : Finset ι) (ρ : ι → Module.End Ks WK) (a : ι → L0) (q : L0[X])
    (hq : ∀ z ∈ LinearMap.range (∑ g ∈ s, a g • LinearMap.baseChange L0 (ρ g)),
      Polynomial.aeval (LinearMap.baseChange L0 T0) q z = 0) :
    ∀ y ∈ LinearMap.range (∑ g ∈ s, rd (a g) • LinearMap.baseChange KB (ρ g)),
      Polynomial.aeval (LinearMap.baseChange KB T0) (q.map rd) y = 0 := by
  classical

  let rdL : L0 →ₗ[Ks] KB :=
    { toFun := rd
      map_add' := rd.map_add
      map_smul' := fun c x => by
        simp only [Algebra.smul_def, map_mul, hrd, RingHom.id_apply] }
  let R : L0 ⊗[Ks] WK →ₗ[Ks] KB ⊗[Ks] WK := LinearMap.rTensor WK rdL
  have hRt : ∀ (c : L0) (w : WK), R (c ⊗ₜ[Ks] w) = rd c ⊗ₜ[Ks] w := fun c w => rfl

  have hRs : ∀ (c : L0) (z : L0 ⊗[Ks] WK), R (c • z) = rd c • R z := by
    intro c z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x w => simp [TensorProduct.smul_tmul', hRt]
    | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]

  set B0 := LinearMap.baseChange L0 T0 with hB0
  set B := LinearMap.baseChange KB T0 with hB
  have hRB : ∀ z, R (B0 z) = B (R z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x w => simp [hB0, hB, hRt]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hRpow : ∀ (n : ℕ) z, R ((B0 ^ n) z) = (B ^ n) (R z) := by
    intro n
    induction n with
    | zero => intro z; simp
    | succ n ih =>
      intro z
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hRB]
  have hRq : ∀ (p : L0[X]) z, Polynomial.aeval B (p.map rd) (R z) = R (Polynomial.aeval B0 p z) := by
    intro p z
    induction p using Polynomial.induction_on' with
    | add p r hp hr =>
      simp only [Polynomial.map_add (f := _), map_add (f := _), LinearMap.add_apply, hp, hr]
    | monomial n c =>
      rw [Polynomial.map_monomial, Polynomial.aeval_monomial, Polynomial.aeval_monomial]
      simp only [Module.End.mul_apply, Module.algebraMap_end_apply, hRs, hRpow]

  have hE : ∀ (c : KB) (f : WK),
      (∑ g ∈ s, rd (a g) • LinearMap.baseChange KB (ρ g)) (c ⊗ₜ[Ks] f)
        = c • R ((∑ g ∈ s, a g • LinearMap.baseChange L0 (ρ g)) ((1 : L0) ⊗ₜ[Ks] f)) := by
    intro c f
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.baseChange_tmul, map_sum,
      hRs, hRt, map_one, Finset.smul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [mul_comm]
  rintro y ⟨x, rfl⟩
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c f =>
    rw [hE, map_smul, hRq, hq _ ⟨_, rfl⟩, map_zero, smul_zero]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, add_zero]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangePolynomialAnnihilatesDescentStatement
open Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseChange_polynomial_annihilates_descent : ∀ (Ks L0 KB WK ι : Type) [Field Ks] [Field L0] [Field KB] [Algebra Ks L0] [Algebra Ks KB] [AddCommGroup WK]
    [Module Ks WK] (rd : L0 →+* KB), (∀ a : Ks, rd (algebraMap Ks L0 a) = algebraMap Ks KB a) →
    ∀ (T0 : Module.End Ks WK) (s : Finset ι) (ρ : ι → Module.End Ks WK) (a : ι → L0) (q : L0[X]),
    (∀ z ∈ LinearMap.range (∑ g ∈ s, a g • LinearMap.baseChange L0 (ρ g)),
      Polynomial.aeval (LinearMap.baseChange L0 T0) q z = 0) →
    ∀ y ∈ LinearMap.range (∑ g ∈ s, rd (a g) • LinearMap.baseChange KB (ρ g)),
      Polynomial.aeval (LinearMap.baseChange KB T0) (q.map rd) y = 0 := by
  first | exact @GlobalTheory.baseChange_polynomial_kills_descent | exact GlobalTheory.baseChange_polynomial_kills_descent | (intros; apply GlobalTheory.baseChange_polynomial_kills_descent <;> assumption)
end
end

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw
open Formalism.IndefR.NX
open scoped TensorProduct

namespace GlobalTheory.GoodSS

theorem aeval_intertwine {K M N : Type} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (e : M ≃ₗ[K] N) (A : Module.End K M) (B : Module.End K N) (h : ∀ x, e (A x) = B (e x)) (p : K[X]) (x : M) :
    e (Polynomial.aeval A p x) = Polynomial.aeval B p (e x) := by
  have hpow : ∀ n : ℕ, ∀ x, e ((A ^ n) x) = (B ^ n) (e x) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih => intro x; rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add (f := _), LinearMap.add_apply, hp, hq]
  | monomial n a => simp only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      map_smul, hpow]

theorem separable_comp_smul {K : Type} [Field K] {p : K[X]} (hp : p.Separable) {a : K} (ha : a ≠ 0) :
    (p.comp (Polynomial.C a * Polynomial.X)).Separable := by
  have h1 := IsCoprime.map hp (Polynomial.compRingHom (Polynomial.C a * Polynomial.X))
  rw [Polynomial.coe_compRingHom_apply, Polynomial.coe_compRingHom_apply] at h1
  have h2 : IsCoprime (p.comp (Polynomial.C a * Polynomial.X)) (Polynomial.C a) :=
    ⟨0, Polynomial.C a⁻¹, by rw [zero_mul, zero_add, ← Polynomial.C_mul, inv_mul_cancel₀ ha, Polynomial.C_1]⟩
  have h3 : Polynomial.derivative (p.comp (Polynomial.C a * Polynomial.X)) =
      (Polynomial.derivative p).comp (Polynomial.C a * Polynomial.X) * Polynomial.C a := by
    rw [Polynomial.derivative_comp, Polynomial.derivative_mul, Polynomial.derivative_C, Polynomial.derivative_X,
      zero_mul, zero_add, mul_one, mul_comm]
  show IsCoprime _ _
  rw [h3]
  exact h1.mul_right h2

theorem aeval_smul_comp {K M : Type} [Field K] [AddCommGroup M] [Module K M] (B : Module.End K M) {c : K}
    (hc : c ≠ 0) (p : K[X]) (y : M) :
    Polynomial.aeval (c • B) (p.comp (Polynomial.C c⁻¹ * Polynomial.X)) y = Polynomial.aeval B p y := by
  rw [Polynomial.aeval_comp]
  congr 2
  rw [map_mul, Polynomial.aeval_C, Polynomial.aeval_X, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
    smul_smul, inv_mul_cancel₀ hc, one_smul]


set_option maxHeartbeats 800000 in
theorem hkF_separable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks]
    [Algebra Ks D.what₂.LL] (Rl : Formalism.IndefR.Links.RealDat3 D A3 Ks) (F : Formalism.IndefR.Links.Face3 D A3)
    (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : RatDat D.ntw) (Y : NExpRealS Rl cG S) (H : NExpRealH Rl cG S Y) : CommG D → HkComm D → NExpHeckeRowX Rl cG S Y H (fun j => goodProjW S j D.nexp.eLL0) →
    Rl.Char3 F → Rl.toRealDat.LUnif → Rl.toRealDat.LIntegral →
    (∀ i P P', P ∈ D.ntw.S0 i → IsConjPl D.host P P' → P' ∈ D.ntw.S0 i) →
    (∀ i, placesOver D.host.E 2 ⊆ (D.ntw.S0 i : Set (PlE D.host))) →
    (∀ i, ∀ Q ∈ Rl.Sb, Q ∈ D.ntw.S0 i) →
    ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b k P, HkIdx i k P →
      ∃ p : (FractionRing (D.ntw.O i))[X], p.Separable ∧
        ∀ x ∈ V0 D.nexp i j b, Polynomial.aeval (D.nexp.hkF i j b k P) p x = 0 := by
  intro hG hC hX hR hU hI hS0c hS02 hS0b i hi j hj b k P hk
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
  obtain ⟨q, hqs, hq⟩ := GlobalTheory.T.hecke_commutation_real_expansion Rl F cG S Y H hG hC hX hR hU hI hS0c hS02 hS0b i hi j h1 h2 b k P hk

  set rd : ↥D.LL0 →+* KB S i b := readLL0 S i b with hrd
  set hst := Y.rho j h1 h2
  set hχ := Y.chi j h1 h2
  set T0 := GlobalTheory.GoodSS.opK S j (H.hL j k P) (fun x hx => H.hs j h1 h2 k P x hx) with hT0
  set s := (D.nexp.eAlg i b).coeff.support with hs
  set a : G0g D.nd → ↥D.LL0 := fun g => D.nexp.eLL0 g * (chiL S j hχ (S.eG.symm g))⁻¹ with ha
  set ρ : G0g D.nd → Module.End S.Ks (FmK S j) := fun g => rhoKG S j hst (S.eG.symm g) with hρ

  have hcoef : ∀ g, (D.nexp.eAlg i b).coeff g = rd (D.nexp.eLL0 g) := fun g => by
    rw [D.nexp.eAlg_def]; rfl
  have hsupp : ∀ g, g ∉ s → D.nexp.eLL0 g = 0 := fun g hg => by
    have h0 : (D.nexp.eAlg i b).coeff g = 0 := Finsupp.notMem_support_iff.1 hg
    rw [hcoef] at h0
    exact (map_eq_zero_iff rd rd.injective).1 h0

  have hE' : GlobalTheory.GoodSS.goodProjectorBaseChangeForms S j hst hχ D.nexp.eLL0 = ∑ g ∈ s, a g • LinearMap.baseChange ↥D.LL0 (ρ g) := by
    unfold GlobalTheory.GoodSS.goodProjectorBaseChangeForms
    refine finsum_eq_sum_of_support_subset _ fun g hg => ?_
    by_contra hgs
    exact hg (by simp only [hsupp g hgs, zero_mul, zero_smul])

  have hdesc := GlobalTheory.T.baseChange_polynomial_annihilates_descent S.Ks ↥D.LL0 (KB S i b) (FmK S j) (G0g D.nd) rd (fun _ => rfl) T0 s ρ a q
    (fun z hz => hq z (hE' ▸ hz))
  set c := H.cHk i b k P with hc
  have hc0 : c ≠ 0 := by
    rw [hc, H.cHk_pow]
    exact pow_ne_zero _ (H.cHk_unit i b P).ne_zero

  set B : Module.End (FractionRing (D.ntw.O i)) (Fm S i j b) := LinearMap.baseChange (KB S i b) T0 with hB
  have hAB : ∀ x, Y.eF i j b h1 h2 (D.nexp.hkF i j b k P x) = (c • B) (Y.eF i j b h1 h2 x) := fun x =>
    H.hkEq i j b h1 h2 k P x hk.2.2.2 hk.2.2.1 hk.2.1

  have hE : ∀ x0, Y.eF i j b h1 h2 (eG D.nexp i j b x0) =
      (∑ g ∈ s, rd (a g) • LinearMap.baseChange (KB S i b) (ρ g)) (Y.eF i j b h1 h2 x0) := by
    intro x0
    have hact : ∀ g y, actG S i j b hst hχ g y =
        (rd (chiL S j hχ (S.eG.symm g)))⁻¹ • LinearMap.baseChange (KB S i b) (ρ g) y := fun _ _ => rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [eG, MonoidAlgebra.lift_apply, Finsupp.sum, LinearMap.sum_apply, map_sum]
    refine (Finset.sum_congr rfl fun g _ => ?_).trans (LinearMap.sum_apply _ _ _).symm
    change Y.eF i j b h1 h2 ((D.nexp.eAlg i b).coeff g • D.nexp.actG i j b g x0) =
      rd (a g) • LinearMap.baseChange (KB S i b) (ρ g) (Y.eF i j b h1 h2 x0)
    rw [map_smul, Y.act i j b h1 h2 g x0, hact, hcoef]
    have hag : rd (a g) = rd (D.nexp.eLL0 g) * (rd (chiL S j hχ (S.eG.symm g)))⁻¹ := by
      simp only [ha, map_mul, map_inv₀]
    rw [hag]
    exact (mul_smul _ _ _).symm
  refine ⟨(q.map rd).comp (Polynomial.C c⁻¹ * Polynomial.X), ?_, ?_⟩
  · exact separable_comp_smul ((Polynomial.separable_map rd).2 hqs) (inv_ne_zero hc0)
  · rintro x ⟨x0, -, rfl⟩
    apply (Y.eF i j b h1 h2).injective
    rw [map_zero]
    refine (aeval_intertwine (Y.eF i j b h1 h2) _ (c • B) hAB _ _).trans ?_
    refine (aeval_smul_comp B hc0 _ _).trans ?_
    rw [hE]
    exact hdesc _ ⟨_, rfl⟩

end GlobalTheory.GoodSS
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckePreservesGoodPart
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckePreservesGoodPart
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw
open scoped TensorProduct

namespace GlobalTheory.HkGoodStable

theorem hkF_mem_V0 : ∀ (D : D7), CommG D → ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b k P, HkIdx i k P →
    ∀ x ∈ V0 D.nexp i j b, D.nexp.hkF i j b k P x ∈ V0 D.nexp i j b := by
  intro D hC i hi j hj b k P hk x hx
  have hc : ∀ g z, D.nexp.actG i j b g (D.nexp.hkF i j b k P z) = D.nexp.hkF i j b k P (D.nexp.actG i j b g z) :=
    fun g z => LinearMap.congr_fun (hC i hi b j hj g k P hk) z
  have hcomm : ∀ a, Commute (MonoidAlgebra.lift (FractionRing (D.ntw.O i))
      (Module.End (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b)) (G0g D.nd)
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (D.nexp.actG i j b)) a) (D.nexp.hkF i j b k P) := by
    intro a
    induction a using MonoidAlgebra.induction_on with
    | of g =>
      rw [MonoidAlgebra.lift_of]
      exact LinearMap.ext fun z => hc g z
    | add a a' ha ha' => rw [map_add (f := _)]; exact ha.add_left ha'
    | smul c a ha => rw [map_smul]; exact ha.smul_left c
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
  refine Submodule.mem_map.mpr ⟨D.nexp.hkF i j b k P y, ?_, ?_⟩
  · simp only [Fm0, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, LinearEquiv.coe_coe] at hy ⊢
    intro u
    have h := hy u
    rw [sub_eq_zero] at h ⊢
    rw [hc, h, map_smul]
  · exact LinearMap.congr_fun (hcomm (D.nexp.eAlg i b)) y

end GlobalTheory.HkGoodStable
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckePreservesGoodPartStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_preserves_good_part : ∀ (D : D7), CommG D → ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b k P, HkIdx i k P → ∀ x ∈ V0 D.nexp i j b, D.nexp.hkF i j b k P x ∈ V0 D.nexp i j b := by
  first | exact @GlobalTheory.HkGoodStable.hkF_mem_V0 | exact GlobalTheory.HkGoodStable.hkF_mem_V0 | (intros; apply GlobalTheory.HkGoodStable.hkF_mem_V0 <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitCharpolyLatticeKillsSpan
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitCharpolyLatticeKillsSpan
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw
open scoped TensorProduct

namespace GlobalTheory

theorem charpoly_split_kills_span : ∀ (O V B : Type) [CommRing O] [IsDomain O] [AddCommGroup V] [Module (FractionRing O) V] [Module O V] [IsScalarTower O (FractionRing O) V] [FiniteDimensional (FractionRing O) V] [AddCommGroup B] [Module O B] [Module.Free O B] [Module.Finite O B] (e : B →ₗ[O] V) (t : Module.End O B) (T : Module.End (FractionRing O) V), (∀ x, e (t x) = T (e x)) → ((LinearMap.charpoly t).map (algebraMap O (FractionRing O))).Splits → ∃ p : (FractionRing O)[X], p ≠ 0 ∧ p.Splits ∧ ∀ x ∈ Submodule.span (FractionRing O) (Set.range e), Polynomial.aeval T p x = 0 := by
  intro O V B _ _ _ _ _ _ _ _ _ _ _ e t T he hs
  refine ⟨(LinearMap.charpoly t).map (algebraMap O (FractionRing O)), ?_, hs, ?_⟩
  · exact ((LinearMap.charpoly_monic t).map _).ne_zero
  · have hpow : ∀ (n : ℕ) (b : B), (T ^ n) (e b) = e ((t ^ n) b) := by
      intro n
      induction n with
      | zero => intro b; simp
      | succ n ih => intro b; rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ← he, ih]
    have key : ∀ (q : O[X]) (b : B), Polynomial.aeval T (q.map (algebraMap O (FractionRing O))) (e b) = e (Polynomial.aeval t q b) := by
      intro q b
      induction q using Polynomial.induction_on' with
      | add p q hp hq => simp only [Polynomial.map_add (f := _), map_add (f := _), LinearMap.add_apply, hp, hq]
      | monomial n a =>
          simp only [Polynomial.map_monomial, Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, hpow, LinearMap.map_smul_of_tower]
          rw [algebraMap_smul]
    have hle : Submodule.span (FractionRing O) (Set.range e) ≤ LinearMap.ker (Polynomial.aeval T ((LinearMap.charpoly t).map (algebraMap O (FractionRing O)))) := by
      rw [Submodule.span_le]
      rintro _ ⟨b, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, key, LinearMap.aeval_self_charpoly, LinearMap.zero_apply, map_zero]
    intro x hx
    exact hle hx

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitCharpolyLatticeKillsSpanStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_charpoly_lattice_kills_span : ∀ (O V B : Type) [CommRing O] [IsDomain O] [AddCommGroup V] [Module (FractionRing O) V] [Module O V] [IsScalarTower O (FractionRing O) V] [FiniteDimensional (FractionRing O) V] [AddCommGroup B] [Module O B] [Module.Free O B] [Module.Finite O B] (e : B →ₗ[O] V) (t : Module.End O B) (T : Module.End (FractionRing O) V), (∀ x, e (t x) = T (e x)) → ((LinearMap.charpoly t).map (algebraMap O (FractionRing O))).Splits → ∃ p : (FractionRing O)[X], p ≠ 0 ∧ p.Splits ∧ ∀ x ∈ Submodule.span (FractionRing O) (Set.range e), Polynomial.aeval T p x = 0 := by
  first | exact @GlobalTheory.charpoly_split_kills_span | exact GlobalTheory.charpoly_split_kills_span | (intros; apply GlobalTheory.charpoly_split_kills_span <;> assumption)
end
end

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw
open Formalism.IndefR.NX
open scoped TensorProduct

namespace GlobalTheory.GoodSpan

theorem hkSS_of_rows_guarded {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks]
    [Algebra Ks D.what₂.LL] (Rl : Formalism.IndefR.Links.RealDat3 D A3 Ks) (F : Formalism.IndefR.Links.Face3 D A3)
    (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : RatDat D.ntw) (Y : NExpRealS Rl cG S) (H : NExpRealH Rl cG S Y)
    (hG : CommG D) (hC : HkComm D) (hSF : SupFull D)
    (X : NExpHeckeRowX Rl cG S Y H (fun j => goodProjW S j D.nexp.eLL0))
    (hR : Rl.Char3 F) (hU : Rl.toRealDat.LUnif) (hI : Rl.toRealDat.LIntegral)
    (hS0c : ∀ i P P', P ∈ D.ntw.S0 i → IsConjPl D.host P P' → P' ∈ D.ntw.S0 i)
    (hS02 : ∀ i, placesOver D.host.E 2 ⊆ (D.ntw.S0 i : Set (PlE D.host)))
    (hS0b : ∀ i, ∀ Q ∈ Rl.Sb, Q ∈ D.ntw.S0 i)
    (hEmb : ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b k P, HkIdx i k P → ∀ x,
      D.nexp.embB i j b (D.ntw.hk i j b k P x) = D.nexp.hkF i j b k P (D.nexp.embB i j b x))
    (hBr : ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b, LinearMap.range (D.nexp.embB i j b) =
      D.nexp.Bsup i j b ⊓ (V0 D.nexp i j b).restrictScalars (D.ntw.O i))
    (hSp : ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b k P, HkIdx i k P →
      ((LinearMap.charpoly (D.ntw.hk i j b k P)).map (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)))).Splits) :
    HkSS D := by
  intro i hi j hj b
  have := D.nexp.towFm i j b

  have hspan : ∀ x ∈ V0 D.nexp i j b,
      x ∈ Submodule.span (FractionRing (D.ntw.O i)) (Set.range (D.nexp.embB i j b)) := by
    intro x hx
    have hx' : x ∈ Submodule.span (FractionRing (D.ntw.O i)) (D.nexp.Bsup i j b : Set (D.nexp.Fm i j b)) := by
      rw [(hSF i hi j hj b).2]; exact Submodule.mem_top
    obtain ⟨y, hy, z, rfl⟩ := (IsLocalization.mem_span_iff (nonZeroDivisors (D.ntw.O i))).1 hx'
    rw [Submodule.span_eq] at hy
    have hyV : y ∈ V0 D.nexp i j b := by
      have e : y = (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (z : D.ntw.O i)) •
          (IsLocalization.mk' (FractionRing (D.ntw.O i)) (1 : D.ntw.O i) z • y) := by
        rw [smul_smul, mul_comm, IsLocalization.mk'_spec, map_one, one_smul]
      rw [e]; exact Submodule.smul_mem _ _ hx
    have hyR : y ∈ LinearMap.range (D.nexp.embB i j b) := by
      rw [hBr i hi j hj b]
      exact Submodule.mem_inf.2 ⟨hy, (Submodule.restrictScalars_mem _ _ _).2 hyV⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span (LinearMap.mem_range.1 hyR))

  have hpoly : ∀ k P, HkIdx i k P → ∃ p : (FractionRing (D.ntw.O i))[X], p.Separable ∧ p.Splits ∧
      ∀ x ∈ V0 D.nexp i j b, Polynomial.aeval (D.nexp.hkF i j b k P) p x = 0 := by
    intro k P hkP
    obtain ⟨p1, hp10, hp1s, hp1k⟩ := GlobalTheory.T.split_charpoly_lattice_kills_span (D.ntw.O i) (D.nexp.Fm i j b) (D.ntw.B i j b)
      (D.nexp.embB i j b) (D.ntw.hk i j b k P) (D.nexp.hkF i j b k P) (hEmb i hi j hj b k P hkP)
      (hSp i hi j hj b k P hkP)
    obtain ⟨p2, hp2s, hp2k⟩ :=
      GlobalTheory.GoodSS.hkF_separable Rl F cG S Y H hG hC X hR hU hI hS0c hS02 hS0b i hi j hj b k P hkP
    classical
    refine ⟨EuclideanDomain.gcd p1 p2, hp2s.of_dvd (EuclideanDomain.gcd_dvd_right _ _),
      hp1s.of_dvd hp10 (EuclideanDomain.gcd_dvd_left _ _), ?_⟩
    intro x hx
    rw [EuclideanDomain.gcd_eq_gcd_ab, mul_comm p1, mul_comm p2, map_add (f := _), map_mul, map_mul,
      LinearMap.add_apply, Module.End.mul_apply, Module.End.mul_apply, hp1k x (hspan x hx), hp2k x hx,
      map_zero, map_zero, add_zero]

  have hJ := GlobalTheory.JointDiag.le_iSup_jointEigenspace_inf (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b) {a : ℕ × PlE D.host // HkIdx i a.1 a.2}
    (fun a => D.nexp.hkF i j b a.1.1 a.1.2) (V0 D.nexp i j b)
    (fun a c => hC i hi j hj b _ _ _ _ a.2 c.2)
    (fun a x hx => GlobalTheory.T.hecke_preserves_good_part D hG i hi j hj b _ _ a.2 x hx)
    (fun a => hpoly _ _ a.2)
  refine hJ.trans (iSup_le fun ev => ?_)
  classical
  refine le_iSup_of_le (fun k P => if h : HkIdx i k P then ev ⟨(k, P), h⟩ else 0) (inf_le_inf_right _ ?_)
  unfold Eigsp
  refine le_iInf fun k => le_iInf fun P => le_iInf fun h => ?_
  refine (iInf_le _ ⟨(k, P), h⟩).trans ?_
  simp only [dif_pos h]
  exact le_rfl

end GlobalTheory.GoodSpan
end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwHkSS

theorem hkSS_of_sides : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), CommG D → HkComm D → SupFull D → HkSS D := by
  intro D X E Y hG hC hSF
  have hX : Formalism.IndefR.NX.NExpHeckeRowX X.R X.cG Y.S Y.YS Y.H (fun j => Formalism.IndefR.NX.goodProjW Y.S j D.nexp.eLL0) :=
    ⟨fun i k P hs ho _ _ hk α R hα hR x _ => Y.reads i k P hs ho hk α R hα hR x⟩
  exact GlobalTheory.GoodSpan.hkSS_of_rows_guarded X.R X.F X.cG Y.S Y.YS Y.H hG hC hSF hX X.char X.unif X.integral
    (fun i P P' hP hc => Y.Z.good.goodSetup_badPlaces_conj i P hP P' hc) (fun i => Y.Z.good.goodSetup_placesOverTwo_subset i) Y.Sb
    (fun i _ j hj b k P hk x => Y.hk_emb i j b k P x (Finset.mem_Icc.1 hj).1 (Finset.mem_Icc.1 hj).2 hk)
    Y.B_range Y.hk_split

end GlobalTheory.TwHkSS
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwInputs

theorem levelOf_of_serSide {D : D7} {X : RealSide D} {E : IntegralHeckeForms.XD D} (Y : SerSide X E) : Y.Z.ρ.LevelOf D.nexp :=
  ⟨fun i j b g => (Y.Z.tie i j b).U_eq g, fun i j b u hu => (Y.Z.tie i j b).psiU_eq u hu⟩

end GlobalTheory.TwInputs
