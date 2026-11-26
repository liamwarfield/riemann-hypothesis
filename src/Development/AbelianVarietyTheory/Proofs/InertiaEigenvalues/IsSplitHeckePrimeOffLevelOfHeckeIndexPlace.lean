module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BaseEmbeddingReadingEvalAdelicFunction
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharInfinityEqCoeffMulHalfNormPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PairFixedVectorLatticeVacuumOffLevels
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.NotFamConstZero
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSameData
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapVVSymmMapVV
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemLevelTypeFormsOfUniversalCoeffReading
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlacesTranslationLatticeBoundedNorm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsInnerEqFockInnerProductMulNorm
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockCoefficientRealPlaceTwoVacua
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurFiniteHeisenbergFockVacuumThetaFunctions

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitHeckePrimeOffLevelOfHeckeIndexPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitHeckePrimeOffLevelOfHeckeIndexPlace
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.GeoTie

set_option autoImplicit false

namespace GlobalTheory.HeckeIndexPrime

theorem isHeckePrime_of_hkIdx : ∀ (D : D7) (T0 : CoreJ D), LawsJ T0 → ∀ (i : D.ntw.Tw) (k : ℕ) (P : PlE D.host),
    Formalism.MainNotions.IntegralHeckeForms.HkIdx (X := D.ntw) i k P →
    GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.IsHeckePrime T0.Q.H T0.Q.l P.asIdeal (charAt P) ∧ charAt P ≠ D.ntw.l i := by
  intro D T0 hL i k P hk
  obtain ⟨_, _, hsp, hS⟩ := hk
  refine ⟨⟨P.isMaximal, GlobalTheory.HeckeSup.split_of_ne ((GlobalTheory.HeckeTieCompare.isSplitPl_iff P).1 hsp), charAt_prime P,
    charAt_mem P, GlobalTheory.HeckeSup.not_dvd_level hL (charAt_mem P) (GlobalTheory.HeckeTieCompare.level_notMem ⟨i, hS⟩)⟩, ?_⟩
  intro he
  apply hS
  have hm : P ∈ Formalism.BasicNotions.placesOver D.host.E (D.ntw.l i) := by
    show ((D.ntw.l i : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal
    rw [← he]
    exact charAt_mem P
  exact D.ntw.twistExcludedPlaces_contains_residueChar i hm

end GlobalTheory.HeckeIndexPrime
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitHeckePrimeOffLevelOfHeckeIndexPlaceStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.GeoTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSplitHeckePrimeOffLevel_of_heckeIndexPlace : ∀ (D : D7) (T0 : CoreJ D), LawsJ T0 → ∀ (i : D.ntw.Tw) (k : ℕ) (P : PlE D.host), Formalism.MainNotions.IntegralHeckeForms.HkIdx (X := D.ntw) i k P → GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.IsHeckePrime T0.Q.H T0.Q.l P.asIdeal (charAt P) ∧ charAt P ≠ D.ntw.l i := by
  first | exact @GlobalTheory.HeckeIndexPrime.isHeckePrime_of_hkIdx | exact GlobalTheory.HeckeIndexPrime.isHeckePrime_of_hkIdx | (intros; apply GlobalTheory.HeckeIndexPrime.isHeckePrime_of_hkIdx <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeUnitOfExportTie
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
open Formalism.MainNotions.IntegralHeckeForms (HkIdx)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.GeoTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T1 : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m} {T0 : CoreJ D} [Algebra T0.Q.c.F D.what₂.LL]
  {Rl : RealDat3 D A3 T0.Q.c.F} {cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  {κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)} {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}
  (fw : FWTie T0 Rl.toRealDat κ v₀)

theorem exists_delta_root {ρ : GlobalTheory.SeriesTie.Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    (z : (Formalism.L2.Theta.AE D)ˣ) : ∃ a : FractionRing (D.ntw.O i),
      ρ.e i b a = (((ρ.B i j b).de.chi z : Circle) : ℂ) ∧ ∃ n : ℕ, n ≠ 0 ∧ a ^ n = 1 := by
  obtain ⟨σ, hσ⟩ := ρ.rc.exists_sym z
  have hopen : IsOpen ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker : Set (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om)) := by
    have e : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker = (D.ntw.delta i).ker := by
      ext g
      cases b <;> simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, MonoidHom.mem_ker]
    rw [e]
    exact D.ntw.delta_open i
  have : Finite (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om ⧸ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker) :=
    Subgroup.quotient_finite_of_isOpen _ hopen
  have hfi : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hn : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have hpow : Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ ^ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.index = 1 := by
    rw [← map_pow]
    exact MonoidHom.mem_ker.1 (Subgroup.pow_index_mem _ σ)
  refine ⟨algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))
    (algebraMap (D.ntw.O0 i) (D.ntw.O i) ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)), ?_, _, hn, ?_⟩
  · rw [hρ.delta i j b]
    exact (GlobalTheory.SeriesTie.charOf_eq ρ.rc ((ρ.eO i b).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i))) hopen hσ hn hpow).symm
  · rw [← map_pow, ← map_pow, ← Units.val_pow_eq_pow_val, hpow, Units.val_one, map_one, map_one]

section Side

variable {i : D.ntw.Tw} (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]) (b : Bool) (j : Fin D.R.m)

theorem valC_geoHecke {P : PlE D.host} {k : ℕ} (hP : GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.IsHeckePrime T0.Q.l P.asIdeal (charAt P))
    (s : T0.Q.c.F) {f g : T0.R ((j : ℕ) + 1)} (hf : f ∈ sec (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c (wtA (κ j)) (κ j).n)
    (hfg : GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.GeoHecke T0 ((j : ℕ) + 1) P.asIdeal (charAt P) k s f g)
    (z : FrC YS iC b ((j : ℕ) + 1)) (quot : HkKer P.asIdeal (charAt P) k z → FrC YS iC b ((j : ℕ) + 1))
    (hq : ∀ C, IsHkQuot P.asIdeal (charAt P) k z C (quot C)) :
    valC z g = embC YS iC b s * ∑ᶠ C, valC (quot C) f := by
  have hrel := hfg (PAt (embC YS iC b)) z
  have hL : GlobalTheory.Reg.EvLaws (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c := (GlobalTheory.Reg.evLaws_genFr_nonempty_comp _ _ _ _ _ _).1
  have hfun := GlobalTheory.HeckePointLaw.heckePointLaws.2.2.1 _ _ _ _ (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c P.asIdeal (charAt P) k hP
  have hterm : ∀ C, hkTerm (fun S _ _ => FrPt (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c S) (fun φ y z => FrMap φ y z)
      (fun Ω _ _ _ y => hkKer (Xo := T0.Q.Xo ((j : ℕ) + 1)) P.asIdeal (charAt P) k Ω y)
      (fun Ω _ _ _ y C z => hkRelFr P.asIdeal (charAt P) k (GlobalTheory.ThetaTrace.hkTr (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c (charAt P)) Ω y C z)
      f z C = valC (quot C) f := by
    intro C
    have hex : ∃ w, hkRelFr P.asIdeal (charAt P) k (GlobalTheory.ThetaTrace.hkTr (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c (charAt P))
        (PAt (embC YS iC b)) z C w := ⟨quot C, hq C⟩
    unfold hkTerm
    rw [dite_eq_left hex]
    have hm := hfun (PAt (embC YS iC b)) z C _ _ hex.choose_spec (hq C)
    exact (GlobalTheory.Reg.PChartModel.evR_map hL hf.1 (AlgHom.id _ _) hm).symm
  change toCp _ (evR (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c g z) = _
  unfold evR
  rw [hrel, map_mul, toCp_algebraMap]
  congr 1
  unfold hkVal
  exact finsum_congr hterm

end Side

end GlobalTheory.GeoTie
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SameSetup
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwInputs.Move

variable {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}

def CopyTw.cm (h : CopyTw D D' ι e) (j : Fin D.R.m) : Fin D'.R.m :=
  Fin.cast (congrArg Ranks.m h.gal.R) j

theorem CopyTw.cm_val (h : CopyTw D D' ι e) (j : Fin D.R.m) : ((h.cm j : Fin D'.R.m) : ℕ) = j := rfl

abbrev SameSetup (ρ : Setup D.ntw) (ρ' : Setup D'.ntw) : Prop := SameData ρ ρ'

def RdRel (h : CopyTw D D' ι e) {ρ : Setup D.ntw} {ρ' : Setup D'.ntw} (rd : Rds D.nexp ρ) (rd' : Rds D'.nexp ρ') : Prop :=
  ∀ (i : D.ntw.Tw) (i' : D'.ntw.Tw) (hi : HEq i i') (j : Fin D.R.m) (b : Bool) (f : D.nexp.Fm i ((j : ℕ) + 1) b),
    HEq (rd' i' (h.cm j) b (h.fmCast hi ((j : ℕ) + 1) b f)) (rd i j b f)

end GlobalTheory.TwInputs.Move

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelCharacterApplyEqLevelFunctionSwap
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ExportSeries GlobalTheory.ConjTwist GlobalTheory.SeriesTie.Scale

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.MtLatConj

variable {D : D7}

theorem locC_conj {τ : ℂ ≃+* ℂ} {ν ν' : Twist D Circle} (h : ConjChar τ ν ν') (hν : ν.Good) (hν' : ν'.Good)
    (PP : Pl D.host.E) (u : (kP PP)ˣ) : τ ((ν.locC PP u : ℂˣ) : ℂ) = ((ν'.locC PP u : ℂˣ) : ℂ) := by
  classical
  unfold Twist.locC
  by_cases hP : PP ∈ ν.Q
  · have hP' : PP ∈ ν'.Q := by rw [h.1]; exact hP
    rw [if_pos hP, if_pos hP']
    exact (h.res hν hν' hP u).symm
  · have hP' : PP ∉ ν'.Q := by rw [h.1]; exact hP
    rw [if_neg hP, if_neg hP']
    simp

theorem levPOf_ext1_apply_eq_units_map_inv {r : ℕ} {Pg : Finset (Pl D.host.E)} (P : LevelP Pg r ℂ) {τ : ℂ ≃+* ℂ}
    (hP : ∀ p, τ ((P.chi p : ℂˣ) : ℂ) = ((P.chi p : ℂˣ) : ℂ)) (g : G0 Pg r) :
    τ ((Formalism.L2.DIV.ext1 P.H P.chi g : ℂˣ) : ℂ) = ((Formalism.L2.DIV.ext1 P.H P.chi g : ℂˣ) : ℂ) := by
  unfold Formalism.L2.DIV.ext1
  split_ifs
  · exact hP _
  · simp

theorem levFn_conj {S T : HSp D} {B : Base S T} (hB : B.Good) {τ : ℂ ≃+* ℂ} {ψ ψ' : Twist D Circle} (hψ : ψ.Good)
    (hψ' : ψ'.Good) (hcc : ConjChar τ ψ ψ') (hf : FixDat B τ) (x : GL (Fin S.rank) (Lev.EAf D)) :
    τ ((levFn B.F.βS (B.levS ψ) x : ℂˣ) : ℂ) = ((levFn B.F.βS (B.levS ψ') x : ℂˣ) : ℂ) := by
  simp only [levFn, Base.levS, Units.val_mul, Units.coe_prod, map_mul, map_prod]
  rw [hcc.1]
  congr 1
  congr 1
  · exact levPOf_ext1_apply_eq_units_map_inv B.G.P hf.2.1 _
  · refine Finset.prod_congr rfl fun PP hPP => Finset.prod_congr rfl fun c _ => ?_
    exact hf.2.2 PP hPP _
  · refine Finset.prod_congr rfl fun PP _ => ?_
    rw [MonoidHom.mul_apply, MonoidHom.mul_apply, Units.val_mul, Units.val_mul, map_mul,
      locC_conj hf.conjChar hB.de hB.de, locC_conj hcc hψ hψ']

theorem mem_levJ_of {S T : HSp D} (B : Base S T) {ψ ψ' : Twist D Circle} (hQ : ψ'.Q = ψ.Q) {k : Bridge.Gf S}
    (hk : k ∈ B.levJ ψ') : k ∈ B.levJ ψ := by
  simp only [Base.levJ, Subgroup.mem_comap, Lev.toAfE, mem_lev, mem_parLev, Base.levS] at hk ⊢
  rw [hQ] at hk
  exact hk

set_option maxHeartbeats 800000 in
theorem levelCharacter_apply_eq_levelFunction_swap {S T : HSp D} (B : Base S T) (ψ : Twist D Circle) (k : B.levJ ψ) :
    B.levLam ψ k = levFn B.F.βS (B.levS ψ) (Formalism.UG.bc (Lev.swapAE D) k.1.1) := by
  unfold Base.levLam Lev.levCharAfE
  rfl

theorem levLam_conj {S T : HSp D} {B : Base S T} (hB : B.Good) {τ : ℂ ≃+* ℂ} {ψ ψ' : Twist D Circle} (hψ : ψ.Good)
    (hψ' : ψ'.Good) (hcc : ConjChar τ ψ ψ') (hf : FixDat B τ) (k : B.levJ ψ') :
    ((B.levLam ψ' k : ℂˣ) : ℂ) = τ ((B.levLam ψ ⟨k.1, mem_levJ_of B hcc.1 k.2⟩ : ℂˣ) : ℂ) := by
  rw [levelCharacter_apply_eq_levelFunction_swap, levelCharacter_apply_eq_levelFunction_swap]
  exact (levFn_conj hB hψ hψ' hcc hf _).symm

variable {n : ℕ}

def cmapGL (τ : ℂ ≃+* ℂ) : GLR D n →* GLR D n :=
  MonoidHom.pi fun t => (Units.map (RingHom.mapMatrix (τ : ℂ →+* ℂ) : Matrix (Fin n) (Fin n) ℂ →+* _).toMonoidHom).comp
    (Pi.evalMonoidHom (fun _ : D.what₂.Tau => GL (Fin n) ℂ) t)

theorem cmapGL_val (τ : ℂ ≃+* ℂ) (y : GLR D n) (t : D.what₂.Tau) (a b : Fin n) :
    ((cmapGL τ y t : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) a b = τ (((y t : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) a b) := rfl

theorem coefFn_conj (τ : ℂ ≃+* ℂ) (lam : D.what₂.Tau → DomWeight n) (F : Pol ℂ D.what₂.Tau n) (y : GLR D n) :
    coefFn (RingHom.id ℂ) lam (MvPolynomial.map (τ : ℂ →+* ℂ) F) y = τ (coefFn (RingHom.id ℂ) lam F (cmapGL τ.symm y)) := by
  simp only [coefFn, map_mul]
  congr 1
  · simp only [detFam, MonoidHom.coe_mk, OneHom.coe_mk, Units.coe_prod, map_prod, Units.val_zpow_eq_zpow_val, map_zpow₀,
      GeneralLinearGroup.val_det_apply]
    refine Finset.prod_congr rfl fun t _ => ?_
    congr 1
    have e := RingHom.map_det (τ : ℂ →+* ℂ) (((cmapGL τ.symm y t : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))
    refine Eq.trans ?_ e.symm
    congr 1
    ext a b
    simp [cmapGL_val]
  · simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_map]
    have e := MvPolynomial.hom_eval₂ F (RingHom.id ℂ) (τ : ℂ →+* ℂ)
      (fun v : D.what₂.Tau × Fin n × Fin n => ((cmapGL τ.symm y v.1 : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) v.2.1 v.2.2)
    refine Eq.trans ?_ e.symm
    congr 1
    funext v
    simp [cmapGL_val]

theorem cmapGL_embGL (τ : ℂ ≃+* ℂ) (hτ : ∀ (t : D.what₂.Tau) (e : D.host.E), τ (tauE D t e) = tauE D t e)
    (g : GL (Fin n) D.host.E) : cmapGL τ (embGL (tauE D) g) = embGL (tauE D) g := by
  funext t
  refine Units.ext (Matrix.ext fun a b => ?_)
  rw [cmapGL_val]
  exact hτ t _

theorem hasLaw_conj {i : Fin D.R.m} {B : Base (Vc D i) (Wc D i)} (hB : B.Good)
    {Φ : VsV D i ℂ →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank} {κ : ℂ} (hκ0 : κ ≠ 0) (hval : ∀ x, Φ x ∈ B.valSpace)
    (hκ : ∀ x : VsV D i ℂ, harmFn (Wc D i).rank B.w B.F.BS (Φ x) =
      κ • coefFn (RingHom.id ℂ) (lamV D i) (x : Pol ℂ D.what₂.Tau (Vc D i).rank))
    {τ : ℂ ≃+* ℂ} (hτE : ∀ (t : D.what₂.Tau) (e : D.host.E), τ.symm (tauE D t e) = tauE D t e)
    {ψ ψ' : Twist D Circle} (hψ : ψ.Good) (hψ' : ψ'.Good) (hcc : ConjChar τ ψ ψ') (hf : FixDat B τ)
    {x x' : Bridge.Gf (Vc D i) → VsV D i ℂ} (hxx : ∀ h, ConjVec i τ (x h) (x' h))
    (hlaw : B.HasLaw ψ (fun h => Φ (x h))) : B.HasLaw ψ' (fun h => Φ ((τ κ / κ) • x' h)) := by
  intro γ h k
  have hfn : ∀ (w : VsV D i ℂ) z, harmFn (Wc D i).rank B.w B.F.BS (Φ w) z = κ * coefLin (lamV D i) w z :=
    fun w z => congrFun (hκ w) z
  obtain ⟨γE, hγ⟩ : ∃ γE, Bridge.IsRatMat (Vc D i) γ γE := by
    obtain ⟨y, -, hy⟩ := γ.2
    exact ⟨y, hy.symm⟩
  set u := realGL B.F.θ (Vc D i) γ with hu_def
  have hu : u = embGL (tauE D) γE := realGL_rat hB.frame.vac.2.inf hγ
  have hact : ∀ P z, harmFn (Wc D i).rank B.w B.F.BS (B.act γ P) z =
      harmFn (Wc D i).rank B.w B.F.BS P (u⁻¹ * z) := fun P z => harmFn_fockGL _ _ _ _ _
  have hfix : ∀ z, cmapGL τ.symm (u⁻¹ * z) = u⁻¹ * cmapGL τ.symm z := by
    intro z
    rw [map_mul, hu, ← map_inv, cmapGL_embGL τ.symm hτE]
  have hconj : ∀ w z, coefLin (lamV D i) (x' w) z = τ (coefLin (lamV D i) (x w) (cmapGL τ.symm z)) := fun w z => by
    change coefFn (RingHom.id ℂ) (lamV D i) (x' w : Pol ℂ D.what₂.Tau (Vc D i).rank) z =
      τ (coefFn (RingHom.id ℂ) (lamV D i) (x w : Pol ℂ D.what₂.Tau (Vc D i).rank) _)
    rw [hxx w]
    exact coefFn_conj τ _ _ z
  set g := Bridge.ratF (Vc D i) γ * h * (k : Bridge.Gf (Vc D i)) with hg
  set lam : ℂ := ((B.levLam ψ ⟨k.1, mem_levJ_of B hcc.1 k.2⟩ : ℂˣ) : ℂ) with hlam
  have hL : Φ (x g) = lam • B.act γ (Φ (x h)) := hlaw γ h ⟨k.1, mem_levJ_of B hcc.1 k.2⟩
  have E1 : ∀ z, coefLin (lamV D i) (x g) z = lam * coefLin (lamV D i) (x h) (u⁻¹ * z) := by
    intro z
    have e1 : harmFn (Wc D i).rank B.w B.F.BS (Φ (x g)) z =
        lam * harmFn (Wc D i).rank B.w B.F.BS (B.act γ (Φ (x h))) z := by
      rw [hL, map_smul]
      rfl
    rw [hact, hfn, hfn] at e1
    apply mul_left_cancel₀ hκ0
    rw [e1]
    ring
  have hl' : ((B.levLam ψ' k : ℂˣ) : ℂ) = τ lam := levLam_conj hB hψ hψ' hcc hf k
  show Φ ((τ κ / κ) • x' g) = ((B.levLam ψ' k : ℂˣ) : ℂ) • B.act γ (Φ ((τ κ / κ) • x' h))
  rw [hl']
  refine sub_eq_zero.1 (GlobalTheory.T.harmonic_polynomial_eq_zero_of_function D _ _ B.w B.F.BS hB.wt (GlobalTheory.CoefLatConj.pq_le hB) _
    (sub_mem (hval _) (Submodule.smul_mem _ _ (Base.act_mem_valSpace _ (hval _)))) ?_)
  funext z
  have e2 : ∀ (P Q : PolF D (Wc D i).rank (Vc D i).rank) (a : ℂ), harmFn (Wc D i).rank B.w B.F.BS (P - a • Q) z =
      harmFn (Wc D i).rank B.w B.F.BS P z - a * harmFn (Wc D i).rank B.w B.F.BS Q z := fun P Q a => by
    rw [map_sub, map_smul]
    rfl
  rw [e2, hact, hfn, hfn, map_smul, map_smul]
  change κ * ((τ κ / κ) * coefLin (lamV D i) (x' g) z) - τ lam * (κ * ((τ κ / κ) * coefLin (lamV D i) (x' h) (u⁻¹ * z))) = 0
  rw [hconj, hconj, hfix, E1, map_mul]
  ring

theorem mtLat_conj : ∀ (D : D7) (i : Fin D.R.m) (B : Base (Vc D i) (Wc D i)), B.Good → B.w.lam = lamV D i → ∀ (Φ : VsV D i ℂ →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (κ : ℂ), κ ≠ 0 → (∀ x, Φ x ∈ B.valSpace) → (∀ x : VsV D i ℂ, harmFn (Wc D i).rank B.w B.F.BS (Φ x) = κ • coefFn (RingHom.id ℂ) (lamV D i) (x : Pol ℂ D.what₂.Tau (Vc D i).rank)) → ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K)) (O : Subring ℂ), IsCoefRing σ emb O → ∀ τ : ℂ ≃+* ℂ, (∀ a : K, τ (σ a) = σ a) → ∀ (ψ ψ' : Twist D Circle), ψ.Good → ψ'.Good → ConjChar τ ψ ψ' → FixDat B τ → ∀ f f' : Bridge.Gf (Vc D i) → PolF D (Wc D i).rank (Vc D i).rank, (∀ h, ∃ x x' : VsV D i ℂ, ConjVec i τ x x' ∧ f h = Φ x ∧ f' h = Φ ((τ κ / κ) • x')) → f ∈ B.mtLat σ emb O ψ → f' ∈ B.mtLat σ emb (O.map (τ : ℂ →+* ℂ)) ψ' := by
  intro D i B hB hlam Φ κ hκ0 hval hκ K _ _ σ emb O hc τ hτ ψ ψ' hψ hψ' hcc hf f f' hff hfm
  choose x x' hxx hfx hfx' using hff
  have hτE : ∀ (t : D.what₂.Tau) (e : D.host.E), τ.symm (tauE D t e) = tauE D t e := fun t e => by
    rw [← hc.emb t, RingHom.comp_apply, τ.symm_apply_eq, hτ]
  obtain ⟨hform, hlat⟩ := (Base.mem_mtLat B σ emb O).1 hfm
  have hlaw : B.HasLaw ψ (fun h => Φ (x h)) := by
    have e : f = fun h => Φ (x h) := funext hfx
    rw [← e]
    exact ((Base.mem_formsC B).1 hform).2
  have e' : f' = fun h => Φ ((τ κ / κ) • x' h) := funext hfx'
  refine (Base.mem_mtLat B σ emb (O.map (τ : ℂ →+* ℂ))).2 ⟨(Base.mem_formsC B).2 ⟨fun h => (hfx' h).symm ▸ hval _, ?_⟩, fun h => ?_⟩
  · rw [e']
    exact hasLaw_conj hB hκ0 hval hκ hτE hψ hψ' hcc hf hxx hlaw
  · rw [hfx' h]
    exact (GlobalTheory.CoefLatConj.conj_mem_iff Φ hlam hκ0 hval hκ σ emb O τ hτ h (hxx h)).1 (hfx h ▸ hlat h)

end GlobalTheory.MtLatConj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaSeriesTypeUnderSupportedLifts
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaSeriesTypeUnderSupportedLifts
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.TypeSupportLift

variable {D : D7}

theorem exists_isBaseFrame {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hβ : IsFrame β Λ) (h : IsSelfDualC V Λ) :
    ∃ N, Lev.IsBaseFrame V β Λ N := by
  obtain ⟨_, N, hB⟩ := GlobalTheory.FinAdIdent.exists_baseFrame V Λ h
  exact ⟨N, hβ, hB.2⟩

theorem idem_add_conj_mul {P : Finset (Pl D.host.E)} (hP : SplitSet P) {PP : Pl D.host.E} (hPP : PP ∈ P) :
    (idem P + cA D (idem P)) * (idemAt PP + cA D (idemAt PP)) = idemAt PP + cA D (idemAt PP) := by
  have e1 : idem P * idemAt PP = idemAt PP := by
    rw [idem, Finset.sum_mul, Finset.sum_eq_single PP (fun q hq hne => hP.mul_eq_zero hq hPP fun e => hne e.symm)
      (fun h => absurd hPP h)]
    exact (hP.isIdemAt hPP).1.1
  have e2 : idem P * cA D (idemAt PP) = 0 := by
    rw [idem, Finset.sum_mul]
    exact Finset.sum_eq_zero fun q hq => hP.mul_conj hq hPP
  have e3 : cA D (idem P) * idemAt PP = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [idem, map_sum, Finset.sum_mul]
    exact Finset.sum_eq_zero fun q hq => by rw [mul_comm]; exact hP.mul_conj hPP hq
  have e4 : cA D (idem P) * cA D (idemAt PP) = cA D (idemAt PP) := by rw [← RingHom.map_mul, e1]
  rw [add_mul, mul_add, mul_add, e1, e2, e3, e4, add_zero, zero_add]

theorem suppAt_idem_of_mem {V : HSp D} {P : Finset (Pl D.host.E)} (hP : SplitSet P) {PP : Pl D.host.E} (hPP : PP ∈ P)
    {g : GA D V} (hg : SuppAt (idemAt PP) V g) : SuppAt (idem P) V g := fun i j => by
  rw [← hg i j, ← mul_assoc, idem_add_conj_mul hP hPP]

theorem exists_lift_supp {S T : HSp D} (B : Base S T) (hB : B.Good) (u : G0 B.G.Pg T.rank) :
    ∃ κ : GA D T, Lev.IsLevelLift T B.F.βT B.G.levT u κ ∧ SuppAt (idem B.G.Pg) T κ := by
  obtain ⟨N, hN⟩ := exists_isBaseFrame hB.frame.frT hB.frame.sdT
  obtain ⟨R, h1, -, hR⟩ := hB.places.split
  have hPg : SplitSet B.G.Pg := hR.mono h1
  obtain ⟨e, κ, hl, hall⟩ := GlobalTheory.ParahoricLift.exists_lift_prod T B.F.βT B.G.levT B.F.ΛT N hN
    (fun PP hP PP' hP' => by
      rcases hP' with hP' | hP'
      · exact GlobalTheory.ExportType.not_isConjPl_of_splitSet hR (h1 hP) (h1 hP')
      · exact absurd hP' (Finset.notMem_empty _))
    (Finset.disjoint_empty_right _) u
  refine ⟨_, (hall Finset.univ.toList (Finset.nodup_toList _) fun PP => Finset.mem_toList.2 (Finset.mem_univ PP)).1, ?_⟩
  refine List.prod_induction _ (fun a b ha hb => GlobalTheory.SplitLinear.suppAt_mul ha hb) (GlobalTheory.SplitLinear.suppAt_one _ _) ?_
  intro x hx
  obtain ⟨PP, -, rfl⟩ := List.mem_map.1 hx
  have hs := (hl PP).2.1
  rw [← idemAt_eq (hl PP).1] at hs
  exact suppAt_idem_of_mem hPg PP.2 hs


open Classical in
theorem series_type_supp : ∀ (D : D7) (S T : HSp D) (B : Base S T), B.Good → S.SigOK → ∀ ω : PairRep S T, B.IsWeil 1 ω →
    ∀ (u : G0 B.G.Pg T.rank) (hu : u ∈ B.G.P.H), ∃ κ : GA D T, Lev.IsLevelLift T B.F.βT B.G.levT u κ ∧
      SuppAt (idem B.G.Pg) T κ ∧ ∀ (Q : Finset (Pl D.host.E)), B.admitted Q →
        ∀ (φ : ∀ PP : ↥Q, Matrix (Fin T.rank) (Fin S.rank) (kP PP.1) → ℂ) (h : GA D S) (P : PolF D T.rank S.rank) (g : GA D T),
          series B.F ω (B.vecAt Q φ) h P (g * κ) = ((B.G.P.chi ⟨u, hu⟩ : ℂˣ) : ℂ) * series B.F ω (B.vecAt Q φ) h P g := by
  intro D S T B hB hS ω hω u hu
  obtain ⟨κ, hκ, hs⟩ := exists_lift_supp B hB u
  refine ⟨κ, hκ, hs, fun Q hQ φ h P g => ?_⟩
  have hred : ∀ PP : ↥Q, redFn B.F.βT PP.1 (Lev.finE T κ) = 1 := fun PP =>
    GlobalTheory.ExportSeries.redFn_eq_one_of_suppAt B.F.βT (GlobalTheory.ExportSeries.DualType.dualTypePlaces_isSplitNonconjugate_of_admissible hQ) Finset.subset_union_left
      (Finset.mem_union_right _ (Finset.mem_union_right _ PP.2))
      (fun h => Finset.disjoint_left.1 hQ.1.disj h (Finset.mem_union_right _ PP.2)) (parLev_St hκ.2.1) hs
  have := GlobalTheory.ExportType.series_type hB hS hQ hω hu (GlobalTheory.ExportType.lifts_of_isLiftG0 hκ) (φ := φ) (φ' := φ) (fun _ => 1)
    (fun PP y => by rw [hred PP, Units.val_one, Matrix.one_mul, Units.val_one, one_mul]) h P g
  rw [this, Finset.prod_const_one, inv_one, mul_one]

end GlobalTheory.TypeSupportLift

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaSeriesTypeUnderSupportedLiftsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSeries_type_under_supported_lifts : ∀ (D : D7) (S T : HSp D) (B : Base S T), B.Good → S.SigOK → ∀ ω : PairRep S T, B.IsWeil 1 ω → ∀ (u : G0 B.G.Pg T.rank) (hu : u ∈ B.G.P.H), ∃ κ : GA D T, Lev.IsLevelLift T B.F.βT B.G.levT u κ ∧ SuppAt (idem B.G.Pg) T κ ∧ ∀ (Q : Finset (Pl D.host.E)), B.admitted Q → ∀ (φ : ∀ PP : ↥Q, Matrix (Fin T.rank) (Fin S.rank) (kP PP.1) → ℂ) (h : GA D S) (P : PolF D T.rank S.rank) (g : GA D T), series B.F ω (B.vecAt Q φ) h P (g * κ) = ((B.G.P.chi ⟨u, hu⟩ : ℂˣ) : ℂ) * series B.F ω (B.vecAt Q φ) h P g := by
  first | exact @GlobalTheory.TypeSupportLift.series_type_supp | exact GlobalTheory.TypeSupportLift.series_type_supp | (intros; apply GlobalTheory.TypeSupportLift.series_type_supp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefLatLeTranslateSplitPlacesPrimeToL
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefLatLeTranslateSplitPlacesPrimeToL
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LatTranslate

theorem coefFn_natCast_smul {D : D7} {n : ℕ} {K : Type} [Field K] (σ : K →+* ℂ) (lam : D.what₂.Tau → Formalism.BasicNotions.DomWeight n)
    (N : ℕ) (F : Formalism.L2.DIV.Pol K D.what₂.Tau n) (x : GLR D n) :
    coefFn σ lam ((N : K) • F) x = (N : ℂ) * coefFn σ lam F x := by
  simp only [coefFn, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval₂Hom_C, map_natCast]
  ring

theorem coefLatFn_transfer {D : D7} {n : ℕ} {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ)
    (emb : D.what₂.Tau → D.host.E →+* K) (lam : D.what₂.Tau → Formalism.BasicNotions.DomWeight n) {O O' : Subring ℂ} (hOO : O ≤ O')
    {M M' : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (N : ℕ) (hN : N ≠ 0) (hinv : ((N : ℂ))⁻¹ ∈ O')
    (hF : ∀ F ∈ Formalism.L2.DIV.nabAtr emb lam M, (N : K) • F ∈ Formalism.L2.DIV.nabAtr emb lam M')
    {φ : GLR D n → ℂ} (hφ : φ ∈ coefLatFn σ emb O lam M) : φ ∈ coefLatFn σ emb O' lam M' := by
  induction hφ using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨F, hFm, rfl⟩ := h
    have h1 : coefFn σ lam (((N : K) • F : Formalism.L2.DIV.VV K lam) : Formalism.L2.DIV.Pol K D.what₂.Tau n) ∈ coefLatFn σ emb O' lam M' :=
      Submodule.subset_span ⟨_, hF F hFm, rfl⟩
    have h2 := Submodule.smul_mem _ (⟨_, hinv⟩ : O') h1
    convert h2 using 1
    funext x
    have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN
    change _ = (N : ℂ)⁻¹ * _
    rw [Submodule.coe_smul, coefFn_natCast_smul, inv_mul_cancel_left₀ hN']
  | zero => exact zero_mem _
  | add _ _ _ _ h1 h2 => exact add_mem h1 h2
  | smul c _ _ h1 => exact Submodule.smul_mem _ (⟨c, hOO c.2⟩ : O') h1

theorem normProd_ne_zero {D : D7} (Q : Finset (Pl D.host.E)) : normProd Q ≠ 0 := by
  unfold normProd
  refine Finset.prod_ne_zero_iff.2 fun v _ => ?_
  rw [Ne, Ideal.absNorm_eq_zero_iff]
  exact v.ne_bot


set_option maxHeartbeats 800000 in
theorem lat_translate : ∀ (D : D7) (ρ : Setup D.ntw), ρ.Good → ∀ (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool), ∀ k (Q : Finset (Pl D.host.E)) (h hQ : GA D (Vc D j)) P, SplitSet Q → Disjoint Q (D.ntw.S0 i) → h ∈ GfC (Vc D j) → SuppAt (idem Q) (Vc D j) hQ → P ∈ ρ.lat i j b (ρ.eO i b).range h → P ∈ ρ.lat i j b (ρ.eOk i b k).range (h * hQ) := by
  intro D ρ hρ i j b k Q h hQ P hS hD hh hsupp hP
  unfold GlobalTheory.SeriesTie.Setup.lat GlobalTheory.ExportSeries.Base.coefLat at *
  rw [GlobalTheory.ExportSeries.mem_harmLat] at *
  refine ⟨hP.1, ?_⟩
  obtain ⟨c, h1, h2⟩ := GlobalTheory.T.splitPlaces_translation_lattice_bounded_norm D ρ hρ i j b Q h hQ hS hsupp
  have hN0 : normProd Q ^ c ≠ 0 := pow_ne_zero _ (normProd_ne_zero Q)
  obtain ⟨a, ha⟩ := GlobalTheory.T.dualWeylLattice_exists_natPow_smul_mem _ _ _ _ (labLL0 D) (ρ.B i j b).w.lam _ _ (normProd Q ^ c) hN0 (by first | exact GlobalTheory.LatFull.latAt_isFullLattice D ρ hρ i j b h | exact (GlobalTheory.LatFull.latAt_isFullLattice D ρ hρ i j b h).toIsLattice)
    (by first | exact GlobalTheory.LatFull.latAt_isFullLattice D ρ hρ i j b (h * hQ) | exact (GlobalTheory.LatFull.latAt_isFullLattice D ρ hρ i j b (h * hQ)).toIsLattice) h1 h2
  have hu : ((normProd Q : ℕ) : ℂ)⁻¹ ∈ (ρ.eOk i b k).range := hρ.range_le i b k (GlobalTheory.T.inv_place_norm_product_mem_coefficient_ring D ρ i b Q hD)
  have hinv : (((normProd Q ^ c) ^ a : ℕ) : ℂ)⁻¹ ∈ (ρ.eOk i b k).range := by
    rw [Nat.cast_pow, Nat.cast_pow, ← inv_pow, ← inv_pow]
    exact Subring.pow_mem _ (Subring.pow_mem _ hu _) _
  have hF : ∀ F ∈ Formalism.L2.DIV.nabAtr (labLL0 D) (ρ.B i j b).w.lam ((ρ.B i j b).latAt (finPt (Vc D j) h)),
      (((normProd Q ^ c) ^ a : ℕ) : ↥D.LL0) • F ∈
        Formalism.L2.DIV.nabAtr (labLL0 D) (ρ.B i j b).w.lam ((ρ.B i j b).latAt (finPt (Vc D j) (h * hQ))) := by
    intro F hF
    have := ha F hF
    rwa [Nat.cast_pow (α := ↥D.LL0) (normProd Q ^ c) a]
  exact coefLatFn_transfer (Formalism.L2.Host.embLL0 D) (labLL0 D) (ρ.B i j b).w.lam (hρ.range_le i b k)
    ((normProd Q ^ c) ^ a) (pow_ne_zero _ hN0) hinv hF hP.2

end GlobalTheory.LatTranslate

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefLatLeTranslateSplitPlacesPrimeToLStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefLat_le_translate_splitPlaces_prime_to_l : ∀ (D : D7) (ρ : Setup D.ntw), ρ.Good → ∀ (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool), ∀ k (Q : Finset (Pl D.host.E)) (h hQ : GA D (Vc D j)) P, SplitSet Q → Disjoint Q (D.ntw.S0 i) → h ∈ GfC (Vc D j) → SuppAt (idem Q) (Vc D j) hQ → P ∈ ρ.lat i j b (ρ.eO i b).range h → P ∈ ρ.lat i j b (ρ.eOk i b k).range (h * hQ) := by
  first | exact @GlobalTheory.LatTranslate.lat_translate | exact GlobalTheory.LatTranslate.lat_translate | (intros; apply GlobalTheory.LatTranslate.lat_translate <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqConstMulOfNormOne
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverConst

theorem eq_const_mul_of_norm_one : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {ι : Type*} (U : Set V), IsOpen U → IsPreconnected U → ∀ (P₂ P : ι → V → ℂ) (g : V → ℂ), (∀ i, DifferentiableOn ℂ (P₂ i) U) → (∀ i, DifferentiableOn ℂ (P i) U) → (∀ x ∈ U, ‖g x‖ = 1) → (∀ i, ∀ x ∈ U, P₂ i x = g x * P i x) → ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ i, ∀ x ∈ U, P₂ i x = u * P i x := by
  intro V _ _ ι U hU hc P₂ P g hP₂ hP hg1 hg
  by_cases h : ∃ i, ∃ x ∈ U, P i x ≠ 0
  swap
  · push_neg at h
    refine ⟨1, by simp, fun i x hx => ?_⟩
    rw [hg i x hx, h i x hx]
    simp
  obtain ⟨i₀, x₀, hx₀, hne⟩ := h
  have hcont : ContinuousAt (P i₀) x₀ := (hP i₀).continuousOn.continuousAt (hU.mem_nhds hx₀)
  have hnb : ∀ᶠ y in nhds x₀, y ∈ U ∧ P i₀ y ≠ 0 := (hU.eventually_mem hx₀).and (hcont.eventually_ne hne)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hnb
  have hx₀b : x₀ ∈ Metric.ball x₀ ε := Metric.mem_ball_self hε
  let q : V → ℂ := fun y => P₂ i₀ y * (P i₀ y)⁻¹
  have hqd : DifferentiableOn ℂ q (Metric.ball x₀ ε) :=
    ((hP₂ i₀).mono (fun y hy => (hball y hy).1)).mul (((hP i₀).mono (fun y hy => (hball y hy).1)).inv
      (fun y hy => (hball y hy).2))
  have hqg : ∀ y ∈ Metric.ball x₀ ε, q y = g y := fun y hy => by
    simp only [q]
    rw [hg i₀ y (hball y hy).1, mul_assoc, mul_inv_cancel₀ (hball y hy).2, mul_one]
  have hmax : IsMaxOn (norm ∘ q) (Metric.ball x₀ ε) x₀ := fun y hy => by
    simp only [Set.mem_setOf_eq, Function.comp_apply]
    rw [hqg y hy, hqg x₀ hx₀b, hg1 _ (hball y hy).1, hg1 _ (hball x₀ hx₀b).1]
  have heq := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm (convex_ball x₀ ε).isPreconnected
    Metric.isOpen_ball hqd hx₀b hmax
  refine ⟨g x₀, hg1 x₀ hx₀, fun i => ?_⟩
  have hzero : ∀ y ∈ U, (fun y => P₂ i y - g x₀ * P i y) y = 0 := by
    refine ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.eq_zero_of_eventually hU hc ((hP₂ i).sub ((hP i).const_mul (g x₀))) hx₀ ?_
    filter_upwards [Metric.ball_mem_nhds x₀ hε] with y hy
    have e : g y = g x₀ := by
      rw [← hqg y hy, ← hqg x₀ hx₀b]
      exact heq hy
    simp only [Pi.zero_apply]
    rw [hg i y (hball y hy).1, e]
    ring
  intro x hx
  have := hzero x hx
  simp only at this
  exact sub_eq_zero.1 this

theorem psi_and_weight_eq : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ (k₂ : C.U₂.Comp) (k : (T.U j σ).Comp), (∀ τ : D.host.E →+* ℂ, τ ∈ (C.U₂.X k₂).Ψ ↔ τ ∈ ((T.U j σ).X k).Ψ) ∧ ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X k₂).Ψ) (h₁ : τ ∈ ((T.U j σ).X k).Ψ) (i : Fin D.R.r), laU C.U₂ a n k₂ ⟨τ, h₂⟩ i = laU (T.U j σ) a n k ⟨τ, h₁⟩ i := by
  intro D T hL j hj σ hσ C hC k₂ k
  have hU₂ : IsUnf C.U₂ := hC.2.2.2.1
  have hU₁ : IsUnf (T.U j σ) := hL.unf j hj σ hσ
  have hrel : relab C.d.c₂ C.σ₂ = relab T.Q.c σ := by
    funext τ
    ext x
    have e := congrArg (fun φ : T.Q.c.F →+* ℂ => φ (embF T.Q.c τ x)) hC.2.2.1
    simp only [RingHom.comp_apply] at e
    show C.σ₂ (embF C.d.c₂ τ x) = σ (embF T.Q.c τ x)
    rw [← e]
    congr 1
  refine ⟨fun τ => by rw [(hU₂.2.1 k₂).2 τ, (hU₁.2.1 k).2 τ], fun a n τ h₂ h₁ i => ?_⟩
  unfold laU
  rw [(hU₂.2.1 k₂).1, (hU₁.2.1 k).1, hrel]

theorem cover_scalar_const : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ n : ℕ, ∀ k₂ : C.U₂.Comp, ∃ (k : (T.U j σ).Comp) (γ : GL (Fin D.R.r) D.host.E), (((T.U j σ).X k).Λ : Set (Fin D.R.r → D.host.E)) = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec '' ((C.U₂.X k₂).Λ : Set _) ∧ (∀ v w, herm ((T.U j σ).X k).Gm ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm (C.U₂.X k₂).Gm v w) ∧ (∀ h, (C.dict₂ h).1 = k₂ → (T.dict j σ h).1 = k) ∧ ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ (x : Frame (C.U₂.X k₂).Ψ D.R.r) (x' : Frame ((T.U j σ).X k).Ψ D.R.r), x ∈ (C.U₂.X k₂).dom → (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X k₂).Ψ) (h₁ : τ ∈ ((T.U j σ).X k).Ψ), mat x' ⟨τ, h₁⟩ = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat x ⟨τ, h₂⟩) → x' ∈ ((T.U j σ).X k).dom ∧ ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ), Dom a n → ∀ f ∈ sec (T.Q.Xo j) T.Q.c a n, ∀ f₂ ∈ sec C.d.Xo₂ C.d.c₂ a n, C.IsPull f f₂ → rdU C.U₂ f₂ k₂ x = u * rdU (T.U j σ) f k x' := by
  intro D T hL j hj σ hσ C hC n k₂
  obtain ⟨k, γ, hΛ, hh, hd, hx⟩ := GlobalTheory.T.levelCover_component_readings_unit_modulus_scalar D T hL j hj σ hσ C hC k₂
  obtain ⟨hΨ, hla⟩ := psi_and_weight_eq D T hL j hj σ hσ C hC k₂ k
  refine ⟨k, γ, hΛ, hh, hd, ?_⟩
  have hU₂ : IsUnf C.U₂ := hC.2.2.2.1
  have hU₁ : IsUnf (T.U j σ) := hL.unf j hj σ hσ

  let G : Frame (C.U₂.X k₂).Ψ D.R.r → Frame ((T.U j σ).X k).Ψ D.R.r := fun x τ =>
    ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1 * mat x ⟨τ.1, (hΨ τ.1).2 τ.2⟩ : Matrix (Fin D.R.r) (Fin D.R.r) ℂ)
  have hGrel : ∀ x (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X k₂).Ψ) (h₁ : τ ∈ ((T.U j σ).X k).Ψ),
      mat (G x) ⟨τ, h₁⟩ = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat x ⟨τ, h₂⟩ := by
    intro x τ h₂ h₁
    rfl
  have hGdom : ∀ x ∈ (C.U₂.X k₂).dom, G x ∈ ((T.U j σ).X k).dom := fun x hx' => (hx x (G x) hx' (hGrel x)).1
  have hGdiff : Differentiable ℂ G := by
    refine differentiable_pi.2 fun τ => differentiable_pi.2 fun a => differentiable_pi.2 fun b => ?_
    simp only [G, mat, Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply]
    fun_prop

  let ι := {p : ((D.host.E →+* ℂ) × ℕ → ℕ) × Rul (T.Q.Xo j) T.Q.c × Rul C.d.Xo₂ C.d.c₂ //
    Dom p.1 n ∧ p.2.1 ∈ sec (T.Q.Xo j) T.Q.c p.1 n ∧ p.2.2 ∈ sec C.d.Xo₂ C.d.c₂ p.1 n ∧ C.IsPull p.2.1 p.2.2}
  let P₂ : ι → Frame (C.U₂.X k₂).Ψ D.R.r → ℂ := fun i => rdU C.U₂ i.1.2.2 k₂
  let P : ι → Frame (C.U₂.X k₂).Ψ D.R.r → ℂ := fun i x => rdU (T.U j σ) i.1.2.1 k (G x)
  have hP₂d : ∀ i, DifferentiableOn ℂ (P₂ i) (C.U₂.X k₂).dom := fun i =>
    (hU₂.2.2.2.2.1 i.1.1 n i.2.1 i.1.2.2 i.2.2.2.1 k₂).1
  have hPd : ∀ i, DifferentiableOn ℂ (P i) (C.U₂.X k₂).dom := fun i =>
    (hU₁.2.2.2.2.1 i.1.1 n i.2.1 i.1.2.1 i.2.2.1 k).1.comp hGdiff.differentiableOn hGdom
  have hg : ∀ x ∈ (C.U₂.X k₂).dom, ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ i : ι, P₂ i x = c * P i x := by
    intro x hxd
    obtain ⟨b, hb, hyd, hyo⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.exists_borel_orthonormal_move (C.U₂.X k₂) hxd
    obtain ⟨-, t, -, hmod, hrel⟩ := hx (rmul x b) (G (rmul x b)) hyd (hGrel _)
    have ht1 : ‖t‖ = 1 := hmod (fun τ i => ReciprocityTheory.ChartRestriction.G.PullbackSections.norm_diagonal_minor_one _ hyo τ i)
    refine ⟨t ^ n, by rw [norm_pow, ht1, one_pow], ?_⟩
    rintro ⟨⟨a, f, f₂⟩, hDom, hf, hf₂, hP⟩
    let b₁ : Frame ((T.U j σ).X k).Ψ D.R.r := fun τ => b ⟨τ.1, (hΨ τ.1).2 τ.2⟩
    have hb₁ : b₁ ∈ Bor ((T.U j σ).X k).Ψ D.R.r := fun τ => hb ⟨τ.1, (hΨ τ.1).2 τ.2⟩
    have e1 := hrel n a hDom f hf f₂ hf₂ hP
    have e2 : rdU C.U₂ f₂ k₂ (rmul x b) = bchar (laU C.U₂ a n k₂) b * rdU C.U₂ f₂ k₂ x :=
      (hU₂.2.2.2.2.1 a n hDom f₂ hf₂ k₂).2.1 x hxd b hb
    have e3 : G (rmul x b) = rmul (G x) b₁ := by
      funext τ
      simp only [G, rmul, b₁, mat]
      exact (Matrix.mul_assoc ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1) (mat x ⟨τ.1, (hΨ τ.1).2 τ.2⟩) (mat b ⟨τ.1, (hΨ τ.1).2 τ.2⟩)).symm
    have e4 : rdU (T.U j σ) f k (rmul (G x) b₁) = bchar (laU (T.U j σ) a n k) b₁ * rdU (T.U j σ) f k (G x) :=
      (hU₁.2.2.2.2.1 a n hDom f hf k).2.1 (G x) (hGdom x hxd) b₁ hb₁
    have e5 : bchar (laU C.U₂ a n k₂) b = bchar (laU (T.U j σ) a n k) b₁ := by
      unfold bchar
      refine Fintype.prod_equiv (Equiv.subtypeEquivRight (fun τ => hΨ τ)) _ _ (fun τ => ?_)
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [hla a n τ.1 τ.2 ((hΨ τ.1).1 τ.2) i]
      rfl
    have e6 : bchar (laU C.U₂ a n k₂) b ≠ 0 := by
      unfold bchar
      refine Finset.prod_ne_zero_iff.2 fun τ _ => Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ ?_
      have hdet : (mat b τ).det ≠ 0 := (hb τ).1
      rw [Matrix.det_of_upperTriangular (M := mat b τ) (fun a c h => (hb τ).2 a c h)] at hdet
      simpa [mat] using Finset.prod_ne_zero_iff.1 hdet i (Finset.mem_univ _)
    show rdU C.U₂ f₂ k₂ x = t ^ n * rdU (T.U j σ) f k (G x)
    apply mul_left_cancel₀ e6
    rw [← e2, e1, e3, e4, ← e5]
    ring
  classical
  let g : Frame (C.U₂.X k₂).Ψ D.R.r → ℂ := fun x => if h : x ∈ (C.U₂.X k₂).dom then (hg x h).choose else 1
  have hg1 : ∀ x ∈ (C.U₂.X k₂).dom, ‖g x‖ = 1 := fun x h => by
    simp only [g, dif_pos h]; exact (hg x h).choose_spec.1
  have hgr : ∀ i, ∀ x ∈ (C.U₂.X k₂).dom, P₂ i x = g x * P i x := fun i x h => by
    simp only [g, dif_pos h]; exact (hg x h).choose_spec.2 i
  obtain ⟨u, hu1, hu⟩ := eq_const_mul_of_norm_one (C.U₂.X k₂).dom (ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain.isOpen_dom _)
    (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.flag_domain_frames_connected D.R.r (C.U₂.X k₂)).isPreconnected P₂ P g hP₂d hPd hg1 hgr
  refine ⟨u, hu1, fun x x' hxd hrel' => ⟨(hx x x' hxd hrel').1, ?_⟩⟩
  have hx' : x' = G x := by
    funext τ
    exact hrel' τ.1 ((hΨ τ.1).2 τ.2) τ.2
  intro a hDom f hf f₂ hf₂ hP
  rw [hx']
  exact hu ⟨(a, f, f₂), hDom, hf, hf₂, hP⟩ x hxd

end GlobalTheory.CoverConst
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockVacuumPairingPolynomialTranslatesScalar
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockVacuumPairingPolynomialTranslatesScalar
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.VacPairSchur

set_option synthInstance.maxHeartbeats 400000 in
theorem actO_fin : ∀ (D : D7) (S T : HSp D) (u : GA D T), u ∈ GinfC T → ∀ w : WO S T, w.map (infPart D) = 0 → actO S T 1 u w = w := by
  intro D S T u hu w hw
  have hf : (Formalism.L2.Theta.mt T u).map (finPart D) = 1 := by
    have h := congrArg (fun g : GL (Fin T.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) => g.val)
      (MonoidHom.mem_ker.1 hu)
    exact h
  have hm : Formalism.L2.Theta.mt S 1 = 1 := by simp [Formalism.L2.Theta.mt]
  unfold actO
  rw [inv_one, hm, Matrix.mul_one]
  ext i j
  refine GlobalTheory.UnitarySplit.parts_inj D _ _ ?_ ?_
  · have h0 : ∀ k, infPart D (w k j) = 0 := fun k => by
      have := congrFun (congrFun hw k) j
      simpa using this
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.mul_apply, map_sum]
    simp [h0]
  · have h1 : ∀ k, finPart D (Formalism.L2.Theta.mt T u i k) = if i = k then 1 else 0 := fun k => by
      have := congrFun (congrFun hf i) k
      simpa [Matrix.one_apply] using this
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.mul_apply, map_sum]
    simp [h1]

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem pT_heisO (hθ : IsInfFam θ) (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO S T → ℂ) {w : WO S T}
    (hw : w.map (infPart D) = 0) (P : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    pureTensorO ψ θ S T sS sT BS BT (heisO ψ S T w f) P = heisO ψ S T w (pureTensorO ψ θ S T sS sT BS BT f P) := by
  have h := (GlobalTheory.OrientedHeis.pureTensorL_intertwine (fun _ => True) trivial (fun _ _ _ _ => trivial)
    (fun _ _ _ => trivial) (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT)
    (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT) (GlobalTheory.Hk3.FiniteHeis.heisLin ψ S T w)
    (fun k g _ => ⟨trivial, ?_⟩) f trivial P).2
  · exact h.symm
  · obtain ⟨τ, i, j⟩ := k
    simp only [aPlusAll, aPlus, crea]
    rw [map_smul, map_sub, map_smul]
    show _ • (heisO ψ S T w (Formalism.IndefR.Datum.dRho _ _ _ _ _) - _ • heisO ψ S T w (Formalism.IndefR.Datum.dRho _ _ _ _ _)) = _
    rw [GlobalTheory.Hk3.FiniteHeis.heisO_dRho ψ hθ hw, GlobalTheory.Hk3.FiniteHeis.heisO_dRho ψ hθ hw]
    rfl

theorem thetaIP_eq_ipO (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) (f g : WO S T → ℂ) :
    thetaIP μ 𝓕 f g = GlobalTheory.Ker.ipO μ 𝓕 g f := by
  unfold thetaIP GlobalTheory.Ker.ipO
  congr 1
  funext w
  rw [mul_comm]
  rfl

theorem thetaInner_heisenberg (hψ : IsStdChar D ψ (-1)) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}
    (hcv : IsCovolOne (ratL T S) μ 𝓕) {a b : WO S T → ℂ} (ha : IsThetaFunO ψ S T a) (hb : IsThetaFunO ψ S T b)
    (w : WO S T) : thetaIP μ 𝓕 (heisO ψ S T w a) (heisO ψ S T w b) = thetaIP μ 𝓕 a b := by
  rw [thetaIP_eq_ipO, thetaIP_eq_ipO, GlobalTheory.Size.ipO_heisO hψ hcv.1 hcv.2.1 hb ha]

theorem om_heisO_fin {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hom : IsWeilDatumO ψ S T χS χT om) {u : GA D T} (hu : u ∈ GinfC T) {w : WO S T} (hw : w.map (infPart D) = 0)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    om (1, u) (heisO ψ S T w f) = heisO ψ S T w (om (1, u) f) := by
  rw [hom.om_heis 1 u w f hf, actO_fin D S T u hu w hw]

theorem pT_lin (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (a : ℂ) {f f' : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (hf' : IsThetaFunO ψ S T f') (P : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    pureTensorO ψ θ S T sS sT BS BT (a • f + f') P =
      a • pureTensorO ψ θ S T sS sT BS BT f P + pureTensorO ψ θ S T sS sT BS BT f' P :=
  GlobalTheory.VacCoefAtPlace.pure_lin (P := IsThetaFunO ψ S T) (fun _ _ h => GlobalTheory.FockIndep.aPlus_theta hψ hθ _ _ _ h)
    (fun _ b _ _ h h' => by
      simp only [aPlusAll]
      rw [GlobalTheory.FockIndep.aPlus_add hψ hθ _ _ _ (GlobalTheory.OrientedHeis.theta_smul b h) h',
        GlobalTheory.FockIndep.aPlus_smul hψ hθ _ _ _ b h]) a hf hf' P

theorem onb_min {k : ℕ} {G s B : Matrix (Fin k) (Fin k) ℂ} {p : ℕ} (h : IsONBasis G s B p) :
    IsONBasis G s B (min p k) := by
  obtain ⟨ε, h1, h2, h3⟩ := h
  refine ⟨ε, fun a => ?_, h2, h3⟩
  rcases h1 a with ⟨e, ha⟩ | ⟨e, ha⟩
  · exact Or.inl ⟨e, lt_min ha a.2⟩
  · exact Or.inr ⟨e, (min_le_left _ _).trans ha⟩

theorem cs (hψ : IsStdChar D ψ (-1)) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}
    (hcv : IsCovolOne (ratL T S) μ 𝓕) {a b : WO S T → ℂ} (ha : IsThetaFunO ψ S T a) (hb : IsThetaFunO ψ S T b) :
    ‖thetaIP μ 𝓕 a b‖ ^ 2 ≤ (thetaIP μ 𝓕 a a).re * (thetaIP μ 𝓕 b b).re := by
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  have ii : ∀ {c : WO S T → ℂ}, IsThetaFunO ψ S T c → Integrable (fun x => star (c x) * c x) (μ.restrict 𝓕) :=
    fun {c} hc => (GlobalTheory.Size.integrableOn_mul_conj hψ hcv.1 hcv.2.1 hc hc).congr
      (ae_of_all _ fun x => mul_comm _ _)
  exact GlobalTheory.norm_integral_star_mul_sq_le (μ.restrict 𝓕) a b ha.cont.aestronglyMeasurable
    hb.cont.aestronglyMeasurable (ii ha) (ii hb)

theorem pair_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (pS pT : D.what₂.Tau → ℕ), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → (∀ τ, IsONBasis (gramAt D S τ) (sS τ) (BS τ) (pS τ)) → (∀ τ, IsONBasis (gramAt D T τ) (sT τ) (BT τ) (pT τ)) → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ u ∈ GinfC T, ∀ P P' : MvPolynomial (FVar D T.rank S.rank) ℂ, ∃ c : ℂ, ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g) → thetaIP μ 𝓕 (om (1, u) (pureTensorO ψ θ S T sS sT BS BT f P)) (pureTensorO ψ θ S T sS sT BS BT g P') = c * thetaIP μ 𝓕 f g := by
  intro D ψ θ S T χS χT om hom hθ sS BS sT BT pS pT hcS hcT hoS hoT μ 𝓕 hcv u hu P P'
  have hψ := hom.std
  have hμ := hcv.1
  have h𝓕 := hcv.2.1
  have thp : ∀ f, IsThetaFunO ψ S T f → ∀ Q, IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f Q) :=
    fun f hf Q => GlobalTheory.Chain.InnerSteps.theta_pureTensorO hψ hθ sS BS sT BT hf Q
  have thom : ∀ f, IsThetaFunO ψ S T f → ∀ Q,
      IsThetaFunO ψ S T (om (1, u) (pureTensorO ψ θ S T sS sT BS BT f Q)) :=
    fun f hf Q => hom.om_pres _ _ (thp f hf Q)
  have key : ∀ f, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → ∀ Q,
      thetaIP μ 𝓕 (pureTensorO ψ θ S T sS sT BS BT f Q) (pureTensorO ψ θ S T sS sT BS BT f Q) =
        GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockIp Q Q * (nrm2 μ 𝓕 f : ℂ) := by
    intro f hf vf Q
    rw [thetaIP_eq_ipO]
    exact GlobalTheory.FockIsometry.ipO_pureTensorO D ψ θ S T hψ hθ sS BS sT BT (fun τ => min (pS τ) S.rank)
      (fun τ => min (pT τ) T.rank) (fun τ => min_le_right _ _) (fun τ => min_le_right _ _) hcS hcT
      (fun τ => onb_min (hoS τ)) (fun τ => onb_min (hoT τ)) f hf vf μ 𝓕 hcv Q Q
  set Φ : (WO S T → ℂ) → (WO S T → ℂ) → ℂ := fun f g =>
    thetaIP μ 𝓕 (om (1, u) (pureTensorO ψ θ S T sS sT BS BT f P)) (pureTensorO ψ θ S T sS sT BS BT g P') with hΦ
  have hl : ∀ (a : ℂ) (f f' g : WO S T → ℂ), IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → IsThetaFunO ψ S T g →
      (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f') → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g) → Φ (a • f + f') g = star a * Φ f g + Φ f' g := by
    intro a f f' g hf hf' hg _ _ _
    simp only [hΦ]
    rw [pT_lin hψ hθ sS BS sT BT a hf hf' P, map_add (f := _), map_smul, thetaIP_eq_ipO, thetaIP_eq_ipO, thetaIP_eq_ipO,
      GlobalTheory.Size.ipO_add_right hψ hμ h𝓕 (thp g hg P') (GlobalTheory.OrientedHeis.theta_smul a (thom f hf P)) (thom f' hf' P),
      GlobalTheory.Size.ipO_smul_right]
    rfl
  have hr : ∀ (a : ℂ) (f g g' : WO S T → ℂ), IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' →
      (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g) → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g') → Φ f (a • g + g') = a * Φ f g + Φ f g' := by
    intro a f g g' hf hg hg' _ _ _
    simp only [hΦ]
    rw [pT_lin hψ hθ sS BS sT BT a hg hg' P', thetaIP_eq_ipO, thetaIP_eq_ipO, thetaIP_eq_ipO,
      GlobalTheory.Size.ipO_add_left hψ hμ h𝓕 (GlobalTheory.OrientedHeis.theta_smul a (thp g hg P')) (thp g' hg' P') (thom f hf P),
      GlobalTheory.Size.ipO_smul_left]
  have hb : ∃ C : ℝ, ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g) →
      ‖Φ f g‖ ^ 2 ≤ C * (nrm2 μ 𝓕 f * nrm2 μ 𝓕 g) := by
    refine ⟨(GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockIp P P).re * (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockIp P' P').re, fun f g hf hg vf vg => ?_⟩
    simp only [hΦ]
    have h1 := cs hψ hcv (thom f hf P) (thp g hg P')
    rw [GlobalTheory.WeilPairing.thetaInner_weilRep D ψ S T χS χT om μ 𝓕 hom hcv _ _ _ (thp f hf P) (thp f hf P),
      key f hf vf P, key g hg vg P', Complex.re_mul_ofReal, Complex.re_mul_ofReal] at h1
    linarith
  have hi : ∀ w : WO S T, w.map (infPart D) = 0 → ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g →
      (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g) → Φ (heisO ψ S T w f) (heisO ψ S T w g) = Φ f g := by
    intro w hw f g hf hg _ _
    simp only [hΦ]
    rw [pT_heisO hθ sS BS sT BT f hw, pT_heisO hθ sS BS sT BT g hw, om_heisO_fin hom hu hw (thp f hf P),
      thetaInner_heisenberg hψ hcv (thom f hf P) (thp g hg P')]
  exact GlobalTheory.T.schur_finiteHeisenberg_fockVacuumThetaFunctions D ψ θ S T hψ hθ sS sT hcS hcT μ 𝓕 hcv Φ hl hr hb hi

end GlobalTheory.VacPairSchur
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockVacuumPairingPolynomialTranslatesScalarStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVacuum_pairing_polynomial_translates_scalar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (pS pT : D.what₂.Tau → ℕ), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → (∀ τ, IsONBasis (gramAt D S τ) (sS τ) (BS τ) (pS τ)) → (∀ τ, IsONBasis (gramAt D T τ) (sT τ) (BT τ) (pT τ)) → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ u ∈ GinfC T, ∀ P P' : MvPolynomial (FVar D T.rank S.rank) ℂ, ∃ c : ℂ, ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g) → thetaIP μ 𝓕 (om (1, u) (pureTensorO ψ θ S T sS sT BS BT f P)) (pureTensorO ψ θ S T sS sT BS BT g P') = c * thetaIP μ 𝓕 f g := by
  first | exact @GlobalTheory.VacPairSchur.pair_eq | exact GlobalTheory.VacPairSchur.pair_eq | (intros; apply GlobalTheory.VacPairSchur.pair_eq <;> assumption)
end
end
