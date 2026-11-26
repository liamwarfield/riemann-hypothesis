module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleTwistOfTwistingCharacter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DownwardThetaLiftPreservesGood
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaSeriesIntegralSourceTranslationRightMul
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KeepSideBMtVPlaces
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharInfinityEqCoeffMulHalfNormPow

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedSeriesSpecialisedUniversalDatumMemSpan
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidueCharacterTwistUniversalCharAtChosenPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidueCharacterTwistUniversalCharAtChosenPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.ResTwist

theorem res_twist_spec : ∀ {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (ρ : Setup X), ρ.Good →
  ∀ (Y : NExp D.R D.host D.what₂ D.LL0 N X), GlobalTheory.UnivChar.IsUnivChar Y →
  ∀ (i : X.Tw) (b : Bool) (k : ℕ) (Q : Finset (Pl D.host.E)) (M : ℕ)
    (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ),
    TwOK i k Q (χ.comp (Y.delU i Q M)) →
    ∀ (PP : ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M))) (x : (kP PP.1)ˣ),
      (((ρ.tw i b k Q (χ.comp (Y.delU i Q M))).resC PP.1 x : ℂˣ) : ℂ) =
        ρ.eOk i b k ((χ (Multiplicative.ofAdd (spread Y i Q M (ρ.ch i)
          (Pi.single PP (Multiplicative.toAdd ((univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).kap PP.1 x))))) : (X.Ok i k)ˣ) : X.Ok i k) := by
  intro D N X ρ hρ Y hY i b k Q M χ hT PP x
  let χc : Multiplicative (↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) → ZMod (X.l i ^ M)) →* Circle :=
    unitPart.comp ((Units.map (ρ.eOk i b k).toMonoidHom).comp (χ.comp (AddMonoidHom.toMultiplicative (spread Y i Q M (ρ.ch i)))))
  have hgood := GlobalTheory.UnivGood.univOf_good D N X ρ hρ Y i Q M

  have hchar : charOf ρ.rc (ρ.eOk i b k) (χ.comp (Y.delU i Q M)) = χc.comp ((univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).delQ (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M))) := by
    ext1 y
    obtain ⟨σ, hσ⟩ := ρ.rc.exists_sym y
    have hψ : IsOpen ((χ.comp (Y.delU i Q M)).ker : Set (G D.host.E N.Om)) :=
      Subgroup.isOpen_mono (H₁ := (Y.delU i Q M).ker) (fun g hg => by simp [MonoidHom.mem_ker.1 hg]) (Y.delU_open i Q M)
    have hco : ∀ P : Pl D.host.E, IsOpen ((coord Y i (admissibleConjugatePairPlaces X i Q M) M P).ker : Set (G D.host.E N.Om)) := by
      intro P
      by_cases hP : P ∈ admissibleConjugatePairPlaces X i Q M
      · refine Subgroup.isOpen_mono (H₁ := (Y.delU i (admissibleConjugatePairPlaces X i Q M) M).ker) (fun g hg => ?_) (Y.delU_open i (admissibleConjugatePairPlaces X i Q M) M)
        refine MonoidHom.mem_ker.2 (Multiplicative.toAdd.injective ?_)
        rw [coord_apply Y i (admissibleConjugatePairPlaces X i Q M) M hP, MonoidHom.mem_ker.1 hg]
        rfl
      · rw [coord, dite_eq_right hP]
        simp
    have e1 : (univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).delQ (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) y = Multiplicative.ofAdd fun P : ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) => Multiplicative.toAdd (coord Y i (admissibleConjugatePairPlaces X i Q M) M P.1 σ) := by
      change Multiplicative.ofAdd (fun PP : ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) => Multiplicative.toAdd (ρ.rc.pull (coord Y i (admissibleConjugatePairPlaces X i Q M) M PP.1) y)) = _
      congr 1
      funext P
      exact congrArg Multiplicative.toAdd (ρ.rc.pull_eq (hco P.1) hσ)
    have e2 : Y.delU i Q M σ = AddMonoidHom.toMultiplicative (spread Y i Q M (ρ.ch i))
        (Multiplicative.ofAdd fun P : ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) => Multiplicative.toAdd (coord Y i (admissibleConjugatePairPlaces X i Q M) M P.1 σ)) :=
      Multiplicative.toAdd.injective (delU_eq_spread hY (twSet_of_twOK hT) (hρ.ch i) σ)
    simp only [charOf, MonoidHom.comp_apply]
    rw [ρ.rc.pull_eq hψ hσ, e1, MonoidHom.comp_apply, e2]
    rfl
  have hspec := GlobalTheory.ExportSeries.SpecGood.spec_good D (ZMod (X.l i ^ M)) Circle (univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc) (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) χc hgood
  have hres : IsResAt (χc.comp ((univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).delQ (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)))) PP.1 (((univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).spec (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) χc).res PP.1) := hspec.res PP.1 PP.2
  have hidem := hgood.1.isIdemAt PP.2
  have htres : (ρ.tw i b k Q (χ.comp (Y.delU i Q M))).res PP.1 = ((univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).spec (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) χc).res PP.1 := by
    change resOf (charOf ρ.rc (ρ.eOk i b k) (χ.comp (Y.delU i Q M))) PP.1 = _
    rw [hchar]
    exact GlobalTheory.ConjTwist.isResAt_unique hidem (isResAt_resOf ⟨_, hres⟩) hres
  have hs : ((univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).spec (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) χc).res PP.1 = χc.comp ((AddMonoidHom.toMultiplicative
      (AddMonoidHom.single (fun _ : ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) => ZMod (X.l i ^ M)) ⟨PP.1, PP.2⟩)).comp ((univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).kap PP.1)) := dif_pos PP.2
  have hz : ∀ z : Multiplicative (DelQM D.host (X.l i) Q M), z ^ (X.l i ^ M) = 1 := by
    intro z
    rw [← ofAdd_toAdd z, ← ofAdd_nsmul]
    refine congrArg Multiplicative.ofAdd (funext fun v => ?_)
    simp [nsmul_eq_mul, ZMod.natCast_self]
  change (((ρ.tw i b k Q (χ.comp (Y.delU i Q M))).res PP.1 x : Circle) : ℂ) = _
  rw [htres, hs]
  simp only [χc, MonoidHom.comp_apply]
  rw [unitPart_of_pow (n := X.l i ^ M) (pow_ne_zero _ (X.lPrime i).out.ne_zero)
    (by rw [← map_pow, ← map_pow, hz, map_one, map_one])]
  rfl

end GlobalTheory.ResTwist
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidueCharacterTwistUniversalCharAtChosenPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residueCharacter_twist_universalChar_at_chosen_place : ∀ {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (ρ : Setup X), ρ.Good →
  ∀ (Y : NExp D.R D.host D.what₂ D.LL0 N X), GlobalTheory.UnivChar.IsUnivChar Y →
  ∀ (i : X.Tw) (b : Bool) (k : ℕ) (Q : Finset (Pl D.host.E)) (M : ℕ)
    (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ),
    TwOK i k Q (χ.comp (Y.delU i Q M)) →
    ∀ (PP : ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M))) (x : (kP PP.1)ˣ),
      (((ρ.tw i b k Q (χ.comp (Y.delU i Q M))).resC PP.1 x : ℂˣ) : ℂ) =
        ρ.eOk i b k ((χ (Multiplicative.ofAdd (spread Y i Q M (ρ.ch i)
          (Pi.single PP (Multiplicative.toAdd ((univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).kap PP.1 x))))) : (X.Ok i k)ˣ) : X.Ok i k) := by
  first | exact @GlobalTheory.ResTwist.res_twist_spec | exact GlobalTheory.ResTwist.res_twist_spec | (intros; apply GlobalTheory.ResTwist.res_twist_spec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleConjugatePairPlacesEqOfTwistConditionA
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleConjugatePairPlacesEqOfTwistConditionA
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdmAll

theorem admissibleConjugatePairPlaces_eq_of_twist_condition : ∀ {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (Y : NExp D.R D.host D.what₂ D.LL0 N X),
  GlobalTheory.UnivChar.IsUnivChar Y → ∀ (i : X.Tw) (k : ℕ) (Q : Finset (Pl D.host.E)) (M : ℕ)
    (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ),
    TwOK i k Q (χ.comp (Y.delU i Q M)) → admissibleConjugatePairPlaces X i Q M = Q := by
  intro D N X Y hY i k Q M χ hT
  classical
  refine Finset.Subset.antisymm (admissibleConjugatePairPlaces_subset i Q M) fun v hv => ?_
  by_contra hna
  obtain ⟨A, hA⟩ := exists_isPlaceOver N.Om v
  obtain ⟨σ, hσ, hne⟩ := (hT.2.2.2.2.2.1 v A hA).2 hv
  apply hne
  have h1 : Y.delU i Q M σ = 1 := by
    apply Multiplicative.toAdd.injective
    funext w
    by_cases hw : w.1 ∈ admissibleConjugatePairPlaces X i Q M
    · rw [delU_on hY σ w hw]
      have hvp : v ∉ GalChar.pair D.host w.1 := by
        rintro (h | hc)
        · exact hna (h ▸ hw)
        · exact hna (conj_mem_admissibleConjugatePairPlaces hw hc)
      rw [(GalChar.delOf_laws D.host X.cc (X.l i) M _).2.2.2 v hvp A hA σ hσ]
      rfl
    · rw [delU_off hY (twSet_of_twOK hT) σ w hw]
      rfl
  rw [MonoidHom.comp_apply, h1, map_one]

end GlobalTheory.AdmAll
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleConjugatePairPlacesEqOfTwistConditionAStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissibleConjugatePairPlaces_eq_of_twOK : ∀ {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (Y : NExp D.R D.host D.what₂ D.LL0 N X),
  GlobalTheory.UnivChar.IsUnivChar Y → ∀ (i : X.Tw) (k : ℕ) (Q : Finset (Pl D.host.E)) (M : ℕ)
    (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ),
    TwOK i k Q (χ.comp (Y.delU i Q M)) → admissibleConjugatePairPlaces X i Q M = Q := by
  first | exact @GlobalTheory.AdmAll.admissibleConjugatePairPlaces_eq_of_twist_condition | exact GlobalTheory.AdmAll.admissibleConjugatePairPlaces_eq_of_twist_condition | (intros; apply GlobalTheory.AdmAll.admissibleConjugatePairPlaces_eq_of_twist_condition <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientRowsExteriorDetEqConstMulTopBlockDet
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientRowsExteriorDetEqConstMulTopBlockDet
open Matrix Formalism.IndefR.Datum GlobalTheory.ExportSeries

namespace GlobalTheory

theorem dU_eq_const_mul_det_topL_translate :
  ∀ (k : Type) [Field k] (r n : ℕ) (β : DetBases k r n) (U : Planes k r n),
  ∃ (g : GL (Fin n) k) (c : kˣ), ∀ y : Matrix (Fin r) (Fin n) k,
    dU β U y = (c : k) * (topL r (y * (g : Matrix (Fin n) (Fin n) k))).det := by
  intro k _ r n β U
  have hrn : r ≤ n := by have := U.2; omega
  let b := Module.finBasisOfFinrankEq k _ (finrank_quot U)
  have hU : Module.finrank k U.1 = n - r := by have := U.2; omega
  let bU := Module.finBasisOfFinrankEq k U.1 hU
  obtain ⟨lam, hlam⟩ := LinearMap.exists_extend (bU.equivFun.toLinearMap)
  let φ : (Fin n → k) →ₗ[k] (Fin n → k) := LinearMap.pi fun j =>
    if h : j.val < r then (LinearMap.proj (⟨j.val, h⟩ : Fin r)) ∘ₗ b.equivFun.toLinearMap ∘ₗ U.1.mkQ
    else (LinearMap.proj (⟨j.val - r, by have := j.2; omega⟩ : Fin (n - r))) ∘ₗ lam
  have hφ1 : ∀ v (i : Fin r), φ v ⟨i.val, by omega⟩ = b.repr (U.1.mkQ v) i := by
    intro v i
    simp [φ, i.2]
  have hφ2 : ∀ v (i : Fin (n - r)), φ v ⟨r + i.val, by omega⟩ = lam v i := by
    intro v i
    simp [φ]
  have hφ : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have h1 : U.1.mkQ v = 0 := by
      apply b.repr.injective
      ext i
      have := hφ1 v i
      rw [hv] at this
      simpa using this.symm
    have hvU : v ∈ U.1 := by simpa using h1
    have h2 : bU.equivFun ⟨v, hvU⟩ = 0 := by
      have e : lam v = bU.equivFun ⟨v, hvU⟩ := by
        have := LinearMap.congr_fun hlam ⟨v, hvU⟩
        simpa using this
      rw [← e]
      ext i
      have := hφ2 v i
      rw [hv] at this
      simpa using this.symm
    have : (⟨v, hvU⟩ : U.1) = 0 := bU.equivFun.injective (by rw [h2, map_zero])
    simpa using congrArg Subtype.val this

  let ψ := LinearEquiv.ofInjectiveEndo φ hφ
  let A : Matrix (Fin n) (Fin n) k := (LinearMap.toMatrix' φ)ᵀ
  let B : Matrix (Fin n) (Fin n) k := (LinearMap.toMatrix' ψ.symm.toLinearMap)ᵀ
  have hAB : A * B = 1 := by
    have hc : ψ.symm.toLinearMap ∘ₗ φ = LinearMap.id := by
      refine LinearMap.ext fun v => ?_
      show ψ.symm (ψ v) = v
      exact ψ.symm_apply_apply v
    simp only [A, B, ← transpose_mul, ← LinearMap.toMatrix'_comp, hc, LinearMap.toMatrix'_id, transpose_one]
  have hBA : B * A = 1 := by
    have hc : φ ∘ₗ ψ.symm.toLinearMap = LinearMap.id := by
      refine LinearMap.ext fun v => ?_
      show ψ (ψ.symm v) = v
      exact ψ.apply_symm_apply v
    simp only [A, B, ← transpose_mul, ← LinearMap.toMatrix'_comp, hc, LinearMap.toMatrix'_id, transpose_one]
  let g : GL (Fin n) k := ⟨A, B, hAB, hBA⟩
  have hb : β.form U b ≠ 0 := fun h0 => β.ne U (by rw [(β.form U).eq_smul_basis_det b, h0, zero_smul])
  refine ⟨g, Units.mk0 _ hb, fun y => ?_⟩
  have key : ∀ i j, (y * A) i j = φ (y.row i) j := by
    intro i j
    rw [← congrFun (LinearMap.toMatrix'_mulVec φ (y.row i)) j]
    simp [A, Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm, Matrix.row]
  have ht : topL r (y * (g : Matrix (Fin n) (Fin n) k)) = (b.toMatrix fun i => U.1.mkQ (y.row i))ᵀ := by
    ext i j
    have hj : j.val < n := by omega
    have e1 : topL r (y * (g : Matrix (Fin n) (Fin n) k)) i j = (y * A) i ⟨j.val, hj⟩ := by
      simp [topL, hj, g]
    rw [e1, key, hφ1 (y.row i) j, transpose_apply, Module.Basis.toMatrix_apply]
  rw [ht, det_transpose, ← Module.Basis.det_apply, dU]
  conv_lhs => rw [(β.form U).eq_smul_basis_det b]
  rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientRowsExteriorDetEqConstMulTopBlockDetStatement
open Matrix Formalism.IndefR.Datum GlobalTheory.ExportSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotientRowsExteriorDet_eq_const_mul_topBlockDet : ∀ (k : Type) [Field k] (r n : ℕ) (β : DetBases k r n) (U : Planes k r n),
  ∃ (g : GL (Fin n) k) (c : kˣ), ∀ y : Matrix (Fin r) (Fin n) k,
    dU β U y = (c : k) * (topL r (y * (g : Matrix (Fin n) (Fin n) k))).det := by
  first | exact @GlobalTheory.dU_eq_const_mul_det_topL_translate | exact GlobalTheory.dU_eq_const_mul_det_topL_translate | (intros; apply GlobalTheory.dU_eq_const_mul_det_topL_translate <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedSeriesSpecialisedUniversalDatumMemSpan
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SpecSpan


open Classical in
theorem series_sum {D : D7} {S T : HSp D} (B : Base S T) (hB : B.Good) (ω : PairRep S T) {τs : Type} (s : Finset τs)
    (c : τs → ℂ) (f : τs → WO S T → ℂ) (hf : ∀ τ, IsThetaFunO B.F.ψ S T (f τ)) (h : GA D S) (P : PolF D T.rank S.rank) :
    series B.F ω (∑ τ ∈ s, c τ • f τ) h P = ∑ τ ∈ s, c τ • series B.F ω (f τ) h P := by
  have hθ : ∀ s : Finset τs, IsThetaFunO B.F.ψ S T (∑ τ ∈ s, c τ • f τ) := fun s => by
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty]; exact GlobalTheory.OrientedHeis.theta_zero
    | insert a s ha ih => rw [Finset.sum_insert ha]; exact GlobalTheory.OrientedHeis.theta_add (GlobalTheory.OrientedHeis.theta_smul _ (hf a)) ih
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    funext g
    rw [series_apply]
    change ω (h, g) (pureTensorO B.F.ψ B.F.θ S T (fun _ => 1) B.F.sT (fun τ => (B.F.BS τ).val) B.F.BT 0 P) 0 = 0
    rw [GlobalTheory.FockFiniteHeis.pureTensorO_zero _ _ _ _ hB.frame.vac.1 hB.frame.vac.2.inf, map_zero]
    rfl
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    funext g
    simp only [series_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    change ω (h, g) (pureTensorO B.F.ψ B.F.θ S T (fun _ => 1) B.F.sT (fun τ => (B.F.BS τ).val) B.F.BT
      (c a • f a + ∑ τ ∈ s, c τ • f τ) P) 0 = c a * ω (h, g) (pureTensorO B.F.ψ B.F.θ S T (fun _ => 1) B.F.sT (fun τ => (B.F.BS τ).val) B.F.BT
      (f a) P) 0 + ω (h, g) (pureTensorO B.F.ψ B.F.θ S T (fun _ => 1) B.F.sT (fun τ => (B.F.BS τ).val) B.F.BT
      (∑ τ ∈ s, c τ • f τ) P) 0
    rw [GlobalTheory.FockFiniteHeis.pureTensorO_lin _ _ _ _ hB.frame.vac.1 hB.frame.vac.2.inf _ _ _ _ _ (hf a) (hθ s), map_add (f := _), map_smul]
    rfl

theorem theta_vecAt {D : D7} {S T : HSp D} {B : Base S T} (hB : B.Good) {Q : Finset (Pl D.host.E)} (hQ : B.admitted Q)
    (φ : ∀ PP : ↥Q, Matrix (Fin T.rank) (Fin S.rank) (kP PP.1) → ℂ) : IsThetaFunO B.F.ψ S T (B.vecAt Q φ) :=
  GlobalTheory.GalLift.Vec.theta_of_thetaAt hB.frame.vac.1 hB.frame.vac.2.inf (Base.isThetaAt_vecAt hB hQ φ) hB.frame.vac.2.theta


open Classical in
theorem twist_series_mem_span {D : D7} {S T : HSp D} (B : Base S T) (hB : B.Good) (hS : S.SigOK) (ω : PairRep S T)
    (hω : B.IsWeil 1 ω) (t : Twist D Circle) (hQ : B.admitted t.Q) (O : Subring ℂ) (ι : ↥t.Q → Type) [∀ PP, Fintype (ι PP)]
    (a : ∀ PP, ι PP → ℂ) (ha : ∀ PP u, a PP u ∈ O) (g : ∀ PP, ι PP → GL (Fin S.rank) (kP PP.1))
    (loc : ∀ PP : ↥t.Q, Matrix (Fin T.rank) (Fin S.rank) (kP PP.1) → ℂ)
    (hloc : ∀ PP y, loc PP y = ∑ u, a PP u * flat (t.resC PP.1) (y * (g PP u : Matrix (Fin S.rank) (Fin S.rank) (kP PP.1))))
    (h : GA D S) (P : PolF D T.rank S.rank) :
    twistBy T t.chi (series B.F ω (B.vecAt t.Q loc) h P) ∈ Submodule.span O (B.genSet ω t h P) := by
  let φ : (∀ PP, ι PP) → ∀ PP : ↥t.Q, Matrix (Fin T.rank) (Fin S.rank) (kP PP.1) → ℂ :=
    fun τ PP y => flat (t.resC PP.1) (y * (g PP (τ PP) : Matrix (Fin S.rank) (Fin S.rank) (kP PP.1)))
  have hvec : B.vecAt t.Q loc = ∑ τ : (∀ PP, ι PP), (∏ PP, a PP (τ PP)) • B.vecAt t.Q (φ τ) := by
    have e1 : B.locFn t.Q loc = ∑ τ : (∀ PP, ι PP), (∏ PP, a PP (τ PP)) • B.locFn t.Q (φ τ) := by
      funext y
      simp only [Base.locFn, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hloc]
      rw [Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [Finset.prod_mul_distrib]
      ring
    change B.F.vecL B.G _ (B.locFn t.Q loc) = ∑ τ : (∀ PP, ι PP), (∏ PP, a PP (τ PP)) • B.F.vecL B.G _ (B.locFn t.Q (φ τ))
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e1, map_sum]
    simp only [map_smul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hvec, series_sum B hB ω _ _ _ (fun τ => theta_vecAt hB hQ (φ τ)), map_sum]
  refine Submodule.sum_mem _ fun τ _ => ?_
  obtain ⟨hQτ, hsupp, hmove⟩ := GlobalTheory.T.thetaSeries_integralSourceTranslation_right_mul D S T B hB hS ω hω t.Q hQ (fun PP => g PP (τ PP))
  have e2 : series B.F ω (B.vecAt t.Q (φ τ)) h P = series B.F ω (B.vecFlat t) (h * hQτ) P :=
    hmove (fun PP => flat (t.resC PP.1)) h P
  rw [map_smul, e2]
  have hmem : ∏ PP, a PP (τ PP) ∈ O := Subring.prod_mem _ fun PP _ => ha PP (τ PP)
  have e3 : (∏ PP, a PP (τ PP)) • twistBy T t.chi (series B.F ω (B.vecFlat t) (h * hQτ) P) =
      (⟨_, hmem⟩ : O) • twistBy T t.chi (series B.F ω (B.vecFlat t) (h * hQτ) P) := rfl
  rw [e3]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨hQτ, hsupp, rfl⟩)

end GlobalTheory.SpecSpan

namespace GlobalTheory.SpecSpan


open Classical in
theorem univ_spec {k : Type} [Field k] [Finite k] {r n : ℕ} {C : Type} [AddCommGroup C] [Fintype C]
    [Fintype (Planes k r n)] (β : DetBases k r n) (κ : kˣ →* Multiplicative C) (ν : Multiplicative C →* ℂˣ)
    (g : Planes k r n → GL (Fin n) k) (c : Planes k r n → kˣ)
    (hg : ∀ U y, dU β U y = (c U : k) * (topL r (y * (g U : Matrix (Fin n) (Fin n) k))).det)
    (y : Matrix (Fin r) (Fin n) k) :
    ∑ a : C, (ν (Multiplicative.ofAdd a) : ℂ) * ((univCoef β κ a y : ℚ) : ℂ) =
      ∑ U : Planes k r n, ((Nat.card k : ℂ) ^ (r * (n - r)))⁻¹ * (ν (κ (c U)) : ℂ) *
        flat (ν.comp κ) (y * (g U : Matrix (Fin n) (Fin n) k)) := by
  have hterm : ∀ U : Planes k r n, ∑ a : C, (ν (Multiplicative.ofAdd a) : ℂ) * (((univTerm β κ y U).coeff a : ℚ) : ℂ) =
      (ν (κ (c U)) : ℂ) * flat (ν.comp κ) (y * (g U : Matrix (Fin n) (Fin n) k)) := by
    intro U
    unfold univTerm
    by_cases hC : Compl U.1 y
    · rw [dite_eq_left hC]
      have hd : dU β U y ≠ 0 := (dU_ne_zero_iff β U y).2 hC
      have hdet : (topL r (y * (g U : Matrix (Fin n) (Fin n) k))).det ≠ 0 := by
        intro h0; apply hd; rw [hg, h0, mul_zero]
      simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
      rw [Finset.sum_eq_single (Multiplicative.toAdd (κ (Units.mk0 _ hd)))]
      · rw [if_pos rfl, Rat.cast_one, mul_one, flat_of_isUnit (ν.comp κ) (u := Units.mk0 _ hdet) rfl]
        have e : Units.mk0 _ hd = c U * Units.mk0 _ hdet := Units.ext (by simp [hg])
        rw [ofAdd_toAdd, e, map_mul, map_mul, Units.val_mul, MonoidHom.comp_apply]
      · intro a _ ha
        rw [if_neg (Ne.symm ha), Rat.cast_zero, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [dite_eq_right hC]
      have hd : dU β U y = 0 := by
        by_contra h; exact hC ((dU_ne_zero_iff β U y).1 h)
      have hdet : ¬ IsUnit (topL r (y * (g U : Matrix (Fin n) (Fin n) k))).det := by
        rw [isUnit_iff_ne_zero]; intro h0
        rw [hg] at hd
        exact h0 ((mul_eq_zero.1 hd).resolve_left (c U).ne_zero)
      rw [flat_of_not_isUnit _ hdet, mul_zero]
      simp
  have hcoef : ∀ a : C, univCoef β κ a y =
      ((Nat.card k : ℚ) ^ (r * (n - r)))⁻¹ * ∑ U : Planes k r n, (univTerm β κ y U).coeff a := by
    intro a
    rw [univCoef, univ, AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul, AddMonoidAlgebra.coeff_sum,
      Finsupp.finsetSum_apply]
    congr 1
    exact Finset.sum_congr (by congr; exact Subsingleton.elim _ _) fun _ _ => rfl
  simp only [hcoef, Rat.cast_mul, Rat.cast_inv, Rat.cast_pow, Rat.cast_natCast, Rat.cast_sum]
  rw [Finset.sum_congr rfl fun U _ => (by rw [mul_assoc, ← hterm U] :
    ((Nat.card k : ℂ) ^ (r * (n - r)))⁻¹ * (ν (κ (c U)) : ℂ) * flat (ν.comp κ) (y * (g U : Matrix (Fin n) (Fin n) k)) =
      ((Nat.card k : ℂ) ^ (r * (n - r)))⁻¹ * ∑ a : C, (ν (Multiplicative.ofAdd a) : ℂ) * (((univTerm β κ y U).coeff a : ℚ) : ℂ))]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun U _ => Finset.sum_congr rfl fun a _ => by ring

end GlobalTheory.SpecSpan

namespace GlobalTheory.SpecSpan

theorem specSer_mem_span : ∀ {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (ρ : Setup X), ρ.Good →
  ∀ (Y : NExp D.R D.host D.what₂ D.LL0 N X), GlobalTheory.UnivChar.IsUnivChar Y →
  ∀ (i : X.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ) (Q : Finset (Pl D.host.E)) (M : ℕ)
    (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ),
    TwOK i k Q (χ.comp (Y.delU i Q M)) → InRange X i Q →
    ∀ (s : Finset (Pl D.host.E)) (h : GA D (Vc D j)) (P : PolF D (Wc D j).rank (Vc D j).rank),
      ρ.IsDatum i j b s h P → (∀ v ∈ Q, ((normProd s : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal) →
      specSer ρ Y i j b k Q M χ h P ∈
        Submodule.span (ρ.eOk i b k).range (ρ.gens i j b k Q (χ.comp (Y.delU i Q M)) h P) := by
  intro D N X ρ hρ Y hY i j b k Q M χ hT _ s h P _ _
  classical
  have hA : admissibleConjugatePairPlaces X i Q M = Q := GlobalTheory.T.admissibleConjugatePairPlaces_eq_of_twOK Y hY i k Q M χ hT
  obtain ⟨-, hadm, -⟩ := GlobalTheory.TwistGood.tw_good D N X ρ hρ i j b k Q (χ.comp (Y.delU i Q M)) hT
  have hS : (Vc D j).SigOK := D.sp.V_sig _
  haveI : ∀ PP : Pl D.host.E, Fintype (Planes (kP PP) (Wc D j).rank (Vc D j).rank) := fun PP => Fintype.ofFinite _
  choose gC cC hgc using fun (PP : Pl D.host.E) (U : Planes (kP PP) (Wc D j).rank (Vc D j).rank) =>
    GlobalTheory.T.quotientRowsExteriorDet_eq_const_mul_topBlockDet (kP PP) (Wc D j).rank (Vc D j).rank (ρ.β j PP) U
  have key : ∀ (Q₀ : Finset (Pl D.host.E)), Q₀ = (ρ.tw i b k Q (χ.comp (Y.delU i Q M))).Q →
      ∀ (loc : ∀ PP : ↥Q₀, Matrix (Fin (Wc D j).rank) (Fin (Vc D j).rank) (kP PP.1) → ℂ)
        (a : ∀ PP : ↥Q₀, Planes (kP PP.1) (Wc D j).rank (Vc D j).rank → ℂ),
        (∀ PP u, a PP u ∈ (ρ.eOk i b k).range) →
        (∀ PP y, loc PP y = ∑ u, a PP u * flat ((ρ.tw i b k Q (χ.comp (Y.delU i Q M))).resC PP.1)
          (y * (gC PP.1 u : Matrix (Fin (Vc D j).rank) (Fin (Vc D j).rank) (kP PP.1)))) →
        twistBy (Wc D j) (ρ.tw i b k Q (χ.comp (Y.delU i Q M))).chi
          (series (ρ.B i j b).F (ρ.om i j b 1) ((ρ.B i j b).vecAt Q₀ loc) h P) ∈
          Submodule.span (ρ.eOk i b k).range (ρ.gens i j b k Q (χ.comp (Y.delU i Q M)) h P) := by
    intro Q₀ hQ₀
    subst hQ₀
    intro loc a ha hloc
    exact twist_series_mem_span (ρ.B i j b) (hρ.base i j b) hS (ρ.om i j b 1) (hρ.weil_base i j b) _ hadm _
      (fun PP => Planes (kP PP.1) (Wc D j).rank (Vc D j).rank) a ha (fun PP u => gC PP.1 u) loc hloc h P

  let ν : ∀ PP : ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)), Multiplicative (ZMod (X.l i ^ M)) →* ℂˣ := fun PP =>
    (Units.map (ρ.eOk i b k).toMonoidHom).comp (χ.comp (AddMonoidHom.toMultiplicative
      ((spread Y i Q M (ρ.ch i)).comp (AddMonoidHom.single (fun _ : ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) => ZMod (X.l i ^ M)) PP))))
  have hν : ∀ PP a, (ν PP (Multiplicative.ofAdd a) : ℂ) =
      ρ.eOk i b k ((χ (Multiplicative.ofAdd (spread Y i Q M (ρ.ch i) (Pi.single PP a))) : (X.Ok i k)ˣ) : X.Ok i k) := by
    intro PP a; rfl
  have hres : ∀ PP : ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)),
      (ν PP).comp ((univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).kap PP.1) = (ρ.tw i b k Q (χ.comp (Y.delU i Q M))).resC PP.1 := by
    intro PP
    ext x
    rw [GlobalTheory.T.residueCharacter_twist_universalChar_at_chosen_place ρ hρ Y hY i b k Q M χ hT PP x, MonoidHom.comp_apply, ← hν, ofAdd_toAdd]
  have hnS : ∀ PP : ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)), PP.1 ∉ X.S0 i := fun PP =>
    Finset.disjoint_left.1 hT.2.1 (admissibleConjugatePairPlaces_subset i Q M (mem_half.1 PP.2).1)
  let qi : Pl D.host.E → ℂ := fun PP => ((Nat.card (kP PP) : ℂ) ^ ((Wc D j).rank * ((Vc D j).rank - (Wc D j).rank)))⁻¹
  have hqi : ∀ PP : ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)), qi PP.1 ∈ (ρ.eOk i b k).range := by
    intro PP
    obtain ⟨w, hw⟩ := GlobalTheory.T.isUnit_card_residueField_off_exceptional_places X i k PP.1 (hnS PP)
    refine ⟨((w⁻¹ ^ ((Wc D j).rank * ((Vc D j).rank - (Wc D j).rank)) : (X.Ok i k)ˣ) : X.Ok i k), ?_⟩
    have e : ρ.eOk i b k (w : X.Ok i k) = (Nat.card (kP PP.1) : ℂ) := by rw [hw, map_natCast]
    have e' : ρ.eOk i b k (w : X.Ok i k) ≠ 0 := by
      intro h0; exact w.ne_zero ((map_eq_zero_iff _ (ρ.eOk_injective i b k)).1 h0)
    have e2 : ρ.eOk i b k ((w⁻¹ : (X.Ok i k)ˣ) : X.Ok i k) = (Nat.card (kP PP.1) : ℂ)⁻¹ := by
      rw [← e]
      exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])
    show _ = ((Nat.card (kP PP.1) : ℂ) ^ ((Wc D j).rank * ((Vc D j).rank - (Wc D j).rank)))⁻¹
    rw [Units.val_pow_eq_pow_val, map_pow, e2, inv_pow]
  refine key _ (by show half _ _ = half _ _; rw [hA]) (specLoc ρ Y i j b k Q M χ)
    (fun PP U => qi PP.1 * (ν PP ((univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).kap PP.1 (cC PP.1 U)) : ℂ)) ?_ ?_
  · intro PP U
    refine Subring.mul_mem _ (hqi PP) ?_
    exact ⟨_, rfl⟩
  · intro PP y
    have := univ_spec (ρ.β j PP.1) ((univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).kap PP.1) (ν PP) (gC PP.1) (cC PP.1)
      (hgc PP.1) y
    rw [hres PP] at this
    exact this
end GlobalTheory.SpecSpan

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedSeriesSpecialisedUniversalDatumMemSpanStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedSeries_specialisedUniversalDatum_mem_span : ∀ {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (ρ : Setup X), ρ.Good →
  ∀ (Y : NExp D.R D.host D.what₂ D.LL0 N X), GlobalTheory.UnivChar.IsUnivChar Y →
  ∀ (i : X.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ) (Q : Finset (Pl D.host.E)) (M : ℕ)
    (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ),
    TwOK i k Q (χ.comp (Y.delU i Q M)) → InRange X i Q →
    ∀ (s : Finset (Pl D.host.E)) (h : GA D (Vc D j)) (P : PolF D (Wc D j).rank (Vc D j).rank),
      ρ.IsDatum i j b s h P → (∀ v ∈ Q, ((normProd s : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal) →
      specSer ρ Y i j b k Q M χ h P ∈
        Submodule.span (ρ.eOk i b k).range (ρ.gens i j b k Q (χ.comp (Y.delU i Q M)) h P) := by
  first | exact @GlobalTheory.SpecSpan.specSer_mem_span | exact GlobalTheory.SpecSpan.specSer_mem_span | (intros; apply GlobalTheory.SpecSpan.specSer_mem_span <;> assumption)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SeriesTie

theorem thetaLatticeCondition_of_seriesComparison_universalChar {D : D7} {ρ : Setup D.ntw} {hρ : ρ.Good} {rd : Rds D.nexp ρ} (T : Comparison₂ hρ rd)
    (hY : GlobalTheory.UnivChar.IsUnivChar D.nexp) (hR : ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j b, RatTwist hρ (rd i j b)) :
    Formalism.MainNotions.IntegralHeckeForms.TwistedSeriesSpecialisation D.nexp := by
  intro i hi j hj b k Q M χ hψ a hQa
  obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.1 hj
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hj1
  let j' : Fin D.R.m := ⟨n, hj2⟩
  have T := T i j' b
  by_cases hoff : InRange D.ntw i Q ∧ ∀ a', ρ.xi i j' b D.nexp Q M (T.cls a) (T.coef a) a' ∈ Set.range (rd i j' b)
  · choose x hx using hoff.2
    rw [T.thU_eq Q M a hoff.1 x hx]
    obtain ⟨z, hz, hzr⟩ := exists_mem_thPsi_of_mem_span T (hR i hi j' b) hψ hoff.1.2.1 a
      (f := specXi ρ D.nexp i j' b k Q M χ (T.cls a) (T.coef a))
      (by
        rw [GlobalTheory.T.specialised_universal_series_eq_twisted_thetaSeries ρ hρ D.nexp hY i j' b k Q M χ hψ]
        exact GlobalTheory.T.twistedSeries_specialisedUniversalDatum_mem_span ρ hρ D.nexp hY i j' b k Q M χ hψ hoff.1 _ _ _ (T.dat a)
          fun v hv h => Finset.disjoint_left.1 hQa hv ((T.lev_iff a v).2 h))
    have e : z = Formalism.MainNotions.IntegralHeckeForms.specU D.nexp i ((j' : ℕ) + 1) b Q M k χ (grpSum D.nexp (ρ.ch i) Q M x) := by
      refine T.injective_rdK k (hzr.trans ?_)
      rw [rdK_specU_grpSum hρ (rd i j' b) k Q M χ x, specXi]
      exact Finset.sum_congr rfl fun a' _ => by rw [hx a']
    rw [← e]
    exact hz
  · rw [T.thU_off Q M a hoff, map_zero]
    exact zero_mem _

theorem thetaLatticeCondition_of_fullSeriesComparison : ∀ (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (rd : Rds D.nexp ρ), FullTie hρ rd →
    GlobalTheory.TwInputs.Laws hρ rd → Formalism.MainNotions.IntegralHeckeForms.TwistedSeriesSpecialisation D.nexp :=
  fun _ _ _ _ F L => thetaLatticeCondition_of_seriesComparison_universalChar F.tie F.univ fun i hi j b => (L.rat i hi j b).2.1

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} {YS : NX.NExpRealS Rl cG S}
  {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}

end GlobalTheory.SeriesTie
