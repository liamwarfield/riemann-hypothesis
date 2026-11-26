module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPlaceGood
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftAutomorphicForm
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsVectorPrescribedCosetsBadPrimesFrames
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitLocalComponentHasFixedVectorOfIsotypic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OperatorEigenGoodPlaceSecond
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLimitRep
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceDoubledEigenfunctionsLineVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitarisableOfIsLocCompCusp
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KerEntTiedTrueEnt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PointsEqualEigenMatch
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.EigAgree

end GlobalTheory.EigAgree

theorem GlobalTheory.EigAgree.cast_ne_zero {D : D7} {μ : D.what₂.Tup} {a b : ℕ} (h : a = b) (f : D.what₂.Mt μ a) (hf : f ≠ 0) :
    (h ▸ f : D.what₂.Mt μ b) ≠ 0 := by
  subst h
  exact hf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaEigenCompatibilitySecond
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsotypicFixedVectorIsSatakeEigenInertPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsotypicFixedVectorIsSatakeEigenInertPlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EigIsoInert

def stabRt {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    (f : GAf L n → W) : Subgroup (GAf L n) where
  carrier := {κ | NG.rt L n κ f = f}
  one_mem' := funext fun y => by
    show f (y * 1) = f y
    rw [mul_one]
  mul_mem' := by
    intro a b ha hb
    have ha' : NG.rt L n a f = f := ha
    have hb' : NG.rt L n b f = f := hb
    show NG.rt L n (a * b) f = f
    have e : NG.rt L n (a * b) f = NG.rt L n a (NG.rt L n b f) := funext fun y => by
      show f (y * (a * b)) = f (y * a * b)
      rw [mul_assoc]
    rw [e, hb', ha']
  inv_mem' := by
    intro a ha
    have ha' : NG.rt L n a f = f := ha
    show NG.rt L n a⁻¹ f = f
    calc NG.rt L n a⁻¹ f = NG.rt L n a⁻¹ (NG.rt L n a f) := by rw [ha']
      _ = f := funext fun y => by
        show f (y * a⁻¹ * a) = f y
        rw [inv_mul_cancel_right]

theorem eig_of_irr (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n)
    (S : Submodule ℂ (GAf L n → a.W)) (hS : NG.IsIrrRep a.ρ S) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (w : HeightOneSpectrum (𝓞 L)) (hw : NG.OverPl w v) (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ)
    (hsat : NG.SatAt { a with S := S, irrS := hS } Dv α) (f : GAf L n → a.W) (hfS : f ∈ S)
    (hfK : ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f = f)
    (h : Formalism.UG.GU Dv.σw n → ℂ) (hh : h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n)) :
    heckeFunI L n (Umax L n) Dv h f = Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) h α • f := by
  let U : Subgroup (GAf L n) := Umax L n ⊓ stabRt f
  have hU : ∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n) :=
    fun κ hκ => ⟨fun h1 => h1.1, fun h1 => ⟨h1, hfK κ h1 hκ⟩⟩
  have e1 := GlobalTheory.InertSph.satU_of_fixed L n a S hS v w Dv α hw hsat U hU f hfS (fun κ hκ => hκ.2) h hh
  have hK : ∀ κ : GAf L n, κ ∈ Umax L n → TrivOutside {v} κ → ∃ hκ : Dv.loc κ ∈ Formalism.UG.GU Dv.σw n,
      (⟨Dv.loc κ, hκ⟩ : Formalism.UG.GU Dv.σw n) ∈ Formalism.UG.KU Dv.σw n :=
    fun κ hκ _ => ⟨GlobalTheory.T.inertDatum_local_mem_unitaryGroup_antidiagonal L n v w Dv κ, GlobalTheory.T.inertDatum_local_stdLatticeStabilizer_mem_maxCompact L n v w Dv κ hκ _⟩
  rw [GlobalTheory.T.inertHeckeOperator_level_independent L n v w Dv hK (Umax L n) U (fun _ _ => Iff.rfl) hU a.W h hh.1 f hfK]
  exact e1

theorem eig_of_isoTyp_fixed : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.AutRep L n) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ), NG.SatAt π Dv α → ∀ φ ∈ NG.isoTyp π.ρ π.S, (∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ φ = φ) → ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n), heckeFunI L n (Umax L n) Dv h φ = Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) h α • φ := by
  intro L _ _ _ n π v w hw Dv α hsat φ hφ hφK h hh
  have hfin : ∀ (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) →
      ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n), Set.Finite {c : GAf L n ⧸ U | ∃ x : GAf L n,
        (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x ∧ Dv.hval h (Dv.loc x) ≠ 0} :=
    fun U hU h hh => GlobalTheory.T.finite_inertHecke_support_cosets L n v w Dv (fun s => GlobalTheory.T.unitary_doubleCoset_finite_left_cosets Dv.ϖ Dv.σw _ n Dv.unram s)
      (GlobalTheory.T.mem_maxCompact_of_trivOutside_local_integral L n v w Dv) U hU h hh
  set c := Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) h α with hc

  have hirr : ∀ S' : Submodule ℂ (GAf L n → π.W), NG.IsIrrRep π.ρ S' ∧ NG.IsoRep π.S S' → ∀ f ∈ S',
      (∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f = f) → heckeFunI L n (Umax L n) Dv h f = c • f := by
    rintro S' ⟨hS', hiso⟩ f hf hfK
    have hsat' : NG.SatAt { π.toAlgWt with S := S', irrS := hS' } Dv α :=
      GlobalTheory.SatIso.satAt_of_iso L n π { π.toAlgWt with S := S', irrS := hS' } ⟨⟨LinearEquiv.refl ℂ _, fun _ _ => rfl⟩, hiso⟩ v w Dv α hfin hsat
    exact eig_of_irr L n π.toAlgWt S' hS' v w hw Dv α hsat' f hf hfK h hh

  obtain ⟨C, cf, xs, hC⟩ := GlobalTheory.SatIso.heckeFunI_eq_sum Dv (Umax L n) h (hfin (Umax L n) (fun _ _ => Iff.rfl) h hh)
  have hadd : ∀ y z : GAf L n → π.W, heckeFunI L n (Umax L n) Dv h (y + z) =
      heckeFunI L n (Umax L n) Dv h y + heckeFunI L n (Umax L n) Dv h z := by
    intro y z
    rw [hC π.W, hC π.W, hC π.W, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [map_add (f := _), smul_add]
  have hzero : heckeFunI L n (Umax L n) Dv h (0 : GAf L n → π.W) = 0 := by
    rw [hC π.W]
    simp
  have key : ∀ t : Finset (Submodule ℂ (GAf L n → π.W)),
      (↑t ⊆ {S' | NG.IsIrrRep π.ρ S' ∧ NG.IsoRep π.S S'}) → ∀ f ∈ (⨆ i ∈ t, i),
      (∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f = f) → heckeFunI L n (Umax L n) Dv h f = c • f := by
    classical
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro _ f hf _
      simp only [Finset.notMem_empty, iSup_false, iSup_bot, Submodule.mem_bot] at hf
      subst hf
      rw [hzero, smul_zero]
    | insert a t ha ih =>
      intro hsub f hf hfix
      have haF : NG.IsIrrRep π.ρ a ∧ NG.IsoRep π.S a := hsub (Finset.mem_insert_self a t)
      have hsF : (↑t : Set _) ⊆ {S' | NG.IsIrrRep π.ρ S' ∧ NG.IsoRep π.S S'} :=
        fun x hx => hsub (Finset.mem_insert_of_mem hx)
      rw [Finset.iSup_insert] at hf
      have hMst : ∀ g, ∀ y ∈ (⨆ i ∈ t, i), NG.rt L n g y ∈ (⨆ i ∈ t, i) :=
        GlobalTheory.IsoFix.iSup_finset_stable t (fun i hi => (hsF hi).1.1.stable)
      by_cases hd : a ⊓ (⨆ i ∈ t, i) = ⊥
      · obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hf
        have hyz : ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ y = y ∧ NG.rt L n κ z = z := by
          intro κ hκ hκt
          have e := hfix κ hκ hκt
          rw [map_add (f := _)] at e
          have h1 : NG.rt L n κ y - y = z - NG.rt L n κ z := by
            rw [sub_eq_sub_iff_add_eq_add, e, add_comm]
          have hm : NG.rt L n κ y - y ∈ a ⊓ (⨆ i ∈ t, i) :=
            ⟨a.sub_mem (haF.1.1.stable κ y hy) hy, h1 ▸ Submodule.sub_mem _ hz (hMst κ z hz)⟩
          rw [hd, Submodule.mem_bot] at hm
          refine ⟨sub_eq_zero.1 hm, ?_⟩
          rw [hm] at h1
          exact (sub_eq_zero.1 h1.symm).symm
        rw [hadd, hirr a haF y hy (fun κ hκ hκt => (hyz κ hκ hκt).1),
          ih hsF z hz (fun κ hκ hκt => (hyz κ hκ hκt).2), smul_add]
      · have hsubrep : NG.IsSubrep π.ρ (a ⊓ ⨆ i ∈ t, i) :=
          ⟨inf_le_left.trans haF.1.1.le, fun g y hy => ⟨haF.1.1.stable g y hy.1, hMst g y hy.2⟩⟩
        have heq : a ⊓ (⨆ i ∈ t, i) = a := (haF.1.2.2 _ hsubrep inf_le_left).resolve_left hd
        have hle : a ≤ ⨆ i ∈ t, i := heq ▸ inf_le_right
        exact ih hsF f ((sup_le hle le_rfl) hf) hfix
  unfold NG.isoTyp at hφ
  obtain ⟨s, hs, hfs⟩ := Submodule.mem_sSup_iff_exists_finset.1 hφ
  exact key s hs φ hfs (fun κ hκ hκt => hφK κ hκ hκt)

end GlobalTheory.EigIsoInert
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsotypicFixedVectorIsSatakeEigenInertPlaceStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotypicFixedVector_isSatakeEigen_inertPlace : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.AutRep L n) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ), NG.SatAt π Dv α → ∀ φ ∈ NG.isoTyp π.ρ π.S, (∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ φ = φ) → ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n), heckeFunI L n (Umax L n) Dv h φ = Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) h α • φ := by
  first | exact @GlobalTheory.EigIsoInert.eig_of_isoTyp_fixed | exact GlobalTheory.EigIsoInert.eig_of_isoTyp_fixed | (intros; apply GlobalTheory.EigIsoInert.eig_of_isoTyp_fixed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotIsSplitPlaceOfInertOverRealSubfield
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotIsSplitPlaceOfInertOverRealSubfield
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem not_isSplitPl_of_isInertAt (D : D7) (Pp : HeightOneSpectrum (𝓞 D.host.E)) (h : Formalism.UG.IsInertAt (↥D.host.F) D.host.E (HeightOneSpectrum.under (𝓞 ↥D.host.F) Pp) Pp) : ¬ Formalism.BasicNotions.IsSplitPl D.host Pp := by
  rintro ⟨x, hx, hy⟩
  have hc : (NumberField.RingOfIntegers.mapRingHom (D.host.conj : D.host.E →+* D.host.E)).comp
      (algebraMap (𝓞 ↥D.host.F) (𝓞 D.host.E)) = algebraMap (𝓞 ↥D.host.F) (𝓞 D.host.E) := by
    refine RingHom.ext fun a => RingOfIntegers.ext ?_
    have key : ((algebraMap (𝓞 ↥D.host.F) (𝓞 D.host.E) a : 𝓞 D.host.E) : D.host.E) = ((a : ↥D.host.F) : D.host.E) := rfl
    have h0 := (D.host.conjE_mem_hostF_iff _).1 (a : ↥D.host.F).2
    show (D.host.conj ((algebraMap (𝓞 ↥D.host.F) (𝓞 D.host.E) a : 𝓞 D.host.E) : D.host.E)) = _
    rw [key]; exact h0
  have hmem : NumberField.RingOfIntegers.mapRingHom (D.host.conj : D.host.E →+* D.host.E) x ∈ Pp.asIdeal := by
    unfold Formalism.UG.IsInertAt at h
    rw [← h] at hx ⊢
    have := Ideal.mem_map_of_mem (NumberField.RingOfIntegers.mapRingHom (D.host.conj : D.host.E →+* D.host.E)) hx
    rwa [Ideal.map_map, hc] at this
  exact hy _ rfl hmem

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotIsSplitPlaceOfInertOverRealSubfieldStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.not_isSplitPlace_of_inert_over_realSubfield : ∀ (D : D7) (Pp : HeightOneSpectrum (𝓞 D.host.E)), Formalism.UG.IsInertAt (↥D.host.F) D.host.E (HeightOneSpectrum.under (𝓞 ↥D.host.F) Pp) Pp → ¬ Formalism.BasicNotions.IsSplitPl D.host Pp := by
  first | exact @GlobalTheory.not_isSplitPl_of_isInertAt | exact GlobalTheory.not_isSplitPl_of_isInertAt | (intros; apply GlobalTheory.not_isSplitPl_of_isInertAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SatakeTransformEqOfUnramifiedBaseChangeEq
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SatakeTransformEqOfUnramifiedBaseChangeEq
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.InertUbcSatake

theorem satU_eq_of_ubc_eq : ∀ (K : Type) [Field K] [Valued K (WithZero (Multiplicative ℤ))] [CompleteSpace K] (ϖ : K) (σ : K →+* K) (q n : ℕ), Formalism.UG.IsUnramInv ϖ σ q → ∀ α β : Fin (n / 2) → ℂ, ubc n (Multiset.map α Finset.univ.val) = ubc n (Multiset.map β Finset.univ.val) → ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), Formalism.UG.SatU ϖ q h α = Formalism.UG.SatU ϖ q h β :=
  GlobalTheory.SatBcZero.satU_eq_of_ubc_eq

end GlobalTheory.InertUbcSatake
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SatakeTransformEqOfUnramifiedBaseChangeEqStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.satakeTransform_eq_of_unramifiedBaseChange_eq : ∀ (K : Type) [Field K] [Valued K (WithZero (Multiplicative ℤ))] [CompleteSpace K] (ϖ : K) (σ : K →+* K) (q n : ℕ), Formalism.UG.IsUnramInv ϖ σ q → ∀ α β : Fin (n / 2) → ℂ, ubc n (Multiset.map α Finset.univ.val) = ubc n (Multiset.map β Finset.univ.val) → ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), Formalism.UG.SatU ϖ q h α = Formalism.UG.SatU ϖ q h β := by
  first | exact @GlobalTheory.InertUbcSatake.satU_eq_of_ubc_eq | exact GlobalTheory.InertUbcSatake.satU_eq_of_ubc_eq | (intros; apply GlobalTheory.InertUbcSatake.satU_eq_of_ubc_eq <;> assumption)
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.EigInert.heckeFunI_umax_sum {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {w : HeightOneSpectrum (𝓞 L)} (Dv : InertDatum L n v w)
    (h : Formalism.UG.GU Dv.σw n → ℂ) (hh : h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n)) :
    ∃ (C : Finset (GAf L n ⧸ Umax L n)) (a : GAf L n ⧸ Umax L n → ℂ) (x : GAf L n ⧸ Umax L n → GAf L n),
      ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (φ : GAf L n → W),
        heckeFunI L n (Umax L n) Dv h φ = ∑ c ∈ C, a c • NG.rt L n (x c) φ :=
  GlobalTheory.SatIso.heckeFunI_eq_sum Dv _ h (GlobalTheory.T.finite_inertHecke_support_cosets L n v w Dv (GlobalTheory.T.unitary_doubleCoset_finite_left_cosets Dv.ϖ Dv.σw _ n Dv.unram)
    (GlobalTheory.T.mem_maxCompact_of_trivOutside_local_integral L n v w Dv) _ (fun _ _ => Iff.rfl) h hh)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ApartOfNotMem
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

namespace GlobalTheory.Cong.OffTLimit

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {l : ℕ} [Fact l.Prime] {a : ℕ}

theorem apart_of_not_mem {w₀ w : HeightOneSpectrum (𝓞 E)} (h₀ : ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal)
    (hw : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) : Apart w w₀ := by
  intro h
  apply hw
  have h1 : ((l : ℕ) : 𝓞 (maximalRealSubfield E)) ∈ (w₀.under (𝓞 (maximalRealSubfield E))).asIdeal := by
    rw [HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast]; exact h₀
  rw [← h, HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast] at h1
  exact h1

theorem z_eq_of_equiv {ι : Qbar l ≃+* ℂ} {Kw : Levels E a} {J : Type} (O : LocOps l ι Kw J) (j : J)
    {σ σ' : SmIrr (GL (Fin a) ((O.pl j).adicCompletion E))} (e : σ.ρ.Equiv σ'.ρ)
    (hne : PRep.fixed σ.ρ (Kw (O.pl j)) ≠ ⊥) : O.z j σ = O.z j σ' := by
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hne
  have he : ∀ g u, e.toLinearEquiv (σ.ρ g u) = σ'.ρ g (e.toLinearEquiv u) := fun g u =>
    LinearMap.congr_fun (e.isIntertwining' g) u
  have hv' : e.toLinearEquiv v ∈ PRep.fixed σ'.ρ (Kw (O.pl j)) := by
    change ∀ h : Kw (O.pl j), σ'.ρ (h : GL (Fin a) ((O.pl j).adicCompletion E)) (e.toLinearEquiv v) =
      ((1 : Kw (O.pl j) →* ℂˣ) h : ℂ) • e.toLinearEquiv v
    intro h
    have := hv h
    simp only [MonoidHom.one_apply, Units.val_one, one_smul] at this ⊢
    rw [← he, this]
  have hop : e.toLinearEquiv (opOf σ.ρ (O.f j) v) = opOf σ'.ρ (O.f j) (e.toLinearEquiv v) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [opOf, Finsupp.sum, map_sum, map_smul, he]
  have h2 := O.act j σ' _ hv'
  rw [← hop, O.act j σ v hv, map_smul] at h2
  have hne' : e.toLinearEquiv v ≠ 0 := by simpa using hv0
  exact smul_left_injective ℂ hne' h2

end GlobalTheory.Cong.OffTLimit

namespace GlobalTheory.Cong

end GlobalTheory.Cong
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalComponentsOfSmoothCharacters
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SphUnr

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem ms_eq_singleton {Δ : Segment k} (h1 : Δ.len = 1) : Δ.ms = {Δ.first} := by
  obtain ⟨z, hz⟩ := Multiset.card_eq_one.1 ((Segment.card_ms Δ).trans h1)
  have h3 : z = Δ.first := by
    have hm : z ∈ Δ.ms := by rw [hz]; exact Multiset.mem_singleton_self z
    obtain ⟨a, ha, rfl⟩ := Segment.mem_carrier.1 (Segment.mem_ms.1 hm)
    obtain rfl : a = 0 := by omega
    simp
  rw [hz, h3]

open scoped Classical in
noncomputable def valAt (ϖ : kˣ) (y : IrrGL (k := k)) : ℂˣ :=
  if h : ∃ (μ : kˣ →* ℂˣ) (hμ : IsSmoothChar μ), y = IrrGL.ofChar μ hμ then h.choose ϖ else 1

end Local

section Sph

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

end Sph

section Glob

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

end Glob

end GlobalTheory.SphUnr

namespace GlobalTheory.SphUnr

end GlobalTheory.SphUnr
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KerTie
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ErrorDataGeneratorsEqColumnPreDatum
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ErrorDataGeneratorsEqColumnPreDatum
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

namespace GlobalTheory.Svd

theorem errXS_pi_of_colT : ∀ (B : GlobalTheory.Mem.Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (t : GlobalTheory.Mem.Top.Bl.ColT w Z), (Formalism.L2.Herm.toErrXS t.full.1).piG = w.px.piG ∧ (Formalism.L2.Herm.toErrXS t.full.1).piT = w.px.piT := by
  intro B f T w Z t
  have hc : t.full.1.cols = t.C.herm := t.full.2
  refine ⟨?_, ?_⟩
  · show (t.full.1.cols.levelZeroCompatibility (w.D Z).u₀).piG = _
    rw [hc, ← t.C.piG]
    exact (t.std _).gl.piG
  · funext u
    show (t.full.1.cols.atT u).piU = _
    rw [hc, ← t.C.piU u]
    exact (t.std u).piU

end GlobalTheory.Svd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ErrorDataGeneratorsEqColumnPreDatumStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.errorData_generators_eq_columnPreDatum : ∀ (B : GlobalTheory.Mem.Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (t : ColT w Z), (Formalism.L2.Herm.toErrXS t.full.1).piG = w.px.piG ∧ (Formalism.L2.Herm.toErrXS t.full.1).piT = w.px.piT := by
  first | exact @GlobalTheory.Svd.errXS_pi_of_colT | exact GlobalTheory.Svd.errXS_pi_of_colT | (intros; apply GlobalTheory.Svd.errXS_pi_of_colT <;> assumption)
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.Svd.Part.kerTie : ∀ (B : GlobalTheory.Mem.Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (O : Obj (w.D Z)), Part w Z (ofObj O) → O.ex.tw = w.tw Z ∧ O.ex.errX.piG = w.px.piG ∧ O.ex.errX.piT = w.px.piT ∧ TC.QpIs w.I O.X.Qp ∧ ∃ t : KerEntTied O.ex, TC.StdKer w.I w.l Z t ∧ t.Adapted ∧ t.TopPinned := by
  intro B f T w Z O P
  obtain ⟨L, gatT, Gx, Gy, Kc, X, cX, ex⟩ := O
  obtain ⟨lev, th, th_io, cmp, lat, tw, ker, ep_def, ep_tie, kapI_def, fills_all, nu_unserved, idx, kap_def, lam_def, kapR_def,
    errX, err, nch, nch_tie, xd, p0, rationalRoots_def, amb, amb0, fdef, duStar_def, Dstar_def, gauge, gauge_def⟩ := ex
  obtain ⟨pin, col, hErr, tp, hxi, qp, ker0, ker_eq, kt⟩ := P
  dsimp only [ofObj, extraObj] at hErr ker_eq qp kt
  cases ker_eq
  subst hErr
  have hpi := GlobalTheory.T.errorData_generators_eq_columnPreDatum B f T w Z col
  refine ⟨rfl, hpi.1, hpi.2, qp, ?_⟩
  refine Exists.imp (by intro t h; exact ⟨(StdModel.stdKer_iff w.I w.l Z t).2 h.1, h.2.2.2.1, h.2.2.2.2⟩)
    (GlobalTheory.Mem.Col2.TC.kerEntTied_true_ent w.I w.ok w.pins w.l Z _ _ _ _ _ _ _ _ kt.O kt.E qp kt.std kt.unf kt.ok (by exact kt.served))
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalTraceMatrixUnitsActsBySumInfinitesimalCh
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalTraceMatrixUnitsActsBySumInfinitesimalCh
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published
noncomputable section

namespace GlobalTheory


open Polynomial in
theorem trace_Eop_of_hasInfChar (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (π : GlobalTheory.CuspRep.CuspSub E a) (τ : E →+* ℂ) (m : Multiset ℂ) (h : π.HasInfChar τ m) :
    ∀ φ ∈ π.V, (∑ i : Fin a, GlobalTheory.CuspRep.Eop τ i i) φ = m.sum • φ := by
  intro φ hφ
  obtain ⟨hcard, hcap⟩ := h
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rw [Multiset.card_eq_zero.1 hcard]; simp
  set c : ℂ := ((a : ℂ) - 1) / 2 with hc
  set P := GroundTheory.BlockD.FourierDecayAlt.GaugeExists.qdetPoly (GlobalTheory.CuspRep.Eop (a := a) τ) with hPdef
  have hP : P.coeff (a - 1) = ∑ i, GlobalTheory.CuspRep.Eop τ i i -
      algebraMap ℂ (Module.End ℂ (GlobalTheory.CuspRep.Sm E a)) (((a : ℂ) * ((a : ℂ) - 1)) / 2) := by
    obtain ⟨-, -, hsub⟩ := GroundTheory.BlockD.FourierDecayAlt.GaugeExists.prod_linear a fun k =>
      GlobalTheory.CuspRep.Eop (a := a) τ k k - algebraMap ℂ (Module.End ℂ (GlobalTheory.CuspRep.Sm E a)) ((k : ℕ) : ℂ)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hPdef, GroundTheory.BlockD.FourierDecayAlt.GaugeExists.coeff_qdetPoly_top _ (a - 1) (by omega), hsub (a - 1) (by omega),
      Finset.sum_sub_distrib, ← map_sum, GroundTheory.BlockD.FourierDecayAlt.GaugeExists.sum_fin_cast]
  rw [← sub_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun ℓ => ?_
  let Q : ℂ[X] := ∑ j ∈ Finset.range (a + 1), C (ℓ (P.coeff j φ)) * X ^ j
  let R : ℂ[X] := C (ℓ φ) * (m.map fun z => X + C (z - c)).prod
  have hdeg : P.natDegree < a + 1 :=
    Nat.lt_succ_of_le (GroundTheory.BlockD.FourierDecayAlt.GaugeExists.natDegree_qdetPoly_le _)
  have hQ : ∀ v : ℂ, Q.eval v = ℓ ((GroundTheory.BlockD.FourierDecayAlt.GaugeExists.evU v P) φ) := by
    intro v
    set_option synthInstance.maxHeartbeats 100000 in
      rw [GroundTheory.BlockD.FourierDecayAlt.GaugeExists.evU_apply, eval₂_eq_sum_range' _ hdeg, LinearMap.sum_apply, map_sum,
      eval_finsetSum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [eval_mul, eval_C, eval_pow, eval_X, RingHom.id_apply, Module.End.mul_apply, ← map_pow,
      Module.algebraMap_end_apply, map_smul, map_smul, smul_eq_mul, mul_comm]
  have hQR : Q = R := by
    refine Polynomial.funext fun v => ?_
    rw [hQ, GroundTheory.BlockD.FourierDecayAlt.GaugeExists.evU_qdetPoly]
    have e := hcap (v - c) φ hφ
    rw [GlobalTheory.CuspRep.cap, show v - c + ((a : ℂ) - 1) / 2 = v by rw [hc]; ring] at e
    rw [e, map_smul, smul_eq_mul]
    simp only [R, eval_mul, eval_C, eval_multiset_prod, Multiset.map_map, Function.comp_def, eval_add, eval_X]
    rw [mul_comm]
    congr 2
    refine Multiset.map_congr rfl fun z _ => ?_
    ring
  have hco := congrArg (fun p : ℂ[X] => p.coeff (a - 1)) hQR
  have hlt : a - 1 ∈ Finset.range (a + 1) := Finset.mem_range.2 (by omega)
  simp only [Q, R, finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', if_pos hlt] at hco
  have hm : (m.map fun z => X + C (z - c)).prod =
      ((m.map fun z => z - c).map fun r => X + C r).prod := by rw [Multiset.map_map]; rfl
  rw [hm, Multiset.prod_X_add_C_coeff _ (by simp [hcard]), Multiset.card_map, hcard,
    show a - (a - 1) = 1 by omega, Multiset.esymm, Multiset.powersetCard_one, Multiset.map_map] at hco
  simp only [Function.comp_def, Multiset.prod_singleton, Multiset.map_id', Multiset.sum_map_sub,
    Multiset.map_const', Multiset.sum_replicate, hcard, nsmul_eq_mul] at hco
  rw [hP] at hco
  simp only [LinearMap.sub_apply, map_sub, Module.algebraMap_end_apply, map_smul, smul_eq_mul] at hco ⊢
  rw [hc] at hco
  linear_combination hco

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalTraceMatrixUnitsActsBySumInfinitesimalChStatement
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_traceMatrixUnits_acts_by_sum_infinitesimalCharacter : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : GlobalTheory.CuspRep.CuspSub E a) (τ : E →+* ℂ) (m : Multiset ℂ), π.HasInfChar τ m → ∀ φ ∈ π.V, (∑ i : Fin a, GlobalTheory.CuspRep.Eop τ i i) φ = m.sum • φ := by
  first | exact @GlobalTheory.trace_Eop_of_hasInfChar | exact GlobalTheory.trace_Eop_of_hasInfChar | (intros; apply GlobalTheory.trace_Eop_of_hasInfChar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsModelOfMem
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.WeilDeligne GlobalTheory.Pst

noncomputable section

namespace GlobalTheory.AboveLRes

theorem exists_model_of_mem {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] {a : ℕ} (T : FinExt l)
    (ρ : Γ →* GL (Fin a) (Om l))
    (hρ : ∀ g i k, ((ρ g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i k ∈ T.1) :
    ∃ ρ' : Γ →* GL (Fin a) ↥T.1, mapRep (algebraMap ↥T.1 (Om l)) ρ' = ρ := by
  let f : GL (Fin a) ↥T.1 →* GL (Fin a) (Om l) := Units.map ((algebraMap ↥T.1 (Om l)).mapMatrix : Matrix (Fin a) (Fin a) ↥T.1 →+* Matrix (Fin a) (Fin a) (Om l)).toMonoidHom
  have hmi : Function.Injective ((algebraMap ↥T.1 (Om l)).mapMatrix : Matrix (Fin a) (Fin a) ↥T.1 → _) :=
    Matrix.map_injective (algebraMap ↥T.1 (Om l)).injective
  have hf : Function.Injective f := Units.map_injective hmi
  let lift : Γ → Matrix (Fin a) (Fin a) ↥T.1 := fun g => Matrix.of fun i k => ⟨_, hρ g i k⟩
  have hlift : ∀ g, (algebraMap ↥T.1 (Om l)).mapMatrix (lift g) = ((ρ g : GL (Fin a) (Om l)) : Matrix _ _ _) :=
    fun g => by ext i k; rfl
  have hm : ∀ g, ρ g ∈ f.range := by
    intro g
    refine ⟨⟨lift g, lift g⁻¹, hmi ?_, hmi ?_⟩, Units.ext (hlift g)⟩
    · rw [map_mul, hlift, hlift, map_one, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
    · rw [map_mul, hlift, hlift, map_one, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  refine ⟨(MonoidHom.ofInjective hf).symm.toMonoidHom.comp (ρ.codRestrict f.range hm), ?_⟩
  exact MonoidHom.ext fun g => MonoidHom.apply_ofInjective_symm hf ⟨ρ g, hm g⟩

end GlobalTheory.AboveLRes

namespace GlobalTheory.AboveLRes

theorem exists_decRes_eq {K L Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [Field L] [NumberField L]
    [Algebra L Ω] [Algebra K L] [IsScalarTower K L Ω] {A : ValuationSubring Ω} (σ : ↥(Dec (F := K) A))
    (hσ : ∀ x : L, (σ : G K Ω) (algebraMap L Ω x) = algebraMap L Ω x) :
    ∃ σ' : ↥(Dec (F := L) A), decRes A σ' = σ := by
  let τ : G L Ω := { (σ : G K Ω).toRingEquiv with commutes' := hσ }
  have hτ : τ ∈ Dec (F := L) A := by
    have hg := mem_Dec.mp σ.2
    rw [mem_Dec]
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    conv_rhs => rw [← hg, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    rfl
  exact ⟨⟨τ, hτ⟩, Subtype.ext (AlgEquiv.ext fun _ => rfl)⟩

end GlobalTheory.AboveLRes

namespace GlobalTheory.AboveLRes


open GlobalTheory.AboveL in
theorem exists_model_dec {K L Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
    [Field L] [NumberField L] [Algebra L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) {l : ℕ}
    [Fact l.Prime] {a : ℕ} (r : G K Ω →* GL (Fin a) (Om l)) (LL' B : FinExt l)
    (r' : ↥(Dec (F := L) A) →* GL (Fin a) ↥LL'.1)
    (hm' : mapRep (algebraMap ↥LL'.1 (Om l)) r' = (resTo L r).comp (Dec (F := L) A).subtype) :
    ∃ (T : FinExt l) (r₁ : ↥(Dec (F := K) A) →* GL (Fin a) ↥T.1), B.1 ≤ T.1 ∧
      mapRep (algebraMap ↥T.1 (Om l)) r₁ = r.comp (Dec (F := K) A).subtype := by
  let M : IntermediateField K Ω := (IsScalarTower.toAlgHom K L Ω).fieldRange
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  haveI : FiniteDimensional K M :=
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom K L Ω)).toLinearEquiv.finiteDimensional
  haveI : Finite (G K Ω ⧸ M.fixingSubgroup) := Subgroup.quotient_finite_of_isOpen _ M.fixingSubgroup_isOpen
  haveI : M.fixingSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  set H : Subgroup ↥(Dec (F := K) A) := M.fixingSubgroup.subgroupOf (Dec (F := K) A) with hH
  haveI : Finite (↥(Dec (F := K) A) ⧸ H) := Subgroup.finite_quotient_of_finiteIndex
  set S : Set (Om l) := Set.range fun x : (↥(Dec (F := K) A) ⧸ H) × Fin a × Fin a =>
    ((r (x.1.out : G K Ω) : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) x.2.1 x.2.2 with hS
  have hSf : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] S) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  obtain ⟨T, hT⟩ : ∃ T : FinExt l, T.1 = IntermediateField.adjoin ℚ_[l] S ⊔ LL'.1 ⊔ B.1 :=
    ⟨supExt (supExt ⟨_, hSf⟩ LL') B, rfl⟩
  have hET : IntermediateField.adjoin ℚ_[l] S ≤ T.1 := hT ▸ le_sup_left.trans le_sup_left
  have hLT : LL'.1 ≤ T.1 := hT ▸ le_sup_right.trans le_sup_left
  have hBT : B.1 ≤ T.1 := hT ▸ le_sup_right
  have hfix : ∀ σ : ↥(Dec (F := K) A), σ ∈ H → ∀ i k,
      ((r (σ : G K Ω) : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i k ∈ LL'.1 := by
    intro σ hσ i k
    have hσ' : ∀ x : L, (σ : G K Ω) (algebraMap L Ω x) = algebraMap L Ω x := fun x =>
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 (Subgroup.mem_subgroupOf.1 hσ) _ ⟨x, rfl⟩
    obtain ⟨τ, hτ⟩ := exists_decRes_eq σ hσ'
    have e1 : (r (σ : G K Ω)) = ((resTo L r).comp (Dec (F := L) A).subtype) τ := by
      rw [← hτ]; rfl
    rw [e1, ← hm']
    exact ((r' τ : GL (Fin a) ↥LL'.1) : Matrix (Fin a) (Fin a) ↥LL'.1) i k |>.2
  have hent : ∀ (g : ↥(Dec (F := K) A)) i k,
      (((r.comp (Dec (F := K) A).subtype) g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i k ∈ T.1 := by
    intro g i k
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
    have hg : g = (QuotientGroup.mk g : ↥(Dec (F := K) A) ⧸ H).out * ((h⁻¹ : H) : ↥(Dec (F := K) A)) := by
      rw [hh, Subgroup.coe_inv, mul_inv_cancel_right]
    rw [MonoidHom.comp_apply, hg, map_mul, map_mul, Units.val_mul, Matrix.mul_apply]
    refine sum_mem fun m _ => mul_mem (hET (IntermediateField.subset_adjoin _ _ ⟨⟨_, i, m⟩, rfl⟩)) ?_
    exact hLT (hfix _ (h⁻¹).2 m k)
  obtain ⟨r₁, hr₁⟩ := exists_model_of_mem T _ hent
  exact ⟨T, r₁, hBT, hr₁⟩

end GlobalTheory.AboveLRes

namespace GlobalTheory.AboveLRes


open GlobalTheory.AboveL in
theorem isPstAt_of_resTo : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (a : ℕ) (r : G K Ω →* GL (Fin a) (Om l)), Continuous r → ∀ (O O' : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] [CommRing O'] [Algebra ℤ_[l] O'] [TopologicalSpace O'] (Bw : LocBridge l K Ω (Dec (F := K) A) O) (Bw' : LocBridge l L Ω (Dec (F := L) A) O'), GlobalTheory.Pst.Induces Bw → GlobalTheory.Pst.Induces Bw' → IsPstAt P Bw' ((GlobalTheory.AboveL.resTo L r).comp (Dec (F := L) A).subtype) → IsPstAt P Bw (r.comp (Dec (F := K) A).subtype) := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ A l _ P AI hT a r hr O O' _ _ _ _ _ _ Bw Bw' hj hj' hL
  have hcL : Continuous fun g : ↥(Dec (F := L) A) =>
      ((((resTo L r).comp (Dec (F := L) A).subtype) g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) :=
    Units.continuous_val.comp ((hr.comp (UpperTheory.V.Af.continuous_restrictScalarsHom K L Ω)).comp continuous_subtype_val)
  obtain ⟨LL', r', hm', hV'⟩ := hL
  obtain ⟨T, r₁, hBT, hr₁⟩ := exists_model_dec A r LL' Bw.LL r' hm'.2

  obtain ⟨S'', Bw'', hjj, hTS, hle⟩ := exists_bridge (L := L) Bw hj T
  have hj'' : GlobalTheory.Pst.Induces Bw'' := fun x => by rw [hjj]; exact hj x
  obtain ⟨LL₃, r₃, hm₃, hV₃⟩ := GlobalTheory.Pst.PstBridge.isPstAt_indep_bridge l P AI hT L Ω A O' _ Bw' Bw'' hj' hj'' a _
    hcL ⟨LL', r', hm', hV'⟩
  have h1 : Bw''.LL.1 ≤ (supExt Bw''.LL LL₃).1 := le_sup_left
  have h3 : LL₃.1 ≤ (supExt Bw''.LL LL₃).1 := le_sup_right
  have hTT : T.1 ≤ (supExt Bw''.LL LL₃).1 := hTS.trans h1
  have hr₁' : mapRep (algebraMap ↥(supExt Bw''.LL LL₃).1 (Om l))
      (mapRep (IntermediateField.inclusion hTT).toRingHom r₁) = r.comp (Dec (F := K) A).subtype := by
    ext g i k
    exact congrArg (fun f : ↥(Dec (F := K) A) →* GL (Fin a) (Om l) =>
      ((f g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i k) hr₁
  have hmL : IsModel Bw'' ((resTo L r).comp (Dec (F := L) A).subtype) (supExt Bw''.LL LL₃)
      ((mapRep (IntermediateField.inclusion hTT).toRingHom r₁).comp (decRes A)) := by
    refine ⟨h1, ?_⟩
    ext g i k
    exact congrArg (fun f : ↥(Dec (F := K) A) →* GL (Fin a) (Om l) =>
      ((f (decRes A g) : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i k) hr₁'
  have hm₃' : IsModel Bw'' ((resTo L r).comp (Dec (F := L) A).subtype) (supExt Bw''.LL LL₃)
      (mapRep (IntermediateField.inclusion h3).toRingHom r₃) := by
    refine ⟨hm₃.1.trans h3, ?_⟩
    ext g i k
    exact congrArg (fun f : ↥(Dec (F := L) A) →* GL (Fin a) (Om l) =>
      ((f g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i k) hm₃.2
  have heq := IsModel.unique Bw'' _ hm₃' hmL
  have hp := GlobalTheory.PstExt.isPst_enlarge P Bw'' h3 r₃ hV₃
  rw [heq, repE_decRes Bw Bw'' hjj hle] at hp
  exact ⟨_, _, ⟨hBT.trans hTT, hr₁'⟩, (GlobalTheory.PstLaws.isPst_resTo_iff P _ hle).1 hp⟩

end GlobalTheory.AboveLRes
end
end
