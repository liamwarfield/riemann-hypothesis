module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
public import Formalism.LocalToGlobal.IndefiniteReal.BridgeColPts
public import Formalism.LocalToGlobal.Columns.InputsGenus
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CorrectionOfTransport
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LabelSettingTameGenerator
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryAdelicTwistDiagonalAtPrimes
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
public import Formalism.LocalToGlobal.NumberFieldFamilies.HeckeStd0Of

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TranslatedStdLatticeEqDecoratedLatticeReindexed
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TranslatedStdLatticeEqDecoratedLatticeReindexed
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.Mem.R3.LiftLatStd

theorem hLat_eq_decoPt_N : ∀ (X : Stages) (i : Fin X.toD7.R.m) (Λ : Submodule (𝓞 X.toD7.host.E) (Fin (Vc X.toD7 i).rank → X.toD7.host.E)),
    IsSDFrame (Vc X.toD7 i) 1 Λ 1 → ∀ (SG : Finset (Pl X.toD7.host.E))
    (eG : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV ≃* Bridge.Gf (Vc X.toD7 i)),
    (∀ x, LiftBrg.castGL (LiftBrg.rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7)
          ((eG x : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.toD7.host.F ⊗[X.toD7.host.F] X.toD7.host.E))) =
        (x : GL (Fin X.B.R.nV) (LiftBrg.EA X))) →
    ∀ x : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV,
      Bridge.hLat (Vc X.toD7 i) (eG x) =
        (Formalism.L2.Col.decoPt X.toD7.sp.cm X.B.R.nV ∅ SG (QuotientGroup.mk x)).1.N.map
          (LinearEquiv.funCongrLeft (𝓞 X.toD7.host.E) X.toD7.host.E (finCongr (LiftBrg.rkEq X i)).symm).toLinearMap := by
  intro X i Λ hΛ SG eG hx x
  have hΛ' := hΛ
  obtain ⟨c, hfr, -⟩ := hΛ'
  rw [GlobalTheory.HLatMove.hLat_eq_span hΛ, Formalism.L2.Col.decoPt_mk]
  unfold Formalism.L2.Col.decoOf
  rw [dite_eq_left (Formalism.L2.Col.decorated_lattice_exists _ _ _ _ _ x.2)]
  set h := eG x with hh
  set g := Formalism.UG.bc (swapAE X.toD7) (h : GL (Fin (Vc X.toD7 i).rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.toD7.host.F ⊗[X.toD7.host.F] X.toD7.host.E)) with hg
  have hxg : (x : GL (Fin X.B.R.nV) (LiftBrg.EA X)) = LiftBrg.castGL (LiftBrg.rkEq X i).symm g := (hx x).symm
  have hL : ∀ y : Fin (Vc X.toD7 i).rank → X.toD7.host.E,
      (h.1⁻¹).1 *ᵥ (fun j => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.toD7.host.F) ⊗ₜ[X.toD7.host.F] y j) ∈
          GlobalTheory.AdLat.hat X.toD7.host.F (Λ : Set (Fin (Vc X.toD7 i).rank → X.toD7.host.E)) ↔
        ∀ j, ((g⁻¹).1 *ᵥ (fun k => Formalism.L2.Col.iA X.toD7.host.F X.toD7.host.E (y k))) j ∈
          Formalism.L2.Herm.intAf X.toD7.host.F X.toD7.host.E := by
    intro y
    have e : ((g⁻¹).1 *ᵥ (fun k => Formalism.L2.Col.iA X.toD7.host.F X.toD7.host.E (y k))) =
        fun j => Algebra.TensorProduct.comm X.toD7.host.F _ X.toD7.host.E
          (((h.1⁻¹).1 *ᵥ (fun k => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.toD7.host.F) ⊗ₜ[X.toD7.host.F] y k)) j) := by
      rw [hg, ← map_inv]
      funext j
      change _ = swapAE X.toD7 _
      rw [RingHom.map_mulVec (swapAE X.toD7)]
      rfl
    have e1 := hfr ((g⁻¹).1 *ᵥ (fun k => Formalism.L2.Col.iA X.toD7.host.F X.toD7.host.E (y k)))
    rw [inv_one, Units.val_one, Matrix.one_mulVec] at e1
    rw [← e1, e]
    constructor
    · intro hz
      exact GlobalTheory.PrincInLevel.swap_mem_hatL Λ _ hz
    · intro hz
      have := GlobalTheory.PrincInLevel.swap_symm_mem_hat Λ _ hz
      simpa only [AlgEquiv.symm_apply_apply] using this
  have hR : ∀ y : Fin (Vc X.toD7 i).rank → X.toD7.host.E,
      y ∈ (Formalism.UG.CS.globLat (x : GL (Fin X.B.R.nV) (LiftBrg.EA X)) (Formalism.L2.Col.stdLat X.toD7.host.E X.B.R.nV)).map
          (LinearEquiv.funCongrLeft (𝓞 X.toD7.host.E) X.toD7.host.E (finCongr (LiftBrg.rkEq X i)).symm).toLinearMap ↔
        ∀ j, ((g⁻¹).1 *ᵥ (fun k => Formalism.L2.Col.iA X.toD7.host.F X.toD7.host.E (y k))) j ∈
          Formalism.L2.Herm.intAf X.toD7.host.F X.toD7.host.E := by
    intro y
    rw [Submodule.mem_map_equiv, LinearEquiv.funCongrLeft_symm, Formalism.L2.Col.mem_globLat]
    unfold Formalism.L2.Col.pullV
    rw [hxg, ← map_inv]
    simp only [LiftBrg.castGL, Units.coe_mapEquiv, Equiv.symm_symm, LinearEquiv.funCongrLeft_apply]
    simp only [LinearMap.funLeft_apply]
    have e2 : ∀ (M : Matrix (Fin (Vc X.toD7 i).rank) (Fin (Vc X.toD7 i).rank) (Lev.EAf X.toD7)),
        ((Matrix.reindexAlgEquiv (Lev.EAf X.toD7) (Lev.EAf X.toD7) (finCongr (LiftBrg.rkEq X i).symm)).toRingEquiv.toMulEquiv M) *ᵥ
          (fun a => Formalism.L2.Col.iA X.toD7.host.F X.toD7.host.E (y (finCongr (LiftBrg.rkEq X i) a))) =
        fun a => (M *ᵥ fun k => Formalism.L2.Col.iA X.toD7.host.F X.toD7.host.E (y k)) (finCongr (LiftBrg.rkEq X i) a) := by
      intro M
      change Matrix.reindexAlgEquiv (Lev.EAf X.toD7) (Lev.EAf X.toD7) (finCongr (LiftBrg.rkEq X i).symm) M *ᵥ _ = _
      rw [Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
      funext a
      simp [Function.comp_def]
    rw [e2]
    exact ⟨fun H j => by simpa using H ((finCongr (LiftBrg.rkEq X i)).symm j), fun H a => H _⟩
  refine le_antisymm (Submodule.span_le.2 fun y hy => (hR y).2 ((hL y).1 hy)) fun y hy => Submodule.subset_span ((hL y).2 ((hR y).1 hy))

end GlobalTheory.Mem.R3.LiftLatStd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TranslatedStdLatticeEqDecoratedLatticeReindexedStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translatedStdLattice_eq_decoratedLattice_reindexed : ∀ (X : Stages) (i : Fin X.toD7.R.m) (Λ : Submodule (𝓞 X.toD7.host.E) (Fin (Vc X.toD7 i).rank → X.toD7.host.E)),
    IsSDFrame (Vc X.toD7 i) 1 Λ 1 → ∀ (SG : Finset (Pl X.toD7.host.E))
    (eG : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV ≃* Bridge.Gf (Vc X.toD7 i)),
    (∀ x, LiftBrg.castGL (LiftBrg.rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7)
          ((eG x : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.toD7.host.F ⊗[X.toD7.host.F] X.toD7.host.E))) =
        (x : GL (Fin X.B.R.nV) (LiftBrg.EA X))) →
    ∀ x : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV,
      Bridge.hLat (Vc X.toD7 i) (eG x) =
        (Formalism.L2.Col.decoPt X.toD7.sp.cm X.B.R.nV ∅ SG (QuotientGroup.mk x)).1.N.map
          (LinearEquiv.funCongrLeft (𝓞 X.toD7.host.E) X.toD7.host.E (finCongr (LiftBrg.rkEq X i)).symm).toLinearMap := by
  first | exact @GlobalTheory.Mem.R3.LiftLatStd.hLat_eq_decoPt_N | exact GlobalTheory.Mem.R3.LiftLatStd.hLat_eq_decoPt_N | (intros; apply GlobalTheory.Mem.R3.LiftLatStd.hLat_eq_decoPt_N <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NatPrimeNotMem
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NatCastNotMemOfPrimeNe
namespace GlobalTheory.NatCastNotMemPrime

theorem natCast_notMem_of_prime_ne {A : Type} [inst : CommRing A] (P : Ideal A)
    [hP : Ideal.IsPrime P] {p l : ℕ} (hp : Nat.Prime p) (hl : Nat.Prime l) (hne : l ≠ p)
    (hpP : (↑p : A) ∈ P) : (↑l : A) ∉ P := by
  intro hlP
  have hcop : Nat.Coprime l p := (Nat.coprime_primes hl hp).2 hne
  have hc : IsCoprime (l : A) (p : A) := Nat.Coprime.cast hcop
  obtain ⟨a, b, hab⟩ := hc
  apply hP.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  exact P.add_mem (P.mul_mem_left a hlP) (P.mul_mem_left b hpP)

end GlobalTheory.NatCastNotMemPrime
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.TwistPlaces

theorem natPrime_not_mem {A : Type} [CommRing A] (P : Ideal A) [hP : P.IsPrime] {p l : ℕ} (hp : p.Prime) (hl : l.Prime)
    (hne : l ≠ p) (hpP : (p : A) ∈ P) : (l : A) ∉ P :=
  _root_.GlobalTheory.NatCastNotMemPrime.natCast_notMem_of_prime_ne P hp hl hne hpP

theorem twistPlaces : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px), I.Ok → ∀ a : I.ι,
    (∀ PP ∈ I.Q a, ¬ (I.xi a).UnrAt PP) → Formalism.IndefR.Lev.IsTwistPlaces (D := X.toD7) X.toD7.host.g (I.Q a) ∧
    ∀ PP ∈ I.Q a, ((X.toD7.host.QS * X.toD7.host.q * X.toD7.host.d * X.toD7.sp.T : ℕ) : 𝓞 X.toD7.host.E) ∉ PP.asIdeal ∧
      ∀ u : X.toD7.what₂.Word, (((X.toD7.mem u).A.T : ℕ) : 𝓞 X.toD7.host.E) ∉ PP.asIdeal := by
  intro X px I hI a hU
  have htw := (GlobalTheory.Mem.ReadTwist.isTwist_of_reads X.B.R X.B.host _ X.B.embLL I.S (I.tup a) (I.xi a) (hI.xi_reads a)).1
  have key := fun PP (hPP : PP ∈ I.Q a) => htw.2.2.2 PP (hU PP hPP)
  have hstar : ∀ x : X.B.host.E, star x = X.B.host.conj x := bridge_star_holds X.B.R X.B.host

  have off : ∀ PP ∈ I.Q a, ∀ l : ℕ, l.Prime → l ∈ I.S → ((l : ℕ) : 𝓞 X.B.host.E) ∉ PP.asIdeal := by
    intro PP hPP l hl hS
    obtain ⟨-, hp, -, hpS⟩ := key PP hPP
    exact natPrime_not_mem PP.asIdeal hp hl (fun e => hpS (e ▸ hS)) (Ideal.absNorm_mem PP.asIdeal)
  refine ⟨fun PP hPP => ⟨?_, fun PP' hPP' hc => ?_⟩, fun PP hPP => ⟨?_, fun u => ?_⟩⟩
  · obtain ⟨-, hp, hsq, hpS⟩ := key PP hPP
    refine ⟨Ideal.absNorm PP.asIdeal, hp, ?_, hsq, fun i e => hpS (e ▸ hI.g_mem i)⟩
    show Nat.card (𝓞 X.B.host.E ⧸ PP.asIdeal) = Ideal.absNorm PP.asIdeal
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  · obtain ⟨v, -, rfl, -⟩ := I.exists_of_mem_Q hPP
    obtain ⟨v', -, rfl, -⟩ := I.exists_of_mem_Q hPP'
    have hle : v.asIdeal ≤ v'.asIdeal := by
      intro c hc'
      have h1 : algebraMap (𝓞 X.B.host.F) (𝓞 X.B.host.E) c ∈ (I.sel v).asIdeal := by
        have := hI.sel_ok v
        rw [← this] at hc'
        exact hc'
      obtain ⟨c', h2, h3⟩ := hc _ h1
      have h4 : c' = algebraMap (𝓞 X.B.host.F) (𝓞 X.B.host.E) c := by
        apply RingOfIntegers.ext
        rw [h3]
        show star (algebraMap X.B.host.F X.B.host.E (c : X.B.host.F)) = algebraMap X.B.host.F X.B.host.E (c : X.B.host.F)
        rw [hstar, ← X.B.conjF_eq, AlgHom.commutes]
      rw [h4] at h2
      rw [← hI.sel_ok v']
      exact h2
    have hv : v = v' := HeightOneSpectrum.ext (v.isMaximal.eq_of_le v'.isPrime.ne_top hle)
    subst hv
    obtain ⟨⟨x, hx, hy⟩, -⟩ := key _ hPP
    obtain ⟨c', h2, h3⟩ := hc x hx
    exact hy c' (h3.trans (hstar _)) h2
  · have hp2 : ((X.B.host.QS : ℕ) : 𝓞 X.B.host.E) ∉ PP.asIdeal := fun h => by
      rw [← Nat.prod_primeFactorsList X.B.host.QS_pos.ne', Nat.cast_list_prod] at h
      have := PP.isPrime
      obtain ⟨a, ha, h'⟩ := (Ideal.IsPrime.multiset_prod_mem_iff_exists_mem PP.isPrime
        ((X.B.host.QS.primeFactorsList.map Nat.cast : List (𝓞 X.B.host.E)) : Multiset _)).1 (by simpa using h)
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 (Multiset.mem_coe.1 ha)
      exact off PP hPP l (Nat.prime_of_mem_primeFactorsList hl)
        (hI.mem_of_dvd_QS (Nat.prime_of_mem_primeFactorsList hl) (Nat.dvd_of_mem_primeFactorsList hl)) h'
    have hq : ((X.B.host.q : ℕ) : 𝓞 X.B.host.E) ∉ PP.asIdeal := off PP hPP _ X.B.host.hyp.1 hI.two_q_d_mem.2.1
    have hd : ((X.B.host.d : ℕ) : 𝓞 X.B.host.E) ∉ PP.asIdeal := off PP hPP _ X.B.host.hyp.2.1 hI.two_q_d_mem.2.2
    have hT : ((X.B.T X.B.u₀ : ℕ) : 𝓞 X.B.host.E) ∉ PP.asIdeal :=
      off PP hPP _ (X.B.T_prime X.B.u₀) (hI.T_mem X.B.u₀)
    have hsp : X.toD7.sp.T = X.B.T X.B.u₀ := X.B.sp_T
    rw [hsp]
    show ((X.B.host.QS * X.B.host.q * X.B.host.d * X.B.T X.B.u₀ : ℕ) : 𝓞 X.B.host.E) ∉ PP.asIdeal
    have hPr := PP.isPrime
    push_cast
    intro h
    rcases hPr.mem_or_mem h with h | h
    · rcases hPr.mem_or_mem h with h | h
      · rcases hPr.mem_or_mem h with h | h
        · exact hp2 (by exact_mod_cast h)
        · exact hq h
      · exact hd h
    · exact hT h
  · have hA : (X.toD7.mem u).A.T = X.B.T u := X.C.A_T u
    rw [hA]
    exact off PP hPP _ (X.B.T_prime u) (hI.T_mem u)

end GlobalTheory.Mem.TwistPlaces
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteAdelicUnitaryConjIntegralFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteAdelicUnitaryConjIntegralFrame
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg

noncomputable section

set_option maxHeartbeats 1000000

namespace GlobalTheory.Mem.R3.LiftBrg.FrameEquiv

theorem castGL_castGL_symm {R : Type} [CommRing R] {m n : ℕ} (h : m = n) (x : GL (Fin n) R) :
    castGL h (castGL h.symm x) = x := by
  subst h
  ext i j
  simp [castGL]

theorem bc_swapAE_injective (D : D7) (m : ℕ) :
    Function.Injective (Formalism.UG.bc (n := Fin m) (swapAE D)) := by
  intro a b h
  have hs : Function.Injective (swapAE D) := fun x y hxy =>
    (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).injective hxy
  ext i j
  have := congrArg (fun g : GL (Fin m) (Formalism.IndefR.Lev.EAf D) => g.val i j) h
  exact hs this

theorem frame_equiv : ∀ (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (EA X)) (hF : FrameOK X I U i t A k),
    ∃ Φ : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV ≃* Bridge.Gf (Vc X.toD7 i), ∀ u,
      castGL (rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7) ((Φ u : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _)) = A * k * (u : GL (Fin X.B.R.nV) (EA X)) * (A * k)⁻¹ := by
  intro X px I hX U Xg tr L i t A k hF
  obtain ⟨-, -, h3, hk, -, -⟩ := hF
  set V := Vc X.toD7 i
  set h := rkEq X i
  set G := Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV
  let c : Bridge.Gf V →* GL (Fin X.B.R.nV) (EA X) :=
    (castGL h.symm).toMonoidHom.comp ((Formalism.UG.bc (swapAE X.toD7)).comp (Bridge.Gf V).subtype)
  have hc : ∀ g, c g = castGL h.symm (Formalism.UG.bc (swapAE X.toD7) (g : GL (Fin V.rank) _)) := fun _ => rfl
  have hmem : ∀ g : Bridge.Gf V, (A * k)⁻¹ * c g * (A * k) ∈ G := by
    intro g
    have hUA : Formalism.UG.bc (swapAE X.toD7) (g : GL (Fin V.rank) _) ∈ UA X.toD7.sp.cm V.gram := by
      obtain ⟨κ, hκ⟩ := g.2
      rw [← hκ]
      exact GlobalTheory.LevFinCong.finE_mem_UA V κ
    have hx : A⁻¹ * c g * A ∈ G := by
      rw [h3]
      have e : A * (A⁻¹ * c g * A) * A⁻¹ = c g := by group
      rw [e, hc, castGL_castGL_symm]
      exact hUA
    have e2 : (A * k)⁻¹ * c g * (A * k) = k⁻¹ * (A⁻¹ * c g * A) * k := by group
    rw [e2]
    exact G.mul_mem (G.mul_mem (G.inv_mem hk) hx) hk
  let ψ : Bridge.Gf V →* G :=
    { toFun := fun g => ⟨(A * k)⁻¹ * c g * (A * k), hmem g⟩
      map_one' := by ext1; simp
      map_mul' := fun a b => by ext1; simp only [map_mul, Subgroup.coe_mul]; group }
  have hψ : ∀ g, ((ψ g : G) : GL (Fin X.B.R.nV) (EA X)) = (A * k)⁻¹ * c g * (A * k) := fun _ => rfl
  have hinj : Function.Injective ψ := by
    intro a b hab
    have e := congrArg (fun x : G => (x : GL (Fin X.B.R.nV) (EA X))) hab
    simp only [hψ, mul_left_inj, mul_right_inj] at e
    rw [hc, hc] at e
    have e' := (castGL h.symm).injective e
    exact Subtype.ext (bc_swapAE_injective X.toD7 V.rank e')
  have hsurj : Function.Surjective ψ := by
    intro u
    have hku : k * (u : GL (Fin X.B.R.nV) (EA X)) * k⁻¹ ∈ G := G.mul_mem (G.mul_mem hk u.2) (G.inv_mem hk)
    have hw := (h3 _).1 hku
    obtain ⟨κ, -, hκ⟩ := GlobalTheory.AdIsomCorrection.exists_finE V _ hw
    refine ⟨⟨finHom V κ, κ, rfl⟩, ?_⟩
    ext1
    rw [hψ, hc]
    change (A * k)⁻¹ * castGL h.symm (finE V κ) * (A * k) = _
    rw [hκ, castGL_castGL_symm h.symm]
    group
  have hbij : Function.Bijective ψ := ⟨hinj, hsurj⟩
  let Ψ := MulEquiv.ofBijective ψ hbij
  refine ⟨Ψ.symm, fun u => ?_⟩
  have e0 : ψ (Ψ.symm u) = u := Ψ.apply_symm_apply u
  have e := congrArg (fun x : G => (x : GL (Fin X.B.R.nV) (EA X))) e0
  simp only [hψ] at e
  rw [← hc, ← e]
  group

end GlobalTheory.Mem.R3.LiftBrg.FrameEquiv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteAdelicUnitaryConjIntegralFrameStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteAdelicUnitary_conj_integralFrame : ∀ (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (EA X)) (hF : FrameOK X I U i t A k),
    ∃ Φ : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV ≃* Bridge.Gf (Vc X.toD7 i), ∀ u,
      castGL (rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7) ((Φ u : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _)) = A * k * (u : GL (Fin X.B.R.nV) (EA X)) * (A * k)⁻¹ := by
  first | exact @GlobalTheory.Mem.R3.LiftBrg.FrameEquiv.frame_equiv | exact GlobalTheory.Mem.R3.LiftBrg.FrameEquiv.frame_equiv | (intros; apply GlobalTheory.Mem.R3.LiftBrg.FrameEquiv.frame_equiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistLiftFormsEqBaseChangeRationalDatumForms
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistLiftFormsEqBaseChangeRationalDatumForms
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HeightCounting.FormsStep

theorem formsExport_eq : ∀ (D : D7) (S : RatDat D.ntw) (In : RatIn D S) (T : TwR D.LL0 D.nd) (hE : IsEmpty D.nd.Loc)
    (hfg : ∀ i j b, (BsupT D T S i j b).FG) (hst : HkStab D T S In) (sd : SigData D T) (rho : RhoFam D T)
    (hrho : ∀ i σ b, Continuous fun g =>
      ((rho i σ b g : GL (Fin D.R.r) (T.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (T.O0 i))) (he : EIdem D)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (wt : WtData D T)
    (i : (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T)).Tw) (j : ℕ) (b : Bool) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m),
    ∃ e : (mkEx D T S In hE hfg hst sd rho hrho he Pq wt).Fm i j b ≃ₗ[FractionRing ((T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T)).O i)]
        Fm ({ S with } : RatDat (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T))) i j b,
      (∀ x, x ∈ (mkEx D T S In hE hfg hst sd rho hrho he Pq wt).Bsup i j b ↔
        e x ∈ Bsup ({ S with } : RatDat (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T))) i j b) ∧
      (∀ g x, e ((mkEx D T S In hE hfg hst sd rho hrho he Pq wt).actG i j b g x) =
        actG ({ S with } : RatDat (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T))) i j b
          (In.rho j h1 h2) (In.chi j h1 h2) g (e x)) ∧
      ∀ k P x, e ((mkEx D T S In hE hfg hst sd rho hrho he Pq wt).hkF i j b k P x) =
        algebraMap ((T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T)).O i)
            (FractionRing ((T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T)).O i)) (cHkT D T i b P : T.O i) ^ k •
          GlobalTheory.HeightCounting.hkF D ({ S with } : RatDat (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T))) i j b
            (In.hL j) (In.hs j h1 h2) k P (e x) := by
  intro D S In T hE hfg hst sd rho hrho he Pq wt i j b h1 h2
  let i' : T.Tw := i
  have hW : WKr D S j = (S.A j).WK := WKr_of D S h1 h2
  let e : (KT D T i' b ⊗[S.Ks] ↥(WKr D S j)) ≃ₗ[KT D T i' b] (KT D T i' b ⊗[S.Ks] ↥(S.A j).WK) :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (KT D T i' b) (KT D T i' b)) (LinearEquiv.ofEq _ _ hW)
  have he1 : ∀ (a : KT D T i' b) (w : ↥(WKr D S j)), e (a ⊗ₜ[S.Ks] w) = a ⊗ₜ[S.Ks] (LinearEquiv.ofEq _ _ hW w) :=
    fun a w => rfl
  have hbc : ∀ (f : Module.End S.Ks ↥(WKr D S j)) (f' : Module.End S.Ks ↥(S.A j).WK),
      (∀ w, ((f w : ↥(WKr D S j)) : S.WL j) = (f' (LinearEquiv.ofEq _ _ hW w) : S.WL j)) →
      ∀ y, e (Module.End.baseChangeHom S.Ks (KT D T i' b) _ f y) = Module.End.baseChangeHom S.Ks (KT D T i' b) _ f' (e y) := by
    intro f f' hf y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a w =>
      show a ⊗ₜ[S.Ks] (LinearEquiv.ofEq _ _ hW (f w)) = a ⊗ₜ[S.Ks] (f' (LinearEquiv.ofEq _ _ hW w))
      exact congrArg (a ⊗ₜ[S.Ks] ·) (Subtype.ext (hf w))
    | add y z hy hz => rw [map_add (f := _), map_add (f := _), hy, hz, map_add (f := _), map_add (f := _)]
  have hc : ∀ g', cR D S In.chi j g' = chiL S j (In.chi j h1 h2) g' := fun g' => dif_pos ⟨h1, h2⟩
  have hsm : ∀ (r : T.O i') (y : KT D T i' b ⊗[S.Ks] ↥(WKr D S j)),
      e ((show KT D T i' b from algebraMap (T.O i') (FractionRing (T.O i')) r) • y) =
        (show KT D T i' b from algebraMap (T.O i') (FractionRing (T.O i')) r) • e y := fun r y => e.map_smul _ y
  have hsm' : ∀ (r : T.O i') (y : KT D T i' b ⊗[S.Ks] ↥(S.A j).WK),
      e.symm ((show KT D T i' b from algebraMap (T.O i') (FractionRing (T.O i')) r) • y) =
        (show KT D T i' b from algebraMap (T.O i') (FractionRing (T.O i')) r) • e.symm y := fun r y => e.symm.map_smul _ y
  refine ⟨e, ?_, ?_, ?_⟩
  · let eO : (mkEx D T S In hE hfg hst sd rho hrho he Pq wt).Fm i j b →ₗ[(T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T)).O i] Fm ({ S with } : RatDat (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T))) i j b :=
      { toFun := fun y => e y, map_add' := fun y z => e.map_add y z, map_smul' := fun r y => hsm r y }
    let eO' : Fm ({ S with } : RatDat (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T))) i j b →ₗ[(T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T)).O i] (mkEx D T S In hE hfg hst sd rho hrho he Pq wt).Fm i j b :=
      { toFun := fun y => e.symm y, map_add' := fun y z => e.symm.map_add y z, map_smul' := fun r y => hsm' r y }
    have hle1 : (mkEx D T S In hE hfg hst sd rho hrho he Pq wt).Bsup i j b ≤ (Bsup ({ S with } : RatDat (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T))) i j b).comap eO := by
      show BsupT D T S i' j b ≤ _
      refine Submodule.span_le.mpr ?_
      rintro y ⟨w, hw, rfl⟩
      exact (Submodule.subset_span ⟨LinearEquiv.ofEq _ _ hW w, hw, rfl⟩ : _ ∈ Bsup ({ S with } : RatDat (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T))) i j b)
    have hle2 : Bsup ({ S with } : RatDat (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T))) i j b ≤ ((mkEx D T S In hE hfg hst sd rho hrho he Pq wt).Bsup i j b).comap eO' := by
      refine Submodule.span_le.mpr ?_
      rintro y ⟨w, hw, rfl⟩
      exact (Submodule.subset_span ⟨(LinearEquiv.ofEq _ _ hW).symm w, hw, rfl⟩ : _ ∈ BsupT D T S i' j b)
    intro x
    refine ⟨fun hx => hle1 hx, fun hx => ?_⟩
    have h := hle2 hx
    rw [Submodule.mem_comap] at h
    change e.symm (e x) ∈ _ at h
    exact Eq.mp (congrArg (fun (z : (mkEx D T S In hE hfg hst sd rho hrho he Pq wt).Fm i j b) => z ∈ (mkEx D T S In hE hfg hst sd rho hrho he Pq wt).Bsup i j b) (e.symm_apply_apply x)) h
  · intro g x
    change e ((actEndT D T S In.rho In.chi i' j b (S.eG.symm g)) x) =
      (actEnd ({ S with } : RatDat (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T))) i j b (In.rho j h1 h2) (In.chi j h1 h2) (S.eG.symm g)) (e x)
    change e ((readK D T i' b (cR D S In.chi j (S.eG.symm g)))⁻¹ •
        Module.End.baseChangeHom S.Ks (KT D T i' b) ↥(WKr D S j) (rhoR D S In.rho j (S.eG.symm g)) x) =
      (readK D T i' b (chiL S j (In.chi j h1 h2) (S.eG.symm g)))⁻¹ •
        Module.End.baseChangeHom S.Ks (KT D T i' b) ↥(S.A j).WK (rhoKG S j (In.rho j h1 h2) (S.eG.symm g)) (e x)
    rw [LinearEquiv.map_smul, hbc _ (rhoKG S j (In.rho j h1 h2) (S.eG.symm g)) (fun w => rfl) x, hc]
  · intro k P x
    change e ((show KT D T i' b from algebraMap (T.O i') (FractionRing (T.O i')) (cHkT D T i' b P : T.O i')) ^ k •
        Module.End.baseChangeHom S.Ks (KT D T i' b) ↥(WKr D S j) (hLr D S In j k P) x) =
      (show KT D T i' b from algebraMap (T.O i') (FractionRing (T.O i')) (cHkT D T i' b P : T.O i')) ^ k •
        Module.End.baseChangeHom S.Ks (KT D T i' b) ↥(S.A j).WK
          (((In.hL j k P).restrictScalars S.Ks).restrict (p := (S.A j).WK) (q := (S.A j).WK)
            fun x hx => In.hs j h1 h2 k P x hx) (e x)
    rw [LinearEquiv.map_smul, hbc _ _ ?_ x]
    intro w
    rw [hLr, dif_pos ⟨h1, h2⟩]
    rfl

end GlobalTheory.HeightCounting.FormsStep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistLiftFormsEqBaseChangeRationalDatumFormsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistLiftForms_eq_baseChange_rationalDatumForms : ∀ (D : D7) (S : RatDat D.ntw) (In : RatIn D S) (T : TwR D.LL0 D.nd) (hE : IsEmpty D.nd.Loc)
    (hfg : ∀ i j b, (BsupT D T S i j b).FG) (hst : HkStab D T S In) (sd : SigData D T) (rho : RhoFam D T)
    (hrho : ∀ i σ b, Continuous fun g =>
      ((rho i σ b g : GL (Fin D.R.r) (T.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (T.O0 i))) (he : EIdem D)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (wt : WtData D T)
    (i : (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T)).Tw) (j : ℕ) (b : Bool) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m),
    ∃ e : (mkEx D T S In hE hfg hst sd rho hrho he Pq wt).Fm i j b ≃ₗ[FractionRing ((T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T)).O i)]
        Fm ({ S with } : RatDat (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T))) i j b,
      (∀ x, x ∈ (mkEx D T S In hE hfg hst sd rho hrho he Pq wt).Bsup i j b ↔
        e x ∈ Bsup ({ S with } : RatDat (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T))) i j b) ∧
      (∀ g x, e ((mkEx D T S In hE hfg hst sd rho hrho he Pq wt).actG i j b g x) =
        actG ({ S with } : RatDat (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T))) i j b
          (In.rho j h1 h2) (In.chi j h1 h2) g (e x)) ∧
      ∀ k P x, e ((mkEx D T S In hE hfg hst sd rho hrho he Pq wt).hkF i j b k P x) =
        algebraMap ((T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T)).O i)
            (FractionRing ((T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T)).O i)) (cHkT D T i b P : T.O i) ^ k •
          GlobalTheory.HeightCounting.hkF D ({ S with } : RatDat (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T))) i j b
            (In.hL j) (In.hs j h1 h2) k P (e x) := by
  first | exact @GlobalTheory.HeightCounting.FormsStep.formsExport_eq | exact GlobalTheory.HeightCounting.FormsStep.formsExport_eq | (intros; apply GlobalTheory.HeightCounting.FormsStep.formsExport_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameTransportEtaSupportedAtPlaceIdempotent
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportedAtConjPrimeIdempotentOfTrivialOffPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportedAtConjPrimeIdempotentOfTrivialOffPlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg

noncomputable section

namespace GlobalTheory.Mem.SuppOffPlace

section Gen

variable {F : Type} [Field F] [NumberField F] {E : Type} [CommRing E] [Algebra F E]

theorem prV_entry_eq_zero {n : ℕ} (g : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (w : HeightOneSpectrum (𝓞 F))
    (h : Formalism.UG.bc (Formalism.UG.prV (E := E) w) g = 1) (i j : Fin n) : Formalism.UG.prV (E := E) w ((g.val - 1) i j) = 0 := by
  have h1 : (Formalism.UG.bc (Formalism.UG.prV (E := E) w) g).val i j = (1 : GL (Fin n) (E ⊗[F] w.adicCompletion F)).val i j := by
    rw [h]
  rw [Formalism.UG.bc, Units.coe_map] at h1
  change Formalism.UG.prV (E := E) w (g.val i j) = (1 : Matrix (Fin n) (Fin n) (E ⊗[F] w.adicCompletion F)) i j at h1
  rw [Matrix.sub_apply, map_sub, h1, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem eps_mul_of_off (v : HeightOneSpectrum (𝓞 F)) {y : E ⊗[F] FiniteAdeleRing (𝓞 F) F}
    (hy : ∀ w, w ≠ v → Formalism.UG.prV (E := E) w y = 0) : Formalism.UG.P.afsplitEps E v * y = y := by
  rw [← sub_eq_zero]
  apply Formalism.UG.P.afsplit_inj
  intro w
  rw [map_sub, map_mul]
  by_cases h : w = v
  · subst h
    rw [Formalism.UG.P.afsplit_prV_eps, one_mul, sub_self]
  · rw [hy w h, mul_zero, sub_zero]

end Gen

variable {D : D7}

theorem belowPl_conjP {v : HeightOneSpectrum (𝓞 D.host.F)} {Pb : Formalism.L2.DIV.Pl D.host.E}
    (h : Formalism.L2.Col.IsOver v Pb) : Formalism.IndefR.Fin.belowPl (D := D) (Formalism.L2.Col.conjPrime₂ Pb) = v := by
  apply HeightOneSpectrum.ext
  rw [h]
  ext x
  show Formalism.L2.Col.cO D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) ∈ Pb.asIdeal ↔
    algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x ∈ Pb.asIdeal
  have : Formalism.L2.Col.cO D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x := by
    apply RingOfIntegers.ext
    show star ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x : 𝓞 D.host.E) : D.host.E) = _
    rw [show ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x : 𝓞 D.host.E) : D.host.E) = algebraMap D.host.F D.host.E (x : D.host.F) from rfl]
    exact (D.sp.cm.fixed _).2 ⟨_, rfl⟩
  rw [this]

theorem afsplitI_one (v : HeightOneSpectrum (𝓞 D.host.F)) :
    Formalism.UG.P.afsplitI v (1 : v.adicCompletion D.host.F) = Formalism.IndefR.Fin.sglV v 1 := by
  apply Formalism.IndefR.Fin.af_ext
  intro w
  by_cases hw : w = v
  · subst hw
    rw [Formalism.IndefR.Fin.sglV_same]
    exact Formalism.UG.P.afsplitI_self w 1
  · rw [Formalism.IndefR.Fin.sglV_ne v _ hw]
    exact Formalism.UG.P.afsplitI_ne v w hw 1

theorem swap_finPart_phiE (v : HeightOneSpectrum (𝓞 D.host.F)) :
    swapAE D (finPart D (Formalism.IndefR.Fin.phiE v 1)) = Formalism.UG.P.afsplitEps D.host.E v := by
  rw [Formalism.UG.P.afsplitEps, Algebra.TensorProduct.one_def, Formalism.UG.P.afsplitIE_tmul, afsplitI_one]
  rfl

theorem suppAt_of_trivial_off : ∀ {D : D7} (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (Pb : Formalism.L2.DIV.Pl D.host.E) (e : Formalism.L2.Theta.AE D), Formalism.L2.Col.IsOver v Pb → Formalism.L2.NTheta.IsIdemAt e (Formalism.L2.Col.conjPrime₂ Pb) → ∀ α : GA D V, α ∈ GfC V → (∀ w : HeightOneSpectrum (𝓞 D.host.F), w ≠ v → Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) w) (finE V α) = 1) → SuppAt e V α := by
  intro D V v Pb e hO hI α hα hw
  rw [GlobalTheory.HeckeTrans.suppAt_iff e hα, Formalism.IndefR.Fin.below_of_idemAt hI, belowPl_conjP hO,
    ← GlobalTheory.HeckeTrans.finE_unswap]
  have hM : (finE V α).val.map
      (GlobalTheory.HeckeTrans.unswap D) - 1 =
      ((finE V α).val - 1).map
      (GlobalTheory.HeckeTrans.unswap D) := by
    rw [Matrix.map_sub _ (RingHom.map_sub _), Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _)]
  rw [hM]
  ext i j
  rw [Matrix.smul_apply, smul_eq_mul, Matrix.map_apply]
  apply Function.LeftInverse.injective (GlobalTheory.HeckeTrans.unswap_swap (D := D))
  rw [map_mul, swap_finPart_phiE, GlobalTheory.HeckeTrans.swap_unswap]
  exact eps_mul_of_off v (fun w hw' => prV_entry_eq_zero _ w (hw w hw') i j)

end GlobalTheory.Mem.SuppOffPlace
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportedAtConjPrimeIdempotentOfTrivialOffPlaceStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.supportedAt_conjPrimeIdempotent_of_trivial_offPlace : ∀ {D : D7} (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (Pb : Formalism.L2.DIV.Pl D.host.E) (e : Formalism.L2.Theta.AE D), Formalism.L2.Col.IsOver v Pb → Formalism.L2.NTheta.IsIdemAt e (Formalism.L2.Col.conjPrime₂ Pb) → ∀ α : GA D V, α ∈ GfC V → (∀ w : HeightOneSpectrum (𝓞 D.host.F), w ≠ v → Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) w) (finE V α) = 1) → SuppAt e V α := by
  first | exact @GlobalTheory.Mem.SuppOffPlace.suppAt_of_trivial_off | exact GlobalTheory.Mem.SuppOffPlace.suppAt_of_trivial_off | (intros; apply GlobalTheory.Mem.SuppOffPlace.suppAt_of_trivial_off <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameTransportEtaSupportedAtPlaceIdempotent
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg

namespace GlobalTheory.Mem.R3.LiftBrg.EtaSupp

theorem castGL_bc_comm {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {m k : ℕ} (h : m = k) (x : GL (Fin m) R) :
    castGL h (Formalism.UG.bc φ x) = Formalism.UG.bc φ (castGL h x) := by
  subst h
  ext i j
  simp [castGL, Formalism.UG.bc]

theorem finE_prV_eq_one {D : D7} (V : HSp D) (n : ℕ) [NeZero n] (h : n = V.rank) (v : HeightOneSpectrum (𝓞 D.host.F))
    (Pb : Formalism.L2.DIV.Pl D.host.E) (Ut : Formalism.L2.Col.MhlUnif Pb) (d : ℕ) (C : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) (α : GA D V)
    (hα : castGL h.symm (Formalism.UG.bc (swapAE D) (finHom V α)) = C * ((Formalism.L2.Col.mhlEta D.sp.cm n v Ut.hπ0 d : Formalism.L2.Col.UAd D.sp.cm n) : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) * C⁻¹)
    (w : HeightOneSpectrum (𝓞 D.host.F)) (hw : w ≠ v) :
    Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) w) (finE V α) = 1 := by
  apply (castGL h.symm).injective
  rw [map_one, castGL_bc_comm]
  show Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) w) (castGL h.symm (Formalism.UG.bc (swapAE D) (finHom V α))) = 1
  rw [hα]
  have key : ∀ {G H : Type} [Group G] [Group H] (f : G →* H) (c x : G), f x = 1 → f (c * x * c⁻¹) = 1 := by
    intro G H _ _ f c x hx
    rw [map_mul, map_mul, hx, mul_one, map_inv, mul_inv_cancel]
  have h1 : Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) w)
      ((Formalism.L2.Col.mhlEta D.sp.cm n v Ut.hπ0 d : Formalism.L2.Col.UAd D.sp.cm n) : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) = 1 :=
    Formalism.L2.Col.rll_put_ne n v w hw _
  exact key _ _ _ h1

end GlobalTheory.Mem.R3.LiftBrg.EtaSupp

namespace GlobalTheory.Mem.R3.LiftBrg

theorem eta_suppAt : ∀ {D : D7} (V : HSp D) (n : ℕ) [NeZero n] (h : n = V.rank) (v : HeightOneSpectrum (𝓞 D.host.F)) (Pb : Formalism.L2.DIV.Pl D.host.E) (Ut : Formalism.L2.Col.MhlUnif Pb) (d : ℕ) (e : Formalism.L2.Theta.AE D) (C : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) (α : GA D V), Formalism.L2.Col.IsOver v Pb → Formalism.L2.NTheta.IsIdemAt e (Formalism.L2.Col.conjPrime₂ Pb) → α ∈ GfC V → castGL h.symm (Formalism.UG.bc (swapAE D) (finHom V α)) = C * ((Formalism.L2.Col.mhlEta D.sp.cm n v Ut.hπ0 d : Formalism.L2.Col.UAd D.sp.cm n) : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) * C⁻¹ → SuppAt e V α := by
  intro D V n _ h v Pb Ut d e C α hv he hα hη
  exact GlobalTheory.T.supportedAt_conjPrimeIdempotent_of_trivial_offPlace V v Pb e hv he α hα fun w hw =>
    EtaSupp.finE_prV_eq_one V n h v Pb Ut d C α hη w hw

end GlobalTheory.Mem.R3.LiftBrg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameTransportEtaSupportedAtPlaceIdempotentStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameTransport_eta_supported_at_placeIdempotent : ∀ {D : D7} (V : HSp D) (n : ℕ) [NeZero n] (h : n = V.rank) (v : HeightOneSpectrum (𝓞 D.host.F)) (Pb : Formalism.L2.DIV.Pl D.host.E) (Ut : Formalism.L2.Col.MhlUnif Pb) (d : ℕ) (e : Formalism.L2.Theta.AE D) (C : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) (α : GA D V), Formalism.L2.Col.IsOver v Pb → Formalism.L2.NTheta.IsIdemAt e (Formalism.L2.Col.conjPrime₂ Pb) → α ∈ GfC V → castGL h.symm (Formalism.UG.bc (swapAE D) (finHom V α)) = C * ((Formalism.L2.Col.mhlEta D.sp.cm n v Ut.hπ0 d : Formalism.L2.Col.UAd D.sp.cm n) : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) * C⁻¹ → SuppAt e V α := by
  first | exact @GlobalTheory.Mem.R3.LiftBrg.eta_suppAt | exact GlobalTheory.Mem.R3.LiftBrg.eta_suppAt | (intros; apply GlobalTheory.Mem.R3.LiftBrg.eta_suppAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTameBlockCharacterTypePlaceNotOverL
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsResidueCharOfTameCharPrimeResidueField
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsResidueCharOfTameCharPrimeResidueField
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2

namespace GlobalTheory.TameTau

theorem tameChar_of_prime_residue : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (P : HeightOneSpectrum (𝓞 E)) (g : ℕ), g.Prime → normV P = g → ((g : ℕ) : 𝓞 E) ∈ P.asIdeal → ∀ {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [TopologicalSpace O] [IsTopologicalRing O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ (χ : G E Ω →* Oˣ), Continuous (fun g => ((χ g : Oˣ) : O)) → (∀ A : ValuationSubring Ω, IsPlaceOver A P → ∀ σ ∈ Ine (F := E) A, χ σ ^ (g - 1) = 1) → ∃ τ : (ZMod g)ˣ →* Oˣ, ∀ (x : (ZMod g)ˣ) (u : 𝓞 E), (((x : ZMod g).val : 𝓞 E) - u) ∈ P.asIdeal → τ x = NX.tameVal χ P 1 u := by
  intro E Ω _ _ _ _ _ P g hg hN hgP O _ _ _ _ _ hadic χ hχc hχI
  have : NeZero g := ⟨hg.ne_zero⟩
  have : Fact (1 < g) := ⟨hg.one_lt⟩
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  set m := g - 1 with hm_def
  have hm0 : 0 < m := by have := hg.two_le; omega
  have hPtop : P.asIdeal ≠ ⊤ := P.isPrime.ne_top
  have hmP : ((m : ℕ) : 𝓞 E) ∉ P.asIdeal := by
    intro h
    apply hPtop
    rw [Ideal.eq_top_iff_one]
    have h1 : ((g : ℕ) : 𝓞 E) = (m : 𝓞 E) + 1 := by
      have : g = m + 1 := by have := hg.two_le; omega
      rw [this]; push_cast; ring
    have := P.asIdeal.sub_mem hgP h
    rwa [h1, add_sub_cancel_left] at this
  have hNm : normV P - 1 = m := by rw [hN]
  obtain ⟨ϖ, hϖ, hϖ2⟩ : ∃ ϖ : 𝓞 E, ϖ ∈ P.asIdeal ∧ ϖ ∉ P.asIdeal ^ 2 := by
    have hlt : P.asIdeal ^ (1 + 1) < P.asIdeal ^ 1 := Ideal.pow_succ_lt_pow P.ne_bot 1
    rw [pow_one] at hlt
    exact SetLike.exists_of_lt hlt
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap E Ω (ϖ : E)) hm0
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow hm0.ne', eq_comm, map_eq_zero_iff _ (algebraMap E Ω).injective] at hπ
    have hϖ0 : ϖ = 0 := by exact_mod_cast hπ
    exact hϖ2 (hϖ0 ▸ Ideal.zero_mem _)
  obtain ⟨A₀, hA₀⟩ := exists_isPlaceOver Ω P
  have hvm : ¬ A₀.valuation (m : Ω) < 1 := by
    intro h; apply hmP; rw [← hA₀]; simpa using h
  have hex : ∀ u : 𝓞 E, u ∉ P.asIdeal → ∃ σ : G E Ω, σ ∈ Ine (F := E) A₀ ∧ ∃ ζ : Ω, ζ ^ m = 1 ∧
      A₀.valuation (ζ - algebraMap E Ω (u : E)) < 1 ∧ σ π = ζ * π := by
    intro u hu
    obtain ⟨ζ, hζ, hζu⟩ := GlobalTheory.T.exists_rootOfUnity_congr_unit_at_place A₀ P hA₀ u hu
    rw [hNm] at hζ
    obtain ⟨σ, hσ, hσπ⟩ := GlobalTheory.T.inertia_acts_on_tame_root A₀ P hA₀ m hm0 hmP ϖ hϖ hϖ2 π hπ ζ hζ
    exact ⟨σ, hσ, ζ, hζ, hζu, hσπ⟩
  have hrep : ∀ σ ∈ Ine (F := E) A₀, ∀ u : 𝓞 E, A₀.valuation (σ π / π - algebraMap E Ω (u : E)) < 1 →
      NX.TameRep P 1 σ u := by
    intro σ hσ u h
    refine ⟨A₀, hA₀, hσ, ϖ, π, hϖ, hϖ2, by rw [hNm]; exact hπ, ?_⟩
    rw [zpow_one]; exact h
  have hkey : ∀ (σ : G E Ω) (u : 𝓞 E), NX.TameRep P 1 σ u → NX.tameVal χ P 1 u = χ σ := by
    intro σ u h
    rw [NX.tameVal, dite_eq_left ⟨σ, h⟩]
    exact GlobalTheory.T.tameChar_eq_of_tameRep_congr P hadic χ hχc (by rw [hNm]; exact hm0) (by rw [hNm]; exact hmP)
      (by intro A hA σ' hσ'; rw [hNm]; exact hχI A hA σ' hσ') _ σ u u (⟨σ, h⟩ : ∃ σ, NX.TameRep P 1 σ u).choose_spec h (by simp)
  have hlt : ∀ a b : Ω, A₀.valuation a ≤ 1 → A₀.valuation b < 1 → A₀.valuation (a * b) < 1 := by
    intro a b ha hb
    rw [map_mul]
    calc A₀.valuation a * A₀.valuation b ≤ 1 * A₀.valuation b := by gcongr
      _ = A₀.valuation b := one_mul _
      _ < 1 := hb
  have hle : ∀ a b : Ω, A₀.valuation a ≤ 1 → A₀.valuation (a - b) < 1 → A₀.valuation b ≤ 1 := by
    intro a b ha hab
    have e : b = a - (a - b) := by ring
    rw [e]
    exact (Valuation.map_sub _ _ _).trans (max_le ha hab.le)
  have hP1 : ∀ w : 𝓞 E, w ∈ P.asIdeal → A₀.valuation (algebraMap E Ω (w : E)) < 1 := fun w hw => (hA₀ w).2 hw
  let U : (ZMod g)ˣ → 𝓞 E := fun x => (((x : ZMod g)).val : 𝓞 E)
  have hcong : ∀ x y : (ZMod g)ˣ, U x * U y - U (x * y) ∈ P.asIdeal := by
    intro x y
    simp only [U, Units.val_mul, ZMod.val_mul]
    have e : (((x : ZMod g).val * (y : ZMod g).val : ℕ) : 𝓞 E) =
        (g : 𝓞 E) * (((x : ZMod g).val * (y : ZMod g).val / g : ℕ) : 𝓞 E) +
          (((x : ZMod g).val * (y : ZMod g).val % g : ℕ) : 𝓞 E) := by
      exact_mod_cast (Nat.div_add_mod ((x : ZMod g).val * (y : ZMod g).val) g).symm
    rw [← Nat.cast_mul, e, add_sub_cancel_right]
    exact P.asIdeal.mul_mem_right _ hgP
  have hU1 : U 1 = 1 := by
    show (((1 : (ZMod g)ˣ) : ZMod g).val : 𝓞 E) = 1
    rw [Units.val_one, ZMod.val_one, Nat.cast_one]
  have hUP : ∀ x, U x ∉ P.asIdeal := by
    intro x hx
    have h := hcong x x⁻¹
    rw [mul_inv_cancel, hU1] at h
    apply hPtop
    rw [Ideal.eq_top_iff_one]
    have e : (1 : 𝓞 E) = U x * U x⁻¹ - (U x * U x⁻¹ - 1) := by ring
    rw [e]
    exact P.asIdeal.sub_mem (P.asIdeal.mul_mem_right _ hx) h
  choose σx hσx ζx hζx hζu hσπ using fun x => hex (U x) (hUP x)
  have hq : ∀ x, σx x π / π = ζx x := fun x => by rw [hσπ x, mul_div_cancel_right₀ _ hπ0]
  have hζ1 : ∀ x, A₀.valuation (ζx x) = 1 := fun x => valuation_eq_one_of_pow_eq_one A₀ hm0.ne' (hζx x)
  have hrepx : ∀ x, NX.TameRep P 1 (σx x) (U x) := fun x => hrep _ (hσx x) _ (by rw [hq]; exact hζu x)
  refine ⟨MonoidHom.mk' (fun x => χ (σx x)) ?_, ?_⟩
  · intro x y
    rw [← map_mul, ← hkey _ _ (hrepx (x * y))]
    refine hkey _ _ (hrep _ ((Ine (F := E) A₀).mul_mem (hσx x) (hσx y)) _ ?_)
    rw [GlobalTheory.TameTau.quot_mul (hσx x) m hvm hπ0 hπ, hq, hq]
    have e : ζx x * ζx y - algebraMap E Ω (U (x * y) : E) =
        ζx x * (ζx y - algebraMap E Ω (U y : E)) + algebraMap E Ω (U y : E) * (ζx x - algebraMap E Ω (U x : E)) +
          algebraMap E Ω ((U x * U y - U (x * y) : 𝓞 E) : E) := by
      push_cast; ring
    rw [e]
    refine Valuation.map_add_lt _ (Valuation.map_add_lt _ (hlt _ _ (hζ1 x).le (hζu y))
      (hlt _ _ (hle _ _ (hζ1 y).le (hζu y)) (hζu x))) (hP1 _ (hcong x y))
  · intro x u hxu
    show χ (σx x) = _
    refine (hkey _ _ (hrep _ (hσx x) _ ?_)).symm
    rw [hq]
    have e : ζx x - algebraMap E Ω (u : E) = (ζx x - algebraMap E Ω (U x : E)) +
        algebraMap E Ω ((U x - u : 𝓞 E) : E) := by
      push_cast; ring
    rw [e]
    exact Valuation.map_add_lt _ (hζu x) (hP1 _ hxu)

end GlobalTheory.TameTau
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsResidueCharOfTameCharPrimeResidueFieldStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_residue_char_of_tame_char_prime_residue_field : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (P : HeightOneSpectrum (𝓞 E)) (g : ℕ), g.Prime → normV P = g → ((g : ℕ) : 𝓞 E) ∈ P.asIdeal → ∀ {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [TopologicalSpace O] [IsTopologicalRing O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ (χ : G E Ω →* Oˣ), Continuous (fun g => ((χ g : Oˣ) : O)) → (∀ A : ValuationSubring Ω, IsPlaceOver A P → ∀ σ ∈ Ine (F := E) A, χ σ ^ (g - 1) = 1) → ∃ τ : (ZMod g)ˣ →* Oˣ, ∀ (x : (ZMod g)ˣ) (u : 𝓞 E), (((x : ZMod g).val : 𝓞 E) - u) ∈ P.asIdeal → τ x = NX.tameVal χ P 1 u := by
  first | exact @GlobalTheory.TameTau.tameChar_of_prime_residue | exact GlobalTheory.TameTau.tameChar_of_prime_residue | (intros; apply GlobalTheory.TameTau.tameChar_of_prime_residue <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTameBlockCharacterTypePlaceNotOverL
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.TameTau

theorem tauTame : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (b0 b1 : Big D)
    (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T) (i : T.Tw) (j : ℕ) (b : Bool)
    (kv : Σ kk : Fin 2, D.nd.PlG kk), 1 ≤ j → j ≤ D.R.m → NX.pG D kv ∉ placesOver D.host.E (T.l i) →
    TauTameT D T i j b kv := by
  intro _ D cf b0 b1 Sx T Sp i j b kv _ _ hl
  have hg := D.host.g_prime kv.1
  have hover := D.naut.plGw_over kv.1 kv.2
  obtain ⟨τ, hτ⟩ := GlobalTheory.T.exists_residue_char_of_tame_char_prime_residue_field (E := D.host.E) (Ω := D.nd.Om) (NX.pG D kv) (D.host.g kv.1) hg
    (GlobalTheory.Proof.EigenvalueCoprimeConjugation.normV_plGw D kv.1 kv.2) (by simpa [placesOver] using hover) (T.twistBaseCoefficientRing_isAdic i) (T.chi1 i j b)
    (T.twistCharacterFamily_continuous i j b) (fun A hA σ hσ => T.twistCharacterFamily_tame i j b kv.1 _ hover hl A hA σ hσ)
  refine ⟨(Units.map (baseCoeffToFractionRing D T i).toMonoidHom).comp τ, fun x u hu => ?_⟩
  rw [MonoidHom.comp_apply, Units.coe_map, hτ x u hu]
  rfl

end GlobalTheory.TameTau
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTameBlockCharacterTypePlaceNotOverLStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasTameBlockCharacter_typePlace_not_over_l : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (b0 b1 : Big D)
    (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T) (i : T.Tw) (j : ℕ) (b : Bool)
    (kv : Σ kk : Fin 2, D.nd.PlG kk), 1 ≤ j → j ≤ D.R.m → NX.pG D kv ∉ placesOver D.host.E (T.l i) →
    TauTameT D T i j b kv := by
  first | exact @GlobalTheory.TameTau.tauTame | exact GlobalTheory.TameTau.tauTame | (intros; apply GlobalTheory.TameTau.tauTame <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalLocalisationSpaceAll
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalLocalisationSpaceAll
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

namespace GlobalTheory.FinDimVProof

theorem finDimV_all : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (B : LocBase0 H what₂), FinDimV B := by
  intro R H what₂ B j w
  classical
  have hfin : (Formalism.L2.Fam.NPC.LatticeFinitenessFree.latJ (what₂ := what₂) j w).Finite :=
    Set.Finite.subset ((what₂.MtLat (what₂.muTw w) j).gen.finite_toSet.preimage
      ((Formalism.L2.Fam.NPC.LatticeFinitenessFree.jMt_injective (what₂.muTw w) j).injOn)) fun x hx => hx
  have hs := Formalism.L2.Fam.NPC.LatticeFinitenessFree.span_iV (B := B) j w
  exact Module.finite_def.2 ⟨(hfin.image (B.iV j w)).toFinset, by simpa using hs⟩

end GlobalTheory.FinDimVProof
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalLocalisationSpaceAllStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_localisation_space_all : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (B : LocBase0 H what₂), FinDimV B := by
  first | exact @GlobalTheory.FinDimVProof.finDimV_all | exact GlobalTheory.FinDimVProof.finDimV_all | (intros; apply GlobalTheory.FinDimVProof.finDimV_all <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeRingActsOnLatticeAsOperators
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeRingActsOnLatticeAsOperators
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

namespace GlobalTheory.HeckeLocN

theorem actHK_holds {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (B : LocBase0 H what₂) (hs : HeckeStd0 B) (hd : FinDimV B)
    (hL : MtLoc B (partCompl_of hs hd)) (hAct : ActEx B (partCompl_of hs hd)) : ActHK B hs hd hL hAct := by
  intro i v k hg z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul c m =>
    rw [LinearMap.baseChange_tmul]
    have hs1 := ((hAct i).choose_spec.2 v k hg m)
    have e : ∀ m' : MtSub B (partCompl_of hs hd) i, PsiC B (partCompl_of hs hd) hL i (c ⊗ₜ m') = c • ((m' : partOf B i) : B.V (jOf B i) (wOf B i)) := by
      intro m'
      haveI := hL i
      simp only [PsiC, mtEquiv, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, Submodule.coe_subtype]
      rw [IsBaseChange.equiv_tmul]
      rfl
    rw [e, e, map_smul]
    congr 1

end GlobalTheory.HeckeLocN
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeRingActsOnLatticeAsOperatorsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeRing_acts_on_lattice_as_operators : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (B : LocBase0 H what₂) (hs : HeckeStd0 B) (hd : FinDimV B) (hL : MtLoc B (partCompl_of hs hd)) (hAct : ActEx B (partCompl_of hs hd)), ActHK B hs hd hL hAct := by
  first | exact @GlobalTheory.HeckeLocN.actHK_holds | exact GlobalTheory.HeckeLocN.actHK_holds | (intros; apply GlobalTheory.HeckeLocN.actHK_holds <;> assumption)
end
end
