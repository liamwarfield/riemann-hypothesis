module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartAtPoint
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeOperatorPreservesSupLatticeRealSide
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OfFirstStepLoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnifPolarizationSquareIso
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AtSame
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsFiniteQCHomModOfExact
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmHostUnitAddConjEqOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGoodRowHeckeOfOcc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceComponentCarriesEveryFrameFlag

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JumpsCardOfBuilt
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

noncomputable section
namespace GlobalTheory.HeightCounting.JumpsAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem lg_of_forall {K : Ctx} {p : ∀ B : Base, Fr B.toPre → TwDat B → Prop} (h : ∀ B f T, p B f T) : large₂ K p :=
  ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, by simp, by simp, fun B f T _ _ _ _ => h B f T⟩

theorem evLgG_of_forall {p : Ctx → ∀ B : Base, Fr B.toPre → TwDat B → Prop} (h : ∀ K B f T, p K B f T) : EvLgG p :=
  evLgG_of_evLg ⟨1, one_pos, fun _ _ _ _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ => ⟨0, fun _ _ => ⟨0,
    fun _ _ => ⟨0, fun K _ _ _ _ _ => lg_of_forall (h K)⟩⟩⟩⟩⟩

end GlobalTheory.HeightCounting.JumpsAt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationFixedLattice
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

namespace GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem valLL0_colW {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (Z : w.Lt) :
    ValLL0 (w.D Z) (TC.cf w.I w.l Z) := by
  rcases w with ⟨px, I, ok, C_eq, S_eq, xi_range, pins, l, l0, δ, exact, fld, val⟩
  subst C_eq
  exact val _ _ _ _ _ _

end GlobalTheory.HeightCounting.Up
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AuxiliaryPlacesSplit
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

namespace GlobalTheory.HeightCounting.Up

theorem isSplitPl_of_mem_levelPrimes {R : Ranks} (H : Host R)
    (hc : ∀ p ∈ H.levelPrimes, p.Prime ∧ p % (H.QS * H.q * H.d) = 1) {p : ℕ} (hp : p ∈ H.levelPrimes)
    (v : HeightOneSpectrum (𝓞 H.E)) (hv : v ∈ placesOver H.E p) : IsSplitPl H v := by
  obtain ⟨hpr, hm⟩ := hc p hp
  have h := (GlobalTheory.HostSplit.split_of_one_mod R H p hpr hm).1
  obtain ⟨-, he, hf⟩ := GlobalTheory.unramified_degree_one_of_ncard_placesOver H.E p hpr h v hv
  exact GlobalTheory.Proof.SemisimpleRepresentationIntegralConjugate.isSplitPl_of_degree_one H v hf he

end GlobalTheory.HeightCounting.Up
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseLevelCharacterEqProdSuperdiagonalSum
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

namespace GlobalTheory.HeightCounting.ThetaSt

section Gen

variable {D : D7}

theorem baseLevelCharacter_eq_prod_superdiagonalSum {Pg : Finset (Pl D.host.E)} {r : ℕ} (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) D.what₂.LL)
    (y : (Formalism.L2.DIV.P0 Pg r ψ).H) :
    (((Formalism.L2.DIV.P0 Pg r ψ).chi y : D.what₂.LLˣ) : D.what₂.LL) =
      ∏ PP : ↥Pg, ψ PP.1 (edgeSum supEdge ((y : G0 Pg r) PP)) := by
  change ↥(Subgroup.pi Set.univ fun PP : ↥Pg => unip (kP PP.1) r) at y
  change (((∏ PP : ↥Pg, (addCharHom (ψ PP.1) (supHom (kP PP.1) r)).comp
    (LevelP.prj (fun PP : ↥Pg => unip (kP PP.1) r) PP)) y : D.what₂.LLˣ) : D.what₂.LL) = _
  letI : IsOneApply (↥(Subgroup.pi Set.univ fun PP : ↥Pg => unip (kP PP.1) r) →* D.what₂.LLˣ) := ⟨fun _ => rfl⟩
  letI : IsMulApply (↥(Subgroup.pi Set.univ fun PP : ↥Pg => unip (kP PP.1) r) →* D.what₂.LLˣ) := ⟨fun _ _ _ => rfl⟩
  rw [prod_apply, Units.coe_prod]
  rfl

theorem supSum_map {κ : Type} [CommRing κ] {n : ℕ} (e : κ →+* ZMod n) {r : ℕ} (g : GL (Fin r) κ) :
    Formalism.L2.NX.supSum r ((Matrix.GeneralLinearGroup.map e g : GL (Fin r) (ZMod n)) : Matrix (Fin r) (Fin r) (ZMod n)) =
      e (edgeSum supEdge g) := by
  unfold Formalism.L2.NX.supSum edgeSum
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases h : (b : ℕ) = a + 1
  · have h' : supEdge a b := h
    rw [if_pos h, if_pos h']
    rfl
  · have h' : ¬ supEdge a b := h
    rw [if_neg h, if_neg h', map_zero]

def thOf (ζ : Fin 2 → ↥D.LL0) (hp : ∀ k, ζ k ^ D.host.g k = 1) (k : Fin 2) :
    Multiplicative (ZMod (D.host.g k)) →* (↥D.LL0)ˣ :=
  ((AddChar.zmodChar (D.host.g k) (hp k)).toMonoidHom.toHomUnits)⁻¹

theorem thOf_val (ζ : Fin 2 → ↥D.LL0) (hp : ∀ k, ζ k ^ D.host.g k = 1) (k : Fin 2) (z : ZMod (D.host.g k)) :
    (((thOf ζ hp k (Multiplicative.ofAdd z) : (↥D.LL0)ˣ) : ↥D.LL0) : D.what₂.LL) = ((ζ k : D.what₂.LL) ^ z.val)⁻¹ := by
  simp [thOf, MonoidHom.inv_apply, AddChar.toMonoidHom_apply, AddChar.zmodChar_apply]

theorem pow_of_emb (ζ : Fin 2 → ↥D.LL0)
    (hζ : ∀ k, D.what₂.embLL (ζ k : D.what₂.LL) = Complex.exp (2 * Real.pi * Complex.I / (D.host.g k : ℂ))) (k : Fin 2) :
    ζ k ^ D.host.g k = 1 := by
  have hg : (D.host.g k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (D.host.g_prime k).ne_zero
  apply Subtype.ext
  apply D.what₂.embLL.injective
  have e1 : ((ζ k ^ D.host.g k : ↥D.LL0) : D.what₂.LL) = (ζ k : D.what₂.LL) ^ D.host.g k := rfl
  rw [e1, map_pow, hζ, ← Complex.exp_nat_mul]
  have e2 : ((D.host.g k : ℕ) : ℂ) * (2 * Real.pi * Complex.I / (D.host.g k : ℂ)) = 2 * Real.pi * Complex.I := by
    field_simp
  rw [e2, Complex.exp_two_pi_mul_I]
  simp

end Gen

section State

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}

theorem roots_g (x : St P) (k : Fin 2) : ∃ ζ : ↥(Dof x).LL0,
    (Dof x).what₂.embLL (ζ : (Dof x).what₂.LL) = Complex.exp (2 * Real.pi * Complex.I / ((Dof x).host.g k : ℂ)) := by
  have hmem : (w.st x.o.Z).B.host.g k * ((w.st x.o.Z).B.host.g k - 1) ∈ [(w.st x.o.Z).B.restRowsFiniteGroupCard,
      (w.st x.o.Z).B.host.g 0 * ((w.st x.o.Z).B.host.g 0 - 1), (w.st x.o.Z).B.host.g 1 * ((w.st x.o.Z).B.host.g 1 - 1), 3 ^ 4,
      5 ^ 4] := by
    fin_cases k <;> simp
  obtain ⟨z, hz, hz'⟩ := (w.st x.o.Z).B.roots_Ks _ hmem
  have hg1 : 1 < (Dof x).host.g k := ((Dof x).host.g_prime k).one_lt
  refine ⟨⟨z ^ ((Dof x).host.g k - 1), (w.st x.o.Z).B.Ks_le (pow_mem hz _)⟩, ?_⟩
  show (w.st x.o.Z).B.embLL (z ^ ((Dof x).host.g k - 1)) = _
  rw [map_pow, hz', ← Complex.exp_nat_mul]
  congr 1
  have hc : (((Dof x).host.g k - 1 : ℕ) : ℂ) = ((Dof x).host.g k : ℂ) - 1 := by
    rw [Nat.cast_sub hg1.le, Nat.cast_one]
  have hg0 : ((Dof x).host.g k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hg1' : ((Dof x).host.g k : ℂ) - 1 ≠ 0 := by
    rw [← hc]; exact Nat.cast_ne_zero.2 (by omega)
  change (((Dof x).host.g k - 1 : ℕ) : ℂ) * (2 * Real.pi * Complex.I / (((Dof x).host.g k * ((Dof x).host.g k - 1) : ℕ) : ℂ)) = _
  rw [Nat.cast_mul, hc]
  field_simp

end State

section Gen

end Gen

end GlobalTheory.HeightCounting.ThetaSt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeReadingEigenvaluePlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RatHeckeBall


end GlobalTheory.RatHeckeBall
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsCAtState
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.RatSide

theorem formsC_of_full {D : D7} (S : RatDat D.ntw)
    (h : ∀ j, 1 ≤ j → j ≤ D.R.m → (S.A j).IsKsForm ∧ (S.A j).MKFull) : FormsC S := by
  intro j h1 h2
  obtain ⟨hK, hM⟩ := h j h1 h2
  refine ⟨hK, ?_, ?_⟩
  · obtain ⟨n, b, -, -, hsp, -, -⟩ := hK
    show FiniteDimensional S.Ks ↥(S.A j).WK
    rw [← hsp]
    exact FiniteDimensional.span_of_finite S.Ks (Set.finite_range b)
  · obtain ⟨T, hT⟩ := hM.1
    refine ⟨T, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
    · rw [← hT]; exact Submodule.subset_span hx
    · exact ⟨hx.fst, by rw [hT]; exact hx⟩
    · rw [← hM.2] at hx
      refine Submodule.span_le.2 (fun y hy => ?_) hx
      have hy' : y ∈ Submodule.span (𝓞 S.Ks) (T : Set (S.WL j)) := by rw [hT]; exact hy
      exact Submodule.span_le_restrictScalars (𝓞 S.Ks) S.Ks _ hy'

end GlobalTheory.HeightCounting.RatSide

namespace GlobalTheory.HeightCounting.RatSide

end GlobalTheory.HeightCounting.RatSide
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisRepsCuspidalAll
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.Up

theorem galoisRepsCusp_of_galEx {D : D7} (h : GalEx D) : GlobalTheory.BlockComplement.GaloisRepsCusp D :=
  fun i a ha π hc hr => h (D.nd.l i) (D.naut.iotaQC i) a ha π hc hr


end GlobalTheory.HeightCounting.Up
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AuxiliaryPlacesSplitAll
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

namespace GlobalTheory.SplitPrimeAuxiliary

open scoped Pointwise

theorem eq_one_of_smul_eq (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] {p : ℕ} (hp : p.Prime)
    (h : ((Ideal.span {(p : ℤ)}).primesOver (𝓞 E)).ncard = Module.finrank ℚ E)
    (P : Ideal (𝓞 E)) [P.IsPrime] (hP : (p : 𝓞 E) ∈ P) (σ : Gal(E/ℚ)) (hσ : σ • P = P) : σ = 1 := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    ((Ideal.span_singleton_prime hpz.ne_zero).2 hpz).isMaximal (by simpa using hp.ne_zero)
  have hlo : P.LiesOver (Ideal.span {(p : ℤ)}) := by
    refine ⟨hmax.eq_of_le (Ideal.IsPrime.under ℤ P).ne_top ?_⟩
    rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap]
    simpa using hP
  have horb := Algebra.IsInvariant.orbit_eq_primesOver ℤ (𝓞 E) Gal(E/ℚ) (Ideal.span {(p : ℤ)}) P
  have hidx := MulAction.index_stabilizer Gal(E/ℚ) P
  rw [horb, h, ← IsGalois.card_aut_eq_finrank] at hidx
  have hmul := (MulAction.stabilizer Gal(E/ℚ) P).card_mul_index
  rw [hidx] at hmul
  have h1 : Nat.card (MulAction.stabilizer Gal(E/ℚ) P) = 1 :=
    Nat.eq_of_mul_eq_mul_right Nat.card_pos (by rw [hmul, one_mul])
  have hb := Subgroup.card_eq_one.1 h1
  have hm : σ ∈ MulAction.stabilizer Gal(E/ℚ) P := hσ
  rwa [hb, Subgroup.mem_bot] at hm

theorem conj_ne_one {R : Ranks} (H : Host R) : H.conj ≠ 1 := by
  have : IsCMField H.E := H.isCMField_hostE
  intro h
  apply IsCMField.complexConj_ne_one H.E
  ext z
  have : IsCMField.complexConj H.E z = H.conj z := by
    apply H.φ₀.injective
    rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]
  rw [this, h]
  rfl

theorem isSplitPl_of_split {R : Ranks} (H : Host R) {p : ℕ} (hp : p.Prime)
    (h : ((Ideal.span {(p : ℤ)}).primesOver (𝓞 H.E)).ncard = Module.finrank ℚ H.E)
    (v : HeightOneSpectrum (𝓞 H.E)) (hv : v ∈ placesOver H.E p) : IsSplitPl H v := by
  have : IsGalois ℚ H.E := H.hostE_isGalois
  have := v.isPrime
  by_contra hs
  apply conj_ne_one H
  rw [← inv_eq_one]
  refine eq_one_of_smul_eq H.E hp h v.asIdeal hv _ (Eq.symm ?_)
  refine v.isMaximal.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_
  intro x hx
  rw [Ideal.mem_inv_pointwise_smul_iff]
  by_contra hx'
  refine hs ⟨x, hx, fun y hy => ?_⟩
  have : y = H.conj • x := RingOfIntegers.ext hy
  rwa [this]

end GlobalTheory.SplitPrimeAuxiliary
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SiegelFamilyProperExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrincipalPolarizationOfMumfordBundleSiegelFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrincipalPolarizationOfMumfordBundleSiegelFibre
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj

noncomputable section
attribute [local instance] Over.cartesianMonoidalCategory
open MonoidalCategory CartesianMonoidalCategory MonObj

namespace GlobalTheory.SiegFibrePol

theorem polAV_of_lam_univ : ∀ (o : Type) [CommRing o] (ζ : o) (g n : ℕ) (F : SFam g n ζ) (K : Type) [Field K] (y : Sp K ⟶ F.X) (B : Over (Sp K)) [GrpObj B] (α : B.left ⟶ F.univ.A.left) (α₂ : (G2 B).left ⟶ (G2 F.univ.A).left), IsGrpPullback B F.univ.A y α → IsSquare α α₂ → ∀ L : LB B.left, L.IsLB → Rigidified B L → Out.Sym B L → LBIso (abelian₂ B L) (F.univ.P.pull α₂) → IsAbelianScheme B ∧ RelAmple B L ∧ KTriv B L := by
  intro o _ ζ g n F K _ y B _ α α₂ hpb hsq L hL hrig hsym hΛ
  open GlobalTheory.CechPic GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.AbLaw in
  have hB : IsAbelianScheme B := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback F.univ.ab hpb
  have := hB.comm
  have laws : Out.Laws := GlobalTheory.allSixLaws.1
  haveI : IsProper F.univ.A.hom := F.univ.ab.proper
  have hP' : (F.univ.P.pull α₂).IsLB := pull_isLB F.univ.isLB α₂
  have hrefl : LBIso (F.univ.P.pull α₂) (F.univ.P.pull α₂) := (GlobalTheory.CechPic.cls_eq_iff hP' hP').1 rfl
  have hn := GlobalTheory.SiegelPull.nondeg_pull hpb hsq F.univ.isLB hP' hrefl F.princ.2
  have hM0 : (F.univ.diag.pull α).IsLB := pull_isLB (pull_isLB F.univ.isLB _) α
  have hamp0 : Out.RelAmple B (F.univ.diag.pull α) :=
    GlobalTheory.AmpleBaseChange.relAmple_of_isPullback (pull_isLB F.univ.isLB _) F.princ.1 hpb.1
  have hd : ((F.univ.P.pull α₂).pull (lift (𝟙 B) (𝟙 B)).left).IsLB := pull_isLB hP' _
  have hdiag := GlobalTheory.SiegelPull.diag_iso hsq hrefl
  have eM0 : GlobalTheory.CechPic.cls _ hM0 = GlobalTheory.CechPic.cls _ hd := ((GlobalTheory.CechPic.cls_eq_iff hd hM0).2 hdiag).symm
  have hp : IsProjBy B.hom :=
    (GlobalTheory.AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral _ B _ hB hM0 hamp0 K (𝟙 _) _ (𝟙 _) B.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)).1
  have hΘ := GlobalTheory.AbLaw.CubeAffine.triv_theta_of_isProjBy laws K B hB hp L hL
  have s₁ := GlobalTheory.SameLam.pull_inv_cls hL hsym
  have e₀ : GlobalTheory.CechPic.cls _ hP' = GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls L hL) (fst B B) (snd B B) :=
    ((GlobalTheory.CechPic.cls_eq_iff (LB.isLB_linComb hL _ _) hP').2 hΛ).symm.trans
      (GlobalTheory.CechPic.cls_cube_two hL _ _ (LB.isLB_linComb hL _ _))
  have hη : GlobalTheory.CechPic.pull (η[B] : 𝟙_ _ ⟶ B).left (GlobalTheory.CechPic.cls L hL) = 0 := by
    rw [← GlobalTheory.CechPic.cls_pull hL _ (pull_isLB hL _)]
    exact (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hL _)).2 hrig
  have h1 : GlobalTheory.CechPic.pull (1 : B ⟶ B).left (GlobalTheory.CechPic.cls L hL) = 0 := by
    rw [Hom.one_def, Over.comp_left, GlobalTheory.CechPic.pull_comp, hη, map_zero]
  have e₃ : GlobalTheory.CechPic.cls _ hd = 2 • GlobalTheory.CechPic.cls L hL := by
    refine (GlobalTheory.CechPic.cls_pull hP' _ _).trans ?_
    rw [e₀, GlobalTheory.CechPic.pull_lam, lift_fst, lift_snd, GlobalTheory.SymRoot.lam_diag hL hΘ s₁, GlobalTheory.SymRoot.rigCls, h1, sub_zero]
  have f : IsFinite (𝟙 B : B ⟶ B).left := by rw [Over.id_left]; infer_instance
  have iso : LBIso (F.univ.diag.pull α) (lbPow L 2) :=
    (GlobalTheory.CechPic.cls_eq_iff hM0 (isLB_lbPow hL 2)).1 (eM0.trans (e₃.trans (cls_lbPow hL 2 _).symm))
  have hamp : Out.RelAmple B L :=
    (GlobalTheory.relAmple_finite_pow_iso _ B B (𝟙 _) L 2 two_pos hB hB hL f).2.1.1
      ((GlobalTheory.relAmple_finite_pow_iso _ B B (𝟙 _) _ 2 two_pos hB hB hM0 f).2.2.2 _ (isLB_lbPow hL 2) iso hamp0)
  exact ⟨hB, hamp, GlobalTheory.ThetaExtend.kTriv_of_lam hL hP' e₀ hn⟩

end GlobalTheory.SiegFibrePol
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrincipalPolarizationOfMumfordBundleSiegelFibreStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalPolarization_of_mumfordBundle_siegelFibre : ∀ (o : Type) [CommRing o] (ζ : o) (g n : ℕ) (F : SFam g n ζ) (K : Type) [Field K] (y : Sp K ⟶ F.X) (B : Over (Sp K)) [GrpObj B] (α : B.left ⟶ F.univ.A.left) (α₂ : (G2 B).left ⟶ (G2 F.univ.A).left), IsGrpPullback B F.univ.A y α → IsSquare α α₂ → ∀ L : LB B.left, L.IsLB → Rigidified B L → Out.Sym B L → LBIso (abelian₂ B L) (F.univ.P.pull α₂) → IsAbelianScheme B ∧ RelAmple B L ∧ KTriv B L := by
  first | exact @GlobalTheory.SiegFibrePol.polAV_of_lam_univ | exact GlobalTheory.SiegFibrePol.polAV_of_lam_univ | (intros; apply GlobalTheory.SiegFibrePol.polAV_of_lam_univ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RigidifiedSymmetricLineBundleGroupPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RigidifiedSymmetricLineBundleGroupPullback
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RigSymBaseChange

theorem rigidified_and_sym_pull : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] (B : Over S') [GrpObj B] (β : B.left ⟶ G.left), IsGrpPullback B G f β → ∀ (L : RigLB G) (σ : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(GrpObj.inv : G ⟶ G).left, 𝟙 G.left] ![1, -1])), σ.IsGen → Rigidified B (L.L.pull β) ∧ Out.Sym B (L.L.pull β) := by
  intro S S' f G _ B _ β gp L σ hσ
  refine ⟨PolBaseChange.rigidified_pull gp ⟨L.rig, L.rigGen⟩, fun _ => ⟨⊤, trivial, ?_⟩⟩
  refine gen_chartPull (chartPullLinComb L.L β (K := Fin 2) _
    ![(GrpObj.inv : G ⟶ G).left, 𝟙 G.left] ![1, -1] ((B.hom ⁻¹ᵁ ⊤).ι ≫ β) fun k => ?_) σ hσ
  fin_cases k
  · show ((B.hom ⁻¹ᵁ ⊤).ι ≫ (GrpObj.inv : B ⟶ B).left) ≫ β = ((B.hom ⁻¹ᵁ ⊤).ι ≫ β) ≫ (GrpObj.inv : G ⟶ G).left
    rw [Category.assoc, PolBaseChange.inv_comm gp, Category.assoc]
  · show (B.hom ⁻¹ᵁ ⊤).ι ≫ β = ((B.hom ⁻¹ᵁ ⊤).ι ≫ β) ≫ 𝟙 G.left
    rw [Category.comp_id]

end GlobalTheory.RigSymBaseChange
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RigidifiedSymmetricLineBundleGroupPullbackStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rigidified_symmetric_lineBundle_groupPullback : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] (B : Over S') [GrpObj B] (β : B.left ⟶ G.left), IsGrpPullback B G f β → ∀ (L : RigLB G) (σ : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(GrpObj.inv : G ⟶ G).left, 𝟙 G.left] ![1, -1])), σ.IsGen → Rigidified B (L.L.pull β) ∧ Out.Sym B (L.L.pull β) := by
  first | exact @GlobalTheory.RigSymBaseChange.rigidified_and_sym_pull | exact GlobalTheory.RigSymBaseChange.rigidified_and_sym_pull | (intros; apply GlobalTheory.RigSymBaseChange.rigidified_and_sym_pull <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SiegLoc.TraitOrd

section Specialise

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ} {F : SFam g n ζ} {S : Scheme.{0}} {j : F.X ⟶ S} [IsOpenImmersion j]
  {G : Over S} [GrpObj G] {e : F.univ.A.left ⟶ G.left}

theorem isSemiAbelian_of_isGrpPullback {T : Scheme.{0}} {f : T ⟶ S} {G' : Over T} [GrpObj G'] [IsCommMonObj G']
    {π : G'.left ⟶ G.left} (h : IsGrpPullback G' G f π) (hG : IsSemiAbelian G) : IsSemiAbelian G' := by
  obtain ⟨bc, mbc, -⟩ := grpPullback_iso h (isGrpPullback_pullback G f)
  exact isSemiAbelian_of_grpIso bc (IsSemiAbelian.pullback f G hG)

end Specialise

theorem eq_of_associated_pow {V : Type} [CommRing V] [IsDomain V] {ϖ : V} (hϖ : Irreducible ϖ) {a b : ℕ}
    (h : Associated (ϖ ^ a) (ϖ ^ b)) : a = b :=
  le_antisymm ((pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 h.dvd) ((pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 h.symm.dvd)


end GlobalTheory.SiegLoc.TraitOrd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChoiceSide
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr

noncomputable section
namespace GlobalTheory.LayerMove
set_option maxHeartbeats 4000000
variable {D : D7} (m : Mv D) {hL : GlobalTheory.Published.LocalLanglandsGL}

def Mv.sideA {cf : CharFrame D} {jE : D.host.E →+* Qb} (A : SideA D cf jE) : SideA m.D (m.cf cf) jE := @_root_.GlobalTheory.HeightCounting.SideA.mk (_) (_) (_)
    (bare := (A.bare))
    (wdT := (A.wdT))
    (lab := (A.lab))
    (chr := @_root_.GlobalTheory.HeightCounting.CharSide.mk (_) (_)
      (e1 := (A.chr.e1))
      (unr_iff := (A.chr.unr_iff))
      (frob := (A.chr.frob))
      (tw := (A.chr.tw))
      (infG := (A.chr.infG))
      (csd := (A.chr.csd))
      (etaT := (A.chr.etaT))
      (etaTinv := (A.chr.etaTinv))
      (plGw := (A.chr.plGw)))
    (row := @_root_.GlobalTheory.HeightCounting.RowSide.mk (_)
      (locR := (A.row.locR))
      (satR := (A.row.satR))
      (lab_eq := (A.row.lab_eq)))
    (pl := @_root_.GlobalTheory.HeightCounting.PlSide.mk (_)
      (ι := (A.pl.ι))
      (ι_w := (A.pl.ι_w))
      (plB := (A.pl.plB))
      (plB_eq := (A.pl.plB_eq))
      (plκ := (A.pl.plκ)))
    (iota := (A.iota))
    (wd := @_root_.GlobalTheory.HeightCounting.WDSide.mk (_) (_)
      (wdOf := (A.wd.wdOf))
      (wdOf_dim := (A.wd.wdOf_dim))
      (wdOf_unr := (A.wd.wdOf_unr))
      (wdOf_frob := (A.wd.wdOf_frob))
      (wdOf_ine := (A.wd.wdOf_ine))
      (wdOf_mono0 := (A.wd.wdOf_mono0))
      (IsCrysW := (A.wd.IsCrysW))
      (IsPotCrysW := (A.wd.IsPotCrysW))
      (IsdRW := (A.wd.IsdRW))
      (jumpsW := (A.wd.jumpsW))
      (wdOf_unrL := (A.wd.wdOf_unrL))
      (wdOf_mono0L := (A.wd.wdOf_mono0L))
      (away := (A.wd.away))
      (above := (A.wd.above))
      (loc := (A.wd.loc)))
    (grp := @_root_.GlobalTheory.HeightCounting.GrpSide.mk (_)
      (tA := (A.grp.tA))
      (tκ := (A.grp.tκ))
      (teichC_def := (A.grp.teichC_def))
      (ζ := (A.grp.ζ))
      (ζ_gen := (A.grp.ζ_gen))
      (O := (A.grp.O))
      (eSer_def := (A.grp.eSer_def))
      (kv := (A.grp.kv))
      (tg_tame := (A.grp.tg_tame))
      (O_equiv := (A.grp.O_equiv))
      (O_tw := (A.grp.O_tw)))
    (par := @_root_.GlobalTheory.HeightCounting.ParSide.mk (_) (_)
      (eM := (A.par.eM))
      (eM_K := (A.par.eM_K))
      (eP := (A.par.eP))
      (locPar_def := (A.par.locPar_def)))
    (au := @_root_.GlobalTheory.HeightCounting.AUSide.mk (_)
      (cls := (A.au.cls))
      (surj := (A.au.surj))
      (iso := (A.au.iso))
      (mult := (A.au.mult))
      (sph := (A.au.sph))
      (sat := (A.au.sat))
      (clsWt := (A.au.clsWt))
      (surjWt := (A.au.surjWt))
      (isoWt := (A.au.isoWt))
      (wt := (A.au.wt))
      (infW := (A.au.infW))
      (locUnr := (A.au.locUnr))
      (locPol := (A.au.locPol)))
    (chiT := (A.chiT))

def Mv.cg {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : SideA D cf jE} (x : CGTrue hL D A.wdT) : CGTrue hL m.D (m.sideA A).wdT := @_root_.GlobalTheory.HeightCounting.CGTrue.mk (_) (_) (_)
    (e := (x.e))
    (surj := (x.surj))
    (zero := (x.zero))
    (loc := (x.loc))
    (tw := (x.tw))
    (inf := (x.inf))
    (csd := (x.csd))
theorem Mv.au {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : SideA D cf jE} (x : AUTrue hL D A.wdT A.au) : AUTrue hL m.D (m.sideA A).wdT (m.sideA A).au := (x)
theorem Mv.row {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : SideA D cf jE} {rep} (x : RowTrue hL D rep (fun σ w ↦ (A.wdT.e w) (A.row.locR σ w)) A.row.satR) : RowTrue hL m.D rep (fun σ w ↦ ((m.sideA A).wdT.e w) ((m.sideA A).row.locR σ w)) (m.sideA A).row.satR := (x)

section
variable {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : SideA D cf jE} {M : Formalism.L2.MtFam D} {C : NChoice D} {tp : TupTied D cf C}
theorem Mv.mtInput (x : MtInput D M tp.tup C.Q) : MtInput m.D (m.mt M) (m.tp tp).tup (m.ch C).Q := @_root_.GlobalTheory.HeightCounting.MtInput.mk (_) (_) (_) (_)
    (prod := (x.prod))
    (para := (x.para))
    (uni := (x.uni))
    (hyp := (x.hyp))
    (wt := (x.wt))
    (rat := (x.rat))
    (int := (x.int))
    (full := (x.full))

def Mv.ratIn {S} (x : RatIn D S) : RatIn m.D S := @_root_.GlobalTheory.HeightCounting.RatIn.mk (_) (_)
    (Sb := (x.Sb))
    (rho := (x.rho))
    (chi := (x.chi))
    (ks := (x.ks))
    (fd := (x.fd))
    (mk_fg := (x.mk_fg))
    (hL := (x.hL))
    (hs := (x.hs))
    (hL_zero := (x.hL_zero))
    (θ := (x.θ))
    (θ_ne := (x.θ_ne))
    (eig := (x.eig))
    (span := (x.span))
    (hL_int := (x.hL_int))
theorem Mv.rowDepth {rep} (x : RowDepth D rep) : RowDepth m.D rep := (x)
end

def Mv.host (x : HostTied D) : HostTied m.D := @_root_.Formalism.L2.Host.HostTied.mk (_)
    (fr := (x.fr))
    (jLL := (x.jLL))
    (embLL := (x.embLL))
section
variable {cf : CharFrame D} {C : NChoice D} {tp : TupTied D cf C}

def Mv.chrN (x : NCharTied D cf C tp) : NCharTied m.D (m.cf cf) (m.ch C) (m.tp tp) := @_root_.Formalism.L2.Host.NCharTied.mk (_) (_) (_) (_)
    (e1 := (x.e1))
    (unr_iff := (x.unr_iff))
    (frob := (x.frob))
    (tw := (x.tw))
    (infG := (x.infG))
    (csd := (x.csd))
    (muC := (x.muC))
    (etaT := (x.etaT))
    (etaTinv := (x.etaTinv))
    (plGw := (x.plGw))
theorem Mv.chrGal (x : NGalChrTied D cf C tp) : NGalChrTied m.D (m.cf cf) (m.ch C) (m.tp tp) := @_root_.Formalism.L2.Host.NGalChrTied.mk (_) (_) (_) (_)
    (psi_is := (x.psi_is))
    (psiL := (x.psiL))
    (deltaRead := (x.deltaRead))
theorem Mv.oSplit (x : GlobalTheory.SplitCoef.OSplit D) : GlobalTheory.SplitCoef.OSplit m.D := (x)
theorem Mv.large (x : GlobalTheory.CoefDuty.Large D) : GlobalTheory.CoefDuty.Large m.D := (x)
theorem Mv.bkLaw (x : BkLaw D) : BkLaw m.D := (x)

def Mv.omFrame (x : Formalism.L2.OmFrame D) : Formalism.L2.OmFrame m.D := @_root_.Formalism.L2.OmFrame.mk (_)
    (jE := (x.jE))
    (eOm := (x.eOm))
    (comm := (x.comm))
end

theorem Mv.pack_pre {D₀ : D7} {L : LocAll (lay0 D₀)} (m : Mv (withLoc L)) {cf : CharFrame D₀} {C : NChoice D₀} (tp : TupTied D₀ cf C) :
    (⟨m.D, m.cf (cfL L cf), m.ch (chL L C), m.tp (tpL L tp)⟩ : Σ D : D7, Σ c : CharFrame D, Σ C : NChoice D, TupTied D c C) =
      ⟨withLoc (m.pre.loc L), cfL (m.pre.loc L) (m.pre.cf cf), chL (m.pre.loc L) (m.pre.ch C), tpL (m.pre.loc L) (m.pre.tp tp)⟩ :=
  (@Eq.refl (@Sigma D7 fun D ↦ @Sigma (CharFrame D) fun c ↦ @Sigma (NChoice D) fun C ↦ TupTied D c C) (@Sigma.mk D7 (fun D ↦ @Sigma (CharFrame D) fun c ↦ @Sigma (NChoice D) fun C ↦ TupTied D c C) (@D (@withLoc D₀ L) m) (@Sigma.mk (CharFrame (@D (@withLoc D₀ L) m)) (fun c ↦ @Sigma (NChoice (@D (@withLoc D₀ L) m)) fun C ↦ TupTied (@D (@withLoc D₀ L) m) c C) (@Mv.cf (@withLoc D₀ L) m (@cfL D₀ L cf)) (@Sigma.mk (NChoice (@D (@withLoc D₀ L) m)) (fun C ↦ TupTied (@D (@withLoc D₀ L) m) (@Mv.cf (@withLoc D₀ L) m (@cfL D₀ L cf)) C) (@ch (@withLoc D₀ L) m (@chL D₀ L C)) (@Mv.tp (@withLoc D₀ L) m (@cfL D₀ L cf) (@chL D₀ L C) (@tpL D₀ L cf C tp))))))

end GlobalTheory.LayerMove
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitOfPowEqOne
open CategoryTheory AlgebraicGeometry NumberField MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WeilTorsChar

theorem exists_mulEquiv_points {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G']
    (φ : G'.left ⟶ G.left) (h : IsGrpPullback G' G f φ) (T : Over S') :
    ∃ Φ : (T ⟶ G') ≃* (Over.mk (T.hom ≫ f) ⟶ G), ∀ x, (Φ x).left = x.left ≫ φ := by
  let F : (T ⟶ G') → (Over.mk (T.hom ≫ f) ⟶ G) := fun x =>
    Over.homMk (x.left ≫ φ) (by
      change (x.left ≫ φ) ≫ G.hom = T.hom ≫ f
      rw [Category.assoc, h.1.w, ← Category.assoc, Over.w x])
  let I : (Over.mk (T.hom ≫ f) ⟶ G) → (T ⟶ G') := fun y =>
    Over.homMk (h.1.lift y.left T.hom (Over.w y)) (h.1.lift_snd _ _ _)
  refine ⟨⟨⟨F, I, fun x => ?_, fun y => ?_⟩, fun x y => ?_⟩, fun _ => rfl⟩
  · apply Over.OverMorphism.ext
    apply h.1.hom_ext
    · exact h.1.lift_fst _ _ _
    · exact (h.1.lift_snd _ _ _).trans (Over.w x).symm
  · apply Over.OverMorphism.ext
    exact h.1.lift_fst _ _ _
  · apply Over.OverMorphism.ext
    exact (h.2 T x y (F x) (F y) rfl rfl).symm

end GlobalTheory.WeilTorsChar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadWMemGoodW
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EigSpanDesc

section Real

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def iotaR (R : RealDat3 D A3 Ks) (i : Fin D.R.m) :
    (Fin (R.nW i) → D.what₂.LL) →ₛₗ[sg0 D A3.A] Formalism.IndefR.Mult.MMap (R.MW i (sg0 D A3.A)) :=
  (R.HW i (sg0 D A3.A)).e.comp ((R.FW i).j (sg0 D A3.A))

theorem iotaR_apply (R : RealDat3 D A3 Ks) (i : Fin D.R.m) (v : Fin (R.nW i) → D.what₂.LL) :
    iotaR R i v = (R.HW i (sg0 D A3.A)).e ((R.FW i).j (sg0 D A3.A) v) := rfl

variable {R : RealDat D A3.A Ks} {F : Face D A3.A} {X0 : BaseLevelRowSide D}

theorem readW_mem_goodW (Y : Read (A3 := A3) R F X0) (i : Fin D.R.m) (y : D.what₂.Mj ((i : ℕ) + 1)) :
    GlobalTheory.EigRows.readW Y i y ∈ GlobalTheory.EigRows.goodW R F i := by
  obtain ⟨a, ha, e⟩ := Submodule.mem_map.1 (Y.IL.jMj i y).2
  have h' : a = GlobalTheory.EigRows.readW Y i y :=
    (PiTensorProduct.lift : Formalism.IndefR.Mult.MMap (R.MW i (sg0 D A3.A)) ≃ₗ[ℂ] _).injective
      (e.trans (GlobalTheory.EigRows.lift_readW Y i y).symm)
  exact h' ▸ ha

theorem goodW_le_parts (Y : Read (A3 := A3) R F X0) (hI : Rows.IsotInternal D.what₂) (hG : GlobalTheory.EigRows.OccGood D)
    (i : Fin D.R.m) (n : ℕ) (hn : (i : ℕ) + 1 = n) :
    GlobalTheory.EigRows.goodW R F i ≤ ⨆ σ ∈ {σ | D.what₂.isot n σ ≠ ⊥ ∧ D.nd.goodRow σ},
      (D.what₂.isot ((i : ℕ) + 1) σ).map (GlobalTheory.EigRows.readW Y i) := by
  subst hn
  intro z hz
  obtain ⟨y, rfl⟩ := GlobalTheory.EigRows.exists_readW Y i hz
  have hy : y ∈ ⨆ σ, D.what₂.isot ((i : ℕ) + 1) σ := by
    rw [(hI _ (Nat.le_add_left 1 i) i.2).submodule_iSup_eq_top]; trivial
  have key : (⨆ σ, D.what₂.isot ((i : ℕ) + 1) σ) ≤ (⨆ σ ∈ {σ | D.what₂.isot ((i : ℕ) + 1) σ ≠ ⊥ ∧ D.nd.goodRow σ},
      (D.what₂.isot ((i : ℕ) + 1) σ).map (GlobalTheory.EigRows.readW Y i)).comap (GlobalTheory.EigRows.readW Y i) := by
    refine iSup_le fun σ => ?_
    by_cases h0 : D.what₂.isot ((i : ℕ) + 1) σ = ⊥
    · rw [h0]; exact bot_le
    · intro u hu
      exact Submodule.mem_comap.2 (Submodule.mem_iSup_of_mem σ (Submodule.mem_iSup_of_mem
        (show σ ∈ {σ | D.what₂.isot ((i : ℕ) + 1) σ ≠ ⊥ ∧ D.nd.goodRow σ} from ⟨h0, hG _ (Nat.le_add_left 1 i) i.2 σ h0⟩)
        (Submodule.mem_map_of_mem hu)))
  exact key hy

end Real

end GlobalTheory.EigSpanDesc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceComponentUniquePointEachFlag
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceComponentUniquePointEachFlag
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

namespace GlobalTheory.CarryAll

theorem carry_some : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (K : Type) [Field K] (χ : c.F →+* K) (p : Sp K ⟶ C.Y.X), p ≫ C.π ≫ genStr Z = spMap χ → ∃ g : EigFrame Z χ (p ≫ C.π ≫ genι Z), C.Carries p g := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C K _ χ p hp
  let y : C.Y.X := p (IsLocalRing.closedPoint K)
  let ψ : C.Y.X.presheaf.stalk y →+* K := (Scheme.stalkClosedPointTo p).hom
  have hfac : p = spMap ψ ≫ stalkPt C.Y y := (Scheme.Spec_stalkClosedPointTo_fromSpecStalk p).symm
  obtain ⟨φ, fr, t, hT, -⟩ := C.gr_spec y
  obtain ⟨g, hg⟩ := EigFrame.exists_baseChange E H Dw l Xo c O β Z _ K φ (stalkPt C.Y y ≫ C.π ≫ genι Z) fr ψ
  have hs : stalkPt C.Y y ≫ C.π ≫ genStr Z = spMap φ := by
    obtain ⟨s', hs'⟩ : ∃ s' : c.F →+* C.Y.X.presheaf.stalk y, spMap s' = stalkPt C.Y y ≫ C.π ≫ genStr Z :=
      ⟨(Spec.preimage (stalkPt C.Y y ≫ C.π ≫ genStr Z)).hom, Spec.map_preimage _⟩
    rw [← hs']
    congr 1
    have ha : Function.Injective (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField) :=
      IsFractionRing.injective _ _
    have h2 : (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField).comp s' = constF e C.Y := by
      apply GlobalTheory.ShFam.EigLoc.spMap_inj
      rw [GlobalTheory.ShFam.TieBase.spMap_trans, hs', ← GlobalTheory.ShFam.TieBase.genericPt_str e C.Y C.π C.π_str,
        GlobalTheory.ShFam.TieBase.genericPt_eq C.Y y]
      simp only [Category.assoc]
    refine RingHom.ext fun r => ha ?_
    have := DFunLike.congr_fun (h2.trans hT.2.1) r
    exact this
  have hφ : χ = ψ.comp φ := by
    apply GlobalTheory.ShFam.EigLoc.spMap_inj
    rw [GlobalTheory.ShFam.TieBase.spMap_trans, ← hs, ← hp, hfac]
    simp only [Category.assoc]
  subst hφ
  have key : ∀ q : Sp K ⟶ C.Y.X, q = spMap ψ ≫ stalkPt C.Y y →
      ∃ g : EigFrame Z (ψ.comp φ) (q ≫ C.π ≫ genι Z), C.Carries q g := by
    intro q hq
    subst hq
    refine ⟨g, y, ψ, φ, fr, t, 1, rfl, hT, rfl, rfl, fun τ i => ⟨Pi.single i 1, by simp, fun k hk => Pi.single_eq_of_ne hk.ne' _, ?_⟩⟩
    have e' : (fun k => spMap (Formalism.L2.Pj.dualMap ψ) ≫ fr.v τ k) = g.v τ := funext fun k => (hg τ k).symm
    rw [e']
    exact isCombAtG_single Z.t _ (g.tan τ) i
  exact key p hfac

theorem carries_everywhere : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (N : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ N) (Φ : FlagTor Z e U) (k : U.Comp) (X : Var F) (j : X.X ⟶ gen Z), IsOpenImmersion j → j ≫ genStr Z ≫ spMap e.toRingHom = X.str → ∀ (f : (Φ.C k).Y.X ⟶ X.X), f ≫ j = (Φ.C k).π → ∀ (K : Type) [Field K] [IsAlgClosed K] (χ : c.F →+* K) (x : Sp K ⟶ X.X), x ≫ j ≫ genStr Z = spMap χ → ∀ g : EigFrame Z χ (x ≫ j ≫ genι Z), ∃! p : Sp K ⟶ (Φ.C k).Y.X, p ≫ f = x ∧ (Φ.C k).Carries p g := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e σ N U Φ k X j hj hstr f hf K _ _ χ x hx g
  have hm : Mono j := by have := hj; infer_instance
  have hx' : (x ≫ j) ≫ genStr Z = spMap χ := by rw [Category.assoc]; exact hx
  have tr : ∀ (C : FlagCpt Z e) (p : Sp K ⟶ C.Y.X) (a b : Sp K ⟶ Z.X) (h : a = b) (g₀ : EigFrame Z χ a),
      C.Carries p g₀ → C.Carries p (h ▸ g₀) := by
    intro C p a b h g₀ hg; subst h; exact hg
  obtain ⟨p, hp⟩ := GlobalTheory.T.exists_flagComponent_point_over_geometricBasePoint E H Dw l Xo c O β Z F e σ N U Φ k X j hj hstr f hf (GlobalTheory.T.flagSpaceComponent_carries_every_frame_flag E H Dw l Xo c O β Z F e σ N U Φ)
    (fun i K _ χ p h => carry_some E H Dw l Xo c O β Z F e (Φ.C i) K χ p h) K χ x hx
  have hπ : p ≫ (Φ.C k).π = x ≫ j := by rw [← hf, ← Category.assoc, hp]
  obtain ⟨g₀, hg₀⟩ := carry_some E H Dw l Xo c O β Z F e (Φ.C k) K χ p (by rw [← Category.assoc, hπ, Category.assoc]; exact hx)
  have h1 : p ≫ (Φ.C k).π ≫ genι Z = (x ≫ j) ≫ genι Z := by rw [← Category.assoc, hπ]
  obtain ⟨p', hp', hc⟩ := GlobalTheory.T.flagSpaceComponent_carries_every_frame_flag E H Dw l Xo c O β Z F e σ N U Φ k K χ (x ≫ j) hx' (h1 ▸ g₀) g p hπ (tr _ p _ _ h1 g₀ hg₀)
  obtain ⟨q, -, hqu⟩ := Φ.lifts K χ (x ≫ j) hx' g
  have e' := hqu ⟨k, p'⟩ ⟨hp', hc⟩
  refine ⟨p', ⟨(cancel_mono j).1 (by rw [Category.assoc, hf, hp']), hc⟩, fun p₂ ⟨h₂, c₂⟩ => ?_⟩
  have e₂ := hqu ⟨k, p₂⟩ ⟨by rw [← hf, ← Category.assoc, h₂], c₂⟩
  exact eq_of_heq (Sigma.mk.inj_iff.1 (e₂.trans e'.symm)).2

end GlobalTheory.CarryAll
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceComponentUniquePointEachFlagStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagSpace_component_unique_point_each_flag : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (N : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ N) (Φ : FlagTor Z e U) (k : U.Comp) (X : Var F) (j : X.X ⟶ gen Z), IsOpenImmersion j → j ≫ genStr Z ≫ spMap e.toRingHom = X.str → ∀ (f : (Φ.C k).Y.X ⟶ X.X), f ≫ j = (Φ.C k).π → ∀ (K : Type) [Field K] [IsAlgClosed K] (χ : c.F →+* K) (x : Sp K ⟶ X.X), x ≫ j ≫ genStr Z = spMap χ → ∀ g : EigFrame Z χ (x ≫ j ≫ genι Z), ∃! p : Sp K ⟶ (Φ.C k).Y.X, p ≫ f = x ∧ (Φ.C k).Carries p g := by
  first | exact @GlobalTheory.CarryAll.carries_everywhere | exact GlobalTheory.CarryAll.carries_everywhere | (intros; apply GlobalTheory.CarryAll.carries_everywhere <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AntisymmChernRootsMulFibrePoint
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.GoodMetric.FibreAntisymm
open GlobalTheory.GoodMetric

theorem rename_chernRoots (ι : Type) [Fintype ι] (m : ι → ℕ) (w : ∀ τ, Equiv.Perm (Fin (m τ)))
    (R : MvPolynomial (ι × ℕ) ℝ) :
    rename (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) (chernRoots m R) = chernRoots m R := by
  have h : (rename (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m))).comp (chernRoots m) = chernRoots m := by
    apply MvPolynomial.algHom_ext
    intro x
    simp only [AlgHom.comp_apply, chernRoots, aeval_X, rename_rename]
    have e : ((fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) ∘ Sigma.mk x.1) = Sigma.mk x.1 ∘ (w x.1) := by
      funext i; rfl
    rw [e, ← rename_rename, rename_esymm]
  exact AlgHom.congr_fun h R

theorem antisymm_chernRoots_mul (ι : Type) [Fintype ι] (m : ι → ℕ) (R : MvPolynomial (ι × ℕ) ℝ)
    (Q : MvPolynomial (Root m) ℝ) : antisymm (chernRoots m R * Q) = chernRoots m R * antisymm Q := by
  unfold antisymm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [map_mul, rename_chernRoots, mul_smul_comm]

theorem prod_Ioi_rev {R : Type*} [CommRing R] {N : ℕ} (v : Fin N → R) :
    (∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (v (Fin.rev i) - v (Fin.rev j))) = ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (v j - v i) := by
  have h : ∀ f : Fin N → Fin N → R, (∏ i : Fin N, ∏ j ∈ Finset.Ioi i, f i j) =
      ∏ i : Fin N, ∏ j : Fin N, if i < j then f i j else 1 := by
    intro f
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Finset.prod_filter]
    congr 1
    ext j; simp
  rw [h, h, ← Fintype.prod_prod_type' (f := fun i j => if i < j then v (Fin.rev i) - v (Fin.rev j) else 1),
    ← Fintype.prod_prod_type' (f := fun i j => if i < j then v j - v i else 1)]
  refine Fintype.prod_equiv ((Equiv.prodComm _ _).trans (Fin.revPerm.prodCongr Fin.revPerm)) _ _ fun p => ?_
  simp [Fin.rev_lt_rev]

theorem sum_sign_prod_neg_pow {R : Type*} [CommRing R] {N : ℕ} (v : Fin N → R) :
    (∑ σ : Equiv.Perm (Fin N), (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : R) * ∏ i : Fin N, (-v (σ i)) ^ (N - 1 - (i : ℕ))) =
      ∏ j : Fin N, ∏ i ∈ Finset.Iio j, (v j - v i) := by
  let M : Matrix (Fin N) (Fin N) R := Matrix.of fun j i => (-v j) ^ (N - 1 - (i : ℕ))
  have h1 : M.det = ∑ σ : Equiv.Perm (Fin N), (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : R) * ∏ i : Fin N, (-v (σ i)) ^ (N - 1 - (i : ℕ)) := by
    rw [Matrix.det_apply']
    rfl
  have h2 : M.submatrix Fin.revPerm Fin.revPerm = Matrix.vandermonde (fun j => -v (Fin.rev j)) := by
    ext j i
    simp only [M, Matrix.submatrix_apply, Matrix.of_apply, Matrix.vandermonde_apply, Fin.revPerm_apply, Fin.val_rev]
    congr 1
    omega
  rw [← h1, ← Matrix.det_submatrix_equiv_self Fin.revPerm, h2, Matrix.det_vandermonde,
    GlobalTheory.GoodMetric.RootDiscrPerm.prod_Iio_eq_det, Matrix.det_vandermonde, ← prod_Ioi_rev]
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  simp only [Fin.rev_rev]
  ring

theorem antisymm_fibrePoint (ι : Type) [Fintype ι] (m : ι → ℕ) : antisymm (fibrePoint m) = rootDiscr m := by
  have hw : ∀ w : ∀ τ, Equiv.Perm (Fin (m τ)),
      ((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) • rename (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) (fibrePoint m) =
        ∏ τ, ((((Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) : MvPolynomial (Root m) ℝ) *
          ∏ i : Fin (m τ), (-(X (⟨τ, w τ i⟩ : Root m) : MvPolynomial (Root m) ℝ)) ^ (m τ - 1 - (i : ℕ))) := by
    intro w
    unfold fibrePoint
    rw [map_prod, Fintype.prod_sigma, zsmul_eq_mul, Units.coe_prod, Int.cast_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [map_pow, map_neg, rename_X]
  unfold antisymm
  rw [Finset.sum_congr rfl fun w _ => hw w]
  rw [← Fintype.prod_sum (fun τ (σ : Equiv.Perm (Fin (m τ))) => ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : MvPolynomial (Root m) ℝ) *
          ∏ i : Fin (m τ), (-(X (⟨τ, σ i⟩ : Root m) : MvPolynomial (Root m) ℝ)) ^ (m τ - 1 - (i : ℕ))))]
  unfold rootDiscr
  refine Finset.prod_congr rfl fun τ _ => ?_
  exact sum_sign_prod_neg_pow (fun i : Fin (m τ) => (X (⟨τ, i⟩ : Root m) : MvPolynomial (Root m) ℝ))

end GlobalTheory.GoodMetric.FibreAntisymm

namespace GlobalTheory.GoodMetric

theorem antisymm_chernRoots_mul_fibrePoint : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (R : MvPolynomial (ι × ℕ) ℝ),
    GlobalTheory.GoodMetric.antisymm (GlobalTheory.GoodMetric.chernRoots m R * GlobalTheory.GoodMetric.fibrePoint m) =
      GlobalTheory.GoodMetric.chernRoots m R * GlobalTheory.GoodMetric.rootDiscr m := by
  intro ι _ m R
  rw [FibreAntisymm.antisymm_chernRoots_mul, FibreAntisymm.antisymm_fibrePoint]

end GlobalTheory.GoodMetric
end
