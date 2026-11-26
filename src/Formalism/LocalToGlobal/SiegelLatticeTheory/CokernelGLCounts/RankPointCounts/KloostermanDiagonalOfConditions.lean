module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.KloostermanCosetSumLe
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UnitaryDimensionFormula
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.InPOfMemPow
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefNotInt
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsDenominatorSecond
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXLeaves

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.KloostermanDiagonalOfConditions
noncomputable section

open Formalism.L2.SG.Full Formalism.L2.SG.KappaOffDiagonal

namespace Formalism.L2.SG.KappaOffDiagonal

theorem corankPosC_holds : Formalism.L2.SG.RowsConc.CorankPosC :=
  fun _ _ Y u u' _ => Formalism.L2.SG.Pf.SatGram.corankPos_tO Y u u'

end Formalism.L2.SG.KappaOffDiagonal
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AlTieFD
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.AlTieFD

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets
  Formalism.L2.SG.Pf.AlTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word)

def DiscriminantAbsEq : Prop := |(NumberField.discr X.B.I.F : ℝ)| = |(NumberField.discr D.host.F : ℝ)|

def InfinitePlacesCardEq : Prop := Fintype.card (NumberField.InfinitePlace X.B.I.F) = Module.finrank ℚ D.host.F

def EulerProductEta : Prop :=
  ∀ i : ℕ, 2 ≤ i → HasProd (fun v : PlX X =>
      (1 - ((etaV (E := X.B.I.E) v : ℤ) : ℝ) ^ i / ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ i)⁻¹)
      (Formalism.HermitianLattices.Ext.L3.lValEtaF D.host.E D.host.F i)

def LocalFactorProduct : Prop :=
  HasProd (fun v : PlX X => if (((D.mem u).A.T : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal then
      1 - ((etaV (E := X.B.I.E) v : ℤ) : ℝ) ^ D.R.k / ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ D.R.k else 1)
    (∏' 𝔭 : {𝔭 : Ideal (𝓞 D.host.F) // 𝔭.IsMaximal},
      (if (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ 𝔭.1 then
        1 - Formalism.HermitianLattices.Ext.L3.etaF D.host.E D.host.F 𝔭.1 ^ D.R.k * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(D.R.k : ℤ)) else 1))

def VInvEqHalfRootDiscriminant : Prop :=
  Formalism.HermitianLatticesTheory.vInv D.host.E = |(NumberField.discr D.host.F : ℝ)| ^ ((1 : ℝ) / Module.finrank ℚ D.host.F) / 2

def QuadraticInfinitePlaces : Prop := Formalism.HermitianLatticesTheory.fDeg D.host.E = Module.finrank ℚ D.host.F

def DifferentGeneratorUnit : Prop := ∀ p : TypX X, absV p.1 (dV p.1) = 1

def TypedGeneratorProduct : Prop := ∏ p : TypX X, (gAt X p.1 : ℝ) = ((Lat.gS D : ℕ) : ℝ) ^ Module.finrank ℚ D.host.F

theorem discriminant_abs_eq : DiscriminantAbsEq X := by
  unfold DiscriminantAbsEq
  rw [NumberField.discr_eq_discr_of_algEquiv X.B.I.F (RingEquiv.toRatAlgEquiv (Formalism.L2.GlobalTheoryTheory.AFTransport.iotaF X))]

theorem finrank_eq : Module.finrank ℚ X.B.I.F = Module.finrank ℚ D.host.F :=
  (RingEquiv.toRatAlgEquiv (Formalism.L2.GlobalTheoryTheory.AFTransport.iotaF X)).toLinearEquiv.finrank_eq

theorem infinite_places_card : InfinitePlacesCardEq X := by
  unfold InfinitePlacesCardEq
  rw [← finrank_eq X]
  haveI := X.B.I.cm.totReal
  have h1 := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank X.B.I.F
  rw [NumberField.IsTotallyReal.nrComplexPlaces_eq_zero, mul_zero, add_zero] at h1
  rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    NumberField.IsTotallyReal.nrComplexPlaces_eq_zero, add_zero, h1]

theorem T_not_mem (w : D.what₂.Word) (p : TypX X) : ¬ ((((D.mem w).A.T : ℕ) : 𝓞 X.B.I.F) ∈ p.1.asIdeal) := by
  intro hw
  have hc := (resChar_eq_iff (plEquiv X p.1) (D.mem w).A.T_prime).2 ((natCast_mem_plEquiv X p.1 _).2 hw)
  rcases (typAt_iff X p.1).1 p.2 with h | h
  · exact D.T_ne_g w 0 (hc.symm.trans h)
  · exact D.T_ne_g w 1 (hc.symm.trans h)

theorem local_a_factor_symmetric : ∀ p : TypX X,
    aP (E := X.B.I.E) p.1 D.R.k X.B.I.n (Tw u') = aP (E := X.B.I.E) p.1 D.R.k X.B.I.n (Tw u) := by
  intro p
  unfold aP Tw
  rw [if_neg (T_not_mem X u' p), if_neg (T_not_mem X u p)]

theorem fieldDict_of (h3 : EulerProductEta X) (h4 : LocalFactorProduct X u) (h5 : VInvEqHalfRootDiscriminant (D := D)) (h6 : QuadraticInfinitePlaces (D := D)) (h8 : DifferentGeneratorUnit X)
    (h10 : TypedGeneratorProduct X) : Formalism.L2.SG.Pf.NcVal.FieldDict X u u' := by
  unfold Formalism.L2.SG.Pf.NcVal.FieldDict
  exact ⟨discriminant_abs_eq X, infinite_places_card X, h3, h4, h5, h6, X.n_eq, h8, local_a_factor_symmetric X u u', h10⟩

theorem over_g_of_typed (p : TypX X) : ∃ i : Fin 2, ((D.host.g i : ℕ) : 𝓞 X.B.I.F) ∈ p.1.asIdeal := by
  have h := (mem_typSet X.B.I.F _ _ (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero p.1).1 p.2
  rcases h with h | h
  exacts [⟨0, h⟩, ⟨1, h⟩]

theorem not_dvd_diff (v : HeightOneSpectrum (𝓞 X.B.I.F)) (i : Fin 2)
    (hv : ((D.host.g i : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal) : ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 X.B.I.F) := by
  let _ : Algebra X.B.I.F D.host.E := (X.ιE.toRingHom.comp (algebraMap X.B.I.F X.B.I.E)).toAlgebra
  have hp := D.host.g_prime i
  obtain ⟨he, -⟩ := Formalism.L2.SG.Pf.TypedLoc.tower_ef X.B.I.F D.host.E hp (D.nd.g_split i) v hv
  have hvq : v.asIdeal ∈ (Ideal.span {((D.host.g i : ℕ) : ℤ)}).primesOver (𝓞 X.B.I.F) := by
    rw [Formalism.L2.SG.Pf.TypedLoc.primesOver_eq X.B.I.F hp]; exact ⟨v, hv, rfl⟩
  have : v.asIdeal.LiesOver (Ideal.span {((D.host.g i : ℕ) : ℤ)}) := hvq.2
  have : v.asIdeal.IsPrime := v.isPrime
  rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ (Formalism.L2.SG.Pf.TypedLoc.span_p_ne_bot hp)] at he
  rw [not_dvd_differentIdeal_iff, Algebra.isUnramifiedAt_iff_of_isDedekindDomain]
  exact he

theorem different_generator_unit : DifferentGeneratorUnit X := by
  intro p
  obtain ⟨i, hi⟩ := over_g_of_typed X p
  have hnd := not_dvd_diff X p.1 i hi
  have hex : ∃ x ∈ differentIdeal ℤ (𝓞 X.B.I.F), x ∉ p.1.asIdeal := by
    by_contra hc
    push Not at hc
    exact hnd (Ideal.dvd_iff_le.2 hc)
  have hval : ∀ x : 𝓞 X.B.I.F,
      Valued.v (algebraMap X.B.I.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv X.B.I.F p.1) (x : X.B.I.F)) = p.1.intValuation x := by
    intro x
    have h := IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := X.B.I.F) p.1 x
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap] at h
    exact h
  have hv1 : Valued.v (dV p.1) = 1 := by
    unfold dV
    split_ifs with hd
    · obtain ⟨-, hle, x0, -, heq⟩ := hd.choose_spec
      obtain ⟨x1, hx1, hx1n⟩ := hex
      have h1 := hle x1 hx1
      rw [hval, (IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff).2 hx1n] at h1
      rw [hval] at heq
      have h2 := p.1.intValuation_le_one x0
      rw [heq] at h2
      exact le_antisymm h2 h1
    · exact map_one _
  unfold absV
  split_ifs with h0
  · exact absurd (hv1 ▸ h0) one_ne_zero
  · have e2 : WithZero.unzero h0 = 1 := by
      apply WithZero.coe_inj.1
      rw [WithZero.coe_unzero, hv1, WithZero.coe_one]
    rw [e2]
    simp

theorem not_both (v : HeightOneSpectrum (𝓞 X.B.I.F)) (h0 : ((D.host.g 0 : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal)
    (h1 : ((D.host.g 1 : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal) : False := by
  have hcop : IsCoprime ((D.host.g 0 : ℕ) : ℤ) ((D.host.g 1 : ℕ) : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
    exact (Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).mpr D.host.g_ne
  obtain ⟨a, b, hab⟩ := hcop
  have hone : (1 : 𝓞 X.B.I.F) ∈ v.asIdeal := by
    have e := congrArg (Int.cast : ℤ → 𝓞 X.B.I.F) hab
    push_cast at e
    rw [← e]
    exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ h0) (v.asIdeal.mul_mem_left _ h1)
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr hone)

theorem card_over (i : Fin 2) :
    ({v : HeightOneSpectrum (𝓞 X.B.I.F) | ((D.host.g i : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal}).ncard =
      Module.finrank ℚ X.B.I.F := by
  let _ : Algebra X.B.I.F D.host.E := (X.ιE.toRingHom.comp (algebraMap X.B.I.F X.B.I.E)).toAlgebra
  have hp := D.host.g_prime i
  have := Formalism.L2.SG.Pf.TypedLoc.span_p_maximal hp
  have hq0 := Formalism.L2.SG.Pf.TypedLoc.span_p_ne_bot hp
  have hsum := Ideal.sum_ramification_inertia (𝓞 X.B.I.F) ℚ X.B.I.F hq0
  have hall : ∀ Q ∈ IsDedekindDomain.primesOverFinset (Ideal.span {((D.host.g i : ℕ) : ℤ)}) (𝓞 X.B.I.F),
      (Ideal.span {((D.host.g i : ℕ) : ℤ)}).ramificationIdx' Q * (Ideal.span {((D.host.g i : ℕ) : ℤ)}).inertiaDeg' Q = 1 := by
    intro Q hQ
    rw [IsDedekindDomain.mem_primesOverFinset_iff hq0] at hQ
    have hQ' : Q ∈ (Ideal.span {((D.host.g i : ℕ) : ℤ)}).primesOver (𝓞 X.B.I.F) := hQ
    rw [Formalism.L2.SG.Pf.TypedLoc.primesOver_eq X.B.I.F hp] at hQ'
    obtain ⟨v, hv, rfl⟩ := hQ'
    obtain ⟨he, hf⟩ := Formalism.L2.SG.Pf.TypedLoc.tower_ef X.B.I.F D.host.E hp (D.nd.g_split i) v hv
    rw [he, hf]
  rw [Finset.sum_congr rfl hall, Finset.sum_const, smul_eq_mul, mul_one] at hsum
  rw [← hsum, ← Set.ncard_coe_finset, IsDedekindDomain.coe_primesOverFinset hq0,
    Formalism.L2.SG.Pf.TypedLoc.primesOver_eq X.B.I.F hp]
  exact (Set.ncard_image_of_injective _ (fun v w hvw => HeightOneSpectrum.ext hvw)).symm

theorem typed_generator_product : TypedGeneratorProduct X := by
  unfold TypedGeneratorProduct
  have hg0 := (D.host.g_prime 0).ne_zero
  have hg1 := (D.host.g_prime 1).ne_zero
  have hA0 := finite_over X.B.I.F (D.host.g 0) hg0
  have hA1 := finite_over X.B.I.F (D.host.g 1) hg1
  have hT : typSet X.B.I.F (D.host.g 0) (D.host.g 1) = hA0.toFinset ∪ hA1.toFinset := by
    ext v
    rw [mem_typSet _ _ _ hg0 hg1, Finset.mem_union, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
    rfl
  have hdisj : Disjoint hA0.toFinset hA1.toFinset :=
    Finset.disjoint_left.2 fun v h0 h1 =>
      not_both X v (hA0.mem_toFinset.1 h0) (hA1.mem_toFinset.1 h1)
  have hc0 : hA0.toFinset.card = Module.finrank ℚ D.host.F := by
    rw [← Set.ncard_eq_toFinset_card _ hA0, card_over X 0, finrank_eq X]
  have hc1 : hA1.toFinset.card = Module.finrank ℚ D.host.F := by
    rw [← Set.ncard_eq_toFinset_card _ hA1, card_over X 1, finrank_eq X]
  have hg0v : ∀ v ∈ hA0.toFinset, (gAt X v : ℝ) = (D.host.g 0 : ℝ) := by
    intro v hv
    rw [gAt, if_pos (show ((D.host.g 0 : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal from hA0.mem_toFinset.1 hv)]
  have hg1v : ∀ v ∈ hA1.toFinset, (gAt X v : ℝ) = (D.host.g 1 : ℝ) := by
    intro v hv
    have h1 : ((D.host.g 1 : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal := hA1.mem_toFinset.1 hv
    rw [gAt, if_neg (fun h0 => not_both X v h0 h1)]
  show ∏ p : ↥(typSet X.B.I.F (D.host.g 0) (D.host.g 1)), (gAt X p.1 : ℝ) = _
  rw [Finset.prod_coe_sort (typSet X.B.I.F (D.host.g 0) (D.host.g 1)) (fun v => (gAt X v : ℝ)), hT,
    Finset.prod_union hdisj, Finset.prod_congr rfl hg0v, Finset.prod_congr rfl hg1v, Finset.prod_const,
    Finset.prod_const, hc0, hc1, ← mul_pow]
  unfold Lat.gS
  push_cast
  rfl

theorem totally_complex_quadratic : QuadraticInfinitePlaces (D := D) := by
  unfold QuadraticInfinitePlaces Formalism.HermitianLatticesTheory.fDeg
  have : IsTotallyComplex D.host.E := (Formalism.L2.SG.Pf.Cnt.field_dictionary_holds D).1.1
  have h1 := NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces D.host.E
  have h2 := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank D.host.E
  have h3 := NumberField.IsTotallyComplex.nrRealPlaces_eq_zero D.host.E
  have h4 := Module.finrank_mul_finrank ℚ D.host.F D.host.E
  rw [Formalism.BasicNotions.Examples₂.finrank_FE D.host] at h4
  omega

theorem field_dictionary_of_leaves (h3 : EulerProductEta X) (h4 : LocalFactorProduct X u) (h5 : VInvEqHalfRootDiscriminant (D := D)) : Formalism.L2.SG.Pf.NcVal.FieldDict X u u' := fieldDict_of X u u' h3 h4 h5 (totally_complex_quadratic (D := D)) (different_generator_unit X) (typed_generator_product X)

theorem discriminant_sq_relation : VInvEqHalfRootDiscriminant (D := D) := by
  unfold VInvEqHalfRootDiscriminant Formalism.HermitianLatticesTheory.vInv
  have h6 : Formalism.HermitianLatticesTheory.fDeg D.host.E = Module.finrank ℚ D.host.F := totally_complex_quadratic
  rw [h6, Formalism.L2.SG.NGCut.LeadingMinorIntegrality.discr_sq]
  congr 1
  push_cast
  rw [abs_pow, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
  congr 1
  have hf : (0 : ℝ) < Module.finrank ℚ D.host.F := by exact_mod_cast Module.finrank_pos
  field_simp
  norm_num

end Formalism.L2.SG.Pf.AlTieFD
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefLoc
noncomputable section

namespace Formalism.L2.SG.Pf.Coef

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
  {δ : ∀ p : PlF D, (D.s.atP p).Fp} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem normRepElig_of (hN : PairVal.NormRepExists D u u' F0 what₂) : NormRepElig u u' F0 what₂ := by
  intro γ w hγ
  obtain ⟨y, hy⟩ := hN γ w hγ.2 (PCount.eligRel_holds γ w hγ) hγ.1.1
  exact ⟨(w, y), hy⟩

theorem locClsE_of (hA : ∀ p, Agree δ M p) (hT : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2])
    (hrows : IsRowReps D F0 what₂) (hN : PairVal.NormRepExists D u u' F0 what₂)
    (hO : ∀ Zd : TermLoc.LocDat D, PCount.InOrbZ Zd u u') : LocClsE M δ u u' F0 what₂ := by
  intro γ w hγ p
  refine ⟨fun a b => ?_, hO ⟨δ, M, hA⟩ w (zT γ) (PCount.atMat_zT hN hrows hγ (PCount.eligRel_holds γ w hγ)) p⟩
  obtain ⟨Λ, hΛ, F', hF'⟩ := dnInDens_of (normRepElig_of hN) hrows γ w hγ
  have hI := PI.CntNotIntW.integral_on_pairs_holds D δ M hA u u' hT F0 what₂ hrows Λ hΛ (zT γ) F' hF' p
  simp only [yT, LsDatumB.sgnP, Matrix.mul_diagonal]
  exact Subring.mul_mem _ (hI a b) (Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) _)

end Formalism.L2.SG.Pf.Coef
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarCohPfE
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching IsDedekindDomain ValuativeRel

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open CohCut

namespace CohIntPf

variable {D : Formalism.BasicNotions.D7}

theorem exists_den {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Submodule.IsFullLattice D.host.E Λ) (x : (VS D).V) :
    ∃ d : 𝓞 D.host.F, d ≠ 0 ∧ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) d • x ∈ Λ :=
  _root_.UpperTheory.Reformulated.B.ExistsBaseFieldIntegerDenominator.exists_den hΛ x

variable (Zd : LocDat D)

theorem bcP_mem_cof {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Submodule.IsFullLattice D.host.E Λ) (x : (VS D).V) :
    {p : PlF D | baseChange₂ D p x ∉ lattice₂ D Zd.M p Λ}.Finite := by
  obtain ⟨d, hd, hdx⟩ := exists_den hΛ x
  have hI : Ideal.span {d} ≠ (0 : Ideal (𝓞 D.host.F)) := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hd
  refine (Ideal.finite_factors hI).subset fun p hp => ?_
  simp only [Set.mem_ofPred_eq] at hp ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  by_contra hnd
  apply hp
  have := p.isPrime
  letI := hΛ
  rw [Formalism.L2.SG.Pf.LocalDenominators.baseChangeAt_mem_localLattice_iff Zd p (Λ := Λ) (by infer_instance)]
  exact (Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF p.asIdeal Λ x).2 ⟨d, hnd, hdx⟩

theorem scal_mem {p : PlF D} (hs : (Zd.M p).split = none)
    (hδ : Zd.δ p ∈ 𝒪[(D.s.atP p).Fp] ∧ (Zd.δ p)⁻¹ ∈ 𝒪[(D.s.atP p).Fp])
    (hu : (D.s.atP p).ιE (uP p : D.host.E) ∈ (D.s.atP p).O ∧ (D.s.atP p).ιE ((uP p : D.host.E)⁻¹) ∈ (D.s.atP p).O)
    (b : Fin (D.R.rS + 1)) : TermLoc.sgnP' D p b * frFac Zd.δ p b ∈ (D.s.atP p).O := by
  have hs' : (D.s.atP p).split = none := by
    have hA := (Zd.agree p).2.2.2.2.2
    rw [hs] at hA
    cases h2 : (D.s.atP p).split with
    | none => rfl
    | some sg =>
      rw [h2] at hA
      exact (hA : False).elim
  refine Subring.mul_mem _ ?_ ?_
  · unfold TermLoc.sgnP'
    rw [hs']
    exact Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) _
  · rw [Formalism.L2.SG.Pf.BBTie.bt_frFac_eq Zd p b]
    set w : (D.s.atP p).Ep := algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Zd.δ p)⁻¹ *
      (D.s.atP p).ιE ((uP p : D.host.E)⁻¹) with hw
    have hwO : w ∈ (D.s.atP p).O :=
      Subring.mul_mem _ (Formalism.L2.SG.Pf.LocalDenominators.alg_mem_O (D.s.atP p) hδ.2) hu.2
    have hinv : (((Formalism.L2.SG.Pf.BBTie.bt_T_unit Zd p).unit⁻¹ : (D.s.atP p).Epˣ) : (D.s.atP p).Ep) = w := by
      apply Units.inv_eq_of_mul_eq_one_right
      rw [IsUnit.unit_spec]
      show algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Zd.δ p) * (D.s.atP p).ιE (uP p : D.host.E) * w = 1
      rw [hw]
      have hδ0 : Zd.δ p ≠ 0 := (Zd.agree p).2.1
      have hu0 := Formalism.L2.SG.Pf.BBTie.uP_ne (D := D) p
      calc algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Zd.δ p) * (D.s.atP p).ιE (uP p : D.host.E) *
            (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Zd.δ p)⁻¹ * (D.s.atP p).ιE ((uP p : D.host.E)⁻¹))
          = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Zd.δ p * (Zd.δ p)⁻¹) *
            (D.s.atP p).ιE ((uP p : D.host.E) * (uP p : D.host.E)⁻¹) := by rw [map_mul, map_mul]; ring
        _ = 1 := by rw [mul_inv_cancel₀ hδ0, mul_inv_cancel₀ hu0, map_one, map_one, mul_one]
    rw [Units.val_pow_eq_pow_val, hinv]
    exact Subring.pow_mem _ hwO _

end CohIntPf

open CohIntPf

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem cohInt_holds : CohInt Zd u u' F0 what₂ := by
  intro hP γ Z F'₂ φ' _
  have hΛ : Submodule.IsFullLattice D.host.E γ.lam := (hP.2.1.1 γ.lam γ.mem).1.1
  have hgood := Formalism.L2.SG.Pf.LocModel.good_cofinite Zd.δ Zd.M Zd.agree ∅
  rw [Filter.eventually_cofinite] at hgood
  refine (hgood.union (Set.finite_iUnion fun b => bcP_mem_cof Zd hΛ (frame F'₂ b))).subset ?_
  intro p hp
  by_contra hn
  simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_iUnion, not_or, not_exists, not_not] at hn
  obtain ⟨hg, hb⟩ := hn
  apply hp
  intro b
  exact Formalism.L2.SG.Pf.LocalDenominators.smul_mem_localLattice Zd p (scal_mem Zd hg.1 hg.2.1 hg.2.2.1 b) (hb b)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SRLift
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CrossTranspose
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CornerShOfKind
noncomputable section

open scoped Classical
open Matrix
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.Pf.PCount

namespace Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem cornerSh_of_kind (δ : ∀ p : PlF D, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D)
    {w w' : Point D.host.E (D.R.rS + 1)} (h : kind w = kind w') : cornerSh δ T T' p w = cornerSh δ T T' p w' := by
  unfold kind at h
  unfold cornerSh
  by_cases h1 : Dmin w D.R.rS = 0 <;> by_cases h2 : Dmin w' D.R.rS = 0
  · simp [h1, h2]
  · simp [h1, h2] at h
  · simp [h1, h2] at h
  · simp only [h1, h2, if_false] at h ⊢
    rw [Option.some.inj h]

theorem sgn_sq (q : ℕ) :
    (∏ b : Fin q, (-1 : D.host.E) ^ (D.R.rS - (b : ℕ))) * (∏ b : Fin q, (-1 : D.host.E) ^ (D.R.rS - (b : ℕ))) = 1 := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun b _ => ?_
  rw [← pow_add, ← two_mul, pow_mul]
  simp

theorem lead_at {w : Point D.host.E (D.R.rS + 1)} {Z : PairVal.MatR D} (hZ : AtMat w Z) (q : ℕ) (hq : q ≤ D.R.rS + 1) :
    leadMinorE Z q = (∏ b : Fin q, (-1 : D.host.E) ^ (D.R.rS - (b : ℕ))) * Dmin w q := by
  have h1 := Formalism.L2.SG.NGCut.LeadingMinorIntegrality.lead_cell (ZhatOM Z) w hZ q
  rw [Formalism.L2.SG.NGCut.LeadingMinorIntegrality.lead_ZhatOM Z q hq, Formalism.L2.SG.NGCut.NormalVectorPairings.leadingMinor_eq_pointMinor w q hq] at h1
  rw [h1, ← mul_assoc, sgn_sq, one_mul]

theorem cross_of_kind {w w' : Point D.host.E (D.R.rS + 1)} {Z Z' : PairVal.MatR D} (hk : kind w = kind w')
    (hZ : AtMat w Z) (hZ' : AtMat w' Z') :
    leadMinorE Z D.R.rS * leadMinorE Z' (D.R.rS + 1) = leadMinorE Z' D.R.rS * leadMinorE Z (D.R.rS + 1) := by
  rw [lead_at hZ _ (Nat.le_succ _), lead_at hZ' _ le_rfl, lead_at hZ' _ (Nat.le_succ _), lead_at hZ _ le_rfl]
  have key : Dmin w D.R.rS * Dmin w' (D.R.rS + 1) = Dmin w' D.R.rS * Dmin w (D.R.rS + 1) := by
    unfold kind at hk
    by_cases h1 : Dmin w D.R.rS = 0 <;> by_cases h2 : Dmin w' D.R.rS = 0
    · rw [h1, h2]; ring
    · simp [h1, h2] at hk
    · simp [h1, h2] at hk
    · simp only [h1, h2, if_false, Option.some.injEq] at hk
      unfold zetaOf at hk
      field_simp at hk
      linear_combination -hk
  linear_combination (∏ b : Fin D.R.rS, (-1 : D.host.E) ^ (D.R.rS - (b : ℕ))) *
    (∏ b : Fin (D.R.rS + 1), (-1 : D.host.E) ^ (D.R.rS - (b : ℕ))) * key

theorem inv_last_mul_det {K : Type*} [CommRing K] {m : ℕ} (Y : Matrix (Fin (m + 1)) (Fin (m + 1)) K)
    (hY : IsUnit Y.det) :
    Y⁻¹ (Fin.last m) (Fin.last m) * Y.det = (Y.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_fin_succ_eq_det_submatrix, smul_eq_mul]
  simp only [Fin.succAbove_last, Fin.val_last]
  rw [show ((-1 : K) ^ (m + m)) = 1 by rw [← two_mul, pow_mul]; simp, one_mul, mul_comm, ← mul_assoc,
    Ring.mul_inverse_cancel _ hY, one_mul]

end Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents
end
end

noncomputable section

open Matrix

namespace Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents

variable {K K' : Type*} [CommRing K] [CommRing K'] {r : ℕ}

def ld (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) : K := (A.submatrix Fin.castSucc Fin.castSucc).det

def Ec (r : ℕ) : Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
  Matrix.of fun a b => if a = Fin.last r ∧ b = Fin.last r then 1 else 0

theorem ld_add_corner (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (t : K) : ld (A + t • Ec r) = ld A := by
  unfold ld
  congr 1
  ext a b
  simp [Ec, Fin.castSucc_ne_last]

theorem det_add_corner (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (t : K) :
    (A + t • Ec r).det = A.det + t * ld A := by
  have hE : A + t • Ec r = A.updateRow (Fin.last r) (A (Fin.last r) + t • Pi.single (Fin.last r) 1) := by
    ext a b
    by_cases ha : a = Fin.last r
    · subst ha
      by_cases hb : b = Fin.last r
      · subst hb; simp [Ec]
      · simp [Ec, hb]
    · simp [Ec, ha]
  rw [hE, Matrix.det_updateRow_add, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self]
  congr 2
  rw [Matrix.det_succ_row _ (Fin.last r), Fin.sum_univ_castSucc]
  have h0 : ∀ j : Fin r, (A.updateRow (Fin.last r) (Pi.single (Fin.last r) 1)) (Fin.last r) j.castSucc = 0 := by
    intro j
    rw [Matrix.updateRow_self, Pi.single_eq_of_ne (Fin.castSucc_ne_last j)]
  simp only [h0, mul_zero, zero_mul, Finset.sum_const_zero, zero_add, Matrix.updateRow_self,
    Pi.single_eq_same, mul_one, Fin.succAbove_last]
  have hs : (A.updateRow (Fin.last r) (Pi.single (Fin.last r) 1)).submatrix Fin.castSucc Fin.castSucc =
      A.submatrix Fin.castSucc Fin.castSucc := by
    ext a b
    simp only [Matrix.submatrix_apply]
    rw [Matrix.updateRow_ne (Fin.castSucc_ne_last a)]
  rw [hs, ld]
  have hpow : ((-1 : K) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ))) = 1 := Even.neg_one_pow ⟨_, rfl⟩
  rw [hpow, one_mul]

theorem ld_smul (c : K) (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) : ld (c • A) = c ^ r * ld A := by
  unfold ld
  rw [show (c • A).submatrix Fin.castSucc Fin.castSucc = c • A.submatrix Fin.castSucc Fin.castSucc from rfl,
    Matrix.det_smul, Fintype.card_fin]

theorem ld_transpose (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) : ld Aᵀ = ld A := by
  unfold ld
  rw [← Matrix.det_transpose]
  rfl

theorem ld_map (f : K →+* K') (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) : ld (A.map f) = f (ld A) := by
  unfold ld
  rw [RingHom.map_det]
  rfl

def Cross (A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) K) : Prop := ld A * A'.det = ld A' * A.det

theorem cross_shift {A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : Cross A A') (c t : K) :
    Cross (c • A + t • Ec r) (c • A' + t • Ec r) := by
  unfold Cross at h ⊢
  rw [ld_add_corner, ld_add_corner, det_add_corner, det_add_corner, ld_smul, ld_smul, Matrix.det_smul,
    Matrix.det_smul, Fintype.card_fin]
  linear_combination c ^ r * c ^ (r + 1) * h

theorem cross_transpose {A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : Cross A A') : Cross Aᵀ A'ᵀ := by
  unfold Cross at h ⊢
  rw [ld_transpose, ld_transpose, Matrix.det_transpose, Matrix.det_transpose]
  exact h

theorem cross_map (f : K →+* K') {A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : Cross A A') :
    Cross (A.map f) (A'.map f) := by
  unfold Cross at h ⊢
  have e1 : (A'.map f).det = f A'.det := (RingHom.map_det f A').symm
  have e2 : (A.map f).det = f A.det := (RingHom.map_det f A).symm
  rw [ld_map, ld_map, e1, e2, ← map_mul, ← map_mul, h]

theorem cross_scale (x y : Fin (r + 1) → K) {A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : Cross A A') :
    Cross (Matrix.of fun a b => y b * x a * A a b) (Matrix.of fun a b => y b * x a * A' a b) := by
  have e : ∀ B : Matrix (Fin (r + 1)) (Fin (r + 1)) K,
      (Matrix.of fun a b => y b * x a * B a b) = Matrix.diagonal x * B * Matrix.diagonal y := by
    intro B; ext a b; simp [Matrix.diagonal_mul, Matrix.mul_diagonal]; ring
  have el : ∀ B : Matrix (Fin (r + 1)) (Fin (r + 1)) K,
      ld (Matrix.diagonal x * B * Matrix.diagonal y) = (∏ i : Fin r, x i.castSucc) * (∏ i : Fin r, y i.castSucc) * ld B := by
    intro B
    unfold ld
    have : (Matrix.diagonal x * B * Matrix.diagonal y).submatrix Fin.castSucc Fin.castSucc =
        Matrix.diagonal (fun i : Fin r => x i.castSucc) * B.submatrix Fin.castSucc Fin.castSucc *
          Matrix.diagonal (fun i : Fin r => y i.castSucc) := by
      ext a b; simp [Matrix.diagonal_mul, Matrix.mul_diagonal]
    rw [this, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal]
    ring
  unfold Cross at h ⊢
  rw [e, e, el, el, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul]
  linear_combination (∏ i : Fin r, x i.castSucc) * (∏ i : Fin r, y i.castSucc) * (Matrix.diagonal x).det *
    (Matrix.diagonal y).det * h

theorem kappa_eq {A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : Cross A A') (c : K)
    (hu : IsUnit (A + c • (Ec (K := K) r)).det) (hu' : IsUnit (A' + c • (Ec (K := K) r)).det) :
    (A + c • (Ec (K := K) r))⁻¹ (Fin.last r) (Fin.last r) = (A' + c • (Ec (K := K) r))⁻¹ (Fin.last r) (Fin.last r) := by
  have k1 := SplitCoefficientComponents.inv_last_mul_det (A + c • (Ec (K := K) r)) hu
  have k2 := SplitCoefficientComponents.inv_last_mul_det (A' + c • (Ec (K := K) r)) hu'
  have l1 : ((A + c • (Ec (K := K) r)).submatrix Fin.castSucc Fin.castSucc).det = ld A := ld_add_corner A c
  have l2 : ((A' + c • (Ec (K := K) r)).submatrix Fin.castSucc Fin.castSucc).det = ld A' := ld_add_corner A' c
  rw [l1, det_add_corner] at k1
  rw [l2, det_add_corner] at k2
  rw [det_add_corner] at hu hu'
  unfold Cross at h
  obtain ⟨v, hv⟩ := hu
  obtain ⟨v', hv'⟩ := hu'
  have key : (A + c • (Ec (K := K) r))⁻¹ (Fin.last r) (Fin.last r) * ((A.det + c * ld A) * (A'.det + c * ld A')) =
      (A' + c • (Ec (K := K) r))⁻¹ (Fin.last r) (Fin.last r) * ((A.det + c * ld A) * (A'.det + c * ld A')) := by
    have e1 : (A + c • (Ec (K := K) r))⁻¹ (Fin.last r) (Fin.last r) * ((A.det + c * ld A) * (A'.det + c * ld A')) =
        ld A * (A'.det + c * ld A') := by rw [← mul_assoc, k1]
    have e2 : (A' + c • (Ec (K := K) r))⁻¹ (Fin.last r) (Fin.last r) * ((A.det + c * ld A) * (A'.det + c * ld A')) =
        ld A' * (A.det + c * ld A) := by rw [mul_comm (A.det + _), ← mul_assoc, k2]
    rw [e1, e2]
    linear_combination h
  have hunit : IsUnit ((A.det + c * ld A) * (A'.det + c * ld A')) := by
    rw [← hv, ← hv']; exact (v * v').isUnit
  exact hunit.mul_right_cancel key

end Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents
end
end

noncomputable section

open Matrix

namespace Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents

def SRLift : Prop :=
  ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Formalism.MainNotions.S.Loc.Model F E), M.OK → ∀ (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) M.R)
    (K : Submodule M.R (Fin (n + 1) → M.R)),
    (∀ i, A i (Fin.last n) = if i = Fin.last n then 1 else 0) →
    (∀ v : Fin (n + 1) → M.R, ∃ x, v - A.mulVec x ∈ K) →
    ∃ H : Matrix (Fin (n + 1)) (Fin (n + 1)) M.R, (∀ j, (fun i => H i j) ∈ K) ∧ (∀ i, H i (Fin.last n) = 0) ∧
      IsUnit (A + H).det

end Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FrGlobOfFstar
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.BcPFrame
noncomputable section

open scoped Classical
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc
  ValuativeRel

namespace Formalism.L2.SG.Pf.LocalDenominators

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem denF (x : D.host.E) : ∃ d : 𝓞 D.host.F, d ≠ 0 ∧ IsIntegral ℤ (algebraMap D.host.F D.host.E (d : D.host.F) * x) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 D.host.E) x
  have hb0 : (b : D.host.E) ≠ 0 := by
    have : (b : 𝓞 D.host.E) ≠ 0 := nonZeroDivisors.ne_zero hb
    exact_mod_cast this
  have hbi : IsIntegral ℤ (b : D.host.E) := (b : 𝓞 D.host.E).2
  have hbc : IsIntegral ℤ (D.conjF (b : D.host.E)) := hbi.map (D.conjF.toRingHom.toIntAlgHom)
  obtain ⟨t0, ht0⟩ := conjF_fix ((b : D.host.E) * D.conjF (b : D.host.E)) (by rw [map_mul, conjF_invol, mul_comm])
  have ht0i : IsIntegral ℤ t0 := (isIntegral_algebraMap_iff ).1
    (by rw [ht0]; exact hbi.mul hbc)
  refine ⟨⟨t0, ht0i⟩, ?_, ?_⟩
  · intro h
    have h1 : t0 = 0 := congrArg Subtype.val h
    rw [h1, map_zero] at ht0
    have hc0 : D.conjF (b : D.host.E) ≠ 0 := by
      intro hc; apply hb0
      have := congrArg D.conjF hc
      rwa [conjF_invol, map_zero] at this
    exact mul_ne_zero hb0 hc0 ht0.symm
  · show IsIntegral ℤ (algebraMap D.host.F D.host.E t0 *
      (algebraMap (𝓞 D.host.E) D.host.E a / algebraMap (𝓞 D.host.E) D.host.E (b : 𝓞 D.host.E)))
    have e : algebraMap D.host.F D.host.E t0 *
        (algebraMap (𝓞 D.host.E) D.host.E a / algebraMap (𝓞 D.host.E) D.host.E (b : 𝓞 D.host.E)) =
        D.conjF (b : D.host.E) * (a : D.host.E) := by
      rw [ht0]
      have hb0' : algebraMap (𝓞 D.host.E) D.host.E (b : 𝓞 D.host.E) ≠ 0 := hb0
      field_simp
    rw [e]; exact hbc.mul (a : 𝓞 D.host.E).2

theorem denE (p : PlF D) (a : (D.s.atP p).Ep) :
    ∃ d : 𝓞 D.host.F, d ≠ 0 ∧ algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (d : D.host.F)) * a ∈ (D.s.atP p).O := by
  obtain ⟨x, hx, -⟩ := Formalism.L2.SG.Pf.PCountEx.approxE D.s.atP {p} 1 one_ne_zero
    (Function.update (fun q => (0 : (D.s.atP q).Ep)) p a)
  obtain ⟨o, ho, hxo⟩ := hx p (Finset.mem_singleton_self p)
  simp only [Function.update_self, map_one, one_mul] at hxo
  obtain ⟨d, hd0, hdx⟩ := denF x
  refine ⟨d, hd0, ?_⟩
  have hxeq : a = (D.s.atP p).ιE x - o := by rw [← hxo]; ring
  have hd : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (d : D.host.F)) ∈ (D.s.atP p).O := by
    rw [← iE_alg]; exact iE_int (D.s.atP p) ((d : 𝓞 D.host.F).2.map (algebraMap D.host.F D.host.E).toIntAlgHom)
  rw [hxeq, mul_sub]
  refine (D.s.atP p).O.sub_mem ?_ ((D.s.atP p).O.mul_mem hd ho)
  have h2 := iE_int (D.s.atP p) hdx
  rw [map_mul, iE_alg] at h2
  exact h2

theorem baseChangeAt_frame (p : PlF D) (j : Fin (nV D)) : baseChange₂ D p ((VS D).frame j) = Pi.single j 1 := by
  funext i
  simp only [baseChange₂, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Module.Basis.repr_self, Finsupp.single_apply, Pi.single_apply]
  split_ifs with h1 h2 h2 <;> simp_all [eq_comm]


set_option maxHeartbeats 1000000 in
theorem exists_isLattice_eq_localLattice (Zd : LocDat D) (p : PlF D) (M : Submodule (Zd.M p).L.O (Vp D p)) (hfg : M.FG)
    (hsp : Submodule.span (D.s.atP p).Ep (M : Set (Vp D p)) = ⊤) :
    ∃ Λ' : Submodule (𝓞 D.host.E) (VS D).V, Submodule.IsFullLattice D.host.E Λ' ∧ M = lattice₂ D Zd.M p Λ' := by
  let u : 𝓞 D.host.F → (D.s.atP p).Ep := fun d => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (d : D.host.F))
  have u_mem : ∀ d, u d ∈ (D.s.atP p).O := fun d => by
    show algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (d : D.host.F)) ∈ (D.s.atP p).O
    rw [← iE_alg]; exact iE_int (D.s.atP p) ((d : 𝓞 D.host.F).2.map (algebraMap D.host.F D.host.E).toIntAlgHom)
  have u_mul : ∀ a b, u (a * b) = u a * u b := fun a b => by
    show algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF ((a * b : 𝓞 D.host.F) : D.host.F)) = _
    push_cast; rw [map_mul, map_mul]
  have smulM : ∀ {z : (D.s.atP p).Ep}, z ∈ (D.s.atP p).O → ∀ {v : Vp D p}, v ∈ M → z • v ∈ M := fun {z} hz {v} hv => by
    have hz' : z ∈ (Zd.M p).L.O := by rw [hO Zd p]; exact hz
    exact M.smul_mem ⟨z, hz'⟩ hv
  obtain ⟨s, hs⟩ := hfg

  have hall : ∀ j : Fin (nV D), (Pi.single j 1 : Vp D p) ∈ Submodule.span (D.s.atP p).Ep ((s : Set (Vp D p))) := by
    intro j
    have h1 : Submodule.span (D.s.atP p).Ep (s : Set (Vp D p)) = ⊤ := by
      rw [← Submodule.span_span_of_tower (Zd.M p).L.O (D.s.atP p).Ep, hs, hsp]
    rw [h1]; exact Submodule.mem_top
  choose ε _ hε using fun j => Submodule.mem_span_finset.1 (hall j)
  choose d hd0 hdm using fun (j : Fin (nV D)) (m : Vp D p) => denE p (ε j m)
  set c : 𝓞 D.host.F := ∏ j, ∏ m ∈ s, d j m with hcdef
  have hc0 : c ≠ 0 := by
    rw [hcdef, Finset.prod_ne_zero_iff]
    intro j _
    rw [Finset.prod_ne_zero_iff]
    exact fun m _ => hd0 j m
  have hkey : ∀ j, ∀ m ∈ s, u c * ε j m ∈ (D.s.atP p).O := by
    intro j m hm
    have hdv : d j m ∣ c := (Finset.dvd_prod_of_mem _ hm).trans (Finset.dvd_prod_of_mem (fun j => ∏ m ∈ s, d j m)
      (Finset.mem_univ j))
    obtain ⟨r, hr⟩ := hdv
    rw [hr, mul_comm (d j m) r, u_mul, mul_assoc]
    exact (D.s.atP p).O.mul_mem (u_mem r) (hdm j m)
  have hsM : ∀ m ∈ s, m ∈ M := fun m hm => by rw [← hs]; exact Submodule.subset_span hm
  have hce : ∀ j, u c • (Pi.single j 1 : Vp D p) ∈ M := by
    intro j
    rw [← hε j, Finset.smul_sum]
    refine Submodule.sum_mem _ fun m hm => ?_
    rw [smul_smul]
    exact smulM (hkey j m hm) (hsM m hm)
  have hdec : ∀ w : Vp D p, u c • w = ∑ i, w i • (u c • (Pi.single i 1 : Vp D p)) := by
    intro w
    funext j
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ j), mul_comm]
  have hcv : ∀ v : Vp D p, (∀ i, v i ∈ (D.s.atP p).O) → u c • v ∈ M := by
    intro v hv
    rw [hdec v]
    exact Submodule.sum_mem _ fun i _ => smulM (hv i) (hce i)

  have happ : ∀ m : Vp D p, ∃ xm : (VS D).V, ∃ ov : Vp D p, (∀ i, ov i ∈ (D.s.atP p).O) ∧ baseChange₂ D p xm - m = u c • ov := by
    intro m
    have h1 : ∀ i, ∃ x : D.host.E, ∃ o ∈ (D.s.atP p).O, (D.s.atP p).ιE x - m i = u c * o := by
      intro i
      obtain ⟨x, hx, -⟩ := Formalism.L2.SG.Pf.PCountEx.approxE D.s.atP {p} c hc0
        (Function.update (fun q => (0 : (D.s.atP q).Ep)) p (m i))
      obtain ⟨o, ho, hxo⟩ := hx p (Finset.mem_singleton_self p)
      simp only [Function.update_self] at hxo
      exact ⟨x, o, ho, hxo⟩
    choose x o ho hxo using h1
    refine ⟨(VS D).frame.equivFun.symm x, o, ho, ?_⟩
    funext i
    have hr : (VS D).frame.repr ((VS D).frame.equivFun.symm x) i = x i := by
      rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    show (D.s.atP p).ιE ((VS D).frame.repr ((VS D).frame.equivFun.symm x) i) - m i = u c * o i
    rw [hr, hxo i]
  choose xs ov hov hxs using happ
  obtain ⟨G, hG⟩ : ∃ G : Set (VS D).V, G = xs '' (s : Set (Vp D p)) ∪
      Set.range (fun i : Fin (nV D) => algebraMap D.host.F D.host.E (c : D.host.F) • (VS D).frame i) := ⟨_, rfl⟩
  have hGx : ∀ m ∈ s, xs m ∈ G := fun m hm => by rw [hG]; exact Or.inl ⟨m, hm, rfl⟩
  have hGc : ∀ i, algebraMap D.host.F D.host.E (c : D.host.F) • (VS D).frame i ∈ G := fun i => by
    rw [hG]; exact Or.inr ⟨i, rfl⟩
  have hGfin : G.Finite := by rw [hG]; exact (s.finite_toSet.image xs).union (Set.finite_range _)
  obtain ⟨Λ', hΛ'⟩ : ∃ Λ' : Submodule (𝓞 D.host.E) (VS D).V, Λ' = Submodule.span (𝓞 D.host.E) G := ⟨_, rfl⟩
  have hbcf : ∀ i, baseChange₂ D p (algebraMap D.host.F D.host.E (c : D.host.F) • (VS D).frame i) = u c • (Pi.single i 1 : Vp D p) := by
    intro i
    rw [baseChange_smul₂, baseChangeAt_frame, iE_alg]
  have hlat : Submodule.IsFullLattice D.host.E Λ' := by
    have hfg' : Λ'.FG := by
      rw [hΛ']
      exact Submodule.fg_span hGfin
    letI := Submodule.IsLattice.of_fg D.host.E hfg'
    refine ⟨?_⟩
    have hcE : algebraMap D.host.F D.host.E (c : D.host.F) ≠ 0 := by
      apply (map_ne_zero _).mpr
      exact_mod_cast hc0
    apply top_unique
    rw [← (VS D).frame.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe]
    have hi : algebraMap D.host.F D.host.E (c : D.host.F) • (VS D).frame i ∈ Λ' := by
      rw [hΛ']
      exact Submodule.subset_span (hGc i)
    have hinv := (Submodule.span D.host.E (Λ' : Set (VS D).V)).smul_mem
      (algebraMap D.host.F D.host.E (c : D.host.F))⁻¹ (Submodule.subset_span hi)
    simpa only [smul_smul, inv_mul_cancel₀ hcE, one_smul] using hinv
  refine ⟨Λ', hlat, le_antisymm ?_ ?_⟩
  · rw [← hs, Submodule.span_le]
    intro m hm
    have e : m = baseChange₂ D p (xs m) - u c • ov m := by rw [← hxs m]; abel
    rw [SetLike.mem_coe, e]
    refine Submodule.sub_mem _ (Submodule.subset_span ⟨xs m, by rw [hΛ']; exact Submodule.subset_span (hGx m hm), rfl⟩) ?_
    rw [hdec (ov m)]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← hbcf i]
    exact smul_mem_localLattice Zd p (hov m i) (Submodule.subset_span ⟨_, by rw [hΛ']; exact Submodule.subset_span (hGc i), rfl⟩)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, hΛ'] at hy
    rw [SetLike.mem_coe]
    induction hy using Submodule.span_induction with
    | mem y hy =>
      rw [hG] at hy
      rcases hy with ⟨m, hm, rfl⟩ | ⟨i, rfl⟩
      · have e : baseChange₂ D p (xs m) = m + u c • ov m := by rw [← hxs m]; abel
        rw [e]
        exact M.add_mem (hsM m hm) (hcv _ (hov m))
      · rw [hbcf]; exact hce i
    | zero => rw [map_zero]; exact M.zero_mem
    | add a b _ _ ha hb => rw [map_add (f := _)]; exact M.add_mem ha hb
    | smul a y _ hy =>
      rw [oE_smul, baseChange_smul₂]
      exact smulM (iE_int (D.s.atP p) (a : 𝓞 D.host.E).2) hy

end Formalism.L2.SG.Pf.LocalDenominators
end
end

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.TermLoc

namespace Formalism.L2.SG.Pf.FrameGlobalPatching

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
  (what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V))

theorem locFullC_holds : LocFullC Zd u u' F0 what₂ := by
  intro γ w hγ w' hG' hk Z hZ F'₂ φ φ' hF hT p M hM
  exact Formalism.L2.SG.Pf.LocalDenominators.exists_isLattice_eq_localLattice Zd p M hM.1.1.1.1 hM.1.1.1.2.1

theorem patchC_holds : PatchC Zd u u' F0 what₂ := patchC_of_full Zd (locFullC_holds Zd u u' F0 what₂)

variable {Zd u u' F0 what₂}

theorem frGlob_of_fstar (hA : FStarC Zd u u' F0 what₂) : Formalism.L2.SG.Pf.PCount.FrGlob Zd u u' F0 what₂ :=
  frGlob_of Zd hA (patchC_holds Zd u u' F0 what₂)

end Formalism.L2.SG.Pf.FrameGlobalPatching
end
end
