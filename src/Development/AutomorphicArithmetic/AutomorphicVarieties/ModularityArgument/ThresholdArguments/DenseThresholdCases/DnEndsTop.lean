module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.InertiaRankTwo.PotTwo
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.UpperTriangularPlaces.ConjLeftPosAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SymTop
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BirthTop
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnitaryThreeInputsOfLiterature
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.GdEndOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BrAutNew
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.TanA
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnitaryRankTwoFlags
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.CompOfFree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ModNOf

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Pr.IsCD.fin UpperTheory.V.Alg.IsCO.toIsLocalRing UpperTheory.V.Alg.IsCO.complete UpperTheory.V.Alg.IsCO.isLocalHom UpperTheory.V.Alg.IsCO.self UpperTheory.V.UnitaryThreeInertia.Coef.isLocalRing

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.InertiaRankTwo.InertiaConditionRankTwoLinkOfInertia
open UpperTheory.V.Z.Win.Dn

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.U3 UpperTheory.V.Base in
theorem UpperTheory.V.Z.Win.Dn.inertiaConditionRankTwoLink_of_inertia :
    UpperTheory.V.Keep.IneOf → Ine2 := by
  intro hI Ω _ _ _ l _ c _ N _ e ψ η σ g₁ B M _ L _ _ _ _ _ Φ C₀ k _ A _ _ r hr _ _ K _ _ _ _ _ _ hop W hW
  have hd : IsOpen ((Chr.dirG ℚ Ω ψ).ker : Set (G ℚ Ω)) :=
    Subgroup.isOpen_mono (H₁ := (Chr.cls ℚ Ω N).ker) (fun s hs => by
      rw [MonoidHom.mem_ker, Chr.dirG, MonoidHom.comp_apply, MonoidHom.mem_ker.1 hs, map_one])
      (Chr.clsFacts ℚ Ω N).1
  refine hI Ω l 2 W (η.ker ⊓ (Chr.dirG ℚ Ω ψ).ker) (hop.inter hd)
    (le_inf (Abelianization.commutator_subset_ker η) (Abelianization.commutator_subset_ker _)) ?_
  intro A' hA' g hg hH
  have hc : cycZ ℚ Ω l g = 1 := MonoidHom.mem_ker.1 ((places ℚ Ω l A').2.2.2 hA' hg)
  have hχ : chiO ℚ Ω l c.O g = 1 := by
    show Units.map _ (cycZ ℚ Ω l g) = 1
    rw [hc, map_one]
  have hP : Chr.Psi l e (Chr.dirG ℚ Ω ψ) g = 1 := by
    rw [Chr.Psi, MonoidHom.mul_apply, zpow_natCast, MonoidHom.pow_apply, hχ, one_pow, one_mul]
    exact hH.2
  have hr1 : r g = 1 := hr.away A' hA' g hg hH.1 hP
  apply Units.ext
  rw [hW g hH.1]
  have hp : UnitaryThreeInertia.push A.val r g = 1 := by
    rw [MonoidHom.comp_apply, hr1, map_one]
  rw [hp]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [corner, GG.mat, Matrix.one_apply]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DnEnds
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DnHost
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr UpperTheory.V UpperTheory.V.Z.Win
open Formalism.GaloisCohomology UpperTheory.V.Base in
theorem UpperTheory.V.Z.Win.Dn.hostEnd_of_loc3_frame_linkedEnd_downCsdK (h3 : Dn.Loc3) (hK3 : Dn.LocalConditionRankThreeEvenLevel) :
    HostFrameEx → _root_.UpperTheory.V.Z.Sym.Pl.LinkedEndEAlt → _root_.UpperTheory.V.Z.Win.Dn.DownCsdKAlt → _root_.UpperTheory.V.Pr.HostEndAlt := by
  intro hF hL hD K _ _ _ hK Ω _ _ _ l hl ι c N _ e ψ o₁ hd σ hσ B hB
  haveI : IsLocalHom (algebraMap ℤ_[l] c.O) := (dvrFacts l c.O).2.2.1
  haveI : CharP (ResidueField c.O) l := by
    rw [CharP.charP_iff_prime_eq_zero hl.out, ← map_natCast (residue c.O), residue_eq_zero_iff,
      mem_maximalIdeal, mem_nonunits_iff, ← map_natCast (algebraMap ℤ_[l] c.O)]
    intro hu
    exact PadicInt.prime_p.not_unit (isUnit_of_map_unit _ _ hu)
  obtain ⟨L, _, _, _, _, g₁, Φ, C₀, ⟨k⟩, ok, big, sc⟩ := hF Ω l c N e ψ o₁ hd σ hσ B hB
  have hσ' : IsConjOm σ.toRingEquiv := hσ
  have hsq : σ * σ = 1 := by
    obtain ⟨j, hj⟩ := hσ'
    exact AlgEquiv.ext fun x => j.injective (by
      have h1 : j (σ (σ x)) = starRingEnd ℂ (j (σ x)) := hj (σ x)
      have h2 : j (σ x) = starRingEnd ℂ (j x) := hj x
      rw [AlgEquiv.mul_apply, h1, h2, Complex.conj_conj, AlgEquiv.one_apply])
  have hΨ : Chr.Psi l e (Chr.dirG ℚ Ω ψ) σ = 1 := by
    have h1 : cycZ ℚ Ω l σ = -1 := hσ'.cyc (E := ℚ)
    have h2 : chiO ℚ Ω l c.O σ = -1 := by
      show Units.map (algebraMap ℤ_[l] c.O).toMonoidHom (cycZ ℚ Ω l σ) = -1
      rw [h1]
      apply Units.ext
      simp
    have h3 : (Chr.dirG ℚ Ω ψ σ : c.O) = (-1) ^ e := by
      rw [Chr.dirG, MonoidHom.comp_apply, (Chr.clsFacts ℚ Ω N).2.2.2.1 σ hσ', MulChar.coe_toUnitHom]
      exact hd.par
    apply Units.ext
    show ((chiO ℚ Ω l c.O σ ^ (e : ℤ) * Chr.dirG ℚ Ω ψ σ : c.Oˣ) : c.O) = 1
    rw [h2, zpow_natCast, Units.val_mul, h3, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, ← mul_pow]
    simp
  have hram : ∀ B' : ValuationSubring Ω, ¬ Ine (F := ℚ) B' ≤ (UnitaryThreeInertia.eta4 Ω).ker →
      B'.valuation ((l * N : ℕ) : Ω) < 1 := by
    intro B' h
    have h4 : B'.valuation ((4 : ℕ) : Ω) < 1 := by
      by_contra h4
      refine h fun s hs => ?_
      have h5 : Chr.cls ℚ Ω 4 s = 1 := (Chr.clsFacts ℚ Ω 4).2.2.2.2 B' h4 hs
      rw [MonoidHom.mem_ker, UnitaryThreeInertia.eta4, Chr.dirG, MonoidHom.comp_apply, h5, map_one]
    have h2 : B'.valuation ((2 : ℕ) : Ω) < 1 := by
      by_contra h2
      rw [not_lt] at h2
      rw [show (4 : ℕ) = 2 * 2 from rfl, Nat.cast_mul, map_mul] at h4
      exact (not_lt.2 (one_le_mul h2 h2)) h4
    obtain ⟨m, hm⟩ := (hd.N_even.mul_left l).two_dvd
    have hm' : B'.valuation (m : Ω) ≤ 1 := (B'.valuation_le_one_iff _).2 (natCast_mem B' m)
    rw [hm, Nat.cast_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' hm') h2
  obtain ⟨hfin, haut, -⟩ := hL Ω l ι c N e ψ hd.e_pos hd.N_even (UnitaryThreeInertia.eta4 Ω) σ g₁ B (l * N) dvd_rfl hram L Φ C₀ k hB ok big sc
  haveI : IsAlgClosure L Ω := Th.Db.algClo L Ω
  have hLk : LinkHyp c N e (UnitaryThreeInertia.eta4 Ω) σ B (l * N) := ⟨hd.e_pos, dvd_rfl, mul_ne_zero hl.out.ne_zero (NeZero.ne N), hram, hB, hσ⟩
  have hker : ∀ [Algebra K Ω], Base.galOf ℚ K Ω = (UnitaryThreeInertia.eta4 Ω).ker := by
    intro _
    rw [← Base.range_galEmb]
    exact (UnitaryThreeInertia.gaussian_field_range_eq_ker_quartic_char.2 Ω K hK).1
  exact ⟨g₁, marks_of_link k ok (dvd_mul_right l N) hsq hΨ, finEnd_of_finPt k ok (dvd_mul_right l N) hsq hfin,
    _root_.UpperTheory.V.Z.Win.Dn.autEnd3_alt hD k ok (dvd_mul_right l N) hσ ι K hker (fun A _ _ r hr hi _ _ _ ρ hρ => by
    haveI : IsAlgClosure K Ω := Th.Db.algClo K Ω
    have t := h3 Ω l c N e ψ _ _ g₁ B _ hLk L Φ C₀ k ok A r hr K hker.symm ρ hρ
    exact ⟨t.1, t.2, hK3 Ω l c N e ψ hd.N_even _ _ g₁ B _ hLk L Φ C₀ k ok big sc A r hr hi K hker.symm ρ hρ⟩) haut⟩
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DnDown
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.GalN.V UpperTheory.V.Af
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.Base
open UpperTheory.V.Z.Win in
theorem UpperTheory.V.Z.Win.Dn.downCsdK_of_printsH :
    _root_.UpperTheory.V.Af.HypothesesH' → _root_.UpperTheory.V.Z.Win.Dn.DownCsdKAlt := by
  intro hP K L Ω _ _ _ _ _ _ _ _ _ _ _ _ _ _ hsol l _ ι n hn r σ hσ hr hpair hirr hI hF hKp haut
  obtain ⟨P, hPr⟩ := hpair
  obtain ⟨j, hj⟩ := hσ
  have algClosure (F : Type) [Field F] [CharZero F] [Algebra F Ω] : IsAlgClosure F Ω :=
    ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) F⟩
  have : IsAlgClosure K Ω := algClosure K
  have : IsAlgClosure L Ω := algClosure L
  have : IsAlgClosure (maximalRealSubfield K) Ω := algClosure (maximalRealSubfield K)
  let c : G (maximalRealSubfield K) Ω := AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) fun x => by
    apply j.injective
    refine (hj _).trans ?_
    exact (mem_maximalRealSubfield_iff x.1).1 x.2 (j.comp (algebraMap K Ω))
  have hc : IsConjEl c := ⟨j, hj⟩
  have hpc : IsPairing c r (cycBar K Ω l ^ (1 - (n : ℤ))) P := fun s s' hs =>
    hPr s s' (AlgEquiv.ext fun x => DFunLike.congr_fun hs x)
  have halg : IsAlgChar ι (cycBar (maximalRealSubfield K) Ω l ^ (1 - (n : ℤ))) := by
    have hcont : Continuous (cycBar (maximalRealSubfield K) Ω l) :=
      _root_.UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.cyc_cont _ Ω l
    refine (_root_.UpperTheory.V.Af.algOfCyc_s hP (maximalRealSubfield K) Ω l ι).1 _ (hcont.zpow _) fun w _ => ?_
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    refine ⟨A, hA, 1 - (n : ℤ), 1, one_pos, fun s _ => ?_⟩
    rw [pow_one, MonoidHom.zpow_apply, zpow_neg, mul_inv_cancel]
  have hconj (a b : G (maximalRealSubfield K) Ω) (ha : IsConjEl a) (hb : IsConjEl b) :
      (cycBar (maximalRealSubfield K) Ω l ^ (1 - (n : ℤ))) a =
        (cycBar (maximalRealSubfield K) Ω l ^ (1 - (n : ℤ))) b := by
    have ha' : cycZ (maximalRealSubfield K) Ω l a = -1 :=
      UpperTheory.V.IsConjOm.cyc (E := maximalRealSubfield K) (σ := a.toRingEquiv) ha
    have hb' : cycZ (maximalRealSubfield K) Ω l b = -1 :=
      UpperTheory.V.IsConjOm.cyc (E := maximalRealSubfield K) (σ := b.toRingEquiv) hb
    simp only [MonoidHom.zpow_apply, cycBar, MonoidHom.comp_apply, ha', hb']
  have hN := _root_.UpperTheory.GalN.V.csdN'_alt hP.toClassicalTheorems hn haut
  have hpol : Sol.Pol ι r := ⟨maximalRealSubfield K, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, _, c, P, halg, hconj, hc, hpc⟩
  suffices h0 : AutCsd0 ι r from _root_.UpperTheory.GalN.V.mkCsd'_alt h0 fun hc' => _root_.UpperTheory.V.Z.Win.Dn.down'_alt L hP hsol hn hc' hirr hpol h0.c0 hF hI hKp
    (hN.2 (hc'.comp (continuous_restrictScalarsHom K L Ω)))
  refine _root_.UpperTheory.GalN.V.csdOf0_alt hP (maximalRealSubfield K) K Ω inferInstance l ι n hn r c P hc ?_ hpc
  refine (_root_.UpperTheory.V.Af.solvable_descent_of_printed_hida hP (maximalRealSubfield K) K L Ω hsol ⟨inferInstance, Or.inr ⟨?_, inferInstance⟩⟩ (Or.inr inferInstance)
    l ι n hn r (cycBar (maximalRealSubfield K) Ω l ^ (1 - (n : ℤ))) hr hirr halg hconj ⟨c, P, hc, hpc⟩).2
    ((_root_.UpperTheory.GalN.V.automorphy_bridge_of_printed_hida hP L Ω l ι n _).2.2 haut)
  exact Algebra.IsQuadraticExtension.finrank_eq_two _ _
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.GalRepDescentAlongQuadraticExtension
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.RankTwoDescentSplit
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ExistsResidualRepQuadratic
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc UpperTheory.V.Af.Sol
namespace UpperTheory.V.Z.Bc
theorem exists_residual_rep_quadratic_alt (P : _root_.UpperTheory.V.Af.HypothesesH') : ExRTwo := fun F Ω _ _ _ _ _ _ l _ ι π χ h1 h2 =>
  let ⟨r, _, _, H, h, _⟩ := _root_.UpperTheory.Gal.SV.exRS_alt P.toClassicalTheorems F Ω l ι 2 one_le_two π χ h1 h2
  ⟨r, H.cont, h⟩
end UpperTheory.V.Z.Bc
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DownQuadS
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PolGL2
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField Matrix Neutral.B1 GlobalTheory.CuspRep Formalism.L2.Host
namespace UpperTheory.V.Sd.Wc
private def wGL (R : Type) [CommRing R] : GL (Fin 2) R :=
  ⟨!![0, 1; -1, 0], !![0, -1; 1, 0], by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩
private theorem map_wGL {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) :
    GeneralLinearGroup.map f (wGL R) = wGL S := by
  ext i j
  change f ((!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) R) i j) = (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) S) i j
  fin_cases i <;> fin_cases j <;> simp
private theorem invT_eq {R : Type} [CommRing R] (g : GL (Fin 2) R) :
    invT 2 R g = GeneralLinearGroup.scalar (Fin 2) (GeneralLinearGroup.det g)⁻¹ * (wGL R * (g * (wGL R)⁻¹)) := by
  rw [map_inv, eq_inv_mul_iff_mul_eq, ← eq_mul_inv_iff_mul_eq]
  apply Units.ext
  change Matrix.scalar (Fin 2) g.val.det = !![0, 1; -1, 0] * (g.val * !![0, -1; 1, 0]) * g.valᵀ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.det_fin_two, Fin.sum_univ_two] <;> ring
private theorem rt_w_mem {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (π : TR.CuspSub F 2)
    {φ : TR.Sm F 2} (hφ : φ ∈ π.V) : TR.rt F 2 (wGL (Ad F))⁻¹ φ ∈ π.V := by
  let k : TR.Kinf F 2 := ⟨!![0, -1; 1, 0], by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j : 1
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩
  have hk : Unitary.toUnits k = (wGL (TR.Rinf F))⁻¹ := Units.ext rfl
  rw [← TR.infGL_mul_finGL (wGL (Ad F))⁻¹, map_inv, map_wGL, ← hk, map_mul]
  exact π.stable (.cpt k) _ (π.stable (.fin _) _ hφ)
end UpperTheory.V.Sd.Wc
open UpperTheory.V UpperTheory.V.Sd.Wc in
theorem UpperTheory.V.Sd.Wc.polGL2_alt :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Sd.Wc.PolGL2 := by
  intro P F _ _ _ π ω h
  obtain ⟨B, hl, hr, hf, hc, hX⟩ := P.gkR F 2 π
  refine TR.CuspSub.isSelfDualBy_of_iso B hl hr hf hc hX ?_
  have hle : (π.dual.twist ω).V ≤ π.V := by
    rintro _ ⟨_, ⟨φ, hφ, rfl⟩, rfl⟩
    convert rt_w_mem π hφ using 1
    refine Subtype.ext (funext fun g => ?_)
    change φ.1 (invT 2 (Ad F) g) * ((ω.1 (GeneralLinearGroup.det g) : ℂˣ) : ℂ) = φ.1 (g * (wGL (Ad F))⁻¹)
    have e : wGL (Ad F) = ratGL F 2 (wGL F) := (map_wGL _).symm
    rw [invT_eq, h _ φ hφ, map_inv, mul_right_comm, Units.inv_mul, one_mul]
    conv_lhs => rw [e]
    rw [(π.cusp φ hφ).1.left, ← e]
  have e : π.dual.twist ω = π :=
    TR.CuspSub.ext ((π.irred _ hle (π.dual.twist ω).stable).resolve_left (π.dual.twist ω).ne_bot)
  rw [e]
  exact TR.CuspSub.Iso.refl π
end
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc UpperTheory.V.Af.Sol UpperTheory.V.Z.Bc
private theorem cusp_unique {F : Type} [Field F] [NumberField F] {n : ℕ} {sat : HeightOneSpectrum (𝓞 F) → Multiset ℂˣ → Prop}
    {inf : (F →+* ℂ) → Multiset ℂ → Prop} (h : IsCusp n sat inf) : ∀ v B B', sat v B → sat v B' → B = B' := by
  rcases h with ⟨_, π, rfl, -⟩ | ⟨_, π, rfl, -⟩
  · exact fun _ _ _ h h' => h.unique h'
  · exact fun _ _ _ h h' => h.unique h'
private theorem not_both (F : Type) [Field F] [NumberField F] (h : IsTotallyReal F) (h' : IsTotallyComplex F) : False := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact (InfinitePlace.not_isReal_iff_isComplex.2 (h'.isComplex v)) (h.isReal v)
private theorem contCoeff {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (n i : ℕ) :
    Continuous fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i := by
  have h : (fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i) =
      fun M => MvPolynomial.eval (fun ij : Fin n × Fin n => M ij.1 ij.2)
        ((Matrix.charpoly.univ K (Fin n)).coeff i) := by
    funext M
    exact (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id K) (fun ij : Fin n × Fin n => M ij.1 ij.2) i).symm
  rw [h]
  exact (MvPolynomial.continuous_eval _).comp
    (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))
private theorem normV_under {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (w : HeightOneSpectrum (𝓞 K')) : normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  simp only [normV, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 K') w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]
private theorem isoOfFrobOne (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ) (r r' : G F Ω →* GL (Fin n) (Qbar l)) (hr : Continuous r)
    (hr' : Continuous r') (hs : IsSSRep r) (hs' : IsSSRep r')
    (hw : ∀ᶠ w : HeightOneSpectrum (𝓞 F) in Filter.cofinite, w.asIdeal.inertiaDeg ℤ = 1 →
      ∃ B, FrobEig ι r w B ∧ FrobEig ι r' w B) : RepIso r r' := by
  have hD := GlobalTheory.Published.ChebotarevDegreeOne.dense (F := F) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne'
    (Filter.eventually_cofinite.1 hw)
  have hc : ∀ g : G F Ω, (r g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly =
      (r' g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly := by
    intro g
    ext i
    have h1 : Continuous fun g : G F Ω => (r g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i :=
      (contCoeff n i).comp (Units.continuous_val.comp (hr.comp continuous_inv))
    have h2 : Continuous fun g : G F Ω => (r' g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i :=
      (contCoeff n i).comp (Units.continuous_val.comp (hr'.comp continuous_inv))
    refine congrFun (Continuous.ext_on hD h1 h2 ?_) g
    rintro σ ⟨v, hv, hd, A, hA, hσ⟩
    obtain ⟨B, hB, hB'⟩ := not_not.1 hv hd
    have h := ((hB A hA).2 σ hσ).trans ((hB' A hA).2 σ hσ).symm
    have h' := Polynomial.map_injective ι.toRingHom ι.injective h
    simp only [h']
  obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix r r' hs hs' (fun g => by simpa using hc g⁻¹)
  exact ⟨P⁻¹, fun s => by rw [hP s, inv_inv]⟩
private theorem normV_one {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (w : HeightOneSpectrum (𝓞 K')) (h : w.asIdeal.inertiaDeg ℤ = 1) : normV w = normV (w.under (𝓞 K)) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  rw [Ideal.inertiaDeg_tower (R := ℤ) (w.under (𝓞 K)).asIdeal w.asIdeal] at h
  rw [normV_under (K := K) w, Nat.eq_one_of_mul_eq_one_left h, pow_one]
theorem UpperTheory.V.Z.Bc.automorphic_rank_two_of_automorphic_restrict_of_finite_det :
    ∀ (H : _root_.UpperTheory.V.Af.HypothesesH') (cyc : DescS) (hG : GapTwo) (hR : ExRTwo) (M Ω : Type) [Field M] [NumberField M] [Field Ω] [Algebra ℚ Ω]
      [Algebra M Ω] [IsScalarTower ℚ M Ω] [IsAlgClosure ℚ Ω] [IsAlgClosure M Ω] (hp : Module.finrank ℚ M = 2) (hM : IsCMField M)
      (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (r : G ℚ Ω →* GL (Fin 2) (Qbar l)) (hr : Continuous r)
      (hirr : IsIrr (r.comp (resG ℚ M Ω))) (hfin : ∃ N : ℕ, 0 < N ∧ ∀ s, Matrix.GeneralLinearGroup.det (r s) ^ N = 1), IsAut ι (r.comp (resG ℚ M Ω)) → IsAut ι r := by
  intro H cyc hG hR M Ω _ _ _ _ _ _ _ _ hp hM l _ ι r hr hirr hfin
  haveI : Algebra.IsQuadraticExtension ℚ M := ⟨hp⟩
  have hK : IsTotallyReal ℚ := inferInstance
  have hdown := cyc M hp inferInstance
  have hss : IsSSRep (r.comp (resG ℚ M Ω)) := (Bc.irrBasic.1 _ Unit _ 2 _).2.1 hirr
  have hirr' : IsIrr r := (Bc.irrBasic.1 _ _ _ 2 r).1 _ hirr
  have hcont := continuous_restrictScalarsHom ℚ M Ω
  rintro ⟨sat', inf', hc', hreg', hatt'⟩
  have hgap : Gap2 inf' := by
    rcases hc' with ⟨_, P, rfl, rfl⟩ | ⟨hR', -⟩
    · refine hG M Ω l ι _ P ((GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => ?_) hatt' (hfin.imp fun N h => ⟨h.1, fun s => h.2 _⟩)
      obtain ⟨m, hm, h⟩ := hreg' τ
      rw [CG.HasInfChar.infChar_eq (π := CG.mk P) hm]
      exact h
    · exact (not_both M hR' inferInstance).elim
  obtain ⟨sat, inf, hc, hbc, hinf⟩ := hdown sat' inf' hc' hreg' hgap (UpperTheory.satake_invariant_of_frobConj_of_eigenvalue_basic UpperTheory.frobenius_conj_of_galois_conjugate_places UpperTheory.hecke_eigenvalue_basic_properties ℚ M Ω l ι 2 r sat' hatt')
  have hreg : RegInf 2 inf := fun τ => by
    obtain ⟨m, hm, h⟩ := hreg' (ComplexEmbedding.lift M τ)
    have := hinf _ m hm
    rw [ComplexEmbedding.lift_comp_algebraMap] at this
    exact ⟨m, this, h⟩
  obtain ⟨r₁, hr₁, hatt₁⟩ := (show ∃ r₁ : G ℚ Ω →* GL (Fin 2) (Qbar l), Continuous r₁ ∧ AttachedSys ι r₁ sat by
    rcases hc with ⟨hC, -⟩ | ⟨hR', π, rfl, rfl⟩
    · exact (not_both ℚ hK hC).elim
    · obtain ⟨ω, hω, -⟩ := _root_.UpperTheory.V.Sd.Wc.centChar_alt H.toClassicalTheorems ℚ π
      refine hR ℚ Ω l ι π ω (fun v => ?_) ⟨fun v v' => by rw [Subsingleton.elim v v'], _root_.UpperTheory.V.Sd.Wc.polGL2_alt H.toClassicalTheorems ℚ π ω hω⟩
      have := hreg v.embedding
      simpa only [InfinitePlace.mk_embedding] using this)
  have hN := (UpperTheory.galois_representation_image_spec ℚ M Ω).1
  have hss₁ := UpperTheory.semisimpleModule_restriction_to_normal_subgroup _ _ _ 2 r₁ (resG ℚ M Ω) hN hatt₁.1
  have hiso : RepIso (r₁.comp (resG ℚ M Ω)) (r.comp (resG ℚ M Ω)) := by
    refine isoOfFrobOne M Ω l ι 2 _ _ (hr₁.comp hcont) (hr.comp hcont) hss₁ hss ?_
    filter_upwards [hbc, (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under ℚ M).eventually hatt₁.2, hatt'.2]
      with w h1 ⟨B₁, hB₁, h₁⟩ ⟨B', hB', h'⟩ hd
    have hn := normV_one (K := ℚ) w hd
    obtain ⟨B, hB, hP⟩ := h1 hn
    obtain rfl := cusp_unique hc _ _ _ hB hB₁
    obtain rfl := cusp_unique hc' _ _ _ hP hB'
    have h3 := (UpperTheory.frobenius_power_compatibility ℚ M Ω l ι w 1 (by rw [pow_one]; exact hn)).1 2 r₁ _ h₁
    simp only [pow_one, Multiset.map_id'] at h3
    rw [← hn] at h3
    exact ⟨_, h3, h'⟩
  obtain ⟨δ, hδ, hiso'⟩ := UpperTheory.schur_extension _ _ _ 2 r r₁ (resG ℚ M Ω) hN hirr hiso
  have hF := UpperTheory.finiteCharacter_of_algebraic_cyclotomic (_root_.UpperTheory.V.Af.algOfCyc_s H)
  obtain ⟨sat₂, inf₂, hc₂, hreg₂, hatt₂⟩ := _root_.UpperTheory.V.Af.twist_invariance_automorphic H ℚ Ω l ι 2 r₁ δ ⟨sat, inf, hc, hreg, hatt₁⟩
    (hF.1 ℚ Ω l ι δ (hF.2 ℚ M Ω l δ hδ))
  exact ⟨sat₂, inf₂, hc₂, hreg₂, (Bc.irrBasic.1 _ Unit _ 2 _).2.1 hirr',
    hatt₂.2.mono fun w ⟨B, hB, h⟩ => ⟨B, hB, h.of_iso hiso'⟩⟩
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.Base UpperTheory.V.Af
open scoped Matrix
private theorem cc_ex (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] : ∃ c : G ℚ Ω, IsConjEl c := by
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  let j : Ω →ₐ[ℚ] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  letI : Algebra Ω ℂ := j.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ Ω ℂ := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  let τ : ℂ ≃ₐ[ℚ] ℂ := AlgEquiv.ofRingEquiv (f := starRingAut) fun x => by simp
  exact ⟨τ.restrictNormal Ω, algebraMap Ω ℂ, fun x => AlgEquiv.restrictNormal_commutes τ Ω x⟩
private theorem cc_mu {Ω : Type} [Field Ω] [CharZero Ω] {c : G ℚ Ω} (hc : IsConjEl c) {M : ℕ} (hM : 1 ≤ M) {ζ : Ω}
    (h : ζ ^ M = 1) : c ζ = ζ⁻¹ := by
  obtain ⟨j, hj⟩ := hc
  apply j.injective
  have h1 : (j ζ) ^ M = 1 := by rw [← map_pow, h, map_one]
  rw [hj, map_inv₀, Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one h1 (by omega))]
private theorem kills_cc {Ω : Type} [Field Ω] [CharZero Ω] {C : Type} [CommGroup C] {M : ℕ} (hM : 1 ≤ M) {χ : G ℚ Ω →* C}
    (hχ : KillsMu M χ) {c c' : G ℚ Ω} (hc : IsConjEl c) (hc' : IsConjEl c') : χ c = χ c' := by
  have := hχ (c⁻¹ * c') fun ζ h => by
    rw [AlgEquiv.mul_apply, cc_mu hc' hM h, ← cc_mu hc hM h]
    exact c.symm_apply_apply ζ
  rw [map_mul, map_inv, inv_mul_eq_one] at this
  exact this
private theorem kills_pow {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {C : Type} [CommGroup C] {M : ℕ} (hM : 1 ≤ M)
    {χ : G ℚ Ω →* C} (hχ : KillsMu M χ) : ∃ k : ℕ, 0 < k ∧ ∀ s, χ s ^ k = 1 := by
  haveI : NeZero M := ⟨by omega⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨μ, hμ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω M
  refine ⟨Fintype.card (ZMod M)ˣ, Fintype.card_pos, fun s => ?_⟩
  rw [← map_pow]
  refine hχ _ fun ζ h => ?_
  have h1 := hμ.autToPow_spec ℚ (s ^ Fintype.card (ZMod M)ˣ)
  rw [map_pow, pow_card_eq_one, Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod _ hμ.pow_eq_one, pow_one] at h1
  obtain ⟨i, -, rfl⟩ := hμ.eq_pow_of_pow_eq_one h
  rw [map_pow, ← h1]
private theorem pair2 {k : Type} [Field k] (A : Matrix (Fin 2) (Fin 2) k) :
    Aᵀ * !![0, 1; -1, 0] * A = A.det • (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) k) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.det_fin_two] <;> ring
private theorem pairing2 {F Ω k : Type} [Field F] [Field Ω] [Algebra F Ω] [Field k] (r : G F Ω →* GL (Fin 2) k) (c : G F Ω) :
    ∃ P, IsPairing c r ((Matrix.GeneralLinearGroup.det.comp r).comp (resG F F Ω)) P := by
  let J : GL (Fin 2) k := Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; -1, 0] (by simp [Matrix.det_fin_two])
  refine ⟨J * r c⁻¹, fun s s' h => ?_⟩
  have h' : s' = c * s * c⁻¹ := h
  have e : r c⁻¹ * r s' = r s * r c⁻¹ := by rw [h', ← map_mul, ← map_mul]; congr 1; group
  have e' : (r c⁻¹).val * (r s').val = (r s).val * (r c⁻¹).val := congrArg Units.val e
  have hp : (r s).valᵀ * J.val * (r s).val = (r s).val.det • J.val := pair2 _
  have hd : (((Matrix.GeneralLinearGroup.det.comp r).comp (resG F F Ω) s : kˣ) : k) = (r s).val.det := rfl
  rw [hd, Units.val_mul, ← Matrix.smul_mul, ← hp]
  simp only [Matrix.mul_assoc, e']
private theorem tf (L Ω : Type) [Field L] [Field Ω] [Algebra L Ω] : Module.IsTorsionFree L Ω :=
  DivisionSemiring.to_moduleIsTorsionFree
attribute [local instance] tf
private theorem algClosure_up (L Ω : Type) [Field L] [CharZero L] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra L Ω] :
    IsAlgClosure L Ω :=
  ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) L⟩
open UpperTheory.V UpperTheory.V.Af in
private theorem via (P : _root_.UpperTheory.V.Af.HypothesesH') (cyc : Z.Bc.CycC) (cyc2 : Z.Bc.DescS) (hG : Z.Bc.GapTwo) (K L Ω : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsAbelianGalois ℚ L]
    (hK : Module.finrank ℚ K = 2) (hC : IsCMField K) (hL : IsCMField L) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (W : G ℚ Ω →* GL (Fin 2) (Qbar l)) (hW : Continuous W) (hirr : IsIrr (W.comp (resG ℚ L Ω))) (hpol : Sol.Pol ι W)
    (hfin : ∃ N : ℕ, 0 < N ∧ ∀ s, Matrix.GeneralLinearGroup.det (W s) ^ N = 1)
    (haut : IsAut ι (W.comp (resG ℚ L Ω))) : IsAut ι W := by
  haveI : IsAlgClosure K Ω := algClosure_up K Ω
  haveI : IsAlgClosure L Ω := algClosure_up L Ω
  haveI a : IsAbelianGalois K L := IsAbelianGalois.tower_top ℚ K L
  have e : (W.comp (resG ℚ K Ω)).comp (resG K L Ω) = W.comp (resG ℚ L Ω) := MonoidHom.ext fun _ => rfl
  rw [← e] at hirr haut
  have h1 := (_root_.UpperTheory.V.Z.Bc.solC_alt P cyc K L Ω (isSolvable_of_comm a.is_comm.comm) hC hL l ι 2 one_le_two (W.comp (resG ℚ K Ω))
    (hW.comp (continuous_restrictScalarsHom ℚ K Ω)) hirr (UpperTheory.solvable_polarized_restriction ℚ K Ω l ι 2 W hpol)).2 haut
  exact _root_.UpperTheory.V.Z.Bc.automorphic_rank_two_of_automorphic_restrict_of_finite_det P cyc2 hG (_root_.UpperTheory.V.Z.Bc.exists_residual_rep_quadratic_alt P) K Ω hK hC l ι W hW ((UpperTheory.galoisRep_irreducibility_criterion.1 _ _ _ 2 _).1 _ hirr) hfin h1
open UpperTheory.V UpperTheory.V.Af in
theorem UpperTheory.V.Z.Bc.isAutR_of_isAutC_comp_galEmb_of_odd_quadratic_char (P : _root_.UpperTheory.V.Af.HypothesesH') (cyc : Z.Bc.CycC) (cyc2 : Z.Bc.DescS) (hG : Z.Bc.GapTwo) :
  ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [IsAbelianGalois ℚ L] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
    [Algebra L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (W : G ℚ Ω →* GL (Fin 2) (Qbar l)), Continuous W →
    IsCycWt l 0 (Matrix.GeneralLinearGroup.det.comp W) → IsIrr (W.comp (galEmb ℚ L Ω)) →
    (∃ (η : G ℚ Ω →* ℤˣ) (σ : G ℚ Ω), Sd.IsCC σ ∧ η σ = -1 ∧ ∀ s : G L Ω, η (galEmb ℚ L Ω s) = 1) →
    Sd.IsAutC ι (W.comp (galEmb ℚ L Ω)) → IsAutR ι W := by
  intro L Ω _ _ _ _ _ _ _ _ l _ ι W hW hdet hirr ⟨η, σ, hσ, hησ, hηL⟩ haut
  haveI : IsAlgClosure L Ω := algClosure_up L Ω
  obtain ⟨M, χ, hM, hχ, hθ⟩ := hdet
  rw [zpow_zero, one_mul] at hθ
  have hcont : Continuous (Matrix.GeneralLinearGroup.det.comp W) :=
    Matrix.GeneralLinearGroup.continuous_det.comp hW
  obtain ⟨k, hk, hpow⟩ := kills_pow hM hχ
  have halg : IsAlgChar ι (Matrix.GeneralLinearGroup.det.comp W) := by
    refine (_root_.UpperTheory.V.Af.algOfCyc_s P ℚ Ω l ι).1 _ hcont fun w _ => ?_
    obtain ⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w := exists_isPlaceOver Ω w
    exact ⟨A, hA, 0, k, hk, fun s _ => by rw [neg_zero, zpow_zero, mul_one, hθ, hpow]⟩
  obtain ⟨c, hc⟩ := cc_ex Ω
  obtain ⟨Q, hQ⟩ := pairing2 W c
  have hfin : ∃ N : ℕ, 0 < N ∧ ∀ s, Matrix.GeneralLinearGroup.det (W s) ^ N = 1 :=
    ⟨k, hk, fun s => by
      have e : Matrix.GeneralLinearGroup.det (W s) = χ s := DFunLike.congr_fun hθ s
      rw [e, hpow]⟩
  obtain ⟨K, hK, hC⟩ := Z.Bc.exists_quad L Ω η σ hσ hησ hηL
  have hpol : Sol.Pol ι W := ⟨ℚ, _, _, _, _, inferInstance, inferInstance, inferInstance, _, c, Q, halg,
    fun c c' h h' => by rw [hθ]; exact kills_cc hM hχ h h', hc, hQ⟩
  exact (_root_.UpperTheory.GalN.V.automorphy_bridge_of_printed_hida P ℚ Ω l ι 2 W).1.1 (via P cyc cyc2 hG K L Ω hK hC inferInstance l ι W hW hirr hpol hfin ((_root_.UpperTheory.GalN.V.automorphy_bridge_of_printed_hida P L Ω l ι 2 _).2.1.2 haut))
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TGapTwo
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Z.Bc
section SlopeTestRemainingChoices
variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
private theorem lie_central {π : CuspSub E a} {ω : HChar E} (hω : π.HasCentral ω) (z : Cinf E) {ψ : Sm E a} (hψ : ψ ∈ π.V) :
    ∑ i, lieS E a i i z ψ = dchi ω z • ψ := by
  have e2 : lie E a (Central.scL a z) = ∑ i, lieS E a i i z := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [lieS_apply, ← map_sum]
    exact congrArg (lie E a) (Matrix.sum_single_eq_diagonal (fun _ : Fin a => z)).symm
  rw [← LinearMap.sum_apply, ← e2]
  refine Subtype.ext (funext fun g => ?_)
  have h1 := Central.hasDerivAt_scalar z ψ g
  have h2 : (fun t : ℝ => ψ.1 (g * Matrix.GeneralLinearGroup.scalar (Fin a) (infId E (expU (t • z))))) =
      fun t : ℝ => Complex.exp (t * dchi ω z) * ψ.1 g := by
    funext t
    have h3 := congrFun (congrArg Subtype.val (hω (infId E (expU (t • z))) ψ hψ)) g
    have h4 := chiInf_expU ω (t • z)
    rw [map_smul, Complex.real_smul] at h4
    rw [← h4]
    exact h3
  rw [h2] at h1
  have h5 := (((Complex.ofRealCLM.hasDerivAt (x := 0)).mul_const (dchi ω z)).cexp).mul_const (ψ.1 g)
  have h6 := h1.unique h5
  change lieD _ ψ.1 g = dchi ω z * ψ.1 g
  rw [h6]
  simp
private theorem expo_central {π : CuspSub E a} {ω : HChar E} (hω : π.HasCentral ω) {τ : E →+* ℂ} {m : Multiset ℂ}
    (hm : π.HasInfChar τ m) : expo ω τ = m.sum := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  refine smul_left_injective ℂ h0 ?_
  beta_reduce
  rw [← GlobalTheory.trace_Eop_of_hasInfChar E a π τ m hm φ hφ]
  have h1 := lie_central hω (atEmb τ 1) hφ
  have h2 := lie_central hω (atEmb τ Complex.I) hφ
  simp only [Eop, expo, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.sub_apply, ← Finset.smul_sum, Finset.sum_sub_distrib, h1, h2]
  module
private theorem det_algSat (M : Matrix (Fin 2) (Fin 2) ℂ) (q : ℕ) (x y : ℂˣ)
    (h : M.charpoly = ((algSat 2 q {x, y}).map fun b => X - C b).prod) : M.det = (q : ℂ) * ((x * y : ℂˣ) : ℂ) := by
  have hq : ((q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2)) * ((q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2)) = q := by
    rw [← Real.rpow_add' (Nat.cast_nonneg q) (by norm_num)]
    norm_num
  have hq' := congrArg (fun x : ℝ => (x : ℂ)) hq
  simp only [Complex.ofReal_mul, Complex.ofReal_natCast] at hq'
  have e : algSat 2 q {x, y} = {(((q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2) : ℝ) : ℂ) * x,
      (((q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2) : ℝ) : ℂ) * y} := by
    simp [algSat]
  rw [Matrix.det_eq_prod_roots_charpoly, h, roots_multiset_prod_X_sub_C, e, Multiset.prod_pair, mul_mul_mul_comm, hq',
    Units.val_mul]
private theorem gap_of_sum {x y : ℂ} (hne : x ≠ y) {i j : ℤ} (hi : x = i + 1 / 2) (hj : y = j + 1 / 2) (hs : x + y = 1) :
    ∃ (c : ℂ) (k : ℕ), 2 ≤ k ∧ ({x, y} : Multiset ℂ) = {c, c + k} := by
  have h0 : i + j = 0 := by
    have : ((i + j : ℤ) : ℂ) = 0 := by push_cast; linear_combination hs - hi - hj
    exact_mod_cast this
  have h1 : i ≠ j := fun e => hne (by rw [hi, hj, e])
  rcases lt_or_gt_of_ne h1 with h | h
  · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 h.le)
    refine ⟨x, k, by omega, ?_⟩
    have : ((j - i : ℤ) : ℂ) = k := by rw [hk]; simp
    push_cast at this
    rw [show x + k = y by linear_combination hi - hj - this]
  · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 h.le)
    refine ⟨y, k, by omega, ?_⟩
    have : ((i - j : ℤ) : ℂ) = k := by rw [hk]; simp
    push_cast at this
    rw [show y + k = x by linear_combination hj - hi - this, Multiset.pair_comm]
end SlopeTestRemainingChoices
theorem UpperTheory.V.Z.Bc.gapTwo_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Z.Bc.GapTwo := by
  intro _ F Ω _ _ _ _ _ _ l _ ι r P hreg hatt ⟨N, hN, hdet⟩ τ
  obtain ⟨ω, hω⟩ := Central.exists_hasCentral F 2 P
  have hone : (ω * GlobalTheory.HeckeGal.Model.absPow F (-1)) ^ N = 1 := by
    refine PositivityTheory.jumpWindows.FiniteInfinitePlaceProduct.eq_one _ ?_
    filter_upwards [hatt.2] with w ⟨B, hB, hF⟩
    obtain ⟨x, y, rfl⟩ := Multiset.card_eq_two.1 hB.card
    have h1 := PositivityTheory.jumpWindows.PSmo.val_eq_prod (CuspSub.hasCentral_iff.1 hω) hB
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    obtain ⟨σ, hσ⟩ := ReciprocityTheory.Gal.exists_isFrob hA
    have e2 := (hF A hA).2 σ hσ
    rw [← Matrix.charpoly_map] at e2
    have e3 := det_algSat _ _ _ _ e2
    have e4 : ι (r σ⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).det =
        ((r σ⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).map ι.toRingHom).det := ι.toRingHom.map_det _
    have e5 := congrArg (fun u : (Qbar l)ˣ => ι (u : Qbar l)) (hdet σ⁻¹)
    simp only [Units.val_pow_eq_pow_val, map_pow, Units.val_one, map_one, Matrix.GeneralLinearGroup.val_det_apply] at e5
    rw [e4, e3] at e5
    have e6 := (GlobalTheory.HeckeGal.Model.absPow_isAbsPow F (-1)).2.1 w
    refine Units.ext ?_
    have hp : ∀ ν : HChar F, (ν ^ N).val w = ν.val w ^ N := fun ν => MonoidHom.pow_apply ν.1 N _
    rw [hp, HChar.val_mul, Units.val_pow_eq_pow_val, Units.val_mul, e6, h1, Multiset.prod_pair, Units.val_one, ← e5, mul_comm]
    simp [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hsum : ((CG.mk P).infChar τ).sum = 1 := by
    have h1 := GlobalTheory.BCT.TwistDisc.expo_pow (ω * GlobalTheory.HeckeGal.Model.absPow F (-1)) N τ
    have h2 := GlobalTheory.BCT.TwistDisc.expo_pow (1 : HChar F) 0 τ
    rw [pow_zero, Nat.cast_zero, zero_mul] at h2
    have h3 := (CG.hasInfChar_ofChar ω τ).twist (GlobalTheory.HeckeGal.Model.absPow F (-1))
    rw [CG.twist_ofChar, Multiset.map_singleton] at h3
    have h4 := h3.infChar_eq
    rw [CG.infChar_ofChar, Multiset.singleton_inj] at h4
    have h5 : expo (GlobalTheory.HeckeGal.Model.absPow F (-1)) τ = ((-1 : ℝ) : ℂ) := GlobalTheory.CuspRep.Model.expo_absC _ τ
    rw [hone, h2, h4, h5, expo_central hω (ParLaws.hasInfChar_infChar (CG.mk P) τ)] at h1
    have h6 := (mul_eq_zero.1 h1.symm).resolve_left (Nat.cast_ne_zero.2 hN.ne')
    push_cast at h6
    linear_combination h6
  have hm : P.HasInfChar τ ((CG.mk P).infChar τ) := ParLaws.hasInfChar_infChar (CG.mk P) τ
  obtain ⟨hnd, hint⟩ := hreg τ
  obtain ⟨x, y, e⟩ := Multiset.card_eq_two.1 (CG.card_infChar (CG.mk P) τ)
  rw [e] at hm hnd hint hsum
  obtain ⟨i, hi⟩ := hint x (by simp)
  obtain ⟨j, hj⟩ := hint y (by simp)
  obtain ⟨c, k, hk, e'⟩ := gap_of_sum (x := x) (y := y) (by simpa using hnd) (i := i) (j := j) (by rw [hi]; norm_num)
    (by rw [hj]; norm_num) (by simpa using hsum)
  exact ⟨c, k, hk, e' ▸ hm⟩
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
theorem UpperTheory.V.Af.rankTwoAutomorphyDescends_of_printsH :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Pr.RankTwoAutomorphyDescendsFromAbelianCMToRat := fun P =>
  Or.elim P.cyc2 (fun h => _root_.UpperTheory.V.Z.Bc.isAutR_of_isAutC_comp_galEmb_of_odd_quadratic_char P P.cyc h (_root_.UpperTheory.V.Z.Bc.gapTwo_alt P))
    fun h L Ω _ _ _ _ _ _ _ _ l _ ι W h1 h2 h3 h4 h5 => h L Ω l ι W h1 h2 h3 h4 h5
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SymmetricCubeTheoremOfEndomorphisms
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr UpperTheory.V
private theorem totDisc_quot {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) :
    TotallyDisconnectedSpace (G ⧸ N) := by
  rw [totallyDisconnectedSpace_iff_connectedComponent_one]
  refine Set.eq_singleton_iff_unique_mem.2 ⟨mem_connectedComponent, fun y hy => ?_⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  by_contra hx
  have hx' : x ∉ N := fun h => hx ((QuotientGroup.eq_one_iff x).2 h)
  have ho : IsOpen {g : G | g * x ∉ N} := hN.isOpen_compl.preimage (continuous_mul_const x)
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one ho (by simpa using hx')
  let V : Subgroup (G ⧸ N) := U.toSubgroup.map (QuotientGroup.mk' N)
  have hVo : IsOpen (V : Set (G ⧸ N)) := QuotientGroup.isOpenMap_coe _ U.isOpen'
  have hV : IsClopen (V : Set (G ⧸ N)) := ⟨V.isClosed_of_isOpen hVo, hVo⟩
  obtain ⟨u, hu, hux⟩ := hV.connectedComponent_subset V.one_mem hy
  exact hU (U.toSubgroup.inv_mem hu) (QuotientGroup.eq.1 hux)
private theorem tw_iso {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r r' : Γ →* GL (Fin n) k} (χ : Γ →* kˣ)
    (h : Af.RepIso r r') : Af.RepIso (Af.tw r χ) (Af.tw r' χ) := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g, fun s => Units.ext ?_⟩
  rw [Units.val_mul, Units.val_mul, Af.tw_val, Af.tw_val, hg, Units.val_mul, Units.val_mul, Matrix.mul_smul,
    Matrix.smul_mul]
private theorem conj_left {G R : Type} [Group G] [CommRing R]
    (r : G →* GG (m := 3) (R := R)) (h : GL (Fin 3) R) (g : G)
    (hg : (r g).right = 1) : (conjBy h r g).left = h * (r g).left * h⁻¹ := by
  have e : conjBy h r g = GG.ofGL h * r g * GG.ofGL h⁻¹ := by
    rw [map_inv]; rfl
  rw [e, SemidirectProduct.mul_left, SemidirectProduct.mul_left, SemidirectProduct.left_inl,
    SemidirectProduct.left_inl, SemidirectProduct.right_inl, sgnAct_one, SemidirectProduct.mul_right,
    SemidirectProduct.right_inl, hg, mul_one, sgnAct_one]
open Matrix in
private theorem matIrr_conj {G R : Type} [Group G] [CommRing R] {m : ℕ} {U : Subgroup G}
    {a a' : G → Matrix (Fin m) (Fin m) R} (h : GL (Fin m) R)
    (e : ∀ g ∈ U, a g = ((h⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) * a' g * h) (H : MatIrr U a) :
    MatIrr U a' :=
  _root_.UpperTheory.Reformulated.B.Qf5.matIrr_conj h e H
private theorem tri_of_char {O G A : Type} [CommRing O] [IsLocalRing O] [Finite (ResidueField O)] [Group G]
    [CommRing A] [IsDomain A] [IsLocalRing A] [Algebra O A] (h2 : IsUnit (2 : O))
    (h0 : ∀ a ∈ maximalIdeal O, algebraMap O A a = 0) {η : G →* ℤˣ} {Ψ : G →* Oˣ} {c g₁ : G} (hM : Marks η Ψ c g₁)
    {r : G →* GG (m := 3) (R := A)} (hr : UnitaryThreeInertia.Red η Ψ r) (hN : Normalised c g₁ r)
    (U : Subgroup G) (hU : U.FiniteIndex)
    (hch : ∀ g ∈ U, η g = 1 → (r g).mat.charpoly = (((r0 η Ψ g).mat).map (algebraMap O A)).charpoly) :
    Upper η r ∨ Lower η r := by
  letI : Algebra (ResidueField O) A := (Ideal.Quotient.lift _ (algebraMap O A) h0).toAlgebra
  let Φ : G →* (ResidueField O)ˣ := (Units.map (residue O).toMonoidHom).comp Ψ
  have e : ∀ g, ((r0 η Φ g).mat).map (algebraMap (ResidueField O) A) = ((r0 η Ψ g).mat).map (algebraMap O A) := by
    intro g
    rw [GG.mat, GG.mat, unitaryThreeReflection_left, unitaryThreeReflection_left, tor_val, tor_val, Matrix.diagonal_map (map_zero _),
      Matrix.diagonal_map (map_zero _)]
    congr 1
    funext i
    rw [show Φ g ^ wt1 i = Units.map (residue O).toMonoidHom (Ψ g ^ wt1 i) from
      (map_zpow (Units.map (residue O).toMonoidHom) (Ψ g) _).symm]
    rfl
  refine (constOfChar G (ResidueField O) A ?_ η Φ c g₁ ⟨hM.csq, hM.ηc, ?_, hM.ηg, ?_⟩ r hr.mult
    (fun g => ?_) hN U hU fun g hg hη => ?_).1
  · simpa [map_ofNat] using (h2.map (residue O)).ne_zero
  · show Units.map _ (Ψ c) = 1
    rw [hM.Ψc, map_one]
  · have := hM.Ψg.map (residue O)
    rwa [map_sub, map_pow, map_one] at this
  · rw [e]; exact hr.red g
  · rw [e]; exact hch g hg hη
attribute [local instance] UpperTheory.V.Alg.IsCO.toIsLocalRing UpperTheory.V.UnitaryThreeInertia.Coef.isLocalRing in
theorem UpperTheory.V.Pr.symmetric_cube_theorem_of_endomorphisms_alt :
    _root_.UpperTheory.V.Pr.HostEndAlt → _root_.UpperTheory.V.Aut.ThmS6Core_s := by
  intro H K _ _ _ hK Ω _ _ _ l _ ι c N _ e ψ o₁ hd S A F hF
  obtain ⟨σ, hσ, hc⟩ := hF.cc
  have hv : (A F.vl).valuation (l : Ω) < 1 := by simpa using (hF.isOver F.vl (l : 𝓞 ℚ)).2 hF.vl
  obtain ⟨g₁, hM, ⟨U, hU, hfin⟩, haut⟩ := H K hK Ω l ι c N e ψ o₁ hd σ hσ (A F.vl) hv
  have hη : ∀ g, F.η (toGS Ω _ g) = UnitaryThreeInertia.eta4 Ω g := fun g => by rw [← hF.η, hF.π]; rfl
  have hΨ : ∀ g, F.Ψ (toGS Ω _ g) = Chr.Psi l e (Chr.dirG ℚ Ω ψ) g := fun g => by rw [← hF.Ψ, hF.π]; rfl
  rw [hF.π] at hc
  have hg : F.Marked (toGS Ω _ g₁) := ⟨(hη g₁).trans hM.ηg, by rw [hΨ]; exact hM.Ψg⟩
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  haveI hcl := isClosed_NS Ω (S : Set UnitaryThreeInertia.Pl)
  haveI : CompactSpace (UnitaryThreeInertia.Gam Ω S) := inferInstance
  haveI : T2Space (UnitaryThreeInertia.Gam Ω S) := inferInstance
  haveI : TotallyDisconnectedSpace (UnitaryThreeInertia.Gam Ω S) := totDisc_quot _ hcl
  have hOk := UnitaryThreeInertia.hostFrame_ok Ω c e ψ o₁ hd S A F hF
  have hsurj : ∀ x : UnitaryThreeInertia.Gam Ω S, ∃ s, toGS Ω _ s = x := fun x => QuotientGroup.mk_surjective x
  refine ⟨_, hg, fun R _ _ _ u hu => ?_⟩
  have hM2 : Module.Finite c.O (UnitaryThreeInertia.wpart c.O u 0) := by
    refine UnitaryThreeInertia.universal_diagonal_of_triangular_points F hOk (UnitaryThreeInertia.frame_class_one Ω c e ψ o₁ hd S A F hF) _ hg u hu fun B _ _ hB h0 r hr => ?_
    haveI := hB.toIsDomain
    haveI := hB.toIsDiscreteValuationRing
    have ho := ordPt_of_isPt Ω c e ψ o₁ hd S A F hF σ g₁ hc r hr
    refine (tri_of_char hOk.two h0 hM ho.red ho.norm U hU (hfin B h0 _ ho)).imp (fun h g hg => ?_) fun h g hg => ?_
    · obtain ⟨s, rfl⟩ := hsurj g
      exact h s ((hη s).symm.trans hg)
    · obtain ⟨s, rfl⟩ := hsurj g
      exact h s ((hη s).symm.trans hg)
  refine ⟨hM2, fun ξ r h1 h2 => ?_⟩
  have hz : F.IsCharZeroPt _ r := UnitaryThreeInertia.isCharZeroPt_of_isPtHom (l := l) F hOk _ hg u hu hM2 ξ r h1
  have hirr := UnitaryThreeInertia.matIrr_open Ω c e ψ o₁ hd S A F hF _ hg r hz h2
  obtain ⟨B, _, _, t, r', hr', ht⟩ := hz
  have ho := ordPt_of_isPt Ω c e ψ o₁ hd S A F hF σ g₁ hc r' hr'
  have hm : ∀ s, (r (toGS Ω _ s)).right = UnitaryThreeInertia.eta4 Ω s := fun s =>
    ((h1 _).1.trans (hu.pt.mult _)).trans (hη s)
  have hl : ∀ s ∈ (UnitaryThreeInertia.eta4 Ω).ker, (UnitaryThreeInertia.push B.val (r'.comp (toGS Ω _)) s).left =
      tor _ t * (r (toGS Ω _ s)).left * (tor _ t)⁻¹ := fun s hs => by
    rw [← conj_left r _ _ ((hm s).trans hs), ← ht]
    rfl
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  letI : Algebra K Ω := (IsAlgClosed.lift : K →ₐ[ℚ] Ω).toRingHom.toAlgebra
  have hker : ∀ s : G K Ω, Base.galEmb ℚ K Ω s ∈ (UnitaryThreeInertia.eta4 Ω).ker := fun s => by
    rw [← (UnitaryThreeInertia.gaussian_field_range_eq_ker_quartic_char.2 Ω K hK).1]
    exact ⟨s, rfl⟩
  let j : G K Ω →* (UnitaryThreeInertia.eta4 Ω).ker := (Base.galEmb ℚ K Ω).codRestrict _ hker
  let ρ : G K Ω →* GL (Fin 3) (Qbar l) := (glPart (UnitaryThreeInertia.eta4 Ω) (r.comp (toGS Ω _)) hm).comp j
  let ρ' : G K Ω →* GL (Fin 3) (Qbar l) :=
    (glPart (UnitaryThreeInertia.eta4 Ω) (UnitaryThreeInertia.push B.val (r'.comp (toGS Ω _))) ho.red.mult).comp j
  have hiso : Af.RepIso ρ ρ' := ⟨tor _ t, fun s => hl _ (hker s)⟩
  have key := haut B _ ho (fun V hV hVη => matIrr_conj (tor _ t) (fun s hs => by
    rw [mats, GG.mat, GG.mat, hl s (hVη hs), ← Units.val_mul, ← Units.val_mul]
    congr 1
    group) (hirr V hV hVη)) ρ' fun s => rfl
  refine ⟨inferInstance, inferInstance, ρ, fun s => rfl, ?_⟩
  rw [zpow_neg_one]
  exact _root_.UpperTheory.GalN.V.autCsd_iso_alt (tw_iso _ hiso.symm') key
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
namespace UpperTheory.V.Z.Win.Dn
open UpperTheory.V.Lit UpperTheory.V.W UpperTheory.V.HV UpperTheory.V.Z.Sym.Pl
theorem ends_rank_three_of_local' (hH : _root_.UpperTheory.V.Af.HypothesesH') (hU : J.LinkedUnlE) : LocalConditionRankThreeEvenLevel := fun Ω _ _ _ l _ c _ N _ e ψ hev η σ g₁ B M h =>
  Keep.keeps3E (_root_.UpperTheory.V.W.locPrints_of_litN hH.litN) hU Ω l c N e ψ η σ g₁ B M h hev
theorem ends_of_alt (hH : _root_.UpperTheory.V.Af.HypothesesH') (hE : _root_.UpperTheory.V.Z.Sym.Pl.LinkedEndEAlt) (hU : J.LinkedUnlE) : _root_.UpperTheory.V.Pr.GdEndAlt ∧ _root_.UpperTheory.V.Aut.ThmS6Core_s :=
  have h3 := localConditionRankThreeLink_of_inertia_ordinary ineOfKer_of flagAll_of
  ⟨_root_.UpperTheory.V.Z.Win.Dn.gdEnd_of_frame_linkedEnd_downCsdK_descent hH h3 (_root_.UpperTheory.V.Z.Win.Dn.ends_rank_three_of_local' hH hU) potTwo_of (inertiaConditionRankTwoLink_of_inertia UpperTheory.V.Keep.ineOf) (Fr.gd_ex (_root_.UpperTheory.V.W.global_compat_printed_of_literal_automorphy_n hH.litN)) hE (_root_.UpperTheory.V.Z.Win.Dn.downCsdK_of_printsH hH) (_root_.UpperTheory.V.Af.rankTwoAutomorphyDescends_of_printsH hH)
      (_root_.UpperTheory.V.Br.autNewformA_of_printsH hH) (_root_.UpperTheory.V.Sd.twist_conjugate_selfDual hH.toClassicalTheorems) (_root_.UpperTheory.V.Sd.alg_cyclotomic_of_printed_results hH.toClassicalTheorems),
    _root_.UpperTheory.V.Pr.symmetric_cube_theorem_of_endomorphisms_alt (_root_.UpperTheory.V.Z.Win.Dn.hostEnd_of_loc3_frame_linkedEnd_downCsdK h3 (_root_.UpperTheory.V.Z.Win.Dn.ends_rank_three_of_local' hH hU) (Fr.host_ex (_root_.UpperTheory.V.W.global_compat_printed_of_literal_automorphy_n hH.litN)) hE (_root_.UpperTheory.V.Z.Win.Dn.downCsdK_of_printsH hH))⟩
theorem ends_u_alt (hH : _root_.UpperTheory.V.Af.HypothesesH') (hU : J.LinkedUnlE) : _root_.UpperTheory.V.Pr.GdEndAlt ∧ _root_.UpperTheory.V.Aut.ThmS6Core_s :=
  _root_.UpperTheory.V.Z.Win.Dn.ends_of_alt hH (_root_.UpperTheory.V.Z.Sym.Top.linkedEnd_alt hH (_root_.UpperTheory.V.Z.Win.Birth.seed2_alt hH) (_root_.UpperTheory.V.Z.Sym.W.unitary_three_automorphy_dense_of_prints hH)) hU
end UpperTheory.V.Z.Win.Dn
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LinkedUnlEHolds
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.GaloisCohomology UpperTheory.Top GlobalTheory.Mem.LiteralAutomorphy
namespace UpperTheory.V.Z.J
open UpperTheory.V.HV UpperTheory.V.Lit UpperTheory.V.W UpperTheory.V.J
theorem linkedUnlE_holds_alt (hH : _root_.UpperTheory.V.Af.HypothesesH') (s2 : _root_.UpperTheory.V.Sd.Seed2Alt) (s3 : _root_.UpperTheory.V.Z.Sym.UnitaryThreeAutomorphyDense) : LinkedUnlE :=
  have hN := hH.litN
  have hA := hH.toClassicalTheorems
  _root_.UpperTheory.Gal.projectedFormsSystemPart.linkedUnlE_alt hN.aut.art (_root_.UpperTheory.V.W.local_class_field_theory_all_of_literal_automorphy hN) (_root_.UpperTheory.V.HV.Core.modU_of_printsH hH) (_root_.UpperTheory.V.Z.J.D.modularity_n_of_printed_mult_comp hH Z.Mult.mult_free Z.Mult.compOf_free) levEx
    (lamEx (_root_.UpperTheory.V.W.local_class_field_theory_all_of_literal_automorphy hN)) (b0Ex (phiAll (_root_.UpperTheory.V.W.cohP_alt hN))) s3 s2 (_root_.UpperTheory.V.Sd.twist_of_printed_results hA) (_root_.UpperTheory.V.Sd.alg_cyclotomic_of_printed_results hA) (_root_.UpperTheory.V.Sd.alg_restriction_of_printed_results hA)
    (tanA (_root_.UpperTheory.V.W.global_compat_printed_of_literal_automorphy_n hN) (_root_.UpperTheory.V.W.locPrints_of_litN hN)) (_root_.UpperTheory.V.Th.core_alt_bis hH (_root_.UpperTheory.V.W.cohP_alt hN))
end UpperTheory.V.Z.J
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
namespace UpperTheory.V.Z.Win.Dn
theorem ends0_alt (hH : _root_.UpperTheory.V.Af.HypothesesH') : _root_.UpperTheory.V.Pr.GdEndAlt ∧ _root_.UpperTheory.V.Aut.ThmS6Core_s :=
  _root_.UpperTheory.V.Z.Win.Dn.ends_u_alt hH (_root_.UpperTheory.V.Z.J.linkedUnlE_holds_alt hH (_root_.UpperTheory.V.Z.Win.Birth.seed2_alt hH) (_root_.UpperTheory.V.Z.Sym.W.unitary_three_automorphy_dense_of_prints hH))
end UpperTheory.V.Z.Win.Dn
end
