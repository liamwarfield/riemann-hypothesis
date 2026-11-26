module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeisenbergOrientedFiniteFixesFockPolynomialVecto
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelCohomologicalModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankWeightComponentEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalFockIntertwinerRealPlaceOfCoverContra
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsUnitarySphericalSatakeOfUnitarisableHasSatake
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsUnitarySphericalSatakeMultisetMapInv
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RestrictsSelf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneSemisimple

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsNormEqOfSplitFactor
namespace GlobalTheory.ColPeriod

open NumberField IsDedekindDomain Formalism.L2.Col Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance (DegOneUnram)

section Split

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem absNorm_eq_of_split_factor (h2 : Module.finrank F E = 2) {v : HeightOneSpectrum (𝓞 F)} (hv : DegOne v)
    {P P' : HeightOneSpectrum (𝓞 E)} (hne : P ≠ P')
    (hm : v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) = P.asIdeal * P'.asIdeal) :
    Ideal.absNorm P.asIdeal = Ideal.absNorm v.asIdeal ∧ ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 := by
  obtain ⟨hq, hq2⟩ := hv
  constructor
  · have hr : Module.finrank (𝓞 F) (𝓞 E) = 2 := by
      rw [← h2]
      exact (IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E).symm
    have h1 := Ideal.absNorm_algebraMap (𝓞 F) (𝓞 E) v.asIdeal
    rw [hm, hr, map_mul] at h1
    have hP : Ideal.absNorm P.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]; exact P.isPrime.ne_top
    have hP' : Ideal.absNorm P'.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]; exact P'.isPrime.ne_top
    obtain ⟨k, hk, e⟩ := (Nat.dvd_prime_pow hq).1 (Dvd.intro _ h1)
    interval_cases k
    · exact absurd (by simpa using e) hP
    · simpa using e
    · rw [e] at h1
      exact absurd ((Nat.mul_eq_left (pow_pos hq.pos 2).ne').1 h1) hP'
  · intro hmem
    obtain ⟨I, hI⟩ : v.asIdeal ∣ Ideal.span {((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F)} := by
      rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
      exact Ideal.absNorm_mem _
    have h3 := congrArg (Ideal.map (algebraMap (𝓞 F) (𝓞 E))) hI
    rw [Ideal.map_span, Set.image_singleton, map_natCast, Ideal.map_mul, hm, mul_assoc] at h3
    have h4 : P.asIdeal * P.asIdeal ∣ P.asIdeal * (P'.asIdeal * I.map (algebraMap (𝓞 F) (𝓞 E))) := by
      rw [← h3, ← sq, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
      exact hmem
    have h5 := (mul_dvd_mul_iff_left P.ne_bot).1 h4
    rcases P.prime.dvd_or_dvd h5 with h6 | h6
    · rw [Ideal.dvd_iff_le] at h6
      exact hne (HeightOneSpectrum.ext (P'.isMaximal.eq_of_le P.isPrime.ne_top h6).symm)
    · rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap] at h6
      have h7 : v.asIdeal ≤ P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) := by
        rw [← Ideal.map_le_iff_le_comap, hm]
        exact (Ideal.mul_le_inf).trans inf_le_left
      rw [← v.isMaximal.eq_of_le (Ideal.comap_ne_top _ P.isPrime.ne_top) h7] at h6
      apply hq2
      rw [← Ideal.span_singleton_le_iff_mem, hI, sq]
      exact Ideal.mul_mono_right h6

theorem absNorm_eq_of_splitAt (h2 : Module.finrank F E = 2) {v : HeightOneSpectrum (𝓞 F)} (hs : SplitAt E v)
    (hv : DegOne v) {Q : HeightOneSpectrum (𝓞 E)} (hQ : Q.asIdeal.under (𝓞 F) = v.asIdeal) :
    Ideal.absNorm Q.asIdeal = Ideal.absNorm v.asIdeal ∧ ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 E) ∉ Q.asIdeal ^ 2 := by
  obtain ⟨P, P', hne, hm⟩ := hs
  have h1 : P.asIdeal * P'.asIdeal ≤ Q.asIdeal := by
    rw [← hm, Ideal.map_le_iff_le_comap, ← hQ]
  rcases Q.isPrime.mul_le.1 h1 with h | h
  · obtain rfl : P = Q := HeightOneSpectrum.ext (P.isMaximal.eq_of_le Q.isPrime.ne_top h)
    exact absNorm_eq_of_split_factor h2 hv hne hm
  · obtain rfl : P' = Q := HeightOneSpectrum.ext (P'.isMaximal.eq_of_le Q.isPrime.ne_top h)
    exact absNorm_eq_of_split_factor h2 hv hne.symm (hm.trans (mul_comm _ _))


omit [NumberField E] [Field E] [Algebra F E] in
theorem plc_eq_absNorm {v : HeightOneSpectrum (𝓞 F)} (hq : (Ideal.absNorm v.asIdeal).Prime) :
    Formalism.EigenvalueLevelCeiling.plc v = Ideal.absNorm v.asIdeal := by
  have h6 : ringChar (𝓞 F ⧸ v.asIdeal) ∣ Ideal.absNorm v.asIdeal := by
    rw [← ringChar.spec, ← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.absNorm_mem _
  have := v.isPrime
  rcases (Nat.dvd_prime hq).1 h6 with h7 | h7
  · exact absurd h7 CharP.ringChar_ne_one
  · exact h7

end Split

theorem degOneUnram_of_mem_vG {X : Fields} {Pr : Primes X} (hX : X.Ok) (hPr : Pr.Ok) (i : Fin 2)
    {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Pr.vG i) : DegOneUnram P := by
  have hcc : ∀ x, X.conjO (X.conjO x) = x := fun x => RingOfIntegers.ext (star_star (x : X.E))
  have hE : Module.finrank ℚ X.E = 2 * X.f := by
    rw [← Module.finrank_mul_finrank ℚ X.F X.E, hX.rankE, ← hX.card_Tau, mul_comm]
    rfl
  have hn : qOf P = Pr.g i := hPr.vG_norm i P hP
  refine ⟨hn ▸ hPr.g_prime i, ?_⟩
  rw [hn]
  refine GlobalTheory.SplitUnram.natCast_notMem_sq X.E X.conjO (X.conjO (Pr.piG i)) (Pr.g i) hcc (hPr.g_prime i) ?_ ?_ ?_
    (hPr.vG_norm i) P hP
  · rw [hcc, mul_comm]; exact hPr.piG_norm i
  · rw [hcc]; exact (hPr.piG_cop i).symm
  · rw [hE, ← hPr.vG_card i]; rfl

theorem levelPrimes : LevelPrimes := by
  classical
  intro X Pr sel S mu hX hPr hsel P
  by_cases hP : P.1 ∈ Pr.vGs
  · refine ⟨?_, fun h => absurd hP h⟩
    rcases Finset.mem_union.1 hP with h | h
    exacts [degOneUnram_of_mem_vG hX hPr 0 h, degOneUnram_of_mem_vG hX hPr 1 h]
  · rcases Finset.mem_union.1 P.2 with h1 | h1
    · exact absurd h1 hP
    unfold QE at h1
    split_ifs at h1 with h2
    · obtain ⟨v0, hv0, e⟩ := Finset.mem_image.1 h1
      have hv1 : v0 ∈ Qprime (mu : Chr X.F X.E X.K) := by simpa using hv0
      have hgood : GoodPl X.E S v0 := by
        by_contra hn
        have h4 := (Subgroup.mem_inf.1 mu.2).2
        exact hv1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h4 v0) hn)
      obtain ⟨h3, h4⟩ := absNorm_eq_of_splitAt hX.rankE hgood.1 hgood.2.1 (Q := P.1) (e ▸ hsel v0)
      have h5 : qOf P.1 = Ideal.absNorm v0.asIdeal := h3
      refine ⟨⟨h5 ▸ hgood.2.1.1, h5 ▸ h4⟩, fun _ => ?_⟩
      rw [h5, ← plc_eq_absNorm hgood.2.1.1]
      exact hgood.2.2
    · simp at h1

end GlobalTheory.ColPeriod
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalOperatorsFormsOnRankSpaceNormal
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalOperatorsFormsOnRankSpaceNormal
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SphOpsModel

theorem exists_lift {H X : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup X] [Module ℂ X] (e : H →ₗ[ℂ] X)
    (he : Function.Injective e) (L : X →ₗ[ℂ] X) (hL : ∀ x, L (e x) ∈ LinearMap.range e) :
    ∃ h : Module.End ℂ H, ∀ x, e (h x) = L (e x) := by
  refine ⟨(LinearEquiv.ofInjective e he).symm.toLinearMap ∘ₗ (L ∘ₗ e).codRestrict _ hL, fun x => ?_⟩
  exact congrArg Subtype.val ((LinearEquiv.ofInjective e he).apply_symm_apply ⟨L (e x), hL x⟩)

theorem dualLab_dualLab (d : List ℤ) : dualLab (dualLab d) = d := by
  simp [dualLab, List.map_reverse, List.map_map]

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem sphOp_rep {P : Pl D.host.E} {d : List ℤ} (h : IsLab V P d) : SphOp V P d (GlobalTheory.Hk3.rep V P d) := by
  unfold GlobalTheory.Hk3.rep
  rw [dite_eq_left h]
  exact h.choose_spec

theorem heckeOn_rep_of_not (M : DSModel V S) {P : Pl D.host.E} {d : List ℤ} (h : ¬ IsLab V P d) (U : MMap M) :
    heckeOn M (GlobalTheory.Hk3.rep V P d) U = 0 := by
  ext v g
  unfold GlobalTheory.Hk3.rep
  rw [dite_eq_right h, heckeOn, postOn_apply, heckeLin_apply, Finset.sum_empty]
  rfl

theorem postOn_single (M : DSModel V S) (P : Pl D.host.E) (d : List ℤ) (U : MMap M) :
    postOn M (hk V P (Finsupp.single d 1)) U = heckeOn M (GlobalTheory.Hk3.rep V P d) U := by
  rw [GlobalTheory.LevOp.postOn_hk, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton, Finsupp.single_eq_same,
    one_smul]

section Model

variable {M : DSModel V S} {HM : HMod (MMap M)} {P : Pl D.host.E} {h : (List ℤ →₀ ℂ) → Module.End ℂ HM.H}

theorem op_eq_sum (inj : Function.Injective HM.e) (hh : ∀ c x, HM.e (h c x) = postOn M (hk V P c) (HM.e x))
    (c : List ℤ →₀ ℂ) : h c = c.sum fun d z => z • h (Finsupp.single d 1) := by
  refine LinearMap.ext fun x => inj ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hh, GlobalTheory.LevOp.postOn_hk, Finsupp.sum, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [LinearMap.smul_apply, map_smul, hh, postOn_single]

theorem op_single_of_not (inj : Function.Injective HM.e) (hh : ∀ c x, HM.e (h c x) = postOn M (hk V P c) (HM.e x))
    {d : List ℤ} (hd : ¬ IsLab V P d) : h (Finsupp.single d 1) = 0 := by
  refine LinearMap.ext fun x => inj ?_
  rw [hh, postOn_single, heckeOn_rep_of_not M hd, LinearMap.zero_apply, map_zero]

theorem op_eigen (inj : Function.Injective HM.e) (hh : ∀ c x, HM.e (h c x) = postOn M (hk V P c) (HM.e x))
    {a : List ℤ → ℂ} {x : HM.H} (hx : ∀ d, IsLab V P d → h (Finsupp.single d 1) x = a d • x) (c : List ℤ →₀ ℂ) :
    h c x = evC V P a c • x := by
  rw [op_eq_sum inj hh, evC, Finsupp.sum, Finsupp.sum, LinearMap.sum_apply, Finset.sum_smul]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [LinearMap.smul_apply]
  split_ifs with hd
  · rw [hx d hd, mul_smul]
  · rw [op_single_of_not inj hh hd, LinearMap.zero_apply, smul_zero, zero_smul]

end Model

theorem exists_ops (θ : InfFam D) (M : DSModel V S) (J : Subgroup (GA D V)) (χ : GA D V → ℂ) (μ : Measure (GA D V))
    (𝓕 : Set (GA D V)) (HM : HMod (MMap M)) (a : ℂ) (ok : Pl D.host.E → Prop)
    (hM : HM.Is (Mult θ M (J : Set (GA D V)) χ) fun T T' => a * ipM M μ 𝓕 T T') (hθ : IsInfFam θ) (hμ : μ.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) (hS : SchurMult θ M (J : Set (GA D V)) χ μ 𝓕)
    (hfull : ∀ P, ok P → ∀ d B, Hecke₂ V (J : Set (GA D V)) χ ∅ P d B ↔ SphOp V P d B)
    (hkeep : ∀ P, ok P → ∀ c, ∀ U ∈ Mult θ M (J : Set (GA D V)) χ, postOn M (hk V P c) U ∈ Mult θ M (J : Set (GA D V)) χ) :
    ∃ h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ HM.H,
      (∀ P, ok P → ∀ c x, HM.e (h P c x) = postOn M (hk V P c) (HM.e x)) ∧ NormalFam ok h := by
  obtain ⟨inj, hr, hip⟩ := hM
  have hmem : ∀ x, HM.e x ∈ Mult θ M (J : Set (GA D V)) χ := fun x => hr ▸ LinearMap.mem_range_self _ x
  have hex : ∀ P c, ∃ h : Module.End ℂ HM.H, ok P → ∀ x, HM.e (h x) = postOn M (hk V P c) (HM.e x) := fun P c => by
    by_cases hP : ok P
    · obtain ⟨h, hh⟩ := exists_lift HM.e inj (postOn M (hk V P c)) fun x => hr ▸ hkeep P hP c _ (hmem x)
      exact ⟨h, fun _ => hh⟩
    · exact ⟨0, fun h => absurd h hP⟩
  choose h hh using hex
  have hh' : ∀ P, ok P → ∀ c x, HM.e (h P c x) = postOn M (hk V P c) (HM.e x) := fun P hP c => hh P c hP
  have hdual : ∀ P, ok P → ∀ d, IsLab V P d → IsLab V P (dualLab d) := fun P hP d ⟨B, hB⟩ => by
    obtain ⟨B', hB', -⟩ := GlobalTheory.SphericalOps.exists_dual (GlobalTheory.HeckeAdjoint.realUnif D P) ((hfull P hP d B).2 hB)
    exact ⟨B', (hfull P hP _ B').1 hB'⟩
  refine ⟨h, hh', fun P P' hP hP' c c' => ?_, fun P hP c => ?_⟩
  · rw [op_eq_sum inj (hh' P hP) c, op_eq_sum inj (hh' P' hP') c']
    refine Commute.sum_left _ _ _ fun d _ => Commute.sum_right _ _ _ fun d' _ => ?_
    refine Commute.smul_left (Commute.smul_right ?_ _) _
    by_cases hd : IsLab V P d
    · by_cases hd' : IsLab V P' d'
      · refine LinearMap.ext fun x => inj ?_
        rw [Module.End.mul_apply, Module.End.mul_apply, hh' P hP, hh' P' hP', hh' P' hP', hh' P hP]
        simp only [postOn_single]
        exact MultilinearMap.ext fun v => GlobalTheory.SphericalOps.comm_heckeLin (GlobalTheory.HeckeAdjoint.realUnif D P)
          ((hfull P hP d _).2 (sphOp_rep hd)) ((hfull P' hP' d' _).2 (sphOp_rep hd'))
          (((GlobalTheory.MultMem.mem_mult_iff ..).1 (hmem x)).lev v)
      · rw [op_single_of_not inj (hh' P' hP') hd']
        exact Commute.zero_right _
    · rw [op_single_of_not inj (hh' P hP) hd]
      exact Commute.zero_left _
  · have key : ∀ d, LinearMap.adjoint (h P (Finsupp.single d 1)) = h P (Finsupp.single (dualLab d) 1) := fun d => by
      by_cases hd : IsLab V P d
      · symm
        rw [LinearMap.eq_adjoint_iff]
        intro x y
        rw [hip, hip, hh' P hP, hh' P hP, postOn_single, postOn_single]
        refine congrArg (a * ·) (GlobalTheory.T.petersson_adjoint_heckeOperator_eq_dualLabel D V S θ M J χ ∅ μ 𝓕 hθ hμ h𝓕 hS P (dualLab d) _ _
          ((hfull P hP _ _).2 (sphOp_rep (hdual P hP d hd))) ?_ _ (hmem x) _ (hmem y) ?_ ?_)
        · rw [dualLab_dualLab]
          exact (hfull P hP _ _).2 (sphOp_rep hd)
        · rw [← postOn_single]
          exact hkeep P hP _ _ (hmem x)
        · rw [← postOn_single]
          exact hkeep P hP _ _ (hmem y)
      · have hd' : ¬ IsLab V P (dualLab d) := fun h' => hd (dualLab_dualLab d ▸ hdual P hP _ h')
        rw [op_single_of_not inj (hh' P hP) hd, op_single_of_not inj (hh' P hP) hd', map_zero]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [op_eq_sum inj (hh' P hP) c, op_eq_sum inj (hh' P hP) (dualC _), dualC,
      Finsupp.sum_mapDomain_index (h := fun d (z : ℂ) => z • h P (Finsupp.single d 1)) (fun _ => zero_smul _ _)
        (fun _ _ _ => add_smul _ _ _),
      Finsupp.sum_mapRange_index (h := fun d (z : ℂ) => z • h P (Finsupp.single (dualLab d) 1)) (fun _ => zero_smul _ _), Finsupp.sum, Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [LinearEquiv.map_smulₛₗ, key]
    rfl

theorem parts_of_projector {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (ok : Pl D.host.E → Prop) (lab : Pl D.host.E → List ℤ → Prop) (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ H)
    (hN : NormalFam ok h) (p : Module.End ℂ H) (hp : p * p = p) (he : ∀ P, ok P → ∀ cc, Commute (h P cc) p)
    (W : (Pl D.host.E → List ℤ → ℂ) → Submodule ℂ H)
    (hW : ∀ c x, x ∈ W c ↔ p x = x ∧ ∀ P d, ok P → lab P d → h P (Finsupp.single d 1) x = c P d • x) :
    (⨆ c, W c) = LinearMap.range p ∧
      ∀ c (g : Module.End ℂ H), Commute p g → (∀ P, ok P → ∀ cc, Commute (h P cc) g) → (W c).map g ≤ W c := by
  refine ⟨le_antisymm (iSup_le fun c x hx => ⟨x, ((hW c x).1 hx).1⟩) ?_, ?_⟩
  · obtain ⟨h1, h2, -⟩ := GlobalTheory.normalFamily_orthogonal_decomposition
      (fun j : {j : Pl D.host.E × List ℤ // ok j.1} => h j.1.1 (Finsupp.single j.1.2 1))
      (fun j k => hN.1 _ _ j.2 k.2 _ _) (fun j => ⟨⟨(j.1.1, dualLab j.1.2), j.2⟩, by
        rw [hN.2 _ j.2, dualC, Finsupp.mapRange_single, Finsupp.mapDomain_single, star_one]⟩)
    rw [LinearMap.range_eq_map, ← h2, Submodule.map_iSup]
    refine iSup_le fun y => ?_
    classical
    refine le_iSup_of_le (fun P d => if hP : ok P then y ⟨(P, d), hP⟩ else 0) ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [h1, SetLike.mem_coe, Submodule.mem_iInf] at hx
    refine (hW _ _).2 ⟨LinearMap.congr_fun hp x, fun P d hP _ => ?_⟩
    have h3 := Module.End.mem_eigenspace_iff.1 (hx ⟨(P, d), hP⟩)
    have h4 : h P (Finsupp.single d 1) (p x) = p (h P (Finsupp.single d 1) x) := LinearMap.congr_fun (he P hP _).eq x
    rw [dite_eq_left hP, h4, ← map_smul]
    exact congrArg _ h3
  · rintro c g hg hg' _ ⟨x, hx, rfl⟩
    obtain ⟨h1, h2⟩ := (hW c x).1 hx
    refine (hW _ _).2 ⟨?_, fun P d hP hd => ?_⟩
    · have h4 : p (g x) = g (p x) := LinearMap.congr_fun hg.eq x
      rw [h4, h1]
    · have h4 : h P (Finsupp.single d 1) (g x) = g (h P (Finsupp.single d 1) x) := LinearMap.congr_fun (hg' P hP _).eq x
      rw [h4, h2 P d hP hd, map_smul]

theorem sphericalOperators_forms_on_rank_space_normal_alt : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → SchurAll R → (∀ χ ∈ A.X, IsAbsIrrChar χ) → ∀ SF, IsSF R SF → ∀ i, ∃ h, IsOpsW R i h ∧ NormalFam (Good R A.μ0) h ∧ (∀ P, Good R A.μ0 P → ∀ cc g, Commute (h P cc) (R.gW i (sg0 D A) g)) ∧ (⨆ c, Wcc R SF i c) = LinearMap.range (eH R i) ∧ (∀ c g, (Wcc R SF i c).map (R.gW i (sg0 D A) g) ≤ Wcc R SF i c) ∧ (∀ c P, Good R A.μ0 P → ∀ cc, ∀ x ∈ Wcc R SF i c, h P cc x = evC (Wc D i) P (c P) cc • x) ∧ ∀ (c : Pl D.host.E → List ℤ → ℂ) x, eH R i x = x → (∀ P d, Good R A.μ0 P → IsLab (Wc D i) P d → h P (Finsupp.single d 1) x = c P d • x) → x ∈ Wcc R SF i c := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC hS hX SF hSF i
  obtain ⟨hQ, hgood, hoff, -⟩ := GlobalTheory.GoodPrimes.good_primes R F hC.lev
  obtain ⟨n, hβ⟩ := hC.lev.βW i
  have hlev := fun (P : Pl D.host.E) (hP : Good R A.μ0 P) =>
    GlobalTheory.LevOp.level_operators (Wc D i) (R.βW i) (R.ΛW i) (1 ^ n) (R.datWp i R.triv) hβ P
      (by rw [one_pow, Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top)
      (fun PP hPP => hP PP (hPP.imp id fun h => absurd h (Finset.notMem_empty _)))
  have hM := hC.models.HW i (sg0 D A)
  have inj : Function.Injective (R.HW i (sg0 D A)).e := hM.1
  have hmem : ∀ x, (R.HW i (sg0 D A)).e x ∈ R.Wall i (sg0 D A) := fun x => hM.2.1 ▸ LinearMap.mem_range_self _ x
  have hlv := fun x v => ((GlobalTheory.MultMem.mem_mult_iff ..).1 (hmem x)).lev v
  obtain ⟨e1, e2, e3, -⟩ := GlobalTheory.T.goodProjector_unitaryFormsModel_laws R F hC hX i
  obtain ⟨h, hh, hN⟩ := exists_ops R.θ (R.MW i (sg0 D A)) (levG _ (R.βW i) (R.datWp i R.triv))
    (levChi _ (R.βW i) (R.datWp i R.triv)) (R.νW i) (R.fdW i) (R.HW i (sg0 D A)) _ (Good R A.μ0) hM hC.models.inf
    (hC.models.νW i).1.1 (hC.models.νW i).2 (hS.2.2 i)
    (fun P hP d B => ((hlev P hP).2.1 ∅ d B).trans (and_iff_right GlobalTheory.LevOp.offS_empty))
    (fun P hP c => (hlev P hP).2.2.2.2 _ R.θ _ c hC.models.inf)
  have hg : ∀ P, Good R A.μ0 P → ∀ cc g, Commute (h P cc) (R.gW i (sg0 D A) g) := fun P hP cc g => by
    refine LinearMap.ext fun x => inj ?_
    rw [Module.End.mul_apply, Module.End.mul_apply, hh P hP, hC.models.gW, hC.models.gW, hh P hP]
    refine MultilinearMap.ext fun v => ((hlev P hP).2.2.2.1 cc (R.eG g) _ fun k hk y => ?_).symm
    rw [hlv x v k ((hlev P hP).1 k hk).1, ((hlev P hP).1 k hk).2, one_mul]
  have he : ∀ P, Good R A.μ0 P → ∀ cc, Commute (h P cc) (eH R i) := fun P hP cc =>
    Commute.sum_right _ _ _ fun g _ => (hg P hP cc g).smul_right _
  have hW : ∀ (c : Pl D.host.E → List ℤ → ℂ) x, x ∈ Wcc R SF i c ↔ eH R i x = x ∧
      ∀ P d, Good R A.μ0 P → IsLab (Wc D i) P d → h P (Finsupp.single d 1) x = c P d • x := fun c x => by
    unfold Wcc
    rw [Submodule.mem_comap, Submodule.mem_inf, e3, mem_partFull]
    refine and_congr_right fun _ => ⟨fun hx P d hP hd => inj ?_, fun hx => ⟨hmem x, fun P d B hB v => ?_⟩⟩
    · rw [hh P hP, postOn_single, map_smul]
      exact MultilinearMap.ext fun v => hx.2 P d _ (((hlev P hP).2.1 SF d _).2 ⟨(hoff SF hSF P).2 hP, sphOp_rep hd⟩) v
    · have hP : Good R A.μ0 P := by
        obtain ⟨_, _, _, _, ho, _⟩ := hB
        exact (hoff SF hSF P).1 ho
      have hd : IsLab (Wc D i) P d := ⟨B, (((hlev P hP).2.1 SF d B).1 hB).2⟩
      have h1 := congrArg (R.HW i (sg0 D A)).e (hx P d hP hd)
      rw [hh P hP, postOn_single, map_smul] at h1
      rw [GlobalTheory.SphericalOps.labelUnique (J := levG _ (R.βW i) (R.datWp i R.triv)) (GlobalTheory.HeckeAdjoint.realUnif D) P d B _ hB
        (((hlev P hP).2.1 SF d _).2 ⟨(hoff SF hSF P).2 hP, sphOp_rep hd⟩) _ (hlv x v)]
      exact congrArg (fun U => U v) h1
  obtain ⟨h1, h2⟩ := parts_of_projector (Good R A.μ0) (IsLab (Wc D i)) h hN (eH R i) e1 he (Wcc R SF i) hW
  refine ⟨h, hh, hN, hg, h1, fun c g => h2 c _ (e2 g) fun P hP cc => hg P hP cc g, ?_, fun c x h1 h2 => (hW c x).2 ⟨h1, h2⟩⟩
  intro c P hP cc x hx
  exact op_eigen inj (hh P hP) (fun d hd => ((hW c x).1 hx).2 P d hP hd) cc

end GlobalTheory.SphOpsModel

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalOperatorsFormsOnRankSpaceNormalStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sphericalOperators_forms_on_rank_space_normal : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → SchurAll R → (∀ χ ∈ A.X, IsAbsIrrChar χ) → ∀ SF, IsSF R SF → ∀ i, ∃ h, IsOpsW R i h ∧ NormalFam (Good R A.μ0) h ∧ (∀ P, Good R A.μ0 P → ∀ cc g, Commute (h P cc) (R.gW i (sg0 D A) g)) ∧ (⨆ c, Wcc R SF i c) = LinearMap.range (eH R i) ∧ (∀ c g, (Wcc R SF i c).map (R.gW i (sg0 D A) g) ≤ Wcc R SF i c) ∧ (∀ c P, Good R A.μ0 P → ∀ cc, ∀ x ∈ Wcc R SF i c, h P cc x = evC (Wc D i) P (c P) cc • x) ∧ ∀ (c : Pl D.host.E → List ℤ → ℂ) x, eH R i x = x → (∀ P d, Good R A.μ0 P → IsLab (Wc D i) P d → h P (Finsupp.single d 1) x = c P d • x) → x ∈ Wcc R SF i c := by
  first | exact @GlobalTheory.SphOpsModel.sphericalOperators_forms_on_rank_space_normal_alt | exact GlobalTheory.SphOpsModel.sphericalOperators_forms_on_rank_space_normal_alt | (intros; apply GlobalTheory.SphOpsModel.sphericalOperators_forms_on_rank_space_normal_alt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RegularAlgebraicPurityOfClozel
namespace GlobalTheory

theorem regularAlgebraicPurity_of_clozel (hP : GlobalTheory.Published.ClozelPurity) (hC : GlobalTheory.Published.ClozelCohomological) :
    GlobalTheory.Published.RegularAlgebraicPurity := by
  intro E _ _ _ a ha π hr
  exact ⟨hP E a ha π fun τ => (hr τ).2, hC E a ha π hr⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsInertPlOfInertOff
open Formalism.BasicNotions IsDedekindDomain NumberField

noncomputable section
namespace GlobalTheory.InertOfConj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem unram (D : D7) : Algebra.Unramified (𝓞 D.host.F) (𝓞 D.host.E) := by
  haveI := D.host.isCMField_hostE
  exact Formalism.L2.Pj.unramBridge_holds D.host.E fun P hP => by
    obtain ⟨θ, t, ht, hθ⟩ := D.sp.cm.cmUnram.2.2 P hP
    refine ⟨θ, ?_⟩
    have : RingOfIntegers.mapRingEquiv
        (IsCMField.complexConj D.host.E : D.host.E ≃+* D.host.E) θ = t :=
      RingOfIntegers.ext ht.symm
    rwa [this]

end GlobalTheory.InertOfConj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharacterisationPlacesPartsOfWeak
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharacterisationPlacesPartsOfWeak
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoreThree

open Formalism.IndefR.Bridge in
theorem conj_ne_of_two {D : D7} (P : HeightOneSpectrum (𝓞 D.host.E)) (h2 : ((2 : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) :
    Formalism.DivisionValues.conjPl P ≠ P := by
  intro hP
  have hP' : P.asIdeal.map (Formalism.DivisionValues.cO D.host.E) = P.asIdeal := congrArg HeightOneSpectrum.asIdeal hP
  have hfix : ∀ x : 𝓞 D.host.E, Formalism.DivisionValues.cO D.host.E x ∈ P.asIdeal ↔ x ∈ P.asIdeal := fun x => by
    conv_lhs => rw [← hP']
    exact Ideal.apply_mem_of_equiv_iff
  refine Formalism.MainNotions.KudlaSiegelWeil.InertConditionsOfHost.not_fixed_ram D P 2 (Or.inl rfl) h2 (Ideal.ext fun x => ?_)
  rw [Ideal.mem_comap, ← hfix x]
  refine Eq.to_iff (congrArg (· ∈ P.asIdeal) (RingOfIntegers.ext ?_))
  exact (Formalism.BasicNotions.Examples₂.star_eq_conj D.host _).symm

theorem exists_two (D : D7) : ∃ P : HeightOneSpectrum (𝓞 D.host.E), ((2 : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
  haveI : (Ideal.span {(2 : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp Nat.prime_two).irreducible
  obtain ⟨Q, hQ, hc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 D.host.E) (Ideal.span {(2 : ℤ)}) (by
    intro x hx
    rw [RingHom.mem_ker] at hx
    have : x = 0 := by
      have := congrArg (fun y : 𝓞 D.host.E => ((y : D.host.E))) hx
      simpa using this
    rw [this]; exact zero_mem _)
  have h2 : ((2 : ℕ) : 𝓞 D.host.E) ∈ Q := by
    have : (2 : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 D.host.E)) := by
      change (2 : ℤ) ∈ Ideal.under ℤ Q
      rw [hc]
      exact Ideal.mem_span_singleton_self _
    simpa using this
  refine ⟨⟨Q, hQ.isPrime, fun hb => ?_⟩, h2⟩
  rw [hb, Ideal.mem_bot] at h2
  have := congrArg (fun y : 𝓞 D.host.E => ((y : D.host.E))) h2
  norm_num at this

end GlobalTheory.CoreThree

namespace GlobalTheory.CoreThree

theorem heckeCharacterisation_places_parts_of_weak : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → (R.toRealDat.ExAt → Core R.toRealDat F.lv2) ∧ IsSF R.toRealDat R.SF ∧ (∀ t, ∀ Q ∈ A3.okI t, Good R.toRealDat t (R.plI Q) ∧ Formalism.DivisionValues.conjPl (R.plI Q) = R.plI Q) ∧ (∀ P, Good R.toRealDat A3.A.μ0 P → (Formalism.DivisionValues.conjPl P = P → ∃ Q ∈ A3.okI A3.A.μ0, R.plI Q = P) ∧ (Formalism.DivisionValues.conjPl P ≠ P → ∃ P0 ∈ A3.A.ok A3.A.μ0, R.pl P0 = P)) ∧ (∀ c, R.EEc c = EEc R.toRealDat R.SF c) ∧ (∀ i c, R.Wc' i c = Wcc R.toRealDat R.SF i c) ∧ (A3.A.ok A3.A.μ0).Nonempty := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F h
  have hL : R.toLevCh.Is A3.A.μ0 := h.base.lev
  obtain ⟨hQ0, -, -, -⟩ := GlobalTheory.GoodPrimes.good_primes R.toRealDat F.lv2 hL
  obtain ⟨_, _, _, ht⟩ := h.base.fam.tie
  have hSb : (R.Sb : Set (Pl D.host.E)) = R.Pg := by rw [h.allPl]
  have hon : ∀ P, Good R.toRealDat A3.A.μ0 P → (Formalism.DivisionValues.conjPl P = P → ∃ Q ∈ A3.okI A3.A.μ0, R.plI Q = P) ∧
      (Formalism.DivisionValues.conjPl P ≠ P → ∃ P0 ∈ A3.A.ok A3.A.μ0, R.pl P0 = P) := by
    intro P hP
    have hnS : P ∉ (R.Sb : Set (Pl D.host.E)) := by
      rw [hSb]; intro hm; exact (hP P (Or.inl hm)).1 rfl
    refine ⟨fun hf => ?_, fun hf => ?_⟩
    · have hio : Formalism.IndefR.Bridge.InertOff P (R.Sb : Set (Pl D.host.E)) := by
        refine ⟨?_, hnS⟩
        rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq, hf]
      obtain ⟨Q, hQ⟩ := h.inert.onto P hio
      refine ⟨Q, (h.inert.tie.okI A3.A.μ0 Q).2 ?_, hQ⟩
      rw [hQ0, Finset.coe_empty, Set.union_empty, hQ]
      exact hio
    · have hso : Formalism.IndefR.Bridge.SplitOff P (R.Sb : Set (Pl D.host.E)) := by
        refine ⟨?_, hnS, fun Q hQ he => ?_⟩
        · rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq]
          exact fun he => hf (HeightOneSpectrum.ext he)
        · rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq] at he
          have hQP : Q = Formalism.DivisionValues.conjPl P := HeightOneSpectrum.ext he
          rw [hSb] at hQ
          apply (hP Q (Or.inl hQ)).2
          have := GlobalTheory.SplitHeckeAdj.isConjPl_conj (Formalism.DivisionValues.conjPl P)
          rw [Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl] at this
          rw [hQP]; exact this
      obtain ⟨P0, hP0⟩ := h.base.fam.pl_onto P hso
      refine ⟨P0, (ht.ok A3.A.μ0 P0).2 ?_, hP0⟩
      rw [hQ0, Finset.coe_empty, Set.union_empty, hP0]
      exact hso
  refine ⟨fun e => (GlobalTheory.CoreOfWeak.core_of_weak R F h e).1, ?_, ?_, hon, fun c => rfl, fun i c => rfl, ?_⟩
  · intro v
    rw [h.inert.SF v, h.allPl]
  · intro t Q hQ
    obtain ⟨hfix, hoff⟩ := (h.inert.tie.okI t Q).1 hQ
    rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq] at hfix
    have hf : Formalism.DivisionValues.conjPl (R.plI Q) = R.plI Q := HeightOneSpectrum.ext hfix
    refine ⟨fun PP hPP => ⟨fun he => hoff ?_, fun hc => hoff ?_⟩, hf⟩
    · rcases hPP with hm | hm
      · exact Or.inl (by rw [hSb, ← he]; exact hm)
      · exact Or.inr (by rw [← he]; exact hm)
    · have e1 := GlobalTheory.SplitHeckeAdj.eq_conj_of_isConjPl hc
      have e2 : PP = R.plI Q := by
        rw [← Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl PP, ← e1, hf]
      rcases hPP with hm | hm
      · exact Or.inl (by rw [hSb, ← e2]; exact hm)
      · exact Or.inr (by rw [← e2]; exact hm)
  · obtain ⟨P, h2⟩ := exists_two D
    have hg : Good R.toRealDat A3.A.μ0 P := by
      intro PP hPP
      rw [hQ0] at hPP
      have hm : PP ∈ R.Pg := hPP.resolve_right (by simp)
      obtain ⟨k, hk⟩ := (hL.Pg PP).1 hm
      have hgk := GlobalTheory.LevelPlaces.mem_of_div _ k PP hk
      have hn : ((2 : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal :=
        GlobalTheory.LevelPlaces.not_mem_of_prime PP.isPrime.ne_top Nat.prime_two (D.host.g_prime k) (Formalism.L2.Pj.g_ne_two D k) hgk
      refine ⟨fun he => hn (he ▸ h2), fun hc => ?_⟩
      have hgP := GlobalTheory.LevelPlaces.natCast_mem_of_isConjPl hc hgk
      exact GlobalTheory.LevelPlaces.not_mem_of_prime P.isPrime.ne_top Nat.prime_two (D.host.g_prime k)
        (Formalism.L2.Pj.g_ne_two D k) hgP h2
    obtain ⟨P0, hP0, -⟩ := (hon P hg).2 (conj_ne_of_two P h2)
    exact ⟨P0, hP0⟩

end GlobalTheory.CoreThree
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharacterisationPlacesPartsOfWeakStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeCharacterisation_places_of_weakCharacterisation : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → (R.toRealDat.ExAt → Core R.toRealDat F.lv2) ∧ IsSF R.toRealDat R.SF ∧ (∀ t, ∀ Q ∈ A3.okI t, Good R.toRealDat t (R.plI Q) ∧ Formalism.DivisionValues.conjPl (R.plI Q) = R.plI Q) ∧ (∀ P, Good R.toRealDat A3.A.μ0 P → (Formalism.DivisionValues.conjPl P = P → ∃ Q ∈ A3.okI A3.A.μ0, R.plI Q = P) ∧ (Formalism.DivisionValues.conjPl P ≠ P → ∃ P0 ∈ A3.A.ok A3.A.μ0, R.pl P0 = P)) ∧ (∀ c, R.EEc c = EEc R.toRealDat R.SF c) ∧ (∀ i c, R.Wc' i c = Wcc R.toRealDat R.SF i c) ∧ (A3.A.ok A3.A.μ0).Nonempty := by
  first | exact @GlobalTheory.CoreThree.heckeCharacterisation_places_parts_of_weak | exact GlobalTheory.CoreThree.heckeCharacterisation_places_parts_of_weak | (intros; apply GlobalTheory.CoreThree.heckeCharacterisation_places_parts_of_weak <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplittingCharactersUnramifiedOffLevels
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplittingCharactersUnramifiedOffLevels
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnrOffLevels

open GlobalTheory.IdemSupport GlobalTheory.ResLoc Formalism.L2.JoinChr

theorem exists_glue {A : Type} [CommRing A] {e : A} (he : e * e = e) (x : Aˣ) :
    ∃ y : Aˣ, (y : A) = e * (x : A) + (1 - e) ∧ e * ((y : A) - 1) = (y : A) - 1 := by
  have hxx : (x : A) * ((x⁻¹ : Aˣ) : A) = 1 := Units.mul_inv x
  refine ⟨⟨e * (x : A) + (1 - e), e * ((x⁻¹ : Aˣ) : A) + (1 - e), ?_, ?_⟩, rfl, ?_⟩
  · linear_combination (e * e) * hxx + (2 - (x : A) - ((x⁻¹ : Aˣ) : A)) * he
  · linear_combination (e * e) * hxx + (2 - (x : A) - ((x⁻¹ : Aˣ) : A)) * he
  · change e * (e * (x : A) + (1 - e) - 1) = e * (x : A) + (1 - e) - 1
    linear_combination ((x : A) - 1) * he

variable {D : D7}


set_option maxHeartbeats 1000000 in
theorem exists_part {c : (AE D)ˣ →* Circle} {χ : Formalism.L2.Host.HChar D.host.E} (hc : ChrEq c χ) {P : Pl D.host.E} (hu : χ.UnrAt P)
    {Φ : AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E} (hΦ : Comp D Φ) {e : AE D} (hd : IsDelta Φ P e) (hpl : IsPlIdem D e P)
    (x : (AE D)ˣ) (h1 : finPart D (x : AE D) ∈ intAE D) (h2 : finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D) :
    ∃ y : (AE D)ˣ, (y : AE D) = e * (x : AE D) + (1 - e) ∧ c y = 1 := by
  obtain ⟨d0, d1, d2⟩ := id hd
  have he : e * e = e := hpl.1
  obtain ⟨N, hN, hker⟩ := exists_modulus hΦ c hc.1.1
  obtain ⟨y, hy, hsupp⟩ := exists_glue he x
  have hyP : Φ (y : AE D) P = Φ (x : AE D) P := by
    rw [hy, ev_add, ev_mul, d1, one_mul, ev_sub, ev_one, d1, sub_self, add_zero]
  have hv : Valued.v (Φ (x : AE D) P) = 1 := by
    have a : Valued.v (Φ (x : AE D) P) ≤ 1 := (hΦ.int _).1 h1 P
    have b : Valued.v (Φ ((x⁻¹ : (AE D)ˣ) : AE D) P) ≤ 1 := (hΦ.int _).1 h2 P
    have ab : Valued.v (Φ (x : AE D) P) * Valued.v (Φ ((x⁻¹ : (AE D)ˣ) : AE D) P) = 1 := by
      rw [← map_mul, ← ev_mul, Units.mul_inv, ev_one, map_one]
    refine le_antisymm a ?_
    rw [← ab]
    exact mul_le_of_le_one_right' b
  have hy1 : Valued.v (Φ (y : AE D) P) = 1 := by rw [hyP, hv]
  obtain ⟨k, k1, k2, k3⟩ := GlobalTheory.adicCompletion_exists_unit_approx D.host.E N hN P (Φ (y : AE D) P) (fun h => by
    rw [h, map_zero] at hy1
    exact zero_ne_one hy1)
  rw [hy1] at k1
  rw [← k1, mul_one] at k2 k3
  obtain ⟨l, hl⟩ : ∃ l : (AE D)ˣ, (l : AE D) = 1 + e * (incA D (k : D.host.E) - 1) := ⟨locU hpl.1 k, rfl⟩
  obtain ⟨z, hz, hz'⟩ := exists_units_quot y l hl
  have hyz : Φ (y : AE D) P = Φ (z : AE D) P * algebraMap D.host.E _ (k : D.host.E) := by
    rw [← ev_inc hΦ]
    exact map_eq_mul_of_supp (evAt Φ P) d1 hz'
  have hcz : c z = 1 := by
    refine hker P z (map_eq_one_of_supp (infPart D) d0 hsupp hz')
      (fun Q hQ => map_eq_one_of_supp (evAt Φ Q) (d2 Q hQ) hsupp hz') ?_ ?_
    · rwa [hyz, map_mul, val_alg, ← k1, mul_one] at hy1
    · rwa [hyz, ← sub_one_mul, map_mul, val_alg, ← k1, mul_one] at k2
  have hcl : c l = 1 := by
    have e1 := hc.2 P e hpl k l hl
    have e2 : χ.locK P k = 1 := by
      refine hu (Formalism.L2.Host.atFin P k) ?_
      change Valued.v (algebraMap D.host.E (P.adicCompletion D.host.E) (k : D.host.E)) = 1
      rw [val_alg]
      exact k1.symm
    rw [e2, Units.val_one] at e1
    exact Circle.ext e1
  exact ⟨y, hy, by rw [hz, map_mul, hcz, hcl, one_mul]⟩

theorem unrPl_of_chrEq {c : (AE D)ˣ →* Circle} {χ : Formalism.L2.Host.HChar D.host.E} (hc : ChrEq c χ) {P : Pl D.host.E} (h : χ.UnrAt P)
    (h' : χ.UnrAt (Formalism.DivisionValues.conjPl P)) : UnrPl P c := by
  intro e f hp x hx h1 h2
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  have hd : IsDelta Φ P e := (of_isPrimeIdem hΦ hp).1
  rcases hp with ⟨hi, rfl⟩ | ⟨rfl, ⟨v, ε, hε, he⟩, ht⟩
  · have hc' : Formalism.IndefR.Lev.IsConjPl P (Formalism.DivisionValues.conjPl P) := GlobalTheory.GoodPrimes.isConjPl_iff.2 rfl
    have hi' : Formalism.L2.NTheta.IsIdemAt (cA D e) (Formalism.DivisionValues.conjPl P) :=
      (supported_group_and_prime_idempotents (D.sp.V 0)).2.2.2 P _ e hi hc'
    have hd' : IsDelta Φ (Formalism.DivisionValues.conjPl P) (cA D e) := delta_of_isIdemAt hΦ hi'
    have pl : ∀ {w : Pl D.host.E} {a : AE D}, Formalism.L2.NTheta.IsIdemAt a w → IsPlIdem D a w := fun ha => by
      obtain ⟨⟨e1, e2, v, ε, hε, e3⟩, e4⟩ := ha
      exact ⟨e1, ⟨v, ε, hε, Or.inl ⟨e2, e3⟩⟩, e4⟩
    obtain ⟨y, hy, hy1⟩ := exists_part hc h hΦ hd (pl hi) x h1 h2
    obtain ⟨z, hz, hz1⟩ := exists_part hc h' hΦ hd' (pl hi') x h1 h2
    have ho : e * cA D e = 0 := hi.1.2.1
    have e1 : x = y * z := Units.ext (by
      rw [Units.val_mul, hy, hz]
      linear_combination (-1 : AE D) * hx - ((x : AE D) - 1) ^ 2 * ho)
    rw [e1, map_mul, hy1, hz1, one_mul]
  · obtain ⟨y, hy, hy1⟩ := exists_part hc h hΦ hd ⟨delta_idem hΦ hd, ⟨v, ε, hε, Or.inr he⟩, ht⟩ x h1 h2
    have e1 : x = y := Units.ext (by rw [hy]; linear_combination (-1 : AE D) * hx)
    rw [e1, hy1]

theorem unrPl_of_good : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.toLevCh.Is A.μ0 → ∀ t P, Good R t P → UnrPl P R.eta ∧ ∀ j, 1 ≤ j → j ≤ D.R.m → UnrPl P (R.toLevCh.mu t j) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL t P hP
  obtain ⟨hg, hc, -⟩ := (GlobalTheory.GoodPrimes.good_primes R F hL).2.1 t P hP
  have hg' := (GlobalTheory.GoodPrimes.good_primes R F hL).2.1 t _ hc
  have hμ : ∀ w, Good R t w → ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal → ∀ k, (hk : k < D.R.m) →
      (R.C.mu0 ⟨k, hk⟩).UnrAt w ∧ (R.xiH t).UnrAt w := fun w hw hgw k hk => by
    refine ⟨(R.C.isMu0 _).unr w fun i hi => ?_, ?_⟩
    · have hi' : ((D.host.g i : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := hi
      refine hgw ?_
      rw [Nat.cast_mul]
      fin_cases i
      · exact Ideal.mul_mem_right _ _ hi'
      · exact Ideal.mul_mem_left _ _ hi'
    · by_contra h
      rcases (hL.Q_ram t w).1 h with h | ⟨PP, h, hc⟩
      · exact (hw w (Or.inr h)).1 rfl
      · exact (hw PP (Or.inr h)).2 hc
  refine ⟨unrPl_of_chrEq hL.eta (R.C.isEta.unr _) (R.C.isEta.unr _), fun j h1 h2 => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have a := unrPl_of_chrEq (hL.mu0 ⟨k, h2⟩) (hμ P hP hg k h2).1 (hμ _ hc hg'.1 k h2).1
  have b := unrPl_of_chrEq (hL.xi t) (hμ P hP hg k h2).2 (hμ _ hc hg'.1 k h2).2
  intro e f h x x1 x2 x3
  show R.mu0 (k + 1) x * R.xi t x = 1
  rw [a e f h x x1 x2 x3, b e f h x x1 x2 x3, one_mul]

end GlobalTheory.UnrOffLevels
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplittingCharactersUnramifiedOffLevelsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splittingCharacters_unramified_offLevels : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.toLevCh.Is A.μ0 → ∀ t P, Good R t P → UnrPl P R.eta ∧ ∀ j, 1 ≤ j → j ≤ D.R.m → UnrPl P (R.toLevCh.mu t j) := by
  first | exact @GlobalTheory.UnrOffLevels.unrPl_of_good | exact GlobalTheory.UnrOffLevels.unrPl_of_good | (intros; apply GlobalTheory.UnrOffLevels.unrPl_of_good <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FamilySplitOperatorsEqLabelOperatorsModels
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FamilySplitOperatorsEqLabelOperatorsModels
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitHeckeLabel

theorem ext_mul {Gr Γ W K : Type} [Group Gr] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K] [NumberField K]
    [StarRing K] {ι : Γ →* Gr} {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup Gr} {χ : J →* ℂˣ}
    (P : Bridge.ClassPres ι S σ ρ J χ) (f : S.Forms) (g : Gr) (k : J) (hk : χ k = 1) : P.ext f.1 (g * k) = P.ext f.1 g := by
  have h2 := (GlobalTheory.classPres_basic ι S σ ρ J χ P).1 f 1 g k
  rwa [map_one, map_one, one_mul, Module.End.one_apply, hk, Units.val_one, one_smul] at h2

def rightTr {H Gr : Type} [Group H] [Group Gr] (φ : H →* Gr) (W : Type) [AddCommGroup W] [Module ℂ W] :
    H →* Module.End ℂ (Gr → W) where
  toFun g := LinearMap.funLeft ℂ W (fun h => h * φ g)
  map_one' := by ext F h; simp [LinearMap.funLeft]
  map_mul' g g' := by ext F h; simp [LinearMap.funLeft, mul_assoc]

theorem rightTr_sum {H Gr : Type} [Group H] [Group Gr] (φ : H →* Gr) {W : Type} [AddCommGroup W] [Module ℂ W] (s : Finset H)
    (F : Gr → W) (h : Gr) : (∑ γ ∈ s, rightTr φ W γ) F h = ∑ γ ∈ s, F (h * φ γ) := by
  rw [LinearMap.sum_apply, Finset.sum_apply]
  rfl

theorem opOf_single {D : D7} {V : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M)
    (P : Pl D.host.E) (d : List ℤ) : opOf π P (Finsupp.single d 1) = ∑ γ ∈ Hk3.rep V P d, π γ := by
  unfold opOf
  rw [Finsupp.sum_single_index (by exact zero_smul ℂ _), one_smul]

theorem hkF_single {D : D7} (V : HSp D) {W : Type} [AddCommGroup W] [Module ℂ W] (P : Pl D.host.E) (d : List ℤ)
    (F : Bridge.Gf V → W) :
    hkF V P (Finsupp.single d 1) F = opOf (rightTr (finHom V).rangeRestrict W) P (Finsupp.single d 1) F := by
  funext h
  have e1 : hkF V P (Finsupp.single d 1) F h = (1 : ℂ) • ∑ γ ∈ Hk3.rep V P d, F (h * (finHom V).rangeRestrict γ) :=
    Finsupp.sum_single_index (h := fun d (z : ℂ) => z • ∑ γ ∈ Hk3.rep V P d, F (h * (finHom V).rangeRestrict γ))
      (zero_smul ℂ _)
  exact e1.trans ((one_smul ℂ _).trans ((rightTr_sum (finHom V).rangeRestrict _ F h).symm.trans
    (congrArg (fun u : Module.End ℂ (Bridge.Gf V → W) => u F h) (opOf_single _ P d).symm)))

theorem side_label {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (L : LevDat D.host.E ℂ V.rank) (hβ : IsSDFrame V β Λ 1) {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {ρ : GQ V →* Module.End ℂ W} {K : Type} [Field K] [NumberField K] [StarRing K] {σ : K →+* ℂ} {S : CSD K}
    (Pr : Bridge.ClassPres (Bridge.ratF V) S σ ρ (levEnv V β L).J (levEnv V β L).χ) {Pl0 : Type} (pl : Pl0 → Pl D.host.E)
    (ok : Set Pl0) (op : ok × ℕ → Module.End K S.Forms)
    (Comparison₂ : Bridge.HeckeTie (Bridge.ratF V) Pr op (fun i => 1 ≤ i.2 ∧ i.2 ≤ V.rank) (isTEnv V pl ok) (isLocEnv V pl ok))
    (P : ok) (h0 : op (P, 0) = 1) (hoff : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ pl P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP (pl P))
    (k : ℕ) (hk : k ≤ V.rank) (f : S.Forms) :
    Pr.ext (op (P, k) f).1 = hkF V (pl P) (Finsupp.single (splitLab V.rank k) 1) (Pr.ext f.1) := by
  refine hβ.elim fun c hc => ?_
  have hc' : IsBaseFrame V β Λ 1 := (one_pow c : (1 : ℕ) ^ c = 1) ▸ hc
  have h1 : ((1 : ℕ) : 𝓞 D.host.E) ∉ (pl P).asIdeal := by
    rw [Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 (pl P).isPrime.ne_top
  have hl := fun e f' he => (GlobalTheory.LevSplit.lev_split V β Λ 1 (flag1L L) hc').2 (pl P) e f' he h1 hoff
  have hinv : ∀ g (x : (levEnv V β L).J), GlobalTheory.Hk3.IsLocElt V (pl P) x → Pr.ext f.1 (g * x) = Pr.ext f.1 g := by
    rintro g ⟨x, hx⟩ ⟨e, f', a, he, ha, hxa, hs⟩
    obtain rfl : x = (finHom V).rangeRestrict a := Subtype.ext hxa
    exact ext_mul Pr f g _ (Units.ext ((hl e f' he).2.1 a ⟨ha, hx⟩ hs))
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · have e0 : splitLab V.rank 0 = List.replicate V.rank 0 := by simp [splitLab]
    rw [h0, e0, hkF_single]
    refine ((GlobalTheory.T.spherical_label_operators_on_hyperspecial_fixed_vectors V (pl P)).2.2.1.2 _ _ _ fun a ha => ?_).symm
    obtain ⟨ha, e, f', he, hs⟩ := ha
    funext g
    exact hinv g ⟨(finHom V).rangeRestrict a, (((hl e f' he).1 a hs).2 ha).2⟩ ⟨e, f', a, he, ha.1, rfl, hs⟩
  · have hi : 1 ≤ ((P, k) : ok × ℕ).2 ∧ ((P, k) : ok × ℕ).2 ≤ V.rank := ⟨hpos, hk⟩
    have hs := fun x => GlobalTheory.T.split_hecke_element_label_zeros_then_neg_ones V pl ok (P, k) x
    have hd := GlobalTheory.T.doubleCosetOperator_eq_labelOperator_localReps V β Λ 1 L hc' (pl P) h1 hoff (splitLab V.rank k) (Comparison₂.hx (P, k)) (Comparison₂.hA (P, k)) (hs 1).2.2
      ((hs _).1 hk (Comparison₂.hx_ok _ hi)) (fun a ha => (hs a).2.1 (Comparison₂.hA_loc _ hi a ha)) (Comparison₂.hDC _ hi)
    exact (Comparison₂.op_eq _ hi f).trans (hd.2 W _ hinv)

theorem split_ops : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → (∀ t h, IsOpsX R t h → ∀ (P : A.ok t) k, k ≤ D.sp.X'.rank → ∀ f, R.jX t (A.heckeR t (P, k) f) = h (R.pl P) (Finsupp.single (splitLab D.sp.X'.rank k) 1) (R.jX t f)) ∧ ∀ j t h, IsOpsV R j t h → ∀ (P : A.ok t) k, k ≤ (Vc D j).rank → ∀ f, R.jV j t (A.heckeL j t (P, k) f) = h (R.pl P) (Finsupp.single (splitLab (Vc D j).rank k) 1) (R.jV j t f) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL hF hM
  have hgood : ∀ t (P : A.ok t), Good R t (R.pl P) := fun t P => ((GlobalTheory.T.theta_lift_levels_good_primes_properties R F hL).2.2.2 hF t P P.2).1
  refine ⟨fun t h hh P k hk f => ?_, fun j t h hh P k hk f => ?_⟩
  · have hd := side_label D.sp.X' R.βX R.ΛX (R.datXt t) hL.βX (R.B.R t).pres R.pl (A.ok t) (A.heckeR t) (R.B.R t).hecke
      P (hF.degR t P).1 (hgood t P) k hk f
    refine (hM.HX t).1 ?_
    refine (hM.jX t _).trans (Eq.trans ?_ (hh _ (hgood t P) _ _).symm)
    exact hd.trans (congrArg (hkF D.sp.X' (R.pl P) (Finsupp.single (splitLab D.sp.X'.rank k) 1)) (hM.jX t f).symm)
  · have hd := side_label (Vc D j) (R.βV j) (R.ΛV j) (R.datVt j t) (hL.βV j) (R.B.L j t).pres R.pl (A.ok t) (A.heckeL j t)
      (R.B.L j t).hecke P (hF.degL j t P).1 (hgood t P) k hk f
    refine (hM.HV j t).1 ?_
    refine (hM.jV j t _).trans (Eq.trans ?_ (hh _ (hgood t P) _ _).symm)
    exact hd.trans (congrArg (hkF (Vc D j) (R.pl P) (Finsupp.single (splitLab (Vc D j).rank k) 1)) (hM.jV j t f).symm)

end GlobalTheory.SplitHeckeLabel

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FamilySplitOperatorsEqLabelOperatorsModelsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.familySplitOperators_eq_labelOperators_models : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → (∀ t h, IsOpsX R t h → ∀ (P : A.ok t) k, k ≤ D.sp.X'.rank → ∀ f, R.jX t (A.heckeR t (P, k) f) = h (R.pl P) (Finsupp.single (splitLab D.sp.X'.rank k) 1) (R.jX t f)) ∧ ∀ j t h, IsOpsV R j t h → ∀ (P : A.ok t) k, k ≤ (Vc D j).rank → ∀ f, R.jV j t (A.heckeL j t (P, k) f) = h (R.pl P) (Finsupp.single (splitLab (Vc D j).rank k) 1) (R.jV j t f) := by
  first | exact @GlobalTheory.SplitHeckeLabel.split_ops | exact GlobalTheory.SplitHeckeLabel.split_ops | (intros; apply GlobalTheory.SplitHeckeLabel.split_ops <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitarySphericalComponentOfReading
noncomputable section

namespace GlobalTheory.SplitRead

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL
  GlobalTheory.SplitWeil GlobalTheory.RowTie

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end GlobalTheory.SplitRead
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilRepEquivOfCharpolyEq
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilRepEquivOfCharpolyEq
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding IsPlaceOver G
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AboveL

theorem weil_rep_equiv_of_charpoly_eq : ∀ (K Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (h : IsPlaceOver A v) (n m : ℕ) (a : WDRep h (Fin n → ℂ)) (b : WDRep h (Fin m → ℂ)), (∀ σ : Weil h, (a.ρ σ).charpoly = (b.ρ σ).charpoly) → ∃ e : (Fin n → ℂ) ≃ₗ[ℂ] (Fin m → ℂ), ∀ σ z, e (a.ρ σ z) = b.ρ σ (e z) := by
  intro K Ω _ _ _ _ _ A v h n m a b hc
  have ha := (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule a.ρ).1
    (GlobalTheory.WeilDeligne.WDRep.isSemisimpleRepresentation_rho K Ω A v h n a)
  have hb := (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule b.ρ).1
    (GlobalTheory.WeilDeligne.WDRep.isSemisimpleRepresentation_rho K Ω A v h m b)
  obtain ⟨e, he⟩ := Formalism.IrreducibleCountingLemmas.Z.brauer_nesbitt ℂ (Weil h) _ _ a.ρ b.ρ ha hb hc
  exact ⟨e, fun σ z => LinearMap.congr_fun (he σ) z⟩

end GlobalTheory.AboveL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilRepEquivOfCharpolyEqStatement
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding IsPlaceOver G
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRep_equiv_of_charpoly_eq : ∀ (K Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (h : IsPlaceOver A v) (n m : ℕ) (a : WDRep h (Fin n → ℂ)) (b : WDRep h (Fin m → ℂ)), (∀ σ : Weil h, (a.ρ σ).charpoly = (b.ρ σ).charpoly) → ∃ e : (Fin n → ℂ) ≃ₗ[ℂ] (Fin m → ℂ), ∀ σ z, e (a.ρ σ z) = b.ρ σ (e z) := by
  first | exact @GlobalTheory.AboveL.weil_rep_equiv_of_charpoly_eq | exact GlobalTheory.AboveL.weil_rep_equiv_of_charpoly_eq | (intros; apply GlobalTheory.AboveL.weil_rep_equiv_of_charpoly_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeFactsAt
noncomputable section

namespace GlobalTheory.ColPeriod

open NumberField IsDedekindDomain Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recSeam HostTie AnTie)
open GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint (WtCompat InDeg LatWithBasis)

def JetOpWeyl : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (ι : Type) [Fintype ι] (a b : ℕ) (hab : a < b)
    (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (s s' : ι → ℤ) (n : ι → ℕ), WtCompat hab lam lam' s s' n →
    ∀ (M : ι → Submodule (𝓞 K) (Fin a → K)) (MW : ι → Submodule (𝓞 K) (Fin b → K)),
      (∀ τ, Submodule.IsLattice K (M τ)) → (∀ τ, Submodule.IsLattice K (MW τ)) → LatWithBasis w M 1 → LatWithBasis w MW 1 →
      ∀ (c : K) (J : (DVar ι a b →₀ ℕ) → K), (∀ m, InDeg lam s' m → w.valuation K (c * J m) ≤ 1) →
        ∀ F ∈ localization₂ w.asIdeal (delK lam fun τ => dualFr (M τ)),
          c • jetOp lam lam' J n F ∈ localization₂ w.asIdeal (delK lam' fun τ => dualFr (MW τ))

end GlobalTheory.ColPeriod
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RestrictsLpDimMono0CharPol
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding IsPlaceOver G
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AboveL

theorem restricts_lpDim_mono0_charPol : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω]
    [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L]
    [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L))
    (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (x : WD h) (x' : WD h'), Restricts x x' →
    x'.lpDim = x.lpDim ∧ (x'.mono0 ↔ x.mono0) ∧ ∀ (σ : Weil h) (σ' : Weil h'),
      (∀ z : Ω, (σ : G K Ω) z = (σ' : G L Ω) z) → x'.charPol σ' = x.charPol σ := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ A v v' h h' x x' hr
  obtain ⟨n, a, b, rfl, rfl, hN, hρ⟩ := hr
  refine ⟨by rw [WD.lpDim_mk, WD.lpDim_mk], by rw [WD.monodromyZero_ofWeilDeligneRepClass_iff, WD.monodromyZero_ofWeilDeligneRepClass_iff, hN], fun σ σ' hs => ?_⟩
  rw [WD.charPol_mk, WD.charPol_mk, hρ σ σ' hs]

end GlobalTheory.AboveL
end
