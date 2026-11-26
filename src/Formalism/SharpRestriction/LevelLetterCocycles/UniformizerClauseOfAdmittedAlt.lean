module

public import Formalism.SharpRestriction.LevelLetterCocycles.FirstLiftOfUniformizerClause
public import Formalism.SharpRestriction.LevelLetterCocycles.SecondLiftOfHypotheses
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalClauseOfFrobeniusHyps
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.LemKD
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.FilDimOf
public import Formalism.SharpRestriction.LevelLetterCocycles.CompleteMax
public import Formalism.SharpRestriction.LevelLetterCocycles.TruncationClauseOfLatticeHypotheses

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.ExtDataExtTool
section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.ExtDataOneMapSmulO
section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusMemPullbackOfInvariant
noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.Sh

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.LiftingTheory Formalism.MainNotions.CrystallineLiftingInputs

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem letE_mul_self_eq (i : ZMod n) : (letE i : LetA O n) * letE i = letE i := by
  unfold letE
  rw [← Pi.single_mul, mul_one]

theorem idempotent_smul_smul (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n)
    (x : W.DD T) : (letE i : LetA O n) • (letE i : LetA O n) • x = (letE i : LetA O n) • x := by
  rw [smul_smul, letE_mul_self_eq]

private theorem phiD_letA_smul_eq_phiA_smul_phiD (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)
    (a : LetA O n) (x : W.DD T) : W.φD T (a • x) = W.φA a • W.φD T x := by
  rw [← algebraMap_smul W.EE a x, W.φD_smul, W.φE_ext, algebraMap_smul] <;> rfl

private theorem phiA_letE_sub_one_eq_letE (W : LocWach PD LL O v n) (i : ZMod n) :
    W.φA (letE (i - 1) : LetA O n) = letE i := by
  funext j
  show W.φ₀ ((letE (i - 1) : LetA O n) (j - 1)) = (letE i : LetA O n) j
  by_cases h : j = i
  · subst h
    simp [letE]
  · have h' : j - 1 ≠ i - 1 := fun e => h (sub_left_inj.mp e)
    simp [letE, Pi.single_apply, h, h']

theorem frobenius_idempotent_shift (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (x : W.DD T) :
    W.φD T ((letE (i - 1) : LetA O n) • x) = (letE i : LetA O n) • W.φD T x := by
  rw [phiD_letA_smul_eq_phiA_smul_phiD, phiA_letE_sub_one_eq_letE]

private theorem letGamma_letE_eq_letE (W : LocWach PD LL O v n) (g : W.Gam) (i : ZMod n) :
    letγ (W.γ₀ g) (letE i : LetA O n) = letE i := by
  funext j
  show W.γ₀ g ((letE i : LetA O n) j) = (letE i : LetA O n) j
  by_cases h : j = i
  · subst h
    simp [letE]
  · simp [letE, Pi.single_apply, h]

theorem gammaD_idempotent_smul (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (g : W.Gam) (i : ZMod n)
    (x : W.DD T) : W.γD T g ((letE i : LetA O n) • x) = (letE i : LetA O n) • W.γD T g x := by
  rw [← algebraMap_smul W.EE (letE i : LetA O n) x, W.γD_smul, W.γE_ext, algebraMap_smul,
    letGamma_letE_eq_letE]

theorem natCast_pow_smul_eq_algebra (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (N : ℕ) (x : W.DD T) :
    ((PD.p : ℕ) : O) ^ N • x = ((PD.p : ℕ) : LetA O n) ^ N • x := by
  rw [← algebraMap_smul (LetA O n) (((PD.p : ℕ) : O) ^ N) x, map_pow, map_natCast]

theorem frobeniusA_natCast_pow (W : LocWach PD LL O v n) (N : ℕ) :
    W.φA (((PD.p : ℕ) : LetA O n) ^ N) = ((PD.p : ℕ) : LetA O n) ^ N := by
  rw [map_pow, map_natCast]

theorem gammaA_natCast_pow (W : LocWach PD LL O v n) (g : W.Gam) (N : ℕ) :
    W.γA g (((PD.p : ℕ) : LetA O n) ^ N) = ((PD.p : ℕ) : LetA O n) ^ N := by
  rw [map_pow, map_natCast]

theorem basis_vector_eq_zero_or_torsionFree (W : LocWach PD LL O v n) (e : W.DD W.one)
    (hspan : W.N W.one = Submodule.span (LetA O n) {e}) (π' : LetA O n)
    (hm : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W W.one π') : e = 0 ∨ ∀ β : LetA O n, β • e = 0 → β = 0 := by
  obtain ⟨⟨r, b, hb, huniq, -⟩, -⟩ := hm
  by_cases he : e = 0
  · exact Or.inl he
  right
  intro β hβ
  have heN : e ∈ W.N W.one := by
    rw [hspan]
    exact Submodule.mem_span_singleton_self e
  have hkill : ∀ y ∈ W.N W.one, β • y = 0 := by
    intro y hy
    rw [hspan] at hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [smul_smul, mul_comm, ← smul_smul, hβ, smul_zero]
  obtain ⟨a, ha, hu⟩ := huniq e heN
  have hr : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · subst h0
      exact (he (by simpa using ha)).elim
    · exact h0
  have hz : ∑ j, β • b j = 0 := Finset.sum_eq_zero fun j _ => hkill _ (hb j).1
  have h2 : e = ∑ j, (a j + β) • b j := by
    simp only [add_smul, Finset.sum_add_distrib]
    rw [← ha, hz, add_zero]
  have h3 := congrFun (hu (fun j => a j + β) h2) ⟨0, hr⟩
  simpa using h3

theorem eq_zero_of_natCast_pow_mul (hζ : ∃ ζ : LL, IsPrimitiveRoot ζ PD.p)
    (hO : ∃ _ : IsDomain O, IsDiscreteValuationRing O ∧ IsFractionRing O LL) (N : ℕ) (β : LetA O n)
    (h : ((PD.p : ℕ) : LetA O n) ^ N * β = 0) : β = 0 := by
  obtain ⟨hd, -, hf⟩ := hO
  haveI := hd
  haveI : NeZero PD.p := ⟨PD.hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := hζ
  have hLL : ((PD.p : ℕ) : LL) ≠ 0 := hζ.neZero'.out
  have hpO : ((PD.p : ℕ) : O) ≠ 0 := by
    intro h0
    apply hLL
    rw [← map_natCast (algebraMap O LL), h0, map_zero]
  have hpS : ((PD.p : ℕ) : PowerSeries O) ≠ 0 := by
    intro h0
    apply hpO
    have h1 := congrArg PowerSeries.constantCoeff h0
    rwa [map_natCast, map_zero] at h1
  funext j
  have hj := congrFun h j
  simp only [Pi.mul_apply, Pi.pow_apply, Pi.natCast_apply, Pi.zero_apply] at hj
  rcases mul_eq_zero.mp hj with h1 | h1
  · exact ((pow_ne_zero N hpS) h1).elim
  · exact h1

theorem frobenius_mem_pullback_of_invariant (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (π' : LetA O n)
    (hm : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T π') (i : ZMod n) (t : W.DD T) (ht : t ∈ W.N T)
    (hl : (letE (i - 1) : LetA O n) • t = t) : W.φD T t ∈ pullJ W T (i - 1) 1 := by
  obtain ⟨⟨r, b, hb, huniq, -⟩, -⟩ := hm
  obtain ⟨a, ha, -⟩ := huniq t ht
  have ht' : t = ∑ j, a j • ((letE (i - 1) : LetA O n) • b j) := by
    calc t = (letE (i - 1) : LetA O n) • t := hl.symm
      _ = (letE (i - 1) : LetA O n) • ∑ j, a j • b j := by rw [← ha]
      _ = _ := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [smul_smul, smul_smul, mul_comm]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [ht', map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [phiD_letA_smul_eq_phiA_smul_phiD]
  apply Submodule.smul_mem
  unfold pullJ
  apply Submodule.subset_span
  refine ⟨(letE (i - 1) : LetA O n) • b j,
    ⟨(W.N T).smul_mem _ (hb j).1, idempotent_smul_smul W T (i - 1) (b j), fun δ hδ => ?_⟩, ?_⟩
  · rw [gammaD_idempotent_smul, (hb j).2 δ hδ]
  · simp

private theorem locWach_map_letA_smul_comm (W : LocWach PD LL O v n) {T Y : LocLat G Qp LL O}
    (f : LatHom T.L Y.L) (a : LetA O n) (x : W.DD T) : W.map f (a • x) = a • W.map f x := by
  rw [← algebraMap_smul W.EE a x, map_smul, algebraMap_smul]

theorem pullback_span_of_exact (W : LocWach PD LL O v n) {T Y : LocLat G Qp LL O} (ι : LatHom T.L Y.L)
    (π : LatHom Y.L W.one.L) (hY : IsCrys PD Y.ρ) (hO : IsCrys PD W.one.ρ)
    (hker : ∀ x, W.map π x = 0 ↔ ∃ y, W.map ι y = x) (hsat : ∀ x, W.map ι x ∈ W.N Y → x ∈ W.N T)
    (hinj : Function.Injective (W.map ι)) (π' : LetA O n) (hmT : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T π')
    (e' : W.DD W.one) (hspan : W.N W.one = Submodule.span (LetA O n) {e'}) (i : ZMod n) (N : ℕ)
    (ε : W.DD Y) (hεN : ε ∈ W.N Y)
    (hεπ : W.map π ε = ((PD.p : ℕ) : LetA O n) ^ N • (letE (i - 1) : LetA O n) • e') :
    ∀ x ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W Y (W.Nl Y (i - 1)), ∃ p ∈ pullJ W T (i - 1) 1, ∃ β : LetA O n,
      ((PD.p : ℕ) : LetA O n) ^ N • x = W.map ι p + β • W.φD Y ε ∧ (e' = 0 → β = 0) := by
  intro x hx
  unfold Formalism.MainNotions.DeltaInvariantLattices.φspan at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z0, hz0, rfl⟩ := hx
    obtain ⟨y, hy, rfl⟩ := (hz0 : z0 ∈ (W.N Y).map ((letE (i - 1) : LetA O n) • LinearMap.id))
    simp only [LinearMap.smul_apply, LinearMap.id_apply]
    set z : W.DD Y := (letE (i - 1) : LetA O n) • y with hzdef
    have hz_idem : (letE (i - 1) : LetA O n) • z = z := by
      rw [hzdef]
      exact idempotent_smul_smul W Y (i - 1) y
    have hzN : z ∈ W.N Y := (W.N Y).smul_mem _ hy
    have hπz := W.map_N π hY hO z hzN
    obtain ⟨c, hc, hc0⟩ : ∃ c : LetA O n, c • e' = W.map π z ∧ (e' = 0 → c = 0) := by
      by_cases he : e' = 0
      · rw [hspan, he, Submodule.span_zero_singleton, Submodule.mem_bot] at hπz
        exact ⟨0, by rw [zero_smul, hπz], fun _ => rfl⟩
      · rw [hspan] at hπz
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hπz
        exact ⟨c, hc, fun h => (he h).elim⟩
    have hπlet : W.map π z = (letE (i - 1) : LetA O n) • W.map π z := by
      rw [← locWach_map_letA_smul_comm, hz_idem]
    have hce : c • e' = ((letE (i - 1) : LetA O n) * c) • e' := by
      rw [← smul_smul, hc]
      exact hπlet
    have hw : W.map π (((PD.p : ℕ) : LetA O n) ^ N • z - c • ε) = 0 := by
      rw [map_sub, locWach_map_letA_smul_comm W π _ z, locWach_map_letA_smul_comm W π c ε, hεπ, ← hc, hce]
      simp only [smul_smul]
      rw [sub_eq_zero]
      congr 1
      ring
    obtain ⟨y', hy'⟩ := (hker _).mp hw
    have hι : W.map ι ((letE (i - 1) : LetA O n) • y') =
        ((PD.p : ℕ) : LetA O n) ^ N • z - c • ((letE (i - 1) : LetA O n) • ε) := by
      rw [locWach_map_letA_smul_comm, hy', smul_sub, smul_comm (letE (i - 1) : LetA O n) _ z, hz_idem,
        smul_comm (letE (i - 1) : LetA O n) c ε]
    have hyN : (letE (i - 1) : LetA O n) • y' ∈ W.N T := by
      apply hsat
      rw [hι]
      exact sub_mem ((W.N Y).smul_mem _ hzN) ((W.N Y).smul_mem _ ((W.N Y).smul_mem _ hεN))
    have hp := frobenius_mem_pullback_of_invariant W T π' hmT i _ hyN (idempotent_smul_smul W T (i - 1) y')
    have e1 : W.φD Y (((PD.p : ℕ) : LetA O n) ^ N • z) = ((PD.p : ℕ) : LetA O n) ^ N • W.φD Y z := by
      rw [phiD_letA_smul_eq_phiA_smul_phiD, frobeniusA_natCast_pow]
    have e2 : W.φD Y (c • (letE (i - 1) : LetA O n) • ε) =
        (W.φA c * (letE i : LetA O n)) • W.φD Y ε := by
      rw [phiD_letA_smul_eq_phiA_smul_phiD, frobenius_idempotent_shift, smul_smul]
    refine ⟨_, hp, W.φA c * (letE i : LetA O n), ?_, fun h => by rw [hc0 h, map_zero, zero_mul]⟩
    rw [W.map_φ, hι, map_sub, e1, e2, sub_add_cancel]
  | zero => exact ⟨0, Submodule.zero_mem _, 0, by simp, fun _ => rfl⟩
  | add a b _ _ ha hb =>
    obtain ⟨q1, hq1, β1, h11, h21⟩ := ha
    obtain ⟨q2, hq2, β2, h12, h22⟩ := hb
    refine ⟨q1 + q2, Submodule.add_mem _ hq1 hq2, β1 + β2, ?_, fun h => by rw [h21 h, h22 h, add_zero]⟩
    rw [smul_add, h11, h12, map_add (f := _), add_smul]
    abel
  | smul c a _ ha =>
    obtain ⟨q, hq, β, h1, h2⟩ := ha
    refine ⟨c • q, Submodule.smul_mem _ _ hq, c * β, ?_, fun h => by rw [h2 h, mul_zero]⟩
    rw [smul_comm, h1, smul_add, locWach_map_letA_smul_comm, smul_smul]

end Formalism.MainNotions.RamifiedCoefficientChains.Sh

end
end

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.Sh

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.LiftingTheory Formalism.MainNotions.CrystallineLiftingInputs

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def extDataOne_Rel (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (Mi hi : ZMod n → ℕ) (a N : ℕ)
    (y z : W.DD T) (μ ν : ZMod n → W.DD T) : Prop :=
  ∀ i : ZMod n, DL W T i (μ i) ∧ DL W T i (ν i) ∧
    InPN W T 1 (((PD.p : ℕ) : O) ^ N • ((letE i : LetA O n) • z) + (W.γ T (μ i) - μ i)) ∧
    qp W ^ Mi i • (((PD.p : ℕ) : O) ^ N • ((letE i : LetA O n) • y) + W.φD T (μ (i - 1)) - μ i) ∈ W.N T ∧
    (∃ s : ℕ, ((PD.p : ℕ) : O) ^ s • (qp W ^ hi i •
      (((PD.p : ℕ) : O) ^ N • ((letE i : LetA O n) • y) + W.φD T (μ (i - 1)) - μ i)) ∈
        pullJ W T (i - 1) 1) ∧
    ((PD.p : ℕ) : O) ^ N • ν i - qp W ^ a • μ i ∈ W.N T

theorem extDataOne_π₀_cancel (W : LocWach PD LL O v n) (R : lifta_Ring W) {T : LocLat G Qp LL O}
    (x : W.DD T) (h : W.π₀ • x = 0) : x = 0 := by
  apply (liftb_unit_bij W T W.π₀ R.πU).1
  change W.π₀ • x = W.π₀ • (0 : W.DD T)
  rw [smul_zero]
  exact h

theorem extDataOne_Qqp (W : LocWach PD LL O v n) (R : lifta_Ring W) (hs : W.s = 1) {T : LocLat G Qp LL O}
    (S : Submodule (LetA O n) (W.DD T)) (M : ℕ) (x : W.DD T) (h : W.Q ^ M • x ∈ S) : qp W ^ M • x ∈ S := by
  obtain ⟨w, hw⟩ := R.qq
  rw [lifta_Q_eq W hs, hw, mul_pow, mul_smul] at h
  have h' := S.smul_mem ((↑(w⁻¹) : LetA O n) ^ M) h
  rwa [← mul_smul, ← mul_pow, Units.inv_mul, one_pow, one_smul] at h'

theorem extDataOne_mem_Nl (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (x : W.DD T)
    (hx : x ∈ W.N T) (hl : (letE i : LetA O n) • x = x) : x ∈ W.Nl T i :=
  hl ▸ liftb_letE_mem W T i hx

theorem extDataOne_exists [NeZero n] (W : LocWach PD LL O v n)
    (hH : Formalism.MainNotions.ElementDenominator.coreHerrExtΔ W) (hExt : liftb_HExt W) (hOne : liftb_HOne W)
    (hEx : ∀ (T₀ T₁ T₂ : LocLat G Qp LL O) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L),
      IsSESLat (Qp := Qp) (O := O) ι π → Function.Injective (W.map ι) ∧ Function.Surjective (W.map π) ∧
        ∀ x, W.map π x = 0 ↔ ∃ y, W.map ι y = x)
    (hdex : W.DelF.card = PD.p - 1 → ∃ d : O, d * (W.DelF.card : O) = 1)
    (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (h6 : Formalism.MainNotions.DeltaInvariantLattices.WachSaturationExactness W) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hA : CaseA W) (hζ : ∃ ζ : LL, IsPrimitiveRoot ζ PD.p)
    (hOd : ∃ _ : IsDomain O, IsDiscreteValuationRing O ∧ IsFractionRing O LL)
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (Mi hi : ZMod n → ℕ) (a N : ℕ)
    (hJY : ∀ (Y : LocLat G Qp LL O) (ι : LatHom T.L Y.L) (π : LatHom Y.L W.one.L),
      IsSESLat (Qp := Qp) (O := O) ι π → IsCrys PD Y.ρ → Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W Y Mi hi)
    (hK : ∀ (Y : LocLat G Qp LL O) (ι : LatHom T.L Y.L) (π : LatHom Y.L W.one.L),
      IsSESLat (Qp := Qp) (O := O) ι π → IsCrys PD Y.ρ → ∀ i : ZMod n,
        Kills W π i (lp W N) ∧ Kills W π i (qp W ^ a))
    (c : G → T.V) (hc : c ∈ latticeFiniteCocycles PD T.L) :
    ∃ (y z : W.DD T) (μ ν : ZMod n → W.DD T) (h : (y, z) ∈ W.wachCocyclesDelta T) (hc' : c ∈ latticeCocycles T.L),
      W.clK T ⟨(y, z), h⟩ = Submodule.Quotient.mk (⟨c, hc'⟩ : ↥(latticeCocycles T.L)) ∧
        extDataOne_Rel W T Mi hi a N y z μ ν := by
  have hs : W.s = 1 := hA.2.1
  have hp2 : PD.p ≠ 2 := hA.2.2
  have hgK : W.gamK = W.gam := W.gamK_eq_one hs hp2
  have hcard : W.DelF.card = PD.p - 1 := by
    rw [(h9 T hT hs hp2).1, finrank_eq_one_case_A W hA, Nat.div_one]
  obtain ⟨d, hd⟩ := hdex hcard
  have hcZ : c ∈ latticeCocycles T.L := (Submodule.mem_inf.1 hc).1
  obtain ⟨Y, ι, π, hY, hext⟩ := hExt T c hT hc
  obtain ⟨hOc, -, e, he, hspan, hφe, hγe⟩ := hOne
  have hses := hext.1
  obtain ⟨hinj, hsurj, hker⟩ := hEx T Y W.one ι π hses
  have hsat : ∀ x, W.map ι x ∈ W.N Y → x ∈ W.N T := (h6.2.2 T Y W.one ι π hT hY hOc hses).2.2.2.1
  have hπι : ∀ x, W.map π (W.map ι x) = 0 := fun x => (hker _).2 ⟨x, rfl⟩
  obtain ⟨u, hu⟩ := hH hs hp2 T Y ι π hT hY c hcZ hext e ⟨hspan, hφe, hγe⟩
  obtain ⟨h9T, hmT⟩ := uniformizer_ring_and_module_clauses W h9 hA T hT
  obtain ⟨-, hmY⟩ := uniformizer_ring_and_module_clauses W h9 hA Y hY
  obtain ⟨-, hmO⟩ := uniformizer_ring_and_module_clauses W h9 hA W.one hOc
  have R := lifta_ring_of W h9T
  have hqΔ : qp W ∈ W.AΔ := lifta_qΔ W R.πΔ
  have hγdef : ∀ (T' : LocLat G Qp LL O) (x : W.DD T'), W.γ T' x = W.γD T' W.gam x := fun _ _ => rfl

  obtain ⟨e', he'd⟩ : ∃ e' : W.DD W.one, e' = ((u⁻¹ : Oˣ) : O) • e := ⟨_, rfl⟩
  have hφe' : W.φD W.one e' = e' := by rw [he'd, map_smul, hφe]
  have hγe' : ∀ g, W.γD W.one g e' = e' := fun g => by rw [he'd, map_smul, hγe]
  have hspan' : W.N W.one = Submodule.span (LetA O n) {e'} := by
    rw [hspan, he'd, ← algebraMap_smul (LetA O n) ((u⁻¹ : Oˣ) : O) e,
      Submodule.span_singleton_smul_eq ((u⁻¹).isUnit.map (algebraMap O (LetA O n)))]

  obtain ⟨X₀, hX₀⟩ := hsurj e'
  obtain ⟨X, hXd⟩ : ∃ X : W.DD Y, X = lifta_avg W Y d X₀ := ⟨_, rfl⟩
  have hXΔ : ∀ δ ∈ W.DelF, W.γD Y δ X = X := by rw [hXd]; exact lifta_avg_inv W Y d X₀
  have hXπ : W.map π X = e' := by
    rw [hXd, lifta_avg_map, hX₀]; exact lifta_avg_fix W W.one d hd e' (fun δ _ => hγe' δ)
  have hφX : W.map π (W.φD Y X - X) = 0 := by rw [map_sub, W.map_φ, hXπ, hφe', sub_self]
  have hγX : W.map π (W.γD Y W.gamK X - X) = 0 := by rw [map_sub, W.map_γ, hXπ, hγe', sub_self]
  obtain ⟨y, hy⟩ := (hker _).1 hφX
  obtain ⟨z, hz⟩ := (hker _).1 hγX
  have hz' : W.map ι z = W.γD Y W.gam X - X := by rw [hz, hgK]
  have hyΔ : ∀ δ ∈ W.DelF, W.γD T δ y = y := fun δ hδ => hinj (by
    rw [W.map_γ, hy, map_sub, ← W.φγ_comm, hXΔ δ hδ])
  have hzΔ : ∀ δ ∈ W.DelF, W.γD T δ z = z := fun δ hδ => hinj (by
    rw [W.map_γ, hz, map_sub, ← W.γD_mul, mul_comm, W.γD_mul, hXΔ δ hδ])
  have hcoc : (W.γD T W.gam y - y) - (W.φD T z - z) = 0 := hinj (by
    simp only [map_sub, W.map_γ, W.map_φ, hy, hz', W.φγ_comm, map_zero]
    abel)
  have hZ : (y, z) ∈ W.wachCocyclesDelta T := by
    rw [lifta_mem_Z1DΔ]
    refine ⟨?_, fun δ hδ => ⟨hyΔ δ hδ, hzΔ δ hδ⟩⟩
    rw [hgK]
    exact (liftb_mem_Z1D W T y z).2 hcoc
  have hcl : W.clK T ⟨(y, z), hZ⟩ = Submodule.Quotient.mk (⟨c, hcZ⟩ : ↥(latticeCocycles T.L)) := by
    rw [hu X ((u⁻¹ : Oˣ) : O) hXΔ (by rw [hXπ, he'd]) y z hZ hy hz, Units.mul_inv, one_smul]

  have he'N : e' ∈ W.N W.one := by
    rw [hspan']
    exact Submodule.mem_span_singleton_self e'
  have hKY := hK Y ι π hses hY
  have hlift : ∀ (i : ZMod n) (b : LetA O n), Kills W π i b → b ∈ W.AΔ →
      ∃ ε : W.DD Y, ε ∈ W.NΔ Y ∧ (letE i : LetA O n) • ε = ε ∧
        W.map π ε = b • (letE i : LetA O n) • e' := by
    intro i b hb hbΔ
    have hy0 : (letE i : LetA O n) • e' ∈ W.Nl W.one i :=
      extDataOne_mem_Nl W W.one i _ ((W.N W.one).smul_mem _ he'N) (idempotent_smul_smul W W.one i e')
    obtain ⟨ε₀, hε₀, hε₀π⟩ := Submodule.mem_map.1 (hb _ hy0)
    obtain ⟨m0, hm0, hm0e⟩ := Submodule.mem_map.1 hε₀
    have hε₀e : ε₀ = (letE i : LetA O n) • m0 := by
      rw [← hm0e, LinearMap.smul_apply (letE i : LetA O n) (LinearMap.id : W.DD Y →ₗ[LetA O n] W.DD Y) m0,
        LinearMap.id_apply]
    have h1 : W.map π ε₀ = b • (letE i : LetA O n) • e' := hε₀π
    refine ⟨lifta_avg W Y d ε₀, lifta_avg_N W Y d ε₀ (by rw [hε₀e]; exact (W.N Y).smul_mem _ hm0), ?_, ?_⟩
    · rw [← lifta_avg_smul W Y d _ (fun δ _ => gammaA_letter_idempotent W δ i), hε₀e, idempotent_smul_smul]
    · rw [lifta_avg_map, h1]
      refine lifta_avg_fix W W.one d hd _ (fun δ hδ => ?_)
      rw [gammaD_semilinear, hbΔ δ hδ, gammaD_idempotent_smul, hγe']
  have hlpΔ : lp W N ∈ W.AΔ := fun δ _ => gammaA_natCast_pow W δ N
  choose ε hεΔ hεl hεπ using fun i => hlift i (lp W N) (hKY i).1 hlpΔ
  choose x' hx'Δ hx'l hx'π using fun i => hlift i (qp W ^ a) (hKY i).2 (W.AΔ.pow_mem hqΔ a)
  have hεπ'' : ∀ j, W.map π (ε j) = ((PD.p : ℕ) : LetA O n) ^ N • (letE j : LetA O n) • e' := hεπ

  have hμex : ∀ i, ∃ m : W.DD T, W.map ι m = ε i - ((PD.p : ℕ) : LetA O n) ^ N • (letE i : LetA O n) • X :=
    fun i => (hker _).1 (by rw [map_sub, liftb_map_smul, liftb_map_smul, hXπ, hεπ'' i, sub_self])
  have hνex : ∀ i, ∃ m : W.DD T, W.map ι m = x' i - qp W ^ a • (letE i : LetA O n) • X := fun i =>
    (hker _).1 (by rw [map_sub, liftb_map_smul, liftb_map_smul, hXπ, hx'π i, sub_self])
  choose μ hμ using hμex
  choose ν hν using hνex
  refine ⟨y, z, μ, ν, hZ, hcZ, hcl, fun i => ?_⟩
  have hY5 := h5 Y Mi hi hY (hJY Y ι π hses hY)
  have hεNl : ∀ j, ε j ∈ W.Nl Y j := fun j => extDataOne_mem_Nl W Y j _ (hεΔ j).1 (hεl j)
  have hqaΔ : ∀ δ ∈ W.DelF, W.γA δ (qp W ^ a) = qp W ^ a := W.AΔ.pow_mem hqΔ a

  have hDLμ : DL W T i (μ i) := by
    refine ⟨hinj ?_, fun δ hδ => hinj ?_⟩
    · rw [liftb_map_smul, hμ i, smul_sub, hεl i,
        smul_comm (letE i : LetA O n) (((PD.p : ℕ) : LetA O n) ^ N), idempotent_smul_smul]
    · rw [W.map_γ, hμ i, map_sub, gammaD_semilinear, gammaA_natCast_pow, gammaD_idempotent_smul, hXΔ δ hδ,
        (hεΔ i).2 δ hδ]
  have hDLν : DL W T i (ν i) := by
    refine ⟨hinj ?_, fun δ hδ => hinj ?_⟩
    · rw [liftb_map_smul, hν i, smul_sub, hx'l i, smul_comm (letE i : LetA O n) (qp W ^ a),
        idempotent_smul_smul]
    · rw [W.map_γ, hν i, map_sub, gammaD_semilinear, hqaΔ δ hδ, gammaD_idempotent_smul, hXΔ δ hδ, (hx'Δ i).2 δ hδ]

  have h3 : InPN W T 1 (((PD.p : ℕ) : O) ^ N • ((letE i : LetA O n) • z) + (W.γ T (μ i) - μ i)) := by
    obtain ⟨w, hw, hwe⟩ := hmY.2 (ε i) (hεΔ i)
    have hπw : W.map π w = 0 := by
      apply extDataOne_π₀_cancel W R
      rw [← liftb_map_smul, ← hwe, map_sub, hγdef, W.map_γ, hεπ'' i, gammaD_semilinear, gammaA_natCast_pow,
        gammaD_idempotent_smul, hγe', sub_self]
    obtain ⟨t, ht⟩ := (hker _).1 hπw
    have htN : t ∈ W.N T := hsat t (by rw [ht]; exact hw.1)
    have htΔ : ∀ δ ∈ W.DelF, W.γD T δ t = t := fun δ hδ => hinj (by rw [W.map_γ, ht, hw.2 δ hδ])
    refine ⟨t, htN, htΔ, hinj ?_⟩
    rw [pow_one, liftb_map_smul W ι W.π₀ t, ht, ← hwe]
    simp only [natCast_pow_smul_eq_algebra W T N, map_add (f := _), map_sub, liftb_map_smul, hγdef, W.map_γ, hz', hμ i,
      gammaD_semilinear, gammaA_natCast_pow, gammaA_letter_idempotent, smul_sub]
    abel

  have hw4 : W.map ι (((PD.p : ℕ) : O) ^ N • ((letE i : LetA O n) • y) + W.φD T (μ (i - 1)) - μ i) =
      W.φD Y (ε (i - 1)) - ε i := by
    simp only [natCast_pow_smul_eq_algebra W T N, map_add (f := _), map_sub, liftb_map_smul, W.map_φ, hy, hμ, liftb_φ_smul,
      frobeniusA_natCast_pow, wmap_φA_letE, smul_sub]
    abel
  have h4 : qp W ^ Mi i • (((PD.p : ℕ) : O) ^ N • ((letE i : LetA O n) • y) + W.φD T (μ (i - 1)) - μ i) ∈
      W.N T := hsat _ (by
    rw [liftb_map_smul, hw4, smul_sub]
    exact sub_mem (extDataOne_Qqp W R hs _ _ _ (hY5.1 i _ (hεNl (i - 1))))
      ((W.N Y).smul_mem _ (hεΔ i).1))
  have h5' : ∃ s : ℕ, ((PD.p : ℕ) : O) ^ s • (qp W ^ hi i •
      (((PD.p : ℕ) : O) ^ N • ((letE i : LetA O n) • y) + W.φD T (μ (i - 1)) - μ i)) ∈
        pullJ W T (i - 1) 1 := by
    refine ⟨N, ?_⟩
    have hxY : qp W ^ hi i • (W.φD Y (ε (i - 1)) - ε i) ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W Y (W.Nl Y (i - 1)) := by
      rw [smul_sub]
      exact sub_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨ε (i - 1), hεNl (i - 1), rfl⟩))
        (extDataOne_Qqp W R hs _ _ _ (hY5.2.1 i _ (hεNl i)))
    obtain ⟨p, hp, β, hβe, hβ0⟩ := pullback_span_of_exact W ι π hY hOc hker hsat hinj W.π₀ hmT e' hspan' i N
      (ε (i - 1)) (hεΔ (i - 1)).1 (hεπ'' (i - 1)) _ hxY
    have hβz : β • W.φD Y (ε (i - 1)) = 0 := by
      have hπ0 : W.map π (((PD.p : ℕ) : LetA O n) ^ N • (qp W ^ hi i • (W.φD Y (ε (i - 1)) - ε i))) = 0 := by
        rw [← hw4, ← liftb_map_smul, ← liftb_map_smul, hπι]
      rw [hβe, map_add (f := _), hπι, zero_add, liftb_map_smul, W.map_φ, hεπ'' (i - 1), liftb_φ_smul,
        frobeniusA_natCast_pow, frobenius_idempotent_shift, hφe', smul_smul, smul_smul] at hπ0
      by_cases he'0 : e' = 0
      · rw [hβ0 he'0, zero_smul]
      · have h1 := (basis_vector_eq_zero_or_torsionFree W e' hspan' W.π₀ hmO).resolve_left he'0 _ hπ0
        have h2 : β * (letE i : LetA O n) = 0 := eq_zero_of_natCast_pow_mul hζ hOd N _ (by rw [← h1]; ring)
        have h3 : W.φD Y (ε (i - 1)) = (letE i : LetA O n) • W.φD Y (ε (i - 1)) := by
          conv_lhs => rw [← hεl (i - 1)]
          exact frobenius_idempotent_shift W Y i _
        rw [h3, smul_smul, h2, zero_smul]
    have hfin : W.map ι (((PD.p : ℕ) : O) ^ N • (qp W ^ hi i •
        (((PD.p : ℕ) : O) ^ N • ((letE i : LetA O n) • y) + W.φD T (μ (i - 1)) - μ i))) = W.map ι p := by
      rw [natCast_pow_smul_eq_algebra W T N (qp W ^ hi i • _), liftb_map_smul, liftb_map_smul, hw4, hβe, hβz, add_zero]
    rw [hinj hfin]
    exact hp
  have h6' : ((PD.p : ℕ) : O) ^ N • ν i - qp W ^ a • μ i ∈ W.N T := hsat _ (by
    rw [natCast_pow_smul_eq_algebra W T N, map_sub, liftb_map_smul, liftb_map_smul, hν i, hμ i, smul_sub, smul_sub,
      smul_comm (((PD.p : ℕ) : LetA O n) ^ N) (qp W ^ a) ((letE i : LetA O n) • X), sub_sub_sub_cancel_right]
    exact sub_mem ((W.N Y).smul_mem _ (hx'Δ i).1) ((W.N Y).smul_mem _ (hεΔ i).1))
  exact ⟨hDLμ, hDLν, h3, h4, h5', h6'⟩

end Formalism.MainNotions.RamifiedCoefficientChains.Sh

end
end

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.Sh

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.LiftingTheory Formalism.MainNotions.CrystallineLiftingInputs

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem extData_win (d : ℕ) (b : ZMod n → ℕ) (S η : ℕ) (i : ZMod n) (hηb : η ≤ b i) :
    Formalism.MainNotions.RamifiedCoefficientChains.JumpWinS d b S η i ⊆
      Set.Icc (-(Formalism.MainNotions.RamifiedCoefficientChains.MiW d b S η i : ℤ)) (Formalism.MainNotions.RamifiedCoefficientChains.hiW d b S η i : ℤ) := by
  intro x hx
  unfold Formalism.MainNotions.RamifiedCoefficientChains.JumpWinS at hx
  unfold Formalism.MainNotions.RamifiedCoefficientChains.MiW Formalism.MainNotions.RamifiedCoefficientChains.hiW
  split_ifs at hx ⊢ with h <;> simp only [Set.mem_union, Set.mem_Icc] at hx ⊢ <;> push_cast at hx ⊢ <;> omega

theorem extData_lin {FF M I : Type} [AddCommGroup FF] [Module O FF] [AddCommGroup M] [Module O M] [Fintype I]
    (P : M → Prop) (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y)) (hsmul : ∀ (c : O) x, P x → P (c • x))
    (bF : Module.Basis I O FF) (Φ : FF →ₗ[O] M) (h : ∀ j, P (Φ (bF j))) (f : FF) : P (Φ f) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← bF.sum_equivFun f, map_sum]
  exact Finset.sum_induction _ P hadd h0 fun j _ => by rw [map_smul]; exact hsmul _ _ (h j)

theorem extData_extTool [NeZero n] (W : LocWach PD LL O v n)
    (hH : Formalism.MainNotions.ElementDenominator.coreHerrExtΔ W) (hExt : Formalism.MainNotions.LiftingTheory.liftb_HExt W) (hOne : Formalism.MainNotions.LiftingTheory.liftb_HOne W)
    (hKer : Formalism.MainNotions.LiftingTheory.liftb_HKer W) (hJmp : Formalism.MainNotions.CrystallineLiftingBounds.coreJumps PD LL O)
    (hEx : ∀ (T₀ T₁ T₂ : LocLat G Qp LL O) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L),
      IsSESLat (Qp := Qp) (O := O) ι π → Function.Injective (W.map ι) ∧ Function.Surjective (W.map π) ∧
        ∀ x, W.map π x = 0 ↔ ∃ y, W.map ι y = x)
    (hdex : W.DelF.card = PD.p - 1 → ∃ d : O, d * (W.DelF.card : O) = 1)
    (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (h6 : Formalism.MainNotions.DeltaInvariantLattices.WachSaturationExactness W) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hQ : Formalism.MainNotions.CrystallineLiftingInputs.QTool W) :
    ExtTool W := by
  intro d T₁ T₂ F b S η m hS FF _ _ _ _ g
  have hS' := hS
  obtain ⟨hA, h11, -, hOd, hζ, hSur, hJ1, -, hab, -⟩ := hS
  have hηb : ∀ i, η ≤ b i := fun i => by
    have h0 := Formalism.MainNotions.RamifiedCoefficientChains.aR_nonneg PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η) (by omega)
    have h1 := hab i
    have h2 : (η : ℝ) ≤ (b i : ℝ) := by linarith
    exact_mod_cast h2
  set Mi := Formalism.MainNotions.RamifiedCoefficientChains.MiW d b S η with hMi
  set hi := Formalism.MainNotions.RamifiedCoefficientChains.hiW d b S η with hhi
  set a := ⌈Formalism.MainNotions.RamifiedCoefficientChains.aR PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η)⌉₊ with ha
  have c1 : IsCrys PD T₁.ρ := hSur.1
  have c2 : IsCrys PD T₂.ρ := hSur.2.1
  have hOc : IsCrys PD W.one.ρ := hOne.1
  have hJL1 : Formalism.MainNotions.LiftingTheory.JumpsLet W T₁ Mi hi := fun i τ hτ x hx => extData_win d b S η i (hηb i) (hJ1 i τ hτ x hx)
  obtain ⟨T₀, ι₀, hses₀, c0⟩ := hKer T₁ T₂ F hSur
  have hJY : ∀ (Y : LocLat G Qp LL O) (ι : LatHom T₂.L Y.L) (π : LatHom Y.L W.one.L),
      IsSESLat (Qp := Qp) (O := O) ι π → IsCrys PD Y.ρ → Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W Y Mi hi := by
    intro Y ι π hses hY τ i hτ x hx
    rcases (hJmp T₂ Y W.one ι π hses c2 hY hOc τ x).1 hx with h | h
    · exact hJL1 i τ hτ x ((hJmp T₀ T₁ T₂ ι₀ F hses₀ c0 c1 c2 τ x).2 (Or.inr h))
    · rw [hOne.2.1 τ x h]
      simp
  have hQ1 := (hQ d T₁ T₂ F b S η m Mi hi hS' hJL1).2
  set N := eWA PD.p (Hmax n Mi hi) with hN
  have hK : ∀ (Y : LocLat G Qp LL O) (ι : LatHom T₂.L Y.L) (π : LatHom Y.L W.one.L),
      IsSESLat (Qp := Qp) (O := O) ι π → IsCrys PD Y.ρ → ∀ i : ZMod n,
        Kills W π i (lp W N) ∧ Kills W π i (qp W ^ a) := fun Y ι π hses hY i =>
    ⟨(hQ1 Y ι π hses hY i).2.1, (hQ1 Y ι π hses hY i).2.2⟩

  let I := Module.Free.ChooseBasisIndex O FF
  let bF : Module.Basis I O FF := Module.Free.chooseBasis O FF
  have one := fun j : I => extDataOne_exists W hH hExt hOne hEx hdex h5 h6 h9 hA hζ hOd T₂ c2 Mi hi a N
    hJY hK (g (bF j) : G → T₂.V) (g (bF j)).2
  choose yj zj μj νj hZj hcZj hclj hRelj using one
  let y : FF →ₗ[O] W.DD T₂ := bF.constr O yj
  let z : FF →ₗ[O] W.DD T₂ := bF.constr O zj
  let μ : ZMod n → FF →ₗ[O] W.DD T₂ := fun i => bF.constr O fun j => μj j i
  let ν : ZMod n → FF →ₗ[O] W.DD T₂ := fun i => bF.constr O fun j => νj j i
  have hyb : ∀ j, y (bF j) = yj j := fun j => bF.constr_basis O yj j
  have hzb : ∀ j, z (bF j) = zj j := fun j => bF.constr_basis O zj j
  have hμb : ∀ i j, μ i (bF j) = μj j i := fun i j => bF.constr_basis O (fun j => μj j i) j
  have hνb : ∀ i j, ν i (bF j) = νj j i := fun i j => bF.constr_basis O (fun j => νj j i) j
  refine ⟨N, y, z, μ, ν, fun f => ?_, fun i f => ?_⟩
  · have hκ : ((g f : ↥(latticeFiniteCocycles PD T₂.L)) : G → T₂.V) ∈ latticeCocycles T₂.L := (Submodule.mem_inf.1 (g f).2).1
    have hyf : y f = ∑ j, bF.equivFun f j • yj j := by simp [y, Module.Basis.constr_apply_fintype]
    have hzf : z f = ∑ j, bF.equivFun f j • zj j := by simp [z, Module.Basis.constr_apply_fintype]
    have hpair : ((y f, z f) : W.DD T₂ × W.DD T₂) = ∑ j, bF.equivFun f j • ((yj j, zj j) : W.DD T₂ × W.DD T₂) := by
      rw [hyf, hzf]
      ext <;> simp [Prod.fst_sum, Prod.snd_sum]
    have hmem : ((y f, z f) : W.DD T₂ × W.DD T₂) ∈ herrZ1Δ (W.γD T₂ W.gamK) (W.φD T₂) W.DelF (W.γD T₂) := by
      rw [hpair]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hZj j)
    refine ⟨⟨(y f, z f), hmem⟩, hκ, rfl, ?_⟩
    have hx : (⟨(y f, z f), hmem⟩ : ↥(herrZ1Δ (W.γD T₂ W.gamK) (W.φD T₂) W.DelF (W.γD T₂))) =
        ∑ j, bF.equivFun f j • (⟨(yj j, zj j), hZj j⟩ :
          ↥(herrZ1Δ (W.γD T₂ W.gamK) (W.φD T₂) W.DelF (W.γD T₂))) := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul]
      exact hpair
    have hsum : (⟨((g f : ↥(latticeFiniteCocycles PD T₂.L)) : G → T₂.V), hκ⟩ : ↥(latticeCocycles T₂.L)) =
        ∑ j, bF.equivFun f j • (⟨((g (bF j) : ↥(latticeFiniteCocycles PD T₂.L)) : G → T₂.V), hcZj j⟩ : ↥(latticeCocycles T₂.L)) := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul]
      conv_lhs => rw [← bF.sum_equivFun f]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Submodule.coe_sum]
      simp only [map_smul, Submodule.coe_smul]
    show W.clK T₂ (⟨(y f, z f), hmem⟩ : ↥(herrZ1Δ (W.γD T₂ W.gamK) (W.φD T₂) W.DelF (W.γD T₂))) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hx, map_sum, hsum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_smul, hclj, ← Submodule.mkQ_apply, map_sum]
  · let sA : LetA O n → (W.DD T₂ →ₗ[O] W.DD T₂) := fun c =>
      ((c • LinearMap.id : W.DD T₂ →ₗ[LetA O n] W.DD T₂)).restrictScalars O
    have hsA : ∀ c x, sA c x = c • x := fun c x => by
      simp only [sA, LinearMap.restrictScalars_apply, LinearMap.smul_apply, LinearMap.id_apply]
    have hNs : ∀ (c : O) (x : W.DD T₂), x ∈ W.N T₂ → c • x ∈ W.N T₂ := fun c x h => by
      rw [← algebraMap_smul (LetA O n) c x]; exact (W.N T₂).smul_mem _ h
    have hJs : ∀ (c : O) (x : W.DD T₂), x ∈ pullJ W T₂ (i - 1) 1 → c • x ∈ pullJ W T₂ (i - 1) 1 :=
      fun c x h => by rw [← algebraMap_smul (LetA O n) c x]; exact Submodule.smul_mem _ _ h
    let Φ4 : FF →ₗ[O] W.DD T₂ := ((PD.p : ℕ) : O) ^ N • (sA (letE i) ∘ₗ y) + (W.φD T₂ ∘ₗ μ (i - 1)) - μ i
    have hΦ4 : ∀ f', Φ4 f' = ((PD.p : ℕ) : O) ^ N • ((letE i : LetA O n) • y f') + W.φD T₂ (μ (i - 1) f') -
        μ i f' := fun f' => by
      simp only [Φ4, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply, hsA]
    have hΦ4b : ∀ j, Φ4 (bF j) = ((PD.p : ℕ) : O) ^ N • ((letE i : LetA O n) • yj j) +
        W.φD T₂ (μj j (i - 1)) - μj j i := fun j => by rw [hΦ4, hyb, hμb, hμb]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact extData_lin (DL W T₂ i) ⟨smul_zero _, fun δ _ => map_zero _⟩
        (fun x y hx hy => Formalism.MainNotions.RamifiedCoefficientChains.S9.dl_add W T₂ hx hy) (fun c x hx => Formalism.MainNotions.RamifiedCoefficientChains.S9.dl_smul W T₂ c hx)
        bF (μ i) (fun j => by rw [hμb]; exact (hRelj j i).1) f
    · exact extData_lin (DL W T₂ i) ⟨smul_zero _, fun δ _ => map_zero _⟩
        (fun x y hx hy => Formalism.MainNotions.RamifiedCoefficientChains.S9.dl_add W T₂ hx hy) (fun c x hx => Formalism.MainNotions.RamifiedCoefficientChains.S9.dl_smul W T₂ c hx)
        bF (ν i) (fun j => by rw [hνb]; exact (hRelj j i).2.1) f
    · let Φ3 : FF →ₗ[O] W.DD T₂ := ((PD.p : ℕ) : O) ^ N • (sA (letE i) ∘ₗ z) + ((W.γ T₂) ∘ₗ μ i - μ i)
      have hΦ3 : ∀ f', Φ3 f' = ((PD.p : ℕ) : O) ^ N • ((letE i : LetA O n) • z f') +
          (W.γ T₂ (μ i f') - μ i f') := fun f' => by
        simp only [Φ3, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply, hsA]
      rw [← hΦ3]
      exact extData_lin (InPN W T₂ 1) ⟨0, (W.N T₂).zero_mem, fun δ _ => map_zero _, (smul_zero _).symm⟩
        (fun x y hx hy => Formalism.MainNotions.RamifiedCoefficientChains.S9.inPN_add W T₂ hx hy) (fun c x hx => Formalism.MainNotions.RamifiedCoefficientChains.S9.inPN_smul W T₂ c hx)
        bF Φ3 (fun j => by rw [hΦ3, hzb, hμb]; exact (hRelj j i).2.2.1) f
    · have := extData_lin (fun x => x ∈ W.N T₂) (W.N T₂).zero_mem (fun x y hx hy => (W.N T₂).add_mem hx hy)
        hNs bF (sA (qp W ^ Mi i) ∘ₗ Φ4) (fun j => by
          rw [LinearMap.comp_apply, hsA, hΦ4b]; exact (hRelj j i).2.2.2.1) f
      rwa [LinearMap.comp_apply, hsA, hΦ4] at this
    · have := extData_lin (fun x => ∃ s : ℕ, ((PD.p : ℕ) : O) ^ s • x ∈ pullJ W T₂ (i - 1) 1)
        ⟨0, by rw [smul_zero]; exact Submodule.zero_mem _⟩
        (fun x y ⟨s₁, h₁⟩ ⟨s₂, h₂⟩ => ⟨s₁ + s₂, by
          simp only [smul_add, pow_add, mul_smul]
          rw [smul_comm (((PD.p : ℕ) : O) ^ s₁) (((PD.p : ℕ) : O) ^ s₂) x]
          exact Submodule.add_mem _ (hJs _ _ h₁) (hJs _ _ h₂)⟩)
        (fun c x ⟨s₀, h₀⟩ => ⟨s₀, by rw [smul_comm]; exact hJs c _ h₀⟩)
        bF (sA (qp W ^ hi i) ∘ₗ Φ4) (fun j => by
          rw [LinearMap.comp_apply, hsA, hΦ4b]; exact (hRelj j i).2.2.2.2.1) f
      rwa [LinearMap.comp_apply, hsA, hΦ4] at this
    · let Φ6 : FF →ₗ[O] W.DD T₂ := ((PD.p : ℕ) : O) ^ N • ν i - sA (qp W ^ a) ∘ₗ μ i
      have hΦ6 : ∀ f', Φ6 f' = ((PD.p : ℕ) : O) ^ N • ν i f' - qp W ^ a • μ i f' := fun f' => by
        simp only [Φ6, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply, hsA]
      rw [← hΦ6]
      exact extData_lin (fun x => x ∈ W.N T₂) (W.N T₂).zero_mem (fun x y hx hy => (W.N T₂).add_mem hx hy)
        hNs bF Φ6 (fun j => by rw [hΦ6, hνb, hμb]; exact (hRelj j i).2.2.2.2.2) f

end Formalism.MainNotions.RamifiedCoefficientChains.Sh

end
end

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.LocalLemmasFromLiterature

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains Formalism.MainNotions.RamifiedCoefficientChains.S9

variable (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
variable {CR CA CB CK : ℝ}

theorem caseA_loc' {l : ℕ} [Fact l.Prime] {K LL : Loc.FinExt l} (hg : Loc.Good K 1 LL)
    (hCA : Formalism.MainNotions.LiftingTheory.CaseA ((HW l).W K 1 LL hg)) : Loc.CaseA K LL := by
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  refine ⟨fun x hx => ?_, by rw [← hpl]; exact hCA.2.2, hg⟩
  obtain ⟨y, hy⟩ := hCA.1.2 ⟨x, hx⟩
  have h2 := y.2.2
  have : ((y : ↥(K0 K)) : Om l) = x := congrArg Subtype.val hy
  rw [this] at h2
  exact h2

theorem laurent_clause_of_admitted' (hA : admitted D HW F Cm CR CA CB CK) : Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm :=
  fun l _ K s LL h => (hA.1 l K s LL h).2.2.2.1

theorem uniformizer_clause_of_admitted (hA : admitted D HW F Cm CR CA CB CK) : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F :=
  fun l _ K s LL h => (hA.1 l K s LL h).2.2.2.2.2.2.2.2.1

theorem level_tools_of_admitted' (hA : admitted D HW F Cm CR CA CB CK) : Formalism.MainNotions.WachCoordinates.adm7 D HW F Cm :=
  Formalism.MainNotions.UnusedSlot80.tools_unramified_statement D HW F Cm ⟨fun l _ K s LL h => (hA.1 l K s LL h).2.2.1, laurent_clause_of_admitted' D HW F Cm hA,
    uniformizer_clause_of_admitted D HW F Cm hA⟩


set_option maxHeartbeats 0 in
theorem local_lemmas_of_literature (hA : admitted D HW F Cm CR CA CB CK) (h23 : Formalism.MainNotions.LiftingTheory.adm23 D HW F)
    (hHerr : Formalism.MainNotions.ElementDenominator.HerrClassNaturalExtension D.loc D.locA HW F) (a22 : Formalism.MainNotions.CrystallineLiftingBounds.adm22 D HW F)
    (hFont : Formalism.MainNotions.InvariantsGenerators.LitFont D HW F) : cocyclesToWachVectorsBoundAtGoodExtensions D HW F := by
  intro l _ K LL hg _
  intro d T₁ T₂ F' b S η m hset
  have hCA : Formalism.MainNotions.LiftingTheory.CaseA ((HW l).W K 1 LL hg) := hset.1
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hCAl : Loc.CaseA K LL := caseA_loc' D HW hg hCA
  have h5l : 5 ≤ l := by have := hset.2.1; rw [hpl] at this; omega
  set W := (HW l).W K 1 LL hg with hW
  have h1 := hA.1 l K 1 LL hg
  have h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W := h1.2.2.2.2.2.2.2.2.1
  obtain ⟨hE, hC, hQ⟩ := hA.2.2.2.2.2.2.2.2.2.2.1 l K LL
  have hs : W.s = 1 := hCA.2.1
  haveI : IsFractionRing ↥(OL LL) ↥LL.1 := Formalism.MainNotions.UnusedSlot80.BCF.isFrac_OL LL
  haveI : IsLocalRing ↥(OL LL) := Formalism.MainNotions.LiftingTheory.lkd_local (D.loc l) LL
  have hring : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W :=
    (((h9 _ (Formalism.MainNotions.LiftingTheory.gen_one_crys W)) hs hCA.2.2).2.2 (Formalism.MainNotions.UnusedSlot80.finrank_K0_eq_one_of_le_Kur hCAl.1)).1
  have C := ((Cm l).C K 1 LL hg).tie
  have hG := Formalism.MainNotions.N.Pv.LocalLengthBound.gam_of_tie W hs C
  have hLev : Formalism.MainNotions.WachCoordinates.LevelMapHodgeFiltration W := (level_tools_of_admitted' D HW F Cm hA l K LL hCAl h5l).2
  have hRu : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRules W := Formalism.MainNotions.N.Pv.LocalLengthBound.expRules_of W hLev hG.1 hG.2
  have hRing : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRing W := Formalism.MainNotions.N.Pv.LocalLengthBound.expRing_of W hring
  have hpt := Formalism.MainNotions.UnusedSlot80.points_exist_of_ring_condition D HW F (uniformizer_clause_of_admitted D HW F Cm hA)
  have hL := Formalism.MainNotions.UnusedSlot80.levCoeff_of_pt D HW F Cm (laurent_clause_of_admitted' D HW F Cm hA) hpt
  have hBas : Formalism.MainNotions.RamifiedCoefficientChains.Sh.BasTool W := Formalism.MainNotions.RamifiedCoefficientChains.Sh.basTool_of W h9
  have hK : Formalism.MainNotions.RamifiedCoefficientChains.Sh.LemK W := Formalism.MainNotions.N.Pv.LocalLengthBound.lemK_D D HW F Cm CR CA CB CK hA hL l K LL hCAl h5l
  have hFD : Formalism.MainNotions.RamifiedCoefficientChains.Sh.FilDim W := Formalism.MainNotions.N.Pv.LocalLengthBound.filDim_of W hQ
  have hΔ : IsUnit ((W.DelF.card : ℕ) : ↥(OL LL)) := by
    have hcard : W.DelF.card = l - 1 :=
      Formalism.MainNotions.UnusedSlot80.LevR.card_delF D HW F (uniformizer_clause_of_admitted D HW F Cm hA) l K LL hCAl
    by_contra hnu
    have hm : ((W.DelF.card : ℕ) : ↥(OL LL)) ∈ IsLocalRing.maximalIdeal ↥(OL LL) := hnu
    have hlm := Formalism.BasicNotions.Examples₂.LB.l_mem_max LL
    have e : ((l : ℕ) : ↥(OL LL)) - ((W.DelF.card : ℕ) : ↥(OL LL)) = 1 := by
      rw [hcard, Nat.cast_sub (by omega)]; simp
    have h3 := Submodule.sub_mem _ hlm hm
    rw [e] at h3
    exact (IsLocalRing.maximalIdeal.isMaximal ↥(OL LL)).ne_top ((Ideal.eq_top_iff_one _).2 h3)
  have hP9π : Formalism.MainNotions.LiftingTheory.P9π₀ W := (Formalism.MainNotions.LiftingTheory.uniformizer_ring_and_module_clauses W h9 hCA _ (Formalism.MainNotions.LiftingTheory.gen_one_crys W)).1
  have hRN : Formalism.MainNotions.LiftingTheory.CaseA W → Formalism.MainNotions.CrystallineLiftingInputs.RToolNum W := fun hCA' =>
    Formalism.MainNotions.CrystallineLiftingInputs.RToolNum_holds (D.loc l) (HW l) K LL hg hCA'
  have hDss : Formalism.MainNotions.RamifiedCoefficientChains.DssLet W := hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 l K 1 LL hg
  have hS1 : Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.Step1 W :=
    Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.first_lift_of_uniformizer_clause W (Formalism.MainNotions.WachCoordinates.Br.valRing_rec (D.loc l) LL) hP9π hRN h9 hDss hRu hRing hK hFD
      hBas hE hC hQ
  have hTZ' : Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.TTool2Z W :=
    Formalism.MainNotions.CrystallineLiftingInputs.truncatedSeriesData.tTool2Z_DU D HW F (uniformizer_clause_of_admitted D HW F Cm hA) hA.2.2.2.2.2.2.2.1 hA.2.2.2.2.2.2.2.2.1 l K LL hg
  have hFT : Formalism.MainNotions.CrystallineLiftingInputs.FTool W := Formalism.MainNotions.CrystallineLiftingInputs.Tools.local_clause_of_admitted_statements D HW F Cm hA l K LL hg
  have h2a : ∀ T : LocLat _ ℚ_[l] ↥LL.1 ↥(OL LL), IsCrys _ T.ρ → Formalism.MainNotions.DeltaInvariantLattices.p2aK W T :=
    fun T hT => ((hA.2.2.1 l K 1 LL hg).1 T hT).2
  have hS2 : Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.Step2 W :=
    Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.second_lift_of_hypotheses W hTZ' hFT hBas hK hFD hRing hRu h2a h1.2.2.2.2.1 h9 hE hC hQ
  have hQT : Formalism.MainNotions.CrystallineLiftingInputs.QTool W := Formalism.MainNotions.CrystallineLiftingInputs.Tools.level_clause_of_admitted_statements D HW F Cm hA h23 l K LL hg
  have hdex : W.DelF.card = ((D.loc l).PD K).p - 1 → ∃ dd : ↥(OL LL), dd * (W.DelF.card : ↥(OL LL)) = 1 :=
    fun _ => hΔ.exists_left_inv
  have hExt : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExtTool W :=
    Formalism.MainNotions.RamifiedCoefficientChains.Sh.extData_extTool W (hHerr l K 1 LL hg).2.2.2 (Formalism.MainNotions.LiftingTheory.liftb_HExt_holds D HW F l K 1 LL hg)
      (Formalism.MainNotions.LiftingTheory.liftb_HOne_holds D HW F l K 1 LL hg) (Formalism.MainNotions.LiftingTheory.lker_HKer_D D HW F a22 l K 1 LL hg)
      (h23 l K LL) ((hFont l K LL hCAl).2.1) hdex h1.2.2.2.2.1 h1.2.2.2.2.2.1 h9 hQT
  exact Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.cocyclesToWachVectorsBound_of_extTool W hExt hS1 hS2 d T₁ T₂ F' b S η m hset

end Formalism.MainNotions.RamifiedCoefficientChains.S9.LocalLemmasFromLiterature
