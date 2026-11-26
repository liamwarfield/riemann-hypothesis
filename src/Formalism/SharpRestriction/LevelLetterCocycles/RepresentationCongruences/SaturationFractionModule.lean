module

public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.RingDataOfCaseAOfP9
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Pi0MemADelta
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ImportsAlt
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.DivAddLogbLeEightMulErrorScale

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.SaturationFractionModule
noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [FiniteDimensional Qp LL]

variable (W : LocWach PD LL O v n)

theorem gamma_pi0_eq_pi0_mul_one_add_unit_mul_q (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) :
    ∃ κ ∈ W.AΔ, IsUnit κ ∧ W.γA W.gam W.π₀ = W.π₀ * (1 + κ * qA W) := by
  obtain ⟨w, hw, h⟩ := GS.gamma_pi0_eq_pi0_mul_unit (GS.ringData_of_caseA_of_p9 W hcase hP9)
  exact ⟨w, hw, w.isUnit, h⟩

theorem gamma_sub_self_mem_pi0_q (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (f : LetA O n) (hf : f ∈ W.AΔ) :
    ∃ g ∈ W.AΔ, W.γA W.gam f - f = W.π₀ * qA W * g :=
  GS.gam_A_core (GS.ringData_of_caseA_of_p9 W hcase hP9) hf

theorem gamma_level_eq_mul (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (s : ℕ) (hs : 1 ≤ s) :
    ∃ g ∈ W.AΔ, W.γA W.gam (ps W s) = ps W s * (1 + W.π₀ * qA W * g) :=
  GS.gam_ps_core (GS.ringData_of_caseA_of_p9 W hcase hP9) s hs

theorem gamma_fraction_in_ideal (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (a : ZMod n) (e : ℕ) (α : ℕ → ℤ)
    (f : W.EE) (hf : InId W a e α f) :
    InId W a e α (W.γE W.gam f) ∧
      InFr W a (W.π₀ * ∏ s ∈ Finset.range e, ps W s ^ (α s).toNat)
        (∏ s ∈ Finset.range e, ps W s ^ (-(α s)).toNat) (W.γE W.gam f - f) :=
  GS.gam_frac_core (GS.ringData_of_caseA_of_p9 W hcase hP9) a e α f hf

theorem saturation_fraction_ring [IsDomain O] [IsDiscreteValuationRing O] (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hinj : Function.Injective (algebraMap O LL)) (f₁ f₂ f' : LetA O n) (h₁ : f₁ ∈ PiPs W) (h₂ : f₂ ∈ PiPs W)
    (h' : f' ∈ PiPs W) (x : LetA O n) (hx : f' * x ∈ W.AΔ)
    (hk : ∃ (k : ℕ) (y : LetA O n), y ∈ W.AΔ ∧ lA W ^ k * (f₂ * x) = f₁ * y) :
    ∃ y ∈ W.AΔ, f₂ * x = f₁ * y := by
  obtain ⟨k, y, hy, hky⟩ := hk
  exact GS.sat_A_core (GS.ringData_of_caseA_of_p9 W hcase hP9) (GS.p_ne_zero W) h₁ hy k hky

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.CmpDSmulLetter
noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [FiniteDimensional Qp LL]

variable (W : LocWach PD LL O v n) (A : ArcP n) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (c : ZMod n) {d : ℕ} (b : Fin d → W.DD T₂) (sol : Fin d → ℕ → Fin d → LL) (k₀ : Fin d)

namespace TypesD

variable (W : LocWach PD LL O v n)

theorem letE_idem (c : ZMod n) : (letE (O := O) c : LetA O n) * letE c = letE c := by
  unfold letE
  funext i
  by_cases h : i = c
  · subst h; simp
  · simp [h]

theorem letE_mem (c : ZMod n) : (letE (O := O) c : LetA O n) ∈ W.AΔ := by
  unfold letE
  show ∀ δ ∈ W.DelF, (W.γA δ) (Pi.single c 1) = Pi.single c 1
  intro δ hδ
  unfold LocWach.γA letγ
  funext i
  show (W.γ₀ δ) ((Pi.single c (1 : PowerSeries O) : ZMod n → PowerSeries O) i) =
    (Pi.single c (1 : PowerSeries O) : ZMod n → PowerSeries O) i
  by_cases h : i = c
  · subst h; simp
  · simp [h]

theorem φA_letE (i : ZMod n) : W.φA (letE (O := O) i) = letE (i + 1) := by
  unfold letE LocWach.φA letφ
  funext j
  show W.φ₀ ((Pi.single i (1 : PowerSeries O) : ZMod n → PowerSeries O) (j - 1)) =
    (Pi.single (i + 1) (1 : PowerSeries O) : ZMod n → PowerSeries O) j
  by_cases h : j = i + 1
  · subst h; simp
  · have h' : j - 1 ≠ i := fun h' => h (by rw [← h']; ring)
    simp [h, h']

theorem φD_letter {T : LocLat G Qp LL O} {i : ZMod n} {x : W.DD T}
    (hx : (letE (O := O) i : LetA O n) • x = x) :
    (letE (O := O) (i + 1) : LetA O n) • W.φD T x = W.φD T x := by
  have key : ∀ (a : LetA O n) (y : W.DD T), W.φD T (a • y) = W.φA a • W.φD T y := by
    intro a y
    have h := W.55 T (algebraMap (LetA O n) W.EE a) y
    rw [algebraMap_smul] at h
    rw [h, ← algebraMap_smul W.EE (W.φA a)]
    congr 1
    exact W.44 a
  conv_rhs => rw [← hx]
  rw [key, φA_letE]

theorem φDpow_letter {T : LocLat G Qp LL O} {i : ZMod n} {x : W.DD T}
    (hx : (letE (O := O) i : LetA O n) • x = x) (e : ℕ) :
    (letE (O := O) (i + (e : ZMod n)) : LetA O n) • ((W.φD T) ^ e) x = ((W.φD T) ^ e) x := by
  induction e with
  | zero => simpa using hx
  | succ e ih =>
    rw [pow_succ']
    show (letE (O := O) (i + ((e + 1 : ℕ) : ZMod n)) : LetA O n) • W.φD T (((W.φD T) ^ e) x) =
      W.φD T (((W.φD T) ^ e) x)
    rw [Nat.cast_succ, ← add_assoc]
    exact φD_letter W ih

private theorem letE_smul_of_mem_Nl' {T : LocLat G Qp LL O} {i : ZMod n} {x : W.DD T} (hx : x ∈ W.Nl T i) :
    (letE (O := O) i : LetA O n) • x = x := by
  unfold LocWach.Nl at hx
  obtain ⟨y, -, rfl⟩ := hx
  simp only [LinearMap.smul_apply, LinearMap.id_apply]
  rw [← mul_smul, letE_idem]

theorem horTr_letter {T : LocLat G Qp LL O} {c' : ZMod n} {d : ℕ} {b : Fin d → W.DD T}
    {sol : Fin d → ℕ → Fin d → LL} (hb : IsHor W T c' b sol) {R κ : ℕ} {k : Fin d} {x : W.DD T}
    (h : IsHorTr W T b sol R κ k x) : (letE (O := O) c' : LetA O n) • x = x := by
  obtain ⟨y, -, rfl⟩ := h
  have hbm : ∀ m, (letE (O := O) c' : LetA O n) • b m = b m := fun m => letE_smul_of_mem_Nl' W (hb.1.1 m).2
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [← mul_smul, mul_comm, mul_smul]
  congr 1
  unfold Formalism.MainNotions.LiftingTheory.vecB
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  first
  | rw [smul_comm, hbm m]
  | rw [← algebraMap_smul (LetA O n) (y r m) (b m), ← mul_smul, mul_comm, mul_smul, hbm m]

end TypesD

theorem LiftsAtT.letter (hb : IsHor W T₂ (c - ((A.len c : ℕ) : ZMod n)) b sol) {f : W.EE} {e : ℕ}
    (h : LiftsAtT W A F c b sol k₀ f e) :
    LiftsAtT W A F c b sol k₀ (algebraMap (LetA O n) W.EE (letE c) * f) e := by
  unfold LiftsAtT at h ⊢
  obtain ⟨w₁, z, hw, hΛ, hP, hz, κ, κ', H, a, hH, ha, hR⟩ := h
  refine ⟨w₁, z, hw, hΛ, hP, hz, κ, κ', H, fun k => letE c * a k, hH,
    fun k => ⟨mul_mem (TypesD.letE_mem W c) (ha k).1, ?_⟩, ?_⟩
  · have hak := (ha k).2
    beta_reduce at hak ⊢
    have hfk : (if k = k₀ then lE W e * (algebraMap (LetA O n) W.EE (letE c) * f) else 0) =
        algebraMap (LetA O n) W.EE (letE c) * (if k = k₀ then lE W e * f else 0) := by
      split_ifs <;> ring
    rw [hfk, map_mul, ← hak]
    ring
  · have hs : ∑ k, (letE (O := O) c * a k) • ((W.φD T₂) ^ (A.len c)) (H k) =
        ∑ k, a k • ((W.φD T₂) ^ (A.len c)) (H k) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [mul_smul, smul_comm]
      congr 1
      have := TypesD.φDpow_letter W (TypesD.horTr_letter W hb (hH k)) (A.len c)
      rwa [sub_add_cancel] at this
    beta_reduce
    rw [hs]
    exact hR

namespace TypesD

variable (W : LocWach PD LL O v n)

theorem nl_letter {T : LocLat G Qp LL O} {i : ZMod n} {x : W.DD T} (hx : x ∈ W.Nl T i) :
    (letE (O := O) i : LetA O n) • x = x := by
  unfold LocWach.Nl at hx
  obtain ⟨y, -, rfl⟩ := hx
  simp only [LinearMap.smul_apply, LinearMap.id_apply]
  rw [← mul_smul, letE_idem]

theorem cmpD_sum {T : LocLat G Qp LL O} {d : ℕ} (y : Fin d → W.DD T) (hy : ∀ m, y m ∈ W.N T) :
    cmpD W T (∑ m, y m) = ∑ m, cmpD W T (y m) := by
  unfold cmpD
  have hs : ∑ m, y m ∈ W.N T := Submodule.sum_mem _ (fun m _ => hy m)
  rw [dite_eq_left hs]
  conv_rhs => arg 2; ext m; rw [dite_eq_left (hy m)]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum]
  congr 1
  apply Subtype.ext
  simp

theorem cmpD_smul_letter {T : LocLat G Qp LL O} {i : ZMod n} (a : LetA O n) {y : W.DD T} (hyN : y ∈ W.N T)
    (hy : (letE (O := O) i : LetA O n) • y = y) :
    cmpD W T (a • y) = algebraMap O LL (PowerSeries.constantCoeff (a i)) • cmpD W T y := by
  set c₀ : O := PowerSeries.constantCoeff (a i) with hc₀
  let r : LetA O n := fun _ => PowerSeries.mk fun p => PowerSeries.coeff (p + 1) (a i)
  have hring : a * letE i = (algebraMap O (LetA O n) c₀ + letπ * r) * letE i := by
    funext j
    simp only [Pi.mul_apply, Pi.add_apply, letE, Pi.single_apply]
    split_ifs with h
    · subst h
      rw [mul_one, mul_one, Pi.algebraMap_apply, PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
      simp only [letπ, r]
      rw [add_comm]
      exact PowerSeries.eq_X_mul_shift_add_const (a j)
    · rw [mul_zero, mul_zero]
  have hid : a • y = c₀ • y + (letπ : LetA O n) • (r • y) := by
    rw [← algebraMap_smul (LetA O n) c₀ y, smul_smul, ← add_smul]
    conv_lhs => rw [← hy, smul_smul, hring]
    rw [← smul_smul, hy]
  have hay : a • y ∈ W.N T := (W.N T).smul_mem a hyN
  have hry : r • y ∈ W.N T := (W.N T).smul_mem r hyN
  have he : (⟨a • y, hay⟩ : W.N T) = c₀ • (⟨y, hyN⟩ : W.N T) + (letπ : LetA O n) • (⟨r • y, hry⟩ : W.N T) := by
    apply Subtype.ext
    simp only [Submodule.coe_add, Submodule.coe_smul_of_tower]
    exact hid
  rw [cmpD, dite_eq_left hay, he, map_add (f := _), W.cmp_smul, W.cmp_π, add_zero, cmpD, dite_eq_left hyN]

end TypesD

theorem constants_pre (hA : A.OK) (hc : c ∈ A.cuts) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hl : 5 ≤ PD.p)
    (hHF : HorFrameCoreT W) (hArcL : ArcLCore W) (hW₁ : Win W A T₁) (hsur : Formalism.MainNotions.LiftingTheory.Sur W F)
    (rr : ℕ) (hrr : ∀ c'' ∈ A.cuts, Formalism.MainNotions.LiftingTheory.KillsΔ W F c'' (Formalism.MainNotions.LiftingTheory.lp W rr))
    (hb : IsHor W T₂ (c - ((A.len c : ℕ) : ZMod n)) b sol) :
    ∃ (d₁ : ℕ) (b₁ : Fin d₁ → W.DD T₁) (sol₁ : Fin d₁ → ℕ → Fin d₁ → LL) (c₁ : Fin d₁ → O),
      IsHor W T₁ (c - ((A.len c : ℕ) : ZMod n)) b₁ sol₁ ∧
      Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B F.f (dvO W T₁ (A.len c) b₁ c₁) =
        ((PD.p : LL) ^ rr) • dv W T₂ (A.len c) b (Pi.single k₀ 1) := by
  have hc' : c - ((A.len c : ℕ) : ZMod n) ∈ A.cuts := (hA.2.2.1 c hc).2.2.1
  obtain ⟨d₁, b₁, sol₁, hb₁⟩ := hHF hcase hl A hA T₁ hW₁ (c - ((A.len c : ℕ) : ZMod n))
  obtain ⟨⟨hfr₂, -⟩, -⟩ := hb
  have hb₁' := hb₁
  obtain ⟨⟨hfr₁, huniq₁⟩, -⟩ := hb₁'
  obtain ⟨x₁, hx₁, hmap⟩ := hArcL hcase T₁ T₂ F hsur _ rr (A.len c) (hrr _ hc') (b k₀) (hfr₂ k₀)
  obtain ⟨a, ⟨-, hx⟩, -⟩ := huniq₁ x₁ hx₁
  have hN : ∀ m, b₁ m ∈ W.N T₁ := fun m => (hfr₁ m).1.1
  have hL : ∀ m, (letE (O := O) (c - ((A.len c : ℕ) : ZMod n)) : LetA O n) • b₁ m = b₁ m :=
    fun m => TypesD.nl_letter W (hfr₁ m).2
  have hcmp : cmpD W T₁ x₁ = ∑ m, algebraMap O LL (PowerSeries.constantCoeff (a m (c - ((A.len c : ℕ) : ZMod n)))) •
      cmpD W T₁ (b₁ m) := by
    rw [hx, TypesD.cmpD_sum W _ fun m => (W.N T₁).smul_mem _ (hN m)]
    exact Finset.sum_congr rfl fun m _ => TypesD.cmpD_smul_letter W (a m) (hN m) (hL m)
  refine ⟨d₁, b₁, sol₁, fun m => PowerSeries.constantCoeff (a m (c - ((A.len c : ℕ) : ZMod n))), hb₁, ?_⟩
  have hdv1 : dvO W T₁ (A.len c) b₁ (fun m => PowerSeries.constantCoeff (a m (c - ((A.len c : ℕ) : ZMod n)))) =
      ((φVB PD (LL := LL) (V := T₁.V)) ^ (A.len c)) (cmpD W T₁ x₁) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hcmp, map_sum]
    simp only [dvO, dv, map_smul]
  have hdv2 : dv W T₂ (A.len c) b (Pi.single k₀ 1) =
      ((φVB PD (LL := LL) (V := T₂.V)) ^ (A.len c)) (cmpD W T₂ (b k₀)) := by
    unfold dv
    rw [Finset.sum_eq_single k₀ (fun m _ hm => by simp [hm]) (fun h => absurd (Finset.mem_univ _) h)]
    simp
  rw [hdv1, hdv2]
  exact hmap

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.AlgebraMapMemInvariants
noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [FiniteDimensional Qp LL]

open TypesA

variable (W : LocWach PD LL O v n)

section Smul

variable {T : LocLat G Qp LL O}

theorem algebraMap_mem_invariants (t : O) : algebraMap O (LetA O n) t ∈ W.AΔ := W.AΔ.algebraMap_mem t

theorem algebraMap_smul_eq_smul (t : O) (x : W.DD T) : algebraMap O (LetA O n) t • x = t • x :=
  algebraMap_smul (LetA O n) t x

theorem inI_algebraMap_smul {c : ZMod n} (t : O) {w : W.DD T} (h : InI W T c w) :
    InI W T c (algebraMap O (LetA O n) t • w) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · show (letE (O := O) c : LetA O n) • (algebraMap O (LetA O n) t • w) = algebraMap O (LetA O n) t • w
    rw [smul_comm]
    exact congrArg _ h1
  · intro δ hδ
    rw [algebraMap_smul_eq_smul, map_smul, h2 δ hδ]
  · have : W.γ T (algebraMap O (LetA O n) t • w) - algebraMap O (LetA O n) t • w =
        algebraMap O (LetA O n) t • (W.γ T w - w) := by
      rw [algebraMap_smul_eq_smul, algebraMap_smul_eq_smul, map_smul, smul_sub]
    rw [this]
    exact InFNc_smul W (algebraMap_mem_invariants W t) h3

theorem repVV_smul_invariant {c' : ZMod n} {e M : ℕ} {Λ : LetA O n} {d : ℕ} {b : Fin d → W.DD T}
    {sol : Fin d → ℕ → Fin d → LL} (a : LetA O n) (ha : a ∈ W.AΔ) {x : W.DD T} {f : Fin d → W.EE}
    (h : RepVV W T c' e M Λ b sol x f) :
    RepVV W T c' e M Λ b sol (a • x) (fun k => algebraMap (LetA O n) W.EE a * f k) := by
  obtain ⟨κ, κ', H, a', hH, ha', hP⟩ := h
  refine ⟨κ, κ', H, fun k => a * a' k, hH,
    fun k => ⟨W.AΔ.mul_mem ha (ha' k).1, ?_⟩, ?_⟩
  · rw [map_mul, ← (ha' k).2]
    ring
  · have hs : ∑ k, (a * a' k) • ((W.φD T) ^ e) (H k) = a • ∑ k, a' k • ((W.φD T) ^ e) (H k) := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun k _ => mul_smul _ _ _
    rw [hs]
    have key : lA W ^ κ' • (lA W ^ κ • Λ • (a • x) - a • ∑ k, a' k • ((W.φD T) ^ e) (H k)) =
        a • (lA W ^ κ' • (lA W ^ κ • Λ • x - ∑ k, a' k • ((W.φD T) ^ e) (H k))) := by
      simp only [smul_sub]
      rw [smul_comm Λ a x, smul_comm (lA W ^ κ) a, smul_comm (lA W ^ κ') a, smul_comm (lA W ^ κ') a]
    rw [key]
    exact inMultiple_smul W ha hP

end Smul

theorem liftsAt_algebraMap_mul (A : ArcP n) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (c : ZMod n) {d : ℕ} (bb : Fin d → W.DD T₂) (sol : Fin d → ℕ → Fin d → LL) (k₀ : Fin d) {g : W.EE}
    {e : ℕ} (t : O) (h : LiftsAt W A F c bb sol k₀ g e) :
    LiftsAt W A F c bb sol k₀ (algebraMap O W.EE t * g) e := by
  obtain ⟨w₁, z, h1, ⟨Λ', hΛ', h2⟩, h3, h4, h5⟩ := h
  set a := algebraMap O (LetA O n) t with ha_def
  have ha : a ∈ W.AΔ := algebraMap_mem_invariants W t
  refine ⟨a • w₁, a • z, inI_algebraMap_smul W t h1, ⟨Λ', hΛ', ?_⟩, ?_, InFNc_smul W ha h4, ?_⟩
  · rw [smul_comm]
    exact InFNc_smul W ha h2
  · rw [map_smulA, smul_comm]
    exact inMultiple_smul W ha h3
  · have h6 := repVV_smul_invariant W a ha h5
    rw [map_smulA, ← smul_sub]
    refine RepVV_congr W h6 rfl fun k => ?_
    have hat : algebraMap (LetA O n) W.EE a = algebraMap O W.EE t := by
      rw [ha_def, ← IsScalarTower.algebraMap_apply]
    split_ifs
    · rw [hat]; ring
    · rw [mul_zero]

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end
