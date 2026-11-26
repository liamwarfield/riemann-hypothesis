module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeCharCMLocKNonsplitEqNegOnePow

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.LocalRingStructure
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LocalRingStructure

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

def IsOver (i : ZMod n) (τ : K →ₐ[Qp] LL) : Prop :=
  ∀ c : K₀, τ (algebraMap K₀ K c) = W.emb i c

def JumpsBounded (T : LocLat G Qp LL O) (M h : ZMod n → ℕ) : Prop :=
  ∀ (i : ZMod n) (τ : K →ₐ[Qp] LL), IsOver W i τ →
    JumpsInV PD T.ρ τ (Set.Icc (-(M i : ℤ)) (h i : ℤ))

def phiStar (T : LocLat G Qp LL O) (i : ZMod n) : Submodule (LetA O n) (W.DD T) :=
  Submodule.span (LetA O n) (W.φD T '' (W.Nl T (i - 1) : Set (W.DD T)))

def PartA (T : LocLat G Qp LL O) (M h : ZMod n → ℕ) : Prop :=
  ∀ i : ZMod n,
    (∀ y ∈ phiStar W T i, W.Q ^ M i • y ∈ W.Nl T i) ∧
    (∀ y ∈ W.Nl T i, W.Q ^ h i • y ∈ phiStar W T i)

def LocRing (_W : LocWach PD LL O v n) (_i : ZMod n) (_ζ : LL) : Type := PowerSeries LL

instance (i : ZMod n) (ζ : LL) : CommRing (LocRing W i ζ) :=
  inferInstanceAs (CommRing (PowerSeries LL))

instance (i : ZMod n) (ζ : LL) : Algebra (LetA O n) (LocRing W i ζ) :=
  RingHom.toAlgebra (R := LetA O n) (S := LocRing W i ζ) (W.lev i ζ).toRingHom

abbrev Nloc (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) : Type :=
  LocRing W i ζ ⊗[LetA O n] ↥(W.Nl T i)

def MemInv (T : LocLat G Qp LL O) (i : ZMod n) (y : W.DD T) : Prop :=
  ∃ k : ℕ, W.Q ^ k • y ∈ W.Nl T i

def MemLoc (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (y : W.DD T) : Prop :=
  ∃ (k : ℕ) (hk : W.Q ^ k • y ∈ W.Nl T i) (z : Nloc W T i ζ),
    (1 : LocRing W i ζ) ⊗ₜ[LetA O n] (⟨W.Q ^ k • y, hk⟩ : ↥(W.Nl T i)) =
      (algebraMap (LetA O n) (LocRing W i ζ) (W.Q ^ k)) • z

def PartB (T : LocLat G Qp LL O) : Prop :=
  ∀ (i : ZMod n) (y : W.DD T), MemInv W T i y →
    (y ∈ W.Nl T i ↔ ∀ ζ : LL, IsPrimitiveRoot ζ (PD.p ^ W.s) → MemLoc W T i ζ y)

variable {W} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA] [Algebra O RW]
  {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
  (E : EtTie W RA RW inclR φR gR πA)

def latAinf (_E : EtTie W RA RW inclR φR gR πA) (T : LocLat G Qp LL O) : Submodule O (TW RW T) :=
  LinearMap.range (TWincl inclR T)

def wachAinf (T : LocLat G Qp LL O) : Submodule O (TW RW T) :=
  Submodule.span O {w | ∃ (a : RA) (x : W.DD T), x ∈ W.N T ∧ w = inclR a • E.jD T x}

def PartC (T : LocLat G Qp LL O) (M h : ℕ) : Prop :=
  (∀ w ∈ latAinf E T, inclR (E.io W.X) ^ h • w ∈ wachAinf E T) ∧
  (∀ w ∈ wachAinf E T, inclR (E.io W.X) ^ M • w ∈ latAinf E T)

end Generic


open TensorProduct in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.LocalRingStructure.letters_neZero {l : ℕ} [Fact l.Prime] (K : _root_.Formalism.BasicNotions.Loc.FinExt l) :
    NeZero (Module.finrank ℚ_[l] ↥(_root_.Formalism.BasicNotions.Loc.K0 K)) := by
  haveI : FiniteDimensional ℚ_[l] ↥(K : IntermediateField ℚ_[l] (_root_.Formalism.BasicNotions.Loc.Om l)) := K.2
  have hle : _root_.Formalism.BasicNotions.Loc.K0 K ≤ (K : IntermediateField ℚ_[l] (_root_.Formalism.BasicNotions.Loc.Om l)) := inf_le_left
  haveI : FiniteDimensional ℚ_[l] ↥(_root_.Formalism.BasicNotions.Loc.K0 K) :=
    Module.Finite.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion hle).injective
  exact ⟨Module.finrank_pos.ne'⟩

def letterMax {l : ℕ} [Fact l.Prime] (K : FinExt l)
    (m : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ℕ) : ℕ :=
  haveI := letters_neZero K
  Finset.univ.sup m

def HeightsFromJumps (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (H : LocHW l P)
    (F : LocFon l P AI H) (_C : LocCmpT l P AI H F) : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (hg : Good K s LL)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys (P.PD K) T.ρ →
    ∀ M h : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ℕ, JumpsBounded (H.W K s LL hg) T M h →
      PartA (H.W K s LL hg) T M h ∧ PartB (H.W K s LL hg) T ∧
        PartC (F.E K s LL hg).tie T (letterMax K M) (letterMax K h)

end GlobalTheory.IndefiniteRowSideFullHecke.LocalRingStructure
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapLocRing
section -- merged from Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.CriterionWithoutRoot
noncomputable section

namespace GlobalTheory.WachHeightTest

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.DeltaInvariantLattices PowerSeries

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem q_eq : W.q = ∑ k ∈ Finset.range PD.p, (1 + (letπ : LetA O n)) ^ k := by
  funext i
  have h := W.q₀_def
  have h2 : (PowerSeries.X : PowerSeries O) * ∑ k ∈ Finset.range PD.p, (1 + PowerSeries.X) ^ k =
      (1 + PowerSeries.X) ^ PD.p - 1 := by
    have := mul_geom_sum (1 + (PowerSeries.X : PowerSeries O)) PD.p
    simpa using this
  have h3 := PowerSeries.X_mul_cancel (h.trans h2.symm)
  simp [LocWach.q, h3, letπ, Finset.sum_apply]

theorem φ_one_add : W.φA (1 + letπ) = (1 + (letπ : LetA O n)) ^ PD.p := by
  rw [map_add (f := _), map_one, W.φA_π]
  funext i
  have h := W.q₀_def
  simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.one_apply, letπ, LocWach.q, h]
  ring

theorem φpow_one_add (j : ℕ) : (W.φA ^ j) (1 + letπ) = (1 + (letπ : LetA O n)) ^ (PD.p ^ j) := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ', AlgHom.mul_apply, ih, map_pow, φ_one_add, ← pow_mul, pow_succ']

theorem Q_eq : W.Q = ∑ k ∈ Finset.range PD.p, ((1 + (letπ : LetA O n)) ^ (PD.p ^ (W.s - 1))) ^ k := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [LocWach.Q, q_eq, map_sum]
  simp only [map_pow, φpow_one_add]

theorem value_Q (i : ZMod n) (ζ : LL) (hζ : ∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) :
    PowerSeries.constantCoeff (W.lev i ζ W.Q) =
      ∑ k ∈ Finset.range PD.p, (ζ ^ (PD.p ^ (W.s - 1))) ^ k := by
  obtain ⟨E, hE, -, h⟩ := W.lev_π i ζ hζ
  rw [Q_eq]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_pow, map_add (f := _), map_one]
  have : 1 + PowerSeries.constantCoeff (W.lev i ζ letπ) = ζ := by
    have := congrArg PowerSeries.constantCoeff h
    simpa [hE] using this
  rw [this]

include W in
theorem p_ne_zero : ((PD.p : ℕ) : LL) ≠ 0 := by
  intro h
  have := W.v_l
  rw [h, AddValuation.map_zero] at this
  exact WithTop.top_ne_one this

theorem qRoot_iff (i : ZMod n) (ζ : LL) :
    QRoot W i ζ ↔ (∃ c : O, algebraMap O LL c = ζ) ∧ IsPrimitiveRoot ζ (PD.p ^ W.s) := by
  haveI : Fact PD.p.Prime := ⟨PD.hp⟩
  have hs : W.s = W.s - 1 + 1 := by have := W.s_pos; omega
  constructor
  · rintro ⟨hc, ⟨m, hm⟩, h0⟩
    refine ⟨hc, ?_⟩
    have hprim : ∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j) := by
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow PD.hp).1 (orderOf_dvd_of_pow_eq_one hm)
      exact ⟨j, hj ▸ IsPrimitiveRoot.orderOf ζ⟩
    rw [value_Q W i ζ hprim] at h0
    have h1 : ¬ ζ ^ PD.p ^ (W.s - 1) = 1 := by
      intro h
      rw [h] at h0
      apply p_ne_zero W
      simpa using h0
    have h2 : ζ ^ PD.p ^ (W.s - 1 + 1) = 1 := by
      have := geom_sum_mul (ζ ^ PD.p ^ (W.s - 1)) PD.p
      rw [h0, zero_mul] at this
      rw [pow_succ, pow_mul]
      exact (sub_eq_zero.1 this.symm)
    have := orderOf_eq_prime_pow h1 h2
    rw [hs, ← this]
    exact IsPrimitiveRoot.orderOf ζ
  · rintro ⟨hc, hp⟩
    refine ⟨hc, ⟨W.s, hp.pow_eq_one⟩, ?_⟩
    rw [value_Q W i ζ ⟨_, hp⟩]
    have h1 : ζ ^ PD.p ^ (W.s - 1) ≠ 1 :=
      hp.pow_ne_one_of_pos_of_lt (pow_pos PD.hp.pos _).ne'
        (Nat.pow_lt_pow_right PD.hp.one_lt (by omega))
    have := geom_sum_mul (ζ ^ PD.p ^ (W.s - 1)) PD.p
    rw [← pow_mul, ← pow_succ, ← hs, hp.pow_eq_one, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 h1)

end Local

end GlobalTheory.WachHeightTest
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LetterSandwichOfFrobMatrices
noncomputable section

namespace GlobalTheory.WachLettersCompare

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition GlobalTheory.IndefiniteRowSideFullHecke.WachLettersFreeness

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

attribute [local instance] letterModule

theorem mul_letE (i : ZMod n) (a : LetA O n) : a * letE i = Pi.single i (a i) := by
  funext j
  by_cases h : j = i
  · subst h; simp [letE]
  · simp [letE, h]

theorem letE_mul_self (i : ZMod n) : (letE i : LetA O n) * letE i = letE i := by
  rw [mul_letE]; simp [letE]

theorem mem_Nl_iff (i : ZMod n) (x : W.DD T) :
    x ∈ W.Nl T i ↔ x ∈ W.N T ∧ (letE i : LetA O n) • x = x := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨(W.N T).smul_mem _ hy, ?_⟩
    change (letE i : LetA O n) • ((letE i : LetA O n) • y) = (letE i : LetA O n) • y
    rw [smul_smul, letE_mul_self]
  · rintro ⟨hx, he⟩
    exact ⟨x, hx, he⟩

theorem letE_smul_mem (i : ZMod n) {x : W.DD T} (hx : x ∈ W.N T) :
    (letE i : LetA O n) • x ∈ W.Nl T i := ⟨x, hx, rfl⟩

theorem φD_smulA (a : LetA O n) (x : W.DD T) : W.φD T (a • x) = W.φA a • W.φD T x := by
  have := W.φD_smul T (algebraMap (LetA O n) W.EE a) x
  rw [algebraMap_smul, W.φE_ext, algebraMap_smul] at this
  exact this


include W in
theorem neZero_letters : NeZero n := by
  have := PD.finK₀
  exact ⟨by rw [W.n_eq]; exact Module.finrank_pos.ne'⟩

theorem isUnit_Q : IsUnit (algebraMap (LetA O n) W.EE W.Q) := by
  have hq : IsUnit (algebraMap (LetA O n) W.EE W.q) := by
    have h1 : (letπ : LetA O n) * W.q = (1 + letπ) ^ PD.p - 1 := by
      funext i
      simpa [letπ, LocWach.q] using W.q₀_def
    set x := algebraMap (LetA O n) W.EE letπ with hx
    obtain ⟨r, hr⟩ := exists_add_pow_prime_eq PD.hp (1 : W.EE) x
    obtain ⟨u, hu⟩ : IsUnit (x ^ PD.p) := W.EE_π.pow _
    have := W.EE_complete
    have hj : ((PD.p : ℕ) : W.EE) ∈ Ideal.jacobson (⊥ : Ideal W.EE) :=
      IsAdicComplete.le_jacobson_bot (Ideal.span {((PD.p : ℕ) : W.EE)})
        (Ideal.mem_span_singleton_self _)
    have h2 := (Ideal.mem_jacobson_bot.1 hj) (x * r * (↑u⁻¹ : W.EE))
    have h3 : x * algebraMap (LetA O n) W.EE W.q =
        (((PD.p : ℕ) : W.EE) * (x * r * (↑u⁻¹ : W.EE)) + 1) * u := by
      rw [hx, ← map_mul, h1, map_sub, map_pow, map_add (f := _), map_one, ← hx, hr, ← hu]
      have := u.inv_mul
      linear_combination (-((PD.p : ℕ) : W.EE) * x * r) * this
    exact isUnit_of_mul_isUnit_right (h3 ▸ h2.mul u.isUnit)
  have key : ∀ k : ℕ, IsUnit (algebraMap (LetA O n) W.EE ((W.φA ^ k) W.q)) := by
    intro k
    induction k with
    | zero => simpa using hq
    | succ k ih =>
      rw [pow_succ', AlgHom.mul_apply]
      have := W.φE_ext ((W.φA ^ k) W.q)
      exact this ▸ ih.map W.φE
  exact key _

theorem Q_pow_smul_cancel (m : ℕ) {x y : W.DD T} (h : W.Q ^ m • x = W.Q ^ m • y) : x = y := by
  rw [← algebraMap_smul W.EE, ← algebraMap_smul W.EE (W.Q ^ m) y, map_pow] at h
  exact ((isUnit_Q W).pow m).smul_left_cancel.1 h

variable {W T}

variable (W T)

end Generic

end GlobalTheory.WachLettersCompare
end
end

noncomputable section

namespace GlobalTheory.HeightsClauseCompare

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.DeltaInvariantLattices TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.LocalRingStructure
open GlobalTheory.WachLettersCompare (mem_Nl_iff letE_smul_mem φD_smulA neZero_letters Q_pow_smul_cancel
  letE_mul_self)

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem isOver_iff (i : ZMod n) (τ : K →ₐ[Qp] LL) : IsOver W i τ ↔ OverLetter W τ i :=
  ⟨fun h => AlgHom.ext h, fun h c => DFunLike.congr_fun h c⟩

theorem jumps_iff (M h : ZMod n → ℕ) : JumpsBounded W T M h ↔ JumpsLet W T M h :=
  ⟨fun H τ i hτ => H i τ ((isOver_iff W i τ).2 hτ), fun H i τ hτ => H τ i ((isOver_iff W i τ).1 hτ)⟩

theorem φA_letE (i : ZMod n) : W.φA (letE (i - 1)) = letE i := by
  funext j
  change W.φ₀ ((letE (i - 1) : LetA O n) (j - 1)) = _
  by_cases hj : j = i
  · subst hj
    simp [letE]
  · have : j - 1 ≠ i - 1 := fun h => hj (sub_left_injective h)
    simp [letE, hj, this]

theorem pole_iff (i : ZMod n) (m : ℕ) :
    (∀ y ∈ phiStar W T i, W.Q ^ m • y ∈ W.Nl T i) ↔
      ∀ x ∈ W.Nl T (i - 1), W.Q ^ m • W.φD T x ∈ W.N T := by
  constructor
  · intro H x hx
    exact ((mem_Nl_iff W T i _).1 (H _ (Submodule.subset_span ⟨x, hx, rfl⟩))).1
  · intro H y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, hx, rfl⟩ := hy
      refine (mem_Nl_iff W T i _).2 ⟨H x hx, ?_⟩
      have h1 := ((mem_Nl_iff W T (i - 1) x).1 hx).2
      rw [smul_comm, ← φA_letE W i, ← φD_smulA, h1]
    | zero => simp
    | add a b _ _ ha hb => rw [smul_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [smul_comm]; exact Submodule.smul_mem _ _ ha

theorem partA_iff (M h : ZMod n → ℕ) : PartA W T M h ↔
    (∀ i, ∀ x ∈ W.Nl T (i - 1), W.Q ^ (M i) • W.φD T x ∈ W.N T) ∧
      (∀ i, ∀ y ∈ W.Nl T i, W.Q ^ (h i) • y ∈ φspan W T (W.Nl T (i - 1))) :=
  ⟨fun H => ⟨fun i => (pole_iff W T i _).1 (H i).1, fun i => (H i).2⟩,
    fun H i => ⟨(pole_iff W T i _).2 (H.1 i), H.2 i⟩⟩

theorem simple_zero (i : ZMod n) (ζ : LL) (hζ : QRoot W i ζ) :
    ∃ w : PowerSeries LL, IsUnit w ∧ W.lev i ζ W.Q = PowerSeries.X * w := by
  have hp := ((GlobalTheory.WachHeightTest.qRoot_iff W i ζ).1 hζ).2
  obtain ⟨w, hw⟩ := PowerSeries.X_dvd_iff.2 hζ.2.2
  refine ⟨w, ?_, hw⟩
  rw [PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
  intro h0
  obtain ⟨w', hw'⟩ := PowerSeries.X_dvd_iff.2 h0
  obtain ⟨E, hE, hd, hlev⟩ := W.lev_π i ζ ⟨_, hp⟩
  have hs : W.s = W.s - 1 + 1 := by have := W.s_pos; omega
  have h1 : W.lev i ζ W.Q * ((PowerSeries.C ζ * E) ^ (PD.p ^ (W.s - 1)) - 1) =
      E ^ (PD.p ^ W.s) - 1 := by
    rw [GlobalTheory.WachHeightTest.Q_eq]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_pow, map_add (f := _), map_one, hlev]
    rw [geom_sum_mul, ← pow_mul, ← pow_succ, ← hs, mul_pow, ← map_pow, hp.pow_eq_one, map_one,
      one_mul]
  have h2 : PowerSeries.X ^ 2 ∣ E ^ (PD.p ^ W.s) - 1 := by
    rw [← h1, hw, hw']
    exact Dvd.dvd.mul_right ⟨w', by ring⟩ _
  have h3 := PowerSeries.X_pow_dvd_iff.1 h2 1 (by norm_num)
  have h4 : PowerSeries.coeff 1 E = 1 := by
    have := congrArg (PowerSeries.coeff 0) hd
    rw [PowerSeries.coeff_derivative] at this
    simpa [hE] using this
  rw [map_sub, PowerSeries.coeff_one_pow, h4, hE] at h3
  simp [PowerSeries.coeff_one] at h3
  exact GlobalTheory.WachHeightTest.p_ne_zero W h3.1

def Van (i : ZMod n) (ζ : LL) (x : W.DD T) : Prop :=
  ∀ k : ℕ, W.Q ^ k • x ∈ W.N T → W.Q ^ k • x ∈ vanI W i ζ k • W.N T

theorem mem_vanI {i : ZMod n} {ζ : LL} {k : ℕ} {a : LetA O n} :
    a ∈ vanI W i ζ k ↔ PowerSeries.X ^ k ∣ W.lev i ζ a := by
  simp only [vanI, Ideal.mem_comap, Ideal.mem_span_singleton]

theorem mem_smul_iff {ι : Type} [Fintype ι] (nb : Module.Basis ι (LetA O n) ↥(W.N T))
    (I : Ideal (LetA O n)) (y : W.DD T) (hy : y ∈ W.N T) :
    y ∈ I • W.N T ↔ ∀ j, nb.repr ⟨y, hy⟩ j ∈ I := by
  constructor
  · intro h
    have key : ∃ h : y ∈ W.N T, ∀ j, nb.repr ⟨y, h⟩ j ∈ I := by
      refine Submodule.smul_induction_on h (fun a ha z hz => ⟨(W.N T).smul_mem a hz, fun j => ?_⟩) ?_
      · have e : (⟨a • z, (W.N T).smul_mem a hz⟩ : ↥(W.N T)) = a • (⟨z, hz⟩ : ↥(W.N T)) := rfl
        rw [e, map_smul, Finsupp.smul_apply, smul_eq_mul]
        exact I.mul_mem_right _ ha
      · rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨(W.N T).add_mem ha hb, fun j => ?_⟩
        have e : (⟨a + b, (W.N T).add_mem ha hb⟩ : ↥(W.N T)) = ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
        rw [e, map_add (f := _), Finsupp.add_apply]
        exact I.add_mem (ha' j) (hb' j)
    exact key.2
  · intro h
    have h1 := congrArg Subtype.val (nb.sum_repr ⟨y, hy⟩)
    simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at h1
    rw [← h1]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem_smul (h j) (nb j).2

theorem van_of_one {ι : Type} [Fintype ι] (nb : Module.Basis ι (LetA O n) ↥(W.N T))
    {i : ZMod n} {ζ : LL} (hζ : QRoot W i ζ) {x : W.DD T} {k : ℕ} (hk : W.Q ^ k • x ∈ W.N T)
    (h : W.Q ^ k • x ∈ vanI W i ζ k • W.N T) : Van W T i ζ x := by
  intro k' hk'
  obtain ⟨w, hw, hQ⟩ := simple_zero W i ζ hζ
  rw [mem_smul_iff W T nb _ _ hk] at h
  rw [mem_smul_iff W T nb _ _ hk']
  intro j
  have e : W.Q ^ k' • (⟨_, hk⟩ : ↥(W.N T)) = W.Q ^ k • (⟨_, hk'⟩ : ↥(W.N T)) :=
    Subtype.ext (smul_comm _ _ _)
  have e2 := congrArg (fun z => W.lev i ζ (nb.repr z j)) e
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, map_pow, hQ] at e2
  obtain ⟨c, hc⟩ := (mem_vanI W).1 (h j)
  rw [hc] at e2
  rw [mem_vanI, ← (hw.pow k).dvd_mul_left]
  refine ⟨w ^ k' * c, ?_⟩
  apply mul_left_cancel₀ (pow_ne_zero k (PowerSeries.X_ne_zero (R := LL)))
  rw [mul_pow, mul_pow] at e2
  linear_combination -e2

theorem lev_letE (i : ZMod n) (ζ : LL) : W.lev i ζ (letE i) = 1 := by
  have := W.lev_letter i ζ (1 - letE i) (by simp [letE])
  rw [map_sub, map_one] at this
  exact (sub_eq_zero.1 this).symm

theorem memLoc_iff {ι : Type} [Fintype ι] (nb : Module.Basis ι (LetA O n) ↥(W.N T))
    {i : ZMod n} {ζ : LL} (hζ : QRoot W i ζ) {y : W.DD T} (hy : MemInv W T i y) :
    MemLoc W T i ζ y ↔ Van W T i ζ y := by
  obtain ⟨w, hw, hQ⟩ := simple_zero W i ζ hζ
  constructor
  · rintro ⟨k, hk, z, hz⟩
    have hk' := ((mem_Nl_iff W T i _).1 hk).1
    refine van_of_one W T nb hζ hk' ((mem_smul_iff W T nb _ _ hk').2 fun j => ?_)
    have hle : W.Nl T i ≤ W.N T := fun x hx => ((mem_Nl_iff W T i _).1 hx).1
    let f : ↥(W.Nl T i) →ₗ[LetA O n] LocRing W i ζ :=
      (Algebra.linearMap (LetA O n) (LocRing W i ζ)).comp
        ((nb.coord j).comp (Submodule.inclusion hle))
    have h1 := congrArg (f.liftBaseChange (LocRing W i ζ)) hz
    rw [map_smul, LinearMap.liftBaseChange_tmul, one_smul, smul_eq_mul] at h1
    rw [mem_vanI]
    have h2 : W.lev i ζ (nb.repr ⟨_, hk'⟩ j) = W.lev i ζ (W.Q ^ k) *
      (show PowerSeries LL from f.liftBaseChange (LocRing W i ζ) z) := h1
    rw [h2, map_pow, hQ, mul_pow, mul_assoc]
    exact dvd_mul_right _ _
  · intro H
    obtain ⟨k, hk⟩ := hy
    obtain ⟨hk', he⟩ := (mem_Nl_iff W T i _).1 hk
    refine ⟨k, hk, ?_⟩
    have key : ∀ m ∈ vanI W i ζ k • W.N T, ∃ (hm : (letE i : LetA O n) • m ∈ W.Nl T i)
        (z : Nloc W T i ζ), (1 : LocRing W i ζ) ⊗ₜ[LetA O n] (⟨_, hm⟩ : ↥(W.Nl T i)) =
          (algebraMap (LetA O n) (LocRing W i ζ) (W.Q ^ k)) • z := by
      intro m hm
      refine Submodule.smul_induction_on hm (fun a ha z hz => ?_) ?_
      · refine ⟨letE_smul_mem W T i ((W.N T).smul_mem a hz), ?_⟩
        have hd : W.lev i ζ (W.Q ^ k) ∣ W.lev i ζ a := by
          rw [map_pow, hQ, mul_pow, (hw.pow k).mul_right_dvd]
          exact (mem_vanI W).1 ha
        obtain ⟨c, hc⟩ := hd
        refine ⟨(show LocRing W i ζ from c) ⊗ₜ[LetA O n]
          (⟨_, letE_smul_mem W T i hz⟩ : ↥(W.Nl T i)), ?_⟩
        have e : (⟨_, letE_smul_mem W T i ((W.N T).smul_mem a hz)⟩ : ↥(W.Nl T i)) =
            a • (⟨_, letE_smul_mem W T i hz⟩ : ↥(W.Nl T i)) := Subtype.ext (smul_comm _ _ _)
        rw [e, ← TensorProduct.smul_tmul, TensorProduct.smul_tmul', smul_eq_mul,
          Algebra.smul_def, mul_one]
        congr 1
      · rintro a b ⟨ha, za, ha'⟩ ⟨hb, zb, hb'⟩
        refine ⟨by rw [smul_add]; exact Submodule.add_mem _ ha hb, za + zb, ?_⟩
        rw [smul_add _ za zb, ← ha', ← hb', ← TensorProduct.tmul_add]
        congr 1
        exact Subtype.ext (smul_add _ _ _)
    obtain ⟨hm, z, hz⟩ := key _ (H k hk')
    refine ⟨z, ?_⟩
    rw [← hz]
    congr 1
    exact Subtype.ext he.symm

theorem fixed_of_memInv {i : ZMod n} {y : W.DD T} (hy : MemInv W T i y) :
    (letE i : LetA O n) • y = y := by
  obtain ⟨k, hk⟩ := hy
  refine Q_pow_smul_cancel W T k ?_
  rw [smul_comm]
  exact ((mem_Nl_iff W T i _).1 hk).2

theorem van_other {i i' : ZMod n} (h : i' ≠ i) (ζ : LL) {y : W.DD T}
    (hy : (letE i : LetA O n) • y = y) : Van W T i' ζ y := by
  intro k hk
  rw [← hy, smul_comm]
  refine Submodule.smul_mem_smul ?_ hk
  rw [mem_vanI, W.lev_letter i' ζ _ (by simp [letE, h])]
  exact dvd_zero _

theorem van_letE_iff {ι : Type} [Fintype ι] (nb : Module.Basis ι (LetA O n) ↥(W.N T))
    {i : ZMod n} {ζ : LL} (hζ : QRoot W i ζ) {x : W.DD T} (hx : ∃ k : ℕ, W.Q ^ k • x ∈ W.N T) :
    Van W T i ζ ((letE i : LetA O n) • x) ↔ Van W T i ζ x := by
  obtain ⟨k, hk⟩ := hx
  have hk' : W.Q ^ k • (letE i : LetA O n) • x ∈ W.N T := by
    rw [smul_comm]; exact (W.N T).smul_mem _ hk
  constructor
  · intro H
    refine van_of_one W T nb hζ hk ?_
    have e : W.Q ^ k • x = W.Q ^ k • (letE i : LetA O n) • x + (1 - letE i : LetA O n) • W.Q ^ k • x := by
      rw [smul_comm (W.Q ^ k) (letE i : LetA O n), ← add_smul, add_sub_cancel, one_smul]
    rw [e]
    refine Submodule.add_mem _ (H k hk') (Submodule.smul_mem_smul ?_ hk)
    rw [mem_vanI, map_sub, map_one, lev_letE, sub_self]
    exact dvd_zero _
  · intro H
    refine van_of_one W T nb hζ hk' ?_
    rw [smul_comm]
    exact Submodule.smul_mem _ _ (H k hk)

include W in
theorem mem_N_iff (x : W.DD T) : x ∈ W.N T ↔ ∀ i, (letE i : LetA O n) • x ∈ W.Nl T i := by
  refine ⟨fun h i => letE_smul_mem W T i h, fun h => ?_⟩
  haveI := neZero_letters W
  have e : (∑ i, letE i : LetA O n) = 1 := Finset.univ_sum_single (1 : LetA O n)
  rw [← one_smul (LetA O n) x, ← e, Finset.sum_smul]
  exact Submodule.sum_mem _ fun i _ => ((mem_Nl_iff W T i _).1 (h i)).1

theorem partB_iff {ι : Type} [Fintype ι] (nb : Module.Basis ι (LetA O n) ↥(W.N T))
    (hO : ∀ ζ : LL, IsPrimitiveRoot ζ (PD.p ^ W.s) → ∃ c : O, algebraMap O LL c = ζ) :
    PartB W T ↔ ∀ x : W.DD T, (∃ k : ℕ, W.Q ^ k • x ∈ W.N T) →
      (x ∈ W.N T ↔ ∀ i ζ, QRoot W i ζ → ∀ k : ℕ, W.Q ^ k • x ∈ W.N T →
        W.Q ^ k • x ∈ vanI W i ζ k • W.N T) := by
  have hr : ∀ i ζ, QRoot W i ζ ↔ IsPrimitiveRoot ζ (PD.p ^ W.s) := fun i ζ =>
    (GlobalTheory.WachHeightTest.qRoot_iff W i ζ).trans ⟨fun h => h.2, fun h => ⟨hO ζ h, h⟩⟩
  constructor
  · intro H x hx
    have hi : ∀ i, MemInv W T i ((letE i : LetA O n) • x) := fun i => by
      obtain ⟨k, hk⟩ := hx
      exact ⟨k, by rw [smul_comm]; exact letE_smul_mem W T i hk⟩
    rw [mem_N_iff W T x]
    refine forall_congr' fun i => ?_
    rw [H i _ (hi i)]
    refine forall_congr' fun ζ => ?_
    rw [← hr i ζ]
    refine imp_congr_right fun hζ => ?_
    rw [memLoc_iff W T nb hζ (hi i), van_letE_iff W T nb hζ hx]
    rfl
  · intro H i y hy
    have he := fixed_of_memInv W T hy
    have hx : ∃ k : ℕ, W.Q ^ k • y ∈ W.N T := by
      obtain ⟨k, hk⟩ := hy
      exact ⟨k, ((mem_Nl_iff W T i _).1 hk).1⟩
    rw [mem_Nl_iff, and_iff_left he, H y hx]
    constructor
    · intro h ζ hζ
      exact (memLoc_iff W T nb ((hr i ζ).2 hζ) hy).2 (h i ζ ((hr i ζ).2 hζ))
    · intro h i' ζ hζ
      by_cases hi : i' = i
      · subst hi
        exact (memLoc_iff W T nb hζ hy).1 (h ζ ((hr _ ζ).1 hζ))
      · exact van_other W T hi ζ he

theorem partAB_iff {ι : Type} [Fintype ι] (nb : Module.Basis ι (LetA O n) ↥(W.N T))
    (hO : ∀ ζ : LL, IsPrimitiveRoot ζ (PD.p ^ W.s) → ∃ c : O, algebraMap O LL c = ζ)
    (M h : ZMod n → ℕ) : PartA W T M h ∧ PartB W T ↔ p5 W T M h := by
  rw [partA_iff, partB_iff W T nb hO, and_assoc]
  rfl

theorem partC_iff {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA] [Algebra O RW]
    {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    (E : EtTie W RA RW inclR φR gR πA) (M h : ℕ) : PartC E T M h ↔ wachInfiniteLevelJumpBound W E T M h := Iff.rfl

end Generic

theorem letterMax_eq {l : ℕ} [Fact l.Prime] (K : FinExt l)
    (m : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ℕ) : letterMax K m = mx m := by
  haveI := letters_neZero K
  unfold letterMax mx
  exact Finset.sup_univ_eq_ciSup m

theorem partAB_iff_good {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (K : FinExt l) (s : ℕ)
    (LL : FinExt l) (hg : Good K s LL) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL))
    (hT : IsCrys (P.PD K) T.ρ) (M h : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ℕ) :
    PartA (H.W K s LL hg) T M h ∧ PartB (H.W K s LL hg) T ↔ p5 (H.W K s LL hg) T M h := by
  obtain ⟨nb⟩ := GlobalTheory.NL.N_basis_loc H K s LL hg T hT
  refine partAB_iff _ T nb (fun ζ hζ => ⟨⟨ζ, ?_⟩, rfl⟩) M h
  exact IsIntegral.of_pow (pow_pos (P.PD K).hp.pos _) (by rw [hζ.pow_eq_one]; exact isIntegral_one)

theorem heights_iff_loc (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (H : LocHW l P)
    (F : LocFon l P AI H) (C : LocCmpT l P AI H F) :
    HeightsFromJumps l P AI H F C ↔
      (∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (hg : Good K s LL), P5W (H.W K s LL hg)) ∧
      (∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (hg : Good K s LL),
        WachInfiniteLevelBound (H.W K s LL hg) (F.E K s LL hg).tie) := by
  constructor
  · intro h
    refine ⟨fun K s LL hg T M h' hT hJ => ?_, fun K s LL hg T M h' hT hJ => ?_⟩
    · have := h K s LL hg T hT M h' ((jumps_iff _ T M h').2 hJ)
      exact (partAB_iff_good H K s LL hg T hT M h').1 ⟨this.1, this.2.1⟩
    · have := (h K s LL hg T hT M h' ((jumps_iff _ T M h').2 hJ)).2.2
      rwa [letterMax_eq, letterMax_eq, partC_iff] at this
  · rintro ⟨h1, h2⟩ K s LL hg T hT M h' hJ
    have hJ' := (jumps_iff _ T M h').1 hJ
    have := (partAB_iff_good H K s LL hg T hT M h').2 (h1 K s LL hg T M h' hT hJ')
    refine ⟨this.1, this.2, ?_⟩
    rw [letterMax_eq, letterMax_eq, partC_iff]
    exact h2 K s LL hg T M h' hT hJ'

theorem heights_iff (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (C : CmpOf D.loc D.locA HW F) :
    (∀ (l : ℕ) [Fact l.Prime], HeightsFromJumps l (D.loc l) (D.locA l) (HW l) (F l) (C l)) ↔
      P5 D HW F ∧ p5eL D.loc D.locA HW F :=
  ⟨fun h => ⟨fun l _ => ((heights_iff_loc l _ _ _ _ _).1 (h l)).1,
      fun l _ => ((heights_iff_loc l _ _ _ _ _).1 (h l)).2⟩,
    fun h l _ => (heights_iff_loc l _ _ _ _ _).2 ⟨h.1 l, h.2 l⟩⟩

end GlobalTheory.HeightsClauseCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeightsFromJumpsIff
noncomputable section

namespace GlobalTheory.HeightsFromJumpsCompare

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.IndefiniteRowSideFullHecke

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

variable {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}

end Generic


open TensorProduct in
theorem _root_.GlobalTheory.HeightsFromJumpsCompare.heightsFromJumps_iff (l : ℕ) [Fact l.Prime] (P : _root_.Formalism.BasicNotions.LocPrime l) (AI : _root_.Formalism.BasicNotions.LocAinf l P)
    (H : _root_.Formalism.BasicNotions.LocHW l P) (F : _root_.Formalism.BasicNotions.LocFon l P AI H) (C : _root_.Formalism.BasicNotions.LocCmpT l P AI H F) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.PointRingCommRing.HeightsFromJumps l P AI H F C ↔
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.LocalRingStructure.HeightsFromJumps l P AI H F C :=
  Iff.rfl

end GlobalTheory.HeightsFromJumpsCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantWachModuleBasisOfNonnegJumps
open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WachFrame

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {f : ℕ}
    (W : LocWach PD LL O v f) {T : LocLat G Qp LL O} {n : ℕ}

theorem γD_smulA (g : W.Gam) (a : LetA O f) (x : W.DD T) :
    W.γD T g (a • x) = W.γA g a • W.γD T g x := by
  have := W.γD_smul T g (algebraMap (LetA O f) W.EE a) x
  rwa [algebraMap_smul, W.γE_ext, algebraMap_smul] at this

theorem coe_eq_sum (b : Module.Basis (Fin n) (LetA O f) ↥(W.N T)) (y : ↥(W.N T)) :
    (y : W.DD T) = ∑ m, b.repr y m • (b m : W.DD T) := by
  have h1 := congrArg Subtype.val (b.sum_repr y)
  simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at h1
  exact h1.symm

theorem coord_fixed (b : Module.Basis (Fin n) (LetA O f) ↥(W.N T)) (hb : ∀ k, (b k : W.DD T) ∈ W.NΔ T)
    (y : ↥(W.N T)) (δ : W.Gam) (hδ : δ ∈ W.DelF) (hy : W.γD T δ (y : W.DD T) = y) (m : Fin n) :
    W.γA δ (b.repr y m) = b.repr y m := by
  have e : ∑ m, W.γA δ (b.repr y m) • b m = y := by
    apply Subtype.ext
    have h1 : W.γD T δ (y : W.DD T) = ∑ m, W.γA δ (b.repr y m) • (b m : W.DD T) := by
      set_option synthInstance.maxHeartbeats 100000 in
        conv_lhs => rw [coe_eq_sum W b y, map_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [γD_smulA, (hb m).2 δ hδ]
    simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul]
    exact h1.symm.trans hy
  have h2 := congrFun (b.repr_sum_self fun m => W.γA δ (b.repr y m)) m
  rw [e] at h2
  exact h2.symm

variable (l : ℕ) [Fact l.Prime] [Algebra ℤ_[l] O]

theorem exists_inc (hI : ∀ a : O⟦X⟧, (∀ δ ∈ W.DelF, W.γ₀ δ a = a) → ∃ y, inc l O y = a)
    (b : Module.Basis (Fin n) (LetA O f) ↥(W.N T)) (hb : ∀ k, (b k : W.DD T) ∈ W.NΔ T)
    (y : ↥(W.N T)) (hy : ∀ δ ∈ W.DelF, W.γD T δ (y : W.DD T) = y) (m : Fin n) (i : ZMod f) :
    ∃ z, inc l O z = b.repr y m i :=
  hI _ fun δ hδ => congrFun (coord_fixed W b hb y δ hδ (hy δ hδ) m) i

theorem exists_phi_matrix (hI : ∀ a : O⟦X⟧, (∀ δ ∈ W.DelF, W.γ₀ δ a = a) → ∃ y, inc l O y = a)
    (b : Module.Basis (Fin n) (LetA O f) ↥(W.N T)) (hb : ∀ k, (b k : W.DD T) ∈ W.NΔ T)
    (hφ : ∀ x ∈ W.N T, W.φD T x ∈ W.N T) :
    ∃ Pm : ZMod f → Matrix (Fin n) (Fin n) O⟦X⟧, ∀ k, W.φD T (b k : W.DD T) =
      ∑ m, (fun i => inc l O (Pm i m k) : LetA O f) • (b m : W.DD T) := by
  have h : ∀ i m k, ∃ z, inc l O z = b.repr ⟨W.φD T (b k : W.DD T), hφ _ (b k).2⟩ m i := fun i m k =>
    exists_inc W l hI b hb _ (fun δ hδ => by
      change W.γD T δ (W.φD T (b k : W.DD T)) = W.φD T (b k : W.DD T)
      rw [← W.φγ_comm, (hb k).2 δ hδ]) m i
  choose Pm hPm using h
  refine ⟨fun i => Matrix.of (Pm i), fun k => ?_⟩
  refine (coe_eq_sum W b ⟨W.φD T (b k : W.DD T), hφ _ (b k).2⟩).trans (Finset.sum_congr rfl fun m _ => ?_)
  congr 1
  funext i
  exact (hPm i m k).symm

theorem exists_gam_matrix (hI : ∀ a : O⟦X⟧, (∀ δ ∈ W.DelF, W.γ₀ δ a = a) → ∃ y, inc l O y = a)
    (b : Module.Basis (Fin n) (LetA O f) ↥(W.N T)) (hb : ∀ k, (b k : W.DD T) ∈ W.NΔ T) (γ : W.Gam) :
    ∃ Dm : ZMod f → Matrix (Fin n) (Fin n) O⟦X⟧, ∀ k, W.γD T γ (b k : W.DD T) =
      ∑ m, (fun i => inc l O ((1 + (X : O⟦X⟧) • Dm i) m k) : LetA O f) • (b m : W.DD T) := by
  have hγ : ∀ k, W.γD T γ (b k : W.DD T) ∈ W.N T := fun k => W.N_Γ T γ _ (b k).2
  have h : ∀ i m k, ∃ d : O⟦X⟧, inc l O ((1 : Matrix (Fin n) (Fin n) O⟦X⟧) m k + X * d) =
      b.repr ⟨W.γD T γ (b k : W.DD T), hγ k⟩ m i := by
    intro i m k
    obtain ⟨z, hz⟩ := exists_inc W l hI b hb ⟨W.γD T γ (b k : W.DD T), hγ k⟩ (fun δ hδ => by
      change W.γD T δ (W.γD T γ (b k : W.DD T)) = W.γD T γ (b k : W.DD T)
      rw [← W.γD_mul, mul_comm, W.γD_mul, (hb k).2 δ hδ]) m i
    obtain ⟨y, hy, e⟩ := W.N_π T γ _ (b k).2
    have e1 : (⟨W.γD T γ (b k : W.DD T), hγ k⟩ : ↥(W.N T)) = b k + (letπ : LetA O f) • (⟨y, hy⟩ : ↥(W.N T)) :=
      Subtype.ext (eq_add_of_sub_eq' e)
    have e2 : constantCoeff (z - (1 : Matrix (Fin n) (Fin n) O⟦X⟧) m k) = 0 := by
      rw [map_sub, ← (pi0Subst_laws_hold l O).2.2.2.2.2.1 z, hz, e1, map_add (f := _), map_smul, b.repr_self]
      by_cases hmk : m = k
      · subst hmk
        simp [letπ]
      · simp [letπ, hmk, Finsupp.single_eq_of_ne hmk]
    obtain ⟨d, hd⟩ := X_dvd_iff.2 e2
    exact ⟨d, by rw [← hd, add_sub_cancel, hz]⟩
  choose Dm hDm using h
  refine ⟨fun i => Matrix.of (Dm i), fun k => ?_⟩
  refine (coe_eq_sum W b ⟨W.γD T γ (b k : W.DD T), hγ k⟩).trans (Finset.sum_congr rfl fun m _ => ?_)
  congr 1
  funext i
  exact (hDm i m k).symm

theorem mem_of_letters (x : W.DD T) (h : ∀ i, (letE i : LetA O f) • x ∈ W.N T) : x ∈ W.N T := by
  haveI := GlobalTheory.WachLettersCompare.neZero_letters W
  have e : (∑ i, letE i : LetA O f) = 1 := Finset.univ_sum_single (1 : LetA O f)
  rw [← one_smul (LetA O f) x, ← e, Finset.sum_smul]
  exact Submodule.sum_mem _ fun i _ => h i

theorem phi_mem (hH : GlobalTheory.WachUse.Heights W) (U : ZMod f → Multiset ℤ)
    (hU : GlobalTheory.AdmLoc.CrysWith PD W.emb T.ρ U) (hpos : ∀ i, ∀ u ∈ U i, 0 ≤ u) :
    ∀ x ∈ W.N T, W.φD T x ∈ W.N T := by
  intro x hx
  refine mem_of_letters W _ fun i => ?_
  have := (hH T U (fun _ => 0) (fun i => ((U i).map Int.toNat).sum) hU (fun i u hu => ?_) i).1 x hx
  · simpa using this
  · refine ⟨by simpa using hpos i u hu, ?_⟩
    have h1 : u.toNat ≤ ((U i).map Int.toNat).sum := Multiset.le_sum_of_mem (Multiset.mem_map_of_mem _ hu)
    exact (Int.self_le_toNat u).trans (by exact_mod_cast h1)

end Generic

theorem exists_rem {l : ℕ} [Fact l.Prime] (LL : FinExt l) (g : (↥(OL LL))⟦X⟧) :
    ∃ a : ↥(OL LL), (X - C (l : ↥(OL LL))) ∣ g - C a := by
  obtain ⟨_, hc, hl⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
  obtain ⟨g₁, a, e⟩ := (linear_division_holds ↥(OL LL) (maximalIdeal ↥(OL LL)) (l : ↥(OL LL))
    ((mem_maximalIdeal _).2 hl)).1 g
  exact ⟨a, g₁, by rw [e, add_sub_cancel_right]⟩

theorem exists_frame : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (U : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Multiset ℤ) (n : ℕ), GlobalTheory.AdmLoc.CrysWith ((D.loc l).PD K) ((HW l).W K 1 LL hA.2.2).emb T.ρ U → (∀ i, ∀ u ∈ U i, 0 ≤ u) → Module.finrank ↥(OL LL) ↥T.L.T = n → ∀ γ : ((HW l).W K 1 LL hA.2.2).Gam, ∃ (b : Module.Basis (Fin n) (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥(((HW l).W K 1 LL hA.2.2).N T)) (N : Lat (ZMod (Module.finrank ℚ_[l] ↥(K0 K))) n ↥(OL LL)), IsFrame ((HW l).W K 1 LL hA.2.2) T γ b N := by
  intro D HW F Cm l _ K LL hA T U n hU hpos hn γ
  have hR := GlobalTheory.T.wachRingFacts_unramified_levelOne (HW l) K LL hA
  have hJ := (GlobalTheory.HeightsClauseCompare.heights_iff D HW F Cm).2
    ⟨GlobalTheory.NL.Heights.heights_from_jumps D HW F Cm, GlobalTheory.NL.SandJumps.main D HW F Cm⟩
  have hH := GlobalTheory.WachUse.HeightsProof.heights_of_caseA (D.locA l) (HW l) (F l) (Cm l) ⟨D.locT l⟩
    ((GlobalTheory.HeightsFromJumpsCompare.heightsFromJumps_iff l _ _ _ _ _).2 (hJ l)) K LL hA
  obtain ⟨b₀⟩ := GlobalTheory.WachFree.wach_free (D.loc l) (HW l) K 1 LL hA.2.2 T hU.1
  obtain ⟨b, hb⟩ := GlobalTheory.WachTie.exists_invariant_basis _ T hR.2.2.2.2.2 ⟨b₀.reindex (finCongr hn)⟩
  obtain ⟨Pm, hP⟩ := exists_phi_matrix _ l (fun a => (hR.2.2.2.2.1 a).1) b hb (phi_mem _ hH U hU hpos)
  obtain ⟨Dm, hD⟩ := exists_gam_matrix _ l (fun a => (hR.2.2.2.2.1 a).1) b hb γ
  choose Th hTh using fun i a c => exists_rem LL (Dm i a c)
  exact ⟨b, ⟨Pm, Dm, fun i => Matrix.of (Th i)⟩, hb, hP, hD, hTh⟩

end GlobalTheory.WachFrame

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantWachModuleBasisOfNonnegJumpsStatement
open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invariant_wachModule_basis_of_nonneg_jumps : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (U : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Multiset ℤ) (n : ℕ), GlobalTheory.AdmLoc.CrysWith ((D.loc l).PD K) ((HW l).W K 1 LL hA.2.2).emb T.ρ U → (∀ i, ∀ u ∈ U i, 0 ≤ u) → Module.finrank ↥(OL LL) ↥T.L.T = n → ∀ γ : ((HW l).W K 1 LL hA.2.2).Gam, ∃ (b : Module.Basis (Fin n) (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥(((HW l).W K 1 LL hA.2.2).N T)) (N : Lat (ZMod (Module.finrank ℚ_[l] ↥(K0 K))) n ↥(OL LL)), IsFrame ((HW l).W K 1 LL hA.2.2) T γ b N := by
  first | exact @GlobalTheory.WachFrame.exists_frame | exact GlobalTheory.WachFrame.exists_frame | (intros; apply GlobalTheory.WachFrame.exists_frame <;> assumption)
end
