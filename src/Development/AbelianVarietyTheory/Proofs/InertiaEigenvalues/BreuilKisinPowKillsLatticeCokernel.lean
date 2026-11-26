module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EulerEAddSmulMemEisensteinShiftGraded
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VPowLatticeLeImageAddLPowOfFiniteCokernel
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeInfSubspaceBaseChangeDvr
public import Formalism.PadicSubsetSums.StableGradedCounts.ARCReuse
public import Formalism.PadicSubsetSums.StableGradedCounts.PadicValCardGL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MaxFrobeniusOrbitLengthDiffBoundsZmod

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumIsotypicProjectorsEqId
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumIsotypicProjectorsEqId
open PowerSeries GlobalTheory.BK

namespace GlobalTheory.CokerL

theorem sum_zmod_val_eq_sum_range {M : Type} [AddCommMonoid M] (e : ℕ) [NeZero e] (f : ℕ → M) :
    ∑ c : ZMod e, f c.val = ∑ i ∈ Finset.range e, f i := by
  refine Finset.sum_bij (fun c _ => c.val) (fun c _ => Finset.mem_range.2 (ZMod.val_lt c))
    (fun c _ d _ h => ZMod.val_injective e h) (fun i hi => ?_) (fun _ _ => rfl)
  exact ⟨(i : ZMod e), Finset.mem_univ _, ZMod.val_cast_of_lt (Finset.mem_range.1 hi)⟩

theorem sum_zmod_pow_eq_zero {K : Type} [Field K] (e : ℕ) [NeZero e] {r : K} (hr : r ^ e = 1)
    (h1 : r ≠ 1) : ∑ c : ZMod e, r ^ c.val = 0 := by
  rw [sum_zmod_val_eq_sum_range e (fun i => r ^ i), geom_sum_eq h1, hr, sub_self, zero_div]

theorem root_inertia_ne_one {K : Type} [NormedField K] {l e a : ℕ} [Fact l.Prime]
    [NormedAlgebra ℚ_[l] K] [NeZero a] [TameDescentExponentData K l e a] {ζ : rootsOfUnity e K} (h : ζ ≠ 1)
    (τ : ZMod a) : (TameGal.inertia ζ : TameGal K l e a).root τ ≠ 1 := by
  intro h1
  apply h
  have h2 : powL l (-τ) ζ = 1 := Subtype.ext (Units.ext h1)
  have h3 := powL_add l τ (-τ) ζ
  rw [h2, map_one, add_neg_cancel, powL_zero] at h3
  exact h3

theorem sum_isoProj : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime]
    [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (P : PhiMod O K l e a ι)
    (Δ : Descent P) (v : Vec K a ι), ∑ c : ZMod e, GlobalTheory.CokerL.isoProj Δ c v = v := by
  intro O K _ _ _ _ _ l e a ι _ _ _ _ _ _ _ P Δ v
  letI := Fintype.ofFinite (rootsOfUnity e K)
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  have he : (e : K) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne e)
  simp only [isoProj, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply]
  rw [← Finset.smul_sum, Finset.sum_comm]
  classical
  rw [Finset.sum_eq_single (1 : rootsOfUnity e K)]
  · ext1 τ
    simp only [map_one, TameGal.root_one, inv_one, one_pow, Pi.smul_apply, Finset.sum_apply,
      diagScale_apply, one_smul, Module.End.one_apply, Finset.sum_const, Finset.card_univ, ZMod.card]
    rw [← Nat.cast_smul_eq_nsmul K, smul_smul, inv_mul_cancel₀ he, one_smul]
  · intro ζ _ hζ
    ext1 τ
    simp only [Finset.sum_apply, diagScale_apply, Pi.zero_apply]
    rw [← Finset.sum_smul, sum_zmod_pow_eq_zero e (by rw [inv_pow, TameGal.root_pow, inv_one])
      (fun h => root_inertia_ne_one hζ τ (inv_eq_one.1 h)), zero_smul]
  · simp

end GlobalTheory.CokerL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumIsotypicProjectorsEqIdStatement
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_isotypicProjectors_eq_id : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (P : PhiMod O K l e a ι) (Δ : Descent P) (v : Vec K a ι), ∑ c : ZMod e, GlobalTheory.CokerL.isoProj Δ c v = v := by
  first | exact @GlobalTheory.CokerL.sum_isoProj | exact GlobalTheory.CokerL.sum_isoProj | (intros; apply GlobalTheory.CokerL.sum_isoProj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemPrimePowLatticeOfXPowSmulMem
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemPrimePowLatticeOfXPowSmulMem
open PowerSeries GlobalTheory.BK

namespace GlobalTheory.CokerL

open Matrix

theorem inv_mul_coeff_eq_of_X_pow_mul {K : Type} [Field K] {N : ℕ} {c : K} (hc : c ≠ 0)
    {f g : K⟦X⟧} (h : X ^ N * f = c • g) (k : ℕ) : c⁻¹ * coeff k f = coeff (k + N) g := by
  have := congrArg (coeff (k + N)) h
  rw [coeff_X_pow_mul, coeff_smul, smul_eq_mul] at this
  rw [this, inv_mul_cancel_left₀ hc]

theorem mem_lpow_L_of_vpow_smul (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime]
    [NormedAlgebra ℚ_[l] K] (P : PhiMod O K l e a ι) (n b : ℕ) (w z : Vec K a ι) (hw : w ∈ P.L)
    (hz : z ∈ P.L) (h : ((X : K⟦X⟧) ^ e) ^ n • w = (l : K) ^ b • z) :
    ∃ z' ∈ P.L, w = (l : K) ^ b • z' := by
  have hc : (l : K) ^ b ≠ 0 := pow_ne_zero _ (l_ne_zero l)
  refine ⟨((l : K) ^ b)⁻¹ • w, mem_tot.2 fun τ => P.mem_extc_iff.2 fun i => ?_,
    (smul_inv_smul₀ hc w).symm⟩
  have hm := P.mem_extc_iff.1 (mem_tot.1 hw τ)
  have hm' := P.mem_extc_iff.1 (mem_tot.1 hz τ)
  have hi : X ^ (e * n) * (P.mxInv τ *ᵥ w τ) i = (l : K) ^ b • (P.mxInv τ *ᵥ z τ) i := by
    have hτ := congrArg (fun v : Vec K a ι => (P.mxInv τ *ᵥ v τ) i) h
    simp only [Pi.smul_apply, Matrix.mulVec_smul, smul_eq_mul] at hτ
    rw [pow_mul]
    exact hτ
  rw [mem_A]
  intro k
  rw [Pi.smul_apply, Matrix.mulVec_smul, Pi.smul_apply, coeff_smul, smul_eq_mul,
    inv_mul_coeff_eq_of_X_pow_mul hc hi]
  exact mem_A.1 (hm' i) _

end GlobalTheory.CokerL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemPrimePowLatticeOfXPowSmulMemStatement
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_prime_pow_lattice_of_X_pow_smul_mem : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] (P : PhiMod O K l e a ι) (n b : ℕ) (w z : Vec K a ι), w ∈ P.L → z ∈ P.L → ((X : K⟦X⟧) ^ e) ^ n • w = (l : K) ^ b • z → ∃ z' ∈ P.L, w = (l : K) ^ b • z' := by
  first | exact @GlobalTheory.CokerL.mem_lpow_L_of_vpow_smul | exact GlobalTheory.CokerL.mem_lpow_L_of_vpow_smul | (intros; apply GlobalTheory.CokerL.mem_lpow_L_of_vpow_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsotypicProjectorMemBreuilKisinLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsotypicProjectorMemBreuilKisinLattice
open PowerSeries GlobalTheory.BK

namespace GlobalTheory.CokerL

theorem isoProj_mem_L : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (P : PhiMod O K l e a ι) (Δ : Descent P) (c : ZMod e) (v : Vec K a ι), v ∈ P.L → GlobalTheory.CokerL.isoProj Δ c v ∈ P.L := by
  intro O K _ _ _ _ _ l e a ι _ _ _ _ _ _ _ P Δ c v hv
  letI := Fintype.ofFinite (rootsOfUnity e K)
  have key : ∀ s : ZMod a → K, (∀ τ, ‖s τ‖ ≤ 1) → ∀ w ∈ P.L, diagScale K a ι s w ∈ P.L := by
    intro s hs w hw
    have h : diagScale K a ι s w = (fun τ => C (s τ)) • w := by
      ext τ i
      simp [diagScale_apply, Pi.smul_apply', PowerSeries.smul_eq_C_mul]
    rw [h]
    refine P.smul_tot_mem_ext (fun τ => mem_A.2 fun n => ?_) hw
    rw [coeff_C]
    split_ifs
    · exact hs τ
    · simp
  have hnd : ¬ l ∣ e := by
    intro h
    have h1 : l ∣ e + 1 := by
      rw [TameDescentExponentData.succ_eq (K := K) (l := l) (e := e) (a := a)]
      exact dvd_pow_self l (NeZero.ne a)
    exact (Fact.out : l.Prime).one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h).1 h1))
  have he : ‖(e : K)⁻¹‖ ≤ 1 := by
    rw [norm_inv, norm_natCast_eq l, Padic.norm_natCast_eq_one_iff.2
      ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hnd), inv_one]
  have hsc : isoProj Δ c v = diagScale K a ι (fun _ => (e : K)⁻¹) (∑ ζ : rootsOfUnity e K,
      diagScale K a ι (fun τ => ((TameGal.inertia ζ : TameGal K l e a).root τ)⁻¹ ^ c.val)
        (Δ.act (TameGal.inertia ζ) v)) := by
    simp only [isoProj, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply]
    rfl
  rw [hsc]
  refine key _ (fun _ => he) _ (Submodule.sum_mem _ fun ζ _ => key _ (fun τ => ?_) _ ?_)
  · rw [norm_pow, norm_inv, TameGal.norm_root, inv_one, one_pow]
  · exact Δ.act_mem_ext _ le_rfl rot_A hv

end GlobalTheory.CokerL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsotypicProjectorMemBreuilKisinLatticeStatement
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotypicProjector_mem_breuilKisinLattice : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (P : PhiMod O K l e a ι) (Δ : Descent P) (c : ZMod e) (v : Vec K a ι), v ∈ P.L → GlobalTheory.CokerL.isoProj Δ c v ∈ P.L := by
  first | exact @GlobalTheory.CokerL.isoProj_mem_L | exact GlobalTheory.CokerL.isoProj_mem_L | (intros; apply GlobalTheory.CokerL.isoProj_mem_L <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsotypicProjectorMemIsotypicPartExplicit
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsotypicProjectorMemIsotypicPartExplicit
noncomputable section

namespace GlobalTheory.CokerL

open PowerSeries GlobalTheory.BK

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a]


omit [NeZero e] in
theorem act_inertia_diagScale {P : PhiMod O K l e a ι} (Δ : Descent P) (ξ : rootsOfUnity e K)
    (s : ZMod a → K) (w : Vec K a ι) :
    Δ.act (TameGal.inertia ξ) (diagScale K a ι s w) =
      diagScale K a ι s (Δ.act (TameGal.inertia ξ) w) := by
  have h1 (u : Vec K a ι) : diagScale K a ι s u = (fun τ => (C (s τ) : K⟦X⟧)) • u := by
    ext τ i : 2
    simp [diagScale_apply, smul_eq_C_mul]
  have h2 : ringAct (TameGal.inertia ξ : TameGal K l e a) (fun τ => (C (s τ) : K⟦X⟧)) =
      fun τ => C (s τ) := by
    ext τ n
    rw [ringAct_apply, TameGal.shift_inertia, sub_zero, coeff_rescale, coeff_C]
    split_ifs with h <;> simp [h]
  rw [h1, h1, Δ.act_smul_tot, h2]

theorem isoProj_mem_isotypic {P : PhiMod O K l e a ι} (Δ : Descent P) (c : ZMod e)
    (v : Vec K a ι) : isoProj Δ c v ∈ Δ.isotypic c := by
  letI := Fintype.ofFinite (rootsOfUnity e K)
  unfold isoProj
  rw [LinearMap.smul_apply]
  refine Submodule.smul_mem _ _ ?_
  intro ξ τ
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, map_sum, act_inertia_diagScale,
    Finset.sum_apply, diagScale_apply, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft ξ) _ _ fun ζ => ?_
  rw [Equiv.coe_mulLeft, ← Module.End.mul_apply, ← map_mul, ← map_mul, smul_smul]
  congr 1
  rw [map_mul, TameGal.root_mul, TameGal.shift_inertia, sub_zero, ← mul_pow, mul_inv,
    mul_inv_cancel_left₀ (TameGal.root_ne_zero _ _)]

theorem isoProj_mem_isotypic' : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime]
    [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (P : PhiMod O K l e a ι)
    (Δ : Descent P) (c : ZMod e) (v : Vec K a ι), GlobalTheory.CokerL.isoProj Δ c v ∈ Δ.isotypic c :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Δ c v => isoProj_mem_isotypic Δ c v

end GlobalTheory.CokerL
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsotypicProjectorMemIsotypicPartExplicitStatement
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotypicProjector_mem_isotypicPart_explicit : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (P : PhiMod O K l e a ι) (Δ : Descent P) (c : ZMod e) (v : Vec K a ι), GlobalTheory.CokerL.isoProj Δ c v ∈ Δ.isotypic c := by
  first | exact @GlobalTheory.CokerL.isoProj_mem_isotypic' | exact GlobalTheory.CokerL.isoProj_mem_isotypic' | (intros; apply GlobalTheory.CokerL.isoProj_mem_isotypic' <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimePowKillsFiniteLengthIntegralPowerSeri
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimePowKillsFiniteLengthIntegralPowerSeri
open PowerSeries GlobalTheory.BK

namespace GlobalTheory.PowKill

theorem exists_pow_smul_eq_zero {R : Type} [CommRing R] {x : R}
    (hx : ∀ I : Ideal R, I.IsMaximal → x ∈ I) {M : Type} [AddCommGroup M] [Module R M]
    (h : IsFiniteLength R M) : ∃ m : ℕ, ∀ q : M, (x ^ m) • q = 0 := by
  induction h with
  | of_subsingleton => exact ⟨0, fun q => Subsingleton.elim _ _⟩
  | @of_simple_quotient M _ _ N hs _ ih =>
    obtain ⟨m, hm⟩ := ih
    obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.1 hs
    refine ⟨m + 1, fun q => ?_⟩
    have h1 : x • q ∈ N := by
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
      apply e.injective
      obtain ⟨r, hr⟩ := Submodule.Quotient.mk_surjective I (e (Submodule.Quotient.mk q))
      rw [map_smul, ← hr, map_zero, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
        smul_eq_mul]
      exact I.mul_mem_right r (hx I hI)
    have h2 := hm ⟨x • q, h1⟩
    rw [pow_succ, mul_smul]
    exact congrArg Subtype.val h2

section

variable {O : Type} [CommRing O] (l : ℕ) [Fact l.Prime]

theorem isUnit_l_mul_add_one (K : Type) [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (c : O) : IsUnit ((l : O) * c + 1) := by
  set u := algebraMap O K ((l : O) * c + 1) with hu
  have hlc : ‖(l : K) * algebraMap O K c‖ < 1 := by
    rw [norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (norm_algebraMap_le c))
      (norm_l_lt_one (K := K) l)
  have hu1 : ‖u‖ = 1 := by
    have : u = (l : K) * algebraMap O K c + 1 := by simp [hu]
    rw [this, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact hlc.ne)]
    rw [norm_one]; exact max_eq_right hlc.le
  have hu0 : u ≠ 0 := by intro h; rw [h, norm_zero] at hu1; exact zero_ne_one hu1
  obtain ⟨b, hb⟩ := (IsUnitBall.mem_range_iff (O := O) (u⁻¹)).2 (by rw [norm_inv, hu1, inv_one])
  refine isUnit_iff_exists_inv.2 ⟨b, IsUnitBall.inj (O := O) (K := K) ?_⟩
  rw [map_mul, hb, ← hu, mul_inv_cancel₀ hu0, map_one]

theorem l_mem_maximal {K : Type} [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (I : Ideal (A O K)) (hI : I.IsMaximal) : (l : A O K) ∈ I := by
  have hj : (l : A O K) ∈ Ideal.jacobson (⊥ : Ideal (A O K)) := by
    rw [Ideal.mem_jacobson_bot]
    intro y
    have key : IsUnit ((equivA O K).symm ((l : A O K) * y + 1)) := by
      rw [map_add (f := _), map_mul, map_natCast, map_one, PowerSeries.isUnit_iff_constantCoeff, map_add (f := _),
        map_mul, map_natCast, map_one]
      exact isUnit_l_mul_add_one l K _
    simpa using key.map (equivA O K).toRingEquiv.toRingHom
  have hle : Ideal.jacobson (⊥ : Ideal (A O K)) ≤ I := by
    rw [Ideal.jacobson]; exact sInf_le ⟨bot_le, hI⟩
  exact hle hj

end

theorem main : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] (Mo : Type) [AddCommGroup Mo]
    [Module (A O K) Mo], IsFiniteLength (A O K) Mo → ∃ m : ℕ, ∀ q : Mo, ((l : A O K) ^ m) • q = 0 :=
  fun O K _ _ _ _ _ l _ _ _ _ _ h => exists_pow_smul_eq_zero (l_mem_maximal (K := K) l) h

end GlobalTheory.PowKill
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimePowKillsFiniteLengthIntegralPowerSeriStatement
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prime_pow_kills_finiteLength_integralPowerSeries : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] (Mo : Type) [AddCommGroup Mo] [Module (A O K) Mo], IsFiniteLength (A O K) Mo → ∃ m : ℕ, ∀ q : Mo, ((l : A O K) ^ m) • q = 0 := by
  first | exact @GlobalTheory.PowKill.main | exact GlobalTheory.PowKill.main | (intros; apply GlobalTheory.PowKill.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EulerDerivationPreservesBreuilKisinSumSubmodule
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EulerDerivationPreservesBreuilKisinSumSubmodule
open PowerSeries GlobalTheory.BK

namespace GlobalTheory.CokerL.Tconn

theorem N_vpow {K : Type} [NormedField K] (e A' : ℕ) :
    N K (((X : K⟦X⟧) ^ e) ^ A') = ((e * A' : ℕ) : K⟦X⟧) * ((X : K⟦X⟧) ^ e) ^ A' := by
  ext n
  rw [coeff_N, ← pow_mul, ← map_natCast (C (R := K)), coeff_C_mul, coeff_X_pow]
  split_ifs with h
  · subst h; simp
  · simp

theorem N_lpow {K : Type} [NormedField K] (l b : ℕ) : N K ((l : K⟦X⟧) ^ b) = 0 := by
  rw [← Nat.cast_pow]; exact Derivation.map_natCast _ _

theorem part_top {K O κ : Type} {a : ℕ} [NormedField K] [CommRing O] [Algebra O K]
    (V : Submodule O (Vec K a κ)) : GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.part ⊤ V = V := by
  ext v; simp [GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.part]

end GlobalTheory.CokerL.Tconn

theorem GlobalTheory.CokerL.Tsub_conn : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (η H : ℕ) (D₁ : BKDat O K l e a ι η H) (D₂ : BKDat O K l e a κ η H) (F : BKHom D₁ D₂) (A' b : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.Reduction O K l e a → ∀ x ∈ GlobalTheory.CokerL.Tsub F A' b, D₂.conn x ∈ GlobalTheory.CokerL.Tsub F A' b := by
  intro O K _ _ _ _ _ l e a ι _ _ _ _ _ _ _ κ _ _ η H D₁ D₂ F A' b hred x hx
  have hIS := (hred.2.2 ι κ η H D₁ D₂ F).2.1
  have hMH := (hred.2.1 κ η H D₂).1
  have hvS : ((X : K⟦X⟧) ^ e) ^ A' ∈ S O K e := pow_mem (pow_mem HasU.X_mem e) A'
  have hHigh : ∀ (f : K⟦X⟧), f ∈ S O K e → ∀ q ∈ GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.MMHigh D₂.toPhiMod,
      f • q ∈ GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.MMHigh D₂.toPhiMod := fun f hf q hq =>
    (GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.SHigh O K l e • D₂.MM).smul_mem (⟨f, hf⟩ : S O K e) hq
  have hnat : ∀ (n : ℕ) (q : Vec K a κ) (V : Submodule O (Vec K a κ)), q ∈ V → ((n : K⟦X⟧)) • q ∈ V :=
    fun n q V hq => by
      rw [Nat.cast_smul_eq_nsmul]; exact V.nsmul_mem hq n
  obtain ⟨x12, h12, x3, h3, rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨x1, h1, x2, h2, rfl⟩ := Submodule.mem_sup.1 h12
  rw [map_add (f := _), map_add (f := _)]
  refine add_mem (add_mem ?_ ?_) ?_
  · obtain ⟨y, hy, rfl⟩ := h1
    change D₂.toPhiMod.conn (((X : K⟦X⟧) ^ e) ^ A' • y) ∈ _
    rw [PhiMod.conn_smul, GlobalTheory.CokerL.Tconn.N_vpow, mul_smul]
    refine add_mem ?_ ?_
    · have : ((e * A' : ℕ) : K⟦X⟧) • y ∈ (F.imL.restrictScalars O) := hnat _ _ _ hy
      rw [smul_comm]
      exact Submodule.mem_sup_left (Submodule.mem_sup_left ⟨_, this, rfl⟩)
    · have hc := hIS y (by
        rw [GlobalTheory.CokerL.Tconn.part_top, GlobalTheory.CokerL.Tconn.part_top]
        exact Submodule.mem_sup_left hy)
      rw [GlobalTheory.CokerL.Tconn.part_top, GlobalTheory.CokerL.Tconn.part_top] at hc
      obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.1 hc
      rw [← hpq, smul_add]
      exact add_mem (Submodule.mem_sup_left (Submodule.mem_sup_left ⟨p, hp, rfl⟩))
        (Submodule.mem_sup_right (hHigh _ hvS q hq))
  · obtain ⟨z, hz, rfl⟩ := h2
    change D₂.toPhiMod.conn (((l : K⟦X⟧) ^ b) • z) ∈ _
    rw [PhiMod.conn_smul, GlobalTheory.CokerL.Tconn.N_lpow, zero_smul, zero_add]
    have hzM : z ∈ D₂.MM := PhiMod.ext_mono _ (A_le_S l e) hz
    have hc : D₂.conn z ∈ GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.part ⊤ (D₂.MM.restrictScalars O) := by
      rw [GlobalTheory.CokerL.Tconn.part_top]
      exact BKDat.conn_mem_MM D₂ hzM
    rw [hMH.MM_eq, GlobalTheory.CokerL.Tconn.part_top, GlobalTheory.CokerL.Tconn.part_top] at hc
    obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.1 hc
    change (l : K⟦X⟧) ^ b • D₂.toPhiMod.conn z ∈ _
    rw [← hpq, smul_add]
    refine add_mem (Submodule.mem_sup_left (Submodule.mem_sup_right ⟨p, hp, rfl⟩)) ?_
    refine Submodule.mem_sup_right ?_
    rw [← Nat.cast_pow]
    exact hnat _ _ _ hq
  · have := hMH.conn_high x3 (by rw [GlobalTheory.CokerL.Tconn.part_top]; exact h3)
    rw [GlobalTheory.CokerL.Tconn.part_top] at this
    exact Submodule.mem_sup_right this
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EulerDerivationPreservesBreuilKisinSumSubmoduleStatement
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eulerDerivation_preserves_breuilKisin_sum_submodule : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (η H : ℕ) (D₁ : BKDat O K l e a ι η H) (D₂ : BKDat O K l e a κ η H) (F : BKHom D₁ D₂) (A' b : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.Reduction O K l e a → ∀ x ∈ GlobalTheory.CokerL.Tsub F A' b, D₂.conn x ∈ GlobalTheory.CokerL.Tsub F A' b := by
  first | exact @GlobalTheory.CokerL.Tsub_conn | exact GlobalTheory.CokerL.Tsub_conn | (intros; apply GlobalTheory.CokerL.Tsub_conn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LagrangePrimePowMemIsotypicDegreePolySpan
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LagrangePrimePowMemIsotypicDegreePolySpan
open PowerSeries GlobalTheory.BK

namespace GlobalTheory


open GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds in
theorem degrees_eq_image_pairs {e : ℕ} (Sig : Finset (ZMod e)) (c : ZMod e) (m m' : ℕ) :
    degrees Sig c m m' =
      ((Sig.image fun s => (c - s).val) ×ˢ Finset.Ico m m').image (fun p : ℕ × ℕ => p.1 + p.2 * e) := by
  ext i
  simp only [degrees, Finset.mem_image, Finset.mem_product, Prod.exists]
  constructor
  · rintro ⟨s, n, ⟨hs, hn⟩, rfl⟩
    exact ⟨(c - s).val, n, ⟨⟨s, hs, rfl⟩, hn⟩, rfl⟩
  · rintro ⟨x, n, ⟨⟨s, hs, rfl⟩, hn⟩, rfl⟩
    exact ⟨s, n, ⟨hs, hn⟩, rfl⟩

theorem add_mul_inj_of_lt {e x y n m : ℕ} (hx : x < e) (hy : y < e) (h : x + n * e = y + m * e) :
    x = y ∧ n = m := by
  have h1 : (x + n * e) % e = x := by rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx]
  have h2 : (y + m * e) % e = y := by rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hy]
  have hxy : x = y := by rw [← h1, ← h2, h]
  subst hxy
  have he : 0 < e := lt_of_le_of_lt (Nat.zero_le _) hx
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_right he (by omega)⟩

end GlobalTheory

namespace GlobalTheory

theorem exists_period_dvd {l e a : ℕ} (ha : 1 ≤ a) (he : e + 1 = l ^ a) [NeZero e]
    (Sig : Finset (ZMod e)) (c : ZMod e) {s s' : ZMod e} (hs : s ∈ Sig) (hs' : s' ∈ Sig) :
    ∃ ρ, 1 ≤ ρ ∧ ρ ≤ GlobalTheory.BK.maxPeriod l Sig ∧
      ((l : ℤ) ^ a - 1) ∣ ((((c - s).val : ℕ) : ℤ) - (((c - s').val : ℕ) : ℤ)) * ((l : ℤ) ^ ρ - 1) := by
  have hla : ((l : ZMod e)) ^ a = 1 := by
    have h := congrArg (Nat.cast : ℕ → ZMod e) he
    push_cast at h
    rw [ZMod.natCast_self, zero_add] at h
    exact h.symm
  have hper : Function.IsPeriodicPt (fun x : ZMod e => (l : ZMod e) * x) a (s' - s) := by
    show (fun x : ZMod e => (l : ZMod e) * x)^[a] (s' - s) = s' - s
    rw [mul_left_iterate, hla]; exact one_mul _
  refine ⟨GlobalTheory.BK.frobPeriod l (s' - s), hper.minimalPeriod_pos (by omega), ?_, ?_⟩
  · exact Finset.le_sup (f := fun p : ZMod e × ZMod e => GlobalTheory.BK.frobPeriod l (p.1 - p.2)) (b := (s', s))
      (Finset.mem_product.2 ⟨hs', hs⟩)
  · have hE : ((l : ℤ) ^ a - 1) = (e : ℤ) := by
      have : (e : ℤ) + 1 = (l : ℤ) ^ a := by exact_mod_cast he
      linarith
    rw [hE, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hfix : (fun x : ZMod e => (l : ZMod e) * x)^[GlobalTheory.BK.frobPeriod l (s' - s)] (s' - s) = s' - s :=
      Function.iterate_minimalPeriod
    rw [mul_left_iterate] at hfix
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    linear_combination hfix

end GlobalTheory

namespace GlobalTheory


open GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds GlobalTheory.BK in
theorem lagrange_C_rho_eq_comb_degrees : ∀ (l e a : ℕ) [Fact l.Prime], 1 ≤ a → e + 1 = l ^ a →
    ∀ (Sig : Finset (ZMod e)) (c : ZMod e) (A' N : ℕ), Sig.card ≤ N → 2 * A' + 2 < l →
    ∃ α β : Polynomial ℤ_[l], Polynomial.C ((l : ℤ_[l]) ^ GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.rho l Sig N) =
      α * (GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.P₁ Sig c A').map (Int.castRingHom ℤ_[l]) +
        β * (GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.P₂ Sig c A').map (Int.castRingHom ℤ_[l]) := by
  intro l e a _ ha he Sig c A' N hN hA
  have hl : l.Prime := Fact.out
  have hl2 := hl.two_le
  have hepos : 0 < e := by
    have : l ≤ l ^ a := Nat.le_self_pow (by omega) l
    omega
  have : NeZero e := ⟨by omega⟩
  have hE : ((l : ℤ) ^ a - 1) = (e : ℤ) := by
    have : (e : ℤ) + 1 = (l : ℤ) ^ a := by exact_mod_cast he
    linarith
  set Cc : Finset ℕ := Sig.image fun s => (c - s).val with hCc
  have hCclt : ∀ x ∈ Cc, x < e := by
    intro x hx
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.1 hx
    exact ZMod.val_lt _
  have hD₁ : D₁ Sig c A' = (Cc ×ˢ Finset.Ico 0 A').image (fun p : ℕ × ℕ => p.1 + p.2 * e) :=
    degrees_eq_image_pairs Sig c 0 A'
  have hD₂ : D₂ Sig c A' = (Cc ×ˢ Finset.Ico A' (2 * A')).image (fun p : ℕ × ℕ => p.1 + p.2 * e) :=
    degrees_eq_image_pairs Sig c A' (2 * A')
  have hmap : ∀ T : Finset ℕ, (rootPoly T).map (Int.castRingHom ℤ_[l]) =
      ∏ i ∈ T.image (Nat.cast : ℕ → ℤ), (Polynomial.X - Polynomial.C ((i : ℤ) : ℤ_[l])) := by
    intro T
    rw [Finset.prod_image (fun x _ y _ hxy => by exact_mod_cast hxy)]
    simp [rootPoly, Polynomial.map_prod]
  set Z₁ : Finset ℤ := (D₁ Sig c A').image (Nat.cast : ℕ → ℤ) with hZ₁
  set Z₂ : Finset ℤ := (D₂ Sig c A').image (Nat.cast : ℕ → ℤ) with hZ₂
  have hdisj : Disjoint Z₁ Z₂ := by
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    obtain ⟨i₁, hi₁, rfl⟩ := Finset.mem_image.1 hi1
    obtain ⟨i₂, hi₂, heq⟩ := Finset.mem_image.1 hi2
    have heq' : i₂ = i₁ := by exact_mod_cast heq
    subst heq'
    rw [hD₁] at hi₁
    rw [hD₂] at hi₂
    obtain ⟨p, hp, hpe⟩ := Finset.mem_image.1 hi₁
    obtain ⟨q, hq, hqe⟩ := Finset.mem_image.1 hi₂
    rw [Finset.mem_product, Finset.mem_Ico] at hp hq
    have := add_mul_inj_of_lt (hCclt _ hp.1) (hCclt _ hq.1) (hpe.trans hqe.symm)
    omega
  have hlt : ∀ x ∈ Cc, x < l ^ a - 1 := fun x hx => by have := hCclt x hx; omega
  have hper : ∀ x ∈ Cc, ∀ y ∈ Cc, x ≠ y → ∃ ρ, 1 ≤ ρ ∧ ρ ≤ maxPeriod l Sig ∧
      ((l : ℤ) ^ a - 1) ∣ ((x : ℤ) - y) * ((l : ℤ) ^ ρ - 1) := by
    intro x hx y hy _
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨s', hs', rfl⟩ := Finset.mem_image.1 hy
    exact exists_period_dvd ha he Sig c hs hs'
  have hU : Z₁ ∪ Z₂ = ((Cc ×ˢ Finset.range (2 * A')).image
      (fun p : ℕ × ℕ => p.1 + p.2 * e)).image (Nat.cast : ℕ → ℤ) := by
    rw [hZ₁, hZ₂, ← Finset.image_union, hD₁, hD₂, ← Finset.image_union, ← Finset.product_union]
    congr 3
    ext n
    simp only [Finset.mem_union, Finset.mem_Ico, Finset.mem_range]
    omega
  have hbound : ∀ i ∈ Z₁, (∑ j ∈ Z₂, padicValInt l (i - j)) +
      ∑ j ∈ Z₁.erase i, padicValInt l (i - j) ≤ rho l Sig N := by
    intro i hi
    rw [Finset.sum_erase _ (by simp), add_comm, ← Finset.sum_union hdisj, hU,
      Finset.sum_image (fun x _ y _ hxy => by exact_mod_cast hxy)]
    rw [Finset.sum_image (fun p hp q hq hpq => by
      rw [Finset.mem_coe, Finset.mem_product] at hp hq
      have := add_mul_inj_of_lt (hCclt _ hp.1) (hCclt _ hq.1) hpq
      exact Prod.ext this.1 this.2), Finset.sum_product]
    obtain ⟨i₀, hi₀, rfl⟩ := Finset.mem_image.1 hi
    rw [hD₁] at hi₀
    obtain ⟨⟨x, n⟩, hxn, rfl⟩ := Finset.mem_image.1 hi₀
    rw [Finset.mem_product, Finset.mem_Ico] at hxn
    have LB := Formalism.IrreducibleCountingLemmas.WindowSums.sumPadicValDifferencesLe l a A' (maxPeriod l Sig) Cc hl ha (by omega) hlt
      hper x hxn.1 n hxn.2.2
    rw [hE] at LB
    refine le_trans (le_of_eq ?_) (LB.trans ?_)
    · refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun m _ => ?_
      split_ifs with hc
      · obtain ⟨rfl, rfl⟩ := hc
        simp
      · push_cast
        rfl
    · have hcard : Cc.card ≤ N := Finset.card_image_le.trans hN
      unfold rho
      calc (Cc.card - 1) * maxPeriod l Sig ≤ (N - 1) * maxPeriod l Sig :=
            Nat.mul_le_mul_right _ (by omega)
        _ ≤ 2 * (N - 1) * maxPeriod l Sig := Nat.mul_le_mul_right _ (by omega)
  obtain ⟨α, β, hαβ⟩ := Ideal.mem_span_pair.1
    (Formalism.IrreducibleCountingLemmas.WindowSums.lagrange_resolvent_T l Z₁ Z₂ (rho l Sig N) hdisj hbound)
  refine ⟨α, β, ?_⟩
  rw [← hαβ, P₁, P₂, hmap, hmap]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LagrangePrimePowMemIsotypicDegreePolySpanStatement
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lagrange_prime_pow_mem_isotypicDegreePoly_span : ∀ (l e a : ℕ) [Fact l.Prime], 1 ≤ a → e + 1 = l ^ a → ∀ (Sig : Finset (ZMod e)) (c : ZMod e) (A' N : ℕ), Sig.card ≤ N → 2 * A' + 2 < l → ∃ α β : Polynomial ℤ_[l], Polynomial.C ((l : ℤ_[l]) ^ GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.rho l Sig N) = α * (GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.P₁ Sig c A').map (Int.castRingHom ℤ_[l]) + β * (GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.P₂ Sig c A').map (Int.castRingHom ℤ_[l]) := by
  first | exact @GlobalTheory.lagrange_C_rho_eq_comb_degrees | exact GlobalTheory.lagrange_C_rho_eq_comb_degrees | (intros; apply GlobalTheory.lagrange_C_rho_eq_comb_degrees <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPowKillsLatticeCokernel
noncomputable section

namespace GlobalTheory.CokerL

open PowerSeries GlobalTheory.BK

theorem aeval_mem_of_stable {O K V : Type} [CommRing O] [NormedField K] [Algebra O K] [IsUnitBall O K]
    [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] (W : Submodule O V)
    (T : Module.End K V) (hT : ∀ x ∈ W, T x ∈ W) (p : Polynomial K) (hp : ∀ n, ‖p.coeff n‖ ≤ 1) :
    ∀ x ∈ W, Polynomial.aeval T p x ∈ W := by
  intro x hx
  have hpow : ∀ n : ℕ, (T ^ n) x ∈ W := by
    intro n
    induction n with
    | zero => simpa using hx
    | succ n ih => rw [pow_succ', Module.End.mul_apply]; exact hT _ ih
  rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨c, hc⟩ := (IsUnitBall.mem_range_iff (O := O) (p.coeff i)).2 (hp i)
  rw [LinearMap.smul_apply, ← hc, algebraMap_smul]
  exact W.smul_mem c (hpow i)

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fact l.Prime]

theorem app_aeval {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} (F : BK.Hom P Q) (p : Polynomial K)
    (v : Vec K a ι) : F.app (Polynomial.aeval P.conn p v) = Polynomial.aeval Q.conn p (F.app v) := by
  have hpow : ∀ (n : ℕ) (v : Vec K a ι), F.app ((P.conn ^ n) v) = (Q.conn ^ n) (F.app v) := by
    intro n
    induction n with
    | zero => intro v; rfl
    | succ n ih =>
      intro v
      simp only [pow_succ', Module.End.mul_apply]
      rw [F.app_conn, ih]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range, LinearMap.sum_apply,
    LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.map_smul_of_tower, hpow]

theorem app_mem_MMHigh [NormedAlgebra ℚ_[l] K] [NeZero e] {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} (F : BK.Hom P Q)
    {h : Vec K a ι} (hh : h ∈ GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.MMHigh P) : F.app h ∈ GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.MMHigh Q := by
  change h ∈ GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.SHigh O K l e • P.MM at hh
  change F.app h ∈ GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.SHigh O K l e • Q.MM
  refine Submodule.smul_induction_on hh (fun s hs m hm => ?_) (fun x y hx hy => ?_)
  · rw [LinearMap.map_smul_of_tower]
    exact Submodule.smul_mem_smul hs (F.app_mem_ext (A_le_S l e) hm)
  · rw [map_add (f := _)]
    exact add_mem hx hy

end GlobalTheory.CokerL

namespace GlobalTheory.CokerL

open PowerSeries GlobalTheory.BK

theorem isotypic_step : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (η H : ℕ) (D₁ : BKDat O K l e a ι η H) (D₂ : BKDat O K l e a κ η H) (F : BKHom D₁ D₂), ∀ (Sig : Finset (ZMod e)) (U : Finset ℤ) (N : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.Bounds l e Sig U N η H → (∀ τ, D₁.desc.chars τ ⊆ (Sig : Set (ZMod e))) → (∀ τ, D₂.desc.chars τ ⊆ (Sig : Set (ZMod e))) → IsFiniteLength (A O K) F.coker → ∀ c : ZMod e, ∀ x ∈ D₂.L, (l : K) ^ GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.rho l Sig N • isoProj D₂.desc c (((X : K⟦X⟧) ^ e) ^ (H + η + (GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.rho l Sig N + 1)) • x) ∈ Tsub F (H + η + (GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.rho l Sig N + 1)) (GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.rho l Sig N + 1) := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ κ _ _ η H D₁ D₂ F Sig U N hB h₁ h₂ hfl c x hx
  set ρ := GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.rho l Sig N with hρ
  set b := ρ + 1 with hb
  set A' := H + η + b with hA'
  have ha : 1 ≤ a := Nat.one_le_iff_ne_zero.2 (NeZero.ne a)
  have he : e + 1 = l ^ a := TameDescentExponentData.succ_eq (K := K)
  have horb := GlobalTheory.T.maxFrobeniusOrbitLengthDiff_bounds_zmod l e a (Fact.out : l.Prime) ha he Sig N hB.frob_mem hB.zero_mem_Sig
    hB.card_Sig hB.two_le
  have hnum := GlobalTheory.T.numerical_conditions_theorem_T_large_prime l H N η (maxPeriod l Sig) hB.two_le hB.one_le hB.lt horb.2.1 hB.large
  have hA'l : 2 * A' + 2 < l := by
    have : A' = H + η + 2 * (N - 1) * maxPeriod l Sig + 1 := by
      simp only [hA', hb, hρ, GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.rho]; ring
    rw [this]; exact hnum.1
  have hred := GlobalTheory.T.monodromy_reduction_modulo_high_degree O K l e a
  have hdeg := GlobalTheory.T.isotypic_monodromy_polynomials_raise_degree O K l e a
  obtain ⟨α, β, hαβ⟩ := GlobalTheory.T.lagrange_prime_pow_mem_isotypicDegreePoly_span l e a ha he Sig c A' N hB.card_Sig hA'l

  have hlpow : ∀ (n : ℕ) (v : Vec K a κ), (l : K) ^ n • v = (l ^ n) • v := fun n v => by
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul K]
  have hlpow' : ∀ (n : ℕ) (v : Vec K a κ), (l : K⟦X⟧) ^ n • v = (l : K) ^ n • v := fun n v => by
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul K⟦X⟧, hlpow]
  have hvA : ∀ n : ℕ, ((X : K⟦X⟧) ^ e) ^ n ∈ A O K := fun n =>
    pow_mem (pow_mem (HasU.X_mem (B := A O K)) e) n
  have vmemL : ∀ n : ℕ, ∀ v ∈ D₂.L, ((X : K⟦X⟧) ^ e) ^ n • v ∈ D₂.L := fun n v hv =>
    D₂.L.smul_mem (⟨_, hvA n⟩ : A O K) hv

  set T := Tsub F A' b with hT
  have memT1 : ∀ y ∈ D₁.L, ((X : K⟦X⟧) ^ e) ^ A' • F.app y ∈ T := fun y hy =>
    Submodule.mem_sup_left (Submodule.mem_sup_left ⟨F.app y, ⟨y, hy, rfl⟩, rfl⟩)
  have memT2 : ∀ z ∈ D₂.L, (l : K) ^ b • z ∈ T := fun z hz =>
    Submodule.mem_sup_left (Submodule.mem_sup_right ⟨z, hz, by simp [hlpow']⟩)
  have memT3 : ∀ h ∈ GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.MMHigh D₂.toPhiMod, h ∈ T := fun h hh =>
    Submodule.mem_sup_right hh
  have hTc : ∀ w ∈ T, D₂.conn w ∈ T := GlobalTheory.T.eulerDerivation_preserves_breuilKisin_sum_submodule O K l e a ι κ η H D₁ D₂ F A' b hred

  have a3 := GlobalTheory.T.vPow_lattice_le_image_add_lPow_of_finite_cokernel O K l e a ι κ η H D₁ D₂ F hfl b (by omega) (by omega)
  obtain ⟨y₀, hy₀, z₀, hz₀, h3⟩ := a3 x hx
  have hyd : isoProj D₂.desc c (((X : K⟦X⟧) ^ e) ^ A' • x) =
      F.app (isoProj D₁.desc c y₀) + (l : K) ^ b • isoProj D₂.desc c z₀ := by
    rw [h3, map_add (f := _), map_smul, app_isoProj]
  have hy_iso := GlobalTheory.T.isotypicProjector_mem_isotypicPart_explicit O K l e a κ D₂.toPhiMod D₂.desc c (((X : K⟦X⟧) ^ e) ^ A' • x)
  have hy_v : isoProj D₂.desc c (((X : K⟦X⟧) ^ e) ^ A' • x) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.vL D₂.toPhiMod A' := by
    rw [isoProj_vpow]
    exact ⟨_, GlobalTheory.T.isotypicProjector_mem_breuilKisinLattice O K l e a κ D₂.toPhiMod D₂.desc c x hx, rfl⟩
  have hy₁L := GlobalTheory.T.isotypicProjector_mem_breuilKisinLattice O K l e a ι D₁.toPhiMod D₁.desc c y₀ hy₀
  have hy₁iso := GlobalTheory.T.isotypicProjector_mem_isotypicPart_explicit O K l e a ι D₁.toPhiMod D₁.desc c y₀
  have hz₁L := GlobalTheory.T.isotypicProjector_mem_breuilKisinLattice O K l e a κ D₂.toPhiMod D₂.desc c z₀ hz₀
  set y := isoProj D₂.desc c (((X : K⟦X⟧) ^ e) ^ A' • x) with hy

  let φ : ℤ_[l] →+* K := (algebraMap ℚ_[l] K).comp PadicInt.Coe.ringHom
  have hφ : ∀ t, ‖φ t‖ ≤ 1 := fun t => by
    simp only [φ, RingHom.comp_apply, norm_algebraMap']
    exact PadicInt.norm_le_one t
  have hPZ : ∀ p : Polynomial ℤ, (p.map (Int.castRingHom ℤ_[l])).map φ = p.map (Int.castRingHom K) := by
    intro p
    rw [Polynomial.map_map]
    congr 1
    exact RingHom.ext_int _ _
  have hZ : ∀ (p : Polynomial ℤ), ∀ (m : ℕ), ‖(p.map (Int.castRingHom K)).coeff m‖ ≤ 1 := by
    intro p m
    rw [Polynomial.coeff_map, eq_intCast]
    exact IsUltrametricDist.norm_intCast_le_one K _
  have haeZ : ∀ {μ : Type} [Fintype μ] [DecidableEq μ] (P : PhiMod O K l e a μ) (p : Polynomial ℤ)
      (v : Vec K a μ), Polynomial.aeval P.conn p v = Polynomial.aeval P.conn (p.map (Int.castRingHom K)) v := by
    intro μ _ _ P p v
    rw [← algebraMap_int_eq, Polynomial.aeval_map_algebraMap]
  have key : (l : K) ^ ρ • y =
      Polynomial.aeval D₂.conn (α.map φ)
          (Polynomial.aeval D₂.conn (GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.P₁ Sig c A') y) +
        Polynomial.aeval D₂.conn (β.map φ)
          (Polynomial.aeval D₂.conn (GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.P₂ Sig c A') y) := by
    have h1 := congrArg (Polynomial.map φ) hαβ
    rw [Polynomial.map_C, Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.map_mul, hPZ, hPZ] at h1
    have h2 := congrArg (fun p => Polynomial.aeval D₂.conn p y) h1
    rw [Polynomial.aeval_C, Module.algebraMap_end_apply, map_pow, map_natCast] at h2
    simp only [map_add (f := _), map_mul, LinearMap.add_apply, Module.End.mul_apply] at h2
    rw [h2, haeZ, haeZ]

  have hA : Polynomial.aeval D₂.conn (GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.P₁ Sig c A') y ∈ T := by
    rw [haeZ, hyd, map_add (f := _), map_smul, ← app_aeval, ← haeZ]
    refine add_mem ?_ ?_
    · have hr := ((hdeg Sig c A' (by omega)).2 ι η H D₁ h₁).aeval₁ _ ⟨hy₁L, hy₁iso⟩
      obtain ⟨u, hu, h, hh, hsum⟩ := Submodule.mem_sup.1 hr
      rw [← hsum, map_add (f := _)]
      obtain ⟨w, hw, rfl⟩ := GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.mem_mulL.1 hu
      rw [map_smul]
      exact add_mem (memT1 w hw) (memT3 _ (app_mem_MMHigh F.toHom hh))
    · have hMM : isoProj D₂.desc c z₀ ∈
          GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.part ⊤ (D₂.MM.restrictScalars O) :=
        ⟨D₂.ext_mono (A_le_S l e) hz₁L, Submodule.mem_top⟩
      have hst := aeval_mem_of_stable (GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.part ⊤ (D₂.MM.restrictScalars O)) D₂.conn
        ((hred.2.1 κ η H D₂).1.conn_MM) _ (hZ (GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.P₁ Sig c A')) _ hMM
      rw [(hred.2.1 κ η H D₂).1.MM_eq] at hst
      obtain ⟨u, hu, h, hh, hsum⟩ := Submodule.mem_sup.1 hst
      rw [← hsum, smul_add]
      refine add_mem (memT2 _ hu.1) (memT3 _ ?_)
      rw [hlpow]
      exact (GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.MMHigh D₂.toPhiMod).toAddSubmonoid.nsmul_mem hh.1 _

  have hB' : Polynomial.aeval D₂.conn (GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.P₂ Sig c A') y ∈ T := by
    have hr := ((hdeg Sig c A' (by omega)).2 κ η H D₂ h₂).aeval₂ _ ⟨hy_v, hy_iso⟩
    obtain ⟨u, hu, h, hh, hsum⟩ := Submodule.mem_sup.1 hr
    rw [← hsum]
    refine add_mem ?_ (memT3 _ hh)
    obtain ⟨w, hw, rfl⟩ := GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.mem_mulL.1 hu
    obtain ⟨y', hy', z', hz', h4⟩ := a3 w hw
    have : ((X : K⟦X⟧) ^ e) ^ (2 * A') • w = ((X : K⟦X⟧) ^ e) ^ A' • ((X : K⟦X⟧) ^ e) ^ A' • w := by
      rw [smul_smul, ← pow_add, two_mul]
    rw [this, h4, smul_add, smul_comm _ ((l : K) ^ b)]
    exact add_mem (memT1 y' hy') (memT2 _ (vmemL _ _ hz'))
  rw [key]
  exact add_mem
    (aeval_mem_of_stable T D₂.conn hTc _ (fun n => by rw [Polynomial.coeff_map]; exact hφ _) _ hA)
    (aeval_mem_of_stable T D₂.conn hTc _ (fun n => by rw [Polynomial.coeff_map]; exact hφ _) _ hB')

end GlobalTheory.CokerL

namespace GlobalTheory.CokerL

open PowerSeries GlobalTheory.BK

theorem kills_cokerL : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (η H : ℕ) (D₁ : BKDat O K l e a ι η H) (D₂ : BKDat O K l e a κ η H) (F : BKHom D₁ D₂), ∀ (Sig : Finset (ZMod e)) (U : Finset ℤ) (N : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.Bounds l e Sig U N η H → (∀ τ, D₁.desc.chars τ ⊆ (Sig : Set (ZMod e))) → (∀ τ, D₂.desc.chars τ ⊆ (Sig : Set (ZMod e))) → IsFiniteLength (A O K) F.coker → GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.KillsCoker F.app (l ^ GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.rho l Sig N) D₁.L D₂.L := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ κ _ _ η H D₁ D₂ F Sig U N hB h₁ h₂ hfl
  set ρ := GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.rho l Sig N with hρ
  set b := ρ + 1 with hb
  set A' := H + η + b with hA'

  have horb := GlobalTheory.T.maxFrobeniusOrbitLengthDiff_bounds_zmod l e a (Fact.out : l.Prime) (Nat.one_le_iff_ne_zero.2 (NeZero.ne a))
    (TameDescentExponentData.succ_eq (K := K)) Sig N hB.frob_mem hB.zero_mem_Sig hB.card_Sig hB.two_le
  have hnum := GlobalTheory.T.numerical_conditions_theorem_T_large_prime l H N η (maxPeriod l Sig) hB.two_le hB.one_le hB.lt horb.2.1 hB.large
  have hA'l : 2 * A' + 2 < l := by
    have : A' = H + η + 2 * (N - 1) * maxPeriod l Sig + 1 := by
      simp only [hA', hb, hρ, GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.rho]; ring
    rw [this]; exact hnum.1

  have hns : ∀ (n : ℕ) (v : Vec K a κ), ((n : K)) • v = n • v := fun n v => Nat.cast_smul_eq_nsmul K n v
  have hns' : ∀ (n : ℕ) (v : Vec K a κ), ((n : K⟦X⟧)) • v = n • v := fun n v => Nat.cast_smul_eq_nsmul K⟦X⟧ n v
  have hlpow : ∀ (n : ℕ) (v : Vec K a κ), (l : K) ^ n • v = (l ^ n) • v := fun n v => by
    rw [← Nat.cast_pow, hns]
  have hlpow' : ∀ (n : ℕ) (v : Vec K a κ), (l : K⟦X⟧) ^ n • v = (l : K) ^ n • v := fun n v => by
    rw [← Nat.cast_pow, hns', hlpow]
  have hlpow₁ : ∀ (n : ℕ) (v : Vec K a ι), (l : K) ^ n • v = (l ^ n) • v := fun n v => by
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul K]
  have hvA : ∀ n : ℕ, ((X : K⟦X⟧) ^ e) ^ n ∈ A O K := fun n =>
    pow_mem (pow_mem (HasU.X_mem (B := A O K)) e) n
  have vmemL : ∀ n : ℕ, ∀ v ∈ D₂.L, ((X : K⟦X⟧) ^ e) ^ n • v ∈ D₂.L := fun n v hv =>
    D₂.L.smul_mem (⟨_, hvA n⟩ : A O K) hv
  have lmemL : ∀ n : ℕ, ∀ v ∈ D₂.L, (l : K) ^ n • v ∈ D₂.L := fun n v hv => by
    rw [hlpow]; exact D₂.L.toAddSubmonoid.nsmul_mem hv _
  have lmemL₁ : ∀ n : ℕ, ∀ v ∈ D₁.L, (l : K) ^ n • v ∈ D₁.L := fun n v hv => by
    rw [hlpow₁]; exact D₁.L.toAddSubmonoid.nsmul_mem hv _
  have appL : ∀ v ∈ D₁.L, F.app v ∈ D₂.L := fun v hv => F.app_mem_ext le_rfl hv
  have hred := GlobalTheory.T.monodromy_reduction_modulo_high_degree O K l e a

  have a3 : ∀ x ∈ D₂.L, ∃ y ∈ D₁.L, ∃ z ∈ D₂.L,
      ((X : K⟦X⟧) ^ e) ^ A' • x = F.app y + (l : K) ^ b • z :=
    GlobalTheory.T.vPow_lattice_le_image_add_lPow_of_finite_cokernel O K l e a ι κ η H D₁ D₂ F hfl b (by omega) (by omega)

  have stepP : ∀ x ∈ D₂.L, ∃ y ∈ D₁.L, ∃ z ∈ D₂.L, (l : K) ^ ρ • x = F.app y + (l : K) ^ b • z := by
    intro x hx
    have hT : (l : K) ^ ρ • (((X : K⟦X⟧) ^ e) ^ A' • x) ∈ GlobalTheory.CokerL.Tsub F A' b := by
      rw [← GlobalTheory.T.sum_isotypicProjectors_eq_id O K l e a κ D₂.toPhiMod D₂.desc (((X : K⟦X⟧) ^ e) ^ A' • x),
        Finset.smul_sum]
      refine Submodule.sum_mem _ fun c _ => ?_
      exact GlobalTheory.CokerL.isotypic_step O K l e a ι κ η H D₁ D₂ F Sig U N hB h₁ h₂ hfl c x hx
    obtain ⟨t, ht, h, hh, hth⟩ := Submodule.mem_sup.1 hT
    obtain ⟨t₁, ht₁, t₂, ht₂, rfl⟩ := Submodule.mem_sup.1 ht
    obtain ⟨u₁, hu₁, rfl⟩ := Submodule.mem_map.1 ht₁
    obtain ⟨y', hy', rfl⟩ := Submodule.mem_map.1 (Submodule.restrictScalars_mem _ _ _ |>.1 hu₁)
    obtain ⟨z', hz', rfl⟩ := Submodule.mem_map.1 ht₂
    simp only [LinearMap.restrictScalars_apply, GlobalTheory.BK.mulV_apply] at hth
    have hz'L : z' ∈ D₂.L := hz'
    have hhL : h ∈ D₂.L := by
      have : h = (l : K) ^ ρ • (((X : K⟦X⟧) ^ e) ^ A' • x) -
          (((X : K⟦X⟧) ^ e) ^ A' • F.app y' + (l : K⟦X⟧) ^ b • z') := by rw [← hth]; abel
      rw [this]
      exact sub_mem (lmemL _ _ (vmemL _ _ hx))
        (add_mem (vmemL _ _ (appL _ hy')) (by rw [hlpow']; exact lmemL _ _ hz'L))
    have hv : h ∈ GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.vL D₂.toPhiMod l := by
      have hi := (hred.2.1 κ η H D₂).1.inter_eq
      have hmem : h ∈ GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.part ⊤ (D₂.L.restrictScalars O) ⊓
          GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.part ⊤ (GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.MMHigh D₂.toPhiMod) :=
        ⟨⟨hhL, Submodule.mem_top⟩, ⟨hh, Submodule.mem_top⟩⟩
      rw [hi] at hmem
      exact hmem.1
    obtain ⟨h₀, hh₀, rfl⟩ := GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.mem_mulL.1 hv
    have hle : A' ≤ l := by omega
    have hwL : (l : K) ^ ρ • x - F.app y' - ((X : K⟦X⟧) ^ e) ^ (l - A') • h₀ ∈ D₂.L :=
      sub_mem (sub_mem (lmemL _ _ hx) (appL _ hy')) (vmemL _ _ hh₀)
    have hw : ((X : K⟦X⟧) ^ e) ^ A' • ((l : K) ^ ρ • x - F.app y' - ((X : K⟦X⟧) ^ e) ^ (l - A') • h₀) =
        (l : K) ^ b • z' := by
      rw [smul_sub, smul_sub, smul_comm (((X : K⟦X⟧) ^ e) ^ A') ((l : K) ^ ρ), smul_smul, ← pow_add,
        Nat.add_sub_cancel' hle, ← hth, hlpow']
      abel
    obtain ⟨z'', hz'', hw'⟩ := GlobalTheory.T.mem_prime_pow_lattice_of_X_pow_smul_mem O K l e a κ D₂.toPhiMod A' b _ z' hwL hz'L hw
    obtain ⟨y₂, hy₂, z₂, hz₂, h2⟩ := a3 _ (vmemL (l - 2 * A') _ hh₀)
    have e1 : ((X : K⟦X⟧) ^ e) ^ (l - A') • h₀ =
        ((X : K⟦X⟧) ^ e) ^ A' • ((X : K⟦X⟧) ^ e) ^ (l - 2 * A') • h₀ := by
      rw [smul_smul, ← pow_add]
      congr 2
      omega
    refine ⟨y' + y₂, add_mem hy' hy₂, z'' + z₂, add_mem hz'' hz₂, ?_⟩
    have key : (l : K) ^ ρ • x = ((l : K) ^ ρ • x - F.app y' - ((X : K⟦X⟧) ^ e) ^ (l - A') • h₀) +
        F.app y' + ((X : K⟦X⟧) ^ e) ^ (l - A') • h₀ := by abel
    rw [key, hw', e1, h2, map_add (f := _), smul_add]
    abel

  obtain ⟨m, hm⟩ := GlobalTheory.T.exists_prime_pow_kills_finiteLength_integralPowerSeries O K l F.coker hfl
  have killM : GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.KillsCoker F.app (l ^ m) D₁.M D₂.M :=
    (GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.killsCoker_M_iff F.toHom (l ^ m)).2 fun q => by
      rw [← Nat.cast_smul_eq_nsmul (A O K), Nat.cast_pow]
      exact hm q
  have killL : ∀ x ∈ D₂.L, ∃ y ∈ D₁.L, F.app y = (l ^ m) • x := by
    intro x hx
    rw [D₂.toPhiMod.L_eq_span] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, hw, rfl⟩ := hx
      obtain ⟨y₀, hy₀, hF⟩ := killM w hw
      exact ⟨D₁.phi y₀, D₁.phi_mem_L hy₀, by rw [F.app_phi, hF, map_nsmul]⟩
    | zero => exact ⟨0, zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a1, ha1, e1⟩ := hx
      obtain ⟨a2, ha2, e2⟩ := hy
      exact ⟨a1 + a2, add_mem ha1 ha2, by rw [map_add (f := _), e1, e2, smul_add]⟩
    | smul r x _ hx =>
      obtain ⟨a1, ha1, e1⟩ := hx
      exact ⟨r • a1, D₁.L.smul_mem r ha1, by rw [LinearMap.map_smul_of_tower, e1, smul_comm]⟩
  have Q : ∀ k : ℕ, ∀ x ∈ D₂.L, ∃ y ∈ D₁.L, ∃ z ∈ D₂.L,
      (l : K) ^ ρ • x = F.app y + (l : K) ^ (ρ + k) • z := by
    intro k
    induction k with
    | zero => exact fun x hx => ⟨0, zero_mem _, x, hx, by simp⟩
    | succ k ih =>
      intro x hx
      obtain ⟨y, hy, z, hz, e1⟩ := ih x hx
      obtain ⟨y₂, hy₂, z₂, hz₂, e2⟩ := stepP z hz
      refine ⟨y + (l : K) ^ k • y₂, add_mem hy (lmemL₁ _ _ hy₂), z₂, hz₂, ?_⟩
      have hp : (l : K) ^ (ρ + (k + 1)) = (l : K) ^ k * (l : K) ^ b := by
        rw [← pow_add]; congr 1; omega
      rw [e1, pow_add, mul_comm, mul_smul, e2, smul_add, smul_smul, ← hp, map_add (f := _),
        LinearMap.map_smul_of_tower, add_assoc]
  intro x hx
  obtain ⟨y, hy, z, hz, e1⟩ := Q m x hx
  obtain ⟨y₃, hy₃, e3⟩ := killL z hz
  refine ⟨y + (l : K) ^ ρ • y₃, add_mem hy (lmemL₁ _ _ hy₃), ?_⟩
  rw [← hlpow ρ x, e1, pow_add, mul_smul, hlpow m z, map_add (f := _), LinearMap.map_smul_of_tower, e3]

end GlobalTheory.CokerL
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPowKillsLatticeCokernelStatement
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_pow_kills_lattice_cokernel : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (η H : ℕ) (D₁ : BKDat O K l e a ι η H) (D₂ : BKDat O K l e a κ η H) (F : BKHom D₁ D₂), ∀ (Sig : Finset (ZMod e)) (U : Finset ℤ) (N : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.Bounds l e Sig U N η H → (∀ τ, D₁.desc.chars τ ⊆ (Sig : Set (ZMod e))) → (∀ τ, D₂.desc.chars τ ⊆ (Sig : Set (ZMod e))) → IsFiniteLength (A O K) F.coker → GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.KillsCoker F.app (l ^ GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.rho l Sig N) D₁.L D₂.L := by
  first | exact @GlobalTheory.CokerL.kills_cokerL | exact GlobalTheory.CokerL.kills_cokerL | (intros; apply GlobalTheory.CokerL.kills_cokerL <;> assumption)
end
