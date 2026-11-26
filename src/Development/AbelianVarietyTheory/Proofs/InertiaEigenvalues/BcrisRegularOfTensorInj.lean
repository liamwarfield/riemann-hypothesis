module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisInvariantsBcrisEqMaxUnramified
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateCharacterFiniteOnInertiaOfEigenvectorStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteQuotientCocycleSpanRhoCharLeCocycles

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixedOfInertiaFrobenius
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixedOfInertiaFrobenius
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.RegularDense

theorem fixed_of_inertia_frobenius : ∀ (l : ℕ) [Fact l.Prime] (F : GQ l),
    (∀ (x : Om l) (m : ℕ), 0 < m → ¬ l ∣ m → x ^ m = 1 → F x = x ^ l) →
    ∀ y : ℂ_[l], (∀ g ∈ (MaximalUnramifiedExtension l).fixingSubgroup, Per.σC g y = y) → Per.σC F y = y →
      ∀ g : GQ l, Per.σC g y = y := by
  intro l hl F hF y hI hFy g
  let H : Subgroup (GQ l) :=
    { carrier := {h | Per.σC h y = y}
      mul_mem' := fun {a b} ha hb => by
        show Per.σC (a * b) y = y
        have ha' : Per.σC a y = y := ha
        have hb' : Per.σC b y = y := hb
        rw [GlobalTheory.RingBasics.σC_mul, hb', ha']
      one_mem' := by
        show Per.σC 1 y = y
        rw [GlobalTheory.RingBasics.σC_one]
      inv_mem' := fun {a} ha => by
        show Per.σC a⁻¹ y = y
        have ha' : Per.σC a y = y := ha
        conv_lhs => rw [← ha']
        rw [← GlobalTheory.RingBasics.σC_mul, inv_mul_cancel, GlobalTheory.RingBasics.σC_one] }
  have hy := ax_sen_tate l H y (fun h hh => hh)
  have hcont : Continuous (fun z : ℂ_[l] => Per.σC g z) := by
    refine Isometry.continuous (Isometry.of_dist_eq fun a b => ?_)
    rw [dist_eq_norm, dist_eq_norm, ← map_sub, GlobalTheory.RingBasics.norm_σC]
  have hcl : IsClosed {z : ℂ_[l] | Per.σC g z = z} := isClosed_eq hcont continuous_id
  refine closure_minimal ?_ hcl hy
  rintro _ ⟨z, hz, rfl⟩
  show Per.σC g (z : ℂ_[l]) = z
  rw [GlobalTheory.RingBasics.σC_coe]
  congr 1
  have hzK : z ∈ MaximalUnramifiedExtension l := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup (MaximalUnramifiedExtension l), IntermediateField.mem_fixedField_iff]
    intro h hh
    exact hz h (hI h hh)
  have hFz : F z = z := hz F hFy
  have hpow : ∀ n : ℕ, (F ^ n) z = z := fun n => by
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ, AlgEquiv.mul_apply, hFz, ih]
  obtain ⟨m, hm, hlm, hH⟩ := FrobLaws.exists_level hzK
  have hr : ∀ (n : ℕ) (ζ : Om l), ζ ^ m = 1 → (F ^ n) ζ = ζ ^ (l ^ n) := fun n ζ hζ => by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, hF ζ m hm hlm hζ, ← pow_mul, pow_succ']
  obtain ⟨n, hn⟩ := FrobLaws.gal_root g hm hlm
  rw [hH g (F ^ n) fun ζ hζ => by rw [hn ζ hζ, hr n ζ hζ], hpow]

end GlobalTheory.RegularDense
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixedOfInertiaFrobeniusStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixed_of_fixed_inertia_of_fixed_frobenius : ∀ (l : ℕ) [Fact l.Prime] (F : GQ l), (∀ (x : Om l) (m : ℕ), 0 < m → ¬ l ∣ m → x ^ m = 1 → F x = x ^ l) → ∀ y : ℂ_[l], (∀ g ∈ (MaximalUnramifiedExtension l).fixingSubgroup, Per.σC g y = y) → Per.σC F y = y → ∀ g : GQ l, Per.σC g y = y := by
  first | exact @GlobalTheory.RegularDense.fixed_of_inertia_frobenius | exact GlobalTheory.RegularDense.fixed_of_inertia_frobenius | (intros; apply GlobalTheory.RegularDense.fixed_of_inertia_frobenius <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisExistsTPowMulThetaNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisExistsTPowMulThetaNeZero
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.RegDivide

theorem exists_pow_mul_not_dvd {R : Type*} [CommRing R] (ξ : R) [IsHausdorff (Ideal.span {ξ}) R]
    {y : R} (hy : y ≠ 0) : ∃ (n : ℕ) (z : R), y = ξ ^ n * z ∧ ¬ ξ ∣ z := by
  classical
  have hex : ∃ n : ℕ, ¬ ξ ^ (n + 1) ∣ y := by
    by_contra h
    push Not at h
    apply hy
    apply IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {ξ}) R)
    intro n
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact (pow_dvd_pow ξ (Nat.le_succ n)).trans (h n)
  have h1 : ξ ^ (Nat.find hex) ∣ y := by
    rcases h : Nat.find hex with _ | k
    · simp
    · by_contra hk
      exact Nat.find_min hex (by omega : k < Nat.find hex) hk
  obtain ⟨z, hz⟩ := h1
  refine ⟨Nat.find hex, z, hz, ?_⟩
  rintro ⟨w, rfl⟩
  apply Nat.find_spec hex
  exact ⟨w, by rw [pow_succ, mul_assoc]; exact hz⟩

theorem abstract {B R D : Type*} [CommRing B] [CommRing R] [CommRing D] (ι : B →+* D) (a : R →+* D)
    (hι : Function.Injective ι) (ξ v : R) [IsHausdorff (Ideal.span {ξ}) R] (hv : IsUnit v)
    (t : B) (ht : IsUnit t) (hιt : ι t = a (ξ * v))
    (hD : ∀ x : D, ∃ (n : ℕ) (y : R), x * a ξ ^ n = a y) (b : B) (hb : b ≠ 0) :
    ∃ (m n : ℕ) (b' : B) (y : R), b * t ^ m = t ^ n * b' ∧ ι b' = a y ∧ ¬ ξ ∣ y := by
  obtain ⟨m, y₀, h0⟩ := hD (ι b)
  obtain ⟨s, hs⟩ := ht.exists_right_inv
  obtain ⟨w, hw⟩ := hv.exists_right_inv
  have h1 : ι (b * t ^ m) = a (y₀ * v ^ m) := by
    rw [map_mul, map_pow, hιt, map_mul, map_mul, ← h0, map_pow]
    ring
  have hne : y₀ * v ^ m ≠ 0 := by
    intro h
    rw [h, map_zero, ← map_zero ι] at h1
    exact hb ((ht.pow m).mul_left_eq_zero.1 (hι h1))
  obtain ⟨n, z, hz, hnd⟩ := exists_pow_mul_not_dvd ξ hne
  refine ⟨m, n, b * t ^ m * s ^ n, z * w ^ n, ?_, ?_, ?_⟩
  · calc b * t ^ m = b * t ^ m * (t * s) ^ n := by rw [hs, one_pow, mul_one]
      _ = _ := by ring
  · have h2 : a ξ * a v * ι s = 1 := by rw [← map_mul a, ← hιt, ← map_mul, hs, map_one]
    have h3 : a v * a w = 1 := by rw [← map_mul, hw, map_one]
    rw [map_mul, h1, hz, map_mul, map_mul, map_pow, map_pow, map_pow]
    calc a ξ ^ n * a z * ι s ^ n = a ξ ^ n * a z * ι s ^ n * (a v * a w) ^ n := by
          rw [h3, one_pow, mul_one]
      _ = a z * a w ^ n * (a ξ * a v * ι s) ^ n := by ring
      _ = _ := by rw [h2, one_pow, mul_one]
  · intro h
    apply hnd
    have : z = z * w ^ n * v ^ n := by
      rw [mul_assoc, ← mul_pow, mul_comm w v, hw, one_pow, mul_one]
    rw [this]
    exact h.mul_right _

theorem exists_divide : ∀ (l : ℕ) [Fact l.Prime] (C : Core l) (b : Per.Bcris l), b ≠ 0 →
    ∃ (m n : ℕ) (b' : Per.Bcris l) (y : Per.BdRp l), b * C.tB ^ m = C.tB ^ n * b' ∧
      C.ι b' = algebraMap (Per.BdRp l) (Per.BdR l) y ∧ Per.θD l y ≠ 0 := by
  intro l _ C b hb
  have he := core_isEps l C
  obtain ⟨hF, -, hc, -⟩ := filtration_eq_xi_pow l C.ε he
  obtain ⟨ht, h1, h2, -⟩ := core_t_unit_fil l C
  obtain ⟨-, hk, hu, -⟩ := thetaD_props l
  have hinj := (ULaws.u_laws l C).2.2.2.1
  have hD := (BdRField.bdR_isField l).2.2.2 C.ε he
  have hθ : ∀ y : Per.BdRp l, ¬ aDp l (xi C.ε) ∣ y → Per.θD l y ≠ 0 := fun y hy h =>
    hy (by simpa only [pow_one] using (hF 1 y).1 ((hk y).1 h))
  obtain ⟨v, hv⟩ := (hF 1 _).1 h1
  rw [pow_one] at hv
  have hvu : IsUnit v := by
    apply hu
    apply hθ
    rintro ⟨w, hw⟩
    apply h2
    refine (hF 2 _).2 ⟨w, ?_⟩
    rw [hv, hw, pow_two, mul_assoc]
  haveI := hc.toIsHausdorff
  obtain ⟨m, n, b', y, e1, e2, e3⟩ := abstract C.ι (algebraMap (Per.BdRp l) (Per.BdR l)) hinj
    (aDp l (xi C.ε)) v hvu C.tB ht (by rw [← hv]; exact C.ι_j C.t) hD b hb
  exact ⟨m, n, b', y, e1, e2, hθ y e3⟩

end GlobalTheory.MemLoc.RegDivide
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisExistsTPowMulThetaNeZeroStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bcris_exists_tPow_mul_theta_ne_zero : ∀ (l : ℕ) [Fact l.Prime] (C : Core l) (b : Per.Bcris l), b ≠ 0 → ∃ (m n : ℕ) (b' : Per.Bcris l) (y : Per.BdRp l), b * C.tB ^ m = C.tB ^ n * b' ∧ C.ι b' = algebraMap (Per.BdRp l) (Per.BdR l) y ∧ Per.θD l y ≠ 0 := by
  first | exact @GlobalTheory.MemLoc.RegDivide.exists_divide | exact GlobalTheory.MemLoc.RegDivide.exists_divide | (intros; apply GlobalTheory.MemLoc.RegDivide.exists_divide <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisRegularOfFullGaloisLineUnits
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisRegularOfFullGaloisLineUnits
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem regular_of_full : ∀ (l : ℕ) [Fact l.Prime] (C : Core l), (∀ b : Per.Bcris l, b ≠ 0 → (∀ g : GQ l, ∃ x : ℚ_[l], Per.σB g b = C.qB x * b) → IsUnit b) → C.Regular := by
  intro l _ C H K b hb hx
  classical
  have hK := K.2
  have hidx : (GK K).index ≠ 0 := by
    rw [GK, ← IntermediateField.finrank_eq_fixingSubgroup_index]
    exact Module.finrank_pos.ne'
  have hfin : Fintype (GQ l ⧸ GK K) := Subgroup.fintypeOfIndexNeZero hidx
  have hmul : ∀ (g h : GQ l) (x : Per.Bcris l), Per.σB (g * h) x = Per.σB g (Per.σB h x) :=
    (ActLaws.act_laws l).1
  have hone : ∀ x : Per.Bcris l, Per.σB (1 : GQ l) x = x := (ActLaws.act_laws l).2.1
  have hinv : ∀ (g : GQ l) (x : Per.Bcris l), Per.σB g⁻¹ (Per.σB g x) = x := fun g x => by
    rw [← hmul, inv_mul_cancel, hone]
  have hfix : ∀ (g : GQ l) (x : ℚ_[l]), Per.σB g (C.qB x) = C.qB x := fun g x =>
    (ULaws.u_laws l C).2.1 g _ _ (g.commutes x)
  have hD : IsDomain (Per.BdR l) := (BdRField.bdR_isField l).2.2.1.isDomain
  have hB : IsDomain (Per.Bcris l) := (ULaws.u_laws l C).2.2.2.1.isDomain C.ι
  have fout : ∀ g : GQ l, ∃ x : ℚ_[l], Per.σB g b = C.qB x * Per.σB (g : GQ l ⧸ GK K).out b := fun g => by
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (GK K) g
    obtain ⟨x, hx'⟩ := hx (h : GQ l)⁻¹ (inv_mem h.2)
    refine ⟨x, ?_⟩
    rw [← hfix (g : GQ l ⧸ GK K).out x, ← map_mul, ← hx', ← hmul, hh, mul_inv_cancel_right]
  choose c hc using fout
  have hP : IsUnit (∏ q : GQ l ⧸ GK K, Per.σB q.out b) := by
    refine H _ (Finset.prod_ne_zero_iff.2 fun q _ h0 => hb ?_) fun g => ⟨∏ q : GQ l ⧸ GK K, c (g * q.out), ?_⟩
    · rw [← hinv q.out b, h0, map_zero]
    · rw [map_prod, map_prod,
        ← Equiv.prod_comp (MulAction.toPerm g) fun q : GQ l ⧸ GK K => Per.σB q.out b,
        ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun q _ => ?_
      have e : MulAction.toPerm g q = ((g * q.out : GQ l) : GQ l ⧸ GK K) := by
        rw [MulAction.toPerm_apply, ← smul_eq_mul, MulAction.Quotient.mk_smul_out]
      rw [e, ← hmul, ← hc]
  have hu := isUnit_of_dvd_unit
    (Finset.dvd_prod_of_mem (fun q : GQ l ⧸ GK K => Per.σB q.out b) (Finset.mem_univ ((1 : GQ l) : GQ l ⧸ GK K))) hP
  have := hu.map (Per.σB (((1 : GQ l) : GQ l ⧸ GK K).out)⁻¹)
  rwa [hinv] at this

end GlobalTheory.MemLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisRegularOfFullGaloisLineUnitsStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bcris_regular_of_full_galois_line_units : ∀ (l : ℕ) [Fact l.Prime] (C : Core l), (∀ b : Per.Bcris l, b ≠ 0 → (∀ g : GQ l, ∃ x : ℚ_[l], Per.σB g b = C.qB x * b) → IsUnit b) → C.Regular := by
  first | exact @GlobalTheory.MemLoc.regular_of_full | exact GlobalTheory.MemLoc.regular_of_full | (intros; apply GlobalTheory.MemLoc.regular_of_full <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitCharacterOfGaloisStableLineCLTate
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitCharacterOfGaloisStableLineCLTate
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.Per

theorem exists_unit_character_of_stable_line (l : ℕ) [Fact l.Prime] (y : ℂ_[l]) (hy : y ≠ 0)
    (h : ∀ g : GQ l, ∃ x : ℚ_[l], Per.σC g y = algebraMap ℚ_[l] ℂ_[l] x * y) :
    ∃ η : GQ l →* ℤ_[l]ˣ, ∀ g : GQ l,
      Per.σC g y = algebraMap ℚ_[l] ℂ_[l] ((η g : ℤ_[l]) : ℚ_[l]) * y := by
  choose x hx using h
  have hn : ∀ g, ‖x g‖ = 1 := fun g => by
    have h1 := GlobalTheory.RingBasics.norm_σC g y
    rw [hx, norm_mul, norm_algebraMap'] at h1
    exact mul_right_cancel₀ (norm_ne_zero_iff.2 hy) (h1.trans (one_mul _).symm)
  have hm : ∀ g k, x (g * k) = x g * x k := fun g k => by
    apply (algebraMap ℚ_[l] ℂ_[l]).injective
    apply mul_right_cancel₀ hy
    rw [← hx, GlobalTheory.RingBasics.σC_mul, hx k, map_mul, TateTwist.σC_algebraMap, hx g, map_mul]
    ring
  refine ⟨MonoidHom.mk' (fun g => PadicInt.mkUnits (hn g)) fun g k => ?_, fun g => hx g⟩
  apply Units.ext
  apply Subtype.ext
  exact hm g k

end GlobalTheory.Per
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitCharacterOfGaloisStableLineCLTateStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitCharacter_of_galoisStable_line_cLTate : ∀ (l : ℕ) [Fact l.Prime] (y : ℂ_[l]), y ≠ 0 → (∀ g : GQ l, ∃ x : ℚ_[l], Per.σC g y = algebraMap ℚ_[l] ℂ_[l] x * y) → ∃ η : GQ l →* ℤ_[l]ˣ, ∀ g : GQ l, Per.σC g y = algebraMap ℚ_[l] ℂ_[l] ((η g : ℤ_[l]) : ℚ_[l]) * y := by
  first | exact @GlobalTheory.Per.exists_unit_character_of_stable_line | exact GlobalTheory.Per.exists_unit_character_of_stable_line | (intros; apply GlobalTheory.Per.exists_unit_character_of_stable_line <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfFrobeniusUnitEigenvectorGaloisLine
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfFrobeniusUnitEigenvectorGaloisLine
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.UnitLine

theorem exists_fixed {R : Type} [CommRing R] (φ σ : R →+* R) (h : ∀ a, φ (σ a) = σ (φ a)) (w c : R)
    (hw : IsUnit w) (hc : IsUnit c) (hσ : σ c = c) (hφ : φ w = c * w) :
    ∃ a, φ a = a ∧ σ w = a * w := by
  obtain ⟨v, hv⟩ := hw.exists_right_inv
  have e : σ w = σ w * v * w := by linear_combination (-σ w) * hv
  refine ⟨σ w * v, ?_, e⟩
  have h1 := congrArg φ e
  rw [map_mul φ _ w, h, hφ, map_mul σ, hσ] at h1
  apply (hc.mul hw).mul_right_cancel
  rw [← h1]
  linear_combination (-c * σ w) * hv

theorem sigma_unit_eigen : ∀ (l : ℕ) [Fact l.Prime] (w : Per.Ainf l) (u : ℤ_[l]ˣ), IsUnit w → Per.φA l w = Per.zA l u * w → ∀ g : GQ l, ∃ z : ℤ_[l], Per.σB g (Per.aB l w) = Per.zB l z * Per.aB l w := by
  intro l _ w u hw hφ g
  obtain ⟨-, -, -, -, -, h6, -, h8, -⟩ := ActLaws.act_laws l
  obtain ⟨a, ha, e⟩ := exists_fixed (Per.φA l) (Per.σA g) (ActLaws.φA_σA g) w (Per.zA l u) hw
    (u.isUnit.map _) (h8 g u) hφ
  obtain ⟨z, hz⟩ := phi_fixed_eq_padicInt l (algebraMap (Per.Ainf l) (Per.Acris l) a)
    ((PhiFix.phiA_alg l a).trans (congrArg _ ha))
  have hb : Per.aB l a = Per.zB l z := by
    rw [GlobalTheory.RingIface.zB_eq_aB_zA, GlobalTheory.RingIface.aB_eq_alg, GlobalTheory.RingIface.aB_eq_alg, hz]
  exact ⟨z, by rw [h6, e, map_mul, hb]⟩

end GlobalTheory.UnitLine
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfFrobeniusUnitEigenvectorGaloisLineStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ainf_frobenius_unit_eigenvector_galois_line : ∀ (l : ℕ) [Fact l.Prime] (w : Per.Ainf l) (u : ℤ_[l]ˣ), IsUnit w → Per.φA l w = Per.zA l u * w → ∀ g : GQ l, ∃ z : ℤ_[l], Per.σB g (Per.aB l w) = Per.zB l z * Per.aB l w := by
  first | exact @GlobalTheory.UnitLine.sigma_unit_eigen | exact GlobalTheory.UnitLine.sigma_unit_eigen | (intros; apply GlobalTheory.UnitLine.sigma_unit_eigen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisRegularOfTensorInj
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.CrisRegular
variable {l : ℕ} [Fact l.Prime] (C : Core l)

theorem exists_frob (C : Core l) :
    ∃ F : GQ l, ∀ (x : Om l) (m : ℕ), 0 < m → ¬ l ∣ m → x ^ m = 1 → F x = x ^ l := by
  obtain ⟨g, hg⟩ := FrobLaws.exists_ext C.σ
  refine ⟨g, fun ζ m hm hlm hζ => ?_⟩
  let c : ↥(MaximalUnramifiedExtension l) := ⟨ζ, IntermediateField.subset_adjoin _ _ ⟨m, hm, hlm, hζ⟩⟩
  have := C.σ_root c m hm hlm (Subtype.ext hζ)
  rw [show ζ = (c : Om l) from rfl, hg, this]; rfl

theorem qB_coe (z : ℤ_[l]) : C.qB (z : ℚ_[l]) = Per.zB l z := (GlobalTheory.T.localPeriodRingsData_unramified_laws l C).2.2.1 z

theorem ι_aB (a : Per.Ainf l) :
    C.ι (Per.aB l a) = algebraMap (Per.BdRp l) (Per.BdR l) (aDp l a) := by
  rw [GlobalTheory.RingIface.aB_eq_alg, C.ι_j, GlobalTheory.RingIface.tower, C.j_cris.on0, Subalgebra.coe_algebraMap]
  simp only [aDp, RingHom.comp_apply]

theorem theta_eig {b : Per.Bcris l} {y : Per.BdRp l}
    (h : C.ι b = algebraMap (Per.BdRp l) (Per.BdR l) y) {g : GQ l} {x : ℚ_[l]}
    (hx : Per.σB g b = C.qB x * b) :
    Per.σC g (Per.θD l y) = algebraMap ℚ_[l] ℂ_[l] x * Per.θD l y := by
  have h1 := congrArg C.ι hx
  rw [(GlobalTheory.T.localPeriodRingsData_unramified_laws l C).2.2.2.2.1, map_mul, h, (ActLaws.act_laws l).2.2.2.2.2.2.2.2.2.1,
    show C.ι (C.qB x) = _ from C.ι_u _, ← map_mul] at h1
  have h2 := congrArg (Per.θD l) ((BdRField.bdR_isField l).2.1 h1)
  rw [(thetaD_props l).2.2.2.2, map_mul, C.o_sec.th] at h2
  exact h2

theorem σB_tB (g : GQ l) : Per.σB g C.tB = C.qB ((C.χ g : ℤ_[l]) : ℚ_[l]) * C.tB := by
  rw [qB_coe, Core.tB, (ActLaws.act_laws l).2.2.2.2.2.2.2.2.2.2.2.1, TAct.t_act l C g, map_mul,
    GlobalTheory.RingIface.zB_eq_aB_zA, GlobalTheory.RingIface.aB_eq_alg]

theorem isUnit_of_theta {b : Per.Bcris l} {y : Per.BdRp l}
    (h : C.ι b = algebraMap (Per.BdRp l) (Per.BdR l) y) (hy : Per.θD l y ≠ 0)
    (hb : ∀ g : GQ l, ∃ x : ℚ_[l], Per.σB g b = C.qB x * b) : IsUnit b := by
  obtain ⟨η, hη⟩ := GlobalTheory.T.exists_unitCharacter_of_galoisStable_line_cLTate l _ hy fun g => (hb g).imp fun x hx => theta_eig C h hx
  obtain ⟨N, hN, hI⟩ := GlobalTheory.T.tate_character_finite_on_inertia_of_eigenvector l η _ hy hη
  obtain ⟨F, hF⟩ := exists_frob C
  obtain ⟨w, hw, hwI, hwF, hwφ⟩ := GlobalTheory.T.exists_unramified_period_ainf_unit l F hF (η F ^ N)⁻¹
  have h2 : C.ι (b ^ N * Per.aB l w) = algebraMap (Per.BdRp l) (Per.BdR l) (y ^ N * aDp l w) := by
    rw [map_mul, map_pow, h, ι_aB, map_mul, map_pow]
  have hθ : Per.θD l (y ^ N * aDp l w) ≠ 0 := by
    rw [map_mul, map_pow]
    exact mul_ne_zero (pow_ne_zero _ hy) ((hw.map _).map _).ne_zero
  have hact : ∀ g : GQ l, Per.σC g (Per.θD l (y ^ N * aDp l w)) =
      algebraMap ℚ_[l] ℂ_[l] (((η g ^ N : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) * Per.θD l y ^ N *
        Per.θD l (aDp l (Per.σA g w)) := by
    intro g
    rw [map_mul, map_mul, map_pow, map_pow, hη, ← (thetaD_props l).2.2.2.2,
      (ActLaws.act_laws l).2.2.2.2.2.2.2.2.2.2.1, mul_pow, ← map_pow, Units.val_pow_eq_pow_val,
      PadicInt.coe_pow]
  have hfix := GlobalTheory.T.fixed_of_fixed_inertia_of_fixed_frobenius l F hF (Per.θD l (y ^ N * aDp l w))
    (fun g hg => by rw [hact, hI g hg, hwI g hg]; simp)
    (by
      rw [hact, hwF, map_mul, map_mul, ← C.o_sec.z, C.o_sec.th, map_mul, map_pow]
      have e : algebraMap ℚ_[l] ℂ_[l] (((η F ^ N : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) *
          algebraMap ℚ_[l] ℂ_[l] ((((η F ^ N)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) = 1 := by
        rw [← map_mul, ← PadicInt.coe_mul, Units.mul_inv, PadicInt.coe_one, map_one]
      have e' : ((algebraMap ℚ_[l] (Om l) ((((η F ^ N)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) : Om l) : ℂ_[l]) =
        algebraMap ℚ_[l] ℂ_[l] ((((η F ^ N)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) := rfl
      rw [e']
      linear_combination (Per.θD l y ^ N * Per.θD l (aDp l w)) * e)
  have hinv : ∀ g : GQ l, Per.σB g (b ^ N * Per.aB l w) = b ^ N * Per.aB l w := by
    intro g
    obtain ⟨x, hx⟩ := hb g
    obtain ⟨z, hz⟩ := GlobalTheory.T.ainf_frobenius_unit_eigenvector_galois_line l w _ hw hwφ g
    have e : Per.σB g (b ^ N * Per.aB l w) = C.qB (x ^ N * z) * (b ^ N * Per.aB l w) := by
      rw [map_mul, map_pow, hx, hz, map_mul, map_pow, qB_coe]
      ring
    have e2 := theta_eig C h2 e
    rw [hfix] at e2
    have e3 : algebraMap ℚ_[l] ℂ_[l] (x ^ N * z) = 1 := mul_right_cancel₀ hθ (by rw [one_mul, ← e2])
    have e4 : x ^ N * (z : ℚ_[l]) = 1 := (algebraMap ℚ_[l] ℂ_[l]).injective (by rw [e3, map_one])
    rw [e, e4, map_one, one_mul]
  obtain ⟨c, -, hc⟩ := GlobalTheory.T.galoisInvariants_Bcris_eq_maxUnramified l C ⟨⊥, inferInstance⟩ _ fun g _ => hinv g
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [← hc, map_zero, map_zero] at h2
    apply hθ
    rw [(BdRField.bdR_isField l).2.1 (h2.symm.trans (map_zero _).symm), map_zero]
  have hu : IsUnit (b ^ N * Per.aB l w) := hc ▸ (Ne.isUnit hc0).map C.u
  exact (isUnit_pow_iff hN.ne').1 (isUnit_of_mul_isUnit_left hu)

theorem isUnit_of_line (b : Per.Bcris l) (h0 : b ≠ 0)
    (hb : ∀ g : GQ l, ∃ x : ℚ_[l], Per.σB g b = C.qB x * b) : IsUnit b := by
  obtain ⟨m, n, b', y, e, hy, hθ⟩ := GlobalTheory.T.bcris_exists_tPow_mul_theta_ne_zero l C b h0
  have ht : IsUnit C.tB := (core_t_unit_fil l C).1
  have hu : IsUnit b' := isUnit_of_theta C hy hθ fun g => by
    obtain ⟨x, hx⟩ := hb g
    set a : ℚ_[l] := ((C.χ g : ℤ_[l]) : ℚ_[l]) with ha
    have ha0 : a ≠ 0 := by
      rw [ha]
      exact PadicInt.coe_ne_zero.2 (C.χ g).ne_zero
    refine ⟨x * a ^ m * (a ^ n)⁻¹, ?_⟩
    have e1 := congrArg (Per.σB g) e
    rw [map_mul, map_mul, map_pow, map_pow, hx, σB_tB, ← ha] at e1
    have e2 : C.qB a ^ n * C.qB (a ^ n)⁻¹ = 1 := by
      rw [← map_pow, ← map_mul, mul_inv_cancel₀ (pow_ne_zero _ ha0), map_one]
    apply (ht.pow n).mul_left_cancel
    rw [map_mul, map_mul, map_pow]
    linear_combination (-C.qB (a ^ n)⁻¹) * e1 + (C.qB x * C.qB a ^ m * C.qB (a ^ n)⁻¹) * e -
      (C.tB ^ n * Per.σB g b') * e2
  exact isUnit_of_mul_isUnit_left (e ▸ (ht.pow n).mul hu)

end GlobalTheory.MemLoc.CrisRegular

namespace GlobalTheory.MemLoc

theorem core_regular (l : ℕ) [Fact l.Prime] (C : Core l) : C.Regular :=
  GlobalTheory.T.bcris_regular_of_full_galois_line_units l C (CrisRegular.isUnit_of_line C)

theorem regular_of_tensorInj : ∀ (l : ℕ) [Fact l.Prime] (C : Core l), C.TensorInj → C.Regular :=
  fun l _ C _ => core_regular l C

end GlobalTheory.MemLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisRegularOfTensorInjStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bcris_regular_of_tensorInj : ∀ (l : ℕ) [Fact l.Prime] (C : Core l), C.TensorInj → C.Regular := by
  first | exact @GlobalTheory.MemLoc.regular_of_tensorInj | exact GlobalTheory.MemLoc.regular_of_tensorInj | (intros; apply GlobalTheory.MemLoc.regular_of_tensorInj <;> assumption)
end
