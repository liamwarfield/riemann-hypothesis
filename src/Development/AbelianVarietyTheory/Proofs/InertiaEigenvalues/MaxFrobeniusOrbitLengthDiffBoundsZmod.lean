module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DltEqZero
public import GroundTheory.AutomorphicForms.CompactFormulaCountable
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.WachLatticeTwists.LatticeDualFibres.StatDualFibreLattice

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MaxFrobeniusOrbitLengthDiffBoundsZmod
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MaxFrobeniusOrbitLengthDiffBoundsZmod
open PowerSeries GlobalTheory.BK Function Finset

namespace GlobalTheory.BK.OrbitBound

variable {e : ℕ} (u : ZMod e)

theorem iter_mul (n : ℕ) (x : ZMod e) : (fun y => u * y)^[n] x = u ^ n * x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih => rw [iterate_succ_apply, ih, pow_succ, mul_assoc]

noncomputable def orb (x : ZMod e) : Finset (ZMod e) :=
  (range (minimalPeriod (fun y => u * y) x)).image fun k => u ^ k * x

variable {a : ℕ} (ha : 0 < a) (hu : u ^ a = 1)
include ha hu

theorem mp_pos (x : ZMod e) : 0 < minimalPeriod (fun y => u * y) x :=
  IsPeriodicPt.minimalPeriod_pos ha (by
    change (fun y => u * y)^[a] x = x
    rw [iter_mul, hu, one_mul])

theorem pow_mp_mul (x : ZMod e) : u ^ minimalPeriod (fun y => u * y) x * x = x := by
  rw [← iter_mul]; exact iterate_minimalPeriod

theorem pow_mp_mul_mul (x : ZMod e) (k : ℕ) :
    u ^ (minimalPeriod (fun y => u * y) x * k) * x = x := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.mul_succ, pow_add, mul_assoc, pow_mp_mul u ha hu x, ih]

theorem mp_sub_dvd (x y : ZMod e) : minimalPeriod (fun z => u * z) (x - y) ∣
    minimalPeriod (fun z => u * z) x * minimalPeriod (fun z => u * z) y := by
  apply IsPeriodicPt.minimalPeriod_dvd
  change (fun z => u * z)^[_] (x - y) = x - y
  rw [iter_mul, mul_sub, pow_mp_mul_mul u ha hu x, mul_comm (minimalPeriod _ x),
    pow_mp_mul_mul u ha hu y]

theorem mp_sub_pow_dvd (x : ZMod e) (k : ℕ) : minimalPeriod (fun z => u * z) (x - u ^ k * x) ∣
    minimalPeriod (fun z => u * z) x := by
  apply IsPeriodicPt.minimalPeriod_dvd
  change (fun z => u * z)^[_] (x - u ^ k * x) = x - u ^ k * x
  rw [iter_mul, mul_sub, mul_left_comm, pow_mp_mul u ha hu x]

theorem isUnit_u : IsUnit u :=
  have h : u * u ^ (a - 1) = 1 := by rw [← pow_succ', Nat.sub_add_cancel ha, hu]
  ⟨⟨u, u ^ (a - 1), h, by rw [mul_comm]; exact h⟩, rfl⟩

theorem card_orb (x : ZMod e) : (orb u x).card = minimalPeriod (fun y => u * y) x := by
  rw [orb, card_image_of_injOn, card_range]
  rw [coe_range]
  intro i hi j hj h
  refine iterate_injOn_Iio_minimalPeriod hi hj ?_
  simp only [iter_mul]
  exact h

theorem mem_orb (x : ZMod e) (n : ℕ) : u ^ n * x ∈ orb u x := by
  refine mem_image.2 ⟨n % minimalPeriod (fun y => u * y) x, mem_range.2 (Nat.mod_lt _ (mp_pos u ha hu x)), ?_⟩
  show u ^ (n % _) * x = u ^ n * x
  rw [← iter_mul, ← iter_mul]
  exact iterate_mod_minimalPeriod_eq

omit ha hu in
theorem orb_subset {Sig : Finset (ZMod e)} (hcl : ∀ c ∈ Sig, u * c ∈ Sig) {x : ZMod e}
    (hx : x ∈ Sig) : orb u x ⊆ Sig := by
  have key : ∀ k : ℕ, u ^ k * x ∈ Sig := by
    intro k
    induction k with
    | zero => simpa using hx
    | succ k ih => rw [pow_succ', mul_assoc]; exact hcl _ ih
  intro z hz
  obtain ⟨k, -, rfl⟩ := mem_image.1 hz
  exact key k

theorem four_mp_le (Sig : Finset (ZMod e)) (N : ℕ) (hcl : ∀ c ∈ Sig, u * c ∈ Sig) (h0 : (0 : ZMod e) ∈ Sig)
    (hN : Sig.card ≤ N) (h2 : 2 ≤ N) {x y : ZMod e} (hx : x ∈ Sig) (hy : y ∈ Sig) :
    4 * minimalPeriod (fun z => u * z) (x - y) ≤ N ^ 2 := by
  classical
  by_cases hyo : y ∈ orb u x
  · obtain ⟨k, -, rfl⟩ := mem_image.1 hyo
    have hle := Nat.le_of_dvd (mp_pos u ha hu x) (mp_sub_pow_dvd u ha hu x k)
    by_cases hx0 : x = 0
    · have h1 : minimalPeriod (fun y => u * y) x = 1 :=
        minimalPeriod_eq_one_iff_isFixedPt.2 (by simp [IsFixedPt, hx0])
      nlinarith
    · have hn0 : (0 : ZMod e) ∉ orb u x := by
        intro h
        obtain ⟨j, -, hj⟩ := mem_image.1 h
        exact hx0 (((isUnit_u u ha hu).pow j).mul_right_eq_zero.1 hj)
      have hsub : insert 0 (orb u x) ⊆ Sig := insert_subset h0 (orb_subset u hcl hx)
      have hc := card_le_card hsub
      rw [card_insert_of_notMem hn0, card_orb u ha hu] at hc
      nlinarith
  · have hdisj : Disjoint (orb u x) (orb u y) := by
      rw [disjoint_left]
      intro z hz1 hz2
      obtain ⟨i, -, rfl⟩ := mem_image.1 hz1
      obtain ⟨j, hj, hji⟩ := mem_image.1 hz2
      apply hyo
      have hy' : y = u ^ (minimalPeriod (fun z => u * z) y - j + i) * x := by
        rw [pow_add, mul_assoc, ← hji, ← mul_assoc, ← pow_add,
          Nat.sub_add_cancel (le_of_lt (mem_range.1 hj)), pow_mp_mul u ha hu y]
      rw [hy']
      exact mem_orb u ha hu x _
    have hsub : orb u x ∪ orb u y ⊆ Sig := union_subset (orb_subset u hcl hx) (orb_subset u hcl hy)
    have hc := card_le_card hsub
    rw [card_union_of_disjoint hdisj, card_orb u ha hu, card_orb u ha hu] at hc
    have hle := Nat.le_of_dvd (Nat.mul_pos (mp_pos u ha hu x) (mp_pos u ha hu y)) (mp_sub_dvd u ha hu x y)
    set m1 := minimalPeriod (fun z => u * z) x
    set m2 := minimalPeriod (fun z => u * z) y
    have h4 : 4 * (m1 * m2) ≤ (m1 + m2) ^ 2 := by
      zify; nlinarith [sq_nonneg ((m1 : ℤ) - m2)]
    have h5 : (m1 + m2) ^ 2 ≤ N ^ 2 := Nat.pow_le_pow_left (hc.trans hN) 2
    omega

end GlobalTheory.BK.OrbitBound

namespace GlobalTheory.BK

open OrbitBound in
theorem maxPeriod_bounds : ∀ (l e a : ℕ), l.Prime → 1 ≤ a → e + 1 = l ^ a → ∀ (Sig : Finset (ZMod e)) (N : ℕ),
    (∀ c ∈ Sig, (l : ZMod e) * c ∈ Sig) → (0 : ZMod e) ∈ Sig → Sig.card ≤ N → 2 ≤ N →
    1 ≤ maxPeriod l Sig ∧ 4 * maxPeriod l Sig ≤ N ^ 2 ∧ ∀ c ∈ Sig, frobPeriod l c ≤ maxPeriod l Sig := by
  intro l e a _ ha hea Sig N hcl h0 hN h2
  have hu : (l : ZMod e) ^ a = 1 := by
    rw [← Nat.cast_pow, ← hea]
    push_cast
    rw [ZMod.natCast_self, zero_add]
  have h00 : ((0 : ZMod e), (0 : ZMod e)) ∈ Sig ×ˢ Sig := mem_product.2 ⟨h0, h0⟩
  refine ⟨?_, ?_, ?_⟩
  · exact le_trans (Nat.succ_le_of_lt (mp_pos (l : ZMod e) ha hu ((0 : ZMod e) - 0)))
      (Finset.le_sup (f := fun p : ZMod e × ZMod e => frobPeriod l (p.1 - p.2)) h00)
  · obtain ⟨p, hp, hpe⟩ := Finset.exists_mem_eq_sup (Sig ×ˢ Sig) ⟨_, h00⟩
      (fun p : ZMod e × ZMod e => frobPeriod l (p.1 - p.2))
    unfold maxPeriod
    rw [hpe]
    exact four_mp_le (l : ZMod e) ha hu Sig N hcl h0 hN h2 (mem_product.1 hp).1 (mem_product.1 hp).2
  · intro c hc
    have := Finset.le_sup (f := fun p : ZMod e × ZMod e => frobPeriod l (p.1 - p.2))
      (mem_product.2 ⟨hc, h0⟩ : (c, (0 : ZMod e)) ∈ Sig ×ˢ Sig)
    simp only [sub_zero] at this
    exact this

end GlobalTheory.BK
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MaxFrobeniusOrbitLengthDiffBoundsZmodStatement
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maxFrobeniusOrbitLengthDiff_bounds_zmod : ∀ (l e a : ℕ), l.Prime → 1 ≤ a → e + 1 = l ^ a → ∀ (Sig : Finset (ZMod e)) (N : ℕ), (∀ c ∈ Sig, (l : ZMod e) * c ∈ Sig) → (0 : ZMod e) ∈ Sig → Sig.card ≤ N → 2 ≤ N → 1 ≤ maxPeriod l Sig ∧ 4 * maxPeriod l Sig ≤ N ^ 2 ∧ ∀ c ∈ Sig, frobPeriod l c ≤ maxPeriod l Sig := by
  first | exact @GlobalTheory.BK.maxPeriod_bounds | exact GlobalTheory.BK.maxPeriod_bounds | (intros; apply GlobalTheory.BK.maxPeriod_bounds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmulMemMMOfEqLphiUAdd
noncomputable section

namespace GlobalTheory.BK

open PowerSeries Filter Topology Matrix

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K]

omit [IsUltrametricDist K] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] in
private lemma coeff_eq_add_of_X_pow_succ_dvd_sub {f s g : K⟦X⟧} {c : K} {n : ℕ}
    (h : (X : K⟦X⟧) ^ (n + 1) ∣ f - (s + c • g)) :
    coeff n f = coeff n s + c * coeff n g := by
  have h0 := (PowerSeries.X_pow_dvd_iff.mp h) n (Nat.lt_succ_self n)
  rw [map_sub, map_add (f := _), PowerSeries.coeff_smul, smul_eq_mul, sub_eq_zero] at h0
  exact h0

omit [Fact l.Prime] [NormedAlgebra ℚ_[l] K] in
private lemma norm_add_mul_mul_le_max {x y c : K} {w : ℝ} (hw : 0 ≤ w) :
    ‖x + c * y‖ * w ≤ max (‖x‖ * w) (‖c‖ * (‖y‖ * w)) := by
  calc ‖x + c * y‖ * w ≤ max ‖x‖ ‖c * y‖ * w :=
        mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_add_le_max _ _) hw
    _ = max (‖x‖ * w) (‖c‖ * (‖y‖ * w)) := by
        rw [max_mul_of_nonneg _ _ hw, norm_mul, mul_assoc]

omit [IsUltrametricDist K] in
private lemma norm_natCast_prime_lt_one_inertia_eigenvalues : ‖(l : K)‖ < 1 := by
  rw [← map_natCast (algebraMap ℚ_[l] K), norm_algebraMap']
  exact Padic.norm_p_lt_one

theorem _root_.GlobalTheory.BK.mem_S_of_approx {f : K⟦X⟧}
    (h : ∀ k : ℕ, ∃ s ∈ _root_.GlobalTheory.BK.S O K e, ∀ m : ℕ,
      ∃ g ∈ _root_.GlobalTheory.BK.S O K e,
        (X : K⟦X⟧) ^ m ∣ f - (s + (l : K) ^ k • g)) : f ∈ _root_.GlobalTheory.BK.S O K e := by
  rw [_root_.GlobalTheory.BK.mem_S]
  have hw := _root_.GlobalTheory.BK.wS_nonneg (K := K) e
  refine ⟨fun n => ?_, ?_⟩
  · obtain ⟨s, hs, hm⟩ := h 0
    obtain ⟨g, hg, hdvd⟩ := hm (n + 1)
    rw [coeff_eq_add_of_X_pow_succ_dvd_sub hdvd]
    refine (norm_add_mul_mul_le_max (hw n)).trans (max_le ((_root_.GlobalTheory.BK.mem_S.mp hs).1 n) ?_)
    rw [pow_zero, norm_one, one_mul]
    exact (_root_.GlobalTheory.BK.mem_S.mp hg).1 n
  · rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε (norm_natCast_prime_lt_one_inertia_eigenvalues (K := K) (l := l))
    obtain ⟨s, hs, hm⟩ := h k
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (_root_.GlobalTheory.BK.mem_S.mp hs).2 ε hε
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨g, hg, hdvd⟩ := hm (n + 1)
    have hsn := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg (norm_nonneg _) (hw n))] at hsn ⊢
    rw [coeff_eq_add_of_X_pow_succ_dvd_sub hdvd]
    refine (norm_add_mul_mul_le_max (hw n)).trans_lt (max_lt hsn ?_)
    calc ‖(l : K) ^ k‖ * (‖coeff n g‖ * _root_.GlobalTheory.BK.wS K e n)
        ≤ ‖(l : K) ^ k‖ * 1 :=
          mul_le_mul_of_nonneg_left ((_root_.GlobalTheory.BK.mem_S.mp hg).1 n)
            (norm_nonneg _)
      _ < ε := by rw [mul_one, norm_pow]; exact hk

namespace PhiMod

variable (P : PhiMod O K l e a ι)

omit [Fact l.Prime] [NormedAlgebra ℚ_[l] K] in
theorem _root_.GlobalTheory.BK.PhiMod.l_pow_smul_mem_MM (n : ℕ) {v : _root_.GlobalTheory.BK.Vec K a ι} (hv : v ∈ P.MM) :
    (l : K) ^ n • v ∈ P.MM := by
  rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  exact nsmul_mem hv _

omit [Fact l.Prime] [NormedAlgebra ℚ_[l] K] in
theorem _root_.GlobalTheory.BK.PhiMod.smul_mem_MM {f : K⟦X⟧}
    (hf : f ∈ _root_.GlobalTheory.BK.S O K e) {v : _root_.GlobalTheory.BK.Vec K a ι}
    (hv : v ∈ P.MM) : f • v ∈ P.MM :=
  Submodule.smul_mem _ (⟨f, hf⟩ : _root_.GlobalTheory.BK.S O K e) hv

variable [NeZero e]

theorem _root_.GlobalTheory.BK.PhiMod.l_pow_smul_phi_mem_MM {k : ℕ} {v : _root_.GlobalTheory.BK.Vec K a ι}
    (hv : _root_.GlobalTheory.BK.E K l e ^ k • v ∈
      P.Mext (_root_.GlobalTheory.BK.S O K e)) :
    (l : K) ^ k • P.phi v ∈ P.MM := by
  obtain ⟨c, hc, hcE⟩ :=
    _root_.GlobalTheory.BK.exists_mul_frob_E (O := O) (K := K) l e
  set F := _root_.GlobalTheory.BK.frob K l with hF
  set E := _root_.GlobalTheory.BK.E K l e with hE
  have hw : ∀ τ i, (E ^ k • v) τ i ∈ _root_.GlobalTheory.BK.S O K e := by
    intro τ i
    unfold _root_.GlobalTheory.BK.PhiMod.Mext at hv
    rw [_root_.GlobalTheory.BK.mem_tot] at hv
    exact _root_.GlobalTheory.BK.mem_vecs.mp (hv τ) i
  have hmem : P.phi (E ^ k • v) ∈ P.MM := by
    unfold _root_.GlobalTheory.BK.PhiMod.MM
    rw [_root_.GlobalTheory.BK.PhiMod.ext, _root_.GlobalTheory.BK.mem_tot]
    intro τ
    rw [_root_.GlobalTheory.BK.PhiMod.mem_extc]
    refine ⟨_root_.GlobalTheory.BK.frobV l ((E ^ k • v) (τ - 1)), ?_, _root_.GlobalTheory.BK.PhiMod.phi_apply _ _ _⟩
    rw [_root_.GlobalTheory.BK.mem_vecs]
    intro i
    rw [_root_.GlobalTheory.BK.frobV_apply]
    exact _root_.GlobalTheory.BK.frob_mem_S l (hw _ i)
  have heq : (l : K) ^ k • P.phi v =
      ((⟨c, hc⟩ : _root_.GlobalTheory.BK.S O K e) ^ k) •
        P.phi (E ^ k • v) := by
    funext τ i
    have hvec : _root_.GlobalTheory.BK.frobV l ((E ^ k • v) (τ - 1)) =
        F E ^ k • _root_.GlobalTheory.BK.frobV l (v (τ - 1)) := by
      funext j
      simp only [Pi.smul_apply, _root_.GlobalTheory.BK.frobV_apply, smul_eq_mul, map_mul, map_pow, hF]
    change (l : K) ^ k • P.phi v τ i =
      (c ^ k) • P.phi (E ^ k • v) τ i
    rw [_root_.GlobalTheory.BK.PhiMod.phi_apply, _root_.GlobalTheory.BK.PhiMod.phi_apply, hvec, Matrix.mulVec_smul, Pi.smul_apply, smul_smul, ← mul_pow, hcE,
      ← Nat.cast_pow, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  rw [heq]
  exact Submodule.smul_mem _ _ hmem

variable {η : ℕ} (hη : ∀ v ∈ P.MM, (l : K) ^ η • P.phi v ∈ P.MM)

include hη

end PhiMod

namespace BKDat

variable [NeZero e] [NeZero a] [TameDescentExponentData K l e a] {η H : ℕ} (D : BKDat O K l e a ι η H)

end BKDat

end GlobalTheory.BK
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormGroupSignMulAndNegOne
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NegOneMemNormOfValuationEq
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NegOneMemNormOfValuationEq
open ValuativeRel

namespace GlobalTheory

open GroundTheory.LocalField in
theorem neg_one_mem_norm_of_valuation_eq : ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E], (∀ y : E, ∃ x : F, y ≤ᵥ algebraMap F E x ∧ algebraMap F E x ≤ᵥ y) → ∃ z : E, Algebra.norm F z = -1 := by
  intro F E _ _ _ _ _ _ _ _ _ _ _ hval
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[E]
  obtain ⟨x, h1, h2⟩ := hval (ϖ : E)
  have hv : valuation E (ϖ : E) = valuation E (algebraMap F E x) :=
    le_antisymm ((Valuation.Compatible.vle_iff_le _ _).1 h1) ((Valuation.Compatible.vle_iff_le _ _).1 h2)
  have hord : ord (ϖ : E) = ord (algebraMap F E x) := by
    simp only [ord]
    rw [(normalizedValuation_eq_iff (K := E)).2 hv]
  rw [ord_uniformizer hϖ, ord_algebraMap] at hord
  have he : ramificationIndex F E = 1 := by
    have hd : ((ramificationIndex F E : ℕ) : ℤ) ∣ 1 := ⟨ord x, hord⟩
    exact_mod_cast Int.eq_one_of_dvd_one (by positivity) hd
  haveI : IsUnramified F E := (isUnramified_iff F E).2 he
  obtain ⟨w, hw⟩ := normIntegerUnits_surjective (K := F) (L := E) (-1)
  refine ⟨((w : 𝒪[E]) : E), ?_⟩
  have := congrArg (fun u : 𝒪[F]ˣ => ((u : 𝒪[F]) : F)) hw
  simp only [coe_normIntegerUnits_eq] at this
  rw [← coe_norm_integer]
  simpa using this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NegOneMemNormOfValuationEqStatement
open ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_norm_eq_neg_one_of_unramified_values : ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E], (∀ y : E, ∃ x : F, y ≤ᵥ algebraMap F E x ∧ algebraMap F E x ≤ᵥ y) → ∃ z : E, Algebra.norm F z = -1 := by
  first | exact @GlobalTheory.neg_one_mem_norm_of_valuation_eq | exact GlobalTheory.neg_one_mem_norm_of_valuation_eq | (intros; apply GlobalTheory.neg_one_mem_norm_of_valuation_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormGroupSignMulAndNegOne
open scoped TensorProduct

open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.WeilQuad.NormSign

theorem exists_valuativeRel_of_normed : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [LocallyCompactSpace F],
    ∃ _ : ValuativeRel F, IsNonarchimedeanLocalField F ∧ ∀ x y : F, x ≤ᵥ y ↔ ‖x‖ ≤ ‖y‖ := by
  intro F _ _ _
  letI rel : ValuativeRel F := ValuativeRel.ofValuation (NormedField.valuation (K := F))
  have hc : (NormedField.valuation (K := F)).Compatible := Valuation.Compatible.ofValuation _
  refine ⟨rel, ?_, fun x y => Iff.rfl⟩
  refine { toIsValuativeTopology := ?_, toLocallyCompactSpace := inferInstance, toIsNontrivial := ?_ }
  · exact IsValuativeTopology.of_mem_nhds_zero_iff_vle (NormedField.valuation (K := F))
      (fun {s} => (NormedField.toValued (K := F)).is_topological_valuation s)
  · rw [ValuativeRel.isNontrivial_iff_isNontrivial (NormedField.valuation (K := F))]
    infer_instance

theorem norm_one_tmul {R B L : Type} [Field R] [CommRing B] [Algebra R B] [Field L] [Algebra R L]
    [FiniteDimensional R L] (x : L) :
    Algebra.norm B ((1 : B) ⊗ₜ[R] x) = algebraMap R B (Algebra.norm R x) := by
  have h : Algebra.lmul B (B ⊗[R] L) ((1 : B) ⊗ₜ[R] x) = (Algebra.lmul R L x).baseChange B := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro b z
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [Algebra.norm_apply, h, LinearMap.det_baseChange, Algebra.norm_apply]

theorem norm_algebraMap_of_isPushout : ∀ (F E K L : Type) [Field F] [Field E] [Field K] [CommRing L] [Algebra F E] [Algebra F K] [Algebra F L]
    [Algebra K L] [Algebra E L] [IsScalarTower F K L] [IsScalarTower F E L] [FiniteDimensional F E],
    Algebra.IsPushout F E K L → ∀ z : E, Algebra.norm K (algebraMap E L z) = algebraMap F K (Algebra.norm F z) := by
  intro F E K L _ _ _ _ _ _ _ _ _ _ _ _ h z
  haveI := h.symm
  have he : Algebra.IsPushout.equiv F K E L ((1 : K) ⊗ₜ[F] z) = algebraMap E L z := by
    simp [Algebra.IsPushout.equiv_tmul]
  rw [← he, Algebra.norm_eq_of_algEquiv, norm_one_tmul]

theorem mul_norm_of_not_norm (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [CharZero K] [Field L] [Algebra K L] (h2 : Module.finrank K L = 2)
    (s t : Kˣ) (hs : ¬ ∃ y : L, Algebra.norm K y = s) (ht : ¬ ∃ y : L, Algebra.norm K y = t) :
    ∃ y : L, Algebra.norm K y = ((s * t : Kˣ) : K) := by
  haveI : Algebra.IsQuadraticExtension K L := ⟨h2⟩
  haveI : FiniteDimensional K L := Module.finite_of_finrank_eq_succ h2
  have hN := GroundTheory.Automorphic.natCard_quotient_range_normUnits_eq_two (F := K) (E := L)
  have ht' : t ∉ (GroundTheory.LocalField.normUnits K L).range := fun h =>
    ht ((GroundTheory.Automorphic.mem_range_normUnits_iff t).1 h)
  rcases GroundTheory.Automorphic.mem_or_mul_inv_mem_of_natCard_eq_two hN ht' s with h | h
  · exact absurd ((GroundTheory.Automorphic.mem_range_normUnits_iff s).1 h) hs
  · obtain ⟨z, hz⟩ := (GroundTheory.Automorphic.mem_range_normUnits_iff _).1 h
    refine ⟨z * algebraMap K L (t : K), ?_⟩
    rw [map_mul, hz, Algebra.norm_algebraMap, h2]
    simp only [Units.val_mul, Units.val_inv_eq_inv_val]
    have := t.ne_zero
    field_simp

theorem norms_of_isField {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [hU : Unram F E] (A : Et F E) (hK : IsField A.K) (hL : IsField A.L) :
    A.NL 0 = 0 ∧
    (∀ s t : A.Kˣ, (¬ ∃ y, A.NL y = s) → (¬ ∃ y, A.NL y = t) → ∃ y, A.NL y = ((s * t : A.Kˣ) : A.K)) ∧
      ∃ y, A.NL y = ((-1 : A.Kˣ) : A.K) := by
  letI : Field A.K := hK.toField
  letI : Field A.L := hL.toField
  haveI := hU.ultraF
  haveI := hU.ultraE
  haveI := hU.lcF
  haveI := hU.lcE
  haveI := hU.charZero
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hU.finrank_eq
  have hKL : Module.finrank A.K A.L = 2 := by
    haveI := A.push.symm
    rw [← (Algebra.IsPushout.equiv F A.K E A.L).toLinearEquiv.finrank_eq, Module.finrank_baseChange,
      hU.finrank_eq]
  haveI : CharZero A.K := charZero_of_injective_algebraMap (algebraMap F A.K).injective
  obtain ⟨vF, hFloc, hFv⟩ := exists_valuativeRel_of_normed F
  refine ⟨?_, ?_⟩
  · haveI : FiniteDimensional A.K A.L := Module.finite_of_finrank_eq_succ hKL
    exact Algebra.norm_zero (R := A.K) (S := A.L)
  constructor
  · intro s t hs ht
    obtain ⟨vK, tK, hKloc, -⟩ := GroundTheory.LocalField.exists_isNonarchimedeanLocalField_valuativeExtension F A.K
    exact @mul_norm_of_not_norm A.K A.L _ vK tK hKloc _ _ _ hKL s t hs ht
  · obtain ⟨vE, hEloc, hEv⟩ := exists_valuativeRel_of_normed E
    haveI : ValuativeExtension F E := ⟨by
      intro a b
      rw [hEv, hFv, norm_algebraMap', norm_algebraMap']⟩
    obtain ⟨z, hz⟩ := GlobalTheory.T.exists_norm_eq_neg_one_of_unramified_values F E (fun y => by
      obtain ⟨x, hx⟩ := hU.unram y
      exact ⟨x, by rw [hEv, norm_algebraMap', hx], by rw [hEv, norm_algebraMap', hx]⟩)
    refine ⟨algebraMap E A.L z, ?_⟩
    have := norm_algebraMap_of_isPushout F E A.K A.L A.push z
    simp only [Et.NL, this, hz, map_neg, map_one, Units.val_neg, Units.val_one]

theorem omega_mul_neg_one : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → (∀ s t : A.Kˣ, ω ((s * t : A.Kˣ) : A.K) = ω s * ω t) ∧ ω ((-1 : A.Kˣ) : A.K) = 1 := by
  classical
  intro F E _ _ _ _ _ A ψ x μ ω h
  obtain ⟨hK, hL, -, -, hω⟩ := h
  obtain ⟨hzero, hprod, hneg⟩ := norms_of_isField A hK hL
  letI : Field A.K := hK.toField
  letI : Field A.L := hL.toField
  have hmul : ∀ s t : A.Kˣ, (∃ y, A.NL y = s) → (∃ y, A.NL y = t) → ∃ y, A.NL y = ((s * t : A.Kˣ) : A.K) := by
    rintro s t ⟨y, hy⟩ ⟨y', hy'⟩
    exact ⟨y * y', by simp only [Et.NL] at hy hy' ⊢; rw [map_mul, hy, hy', Units.val_mul]⟩
  have hdiv : ∀ s t : A.Kˣ, (∃ y, A.NL y = s) → (∃ y, A.NL y = ((s * t : A.Kˣ) : A.K)) → ∃ y, A.NL y = t := by
    rintro s t ⟨y, hy⟩ ⟨y', hy'⟩
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [hzero] at hy
      exact s.ne_zero hy.symm
    refine ⟨y' * y⁻¹, ?_⟩
    have h1 : A.NL y * A.NL y⁻¹ = 1 := by
      simp only [Et.NL]; rw [← map_mul, mul_inv_cancel₀ hy0, map_one]
    simp only [Et.NL] at hy hy' h1 ⊢
    rw [map_mul, hy', Units.val_mul]
    rw [hy] at h1
    calc (s : A.K) * t * (Algebra.norm A.K) y⁻¹ = t * ((s : A.K) * (Algebra.norm A.K) y⁻¹) := by ring
      _ = t := by rw [h1, mul_one]
  have hval : ∀ s : A.Kˣ, ω s = if ∃ y, A.NL y = s then 1 else -1 := by
    intro s
    split_ifs with hs
    · exact (hω s).1 hs
    · exact (hω s).2 hs
  refine ⟨fun s t => ?_, by rw [hval, if_pos hneg]⟩
  rw [hval s, hval t, hval (s * t)]
  by_cases hs : ∃ y, A.NL y = s <;> by_cases ht : ∃ y, A.NL y = t
  · rw [if_pos hs, if_pos ht, if_pos (hmul s t hs ht)]; ring
  · rw [if_pos hs, if_neg ht, if_neg (fun h => ht (hdiv s t hs h))]; ring
  · have hst : ¬ ∃ y, A.NL y = ((s * t : A.Kˣ) : A.K) := fun h => hs (hdiv t s ht (by rwa [mul_comm]))
    rw [if_neg hs, if_pos ht, if_neg hst]; ring
  · rw [if_neg hs, if_neg ht, if_pos (hprod s t hs ht)]; ring

end GlobalTheory.JR.WeilQuad.NormSign
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormGroupSignMulAndNegOneStatement
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normGroupSign_mul_and_neg_one : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → (∀ s t : A.Kˣ, ω ((s * t : A.Kˣ) : A.K) = ω s * ω t) ∧ ω ((-1 : A.Kˣ) : A.K) = 1 := by
  first | exact @GlobalTheory.JR.WeilQuad.NormSign.omega_mul_neg_one | exact GlobalTheory.JR.WeilQuad.NormSign.omega_mul_neg_one | (intros; apply GlobalTheory.JR.WeilQuad.NormSign.omega_mul_neg_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FractionRingQuotDivisibleByUniformizer
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FractionRingQuotDivisibleByUniformizer
open ReciprocityTheory.Gal

namespace GlobalTheory

theorem KO_divisible_by_uniformiser : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}, Irreducible ϖ →
    ∀ x : Formalism.NG.KO O, ∃ y : Formalism.NG.KO O, ϖ • y = x := by
  intro O _ _ _ ϖ hϖ x
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h0 : algebraMap O (FractionRing O) ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).mpr hϖ.ne_zero
  refine ⟨Submodule.Quotient.mk (z / algebraMap O (FractionRing O) ϖ), ?_⟩
  rw [← Submodule.Quotient.mk_smul, Algebra.smul_def, mul_div_cancel₀ _ h0]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FractionRingQuotDivisibleByUniformizerStatement
open ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fractionRingQuot_divisible_by_uniformizer : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}, Irreducible ϖ →
    ∀ x : Formalism.NG.KO O, ∃ y : Formalism.NG.KO O, ϖ • y = x := by
  first | exact @GlobalTheory.KO_divisible_by_uniformiser | exact GlobalTheory.KO_divisible_by_uniformiser | (intros; apply GlobalTheory.KO_divisible_by_uniformiser <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteResidueFieldOfCompactIsAdicDvr
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteResidueFieldOfCompactIsAdicDvr
open ReciprocityTheory.Gal

namespace GlobalTheory.ShapeNeg

theorem finite_residueField_of_compact_isAdic :
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
    [IsTopologicalRing O] [CompactSpace O], IsAdic (IsLocalRing.maximalIdeal O) →
    Finite (IsLocalRing.ResidueField O) := by
  intro O _ _ _ _ _ _ h
  have hopen : IsOpen ((IsLocalRing.maximalIdeal O : Ideal O) : Set O) := by
    have := (isAdic_iff.mp h).1 1
    simpa using this
  have hfin : Finite (O ⧸ (IsLocalRing.maximalIdeal O).toAddSubgroup) :=
    AddSubgroup.quotient_finite_of_isOpen _ hopen
  exact hfin

end GlobalTheory.ShapeNeg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteResidueFieldOfCompactIsAdicDvrStatement
open ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_residueField_of_compact_isAdic_dvr : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
    [IsTopologicalRing O] [CompactSpace O], IsAdic (IsLocalRing.maximalIdeal O) →
    Finite (IsLocalRing.ResidueField O) := by
  first | exact @GlobalTheory.ShapeNeg.finite_residueField_of_compact_isAdic | exact GlobalTheory.ShapeNeg.finite_residueField_of_compact_isAdic | (intros; apply GlobalTheory.ShapeNeg.finite_residueField_of_compact_isAdic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FractionRingQuotKilledByPowUniformizer
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FractionRingQuotKilledByPowUniformizer
open ReciprocityTheory.Gal

namespace GlobalTheory.ShapeNeg

theorem ko_killed_by_pow_uniformizer : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}, Irreducible ϖ →
    ∀ x : Formalism.NG.KO O, ∃ n : ℕ, ϖ ^ n • x = 0 := by
  intro O _ _ _ ϖ hϖ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors O) y
  have hb : (b : O) ≠ 0 := nonZeroDivisors.ne_zero b.2
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb hϖ
  refine ⟨n, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_one]
  refine ⟨a * ((u⁻¹ : Oˣ) : O), ?_⟩
  rw [Algebra.smul_def, IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.eq_mk'_iff_mul_eq,
    ← map_mul]
  congr 1
  rw [hu]
  calc a * ((u⁻¹ : Oˣ) : O) * ((u : O) * ϖ ^ n) = a * ϖ ^ n * (((u⁻¹ : Oˣ) : O) * u) := by ring
    _ = ϖ ^ n * a := by simp [mul_comm]

end GlobalTheory.ShapeNeg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FractionRingQuotKilledByPowUniformizerStatement
open ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fractionRingQuot_killed_by_pow_uniformizer : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}, Irreducible ϖ →
    ∀ x : Formalism.NG.KO O, ∃ n : ℕ, ϖ ^ n • x = 0 := by
  first | exact @GlobalTheory.ShapeNeg.ko_killed_by_pow_uniformizer | exact GlobalTheory.ShapeNeg.ko_killed_by_pow_uniformizer | (intros; apply GlobalTheory.ShapeNeg.ko_killed_by_pow_uniformizer <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContActionTorsionLevelZModOfIsLocallyConstant
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContActionTorsionLevelZModOfIsLocallyConstant
open ReciprocityTheory.Gal

namespace GlobalTheory.ShapeNeg

theorem contAction_levRepZ_of_isLocallyConstant
    {G : Type} [Group G] [TopologicalSpace G] {O : Type} [CommRing O] {M : Type} [AddCommGroup M]
    [Module O M] (ρ : Representation O G M) (p r : ℕ) [NeZero (p ^ r)] (c : O)
    (h : ((p : O) ^ r) ∈ Ideal.span {c})
    (hloc : ∀ m : M, c • m = 0 → IsLocallyConstant (fun g => ρ g m)) :
    letI := GlobalTheory.ShapeNeg.levZ (M := M) p r h
    ReciprocityTheory.Gal.ContAction (GlobalTheory.ShapeNeg.levRepZ p r h ρ) := by
  letI := GlobalTheory.ShapeNeg.levZ (M := M) p r h
  unfold ReciprocityTheory.Gal.ContAction
  apply IsLocallyConstant.continuous
  rw [IsLocallyConstant.iff_exists_open]
  rintro ⟨g₀, x₀⟩
  have hx := hloc x₀.val (Lev.smul_val x₀)
  refine ⟨{g | ρ g x₀.val = ρ g₀ x₀.val} ×ˢ {x₀},
    (hx.isOpen_fiber _).prod (isOpen_discrete _), ⟨rfl, rfl⟩, ?_⟩
  rintro ⟨g, x⟩ ⟨hg, hx'⟩
  simp only [Set.mem_singleton_iff] at hx'
  subst hx'
  apply Lev.ext
  show (levRep ρ c g x).val = (levRep ρ c g₀ x).val
  rw [levRep_val, levRep_val]
  exact hg

end GlobalTheory.ShapeNeg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContActionTorsionLevelZModOfIsLocallyConstantStatement
open ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contAction_torsionLevelZMod_of_isLocallyConstant : ∀ {G : Type} [Group G] [TopologicalSpace G] {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M]
    (ρ : Representation O G M) (p r : ℕ) [NeZero (p ^ r)] (c : O) (h : ((p : O) ^ r) ∈ Ideal.span {c}),
    (∀ m : M, c • m = 0 → IsLocallyConstant (fun g => ρ g m)) →
    letI := GlobalTheory.ShapeNeg.levZ (M := M) p r h
    ReciprocityTheory.Gal.ContAction (GlobalTheory.ShapeNeg.levRepZ p r h ρ) := by
  first | exact @GlobalTheory.ShapeNeg.contAction_levRepZ_of_isLocallyConstant | exact GlobalTheory.ShapeNeg.contAction_levRepZ_of_isLocallyConstant | (intros; apply GlobalTheory.ShapeNeg.contAction_levRepZ_of_isLocallyConstant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualLatFiniteFree
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualLatFiniteFree
open Formalism.RepresentationBoundsCohomology.LOC

namespace GlobalTheory

theorem dualLat_finite_free {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {V V' : Type} [AddCommGroup V] [Module O V] [Module (FractionRing O) V]
    [IsScalarTower O (FractionRing O) V] [AddCommGroup V'] [Module O V']
    [Module (FractionRing O) V'] [IsScalarTower O (FractionRing O) V']
    (b : V →ₗ[O] V' →ₗ[O] FractionRing O) (T : Submodule O V) :
    IsLatticeIn T → PerfectRight b →
      Module.Finite O (dualLat b T) ∧ Module.Free O (dualLat b T) := by
  classical
  rintro ⟨⟨s, hs⟩, hspan⟩ hb
  have hsT : ∀ x ∈ s, x ∈ T := fun x hx => hs ▸ Submodule.subset_span hx
  have hmem : ∀ (f : dualLat b T) (x : s), ∃ o : O, algebraMap O (FractionRing O) o = b x f :=
    fun f x => Submodule.mem_one.mp (f.2 x (hsT x x.2))
  let g0 : dualLat b T → s → O := fun f x => Classical.choose (hmem f x)
  have hg0 : ∀ f x, algebraMap O (FractionRing O) (g0 f x) = b x f :=
    fun f x => Classical.choose_spec (hmem f x)
  have hinj : Function.Injective (algebraMap O (FractionRing O)) :=
    IsFractionRing.injective O (FractionRing O)
  let g : dualLat b T →ₗ[O] (s → O) :=
    { toFun := g0
      map_add' := fun f f' => by
        funext x; apply hinj
        rw [Pi.add_apply, map_add (f := _), hg0, hg0, hg0, Submodule.coe_add, map_add (f := _)]
      map_smul' := fun c f => by
        funext x; apply hinj
        rw [Pi.smul_apply, smul_eq_mul, map_mul, hg0, hg0, Submodule.coe_smul, map_smul,
          RingHom.id_apply, Algebra.smul_def] }
  have ginj : Function.Injective g := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro f hf
    have h0 : ∀ x ∈ s, b x f = 0 := fun x hx => by
      rw [← hg0 f ⟨x, hx⟩]
      have : g0 f ⟨x, hx⟩ = 0 := congrFun hf ⟨x, hx⟩
      rw [this, map_zero]
    have hT0 : T ≤ LinearMap.ker (b.flip (f : V')) := by
      intro x hx
      rw [← hs] at hx
      refine (Submodule.span_le.mpr ?_ : Submodule.span O (s : Set V) ≤ _) hx
      intro y hy
      simpa using h0 y hy
    let ψ : V →ₗ[FractionRing O] FractionRing O :=
      (b.flip (f : V')).extendScalarsOfIsLocalization (nonZeroDivisors O) (FractionRing O)
    have hψ : ψ = 0 := by
      have : Submodule.span (FractionRing O) (T : Set V) ≤ LinearMap.ker ψ := by
        rw [Submodule.span_le]
        intro x hx
        have := hT0 hx
        simpa [ψ] using this
      rw [hspan, top_le_iff, LinearMap.ker_eq_top] at this
      exact this
    obtain ⟨f0, _, huniq⟩ := hb 0
    have e1 : (f : V') = f0 := huniq _ (fun x => by
      have := congrArg (fun φ => φ x) hψ
      simpa [ψ] using this)
    have e2 : (0 : V') = f0 := huniq _ (fun x => by simp)
    exact Subtype.ext (e1.trans e2.symm)
  have hfin : Module.Finite O (dualLat b T) := Module.Finite.of_injective g ginj
  have htf : Module.IsTorsionFree O (dualLat b T) :=
    Function.Injective.moduleIsTorsionFree g ginj (fun c m => g.map_smul c m)
  exact ⟨hfin, Module.free_of_finite_type_torsion_free'⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualLatFiniteFreeStatement
open Formalism.RepresentationBoundsCohomology.LOC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualLat_finite_free_of_isLatticeIn : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {V V' : Type} [AddCommGroup V] [Module O V] [Module (FractionRing O) V] [IsScalarTower O (FractionRing O) V] [AddCommGroup V'] [Module O V'] [Module (FractionRing O) V'] [IsScalarTower O (FractionRing O) V'] (b : V →ₗ[O] V' →ₗ[O] FractionRing O) (T : Submodule O V), IsLatticeIn T → PerfectRight b → Module.Finite O (dualLat b T) ∧ Module.Free O (dualLat b T) := by
  first | exact @GlobalTheory.dualLat_finite_free | exact GlobalTheory.dualLat_finite_free | (intros; apply GlobalTheory.dualLat_finite_free <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransferCardH0H1Eq
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransferCardH0H1Eq
open ReciprocityTheory.Gal

noncomputable section

namespace GlobalTheory.ShapeNeg

theorem transfer_card_H0_H1 : ∀ {O : Type} [CommRing O] {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']
    (i : G ≃ₜ* G') {M : Type} [AddCommGroup M] [Module O M] (ρ : Representation O G M)
    (p r : ℕ) [NeZero (p ^ r)] (c : O) (h : ((p : O) ^ r) ∈ Ideal.span {c}),
    letI := GlobalTheory.ShapeNeg.levZ (M := M) p r h
    Nat.card (ReciprocityTheory.Gal.H0 (GlobalTheory.ShapeNeg.levRep ρ c)) =
        Nat.card (ReciprocityTheory.Gal.H0 (GlobalTheory.ShapeNeg.levRepZ p r h (ρ.comp i.symm.toMulEquiv.toMonoidHom))) ∧
      Nat.card (ReciprocityTheory.Gal.H1 (GlobalTheory.ShapeNeg.levRep ρ c)) =
        Nat.card (ReciprocityTheory.Gal.H1 (GlobalTheory.ShapeNeg.levRepZ p r h (ρ.comp i.symm.toMulEquiv.toMonoidHom))) := by
  intro O _ G G' _ _ _ _ i M _ _ ρ p r _ c h
  letI := levZ (M := M) p r h

  have hact : ∀ (g' : G') (x : Lev M c),
      levRepZ p r h (ρ.comp i.symm.toMulEquiv.toMonoidHom) g' x = levRep ρ c (i.symm g') x :=
    fun g' x => rfl
  constructor
  · apply Nat.card_congr
    refine Equiv.subtypeEquivRight ?_
    intro x
    show (∀ g, levRep ρ c g x = x) ↔ ∀ g', levRepZ p r h (ρ.comp i.symm.toMulEquiv.toMonoidHom) g' x = x
    constructor
    · intro hx g'; rw [hact]; exact hx _
    · intro hx g
      have := hx (i g)
      rw [hact, ContinuousMulEquiv.symm_apply_apply] at this
      exact this
  · apply Nat.card_congr
    let ρ' := levRepZ p r h (ρ.comp i.symm.toMulEquiv.toMonoidHom)
    have hs : Continuous (i.symm : G' → G) := i.symm.continuous
    have hi : Continuous (i : G → G') := i.continuous
    let e : Z1 (levRep ρ c) ≃ Z1 ρ' :=
      { toFun := fun f => ⟨(f : G → Lev M c) ∘ i.symm, f.2.1.comp hs, fun a b => by
          show (f : G → Lev M c) (i.symm (a * b)) = (f : G → Lev M c) (i.symm a) + ρ' a ((f : G → Lev M c) (i.symm b))
          rw [map_mul, f.2.2]; rfl⟩
        invFun := fun f => ⟨(f : G' → Lev M c) ∘ i, f.2.1.comp hi, fun a b => by
          show (f : G' → Lev M c) (i (a * b)) = (f : G' → Lev M c) (i a) + levRep ρ c a ((f : G' → Lev M c) (i b))
          rw [map_mul, f.2.2, hact, ContinuousMulEquiv.symm_apply_apply]⟩
        left_inv := fun f => by
          apply Subtype.ext; funext g; show (f : G → Lev M c) (i.symm (i g)) = _
          rw [ContinuousMulEquiv.symm_apply_apply]
        right_inv := fun f => by
          apply Subtype.ext; funext g; show (f : G' → Lev M c) (i (i.symm g)) = _
          rw [ContinuousMulEquiv.apply_symm_apply] }
    refine Quotient.congr e ?_
    intro a b
    rw [Submodule.quotientRel_def, Submodule.quotientRel_def, Submodule.mem_comap, Submodule.mem_comap,
      Submodule.coe_subtype, Submodule.coe_subtype, mem_coboundaries1, mem_coboundaries1]
    constructor
    · rintro ⟨m, hm⟩
      refine ⟨m, fun g' => ?_⟩
      have := hm (i.symm g')
      rw [hact]
      exact this
    · rintro ⟨m, hm⟩
      refine ⟨m, fun g => ?_⟩
      have := hm (i g)
      rw [hact] at this
      change (a : G → Lev M c) (i.symm (i g)) - (b : G → Lev M c) (i.symm (i g)) = _ at this
      rw [ContinuousMulEquiv.symm_apply_apply] at this
      exact this

end GlobalTheory.ShapeNeg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransferCardH0H1EqStatement
open ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transfer_card_H0_H1_eq : ∀ {O : Type} [CommRing O] {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']
    (i : G ≃ₜ* G') {M : Type} [AddCommGroup M] [Module O M] (ρ : Representation O G M)
    (p r : ℕ) [NeZero (p ^ r)] (c : O) (h : ((p : O) ^ r) ∈ Ideal.span {c}),
    letI := GlobalTheory.ShapeNeg.levZ (M := M) p r h
    Nat.card (ReciprocityTheory.Gal.H0 (GlobalTheory.ShapeNeg.levRep ρ c)) =
        Nat.card (ReciprocityTheory.Gal.H0 (GlobalTheory.ShapeNeg.levRepZ p r h (ρ.comp i.symm.toMulEquiv.toMonoidHom))) ∧
      Nat.card (ReciprocityTheory.Gal.H1 (GlobalTheory.ShapeNeg.levRep ρ c)) =
        Nat.card (ReciprocityTheory.Gal.H1 (GlobalTheory.ShapeNeg.levRepZ p r h (ρ.comp i.symm.toMulEquiv.toMonoidHom))) := by
  first | exact @GlobalTheory.ShapeNeg.transfer_card_H0_H1 | exact GlobalTheory.ShapeNeg.transfer_card_H0_H1 | (intros; apply GlobalTheory.ShapeNeg.transfer_card_H0_H1 <;> assumption)
end
end
