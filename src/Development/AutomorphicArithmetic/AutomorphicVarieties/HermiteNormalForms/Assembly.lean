module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.ColsMinSmul
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.AcycSimp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.LogLeExp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.TorsBoundPow

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.TupExact
open CategoryTheory UpperTheory.V.KH

private noncomputable abbrev UpperTheory.V.KH.tupJ {A : Type} (s : Set A) : (s →₀ ℤ) →ₗ[ℤ] (A →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (Subtype.val : s → A)

private theorem UpperTheory.V.KH.tupJ_inj {A : Type} (s : Set A) : Function.Injective (tupJ s) :=
  Finsupp.mapDomain_injective Subtype.val_injective

private theorem UpperTheory.V.KH.tupJ_mem {A : Type} (s : Set A) (c : s →₀ ℤ) :
    tupJ s c ∈ Finsupp.supported ℤ ℤ s := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb
  | single x c =>
    rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
    exact Finsupp.single_mem_supported ℤ _ x.2

private theorem UpperTheory.V.KH.tupJ_surj {A : Type} (s : Set A) (b : A →₀ ℤ)
    (hb : b ∈ Finsupp.supported ℤ ℤ s) : ∃ c, tupJ s c = b := by
  have : Finsupp.supported ℤ ℤ s ≤ LinearMap.range (tupJ s) := by
    rw [Finsupp.supported_eq_span_single, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨Finsupp.single ⟨x, hx⟩ 1, by simp [Finsupp.lmapDomain_apply]⟩
  exact this hb

private theorem UpperTheory.V.KH.tupJ_faceD {I : Type} (S : ∀ n, Set (Fin n → I))
    (hF : UpperTheory.V.ConeExtensionAcyclic.FaceClosed S) (n : ℕ) (c : S (n + 1) →₀ ℤ) :
    tupJ (S n) (faceD (fun (i : Fin (n + 1)) (t : S (n + 1)) =>
      (⟨t.1 ∘ i.succAbove, hF n t.1 t.2 i⟩ : S n)) c) =
      UpperTheory.V.ConeExtensionAcyclic.bd I n (tupJ (S (n + 1)) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | single x c =>
    set_option synthInstance.maxHeartbeats 100000 in
      rw [faceD_single, map_sum, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      UpperTheory.V.ConeExtensionAcyclic.bd, Finsupp.linearCombination_single, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, smul_comm c,
      Finsupp.smul_single_one]

private theorem UpperTheory.V.KH.bd_zero_tupJ {I : Type} (s : Set (Fin (0 + 1) → I)) (c : s →₀ ℤ) :
    UpperTheory.V.ConeExtensionAcyclic.bd I 0 (tupJ s c) = Finsupp.single default (aug s c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb, Finsupp.single_add]
  | single x c =>
    rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      UpperTheory.V.ConeExtensionAcyclic.bd, Finsupp.linearCombination_single, aug_single]
    rw [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.val_zero, pow_zero, one_smul,
      Finsupp.smul_single_one]
    congr 1
    exact Subsingleton.elim _ _

theorem UpperTheory.V.KH.tupExact :
    ∀ (I : Type) (S : ∀ n, Set (Fin n → I)) (hF : UpperTheory.V.ConeExtensionAcyclic.FaceClosed S), (S 0).Nonempty →
      UpperTheory.V.ConeExtensionAcyclic.Acyc S → ∀ m : ℕ,
      FaceExactTo (fun p => S (p + 1))
        (fun p i t => ⟨t.1 ∘ i.succAbove, hF (p + 1) t.1 t.2 i⟩) m := by
  intro I S hF h0 hA m
  obtain ⟨t0, ht0⟩ := h0
  have hdef : (default : Fin 0 → I) ∈ S 0 := by
    rwa [Subsingleton.elim (default : Fin 0 → I) t0]
  refine ⟨fun z => ?_, fun c => ⟨fun hc => ?_, ?_⟩, fun p _ c => ⟨fun hc => ?_, ?_⟩⟩
  · obtain ⟨b, hb, hbz⟩ := hA.1 (Finsupp.single default z) (Finsupp.single_mem_supported ℤ _ hdef)
    obtain ⟨c, rfl⟩ := tupJ_surj _ b hb
    exact ⟨c, Finsupp.single_injective _ ((bd_zero_tupJ (S (0 + 1)) c).symm.trans hbz)⟩
  · obtain ⟨b, hb, hbz⟩ := hA.2 0 (tupJ _ c) (tupJ_mem _ c) (by
      rw [bd_zero_tupJ, hc, Finsupp.single_zero])
    obtain ⟨d, rfl⟩ := tupJ_surj _ b hb
    exact ⟨d, tupJ_inj _ ((tupJ_faceD S hF (0 + 1) d).trans hbz)⟩
  · rintro ⟨d, rfl⟩
    apply Finsupp.single_injective (default : Fin 0 → I)
    have h1 := bd_zero_tupJ (S (0 + 1)) (faceD (fun (i : Fin (0 + 1 + 1)) (t : S (0 + 1 + 1)) =>
      (⟨t.1 ∘ i.succAbove, hF (0 + 1) t.1 t.2 i⟩ : S (0 + 1))) d)
    rw [tupJ_faceD S hF (0 + 1) d, UpperTheory.V.ConeExtensionAcyclic.bd_bd] at h1
    exact h1.symm.trans (Finsupp.single_zero _).symm
  · obtain ⟨b, hb, hbz⟩ := hA.2 (p + 1) (tupJ _ c) (tupJ_mem _ c) (by
      rw [← tupJ_faceD S hF (p + 1) c]
      exact (congrArg (tupJ (S (p + 1))) hc).trans (map_zero _))
    obtain ⟨d, rfl⟩ := tupJ_surj _ b hb
    exact ⟨d, tupJ_inj _ ((tupJ_faceD S hF (p + 1 + 1) d).trans hbz)⟩
  · rintro ⟨d, rfl⟩
    apply tupJ_inj (S (p + 1))
    refine (tupJ_faceD S hF (p + 1) _).trans ?_
    refine (congrArg (UpperTheory.V.ConeExtensionAcyclic.bd I (p + 1)) (tupJ_faceD S hF (p + 1 + 1) d)).trans ?_
    rw [UpperTheory.V.ConeExtensionAcyclic.bd_bd, map_zero]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.ImportsAlt
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Mink3
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Torsfree
open Matrix
open scoped ComplexOrder

private theorem UpperTheory.V.KT.torsfree_sep {R : Type} [Ring R] [Module.Free ℤ R]
    (z w : R) (h : z = (3 : ℤ) • (z * w)) : z = 0 := by
  have hn : ∀ n : ℕ, z = (3 : ℤ) ^ n • (z * w ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc z = (3 : ℤ) • (z * w) := h
        _ = (3 : ℤ) • (((3 : ℤ) ^ n • (z * w ^ n)) * w) := by rw [← ih]
        _ = (3 : ℤ) ^ (n + 1) • (z * w ^ (n + 1)) := by
          rw [smul_mul_assoc, smul_smul, pow_succ', pow_succ, mul_assoc]
  let b := Module.Free.chooseBasis ℤ R
  apply b.repr.injective
  ext i
  have hd : ∀ n : ℕ, (3 : ℤ) ^ n ∣ b.repr z i := by
    intro n
    refine ⟨b.repr (z * w ^ n) i, ?_⟩
    conv_lhs => rw [hn n]
    rw [map_zsmul]
    simp
  simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]
  by_contra hne
  have h1 := Int.natAbs_le_of_dvd_ne_zero (hd (b.repr z i).natAbs) hne
  rw [Int.natAbs_pow] at h1
  have h2 : (b.repr z i).natAbs < 3 ^ (b.repr z i).natAbs := Nat.lt_pow_self (by norm_num)
  have h3 : (3 : ℤ).natAbs = 3 := rfl
  rw [h3] at h1
  omega

private theorem UpperTheory.V.KT.torsfree_binom {R : Type} [Ring R] (z : R) (k : ℕ) :
    ∃ w : R, (1 + z) ^ k = 1 + (k : ℤ) • z + z * z * w := by
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨w, hw⟩ := ih
    refine ⟨(k : ℤ) • 1 + w * (1 + z), ?_⟩
    rw [pow_succ, hw]
    push_cast
    simp only [add_smul, one_smul, mul_add, add_mul, mul_one, one_mul, smul_mul_assoc,
      mul_smul_comm, mul_assoc]
    abel

theorem UpperTheory.V.KT.torsfree :
    ∀ (R : Type) [Ring R] [Module.Free ℤ R] [Module.Finite ℤ R] (u x : R) (k : ℕ), 0 < k →
    u = 1 + 3 * x → u ^ k = 1 → u = 1 := by
  intro R _ _ _ u x k
  have h3 : ∀ y : R, 3 * y = (3 : ℤ) • y := by
    intro y
    rw [zsmul_eq_mul]; norm_num
  induction k using Nat.strong_induction_on generalizing u x with
  | _ k ih =>
    intro hk hu hpow
    rw [h3] at hu
    by_cases hdiv : 3 ∣ k
    · obtain ⟨m, rfl⟩ := hdiv
      have hm : 0 < m := by omega
      obtain ⟨w, hw⟩ := UpperTheory.V.KT.torsfree_binom ((3 : ℤ) • x) m
      rw [← hu] at hw
      set y : R := (m : ℤ) • x + x * ((3 : ℤ) • x) * w with hy
      have hv : u ^ m = 1 + (3 : ℤ) • y := by
        rw [hw, hy, smul_add, smul_comm (3 : ℤ) (m : ℤ), add_assoc, smul_mul_assoc (3 : ℤ) x,
          smul_mul_assoc (3 : ℤ)]
      have hv3 : (1 + (3 : ℤ) • y) ^ 3 = 1 := by
        rw [← hv, ← pow_mul, mul_comm, hpow]
      have hz : (3 : ℤ) • y = 0 := by
        apply UpperTheory.V.KT.torsfree_sep _ (-y - y * y)
        have hinj : Function.Injective (fun t : R => (3 : ℤ) • t) :=
          smul_right_injective R (by norm_num)
        apply hinj
        have e : (3 : ℤ) • ((3 : ℤ) • y) - (3 : ℤ) • ((3 : ℤ) • (((3 : ℤ) • y) * (-y - y * y)))
            = (1 + (3 : ℤ) • y) ^ 3 - 1 := by
          simp only [pow_succ, pow_zero, mul_add, add_mul, mul_sub, mul_neg, mul_one, one_mul,
            smul_mul_assoc, mul_smul_comm, mul_assoc]
          module
        rw [hv3, sub_self, sub_eq_zero] at e
        exact e
      rw [hz, add_zero] at hv
      exact ih m (by omega) u x hm (by rw [h3]; exact hu) hv
    · obtain ⟨w, hw⟩ := UpperTheory.V.KT.torsfree_binom ((3 : ℤ) • x) k
      rw [← hu, hpow, add_assoc, left_eq_add] at hw
      obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a * k + 3 * b = 1 := by
        have : (k : ℤ) % 3 = 1 ∨ (k : ℤ) % 3 = 2 := by omega
        rcases this with h | h
        · exact ⟨1, -((k : ℤ) / 3), by omega⟩
        · exact ⟨-1, (k : ℤ) / 3 + 1, by omega⟩
      have hz : (3 : ℤ) • x = 0 := by
        apply UpperTheory.V.KT.torsfree_sep _ (b • 1 - a • (x * w))
        have e : (3 : ℤ) • (((3 : ℤ) • x) * (b • 1 - a • (x * w)))
            = (a * k + 3 * b) • ((3 : ℤ) • x)
              - a • ((k : ℤ) • ((3 : ℤ) • x) + (3 : ℤ) • x * (3 : ℤ) • x * w) := by
          simp only [mul_sub, mul_one, smul_mul_assoc, mul_smul_comm, mul_assoc]
          module
        rw [e, hw, hab, smul_zero, sub_zero, one_smul]
      rw [hu, hz, add_zero]
end

open Matrix
open scoped ComplexOrder

theorem UpperTheory.V.KT.mink3 :
    ∀ (R : Type) [Ring R] [Module.Free ℤ R] [Module.Finite ℤ R] (H : Subgroup Rˣ), Finite H →
    Nat.card H ≤ 3 ^ Module.finrank ℤ R := by
  intro R _ _ _ H hH
  let f : H → R := fun h => ((h : Rˣ) : R)
  have hinj : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (Units.ext hab)
  have hsep : ∀ a ∈ Set.range f, ∀ b ∈ Set.range f, ∀ x : R, a - b = (3 : ℕ) • x → a = b := by
    rintro _ ⟨h1, rfl⟩ _ ⟨h2, rfl⟩ x hx
    have ha : f h1 = f h2 + 3 * x := by
      rw [sub_eq_iff_eq_add'] at hx
      rw [hx, nsmul_eq_mul, Nat.cast_ofNat]
    let u : H := h2⁻¹ * h1
    have hu : f u = 1 + 3 * (f h2⁻¹ * x) := by
      have e : f u = f h2⁻¹ * f h1 := by
        simp [f, u]
      have e2 : f h2⁻¹ * f h2 = 1 := by
        simp [f]
      rw [e, ha, mul_add, e2]
      congr 1
      noncomm_ring
    have hpow : f u ^ orderOf u = 1 := by
      have : u ^ orderOf u = 1 := pow_orderOf_eq_one u
      simp only [f]
      rw [← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow, this]
      rfl
    have h1u := UpperTheory.V.KT.torsfree R (f u) _ (orderOf u) (orderOf_pos u) hu hpow
    have hu1 : u = 1 := hinj (by rw [h1u]; simp [f])
    have : h2 = h1 := inv_mul_eq_one.mp hu1
    rw [this]
  obtain ⟨_, hcard⟩ := UpperTheory.V.KT.cardsep R 3 (by norm_num) (Set.range f) hsep
  rw [Set.ncard_range_of_injective hinj] at hcard
  exact hcard
end

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

theorem UpperTheory.V.KT.stab :
    ∀ (L : Type) [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L] (N : ℕ) (p : ℕ),
    KH.StabLe (Gm L N) (Sx L N p) (3 ^ (dd L N * N)) := by
  intro L _ _ _ N p t
  have hle : MulAction.stabilizer (Gm L N) t ≤ MulAction.stabilizer (Gm L N) (t.1 0) := by
    intro g hg
    rw [MulAction.mem_stabilizer_iff] at hg ⊢
    rw [← Sx.smul_val, hg]
  have hfin : Finite (MulAction.stabilizer (Gm L N) t) := by
    haveI := UpperTheory.V.KT.stabfin L N (t.1 0)
    exact Finite.of_injective _ (Subgroup.inclusion_injective hle)
  have hrk : Module.finrank ℤ (Matrix (Fin N) (Fin N) (𝓞 L)) = dd L N * N := by
    rw [Module.finrank_matrix, RingOfIntegers.rank]
    simp only [Fintype.card_fin, dd]
    ring
  have h := UpperTheory.V.KT.mink3 (Matrix (Fin N) (Fin N) (𝓞 L))
    (MulAction.stabilizer (Gm L N) t) hfin
  rw [hrk] at h
  exact ⟨hfin, h⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Orbnum
open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

private theorem UpperTheory.V.KT.orbit_number_power_bound (D d N p : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N) (hd : N ≤ d) :
    (D ^ N * d ^ d) ^ (1 + d * N) *
      ((2 * (N ^ N * (D ^ N * d ^ d) ^ 2) + 1) ^ d + 1) ^ (d * N * (p + 1)) ≤
    (2 * D * d) ^ (12 * (p + 1) * d ^ 3 * N) := by
  have hd1 : 1 ≤ d := le_trans hN hd
  set B := 2 * D * d with hBdef
  have hB2 : 2 ≤ B := by
    have : 1 ≤ D * d := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    rw [hBdef, mul_assoc]
    omega
  have hDB : D ≤ B := by
    rw [hBdef]
    nlinarith
  have hdB : d ≤ B := by
    rw [hBdef]
    nlinarith
  have hNB : N ≤ B := le_trans hd hdB
  have hX : D ^ N * d ^ d ≤ B ^ (2 * d) := by
    have a : D ^ N ≤ B ^ d :=
      le_trans (Nat.pow_le_pow_left hDB N) (Nat.pow_le_pow_right (by omega) hd)
    have b : d ^ d ≤ B ^ d := Nat.pow_le_pow_left hdB d
    calc D ^ N * d ^ d ≤ B ^ d * B ^ d := Nat.mul_le_mul a b
      _ = B ^ (2 * d) := by ring
  have hX1 : 1 ≤ D ^ N * d ^ d :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (pow_ne_zero _ (by omega)) (pow_ne_zero _ (by omega)))
  have hNN : N ^ N ≤ B ^ d :=
    le_trans (Nat.pow_le_pow_left hNB N) (Nat.pow_le_pow_right (by omega) hd)
  have hNN1 : 1 ≤ N ^ N := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))
  have f1 : (D ^ N * d ^ d) ^ (1 + d * N) ≤ B ^ (2 * d * (1 + d * N)) := by
    rw [pow_mul B]
    exact Nat.pow_le_pow_left hX _
  have hin : 2 * (N ^ N * (D ^ N * d ^ d) ^ 2) + 1 ≤ B ^ (5 * d + 2) := by
    have hY1 : 1 ≤ N ^ N * (D ^ N * d ^ d) ^ 2 := Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (by omega) (pow_ne_zero _ (by omega)))
    have hY : N ^ N * (D ^ N * d ^ d) ^ 2 ≤ B ^ d * (B ^ (2 * d)) ^ 2 :=
      Nat.mul_le_mul hNN (Nat.pow_le_pow_left hX 2)
    have h4 : 4 ≤ B ^ 2 := by nlinarith
    calc 2 * (N ^ N * (D ^ N * d ^ d) ^ 2) + 1 ≤ 4 * (N ^ N * (D ^ N * d ^ d) ^ 2) := by omega
      _ ≤ B ^ 2 * (B ^ d * (B ^ (2 * d)) ^ 2) := Nat.mul_le_mul h4 hY
      _ = B ^ (5 * d + 2) := by ring
  have hin2 : (2 * (N ^ N * (D ^ N * d ^ d) ^ 2) + 1) ^ d + 1 ≤ B ^ ((5 * d + 2) * d + 1) := by
    have a : (2 * (N ^ N * (D ^ N * d ^ d) ^ 2) + 1) ^ d ≤ B ^ ((5 * d + 2) * d) := by
      rw [pow_mul B]
      exact Nat.pow_le_pow_left hin d
    have b : 1 ≤ B ^ ((5 * d + 2) * d) := Nat.one_le_pow _ _ (by omega)
    calc (2 * (N ^ N * (D ^ N * d ^ d) ^ 2) + 1) ^ d + 1 ≤ 2 * B ^ ((5 * d + 2) * d) := by omega
      _ ≤ B * B ^ ((5 * d + 2) * d) := Nat.mul_le_mul_right _ hB2
      _ = B ^ ((5 * d + 2) * d + 1) := by ring
  have f2 : ((2 * (N ^ N * (D ^ N * d ^ d) ^ 2) + 1) ^ d + 1) ^ (d * N * (p + 1)) ≤
      B ^ (((5 * d + 2) * d + 1) * (d * N * (p + 1))) := by
    rw [pow_mul B]
    exact Nat.pow_le_pow_left hin2 _
  have hexp : 2 * d * (1 + d * N) + ((5 * d + 2) * d + 1) * (d * N * (p + 1)) ≤
      12 * (p + 1) * d ^ 3 * N := by
    have e1 : d ≤ d ^ 3 * N * (p + 1) := by
      have : 1 ≤ d ^ 2 * N * (p + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
      nlinarith
    have e2 : d ^ 2 * N ≤ d ^ 3 * N * (p + 1) := by
      have : 1 ≤ d * (p + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
      nlinarith
    have e3 : d * N * (p + 1) ≤ d ^ 3 * N * (p + 1) := by
      have : 1 ≤ d ^ 2 := Nat.one_le_pow _ _ (by omega)
      nlinarith
    have e4 : d ^ 2 * N * (p + 1) ≤ d ^ 3 * N * (p + 1) := by
      have : d ^ 2 * N * (p + 1) * 1 ≤ d ^ 2 * N * (p + 1) * d := Nat.mul_le_mul_left _ hd1
      nlinarith
    nlinarith
  calc (D ^ N * d ^ d) ^ (1 + d * N) *
        ((2 * (N ^ N * (D ^ N * d ^ d) ^ 2) + 1) ^ d + 1) ^ (d * N * (p + 1))
      ≤ B ^ (2 * d * (1 + d * N)) * B ^ (((5 * d + 2) * d + 1) * (d * N * (p + 1))) :=
        Nat.mul_le_mul f1 f2
    _ = B ^ (2 * d * (1 + d * N) + ((5 * d + 2) * d + 1) * (d * N * (p + 1))) := by ring
    _ ≤ B ^ (12 * (p + 1) * d ^ 3 * N) := Nat.pow_le_pow_right (by omega) hexp

theorem UpperTheory.V.KT.orbnum :
    ∀ (L : Type) [Field L] [NumberField L] (N : ℕ) (p : ℕ), 1 ≤ N →
    orbBound L N p ≤ (2 * absD L * dd L N) ^ (12 * (p + 1) * dd L N ^ 3 * N) := by
  intro L _ _ N p hN
  have hD : 1 ≤ absD L := Nat.one_le_iff_ne_zero.mpr (by
    simp only [absD, ne_eq, Int.natAbs_eq_zero]
    exact NumberField.discr_ne_zero L)
  have hd : N ≤ dd L N := by
    simp only [dd]
    have : 1 ≤ Module.finrank ℚ L := Module.finrank_pos
    nlinarith
  have := orbit_number_power_bound (absD L) (dd L N) N p hD hN hd
  simpa only [orbBound, I0, RR] using this
end

open NumberField Matrix UpperTheory.V

namespace UpperTheory.V.KT

theorem sx_exact (L : Type) [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L] (N m : ℕ) :
    KH.FaceExactTo (Sx L N) (Sx.face L N) m := by
  obtain ⟨h1, h2, h3⟩ := ConeExtensionAcyclic.acyc_simp (good L N)
  exact KH.tupExact _ _ h1 (by rw [h2]; exact Set.univ_nonempty) h3 m

theorem orbBound_mono (L : Type) [Field L] [NumberField L] (N : ℕ) {p p' : ℕ} (h : p ≤ p') :
    orbBound L N p ≤ orbBound L N p' := by
  unfold orbBound
  refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) ?_)
  exact Nat.mul_le_mul_left _ (by omega)

theorem tors_le (L : Type) [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L] (N m : ℕ) :
    KH.TorsLe (K.HGL L N m) (KH.bound m (orbBound L N m) (3 ^ (dd L N * N)) (m + 2)) :=
  KH.mainFace (Gm L N) (Sx L N) (Sx.face L N) Sx.face_smul m _ _ (Nat.one_le_pow _ _ (by norm_num))
    (sx_exact L N m)
    (fun p hp => ⟨(orb L N p).1, (orb L N p).2.trans (orbBound_mono L N hp)⟩)
    (fun p _ => stab L N p)

end UpperTheory.V.KT
