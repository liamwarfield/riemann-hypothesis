module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CupKummerDlogModPrimePowLevelL
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GoodTupleProjectorIsProjCentral
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TorsionKaehlerSpanDlogIndep

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCocycleValueExpansionEqLogDerivSmul
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmulKaehlerDReparametrizationEq
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmulKaehlerDReparametrizationEq
open GlobalTheory.K5 GlobalTheory.Glue

noncomputable section

namespace GlobalTheory.Glue.DPsi

variable {p : ℕ} [Fact p.Prime]

theorem thL_add (a b : Lau p) : thL (a + b) = thL a + thL b := by
  ext r
  simp [thL, mul_add]

theorem thL_zero : thL (0 : Lau p) = 0 := by
  ext r
  simp [thL]

def sh (N : ℕ) (i : ℤ) (w : ℤ → ℤ_[p]) (b : Lau p) : Lau p where
  coeff r := if (N : ℤ) ∣ r then w r * b.coeff (r + i) else 0
  isPWO_support' := by
    refine (b.isPWO_support.image_of_monotone (f := fun r : ℤ => r - i) (fun x y h => by simpa using h)).mono ?_
    intro r hr
    refine ⟨r + i, ?_, by simp⟩
    intro h
    apply hr
    simp [h]

def dn (N : ℕ) (hN : 0 < N) (B : Lau p) : Lau p where
  coeff j := B.coeff ((N : ℤ) * j)
  isPWO_support' := by
    have hm : StrictMono (fun j : ℤ => (N : ℤ) * j) := fun x y h =>
      mul_lt_mul_of_pos_left h (by exact_mod_cast hN)
    have hwf := B.isPWO_support
    rw [Set.IsPWO, Set.partiallyWellOrderedOn_iff_exists_lt] at hwf ⊢
    intro g hg
    obtain ⟨m, n, hmn, h⟩ := hwf (fun k => (N : ℤ) * g k) hg
    exact ⟨m, n, hmn, hm.le_iff_le.1 h⟩

theorem coeff_natCast_mul (n : ℕ) (X : Lau p) (s : ℤ) : ((n : Lau p) * X).coeff s = (n : ℤ_[p]) * X.coeff s := by
  rw [← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℤ_[p], HahnSeries.coeff_smul, smul_eq_mul]

theorem decomp (N : ℕ) (hN : 0 < N) (b : Lau p) :
    b = ∑ i ∈ Finset.range N, HahnSeries.single (i : ℤ) (1 : ℤ_[p]) * sh N i (fun _ => 1) b := by
  ext s
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  rw [HahnSeries.coeff_sum, Finset.sum_eq_single (s % N).toNat]
  · have h0 : (((s % N).toNat : ℕ) : ℤ) = s % N := Int.toNat_of_nonneg (Int.emod_nonneg _ hN'.ne')
    have h1 : (N : ℤ) ∣ s - s % N := Int.dvd_self_sub_emod
    rw [HahnSeries.coeff_single_mul, h0]
    simp [sh, h1]
  · intro i hi hne
    have h1 : ¬ (N : ℤ) ∣ s - i := by
      intro h
      have h2 : (i : ℤ) % N = s % N := (Int.modEq_iff_dvd).2 h
      rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast Finset.mem_range.1 hi)] at h2
      apply hne
      rw [← h2]
      simp
    rw [HahnSeries.coeff_single_mul]
    simp [sh, h1]
  · intro h
    exfalso
    apply h
    rw [Finset.mem_range]
    have := Int.emod_lt_of_pos s hN'
    have := Int.emod_nonneg s hN'.ne'
    omega

theorem thL_part (N i : ℕ) (b : Lau p) :
    thL (HahnSeries.single (i : ℤ) (1 : ℤ_[p]) * sh N i (fun _ => 1) b) =
      (i : Lau p) * (HahnSeries.single (i : ℤ) (1 : ℤ_[p]) * sh N i (fun _ => 1) b) +
      (N : Lau p) * (HahnSeries.single (i : ℤ) (1 : ℤ_[p]) * sh N i (fun r => ((r / N : ℤ) : ℤ_[p])) b) := by
  ext s : 2
  rw [HahnSeries.coeff_add, coeff_natCast_mul, coeff_natCast_mul]
  change (s : ℤ_[p]) * _ = _
  simp only [HahnSeries.coeff_single_mul, sh, one_mul]
  split_ifs with h
  · have h1 : (s : ℤ_[p]) = i + N * (((s - i) / N : ℤ) : ℤ_[p]) := by
      have h2 : s = i + N * ((s - i) / N) := by rw [Int.mul_ediv_cancel' h]; ring
      exact_mod_cast congrArg (Int.cast : ℤ → ℤ_[p]) h2
    rw [← mul_assoc, ← add_mul, ← h1]
  · simp

theorem part_eq_zero {A R M : Type*} [CommRing A] [CommRing R] [Algebra A R] [AddCommGroup M] [Module R M] [Module A M]
    (D : Derivation A R M) (q β γ : R) (i N : ℕ) (hβ : D β = 0) (hN : (N : R) • D q = 0) :
    q • D (q ^ i * β) - ((i : R) * (q ^ i * β) + (N : R) * γ) • D q = 0 := by
  rw [Derivation.leibniz, hβ, smul_zero, zero_add, add_smul, mul_comm (N : R), mul_smul γ, hN, smul_zero, add_zero,
    Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul R, smul_smul, smul_smul, smul_smul, ← sub_smul]
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp
  · have h : q * β * i * q ^ (i - 1) - i * (q ^ i * β) = 0 := by
      conv_lhs => rw [← mul_pow_sub_one hi.ne' q]
      ring
    rw [h, zero_smul]

theorem smul_D_psi : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω] (T : Tower p Ω) (L : ℕ) (ψ : O0 p →+* Ω), IsReb T L ψ → ∀ (b : Lau p) (x y qL : integralClosure (O0 p) Ω), (x : Ω) = ψ (algebraMap (Lau p) (O0 p) b) → (y : Ω) = ψ (algebraMap (Lau p) (O0 p) (thL b)) → (qL : Ω) = T.qq L → qL • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) x = y • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) qL := by
  intro p hp Ω _ _ T L ψ hψ b x y qL hx hy hq
  have hqi : IsIntegral (O0 p) (T.qq L) :=
    IsIntegral.of_pow (pow_pos hp.out.pos L) (by rw [Basic.qq_pow]; exact isIntegral_algebraMap)
  have hmem : ∀ z, ψ z ∈ integralClosure (O0 p) Ω := fun z => by
    have h1 : ψ z ∈ ψ.range := ⟨z, rfl⟩
    rw [hψ.rng] at h1
    exact adjoin_le_integralClosure hqi h1
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : Lau p →+* integralClosure (O0 p) Ω, ∀ c, (Ψ c : Ω) = ψ (algebraMap (Lau p) (O0 p) c) :=
    ⟨(ψ.codRestrict (integralClosure (O0 p) Ω) hmem).comp (algebraMap (Lau p) (O0 p)), fun _ => rfl⟩
  have hx' : x = Ψ b := Subtype.ext (hx.trans (hΨ _).symm)
  have hy' : y = Ψ (thL b) := Subtype.ext (hy.trans (hΨ _).symm)
  rw [hx', hy']
  generalize KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) = D
  have hN : 0 < p ^ L := pow_pos hp.out.pos L
  have hqN : qL ^ p ^ L = algebraMap (O0 p) (integralClosure (O0 p) Ω) (qO p) :=
    Subtype.ext (by rw [SubmonoidClass.coe_pow, hq, Basic.qq_pow]; rfl)
  have hND : ((p ^ L : ℕ) : integralClosure (O0 p) Ω) • D qL = 0 := by
    have h1 : D (qL ^ p ^ L) = 0 := by rw [hqN]; exact D.map_algebraMap _
    rw [Derivation.leibniz_pow] at h1
    have h2 : qL • ((p ^ L) • qL ^ (p ^ L - 1) • D qL) = 0 := by rw [h1, smul_zero]
    rw [← Nat.cast_smul_eq_nsmul (integralClosure (O0 p) Ω), smul_smul, smul_smul, mul_right_comm,
      mul_pow_sub_one hN.ne', hqN, mul_smul] at h2
    have hu : IsUnit (algebraMap (O0 p) (integralClosure (O0 p) Ω) (qO p)) := (Basic.isUnit_qO p).map _
    exact hu.smul_left_cancel.1 (h2.trans (smul_zero _).symm)
  have hmono : ∀ i : ℕ, Ψ (HahnSeries.single (i : ℤ) (1 : ℤ_[p])) = qL ^ i := by
    intro i
    have h1 : (HahnSeries.single (i : ℤ) (1 : ℤ_[p]) : Lau p) = (HahnSeries.single (1 : ℤ) (1 : ℤ_[p])) ^ i := by
      rw [HahnSeries.single_pow]; simp
    have h2 : Ψ (HahnSeries.single (1 : ℤ) (1 : ℤ_[p])) = qL :=
      Subtype.ext (by rw [hΨ, hq]; exact hψ.par)
    rw [h1, map_pow, h2]
  have hsub : ∀ (i : ℤ), D (Ψ (sh (p ^ L) i (fun _ => 1) b)) = 0 := by
    intro i
    have h1 : Ψ (sh (p ^ L) i (fun _ => 1) b) = algebraMap (O0 p) (integralClosure (O0 p) Ω)
        (algebraMap (Lau p) (O0 p) (dn (p ^ L) hN (sh (p ^ L) i (fun _ => 1) b))) := by
      apply Subtype.ext
      rw [hΨ]
      refine hψ.sub _ _ (fun j => ?_) (fun r hr => ?_)
      · simp [dn]
      · have h2 : ¬ ((p ^ L : ℕ) : ℤ) ∣ r := by simpa using hr
        exact if_neg h2
    rw [h1]
    exact D.map_algebraMap _
  let E : Lau p →+ KaehlerDifferential (O0 p) (integralClosure (O0 p) Ω) :=
    { toFun := fun c => qL • D (Ψ c) - Ψ (thL c) • D qL
      map_zero' := by simp [thL_zero]
      map_add' := by
        intro a c
        simp only [thL_add, map_add (f := _), add_smul, smul_add]
        abel }
  have hpart : ∀ i ∈ Finset.range (p ^ L),
      E (HahnSeries.single (i : ℤ) (1 : ℤ_[p]) * sh (p ^ L) i (fun _ => 1) b) = 0 := by
    intro i _
    change qL • D (Ψ _) - Ψ (thL _) • D qL = 0
    rw [thL_part, map_add Ψ, map_mul Ψ (i : Lau p), map_mul Ψ ((p ^ L : ℕ) : Lau p), map_mul Ψ, map_natCast Ψ, map_natCast Ψ, hmono]
    exact part_eq_zero D qL _ _ i (p ^ L) (hsub i) hND
  have hE : E b = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [decomp (p ^ L) hN b, map_sum]
    exact Finset.sum_eq_zero hpart
  exact sub_eq_zero.1 hE

end GlobalTheory.Glue.DPsi
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmulKaehlerDReparametrizationEqStatement
open GlobalTheory.K5 GlobalTheory.Glue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smul_kaehlerD_reparametrization_eq : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω] (T : Tower p Ω) (L : ℕ) (ψ : O0 p →+* Ω), IsReb T L ψ → ∀ (b : Lau p) (x y qL : integralClosure (O0 p) Ω), (x : Ω) = ψ (algebraMap (Lau p) (O0 p) b) → (y : Ω) = ψ (algebraMap (Lau p) (O0 p) (thL b)) → (qL : Ω) = T.qq L → qL • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) x = y • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) qL := by
  first | exact @GlobalTheory.Glue.DPsi.smul_D_psi | exact GlobalTheory.Glue.DPsi.smul_D_psi | (intros; apply GlobalTheory.Glue.DPsi.smul_D_psi <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KaehlerDRootTwist
open GlobalTheory.K5

namespace GlobalTheory.K5

theorem kaehlerD_root_twist (R S : Type) [CommRing R] [CommRing S] [Algebra R S] (ζ : Sˣ) (r : S)
    (N a : ℕ) (hN : 1 ≤ N) (hζ : (ζ : S) ^ N = 1) :
    ((ζ : S) ^ a * r) ^ (N - 1) • KaehlerDifferential.D R S ((ζ : S) ^ a * r) =
      r ^ (N - 1) • KaehlerDifferential.D R S r +
        ((a : S) * r ^ N * ((ζ⁻¹ : Sˣ) : S)) • KaehlerDifferential.D R S (ζ : S) ∧
    (N : S) • (r ^ (N - 1) • KaehlerDifferential.D R S r) = KaehlerDifferential.D R S (r ^ N) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hzi : (ζ : S) * ((ζ⁻¹ : Sˣ) : S) = 1 := Units.mul_inv ζ
  constructor
  · rw [Derivation.leibniz, Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul S]
    simp only [smul_add, smul_smul]
    congr 2
    · have hw : ((ζ : S) ^ a) ^ (M + 1) = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
      rw [mul_pow]
      linear_combination r ^ M * hw
    · rcases a with _ | b
      · simp
      · have hw : ((ζ : S) ^ (b + 1)) ^ (M + 1) = 1 := by
          rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
        simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
        linear_combination ((b : S) + 1) * r ^ (M + 1) *
          (((ζ⁻¹ : Sˣ) : S) * hw - ((ζ : S) ^ (b + 1)) ^ M * (ζ : S) ^ b * hzi)
  · rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul S, Nat.add_sub_cancel]

end GlobalTheory.K5
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCocycleValueExpansionEqLogDerivSmul
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.K5.GeoKummer

open Polynomial

theorem kaehler_map_ex (R A B : Type) [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (f : A →ₐ[R] B) :
    ∃ φ : KaehlerDifferential R A →+ KaehlerDifferential R B, ∀ a x : A,
      φ (a • KaehlerDifferential.D R A x) = f a • KaehlerDifferential.D R B (f x) := by
  letI : Algebra A B := f.toRingHom.toAlgebra
  haveI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq (fun r => (f.commutes r).symm)
  refine ⟨(KaehlerDifferential.map R R A B).toAddMonoidHom, fun a x => ?_⟩
  simp only [LinearMap.toAddMonoidHom_coe, LinearMap.map_smul_of_tower, KaehlerDifferential.map_D]
  rw [← algebraMap_smul B a]
  rfl

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem zeta_pow_add' (T : Tower p Ω) (m k : ℕ) : T.ζ (m + k) ^ p ^ k = T.ζ m := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', pow_mul, ← add_assoc, T.ζpow, ih]

theorem qq_pow_add' (T : Tower p Ω) (m k : ℕ) : T.qq (m + k) ^ p ^ k = T.qq m := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', pow_mul, ← add_assoc, T.qpow, ih]

theorem isInt_qq (T : Tower p Ω) (m : ℕ) : IsIntegral (O0 p) (T.qq m) :=
  IsIntegral.of_pow (pow_pos hp.out.pos m) (by rw [Basic.qq_pow]; exact isIntegral_algebraMap)

theorem isInt_zeta (T : Tower p Ω) (m : ℕ) : IsIntegral (O0 p) (T.ζ m) :=
  IsIntegral.of_pow (pow_pos hp.out.pos m) (by rw [(T.prim m).pow_eq_one]; exact isIntegral_one)

theorem isInt_psi {T : Tower p Ω} {L : ℕ} {ψ : O0 p →+* Ω} (hψ : IsReb T L ψ) (b : O0 p) :
    IsIntegral (O0 p) (ψ b) := by
  have h : ψ b ∈ ψ.range := ⟨b, rfl⟩
  rw [hψ.rng] at h
  exact adjoin_le_integralClosure (isInt_qq T L) h

theorem psi_fix {T : Tower p Ω} {L : ℕ} {ψ : O0 p →+* Ω} (hψ : IsReb T L ψ) {g : Gal p Ω}
    (hg : g (T.qq L) = T.qq L) (b : O0 p) : g (ψ b) = ψ b := by
  have h : ψ b ∈ ψ.range := ⟨b, rfl⟩
  rw [hψ.rng] at h
  have hle : Algebra.adjoin (O0 p) {T.qq L} ≤ AlgHom.equalizer g.toAlgHom (AlgHom.id (O0 p) Ω) :=
    Algebra.adjoin_le (by simpa using hg)
  exact hle h

theorem exists_root_alg (hΩ : IsClo p Ω) {e : Ω} (he : IsIntegral (O0 p) e) (hea : IsAlgZp p e)
    (N : ℕ) (hN : 0 < N) : ∃ y : Ω, y ^ N = e ∧ IsIntegral (O0 p) y ∧ IsAlgZp p y := by
  haveI := hΩ.clo
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq e hN
  refine ⟨y, hy, IsIntegral.of_pow hN (hy ▸ he), ?_⟩
  obtain ⟨P, hP, hPe⟩ := hea
  refine ⟨P.comp (X ^ N), ?_, ?_⟩
  · intro h0
    rw [comp_eq_zero_iff] at h0
    rcases h0 with h0 | ⟨-, h1⟩
    · exact hP h0
    · have := congrArg natDegree h1
      rw [natDegree_X_pow, natDegree_C] at this
      omega
  · rw [Polynomial.map_comp, Polynomial.aeval_comp]
    simpa [hy] using hPe

theorem d_psi {T : Tower p Ω} {L : ℕ} {ψ : O0 p →+* Ω} (hψ : IsReb T L ψ) (b : Lau p)
    (x y qL : integralClosure (O0 p) Ω) (hx : (x : Ω) = ψ (algebraMap (Lau p) (O0 p) b))
    (hy : (y : Ω) = ψ (algebraMap (Lau p) (O0 p) (thL b))) (hq : (qL : Ω) = T.qq L) :
    qL • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) x =
      y • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) qL :=
  GlobalTheory.T.smul_kaehlerD_reparametrization_eq p Ω T L ψ hψ b x y qL hx hy hq


set_option maxHeartbeats 2000000 in
theorem geo_cob : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : GlobalTheory.K5.Tower p Ω) (L n : ℕ), n ≤ L → 1 ≤ n → ∀ (ψ : O0 p →+* Ω), IsReb T L ψ → ∀ (cw : ℤ → Ω) (w w' r : Ω), Ev ψ cw w w' → w ≠ 0 → IsInt (p := p) w⁻¹ → r ^ (p ^ n) = w →
  ∀ a lq : Gal p Ω → ZMod (p ^ n), IsKum T n (Ggeo p Ω ⊓ Gn T L) r a → IsKum T n (Ggeo p Ω ⊓ Gn T L) (T.qq (L + n)) lq →
  Cob1 n (Ggeo p Ω ⊓ Gn T L) (fun g => (p : Ω) ^ c * ((a g).val : Ω) - (p : Ω) ^ c * (w' / w) * ((lq g).val : Ω)) := by
  intro p _ hp2
  obtain ⟨c, hc⟩ := GlobalTheory.T.torsion_kaehler_span_dlog_indep p hp2
  refine ⟨2 * c + 1, ?_⟩
  intro Ω _ _ hΩ T L n hnL hn ψ hψ cw w w' r hEv hw0 hwi hr a lq ha hlq
  obtain ⟨d, e, A, he, -, hwe, hw'e⟩ := hEv
  have hNpos : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos n
  have hN1 : 1 ≤ p ^ n := hNpos
  have hLpos : 0 < p ^ L := pow_pos (Fact.out : p.Prime).pos L
  have hL1 : 1 ≤ p ^ L := hLpos
  let qinv : O0 p := ((Basic.isUnit_qO p).unit⁻¹ : (O0 p)ˣ)
  have hqinv : algebraMap (O0 p) Ω (qO p) * algebraMap (O0 p) Ω qinv = 1 := by
    rw [← map_mul, IsUnit.mul_val_inv, map_one]

  let z : integralClosure (O0 p) Ω := ⟨T.ζ n, isInt_zeta T n⟩
  let zi : integralClosure (O0 p) Ω := ⟨T.ζ n ^ (p ^ n - 1), (isInt_zeta T n).pow _⟩
  let qn : integralClosure (O0 p) Ω := ⟨T.qq n, isInt_qq T n⟩
  let qi : integralClosure (O0 p) Ω := ⟨T.qq n ^ (p ^ n - 1) * algebraMap (O0 p) Ω qinv,
    ((isInt_qq T n).pow _).mul isIntegral_algebraMap⟩
  let qL : integralClosure (O0 p) Ω := ⟨T.qq L, isInt_qq T L⟩
  let qLi : integralClosure (O0 p) Ω := ⟨T.qq L ^ (p ^ L - 1) * algebraMap (O0 p) Ω qinv,
    ((isInt_qq T L).pow _).mul isIntegral_algebraMap⟩
  let qN : integralClosure (O0 p) Ω := ⟨T.qq (L + n), isInt_qq T (L + n)⟩
  have hzzi : z * zi = 1 := by
    apply Subtype.ext
    show T.ζ n * T.ζ n ^ (p ^ n - 1) = 1
    rw [← pow_succ', Nat.sub_add_cancel hN1, (T.prim n).pow_eq_one]
  have hqqi : qn * qi = 1 := by
    apply Subtype.ext
    show T.qq n * (T.qq n ^ (p ^ n - 1) * algebraMap (O0 p) Ω qinv) = 1
    rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hN1, Basic.qq_pow, hqinv]
  have hqL : qL * qLi = 1 := by
    apply Subtype.ext
    show T.qq L * (T.qq L ^ (p ^ L - 1) * algebraMap (O0 p) Ω qinv) = 1
    rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hL1, Basic.qq_pow, hqinv]
  have hqN : qN ^ (p ^ n) = qL := Subtype.ext (by
    show T.qq (L + n) ^ p ^ n = T.qq L; exact qq_pow_add' T L n)
  let ζS : (integralClosure (O0 p) Ω)ˣ := ⟨z, zi, hzzi, by rw [mul_comm]; exact hzzi⟩
  have hζN : (ζS : integralClosure (O0 p) Ω) ^ (p ^ n) = 1 := by
    apply Subtype.ext
    show T.ζ n ^ p ^ n = 1
    rw [(T.prim n).pow_eq_one]

  have hAI : ∀ t, IsIntegral (O0 p) (ψ (algebraMap (Lau p) (O0 p) (A t))) := fun t => isInt_psi hψ _
  have hA'I : ∀ t, IsIntegral (O0 p) (ψ (algebraMap (Lau p) (O0 p) (thL (A t)))) := fun t => isInt_psi hψ _
  let eS : Fin d → integralClosure (O0 p) Ω := fun t => ⟨e t, (he t).1⟩
  let AS : Fin d → integralClosure (O0 p) Ω := fun t => ⟨_, hAI t⟩
  let A'S : Fin d → integralClosure (O0 p) Ω := fun t => ⟨_, hA'I t⟩
  have hwI : IsIntegral (O0 p) w := by
    rw [hwe]; exact IsIntegral.sum _ fun t _ => (he t).1.mul (hAI t)
  have hw'I : IsIntegral (O0 p) w' := by
    rw [hw'e]; exact IsIntegral.sum _ fun t _ => (he t).1.mul (hA'I t)
  let wS : integralClosure (O0 p) Ω := ⟨w, hwI⟩
  let w'S : integralClosure (O0 p) Ω := ⟨w', hw'I⟩
  let wiS : integralClosure (O0 p) Ω := ⟨w⁻¹, hwi⟩
  have hwwi : wS * wiS = 1 := Subtype.ext (by show w * w⁻¹ = 1; exact mul_inv_cancel₀ hw0)
  have hwS : wS = ∑ t, eS t * AS t := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    exact hwe
  have hw'S : w'S = ∑ t, eS t * A'S t := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    exact hw'e
  have hroot : ∀ t, ∃ y : Ω, y ^ (p ^ n) = e t ∧ IsIntegral (O0 p) y ∧ IsAlgZp p y :=
    fun t => exists_root_alg hΩ (he t).1 (he t).2 (p ^ n) hNpos
  choose y hy hyI hyA using hroot
  let yS : Fin d → integralClosure (O0 p) Ω := fun t => ⟨y t, hyI t⟩
  have hyS : ∀ t, yS t ^ (p ^ n) = eS t := fun t => Subtype.ext (hy t)
  have hrI : IsIntegral (O0 p) r := IsIntegral.of_pow hNpos (hr ▸ hwI)
  let r' : integralClosure (O0 p) Ω := ⟨r, hrI⟩
  have hrN : r' ^ (p ^ n) = wS := Subtype.ext hr
  let D := KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω)

  have hterm : ∀ t, D (eS t * AS t) = ((eS t * A'S t) * qLi) • D qL + AS t • D (eS t) := by
    intro t
    have h := d_psi hψ (A t) (AS t) (A'S t) qL rfl rfl rfl
    rw [Derivation.leibniz]
    linear_combination (norm := module) (eS t * qLi) • h - (eS t * hqL) • D (AS t)
  have hd : D wS = (w'S * qLi) • D qL + ∑ t, AS t • D (eS t) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hwS, map_sum, Finset.sum_congr rfl (fun t _ => hterm t), Finset.sum_add_distrib,
      ← Finset.sum_smul, hw'S, Finset.sum_mul]
  let η := (1 * r' ^ (p ^ n - 1)) • D r' - (w'S * qLi * qN ^ (p ^ n - 1)) • D qN -
    ∑ t, (AS t * yS t ^ (p ^ n - 1)) • D (yS t)
  have hE : ((p ^ n : ℕ) : integralClosure (O0 p) Ω) • ∑ t, (AS t * yS t ^ (p ^ n - 1)) • D (yS t) =
      ∑ t, AS t • D (eS t) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    have h := (GlobalTheory.K5.kaehlerD_root_twist (O0 p) _ ζS (yS t) (p ^ n) 0 hN1 hζN).2
    rw [hyS] at h
    rw [← h, smul_smul, smul_smul, smul_smul]
    congr 1
    ring
  have hη : (p ^ n : ℕ) • η = 0 := by
    have h1 := (GlobalTheory.K5.kaehlerD_root_twist (O0 p) _ ζS r' (p ^ n) 0 hN1 hζN).2
    have h2 := (GlobalTheory.K5.kaehlerD_root_twist (O0 p) _ ζS qN (p ^ n) 0 hN1 hζN).2
    rw [hrN] at h1
    rw [hqN] at h2
    rw [← Nat.cast_smul_eq_nsmul (integralClosure (O0 p) Ω)]
    linear_combination (norm := module) h1 - (w'S * qLi) • h2 - hE + hd
  obtain ⟨hF1, hF2⟩ := hc Ω hΩ T n hn z qn zi qi rfl rfl hzzi hqqi
  obtain ⟨x, y0, hxy⟩ := hF1 η hη
  have hpI : IsIntegral (O0 p) (p : Ω) := by
    have h := Basic.isInt_intCast (p := p) (Ω := Ω) (p : ℤ)
    rw [Int.cast_natCast] at h
    exact h
  refine ⟨(p : Ω) ^ (c + 1) * w⁻¹ * (x : Ω), ((hpI.pow _).mul hwi).mul x.2, ?_⟩
  intro g hg
  have hgeo : ∀ v : Ω, IsAlgZp p v → g v = v := (Subgroup.mem_inf.1 hg).1
  have hgL := (Basic.mem_gn T L g).1 (Subgroup.mem_inf.1 hg).2
  have hLn : n + (L - n) = L := by omega
  have hgζ : g (T.ζ n) = T.ζ n := by
    have e0 := zeta_pow_add' T n (L - n)
    rw [hLn] at e0
    rw [← e0, map_pow, hgL.1]
  have hgq : g (T.qq n) = T.qq n := by
    have e0 := qq_pow_add' T n (L - n)
    rw [hLn] at e0
    rw [← e0, map_pow, hgL.2]
  have hgqinv : g (algebraMap (O0 p) Ω qinv) = algebraMap (O0 p) Ω qinv := AlgEquiv.commutes g qinv
  have hgw : g w = w := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hwe, map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [map_mul, hgeo _ (he t).2, psi_fix hψ hgL.2]
  have hgw' : g w' = w' := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hw'e, map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [map_mul, hgeo _ (he t).2, psi_fix hψ hgL.2]
  let gS := (g.toAlgHom).mapIntegralClosure
  obtain ⟨σ, hσ⟩ := kaehler_map_ex (O0 p) _ _ gS
  have hgz : gS z = z := Subtype.ext hgζ
  have hgzi : gS zi = zi := Subtype.ext (by show g (T.ζ n ^ (p ^ n - 1)) = _; rw [map_pow, hgζ])
  have hgqn : gS qn = qn := Subtype.ext hgq
  have hgqi : gS qi = qi := Subtype.ext (by
    show g (T.qq n ^ (p ^ n - 1) * algebraMap (O0 p) Ω qinv) = _; rw [map_mul, map_pow, hgq, hgqinv])
  have hgqLi : gS qLi = qLi := Subtype.ext (by
    show g (T.qq L ^ (p ^ L - 1) * algebraMap (O0 p) Ω qinv) = _; rw [map_mul, map_pow, hgL.2, hgqinv])
  have hgw'S : gS w'S = w'S := Subtype.ext hgw'
  have hgAS : ∀ t, gS (AS t) = AS t := fun t => Subtype.ext (psi_fix hψ hgL.2 _)
  have hgyS : ∀ t, gS (yS t) = yS t := fun t => Subtype.ext (hgeo _ (hyA t))
  have htr : ∀ (s t : integralClosure (O0 p) Ω) (k : ℕ), gS t = (ζS : integralClosure (O0 p) Ω) ^ k * t →
      σ ((s * t ^ (p ^ n - 1)) • D t) =
        gS s • (t ^ (p ^ n - 1) • D t + ((k : integralClosure (O0 p) Ω) * t ^ (p ^ n) * zi) • D z) := by
    intro s t k h
    rw [hσ, map_mul, map_pow, h, mul_smul, (GlobalTheory.K5.kaehlerD_root_twist (O0 p) _ ζS t (p ^ n) k hN1 hζN).1]
    rfl
  have hra : gS r' = (ζS : integralClosure (O0 p) Ω) ^ (a g).val * r' :=
    Subtype.ext (by show g r = T.ζ n ^ (a g).val * r; exact ha g hg)
  have hqa : gS qN = (ζS : integralClosure (O0 p) Ω) ^ (lq g).val * qN :=
    Subtype.ext (by show g (T.qq (L + n)) = T.ζ n ^ (lq g).val * T.qq (L + n); exact hlq g hg)
  let Aval : integralClosure (O0 p) Ω := ((a g).val : integralClosure (O0 p) Ω) -
    w'S * wiS * ((lq g).val : integralClosure (O0 p) Ω)
  have hσE : σ (∑ t, (AS t * yS t ^ (p ^ n - 1)) • D (yS t)) = ∑ t, (AS t * yS t ^ (p ^ n - 1)) • D (yS t) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [hσ, map_mul, map_pow, hgAS, hgyS]
  have hση : σ η = η + (wS * zi * Aval) • D z := by
    have e1 := htr 1 r' _ hra
    have e2 := htr (w'S * qLi) qN _ hqa
    rw [map_one, hrN] at e1
    rw [map_mul, hgw'S, hgqLi, hqN] at e2
    show σ ((1 * r' ^ (p ^ n - 1)) • D r' - (w'S * qLi * qN ^ (p ^ n - 1)) • D qN -
      ∑ t, (AS t * yS t ^ (p ^ n - 1)) • D (yS t)) = _
    rw [map_sub, map_sub, e1, e2, hσE]
    linear_combination (norm := module)
      ((w'S * zi * ((lq g).val : integralClosure (O0 p) Ω)) * hwwi) • D z -
      ((w'S * zi * ((lq g).val : integralClosure (O0 p) Ω)) * hqL) • D z
  have e1 := congrArg σ hxy
  rw [map_nsmul, hση, map_add (f := _), hσ, hσ, map_mul, map_mul, hgz, hgzi, hgqn, hgqi] at e1
  rw [← Nat.cast_smul_eq_nsmul (integralClosure (O0 p) Ω), Nat.cast_pow] at e1 hxy
  have hdiff : ((gS x - x - (p : integralClosure (O0 p) Ω) ^ c * wS * Aval) * zi) • D z +
      ((gS y0 - y0) * qi) • D qn = 0 := by
    linear_combination (norm := module) hxy - e1
  obtain ⟨⟨t, ht⟩, -⟩ := hF2 _ _ hdiff
  have ht' : (p : Ω) ^ c * (g (x : Ω) - x - (p : Ω) ^ c * w *
      (((a g).val : Ω) - w' * w⁻¹ * ((lq g).val : Ω))) =
      (p : Ω) ^ (n - 1) * t := congrArg Subtype.val ht
  have hgwi : g w⁻¹ = w⁻¹ := by rw [map_inv₀, hgw]
  have hww : w * w⁻¹ = 1 := mul_inv_cancel₀ hw0
  have hpn : (p : Ω) ^ n = (p : Ω) ^ (n - 1) * p := by rw [← pow_succ, Nat.sub_add_cancel hn]
  refine ⟨-(w⁻¹ * t), IsIntegral.neg (IsIntegral.mul hwi t.2), ?_⟩
  rw [map_mul, map_mul, map_pow, map_natCast, hgwi, div_eq_mul_inv]
  linear_combination (-(p : Ω) * w⁻¹) * ht' + (-(p : Ω) ^ (2 * c + 1) *
    (((a g).val : Ω) - w' * w⁻¹ * ((lq g).val : Ω))) * hww + (w⁻¹ * t) * hpn

end GlobalTheory.K5.GeoKummer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCocycleValueExpansionEqLogDerivSmulStatement
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerCocycle_value_expansion_eq_logDeriv_smul : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : GlobalTheory.K5.Tower p Ω) (L n : ℕ), n ≤ L → 1 ≤ n → ∀ (ψ : O0 p →+* Ω), IsReb T L ψ → ∀ (cw : ℤ → Ω) (w w' r : Ω), Ev ψ cw w w' → w ≠ 0 → IsInt (p := p) w⁻¹ → r ^ (p ^ n) = w →
  ∀ a lq : Gal p Ω → ZMod (p ^ n), IsKum T n (Ggeo p Ω ⊓ Gn T L) r a → IsKum T n (Ggeo p Ω ⊓ Gn T L) (T.qq (L + n)) lq →
  Cob1 n (Ggeo p Ω ⊓ Gn T L) (fun g => (p : Ω) ^ c * ((a g).val : Ω) - (p : Ω) ^ c * (w' / w) * ((lq g).val : Ω)) := by
  first | exact @GlobalTheory.K5.GeoKummer.geo_cob | exact GlobalTheory.K5.GeoKummer.geo_cob | (intros; apply GlobalTheory.K5.GeoKummer.geo_cob <;> assumption)
end
end

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

noncomputable section

namespace GlobalTheory.EdgeLoc

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem pow_chain (f : ℕ → Ω) (hf : ∀ k, f (k + 1) ^ p = f k) (m k : ℕ) : f (m + k) ^ (p ^ k) = f m := by
  induction k with
  | zero => simp
  | succ k ih => rw [← add_assoc, pow_succ', pow_mul, hf, ih]

theorem zeta_le (T : Tower p Ω) {n L : ℕ} (h : n ≤ L) : T.ζ L ^ (p ^ (L - n)) = T.ζ n := by
  have := pow_chain T.ζ T.ζpow n (L - n)
  rwa [Nat.add_sub_cancel' h] at this

theorem gn_fix_zeta (T : Tower p Ω) {n L : ℕ} (h : n ≤ L) {g : Gal p Ω} (hg : g ∈ Gn T L) :
    g (T.ζ n) = T.ζ n := by
  rw [← zeta_le T h, map_pow, ((Basic.mem_gn T L g).1 hg).1]

theorem kum_add (T : Tower p Ω) {n L : ℕ} (h : n ≤ L) {r : Ω} (hr : r ≠ 0) {x : Gal p Ω → ZMod (p ^ n)}
    (hx : IsKum T n (Gn T L) r x) {g g' : Gal p Ω} (hg : g ∈ Gn T L) (hg' : g' ∈ Gn T L) :
    x (g * g') = x g + x g' := by
  obtain ⟨χ, hχ⟩ := Basic.exists_isCyc T n
  rw [Basic.isKum_mul hχ hr hx hg hg', (Basic.isCyc_eq_one_iff hχ g).2 (gn_fix_zeta T h hg), one_mul]

variable (p) in
theorem adjoin_top (L : ℕ) : Algebra.adjoin (O0 p) {xn p L, yn p L} = ⊤ := by
  obtain ⟨b, hb⟩ := GlobalTheory.K5.OnFree.on_free p L
  rw [eq_top_iff]
  intro s _
  have hs : s ∈ Submodule.span (O0 p) (Set.range b) := b.span_eq ▸ Submodule.mem_top
  refine (Submodule.span_le (p := (Algebra.adjoin (O0 p) {xn p L, yn p L}).toSubmodule)).2 ?_ hs
  rintro _ ⟨⟨i, j⟩, rfl⟩
  rw [hb]
  show _ ∈ Algebra.adjoin (O0 p) {xn p L, yn p L}
  have hx : xn p L ∈ Algebra.adjoin (O0 p) {xn p L, yn p L} := Algebra.subset_adjoin (by simp)
  have hy : yn p L ∈ Algebra.adjoin (O0 p) {xn p L, yn p L} := Algebra.subset_adjoin (by simp)
  exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hx _) (Subalgebra.pow_mem _ hy _)

theorem emb_int (L : ℕ) (ι : On p L →ₐ[O0 p] Ω) (z : On p L) : IsInt (p := p) (ι z) := by
  obtain ⟨b, -⟩ := GlobalTheory.K5.OnFree.on_free p L
  haveI : Module.Finite (O0 p) (On p L) := Module.Finite.of_basis b
  haveI : Algebra.IsIntegral (O0 p) (On p L) := Algebra.IsIntegral.of_finite _ _
  exact IsIntegral.map ι (Algebra.IsIntegral.isIntegral z)

theorem emb_fix (T : Tower p Ω) {L : ℕ} {ι : On p L →ₐ[O0 p] Ω} (hι : IsEmb T L ι) {g : Gal p Ω}
    (hg : g ∈ Gn T L) (z : On p L) : g (ι z) = ι z := by
  have h := AlgHom.ext_of_adjoin_eq_top (adjoin_top p L) (φ₁ := (g : Ω →ₐ[O0 p] Ω).comp ι) (φ₂ := ι) (by
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl
    · simp [hι.1, ((Basic.mem_gn T L g).1 hg).1]
    · simp [hι.2, ((Basic.mem_gn T L g).1 hg).2])
  exact congrArg (fun φ : On p L →ₐ[O0 p] Ω => φ z) h

theorem pint (k : ℕ) : IsInt (p := p) ((p : Ω) ^ k) := by
  have := Basic.isInt_intCast (p := p) (Ω := Ω) ((p : ℤ) ^ k)
  push_cast at this
  exact this

theorem qq_int (T : Tower p Ω) (L : ℕ) : IsInt (p := p) (T.qq L) := by
  refine ⟨Polynomial.X ^ (p ^ L) - Polynomial.C (qO p),
    Polynomial.monic_X_pow_sub_C _ (pow_ne_zero _ hp.out.ne_zero), ?_⟩
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, Basic.qq_pow, sub_self]

theorem reb_mem {T : Tower p Ω} {L : ℕ} {ψ : O0 p →+* Ω} (hψ : IsReb T L ψ) (y : O0 p) :
    ψ y ∈ Algebra.adjoin (O0 p) {T.qq L} := by
  have h := ψ.mem_range_self y
  rw [hψ.rng] at h
  exact h

theorem reb_int {T : Tower p Ω} {L : ℕ} {ψ : O0 p →+* Ω} (hψ : IsReb T L ψ) (y : O0 p) :
    IsInt (p := p) (ψ y) := by
  have h : Algebra.adjoin (O0 p) {T.qq L} ≤ integralClosure (O0 p) Ω :=
    Algebra.adjoin_le (by rw [Set.singleton_subset_iff, SetLike.mem_coe, mem_integralClosure_iff]; exact qq_int T L)
  exact h (reb_mem hψ y)

theorem reb_fix {T : Tower p Ω} {L : ℕ} {ψ : O0 p →+* Ω} (hψ : IsReb T L ψ) {g : Gal p Ω}
    (hg : g (T.qq L) = T.qq L) (y : O0 p) : g (ψ y) = ψ y := by
  have h : Algebra.adjoin (O0 p) {T.qq L} ≤ AlgHom.equalizer (g : Ω →ₐ[O0 p] Ω) (AlgHom.id (O0 p) Ω) :=
    Algebra.adjoin_le (by
      rw [Set.singleton_subset_iff, SetLike.mem_coe, AlgHom.mem_equalizer]
      simpa using hg)
  have h2 := h (reb_mem hψ y)
  rw [AlgHom.mem_equalizer] at h2
  simpa using h2

theorem ev_int {T : Tower p Ω} {L : ℕ} {ψ : O0 p →+* Ω} (hψ : IsReb T L ψ) {c : ℤ → Ω} {x x' : Ω}
    (h : Ev ψ c x x') : IsInt (p := p) x ∧ IsInt (p := p) x' := by
  obtain ⟨d, e, a, he, -, rfl, rfl⟩ := h
  exact ⟨(integralClosure (O0 p) Ω).sum_mem fun t _ => (he t).1.mul (reb_int hψ _),
    (integralClosure (O0 p) Ω).sum_mem fun t _ => (he t).1.mul (reb_int hψ _)⟩

theorem ev_fix {T : Tower p Ω} {L : ℕ} {ψ : O0 p →+* Ω} (hψ : IsReb T L ψ) {c : ℤ → Ω} {x x' : Ω}
    (h : Ev ψ c x x') {g : Gal p Ω} (hg : g ∈ Ggeo p Ω ⊓ Gn T L) : g x = x ∧ g x' = x' := by
  obtain ⟨hg1, hg2⟩ := Subgroup.mem_inf.1 hg
  have hq : g (T.qq L) = T.qq L := ((Basic.mem_gn T L g).1 hg2).2
  obtain ⟨d, e, a, he, -, rfl, rfl⟩ := h
  set_option synthInstance.maxHeartbeats 100000 in
    constructor <;> rw [map_sum] <;>
      refine Finset.sum_congr rfl fun t _ => ?_ <;>
      rw [map_mul, hg1 _ (he t).2, reb_fix hψ hq]

theorem conj_mem {T : Tower p Ω} {L : ℕ} {σ g : Gal p Ω} (hσ : σ ∈ Gn T L) (hg : g ∈ Ggeo p Ω ⊓ Gn T L) :
    σ * g * σ⁻¹ ∈ Ggeo p Ω ⊓ Gn T L := by
  obtain ⟨hg1, hg2⟩ := Subgroup.mem_inf.1 hg
  refine Subgroup.mem_inf.2 ⟨fun z hz => ?_, (Gn T L).mul_mem ((Gn T L).mul_mem hσ hg2) ((Gn T L).inv_mem hσ)⟩
  have h1 : IsAlgZp p (σ⁻¹ z) := by
    obtain ⟨P, hP, e⟩ := hz
    refine ⟨P, hP, ?_⟩
    have := Polynomial.aeval_algHom_apply ((σ⁻¹ : Gal p Ω) : Ω →ₐ[O0 p] Ω) z (P.map (algebraMap ℤ_[p] (O0 p)))
    rw [e, map_zero] at this
    simpa using this
  show σ (g (σ⁻¹ z)) = z
  rw [hg1 _ h1, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

theorem algZp_root {κ ρ : Ω} (hκ : IsAlgZp p κ) {m : ℕ} (hm : 0 < m) (h : ρ ^ m = κ) : IsAlgZp p ρ := by
  obtain ⟨P, hP, e⟩ := hκ
  refine ⟨Polynomial.expand ℤ_[p] m P, (Polynomial.expand_ne_zero hm).2 hP, ?_⟩
  rw [Polynomial.map_expand, Polynomial.expand_aeval, h, e]

theorem kum_rel (T : Tower p Ω) {n : ℕ} {H : Subgroup (Gal p Ω)} {θ ρ ra rb : Ω}
    {e ka kb : Gal p Ω → ZMod (p ^ n)}
    (hθ : IsKum T n H θ e) (ha : IsKum T n H ra ka) (hb : IsKum T n H rb kb)
    (hρ : ∀ g ∈ H, g ρ = ρ) (hrel : θ * rb = ρ * ra) (hne : θ * rb ≠ 0) {g : Gal p Ω} (hg : g ∈ H) :
    Cong (p := p) n (((e g).val : Ω) + ((kb g).val : Ω)) ((ka g).val : Ω) := by
  have h1 := congrArg g hrel
  rw [map_mul, map_mul, hθ g hg, hb g hg, hρ g hg, ha g hg] at h1
  have h2 : T.ζ n ^ ((e g).val + (kb g).val) * (θ * rb) = T.ζ n ^ (ka g).val * (θ * rb) := by
    rw [pow_add]; linear_combination h1 - T.ζ n ^ (ka g).val * hrel
  have h3 := mul_right_cancel₀ hne h2
  rw [Basic.zeta_pow_eq_iff] at h3
  have := Basic.cong_natCast (Ω := Ω) h3
  push_cast at this
  exact this

end GlobalTheory.EdgeLoc

namespace GlobalTheory.EdgeLoc

theorem edge_dlog : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : GlobalTheory.K5.Tower p Ω) (L n : ℕ), n ≤ L → 1 ≤ n → ∀ (ψ : O0 p →+* Ω), IsReb T L ψ → ∀ ι : On p L →ₐ[O0 p] Ω, IsEmb T L ι →
  ∀ (u v : (On p L)ˣ) (α β α' β' : On p L), IsDlog p L (u : On p L) α β → IsDlog p L (v : On p L) α' β' →
  ∀ r s : Ω, r ^ (p ^ n) = ι u → s ^ (p ^ n) = ι v →
  ∀ x y lz η : Gal p Ω → ZMod (p ^ n), IsKum T n (Gn T L) r x → IsKum T n (Gn T L) s y → IsKum T n (Gn T L) (T.ζ (L + n)) lz →
  (∀ g ∈ (Ggeo p Ω ⊓ Gn T L), ∀ h ∈ (Ggeo p Ω ⊓ Gn T L), x g * y h = η h - η (g * h) + η g) →
  (∀ g ∈ (Ggeo p Ω ⊓ Gn T L), ∃ S : Finset Ω, ∀ h ∈ (Ggeo p Ω ⊓ Gn T L), (∀ z ∈ S, h z = g z) → η h = η g) →
  ∃ o : Ω, IsInt (p := p) o ∧ (∀ g ∈ (Ggeo p Ω ⊓ Gn T L), g o = o) ∧ ∀ σ ∈ Gn T L, ∀ (θ κ a a' b b' : Ω) (ca cb : ℤ → Ω),
    IsKum T n (Ggeo p Ω ⊓ Gn T L) θ (fun h => η (σ * h * σ⁻¹) - η h - x h * y σ + x σ * y h) →
    κ ≠ 0 → IsAlgZp p κ → θ ^ (p ^ n) * b = κ * a → Ev ψ ca a a' → Ev ψ cb b b' → a ≠ 0 → IsInt (p := p) a⁻¹ → b ≠ 0 → IsInt (p := p) b⁻¹ →
    Cong (p := p) n ((p : Ω) ^ c * (a' / a - b' / b)) (σ⁻¹ o - o - (p : Ω) ^ c * ι (α * β' - β * α') * ((lz σ).val : Ω)) := by
  intro p _ hp2
  obtain ⟨c₁, h53⟩ := GlobalTheory.T.cup_kummer_dlog_mod_primePow_levelL p hp2
  obtain ⟨c₂, hed⟩ := GlobalTheory.T.edge_class_cup_product_geometric p hp2 c₁
  obtain ⟨c₃, hgeo⟩ := GlobalTheory.T.kummerCocycle_value_expansion_eq_logDeriv_smul p hp2
  have hlevel := GlobalTheory.K5.Reb.h1_geometric_level_coboundary p hp2
  obtain ⟨c₄, h71⟩ := hlevel
  refine ⟨c₂ + c₃ + c₄, ?_⟩
  intro Ω _ _ hΩ T L n hnL hn1 ψ hψ ι hι u v α β α' β' hu hv r s hr hs x y lz η hx hy hlz hcup hloc
  haveI := hΩ.clo
  have hpn : p ^ n ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  have hr0 : r ≠ 0 := by
    rintro rfl; rw [zero_pow hpn] at hr; exact (u.isUnit.map ι).ne_zero hr.symm
  have hs0 : s ≠ 0 := by
    rintro rfl; rw [zero_pow hpn] at hs; exact (v.isUnit.map ι).ne_zero hs.symm
  obtain ⟨lq, hlq⟩ := Basic.exists_isKum T n (Gn T L) (Basic.qq_ne_zero T (L + n)) (fun g hg => by
    rw [pow_chain T.qq T.qpow L n, ((Basic.mem_gn T L g).1 hg).2])
  have hcob := h53 Ω hΩ T L n hnL hn1 ι hι u v α β α' β' hu hv r s hr hs x y lz lq hx hy hlz hlq
  have hadd : ∀ g ∈ Gn T L, ∀ h ∈ Gn T L, x (g * h) = x g + x h ∧ y (g * h) = y g + y h :=
    fun g hg h hh => ⟨kum_add T hnL hr0 hx hg hh, kum_add T hnL hs0 hy hg hh⟩
  obtain ⟨o₁, ho₁i, ho₁f, hE⟩ := hed Ω hΩ T L n hnL x y lz lq η (ι (α * β' - β * α')) hadd hlz hlq
    (emb_int L ι _) (fun g hg => emb_fix T hι hg _) hcup hloc hcob
  have hlqΔ : IsKum T n (Ggeo p Ω ⊓ Gn T L) (T.qq (L + n)) lq := fun g hg => hlq g (Subgroup.mem_inf.1 hg).2
  obtain ⟨-, h71k⟩ := h71 Ω hΩ T L n hnL lq hlqΔ
  refine ⟨(p : Ω) ^ (c₃ + c₄) * o₁, (pint _).mul ho₁i, fun g hg => by rw [map_mul, map_pow, map_natCast, ho₁f g hg], ?_⟩
  intro σ hσ θ κ a a' b b' ca cb hθ hκ0 hκ hrel hea heb ha0 hai hb0 hbi
  have hpn0 : 0 < p ^ n := Nat.pos_of_ne_zero hpn
  obtain ⟨ra, hra⟩ := IsAlgClosed.exists_pow_nat_eq a hpn0
  obtain ⟨rb, hrb⟩ := IsAlgClosed.exists_pow_nat_eq b hpn0
  have hra0 : ra ≠ 0 := by rintro rfl; rw [zero_pow hpn] at hra; exact ha0 hra.symm
  have hrb0 : rb ≠ 0 := by rintro rfl; rw [zero_pow hpn] at hrb; exact hb0 hrb.symm
  obtain ⟨ka, hka⟩ := Basic.exists_isKum T n (Ggeo p Ω ⊓ Gn T L) hra0 (fun g hg => by
    rw [hra, (ev_fix hψ hea hg).1])
  obtain ⟨kb, hkb⟩ := Basic.exists_isKum T n (Ggeo p Ω ⊓ Gn T L) hrb0 (fun g hg => by
    rw [hrb, (ev_fix hψ heb hg).1])
  obtain ⟨xa, hxai, hxa⟩ := hgeo Ω hΩ T L n hnL hn1 ψ hψ ca a a' ra hea ha0 hai hra ka lq hka hlqΔ
  obtain ⟨xb, hxbi, hxb⟩ := hgeo Ω hΩ T L n hnL hn1 ψ hψ cb b b' rb heb hb0 hbi hrb kb lq hkb hlqΔ
  have hθ0 : θ ≠ 0 := by
    rintro rfl; rw [zero_pow hpn, zero_mul] at hrel; exact mul_ne_zero hκ0 ha0 hrel.symm
  set ρ : Ω := θ * rb / ra with hρdef
  have hρpow : ρ ^ (p ^ n) = κ := by
    rw [hρdef, div_pow, mul_pow, hra, hrb, hrel, mul_div_assoc, div_self ha0, mul_one]
  have hρalg : IsAlgZp p ρ := algZp_root hκ hpn0 hρpow
  have hρfix : ∀ g ∈ Ggeo p Ω ⊓ Gn T L, g ρ = ρ := fun g hg => (Subgroup.mem_inf.1 hg).1 ρ hρalg
  have hrel' : θ * rb = ρ * ra := by rw [hρdef]; field_simp
  have hK := fun g (hg : g ∈ Ggeo p Ω ⊓ Gn T L) =>
    kum_rel T hθ hka hkb hρfix hrel' (mul_ne_zero hθ0 hrb0) hg
  obtain ⟨we, hwei, hwe⟩ := hE σ hσ
  have hθ0 : θ ≠ 0 := by
    rintro rfl; rw [zero_pow hpn, zero_mul] at hrel; exact mul_ne_zero hκ0 ha0 hrel.symm
  set ρ : Ω := θ * rb / ra with hρdef
  have hρpow : ρ ^ (p ^ n) = κ := by
    rw [hρdef, div_pow, mul_pow, hra, hrb, hrel, mul_div_assoc, div_self ha0, mul_one]
  have hρalg : IsAlgZp p ρ := algZp_root hκ hpn0 hρpow
  have hρfix : ∀ g ∈ Ggeo p Ω ⊓ Gn T L, g ρ = ρ := fun g hg => (Subgroup.mem_inf.1 hg).1 ρ hρalg
  have hrel' : θ * rb = ρ * ra := by rw [hρdef]; field_simp
  have hK := fun g (hg : g ∈ Ggeo p Ω ⊓ Gn T L) =>
    kum_rel T hθ hka hkb hρfix hrel' (mul_ne_zero hθ0 hrb0) hg
  obtain ⟨we, hwei, hwe⟩ := hE σ hσ
  have key : ∀ w, σ⁻¹ (σ w) = w := fun w => by
    rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  have hσo : ∀ g ∈ Ggeo p Ω ⊓ Gn T L, g (σ⁻¹ o₁) = σ⁻¹ o₁ := fun g hg => by
    have h1 := ho₁f _ (conj_mem hσ hg)
    calc g (σ⁻¹ o₁) = σ⁻¹ (σ (g (σ⁻¹ o₁))) := (key _).symm
      _ = σ⁻¹ ((σ * g * σ⁻¹) o₁) := rfl
      _ = σ⁻¹ o₁ := by rw [h1]
  obtain ⟨X, hXd⟩ : ∃ X : Ω, X = (p : Ω) ^ c₃ * (σ⁻¹ o₁ - o₁ - (p : Ω) ^ c₂ * ι (α * β' - β * α') * ((lz σ).val : Ω))
      - (p : Ω) ^ (c₂ + c₃) * (a' / a - b' / b) := ⟨_, rfl⟩
  have hXi : IsInt (p := p) X := by
    have ha' := (ev_int hψ hea).2
    have hb' := (ev_int hψ heb).2
    have hfi : IsInt (p := p) (ι (α * β' - β * α')) := emb_int L ι _
    have hσi : IsInt (p := p) (σ⁻¹ o₁) := Basic.isInt_gal _ ho₁i
    have hlzi : IsInt (p := p) (((lz σ).val : Ω)) := by
      have := Basic.isInt_intCast (p := p) (Ω := Ω) ((lz σ).val : ℤ)
      exact_mod_cast this
    rw [hXd, div_eq_mul_inv, div_eq_mul_inv]
    exact ((pint _).mul (((hσi.sub ho₁i).sub (((pint _).mul hfi).mul hlzi)))).sub
      ((pint _).mul ((ha'.mul hai).sub (hb'.mul hbi)))
  have hXf : ∀ g ∈ Ggeo p Ω ⊓ Gn T L, g X = X := fun g hg => by
    have hg2 := (Subgroup.mem_inf.1 hg).2
    rw [hXd]
    simp only [map_sub, map_mul, map_div₀, map_pow, map_natCast, hσo g hg, ho₁f g hg,
      emb_fix T hι hg2, (ev_fix hψ hea hg).1, (ev_fix hψ hea hg).2, (ev_fix hψ heb hg).1, (ev_fix hψ heb hg).2]
  have hXcob : Cob1 n (Ggeo p Ω ⊓ Gn T L) (fun g => X * ((lq g).val : Ω)) := by
    refine ⟨(p : Ω) ^ c₂ * (xa - xb) - (p : Ω) ^ c₃ * we,
      ((pint _).mul (hxai.sub hxbi)).sub ((pint _).mul hwei), fun g hg => ?_⟩
    obtain ⟨z1, hz1, e1⟩ := hwe g hg
    obtain ⟨z2, hz2, e2⟩ := hxa g hg
    obtain ⟨z3, hz3, e3⟩ := hxb g hg
    obtain ⟨z4, hz4, e4⟩ := hK g hg
    refine ⟨(p : Ω) ^ (c₂ + c₃) * z4 + (p : Ω) ^ c₂ * (z2 - z3) - (p : Ω) ^ c₃ * z1,
      (((pint _).mul hz4).add ((pint _).mul (hz2.sub hz3))).sub ((pint _).mul hz1), ?_⟩
    rw [hXd]
    simp only [map_sub, map_mul, map_pow, map_natCast] at e1 e2 e3 e4 ⊢
    linear_combination -(p : Ω) ^ c₃ * e1 + (p : Ω) ^ c₂ * e2 - (p : Ω) ^ c₂ * e3 + (p : Ω) ^ (c₂ + c₃) * e4
  obtain ⟨z, hz, ez⟩ := h71k X hXi hXf hXcob
  refine ⟨-z, hz.neg, ?_⟩
  rw [map_mul, map_pow, map_natCast]
  rw [hXd] at ez
  linear_combination -ez
end GlobalTheory.EdgeLoc
