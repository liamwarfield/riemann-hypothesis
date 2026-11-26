module

public import Formalism.TruncatedSeriesCounting.RamifiedValuationInequality
public import Formalism.FrobeniusContraction.FrobeniusContractionProofs.LenBound

@[expose] public section

section -- merged from Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.ExpBound
noncomputable section

namespace Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains

private lemma lam_ge_one (ℓ H : ℕ) (hℓ : 2 ≤ ℓ) : 1 ≤ lam ℓ H := by
  unfold lam
  have h1 : (1 : ℝ) < ℓ := by exact_mod_cast (by omega : 1 < ℓ)
  rcases Nat.eq_zero_or_pos H with rfl | hH
  · simp
  · have h2 : (1 : ℝ) ≤ 2 * (H : ℝ) := by
      have : (1 : ℝ) ≤ H := by exact_mod_cast hH
      linarith
    have := Real.logb_nonneg h1 h2
    linarith

private lemma hcoef_le (x : ℝ) (hx : 11 ≤ x) :
    8 * (2 * x - 1) / (x - 1) ^ 3 + 8 / (x - 1) ^ 2 + 1 / (x * (x - 1)) ≤ 32 / x ^ 2 := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hd0 : (0 : ℝ) < x - 1 := by linarith
  have ht : (0 : ℝ) ≤ x - 11 := by linarith
  have ha : 8 * (2 * x - 1) / (x - 1) ^ 3 ≤ (41 / 2) / x ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_nonneg ht 3, pow_nonneg ht 2]
  have hb : 8 / (x - 1) ^ 2 ≤ 10 / x ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_nonneg ht 2]
  have hc : 1 / (x * (x - 1)) ≤ (11 / 10) / x ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_nonneg ht 2]
  have hx2 : (0 : ℝ) ≤ 1 / x ^ 2 := by positivity
  have e1 : (41 / 2) / x ^ 2 + 10 / x ^ 2 + (11 / 10) / x ^ 2 = (316 / 10) * (1 / x ^ 2) := by ring
  have e2 : 32 / x ^ 2 = 32 * (1 / x ^ 2) := by ring
  linarith

theorem expBound_statement : ExpBound := by
  intro ℓ hℓ h η S b a s₁ E e₂ hbh ha hs1 hE he2
  have hx : (11 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hd : (10 : ℝ) ≤ (ℓ : ℝ) - 1 := by linarith
  have hd0 : (0 : ℝ) < (ℓ : ℝ) - 1 := by linarith
  have hx0 : (0 : ℝ) < ℓ := by linarith
  have hL := lam_ge_one ℓ (h + η) (by omega)
  have hc := hcoef_le (ℓ : ℝ) hx
  have hsig : sig ℓ h η = (((h / (ℓ - 1) : ℕ) : ℝ) + 1 + η) / ((ℓ : ℝ) - 1) + 1 := by
    unfold sig
    push_cast
    ring
  have hfl : ((h / (ℓ - 1) : ℕ) : ℝ) ≤ (h : ℝ) / ((ℓ : ℝ) - 1) := by
    have h1 := Nat.cast_div_le (m := h) (n := ℓ - 1) (α := ℝ)
    rwa [Nat.cast_sub (by omega : 1 ≤ ℓ), Nat.cast_one] at h1
  rw [hsig]
  unfold sig₂ at he2 ⊢
  unfold aR at ha
  set L := lam ℓ (h + η) with hLdef
  set H : ℝ := ((h + η : ℕ) : ℝ) with hHdef
  have hhH : (h : ℝ) ≤ H := by
    rw [hHdef]
    push_cast
    linarith [(Nat.cast_nonneg η : (0 : ℝ) ≤ η)]
  have hbH : (b : ℝ) ≤ H := le_trans (by exact_mod_cast hbh) hhH
  have hH0 : 0 ≤ H := by positivity
  have hfl2 : ((h / (ℓ - 1) : ℕ) : ℝ) / ((ℓ : ℝ) - 1) ≤ H / ((ℓ : ℝ) - 1) ^ 2 := by
    rw [sq, ← div_div]
    apply div_le_div_of_nonneg_right _ hd0.le
    exact hfl.trans (div_le_div_of_nonneg_right hhH hd0.le)
  have hA : (a : ℝ) / ((ℓ : ℝ) - 1) ≤
      (H * (2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2 + 3 + L + 1) / ((ℓ : ℝ) - 1) :=
    div_le_div_of_nonneg_right ha hd0.le
  have hB : (b : ℝ) / ((ℓ : ℝ) * ((ℓ : ℝ) - 1)) ≤ H / ((ℓ : ℝ) * ((ℓ : ℝ) - 1)) :=
    div_le_div_of_nonneg_right hbH (by positivity)
  have hHc := mul_le_mul_of_nonneg_left hc hH0
  have e3 : H * (2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2 / ((ℓ : ℝ) - 1) =
      H * ((2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 3) := by
    rw [div_div, ← pow_succ, mul_div_assoc]
  have hv : 1 / ((ℓ : ℝ) - 1) ≤ 1 / 10 := by
    rw [div_le_div_iff₀ hd0 (by norm_num)]
    linarith
  have hLv : L / ((ℓ : ℝ) - 1) ≤ L / 10 := div_le_div_of_nonneg_left (by linarith) (by norm_num) hd
  have hSv : (S : ℝ) / ((ℓ : ℝ) - 1) ≤ S / 10 :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) hd
  have hηv : 0 ≤ (η : ℝ) / ((ℓ : ℝ) - 1) := by positivity
  have k1 : (2 * (a : ℝ) + 2 * (η : ℝ) + (S : ℝ)) / ((ℓ : ℝ) - 1) =
      2 * ((a : ℝ) / ((ℓ : ℝ) - 1)) + 2 * ((η : ℝ) / ((ℓ : ℝ) - 1)) + (S : ℝ) / ((ℓ : ℝ) - 1) := by
    ring
  have k2 : (3 * (a : ℝ) + (S : ℝ) + 2 * (η : ℝ)) / ((ℓ : ℝ) - 1) =
      3 * ((a : ℝ) / ((ℓ : ℝ) - 1)) + (S : ℝ) / ((ℓ : ℝ) - 1) + 2 * ((η : ℝ) / ((ℓ : ℝ) - 1)) := by
    ring
  have k3 : (H * (2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2 + 3 + L + 1) / ((ℓ : ℝ) - 1) =
      H * (2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2 / ((ℓ : ℝ) - 1) + 4 * (1 / ((ℓ : ℝ) - 1)) +
        L / ((ℓ : ℝ) - 1) := by
    ring
  have k4 : (((h / (ℓ - 1) : ℕ) : ℝ) + 1 + η) / ((ℓ : ℝ) - 1) =
      ((h / (ℓ - 1) : ℕ) : ℝ) / ((ℓ : ℝ) - 1) + 1 / ((ℓ : ℝ) - 1) + (η : ℝ) / ((ℓ : ℝ) - 1) := by
    ring
  have k5 : H * (8 * (2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 3 + 8 / ((ℓ : ℝ) - 1) ^ 2 +
      1 / ((ℓ : ℝ) * ((ℓ : ℝ) - 1))) =
      8 * (H * ((2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 3)) + 8 * (H / ((ℓ : ℝ) - 1) ^ 2) +
        H / ((ℓ : ℝ) * ((ℓ : ℝ) - 1)) := by
    ring
  have k6 : 2 * H / ((ℓ : ℝ) - 1) ^ 2 = 2 * (H / ((ℓ : ℝ) - 1) ^ 2) := by ring
  have k7 : 32 * H / (ℓ : ℝ) ^ 2 = H * (32 / (ℓ : ℝ) ^ 2) := by ring
  have k8 : 10 * (η : ℝ) / ((ℓ : ℝ) - 1) = 10 * ((η : ℝ) / ((ℓ : ℝ) - 1)) := by ring
  rw [k1] at hs1
  rw [k2] at hE
  rw [k3] at hA
  rw [k5] at hHc
  rw [k6] at he2
  rw [k4, k6, k7, k8]
  linarith

end Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains
end
end

section -- merged from Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.SubGen
noncomputable section

namespace Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains

open Formalism.WachCohomologyFacts.PLenBound in
theorem submodule_generator_count : SubGen := by
  intro O _ _ _ M _ _ _ _ ℓ e F P h
  classical

  have hA : ∀ n : ℕ, Module.length O (O ⧸ Ideal.span {ℓ ^ n}) ≤
      (n : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ}) := by
    intro n
    induction n with
    | zero =>
      have : Subsingleton (O ⧸ Ideal.span {ℓ ^ 0}) := by
        rw [pow_zero, Ideal.span_singleton_one]
        infer_instance
      simp [Module.length_eq_zero]
    | succ n ih =>
      have hle : Ideal.span {ℓ ^ (n + 1)} ≤ Ideal.span {ℓ ^ n} :=
        Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow ℓ (Nat.le_succ n))
      let g : (O ⧸ Ideal.span {ℓ ^ (n + 1)}) →ₗ[O] (O ⧸ Ideal.span {ℓ ^ n}) :=
        Submodule.mapQ _ _ LinearMap.id (fun x hx => hle hx)
      have hg : Function.Surjective g := by
        intro y
        obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ y
        exact ⟨Submodule.Quotient.mk a, rfl⟩

      let f0 : (O ⧸ Ideal.span {ℓ}) →ₗ[O] (O ⧸ Ideal.span {ℓ ^ (n + 1)}) :=
        (Ideal.span {ℓ}).liftQ (ℓ ^ n • (Ideal.span {ℓ ^ (n + 1)}).mkQ) (by
          intro a ha
          obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
          rw [LinearMap.mem_ker, LinearMap.smul_apply, ← map_smul, Submodule.mkQ_apply,
            Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton']
          exact ⟨c, by rw [smul_eq_mul]; ring⟩)
      have hf0 : ∀ x, f0 x ∈ LinearMap.ker g := by
        intro x
        obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        rw [LinearMap.mem_ker]
        simp only [f0, g, Submodule.liftQ_apply, LinearMap.smul_apply, Submodule.mkQ_apply,
          map_smul, Submodule.mapQ_apply, LinearMap.id_apply]
        rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton']
        exact ⟨a, by rw [smul_eq_mul, mul_comm]⟩
      have hf1 : Function.Surjective (f0.codRestrict (LinearMap.ker g) hf0) := by
        rintro ⟨y, hy⟩
        obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ y
        rw [LinearMap.mem_ker] at hy
        have ha : a ∈ Ideal.span {ℓ ^ n} := (Submodule.Quotient.mk_eq_zero _).mp hy
        obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
        refine ⟨Submodule.Quotient.mk c, ?_⟩
        apply Subtype.ext
        simp only [LinearMap.codRestrict_apply, f0, Submodule.liftQ_apply, LinearMap.smul_apply,
          Submodule.mkQ_apply]
        rw [← Submodule.Quotient.mk_smul, smul_eq_mul, mul_comm]
      have hker : Module.length O (LinearMap.ker g) ≤ Module.length O (O ⧸ Ideal.span {ℓ}) :=
        Module.length_le_of_surjective _ hf1
      rw [Module.length_eq_add_of_exact (LinearMap.ker g).subtype g
        (Submodule.injective_subtype _) hg (LinearMap.exact_subtype_ker_map g)]
      calc Module.length O (LinearMap.ker g) + Module.length O (O ⧸ Ideal.span {ℓ ^ n})
          ≤ Module.length O (O ⧸ Ideal.span {ℓ}) +
              (n : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ}) := add_le_add hker ih
        _ = ((n + 1 : ℕ) : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ}) := by
          push_cast
          ring

  obtain ⟨k, bF⟩ := Submodule.basisOfPid (Module.Free.chooseBasis O M) F
  have hk : k ≤ Module.finrank O M := by
    have h1 := Submodule.finrank_le F
    rw [Module.finrank_eq_card_basis bF, Fintype.card_fin] at h1
    exact h1
  set Q := P.comap F.subtype with hQ
  have hPF : ∀ y : F, ℓ ^ e • y ∈ Q := by
    intro y
    rw [hQ, Submodule.mem_comap, map_smul]
    exact h _ y.2

  let φ : Fin k → (O ⧸ Ideal.span {ℓ ^ e}) →ₗ[O] (↥F ⧸ Q) := fun i =>
    (Ideal.span {ℓ ^ e}).liftQ (LinearMap.toSpanSingleton O (↥F ⧸ Q) (Q.mkQ (bF i))) (by
      intro a ha
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, ← map_smul, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero, mul_smul]
      exact Q.smul_mem c (hPF _))
  let ψ : (Fin k → O ⧸ Ideal.span {ℓ ^ e}) →ₗ[O] (↥F ⧸ Q) := ∑ i, (φ i).comp (LinearMap.proj i)
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    refine ⟨fun i => Submodule.Quotient.mk (bF.repr x i), ?_⟩
    have hx : (Submodule.Quotient.mk x : ↥F ⧸ Q) =
        ∑ i, bF.repr x i • Submodule.Quotient.mk (bF i) := by
      conv_lhs => rw [← bF.sum_repr x]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← Submodule.mkQ_apply, map_sum]
      simp only [map_smul, Submodule.mkQ_apply]
    rw [hx]
    simp only [ψ, φ, LinearMap.sum_apply, LinearMap.comp_apply,
      LinearMap.proj_apply, Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply,
      Submodule.mkQ_apply]
  have hB : Module.length O (↥F ⧸ Q) ≤ (k : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ ^ e}) := by
    calc Module.length O (↥F ⧸ Q) ≤ Module.length O (Fin k → O ⧸ Ideal.span {ℓ ^ e}) :=
          Module.length_le_of_surjective ψ hψ
      _ = (k : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ ^ e}) := by
          rw [Module.length_pi_of_fintype]
          simp
  calc Module.length O (↥F ⧸ Q)
      ≤ (k : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ ^ e}) := hB
    _ ≤ (k : ℕ∞) * ((e : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ})) := by
        gcongr
        exact hA e
    _ ≤ ((Module.finrank O M * e : ℕ) : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ}) := by
        push_cast
        rw [mul_assoc]
        gcongr

end Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains
end
end

section -- merged from Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.ColAssembly
noncomputable section

namespace Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains

namespace ColAsm

open Formalism.WachCohomologyFacts.PLenBound

variable {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M]

theorem len_two_step (A B P : Submodule O M) (hBA : B ≤ A) :
    Module.length O (↥A ⧸ P.comap A.subtype) =
      Module.length O (↥A ⧸ (B ⊔ P).comap A.subtype) + Module.length O (↥B ⧸ P.comap B.subtype) := by
  have hle : P.comap B.subtype ≤ (P.comap A.subtype).comap (Submodule.inclusion hBA) := by
    intro x hx
    simpa using hx
  let f := Submodule.mapQ (P.comap B.subtype) (P.comap A.subtype) (Submodule.inclusion hBA) hle
  have hPB : P.comap A.subtype ≤ (B ⊔ P).comap A.subtype := Submodule.comap_mono le_sup_right
  let g := Submodule.factor hPB
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [LinearMap.mem_ker] at hx
    simp only [f, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
      Submodule.subtype_apply, Submodule.coe_inclusion] at hx
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply]
    exact hx
  have hg : Function.Surjective g := Submodule.factor_surjective hPB
  have hex : Function.Exact f g := by
    intro y
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    constructor
    · intro ha
      have h0 : (Submodule.Quotient.mk a : ↥A ⧸ (B ⊔ P).comap A.subtype) = 0 := ha
      rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply] at h0
      obtain ⟨b, hb, p, hp, hbp⟩ := Submodule.mem_sup.1 h0
      refine ⟨Submodule.Quotient.mk ⟨b, hb⟩, ?_⟩
      simp only [f, Submodule.mapQ_apply]
      rw [Submodule.Quotient.eq]
      simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub, Submodule.coe_inclusion]
      rw [← hbp]
      simpa using P.neg_mem hp
    · rintro ⟨x, hx⟩
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [← hx]
      show (Submodule.Quotient.mk (Submodule.inclusion hBA x) : ↥A ⧸ (B ⊔ P).comap A.subtype) = 0
      rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_inclusion]
      exact Submodule.mem_sup_left x.2
  rw [Module.length_eq_add_of_exact f g hf hg hex, add_comm]

theorem len_chain (P : Submodule O M) (k : ℕ) (F : ℕ → Submodule O M) (hF0 : F 0 = ⊤)
    (hF : ∀ i < k, F (i + 1) ≤ F i) :
    Module.length O (M ⧸ P) ≤
      (∑ i ∈ Finset.range k, Module.length O (↥(F i) ⧸ (F (i + 1) ⊔ P).comap (F i).subtype)) +
        Module.length O (↥(F k) ⧸ P.comap (F k).subtype) := by
  induction k with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, zero_add]
    have e : (P.comap (F 0).subtype).map
        (((LinearEquiv.ofEq _ _ hF0).trans Submodule.topEquiv : ↥(F 0) ≃ₗ[O] M) : ↥(F 0) →ₗ[O] M) = P := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
      · intro hx
        exact ⟨⟨x, by rw [hF0]; trivial⟩, by simpa using hx, rfl⟩
    exact le_of_eq ((Submodule.Quotient.equiv _ P _ e).length_eq).symm
  | succ k ih =>
    have ih' := ih (fun i hi => hF i (by omega))
    rw [len_two_step (F k) (F (k + 1)) P (hF k (by omega))] at ih'
    rw [Finset.sum_range_succ, add_assoc]
    exact ih'

theorem len_bound (a : O) (g e : ℕ) (Z Bc I : Submodule O M) (s : Finset M)
    (hcard : s.card ≤ g) (hZ : Submodule.span O (s : Set M) ⊔ Bc = Z) (hBc : Bc ≤ I)
    (hI : ∀ p ∈ Z, a ^ e • p ∈ I) :
    Module.length O (↥Z ⧸ I.comap Z.subtype) ≤
      (g : ℕ∞) * (e : ℕ∞) * Module.length O (O ⧸ Ideal.span {a}) := by
  classical
  have hsZ : ∀ x ∈ s, x ∈ Z := fun x hx => hZ ▸ Submodule.mem_sup_left (Submodule.subset_span hx)
  let v : s → (↥Z ⧸ I.comap Z.subtype) := fun x => Submodule.Quotient.mk ⟨x.1, hsZ x.1 x.2⟩
  have hkill : ∀ i, (a ^ e) • v i = 0 := by
    intro i
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    exact hI i.1 (hsZ i.1 i.2)
  have hspan : Submodule.span O (Set.range v) = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.mkQ_surjective _ x
    let T : Submodule O M :=
      ((Submodule.span O (Set.range v)).comap (I.comap Z.subtype).mkQ).map Z.subtype
    have hT : Z ≤ T := by
      rw [← hZ]
      refine sup_le ?_ ?_
      · rw [Submodule.span_le]
        intro y hy
        exact ⟨⟨y, hsZ y hy⟩, Submodule.subset_span ⟨⟨y, hy⟩, rfl⟩, rfl⟩
      · intro b hb
        have hbZ : b ∈ Z := hZ ▸ Submodule.mem_sup_right hb
        refine ⟨⟨b, hbZ⟩, ?_, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_comap, Submodule.mkQ_apply,
          (Submodule.Quotient.mk_eq_zero _).mpr (by simpa using hBc hb)]
        exact Submodule.zero_mem _
    obtain ⟨z', hz', hzz⟩ := hT hz
    have hz'' : z' = ⟨z, hz⟩ := Subtype.ext hzz
    subst hz''
    exact hz'
  have h1 := length_le_of_span v (a ^ e) hspan hkill
  have h2 := length_quot_pow_le a e
  rw [Fintype.card_coe] at h1
  calc _ ≤ _ := h1
    _ ≤ (s.card : ℕ∞) * ((e : ℕ∞) * Module.length O (O ⧸ Ideal.span {a})) := by gcongr
    _ ≤ (g : ℕ∞) * ((e : ℕ∞) * Module.length O (O ⧸ Ideal.span {a})) := by
        gcongr
    _ = _ := (mul_assoc _ _ _).symm

theorem sub_gen [IsDomain O] [IsPrincipalIdealRing O] [Module.Free O M] [Module.Finite O M]
    (a : O) (e : ℕ) (F P : Submodule O M) (hF : ∀ x ∈ F, a ^ e • x ∈ P) :
    Module.length O (↥F ⧸ P.comap F.subtype) ≤
      ((Module.finrank O M * e : ℕ) : ℕ∞) * Module.length O (O ⧸ Ideal.span {a}) := by
  classical
  obtain ⟨n, bF⟩ := Submodule.basisOfPid (Module.Free.chooseBasis O M) F
  let s : Finset M := Finset.univ.image (fun i => (bF i : M))
  have hcard : s.card ≤ Module.finrank O M := by
    calc s.card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_image_le
      _ = n := by simp
      _ = Module.finrank O F := (Module.finrank_eq_card_basis bF).trans (by simp) |>.symm
      _ ≤ Module.finrank O M := Submodule.finrank_le F
  have hspan : Submodule.span O (s : Set M) ⊔ ⊥ = F := by
    rw [sup_bot_eq]
    have hs : (s : Set M) = F.subtype '' Set.range bF := by
      ext x; simp [s]
    rw [hs, Submodule.span_image, bF.span_eq, Submodule.map_top, Submodule.range_subtype]
  have h := len_bound a (Module.finrank O M) e F ⊥ P s hcard hspan bot_le hF
  calc _ ≤ _ := h
    _ = _ := by push_cast; ring

end ColAsm

open ColAsm in
theorem column_assembly_bound : ColAssembly := by
  intro O _ _ _ M _ _ _ _ ℓ P k F gen m e e' L hF0 hF hgen hG hN hk
  have hchain := len_chain P k F hF0 hF
  have hlast := sub_gen ℓ e (F k) P hk
  have hterm : ∀ i ∈ Finset.range k, Module.length O (↥(F i) ⧸ (F (i + 1) ⊔ P).comap (F i).subtype) ≤
      (if i ∈ gen then ((m * e' : ℕ) : ℕ∞) else (L : ℕ∞)) * Module.length O (O ⧸ Ideal.span {ℓ}) := by
    intro i hi
    rw [Finset.mem_range] at hi
    split_ifs with hig
    · obtain ⟨⟨s, hs, hsF, hFs⟩, hl⟩ := hG i hig
      have hZ : Submodule.span O (s : Set M) ⊔ F (i + 1) = F i :=
        le_antisymm (sup_le (Submodule.span_le.2 hsF) (hF i hi)) hFs
      have h1 := len_bound ℓ m e' (F i) (F (i + 1)) (F (i + 1) ⊔ P) s hs hZ le_sup_left hl
      calc _ ≤ (m : ℕ∞) * (e' : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ}) := h1
        _ = ((m * e' : ℕ) : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ}) := by push_cast; ring
    · exact hN i hi hig
  have hcount : ∑ i ∈ Finset.range k, (if i ∈ gen then ((m * e' : ℕ) : ℕ∞) else (L : ℕ∞)) =
      ((gen.card * m * e' + (k - gen.card) * L : ℕ) : ℕ∞) := by
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, Finset.filter_mem_eq_inter,
      Finset.inter_eq_right.2 hgen]
    have hsd : (Finset.range k).filter (fun i => i ∉ gen) = Finset.range k \ gen := by
      ext x
      simp [Finset.mem_sdiff]
    rw [hsd, Finset.card_sdiff, Finset.inter_eq_left.2 hgen, Finset.card_range, nsmul_eq_mul, nsmul_eq_mul]
    push_cast
    ring
  have hsum : ∑ i ∈ Finset.range k, Module.length O (↥(F i) ⧸ (F (i + 1) ⊔ P).comap (F i).subtype) ≤
      ((gen.card * m * e' + (k - gen.card) * L : ℕ) : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ}) := by
    calc _ ≤ ∑ i ∈ Finset.range k, (if i ∈ gen then ((m * e' : ℕ) : ℕ∞) else (L : ℕ∞)) *
          Module.length O (O ⧸ Ideal.span {ℓ}) := Finset.sum_le_sum hterm
      _ = _ := by rw [← Finset.sum_mul, hcount]
  calc Module.length O (M ⧸ P) ≤ _ := hchain
    _ ≤ ((gen.card * m * e' + (k - gen.card) * L : ℕ) : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ}) +
        ((Module.finrank O M * e : ℕ) : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ}) := add_le_add hsum hlast
    _ = _ := by push_cast; ring

end Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains
end
end
