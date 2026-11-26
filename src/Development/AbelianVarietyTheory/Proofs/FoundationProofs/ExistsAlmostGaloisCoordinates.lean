module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicCoboundaryOfDivisible

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ZetaSubOneMemSpanGaloisDifferences
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OneSubPrimeDivZetaSubOneMulIsUnitStatement
open GlobalTheory.K5 GlobalTheory.KumDlog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_sub_prime_div_zeta_sub_one_mul_isUnit : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (j : ℕ), 1 ≤ j → ∀ y : Ω, IsInt (p := p) y →
  1 - (p : Ω) / (T.ζ j - 1) * y ≠ 0 ∧ IsInt (p := p) (1 - (p : Ω) / (T.ζ j - 1) * y)⁻¹ := by
  intro p hp hp2 Ω _ _ _ T j hj y hy
  classical
  set A := integralClosure (O0 p) Ω
  have hpj : 1 < p ^ j := Nat.one_lt_pow (by omega) hp.out.one_lt
  have hζ1 : T.ζ j ≠ 1 := (T.prim j).ne_one hpj
  have hτ0 : T.ζ j - 1 ≠ 0 := sub_ne_zero.2 hζ1
  have hζint : IsIntegral (O0 p) (T.ζ j) := by
    refine IsIntegral.of_pow (n := p ^ j) (by omega) ?_
    rw [(T.prim j).pow_eq_one]; exact isIntegral_one
  have htot : 2 ≤ Nat.totient (p ^ j) := by
    rw [Nat.totient_prime_pow hp.out (by omega)]
    have : 3 ≤ p := by have := hp.out.two_le; omega
    have h1 : 1 ≤ p ^ (j - 1) := Nat.one_le_pow _ _ hp.out.pos
    calc 2 = 1 * 2 := by ring
      _ ≤ p ^ (j - 1) * (p - 1) := Nat.mul_le_mul h1 (by omega)
  have hdiv : IsIntegral (O0 p) ((p : Ω) / (T.ζ j - 1) ^ 2) :=
    GlobalTheory.K5.PDiv.pdiv p Ω T j 2 hj htot
  have hw : IsIntegral (O0 p) ((p : Ω) / (T.ζ j - 1) ^ 2 * y) := hdiv.mul hy
  let ζ' : A := ⟨T.ζ j, hζint⟩
  let τ : A := ζ' - 1
  let w : A := ⟨_, hw⟩
  let u : A := 1 - τ * w
  have hu : (u : Ω) = 1 - (p : Ω) / (T.ζ j - 1) * y := by
    simp only [u, τ, w, ζ', Subalgebra.coe_sub, Subalgebra.coe_mul, Subalgebra.coe_one]
    field_simp
  obtain ⟨hdom, hdvr, hirr⟩ := completed_laurent_isDVR p
  have hmax : IsLocalRing.maximalIdeal (O0 p) = Ideal.span {(p : O0 p)} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hirr

  have hτM : ∀ M : Ideal A, M.IsMaximal → τ ∈ M := by
    intro M hM
    have hc : (M.comap (algebraMap (O0 p) A)).IsMaximal :=
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal M
    have hpM : (p : A) ∈ M := by
      have h1 : M.comap (algebraMap (O0 p) A) = IsLocalRing.maximalIdeal (O0 p) :=
        IsLocalRing.eq_maximalIdeal hc
      have h2 : (p : O0 p) ∈ M.comap (algebraMap (O0 p) A) := by
        rw [h1, hmax]; exact Ideal.mem_span_singleton_self _
      simpa using h2
    have : M.IsPrime := hM.isPrime
    have : Nontrivial (A ⧸ M) := Ideal.Quotient.nontrivial_iff.2 hM.ne_top
    have : CharP (A ⧸ M) p := by
      rw [CharP.charP_iff_prime_eq_zero hp.out]
      rw [← map_natCast (Ideal.Quotient.mk M), Ideal.Quotient.eq_zero_iff_mem]; exact hpM
    have hζp : ζ' ^ (p ^ j) = 1 := Subtype.ext (by simp [ζ', (T.prim j).pow_eq_one])
    have h3 : (Ideal.Quotient.mk M τ) ^ (p ^ j) = 0 := by
      let q := Ideal.Quotient.mk M
      change (q (ζ' - 1)) ^ (p ^ j) = 0
      rw [q.map_sub, q.map_one, sub_pow_char_pow (p := p) (q ζ') 1 j,
        ← q.map_pow, hζp, q.map_one, one_pow, sub_self]
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact pow_eq_zero_iff (by omega) |>.1 h3
  have hunit : IsUnit u := by
    by_contra h
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (Ideal.span {u})
      (by rwa [Ne, Ideal.span_singleton_eq_top])
    have h1 : u ∈ M := hle (Ideal.mem_span_singleton_self _)
    have h2 : τ * w ∈ M := M.mul_mem_right _ (hτM M hM)
    have : (1 : A) ∈ M := by
      have := M.add_mem h1 h2; simpa [u] using this
    exact hM.ne_top ((Ideal.eq_top_iff_one _).2 this)
  obtain ⟨v, hv⟩ := hunit
  have hval : (u : Ω) * (((v⁻¹ : Aˣ) : A) : Ω) = 1 := by
    rw [← hv, ← Subalgebra.coe_mul, Units.mul_inv, Subalgebra.coe_one]
  rw [← hu]
  refine ⟨left_ne_zero_of_mul_eq_one hval, ?_⟩
  rw [← eq_inv_of_mul_eq_one_right hval]
  exact ((v⁻¹ : Aˣ) : A).2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ZetaSubOneMemSpanGaloisDifferences
open GlobalTheory.K5 GlobalTheory.KumDlog

noncomputable section

namespace GlobalTheory.KumIdeal

theorem exists_mul_modEq_ppow {p : ℕ} (hp : p.Prime) {n a : ℕ} (hn : 1 ≤ n) (ha : ¬ p ^ n ∣ a) :
    ∃ k, k * a ≡ p ^ (n - 1) [MOD p ^ n] := by
  have hd : Nat.gcd a (p ^ n) ∣ p ^ n := Nat.gcd_dvd_right _ _
  obtain ⟨v, hv, hv'⟩ := (Nat.dvd_prime_pow hp).1 hd
  have hvn : v ≠ n := by
    intro h; apply ha; rw [← h, ← hv']; exact Nat.gcd_dvd_left _ _
  have hlt : Nat.gcd a (p ^ n) < p ^ n := by
    rw [hv']; exact Nat.pow_lt_pow_right hp.one_lt (lt_of_le_of_ne hv hvn)
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_gcd hlt
  refine ⟨m * p ^ (n - 1 - v), ?_⟩
  have e : p ^ (n - 1) = p ^ v * p ^ (n - 1 - v) := by rw [← pow_add]; congr 1; omega
  rw [e, ← hv', ← hm]
  calc m * p ^ (n - 1 - v) * a = (a * m) * p ^ (n - 1 - v) := by ring
    _ ≡ (a * m % p ^ n) * p ^ (n - 1 - v) [MOD p ^ n] := (Nat.mod_modEq _ _).symm.mul_right _

theorem zeta_sub_one_mem_span : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (n : ℕ) (r : Ω), IsInt (p := p) r → (∀ h ∈ Hinf T, ∃ i : ℕ, h r = T.ζ n ^ i * r) →
  ∀ j : ℕ, 1 ≤ j → ∀ g ∈ Hinf T, g r ≠ r →
  T.ζ j - 1 ∈ Submodule.span (FixI (Hfix T r)) {y : Ω | ∃ x ∈ FixI (Hfix T r), y = g x - x} := by
  intro p _ hp2 Ω _ _ hΩ T n r hr hK j hj g hg hgr
  classical
  have hp : p.Prime := Fact.out
  set C := FixI (Hfix T r) with hC
  set I := Submodule.span C {y : Ω | ∃ x ∈ C, y = g x - x} with hI
  have hr0 : r ≠ 0 := by rintro rfl; exact hgr (map_zero g)
  obtain ⟨y, E, hy, hE, huniq, hsum⟩ :=
    GlobalTheory.T.exists_integral_sum_conj_eq_zeta_sub_one p hp2 Ω hΩ T {r} (by simpa using hr) j hj
  have hE' : ∀ e ∈ E, e ∈ Hinf T := hE
  have huniq' : ∀ h ∈ Hinf T, ∃! e, e ∈ E ∧ h y = e y ∧ h r = e r := by
    intro h hh; simpa using huniq h hh
  have hex : ∀ k : Gal p Ω, ∃ e, k ∈ Hinf T → e ∈ E ∧ k y = e y ∧ k r = e r := by
    intro k
    by_cases hk : k ∈ Hinf T
    · obtain ⟨e, he, -⟩ := huniq' k hk; exact ⟨e, fun _ => he⟩
    · exact ⟨1, fun h => absurd h hk⟩
  choose rep hrep using hex
  have runiq : ∀ k ∈ Hinf T, ∀ e ∈ E, k y = e y → k r = e r → rep k = e := fun k hk e he h1 h2 =>
    (huniq' k hk).unique (hrep k hk) ⟨he, h1, h2⟩
  have hinv : ∀ h : Gal p Ω, ∀ x, h⁻¹ (h x) = x := fun h x => by
    rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  have hinv' : ∀ h : Gal p Ω, ∀ x, h (h⁻¹ x) = x := fun h x => by
    rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
  let Y : Ω → Ω := fun ρ => ∑ e ∈ E with e r = ρ, e y
  have hYgal : ∀ h ∈ Hinf T, ∀ ρ, h (Y ρ) = Y (h ρ) := by
    intro h hh ρ
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Y, map_sum]
    have hmem : ∀ k ∈ Hinf T, ∀ e ∈ E, k * e ∈ Hinf T := fun k hk e he => mul_mem hk (hE' e he)
    refine Finset.sum_nbij' (fun e => rep (h * e)) (fun e => rep (h⁻¹ * e)) ?_ ?_ ?_ ?_ ?_
    · intro e he
      simp only [Finset.mem_filter] at he ⊢
      obtain ⟨h1, -, h3⟩ := hrep _ (hmem h hh e he.1)
      exact ⟨h1, by rw [← h3, AlgEquiv.mul_apply, he.2]⟩
    · intro e he
      simp only [Finset.mem_filter] at he ⊢
      obtain ⟨h1, -, h3⟩ := hrep _ (hmem _ (inv_mem hh) e he.1)
      exact ⟨h1, by rw [← h3, AlgEquiv.mul_apply, he.2, hinv]⟩
    · intro e he
      simp only [Finset.mem_filter] at he
      obtain ⟨h1, h2, h3⟩ := hrep _ (hmem h hh e he.1)
      refine runiq _ (hmem _ (inv_mem hh) _ h1) e he.1 ?_ ?_
      · rw [AlgEquiv.mul_apply, ← h2, AlgEquiv.mul_apply, hinv]
      · rw [AlgEquiv.mul_apply, ← h3, AlgEquiv.mul_apply, hinv]
    · intro e he
      simp only [Finset.mem_filter] at he
      obtain ⟨h1, h2, h3⟩ := hrep _ (hmem _ (inv_mem hh) e he.1)
      refine runiq _ (hmem _ hh _ h1) e he.1 ?_ ?_
      · rw [AlgEquiv.mul_apply, ← h2, AlgEquiv.mul_apply, hinv']
      · rw [AlgEquiv.mul_apply, ← h3, AlgEquiv.mul_apply, hinv']
    · intro e he
      simp only [Finset.mem_filter] at he
      exact (hrep _ (hmem h hh e he.1)).2.1

  have hzn := T.prim n
  have hpos : 0 < p ^ n := pow_pos hp.pos n
  have hζr : ∀ i : ℕ, T.ζ n ^ i = T.ζ n ^ (i % p ^ n) := fun i => by
    conv_lhs => rw [← Nat.mod_add_div i (p ^ n), pow_add, pow_mul, hzn.pow_eq_one, one_pow, mul_one]
  let Z : ℕ → Ω := fun i => Y (T.ζ n ^ i * r)
  have hZC : ∀ i, Z i ∈ C := by
    intro i
    refine ⟨int_sum _ _ fun e _ => int_gal e hy, fun h hh => ?_⟩
    rw [mem_Hfix] at hh
    show h (Y _) = Y _
    rw [hYgal h hh.1, map_mul, map_pow, (mem_Hinf.1 hh.1 n).1, hh.2]
  have hZmod : ∀ i i', i ≡ i' [MOD p ^ n] → Z i = Z i' := by
    intro i i' h
    show Y _ = Y _
    rw [(GlobalTheory.K5.Basic.zeta_pow_eq_iff T n i i').2 h]
  obtain ⟨a, ha⟩ := hK g hg
  have hZg : ∀ i, g (Z i) = Z (i + a) := by
    intro i
    show g (Y _) = Y _
    rw [hYgal g hg, map_mul, map_pow, (mem_Hinf.1 hg n).1, ha, pow_add, mul_assoc]
  have hZa : ∀ i, Z (i + a) - Z i ∈ I := fun i => by
    rw [← hZg]; exact Submodule.subset_span ⟨Z i, hZC i, rfl⟩
  have iter : ∀ b, (∀ i, Z (i + b) - Z i ∈ I) → ∀ t i, Z (i + t * b) - Z i ∈ I := by
    intro b hb t
    induction t with
    | zero => intro i; simp
    | succ t ih =>
      intro i
      have e : i + (t + 1) * b = (i + t * b) + b := by ring
      rw [e]
      have := I.add_mem (hb (i + t * b)) (ih i)
      rwa [sub_add_sub_cancel] at this
  have hn : 1 ≤ n := by
    by_contra h0
    have hn0 : n = 0 := by omega
    apply hgr
    rw [ha, hζr, hn0, pow_zero, Nat.mod_one, pow_zero, one_mul]
  have hna : ¬ p ^ n ∣ a := by
    intro hd
    apply hgr
    rw [ha, hζr, Nat.eq_zero_of_dvd_of_lt ?_ (Nat.mod_lt a hpos), pow_zero, one_mul]
    exact (Nat.dvd_mod_iff dvd_rfl).2 hd
  obtain ⟨k, hk⟩ := exists_mul_modEq_ppow hp hn hna
  have hZd : ∀ i, Z (i + p ^ (n - 1)) - Z i ∈ I := by
    intro i
    rw [hZmod (i + p ^ (n - 1)) (i + k * a) (Nat.ModEq.add_left i hk.symm)]
    exact iter a hZa k i
  set d := p ^ (n - 1) with hd
  set W := ∑ i ∈ Finset.range d, Z i with hW
  have hWC : W ∈ C := Subalgebra.sum_mem _ fun i _ => hZC i
  have hsumW : ∀ t : ℕ, ∑ i ∈ Finset.range (t * d), Z i - (t : Ω) * W ∈ I := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have e : (t + 1) * d = t * d + d := by ring
      rw [e, Finset.sum_range_add]
      have h2 : ∑ x ∈ Finset.range d, Z (t * d + x) - W ∈ I := by
        rw [hW, ← Finset.sum_sub_distrib]
        refine Submodule.sum_mem _ fun x _ => ?_
        rw [add_comm]; exact iter d hZd t x
      have := I.add_mem ih h2
      convert this using 1
      push_cast; ring
  have hNd : p * d = p ^ n := by
    rw [hd, ← pow_succ']; congr 1; omega
  have hsumZ : ∑ i ∈ Finset.range (p ^ n), Z i = T.ζ j - 1 := by
    rw [← hsum]
    have hinj : Set.InjOn (fun i => T.ζ n ^ i * r) (Finset.range (p ^ n) : Set ℕ) := by
      intro i hi i' hi' h
      simp only [Finset.coe_range, Set.mem_Iio] at hi hi'
      exact hzn.pow_inj hi hi' (mul_right_cancel₀ hr0 h)
    rw [← Finset.sum_fiberwise_of_maps_to (t := (Finset.range (p ^ n)).image (fun i => T.ζ n ^ i * r))
      (g := fun e : Gal p Ω => e r)]
    · rw [Finset.sum_image hinj]
    · intro e he
      obtain ⟨i, hi⟩ := hK e (hE' e he)
      rw [Finset.mem_image]
      exact ⟨i % p ^ n, Finset.mem_range.2 (Nat.mod_lt _ hpos), by rw [← hζr, hi]⟩
  have hτI : T.ζ j - 1 - (p : Ω) * W ∈ I := by
    have := hsumW p
    rwa [hNd, hsumZ] at this
  have hτ0 : T.ζ j - 1 ≠ 0 :=
    sub_ne_zero.2 ((T.prim j).ne_one (Nat.one_lt_pow (by omega) hp.one_lt))
  obtain ⟨hu0, huint⟩ := GlobalTheory.T.one_sub_prime_div_zeta_sub_one_mul_isUnit p hp2 Ω hΩ T j hj W hWC.1
  have huC : (1 - (p : Ω) / (T.ζ j - 1) * W)⁻¹ ∈ C := by
    refine ⟨huint, fun h hh => ?_⟩
    rw [mem_Hfix] at hh
    rw [map_inv₀, map_sub, map_one, map_mul, map_div₀, map_sub, map_one, map_natCast,
      (mem_Hinf.1 hh.1 j).1, hWC.2 h (by rw [mem_Hfix]; exact hh)]
  have := I.smul_mem (⟨_, huC⟩ : C) hτI
  rw [Subalgebra.smul_def, smul_eq_mul] at this
  have key : T.ζ j - 1 - (p : Ω) * W = (1 - (p : Ω) / (T.ζ j - 1) * W) * (T.ζ j - 1) := by
    have e2 : (p : Ω) / (T.ζ j - 1) * W * (T.ζ j - 1) = (p : Ω) * W := by
      rw [div_mul_eq_mul_div, div_mul_cancel₀ _ hτ0]
    rw [sub_mul, one_mul, e2]
  rw [key, ← mul_assoc, inv_mul_cancel₀ hu0, one_mul] at this
  exact this

end GlobalTheory.KumIdeal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ZetaSubOneMemSpanGaloisDifferencesStatement
open GlobalTheory.K5 GlobalTheory.KumDlog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zeta_sub_one_mem_span_galois_differences : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (n : ℕ) (r : Ω), IsInt (p := p) r → (∀ h ∈ Hinf T, ∃ i : ℕ, h r = T.ζ n ^ i * r) →
  ∀ j : ℕ, 1 ≤ j → ∀ g ∈ Hinf T, g r ≠ r →
  T.ζ j - 1 ∈ Submodule.span (FixI (Hfix T r)) {y : Ω | ∃ x ∈ FixI (Hfix T r), y = g x - x} := by
  first | exact @GlobalTheory.KumIdeal.zeta_sub_one_mem_span | exact GlobalTheory.KumIdeal.zeta_sub_one_mem_span | (intros; apply GlobalTheory.KumIdeal.zeta_sub_one_mem_span <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAlmostGaloisCoordinates
open GlobalTheory.K5 GlobalTheory.KumDlog

noncomputable section

namespace GlobalTheory.KumDlog.AlmostGal

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

def Rep (C : Subalgebra (O0 p) Ω) (H : Subgroup (Gal p Ω)) (F : Gal p Ω → Ω) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (u v : ι → Ω), (∀ k, u k ∈ C) ∧ (∀ k, v k ∈ C) ∧
    ∀ h ∈ H, F h = ∑ k, u k * h (v k)

variable {C : Subalgebra (O0 p) Ω} {H : Subgroup (Gal p Ω)}

theorem rep_congr {F G : Gal p Ω → Ω} (hF : Rep C H F) (e : ∀ h ∈ H, G h = F h) : Rep C H G := by
  obtain ⟨ι, hι, u, v, hu, hv, hF⟩ := hF
  exact ⟨ι, hι, u, v, hu, hv, fun h hh => (e h hh).trans (hF h hh)⟩

theorem rep_const {c : Ω} (hc : c ∈ C) : Rep C H (fun _ => c) :=
  ⟨Unit, inferInstance, fun _ => c, fun _ => 1, fun _ => hc, fun _ => C.one_mem,
    fun h _ => by simp⟩

theorem rep_eval {x : Ω} (hx : x ∈ C) : Rep C H (fun h => h x) :=
  ⟨Unit, inferInstance, fun _ => 1, fun _ => x, fun _ => C.one_mem, fun _ => hx,
    fun h _ => by simp⟩

theorem rep_add {F G : Gal p Ω → Ω} (hF : Rep C H F) (hG : Rep C H G) :
    Rep C H (fun h => F h + G h) := by
  obtain ⟨ι, _, u, v, hu, hv, hF⟩ := hF
  obtain ⟨ι', _, u', v', hu', hv', hG⟩ := hG
  refine ⟨ι ⊕ ι', inferInstance, Sum.elim u u', Sum.elim v v', ?_, ?_, fun h hh => ?_⟩
  · rintro (k | k)
    · exact hu k
    · exact hu' k
  · rintro (k | k)
    · exact hv k
    · exact hv' k
  · show F h + G h = _
    rw [Fintype.sum_sum_type, hF h hh, hG h hh]
    simp

theorem rep_mul {F G : Gal p Ω → Ω} (hF : Rep C H F) (hG : Rep C H G) :
    Rep C H (fun h => F h * G h) := by
  obtain ⟨ι, _, u, v, hu, hv, hF⟩ := hF
  obtain ⟨ι', _, u', v', hu', hv', hG⟩ := hG
  refine ⟨ι × ι', inferInstance, fun k => u k.1 * u' k.2, fun k => v k.1 * v' k.2,
    fun k => C.mul_mem (hu _) (hu' _), fun k => C.mul_mem (hv _) (hv' _), fun h hh => ?_⟩
  show F h * G h = ∑ k : ι × ι', u k.1 * u' k.2 * h (v k.1 * v' k.2)
  rw [hF h hh, hG h hh, Finset.sum_mul_sum, ← Finset.univ_product_univ, Finset.sum_product]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul]; ring

theorem rep_prod {α : Type*} (s : Finset α) (F : α → Gal p Ω → Ω)
    (hF : ∀ a ∈ s, Rep C H (F a)) : Rep C H (fun h => ∏ a ∈ s, F a h) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (rep_const (H := H) C.one_mem)
  | insert a s ha ih =>
    refine rep_congr (rep_mul (hF a (by simp)) (ih fun b hb => hF b (by simp [hb])))
      fun h _ => ?_
    rw [Finset.prod_insert ha]

theorem gal_mem_C {T : Tower p Ω} {n : ℕ} {r : Ω}
    (hH : ∀ h ∈ Hinf T, ∃ i : ℕ, h r = T.ζ n ^ i * r) {g : Gal p Ω} (hg : g ∈ Hinf T)
    {x : Ω} (hx : x ∈ FixI (Hfix T r)) : g x ∈ FixI (Hfix T r) := by
  refine ⟨int_gal g hx.1, fun h hh => ?_⟩
  obtain ⟨hhinf, hhr⟩ := mem_Hfix.1 hh
  have hgr : h (g r) = g r := by
    obtain ⟨i, hi⟩ := hH g hg
    rw [hi, map_mul, map_pow, (mem_Hinf.1 hhinf n).1, hhr]
  have hk : g⁻¹ * h * g ∈ Hfix T r := by
    refine mem_Hfix.2 ⟨(Hinf T).mul_mem ((Hinf T).mul_mem ((Hinf T).inv_mem hg) hhinf) hg, ?_⟩
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hgr, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
  have e := hx.2 _ hk
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq] at e
  exact e

theorem eq_on_C {T : Tower p Ω} {r : Ω} {g h : Gal p Ω} (hg : g ∈ Hinf T) (hh : h ∈ Hinf T)
    (hr : h r = g r) {x : Ω} (hx : x ∈ FixI (Hfix T r)) : h x = g x := by
  have hk : g⁻¹ * h ∈ Hfix T r := by
    refine mem_Hfix.2 ⟨(Hinf T).mul_mem ((Hinf T).inv_mem hg) hh, ?_⟩
    rw [AlgEquiv.mul_apply, hr, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
  have e := hx.2 _ hk
  rw [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq] at e
  exact e

theorem rep_of_span {T : Tower p Ω} {n : ℕ} {r : Ω}
    (hH : ∀ h ∈ Hinf T, ∃ i : ℕ, h r = T.ζ n ^ i * r) {g : Gal p Ω} (hg : g ∈ Hinf T) {y : Ω}
    (hy : y ∈ Submodule.span (FixI (Hfix T r)) {y : Ω | ∃ x ∈ FixI (Hfix T r), y = g x - x}) :
    ∃ F : Gal p Ω → Ω, Rep (FixI (Hfix T r)) (Hinf T) F ∧ F 1 = y ∧
      ∀ h ∈ Hinf T, h r = g r → F h = 0 := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    refine ⟨fun h => g x + (-1) * h x, rep_add (rep_const (gal_mem_C hH hg hx))
      (rep_mul (rep_const (neg_mem (Subalgebra.one_mem _))) (rep_eval hx)), ?_, ?_⟩
    · simp only [AlgEquiv.one_apply]; ring
    · intro h hh hr
      simp only [eq_on_C hg hh hr hx]; ring
  | zero => exact ⟨fun _ => 0, rep_const (Subalgebra.zero_mem _), rfl, fun _ _ _ => rfl⟩
  | add y z _ _ ihy ihz =>
    obtain ⟨F, hF, hF1, hF0⟩ := ihy
    obtain ⟨G, hG, hG1, hG0⟩ := ihz
    exact ⟨fun h => F h + G h, rep_add hF hG, by simp [hF1, hG1],
      fun h hh hr => by simp [hF0 h hh hr, hG0 h hh hr]⟩
  | smul a y _ ih =>
    obtain ⟨F, hF, hF1, hF0⟩ := ih
    exact ⟨fun h => (a : Ω) * F h, rep_mul (rep_const a.2) hF,
      by simp [hF1, Subalgebra.smul_def], fun h hh hr => by simp [hF0 h hh hr]⟩

end GlobalTheory.KumDlog.AlmostGal


open GlobalTheory.KumDlog.AlmostGal in
theorem GlobalTheory.KumDlog.almostGal_coord : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω]
    [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (n : ℕ) (r : Ω), IsInt (p := p) r →
    (∀ h ∈ Hinf T, ∃ i : ℕ, h r = T.ζ n ^ i * r) →
  ∃ (ι : Type) (_ : Fintype ι) (u v : ι → Ω), (∀ k, u k ∈ FixI (Hfix T r)) ∧
    (∀ k, v k ∈ FixI (Hfix T r)) ∧
  ∑ k, u k * v k = (p : Ω) ∧ ∀ h ∈ Hinf T, h r ≠ r → ∑ k, u k * h (v k) = 0 := by
  intro p _ hp2 Ω _ _ hclo T n r hr hH
  classical
  have hp : p.Prime := Fact.out
  set τ : Ω := T.ζ (n + 1) - 1 with hτ
  have hτ0 : τ ≠ 0 :=
    sub_ne_zero.2 ((T.prim (n + 1)).ne_one (Nat.one_lt_pow (by omega) hp.one_lt))

  set W : Finset Ω := ((Finset.range (p ^ n)).image (fun i => T.ζ n ^ i * r)).filter
    (fun w => w ≠ r ∧ ∃ g ∈ Hinf T, g r = w) with hW
  have hF : ∀ w ∈ W, ∃ F : Gal p Ω → Ω, Rep (FixI (Hfix T r)) (Hinf T) F ∧ F 1 = τ ∧
      ∀ h ∈ Hinf T, h r = w → F h = 0 := by
    intro w hw
    obtain ⟨hwr, g, hg, hgw⟩ := (Finset.mem_filter.1 hw).2
    obtain ⟨F, hF, hF1, hF0⟩ := rep_of_span hH hg
      (GlobalTheory.T.zeta_sub_one_mem_span_galois_differences p hp2 Ω hclo T n r hr hH (n + 1) (by omega) g hg (hgw ▸ hwr))
    exact ⟨F, hF, hF1, fun h hh e => hF0 h hh (e.trans hgw.symm)⟩
  choose! F hFr hF1 hF0 using hF
  set s := W.card with hs
  have hsle : s ≤ Nat.totient (p ^ (n + 1)) := by
    rw [Nat.totient_prime_pow hp (by omega), Nat.add_sub_cancel]
    calc s ≤ ((Finset.range (p ^ n)).image (fun i => T.ζ n ^ i * r)).card :=
          Finset.card_filter_le _ _
      _ ≤ (Finset.range (p ^ n)).card := Finset.card_image_le
      _ = p ^ n := Finset.card_range _
      _ ≤ p ^ n * (p - 1) := Nat.le_mul_of_pos_right _ (by have := hp.two_le; omega)
  set c : Ω := (p : Ω) / τ ^ s with hc
  have hcC : c ∈ FixI (Hfix T r) := by
    refine ⟨GlobalTheory.T.isInt_prime_div_rootOfUnity_sub_one_pow p Ω T (n + 1) s (by omega) hsle, fun g hg => ?_⟩
    have hz : g (T.ζ (n + 1)) = T.ζ (n + 1) := (mem_Hinf.1 (mem_Hfix.1 hg).1 (n + 1)).1
    rw [hc, map_div₀, map_pow, hτ, map_sub, map_one, hz, map_natCast]
  have hrep : Rep (FixI (Hfix T r)) (Hinf T) (fun h => c * ∏ w ∈ W, F w h) :=
    rep_mul (rep_const hcC) (rep_prod W F hFr)
  obtain ⟨ι, hι, u, v, hu, hv, he⟩ := hrep
  refine ⟨ι, hι, u, v, hu, hv, ?_, fun h hh hhr => ?_⟩
  · have e := he 1 (Hinf T).one_mem
    simp only [AlgEquiv.one_apply] at e
    rw [← e, Finset.prod_congr rfl hF1, Finset.prod_const, ← hs, hc,
      div_mul_cancel₀ _ (pow_ne_zero _ hτ0)]
  · rw [← he h hh]
    obtain ⟨i, hi⟩ := hH h hh
    have hmod : h r = T.ζ n ^ (i % p ^ n) * r := by
      rw [hi]
      conv_lhs => rw [← Nat.div_add_mod i (p ^ n), pow_add, pow_mul, (T.prim n).pow_eq_one,
        one_pow, one_mul]
    have hmem : h r ∈ W := by
      refine Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨i % p ^ n, Finset.mem_range.2
        (Nat.mod_lt _ (ppow_pos n)), hmod.symm⟩, hhr, h, hh, rfl⟩
    show c * ∏ w ∈ W, F w h = 0
    rw [Finset.prod_eq_zero hmem (hF0 _ hmem h hh rfl), mul_zero]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAlmostGaloisCoordinatesStatement
open GlobalTheory.K5 GlobalTheory.KumDlog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_almostGalois_coordinates : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (n : ℕ) (r : Ω), IsInt (p := p) r → (∀ h ∈ Hinf T, ∃ i : ℕ, h r = T.ζ n ^ i * r) →
  ∃ (ι : Type) (_ : Fintype ι) (u v : ι → Ω), (∀ k, u k ∈ FixI (Hfix T r)) ∧ (∀ k, v k ∈ FixI (Hfix T r)) ∧
  ∑ k, u k * v k = (p : Ω) ∧ ∀ h ∈ Hinf T, h r ≠ r → ∑ k, u k * h (v k) = 0 := by
  first | exact @GlobalTheory.KumDlog.almostGal_coord | exact GlobalTheory.KumDlog.almostGal_coord | (intros; apply GlobalTheory.KumDlog.almostGal_coord <;> assumption)
end
