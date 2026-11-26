module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLimHom
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdempotentsUniqueForEpsilonRoot
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdempotentsUniqueForEpsilonRoot
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.ContUniv

theorem coi_eq_of_mul_eq_zero {R I : Type} [CommRing R] [Fintype I] {e e' : I → R}
    (h : CompleteOrthogonalIdempotents e) (h' : CompleteOrthogonalIdempotents e')
    (hz : ∀ c c', c ≠ c' → e c * e' c' = 0) : e = e' := by
  classical
  funext c
  have h1 : e c = e c * e' c := by
    calc e c = e c * ∑ b, e' b := by rw [h'.complete, mul_one]
      _ = e c * e' c := by
        rw [Finset.mul_sum]
        exact Finset.sum_eq_single c (fun b _ hb => hz c b hb.symm) (by simp)
  have h2 : e' c = e c * e' c := by
    calc e' c = (∑ b, e b) * e' c := by rw [h.complete, one_mul]
      _ = e c * e' c := by
        rw [Finset.sum_mul]
        exact Finset.sum_eq_single c (fun b _ hb => hz b c hb) (by simp)
  rw [h1, ← h2]

theorem one_sub_pow_dvd {O : Type} [CommRing O] [IsDomain O] {ζ : O} {n d : ℕ}
    (hζ : IsPrimitiveRoot ζ n) (hd : 0 < d) (hdn : d < n) : 1 - ζ ^ d ∣ (n : O) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have h := hζ.prod_one_sub_pow_eq_order
  obtain ⟨j, rfl⟩ : ∃ j, d = j + 1 := ⟨d - 1, by omega⟩
  have hd' : (1 - ζ ^ (j + 1)) ∣ ∏ i ∈ Finset.range k, (1 - ζ ^ (i + 1)) :=
    Finset.dvd_prod_of_mem (fun i => 1 - ζ ^ (i + 1)) (Finset.mem_range.2 (by omega))
  rw [h] at hd'
  simpa using hd'

theorem pow_sub_pow_dvd {O : Type} [CommRing O] [IsDomain O] {ζ : O} {n a b : ℕ}
    (hζ : IsPrimitiveRoot ζ n) (ha : a < n) (hb : b < n) (hab : a ≠ b) :
    ζ ^ a - ζ ^ b ∣ (n : O) := by
  have hu : ∀ i : ℕ, IsUnit (ζ ^ i) := fun i =>
    (hζ.isUnit (by omega)).pow i
  have key : ∀ {a b : ℕ}, a < b → b < n → ζ ^ a - ζ ^ b ∣ (n : O) := by
    intro a b h1 h2
    have e : ζ ^ a - ζ ^ b = ζ ^ a * (1 - ζ ^ (b - a)) := by
      rw [mul_sub, mul_one, ← pow_add]
      congr 2
      omega
    rw [e]
    exact (hu a).mul_left_dvd.2 (one_sub_pow_dvd hζ (by omega) (by omega))
  rcases lt_or_gt_of_ne hab with h | h
  · exact key h hb
  · rw [← neg_sub, neg_dvd]
    exact key h ha

theorem mul_eq_zero_of_pow {O U : Type} [CommRing O] [IsDomain O] [CommRing U] (g : O →+* U)
    {ζ : O} {n a b : ℕ} (hζ : IsPrimitiveRoot ζ n) (ha : a < n) (hb : b < n) (hab : a ≠ b)
    (hn : (n : U) ∈ nonZeroDivisors U) {x S S' : U}
    (h : S * (x - g ζ ^ a) = 0) (h' : S' * (x - g ζ ^ b) = 0) : S * S' = 0 := by
  obtain ⟨w, hw⟩ := pow_sub_pow_dvd hζ ha hb hab
  have e : (n : U) = (g ζ ^ a - g ζ ^ b) * g w := by
    rw [← map_natCast g, hw, map_mul, map_sub, map_pow, map_pow]
  have h0 : S * S' * (g ζ ^ a - g ζ ^ b) = 0 := by
    linear_combination S * h' * 1 - S' * h
  have h1 : (S * S') * (n : U) = 0 := by
    rw [e, ← mul_assoc, h0, zero_mul]
  exact (mem_nonZeroDivisors_iff_right.1 hn) _ h1

variable {l : ℕ} [Fact l.Prime]

theorem sharp_s_eq (t : PAlg l) (x : Ob l) :
    t.sharp (t.s x) = t.oC (theta0 l (WittVector.teichmuller l x)) := by
  rw [oC_theta0, sW, WittVector.map_teichmuller]
  rfl

theorem eq_zero_of_sharp (t : PAlg l) {e : t.A} (he : IsIdempotentElem e) (h : t.sharp e = 0) :
    e = 0 :=
  (RL.idem_au t 0 IsIdempotentElem.zero).unique ⟨he, h⟩ ⟨IsIdempotentElem.zero, sharp_zero t⟩

theorem idem_unique : ∀ {l : ℕ} [Fact l.Prime] (ε : Eps l) (t : PAlg l) (m : ℕ) (x : t.U)
    (e e' : ZMod (l ^ m) → t.A),
    CompleteOrthogonalIdempotents e → CompleteOrthogonalIdempotents e' →
    (∀ c, t.sharp (e c) * (x - t.sharp (t.s (ε.e m)) ^ c.val) = 0) →
    (∀ c, t.sharp (e' c) * (x - t.sharp (t.s (ε.e m)) ^ c.val) = 0) → e = e' := by
  intro l _ ε t m x e e' he he' h h'
  have hζ := (GlobalTheory.T.epsilon_cyclotomic_element_properties ε).2.2.2.2 m
  refine coi_eq_of_mul_eq_zero he he' fun c c' hc => ?_
  have hn : ((l ^ m : ℕ) : t.U) ∈ nonZeroDivisors t.U := by
    rw [Nat.cast_pow]
    exact pow_mem t.l_mem_nzd_U m
  have h1 := h c
  have h2 := h' c'
  rw [sharp_s_eq] at h1 h2
  have h3 := mul_eq_zero_of_pow t.oC hζ (ZMod.val_lt c) (ZMod.val_lt c')
    (fun hv => hc (ZMod.val_injective _ hv)) hn h1 h2
  refine eq_zero_of_sharp t ((he.idem c).mul (he'.idem c')) ?_
  rw [map_mul, h3]

end GlobalTheory.CompanionTheory.ContUniv
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdempotentsUniqueForEpsilonRootStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotents_unique_for_epsilon_root : ∀ {l : ℕ} [Fact l.Prime] (ε : Eps l) (t : PAlg l) (m : ℕ) (x : t.U) (e e' : ZMod (l ^ m) → t.A),
  CompleteOrthogonalIdempotents e → CompleteOrthogonalIdempotents e' →
  (∀ c, t.sharp (e c) * (x - t.sharp (t.s (ε.e m)) ^ c.val) = 0) →
  (∀ c, t.sharp (e' c) * (x - t.sharp (t.s (ε.e m)) ^ c.val) = 0) → e = e' := by
  first | exact @GlobalTheory.CompanionTheory.ContUniv.idem_unique | exact GlobalTheory.CompanionTheory.ContUniv.idem_unique | (intros; apply GlobalTheory.CompanionTheory.ContUniv.idem_unique <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsContinuousEpsilonPower
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.ContUniv.EtaFn

section Var

variable {S : Type} [CommRing S] {l : ℕ} [Fact l.Prime] {ϖ x : S}

theorem pow_sub_one_mem (hl : (l : S) = 0) (hx : x - 1 ∈ Ideal.span {ϖ}) (m : ℕ) :
    x ^ l ^ m - 1 ∈ Ideal.span {ϖ ^ l ^ m} := by
  rcases subsingleton_or_nontrivial S with h | h
  · rw [Subsingleton.elim (x ^ l ^ m - 1) 0]
    exact zero_mem _
  · haveI : CharP S l := (CharP.charP_iff_prime_eq_zero Fact.out).2 hl
    haveI : ExpChar S l := ExpChar.prime Fact.out
    have e : x ^ l ^ m - 1 = (x - 1) ^ l ^ m := by
      rw [sub_pow_char_pow, one_pow]
    rw [e, ← Ideal.span_singleton_pow]
    exact Ideal.pow_mem_pow hx _

theorem pow_sub_pow_mem (hl : (l : S) = 0) (hx : x - 1 ∈ Ideal.span {ϖ}) {a b m : ℕ}
    (h : a ≡ b [MOD l ^ m]) : x ^ a - x ^ b ∈ Ideal.span {ϖ ^ l ^ m} := by
  have key : ∀ a b : ℕ, a ≤ b → a ≡ b [MOD l ^ m] → x ^ b - x ^ a ∈ Ideal.span {ϖ ^ l ^ m} := by
    intro a b hab h
    obtain ⟨c, hc⟩ := (Nat.modEq_iff_dvd' hab).1 h
    have hb : b = a + l ^ m * c := by omega
    obtain ⟨d, hd⟩ : x ^ l ^ m - 1 ∣ (x ^ l ^ m) ^ c - 1 := by
      simpa using sub_dvd_pow_sub_pow (x ^ l ^ m) 1 c
    have e : x ^ b - x ^ a = (x ^ l ^ m - 1) * (d * x ^ a) := by
      rw [hb, pow_add, pow_mul]
      linear_combination x ^ a * hd
    rw [e]
    exact Ideal.mul_mem_right _ _ (pow_sub_one_mem hl hx m)
  rcases le_total a b with hab | hab
  · rw [← neg_sub]
    exact neg_mem (key a b hab h)
  · exact key b a hab h.symm

theorem span_pow_le {k n : ℕ} (h : k ≤ n) : Ideal.span {ϖ ^ n} ≤ Ideal.span {ϖ ^ k} :=
  Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow ϖ h)

theorem le_pow (k : ℕ) : k ≤ l ^ k := (Nat.lt_pow_self (Fact.out : l.Prime).one_lt).le

theorem exists_lim [IsAdicComplete (Ideal.span {ϖ}) S] (hl : (l : S) = 0)
    (hx : x - 1 ∈ Ideal.span {ϖ}) (a : ℕ → ℕ) (ha : ∀ m m', m ≤ m' → a m' ≡ a m [MOD l ^ m]) :
    ∃ L, ∀ m, L - x ^ a m ∈ Ideal.span {ϖ ^ l ^ m} := by
  obtain ⟨L, hL⟩ := exists_tends (ϖ := ϖ) (fun m => x ^ a m) fun k =>
    ⟨k, fun m hm => span_pow_le (le_pow (l := l) k) (pow_sub_pow_mem hl hx (ha k m hm))⟩
  refine ⟨L, fun m => ?_⟩
  obtain ⟨M, hM⟩ := hL (l ^ m)
  have h1 := hM (max M m) (le_max_left _ _)
  have h2 := pow_sub_pow_mem (ϖ := ϖ) hl hx (ha m (max M m) (le_max_right _ _))
  have := sub_mem h2 h1
  convert this using 1
  ring

theorem eq_of_forall_mem [IsHausdorff (Ideal.span {ϖ}) S] {a b : S}
    (h : ∀ m, a - b ∈ Ideal.span {ϖ ^ l ^ m}) : a = b :=
  Tends.unique (ϖ := ϖ) (x := fun _ => a) (tends_const a)
    fun k => ⟨0, fun _ _ => span_pow_le (le_pow (l := l) k) (h k)⟩

end Var

variable {l : ℕ} [Fact l.Prime]

theorem val_modEq {m m' : ℕ} (h : m ≤ m') (z : ℤ_[l]) :
    (PadicInt.toZModPow m' z).val ≡ (PadicInt.toZModPow m z).val [MOD l ^ m] := by
  rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_val, ZMod.natCast_zmod_val,
    PadicInt.cast_toZModPow _ _ h]

theorem val_add_one (m : ℕ) (z : ℤ_[l]) :
    (PadicInt.toZModPow m (z + 1)).val ≡ (PadicInt.toZModPow m z).val + 1 [MOD l ^ m] := by
  rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
    map_add, map_one, Nat.cast_one]

theorem exists_fn (A : PAlg l) (x : A.A) (hx : x - 1 ∈ Ideal.span {A.pi}) :
    ∃ η : (A.cont ℤ_[l]).A,
      (∀ (m : ℕ) (z : ℤ_[l]), Hom.f (A.evCont z) η - x ^ (PadicInt.toZModPow m z).val ∈
        Ideal.span {A.pi ^ (l ^ m)}) ∧
      ∀ z : ℤ_[l], Hom.f (A.evCont (z + 1)) η = x * Hom.f (A.evCont z) η := by
  haveI hc : IsAdicComplete (Ideal.span {A.pi}) A.A := A.compl
  have hl : (l : A.A) = 0 := A.natCast_l
  choose L hL using fun z : ℤ_[l] => exists_lim (ϖ := A.pi) hl hx
    (fun m => (PadicInt.toZModPow m z).val) (fun m m' h => val_modEq h z)
  refine ⟨⟨L, fun k => ?_⟩, fun m z => hL z m, fun z => ?_⟩
  · have e : (Ideal.Quotient.mk (Ideal.span {A.pi ^ k})) ∘ L =
        (fun c : ZMod (l ^ k) => Ideal.Quotient.mk (Ideal.span {A.pi ^ k}) (x ^ c.val)) ∘
          PadicInt.toZModPow k := funext fun z =>
      Ideal.Quotient.eq.2 (span_pow_le (le_pow (l := l) k) (hL z k))
    have h : IsLocallyConstant ((Ideal.Quotient.mk (Ideal.span {A.pi ^ k})) ∘ L) := by
      rw [e]
      exact (GlobalTheory.CompanionTheory.PadicShift.isLocallyConstant_toZModPow l k).comp _
    exact h
  · refine eq_of_forall_mem (ϖ := A.pi) (l := l) fun m => ?_
    have h1 := hL (z + 1) m
    have h2 := Ideal.mul_mem_left _ x (hL z m)
    have h3 := pow_sub_pow_mem (ϖ := A.pi) hl hx (val_add_one m z)
    have := add_mem h1 (sub_mem h3 h2)
    change L (z + 1) - x * L z ∈ _
    convert this using 1
    ring

theorem exists_eta (ε : Eps l) : ∃ η : ((base l).cont ℤ_[l]).A,
    (∀ (m : ℕ) (z : ℤ_[l]), Hom.f ((base l).evCont z) η - (base l).s (ε.e 0) ^ (PadicInt.toZModPow m z).val ∈ Ideal.span {(base l).pi ^ (l ^ m)}) ∧
    Hom.f (contShift (base l)) η = ((base l).cont ℤ_[l]).s (ε.e 0) * η := by
  have hx : (base l).s (ε.e 0) - 1 ∈ Ideal.span {(base l).pi} :=
    ((RL.sharp_cong (base l)).2.1 _ 1).1 (by
      rw [ε.sharp_e (base l), map_one, sub_self]
      exact zero_mem _)
  obtain ⟨η, h1, h2⟩ := exists_fn (base l) _ hx
  refine ⟨η, h1, cont_ext fun z => ?_⟩
  have e : Hom.f ((base l).evCont z) (((base l).cont ℤ_[l]).s (ε.e 0)) = (base l).s (ε.e 0) :=
    RingHom.congr_fun (Hom.comm ((base l).evCont z)) _
  rw [map_mul, e]
  exact h2 z

end GlobalTheory.CompanionTheory.ContUniv.EtaFn
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SharpEpsilonRootIdempotentSum
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SharpEpsilonRootIdempotentSum
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.ContUniv

section Frob

variable {l : ℕ} {R : Type} [CommRing R] (φ : R →+* R)

theorem mem_span_of_frob_mem (hb : Function.Bijective φ) {y p : R}
    (h : φ y ∈ Ideal.span {φ p}) : y ∈ Ideal.span {p} := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h
  obtain ⟨c', rfl⟩ := hb.2 c
  exact Ideal.mem_span_singleton'.2 ⟨c', hb.1 (by rw [map_mul, hc])⟩

theorem mem_span_of_pow_mem (hφ : ∀ x, φ x = x ^ l) (hb : Function.Bijective φ) {x p : R}
    (N : ℕ) (h : x ^ l ^ N ∈ Ideal.span {p ^ l ^ N}) : x ∈ Ideal.span {p} := by
  induction N with
  | zero => simpa using h
  | succ N ih =>
    refine ih (mem_span_of_frob_mem φ hb ?_)
    rw [hφ, hφ, ← pow_mul, ← pow_mul, ← pow_succ]
    exact h

theorem sub_pow_of_frob (hφ : ∀ x, φ x = x ^ l) (a b : R) (N : ℕ) :
    (a - b) ^ l ^ N = a ^ l ^ N - b ^ l ^ N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [pow_succ, pow_mul, pow_mul, pow_mul, ih, ← hφ, map_sub, hφ, hφ]

end Frob

theorem root_pow {l : ℕ} {T : Type} [Monoid T] {x : ℕ → T} (hx : ∀ m, x (m + 1) ^ l = x m) (m k : ℕ) :
    x (m + k) ^ l ^ k = x m := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ' l k, pow_mul, ← add_assoc, hx, ih]

variable {l : ℕ} [Fact l.Prime]

def powSum (A : PAlg l) (u : (A.cont ℤ_[l]).A) (N : ℕ) : (A.cont ℤ_[l]).A :=
  ∑ c : ZMod (l ^ N), ind A N c * u ^ c.val

theorem ev_powSum (A : PAlg l) (u : (A.cont ℤ_[l]).A) (N : ℕ) (z : ℤ_[l]) :
    Hom.f (A.evCont z) (powSum A u N) = Hom.f (A.evCont z) u ^ (PadicInt.toZModPow N z).val := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [powSum, map_sum]
  simp only [map_mul, map_pow, ev_ind, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp

theorem sub_powSum_mem (A : PAlg l) {u ρ : ℕ → (A.cont ℤ_[l]).A} (hu : ∀ n, u (n + 1) ^ l = u n)
    (hρ : ∀ n, ρ (n + 1) ^ l = ρ n)
    (h0 : ∀ (m : ℕ) (z : ℤ_[l]), Hom.f (A.evCont z) (ρ 0) -
      Hom.f (A.evCont z) (u 0) ^ (PadicInt.toZModPow m z).val ∈ Ideal.span {A.pi ^ (l ^ m)})
    (N : ℕ) : ρ N - powSum A (u N) N ∈ Ideal.span {(A.cont ℤ_[l]).pi} := by
  have hf : ∀ x : (A.cont ℤ_[l]).A, (A.cont ℤ_[l]).frob x = x ^ l := fun _ => rfl
  refine mem_span_of_pow_mem (l := l) (A.cont ℤ_[l]).frob hf (A.cont ℤ_[l]).frob_bijective N ?_
  have h1 : ρ N ^ l ^ N = ρ 0 := by simpa using root_pow hρ 0 N
  have h2 : u N ^ l ^ N = u 0 := by simpa using root_pow hu 0 N
  rw [sub_pow_of_frob (l := l) _ hf, h1, mem_span_pi_pow]
  intro z
  rw [map_sub, map_pow, ev_powSum, ← pow_mul, mul_comm, pow_mul, ← map_pow, h2]
  exact h0 N z

theorem sharp_powSum (A : PAlg l) {u : ℕ → (A.cont ℤ_[l]).A} (hu : ∀ n, u (n + 1) ^ l = u n)
    (m k : ℕ) (hv : (A.cont ℤ_[l]).sharp (u m) ^ l ^ m = 1) :
    (A.cont ℤ_[l]).sharp (powSum A (u (m + k)) (m + k) ^ l ^ k) =
      ∑ c : ZMod (l ^ m), (A.cont ℤ_[l]).sharp (ind A m c) * (A.cont ℤ_[l]).sharp (u m) ^ c.val := by
  set B := powSum A (u (m + k)) (m + k) ^ l ^ k with hB
  set v := (A.cont ℤ_[l]).sharp (u m) with hvdef
  set T := ∑ c : ZMod (l ^ m), (A.cont ℤ_[l]).sharp (ind A m c) * v ^ c.val with hT
  have hle : m ≤ m + k := Nat.le_add_right m k
  have h1 : ∀ c' : ZMod (l ^ (m + k)), ind A (m + k) c' * B = ind A (m + k) c' * u m ^ c'.val := by
    intro c'
    refine cont_ext fun z => ?_
    rw [map_mul, map_mul, ev_ind]
    split_ifs with h
    · have hr : Hom.f (A.evCont z) (u (m + k)) ^ l ^ k = Hom.f (A.evCont z) (u m) := by
        rw [← map_pow, root_pow hu]
      rw [hB, map_pow, ev_powSum, map_pow, h, ← pow_mul, mul_comm c'.val, pow_mul, hr]
    · simp
  have h2 : ∀ (c' : ZMod (l ^ (m + k))) (c : ZMod (l ^ m)), ZMod.cast c' ≠ c →
      ind A (m + k) c' * ind A m c = 0 := by
    intro c' c hc
    refine cont_ext fun z => ?_
    rw [map_mul, ev_ind, ev_ind, map_zero]
    split_ifs with h h'
    · exact absurd (by rw [← h', ← h, PadicInt.cast_toZModPow m (m + k) hle]) hc
    all_goals simp
  have h3 : ∀ c' : ZMod (l ^ (m + k)),
      ind A (m + k) c' * ind A m (ZMod.cast c') = ind A (m + k) c' := by
    intro c'
    refine cont_ext fun z => ?_
    rw [map_mul, ev_ind, ev_ind]
    split_ifs with h h'
    · simp
    · exact absurd (by rw [← h, PadicInt.cast_toZModPow m (m + k) hle]) h'
    all_goals simp
  have h4 : ∀ c' : ZMod (l ^ (m + k)), v ^ (ZMod.cast c' : ZMod (l ^ m)).val = v ^ c'.val := by
    intro c'
    rw [pow_eq_pow_mod c'.val hv, ← ZMod.natCast_val, ZMod.val_natCast]
  have key : ∀ c' : ZMod (l ^ (m + k)), (A.cont ℤ_[l]).sharp (ind A (m + k) c') * (A.cont ℤ_[l]).sharp B =
      (A.cont ℤ_[l]).sharp (ind A (m + k) c') * T := by
    intro c'
    rw [← map_mul, h1, map_mul, map_pow, hT, Finset.mul_sum, Finset.sum_eq_single (ZMod.cast c')]
    · rw [← mul_assoc, ← map_mul, h3, h4]
    · intro c _ hc
      rw [← mul_assoc, ← map_mul, h2 c' c (Ne.symm hc), sharp_zero, zero_mul]
    · simp
  have hsum := sum_sharp_eq_one (A.cont ℤ_[l]) (coi_ind A (m + k))
  calc (A.cont ℤ_[l]).sharp B = (∑ c', (A.cont ℤ_[l]).sharp (ind A (m + k) c')) * (A.cont ℤ_[l]).sharp B := by
        rw [hsum, one_mul]
    _ = (∑ c', (A.cont ℤ_[l]).sharp (ind A (m + k) c')) * T := by
        rw [Finset.sum_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun c' _ => key c'
    _ = T := by rw [hsum, one_mul]

theorem sharp_roots_core (A : PAlg l) {u ρ : ℕ → (A.cont ℤ_[l]).A} (hu : ∀ n, u (n + 1) ^ l = u n)
    (hs : (A.cont ℤ_[l]).sharp (u 0) = 1) (hρ : ∀ n, ρ (n + 1) ^ l = ρ n)
    (h0 : ∀ (m : ℕ) (z : ℤ_[l]), Hom.f (A.evCont z) (ρ 0) -
      Hom.f (A.evCont z) (u 0) ^ (PadicInt.toZModPow m z).val ∈ Ideal.span {A.pi ^ (l ^ m)})
    (m : ℕ) : (A.cont ℤ_[l]).sharp (ρ m) =
      ∑ c : ZMod (l ^ m), (A.cont ℤ_[l]).sharp (ind A m c) * (A.cont ℤ_[l]).sharp (u m) ^ c.val := by
  have hv : (A.cont ℤ_[l]).sharp (u m) ^ l ^ m = 1 := by
    rw [← map_pow, (by simpa using root_pow hu 0 m : u m ^ l ^ m = u 0), hs]
  have hk : ∀ k, (A.cont ℤ_[l]).sharp (ρ m) -
      ∑ c : ZMod (l ^ m), (A.cont ℤ_[l]).sharp (ind A m c) * (A.cont ℤ_[l]).sharp (u m) ^ c.val ∈
      Ideal.span {(l : (A.cont ℤ_[l]).U) ^ (k + 1)} := by
    intro k
    have h := (RL.sharp_cong (A.cont ℤ_[l])).1 _ _ k (sub_powSum_mem A hu hρ h0 (m + k))
    rwa [root_pow hρ, sharp_powSum A hu m k hv] at h
  refine sub_eq_zero.1 (IsHausdorff.haus
    (inferInstance : IsHausdorff (Ideal.span {(l : (A.cont ℤ_[l]).U)}) (A.cont ℤ_[l]).U) _ fun k => ?_)
  refine smodEq_iff.2 ?_
  rw [sub_zero]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (hk k)
  exact Ideal.mem_span_singleton'.2 ⟨c * l, by rw [← hc, pow_succ]; ring⟩

theorem sharp_roots_universal {l : ℕ} [Fact l.Prime] (ε : Eps l) (ρ : ℕ → ((base l).cont ℤ_[l]).A)
    (h0 : ∀ (m : ℕ) (z : ℤ_[l]), Hom.f ((base l).evCont z) (ρ 0) -
      (base l).s (ε.e 0) ^ (PadicInt.toZModPow m z).val ∈ Ideal.span {(base l).pi ^ (l ^ m)})
    (hρ : ∀ m, ρ (m + 1) ^ l = ρ m) (m : ℕ) : ((base l).cont ℤ_[l]).sharp (ρ m) =
    ∑ c : ZMod (l ^ m), ((base l).cont ℤ_[l]).sharp (GlobalTheory.CompanionTheory.ContUniv.ind (base l) m c) *
      ((base l).cont ℤ_[l]).sharp (((base l).cont ℤ_[l]).s (ε.e m)) ^ c.val := by
  have hev : ∀ (n : ℕ) (z : ℤ_[l]),
      Hom.f ((base l).evCont z) (((base l).cont ℤ_[l]).s (ε.e n)) = (base l).s (ε.e n) :=
    fun n z => RingHom.congr_fun (Hom.comm ((base l).evCont z)) _
  refine sharp_roots_core (base l) (u := fun n => ((base l).cont ℤ_[l]).s (ε.e n)) (fun n => ?_)
    (ε.sharp_e _) hρ (fun k z => ?_) m
  · show ((base l).cont ℤ_[l]).s (ε.e (n + 1)) ^ l = ((base l).cont ℤ_[l]).s (ε.e n)
    rw [← map_pow, ← Units.val_pow_eq_pow_val, ε.succ]
  · show Hom.f ((base l).evCont z) (ρ 0) -
      Hom.f ((base l).evCont z) (((base l).cont ℤ_[l]).s (ε.e 0)) ^ _ ∈ _
    rw [hev]
    exact h0 k z

end GlobalTheory.CompanionTheory.ContUniv
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SharpEpsilonRootIdempotentSumStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sharp_epsilon_root_idempotent_sum : ∀ {l : ℕ} [Fact l.Prime] (ε : Eps l) (ρ : ℕ → ((base l).cont ℤ_[l]).A),
  (∀ (m : ℕ) (z : ℤ_[l]), Hom.f ((base l).evCont z) (ρ 0) - (base l).s (ε.e 0) ^ (PadicInt.toZModPow m z).val ∈ Ideal.span {(base l).pi ^ (l ^ m)}) →
  (∀ m, ρ (m + 1) ^ l = ρ m) → ∀ m, ((base l).cont ℤ_[l]).sharp (ρ m) =
    ∑ c : ZMod (l ^ m), ((base l).cont ℤ_[l]).sharp (GlobalTheory.CompanionTheory.ContUniv.ind (base l) m c) *
      ((base l).cont ℤ_[l]).sharp (((base l).cont ℤ_[l]).s (ε.e m)) ^ c.val := by
  first | exact @GlobalTheory.CompanionTheory.ContUniv.sharp_roots_universal | exact GlobalTheory.CompanionTheory.ContUniv.sharp_roots_universal | (intros; apply GlobalTheory.CompanionTheory.ContUniv.sharp_roots_universal <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdempotentsCoarsenToLowerLevel
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdempotentsCoarsenToLowerLevel
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.ContUniv

theorem coi_fiber {R I J : Type} [CommRing R] [Fintype I] [Fintype J] [DecidableEq J]
    (π : I → J) {e : I → R} (he : CompleteOrthogonalIdempotents e) :
    CompleteOrthogonalIdempotents (fun c : J => ∑ c' with π c' = c, e c') := by
  classical
  have hmul : ∀ c d : J, (∑ c' with π c' = c, e c') * (∑ c' with π c' = d, e c') =
      if c = d then ∑ c' with π c' = c, e c' else 0 := by
    intro c d
    rw [Finset.sum_mul_sum]
    split_ifs with hcd
    · subst hcd
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.sum_eq_single i]
      · exact he.idem i
      · intro j _ hji
        exact he.ortho hji.symm
      · intro h; exact absurd hi h
    · refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => he.ortho ?_
      rintro rfl
      exact hcd ((Finset.mem_filter.1 hi).2.symm.trans (Finset.mem_filter.1 hj).2)
  refine ⟨⟨fun c => ?_, fun c d hcd => ?_⟩, ?_⟩
  · change _ * _ = _
    rw [hmul, if_pos rfl]
  · change _ * _ = _
    rw [hmul, if_neg hcd]
  · rw [Finset.sum_fiberwise]
    exact he.complete

theorem chain_pow {M : Type} [Monoid M] {p : ℕ} {x : ℕ → M} (h : ∀ k, x (k + 1) ^ p = x k)
    (m d : ℕ) : x (m + d) ^ p ^ d = x m := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [pow_succ', pow_mul, ← add_assoc, h, ih]

theorem mul_sub_pow {S : Type} [CommRing S] {a x y : S} (h : a * (x - y) = 0) (q : ℕ) :
    a * (x ^ q - y ^ q) = 0 := by
  obtain ⟨d, hd⟩ := sub_dvd_pow_sub_pow x y q
  rw [hd, ← mul_assoc, h, zero_mul]

theorem val_modEq {N M : ℕ} [NeZero N] [NeZero M] (h : M ∣ N) (c : ZMod N) :
    c.val ≡ (ZMod.castHom h (ZMod M) c).val [MOD M] := by
  have h0 := map_natCast (ZMod.castHom h (ZMod M)) c.val
  rw [ZMod.natCast_zmod_val] at h0
  rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]
  exact h0.symm

variable {l : ℕ} [Fact l.Prime]

theorem sharp_xi_pow (ε : Eps l) (t : PAlg l) (m d : ℕ) :
    t.sharp (t.s (ε.e (m + d))) ^ l ^ d = t.sharp (t.s (ε.e m)) := by
  rw [← map_pow, ← map_pow, ← Units.val_pow_eq_pow_val, chain_pow ε.succ]

theorem sharp_xi_period (ε : Eps l) (t : PAlg l) (m : ℕ) :
    t.sharp (t.s (ε.e m)) ^ l ^ m = 1 := by
  have := sharp_xi_pow ε t 0 m
  rw [zero_add] at this
  rw [this]
  exact ε.sharp_e t

theorem coi_descend (ε : Eps l) (t : PAlg l) (r : ℕ → t.A) (hr : ∀ m, r (m + 1) ^ l = r m)
    {m n : ℕ} (h : m ≤ n) (e : ZMod (l ^ n) → t.A) (he : CompleteOrthogonalIdempotents e)
    (hc : ∀ c, t.sharp (e c) * (t.sharp (r n) - t.sharp (t.s (ε.e n)) ^ c.val) = 0) :
    CompleteOrthogonalIdempotents
        (fun c : ZMod (l ^ m) => ∑ c' with ZMod.castHom (pow_dvd_pow l h) (ZMod (l ^ m)) c' = c, e c') ∧
      ∀ c : ZMod (l ^ m), t.sharp (∑ c' with ZMod.castHom (pow_dvd_pow l h) (ZMod (l ^ m)) c' = c, e c') *
        (t.sharp (r m) - t.sharp (t.s (ε.e m)) ^ c.val) = 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  refine ⟨coi_fiber _ he, fun c => ?_⟩
  rw [(sharp_sum t _ e (fun i _ => he.idem i) (fun i _ j _ hij => he.ortho hij)).1, Finset.sum_mul]
  refine Finset.sum_eq_zero fun c' hc' => ?_
  have hπ := (Finset.mem_filter.1 hc').2
  have h1 := mul_sub_pow (hc c') (l ^ d)
  rw [← map_pow, chain_pow hr, ← pow_mul, mul_comm c'.val, pow_mul, sharp_xi_pow] at h1
  have h2 : t.sharp (t.s (ε.e m)) ^ c'.val = t.sharp (t.s (ε.e m)) ^ c.val := by
    have hv := val_modEq (pow_dvd_pow l h) c'
    rw [hπ] at hv
    rw [pow_eq_pow_mod c'.val (sharp_xi_period ε t m), pow_eq_pow_mod c.val (sharp_xi_period ε t m)]
    exact congrArg _ hv
  rwa [h2] at h1

end GlobalTheory.CompanionTheory.ContUniv
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdempotentsCoarsenToLowerLevelStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotents_coarsen_to_lower_level : ∀ {l : ℕ} [Fact l.Prime] (ε : Eps l) (t : PAlg l) (r : ℕ → t.A), (∀ m, r (m + 1) ^ l = r m) →
  ∀ {m n : ℕ} (h : m ≤ n) (e : ZMod (l ^ n) → t.A), CompleteOrthogonalIdempotents e →
  (∀ c, t.sharp (e c) * (t.sharp (r n) - t.sharp (t.s (ε.e n)) ^ c.val) = 0) →
  CompleteOrthogonalIdempotents (fun c : ZMod (l ^ m) => ∑ c' with ZMod.castHom (pow_dvd_pow l h) (ZMod (l ^ m)) c' = c, e c') ∧
  ∀ c : ZMod (l ^ m), t.sharp (∑ c' with ZMod.castHom (pow_dvd_pow l h) (ZMod (l ^ m)) c' = c, e c') * (t.sharp (r m) - t.sharp (t.s (ε.e m)) ^ c.val) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.ContUniv.coi_descend | exact GlobalTheory.CompanionTheory.ContUniv.coi_descend | (intros; apply GlobalTheory.CompanionTheory.ContUniv.coi_descend <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousAlgebraUniversalProperty
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.ContUniv

variable {l : ℕ} [Fact l.Prime]

theorem sum_mul_sum_idem {T I : Type} [CommRing T] [Fintype I] {e : I → T}
    (h : CompleteOrthogonalIdempotents e) (a b : I → T) :
    (∑ i, e i * a i) * (∑ i, e i * b i) = ∑ i, e i * (a i * b i) := by
  classical
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · have : e i * a i * (e i * b i) = (e i * e i) * (a i * b i) := by ring
    rw [this, h.idem i]
  · intro j _ hj
    have : e i * a i * (e j * b j) = (e i * e j) * (a i * b j) := by ring
    rw [this, h.ortho hj.symm, zero_mul]
  · simp

def rep {m : ℕ} (c : ZMod (l ^ m)) : ℤ_[l] := ((c.val : ℕ) : ℤ_[l])

theorem toZModPow_rep {m : ℕ} (c : ZMod (l ^ m)) : PadicInt.toZModPow m (rep c) = c := by
  rw [rep, map_natCast, ZMod.natCast_zmod_val]

theorem toZModPow_rep_of_le {m n : ℕ} (h : m ≤ n) (c : ZMod (l ^ n)) :
    PadicInt.toZModPow m (rep c) = ZMod.castHom (pow_dvd_pow l h) (ZMod (l ^ m)) c := by
  rw [rep, map_natCast, ZMod.natCast_val, ZMod.castHom_apply]

def stage {A : PAlg l} {T : Type} [CommRing T] (φ : A.A →+* T) {m : ℕ} (e : ZMod (l ^ m) → T)
    (he : CompleteOrthogonalIdempotents e) : (A.cont ℤ_[l]).A →+* T where
  toFun f := ∑ c, e c * φ (Hom.f (A.evCont (rep c)) f)
  map_one' := by simp only [map_one, mul_one]; exact he.complete
  map_mul' f g := by
    rw [sum_mul_sum_idem he]
    simp only [map_mul]
  map_zero' := by simp only [map_zero, mul_zero, Finset.sum_const_zero]
  map_add' f g := by
    simp only [map_add (f := _), mul_add, Finset.sum_add_distrib]

theorem stage_apply {A : PAlg l} {T : Type} [CommRing T] (φ : A.A →+* T) {m : ℕ} (e : ZMod (l ^ m) → T)
    (he : CompleteOrthogonalIdempotents e) (f : (A.cont ℤ_[l]).A) :
    stage φ e he f = ∑ c, e c * φ (Hom.f (A.evCont (rep c)) f) := rfl

theorem hom_pi {A t : PAlg l} (φ : A ⟶ t) : Hom.f φ A.pi = t.pi :=
  RingHom.congr_fun (Hom.comm φ) (pFlat l)

theorem map_mem_span {A t : PAlg l} (φ : A ⟶ t) {k : ℕ} {x : A.A} (h : x ∈ Ideal.span {A.pi ^ k}) :
    Hom.f φ x ∈ Ideal.span {t.pi ^ k} := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 h
  rw [map_mul, map_pow, hom_pi]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

theorem stage_cauchy {A t : PAlg l} (φ : A ⟶ t) (e : ∀ m : ℕ, ZMod (l ^ m) → t.A)
    (he : ∀ m, CompleteOrthogonalIdempotents (e m))
    (hc : ∀ (m n : ℕ) (h : m ≤ n) (c : ZMod (l ^ m)),
      e m c = ∑ c' with ZMod.castHom (pow_dvd_pow l h) (ZMod (l ^ m)) c' = c, e n c')
    (f : (A.cont ℤ_[l]).A) (k : ℕ) :
    ∃ M, ∀ m, M ≤ m → stage (Hom.f φ) (e m) (he m) f - stage (Hom.f φ) (e M) (he M) f ∈
      Ideal.span {t.pi ^ k} := by
  obtain ⟨M, hM⟩ := exists_period A f k
  refine ⟨M, fun m hm => ?_⟩
  have h1 : stage (Hom.f φ) (e M) (he M) f = ∑ c : ZMod (l ^ m), e m c * Hom.f φ (Hom.f (A.evCont
      (rep (ZMod.castHom (pow_dvd_pow l hm) (ZMod (l ^ M)) c))) f) := by
    rw [stage_apply, ← Finset.sum_fiberwise Finset.univ (ZMod.castHom (pow_dvd_pow l hm) (ZMod (l ^ M)))]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [hc M m hm d, Finset.sum_mul]
    refine Finset.sum_congr rfl fun c hc' => ?_
    rw [(Finset.mem_filter.1 hc').2]
  rw [h1, stage_apply, ← Finset.sum_sub_distrib]
  refine Ideal.sum_mem _ fun c _ => ?_
  rw [← mul_sub, ← map_sub]
  refine Ideal.mul_mem_left _ _ (map_mem_span φ (hM _ _ ?_))
  rw [toZModPow_rep_of_le hm, toZModPow_rep]

theorem stage_ind {A t : PAlg l} (φ : A ⟶ t) (e : ∀ m : ℕ, ZMod (l ^ m) → t.A)
    (he : ∀ m, CompleteOrthogonalIdempotents (e m))
    (hc : ∀ (m n : ℕ) (h : m ≤ n) (c : ZMod (l ^ m)),
      e m c = ∑ c' with ZMod.castHom (pow_dvd_pow l h) (ZMod (l ^ m)) c' = c, e n c')
    {m n : ℕ} (h : m ≤ n) (c : ZMod (l ^ m)) :
    stage (Hom.f φ) (e n) (he n) (ind A m c) = e m c := by
  rw [stage_apply, hc m n h c, Finset.sum_filter]
  refine Finset.sum_congr rfl fun c' _ => ?_
  rw [ev_ind, toZModPow_rep_of_le h]
  split_ifs <;> simp

theorem map_exists (A t : PAlg l) (φ : A ⟶ t) (e : ∀ m : ℕ, ZMod (l ^ m) → t.A)
    (he : ∀ m, CompleteOrthogonalIdempotents (e m))
    (hc : ∀ (m n : ℕ) (h : m ≤ n) (c : ZMod (l ^ m)),
      e m c = ∑ c' with ZMod.castHom (pow_dvd_pow l h) (ZMod (l ^ m)) c' = c, e n c') :
    ∃ ψ : A.cont ℤ_[l] ⟶ t, A.toCont ℤ_[l] ≫ ψ = φ ∧ ∀ m c, Hom.f ψ (ind A m c) = e m c := by
  haveI : IsAdicComplete (Ideal.span {t.pi}) t.A := t.compl
  obtain ⟨ψ, hψ⟩ := exists_lim_hom (ϖ := t.pi) (fun m => stage (Hom.f φ) (e m) (he m))
    (stage_cauchy φ e he hc)
  have hconst : ∀ x : A.A, ψ (Hom.f (A.toCont ℤ_[l]) x) = Hom.f φ x := fun x => by
    refine (hψ _).unique ?_
    have : (fun m => stage (Hom.f φ) (e m) (he m) (Hom.f (A.toCont ℤ_[l]) x)) = fun _ => Hom.f φ x := by
      funext m
      rw [stage_apply]
      simp only [ev_toCont]
      rw [← Finset.sum_mul, (he m).complete, one_mul]
    rw [this]
    exact tends_const _
  have hcomm : ψ.comp (A.cont ℤ_[l]).s = t.s := RingHom.ext fun y => by
    have h := hconst (A.s y)
    exact h.trans (RingHom.congr_fun (Hom.comm φ) y)
  refine ⟨⟨ψ, hcomm⟩, Hom.ext (RingHom.ext hconst), fun m c => ?_⟩
  refine (hψ _).unique fun k => ⟨m, fun n hn => ?_⟩
  beta_reduce
  rw [stage_ind φ e he hc hn c, sub_self]
  exact zero_mem _

theorem map_unique {A t : PAlg l} (ψ ψ' : A.cont ℤ_[l] ⟶ t)
    (h1 : A.toCont ℤ_[l] ≫ ψ = A.toCont ℤ_[l] ≫ ψ')
    (h2 : ∀ m c, Hom.f ψ (ind A m c) = Hom.f ψ' (ind A m c)) : ψ = ψ' := by
  haveI : IsAdicComplete (Ideal.span {t.pi}) t.A := t.compl
  have hconst : ∀ x, Hom.f ψ (Hom.f (A.toCont ℤ_[l]) x) = Hom.f ψ' (Hom.f (A.toCont ℤ_[l]) x) :=
    fun x => congrArg (fun g : A ⟶ t => Hom.f g x) h1
  refine Hom.ext (RingHom.ext fun f => ?_)
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {t.pi}) t.A) _ fun k => ?_
  refine smodEq_iff.2 ?_
  rw [sub_zero]
  obtain ⟨M, hM⟩ := exists_period A f k
  let g : (A.cont ℤ_[l]).A := ∑ c, ind A M c * Hom.f (A.toCont ℤ_[l]) (Hom.f (A.evCont (rep c)) f)
  have hg : Hom.f ψ g = Hom.f ψ' g := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [g, map_sum, map_mul, h2, hconst]
  have hfg : f - g ∈ Ideal.span {(A.cont ℤ_[l]).pi ^ k} := by
    refine (mem_span_pi_pow A k _).2 fun z => ?_
    have : Hom.f (A.evCont z) g = Hom.f (A.evCont (rep (PadicInt.toZModPow M z))) f := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [g, map_sum, map_mul, ev_toCont, ev_ind]
      rw [Finset.sum_eq_single (PadicInt.toZModPow M z)]
      · simp
      · intro c _ hc
        rw [if_neg hc.symm, zero_mul]
      · simp
    rw [map_sub, this]
    exact hM _ _ (toZModPow_rep _).symm
  have h3 := map_mem_span ψ hfg
  have h4 := map_mem_span ψ' hfg
  have := sub_mem h3 h4
  rw [map_sub, map_sub, hg, sub_sub_sub_cancel_right] at this
  exact this

theorem map_existsUnique : ∀ {l : ℕ} [Fact l.Prime] (A t : PAlg l) (φ : A ⟶ t) (e : ∀ m : ℕ, ZMod (l ^ m) → t.A), (∀ m, CompleteOrthogonalIdempotents (e m)) →
  (∀ (m n : ℕ) (h : m ≤ n) (c : ZMod (l ^ m)), e m c = ∑ c' with ZMod.castHom (pow_dvd_pow l h) (ZMod (l ^ m)) c' = c, e n c') →
  ∃! ψ : A.cont ℤ_[l] ⟶ t, A.toCont ℤ_[l] ≫ ψ = φ ∧ ∀ m c, Hom.f ψ (ind A m c) = e m c := by
  intro l _ A t φ e he hc
  obtain ⟨ψ, h1, h2⟩ := map_exists A t φ e he hc
  exact ⟨ψ, ⟨h1, h2⟩, fun ψ' ⟨h3, h4⟩ => map_unique ψ' ψ (h3.trans h1.symm)
    fun m c => (h4 m c).trans (h2 m c).symm⟩

theorem level : ∀ {l : ℕ} [Fact l.Prime] (ε : Eps l) (t : PAlg l), t.IsTest → ∀ (r : ℕ → t.A), (∀ m, r (m + 1) ^ l = r m) → t.sharp (r 0) = 1 →
  ∀ m, ∃ e : ZMod (l ^ m) → t.A, CompleteOrthogonalIdempotents e ∧ ∀ c, t.sharp (e c) * (t.sharp (r m) - t.sharp (t.s (ε.e m)) ^ c.val) = 0 := by
  intro l _ ε t ht r hr h1 m
  have hp := (GlobalTheory.T.epsilon_cyclotomic_element_properties ε).2.2.2.2 m
  have hz : t.sharp (r m) ^ l ^ m = 1 := by
    have : ∀ m, r m ^ l ^ m = r 0 := fun m => by
      induction m with
      | zero => simp
      | succ m ih => rw [pow_succ', pow_mul, hr, ih]
    rw [← map_pow, this, h1]
  obtain ⟨e, he, h⟩ := RL.mu_lc t ht.val_aic.1 m _ hp _ hz
  refine ⟨e, he, fun c => ?_⟩
  have h2 : t.oC (theta0 l (WittVector.teichmuller l (ε.e m : Ob l))) = t.sharp (t.s (ε.e m)) := by
    rw [oC_theta0, sW, WittVector.map_teichmuller]; rfl
  rw [← h2]
  exact h c

theorem formula (ε : Eps l) {ρ : ℕ → ((base l).cont ℤ_[l]).A}
    (hF : ∀ m, ((base l).cont ℤ_[l]).sharp (ρ m) =
      ∑ c : ZMod (l ^ m), ((base l).cont ℤ_[l]).sharp (ind (base l) m c) *
        ((base l).cont ℤ_[l]).sharp (((base l).cont ℤ_[l]).s (ε.e m)) ^ c.val)
    {A t : PAlg l} (ψ : A.cont ℤ_[l] ⟶ t) (m : ℕ) :
    t.sharp (Hom.f ψ (Hom.f (contMap A.fromBase ℤ_[l]) (ρ m))) =
      ∑ c : ZMod (l ^ m), t.sharp (Hom.f ψ (ind A m c)) * t.sharp (t.s (ε.e m)) ^ c.val := by
  have h := congrArg (mapU (contMap A.fromBase ℤ_[l] ≫ ψ)) (hF m)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [mapU_sharp, map_sum] at h
  refine h.trans (Finset.sum_congr rfl fun c _ => ?_)
  rw [map_mul, map_pow, mapU_sharp, mapU_sharp]
  have h1 : Hom.f (contMap A.fromBase ℤ_[l] ≫ ψ) (ind (base l) m c) = Hom.f ψ (ind A m c) :=
    congrArg (Hom.f ψ) (contMap_ind A.fromBase m c)
  have h2 : Hom.f (contMap A.fromBase ℤ_[l] ≫ ψ) (((base l).cont ℤ_[l]).s (ε.e m)) = t.s (ε.e m) :=
    RingHom.congr_fun (Hom.comm (contMap A.fromBase ℤ_[l] ≫ ψ)) _
  rw [h1, h2]

theorem rel_of_formula {t : PAlg l} {m : ℕ} {E : ZMod (l ^ m) → t.A} (hE : CompleteOrthogonalIdempotents E)
    {x ξ : t.U} (hx : x = ∑ c, t.sharp (E c) * ξ ^ c.val) (c : ZMod (l ^ m)) :
    t.sharp (E c) * (x - ξ ^ c.val) = 0 :=
  mul_sub_eq_zero_of_sum (a := fun c => t.sharp (E c)) (b := fun c : ZMod (l ^ m) => ξ ^ c.val)
    (fun i => by rw [← map_mul, hE.idem i]) (fun i j h => by rw [← map_mul, hE.ortho h, sharp_zero]) hx c

theorem continuous_algebra_universal_existsUnique (ε : Eps l) {ρ : ℕ → ((base l).cont ℤ_[l]).A} (hρ : ∀ m, ρ (m + 1) ^ l = ρ m)
    (hF : ∀ m, ((base l).cont ℤ_[l]).sharp (ρ m) =
      ∑ c : ZMod (l ^ m), ((base l).cont ℤ_[l]).sharp (ind (base l) m c) *
        ((base l).cont ℤ_[l]).sharp (((base l).cont ℤ_[l]).s (ε.e m)) ^ c.val)
    (A t : PAlg l) (ht : t.IsTest) (φ : A ⟶ t) (u : (t.A)ˣ) (hu : t.sharp u = 1) :
    ∃! ψ : A.cont ℤ_[l] ⟶ t, A.toCont ℤ_[l] ≫ ψ = φ ∧
      Hom.f ψ (Hom.f (contMap A.fromBase ℤ_[l]) (ρ 0)) = u := by
  obtain ⟨r, hr0, hr⟩ := exists_roots t (u : t.A)
  have hr1 : t.sharp (r 0) = 1 := by rw [hr0, hu]
  choose e he hrel using level ε t ht r hr hr1
  have hcomp : ∀ (m n : ℕ) (h : m ≤ n) (c : ZMod (l ^ m)),
      e m c = ∑ c' with ZMod.castHom (pow_dvd_pow l h) (ZMod (l ^ m)) c' = c, e n c' := fun m n h c => by
    obtain ⟨h1, h2⟩ := GlobalTheory.T.idempotents_coarsen_to_lower_level ε t r hr h (e n) (he n) (hrel n)
    exact congrFun (GlobalTheory.T.idempotents_unique_for_epsilon_root ε t m (t.sharp (r m)) (e m) _ (he m) h1 (hrel m) h2) c
  obtain ⟨ψ, ⟨hψ1, hψ2⟩, hψ⟩ := map_existsUnique A t φ e he hcomp
  have hv : ∀ (ψ' : A.cont ℤ_[l] ⟶ t) (m : ℕ), Hom.f ψ' (Hom.f (contMap A.fromBase ℤ_[l]) (ρ (m + 1))) ^ l =
      Hom.f ψ' (Hom.f (contMap A.fromBase ℤ_[l]) (ρ m)) := fun ψ' m => by
    rw [← map_pow, ← map_pow, hρ]
  refine ⟨ψ, ⟨hψ1, ?_⟩, fun ψ' ⟨h1, h2⟩ => hψ ψ' ⟨h1, fun m c => ?_⟩⟩
  · have hE : ∀ m, (fun c => Hom.f ψ (ind A m c)) = e m := fun m => funext (hψ2 m)
    have key : (fun m => Hom.f ψ (Hom.f (contMap A.fromBase ℤ_[l]) (ρ m))) = r := by
      refine RL.tilt_inj t _ _ (hv ψ) hr fun m => ?_
      rw [formula ε hF ψ m]
      have := eq_sum_of_mul_sub (a := fun c => t.sharp (e m c))
        (b := fun c : ZMod (l ^ m) => t.sharp (t.s (ε.e m)) ^ c.val) (sum_sharp_eq_one t (he m)) (hrel m)
      rw [this]
      exact Finset.sum_congr rfl fun c _ => by rw [hψ2 m c]
    exact (congrFun key 0).trans hr0
  · have key : (fun m => Hom.f ψ' (Hom.f (contMap A.fromBase ℤ_[l]) (ρ m))) = r :=
      roots_unique t (h2.trans hr0.symm) (hv ψ') hr
    refine congrFun (GlobalTheory.T.idempotents_unique_for_epsilon_root ε t m (t.sharp (r m)) _ (e m) (coi_map ψ' m) (he m) (fun c => ?_) (hrel m)) c
    have := rel_of_formula (coi_map ψ' m) (formula ε hF ψ' m) c
    rwa [show Hom.f ψ' (Hom.f (contMap A.fromBase ℤ_[l]) (ρ m)) = r m from congrFun key m] at this

theorem main : ∀ {l : ℕ} [Fact l.Prime] (ε : Eps l),
    ∃ η : (((base l).cont ℤ_[l]).A)ˣ, ((base l).cont ℤ_[l]).sharp η = 1 ∧
      PAlg.Hom.f (CrystallineSemistableComparison.B.contShift (base l)) η =
        ((base l).cont ℤ_[l]).s (ε.e 0) * (η : ((base l).cont ℤ_[l]).A) ∧
      ∀ (A t : PAlg l), t.IsTest → ∀ (φ : A ⟶ t) (u : (t.A)ˣ), t.sharp u = 1 →
        ∃! ψ : A.cont ℤ_[l] ⟶ t, A.toCont ℤ_[l] ≫ ψ = φ ∧
          PAlg.Hom.f ψ (PAlg.Hom.f (contMap A.fromBase ℤ_[l]) η) = u := by
  intro l _ ε
  have hx : (base l).s (ε.e 0) - 1 ∈ Ideal.span {(base l).pi} :=
    ((RL.sharp_cong (base l)).2.1 _ 1).1 (by
      rw [ε.sharp_e (base l), map_one, sub_self]
      exact zero_mem _)
  obtain ⟨η, hη, hshift⟩ := EtaFn.exists_fn (base l) _ hx
  have hs : PAlg.Hom.f (CrystallineSemistableComparison.B.contShift (base l)) η =
      ((base l).cont ℤ_[l]).s (ε.e 0) * η := by
    refine cont_ext fun z => ?_
    have hev : Hom.f ((base l).evCont z) (((base l).cont ℤ_[l]).s (ε.e 0)) =
        (base l).s (ε.e 0) :=
      RingHom.congr_fun (Hom.comm ((base l).evCont z)) _
    rw [map_mul, hev]
    exact hshift z
  obtain ⟨ρ, h0, hρ⟩ := exists_roots ((base l).cont ℤ_[l]) η
  have hF := GlobalTheory.T.sharp_epsilon_root_idempotent_sum ε ρ (fun m z => h0 ▸ hη m z) hρ
  have h1 : ((base l).cont ℤ_[l]).sharp η = 1 := by
    have h := hF 0
    rw [h0] at h
    rw [h, ← sum_sharp_eq_one ((base l).cont ℤ_[l]) (coi_ind (base l) 0)]
    refine Finset.sum_congr rfl fun c _ => ?_
    have : c.val = 0 := by
      have : c.val < 1 := lt_of_lt_of_eq (ZMod.val_lt c) (pow_zero l)
      omega
    rw [this, pow_zero, mul_one]
  obtain ⟨w, rfl⟩ := RL.unit_lift ((base l).cont ℤ_[l]) η (by rw [h1]; exact isUnit_one)
  refine ⟨w, h1, hs, fun A t ht φ u hu => ?_⟩
  have := continuous_algebra_universal_existsUnique ε hρ hF A t ht φ u hu
  rwa [h0] at this

end GlobalTheory.CompanionTheory.ContUniv
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousAlgebraUniversalPropertyStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_algebra_universal_property : ∀ {l : ℕ} [Fact l.Prime] (ε : Eps l), ∃ η : (((base l).cont ℤ_[l]).A)ˣ, ((base l).cont ℤ_[l]).sharp η = 1 ∧ PAlg.Hom.f (contShift (base l)) η = ((base l).cont ℤ_[l]).s (ε.e 0) * η ∧ ∀ (A t : PAlg l), t.IsTest → ∀ (φ : A ⟶ t) (u : (t.A)ˣ), t.sharp u = 1 → ∃! ψ : A.cont ℤ_[l] ⟶ t, A.toCont ℤ_[l] ≫ ψ = φ ∧ PAlg.Hom.f ψ (PAlg.Hom.f (contMap A.fromBase ℤ_[l]) η) = u := by
  first | exact @GlobalTheory.CompanionTheory.ContUniv.main | exact GlobalTheory.CompanionTheory.ContUniv.main | (intros; apply GlobalTheory.CompanionTheory.ContUniv.main <;> assumption)
end
