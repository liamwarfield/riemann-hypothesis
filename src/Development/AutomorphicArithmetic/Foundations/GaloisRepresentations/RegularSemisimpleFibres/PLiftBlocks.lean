module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PLiftBlocks
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private lemma geo_mul (x l : ℕ) (hx : 1 ≤ x) :
    (∑ i ∈ Finset.range l, x ^ i) * (x - 1) = x ^ l - 1 := by
  obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
  have := geom_sum_mul_add y l
  simp only [Nat.add_sub_cancel]
  omega

private lemma div_id (N a b S : ℕ) (ha : 0 < a) (hS : S * a = b) (hb : b ∣ N) (hb0 : 0 < b) :
    S * (N / b) = N / a := by
  obtain ⟨c, rfl⟩ := hb
  rw [Nat.mul_div_cancel_left c hb0]
  subst hS
  rw [show S * a * c = a * (S * c) by ring, Nat.mul_div_cancel_left _ ha]

private lemma sub_one_dvd (x e : ℕ) : x - 1 ∣ x ^ e - 1 := by
  simpa using Nat.sub_dvd_pow_sub_pow x 1 e

private lemma ms_sum {α : Type*} (n : ℕ) (g : ℕ → α) :
    (Multiset.range n).map g = ∑ j ∈ Finset.range n, ({g j} : Multiset α) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Multiset.range_succ, Multiset.map_cons, Finset.sum_range_succ, ih, add_comm,
      Multiset.singleton_add]

private lemma list_sum {α : Type*} (l : ℕ) (F : ℕ → Multiset α) :
    ((List.range l).map F).sum = ∑ i ∈ Finset.range l, F i := by
  induction l with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

private lemma block_mul {α : Type*} (l m' : ℕ) (g : ℕ → α) :
    ∑ i ∈ Finset.range l, ∑ j ∈ Finset.range m', ({g (i + l * j)} : Multiset α) =
      ∑ n ∈ Finset.range (l * m'), ({g n} : Multiset α) := by
  induction m' with
  | zero => simp
  | succ m ih =>
    calc ∑ i ∈ Finset.range l, ∑ j ∈ Finset.range (m + 1), ({g (i + l * j)} : Multiset α)
        = ∑ i ∈ Finset.range l, (∑ j ∈ Finset.range m, ({g (i + l * j)} : Multiset α) +
            {g (i + l * m)}) := Finset.sum_congr rfl fun i _ => Finset.sum_range_succ _ m
      _ = ∑ i ∈ Finset.range l, ∑ j ∈ Finset.range m, ({g (i + l * j)} : Multiset α) +
            ∑ i ∈ Finset.range l, ({g (i + l * m)} : Multiset α) := Finset.sum_add_distrib
      _ = ∑ n ∈ Finset.range (l * (m + 1)), ({g n} : Multiset α) := by
          rw [ih, Nat.mul_succ, Finset.sum_range_add]
          congr 1
          exact Finset.sum_congr rfl fun i _ => by rw [Nat.add_comm]

private lemma perm_map {α : Type*} (l m : ℕ) (hc : Nat.Coprime l m) (hm : 0 < m) (G : ℕ → α)
    (hG : ∀ n, G (n + m) = G n) :
    (Multiset.range m).map (fun j => G (l * j)) = (Multiset.range m).map G := by
  have hper : Function.Periodic G m := hG
  have hinj : Set.InjOn (fun j => l * j % m) (Finset.range m : Set ℕ) := by
    intro x hx y hy hxy
    have hx' : x < m := by simpa using hx
    have hy' : y < m := by simpa using hy
    have h1 : l * x ≡ l * y [MOD m] := hxy
    have h2 : x ≡ y [MOD m] := Nat.ModEq.cancel_left_of_coprime (by rw [Nat.gcd_comm]; exact hc) h1
    exact Nat.ModEq.eq_of_lt_of_lt h2 hx' hy'
  have himg : (Finset.range m).image (fun j => l * j % m) = Finset.range m := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hx
      exact Finset.mem_range.2 (Nat.mod_lt _ hm)
    · rw [Finset.card_image_of_injOn hinj]
  rw [ms_sum, ms_sum]
  conv_rhs => rw [← himg]
  rw [Finset.sum_image hinj]
  exact Finset.sum_congr rfl fun j _ => by rw [hper.map_mod_nat]

private def lbk (Q q : ℕ) (p : ℕ × ℕ) : Multiset (ℕ × ZMod (Q - 1)) :=
  (Multiset.range p.1).map fun j =>
    ((1 : ℕ), ((p.2 * q ^ j * ((Q - 1) / (q ^ p.1 - 1)) : ℕ) : ZMod (Q - 1)))

private lemma lbk_dvd (Q q l m' k : ℕ) :
    ((List.range l).map fun i => lbk Q (q ^ l) (m', k * q ^ i)).sum = lbk Q q (l * m', k) := by
  set G : ℕ → ℕ × ZMod (Q - 1) := fun j =>
    ((1 : ℕ), ((k * q ^ j * ((Q - 1) / (q ^ (l * m') - 1)) : ℕ) : ZMod (Q - 1))) with hGdef
  have h1 : ∀ i, lbk Q (q ^ l) (m', k * q ^ i) =
      ∑ j ∈ Finset.range m', ({G (i + l * j)} : Multiset _) := by
    intro i
    rw [← ms_sum (n := m') (g := fun j => G (i + l * j))]
    unfold lbk
    refine Multiset.map_congr rfl fun j _ => ?_
    simp only [hGdef, ← pow_mul, pow_add, mul_assoc]
  have h2 : lbk Q q (l * m', k) = (Multiset.range (l * m')).map G := rfl
  rw [list_sum, h2, ms_sum, ← block_mul]
  exact Finset.sum_congr rfl fun i _ => h1 i

private lemma lbk_ndvd (Q q l f m k : ℕ) (hq : 2 ≤ q) (hl : l.Prime) (hQ : Q = (q ^ l) ^ f)
    (hm : 0 < m) (hmf : m ∣ f) (hnd : ¬ l ∣ m) :
    lbk Q (q ^ l) (m, k * ∑ i ∈ Finset.range l, q ^ (m * i)) = lbk Q q (m, k) := by
  have hqm : 1 < q ^ m := Nat.one_lt_pow hm.ne' (by omega)
  have hql : 1 < (q ^ l) ^ m := Nat.one_lt_pow hm.ne' (Nat.one_lt_pow hl.ne_zero (by omega))
  have hT : (∑ i ∈ Finset.range l, q ^ (m * i)) * (q ^ m - 1) = (q ^ l) ^ m - 1 := by
    have := geo_mul (q ^ m) l hqm.le
    simp only [← pow_mul] at this ⊢
    rw [this, Nat.mul_comm l m]
  have hd1 : (q ^ l) ^ m - 1 ∣ Q - 1 := by
    obtain ⟨e, rfl⟩ := hmf
    rw [hQ, pow_mul]
    exact sub_one_dvd _ e
  have hd2 : q ^ m - 1 ∣ Q - 1 := (Dvd.intro_left _ hT).trans hd1
  have hC := div_id (Q - 1) (q ^ m - 1) ((q ^ l) ^ m - 1) _ (by omega) hT hd1 (by omega)
  have hC2 : (Q - 1) / (q ^ m - 1) * (q ^ m - 1) = Q - 1 := Nat.div_mul_cancel hd2
  set C := (Q - 1) / (q ^ m - 1) with hCdef
  set T := ∑ i ∈ Finset.range l, q ^ (m * i) with hTdef
  set G : ℕ → ℕ × ZMod (Q - 1) := fun j => ((1 : ℕ), ((k * q ^ j * C : ℕ) : ZMod (Q - 1))) with hGdef
  have hG : ∀ n, G (n + m) = G n := by
    intro n
    obtain ⟨u, hu⟩ : ∃ u, q ^ m = u + 1 := ⟨q ^ m - 1, by omega⟩
    have hCu : C * u = Q - 1 := by rw [hu] at hC2; simpa using hC2
    have : k * q ^ (n + m) * C = k * q ^ n * C + k * q ^ n * (Q - 1) := by
      rw [pow_add, hu, ← hCu]; ring
    simp only [hGdef, this]
    push_cast [ZMod.natCast_self]
    simp [ZMod.natCast_self]
  have hL : lbk Q (q ^ l) (m, k * T) = (Multiset.range m).map fun j => G (l * j) := by
    unfold lbk
    refine Multiset.map_congr rfl fun j _ => ?_
    simp only [hGdef]
    rw [← hC, pow_mul]
    congr 2
    ring
  rw [hL, perm_map l m ((Nat.Prime.coprime_iff_not_dvd hl).2 hnd) hm G hG]
  rfl

private lemma lbkL (Q q l f : ℕ) (hq : 2 ≤ q) (hl : l.Prime) (hQ : Q = (q ^ l) ^ f) :
    ∀ L : List (ℕ × ℕ), (∀ p ∈ L, 0 < p.1) → (∀ p ∈ liftAll q l L, p.1 ∣ f) →
      ((liftAll q l L).map (lbk Q (q ^ l))).sum = (L.map (lbk Q q)).sum := by
  intro L
  induction L with
  | nil => intro _ _; simp [liftAll]
  | cons p L ih =>
    intro h0 hd
    obtain ⟨m, k⟩ := p
    have hsplit : liftAll q l ((m, k) :: L) = (if l ∣ m then liftL q l [(m, k)] else
        [(m, k * ∑ i ∈ Finset.range l, q ^ (m * i))]) ++ liftAll q l L := by
      simp [liftAll]
    rw [hsplit] at hd ⊢
    have hdL : ∀ p ∈ liftAll q l L, p.1 ∣ f := fun p hp => hd p (List.mem_append_right _ hp)
    rw [List.map_append, List.sum_append, ih (fun p hp => h0 p (List.mem_cons_of_mem _ hp)) hdL,
      List.map_cons, List.sum_cons]
    congr 1
    by_cases hlm : l ∣ m
    · obtain ⟨m', rfl⟩ := hlm
      have : liftL q l [(l * m', k)] = (List.range l).map fun i => (m', k * q ^ i) := by
        simp [liftL, Nat.mul_div_cancel_left _ hl.pos]
      rw [if_pos (dvd_mul_right _ _), this, List.map_map]
      exact lbk_dvd Q q l m' k
    · rw [if_neg hlm] at hd ⊢
      have hmf : m ∣ f := hd (m, _) (List.mem_append_left _ (List.mem_singleton.2 rfl))
      simpa using lbk_ndvd Q q l f m k hq hl hQ (h0 (m, k) List.mem_cons_self) hmf hlm

private lemma splitsL (q l f : ℕ) (hl : l.Prime) (L : List (ℕ × ℕ))
    (hd : ∀ p ∈ liftAll q l L, p.1 ∣ f) : ∀ p ∈ L, p.1 ∣ l * f := by
  rintro ⟨m, k⟩ hp
  by_cases hlm : l ∣ m
  · have h1 : (m / l, k * q ^ 0) ∈ liftAll q l L := by
      refine List.mem_flatMap.2 ⟨(m, k), hp, ?_⟩
      simp only [if_pos hlm, liftL]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      exact List.mem_map.2 ⟨0, List.mem_range.2 hl.pos, rfl⟩
    have h2 := hd _ h1
    obtain ⟨m', rfl⟩ := hlm
    rw [Nat.mul_div_cancel_left _ hl.pos] at h2
    exact Nat.mul_dvd_mul_left l h2
  · have h1 : (m, k * ∑ i ∈ Finset.range l, q ^ (m * i)) ∈ liftAll q l L := by
      refine List.mem_flatMap.2 ⟨(m, k), hp, ?_⟩
      simp [if_neg hlm]
    exact (hd _ h1).mul_left l

theorem UpperTheory.Gal.InertialTypesAlt.liftBlocks :
    LiftBlocks := by
  intro a l Q hl ha hs
  obtain ⟨q, D, L⟩ := a
  obtain ⟨hq, hD, hL⟩ := ha
  obtain ⟨f, hf, hQ, hdiv⟩ := hs
  have hq' : 2 ≤ q := hq
  have hQ' : Q = (q ^ l) ^ f := hQ
  have hdiv' : ∀ p ∈ liftAll q l L, p.1 ∣ f := hdiv
  have hL0 : ∀ p ∈ L, 0 < p.1 := fun p hp => (hL p hp).1
  refine ⟨⟨l * f, Nat.mul_pos hl.pos hf, by rw [hQ', pow_mul], splitsL q l f hl L hdiv'⟩, ?_⟩
  have hS := geo_mul q l (by omega)
  have hql : 1 < q ^ l := Nat.one_lt_pow hl.ne_zero (by omega)
  have hDid : (∑ i ∈ Finset.range l, q ^ i) * ((Q - 1) / (q ^ l - 1)) = (Q - 1) / (q - 1) :=
    div_id (Q - 1) (q - 1) (q ^ l - 1) _ (by omega) hS (by rw [hQ']; exact sub_one_dvd _ f) (by omega)
  have hDpart : ((⟨q, D, L⟩ : Lbl).lift l).D.map (fun p =>
        (p.1, ((p.2 * ((Q - 1) / (((⟨q, D, L⟩ : Lbl).lift l).q - 1)) : ℕ) : ZMod (Q - 1)))) =
      D.map (fun p => (p.1, ((p.2 * ((Q - 1) / (q - 1)) : ℕ) : ZMod (Q - 1)))) := by
    show (D.map _).map _ = _
    rw [List.map_map]
    refine List.map_congr_left fun p _ => ?_
    simp only [Function.comp]
    rw [← hDid, mul_assoc]
    rfl
  have hLpart := lbkL Q q l f hq' hl hQ' L hL0 hdiv'
  unfold Lbl.blocks
  rw [hDpart]
  congr 1
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PNameOf
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem natCard_of_finrank {g : ℕ} [Fact g.Prime] {m : ℕ} (hm : 0 < m) {K : Type} [Field K] [Algebra (ZMod g) K]
    (hK : Module.finrank (ZMod g) K = m) : Nat.card K = g ^ m := by
  haveI : Module.Finite (ZMod g) K := Module.finite_of_finrank_pos (hK ▸ hm)
  haveI : Finite K := Module.finite_of_finite (ZMod g)
  haveI : Fintype K := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod g), ZMod.card, hK]

private theorem frob_top {g : ℕ} [Fact g.Prime] {m : ℕ} (hm : 0 < m) {K : Type} [Field K] [Algebra (ZMod g) K]
    (hK : Module.finrank (ZMod g) K = m) (x : K) : x ^ g ^ m = x := by
  haveI : Module.Finite (ZMod g) K := Module.finite_of_finrank_pos (hK ▸ hm)
  haveI : Finite K := Module.finite_of_finite (ZMod g)
  haveI : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = g ^ m := by
    rw [← Nat.card_eq_fintype_card]
    exact natCard_of_finrank hm hK
  rw [← hc]
  exact FiniteField.pow_card x

private theorem aeval_pow_prime_pow_eq_pow {g : ℕ} [Fact g.Prime] {K : Type} [Field K] [Algebra (ZMod g) K]
    (Y : (ZMod g)[X]) (x : K) (j : ℕ) : aeval (x ^ g ^ j) Y = (aeval x Y) ^ g ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, pow_mul, pow_mul, ← ih, ← Polynomial.expand_aeval, ZMod.expand_card, map_pow]

private theorem conj_ne {g : ℕ} [Fact g.Prime] {m : ℕ} (hm : 0 < m) {K : Type} [Field K] [Algebra (ZMod g) K]
    (hK : Module.finrank (ZMod g) K = m) (z : Kˣ) (hz : (minpoly (ZMod g) (z : K)).natDegree = m)
    (a : ℕ) (ha : 0 < a) (ham : a < m) : (z : K) ^ g ^ a ≠ z := by
  intro h
  classical
  have hg : g.Prime := Fact.out
  haveI : Module.Finite (ZMod g) K := Module.finite_of_finrank_pos (hK ▸ hm)
  haveI : Finite K := Module.finite_of_finite (ZMod g)
  haveI : Fintype K := Fintype.ofFinite K
  have hint : IsIntegral (ZMod g) (z : K) := Algebra.IsIntegral.isIntegral _
  set F := IntermediateField.adjoin (ZMod g) {(z : K)} with hFdef
  have hF : Module.finrank (ZMod g) F = m := by
    rw [IntermediateField.adjoin.finrank hint, hz]
  have hfix : ∀ y ∈ F, y ^ g ^ a = y := by
    intro y hy
    have hy' : y ∈ Algebra.adjoin (ZMod g) {(z : K)} := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
      exact hy
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hy'
    obtain ⟨p, rfl⟩ := hy'
    show (aeval (z : K) p) ^ g ^ a = aeval (z : K) p
    rw [← aeval_pow_prime_pow_eq_pow, h]
  have hq : 1 < g ^ a := Nat.one_lt_pow ha.ne' hg.one_lt
  have hP0 : (X ^ (g ^ a) - X : K[X]) ≠ 0 := Polynomial.X_pow_sub_X_ne_zero hq
  have hle := Polynomial.card_le_degree_of_subset_roots (p := (X ^ (g ^ a) - X : K[X]))
    (Z := Finset.univ.map (Function.Embedding.subtype (· ∈ F))) (by
      intro y hy
      rw [Finset.map_val, Multiset.mem_map] at hy
      obtain ⟨⟨y, hyF⟩, -, rfl⟩ := hy
      rw [Polynomial.mem_roots hP0, IsRoot, eval_sub, eval_pow, eval_X]
      simp only [Function.Embedding.coe_subtype]
      rw [hfix y hyF, sub_self])
  rw [Polynomial.natDegree_X_pow_sub_X (R := K) hq, Finset.card_map, Finset.card_univ,
    Module.card_eq_pow_finrank (K := ZMod g), ZMod.card, hF] at hle
  have := Nat.pow_lt_pow_right hg.one_lt ham
  omega

private theorem conj_inj {g : ℕ} [Fact g.Prime] {m : ℕ} (hm : 0 < m) {K : Type} [Field K] [Algebra (ZMod g) K]
    (hK : Module.finrank (ZMod g) K = m) (z : Kˣ) (hz : (minpoly (ZMod g) (z : K)).natDegree = m)
    (i j : ℕ) (hij : i < j) (hj : j < m) : (z : K) ^ g ^ i ≠ (z : K) ^ g ^ j := by
  intro h
  have key : ∀ x : K, (x ^ g ^ i) ^ g ^ (m - i) = x := by
    intro x
    rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' (by omega)]
    exact frob_top hm hK x
  apply conj_ne hm hK z hz (j - i) (by omega) (by omega)
  have hs : (z : K) ^ g ^ j = ((z : K) ^ g ^ (j - i)) ^ g ^ i := by
    rw [← pow_mul, ← pow_add, Nat.sub_add_cancel hij.le]
  rw [hs] at h
  have h2 := congrArg (fun y => y ^ g ^ (m - i)) h
  simp only [key] at h2
  exact h2.symm

private theorem aeval_conj {g : ℕ} [Fact g.Prime] {K : Type} [Field K] [Algebra (ZMod g) K]
    (Y : (ZMod g)[X]) (x : K) (hx : aeval x Y = 0) (j : ℕ) : aeval (x ^ g ^ j) Y = 0 := by
  rw [aeval_pow_prime_pow_eq_pow, hx, zero_pow (pow_ne_zero _ (Fact.out : g.Prime).ne_zero)]

private theorem roots_conj {g : ℕ} [Fact g.Prime] {m : ℕ} (hm : 0 < m) {K : Type} [Field K] [Algebra (ZMod g) K]
    (hK : Module.finrank (ZMod g) K = m) (Y : (ZMod g)[X]) (hY : Irreducible Y) (hYm : Y.Monic)
    (hYd : Y.natDegree = m) (z : Kˣ) (hz : aeval (z : K) Y = 0) {L : Type} [Field L] (ι : K →+* L) :
    ((Y.map (algebraMap (ZMod g) K)).map ι).roots = (Multiset.range m).map fun j => ι ((z : K) ^ g ^ j) := by
  have hzm : (minpoly (ZMod g) (z : K)).natDegree = m := by
    rw [← minpoly.eq_of_irreducible_of_monic hY hz hYm, hYd]
  have hnd : ((Multiset.range m).map fun j => ι ((z : K) ^ g ^ j)).Nodup := by
    rw [Multiset.nodup_map_iff_inj_on (Multiset.nodup_range m)]
    intro i hi j hj hij
    simp only [Multiset.mem_range] at hi hj
    have h' : (z : K) ^ g ^ i = (z : K) ^ g ^ j := ι.injective hij
    rcases lt_trichotomy i j with h | h | h
    · exact absurd h' (conj_inj hm hK z hzm i j h hj)
    · exact h
    · exact absurd h'.symm (conj_inj hm hK z hzm j i h hi)
  have hP0 : ((Y.map (algebraMap (ZMod g) K)).map ι) ≠ 0 := ((hYm.map _).map _).ne_zero
  have hle : ((Multiset.range m).map fun j => ι ((z : K) ^ g ^ j)) ≤
      ((Y.map (algebraMap (ZMod g) K)).map ι).roots := by
    rw [Multiset.le_iff_subset hnd]
    intro y hy
    rw [Multiset.mem_map] at hy
    obtain ⟨j, -, rfl⟩ := hy
    rw [mem_roots hP0, IsRoot, eval_map, eval₂_map, ← Polynomial.hom_eval₂, ← aeval_def,
      aeval_conj Y _ hz j, map_zero]
  have hdeg : ((Y.map (algebraMap (ZMod g) K)).map ι).natDegree = m := by
    rw [natDegree_map, natDegree_map, hYd]
  refine (Multiset.eq_of_le_of_card_le hle ?_).symm
  rw [Multiset.card_map, Multiset.card_range, ← hdeg]
  exact card_roots' _

private theorem false_of_reg_of_mul_pow_modEq {g m c i j : ℕ} (hg : 0 < g) (hc : Reg g m c) (hij : i < j) (hj : j < m)
    (h : c * g ^ i ≡ c * g ^ j [MOD g ^ m - 1]) : False := by
  have hone : g ^ m ≡ 1 [MOD g ^ m - 1] := Nat.modEq_sub (Nat.one_le_pow _ _ hg)
  have h2 := h.mul_right (g ^ (m - i))
  have e1 : c * g ^ i * g ^ (m - i) = c * g ^ m := by
    rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' (by omega)]
  have e2 : c * g ^ j * g ^ (m - i) = c * g ^ (j - i) * g ^ m := by
    rw [mul_assoc, mul_assoc, ← pow_add, ← pow_add]
    congr 2
    omega
  rw [e1, e2] at h2
  have h3 : c * g ^ m ≡ c [MOD g ^ m - 1] := by simpa using hone.mul_left c
  have h4 : c * g ^ (j - i) * g ^ m ≡ c * g ^ (j - i) [MOD g ^ m - 1] := by
    simpa using hone.mul_left (c * g ^ (j - i))
  exact hc (j - i) (by omega) (by omega) (h4.symm.trans (h2.symm.trans h3))

private theorem regular_character_of_pow {g : ℕ} [Fact g.Prime] {m : ℕ} (hm : 0 < m) {K 𝔨 : Type} [Field K] [Algebra (ZMod g) K] [Field 𝔨]
    (hK : Module.finrank (ZMod g) K = m) (ι : K →+* 𝔨) (Θ : 𝔨 →* ℂ) (hΘ : Inj Θ) (c : ℕ) (hc : Reg g m c) :
    GlobalTheory.Published.IsRegularChar g m ((Units.map (Θ.comp ι.toMonoidHom)) ^ c : Kˣ →* ℂˣ) := by
  intro i j hi hj hij
  have hg : g.Prime := Fact.out
  haveI : Module.Finite (ZMod g) K := Module.finite_of_finrank_pos (hK ▸ hm)
  haveI : Finite K := Module.finite_of_finite (ZMod g)
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf ζ = g ^ m - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hζ, Nat.card_eq_fintype_card, Fintype.card_units,
      ← Nat.card_eq_fintype_card, natCard_of_finrank hm hK]
  have hv := DFunLike.congr_fun hij ζ
  simp only [MonoidHom.pow_apply, ← pow_mul] at hv
  rw [← map_pow, ← map_pow] at hv
  have hv' : Θ (ι ((ζ ^ (c * g ^ i) : Kˣ) : K)) = Θ (ι ((ζ ^ (c * g ^ j) : Kˣ) : K)) :=
    congrArg (fun u : ℂˣ => (u : ℂ)) hv
  have h1 := hΘ _ _ (by simp) (by simp) hv'
  have h2 : ζ ^ (c * g ^ i) = ζ ^ (c * g ^ j) := Units.ext (ι.injective h1)
  rw [pow_eq_pow_iff_modEq, hord] at h2
  rcases lt_trichotomy i j with h | h | h
  · exact (false_of_reg_of_mul_pow_modEq hg.pos hc h hj h2).elim
  · exact h
  · exact (false_of_reg_of_mul_pow_modEq hg.pos hc h hi h2.symm).elim

theorem UpperTheory.Gal.InertialTypesAlt.nameOf :
    NameOf := by
  intro g _ m hm F K 𝔨 _ _ _ _ _ hK r e ι Θ hΘ c hc
  refine ⟨(Units.map (Θ.comp ι.toMonoidHom)) ^ c, ?_, regular_character_of_pow hm hK ι Θ hΘ c hc, ?_⟩
  · intro u
    rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val]
    rfl
  · intro τ hτ y hy z hz
    set Y : (ZMod g)[X] := (y : Matrix (Fin m) (Fin m) (ZMod g)).charpoly with hYdef
    have hYm : Y.Monic := Matrix.charpoly_monic _
    have hYd : Y.natDegree = m := by
      rw [hYdef, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
    let γ : GL (Fin m) F := Matrix.GeneralLinearGroup.map r.symm.toRingHom y
    have hyγ : Matrix.GeneralLinearGroup.map r.toRingHom γ = y := by
      ext i j
      simp [γ]
    have hγc : (γ : Matrix (Fin m) (Fin m) F).charpoly = Y.map r.symm.toRingHom := by
      rw [show (γ : Matrix (Fin m) (Fin m) F) = (y : Matrix (Fin m) (Fin m) (ZMod g)).map r.symm.toRingHom
        from rfl, Matrix.charpoly_map]
    have hirr : Irreducible (LinearMap.charpoly (Matrix.toLin' (γ : Matrix (Fin m) (Fin m) F))) := by
      rw [Matrix.charpoly_toLin', hγc]
      exact (MulEquiv.irreducible_iff (Polynomial.mapEquiv r.symm)).mpr hy
    rw [← hyγ, hτ γ]
    delta cusp psiG
    congr 1
    refine (GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_of_irreducible F (Fin m → F) _ (GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow F (Θ.comp e) c).1 _ hirr).trans ?_
    rw [Matrix.charpoly_toLin', hγc]
    delta GlobalTheory.CuspGL.rootSum
    rw [Polynomial.map_map]
    have hP : (Y.map ((algebraMap F (AlgebraicClosure F)).comp r.symm.toRingHom)).Splits :=
      IsAlgClosed.splits _
    have hroots : (Y.map ((algebraMap F (AlgebraicClosure F)).comp r.symm.toRingHom)).roots.map e =
        ((Y.map (algebraMap (ZMod g) K)).map ι).roots := by
      rw [← hP.roots_map e, Polynomial.map_map, Polynomial.map_map]
      congr 2
      exact Subsingleton.elim _ _
    have hre : ((Y.map ((algebraMap F (AlgebraicClosure F)).comp r.symm.toRingHom)).roots.map
        fun α => (Θ.comp e) α ^ c) =
        (((Y.map ((algebraMap F (AlgebraicClosure F)).comp r.symm.toRingHom)).roots.map e).map
        fun β => Θ β ^ c) := by
      rw [Multiset.map_map]
      rfl
    rw [hre, hroots, roots_conj hm hK Y hy hYm hYd z hz ι, Multiset.map_map,
      Finset.sum_eq_multiset_sum, Finset.range_val]
    apply congrArg
    apply Multiset.map_congr rfl
    intro j _
    simp only [Function.comp_apply]
    rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, Units.coe_map, Units.val_pow_eq_pow_val]
    rfl
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PCuspIso
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Semi

variable {F F' : Type} [Field F] [Field F'] (r : F ≃+* F')
  {V V' : Type} [AddCommGroup V] [Module F V] [AddCommGroup V'] [Module F' V']
  (e : V ≃+ V') (he : ∀ (c : F) (x : V), e (c • x) = r c • e x)

include he in
private theorem symm_smul (c : F') (y : V') : e.symm (c • y) = r.symm c • e.symm y := by
  apply e.injective
  rw [he]
  simp

private def smap (W : Submodule F V) : Submodule F' V' where
  carrier := e '' W
  add_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, W.add_mem ha hb, map_add e a b⟩
  zero_mem' := ⟨0, W.zero_mem, map_zero e⟩
  smul_mem' := by
    rintro c _ ⟨a, ha, rfl⟩
    exact ⟨r.symm c • a, W.smul_mem _ ha, by rw [he]; simp⟩

private def scomap (W : Submodule F' V') : Submodule F V where
  carrier := e ⁻¹' W
  add_mem' := by
    intro a b ha hb
    simpa using W.add_mem ha hb
  zero_mem' := by simp
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_preimage, SetLike.mem_coe, he] at ha ⊢
    exact W.smul_mem _ ha

private theorem mem_smap {W : Submodule F V} {y : V'} : y ∈ smap r e he W ↔ e.symm y ∈ W := by
  change y ∈ e '' (W : Set V) ↔ _
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa using ha
  · intro h
    exact ⟨e.symm y, h, by simp⟩

private def smapE : Submodule F V ≃ Submodule F' V' where
  toFun := smap r e he
  invFun := scomap r e he
  left_inv W := by
    ext x
    change e x ∈ smap r e he W ↔ _
    rw [mem_smap]
    simp
  right_inv W := by
    ext y
    rw [mem_smap]
    change e (e.symm y) ∈ W ↔ _
    simp

private def eRes (W : Submodule F V) : W ≃+ smap r e he W where
  toFun x := ⟨e x, (mem_smap r e he).2 (by simp)⟩
  invFun y := ⟨e.symm y, (mem_smap r e he).1 y.2⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  map_add' x y := by ext; simp

include he in
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
  UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Pr.IsCD.fin
  UpperTheory.V.Alg.IsCO.toIsLocalRing UpperTheory.V.Alg.IsCO.complete
  UpperTheory.V.Alg.IsCO.isLocalHom UpperTheory.V.Alg.IsCO.self in
private theorem charpoly_semi [FiniteDimensional F V] [FiniteDimensional F' V']
    (g : Module.End F V) (g' : Module.End F' V') (hg : ∀ x, e (g x) = g' (e x)) :
    LinearMap.charpoly g' = (LinearMap.charpoly g).map r.toRingHom := by
  classical
  let b := Module.finBasis F V
  have hf : ∀ f : Fin (Module.finrank F V) →₀ F,
      Finsupp.mapRange r.symm (map_zero r.symm) (Finsupp.mapRange r (map_zero r) f) = f := by
    intro f
    ext i
    simp
  let repr' : V' ≃ₗ[F'] (Fin (Module.finrank F V) →₀ F') :=
    { toFun := fun y => Finsupp.mapRange r (map_zero r) (b.repr (e.symm y))
      invFun := fun c => e (b.repr.symm (Finsupp.mapRange r.symm (map_zero r.symm) c))
      map_add' := by
        intro x y
        ext i
        simp
      map_smul' := by
        intro c y
        ext i
        simp [symm_smul r e he]
      left_inv := by
        intro y
        show e (b.repr.symm (Finsupp.mapRange r.symm _ (Finsupp.mapRange r _ (b.repr (e.symm y))))) = y
        rw [hf]
        simp
      right_inv := by
        intro c
        ext i
        simp }
  let b' : Module.Basis (Fin (Module.finrank F V)) F' V' := Module.Basis.ofRepr repr'
  have hb' : ∀ j, b' j = e (b j) := by
    intro j
    simp [b', repr']
  rw [← LinearMap.charpoly_toMatrix g b, ← LinearMap.charpoly_toMatrix g' b', ← Matrix.charpoly_map]
  congr 1
  ext i j
  rw [Matrix.map_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, hb', ← hg]
  show (Finsupp.mapRange r (map_zero r) (b.repr (e.symm (e (g (b j)))))) i = _
  simp

end Semi

private theorem semilinear_equiv_conjugate_endomorphism {F F' : Type} [Field F] [Field F'] (r : F ≃+* F') (s : F[X] → ℂ) (s' : F'[X] → ℂ)
    (hs : ∀ P, s' (P.map r.toRingHom) = s P) (n : ℕ) :
    ∀ (V V' : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] [AddCommGroup V'] [Module F' V']
      [FiniteDimensional F' V'] (e : V ≃+ V') (_ : ∀ (c : F) (x : V), e (c • x) = r c • e x)
      (g : Module.End F V) (g' : Module.End F' V'), (∀ x, e (g x) = g' (e x)) →
      GlobalTheory.CuspGL.invariantSubspaceMobiusInverseRec s' n V' g' = GlobalTheory.CuspGL.invariantSubspaceMobiusInverseRec s n V g := by
  induction n with
  | zero =>
    intro V V' _ _ _ _ _ _ e he g g' hg
    rfl
  | succ n ih =>
    intro V V' _ _ _ _ _ _ e he g g' hg
    rw [GlobalTheory.CuspGL.invariantSubspaceMobiusInverseRec_succ, GlobalTheory.CuspGL.invariantSubspaceMobiusInverseRec_succ, charpoly_semi r e he g g' hg, hs]
    congr 1
    have htop : smapE r e he ⊤ = ⊤ := by
      ext y
      change y ∈ smap r e he ⊤ ↔ _
      rw [mem_smap]
      simp
    have hsymm : ∀ y, e.symm (g' y) = g (e.symm y) := by
      intro y
      apply e.injective
      rw [hg]
      simp
    have hiff : ∀ W : Submodule F V, (W ≠ ⊤ ∧ ∀ x ∈ W, g x ∈ W) ↔
        (smapE r e he W ≠ ⊤ ∧ ∀ y ∈ smapE r e he W, g' y ∈ smapE r e he W) := by
      intro W
      constructor
      · rintro ⟨hW, hinv⟩
        refine ⟨?_, ?_⟩
        · intro h
          apply hW
          apply (smapE r e he).injective
          rw [h, htop]
        · intro y hy
          change g' y ∈ smap r e he W
          change y ∈ smap r e he W at hy
          rw [mem_smap] at hy ⊢
          rw [hsymm]
          exact hinv _ hy
      · rintro ⟨hW, hinv⟩
        refine ⟨?_, ?_⟩
        · rintro rfl
          exact hW htop
        · intro x hx
          have h1 : e x ∈ smap r e he W := by
            rw [mem_smap]
            simpa using hx
          have h2 := hinv (e x) h1
          change g' (e x) ∈ smap r e he W at h2
          rw [mem_smap, hsymm] at h2
          simpa using h2
    symm
    apply finsum_eq_of_bijective ((smapE r e he).subtypeEquiv hiff) (Equiv.bijective _)
    intro W
    symm
    exact ih _ _ (eRes r e he W.1)
      (by
        intro c x
        apply Subtype.ext
        simp [eRes, he])
      _ _
      (by
        intro x
        apply Subtype.ext
        simp [eRes, hg]
        rfl)

private theorem rootSum_iso {F F' : Type} [Field F] [Field F'] (r : F ≃+* F')
    (j : AlgebraicClosure F ≃+* AlgebraicClosure F')
    (hj : ∀ x, j (algebraMap _ _ x) = algebraMap _ _ (r x)) (θ : AlgebraicClosure F' →* ℂ) (c : ℕ) (P : F[X]) :
    GlobalTheory.CuspGL.rootSum θ c (P.map r.toRingHom) = GlobalTheory.CuspGL.rootSum (θ.comp j.toMonoidHom) c P := by
  unfold GlobalTheory.CuspGL.rootSum
  have hpoly : (P.map r.toRingHom).map (algebraMap F' (AlgebraicClosure F')) =
      (P.map (algebraMap F (AlgebraicClosure F))).map j.toRingHom := by
    rw [Polynomial.map_map, Polynomial.map_map]
    congr 1
    ext x
    exact (hj x).symm
  rw [hpoly, ← roots_map_of_injective_of_card_eq_natDegree j.injective IsAlgClosed.card_roots_eq_natDegree,
    Multiset.map_map]
  rfl

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
  UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Pr.IsCD.fin
  UpperTheory.V.Alg.IsCO.toIsLocalRing UpperTheory.V.Alg.IsCO.complete
  UpperTheory.V.Alg.IsCO.isLocalHom UpperTheory.V.Alg.IsCO.self in
theorem UpperTheory.Gal.InertialTypesAlt.cuspIso :
    CuspIso := by
  intro F F' _ _ _ r j hj θ m c g
  unfold cusp psiG GlobalTheory.CuspGL.psi
  congr 1
  rw [Module.finrank_fin_fun, Module.finrank_fin_fun]
  apply semilinear_equiv_conjugate_endomorphism r (GlobalTheory.CuspGL.rootSum (θ.comp j.toMonoidHom) c) (GlobalTheory.CuspGL.rootSum θ c)
    (rootSum_iso r j hj θ c) (m + 1) (Fin m → F) (Fin m → F') (AddEquiv.piCongrRight fun _ => r.toAddEquiv)
  · intro a x
    funext i
    simp
  · intro x
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, map_sum, map_mul]
end
