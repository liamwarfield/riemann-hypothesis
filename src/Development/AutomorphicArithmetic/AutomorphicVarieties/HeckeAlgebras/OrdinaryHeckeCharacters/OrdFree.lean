module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsSquareSqSubFourIffIsSquareUnit

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsFiniteIwahoriDoubleCosetRepresentatives
open IsLocalRing Matrix UpperTheory.V.Hi

private def repsRel {Γ Ga Gp : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) (U : Subgroup X.Ub)
    (c : ℕ) : Setoid (Ga × Gp) where
  r g h := ∃ γ, ∃ u ∈ U, ∃ b ∈ X.I.Iw c, g = X.glob γ * h * ((u : Ga), b)
  iseqv :=
    { refl := fun g => ⟨1, 1, one_mem _, 1, one_mem _, by simp [Prod.mk_one_one]⟩
      symm := by
        rintro g h ⟨γ, u, hu, b, hb, rfl⟩
        refine ⟨γ⁻¹, u⁻¹, inv_mem hu, b⁻¹, inv_mem hb, ?_⟩
        have : (((u⁻¹ : X.Ub) : Ga), b⁻¹) = ((u : Ga), b)⁻¹ := rfl
        rw [this, map_inv]
        group
      trans := by
        rintro g h k ⟨γ, u, hu, b, hb, rfl⟩ ⟨γ', u', hu', b', hb', rfl⟩
        refine ⟨γ * γ', u' * u, mul_mem hu' hu, b' * b, mul_mem hb' hb, ?_⟩
        have : (((u' * u : X.Ub) : Ga), b' * b) = ((u' : Ga), b') * ((u : Ga), b) := rfl
        rw [this, map_mul]
        group }

theorem UpperTheory.exists_finite_iwahori_doubleCoset_representatives :
    ∀ (Γ Ga Gp : Type) [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) (U : Subgroup X.Ub), X.FinLevel U → ∀ c : ℕ, ∃ (N : ℕ) (x : Fin N → Ga × Gp), (∀ g, ∃ γ i, ∃ u ∈ U, ∃ b ∈ X.I.Iw c, g = X.glob γ * x i * ((u : Ga), b)) ∧ (∀ i j γ, ∀ u ∈ U, ∀ b ∈ X.I.Iw c, x j = X.glob γ * x i * ((u : Ga), b) → i = j) := by
  intro Γ Ga Gp _ _ _ X U hU c
  obtain ⟨s, hs⟩ := hU
  haveI : Finite (X.I.Iw 0 ⧸ (X.I.Iw c).subgroupOf (X.I.Iw 0)) := Nat.finite_of_card_ne_zero (iwFin Gp X.I c).1
  haveI : Finite (Quotient (repsRel X U c)) := by
    refine Finite.of_surjective
      (fun p : s × (X.I.Iw 0 ⧸ (X.I.Iw c).subgroupOf (X.I.Iw 0)) =>
        Quotient.mk (repsRel X U c) ((p.1 : Ga × Gp) * (1, (p.2.out : Gp)))) ?_
    intro q
    induction q using Quotient.inductionOn with
    | h g =>
      obtain ⟨γ, x, hx, u, hu, b, hb, rfl⟩ := hs g
      obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul ((X.I.Iw c).subgroupOf (X.I.Iw 0)) ⟨b, hb⟩
      refine ⟨(⟨x, hx⟩, ((⟨b, hb⟩ : X.I.Iw 0) : _ ⧸ _)), ?_⟩
      symm
      refine Quotient.sound ⟨γ, u, hu, ((m : X.I.Iw 0) : Gp)⁻¹, inv_mem (Subgroup.mem_subgroupOf.1 m.2), ?_⟩
      simp only [hm, Subgroup.coe_mul, mul_assoc, Prod.mk_mul_mk, one_mul, mul_inv_cancel, mul_one]
  obtain ⟨N, ⟨e⟩⟩ := Finite.exists_equiv_fin (Quotient (repsRel X U c))
  refine ⟨N, fun i => (e.symm i).out, fun g => ?_, fun i j γ u hu b hb h => ?_⟩
  · obtain ⟨γ, u, hu, b, hb, h⟩ := (repsRel X U c).symm (Quotient.mk_out (s := repsRel X U c) g)
    exact ⟨γ, e (Quotient.mk _ g), u, hu, b, hb, by simpa using h⟩
  · have h1 : Quotient.mk (repsRel X U c) (e.symm j).out = Quotient.mk (repsRel X U c) (e.symm i).out :=
      Quotient.sound ⟨γ, u, hu, b, hb, h⟩
    rw [Quotient.out_eq, Quotient.out_eq] at h1
    exact (e.symm.injective h1).symm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MemValInOfInvariantAndValuesMemPow
open IsLocalRing Matrix UpperTheory.V.Hi

theorem UpperTheory.mem_valIn_of_invariant_and_values_mem_pow :
    ∀ (Γ Ga Gp : Type) [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) (A : Type) [CommRing A] [IsCNL A] (m : ℕ) (τ : X.Ub →* GL (Fin m) A) (θ : X.I.T →* Aˣ) (U : Subgroup X.Ub) (k c N : ℕ) (x : Fin N → Ga × Gp), (∀ g, ∃ γ i, ∃ u ∈ U, ∃ b ∈ X.I.Iw c, g = X.glob γ * x i * ((u : Ga), b)) → ∀ f ∈ X.Sp τ θ U, (∀ y ∈ X.I.Nm c, X.rp A m y f - f ∈ X.valIn A m k) → (∀ i j, f (x i) j ∈ maximalIdeal A ^ k) → f ∈ X.valIn A m k := by
  intro Γ Ga Gp _ _ _ X A _ _ m τ θ U k c N x hx f hf hy h0
  have hv : ∀ F : X.Fn A m, F ∈ X.valIn A m k ↔ ∀ g i, F g i ∈ maximalIdeal A ^ k := fun F => by
    simp [Frame.valIn, Submodule.mem_pi]
  have hrp : ∀ (b : Gp) (g : Ga × Gp), X.rp A m b f g = f (g * (1, b)) := fun _ _ => rfl
  obtain ⟨⟨h1, h2, h3, -⟩, h4⟩ := hf
  rw [hv]
  intro g
  obtain ⟨γ, i, u, hu, b, hb, rfl⟩ := hx g
  obtain ⟨n, hn, t, ht, y, hy', rfl⟩ := (iwMem Gp X.I c b).1.1 hb
  have a1 : ∀ j, f (x i * ((u : Ga), 1)) j ∈ maximalIdeal A ^ k := by
    intro j
    have e := congrFun (h4 u⁻¹ (inv_mem hu)) (x i * ((u : Ga), 1))
    rw [Frame.ra_apply] at e
    have e2 : x i * ((u : Ga), (1 : Gp)) * (((u⁻¹ : X.Ub) : Ga), (1 : Gp)) = x i := by
      ext <;> simp
    rw [← e, e2]
    simp only [mulVec, dotProduct]
    exact Submodule.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (h0 _ l)
  have a2 : ∀ j, f (x i * ((u : Ga), 1) * (1, n)) j ∈ maximalIdeal A ^ k := by
    intro j
    rw [← hrp, h2 n hn]
    exact a1 j
  have a3 : ∀ j, f (x i * ((u : Ga), 1) * (1, n) * (1, t)) j ∈ maximalIdeal A ^ k := by
    intro j
    rw [← hrp, h3 ⟨t, ht⟩]
    exact Ideal.mul_mem_left _ _ (a2 j)
  intro j
  have a4 := add_mem ((hv _).1 (hy y hy') (x i * ((u : Ga), 1) * (1, n) * (1, t)) j) (a3 j)
  rw [Pi.sub_apply, Pi.sub_apply, sub_add_cancel, hrp] at a4
  rw [mul_assoc, h1]
  convert a4 using 2
  ext <;> simp [mul_assoc]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.UOperatorPowEventuallyInvariantModPow
open IsLocalRing Matrix UpperTheory.V.Hi

private theorem lower_one {G : Type} [Group G] (I : Iwa G) {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (π : Representation A G M) (c d : ℕ) (hcd : c ≤ d) (v : M) (hN : v ∈ fixd π I.N) (hT : v ∈ fixd π (I.Tc c))
    (hm : v ∈ fixd π (I.Nm (d + 1))) :
    I.uOp π I.z v ∈ fixd π I.N ∧ I.uOp π I.z v ∈ fixd π (I.Tc c) ∧ I.uOp π I.z v ∈ fixd π (I.Nm d) := by
  obtain ⟨h1, -, -, h2, -⟩ := uOpMul G I A M π I.z I.z I.z_mem I.z_mem v hN
  refine ⟨h1, fun t ht => by rw [h2 t (I.Tc_le c ht), hT t ht], fun y hy => ?_⟩
  exact (uOpLevel G I A M π d).2.1 v hN (fun t ht => hT t (I.Tc_anti hcd ht)) hm y (Subgroup.mem_sup_right hy)

private theorem lower_many {G : Type} [Group G] (I : Iwa G) {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (π : Representation A G M) (c n : ℕ) : ∀ v : M, v ∈ fixd π I.N → v ∈ fixd π (I.Tc c) →
      v ∈ fixd π (I.Nm (c + n)) → (I.uOp π I.z ^ n) v ∈ fixd π (I.Nm c) := by
  induction n with
  | zero => exact fun v _ _ hm => by simpa using hm
  | succ n ih =>
    intro v hN hT hm
    obtain ⟨h1, h2, h3⟩ := lower_one I π c (c + n) (Nat.le_add_right c n) v hN hT hm
    rw [pow_succ, Module.End.mul_apply]
    exact ih _ h1 h2 h3

theorem UpperTheory.uOperator_pow_eventually_invariant_mod_pow :
    ∀ (Γ Ga Gp : Type) [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) (A : Type) [CommRing A] [IsCNL A] (m : ℕ) (θ : X.I.T →* Aˣ), X.I.ContChar θ → ∀ f ∈ X.Amb m θ, ∀ k c : ℕ, (∀ t : X.I.T, (t : Gp) ∈ X.I.Tc c → (θ t : A) - 1 ∈ maximalIdeal A ^ k) → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ y ∈ X.I.Nm c, X.rp A m y ((X.U A m X.I.z ^ n) f) - (X.U A m X.I.z ^ n) f ∈ X.valIn A m k := by
  intro Γ Ga Gp _ _ _ X A _ _ m θ _ f hf k c hc
  obtain ⟨-, h2, h3, h4⟩ := hf
  obtain ⟨c1, hc1⟩ := h4 k
  refine ⟨c1, fun n hn y hy => ?_⟩
  let φ : X.Fn A m →ₗ[A] X.Fn (A ⧸ maximalIdeal A ^ k) m := X.mapFn
  have hφ : ∀ f g i, φ f g i = Ideal.Quotient.mk _ (f g i) := fun _ _ _ => rfl
  have hnat : ∀ b f, φ (X.rp A m b f) = X.rp _ m b (φ f) := fun _ _ => rfl
  have hN : φ f ∈ fixd (X.rp (A ⧸ maximalIdeal A ^ k) m) X.I.N := fun x hx => by rw [← hnat, h2 x hx]
  have hT : φ f ∈ fixd (X.rp (A ⧸ maximalIdeal A ^ k) m) (X.I.Tc c) := fun t ht => by
    have ht' := X.I.Tc_le _ ht
    have := hc ⟨t, ht'⟩⁻¹ (inv_mem ht)
    rw [← hnat, h3 ⟨t, ht'⟩]
    funext g i
    rw [hφ, hφ, Ideal.Quotient.eq]
    have h6 := Ideal.mul_mem_right (f g i) _ this
    rw [map_inv] at h6
    convert h6 using 1
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hm : φ f ∈ fixd (X.rp (A ⧸ maximalIdeal A ^ k) m) (X.I.Nm (c + n)) := fun w hw => by
    rw [← hnat]
    funext g i
    rw [hφ, hφ, Ideal.Quotient.eq]
    exact hc1 w (X.I.Nm_anti (by omega) hw) g i
  have hpow : ∀ j : ℕ, φ ((X.U A m X.I.z ^ j) f) =
      (X.I.uOp (X.rp (A ⧸ maximalIdeal A ^ k) m) X.I.z ^ j) (φ f) := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ← ih]
      exact uOpNat Gp X.I A _ (X.rp A m) _ _ (X.rp (A ⧸ maximalIdeal A ^ k) m) φ.toAddMonoidHom X.I.z X.I.z_mem _
        (fun _ _ => rfl)
  have h7 := lower_many X.I (X.rp (A ⧸ maximalIdeal A ^ k) m) c n _ hN hT hm y hy
  rw [← hpow, ← hnat] at h7
  simp only [Frame.valIn, Submodule.mem_pi]
  intro g _ i _
  have h9 := congrFun (congrFun h7 g) i
  rw [hφ, hφ, Ideal.Quotient.eq] at h9
  exact h9
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsOrdinaryProjectorOfEventuallyPeriodic
private theorem UpperTheory.pow_preserves_submodule {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (U : Submodule A M) (T : Module.End A M) (hT : ∀ f ∈ U, T f ∈ U) (n : ℕ) :
    ∀ f ∈ U, (T ^ n) f ∈ U := by
  induction n with
  | zero =>
    intro f hf
    simpa using hf
  | succ n ih =>
    intro f hf
    rw [pow_succ, Module.End.mul_apply]
    exact ih _ (hT f hf)

private theorem UpperTheory.periodic_difference_shift {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (U : Submodule A M) (T : Module.End A M) (hT : ∀ f ∈ U, T f ∈ U) (f : M) (a q : ℕ)
    (h : (T ^ (a + q)) f - (T ^ a) f ∈ U) (m : ℕ) (hm : a ≤ m) :
    (T ^ (m + q)) f - (T ^ m) f ∈ U := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hm
  have h' := UpperTheory.pow_preserves_submodule U T hT r _ h
  have e : (T ^ r) ((T ^ (a + q)) f - (T ^ a) f) = (T ^ (a + r + q)) f - (T ^ (a + r)) f := by
    rw [show a + r + q = r + (a + q) by ring, show a + r = r + a by ring,
      pow_add T r (a + q), pow_add T r a, Module.End.mul_apply, Module.End.mul_apply, map_sub]
  rw [e] at h'
  exact h'

private theorem UpperTheory.periodic_difference_mul_period {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (U : Submodule A M) (T : Module.End A M) (hT : ∀ f ∈ U, T f ∈ U) (f : M) (a q : ℕ)
    (h : (T ^ (a + q)) f - (T ^ a) f ∈ U) (m : ℕ) (hm : a ≤ m) (c : ℕ) :
    (T ^ (m + q * c)) f - (T ^ m) f ∈ U := by
  induction c with
  | zero => simp
  | succ c ih =>
    have h2 := UpperTheory.periodic_difference_shift U T hT f a q h (m + q * c) (by omega)
    have e : m + q * (c + 1) = m + q * c + q := by ring
    rw [e]
    have hs := U.add_mem h2 ih
    rw [sub_add_sub_cancel] at hs
    exact hs

private theorem UpperTheory.factorial_powers_cauchy {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (U : Submodule A M) (T : Module.End A M) (hT : ∀ f ∈ U, T f ∈ U) (f : M) (a p : ℕ)
    (h : (T ^ (a + (p + 1))) f - (T ^ a) f ∈ U) :
    ∃ J : ℕ, ∀ i j, J ≤ i → J ≤ j → (T ^ i.factorial) f - (T ^ j.factorial) f ∈ U := by
  obtain ⟨N, hN⟩ : ∃ N, N = a * (p + 1) := ⟨_, rfl⟩
  have haN : a ≤ N := by
    rw [hN]
    exact Nat.le_mul_of_pos_right a (Nat.succ_pos p)
  have hbase : ∀ i, N + (p + 1) ≤ i → (T ^ i.factorial) f - (T ^ N) f ∈ U := by
    intro i hi
    obtain ⟨k, hk⟩ := Nat.dvd_factorial (Nat.succ_pos p) (show p + 1 ≤ i by omega)
    have hi' : N ≤ i.factorial := le_trans (by omega) (Nat.self_le_factorial i)
    have hak : a ≤ k := by
      rw [hk, hN, mul_comm] at hi'
      exact Nat.le_of_mul_le_mul_left hi' (Nat.succ_pos p)
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hak
    have e : i.factorial = N + (p + 1) * c := by
      rw [hk, hN, Nat.succ_eq_add_one]
      ring
    rw [e]
    exact UpperTheory.periodic_difference_mul_period U T hT f a (p + 1) h N haN c
  refine ⟨N + (p + 1), fun i j hi hj => ?_⟩
  have hs := U.sub_mem (hbase i hi) (hbase j hj)
  rwa [sub_sub_sub_cancel_right] at hs

theorem UpperTheory.exists_ordinaryProjector_of_eventually_periodic :
    ∀ (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (V : ℕ → Submodule A M) (T : Module.End A M), Antitone V → (∀ k, ∀ f ∈ V k, T f ∈ V k) → (∀ f, (∀ k, f ∈ V k) → f = 0) → (∀ a : ℕ → M, (∀ k, a (k + 1) - a k ∈ V k) → ∃ L, ∀ k, L - a k ∈ V k) → (∀ f k, ∃ a p : ℕ, (T ^ (a + (p + 1))) f - (T ^ a) f ∈ V k) → ∃ e : Module.End A M, ∀ f k, (∃ J : ℕ, ∀ j, J ≤ j → (T ^ j.factorial) f - e f ∈ V k) ∧ (∃ n : ℕ, (T ^ (n + 1)) (e f) - e f ∈ V k) ∧ (f ∈ V k → e f ∈ V k) ∧ ((∃ n : ℕ, (T ^ (n + 1)) f - f ∈ V k) → e f - f ∈ V k) := by
  intro A M _ _ _ V T hV hT hsep hcomp hper
  have hJ : ∀ f k, ∃ J : ℕ, ∀ i j, J ≤ i → J ≤ j →
      (T ^ i.factorial) f - (T ^ j.factorial) f ∈ V k := by
    intro f k
    obtain ⟨a, p, h⟩ := hper f k
    exact UpperTheory.factorial_powers_cauchy (V k) T (hT k) f a p h
  choose J hJ using hJ
  let Nm : M → ℕ → ℕ := fun f k => ∑ i ∈ Finset.range (k + 1), J f i
  have hNmJ : ∀ f k, J f k ≤ Nm f k := fun f k =>
    Finset.single_le_sum (f := J f) (fun _ _ => Nat.zero_le _) (Finset.self_mem_range_succ k)
  have hNmmono : ∀ f k, Nm f k ≤ Nm f (k + 1) := fun f k => by
    simp only [Nm]
    rw [Finset.sum_range_succ _ (k + 1)]
    omega
  have hseq : ∀ f k, (T ^ (Nm f (k + 1)).factorial) f - (T ^ (Nm f k).factorial) f ∈ V k :=
    fun f k => hJ f k _ _ (le_trans (hNmJ f k) (hNmmono f k)) (hNmJ f k)
  have hlim : ∀ f, ∃ L, ∀ k, L - (T ^ (Nm f k).factorial) f ∈ V k := fun f =>
    hcomp (fun k => (T ^ (Nm f k).factorial) f) (hseq f)
  choose L hL using hlim
  let P : M → M → Prop := fun f x => ∀ k, ∃ J : ℕ, ∀ j, J ≤ j → (T ^ j.factorial) f - x ∈ V k
  have hPL : ∀ f, P f (L f) := by
    intro f k
    refine ⟨Nm f k, fun j hj => ?_⟩
    have h1 := hJ f k j (Nm f k) (le_trans (hNmJ f k) hj) (hNmJ f k)
    have hs := (V k).sub_mem h1 (hL f k)
    rwa [sub_sub_sub_cancel_right] at hs
  have huniq : ∀ f x y, P f x → P f y → x = y := by
    intro f x y hx hy
    have hxy : x - y = 0 := by
      apply hsep
      intro k
      obtain ⟨J1, h1⟩ := hx k
      obtain ⟨J2, h2⟩ := hy k
      have hs := (V k).sub_mem (h2 (max J1 J2) (le_max_right _ _)) (h1 (max J1 J2) (le_max_left _ _))
      rwa [sub_sub_sub_cancel_left] at hs
    exact sub_eq_zero.mp hxy
  have hPadd : ∀ f g x y, P f x → P g y → P (f + g) (x + y) := by
    intro f g x y hx hy k
    obtain ⟨J1, h1⟩ := hx k
    obtain ⟨J2, h2⟩ := hy k
    refine ⟨max J1 J2, fun j hj => ?_⟩
    have hs := (V k).add_mem (h1 j (le_trans (le_max_left _ _) hj))
      (h2 j (le_trans (le_max_right _ _) hj))
    rw [map_add (f := _)]
    convert hs using 1
    abel
  have hPsmul : ∀ (c : A) f x, P f x → P (c • f) (c • x) := by
    intro c f x hx k
    obtain ⟨J1, h1⟩ := hx k
    refine ⟨J1, fun j hj => ?_⟩
    have hs := (V k).smul_mem c (h1 j hj)
    rwa [smul_sub, ← map_smul] at hs
  let e : Module.End A M :=
    { toFun := L
      map_add' := fun f g => huniq (f + g) _ _ (hPL _) (hPadd f g _ _ (hPL f) (hPL g))
      map_smul' := fun c f => huniq (c • f) _ _ (hPL _) (hPsmul c f _ (hPL f)) }
  refine ⟨e, fun f k => ⟨hPL f k, ?_, ?_, ?_⟩⟩
  · obtain ⟨a, p, h⟩ := hper f k
    obtain ⟨J1, h1⟩ := hPL f k
    refine ⟨p, ?_⟩
    show (T ^ (p + 1)) (L f) - L f ∈ V k
    obtain ⟨j, hjdef⟩ : ∃ j, j = max J1 a := ⟨_, rfl⟩
    have hja : a ≤ j.factorial := le_trans (by omega) (Nat.self_le_factorial _)
    have hA := h1 j (by omega)
    have hB := UpperTheory.periodic_difference_shift (V k) T (hT k) f a (p + 1) h j.factorial hja
    have hC := UpperTheory.pow_preserves_submodule (V k) T (hT k) (p + 1) _ hA
    have eq : (T ^ (p + 1)) ((T ^ j.factorial) f) = (T ^ (j.factorial + (p + 1))) f := by
      rw [add_comm j.factorial (p + 1), pow_add T (p + 1) j.factorial, Module.End.mul_apply]
    have hsum := (V k).add_mem ((V k).add_mem ((V k).neg_mem hC) hB) hA
    rw [map_sub, eq] at hsum
    convert hsum using 1
    abel
  · intro hf
    obtain ⟨J1, h1⟩ := hPL f k
    have hA := h1 J1 le_rfl
    have hB := UpperTheory.pow_preserves_submodule (V k) T (hT k) J1.factorial f hf
    show L f ∈ V k
    have hs := (V k).sub_mem hB hA
    rwa [sub_sub_cancel] at hs
  · rintro ⟨n, hn⟩
    have h0 : (T ^ (0 + (n + 1))) f - (T ^ 0) f ∈ V k := by simpa using hn
    obtain ⟨J1, h1⟩ := hPL f k
    obtain ⟨N, hN⟩ : ∃ N, N = max J1 (n + 1) := ⟨_, rfl⟩
    obtain ⟨c, hc⟩ := Nat.dvd_factorial (Nat.succ_pos n) (show n + 1 ≤ N by omega)
    have hB := UpperTheory.periodic_difference_mul_period (V k) T (hT k) f 0 (n + 1) h0 0 le_rfl c
    rw [zero_add, pow_zero, ← hc] at hB
    have hA := h1 N (by omega)
    show L f - f ∈ V k
    have hs := (V k).sub_mem hB hA
    rw [sub_sub_sub_cancel_left] at hs
    simpa using hs
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsLinearPreimageOfSuccessiveApproximation
theorem UpperTheory.exists_linear_preimage_of_successive_approximation :
    ∀ (A M ι : Type) [CommRing A] [AddCommGroup M] [Module A M] [Fintype ι] (I : Ideal A) [IsAdicComplete I A] (V : ℕ → Submodule A M) (σ : (ι → A) →ₗ[A] M), Antitone V → (∀ k, (I ^ k • ⊤ : Submodule A M) ≤ V k) → (∀ f, (∀ k, f ∈ V k) → f = 0) → (∀ j, ∀ f ∈ V j, ∃ a : ι → A, (∀ i, a i ∈ I ^ j) ∧ f - σ a ∈ V (j + 1)) → ∀ j, ∀ f ∈ V j, ∃ a : ι → A, (∀ i, a i ∈ I ^ j) ∧ σ a = f := by
  intro A M ι _ _ _ _ I _ V σ hV hI hsep hstep j f hf
  classical
  let a' : ℕ → M → ι → A := fun k g => if h : g ∈ V k then (hstep k g h).choose else 0
  have ha' : ∀ k g, g ∈ V k → (∀ i, a' k g i ∈ I ^ k) ∧ g - σ (a' k g) ∈ V (k + 1) := by
    intro k g h
    simp only [a', dif_pos h]
    exact (hstep k g h).choose_spec
  let r : ℕ → M := fun n => Nat.rec f (fun n g => g - σ (a' (j + n) g)) n
  have hrs : ∀ n, r (n + 1) = r n - σ (a' (j + n) (r n)) := fun n => rfl
  have hr : ∀ n, r n ∈ V (j + n) := by
    intro n
    induction n with
    | zero => exact hf
    | succ n ih =>
      rw [hrs, ← add_assoc]
      exact (ha' _ _ ih).2
  let b : ℕ → ι → A := fun n => a' (j + n) (r n)
  have hb : ∀ n i, b n i ∈ I ^ (j + n) := fun n => (ha' _ _ (hr n)).1
  have hrsum : ∀ N, r N = f - σ (∑ n ∈ Finset.range N, b n) := by
    intro N
    induction N with
    | zero => simp [r]
    | succ N ih =>
      show r N - σ (b N) = f - σ (∑ n ∈ Finset.range (N + 1), b n)
      rw [ih, Finset.sum_range_succ, map_add (f := _)]
      abel
  have hlim : ∀ i, ∃ L : A, ∀ n,
      (∑ k ∈ Finset.range n, b k i) ≡ L [SMOD (I ^ n • ⊤ : Submodule A A)] := by
    intro i
    refine IsPrecomplete.prec (inferInstance : IsPrecomplete I A) ?_
    intro m n hmn
    rw [SModEq.sub_mem, ← neg_sub, Submodule.neg_mem_iff, ← Finset.sum_Ico_eq_sub _ hmn]
    refine Submodule.sum_mem _ (fun k hk => ?_)
    have hmk : m ≤ j + k := by
      have := (Finset.mem_Ico.mp hk).1
      omega
    simpa using Submodule.smul_mem_smul (Ideal.pow_le_pow_right hmk (hb k i))
      (Submodule.mem_top : (1 : A) ∈ (⊤ : Submodule A A))
  choose L hL using hlim
  refine ⟨L, fun i => ?_, ?_⟩
  · have h1 := SModEq.sub_mem.mp (hL i j)
    have h2 : (∑ k ∈ Finset.range j, b k i) ∈ I ^ j :=
      Submodule.sum_mem _ (fun k _ => Ideal.pow_le_pow_right (by omega) (hb k i))
    have h1' : (∑ k ∈ Finset.range j, b k i) - L i ∈ I ^ j := by
      simpa [smul_eq_mul, Ideal.mul_top] using h1
    simpa using Submodule.sub_mem _ h2 h1'
  · have h0 : f - σ L = 0 := by
      apply hsep
      intro N
      have hv : ∀ i, ((∑ n ∈ Finset.range N, b n) - L) i ∈ I ^ N := by
        intro i
        have := SModEq.sub_mem.mp (hL i N)
        simpa [Finset.sum_apply, smul_eq_mul, Ideal.mul_top] using this
      have hσ : σ ((∑ n ∈ Finset.range N, b n) - L) ∈ (I ^ N • ⊤ : Submodule A M) := by
        set v := (∑ n ∈ Finset.range N, b n) - L
        set_option synthInstance.maxHeartbeats 100000 in
          rw [pi_eq_sum_univ v, map_sum]
        refine Submodule.sum_mem _ (fun i _ => ?_)
        rw [map_smul]
        exact Submodule.smul_mem_smul (hv i) Submodule.mem_top
      have e : f - σ L = r N + σ ((∑ n ∈ Finset.range N, b n) - L) := by
        rw [hrsum, map_sub]
        abel
      rw [e]
      exact Submodule.add_mem _ (hV (by omega : N ≤ j + N) (hr N)) (hI N hσ)
    exact (sub_eq_zero.mp h0).symm
end

open IsLocalRing Matrix UpperTheory.V.Hi

private theorem ordFree_smul {A N ι : Type} [CommRing A] [AddCommGroup N] [Module A N] [Fintype ι]
    (σ : (ι → A) →ₗ[A] N) (J : Ideal A) (a : ι → A) (ha : ∀ i, a i ∈ J) : σ a ∈ (J • ⊤ : Submodule A N) := by
  classical
  have key : a = ∑ i, a i • (Pi.single i (1 : A) : ι → A) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [key, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [map_smul]
  exact Submodule.smul_mem_smul (ha i) Submodule.mem_top

private theorem ordFree_bij {A N : Type} [CommRing A] [IsLocalRing A] [AddCommGroup N] [Module A N] [Module.Finite A N]
    (φ : N →ₗ[A] N) (h : ∀ f, ∃ g, f - φ g ∈ (maximalIdeal A • ⊤ : Submodule A N)) : Function.Bijective φ := by
  have hsurj : Function.Surjective φ := by
    rw [← LinearMap.range_eq_top, eq_top_iff]
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal A) Module.Finite.fg_top
      (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge ?_
    intro f _
    obtain ⟨g, hg⟩ := h f
    have : f = φ g + (f - φ g) := by abel
    rw [this]
    exact Submodule.add_mem_sup (LinearMap.mem_range_self φ g) hg
  exact ⟨OrzechProperty.injective_of_surjective_endomorphism φ hsurj, hsurj⟩

private theorem ordFree_pow {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (V : Submodule A M)
    (T : Module.End A M) (hT : ∀ v ∈ V, T v ∈ V) (n j : ℕ) (v : M) (hv : (T ^ n) v - v ∈ V) :
    (T ^ (n * j)) v - v ∈ V := by
  have hTk : ∀ k : ℕ, ∀ w ∈ V, (T ^ k) w ∈ V := by
    intro k
    induction k with
    | zero => intro w hw; simpa using hw
    | succ k ih =>
      intro w hw
      rw [pow_succ', Module.End.mul_apply]
      exact hT _ (ih w hw)
  induction j with
  | zero => simp
  | succ j ih =>
    have e : (T ^ (n * (j + 1))) v - v = (T ^ (n * j)) ((T ^ n) v - v) + ((T ^ (n * j)) v - v) := by
      rw [map_sub, ← Module.End.mul_apply, ← pow_add, mul_add, mul_one]
      abel
    rw [e]
    exact V.add_mem (hTk _ _ hv) ih

private theorem linearMap_pi_eq_sum_single {A N ι : Type} [CommRing A] [AddCommGroup N] [Module A N] [Fintype ι]
    [DecidableEq ι] (σ : (ι → A) →ₗ[A] N) (b : ι → A) :
    σ b = ∑ i, b i • σ (Pi.single i (1 : A) : ι → A) := by
  have hb : b = ∑ i, b i • (Pi.single i (1 : A) : ι → A) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hb]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul]

private theorem exists_eventually_periodic_mod_V {A M : Type} [CommRing A] [IsCNL A] [AddCommGroup M] [Module A M]
    (V : ℕ → Submodule A M) (T : Module.End A M)
    (hm : ∀ k, (maximalIdeal A ^ k • ⊤ : Submodule A M) ≤ V k)
    (hlev : ∀ k, ∃ (ι : Type) (_ : Fintype ι) (s : (ι → A) →ₗ[A] M) (ev : M →ₗ[A] (ι → A)),
      (∀ j, ∀ f ∈ V j, ∀ i, ev f i ∈ maximalIdeal A ^ j) ∧
        ∀ f, ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → (T ^ n) f - s (ev ((T ^ n) f)) ∈ V k)
    (f : M) (k : ℕ) : ∃ a p : ℕ, (T ^ (a + (p + 1))) f - (T ^ a) f ∈ V k := by
  obtain ⟨ι, hι, s, ev, -, hs⟩ := hlev k
  obtain ⟨n₀, hn₀⟩ := hs f
  haveI : Finite (A ⧸ maximalIdeal A) := (IsCNL.finite : Finite (ResidueField A))
  haveI : Finite (A ⧸ maximalIdeal A ^ k) :=
    Ideal.finite_quotient_pow (IsNoetherian.noetherian _) k
  let F : ℕ → (ι → A ⧸ maximalIdeal A ^ k) :=
    fun n i => Ideal.Quotient.mk _ (ev ((T ^ (n₀ + n)) f) i)
  have key : ∀ x y : ℕ, x < y → F x = F y → ∃ a p : ℕ, (T ^ (a + (p + 1))) f - (T ^ a) f ∈ V k := by
    intro x y hxy hF
    refine ⟨n₀ + x, y - x - 1, ?_⟩
    have hy : n₀ + x + (y - x - 1 + 1) = n₀ + y := by omega
    rw [hy]
    have hd : ∀ i, ev ((T ^ (n₀ + y)) f - (T ^ (n₀ + x)) f) i ∈ maximalIdeal A ^ k := by
      intro i
      have := congrFun hF i
      simp only [F] at this
      rw [map_sub, Pi.sub_apply]
      exact Ideal.Quotient.eq.1 this.symm
    have h3 := hm k (ordFree_smul s _ _ hd)
    have h1 := hn₀ (n₀ + y) (by omega)
    have h2 := hn₀ (n₀ + x) (by omega)
    have eq : (T ^ (n₀ + y)) f - (T ^ (n₀ + x)) f =
        ((T ^ (n₀ + y)) f - s (ev ((T ^ (n₀ + y)) f))) - ((T ^ (n₀ + x)) f - s (ev ((T ^ (n₀ + x)) f)))
          + s (ev ((T ^ (n₀ + y)) f - (T ^ (n₀ + x)) f)) := by
      simp only [map_sub]
      abel
    rw [eq]
    exact add_mem (sub_mem h1 h2) h3
  obtain ⟨x, y, hne, hxy⟩ := Finite.exists_ne_map_eq_of_infinite F
  rcases lt_or_gt_of_ne hne with h | h
  · exact key x y h hxy
  · exact key y x h hxy.symm

theorem UpperTheory.V.Hi.ordAbs {A M : Type} [CommRing A] [IsCNL A] [AddCommGroup M] [Module A M] (V : ℕ → Submodule A M)
    (T : Module.End A M) (O : Submodule A M) (hanti : Antitone V)
    (hm : ∀ k, (maximalIdeal A ^ k • ⊤ : Submodule A M) ≤ V k)
    (hm1 : ∀ k, ∀ r ∈ maximalIdeal A ^ k, ∀ f ∈ V 1, r • f ∈ V (k + 1))
    (hT : ∀ k, ∀ f ∈ V k, T f ∈ V k) (hsep : ∀ f, (∀ k, f ∈ V k) → f = 0)
    (hcomp : ∀ a : ℕ → M, (∀ k, a (k + 1) - a k ∈ V k) → ∃ L, ∀ k, L - a k ∈ V k)
    (hlev : ∀ k, ∃ (ι : Type) (_ : Fintype ι) (s : (ι → A) →ₗ[A] M) (ev : M →ₗ[A] (ι → A)),
      (∀ j, ∀ f ∈ V j, ∀ i, ev f i ∈ maximalIdeal A ^ j) ∧
        ∀ f, ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → (T ^ n) f - s (ev ((T ^ n) f)) ∈ V k)
    (hO : ∀ f, f ∈ O ↔ ∀ k, ∃ n : ℕ, (T ^ (n + 1)) f - f ∈ V k) :
    Module.Finite A O ∧ Module.Free A O ∧ Set.BijOn T O O ∧
      (∀ j, ∀ f : O, (f : M) ∈ V j → f ∈ (maximalIdeal A ^ j • ⊤ : Submodule A O)) ∧
      ∃ e : Module.End A M, (∀ f, e f ∈ O) ∧ (∀ f ∈ O, e f = f) ∧
        ∀ f k, ∃ J : ℕ, ∀ j, J ≤ j → (T ^ j.factorial) f - e f ∈ V k := by
  classical
  haveI : IsAdicComplete (maximalIdeal A) A := IsCNL.complete
  obtain ⟨e, he⟩ := UpperTheory.exists_ordinaryProjector_of_eventually_periodic A M V T hanti hT hsep hcomp (fun f k => exists_eventually_periodic_mod_V V T hm hlev f k)
  have heO : ∀ f, e f ∈ O := fun f => (hO _).2 fun k => (he f k).2.1
  have heV : ∀ k f, f ∈ V k → e f ∈ V k := fun k f hf => (he f k).2.2.1 hf
  have heid : ∀ f ∈ O, e f = f := by
    intro f hf
    exact sub_eq_zero.1 (hsep _ fun k => (he f k).2.2.2 ((hO f).1 hf k))
  have happ : ∀ k, ∃ (ι : Type) (_ : Fintype ι) (s : (ι → A) →ₗ[A] M) (ev : M →ₗ[A] (ι → A)),
      (∀ j, ∀ f ∈ V j, ∀ i, ev f i ∈ maximalIdeal A ^ j) ∧ ∀ f ∈ O, f - e (s (ev f)) ∈ V k := by
    intro k
    obtain ⟨ι, hι, s, ev, hev, hs⟩ := hlev k
    refine ⟨ι, hι, s, ev, hev, fun f hf => ?_⟩
    obtain ⟨n₀, hn₀⟩ := hs f
    obtain ⟨J, hJ⟩ := (he f k).1
    have h1 : (T ^ (max J n₀).factorial) f - f ∈ V k := by
      have := hJ (max J n₀) (le_max_left _ _)
      rwa [heid f hf] at this
    have h2 := hn₀ (max J n₀).factorial ((le_max_right _ _).trans (Nat.self_le_factorial _))
    have h3 := hm k (ordFree_smul s _ _ (hev k _ h1))
    have h4 : f - s (ev f) ∈ V k := by
      have eq : f - s (ev f) = ((T ^ (max J n₀).factorial) f - s (ev ((T ^ (max J n₀).factorial) f)))
          - ((T ^ (max J n₀).factorial) f - f) + s (ev ((T ^ (max J n₀).factorial) f - f)) := by
        simp only [map_sub]
        abel
      rw [eq]
      exact add_mem (sub_mem h2 h1) h3
    have h5 := heV k _ h4
    rwa [map_sub, heid f hf] at h5
  obtain ⟨ι₁, hι₁, s₁, ev₁, hev₁, h₁⟩ := happ 1
  have hstep : ∀ j, ∀ f ∈ O, f ∈ V j → ∃ a : ι₁ → A, (∀ i, a i ∈ maximalIdeal A ^ j) ∧
      f - e (s₁ a) ∈ V (j + 1) := by
    intro j f hf hfj
    obtain ⟨ι', hι', s', ev', hev', h'⟩ := happ (j + 1)
    have hb : ∀ i, ev' f i ∈ maximalIdeal A ^ j := hev' j f hfj
    refine ⟨∑ i, ev' f i • ev₁ (e (s' (Pi.single i (1 : A) : ι' → A))), fun i' => ?_, ?_⟩
    · rw [Finset.sum_apply]
      refine Ideal.sum_mem _ fun i _ => ?_
      rw [Pi.smul_apply, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ (hb i)
    · have e1 : e (s' (ev' f)) = ∑ i, ev' f i • e (s' (Pi.single i (1 : A) : ι' → A)) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [linearMap_pi_eq_sum_single s' (ev' f), map_sum]
        simp only [map_smul]
      have e2 : f - e (s₁ (∑ i, ev' f i • ev₁ (e (s' (Pi.single i (1 : A) : ι' → A))))) =
          (f - e (s' (ev' f))) + ∑ i, ev' f i • (e (s' (Pi.single i (1 : A) : ι' → A))
            - e (s₁ (ev₁ (e (s' (Pi.single i (1 : A) : ι' → A)))))) := by
        rw [e1]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, map_smul, smul_sub, Finset.sum_sub_distrib]
        abel
      rw [e2]
      exact add_mem (h' f hf) (Submodule.sum_mem _ fun i _ => hm1 j _ (hb i) _ (h₁ _ (heO _)))
  let σ : (ι₁ → A) →ₗ[A] O := (e ∘ₗ s₁).codRestrict O (fun x => heO _)
  have hσ : ∀ a, (σ a : M) = e (s₁ a) := fun a => rfl
  have hlift := UpperTheory.exists_linear_preimage_of_successive_approximation A O ι₁ (maximalIdeal A) (fun j => (V j).comap O.subtype) σ
    (fun i j h => Submodule.comap_mono (hanti h))
    (by
      intro k x hx
      have h := Submodule.mem_map_of_mem (f := O.subtype) hx
      rw [Submodule.map_smul''] at h
      exact hm k (Submodule.smul_mono le_rfl le_top h))
    (fun f hf => Subtype.ext (hsep _ hf))
    (by
      intro j f hf
      obtain ⟨a, ha, hfa⟩ := hstep j f f.2 hf
      exact ⟨a, ha, by simpa [hσ] using hfa⟩)
  have hV0 : ∀ f : M, f ∈ V 0 := fun f => hm 0 (by simp)
  have hsurj : Function.Surjective σ := by
    intro f
    obtain ⟨a, -, ha⟩ := hlift 0 f (hV0 _)
    exact ⟨a, ha⟩
  haveI hfin : Module.Finite A O := Module.Finite.of_surjective σ hsurj
  have hfilt : ∀ j, ∀ f : O, (f : M) ∈ V j → f ∈ (maximalIdeal A ^ j • ⊤ : Submodule A O) := by
    intro j f hf
    obtain ⟨a, ha, rfl⟩ := hlift j f hf
    exact ordFree_smul σ _ a ha
  let ι : O →ₗ[A] (ι₁ → A) := ev₁ ∘ₗ O.subtype
  have hφ : Function.Bijective (σ ∘ₗ ι) := by
    refine ordFree_bij (σ ∘ₗ ι) fun f => ⟨f, ?_⟩
    have := hfilt 1 (f - (σ ∘ₗ ι) f) (by simpa [ι, hσ] using h₁ f f.2)
    simpa using this
  let φe := LinearEquiv.ofBijective (σ ∘ₗ ι) hφ
  haveI : Module.Projective A O := by
    refine Module.Projective.of_split ι (φe.symm.toLinearMap ∘ₗ σ) ?_
    ext f
    simp only [LinearMap.comp_apply, LinearMap.id_apply]
    exact congrArg Subtype.val (φe.symm_apply_apply f)
  have hmaps : ∀ f ∈ O, T f ∈ O := by
    intro f hf
    refine (hO _).2 fun k => ?_
    obtain ⟨n, hn⟩ := (hO f).1 hf k
    refine ⟨n, ?_⟩
    have : (T ^ (n + 1)) (T f) - T f = T ((T ^ (n + 1)) f - f) := by
      rw [map_sub, ← Module.End.mul_apply, ← pow_succ, pow_succ', Module.End.mul_apply]
    rw [this]
    exact hT k _ hn
  have hmapsn : ∀ n : ℕ, ∀ f ∈ O, (T ^ n) f ∈ O := by
    intro n
    induction n with
    | zero => intro f hf; simpa using hf
    | succ n ih =>
      intro f hf
      rw [pow_succ', Module.End.mul_apply]
      exact hmaps _ (ih f hf)
  let TO : O →ₗ[A] O := T.restrict hmaps
  have hTO : Function.Bijective TO := by
    refine ordFree_bij TO fun f => ?_
    obtain ⟨n, hn⟩ := (hO f).1 f.2 1
    refine ⟨⟨(T ^ n) f, hmapsn n f f.2⟩, ?_⟩
    have h := hfilt 1 (f - TO ⟨(T ^ n) f, hmapsn n f f.2⟩) (by
      have : ((f - TO ⟨(T ^ n) f, hmapsn n f f.2⟩ : O) : M) = -((T ^ (n + 1)) f - f) := by
        simp only [TO, Submodule.coe_sub, LinearMap.restrict_coe_apply]
        rw [pow_succ', Module.End.mul_apply]
        abel
      rw [this]
      exact neg_mem hn)
    simpa using h
  refine ⟨hfin, Module.free_of_flat_of_isLocalRing, ⟨hmaps, ?_, ?_⟩, hfilt, e, heO, heid, fun f k => (he f k).1⟩
  · intro x hx y hy hxy
    have := hTO.1 (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) (Subtype.ext hxy)
    exact congrArg Subtype.val this
  · intro y hy
    obtain ⟨x, hx⟩ := hTO.2 ⟨y, hy⟩
    exact ⟨x, x.2, congrArg Subtype.val hx⟩

section

variable {Γ Ga Gp : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) {A : Type} [CommRing A] [IsCNL A] {m : ℕ}

private theorem ordFree_val (k : ℕ) (f : X.Fn A m) : f ∈ X.valIn A m k ↔ ∀ g i, f g i ∈ maximalIdeal A ^ k := by
  simp only [Frame.valIn, Submodule.mem_pi, Set.mem_univ, true_implies]

private theorem ordFree_valU (k : ℕ) {a : Gp} (ha : a ∈ X.I.P) (f : X.Fn A m) (hf : f ∈ X.valIn A m k) :
    X.U A m a f ∈ X.valIn A m k := by
  have hterm : ∀ y : Gp, X.rp A m y f ∈ X.valIn A m k := by
    intro y
    rw [ordFree_val] at hf ⊢
    intro g i
    exact hf _ i
  show X.I.uOp (X.rp A m) a f ∈ X.valIn A m k
  unfold Iwa.uOp
  exact finsum_induction (fun φ : Module.End A (X.Fn A m) => φ f ∈ X.valIn A m k)
    (by simp) (fun φ ψ hφ hψ => by simpa using Submodule.add_mem _ hφ hψ) (fun q => hterm _)

theorem UpperTheory.V.Hi.mem_ord_iff (τ : X.Ub →* GL (Fin m) A) (θ : X.I.T →* Aˣ) (U : Subgroup X.Ub) (f : X.Fn A m) :
    f ∈ X.Ord τ θ U ↔ f ∈ X.Sp τ θ U ∧ ∀ k, ∃ n : ℕ, (X.U A m X.I.z ^ (n + 1)) f - f ∈ X.valIn A m k := by
  have hT : ∀ k, ∀ v ∈ X.valIn A m k, X.U A m X.I.z v ∈ X.valIn A m k :=
    fun k v hv => ordFree_valU X k X.I.z_mem v hv
  have hmem : ∀ k n, f ∈ Submodule.comap (X.U A m X.I.z ^ (n + 1) - 1) (X.valIn A m k) ↔
      (X.U A m X.I.z ^ (n + 1)) f - f ∈ X.valIn A m k := by
    intro k n
    simp [Submodule.mem_comap]
  have hdir : ∀ k, Directed (· ≤ ·)
      (fun n : ℕ => Submodule.comap (X.U A m X.I.z ^ (n + 1) - 1) (X.valIn A m k)) := by
    intro k n n'
    refine ⟨(n + 1) * (n' + 1) - 1, ?_, ?_⟩
    · intro v hv
      simp only [Submodule.mem_comap, LinearMap.sub_apply, Module.End.one_apply] at hv ⊢
      have e : (n + 1) * (n' + 1) - 1 + 1 = (n + 1) * (n' + 1) := by
        have : 1 ≤ (n + 1) * (n' + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
        omega
      rw [e]
      exact ordFree_pow _ _ (hT k) (n + 1) (n' + 1) v hv
    · intro v hv
      simp only [Submodule.mem_comap, LinearMap.sub_apply, Module.End.one_apply] at hv ⊢
      have e : (n + 1) * (n' + 1) - 1 + 1 = (n' + 1) * (n + 1) := by
        have : 1 ≤ (n + 1) * (n' + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
        rw [Nat.mul_comm (n' + 1)]
        omega
      rw [e]
      exact ordFree_pow _ _ (hT k) (n' + 1) (n + 1) v hv
  simp only [Frame.Ord, Submodule.mem_inf, Submodule.mem_iInf]
  refine and_congr_right fun _ => forall_congr' fun k => ?_
  rw [Submodule.mem_iSup_of_directed _ (hdir k)]
  exact exists_congr fun n => hmem k n

theorem UpperTheory.V.Hi.ordStruct (τ : X.Ub →* GL (Fin m) A) (θ : X.I.T →* Aˣ) (hθ : X.I.ContChar θ) (U : Subgroup X.Ub)
    (hU : X.FinLevel U) (hF : X.Free τ θ U) :
    Module.Finite A (X.Ord τ θ U) ∧ Module.Free A (X.Ord τ θ U) ∧
      Set.BijOn (X.U A m X.I.z) (X.Ord τ θ U) (X.Ord τ θ U) ∧
      (∀ j, ∀ f : X.Ord τ θ U, (f : X.Fn A m) ∈ X.valIn A m j →
        f ∈ (maximalIdeal A ^ j • ⊤ : Submodule A (X.Ord τ θ U))) ∧
      ∃ e : X.Sp τ θ U →ₗ[A] X.Ord τ θ U, (∀ f : X.Sp τ θ U, (f : X.Fn A m) ∈ X.Ord τ θ U → (e f : X.Fn A m) = f) ∧
        ∀ (f : X.Sp τ θ U) (k : ℕ), ∃ J : ℕ, ∀ j, J ≤ j →
          (X.U A m X.I.z ^ j.factorial) f - e f ∈ X.valIn A m k := by
  classical
  have hSp : ∀ f ∈ X.Sp τ θ U, X.U A m X.I.z f ∈ X.Sp τ θ U :=
    ((spStab Γ Ga Gp X A m τ θ hθ).2.2.2.1 U X.I.z X.I.z_mem).1
  let S := X.Sp τ θ U
  let T : Module.End A S := (X.U A m X.I.z).restrict hSp
  have hTpow : ∀ (n : ℕ) (f : S), ((T ^ n) f : X.Fn A m) = (X.U A m X.I.z ^ n) f := by
    intro n f
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ← ih]
      rfl
  let V : ℕ → Submodule A S := fun k => (X.valIn A m k).comap S.subtype
  have hV : ∀ k (f : S), f ∈ V k ↔ ∀ g i, (f : X.Fn A m) g i ∈ maximalIdeal A ^ k :=
    fun k f => Submodule.mem_comap.trans (ordFree_val X k _)
  let O : Submodule A S := (X.Ord τ θ U).comap S.subtype
  have hOS : X.Ord τ θ U ≤ S := fun f hf => ((mem_ord_iff X τ θ U f).1 hf).1
  have hanti : Antitone V := by
    intro a b hab f hf
    rw [hV] at hf ⊢
    intro g i
    exact Ideal.pow_le_pow_right hab (hf g i)
  have hm : ∀ k, (maximalIdeal A ^ k • ⊤ : Submodule A S) ≤ V k := by
    intro k
    rw [Submodule.smul_le]
    intro r hr f _
    rw [hV]
    intro g i
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ hr
  have hm1 : ∀ k, ∀ r ∈ maximalIdeal A ^ k, ∀ f ∈ V 1, r • f ∈ V (k + 1) := by
    intro k r hr f hf
    rw [hV] at hf ⊢
    intro g i
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    rw [pow_succ]
    exact Ideal.mul_mem_mul hr (by simpa using hf g i)
  have hTV : ∀ k, ∀ f ∈ V k, T f ∈ V k := by
    intro k f hf
    exact ordFree_valU X k X.I.z_mem _ hf
  have hsep : ∀ f, (∀ k, f ∈ V k) → f = 0 := by
    intro f hf
    apply Subtype.ext
    funext g i
    have hmem : (f : X.Fn A m) g i ∈ ⨅ k, maximalIdeal A ^ k :=
      Submodule.mem_iInf _ |>.2 fun k => (hV k f).1 (hf k) g i
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal A).ne_top] at hmem
    simpa using hmem
  have hcomp : ∀ a : ℕ → S, (∀ k, a (k + 1) - a k ∈ V k) → ∃ L, ∀ k, L - a k ∈ V k := by
    intro a ha
    obtain ⟨L, hL, hLk⟩ := exists_adic_limit_mem_automorphicSpace Γ Ga Gp X A m τ θ U (fun k => (a k : X.Fn A m)) (fun k => (a k).2)
      (fun k => ha k)
    exact ⟨⟨L, hL⟩, hLk⟩
  have hlev : ∀ k, ∃ (ι : Type) (_ : Fintype ι) (s : (ι → A) →ₗ[A] S) (ev : S →ₗ[A] (ι → A)),
      (∀ j, ∀ f ∈ V j, ∀ i, ev f i ∈ maximalIdeal A ^ j) ∧
        ∀ f, ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → (T ^ n) f - s (ev ((T ^ n) f)) ∈ V k := by
    intro k
    obtain ⟨c, hc⟩ := hθ k
    obtain ⟨N, x, hcov, huniq⟩ := exists_finite_iwahori_doubleCoset_representatives Γ Ga Gp X U hU c
    obtain ⟨s, hs⟩ := exists_section_automorphicSpace_with_prescribed_values Γ Ga Gp X A m τ θ hθ U hF c N x hcov huniq
    let ev : S →ₗ[A] (Fin N × Fin m → A) :=
      { toFun := fun f p => (f : X.Fn A m) (x p.1) p.2
        map_add' := by intros; rfl
        map_smul' := by intros; rfl }
    refine ⟨Fin N × Fin m, inferInstance, LinearMap.codRestrict S s (fun v => (hs v).1), ev, ?_, ?_⟩
    · intro j f hf p
      exact (hV j f).1 hf _ _
    · intro f
      obtain ⟨n₀, hn₀⟩ := uOperator_pow_eventually_invariant_mod_pow Γ Ga Gp X A m θ hθ f.1 (Submodule.mem_inf.1 f.2).1 k c hc
      refine ⟨n₀, fun n hn => ?_⟩
      show ((T ^ n) f - LinearMap.codRestrict S s (fun v => (hs v).1) (ev ((T ^ n) f)) : S).1 ∈ X.valIn A m k
      refine mem_valIn_of_invariant_and_values_mem_pow Γ Ga Gp X A m τ θ U k c N x hcov _ (Subtype.prop _) ?_ ?_
      · intro y hy
        have e1 : ((T ^ n) f - LinearMap.codRestrict S s (fun v => (hs v).1) (ev ((T ^ n) f)) : S).1 =
            (X.U A m X.I.z ^ n) f - s (ev ((T ^ n) f)) := by
          rw [Submodule.coe_sub, hTpow]
          rfl
        rw [e1, map_sub]
        have e2 : X.rp A m y ((X.U A m X.I.z ^ n) f) - X.rp A m y (s (ev ((T ^ n) f))) -
            ((X.U A m X.I.z ^ n) f - s (ev ((T ^ n) f))) =
            (X.rp A m y ((X.U A m X.I.z ^ n) f) - (X.U A m X.I.z ^ n) f) -
            (X.rp A m y (s (ev ((T ^ n) f))) - s (ev ((T ^ n) f))) := by abel
        rw [e2]
        exact Submodule.sub_mem _ (hn₀ n hn y hy) ((hs _).2.2 k hc y hy)
      · intro i j
        have e3 : (((T ^ n) f - LinearMap.codRestrict S s (fun v => (hs v).1) (ev ((T ^ n) f)) : S) :
            X.Fn A m) (x i) j = 0 := by
          simp only [Submodule.coe_sub, LinearMap.codRestrict_apply, Pi.sub_apply, (hs _).2.1]
          simp [ev]
        rw [e3]
        exact Submodule.zero_mem _
  have hO : ∀ f, f ∈ O ↔ ∀ k, ∃ n : ℕ, (T ^ (n + 1)) f - f ∈ V k := by
    intro f
    show (f : X.Fn A m) ∈ X.Ord τ θ U ↔ _
    rw [mem_ord_iff]
    constructor
    · rintro ⟨_, h⟩ k
      obtain ⟨n, hn⟩ := h k
      refine ⟨n, ?_⟩
      show (((T ^ (n + 1)) f - f : S) : X.Fn A m) ∈ X.valIn A m k
      rw [Submodule.coe_sub, hTpow]
      exact hn
    · intro h
      refine ⟨f.2, fun k => ?_⟩
      obtain ⟨n, hn⟩ := h k
      refine ⟨n, ?_⟩
      have h' : (((T ^ (n + 1)) f - f : S) : X.Fn A m) ∈ X.valIn A m k := hn
      rwa [Submodule.coe_sub, hTpow] at h'
  obtain ⟨hfin, hfree, hbij, hfilt, e, heO, heid, hconv⟩ :=
    ordAbs V T O hanti hm hm1 hTV hsep hcomp hlev hO
  let E := Submodule.comapSubtypeEquivOfLe hOS
  refine ⟨Module.Finite.equiv E, Module.Free.of_equiv E, ?_, ?_, ?_⟩
  · refine ⟨fun f hf => ?_, fun f hf g hg hfg => ?_, fun f hf => ?_⟩
    · exact hbij.mapsTo (show (⟨f, hOS hf⟩ : S) ∈ O from hf)
    · have := hbij.injOn (show (⟨f, hOS hf⟩ : S) ∈ O from hf) (show (⟨g, hOS hg⟩ : S) ∈ O from hg)
        (Subtype.ext hfg)
      exact congrArg Subtype.val this
    · obtain ⟨y, hy, hTy⟩ := hbij.surjOn (show (⟨f, hOS hf⟩ : S) ∈ O from hf)
      exact ⟨y.1, hy, congrArg Subtype.val hTy⟩
  · intro j f hf
    have h1 := hfilt j (E.symm f) hf
    have h2 : E (E.symm f) ∈ Submodule.map E.toLinearMap (maximalIdeal A ^ j • ⊤) :=
      Submodule.mem_map_of_mem h1
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range] at h2
    simpa using h2
  · refine ⟨E.toLinearMap ∘ₗ LinearMap.codRestrict O e heO, ?_, ?_⟩
    · intro f hf
      exact congrArg Subtype.val (heid f hf)
    · intro f k
      obtain ⟨J, hJ⟩ := hconv f k
      refine ⟨J, fun j hj => ?_⟩
      have h' : (((T ^ j.factorial) f - e f : S) : X.Fn A m) ∈ X.valIn A m k := hJ j hj
      rw [Submodule.coe_sub, hTpow] at h'
      exact h'

end

theorem UpperTheory.V.Hi.ordFree :
    ∀ (Γ Ga Gp : Type) [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) (A : Type) [CommRing A] [IsCNL A] (m : ℕ) (τ : X.Ub →* GL (Fin m) A) (θ : X.I.T →* Aˣ), X.I.ContChar θ → ∀ U, X.FinLevel U → X.Free τ θ U → Module.Finite A (X.Ord τ θ U) ∧ Module.Free A (X.Ord τ θ U) ∧ ∀ a ∈ X.I.P, Set.BijOn (X.U A m a) (X.Ord τ θ U) (X.Ord τ θ U) := by
  intro Γ Ga Gp _ _ _ X A _ _ m τ θ hθ U hU hF
  obtain ⟨hfin, hfree, hbij, -, -⟩ := ordStruct X τ θ hθ U hU hF
  refine ⟨hfin, hfree, fun a ha => ?_⟩
  have hmaps : ∀ b ∈ X.I.P, ∀ f ∈ X.Ord τ θ U, X.U A m b f ∈ X.Ord τ θ U :=
    fun b hb f hf => ((spStab Γ Ga Gp X A m τ θ hθ).2.2.2.1 U b hb).2 f hf
  have hfixN : ∀ f ∈ X.Ord τ θ U, f ∈ fixd (X.rp A m) X.I.N := by
    intro f hf
    have hSp : f ∈ X.Sp τ θ U := (Submodule.mem_inf.mp hf).1
    have hAmb : f ∈ X.Amb m θ := (Submodule.mem_inf.mp hSp).1
    exact hAmb.2.1
  have hmul : ∀ b ∈ X.I.P, ∀ c ∈ X.I.P, ∀ f ∈ X.Ord τ θ U,
      X.U A m b (X.U A m c f) = X.U A m (b * c) f :=
    fun b hb c hc f hf => (uOpMul Gp X.I A _ (X.rp A m) b c hb hc f (hfixN f hf)).2.1
  have hone : ∀ f ∈ X.Ord τ θ U, X.U A m 1 f = f :=
    fun f hf => (uOpMul Gp X.I A _ (X.rp A m) 1 1 X.I.P.one_mem X.I.P.one_mem f (hfixN f hf)).2.2.1
  have hpow : ∀ k : ℕ, ∀ f ∈ X.Ord τ θ U, (X.U A m X.I.z ^ k) f = X.U A m (X.I.z ^ k) f := by
    intro k
    induction k with
    | zero => intro f hf; simp [hone f hf]
    | succ k ih =>
      intro f hf
      rw [pow_succ', Module.End.mul_apply, ih f hf,
        hmul _ X.I.z_mem _ (X.I.P.pow_mem X.I.z_mem k) f hf, ← pow_succ']
  obtain ⟨k, hk⟩ := X.I.exists_pow_mul_inv_mem a ha
  set b := X.I.z ^ k * a⁻¹ with hbdef
  have hzk : X.I.z ^ k = b * a := by rw [hbdef]; group
  have hab : a * b = b * a := X.I.comm a (X.I.P_le a ha) b (X.I.P_le b hk)
  have hbijk : Set.BijOn (X.U A m X.I.z ^ k) (X.Ord τ θ U) (X.Ord τ θ U) := by
    rw [Module.End.coe_pow]
    exact hbij.iterate k
  refine ⟨fun f hf => hmaps a ha f hf, ?_, ?_⟩
  · intro f hf g hg hfg
    apply hbijk.injOn hf hg
    rw [hpow k f hf, hpow k g hg, hzk, ← hmul b hk a ha f hf, ← hmul b hk a ha g hg]
    exact congrArg (X.U A m b) hfg
  · intro g hg
    obtain ⟨h, hh, rfl⟩ := hbijk.surjOn hg
    refine ⟨X.U A m b h, hmaps b hk h hh, ?_⟩
    rw [hmul a ha b hk h hh, hab, ← hzk, hpow k h hh]
