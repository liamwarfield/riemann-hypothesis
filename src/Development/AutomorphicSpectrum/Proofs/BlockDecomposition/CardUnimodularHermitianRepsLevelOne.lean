module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuotientCard
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormFibreCardNonzero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HenselPolynomialRefinement

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardOrthonormalFramesHermitianSpace
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianVectorValuesCard
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianSpaceAnisotropicUnit
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianSpaceAnisotropicUnit
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens

namespace GlobalTheory.CompanionTheory.UnrDens

theorem exists_trace_ne_zero {E : Type} [CommRing E] {τ : E →+* E} {q : ℕ} {ε : ℤ}
    (hE : ResAlg E τ q ε) {a : E} (ha : a ≠ 0) : ∃ c : E, c * a + τ (c * a) ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨u, hu, -⟩ := hE.basis
  have h1 := hcon 1
  have h2 := hcon u
  simp only [one_mul, map_mul] at h1 h2
  have hta : τ a = -a := by linear_combination h1
  rw [hta] at h2
  obtain ⟨w', hw'⟩ := hu.exists_left_inv
  apply ha
  linear_combination w' * h2 - a * hw'

theorem exists_unit_norm (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ)
    (hE : ResAlg E τ q ε) (V : Type) [AddCommGroup V] [Module E V] (B : HermSp E τ V)
    (hV : Nontrivial V) : ∃ w : V, IsUnit (B.h w w) := by
  have key : ∀ w : V, B.h w w ≠ 0 → IsUnit (B.h w w) := fun w hw =>
    hE.fixedUnit _ (B.self_fixed hE.inv w) hw
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hex : ∃ w, B.h v w ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hv (B.nondeg v hcon)
  obtain ⟨w, hvw⟩ := hex
  obtain ⟨c, hc⟩ := exists_trace_ne_zero hE hvw
  by_cases hww : B.h w w = 0
  · by_cases hvv : B.h v v = 0
    · refine ⟨w + c • v, key _ ?_⟩
      have expand : B.h (w + c • v) (w + c • v) = c * B.h v w + τ (c * B.h v w) := by
        rw [B.add_left, B.add_right, B.add_right, B.smul_left, B.smul_left, B.smul_right,
          B.smul_right, hww, hvv, B.symm v w, map_mul]
        ring
      rw [expand]
      exact hc
    · exact ⟨v, key v hvv⟩
  · exact ⟨w, key w hww⟩

end GlobalTheory.CompanionTheory.UnrDens
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianSpaceAnisotropicUnitStatement
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_space_anisotropic_unit : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε → ∀ (V : Type) [AddCommGroup V] [Module E V] (B : HermSp E τ V), Nontrivial V → ∃ w : V, IsUnit (B.h w w) := by
  first | exact @GlobalTheory.CompanionTheory.UnrDens.exists_unit_norm | exact GlobalTheory.CompanionTheory.UnrDens.exists_unit_norm | (intros; apply GlobalTheory.CompanionTheory.UnrDens.exists_unit_norm <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianVectorValuesCard
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens

namespace GlobalTheory.CompanionTheory.UnrDens.Sphere

theorem card_fibre {E : Type} [CommRing E] {τ : E →+* E} [Fintype E] {V : Type} [AddCommGroup V]
    [Module E V] [Finite V] (B : HermSp E τ V) {w : V} (hw : IsUnit (B.h w w)) (c : E) :
    Nat.card {v : V // B.h v v = c} =
      ∑ a : E, Nat.card {v : B.perp w // (B.perpForm hw).h v v = c - a * τ a * B.h w w} := by
  rw [← Nat.card_sigma]
  refine Nat.card_congr ?_
  have e1 : {x : E × B.perp w // (B.perpForm hw).h x.2 x.2 = c - x.1 * τ x.1 * B.h w w} ≃
      {v : V // B.h v v = c} :=
    Equiv.subtypeEquiv (B.perpEquiv hw) (by
      rintro ⟨a, v⟩
      have hv : B.h (v : V) w = 0 := v.2
      simp only [HermSp.perpEquiv_apply, HermSp.perpForm_h]
      rw [B.norm_perp hv a]
      constructor
      · intro h; rw [h]; ring
      · intro h; rw [← h]; ring)
  exact e1.symm.trans
    ⟨fun x => ⟨x.1.1, x.1.2, x.2⟩, fun s => ⟨(s.1, s.2.1), s.2.2⟩, fun _ => rfl, fun _ => rfl⟩

theorem sum_ite_card {E : Type} [Fintype E] (p : E → Prop) (A B₀ : ℝ) [DecidablePred p] :
    ∑ a, (if p a then B₀ else A) =
      (Nat.card {a // p a} : ℝ) * B₀ + ((Nat.card E : ℝ) - Nat.card {a // p a}) * A := by
  have h : ∀ a, (if p a then B₀ else A) = A + (B₀ - A) * (if p a then 1 else 0) := by
    intro a; split_ifs <;> ring
  simp only [h]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole, Finset.sum_const,
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp only [Finset.card_univ, nsmul_eq_mul]
  ring

theorem arith_unit (q ε x Q : ℝ) (hq : q ≠ 0) :
    (q - ε) * (Q / q * (1 + (q - 1) * x)) + (q ^ 2 - (q - ε)) * (Q / q * (1 - x)) =
      Q * q ^ 2 / q * (1 - x * (ε / q)) := by
  field_simp
  ring

theorem arith_zero (q ε x Q : ℝ) (hq : q ≠ 0) :
    (q * (1 + ε) - ε) * (Q / q * (1 + (q - 1) * x)) +
        (q ^ 2 - (q * (1 + ε) - ε)) * (Q / q * (1 - x)) =
      Q * q ^ 2 / q * (1 + (q - 1) * (x * (ε / q))) := by
  field_simp
  ring

theorem count : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε → ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module E V] (B : HermSp E τ V), Nat.card V = q ^ (2 * m) → (∀ c : E, τ c = c → c ≠ 0 → (Nat.card {v : V // B.h v v = c} : ℝ) = (q : ℝ) ^ (2 * m) / q * (1 - ((ε : ℝ) / q) ^ m)) ∧ (Nat.card {v : V // B.h v v = 0} : ℝ) = (q : ℝ) ^ (2 * m) / q * (1 + ((q : ℝ) - 1) * ((ε : ℝ) / q) ^ m) := by
  intro E _ τ q ε hR m
  have hq1 : 1 < q := hR.one_lt
  have hq0 : (q : ℝ) ≠ 0 := by
    have : 0 < q := by omega
    exact_mod_cast this.ne'
  induction m with
  | zero =>
    intro V _ _ B hc
    have hc1 : Nat.card V = 1 := by simpa using hc
    obtain ⟨hs, -⟩ := Nat.card_eq_one_iff_unique.1 hc1
    refine ⟨?_, ?_⟩
    · intro c _ hc0
      have : IsEmpty {v : V // B.h v v = c} :=
        ⟨fun x => hc0 (by
          have h := x.2
          rw [Subsingleton.elim x.1 0, B.zero_left] at h
          exact h.symm)⟩
      rw [Nat.card_of_isEmpty]
      simp
    · have : Subsingleton {v : V // B.h v v = 0} := inferInstance
      rw [Nat.card_of_subsingleton (⟨0, B.zero_left 0⟩ : {v : V // B.h v v = 0})]
      field_simp
      ring
  | succ m ih =>
    intro V _ _ B hc
    have hpow : 1 < q ^ (2 * (m + 1)) := Nat.one_lt_pow (by omega) hq1
    have hfin : Finite V := Nat.finite_of_card_ne_zero (by omega)
    have hfinE : Finite E := Nat.finite_of_card_ne_zero (by
      rw [hR.card]; exact pow_ne_zero _ (by omega))
    have hnt : Nontrivial V := Finite.one_lt_card_iff_nontrivial.1 (by omega)
    obtain ⟨w, hw⟩ := GlobalTheory.T.hermitian_space_anisotropic_unit E τ q ε hR V B hnt
    have hP : Nat.card (B.perp w) = q ^ (2 * m) := by
      have h1 : Nat.card E * Nat.card (B.perp w) = Nat.card V := by
        rw [← Nat.card_prod]; exact Nat.card_congr (B.perpEquiv hw)
      rw [hR.card, hc] at h1
      have hq2 : 0 < q ^ 2 := pow_pos (by omega) _
      apply Nat.eq_of_mul_eq_mul_left hq2
      rw [h1]; ring
    obtain ⟨ihc, ihz⟩ := ih (B.perp w) (B.perpForm hw) hP
    classical
    haveI := Fintype.ofFinite E
    have hdfix : τ (B.h w w) = B.h w w := (B.symm w w).symm
    obtain ⟨di, hdi⟩ : ∃ di, B.h w w * di = 1 := hw.exists_right_inv
    have hdifix : τ di = di := by
      have h1 : B.h w w * τ di = 1 := by
        have := congrArg τ hdi
        rwa [map_mul, hdfix, map_one] at this
      calc τ di = (B.h w w * di) * τ di := by rw [hdi, one_mul]
        _ = di * (B.h w w * τ di) := by ring
        _ = di := by rw [h1, mul_one]
    set A : ℝ := (q : ℝ) ^ (2 * m) / q * (1 - ((ε : ℝ) / q) ^ m) with hA
    set B₀ : ℝ := (q : ℝ) ^ (2 * m) / q * (1 + ((q : ℝ) - 1) * ((ε : ℝ) / q) ^ m) with hB₀
    have key : ∀ c : E, τ c = c → (Nat.card {v : V // B.h v v = c} : ℝ) =
        (Nat.card {a : E // a * τ a = c * di} : ℝ) * B₀ +
          ((q : ℝ) ^ 2 - Nat.card {a : E // a * τ a = c * di}) * A := by
      intro c hcf
      have hiff : ∀ a : E, a * τ a * B.h w w = c ↔ a * τ a = c * di := by
        intro a
        constructor
        · intro h
          rw [← h, mul_assoc, hdi, mul_one]
        · intro h
          rw [h, mul_assoc, mul_comm di, hdi, mul_one]
      have hterm : ∀ a : E,
          (Nat.card {v : B.perp w // (B.perpForm hw).h v v = c - a * τ a * B.h w w} : ℝ) =
            if a * τ a = c * di then B₀ else A := by
        intro a
        split_ifs with h
        · have h0 : c - a * τ a * B.h w w = 0 := by rw [(hiff a).2 h, sub_self]
          rw [h0]; exact ihz
        · refine ihc _ ?_ ?_
          · rw [map_sub, map_mul, map_mul, hcf, hdfix, hR.inv a]
            ring
          · intro h0
            exact h ((hiff a).1 (sub_eq_zero.1 h0).symm)
      rw [card_fibre B hw c]
      push_cast
      rw [Finset.sum_congr rfl (fun a _ => hterm a), sum_ite_card, hR.card]
      push_cast
      rfl
    have hpw : (q : ℝ) ^ (2 * (m + 1)) = (q : ℝ) ^ (2 * m) * (q : ℝ) ^ 2 := by ring
    refine ⟨?_, ?_⟩
    · intro c hcf hc0
      have hn : (Nat.card {a : E // a * τ a = c * di} : ℝ) = (q : ℝ) - ε := by
        have := GlobalTheory.T.norm_fibre_card_nonzero E τ q ε hR (c * di)
          (by rw [map_mul, hcf, hdifix])
          (by
            intro h0
            apply hc0
            calc c = c * (di * B.h w w) := by rw [mul_comm di, hdi, mul_one]
              _ = (c * di) * B.h w w := by ring
              _ = 0 := by rw [h0, zero_mul])
        exact_mod_cast this
      rw [key c hcf, hn, hpw, pow_succ ((ε : ℝ) / q) m]
      exact arith_unit _ _ _ _ hq0
    · have hn : (Nat.card {a : E // a * τ a = (0 : E) * di} : ℝ) = (q : ℝ) * (1 + ε) - ε := by
        have := GlobalTheory.T.norm_fibre_card_zero E τ q ε hR
        rw [zero_mul]
        exact_mod_cast this
      rw [key 0 (map_zero τ), hn, hpw, pow_succ ((ε : ℝ) / q) m]
      exact arith_zero _ _ _ _ hq0

end GlobalTheory.CompanionTheory.UnrDens.Sphere
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianVectorValuesCardStatement
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_vector_values_card : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε → ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module E V] (B : HermSp E τ V), Nat.card V = q ^ (2 * m) → (∀ c : E, τ c = c → c ≠ 0 → (Nat.card {v : V // B.h v v = c} : ℝ) = (q : ℝ) ^ (2 * m) / q * (1 - ((ε : ℝ) / q) ^ m)) ∧ (Nat.card {v : V // B.h v v = 0} : ℝ) = (q : ℝ) ^ (2 * m) / q * (1 + ((q : ℝ) - 1) * ((ε : ℝ) / q) ^ m) := by
  first | exact @GlobalTheory.CompanionTheory.UnrDens.Sphere.count | exact GlobalTheory.CompanionTheory.UnrDens.Sphere.count | (intros; apply GlobalTheory.CompanionTheory.UnrDens.Sphere.count <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardOrthonormalFramesHermitianSpace
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens

namespace GlobalTheory.CompanionTheory.UnrDens.OrthCount

variable {E : Type} [CommRing E] {τ : E →+* E} {V : Type} [AddCommGroup V] [Module E V]

abbrev Tuples (B : HermSp E τ V) (n : ℕ) : Type :=
  {x : Fin n → V // ∀ i j, B.h (x i) (x j) = if i = j then 1 else 0}

theorem isUnit_norm (B : HermSp E τ V) (w : {w : V // B.h w w = 1}) : IsUnit (B.h w.1 w.1) := by
  rw [w.2]; exact isUnit_one

noncomputable def consEquiv (B : HermSp E τ V) (n : ℕ) :
    Tuples B (n + 1) ≃
      Σ w : {w : V // B.h w w = 1}, Tuples (B.perpForm (isUnit_norm B w)) n where
  toFun x := ⟨⟨x.1 0, by simpa using x.2 0 0⟩,
    ⟨fun j => ⟨x.1 j.succ, by
      show B.h (x.1 j.succ) (x.1 0) = 0
      simpa [Fin.succ_ne_zero] using x.2 j.succ 0⟩, fun i j => by
      simpa using x.2 i.succ j.succ⟩⟩
  invFun p := ⟨Fin.cons p.1.1 (fun j => (p.2.1 j : V)), by
    obtain ⟨⟨w, hw⟩, ⟨y, hy⟩⟩ := p
    intro i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simpa using hw
    · have h0 : B.h (y j : V) w = 0 := (y j).2
      simp [B.symm (y j : V) w, h0, (Fin.succ_ne_zero j).symm]
    · have h0 : B.h (y i : V) w = 0 := (y i).2
      simp [h0, Fin.succ_ne_zero i]
    · simpa using hy i j⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    refine Fin.cases rfl (fun j => rfl) i
  right_inv p := by
    obtain ⟨⟨w, hw⟩, ⟨y, hy⟩⟩ := p
    rfl

end GlobalTheory.CompanionTheory.UnrDens.OrthCount

namespace GlobalTheory.CompanionTheory.UnrDens


open OrthCount in
theorem card_orthonormal_tuples : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε → ∀ (n m : ℕ), n ≤ m → ∀ (V : Type) [AddCommGroup V] [Module E V] (B : HermSp E τ V), Nat.card V = q ^ (2 * m) → (Nat.card {x : Fin n → V // ∀ i j, B.h (x i) (x j) = if i = j then 1 else 0} : ℝ) = ∏ i : Fin n, ((q : ℝ) ^ (2 * (m - (i : ℕ))) / q * (1 - ((ε : ℝ) / q) ^ (m - (i : ℕ)))) := by
  intro E _ τ q ε hR n
  induction n with
  | zero =>
    intro m _ V _ _ B _
    have h1 : Nat.card {x : Fin 0 → V // ∀ i j, B.h (x i) (x j) = if i = j then 1 else 0} = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun a b => Subtype.ext (funext fun i => i.elim0)⟩,
        ⟨⟨fun i => i.elim0, fun i => i.elim0⟩⟩⟩
    simp [h1]
  | succ n ih =>
    intro m hnm V _ _ B hc
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hq : 1 < q := hR.one_lt
    have hq0 : q ≠ 0 := by omega
    haveI : Finite V := Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ hq0)
    haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hR.card]; exact pow_ne_zero _ hq0)
    haveI : Nontrivial E := Finite.one_lt_card_iff_nontrivial.1 (by rw [hR.card]; nlinarith)
    have hsph := (GlobalTheory.T.hermitian_vector_values_card E τ q ε hR (m' + 1) V B hc).1 1 (map_one τ) one_ne_zero
    have hperp : ∀ w : {w : V // B.h w w = 1}, Nat.card (B.perp w.1) = q ^ (2 * m') := by
      intro w
      have h1 := Nat.card_congr (B.perpEquiv (isUnit_norm B w))
      rw [Nat.card_prod, hR.card, hc] at h1
      have h2 : q ^ (2 * (m' + 1)) = q ^ 2 * q ^ (2 * m') := by ring
      rw [h2] at h1
      exact Nat.eq_of_mul_eq_mul_left (pow_pos (by omega) 2) h1
    have hfib : ∀ w : {w : V // B.h w w = 1},
        (Nat.card (Tuples (B.perpForm (isUnit_norm B w)) n) : ℝ) =
          ∏ i : Fin n, ((q : ℝ) ^ (2 * (m' - (i : ℕ))) / q * (1 - ((ε : ℝ) / q) ^ (m' - (i : ℕ)))) :=
      fun w => ih m' (by omega) (B.perp w.1) (B.perpForm (isUnit_norm B w)) (hperp w)
    haveI : Fintype {w : V // B.h w w = 1} := Fintype.ofFinite _
    have hcard : (Nat.card (Tuples B (n + 1)) : ℝ) =
        (Nat.card {w : V // B.h w w = 1} : ℝ) *
          ∏ i : Fin n, ((q : ℝ) ^ (2 * (m' - (i : ℕ))) / q * (1 - ((ε : ℝ) / q) ^ (m' - (i : ℕ)))) := by
      rw [Nat.card_congr (consEquiv B n), Nat.card_sigma]
      push_cast
      rw [Finset.sum_congr rfl (fun w _ => hfib w), Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, Nat.card_eq_fintype_card]
    change (Nat.card (Tuples B (n + 1)) : ℝ) = _
    rw [hcard, hsph, Fin.prod_univ_succ]
    simp [Nat.add_sub_add_right]

end GlobalTheory.CompanionTheory.UnrDens
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardOrthonormalFramesHermitianSpaceStatement
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_orthonormal_frames_hermitian_space : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε → ∀ (n m : ℕ), n ≤ m → ∀ (V : Type) [AddCommGroup V] [Module E V] (B : HermSp E τ V), Nat.card V = q ^ (2 * m) → (Nat.card {x : Fin n → V // ∀ i j, B.h (x i) (x j) = if i = j then 1 else 0} : ℝ) = ∏ i : Fin n, ((q : ℝ) ^ (2 * (m - (i : ℕ))) / q * (1 - ((ε : ℝ) / q) ^ (m - (i : ℕ)))) := by
  first | exact @GlobalTheory.CompanionTheory.UnrDens.card_orthonormal_tuples | exact GlobalTheory.CompanionTheory.UnrDens.card_orthonormal_tuples | (intros; apply GlobalTheory.CompanionTheory.UnrDens.card_orthonormal_tuples <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardHermitianRepresentationsResidue
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsHermitianCongrToOne
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsHermitianCongrToOne
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens

namespace GlobalTheory.CompanionTheory.UnrDens

theorem exists_congr_one : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε →
    ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E), cT τ T = T → IsUnit T.det →
      ∃ g : Matrix (Fin n) (Fin n) E, IsUnit g.det ∧ cT τ g * T * g = 1 := by
  intro E _ τ q ε hR n T hT hdet
  have hinv : ∀ a : E, τ (τ a) = a := hR.inv
  have hq : 1 < q := hR.one_lt
  have hcard : Nat.card (Fin n → E) = q ^ (2 * n) := by
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin, hR.card, ← pow_mul]
  have hcnt := GlobalTheory.T.card_orthonormal_frames_hermitian_space E τ q ε hR n n le_rfl (Fin n → E) (HermSp.ofMatrix hinv T hT hdet) hcard
  have hε : ε = -1 ∨ ε = 1 := by
    rcases hR.eps with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  have hne : Nat.card {x : Fin n → Fin n → E // ∀ i j : Fin n,
      (HermSp.ofMatrix hinv T hT hdet).h (x i) (x j) = if i = j then 1 else 0} ≠ 0 := by
    intro h0
    rw [h0, Nat.cast_zero, eq_comm, Finset.prod_eq_zero_iff] at hcnt
    obtain ⟨i, -, hi⟩ := hcnt
    have hk : n - (i : ℕ) ≠ 0 := Nat.sub_ne_zero_of_lt i.isLt
    rcases mul_eq_zero.mp hi with h | h
    · rw [div_eq_zero_iff] at h
      rcases h with h | h
      · have h' := pow_eq_zero_iff (n := 2 * (n - (i : ℕ))) (by omega) |>.mp h
        rw [Nat.cast_eq_zero] at h'
        omega
      · rw [Nat.cast_eq_zero] at h
        omega
    · rw [sub_eq_zero] at h
      have h2 := congrArg abs h
      rw [abs_one, abs_pow, abs_div, Nat.abs_cast] at h2
      have key : ∀ {F : Type} [Field F] [LinearOrder F] [IsStrictOrderedRing F] (e : ℤ) (k : ℕ),
          (e = -1 ∨ e = 1) → k ≠ 0 → (1 : F) ≠ (|(e : F)| / (q : F)) ^ k := by
        intro F _ _ _ e k he hk' hh
        have hqF : (1 : F) < q := by exact_mod_cast hq
        have habs : |(e : F)| = 1 := by
          rcases he with rfl | rfl <;> simp
        rw [habs] at hh
        have hlt : (1 / (q : F)) ^ k < 1 :=
          pow_lt_one₀ (by positivity) ((div_lt_one (by linarith)).mpr hqF) hk'
        linarith
      exact key ε _ hε hk h2
  obtain ⟨⟨x, hx⟩⟩ := (Nat.card_ne_zero.mp hne).1
  have hg : cT τ (Matrix.of fun a i => x i a) * T * (Matrix.of fun a i => x i a) = 1 := by
    ext i j
    rw [gram_apply hinv T hT hdet]
    show (HermSp.ofMatrix hinv T hT hdet).h (x j) (x i) = (1 : Matrix (Fin n) (Fin n) E) i j
    rw [hx j i, Matrix.one_apply]
    by_cases h : i = j
    · subst h
      simp
    · rw [if_neg (Ne.symm h), if_neg h]
  exact ⟨_, Matrix.isUnit_det_of_left_inverse hg, hg⟩

end GlobalTheory.CompanionTheory.UnrDens
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsHermitianCongrToOneStatement
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hermitian_congr_to_one : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E), cT τ T = T → IsUnit T.det → ∃ g : Matrix (Fin n) (Fin n) E, IsUnit g.det ∧ cT τ g * T * g = 1 := by
  first | exact @GlobalTheory.CompanionTheory.UnrDens.exists_congr_one | exact GlobalTheory.CompanionTheory.UnrDens.exists_congr_one | (intros; apply GlobalTheory.CompanionTheory.UnrDens.exists_congr_one <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardHermitianRepresentationsResidue
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens

namespace GlobalTheory.CompanionTheory.UnrDens.Emb

variable {E : Type} [CommRing E] {τ : E →+* E}

theorem cT_mul_rect {a b c : ℕ} (x : Matrix (Fin a) (Fin b) E) (y : Matrix (Fin b) (Fin c) E) :
    cT τ (x * y) = cT τ y * cT τ x := by
  unfold cT
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem cT_one_sq {a : ℕ} : cT τ (1 : Matrix (Fin a) (Fin a) E) = 1 := by
  unfold cT
  rw [Matrix.map_one _ (map_zero τ) (map_one τ), Matrix.transpose_one]

theorem card_eq_card_one {m n : ℕ} (S : Matrix (Fin m) (Fin m) E) (T g : Matrix (Fin n) (Fin n) E)
    (hg : IsUnit g.det) (hgT : cT τ g * T * g = 1) :
    Nat.card {x : Matrix (Fin m) (Fin n) E // cT τ x * S * x = T} =
      Nat.card {y : Matrix (Fin m) (Fin n) E // cT τ y * S * y = 1} := by
  have hgh : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hg
  have hhg : cT τ g⁻¹ * cT τ g = 1 := by rw [← cT_mul_rect, hgh, cT_one_sq]
  have hT : T = cT τ g⁻¹ * g⁻¹ := by
    calc T = (cT τ g⁻¹ * cT τ g) * T * (g * g⁻¹) := by rw [hhg, hgh, Matrix.one_mul, Matrix.mul_one]
      _ = cT τ g⁻¹ * (cT τ g * T * g) * g⁻¹ := by simp only [Matrix.mul_assoc]
      _ = cT τ g⁻¹ * g⁻¹ := by rw [hgT, Matrix.mul_one]
  refine Nat.card_congr ⟨fun x => ⟨x.1 * g, ?_⟩, fun y => ⟨y.1 * g⁻¹, ?_⟩, ?_, ?_⟩
  · rw [cT_mul_rect]
    calc cT τ g * cT τ x.1 * S * (x.1 * g) = cT τ g * (cT τ x.1 * S * x.1) * g := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [x.2, hgT]
  · rw [cT_mul_rect]
    calc cT τ g⁻¹ * cT τ y.1 * S * (y.1 * g⁻¹) = cT τ g⁻¹ * (cT τ y.1 * S * y.1) * g⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = T := by rw [y.2, Matrix.mul_one, ← hT]
  · intro x
    apply Subtype.ext
    show x.1 * g * g⁻¹ = x.1
    rw [Matrix.mul_assoc, hgh, Matrix.mul_one]
  · intro y
    apply Subtype.ext
    show y.1 * g⁻¹ * g = y.1
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul g hg, Matrix.mul_one]

theorem card_one_eq_orthonormal (hτ : ∀ a, τ (τ a) = a) {m n : ℕ} (S : Matrix (Fin m) (Fin m) E)
    (hS : cT τ S = S) (hd : IsUnit S.det) :
    Nat.card {y : Matrix (Fin m) (Fin n) E // cT τ y * S * y = 1} =
      Nat.card {x : Fin n → (Fin m → E) //
        ∀ i j, (HermSp.ofMatrix hτ S hS hd).h (x i) (x j) = if i = j then 1 else 0} := by
  refine Nat.card_congr ⟨fun y => ⟨fun j a => y.1 a j, ?_⟩,
    fun x => ⟨Matrix.of (fun a j => x.1 j a), ?_⟩, ?_, ?_⟩
  · intro i j
    have h := gram_apply hτ S hS hd y.1 j i
    rw [y.2, Matrix.one_apply] at h
    rw [← h]
    simp only [eq_comm]
  · ext i j
    rw [gram_apply hτ S hS hd, Matrix.one_apply]
    have h := x.2 j i
    simp only [eq_comm (a := i)]
    exact h
  · intro y
    apply Subtype.ext
    ext a j
    rfl
  · intro x
    apply Subtype.ext
    funext j a
    rfl

theorem prod_pow_div (x : ℝ) (hx : x ≠ 0) (n : ℕ) : ∀ m : ℕ, n ≤ m →
    ∏ i : Fin n, (x ^ (2 * (m - (i : ℕ))) / x) = x ^ (2 * m * n - n ^ 2) := by
  induction n with
  | zero => intro m _; simp
  | succ n ih =>
    intro m hnm
    obtain ⟨k, rfl⟩ : ∃ k, m = n + 1 + k := ⟨m - (n + 1), by omega⟩
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih _ (by omega)]
    have a : 2 * (n + 1 + k) * n - n ^ 2 = n ^ 2 + 2 * n + 2 * k * n := by
      apply Nat.sub_eq_of_eq_add; ring
    have b : 2 * (n + 1 + k) * (n + 1) - (n + 1) ^ 2 = (n + 1) ^ 2 + 2 * k * (n + 1) := by
      apply Nat.sub_eq_of_eq_add; ring
    have c : n + 1 + k - n = k + 1 := by omega
    have d : x ^ (2 * (k + 1)) / x = x ^ (2 * k + 1) := by
      have : x ^ (2 * (k + 1)) = x ^ (2 * k + 1) * x := by ring
      rw [this, mul_div_cancel_right₀ _ hx]
    rw [a, b, c, d, ← pow_add]
    congr 1
    ring

theorem card_isometric_embeddings : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ),
    ResAlg E τ q ε → ∀ (m n : ℕ), n ≤ m → ∀ (S : Matrix (Fin m) (Fin m) E)
    (T : Matrix (Fin n) (Fin n) E), cT τ S = S → IsUnit S.det → cT τ T = T → IsUnit T.det →
    (Nat.card {x : Matrix (Fin m) (Fin n) E // cT τ x * S * x = T} : ℝ) =
      (q : ℝ) ^ (2 * m * n - n ^ 2) * ∏ i : Fin n, (1 - ((ε : ℝ) / q) ^ (m - (i : ℕ))) := by
  intro E _ τ q ε hR m n hnm S T hS hSd hT hTd
  obtain ⟨g, hg, hgT⟩ := GlobalTheory.T.exists_hermitian_congr_to_one E τ q ε hR n T hT hTd
  have hcard : Nat.card (Fin m → E) = q ^ (2 * m) := by
    rw [Nat.card_fun, hR.card, Nat.card_eq_fintype_card, Fintype.card_fin, pow_mul]
  have hq : (q : ℝ) ≠ 0 := by
    have := hR.one_lt
    exact_mod_cast (by omega : q ≠ 0)
  rw [card_eq_card_one S T g hg hgT, card_one_eq_orthonormal hR.inv S hS hSd,
    GlobalTheory.T.card_orthonormal_frames_hermitian_space E τ q ε hR n m hnm (Fin m → E) (HermSp.ofMatrix hR.inv S hS hSd) hcard,
    Finset.prod_mul_distrib, prod_pow_div _ hq n m hnm]

end GlobalTheory.CompanionTheory.UnrDens.Emb
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardHermitianRepresentationsResidueStatement
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_hermitian_representations_residue : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε → ∀ (m n : ℕ), n ≤ m → ∀ (S : Matrix (Fin m) (Fin m) E) (T : Matrix (Fin n) (Fin n) E), cT τ S = S → IsUnit S.det → cT τ T = T → IsUnit T.det → (Nat.card {x : Matrix (Fin m) (Fin n) E // cT τ x * S * x = T} : ℝ) = (q : ℝ) ^ (2 * m * n - n ^ 2) * ∏ i : Fin n, (1 - ((ε : ℝ) / q) ^ (m - (i : ℕ))) := by
  first | exact @GlobalTheory.CompanionTheory.UnrDens.Emb.card_isometric_embeddings | exact GlobalTheory.CompanionTheory.UnrDens.Emb.card_isometric_embeddings | (intros; apply GlobalTheory.CompanionTheory.UnrDens.Emb.card_isometric_embeddings <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardUnimodularHermitianRepsLevelOne
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens

namespace GlobalTheory.CompanionTheory.UnrDens

theorem red_cT_one {R : Type} [CommRing R] (σ : R →+* R) (ϖ : R) (h : σ ϖ = ϖ) {a b : ℕ}
    (x : Matrix (Fin a) (Fin b) R) :
    red ϖ 1 (cT σ x) = cT (barσ σ ϖ h 1) (red ϖ 1 x) := by
  ext i j
  simp only [red, cT, Matrix.map_apply, Matrix.transpose_apply, barσ_mk]

theorem red_mul_one {R : Type} [CommRing R] (ϖ : R) {a b c : ℕ}
    (x : Matrix (Fin a) (Fin b) R) (y : Matrix (Fin b) (Fin c) R) :
    red ϖ 1 (x * y) = red ϖ 1 x * red ϖ 1 y := by
  simp only [red]
  exact Matrix.map_mul

theorem red_surj_one {R : Type} [CommRing R] (ϖ : R) {a b : ℕ}
    (y : Matrix (Fin a) (Fin b) (R ⧸ lev ϖ 1)) : ∃ x, red ϖ 1 x = y := by
  refine ⟨Matrix.of fun i j => (Ideal.Quotient.mk_surjective (y i j)).choose, ?_⟩
  ext i j
  simp only [red, Matrix.map_apply, Matrix.of_apply]
  exact (Ideal.Quotient.mk_surjective (y i j)).choose_spec

theorem isUnit_det_red_one {R : Type} [CommRing R] (ϖ : R) {a : ℕ}
    (x : Matrix (Fin a) (Fin a) R) (hx : IsUnit x.det) : IsUnit (red ϖ 1 x).det := by
  have e : (red ϖ 1 x).det = Ideal.Quotient.mk (lev ϖ 1) x.det := by
    rw [RingHom.map_det]
    rfl
  rw [e]
  exact hx.map _

theorem red_image_one {R : Type} [CommRing R] (σ : R →+* R) (ϖ : R) (h : σ ϖ = ϖ) {m n : ℕ}
    (S : Matrix (Fin m) (Fin m) R) (T : Matrix (Fin n) (Fin n) R) :
    red ϖ 1 '' {x : Matrix (Fin m) (Fin n) R | red ϖ 1 (cT σ x * S * x) = red ϖ 1 T} =
      {y | cT (barσ σ ϖ h 1) y * red ϖ 1 S * y = red ϖ 1 T} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [red_mul_one, red_mul_one, red_cT_one σ ϖ h] at hx
    exact hx
  · intro hy
    obtain ⟨x, rfl⟩ := red_surj_one ϖ y
    simp only [Set.mem_setOf_eq] at hy
    refine ⟨x, ?_, rfl⟩
    simp only [Set.mem_setOf_eq]
    rw [red_mul_one, red_mul_one, red_cT_one σ ϖ h]
    exact hy

theorem solCount_one : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ), IsUnrQuad R σ ϖ q ε → ∀ (m n : ℕ), n ≤ m → ∀ (S : Matrix (Fin m) (Fin m) R) (T : Matrix (Fin n) (Fin n) R), IsUnimod σ S → IsUnimod σ T → (solCount σ ϖ S T 1 : ℝ) = (q : ℝ) ^ (2 * m * n - n ^ 2) * ∏ i : Fin n, (1 - ((ε : ℝ) / q) ^ (m - (i : ℕ))) := by
  intro R _ σ ϖ q ε hR m n hnm S T hS hT
  have hS' : cT σ S = S ∧ IsUnit S.det := hS
  have hT' : cT σ T = T ∧ IsUnit T.det := hT
  have h1 : cT (barσ σ ϖ hR.fix_ϖ 1) (red ϖ 1 S) = red ϖ 1 S := by
    rw [← red_cT_one σ ϖ hR.fix_ϖ, hS'.1]
  have h2 : cT (barσ σ ϖ hR.fix_ϖ 1) (red ϖ 1 T) = red ϖ 1 T := by
    rw [← red_cT_one σ ϖ hR.fix_ϖ, hT'.1]
  unfold solCount
  rw [red_image_one σ ϖ hR.fix_ϖ S T]
  exact GlobalTheory.T.card_hermitian_representations_residue (R ⧸ lev ϖ 1) (barσ σ ϖ hR.fix_ϖ 1) q ε
    (resAlg_of_isUnrQuad R σ ϖ q ε hR) m n hnm (red ϖ 1 S) (red ϖ 1 T) h1
    (isUnit_det_red_one ϖ S hS'.2) h2 (isUnit_det_red_one ϖ T hT'.2)

end GlobalTheory.CompanionTheory.UnrDens
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardUnimodularHermitianRepsLevelOneStatement
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_unimodular_hermitian_reps_level_one : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ), IsUnrQuad R σ ϖ q ε → ∀ (m n : ℕ), n ≤ m → ∀ (S : Matrix (Fin m) (Fin m) R) (T : Matrix (Fin n) (Fin n) R), IsUnimod σ S → IsUnimod σ T → (solCount σ ϖ S T 1 : ℝ) = (q : ℝ) ^ (2 * m * n - n ^ 2) * ∏ i : Fin n, (1 - ((ε : ℝ) / q) ^ (m - (i : ℕ))) := by
  first | exact @GlobalTheory.CompanionTheory.UnrDens.solCount_one | exact GlobalTheory.CompanionTheory.UnrDens.solCount_one | (intros; apply GlobalTheory.CompanionTheory.UnrDens.solCount_one <;> assumption)
end
