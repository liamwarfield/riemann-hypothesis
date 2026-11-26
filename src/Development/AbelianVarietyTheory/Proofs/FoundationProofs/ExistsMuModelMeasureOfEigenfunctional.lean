module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CentralIdempotentIrreducibleCharacterProps

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MuModelProductIsModularFormCoeffSeqLocallyAlgebr
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MuModelProductIsModularFormCoeffSeqLocallyAlgebr
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM.ZmChar

theorem ch_mul {M : ℕ} (χ : DirichletCharacter ℂ M) (x y : ℤ) : ch χ (x * y) = ch χ x * ch χ y := by
  simp [ch]

theorem ch_add_dvd {M : ℕ} (χ : DirichletCharacter ℂ M) (K : ℕ) (h : M ∣ K) (x : ℤ) : ch χ (x + K) = ch χ x := by
  obtain ⟨t, rfl⟩ := h
  simp [ch, ZMod.natCast_self]

theorem ch_zero {M : ℕ} [Fact (1 < M)] (χ : DirichletCharacter ℂ M) : ch χ 0 = 0 := by
  simp only [ch, Int.cast_zero]
  exact MulChar.map_nonunit χ not_isUnit_zero

theorem inv_apply_neg_one {M : ℕ} (χ : DirichletCharacter ℂ M) : χ⁻¹ (-1) = χ (-1) := by
  rw [MulChar.inv_apply]
  have : Ring.inverse (-1 : ZMod M) = -1 := by simpa using Ring.inverse_unit (-1 : (ZMod M)ˣ)
  rw [this]

theorem isUnit_of_coprime {M : ℕ} (d : ℤ) (h : IsCoprime d (M : ℤ)) : IsUnit (d : ZMod M) := by
  obtain ⟨a, b, hab⟩ := h
  have := congrArg (Int.cast : ℤ → ZMod M) hab
  push_cast at this
  simp [ZMod.natCast_self] at this
  exact isUnit_iff_exists_inv.2 ⟨a, by rw [mul_comm]; exact this⟩

theorem mul_inv_unit {M : ℕ} (χ : DirichletCharacter ℂ M) (d : ℤ) (h : IsUnit (d : ZMod M)) : ch χ d * ch χ⁻¹ d = 1 := by
  show χ (d : ZMod M) * χ⁻¹ (d : ZMod M) = 1
  rw [← MulChar.mul_apply, mul_inv_cancel]
  exact MulChar.one_apply h

end GlobalTheory.EisM.ZmChar

namespace GlobalTheory.EisM.ZmChar

theorem cop_dvd {d : ℤ} {A B : ℕ} (h : IsCoprime d (B : ℤ)) (hAB : A ∣ B) : IsCoprime d (A : ℤ) :=
  h.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.2 hAB)

end GlobalTheory.EisM.ZmChar


open GlobalTheory.EisM.ZmChar in
theorem GlobalTheory.zm_char_mf : ∀ (k j N l m : ℕ) (ε : DirichletCharacter ℂ N) (u : ℤ → ℂ) (θ ν : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ (l ^ m)), j + 2 ≤ k → 0 < N → l.Prime → 1 ≤ m → ¬ l ∣ N → (∀ x, u (x + N) = u x) → (∀ d x : ℤ, IsCoprime d N → u (x * d) = ch θ⁻¹ d * u x) → ε = θ⁻¹ * ν → ψ (-1) * θ (-1) = (-1) ^ (k - 1 - j) → ψ (-1) * ν (-1) = (-1) ^ (j + 1) → MF k (N * l ^ (m + 1)) (ch ε) (Zm k l u (ch ν) (fun x y => ch ψ x * ch ψ⁻¹ y * ((y : ℂ) / x) ^ j)) := by
  intro k j N l m ε u θ ν ψ hjk hN hl hm hlN hu hmul hε hpar1 hpar2
  have hl1 : 1 < l ^ m := Nat.one_lt_pow (by omega) hl.one_lt
  haveI : Fact (1 < l ^ m) := ⟨hl1⟩
  have hlm : 0 < l ^ m := by omega
  have hup : ∀ K : ℕ, N ∣ K → ∀ x, u (x + K) = u x := by
    intro K hK x
    obtain ⟨t, rfl⟩ := hK
    have e : ((N * t : ℕ) : ℤ) = (t : ℤ) * N := by push_cast; ring
    rw [e]
    exact (Function.Periodic.nat_mul (show Function.Periodic u (N : ℤ) from hu) t) x
  obtain ⟨c, hE1⟩ := GlobalTheory.T.eisenstein_periodic_weights_isModularForm (k - 1 - j) (N * l ^ m) 1 (fun x => u x * ch ψ x) (fun _ => 1)
    (fun d => ch θ⁻¹ d * ch ψ d) (fun _ => 1) (by omega) (by positivity) one_pos (by simp [ch_zero])
    (fun x => by rw [hup _ (dvd_mul_right _ _), ch_add_dvd _ _ (dvd_mul_left _ _)]) (fun _ => rfl)
    (fun d hd => by
      have hdN : IsCoprime d (N : ℤ) := cop_dvd hd (by simp)
      refine ⟨fun x => ?_, fun x => by ring⟩
      rw [hmul d x hdN, ch_mul]
      ring)
    (by simp only [ch, Int.cast_neg, Int.cast_one, mul_one]; rw [inv_apply_neg_one, mul_comm, hpar1])
  obtain ⟨c', hE2⟩ := GlobalTheory.T.eisenstein_periodic_weights_isModularForm (j + 1) (l ^ m) N (ch ψ⁻¹) (ch ν) (ch ψ⁻¹) (ch ν) (by omega) hlm hN
    (ch_zero _) (ch_add_dvd _ _ dvd_rfl) (ch_add_dvd _ _ dvd_rfl)
    (fun d _ => ⟨fun x => by rw [ch_mul, mul_comm], fun x => by rw [ch_mul, mul_comm]⟩)
    (by simp only [ch, Int.cast_neg, Int.cast_one]; rw [inv_apply_neg_one, hpar2])
  have hD1 := (GlobalTheory.T.isModularFormCoeffSeq_heckeU_and_depletion (k - 1 - j) (N * l ^ m * 1) l _ _ (by omega) hl
    (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (dvd_pow_self l (by omega)) _) _)
    (fun d => by rw [ch_add_dvd _ _ (dvd_mul_of_dvd_left (dvd_mul_right _ _) _),
      ch_add_dvd _ _ (dvd_mul_of_dvd_left (dvd_mul_left _ _) _)]) hE1).2
  have hD2 := (GlobalTheory.T.isModularFormCoeffSeq_heckeU_and_depletion (j + 1) (l ^ m * N) l _ _ (by omega) hl
    (dvd_mul_of_dvd_left (dvd_pow_self l (by omega)) _)
    (fun d => by rw [ch_add_dvd _ _ (dvd_mul_right _ _), ch_add_dvd _ _ (dvd_mul_left _ _)]) hE2).2
  have hD1' := (GlobalTheory.EisM.mf_linear _ _ _).2.2.2.2.1 (N * l ^ (m + 1)) _ ⟨1, by ring⟩ hD1
  have hD2' := (GlobalTheory.EisM.mf_linear _ _ _).2.2.2.2.1 (N * l ^ (m + 1)) _ ⟨1, by ring⟩ hD2
  have P := GlobalTheory.EisM.mul_main.2 _ _ _ _ _ _ _ hD1' hD2'
  rw [GlobalTheory.T.eisensteinProductSeries_eq_depleted_eisenstein_product k l j u (ch ν) (ch ψ) (ch ψ⁻¹) c c' hjk]
  have hk : k - 1 - j + (j + 1) = k := by omega
  rw [hk] at P
  refine (GlobalTheory.EisM.mf_linear _ _ _).2.2.2.1 (ch ε) _ (fun d hd => ?_) P
  have hU := mul_inv_unit ψ d (isUnit_of_coprime d (cop_dvd hd (dvd_mul_of_dvd_right (pow_dvd_pow l (by omega)) _)))
  subst hε
  simp only [ch, MulChar.mul_apply] at hU ⊢
  linear_combination (θ⁻¹ (d : ZMod N) * ν (d : ZMod N)) * hU
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MuModelProductIsModularFormCoeffSeqLocallyAlgebrStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.muModelProduct_isModularFormCoeffSeq_locallyAlgebraic : ∀ (k j N l m : ℕ) (ε : DirichletCharacter ℂ N) (u : ℤ → ℂ) (θ ν : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ (l ^ m)), j + 2 ≤ k → 0 < N → l.Prime → 1 ≤ m → ¬ l ∣ N → (∀ x, u (x + N) = u x) → (∀ d x : ℤ, IsCoprime d N → u (x * d) = ch θ⁻¹ d * u x) → ε = θ⁻¹ * ν → ψ (-1) * θ (-1) = (-1) ^ (k - 1 - j) → ψ (-1) * ν (-1) = (-1) ^ (j + 1) → MF k (N * l ^ (m + 1)) (ch ε) (Zm k l u (ch ν) (fun x y => ch ψ x * ch ψ⁻¹ y * ((y : ℂ) / x) ^ j)) := by
  first | exact @GlobalTheory.zm_char_mf | exact GlobalTheory.zm_char_mf | (intros; apply GlobalTheory.zm_char_mf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsModularFormCoeffSeqEisensteinProductParity
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsModularFormCoeffSeqEisensteinProductParity
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem zmf_congr_cop {k l : ℕ} (u v : ℤ → ℂ) (F G : ℕ → ℕ → ℂ)
    (h : ∀ x y : ℕ, ¬ l ∣ x → ¬ l ∣ y → F x y = G x y) : Zm k l u v F = Zm k l u v G := by
  funext n
  unfold Zm
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_
  split_ifs with hp
  · rfl
  · push_neg at hp
    rw [Nat.mem_divisorsAntidiagonal] at hx hy
    have hx' : ¬ l ∣ x.1 := fun hd => hp.1 (hx.1 ▸ dvd_mul_of_dvd_left hd _)
    have hy' : ¬ l ∣ y.2 := fun hd => hp.2 (hy.1 ▸ dvd_mul_of_dvd_right hd _)
    rw [h _ _ hx' hy']

theorem zmf_sum_smul {ι : Type*} (s : Finset ι) (k l : ℕ) (u v : ℤ → ℂ) (c : ι → ℂ) (G : ι → ℕ → ℕ → ℂ) :
    Zm k l u v (fun x y => ∑ i ∈ s, c i * G i x y) = ∑ i ∈ s, c i • Zm k l u v (G i) := by
  funext n
  simp only [Zm, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  split_ifs
  · simp
  · refine Finset.sum_congr rfl fun i _ => ?_
    ring

theorem zmf_mf_sum {ι : Type*} (s : Finset ι) (k L : ℕ) (χ : ℤ → ℂ) (g : ι → ℕ → ℂ)
    (h : ∀ i ∈ s, MF k L χ (g i)) : MF k L χ (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (GlobalTheory.T.modularFormCoeffSeq_linear_structure k L χ).1
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact ((GlobalTheory.T.modularFormCoeffSeq_linear_structure k L χ).2.1 _ _ (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))).1

theorem zm_fun_mf : ∀ (k N l m : ℕ) (ε θ ν : DirichletCharacter ℂ N) (f : ZMod (l ^ m) → ℂ), 3 ≤ k → Odd k → 0 < N → l.Prime → 1 ≤ m → ¬ l ∣ N → ε = θ⁻¹ * ν → ν (-1) = -θ (-1) → (∀ x, f (-x) = θ (-1) * f x) → MF k (N * l ^ (m + 1)) (ch ε) (Zm k l (hat θ) (ch ν) (fun A d => f ((A : ZMod (l ^ m)) * (d : ZMod (l ^ m))⁻¹))) := by
  intro k N l m ε θ ν f hk hodd hN hl hm hlN hε hν hf
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ hl.ne_zero⟩
  set φ : ℂ := ((l ^ m).totient : ℂ) with hφ
  have hφ0 : φ ≠ 0 := by
    rw [hφ]; exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero (pow_ne_zero _ hl.ne_zero))).ne'
  set c : DirichletCharacter ℂ (l ^ m) → ℂ := fun ψ => φ⁻¹ * ∑ u : (ZMod (l ^ m))ˣ, f u * ψ⁻¹ u with hc
  have hinv : ∀ (ψ : DirichletCharacter ℂ (l ^ m)) (u : (ZMod (l ^ m))ˣ),
      ψ⁻¹ (u : ZMod (l ^ m)) = ψ ((u : ZMod (l ^ m))⁻¹) := by
    intro ψ u; rw [MulChar.inv_apply, Ring.inverse_unit, ZMod.inv_coe_unit]
  have hexp : ∀ w : (ZMod (l ^ m))ˣ, f w = ∑ ψ, c ψ * ψ w := by
    intro w
    calc f w = φ⁻¹ * (f w * φ) := by field_simp
      _ = φ⁻¹ * ∑ u : (ZMod (l ^ m))ˣ, f u * (if (u : ZMod (l ^ m)) = w then φ else 0) := by
          congr 1
          simp only [Units.val_inj, mul_ite, mul_zero]
          rw [Finset.sum_ite_eq']; simp
      _ = φ⁻¹ * ∑ u : (ZMod (l ^ m))ˣ, f u * ∑ ψ : DirichletCharacter ℂ (l ^ m), ψ ((u : ZMod (l ^ m))⁻¹) * ψ w := by
          congr 1
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ u.isUnit]
      _ = ∑ ψ, c ψ * ψ w := by
          simp only [hc, hinv, Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun ψ _ => Finset.sum_congr rfl fun u _ => ?_
          ring
  have hquo : Zm k l (hat θ) (ch ν) (fun A d => f ((A : ZMod (l ^ m)) * (d : ZMod (l ^ m))⁻¹)) = Zm k l (hat θ) (ch ν)
      (fun x y => ∑ ψ : DirichletCharacter ℂ (l ^ m), c ψ * (ch ψ x * ch ψ⁻¹ y * ((y : ℂ) / x) ^ 0)) := by
    apply zmf_congr_cop
    intro x y hx hy
    have cx : Nat.Coprime x (l ^ m) := (Nat.Coprime.pow_left m ((hl.coprime_iff_not_dvd).2 hx)).symm
    have cy : Nat.Coprime y (l ^ m) := (Nat.Coprime.pow_left m ((hl.coprime_iff_not_dvd).2 hy)).symm
    set ux := ZMod.unitOfCoprime x cx
    set uy := ZMod.unitOfCoprime y cy
    have ex : ((x : ℤ) : ZMod (l ^ m)) = ux := by simp [ux, ZMod.coe_unitOfCoprime]
    have ey : ((y : ℤ) : ZMod (l ^ m)) = uy := by simp [uy, ZMod.coe_unitOfCoprime]
    have ex' : (x : ZMod (l ^ m)) = ux := by simp [ux, ZMod.coe_unitOfCoprime]
    have ey' : (y : ZMod (l ^ m)) = uy := by simp [uy, ZMod.coe_unitOfCoprime]
    simp only [ch, ex, ey, ex', ey', pow_zero, mul_one, hinv]
    rw [ZMod.inv_coe_unit, ← Units.val_mul, hexp]
    refine Finset.sum_congr rfl fun ψ _ => ?_
    rw [← map_mul, ← Units.val_mul]
  rw [hquo, zmf_sum_smul]
  apply zmf_mf_sum
  intro ψ _
  have hsq : ∀ {M : ℕ} (χ : DirichletCharacter ℂ M), χ (-1) * χ (-1) = 1 := by
    intro M χ; rw [← map_mul, neg_one_mul, neg_neg, map_one]
  have hh := (GlobalTheory.T.dirichletCharFiniteFourierTransform_properties).1 N θ hN
  by_cases hψ : ψ (-1) = θ (-1)
  · have h1 : ψ (-1) * θ (-1) = (-1) ^ (k - 1 - 0) := by
      obtain ⟨r, rfl⟩ := hodd
      rw [hψ, hsq, show 2 * r + 1 - 1 - 0 = 2 * r by omega, pow_mul]; norm_num
    have h2 : ψ (-1) * ν (-1) = (-1) ^ (0 + 1) := by
      rw [hψ, hν, mul_neg, hsq]; norm_num
    exact ((GlobalTheory.T.modularFormCoeffSeq_linear_structure k _ (ch ε)).2.2.1 (c ψ) _
      (GlobalTheory.T.muModelProduct_isModularFormCoeffSeq_locallyAlgebraic k 0 N l m ε (hat θ) θ ν ψ (by omega) hN hl hm hlN hh.1 hh.2.1 hε h1 h2)).1
  · have hc0 : c ψ = 0 := by
      have hpm : ∀ {M : ℕ} (χ : DirichletCharacter ℂ M), χ (-1) = 1 ∨ χ (-1) = -1 := by
        intro M χ
        have := hsq χ
        have h' : (χ (-1) - 1) * (χ (-1) + 1) = 0 := by linear_combination this
        rcases mul_eq_zero.1 h' with h | h
        · left; linear_combination h
        · right; linear_combination h
      have hprod : θ (-1) * ψ⁻¹ (-1) = -1 := by
        have hi : ψ⁻¹ (-1) = ψ (-1) := by
          rw [MulChar.inv_apply, show (-1 : ZMod (l ^ m)) = ((-1 : (ZMod (l ^ m))ˣ) : ZMod (l ^ m)) by simp, Ring.inverse_unit, inv_neg_one]
        rw [hi]
        rcases hpm θ with h | h <;> rcases hpm ψ with h' | h' <;> rw [h, h'] at hψ ⊢
        all_goals first | exact absurd rfl hψ | norm_num
      set S := ∑ u : (ZMod (l ^ m))ˣ, f u * ψ⁻¹ u with hS
      have hS' : S = - S := by
        calc S = ∑ u : (ZMod (l ^ m))ˣ, f ((-u : (ZMod (l ^ m))ˣ) : ZMod (l ^ m)) * ψ⁻¹ ((-u : (ZMod (l ^ m))ˣ) : ZMod (l ^ m)) :=
              (Fintype.sum_equiv (Equiv.neg _) _ _ (fun _ => rfl)).symm
          _ = ∑ u : (ZMod (l ^ m))ˣ, (θ (-1) * ψ⁻¹ (-1)) * (f u * ψ⁻¹ u) := by
              refine Finset.sum_congr rfl fun u _ => ?_
              rw [Units.val_neg, hf, neg_eq_neg_one_mul (u : ZMod (l ^ m)), map_mul]
              ring
          _ = - S := by rw [← Finset.mul_sum, hprod, neg_one_mul]
      have : S = 0 := by linear_combination hS' / 2
      simp [hc, ← hS, this]
    rw [hc0, zero_smul]
    exact (GlobalTheory.T.modularFormCoeffSeq_linear_structure k _ (ch ε)).1

end GlobalTheory.EisM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsModularFormCoeffSeqEisensteinProductParityStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isModularFormCoeffSeq_eisensteinProduct_parity : ∀ (k N l m : ℕ) (ε θ ν : DirichletCharacter ℂ N) (f : ZMod (l ^ m) → ℂ), 3 ≤ k → Odd k → 0 < N → l.Prime → 1 ≤ m → ¬ l ∣ N → ε = θ⁻¹ * ν → ν (-1) = -θ (-1) → (∀ x, f (-x) = θ (-1) * f x) → MF k (N * l ^ (m + 1)) (ch ε) (Zm k l (hat θ) (ch ν) (fun A d => f ((A : ZMod (l ^ m)) * (d : ZMod (l ^ m))⁻¹))) := by
  first | exact @GlobalTheory.EisM.zm_fun_mf | exact GlobalTheory.EisM.zm_fun_mf | (intros; apply GlobalTheory.EisM.zm_fun_mf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IterULevelValStable
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory

lemma ch_periodic_of_dvd {N L : ℕ} (ε : DirichletCharacter ℂ N) (h : N ∣ L) (d : ℤ) :
    ch ε (d + L) = ch ε d := by
  unfold ch
  have : ((L : ℤ) : ZMod N) = 0 := by
    rw [Int.cast_natCast]; exact (ZMod.natCast_eq_zero_iff L N).2 h
  rw [Int.cast_add, this, add_zero]

theorem iterU_level_val_stable : ∀ (k N l m : ℕ) (ε : DirichletCharacter ℂ N) (t : ℕ → ℂ) (α : ℂ) (B : ℕ) (c a : ℕ → ℂ),
    1 ≤ k → l.Prime → α ≠ 0 → MF k (N * l ^ (m + 1)) (ch ε) a → MF k (N * l) (ch ε) ((Uo l)^[m] a) ∧
      (EigF k N l ε t α B c → ∀ r, m ≤ r → val B c l α r a = val B c l α m a) := by
  intro k N l m ε t α B c a hk hl hα ha
  have lev : ∀ m (a : ℕ → ℂ), MF k (N * l ^ (m + 1)) (ch ε) a → MF k (N * l) (ch ε) ((Uo l)^[m] a) := by
    intro m
    induction m with
    | zero => intro a ha; simpa using ha
    | succ m ih =>
      intro a ha
      have hU : MF k (N * l ^ (m + 1)) (ch ε) (Uo l a) := by
        refine GlobalTheory.T.coeffHeckeUOperator_lowers_level k (N * l ^ (m + 1)) l (ch ε) a hk hl ?_ ?_ ?_
        · exact Dvd.dvd.mul_left (dvd_pow_self l (Nat.succ_ne_zero m)) N
        · exact ch_periodic_of_dvd ε (Dvd.intro _ rfl)
        · simpa [pow_succ, mul_assoc] using ha
      rw [Function.iterate_succ_apply]
      exact ih _ hU
  have hb := lev m a ha
  refine ⟨hb, fun hE r hr => ?_⟩
  have per : ∀ d, ch ε (d + ((N * l : ℕ) : ℤ)) = ch ε d := ch_periodic_of_dvd ε (Dvd.intro _ rfl)
  have mfj : ∀ j, MF k (N * l) (ch ε) ((Uo l)^[j] ((Uo l)^[m] a)) := by
    intro j
    induction j with
    | zero => simpa using hb
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact (GlobalTheory.T.isModularFormCoeffSeq_heckeU_and_depletion k (N * l) l (ch ε) _ hk hl (Dvd.intro_left _ rfl) per ih).1
  have lamj : ∀ j, lam B c ((Uo l)^[j] ((Uo l)^[m] a)) = α ^ j * lam B c ((Uo l)^[m] a) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Function.iterate_succ_apply', hE.U _ (mfj j), ih, pow_succ]
      ring
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hr
  unfold val
  rw [add_comm m j, Function.iterate_add_apply, lamj, pow_add]
  have hj : α ^ j ≠ 0 := pow_ne_zero _ hα
  field_simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinTameWeightSecondEqCharacterSum
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinTameWeightSecondEqCharacterSum
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem eisensteinTameWeightSecond_eq_character_sum :
    ∀ (N : ℕ) (s : ℂ), 0 < N → ∀ B : ℤ,
      tw2 N s B = ((N.totient : ℂ))⁻¹ * ∑ ν : DirichletCharacter ℂ N, (1 - s * ν (-1)) * ch ν B := by
  intro N s hN B
  haveI : NeZero N := ⟨hN.ne'⟩
  have hφ : ((N.totient : ℂ)) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hN).ne'
  have h1 := DirichletCharacter.sum_characters_eq ℂ (B : ZMod N)
  have h2 := DirichletCharacter.sum_characters_eq ℂ (-(B : ZMod N))
  have h3 : ∑ ν : DirichletCharacter ℂ N, ν (-1) * ν (B : ZMod N)
      = ∑ ν : DirichletCharacter ℂ N, ν (-(B : ZMod N)) := by
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [← map_mul, neg_one_mul]
  have h4 : (-(B : ZMod N) = 1) ↔ ((B : ZMod N) = -1) := neg_eq_iff_eq_neg
  have hsum : ∑ ν : DirichletCharacter ℂ N, (1 - s * ν (-1)) * ch ν B
      = ∑ ν : DirichletCharacter ℂ N, ν (B : ZMod N)
        - s * ∑ ν : DirichletCharacter ℂ N, ν (-1) * ν (B : ZMod N) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ν _ => ?_
    simp only [ch]
    ring
  rw [hsum, h3, h1, h2]
  simp only [tw2, h4]
  field_simp
  split_ifs <;> ring

end GlobalTheory.EisM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinTameWeightSecondEqCharacterSumStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tw2_eq_inv_totient_mul_sum_characters : ∀ (N : ℕ) (s : ℂ), 0 < N → ∀ B : ℤ, tw2 N s B = ((N.totient : ℂ))⁻¹ * ∑ ν : DirichletCharacter ℂ N, (1 - s * ν (-1)) * ch ν B := by
  first | exact @GlobalTheory.EisM.eisensteinTameWeightSecond_eq_character_sum | exact GlobalTheory.EisM.eisensteinTameWeightSecond_eq_character_sum | (intros; apply GlobalTheory.EisM.eisensteinTameWeightSecond_eq_character_sum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ZsNormCharLeOne
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory

theorem zs_iter_Uo {R : Type*} [CommRing R] (l r : ℕ) (a : ℕ → R) (n : ℕ) :
    (GlobalTheory.EisM.Uo l)^[r] a n = a (l ^ r * n) := by
  induction r generalizing n with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply', GlobalTheory.EisM.Uo, ih]
    congr 1; ring

theorem zs_norm_char_le_one {l : ℕ} [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) {N : ℕ} (hN : 0 < N)
    (θ : DirichletCharacter ℂ N) (z : ZMod N) : ‖ι.symm (θ z)‖ ≤ 1 := by
  haveI : NeZero N := ⟨hN.ne'⟩
  by_cases hz : IsUnit z
  · obtain ⟨u, rfl⟩ := hz
    have h1 : (θ (u : ZMod N)) ^ Fintype.card (ZMod N)ˣ = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one]
    have h2 : ‖ι.symm (θ (u : ZMod N))‖ ^ Fintype.card (ZMod N)ˣ = 1 := by
      rw [← norm_pow, ← map_pow, h1, map_one, norm_one]
    exact ((pow_eq_one_iff_of_nonneg (norm_nonneg _) Fintype.card_ne_zero).1 h2).le
  · rw [MulChar.map_nonunit θ hz, map_zero, norm_zero]; exact zero_le_one

theorem zs_norm_exp {l : ℕ} [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) {N : ℕ} (hN : 0 < N) (y : ℕ) (d : ℤ) :
    ‖ι.symm (cexp (2 * π * Complex.I * (y * d) / N))‖ = 1 := by
  have h1 : (cexp (2 * π * Complex.I * (y * d) / N)) ^ N = 1 := by
    rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    refine ⟨(y : ℤ) * d, ?_⟩
    have : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    push_cast
    field_simp
  have h2 : ‖ι.symm (cexp (2 * π * Complex.I * (y * d) / N))‖ ^ N = 1 := by
    rw [← norm_pow, ← map_pow, h1, map_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hN.ne').1 h2

theorem zs_norm_hat_le_one {l : ℕ} [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) {N : ℕ} (hN : 0 < N)
    (θ : DirichletCharacter ℂ N) (d : ℤ) : ‖ι.symm (GlobalTheory.EisM.hat (fun z => θ z) d)‖ ≤ 1 := by
  unfold GlobalTheory.EisM.hat
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun y _ => ?_
  rw [map_mul, norm_mul, zs_norm_exp ι hN, mul_one]
  exact zs_norm_char_le_one ι hN θ _

end GlobalTheory

namespace GlobalTheory

end GlobalTheory

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMuModelMeasureOfEigenfunctional
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM

lemma measMu_val_eq (B : ℕ) (c : ℕ → ℂ) (l : ℕ) (α : ℂ) (r : ℕ) (a : ℕ → ℂ) :
    val B c l α r a = (α ^ r)⁻¹ * ∑ n ∈ Finset.range B, c n * a (l ^ r * n) := by
  simp only [val, lam, GlobalTheory.zs_iter_Uo]

lemma measMu_val_sum {κ : Type*} (B : ℕ) (c : ℕ → ℂ) (l : ℕ) (α : ℂ) (r : ℕ) (s : Finset κ) (a : κ → ℂ)
    (g : κ → ℕ → ℂ) :
    val B c l α r (fun n => ∑ i ∈ s, a i * g i n) = ∑ i ∈ s, a i * val B c l α r (g i) := by
  simp only [measMu_val_eq, Finset.mul_sum]
  rw [Finset.sum_comm (s := Finset.range B)]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun n _ => by ring

lemma measMu_zm_sum {κ : Type*} (k l : ℕ) (u : ℤ → ℂ) (s : Finset κ) (a : κ → ℂ) (w : κ → ℤ → ℂ)
    (F : ℕ → ℕ → ℂ) (n : ℕ) :
    Zm k l u (fun B => ∑ i ∈ s, a i * w i B) F n = ∑ i ∈ s, a i * Zm k l u (w i) F n := by
  unfold Zm
  have key : ∀ (p x y : ℕ × ℕ), (if l ∣ p.1 ∨ l ∣ p.2 then (0 : ℂ) else
      (x.1 : ℂ) ^ (k - 2) * u x.1 * (∑ i ∈ s, a i * w i y.1) * F x.1 y.2) =
      ∑ i ∈ s, a i * (if l ∣ p.1 ∨ l ∣ p.2 then (0 : ℂ) else (x.1 : ℂ) ^ (k - 2) * u x.1 * w i y.1 * F x.1 y.2) := by
    intro p x y
    split_ifs
    · simp
    · rw [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
  simp only [key]
  simp only [Finset.mul_sum]
  symm
  rw [Finset.sum_comm (s := s)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_comm (s := s)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm (s := s)]

lemma measMu_zm_zero (k l : ℕ) (u v : ℤ → ℂ) : Zm k l u v (fun _ _ => 0) = fun _ => 0 := by
  funext n; simp [Zm]

lemma measMu_val_zero (B : ℕ) (c : ℕ → ℂ) (l : ℕ) (α : ℂ) (r : ℕ) : val B c l α r (fun _ => (0:ℂ)) = 0 := by
  simp [measMu_val_eq]

lemma measMu_zm_congr (k l : ℕ) (u v : ℤ → ℂ) (F G : ℕ → ℕ → ℂ)
    (h : ∀ x y, ¬ l ∣ x → ¬ l ∣ y → F x y = G x y) : Zm k l u v F = Zm k l u v G := by
  funext n
  unfold Zm
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_
  split_ifs with h1
  · rfl
  · push_neg at h1
    have hx1 : x.1 ∣ p.1 := Dvd.intro _ (Nat.mem_divisorsAntidiagonal.mp hx).1
    have hy2 : y.2 ∣ p.2 := Dvd.intro_left _ (Nat.mem_divisorsAntidiagonal.mp hy).1
    rw [h x.1 y.2 (fun hd => h1.1 (hd.trans hx1)) (fun hd => h1.2 (hd.trans hy2))]

lemma measMu_quo_succ {l : ℕ} (hp : l.Prime) (m : ℕ) (f : ZMod (l ^ m) → ℂ) (f' : ZMod (l ^ (m + 1)) → ℂ)
    (h : ∀ x : ℕ, f' x = f x) (x y : ℕ) (hy : ¬ l ∣ y) :
    f' ((x : ZMod (l ^ (m + 1))) * (y : ZMod (l ^ (m + 1)))⁻¹) = f ((x : ZMod (l ^ m)) * (y : ZMod (l ^ m))⁻¹) := by
  haveI : NeZero (l ^ (m + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hcop : y.Coprime (l ^ (m + 1)) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_comm).mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hy))
  have hdvd : l ^ m ∣ l ^ (m + 1) := pow_dvd_pow l (Nat.le_succ m)
  set w : ZMod (l ^ (m + 1)) := (x : ZMod (l ^ (m + 1))) * (y : ZMod (l ^ (m + 1)))⁻¹ with hw
  rw [← ZMod.natCast_zmod_val w, h]
  congr 1
  have hc : ((w.val : ℕ) : ZMod (l ^ m)) = ZMod.castHom hdvd (ZMod (l ^ m)) w := by
    rw [ZMod.castHom_apply, ZMod.cast_eq_val]
  rw [hc, hw, map_mul, map_natCast]
  congr 1
  symm
  apply ZMod.inv_eq_of_mul_eq_one
  rw [← map_natCast (ZMod.castHom hdvd (ZMod (l ^ m))) y, ← map_mul, ZMod.coe_mul_inv_eq_one y hcop, map_one]

lemma measMu_parity_succ {l : ℕ} (hp : l.Prime) (m : ℕ) (f : ZMod (l ^ m) → ℂ) (f' : ZMod (l ^ (m + 1)) → ℂ)
    (h : ∀ x : ℕ, f' x = f x) (s : ℂ) (hf : ∀ y, f (-y) = s * f y) : ∀ y, f' (-y) = s * f' y := by
  haveI : NeZero (l ^ (m + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hdvd : l ^ m ∣ l ^ (m + 1) := pow_dvd_pow l (Nat.le_succ m)
  have hc : ∀ w : ZMod (l ^ (m + 1)), f' w = f (ZMod.castHom hdvd (ZMod (l ^ m)) w) := by
    intro w
    rw [← ZMod.natCast_zmod_val w, h, map_natCast]
  intro y
  rw [hc, hc, map_neg, hf]

lemma measMu_char_level_one (l : ℕ) (ψ : DirichletCharacter ℂ l) :
    ∃ ψ' : DirichletCharacter ℂ (l ^ 1), (∀ x : ℕ, ch ψ' x = ψ x) ∧ (∀ y : ℕ, ch ψ'⁻¹ y = ψ⁻¹ y) ∧
      ψ' (-1) = ψ (-1) := by
  have key : ∀ M, M = l → ∃ ψ' : DirichletCharacter ℂ M, (∀ x : ℕ, ch ψ' x = ψ x) ∧
      (∀ y : ℕ, ch ψ'⁻¹ y = ψ⁻¹ y) ∧ ψ' (-1) = ψ (-1) := by
    rintro M rfl
    exact ⟨ψ, fun x => by simp [ch], fun y => by simp [ch], rfl⟩
  exact key _ (pow_one l)

lemma measMu_zm_val_bound {l : ℕ} [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (k : ℕ) (u w : ℤ → ℂ) (α : ℂ) (B : ℕ)
    (c : ℕ → ℂ) (hu : ∀ x, ‖ι.symm (u x)‖ ≤ 1) (hw : ∀ x, ‖ι.symm (w x)‖ ≤ 1) (hα : ‖ι.symm α‖ = 1) (r : ℕ)
    (F F' : ℕ → ℕ → ℂ) (δ : ℝ) (hδ : 0 ≤ δ) (hF : ∀ x y : ℕ, ¬ l ∣ x → ¬ l ∣ y → ‖ι.symm (F x y - F' x y)‖ ≤ δ) :
    ‖ι.symm (val B c l α r (Zm k l u w F) - val B c l α r (Zm k l u w F'))‖ ≤
      (∑ n ∈ Finset.range B, ‖ι.symm (c n)‖) * δ := by
  have hZ : ∀ m, ‖ι.symm (Zm k l u w F m - Zm k l u w F' m)‖ ≤ δ := by
    intro m
    have e : Zm k l u w F m - Zm k l u w F' m =
        ∑ p ∈ Finset.HasAntidiagonal.antidiagonal m, ∑ x ∈ p.1.divisorsAntidiagonal, ∑ y ∈ p.2.divisorsAntidiagonal,
          if l ∣ p.1 ∨ l ∣ p.2 then 0 else
            (x.1 : ℂ) ^ (k - 2) * u x.1 * w y.1 * (F x.1 y.2 - F' x.1 y.2) := by
      simp only [Zm, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      split_ifs <;> ring
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e, map_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hδ fun p _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hδ fun x hx => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hδ fun y hy => ?_
    split_ifs with h
    · rw [map_zero, norm_zero]; exact hδ
    · push_neg at h
      have hx1 : ¬ l ∣ x.1 := fun hd => h.1 (hd.trans (Dvd.intro _ (Nat.mem_divisorsAntidiagonal.1 hx).1))
      have hy2 : ¬ l ∣ y.2 := fun hd => h.2 (hd.trans (Dvd.intro_left _ (Nat.mem_divisorsAntidiagonal.1 hy).1))
      have h1 : ‖ι.symm ((x.1 : ℂ) ^ (k - 2))‖ ≤ 1 := by
        rw [map_pow, map_natCast, norm_pow]
        exact pow_le_one₀ (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _)
      have h4 := hF x.1 y.2 hx1 hy2
      rw [map_mul, map_mul, map_mul, norm_mul, norm_mul, norm_mul]
      calc ‖ι.symm ((x.1 : ℂ) ^ (k - 2))‖ * ‖ι.symm (u x.1)‖ * ‖ι.symm (w y.1)‖ * ‖ι.symm (F x.1 y.2 - F' x.1 y.2)‖
          ≤ 1 * 1 * 1 * δ := by gcongr; exacts [hu _, hw _]
        _ = δ := by ring
  have e2 : val B c l α r (Zm k l u w F) - val B c l α r (Zm k l u w F') =
      (α ^ r)⁻¹ * ∑ n ∈ Finset.range B, c n * (Zm k l u w F (l ^ r * n) - Zm k l u w F' (l ^ r * n)) := by
    simp only [measMu_val_eq, ← mul_sub, ← Finset.sum_sub_distrib]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e2, map_mul, norm_mul, map_inv₀, map_pow, norm_inv, norm_pow, hα, one_pow, inv_one, one_mul, map_sum]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun n _ => ?_
  rw [map_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left (hZ _) (norm_nonneg _)

end GlobalTheory.EisM

namespace GlobalTheory.EisM

theorem measMu_of_eig : ∀ (l : ℕ) [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (e N : ℕ) (χ θ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ l) (α : ℂ) (B : ℕ) (c : ℕ → ℂ), 1 ≤ e → 0 < N → ¬ l ∣ N → ‖ι.symm α‖ = 1 → (∀ (ε : DirichletCharacter ℂ N) (a : ℕ → ℂ), ε ≠ χ → MF (2 * e + 1) (N * l) (ch ε) a → lam B c a = 0) → (∀ a, MF (2 * e + 1) (N * l) (ch χ) a → lam B c (Uo l a) = α * lam B c a) → θ (-1) = (-1) ^ e * ψ (-1) → χ (-1) = -1 → MeasMu ι e ((-1) ^ e * ψ (-1)) (hat θ) (tw2 N ((-1) ^ e * ψ (-1))) ψ α B c ((2 / (N.totient : ℂ)) * val B c l α 1 (Zm (2 * e + 1) l (hat θ) (ch (θ * χ)) (fun A d => ψ A * ψ⁻¹ d * ((d : ℂ) / A) ^ e))) := by
  intro l _ ι e N χ θ ψ α B c he hN hlN hα hkill hU hθ hχ
  have hp : l.Prime := Fact.out
  have hα0 : α ≠ 0 := by rintro rfl; simp at hα
  haveI : NeZero N := ⟨hN.ne'⟩
  have hψsq : ψ (-1) * ψ (-1) = 1 := by rw [← map_mul]; simp
  have hE2 : ((-1 : ℂ) ^ e) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  set s : ℂ := (-1) ^ e * ψ (-1) with hs
  have hs2 : s * s = 1 := by rw [hs]; linear_combination ((-1 : ℂ) ^ e) ^ 2 * hψsq + hE2
  have hθχ : (θ * χ) (-1) = -s := by rw [MulChar.coeToFun_mul, Pi.mul_apply, hθ, hχ]; ring
  have hχeq : θ⁻¹ * (θ * χ) = χ := by rw [← mul_assoc, inv_mul_cancel, one_mul]
  have hodd : Odd (2 * e + 1) := odd_two_mul_add_one e
  have hlift : ∀ (ε : DirichletCharacter ℂ N) (a : ℕ → ℂ) (m r : ℕ), m ≤ r →
      MF (2 * e + 1) (N * l ^ (m + 1)) (ch ε) a → MF (2 * e + 1) (N * l ^ (r + 1)) (ch ε) a := fun ε a m r hmr ha =>
    (GlobalTheory.EisM.mf_linear (2 * e + 1) _ (ch ε)).2.2.2.2.1 _ a (Nat.mul_dvd_mul_left N (pow_dvd_pow l (by omega))) ha
  have hlev : ∀ (ε : DirichletCharacter ℂ N) (a : ℕ → ℂ) (m r : ℕ), m ≤ r →
      MF (2 * e + 1) (N * l ^ (m + 1)) (ch ε) a → MF (2 * e + 1) (N * l) (ch ε) ((Uo l)^[r] a) := fun ε a m r hmr ha =>
    (GlobalTheory.iterU_level_val_stable (2 * e + 1) N l r ε (fun _ => 0) α B c a (by omega) hp hα0 (hlift ε a m r hmr ha)).1
  have hstab : ∀ (m : ℕ) (a : ℕ → ℂ), MF (2 * e + 1) (N * l ^ (m + 1)) (ch χ) a →
      val B c l α (m + 1) a = val B c l α m a := by
    intro m a ha
    have h1 := hlev χ a m m le_rfl ha
    simp only [val]
    rw [Function.iterate_succ_apply', hU _ h1, pow_succ]
    field_simp
  have hzero : ∀ (m r : ℕ) (f : ZMod (l ^ m) → ℂ) (ν : DirichletCharacter ℂ N), 1 ≤ m → m ≤ r →
      (∀ y, f (-y) = s * f y) → ν ≠ θ * χ → ν (-1) ≠ s →
      val B c l α r (Zm (2 * e + 1) l (hat θ) (ch ν) (fun A d => f ((A : ZMod (l ^ m)) * (d : ZMod (l ^ m))⁻¹))) = 0 := by
    intro m r f ν hm hmr hf hne hνs
    have hνsq : ν (-1) * ν (-1) = 1 := by rw [← map_mul]; simp
    have hν : ν (-1) = -θ (-1) := by
      have h0 : (ν (-1) - s) * (ν (-1) + s) = 0 := by linear_combination hνsq - hs2
      rcases mul_eq_zero.1 h0 with h | h
      · exact absurd (sub_eq_zero.1 h) hνs
      · rw [hθ]; linear_combination h
    have hMF := GlobalTheory.T.isModularFormCoeffSeq_eisensteinProduct_parity (2 * e + 1) N l m (θ⁻¹ * ν) θ ν f (by omega) hodd hN hp hm hlN rfl hν
      (fun x => by rw [hf, hθ])
    have hL := hlev _ _ m r hmr hMF
    have hne' : θ⁻¹ * ν ≠ χ := by
      intro h; apply hne; rw [← h, ← mul_assoc, mul_inv_cancel, one_mul]
    simp only [val, hkill _ _ hne' hL, mul_zero]
  have htw : tw2 N s = fun B' => ∑ ν : DirichletCharacter ℂ N, ((N.totient : ℂ)⁻¹ * (1 - s * ν (-1))) * ch ν B' := by
    funext B'
    rw [GlobalTheory.T.tw2_eq_inv_totient_mul_sum_characters N s hN B', Finset.mul_sum]
    exact Finset.sum_congr rfl fun ν _ => by ring
  have hred : ∀ (m r : ℕ) (f : ZMod (l ^ m) → ℂ), 1 ≤ m → m ≤ r → (∀ y, f (-y) = s * f y) →
      val B c l α r (Zm (2 * e + 1) l (hat θ) (tw2 N s) (fun A d => f ((A : ZMod (l ^ m)) * (d : ZMod (l ^ m))⁻¹))) =
        (2 / (N.totient : ℂ)) * val B c l α r (Zm (2 * e + 1) l (hat θ) (ch (θ * χ))
          (fun A d => f ((A : ZMod (l ^ m)) * (d : ZMod (l ^ m))⁻¹))) := by
    intro m r f hm hmr hf
    have hZ : Zm (2 * e + 1) l (hat θ) (tw2 N s) (fun A d => f ((A : ZMod (l ^ m)) * (d : ZMod (l ^ m))⁻¹)) =
        fun n => ∑ ν : DirichletCharacter ℂ N, ((N.totient : ℂ)⁻¹ * (1 - s * ν (-1))) *
          Zm (2 * e + 1) l (hat θ) (ch ν) (fun A d => f ((A : ZMod (l ^ m)) * (d : ZMod (l ^ m))⁻¹)) n := by
      funext n
      rw [htw, measMu_zm_sum]
    rw [hZ, measMu_val_sum, Finset.sum_eq_single (θ * χ)]
    · rw [hθχ, show (1 : ℂ) - s * -s = 2 by linear_combination hs2, div_eq_mul_inv]
      ring
    · intro ν _ hne
      by_cases h : ν (-1) = s
      · rw [h, hs2]; ring
      · rw [hzero m r f ν hm hmr hf hne h, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hu : ∀ x, ‖ι.symm (hat θ x)‖ ≤ 1 := fun x => GlobalTheory.zs_norm_hat_le_one ι hN θ x
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m hm f f' hf hff'
    have hf' := measMu_parity_succ hp m f f' hff' s hf
    have hMF : MF (2 * e + 1) (N * l ^ (m + 1)) (ch χ) (Zm (2 * e + 1) l (hat θ) (ch (θ * χ))
        (fun A d => f ((A : ZMod (l ^ m)) * (d : ZMod (l ^ m))⁻¹))) := by
      have := GlobalTheory.T.isModularFormCoeffSeq_eisensteinProduct_parity (2 * e + 1) N l m (θ⁻¹ * (θ * χ)) θ (θ * χ) f (by omega) hodd hN hp hm hlN rfl
        (by rw [hθχ, hθ]) (fun x => by rw [hf, hθ])
      rwa [hχeq] at this
    unfold mesMu
    rw [measMu_zm_congr _ _ _ _ _ (fun A d => f ((A : ZMod (l ^ m)) * (d : ZMod (l ^ m))⁻¹))
        (fun x y _ hy => measMu_quo_succ hp m f f' hff' x y hy),
      hred m (m + 1) f hm (by omega) hf, hred m m f hm le_rfl hf, hstab m _ hMF]
  · have hsn : ‖ι.symm s‖ ≤ 1 := by
      rw [hs, map_mul, norm_mul, map_pow, map_neg, map_one, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      exact GlobalTheory.zs_norm_char_le_one ι hp.pos ψ _
    have hw : ∀ x, ‖ι.symm (tw2 N s x)‖ ≤ 1 := by
      intro x
      unfold tw2
      rw [map_sub, sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · split_ifs <;> simp
      · rw [norm_neg, map_mul, norm_mul]
        split_ifs <;> simp [hsn]
    refine ⟨∑ n ∈ Finset.range B, ‖ι.symm (c n)‖, fun m f δ hδ hf => ?_⟩
    have := measMu_zm_val_bound ι (2 * e + 1) (hat θ) (tw2 N s) α B c hu hw hα m
      (fun A d => f ((A : ZMod (l ^ m)) * (d : ZMod (l ^ m))⁻¹)) (fun _ _ => 0) δ hδ (fun x y _ _ => by simpa using hf _)
    rwa [measMu_zm_zero, measMu_val_zero, sub_zero] at this
  · classical
    set ζ : ℂ := cexp (2 * π * Complex.I / N) with hζ
    let S : Finset (PadicAlgCl l) := insert (ι.symm α) (insert (ι.symm ζ) (insert (ι.symm s)
      ((Finset.range B).image (fun n => ι.symm (c n)) ∪ Finset.univ.image (fun x : ZMod N => ι.symm (θ x)))))
    refine ⟨IntermediateField.adjoin ℚ_[l] (S : Set (PadicAlgCl l)),
      IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x), ?_⟩
    intro m f E' hE hf
    let F : Subfield ℂ := E'.toSubfield.comap (ι.symm : ℂ →+* PadicAlgCl l)
    have memF : ∀ z : ℂ, z ∈ F ↔ ι.symm z ∈ E' := fun z => Iff.rfl
    have hS : ∀ z : ℂ, ι.symm z ∈ S → z ∈ F := fun z hz =>
      (memF z).2 (hE (IntermediateField.subset_adjoin ℚ_[l] _ (Finset.mem_coe.2 hz)))
    have hαF : α ∈ F := hS _ (by simp [S])
    have hζF : ζ ∈ F := hS _ (by simp [S])
    have hsF : s ∈ F := hS _ (by simp [S])
    have hc : ∀ n < B, c n ∈ F := fun n hn => hS _ (by
      simp only [S, Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_range]
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, rfl⟩))))
    have hθF : ∀ x : ZMod N, θ x ∈ F := fun x => hS _ (by
      simp only [S, Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨x, rfl⟩))))
    have hfF : ∀ x, f x ∈ F := fun x => (memF _).2 (hf x)
    have hhat : ∀ d : ℤ, hat θ d ∈ F := by
      intro d
      unfold hat
      refine F.sum_mem fun y _ => F.mul_mem (hθF _) ?_
      have : cexp (2 * π * Complex.I * (y * d) / N) = ζ ^ ((y : ℤ) * d) := by
        rw [hζ, ← Complex.exp_int_mul]; congr 1; push_cast; ring
      rw [this]
      exact F.zpow_mem hζF _
    have htwF : ∀ B' : ℤ, tw2 N s B' ∈ F := by
      intro B'
      unfold tw2
      refine F.sub_mem ?_ (F.mul_mem hsF ?_) <;> split_ifs <;> first | exact F.one_mem | exact F.zero_mem
    have hZ : ∀ n, Zm (2 * e + 1) l (hat θ) (tw2 N s) (fun A d => f ((A : ZMod (l ^ m)) * (d : ZMod (l ^ m))⁻¹)) n ∈ F := by
      intro n
      unfold Zm
      refine F.sum_mem fun p _ => F.sum_mem fun x _ => F.sum_mem fun y _ => ?_
      split_ifs
      · exact F.zero_mem
      · exact F.mul_mem (F.mul_mem (F.mul_mem (F.pow_mem (natCast_mem F _) _) (hhat _)) (htwF _)) (hfF _)
    show mesMu (2 * e + 1) l (hat θ) (tw2 N s) α B c m f ∈ F
    rw [mesMu, measMu_val_eq]
    exact F.mul_mem (F.inv_mem (F.pow_mem hαF _)) (F.sum_mem fun n hn => F.mul_mem (hc n (Finset.mem_range.1 hn)) (hZ _))
  · have hw' : ∀ x, ‖ι.symm (ch (θ * χ) x)‖ ≤ 1 := fun x => GlobalTheory.zs_norm_char_le_one ι hN (θ * χ) _
    refine ⟨‖ι.symm (2 / (N.totient : ℂ))‖ * ∑ n ∈ Finset.range B, ‖ι.symm (c n)‖, fun m hm f δ hδ hf hfd => ?_⟩
    obtain ⟨ψ', h1, h2, h3⟩ := measMu_char_level_one l ψ
    have hpar1 : ψ' (-1) * θ (-1) = (-1) ^ (2 * e + 1 - 1 - e) := by
      rw [show 2 * e + 1 - 1 - e = e by omega, h3, hθ, hs]
      linear_combination ((-1 : ℂ) ^ e) * hψsq
    have hpar2 : ψ' (-1) * (θ * χ) (-1) = (-1) ^ (e + 1) := by
      rw [hθχ, h3, hs]
      linear_combination (-(-1 : ℂ) ^ e) * hψsq
    have hMF0 := GlobalTheory.T.muModelProduct_isModularFormCoeffSeq_locallyAlgebraic (2 * e + 1) e N l 1 (θ⁻¹ * (θ * χ)) (hat θ) θ (θ * χ) ψ' (by omega) hN hp le_rfl hlN
      (hat_char_props.1 N θ hN).1 (hat_char_props.1 N θ hN).2.1 rfl hpar1 hpar2
    rw [hχeq] at hMF0
    have hG : (fun x y : ℕ => ch ψ' x * ch ψ'⁻¹ y * ((y : ℂ) / x) ^ e) =
        fun x y : ℕ => ψ x * ψ⁻¹ y * ((y : ℂ) / x) ^ e := by
      funext x y; rw [h1, h2]
    rw [hG] at hMF0
    have hall : ∀ r, 1 ≤ r → val B c l α r (Zm (2 * e + 1) l (hat θ) (ch (θ * χ))
        (fun A d => ψ A * ψ⁻¹ d * ((d : ℂ) / A) ^ e)) =
        val B c l α 1 (Zm (2 * e + 1) l (hat θ) (ch (θ * χ)) (fun A d => ψ A * ψ⁻¹ d * ((d : ℂ) / A) ^ e)) := by
      intro r hr
      induction r, hr using Nat.le_induction with
      | base => rfl
      | succ r hr ih => rw [hstab r _ (hlift χ _ 1 r hr hMF0), ih]
    unfold mesMu
    rw [hred m m f hm le_rfl hf, ← hall m hm, ← mul_sub, map_mul, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (measMu_zm_val_bound ι (2 * e + 1) (hat θ) (ch (θ * χ)) α B c hu hw' hα m _ _ δ hδ
      (fun x y hx hy => hfd x y hx hy)) (norm_nonneg _)

end GlobalTheory.EisM

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMuModelMeasureOfEigenfunctionalStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_muModel_measure_of_eigenfunctional : ∀ (l : ℕ) [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (e N : ℕ) (χ θ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ l) (α : ℂ) (B : ℕ) (c : ℕ → ℂ), 1 ≤ e → 0 < N → ¬ l ∣ N → ‖ι.symm α‖ = 1 → (∀ (ε : DirichletCharacter ℂ N) (a : ℕ → ℂ), ε ≠ χ → MF (2 * e + 1) (N * l) (ch ε) a → lam B c a = 0) → (∀ a, MF (2 * e + 1) (N * l) (ch χ) a → lam B c (Uo l a) = α * lam B c a) → θ (-1) = (-1) ^ e * ψ (-1) → χ (-1) = -1 → MeasMu ι e ((-1) ^ e * ψ (-1)) (hat θ) (tw2 N ((-1) ^ e * ψ (-1))) ψ α B c ((2 / (N.totient : ℂ)) * val B c l α 1 (Zm (2 * e + 1) l (hat θ) (ch (θ * χ)) (fun A d => ψ A * ψ⁻¹ d * ((d : ℂ) / A) ^ e))) := by
  first | exact @GlobalTheory.EisM.measMu_of_eig | exact GlobalTheory.EisM.measMu_of_eig | (intros; apply GlobalTheory.EisM.measMu_of_eig <;> assumption)
end
