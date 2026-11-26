module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHeckeEigenfunctionalOfDepletedEigenform
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RankinValuesAtZeroStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepletedEisensteinProductValueNeZeroOfRankin
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepletedEisensteinProductValueNeZeroOfRankin
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.DepletedValue

lemma isUnit_of_isCoprime {n : ℕ} {d : ℤ} (h : IsCoprime d (n : ℤ)) : IsUnit (d : ZMod n) := by
  obtain ⟨u, v, huv⟩ := h
  have h1 := congrArg (Int.cast : ℤ → ZMod n) huv
  push_cast at h1
  simp only [ZMod.natCast_self, mul_zero, add_zero] at h1
  exact isUnit_iff_exists_inv.mpr ⟨_, by rw [mul_comm]; exact h1⟩

lemma ch_ne_zero {n : ℕ} (χ : DirichletCharacter ℂ n) {d : ℤ} (h : IsCoprime d (n : ℤ)) : ch χ d ≠ 0 :=
  ((isUnit_of_isCoprime h).map χ).ne_zero

lemma ch_inv {n : ℕ} (χ : DirichletCharacter ℂ n) (d : ℤ) : ch χ⁻¹ d = (ch χ d)⁻¹ :=
  MulChar.inv_apply_eq_inv' _ _

lemma ch_mul {n : ℕ} (θ χ : DirichletCharacter ℂ n) (d : ℤ) : ch (θ * χ) d = ch θ d * ch χ d := by
  simp [ch]

lemma ch_one {n : ℕ} {d : ℤ} (h : IsCoprime d (n : ℤ)) : ch (1 : DirichletCharacter ℂ n) d = 1 :=
  MulChar.one_apply (isUnit_of_isCoprime h)

lemma ch_dvd {l : ℕ} (hl : l.Prime) (ψ : DirichletCharacter ℂ l) {d : ℤ} (h : (l : ℤ) ∣ d) : ch ψ d = 0 := by
  haveI : Fact l.Prime := ⟨hl⟩
  have : (d : ZMod l) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd d l).2 h
  simp only [ch, this]; exact MulChar.map_zero ψ

lemma coprime_left {d : ℤ} {N l : ℕ} (h : IsCoprime d ((N * l : ℕ) : ℤ)) : IsCoprime d (N : ℤ) := by
  push_cast at h; exact h.of_mul_right_left

lemma coprime_right {d : ℤ} {N l : ℕ} (h : IsCoprime d ((N * l : ℕ) : ℤ)) : IsCoprime d (l : ℤ) := by
  push_cast at h; exact h.of_mul_right_right

lemma mul_smul_right (a b : ℕ → ℂ) (s : ℂ) : mul a (s • b) = s • mul a b := by
  funext n; simp [mul, Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring)

lemma mul_smul_left (a b : ℕ → ℂ) (s : ℂ) : mul (s • a) b = s • mul a b := by
  funext n; simp [mul, Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring)

lemma mul_add_right (a b b' : ℕ → ℂ) : mul a (b + b') = mul a b + mul a b' := by
  funext n; simp [mul, mul_add, Finset.sum_add_distrib]

lemma lam_add (B : ℕ) (c a b : ℕ → ℂ) : lam B c (a + b) = lam B c a + lam B c b := by
  simp [lam, mul_add, Finset.sum_add_distrib]

lemma lam_smul (B : ℕ) (c a : ℕ → ℂ) (s : ℂ) : lam B c (s • a) = s * lam B c a := by
  simp [lam, Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring)

lemma lam_sub (B : ℕ) (c a b : ℕ → ℂ) : lam B c (a - b) = lam B c a - lam B c b := by
  simp [lam, mul_sub, Finset.sum_sub_distrib]

lemma mul_zero_right (a : ℕ → ℂ) : mul a 0 = 0 := by
  funext n; simp [mul]

lemma lam_zero (B : ℕ) (c : ℕ → ℂ) : lam B c 0 = 0 := by simp [lam]

lemma core {l : ℕ} (hl : 0 < l) (B : ℕ) (c : ℕ → ℂ) (α t₀ : ℂ) (F E : ℕ → ℂ) (hF : Uo l F = t₀ • F) (hE : Uo l E = E)
    (hU : lam B c (Uo l (mul F E)) = α * lam B c (mul F E)) (h0 : lam B c (mul F E) ≠ 0) (hα : α ≠ t₀) (hα0 : α ≠ 0) :
    val B c l α 1 (mul (dep l F) (dep l E)) ≠ 0 := by
  simp only [val, Function.iterate_one, pow_one]
  rw [(GlobalTheory.T.coeffHecke_UV_cauchyProduct_identities ℂ l hl).2.1, hF, hE, mul_smul_left, lam_sub, lam_smul, hU, ← sub_mul]
  exact mul_ne_zero (inv_ne_zero hα0) (mul_ne_zero (sub_ne_zero.mpr hα) h0)

end GlobalTheory.DepletedValue

namespace GlobalTheory.DepletedValue

lemma zs_eq (e l : ℕ) (he : 1 ≤ e) {N : ℕ} (θ χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ l) (c₀ c' : ℂ) :
    Zs (2 * e + 1) l (ch θ) (hat ⇑(θ * χ)) (fun x y => ψ x * ψ⁻¹ y * ((y : ℂ) / x) ^ e) =
      mul (dep l (eis e c₀ (ch ψ) (ch θ))) (dep l (eis (e + 1) c' (fun y => ch ψ⁻¹ y * hat ⇑(θ * χ) y) fun _ => 1)) := by
  have h := GlobalTheory.T.zs_monomial_ratio_eq_mul_dep_eis (2 * e + 1) l e (ch θ) (hat ⇑(θ * χ)) (ch ψ) (ch ψ⁻¹) c₀ c' (by omega)
  have hk : 2 * e + 1 - 1 - e = e := by omega
  rw [hk] at h
  rw [← h]
  congr 1
  funext x y
  simp [ch]

lemma U_FF (e N l : ℕ) (he : 1 ≤ e) (hN : 0 < N) (hl : l.Prime) (θ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ l) (c₀ : ℂ)
    (hF : MF e (N * l) (fun d => ch ψ d * ch θ d) (eis e c₀ (ch ψ) (ch θ))) :
    Uo l (eis e c₀ (ch ψ) (ch θ)) = θ l • eis e c₀ (ch ψ) (ch θ) := by
  have hper : ∀ d : ℤ, (fun d => ch ψ d * ch θ d) (d + ((N * l : ℕ) : ℤ)) = (fun d => ch ψ d * ch θ d) d := by
    intro d; simp [ch]
  have h1 := (GlobalTheory.T.isModularFormCoeffSeq_heckeU_and_depletion e (N * l) l _ _ he hl (dvd_mul_left l N) hper hF).1
  have h2 := ((GlobalTheory.T.modularFormCoeffSeq_linear_structure e (N * l) _).2.2.1 (θ l) _ hF).1
  refine GlobalTheory.T.modularFormCoeffSeq_eq_of_pos_coeff_eq e (N * l) _ _ _ he (Nat.mul_pos hN hl.pos) h1 h2 (fun n hn => ?_)
  have h3 := (GlobalTheory.T.coeffEisensteinSeriesTwisted_heckeU_heckeV e l c₀ (θ l) (ch ψ) (ch θ) hl).1 (fun x hx => ch_dvd hl ψ hx) (fun y => by simp [ch]) n hn
  simpa [Uo] using h3

lemma U_EE (e N l : ℕ) (hl : l.Prime) (θ' : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ l) (c' : ℂ) :
    Uo l (eis (e + 1) c' (fun y => ch ψ⁻¹ y * hat ⇑θ' y) fun _ => 1) = eis (e + 1) c' (fun y => ch ψ⁻¹ y * hat ⇑θ' y) fun _ => 1 := by
  funext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Uo]
  have h3 := (GlobalTheory.T.coeffEisensteinSeriesTwisted_heckeU_heckeV (e + 1) l c' 1 (fun y => ch ψ⁻¹ y * hat ⇑θ' y) (fun _ => 1) hl).1
    (fun x hx => by simp [ch_dvd hl ψ⁻¹ hx]) (fun y => by simp) n hn
  simpa [Uo] using h3

lemma char_eq {N l : ℕ} (χ θ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ l) (φ : DirichletCharacter ℂ (N * l))
    (hφ : ∀ d : ℤ, ch φ d = ch (θ * χ) d * ch ψ d) (d : ℤ) (hd : IsCoprime d ((N * l : ℕ) : ℤ)) :
    ch ψ d * ch θ d * ch φ⁻¹ d = ch χ⁻¹ d := by
  have h1 := ch_ne_zero ψ (coprime_right hd)
  have h2 := ch_ne_zero θ (coprime_left hd)
  have h3 := ch_ne_zero χ (coprime_left hd)
  rw [ch_inv, ch_inv, hφ, ch_mul]
  field_simp

end GlobalTheory.DepletedValue

namespace GlobalTheory.DepletedValue

lemma good_ne (e N l : ℕ) (χ θ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ l) (φ : DirichletCharacter ℂ (N * l))
    (c₀ c₁ : ℂ) (B : ℕ) (c : ℕ → ℂ) (he : 1 ≤ e) (hN : 0 < N) (hl : l.Prime) (hlN : ¬ l ∣ N) (hψ : ψ ≠ 1)
    (hφ : ∀ d : ℤ, ch φ d = ch (θ * χ) d * ch ψ d)
    (hF : MF e (N * l) (fun d => ch ψ d * ch θ d) (eis e c₀ (ch ψ) (ch θ)))
    (hE : MF (e + 1) (N * l) (ch φ⁻¹) (eis (e + 1) c₁ (hat φ) fun _ => 1))
    (hlam : lam B c (mul (eis e c₀ (ch ψ) (ch θ)) (eis (e + 1) c₁ (hat φ) fun _ => 1)) ≠ 0) :
    ∃ c' : ℂ, MF (2 * e + 1) (N * l) (ch χ⁻¹) (mul (eis e c₀ (ch ψ) (ch θ)) (eis (e + 1) c' (fun y => ch ψ⁻¹ y * hat ⇑(θ * χ) y) fun _ => 1)) ∧
      lam B c (mul (eis e c₀ (ch ψ) (ch θ)) (eis (e + 1) c' (fun y => ch ψ⁻¹ y * hat ⇑(θ * χ) y) fun _ => 1)) ≠ 0 := by
  have hcop : N.Coprime l := (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hl).2 hlN))
  set κ : ℂ := ch (θ * χ) l * ch ψ N * hat ψ 1 with hκ
  have hhat : ∀ x, hat φ x = κ * (ch ψ⁻¹ x * hat ⇑(θ * χ) x) := by
    intro x
    rw [(GlobalTheory.T.dirichletCharFiniteFourierTransform_properties).2.1 N l (θ * χ) ψ φ hN hl.pos hcop hφ x, ((GlobalTheory.T.dirichletCharFiniteFourierTransform_properties).2.2 l ψ hl).1 hψ |>.2 x, hκ]
    ring
  have hEn : ∀ c' : ℂ, ∀ n, n ≠ 0 → (eis (e + 1) c₁ (hat φ) fun _ => 1) n = κ * (eis (e + 1) c' (fun y => ch ψ⁻¹ y * hat ⇑(θ * χ) y) fun _ => 1) n := by
    intro c' n hn
    simp only [eis, if_neg hn, Finset.mul_sum, hhat]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  have hκ0 : κ ≠ 0 := by
    intro h0
    have hz : (eis (e + 1) c₁ (hat φ) fun _ => 1) = 0 :=
      GlobalTheory.T.modularFormCoeffSeq_eq_of_pos_coeff_eq (e + 1) (N * l) _ _ _ (by omega) (Nat.mul_pos hN hl.pos) hE (GlobalTheory.T.modularFormCoeffSeq_linear_structure (e + 1) (N * l) _).1
        (fun n hn => by rw [hEn 0 n hn, h0, zero_mul]; rfl)
    rw [hz, mul_zero_right, lam_zero] at hlam
    exact hlam rfl
  refine ⟨c₁ / κ, ?_, ?_⟩ <;>
  have hEE : (eis (e + 1) (c₁ / κ) (fun y => ch ψ⁻¹ y * hat ⇑(θ * χ) y) fun _ => 1) = κ⁻¹ • (eis (e + 1) c₁ (hat φ) fun _ => 1) := by
    funext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [eis, div_eq_inv_mul]
    · rw [Pi.smul_apply, hEn (c₁ / κ) n hn, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hκ0, one_mul]
  · rw [hEE]
    have h1 := ((GlobalTheory.T.modularFormCoeffSeq_linear_structure (e + 1) (N * l) _).2.2.1 κ⁻¹ _ hE).1
    have h2 := GlobalTheory.T.modularFormCoeffSeq_mul_and_qExpansion.2 _ _ _ _ _ _ _ hF h1
    have hw : e + (e + 1) = 2 * e + 1 := by ring
    rw [hw] at h2
    exact (GlobalTheory.T.modularFormCoeffSeq_linear_structure (2 * e + 1) (N * l) _).2.2.2.1 _ _ (fun d hd => char_eq χ θ ψ φ hφ d hd) h2
  · rw [hEE, mul_smul_right, lam_smul]
    exact mul_ne_zero (inv_ne_zero hκ0) hlam

end GlobalTheory.DepletedValue

namespace GlobalTheory.DepletedValue

lemma ch_one_of_not_dvd {l : ℕ} (hl : l.Prime) {d : ℤ} (h : ¬ (l : ℤ) ∣ d) : ch (1 : DirichletCharacter ℂ l) d = 1 := by
  haveI : Fact l.Prime := ⟨hl⟩
  have h' : (d : ZMod l) ≠ 0 := fun h0 => h ((ZMod.intCast_zmod_eq_zero_iff_dvd d l).1 h0)
  exact MulChar.one_apply h'.isUnit

lemma good_one (e N l : ℕ) (χ θ : DirichletCharacter ℂ N) (φ : DirichletCharacter ℂ (N * l))
    (α c₀ c₁ : ℂ) (B : ℕ) (c : ℕ → ℂ) (he : 1 ≤ e) (hN : 0 < N) (hl : l.Prime) (hlN : ¬ l ∣ N) (hα0 : α ≠ 0)
    (hU : ∀ a, MF (2 * e + 1) (N * l) (ch χ⁻¹) a → lam B c (Uo l a) = α * lam B c a)
    (hθ : θ (-1) = (-1) ^ e * (1 : DirichletCharacter ℂ l) (-1)) (hχ : χ (-1) = -1) (hθχ : θ * χ ≠ 1)
    (hφ : ∀ d : ℤ, ch φ d = ch (θ * χ) d * ch (1 : DirichletCharacter ℂ l) d)
    (hF : MF e (N * l) (fun d => ch (1 : DirichletCharacter ℂ l) d * ch θ d) (eis e c₀ (ch (1 : DirichletCharacter ℂ l)) (ch θ)))
    (hE : MF (e + 1) (N * l) (ch φ⁻¹) (eis (e + 1) c₁ (hat φ) fun _ => 1))
    (hlam : lam B c (mul (eis e c₀ (ch (1 : DirichletCharacter ℂ l)) (ch θ)) (eis (e + 1) c₁ (hat φ) fun _ => 1)) ≠ 0)
    (hαχ : α ≠ (l : ℂ) ^ e * χ⁻¹ l) :
    ∃ c' : ℂ, MF (2 * e + 1) (N * l) (ch χ⁻¹) (mul (eis e c₀ (ch (1 : DirichletCharacter ℂ l)) (ch θ))
        (eis (e + 1) c' (fun y => ch (1 : DirichletCharacter ℂ l)⁻¹ y * hat ⇑(θ * χ) y) fun _ => 1)) ∧
      lam B c (mul (eis e c₀ (ch (1 : DirichletCharacter ℂ l)) (ch θ))
        (eis (e + 1) c' (fun y => ch (1 : DirichletCharacter ℂ l)⁻¹ y * hat ⇑(θ * χ) y) fun _ => 1)) ≠ 0 := by
  haveI : Fact l.Prime := ⟨hl⟩
  have hcop : N.Coprime l := (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hl).2 hlN))
  have hlZ : IsCoprime (l : ℤ) (N : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop.symm
  have hNZ : IsCoprime (N : ℤ) (l : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
  set θ' := θ * χ with hθ'
  set FF := eis e c₀ (ch (1 : DirichletCharacter ℂ l)) (ch θ) with hFF
  obtain ⟨hper, htw, hz⟩ := (GlobalTheory.T.dirichletCharFiniteFourierTransform_properties).1 N θ' hN

  obtain ⟨c'', hBs⟩ := GlobalTheory.T.eisenstein_periodic_weights_isModularForm (e + 1) N 1 (hat ⇑θ') (fun _ => 1) (ch θ'⁻¹) (fun _ => 1) (by omega) hN one_pos
    (hz hθχ) hper (fun _ => rfl) (fun d hd => ⟨fun x => htw d x (by simpa using hd), fun x => by simp⟩) (by
      have h1 : ch θ (-1) = θ (-1) := by simp [ch]
      have h2 : ch χ (-1) = χ (-1) := by simp [ch]
      have h3 : (1 : DirichletCharacter ℂ l) (-1) = 1 := MulChar.one_apply isUnit_one.neg
      rw [ch_inv, ch_mul, h1, h2, hθ, hχ, h3, pow_succ]
      simp
      rw [← inv_pow, inv_neg, inv_one])
  rw [Nat.mul_one] at hBs
  set Bs := eis (e + 1) c'' (hat ⇑θ') fun _ => 1 with hBsdef
  have hBsL : MF (e + 1) (N * l) (fun d => ch θ'⁻¹ d * 1) Bs := (GlobalTheory.T.modularFormCoeffSeq_linear_structure (e + 1) N _).2.2.2.2.1 _ _ (dvd_mul_right N l) hBs
  have hVBs : MF (e + 1) (N * l) (fun d => ch θ'⁻¹ d * 1) (Vo l Bs) := (GlobalTheory.T.coeffHeckeVOperator_raises_level (e + 1) N l _ Bs hl.pos).1 hBs
  set et := ch θ'⁻¹ (l : ℤ) with het
  have hVpart : ∀ n, n ≠ 0 → eis (e + 1) c'' (fun x => if (l : ℤ) ∣ x then hat ⇑θ' x else 0) (fun _ => 1) n = et * (l : ℂ) ^ e * Vo l Bs n := by
    intro n hn
    have := (GlobalTheory.T.coeffEisensteinSeriesTwisted_heckeU_heckeV (e + 1) l c'' et (hat ⇑θ') (fun _ => 1) hl).2 (by omega) (fun x => by rw [mul_comm]; exact htw l x hlZ) n hn
    simpa using this

  have hinv : (1 : DirichletCharacter ℂ l)⁻¹ = 1 := inv_one
  have hEE : (eis (e + 1) (c'' + (-(et * (l : ℂ) ^ e)) * c'') (fun y => ch (1 : DirichletCharacter ℂ l)⁻¹ y * hat ⇑θ' y) fun _ => 1) =
      Bs + (-(et * (l : ℂ) ^ e)) • Vo l Bs := by
    funext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hBsdef, eis, Vo]
    · rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, neg_mul (et * (l : ℂ) ^ e) (Vo l Bs n), ← hVpart n hn, hBsdef]
      simp only [eis, if_neg hn, hinv]
      rw [← sub_eq_add_neg, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      by_cases h : (l : ℤ) ∣ (p.1 : ℤ)
      · simp [h, ch_dvd hl 1 h]
      · simp [h, ch_one_of_not_dvd hl h]

  have hEEmf : MF (e + 1) (N * l) (fun d => ch θ'⁻¹ d * 1) (Bs + (-(et * (l : ℂ) ^ e)) • Vo l Bs) :=
    ((GlobalTheory.T.modularFormCoeffSeq_linear_structure (e + 1) (N * l) _).2.1 _ _ hBsL ((GlobalTheory.T.modularFormCoeffSeq_linear_structure (e + 1) (N * l) _).2.2.1 _ _ hVBs).1).1

  have hprod : ∀ G, MF (e + 1) (N * l) (fun d => ch θ'⁻¹ d * 1) G → MF (2 * e + 1) (N * l) (ch χ⁻¹) (mul FF G) := by
    intro G hG
    have h2 := GlobalTheory.T.modularFormCoeffSeq_mul_and_qExpansion.2 _ _ _ _ _ _ _ hF hG
    have hw : e + (e + 1) = 2 * e + 1 := by ring
    rw [hw] at h2
    refine (GlobalTheory.T.modularFormCoeffSeq_linear_structure (2 * e + 1) (N * l) _).2.2.2.1 _ _ (fun d hd => ?_) h2
    have h1 := ch_ne_zero θ (coprime_left hd)
    have h3 := ch_ne_zero χ (coprime_left hd)
    simp only [ch_one (coprime_right hd), ch_inv, hθ', ch_mul]
    field_simp

  have hhatE : ∀ x, hat φ x = ch θ' l * (hat ⇑θ' x * ((if (l : ℤ) ∣ x then (l : ℂ) else 0) - 1)) := by
    intro x
    rw [(GlobalTheory.T.dirichletCharFiniteFourierTransform_properties).2.1 N l θ' 1 φ hN hl.pos hcop hφ x, ((GlobalTheory.T.dirichletCharFiniteFourierTransform_properties).2.2 l 1 hl).2 rfl x, ch_one hNZ, mul_one]
  have hEn : ∀ n, n ≠ 0 → (eis (e + 1) c₁ (hat φ) fun _ => 1) n =
      ((ch θ' l * (et * (l : ℂ) ^ (e + 1))) • Vo l Bs + (-ch θ' l) • Bs) n := by
    intro n hn
    have hV := hVpart n hn
    have hsplit : ((ch θ' l * (et * (l : ℂ) ^ (e + 1))) • Vo l Bs + (-ch θ' l) • Bs) n =
        ch θ' l * (l : ℂ) * eis (e + 1) c'' (fun x => if (l : ℤ) ∣ x then hat ⇑θ' x else 0) (fun _ => 1) n - ch θ' l * Bs n := by
      rw [hV, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, pow_succ]; ring
    rw [hsplit, hBsdef]
    simp only [eis, if_neg hn, Finset.mul_sum, ← Finset.sum_sub_distrib, hhatE]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    split_ifs <;> ring
  have hRmf : MF (e + 1) (N * l) (ch φ⁻¹) ((ch θ' l * (et * (l : ℂ) ^ (e + 1))) • Vo l Bs + (-ch θ' l) • Bs) := by
    have h1 := ((GlobalTheory.T.modularFormCoeffSeq_linear_structure (e + 1) (N * l) _).2.1 _ _ ((GlobalTheory.T.modularFormCoeffSeq_linear_structure (e + 1) (N * l) _).2.2.1 (ch θ' l * (et * (l : ℂ) ^ (e + 1))) _ hVBs).1
      ((GlobalTheory.T.modularFormCoeffSeq_linear_structure (e + 1) (N * l) _).2.2.1 (-ch θ' l) _ hBsL).1).1
    refine (GlobalTheory.T.modularFormCoeffSeq_linear_structure (e + 1) (N * l) _).2.2.2.1 _ _ (fun d hd => ?_) h1
    simp only [ch_inv, hφ, ch_one (coprime_right hd), mul_one]
  have hEeq := GlobalTheory.T.modularFormCoeffSeq_eq_of_pos_coeff_eq (e + 1) (N * l) _ _ _ (by omega) (Nat.mul_pos hN hl.pos) hE hRmf hEn

  have hUFF := U_FF e N l he hN hl θ 1 c₀ hF
  have hUV : α * lam B c (mul FF (Vo l Bs)) = θ l * lam B c (mul FF Bs) := by
    rw [← hU _ (hprod _ hVBs), (GlobalTheory.T.coeffHecke_UV_cauchyProduct_identities ℂ l hl.pos).1, hUFF, mul_smul_left, lam_smul]
  have hlamE : lam B c (mul FF (eis (e + 1) c₁ (hat φ) fun _ => 1)) =
      ch θ' l * (et * (l : ℂ) ^ (e + 1)) * lam B c (mul FF (Vo l Bs)) + (-ch θ' l) * lam B c (mul FF Bs) := by
    rw [hEeq, mul_add_right, mul_smul_right, mul_smul_right, lam_add, lam_smul, lam_smul]
  have hB0 : lam B c (mul FF Bs) ≠ 0 := by
    intro h0
    have hV0 : lam B c (mul FF (Vo l Bs)) = 0 := by
      have := hUV; rw [h0, mul_zero] at this
      exact (mul_eq_zero.mp this).resolve_left hα0
    exact hlam (by rw [hlamE, hV0, h0]; ring)
  have hetθ : et * θ l = χ⁻¹ l := by
    have h1 : ch θ (l : ℤ) ≠ 0 := ch_ne_zero θ hlZ
    have h3 : ch χ (l : ℤ) ≠ 0 := ch_ne_zero χ hlZ
    have e1 : θ l = ch θ (l : ℤ) := by simp [ch]
    have e2 : χ⁻¹ l = ch χ⁻¹ (l : ℤ) := by simp [ch]
    rw [e1, e2, het, ch_inv, ch_inv, hθ', ch_mul]
    field_simp
  refine ⟨c'' + (-(et * (l : ℂ) ^ e)) * c'', ?_, ?_⟩
  · rw [hEE]; exact hprod _ hEEmf
  · rw [hEE, mul_add_right, mul_smul_right, lam_add, lam_smul]
    intro h0
    have : (α - (l : ℂ) ^ e * χ⁻¹ l) * lam B c (mul FF Bs) = 0 := by
      rw [← hetθ]
      linear_combination α * h0 + et * (l : ℂ) ^ e * hUV
    rcases mul_eq_zero.mp this with h | h
    · exact hαχ (sub_eq_zero.mp h)
    · exact hB0 h

end GlobalTheory.DepletedValue

namespace GlobalTheory.EisM

theorem val_depleted_ne_zero : ∀ (e N l : ℕ) (χ θ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ l) (φ : DirichletCharacter ℂ (N * l)) (t : ℕ → ℂ) (α c₀ c₁ : ℂ) (B : ℕ) (c : ℕ → ℂ), 1 ≤ e → 0 < N → l.Prime → ¬ l ∣ N → α ≠ 0 → EigF (2 * e + 1) N l χ⁻¹ t α B c → θ (-1) = (-1) ^ e * ψ (-1) → χ (-1) = -1 → θ * χ ≠ 1 → (∀ d : ℤ, ch φ d = ch (θ * χ) d * ch ψ d) → MF e (N * l) (fun d => ch ψ d * ch θ d) (eis e c₀ (ch ψ) (ch θ)) → MF (e + 1) (N * l) (ch φ⁻¹) (eis (e + 1) c₁ (hat φ) fun _ => 1) → lam B c (mul (eis e c₀ (ch ψ) (ch θ)) (eis (e + 1) c₁ (hat φ) fun _ => 1)) ≠ 0 → α ≠ θ l → α ≠ (l : ℂ) ^ e * χ⁻¹ l → val B c l α 1 (Zs (2 * e + 1) l (ch θ) (hat ⇑(θ * χ)) (fun x y => ψ x * ψ⁻¹ y * ((y : ℂ) / x) ^ e)) ≠ 0 := by
  intro e N l χ θ ψ φ t α c₀ c₁ B c he hN hl hlN hα0 hEig hθ hχ hθχ hφ hF hE hlam hαθ hαχ
  obtain ⟨c', hmf, hne⟩ : ∃ c' : ℂ, MF (2 * e + 1) (N * l) (ch χ⁻¹) (mul (eis e c₀ (ch ψ) (ch θ)) (eis (e + 1) c' (fun y => ch ψ⁻¹ y * hat ⇑(θ * χ) y) fun _ => 1)) ∧
      lam B c (mul (eis e c₀ (ch ψ) (ch θ)) (eis (e + 1) c' (fun y => ch ψ⁻¹ y * hat ⇑(θ * χ) y) fun _ => 1)) ≠ 0 := by
    rcases eq_or_ne ψ 1 with rfl | hψ
    · exact GlobalTheory.DepletedValue.good_one e N l χ θ φ α c₀ c₁ B c he hN hl hlN hα0 hEig.U hθ hχ hθχ hφ hF hE hlam hαχ
    · exact GlobalTheory.DepletedValue.good_ne e N l χ θ ψ φ c₀ c₁ B c he hN hl hlN hψ hφ hF hE hlam
  rw [GlobalTheory.DepletedValue.zs_eq e l he θ χ ψ c₀ c']
  exact GlobalTheory.DepletedValue.core hl.pos B c α (θ l) _ _ (GlobalTheory.DepletedValue.U_FF e N l he hN hl θ ψ c₀ hF) (GlobalTheory.DepletedValue.U_EE e N l hl (θ * χ) ψ c')
    (hEig.U _ hmf) hne hαθ hα0

end GlobalTheory.EisM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepletedEisensteinProductValueNeZeroOfRankinStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depletedEisensteinProduct_value_ne_zero_of_rankin : ∀ (e N l : ℕ) (χ θ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ l) (φ : DirichletCharacter ℂ (N * l)) (t : ℕ → ℂ) (α c₀ c₁ : ℂ) (B : ℕ) (c : ℕ → ℂ), 1 ≤ e → 0 < N → l.Prime → ¬ l ∣ N → α ≠ 0 → EigF (2 * e + 1) N l χ⁻¹ t α B c → θ (-1) = (-1) ^ e * ψ (-1) → χ (-1) = -1 → θ * χ ≠ 1 → (∀ d : ℤ, ch φ d = ch (θ * χ) d * ch ψ d) → MF e (N * l) (fun d => ch ψ d * ch θ d) (eis e c₀ (ch ψ) (ch θ)) → MF (e + 1) (N * l) (ch φ⁻¹) (eis (e + 1) c₁ (hat φ) fun _ => 1) → lam B c (mul (eis e c₀ (ch ψ) (ch θ)) (eis (e + 1) c₁ (hat φ) fun _ => 1)) ≠ 0 → α ≠ θ l → α ≠ (l : ℂ) ^ e * χ⁻¹ l → val B c l α 1 (Zs (2 * e + 1) l (ch θ) (hat ⇑(θ * χ)) (fun x y => ψ x * ψ⁻¹ y * ((y : ℂ) / x) ^ e)) ≠ 0 := by
  first | exact @GlobalTheory.EisM.val_depleted_ne_zero | exact GlobalTheory.EisM.val_depleted_ne_zero | (intros; apply GlobalTheory.EisM.val_depleted_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeRootsNePrimePowMulRootOfUnity
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeRootsNePrimePowMulRootOfUnity
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.FactorsAtL

theorem norm_one_of_pow {R : Type*} [NormedDivisionRing R] {z : R} {n : ℕ} (hn : 0 < n) (h : z ^ n = 1) :
    ‖z‖ = 1 := by
  have : ‖z‖ ^ n = 1 := by rw [← norm_pow, h, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg z) hn.ne').1 this

theorem char_inv_facts {N : ℕ} (hN : 0 < N) (χ : DirichletCharacter ℂ N) (l : ℕ) (hl : l.Coprime N) :
    (χ⁻¹ (l : ZMod N)) ^ N.totient = 1 ∧ χ⁻¹ (l : ZMod N) * χ (l : ZMod N) = 1 := by
  haveI : NeZero N := ⟨hN.ne'⟩
  have hu : IsUnit (l : ZMod N) := (ZMod.isUnit_iff_coprime l N).2 hl
  constructor
  · obtain ⟨v, hv⟩ := hu
    rw [← hv, ← map_pow, ← Units.val_pow_eq_pow_val, ZMod.pow_totient, Units.val_one, map_one]
  · rw [show χ⁻¹ (l : ZMod N) * χ (l : ZMod N) = (χ⁻¹ * χ) (l : ZMod N) from rfl, MulChar.inv_mul, MulChar.one_apply hu]

theorem norm_natCast_self (l : ℕ) [Fact l.Prime] : ‖(l : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends, Padic.norm_p]

end GlobalTheory.FactorsAtL

namespace GlobalTheory.FactorsAtL

theorem factors_ne_zero : ∀ (l : ℕ) [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (e N : ℕ) (χ : DirichletCharacter ℂ N)
    (g : ℕ → ℂ) (α β ζ : ℂ), 1 ≤ e → 0 < N → ¬ l ∣ N → Prim (2 * e + 1) N χ g → α + β = χ⁻¹ l * g l →
    α * β = χ⁻¹ l * (l : ℂ) ^ (2 * e) → ‖ι.symm α‖ = 1 → (∃ n : ℕ, 0 < n ∧ ζ ^ n = 1) →
    α ≠ ζ ∧ β ≠ l * ζ ∧ ∀ j : ℕ, 1 ≤ j → α ≠ (l : ℂ) ^ j * ζ := by
  intro l _ ι e N χ g α β ζ he hN hlN hP hs hp hα ⟨n, hn, hζ⟩
  have hlp : l.Prime := Fact.out
  have hcop : l.Coprime N := (Nat.Prime.coprime_iff_not_dvd hlp).2 hlN
  obtain ⟨hut, huc⟩ := char_inv_facts hN χ l hcop
  have htot : 0 < N.totient := Nat.totient_pos.2 hN
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hlp.one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  have hinv0 : (0 : ℝ) < (l : ℝ)⁻¹ := inv_pos.2 hl0
  have hinv1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  have hnl : ‖ι.symm (l : ℂ)‖ = (l : ℝ)⁻¹ := by rw [map_natCast]; exact norm_natCast_self l
  have hnζ : ‖ι.symm ζ‖ = 1 := norm_one_of_pow hn (by rw [← map_pow, hζ, map_one])
  have hnu : ‖ι.symm (χ⁻¹ (l : ZMod N))‖ = 1 := norm_one_of_pow htot (by rw [← map_pow, hut, map_one])
  refine ⟨?_, ?_, ?_⟩
  · intro hαζ
    have hcα : ‖α‖ = 1 := by rw [hαζ]; exact Complex.norm_eq_one_of_pow_eq_one hζ hn.ne'
    have hcu : ‖χ⁻¹ (l : ZMod N)‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hut htot.ne'
    have hβn : ‖β‖ = (l : ℝ) ^ (2 * e) := by
      have h := congrArg norm hp
      rw [norm_mul, norm_mul, hcα, hcu, norm_pow, Complex.norm_natCast, one_mul, one_mul] at h
      exact h
    obtain ⟨_, hrec, _⟩ := GlobalTheory.T.depletedCuspEigenform_heckeRelations (2 * e + 1) N χ g (by omega) hN hP
    obtain ⟨_, ⟨C, hC⟩, _⟩ := GlobalTheory.T.rankin_mean_square_cuspForm (2 * e + 1) N (ch χ) g (by omega) hP.cf
    set u := χ⁻¹ (l : ZMod N) with hu_def
    let c : ℕ → ℂ := fun r => u ^ r * g (l ^ r)
    have hc0 : c 0 = 1 := by simp [c, hP.one]
    have hc1 : c 1 = α + β := by simp [c, hs]
    have hcr : ∀ r, c (r + 2) = (α + β) * c (r + 1) - α * β * c r := by
      intro r
      simp only [c]
      rw [hrec l r hlp hlN, hs, hp, show 2 * e + 1 - 1 = 2 * e by omega]
      have key : u ^ (r + 2) * χ (l : ZMod N) = u ^ (r + 1) := by rw [pow_succ, mul_assoc, huc, mul_one]
      linear_combination (-(l : ℂ) ^ (2 * e) * g (l ^ r)) * key
    set s := Real.sqrt l with hs_def
    have hs2 : s ^ 2 = l := Real.sq_sqrt hl0.le
    have hs1 : 1 < s := by rw [hs_def]; exact Real.lt_sqrt (by norm_num) |>.2 (by simpa using hl1)
    set R := s ^ (2 * e + 1) with hR
    have hR0 : 0 ≤ R := by positivity
    have hbound : ∀ r, ‖c r‖ ≤ Real.sqrt (max C 0) * R ^ r := by
      intro r
      have h1 : ‖c r‖ = ‖g (l ^ r)‖ := by
        simp only [c]; rw [norm_mul, norm_pow, hcu, one_pow, one_mul]
      have hX : ((l ^ r : ℕ) : ℝ) ^ (2 * e + 1) = (R ^ r) ^ 2 := by
        push_cast; rw [hR, ← hs2]; ring
      have h2 : ‖g (l ^ r)‖ ^ 2 ≤ max C 0 * (R ^ r) ^ 2 := by
        rw [← hX]; exact (hC _).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
      rw [h1, ← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq (pow_nonneg hR0 r), ← Real.sqrt_mul (le_max_right _ _)]
      exact Real.sqrt_le_sqrt h2
    obtain ⟨_, hβR⟩ := GlobalTheory.T.roots_norm_le_of_bounded_two_step_recurrence α β c (Real.sqrt (max C 0)) R hR0 hc0 hc1 hcr hbound
    rw [hβn, ← hs2, ← pow_mul, hR] at hβR
    have : s ^ (2 * e + 1) < s ^ (2 * (2 * e)) := pow_lt_pow_right₀ hs1 (by omega)
    linarith
  · intro hβζ
    have h := congrArg (fun z => ‖ι.symm z‖) hp
    simp only [map_mul, map_pow, norm_mul, norm_pow] at h
    rw [hα, hnu, hnl, one_mul, one_mul, hβζ, map_mul, norm_mul, hnl, hnζ, mul_one] at h
    have : ((l : ℝ)⁻¹) ^ (2 * e) < ((l : ℝ)⁻¹) ^ 1 := pow_lt_pow_right_of_lt_one₀ hinv0 hinv1 (by omega)
    rw [pow_one] at this
    linarith
  · intro j hj hαj
    rw [hαj, map_mul, map_pow, norm_mul, norm_pow, hnl, hnζ, mul_one] at hα
    have : ((l : ℝ)⁻¹) ^ j < 1 := pow_lt_one₀ hinv0.le hinv1 (by omega)
    linarith

end GlobalTheory.FactorsAtL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeRootsNePrimePowMulRootOfUnityStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeRoots_ne_prime_pow_mul_rootOfUnity : ∀ (l : ℕ) [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (e N : ℕ) (χ : DirichletCharacter ℂ N) (g : ℕ → ℂ) (α β ζ : ℂ), 1 ≤ e → 0 < N → ¬ l ∣ N → Prim (2 * e + 1) N χ g → α + β = χ⁻¹ l * g l → α * β = χ⁻¹ l * (l : ℂ) ^ (2 * e) → ‖ι.symm α‖ = 1 → (∃ n : ℕ, 0 < n ∧ ζ ^ n = 1) → α ≠ ζ ∧ β ≠ l * ζ ∧ ∀ j : ℕ, 1 ≤ j → α ≠ (l : ℂ) ^ j * ζ := by
  first | exact @GlobalTheory.FactorsAtL.factors_ne_zero | exact GlobalTheory.FactorsAtL.factors_ne_zero | (intros; apply GlobalTheory.FactorsAtL.factors_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHeckeEigenfunctionalDepletedEisensteinNeZe
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM

theorem zv_unit_of_isCoprime {L : ℕ} {d : ℤ} (h : IsCoprime d (L : ℤ)) : IsUnit (d : ZMod L) := by
  obtain ⟨u, v, huv⟩ := h
  have h1 := congrArg (Int.cast : ℤ → ZMod L) huv
  push_cast at h1
  rw [ZMod.natCast_self, mul_zero, add_zero] at h1
  exact isUnit_iff_exists_inv.mpr ⟨_, (mul_comm _ _).trans h1⟩

theorem zv_apply_ne_zero {L : ℕ} (χ : DirichletCharacter ℂ L) {x : ZMod L} (hx : IsUnit x) : χ x ≠ 0 := by
  obtain ⟨u, rfl⟩ := hx
  intro h
  have h1 : χ ((u : ZMod L) * ((u⁻¹ : (ZMod L)ˣ) : ZMod L)) = 1 := by rw [Units.mul_inv, map_one]
  rw [map_mul, h, zero_mul] at h1
  exact zero_ne_one h1

theorem zv_inv_mul {L : ℕ} (χ : DirichletCharacter ℂ L) {x : ZMod L} (hx : IsUnit x) : χ⁻¹ x * χ x = 1 := by
  rw [MulChar.inv_apply_eq_inv']
  exact inv_mul_cancel₀ (zv_apply_ne_zero χ hx)

theorem zv_ch_changeLevel_mul {N l : ℕ} (cop : N.Coprime l) (A : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ l)
    (d : ℤ) : ch (A.changeLevel (dvd_mul_right N l) * ψ.changeLevel (dvd_mul_left l N)) d = ch A d * ch ψ d := by
  unfold ch
  rw [MulChar.mul_apply]
  by_cases hu : IsUnit ((d : ZMod (N * l)))
  · obtain ⟨u, hu⟩ := hu
    rw [← hu, DirichletCharacter.changeLevel_eq_cast_of_dvd, DirichletCharacter.changeLevel_eq_cast_of_dvd, hu,
      ZMod.cast_intCast (dvd_mul_right N l), ZMod.cast_intCast (dvd_mul_left l N)]
  · rw [MulChar.map_nonunit _ hu, zero_mul]
    have hn : ¬ (IsUnit (d : ZMod N) ∧ IsUnit (d : ZMod l)) := by
      rintro ⟨h1, h2⟩
      apply hu
      have : IsUnit (ZMod.chineseRemainder cop (d : ZMod (N * l))) := by
        rw [map_intCast]
        exact Prod.isUnit_iff.mpr ⟨by simpa using h1, by simpa using h2⟩
      exact (isUnit_map_iff (ZMod.chineseRemainder cop) _).mp this
    rcases not_and_or.mp hn with h | h
    · rw [MulChar.map_nonunit _ h, zero_mul]
    · rw [MulChar.map_nonunit _ h, mul_zero]

theorem zv_root {N l : ℕ} (hN : 0 < N) (cop : l.Coprime N) (θ : DirichletCharacter ℂ N) :
    ∃ n : ℕ, 0 < n ∧ (θ (l : ZMod N)) ^ n = 1 := by
  haveI : NeZero N := ⟨hN.ne'⟩
  refine ⟨Fintype.card (ZMod N)ˣ, Fintype.card_pos, ?_⟩
  rw [← ZMod.coe_unitOfCoprime l cop, ← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one]

end GlobalTheory.EisM

namespace GlobalTheory.EisM

theorem eigF_value_ne_zero : ∀ (l : ℕ) [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (e N : ℕ) (χ θ : DirichletCharacter ℂ N)
    (ψ : DirichletCharacter ℂ l) (g : ℕ → ℂ) (α β : ℂ), 1 ≤ e → 0 < N → ¬ l ∣ N → Prim (2 * e + 1) N χ g →
    α + β = χ⁻¹ l * g l → α * β = χ⁻¹ l * (l : ℂ) ^ (2 * e) → ‖ι.symm α‖ = 1 → θ (-1) = (-1) ^ e * ψ (-1) →
    θ * χ ≠ 1 → ∃ (B : ℕ) (c : ℕ → ℂ), EigF (2 * e + 1) N l χ⁻¹ (fun q => χ⁻¹ q * g q) α B c ∧
      val B c l α 1 (Zs (2 * e + 1) l (ch θ) (hat ⇑(θ * χ)) (fun x y => ψ x * ψ⁻¹ y * ((y : ℂ) / x) ^ e)) ≠ 0 := by
  intro l _ ι e N χ θ ψ g α β he hN hlN hg hsum hprod hα hpar hθχ
  have hp : l.Prime := Fact.out
  have hl0 : 0 < l := hp.pos
  have hNl : 0 < N * l := Nat.mul_pos hN hl0
  have cop : N.Coprime l := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hlN).symm
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.exists_gammaZeroPartitionWeight (N * l) hNl
  have hprod' : α * β = χ⁻¹ l * (l : ℂ) ^ (2 * e + 1 - 1) := by rw [Nat.add_sub_cancel]; exact hprod
  obtain ⟨B, c, hEig, hlam⟩ := GlobalTheory.T.exists_heckeEigenfunctional_of_depletedEigenform (2 * e + 1) N l χ g ρ α β (by omega) hN hp hlN hg hρ hsum hprod'
  refine ⟨B, c, hEig, ?_⟩
  have hχm : χ (-1) = -1 :=
    (GlobalTheory.T.odd_chi_and_tendsto_twisted_LSeries_ne_zero_of_prim (2 * e + 1) N 1 χ 1 g ((((2 * e + 1 : ℕ) : ℝ) + 1) / 2) ⟨e, rfl⟩ hN one_pos hg le_rfl).1

  obtain ⟨φ, hφ⟩ : ∃ φ : DirichletCharacter ℂ (N * l), ∀ d : ℤ, ch φ d = ch (θ * χ) d * ch ψ d :=
    ⟨_, zv_ch_changeLevel_mul cop _ _⟩
  have hφ1 : φ ≠ 1 := by
    intro h1
    apply hθχ
    ext a
    obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder cop (a : ZMod N).val 1
    haveI : NeZero N := ⟨hN.ne'⟩
    have hkN : ((k : ℕ) : ZMod N) = a := by
      rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr hk1, ZMod.natCast_zmod_val]
    have hkl : ((k : ℕ) : ZMod l) = 1 := by
      rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr hk2, Nat.cast_one]
    have hk : ch φ ((k : ℕ) : ℤ) = (θ * χ) a := by
      rw [hφ]; unfold ch; push_cast; rw [hkN, hkl, map_one, mul_one]
    rw [h1] at hk
    unfold ch at hk
    rw [MulChar.one_apply_coe]
    by_cases hu : IsUnit ((((k : ℕ) : ℤ)) : ZMod (N * l))
    · rw [MulChar.one_apply hu] at hk; exact hk.symm
    · rw [MulChar.map_nonunit _ hu] at hk; exact absurd hk.symm (zv_apply_ne_zero (θ * χ) a.isUnit)

  have hψ2 : ψ (-1) * ψ (-1) = 1 := by rw [← map_mul, neg_one_mul, neg_neg, map_one]
  have hφm : ch φ (-1) = (-1) ^ e * ψ (-1) * (-1) * ψ (-1) := by
    rw [hφ]; unfold ch; push_cast; rw [MulChar.mul_apply, hpar, hχm]

  obtain ⟨c₀, hFF⟩ := GlobalTheory.T.eisenstein_periodic_weights_isModularForm e l N (ch ψ) (ch θ) (ch ψ) (ch θ) he hl0 hN
    (by unfold ch; push_cast; exact MulChar.map_zero ψ)
    (fun x => by unfold ch; push_cast; rw [ZMod.natCast_self, add_zero])
    (fun x => by unfold ch; push_cast; rw [ZMod.natCast_self, add_zero])
    (fun d _ => ⟨fun x => by unfold ch; push_cast; rw [map_mul, mul_comm],
      fun x => by unfold ch; push_cast; rw [map_mul, mul_comm]⟩)
    (by unfold ch; push_cast; rw [hpar]; linear_combination (-1 : ℂ) ^ e * hψ2)
  rw [mul_comm l N] at hFF

  have hat0 : hat φ 0 = 0 := ((GlobalTheory.T.dirichletCharFiniteFourierTransform_properties).1 (N * l) φ hNl).2.2 hφ1
  obtain ⟨c₁, hE, hlat⟩ := GlobalTheory.T.eisenstein_latticeFunction_isModularFormCoeffSeq (e + 1) (N * l) 1 (fun _ => 1) (ch φ⁻¹) (fun _ => 1) φ (by omega) hNl one_pos
    hat0 (fun _ => rfl)
    (fun d hd => by
      have hu : IsUnit (d : ZMod (N * l)) := zv_unit_of_isCoprime (by simpa using hd)
      refine ⟨fun y => ?_, fun x => by ring⟩
      unfold ch
      rw [map_mul, ← mul_assoc, mul_comm (φ⁻¹ _), mul_assoc, zv_inv_mul φ hu, mul_one])
    (by
      rw [mul_one]
      unfold ch
      rw [MulChar.inv_apply_eq_inv']
      have := hφm; unfold ch at this; rw [this]
      apply inv_eq_of_mul_eq_one_left
      have hm : ((-1 : ℂ) ^ e) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      linear_combination ((-1 : ℂ) ^ e) ^ 2 * hψ2 + hm)
  rw [mul_one] at hE
  have hE' : MF (e + 1) (N * l) (ch φ⁻¹) (eis (e + 1) c₁ (hat ⇑φ) fun _ => 1) := by
    simpa only [mul_one] using hE

  set FF := eis e c₀ (ch ψ) (ch θ) with hFFdef
  set E := eis (e + 1) c₁ (hat ⇑φ) fun _ => 1 with hEdef
  have hX : MF (2 * e + 1) (N * l) (ch χ⁻¹) (mul FF E) := by
    have h1 := (GlobalTheory.T.modularFormCoeffSeq_mul_and_qExpansion).2 e (e + 1) (N * l) _ _ FF E hFF hE'
    rw [show e + (e + 1) = 2 * e + 1 by ring] at h1
    refine (GlobalTheory.T.modularFormCoeffSeq_linear_structure (2 * e + 1) (N * l) _).2.2.2.1 _ _ (fun d hd => ?_) h1
    have hu : IsUnit (d : ZMod (N * l)) := zv_unit_of_isCoprime hd
    have hd' : IsCoprime d (N : ℤ) := by
      have : IsCoprime d ((N : ℤ) * (l : ℤ)) := by simpa using hd
      exact this.of_mul_right_left
    have hd'' : IsCoprime d (l : ℤ) := by
      have : IsCoprime d ((N : ℤ) * (l : ℤ)) := by simpa using hd
      exact this.of_mul_right_right
    have uN := zv_unit_of_isCoprime hd'
    have ul := zv_unit_of_isCoprime hd''
    have e1 := hφ d
    unfold ch at e1 ⊢
    rw [MulChar.mul_apply] at e1
    rw [MulChar.inv_apply_eq_inv', MulChar.inv_apply_eq_inv', e1]
    have := zv_apply_ne_zero θ uN
    have := zv_apply_ne_zero χ uN
    have := zv_apply_ne_zero ψ ul
    field_simp
  have hqs : qs (mul FF E) = fun τ => qs FF τ * qs E τ := ((GlobalTheory.T.modularFormCoeffSeq_mul_and_qExpansion).1 FF E hFF.1 hE'.1).2
  obtain ⟨κ, hκ, hlat'⟩ : ∃ κ : ℂ, κ ≠ 0 ∧ ∀ τ : ℍ,
      lat (e + 1) 0 (N * l) (0, 1) (latF (N * l) (fun _ => 1) φ) τ = κ * qs E τ :=
    ⟨_, by
      have : ((N * l : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hNl.ne'
      have h2 : (-2 * (π : ℂ) * Complex.I) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
      have h3 : (((e + 1 - 1).factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
      exact div_ne_zero (mul_ne_zero two_ne_zero (pow_ne_zero _ (div_ne_zero h2 this))) h3, hlat⟩
  have hpet : ∀ h : ℍ → ℂ, pet (2 * e + 1) ρ h (qs (mul FF E)) =
      κ⁻¹ * pet (2 * e + 1) ρ h (fun τ => qs FF τ * lat (e + 1) 0 (N * l) (0, 1) (latF (N * l) (fun _ => 1) φ) τ) := by
    intro h
    unfold pet
    rw [← integral_const_mul]
    congr 1
    funext τ
    rw [hqs]
    beta_reduce
    rw [hlat' τ]
    field_simp
  obtain ⟨P, hP0, hP1, hP2⟩ := GlobalTheory.T.pet_eis_lat_eq_and_vo_eq_mul e N l χ θ ψ φ g ρ c₀ he hN hp hlN hg hρ hφ hφ1 hFF

  have copl : l.Coprime N := cop.symm
  have hα0 : α ≠ 0 := by
    intro h; rw [h, map_zero, norm_zero] at hα; exact zero_ne_one hα
  have fθ := GlobalTheory.T.heckeRoots_ne_prime_pow_mul_rootOfUnity l ι e N χ g α β (θ l) he hN hlN hg hsum hprod hα (zv_root hN copl θ)
  have fχ := GlobalTheory.T.heckeRoots_ne_prime_pow_mul_rootOfUnity l ι e N χ g α β (χ⁻¹ l) he hN hlN hg hsum hprod hα (zv_root hN copl χ⁻¹)
  have hlamX : lam B c (mul FF E) ≠ 0 := by
    rw [hlam _ hX, hpet, hpet, hP1, hP2]
    intro h0
    have hl : (l : ℂ) ≠ 0 := by exact_mod_cast hl0.ne'
    have hκi : κ⁻¹ ≠ 0 := inv_ne_zero hκ
    have h3 : κ⁻¹ * P / (l : ℂ) ^ (2 * e + 1) * ((l : ℂ) * θ l - β) = 0 := by
      rw [← h0]; field_simp; ring
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact div_ne_zero (mul_ne_zero hκi hP0) (pow_ne_zero _ hl) h4
    · exact fθ.2.1 (by linear_combination -h4)
  exact GlobalTheory.T.depletedEisensteinProduct_value_ne_zero_of_rankin e N l χ θ ψ φ (fun q => χ⁻¹ q * g q) α c₀ c₁ B c he hN hp hlN hα0 hEig hpar hχm hθχ hφ hFF hE'
    hlamX fθ.1 (fχ.2.2 e he)

end GlobalTheory.EisM
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHeckeEigenfunctionalDepletedEisensteinNeZeStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heckeEigenfunctional_depletedEisenstein_ne_zero : ∀ (l : ℕ) [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (e N : ℕ) (χ θ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ l) (g : ℕ → ℂ) (α β : ℂ), 1 ≤ e → 0 < N → ¬ l ∣ N → Prim (2 * e + 1) N χ g → α + β = χ⁻¹ l * g l → α * β = χ⁻¹ l * (l : ℂ) ^ (2 * e) → ‖ι.symm α‖ = 1 → θ (-1) = (-1) ^ e * ψ (-1) → θ * χ ≠ 1 → ∃ (B : ℕ) (c : ℕ → ℂ), EigF (2 * e + 1) N l χ⁻¹ (fun q => χ⁻¹ q * g q) α B c ∧ val B c l α 1 (Zs (2 * e + 1) l (ch θ) (hat ⇑(θ * χ)) (fun x y => ψ x * ψ⁻¹ y * ((y : ℂ) / x) ^ e)) ≠ 0 := by
  first | exact @GlobalTheory.EisM.eigF_value_ne_zero | exact GlobalTheory.EisM.eigF_value_ne_zero | (intros; apply GlobalTheory.EisM.eigF_value_ne_zero <;> assumption)
end
