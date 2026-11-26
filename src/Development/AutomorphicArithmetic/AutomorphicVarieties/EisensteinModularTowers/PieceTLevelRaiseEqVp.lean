module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedEisensteinFxSumRowLiftsDistribution
public import Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.SmoothedEisensteinCongrOfModEq

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinPieceUnitSetLevelSuccEq
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumGl2FirstColumnUnitSetSuccFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumGl2FirstColumnUnitSetSuccFibre
noncomputable section

open GlobalTheory.KummerEisensteinGalois Finset
open scoped Classical

namespace GlobalTheory.KummerEisensteinGalois

theorem glFibre_val_map {p n : ℕ} [NeZero p] (x : ZMod (p ^ (n + 1))) :
    (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) x).val = x.val % p ^ n := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]

theorem glFibre_isUnit_iff {p : ℕ} [Fact p.Prime] {n : ℕ} (hn : 1 ≤ n) (x : ZMod (p ^ n)) :
    IsUnit x ↔ ¬ p ∣ x.val := by
  have hp : p.Prime := Fact.out
  conv_lhs => rw [← ZMod.natCast_zmod_val x]
  rw [ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff (by omega), Nat.coprime_comm,
    hp.coprime_iff_not_dvd]

theorem glFibre_dvd_map_iff {p : ℕ} [Fact p.Prime] {n : ℕ} (hn : 1 ≤ n) (x : ZMod (p ^ (n + 1))) :
    p ∣ (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) x).val ↔ p ∣ x.val := by
  rw [glFibre_val_map, Nat.dvd_mod_iff (dvd_pow_self p (by omega))]

theorem sum_unitSet_succ_fibre : ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (K : Type) [CommRing K] (G : GL (Fin 2) (ZMod (p ^ n)) → K) (Φ : ZMod (p ^ (n + 1)) → ZMod (p ^ (n + 1)) → ZMod (p ^ (n + 1)) → ZMod (p ^ (n + 1)) → K), 1 ≤ n → ∑ γ ∈ unitSet p (n + 1), G (Matrix.GeneralLinearGroup.map (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))) γ) * Φ ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 0 0) ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 0 1) ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 1 0) ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 1 1) = ∑ γ ∈ unitSet p n, G γ * ∑ y₀₀ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 0 0)), ∑ y₀₁ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 0 1)), ∑ y₁₀ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 1 0)), ∑ y₁₁ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 1 1)), Φ y₀₀ y₀₁ y₁₀ y₁₁ := by
  intro p _ n K _ G Φ hn
  set ρ := ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) with hρ
  have hent : ∀ (γ : GL (Fin 2) (ZMod (p ^ (n + 1)))) (a b : Fin 2),
      (Matrix.GeneralLinearGroup.map ρ γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) a b =
        ρ ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) a b) := fun _ _ _ => rfl
  have hmaps : ∀ γ ∈ unitSet p (n + 1), Matrix.GeneralLinearGroup.map ρ γ ∈ unitSet p n := by
    intro γ hγ
    simp only [unitSet, mem_filter, mem_univ, true_and] at hγ ⊢
    rw [hent, hent, hρ, glFibre_dvd_map_iff hn, glFibre_dvd_map_iff hn]
    exact hγ
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl (fun g hg => ?_)
  rw [Finset.sum_congr rfl (fun γ hγ => by rw [(mem_filter.mp hγ).2]), ← Finset.mul_sum]
  congr 1
  simp only [← Finset.sum_product']
  refine Finset.sum_bij (fun γ _ => (((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 0 0),
      ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 0 1),
      ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 1 0),
      ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 1 1))) ?_ ?_ ?_ ?_
  · intro γ hγ
    obtain ⟨_, hγg⟩ := mem_filter.mp hγ
    simp only [mem_product, mem_filter, mem_univ, true_and, ← hγg, hent, and_self]
  · intro γ _ δ _ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    ext a b
    fin_cases a <;> fin_cases b
    exacts [h1, h2, h3, h4]
  · rintro ⟨a, b, c, d⟩ hb
    simp only [mem_product, mem_filter, mem_univ, true_and] at hb
    obtain ⟨ha, hb', hc, hd⟩ := hb
    let B : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1))) := !![a, b; c, d]
    have hBm : ρ.mapMatrix B = (g : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) := by
      ext i j
      fin_cases i <;> fin_cases j
      exacts [ha, hb', hc, hd]
    have hdet : IsUnit B.det := by
      have h1 : IsUnit (ρ B.det) := by
        rw [RingHom.map_det, hBm]; exact (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit
      rw [glFibre_isUnit_iff hn, hρ, glFibre_dvd_map_iff hn] at h1
      exact (glFibre_isUnit_iff (by omega) _).mpr h1
    obtain ⟨γ, hγ⟩ := (Matrix.isUnit_iff_isUnit_det B).mpr hdet
    have hmap : Matrix.GeneralLinearGroup.map ρ γ = g := by
      apply Units.ext
      rw [← hBm, ← hγ]; rfl
    refine ⟨γ, ?_, ?_⟩
    · refine mem_filter.mpr ⟨?_, hmap⟩
      simp only [unitSet, mem_filter, mem_univ, true_and] at hg ⊢
      rw [← glFibre_dvd_map_iff hn, ← glFibre_dvd_map_iff hn, ← hρ, ← hent, ← hent, hmap]
      exact hg
    · simp only [hγ, B]
      rfl
  · intro γ _
    rfl

end GlobalTheory.KummerEisensteinGalois
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumGl2FirstColumnUnitSetSuccFibreStatement
open GlobalTheory.KummerEisensteinGalois Finset
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_gl2FirstColumnUnitSet_succ_fibre : ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (K : Type) [CommRing K] (G : GL (Fin 2) (ZMod (p ^ n)) → K) (Φ : ZMod (p ^ (n + 1)) → ZMod (p ^ (n + 1)) → ZMod (p ^ (n + 1)) → ZMod (p ^ (n + 1)) → K), 1 ≤ n → ∑ γ ∈ unitSet p (n + 1), G (Matrix.GeneralLinearGroup.map (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))) γ) * Φ ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 0 0) ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 0 1) ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 1 0) ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 1 1) = ∑ γ ∈ unitSet p n, G γ * ∑ y₀₀ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 0 0)), ∑ y₀₁ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 0 1)), ∑ y₁₀ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 1 0)), ∑ y₁₁ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 1 1)), Φ y₀₀ y₀₁ y₁₀ y₁₁ := by
  first | exact @GlobalTheory.KummerEisensteinGalois.sum_unitSet_succ_fibre | exact GlobalTheory.KummerEisensteinGalois.sum_unitSet_succ_fibre | (intros; apply GlobalTheory.KummerEisensteinGalois.sum_unitSet_succ_fibre <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EePosFalseDvd
noncomputable section

open Finset
open scoped Classical

namespace GlobalTheory.KummerEisensteinGalois.UpSplit

open GlobalTheory.KummerEisensteinGalois

variable {K : Type*} [Field K] [CharZero K]

theorem cmul_vp_vp (p : ℕ) (hp : 0 < p) (f g : ℕ → K) (r : ℕ) :
    cmul (vp p f) (vp p g) (p * r) = cmul f g r := by
  unfold cmul
  symm
  have h1 : ∀ j ∈ range (r + 1), f j * g (r - j) = vp p f (p * j) * vp p g (p * r - p * j) := by
    intro j _
    simp only [vp, dvd_mul_right, if_true, ← Nat.mul_sub, Nat.mul_div_cancel_left _ hp]
  rw [sum_congr rfl h1, ← sum_image (f := fun i => vp p f i * vp p g (p * r - i)) (g := fun j => p * j)
    (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hp h)]
  apply sum_subset
  · intro i hi
    simp only [mem_image, mem_range] at hi ⊢
    obtain ⟨j, hj, rfl⟩ := hi
    have : j ≤ r := by omega
    have := Nat.mul_le_mul_left p this
    omega
  · intro i hi hni
    simp only [mem_image, mem_range, not_exists, not_and] at hi hni
    by_cases hpi : p ∣ i
    · obtain ⟨j, rfl⟩ := hpi
      exact absurd rfl (hni j (by
        have : p * j ≤ p * r := by omega
        have := Nat.le_of_mul_le_mul_left this hp
        omega))
    · simp [vp, hpi]

end GlobalTheory.KummerEisensteinGalois.UpSplit

namespace GlobalTheory.KummerEisensteinGalois


end GlobalTheory.KummerEisensteinGalois
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinPieceUnitSetLevelSuccEq
noncomputable section
open Finset
open scoped Classical
open GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.KummerEisensteinGalois.LevelT

theorem vp_cmul {K : Type} [Field K] [CharZero K] (p : ℕ) (hp : 0 < p) (f g : ℕ → K) (r : ℕ) :
    vp p (cmul f g) r = cmul (vp p f) (vp p g) r := by
  by_cases h : p ∣ r
  · obtain ⟨r', rfl⟩ := h
    rw [UpSplit.cmul_vp_vp p hp]
    simp [vp, Nat.mul_div_cancel_left _ hp]
  · rw [show vp p (cmul f g) r = 0 by simp [vp, h]]
    unfold cmul
    symm
    apply sum_eq_zero
    intro i hi
    have hi' : i ≤ r := Nat.lt_succ_iff.mp (mem_range.mp hi)
    by_cases hpi : p ∣ i
    · have : ¬ p ∣ r - i := by
        intro h2
        apply h
        have := Nat.dvd_add h2 hpi
        rwa [Nat.sub_add_cancel hi'] at this
      simp [vp, this]
    · simp [vp, hpi]

theorem cauchyProduct_fourfold_finsetSum {K : Type} [Field K] {α : Type} (s₁ s₂ s₃ s₄ : Finset α) (f g : α → α → ℕ → K) (r : ℕ) :
    ∑ a ∈ s₁, ∑ b ∈ s₂, ∑ c ∈ s₃, ∑ d ∈ s₄, cmul (f a b) (g c d) r =
      cmul (fun i => ∑ a ∈ s₁, ∑ b ∈ s₂, f a b i) (fun i => ∑ c ∈ s₃, ∑ d ∈ s₄, g c d i) r := by
  unfold cmul
  simp_rw [Finset.sum_comm (s := s₄) (t := range (r + 1))]
  simp_rw [Finset.sum_comm (s := s₃) (t := range (r + 1))]
  simp_rw [Finset.sum_comm (s := s₂) (t := range (r + 1))]
  simp_rw [Finset.sum_comm (s := s₁) (t := range (r + 1))]
  refine sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]; refine sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul]; refine sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]; refine sum_congr rfl fun c _ => ?_
  rw [Finset.mul_sum]

theorem dvd_castHom_val_iff {p : ℕ} [Fact p.Prime] {n : ℕ} (hn : 1 ≤ n) (x : ZMod (p ^ (n + 1))) :
    p ∣ (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) x).val ↔ p ∣ x.val := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast,
    Nat.dvd_mod_iff (dvd_pow_self p (by omega))]

theorem sum_preimage_fibre (p : ℕ) [Fact p.Prime] (n : ℕ) (hn : 1 ≤ n) (K : Type) [CommRing K]
    (X : Finset (GL (Fin 2) (ZMod (p ^ n))))
    (hX : ∀ γ ∈ X, ¬ p ∣ ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 0 0).val ∧ ¬ p ∣ ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 1 0).val)
    (G : GL (Fin 2) (ZMod (p ^ n)) → K)
    (Φ : ZMod (p ^ (n + 1)) → ZMod (p ^ (n + 1)) → ZMod (p ^ (n + 1)) → ZMod (p ^ (n + 1)) → K) :
    ∑ γ ∈ (univ.filter fun γ : GL (Fin 2) (ZMod (p ^ (n + 1))) => Matrix.GeneralLinearGroup.map (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))) γ ∈ X),
      G (Matrix.GeneralLinearGroup.map (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))) γ) * Φ ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 0 0) ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 0 1) ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 1 0) ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 1 1) =
    ∑ γ ∈ X, G γ * ∑ y₀₀ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 0 0)), ∑ y₀₁ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 0 1)), ∑ y₁₀ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 1 0)), ∑ y₁₁ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 1 1)), Φ y₀₀ y₀₁ y₁₀ y₁₁ := by
  set ρ := ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) with hρ
  have hS : (univ.filter fun γ : GL (Fin 2) (ZMod (p ^ (n + 1))) => Matrix.GeneralLinearGroup.map ρ γ ∈ X) =
      (unitSet p (n + 1)).filter (fun γ => Matrix.GeneralLinearGroup.map ρ γ ∈ X) := by
    ext γ
    simp only [mem_filter, mem_univ, true_and, unitSet]
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := hX _ h
      have e1 : ((Matrix.GeneralLinearGroup.map ρ γ : GL (Fin 2) (ZMod (p ^ n))) : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 0 0 = ρ ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 0 0) := rfl
      have e2 : ((Matrix.GeneralLinearGroup.map ρ γ : GL (Fin 2) (ZMod (p ^ n))) : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 1 0 = ρ ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 1 0) := rfl
      rw [e1, hρ, dvd_castHom_val_iff hn] at h1
      rw [e2, hρ, dvd_castHom_val_iff hn] at h2
      exact ⟨⟨h1, h2⟩, h⟩
    · exact fun h => h.2
  have hX' : (unitSet p n).filter (fun γ => γ ∈ X) = X := by
    ext γ
    simp only [mem_filter, unitSet, mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨hX γ h, h⟩⟩
  rw [hS, Finset.sum_filter]
  have h1 := GlobalTheory.T.sum_gl2FirstColumnUnitSet_succ_fibre p n K (fun g => if g ∈ X then G g else 0) Φ hn
  simp only [ite_mul, zero_mul] at h1
  rw [h1, ← Finset.sum_filter, hX']

end GlobalTheory.KummerEisensteinGalois.LevelT


open GlobalTheory.KummerEisensteinGalois.LevelT in
theorem GlobalTheory.KummerEisensteinGalois.pieceT_unitSet_level_succ : ∀ (p : ℕ) [Fact p.Prime] (N n m k : ℕ) (K : Type) [Field K] [CharZero K] (ψ : DirichletCharacter K (p ^ m)) (c d : ℤ) (w w' v v' : ℤ × ℤ) (ζ : K) (X : Finset (GL (Fin 2) (ZMod (p ^ n)))), IsPrimitiveRoot ζ (N * p ^ (n + 1)) → 0 < N → ¬ p ∣ N → 1 ≤ m → m ≤ n → 3 ≤ k → ¬ (p : ℤ) ∣ c → ¬ (p : ℤ) ∣ d → (p : ℤ) * v.1 ≡ w.1 [ZMOD N] → (p : ℤ) * v.2 ≡ w.2 [ZMOD N] → (p : ℤ) * v'.1 ≡ w'.1 [ZMOD N] → (p : ℤ) * v'.2 ≡ w'.2 [ZMOD N] → (∀ γ ∈ X, ¬ p ∣ ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 0 0).val ∧ ¬ p ∣ ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 1 0).val) → ∀ r : ℕ, pieceT N p (n + 1) m k ψ c d v v' ζ (Finset.univ.filter fun γ => Matrix.GeneralLinearGroup.map (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))) γ ∈ X) r = vp p (pieceT N p n m k ψ c d w w' (ζ ^ p) X) r := by
  intro p _ N n m k K _ _ ψ c d w w' v v' ζ X hζ hN hpN hm hmn hk hc hd h1 h2 h3 h4 hX r
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hn : 1 ≤ n := le_trans hm hmn
  have hdet : ∀ γ : GL (Fin 2) (ZMod (p ^ (n + 1))),
      ((((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1))))).det.val : ℕ) : ZMod (p ^ m)) =
      ((((Matrix.GeneralLinearGroup.map (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))) γ : GL (Fin 2) (ZMod (p ^ n))) : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))).det.val : ℕ) : ZMod (p ^ m)) := by
    intro γ
    have hcast : ∀ {a : ℕ} [NeZero a] (y : ZMod a) (h : p ^ m ∣ a),
        ((y.val : ℕ) : ZMod (p ^ m)) = ZMod.castHom h (ZMod (p ^ m)) y := by
      intro a _ y h
      rw [ZMod.castHom_apply, ZMod.natCast_val]
    have e : ((Matrix.GeneralLinearGroup.map (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))) γ : GL (Fin 2) (ZMod (p ^ n))) : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) =
        ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1))))).map (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))) := rfl
    rw [hcast _ (pow_dvd_pow p (by omega : m ≤ n + 1)), hcast _ (pow_dvd_pow p hmn), e, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      ← RingHom.comp_apply]
    congr 1
    exact Subsingleton.elim _ _
  have hRHS : vp p (pieceT N p n m k ψ c d w w' (ζ ^ p) X) r =
      -((p : K) ^ ((n : ℤ) * ((k : ℤ) - 4))) * ∑ γ ∈ X,
        ψ ((((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n)))).det.val : ℕ) : ZMod (p ^ m)) *
        vp p (cmul (smF c (k - 1) (N * p ^ n) (ζ ^ p) (rowT N p n γ 0 w).1 (rowT N p n γ 0 w).2)
           (smF d 1 (N * p ^ n) (ζ ^ p) (rowT N p n γ 1 w').1 (rowT N p n γ 1 w').2)) r := by
    unfold vp pieceT
    split_ifs <;> simp
  rw [hRHS]
  unfold pieceT
  have hsum := sum_preimage_fibre p n hn K X hX (fun γ => ψ ((((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n)))).det.val : ℕ) : ZMod (p ^ m)))
    (fun y₀₀ y₀₁ y₁₀ y₁₁ => cmul (smF c (k - 1) (N * p ^ (n + 1)) ζ ((N : ℤ) * (y₀₀.val : ℤ) + (p : ℤ) ^ (n + 1) * v.1) ((N : ℤ) * (y₀₁.val : ℤ) + (p : ℤ) ^ (n + 1) * v.2))
      (smF d 1 (N * p ^ (n + 1)) ζ ((N : ℤ) * (y₁₀.val : ℤ) + (p : ℤ) ^ (n + 1) * v'.1) ((N : ℤ) * (y₁₁.val : ℤ) + (p : ℤ) ^ (n + 1) * v'.2)) r)
  have hL : ∑ γ ∈ (Finset.univ.filter fun γ => Matrix.GeneralLinearGroup.map (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))) γ ∈ X), ψ ((((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1))))).det.val : ℕ) : ZMod (p ^ m)) *
      cmul (smF c (k - 1) (N * p ^ (n + 1)) ζ (rowT N p (n + 1) γ 0 v).1 (rowT N p (n + 1) γ 0 v).2)
           (smF d 1 (N * p ^ (n + 1)) ζ (rowT N p (n + 1) γ 1 v').1 (rowT N p (n + 1) γ 1 v').2) r =
      ∑ γ ∈ (Finset.univ.filter fun γ => Matrix.GeneralLinearGroup.map (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))) γ ∈ X), ψ ((((Matrix.GeneralLinearGroup.map (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))) γ : GL (Fin 2) (ZMod (p ^ n))) : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))).det.val : ℕ) : ZMod (p ^ m)) *
      cmul (smF c (k - 1) (N * p ^ (n + 1)) ζ ((N : ℤ) * (((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 0 0).val : ℤ) + (p : ℤ) ^ (n + 1) * v.1) ((N : ℤ) * (((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 0 1).val : ℤ) + (p : ℤ) ^ (n + 1) * v.2))
      (smF d 1 (N * p ^ (n + 1)) ζ ((N : ℤ) * (((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 1 0).val : ℤ) + (p : ℤ) ^ (n + 1) * v'.1) ((N : ℤ) * (((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 1 1).val : ℤ) + (p : ℤ) ^ (n + 1) * v'.2)) r := by
    refine sum_congr rfl fun γ _ => ?_
    rw [hdet]
    rfl
  rw [hL, hsum]
  have hp' : (p : K) ≠ 0 := by exact_mod_cast hp0.ne'
  have hj : 1 ≤ k - 1 := by omega
  have hstep : ∀ γ ∈ X,
      (∑ y₀₀ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 0 0)), ∑ y₀₁ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 0 1)), ∑ y₁₀ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 1 0)), ∑ y₁₁ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 1 1)),
        cmul (smF c (k - 1) (N * p ^ (n + 1)) ζ ((N : ℤ) * (y₀₀.val : ℤ) + (p : ℤ) ^ (n + 1) * v.1) ((N : ℤ) * (y₀₁.val : ℤ) + (p : ℤ) ^ (n + 1) * v.2))
          (smF d 1 (N * p ^ (n + 1)) ζ ((N : ℤ) * (y₁₀.val : ℤ) + (p : ℤ) ^ (n + 1) * v'.1) ((N : ℤ) * (y₁₁.val : ℤ) + (p : ℤ) ^ (n + 1) * v'.2)) r) =
      ((p : K) ^ ((2 : ℤ) - ((k - 1 : ℕ) : ℤ)) * (p : K) ^ ((2 : ℤ) - ((1 : ℕ) : ℤ))) *
        vp p (cmul (smF c (k - 1) (N * p ^ n) (ζ ^ p) (rowT N p n γ 0 w).1 (rowT N p n γ 0 w).2)
           (smF d 1 (N * p ^ n) (ζ ^ p) (rowT N p n γ 1 w').1 (rowT N p n γ 1 w').2)) r := by
    intro γ hγ
    have hu : ¬ p ∣ ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 0 0).val ∧ ¬ p ∣ ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 1 0).val := by
      exact hX γ hγ
    rw [cauchyProduct_fourfold_finsetSum]
    simp only [GlobalTheory.T.smoothedEisensteinFx_sum_row_lifts_distribution p N n (k - 1) K ζ c ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 0 0) ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 0 1) v.1 v.2 w.1 w.2 hζ hN hpN hn hj hc hu.1 h1 h2,
      GlobalTheory.T.smoothedEisensteinFx_sum_row_lifts_distribution p N n 1 K ζ d ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 1 0) ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 1 1) v'.1 v'.2 w'.1 w'.2 hζ hN hpN hn le_rfl hd hu.2 h3 h4]
    rw [vp_cmul p hp0]
    unfold cmul
    rw [Finset.mul_sum]
    refine sum_congr rfl fun i _ => ?_
    simp only [rowT]
    ring
  rw [Finset.sum_congr rfl (fun γ hγ => by rw [hstep γ hγ])]
  have hsc : -((p : K) ^ (((n + 1 : ℕ) : ℤ) * ((k : ℤ) - 4))) *
      ((p : K) ^ ((2 : ℤ) - ((k - 1 : ℕ) : ℤ)) * (p : K) ^ ((2 : ℤ) - ((1 : ℕ) : ℤ))) =
      -((p : K) ^ ((n : ℤ) * ((k : ℤ) - 4))) := by
    rw [← zpow_add₀ hp', neg_mul, ← zpow_add₀ hp']
    congr 2
    push_cast [Nat.cast_sub (by omega : 1 ≤ k)]
    ring
  rw [← hsc, Finset.mul_sum, Finset.mul_sum]
  refine sum_congr rfl fun γ _ => ?_
  ring
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinPieceUnitSetLevelSuccEqStatement
open GlobalTheory.KummerEisensteinGalois
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisensteinPiece_unitSet_level_succ_eq : ∀ (p : ℕ) [Fact p.Prime] (N n m k : ℕ) (K : Type) [Field K] [CharZero K] (ψ : DirichletCharacter K (p ^ m)) (c d : ℤ) (w w' v v' : ℤ × ℤ) (ζ : K) (X : Finset (GL (Fin 2) (ZMod (p ^ n)))), IsPrimitiveRoot ζ (N * p ^ (n + 1)) → 0 < N → ¬ p ∣ N → 1 ≤ m → m ≤ n → 3 ≤ k → ¬ (p : ℤ) ∣ c → ¬ (p : ℤ) ∣ d → (p : ℤ) * v.1 ≡ w.1 [ZMOD N] → (p : ℤ) * v.2 ≡ w.2 [ZMOD N] → (p : ℤ) * v'.1 ≡ w'.1 [ZMOD N] → (p : ℤ) * v'.2 ≡ w'.2 [ZMOD N] → (∀ γ ∈ X, ¬ p ∣ ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 0 0).val ∧ ¬ p ∣ ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 1 0).val) → ∀ r : ℕ, pieceT N p (n + 1) m k ψ c d v v' ζ (Finset.univ.filter fun γ => Matrix.GeneralLinearGroup.map (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))) γ ∈ X) r = vp p (pieceT N p n m k ψ c d w w' (ζ ^ p) X) r := by
  first | exact @GlobalTheory.KummerEisensteinGalois.pieceT_unitSet_level_succ | exact GlobalTheory.KummerEisensteinGalois.pieceT_unitSet_level_succ | (intros; apply GlobalTheory.KummerEisensteinGalois.pieceT_unitSet_level_succ <;> assumption)
end
end

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

theorem UpperTheory.pieceT_level_raise_eq_vp :
    ∀ {K : Type} [Field K] [CharZero K] (l : ℕ) [Fact l.Prime] (N m k : ℕ) (c d : ℤ) (z₀ : ZMod (l ^ m)), 0 < N → ¬ l ∣ N → 1 ≤ m → 3 ≤ k → ¬ (l : ℤ) ∣ c → ¬ (l : ℤ) ∣ d → ∀ (n : ℕ) (ζ : K) (v v' u u' : ℤ × ℤ), IsPrimitiveRoot ζ (N * l ^ (m + n)) → (l : ℤ) ^ n * v.1 ≡ u.1 [ZMOD N] → (l : ℤ) ^ n * v.2 ≡ u.2 [ZMOD N] → (l : ℤ) ^ n * v'.1 ≡ u'.1 [ZMOD N] → (l : ℤ) ^ n * v'.2 ≡ u'.2 [ZMOD N] → ∀ r : ℕ, pieceT N l (m + n) m k (1 : DirichletCharacter K (l ^ m)) c d v v' ζ ((unitSet l (m + n)).filter fun γ : GL (Fin 2) (ZMod (l ^ (m + n))) => (((γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ (m + n)))).det.val : ℕ) : ZMod (l ^ m)) = z₀) r = vp (l ^ n) (pieceT N l m m k (1 : DirichletCharacter K (l ^ m)) c d u u' (ζ ^ (l ^ n)) ((unitSet l m).filter fun γ : GL (Fin 2) (ZMod (l ^ m)) => (((γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ m))).det.val : ℕ) : ZMod (l ^ m)) = z₀)) r := by
  intro K _ _ l hl N m k c d z₀ hN hlN hm hk hc hd n
  have cop : IsCoprime (l : ℤ) (N : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hl.out).2 hlN)
  induction n with
  | zero =>
    intro ζ v v' u u' hζ h1 h2 h3 h4 r
    simp only [pow_zero, one_mul, pow_one, Nat.add_zero] at *
    have hv : ∀ f : ℕ → K, vp 1 f r = f r := fun f => by simp [vp]
    rw [hv]
    unfold pieceT
    congr 1
    refine Finset.sum_congr rfl fun γ _ => ?_
    congr 1
    have M0 : 0 < N * l ^ m := Nat.mul_pos hN (pow_pos hl.out.pos _)
    have key : ∀ (a : ℤ) {s t : ℤ}, s ≡ t [ZMOD N] → a + (l : ℤ) ^ m * s ≡ a + (l : ℤ) ^ m * t [ZMOD ((N * l ^ m : ℕ) : ℤ)] := by
      intro a s t h
      refine Int.ModEq.add_left _ ?_
      have := h.mul_left' (c := (l : ℤ) ^ m)
      push_cast
      rwa [mul_comm (N : ℤ)]
    congr 1
    · exact UpperTheory.smoothedEisenstein_congr_of_modEq _ _ _ _ M0 hζ.pow_eq_one (key _ h1) (key _ h2)
    · exact UpperTheory.smoothedEisenstein_congr_of_modEq _ _ _ _ M0 hζ.pow_eq_one (key _ h3) (key _ h4)
  | succ n ih =>
    intro ζ v v' u u' hζ h1 h2 h3 h4 r
    have hX := GlobalTheory.T.eisensteinPiece_unitSet_level_succ_eq l N (m + n) m k K (1 : DirichletCharacter K (l ^ m)) c d ((l : ℤ) * v.1, (l : ℤ) * v.2) ((l : ℤ) * v'.1, (l : ℤ) * v'.2) v v' ζ
      ((unitSet l (m + n)).filter fun γ : GL (Fin 2) (ZMod (l ^ (m + n))) => (((γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ (m + n)))).det.val : ℕ) : ZMod (l ^ m)) = z₀)
      hζ hN hlN hm (Nat.le_add_right m n) hk hc hd rfl rfl rfl rfl (fun γ hγ => by
        simpa [unitSet] using (Finset.mem_filter.1 hγ).1) r
    have hζ' : IsPrimitiveRoot (ζ ^ l) (N * l ^ (m + n)) :=
      hζ.pow (Nat.mul_pos hN (pow_pos hl.out.pos _)) (by rw [← Nat.add_assoc, pow_succ]; ring)
    have e : ∀ {s t : ℤ}, (l : ℤ) ^ (n + 1) * s ≡ t [ZMOD N] → (l : ℤ) ^ n * ((l : ℤ) * s) ≡ t [ZMOD N] := fun h => by
      rwa [pow_succ, mul_assoc] at h
    have hI := funext (ih (ζ ^ l) ((l : ℤ) * v.1, (l : ℤ) * v.2) ((l : ℤ) * v'.1, (l : ℤ) * v'.2) u u' hζ' (e h1) (e h2) (e h3) (e h4))
    rw [hI] at hX
    have hval : ∀ (j : ℕ) (hj : l ^ j ∣ l ^ (m + n)) (a : ZMod (l ^ (m + n + 1))),
        (((ZMod.castHom (pow_dvd_pow l (Nat.le_succ (m + n))) (ZMod (l ^ (m + n))) a).val : ℕ) : ZMod (l ^ j)) = ((a.val : ℕ) : ZMod (l ^ j)) := by
      intro j hj a
      rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast, ZMod.natCast_eq_natCast_iff]
      exact (Nat.mod_modEq _ _).of_dvd hj
    have hdv : ∀ a : ZMod (l ^ (m + n + 1)),
        l ∣ (ZMod.castHom (pow_dvd_pow l (Nat.le_succ (m + n))) (ZMod (l ^ (m + n))) a).val ↔ l ∣ a.val := by
      intro a
      rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]
      exact Nat.dvd_mod_iff (dvd_pow_self l (by omega))
    refine Eq.trans ?_ (hX.trans ?_)
    · congr 1
      ext γ
      simp only [unitSet, Finset.mem_filter, Finset.mem_univ, true_and]
      have d1 : ((Matrix.GeneralLinearGroup.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ (m + n))) (ZMod (l ^ (m + n)))) γ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) (ZMod (l ^ (m + n)))) = (ZMod.castHom (pow_dvd_pow l (Nat.le_succ (m + n))) (ZMod (l ^ (m + n)))).mapMatrix (γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ (m + n + 1)))) := rfl
      rw [d1, ← RingHom.map_det, hval m (pow_dvd_pow l (Nat.le_add_right m n))]
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, hdv]
    · rw [← pow_mul, ← pow_succ']
      simp only [vp]
      by_cases h : l ∣ r
      · obtain ⟨r', rfl⟩ := h
        have : l ^ (n + 1) ∣ l * r' ↔ l ^ n ∣ r' := by rw [pow_succ', Nat.mul_dvd_mul_iff_left hl.out.pos]
        rw [if_pos (dvd_mul_right _ _), Nat.mul_div_cancel_left _ hl.out.pos]
        simp only [this]
        rw [pow_succ' l n, Nat.mul_div_mul_left _ _ hl.out.pos]
      · rw [if_neg h, if_neg (fun h' => h ((dvd_pow_self l (Nat.succ_ne_zero n)).trans h'))]
