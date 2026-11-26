module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsTemperedCoeff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuotientCard

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValZpowIff
namespace GlobalTheory.CompanionTheory.CongIndex

open ValuativeRel

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

noncomputable def red (ϖ : k) (c : ℕ) (x : k) :
    IsLocalRing.ResidueField (valuation k).integer := by
  classical
  exact if h : valuation k (x * (ϖ ^ c)⁻¹) ≤ 1 then
    IsLocalRing.residue _ ⟨x * (ϖ ^ c)⁻¹, h⟩ else 0

theorem scaled_le {ϖ : k} (h0 : ϖ ≠ 0) {c : ℕ} {x : k}
    (hx : valuation k x ≤ valuation k (ϖ ^ c)) : valuation k (x * (ϖ ^ c)⁻¹) ≤ 1 := by
  have hp : valuation k (ϖ ^ c) ≠ 0 := by
    simpa using (pow_ne_zero c h0)
  rw [map_mul, map_inv₀]
  exact mul_inv_le_one_of_le₀ hx zero_le'

theorem red_of_le {ϖ : k} (h0 : ϖ ≠ 0) {c : ℕ} {x : k}
    (hx : valuation k x ≤ valuation k (ϖ ^ c)) :
    red ϖ c x = IsLocalRing.residue _ ⟨x * (ϖ ^ c)⁻¹, scaled_le h0 hx⟩ := by
  unfold red
  rw [dite_eq_left (scaled_le h0 hx)]

theorem val_add_le {c : ℕ} {ϖ x y : k}
    (hx : valuation k x ≤ valuation k (ϖ ^ c)) (hy : valuation k y ≤ valuation k (ϖ ^ c)) :
    valuation k (x + y) ≤ valuation k (ϖ ^ c) :=
  (valuation k).map_add_le hx hy

theorem red_add {ϖ : k} (h0 : ϖ ≠ 0) {c : ℕ} {x y : k}
    (hx : valuation k x ≤ valuation k (ϖ ^ c)) (hy : valuation k y ≤ valuation k (ϖ ^ c)) :
    red ϖ c (x + y) = red ϖ c x + red ϖ c y := by
  rw [red_of_le h0 hx, red_of_le h0 hy, red_of_le h0 (val_add_le hx hy), ← map_add (f := _)]
  congr 1
  apply Subtype.ext
  simp [add_mul]

theorem red_eq_zero_iff {ϖ : k} (h0 : ϖ ≠ 0) (h1 : valuation k ϖ < 1)
    (hu : ∀ x : k, valuation k x < 1 → valuation k x ≤ valuation k ϖ) {c : ℕ} {x : k}
    (hx : valuation k x ≤ valuation k (ϖ ^ c)) :
    red ϖ c x = 0 ↔ valuation k x ≤ valuation k (ϖ ^ (c + 1)) := by
  have hp : 0 < valuation k (ϖ ^ c) := by
    rw [zero_lt_iff]; simpa using (pow_ne_zero c h0)
  have key : valuation k x = valuation k (ϖ ^ c) * valuation k (x * (ϖ ^ c)⁻¹) := by
    rw [← map_mul]; congr 1; field_simp
  rw [red_of_le h0 hx, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
    mem_nonunits_iff, Valuation.Integers.isUnit_iff_valuation_eq_one (Valuation.integer.integers _)]
  have hle := scaled_le h0 hx
  constructor
  · intro h
    have hlt : valuation k (x * (ϖ ^ c)⁻¹) < 1 := lt_of_le_of_ne hle h
    rw [key, pow_succ ϖ c, (valuation k).map_mul (ϖ ^ c) ϖ]
    exact mul_le_mul_right (hu _ hlt) _
  · intro h hone
    apply absurd h
    rw [not_le, key]
    have hone' : valuation k (x * (ϖ ^ c)⁻¹) = 1 := hone
    rw [hone', pow_succ ϖ c, (valuation k).map_mul (ϖ ^ c) ϖ, mul_one]
    exact mul_lt_of_lt_one_right hp h1

theorem red_surj {ϖ : k} (h0 : ϖ ≠ 0) (c : ℕ)
    (r : IsLocalRing.ResidueField (valuation k).integer) :
    ∃ x : k, valuation k x ≤ valuation k (ϖ ^ c) ∧ red ϖ c x = r := by
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective r
  have hy : valuation k (y : k) ≤ 1 := y.2
  have hx : valuation k ((y : k) * ϖ ^ c) ≤ valuation k (ϖ ^ c) := by
    rw [map_mul]; exact mul_le_of_le_one_left' hy
  refine ⟨(y : k) * ϖ ^ c, hx, ?_⟩
  rw [red_of_le h0 hx]
  congr 1
  apply Subtype.ext
  have : ϖ ^ c ≠ 0 := pow_ne_zero c h0
  simp [this]

variable {N : ℕ}

def Kset (ϖ : k) (c : Fin N → Fin N → ℕ) : Set (GL (Fin N) k) :=
  {g | ∀ i j, valuation k ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j)
    ≤ valuation k (ϖ ^ c i j)}

theorem pow_le_of_le {ϖ : k} (h1 : valuation k ϖ < 1) {a b : ℕ} (h : a ≤ b) :
    valuation k (ϖ ^ b) ≤ valuation k (ϖ ^ a) := by
  rw [map_pow, map_pow]
  exact pow_le_pow_right_of_le_one' h1.le h

theorem Kset_mono {ϖ : k} (h1 : valuation k ϖ < 1) {c c' : Fin N → Fin N → ℕ}
    (h : ∀ i j, c i j ≤ c' i j) : Kset ϖ c' ⊆ Kset ϖ c :=
  fun _ hg i j => (hg i j).trans (pow_le_of_le h1 (h i j))

theorem entry_le {ϖ : k} {c : Fin N → Fin N → ℕ} {g : GL (Fin N) k} (hg : g ∈ Kset ϖ c)
    {i j : Fin N} (hij : i ≠ j) :
    valuation k ((g : Matrix (Fin N) (Fin N) k) i j) ≤ valuation k (ϖ ^ c i j) := by
  simpa [Matrix.one_apply_ne hij] using hg i j

theorem entry_mul {ϖ : k} (h1 : valuation k ϖ < 1) {c : Fin N → Fin N → ℕ} {i j : Fin N}
    (hij : i ≠ j) (hc : ∀ l, c i j + 1 ≤ c i l + c l j) {g h : GL (Fin N) k}
    (hg : g ∈ Kset ϖ c) (hh : h ∈ Kset ϖ c) :
    ∃ e : k, valuation k e ≤ valuation k (ϖ ^ (c i j + 1)) ∧
      ((g * h : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j =
        (g : Matrix (Fin N) (Fin N) k) i j + (h : Matrix (Fin N) (Fin N) k) i j + e := by
  set A : Matrix (Fin N) (Fin N) k := (g : Matrix (Fin N) (Fin N) k) with hA
  set B : Matrix (Fin N) (Fin N) k := (h : Matrix (Fin N) (Fin N) k) with hB
  refine ⟨((A - 1) * (B - 1)) i j, ?_, ?_⟩
  · rw [Matrix.mul_apply]
    refine (valuation k).map_sum_le fun l _ => ?_
    rw [map_mul]
    have e1 : valuation k ((A - 1) i l) ≤ valuation k (ϖ ^ c i l) := hg i l
    have e2 : valuation k ((B - 1) l j) ≤ valuation k (ϖ ^ c l j) := hh l j
    refine (mul_le_mul' e1 e2).trans ?_
    rw [← map_mul, ← pow_add]
    exact pow_le_of_le h1 (hc l)
  · have : ((g * h : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) = A + B - 1 + (A - 1) * (B - 1) := by
      rw [Units.val_mul]; noncomm_ring
    rw [this]
    simp [Matrix.one_apply_ne hij]

theorem step {ϖ : k} (h0 : ϖ ≠ 0) (h1 : valuation k ϖ < 1)
    (hu : ∀ x : k, valuation k x < 1 → valuation k x ≤ valuation k ϖ)
    {c c' : Fin N → Fin N → ℕ} {i j : Fin N} (hij : i ≠ j)
    (hc : ∀ l, c i j + 1 ≤ c i l + c l j)
    (hc1 : c' i j = c i j + 1) (hc2 : ∀ a b, ¬ (a = i ∧ b = j) → c' a b = c a b)
    (G : Subgroup (GL (Fin N) k)) (hG : (G : Set (GL (Fin N) k)) = Kset ϖ c) :
    ∃ G' : Subgroup (GL (Fin N) k), (G' : Set (GL (Fin N) k)) = Kset ϖ c' ∧ G' ≤ G ∧
      G'.relIndex G = Nat.card (IsLocalRing.ResidueField (valuation k).integer) := by
  have hmem : ∀ g : G, (g : GL (Fin N) k) ∈ Kset ϖ c := fun g => by
    rw [← hG]; exact g.2
  let φ : G →* Multiplicative (IsLocalRing.ResidueField (valuation k).integer) :=
    MonoidHom.mk' (fun g => Multiplicative.ofAdd
      (red ϖ (c i j) (((g : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j))) (by
      intro g h
      obtain ⟨e, he, hgh⟩ := entry_mul h1 hij hc (hmem g) (hmem h)
      have hg := entry_le (hmem g) hij
      have hh := entry_le (hmem h) hij
      have he' : valuation k e ≤ valuation k (ϖ ^ c i j) := he.trans (pow_le_of_le h1 (by omega))
      rw [← ofAdd_add]
      congr 1
      rw [Subgroup.coe_mul, hgh, red_add h0 (val_add_le hg hh) he', red_add h0 hg hh,
        (red_eq_zero_iff h0 h1 hu he').2 he, add_zero])
  have hφ : ∀ g : G, φ g = 1 ↔ valuation k (((g : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j)
      ≤ valuation k (ϖ ^ (c i j + 1)) := fun g => by
    rw [← red_eq_zero_iff h0 h1 hu (entry_le (hmem g) hij)]
    exact ofAdd_eq_one
  have hsurj : Function.Surjective φ := by
    intro r
    obtain ⟨x, hx, hr⟩ := red_surj h0 (c i j) (Multiplicative.toAdd r)
    have hdet : (Matrix.transvection i j x).det ≠ 0 := by
      rw [Matrix.det_transvection_of_ne i j hij x]; exact one_ne_zero
    let t : GL (Fin N) k := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet
    have ht : t ∈ Kset ϖ c := by
      intro a b
      have : (t : Matrix (Fin N) (Fin N) k) a b - (1 : Matrix (Fin N) (Fin N) k) a b
          = Matrix.single i j x a b := by
        show (Matrix.transvection i j x) a b - _ = _
        simp [Matrix.transvection]
      rw [this]
      by_cases hab : a = i ∧ b = j
      · obtain ⟨rfl, rfl⟩ := hab
        simpa using hx
      · have : Matrix.single i j x a b = 0 := by
          rw [Matrix.single_apply, if_neg]
          tauto
        simp [this]
    refine ⟨⟨t, by rw [← SetLike.mem_coe, hG]; exact ht⟩, ?_⟩
    have : (t : Matrix (Fin N) (Fin N) k) i j = x := by
      show (Matrix.transvection i j x) i j = x
      simp [Matrix.transvection, Matrix.one_apply_ne hij]
    show Multiplicative.ofAdd (red ϖ (c i j) ((t : Matrix (Fin N) (Fin N) k) i j)) = r
    rw [this, hr]
    rfl
  refine ⟨φ.ker.map G.subtype, ?_, ?_, ?_⟩
  · ext g
    constructor
    · rintro ⟨g', hg', rfl⟩
      intro a b
      have hk := (hφ g').1 hg'
      by_cases hab : a = i ∧ b = j
      · obtain ⟨rfl, rfl⟩ := hab
        rw [hc1]
        simpa [Matrix.one_apply_ne hij] using hk
      · rw [hc2 a b hab]
        exact hmem g' a b
    · intro hg
      have hgc : g ∈ Kset ϖ c := by
        refine Kset_mono h1 (fun a b => ?_) hg
        by_cases hab : a = i ∧ b = j
        · obtain ⟨rfl, rfl⟩ := hab
          omega
        · rw [hc2 a b hab]
      have hgG : g ∈ G := by rw [← SetLike.mem_coe, hG]; exact hgc
      refine ⟨⟨g, hgG⟩, ?_, rfl⟩
      apply (hφ _).2
      have := hg i j
      rw [hc1] at this
      simpa [Matrix.one_apply_ne hij] using this
  · rintro _ ⟨g', _, rfl⟩
    exact g'.2
  · have hsub : (φ.ker.map G.subtype).subgroupOf G = φ.ker := by
      ext g
      simp [Subgroup.mem_subgroupOf]
    rw [Subgroup.relIndex, hsub, Subgroup.index_ker, MonoidHom.range_eq_top.2 hsurj]
    simp only [Subgroup.card_top]
    exact Nat.card_congr Multiplicative.toAdd

theorem chainS {ϖ : k} (h0 : ϖ ≠ 0) (h1 : valuation k ϖ < 1)
    (hu : ∀ x : k, valuation k x < 1 → valuation k x ≤ valuation k ϖ)
    {m : ℕ} (hm : 1 ≤ m) {b : Fin N → Fin N → ℕ} (hb : ∀ i j l, b i j ≤ b i l + b l j)
    (G : Subgroup (GL (Fin N) k)) (hG : (G : Set (GL (Fin N) k)) = Kset ϖ (fun i j => m + b i j))
    (S : Finset (Fin N × Fin N)) (hS : ∀ p ∈ S, p.1 ≠ p.2) :
    ∃ G' : Subgroup (GL (Fin N) k),
      (G' : Set (GL (Fin N) k)) = Kset ϖ (fun i j => m + b i j + if (i, j) ∈ S then 1 else 0) ∧
      G' ≤ G ∧
      G'.relIndex G = Nat.card (IsLocalRing.ResidueField (valuation k).integer) ^ S.card := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨G, by simpa using hG, le_rfl, by simp⟩
  | insert p S hp ih =>
    obtain ⟨G₁, hG₁, hle, hidx⟩ := ih fun q hq => hS q (Finset.mem_insert_of_mem hq)
    obtain ⟨G₂, hG₂, hle₂, hidx₂⟩ := step (c := fun i j => m + b i j + if (i, j) ∈ S then 1 else 0)
      (c' := fun i j => m + b i j + if (i, j) ∈ insert p S then 1 else 0) h0 h1 hu
      (i := p.1) (j := p.2) (hS _ (Finset.mem_insert_self _ _))
      (fun l => by
        have := hb p.1 p.2 l
        simp only [Prod.mk.eta, hp, if_false]
        split_ifs <;> omega)
      (by simp [hp])
      (fun a c hac => by
        have hne : (a, c) ≠ p := fun h => hac (by simp [← h])
        simp [Finset.mem_insert, hne])
      G₁ hG₁
    refine ⟨G₂, hG₂, hle₂.trans hle, ?_⟩
    rw [← Subgroup.relIndex_mul_relIndex G₂ G₁ G hle₂ hle, hidx₂, hidx, Finset.card_insert_of_notMem hp,
      pow_succ, mul_comm]

theorem chainT {ϖ : k} (h0 : ϖ ≠ 0) (h1 : valuation k ϖ < 1)
    (hu : ∀ x : k, valuation k x < 1 → valuation k x ≤ valuation k ϖ)
    {m : ℕ} (hm : 1 ≤ m) {b : Fin N → Fin N → ℕ} (hb : ∀ i j l, b i j ≤ b i l + b l j)
    (hb0 : ∀ i, b i i = 0)
    (H : Subgroup (GL (Fin N) k)) (hH : (H : Set (GL (Fin N) k)) = Kset ϖ (fun _ _ => m)) (t : ℕ) :
    ∃ G : Subgroup (GL (Fin N) k),
      (G : Set (GL (Fin N) k)) = Kset ϖ (fun i j => m + min (b i j) t) ∧ G ≤ H ∧
      G.relIndex H = Nat.card (IsLocalRing.ResidueField (valuation k).integer) ^
        (∑ i, ∑ j, min (b i j) t) := by
  classical
  induction t with
  | zero => exact ⟨H, by simpa using hH, le_rfl, by simp⟩
  | succ t ih =>
    obtain ⟨G₁, hG₁, hle, hidx⟩ := ih
    obtain ⟨G₂, hG₂, hle₂, hidx₂⟩ := chainS h0 h1 hu hm (b := fun i j => min (b i j) t)
      (fun i j l => by have := hb i j l; omega) G₁ hG₁
      (Finset.univ.filter fun p => t < b p.1 p.2)
      (fun p hp he => by
        have := (Finset.mem_filter.1 hp).2
        rw [he, hb0] at this
        omega)
    refine ⟨G₂, ?_, hle₂.trans hle, ?_⟩
    · rw [hG₂]
      congr 1
      funext i j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      split_ifs <;> omega
    · rw [← Subgroup.relIndex_mul_relIndex G₂ G₁ H hle₂ hle, hidx₂, hidx, ← pow_add]
      congr 1
      rw [Finset.card_filter, Fintype.sum_prod_type, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only
      split_ifs <;> omega

theorem val_zpow_iff {ϖ : k} (h0 : ϖ ≠ 0) (h1 : valuation k ϖ < 1) (m : ℕ) (e : ℤ) (x : k) :
    (valuation k x ≤ valuation k (ϖ ^ m) ∧ valuation k (ϖ ^ e * x) ≤ valuation k (ϖ ^ m)) ↔
      valuation k x ≤ valuation k (ϖ ^ (m + (-e).toNat)) := by
  have hpos : ∀ t : ℕ, 0 < valuation k (ϖ ^ t) := fun t => by
    rw [zero_lt_iff]; simpa using pow_ne_zero t h0
  rcases le_total 0 e with he | he
  · obtain ⟨t, rfl⟩ := Int.eq_ofNat_of_zero_le he
    have : (-(t : ℤ)).toNat = 0 := by omega
    rw [this, add_zero, zpow_natCast]
    refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
    rw [map_mul]
    exact (mul_le_of_le_one_left' (by rw [map_pow]; exact pow_le_one' h1.le t)).trans h
  · obtain ⟨t, ht⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.2 he)
    have he' : e = -(t : ℤ) := by omega
    subst he'
    have : (-(-(t : ℤ))).toNat = t := by omega
    rw [this]
    have hx : x = ϖ ^ t * (ϖ ^ (-(t : ℤ)) * x) := by
      rw [zpow_neg, zpow_natCast]; field_simp
    generalize hy : ϖ ^ (-(t : ℤ)) * x = y at hx ⊢
    clear hy
    subst hx
    rw [(valuation k).map_mul (ϖ ^ t) y, pow_add, (valuation k).map_mul (ϖ ^ m) (ϖ ^ t)]
    constructor
    · rintro ⟨-, h⟩
      rw [mul_comm]
      exact mul_le_mul_left h _
    · intro h
      rw [mul_comm (valuation k (ϖ ^ m))] at h
      have h' : valuation k y ≤ valuation k (ϖ ^ m) := le_of_mul_le_mul_left h (hpos t)
      exact ⟨(mul_le_of_le_one_left' (by rw [map_pow]; exact pow_le_one' h1.le t)).trans h', h'⟩

theorem conj_entry {ϖ : k} (h0 : ϖ ≠ 0) {a : Fin N → ℤ} {D : GL (Fin N) k}
    (hD : (D : Matrix (Fin N) (Fin N) k) = Matrix.diagonal (fun i => ϖ ^ (a i)))
    (g : GL (Fin N) k) (i j : Fin N) :
    ((D⁻¹ * g * D : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j
        - (1 : Matrix (Fin N) (Fin N) k) i j =
      ϖ ^ (a j - a i) * ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) := by
  have hDE : (D : Matrix (Fin N) (Fin N) k) * Matrix.diagonal (fun i => ϖ ^ (-a i)) = 1 := by
    rw [hD, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [zpow_neg]
    exact mul_inv_cancel₀ (zpow_ne_zero _ h0)
  have hinv : ((D⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) =
      Matrix.diagonal (fun i => ϖ ^ (-a i)) := by
    calc ((D⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k)
        = ((D⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) *
            ((D : Matrix (Fin N) (Fin N) k) * Matrix.diagonal (fun i => ϖ ^ (-a i))) := by
          rw [hDE, mul_one]
      _ = _ := by
          rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  rw [Units.val_mul, Units.val_mul, hinv, hD, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.one_apply_eq, sub_self, zpow_zero, one_mul]
    rw [zpow_neg]
    field_simp
  · simp only [Matrix.one_apply_ne hij, sub_zero]
    rw [zpow_sub₀ h0, zpow_neg]
    field_simp

theorem index_main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (ϖ : k) (m : ℕ) (a : Fin N → ℤ), ϖ ≠ 0 →
    ValuativeRel.valuation k (ϖ) < 1 →
    (∀ x : k, ValuativeRel.valuation k (x) < 1 →
      ValuativeRel.valuation k (x) ≤ ValuativeRel.valuation k (ϖ)) → 1 ≤ m → Antitone a →
    ∀ D : GL (Fin N) k, (D : Matrix (Fin N) (Fin N) k) = Matrix.diagonal (fun i => ϖ ^ (a i)) →
    ∀ H : Subgroup (GL (Fin N) k), (H : Set (GL (Fin N) k)) =
      {g : GL (Fin N) k | ∀ i j, ValuativeRel.valuation k ((g : Matrix (Fin N) (Fin N) k) i j -
        (1 : Matrix (Fin N) (Fin N) k) i j) ≤ ValuativeRel.valuation k (ϖ ^ m)} →
    (H.map (MulAut.conj D).toMonoidHom).relIndex H =
      Nat.card (IsLocalRing.ResidueField (ValuativeRel.valuation k).integer) ^
        (∑ i : Fin N, ∑ j : Fin N, if i < j then (a i - a j).toNat else 0) := by
  intro k _ _ _ _ N ϖ m a h0 h1 hu hm ha D hD H hH
  classical
  have hH' : (H : Set (GL (Fin N) k)) = Kset ϖ (fun _ _ => m) := hH
  set b : Fin N → Fin N → ℕ := fun i j => (a i - a j).toNat with hbdef
  obtain ⟨T, hT⟩ : ∃ T, ∀ i j, b i j ≤ T :=
    ⟨∑ i, ∑ j, b i j, fun i j =>
      (Finset.single_le_sum (f := fun j => b i j) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, b i j) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i))⟩
  obtain ⟨G, hG, -, hidx⟩ := chainT h0 h1 hu hm (b := b)
    (fun i j l => by simp only [hbdef]; omega) (fun i => by simp [hbdef]) H hH' T
  have hmin : ∀ i j, min (b i j) T = b i j := fun i j => min_eq_left (hT i j)
  simp only [hmin] at hG hidx
  have hGeq : G = H.map (MulAut.conj D).toMonoidHom ⊓ H := by
    apply SetLike.coe_injective
    rw [hG]
    ext g
    have hmap : g ∈ H.map (MulAut.conj D).toMonoidHom ↔ D⁻¹ * g * D ∈ H := by
      rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    have hmemH : ∀ x, x ∈ H ↔ x ∈ Kset ϖ (fun _ _ => m) := fun x => by
      rw [← hH']; rfl
    rw [SetLike.mem_coe, Subgroup.mem_inf, hmap, hmemH, hmemH]
    simp only [Kset, Set.mem_setOf_eq, conj_entry h0 hD]
    constructor
    · intro h
      refine ⟨fun i j => ?_, fun i j => ?_⟩
      · have := (val_zpow_iff h0 h1 m (a j - a i) _).2 (by simpa [hbdef] using h i j)
        exact this.2
      · have := (val_zpow_iff h0 h1 m (a j - a i) _).2 (by simpa [hbdef] using h i j)
        exact this.1
    · rintro ⟨h2, h3⟩ i j
      have := (val_zpow_iff h0 h1 m (a j - a i) _).1 ⟨h3 i j, h2 i j⟩
      simpa [hbdef] using this
  rw [← Subgroup.inf_relIndex_right, ← hGeq, hidx]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs with hij
  · rfl
  · have : a i ≤ a j := ha (not_lt.1 hij)
    simp only [hbdef]
    omega

end GlobalTheory.CompanionTheory.CongIndex
end

open MeasureTheory GlobalTheory.LocGL

namespace GlobalTheory.CompanionTheory.DoubleCosetVolume

theorem measure_doubleCoset {Q : Type*} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    [MeasurableSpace Q] [BorelSpace Q] (μ : Measure Q) [μ.IsMulLeftInvariant] (B : Subgroup Q)
    (hB : IsOpen (B : Set Q)) (s : Q)
    (hfin : (B.map (MulAut.conj s).toMonoidHom).relIndex B ≠ 0) :
    μ {q : Q | ∃ x ∈ B, ∃ y ∈ B, q = x * s * y} =
      ((B.map (MulAut.conj s).toMonoidHom).relIndex B : ENNReal) * μ (B : Set Q) := by
  classical
  set C : Subgroup B := (B.map (MulAut.conj s).toMonoidHom).subgroupOf B with hC
  have hidx : C.index ≠ 0 := hfin
  have : C.FiniteIndex := ⟨hidx⟩
  have : Finite (B ⧸ C) := inferInstance
  letI : Fintype (B ⧸ C) := Fintype.ofFinite _
  have hmemC : ∀ w : B, w ∈ C ↔ ∃ b ∈ B, s * b * s⁻¹ = (w : Q) := by
    intro w
    rw [hC, Subgroup.mem_subgroupOf, Subgroup.mem_map]
    simp [MulAut.conj_apply]
  let r : B ⧸ C → Q := fun c => ((Quotient.out c : B) : Q) * s
  let T : B ⧸ C → Set Q := fun c => (fun h => (r c)⁻¹ * h) ⁻¹' (B : Set Q)
  have hcover : {q : Q | ∃ x ∈ B, ∃ y ∈ B, q = x * s * y} = ⋃ c, T c := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨x, hx, y, hy, rfl⟩
      refine ⟨QuotientGroup.mk (⟨x, hx⟩ : B), ?_⟩
      have h1 : (QuotientGroup.mk (Quotient.out (QuotientGroup.mk (⟨x, hx⟩ : B) : B ⧸ C)) : B ⧸ C) =
          QuotientGroup.mk (⟨x, hx⟩ : B) := QuotientGroup.out_eq' _
      obtain ⟨b, hb, hbw⟩ := (hmemC _).1 (QuotientGroup.eq.1 h1)
      have h2 : ((Quotient.out (QuotientGroup.mk (⟨x, hx⟩ : B) : B ⧸ C) : B) : Q)⁻¹ * x =
          s * b * s⁻¹ := by
        rw [hbw]; simp
      show (r _)⁻¹ * (x * s * y) ∈ B
      have h3 : (r (QuotientGroup.mk (⟨x, hx⟩ : B)))⁻¹ * (x * s * y) = b * y := by
        show (((Quotient.out (QuotientGroup.mk (⟨x, hx⟩ : B) : B ⧸ C) : B) : Q) * s)⁻¹ *
          (x * s * y) = b * y
        rw [mul_inv_rev, mul_assoc s⁻¹, ← mul_assoc _ (x * s) y, ← mul_assoc _ x s, h2]
        group
      rw [h3]
      exact B.mul_mem hb hy
    · rintro ⟨c, hc⟩
      refine ⟨_, (Quotient.out c : B).2, _, hc, ?_⟩
      show q = r c * ((r c)⁻¹ * q)
      group
  have hdisj : Pairwise (Function.onFun Disjoint T) := by
    intro c c' hcc
    refine Set.disjoint_left.2 fun q hq hq' => hcc ?_
    have hq1 : (r c)⁻¹ * q ∈ B := hq
    have hq2 : (r c')⁻¹ * q ∈ B := hq'
    have hw : (Quotient.out c : B)⁻¹ * (Quotient.out c' : B) ∈ C := by
      refine (hmemC _).2 ⟨((r c)⁻¹ * q) * ((r c')⁻¹ * q)⁻¹, B.mul_mem hq1 (B.inv_mem hq2), ?_⟩
      show _ = ((Quotient.out c : B) : Q)⁻¹ * ((Quotient.out c' : B) : Q)
      show s * (((((Quotient.out c : B) : Q) * s)⁻¹ * q) *
        (((((Quotient.out c' : B) : Q) * s)⁻¹ * q))⁻¹) * s⁻¹ = _
      group
    have := QuotientGroup.eq.2 hw
    rw [QuotientGroup.out_eq', QuotientGroup.out_eq'] at this
    exact this
  have hopen : ∀ c, MeasurableSet (T c) := fun c =>
    (hB.preimage (continuous_const.mul continuous_id)).measurableSet
  have hT : ∀ c, μ (T c) = μ (B : Set Q) := fun c => measure_preimage_mul μ _ _
  rw [hcover, measure_iUnion hdisj hopen]
  simp only [hT, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 2
  show _ = C.index
  rw [Subgroup.index, Nat.card_eq_fintype_card]

theorem relIndex_map_mk {G : Type*} [Group G] (Z : Subgroup G) [Z.Normal] (H : Subgroup G) (t : G)
    (hZ : ∀ g ∈ H, ∀ h ∈ H, (t * h * t⁻¹)⁻¹ * g ∈ Z → ∃ h₂ ∈ H, t * h₂ * t⁻¹ = g) :
    ((H.map (QuotientGroup.mk' Z)).map (MulAut.conj (QuotientGroup.mk' Z t)).toMonoidHom).relIndex
        (H.map (QuotientGroup.mk' Z)) =
      (H.map (MulAut.conj t).toMonoidHom).relIndex H := by
  rw [← Subgroup.relIndex_comap, ← Subgroup.inf_relIndex_right,
    ← Subgroup.inf_relIndex_right (H.map (MulAut.conj t).toMonoidHom)]
  congr 1
  ext g
  simp only [Subgroup.mem_inf, Subgroup.mem_comap, Subgroup.mem_map]
  refine and_congr_left fun hg => ?_
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, exists_exists_and_eq_and]
  constructor
  · rintro ⟨h, hh, he⟩
    have h1 : (QuotientGroup.mk' Z) (t * h * t⁻¹) = (QuotientGroup.mk' Z) g := by
      simpa using he
    exact hZ g hg h hh (QuotientGroup.eq.1 h1)
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h, hh, by simp⟩

theorem toNat_natCast_mul (j : ℕ) (x : ℤ) : ((j : ℤ) * x).toNat = j * x.toNat := by
  rcases le_total 0 x with h | h
  · lift x to ℕ using h
    rw [← Nat.cast_mul, Int.toNat_natCast, Int.toNat_natCast]
  · have h1 : (j : ℤ) * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) h
    rw [Int.toNat_of_nonpos h1, Int.toNat_of_nonpos h, mul_zero]

end GlobalTheory.CompanionTheory.DoubleCosetVolume

namespace GlobalTheory.CompanionTheory.DoubleCosetVolume

open ValuativeRel

variable {k : Type} [Field k] [ValuativeRel k]

theorem central_mem_cong {N : ℕ} {r : ValueGroupWithZero k} (hr : r < 1)
    (t : GL (Fin N) k) (d : Fin N → k) (hd : ∀ i, d i ≠ 0)
    (ht : (t : Matrix (Fin N) (Fin N) k) = Matrix.diagonal d)
    (g h z : GL (Fin N) k)
    (hg : ∀ i j, valuation k ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ r)
    (hh : ∀ i j, valuation k ((h : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ r)
    (hz : z ∈ Subgroup.center (GL (Fin N) k)) (hgz : g = t * h * t⁻¹ * z) :
    ∀ i j, valuation k ((z : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ r := by
  obtain ⟨c, hc⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.1 hz
  have hzv : (z : Matrix (Fin N) (Fin N) k) = Matrix.scalar (Fin N) c := hc.symm
  have htinv : ((t⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) = Matrix.diagonal fun i => (d i)⁻¹ := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [ht, Matrix.diagonal_mul_diagonal]
    simp [hd, Matrix.diagonal_one]
  intro i j
  by_cases hij : i = j
  · subst hij
    have h1 : (g : Matrix (Fin N) (Fin N) k) i i = (h : Matrix (Fin N) (Fin N) k) i i * c := by
      rw [hgz]
      simp only [Units.val_mul, hzv, htinv, ht, Matrix.scalar_apply, Matrix.mul_diagonal,
        Matrix.diagonal_mul]
      field_simp [hd i]
    have h2 : valuation k ((h : Matrix (Fin N) (Fin N) k) i i) = 1 := by
      have h3 := hh i i
      rw [Matrix.one_apply_eq] at h3
      have h4 := Valuation.map_one_add_of_lt (valuation k) (h3.trans_lt hr)
      rwa [add_sub_cancel] at h4
    have h5 := hg i i
    have h6 := hh i i
    rw [Matrix.one_apply_eq] at h5 h6 ⊢
    have h7 : (h : Matrix (Fin N) (Fin N) k) i i * (c - 1) =
        ((g : Matrix (Fin N) (Fin N) k) i i - 1) - ((h : Matrix (Fin N) (Fin N) k) i i - 1) := by
      rw [h1]; ring
    have h8 : valuation k (c - 1) ≤ r := by
      have h9 := Valuation.map_sub (valuation k) ((g : Matrix (Fin N) (Fin N) k) i i - 1)
        ((h : Matrix (Fin N) (Fin N) k) i i - 1)
      rw [← h7, map_mul, h2, one_mul] at h9
      exact h9.trans (max_le h5 h6)
    rw [hzv]
    simpa using h8
  · rw [hzv, Matrix.one_apply_ne hij]
    simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij]

end GlobalTheory.CompanionTheory.DoubleCosetVolume

namespace GlobalTheory.CompanionTheory.DoubleCosetVolume

open ValuativeRel

theorem measure_image_doubleCoset : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (ϖ : k) (m : ℕ) (a : Fin N → ℤ), ϖ ≠ 0 → ValuativeRel.valuation k (ϖ) < 1 → (∀ x : k, ValuativeRel.valuation k (x) < 1 → ValuativeRel.valuation k (x) ≤ ValuativeRel.valuation k (ϖ)) → 1 ≤ m → Antitone a → ∀ D : GL (Fin N) k, (D : Matrix (Fin N) (Fin N) k) = Matrix.diagonal (fun i => ϖ ^ (a i)) → ∀ [MeasurableSpace (AdGL k N)] [BorelSpace (AdGL k N)] (μ : MeasureTheory.Measure (AdGL k N)), μ.IsHaarMeasure → ∀ j : ℕ, μ ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' {g : GL (Fin N) k | ∃ x ∈ {g : GL (Fin N) k | ∀ i j, ValuativeRel.valuation k ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ ValuativeRel.valuation k (ϖ ^ m)}, ∃ y ∈ {g : GL (Fin N) k | ∀ i j, ValuativeRel.valuation k ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ ValuativeRel.valuation k (ϖ ^ m)}, g = x * D ^ j * y}) = ((Nat.card (IsLocalRing.ResidueField (ValuativeRel.valuation k).integer) : ENNReal) ^ (j * (∑ i : Fin N, ∑ j : Fin N, if i < j then (a i - a j).toNat else 0))) * μ ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' {g : GL (Fin N) k | ∀ i j, ValuativeRel.valuation k ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ ValuativeRel.valuation k (ϖ ^ m)}) := by
  intro k _ _ _ _ N ϖ m a hϖ0 hϖ1 hunif hm ha D hD _ _ μ hμ j
  have hϖm0 : ϖ ^ m ≠ 0 := pow_ne_zero _ hϖ0
  have hr : valuation k (ϖ ^ m) < 1 := by
    rw [map_pow]
    exact pow_lt_one₀ zero_le hϖ1 (by omega)
  obtain ⟨H, hH⟩ := GlobalTheory.CompanionTheory.PrincipalCongruence.exists_principalCongruence k N (ϖ ^ m) hϖm0 hr
  have hopen : IsOpen (H : Set (GL (Fin N) k)) := by
    rw [hH]
    exact (GlobalTheory.CompanionTheory.PrincipalCongruence.isOpen_isCompact_principal k N (ϖ ^ m) hϖm0 hr).1
  have hmem : ∀ g : GL (Fin N) k, g ∈ H ↔ ∀ i j, valuation k
      ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ valuation k (ϖ ^ m) := by
    intro g
    rw [← SetLike.mem_coe, hH]
    rfl
  rw [← hH]
  set t : GL (Fin N) k := D ^ j with ht
  have hDj : (t : Matrix (Fin N) (Fin N) k) = Matrix.diagonal (fun i => ϖ ^ ((j : ℤ) * a i)) := by
    rw [ht, Units.val_pow_eq_pow_val, hD, Matrix.diagonal_pow]
    congr 1
    funext i
    simp only [Pi.pow_apply]
    rw [← zpow_natCast, ← zpow_mul, mul_comm]
  have hanti : Antitone fun i => (j : ℤ) * a i := fun x y hxy =>
    mul_le_mul_of_nonneg_left (ha hxy) (by positivity)
  have hindex := GlobalTheory.CompanionTheory.CongIndex.index_main k N ϖ m (fun i => (j : ℤ) * a i) hϖ0 hϖ1 hunif hm hanti t hDj H hH
  have hsum : (∑ i : Fin N, ∑ l : Fin N, if i < l then ((j : ℤ) * a i - (j : ℤ) * a l).toNat else 0) =
      j * ∑ i : Fin N, ∑ l : Fin N, if i < l then (a i - a l).toNat else 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs
    · rw [← mul_sub, toNat_natCast_mul]
    · simp
  simp only [hsum] at hindex
  have hq : 0 < Nat.card (IsLocalRing.ResidueField (valuation k).integer) := Nat.card_pos
  set Z : Subgroup (GL (Fin N) k) := Subgroup.center (GL (Fin N) k) with hZdef
  have hmerge : ∀ g ∈ H, ∀ h ∈ H, (t * h * t⁻¹)⁻¹ * g ∈ Z → ∃ h₂ ∈ H, t * h₂ * t⁻¹ = g := by
    intro g hg h hh hz
    have hzH : (t * h * t⁻¹)⁻¹ * g ∈ H := (hmem _).2 (central_mem_cong hr t _
      (fun i => zpow_ne_zero _ hϖ0) hDj g h _ ((hmem g).1 hg) ((hmem h).1 hh) hz (by group))
    refine ⟨h * ((t * h * t⁻¹)⁻¹ * g), H.mul_mem hh hzH, ?_⟩
    have hc := Subgroup.mem_center_iff.1 hz t⁻¹
    calc t * (h * ((t * h * t⁻¹)⁻¹ * g)) * t⁻¹
        = t * h * (((t * h * t⁻¹)⁻¹ * g) * t⁻¹) := by group
      _ = t * h * (t⁻¹ * ((t * h * t⁻¹)⁻¹ * g)) := by rw [hc]
      _ = g := by group
  have hI := relIndex_map_mk Z H t hmerge
  set B : Subgroup (AdGL k N) := H.map (QuotientGroup.mk' Z) with hB
  set s : AdGL k N := QuotientGroup.mk' Z t with hs
  have hBopen : IsOpen (B : Set (AdGL k N)) := by
    have := QuotientGroup.isOpenMap_coe (N := Z) _ hopen
    simpa [hB, Subgroup.coe_map] using this
  have hBcoe : (QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' (H : Set (GL (Fin N) k)) = (B : Set (AdGL k N)) := by
    rw [hB, Subgroup.coe_map]; rfl
  have hdc : (QuotientGroup.mk : GL (Fin N) k → AdGL k N) ''
      {g : GL (Fin N) k | ∃ x ∈ (H : Set (GL (Fin N) k)), ∃ y ∈ (H : Set (GL (Fin N) k)), g = x * t * y} =
      {q : AdGL k N | ∃ x ∈ B, ∃ y ∈ B, q = x * s * y} := by
    ext q
    constructor
    · rintro ⟨_, ⟨x, hx, y, hy, rfl⟩, rfl⟩
      exact ⟨_, Subgroup.mem_map_of_mem _ hx, _, Subgroup.mem_map_of_mem _ hy, rfl⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨x * t * y, ⟨x, hx, y, hy, rfl⟩, rfl⟩
  rw [hBcoe, hdc, measure_doubleCoset μ B hBopen s (by rw [hI, hindex]; positivity), hI, hindex]
  push_cast
  rfl

end GlobalTheory.CompanionTheory.DoubleCosetVolume
