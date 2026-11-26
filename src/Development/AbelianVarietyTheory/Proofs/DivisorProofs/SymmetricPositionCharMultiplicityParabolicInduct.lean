module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankMirabolicWhittakerEigenspace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviWhittakerEqOneOfCuspidal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerateWhittakerDimParabolicInductionCuspidal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricPositionCharMultiplicityEqSumDegenerate
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricPositionCharMultiplicityEqSumDegenerate
noncomputable section

namespace GlobalTheory.FinGL.PosOne

open GlobalTheory.FinGL Formalism.L2.DIV Module Matrix

theorem mem_eig {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ G V) (S : Set G) (χ : G → ℂ)
    (v : V) : v ∈ eig τ S χ ↔ ∀ g ∈ S, τ g v = χ g • v := by
  simp [eig, Submodule.mem_iInf, sub_eq_zero]

theorem exists_descent {G P V : Type} [Group G] [Group P] [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ G V)
    (Q : Subgroup G) (ρ : Q →* P) (hρ : Function.Surjective ρ) (χ : Q →* ℂˣ) :
    ∃ (M : Submodule ℂ V) (π : Representation ℂ P M), ∀ (S : Set P) (c : P → ℂ) (T : Set G) (d : G → ℂ),
      (1 : P) ∈ S → c 1 = 1 → (∀ g, g ∈ T ↔ ∃ h : g ∈ Q, ρ ⟨g, h⟩ ∈ S) →
      (∀ g : Q, ρ g ∈ S → d g = χ g * c (ρ g)) → finrank ℂ (eig π S c) = finrank ℂ (eig τ T d) := by
  let σ : Representation ℂ Q V :=
    { toFun := fun g => (((χ g)⁻¹ : ℂˣ) : ℂ) • τ g
      map_one' := by simp
      map_mul' := fun x y => by
        simp only [map_mul, Subgroup.coe_mul, mul_inv, Units.val_mul, smul_mul_smul_comm] }
  have hσ : ∀ (g : Q) (v : V), σ g v = (((χ g)⁻¹ : ℂˣ) : ℂ) • τ g v := fun g v => rfl
  let M : Submodule ℂ V := eig σ (ρ.ker : Set Q) fun _ => 1
  have hM : ∀ v, v ∈ M ↔ ∀ g : Q, ρ g = 1 → σ g v = v := fun v => by
    simp [M, mem_eig]
  have hst : ∀ g : Q, ∀ v ∈ M, σ g v ∈ M := by
    intro g v hv
    rw [hM] at hv ⊢
    intro n hn
    have h1 := hv (g⁻¹ * n * g) (by simp [hn])
    have h2 : n * g = g * (g⁻¹ * n * g) := by group
    calc σ n (σ g v) = σ (n * g) v := by rw [map_mul]; rfl
      _ = σ g (σ (g⁻¹ * n * g) v) := by rw [h2, map_mul]; rfl
      _ = σ g v := by rw [h1]
  let σM : Q →* Module.End ℂ M :=
    { toFun := fun g => (σ g).restrict (hst g)
      map_one' := by ext v; simp
      map_mul' := fun x y => by ext v; simp }
  have hσM : ∀ (g : Q) (v : M), (σM g v : V) = σ g v := fun g v => rfl
  have hker : ∀ x y : Q, ρ x = ρ y → σM x = σM y := by
    intro x y h
    ext v
    have h1 := (hM v.1).1 v.2 (y⁻¹ * x) (by simp [h])
    have h2 : x = y * (y⁻¹ * x) := by group
    rw [hσM, hσM]
    conv_lhs => rw [h2, map_mul]
    show σ y (σ (y⁻¹ * x) v) = _
    rw [h1]
  obtain ⟨s, hs⟩ := hρ.hasRightInverse
  let π : Representation ℂ P M :=
    { toFun := fun p => σM (s p)
      map_one' := by rw [hker (s 1) 1 (by rw [hs 1, map_one]), map_one]
      map_mul' := fun x y => by
        rw [← map_mul]; exact hker _ _ (by rw [map_mul, hs x, hs y, hs (x * y)]) }
  have hπ : ∀ (g : Q) (v : M), (π (ρ g) v : V) = σ g v := fun g v => by
    show (σM (s (ρ g)) v : V) = _
    rw [hker (s (ρ g)) g (hs _), hσM]
  refine ⟨M, π, fun S c T d h1 hc hT hd => ?_⟩
  have key : ∀ (g : Q) (v : V), ρ g ∈ S → (σ g v = c (ρ g) • v ↔ τ g v = d g • v) := by
    intro g v hg
    rw [hσ, hd g hg, mul_smul]
    constructor
    · intro h; rw [← h, smul_smul]; simp
    · intro h; rw [h, smul_smul]; simp
  have e : (eig π S c).map M.subtype = eig τ T d := by
    ext v
    simp only [Submodule.mem_map, mem_eig]
    constructor
    · rintro ⟨w, hw, rfl⟩ g hg
      obtain ⟨h, hh⟩ := (hT g).1 hg
      refine (key ⟨g, h⟩ _ hh).1 ?_
      have := congrArg Subtype.val (hw _ hh)
      rw [hπ] at this
      exact this
    · intro hv
      have hv' : ∀ g : Q, ρ g ∈ S → σ g v = c (ρ g) • v := fun g hg =>
        (key g v hg).2 (hv g ((hT g).2 ⟨g.2, hg⟩))
      refine ⟨⟨v, (hM v).2 fun g hg => ?_⟩, fun p hp => ?_, rfl⟩
      · rw [hv' g (by rw [hg]; exact h1), hg, hc, one_smul]
      · obtain ⟨g, rfl⟩ := hρ p
        apply Subtype.ext
        rw [hπ]
        exact hv' g hp
  rw [← e]
  exact (Submodule.finrank_map_subtype_eq M _).symm

variable {F : Type} [Field F] {r : ℕ}

def tailOnesBlockSizes (k : ℕ) (a : Fin r) : ℕ := if a.val < k then 0 else a.val + 1

def tailUnip (F : Type) [Field F] (r k : ℕ) : Subgroup (GL (Fin r) F) where
  carrier := {g | g ∈ blockTri (κ := F) (tailOnesBlockSizes k) ∧ ∀ i : Fin r, k ≤ i.val → (g : Matrix (Fin r) (Fin r) F) i i = 1}
  one_mem' := ⟨Subgroup.one_mem _, fun i _ => by simp⟩
  mul_mem' := by
    rintro x y ⟨hx, hx1⟩ ⟨hy, hy1⟩
    refine ⟨Subgroup.mul_mem _ hx hy, fun i hi => ?_⟩
    rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single i, hx1 i hi, hy1 i hi, one_mul]
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with h | h
      · have h' : l.val < i.val := h
        rw [hx (show tailOnesBlockSizes k l < tailOnesBlockSizes k i by unfold tailOnesBlockSizes; split_ifs <;> omega), zero_mul]
      · have h' : i.val < l.val := h
        rw [hy (show tailOnesBlockSizes k i < tailOnesBlockSizes k l by unfold tailOnesBlockSizes; split_ifs <;> omega), mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  inv_mem' := by
    rintro x ⟨hx, hx1⟩
    have hi := Subgroup.inv_mem _ hx
    refine ⟨hi, fun i hk => ?_⟩
    have h1 : ((x * x⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i i = 1 := by simp
    rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single i, hx1 i hk, one_mul] at h1
    · exact h1
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with h | h
      · have h' : l.val < i.val := h
        rw [hx (show tailOnesBlockSizes k l < tailOnesBlockSizes k i by unfold tailOnesBlockSizes; split_ifs <;> omega), zero_mul]
      · have h' : i.val < l.val := h
        rw [hi (show tailOnesBlockSizes k i < tailOnesBlockSizes k l by unfold tailOnesBlockSizes; split_ifs <;> omega), mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h

theorem mem_tailUnip {k : ℕ} {g : GL (Fin r) F} : g ∈ tailUnip F r k ↔
    ∀ i j : Fin r, k ≤ i.val → j.val ≤ i.val →
      (g : Matrix (Fin r) (Fin r) F) i j = (1 : Matrix (Fin r) (Fin r) F) i j := by
  constructor
  · rintro ⟨h1, h2⟩ i j hi hj
    rcases hj.lt_or_eq with h | h
    · rw [h1 (show tailOnesBlockSizes k j < tailOnesBlockSizes k i by unfold tailOnesBlockSizes; split_ifs <;> omega),
        one_apply_ne (fun e => by rw [e] at h; omega)]
    · obtain rfl : j = i := Fin.ext h
      rw [h2 j hi, one_apply_eq]
  · intro h
    refine ⟨fun i j hij => ?_, fun i hi => by rw [h i i hi le_rfl, one_apply_eq]⟩
    have : k ≤ i.val ∧ j.val < i.val := by
      unfold tailOnesBlockSizes at hij; split_ifs at hij <;> omega
    rw [h i j this.1 this.2.le, one_apply_ne (fun e => by rw [e] at this; omega)]

theorem mem_unip {g : GL (Fin r) F} : g ∈ unip F r ↔
    ∀ i j : Fin r, j.val ≤ i.val → (g : Matrix (Fin r) (Fin r) F) i j = (1 : Matrix (Fin r) (Fin r) F) i j := by
  constructor
  · intro hg i j hj
    rcases hj.lt_or_eq with h | h
    · rw [unip_lower hg (show j < i from h), one_apply_ne (fun e => by rw [e] at h; omega)]
    · obtain rfl : j = i := Fin.ext h
      rw [unip_diag hg, one_apply_eq]
  · intro h
    refine ⟨fun i j hij => ?_, fun i => by rw [h i i le_rfl, one_apply_eq]⟩
    have hij' : j.val < i.val := hij
    rw [h i j hij'.le, one_apply_ne (fun e => by rw [e] at hij'; omega)]

theorem mem_tailUnip_last {k : ℕ} (g : GL (Fin (k + 1)) F) : g ∈ tailUnip F (k + 1) k ↔
    ∀ j, (g : Matrix (Fin (k + 1)) (Fin (k + 1)) F) (Fin.last k) j =
      (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) F) (Fin.last k) j := by
  rw [mem_tailUnip]
  constructor
  · intro h j
    exact h _ j (by simp) (by have := j.2; simp only [Fin.val_last]; omega)
  · intro h i j hi _
    obtain rfl : i = Fin.last k := Fin.ext (by have := i.2; simp only [Fin.val_last]; omega)
    exact h j

theorem tailUnip_le (k : ℕ) : tailUnip F r k ≤ blockTri (blk2 (k + 1)) := by
  intro g hg i j hij
  have : k + 1 ≤ i.val ∧ j.val < k + 1 := by
    unfold blk2 at hij; split_ifs at hij <;> omega
  rw [mem_tailUnip.1 hg i j (by omega) (by omega), one_apply_ne (fun e => by rw [e] at this; omega)]

theorem one_castLE {n : ℕ} (h : n ≤ r) (i j : Fin n) :
    (1 : Matrix (Fin r) (Fin r) F) (Fin.castLE h i) (Fin.castLE h j) = (1 : Matrix (Fin n) (Fin n) F) i j := by
  simp [Matrix.one_apply]

def corner {k : ℕ} (h : k + 1 ≤ r) : tailUnip F r k →* tailUnip F (k + 1) k :=
  ((blkR h).comp (Subgroup.inclusion (tailUnip_le k))).codRestrict _ fun g =>
    mem_tailUnip.2 fun i j hi hj => by
      rw [← one_castLE h]
      exact mem_tailUnip.1 g.2 (Fin.castLE h i) (Fin.castLE h j) hi hj

theorem corner_apply {k : ℕ} (h : k + 1 ≤ r) (g : tailUnip F r k) (i j : Fin (k + 1)) :
    ((corner h g : GL (Fin (k + 1)) F) : Matrix (Fin (k + 1)) (Fin (k + 1)) F) i j =
      ((g : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) (Fin.castLE h i) (Fin.castLE h j) := rfl

theorem corner_surj {k : ℕ} (h : k + 1 ≤ r) : Function.Surjective (corner (F := F) h) := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
  intro p
  let e : Fin (k + 1) ⊕ Fin c ≃ Fin (k + 1 + c) := finSumFinEquiv
  let f : GL (Fin (k + 1)) F → Matrix (Fin (k + 1 + c)) (Fin (k + 1 + c)) F := fun x =>
    (fromBlocks (x : Matrix (Fin (k + 1)) (Fin (k + 1)) F) 0 0 (1 : Matrix (Fin c) (Fin c) F)).submatrix e.symm e.symm
  have hf : ∀ x y, x * y = 1 → f x * f y = 1 := fun x y hxy => by
    simp only [f, submatrix_mul_equiv, fromBlocks_multiply, ← Units.val_mul, hxy]
    simp
  let g : GL (Fin (k + 1 + c)) F := ⟨f p, f p⁻¹, hf _ _ (by simp), hf _ _ (by simp)⟩
  have hg : ∀ a b, (g : Matrix _ _ F) (e a) (e b) =
      fromBlocks ((p : GL (Fin (k + 1)) F) : Matrix (Fin (k + 1)) (Fin (k + 1)) F) 0 0 (1 : Matrix (Fin c) (Fin c) F) a b :=
    fun a b => by simp [g, f]
  have h1 : ∀ a b, (1 : Matrix _ _ F) (e a) (e b) =
      fromBlocks (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) F) 0 0 (1 : Matrix (Fin c) (Fin c) F) a b :=
    fun a b => by rw [fromBlocks_one]; simp [Matrix.one_apply]
  refine ⟨⟨g, mem_tailUnip.2 fun i j hi hj => ?_⟩, ?_⟩
  · obtain ⟨a, rfl⟩ := e.surjective i
    obtain ⟨b, rfl⟩ := e.surjective j
    rw [hg, h1]
    rcases a with a | a <;> rcases b with b | b
    · exact mem_tailUnip.1 p.2 a b hi hj
    all_goals rfl
  · apply Subtype.ext
    apply Units.ext
    ext i j
    rw [corner_apply]
    exact hg (Sum.inl i) (Sum.inl j)

def tailEdge (k : ℕ) (a b : Fin r) : Prop := b.val = a.val + 1 ∧ k ≤ a.val

instance (k : ℕ) : DecidableRel (tailEdge (r := r) k) := fun a b =>
  inferInstanceAs (Decidable (b.val = a.val + 1 ∧ k ≤ a.val))

def tailHom (F : Type) [Field F] (r k : ℕ) : tailUnip F r k →* Multiplicative F :=
  edgeHom (tailEdge k) (tailUnip F r k) (fun i j h e => by unfold tailEdge at h; rw [e] at h; omega)
    (fun x hx y hy i j h => by
      obtain ⟨h1, h2⟩ := h
      have hij : i ≠ j := fun e => by rw [e] at h1; omega
      rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_add i j hij, hx.2 i h2, hy.2 j (by omega),
        one_mul, mul_one, add_comm]
      · rintro l _ ⟨hli, hlj⟩
        have a1 : l.val ≠ i.val := fun e => hli (Fin.ext e)
        have a2 : l.val ≠ j.val := fun e => hlj (Fin.ext e)
        rcases lt_or_gt_of_ne a1 with h | h
        · rw [mem_tailUnip.1 hx i l h2 h.le, one_apply_ne (Ne.symm hli), zero_mul]
        · rw [mem_tailUnip.1 hy l j (by omega) (by omega), one_apply_ne hlj, mul_zero]
      · intro h; exact absurd (Finset.mem_univ i) h
      · intro h; exact absurd (Finset.mem_univ j) h)

theorem edgeSum_split {k : ℕ} (h : k + 1 ≤ r) (g : tailUnip F r k) (E : Fin r → Fin r → Prop) [DecidableRel E]
    (E' : Fin (k + 1) → Fin (k + 1) → Prop) [DecidableRel E']
    (h1 : ∀ a b, E' a b ↔ E (Fin.castLE h a) (Fin.castLE h b))
    (h2 : ∀ a b, E a b → b.val = a.val + 1) (h3 : ∀ a b, tailEdge k a b → E a b) :
    edgeSum E (g : GL (Fin r) F) =
      edgeSum (tailEdge k) (g : GL (Fin r) F) + edgeSum E' (corner h g : GL (Fin (k + 1)) F) := by
  have e : edgeSum E' (corner h g : GL (Fin (k + 1)) F) =
      edgeSum (fun a b => E a b ∧ a.val < k) (g : GL (Fin r) F) := by
    unfold edgeSum
    refine Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ (fun a ha => ?_) (fun a => ?_)
    · refine Finset.sum_eq_zero fun b _ => if_neg fun hb => ha ⟨⟨a.val, by omega⟩, rfl⟩
    · refine Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ (fun b hb => ?_) (fun b => ?_)
      · refine if_neg fun hE => hb ⟨⟨b.val, by have := h2 _ _ hE.1; have := hE.2; omega⟩, rfl⟩
      · rw [corner_apply]
        refine if_congr ⟨fun hE => ⟨(h1 _ _).1 hE, ?_⟩, fun hE => (h1 _ _).2 hE.1⟩ rfl rfl
        have := h2 _ _ ((h1 _ _).1 hE)
        have hb := b.2
        simp only [Fin.val_castLE] at this ⊢
        omega
  rw [e]
  unfold edgeSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases hE : E a b
  · by_cases ha : a.val < k
    · rw [if_pos hE, if_neg (fun t : tailEdge k a b => absurd t.2 (by omega)), if_pos ⟨hE, ha⟩, zero_add]
    · rw [if_pos hE, if_pos (show tailEdge k a b from ⟨h2 _ _ hE, by omega⟩), if_neg (fun t => ha t.2), add_zero]
  · rw [if_neg hE, if_neg (fun t => hE (h3 _ _ t)), if_neg (fun t => hE t.1), add_zero]

theorem mem_unip_iff {k : ℕ} (h : k + 1 ≤ r) (g : GL (Fin r) F) : g ∈ unip F r ↔
    ∃ hg : g ∈ tailUnip F r k, (corner h ⟨g, hg⟩ : GL (Fin (k + 1)) F) ∈ unip F (k + 1) := by
  constructor
  · intro hg
    refine ⟨mem_tailUnip.2 fun i j _ hj => mem_unip.1 hg i j hj, mem_unip.2 fun i j hj => ?_⟩
    rw [corner_apply, ← one_castLE h]
    exact mem_unip.1 hg _ _ hj
  · rintro ⟨hg, hc⟩
    refine mem_unip.2 fun i j hj => ?_
    by_cases hi : k ≤ i.val
    · exact mem_tailUnip.1 hg i j hi hj
    · have := mem_unip.1 hc ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ hj
      rw [corner_apply, ← one_castLE h] at this
      exact this

theorem mem_unipSym_iff {k : ℕ} (h : k + 1 ≤ r) (g : GL (Fin r) F) : g ∈ unipSym F r 0 k ↔
    ∃ hg : g ∈ tailUnip F r k, (corner h ⟨g, hg⟩ : GL (Fin (k + 1)) F) ∈ unipSym F (k + 1) 0 k := by
  constructor
  · rintro ⟨hg, h0⟩
    obtain ⟨hg', hc⟩ := (mem_unip_iff h g).1 hg
    exact ⟨hg', hc, fun i j a b c => h0 (Fin.castLE h i) (Fin.castLE h j) a b c⟩
  · rintro ⟨hg, hc, h0⟩
    exact ⟨(mem_unip_iff h g).2 ⟨hg, hc⟩, fun i j a b c =>
      h0 ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ a b c⟩

theorem edgeSum_one {n : ℕ} (E : Fin n → Fin n → Prop) [DecidableRel E] (h : ∀ a b, E a b → b.val = a.val + 1) :
    edgeSum E (1 : GL (Fin n) F) = 0 := by
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  split_ifs with hE
  · have := h _ _ hE
    rw [Units.val_one, one_apply_ne (fun e => by rw [e] at this; omega)]
  · rfl

theorem nPos_zero_eq_sum : ∀ (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ), ψ ≠ 1 → ∀ (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (τ : Representation ℂ (GL (Fin r) F) V) (k : ℕ), k + 1 ≤ r → nPos ψ τ 0 k = ∑ j ∈ Finset.range (k + 1), gam (Fintype.card F) (k - j) * whCut ψ τ j := by
  intro F _ _ ψ hψ r V _ _ _ τ k h
  obtain ⟨M, π, hπ⟩ := exists_descent τ (tailUnip F r k) (corner h) (corner_surj h) (addCharHom ψ (tailHom F r k))
  have hχ : ∀ g : tailUnip F r k, ((addCharHom ψ (tailHom F r k) g : ℂˣ) : ℂ) =
      ψ (edgeSum (tailEdge k) (g : GL (Fin r) F)) := fun g => rfl
  have main := GlobalTheory.T.finrank_mirabolic_whittaker_eigenspace F ψ hψ k (tailUnip F (k + 1) k) mem_tailUnip_last M π
  have hs : ∀ {n : ℕ} (a b : Fin n), symEdge 0 k a b → b.val = a.val + 1 := fun a b t => by
    unfold symEdge at t; omega
  rw [hπ _ _ (unipSym F r 0 k : Set (GL (Fin r) F)) (fun g => ψ (edgeSum (symEdge 0 k) g))
    (Subgroup.one_mem (unipSym F (k + 1) 0 k))
    (by simp only [OneMemClass.coe_one]; rw [edgeSum_one _ hs, AddChar.map_zero_eq_one])
    (mem_unipSym_iff h) (fun g _ => by
      rw [hχ, ← AddChar.map_add_eq_mul, ← edgeSum_split h g (symEdge 0 k) (symEdge 0 k) (fun _ _ => Iff.rfl) hs
        (fun a b t => by unfold tailEdge at t; unfold symEdge; omega)])] at main
  unfold nPos
  rw [main]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.1 hj
  rw [hπ _ _ (unip F r : Set (GL (Fin r) F)) (fun g => ψ (edgeSum (cutEdge j) g))
    (Subgroup.one_mem (unip F (k + 1)))
    (by simp only [OneMemClass.coe_one]; rw [edgeSum_one _ (fun _ _ t => t.1), AddChar.map_zero_eq_one])
    (mem_unip_iff h) (fun g _ => by
      rw [hχ, ← AddChar.map_add_eq_mul, ← edgeSum_split h g (cutEdge j) (cutEdge j) (fun _ _ => Iff.rfl) (fun _ _ t => t.1)
        (fun a b t => by unfold tailEdge at t; unfold cutEdge; omega)])]
  rfl

end GlobalTheory.FinGL.PosOne
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricPositionCharMultiplicityEqSumDegenerateStatement
open GlobalTheory.FinGL Formalism.L2.DIV Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricPositionCharMultiplicity_eq_sum_degenerateWhittaker : ∀ (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ), ψ ≠ 1 → ∀ (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (τ : Representation ℂ (GL (Fin r) F) V) (k : ℕ), k + 1 ≤ r → nPos ψ τ 0 k = ∑ j ∈ Finset.range (k + 1), gam (Fintype.card F) (k - j) * whCut ψ τ j := by
  first | exact @GlobalTheory.FinGL.PosOne.nPos_zero_eq_sum | exact GlobalTheory.FinGL.PosOne.nPos_zero_eq_sum | (intros; apply GlobalTheory.FinGL.PosOne.nPos_zero_eq_sum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricPositionCharMultiplicitySuccEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricPositionCharMultiplicitySuccEq
noncomputable section

namespace GlobalTheory.FinGL.RootExchange

open Formalism.L2.DIV Module

section Abstract

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

theorem mem_eig_iff (τ : Representation ℂ G V) (S : Set G) (χ : G → ℂ) (v : V) :
    v ∈ eig τ S χ ↔ ∀ g ∈ S, τ g v = χ g • v := by
  simp [eig, Submodule.mem_iInf, sub_eq_zero]

def proj (τ : Representation ℂ G V) (A : Subgroup G) [Fintype A] (χ : G → ℂ) : V →ₗ[ℂ] V :=
  ∑ a : A, χ (a : G)⁻¹ • τ a

theorem proj_apply (τ : Representation ℂ G V) (A : Subgroup G) [Fintype A] (χ : G → ℂ) (v : V) :
    proj τ A χ v = ∑ a : A, χ (a : G)⁻¹ • τ a v := by
  simp [proj, LinearMap.sum_apply]

theorem proj_mem (τ : Representation ℂ G V) (A : Subgroup G) [Fintype A] (χ : G → ℂ)
    (hχ : ∀ x ∈ A, ∀ y ∈ A, χ (x * y) = χ x * χ y) (v : V) : proj τ A χ v ∈ eig τ A χ := by
  rw [mem_eig_iff]
  intro g hg
  set_option synthInstance.maxHeartbeats 100000 in
    rw [proj_apply, map_sum, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft (⟨g, hg⟩ : A)) _ _ fun a => ?_
  have h : χ (a : G)⁻¹ = χ g * χ (g * a)⁻¹ := by
    rw [mul_comm, ← hχ _ (A.inv_mem (A.mul_mem hg a.2)) _ hg]
    congr 1
    group
  simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, map_smul, map_mul, Module.End.mul_apply, smul_smul, h]

theorem proj_act (τ : Representation ℂ G V) (A : Subgroup G) [Fintype A] (χ : G → ℂ)
    (hχ : ∀ x ∈ A, ∀ y ∈ A, χ (x * y) = χ x * χ y) {g : G} (hg : g ∈ A) (v : V) :
    proj τ A χ (τ g v) = χ g • proj τ A χ v := by
  rw [proj_apply, proj_apply, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulRight (⟨g, hg⟩ : A)) _ _ fun a => ?_
  have h : χ (a : G)⁻¹ = χ g * χ (a * g)⁻¹ := by
    rw [← hχ _ hg _ (A.inv_mem (A.mul_mem a.2 hg))]
    congr 1
    group
  simp only [Equiv.coe_mulRight, Subgroup.coe_mul, map_mul, Module.End.mul_apply, smul_smul, h]

theorem proj_of_mem (τ : Representation ℂ G V) (A : Subgroup G) [Fintype A] (χ : G → ℂ)
    (hχ : ∀ x ∈ A, ∀ y ∈ A, χ (x * y) = χ x * χ y) (h1 : χ 1 = 1) {v : V} (hv : v ∈ eig τ A χ) :
    proj τ A χ v = (Fintype.card A : ℂ) • v := by
  rw [mem_eig_iff] at hv
  rw [proj_apply, Finset.sum_congr rfl (g := fun _ => v)]
  · rw [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
  · intro a _
    rw [hv a a.2, smul_smul, ← hχ _ (A.inv_mem a.2) _ a.2, inv_mul_cancel, h1, one_smul]

theorem finrank_eig_le [FiniteDimensional ℂ V] (τ : Representation ℂ G V) (A B : Subgroup G) [Finite A] [Finite B]
    (χ : G → ℂ) (hA : ∀ x ∈ A, ∀ y ∈ A, χ (x * y) = χ x * χ y) (hB : ∀ x ∈ B, ∀ y ∈ B, χ (x * y) = χ x * χ y)
    (h1 : χ 1 = 1) (hx : ∀ b ∈ B, b ∉ A → ∃ a ∈ A, b⁻¹ * a * b ∈ A ∧ χ (b⁻¹ * a * b) ≠ χ a) :
    finrank ℂ (eig τ A χ) ≤ finrank ℂ (eig τ B χ) := by
  classical
  haveI := Fintype.ofFinite A
  haveI := Fintype.ofFinite B
  let f : eig τ A χ →ₗ[ℂ] eig τ B χ :=
    ((proj τ B χ).comp (eig τ A χ).subtype).codRestrict _ fun v => proj_mem τ B χ hB v
  refine LinearMap.finrank_le_finrank_of_injective (f := f) ?_
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  rintro ⟨v, hv⟩ h0
  have h0' : proj τ B χ v = 0 := congrArg Subtype.val h0
  have hv' := (mem_eig_iff τ A χ v).1 hv
  have key : ∀ b : B, proj τ A χ (χ (b : G)⁻¹ • τ b v) =
      (if (b : G) ∈ A then (Fintype.card A : ℂ) else 0) • v := by
    intro b
    rw [map_smul]
    split_ifs with hb
    · rw [proj_act τ A χ hA hb, smul_smul, ← hA _ (A.inv_mem hb) _ hb, inv_mul_cancel, h1, one_smul,
        proj_of_mem τ A χ hA h1 hv]
    · obtain ⟨a, ha, ha', hne⟩ := hx b b.2 hb
      have e1 := proj_act τ A χ hA ha (τ b v)
      have e2 : τ a (τ b v) = χ ((b : G)⁻¹ * a * b) • τ b v := by
        rw [← map_smul, ← hv' _ ha', ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
        congr 2
        group
      rw [e2, map_smul, ← sub_eq_zero, ← sub_smul, smul_eq_zero, sub_eq_zero] at e1
      rw [e1.resolve_left hne, smul_zero, zero_smul]
  have h2 := congrArg (proj τ A χ) h0'
  set_option synthInstance.maxHeartbeats 100000 in
    rw [proj_apply τ B, map_sum, map_zero, Finset.sum_congr rfl fun b _ => key b, ← Finset.sum_smul,
    smul_eq_zero] at h2
  refine Subtype.ext (h2.resolve_left ?_)
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  refine mul_ne_zero ?_ (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
  refine Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨1, ?_⟩)
  simp

theorem finrank_eig_conj (τ : Representation ℂ G V) (S T : Set G) (χ χ' : G → ℂ) (w : G)
    (hS : ∀ g, g ∈ T ↔ w⁻¹ * g * w ∈ S) (hχ : ∀ g, χ (w⁻¹ * g * w) = χ' g) :
    finrank ℂ (eig τ S χ) = finrank ℂ (eig τ T χ') := by
  let e : V ≃ₗ[ℂ] V := LinearEquiv.ofLinear (τ w) (τ w⁻¹)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl)
  refine (e.ofSubmodules _ _ ?_).finrank_eq
  ext v
  rw [Submodule.mem_map_equiv, mem_eig_iff, mem_eig_iff]
  have he : e.symm v = τ w⁻¹ v := rfl
  rw [he]
  constructor
  · intro h g hg
    have h1 := congrArg (τ w) (h _ ((hS g).1 hg))
    rw [hχ, map_smul] at h1
    simp only [← Module.End.mul_apply, ← map_mul] at h1
    simpa [mul_assoc] using h1
  · intro h g hg
    have e1 : w⁻¹ * (w * g * w⁻¹) * w = g := by group
    have h1 := congrArg (τ w⁻¹) (h (w * g * w⁻¹) ((hS _).2 (by rwa [e1])))
    rw [← hχ, e1, map_smul] at h1
    rw [← h1]
    simp only [← Module.End.mul_apply, ← map_mul]
    congr 2
    group

end Abstract

section Matrices

variable {F : Type} [Field F] {r : ℕ}

def cyc (ρ k : ℕ) (h : ρ + k < r) : Equiv.Perm (Fin r) where
  toFun i := ⟨if i.val < ρ then i.val else if i.val < ρ + k then i.val + 1 else if i.val = ρ + k then ρ else i.val, by
    have := i.2
    split_ifs <;> omega⟩
  invFun i := ⟨if i.val < ρ then i.val else if i.val = ρ then ρ + k else if i.val ≤ ρ + k then i.val - 1 else i.val, by
    have := i.2
    split_ifs <;> omega⟩
  left_inv i := by
    ext
    dsimp only
    split_ifs <;> omega
  right_inv i := by
    ext
    dsimp only
    split_ifs <;> omega

theorem cyc_val (ρ k : ℕ) (h : ρ + k < r) (i : Fin r) : (cyc ρ k h i).val =
    if i.val < ρ then i.val else if i.val < ρ + k then i.val + 1 else if i.val = ρ + k then ρ else i.val := rfl

theorem exists_perm (σ : Equiv.Perm (Fin r)) : ∃ w : GL (Fin r) F, ∀ (g : GL (Fin r) F) (i j : Fin r),
    ((w⁻¹ * g * w : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j = (g : Matrix (Fin r) (Fin r) F) (σ i) (σ j) := by
  refine ⟨⟨σ.symm.toPEquiv.toMatrix, σ.toPEquiv.toMatrix, ?_, ?_⟩, fun g i j => ?_⟩
  · rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]; simp
  · rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]; simp
  · show ((σ.toPEquiv.toMatrix * (g : Matrix (Fin r) (Fin r) F) * σ.symm.toPEquiv.toMatrix :
      Matrix (Fin r) (Fin r) F)) i j = _
    rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
    simp

def elem {p q : Fin r} (h : p ≠ q) (t : F) : GL (Fin r) F :=
  ⟨Matrix.transvection p q t, Matrix.transvection p q (-t),
    by rw [Matrix.transvection_mul_transvection_same _ _ h]; simp,
    by rw [Matrix.transvection_mul_transvection_same _ _ h]; simp⟩

theorem conj_elem {p q : Fin r} (h : p ≠ q) (t : F) (g : GL (Fin r) F) (i l : Fin r) :
    ((g⁻¹ * elem h t * g : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i l =
      (1 : Matrix (Fin r) (Fin r) F) i l +
        ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i p * t * (g : Matrix (Fin r) (Fin r) F) q l := by
  have e : ((elem h t : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) = 1 + Matrix.single p q t := rfl
  rw [Units.val_mul, Units.val_mul, e, mul_add, add_mul, mul_one, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.add_apply]
  congr 1
  rw [Matrix.mul_apply, Finset.sum_eq_single q]
  · rw [Matrix.mul_single_apply_same]
  · intro b _ hb
    rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hb, zero_mul]
  · simp

end Matrices

section Main

variable {F : Type} [Field F] {r : ℕ}

theorem edgeSum_single (Ed : Fin r → Fin r → Prop) [DecidableRel Ed] (g : GL (Fin r) F) {p q : Fin r} (h : Ed p q)
    (h0 : ∀ i j, Ed i j → (i ≠ p ∨ j ≠ q) → (g : Matrix (Fin r) (Fin r) F) i j = 0) :
    edgeSum Ed g = (g : Matrix (Fin r) (Fin r) F) p q := by
  unfold edgeSum
  rw [Finset.sum_eq_single p, Finset.sum_eq_single q, if_pos h]
  · intro j _ hj
    split_ifs with e
    · exact h0 _ _ e (Or.inr hj)
    · rfl
  · simp
  · intro i _ hi
    refine Finset.sum_eq_zero fun j _ => ?_
    split_ifs with e
    · exact h0 _ _ e (Or.inl hi)
    · rfl
  · simp

theorem mem_unip_iff (g : GL (Fin r) F) : g ∈ unip F r ↔
    (∀ i, (g : Matrix (Fin r) (Fin r) F) i i = 1) ∧
      ∀ i j : Fin r, j.val < i.val → (g : Matrix (Fin r) (Fin r) F) i j = 0 :=
  ⟨fun h => ⟨h.2, fun _ _ e => h.1 e⟩, fun h => ⟨fun i j e => h.2 i j e, h.1⟩⟩

theorem mem_unipSym_iff (ρ k : ℕ) (g : GL (Fin r) F) : g ∈ unipSym F r ρ k ↔
    g ∈ unip F r ∧ ∀ i j : Fin r, ρ ≤ i.val → i.val < ρ + k → j.val = ρ + k →
      (g : Matrix (Fin r) (Fin r) F) i j = 0 := Iff.rfl

theorem mem_conj_iff {ρ k : ℕ} (h : ρ + k < r) {g g' : GL (Fin r) F}
    (e : ∀ i j, (g' : Matrix (Fin r) (Fin r) F) i j = (g : Matrix (Fin r) (Fin r) F) (cyc ρ k h i) (cyc ρ k h j)) :
    g' ∈ unipSym F r ρ k ↔ g ∈ unip F r ∧ ∀ i j : Fin r, i.val = ρ → ρ < j.val → j.val ≤ ρ + k →
      (g : Matrix (Fin r) (Fin r) F) i j = 0 := by
  rw [mem_unipSym_iff, mem_unip_iff, mem_unip_iff]
  simp only [e]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨fun i => ?_, fun i j hij => ?_⟩, fun i j a1 a2 a3 => ?_⟩
    · obtain ⟨i, rfl⟩ := (cyc ρ k h).surjective i
      exact h1 i
    · obtain ⟨i, rfl⟩ := (cyc ρ k h).surjective i
      obtain ⟨j, rfl⟩ := (cyc ρ k h).surjective j
      rw [cyc_val, cyc_val] at hij
      by_cases c : j.val < i.val
      · exact h2 i j c
      · refine h3 i j ?_ ?_ ?_ <;> split_ifs at hij <;> omega
    · obtain ⟨i, rfl⟩ := (cyc ρ k h).surjective i
      obtain ⟨j, rfl⟩ := (cyc ρ k h).surjective j
      rw [cyc_val] at a1 a2 a3
      refine h2 i j ?_
      split_ifs at a1 a2 a3 <;> omega
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨fun i => h1 _, fun i j hij => ?_⟩, fun i j a1 a2 a3 => ?_⟩
    · by_cases c : (cyc ρ k h j).val < (cyc ρ k h i).val
      · exact h2 _ _ c
      · rw [cyc_val, cyc_val] at c
        refine h3 _ _ ?_ ?_ ?_ <;> rw [cyc_val] <;> split_ifs at c ⊢ <;> omega
    · refine h2 _ _ ?_
      rw [cyc_val, cyc_val]
      split_ifs <;> omega

theorem edgeSum_conj {ρ k : ℕ} (h : ρ + k < r) {g g' : GL (Fin r) F}
    (e : ∀ i j, (g' : Matrix (Fin r) (Fin r) F) i j = (g : Matrix (Fin r) (Fin r) F) (cyc ρ k h i) (cyc ρ k h j)) :
    edgeSum (symEdge ρ k) g' = edgeSum (symEdge (ρ + 1) k) g := by
  unfold edgeSum
  refine Fintype.sum_equiv (cyc ρ k h) _ _ fun i => Fintype.sum_equiv (cyc ρ k h) _ _ fun j => ?_
  rw [e]
  refine if_congr ?_ rfl rfl
  unfold symEdge
  rw [cyc_val, cyc_val]
  split_ifs <;> omega

theorem chi_mul (ψ : AddChar F ℂ) (ρ k : ℕ) {x y : GL (Fin r) F} (hx : x ∈ unipSym F r ρ k)
    (hy : y ∈ unipSym F r ρ k) :
    ψ (edgeSum (symEdge ρ k) (x * y)) = ψ (edgeSum (symEdge ρ k) x) * ψ (edgeSum (symEdge ρ k) y) := by
  rw [← AddChar.map_add_eq_mul]
  congr 1
  exact congrArg Multiplicative.toAdd ((symHom F r ρ k).map_mul ⟨x, hx⟩ ⟨y, hy⟩)

theorem conj_elem_mem_unip {p q : Fin r} (h : p ≠ q) (hpq : p.val < q.val) (t : F) {g : GL (Fin r) F}
    (hg : g ∈ unip F r) : g⁻¹ * elem h t * g ∈ unip F r := by
  refine (unip F r).mul_mem ((unip F r).mul_mem ((unip F r).inv_mem hg) ?_) hg
  have e : ((elem h t : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) = 1 + Matrix.single p q t := rfl
  rw [mem_unip_iff, e]
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · rw [Matrix.add_apply, Matrix.single_apply_of_ne, Matrix.one_apply_eq, add_zero]
    rintro ⟨rfl, rfl⟩
    exact h rfl
  · rw [Matrix.add_apply, Matrix.single_apply_of_ne, Matrix.one_apply_ne, add_zero]
    · rintro rfl
      omega
    · rintro ⟨rfl, rfl⟩
      omega

theorem conj_elem_zero {p q : Fin r} (h : p ≠ q) (t : F) {g : GL (Fin r) F} (hg : g ∈ unip F r) {i l : Fin r}
    (hil : i.val ≠ l.val) (h0 : p.val < i.val ∨ l.val < q.val) :
    ((g⁻¹ * elem h t * g : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i l = 0 := by
  rw [conj_elem, Matrix.one_apply_ne (fun e => hil (congrArg _ e)), zero_add]
  rcases h0 with h0 | h0
  · rw [unip_lower ((unip F r).inv_mem hg) (show p < i from h0), zero_mul, zero_mul]
  · rw [unip_lower hg (show l < q from h0), mul_zero]

theorem edgeSum_conj_elem {ρ k : ℕ} {a c p q : Fin r} (ha : a.val = ρ) (hc : c.val = ρ + k + 1) (h : p ≠ q)
    (hs : (p.val = ρ ∧ ρ < q.val) ∨ (q.val = ρ + k + 1 ∧ p.val ≤ ρ + k)) (t : F) {g : GL (Fin r) F}
    (hg : g ∈ unip F r) :
    edgeSum (symEdge (ρ + 1) k) (g⁻¹ * elem h t * g) =
      ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) a p * t * (g : Matrix (Fin r) (Fin r) F) q c := by
  rw [edgeSum_single (p := a) (q := c) _ _ (Or.inr ⟨by omega, by omega⟩), conj_elem,
    Matrix.one_apply_ne (fun e => by rw [e] at ha; omega), zero_add]
  intro i j hij hne
  rw [Ne, Ne, Fin.ext_iff, Fin.ext_iff] at hne
  unfold symEdge at hij
  exact conj_elem_zero h t hg (by omega) (by omega)

theorem nPos_succ (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (r : ℕ) (V : Type)
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (τ : Representation ℂ (GL (Fin r) F) V) (ρ k : ℕ)
    (hr : ρ + k + 2 ≤ r) : nPos ψ τ ρ k = nPos ψ τ (ρ + 1) k := by
  classical
  have h : ρ + k < r := by omega
  obtain ⟨w, hw⟩ := exists_perm (F := F) (cyc ρ k h)
  obtain ⟨t, ht⟩ := AddChar.ne_one_iff.1 hψ
  let A : Subgroup (GL (Fin r) F) := (unipSym F r ρ k).comap (MulAut.conj w⁻¹).toMonoidHom
  have hA0 : ∀ g, g ∈ A ↔ w⁻¹ * g * w ∈ unipSym F r ρ k := fun g => by simp [A]
  have hA : ∀ g, g ∈ A ↔ g ∈ unip F r ∧ ∀ i j : Fin r, i.val = ρ → ρ < j.val → j.val ≤ ρ + k →
      (g : Matrix (Fin r) (Fin r) F) i j = 0 := fun g => (hA0 g).trans (mem_conj_iff h (hw g))
  have hE : ∀ g : GL (Fin r) F, edgeSum (symEdge ρ k) (w⁻¹ * g * w) = edgeSum (symEdge (ρ + 1) k) g :=
    fun g => edgeSum_conj h (hw g)
  let χ : GL (Fin r) F → ℂ := fun g => ψ (edgeSum (symEdge (ρ + 1) k) g)
  have hχA : ∀ x ∈ A, ∀ y ∈ A, χ (x * y) = χ x * χ y := by
    intro x hx y hy
    simp only [χ, ← hE]
    rw [← chi_mul ψ ρ k ((hA0 x).1 hx) ((hA0 y).1 hy)]
    congr 2
    group
  have hχB : ∀ x ∈ unipSym F r (ρ + 1) k, ∀ y ∈ unipSym F r (ρ + 1) k, χ (x * y) = χ x * χ y :=
    fun x hx y hy => chi_mul ψ (ρ + 1) k hx hy
  have hχ1 : χ 1 = 1 := by
    have : edgeSum (symEdge (ρ + 1) k) (1 : GL (Fin r) F) = 0 :=
      congrArg Multiplicative.toAdd (symHom F r (ρ + 1) k).map_one
    simp only [χ, this, AddChar.map_zero_eq_one]
  let a : Fin r := ⟨ρ, by omega⟩
  let c : Fin r := ⟨ρ + k + 1, by omega⟩
  have ha : a.val = ρ := rfl
  have hc : c.val = ρ + k + 1 := rfl
  have triv : ∀ x : GL (Fin r) F, x = 1⁻¹ * x * 1 := fun x => by simp
  unfold nPos
  rw [finrank_eig_conj τ _ (A : Set (GL (Fin r) F)) _ χ w hA0 (fun g => by simp only [χ, hE])]
  refine le_antisymm (finrank_eig_le τ _ _ χ hχA hχB hχ1 fun b hb hbA => ?_)
    (finrank_eig_le τ _ _ χ hχB hχA hχ1 fun b hb hbB => ?_)
  · have hu : b ∈ unip F r := hb.1
    have h1 : b⁻¹ ∉ A := fun e => hbA (by simpa using A.inv_mem e)
    rw [hA] at h1
    push Not at h1
    obtain ⟨i, j, hi, hj1, hj2, hne⟩ := h1 ((unip F r).inv_mem hu)
    obtain rfl : i = a := Fin.ext hi
    have hjc : j ≠ c := fun e => by rw [e] at hj2; omega
    have hmem : ∀ (s : F) (g : GL (Fin r) F), g ∈ unip F r → g⁻¹ * elem hjc s * g ∈ A := fun s g hg =>
      (hA _).2 ⟨conj_elem_mem_unip hjc (by omega) s hg, fun i l _ _ _ =>
        conj_elem_zero hjc s hg (by omega) (by omega)⟩
    refine ⟨elem hjc ((((b⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) a j)⁻¹ * t), ?_, hmem _ _ hu, ?_⟩
    · rw [triv (elem _ _)]
      exact hmem _ _ (unip F r).one_mem
    · conv_rhs => rw [triv (elem _ _)]
      simp only [χ]
      rw [edgeSum_conj_elem ha hc hjc (by omega) _ hu, edgeSum_conj_elem ha hc hjc (by omega) _ (unip F r).one_mem,
        unip_diag hu, mul_one, mul_inv_cancel_left₀ hne, inv_one, Units.val_one,
        Matrix.one_apply_ne (fun e : a = j => by rw [← e] at hj1; omega), zero_mul, zero_mul, AddChar.map_zero_eq_one]
      exact ht
  · have hu : b ∈ unip F r := ((hA b).1 hb).1
    rw [mem_unipSym_iff] at hbB
    push Not at hbB
    obtain ⟨j, l, hj1, hj2, hl, hne⟩ := hbB hu
    obtain rfl : l = c := Fin.ext (by omega)
    have haj : a ≠ j := fun e => by rw [← e] at hj1; omega
    have hmem : ∀ (s : F) (g : GL (Fin r) F), g ∈ unip F r → g⁻¹ * elem haj s * g ∈ unipSym F r (ρ + 1) k :=
      fun s g hg => ⟨conj_elem_mem_unip haj (by omega) s hg, fun i l _ _ _ =>
        conj_elem_zero haj s hg (by omega) (by omega)⟩
    refine ⟨elem haj (t * ((b : Matrix (Fin r) (Fin r) F) j c)⁻¹), ?_, hmem _ _ hu, ?_⟩
    · rw [triv (elem _ _)]
      exact hmem _ _ (unip F r).one_mem
    · conv_rhs => rw [triv (elem _ _)]
      simp only [χ]
      rw [edgeSum_conj_elem ha hc haj (by omega) _ hu, edgeSum_conj_elem ha hc haj (by omega) _ (unip F r).one_mem,
        unip_diag ((unip F r).inv_mem hu), one_mul, inv_mul_cancel_right₀ hne, Units.val_one,
        Matrix.one_apply_ne (fun e : j = c => by rw [e] at hj2; omega), mul_zero, AddChar.map_zero_eq_one]
      exact ht

end Main

end GlobalTheory.FinGL.RootExchange
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricPositionCharMultiplicitySuccEqStatement
open GlobalTheory.FinGL Formalism.L2.DIV Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricPositionCharMultiplicity_succ_eq : ∀ (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ), ψ ≠ 1 → ∀ (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (τ : Representation ℂ (GL (Fin r) F) V) (ρ k : ℕ), ρ + k + 2 ≤ r → nPos ψ τ ρ k = nPos ψ τ (ρ + 1) k := by
  first | exact @GlobalTheory.FinGL.RootExchange.nPos_succ | exact GlobalTheory.FinGL.RootExchange.nPos_succ | (intros; apply GlobalTheory.FinGL.RootExchange.nPos_succ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricPositionCharMultiplicityParabolicInduct
namespace GlobalTheory.FinGL

open Formalism.L2.DIV Module

theorem finiteDimensional_coindV_blockTri {F : Type} [Field F] [Fintype F] {r : ℕ} {V : Type} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V) :
    FiniteDimensional ℂ (Representation.coindV (blockTri (κ := F) b).subtype σ) := by
  classical
  have : Finite (GL (Fin r) F) := inferInstance
  infer_instance

theorem nPos_parInd (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (r : ℕ) (V : Type)
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (b : Fin r → ℕ)
    (σ : Representation ℂ (blockTri (κ := F) b) V) (hσ : IsCuspDatum b σ) (ρ k : ℕ) (h : ρ + k + 1 ≤ r) :
    nPos ψ (parInd b σ) ρ k = ∑ j ∈ Finset.range (k + 1), splitDoublingNBlock b j * gam (Fintype.card F) (k - j) := by
  have hfd := finiteDimensional_coindV_blockTri b σ
  induction ρ with
  | zero =>
    rw [GlobalTheory.T.symmetricPositionCharMultiplicity_eq_sum_degenerateWhittaker F ψ hψ r _ (parInd b σ) k (by omega)]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.1 hj
    rw [GlobalTheory.T.degenerateWhittakerDim_parabolicInduction_cuspidal F ψ hψ r V b σ hσ j (Or.inl (by omega)), GlobalTheory.T.levi_whittaker_eq_one_of_cuspidal F ψ hψ r V b σ hσ, mul_one, mul_comm]
  | succ ρ ih =>
    rw [← GlobalTheory.T.symmetricPositionCharMultiplicity_succ_eq F ψ hψ r _ (parInd b σ) ρ k (by omega)]
    exact ih (by omega)

end GlobalTheory.FinGL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricPositionCharMultiplicityParabolicInductStatement
open GlobalTheory.FinGL Formalism.L2.DIV Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricPositionCharMultiplicity_parabolicInduction : ∀ (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ), ψ ≠ 1 → ∀ (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V), IsCuspDatum b σ → ∀ ρ k : ℕ, ρ + k + 1 ≤ r → nPos ψ (parInd b σ) ρ k = ∑ j ∈ Finset.range (k + 1), splitDoublingNBlock b j * gam (Fintype.card F) (k - j) := by
  first | exact @GlobalTheory.FinGL.nPos_parInd | exact GlobalTheory.FinGL.nPos_parInd | (intros; apply GlobalTheory.FinGL.nPos_parInd <;> assumption)
end
