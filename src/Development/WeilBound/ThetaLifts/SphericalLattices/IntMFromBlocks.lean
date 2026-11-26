module

public import Development.WeilBound.ThetaLifts.SphericalLattices.LocCommSt

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.SphericalLattices.IndexComapOfCover
noncomputable section

namespace PositivityTheory.Sph.M2.ZC

open Matrix Formalism.UG

theorem index_comap_of_cover {A G : Type*} [Group A] [Group G] (f : A →* G) (H : Subgroup G)
    (h : ∀ g, ∃ a, (f a)⁻¹ * g ∈ H) : (H.comap f).index = H.index := by
  refine Nat.card_congr (Equiv.ofBijective
    (Quotient.map' f (fun a b hab => ?_) : A ⧸ H.comap f → G ⧸ H) ⟨?_, ?_⟩)
  · rw [QuotientGroup.leftRel_apply] at hab ⊢
    simpa using hab
  · intro a b
    induction a using QuotientGroup.induction_on with | H a => ?_
    induction b using QuotientGroup.induction_on with | H b => ?_
    intro hab
    have h1 : ((f a : G) : G ⧸ H) = (f b : G) := hab
    rw [QuotientGroup.eq] at h1 ⊢
    simpa using h1
  · intro g
    induction g using QuotientGroup.induction_on with | H g => ?_
    obtain ⟨a, ha⟩ := h g
    exact ⟨(a : A ⧸ H.comap f), (QuotientGroup.eq.mpr ha : ((f a : G) : G ⧸ H) = g)⟩

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem mem_int {y : L} : y ∈ intL L ↔ Valued.v y ≤ (1 : WithZero (Multiplicative ℤ)) := Iff.rfl

def A (r : L) : AddSubgroup L := (intL L).toAddSubgroup.comap (AddMonoidHom.mulLeft r)

theorem mem_A {r y : L} : y ∈ A r ↔ r * y ∈ intL L := Iff.rfl

theorem A_mul (r s : L) : A (r * s) = (A r).comap (AddMonoidHom.mulLeft s) := by
  ext y
  simp [mem_A, mul_assoc]

theorem relIndex_A_mul (r r' s : L) (hs : s ≠ 0) : (A (r * s)).relIndex (A (r' * s)) = (A r).relIndex (A r') := by
  rw [A_mul, A_mul, AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective]
  intro y
  exact ⟨s⁻¹ * y, by simp [hs]⟩

variable {ϖ : L} {c : L →+* L} {q : ℕ}

theorem pi_ne (h : IsUnramInv ϖ c q) : ϖ ≠ 0 := by
  intro h0
  have := h.2.2.2.1
  rw [h0, map_zero] at this
  exact WithZero.coe_ne_zero this.symm

theorem pi_int (h : IsUnramInv ϖ c q) : ϖ ∈ intL L := by
  rw [mem_int, h.2.2.2.1, ← WithZero.coe_one, WithZero.coe_le_coe]
  decide

theorem mem_A_inv (h : IsUnramInv ϖ c q) {y : L} :
    y ∈ A ϖ⁻¹ ↔ Valued.v y < (1 : WithZero (Multiplicative ℤ)) := by
  rw [mem_A, mem_int, map_mul, map_inv₀, h.2.2.2.1]
  by_cases hy : Valued.v y = (0 : WithZero (Multiplicative ℤ))
  · simp [hy]
  · obtain ⟨n, hn⟩ := WithZero.ne_zero_iff_exists.mp hy
    rw [← hn, ← WithZero.coe_inv, ← WithZero.coe_mul, ← WithZero.coe_one, WithZero.coe_le_coe, WithZero.coe_lt_coe]
    show (-(-1 : ℤ) + Multiplicative.toAdd n ≤ 0) ↔ Multiplicative.toAdd n < 0
    omega

theorem relIndex_one (h : IsUnramInv ϖ c q) : (A ϖ⁻¹).relIndex (A (1 : L)) = q ^ 2 := by
  have e : A (1 : L) = (intL L).subtype.toAddMonoidHom.range := by
    ext y
    simp [mem_A]
  rw [e, ← AddSubgroup.index_comap, ← h.2.2.2.2.2.2]
  have e2 : (A ϖ⁻¹).comap (intL L).subtype.toAddMonoidHom =
      (IsLocalRing.maximalIdeal (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring).toAddSubgroup := by
    ext y
    rw [AddSubgroup.mem_comap, mem_A_inv h]
    exact (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation L (WithZero (Multiplicative ℤ)))) (a := y)).symm
  rw [e2]
  rfl

theorem A_le (h : IsUnramInv ϖ c q) (r : L) : A (ϖ⁻¹ * r) ≤ A r := by
  intro y hy
  rw [mem_A] at hy ⊢
  have := (intL L).mul_mem (pi_int h) hy
  rwa [mul_assoc, mul_inv_cancel_left₀ (pi_ne h)] at this

theorem relIndex_two (h : IsUnramInv ϖ c q) : (A (ϖ⁻¹ * ϖ⁻¹)).relIndex (A (1 : L)) = q ^ 4 := by
  have h1 : (A (ϖ⁻¹ * ϖ⁻¹)).relIndex (A ϖ⁻¹) = q ^ 2 := by
    rw [← relIndex_one h, ← relIndex_A_mul ϖ⁻¹ 1 ϖ⁻¹ (inv_ne_zero (pi_ne h)), one_mul]
  have h2 : A ϖ⁻¹ ≤ A (1 : L) := by simpa using A_le h 1
  rw [← AddSubgroup.relIndex_mul_relIndex _ _ _ (A_le h _) h2, h1, relIndex_one h]
  ring

def MA (m : ℕ) (r : L) : AddSubgroup (Matrix (Fin m) (Fin m) L) :=
  AddSubgroup.pi Set.univ fun _ => AddSubgroup.pi Set.univ fun _ => A r

theorem mem_MA {m : ℕ} {r : L} {X : Matrix (Fin m) (Fin m) L} : X ∈ MA m r ↔ ∀ i j, r * X i j ∈ intL L :=
  ⟨fun h i j => h i trivial j trivial, fun h i _ j _ => h i j⟩

theorem relIndex_MA (m : ℕ) (r : L) : (MA m r).relIndex (MA m (1 : L)) = ((A r).relIndex (A (1 : L))) ^ (m * m) := by
  let g : (Fin m → Fin m → A (1 : L)) →+ Matrix (Fin m) (Fin m) L :=
    { toFun := fun Y => Matrix.of fun i j => (Y i j : L)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have e : MA m (1 : L) = g.range := by
    ext X
    constructor
    · intro hX
      exact ⟨fun i j => ⟨X i j, mem_MA.mp hX i j⟩, rfl⟩
    · rintro ⟨Y, rfl⟩
      exact mem_MA.mpr fun i j => (Y i j).2
  have e2 : (MA m r).comap g = AddSubgroup.pi Set.univ fun _ => AddSubgroup.pi Set.univ fun _ =>
      (A r).addSubgroupOf (A (1 : L)) := by
    ext Y
    exact ⟨fun h i _ j _ => h i trivial j trivial, fun h i _ j _ => h i trivial j trivial⟩
  rw [e, ← AddSubgroup.index_comap, e2, AddSubgroup.index_pi]
  simp only [AddSubgroup.index_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
  rfl

def NA (c : L →+* L) (m : ℕ) : AddSubgroup (Matrix (Fin m) (Fin m) L) where
  carrier := {X | (∀ i j, X i j ∈ intL L) ∧ ∀ i j, c (X i j) = -X j i}
  zero_mem' := ⟨fun _ _ => (intL L).zero_mem, fun _ _ => by simp⟩
  add_mem' := fun {X Y} hX hY => ⟨fun i j => (intL L).add_mem (hX.1 i j) (hY.1 i j), fun i j => by
    simp only [Matrix.add_apply, map_add (f := _), hX.2, hY.2, neg_add]⟩
  neg_mem' := fun {X} hX => ⟨fun i j => (intL L).neg_mem (hX.1 i j), fun i j => by
    simp only [Matrix.neg_apply, map_neg, hX.2]⟩

theorem c_int (h : IsUnramInv ϖ c q) {y : L} (hy : y ∈ intL L) : c y ∈ intL L := by
  rw [mem_int, h.2.1]; exact hy

theorem relIndex_NA_sq (h : IsUnramInv ϖ c q) (m : ℕ) (r : L) (hr : c r = r) :
    (MA m r).relIndex (NA c m) * (MA m r).relIndex (NA c m) = (MA m r).relIndex (MA m (1 : L)) := by
  obtain ⟨x, hx, hd⟩ := h.2.2.2.2.1
  have hd0 : c x - x ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hd
    exact zero_ne_one hd
  have hd1 : x - c x ≠ 0 := fun h0 => hd0 (by linear_combination -h0)
  have hdi : (c x - x)⁻¹ ∈ intL L := by rw [mem_int, map_inv₀, hd, inv_one]
  let f : NA c m × NA c m →+ Matrix (Fin m) (Fin m) L :=
    { toFun := fun p => (p.1 : Matrix (Fin m) (Fin m) L) + x • (p.2 : Matrix (Fin m) (Fin m) L)
      map_zero' := by simp
      map_add' := fun p p' => by
        simp only [Prod.fst_add, Prod.snd_add, AddSubgroup.coe_add, smul_add]
        abel }
  have fa : ∀ p i j, f p i j = (p.1 : Matrix (Fin m) (Fin m) L) i j + x * (p.2 : Matrix (Fin m) (Fin m) L) i j :=
    fun _ _ _ => rfl
  have e : MA m (1 : L) = f.range := by
    ext X
    rw [mem_MA]
    simp only [one_mul]
    constructor
    · intro hX
      have hb : ∀ i j, -((c x - x)⁻¹ * (X i j + c (X j i))) ∈ intL L := fun i j =>
        (intL L).neg_mem ((intL L).mul_mem hdi ((intL L).add_mem (hX i j) (c_int h (hX j i))))
      refine ⟨(⟨Matrix.of fun i j => X i j - x * -((c x - x)⁻¹ * (X i j + c (X j i))), fun i j =>
          (intL L).sub_mem (hX i j) ((intL L).mul_mem hx (hb i j)), fun i j => ?_⟩,
        ⟨Matrix.of fun i j => -((c x - x)⁻¹ * (X i j + c (X j i))), hb, fun i j => ?_⟩), ?_⟩
      · simp only [Matrix.of_apply, map_sub, map_mul, map_neg, map_inv₀, map_add (f := _), h.1]
        rw [← neg_sub (c x) x, inv_neg]
        field_simp
        ring
      · simp only [Matrix.of_apply, map_sub, map_mul, map_neg, map_inv₀, map_add (f := _), h.1]
        rw [← neg_sub (c x) x, inv_neg]
        ring
      · ext i j
        rw [fa]
        simp
    · rintro ⟨p, rfl⟩ i j
      rw [fa]
      exact (intL L).add_mem (p.1.2.1 i j) ((intL L).mul_mem hx (p.2.2.1 i j))
  have e2 : (MA m r).comap f = ((MA m r).addSubgroupOf (NA c m)).prod ((MA m r).addSubgroupOf (NA c m)) := by
    ext p
    simp only [AddSubgroup.mem_comap, AddSubgroup.mem_prod, AddSubgroup.mem_addSubgroupOf, mem_MA, fa]
    constructor
    · intro hp
      have hb : ∀ i j, r * (p.2 : Matrix (Fin m) (Fin m) L) i j ∈ intL L := fun i j => by
        have h1 := (intL L).neg_mem ((intL L).mul_mem hdi ((intL L).add_mem (hp i j) (c_int h (hp j i))))
        simp only [map_mul, map_add (f := _), hr, p.1.2.2, p.2.2.2] at h1
        convert h1 using 1
        field_simp
        ring
      refine ⟨fun i j => ?_, hb⟩
      have h1 := (intL L).sub_mem (hp i j) ((intL L).mul_mem hx (hb i j))
      convert h1 using 1
      ring
    · intro hp i j
      have h1 := (intL L).add_mem (hp.1 i j) ((intL L).mul_mem hx (hp.2 i j))
      convert h1 using 1
      ring
  rw [e, ← AddSubgroup.index_comap, e2, AddSubgroup.index_prod]
  rfl

theorem relIndex_NA (h : IsUnramInv ϖ c q) (m : ℕ) :
    (MA m (ϖ⁻¹ * ϖ⁻¹)).relIndex (NA c m) = q ^ (2 * m * m) := by
  have h1 := relIndex_NA_sq h m (ϖ⁻¹ * ϖ⁻¹) (by rw [map_mul, map_inv₀, h.2.2.1])
  rw [relIndex_MA, relIndex_two h] at h1
  apply Nat.mul_self_inj.mp
  rw [h1]
  ring

end PositivityTheory.Sph.M2.ZC

end
end

noncomputable section

namespace PositivityTheory.Sph.M2.ZC

open Matrix Formalism.UG GlobalTheory.CompanionTheory.VacLoc.BigCellLocal

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {ϖ : L} {c : L →+* L} {q : ℕ} {m : ℕ}

def IntM {α β : Type} (X : Matrix α β L) : Prop := ∀ i j, X i j ∈ intL L

theorem IntM.mul {α β γ : Type} [Fintype β] {X : Matrix α β L} {Y : Matrix β γ L} (hX : IntM X) (hY : IntM Y) :
    IntM (X * Y) := by
  intro i j
  rw [Matrix.mul_apply]
  exact sum_mem fun k _ => mul_mem (hX i k) (hY k j)

theorem IntM.conjT (h : IsUnramInv ϖ c q) {α β : Type} {X : Matrix α β L} (hX : IntM X) : IntM (X.map c)ᵀ := by
  intro i j
  exact c_int h (hX j i)

theorem intM_one {α : Type} [DecidableEq α] : IntM (1 : Matrix α α L) := by
  intro i j
  rw [Matrix.one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem intM_zero {α β : Type} : IntM (0 : Matrix α β L) := by
  intro i j
  exact zero_mem _

theorem intM_fromBlocks {α : Type} {a b c' d : Matrix α α L} :
    IntM (fromBlocks a b c' d) ↔ IntM a ∧ IntM b ∧ IntM c' ∧ IntM d := by
  constructor
  · intro hM
    exact ⟨fun i j => hM (Sum.inl i) (Sum.inl j), fun i j => hM (Sum.inl i) (Sum.inr j),
      fun i j => hM (Sum.inr i) (Sum.inl j), fun i j => hM (Sum.inr i) (Sum.inr j)⟩
  · rintro ⟨ha, hb, hc, hd⟩ i j
    rcases i with i | i <;> rcases j with j | j
    exacts [ha i j, hb i j, hc i j, hd i j]

theorem mem_IntGL {g : GL (Fin m ⊕ Fin m) L} : g ∈ IntGL L m ↔ IntM g.val ∧ IntM (g⁻¹).val := by
  constructor
  · intro hg
    obtain ⟨g', rfl⟩ := MonoidHom.mem_range.mp hg
    exact ⟨fun i j => (g'.val i j).2, fun i j => ((g'⁻¹).val i j).2⟩
  · rintro ⟨h1, h2⟩
    refine MonoidHom.mem_range.mpr
      ⟨⟨Matrix.of fun i j => ⟨g.val i j, h1 i j⟩, Matrix.of fun i j => ⟨(g⁻¹).val i j, h2 i j⟩, ?_, ?_⟩, ?_⟩
    · ext i j
      have e := congrFun (congrFun (Units.mul_inv g) i) j
      rw [Matrix.mul_apply] at e
      rw [Matrix.mul_apply, AddSubmonoidClass.coe_finsetSum]
      simp only [MulMemClass.coe_mul, Matrix.of_apply]
      rw [e, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> rfl
    · ext i j
      have e := congrFun (congrFun (Units.inv_mul g) i) j
      rw [Matrix.mul_apply] at e
      rw [Matrix.mul_apply, AddSubmonoidClass.coe_finsetSum]
      simp only [MulMemClass.coe_mul, Matrix.of_apply]
      rw [e, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> rfl
    · ext i j
      rfl

theorem inv_of_iso (h : IsUnramInv ϖ c q) {g : GL (Fin m ⊕ Fin m) L} (hg : Iso c (Wm L (Fin m)) (Wm L (Fin m)) g.val) :
    (g⁻¹).val = Wm L (Fin m) * (g.val.map c)ᵀ * Wm L (Fin m) := by
  have hcc : ∀ y, c (c y) = y := h.1
  have hW : (Wm L (Fin m)).map c = Wm L (Fin m) := by
    show (fromBlocks 0 1 1 0 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L).map c = fromBlocks 0 1 1 0
    rw [Matrix.fromBlocks_map]
    simp
  have hgg : (g.val.map c).map c = g.val := by
    rw [Matrix.map_map]
    ext i j
    exact hcc _
  have hg' : g.valᵀ * Wm L (Fin m) * g.val.map c = Wm L (Fin m) := hg
  have h2 : (g.val.map c)ᵀ * Wm L (Fin m) * g.val = Wm L (Fin m) := by
    have e := congrArg (fun M => M.map c) hg'
    rw [Matrix.map_mul, Matrix.map_mul, hW, hgg, Matrix.transpose_map] at e
    exact e
  apply Units.inv_eq_of_mul_eq_one_left
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (g.val.map c)ᵀ, h2, Wm_mul_self]

theorem mem_KPW (h : IsUnramInv ϖ c q) {g : GL (Fin m ⊕ Fin m) L} :
    g ∈ KPW L c m ↔ g ∈ GW L c m ∧ g.val.toBlocks₂₁ = 0 ∧ IntM g.val := by
  have hB : g ∈ GlobalTheory.LGrp.blockQ L (GlobalTheory.LGrp.twoBlocks (Fin m) (Fin m)) ↔ g.val.toBlocks₂₁ = 0 := by
    show (g.val).BlockTriangular (GlobalTheory.LGrp.twoBlocks (Fin m) (Fin m)) ↔ _
    constructor
    · intro hb
      ext i j
      exact @hb (Sum.inr i) (Sum.inl j) (show (0:ℕ) < 1 from Nat.one_pos)
    · intro h0 i j hij
      rcases i with i | i <;> rcases j with j | j
      · exact absurd hij (lt_irrefl _)
      · exact absurd hij (Nat.not_lt_zero _)
      · exact congrFun (congrFun h0 i) j
      · exact absurd hij (lt_irrefl _)
  have hWint : IntM (Wm L (Fin m)) := by
    show IntM (fromBlocks 0 1 1 0 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L)
    exact intM_fromBlocks.mpr ⟨intM_zero, intM_one, intM_one, intM_zero⟩
  show g ∈ (GW L c m ⊓ GlobalTheory.LGrp.blockQ L (GlobalTheory.LGrp.twoBlocks (Fin m) (Fin m))) ⊓ (GW L c m ⊓ IntGL L m) ↔ _
  simp only [Subgroup.mem_inf, hB, mem_IntGL]
  constructor
  · rintro ⟨⟨hG, hC⟩, -, hI, -⟩
    exact ⟨hG, hC, hI⟩
  · rintro ⟨hG, hC, hI⟩
    refine ⟨⟨hG, hC⟩, hG, hI, ?_⟩
    rw [inv_of_iso h hG]
    exact IntM.mul (IntM.mul hWint (IntM.conjT h hI)) hWint

theorem zW_mem (h : IsUnramInv ϖ c q) {x : Lˣ} (hx : (x : L) = ϖ) : zW L m x ∈ GW L c m := by
  have hcx : c (x : L) = x := by rw [hx]; exact h.2.2.1
  have hx0 : (x : L) ≠ 0 := x.ne_zero
  have hcx' : c (x : L)⁻¹ = (x : L)⁻¹ := by rw [map_inv₀, hcx]
  show (fromBlocks ((x : L) • (1 : Matrix (Fin m) (Fin m) L)) 0 0 (((x⁻¹ : Lˣ) : L) • 1))ᵀ * fromBlocks 0 1 1 0 *
      (fromBlocks ((x : L) • (1 : Matrix (Fin m) (Fin m) L)) 0 0 (((x⁻¹ : Lˣ) : L) • 1)).map c = fromBlocks 0 1 1 0
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [Units.val_inv_eq_inv_val, Matrix.smul_one_eq_diagonal, Matrix.diagonal_map, Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal, hcx, hcx', hx0]

theorem conj_val (x : Lˣ) (g : GL (Fin m ⊕ Fin m) L) :
    ((zW L m x)⁻¹ * g * zW L m x).val = fromBlocks g.val.toBlocks₁₁ (((x : L)⁻¹ * (x : L)⁻¹) • g.val.toBlocks₁₂)
      (((x : L) * x) • g.val.toBlocks₂₁) g.val.toBlocks₂₂ := by
  have hx0 : (x : L) ≠ 0 := x.ne_zero
  have hg : g.val = fromBlocks g.val.toBlocks₁₁ g.val.toBlocks₁₂ g.val.toBlocks₂₁ g.val.toBlocks₂₂ :=
    (Matrix.fromBlocks_toBlocks _).symm
  show fromBlocks (((x⁻¹ : Lˣ) : L) • (1 : Matrix (Fin m) (Fin m) L)) 0 0 ((x : L) • 1) * g.val *
      fromBlocks ((x : L) • (1 : Matrix (Fin m) (Fin m) L)) 0 0 (((x⁻¹ : Lˣ) : L) • 1) = _
  conv_lhs => rw [hg]
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [Units.val_inv_eq_inv_val, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hx0]

theorem mem_conj (h : IsUnramInv ϖ c q) {x : Lˣ} (hx : (x : L) = ϖ) {g : GL (Fin m ⊕ Fin m) L} :
    g ∈ (KPW L c m).map (MulAut.conj (zW L m x)).toMonoidHom ↔ g ∈ GW L c m ∧ g.val.toBlocks₂₁ = 0 ∧
      IntM g.val.toBlocks₁₁ ∧ IntM g.val.toBlocks₂₂ ∧ g.val.toBlocks₁₂ ∈ MA m (ϖ⁻¹ * ϖ⁻¹) := by
  have hz := zW_mem (m := m) h hx
  have key : g ∈ (KPW L c m).map (MulAut.conj (zW L m x)).toMonoidHom ↔
      (zW L m x)⁻¹ * g * zW L m x ∈ KPW L c m := by
    constructor
    · intro hg
      obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hg
      simpa [mul_assoc] using hk
    · intro hk
      exact Subgroup.mem_map.mpr ⟨_, hk, by simp [mul_assoc]⟩
  have hGW : (zW L m x)⁻¹ * g * zW L m x ∈ GW L c m ↔ g ∈ GW L c m := by
    constructor
    · intro h1
      have := (GW L c m).mul_mem ((GW L c m).mul_mem hz h1) ((GW L c m).inv_mem hz)
      simpa [mul_assoc] using this
    · intro h1
      exact (GW L c m).mul_mem ((GW L c m).mul_mem ((GW L c m).inv_mem hz) h1) hz
  have hp : ϖ ≠ 0 := pi_ne h
  rw [key, mem_KPW h, hGW, conj_val, Matrix.toBlocks_fromBlocks₂₁, intM_fromBlocks, hx]
  constructor
  · rintro ⟨hG, hC, hA, hB, -, hD⟩
    have hC' : g.val.toBlocks₂₁ = 0 := by
      rw [smul_eq_zero] at hC
      exact hC.resolve_left (mul_ne_zero hp hp)
    refine ⟨hG, hC', hA, hD, ?_⟩
    rw [mem_MA]
    intro i j
    exact hB i j
  · rintro ⟨hG, hC, hA, hD, hB⟩
    rw [mem_MA] at hB
    refine ⟨hG, by rw [hC, smul_zero], hA, fun i j => hB i j, by rw [hC, smul_zero]; exact intM_zero, hD⟩

theorem conj_le (h : IsUnramInv ϖ c q) {x : Lˣ} (hx : (x : L) = ϖ) :
    (KPW L c m).map (MulAut.conj (zW L m x)).toMonoidHom ≤ KPW L c m := by
  intro g hg
  rw [mem_conj h hx] at hg
  obtain ⟨hG, hC, hA, hD, hB⟩ := hg
  rw [mem_KPW h]
  refine ⟨hG, hC, ?_⟩
  rw [← Matrix.fromBlocks_toBlocks g.val, intM_fromBlocks]
  refine ⟨hA, ?_, by rw [hC]; exact intM_zero, hD⟩
  intro i j
  rw [mem_MA] at hB
  have hp : ϖ ≠ 0 := pi_ne h
  have e : g.val.toBlocks₁₂ i j = (ϖ * ϖ) * ((ϖ⁻¹ * ϖ⁻¹) * g.val.toBlocks₁₂ i j) := by
    field_simp
  rw [e]
  exact mul_mem (mul_mem (pi_int h) (pi_int h)) (hB i j)

def nU (X : Matrix (Fin m) (Fin m) L) : GL (Fin m ⊕ Fin m) L :=
  ⟨fromBlocks 1 X 0 1, fromBlocks 1 (-X) 0 1, by simp [fromBlocks_multiply, fromBlocks_one],
    by simp [fromBlocks_multiply, fromBlocks_one]⟩

theorem nU_mem (h : IsUnramInv ϖ c q) {X : Matrix (Fin m) (Fin m) L} (hX : X ∈ NA c m) : nU X ∈ KPW L c m := by
  obtain ⟨hXi, hXs⟩ := hX
  rw [mem_KPW h]
  refine ⟨?_, ?_, ?_⟩
  · show Iso c (Wm L (Fin m)) (Wm L (Fin m)) (fromBlocks 1 X 0 1)
    apply iso_n
    ext i j
    exact hXs i j
  · exact Matrix.toBlocks_fromBlocks₂₁ _ _ _ _
  · show IntM (fromBlocks 1 X 0 1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L)
    exact intM_fromBlocks.mpr ⟨intM_one, hXi, intM_zero, intM_one⟩

def nHom (h : IsUnramInv ϖ c q) (m : ℕ) : Multiplicative (NA c m) →* KPW L c m where
  toFun X := ⟨nU (X.toAdd : NA c m).1, nU_mem h (X.toAdd : NA c m).2⟩
  map_one' := Subtype.ext (Units.ext (by simp [nU, fromBlocks_one]))
  map_mul' X Y := Subtype.ext (Units.ext (by simp [nU, fromBlocks_multiply, add_comm]))

theorem skew_of_iso (h : IsUnramInv ϖ c q) {a b d : Matrix (Fin m) (Fin m) L}
    (hg : Iso c (Wm L (Fin m)) (Wm L (Fin m)) (fromBlocks a b 0 d)) :
    (a.map c)ᵀ * d = 1 ∧ (b * (a.map c)ᵀ).map c = -(b * (a.map c)ᵀ)ᵀ := by
  have hcc : ∀ y, c (c y) = y := h.1
  have hmm : ∀ M : Matrix (Fin m) (Fin m) L, (M.map c).map c = M := by
    intro M
    rw [Matrix.map_map]
    ext i j
    exact hcc _
  have hg' : (fromBlocks a b 0 d)ᵀ * fromBlocks 0 1 1 0 * (fromBlocks a b 0 d).map c =
      (fromBlocks 0 1 1 0 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) := hg
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply] at hg'
  simp only [Matrix.transpose_zero, Matrix.map_zero, map_zero, Matrix.mul_zero, Matrix.zero_mul,
    Matrix.mul_one, Matrix.one_mul, add_zero, zero_add] at hg'
  obtain ⟨-, h12, h21, h22⟩ := Matrix.fromBlocks_inj.mp hg'
  have e1 : (a.map c)ᵀ * d = 1 := by
    have e := congrArg (fun M => M.map c) h12
    simp only [Matrix.map_mul, hmm, Matrix.map_one (⇑c) (map_zero c) (map_one c)] at e
    rw [← Matrix.transpose_map]
    exact e
  have hA : a.map c * dᵀ = 1 := mul_eq_one_comm.mp h21
  have hD : d.map c * aᵀ = 1 := mul_eq_one_comm.mp h12
  have h22' : dᵀ * b.map c = -(bᵀ * d.map c) := eq_neg_of_add_eq_zero_left h22
  refine ⟨e1, ?_⟩
  rw [Matrix.map_mul, Matrix.transpose_map, hmm, Matrix.transpose_mul, Matrix.transpose_transpose]
  calc b.map c * aᵀ = a.map c * dᵀ * b.map c * aᵀ := by rw [hA, Matrix.one_mul]
    _ = a.map c * (dᵀ * b.map c) * aᵀ := by rw [Matrix.mul_assoc (a.map c)]
    _ = -(a.map c * bᵀ * (d.map c * aᵀ)) := by
      rw [h22']
      simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
    _ = -(a.map c * bᵀ) := by rw [hD, Matrix.mul_one]

theorem cover (h : IsUnramInv ϖ c q) {x : Lˣ} (hx : (x : L) = ϖ) (k : KPW L c m) :
    ∃ X, (nHom h m X)⁻¹ * k ∈ ((KPW L c m).map (MulAut.conj (zW L m x)).toMonoidHom).subgroupOf (KPW L c m) := by
  have hk := (mem_KPW h).mp k.2
  obtain ⟨hG, hC, hI⟩ := hk
  obtain ⟨A, hA'⟩ : ∃ A, A = (k : GL (Fin m ⊕ Fin m) L).val.toBlocks₁₁ := ⟨_, rfl⟩
  obtain ⟨B, hB'⟩ : ∃ B, B = (k : GL (Fin m ⊕ Fin m) L).val.toBlocks₁₂ := ⟨_, rfl⟩
  obtain ⟨D, hD'⟩ : ∃ D, D = (k : GL (Fin m ⊕ Fin m) L).val.toBlocks₂₂ := ⟨_, rfl⟩
  have hv : (k : GL (Fin m ⊕ Fin m) L).val = fromBlocks A B 0 D := by
    rw [hA', hB', hD', ← hC, Matrix.fromBlocks_toBlocks]
  have hiso : Iso c (Wm L (Fin m)) (Wm L (Fin m)) (fromBlocks A B 0 D) := by
    rw [← hv]
    exact hG
  obtain ⟨e1, e2⟩ := skew_of_iso h hiso
  have hIfb : IntM (fromBlocks A B 0 D) := by
    rw [← hv]
    exact hI
  obtain ⟨hA, hB, -, hD⟩ := intM_fromBlocks.mp hIfb
  obtain ⟨X, hXdef⟩ : ∃ X : Matrix (Fin m) (Fin m) L, X = B * (A.map c)ᵀ := ⟨_, rfl⟩
  have hXNA : X ∈ NA c m := by
    refine ⟨?_, ?_⟩
    · rw [hXdef]
      exact IntM.mul hB (IntM.conjT h hA)
    · intro i j
      rw [hXdef]
      exact congrFun (congrFun e2 i) j
  have hXD : X * D = B := by
    rw [hXdef, Matrix.mul_assoc, e1, Matrix.mul_one]
  refine ⟨Multiplicative.ofAdd ⟨X, hXNA⟩, ?_⟩
  have hprod : (((nHom h m (Multiplicative.ofAdd ⟨X, hXNA⟩))⁻¹ * k : KPW L c m) :
      GL (Fin m ⊕ Fin m) L).val = fromBlocks A 0 0 D := by
    show fromBlocks 1 (-X) 0 1 * (k : GL (Fin m ⊕ Fin m) L).val = _
    rw [hv, Matrix.fromBlocks_multiply]
    simp [hXD]
  rw [Subgroup.mem_subgroupOf, mem_conj h hx, hprod, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₁₁,
    Matrix.toBlocks_fromBlocks₂₂, Matrix.toBlocks_fromBlocks₁₂]
  exact ⟨((nHom h m (Multiplicative.ofAdd ⟨X, hXNA⟩))⁻¹ * k).2.1.1, rfl, hA, hD, zero_mem _⟩

theorem comap_eq (h : IsUnramInv ϖ c q) {x : Lˣ} (hx : (x : L) = ϖ) :
    (((KPW L c m).map (MulAut.conj (zW L m x)).toMonoidHom).subgroupOf (KPW L c m)).comap (nHom h m) =
      ((MA m (ϖ⁻¹ * ϖ⁻¹)).addSubgroupOf (NA c m)).toSubgroup := by
  ext X
  rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, mem_conj h hx]
  show _ ↔ ((Multiplicative.toAdd X : NA c m) : Matrix (Fin m) (Fin m) L) ∈ MA m (ϖ⁻¹ * ϖ⁻¹)
  have hv : ((nHom h m X : KPW L c m) : GL (Fin m ⊕ Fin m) L).val =
      fromBlocks 1 ((Multiplicative.toAdd X : NA c m) : Matrix (Fin m) (Fin m) L) 0 1 := rfl
  rw [hv, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₂₂,
    Matrix.toBlocks_fromBlocks₁₂]
  constructor
  · rintro ⟨-, -, -, -, hM⟩
    exact hM
  · intro hM
    exact ⟨(nHom h m X).2.1.1, rfl, intM_one, intM_one, hM⟩

end PositivityTheory.Sph.M2.ZC

namespace PositivityTheory.Sph.M2

theorem zCount : ZCountSt := by
  intro L _ _ ϖ c q h m x hx
  refine ⟨ZC.conj_le h hx, ?_⟩
  show (((KPW L c m).map (MulAut.conj (zW L m x)).toMonoidHom).subgroupOf (KPW L c m)).index = q ^ (2 * m * m)
  rw [← ZC.index_comap_of_cover (ZC.nHom h m) _ (ZC.cover h hx), ZC.comap_eq h hx, AddSubgroup.index_toSubgroup]
  exact ZC.relIndex_NA h m

end PositivityTheory.Sph.M2

end
