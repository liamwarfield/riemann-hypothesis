module

public import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.GLVolumeIndex
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.GLVolumeIndex

open MeasureTheory Matrix Finset ValuativeRel
open Formalism.MainNotions.ZetaProductPairs (qE zetaProd idxPar Lpair)
open scoped Classical

section Levels

variable {O : Type} [CommRing O] [IsLocalRing O]

abbrev red {m n : Type} (A : Matrix m n O) : Matrix m n (IsLocalRing.ResidueField O) :=
  A.map (IsLocalRing.residue O)

def princ (O : Type) [CommRing O] [IsLocalRing O] (n : Type) [Fintype n] [DecidableEq n] :
    Subgroup (GL n O) :=
  (Matrix.GeneralLinearGroup.map (n := n) (IsLocalRing.residue O)).ker

theorem isUnit_of_red {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n O)
    (h : IsUnit (red A)) : IsUnit A := by
  rw [Matrix.isUnit_iff_isUnit_det] at h ⊢
  have e : (red A).det = IsLocalRing.residue O A.det := (RingHom.map_det _ _).symm
  rw [e] at h
  exact (IsLocalRing.residue_ne_zero_iff_isUnit _).1 h.ne_zero

theorem red_mul {l m n : Type} [Fintype m] (A : Matrix l m O) (B : Matrix m n O) :
    red (A * B) = red A * red B := by
  exact Matrix.map_mul

theorem red_add {m n : Type} (A B : Matrix m n O) : red (A + B) = red A + red B := by
  ext i j
  simp [red]

theorem red_eq_zero {m n : Type} (A : Matrix m n O) :
    red A = 0 ↔ ∀ i j, A i j ∈ IsLocalRing.maximalIdeal O := by
  rw [← Matrix.ext_iff]
  simp [red, IsLocalRing.residue_eq_zero_iff]

theorem exists_mem_of_red {n : Type} [Fintype n] [DecidableEq n] {J : Subgroup (GL n O)}
    (hJ : princ O n ≤ J) {k : GL n O} (hk : k ∈ J) {A : Matrix n n O}
    (h : red A = red (k : Matrix n n O)) : ∃ k' ∈ J, (k' : Matrix n n O) = A := by
  have hred1 : red (((k⁻¹ : GL n O) : Matrix n n O) * A) = 1 := by
    rw [red_mul, h, ← red_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    ext i j
    simp [red, Matrix.one_apply]
  have hu : IsUnit (((k⁻¹ : GL n O) : Matrix n n O) * A) := isUnit_of_red _ (by rw [hred1]; exact isUnit_one)
  have hup : hu.unit ∈ princ O n := by
    rw [princ, MonoidHom.mem_ker]
    ext1
    simpa using hred1
  refine ⟨k * hu.unit, J.mul_mem hk (hJ hup), ?_⟩
  simp [← Matrix.mul_assoc]

theorem blocks_mul {a t : Type} [Fintype a] [Fintype t] (g h : Matrix (a ⊕ t) (a ⊕ t) O) :
    (g * h).toBlocks₁₁ = g.toBlocks₁₁ * h.toBlocks₁₁ + g.toBlocks₁₂ * h.toBlocks₂₁ ∧
    (g * h).toBlocks₂₁ = g.toBlocks₂₁ * h.toBlocks₁₁ + g.toBlocks₂₂ * h.toBlocks₂₁ ∧
    (g * h).toBlocks₂₂ = g.toBlocks₂₁ * h.toBlocks₁₂ + g.toBlocks₂₂ * h.toBlocks₂₂ := by
  refine ⟨?_, ?_, ?_⟩ <;> ext i j <;>
    simp [toBlocks₁₁, toBlocks₁₂, toBlocks₂₁, toBlocks₂₂, Matrix.mul_apply, Fintype.sum_sum_type]

def level {a : ℕ} (t : ℕ) (J' : Subgroup (GL (Fin a) O)) (hJ : princ O (Fin a) ≤ J') :
    Subgroup (GL (Fin a ⊕ Fin t) O) where
  carrier := {g | (∃ k ∈ J', (k : Matrix (Fin a) (Fin a) O) = g.val.toBlocks₁₁) ∧
    (∀ i j, g.val.toBlocks₂₁ i j ∈ IsLocalRing.maximalIdeal O) ∧
    ∃ d : GL (Fin t) O, (d : Matrix (Fin t) (Fin t) O) = g.val.toBlocks₂₂}
  one_mem' := by
    refine ⟨⟨1, J'.one_mem, ?_⟩, ?_, ⟨1, ?_⟩⟩
    · ext i j; simp [toBlocks₁₁, Matrix.one_apply]
    · intro i j; simp [toBlocks₂₁]
    · ext i j; simp [toBlocks₂₂, Matrix.one_apply]
  mul_mem' := by
    rintro g h ⟨⟨k, hk, e1⟩, c1, d, f1⟩ ⟨⟨k', hk', e2⟩, c2, d', f2⟩
    obtain ⟨b1, b2, b3⟩ := blocks_mul g.val h.val
    rw [← red_eq_zero] at c1 c2
    refine ⟨exists_mem_of_red hJ (J'.mul_mem hk hk') ?_, ?_, ?_⟩
    · rw [Units.val_mul, b1, red_add, red_mul _ (toBlocks₂₁ _), c2, ← e1, ← e2]; simp
    · rw [← red_eq_zero, Units.val_mul, b2, red_add, red_mul, red_mul, c1, c2]; simp
    · apply isUnit_of_red
      rw [Units.val_mul, b3, red_add, red_mul (toBlocks₂₁ _), c1, ← f1, ← f2, Matrix.zero_mul,
        zero_add, ← Units.val_mul]
      exact (d * d').isUnit.map (IsLocalRing.residue O).mapMatrix
  inv_mem' := by
    rintro g ⟨⟨k, hk, e1⟩, c1, d, f1⟩
    obtain ⟨b1, b2, b3⟩ := blocks_mul g.val (g⁻¹).val
    rw [Units.mul_inv] at b1 b2 b3
    rw [← red_eq_zero] at c1
    have o1 : (1 : Matrix (Fin a ⊕ Fin t) (Fin a ⊕ Fin t) O).toBlocks₁₁ = 1 := by
      ext i j; simp [toBlocks₁₁, Matrix.one_apply]
    have o2 : (1 : Matrix (Fin a ⊕ Fin t) (Fin a ⊕ Fin t) O).toBlocks₂₁ = 0 := by
      ext i j; simp [toBlocks₂₁]
    have o3 : (1 : Matrix (Fin a ⊕ Fin t) (Fin a ⊕ Fin t) O).toBlocks₂₂ = 1 := by
      ext i j; simp [toBlocks₂₂, Matrix.one_apply]
    rw [o1, ← e1] at b1
    rw [o2, ← f1] at b2
    rw [o3, ← f1] at b3
    have r1 : ∀ n : ℕ, red (1 : Matrix (Fin n) (Fin n) O) = 1 := fun n => by simp [red]
    have c2 : red (g⁻¹).val.toBlocks₂₁ = 0 := by
      have := congrArg (fun X => red (d⁻¹).val * red X) b2
      simp only [red_add, red_mul (toBlocks₂₁ _), c1, Matrix.zero_mul, zero_add] at this
      rw [← red_mul, ← red_mul, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul] at this
      rw [← this]; simp [red]
    refine ⟨exists_mem_of_red hJ (J'.inv_mem hk) ?_, (red_eq_zero _).1 c2, ?_⟩
    · have := congrArg (fun X => red (k⁻¹).val * red X) b1
      simp only [red_add, red_mul _ (toBlocks₂₁ _), c2, Matrix.mul_zero, add_zero] at this
      rw [← red_mul, ← red_mul, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul,
        Matrix.mul_one] at this
      exact this.symm
    · apply isUnit_of_red
      have := congrArg red b3
      rw [red_add, red_mul (toBlocks₂₁ _), c1, Matrix.zero_mul, zero_add, red_mul, r1] at this
      exact (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_left_inverse this.symm)

def parahoric (O : Type) [CommRing O] [IsLocalRing O] (r s : ℕ) : Subgroup (GL (Fin r ⊕ Fin s) O) :=
  level s (⊤ : Subgroup (GL (Fin r) O)) le_top

end Levels

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

def resCard (F : Type) [Field F] [ValuativeRel F] : ℝ := (Nat.card 𝓀[F] : ℝ)

def unitIn (u : 𝒪[F]ˣ) : Fˣ := Units.map (𝒪[F].subtype : 𝒪[F] →* F) u

def entries {m n : Type} (A : Matrix m n 𝒪[F]) : m → n → F := fun i j => (A i j : F)

def groupSet {n : Type} [Fintype n] [DecidableEq n] (H : Subgroup (GL n 𝒪[F])) : Set (n → n → F) :=
  {x | ∃ k ∈ H, entries k.val = x}

def zetaFrom (q : ℝ) (c n : ℕ) : ℝ := (qE q (c + 1) n)⁻¹

variable [MeasurableSpace F]

def volAdd (ν : Measure F) (m n : Type) [Fintype m] [Fintype n] : Measure (m → n → F) :=
  Measure.pi fun _ : m => Measure.pi fun _ : n => ν

def volGroup (ν : Measure F) {n : Type} [Fintype n] [DecidableEq n] (H : Subgroup (GL n 𝒪[F])) : ℝ :=
  (volAdd ν n n).real (groupSet H)

def VolumeOfGL (ν : Measure F) : Prop :=
  ∀ (n : Type) [Fintype n] [DecidableEq n],
    volGroup ν (⊤ : Subgroup (GL n 𝒪[F])) = qE (resCard F) 1 (Fintype.card n)

end Local

end GlobalTheory.IndefiniteRowSideFullHecke.GLVolumeIndex
end
end

noncomputable section

namespace GlobalTheory.IndexVolume

open MeasureTheory Matrix Finset ValuativeRel
open Formalism.MainNotions.ZetaProductPairs (qE zetaProd idxPar Lpair)
open GlobalTheory.IndefiniteRowSideFullHecke.GLVolumeIndex
open scoped Classical

theorem card_GL_real (k : Type) [Field k] [Finite k] (n : Type) [Fintype n] [DecidableEq n] :
    (Nat.card (GL n k) : ℝ) =
      (Nat.card k : ℝ) ^ (Fintype.card n * Fintype.card n) * qE (Nat.card k) 1 (Fintype.card n) := by
  have := Fintype.ofFinite k
  have e : GL n k ≃ GL (Fin (Fintype.card n)) k :=
    (Units.mapEquiv (Matrix.reindexAlgEquiv k k (Fintype.equivFin n)).toMulEquiv).toEquiv
  rw [Nat.card_congr e, Matrix.card_GL_field, ← Nat.card_eq_fintype_card (α := k)]
  generalize Fintype.card n = N
  have hq : 0 < Nat.card k := Nat.card_pos
  generalize Nat.card k = q at hq
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  rw [Nat.cast_prod]
  have h1 : ∀ i : Fin N, ((q ^ N - q ^ (i : ℕ) : ℕ) : ℝ) =
      (q : ℝ) ^ N * (1 - (q : ℝ) ^ (-((N - 1 - i + 1 : ℕ) : ℤ))) := by
    intro i
    rw [Nat.cast_sub (Nat.pow_le_pow_right hq i.2.le), _root_.zpow_neg, _root_.zpow_natCast]
    have : N = i + (N - 1 - i + 1) := by have := i.2; omega
    generalize N - 1 - i + 1 = l at this ⊢
    have h2 : (q : ℝ) ^ N = q ^ (i : ℕ) * q ^ l := by rw [← pow_add, ← this]
    push_cast
    rw [h2]
    field_simp
  simp only [h1]
  rw [Fin.prod_univ_eq_prod_range
    (fun i => (q : ℝ) ^ N * (1 - (q : ℝ) ^ (-((N - 1 - i + 1 : ℕ) : ℤ)))) N,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul,
    Finset.prod_range_reflect (fun i => 1 - (q : ℝ) ^ (-((i + 1 : ℕ) : ℤ))) N, qE,
    ← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range]
  simp [add_comm]

section Levels

variable {O : Type} [CommRing O] [IsLocalRing O]

def bar {n : Type} [Fintype n] [DecidableEq n] (H : Subgroup (GL n O)) :
    Set (Matrix n n (IsLocalRing.ResidueField O)) := {B | ∃ h ∈ H, red h.val = B}

theorem exists_red {m n : Type} (B : Matrix m n (IsLocalRing.ResidueField O)) :
    ∃ A : Matrix m n O, red A = B := by
  choose A hA using fun i j => IsLocalRing.residue_surjective (B i j)
  exact ⟨Matrix.of A, by ext i j; exact hA i j⟩

theorem map_surjective (n : Type) [Fintype n] [DecidableEq n] :
    Function.Surjective (Matrix.GeneralLinearGroup.map (n := n) (IsLocalRing.residue O)) := by
  intro B
  obtain ⟨A, hA⟩ := exists_red B.val
  obtain ⟨u, hu⟩ := isUnit_of_red A (hA ▸ B.isUnit)
  refine ⟨u, Units.ext ?_⟩
  change red u.val = B.val
  rw [hu, hA]

theorem index_mul_card_bar {n : Type} [Fintype n] [DecidableEq n] {H : Subgroup (GL n O)}
    (hH : princ O n ≤ H) :
    H.index * Nat.card (bar H) = Nat.card (GL n (IsLocalRing.ResidueField O)) := by
  have e : bar H = Units.val ''
      ((H.map (Matrix.GeneralLinearGroup.map (n := n) (IsLocalRing.residue O)) :
        Subgroup (GL n (IsLocalRing.ResidueField O))) : Set (GL n (IsLocalRing.ResidueField O))) := by
    ext B
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact ⟨_, ⟨h, hh, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨h, hh, rfl⟩, rfl⟩
      exact ⟨h, hh, rfl⟩
  rw [e, Nat.card_image_of_injective Units.val_injective,
    ← Subgroup.index_map_eq H (map_surjective n) hH]
  exact Subgroup.index_mul_card _

end Levels

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem secondCountable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : SecondCountableTopology k := by
  letI := IsTopologicalAddGroup.rightUniformSpace k
  haveI := isUniformAddGroup_of_addCommGroup (G := k)
  letI : (Valued.v (R := k)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  open scoped Valued in
  haveI : ProperSpace k := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace k
  exact secondCountable_of_proper

theorem one_lt_resCard : 1 < resCard F := by
  have : 1 < Nat.card 𝓀[F] := Finite.one_lt_card
  unfold resCard
  exact_mod_cast this

def cell (c : 𝓀[F]) : Set F := {x | ∃ y : 𝒪[F], (y : F) = x ∧ IsLocalRing.residue 𝒪[F] y = c}

def pre {m n : Type} (S : Set (Matrix m n 𝓀[F])) : Set (m → n → F) :=
  {x | ∃ A : Matrix m n 𝒪[F], entries A = x ∧ red A ∈ S}

theorem cell_eq (y : 𝒪[F]) :
    cell (IsLocalRing.residue 𝒪[F] y) = (fun x => x + (-(y : F))) ⁻¹' cell (0 : 𝓀[F]) := by
  ext x
  constructor
  · rintro ⟨z, rfl, hz⟩
    exact ⟨z - y, by simp [sub_eq_add_neg], by rw [map_sub, hz, sub_self]⟩
  · rintro ⟨z, hz, h0⟩
    refine ⟨z + y, ?_, by rw [map_add (f := _), h0, zero_add]⟩
    push_cast
    rw [hz]; ring

theorem isClosed_cell (c : 𝓀[F]) : IsClosed (cell c) := by
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective c
  rw [cell_eq]
  refine IsClosed.preimage (by fun_prop) ?_
  have : cell (0 : 𝓀[F]) = Subtype.val '' (𝓂[F] : Set 𝒪[F]) := by
    ext x
    constructor
    · rintro ⟨z, rfl, hz⟩
      exact ⟨z, (IsLocalRing.residue_eq_zero_iff _).1 hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, rfl, (IsLocalRing.residue_eq_zero_iff _).2 hz⟩
  rw [this]
  have : T2Space F := by
    letI := IsTopologicalAddGroup.rightUniformSpace F
    haveI := isUniformAddGroup_of_addCommGroup (G := F)
    infer_instance
  exact ((IsNoetherianRing.isClosed_ideal 𝓂[F]).isCompact.image continuous_subtype_val).isClosed

theorem entries_injective {m n : Type} :
    Function.Injective (entries : Matrix m n 𝒪[F] → m → n → F) := fun A B h => by
  ext i j
  exact congrFun (congrFun h i) j

theorem pre_singleton {m n : Type} (B : Matrix m n 𝓀[F]) :
    pre {B} = Set.univ.pi fun i => Set.univ.pi fun j => cell (B i j) := by
  ext x
  constructor
  · rintro ⟨A, rfl, rfl⟩ i _ j _
    exact ⟨A i j, rfl, rfl⟩
  · intro h
    choose A hA hB using fun i j => h i trivial j trivial
    exact ⟨Matrix.of A, funext fun i => funext fun j => hA i j, by ext i j; exact hB i j⟩

theorem groupSet_eq {n : Type} [Fintype n] [DecidableEq n] {H : Subgroup (GL n 𝒪[F])}
    (hH : princ 𝒪[F] n ≤ H) : groupSet H = pre (bar H) := by
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k.val, rfl, k, hk, rfl⟩
  · rintro ⟨A, rfl, k, hk, h⟩
    obtain ⟨k', hk', e⟩ := exists_mem_of_red hH hk h.symm
    exact ⟨k', hk', by rw [e]⟩

variable [MeasurableSpace F] [BorelSpace F] (ν : Measure F) [ν.IsAddHaarMeasure]

theorem measure_cell (hν : ν (𝒪[F] : Set F) = 1) (c : 𝓀[F]) :
    ν (cell c) = (Nat.card 𝓀[F] : ENNReal)⁻¹ := by
  have hv : ∀ c : 𝓀[F], ν (cell c) = ν (cell (0 : 𝓀[F])) := fun c => by
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective c
    rw [cell_eq, measure_preimage_add_right]
  have hU : (𝒪[F] : Set F) = ⋃ c : 𝓀[F], cell c := by
    ext x
    simp only [Set.mem_iUnion]
    exact ⟨fun h => ⟨_, ⟨x, h⟩, rfl, rfl⟩, fun ⟨_, y, hy, _⟩ => hy ▸ y.2⟩
  have := Fintype.ofFinite 𝓀[F]
  rw [hU, measure_iUnion (fun u u' h => Set.disjoint_left.2 ?_)
    (fun u => (isClosed_cell u).measurableSet)] at hν
  · simp only [hv, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Nat.card_eq_fintype_card] at hν
    rw [hv]
    exact ENNReal.eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hν)
  · rintro _ ⟨y, rfl, rfl⟩ ⟨z, hz, rfl⟩
    exact h (by rw [Subtype.ext hz])

omit [ν.IsAddHaarMeasure] in
theorem measurableSet_pre_singleton {m n : Type} [Fintype m] [Fintype n] (B : Matrix m n 𝓀[F]) :
    MeasurableSet (pre {B}) := by
  rw [pre_singleton]
  exact MeasurableSet.univ_pi fun i => MeasurableSet.univ_pi fun j => (isClosed_cell _).measurableSet

theorem pre_eq_iUnion {m n : Type} (S : Set (Matrix m n 𝓀[F])) :
    pre S = ⋃ B : S, pre {B.val} := by
  ext x
  simp only [Set.mem_iUnion]
  exact ⟨fun ⟨A, h1, h2⟩ => ⟨⟨_, h2⟩, A, h1, rfl⟩, fun ⟨B, A, h1, h2⟩ => ⟨A, h1, by
    rw [Set.mem_singleton_iff.1 h2]; exact B.2⟩⟩

theorem measurableSet_pre {m n : Type} [Fintype m] [Fintype n] (S : Set (Matrix m n 𝓀[F])) :
    MeasurableSet (pre S) := by
  have : Finite (Matrix m n 𝓀[F]) := inferInstanceAs (Finite (m → n → 𝓀[F]))
  rw [pre_eq_iUnion]
  exact MeasurableSet.iUnion fun B => measurableSet_pre_singleton _

theorem measure_pre (hν : ν (𝒪[F] : Set F) = 1) {m n : Type} [Fintype m] [Fintype n]
    (S : Set (Matrix m n 𝓀[F])) :
    volAdd ν m n (pre S) =
      Nat.card S * (Nat.card 𝓀[F] : ENNReal)⁻¹ ^ (Fintype.card m * Fintype.card n) := by
  have : Finite (Matrix m n 𝓀[F]) := inferInstanceAs (Finite (m → n → 𝓀[F]))
  have := secondCountable F
  have := Fintype.ofFinite S
  have h1 : ∀ B : Matrix m n 𝓀[F], volAdd ν m n (pre {B}) =
      (Nat.card 𝓀[F] : ENNReal)⁻¹ ^ (Fintype.card m * Fintype.card n) := fun B => by
    rw [pre_singleton, volAdd, Measure.pi_pi]
    simp only [Measure.pi_pi, measure_cell ν hν, Finset.prod_const, Finset.card_univ]
    rw [← pow_mul, mul_comm]
  rw [pre_eq_iUnion, measure_iUnion (fun u u' h => Set.disjoint_left.2 ?_)
    (fun u => measurableSet_pre_singleton _)]
  · simp only [h1, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Nat.card_eq_fintype_card]
  · rintro _ ⟨A, rfl, hA⟩ ⟨B, hB, hB'⟩
    rw [entries_injective hB] at hB'
    exact h (Subtype.ext ((Set.mem_singleton_iff.1 hA).symm.trans hB'))

theorem measureReal_pre (hν : ν (𝒪[F] : Set F) = 1) {m n : Type} [Fintype m] [Fintype n]
    (S : Set (Matrix m n 𝓀[F])) :
    (volAdd ν m n).real (pre S) = Nat.card S / resCard F ^ (Fintype.card m * Fintype.card n) := by
  rw [Measure.real, measure_pre ν hν]
  simp [resCard, div_eq_mul_inv]

theorem volGroup_eq (hν : ν (𝒪[F] : Set F) = 1) {n : Type} [Fintype n] [DecidableEq n]
    {H : Subgroup (GL n 𝒪[F])} (hH : princ 𝒪[F] n ≤ H) :
    volGroup ν H = Nat.card (bar H) / resCard F ^ (Fintype.card n * Fintype.card n) := by
  rw [volGroup, groupSet_eq hH, measureReal_pre ν hν]

theorem index_mul_volGroup (hν : ν (𝒪[F] : Set F) = 1) {n : Type} [Fintype n] [DecidableEq n]
    {H : Subgroup (GL n 𝒪[F])} (hH : princ 𝒪[F] n ≤ H) :
    (H.index : ℝ) * volGroup ν H = qE (resCard F) 1 (Fintype.card n) := by
  have h := congrArg (Nat.cast : ℕ → ℝ) (index_mul_card_bar hH)
  rw [card_GL_real, Nat.cast_mul] at h
  have hq : 0 < resCard F := lt_trans one_pos one_lt_resCard
  rw [volGroup_eq ν hν hH, ← mul_div_assoc, h]
  change resCard F ^ _ * qE (resCard F) _ _ / _ = _
  field_simp

theorem volumeOfGL (hν : ν (𝒪[F] : Set F) = 1) : VolumeOfGL ν := by
  intro n _ _
  have := index_mul_volGroup ν hν (le_top : princ 𝒪[F] n ≤ ⊤)
  simpa using this

end Local

end GlobalTheory.IndexVolume
