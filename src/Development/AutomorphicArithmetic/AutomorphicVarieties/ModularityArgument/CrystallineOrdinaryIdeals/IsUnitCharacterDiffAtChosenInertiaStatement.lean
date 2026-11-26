module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.GaloisSubgroupLBasicProperties

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.IsUnitCharacterDiffAtChosenInertiaStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_characterDiff_at_chosenInertia : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B], (∀ a b : Fin 3, a ≠ b → IsUnit (algebraMap O B (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a (GlobalTheory.OrdLoc.s0 D)) - algebraMap O B (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ b (GlobalTheory.OrdLoc.s0 D)))) ∧ ∀ a, IsUnit (algebraMap O B (GlobalTheory.OrdLoc.cc D a)) := by
  intro l _ O _ _ _ _ _ _ _ D B _ _ _ _ _ _
  obtain ⟨-, -, -, hΨ, hs0⟩ := GlobalTheory.T.galoisSubgroupL_basic_properties D
  rw [UpperTheory.V.Loc.Dat3.IsInertiaInfiniteCyclotomic.eq_1] at hs0
  obtain ⟨hH, hI, hc⟩ := hs0
  have key : ∀ a : Fin 3, UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a D.s0 =
      algebraMap ℤ_[l] O ((cyc l l D.s0 ^ ((D.e : ℤ) * wt1 a) : ℤ_[l]ˣ) : ℤ_[l]) := by
    intro a
    rw [UpperTheory.V.UnitaryThreeInertia.psi.eq_1, hΨ _ hH hI, cycA.eq_1, MonoidHom.comp_apply, ← map_pow, ← map_zpow,
      Units.coe_map, zpow_mul, zpow_natCast]
    rfl
  have unitQ : ∀ z : ℤ_[l], z ≠ 0 → IsUnit (algebraMap ℤ_[l] B z) := by
    intro z hz
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] B]
    apply IsUnit.map
    apply Ne.isUnit
    simpa using hz
  have expo : ∀ a b : Fin 3, a ≠ b → (D.e : ℤ) * wt1 a ≠ (D.e : ℤ) * wt1 b := by
    intro a b hab hw
    apply hab
    have he0 : (D.e : ℤ) ≠ 0 := by
      have : (1 : ℤ) ≤ D.e := by exact_mod_cast D.e_pos
      omega
    have hw' := mul_left_cancel₀ he0 hw
    rw [wt1.eq_1, wt1.eq_1] at hw'
    apply Fin.ext
    omega
  have ne : ∀ m n : ℤ, m ≠ n →
      ((cyc l l D.s0 ^ m : ℤ_[l]ˣ) : ℤ_[l]) - ((cyc l l D.s0 ^ n : ℤ_[l]ˣ) : ℤ_[l]) ≠ 0 := by
    intro m n hmn hz
    apply hc
    rw [isOfFinOrder_iff_zpow_eq_one]
    refine ⟨m - n, sub_ne_zero.mpr hmn, ?_⟩
    have hu : cyc l l D.s0 ^ m = cyc l l D.s0 ^ n := Units.ext (sub_eq_zero.mp hz)
    rw [zpow_sub, hu, mul_inv_cancel]
  have diff : ∀ a b : Fin 3, a ≠ b → IsUnit (algebraMap O B (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a D.s0) -
      algebraMap O B (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ b D.s0)) := by
    intro a b hab
    rw [key a, key b, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, ← map_sub]
    exact unitQ _ (ne _ _ (expo a b hab))
  refine ⟨diff, ?_⟩
  intro a
  rw [UpperTheory.V.Loc.Dat3.cc.eq_1, map_mul, map_sub, map_sub]
  refine IsUnit.mul (diff a (a + 1) ?_) (diff a (a + 2) ?_)
  · fin_cases a <;> decide
  · fin_cases a <;> decide
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.OrdinaryIdealSaturatorsConjInvariant
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.OrdinaryIdealSaturatorsConjInvariant
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.OrdLoc

theorem conjBy_left {G C : Type} [Group G] [CommRing C] (h : GL (Fin 3) C)
    (r : G →* UpperTheory.V.U3.GG (m := 3) (R := C)) (g : G)
    (hg : (r g).right = 1) : (conjBy h r g).left = h * (r g).left * h⁻¹ := by
  show (GG.ofGL h * r g * (GG.ofGL h)⁻¹).left = _
  rw [SemidirectProduct.mul_left, SemidirectProduct.mul_left, SemidirectProduct.inv_left]
  simp only [SemidirectProduct.right_inl, SemidirectProduct.left_inl, SemidirectProduct.mul_right, hg, mul_one, inv_one, map_one, MulAut.one_apply]

theorem conjBy_mat {G C : Type} [Group G] [CommRing C] (h : GL (Fin 3) C)
    (r : G →* UpperTheory.V.U3.GG (m := 3) (R := C)) (g : G)
    (hg : (r g).right = 1) :
    (conjBy h r g).mat = (h : Matrix (Fin 3) (Fin 3) C) * (r g).mat * ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) := by
  unfold GG.mat
  rw [conjBy_left h r g hg, Units.val_mul, Units.val_mul]

section Conj

variable {C : Type} [CommRing C]

theorem ent_mem_mul {J : Ideal C} {N : Matrix (Fin 3) (Fin 3) C} (hN : ∀ i j, N i j ∈ J)
    (A B : Matrix (Fin 3) (Fin 3) C) (i j : Fin 3) : (A * N * B) i j ∈ J := by
  simp only [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _
    (Ideal.sum_mem _ fun m _ => Ideal.mul_mem_left _ _ (hN m k))

theorem conj_sub_scalar (h : GL (Fin 3) C) (M : Matrix (Fin 3) (Fin 3) C) (c : C) :
    (h : Matrix (Fin 3) (Fin 3) C) * M * ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) - Matrix.scalar _ c =
      (h : Matrix (Fin 3) (Fin 3) C) * (M - Matrix.scalar _ c) * ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) := by
  have e : (h : Matrix (Fin 3) (Fin 3) C) * ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [Matrix.mul_sub, Matrix.sub_mul, ← (Matrix.scalar_commute c (fun _ => Commute.all _ _) (h : Matrix (Fin 3) (Fin 3) C)),
    Matrix.mul_assoc (Matrix.scalar _ c), e, Matrix.mul_one]

theorem conj_mul_three_alt (h : GL (Fin 3) C) (A B E : Matrix (Fin 3) (Fin 3) C) :
    ((h : Matrix (Fin 3) (Fin 3) C) * A * ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C)) *
      ((h : Matrix (Fin 3) (Fin 3) C) * B * ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C)) *
      ((h : Matrix (Fin 3) (Fin 3) C) * E * ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C)) =
      (h : Matrix (Fin 3) (Fin 3) C) * (A * B * E) * ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) := by
  have e : ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) * (h : Matrix (Fin 3) (Fin 3) C) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) (h : Matrix (Fin 3) (Fin 3) C), e, Matrix.one_mul,
    ← Matrix.mul_assoc ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) (h : Matrix (Fin 3) (Fin 3) C), e, Matrix.one_mul]

theorem unconj (h : GL (Fin 3) C) (M : Matrix (Fin 3) (Fin 3) C) :
    M = ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) *
      ((h : Matrix (Fin 3) (Fin 3) C) * M * ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C)) * (h : Matrix (Fin 3) (Fin 3) C) := by
  have e : ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) * (h : Matrix (Fin 3) (Fin 3) C) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  simp only [Matrix.mul_assoc]
  rw [e, Matrix.mul_one, ← Matrix.mul_assoc, e, Matrix.one_mul]

theorem trace_conj (h : GL (Fin 3) C) (M : Matrix (Fin 3) (Fin 3) C) :
    ((h : Matrix (Fin 3) (Fin 3) C) * M * ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C)).trace = M.trace := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]

theorem charpoly_conj (h : GL (Fin 3) C) (M : Matrix (Fin 3) (Fin 3) C) :
    ((h : Matrix (Fin 3) (Fin 3) C) * M * ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C)).charpoly = M.charpoly := by
  rw [Matrix.coe_units_inv]
  exact Matrix.charpoly_units_conj h M

end Conj

end GlobalTheory.OrdLoc

namespace GlobalTheory.OrdLoc

end GlobalTheory.OrdLoc
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.OrdinaryIdealSaturatorsConjInvariantStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ordinaryIdeal_saturators_conj_invariant :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
      (D : Dat3 l O) {C : Type} [CommRing C] [Algebra O C]
      (r : GQ l →* GG (m := 3) (R := C)) (h : GL (Fin 3) C), HasMult D.η r →
      D.ordIdeal (conjBy h r) = D.ordIdeal r ∧
        (∀ a, D.dd (conjBy h r) a = D.dd r a) ∧ D.del (conjBy h r) = D.del r := by
  intro l _ O _ _ _ D C _ _ r h hr
  have hone : ∀ s ∈ D.HL, (r s).right = 1 := by
    intro s hs
    rw [hr s]
    exact MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 hs).1
  have hmat (s : GQ l) (hs : s ∈ D.HL) :
      (conjBy h r s).mat =
        (h : Matrix (Fin 3) (Fin 3) C) * (r s).mat *
          ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) := by
    have hleft : (conjBy h r s).left = h * (r s).left * h⁻¹ := by
      show (GG.ofGL h * r s * (GG.ofGL h)⁻¹).left = _
      rw [SemidirectProduct.mul_left, SemidirectProduct.mul_left, SemidirectProduct.inv_left]
      simp only [SemidirectProduct.right_inl, SemidirectProduct.left_inl, SemidirectProduct.mul_right,
        hone s hs, mul_one, inv_one, map_one, MulAut.one_apply]
    unfold GG.mat
    rw [hleft, Units.val_mul, Units.val_mul]
  have hsh : ∀ s ∈ D.HL, ∀ a, D.sh (conjBy h r) a s =
      (h : Matrix (Fin 3) (Fin 3) C) * D.sh r a s * ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) := by
    intro s hs a
    simp only [UpperTheory.V.Loc.Dat3.sh]
    rw [hmat s hs, GlobalTheory.OrdLoc.conj_sub_scalar]
  have hHLopen : IsOpen (D.HL : Set (GQ l)) := GlobalTheory.OrdLoc.hl_isOpen' D
  have hs0 : D.s0 ∈ D.HL := by
    obtain ⟨s, ⟨hs, hi⟩, hcyc⟩ := ((cycInertia l).2 D.HL hHLopen).2
    have hex : ∃ s, D.IsInertiaInfiniteCyclotomic s := ⟨s, hs, hi, hcyc⟩
    exact (Classical.epsilon_spec hex).1
  have hex : ∃ σ, D.IsFr σ := by
    have : D.HL.Normal := GlobalTheory.OrdLoc.hl_normal' D
    obtain ⟨hIn, -, -, ⟨σ₀, hσ₀⟩, -⟩ := iqBasic l
    have : (Iq l).Normal := hIn
    have : D.HL.FiniteIndex := GlobalTheory.OrdLoc.finiteIndex_of_open' ⟨D.HL, hHLopen⟩
    let N : Subgroup (GQ l) := D.HL ⊔ Iq l
    have : N.FiniteIndex := Subgroup.finiteIndex_of_le (show D.HL ≤ N from le_sup_left)
    have : N.Normal := Subgroup.sup_normal _ _
    let q : GQ l ⧸ N := (σ₀ : GQ l ⧸ N)
    let m := orderOf q
    have hmN : σ₀ ^ m ∈ N := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
      exact pow_orderOf_eq_one q
    obtain ⟨σ, hσ, i₀, hi₀, hpow⟩ := Subgroup.mem_sup_of_normal_right.1 hmN
    let φ := QuotientGroup.mk' (Iq l)
    have hφ : ∀ {x}, φ x = 1 ↔ x ∈ Iq l := fun {x} => QuotientGroup.eq_one_iff x
    have hφm : φ σ₀ ^ m = φ σ := by
      rw [← map_pow, ← hpow, map_mul, hφ.2 hi₀, mul_one]
    refine ⟨σ, ⟨hσ, ?_⟩, σ₀, m, hσ₀, orderOf_pos q, ?_⟩
    · rw [eq_top_iff]
      intro g _
      rw [← SetLike.mem_coe, Subgroup.topologicalClosure_coe, mem_closure_iff]
      intro U hU hgU
      have hV : IsOpen (D.HL.subtype '' U) :=
        hHLopen.isOpenEmbedding_subtypeVal.isOpenMap U hU
      have hcl : (g : GQ l) ∈ closure ((Iq l ⊔ Subgroup.zpowers σ₀ : Subgroup (GQ l)) :
          Set (GQ l)) := by
        rw [← Subgroup.topologicalClosure_coe, frobDense σ₀ hσ₀]
        trivial
      obtain ⟨x, ⟨u, huU, rfl⟩, hx⟩ := mem_closure_iff.1 hcl _ hV ⟨g, hgU, rfl⟩
      obtain ⟨i, hi, z, hz, hiz⟩ := Subgroup.mem_sup_of_normal_left.1 hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
      change i * σ₀ ^ k = (u : GQ l) at hiz
      have hkN : σ₀ ^ k ∈ N := by
        have e : σ₀ ^ k = i⁻¹ * (u : GQ l) := by rw [← hiz]; group
        rw [e]
        exact N.mul_mem (Subgroup.mem_sup_right (Subgroup.inv_mem _ hi)) (Subgroup.mem_sup_left u.2)
      have hdvd : (m : ℤ) ∣ k := by
        change (orderOf q : ℤ) ∣ k
        rw [orderOf_dvd_iff_zpow_eq_one, ← QuotientGroup.mk_zpow, QuotientGroup.eq_one_iff]
        exact hkN
      obtain ⟨j, rfl⟩ := hdvd
      have hφu : φ (u : GQ l) = φ σ ^ j := by
        rw [← hiz, map_mul, hφ.2 hi, one_mul, map_zpow, zpow_mul, zpow_natCast, hφm]
      have hy : (u : GQ l) * σ ^ (-j) ∈ Iq l := by
        rw [← hφ, map_mul, map_zpow, hφu, zpow_neg, mul_inv_cancel]
      refine ⟨u, huU, ?_⟩
      let y : D.HL := ⟨(u : GQ l) * σ ^ (-j), D.HL.mul_mem u.2 (D.HL.zpow_mem hσ _)⟩
      have e : u = y * (⟨σ, hσ⟩ : D.HL) ^ j := by
        ext
        simp [y]
      rw [SetLike.mem_coe, e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hy)
        (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers _ _))
    · rw [← hpow]
      simpa using Subgroup.inv_mem _ hi₀
  have hfrSpec : D.IsFr D.fr := Classical.epsilon_spec hex
  obtain ⟨hfr, -⟩ := hfrSpec.1
  have htr : ∀ a, D.tr (conjBy h r) a = D.tr r a := by
    intro a
    simp only [UpperTheory.V.Loc.Dat3.tr]
    rw [hsh _ hs0, hsh _ hs0, hmat _ hfr, GlobalTheory.OrdLoc.conj_mul_three_alt, GlobalTheory.OrdLoc.trace_conj]
  have hdd : ∀ a, D.dd (conjBy h r) a = D.dd r a := by
    intro a
    simp only [UpperTheory.V.Loc.Dat3.dd, htr]
  have hprod : ∀ t : Fin 3 → GQ l, (∀ a, t a ∈ D.HL ⊓ Iq l) →
      D.sh (conjBy h r) 0 (t 0) * D.sh (conjBy h r) 1 (t 1) * D.sh (conjBy h r) 2 (t 2) =
        (h : Matrix (Fin 3) (Fin 3) C) * (D.sh r 0 (t 0) * D.sh r 1 (t 1) * D.sh r 2 (t 2)) *
          ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) := by
    intro t ht
    rw [hsh _ (Subgroup.mem_inf.1 (ht 0)).1, hsh _ (Subgroup.mem_inf.1 (ht 1)).1,
      hsh _ (Subgroup.mem_inf.1 (ht 2)).1, GlobalTheory.OrdLoc.conj_mul_three_alt]
  refine ⟨?_, hdd, by simp only [UpperTheory.V.Loc.Dat3.del, hdd]⟩
  unfold UpperTheory.V.Loc.Dat3.ordIdeal
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro x (⟨s, hs, i, rfl⟩ | ⟨t, ht, i, j, rfl⟩)
    · exact Ideal.subset_span
        (Or.inl ⟨s, hs, i, by rw [hmat s (Subgroup.mem_inf.1 hs).1, GlobalTheory.OrdLoc.charpoly_conj]⟩)
    · rw [hprod t ht]
      apply GlobalTheory.OrdLoc.ent_mem_mul
      intro a b
      exact Ideal.subset_span (Or.inr ⟨t, ht, a, b, rfl⟩)
  · rw [Ideal.span_le]
    rintro x (⟨s, hs, i, rfl⟩ | ⟨t, ht, i, j, rfl⟩)
    · exact Ideal.subset_span
        (Or.inl ⟨s, hs, i, by rw [hmat s (Subgroup.mem_inf.1 hs).1, GlobalTheory.OrdLoc.charpoly_conj]⟩)
    · rw [GlobalTheory.OrdLoc.unconj h (D.sh r 0 (t 0) * D.sh r 1 (t 1) * D.sh r 2 (t 2)), ← hprod t ht]
      apply GlobalTheory.OrdLoc.ent_mem_mul
      intro a b
      exact Ideal.subset_span (Or.inr ⟨t, ht, a, b, rfl⟩)
end
end
