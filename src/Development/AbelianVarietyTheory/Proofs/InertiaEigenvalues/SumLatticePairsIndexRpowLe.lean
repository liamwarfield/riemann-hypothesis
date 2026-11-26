module

public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthCommensurableSpanSpanOfDetNeZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AntitoneFiltrationExistsAdaptedLinearIndepSet

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumSublatticeIndexRpowLeSolomon
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumSublatticeIndexRpowLeSolomon
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory.SubZeta

theorem index_eq_mul_of_exact {G A B : Type*} [AddCommGroup G] [AddCommGroup A] [AddCommGroup B]
    (π : G →+ A) (hπ : Function.Surjective π) (ι : B →+ G) (hι : ι.range = π.ker)
    (H : AddSubgroup G) : H.index = (H.map π).index * (H.comap ι).index := by
  have h1 : (H.map π).index = (H ⊔ π.ker).index := by
    rw [← AddSubgroup.index_comap_of_surjective (H := H.map π) hπ, AddSubgroup.comap_map_eq]
  have h2 : (H.comap ι).index = H.relIndex π.ker := by
    rw [AddSubgroup.index_comap, hι]
  rw [h1, h2, ← AddSubgroup.relIndex_sup_left, mul_comm, AddSubgroup.relIndex_mul_index le_sup_left]

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem index_span_pow {ϖ : O} (hϖ : Irreducible ϖ) (n : ℕ) :
    (Ideal.span {ϖ ^ n} : Ideal O).toAddSubgroup.index =
      Nat.card (IsLocalRing.ResidueField O) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hle : (Ideal.span {ϖ ^ (n+1)} : Ideal O).toAddSubgroup ≤
        (Ideal.span {ϖ ^ n} : Ideal O).toAddSubgroup := by
      intro x hx
      exact (Ideal.span_singleton_le_span_singleton.mpr (Dvd.intro _ (pow_succ ϖ n).symm)) hx
    rw [← AddSubgroup.relIndex_mul_index hle, ih, pow_succ (Nat.card (IsLocalRing.ResidueField O)) n, mul_comm]
    congr 1
    let f : O →+ O := AddMonoidHom.mulLeft (ϖ ^ n)
    have hr : f.range = (Ideal.span {ϖ ^ n} : Ideal O).toAddSubgroup := by
      ext x
      simp [f, Ideal.mem_span_singleton', mul_comm]
    rw [← hr, ← AddSubgroup.index_comap]
    have hc : (Ideal.span {ϖ ^ (n+1)} : Ideal O).toAddSubgroup.comap f =
        (IsLocalRing.maximalIdeal O).toAddSubgroup := by
      ext x
      simp only [AddSubgroup.mem_comap, Submodule.mem_toAddSubgroup, f, AddMonoidHom.coe_mulLeft]
      rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.mem_span_singleton,
        Ideal.mem_span_singleton, pow_succ, mul_dvd_mul_iff_left (pow_ne_zero _ hϖ.ne_zero)]
    rw [hc]
    rfl

end GlobalTheory.SubZeta

namespace GlobalTheory.SubZeta

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem infinite_of_dvr : Infinite O := by
  by_contra h
  rw [not_infinite_iff_finite] at h
  exact IsDiscreteValuationRing.not_isField O (Finite.isField_of_domain O)

theorem sum_ideal_le [Finite (IsLocalRing.ResidueField O)] (σ : ℝ) (hσ : 0 < σ) (D : Finset (Ideal O))
    (hD : ∀ I ∈ D, I.toAddSubgroup.index ≠ 0) :
    ∑ I ∈ D, (I.toAddSubgroup.index : ℝ) ^ (-σ) ≤
      (1 - (Nat.card (IsLocalRing.ResidueField O) : ℝ) ^ (-σ))⁻¹ := by
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hq : (1 : ℝ) < (Nat.card (IsLocalRing.ResidueField O) : ℝ) := by
    exact_mod_cast Finite.one_lt_card
  have hne : ∀ I ∈ D, I ≠ ⊥ := by
    intro I hI h
    apply hD I hI
    rw [h, Submodule.bot_toAddSubgroup, AddSubgroup.index_bot]
    haveI := infinite_of_dvr (O := O)
    exact Nat.card_eq_zero_of_infinite
  choose! e he using fun I hI => IsDiscreteValuationRing.ideal_eq_span_pow_irreducible (hne I hI) hϖ
  have hinj : Set.InjOn e D := fun I hI J hJ h => by rw [he I hI, he J hJ, h]
  set q : ℝ := (Nat.card (IsLocalRing.ResidueField O) : ℝ) with hqdef
  have hq0 : 0 < q := by linarith
  have hval : ∀ I ∈ D, (I.toAddSubgroup.index : ℝ) ^ (-σ) = (q ^ (-σ)) ^ e I := by
    intro I hI
    have hidx : I.toAddSubgroup.index = Nat.card (IsLocalRing.ResidueField O) ^ e I := by
      conv_lhs => rw [he I hI]
      exact index_span_pow hϖ _
    rw [hidx, Nat.cast_pow, ← hqdef, ← Real.rpow_natCast q, ← Real.rpow_mul hq0.le,
      ← Real.rpow_natCast (q ^ (-σ)), ← Real.rpow_mul hq0.le, mul_comm]
  rw [Finset.sum_congr rfl hval, ← Finset.sum_image (f := fun n : ℕ => (q ^ (-σ)) ^ n) hinj]
  have hx0 : 0 ≤ q ^ (-σ) := (Real.rpow_pos_of_pos hq0 _).le
  have hx1 : q ^ (-σ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)
  rw [← tsum_geometric_of_lt_one hx0 hx1]
  exact Summable.sum_le_tsum _ (fun i _ => pow_nonneg hx0 i) (summable_geometric_of_lt_one hx0 hx1)

def headL (r : ℕ) : (Fin (r+1) → O) →ₗ[O] O := LinearMap.proj (R := O) (φ := fun _ => O) 0

theorem headL_apply (r : ℕ) (x : Fin (r+1) → O) : headL r x = x 0 := rfl

def consL (r : ℕ) : (Fin r → O) →ₗ[O] (Fin (r+1) → O) where
  toFun y := Fin.cons 0 y
  map_add' y z := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_smul' c y := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem consL_apply (r : ℕ) (y : Fin r → O) : consL r y = Fin.cons 0 y := rfl

theorem index_split {r : ℕ} (M : Submodule O (Fin (r+1) → O)) :
    M.toAddSubgroup.index =
      (M.map (headL r)).toAddSubgroup.index * (M.comap (consL r)).toAddSubgroup.index := by
  have hπ : Function.Surjective (headL (O := O) r).toAddMonoidHom :=
    fun a => ⟨Fin.cons a 0, by simp [headL_apply]⟩
  have hι : (consL (O := O) r).toAddMonoidHom.range = (headL (O := O) r).toAddMonoidHom.ker := by
    ext x
    simp only [AddMonoidHom.mem_range, AddMonoidHom.mem_ker, LinearMap.toAddMonoidHom_coe,
      headL_apply, consL_apply]
    constructor
    · rintro ⟨y, rfl⟩
      simp
    · intro h
      exact ⟨Fin.tail x, by rw [← h]; exact Fin.cons_self_tail x⟩
  have := index_eq_mul_of_exact _ hπ _ hι M.toAddSubgroup
  rw [this]
  congr 2
  all_goals (ext x; simp)

theorem le_of_lift {r : ℕ} (M1 M2 : Submodule O (Fin (r+1) → O)) (g : O)
    (hI : M1.map (headL r) ≤ Ideal.span {g}) (hc : M1.comap (consL r) ≤ M2.comap (consL r))
    (w1 w2 : Fin (r+1) → O) (hw1 : w1 ∈ M1) (hw2 : w2 ∈ M2) (h1 : w1 0 = g) (h2 : w2 0 = g)
    (hd : Fin.tail w1 - Fin.tail w2 ∈ M2.comap (consL r)) : M1 ≤ M2 := by
  intro x hx
  have hx0 : x 0 ∈ Ideal.span {g} := hI (Submodule.mem_map_of_mem hx)
  obtain ⟨c, hc'⟩ := Ideal.mem_span_singleton'.mp hx0
  have hA : Fin.tail x - c • Fin.tail w1 ∈ M2.comap (consL r) := by
    apply hc
    rw [Submodule.mem_comap]
    have : consL r (Fin.tail x - c • Fin.tail w1) = x - c • w1 := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [consL_apply, h1, hc']
      · simp [consL_apply, Fin.tail]
    rw [this]
    exact M1.sub_mem hx (M1.smul_mem c hw1)
  have key : x = consL r (Fin.tail x - c • Fin.tail w1) + c • consL r (Fin.tail w1 - Fin.tail w2)
      + c • w2 := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [consL_apply, h2, hc']
    · simp only [consL_apply, Fin.tail, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Fin.cons_succ,
        smul_eq_mul]
      ring
  rw [key]
  exact M2.add_mem (M2.add_mem hA (M2.smul_mem c hd)) (M2.smul_mem c hw2)

end GlobalTheory.SubZeta

namespace GlobalTheory.SubZeta

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem fiber_card_le {r : ℕ} (I : Ideal O) (M' : Submodule O (Fin r → O))
    (hM' : M'.toAddSubgroup.index ≠ 0) (S : Finset (Submodule O (Fin (r+1) → O)))
    (hS : ∀ M ∈ S, M.map (headL r) = I ∧ M.comap (consL r) = M') :
    S.card ≤ M'.toAddSubgroup.index := by
  classical
  obtain ⟨g, hg⟩ : ∃ g, I = Ideal.span {g} :=
    ⟨_, (Submodule.IsPrincipal.span_singleton_generator I).symm⟩
  have hex : ∀ M ∈ S, ∃ w ∈ M, w 0 = g := by
    intro M hM
    have : g ∈ M.map (headL r) := by
      rw [(hS M hM).1, hg]
      exact Ideal.mem_span_singleton_self g
    obtain ⟨w, hw, hw0⟩ := Submodule.mem_map.mp this
    exact ⟨w, hw, hw0⟩
  choose! w hwM hw0 using hex
  haveI : Finite ((Fin r → O) ⧸ M'.toAddSubgroup) := Nat.finite_of_card_ne_zero hM'
  haveI := Fintype.ofFinite ((Fin r → O) ⧸ M'.toAddSubgroup)
  have hinj : Set.InjOn (fun M => (QuotientAddGroup.mk (Fin.tail (w M)) :
      (Fin r → O) ⧸ M'.toAddSubgroup)) S := by
    intro M1 h1 M2 h2 heq
    have hd : -Fin.tail (w M1) + Fin.tail (w M2) ∈ M' := (QuotientAddGroup.eq).mp heq
    have hd1 : Fin.tail (w M1) - Fin.tail (w M2) ∈ M' := by
      have := M'.neg_mem hd
      rwa [neg_add, neg_neg, ← sub_eq_add_neg] at this
    have hd2 : Fin.tail (w M2) - Fin.tail (w M1) ∈ M' := by
      rwa [neg_add_eq_sub] at hd
    apply le_antisymm
    · refine le_of_lift M1 M2 g ?_ ?_ _ _ (hwM M1 h1) (hwM M2 h2) (hw0 M1 h1) (hw0 M2 h2) ?_
      · rw [(hS M1 h1).1, hg]
      · rw [(hS M1 h1).2, (hS M2 h2).2]
      · rw [(hS M2 h2).2]; exact hd1
    · refine le_of_lift M2 M1 g ?_ ?_ _ _ (hwM M2 h2) (hwM M1 h1) (hw0 M2 h2) (hw0 M1 h1) ?_
      · rw [(hS M2 h2).1, hg]
      · rw [(hS M1 h1).2, (hS M2 h2).2]
      · rw [(hS M1 h1).2]; exact hd2
  calc S.card ≤ (Finset.univ : Finset ((Fin r → O) ⧸ M'.toAddSubgroup)).card :=
        Finset.card_le_card_of_injOn _ (fun _ _ => Finset.mem_univ _) hinj
    _ = M'.toAddSubgroup.index := by
        rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
        rfl

theorem main_bound [Finite (IsLocalRing.ResidueField O)] : ∀ (r : ℕ) (σ : ℝ), (r : ℝ) - 1 < σ →
    ∀ C : Finset (Submodule O (Fin r → O)), (∀ M ∈ C, M.toAddSubgroup.index ≠ 0) →
    ∑ M ∈ C, (M.toAddSubgroup.index : ℝ) ^ (-σ) ≤
      ∏ i ∈ Finset.range r, (1 - (Nat.card (IsLocalRing.ResidueField O) : ℝ) ^ ((i : ℝ) - σ))⁻¹ := by
  classical
  intro r
  induction r with
  | zero =>
    intro σ _ C _
    have hC : C ⊆ {⊤} := fun M _ => Finset.mem_singleton.mpr (Subsingleton.elim _ _)
    calc ∑ M ∈ C, (M.toAddSubgroup.index : ℝ) ^ (-σ)
        ≤ ∑ M ∈ ({⊤} : Finset (Submodule O (Fin 0 → O))), (M.toAddSubgroup.index : ℝ) ^ (-σ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hC (fun _ _ _ => by positivity)
      _ = ∏ i ∈ Finset.range 0,
            (1 - (Nat.card (IsLocalRing.ResidueField O) : ℝ) ^ ((i : ℝ) - σ))⁻¹ := by simp
  | succ r ih =>
    intro σ hσ C hC
    set q : ℝ := (Nat.card (IsLocalRing.ResidueField O) : ℝ) with hqdef
    have hσ' : (r : ℝ) - 1 < σ - 1 := by push_cast at hσ; linarith
    have hσ0 : 0 < σ := by
      have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
      push_cast at hσ; linarith
    let p : Submodule O (Fin (r+1) → O) → Ideal O × Submodule O (Fin r → O) :=
      fun M => (M.map (headL r), M.comap (consL r))
    have hidx : ∀ M : Submodule O (Fin (r+1) → O), M.toAddSubgroup.index =
        (p M).1.toAddSubgroup.index * (p M).2.toAddSubgroup.index := fun M => index_split M
    have hC1 : ∀ x ∈ C.image p, x.1.toAddSubgroup.index ≠ 0 ∧ x.2.toAddSubgroup.index ≠ 0 := by
      intro x hx
      obtain ⟨M, hM, rfl⟩ := Finset.mem_image.mp hx
      have := hC M hM
      rw [hidx] at this
      exact ⟨left_ne_zero_of_mul this, right_ne_zero_of_mul this⟩
    set D1 := (C.image p).image Prod.fst
    set D2 := (C.image p).image Prod.snd
    have hD1 : ∀ I ∈ D1, I.toAddSubgroup.index ≠ 0 := by
      intro I hI
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hI
      exact (hC1 x hx).1
    have hD2 : ∀ N ∈ D2, N.toAddSubgroup.index ≠ 0 := by
      intro N hN
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hN
      exact (hC1 x hx).2
    have hq1 : (1 : ℝ) < q := by
      have := Finite.one_lt_card (α := IsLocalRing.ResidueField O)
      rw [hqdef]
      exact_mod_cast this
    have hx1 : q ^ (-σ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq1 (by linarith)
    calc ∑ M ∈ C, (M.toAddSubgroup.index : ℝ) ^ (-σ)
        = ∑ x ∈ C.image p, ∑ M ∈ C with p M = x, (M.toAddSubgroup.index : ℝ) ^ (-σ) :=
          (Finset.sum_fiberwise_of_maps_to (fun M hM => Finset.mem_image_of_mem p hM) _).symm
      _ ≤ ∑ x ∈ C.image p, (x.1.toAddSubgroup.index : ℝ) ^ (-σ) *
            (x.2.toAddSubgroup.index : ℝ) ^ (-(σ - 1)) := by
          apply Finset.sum_le_sum
          intro x hx
          have hterm : ∀ M ∈ C.filter (fun M => p M = x), (M.toAddSubgroup.index : ℝ) ^ (-σ) =
              (x.1.toAddSubgroup.index : ℝ) ^ (-σ) * (x.2.toAddSubgroup.index : ℝ) ^ (-σ) := by
            intro M hM
            rw [Finset.mem_filter] at hM
            rw [hidx M, hM.2, Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity)]
          rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
          have hcard : ((C.filter (fun M => p M = x)).card : ℝ) ≤ x.2.toAddSubgroup.index := by
            exact_mod_cast fiber_card_le x.1 x.2 (hC1 x hx).2 _ (fun M hM => by
              rw [Finset.mem_filter] at hM
              rw [← hM.2]
              exact ⟨rfl, rfl⟩)
          have hpos2 : (0 : ℝ) < x.2.toAddSubgroup.index := by
            exact_mod_cast Nat.pos_of_ne_zero (hC1 x hx).2
          have hsplit : (x.2.toAddSubgroup.index : ℝ) ^ (-(σ - 1)) =
              x.2.toAddSubgroup.index * (x.2.toAddSubgroup.index : ℝ) ^ (-σ) := by
            rw [show -(σ - 1) = 1 + -σ by ring, Real.rpow_add hpos2, Real.rpow_one]
          rw [hsplit]
          have ha : (0 : ℝ) ≤ (x.1.toAddSubgroup.index : ℝ) ^ (-σ) := by positivity
          have hb : (0 : ℝ) ≤ (x.2.toAddSubgroup.index : ℝ) ^ (-σ) := by positivity
          calc ((C.filter (fun M => p M = x)).card : ℝ) *
                ((x.1.toAddSubgroup.index : ℝ) ^ (-σ) * (x.2.toAddSubgroup.index : ℝ) ^ (-σ))
              = (x.1.toAddSubgroup.index : ℝ) ^ (-σ) *
                  (((C.filter (fun M => p M = x)).card : ℝ) * (x.2.toAddSubgroup.index : ℝ) ^ (-σ)) := by
                ring
            _ ≤ (x.1.toAddSubgroup.index : ℝ) ^ (-σ) *
                  ((x.2.toAddSubgroup.index : ℝ) * (x.2.toAddSubgroup.index : ℝ) ^ (-σ)) := by
                gcongr
      _ ≤ ∑ x ∈ D1 ×ˢ D2, (x.1.toAddSubgroup.index : ℝ) ^ (-σ) *
            (x.2.toAddSubgroup.index : ℝ) ^ (-(σ - 1)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro x hx
            exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hx, Finset.mem_image_of_mem _ hx⟩
          · intro _ _ _
            positivity
      _ = (∑ I ∈ D1, (I.toAddSubgroup.index : ℝ) ^ (-σ)) *
            ∑ N ∈ D2, (N.toAddSubgroup.index : ℝ) ^ (-(σ - 1)) := by
          rw [Finset.sum_mul_sum, Finset.sum_product]
      _ ≤ (1 - q ^ (-σ))⁻¹ * ∏ i ∈ Finset.range r, (1 - q ^ ((i : ℝ) - (σ - 1)))⁻¹ := by
          apply mul_le_mul (sum_ideal_le σ hσ0 D1 hD1) (ih (σ - 1) hσ' D2 hD2)
          · exact Finset.sum_nonneg (fun _ _ => by positivity)
          · exact (inv_pos.mpr (by linarith)).le
      _ = ∏ i ∈ Finset.range (r + 1), (1 - q ^ ((i : ℝ) - σ))⁻¹ := by
          rw [Finset.prod_range_succ', mul_comm]
          congr 1
          · apply Finset.prod_congr rfl
            intro i _
            congr 3
            push_cast
            ring
          · simp

theorem sum_index_rpow_le : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] (r : ℕ) (σ : ℝ), (r : ℝ) - 1 < σ →
    ∀ C : Finset (Submodule O (Fin r → O)), (∀ M ∈ C, M.toAddSubgroup.index ≠ 0) →
    ∑ M ∈ C, (M.toAddSubgroup.index : ℝ) ^ (-σ) ≤
      ∏ i ∈ Finset.range r, (1 - (Nat.card (IsLocalRing.ResidueField O) : ℝ) ^ ((i : ℝ) - σ))⁻¹ :=
  fun _ _ _ _ _ r σ hσ C hC => main_bound r σ hσ C hC

end GlobalTheory.SubZeta
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumSublatticeIndexRpowLeSolomonStatement
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_sublattice_index_rpow_le_solomon : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] (r : ℕ) (σ : ℝ), (r : ℝ) - 1 < σ → ∀ C : Finset (Submodule O (Fin r → O)), (∀ M ∈ C, M.toAddSubgroup.index ≠ 0) → ∑ M ∈ C, (M.toAddSubgroup.index : ℝ) ^ (-σ) ≤ ∏ i ∈ Finset.range r, (1 - (Nat.card (IsLocalRing.ResidueField O) : ℝ) ^ ((i : ℝ) - σ))⁻¹ := by
  first | exact @GlobalTheory.SubZeta.sum_index_rpow_le | exact GlobalTheory.SubZeta.sum_index_rpow_le | (intros; apply GlobalTheory.SubZeta.sum_index_rpow_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumLatticePairsIndexRpowLe
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory.LatticePairSum

section Index

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)]

theorem index_range_eq_pow {r : ℕ} (A : Matrix (Fin r) (Fin r) O) (hA : A.det ≠ 0) :
    ∃ n : ℕ, IsDiscreteValuationRing.addVal O A.det = n ∧
      (LinearMap.range A.mulVecLin).toAddSubgroup.index =
        Nat.card (IsLocalRing.ResidueField O) ^ n := by
  have hl := GlobalTheory.length_quotient_range_mulVecLin_eq_addVal_det A
  have hne : Module.length O ((Fin r → O) ⧸ LinearMap.range A.mulVecLin) ≠ ⊤ := by
    rw [hl, ne_eq, IsDiscreteValuationRing.addVal_eq_top_iff]
    exact hA
  have hfl := Module.length_ne_top_iff.mp hne
  obtain ⟨n, hn, hc⟩ := GlobalTheory.exists_length_eq_and_card_eq_pow_of_isFiniteLength O _ hfl
  exact ⟨n, by rw [← hl, hn], hc⟩

theorem index_range_ne_zero {r : ℕ} (A : Matrix (Fin r) (Fin r) O) (hA : A.det ≠ 0) :
    (LinearMap.range A.mulVecLin).toAddSubgroup.index ≠ 0 := by
  obtain ⟨n, -, hc⟩ := index_range_eq_pow A hA
  rw [hc]
  exact pow_ne_zero _ Nat.card_pos.ne'

theorem index_range_transpose {r : ℕ} (A : Matrix (Fin r) (Fin r) O) (hA : A.det ≠ 0) :
    (LinearMap.range A.transpose.mulVecLin).toAddSubgroup.index =
      (LinearMap.range A.mulVecLin).toAddSubgroup.index := by
  obtain ⟨n, hn, hc⟩ := index_range_eq_pow A hA
  obtain ⟨m, hm, hd⟩ := index_range_eq_pow A.transpose (by rwa [Matrix.det_transpose])
  rw [Matrix.det_transpose, hn] at hm
  have : n = m := by exact_mod_cast hm
  rw [hc, hd, this]

theorem exists_matrix_of_index_ne_zero {r : ℕ} (M : Submodule O (Fin r → O))
    (hM : M.toAddSubgroup.index ≠ 0) :
    ∃ B : Matrix (Fin r) (Fin r) O, B.det ≠ 0 ∧ LinearMap.range B.mulVecLin = M := by
  classical
  have hfin : Finite ((Fin r → O) ⧸ M) := Nat.finite_of_card_ne_zero hM
  have hinf : Infinite O := by
    by_contra h
    rw [not_infinite_iff_finite] at h
    exact IsDiscreteValuationRing.not_isField O (Finite.isField_of_domain O)
  have htors : Module.finrank O ((Fin r → O) ⧸ M) = 0 := by
    apply Module.finrank_eq_zero_of_rank_eq_zero
    rw [rank_eq_zero_iff]
    intro x
    obtain ⟨a, b, hab, he⟩ := Finite.exists_ne_map_eq_of_infinite (fun c : O => c • x)
    exact ⟨a - b, sub_ne_zero.mpr hab, by rw [sub_smul, he, sub_self]⟩
  have hrank : Module.finrank O M = r := by
    have := Submodule.finrank_quotient_add_finrank M
    simpa [htors] using this
  let b := Module.finBasisOfFinrankEq O M hrank
  let B : Matrix (Fin r) (Fin r) O := Matrix.of fun i j => (b j : Fin r → O) i
  have hB : LinearMap.range B.mulVecLin = M := by
    rw [Matrix.range_mulVecLin]
    have h1 : Set.range B.col = Subtype.val '' (Set.range b) := by
      ext v
      simp only [Set.mem_range, Set.mem_image, exists_exists_eq_and]
      rfl
    have h2 : Submodule.span O (Subtype.val '' (Set.range b)) =
        (Submodule.span O (Set.range b)).map M.subtype := (Submodule.map_span M.subtype _).symm
    rw [h1, h2, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  refine ⟨B, ?_, hB⟩
  intro h0
  have hl := GlobalTheory.length_quotient_range_mulVecLin_eq_addVal_det B
  rw [h0, IsDiscreteValuationRing.addVal_zero, hB] at hl
  obtain ⟨n, hn, -⟩ := GlobalTheory.exists_length_eq_and_card_eq_pow O ((Fin r → O) ⧸ M)
  rw [hn] at hl
  exact ENat.coe_ne_top n hl

end Index

section Lat

variable (O K : Type) [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
  {r : ℕ}

noncomputable def incl (r : ℕ) : (Fin r → O) →ₗ[O] (Fin r → K) :=
  LinearMap.compLeft (Algebra.linearMap O K) (Fin r)

noncomputable abbrev stdLat (r : ℕ) : Submodule O (Fin r → K) :=
  Submodule.span O (Set.range (Pi.basisFun K (Fin r)))

noncomputable abbrev lat (X : Matrix (Fin r) (Fin r) K) : Submodule O (Fin r → K) :=
  (stdLat O K r).map ((X.mulVecLin).restrictScalars O)

variable {O K}

theorem incl_apply (x : Fin r → O) (i : Fin r) : incl O K r x i = algebraMap O K (x i) := rfl

theorem incl_injective : Function.Injective (incl O K r) := by
  intro x y h
  funext i
  exact IsFractionRing.injective O K (congrFun h i)

theorem stdLat_eq_range : stdLat O K r = LinearMap.range (incl O K r) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨Pi.single i 1, ?_⟩
    funext j
    rw [incl_apply, Pi.basisFun_apply]
    by_cases h : j = i
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  · rintro _ ⟨x, rfl⟩
    have : incl O K r x = ∑ i, x i • (Pi.basisFun K (Fin r)) i := by
      funext j
      simp [incl_apply, Finset.sum_apply, Pi.single_apply, Algebra.smul_def]
    rw [this]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem mem_lat {X : Matrix (Fin r) (Fin r) K} {v : Fin r → K} :
    v ∈ lat O K X ↔ ∃ x : Fin r → O, X.mulVec (incl O K r x) = v := by
  rw [lat, stdLat_eq_range]
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨_, ⟨x, rfl⟩, rfl⟩

theorem map_mulVec_incl (A : Matrix (Fin r) (Fin r) O) (x : Fin r → O) :
    (A.map (algebraMap O K)).mulVec (incl O K r x) = incl O K r (A.mulVec x) := by
  funext i
  rw [incl_apply]
  exact (RingHom.map_mulVec (algebraMap O K) A x i).symm

theorem exists_int_matrix (X : Matrix (Fin r) (Fin r) K) (h : lat O K X ≤ stdLat O K r) :
    ∃ X₀ : Matrix (Fin r) (Fin r) O, X₀.map (algebraMap O K) = X := by
  classical
  have hc : ∀ j, ∃ y : Fin r → O, incl O K r y = X.mulVec (Pi.single j 1) := by
    intro j
    have h1 : X.mulVec (Pi.single j 1) ∈ lat O K X := by
      rw [mem_lat]
      refine ⟨Pi.single j 1, ?_⟩
      congr 1
      funext i
      rw [incl_apply]
      by_cases hij : i = j
      · subst hij; simp
      · simp [Pi.single_eq_of_ne hij]
    have h2 := h h1
    rw [stdLat_eq_range] at h2
    exact h2
  choose y hy using hc
  refine ⟨Matrix.of fun i j => y j i, ?_⟩
  ext i j
  have := congrFun (hy j) i
  rw [incl_apply] at this
  simpa using this

end Lat

section Main

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Field K] [Algebra O K] [IsFractionRing O K] {r : ℕ}

omit [IsDiscreteValuationRing O] in
theorem relIndex_stdLat (H : AddSubgroup (Fin r → K)) :
    H.relIndex (stdLat O K r).toAddSubgroup =
      (H.comap (incl O K r).toAddMonoidHom).index := by
  have h : (stdLat O K r).toAddSubgroup =
      (⊤ : AddSubgroup (Fin r → O)).map (incl O K r).toAddMonoidHom := by
    ext v
    rw [Submodule.mem_toAddSubgroup, stdLat_eq_range]
    simp
  rw [h, ← AddSubgroup.relIndex_comap, AddSubgroup.relIndex_top_right]

omit [IsDiscreteValuationRing O] in
theorem det_map_ne_zero (B : Matrix (Fin r) (Fin r) O) (hB : B.det ≠ 0) :
    (B.map (algebraMap O K)).det ≠ 0 := by
  have h1 : (B.map (algebraMap O K)).det = algebraMap O K B.det :=
    (RingHom.map_det (algebraMap O K) B).symm
  rw [h1]
  exact fun h => hB (IsFractionRing.injective O K (by simpa using h))

omit [IsDiscreteValuationRing O] in
theorem exists_dual (B : Matrix (Fin r) (Fin r) O) (hB : B.det ≠ 0) (g : GL (Fin r) K)
    (h : (lat O K (g : Matrix (Fin r) (Fin r) K)).comap (incl O K r) =
      LinearMap.range B.mulVecLin) :
    ∃ A : Matrix (Fin r) (Fin r) O,
      A.map (algebraMap O K) =
        ((g⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) * B.map (algebraMap O K) ∧
      A.det ≠ 0 ∧
      (stdLat O K r).toAddSubgroup.relIndex
          (lat O K (g : Matrix (Fin r) (Fin r) K)).toAddSubgroup =
        (LinearMap.range A.mulVecLin).toAddSubgroup.index := by
  have hGi : ((g⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) * (g : Matrix (Fin r) (Fin r) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hGG : (g : Matrix (Fin r) (Fin r) K) * ((g⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  generalize hG : (g : Matrix (Fin r) (Fin r) K) = G at *
  generalize hGinv : ((g⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) = Gi at *
  have hle : lat O K (Gi * B.map (algebraMap O K)) ≤ stdLat O K r := by
    intro v hv
    obtain ⟨x, rfl⟩ := mem_lat.1 hv
    have h1 : B.mulVec x ∈ (lat O K G).comap (incl O K r) := by
      rw [h]; exact ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := mem_lat.1 (Submodule.mem_comap.1 h1)
    rw [stdLat_eq_range]
    refine ⟨y, ?_⟩
    rw [← Matrix.mulVec_mulVec, map_mulVec_incl, ← hy, Matrix.mulVec_mulVec, hGi,
      Matrix.one_mulVec]
  obtain ⟨A, hA⟩ := exists_int_matrix _ hle
  have hdet : A.det ≠ 0 := by
    intro h0
    have h1 : (A.map (algebraMap O K)).det = algebraMap O K A.det :=
      (RingHom.map_det (algebraMap O K) A).symm
    rw [h0, map_zero, hA, Matrix.det_mul] at h1
    have h2 : Gi.det ≠ 0 := by
      intro h3
      have := congrArg Matrix.det hGi
      rw [Matrix.det_mul, h3, zero_mul, Matrix.det_one] at this
      exact zero_ne_one this
    exact (mul_ne_zero h2 (det_map_ne_zero B hB)) h1
  refine ⟨A, hA, hdet, ?_⟩
  have hmap : (lat O K G).toAddSubgroup =
      (stdLat O K r).toAddSubgroup.map G.mulVecLin.toAddMonoidHom := by
    ext v
    simp
  rw [hmap, ← AddSubgroup.relIndex_comap, relIndex_stdLat]
  congr 1
  ext x
  simp only [AddSubgroup.mem_comap, LinearMap.toAddMonoidHom_coe, Submodule.mem_toAddSubgroup,
    LinearMap.mem_range, Matrix.mulVecLin_apply]
  constructor
  · intro hx
    rw [stdLat_eq_range] at hx
    obtain ⟨y, hy⟩ := hx
    have h1 : y ∈ (lat O K G).comap (incl O K r) := by
      refine Submodule.mem_comap.2 (mem_lat.2 ⟨x, hy.symm⟩)
    rw [h] at h1
    obtain ⟨z, rfl⟩ := h1
    refine ⟨z, incl_injective (K := K) ?_⟩
    rw [← map_mulVec_incl, hA, ← Matrix.mulVec_mulVec]
    rw [Matrix.mulVecLin_apply, ← map_mulVec_incl (K := K)] at hy
    rw [hy, Matrix.mulVec_mulVec, hGi, Matrix.one_mulVec]
  · rintro ⟨z, rfl⟩
    rw [stdLat_eq_range]
    refine ⟨B.mulVec z, ?_⟩
    rw [← map_mulVec_incl, ← map_mulVec_incl, hA, Matrix.mulVec_mulVec, ← mul_assoc, hGG,
      one_mul]

end Main

section Final

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Field K] [Algebra O K] [IsFractionRing O K] {r : ℕ}


omit [IsDiscreteValuationRing O] in
theorem lat_le_of_range_transpose_le (B : Matrix (Fin r) (Fin r) O) (hB : B.det ≠ 0)
    (g₀ g₁ : GL (Fin r) K) (A₀ A₁ : Matrix (Fin r) (Fin r) O)
    (h₀ : A₀.map (algebraMap O K) =
      ((g₀⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) * B.map (algebraMap O K))
    (h₁ : A₁.map (algebraMap O K) =
      ((g₁⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) * B.map (algebraMap O K))
    (hr : LinearMap.range A₁.transpose.mulVecLin ≤ LinearMap.range A₀.transpose.mulVecLin) :
    lat O K (g₀ : Matrix (Fin r) (Fin r) K) ≤ lat O K (g₁ : Matrix (Fin r) (Fin r) K) := by
  classical
  have hcol : ∀ j, ∃ u : Fin r → O,
      A₀.transpose.mulVec u = A₁.transpose.mulVec (Pi.single j 1) := fun j => by
    obtain ⟨u, hu⟩ := hr (LinearMap.mem_range_self A₁.transpose.mulVecLin (Pi.single j 1))
    exact ⟨u, hu⟩
  choose u hu using hcol
  let U : Matrix (Fin r) (Fin r) O := Matrix.of fun i j => u j i
  have hU : A₁.transpose = A₀.transpose * U := by
    ext i j
    have := congrFun (hu j) i
    rw [Matrix.mulVec_single_one] at this
    rw [Matrix.mul_apply]
    simpa [Matrix.mulVec, dotProduct, U] using this.symm
  have hU' : A₁ = U.transpose * A₀ := by
    rw [← Matrix.transpose_transpose A₁, hU, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hdetB : IsUnit (B.map (algebraMap O K)).det := (det_map_ne_zero B hB).isUnit
  have hmap : ((g₁⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) =
      U.transpose.map (algebraMap O K) * ((g₀⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) := by
    have h2 : ((g₁⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) * B.map (algebraMap O K) =
        U.transpose.map (algebraMap O K) *
          ((g₀⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) * B.map (algebraMap O K) := by
      rw [← h₁, hU', Matrix.map_mul, h₀, mul_assoc]
    have h3 := congrArg (· * (B.map (algebraMap O K))⁻¹) h2
    simpa only [mul_assoc, Matrix.mul_nonsing_inv _ hdetB, mul_one] using h3
  have hg : (g₀ : Matrix (Fin r) (Fin r) K) =
      (g₁ : Matrix (Fin r) (Fin r) K) * U.transpose.map (algebraMap O K) := by
    have e₁ : (g₁ : Matrix (Fin r) (Fin r) K) * ((g₁⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have e₀ : ((g₀⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) * (g₀ : Matrix (Fin r) (Fin r) K) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc (g₀ : Matrix (Fin r) (Fin r) K)
        = (g₁ : Matrix (Fin r) (Fin r) K) * ((g₁⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) *
            (g₀ : Matrix (Fin r) (Fin r) K) := by rw [e₁, one_mul]
      _ = (g₁ : Matrix (Fin r) (Fin r) K) * U.transpose.map (algebraMap O K) := by
          rw [hmap, mul_assoc, mul_assoc, e₀, mul_one]
  intro v hv
  obtain ⟨x, rfl⟩ := mem_lat.1 hv
  refine mem_lat.2 ⟨U.transpose.mulVec x, ?_⟩
  rw [hg, ← Matrix.mulVec_mulVec, map_mulVec_incl]

variable [Finite (IsLocalRing.ResidueField O)]

theorem sum_over_fiber_le (σ : ℝ) (hσ : (r : ℝ) - 1 < σ) (B : Matrix (Fin r) (Fin r) O)
    (hB : B.det ≠ 0) (S : Finset (GL (Fin r) K))
    (hinj : ∀ g ∈ S, ∀ g' ∈ S, lat O K (g : Matrix (Fin r) (Fin r) K) =
      lat O K (g' : Matrix (Fin r) (Fin r) K) → g = g')
    (hS : ∀ g ∈ S, (lat O K (g : Matrix (Fin r) (Fin r) K)).comap (incl O K r) =
      LinearMap.range B.mulVecLin) :
    ∑ g ∈ S, (((stdLat O K r).toAddSubgroup.relIndex
        (lat O K (g : Matrix (Fin r) (Fin r) K)).toAddSubgroup : ℕ) : ℝ) ^ (-σ) ≤
      ∏ i ∈ Finset.range r,
        (1 - (Nat.card (IsLocalRing.ResidueField O) : ℝ) ^ ((i : ℝ) - σ))⁻¹ := by
  classical
  choose! A hA₁ hA₂ hA₃ using fun g (hg : g ∈ S) => exists_dual B hB g (hS g hg)
  let f : GL (Fin r) K → Submodule O (Fin r → O) :=
    fun g => LinearMap.range (A g).transpose.mulVecLin
  have hf : Set.InjOn f S := fun g hg g' hg' he => by
    have hg₀ : g ∈ S := hg
    have hg₁ : g' ∈ S := hg'
    refine hinj g hg₀ g' hg₁ (le_antisymm ?_ ?_)
    · exact lat_le_of_range_transpose_le B hB g g' _ _ (hA₁ g hg₀) (hA₁ g' hg₁) he.ge
    · exact lat_le_of_range_transpose_le B hB g' g _ _ (hA₁ g' hg₁) (hA₁ g hg₀) he.le
  calc ∑ g ∈ S, (((stdLat O K r).toAddSubgroup.relIndex
        (lat O K (g : Matrix (Fin r) (Fin r) K)).toAddSubgroup : ℕ) : ℝ) ^ (-σ)
      = ∑ g ∈ S, (((f g).toAddSubgroup.index : ℕ) : ℝ) ^ (-σ) := by
        refine Finset.sum_congr rfl fun g hg => ?_
        rw [hA₃ g hg]
        simp only [f]
        rw [index_range_transpose _ (hA₂ g hg)]
    _ = ∑ N ∈ S.image f, ((N.toAddSubgroup.index : ℕ) : ℝ) ^ (-σ) :=
        (Finset.sum_image (f := fun N : Submodule O (Fin r → O) => ((N.toAddSubgroup.index : ℕ) : ℝ) ^ (-σ)) hf).symm
    _ ≤ _ := GlobalTheory.T.sum_sublattice_index_rpow_le_solomon O r σ hσ _ (by
        intro N hN
        obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hN
        exact index_range_ne_zero _ (by rw [Matrix.det_transpose]; exact hA₂ g hg))

end Final

theorem sum_index_pairs_le : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ) (σ : ℝ), (r : ℝ) - 1 < σ → ∀ C : Finset (GL (Fin r) K), (∀ g ∈ C, ∀ g' ∈ C, (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map (((g : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O) = (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map (((g' : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O) → g = g') → ∑ g ∈ C, (((((Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map (((g : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O)).toAddSubgroup.relIndex (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).toAddSubgroup : ℕ) : ℝ) * (((Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).toAddSubgroup.relIndex ((Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map (((g : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O)).toAddSubgroup : ℕ) : ℝ)) ^ (-σ) ≤ (∏ i ∈ Finset.range r, (1 - (Nat.card (IsLocalRing.ResidueField O) : ℝ) ^ ((i : ℝ) - σ))⁻¹) ^ 2 := by
  intro O K _ _ _ _ _ _ _ r σ hσ C hC
  classical
  change ∑ g ∈ C, ((((lat O K (g : Matrix (Fin r) (Fin r) K)).toAddSubgroup.relIndex
      (stdLat O K r).toAddSubgroup : ℕ) : ℝ) *
    (((stdLat O K r).toAddSubgroup.relIndex
      (lat O K (g : Matrix (Fin r) (Fin r) K)).toAddSubgroup : ℕ) : ℝ)) ^ (-σ) ≤ _
  generalize hZ : (∏ i ∈ Finset.range r,
    (1 - (Nat.card (IsLocalRing.ResidueField O) : ℝ) ^ ((i : ℝ) - σ))⁻¹) = Z
  have hZ0 : 0 ≤ Z := by
    have := GlobalTheory.T.sum_sublattice_index_rpow_le_solomon O r σ hσ ∅ (by simp)
    simpa [hZ] using this
  let Mg : GL (Fin r) K → Submodule O (Fin r → O) :=
    fun g => (lat O K (g : Matrix (Fin r) (Fin r) K)).comap (incl O K r)
  have hI : ∀ g : GL (Fin r) K, (lat O K (g : Matrix (Fin r) (Fin r) K)).toAddSubgroup.relIndex
      (stdLat O K r).toAddSubgroup = (Mg g).toAddSubgroup.index := fun g => by
    rw [relIndex_stdLat]
    rfl
  let I2 : GL (Fin r) K → ℝ := fun g => (((stdLat O K r).toAddSubgroup.relIndex
      (lat O K (g : Matrix (Fin r) (Fin r) K)).toAddSubgroup : ℕ) : ℝ) ^ (-σ)
  have hterm : ∀ g : GL (Fin r) K, ((((lat O K (g : Matrix (Fin r) (Fin r) K)).toAddSubgroup.relIndex
      (stdLat O K r).toAddSubgroup : ℕ) : ℝ) *
    (((stdLat O K r).toAddSubgroup.relIndex
      (lat O K (g : Matrix (Fin r) (Fin r) K)).toAddSubgroup : ℕ) : ℝ)) ^ (-σ) =
      (((Mg g).toAddSubgroup.index : ℕ) : ℝ) ^ (-σ) * I2 g := fun g => by
    rw [hI, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  have hzero : ∀ g : GL (Fin r) K, (Mg g).toAddSubgroup.index = 0 →
      (((Mg g).toAddSubgroup.index : ℕ) : ℝ) ^ (-σ) * I2 g = 0 := by
    intro g hg
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · have : Subsingleton (Fin 0 → O) := inferInstance
      rw [AddSubgroup.index_eq_zero_iff_infinite] at hg
      exact absurd hg (by simp [not_infinite_iff_finite]; infer_instance)
    · have hσ0 : 0 < σ := by
        have : (1 : ℝ) ≤ r := by exact_mod_cast hr
        linarith
      rw [hg, Nat.cast_zero, Real.zero_rpow (by linarith), zero_mul]
  simp only [hterm]
  let C' := C.filter fun g => (Mg g).toAddSubgroup.index ≠ 0
  have h1 : ∑ g ∈ C, (((Mg g).toAddSubgroup.index : ℕ) : ℝ) ^ (-σ) * I2 g =
      ∑ g ∈ C', (((Mg g).toAddSubgroup.index : ℕ) : ℝ) ^ (-σ) * I2 g := by
    exact (Finset.sum_filter_of_ne (p := fun g => (Mg g).toAddSubgroup.index ≠ 0)
      fun g _ hne hg => hne (hzero g hg)).symm
  rw [h1, ← Finset.sum_fiberwise_of_maps_to (s := C') (t := C'.image Mg) (g := Mg)
    (fun g hg => Finset.mem_image_of_mem _ hg)]
  have hfib : ∀ M ∈ C'.image Mg, ∑ g ∈ C' with Mg g = M,
      (((Mg g).toAddSubgroup.index : ℕ) : ℝ) ^ (-σ) * I2 g ≤
      ((M.toAddSubgroup.index : ℕ) : ℝ) ^ (-σ) * Z := by
    intro M hM
    obtain ⟨g₀, hg₀, rfl⟩ := Finset.mem_image.1 hM
    have hne : (Mg g₀).toAddSubgroup.index ≠ 0 := (Finset.mem_filter.1 hg₀).2
    obtain ⟨B, hB, hBM⟩ := exists_matrix_of_index_ne_zero _ hne
    have h2 : ∑ g ∈ C' with Mg g = Mg g₀,
        (((Mg g).toAddSubgroup.index : ℕ) : ℝ) ^ (-σ) * I2 g =
        (((Mg g₀).toAddSubgroup.index : ℕ) : ℝ) ^ (-σ) * ∑ g ∈ C' with Mg g = Mg g₀, I2 g := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun g hg => ?_
      rw [(Finset.mem_filter.1 hg).2]
    rw [h2]
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    rw [← hZ]
    refine sum_over_fiber_le σ hσ B hB _ ?_ ?_
    · intro g hg g' hg' he
      exact hC g (Finset.mem_filter.1 (Finset.mem_filter.1 hg).1).1 g'
        (Finset.mem_filter.1 (Finset.mem_filter.1 hg').1).1 he
    · intro g hg
      rw [hBM]
      exact (Finset.mem_filter.1 hg).2
  calc _ ≤ ∑ M ∈ C'.image Mg, ((M.toAddSubgroup.index : ℕ) : ℝ) ^ (-σ) * Z :=
        Finset.sum_le_sum hfib
    _ = (∑ M ∈ C'.image Mg, ((M.toAddSubgroup.index : ℕ) : ℝ) ^ (-σ)) * Z :=
        (Finset.sum_mul _ _ _).symm
    _ ≤ Z * Z := by
        refine mul_le_mul_of_nonneg_right ?_ hZ0
        rw [← hZ]
        refine GlobalTheory.T.sum_sublattice_index_rpow_le_solomon O r σ hσ _ ?_
        intro M hM
        obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hM
        exact (Finset.mem_filter.1 hg).2
    _ = Z ^ 2 := (sq Z).symm

end GlobalTheory.LatticePairSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumLatticePairsIndexRpowLeStatement
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_lattice_pairs_index_rpow_le : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ) (σ : ℝ), (r : ℝ) - 1 < σ → ∀ C : Finset (GL (Fin r) K), (∀ g ∈ C, ∀ g' ∈ C, (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map (((g : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O) = (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map (((g' : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O) → g = g') → ∑ g ∈ C, (((((Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map (((g : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O)).toAddSubgroup.relIndex (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).toAddSubgroup : ℕ) : ℝ) * (((Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).toAddSubgroup.relIndex ((Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map (((g : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O)).toAddSubgroup : ℕ) : ℝ)) ^ (-σ) ≤ (∏ i ∈ Finset.range r, (1 - (Nat.card (IsLocalRing.ResidueField O) : ℝ) ^ ((i : ℝ) - σ))⁻¹) ^ 2 := by
  first | exact @GlobalTheory.LatticePairSum.sum_index_pairs_le | exact GlobalTheory.LatticePairSum.sum_index_pairs_le | (intros; apply GlobalTheory.LatticePairSum.sum_index_pairs_le <;> assumption)
end
