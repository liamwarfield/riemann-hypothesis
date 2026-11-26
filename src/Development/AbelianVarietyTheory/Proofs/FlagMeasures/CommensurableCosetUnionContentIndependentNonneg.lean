module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EichlerIsometry
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsConsecutiveRatioLeRpow

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommensurableCosetUnionContentIndependentNonneg
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommensurableCosetUnionContentIndependentNonneg
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

theorem image_mk_eq_preimage_of_le {W : Type} [AddCommGroup W] {A A' : AddSubgroup W} {S : Set W}
    (hle : A' ≤ A) (hS : ∀ x ∈ S, ∀ a ∈ A, x + a ∈ S) :
    (QuotientAddGroup.mk : W → W ⧸ A') '' S =
      (AddSubgroup.quotientEquivProdOfLE hle) ⁻¹'
        (((QuotientAddGroup.mk : W → W ⧸ A) '' S) ×ˢ Set.univ) := by
  ext q
  induction q using QuotientAddGroup.induction_on with
  | H x =>
    have h1 : (AddSubgroup.quotientEquivProdOfLE hle (QuotientAddGroup.mk x)).1 =
        (QuotientAddGroup.mk x : W ⧸ A) := rfl
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true, h1]
    constructor
    · rintro ⟨y, hy, hyx⟩
      exact ⟨y, hy, QuotientAddGroup.eq.2 (hle (QuotientAddGroup.eq.1 hyx))⟩
    · rintro ⟨y, hy, hyx⟩
      have := hS y hy _ (QuotientAddGroup.eq.1 hyx)
      refine ⟨x, ?_, rfl⟩
      simpa using this

theorem ncard_image_mk_of_le {W : Type} [AddCommGroup W] {A A' : AddSubgroup W} {S : Set W}
    (hle : A' ≤ A) (hS : ∀ x ∈ S, ∀ a ∈ A, x + a ∈ S) :
    ((QuotientAddGroup.mk : W → W ⧸ A') '' S).ncard =
      ((QuotientAddGroup.mk : W → W ⧸ A) '' S).ncard * A'.relIndex A := by
  rw [image_mk_eq_preimage_of_le hle hS,
    Set.ncard_preimage_of_injective_subset_range (Equiv.injective _)
      (by rw [Equiv.range_eq_univ]; exact Set.subset_univ _), Set.ncard_prod, Set.ncard_univ]
  rfl

theorem GoodSub.of_le {W : Type} [AddCommGroup W] {W0 A A' : AddSubgroup W} {S : Set W}
    (h : GoodSub W0 A S) (hle : A' ≤ A) (hi : A'.relIndex A ≠ 0) : GoodSub W0 A' S := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨AddSubgroup.relIndex_ne_zero_trans hi h1,
    fun h0 => h2 (AddSubgroup.relIndex_eq_zero_of_le_right hle h0),
    fun x hx a ha => h3 x hx a (hle ha), ?_⟩
  rw [image_mk_eq_preimage_of_le hle h3]
  haveI : Finite (A ⧸ A'.addSubgroupOf A) := Nat.finite_of_card_ne_zero hi
  exact (h4.prod Set.finite_univ).preimage (Equiv.injective _).injOn

theorem relVol_eq_mul_of_le {W : Type} [AddCommGroup W] {W0 A A' : AddSubgroup W}
    (h1 : A.relIndex W0 ≠ 0) (hle : A' ≤ A) (hi : A'.relIndex A ≠ 0) :
    relVol W0 A = (A'.relIndex A : ℝ) * relVol W0 A' := by
  have h1' : A'.relIndex W0 ≠ 0 := AddSubgroup.relIndex_ne_zero_trans hi h1
  have e1 : W0.relIndex A' * A'.relIndex A = (W0 ⊓ A').relIndex A := by
    have := AddSubgroup.relIndex_inf_mul_relIndex W0 A' A
    rwa [inf_eq_left.2 hle] at this
  have e2 : A'.relIndex (W0 ⊓ A) * W0.relIndex A = (A' ⊓ W0).relIndex A :=
    AddSubgroup.relIndex_inf_mul_relIndex A' W0 A
  have e3 : A'.relIndex (A ⊓ W0) * A.relIndex W0 = A'.relIndex W0 := by
    have := AddSubgroup.relIndex_inf_mul_relIndex A' A W0
    rwa [inf_eq_left.2 hle] at this
  rw [inf_comm A' W0, ← e1, inf_comm W0 A] at e2
  have e2' : (A'.relIndex (A ⊓ W0) : ℝ) * W0.relIndex A = W0.relIndex A' * A'.relIndex A := by
    exact_mod_cast e2
  have e3' : (A'.relIndex (A ⊓ W0) : ℝ) * A.relIndex W0 = A'.relIndex W0 := by
    exact_mod_cast e3
  have n1 : (A.relIndex W0 : ℝ) ≠ 0 := by exact_mod_cast h1
  have n2 : (A'.relIndex W0 : ℝ) ≠ 0 := by exact_mod_cast h1'
  unfold relVol
  rw [← mul_div_assoc, div_eq_div_iff n1 n2, ← e3']
  linear_combination (A.relIndex W0 : ℝ) * e2'

theorem GoodSub.count_eq_of_le {W : Type} [AddCommGroup W] {W0 A A' : AddSubgroup W} {S : Set W}
    (h : GoodSub W0 A S) (hle : A' ≤ A) (hi : A'.relIndex A ≠ 0) :
    (((QuotientAddGroup.mk : W → W ⧸ A) '' S).ncard : ℝ) * relVol W0 A =
      (((QuotientAddGroup.mk : W → W ⧸ A') '' S).ncard : ℝ) * relVol W0 A' := by
  rw [ncard_image_mk_of_le hle h.2.2.1, relVol_eq_mul_of_le h.1 hle hi]
  push_cast
  ring

theorem GoodSub.count_eq {W : Type} [AddCommGroup W] {W0 A B : AddSubgroup W} {S : Set W}
    (hA : GoodSub W0 A S) (hB : GoodSub W0 B S) :
    (((QuotientAddGroup.mk : W → W ⧸ A) '' S).ncard : ℝ) * relVol W0 A =
      (((QuotientAddGroup.mk : W → W ⧸ B) '' S).ncard : ℝ) * relVol W0 B := by
  have i1 : (A ⊓ B).relIndex A ≠ 0 := by
    rw [AddSubgroup.inf_relIndex_left]
    exact AddSubgroup.relIndex_ne_zero_trans hB.1 hA.2.1
  have i2 : (A ⊓ B).relIndex B ≠ 0 := by
    rw [AddSubgroup.inf_relIndex_right]
    exact AddSubgroup.relIndex_ne_zero_trans hA.1 hB.2.1
  rw [hA.count_eq_of_le inf_le_left i1, hB.count_eq_of_le inf_le_right i2]

theorem GoodSub.cont_eq {W : Type} [AddCommGroup W] {W0 A : AddSubgroup W} {S : Set W}
    (hA : GoodSub W0 A S) :
    cont W0 S = (((QuotientAddGroup.mk : W → W ⧸ A) '' S).ncard : ℝ) * relVol W0 A := by
  have h : IsCO W0 S := ⟨A, hA⟩
  unfold cont
  rw [dite_eq_left h]
  exact GoodSub.count_eq h.choose_spec hA

theorem cont_independent_pos : ∀ {W : Type} [AddCommGroup W] (W0 : AddSubgroup W) (S : Set W), (∀ A, GoodSub W0 A S → cont W0 S = (((QuotientAddGroup.mk : W → W ⧸ A) '' S).ncard : ℝ) * relVol W0 A) ∧ (∀ A A', GoodSub W0 A S → A' ≤ A → A'.relIndex A ≠ 0 → GoodSub W0 A' S) ∧ 0 ≤ cont W0 S ∧ (IsCO W0 S → S.Nonempty → 0 < cont W0 S) := by
  intro W _ W0 S
  refine ⟨fun A hA => hA.cont_eq, fun A A' h hle hi => h.of_le hle hi, ?_, ?_⟩
  · unfold cont relVol
    split_ifs
    · positivity
    · exact le_rfl
  · rintro ⟨A, hA⟩ hne
    rw [hA.cont_eq]
    have p1 : 0 < ((QuotientAddGroup.mk : W → W ⧸ A) '' S).ncard :=
      (Set.ncard_pos hA.2.2.2).2 (hne.image _)
    have p2 : 0 < W0.relIndex A := Nat.pos_of_ne_zero hA.2.1
    have p3 : 0 < A.relIndex W0 := Nat.pos_of_ne_zero hA.1
    unfold relVol
    positivity

end GlobalTheory.HL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommensurableCosetUnionContentIndependentNonnegStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commensurableCosetUnionContent_independent_nonneg : ∀ {W : Type} [AddCommGroup W] (W0 : AddSubgroup W) (S : Set W), (∀ A, GoodSub W0 A S → cont W0 S = (((QuotientAddGroup.mk : W → W ⧸ A) '' S).ncard : ℝ) * relVol W0 A) ∧ (∀ A A', GoodSub W0 A S → A' ≤ A → A'.relIndex A ≠ 0 → GoodSub W0 A' S) ∧ 0 ≤ cont W0 S ∧ (IsCO W0 S → S.Nonempty → 0 < cont W0 S) := by
  first | exact @GlobalTheory.HL.cont_independent_pos | exact GlobalTheory.HL.cont_independent_pos | (intros; apply GlobalTheory.HL.cont_independent_pos <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassOrbitsEqTsumFiber
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

theorem encard_eq_tsum_fiber {X Z : Type*} (q : X → Z) (Q : X → Prop) :
    (({x | Q x} : Set X).encard : ℝ≥0∞)
      = ∑' z : Z, (({x | q x = z ∧ Q x} : Set X).encard : ℝ≥0∞) := by
  have e : ∀ S : Set X, (S.encard : ℝ≥0∞) = ∑' x, S.indicator (fun _ => (1 : ℝ≥0∞)) x := by
    intro S
    rw [← ENNReal.tsum_set_one, tsum_subtype S (fun _ => (1 : ℝ≥0∞))]
  simp only [e]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun x => ?_
  rw [tsum_eq_single (q x)]
  · simp [Set.indicator]
  · intro z hz
    have : ¬ q x = z := fun h => hz h.symm
    simp [Set.indicator, this]

theorem encard_orbit_fiber {G X Y : Type*} [Group G] [MulAction G X] [MulAction G Y]
    (H : Subgroup G) (P : X → Prop) (π : X → Y)
    (hP : ∀ h ∈ H, ∀ x, P x → P (h • x) ∧ π (h • x) = h • π x) (x : X) (hx : P x)
    (hfin : (H ⊓ MulAction.stabilizer G x).relIndex (H ⊓ MulAction.stabilizer G (π x)) ≠ 0) :
    ({z | (Quotient.mk'' z : MulAction.orbitRel.Quotient H X) = Quotient.mk'' x ∧
        P z ∧ π z = π x} : Set X).encard
      = (H ⊓ MulAction.stabilizer G x).relIndex (H ⊓ MulAction.stabilizer G (π x)) := by
  have h1 : ({z | (Quotient.mk'' z : MulAction.orbitRel.Quotient H X) = Quotient.mk'' x ∧
        P z ∧ π z = π x} : Set X)
      = MulAction.orbit (↥(H ⊓ MulAction.stabilizer G (π x))) x := by
    ext z
    simp only [Set.mem_setOf_eq, Quotient.eq'', MulAction.orbitRel_apply]
    constructor
    · rintro ⟨⟨h, rfl⟩, -, hz⟩
      have h2 := (hP h h.2 x hx).2
      exact ⟨⟨h, h.2, h2.symm.trans hz⟩, rfl⟩
    · rintro ⟨⟨h, hh, hs⟩, rfl⟩
      have h2 := hP h hh x hx
      exact ⟨⟨⟨h, hh⟩, rfl⟩, h2.1, h2.2.trans hs⟩
  have h2 : (H ⊓ MulAction.stabilizer G x).relIndex (H ⊓ MulAction.stabilizer G (π x))
      = (MulAction.orbit (↥(H ⊓ MulAction.stabilizer G (π x))) x).ncard := by
    rw [← MulAction.index_stabilizer, Subgroup.relIndex]
    congr 1
    ext ⟨h, hh, hs⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
    exact ⟨fun a => a.2, fun a => ⟨hh, a⟩⟩
  rw [h1, h2]
  rw [h2] at hfin
  exact (Set.finite_of_ncard_ne_zero hfin).cast_ncard_eq.symm

theorem mass_orbits_eq_tsum_fiber : ∀ {G X Y : Type} [Group G] [MulAction G X] [MulAction G Y] (H K0 : Subgroup G) (P : X → Prop) (π : X → Y), K0 ≤ H → (∀ h ∈ H, ∀ x, P x → P (h • x) ∧ π (h • x) = h • π x ∧ invVol K0 (H ⊓ MulAction.stabilizer G (h • x)) = invVol K0 (H ⊓ MulAction.stabilizer G x)) → (∀ x, P x → K0.relIndex (H ⊓ MulAction.stabilizer G x) ≠ 0 ∧ (H ⊓ MulAction.stabilizer G x).relIndex K0 ≠ 0 ∧ K0.relIndex (H ⊓ MulAction.stabilizer G (π x)) ≠ 0 ∧ (H ⊓ MulAction.stabilizer G (π x)).relIndex K0 ≠ 0) → (∑' o : MulAction.orbitRel.Quotient H X, if P o.out then ENNReal.ofReal (invVol K0 (H ⊓ MulAction.stabilizer G o.out)) else 0) = ∑' c : MulAction.orbitRel.Quotient H Y, ENNReal.ofReal (invVol K0 (H ⊓ MulAction.stabilizer G c.out)) * (({x | P x ∧ π x = c.out} : Set X).encard : ℝ≥0∞) := by
  intro G X Y _ _ _ H K0 P π _ hP hc
  have hP' : ∀ h ∈ H, ∀ x, P x → P (h • x) ∧ π (h • x) = h • π x :=
    fun h hh x hx => ⟨(hP h hh x hx).1, (hP h hh x hx).2.1⟩
  simp only [fun c : MulAction.orbitRel.Quotient H Y =>
    encard_eq_tsum_fiber (fun z : X => (Quotient.mk'' z : MulAction.orbitRel.Quotient H X))
      (fun x => P x ∧ π x = c.out), ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun o => ?_
  have hmem : ∀ z : X, (Quotient.mk'' z : MulAction.orbitRel.Quotient H X) = o →
      ∃ h ∈ H, h • z = o.out := by
    intro z hz
    have : (Quotient.mk'' o.out : MulAction.orbitRel.Quotient H X) = Quotient.mk'' z := by
      rw [hz]; exact Quotient.out_eq' o
    rw [Quotient.eq'', MulAction.orbitRel_apply] at this
    obtain ⟨h, hh⟩ := this
    exact ⟨h, h.2, hh⟩
  split_ifs with ho
  · set c0 : MulAction.orbitRel.Quotient H Y := Quotient.mk'' (π o.out) with hc0
    rw [tsum_eq_single c0]
    · have : (Quotient.mk'' c0.out : MulAction.orbitRel.Quotient H Y) = Quotient.mk'' (π o.out) :=
        Quotient.out_eq' c0
      rw [Quotient.eq'', MulAction.orbitRel_apply] at this
      obtain ⟨⟨h, hh⟩, hy⟩ := this
      have hy' : h • π o.out = c0.out := hy
      obtain ⟨p1, p2, p3⟩ := hP h hh _ ho
      have ho' : o = Quotient.mk'' (h • o.out) := by
        conv_lhs => rw [← Quotient.out_eq' o]
        symm
        rw [Quotient.eq'', MulAction.orbitRel_apply]
        exact ⟨⟨h, hh⟩, rfl⟩
      rw [← p3, ← hy', ← p2]
      generalize h • o.out = x at p1 ho'
      obtain ⟨a1, a2, a3, a4⟩ := hc x p1
      have hle : H ⊓ MulAction.stabilizer G x ≤ H ⊓ MulAction.stabilizer G (π x) := by
        rintro g ⟨g1, g2⟩
        refine ⟨g1, ?_⟩
        have g3 : g • x = x := g2
        have := (hP' g g1 x p1).2
        rw [g3] at this
        exact this.symm
      obtain ⟨-, -, b, -⟩ := invVol_mul_pos_le_conj K0 _ _ a3 a4 a1 a2
      rw [ho', encard_orbit_fiber H P π hP' x p1 (Subgroup.relIndex_ne_zero_trans a2 a3), b hle,
        ENNReal.ofReal_mul' (Nat.cast_nonneg _)]
      simp
    · intro c hne
      have : ({x | (Quotient.mk'' x : MulAction.orbitRel.Quotient H X) = o ∧ P x ∧ π x = c.out} :
          Set X) = ∅ := by
        ext z
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨h1, h2, h3⟩
        obtain ⟨h, hh, e⟩ := hmem z h1
        apply hne
        rw [hc0, ← e, (hP' h hh z h2).2, h3]
        conv_lhs => rw [← Quotient.out_eq' c]
        symm
        rw [Quotient.eq'', MulAction.orbitRel_apply]
        exact ⟨⟨h, hh⟩, rfl⟩
      rw [this]; simp
  · symm
    refine ENNReal.tsum_eq_zero.2 fun c => ?_
    have : ({x | (Quotient.mk'' x : MulAction.orbitRel.Quotient H X) = o ∧ P x ∧ π x = c.out} :
        Set X) = ∅ := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨h1, h2, -⟩
      obtain ⟨h, hh, e⟩ := hmem z h1
      exact ho (e ▸ (hP' h hh z h2).1)
    rw [this]; simp

end GlobalTheory.HL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardSubmoduleAndHomLe
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.SubmoduleCount

section Abstract

variable {R : Type*} [CommRing R] {D : Type*} [AddCommGroup D] [Module R D]

end Abstract

variable {R : Type*} [CommRing R] {D : Type*} [AddCommGroup D] [Module R D] in
private theorem exists_finite_generators_of_isPrincipalIdealRing [IsPrincipalIdealRing R] :
    ∀ (g : ℕ) (M : Type) [AddCommGroup M] [Module R M] (x : Fin g → M),
      Submodule.span R (Set.range x) = ⊤ →
        ∀ N : Submodule R M, ∃ v : Fin g → M, N = Submodule.span R (Set.range v) := by
  intro g
  induction g with
  | zero =>
    intro M _ _ x hx N
    refine ⟨Fin.elim0, ?_⟩
    have hbot : (⊤ : Submodule R M) = ⊥ := by
      rw [← hx, Set.range_eq_empty, Submodule.span_empty]
    rw [Set.range_eq_empty, Submodule.span_empty, eq_bot_iff, ← hbot]
    exact le_top
  | succ g ih =>
    intro M _ _ x hx N
    set P := Submodule.span R (Set.range (fun i : Fin g => x i.succ)) with hPdef
    let x' : Fin g → P := fun i => ⟨x i.succ, Submodule.subset_span ⟨i, rfl⟩⟩
    have hx' : Submodule.span R (Set.range x') = ⊤ := by
      apply Submodule.map_injective_of_injective (f := P.subtype) Subtype.val_injective
      rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp]
      rfl
    obtain ⟨w, hw⟩ := ih P x' hx' (N.comap P.subtype)
    set I : Ideal R := (N ⊔ P).comap (LinearMap.toSpanSingleton R M (x 0)) with hIdef
    set a := Submodule.IsPrincipal.generator I
    have ha : a ∈ I := Submodule.IsPrincipal.generator_mem I
    rw [hIdef, Submodule.mem_comap, LinearMap.toSpanSingleton_apply, Submodule.mem_sup] at ha
    obtain ⟨n, hn, p, hp, hnp⟩ := ha
    refine ⟨Fin.cons n (fun i => (w i : M)), le_antisymm ?_ ?_⟩
    · intro m hm
      have hmtop : m ∈ Submodule.span R (Set.range x) := hx ▸ Submodule.mem_top
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hmtop
      rw [Fin.sum_univ_succ] at hm ⊢
      set q := ∑ i : Fin g, c i.succ • x i.succ with hqdef
      have hq : q ∈ P := Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      have hc0 : c 0 ∈ I := by
        rw [hIdef, Submodule.mem_comap, LinearMap.toSpanSingleton_apply]
        have := sub_mem (Submodule.mem_sup_left hm : _ ∈ N ⊔ P) (Submodule.mem_sup_right hq : _ ∈ N ⊔ P)
        simpa using this
      rw [← Submodule.IsPrincipal.span_singleton_generator I, Submodule.mem_span_singleton] at hc0
      obtain ⟨t, ht⟩ := hc0
      have hdiff : c 0 • x 0 + q - t • n = q + t • p := by
        rw [← ht, smul_assoc, ← hnp, smul_add]; abel
      have hdP : c 0 • x 0 + q - t • n ∈ P := by
        rw [hdiff]; exact add_mem hq (Submodule.smul_mem _ _ hp)
      have hdN : c 0 • x 0 + q - t • n ∈ N := sub_mem hm (Submodule.smul_mem _ _ hn)
      have hmem : (⟨_, hdP⟩ : P) ∈ Submodule.span R (Set.range w) := hw ▸ hdN
      have hle : Submodule.span R (Set.range w) ≤ (Submodule.span R (Set.range (Fin.cons n (fun i => (w i : M)) : Fin (g + 1) → M))).comap P.subtype := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact Submodule.subset_span ⟨i.succ, by simp⟩
      have h1 := hle hmem
      rw [Submodule.mem_comap, Submodule.coe_subtype] at h1
      have h2 : t • n ∈ Submodule.span R (Set.range (Fin.cons n (fun i => (w i : M)) : Fin (g + 1) → M)) :=
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, by simp⟩)
      simpa using add_mem h1 h2
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa using hn
      · have : w i ∈ N.comap P.subtype := hw ▸ Submodule.subset_span ⟨i, rfl⟩
        simpa using this

theorem _root_.GlobalTheory.SubmoduleCount.card_submodule_and_hom_le : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E), ∀ (D : Type) [AddCommGroup D] [Module L.O D] [Finite D] (g : ℕ) (x : Fin g → D), Submodule.span L.O (Set.range x) = ⊤ → Nat.card (Submodule L.O D) ≤ Nat.card D ^ g ∧ ∀ (D' : Type) [AddCommGroup D'] [Module L.O D'] [Finite D'], Nat.card (D →ₗ[L.O] D') ≤ Nat.card D' ^ g := by
  intro F _ _ _ _ _ E _ _ _ L D _ _ _ g x hx
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (ValuativeRel.valuation F).integer
  haveI : IsPrincipalIdealRing L.O := (_root_.GlobalTheory.UnramOrder.order_facts L ϖ hϖ).2.2.2.1
  refine ⟨?_, fun D' _ _ _ => ?_⟩
  · have hsurj : Function.Surjective (fun v : Fin g → D => Submodule.span L.O (Set.range v)) := by
      intro N
      obtain ⟨v, hv⟩ := exists_finite_generators_of_isPrincipalIdealRing g D x hx N
      exact ⟨v, hv.symm⟩
    calc Nat.card (Submodule L.O D) ≤ Nat.card (Fin g → D) := Nat.card_le_card_of_surjective _ hsurj
      _ = Nat.card D ^ g := by simp [Nat.card_fun]
  · have hinj : Function.Injective (fun f : D →ₗ[L.O] D' => fun i => f (x i)) := by
      intro f f' h
      exact LinearMap.ext_on_range hx (fun i => congrFun h i)
    calc Nat.card (D →ₗ[L.O] D') ≤ Nat.card (Fin g → D') := Nat.card_le_card_of_injective _ hinj
      _ = Nat.card D' ^ g := by simp [Nat.card_fun]

end GlobalTheory.SubmoduleCount
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryConjugatorOfSplitIdempotents
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryConjugatorOfSplitIdempotents
open Matrix

namespace GlobalTheory

open ReciprocityTheory.Aut

theorem unitary_conjugator_of_split_idempotents :
  ∀ (R : Type) [CommRing R] (σ : R →+* R), (∀ a, σ (σ a) = a) → ∀ (m n : ℕ) (ι : Type) [Fintype ι] (ε : ι → R), (∀ j, ε j * ε j = ε j) → (∀ j, ε j * σ (ε j) = 0) → (∀ j k, j ≠ k → ε j * ε k = 0 ∧ ε j * σ (ε k) = 0) → ∀ (Z P : Matrix (Fin m) (Fin n) R) (Z' P' : Matrix (Fin n) (Fin m) R), Z * Z' = 1 → Z' * Z = 1 → P * P' = 1 → P' * P = 1 → ∃ c : GL (Fin n) R, (c : Matrix (Fin n) (Fin n) R) * ReciprocityTheory.Aut.conjT σ (c : Matrix (Fin n) (Fin n) R) = 1 ∧ ∀ j, ε j • (Z * (c : Matrix (Fin n) (Fin n) R)) = ε j • P ∧ ε j • (((c⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * Z') = ε j • P' := by
  intro R _ σ hσ m n ι _ ε hidem hself hcross Z P Z' P' hZZ' hZ'Z hPP' hP'P
  classical

  obtain ⟨e, he⟩ : ∃ e : R, e = ∑ j, ε j := ⟨_, rfl⟩
  have hje : ∀ j, ε j * e = ε j := by
    intro j
    rw [he, Finset.mul_sum, Finset.sum_eq_single j (fun k _ hk => (hcross j k (Ne.symm hk)).1)
      (fun h => absurd (Finset.mem_univ j) h), hidem]
  have hjse : ∀ j, ε j * σ e = 0 := by
    intro j
    set_option synthInstance.maxHeartbeats 100000 in
      rw [he, map_sum, Finset.mul_sum]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    by_cases hk : j = k
    · subst hk; exact hself j
    · exact (hcross j k hk).2
  have hee : e * e = e := by
    nth_rewrite 1 [he]
    rw [Finset.sum_mul]
    simp only [hje]
    exact he.symm
  have hese : e * σ e = 0 := by
    nth_rewrite 1 [he]
    rw [Finset.sum_mul]
    exact Finset.sum_eq_zero (fun j _ => hjse j)
  obtain ⟨e', he'⟩ : ∃ e' : R, e' = σ e := ⟨_, rfl⟩
  rw [← he'] at hese hjse
  have he'e' : e' * e' = e' := by rw [he', ← map_mul, hee]
  have he'e : e' * e = 0 := by rw [mul_comm, hese]
  have hσe' : σ e' = e := by rw [he', hσ]
  obtain ⟨f, hf⟩ : ∃ f : R, f = 1 - e - e' := ⟨_, rfl⟩
  have hσf : σ f = f := by rw [hf, map_sub, map_sub, map_one, hσe', ← he']; ring
  have hfe : f * e = 0 := by rw [hf]; linear_combination -hee - he'e
  have hfe' : f * e' = 0 := by rw [hf]; linear_combination -hese - he'e'
  have hff : f * f = f := by rw [hf]; linear_combination hee + he'e' + 2 * hese
  have hef : e * f = 0 := by rw [mul_comm, hfe]
  have he'f : e' * f = 0 := by rw [mul_comm, hfe']
  have hee'' : e * e' = 0 := hese
  have hsum : f + e + e' = 1 := by rw [hf]; ring

  have cadd : ∀ A B : Matrix (Fin n) (Fin n) R, conjT σ (A + B) = conjT σ A + conjT σ B := by
    intro A B; ext i j; simp [conjT]
  have csmul : ∀ (a : R) (A : Matrix (Fin n) (Fin n) R), conjT σ (a • A) = σ a • conjT σ A := by
    intro a A; ext i j; simp [conjT]
  set X : Matrix (Fin n) (Fin n) R := Z' * P with hX
  set Y : Matrix (Fin n) (Fin n) R := conjT σ (P' * Z) with hY
  set c : Matrix (Fin n) (Fin n) R := f • (1 : Matrix (Fin n) (Fin n) R) + e • X + e' • Y with hc
  have hcT : conjT σ c = f • (1 : Matrix (Fin n) (Fin n) R) + e' • conjT σ X + e • (P' * Z) := by
    rw [hc, cadd, cadd, csmul, csmul, csmul, conjT_one, hσf, hY, conjT_conjT σ hσ, hσe', ← he']
  have hXY : X * conjT σ Y = 1 := by
    rw [hY, conjT_conjT σ hσ, hX, Matrix.mul_assoc, ← Matrix.mul_assoc P, hPP', Matrix.one_mul, hZ'Z]
  have hYX : Y * conjT σ X = 1 := by
    rw [hY, ← conjT_mul, ← hXY, hY, conjT_conjT σ hσ]
    rw [hX, Matrix.mul_assoc, ← Matrix.mul_assoc P, hPP', Matrix.one_mul, hZ'Z, conjT_one]
  have hcc : c * conjT σ c = 1 := by
    rw [hcT, hc]
    have hYeq : P' * Z = conjT σ Y := by rw [hY, conjT_conjT σ hσ]
    rw [hYeq]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      hff, hfe, hfe', hef, he'f, hee, hee'', he'e, he'e', zero_smul, add_zero, zero_add,
      Matrix.one_mul, Matrix.mul_one, hXY, hYX, smul_add]
    conv_rhs => rw [← one_smul R (1 : Matrix (Fin n) (Fin n) R), ← hsum]
    simp only [add_smul]
    abel
  have hcc' : conjT σ c * c = 1 := mul_eq_one_comm.mp hcc
  refine ⟨⟨c, conjT σ c, hcc, hcc'⟩, hcc, fun j => ⟨?_, ?_⟩⟩
  · show ε j • (Z * c) = ε j • P
    have hjf : ε j * f = 0 := by
      rw [hf]; linear_combination -hje j - hjse j
    rw [hc, Matrix.mul_add, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul,
      smul_add, smul_add, smul_smul, smul_smul, smul_smul, hjf, hje, hjse, zero_smul, zero_smul,
      zero_add, add_zero, hX, ← Matrix.mul_assoc, hZZ', Matrix.one_mul]
  · show ε j • (conjT σ c * Z') = ε j • P'
    have hjf : ε j * f = 0 := by
      rw [hf]; linear_combination -hje j - hjse j
    rw [hcT, Matrix.add_mul, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.smul_mul,
      smul_add, smul_add, smul_smul, smul_smul, smul_smul, hjf, hje, hjse, zero_smul, zero_smul,
      zero_add, zero_add, Matrix.mul_assoc, hZZ', Matrix.mul_one]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryConjugatorOfSplitIdempotentsStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_conjugator_of_split_idempotents : ∀ (R : Type) [CommRing R] (σ : R →+* R), (∀ a, σ (σ a) = a) → ∀ (m n : ℕ) (ι : Type) [Fintype ι] (ε : ι → R), (∀ j, ε j * ε j = ε j) → (∀ j, ε j * σ (ε j) = 0) → (∀ j k, j ≠ k → ε j * ε k = 0 ∧ ε j * σ (ε k) = 0) → ∀ (Z P : Matrix (Fin m) (Fin n) R) (Z' P' : Matrix (Fin n) (Fin m) R), Z * Z' = 1 → Z' * Z = 1 → P * P' = 1 → P' * P = 1 → ∃ c : GL (Fin n) R, (c : Matrix (Fin n) (Fin n) R) * ReciprocityTheory.Aut.conjT σ (c : Matrix (Fin n) (Fin n) R) = 1 ∧ ∀ j, ε j • (Z * (c : Matrix (Fin n) (Fin n) R)) = ε j • P ∧ ε j • (((c⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * Z') = ε j • P' := by
  first | exact @GlobalTheory.unitary_conjugator_of_split_idempotents | exact GlobalTheory.unitary_conjugator_of_split_idempotents | (intros; apply GlobalTheory.unitary_conjugator_of_split_idempotents <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DetGramSumElimSmulSub
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc

namespace GlobalTheory

section

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)

private lemma hsub_left (x x' y : V) : H.h (x - x') y = H.h x y - H.h x' y := by
  rw [eq_sub_iff_add_eq, ← H.h_add_left, sub_add_cancel]

private lemma hsub_right (x y y' : V) : H.h x (y - y') = H.h x y - H.h x y' := by
  rw [H.h_herm (y - y') x, hsub_left, map_sub, ← H.h_herm, ← H.h_herm]

private lemma hsmul_right (c : F) (x y : V) :
    H.h x (algebraMap F E c • y) = algebraMap F E c * H.h x y := by
  rw [H.h_herm (algebraMap F E c • y) x, H.h_smul_left, map_mul, AlgEquiv.commutes, ← H.h_herm]

private lemma det_transpose_map_cj {ι : Type} [Fintype ι] [DecidableEq ι] (N : Matrix ι ι E) :
    (N.transpose.map M.L.cj).det = M.L.cj N.det := by
  have h1 := RingHom.map_det (M.L.cj : E →+* E) N.transpose
  rw [Matrix.det_transpose] at h1
  exact h1.symm

private lemma castLE_succ_eq_castSucc (r : ℕ) (h : r ≤ r + 1) :
    (Fin.castLE h : Fin r → Fin (r + 1)) = Fin.castSucc := by
  funext i
  rfl

theorem det_gram_sumElim_frames {r : ℕ} (P : LocNG.FPair H r) :
    (H.gram (Sum.elim P.A.f P.B.f)).det = (-1) ^ (r + 1) * P.Gv := by
  have diag : ∀ (Fr : LocNG.FrameD H r) (a b : Fin (r + 1)),
      H.h (Fr.f b) (Fr.f a) = Matrix.diagonal
        (fun i => if i = Fin.last r then -algebraMap F E Fr.T else 0) a b := by
    intro Fr a b
    rw [Matrix.diagonal_apply]
    by_cases hab : a = b
    · subst hab
      by_cases ha : a = Fin.last r
      · subst ha
        simp [Fr.h_zz]
      · simp [ha, Fr.h_iso a a (Or.inl ha)]
    · rw [if_neg hab, Fr.h_iso b a ?_]
      by_contra hc
      simp only [not_or, not_not] at hc
      exact hab (hc.2.trans hc.1.symm)
  have hblk : H.gram (Sum.elim P.A.f P.B.f) = Matrix.fromBlocks
      (Matrix.diagonal fun i => if i = Fin.last r then -algebraMap F E P.A.T else 0)
      (H.Zhat P.A.f P.B.f)
      ((H.Zhat P.A.f P.B.f).transpose.map M.L.cj)
      (Matrix.diagonal fun i => if i = Fin.last r then -algebraMap F E P.B.T else 0) := by
    ext (a | a) (b | b)
    · exact diag P.A a b
    · rfl
    · exact H.h_herm _ _
    · exact diag P.B a b
  rw [hblk, GlobalTheory.det_gram_two_frames, det_transpose_map_cj]
  have hsub : ((H.Zhat P.A.f P.B.f).transpose.map M.L.cj).submatrix Fin.castSucc Fin.castSucc
      = ((H.Zhat P.A.f P.B.f).submatrix Fin.castSucc Fin.castSucc).transpose.map M.L.cj := rfl
  rw [hsub, det_transpose_map_cj]
  congr 1
  simp only [LocNG.FPair.Gv, HermSp.Gdet, HermSp.normE, HermSp.Dl, dif_pos le_rfl,
    dif_pos (Nat.le_succ r), Fin.castLE_rfl, Matrix.submatrix_id_id, castLE_succ_eq_castSucc, map_mul]

theorem det_gram_sumElim_smul_sub {n : ℕ} (f f' : Fin n → V) (c : F) :
    (H.gram (Sum.elim f fun a => algebraMap F E c • (f' a - f a))).det
      = algebraMap F E c ^ (2 * n) * (H.gram (Sum.elim f f')).det := by
  set c' := algebraMap F E c with hc'
  have hcs : ∀ x : E, c • x = algebraMap F E c * x := fun x => Algebra.smul_def c x
  have key : H.gram (Sum.elim f fun a => c' • (f' a - f a)) =
      Matrix.fromBlocks 1 0 (-c' • (1 : Matrix (Fin n) (Fin n) E)) (c' • 1) * H.gram (Sum.elim f f') *
        Matrix.fromBlocks 1 (-c' • (1 : Matrix (Fin n) (Fin n) E)) 0 (c' • 1) := by
    ext (a | a) (b | b) <;>
      simp [HermSp.gram, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, H.h_smul_left,
        hsub_left, hsub_right, hc', hsmul_right, hcs] <;> ring
  rw [key, Matrix.det_mul, Matrix.det_mul, Matrix.det_fromBlocks_zero₁₂, Matrix.det_fromBlocks_zero₂₁]
  simp only [Matrix.det_one, Matrix.det_smul, Fintype.card_fin, one_mul, two_mul, pow_add]
  ring

end

theorem det_gram_frame_generators :
    ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
      [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK →
      ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r _k : ℕ) (P : LocNG.FPair H r),
        (H.gram P.MMgen).det * algebraMap F E (LocNG.theta M) ^ (2 * (r + 1))
          = (-1) ^ (r + 1) * P.Gv := by
  intro F _ _ _ E _ _ _ _ M _ V _ _ H r _ P
  unfold LocNG.FPair.MMgen HermSp.MMfam LocNG.theta
  cases hs : M.split with
  | none =>
    simp only [map_one, one_pow, mul_one]
    exact det_gram_sumElim_frames H P
  | some g =>
    simp only
    rw [det_gram_sumElim_smul_sub H, det_gram_sumElim_frames H P, mul_comm _ (algebraMap F E _ ^ _),
      ← mul_assoc, ← mul_pow, ← map_mul]
    have hq : ((g.q : 𝒪[F]) : F) ≠ 0 := by
      intro h0
      exact g.q_irr.ne_zero (Subtype.ext h0)
    rw [mul_inv_cancel₀ hq, map_one, one_pow, one_mul]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EichlerMapMemUnipotentCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EichlerMapMemUnipotentCharacter
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.EichlerUnip
open GlobalTheory.HL.Eichler

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem spanTo_mono (g : Fin (r + 1) → S.V) {a b : ℕ} (h : a ≤ b) : S.spanTo g a ≤ S.spanTo g b :=
  Submodule.span_mono (Set.image_mono fun _ hi => lt_of_lt_of_le hi h)

theorem mem_spanTo (g : Fin (r + 1) → S.V) {a : ℕ} (i : Fin (r + 1)) (h : (i : ℕ) < a) :
    g i ∈ S.spanTo g a := Submodule.subset_span ⟨i, h, rfl⟩

theorem hf_spanTo (g : Fin (r + 1) → S.V) {a : ℕ} (y : S.V)
    (h : ∀ i : Fin (r + 1), (i : ℕ) < a → hf L S.Hm (g i) y = 0) {x : S.V} (hx : x ∈ S.spanTo g a) :
    hf L S.Hm x y = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨i, hi, rfl⟩ := hx; exact h i hi
  | zero => simp [hf]
  | add a b _ _ ha hb => rw [hf_add_l, ha, hb, add_zero]
  | smul c a _ ha => rw [hf_smul_l, ha, mul_zero]

theorem hf_symm0 {x y : S.V} (h : hf L S.Hm x y = 0) : hf L S.Hm y x = 0 := by
  rw [← hf_cj L S.herm.1, h, map_zero]

theorem mem_unipOn {N : ℕ} {A B : Submodule E (Fin N → E)} (hBA : B ≤ A)
    (n : (Fin N → E) ≃ₗ[E] (Fin N → E)) (h1 : ∀ v ∈ A, n v - v ∈ B) (h2 : ∀ v ∈ A, n⁻¹ v - v ∈ B) :
    n ∈ unipOn A B := by
  refine ⟨fun v => ⟨fun hv => ?_, fun hv => ?_⟩, h1⟩
  · have h3 := A.add_mem (hBA (h2 _ hv)) hv
    have h4 : n⁻¹ (n v) = v := n.symm_apply_apply v
    rw [h4] at h3
    simpa using h3
  · simpa using A.add_mem (hBA (h1 _ hv)) hv

end

theorem eichler_mem_unip : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (g : Fin (r + 1) → S.V) (gs : Fin r → S.V), (g = S.f ∧ gs = S.es) ∨ (g = S.f' ∧ gs = S.es') → ∀ (j : Fin r) (x u : S.V) (s : E), x ∈ S.spanTo g (j + 1) → u ∈ perp L S.Hm (S.spanTo g (j + 1)) → s + L.cj s = S.h u u → ∃ n ∈ S.Nof g, (∀ v, n v = eich L S.Hm x u s v) ∧ (∀ v, n⁻¹ v = eich L S.Hm x (-u) (L.cj s) v) ∧ (∀ v ∈ S.spanTo g (j + 1), n v = v) ∧ ∀ m ∈ S.Nof g, S.psiOf g gs n = L.psi0 (algebraMap F E S.th⁻¹ * (S.h x (gs j) * S.h (m (g j.succ)) u)) := by
  intro F _ _ _ _ _ E _ _ _ L r k S g gs hg j x u s hx hu hs
  have hgram : ∀ a b : Fin (r + 1), (b : ℕ) < r → hf L S.Hm (g a) (g b) = 0 := by
    intro a b hb
    have hb' : b ≠ Fin.last r := fun h => by simp [h] at hb
    rcases hg with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · rw [S.gram]; simp [hb']
    · rw [S.gram']; simp [hb']
  have hdual : ∀ a i, hf L S.Hm (g a) (gs i) = if a = i.castSucc then 1 else 0 := by
    intro a i
    rcases hg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact S.dual a i
    · exact S.dual' a i
  have hjr : (j : ℕ) + 1 ≤ r := j.2
  have hgX : ∀ a, ∀ y ∈ S.spanTo g r, hf L S.Hm (g a) y = 0 := fun a y hy =>
    hf_symm0 S (hf_spanTo S g _ (fun i hi => hf_symm0 S (hgram a i hi)) hy)
  have hXX : ∀ {c : ℕ}, ∀ v ∈ S.spanTo g c, v ∈ perp L S.Hm (S.spanTo g r) := fun v hv y hy =>
    hf_spanTo S g y (fun i _ => hgX i y hy) hv
  have hxr : x ∈ S.spanTo g r := spanTo_mono S g hjr hx
  have hE : ∀ (u : S.V) (s : E), ∀ v ∈ perp L S.Hm (S.spanTo g r),
      eich L S.Hm x u s v - v = hf L S.Hm v u • x := by
    intro u s v hv
    simp only [eich, hv x hxr]
    module
  have hfl : ∀ u ∈ perp L S.Hm (S.spanTo g (j + 1)), ∀ (s : E) (i : ℕ), ∀ v ∈ S.spanTo g (i + 1),
      eich L S.Hm x u s v - v ∈ S.spanTo g i := by
    intro u hu s i v hv
    rw [hE u s v (hXX v hv)]
    rcases le_or_gt i j with h | h
    · rw [hf_symm0 S (hu v (spanTo_mono S g (by omega) hv)), zero_smul]
      exact Submodule.zero_mem _
    · exact Submodule.smul_mem _ _ (spanTo_mono S g h hx)
  obtain ⟨n, hn, h1, h2⟩ := eichler_isometry L S.Hm S.herm x u s (hXX x hx x hxr) (hu x hx) hs
  refine ⟨n, ⟨⟨hn, ?_⟩, ?_⟩, h1, h2, ?_, ?_⟩
  · refine Subgroup.mem_iInf.2 fun i => ?_
    refine mem_unipOn (spanTo_mono S g (by omega)) n (fun v hv => ?_) (fun v hv => ?_)
    · rw [h1]; exact hfl u hu s i v hv
    · rw [h2]; exact hfl _ (Submodule.neg_mem _ hu) _ i v hv
  · refine mem_unipOn (fun v hv => hXX v hv) n (fun v hv => ?_) (fun v hv => ?_)
    · rw [h1, hE _ _ v hv]; exact Submodule.smul_mem _ _ hxr
    · rw [h2, hE _ _ v hv]; exact Submodule.smul_mem _ _ hxr
  · intro v hv
    have := hE u s v (hXX v hv)
    rw [hf_symm0 S (hu v hv), zero_smul, sub_eq_zero] at this
    rw [h1, this]
  · rintro m ⟨⟨-, hm1⟩, hm2⟩
    replace hm1 := Subgroup.mem_iInf.1 hm1
    have hm : m (g j.succ) - g j.succ ∈ S.spanTo g (j + 1) := by
      rcases hjr.lt_or_eq with h | h
      · exact (hm1 ⟨j + 1, h⟩).2 _ (mem_spanTo S g _ (by simp))
      · have := hm2.2 (g j.succ) (hgX _)
        exact spanTo_mono S g h.ge this
    have hmu : hf L S.Hm (m (g j.succ)) u = hf L S.Hm (g j.succ) u := by
      have := hf_symm0 S (hu _ hm)
      rwa [hf_sub_l, sub_eq_zero] at this
    have hc : ∀ i : Fin r, S.coef g gs n i = hf L S.Hm x (gs i) * hf L S.Hm (g i.succ) u := by
      intro i
      have h3 := hE u s (g i.succ) (hgX _)
      rw [sub_eq_iff_eq_add, ← h1] at h3
      have h4 : i.succ ≠ i.castSucc := (Fin.castSucc_lt_succ).ne'
      simp only [Frames.coef, Frames.h]
      rw [h3, hf_add_l, hf_smul_l, hdual, if_neg h4]
      ring
    have hsum : ∑ i, S.coef g gs n i = S.h x (gs j) * S.h (m (g j.succ)) u := by
      simp only [Frames.h]
      rw [Finset.sum_eq_single j, hc, hmu]
      · intro i _ hij
        rw [hc]
        rcases lt_or_gt_of_ne hij with h | h
        · have h' : (i : ℕ) < j := h
          rw [hf_symm0 S (hu _ (mem_spanTo S g i.succ (by simp; omega))), mul_zero]
        · have h' : (j : ℕ) < i := h
          rw [hf_spanTo S g (gs i) (fun a ha => ?_) hx, zero_mul]
          rw [hdual, if_neg]
          rintro rfl
          simp at ha
          omega
      · simp
    simp only [Frames.psiOf, hsum]

end GlobalTheory.HL.EichlerUnip
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EichlerMapMemUnipotentCharacterStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eichler_map_mem_unipotent_character : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (g : Fin (r + 1) → S.V) (gs : Fin r → S.V), (g = S.f ∧ gs = S.es) ∨ (g = S.f' ∧ gs = S.es') → ∀ (j : Fin r) (x u : S.V) (s : E), x ∈ S.spanTo g (j + 1) → u ∈ perp L S.Hm (S.spanTo g (j + 1)) → s + L.cj s = S.h u u → ∃ n ∈ S.Nof g, (∀ v, n v = eich L S.Hm x u s v) ∧ (∀ v, n⁻¹ v = eich L S.Hm x (-u) (L.cj s) v) ∧ (∀ v ∈ S.spanTo g (j + 1), n v = v) ∧ ∀ m ∈ S.Nof g, S.psiOf g gs n = L.psi0 (algebraMap F E S.th⁻¹ * (S.h x (gs j) * S.h (m (g j.succ)) u)) := by
  first | exact @GlobalTheory.HL.EichlerUnip.eichler_mem_unip | exact GlobalTheory.HL.EichlerUnip.eichler_mem_unip | (intros; apply GlobalTheory.HL.EichlerUnip.eichler_mem_unip <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SqNormSumRepsMulIndexLe
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical ComplexConjugate

namespace GlobalTheory.HL.GaussSum

theorem sq_norm_sum_mul_index_le {G : Type*} [AddCommGroup G] [Fintype G] (Q : AddSubgroup G)
    (f : G → ℂ) (hf : ∀ u, ‖f u‖ = 1)
    (hQ : ∀ h, h ∉ Q → ∃ (v : G) (c : ℂ), c ≠ 1 ∧
      ∀ u, f (u + v + h) * conj (f (u + v)) = c * (f (u + h) * conj (f u))) :
    ‖∑ u, f u‖ ^ 2 * (Q.index : ℝ) ≤ (Fintype.card G : ℝ) ^ 2 := by
  classical
  have hzero : ∀ h, h ∉ Q → ∑ u, f (u + h) * conj (f u) = 0 := by
    intro h hh
    obtain ⟨v, c, hc, hrel⟩ := hQ h hh
    have h1 : ∑ u, f (u + h) * conj (f u) = c * ∑ u, f (u + h) * conj (f u) := by
      rw [Finset.mul_sum]
      calc ∑ u, f (u + h) * conj (f u) = ∑ u, f (u + v + h) * conj (f (u + v)) :=
            (Fintype.sum_equiv (Equiv.addRight v) (fun u => f (u + v + h) * conj (f (u + v)))
              (fun u => f (u + h) * conj (f u)) (fun u => rfl)).symm
        _ = ∑ u, c * (f (u + h) * conj (f u)) := Finset.sum_congr rfl fun u _ => hrel u
    have h2 : (1 - c) * ∑ u, f (u + h) * conj (f u) = 0 := by
      rw [sub_mul, one_mul, ← h1, sub_self]
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd (sub_eq_zero.mp h3).symm hc
    · exact h3
  have hexp : (∑ u, f u) * conj (∑ u, f u) = ∑ h, ∑ u, f (u + h) * conj (f u) := by
    calc (∑ u, f u) * conj (∑ u, f u) = ∑ w, ∑ u, f w * conj (f u) := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum, Finset.sum_mul_sum]
      _ = ∑ u, ∑ w, f w * conj (f u) := Finset.sum_comm
      _ = ∑ u, ∑ h, f (u + h) * conj (f u) := Finset.sum_congr rfl fun u _ =>
          (Fintype.sum_equiv (Equiv.addLeft u) (fun h => f (u + h) * conj (f u))
            (fun w => f w * conj (f u)) (fun h => rfl)).symm
      _ = ∑ h, ∑ u, f (u + h) * conj (f u) := Finset.sum_comm
  have hnorm : ‖∑ u, f u‖ ^ 2 ≤ (Fintype.card G : ℝ) * (Nat.card Q : ℝ) := by
    calc ‖∑ u, f u‖ ^ 2 = ‖(∑ u, f u) * conj (∑ u, f u)‖ := by
          rw [norm_mul, RCLike.norm_conj, sq]
      _ = ‖∑ h, ∑ u, f (u + h) * conj (f u)‖ := by rw [hexp]
      _ ≤ ∑ h, ‖∑ u, f (u + h) * conj (f u)‖ := norm_sum_le _ _
      _ ≤ ∑ h, (if h ∈ Q then (Fintype.card G : ℝ) else 0) := by
          refine Finset.sum_le_sum fun h _ => ?_
          split_ifs with hh
          · calc ‖∑ u, f (u + h) * conj (f u)‖ ≤ ∑ u, ‖f (u + h) * conj (f u)‖ :=
                  norm_sum_le _ _
              _ = ∑ _u : G, (1 : ℝ) := by simp [hf]
              _ = Fintype.card G := by simp
          · rw [hzero h hh, norm_zero]
      _ = (Fintype.card G : ℝ) * (Nat.card Q : ℝ) := by
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
            mul_comm]
          congr 1
          rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hci : (Nat.card Q : ℝ) * (Q.index : ℝ) = Fintype.card G := by
    rw [← Nat.card_eq_fintype_card, ← AddSubgroup.card_mul_index (H := Q)]
    push_cast
    ring
  calc ‖∑ u, f u‖ ^ 2 * (Q.index : ℝ) ≤ (Fintype.card G : ℝ) * Nat.card Q * Q.index :=
        mul_le_mul_of_nonneg_right hnorm (Nat.cast_nonneg _)
    _ = (Fintype.card G : ℝ) ^ 2 := by rw [mul_assoc, hci, sq]

theorem sq_norm_sum_reps_mul_index_le {M : Type*} [AddCommGroup M] (P Q : AddSubgroup M)
    (hPQ : P ≤ Q) (R : Finset M) (hR : ∀ u, ∃! w, w ∈ R ∧ u - w ∈ P)
    (f : M → ℂ) (hf : ∀ u, ‖f u‖ = 1) (hP : ∀ u, ∀ p ∈ P, f (u + p) = f u)
    (hQ : ∀ h, h ∉ Q → ∃ (v : M) (c : ℂ), c ≠ 1 ∧
      ∀ u, f (u + v + h) * conj (f (u + v)) = c * (f (u + h) * conj (f u))) :
    ‖∑ u ∈ R, f u‖ ^ 2 * (Q.index : ℝ) ≤ (R.card : ℝ) ^ 2 := by
  classical
  have hsurj : ∀ x : M ⧸ P, ∃ w ∈ R, (w : M ⧸ P) = x := by
    intro x
    obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective x
    obtain ⟨w, ⟨hwR, hw⟩, -⟩ := hR u
    refine ⟨w, hwR, ?_⟩
    rw [QuotientAddGroup.eq]
    have e : -w + u = u - w := by abel
    rw [e]
    exact hw
  have hinj : ∀ w ∈ R, ∀ w' ∈ R, (w : M ⧸ P) = w' → w = w' := by
    intro w hw w' hw' h
    rw [QuotientAddGroup.eq] at h
    obtain ⟨z, -, hz⟩ := hR w
    have h1 : w = z := hz w ⟨hw, by simp⟩
    have h2 : w' = z := hz w' ⟨hw', by
      rw [show w - w' = -(-w + w') by abel]
      exact P.neg_mem h⟩
    rw [h1, h2]
  have : Finite (M ⧸ P) := by
    apply Finite.of_surjective (fun w : R => ((w : M) : M ⧸ P))
    intro x
    obtain ⟨w, hw, rfl⟩ := hsurj x
    exact ⟨⟨w, hw⟩, rfl⟩
  let : Fintype (M ⧸ P) := Fintype.ofFinite _
  have hf' : ∀ u : M, f ((u : M ⧸ P)).out = f u := by
    intro u
    have h := QuotientAddGroup.eq.mp (QuotientAddGroup.out_eq' (u : M ⧸ P))
    have e := hP ((u : M ⧸ P)).out _ h
    rw [add_neg_cancel_left] at e
    exact e.symm
  have h1 := GlobalTheory.HL.GaussSum.sq_norm_sum_mul_index_le (Q.map (QuotientAddGroup.mk' P))
    (fun x : M ⧸ P => f x.out) (fun x => hf _) (by
      intro h' hh'
      obtain ⟨h, rfl⟩ := QuotientAddGroup.mk_surjective h'
      have hhQ : h ∉ Q := fun hq => hh' (AddSubgroup.mem_map_of_mem _ hq)
      obtain ⟨v, c, hc, hrel⟩ := hQ h hhQ
      refine ⟨(v : M ⧸ P), c, hc, fun x => ?_⟩
      obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective x
      simp only [← QuotientAddGroup.mk_add, hf']
      exact hrel u)
  have hidx : (Q.map (QuotientAddGroup.mk' P)).index = Q.index :=
    AddSubgroup.index_map_eq (H := Q) (QuotientAddGroup.mk'_surjective P)
      (by rw [QuotientAddGroup.ker_mk']; exact hPQ)
  have hi1 : ∀ a ∈ R, ((a : M ⧸ P)) ∈ (Finset.univ : Finset (M ⧸ P)) :=
    fun _ _ => Finset.mem_univ _
  have hi2 : Set.InjOn (fun a : M => (a : M ⧸ P)) R := by
    intro w hw w' hw' h
    exact hinj w hw w' hw' h
  have hi3 : Set.SurjOn (fun a : M => (a : M ⧸ P)) R (↑(Finset.univ : Finset (M ⧸ P)) : Set (M ⧸ P)) := by
    intro x _
    obtain ⟨w, hw, rfl⟩ := hsurj x
    exact ⟨w, hw, rfl⟩
  have hsum : ∑ u ∈ R, f u = ∑ x : M ⧸ P, f x.out :=
    Finset.sum_nbij (fun a : M => (a : M ⧸ P)) hi1 hi2 hi3 (fun u _ => (hf' u).symm)
  have hcard : R.card = Fintype.card (M ⧸ P) := by
    rw [← Finset.card_univ]
    exact Finset.card_nbij (fun a : M => (a : M ⧸ P)) hi1 hi2 hi3
  rw [hsum, hcard, ← hidx]
  exact h1

theorem mul_conj_eq {A : Type*} [AddCommGroup A] (ψ : AddChar A ℂ) (h : ∀ x, ‖ψ x‖ = 1) (x y : A) :
    ψ x * conj (ψ y) = ψ (x - y) := by
  rw [sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv, Complex.inv_def,
    Complex.normSq_eq_norm_sq, h y]
  simp

end GlobalTheory.HL.GaussSum
end
