module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TupleJacobianRightMulIsometry
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermIntegralNearOneBound
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFineSubgroupMovesAtLattice

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IndexIntegrableShareTopLevelVectors
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IndexIntegrableShareTopLevelVectors
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.TopLevelShare

theorem _root_.GlobalTheory.TopLevelShare.main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E), ∀ (r k : ℕ) (S : _root_.GlobalTheory.HL.Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → 1 ≤ βJ ∧ 1 ≤ β ∧ _root_.GlobalTheory.IdxInt.Nice (S.refB (j + 1) Λ) (_root_.GlobalTheory.IdxInt.ind fun b : S.V × S.V => b ∈ S.refB (j + 1) Λ ∧ S.lev (S.fr d Λ) (S.fr' d Λ) (b.1 + b.2) = j + 1) ∧ _root_.GlobalTheory.IdxInt.cint (S.refB (j + 1) Λ) (_root_.GlobalTheory.IdxInt.ind fun b : S.V × S.V => b ∈ S.refB (j + 1) Λ ∧ S.lev (S.fr d Λ) (S.fr' d Λ) (b.1 + b.2) = j + 1) = (βJ : ℂ) / (β : ℂ) := by
  intro F _ _ _ _ _ E _ _ _ L r k S j β βJ d Λ hT hF
  obtain ⟨-, hbe, hle, ⟨y₀, hy₀, hy₀l⟩, hJ⟩ := hF
  obtain ⟨-, -, hMsat, -⟩ := _root_.GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT
  obtain ⟨-, -, -, -, -, ⟨i, -, hq⟩, -, -, -, -, hlev⟩ := _root_.GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ hT
  have hth : S.th ≠ 0 := (_root_.GlobalTheory.FrameBasic.main L r k S).2.2.2.2.2.1
  set A := S.refB (↑j + 1) Λ with hAdef
  have hA : ∀ b : S.V × S.V, b ∈ A ↔ b.1 ∈ S.spanTo S.f (↑j + 1) ∧ b.2 ∈ S.spanTo S.f' (↑j + 1) ∧ ∃ y ∈ Λ, S.th • y = b.1 + b.2 := by
    intro b
    simp [hAdef, _root_.GlobalTheory.HL.Frames.refB, AddSubgroup.mem_prod, and_assoc]
  have hlevC : ∀ y, S.levC d Λ y = S.lev (S.fr d Λ) (S.fr' d Λ) (S.th • y) := by
    intro y
    simp [_root_.GlobalTheory.HL.Frames.levC]
  have hsat : ∀ y, y ∈ S.sat Λ ↔ y ∈ Λ ∧ y ∈ S.spanTo S.f (r + 1) ⊔ S.spanTo S.f' (r + 1) := by
    intro y
    show y ∈ Λ ⊓ S.ME.restrictScalars L.O ↔ _
    rw [Submodule.mem_inf, Submodule.restrictScalars_mem]
    rfl
  have hbe' : S.be d Λ = (S.M d Λ).toAddSubgroup.relIndex (S.sat Λ).toAddSubgroup := rfl
  have hq0 : S.q ≠ 0 := by
    have hirr := S.ϖ_irr
    show _root_.GlobalTheory.HL.resQ S.ϖ ≠ 0
    unfold _root_.GlobalTheory.HL.resQ
    rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hirr]
    exact (Nat.card_pos (α := IsLocalRing.ResidueField (ValuativeRel.valuation F).integer)).ne'
  have hβ0 : β ≠ 0 := by rw [← hbe, hq]; exact pow_ne_zero _ hq0
  set π : S.V × S.V → S.V := fun b => S.th⁻¹ • (b.1 + b.2) with hπdef
  have hπsmul : ∀ b, S.th • π b = b.1 + b.2 := fun b => smul_inv_smul₀ hth _
  have hπadd : ∀ a b, π (a + b) = π a + π b := by
    intro a b
    simp only [hπdef, Prod.fst_add, Prod.snd_add, ← smul_add, add_add_add_comm]
  have hπsub : ∀ a b, π (a - b) = π a - π b := by
    intro a b
    simp only [hπdef, Prod.fst_sub, Prod.snd_sub, ← smul_sub, sub_add_sub_comm]
  have hπA : ∀ b ∈ A, π b ∈ S.sat Λ := by
    intro b hb
    obtain ⟨h1, h2, y, hy, hyb⟩ := (hA b).1 hb
    have hjr : (↑j + 1 : ℕ) ≤ r + 1 := by omega
    rw [hsat]
    refine ⟨?_, ?_⟩
    · rw [hπdef]; dsimp only; rw [← hyb, inv_smul_smul₀ hth]; exact hy
    · refine Submodule.smul_of_tower_mem _ _ (add_mem ?_ ?_)
      · exact Submodule.mem_sup_left (_root_.GlobalTheory.HL.FrameOnto.spanTo_mono S S.f hjr h1)
      · exact Submodule.mem_sup_right (_root_.GlobalTheory.HL.FrameOnto.spanTo_mono S S.f' hjr h2)
  have hlevπ : ∀ b : S.V × S.V, S.lev (S.fr d Λ) (S.fr' d Λ) (b.1 + b.2) = S.levC d Λ (π b) := by
    intro b; rw [hlevC, hπsmul]
  have hinv : ∀ y ∈ S.sat Λ, ∀ m ∈ S.M d Λ, S.levC d Λ (y + m) = S.levC d Λ y := by
    intro y hy m hm
    have key : ∀ n : ℕ, S.levC d Λ (y + m) ≤ n ↔ S.levC d Λ y ≤ n := by
      intro n
      rw [hlev _ (add_mem hy (hMsat hm)), hlev _ hy]
      constructor
      · rintro ⟨y₁, h₁, h₂⟩
        exact ⟨y₁, h₁, by simpa [add_sub_right_comm] using sub_mem h₂ hm⟩
      · rintro ⟨y₁, h₁, h₂⟩
        exact ⟨y₁, h₁, by simpa [add_sub_right_comm] using add_mem h₂ hm⟩
    exact le_antisymm ((key _).2 le_rfl) ((key _).1 le_rfl)
  set B : AddSubgroup (S.V × S.V) := A ⊓ AddSubgroup.comap (AddMonoidHom.fst S.V S.V + AddMonoidHom.snd S.V S.V) ((S.M d Λ).toAddSubgroup.map (DistribSMul.toAddMonoidHom S.V S.th)) with hBdef
  have hB : ∀ b, b ∈ B ↔ b ∈ A ∧ π b ∈ S.M d Λ := by
    intro b
    rw [hBdef, AddSubgroup.mem_inf]
    refine and_congr_right fun _ => ?_
    simp only [AddSubgroup.mem_comap, AddSubgroup.mem_map, AddMonoidHom.add_apply, AddMonoidHom.coe_fst, AddMonoidHom.coe_snd, DistribSMul.toAddMonoidHom_apply, Submodule.mem_toAddSubgroup]
    constructor
    · rintro ⟨m, hm, hmb⟩
      rw [hπdef]; dsimp only; rw [← hmb, inv_smul_smul₀ hth]; exact hm
    · intro h
      exact ⟨π b, h, hπsmul b⟩
  have hsatΛ : ∀ y ∈ S.sat Λ, y ∈ Λ := fun y hy => ((hsat y).1 hy).1
  have hlift : ∀ y ∈ S.sat Λ, ∃ b ∈ A, y - π b ∈ S.M d Λ := by
    intro y hy
    obtain ⟨y₁, hy₁U, hyM⟩ := (hlev y hy (↑j + 1)).1 (hle y hy)
    have hy₁Λ : y₁ ∈ Λ := by simpa using sub_mem (hsatΛ y hy) (hsatΛ _ (hMsat hyM))
    obtain ⟨u₁, hu₁, u₂, hu₂, hu⟩ := Submodule.mem_sup.1 (Submodule.smul_of_tower_mem _ S.th hy₁U)
    refine ⟨(u₁, u₂), (hA _).2 ⟨hu₁, hu₂, y₁, hy₁Λ, hu.symm⟩, ?_⟩
    have : π (u₁, u₂) = y₁ := by
      rw [hπdef]; dsimp only; rw [hu, inv_smul_smul₀ hth]
    rw [this]; exact hyM
  set K := (S.M d Λ).toAddSubgroup.addSubgroupOf (S.sat Λ).toAddSubgroup with hKdef
  let πA : A →+ (S.sat Λ).toAddSubgroup :=
    { toFun := fun b => ⟨π b, hπA b b.2⟩
      map_zero' := Subtype.ext (by simp [hπdef])
      map_add' := fun a b => Subtype.ext (hπadd a b) }
  let g : A →+ (S.sat Λ).toAddSubgroup ⧸ K := (QuotientAddGroup.mk' K).comp πA
  have hg : ∀ a : A, g a = QuotientAddGroup.mk (⟨π a, hπA a a.2⟩ : (S.sat Λ).toAddSubgroup) := fun a => rfl
  have hsurj : Function.Surjective g := by
    intro c
    obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientAddGroup.mk_surjective c
    obtain ⟨b, hb, hbM⟩ := hlift y hy
    refine ⟨⟨b, hb⟩, ?_⟩
    rw [hg, QuotientAddGroup.eq, hKdef, AddSubgroup.mem_addSubgroupOf]
    simpa [neg_add_eq_sub] using hbM
  have hker : g.ker = B.addSubgroupOf A := by
    ext a
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, hB, hg, QuotientAddGroup.eq_zero_iff, hKdef, AddSubgroup.mem_addSubgroupOf]
    simp
  have hidx : B.relIndex A = β := by
    rw [← hbe, hbe', AddSubgroup.relIndex, AddSubgroup.relIndex, ← hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hsurj, AddSubgroup.card_top]
    rfl
  have hidx0 : B.relIndex A ≠ 0 := by rw [hidx]; exact hβ0
  haveI : Finite (A ⧸ B.addSubgroupOf A) := Nat.finite_of_card_ne_zero hidx0
  set φ := _root_.GlobalTheory.IdxInt.ind (fun b : S.V × S.V => b ∈ A ∧ S.lev (S.fr d Λ) (S.fr' d Λ) (b.1 + b.2) = ↑j + 1) with hφdef
  have hφval : ∀ w, φ w = if w ∈ A ∧ S.lev (S.fr d Λ) (S.fr' d Λ) (w.1 + w.2) = ↑j + 1 then 1 else 0 := by
    intro w
    rw [hφdef]
    unfold _root_.GlobalTheory.IdxInt.ind
    congr
  have hφinv : ∀ w b : S.V × S.V, b ∈ B → φ (w + b) = φ w := by
    intro w b hb
    obtain ⟨hbA, hbM⟩ := (hB b).1 hb
    have key : (w + b ∈ A ∧ S.lev (S.fr d Λ) (S.fr' d Λ) ((w + b).1 + (w + b).2) = ↑j + 1) ↔ (w ∈ A ∧ S.lev (S.fr d Λ) (S.fr' d Λ) (w.1 + w.2) = ↑j + 1) := by
      by_cases hw : w ∈ A
      · rw [hlevπ, hlevπ, hπadd, hinv _ (hπA w hw) _ hbM]
        simp [hw, add_mem hw hbA]
      · have hwb : w + b ∉ A := fun h => hw (by simpa using sub_mem h hbA)
        simp [hw, hwb]
    simp only [hφval, key]
  have hsupp : Function.support φ ⊆ A := by
    intro w hw
    by_contra h
    exact hw (by rw [hφval, if_neg (fun hc => h hc.1)])
  have hfin : ((fun w : S.V × S.V => (w : (S.V × S.V) ⧸ B)) '' Function.support φ).Finite := by
    let h : A ⧸ B.addSubgroupOf A →+ (S.V × S.V) ⧸ B := QuotientAddGroup.map (B.addSubgroupOf A) B A.subtype (fun x hx => hx)
    refine (Set.finite_range h).subset ?_
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨QuotientAddGroup.mk ⟨w, hsupp hw⟩, rfl⟩
  have hfine : _root_.GlobalTheory.IdxInt.Fine A φ B := ⟨inf_le_left, hidx0, hφinv, hfin⟩
  set T : Set ((S.V × S.V) ⧸ B) := {c | Quotient.out c ∈ A ∧ S.lev (S.fr d Λ) (S.fr' d Λ) ((Quotient.out c).1 + (Quotient.out c).2) = ↑j + 1} with hTdef
  have hTsub : T ⊆ (fun w : S.V × S.V => (w : (S.V × S.V) ⧸ B)) '' Function.support φ := by
    intro c hc
    refine ⟨Quotient.out c, ?_, QuotientAddGroup.out_eq' c⟩
    simp [Function.mem_support, hφval, hc.1, hc.2]
  have hTfin : T.Finite := hfin.subset hTsub
  have hsum : ∑ᶠ c : (S.V × S.V) ⧸ B, φ (Quotient.out c) = (T.ncard : ℂ) := by
    calc ∑ᶠ c : (S.V × S.V) ⧸ B, φ (Quotient.out c) = ∑ᶠ c ∈ T, (1 : ℂ) := by
          rw [finsum_mem_def]
          refine finsum_congr fun c => ?_
          simp only [hφval, Set.indicator, hTdef, Set.mem_setOf_eq]
      _ = T.ncard := by
          rw [finsum_mem_eq_finite_toFinset_sum _ hTfin, Finset.sum_const, nsmul_eq_mul, mul_one, Set.ncard_eq_toFinset_card T hTfin]
  have hout : ∀ b : S.V × S.V, Quotient.out (b : (S.V × S.V) ⧸ B) - b ∈ B := by
    intro b
    have h := QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' (b : (S.V × S.V) ⧸ B))
    rw [neg_add_eq_sub, ← neg_sub] at h
    simpa using B.neg_mem h
  set fC : (S.V × S.V) ⧸ B → Set S.V := fun c => {x | x - π (Quotient.out c) ∈ S.M d Λ} with hfCdef
  have himage : fC '' T = {C | ∃ y ∈ S.sat Λ, S.levC d Λ y = ↑j + 1 ∧ C = {x | x - y ∈ S.M d Λ}} := by
    ext C
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨π (Quotient.out c), hπA _ hc.1, (hlevπ _).symm.trans hc.2, rfl⟩
    · rintro ⟨y, hy, hyl, rfl⟩
      obtain ⟨b, hb, hbM⟩ := hlift y hy
      obtain ⟨h₁, h₂⟩ := (hB _).1 (hout b)
      have hoA : Quotient.out (b : (S.V × S.V) ⧸ B) ∈ A := by simpa using add_mem h₁ hb
      rw [hπsub] at h₂
      have hyo : y - π (Quotient.out (b : (S.V × S.V) ⧸ B)) ∈ S.M d Λ := by
        have := sub_mem hbM h₂
        rwa [sub_sub_sub_cancel_right] at this
      refine ⟨(b : (S.V × S.V) ⧸ B), ⟨hoA, ?_⟩, ?_⟩
      · have := hinv _ (hπA _ hoA) _ hyo
        rw [add_sub_cancel] at this
        rw [hlevπ, ← this, hyl]
      · ext x
        simp only [hfCdef, Set.mem_setOf_eq]
        constructor
        · intro hx
          have := sub_mem hx hyo
          rwa [sub_sub_sub_cancel_right] at this
        · intro hx
          have := add_mem hx hyo
          rwa [sub_add_sub_cancel] at this
  have hinj : Set.InjOn fC T := by
    intro c₁ hc₁ c₂ hc₂ heq
    have hmem : π (Quotient.out c₁) ∈ fC c₁ := by
      show π (Quotient.out c₁) - π (Quotient.out c₁) ∈ S.M d Λ
      rw [sub_self]; exact zero_mem _
    rw [heq] at hmem
    have hB₁₂ : Quotient.out c₁ - Quotient.out c₂ ∈ B :=
      (hB _).2 ⟨sub_mem hc₁.1 hc₂.1, by rw [hπsub]; exact hmem⟩
    rw [← QuotientAddGroup.out_eq' c₁, ← QuotientAddGroup.out_eq' c₂, QuotientAddGroup.eq, neg_add_eq_sub, ← neg_sub]
    exact B.neg_mem hB₁₂
  have hcount : T.ncard = βJ := by
    rw [← hJ]
    unfold _root_.GlobalTheory.HL.Frames.nLev
    rw [← himage, Set.InjOn.ncard_image hinj]
  have hTne : T.Nonempty := by
    have : (fC '' T).Nonempty := by
      rw [himage]; exact ⟨_, y₀, hy₀, hy₀l, rfl⟩
    exact Set.image_nonempty.1 this
  refine ⟨?_, Nat.one_le_iff_ne_zero.2 hβ0, ⟨B, hfine⟩, ?_⟩
  · rw [← hcount]
    exact (Set.ncard_pos hTfin).2 hTne
  · rw [_root_.GlobalTheory.IdxInt.cint_eq_of_fine A B φ hfine, hsum, hcount, hidx]

end GlobalTheory.TopLevelShare
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IndexIntegrableShareTopLevelVectorsStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indexIntegrable_share_top_level_vectors : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → 1 ≤ βJ ∧ 1 ≤ β ∧ Nice (S.refB (j + 1) Λ) (ind fun b : S.V × S.V => b ∈ S.refB (j + 1) Λ ∧ S.lev (S.fr d Λ) (S.fr' d Λ) (b.1 + b.2) = j + 1) ∧ cint (S.refB (j + 1) Λ) (ind fun b : S.V × S.V => b ∈ S.refB (j + 1) Λ ∧ S.lev (S.fr d Λ) (S.fr' d Λ) (b.1 + b.2) = j + 1) = (βJ : ℂ) / (β : ℂ) := by
  first | exact @GlobalTheory.TopLevelShare.main | exact GlobalTheory.TopLevelShare.main | (intros; apply GlobalTheory.TopLevelShare.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EichlerMoveScalarFibreMeasureOne
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EichlerMoveScalarFibreMeasureOne
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.MoveFibre

theorem cint_coset {W : Type} [AddCommGroup W] (A : AddSubgroup W) (P : W → Prop) (t₀ : W)
    (hP : ∀ t, P t ↔ t - t₀ ∈ A) : cint A (ind P) = 1 := by
  have hN : Nice A (ind P) := by
    refine ⟨A, le_rfl, by simp, fun w b hb => ?_, ?_⟩
    · have : P (w + b) ↔ P w := by
        rw [hP, hP, show w + b - t₀ = w - t₀ + b by abel]
        exact A.add_mem_cancel_right hb
      simp only [ind, this]
    · refine (Set.finite_singleton (QuotientAddGroup.mk t₀ : W ⧸ A)).subset ?_
      rintro _ ⟨w, hw, rfl⟩
      have h1 : P w := by
        by_contra h
        exact hw (by simp [ind, h])
      rw [Set.mem_singleton_iff, eq_comm, QuotientAddGroup.eq, neg_add_eq_sub]
      exact (hP w).1 h1
  rw [cint, dite_eq_left hN]
  obtain ⟨hle, hidx, -, -⟩ := hN.choose_spec
  generalize hN.choose = B at hle hidx
  let g : A ⧸ B.addSubgroupOf A → W ⧸ B := fun x =>
    Quotient.liftOn' x (fun a : A => (QuotientAddGroup.mk (t₀ + a) : W ⧸ B)) (fun a b hab => by
      rw [QuotientAddGroup.leftRel_apply, AddSubgroup.mem_addSubgroupOf] at hab
      rw [QuotientAddGroup.eq]
      convert hab using 1
      push_cast; abel)
  have hg : ∀ a : A, g (QuotientAddGroup.mk a) = QuotientAddGroup.mk (t₀ + a) := fun _ => rfl
  have hinj : Function.Injective g := by
    intro x y
    induction x using QuotientAddGroup.induction_on with | H a => ?_
    induction y using QuotientAddGroup.induction_on with | H b => ?_
    intro h
    rw [hg, hg, QuotientAddGroup.eq] at h
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    convert h using 1
    push_cast; abel
  have hr : ∀ c : W ⧸ B, P c.out ↔ c ∈ Set.range g := by
    intro c
    rw [hP]
    constructor
    · intro h
      exact ⟨QuotientAddGroup.mk ⟨_, h⟩, by rw [hg]; simp⟩
    · rintro ⟨x, hx⟩
      induction x using QuotientAddGroup.induction_on with | H a => ?_
      rw [hg, ← c.out_eq, QuotientAddGroup.eq] at hx
      have := A.add_mem (hle hx) a.2
      convert this using 1
      abel
  have hfin : Finite (A ⧸ B.addSubgroupOf A) := Nat.finite_of_card_ne_zero hidx
  have := Fintype.ofFinite (A ⧸ B.addSubgroupOf A)
  have hs : (∑ᶠ c : W ⧸ B, ind P c.out) = ∑ᶠ c ∈ Set.range g, (1 : ℂ) := by
    refine finsum_congr fun c => ?_
    rw [finsum_eq_if]
    simp only [ind, hr]
  rw [hs, finsum_mem_range hinj, finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, ← Nat.card_eq_fintype_card]
  exact div_self (Nat.cast_ne_zero.2 hidx)

theorem cj_hf_self {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) {n : ℕ}
    {Hm : Matrix (Fin n) (Fin n) E} (h : IsHerm L Hm) (u : Fin n → E) :
    L.cj (hf L Hm u u) = hf L Hm u u := by
  have h1 : ∀ i j, L.cj (Hm i j) = Hm j i := fun i j => congrFun (congrFun h j) i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hf, map_sum, map_mul, L.cj_cj, h1]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem fibre_scalar : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 0 ≤ S.a → ∀ u : S.V, (S.InZ u → cint S.refT (ind fun t : E => (∃ c ∈ L.O, algebraMap F E 2⁻¹ * S.h u u + t = algebraMap F E ((S.ϖ : F) ^ S.a) * c) ∧ t + L.cj t = 0) = 1) ∧ ((∃ t : E, (∃ c ∈ L.O, algebraMap F E 2⁻¹ * S.h u u + t = algebraMap F E ((S.ϖ : F) ^ S.a) * c) ∧ t + L.cj t = 0) → S.InZ u) := by
  intro F _ _ _ _ _ E _ _ _ L r k S _ u
  obtain ⟨htr, hO, -⟩ := GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr
  have hfix : L.cj (S.h u u) = S.h u u := cj_hf_self L S.herm.1 u
  have h2 : algebraMap F E 2⁻¹ * 2 = 1 := by
    rw [← map_ofNat (algebraMap F E) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]
  have hT : ∀ t, t ∈ S.refT ↔ t + L.cj t = 0 ∧
      ∃ c ∈ L.O, algebraMap F E ((S.ϖ : F) ^ S.a) * c = t := fun t => Iff.rfl
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨x, hx, hxc⟩ := htr c
    rw [map_mul, ← hxc] at hc
    refine cint_coset _ _
      (algebraMap F E ((S.ϖ : F) ^ S.a) * x - algebraMap F E 2⁻¹ * S.h u u) fun t => ?_
    rw [hT]
    simp only [map_sub L.cj, map_mul L.cj, AlgEquiv.commutes, hfix]
    constructor
    · rintro ⟨⟨y, hy, e⟩, ht⟩
      exact ⟨by linear_combination ht + hc + S.h u u * h2,
        y - x, L.O.sub_mem hy hx, by linear_combination -e⟩
    · rintro ⟨ht, y, hy, e⟩
      exact ⟨⟨y + x, L.O.add_mem hy hx, by linear_combination -e⟩,
        by linear_combination ht - hc - S.h u u * h2⟩
  · rintro ⟨t, ⟨y, hy, e⟩, ht⟩
    obtain ⟨c, hc⟩ := (hO y hy).2.1
    refine ⟨c, ?_⟩
    have e' := congrArg L.cj e
    simp only [map_add L.cj, map_mul L.cj, AlgEquiv.commutes, hfix] at e'
    rw [map_mul, ← hc]
    linear_combination e + e' - ht - S.h u u * h2

end GlobalTheory.MoveFibre
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EichlerMoveScalarFibreMeasureOneStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eichlerMove_scalar_fibre_measure_one : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 0 ≤ S.a → ∀ u : S.V, (S.InZ u → cint S.refT (ind fun t : E => (∃ c ∈ L.O, algebraMap F E 2⁻¹ * S.h u u + t = algebraMap F E ((S.ϖ : F) ^ S.a) * c) ∧ t + L.cj t = 0) = 1) ∧ ((∃ t : E, (∃ c ∈ L.O, algebraMap F E 2⁻¹ * S.h u u + t = algebraMap F E ((S.ϖ : F) ^ S.a) * c) ∧ t + L.cj t = 0) → S.InZ u) := by
  first | exact @GlobalTheory.MoveFibre.fibre_scalar | exact GlobalTheory.MoveFibre.fibre_scalar | (intros; apply GlobalTheory.MoveFibre.fibre_scalar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IndexMeasureIntegralProdFubini
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IndexMeasureIntegralProdFubini
open GlobalTheory.IdxInt
open scoped Pointwise Classical

namespace GlobalTheory.IdxInt.Fubini

variable {W : Type} [AddCommGroup W] {W' : Type} [AddCommGroup W']

lemma relIndex_prod (H K : AddSubgroup W) (H' K' : AddSubgroup W') :
    (H.prod H').relIndex (K.prod K') = H.relIndex K * H'.relIndex K' := by
  unfold AddSubgroup.relIndex
  rw [← AddSubgroup.index_prod,
    ← AddSubgroup.index_comap_of_surjective ((H.addSubgroupOf K).prod (H'.addSubgroupOf K'))
      (f := (AddSubgroup.prodEquiv K K').toAddMonoidHom) (AddSubgroup.prodEquiv K K').surjective]
  congr 1

lemma exists_fine_prod {A : AddSubgroup W} {A' : AddSubgroup W'} {φ : W × W' → ℂ}
    (h : Nice (A.prod A') φ) :
    ∃ (B : AddSubgroup W) (B' : AddSubgroup W'), B ≤ A ∧ B' ≤ A' ∧ B.relIndex A ≠ 0 ∧
      B'.relIndex A' ≠ 0 ∧ Fine (A.prod A') φ (B.prod B') := by
  obtain ⟨C, hC⟩ := h
  have i1 : (C.comap (AddMonoidHom.inl W W')).relIndex A ≠ 0 := by
    rw [AddSubgroup.relIndex_comap]
    intro z
    refine hC.2.1 (AddSubgroup.relIndex_eq_zero_of_le_right ?_ z)
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨ha, A'.zero_mem⟩
  have i2 : (C.comap (AddMonoidHom.inr W W')).relIndex A' ≠ 0 := by
    rw [AddSubgroup.relIndex_comap]
    intro z
    refine hC.2.1 (AddSubgroup.relIndex_eq_zero_of_le_right ?_ z)
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨A.zero_mem, ha⟩
  refine ⟨C.comap (AddMonoidHom.inl W W'), C.comap (AddMonoidHom.inr W W'),
    fun a ha => (hC.1 ha).1, fun a ha => (hC.1 ha).2, i1, i2, Model.fine_refine hC ?_ ?_⟩
  · rintro ⟨a, b⟩ ⟨ha, hb⟩
    have := C.add_mem ha hb
    simpa using this
  · rw [relIndex_prod]
    exact mul_ne_zero i1 i2

theorem cint_prod (A : AddSubgroup W) (A' : AddSubgroup W') (φ : W × W' → ℂ)
    (h : Nice (A.prod A') φ) :
    (∀ w, Nice A' (fun w' => φ (w, w'))) ∧ Nice A (fun w => cint A' (fun w' => φ (w, w'))) ∧
      cint (A.prod A') φ = cint A (fun w => cint A' (fun w' => φ (w, w'))) := by
  obtain ⟨B, B', hB, hB', i1, i2, hF⟩ := exists_fine_prod h
  let e := QuotientAddGroup.prodEquiv B B'
  have he : ∀ p : W × W', e (QuotientAddGroup.mk p) =
      ((QuotientAddGroup.mk p.1 : W ⧸ B), (QuotientAddGroup.mk p.2 : W' ⧸ B')) := fun _ => rfl
  have hS := hF.2.2.2.image e
  have f1 : ∀ w, Fine A' (fun w' => φ (w, w')) B' := by
    intro w
    refine ⟨hB', i2, fun w' b hb => ?_, (hS.image Prod.snd).subset ?_⟩
    · have := hF.2.2.1 (w, w') (0, b) ⟨B.zero_mem, hb⟩
      simpa using this
    · rintro _ ⟨w', hw', rfl⟩
      exact ⟨_, ⟨_, ⟨(w, w'), hw', rfl⟩, rfl⟩, rfl⟩
  have hinv : ∀ w, ∀ b ∈ B, (fun w' => φ (w + b, w')) = fun w' => φ (w, w') := by
    intro w b hb
    funext w'
    have := hF.2.2.1 (w, w') (b, 0) ⟨hb, B'.zero_mem⟩
    simpa using this
  have f2 : Fine A (fun w => cint A' (fun w' => φ (w, w'))) B := by
    refine ⟨hB, i1, fun w b hb => by simp only [hinv w b hb], (hS.image Prod.fst).subset ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    have : ∃ w', φ (w, w') ≠ 0 := by
      by_contra hn
      push Not at hn
      apply hw
      show cint A' (fun w' => φ (w, w')) = 0
      rw [Model.cint_eq (f1 w)]
      simp [hn]
    obtain ⟨w', hw'⟩ := this
    exact ⟨_, ⟨_, ⟨(w, w'), hw', rfl⟩, rfl⟩, rfl⟩
  refine ⟨fun w => ⟨B', f1 w⟩, ⟨B, f2⟩, ?_⟩
  rw [Model.cint_eq hF, Model.cint_eq f2, relIndex_prod]
  simp only [fun w => Model.cint_eq (f1 w)]
  have h1 : ∀ p : (W ⧸ B) × (W' ⧸ B'), φ (e.symm p).out = φ (p.1.out, p.2.out) := by
    intro p
    have : e.symm p = QuotientAddGroup.mk (p.1.out, p.2.out) := by
      rw [Equiv.symm_apply_eq, he]
      simp
    rw [this, Model.out_mk hF.2.2.1]
  have hfin : (Function.support fun p : (W ⧸ B) × (W' ⧸ B') => φ (p.1.out, p.2.out)).Finite := by
    refine hS.subset ?_
    intro p hp
    refine ⟨_, ⟨(p.1.out, p.2.out), hp, rfl⟩, ?_⟩
    rw [he]; simp
  have h2 : (∑ᶠ c : (W × W') ⧸ B.prod B', φ c.out) =
      ∑ᶠ (a : W ⧸ B) (b : W' ⧸ B'), φ (a.out, b.out) := by
    rw [← finsum_comp_equiv e.symm, finsum_congr h1, finsum_curry _ hfin]
  rw [h2]
  simp only [div_eq_mul_inv]
  rw [← finsum_mul]
  push_cast
  rw [mul_inv]
  ring

end GlobalTheory.IdxInt.Fubini
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IndexMeasureIntegralProdFubiniStatement
open GlobalTheory.IdxInt
open scoped Pointwise Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indexMeasureIntegral_prod_fubini : ∀ {W : Type} [AddCommGroup W] {W' : Type} [AddCommGroup W'] (A : AddSubgroup W) (A' : AddSubgroup W') (φ : W × W' → ℂ), Nice (A.prod A') φ → (∀ w, Nice A' (fun w' => φ (w, w'))) ∧ Nice A (fun w => cint A' (fun w' => φ (w, w'))) ∧ cint (A.prod A') φ = cint A (fun w => cint A' (fun w' => φ (w, w'))) := by
  first | exact @GlobalTheory.IdxInt.Fubini.cint_prod | exact GlobalTheory.IdxInt.Fubini.cint_prod | (intros; apply GlobalTheory.IdxInt.Fubini.cint_prod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianMovesTotalMeasureEstimates
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.MoveTotal
open GlobalTheory.HL.Eichler GlobalTheory.HL.FrameOnto

section abstract
variable {W W₁ W₂ W₃ : Type} [AddCommGroup W] [AddCommGroup W₁] [AddCommGroup W₂] [AddCommGroup W₃]

theorem cint_zero (A : AddSubgroup W) : cint A (fun _ => (0 : ℂ)) = 0 := by
  unfold cint
  split_ifs <;> simp

theorem nice_of_ne (A : AddSubgroup W) (φ : W → ℂ) (h : cint A φ ≠ 0) : Nice A φ := by
  by_contra hn
  exact h (by unfold cint; rw [dite_eq_right hn])

theorem fine_mul {A B : AddSubgroup W} {P : W → Prop} (h : Fine A (ind P) B) (g : W → ℂ)
    (hg : ∀ w, P w → ∀ b ∈ B, g (w + b) = g w) : Fine A (fun w => ind P w * g w) B := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, fun w b hb => ?_, h4.subset (Set.image_mono fun w hw => ?_)⟩
  · beta_reduce
    by_cases hw : P w
    · rw [h3 w b hb, hg w hw b hb]
    · rw [h3 w b hb]; simp [ind, hw]
  · exact left_ne_zero_of_mul hw

theorem triple (A₁ : AddSubgroup W₁) (A₂ : AddSubgroup W₂) (A₃ : AddSubgroup W₃) (P : W₁ → Prop)
    (Q Z : W₂ → Prop) (R : W₂ → W₃ → Prop) (M : W₁ × W₂ × W₃ → Prop)
    (hM : ∀ b u t, M (b, u, t) ↔ P b ∧ Q u ∧ R u t)
    (h1 : ∀ u, Z u → cint A₃ (ind (R u)) = 1) (h2 : ∀ u, (∃ t, R u t) → Z u) (g : W₁ → W₂ → ℂ)
    (hn : Nice (A₁.prod (A₂.prod A₃)) (fun w => ind M w * g w.1 w.2.1)) :
    Nice A₁ (fun b => ind P b * cint A₂ (fun u => ind (fun u => Q u ∧ Z u) u * g b u)) ∧
    cint (A₁.prod (A₂.prod A₃)) (fun w => ind M w * g w.1 w.2.1) =
      cint A₁ (fun b => ind P b * cint A₂ (fun u => ind (fun u => Q u ∧ Z u) u * g b u)) := by
  obtain ⟨k1, k2, k3⟩ := GlobalTheory.T.indexMeasureIntegral_prod_fubini _ _ _ hn
  have key : (fun b => cint (A₂.prod A₃) (fun w' => ind M (b, w') * g b w'.1)) =
      (fun b => ind P b * cint A₂ (fun u => ind (fun u => Q u ∧ Z u) u * g b u)) := by
    funext b
    rw [(GlobalTheory.T.indexMeasureIntegral_prod_fubini _ _ _ (k1 b)).2.2]
    by_cases hb : P b
    · rw [show ind P b = 1 by simp [ind, hb], one_mul]
      congr 1
      funext u
      by_cases hq : Q u
      · by_cases hz : Z u
        · have e : (fun t => ind M (b, u, t) * g b u) = fun t => g b u * ind (R u) t := by
            funext t; simp [ind, hM, hb, hq]
          have := ((GlobalTheory.T.indexMeasureIntegral_linear_positive_norm_bound A₃).2.1 (g b u) _ (nice_of_ne _ _ (by rw [h1 u hz]; simp))).2
          simp only
          rw [e, this, h1 u hz]
          simp [ind, hq, hz]
        · have e : (fun t => ind M (b, u, t) * g b u) = fun _ => 0 := by
            funext t
            have : ¬ R u t := fun h => hz (h2 u ⟨t, h⟩)
            simp [ind, hM, this]
          simp only
          rw [e, cint_zero]
          simp [ind, hz]
      · have e : (fun t => ind M (b, u, t) * g b u) = fun _ => 0 := by
          funext t
          simp [ind, hM, hq]
        simp only
        rw [e, cint_zero]
        simp [ind, hq]
    · have e : (fun u => cint A₃ (fun t => ind M (b, u, t) * g b u)) = fun _ => 0 := by
        funext u
        have e : (fun t => ind M (b, u, t) * g b u) = fun _ => 0 := by
          funext t
          simp [ind, hM, hb]
        rw [e, cint_zero]
      simp only
      rw [e, cint_zero]
      simp [ind, hb]
  simp only at k2 k3
  rw [key] at k2 k3
  exact ⟨k2, k3⟩

theorem cint_ind_mul (A : AddSubgroup W) (φ : W → ℂ) (h : Nice A φ) (c : ℂ) :
    cint A (fun w => φ w * c) = cint A φ * c := by
  simpa [mul_comm] using ((GlobalTheory.T.indexMeasureIntegral_linear_positive_norm_bound A).2.1 c φ h).2

theorem norm_le (A : AddSubgroup W) (P : W → Prop) (h : Nice A (ind P)) (φ : W → ℂ)
    (hφ : Nice A (fun w => ind P w * φ w)) (m : ℝ) (hm : ∀ w, P w → ‖φ w‖ ≤ m) :
    ‖cint A (fun w => ind P w * φ w)‖ ≤ m * (cint A (ind P)).re := by
  obtain ⟨e1, e2⟩ := (GlobalTheory.T.indexMeasureIntegral_linear_positive_norm_bound A).2.1 (m : ℂ) _ h
  have := ((GlobalTheory.T.indexMeasureIntegral_linear_positive_norm_bound A).1 _ _ hφ e1).2.2 fun w => by
    by_cases hw : P w
    · simpa [ind, hw] using hm w hw
    · simp [ind, hw]
  rw [e2] at this
  simpa using this

end abstract

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem exists_coords (g : Fin (r + 1) → S.V) (gs : Fin r → S.V)
    (dual : ∀ a j, hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)
    (n : S.GLV) (hn : n ∈ S.Nof g) (j : Fin r) (x : S.V) (hx : x ∈ S.spanTo g (j + 1)) :
    ∃ al : Fin (r + 1) → E, x = ∑ i, al i • n (g i) ∧ al j.castSucc = S.h x (gs j) := by
  have hu := Subgroup.mem_iInf.1 hn.1.2 j
  have hv : n.symm x ∈ S.spanTo g (j + 1) := (hu.1 _).1 (by simpa using hx)
  have hd := hu.2 _ hv
  obtain ⟨c, -, hc⟩ := coords S g hv
  refine ⟨c, ?_, ?_⟩
  · have := congrArg n hc
    simpa using this
  · have h0 : hf L S.Hm (n (n.symm x) - n.symm x) (gs j) = 0 :=
      hf_spanTo S g hd fun i hi => by
        rw [dual, if_neg]
        rintro rfl
        simp at hi
    rw [hf_sub_l, LinearEquiv.apply_symm_apply, sub_eq_zero] at h0
    have h1 : hf L S.Hm (∑ i, c i • g i) (gs j) = ∑ i, c i * hf L S.Hm (g i) (gs j) := by
      induction (Finset.univ : Finset (Fin (r + 1))) using Finset.induction_on with
      | empty => simp [hf]
      | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hf_add_l, hf_smul_l, ih]
    change _ = hf L S.Hm x (gs j)
    rw [h0, hc, h1]
    simp [dual]

theorem mem_refB (J : ℕ) (Λ : Submodule L.O S.V) (b : S.V × S.V) :
    b ∈ S.refB J Λ ↔ b.1 ∈ S.spanTo S.f J ∧ b.2 ∈ S.spanTo S.f' J ∧ S.InTh Λ (b.1 + b.2) := by
  simp only [Frames.refB, AddSubgroup.mem_inf, AddSubgroup.mem_prod, AddSubgroup.mem_comap,
    AddSubgroup.mem_map, Frames.InTh, and_assoc]
  refine and_congr Iff.rfl (and_congr Iff.rfl (exists_congr fun y => and_congr Iff.rfl ?_))
  exact eq_comm

theorem mv_iff [CharZero F] (J : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V) (b : S.V × S.V) (u : S.V) (t : E) :
    S.Mv J d Λ (b, u, t) ↔ (b ∈ S.refB J Λ ∧ S.lev (S.fr d Λ) (S.fr' d Λ) (b.1 + b.2) = J) ∧
      u ∈ S.refU J Λ ∧
      ((∃ c ∈ L.O, algebraMap F E 2⁻¹ * S.h u u + t = algebraMap F E ((S.ϖ : F) ^ S.a) * c) ∧
        t + L.cj t = 0) := by
  have hs : algebraMap F E 2⁻¹ * S.h u u + L.cj (algebraMap F E 2⁻¹ * S.h u u) = S.h u u := by
    rw [map_mul, AlgEquiv.commutes, Frames.h, hf_cj L S.herm.1, ← add_mul, ← map_add (f := _)]
    norm_num
  have e : (S.sOf (b, u, t) + L.cj (S.sOf (b, u, t)) = S.h u u) ↔ t + L.cj t = 0 := by
    simp only [Frames.sOf]
    rw [map_add (f := _)]
    constructor <;> intro h
    · linear_combination h - hs
    · linear_combination h + hs
  have hU : u ∈ S.refU J Λ ↔ u ∈ Λ ∧ u ∈ perp L S.Hm (S.spanTo S.f J ⊔ S.spanTo S.f' J) := Iff.rfl
  rw [mem_refB, hU, ← e]
  simp only [Frames.Mv, Frames.IsMove, and_assoc]
  rfl

end

theorem total_moves : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → Nice (S.refA (j + 1) Λ) (ind (S.Mv (j + 1) d Λ)) ∧ Nice (S.refA (j + 1) Λ) (ind fun w => S.Mv (j + 1) d Λ w ∧ ¬ S.NoLeak Λ w.2.1) ∧ Nice (S.refA (j + 1) Λ) (fun w => ind (S.Mv (j + 1) d Λ) w * S.chiM j d Λ w.1 w.2.1) ∧ |S.cK β βJ * (cint (S.refA (j + 1) Λ) (ind (S.Mv (j + 1) d Λ))).re - 1| ≤ 8 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) ∧ S.cK β βJ * (cint (S.refA (j + 1) Λ) (ind fun w => S.Mv (j + 1) d Λ w ∧ ¬ S.NoLeak Λ w.2.1)).re ≤ 16 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) ∧ S.cK β βJ * ‖cint (S.refA (j + 1) Λ) (fun w => ind (S.Mv (j + 1) d Λ) w * S.chiM j d Λ w.1 w.2.1)‖ ≤ 8 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) := by
  intro F _ _ _ _ _ E _ _ _ L r k S hk j β βJ d Λ hT hF
  obtain ⟨B, hB, hinv⟩ := GlobalTheory.T.exists_fineSubgroup_moves_at_lattice L r k S j β βJ d Λ hT hF
  obtain ⟨hβJ, hβ, nB, cB⟩ := GlobalTheory.T.indexIntegrable_share_top_level_vectors L r k S j β βJ d Λ hT hF
  obtain ⟨u1, u2, u3⟩ := GlobalTheory.T.term_integral_near_one_bound L r k S hk (j + 1) d Λ hT
  have hTf := GlobalTheory.T.eichlerMove_scalar_fibre_measure_one L r k S (GlobalTheory.T.term_exponents_nonneg_and_defect_group_bound L r k S d Λ hT).1
  have tri := triple (S.refB (j + 1) Λ) (S.refU (j + 1) Λ) S.refT _ _ S.InZ _ (S.Mv (j + 1) d Λ)
    (mv_iff S (j + 1) d Λ) (fun u => (hTf u).1) (fun u => (hTf u).2)
  have hβ' : (β : ℝ) ≠ 0 := by positivity
  have hβJ' : (βJ : ℝ) ≠ 0 := by positivity
  have cB' : cint (S.refB (j + 1) Λ) (ind fun b : S.V × S.V => b ∈ S.refB (j + 1) Λ ∧
      S.lev (S.fr d Λ) (S.fr' d Λ) (b.1 + b.2) = j + 1) = (((βJ : ℝ) / β : ℝ) : ℂ) := by
    rw [cB]; push_cast; rfl
  have e2 : (ind fun w => S.Mv (j + 1) d Λ w ∧ ¬ S.NoLeak Λ w.2.1) =
      fun w => ind (S.Mv (j + 1) d Λ) w * ind (fun u => ¬ S.NoLeak Λ u) w.2.1 := by
    funext w
    by_cases h1 : S.Mv (j + 1) d Λ w <;> by_cases h2 : S.NoLeak Λ w.2.1 <;> simp [ind, h1, h2]
  have e2' : (fun u => ind (fun u => u ∈ S.refU (j + 1) Λ ∧ S.InZ u) u * ind (fun u => ¬ S.NoLeak Λ u) u) =
      ind fun u => u ∈ S.refU (j + 1) Λ ∧ S.InZ u ∧ ¬ S.NoLeak Λ u := by
    funext u
    by_cases h1 : u ∈ S.refU (j + 1) Λ <;> by_cases h2 : S.NoLeak Λ u <;> by_cases h3 : S.InZ u <;>
      simp [ind, h1, h2, h3]
  have n2 : Nice (S.refA (j + 1) Λ)
      fun w => ind (S.Mv (j + 1) d Λ) w * ind (fun u => ¬ S.NoLeak Λ u) w.2.1 :=
    ⟨B, fine_mul hB (fun w => ind (fun u => ¬ S.NoLeak Λ u) w.2.1) fun w hw b hb => by
      have := (hinv w hw b hb).2.2
      by_cases h : S.NoLeak Λ w.2.1
      · simp only [ind, h, this.2 h, not_true, if_false]
      · simp only [ind, h, mt this.1 h, not_false_iff, if_true]⟩
  have n3 : Nice (S.refA (j + 1) Λ) fun w => ind (S.Mv (j + 1) d Λ) w * S.chiM j d Λ w.1 w.2.1 :=
    ⟨B, fine_mul hB (fun w => S.chiM j d Λ w.1 w.2.1) fun w hw b hb => (hinv w hw b hb).2.1⟩
  refine ⟨⟨B, hB⟩, e2 ▸ n2, n3, ?_, ?_, ?_⟩
  · have t1 := (tri (fun _ _ => 1) (by simpa using ⟨B, hB⟩)).2
    simp only [mul_one] at t1
    rw [cint_ind_mul _ _ nB, cB'] at t1
    have t1' : cint (S.refA (j + 1) Λ) (ind (S.Mv (j + 1) d Λ)) = _ := t1
    rw [t1', Complex.re_ofReal_mul]
    convert u1 using 3
    unfold Frames.cK
    field_simp
  · have t2 := (tri (fun _ u => ind (fun u => ¬ S.NoLeak Λ u) u) n2).2
    rw [cint_ind_mul _ _ nB, cB', e2'] at t2
    have t2' : cint (S.refA (j + 1) Λ)
      (fun w => ind (S.Mv (j + 1) d Λ) w * ind (fun u => ¬ S.NoLeak Λ u) w.2.1) = _ := t2
    rw [e2, t2', Complex.re_ofReal_mul]
    convert u2 using 1
    unfold Frames.cK
    field_simp
  · obtain ⟨s3, t3⟩ := tri (S.chiM j d Λ) n3
    have t3' : cint (S.refA (j + 1) Λ)
      (fun w => ind (S.Mv (j + 1) d Λ) w * S.chiM j d Λ w.1 w.2.1) = _ := t3
    have hw : S.IsTermW d Λ (S.wit d Λ).1 (S.wit d Λ).2 := by
      unfold Frames.wit
      rw [dite_eq_left hT]
      exact hT.choose_spec
    have hqa : (0 : ℝ) ≤ (S.q : ℝ) ^ S.a := by positivity
    rcases hqa.eq_or_lt with h0 | h0
    · unfold Frames.cK
      rw [← h0, zero_mul, zero_div, zero_mul]
      positivity
    have bd := norm_le _ _ nB _ s3
      (8 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) / (S.q : ℝ) ^ S.a) fun b hb => by
        obtain ⟨b1, b2, b3⟩ := (mem_refB S _ _ _).1 hb.1
        obtain ⟨al, ha1, ha2⟩ := exists_coords S S.f S.es S.dual _ hw.2.2.1 j b.1 b1
        obtain ⟨al', ha1', ha2'⟩ := exists_coords S S.f' S.es' S.dual' _ hw.2.2.2.1 j b.2 b2
        obtain ⟨u, hu1, hu2, hu3⟩ := GlobalTheory.T.frameMove_character_ne_one L r k S j β βJ d Λ hT hF b.1 b1 b.2 b2 b3 hb.2
          al al' ha1 ha1'
        rw [ha2, ha2'] at hu3
        have ey : ∀ u, S.chiM j d Λ b u = L.psi0 (S.h (-(algebraMap F E S.th⁻¹) •
            (S.h b.1 (S.es j) • S.fr d Λ j.succ + S.h b.2 (S.es' j) • S.fr' d Λ j.succ)) u) := by
          intro u
          unfold Frames.chiM
          congr 1
          simp only [Frames.h, hf_smul_l, neg_mul]
        rw [le_div_iff₀ h0]
        simp only [ey]
        exact u3 _ ⟨u, ⟨hu1, hu2⟩, by rw [← ey]; exact hu3⟩
    rw [cB', Complex.ofReal_re] at bd
    rw [t3']
    have hc : 0 ≤ S.cK β βJ := by unfold Frames.cK; positivity
    refine (mul_le_mul_of_nonneg_left bd hc).trans (le_of_eq ?_)
    unfold Frames.cK
    field_simp

end GlobalTheory.HL.MoveTotal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianMovesTotalMeasureEstimatesStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianMoves_total_measure_estimates : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → Nice (S.refA (j + 1) Λ) (ind (S.Mv (j + 1) d Λ)) ∧ Nice (S.refA (j + 1) Λ) (ind fun w => S.Mv (j + 1) d Λ w ∧ ¬ S.NoLeak Λ w.2.1) ∧ Nice (S.refA (j + 1) Λ) (fun w => ind (S.Mv (j + 1) d Λ) w * S.chiM j d Λ w.1 w.2.1) ∧ |S.cK β βJ * (cint (S.refA (j + 1) Λ) (ind (S.Mv (j + 1) d Λ))).re - 1| ≤ 8 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) ∧ S.cK β βJ * (cint (S.refA (j + 1) Λ) (ind fun w => S.Mv (j + 1) d Λ w ∧ ¬ S.NoLeak Λ w.2.1)).re ≤ 16 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) ∧ S.cK β βJ * ‖cint (S.refA (j + 1) Λ) (fun w => ind (S.Mv (j + 1) d Λ) w * S.chiM j d Λ w.1 w.2.1)‖ ≤ 8 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) := by
  first | exact @GlobalTheory.HL.MoveTotal.total_moves | exact GlobalTheory.HL.MoveTotal.total_moves | (intros; apply GlobalTheory.HL.MoveTotal.total_moves <;> assumption)
end
