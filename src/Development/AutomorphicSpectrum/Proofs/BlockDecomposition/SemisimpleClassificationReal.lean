module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.LeviCommutantWordReduction
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocallyConstantCompactSupportUnipotent

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CreqAnnqTopqSame
open Finset
open scoped InnerProductSpace
open GlobalTheory.CompanionTheory.PairMult
open Formalism.REAL (GlRel KHighest)
open CompanionTheory.D.LK (Pos)
open CompanionTheory.RgExh.U (adC)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

noncomputable section

namespace GlobalTheory.CompanionTheory.PairMult.TopK

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem sgL_erase (l : Lt n) (B : Finset (Lt n)) : sgL l (B.erase l) = sgL l B := by
  unfold sgL
  congr 2
  ext j
  simp only [mem_filter, mem_erase]
  constructor
  · exact fun h => ⟨h.1.2, h.2⟩
  · exact fun h => ⟨⟨fun e => by subst e; exact lt_irrefl _ h.2, h.1⟩, h.2⟩

theorem sgL_sq (l : Lt n) (B : Finset (Lt n)) : sgL l B * sgL l B = 1 := by
  unfold sgL; rw [← pow_add, ← two_mul, pow_mul]; simp

theorem adC_diag_ne {p q : Fin n} (h : p ≠ q) (i : Pos n) : adC p q i i = 0 := by
  have h1 : ¬(q = i.1.1 ∧ i.1 = (p, i.1.2)) := fun e => h (by
    have := congrArg Prod.fst e.2
    exact (this.symm.trans e.1.symm))
  have h2 : ¬(i.1.2 = p ∧ i.1 = (i.1.1, q)) := fun e => h (by
    have := congrArg Prod.snd e.2
    exact e.1.symm.trans this)
  simp [adC, h1, h2]

theorem adC_diag_self (p : Fin n) (i : Pos n) :
    adC p p i i = (if i.1.1 = p then 1 else 0) - (if i.1.2 = p then 1 else 0) := by
  have e1 : (p = i.1.1 ∧ i.1 = (p, i.1.2)) ↔ i.1.1 = p :=
    ⟨fun h => h.1.symm, fun h => ⟨h.symm, Prod.ext h rfl⟩⟩
  have e2 : (i.1.2 = p ∧ i.1 = (i.1.1, p)) ↔ i.1.2 = p :=
    ⟨fun h => h.1, fun h => ⟨h, Prod.ext rfl h⟩⟩
  simp only [adC, e1, e2]

theorem sum_diag {lev : Fin n → ℕ} (hm : Monotone lev) (p : Fin n) :
    (∑ i : Pos n, if lev i.1.1 < lev i.1.2 then adC p p i i else 0) = ((2 * rhoU lev p : ℝ) : ℂ) := by
  have hs : ∀ i : Pos n, (if lev i.1.1 < lev i.1.2 then adC p p i i else 0) =
      (if lev i.1.1 < lev i.1.2 ∧ i.1.1 = p then (1 : ℂ) else 0) -
        (if lev i.1.1 < lev i.1.2 ∧ i.1.2 = p then (1 : ℂ) else 0) := by
    intro i
    rw [adC_diag_self]
    by_cases h : lev i.1.1 < lev i.1.2 <;> simp [h]
  have c1 : (univ.filter fun i : Pos n => lev i.1.1 < lev i.1.2 ∧ i.1.1 = p).card =
      (univ.filter fun b => lev p < lev b).card := by
    refine Finset.card_bij (fun i _ => i.1.2) ?_ ?_ ?_
    · intro i hi
      obtain ⟨h1, h2⟩ := (mem_filter.1 hi).2
      exact mem_filter.2 ⟨mem_univ _, h2 ▸ h1⟩
    · intro i hi j hj e
      have h1 := (mem_filter.1 hi).2.2
      have h2 := (mem_filter.1 hj).2.2
      exact Subtype.ext (Prod.ext (h1.trans h2.symm) e)
    · intro b hb
      have hb' := (mem_filter.1 hb).2
      exact ⟨⟨(p, b), hm.reflect_lt hb'⟩, mem_filter.2 ⟨mem_univ _, hb', rfl⟩, rfl⟩
  have c2 : (univ.filter fun i : Pos n => lev i.1.1 < lev i.1.2 ∧ i.1.2 = p).card =
      (univ.filter fun b => lev b < lev p).card := by
    refine Finset.card_bij (fun i _ => i.1.1) ?_ ?_ ?_
    · intro i hi
      obtain ⟨h1, h2⟩ := (mem_filter.1 hi).2
      exact mem_filter.2 ⟨mem_univ _, h2 ▸ h1⟩
    · intro i hi j hj e
      have h1 := (mem_filter.1 hi).2.2
      have h2 := (mem_filter.1 hj).2.2
      exact Subtype.ext (Prod.ext e (h1.trans h2.symm))
    · intro b hb
      have hb' := (mem_filter.1 hb).2
      exact ⟨⟨(b, p), hm.reflect_lt hb'⟩, mem_filter.2 ⟨mem_univ _, hb', rfl⟩, rfl⟩
  rw [Finset.sum_congr rfl fun i _ => hs i, Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_boole, c1, c2]
  simp only [rhoU]
  push_cast
  ring

end GlobalTheory.CompanionTheory.PairMult.TopK

namespace GlobalTheory.CompanionTheory.PairMult.TopK

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem rhoU_eq {lev : Fin n → ℕ} {a b : Fin n} (h : lev a = lev b) : rhoU lev a = rhoU lev b := by
  simp only [rhoU, h]

theorem kF_bracket {E1 E2 : Fin n → Fin n → Module.End ℂ V} (g1 : GlRel E1) (g2 : GlRel E2)
    (hc : ∀ a b c d, E1 a b * E2 c d = E2 c d * E1 a b) (p q : Fin n) :
    kF E1 E2 q p * kF E1 E2 p q - kF E1 E2 p q * kF E1 E2 q p = kF E1 E2 q q - kF E1 E2 p p := by
  have h1 := g1 q p p q
  have h2 := g2 q p p q
  simp only [if_true] at h1 h2
  have e : kF E1 E2 q p * kF E1 E2 p q - kF E1 E2 p q * kF E1 E2 q p =
      (E1 q p * E1 p q - E1 p q * E1 q p) + (E2 q p * E2 p q - E2 p q * E2 q p) := by
    simp only [kF, add_mul, mul_add, hc q p p q, hc p q q p]
    abel
  rw [e, h1, h2]
  simp only [kF]
  abel

theorem K_act {lam : Fin n → ℤ} {lev : Fin n → ℕ} (hl : IsLev lam lev) {E1 E2 : Fin n → Fin n → Module.End ℂ V}
    (hA : AdmFor lam lev E1 E2) {x : V} (hx : x ∈ hwSp E1 E2 (muQ lam lev)) {p q : Fin n} (hpq : lev p = lev q) :
    kF E1 E2 p q x = if p = q then ((muQ lam lev p : ℝ) : ℂ) • x else 0 := by
  have hK : KHighest (fun _ => true) (kF E1 E2) (muQ lam lev) x := hx
  rcases lt_trichotomy p q with h | rfl | h
  · rw [if_neg h.ne, hK.2 p q h rfl]
  · rw [if_pos rfl, hK.1 p]
  · rw [if_neg h.ne']
    have hmu : muQ lam lev q = muQ lam lev p := by
      simp only [muQ, rhoU_eq hpq.symm, hl.2 q p hpq.symm]
    have hb := LinearMap.congr_fun (kF_bracket hA.gl1 hA.gl2 hA.comm p q) x
    simp only [LinearMap.sub_apply, Module.End.mul_apply, hK.2 q p h rfl, map_zero, sub_zero, hK.1 q, hK.1 p, hmu,
      sub_self] at hb
    have hn : ⟪kF E1 E2 p q x, kF E1 E2 p q x⟫_ℂ = 0 := by
      rw [hA.unitK p q x, hb, inner_zero_right]
    exact inner_self_eq_zero.1 hn

end GlobalTheory.CompanionTheory.PairMult.TopK
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SemisimpleClassificationReal
open Finset
open CompanionTheory.D.LK (Pos)
open CompanionTheory.RgExh.U (adC)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

noncomputable section

namespace GlobalTheory.CompanionTheory.SemiClass

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem annL_app (l : Lt n) (x : Cq n V) (B : Finset (Lt n)) :
    annL l x B = if l ∈ B then 0 else sgL l B • x (insert l B) := rfl

theorem creL_app (l : Lt n) (x : Cq n V) (B : Finset (Lt n)) :
    creL l x B = if l ∈ B then sgL l B • x (B.erase l) else 0 := rfl

theorem sgL_erase (l : Lt n) (B : Finset (Lt n)) : sgL l (B.erase l) = sgL l B := by
  unfold sgL
  congr 2
  ext m
  simp only [Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨⟨_, hm⟩, hk⟩
    exact ⟨hm, hk⟩
  · rintro ⟨hm, hk⟩
    refine ⟨⟨?_, hm⟩, hk⟩
    rintro rfl
    exact lt_irrefl _ hk

theorem sgL_sq (l : Lt n) (B : Finset (Lt n)) : sgL l B * sgL l B = 1 := by
  unfold sgL; rw [← pow_add, ← two_mul, pow_mul]; simp

theorem creL_annL (l : Lt n) (x : Cq n V) (B : Finset (Lt n)) :
    creL l (annL l x) B = if l ∈ B then x B else 0 := by
  rw [creL_app]
  split_ifs with hB
  · rw [annL_app, if_neg (by simp), Finset.insert_erase hB, sgL_erase, smul_smul, sgL_sq, one_smul]
  · rfl

theorem mem_omU {lev : Fin n → ℕ} {l : Lt n} : l ∈ omU lev ↔ l.1 = false ∧ lev l.2.1.1 < lev l.2.1.2 := by
  simp [omU]

omit [Module ℂ V] in
theorem top_app (lev : Fin n → ℕ) (x : V) (B : Finset (Lt n)) :
    (Pi.single (omU lev) x : Cq n V) B = if B = omU lev then x else 0 := by
  rw [Pi.single_apply]

theorem top_smul (lev : Fin n → ℕ) (c : ℂ) (x : V) :
    (Pi.single (omU lev) (c • x) : Cq n V) = c • (Pi.single (omU lev) x : Cq n V) := by
  ext B
  simp only [Pi.smul_apply, top_app]
  split_ifs <;> simp

omit [Module ℂ V] in
theorem top_zero (lev : Fin n → ℕ) : (Pi.single (omU lev) (0 : V) : Cq n V) = 0 := by
  exact Pi.single_zero _

theorem liftL_top (lev : Fin n → ℕ) (T : Module.End ℂ V) (x : V) :
    (liftL n T : Module.End ℂ (Cq n V)) (Pi.single (omU lev) x) = Pi.single (omU lev) (T x) := by
  ext B
  simp only [liftL, LinearMap.compLeft_apply, Function.comp_apply, top_app]
  split_ifs <;> simp

theorem annL_top_of_notMem {lev : Fin n → ℕ} {l : Lt n} (x : V) (h : l ∉ omU lev) :
    annL l (Pi.single (omU lev) x : Cq n V) = 0 := by
  ext B
  rw [annL_app, top_app]
  split_ifs with h1 h2
  · rfl
  · exact absurd (by rw [← h2]; exact Finset.mem_insert_self l B) h
  · simp

theorem creL_annL_top_same {lev : Fin n → ℕ} {l : Lt n} (x : V) (h : l ∈ omU lev) :
    creL l (annL l (Pi.single (omU lev) x : Cq n V)) = Pi.single (omU lev) x := by
  ext B
  rw [creL_annL]
  split_ifs with hB
  · rfl
  · rw [top_app, if_neg (fun e => hB (by rw [e]; exact h))]

theorem creL_annL_top_ne {lev : Fin n → ℕ} {l m : Lt n} (x : V) (hm : m ∈ omU lev) (hne : m ≠ l) :
    creL m (annL l (Pi.single (omU lev) x : Cq n V)) = 0 := by
  ext B
  rw [creL_app]
  split_ifs with hB
  · rw [annL_app]
    split_ifs with hl
    · simp
    · rw [top_app, if_neg]
      · simp
      · intro e
        have hmem : m ∈ insert l (B.erase m) := by
          rw [e]
          exact hm
        simp [hne] at hmem
  · rfl

theorem mem_omU_of_adCL_ne {lev : Fin n → ℕ} {p q : Fin n} {l k : Lt n} (hpq : lev p = lev q)
    (hl : l ∈ omU lev) (h : adCL false p q l k ≠ 0) : k ∈ omU lev := by
  rw [mem_omU] at hl ⊢
  obtain ⟨hl1, hl2⟩ := hl
  have case1 : (q = l.2.1.1 ∧ k.1 = xor false l.1 ∧ k.2.1 = (p, l.2.1.2)) →
      k.1 = false ∧ lev k.2.1.1 < lev k.2.1.2 := by
    rintro ⟨e1, e2, e3⟩
    refine ⟨by simp [e2, hl1], ?_⟩
    calc lev k.2.1.1 = lev p := by rw [e3]
      _ = lev q := hpq
      _ = lev l.2.1.1 := by rw [e1]
      _ < lev l.2.1.2 := hl2
      _ = lev k.2.1.2 := by rw [e3]
  have case2 : (l.2.1.2 = p ∧ k.1 = xor false l.1 ∧ k.2.1 = (l.2.1.1, q)) →
      k.1 = false ∧ lev k.2.1.1 < lev k.2.1.2 := by
    rintro ⟨e1, e2, e3⟩
    refine ⟨by simp [e2, hl1], ?_⟩
    calc lev k.2.1.1 = lev l.2.1.1 := by rw [e3]
      _ < lev l.2.1.2 := hl2
      _ = lev p := by rw [e1]
      _ = lev q := hpq
      _ = lev k.2.1.2 := by rw [e3]
  unfold adCL at h
  split_ifs at h with c1 c2 c3
  · exact case1 c1
  · exact case1 c1
  · exact case2 c3
  · simp at h

theorem adCL_self (p q : Fin n) (i : Pos n) :
    adCL false p q ((false, i) : Lt n) (false, i) = adC p q i i := by
  simp [adCL, adC]

theorem adLL_top {lev : Fin n → ℕ} {p q : Fin n} (hpq : lev p = lev q) (x : V) :
    adLL lev false p q (Pi.single (omU lev) x : Cq n V) =
      (∑ i : Pos n, if lev i.1.1 < lev i.1.2 then adC p q i i else 0) • (Pi.single (omU lev) x : Cq n V) := by
  have key : ∀ l k : Lt n, ((if inUU lev l then adCL false p q l k • (creL k * annL l) else 0 :
      Module.End ℂ (Cq n V)) (Pi.single (omU lev) x)) =
      if k = l then (if l ∈ omU lev then adCL false p q l l • (Pi.single (omU lev) x : Cq n V) else 0) else 0 := by
    intro l k
    by_cases hl : l ∈ omU lev
    · have hin : inUU lev l := (mem_omU.1 hl).2
      rw [if_pos hin, LinearMap.smul_apply, Module.End.mul_apply]
      by_cases hk : k = l
      · subst hk
        rw [creL_annL_top_same x hl, if_pos rfl, if_pos hl]
      · rw [if_neg hk]
        by_cases hkm : k ∈ omU lev
        · rw [creL_annL_top_ne x hkm hk, smul_zero]
        · have h0 : adCL false p q l k = 0 := by
            by_contra hne
            exact hkm (mem_omU_of_adCL_ne hpq hl hne)
          rw [h0, zero_smul]
    · have hr : (if k = l then (if l ∈ omU lev then adCL false p q l l • (Pi.single (omU lev) x : Cq n V) else 0)
          else 0) = 0 := by
        split_ifs <;> rfl
      rw [hr]
      split_ifs
      · rw [LinearMap.smul_apply, Module.End.mul_apply, annL_top_of_notMem x hl, map_zero, smul_zero]
      · rfl
  have hsum : (∑ l ∈ omU lev, adCL false p q l l) =
      ∑ i : Pos n, if lev i.1.1 < lev i.1.2 then adC p q i i else 0 := by
    rw [omU, Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_bool]
    simp [adCL_self]
  unfold adLL
  simp only [LinearMap.sum_apply, key, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [← hsum, Finset.sum_smul, ← Finset.sum_filter]
  congr 1
  ext l
  simp

theorem leviFamilyOne_add_leviFamilyTwo (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) (a c : Fin n) :
    firstLeviFamily lev E1 E2 a c + secondLeviFamily lev E1 E2 a c = evLc lev E1 E2 (FreeAlgebra.ι ℂ (false, a, c)) := by
  simp only [firstLeviFamily, secondLeviFamily, ← smul_add]
  rw [add_add_sub_cancel, ← two_smul ℂ, smul_smul]
  norm_num

end GlobalTheory.CompanionTheory.SemiClass

namespace GlobalTheory.CompanionTheory.SemiClass

open GlobalTheory.CompanionTheory.PairMult.TopK (K_act sum_diag adC_diag_ne)

theorem semiCls : SemiCls := by
  intro n lam _ lev hl V _ _ E1 E2 hA v hv a c hac
  rw [leviFamilyOne_add_leviFamilyTwo]
  unfold evLc
  rw [FreeAlgebra.lift_ι_apply]
  dsimp only
  rw [if_pos hac]
  simp only [Bool.false_eq_true, if_false, ite_false]
  rw [LinearMap.add_apply, liftL_top, adLL_top hac]
  have hk : kA E1 E2 a c v = kF E1 E2 a c v := rfl
  rw [hk, GlobalTheory.CompanionTheory.PairMult.TopK.K_act hl hA hv hac]
  by_cases h : a = c
  · subst h
    rw [if_pos (rfl : a = a), if_pos (rfl : a = a), GlobalTheory.CompanionTheory.PairMult.TopK.sum_diag hl.1, top_smul, ← add_smul]
    congr 1
    push_cast
    ring
  · rw [if_neg h, if_neg h, top_zero, zero_add]
    have h0 : (∑ i : Pos n, if lev i.1.1 < lev i.1.2 then adC a c i i else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [GlobalTheory.CompanionTheory.PairMult.TopK.adC_diag_ne h i]
      simp
    rw [h0, zero_smul]

end GlobalTheory.CompanionTheory.SemiClass
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SemisimpleClassificationRealStatement
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semisimple_classification_real : PositivityTheory.RgBcC.RealD.SemiCls := by
  first | exact @GlobalTheory.CompanionTheory.SemiClass.semiCls | exact GlobalTheory.CompanionTheory.SemiClass.semiCls | (intros; apply GlobalTheory.CompanionTheory.SemiClass.semiCls <;> assumption)
end
