module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteInertHeckeSupportCosets
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertHeckeOperatorIndepOfInertDatum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiamondElementIntegralSupportLastRow

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftWeightParamEqInfinitesimalCharacterOfHalfInt
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftWeightParamEqInfinitesimalCharacterOfHalfInt
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.WtComb

theorem orderEmb_add_le {n : ℕ} (e : Fin n ↪o ℤ) :
    ∀ (k : ℕ) (a b : Fin n), (b : ℕ) = (a : ℕ) + k → e a + (k : ℤ) ≤ e b := by
  intro k
  induction k with
  | zero =>
    intro a b hb
    have : a = b := Fin.ext (by omega)
    subst this; simp
  | succ k ih =>
    intro a b hb
    have hk : (a : ℕ) + k < n := by have := b.2; omega
    have h1 := ih a ⟨(a : ℕ) + k, hk⟩ rfl
    have h2 : e ⟨(a : ℕ) + k, hk⟩ < e b := e.lt_iff_lt.2 (by rw [Fin.lt_def]; simp; omega)
    push_cast; linarith

theorem exists_domWeight_infOf (n : ℕ) (S : Multiset ℂ) (hc : Multiset.card S = n) (hd : S.Nodup)
    (hm : ∀ x ∈ S, ∃ z : ℤ, x = (z : ℂ) + ((n : ℂ) - 1) / 2) :
    ∃ lam : DomWeight n, NG.infOf lam.w = S := by
  classical
  set c : ℂ := ((n : ℂ) - 1) / 2 with hcdef
  let g : ℂ → ℤ := fun x => if h : ∃ z : ℤ, x = (z : ℂ) + c then h.choose else 0
  have hg : ∀ x ∈ S, x = (g x : ℂ) + c := fun x hx => by
    simp only [g, dif_pos (hm x hx)]; exact (hm x hx).choose_spec
  let M : Multiset ℤ := S.map (fun x => -g x)
  have hMd : M.Nodup := hd.map_on (fun x hx y hy hxy => by
    rw [hg x hx, hg y hy]; simp only [neg_inj] at hxy; rw [hxy])
  let T : Finset ℤ := ⟨M, hMd⟩
  have hT : T.card = n := by simp [T, M, hc]
  let e := T.orderEmbOfFin hT
  refine ⟨⟨fun a => -e a + (a : ℕ), ?_⟩, ?_⟩
  · intro a b hab
    have := orderEmb_add_le e ((b : ℕ) - (a : ℕ)) a b (by rw [Fin.le_def] at hab; omega)
    show -e b + ((b : ℕ) : ℤ) ≤ -e a + ((a : ℕ) : ℤ)
    rw [Fin.le_def] at hab
    push_cast [Nat.cast_sub hab] at this
    linarith
  · unfold NG.infOf
    have h1 : (Finset.univ.map e.toEmbedding) = T := Finset.map_orderEmbOfFin_univ T hT
    calc (Finset.univ.val.map fun a : Fin n => ((-e a + ((a : ℕ) : ℤ) : ℤ) : ℂ) + ((n : ℂ) - 1) / 2 - ((a : ℕ) : ℂ))
        = (Finset.univ.val.map fun a : Fin n => e a).map (fun y : ℤ => -(y : ℂ) + c) := by
          rw [Multiset.map_map]
          refine Multiset.map_congr rfl fun a _ => ?_
          simp only [Function.comp, hcdef]; push_cast; ring
      _ = T.val.map (fun y : ℤ => -(y : ℂ) + c) := by rw [← h1]; rfl
      _ = S := by
          show M.map _ = S
          rw [Multiset.map_map]
          conv_rhs => rw [← Multiset.map_id S]
          refine Multiset.map_congr rfl fun x hx => ?_
          simp only [Function.comp, id]
          have h := hg x hx
          push_cast
          linear_combination -1 * h

end GlobalTheory.WtComb

namespace GlobalTheory.WtComb

theorem chain_lt (f : ℕ → ℚ) (N : ℕ) (hs : ∀ i, i + 1 < N → f (i + 1) < f i) :
    ∀ i i', i < i' → i' < N → f i' < f i := by
  intro i i' h
  induction i' with
  | zero => omega
  | succ i' ih =>
    intro hN
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h' | h'
    · exact lt_trans (hs i' hN) (ih h' (by omega))
    · subst h'; exact hs i hN

theorem chain_le (f : ℕ → ℚ) (N : ℕ) (hs : ∀ i, i + 1 < N → f (i + 1) < f i) :
    ∀ i i', i ≤ i' → i' < N → f i' ≤ f i := by
  intro i i' h hN
  rcases Nat.lt_or_eq_of_le h with h' | h'
  · exact (chain_lt f N hs i i' h' hN).le
  · rw [h']

def qv (R : Ranks) (h : HCParam R) (j : Fin R.m) : Multiset ℚ :=
  (Finset.univ.val.map fun i : Fin (R.k - 1) => h.v i) + (Finset.univ.val.map fun i : Fin R.m => -h.b i) +
  ((Multiset.range R.t).map fun c : ℕ => -h.e j + ((R.t : ℚ) - 1 - 2 * c) / 2)

theorem paramV_eq (R : Ranks) (h : HCParam R) (j : Fin R.m) (sh : ℂ) :
    NG.paramV R h j sh = (qv R h j).map (fun q : ℚ => (q : ℂ) - sh) := by
  unfold NG.paramV qv
  simp only [Multiset.map_add (f := _), Multiset.map_map]
  congr 1
  · congr 1
    all_goals refine Multiset.map_congr rfl fun i _ => ?_
    all_goals simp only [Function.comp]; push_cast; try ring
  · refine Multiset.map_congr rfl fun c _ => ?_
    simp only [Function.comp]; push_cast; try ring

theorem card_qv (R : Ranks) (h : HCParam R) (j : Fin R.m) : Multiset.card (qv R h j) = R.nV := by
  have := R.m_add_three_le_k
  simp [qv, Ranks.nV, Ranks.r]
  omega

end GlobalTheory.WtComb

namespace GlobalTheory.WtComb

theorem nodup_qv (R : Ranks) (h : HCParam R) (j : Fin R.m) : (qv R h j).Nodup := by
  classical
  have hk := R.m_add_three_le_k
  have hm2 := R.two_le_m
  have ht0 : (0 : ℚ) ≤ R.t := by positivity
  let U : ℕ → ℚ := fun i => if hi : i < R.k then h.u ⟨i, hi⟩ else 0
  let V : ℕ → ℚ := fun i => if hi : i < R.k - 1 then h.v ⟨i, hi⟩ else 0
  let B : ℕ → ℚ := fun i => if hi : i < R.m then -h.b ⟨i, hi⟩ else 0
  have hU : ∀ i, i + 1 < R.k → U (i + 1) < U i := by
    intro i hi
    have h1 := h.u_gt_v ⟨i, by omega⟩
    have h2 := h.v_gt_u ⟨i, by omega⟩
    simp only [U, dif_pos hi, dif_pos (show i < R.k by omega)]
    exact lt_trans h2 h1
  have hV : ∀ i, i + 1 < R.k - 1 → V (i + 1) < V i := by
    intro i hi
    have h1 := h.u_gt_v ⟨i + 1, hi⟩
    have h2 := h.v_gt_u ⟨i, by omega⟩
    simp only [V, dif_pos hi, dif_pos (show i < R.k - 1 by omega)]
    exact lt_trans h1 h2
  have hB : ∀ i, i + 1 < R.m → B (i + 1) < B i := by
    intro i hi
    have h1 := h.gap_be ⟨i, by omega⟩
    have h2 := h.gap_eb ⟨i, by omega⟩ hi
    simp only [B, dif_pos hi, dif_pos (show i < R.m by omega)]
    linarith
  have bmono : ∀ i i' : Fin R.m, i.1 ≤ i'.1 → -h.b i' ≤ -h.b i := by
    intro i i' hii
    have := chain_le B R.m hB i.1 i'.1 hii i'.2
    simpa only [B, dif_pos i.2, dif_pos i'.2] using this
  have vgt : ∀ (i : Fin (R.k - 1)) (i' : Fin R.m), -h.b i' < h.v i := by
    intro i i'
    have a1 := h.v_gt_u i
    have a2 := chain_le U R.k hU (i.1 + 1) (R.k - 1) (by omega) (by omega)
    have a3 := h.u_last_gt (by omega) (by omega)
    have a4 := bmono ⟨0, by omega⟩ i' (Nat.zero_le _)
    simp only [U, dif_pos (show R.k - 1 < R.k by omega), dif_pos (show i.1 + 1 < R.k by omega)] at a2
    linarith
  have top : ∀ c : ℕ, -h.e j + ((R.t : ℚ) - 1 - 2 * c) / 2 < -h.b j := by
    intro c
    have := h.gap_be j
    have hc : (0 : ℚ) ≤ c := by positivity
    linarith
  have bne : ∀ (i : Fin R.m) (c : ℕ), c < R.t → -h.b i ≠ -h.e j + ((R.t : ℚ) - 1 - 2 * c) / 2 := by
    intro i c hc
    by_cases hij : i.1 ≤ j.1
    · have := bmono i j hij
      have := top c
      intro heq; linarith
    · have hj1 : j.1 + 1 < R.m := by have := i.2; omega
      have a1 := h.gap_eb j hj1
      have a2 := bmono ⟨j.1 + 1, hj1⟩ i (show j.1 + 1 ≤ i.1 by omega)
      have hc' : (c : ℚ) + 1 ≤ R.t := by exact_mod_cast hc
      intro heq; linarith
  have vne : ∀ (i : Fin (R.k - 1)) (c : ℕ), h.v i ≠ -h.e j + ((R.t : ℚ) - 1 - 2 * c) / 2 := by
    intro i c heq
    have := vgt i j
    have := top c
    linarith
  have vinj : Function.Injective h.v := by
    refine StrictAnti.injective fun a b hab => ?_
    have := chain_lt V (R.k - 1) hV a.1 b.1 hab b.2
    simpa only [V, dif_pos a.2, dif_pos b.2] using this
  have binj : Function.Injective fun i : Fin R.m => -h.b i := by
    refine StrictAnti.injective fun a b hab => ?_
    have := chain_lt B R.m hB a.1 b.1 hab b.2
    simpa only [B, dif_pos a.2, dif_pos b.2] using this
  have rinj : Function.Injective fun c : ℕ => -h.e j + ((R.t : ℚ) - 1 - 2 * c) / 2 := by
    intro c c' hcc
    have : (c : ℚ) = c' := by simp only at hcc; linarith
    exact_mod_cast this
  unfold qv
  refine Multiset.nodup_add.2 ⟨Multiset.nodup_add.2 ⟨Finset.univ.nodup.map vinj, Finset.univ.nodup.map binj, ?_⟩,
    (Multiset.nodup_range _).map rinj, ?_⟩
  · refine Multiset.disjoint_left.2 fun ha hb => ?_
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 ha
    obtain ⟨i', -, hi'⟩ := Multiset.mem_map.1 hb
    have := vgt i i'
    linarith
  · refine Multiset.disjoint_left.2 fun ha hb => ?_
    obtain ⟨c, hc, rfl⟩ := Multiset.mem_map.1 hb
    rw [Multiset.mem_range] at hc
    rcases Multiset.mem_add.1 ha with ha | ha
    · obtain ⟨i, -, hi⟩ := Multiset.mem_map.1 ha
      exact vne i c hi
    · obtain ⟨i, -, hi⟩ := Multiset.mem_map.1 ha
      exact bne i c hc hi

theorem int_qv (R : Ranks) (h : HCParam R) (j : Fin R.m) : ∀ q ∈ qv R h j, ∃ z : ℤ, q = z := by
  intro q hq
  unfold qv at hq
  rcases Multiset.mem_add.1 hq with hq | hq
  · rcases Multiset.mem_add.1 hq with hq | hq
    · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hq
      exact h.v_int i
    · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hq
      obtain ⟨z, hz⟩ := h.b_int i
      exact ⟨-z, by rw [hz]; push_cast; ring⟩
  · obtain ⟨c, -, rfl⟩ := Multiset.mem_map.1 hq
    obtain ⟨z, hz⟩ := h.e_int j
    obtain ⟨s, hs⟩ := R.t_odd
    refine ⟨-z + s - c, ?_⟩
    rw [hz, hs]; push_cast; ring

theorem paramV_eq_infOf : ∀ (R : Ranks) (h : HCParam R) (j : Fin R.m) (sh : ℂ), (∃ z : ℤ, sh = (z : ℂ) + 1 / 2) →
    ∃ lam : DomWeight R.nV, NG.infOf lam.w = NG.paramV R h j sh := by
  intro R h j sh ⟨z', hz'⟩
  rw [paramV_eq]
  apply exists_domWeight_infOf
  · rw [Multiset.card_map, card_qv]
  · exact (nodup_qv R h j).map (fun a b hab => by simpa using hab)
  · intro x hx
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.1 hx
    obtain ⟨w, rfl⟩ := int_qv R h j q hq
    obtain ⟨a, ha⟩ := R.k_even
    obtain ⟨b, hb⟩ := R.m_even
    obtain ⟨s, hs⟩ := R.t_odd
    have hk := R.m_add_three_le_k
    have hp : R.nV = 2 * (a + b + s) := by simp only [Ranks.nV, Ranks.r]; omega
    refine ⟨w - z' - (a + b + s), ?_⟩
    rw [hz', hp]; push_cast; ring

end GlobalTheory.WtComb
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftWeightParamEqInfinitesimalCharacterOfHalfIntStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftWeightParam_eq_infinitesimalCharacter_of_halfInt : ∀ (R : Ranks) (h : HCParam R) (j : Fin R.m) (sh : ℂ), (∃ z : ℤ, sh = (z : ℂ) + 1 / 2) →
    ∃ lam : DomWeight R.nV, NG.infOf lam.w = NG.paramV R h j sh := by
  first | exact @GlobalTheory.WtComb.paramV_eq_infOf | exact GlobalTheory.WtComb.paramV_eq_infOf | (intros; apply GlobalTheory.WtComb.paramV_eq_infOf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryRationalPointMatrixHomSurjectiveOnto
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryRationalPointMatrixHomSurjectiveOnto
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.AlgWtF

theorem conjAL_includeLeft {L : Type} [Field L] [NumberField L] [IsCMField L] (x : L) :
    conjAL L ((Algebra.TensorProduct.includeLeftRingHom : L →+* AL L) x) =
      (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L) ((IsCMField.complexConj L : L →+* L) x) := by
  simp [conjAL, Algebra.TensorProduct.map_tmul]

theorem incGL_mem_GA {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (γ₀ : GL (Fin n) L)
    (h : γ₀ ∈ GQ0 L n) : incGL (L := L) (n := n) γ₀ ∈ GA L n := by
  have h0 : (γ₀ : Matrix (Fin n) (Fin n) L) * conjT (IsCMField.complexConj L : L →+* L) γ₀ = 1 := h
  show ((incGL (L := L) (n := n) γ₀ : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
    conjT (conjAL L) (incGL (L := L) (n := n) γ₀) = 1
  have hc : conjT (conjAL L)
      ((incGL (L := L) (n := n) γ₀ : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      (conjT (IsCMField.complexConj L : L →+* L) (γ₀ : Matrix (Fin n) (Fin n) L)).map
        (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L) := by
    ext i j
    simp only [conjT, Matrix.transpose_apply, Matrix.map_apply, incGL,
      Matrix.GeneralLinearGroup.map_apply]
    exact conjAL_includeLeft _
  rw [hc]
  have e : ((incGL (L := L) (n := n) γ₀ : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      (γ₀ : Matrix (Fin n) (Fin n) L).map (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L) := rfl
  rw [e, ← Matrix.map_mul, h0, Matrix.map_one _ (map_zero _) (map_one _)]

theorem ratHom_surjective : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (γ₀ : GL (Fin n) L),
    γ₀ ∈ GQ0 L n → ∃ γ : GQ L n, GlobalTheory.AlgWtF.ratHom (L := L) (n := n) γ = γ₀ := by
  intro L _ _ _ n γ₀ h
  let g : GA L n := ⟨incGL (L := L) (n := n) γ₀, incGL_mem_GA γ₀ h⟩
  have hg : g ∈ GQ L n := Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨γ₀, h, rfl⟩)
  refine ⟨⟨g, hg⟩, ?_⟩
  apply incGL_injective
  exact incGL_ratFun (L := L) (n := n) ⟨g, hg⟩

end GlobalTheory.AlgWtF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryRationalPointMatrixHomSurjectiveOntoStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryRationalPointMatrixHom_surjective_onto : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (γ₀ : GL (Fin n) L), γ₀ ∈ GQ0 L n →
    ∃ γ : GQ L n, GlobalTheory.AlgWtF.ratHom (L := L) (n := n) γ = γ₀ :=
  GlobalTheory.AlgWtF.ratHom_surjective
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianE0SymmetricFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianE0SymmetricFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SymChar

theorem hA_e0_symVec : ∀ (D : D7) (X : HidaSetting D) (kv : Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal → ∀ (b : Fin D.R.rS) (j : Fin D.R.r), hA X.B.I (X.e0 b) (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2) j) - (if j.val = 2 * D.R.rS + D.R.k - b.val then 1 else 0) ∈ GlobalTheory.Mem.SymChar.wInt X (D.naut.plGw kv.1 kv.2) := by
  intro D X kv hg b j
  have hW : ∀ i, ZMod' X.B.I X.B.g (hA X.B.I (X.e0 b) (GlobalTheory.Mem.SymFrame.epsW X (D.naut.plGw kv.1 kv.2) i)) := by
    intro i
    unfold GlobalTheory.Mem.SymFrame.epsW
    split_ifs
    · exact ((X.weightVectorsIntegral _).2.2 b).1
    · exact ((X.weightVectorsIntegral _).2.2 b).2.2.1
  refine wInt_of_zmod X kv.1 hg ?_
  have hb := b.2
  unfold GlobalTheory.Mem.SymFrame.symVec GlobalTheory.SeeConjRead.flagV
  by_cases h1 : j.1 < D.R.rS
  · rw [dite_eq_left h1, if_neg (by omega), sub_zero]; exact (X.gramIntegral _ _).1
  rw [dite_eq_right h1]
  by_cases h2 : j.1 < D.R.rS + D.R.k
  · rw [dite_eq_left h2, if_neg (by omega), sub_zero]; exact hW _
  rw [dite_eq_right h2]
  by_cases h4 : j.1 = D.R.rS + D.R.k
  · rw [dite_eq_left h4, if_neg (by omega), sub_zero]; exact (X.formsAtZero.2 b).1
  rw [dite_eq_right h4]
  by_cases h3 : j.1 < 2 * D.R.rS + D.R.k + 1
  · rw [dite_eq_left h3]
    have h := (X.gramIntegral b ⟨2 * D.R.rS + D.R.k - j.1, by omega⟩).2.2
    by_cases e : j.1 = 2 * D.R.rS + D.R.k - b.1
    · rw [if_pos e]
      rwa [if_pos (Fin.ext (by simp only; omega))] at h
    · rw [if_neg e]
      rwa [if_neg (fun h' => e (by have := congrArg Fin.val h'; simp only at this; omega))] at h
  · rw [dite_eq_right h3, if_neg (by omega), sub_zero, hA_zero_right']
    exact ⟨0, zero_mem _, by simp⟩

end GlobalTheory.Mem.SymChar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianE0SymmetricFrameStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_e0_symmetric_frame : ∀ (D : D7) (X : HidaSetting D) (kv : Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal → ∀ (b : Fin D.R.rS) (j : Fin D.R.r), hA X.B.I (X.e0 b) (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2) j) - (if j.val = 2 * D.R.rS + D.R.k - b.val then 1 else 0) ∈ GlobalTheory.Mem.SymChar.wInt X (D.naut.plGw kv.1 kv.2) := by
  first | exact @GlobalTheory.Mem.SymChar.hA_e0_symVec | exact GlobalTheory.Mem.SymChar.hA_e0_symVec | (intros; apply GlobalTheory.Mem.SymChar.hA_e0_symVec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharZeroFractionRingCoefficientRing
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharZeroFractionRingCoefficientRing
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.HeightCounting.FracCharZero

theorem injective_of_finite_dvr {A B : Type} [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [Module.Finite A B] :
    Function.Injective (algebraMap A B) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  by_contra hne
  push_neg at hne
  obtain ⟨a, ha, ha0⟩ := hne
  have hker : (⊥ : Ideal B).comap (algebraMap A B) ≠ ⊥ := by
    intro h
    apply ha0
    have : a ∈ (⊥ : Ideal B).comap (algebraMap A B) := by simp [Ideal.mem_comap, ha]
    rw [h] at this
    simpa using this
  have hmax : ((⊥ : Ideal B).comap (algebraMap A B)).IsMaximal :=
    Ideal.IsPrime.isMaximal inferInstance hker
  have hbot : (⊥ : Ideal B).IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := A) ⊥ hmax
  exact IsDiscreteValuationRing.not_a_field B (IsLocalRing.eq_maximalIdeal hbot).symm

theorem charZero_of_injective {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] [CharZero R]
    (f : R →+* S) (hf : Function.Injective f) : CharZero S :=
  ⟨fun m n h => by
    have : f (m : R) = f (n : R) := by simpa [map_natCast] using h
    exact Nat.cast_injective (hf this)⟩

end GlobalTheory.HeightCounting.FracCharZero

namespace GlobalTheory.HeightCounting

theorem TwR.charZero_fractionRing_O : ∀ (D : D7) (T : TwR D.LL0 D.nd) (i : T.Tw),
    CharZero (FractionRing (T.O i)) := by
  intro D T i
  have h1 : Function.Injective (algebraMap ℤ_[T.l i] (T.O0 i)) :=
    FracCharZero.injective_of_finite_dvr
  have h2 := T.O_inj i
  have h3 := IsFractionRing.injective (T.O i) (FractionRing (T.O i))
  exact FracCharZero.charZero_of_injective
    (((algebraMap (T.O i) (FractionRing (T.O i))).comp (algebraMap (T.O0 i) (T.O i))).comp
      (algebraMap ℤ_[T.l i] (T.O0 i))) (h3.comp (h2.comp h1))

end GlobalTheory.HeightCounting
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharZeroFractionRingCoefficientRingStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charZero_fractionRing_coefficientRing : ∀ (D : D7) (T : TwR D.LL0 D.nd) (i : T.Tw), CharZero (FractionRing (T.O i)) := by
  first | exact @GlobalTheory.HeightCounting.TwR.charZero_fractionRing_O | exact GlobalTheory.HeightCounting.TwR.charZero_fractionRing_O | (intros; apply GlobalTheory.HeightCounting.TwR.charZero_fractionRing_O <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetMovesWithFrameChange
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetMovesWithFrameChange
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.ChEx


open Classical in
theorem frsF_ya_symm {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
    {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}
    (Λ : LevFam X.E X.K (R.N j) Pr.vGs) (Θ : LevQFam X.E X.K (R.N j) (QE sel (mu : Chr X.F X.E X.K)))
    (g : FrmG Λ Θ) (r : PtAt R sel mu cst u j) (P : QE sel (mu : Chr X.F X.E X.K)) (hP : P.1 ∉ Pr.vGs) (y : Sp X.E (R.N j)) :
    (frsF sel mu (ya Λ Θ g r).1.1 ⟨P.1, Finset.mem_union_right _ P.2⟩).symm (g.1.1 y) =
      (g.2.2.1 P).1 ((frsF sel mu r.1.1 ⟨P.1, Finset.mem_union_right _ P.2⟩).symm y) := by
  rw [LinearEquiv.symm_apply_eq]
  have e1 : (⟨P.1, (Finset.mem_union.mp (Finset.mem_union_right _ P.2)).resolve_left hP⟩ : QE sel (mu : Chr X.F X.E X.K)) = P :=
    Subtype.ext rfl
  simp only [frsF, dif_neg hP, e1]
  show _ = (g.1.1 * r.1.1.1.2 P * ((g.2.2.1 P)⁻¹).1) ((g.2.2.1 P).1 ((r.1.1.1.2 P).symm y))
  have e2 : ((g.2.2.1 P)⁻¹).1 ((g.2.2.1 P).1 ((r.1.1.1.2 P).symm y)) = (r.1.1.1.2 P).symm y := by
    show (g.2.2.1 P).1.symm ((g.2.2.1 P).1 _) = _
    exact LinearEquiv.symm_apply_apply _ _
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, e2]
  show g.1.1 y = g.1.1 ((r.1.1.1.2 P) ((r.1.1.1.2 P).symm y))
  rw [LinearEquiv.apply_symm_apply]

theorem invActs_cqOf : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}, (∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs) → GlobalTheory.Mem.Col2.ChEx.InvActs (GlobalTheory.Mem.Col2.ChEx.cqOf (R := R) (cst := cst) (u := u) (j := j) : PtAt R sel mu cst u j → _) := by
  intro X Pr R sel S mu cst u j hQ Λ Θ g r P
  have hP := hQ P.1 P.2
  ext z
  simp only [cqOf, cosetIn, Set.mem_setOf_eq, Set.mem_image, if_neg hP]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, hz⟩
    refine ⟨(g.2.2.1 P).1.symm z, ⟨y, hy, ?_⟩, LinearEquiv.apply_symm_apply _ _⟩
    rw [frsF_ya_symm Λ Θ g r P hP y] at hz
    rw [← (g.2.2.1 P).2]
    rw [map_smul, map_sub, LinearEquiv.apply_symm_apply]
    exact hz
  · rintro ⟨z0, ⟨y, hy, hz⟩, rfl⟩
    refine ⟨g.1.1 y, ⟨y, hy, rfl⟩, ?_⟩
    rw [frsF_ya_symm Λ Θ g r P hP y, ← map_sub, ← map_smul]
    exact ((g.2.2.1 P).2 _).2 hz

end GlobalTheory.Mem.Col2.ChEx
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetMovesWithFrameChangeStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.couplingCoset_moves_with_frameChange : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}, (∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs) → GlobalTheory.Mem.Col2.ChEx.InvActs (GlobalTheory.Mem.Col2.ChEx.cqOf (R := R) (cst := cst) (u := u) (j := j) : PtAt R sel mu cst u j → _) := by
  first | exact @GlobalTheory.Mem.Col2.ChEx.invActs_cqOf | exact GlobalTheory.Mem.Col2.ChEx.invActs_cqOf | (intros; apply GlobalTheory.Mem.Col2.ChEx.invActs_cqOf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianFormMiddleSymmetricFrameNotOneAt
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianFormMiddleSymmetricFrameNotOneAt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section


open GlobalTheory.Mem.SymFrame GlobalTheory.Mem.SymChar in
theorem GlobalTheory.Mem.SymChar.Resid.hA_bw_symVec_not_ewAt : ∀ (D : D7) (X : HidaSetting D) (kv : Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal → ¬ GlobalTheory.Mem.SymFrame.EwAt X (D.naut.plGw kv.1 kv.2) → sigA X.B.I X.ew - 1 ∈ GlobalTheory.Mem.SymChar.wInt X (D.naut.plGw kv.1 kv.2) → ∀ (m : Fin D.R.k) (j : Fin D.R.r), hA X.B.I (X.bw m) (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2) j) - (if j.val = D.R.rS + D.R.k - 1 - m.val then 1 else 0) ∈ GlobalTheory.Mem.SymChar.wInt X (D.naut.plGw kv.1 kv.2) := by
  intro D X kv hg hEw hs m j
  have hm := m.2
  have hZ : ∀ c, ZMod' X.B.I X.B.g c → c ∈ wInt X (D.naut.plGw kv.1 kv.2) :=
    fun c hc => wInt_of_zmod X kv.1 hg hc
  have hS : ∀ v, ZMod' X.B.I X.B.g (hA X.B.I v (X.bw m)) → hA X.B.I (X.bw m) v ∈ wInt X (D.naut.plGw kv.1 kv.2) := by
    intro v hv
    rw [Formalism.L2.SG.Pf.unitaryCongruence.hA_symm X.B.I v (X.bw m)]
    exact hZ _ (Formalism.L2.SG.Pf.unitaryCongruence.Z_sig _ _ hv)
  have hB : ∀ l : Fin D.R.k, hA X.B.I (X.bw m) (X.bwd l) - (if l = m then 1 else 0) ∈
      wInt X (D.naut.plGw kv.1 kv.2) := by
    intro l
    have h := Formalism.L2.SG.Pf.unitaryCongruence.Z_sig _ _ (X.bw_dual l m)
    rw [map_sub, apply_ite (sigA X.B.I), map_zero] at h
    rw [Formalism.L2.SG.Pf.unitaryCongruence.hA_symm X.B.I (X.bwd l) (X.bw m)]
    by_cases hl : l = m
    · simp only [hl, if_true] at h ⊢
      have := add_mem (hZ _ h) hs
      convert this using 1
      ring
    · simp only [hl, if_false] at h ⊢
      simpa using hZ _ h
  unfold symVec epsW
  rw [if_neg hEw]
  unfold GlobalTheory.SeeConjRead.flagV
  by_cases h1 : j.1 < D.R.rS
  · rw [dite_eq_left h1, if_neg (by omega), sub_zero]
    exact hS _ ((X.weightVectorsIntegral m).2.2 ⟨j.1, h1⟩).1
  rw [dite_eq_right h1]
  by_cases h2 : j.1 < D.R.rS + D.R.k
  · rw [dite_eq_left h2]
    have e : ((Fin.rev (⟨j.1 - D.R.rS, by omega⟩ : Fin D.R.k)) = m) ↔ j.val = D.R.rS + D.R.k - 1 - m.val := by
      rw [Fin.ext_iff, Fin.val_rev]; simp only [Fin.val_mk]; constructor <;> intro h <;> omega
    have := hB (Fin.rev ⟨j.1 - D.R.rS, by omega⟩)
    by_cases h' : j.val = D.R.rS + D.R.k - 1 - m.val
    · rw [if_pos h']; rwa [if_pos (e.2 h')] at this
    · rw [if_neg h']; rwa [if_neg (fun hh => h' (e.1 hh))] at this
  rw [dite_eq_right h2]
  by_cases h4 : j.1 = D.R.rS + D.R.k
  · rw [dite_eq_left h4, if_neg (by omega), sub_zero]
    exact hS _ (X.weightVectorsIntegral m).1
  rw [dite_eq_right h4]
  by_cases h3 : j.1 < 2 * D.R.rS + D.R.k + 1
  · rw [dite_eq_left h3, if_neg (by omega), sub_zero]
    exact hS _ ((X.weightVectorsIntegral m).2.2 _).2.1
  · rw [dite_eq_right h3, if_neg (by omega), sub_zero, hA_zero_right']
    exact zero_mem _

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianFormMiddleSymmetricFrameNotOneAtStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianForm_middle_symmetricFrame_not_oneAt : ∀ (D : D7) (X : HidaSetting D) (kv : Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal → ¬ GlobalTheory.Mem.SymFrame.EwAt X (D.naut.plGw kv.1 kv.2) → sigA X.B.I X.ew - 1 ∈ GlobalTheory.Mem.SymChar.wInt X (D.naut.plGw kv.1 kv.2) → ∀ (m : Fin D.R.k) (j : Fin D.R.r), hA X.B.I (X.bw m) (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2) j) - (if j.val = D.R.rS + D.R.k - 1 - m.val then 1 else 0) ∈ GlobalTheory.Mem.SymChar.wInt X (D.naut.plGw kv.1 kv.2) := by
  first | exact @GlobalTheory.Mem.SymChar.Resid.hA_bw_symVec_not_ewAt | exact GlobalTheory.Mem.SymChar.Resid.hA_bw_symVec_not_ewAt | (intros; apply GlobalTheory.Mem.SymChar.Resid.hA_bw_symVec_not_ewAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlacesOverTypePrimeChosenAndConj
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlacesOverTypePrimeChosenAndConj
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlacesOverG

theorem isConjPl_cP {D : D7} (P : HeightOneSpectrum (𝓞 D.host.E)) :
    Formalism.BasicNotions.IsConjPl D.host P (GlobalTheory.IdemSupport.cP (D := D) P) := by
  intro x y hxy
  have hy : y = GlobalTheory.IdemSupport.cO D x := by
    apply RingOfIntegers.ext
    rw [hxy, GlobalTheory.IdemSupport.cO_coe]
    exact (Formalism.BasicNotions.bridge_star_holds D.R D.host _).symm
  rw [GlobalTheory.IdemSupport.mem_cP, hy, GlobalTheory.IdemSupport.cO_cO]

theorem conjPrime_conjPrime₂ {D : D7} (P : HeightOneSpectrum (𝓞 D.host.E)) :
    GlobalTheory.IdemSupport.cP (D := D) (GlobalTheory.IdemSupport.cP (D := D) P) = P := by
  apply HeightOneSpectrum.ext
  ext x
  rw [GlobalTheory.IdemSupport.mem_cP, GlobalTheory.IdemSupport.mem_cP, GlobalTheory.IdemSupport.cO_cO]

theorem finrank_E' (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  have h1 : Module.finrank ℚ D.host.E = 4 * D.R.ord := D.host.finrank_cmField
  have h5 : D.R.f = 2 * D.R.ord := rfl
  rw [h1, h5]; ring

theorem places_over_g_k : ∀ (D : D7) (k : Fin 2), Function.Injective (Sum.elim (D.naut.plGw k) (fun v => GlobalTheory.IdemSupport.cP (D := D) (D.naut.plGw k v))) ∧ (∀ W : HeightOneSpectrum (𝓞 D.host.E), ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ W.asIdeal ↔ ∃ i, Sum.elim (D.naut.plGw k) (fun v => GlobalTheory.IdemSupport.cP (D := D) (D.naut.plGw k v)) i = W) ∧ Fintype.card (D.nd.PlG k ⊕ D.nd.PlG k) = Module.finrank ℚ D.host.E := by
  intro D k
  set f := Sum.elim (D.naut.plGw k) (fun v => GlobalTheory.IdemSupport.cP (D := D) (D.naut.plGw k v)) with hf
  have hne : ∀ v v', D.naut.plGw k v ≠ GlobalTheory.IdemSupport.cP (D := D) (D.naut.plGw k v') := fun v v' e =>
    D.naut.plGw_nconj k v' v (e ▸ isConjPl_cP _)
  have hinj : Function.Injective f := by
    rintro (a | a) (b | b) e
    · simp only [hf, Sum.elim_inl] at e; rw [D.naut.plGw_inj k e]
    · simp only [hf, Sum.elim_inl, Sum.elim_inr] at e; exact absurd e (hne a b)
    · simp only [hf, Sum.elim_inl, Sum.elim_inr] at e; exact absurd e.symm (hne b a)
    · simp only [hf, Sum.elim_inr] at e
      have := congrArg (GlobalTheory.IdemSupport.cP (D := D)) e
      rw [conjPrime_conjPrime₂, conjPrime_conjPrime₂] at this
      rw [D.naut.plGw_inj k this]
  have hmem : ∀ i, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ (f i).asIdeal := by
    rintro (v | v)
    · exact D.naut.plGw_over k v
    · show _ ∈ (GlobalTheory.IdemSupport.cP (D := D) (D.naut.plGw k v)).asIdeal
      rw [GlobalTheory.IdemSupport.mem_cP, map_natCast]
      exact D.naut.plGw_over k v
  have hcard : Fintype.card (D.nd.PlG k ⊕ D.nd.PlG k) = Module.finrank ℚ D.host.E := by
    rw [Fintype.card_sum, D.nd.card_PlG k, finrank_E', two_mul]
  refine ⟨hinj, fun W => ⟨fun hW => ?_, ?_⟩, hcard⟩
  · have hfin : (Formalism.BasicNotions.placesOver D.host.E (D.host.g k)).Finite := by
      apply Set.finite_of_ncard_ne_zero
      rw [D.nd.g_split k]; exact Module.finrank_pos.ne'
    have hsub : Set.range f ⊆ Formalism.BasicNotions.placesOver D.host.E (D.host.g k) := by
      rintro _ ⟨i, rfl⟩; exact hmem i
    have hle : (Formalism.BasicNotions.placesOver D.host.E (D.host.g k)).ncard ≤ (Set.range f).ncard := by
      rw [D.nd.g_split k, Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, hcard]
    have heq := Set.eq_of_subset_of_ncard_le hsub hle hfin
    have : W ∈ Set.range f := by rw [heq]; exact hW
    exact this
  · rintro ⟨i, rfl⟩; exact hmem i

end GlobalTheory.PlacesOverG
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlacesOverTypePrimeChosenAndConjStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.places_over_typePrime_chosen_and_conj : ∀ (D : D7) (k : Fin 2), Function.Injective (Sum.elim (D.naut.plGw k) (fun v => GlobalTheory.IdemSupport.cP (D := D) (D.naut.plGw k v))) ∧ (∀ W : HeightOneSpectrum (𝓞 D.host.E), ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ W.asIdeal ↔ ∃ i, Sum.elim (D.naut.plGw k) (fun v => GlobalTheory.IdemSupport.cP (D := D) (D.naut.plGw k v)) i = W) ∧ Fintype.card (D.nd.PlG k ⊕ D.nd.PlG k) = Module.finrank ℚ D.host.E := by
  first | exact @GlobalTheory.PlacesOverG.places_over_g_k | exact GlobalTheory.PlacesOverG.places_over_g_k | (intros; apply GlobalTheory.PlacesOverG.places_over_g_k <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjIdempotentSubOneMemPlaceIdeal
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjIdempotentSubOneMemPlaceIdeal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SymChar

variable {D : D7}

theorem smul_mem_wLf_of_mem_wInt (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E))
    {c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F} (hc : c ∈ wInt X w) {y : VA X.B.I} (hy : y ∈ X.B.I.Lf) :
    c • y ∈ Formalism.L2.SG.RowDict.wLf X w := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨a, ha, rfl⟩ := hc
    exact GlobalTheory.Mem.SymFrame.inclE_smul_mem_wLf X w a ha hy
  | zero => rw [zero_smul]; exact zero_mem _
  | add a b _ _ ha hb => rw [add_smul]; exact add_mem ha hb
  | smul r a _ ha =>
    rw [smul_assoc]
    exact Submodule.smul_mem _ r ha

theorem mem_wInt_of_mem_idS (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E))
    {s : Formalism.L2.Herm.intAf X.B.I.F X.B.I.E}
    (hs : s ∈ idS X.B.I.F (Formalism.L2.SG.Pf.RowDictPf.wB X w).asIdeal) :
    (s : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ∈ wInt X w := by
  let J : Ideal (Formalism.L2.Herm.intAf X.B.I.F X.B.I.E) :=
    { carrier := {s | (s : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ∈ wInt X w}
      add_mem' := fun {a b} ha hb => by
        show ((a + b : Formalism.L2.Herm.intAf X.B.I.F X.B.I.E) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ∈ wInt X w
        rw [Subring.coe_add]; exact add_mem ha hb
      zero_mem' := by
        show ((0 : Formalism.L2.Herm.intAf X.B.I.F X.B.I.E) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ∈ wInt X w
        rw [ZeroMemClass.coe_zero]; exact zero_mem _
      smul_mem' := fun r {a} ha => by
        show ((r * a : Formalism.L2.Herm.intAf X.B.I.F X.B.I.E) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ∈ wInt X w
        exact (wInt X w).smul_mem r ha }
  have hle : idS X.B.I.F (Formalism.L2.SG.Pf.RowDictPf.wB X w).asIdeal ≤ J := by
    refine Ideal.map_le_iff_le_comap.2 fun a ha => ?_
    show ((oToS X.B.I.F X.B.I.E a : Formalism.L2.Herm.intAf X.B.I.F X.B.I.E) :
      X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ∈ wInt X w
    refine Submodule.subset_span ⟨a, ⟨RingOfIntegers.mapRingEquiv X.ιE a, ha, rfl⟩, ?_⟩
    rw [oToS_coe]
    rfl
  exact hle hs

end GlobalTheory.Mem.SymChar

namespace GlobalTheory.Mem.SymChar

theorem sigA_ew_sub_one_mem_wInt : ∀ (D : D7) (X : HidaSetting D), X.B.I = Formalism.L2.SG.InstExistsPf.instOf D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (kv : Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal → ¬ GlobalTheory.Mem.SymFrame.EwAt X (D.naut.plGw kv.1 kv.2) → sigA X.B.I X.ew - 1 ∈ GlobalTheory.Mem.SymChar.wInt X (D.naut.plGw kv.1 kv.2) := by
  intro D X _ _ kv hg hne
  set w := D.naut.plGw kv.1 kv.2 with hw
  have h1 : 1 - X.ew - sigA X.B.I X.ew ∈ wInt X w :=
    wInt_of_zmod X kv.1 hg (Formalism.L2.SG.Pf.SatGram.one_sub_ew X)
  let PP := Formalism.L2.SG.Pf.RowDictPf.wB X w
  let e : Formalism.L2.Herm.intAf X.B.I.F X.B.I.E := ⟨X.ew, X.ew_int⟩
  have hidem : e * (1 - e) = 0 := by
    apply Subtype.ext
    show X.ew * (1 - X.ew) = 0
    rw [mul_sub, mul_one, X.ew_idem, sub_self]
  have hr : resS X.B.I.F PP e * resS X.B.I.F PP (1 - e) = 0 := by rw [← map_mul, hidem, map_zero]
  have he : X.ew ∈ wInt X w := by
    rcases mul_eq_zero.1 hr with h | h
    · exact mem_wInt_of_mem_idS X w ((resS_eq_zero_iff PP e).1 h)
    · exfalso
      apply hne
      intro y hy
      have := mem_wInt_of_mem_idS X w ((resS_eq_zero_iff PP (1 - e)).1 h)
      exact smul_mem_wLf_of_mem_wInt X w this hy
  have e2 : sigA X.B.I X.ew - 1 = -X.ew - (1 - X.ew - sigA X.B.I X.ew) := by ring
  rw [e2]
  exact sub_mem (neg_mem he) h1

end GlobalTheory.Mem.SymChar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjIdempotentSubOneMemPlaceIdealStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_idempotent_sub_one_mem_placeIdeal : ∀ (D : D7) (X : HidaSetting D), X.B.I = Formalism.L2.SG.InstExistsPf.instOf D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (kv : Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal → ¬ GlobalTheory.Mem.SymFrame.EwAt X (D.naut.plGw kv.1 kv.2) → sigA X.B.I X.ew - 1 ∈ GlobalTheory.Mem.SymChar.wInt X (D.naut.plGw kv.1 kv.2) := by
  first | exact @GlobalTheory.Mem.SymChar.sigA_ew_sub_one_mem_wInt | exact GlobalTheory.Mem.SymChar.sigA_ew_sub_one_mem_wInt | (intros; apply GlobalTheory.Mem.SymChar.sigA_ew_sub_one_mem_wInt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitLocalLevelFirstFactorReadsComponent
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitLocalLevelFirstFactorReadsComponent
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdFirst

theorem qPi_eq_phi_of_adAt : ∀ {F E K : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {Q : Finset (Pl E)} {Θ : LevQFam E K n Q} (q : QLoc hc n Q Θ) (P : Q), conjPrime₂ P.1 ≠ P.1 → ∀ (a : AfE F E) (e : E), adAt F P.1 a = algebraMap E _ e → qPi q P a = q.phi P e := by
  intro F E K _ _ _ _ _ _ _ hc n _ Q Θ q P hP a e he
  have hw : P.1.under (𝓞 F) = qv F P.1 := HeightOneSpectrum.ext rfl
  set ψ := GlobalTheory.Mem.Dil.psi (qv F P.1) P.1 hw with hψ
  set sp := q.sp P with hsp

  have hu' : ψ (sp.symm (0, 1)) = 0 := by
    obtain ⟨r, hr, hr'⟩ := exists_mem_notMem (Ne.symm hP)
    have hcr : cO E r ∉ P.1.asIdeal := fun h => hr' ((mem_conjP _ _).2 h)
    obtain ⟨hne, hinv⟩ := qdf_phi_unit q P hcr
    set w := Formalism.UG.inclE (F := F) ((qv F P.1).adicCompletion F) (r : E) with hwdef
    have hws : w = Formalism.UG.sigR hc.sig _ (Formalism.UG.inclE (F := F) ((qv F P.1).adicCompletion F) ((cO E r : 𝓞 E) : E)) := by
      rw [hwdef]
      show _ = Formalism.UG.inclE (F := F) _ (star (star ((r : 𝓞 E) : E)))
      rw [star_star]
    have hw2 : (sp w).2 = q.phi P ((cO E r : 𝓞 E) : E) := by
      rw [hws, hsp, q.sp_sig]
      rfl
    set z := sp.symm (0, ((sp w).2)⁻¹) with hz
    have hzint : z ∈ Formalism.BasicNotions.intV E (qv F P.1) := by
      refine (q.sp_int P z).2 ⟨?_, ?_⟩
      · rw [hz, ← hsp, sp.apply_symm_apply]; exact zero_mem _
      · rw [hz, ← hsp, sp.apply_symm_apply]; show ((sp w).2)⁻¹ ∈ _; rw [hw2]; exact hinv
    have hwz : w * z = sp.symm (0, 1) := by
      apply sp.injective
      rw [map_mul, hz, sp.apply_symm_apply, sp.apply_symm_apply]
      refine Prod.ext (mul_zero _) ?_
      show (sp w).2 * ((sp w).2)⁻¹ = 1
      rw [hw2]
      exact mul_inv_cancel₀ hne
    have hidem : ψ (sp.symm (0, 1)) * ψ (sp.symm (0, 1)) = ψ (sp.symm (0, 1)) := by
      rw [← map_mul, ← map_mul sp.symm]
      simp
    rcases mul_eq_zero.1 (show ψ (sp.symm (0, 1)) * (ψ (sp.symm (0, 1)) - 1) = 0 by rw [mul_sub, hidem, mul_one, sub_self]) with h | h
    · exact h
    · exfalso
      have h1 : ψ (sp.symm (0, 1)) = 1 := sub_eq_zero.1 h
      rw [← hwz, map_mul] at h1
      have hv1 : Valued.v (ψ w) < 1 := by
        rw [hψ, hwdef, GlobalTheory.Mem.Dil.psi_inclE]
        exact GlobalTheory.Mem.Dil.val_lt_one hr
      have hv2 : Valued.v (ψ z) ≤ 1 := (GlobalTheory.Mem.Dil.mem_intV_iff (qv F P.1) z).1 hzint P.1 hw
      have h3 := congrArg Valued.v h1
      rw [map_mul, map_one] at h3
      exact absurd h3 (ne_of_lt (lt_of_le_of_lt (mul_le_of_le_one_right' hv2) hv1))
  have hu : ψ (sp.symm (1, 0)) = 1 := by
    have e1 : sp.symm (1, 0) + sp.symm (0, 1) = 1 := by
      rw [← map_add (f := _)]; simp
    have e2 := congrArg ψ e1
    rw [map_add (f := _), hu', add_zero, map_one] at e2
    exact e2

  set x := prV (E := E) (qv F P.1) a - Formalism.UG.inclE (F := F) ((qv F P.1).adicCompletion F) e with hx
  have hψx : ψ x = 0 := by
    rw [hx, map_sub, hψ, GlobalTheory.Mem.Dil.psi_prV, GlobalTheory.Mem.Dil.psi_inclE, he, sub_self]
  have hx1 : (sp x).1 = 0 := by
    by_contra ht
    have hxy : x * sp.symm (((sp x).1)⁻¹, 0) = sp.symm (1, 0) := by
      apply sp.injective
      rw [map_mul, sp.apply_symm_apply, sp.apply_symm_apply]
      exact Prod.ext (mul_inv_cancel₀ ht) (mul_zero _)
    have h2 := congrArg ψ hxy
    rw [map_mul, hψx, zero_mul, hu] at h2
    exact zero_ne_one h2
  have e3 : qPi q P a - q.phi P e = (sp x).1 := by
    rw [hx, map_sub]
    rfl
  exact sub_eq_zero.1 (e3.trans hx1)

end GlobalTheory.Mem.Col2.AdFirst
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitLocalLevelFirstFactorReadsComponentStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitLocalLevel_firstFactor_reads_component : ∀ {F E K : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {Q : Finset (Pl E)} {Θ : LevQFam E K n Q} (q : QLoc hc n Q Θ) (P : Q), conjPrime₂ P.1 ≠ P.1 → ∀ (a : AfE F E) (e : E), adAt F P.1 a = algebraMap E _ e → qPi q P a = q.phi P e := by
  first | exact @GlobalTheory.Mem.Col2.AdFirst.qPi_eq_phi_of_adAt | exact GlobalTheory.Mem.Col2.AdFirst.qPi_eq_phi_of_adAt | (intros; apply GlobalTheory.Mem.Col2.AdFirst.qPi_eq_phi_of_adAt <;> assumption)
end
end
