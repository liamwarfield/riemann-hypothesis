module

public import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
public import Formalism.SharpRestriction.Divisibility.BoundaryLocalData
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelPrimeSplitsCompletelyInCmField

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IndexAtLevelIffOuterClausesAnd
section -- merged from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.IndexAtLevel
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.IndexAtLevelRanks

open Formalism.BasicNotions Formalism.MainNotions

variable (D : D7) (u : D.what₂.Word)

def IsScaledU (w : D.what₂.places.Pl) (v : (D.mem u).A.vT)
    (g : (D.fm u).ramSub →ₗ[D.what₂.LL] (D.fm u).ramSub) : Prop :=
  ∀ x : (D.fm u).ramSub, (D.fm u).emb 0 (g x : LT.Vl D u 0) =
    (((D.mem u).A.T : ℂ) ^ (D.fm u).bTop ((D.fm u).tauOf w v)) •
      LT.Uop D u 0 v ((D.fm u).emb 0 (x : LT.Vl D u 0))

end GlobalTheory.IndefiniteRowSideFullHecke.IndexAtLevelRanks

end
end

noncomputable section

namespace GlobalTheory.LevelIndexCompare

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.IndefiniteRowSideFullHecke.IndexAtLevelRanks

section General

end General

variable (D : D7) (u : D.what₂.Word)

def incl (w : D.what₂.places.Pl) : LT.Sram D u w →ₗ[LT.Ow D w] (D.fm u).ramSub where
  toFun x := ⟨x.1, x.2.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def URamStable (v : (D.mem u).A.vT) : Prop :=
  ∀ x ∈ (D.fm u).ramSub, ∃ y ∈ (D.fm u).ramSub, (D.fm u).emb 0 y = LT.Uop D u 0 v ((D.fm u).emb 0 x)

theorem T_ne_zero : ((D.mem u).A.T : ℂ) ≠ 0 := by exact_mod_cast (D.mem u).A.T_prime.ne_zero

theorem emb_zpow_smul (n : ℤ) (x : LT.Vl D u 0) :
    (D.fm u).emb 0 ((((D.mem u).A.T : D.what₂.LL) ^ n) • x) = (((D.mem u).A.T : ℂ) ^ n) • (D.fm u).emb 0 x := by
  rw [LinearMap.map_smulₛₗ, map_zpow₀, map_natCast]

theorem exists_isScaledU_iff (w : D.what₂.places.Pl) (v : (D.mem u).A.vT) :
    (∃ g, IsScaledU D u w v g) ↔ URamStable D u v := by
  constructor
  · rintro ⟨g, hg⟩ x hx
    refine ⟨(((D.mem u).A.T : D.what₂.LL) ^ (-(D.fm u).bTop ((D.fm u).tauOf w v))) • (g ⟨x, hx⟩ : LT.Vl D u 0),
      (D.fm u).ramSub.smul_mem _ (g ⟨x, hx⟩).2, ?_⟩
    rw [emb_zpow_smul, hg, smul_smul, ← zpow_add₀ (T_ne_zero D u), neg_add_cancel, zpow_zero, one_smul]
  · intro h
    let e : (D.fm u).ramSub →ₛₗ[D.what₂.embLL] LT.Fn D u 0 := ((D.fm u).emb 0).comp (D.fm u).ramSub.subtype
    have he : Function.Injective e := ((D.fm u).emb_inj 0).comp Subtype.val_injective
    let f : LT.Fn D u 0 →ₗ[ℂ] LT.Fn D u 0 :=
      (((D.mem u).A.T : ℂ) ^ (D.fm u).bTop ((D.fm u).tauOf w v)) • LT.Uop D u 0 v
    have hf : ∀ x, ∃ y, e y = f (e x) := by
      intro x
      obtain ⟨y, hy, hxy⟩ := h x.1 x.2
      refine ⟨⟨(((D.mem u).A.T : D.what₂.LL) ^ ((D.fm u).bTop ((D.fm u).tauOf w v))) • y,
        (D.fm u).ramSub.smul_mem _ hy⟩, ?_⟩
      exact (emb_zpow_smul D u _ y).trans (by rw [hxy]; rfl)
    exact ⟨descend e e he f hf, fun x => descend_spec e e he f hf x⟩

theorem emb_list_prod (w : D.what₂.places.Pl) (g : (D.mem u).A.vT → Module.End D.what₂.LL (D.fm u).ramSub)
    (l : List (D.mem u).A.vT) (hg : ∀ v ∈ l, IsScaledU D u w v (g v)) (x : (D.fm u).ramSub) :
    (D.fm u).emb 0 ((l.map g).prod x : LT.Vl D u 0) =
      (((D.mem u).A.T : ℂ) ^ (l.map fun v => (D.fm u).bTop ((D.fm u).tauOf w v)).sum) •
        (l.foldr (fun v f => (LT.Uop D u 0 v).comp f) LinearMap.id) ((D.fm u).emb 0 (x : LT.Vl D u 0)) := by
  induction l with
  | nil => simp
  | cons v l ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, hg v List.mem_cons_self,
      ih (fun v' hv' => hg v' (List.mem_cons_of_mem _ hv')), map_smul, smul_smul, List.map_cons, List.sum_cons,
      zpow_add₀ (T_ne_zero D u)]
    rfl

theorem emb_pow (G : Module.End D.what₂.LL (D.fm u).ramSub) (c : ℂ) (U : Module.End ℂ (LT.Fn D u 0))
    (h : ∀ x : (D.fm u).ramSub, (D.fm u).emb 0 (G x : LT.Vl D u 0) = c • U ((D.fm u).emb 0 (x : LT.Vl D u 0)))
    (n : ℕ) (x : (D.fm u).ramSub) :
    (D.fm u).emb 0 ((G ^ n) x : LT.Vl D u 0) = c ^ n • (U ^ n) ((D.fm u).emb 0 (x : LT.Vl D u 0)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, h, ih, map_smul, smul_smul, pow_succ' c, pow_succ' U, Module.End.mul_apply]

theorem mem_Nlam_iff (w : D.what₂.places.Pl) (g : (D.mem u).A.vT → Module.End D.what₂.LL (D.fm u).ramSub)
    (hg : ∀ v ∈ LT.VVT D u w, IsScaledU D u w v (g v)) (y : LT.Vl D u 0) :
    y ∈ LT.Nlam D u w ↔ ∃ x : LT.Sram D u w,
      y = ((((LT.VVT D u w).toList.map g).prod ^ D.R.m) (incl D u w x) : (D.fm u).ramSub) := by
  have key : ∀ x : (D.fm u).ramSub,
      (D.fm u).emb 0 ((((LT.VVT D u w).toList.map g).prod ^ D.R.m) x : (D.fm u).ramSub) =
        ((((D.mem u).A.T : ℂ) ^ LT.expT D u w) • (LT.Uprod D u 0 w) ^ D.R.m) ((D.fm u).emb 0 (x : LT.Vl D u 0)) := by
    intro x
    rw [emb_pow D u _ _ (LT.Uprod D u 0 w)
      (emb_list_prod D u w g _ (fun v hv => hg v (Finset.mem_toList.1 hv))), Finset.sum_map_toList,
      ← zpow_natCast, ← zpow_mul, mul_comm]
    rfl
  constructor
  · rintro ⟨x, hx, hxy⟩
    exact ⟨⟨x, hx⟩, (D.fm u).emb_inj 0 (hxy.trans (key (incl D u w ⟨x, hx⟩)).symm)⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x.1, x.2, key _⟩

end GlobalTheory.LevelIndexCompare

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HookREqHookProd
section -- merged from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.ThetaLift
noncomputable section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions
open scoped Classical

namespace GlobalTheory.IndefiniteRowSideFullHecke.SchurTensorLattices

section Theta
variable {P : Type} [Fintype P]

end Theta

section Schur
variable {T : Type} [Fintype T] {n₀ : ℕ}

end Schur

def hookProd (n : ℕ) (ν : ℕ → ℕ) : ℕ :=
  ∏ r ∈ Finset.range n, ∏ c ∈ Finset.range (ν r),
    ((ν r - c - 1) + ((Finset.Ioo r n).filter (fun r' => c < ν r')).card + 1)

variable (D : D7)

end GlobalTheory.IndefiniteRowSideFullHecke.SchurTensorLattices

end
end

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory.LiftSizeCompare

open GlobalTheory.IndefiniteRowSideFullHecke.SchurTensorLattices

theorem telescope (a k b : ℕ) (hb : b ≤ a) :
    (∏ c ∈ Finset.range b, (a - c - 1 + (k + 1) + 1)) * (a - b + k + 1) =
      (∏ c ∈ Finset.range b, (a - c - 1 + k + 1)) * (a + k + 1) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ]
    have h1 : a - b - 1 + (k + 1) + 1 = a - b + k + 1 := by omega
    have h2 : a - (b + 1) + k + 1 = a - b - 1 + k + 1 := by omega
    rw [h1, h2, ih (by omega)]
    ring

theorem row_hook (ν : ℕ → ℕ) (r k : ℕ) (hν : ∀ x y, x ≤ y → y < r + 1 + k → ν y ≤ ν x) :
    (∏ c ∈ Finset.range (ν r),
        ((ν r - c - 1) + ((Finset.Ioo r (r + 1 + k)).filter (fun r' => c < ν r')).card + 1)) *
      ∏ l ∈ Finset.Ioo r (r + 1 + k), (ν r - ν l + (l - r)) = (ν r + k).factorial := by
  induction k with
  | zero =>
    have he : Finset.Ioo r (r + 1 + 0) = ∅ := by
      ext x
      simp only [Finset.mem_Ioo, Finset.notMem_empty, iff_false]
      omega
    rw [he, Finset.prod_empty, mul_one, Nat.add_zero]
    simp only [Finset.filter_empty, Finset.card_empty, add_zero]
    rw [← Finset.prod_range_add_one_eq_factorial, ← Finset.prod_range_reflect]
    refine Finset.prod_congr rfl fun c hc => ?_
    rw [Finset.mem_range] at hc
    omega
  | succ k ih =>
    have hν' : ∀ x y, x ≤ y → y < r + 1 + k → ν y ≤ ν x := fun x y hxy hy => hν x y hxy (by omega)
    have IH := ih hν'
    set m := r + 1 + k with hm
    have hIns : Finset.Ioo r (r + 1 + (k + 1)) = insert m (Finset.Ioo r m) := by
      ext x
      simp only [Finset.mem_Ioo, Finset.mem_insert]
      omega
    have hmn : m ∉ Finset.Ioo r m := by simp
    have hba : ν m ≤ ν r := hν r m (by omega) (by omega)
    have hcardIoo : (Finset.Ioo r m).card = k := by rw [Nat.card_Ioo]; omega
    rw [hIns, Finset.prod_insert hmn]
    rw [← Finset.prod_range_mul_prod_Ico _ hba] at IH ⊢
    have hlow : ∀ c ∈ Finset.range (ν m),
        ν r - c - 1 + ((insert m (Finset.Ioo r m)).filter (fun r' => c < ν r')).card + 1 =
          ν r - c - 1 + (k + 1) + 1 := by
      intro c hc
      rw [Finset.mem_range] at hc
      rw [Finset.filter_insert, if_pos hc, Finset.card_insert_of_notMem (by simp),
        Finset.filter_true_of_mem (fun l hl => ?_), hcardIoo]
      rw [Finset.mem_Ioo] at hl
      exact lt_of_lt_of_le hc (hν l m hl.2.le (by omega))
    have hlow' : ∀ c ∈ Finset.range (ν m),
        ν r - c - 1 + ((Finset.Ioo r m).filter (fun r' => c < ν r')).card + 1 =
          ν r - c - 1 + k + 1 := by
      intro c hc
      rw [Finset.mem_range] at hc
      rw [Finset.filter_true_of_mem (fun l hl => ?_), hcardIoo]
      rw [Finset.mem_Ioo] at hl
      exact lt_of_lt_of_le hc (hν l m hl.2.le (by omega))
    have hhigh : ∀ c ∈ Finset.Ico (ν m) (ν r),
        ν r - c - 1 + ((insert m (Finset.Ioo r m)).filter (fun r' => c < ν r')).card + 1 =
          ν r - c - 1 + ((Finset.Ioo r m).filter (fun r' => c < ν r')).card + 1 := by
      intro c hc
      rw [Finset.mem_Ico] at hc
      rw [Finset.filter_insert, if_neg (by omega)]
    rw [Finset.prod_congr rfl hlow, Finset.prod_congr rfl hhigh]
    rw [Finset.prod_congr rfl hlow'] at IH
    have hT := telescope (ν r) k (ν m) hba
    have hd : ν r - ν m + (m - r) = ν r - ν m + k + 1 := by omega
    rw [hd, show ν r + (k + 1) = (ν r + k) + 1 by ring, Nat.factorial_succ, ← IH]
    calc (∏ c ∈ Finset.range (ν m), (ν r - c - 1 + (k + 1) + 1)) *
          (∏ c ∈ Finset.Ico (ν m) (ν r),
            (ν r - c - 1 + ((Finset.Ioo r m).filter (fun r' => c < ν r')).card + 1)) *
          ((ν r - ν m + k + 1) * ∏ l ∈ Finset.Ioo r m, (ν r - ν l + (l - r)))
        = ((∏ c ∈ Finset.range (ν m), (ν r - c - 1 + (k + 1) + 1)) * (ν r - ν m + k + 1)) *
          (∏ c ∈ Finset.Ico (ν m) (ν r),
            (ν r - c - 1 + ((Finset.Ioo r m).filter (fun r' => c < ν r')).card + 1)) *
          ∏ l ∈ Finset.Ioo r m, (ν r - ν l + (l - r)) := by ring
      _ = _ := by rw [hT]; ring

theorem hookProd_mul (n : ℕ) (ν : ℕ → ℕ) (hν : ∀ x y, x ≤ y → y < n → ν y ≤ ν x) :
    hookProd n ν * ∏ r ∈ Finset.range n, ∏ l ∈ Finset.Ioo r n, (ν r - ν l + (l - r)) =
      ∏ r ∈ Finset.range n, (ν r + n - 1 - r).factorial := by
  unfold hookProd
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun r hr => ?_
  have hr' := Finset.mem_range.1 hr
  have e : r + 1 + (n - 1 - r) = n := by omega
  have h := row_hook ν r (n - 1 - r) (fun x y hxy hy => hν x y hxy (by omega))
  rw [e] at h
  rw [h]
  congr 1
  omega

variable (D : D7) (L : SizeData₂ D)

variable {eps : ℝ} (Fm : FamP eps)

end GlobalTheory.LiftSizeCompare

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.InitMinorNeZeroOfStrictMono
open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching
open Formalism.MainNotions.PrimeDegreeVariant (embGL Interlace)
open scoped DirectSum

namespace GlobalTheory.Branching

theorem initMinor_ne_zero_of_strictMono {r n s : ℕ} (I : Fin s → Fin r) (hs : s ≤ n) (hI : StrictMono I) :
    initMinor ℂ I hs ≠ 0 := by
  intro h0
  have := (colLexInitMinor ℂ r n s I hs hI).2
  rw [h0] at this
  simp at this

theorem xiB_ne_zero {n : ℕ} (lam sg : Fin n → ℕ) : Formalism.BranchingDeterminantCap.xiB ℂ lam sg ≠ 0 := by
  unfold Formalism.BranchingDeterminantCap.xiB
  refine Finset.prod_ne_zero_iff.2 fun i _ => mul_ne_zero (pow_ne_zero _ ?_) (pow_ne_zero _ ?_)
  · refine initMinor_ne_zero_of_strictMono _ _ fun p q hpq => ?_
    exact hpq
  · refine initMinor_ne_zero_of_strictMono _ _ fun p q hpq => ?_
    have h1 := p.2
    have h2 := q.2
    have h3 := i.2
    rw [Fin.lt_def] at hpq ⊢
    simp only [Formalism.BranchingDeterminantCap.rowsB]
    split_ifs <;> simp <;> omega

theorem det_embGL {n : ℕ} (g : GL (Fin n) ℂ) :
    Matrix.GeneralLinearGroup.det (embGL ℂ n (n + 1) rfl g) = Matrix.GeneralLinearGroup.det g := by
  apply Units.ext
  have e : (embGL ℂ n (n + 1) rfl g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) =
      (Matrix.fromBlocks (g : Matrix (Fin n) (Fin n) ℂ) 0 0 (1 : Matrix (Fin 1) (Fin 1) ℂ)).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm := rfl
  simp only [Matrix.GeneralLinearGroup.val_det_apply]
  rw [e, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
  simp

theorem transpose_embGL {n : ℕ} (g : GL (Fin n) ℂ) :
    (embGL ℂ n (n + 1) rfl g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ).transpose =
      Formalism.BranchingDeterminantCap.extM ℂ (g : Matrix (Fin n) (Fin n) ℂ).transpose := by
  ext a b
  rw [Matrix.transpose_apply, embGL_apply]
  simp only [Formalism.BranchingDeterminantCap.extM, Matrix.of_apply, Matrix.transpose_apply]
  by_cases h : a.val < n ∧ b.val < n
  · rw [dite_eq_left h, dite_eq_left h.symm]
  · rw [dite_eq_right h, dite_eq_right (fun h' => h h'.symm)]
    simp only [eq_comm]

theorem exists_intertwining_ne_zero : ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (mu : DomWeight n), Interlace h lam mu → ∃ φ : (smallRep (MonoidHom.id (GL (Fin n) ℂ)) mu).IntertwiningMap (resRep (MonoidHom.id (GL (Fin n) ℂ)) h lam), φ ≠ 0 := by
  intro n N h lam mu hI
  subst h
  set c : ℕ := (mu.detShift - lam.detShift).toNat with hcdef
  have hls : lam.detShift = lam.w (Fin.last n) := by
    simp [DomWeight.detShift, Fin.last]
  have hlow : ∀ i, lam.detShift ≤ lam.w i := fun i => hls ▸ lam.anti (Fin.le_last i)
  have hc : 0 < n → (c : ℤ) = mu.detShift - lam.detShift := by
    intro hn
    have h1 := (hI ⟨n - 1, by omega⟩).2
    have h2 := hlow ⟨n - 1 + 1, by omega⟩
    have h3 : mu.detShift = mu.w ⟨n - 1, by omega⟩ := by simp [DomWeight.detShift, hn]
    simp only at h1
    omega
  have hmlow : ∀ i, mu.detShift ≤ mu.w i := fun i => by
    have hn : 0 < n := i.pos
    have h3 : mu.detShift = mu.w ⟨n - 1, by omega⟩ := by simp [DomWeight.detShift, hn]
    rw [h3]
    refine mu.anti ?_
    have := i.2
    rw [Fin.le_def]
    simp only
    omega
  have hsg : ∀ i, ((mu.natW i + c : ℕ) : ℤ) = mu.w i - lam.detShift := fun i => by
    have h1 := hc i.pos
    have h2 := hmlow i
    simp only [DomWeight.natW]
    omega
  have hlz : ∀ a, Formalism.BranchingDeterminantCap.lamZ (fun i : Fin n => lam.natW i.castSucc) a = lam.w a - lam.detShift := fun a => by
    have h2 := hlow a
    unfold Formalism.BranchingDeterminantCap.lamZ
    split_ifs with ha
    · have : (⟨a.val, ha⟩ : Fin n).castSucc = a := rfl
      simp only [DomWeight.natW, this]
      omega
    · have : a = Fin.last n := Fin.ext (by have := a.2; simp; omega)
      rw [hls, this]; simp
  have hI' : Formalism.BranchingDeterminantCap.Interlace (Formalism.BranchingDeterminantCap.lamZ (fun i : Fin n => lam.natW i.castSucc))
      (fun i => ((mu.natW i + c : ℕ) : ℤ)) := by
    intro i
    simp only [hsg, hlz]
    have h1 : mu.w i ≤ lam.w i.castSucc := (hI i).1
    have h2 : lam.w i.succ ≤ mu.w i := (hI i).2
    constructor <;> omega
  obtain ⟨io, hmem, heq, hhw, -⟩ := Formalism.BranchingDeterminantCap.branchMap ℂ n (fun i : Fin n => lam.natW i.castSucc)
    (fun i => mu.natW i + c) hI'
  obtain ⟨dm, de, dh⟩ := GlobalTheory.Branching.genericDet_pow_mul n c mu.natW
  obtain ⟨am, ae⟩ := GlobalTheory.Branching.AddColumn.add_column (n + 1) n lam.natW (by simp [DomWeight.natW, hls])
  have ha : Antitone mu.natW := fun i j hij => by
    have := mu.anti hij
    simp only [DomWeight.natW]
    omega
  let D : nablaSq ℂ n mu →ₗ[ℂ] dualWeyl ℂ n n (fun i => mu.natW i + c) :=
    { toFun := fun f => ⟨lpMinor ℂ n le_rfl le_rfl ^ c * f, dm f f.2⟩
      map_add' := fun f f' => Subtype.ext (by simp [mul_add])
      map_smul' := fun a f => Subtype.ext (by simp) }
  let L : nablaSq ℂ n mu →ₗ[ℂ] nablaSq ℂ (n + 1) lam :=
    { toFun := fun f => ⟨rename (Prod.map id Fin.castSucc) (io (D f)), am _ (hmem _)⟩
      map_add' := fun f f' => Subtype.ext (by simp)
      map_smul' := fun a f => Subtype.ext (by simp) }
  have hdet : ∀ g : GL (Fin n) ℂ, detPow ℂ n g mu.detShift =
      detPow ℂ n g lam.detShift * (g : Matrix (Fin n) (Fin n) ℂ).det ^ c := by
    intro g
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have : Matrix.GeneralLinearGroup.det g = 1 := Units.ext (by simp)
      simp [detPow, this]
    · have : mu.detShift = lam.detShift + c := by have := hc hn; omega
      rw [this, detPow, detPow, zpow_add, zpow_natCast]
      simp
  have hL : ∀ (g : GL (Fin n) ℂ) (f : nablaSq ℂ n mu),
      L (sqRep ℂ n mu g f) = sqRep ℂ (n + 1) lam (embGL ℂ n (n + 1) rfl g) (L f) := by
    intro g f
    apply Subtype.ext
    have hd0 : detPow ℂ n g lam.detShift ≠ 0 := Units.ne_zero _
    have h1 : io ((detPow ℂ n g lam.detShift)⁻¹ • D (sqRep ℂ n mu g f)) =
        rowAct ℂ (Formalism.BranchingDeterminantCap.extM ℂ (g : Matrix (Fin n) (Fin n) ℂ).transpose) (io (D f)) := by
      apply heq
      change (detPow ℂ n g lam.detShift)⁻¹ • (lpMinor ℂ n le_rfl le_rfl ^ c * sqAct ℂ n mu g f) =
        rowAct ℂ (g : Matrix (Fin n) (Fin n) ℂ).transpose
          (lpMinor ℂ n le_rfl le_rfl ^ c * (f : MvPolynomial (Fin n × Fin n) ℂ))
      rw [de, sqAct, hdet, Matrix.det_transpose, mul_smul_comm, smul_smul, ← mul_assoc,
        inv_mul_cancel₀ hd0, one_mul]
    have h2 : detPow ℂ (n + 1) (embGL ℂ n (n + 1) rfl g) lam.detShift = detPow ℂ n g lam.detShift := by
      rw [detPow, detPow, det_embGL]
    change rename (Prod.map id Fin.castSucc) (io (D (sqRep ℂ n mu g f))) =
      sqAct ℂ (n + 1) lam (embGL ℂ n (n + 1) rfl g) (rename (Prod.map id Fin.castSucc) (io (D f)))
    rw [sqAct, transpose_embGL, ae, ← h1, h2, map_smul, map_smul, smul_smul, mul_inv_cancel₀ hd0, one_smul]
  refine ⟨⟨L, fun g => LinearMap.ext fun f => hL g f⟩, fun h0 => ?_⟩
  have h1 : L ⟨_, hwMem ℂ n n le_rfl _ ha⟩ = 0 := by
    have := congrArg (fun φ => φ.toLinearMap ⟨_, hwMem ℂ n n le_rfl _ ha⟩) h0
    exact this
  have h2 : rename (Prod.map id Fin.castSucc : Fin (n + 1) × Fin n → Fin (n + 1) × Fin (n + 1))
      (io (D ⟨_, hwMem ℂ n n le_rfl _ ha⟩)) = 0 := congrArg Subtype.val h1
  rw [hhw _ (dh ha)] at h2
  have hinj : Function.Injective
      (Prod.map id Fin.castSucc : Fin (n + 1) × Fin n → Fin (n + 1) × Fin (n + 1)) :=
    Function.injective_id.prodMap (Fin.castSucc_injective n)
  have h3 := rename_injective _ hinj (h2.trans (map_zero _).symm)
  rcases smul_eq_zero.1 h3 with h4 | h4
  · exact (Formalism.BranchingDeterminantCap.capConst n _ _ hI').1 (by exact_mod_cast h4)
  · exact xiB_ne_zero _ _ h4

end GlobalTheory.Branching
end
