module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnderEqOfConj

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedLevelRelIndexEqProdParabolicIndices
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemBlockUpperTriangularTwoIffLowerLeftZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.ParabIndex

theorem card_GL_real (κ : Type) [Field κ] [Finite κ] (m : ℕ) :
    (Nat.card (GL (Fin m) κ) : ℝ)
      = (Nat.card κ : ℝ) ^ (m * m) * ∏ i ∈ Finset.Ioc 0 m, (1 - ((Nat.card κ : ℝ) ^ i)⁻¹) := by
  letI := Fintype.ofFinite κ
  rw [GlobalTheory.Mem.card_GL_eq_pow_mul_qE κ m, Nat.card_eq_fintype_card, Formalism.MainNotions.ZetaProductPairs.qE]
  congr 1
  have h : Finset.Icc 1 m = Finset.Ioc 0 m := by
    ext i; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [h]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [_root_.zpow_neg, zpow_natCast]

variable {κ : Type} [Field κ]

theorem val_mk' {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι κ) (h : IsUnit A.det) :
    ((Matrix.GeneralLinearGroup.mk'' A h : GL ι κ) : Matrix ι ι κ) = A := rfl

def toSum {r s : ℕ} (g : GL (Fin (r + s)) κ) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) κ :=
  Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm (g : Matrix (Fin (r + s)) (Fin (r + s)) κ)

theorem isUnit_det_toSum {r s : ℕ} (g : GL (Fin (r + s)) κ) : IsUnit (toSum g).det := by
  rw [toSum, Matrix.det_reindex_self]
  exact (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit

theorem mem_blockUpperTriangularTwo_iff_lowerLeft_zero {r s : ℕ} (g : GL (Fin (r + s)) κ) :
    g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) ↔ (toSum g).toBlocks₂₁ = 0 := by
  rw [Formalism.L2.DIV.mem_blockTri]
  constructor
  · intro h
    ext i j
    simp only [toSum, Matrix.toBlocks₂₁, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
      Matrix.of_apply, Matrix.zero_apply]
    apply h
    simp [Formalism.L2.DIV.blk2]
  · intro h i j hij
    obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective j
    rcases x with x | x <;> rcases y with y | y
    · simp [Formalism.L2.DIV.blk2] at hij
    · simp [Formalism.L2.DIV.blk2] at hij
    · have := congrFun (congrFun h x) y
      simpa [toSum, Matrix.toBlocks₂₁] using this
    · simp [Formalism.L2.DIV.blk2] at hij

theorem toSum_eq_fromBlocks {r s : ℕ} {g : GL (Fin (r + s)) κ} (hg : g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r)) :
    toSum g = Matrix.fromBlocks (toSum g).toBlocks₁₁ (toSum g).toBlocks₁₂ 0 (toSum g).toBlocks₂₂ := by
  rw [← (mem_blockUpperTriangularTwo_iff_lowerLeft_zero g).1 hg]; exact (Matrix.fromBlocks_toBlocks _).symm

theorem isUnit_blocks {r s : ℕ} {g : GL (Fin (r + s)) κ} (hg : g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r)) :
    IsUnit ((toSum g).toBlocks₁₁.det * (toSum g).toBlocks₂₂.det) := by
  rw [← Matrix.det_fromBlocks_zero₂₁ _ (toSum g).toBlocks₁₂, ← toSum_eq_fromBlocks hg]
  exact isUnit_det_toSum g

theorem isUnit_det_fromBlocks {r s : ℕ} (A : GL (Fin r) κ) (D : GL (Fin s) κ) (B : Matrix (Fin r) (Fin s) κ) :
    IsUnit (Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (A : Matrix (Fin r) (Fin r) κ) B 0 (D : Matrix (Fin s) (Fin s) κ))).det := by
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
  exact ((Matrix.isUnit_iff_isUnit_det _).1 A.isUnit).mul ((Matrix.isUnit_iff_isUnit_det _).1 D.isUnit)

noncomputable def blockTriangularEquiv (r s : ℕ) :
    Formalism.L2.DIV.blockTri (κ := κ) (Formalism.L2.DIV.blk2 (n := r + s) r) ≃
      GL (Fin r) κ × GL (Fin s) κ × Matrix (Fin r) (Fin s) κ where
  toFun g :=
    (Matrix.GeneralLinearGroup.mk'' _ (isUnit_of_mul_isUnit_left (isUnit_blocks g.2)),
     Matrix.GeneralLinearGroup.mk'' _ (isUnit_of_mul_isUnit_right (isUnit_blocks g.2)),
     (toSum g.1).toBlocks₁₂)
  invFun x := ⟨Matrix.GeneralLinearGroup.mk'' _ (isUnit_det_fromBlocks x.1 x.2.1 x.2.2), by
    rw [mem_blockUpperTriangularTwo_iff_lowerLeft_zero]
    ext i j
    simp [toSum, Matrix.toBlocks₂₁, val_mk']⟩
  left_inv g := by
    apply Subtype.ext
    apply Units.ext
    show Matrix.reindex finSumFinEquiv finSumFinEquiv _ = _
    have h := toSum_eq_fromBlocks g.2
    change Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (toSum g.1).toBlocks₁₁ (toSum g.1).toBlocks₁₂ 0 (toSum g.1).toBlocks₂₂) = _
    rw [← h, toSum]
    simp
  right_inv x := by
    rcases x with ⟨A, D, B⟩
    refine Prod.ext (Units.ext ?_) (Prod.ext (Units.ext ?_) ?_)
    · show (toSum _).toBlocks₁₁ = _
      ext i j; simp [toSum, Matrix.toBlocks₁₁, val_mk']
    · show (toSum _).toBlocks₂₂ = _
      ext i j; simp [toSum, Matrix.toBlocks₂₂, val_mk']
    · show (toSum _).toBlocks₁₂ = _
      ext i j; simp [toSum, Matrix.toBlocks₁₂, val_mk']

theorem natCard_blockUpperTriangularTwo_finiteField (κ : Type) [Field κ] [Finite κ] (r s : ℕ) :
    Nat.card (Formalism.L2.DIV.blockTri (κ := κ) (Formalism.L2.DIV.blk2 (n := r + s) r)) =
      Nat.card (GL (Fin r) κ) * Nat.card (GL (Fin s) κ) * Nat.card κ ^ (r * s) := by
  rw [Nat.card_congr (blockTriangularEquiv r s), Nat.card_prod, Nat.card_prod, mul_assoc]
  congr 2
  show Nat.card (Fin r → Fin s → κ) = _
  rw [Nat.card_fun, Nat.card_fun, Nat.card_fin, Nat.card_fin, ← pow_mul, mul_comm]

end GlobalTheory.ParabIndex

namespace GlobalTheory.ParabIndex

theorem index_maxParabolic_GL_finiteField : ∀ (κ : Type) [Field κ] [Finite κ] (n r s : ℕ), n = r + s → (((Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) : Subgroup (GL (Fin n) κ)).index : ℕ) : ℝ) = (Nat.card κ : ℝ) ^ (r * s) * (∏ i ∈ Finset.Ioc 0 n, (1 - ((Nat.card κ : ℝ) ^ i)⁻¹)) / ((∏ i ∈ Finset.Ioc 0 r, (1 - ((Nat.card κ : ℝ) ^ i)⁻¹)) * ∏ i ∈ Finset.Ioc 0 s, (1 - ((Nat.card κ : ℝ) ^ i)⁻¹)) := by
  intro κ _ _ n r s hn
  subst hn
  have hmul := (Formalism.L2.DIV.blockTri (κ := κ) (Formalism.L2.DIV.blk2 (n := r + s) r)).card_mul_index
  rw [natCard_blockUpperTriangularTwo_finiteField] at hmul
  have hR : (((Formalism.L2.DIV.blockTri (κ := κ) (Formalism.L2.DIV.blk2 (n := r + s) r)).index : ℕ) : ℝ) *
      ((Nat.card (GL (Fin r) κ) : ℝ) * (Nat.card (GL (Fin s) κ) : ℝ) * (Nat.card κ : ℝ) ^ (r * s))
      = (Nat.card (GL (Fin (r + s)) κ) : ℝ) := by
    rw [mul_comm]; exact_mod_cast hmul
  have hGr : (Nat.card (GL (Fin r) κ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hGs : (Nat.card (GL (Fin s) κ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  rw [card_GL_real] at hGr hGs
  rw [card_GL_real, card_GL_real, card_GL_real] at hR
  have hq : (Nat.card κ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hPr := right_ne_zero_of_mul hGr
  have hPs := right_ne_zero_of_mul hGs
  rw [eq_div_iff (mul_ne_zero hPr hPs)]
  have key : (r + s) * (r + s) = r * r + s * s + r * s + r * s := by ring
  rw [key, pow_add, pow_add, pow_add] at hR
  have hX : (Nat.card κ : ℝ) ^ (r * r) * (Nat.card κ : ℝ) ^ (s * s) * (Nat.card κ : ℝ) ^ (r * s) ≠ 0 := by
    have := pow_ne_zero (r * r) hq; have := pow_ne_zero (s * s) hq; have := pow_ne_zero (r * s) hq
    positivity
  apply mul_right_cancel₀ hX
  linear_combination hR

end GlobalTheory.ParabIndex
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedLevelRelIndexEqProdParabolicIndices
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section

namespace GlobalTheory.TwistIndex

open Classical

theorem index_pi_univ {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] (H : ∀ i, Subgroup (G i)) :
    (Subgroup.pi Set.univ H).index = ∏ i, (H i).index := by
  simp_rw [Subgroup.index, ← Nat.card_pi]
  refine Nat.card_congr ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)
  rw [QuotientGroup.leftRel_pi]

theorem restrictedBlock_self_apply {κ : Type} [CommRing κ] {n : ℕ} (g : GL (Fin n) κ) : Formalism.L2.DIV.upperLeftBlock (le_refl n) g = g := by
  have hg : g ∈ (Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 n) : Subgroup (GL (Fin n) κ)) := by
    show (g : Matrix (Fin n) (Fin n) κ).BlockTriangular _
    intro i j hij
    simp [Formalism.L2.DIV.blk2] at hij
  apply Units.ext
  rw [Formalism.L2.DIV.upper_block_val_submatrix _ hg]
  ext i j
  simp [Fin.castLE]

variable {D : D7}

theorem mem_datY_iff (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) {r t j : ℕ} (hr hr' : r ≤ V.rank) (Pg Q : Finset (Pl D.host.E))
    (χ χ' : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ ξ' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (x : GL (Fin V.rank) (Lev.EAf D)) :
    x ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (Lev.datY V.rank r t j hr Pg Q (LevelP.triv _ _ _) χ ξ Lev.Frm.B) ↔
      x ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (Lev.datY V.rank r t j hr' Pg ∅ (LevelP.triv _ _ _) χ' ξ' Lev.Frm.B) ∧
        ∀ PP ∈ Q, Formalism.L2.DIV.redFn β PP x ∈ (Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) : Subgroup (GL (Fin V.rank) (kP PP))) := by
  constructor
  · rintro ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
    refine ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, ?_⟩, h5⟩, fun PP hP => ?_⟩
    · exact Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => absurd hP (Finset.notMem_empty _)
    · exact (Formalism.L2.DIV.mem_parah.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h4 PP) hP)).2
  · rintro ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, -⟩, h5⟩, h6⟩
    refine ⟨⟨⟨⟨h1, h2⟩, h3⟩, ?_⟩, h5⟩
    exact Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => Formalism.L2.DIV.mem_parah.2 ⟨h2, h6 PP hP⟩

theorem relIndex_twist : ∀ (D : D7) (c : Com D) (w : GlobalTheory.ChainTw.Twist D) (j : ℕ) (s : PiLocalization₂ D), w.Is c → j ≤ D.R.m → IsStage c w j s → ∀ hr χ ξ, Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L ≤ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β (Lev.datY s.V.rank D.R.r D.R.t j hr w.Pg ∅ (LevelP.triv _ _ _) χ ξ Lev.Frm.B) ∧ (((Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L).relIndex (Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β (Lev.datY s.V.rank D.R.r D.R.t j hr w.Pg ∅ (LevelP.triv _ _ _) χ ξ Lev.Frm.B)) : ℕ) : ℝ) = ∏ PP ∈ w.Q, idxQ PP j := by
  intro D c w j s hw _ hs hr' χ ξ
  obtain ⟨hr, hL, hflat⟩ := hs
  rw [hL]
  have hmem := fun x => mem_datY_iff s.V s.β hr hr' w.Pg w.Q w.chi χ w.ξ ξ (r := D.R.r) (t := D.R.t) (j := j) x
  refine ⟨fun x hx => ((hmem x).1 hx).1, ?_⟩
  have hSt : Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β (Lev.datY s.V.rank D.R.r D.R.t j hr' w.Pg ∅ (LevelP.triv _ _ _) χ ξ Lev.Frm.B) ≤
      Formalism.L2.DIV.St s.β := fun x hx => Formalism.L2.DIV.parLev_St hx.1
  let φ : Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β (Lev.datY s.V.rank D.R.r D.R.t j hr' w.Pg ∅ (LevelP.triv _ _ _) χ ξ Lev.Frm.B) →*
      (∀ PP : w.Q, GL (Fin s.V.rank) (kP PP.1)) :=
    MonoidHom.pi fun PP => (Formalism.L2.DIV.redAt s.β PP.1).comp (Subgroup.inclusion hSt)
  have hφ : ∀ x PP, φ x PP = Formalism.L2.DIV.redFn s.β PP.1 x.1 := by
    intro x PP
    unfold Formalism.L2.DIV.redFn
    rw [Formalism.L2.DIV.extendOne_of_mem _ (hSt x.2)]
    rfl
  have hcomap : (Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β (Lev.datY s.V.rank D.R.r D.R.t j hr w.Pg w.Q (LevelP.triv _ _ _) w.chi w.ξ Lev.Frm.B)).subgroupOf
      (Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β (Lev.datY s.V.rank D.R.r D.R.t j hr' w.Pg ∅ (LevelP.triv _ _ _) χ ξ Lev.Frm.B)) =
      (Subgroup.pi Set.univ fun PP : w.Q =>
        (Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 D.R.r) : Subgroup (GL (Fin s.V.rank) (kP PP.1)))).comap φ := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_pi, hmem]
    simp only [hφ]
    constructor
    · rintro ⟨-, h⟩ PP -
      exact h PP.1 PP.2
    · intro h
      exact ⟨x.2, fun PP hP => h ⟨PP, hP⟩ (Set.mem_univ _)⟩
  have hsurj : Function.Surjective φ := by
    intro g
    obtain ⟨N, hN, -⟩ := hflat.base
    obtain ⟨e, he⟩ := hw.com.split
    have hnc := GlobalTheory.ChainOnto.FlagAct.not_isConjPl_of_idemSum he
    let L' : LevDat D.host.E ℂ s.V.rank := Lev.datW s.V.rank c.Pg (LevelP.triv c.Pg s.V.rank ℂ) Lev.Frm.B
    have hlift : Lev.LiftsExist s.V s.β L' :=
      GlobalTheory.ParahoricLift.liftsExist s.V s.β L' s.Λ N hN (fun PP hP PP' hP' => by
        rcases hP' with h | h
        · exact hnc PP hP PP' h
        · exact absurd h (Finset.notMem_empty _)) (Finset.disjoint_empty_right _)
    let g0 : Formalism.L2.DIV.G0 L'.Pg L'.r := fun PP => if h : PP.1 ∈ w.Q then g ⟨PP.1, h⟩ else 1
    have h0 := hlift g0
    have hκ := h0.choose_spec
    have hκ1 : Lev.finE s.V h0.choose ∈ Formalism.L2.DIV.parLev D.sp.cm s.V.gram s.β L' := hκ.2.1
    have hκ2 : Formalism.L2.DIV.rTup s.β L' (Lev.finE s.V h0.choose) = g0 := hκ.2.2
    have hred : ∀ PP (h : PP ∈ c.Pg), Formalism.L2.DIV.redFn s.β PP (Lev.finE s.V h0.choose) = g0 ⟨PP, h⟩ := by
      intro PP h
      exact (restrictedBlock_self_apply _).symm.trans (congrFun hκ2 ⟨PP, h⟩)
    have hPg : ∀ PP ∈ w.Pg, Formalism.L2.DIV.redFn s.β PP (Lev.finE s.V h0.choose) = 1 := by
      intro PP hP
      have hc : PP ∈ c.Pg := by rw [hw.union]; exact Finset.mem_union_left _ hP
      rw [hred PP hc]
      have hq : PP ∉ w.Q := Finset.disjoint_left.1 hw.disj hP
      show (if h : PP ∈ w.Q then g ⟨PP, h⟩ else (1 : GL (Fin s.V.rank) (kP PP))) = 1
      exact dif_neg hq
    have hSt' := Formalism.L2.DIV.parLev_St hκ1
    have hxbig : Lev.finE s.V h0.choose ∈
        Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β (Lev.datY s.V.rank D.R.r D.R.t j hr' w.Pg ∅ (LevelP.triv _ _ _) χ ξ Lev.Frm.B) := by
      refine ⟨⟨⟨⟨Formalism.L2.DIV.parLev_UA hκ1, hSt'⟩, ?_⟩, ?_⟩, ?_⟩
      · exact Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP =>
          Formalism.L2.DIV.mem_parah.2 ⟨hSt', by rw [hPg PP hP]; exact Subgroup.one_mem _⟩
      · exact Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => absurd hP (Finset.notMem_empty _)
      · show Formalism.L2.DIV.rTup s.β (Lev.datY s.V.rank D.R.r D.R.t j hr' w.Pg ∅ (LevelP.triv _ _ _) χ ξ Lev.Frm.B) (Lev.finE s.V h0.choose) ∈
          (⊥ : Subgroup (Formalism.L2.DIV.G0 w.Pg D.R.r))
        refine Subgroup.mem_bot.2 (funext fun PP => ?_)
        show Formalism.L2.DIV.upperLeftBlock hr' (Formalism.L2.DIV.redFn s.β PP.1 (Lev.finE s.V h0.choose)) = 1
        rw [hPg PP.1 PP.2]
        exact Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ _
    refine ⟨⟨_, hxbig⟩, funext fun PP => ?_⟩
    rw [hφ]
    have hc : PP.1 ∈ c.Pg := by rw [hw.union]; exact Finset.mem_union_right _ PP.2
    rw [hred PP.1 hc]
    show (if h : PP.1 ∈ w.Q then g ⟨PP.1, h⟩ else 1) = g PP
    rw [dite_eq_left PP.2]
  have hn : s.V.rank = D.R.r + j * D.R.t := hflat.rank
  rw [Subgroup.relIndex, hcomap, Subgroup.index_comap_of_surjective _ hsurj, index_pi_univ, Nat.cast_prod]
  refine Eq.trans ?_ (Finset.prod_coe_sort w.Q (fun PP => idxQ PP j))
  refine Finset.prod_congr rfl fun PP _ => ?_
  refine (GlobalTheory.ParabIndex.index_maxParabolic_GL_finiteField (kP PP.1) s.V.rank D.R.r (j * D.R.t) hn).trans ?_
  have hq : Nat.card (kP PP.1) = Ideal.absNorm PP.1.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [hq, hn]
  rfl

end GlobalTheory.TwistIndex

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedLevelRelIndexEqProdParabolicIndicesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedLevel_relIndex_eq_prod_parabolicIndices : ∀ (D : D7) (c : Com D) (w : Twist D) (j : ℕ) (s : PiLocalization₂ D), w.Is c → j ≤ D.R.m → IsStage c w j s → ∀ hr χ ξ, Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L ≤ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β (Lev.datY s.V.rank D.R.r D.R.t j hr w.Pg ∅ (LevelP.triv _ _ _) χ ξ Lev.Frm.B) ∧ (((Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L).relIndex (Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β (Lev.datY s.V.rank D.R.r D.R.t j hr w.Pg ∅ (LevelP.triv _ _ _) χ ξ Lev.Frm.B)) : ℕ) : ℝ) = ∏ PP ∈ w.Q, idxQ PP j := by
  first | exact @GlobalTheory.TwistIndex.relIndex_twist | exact GlobalTheory.TwistIndex.relIndex_twist | (intros; apply GlobalTheory.TwistIndex.relIndex_twist <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RelIndexMulMeasureAdelicLevelSet
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RelIndexMulMeasureAdelicLevelSet
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
open scoped NNReal ENNReal

noncomputable section

open scoped Pointwise

namespace GlobalTheory.LevelIndexMeasure

theorem relIndex_mul_measure_preimage {G Q R : Type*} [Group G] [Group Q] [Group R] [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [μ.IsMulLeftInvariant] (φ : G →* Q) (ψ : G →* R) (N : Subgroup G) (hN : ∀ n ∈ N, ψ n = 1)
    (H₁ H₀ : Subgroup Q) (h10 : H₁ ≤ H₀) (hsurj : H₀ ≤ N.map φ) (hfi : H₁.relIndex H₀ ≠ 0) (E : Set R)
    (hS : MeasurableSet (φ ⁻¹' (H₁ : Set Q) ∩ ψ ⁻¹' E)) :
    (H₁.relIndex H₀ : ℝ≥0∞) * μ (φ ⁻¹' (H₁ : Set Q) ∩ ψ ⁻¹' E) = μ (φ ⁻¹' (H₀ : Set Q) ∩ ψ ⁻¹' E) := by
  haveI : (H₁.subgroupOf H₀).FiniteIndex := ⟨hfi⟩
  obtain ⟨s, hs, -⟩ := (H₁.subgroupOf H₀).exists_isComplement_left 1
  have hs' : Finite s := hs.finite_left_iff.mpr inferInstance
  have hl : ∀ a : s, ∃ n ∈ N, φ n = ((a.val : H₀) : Q) := fun a => hsurj a.val.2
  choose lift hlN hlφ using hl
  set S₁ := φ ⁻¹' (H₁ : Set Q) ∩ ψ ⁻¹' E
  have hU : (⋃ a : s, lift a • S₁) = φ ⁻¹' (H₀ : Set Q) ∩ ψ ⁻¹' E := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_smul_set, Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe, S₁, smul_eq_mul]
    constructor
    · rintro ⟨a, y, ⟨hy1, hy2⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [map_mul, hlφ]; exact H₀.mul_mem a.val.2 (h10 hy1)
      · rw [map_mul, hN _ (hlN a), one_mul]; exact hy2
    · rintro ⟨hx1, hx2⟩
      obtain ⟨⟨b, h⟩, hbh, -⟩ := hs.existsUnique ⟨φ x, hx1⟩
      refine ⟨b, (lift b)⁻¹ * x, ⟨?_, ?_⟩, by group⟩
      · have e : ((b : H₀) : Q) * ((h : H₀) : Q) = φ x := congrArg Subtype.val hbh
        rw [map_mul, map_inv, hlφ, ← e, inv_mul_cancel_left]
        exact Subgroup.mem_subgroupOf.mp h.2
      · rw [map_mul, map_inv, hN _ (hlN b), inv_one, one_mul]; exact hx2
  have hdisj : Pairwise (Function.onFun Disjoint fun a : s => lift a • S₁) := by
    intro a b hab
    rw [Function.onFun, Set.disjoint_left]
    rintro x ⟨y1, ⟨hy1, -⟩, rfl⟩ ⟨y2, ⟨hy2, -⟩, he⟩
    apply hab
    simp only [smul_eq_mul] at he
    have he' := congrArg φ he
    rw [map_mul, map_mul, hlφ, hlφ] at he'
    have hh1' : (⟨φ y1, h10 hy1⟩ : H₀) ∈ H₁.subgroupOf H₀ := Subgroup.mem_subgroupOf.mpr hy1
    have hh2' : (⟨φ y2, h10 hy2⟩ : H₀) ∈ H₁.subgroupOf H₀ := Subgroup.mem_subgroupOf.mpr hy2
    have e : (a.val : H₀) * ⟨φ y1, h10 hy1⟩ = (b.val : H₀) * ⟨φ y2, h10 hy2⟩ := Subtype.ext he'.symm
    have := (hs.existsUnique ((a.val : H₀) * ⟨φ y1, h10 hy1⟩)).unique
      (y₁ := (a, ⟨_, hh1'⟩)) (y₂ := (b, ⟨_, hh2'⟩)) rfl e.symm
    exact congrArg Prod.fst this
  calc (H₁.relIndex H₀ : ℝ≥0∞) * μ S₁ = ∑' a : s, μ (lift a • S₁) := by
        simp [measure_smul, hs.encard_left, Subgroup.relIndex]
    _ = μ (⋃ a : s, lift a • S₁) := (measure_iUnion hdisj fun a => hS.const_smul _).symm
    _ = _ := by rw [hU]

end GlobalTheory.LevelIndexMeasure

namespace GlobalTheory.LevelIndexMeasure

variable {D : D7}

theorem relIndex_mul_measure_levelSet : ∀ (D : D7) (V : HSp D) (ν : Measure (GA D V)) [ν.IsMulLeftInvariant] (K₁ K₀ : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (E : Set (GinfC V)), K₁ ≤ K₀ → K₀ ≤ UA D.sp.cm V.gram → K₁.relIndex K₀ ≠ 0 → MeasurableSet {g : GA D V | Lev.finE V g ∈ K₁} → MeasurableSet E → (K₁.relIndex K₀ : ℝ≥0∞) * ν ({g : GA D V | Lev.finE V g ∈ K₁} ∩ GlobalTheory.AutMult.toInf V ⁻¹' E) = ν ({g : GA D V | Lev.finE V g ∈ K₀} ∩ GlobalTheory.AutMult.toInf V ⁻¹' E) := by
  intro D V ν _ K₁ K₀ E h10 h0U hfi hK₁ hE
  obtain ⟨i1, -, -, -, i5, -, -, i8⟩ := GlobalTheory.RealMeasOne.ginfC_facts V
  have hmeas : Measurable (GlobalTheory.AutMult.toInf V) := (GlobalTheory.AutMult.continuous_toInf V).measurable
  have hsurj : K₀ ≤ (GfC V).map (Lev.finE V) := by
    rw [← GlobalTheory.FunObj.map_levA V h0U]
    exact Subgroup.map_mono inf_le_left
  exact relIndex_mul_measure_preimage ν (Lev.finE V) (GlobalTheory.AutMult.toInf V) (GfC V)
    (fun n hn => (GlobalTheory.ChainOnto.HaarInf.toInf_eq_one_iff V n).2 hn) K₁ K₀ h10 hsurj hfi E (hK₁.inter (hmeas hE))

end GlobalTheory.LevelIndexMeasure
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RelIndexMulMeasureAdelicLevelSetStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
open scoped NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_mul_measure_adelicLevelSet : ∀ (D : D7) (V : HSp D) (ν : Measure (GA D V)) [ν.IsMulLeftInvariant] (K₁ K₀ : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (E : Set (GinfC V)), K₁ ≤ K₀ → K₀ ≤ UA D.sp.cm V.gram → K₁.relIndex K₀ ≠ 0 → MeasurableSet {g : GA D V | Lev.finE V g ∈ K₁} → MeasurableSet E → (K₁.relIndex K₀ : ℝ≥0∞) * ν ({g : GA D V | Lev.finE V g ∈ K₁} ∩ GlobalTheory.AutMult.toInf V ⁻¹' E) = ν ({g : GA D V | Lev.finE V g ∈ K₀} ∩ GlobalTheory.AutMult.toInf V ⁻¹' E) := by
  first | exact @GlobalTheory.LevelIndexMeasure.relIndex_mul_measure_levelSet | exact GlobalTheory.LevelIndexMeasure.relIndex_mul_measure_levelSet | (intros; apply GlobalTheory.LevelIndexMeasure.relIndex_mul_measure_levelSet <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealQuotientVolumeGrowthOfScalarHypotheses
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
open scoped NNReal ENNReal

noncomputable section
namespace GlobalTheory.ChainTw.VolScale

theorem scale {D : D7} (V : HSp D)
    (good : ∀ ρ : D.what₂.Tau, Measure (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2) → Prop)
    (hgood : ∀ ρ m, good ρ m → m.IsHaarMeasure) (K₁ K₀ : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (ν₁ ν₀ : Measure (GA D V)) :
    K₁ ≤ K₀ → K₀ ≤ UA D.sp.cm V.gram → K₁.relIndex K₀ ≠ 0 → MeasurableSet {g : GA D V | Lev.finE V g ∈ K₁} →
    Lev.IsMeasLevW V K₁ good ν₁ → Lev.IsMeasLevW V K₀ good ν₀ → ν₁ = (K₁.relIndex K₀ : ℝ≥0∞) • ν₀ := by
  intro hle hUA hne hmeas h₁ h₀
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := GlobalTheory.RealMeasOne.ginfC_facts V
  have := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).1
  have := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.1
  have := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.1
  have := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.1
  obtain ⟨hH₁, ⟨θ, hθ⟩, k1⟩ := h₁
  obtain ⟨⟨A, hA⟩, k1⟩ := k1 θ hθ
  obtain ⟨⟨m, hm⟩, k1⟩ := k1 A hA
  obtain ⟨hH₀, -, k0⟩ := h₀
  obtain ⟨-, k0⟩ := k0 θ hθ
  obtain ⟨-, k0⟩ := k0 A hA
  have k0 := k0 m hm
  haveI := hH₁
  haveI := hH₀
  let B : ∀ ρ : D.what₂.Tau, TopologicalSpace.PositiveCompacts (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2) :=
    fun ρ => Classical.arbitrary _
  have hB : ∀ ρ, MeasurableSet (B ρ : Set (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2)) := fun ρ =>
    (B ρ).isCompact.measurableSet
  let S : Set (GA D V) := {h | ∀ ρ, ∃ b ∈ (B ρ : Set _), UpqT.mat b * A ρ = A ρ * infMat D.sp.cm.sig V.gram (θ ρ) h}
  have hSc : IsClosed S := by
    have e : S = ⋂ ρ, (fun h => A ρ * infMat D.sp.cm.sig V.gram (θ ρ) h) ⁻¹'
        ((fun b => UpqT.mat b * A ρ) '' (B ρ : Set (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2))) := by
      ext h
      simp only [Set.mem_iInter]
      exact Iff.rfl
    rw [e]
    refine isClosed_iInter fun ρ => IsClosed.preimage ?_ ?_
    · exact continuous_const.matrix_mul (GlobalTheory.Mem.VolExists.continuous_infMat (σ := D.sp.cm.sig) V.gram (hθ ρ))
    · exact ((B ρ).isCompact.image ((GlobalTheory.UpqTopology.continuous_mat).matrix_mul continuous_const)).isClosed
  have hS : MeasurableSet S := hSc.measurableSet
  let E : Set (GinfC V) := Subtype.val ⁻¹' S
  have hE : MeasurableSet E := measurable_subtype_coe hS
  have hpre : GlobalTheory.AutMult.toInf V ⁻¹' E = S := by
    ext h
    simp only [E, S, Set.mem_preimage, Set.mem_setOf_eq, GlobalTheory.RealMeasOne.infMat_toInf]
  have hset : ∀ K : Subgroup (GL (Fin V.rank) (Lev.EAf D)), {g : GA D V | Lev.finE V g ∈ K} ∩ GlobalTheory.AutMult.toInf V ⁻¹' E =
      {h | Lev.finE V h ∈ K ∧ ∀ ρ, ∃ b ∈ (B ρ : Set _), UpqT.mat b * A ρ = A ρ * infMat D.sp.cm.sig V.gram (θ ρ) h} := by
    intro K
    rw [hpre]
    rfl
  have v1 : ν₁ ({g : GA D V | Lev.finE V g ∈ K₁} ∩ GlobalTheory.AutMult.toInf V ⁻¹' E) = ∏ ρ, m ρ (B ρ) :=
    (congrArg ν₁ (hset K₁)).trans (k1 m hm (fun ρ => B ρ) hB)
  have v0 : ν₀ ({g : GA D V | Lev.finE V g ∈ K₀} ∩ GlobalTheory.AutMult.toInf V ⁻¹' E) = ∏ ρ, m ρ (B ρ) :=
    (congrArg ν₀ (hset K₀)).trans (k0 (fun ρ => B ρ) hB)
  have hI := GlobalTheory.T.relIndex_mul_measure_adelicLevelSet D V ν₀ K₁ K₀ E hle hUA hne hmeas hE
  rw [v0] at hI
  have h0 : ∏ ρ, m ρ (B ρ) ≠ 0 := Finset.prod_ne_zero_iff.2 fun ρ _ => by
    have := hgood ρ (m ρ) (hm ρ)
    exact (Measure.measure_pos_of_nonempty_interior (m ρ) (B ρ).interior_nonempty).ne'
  have ht : ∏ ρ, m ρ (B ρ) ≠ ⊤ := ENNReal.prod_ne_top fun ρ _ => by
    have := hgood ρ (m ρ) (hm ρ)
    exact (B ρ).isCompact.measure_lt_top.ne
  set x := ν₀ ({g : GA D V | Lev.finE V g ∈ K₁} ∩ GlobalTheory.AutMult.toInf V ⁻¹' E) with hx
  have hx0 : x ≠ 0 := fun h => h0 (by rw [← hI, h, mul_zero])
  have hxt : x ≠ ⊤ := fun h => ht (by rw [← hI, h]; exact ENNReal.mul_top (by exact_mod_cast hne))
  have e : ν₁ = ((Measure.haarScalarFactor ν₁ ν₀ : NNReal) : ENNReal) • ν₀ := Measure.isMulLeftInvariant_eq_smul ν₁ ν₀
  have e' := v1
  rw [e, Measure.smul_apply, smul_eq_mul, ← hI] at e'
  have hc : ((Measure.haarScalarFactor ν₁ ν₀ : NNReal) : ENNReal) = (K₁.relIndex K₀ : ℝ≥0∞) :=
    (ENNReal.mul_left_inj hx0 hxt).1 e'
  rw [e, hc]

theorem vol_step {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L₁ L₀ : LevDat D.host.E ℂ V.rank)
    (good : ∀ ρ : D.what₂.Tau, Measure (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2) → Prop)
    (hgood : ∀ ρ m, good ρ m → m.IsHaarMeasure) (ν₁ ν₀ : Measure (GA D V)) (N : ℝ)
    (hle : lev D.sp.cm V.gram β L₁ ≤ lev D.sp.cm V.gram β L₀)
    (hN : (((lev D.sp.cm V.gram β L₁).relIndex (lev D.sp.cm V.gram β L₀) : ℕ) : ℝ) = N) (hN0 : 0 < N)
    (hmeas : MeasurableSet {g : GA D V | Lev.finE V g ∈ lev D.sp.cm V.gram β L₁})
    (h₁ : Lev.IsMeasLevW V (lev D.sp.cm V.gram β L₁) good ν₁) (h₀ : Lev.IsMeasLevW V (lev D.sp.cm V.gram β L₀) good ν₀) :
    GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ V ν₁ = GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ V ν₀ * N ∧ 0 < GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ V ν₁ := by
  have hne : (lev D.sp.cm V.gram β L₁).relIndex (lev D.sp.cm V.gram β L₀) ≠ 0 := by
    intro h0; rw [h0, Nat.cast_zero] at hN; linarith
  have e := scale V good hgood _ _ ν₁ ν₀ hle lev_le_UA hne hmeas h₁ h₀
  refine ⟨?_, ?_⟩
  · rw [e]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ
    have e2 : GlobalTheory.AutomorphicL2Unitary.autMeasure V (((lev D.sp.cm V.gram β L₁).relIndex (lev D.sp.cm V.gram β L₀) : ℝ≥0∞) • ν₀) =
        ((lev D.sp.cm V.gram β L₁).relIndex (lev D.sp.cm V.gram β L₀) : ℝ≥0∞) • GlobalTheory.AutomorphicL2Unitary.autMeasure V ν₀ :=
      GlobalTheory.AutomorphicL2Unitary.quotMeasure_smul _
    rw [e2, measureReal_ennreal_smul_apply, ← hN, ENNReal.toReal_natCast, mul_comm]
  · haveI := h₁.1
    exact GlobalTheory.RallisIP.Model.vol_pos ν₁

theorem idxQ_pos {D : D7} (PP : Pl D.host.E) (j : ℕ) : 0 < idxQ PP j := by
  have hq : (0 : ℝ) < (Ideal.absNorm PP.asIdeal : ℝ) := by
    have := HeightOneSpectrum.one_lt_absNorm PP
    exact_mod_cast (Nat.zero_lt_one.trans this)
  unfold idxQ
  exact div_pos (mul_pos (pow_pos hq _) (RModel.zinv_pos PP _ _)) (mul_pos (RModel.zinv_pos PP _ _) (RModel.zinv_pos PP _ _))

theorem rVol_of_given : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F →
    (∀ h : RangeX R, RChain R h) → RangeX R → RVol R := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG hC hR t
  have hQ0 : (twR R A.μ0).Q = ∅ := RModel.Q_base R hG.core.lev
  have hprod : ∀ j, 0 < ∏ PP ∈ R.Q t, idxQ PP j := fun j => Finset.prod_pos fun PP _ => idxQ_pos PP j
  refine ⟨fun j hj => ?_, ?_⟩
  · have hS := (hC hR t).2.1 j hj
    obtain ⟨hr0, hL0, -⟩ := (hC hR A.μ0).2.1 j hj
    rw [hQ0] at hL0
    obtain ⟨good, hgood, hW⟩ := GlobalTheory.RealMeasOne.models_good R hG.core.models j hj
    obtain ⟨hle, hN⟩ := GlobalTheory.T.twistedLevel_relIndex_eq_prod_parabolicIndices D (comR R t) (twR R t) j (stY R t j) (hC hR t).1 hj.le hS hr0 R.chi (R.xiR A.μ0)
    have e : Lev.datY (stY R t j).V.rank D.R.r D.R.t j hr0 (twR R t).Pg ∅ (LevelP.triv _ _ _) R.chi (R.xiR A.μ0) Lev.Frm.B =
        R.datYt A.μ0 j R.triv := hL0.symm
    rw [e] at hle hN
    have hmeas := (GlobalTheory.T.thetaChainStage_finiteLevel_eq_product_localLevels D (comR R t) (twR R t) (hC hR t).1 j hj.le (stY R t j) hS).1
    exact vol_step (Yc D j) (R.βY j) (R.datYt t j R.triv) (R.datYt A.μ0 j R.triv) good hgood (R.νY t j) (R.νY A.μ0 j) _
      hle hN (hprod j) hmeas (hW t) (hW A.μ0)
  · have hS := (hC hR t).2.2.1
    obtain ⟨hr0, hL0, -⟩ := (hC hR A.μ0).2.2.1
    rw [hQ0] at hL0
    obtain ⟨hle, hN⟩ := GlobalTheory.T.twistedLevel_relIndex_eq_prod_parabolicIndices D (comR R t) (twR R t) D.R.m (stX R t) (hC hR t).1 le_rfl hS hr0 R.chi (R.xiR A.μ0)
    have e : Lev.datY (stX R t).V.rank D.R.r D.R.t D.R.m hr0 (twR R t).Pg ∅ (LevelP.triv _ _ _) R.chi (R.xiR A.μ0) Lev.Frm.B =
        R.datXt A.μ0 := hL0.symm
    rw [e] at hle hN
    have hmeas := (GlobalTheory.T.thetaChainStage_finiteLevel_eq_product_localLevels D (comR R t) (twR R t) (hC hR t).1 D.R.m le_rfl (stX R t) hS).1
    have h := vol_step D.sp.X' R.βX (R.datXt t) (R.datXt A.μ0) (fun _ m => m.IsHaarMeasure ∧ IsProbabilityMeasure m)
      (fun _ _ hm => hm.1) (R.νX t) (R.νX A.μ0) _ hle hN (hprod D.R.m) hmeas (hG.core.models.νX t).1 (hG.core.models.νX A.μ0).1
    exact ⟨h.1, h.2⟩

end GlobalTheory.ChainTw.VolScale

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealQuotientVolumeGrowthOfScalarHypothesesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realQuotientVolumeGrowth_of_scalarHypotheses : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → (∀ h : RangeX R, RChain R h) → RangeX R → RVol R := by
  first | exact @GlobalTheory.ChainTw.VolScale.rVol_of_given | exact GlobalTheory.ChainTw.VolScale.rVol_of_given | (intros; apply GlobalTheory.ChainTw.VolScale.rVol_of_given <;> assumption)
end
