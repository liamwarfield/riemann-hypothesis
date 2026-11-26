module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DofOTw

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefficientMapLevelCharacterEquivariant
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CastGLSymmCastGL
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.LiftPres

open Formalism.IndefR.Bridge

section Shift

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S : Formalism.L2.Col.GSD K} {G Γ : Type} [Group G] [Group Γ]
  {ι : Γ →* G} {J : Subgroup G}

end Shift

section Read

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S : Formalism.L2.Col.GSD K} {G Γ : Type} [Group G] [Group Γ]
  {ι : Γ →* G} {J : Subgroup G}
variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]

theorem classPresOf_ext (A : AdPts S ι J) (h : S.Ok) (σ : K →+* ℂ) (ρ : Γ →* Module.End ℂ W) (χ : J →* ℂˣ)
    (coef : S.V →ₛₗ[σ] W) (hli : LinearIndependent ℂ fun i => coef (S.bV i))
    (hspan : Submodule.span ℂ (Set.range fun i => coef (S.bV i)) = ⊤)
    (hpair : ∀ x x', inner ℂ (coef x) (coef x') = σ (S.pair x x')) (hK1 : ∀ k : J, (k : G) ∈ A.K1 → χ k = 1)
    (hgl : ∀ (γ : Γ) (k : J) (v : S.V), coef (S.ρ (A.gl (γ, k)) v) = ((χ k)⁻¹ : ℂˣ) • ρ γ (coef v))
    (f : (S.toCSD h).Forms) (g : G) :
    (classPresOf A h σ ρ χ coef hli hspan hpair hK1 hgl).ext (f : S.Cl → S.V) g =
      coef ((((S.res h).symm f : S.EqFun) : S.D → S.V) (A.q g)) := by

  have key : ∀ (γ : Γ) (c : S.Cl) (k : J),
      (classPresOf A h σ ρ χ coef hli hspan hpair hK1 hgl).ext (f : S.Cl → S.V) (ι γ * A.y c * k) =
        coef ((((S.res h).symm f : S.EqFun) : S.D → S.V) (A.q (ι γ * A.y c * k))) := by
    intro γ c k
    have e1 : (classPresOf A h σ ρ χ coef hli hspan hpair hK1 hgl).ext (f : S.Cl → S.V) (ι γ * A.y c * k) =
        (χ k : ℂ) • ρ γ (coef ((f : S.Cl → S.V) c)) :=
      ClassPres.ext_eq (classPresOf A h σ ρ χ coef hli hspan hpair hK1 hgl) f γ c k
    have e2 : A.q (ι γ * A.y c * k) = A.gl (γ, k⁻¹) • S.outSec.rep c := by
      rw [A.q_mul, A.q_y]
    have e3 : (((S.res h).symm f : S.EqFun) : S.D → S.V) (S.outSec.rep c) = (f : S.Cl → S.V) c := by
      have := S.resOf_apply h S.outSec ((S.res h).symm f) c
      rw [← this]
      show ((((S.res h) ((S.res h).symm f)).1 : S.Cl → S.V) c) = _
      rw [LinearEquiv.apply_symm_apply]
    have e4 := (S.mem_EqFun _).1 ((S.res h).symm f).2 (A.gl (γ, k⁻¹)) (S.outSec.rep c)
    rw [e1, e2, e4, e3, hgl, map_inv, inv_inv, Units.smul_def]
  rw [(classPresOf A h σ ρ χ coef hli hspan hpair hK1 hgl).dec_spec g]
  exact key _ _ _

variable {G' Γ' : Type} [Group G'] [Group Γ'] {ι' : Γ' →* G'} {ρ : Γ →* Module.End ℂ W} {ρ' : Γ' →* Module.End ℂ W}
  {J' : Subgroup G'} {χ : J →* ℂˣ} {χ' : J' →* ℂˣ} {T : Formalism.L2.DIV.CSD K} {σ : K →+* ℂ}

theorem transport_ext (P : ClassPres ι T σ ρ J χ) (eG : G ≃* G') (eΓ : Γ ≃* Γ') (hι : ∀ γ, ι' (eΓ γ) = eG (ι γ))
    (hρ : ∀ γ, ρ' (eΓ γ) = ρ γ) (hJ : J' = J.map eG.toMonoidHom)
    (hχ : ∀ (k : J) (hk : eG k ∈ J'), χ' ⟨eG k, hk⟩ = χ k) (f : T.Forms) (g : G) :
    (P.transport eG eΓ hι hρ hJ hχ).ext (f : T.Cl → T.V) (eG g) = P.ext f g := by
  rw [P.dec_spec g]
  have hk : eG (P.decK g : G) ∈ J' := by
    rw [hJ]; exact Subgroup.mem_map_of_mem eG.toMonoidHom (P.decK g).2
  have e : eG (ι (P.decG g) * P.y (P.decC g) * (P.decK g : G)) =
      ι' (eΓ (P.decG g)) * (P.transport eG eΓ hι hρ hJ hχ).y (P.decC g) * ((⟨_, hk⟩ : J') : G') := by
    rw [map_mul, map_mul, hι]; rfl
  rw [e, ClassPres.ext_eq, ClassPres.ext_eq, hχ, hρ]
  rfl

end Read

end GlobalTheory.Mem.R3.LiftPres

namespace GlobalTheory.Mem.R3.LiftPres

open Formalism.IndefR.Bridge

section Assemble

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S : Formalism.L2.Col.GSD K} {G Γ : Type} [Group G] [Group Γ]
  {ι : Γ →* G} {J : Subgroup G}
variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
variable {G' Γ' : Type} [Group G'] [Group Γ'] {ι' : Γ' →* G'}

variable (A : AdPts S ι J) (h : S.Ok) (σ : K →+* ℂ) (ρ' : Γ' →* Module.End ℂ W) (k : G) (eG : G ≃* G') (eΓ : Γ ≃* Γ')
    (hι : ∀ γ, ι' (eΓ γ) = eG (ι γ)) (J' : Subgroup G') (χ' : J' →* ℂˣ)
    (hJ : J' = (J.map (MulAut.conj k).toMonoidHom).map eG.toMonoidHom)
    (coef : S.V →ₛₗ[σ] W) (hli : LinearIndependent ℂ fun i => coef (S.bV i))
    (hspan : Submodule.span ℂ (Set.range fun i => coef (S.bV i)) = ⊤)
    (hpair : ∀ x x', inner ℂ (coef x) (coef x') = σ (S.pair x x'))
    (hK1 : ∀ κ : J, (κ : G) ∈ A.K1 → ∀ hx : eG (k * κ * k⁻¹) ∈ J', χ' ⟨_, hx⟩ = 1)
    (hgl : ∀ (γ : Γ) (κ : J) (v : S.V) (hx : eG (k * κ * k⁻¹) ∈ J'),
      coef (S.ρ (A.gl (γ, κ)) v) = ((χ' ⟨_, hx⟩)⁻¹ : ℂˣ) • ρ' (eΓ γ) (coef v))

end Assemble

end GlobalTheory.Mem.R3.LiftPres

namespace GlobalTheory.Mem.R3.LiftPres

end GlobalTheory.Mem.R3.LiftPres

namespace GlobalTheory.Mem.R3.LiftPres

end GlobalTheory.Mem.R3.LiftPres

namespace GlobalTheory.Mem.R3.LiftPres

theorem ufGL_ratHom {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) (γ : Formalism.L2.Col.URat hc n) :
    Formalism.L2.Col.ufGL E n (Formalism.L2.Col.ratHom hc n γ) = (γ : GL (Fin n) E) := by
  show Formalism.L2.Col.toGLm E n (Formalism.UG.glEquiv (γ : GL (Fin n) E)) = _
  simp only [Formalism.L2.Col.toGLm, Formalism.UG.glEquiv, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]

end GlobalTheory.Mem.R3.LiftPres
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemRowLevelOfReductionMemLevelGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemRowLevelOfReductionMemLevelGroup
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.RowDeco
open GlobalTheory.Mem.R3.RowAd

theorem reindex_symm_reindex {κ : Type} [CommRing κ] {a b : ℕ} (e : Fin a ≃ Fin b) (y : GL (Fin a) κ) :
    Units.map (Matrix.reindexAlgEquiv κ κ e.symm).toMonoidHom (Units.map (Matrix.reindexAlgEquiv κ κ e).toMonoidHom y) = y := by
  apply Units.ext
  ext i j
  simp

theorem of_reindex_mem_HK {κ : Type} [CommRing κ] {a n r t m : ℕ} (h : a = n) (hn : n = r + m * t) (hra : r ≤ a)
    (y : GL (Fin a) κ)
    (hy : Units.map (Matrix.reindexAlgEquiv κ κ (finCongr h)).toMonoidHom y ∈ Formalism.L2.Col.HK n κ r (List.replicate m t)) :
    y ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t) ∧ Formalism.L2.DIV.upperLeftBlock hra y = 1 := by
  subst h
  rw [reindex_finCongr_rfl] at hy
  obtain ⟨hUT, h1⟩ := Formalism.L2.Col.mem_HK.1 hy
  have hb : y ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t) := by
    intro i j hij
    refine hUT (show Formalism.L2.Col.coarse r (List.replicate m t) j.val < Formalism.L2.Col.coarse r (List.replicate m t) i.val from ?_)
    rw [coarse_eq_blkOf hn, coarse_eq_blkOf hn]
    exact hij
  refine ⟨hb, ?_⟩
  apply Units.ext
  rw [Formalism.L2.DIV.upper_block_val_submatrix hra (Formalism.L2.DIV.blockTri_blkOf_le r t hb), Units.val_one]
  ext i j
  rw [Matrix.submatrix_apply, h1 _ _ i.2 j.2]
  simp [Matrix.one_apply, Fin.ext_iff]

theorem of_reindex_mem_HQ {κ : Type} [CommRing κ] {a n r b : ℕ} (h : a = n) (hn : n = r + b) (y : GL (Fin a) κ)
    (hy : Units.map (Matrix.reindexAlgEquiv κ κ (finCongr h)).toMonoidHom y ∈ Formalism.L2.Col.blockUT n κ r [b]) :
    y ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) := by
  subst h
  rw [reindex_finCongr_rfl] at hy
  intro i j hij
  refine hy (show Formalism.L2.Col.coarse r [b] j.val < Formalism.L2.Col.coarse r [b] i.val from ?_)
  rw [coarseBlockIndex_eq_twoBlock hn, coarseBlockIndex_eq_twoBlock hn]
  exact hij

theorem redG_ptE_of (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) {U : Set I.ι}
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (hL : LevOf X I U L) (t : TupU I U) (h : Bridge.Gf X.toD7.sp.X')
    (hSt : Formalism.UG.bc (swapAE X.toD7) ((h : Bridge.Gf X.toD7.sp.X') : GL _ _) ∈ Formalism.L2.DIV.St L.βX)
    (hz : ptE X h ∈ Formalism.L2.Col.J0 X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅)
    (w : Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) :
    Formalism.L2.Col.redG X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ⟨_, hz⟩ w =
      Units.map (Matrix.reindexAlgEquiv (Formalism.L2.DIV.kP w.1) (Formalism.L2.DIV.kP w.1) (finCongr (rank_X' X))).toMonoidHom
        (Formalism.L2.DIV.redFn L.βX w.1 (Formalism.UG.bc (swapAE X.toD7) ((h : Bridge.Gf X.toD7.sp.X') : GL _ _))) :=
  redAt_reindex (finCongr (rank_X' X)) L.βX hL.beta.2 _ hSt (Formalism.L2.Col.congruence_subgroup_le_stabilizer _ _ _ hz) w.1


set_option maxHeartbeats 1000000 in
theorem mem_J_of_redG_mem_grp : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)), I.Ok → LevOf X I U L →
    ∀ (t : TupU I U) (h : Bridge.Gf X.toD7.sp.X') (hz : RowAd.ptE X h ∈ Formalism.L2.Col.J0 X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅),
      Formalism.L2.Col.redG X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ⟨_, hz⟩ ∈
        ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp →
      h ∈ (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J := by
  intro X px I U L hI hL t h hz hred
  have hβ : L.βX = 1 := hL.beta.2
  have hSt : Formalism.UG.bc (swapAE X.toD7) ((h : Bridge.Gf X.toD7.sp.X') : GL _ _) ∈ Formalism.L2.DIV.St L.βX := by
    have h1 := reindex_mem_St_one (finCongr (rank_X' X)).symm (Formalism.L2.Col.congruence_subgroup_le_stabilizer _ _ _ hz)
    have e2 : Units.map (Matrix.reindexAlgEquiv (Formalism.IndefR.Lev.EAf X.toD7) (Formalism.IndefR.Lev.EAf X.toD7)
        (finCongr (rank_X' X)).symm).toMonoidHom (ptE X h) = Formalism.UG.bc (swapAE X.toD7) ((h : Bridge.Gf X.toD7.sp.X') : GL _ _) :=
      reindex_symm_reindex _ _
    rw [hβ]
    exact e2 ▸ h1
  have hUA : Formalism.UG.bc (swapAE X.toD7) ((h : Bridge.Gf X.toD7.sp.X') : GL _ _) ∈
      Formalism.L2.DIV.UA X.toD7.sp.cm X.toD7.sp.X'.gram := by
    obtain ⟨g, hg⟩ := h.2
    rw [← hg]
    exact GlobalTheory.LevSplit.finE_mem_UA X.toD7.sp.X' g
  have hw : ∀ w : Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1,
      Units.map (Matrix.reindexAlgEquiv (Formalism.L2.DIV.kP w.1) (Formalism.L2.DIV.kP w.1) (finCongr (rank_X' X))).toMonoidHom
        (Formalism.L2.DIV.redFn L.βX w.1 (Formalism.UG.bc (swapAE X.toD7) ((h : Bridge.Gf X.toD7.sp.X') : GL _ _))) ∈
        (Formalism.L2.Col.rowTyKK I.Ch I.sel t.1 w).H := fun w => by
    rw [← redG_ptE_of X I L hL t h hSt hz w]
    exact hred w (Set.mem_univ _)
  have hG : ∀ PP ∈ (L.datXt t).Pg,
      Formalism.L2.DIV.redFn L.βX PP (Formalism.UG.bc (swapAE X.toD7) ((h : Bridge.Gf X.toD7.sp.X') : GL _ _)) ∈
                Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf (L.datXt t).r (L.datXt t).t) ∧
        Formalism.L2.DIV.upperLeftBlock (L.datXt t).hr
          (Formalism.L2.DIV.redFn L.βX PP (Formalism.UG.bc (swapAE X.toD7) ((h : Bridge.Gf X.toD7.sp.X') : GL _ _))) = 1 := by
    intro PP hPP
    have hP : PP ∈ (X.B.primes px).vGs := by
      have hP' : PP ∈ L.Pg := hPP
      rw [hL.Pg] at hP'
      exact hP'
    have hm := hw ⟨PP, by classical exact Finset.mem_union_left _ hP⟩
    rw [Formalism.L2.Col.rowTyKK, Formalism.L2.Col.LevFam.glue_of_mem _ _ _ hP] at hm
    exact of_reindex_mem_HK (rank_X' X) (Formalism.L2.Col.rank_X'_eq X.B.R) (L.datXt t).hr _ hm
  have hQ : ∀ PP ∈ (L.datXt t).Q,
      Formalism.L2.DIV.redFn L.βX PP (Formalism.UG.bc (swapAE X.toD7) ((h : Bridge.Gf X.toD7.sp.X') : GL _ _)) ∈
        Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 (L.datXt t).r) := by
    intro PP hPP
    have hq : PP ∈ Formalism.L2.Col.QE I.sel (t.1 : Formalism.L2.DIV.Chr _ _ _) := by
      have hP' : PP ∈ L.Q t := hPP
      have e : I.Q (ixOf I U t) = Formalism.L2.Col.QE I.sel (t.1 : Formalism.L2.DIV.Chr _ _ _) := by
        simp only [ColIn.Q, tup_ixOf]
      rw [hL.Q t, e] at hP'
      exact hP'
    have hm := hw ⟨PP, by classical exact Finset.mem_union_right _ hq⟩
    by_cases hP : PP ∈ (X.B.primes px).vGs
    · rw [Formalism.L2.Col.rowTyKK, Formalism.L2.Col.LevFam.glue_of_mem _ _ _ hP] at hm
      exact Formalism.L2.DIV.blockTri_blkOf_le _ _
        (of_reindex_mem_HK (rank_X' X) (Formalism.L2.Col.rank_X'_eq X.B.R) (L.datXt t).hr _ hm).1
    · rw [Formalism.L2.Col.rowTyKK, Formalism.L2.Col.LevFam.glue_of_not _ _ _ hP] at hm
      exact of_reindex_mem_HQ (rank_X' X) (Formalism.L2.Col.rank_X'_eq X.B.R) _ hm
  exact ⟨Formalism.L2.DIV.mem_parLev.2 ⟨hUA, hSt, fun PP hP => (hG PP hP).1, hQ⟩,
    Subgroup.mem_bot.2 (funext fun PP => (hG PP.1 PP.2).2)⟩

end GlobalTheory.Mem.R3.RowDeco
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemRowLevelOfReductionMemLevelGroupStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_rowLevel_of_reduction_mem_levelGroup : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)), I.Ok → LevOf X I U L →
    ∀ (t : TupU I U) (h : Bridge.Gf X.toD7.sp.X') (hz : RowAd.ptE X h ∈ Formalism.L2.Col.J0 X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅),
      Formalism.L2.Col.redG X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ⟨_, hz⟩ ∈
        ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp →
      h ∈ (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J := by
  first | exact @GlobalTheory.Mem.R3.RowDeco.mem_J_of_redG_mem_grp | exact GlobalTheory.Mem.R3.RowDeco.mem_J_of_redG_mem_grp | (intros; apply GlobalTheory.Mem.R3.RowDeco.mem_J_of_redG_mem_grp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRationalUnitaryEquivRowStageCompat
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRationalUnitaryEquivRowStageCompat
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section

namespace GlobalTheory.Mem.R3.RowStdRat

open GlobalTheory.Mem.R3.RowAd GlobalTheory.Mem.R3.LiftBrg.StdGroups

theorem ptE_eq (X : Stages) (h : Bridge.Gf X.toD7.sp.X') :
    ptE X h = LiftBrg.castGL (rank_X' X) (Formalism.UG.bc (swapAE X.toD7) h.1) := rfl

def psiX (X : Stages) (hg : X.toD7.sp.X'.gram = 1) :
    Formalism.L2.Col.URat X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) →* GQ X.toD7.sp.X' where
  toFun γ :=
    have hm : LiftBrg.castGL (rank_X' X).symm (γ : GL (Fin (X.B.R.N X.B.R.m - 1)) X.toD7.host.E) ∈
        Formalism.UG.UJ (X.toD7.sp.cm.sig : X.toD7.host.E →+* X.toD7.host.E) X.toD7.sp.X'.gram := by
      rw [hg]
      exact castGL_mem_UJ_one _ _ _ γ.2
    ⟨(show GA X.toD7 X.toD7.sp.X' from
        (⟨Formalism.UG.bc (inclR (F := X.toD7.host.F) (AF X.toD7.host.F))
            (LiftBrg.castGL (rank_X' X).symm (γ : GL (Fin (X.B.R.N X.B.R.m - 1)) X.toD7.host.E)),
          bc_inclR_mem_HR _ _ _ _ hm⟩ : HR (AF X.toD7.host.F) X.toD7.sp.cm.sig X.toD7.sp.X'.gram)),
      Subgroup.mem_subgroupOf.2 ⟨_, hm, rfl⟩⟩
  map_one' := Subtype.ext (Subtype.ext (by first | rfl | (simp only [map_one]; rfl) | (simp <;> rfl)))
  map_mul' a b := Subtype.ext (Subtype.ext (by first | rfl | (simp only [map_mul]; rfl) | (simp <;> rfl)))

theorem psiX_mat (X : Stages) (hg : X.toD7.sp.X'.gram = 1) (γ : Formalism.L2.Col.URat X.toD7.sp.cm (X.B.R.N X.B.R.m - 1)) :
    matHom X.toD7.sp.X' (psiX X hg γ : GA X.toD7 X.toD7.sp.X') =
      Formalism.UG.bc (incA X.toD7) (LiftBrg.castGL (rank_X' X).symm (γ : GL (Fin (X.B.R.N X.B.R.m - 1)) X.toD7.host.E)) := rfl

theorem ptE_ratF_psiX (X : Stages) (hg : X.toD7.sp.X'.gram = 1) (γ : Formalism.L2.Col.URat X.toD7.sp.cm (X.B.R.N X.B.R.m - 1)) :
    ptE X (Bridge.ratF X.toD7.sp.X' (psiX X hg γ)) = (Formalism.L2.Col.ratIn X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) γ).1 := by
  rw [ptE_eq, Formalism.L2.Col.ratIn_val]
  have e1 : ((Bridge.ratF X.toD7.sp.X' (psiX X hg γ)) : GL (Fin X.toD7.sp.X'.rank) _) =
      Formalism.UG.bc (inclR (F := X.toD7.host.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.toD7.host.F))
        (LiftBrg.castGL (rank_X' X).symm (γ : GL (Fin (X.B.R.N X.B.R.m - 1)) X.toD7.host.E)) := by
    change finHom X.toD7.sp.X' _ = _
    rw [finHom, MonoidHom.comp_apply, Subgroup.coe_subtype, psiX_mat]
    exact GlobalTheory.HLatMove.bc_map_bc_inclR _ _
  rw [e1]
  have e2 : Formalism.UG.bc (swapAE X.toD7) (Formalism.UG.bc (inclR (F := X.toD7.host.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.toD7.host.F))
      (LiftBrg.castGL (rank_X' X).symm (γ : GL (Fin (X.B.R.N X.B.R.m - 1)) X.toD7.host.E))) =
      Formalism.UG.bc (Formalism.L2.Col.iA X.toD7.host.F X.toD7.host.E)
        (LiftBrg.castGL (rank_X' X).symm (γ : GL (Fin (X.B.R.N X.B.R.m - 1)) X.toD7.host.E)) := by
    ext a b
    simp [Formalism.UG.bc, swapAE, inclR, Formalism.UG.inclE]
  rw [e2, ← castGL_bc, castGL_symm_castGL']

end GlobalTheory.Mem.R3.RowStdRat

namespace GlobalTheory.Mem.R3.RowStdRat

open GlobalTheory.Mem.R3.RowAd GlobalTheory.Mem.R3.LiftBrg.StdGroups

theorem psiX_injective (X : Stages) (hg : X.toD7.sp.X'.gram = 1) : Function.Injective (psiX X hg) := by
  intro a b hab
  have h2 : (Formalism.L2.Col.ratIn X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) a).1 = (Formalism.L2.Col.ratIn X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) b).1 := by
    rw [← ptE_ratF_psiX X hg a, ← ptE_ratF_psiX X hg b, hab]
  simp only [Formalism.L2.Col.ratIn_val] at h2
  exact Subtype.ext (Formalism.L2.DIV.incl_inj _ _ _ h2)

theorem psiX_surjective (X : Stages) (hg : X.toD7.sp.X'.gram = 1) : Function.Surjective (psiX X hg) := by
  intro δ
  obtain ⟨γE, hγE, e⟩ := Subgroup.mem_subgroupOf.1 δ.2
  have hγ : LiftBrg.castGL (rank_X' X) γE ∈ Formalism.L2.Col.URat X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) := by
    rw [hg] at hγE
    exact castGL_mem_UJ_one _ _ _ hγE
  refine ⟨⟨_, hγ⟩, Subtype.ext (Subtype.ext ?_)⟩
  change Formalism.UG.bc (inclR (F := X.toD7.host.F) (AF X.toD7.host.F))
    (LiftBrg.castGL (rank_X' X).symm (LiftBrg.castGL (rank_X' X) γE)) = _
  rw [castGL_symm_castGL' (rank_X' X) γE]
  exact e

theorem matEq_castGL {A : Type} [CommRing A] {m n : ℕ} (h : m = n) (x : GL (Fin m) A) : MatEq (LiftBrg.castGL h x) x := by
  subst h
  refine ⟨rfl, fun i j i' j' hi hj => ?_⟩
  have hi' : i = i' := Fin.ext hi
  have hj' : j = j' := Fin.ext hj
  subst hi' hj'
  simp [LiftBrg.castGL, Matrix.reindexAlgEquiv_apply]

theorem stdRat_equiv : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px), I.Ok →
    ∀ (e : Formalism.L2.Col.UAd X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ≃* Bridge.Gf X.toD7.sp.X'),
    (∀ x, RowAd.ptE X (e x) = x.1) →
    ∃ eΓ : Formalism.L2.Col.URat X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ≃* GQ X.toD7.sp.X',
      (∀ γ, Bridge.ratF X.toD7.sp.X' (eΓ γ) = e (Formalism.L2.Col.ratIn X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) γ)) ∧
      ∀ γ, ∃ γE : GL (Fin X.toD7.sp.X'.rank) X.toD7.host.E, Bridge.IsRatMat X.toD7.sp.X' (eΓ γ) γE ∧
        MatEq γE γ.1 := by
  intro X px I hI e he
  have hg := RowDeco.gram_X'_eq_one X I hI
  have hinj : Function.Injective (ptE X) := by
    intro h h' hh
    obtain ⟨x, rfl⟩ := e.surjective h
    obtain ⟨x', rfl⟩ := e.surjective h'
    rw [he, he] at hh
    rw [Subtype.ext hh]
  refine ⟨MulEquiv.ofBijective (psiX X hg) ⟨psiX_injective X hg, psiX_surjective X hg⟩, fun γ => ?_, fun γ => ?_⟩
  · apply hinj
    rw [he]
    exact ptE_ratF_psiX X hg γ
  · exact ⟨LiftBrg.castGL (rank_X' X).symm (γ : GL (Fin (X.B.R.N X.B.R.m - 1)) X.toD7.host.E), psiX_mat X hg γ,
      matEq_castGL _ _⟩

end GlobalTheory.Mem.R3.RowStdRat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRationalUnitaryEquivRowStageCompatStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_unitary_equiv_rowStage_compat : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px), I.Ok →
    ∀ (e : Formalism.L2.Col.UAd X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ≃* Bridge.Gf X.toD7.sp.X'),
    (∀ x, RowAd.ptE X (e x) = x.1) →
    ∃ eΓ : Formalism.L2.Col.URat X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ≃* GQ X.toD7.sp.X',
      (∀ γ, Bridge.ratF X.toD7.sp.X' (eΓ γ) = e (Formalism.L2.Col.ratIn X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) γ)) ∧
      ∀ γ, ∃ γE : GL (Fin X.toD7.sp.X'.rank) X.toD7.host.E, Bridge.IsRatMat X.toD7.sp.X' (eΓ γ) γE ∧
        MatEq γE γ.1 := by
  first | exact @GlobalTheory.Mem.R3.RowStdRat.stdRat_equiv | exact GlobalTheory.Mem.R3.RowStdRat.stdRat_equiv | (intros; apply GlobalTheory.Mem.R3.RowStdRat.stdRat_equiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivRowStageUnitaryStandardAdelic
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivRowStageUnitaryStandardAdelic
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.Mem.R3.RowStdGrp

open GlobalTheory.Mem.R3.RowAd GlobalTheory.Mem.R3.RowDeco GlobalTheory.Mem.R3.LiftBrg

theorem ptE_eq_castGL (X : Stages) (h : Bridge.Gf X.toD7.sp.X') :
    ptE X h = castGL (rank_X' X) (Formalism.UG.bc (swapAE X.toD7) h.1) := rfl

def ptHom (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hI : I.Ok) :
    Bridge.Gf X.toD7.sp.X' →* Formalism.L2.Col.UAd X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) where
  toFun h := ⟨ptE X h, ptE_mem_UAd X I hI h⟩
  map_one' := Subtype.ext (by
    show ptE X 1 = 1
    exact mul_left_cancel (a := ptE X 1) (by rw [← ptE_mul, mul_one, mul_one]))
  map_mul' a b := Subtype.ext (ptE_mul X a b)

theorem ptHom_val (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hI : I.Ok) (h : Bridge.Gf X.toD7.sp.X') :
    (ptHom X I hI h).1 = ptE X h := rfl

theorem ptHom_injective (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hI : I.Ok) :
    Function.Injective (ptHom X I hI) := by
  intro a b hab
  have h1 := congrArg Subtype.val hab
  simp only [ptHom_val, ptE_eq_castGL] at h1
  have h2 := (castGL (rank_X' X)).injective h1
  exact Subtype.ext (StdGroups.bc_injective _ (Algebra.TensorProduct.comm _ _ _).injective h2)

theorem ptHom_surjective (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hI : I.Ok) :
    Function.Surjective (ptHom X I hI) := by
  intro x
  have hy : castGL (rank_X' X).symm x.1 ∈ Formalism.L2.DIV.UA X.toD7.sp.cm X.toD7.sp.X'.gram := by
    rw [gram_X'_eq_one X I hI]
    exact castGL_mem_UA_std _ _ _ x.2
  refine ⟨⟨finHom X.toD7.sp.X' (GlobalTheory.StdFrameExist.liftF X.toD7.sp.X' _ hy), _, rfl⟩, Subtype.ext ?_⟩
  rw [ptHom_val, ptE_eq_castGL]
  have e := GlobalTheory.StdFrameExist.finE_liftF X.toD7.sp.X' _ hy
  change castGL (rank_X' X) (finE X.toD7.sp.X' (GlobalTheory.StdFrameExist.liftF X.toD7.sp.X' _ hy)) = _
  rw [e, StdGroups.castGL_symm_castGL']

theorem ptE_equiv : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px), I.Ok →
    ∃ e : Formalism.L2.Col.UAd X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ≃* Bridge.Gf X.toD7.sp.X',
      ∀ x, RowAd.ptE X (e x) = x.1 := by
  intro X px I hI
  let e0 := MulEquiv.ofBijective (ptHom X I hI) ⟨ptHom_injective X I hI, ptHom_surjective X I hI⟩
  refine ⟨e0.symm, fun x => ?_⟩
  have h := e0.apply_symm_apply x
  exact congrArg Subtype.val h

end GlobalTheory.Mem.R3.RowStdGrp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivRowStageUnitaryStandardAdelicStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equiv_rowStage_unitary_standard_adelic : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px), I.Ok →
    ∃ e : Formalism.L2.Col.UAd X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ≃* Bridge.Gf X.toD7.sp.X',
      ∀ x, RowAd.ptE X (e x) = x.1 := by
  first | exact @GlobalTheory.Mem.R3.RowStdGrp.ptE_equiv | exact GlobalTheory.Mem.R3.RowStdGrp.ptE_equiv | (intros; apply GlobalTheory.Mem.R3.RowStdGrp.ptE_equiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefficientMapLevelCharacterEquivariant
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.RowStdPres

open Formalism.IndefR.Bridge

section Generic

variable {Xf : Formalism.L2.Col.Fields} {n : ℕ} {SG : Finset (HeightOneSpectrum (𝓞 Xf.E))} (Λ : Formalism.L2.Col.LevFam Xf.E Xf.K n SG)

theorem mem_grp_of_inv_mul (a b : Formalism.L2.Col.GLG (E := Xf.E) (n := n) (SG := SG)) (hb : b = 1) (hu : a⁻¹ * b ∈ Λ.grp) : a ∈ Λ.grp := by
  subst hb
  rw [mul_one] at hu
  exact (Subgroup.inv_mem_iff _).1 hu

theorem inv_mul_mem_grp (a b : Formalism.L2.Col.GLG (E := Xf.E) (n := n) (SG := SG)) (hb : b = 1) (ha : a ∈ Λ.grp) : a⁻¹ * b ∈ Λ.grp := by
  subst hb
  rw [mul_one]
  exact Λ.grp.inv_mem ha

theorem chr_of_inv_mul (σ : Xf.K →+* ℂ) (a b : Formalism.L2.Col.GLG (E := Xf.E) (n := n) (SG := SG)) (hb : b = 1) (ha : a ∈ Λ.grp) (hu : a⁻¹ * b ∈ Λ.grp)
    (z : ℂˣ) (hz : σ ((Λ.chr ⟨_, hu⟩ : Xf.Kˣ) : Xf.K) = (z : ℂ)) :
    σ ((Λ.chr ⟨a, ha⟩ : Xf.Kˣ) : Xf.K) = ((z⁻¹ : ℂˣ) : ℂ) := by
  subst hb
  have e : (⟨a⁻¹ * 1, hu⟩ : Λ.grp) = (⟨a, ha⟩ : Λ.grp)⁻¹ := Subtype.ext (mul_one _)
  rw [e, map_inv, Units.val_inv_eq_inv_val, map_inv₀] at hz
  rw [Units.val_inv_eq_inv_val, ← hz, inv_inv]

variable [NeZero n] (hc : Formalism.BasicNotions.CMData Xf.F Xf.E)

theorem character_trivial_on_reduction_kernel (σ : Xf.K →+* ℂ) (k : colJ hc n ∅ SG Λ.grp) (hk : (k : Formalism.L2.Col.UAd hc n) ∈ principalCongruenceSubgroup hc n ∅ SG) :
    σ ((Λ.chr (Formalism.L2.Col.redH hc n ∅ SG Λ.grp ((colJEquiv hc n ∅ SG Λ.grp).symm k)) : Xf.Kˣ) : Xf.K) = 1 := by
  rw [← colJEquiv_symm_coe, mem_principal_congruence_iff] at hk
  have hr : Formalism.L2.Col.redH hc n ∅ SG Λ.grp ((colJEquiv hc n ∅ SG Λ.grp).symm k) = 1 := Subtype.ext hk
  rw [hr, map_one, Units.val_one, map_one]

theorem formRho_colGl (C : Formalism.L2.Col.CoefPk Xf n (Formalism.L2.Col.DecoSet (E := Xf.E) (n := n) (ST := ∅) (SG := SG)))
    (γ : Formalism.L2.Col.URat hc n) (k : colJ hc n ∅ SG Λ.grp) (v : C.V) :
    (Formalism.L2.Col.formGSD C Λ).ρ (colGl (Formalism.L2.Col.rf_onDeco C Λ) (γ, k)) v =
      ((Λ.chr (Formalism.L2.Col.redH hc n ∅ SG Λ.grp ((colJEquiv hc n ∅ SG Λ.grp).symm k)) : Xf.Kˣ) : Xf.K) •
        C.rho (Formalism.L2.Col.ratHom hc n γ) v := rfl

end Generic


set_option maxHeartbeats 1000000 in
theorem standard_level_element_hat_eq_one (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r) (t : TupU I U)
    (k : (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J) :
    Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_X' X.B.R)
                (eG.symm (rTup L.βX (L.datXt t) (Formalism.UG.bc (swapAE X.toD7) ((k : Bridge.Gf X.toD7.sp.X') : GL _ _)))) = 1 := by
  have h1 : rTup L.βX (L.datXt t) (Formalism.UG.bc (swapAE X.toD7) ((k : Bridge.Gf X.toD7.sp.X') : GL _ _)) = 1 :=
    (RowAct.rTupQ_eq_one_iff X.toD7.sp.X' L.βX (L.datXt t) ⟨k.1, (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J_le k.2⟩).2 k.2
  have h2 : eG.symm (rTup L.βX (L.datXt t) (Formalism.UG.bc (swapAE X.toD7) ((k : Bridge.Gf X.toD7.sp.X') : GL _ _))) = 1 :=
    (congrArg eG.symm h1).trans (map_one eG.symm)
  exact (congrArg (Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_X' X.B.R)) h2).trans (map_one _)


set_option maxHeartbeats 1000000 in
theorem deco_surj (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (hI : I.Ok) (hL : LevOf X I U L) (t : TupU I U) :
    Formalism.L2.Col.DecoPtSurj X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) :=
  Formalism.L2.Col.decoPtSurj_of _ _ _ _ (Formalism.L2.Col.unimodGenus_holds _ _) Formalism.L2.DIV.reduction_surjective_bis
    (by classical convert GlobalTheory.Mem.R3.LiftBrg.isSplitSet_sgL X px I U L hI hL t using 1; exact Finset.empty_union _)
    (Finset.disjoint_empty_left _)


set_option maxHeartbeats 1000000 in
theorem lev_iff (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r) (hI : I.Ok) (hL : LevOf X I U L)
    (hG : IsPlacewiseIdentity X (px := px) eG) (t : TupU I U) (h : Bridge.Gf X.toD7.sp.X') :
      h ∈ (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J ↔
        ∃ hz : RowAd.ptE X h ∈ Formalism.L2.Col.J0 X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅,
          Formalism.L2.Col.redG X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ⟨_, hz⟩ ∈
            ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp := by
  constructor
  · intro hh
    have hz := RowDeco.unitaryFiniteAdelicPointAsMatrix_mem_flagIwahori X I hI L hL t ⟨h, (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J_le hh⟩
    exact ⟨hz, mem_grp_of_inv_mul (Xf := X.B.fields) (Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv _ _
      (standard_level_element_hat_eq_one X px I U L eG t ⟨h, hh⟩)
      (GlobalTheory.T.inv_reduction_mul_flagTranslation_mem_rowLevelGroup X px I U L eG hI hL hG t ⟨h, (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J_le hh⟩ hz)⟩
  · rintro ⟨hz, hg⟩
    exact GlobalTheory.T.mem_rowLevel_of_reduction_mem_levelGroup X px I U L hI hL t h hz hg


set_option maxHeartbeats 1000000 in
theorem chi_eq : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r),
    I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG →
    ∀ (t : TupU I U) (k : (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J)
      (hz : RowAd.ptE X (k : Bridge.Gf X.toD7.sp.X') ∈ Formalism.L2.Col.J0 X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅)
      (hg : Formalism.L2.Col.redG X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ⟨_, hz⟩ ∈
            ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp),
      X.toD7.what₂.embLL (((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv.chr ⟨_, hg⟩ : X.B.fields.Kˣ) : X.B.fields.K) =
        ((((levEnv X.toD7.sp.X' L.βX (L.datXt t)).χ k)⁻¹ : ℂˣ) : ℂ) := by
  intro X px I U L eG hI hV hL hG t k hz hg
  have hb := standard_level_element_hat_eq_one X px I U L eG t k
  have hu := inv_mul_mem_grp (Xf := X.B.fields) (Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv _ _ hb hg
  have h1 := GlobalTheory.T.rowLevelCharacter_translation_eq_flagCharacter X px I U L eG hI hV hL hG t ⟨k.1, (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J_le k.2⟩ hz hu
  exact chr_of_inv_mul (Xf := X.B.fields) (Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv X.B.embLL _ _ hb hg hu _
    (h1.trans (congrArg Units.val ((levEnv X.toD7.sp.X' L.βX (L.datXt t)).ch_J k)))


set_option maxHeartbeats 1000000 in
theorem lev_eq_map (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r) (hI : I.Ok) (hL : LevOf X I U L)
    (hG : IsPlacewiseIdentity X (px := px) eG) (t : TupU I U)
    (e : Formalism.L2.Col.UAd X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ≃* Bridge.Gf X.toD7.sp.X') (he : ∀ x, RowAd.ptE X (e x) = x.1) :
    (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J =
      (colJ X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1)
        ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp).map e.toMonoidHom := by
  ext h
  rw [lev_iff X px I U L eG hI hL hG t h]
  constructor
  · rintro ⟨hz, hg⟩
    have e1 : RowAd.ptE X h = (e.symm h).1 := by
      have := he (e.symm h)
      rwa [MulEquiv.apply_symm_apply] at this
    refine ⟨e.symm h, ⟨⟨RowAd.ptE X h, hz⟩, hg, Subtype.ext e1⟩, by simp⟩
  · rintro ⟨x, ⟨m, hm, rfl⟩, rfl⟩
    have e1 : RowAd.ptE X (e (Formalism.L2.Col.ToUnitaryAdelic X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ m)) = m.1 := he _
    have hz : RowAd.ptE X (e (Formalism.L2.Col.ToUnitaryAdelic X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ m)) ∈
        Formalism.L2.Col.J0 X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ := by
      rw [e1]; exact m.2
    refine ⟨hz, ?_⟩
    have e2 : (⟨_, hz⟩ : Formalism.L2.Col.J0 X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅) = m := Subtype.ext e1
    exact (congrArg (fun z => Formalism.L2.Col.redG X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) z ∈
      ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp) e2).mpr hm

def levE {G G' : Type} [Group G] [Group G'] (e : G ≃* G') (J : Subgroup G) (J' : Subgroup G') (hJ : J' = J.map e.toMonoidHom) :
    J ≃* J' :=
  (J.equivMapOfInjective e.toMonoidHom e.injective).trans (MulEquiv.subgroupCongr hJ.symm)

theorem levE_coe {G G' : Type} [Group G] [Group G'] (e : G ≃* G') (J : Subgroup G) (J' : Subgroup G')
    (hJ : J' = J.map e.toMonoidHom) (k : J) : ((levE e J J' hJ k : J') : G') = e k := rfl


set_option maxHeartbeats 4000000 in
theorem exists_pres : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → L.βX = 1 → ∀ (cX : CoefA X.toD7.sp.X') (c : VV X.B.fields.K X.B.wts.sgTrue →ₛₗ[X.B.embLL] cX.W), (∀ (γ : GQ X.toD7.sp.X') (γE : GL (Fin X.toD7.sp.X'.rank) X.toD7.host.E) (g : GL (Fin (X.B.R.N X.B.R.m - 1)) X.B.fields.E), Bridge.IsRatMat X.toD7.sp.X' γ γE → MatEq γE g → ∀ v, c (rhoV X.B.fields.emb X.B.wts.sgTrue g v) = cX.coef.ρ γ (c v)) → LinearIndependent ℂ (fun i => c (bVV X.B.fields.K X.B.wts.sgTrue i)) → Submodule.span ℂ (Set.range fun i => c (bVV X.B.fields.K X.B.wts.sgTrue i)) = ⊤ → (∀ x y, inner ℂ (c x) (c y) = X.B.embLL (pairV X.B.fields.emb X.B.wts.sgTrue 1 x y)) → ∀ t, ∃ P : Bridge.ClassPres (Bridge.ratF X.toD7.sp.X') ((famR X I hX U Xg tr).A.MtildeCSD t) X.toD7.what₂.embLL cX.coef.ρ (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J (levEnv X.toD7.sp.X' L.βX (L.datXt t)).χ, (∀ x, P.coef x = c x) ∧ (∀ c', RowAd.decoAd X I t (P.y c') = (Formalism.L2.Col.mtildeKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1).outSec.rep c') ∧ ∀ (f : ((famR X I hX U Xg tr).A.MtildeCSD t).Forms) (h : Bridge.Gf X.toD7.sp.X'), P.ext (f : _ → _) h = c ((((Formalism.L2.Col.mtildeKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1).res (Formalism.L2.Col.mtildeKOk _ _ _ _ hX)).symm f).1 (RowAd.decoAd X I t h)) := by
  intro X px I hX U Xg tr L eG hI hV hL hG hβ cX c hint hli hspan hpair t
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_equiv_rowStage_unitary_standard_adelic X px I hI
  obtain ⟨eΓ, hι, hrat⟩ := GlobalTheory.T.exists_rational_unitary_equiv_rowStage_compat X px I hI e he
  have hS := deco_surj X px I U L hI hL t
  have hJ := lev_eq_map X px I U L eG hI hL hG t e he
  let χ' : colJ X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1)
        ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp →* ℂˣ :=
    (levEnv X.toD7.sp.X' L.βX (L.datXt t)).χ.comp (levE e _ _ hJ).toMonoidHom
  let coef : (Formalism.L2.Col.mtildeKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1).V →ₛₗ[X.B.embLL] cX.W := c
  have hchar : ∀ k : colJ X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp,
      X.B.embLL (((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv.chr
        (Formalism.L2.Col.redH X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp ((colJEquiv X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp).symm k)) : X.B.fields.Kˣ) : X.B.fields.K) =
        (((χ' k)⁻¹ : ℂˣ) : ℂ) := by
    intro k
    have e1 : RowAd.ptE X ((levE e _ _ hJ k : (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J) : Bridge.Gf X.toD7.sp.X') =
        ((((colJEquiv X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp).symm k : Formalism.L2.Col.JH X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp) : Formalism.L2.Col.J0 X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅) :
          GL (Fin (X.B.R.N X.B.R.m - 1)) (X.toD7.host.E ⊗[↥X.toD7.host.F] Formalism.L2.Herm.Af ↥X.toD7.host.F)) := by
      rw [levE_coe, he]
      exact congrArg Subtype.val (colJEquiv_symm_coe X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp k).symm
    have hz : RowAd.ptE X ((levE e _ _ hJ k : (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J) : Bridge.Gf X.toD7.sp.X') ∈
        Formalism.L2.Col.J0 X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ := by
      rw [e1]; exact (((colJEquiv X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp).symm k : Formalism.L2.Col.JH X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp) : Formalism.L2.Col.J0 X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅).2
    have e2 : (⟨_, hz⟩ : Formalism.L2.Col.J0 X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅) =
        (((colJEquiv X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp).symm k : Formalism.L2.Col.JH X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp) : Formalism.L2.Col.J0 X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅) :=
      Subtype.ext e1
    have hg : Formalism.L2.Col.redG X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ⟨_, hz⟩ ∈ ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp := by
      rw [e2]; exact ((colJEquiv X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp).symm k).2
    have h3 := chi_eq X px I U L eG hI hV hL hG t (levE e _ _ hJ k) hz hg
    have e3 : Formalism.L2.Col.redH X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp ((colJEquiv X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp).symm k) = ⟨_, hg⟩ :=
      Subtype.ext (congrArg (Formalism.L2.Col.redG X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1)) e2.symm)
    rw [e3]
    exact h3
  have hK1 : ∀ k : colJ X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp,
      (k : Formalism.L2.Col.UAd X.toD7.sp.cm (X.B.R.N X.B.R.m - 1)) ∈ principalCongruenceSubgroup X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) → χ' k = 1 := by
    intro k hk
    have h4 := (hchar k).symm.trans (character_trivial_on_reduction_kernel (Xf := X.B.fields) (Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv
      X.toD7.sp.cm X.B.embLL k hk)
    have h5 : (χ' k)⁻¹ = 1 := Units.ext h4
    exact inv_eq_one.mp h5
  have hgl : ∀ (γ : Formalism.L2.Col.URat X.toD7.sp.cm (X.B.R.N X.B.R.m - 1))
      (k : colJ X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1)
        ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp)
      (v : (Formalism.L2.Col.mtildeKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1).V),
      coef ((Formalism.L2.Col.mtildeKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1).ρ
      (colGl (hc := X.toD7.sp.cm) (Formalism.L2.Col.rf_onDeco (Formalism.L2.Col.rowVal (Pr := X.B.primes px) X.B.wts (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1))
        (Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv) (γ, k)) v) =
      ((χ' k)⁻¹ : ℂˣ) • (cX.coef.ρ.comp eΓ.toMonoidHom) γ (coef v) := by
    intro γ k v
    refine (congrArg coef (formRho_colGl (Xf := X.B.fields) (Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv X.toD7.sp.cm
      (Formalism.L2.Col.rowVal (Pr := X.B.primes px) X.B.wts (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1)) γ k v)).trans ?_
    refine (c.map_smulₛₗ _ _).trans ?_
    obtain ⟨γE, hr, hm⟩ := hrat γ
    have e3 : (Formalism.L2.Col.rowVal (Pr := X.B.primes px) X.B.wts (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1)).rho (Formalism.L2.Col.ratHom X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) γ) v =
        rhoV X.B.fields.emb X.B.wts.sgTrue γ.1 v :=
      congrArg (fun g => rhoV X.B.fields.emb X.B.wts.sgTrue g v) (LiftPres.ufGL_ratHom X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) γ)
    have e4 := (congrArg c e3).trans (hint (eΓ γ) γE γ.1 hr hm v)
    exact congrArg₂ (fun (a : ℂ) (w : cX.W) => a • w) (hchar k) e4
  let P0 := colClassPres (F := ↥X.toD7.host.F) (E := X.toD7.host.E) (hc := X.toD7.sp.cm) (Formalism.L2.Col.rf_onDeco (Formalism.L2.Col.rowVal (Pr := X.B.primes px) X.B.wts (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1))
        (Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv) hS
      (Formalism.L2.Col.mtildeKOk (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1 hX) X.B.embLL
      (cX.coef.ρ.comp eΓ.toMonoidHom) χ' coef hli hspan hpair hK1 hgl
  have hq : ∀ x : Formalism.L2.Col.UAd X.toD7.sp.cm (X.B.R.N X.B.R.m - 1),
      colQ (hc := X.toD7.sp.cm) (Formalism.L2.Col.rf_onDeco (Formalism.L2.Col.rowVal (Pr := X.B.primes px) X.B.wts (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1))
        (Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv) x = RowAd.decoAd X I t (e x) := by
    intro x
    refine (Formalism.L2.Col.decoPt_mk (F := ↥X.toD7.host.F) (E := X.toD7.host.E) X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅
      (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) x).trans ?_
    unfold RowAd.decoAd
    rw [he]
    rfl
  have hχ : ∀ (k : colJ X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1)
        ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp) (hk : e k ∈ (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J),
      (levEnv X.toD7.sp.X' L.βX (L.datXt t)).χ ⟨e k, hk⟩ = χ' k := fun k hk => rfl
  have hρ : ∀ γ, cX.coef.ρ (eΓ γ) = (cX.coef.ρ.comp eΓ.toMonoidHom) γ := fun _ => rfl
  refine ⟨P0.transport e eΓ hι hρ hJ hχ, fun x => rfl, ?_, ?_⟩
  · intro c'
    exact (hq _).symm.trans ((colAdPts (hc := X.toD7.sp.cm) (Formalism.L2.Col.rf_onDeco (Formalism.L2.Col.rowVal (Pr := X.B.primes px) X.B.wts (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1))
        (Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv) hS).q_y c')
  · intro f h
    have h1 := GlobalTheory.Mem.R3.LiftPres.transport_ext P0 e eΓ hι hρ hJ hχ f (e.symm h)
    rw [MulEquiv.apply_symm_apply] at h1
    refine h1.trans ?_
    refine (GlobalTheory.Mem.R3.LiftPres.classPresOf_ext (colAdPts (hc := X.toD7.sp.cm) (Formalism.L2.Col.rf_onDeco (Formalism.L2.Col.rowVal (Pr := X.B.primes px) X.B.wts (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1))
        (Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv) hS) _ _ _ _ coef hli hspan hpair hK1 hgl f
      (e.symm h)).trans ?_
    have h2 : (colAdPts (hc := X.toD7.sp.cm) (Formalism.L2.Col.rf_onDeco (Formalism.L2.Col.rowVal (Pr := X.B.primes px) X.B.wts (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1))
        (Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv) hS).q (e.symm h) = RowAd.decoAd X I t h :=
      (hq _).trans (by rw [MulEquiv.apply_symm_apply])
    rw [h2]
    rfl

end GlobalTheory.Mem.R3.RowStdPres
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefficientMapLevelCharacterEquivariantStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficient_map_level_character_equivariant : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → L.βX = 1 → ∀ (cX : CoefA X.toD7.sp.X') (c : VV X.B.fields.K X.B.wts.sgTrue →ₛₗ[X.B.embLL] cX.W), (∀ (γ : GQ X.toD7.sp.X') (γE : GL (Fin X.toD7.sp.X'.rank) X.toD7.host.E) (g : GL (Fin (X.B.R.N X.B.R.m - 1)) X.B.fields.E), Bridge.IsRatMat X.toD7.sp.X' γ γE → MatEq γE g → ∀ v, c (rhoV X.B.fields.emb X.B.wts.sgTrue g v) = cX.coef.ρ γ (c v)) → LinearIndependent ℂ (fun i => c (bVV X.B.fields.K X.B.wts.sgTrue i)) → Submodule.span ℂ (Set.range fun i => c (bVV X.B.fields.K X.B.wts.sgTrue i)) = ⊤ → (∀ x y, inner ℂ (c x) (c y) = X.B.embLL (pairV X.B.fields.emb X.B.wts.sgTrue 1 x y)) → ∀ t, ∃ P : Bridge.ClassPres (Bridge.ratF X.toD7.sp.X') ((famR X I hX U Xg tr).A.MtildeCSD t) X.toD7.what₂.embLL cX.coef.ρ (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J (levEnv X.toD7.sp.X' L.βX (L.datXt t)).χ, (∀ x, P.coef x = c x) ∧ (∀ c', RowAd.decoAd X I t (P.y c') = (Formalism.L2.Col.mtildeKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1).outSec.rep c') ∧ ∀ (f : ((famR X I hX U Xg tr).A.MtildeCSD t).Forms) (h : Bridge.Gf X.toD7.sp.X'), P.ext (f : _ → _) h = c ((((Formalism.L2.Col.mtildeKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1).res (Formalism.L2.Col.mtildeKOk _ _ _ _ hX)).symm f).1 (RowAd.decoAd X I t h)) := by
  first | exact @GlobalTheory.Mem.R3.RowStdPres.exists_pres | exact GlobalTheory.Mem.R3.RowStdPres.exists_pres | (intros; apply GlobalTheory.Mem.R3.RowStdPres.exists_pres <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowsClassSetPresentationCoefficientMap
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

namespace GlobalTheory

theorem rowsClassPresLink : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → L.βX = 1 → ∀ (cX : CoefA X.toD7.sp.X') (c : VV X.B.fields.K X.B.wts.sgTrue →ₛₗ[X.B.embLL] cX.W), (∀ (γ : GQ X.toD7.sp.X') (γE : GL (Fin X.toD7.sp.X'.rank) X.toD7.host.E) (g : GL (Fin (X.B.R.N X.B.R.m - 1)) X.B.fields.E), Bridge.IsRatMat X.toD7.sp.X' γ γE → MatEq γE g → ∀ v, c (rhoV X.B.fields.emb X.B.wts.sgTrue g v) = cX.coef.ρ γ (c v)) → LinearIndependent ℂ (fun i => c (bVV X.B.fields.K X.B.wts.sgTrue i)) → Submodule.span ℂ (Set.range fun i => c (bVV X.B.fields.K X.B.wts.sgTrue i)) = ⊤ → (∀ x y, inner ℂ (c x) (c y) = X.B.embLL (pairV X.B.fields.emb X.B.wts.sgTrue 1 x y)) → ∀ t, ∃ P : Bridge.ClassPres (Bridge.ratF X.toD7.sp.X') ((famR X I hX U Xg tr).A.MtildeCSD t) X.toD7.what₂.embLL cX.coef.ρ (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J (levEnv X.toD7.sp.X' L.βX (L.datXt t)).χ, (∀ x, P.coef x = c x) ∧ (∀ c', RowAd.decoAd X I t (P.y c') = (Formalism.L2.Col.mtildeKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1).outSec.rep c') ∧ ∀ (f : ((famR X I hX U Xg tr).A.MtildeCSD t).Forms) (h : Bridge.Gf X.toD7.sp.X'), P.ext (f : _ → _) h = c ((((Formalism.L2.Col.mtildeKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1).res (Formalism.L2.Col.mtildeKOk _ _ _ _ hX)).symm f).1 (RowAd.decoAd X I t h)) :=
  GlobalTheory.T.coefficient_map_level_character_equivariant

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowsClassSetPresentationCoefficientMapStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowsClassSet_presentation_coefficientMap : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → L.βX = 1 → ∀ (cX : CoefA X.toD7.sp.X') (c : VV X.B.fields.K X.B.wts.sgTrue →ₛₗ[X.B.embLL] cX.W), (∀ (γ : GQ X.toD7.sp.X') (γE : GL (Fin X.toD7.sp.X'.rank) X.toD7.host.E) (g : GL (Fin (X.B.R.N X.B.R.m - 1)) X.B.fields.E), Bridge.IsRatMat X.toD7.sp.X' γ γE → MatEq γE g → ∀ v, c (rhoV X.B.fields.emb X.B.wts.sgTrue g v) = cX.coef.ρ γ (c v)) → LinearIndependent ℂ (fun i => c (bVV X.B.fields.K X.B.wts.sgTrue i)) → Submodule.span ℂ (Set.range fun i => c (bVV X.B.fields.K X.B.wts.sgTrue i)) = ⊤ → (∀ x y, inner ℂ (c x) (c y) = X.B.embLL (pairV X.B.fields.emb X.B.wts.sgTrue 1 x y)) → ∀ t, ∃ P : Bridge.ClassPres (Bridge.ratF X.toD7.sp.X') ((famR X I hX U Xg tr).A.MtildeCSD t) X.toD7.what₂.embLL cX.coef.ρ (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J (levEnv X.toD7.sp.X' L.βX (L.datXt t)).χ, (∀ x, P.coef x = c x) ∧ (∀ c', RowAd.decoAd X I t (P.y c') = (Formalism.L2.Col.mtildeKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1).outSec.rep c') ∧ ∀ (f : ((famR X I hX U Xg tr).A.MtildeCSD t).Forms) (h : Bridge.Gf X.toD7.sp.X'), P.ext (f : _ → _) h = c ((((Formalism.L2.Col.mtildeKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1).res (Formalism.L2.Col.mtildeKOk _ _ _ _ hX)).symm f).1 (RowAd.decoAd X I t h)) := by
  first | exact @GlobalTheory.rowsClassPresLink | exact GlobalTheory.rowsClassPresLink | (intros; apply GlobalTheory.rowsClassPresLink <;> assumption)
end
