module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarSteps

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarCohPfB
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarCohPf
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarCohPfA
noncomputable section

open ValuativeRel Matrix

namespace Formalism.MainNotions.S.Loc.HermSp.CohU

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)

def hL (y : V) : V →ₗ[E] E where
  toFun x := H.h x y
  map_add' x x' := H.h_add_left x x' y
  map_smul' a x := by simpa using H.h_smul_left a x y

theorem hL_apply (x y : V) : hL H y x = H.h x y := rfl

def GramInv {ι : Type} [Fintype ι] [DecidableEq ι] (v : ι → V) : Prop :=
  ∃ N : Matrix ι ι E, (∀ i j, N i j ∈ M.L.O) ∧ N * H.gram v = 1

variable {H}

theorem h_right_zero {ι : Type} {v : ι → V} {w : V} (hw : ∀ i, H.h w (v i) = 0) {y : V}
    (hy : y ∈ Submodule.span E (Set.range v)) : H.h w y = 0 := by
  have hspan : Submodule.span E (Set.range v) ≤ LinearMap.ker (hL H w) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, hL_apply, H.h_herm, hw i, map_zero]
  have hy' : H.h y w = 0 := by
    have h1 := hspan hy
    rwa [LinearMap.mem_ker, hL_apply] at h1
  rw [H.h_herm, hy', map_zero]

private theorem h_fintype_sum_smul_left {ι : Type} [Fintype ι] (v : ι → V) (c : ι → E) (y : V) :
    H.h (∑ j, c j • v j) y = ∑ j, c j * H.h (v j) y := by
  have h1 := map_sum (hL H y) (fun j => c j • v j) Finset.univ
  simp only [map_smul, smul_eq_mul, hL_apply] at h1
  exact h1

private theorem h_sum_smul_eq_gram_mulVec {ι : Type} [Fintype ι] (v : ι → V) (c : ι → E) (i : ι) :
    H.h (∑ j, c j • v j) (v i) = (H.gram v *ᵥ c) i := by
  rw [h_fintype_sum_smul_left]
  show ∑ j, c j * H.h (v j) (v i) = ∑ j, H.h (v j) (v i) * c j
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem eq_zero_of_orth {ι : Type} [Fintype ι] [DecidableEq ι] {v : ι → V} (hN : GramInv H v) {z : V}
    (hz : z ∈ Submodule.span E (Set.range v)) (h0 : ∀ i, H.h z (v i) = 0) : z = 0 := by
  obtain ⟨N, -, hNG⟩ := hN
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (R := E)).1 hz
  have hc : H.gram v *ᵥ c = 0 := by
    funext i
    rw [← h_sum_smul_eq_gram_mulVec v c i]
    exact h0 i
  have hc0 : c = 0 := by
    rw [← Matrix.one_mulVec c, ← hNG, ← Matrix.mulVec_mulVec, hc, Matrix.mulVec_zero]
  subst hc0
  simp

private theorem h_sub_left' (x y z : V) : H.h (x - y) z = H.h x z - H.h y z := by
  have h1 := (hL H z).map_sub x y
  rw [hL_apply, hL_apply, hL_apply] at h1
  exact h1

theorem decomp {ι : Type} [Fintype ι] [DecidableEq ι] {v : ι → V} (hN : GramInv H v) {Λ : Submodule M.L.O V}
    (hI : ∀ x ∈ Λ, ∀ y ∈ Λ, H.h x y ∈ M.L.O) (hv : ∀ i, v i ∈ Λ) {x : V} (hx : x ∈ Λ) :
    ∃ c : ι → E, (∀ j, c j ∈ M.L.O) ∧ ∀ i, H.h (x - ∑ j, c j • v j) (v i) = 0 := by
  obtain ⟨N, hNO, hNG⟩ := hN
  have hGN : H.gram v * N = 1 := by
    first
      | exact mul_eq_one_comm.1 hNG
      | (rw [← Matrix.inv_eq_left_inv hNG]
         exact Matrix.mul_nonsing_inv _ (Matrix.isUnit_det_of_left_inverse hNG))
  refine ⟨N *ᵥ fun k => H.h x (v k), fun j => ?_, fun i => ?_⟩
  · show ∑ k, N j k * H.h x (v k) ∈ M.L.O
    exact sum_mem fun k _ => mul_mem (hNO j k) (hI x hx (v k) (hv k))
  · rw [h_sub_left', h_sum_smul_eq_gram_mulVec v _ i, Matrix.mulVec_mulVec, hGN, Matrix.one_mulVec]
    exact sub_self _

theorem comb_mem_span {ι : Type} [Fintype ι] (v : ι → V) (c : ι → E) :
    ∑ j, c j • v j ∈ Submodule.span E (Set.range v) :=
  Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem comb_mem_lat {ι : Type} [Fintype ι] {v : ι → V} {Λ : Submodule M.L.O V} (hv : ∀ i, v i ∈ Λ) {c : ι → E}
    (hc : ∀ j, c j ∈ M.L.O) : ∑ j, c j • v j ∈ Λ :=
  Submodule.sum_mem _ fun j _ => Λ.smul_mem (⟨c j, hc j⟩ : M.L.O) (hv j)

theorem le_of_Lset {r : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {v : ι → V} (hN : GramInv H v)
    {f : Fin (r + 1) → V} (hX : H.X f ≤ Submodule.span E (Set.range v)) {Λ₁ Λ₂ : Submodule M.L.O V}
    (hI1 : ∀ x ∈ Λ₁, ∀ y ∈ Λ₁, H.h x y ∈ M.L.O) (hI2 : ∀ x ∈ Λ₂, ∀ y ∈ Λ₂, H.h x y ∈ M.L.O)
    (hv1 : ∀ i, v i ∈ Λ₁) (hv2 : ∀ i, v i ∈ Λ₂) (hL : H.Lset Λ₁ f ⊆ H.Lset Λ₂ f) : Λ₁ ≤ Λ₂ := by
  intro x hx
  obtain ⟨c, hcO, hc⟩ := decomp hN hI1 hv1 hx
  have hs2 : ∑ j, c j • v j ∈ Λ₂ := comb_mem_lat hv2 hcO
  have hperp : x - ∑ j, c j • v j ∈ H.perp (H.X f) := by
    show ∀ z ∈ H.X f, H.h (x - ∑ j, c j • v j) z = 0
    intro z hz
    exact h_right_zero hc (hX hz)
  have hx0 : x - ∑ j, c j • v j ∈ Λ₁ := Λ₁.sub_mem hx (comb_mem_lat hv1 hcO)
  have hmem : H.mkW f ⟨x - ∑ j, c j • v j, hperp⟩ ∈ H.Lset Λ₁ f :=
    ⟨⟨x - ∑ j, c j • v j, hperp⟩, hx0, rfl⟩
  obtain ⟨y, hyΛ, hyeq⟩ := hL hmem
  obtain ⟨d, hdO, hd⟩ := decomp hN hI2 hv2 hyΛ
  have ht2 : ∑ j, d j • v j ∈ Λ₂ := comb_mem_lat hv2 hdO
  have hdiff : (y : V) - (x - ∑ j, c j • v j) ∈ H.X f := by
    have hk := LinearMap.sub_mem_ker_iff.2 hyeq
    rw [Formalism.MainNotions.S.Loc.HermSp.mkW, Submodule.ker_mkQ, Submodule.mem_comap] at hk
    simpa using hk
  have hzero : (x - ∑ j, c j • v j) - ((y : V) - ∑ j, d j • v j) = 0 := by
    apply eq_zero_of_orth hN
    · have h1 : (y : V) - (x - ∑ j, c j • v j) ∈ Submodule.span E (Set.range v) := hX hdiff
      have h2 : ∑ j, d j • v j ∈ Submodule.span E (Set.range v) := comb_mem_span v d
      have h3 : (x - ∑ j, c j • v j) - ((y : V) - ∑ j, d j • v j) =
          ∑ j, d j • v j - ((y : V) - (x - ∑ j, c j • v j)) := by abel
      rw [h3]
      exact Submodule.sub_mem _ h2 h1
    · intro i
      rw [h_sub_left', hc i, hd i, sub_zero]
  have hx0' : x - ∑ j, c j • v j ∈ Λ₂ := by
    rw [sub_eq_zero.1 hzero]
    exact Λ₂.sub_mem hyΛ ht2
  have h4 := Λ₂.add_mem hx0' hs2
  rwa [sub_add_cancel] at h4

theorem lat_eq_of_Lset {r : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {v : ι → V} (hN : GramInv H v)
    {f : Fin (r + 1) → V} (hX : H.X f ≤ Submodule.span E (Set.range v)) {Λ₁ Λ₂ : Submodule M.L.O V}
    (h1 : H.IsSelfDual Λ₁) (h2 : H.IsSelfDual Λ₂) (hv1 : ∀ i, v i ∈ Λ₁) (hv2 : ∀ i, v i ∈ Λ₂)
    (hL : H.Lset Λ₁ f = H.Lset Λ₂ f) : Λ₁ = Λ₂ := by
  have hI1 : ∀ x ∈ Λ₁, ∀ y ∈ Λ₁, H.h x y ∈ M.L.O := fun x hx => (h1.2.2 x).1 hx
  have hI2 : ∀ x ∈ Λ₂, ∀ y ∈ Λ₂, H.h x y ∈ M.L.O := fun x hx => (h2.2.2 x).1 hx
  exact le_antisymm (le_of_Lset hN hX hI1 hI2 hv1 hv2 hL.subset)
    (le_of_Lset hN hX hI2 hI1 hv2 hv1 hL.symm.subset)

theorem f_mem_MMfam {r : ℕ} (t : Term V M r) (a : Fin (r + 1)) : t.f a ∈ Set.range (H.MMfam t) := by
  refine ⟨Sum.inl a, ?_⟩
  unfold Formalism.MainNotions.S.Loc.HermSp.MMfam
  first
    | (generalize M.split = s
       cases s <;> rfl)
    | (rcases hs : M.split with _ | g <;> simp [hs])

theorem X_le_MMfam {r : ℕ} (t : Term V M r) : H.X t.f ≤ Submodule.span E (Set.range (H.MMfam t)) := by
  unfold Formalism.MainNotions.S.Loc.HermSp.X
  apply Submodule.span_mono
  rintro _ ⟨a, rfl⟩
  exact f_mem_MMfam (H := H) t a.castSucc

end Formalism.MainNotions.S.Loc.HermSp.CohU
end
end

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

namespace CohCut

def t2 (p : PlF D) (γ : TermDef.Term D u u' F0 what₂) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (Λ : Submodule (Zd.M p).L.O (Vp D p)) : Loc.Term (Vp D p) (Zd.M p) D.R.rS :=
  ⟨Λ, (tLoc Zd p γ).f, locF' Zd p F'₂, (tLoc Zd p γ).T, (tLoc Zd p γ).T'⟩

def vP (p : PlF D) (γ : TermDef.Term D u u' F0 what₂) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) :
    Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1) → Vp D p :=
  (locH Zd p).MMfam (t2 Zd p γ F'₂ ⊥)

end CohCut

open CohCut

def CohHyp (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D)
    (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)) : Prop :=
  Ctx γ Z ∧ ZhatL (lf D F0) F'₂ = Z ∧ starCompat γ F'₂ ∧
    ∀ p, LsDatumA.LocalCountHypotheses (locH Zd p) (tLoc Zd p γ) (tLoc Zd p γ).f (locF' Zd p F'₂) (LinearEquiv.refl _ _) (φ' p)

variable (u u' F0 what₂)

def CohGen : Prop :=
  CtxP u u' F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
    CohHyp Zd γ Z F'₂ φ' →
    {p | ¬ (locH Zd p).IsGeneric (t2 Zd p γ F'₂ (lattice₂ D Zd.M p γ.lam))}.Finite

def CohGood : Prop :=
  CtxP u u' F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
    CohHyp Zd γ Z F'₂ φ' →
    {p | ¬ Formalism.MainNotions.S.Loc.HermSp.CohU.GramInv (locH Zd p) (vP Zd p γ F'₂)}.Finite

variable {u u' F0 what₂}

theorem locSet_eq_single {p : PlF D} {γ : TermDef.Term D u u' F0 what₂}
    {F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)}
    {φ' : (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)}
    (hmem : lattice₂ D Zd.M p γ.lam ∈ locSet Zd p (tLoc Zd p γ) (locF' Zd p F'₂) (LinearEquiv.refl _ _) φ')
    (hN : Formalism.MainNotions.S.Loc.HermSp.CohU.GramInv (locH Zd p) (vP Zd p γ F'₂)) :
    locSet Zd p (tLoc Zd p γ) (locF' Zd p F'₂) (LinearEquiv.refl _ _) φ' = {lattice₂ D Zd.M p γ.lam} := by
  ext Λ₂
  rw [Set.mem_singleton_iff]
  constructor
  · intro h2
    have hL : (locH Zd p).Lset (lattice₂ D Zd.M p γ.lam) (tLoc Zd p γ).f = (locH Zd p).Lset Λ₂ (tLoc Zd p γ).f := by
      have h := h2.2.1
      exact (Set.image_id _).symm.trans h
    have hX := Formalism.MainNotions.S.Loc.HermSp.CohU.X_le_MMfam (H := locH Zd p) (t2 Zd p γ F'₂ ⊥)
    exact (Formalism.MainNotions.S.Loc.HermSp.CohU.lat_eq_of_Lset hN hX hmem.1.1.1 h2.1.1.1 hmem.1.2.1 h2.1.2.1 hL).symm
  · intro h
    rw [h]
    exact hmem

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open CohCut

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (u u' F0 what₂)

def CohLp : Prop :=
  CtxP u u' F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
    CohHyp Zd γ Z F'₂ φ' →
    {p | ⇑(φ' p) '' (locH Zd p).Lset (lattice₂ D Zd.M p γ.lam) (tLoc Zd p γ).f' ≠
      (locH Zd p).Lset (lattice₂ D Zd.M p γ.lam) (locF' Zd p F'₂)}.Finite

def CohIota : Prop :=
  CtxP u u' F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
    CohHyp Zd γ Z F'₂ φ' →
    {p | ¬ ∀ g, (Zd.M p).split = some g →
      Prod.map ⇑(φ' p) ⇑(LinearEquiv.refl (D.s.atP p).Ep ((locH Zd p).Wb (tLoc Zd p γ).f)) ''
          (locH Zd p).iotaGraph g (tLoc Zd p γ) =
        (locH Zd p).iotaGraph g (t2 Zd p γ F'₂ (lattice₂ D Zd.M p γ.lam))}.Finite

variable {u u' F0 what₂}

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open CohCut

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem split_finite : {p : PlF D | (Zd.M p).split.isSome}.Finite := by
  have hfinite (ℓ : ℕ) : {p : PlF D | Loc.resChar p = ℓ}.Finite := by
    have hsub : {p : PlF D | Loc.resChar p = ℓ} ⊆
        {v | v.asIdeal ∣ Ideal.span {(ℓ : 𝓞 D.host.F)}} := by
      intro p hp
      simp only [Set.mem_ofPred_eq] at hp ⊢
      rw [Ideal.dvd_span_singleton, ← hp, ← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
      exact ringChar.Nat.cast_ringChar
    by_cases hℓ : ℓ = 0
    · subst hℓ
      convert Set.finite_empty
      rename_i p
      change Loc.resChar p = 0 ↔ False
      simp only [iff_false]
      intro hp
      have h1 : ((Ideal.absNorm p.asIdeal : ℕ) : 𝓞 D.host.F ⧸ p.asIdeal) = 0 := by
        rw [← map_natCast (Ideal.Quotient.mk p.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.absNorm_mem p.asIdeal
      have hc : CharP (𝓞 D.host.F ⧸ p.asIdeal) 0 := by
        have h2 := ringChar.charP (𝓞 D.host.F ⧸ p.asIdeal)
        unfold Loc.resChar at hp
        rwa [hp] at h2
      rw [CharP.cast_eq_zero_iff _ 0, zero_dvd_iff, Ideal.absNorm_eq_zero_iff] at h1
      exact p.ne_bot h1
    · refine (Ideal.finite_factors ?_).subset hsub
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast hℓ
  refine ((hfinite (D.host.g 0)).union (hfinite (D.host.g 1))).subset ?_
  intro p hp
  simp only [Set.mem_ofPred_eq] at hp
  have hs : (D.s.atP p).split.isSome := by
    obtain ⟨g, hg⟩ := Option.isSome_iff_exists.1 hp
    have hA := (Zd.agree p).2.2.2.2.2
    rw [hg] at hA
    cases h2 : (D.s.atP p).split with
    | none =>
      rw [h2] at hA
      exact (hA : False).elim
    | some sg => rfl
  have hin : Loc.resChar p ∈ ({D.host.g 0, D.host.g 1} : Finset ℕ) := (D.s_split p).1 hs
  simp only [Finset.mem_insert, Finset.mem_singleton] at hin
  simp only [Set.mem_union, Set.mem_ofPred_eq]
  exact hin

theorem cohIota_holds : CohIota Zd u u' F0 what₂ := by
  intro _ γ Z F'₂ φ' _
  refine (split_finite Zd).subset ?_
  intro p hp
  simp only [Set.mem_ofPred_eq]
  by_contra hn
  apply hp
  intro g hg
  rw [hg] at hn
  exact (hn rfl).elim

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
