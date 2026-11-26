module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataChoiceLeaves

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ZsVolFS
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CongAt
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ZsVolCong
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.OneMemDdPow
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FrameEntry
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ZsVolLat
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ZsVolIn
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ZsVolShape
noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolShape

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal
  Formalism.L2.SG.Pf.ZsVolCut Formalism.L2.SG.Pf.ZsVolGrp Matrix
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)

theorem mem_stZSet_iff (hA : ∀ p, Agree δ M p) (Z L : MatR D) (a : GLR D) :
    a ∈ stZSet M δ u u' Z L ↔ ∃ a' : GLR D, (a : MatR D) = L⁻¹ * (a' : MatR D) * L ∧ IsLoUni (a' : MatR D) ∧
      ∃ b : MatR D, IsUpUni b ∧ (a' : MatR D) * ZhatOM Z * b = ZhatOM Z ∧
        Formalism.L2.SG.Pf.StabIntSh.EntryShape D (a' : MatR D) b := by
  have hL := Formalism.L2.SG.Pf.StabIntSh.locShapeL (D := D)
  have hG := Formalism.L2.SG.Pf.StabIntSh.locShapeG (D := D)
  have hLG := Formalism.L2.SG.Pf.StabIntSh.locGlob (D := D)
  have hNZ := Formalism.L2.SG.Pf.StabIntSh.shapeNZ (D := D)
  constructor
  · rintro ⟨a', ha, hlo, b, hb, hZ, hp⟩
    refine ⟨a', ha, hlo, b, hb, hZ, (Formalism.L2.SG.Pf.StabIntSh.glob_iff hLG hNZ _ _).1 fun p => ?_⟩
    obtain ⟨l, ρ, hl, hρ, hm⟩ := hp p
    obtain ⟨e1, e2⟩ := Formalism.L2.SG.Pf.StabShape.uniq δ M u u' (hA p) _ _ hlo hb l ρ hl.1 hρ.1 hm
    rw [e1] at hl
    rw [e2] at hρ
    exact (Formalism.L2.SG.Pf.StabIntSh.loc_iff hL hG (p := p) hA hlo hb).1 ⟨hl, hρ⟩
  · rintro ⟨a', ha, hlo, b, hb, hZ, he⟩
    refine ⟨a', ha, hlo, b, hb, hZ, fun p => ?_⟩
    have h := (Formalism.L2.SG.Pf.StabIntSh.loc_iff hL hG (p := p) hA hlo hb).2
      ((Formalism.L2.SG.Pf.StabIntSh.glob_iff hLG hNZ _ _).2 he p)
    exact ⟨_, _, h.1, h.2, Formalism.L2.SG.Pf.StabShape.move δ M u u' (hA p) _ _ hlo hb⟩

end Formalism.L2.SG.Pf.ZsVolShape

end
end

noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolIn

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal
  Formalism.L2.SG.Pf.ZsVolCut Formalism.L2.SG.Pf.ZsVolGrp Formalism.L2.SG.Pf.ZsVolShape Matrix
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)
  (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def FrameShapeP : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (L U : MatR D), HypE M δ u u' F0 what₂ γ w F' L U →
    ∀ s ∈ NLam γ.lam (lf D F0) ∩ NLam γ.lam F', ∀ uu uu' : MatR D, IsUpUni uu → IsUpUni uu' →
      (∀ b, s (F0.fvec b) = ∑ c, uu c b • F0.fvec c) → (∀ b, s (F'.fl.fvec b) = ∑ c, uu' c b • F'.fl.fvec c) →
        Formalism.L2.SG.Pf.StabIntSh.EntryShape D uu.conjTranspose
          (Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS * uu' * Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS)

theorem stabInCZ_of (hF : FrameShapeP M δ u u' F0 what₂) : Formalism.L2.SG.Pf.ZsVolOrb.StabInCZ M δ u u' F0 what₂ := by
  intro γ w F' L U hH
  obtain ⟨hA, hT, hR, hP, hE, hN⟩ := hH
  obtain ⟨_, _, hL, hU, hZ⟩ := hN
  have hT0 : ((Tu D u : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast hP.1.pos.ne'
  have hLd : IsUnit L.det := by rw [Formalism.L2.SG.Pf.StabilizerIndexVolumes.lo_det hL]; exact isUnit_one
  refine (Subgroup.closure_le _).2 ?_
  rintro a ⟨s, ⟨hsF, hsF'⟩, uu, huu, ha⟩
  have hsF0 := hsF
  have hsF'0 := hsF'
  obtain ⟨⟨hiso, _⟩, hf1, hf2⟩ := hsF
  obtain ⟨⟨_, _⟩, hg1, hg2⟩ := hsF'
  obtain ⟨uu0, huu0, hu0⟩ := Formalism.L2.SG.Pf.StabilizerIndexVolumes.tri_exists F0 s hf1 hf2
  obtain ⟨uu', huu', hu'⟩ := Formalism.L2.SG.Pf.StabilizerIndexVolumes.tri_exists F'.fl s hg1 hg2
  have heq : uu = uu0 :=
    Formalism.L2.SG.Pf.StabilizerIndexVolumes.coef_unique (Formalism.L2.SG.Pf.StabilizerIndexVolumes.frame_indep F0 hT0) (fun b => s (F0.fvec b)) uu uu0 huu hu0
  subst heq
  have hZc := Formalism.L2.SG.Pf.StabilizerIndexVolumes.zhat_conj F0 F'.fl s hiso uu uu' hu0 hu'
  have hdet : IsUnit uu.conjTranspose.det := by
    rw [Formalism.L2.SG.Pf.StabilizerIndexVolumes.lo_det (Formalism.L2.SG.Pf.StabilizerIndexVolumes.lo_conjT huu0)]; exact isUnit_one
  let a' : GLR D := Matrix.nonsingInvUnit uu.conjTranspose hdet
  have ha' : (a' : MatR D) = uu.conjTranspose := rfl
  have hshape := hF γ w F' L U ⟨hA, hT, hR, hP, hE, ⟨‹_›, ‹_›, hL, hU, hZ⟩⟩ s ⟨hsF0, hsF'0⟩ uu uu' huu0 huu' hu0 hu'
  have hmem : a ∈ stZSet M δ u u' (ZhatL (lf D F0) F') L := by
    refine (mem_stZSet_iff M δ u u' hA _ L a).2 ⟨a', by rw [ha', ha], by rw [ha']; exact Formalism.L2.SG.Pf.StabilizerIndexVolumes.lo_conjT huu0,
      Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS * uu' * Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS, Formalism.L2.SG.Pf.StabilizerIndexVolumes.up_sgn huu', ?_, by rw [ha']; exact hshape⟩
    rw [ha', Formalism.L2.SG.Pf.StabilizerIndexVolumes.zhatOM_eq]
    show uu.conjTranspose * (Zhat F0 F'.fl * Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS) *
      (Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS * uu' * Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS) = Zhat F0 F'.fl * Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS
    rw [show uu.conjTranspose * (Zhat F0 F'.fl * Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS) *
        (Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS * uu' * Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS) =
      uu.conjTranspose * Zhat F0 F'.fl * (Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS * Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS) * uu' *
        Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS by simp only [Matrix.mul_assoc],
      Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM_sq, Matrix.mul_one, ← hZc]
  exact (mem_CZ M δ u u' _ L hLd a).2 hmem

end Formalism.L2.SG.Pf.ZsVolIn

end
end

noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolLat

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

theorem mem_of_mul (I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) (hI : I ≠ 0) (m n : ℤ) (y : D.host.E)
    (h : ∀ x ∈ I ^ n, x * y ∈ I ^ m) : y ∈ I ^ (m - n) := by
  have hle : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) y * I ^ n ≤ I ^ m := by
    refine FractionalIdeal.mul_le.2 fun a ha b hb => ?_
    obtain ⟨c, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 ha
    rw [smul_mul_assoc, mul_comm]
    exact (FractionalIdeal.mem_coe).1 (Submodule.smul_mem _ c ((FractionalIdeal.mem_coe).2 (h b hb)))
  have h2 : I ^ (-n) * (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) y * I ^ n) ≤ I ^ (-n) * I ^ m :=
    mul_right_mono hle
  rw [mul_comm (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) y), ← mul_assoc, ← zpow_add₀ hI,
    neg_add_cancel, zpow_zero, one_mul, ← zpow_add₀ hI, neg_add_eq_sub] at h2
  exact h2 (FractionalIdeal.mem_spanSingleton_self _ y)

theorem coef_XS {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) {v : (VS D).V} (hv : v ∈ XS D F0)
    (y : Fin D.R.rS → D.host.E) (hy : v = ∑ a, y a • F0.e a) (a : Fin D.R.rS) :
    y a ∈ (ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ))) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
  have key : ∃ y' : Fin D.R.rS → D.host.E, (∀ a : Fin D.R.rS, y' a ∈ (ddS D ^ (-((D.R.rS : ℤ) - ((a : Fin D.R.rS) : ℕ))) :
      FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) ∧ v = ∑ a, y' a • F0.e a := by
    clear hy
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, x, hx, rfl⟩ := hx
      refine ⟨Pi.single a x, fun b => ?_, ?_⟩
      · by_cases h : b = a
        · subst h
          simpa using hx
        · rw [Pi.single_eq_of_ne h]
          exact FractionalIdeal.zero_mem _
      · rw [Finset.sum_eq_single a (fun b _ hb => by rw [Pi.single_eq_of_ne hb, zero_smul]) (by simp),
          Pi.single_eq_same]
    | zero => exact ⟨0, fun _ => FractionalIdeal.zero_mem _, by simp⟩
    | add x w _ _ hx hw =>
      obtain ⟨y1, h1, rfl⟩ := hx
      obtain ⟨y2, h2, rfl⟩ := hw
      exact ⟨y1 + y2, fun a => (FractionalIdeal.mem_coe).1 (Submodule.add_mem _ ((FractionalIdeal.mem_coe).2 (h1 a))
        ((FractionalIdeal.mem_coe).2 (h2 a))), by simp [add_smul, Finset.sum_add_distrib]⟩
    | smul c x _ hx =>
      obtain ⟨y1, h1, rfl⟩ := hx
      refine ⟨fun a => (c : D.host.E) * y1 a, fun a => ?_, ?_⟩
      · have := (FractionalIdeal.mem_coe).1 (Submodule.smul_mem _ c ((FractionalIdeal.mem_coe).2 (h1 a)))
        rwa [Algebra.smul_def] at this
      · rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← smul_assoc, Algebra.smul_def]
  obtain ⟨y', hy', hv'⟩ := key
  have hyy : y = y' := by
    have h := F0.e_indep
    rw [Fintype.linearIndependent_iff] at h
    funext b
    have := h (y - y') (by simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, ← hy, ← hv', sub_self]) b
    exact sub_eq_zero.1 this
  rw [hyy]
  exact hy' a

end Formalism.L2.SG.Pf.ZsVolLat

end
end

noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolLat

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

theorem sum_fvec {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (w : Fin (D.R.rS + 1) → D.host.E) :
    ∑ c, w c • F0.fvec c = ∑ a : Fin D.R.rS, w (Fin.castSucc a) • F0.e a + w (Fin.last _) • F0.z := by
  rw [Fin.sum_univ_castSucc]
  simp [FlagG.fvec, Fin.snoc_castSucc, Fin.snoc_last]

theorem frame_entry {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hX : XLam Λ F = XS D F.fl) (hz : F.fl.z ∈ Λ) (s : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hs : ∀ v ∈ Λ, s v ∈ Λ)
    (uu : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) (huu : IsUpUni uu)
    (hfr : ∀ b, s (F.fl.fvec b) = ∑ c, uu c b • F.fl.fvec c) (c b : Fin (D.R.rS + 1)) (hcb : c < b) :
    uu c b ∈ ddS D ^ (-((((b : ℕ) - (c : ℕ) : ℕ)) : ℤ)) := by
  have hne := Formalism.L2.SG.Pf.StabIntSh.lg_ddS_ne (D := D)
  have hXS_le : XS D F.fl ≤ Λ := by rw [← hX]; exact inf_le_left
  have hXmem : ∀ y : Fin D.R.rS → D.host.E, (∑ a, y a • F.fl.e a) ∈ Λ → (∑ a, y a • F.fl.e a) ∈ XS D F.fl := by
    intro y hy
    rw [← hX]
    refine Submodule.mem_inf.2 ⟨hy, ?_⟩
    show (∑ a, y a • F.fl.e a) ∈ F.fl.X
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  have hc : (c : ℕ) < D.R.rS := lt_of_lt_of_le hcb (Nat.lt_succ_iff.1 b.2)
  obtain ⟨a, rfl⟩ : ∃ a : Fin D.R.rS, c = Fin.castSucc a := ⟨⟨c, hc⟩, rfl⟩
  induction b using Fin.lastCases with
  | last =>
    have hv : s F.fl.z - F.fl.z = ∑ a', uu (Fin.castSucc a') (Fin.last _) • F.fl.e a' := by
      have h := hfr (Fin.last _)
      rw [sum_fvec] at h
      simp only [FlagG.fvec, Fin.snoc_last] at h
      rw [h, (huu _ _).2 rfl, one_smul, add_sub_cancel_right]
    have hmem : s F.fl.z - F.fl.z ∈ XS D F.fl := by
      rw [hv]
      apply hXmem
      rw [← hv]
      exact Λ.sub_mem (hs _ hz) hz
    have h := coef_XS F.fl hmem _ hv a
    have e : (-((((Fin.last D.R.rS : Fin (D.R.rS + 1)) : ℕ) - ((Fin.castSucc a : Fin (D.R.rS + 1)) : ℕ) : ℕ)) : ℤ) =
        -((D.R.rS : ℤ) - ((a : ℕ) : ℤ)) := by
      simp only [Fin.val_last, Fin.val_castSucc]
      rw [Nat.cast_sub a.2.le]
    rw [e]
    exact h
  | cast b' =>
    have hab : (a : ℕ) < b' := hcb
    have key : ∀ x ∈ ddS D ^ (-((D.R.rS : ℤ) - ((b' : ℕ) : ℤ))),
        x * uu (Fin.castSucc a) (Fin.castSucc b') ∈ ddS D ^ (-((D.R.rS : ℤ) - ((a : ℕ) : ℤ))) := by
      intro x hx
      have hgen : x • F.fl.e b' ∈ XS D F.fl := Submodule.subset_span ⟨b', x, hx, rfl⟩
      have hv : s (x • F.fl.e b') = ∑ a', (x * uu (Fin.castSucc a') (Fin.castSucc b')) • F.fl.e a' := by
        have h := hfr (Fin.castSucc b')
        rw [sum_fvec] at h
        simp only [FlagG.fvec, Fin.snoc_castSucc] at h
        rw [LinearEquiv.map_smul, h, (huu _ _).1 (Fin.castSucc_lt_last b'), zero_smul, add_zero, Finset.smul_sum]
        refine Finset.sum_congr rfl fun a' _ => ?_
        rw [smul_smul]
      have hmem : s (x • F.fl.e b') ∈ XS D F.fl := by
        rw [hv]
        apply hXmem
        rw [← hv]
        exact hs _ (hXS_le hgen)
      exact coef_XS F.fl hmem _ hv a
    have h := mem_of_mul (ddS D) hne _ _ _ key
    have e : (-((((Fin.castSucc b' : Fin (D.R.rS + 1)) : ℕ) - ((Fin.castSucc a : Fin (D.R.rS + 1)) : ℕ) : ℕ)) : ℤ) =
        -((D.R.rS : ℤ) - ((a : ℕ) : ℤ)) - -((D.R.rS : ℤ) - ((b' : ℕ) : ℤ)) := by
      simp only [Fin.val_castSucc]
      rw [Nat.cast_sub hab.le]
      ring
    rw [e]
    exact h

end Formalism.L2.SG.Pf.ZsVolLat

end
end

noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolLat

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix IsDedekindDomain
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

theorem mem_of_loc (I : Submodule (𝓞 D.host.E) D.host.E) (x : D.host.E)
    (h : ∀ P : HeightOneSpectrum (𝓞 D.host.E), ∃ t : 𝓞 D.host.E, t ∉ P.asIdeal ∧ (t : D.host.E) * x ∈ I) : x ∈ I := by
  let J : Ideal (𝓞 D.host.E) :=
    { carrier := {t | (t : D.host.E) * x ∈ I}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq] at *
        push_cast
        rw [add_mul]
        exact I.add_mem ha hb
      zero_mem' := by
        simp only [Set.mem_ofPred_eq]
        push_cast
        rw [zero_mul]
        exact I.zero_mem
      smul_mem' := fun c a ha => by
        simp only [Set.mem_ofPred_eq] at *
        have e : (((c • a : 𝓞 D.host.E)) : D.host.E) * x = c • ((a : D.host.E) * x) := by
          rw [smul_eq_mul, Algebra.smul_def]
          push_cast
          ring
        rw [e]
        exact I.smul_mem c ha }
  by_contra hx
  have hJ : J ≠ ⊤ := by
    intro h1
    have h2 : (1 : 𝓞 D.host.E) ∈ J := h1 ▸ Submodule.mem_top
    apply hx
    have h3 : ((1 : 𝓞 D.host.E) : D.host.E) * x ∈ I := h2
    simpa using h3
  obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal J hJ
  have hM0 : M ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField D.host.E)
  obtain ⟨t, htP, ht⟩ := h ⟨M, hM.isPrime, hM0⟩
  exact htP (hJM ht)

theorem one_mem_ddPow (k : ℕ) : (1 : D.host.E) ∈ ddS D ^ (-(k : ℤ)) := by
  have hne := Formalism.L2.SG.Pf.StabIntSh.lg_ddS_ne (D := D)
  have h1 : ddS D ^ k ≤ 1 := pow_le_one' FractionalIdeal.coeIdeal_le_one k
  have h2 : (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)⁻¹ ≤ (ddS D ^ k)⁻¹ :=
    FractionalIdeal.inv_anti_mono (pow_ne_zero k hne) h1
  rw [inv_one] at h2
  rw [_root_.zpow_neg, zpow_natCast]
  exact h2 (FractionalIdeal.mem_one_iff _ |>.2 ⟨1, map_one _⟩)

theorem coef_spanO {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) {v : (VS D).V}
    (hv : v ∈ Submodule.span (𝓞 D.host.E) (Set.range F0.e))
    (y : Fin D.R.rS → D.host.E) (hy : v = ∑ a, y a • F0.e a) (a : Fin D.R.rS) :
    ∃ o : 𝓞 D.host.E, (o : D.host.E) = y a := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hv
  have hyy : y = fun b => (c b : D.host.E) := by
    have h := F0.e_indep
    rw [Fintype.linearIndependent_iff] at h
    funext b
    have := h (fun b => y b - (c b : D.host.E)) (by
      simp only [sub_smul, Finset.sum_sub_distrib, ← hy]
      rw [← hc]
      simp only [sub_eq_zero]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [algebraMap_smul]) b
    exact sub_eq_zero.1 this
  exact ⟨c a, by rw [hyy]⟩

end Formalism.L2.SG.Pf.ZsVolLat

end
end

noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolLat

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix IsDedekindDomain
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

theorem mem_locP {W : Type*} [AddCommGroup W] [Module (𝓞 D.host.E) W] (p : Ideal (𝓞 D.host.E)) [p.IsPrime]
    (L : Submodule (𝓞 D.host.E) W) (x : W) :
    x ∈ Formalism.HermitianLatticesTheory.localization₂ p L ↔ ∃ t : 𝓞 D.host.E, t ∉ p ∧ t • x ∈ L := Iff.rfl

theorem smul_O (s : (VS D).V ≃ₗ[D.host.E] (VS D).V) (t : 𝓞 D.host.E) (x : (VS D).V) : s (t • x) = t • s x := by
  rw [← algebraMap_smul D.host.E t x, LinearEquiv.map_smul, algebraMap_smul]

theorem conv_at {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hc : IsFixedConv Λ (Lat.gS D) F) (P : HeightOneSpectrum (𝓞 D.host.E)) (hgP : ((Lat.gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) :
    Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ F) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Submodule.span (𝓞 D.host.E) (Set.range F.fl.e)) := by
  obtain ⟨c, -, hc1, heq⟩ := hc.1 P
  rw [heq]
  congr 2
  ext v
  simp [hc1 hgP]

theorem int_at {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hc : IsFixedConv Λ (Lat.gS D) F) (hz : F.fl.z ∈ Λ) (s : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hs : ∀ v ∈ Λ, s v ∈ Λ)
    (uu : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) (huu : IsUpUni uu)
    (hfr : ∀ b, s (F.fl.fvec b) = ∑ c, uu c b • F.fl.fvec c) (P : HeightOneSpectrum (𝓞 D.host.E))
    (hgP : ((Lat.gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) (c i : Fin (D.R.rS + 1)) :
    ∃ t : 𝓞 D.host.E, t ∉ P.asIdeal ∧ ∃ o : 𝓞 D.host.E, (t : D.host.E) * uu c i = o := by
  have hP := P.isPrime
  have hconv := conv_at F Λ hc P hgP
  rcases lt_trichotomy c i with hci | hci | hci
  · have hcr : (c : ℕ) < D.R.rS := lt_of_lt_of_le hci (Nat.lt_succ_iff.1 i.2)
    obtain ⟨a, rfl⟩ : ∃ a : Fin D.R.rS, c = Fin.castSucc a := ⟨⟨c, hcr⟩, rfl⟩
    have hXmem : ∀ y : Fin D.R.rS → D.host.E, (∑ a, y a • F.fl.e a) ∈ Λ → (∑ a, y a • F.fl.e a) ∈ XLam Λ F := by
      intro y hy
      refine Submodule.mem_inf.2 ⟨hy, ?_⟩
      show (∑ a, y a • F.fl.e a) ∈ F.fl.X
      exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
    induction i using Fin.lastCases with
    | last =>
      have hv : s F.fl.z - F.fl.z = ∑ a', uu (Fin.castSucc a') (Fin.last _) • F.fl.e a' := by
        have h := hfr (Fin.last _)
        rw [sum_fvec] at h
        simp only [FlagG.fvec, Fin.snoc_last] at h
        rw [h, (huu _ _).2 rfl, one_smul, add_sub_cancel_right]
      have hmem : s F.fl.z - F.fl.z ∈ XLam Λ F := by
        rw [hv]
        apply hXmem
        rw [← hv]
        exact Λ.sub_mem (hs _ hz) hz
      have hloc : s F.fl.z - F.fl.z ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Submodule.span (𝓞 D.host.E) (Set.range F.fl.e)) := by
        rw [← hconv]
        exact ⟨1, P.asIdeal.primeCompl.one_mem, by rw [one_smul]; exact hmem⟩
      obtain ⟨t, ht, htv⟩ := (mem_locP P.asIdeal _ _).1 hloc
      have hv2 : t • (s F.fl.z - F.fl.z) = ∑ a', ((t : D.host.E) * uu (Fin.castSucc a') (Fin.last _)) • F.fl.e a' := by
        rw [hv, Finset.smul_sum]
        refine Finset.sum_congr rfl fun a' _ => ?_
        rw [← algebraMap_smul D.host.E t, smul_smul]
      obtain ⟨o, ho⟩ := coef_spanO F.fl htv _ hv2 a
      exact ⟨t, ht, o, ho.symm⟩
    | cast i' =>
      have he : F.fl.e i' ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ F) := by
        rw [hconv]
        exact ⟨1, P.asIdeal.primeCompl.one_mem, by rw [one_smul]; exact Submodule.subset_span ⟨i', rfl⟩⟩
      obtain ⟨t1, ht1, ht1e⟩ := (mem_locP P.asIdeal _ _).1 he
      have hv : s (t1 • F.fl.e i') = ∑ a', ((t1 : D.host.E) * uu (Fin.castSucc a') (Fin.castSucc i')) • F.fl.e a' := by
        have h := hfr (Fin.castSucc i')
        rw [sum_fvec] at h
        simp only [FlagG.fvec, Fin.snoc_castSucc] at h
        rw [smul_O, h, (huu _ _).1 (Fin.castSucc_lt_last i'), zero_smul, add_zero, Finset.smul_sum]
        refine Finset.sum_congr rfl fun a' _ => ?_
        rw [← algebraMap_smul D.host.E t1, smul_smul]
      have hmem : s (t1 • F.fl.e i') ∈ XLam Λ F := by
        rw [hv]
        apply hXmem
        rw [← hv]
        exact hs _ (Submodule.mem_inf.1 ht1e).1
      have hloc : s (t1 • F.fl.e i') ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Submodule.span (𝓞 D.host.E) (Set.range F.fl.e)) := by
        rw [← hconv]
        exact ⟨1, P.asIdeal.primeCompl.one_mem, by rw [one_smul]; exact hmem⟩
      obtain ⟨t2, ht2, ht2v⟩ := (mem_locP P.asIdeal _ _).1 hloc
      have hv2 : t2 • s (t1 • F.fl.e i') =
          ∑ a', ((t2 : D.host.E) * ((t1 : D.host.E) * uu (Fin.castSucc a') (Fin.castSucc i'))) • F.fl.e a' := by
        rw [hv, Finset.smul_sum]
        refine Finset.sum_congr rfl fun a' _ => ?_
        rw [← algebraMap_smul D.host.E t2, smul_smul]
      obtain ⟨o, ho⟩ := coef_spanO F.fl ht2v _ hv2 a
      refine ⟨t2 * t1, fun h => (hP.mem_or_mem h).elim ht2 ht1, o, ?_⟩
      rw [ho]
      push_cast
      ring
  · subst hci
    exact ⟨1, P.asIdeal.primeCompl.one_mem, 1, by rw [(huu c c).2 rfl]; simp⟩
  · exact ⟨1, P.asIdeal.primeCompl.one_mem, 0, by rw [(huu c i).1 hci]; simp⟩

end Formalism.L2.SG.Pf.ZsVolLat

end
end

noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolLat

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix IsDedekindDomain
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

theorem cong_at {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T')
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hc : IsFixedConv Λ (Lat.gS D) F) (hc' : IsFixedConv Λ (Lat.gS D) F')
    (hz' : F'.fl.z ∈ Λ) (hadm : ∀ b, ModG (VS D) Λ (Lat.gS D) (F'.fl.fvec b - F.fl.fvec b))
    (s : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hs : ∀ v ∈ Λ, s v ∈ Λ)
    (uu uu' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) (huu : IsUpUni uu) (huu' : IsUpUni uu')
    (hfr : ∀ b, s (F.fl.fvec b) = ∑ c, uu c b • F.fl.fvec c) (hfr' : ∀ b, s (F'.fl.fvec b) = ∑ c, uu' c b • F'.fl.fvec c)
    (P : HeightOneSpectrum (𝓞 D.host.E)) (hgP : ((Lat.gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal)
    (j i : Fin (D.R.rS + 1)) (hji : j < i) :
    ∃ t : 𝓞 D.host.E, t ∉ P.asIdeal ∧ ∃ o : 𝓞 D.host.E,
      (t : D.host.E) * (uu j i - uu' j i) = ((Lat.gS D : ℕ) : D.host.E) * o := by
  have hP := P.isPrime
  set g : 𝓞 D.host.E := ((Lat.gS D : ℕ) : 𝓞 D.host.E) with hg
  set M := Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {g} • Λ) with hM
  have hg0 : ((Lat.gS D : ℕ) : D.host.E) ≠ 0 := by
    have h2 : (Lat.gS D : ℕ) ≠ 0 := by
      unfold Lat.gS
      exact mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
    exact_mod_cast h2

  have hgs : ∀ x : (VS D).V, x ∈ Ideal.span {g} • Λ ↔ ∃ l ∈ Λ, g • l = x := by
    intro x
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  have hd : ∀ c, F'.fl.fvec c - F.fl.fvec c ∈ M := fun c => hadm c P hgP
  have hsd : s (F'.fl.fvec i - F.fl.fvec i) ∈ M := by
    obtain ⟨t, ht, htd⟩ := (mem_locP P.asIdeal _ _).1 (hd i)
    obtain ⟨l, hl, hlg⟩ := (hgs _).1 htd
    refine (mem_locP P.asIdeal _ _).2 ⟨t, ht, ?_⟩
    rw [← smul_O, ← hlg, smul_O]
    exact (hgs _).2 ⟨s l, hs l hl, rfl⟩
  have hud : ∀ c, uu' c i • (F'.fl.fvec c - F.fl.fvec c) ∈ M := by
    intro c
    obtain ⟨t1, ht1, o, ho⟩ := int_at F' Λ hc' hz' s hs uu' huu' hfr' P hgP c i
    obtain ⟨t2, ht2, htd⟩ := (mem_locP P.asIdeal _ _).1 (hd c)
    obtain ⟨l, hl, hlg⟩ := (hgs _).1 htd
    refine (mem_locP P.asIdeal _ _).2 ⟨t1 * t2, fun h => (hP.mem_or_mem h).elim ht1 ht2, ?_⟩
    have e : (t1 * t2) • (uu' c i • (F'.fl.fvec c - F.fl.fvec c)) = o • (t2 • (F'.fl.fvec c - F.fl.fvec c)) := by
      rw [← algebraMap_smul D.host.E (t1 * t2), ← algebraMap_smul D.host.E o, ← algebraMap_smul D.host.E t2, smul_smul,
        smul_smul]
      have ho' : algebraMap (𝓞 D.host.E) D.host.E t1 * uu' c i = algebraMap (𝓞 D.host.E) D.host.E o := ho
      rw [map_mul, mul_right_comm, ho']
    rw [e, ← hlg]
    exact (hgs _).2 ⟨o • l, Λ.smul_mem o hl, smul_comm g o l⟩

  set y : Fin D.R.rS → D.host.E := fun a => uu' (Fin.castSucc a) i - uu (Fin.castSucc a) i with hy
  have hlast : uu' (Fin.last _) i - uu (Fin.last _) i = 0 := by
    by_cases h : i = Fin.last _
    · subst h
      rw [(huu' _ _).2 rfl, (huu _ _).2 rfl, sub_self]
    · have hlt : i < Fin.last _ := lt_of_le_of_ne (Fin.le_last i) h
      rw [(huu' _ _).1 hlt, (huu _ _).1 hlt, sub_self]
  have hw : ∑ a, y a • F.fl.e a = s (F'.fl.fvec i - F.fl.fvec i) - ∑ c, uu' c i • (F'.fl.fvec c - F.fl.fvec c) := by
    rw [map_sub, hfr i, hfr' i]
    simp only [smul_sub, Finset.sum_sub_distrib]
    have h2 : ∑ c, (uu' c i - uu c i) • F.fl.fvec c = ∑ a, y a • F.fl.e a := by
      rw [sum_fvec]
      simp only [hy, hlast, zero_smul, add_zero]
    rw [← h2]
    simp only [sub_smul, Finset.sum_sub_distrib]
    abel
  have hwM : ∑ a, y a • F.fl.e a ∈ M := by
    rw [hw]
    exact M.sub_mem hsd (M.sum_mem fun c _ => hud c)
  obtain ⟨t, ht, htw⟩ := (mem_locP P.asIdeal _ _).1 hwM
  obtain ⟨l, hl, hlg⟩ := (hgs _).1 htw

  have hl_eq : l = ∑ a, (((Lat.gS D : ℕ) : D.host.E)⁻¹ * ((t : D.host.E) * y a)) • F.fl.e a := by
    have h1 : ((Lat.gS D : ℕ) : D.host.E) • l = t • ∑ a, y a • F.fl.e a := by
      rw [← hlg, ← algebraMap_smul D.host.E g]
      rfl
    have h2 := congrArg (fun v => ((Lat.gS D : ℕ) : D.host.E)⁻¹ • v) h1
    simp only [smul_smul, inv_mul_cancel₀ hg0, one_smul] at h2
    rw [h2, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← algebraMap_smul D.host.E t, smul_smul, smul_smul, mul_assoc]
  have hlX : l ∈ XLam Λ F := by
    refine Submodule.mem_inf.2 ⟨hl, ?_⟩
    show l ∈ F.fl.X
    rw [hl_eq]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  have hloc : l ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Submodule.span (𝓞 D.host.E) (Set.range F.fl.e)) := by
    rw [← conv_at F Λ hc P hgP]
    exact ⟨1, P.asIdeal.primeCompl.one_mem, by rw [one_smul]; exact hlX⟩
  obtain ⟨t', ht', ht'l⟩ := (mem_locP P.asIdeal _ _).1 hloc
  have hv2 : t' • l = ∑ a, ((t' : D.host.E) * (((Lat.gS D : ℕ) : D.host.E)⁻¹ * ((t : D.host.E) * y a))) • F.fl.e a := by
    rw [hl_eq, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← algebraMap_smul D.host.E t', smul_smul]
  have hjr : (j : ℕ) < D.R.rS := lt_of_lt_of_le hji (Nat.lt_succ_iff.1 i.2)
  obtain ⟨o, ho⟩ := coef_spanO F.fl ht'l _ hv2 ⟨j, hjr⟩
  refine ⟨t' * t, fun h => (hP.mem_or_mem h).elim ht' ht, -o, ?_⟩
  have hyj : y ⟨j, hjr⟩ = uu' j i - uu j i := rfl
  rw [hyj] at ho
  have hgi : ((Lat.gS D : ℕ) : D.host.E) * ((Lat.gS D : ℕ) : D.host.E)⁻¹ = 1 := mul_inv_cancel₀ hg0
  push_cast
  linear_combination ((Lat.gS D : ℕ) : D.host.E) * ho + ((t' : D.host.E) * (t : D.host.E) * (uu' j i - uu j i)) * hgi

end Formalism.L2.SG.Pf.ZsVolLat

end
end

noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolLat

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Matrix IsDedekindDomain
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

theorem g_mem_qq : ((Lat.gS D : ℕ) : D.host.E) ∈
    ((Formalism.L2.SG.Pf.StabIntSh.qq D : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :=
  (FractionalIdeal.mem_coeIdeal _).2 ⟨_, Ideal.mem_span_singleton_self _, by simp⟩

theorem g_mul_mem {k : ℕ} {x : D.host.E} (hx : x ∈ Formalism.L2.SG.Pf.StabIntSh.ddPow D k) :
    ((Lat.gS D : ℕ) : D.host.E) * x ∈ Formalism.L2.SG.Pf.StabIntSh.qdPow D k :=
  FractionalIdeal.mul_mem_mul g_mem_qq hx

theorem o_mem_ddPow (k : ℕ) (o : 𝓞 D.host.E) : (o : D.host.E) ∈ Formalism.L2.SG.Pf.StabIntSh.ddPow D k := by
  have h := (FractionalIdeal.mem_coe).1 (Submodule.smul_mem _ o ((FractionalIdeal.mem_coe).2 (one_mem_ddPow (D := D) k)))
  rwa [Algebra.smul_def, mul_one] at h

theorem cong_glob {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T')
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hc : IsFixedConv Λ (Lat.gS D) F) (hc' : IsFixedConv Λ (Lat.gS D) F')
    (hX : XLam Λ F = XS D F.fl) (hX' : XLam Λ F' = XS D F'.fl) (hz : F.fl.z ∈ Λ) (hz' : F'.fl.z ∈ Λ)
    (hadm : ∀ b, ModG (VS D) Λ (Lat.gS D) (F'.fl.fvec b - F.fl.fvec b))
    (s : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hs : ∀ v ∈ Λ, s v ∈ Λ)
    (uu uu' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) (huu : IsUpUni uu) (huu' : IsUpUni uu')
    (hfr : ∀ b, s (F.fl.fvec b) = ∑ c, uu c b • F.fl.fvec c) (hfr' : ∀ b, s (F'.fl.fvec b) = ∑ c, uu' c b • F'.fl.fvec c)
    (j i : Fin (D.R.rS + 1)) (hji : j < i) :
    uu j i - uu' j i ∈ Formalism.L2.SG.Pf.StabIntSh.qdPow D ((i : ℕ) - (j : ℕ)) := by
  have h1 : uu j i ∈ Formalism.L2.SG.Pf.StabIntSh.ddPow D ((i : ℕ) - (j : ℕ)) := frame_entry F Λ hX hz s hs uu huu hfr j i hji
  have h2 : uu' j i ∈ Formalism.L2.SG.Pf.StabIntSh.ddPow D ((i : ℕ) - (j : ℕ)) :=
    frame_entry F' Λ hX' hz' s hs uu' huu' hfr' j i hji
  have hd : uu j i - uu' j i ∈ Formalism.L2.SG.Pf.StabIntSh.ddPow D ((i : ℕ) - (j : ℕ)) :=
    (FractionalIdeal.mem_coe).1 (Submodule.sub_mem _ ((FractionalIdeal.mem_coe).2 h1) ((FractionalIdeal.mem_coe).2 h2))
  refine (FractionalIdeal.mem_coe).1 (mem_of_loc _ _ fun P => ?_)
  by_cases hgP : ((Lat.gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal
  · obtain ⟨t, ht, o, ho⟩ := cong_at F F' Λ hc hc' hz' hadm s hs uu uu' huu huu' hfr hfr' P hgP j i hji
    refine ⟨t, ht, ?_⟩
    rw [ho]
    exact (FractionalIdeal.mem_coe).2 (g_mul_mem (o_mem_ddPow _ o))
  · refine ⟨((Lat.gS D : ℕ) : 𝓞 D.host.E), hgP, ?_⟩
    have e : (((Lat.gS D : ℕ) : 𝓞 D.host.E) : D.host.E) = ((Lat.gS D : ℕ) : D.host.E) := by simp
    rw [e]
    exact (FractionalIdeal.mem_coe).2 (g_mul_mem hd)

end Formalism.L2.SG.Pf.ZsVolLat

end
end

noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolLat

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal Matrix
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

theorem conj_ddPow (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (hA : ∀ p, Agree δ M p) {k : ℕ} (hk : k ≤ D.R.rS) {x : D.host.E} (hx : x ∈ Formalism.L2.SG.Pf.StabIntSh.ddPow D k) :
    D.conjF x ∈ Formalism.L2.SG.Pf.StabIntSh.ddPow D k := by
  have hLG := Formalism.L2.SG.Pf.StabIntSh.locGlob (D := D)
  have hne := (Formalism.L2.SG.Pf.StabIntSh.shapeNZ (D := D)).1 k
  exact (hLG _ hne _).1 fun p => Formalism.L2.SG.Pf.StabIntSh.locMem_conj δ M hA p hk ((hLG _ hne _).2 hx p)

theorem conj_qdPow (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (hA : ∀ p, Agree δ M p) {k : ℕ} (hk : k ≤ D.R.rS) {x : D.host.E} (hx : x ∈ Formalism.L2.SG.Pf.StabIntSh.qdPow D k) :
    D.conjF x ∈ Formalism.L2.SG.Pf.StabIntSh.qdPow D k := by
  unfold Formalism.L2.SG.Pf.StabIntSh.qdPow Formalism.L2.SG.Pf.StabIntSh.qq at *
  rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.mem_singleton_mul] at hx ⊢
  obtain ⟨z, hz, rfl⟩ := hx
  refine ⟨D.conjF z, conj_ddPow δ M hA hk hz, ?_⟩
  rw [map_mul]
  congr 1
  simp

theorem bt_sgn (uu' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) (j i : Fin (D.R.rS + 1)) :
    Formalism.L2.SG.Pf.StabIntSh.bt D (Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS * uu' * Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS) j i = uu' j i := by
  unfold Formalism.L2.SG.Pf.StabIntSh.bt Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  have h1 : ((-1 : D.host.E) ^ (D.R.rS - j.val)) * (-1) ^ (D.R.rS - j.val) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; simp
  have h2 : ((-1 : D.host.E) ^ (D.R.rS - i.val)) * (-1) ^ (D.R.rS - i.val) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; simp
  linear_combination (uu' j i * (-1) ^ (D.R.rS - i.val) * (-1) ^ (D.R.rS - i.val)) * h1 + uu' j i * h2

theorem star_conjF (x : D.host.E) : star x = D.conjF x := by
  rw [D.conjF_eq]
  exact Formalism.BasicNotions.Examples₂.star_eq_conj D.host x

variable (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)
  (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

theorem frameShape_holds : Formalism.L2.SG.Pf.ZsVolIn.FrameShapeP M δ u u' F0 what₂ := by
  intro γ w F' L U hH s hs uu uu' huu huu' hfr hfr'
  obtain ⟨hA, hT, hR, hP, hE, hN⟩ := hH
  obtain ⟨⟨⟨hLift', _, hFOK⟩, _⟩, hAdm, _, _, _⟩ := hN
  obtain ⟨_, ⟨_, _, hLift, hConv⟩, hXF⟩ := hR.1 γ.lam γ.mem
  have hsΛ : ∀ v ∈ γ.lam, s v ∈ γ.lam := fun v hv => by
    have h := hs.1.1.2
    rw [← h]
    exact Submodule.mem_map_of_mem hv
  have hadm : ∀ b, ModG (VS D) γ.lam (Lat.gS D) (F'.fl.fvec b - (lf D F0).fl.fvec b) := by
    intro b
    have h := hAdm.2.2 b
    convert h using 3
    simp [frameAct, Matrix.one_apply]
    rfl
  intro i j hji
  have hk : ((i : ℕ) - (j : ℕ)) ≤ D.R.rS := by have := i.2; omega
  have h1 := frame_entry (lf D F0) γ.lam hXF hLift.1 s hsΛ uu huu hfr j i hji
  have h2 := frame_entry F' γ.lam hFOK.2 hLift'.1 s hsΛ uu' huu' hfr' j i hji
  have h3 := cong_glob (lf D F0) F' γ.lam hConv hFOK.1 hXF hFOK.2 hLift.1 hLift'.1 hadm s hsΛ uu uu' huu huu' hfr hfr' j i hji
  rw [Matrix.conjTranspose_apply, bt_sgn, star_conjF]
  refine ⟨conj_ddPow δ M hA hk h1, h2, ?_⟩
  rw [← map_sub]
  exact conj_qdPow δ M hA hk h3

end Formalism.L2.SG.Pf.ZsVolLat

end
