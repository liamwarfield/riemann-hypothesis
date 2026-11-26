module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibAsm

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ThetaIntMem
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.MemClRow
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem mem_cl_row (b : Fin D.R.rS) (x : InfinitePlace X.B.I.F → Fin (D.R.k + 1) → ℂ) :
    x ∈ cLat X u (Sum.inl (Sum.inr b)) ↔ ∃ y ∈ aaLb X b, rowV X u y = x := by
  let f : (VS D).V →+ (InfinitePlace X.B.I.F → Fin (D.R.k + 1) → ℂ) :=
    AddMonoidHom.mk' (rowV X u) (fun x y => rowV_add (X := X) (u := u) x y)
  let S : AddSubgroup (VS D).V := (Submodule.span (𝓞 D.host.E)
    {y | ∃ c ∈ (aaD D b : Set D.host.E), ∃ l ∈ X.Lb, y = c • l}).toAddSubgroup
  have hc : cLat X u (Sum.inl (Sum.inr b)) = S.map f := AddSubgroup.closure_eq (S.map f)
  have key : x ∈ cLat X u (Sum.inl (Sum.inr b)) ↔ x ∈ S.map f := by
    rw [hc]; exact Iff.rfl
  exact key.trans AddSubgroup.mem_map

def imSub (a : Fin D.R.rS) : AddSubgroup D.host.E where
  carrier := {t | t ∈ ((aaD D a * aaD D a : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Set D.host.E) ∧
    D.host.conj t = -t}
  add_mem' := fun {s t} hs ht => ⟨Submodule.add_mem _ hs.1 ht.1, by rw [map_add (f := _), hs.2, ht.2, neg_add]⟩
  zero_mem' := ⟨Submodule.zero_mem _, by rw [map_zero, neg_zero]⟩
  neg_mem' := fun {t} ht => ⟨Submodule.neg_mem _ ht.1, by rw [map_neg, ht.2]⟩

def imHom : D.host.E →+ (InfinitePlace X.B.I.F → ℝ) where
  toFun t := fun v => (embS D (X.pl v) t).im
  map_zero' := by funext v; simp
  map_add' s t := by funext v; simp

theorem mem_cl_im (a : Fin D.R.rS) (x : InfinitePlace X.B.I.F → ℝ) :
    x ∈ cLat X u (Sum.inr (Sum.inr a)) ↔
      ∃ t : D.host.E, t ∈ aaD D a * aaD D a ∧ D.host.conj t = -t ∧ (fun v => (embS D (X.pl v) t).im) = x := by
  have hc : cLat X u (Sum.inr (Sum.inr a)) = (imSub a).map (imHom X) :=
    AddSubgroup.closure_eq ((imSub a).map (imHom X))
  have key : x ∈ cLat X u (Sum.inr (Sum.inr a)) ↔ x ∈ (imSub a).map (imHom X) := by
    rw [hc]; exact Iff.rfl
  refine key.trans (AddSubgroup.mem_map.trans ?_)
  constructor
  · rintro ⟨t, ⟨h1, h2⟩, rfl⟩
    exact ⟨t, h1, h2, rfl⟩
  · rintro ⟨t, h1, h2, rfl⟩
    exact ⟨t, ⟨h1, h2⟩, rfl⟩

theorem im_inj {t t' : D.host.E} (ht : D.host.conj t = -t) (ht' : D.host.conj t' = -t')
    (h : ∀ v : InfinitePlace X.B.I.F, (embS D (X.pl v) t).im = (embS D (X.pl v) t').im) : t = t' := by
  obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace X.B.I.F))
  have hs : D.host.conj (t - t') = -(t - t') := by rw [map_sub, ht, ht']; ring
  have h1 := CovB.embS_conj (D := D) (X.pl v) (t - t')
  rw [hs, map_neg] at h1
  have him : (embS D (X.pl v) (t - t')).im = 0 := by rw [map_sub, Complex.sub_im, h v, sub_self]
  have hre : (embS D (X.pl v) (t - t')).re = 0 := by
    have h2 := congrArg Complex.re h1
    simp only [Complex.neg_re, Complex.conj_re] at h2
    linarith
  have h0 : embS D (X.pl v) (t - t') = 0 := Complex.ext hre him
  exact sub_eq_zero.mp ((map_eq_zero_iff _ (RingHom.injective _)).mp h0)

theorem aaLb_inW {b : Fin D.R.rS} {y : (VS D).V} (hy : y ∈ aaLb X b) : InW X y := by
  have hL : ∀ l ∈ X.Lb, InW X l := by
    intro l hl
    have hp := Alg.pW_inW (X := X) l
    have he : pW X l = l := by
      have h1 := Level.prV_Lb (X := X) l hl
      rw [Level.prV_apply] at h1
      simpa only [pW] using h1
    rwa [he] at hp
  simp only [aaLb, SetLike.mem_coe] at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, -, l, hl, rfl⟩ := hx
    intro d
    exact ⟨by rw [map_smul, ((hL l hl) d).1, smul_zero], by rw [map_smul, ((hL l hl) d).2, smul_zero]⟩
  | zero => intro d; exact ⟨map_zero _, map_zero _⟩
  | add x z _ _ hx hz =>
    intro d
    exact ⟨by rw [map_add (f := _), (hx d).1, (hz d).1, add_zero], by rw [map_add (f := _), (hx d).2, (hz d).2, add_zero]⟩
  | smul o x _ hx =>
    intro d
    refine ⟨?_, ?_⟩
    · rw [← algebraMap_smul D.host.E o x, map_smul, (hx d).1, smul_zero]
    · rw [← algebraMap_smul D.host.E o x, map_smul, (hx d).2, smul_zero]

end Formalism.L2.SG.Pf.NcReal.JX.NOf
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.StarEqConj
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem star_eq_conj' (t : D.host.E) : star t = D.host.conj t := by
  apply D.host.φ₀.injective
  rw [Formalism.BasicNotions.Examples₂.emb_star, Formalism.BasicNotions.Examples₂.emb_conj]

theorem theta_spec : IsIntegral ℤ (theta D) ∧ theta D + D.host.conj (theta D) = 1 := by
  have h := thetaEx_holds D
  unfold theta
  rw [dite_eq_left h]
  exact h.choose_spec

theorem entry_rel {X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E} {xs : Fin D.R.rS → (VS D).V}
    {M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E} (hok : DataOK X X0 xs M) (b a : Fin D.R.rS) :
    M b a + star (M a b) = -Gp D X0 xs b a := by
  have hok' := hok
  obtain ⟨-, -, -, hM⟩ := hok'
  have h := congrFun (congrFun hM b) a
  simpa only [Matrix.add_apply, Matrix.neg_apply, Matrix.conjTranspose_apply] using h

theorem kblk {X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E} {xs : Fin D.R.rS → (VS D).V}
    {M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E} (hok : DataOK X X0 xs M) (p : Formalism.L2.SG.Pf.LsNc5.LtPair D.R.rS) :
    blkQ X u X0 xs M (Sum.inr (Sum.inl p)) - tauQ X u (Sum.inr (Sum.inl p)) (blkQ X u X0 xs M) =
      embV X (M p.1.1 p.1.2) := by
  have hok' := hok
  obtain ⟨hup, hd, hW, -⟩ := hok'
  show (fun v => (embS D (X.pl v) (M p.1.1 p.1.2) - star (embS D (X.pl v) (M p.1.2 p.1.1))) / 2) -
      (fun v => Hc X u (blkQ X u X0 xs M) v p.1.1 p.1.2 / 2) =
      fun v => embS D (X.pl v) (M p.1.1 p.1.2)
  funext v
  simp only [Pi.sub_apply]
  rw [Hc_blkQ X u X0 xs M hup hd hW v, Matrix.map_apply]
  have e := congrArg (embS D (X.pl v)) (entry_rel X hok p.1.1 p.1.2)
  rw [map_add (f := _), map_neg, Formalism.BasicNotions.Examples₂.emb_star, starRingEnd_apply] at e
  rw [show embS D (X.pl v) (Gp D X0 xs p.1.1 p.1.2) =
      -(embS D (X.pl v) (M p.1.1 p.1.2) + star (embS D (X.pl v) (M p.1.2 p.1.1))) by
    rw [e, neg_neg]]
  ring

def xiA (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (xs : Fin D.R.rS → (VS D).V)
    (M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (a : Fin D.R.rS) : D.host.E :=
  M a a + Gp D X0 xs a a * theta D

theorem Gp_diag_star (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (xs : Fin D.R.rS → (VS D).V) (a : Fin D.R.rS) :
    star (Gp D X0 xs a a) = Gp D X0 xs a a := by
  have h := congrFun (congrFun (Gp_herm X0 xs) a) a
  simpa only [Matrix.conjTranspose_apply] using h

theorem xiA_conj {X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E} {xs : Fin D.R.rS → (VS D).V}
    {M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E} (hok : DataOK X X0 xs M) (a : Fin D.R.rS) :
    D.host.conj (xiA X0 xs M a) = -xiA X0 xs M a := by
  have hs : ∀ t : D.host.E, D.host.conj t = star t := fun t => (star_eq_conj' t).symm
  have hθ : D.host.conj (theta D) = 1 - theta D := eq_sub_of_add_eq' (theta_spec (D := D)).2
  have hM : star (M a a) = -Gp D X0 xs a a - M a a := eq_sub_of_add_eq' (entry_rel X hok a a)
  unfold xiA
  rw [map_add (f := _), map_mul, hθ, hs (M a a), hs (Gp D X0 xs a a), Gp_diag_star X0 xs a, hM]
  ring

theorem imblk {X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E} {xs : Fin D.R.rS → (VS D).V}
    {M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E} (hok : DataOK X X0 xs M) (a : Fin D.R.rS) :
    blkQ X u X0 xs M (Sum.inr (Sum.inr a)) - tauQ X u (Sum.inr (Sum.inr a)) (blkQ X u X0 xs M) =
      fun v => (embS D (X.pl v) (xiA X0 xs M a)).im := by
  have hok' := hok
  obtain ⟨hup, hd, hW, -⟩ := hok'
  show (fun v => (embS D (X.pl v) (M a a)).im) -
      (fun v => -((Hc X u (blkQ X u X0 xs M) v a a).re * (embS D (X.pl v) (theta D)).im)) =
      fun v => (embS D (X.pl v) (xiA X0 xs M a)).im
  funext v
  simp only [Pi.sub_apply]
  rw [Hc_blkQ X u X0 xs M hup hd hW v, Matrix.map_apply]
  have hreal : (embS D (X.pl v) (Gp D X0 xs a a)).im = 0 := by
    have h1 := congrArg (embS D (X.pl v)) (Gp_diag_star X0 xs a)
    rw [Formalism.BasicNotions.Examples₂.emb_star] at h1
    exact Complex.conj_eq_iff_im.mp h1
  simp only [xiA, map_add (f := _), map_mul, Complex.add_im, Complex.mul_im, hreal]
  ring

end Formalism.L2.SG.Pf.NcReal.JX.NOf
end
end

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem theta_int_mem {I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E} {x : D.host.E} (hx : x ∈ I) :
    x * theta D ∈ I := by
  unfold theta
  split_ifs with h
  · obtain ⟨hint, -⟩ := h.choose_spec
    have hmem : (⟨h.choose, hint⟩ : 𝓞 D.host.E) • x ∈ (I : Submodule (𝓞 D.host.E) D.host.E) :=
      Submodule.smul_mem _ _ hx
    rwa [Algebra.smul_def, mul_comm] at hmem
  · rw [mul_zero]
    exact (I : Submodule (𝓞 D.host.E) D.host.E).zero_mem

theorem inW_sub {X : HidaSetting D} {x y : (VS D).V} (hx : InW X x) (hy : InW X y) : InW X (x - y) := by
  intro c
  obtain ⟨h1, h2⟩ := hx c
  obtain ⟨h3, h4⟩ := hy c
  exact ⟨by rw [map_sub, h1, h3, sub_zero], by rw [map_sub, h2, h4, sub_zero]⟩

theorem xblk {X : HidaSetting D} (u : D.what₂.Word) (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)
    (xs : Fin D.R.rS → (VS D).V) (M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)
    (p : Formalism.L2.SG.Pf.LsNc5.LtPair D.R.rS) :
    blkQ X u X0 xs M (Sum.inl (Sum.inl p)) - tauQ X u (Sum.inl (Sum.inl p)) (blkQ X u X0 xs M) =
      embV X (X0 p.1.1 p.1.2) := by
  simp only [blkQ, tauQ]
  first | exact sub_zero _ | rfl | simp

theorem rblk {X : HidaSetting D} (u : D.what₂.Word) (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)
    (xs : Fin D.R.rS → (VS D).V) (M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (b : Fin D.R.rS) :
    blkQ X u X0 xs M (Sum.inl (Sum.inr b)) - tauQ X u (Sum.inl (Sum.inr b)) (blkQ X u X0 xs M) =
      rowV X u (xs b) := by
  simp only [blkQ, tauQ]
  first | exact sub_zero _ | rfl | simp

theorem fibQ_holds : FibQ := by
  intro D X u X0 xs M hok
  have hup := hok.1
  have hd := hok.2.1
  have hW := hok.2.2.1
  constructor
  · intro h

    have hX : ∀ b a : Fin D.R.rS, b < a → X0 b a ∈ iQ D b a := by
      intro b a hba
      have h1 := h (Sum.inl (Sum.inl ⟨(b, a), hba⟩))
      rw [xblk] at h1
      simp only [cLat] at h1
      obtain ⟨t, ht, hte⟩ := (CovB.mem_closure_embV X _ _).1 h1
      have : t = X0 b a := CovB.embVHom_injective X hte
      rw [← this]; exact ht

    have hR : ∀ b, xs b ∈ aaLb X b := by
      intro b
      have h1 := h (Sum.inl (Sum.inr b))
      rw [rblk] at h1
      simp only [cLat] at h1
      obtain ⟨y, hy, hye⟩ := (mem_cl_row X u b _).1 h1
      have hz : rowV X u (xs b - y) = 0 := by rw [rowV_sub, hye, sub_self]
      have := rowV_inj X u _ (inW_sub (hW b) (aaLb_inW X hy)) hz
      rw [sub_eq_zero] at this
      rw [this]; exact hy
    have hG := Gp_mem X X0 xs hup hd hX hR
    refine ⟨hX, hR, ?_⟩

    have hMu : ∀ b a : Fin D.R.rS, b < a → M b a ∈ iP D b a := by
      intro b a hba
      have h1 := h (Sum.inr (Sum.inl ⟨(b, a), hba⟩))
      rw [kblk X u hok] at h1
      simp only [cLat] at h1
      obtain ⟨t, ht, hte⟩ := (CovB.mem_closure_embV X _ _).1 h1
      have : t = M b a := CovB.embVHom_injective X hte
      rw [← this]; exact ht
    intro b a
    rcases lt_trichotomy b a with hba | hba | hba
    · exact hMu b a hba
    · subst hba
      have h1 := h (Sum.inr (Sum.inr b))
      rw [imblk X u hok] at h1
      obtain ⟨t, ht, htc, hte⟩ := (mem_cl_im X u b _).1 h1
      have hteq : t = xiA X0 xs M b := im_inj X htc (xiA_conj X hok b) fun v => congrFun hte v
      have hxi : xiA X0 xs M b ∈ iP D b b := by rw [← hteq]; exact ht
      have e : M b b = xiA X0 xs M b - Gp D X0 xs b b * theta D := by unfold xiA; ring
      rw [e]
      exact Submodule.sub_mem _ hxi (theta_int_mem (hG b b))
    · have e := entry_rel X hok b a
      have e2 : M b a = -Gp D X0 xs b a - star (M a b) := by rw [← e]; ring
      rw [e2]
      refine Submodule.sub_mem _ (Submodule.neg_mem _ (hG b a)) ?_
      have hab : M a b ∈ iP D b a := by rw [iP_comm]; exact hMu a b hba
      exact star_mem_iP hab
  · rintro ⟨hX, hR, hM⟩
    have hG := Gp_mem X X0 xs hup hd hX hR
    intro p
    rcases p with ((p | b) | (p | a))
    · rw [xblk]
      simp only [cLat]
      exact (CovB.mem_closure_embV X _ _).2 ⟨X0 p.1.1 p.1.2, hX _ _ p.2, rfl⟩
    · rw [rblk]
      simp only [cLat]
      exact (mem_cl_row X u b _).2 ⟨xs b, hR b, rfl⟩
    · rw [kblk X u hok]
      simp only [cLat]
      exact (CovB.mem_closure_embV X _ _).2 ⟨M p.1.1 p.1.2, hM _ _, rfl⟩
    · rw [imblk X u hok]
      refine (mem_cl_im X u a _).2 ⟨xiA X0 xs M a, ?_, xiA_conj X hok a, rfl⟩
      exact Submodule.add_mem _ (hM a a) (theta_int_mem (hG a a))

end Formalism.L2.SG.Pf.NcReal.JX.NOf
end
end

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

theorem nofib_holds : Formalism.L2.SG.Pf.NcReal.JX.NOfib := nofib_of_fibQ fibQ_holds

end Formalism.L2.SG.Pf.NcReal.JX.NOf
