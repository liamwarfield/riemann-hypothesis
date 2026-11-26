module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdBetaS
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarNMove

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBetaRatA
noncomputable section

open scoped Classical
open Matrix Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BRat

open FsLA BwdBetaS OmP

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E}

def projL {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → S.V) : S.V →ₗ[E] S.V where
  toFun v := lin u (pc u v)
  map_add' x y := by rw [pc_add, lin_add]
  map_smul' t x := by rw [pc_smul, lin_smul, RingHom.id_apply]

def moveL {ι : Type*} [Fintype ι] [DecidableEq ι] (u u' : ι → S.V) : S.V →ₗ[E] S.V where
  toFun v := lin u' (pc u v)
  map_add' x y := by rw [pc_add, lin_add]
  map_smul' t x := by rw [pc_smul, lin_smul, RingHom.id_apply]

theorem pc_of_orth {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → S.V) {y : S.V} (hy : ∀ k, S.hT (u k) y = 0) :
    pc u y = 0 := by
  have h0 : (fun k => S.hT (u k) y) = 0 := funext fun k => hy k
  rw [pc, h0, Matrix.mulVec_zero]

theorem lin_zero {ι : Type*} [Fintype ι] (u : ι → S.V) : lin u 0 = 0 := by simp [lin]

theorem isometry_extension_two {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (u u' : ι → S.V) (w : κ → S.V) (hG : gram S u' u' = gram S u u) (hdet : (gram S u u).det ≠ 0)
    (hdetw : (gram S w w).det ≠ 0) (hsp : ∀ i, u' i ∈ Submodule.span E (Set.range w))
    (hkey : ∀ y y', (∀ k, S.hT (u k) y = 0) → (∀ k, S.hT (u k) y' = 0) →
      S.hT (lin w (pc w y)) (lin w (pc w y')) = 0) :
    ∃ g : S.V ≃ₗ[E] S.V, (∀ x y, S.hT (g x) (g y) = S.hT x y) ∧ (∀ i, g (u i) = u' i) ∧
      (∀ y, (∀ k, S.hT (u k) y = 0) → g y = y - lin w (pc w y)) := by
  let P : S.V →ₗ[E] S.V := LinearMap.id - projL u
  let β : S.V →ₗ[E] S.V := (LinearMap.id - projL w) ∘ₗ P + moveL u u'
  have hβ : ∀ v, β v = ((v - lin u (pc u v)) - lin w (pc w (v - lin u (pc u v)))) + lin u' (pc u v) :=
    fun v => rfl
  have hsp' : ∀ c, lin u' c ∈ Submodule.span E (Set.range w) := fun c =>
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hsp i)
  have hGe : ∀ i j, S.hT (u' i) (u' j) = S.hT (u i) (u j) := fun i j => congrFun (congrFun hG i) j
  have hiso : ∀ x y, S.hT (β x) (β y) = S.hT x y := by
    intro x y
    set x' := x - lin u (pc u x) with hx'
    set y' := y - lin u (pc u y) with hy'
    have hx'u : ∀ k, S.hT (u k) x' = 0 := fun k => hT_u_rem u hdet x k
    have hy'u : ∀ k, S.hT (u k) y' = 0 := fun k => hT_u_rem u hdet y k
    have hk := hkey x' y' hx'u hy'u
    rw [hβ, hβ]

    have t1 : S.hT (x' - lin w (pc w x')) (lin u' (pc u y)) = 0 := (hT_span_rem w hdetw x' _ (hsp' _)).2
    have t2 : S.hT (lin u' (pc u x)) (y' - lin w (pc w y')) = 0 := (hT_span_rem w hdetw y' _ (hsp' _)).1
    have t3 : S.hT (lin u' (pc u x)) (lin u' (pc u y)) = S.hT (lin u (pc u x)) (lin u (pc u y)) := by
      rw [hT_lin_lin, hT_lin_lin]; simp only [hGe]
    have t4 : S.hT (x' - lin w (pc w x')) (lin w (pc w y')) = 0 :=
      (hT_span_rem w hdetw x' _ (lin_sub w _)).2
    have t5 : S.hT (lin w (pc w x')) (y' - lin w (pc w y')) = 0 :=
      (hT_span_rem w hdetw y' _ (lin_sub w _)).1
    have t6 : S.hT (x' - lin w (pc w x')) (y' - lin w (pc w y')) = S.hT x' y' := by
      have e1 : S.hT (x' - lin w (pc w x')) (y' - lin w (pc w y')) =
          S.hT (x' - lin w (pc w x')) y' := by
        rw [map_sub, t4, sub_zero]
      have e2 : S.hT (lin w (pc w x')) y' = 0 := by
        have := t5
        rw [map_sub, hk, sub_zero] at this
        exact this
      rw [e1, map_sub S.hT x' (lin w (pc w x')), LinearMap.sub_apply, e2, sub_zero]
    have hxy : S.hT x y = S.hT x' y' + S.hT (lin u (pc u x)) (lin u (pc u y)) := by
      have dx : x = x' + lin u (pc u x) := by rw [hx']; abel
      have dy : y = y' + lin u (pc u y) := by rw [hy']; abel
      conv_lhs => rw [dx, dy]
      simp only [map_add (f := _), LinearMap.add_apply]
      rw [(hT_span_rem u hdet x _ (lin_sub u _)).2, (hT_span_rem u hdet y _ (lin_sub u _)).1]
      ring
    rw [← hx', ← hy']
    simp only [map_add (f := _), LinearMap.add_apply]
    rw [t1, t2, t3, t6, hxy]
    ring
  have hinj : Function.Injective β := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro v hv
    rw [LinearMap.mem_ker] at hv
    refine (Submodule.mem_bot E).2 (S.nondeg.1 v fun y => ?_)
    rw [← hiso v y, hv, map_zero, LinearMap.zero_apply]
  have hbij : Function.Bijective β := ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩
  refine ⟨LinearEquiv.ofBijective β hbij, hiso, fun i => ?_, fun y hy => ?_⟩
  · show β (u i) = u' i
    rw [hβ, pc_self u hdet, lin_single, lin_single, sub_self]
    have : pc w (0 : S.V) = 0 := by
      have := pc_smul w 0 0
      simpa using this
    rw [this, lin_zero, sub_zero, zero_add]
  · show β y = y - lin w (pc w y)
    rw [hβ, pc_of_orth u hy, lin_zero, lin_zero, sub_zero, add_zero]

variable {r : ℕ}

theorem norm_om_ne {TA TB : E} (A : FlagG S r TA) (B : FlagG S r TB) (hdet : (Zhat A B).det ≠ 0) {Ω : S.V}
    (hΩ : OmV A B Ω) (hG : Gflag A B ≠ 0) : 1 + TA * S.hT Ω Ω ≠ 0 := by
  have hx := om_zcoef A B hdet hΩ
  set c := (Zhat A B)⁻¹ (Fin.last r) (Fin.last r) with hc
  set x := Ω - c • B.z with hxd
  have hΩe : Ω = x + c • B.z := by rw [hxd]; abel
  have hxx : S.hT x x = 0 := NMoveP.hT_X_X B hx hx
  have hxz : S.hT x B.z = 0 := by
    have h := NMoveP.hT_f_X B (Fin.last r) hx
    rw [NMoveP.fvecL] at h
    rw [BwdNA.hsw S B.z x, h, star_zero]
  have hzx : S.hT B.z x = 0 := by
    have h := NMoveP.hT_f_X B (Fin.last r) hx
    rwa [NMoveP.fvecL] at h
  have hnorm : S.hT Ω Ω = star c * c * (-TB) := by
    rw [hΩe]
    simp only [map_add (f := _), LinearMap.add_apply, LinearMap.map_smulₛₗ, map_smul, LinearMap.smul_apply, hxx, hxz, hzx,
      B.z_norm, smul_eq_mul, starRingEnd_apply, mul_zero, zero_add, add_zero]
    ring
  have hcl : c = leadMinorE (Zhat A B) r / (Zhat A B).det := inv_last _
  intro h0
  apply hG
  unfold Gflag Dl
  rw [FsLA.leadMinorE_full]
  rw [hnorm, hcl, star_div₀] at h0
  have hs : star (Zhat A B).det ≠ 0 := star_ne_zero.2 hdet
  field_simp at h0
  linear_combination h0

theorem key_X {TA TB : E} (A : FlagG S r TA) (B : FlagG S r TB) (hdet : (Zhat A B).det ≠ 0) {Ω : S.V}
    (hΩ : OmV A B Ω) (hG : Gflag A B ≠ 0) {q : S.V}
    (hq : q ∈ Submodule.span E (Set.range (Sum.elim A.fvec B.fvec))) (hqA : ∀ a, S.hT (A.fvec a) q = 0)
    (hqΩ : S.hT Ω q = 0) : q ∈ A.X := by
  obtain ⟨x, hx, c, rfl⟩ := dec A B hdet hΩ hq hqA
  have hΩx : S.hT Ω x = 0 := by
    rw [BwdNA.hsw S x Ω]
    have : x ∈ A.X := hx
    have h := (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth S).1 (show Ω ∈ orth S A.X from ?_) x this
    · rw [h, star_zero]
    · refine (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth S).2 fun y hy => ?_
      change y ∈ Submodule.span E (Set.range A.e) at hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨i, rfl⟩ := hy
        rw [← fvec_cs, hΩ.2]
        simp [Fin.castSucc_ne_last]
      | zero => simp
      | add a b _ _ ha hb => rw [map_add (f := _), LinearMap.add_apply, ha, hb, add_zero]
      | smul t y _ hy => rw [BwdNA.hT_smulL, hy, mul_zero]
  have hΩz : S.hT Ω A.z = 1 := by
    rw [BwdNA.hsw S A.z Ω, ← fvec_last, hΩ.2]
    simp
  have h1 : S.hT Ω (x + c • (A.z + TA • Ω)) = c * (1 + TA * S.hT Ω Ω) := by
    rw [map_add (f := _), hΩx, zero_add, map_smul, map_add (f := _), map_smul, hΩz, smul_eq_mul, smul_eq_mul]
  rw [h1] at hqΩ
  have hc : c = 0 := (mul_eq_zero.1 hqΩ).resolve_right (norm_om_ne A B hdet hΩ hG)
  rw [hc, zero_smul, add_zero]
  exact hx

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BRat
end
end

noncomputable section

open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated
  Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

open BwdCut BwdBetaCut OmP BwdBetaS

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (u u' F0 what₂)


set_option maxHeartbeats 1000000 in
theorem betaRat_holds : BetaRat Zd u u' F0 what₂ := by
  intro γ Z F'₂ φ φ' Λ₂ hB
  obtain ⟨hC, hCtx, hS, -, -, hTH, hPD, hGv⟩ := hB
  obtain ⟨hZd, hZ₁d', hx'⟩ := starMinors_holds u u' F0 what₂ γ Z hCtx
  have hZ : ZhatL (lf D F0) F'₂ = Z := hS.1
  have hrow := hC.2.1.1 γ.lam γ.mem
  have hΛ : Submodule.IsFullLattice D.host.E γ.lam := hrow.1.1
  have hLlf : IsLift γ.lam (lf D F0) := hrow.2.1.2.2.1
  have hLrep : IsLift γ.lam (repF γ) := hPD.1
  set f := frame (lf D F0) with hf
  set g := frame (repF γ) with hg
  set F₂ := F'₂.fl with hF₂
  set Z₁ := starZh f g with hZ₁
  have hlm : ∀ l, leadMinorE Z₁ l = leadMinorE (starZh f (starFrame γ)) l := fun l => (star_frame_lead_minor γ l).symm
  have hZ₁d : Z₁.det ≠ 0 := by
    rw [← FsLA.leadMinorE_full, hlm, FsLA.leadMinorE_full]; exact hZ₁d'
  have hx : leadMinorE Z₁ D.R.rS * Z.det = leadMinorE Z D.R.rS * Z₁.det := by
    rw [hlm, ← FsLA.leadMinorE_full Z₁, hlm, FsLA.leadMinorE_full]; exact hx'
  have hfF : f = F0.fvec := rfl
  have hZe : ∀ a b, (VS D).hT (f a) (F₂.fvec b) = Z a b := fun a b => by rw [← hZ]; rfl
  have hg2 : FsLA.gram (VS D) f F₂.fvec = Zᴴ := by
    refine Matrix.ext fun i j => ?_
    simp only [FsLA.gram, Matrix.conjTranspose_apply]
    rw [← hZe, ← (LinearMap.isSymm_def.1 (VS D).herm) (f j) (F₂.fvec i), starRingEnd_apply]
  have h1g : ∀ a b, (a ≠ Fin.last D.R.rS ∨ b ≠ Fin.last D.R.rS) → (VS D).hT (g a) (g b) = 0 :=
    fun a b h => FsLA.gram_fvec_zero (repF γ).fl a b h
  have h2g : (VS D).hT (g (Fin.last D.R.rS)) (g (Fin.last D.R.rS)) = -((Tu D u' : ℕ) : D.host.E) :=
    FsLA.gram_fvec_last (repF γ).fl
  have h1f : ∀ a b, (a ≠ Fin.last D.R.rS ∨ b ≠ Fin.last D.R.rS) → (VS D).hT (f a) (f b) = 0 :=
    fun a b h => FsLA.gram_fvec_zero F0 a b h
  have h2f : (VS D).hT (f (Fin.last D.R.rS)) (f (Fin.last D.R.rS)) = -CntLocal.Tn u := FsLA.gram_fvec_last F0
  have hdZ1h : Z₁ᴴ.det ≠ 0 := by rw [Matrix.det_conjTranspose]; exact star_ne_zero.2 hZ₁d
  have hdg2 : (FsLA.gram (VS D) f F₂.fvec).det ≠ 0 := by
    rw [hg2, Matrix.det_conjTranspose]; exact star_ne_zero.2 hZd
  have hx2 : leadMinorE (FsLA.gram (VS D) f F₂.fvec) D.R.rS * Z₁ᴴ.det =
      leadMinorE Z₁ᴴ D.R.rS * (FsLA.gram (VS D) f F₂.fvec).det := by
    rw [hg2, FsLA.lm_conjTranspose, FsLA.lm_conjTranspose, Matrix.det_conjTranspose, Matrix.det_conjTranspose,
      ← star_mul', ← star_mul', mul_comm (leadMinorE Z D.R.rS), hx, mul_comm]
  obtain ⟨F₃, hZ3, hom3, hsp3⟩ := FsLA.frame_la F₂ f h1f h2f Z₁ᴴ hdZ1h hdg2 hx2
  set h := F₃.fvec with hh
  set uu := Sum.elim f g with huu
  set uu' := Sum.elim h F₂.fvec with huu'
  set ww := Sum.elim f F₂.fvec with hww
  have hZ3e : ∀ a b, (VS D).hT (F₂.fvec a) (h b) = Z₁ᴴ a b := fun a b => congrFun (congrFun hZ3 a) b
  have k1 : ∀ a b, (VS D).hT (h a) (h b) = (VS D).hT (f a) (f b) := by
    intro a b
    by_cases hab : a ≠ Fin.last D.R.rS ∨ b ≠ Fin.last D.R.rS
    · exact (FsLA.gram_fvec_zero F₃ a b hab).trans (FsLA.gram_fvec_zero F0 a b hab).symm
    · push_neg at hab
      rw [hab.1, hab.2]
      exact (FsLA.gram_fvec_last F₃).trans (FsLA.gram_fvec_last F0).symm
  have k2 : ∀ a b, (VS D).hT (h a) (F₂.fvec b) = (VS D).hT (f a) (g b) := by
    intro a b
    rw [← (LinearMap.isSymm_def.1 (VS D).herm) (F₂.fvec b) (h a), hZ3e, starRingEnd_apply,
      Matrix.conjTranspose_apply, star_star]
    rfl
  have k3 : ∀ a b, (VS D).hT (F₂.fvec a) (h b) = (VS D).hT (g a) (f b) := by
    intro a b
    rw [hZ3e, Matrix.conjTranspose_apply, ← starRingEnd_apply]
    exact (LinearMap.isSymm_def.1 (VS D).herm) (f b) (g a)
  have k4 : ∀ a b, (VS D).hT (F₂.fvec a) (F₂.fvec b) = (VS D).hT (g a) (g b) := by
    intro a b
    by_cases hab : a ≠ Fin.last D.R.rS ∨ b ≠ Fin.last D.R.rS
    · exact (FsLA.gram_fvec_zero F₂ a b hab).trans (h1g a b hab).symm
    · push_neg at hab
      rw [hab.1, hab.2]
      exact (FsLA.gram_fvec_last F₂).trans h2g.symm
  have hGr : FsLA.gram (VS D) uu' uu' = FsLA.gram (VS D) uu uu := by
    refine Matrix.ext fun i j => ?_
    rcases i with a | a <;> rcases j with b | b
    · exact k1 a b
    · exact k2 a b
    · exact k3 a b
    · exact k4 a b
  have hGg : (FsLA.gram (VS D) g F0.fvec).det * star (FsLA.gram (VS D) g F0.fvec).det -
      CntLocal.Tn u * ((Tu D u' : ℕ) : D.host.E) *
        (leadMinorE (FsLA.gram (VS D) g F0.fvec) D.R.rS * star (leadMinorE (FsLA.gram (VS D) g F0.fvec) D.R.rS))
        ≠ 0 := by
    rw [← FsLA.leadMinorE_full]; exact hGv
  have hdet : (FsLA.gram (VS D) uu uu).det ≠ 0 := FsLA.gram_pair_det F0 g h1g h2g hZ₁d hGg
  have hGZ : Gflag F0 F₂ ≠ 0 := hTH.1.2.2
  have hGg₂ : (FsLA.gram (VS D) F₂.fvec F0.fvec).det * star (FsLA.gram (VS D) F₂.fvec F0.fvec).det -
      CntLocal.Tn u * ((Tu D u' : ℕ) : D.host.E) *
        (leadMinorE (FsLA.gram (VS D) F₂.fvec F0.fvec) D.R.rS *
          star (leadMinorE (FsLA.gram (VS D) F₂.fvec F0.fvec) D.R.rS)) ≠ 0 := by
    rw [← FsLA.leadMinorE_full]; exact hGZ
  have hdetZ : (Zhat F0 F₂).det ≠ 0 := by
    have e : Zhat F0 F₂ = Z := hZ
    rw [e]; exact hZd
  have hdetw : (FsLA.gram (VS D) ww ww).det ≠ 0 :=
    FsLA.gram_pair_det F0 F₂.fvec (fun a b hab => FsLA.gram_fvec_zero F₂ a b hab) (FsLA.gram_fvec_last F₂)
      hdetZ hGg₂
  have hsp : ∀ i, uu' i ∈ Submodule.span D.host.E (Set.range ww) := by
    have hsub : Set.range (Sum.elim F₂.fvec f) ⊆ Submodule.span D.host.E (Set.range ww) := by
      rintro _ ⟨k, rfl⟩
      rcases k with b | a
      · exact Submodule.subset_span ⟨Sum.inr b, rfl⟩
      · exact Submodule.subset_span ⟨Sum.inl a, rfl⟩
    intro i
    rcases i with a | b
    · exact Submodule.span_le.2 hsub (hsp3 a)
    · exact Submodule.subset_span ⟨Sum.inr b, rfl⟩

  have hdetγ : (Zhat F0 (repF γ).fl).det ≠ 0 := hZ₁d
  obtain ⟨Ω₂, hΩ₂⟩ := exists_om F0 F₂ hdetZ
  obtain ⟨Ωγ, hΩγ⟩ := exists_om F0 (repF γ).fl hdetγ
  have hΩd : Ω₂ - Ωγ ∈ Xsp (lf D F0) :=
    omega_local_holds Zd u u' F0 what₂ hC.2.1 γ Z hCtx F'₂ φ φ' hS hdetγ hZd Ω₂ Ωγ hΩ₂ hΩγ

  have hXq : ∀ y, (∀ k, (VS D).hT (uu k) y = 0) → FsLA.lin ww (FsLA.pc ww y) ∈ F0.X := by
    intro y hy
    have hrem := fun z hz => (FsLA.hT_span_rem ww hdetw y z hz).1
    have hyU : ∀ z ∈ Submodule.span D.host.E (Set.range uu), (VS D).hT z y = 0 :=
      NMoveP.spanL (VS D) uu y hy
    refine BRat.key_X F0 F₂ hdetZ hΩ₂ hGZ (FsLA.lin_sub ww _) (fun a => ?_) ?_
    · have e := hrem (f a) (Submodule.subset_span ⟨Sum.inl a, rfl⟩)
      rw [map_sub, sub_eq_zero] at e
      rw [← e]
      exact hy (Sum.inl a)
    · have e := hrem Ω₂ (Submodule.span_mono (Set.range_comp_subset_range Sum.inr ww) hΩ₂.1)
      rw [map_sub, sub_eq_zero] at e
      rw [← e]
      have e2 : Ω₂ = Ωγ + (Ω₂ - Ωγ) := by abel
      rw [e2, map_add (f := _), LinearMap.add_apply]
      have h1 : (VS D).hT Ωγ y = 0 :=
        hyU _ (Submodule.span_mono (Set.range_comp_subset_range Sum.inr uu) hΩγ.1)
      have hXu : ∀ x ∈ Xsp (lf D F0), x ∈ Submodule.span D.host.E (Set.range uu) := by
        intro x hx
        refine Submodule.span_le.2 ?_ hx
        rintro _ ⟨i, rfl⟩
        exact Submodule.subset_span ⟨Sum.inl i.castSucc, by simp [huu, hf, frame, FlagG.fvec]⟩
      rw [h1, hyU _ (hXu _ hΩd), add_zero]
  have hkey : ∀ y y', (∀ k, (VS D).hT (uu k) y = 0) → (∀ k, (VS D).hT (uu k) y' = 0) →
      (VS D).hT (FsLA.lin ww (FsLA.pc ww y)) (FsLA.lin ww (FsLA.pc ww y')) = 0 :=
    fun y y' hy hy' => NMoveP.hT_X_X F0 (hXq y hy) (hXq y' hy')
  obtain ⟨β, hiso, hβu, hβy⟩ := BRat.isometry_extension_two uu uu' ww hGr hdet hdetw hsp hkey
  refine ⟨β, hiso, fun b => hβu (Sum.inr b), fun w0 hw0 => ?_, ?_⟩
  ·
    have hw0u : ∀ k, (VS D).hT (uu k) w0 = 0 := fun k =>
      (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hw0 _
        (PI.PairCorankPos.W.frame_mem_UUE γ.lam hΛ (lf D F0) (repF γ) hLlf hLrep k)
    refine ⟨β w0, ?_, ?_, by rw [sub_self]; exact zero_mem _⟩
    · refine (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).2 fun x hx => ?_
      have hxw : x ∈ Submodule.span D.host.E (Set.range ww) :=
        UUE_le_span Λ₂ (lf D F0) (liftF F'₂) rfl rfl hx
      rw [hβy w0 hw0u]
      exact (FsLA.hT_span_rem ww hdetw w0 x hxw).1
    · rw [hβy w0 hw0u, sub_sub_cancel]
      exact hXq w0 hw0u
  ·
    have homf : FsLA.om (VS D) F₂.fvec f = starOmL f (frame F'₂) := by
      rw [FsLA.om, hg2, ← Matrix.adjugate_conjTranspose]
      simp only [starOmL, Matrix.conjTranspose_apply]
      rw [← hZ]
      rfl
    have homh : FsLA.om (VS D) F₂.fvec h = β (starOmL f g) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [FsLA.om, starOmL, map_sum, map_smul]
      have e : FsLA.gram (VS D) h F₂.fvec = Z₁ᴴ := hZ3
      rw [e]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Matrix.adjugate_conjTranspose, Matrix.conjTranspose_apply]
      congr 1
      exact (hβu (Sum.inl a)).symm
    have e1 : Z₁ᴴ.det = star Z₁.det := Matrix.det_conjTranspose _
    have e2 : (FsLA.gram (VS D) f F₂.fvec).det = star Z.det := by rw [hg2, Matrix.det_conjTranspose]
    rw [e1, e2, homf, homh] at hom3
    have hD1 : GDl (frame (lf D F0)) (frame (repF γ)) (D.R.rS + 1) = Z₁.det := by rw [GDl_top']; rfl
    have hD2 : GDl (frame (lf D F0)) (frame (liftF F'₂)) (D.R.rS + 1) = Z.det := by
      rw [GDl_top']; rw [← hZ]; rfl
    have hO1 : Gom (frame (lf D F0)) (frame (repF γ)) = starOmL f g := rfl
    have hO2 : Gom (frame (lf D F0)) (frame (liftF F'₂)) = starOmL f (frame F'₂) := rfl
    unfold OmB
    rw [hD1, hD2, hO1, hO2]
    have := (Xsp (liftF F'₂)).neg_mem hom3
    rw [neg_sub] at this
    exact this

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
