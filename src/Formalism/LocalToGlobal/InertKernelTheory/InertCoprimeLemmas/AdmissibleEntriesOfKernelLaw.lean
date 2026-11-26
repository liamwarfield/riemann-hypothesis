module

public import Formalism.LocalToGlobal.InertKernelTheory.ThetaSeriesDataHypothesesBelowMaximalLevel
public import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.LatticeShapeMiddleHolds
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.FirstKernelLawGlobal

@[expose] public section

section -- merged from Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SecondKernelCoupled
section -- merged from Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SecondKernelInstances
noncomputable section

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Finset

namespace Formalism.L2.KerInert.SecondKernelInstances

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.KerInert.K2

section Gen

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc0 : G.Consts} {Dx : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc0 Dx cX}
variable {p : ℕ} [Fact p.Prime] {X : Sys p} {Y : Pend X} {u : D.what₂.Word} {μ : D.what₂.Tup}

theorem smul_one_tup (j : ℕ) (a : X.Lv.comp j) (L0 : (X.Pj j).Tup) : (X.Lv.lev j a).smul 1 L0 = L0 := by
  funext v
  ext z
  simp [Level.smul]

theorem clsBij_of (cls : ∀ j, X.Lv.comp j → (X.Pj j).Tup → (D.chTw u μ).cls j) (j : ℕ) (hjm : j ≤ X.mm)
    (hiff : ∀ (a a' : X.Lv.comp j) (L0 L1 : (X.Pj j).Tup), (X.Pj j).IsLatTup L0 → (X.Pj j).IsLatTup L1 →
      (cls j a L0 = cls j a' L1 ↔ a = a' ∧ ∃ γ : (X.Lv.lev j a).Γ, L1 = (X.Lv.lev j a).smul γ L0))
    (hsurj : ∀ x : (D.chTw u μ).cls j, ∃ a L0, (X.Pj j).IsLatTup L0 ∧ cls j a L0 = x) :
    ClsBij (Y := Y) u μ cls j := by
  constructor
  · rintro ⟨⟨a1, L1⟩, m1⟩ ⟨⟨a2, L2⟩, m2⟩ heq
    have hl1 := Y.Rep_lat j _ m1
    have hl2 := Y.Rep_lat j _ m2
    obtain ⟨rfl, γ, hγ⟩ := (hiff a1 a2 L1 L2 hl1 hl2).1 heq
    obtain ⟨L0, _, hu⟩ := Y.Rep_ex j hjm a1 L2 hl2
    have e1 : L1 = L0 := hu L1 ⟨m1, γ, hγ⟩
    have e2 : L2 = L0 := hu L2 ⟨m2, 1, (smul_one_tup j a1 L2).symm⟩
    subst e1
    subst e2
    rfl
  · intro x
    obtain ⟨a, L0, hL, hx⟩ := hsurj x
    obtain ⟨L1, ⟨hmem, γ, hγ⟩, _⟩ := Y.Rep_ex j hjm a L0 hL
    refine ⟨⟨(a, L1), hmem⟩, ?_⟩
    show cls j a L1 = x
    rw [← hx]
    exact (hiff a a L1 L0 (Y.Rep_lat j _ hmem) hL).2 ⟨rfl, γ, hγ⟩

theorem fq_le_span {σ : D.what₂.LL →+* X.G.Kf} (cmp : ∀ j, ((ex.tw.fm u μ).lat j).V →ₛₗ[σ] X.Fm j) (j : ℕ)
    (hint : Submodule.span X.G.O (cmp j '' (((ex.tw.fm u μ).lat j).L : Set ((ex.tw.fm u μ).lat j).V)) = X.Lv.Int j) :
    X.FQ j ≤ Submodule.span X.G.Kf (Set.range (cmp j)) := by
  have h1 : X.Lv.Int j ≤ (Submodule.span X.G.Kf (Set.range (cmp j))).restrictScalars X.G.O := by
    rw [← hint]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨x, _, rfl⟩
    exact Submodule.subset_span ⟨x, rfl⟩
  exact Submodule.span_le.2 fun z hz => h1 hz

theorem cmp_mem_fq {σ : D.what₂.LL →+* X.G.Kf} (cmp : ∀ j, ((ex.tw.fm u μ).lat j).V →ₛₗ[σ] X.Fm j) (j : ℕ)
    (hint : Submodule.span X.G.O (cmp j '' (((ex.tw.fm u μ).lat j).L : Set ((ex.tw.fm u μ).lat j).V)) = X.Lv.Int j)
    (y : ((ex.tw.fm u μ).lat j).V) : cmp j y ∈ X.FQ j := by
  have hy : y ∈ Submodule.span D.what₂.LL (((ex.tw.fm u μ).lat j).L : Set ((ex.tw.fm u μ).lat j).V) := by
    rw [((ex.tw.fm u μ).lat_good j).2.2]
    exact Submodule.mem_top
  induction hy using Submodule.span_induction with
  | mem z hz =>
    refine Submodule.subset_span ?_
    change cmp j z ∈ X.Lv.Int j
    rw [← hint]
    exact Submodule.subset_span (Set.mem_image_of_mem _ hz)
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul a b _ hb => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hb

theorem admissible_third_chain {σ : D.what₂.LL →+* X.G.Kf} (cmp : ∀ j, ((ex.tw.fm u μ).lat j).V →ₛₗ[σ] X.Fm j) (j : ℕ)
    (hint : Submodule.span X.G.O (cmp j '' (((ex.tw.fm u μ).lat j).L : Set ((ex.tw.fm u μ).lat j).V)) = X.Lv.Int j)
    (hint' : Submodule.span X.G.O (cmp (j + 1) '' (((ex.tw.fm u μ).lat (j + 1)).L : Set ((ex.tw.fm u μ).lat (j + 1)).V)) =
      X.Lv.Int (j + 1))
    (hrat : (ex.tw.fm u μ).KRat j)
    (hCh : ∀ (x : ((ex.tw.fm u μ).lat j).V) (y : ((ex.tw.fm u μ).lat (j + 1)).V),
      (ex.tw.fm u μ).emb (j + 1) y = (D.chTw u μ).K j ((ex.tw.fm u μ).emb j x) → X.Kz j (cmp j x) = cmp (j + 1) y)
    (F : X.Fm j) (hF : F ∈ X.FQ j) : X.Kz j F ∈ X.FQ (j + 1) := by
  have hs := fq_le_span cmp j hint hF
  clear hF
  induction hs using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, rfl⟩ := hz
    obtain ⟨y, hy⟩ := hrat x
    rw [hCh x y hy]
    exact cmp_mem_fq cmp (j + 1) hint' y
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul a b _ hb => rw [map_smul]; exact Submodule.smul_mem _ a hb

theorem second_kernel_at_place (t : KerEntTied ex) {σ : D.what₂.LL →+* X.G.Kf} (cls : ∀ j, X.Lv.comp j → (X.Pj j).Tup → (D.chTw u μ).cls j)
    (cmp : ∀ j, ((ex.tw.fm u μ).lat j).V →ₛₗ[σ] X.Fm j) (ι : ℂ →+* Y.Kc)
    (Rd : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup →
      ((D.chTw u μ).cls (j + 1) → (D.chTw u μ).Y (j + 1) → ℂ) →ₛₗ[ι] XspC (X.Pj (j + 1)) Y.Kc)
    (Sr : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) Y.Kc) (j : ℕ) (hj : j < D.R.m)
    (hspan : X.FQ j ≤ Submodule.span X.G.Kf (Set.range (cmp j))) (hrat : (ex.tw.fm u μ).KRat j)
    (hCh : ∀ (x : ((ex.tw.fm u μ).lat j).V) (y : ((ex.tw.fm u μ).lat (j + 1)).V),
      (ex.tw.fm u μ).emb (j + 1) y = (D.chTw u μ).K j ((ex.tw.fm u μ).emb j x) → X.Kz j (cmp j x) = cmp (j + 1) y)
    (hbij : ClsBij (Y := Y) u μ cls j) (hT : TiesAt t u μ cls cmp ι Rd Sr j) : SecondKernelAtLevel X Y j := by
  obtain ⟨hSh, hSt, hRd, hSer, cK, h1, h2, h3, hDel⟩ := hT
  refine ⟨cK, h1, h2, h3, ?_⟩
  intro F hF
  refine body_of_span Y j cK (Set.range (cmp j)) ?_ F (hspan hF)
  rintro _ ⟨x, rfl⟩ c' L' hL
  obtain ⟨y, hy⟩ := hrat x
  have hsum : (D.chTw u μ).K j ((ex.tw.fm u μ).emb j x) =
      ∑ c : (D.chTw u μ).cls j, (((Nat.card ((D.chTw u μ).stab j c) : ℕ) : ℂ))⁻¹ • entRec t ex.tw u μ j c x := by
    have hQ := sharpQ_qOf (hSh x)
    funext c1 y1
    rw [compatible_lift_exists D L hT Gi Gl Kc0 Dx cX ex t u μ j hj _ _ hQ.1 hQ.2 c1 y1]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, entRec]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hCh x y hy, hRd y c' L' hL, hy, hsum, map_sum]
  rw [← Finset.sum_coe_sort (Y.Rep j)]
  symm
  refine Fintype.sum_bijective _ hbij _ _ fun La => ?_
  rw [map_smulₛₗ, map_inv₀, map_natCast, hSt La.1 La.2, hDel La.1 La.2 x c' L' hL,
    kernel_of_smul p X Y j La.1 (c', L') _ (hSer La.1 La.2 c' L' hL), mul_smul]

end Gen

theorem class_bijection_instance : ClsBijInst := by
  intro D L hT Gi Gl Kc0 Dx cX ex u μ w h _ Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om Y j hj
  exact clsBij_of (X := sysAt Ch std vp unif eO eO_spec dG dG_spec om) KA.cls j (hj.trans_eq KA.fl_m.symm)
    (fun a a' L0 L1 h0 h1 => KA.cls_iff j hj a a' L0 L1 h0 h1) (KA.cls_surj j hj)

theorem admissible_third_instance : Adm3bInst := by
  intro D L hT Gi Gl Kc0 Dx cX ex u μ w h _ Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om j hj F hF
  have hjm : j < D.R.m := lt_of_lt_of_eq hj KA.fl_m
  exact admissible_third_chain (X := sysAt Ch std vp unif eO eO_spec dG dG_spec om) KA.cmp j (KA.cmp_int j hjm.le)
    (KA.cmp_int (j + 1) hjm) (KA.rat j hjm) (fun x y hy => (KA.cmp_K j hjm x y hy).symm) F hF

theorem second_kernel_chain_instance : SecondKernelSingleLevel := by
  intro D L hT Gi Gl Kc0 Dx cX ex t u μ w h _ Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om Y ι Rd Sr j hj hTs
  have hsp := fq_le_span (X := sysAt Ch std vp unif eO eO_spec dG dG_spec om) KA.cmp j (KA.cmp_int j hj.le)
  have hch : ∀ (x : ((ex.tw.fm u μ).lat j).V) (y : ((ex.tw.fm u μ).lat (j + 1)).V),
      (ex.tw.fm u μ).emb (j + 1) y = (D.chTw u μ).K j ((ex.tw.fm u μ).emb j x) →
      (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Kz j (KA.cmp j x) = KA.cmp (j + 1) y :=
    fun x y hy => (KA.cmp_K j hj x y hy).symm
  have hb : ClsBij (X := sysAt Ch std vp unif eO eO_spec dG dG_spec om) (Y := Y) u μ KA.cls j :=
    class_bijection_instance D L hT Gi Gl Kc0 Dx cX ex u μ w h Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om Y j hj.le
  exact second_kernel_at_place (X := sysAt Ch std vp unif eO eO_spec dG dG_spec om) (Y := Y) (σ := ex.cmp.embW u w h) t KA.cls KA.cmp ι Rd Sr
    j hj hsp (KA.rat j hj) hch hb hTs

theorem second_kernel_entry_instance : SecondKernelEntrywise := by
  intro D L hT Gi Gl Kc0 Dx cX ex t u μ w h _ Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om Y ι Rd Sr hTs j hj
  exact second_kernel_chain_instance D L hT Gi Gl Kc0 Dx cX ex t u μ w h Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om Y ι Rd Sr j
    (by omega) (hTs j hj)

end Formalism.L2.KerInert.SecondKernelInstances
end
end

noncomputable section

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Finset

namespace Formalism.L2.KerInert.SecondKernelCoupled

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.KerInert.K2 Formalism.L2.KerInert.SecondKernelInstances

section Gen

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc0 : G.Consts} {Dx : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc0 Dx cX}
variable {p : ℕ} [Fact p.Prime] {X : Sys p} {Y : Pend X} {u : D.what₂.Word} {μ : D.what₂.Tup}

theorem bodyC_of_span (Y : Pend X) (j : ℕ) (cK : Y.Kc) {I : Type} [Fintype I] (wt : I → Y.Kc) (La : I → X.Lt j)
    (S : Set (X.Fm j))
    (hS : ∀ F ∈ S, ∀ (c' : X.Lv.comp (j + 1)) (L' : (X.Pj (j + 1)).Tup), (X.Pj (j + 1)).IsLatTup L' →
      MvPolynomial.map (algebraMap X.G.Kf Y.Kc) (X.Kz j F c' L') =
        ∑ x : I, (wt x * cK) • Y.ker j (La x) (c', L') (F (La x).1 (La x).2))
    (F : X.Fm j) (hF : F ∈ Submodule.span X.G.Kf S) :
    ∀ (c' : X.Lv.comp (j + 1)) (L' : (X.Pj (j + 1)).Tup), (X.Pj (j + 1)).IsLatTup L' →
      MvPolynomial.map (algebraMap X.G.Kf Y.Kc) (X.Kz j F c' L') =
        ∑ x : I, (wt x * cK) • Y.ker j (La x) (c', L') (F (La x).1 (La x).2) := by
  induction hF using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero =>
    intro c' L' _
    simp only [map_zero, Pi.zero_apply, ker_zero, smul_zero, Finset.sum_const_zero]
  | add x y _ _ hx hy =>
    intro c' L' hL
    simp only [map_add (f := _), Pi.add_apply, ker_add, smul_add, Finset.sum_add_distrib, hx c' L' hL, hy c' L' hL]
  | smul a x _ hx =>
    intro c' L' hL
    simp only [map_smul, Pi.smul_apply, ker_smul]
    rw [map_smul_Kf Y, hx c' L' hL, Finset.smul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [smul_comm]

theorem second_kernel_coupled (t : KerEntTied ex) {σ : D.what₂.LL →+* X.G.Kf} (cmp : ∀ j, ((ex.tw.fm u μ).lat j).V →ₛₗ[σ] X.Fm j)
    (ι : ℂ →+* Y.Kc)
    (Rd : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup →
      ((D.chTw u μ).cls (j + 1) → (D.chTw u μ).Y (j + 1) → ℂ) →ₛₗ[ι] XspC (X.Pj (j + 1)) Y.Kc)
    (Sr : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) Y.Kc) (j : ℕ) (hj : j < D.R.m)
    (lp : (D.chTw u μ).cls j → X.Lt j)
    (hspan : X.FQ j ≤ Submodule.span X.G.Kf (Set.range (cmp j))) (hrat : (ex.tw.fm u μ).KRat j)
    (hCh : ∀ (x : ((ex.tw.fm u μ).lat j).V) (y : ((ex.tw.fm u μ).lat (j + 1)).V),
      (ex.tw.fm u μ).emb (j + 1) y = (D.chTw u μ).K j ((ex.tw.fm u μ).emb j x) → X.Kz j (cmp j x) = cmp (j + 1) y)
    (hT : TiesC Y t u μ cmp ι Rd Sr j lp) (hH : HeckeC Y u μ j lp) : ExpansionDecomposition D X Y j := by
  obtain ⟨hSh, hRd, hLat, hDG, hSer, cK, h1, h2, _, hDel⟩ := hT
  have body := bodyC_of_span Y j cK (fun x : (D.chTw u μ).cls j => (((Nat.card ((D.chTw u μ).stab j x) : ℕ) : Y.Kc))⁻¹) lp
    (Set.range (cmp j)) (by
      rintro _ ⟨x, rfl⟩ c' L' hL
      obtain ⟨y, hy⟩ := hrat x
      have hsum : (D.chTw u μ).K j ((ex.tw.fm u μ).emb j x) =
          ∑ c : (D.chTw u μ).cls j, (((Nat.card ((D.chTw u μ).stab j c) : ℕ) : ℂ))⁻¹ • entRec t ex.tw u μ j c x := by
        have hQ := sharpQ_qOf (hSh x)
        funext c1 y1
        rw [compatible_lift_exists D L hT Gi Gl Kc0 Dx cX ex t u μ j hj _ _ hQ.1 hQ.2 c1 y1]
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, entRec]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hCh x y hy, hRd y c' L' hL, hy, hsum, map_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [map_smulₛₗ, map_inv₀, map_natCast, hDel c x c' L' hL,
        kernel_of_smul p X Y j (lp c) (c', L') _ (hSer c c' L' hL), mul_smul])
  refine ⟨cK, h1, h2, (D.chTw u μ).cls j, Unit, inferInstance, inferInstance,
    fun x => Nat.card ((D.chTw u μ).stab j x), fun x _ => lp x, fun x _ => hLat x,
    fun x => ⟨Nat.card_pos, hDG x⟩, ?_, ?_⟩
  · intro F hF c' L' hL
    simpa only [Finset.univ_unique, Finset.sum_singleton] using body F (hspan hF) c' L' hL
  · intro v i F hF La' hLa'
    simpa only [Finset.univ_unique, Finset.sum_singleton] using hH v i F hF La' hLa'

end Gen

theorem second_kernel_coupled_instance : SecondKernelCoupledLastLift := by
  intro D L hT Gi Gl Kc0 Dx cX ex t u μ w h _ Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om Y ι Rd Sr lp hm hTs hH
  have hj : D.R.m - 1 < D.R.m := by omega
  have hsp := fq_le_span (X := sysAt Ch std vp unif eO eO_spec dG dG_spec om) KA.cmp (D.R.m - 1) (KA.cmp_int (D.R.m - 1) hj.le)
  have hch : ∀ (x : ((ex.tw.fm u μ).lat (D.R.m - 1)).V) (y : ((ex.tw.fm u μ).lat (D.R.m - 1 + 1)).V),
      (ex.tw.fm u μ).emb (D.R.m - 1 + 1) y = (D.chTw u μ).K (D.R.m - 1) ((ex.tw.fm u μ).emb (D.R.m - 1) x) →
      (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Kz (D.R.m - 1) (KA.cmp (D.R.m - 1) x) = KA.cmp (D.R.m - 1 + 1) y :=
    fun x y hy => (KA.cmp_K (D.R.m - 1) hj x y hy).symm
  exact second_kernel_coupled (X := sysAt Ch std vp unif eO eO_spec dG dG_spec om) (Y := Y) (σ := ex.cmp.embW u w h) t KA.cmp ι Rd Sr
    (D.R.m - 1) hj lp hsp (KA.rat (D.R.m - 1) hj) hch hTs hH

theorem admissible_fourth_instance : Adm4NewInst := by
  intro D L hT Gi Gl Kc0 Dx cX ex t u μ w h _ Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om Y ι Rd Sr lp hE hL
  have hmm : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).mm = D.R.m := KA.fl_m
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · have hl : j + 1 < D.R.m := by omega
    obtain ⟨cK, h1, h2, _, hb⟩ :=
      second_kernel_entry_instance D L hT Gi Gl Kc0 Dx cX ex t u μ w h Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om Y ι Rd Sr hE j hl
    exact ⟨cK, h1, h2, hb⟩
  · have hm : 0 < D.R.m := by omega
    obtain rfl : j = D.R.m - 1 := by omega
    obtain ⟨hT1, hH1⟩ := hL hm
    exact second_kernel_coupled_instance D L hT Gi Gl Kc0 Dx cX ex t u μ w h Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om Y ι Rd Sr lp
      hm hT1 hH1

theorem hecke_coupled_entry : HeckeCEntry := by
  intro D L hT Gi Gl Kc0 Dx cX ex u μ w h _ Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om Y lp hm h5b hsec hst
    v i F hF La' hLa'
  have hj : D.R.m - 1 < (sysAt Ch std vp unif eO eO_spec dG dG_spec om).mm :=
    lt_of_lt_of_eq (by omega : D.R.m - 1 < D.R.m) KA.fl_m.symm
  let X := sysAt Ch std vp unif eO eO_spec dG dG_spec om
  letI := X.G.ringO
  letI := X.G.domO
  letI := X.G.dvrO
  letI := X.G.fieldK
  letI := X.G.algOK
  letI := Y.algKf
  have h6 := Formalism.L2.G.Pend.up_down_adjoint D _ Y
  have hk0 (j : ℕ) (hj : j < X.mm) (v : X.Pl) (k : ℕ)
      (F : X.Fm j) (hF : F ∈ X.FQ j) (La' : X.Lt (j + 1)) (hLa' : (X.Pj (j + 1)).IsLatTup La'.2) :
      ∑ La ∈ Y.Rep j, ((X.stab j La : X.G.Kf))⁻¹ •
        ∑ A1 ∈ Pf.UP (X.Pj j) (X.vJ j v) k (La.2 (X.vJ j v)),
          Y.ker j (La.1, Function.update La.2 (X.vJ j v) A1) La' (F La.1 La.2) =
      ∑ La ∈ Y.Rep j, ((X.stab j La : X.G.Kf))⁻¹ • Y.ker j La La' (X.Tm v k j F La.1 La.2) := by
    open Formalism.MainNotions.FormalGroupSystem.Pf Formalism.MainNotions.G.LatticeSystems in
    classical
    apply MvPolynomial.ext
    intro n
    let φ : X.Lv.comp j → (X.Pj j).Tup → (X.Pj j).Tup → Y.Kc := fun c L L1 =>
      if (X.Pj j).IsLatTup L1 then AddMonoidAlgebra.coeff (Y.ker j (c, L1) La' (F c L)) n else 0
    have hφ : ∀ c (γ : (X.Lv.lev j c).Γ) L L1,
        φ c ((X.Lv.lev j c).smul γ L) ((X.Lv.lev j c).smul γ L1) = φ c L L1 := by
      intro c γ L L1
      simp only [φ]
      by_cases h : (X.Pj j).IsLatTup L1
      · rw [if_pos h, if_pos ((latTup_smul _ _ γ L1).2 h), (Eqv_of_FQ X hF).2 c γ L,
          h5b j hj c L1 La' γ (F c L) (vt_FQ X hF c L) h hLa']
      · rw [if_neg h, if_neg (fun h' => h ((latTup_smul _ _ γ L1).1 h'))]
    have key := h6 j hj.le (X.vJ j v) k φ hφ
    have hs : ∀ (La : X.Lt j) (z : Y.Kc), ((X.stab j La : X.G.Kf))⁻¹ • z = ((X.stab j La : Y.Kc))⁻¹ * z := by
      intro La z
      rw [Algebra.smul_def, map_inv₀, map_natCast]
    rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_sum]
    refine Eq.trans ?_ (key.trans ?_)
    · refine Finset.sum_congr rfl fun La hLa => ?_
      have hlat := Y.Rep_lat j La hLa
      rw [MvPolynomial.coeff_smul, hs, MvPolynomial.coeff_sum]
      congr 1
      refine Eq.trans ?_ (finsum_mem_eq_finite_toFinset_sum _ (up_fin (X.Pj j) (X.vJ j v) k (La.2 (X.vJ j v)))).symm
      refine Finset.sum_congr rfl fun A1 hA1 => ?_
      have hE := (mem_UP _).1 hA1
      simp only [φ]
      rw [if_pos (hk_latTup_update _ hlat _ A1 hE.2.1)]
    · refine Finset.sum_congr rfl fun La hLa => ?_
      have hlat := Y.Rep_lat j La hLa
      rw [MvPolynomial.coeff_smul, hs]
      congr 1
      refine Eq.trans (finsum_mem_eq_finite_toFinset_sum _ (edges_fin (X.Pj j) (X.vJ j v) k (La.2 (X.vJ j v)))) ?_
      have e : X.Tm v k j F La.1 La.2 = ∑ L0 ∈ EE (X.Pj j) (X.vJ j v) k (La.2 (X.vJ j v)),
          F La.1 (Function.update La.2 (X.vJ j v) L0) := Tminus_eq (X.Pj j) (X.vJ j v) k (F La.1) La.2
      rw [e, ker_sum, MvPolynomial.coeff_sum]
      refine Finset.sum_congr rfl fun L0 _ => ?_
      simp only [φ]
      rw [if_pos hlat]
  have hk := hk0 (D.R.m - 1) hj v i F hF La' hLa'
  have hs : ∀ (n : ℕ) (z : XspC (X.Pj (D.R.m - 1 + 1)) Y.Kc), ((n : X.G.Kf))⁻¹ • z = ((n : Y.Kc))⁻¹ • z := by
    intro n z
    rw [← algebraMap_smul Y.Kc ((n : X.G.Kf))⁻¹ z, map_inv₀, map_natCast]
  simp only [hs] at hk
  have hk := ((Finset.sum_coe_sort (Y.Rep (D.R.m - 1)) _).trans hk).trans (Finset.sum_coe_sort (Y.Rep (D.R.m - 1)) _).symm
  simp only [Pf.up_finsum]
  have hb : ClsBij (Y := Y) u μ KA.cls (D.R.m - 1) :=
    class_bijection_instance D L hT Gi Gl Kc0 Dx cX ex u μ w h Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om Y (D.R.m - 1)
      (by omega)
  have hbij : Function.Bijective fun x : (D.chTw u μ).cls (D.R.m - 1) =>
      (⟨lp x, (hsec x).1⟩ : {La // La ∈ Y.Rep (D.R.m - 1)}) := by
    constructor
    · intro x1 x2 he
      have h1 := (hsec x1).2
      have h2 := (hsec x2).2
      have : lp x1 = lp x2 := congrArg Subtype.val he
      rw [← h1, ← h2, this]
    · intro La
      refine ⟨KA.cls (D.R.m - 1) La.1.1 La.1.2, ?_⟩
      apply hb.1
      show KA.cls (D.R.m - 1) (lp _).1 (lp _).2 = KA.cls (D.R.m - 1) La.1.1 La.1.2
      exact (hsec _).2
  have hw : ∀ x : (D.chTw u μ).cls (D.R.m - 1),
      Nat.card ((D.chTw u μ).stab (D.R.m - 1) x) = (sysAt Ch std vp unif eO eO_spec dG dG_spec om).stab (D.R.m - 1) (lp x) := by
    intro x
    have e := hst (lp x) (hsec x).1
    rw [(hsec x).2] at e
    exact e
  refine (Fintype.sum_bijective _ hbij _ _ fun x => ?_).trans (hk.trans (Fintype.sum_bijective _ hbij _ _ fun x => ?_).symm)
  · simp only [hw x]
    rfl
  · simp only [hw x]
    rfl

theorem coupled_compatibility_at_place : TiesCOfAt := by
  intro D L hT Gi Gl Kc0 Dx cX ex t u μ w h _ Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om Y ι Rd Sr lp hm hsec hTs
  obtain ⟨hSh, hSt, hRd, hSer, cK, h1, h2, h3, hDel⟩ := hTs
  refine ⟨hSh, hRd, fun x => Y.Rep_lat _ _ (hsec x).1, fun x => ?_, fun x c' L' hL => hSer (lp x) (hsec x).1 c' L' hL,
    cK, h1, h2, h3, fun x y c' L' hL => ?_⟩
  · have e := hSt (lp x) (hsec x).1
    rw [(hsec x).2] at e
    rw [e]
    exact dG_spec (D.R.m - 1) (by have := KA.fl_m; omega) (lp x).1 (lp x).2 (Y.Rep_lat _ _ (hsec x).1)
  · have e := hDel (lp x) (hsec x).1 y c' L' hL
    rw [(hsec x).2] at e
    exact e

theorem coupled_section_exists : SecCEx := by
  intro D L hT Gi Gl Kc0 Dx cX ex u μ w h _ Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om Y hm
  have hb : ClsBij (Y := Y) u μ KA.cls (D.R.m - 1) :=
    class_bijection_instance D L hT Gi Gl Kc0 Dx cX ex u μ w h Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om Y (D.R.m - 1)
      (by omega)
  refine ⟨fun x => (Function.surjInv hb.2 x).1, fun x => ⟨(Function.surjInv hb.2 x).2, ?_⟩⟩
  exact Function.surjInv_eq hb.2 x

end Formalism.L2.KerInert.SecondKernelCoupled
end
end

section -- merged from Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.FirstKernelSmallOfFrameTwist
section -- merged from Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.K1RepresentativesLTOfDictionary
noncomputable section

open scoped Matrix

namespace Formalism.L2.KerInert.RepLt

open Formalism.MainNotions.FormalGroupSystem Formalism.L2.KerInert.RepFrame Formalism.L2.KerInert.RepTwLat
open Formalism.L2.G.Pend (Frm)
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

section Lat

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7)
  (M : ∀ j, X.Lt j → ∀ v : X.Pl, Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))
  (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
  (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))

end Lat

section Int

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : Formalism.L2.G.Pend.CEmbC X.G)
  (M : ∀ j, X.Lt j → ∀ v : X.Pl, Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))
  (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7)
  (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
  (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))

theorem frameIntLt_of (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v) (hM : MInv X M) (hT : TwInt X E)
    (hL : FrameLatMapLt X M hfin D large₂ Lg' ρ) : FrameIntLt X E hfin D large₂ Lg' M ρ := by
  intro j hj L0 hL0 La' hLa' φ r b hb ho i v s b0 a0
  obtain ⟨h1, h2⟩ := hL j hj L0 hL0 La' hLa' φ r b hb ho i v
  constructor
  · obtain ⟨w, hw⟩ := entry_int (W := X.G.P.W v) (Gm X M φ v) (Gmi X M φ v) (Gmi_mul_Gm X M φ (hM j L0) v)
      ((b i).map (fun y => ρ v (D.host.conj y)))ᵀ (Gp X M φ v) h2 a0 b0
    have e1 : ∑ B, ∑ A, ρ v (D.host.conj (b i B A)) * Gp X M φ v B b0 * Gmi X M φ v a0 A =
        (Gmi X M φ v * ((b i).map (fun y => ρ v (D.host.conj y)))ᵀ * Gp X M φ v) a0 b0 := by
      rw [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun B _ => ?_
      rw [Matrix.mul_apply, Finset.sum_mul]
      refine Finset.sum_congr rfl fun A _ => ?_
      simp only [Matrix.transpose_apply, Matrix.map_apply]
      ring
    rw [e1, hw]
    exact hT v s w
  · obtain ⟨w, hw⟩ := entry_int (W := X.G.P.W v) (Gp X M φ v) (Gpi X M φ v) (Gpi_mul_Gp X M φ (hM (j + 1) La') v)
      ((b i).map (ρ v)) (Gm X M φ v) h1 b0 a0
    have e1 : ∑ B, ∑ A, ρ v (b i B A) * Gm X M φ v A a0 * Gpi X M φ v b0 B =
        (Gpi X M φ v * (b i).map (ρ v) * Gm X M φ v) b0 a0 := by
      rw [Matrix.mul_apply, Finset.sum_comm]
      refine Finset.sum_congr rfl fun B _ => ?_
      rw [Matrix.mul_apply, Finset.sum_mul]
      refine Finset.sum_congr rfl fun A _ => ?_
      simp only [Matrix.map_apply]
      ring
    rw [e1, hw]
    exact hT v s w

end Int

end Formalism.L2.KerInert.RepLt

namespace Formalism.L2.KerInert.RepLt

open Formalism.MainNotions.FormalGroupSystem Formalism.L2.Th1.D Formalism.L2.Th1.Top Formalism.L2.KerInert.K1 Formalism.L2.KerInert.RepFrame
open Formalism.InvariantFactorPaths.G7 (UnrOK)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.G.Pend (Frm)
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : Formalism.L2.G.Pend.CEmbC X.G)
  (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)
  (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
  (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))
  (M : ∀ j, X.Lt j → ∀ v : X.Pl, Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))

theorem hypCoordLt_of (lam : Qbar →+* ℂ_[p]) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v)
    (hT : LamTraceLt X hfin D large₂ Lg' lam) (hρ : LamPosG X E D pos lam ρ) (hF : FrobTw X E)
    (hev : ∀ v, Even (X.G.P.n' v)) (hconj : ∀ x, D.host.conj (D.host.conj x) = x) (hM : MInv X M)
    (hI : FrameIntLt X E hfin D large₂ Lg' M ρ) :
    HypCoordLt X E hfin D pos large₂ Lg' M lam 1 := by
  intro j hj L0 hL0 La' hLa' r b hb ho φ
  obtain ⟨σ, twK, wK, hσ, htwK, hσtw, hwK, hσw, hwn⟩ := hF
  have hL := hT j hj L0 hL0 La' hLa' r b hb ho
  have hH : IsHypPair σ (fK X D M φ b ρ twK wK) (fK' X D M φ b ρ twK wK) := by
    unfold IsHypPair
    refine ⟨fun e i => ⟨?_, ?_⟩, fun e i => ⟨?_, ?_⟩, fun e e' => ?_, fun e e' => ?_, fun e e' => ?_⟩
    · exact norm_fK X E D M φ b ρ twK wK htwK hwn
        (fun i v s b0 a0 => (hI j hj L0 hL0 La' hLa' φ r b hb ho i v s b0 a0).1) e i
    · exact sigma2_fK X D M φ b ρ twK wK σ hσtw hσw hev hconj e i
    · exact norm_fK' X E D M φ b ρ twK wK htwK hconj hwn
        (fun i v s b1 a1 => (hI j hj L0 hL0 La' hLa' φ r b hb ho i v s b1 a1).2) e i
    · exact sigma2_fK' X D M φ b ρ twK wK σ hσtw hσw hev hconj e i
    · exact iso_fK X E D pos lam M φ b ρ twK wK hρ htwK σ hσtw hσw hev hconj hL e e'
    · exact iso_fK' X E D pos lam M φ b ρ twK wK hρ htwK σ hσtw hσw hev hconj hL e e'
    · rw [dual_fK X E D pos lam M φ b ρ twK wK hρ htwK σ hσtw hσw hev hconj hL (hM j L0) (hM (j + 1) La') e e']
  refine ⟨σ, fK X D M φ b ρ twK wK, fK' X D M φ b ρ twK wK, hσ, hH, fun e i => ?_, fun e i => ?_⟩
  · rw [inv_one, one_mul]
    exact coe_fK X E D pos lam M φ b ρ twK wK hρ htwK hwK e i
  · rw [inv_one, one_mul]
    exact coe_fK' X E D pos lam M φ b ρ twK wK hρ htwK hwK hconj e i

theorem frameStdLt_of (lam : Qbar →+* ℂ_[p]) (c : ℂ_[p]) (hc0 : c ≠ 0) (h1 : OnbExLt X hfin D large₂ Lg')
    (h2 : LamTraceLt X hfin D large₂ Lg' lam) (h3 : HypCoordLt X E hfin D pos large₂ Lg' M lam c) :
    FrameStdLt X E hfin D pos large₂ Lg' M lam c := by
  intro j hj L0 hL0 La' hLa' φ
  obtain ⟨r, b, hb, ho⟩ := h1 j hj L0 hL0 La' hLa'
  obtain ⟨σ, f, f', hσ, hH, hf, hf'⟩ := h3 j hj L0 hL0 La' hLa' r b hb ho φ
  have hL := h2 j hj L0 hL0 La' hLa' r b hb ho
  refine ⟨r, b, hb, ho, σ, f, f', hσ, hH, fun k => ?_⟩
  rw [(isLin_stdLin X E pos M φ k).repr, Fintype.sum_sum_type]
  simp only [hypLin, Finset.mul_sum, mul_add, Finset.sum_add_distrib]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun i e => MvPowerSeries.C (c * lamC lam (embT D k.1 (b i k.2.1 k.2.2))) *
        (MvPowerSeries.C (f e i : ℂ_[p]) * MvPowerSeries.X (Sum.inl e))),
    Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun i e => MvPowerSeries.C (c * lamC lam (embT D k.1 (b i k.2.1 k.2.2))) *
        (MvPowerSeries.C (f' e i : ℂ_[p]) * MvPowerSeries.X (Sum.inr e)))]
  congr 1
  · refine Finset.sum_congr rfl fun e _ => ?_
    simp only [← mul_assoc, ← map_mul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Finset.sum_mul, ← map_sum]
    congr 2
    simp only [hf]
    exact (coord_recon D lam b hL hc0 (fun k' => frVec X E pos M φ (Sum.inl e) k') k).symm
  · refine Finset.sum_congr rfl fun e _ => ?_
    simp only [← mul_assoc, ← map_mul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Finset.sum_mul, ← map_sum]
    congr 2
    simp only [hf']
    exact (coord_recon D lam b hL hc0 (fun k' => frVec X E pos M φ (Sum.inr e) k') k).symm

theorem frameLinLt_of_std (lam : Qbar →+* ℂ_[p]) (c : ℂ_[p]) (h : FrameStdLt X E hfin D pos large₂ Lg' M lam c) :
    FrameLinLt X E hfin D pos large₂ Lg' (fun j La La' => subGen X E pos M j La La') lam c := by
  intro j hj L0 hL0 La' hLa' φ
  obtain ⟨r, b, hb, ho, σ, f, f', hσ, hH, hk⟩ := h j hj L0 hL0 La' hLa' φ
  exact ⟨r, b, hb, ho, σ, f, f', hσ, hH, fun k => (linFrame_subGen X E pos M φ k).trans (hk k)⟩

theorem frameHypLt_of_lin (S : ∀ j, X.Lt j → X.Lt (j + 1) →
      (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) →
      (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) → ℂ_[p])
    (lam : Qbar →+* ℂ_[p]) (c : ℂ_[p]) (h : FrameLinLt X E hfin D pos large₂ Lg' S lam c)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) →
      MvPowerSeries (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p]) :
    FrameHypLt X E hfin D pos large₂ Lg' F S lam c := by
  intro j hj L0 hL0 La' hLa' φ
  obtain ⟨r, b, hb, ho, σ, f, f', hσ, hH, hk⟩ := h j hj L0 hL0 La' hLa' φ
  refine ⟨r, b, hb, ho, σ, f, f', hσ, hH, ?_⟩
  rw [thA_thFOf_linSub X E pos φ S F, subst_hypLin_thOrth]
  congr 1
  funext k
  exact hk k

theorem onbExLt_of (hO : Formalism.L2.KerInert.OrthBasisExists) (h5 : 5 ≤ p) (hin : jacobiSym (-(D.host.d : ℤ)) p = -1)
    (hadm : ∀ j, j < X.mm → ∀ (L0 : X.Lt j), L0 ∈ Formalism.L2.G.Pend.repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1),
      (X.Pj (j + 1)).IsLatTup La'.2 → admitted D _ _ (large₂ j L0 La') (Lg' j L0 La')) :
    OnbExLt X hfin D large₂ Lg' :=
  fun j hj L0 hL0 La' hLa' => hO D p h5 hin _ _ _ _ (hadm j hj L0 hL0 La' hLa')

theorem rankTieLt_of (hadm : ∀ j, j < X.mm → ∀ (L0 : X.Lt j), L0 ∈ Formalism.L2.G.Pend.repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1),
      (X.Pj (j + 1)).IsLatTup La'.2 → admitted D _ _ (large₂ j L0 La') (Lg' j L0 La')) :
    RankTieLt X hfin D large₂ Lg' :=
  fun j hj L0 hL0 La' hLa' _ b hb =>
    rank_of_locBasis _ _ (hadm j hj L0 hL0 La' hLa').2.2.1 (hadm j hj L0 hL0 La' hLa').2.2.2 b hb

theorem lamTraceLt_of (lam : Qbar →+* ℂ_[p]) (h1 : RankTieLt X hfin D large₂ Lg') (h2 : ColTie X hfin D large₂ Lg' lam) :
    LamTraceLt X hfin D large₂ Lg' lam :=
  fun j hj L0 hL0 La' hLa' r b hb ho =>
    lamONB_of_cols D lam b (h1 j hj L0 hL0 La' hLa' r b hb) (h2 j L0 hL0 La' hLa' r b hb ho)

theorem frameHypLt_of_lat (lam : Qbar →+* ℂ_[p]) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v)
    (h1 : OnbExLt X hfin D large₂ Lg') (hT : LamTraceLt X hfin D large₂ Lg' lam) (hρ : LamPosG X E D pos lam ρ)
    (hF : FrobTw X E) (hM : MInv X M) (hTw : TwInt X E) (hL : FrameLatMapLt X M hfin D large₂ Lg' ρ)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) →
      MvPowerSeries (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p]) :
    FrameHypLt X E hfin D pos large₂ Lg' F (fun j La La' => subGen X E pos M j La La') lam 1 :=
  frameHypLt_of_lin X E hfin D pos large₂ Lg' _ lam 1
    (frameLinLt_of_std X E hfin D pos large₂ Lg' M lam 1
      (frameStdLt_of X E hfin D pos large₂ Lg' M lam 1 one_ne_zero h1 hT
        (hypCoordLt_of X E hfin D pos large₂ Lg' M lam ρ hT hρ hF (fun v => (X.G.P.setting v).even) (conj_conj D) hM
          (frameIntLt_of X E M hfin D large₂ Lg' ρ hM hTw hL)))) F

end Formalism.L2.KerInert.RepLt

namespace Formalism.L2.KerInert.RepLt

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H Formalism.L2.KerInert.RepComb

theorem combAtLt_of_dataRec {p : ℕ} [Fact p.Prime] (X : Formalism.MainNotions.FormalGroupSystem.Sys p) [IsFractionRing X.G.O X.G.Kf]
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ)
    (χ : TaylorLogMetric.IdE D → ℂ) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ) (lam : TaylorLogMetric.Qbar →+* ℂ_[p])
    (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hAlg : B.AlgT χ)
    (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
    (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))
    (Ξ : ∀ j, X.Lt j → X.Lt (j + 1) → Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ)
    (hD : Formalism.L2.KerInert.RepRec.DataRec X D cl Ξ)
    (hA : ∀ j, j < X.mm → ∀ (L0 : X.Lt j), L0 ∈ Formalism.L2.G.Pend.repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1),
      (X.Pj (j + 1)).IsLatTup La'.2 → TaylorLogMetric.admitted D _ _ (large₂ j L0 La') (Lg' j L0 La')) :
    CombAtLt X hfin D large₂ Lg'
      (fun j La La' => Formalism.L2.PairingIndexBounds.F.serP lam (Formalism.L2.PairingIndexBounds.F.kerTh B χ SS cl (large₂ j La La') (Lg' j La La') (Ξ j La La')))
      B.tor (B.eNat χ) lam := by
  obtain ⟨S, hS, hpS, hΞ⟩ := hD
  have hTA : TransAlg D B.tor (B.eNat χ) :=
    transcendence_algebraic_eigen D cc δ B χ hcc hδ (KS.Lat.delta_ne hcc hδ) (B.stdOK hcc hδ) hAlg
  intro j hj L0 h0 La' hL'
  have h := hA j hj L0 h0 La' hL'
  exact ⟨h, combined_kernel_twisted D cc δ B χ _ _ SS cl _ _ _ S p lam h h.2.2.2.1 h.2.2.1.2.1 (aaOf_fg cc)
    (laFacts_of_adm B hcc hδ h) hS.1 hS (hΞ j L0 La') hpS (lambda_in_lattice_pair cc δ _ _) hTA⟩

theorem combAtLt_scalar {p : ℕ} [Fact p.Prime] (X : Formalism.MainNotions.FormalGroupSystem.Sys p) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7)
    (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
    (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))
    (T : TaylorLogMetric.Tor D) (e : TaylorLogMetric.FamE D) (lam : TaylorLogMetric.Qbar →+* ℂ_[p])
    (G : ∀ j, X.Lt j → X.Lt (j + 1) → TaylorLogMetric.VC D ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ)
    (s : ∀ j, X.Lt j → X.Lt (j + 1) → ℂ) (k : ∀ j, X.Lt j → X.Lt (j + 1) → ℤ)
    (h : CombAtLt X hfin D large₂ Lg' (fun j La La' => TaylorLogMetric.pSer D lam (G j La La')) T e lam)
    (hs : ∀ j, j < X.mm → ∀ (L0 : X.Lt j), L0 ∈ Formalism.L2.G.Pend.repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1),
      (X.Pj (j + 1)).IsLatTup La'.2 → s j L0 La' ∈ TaylorLogMetric.Qbar ∧ ‖(p : ℂ_[p]) ^ k j L0 La' * TaylorLogMetric.lamC lam (s j L0 La')‖ ≤ 1) :
    CombAtLt X hfin D large₂ Lg'
      (fun j La La' => ((p : ℂ_[p]) ^ k j La La') • TaylorLogMetric.pSer D lam (fun z => s j La La' * G j La La' z)) T e lam := by
  intro j hj L0 h0 La' hL'
  obtain ⟨hA, hC⟩ := h j hj L0 h0 La' hL'
  exact ⟨hA, Formalism.L2.KerInert.Rep.isComb_scalar D T e lam _ hC (hs j hj L0 h0 La' hL').1 _ (hs j hj L0 h0 La' hL').2⟩

end Formalism.L2.KerInert.RepLt

namespace Formalism.L2.KerInert.RepLt

open Formalism.MainNotions.FormalGroupSystem Formalism.L2.Th1.D Formalism.L2.Th1.Top Formalism.L2.KerInert.K1 Formalism.L2.KerInert.Rep
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (cob UnrOK IsLawOfLog)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.G.Pend (k0ToC wittFractionAlgebraCp OcC Frm thA thFOf)
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

theorem firstKernelLawSmallSteps_of_curve_orthAllLt {p : ℕ} [Fact p.Prime] (h5 : 5 ≤ p) (X : Sys p) [IsFractionRing X.G.O X.G.Kf]
    (E : Formalism.L2.G.Pend.CEmbC X.G) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (be : MvPowerSeries (Fin 2) (K0 p))
    {T : Type} (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p])
    (hB : BeProp p be) (g2 g3 ε s2 : MaximalUnramifiedExtension p) (hC : CurveAt p be g2 g3 ε s2)
    (hO : OrthAllLt X E hfin pos F g2 g3 s2 ε) :
    FirstKernelLawLocalPowerSeries X E hfin be pos F := by
  intro j hj L0 h0 La' hL' φ
  exact k1gen_of_orth h5 hB hC (hO j hj L0 h0 La' hL' φ)

theorem K1_representatives_LT_of_dictionary (hCD : CurveDict) (hInt : Formalism.L2.KerInert.IntInert) (D : D7) {p : ℕ} [Fact p.Prime] (h5 : 5 ≤ p)
    (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : Formalism.L2.G.Pend.CEmbC X.G) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses)
    {g : Formalism.MainNotions.GL3Theta.G1 p} (hLT : Formalism.L2.G.Pend.LTIso g)
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hA : Formalism.MainNotions.GL3Theta.At D cc δ g) (hIn : Formalism.MainNotions.GL3Theta.InertK D p)
    (hM : Formalism.MainNotions.GL3Theta.ModelOverW g.lam g.abelian₂ g.C) (B : Base D cc δ) (hcc : IsCurveIdeal D cc) (hδ : IsDiscriminantTwelfthRootOfIdealLattice D cc δ)
    (χ : IdE D → ℂ) (hχ : IsChi D χ) (hin : jacobiSym (-(D.host.d : ℤ)) p = -1) (hLam : g.abelian₂ = B.tor.abelian₂)
    (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)
    (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
    (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))
    (F Fr : ∀ j, X.Lt j → X.Lt (j + 1) →
      MvPowerSeries (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p])
    (hFr : ∀ j La La', Fr j La La' =
      sclY (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * (Formalism.L2.KerInert.BeCob.eLT hLT)⁻¹) (F j La La'))
    (S : ∀ j, X.Lt j → X.Lt (j + 1) →
      (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) →
      (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) → ℂ_[p])
    (hB : BeProp p (Formalism.L2.G.Pend.beLT hLT))
    (hComb : CombAtLt X hfin D large₂ Lg' F B.tor (B.eNat χ) g.lam)
    (hFH : FrameHypLt X E hfin D pos large₂ Lg' Fr S g.lam 1) :
    FirstKernelLawLocalPowerSeries X E hfin (Formalism.L2.G.Pend.beLT hLT) pos (fun j La La' => linSub (S j La La') (Fr j La La')) := by
  obtain ⟨g2, g3, ε, s2, hC, hD⟩ := curveDict_data hCD D cc δ hLT hA h5 hIn hM
  have hD' : DictInt D g.lam B.tor.abelian₂ (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * (Formalism.L2.KerInert.BeCob.eLT hLT)⁻¹) g2 g3 s2 ε := by
    rw [← hLam]
    exact hD D
  obtain ⟨C, wq, hMod, hW, hDi⟩ := hD'
  refine firstKernelLawSmallSteps_of_curve_orthAllLt h5 X E hfin _ pos _ hB g2 g3 ε s2 hC ?_
  intro j hj L0 h0 La' hL' φ
  obtain ⟨r, b, hLB, hON, σ, f, f', hσ, hP, hEq⟩ := hFH j hj L0 h0 La' hL' φ
  obtain ⟨hAdm, hCb⟩ := hComb j hj L0 h0 La' hL'
  refine ⟨r, thOrth D g.lam (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * (Formalism.L2.KerInert.BeCob.eLT hLT)⁻¹) b (F j L0 La'), σ, f, f', hσ,
    hP, ?_, hDi _ _ r b _ (hInt D cc δ B hcc hδ χ hχ p h5 hin g.lam _ _ _ _ hAdm (F j L0 La') hCb C wq r b hMod hW hLB hON)⟩
  rw [hEq, hFr, thOrth_sclY]

end Formalism.L2.KerInert.RepLt

set_option pp.fullNames true
end
end

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker
open scoped TensorProduct

namespace Formalism.L2.KerInert.KGLt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert.KG

variable {p : ℕ} [Fact p.Prime]


variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem first_kernel_small_of_frame (D : D7) (h5 : 5 ≤ p) (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (g : GL3Theta.G1 p) (hLT : LTIso g)
    (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (fd : FData X D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ)
    (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
    (Ξ₀ : ∀ j, X.Lt j → X.Lt (j + 1) → Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ)
    (muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ)
    (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v)
    (hAt : GL3Theta.At D cc δ g) (hIn : GL3Theta.InertK D p) (hM : GL3Theta.ModelOverW g.lam g.abelian₂ g.C)
    (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hχ : TaylorLogMetric.IsChi D χ) (hLam : g.abelian₂ = B.tor.abelian₂)
    (hAdm : Formalism.L2.KerInert.RepLt.AdmGLt X hfin D fd) (hCl : Formalism.L2.KerInert.RepRec.ClAway p cl)
    (hXi : Formalism.L2.KerInert.RepRec.XiAway X D Ξ₀) (hSc : Formalism.L2.KerInert.RepLt.ScalGLt X hfin fd χ muT g.lam)
    (hρ : Formalism.L2.KerInert.RepFrame.LamPosG X E D pos g.lam ρ) (hMI : Formalism.L2.KerInert.RepFrame.MInv X fd.frM)
    (hL : Formalism.L2.KerInert.RepLt.FrameLatMapLt X fd.frM hfin D (fun j La _ => fd.kerN j La)
        (fun j _ La' => fd.kerN (j + 1) La') ρ) :
    Formalism.L2.KerInert.RepLt.FirstKernelLawLocalPowerSeries X E hfin (beLT hLT) pos (FrecG E.toCEmb pos fd B χ g.lam SS cl Ξ₀ muT (ltC g hLT)) := by

  let large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E) :=
    fun j La _ => fd.kerN j La
  let Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E) :=
    fun j _ La' => fd.kerN (j + 1) La'
  let Ξ : ∀ j, X.Lt j → X.Lt (j + 1) → Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ :=
    fun j La La' => movD (Ξ₀ j La La') (fd.trG j La) (fd.trG (j + 1) La')
  let G : ∀ j, X.Lt j → X.Lt (j + 1) → TaylorLogMetric.VC D ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ :=
    fun j La La' => kerTh B χ SS cl (large₂ j La La') (Lg' j La La') (Ξ j La La')
  let F : ∀ j, X.Lt j → X.Lt (j + 1) →
      MvPowerSeries (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p] :=
    fun j La La' => ((p : ℂ_[p]) ^ expG X j La La') •
      TaylorLogMetric.pSer D g.lam (fun z => scalG fd χ muT j La La' * G j La La' z)
  let Fr : ∀ j, X.Lt j → X.Lt (j + 1) →
      MvPowerSeries (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p] :=
    fun j La La' => Formalism.L2.KerInert.Rep.sclY (ltC g hLT) (F j La La')
  let S := fun j (La : X.Lt j) (La' : X.Lt (j + 1)) => Formalism.L2.KerInert.RepFrame.subGen X E pos fd.frM j La La'
  have hFam : FrecG E.toCEmb pos fd B χ g.lam SS cl Ξ₀ muT (ltC g hLT) =
      fun j La La' => Formalism.MainNotions.FormalGroupSystem.linSub (S j La La') (Fr j La La') := by
    funext j La La'
    have hS : S j La La' = subBG E.toCEmb pos fd j La La' :=
      funext fun x => funext fun y => (subBG_eq E pos fd j La La' x y).symm
    rw [hS]
    exact linSub_scl _ _ _

  have hB : BeProp p (beLT hLT) := Formalism.L2.KerInert.beProp_ofA Formalism.L2.KerInert.inert_facts_first_hold D cc δ p g hLT hAt h5 hIn hM
  have hComb0 : Formalism.L2.KerInert.RepLt.CombAtLt X hfin D large₂ Lg'
      (fun j La La' => TaylorLogMetric.pSer D g.lam (G j La La')) B.tor (B.eNat χ) g.lam :=
    Formalism.L2.KerInert.RepLt.combAtLt_of_dataRec X hfin D B χ SS cl g.lam hcc hδ
      (Formalism.L2.KerInert.AlgTP.algT_of B hcc hδ hχ) large₂ Lg' Ξ
      (Formalism.L2.KerInert.RepRec.dataRec_movD X D cl Ξ₀ (fun j La _ => fd.trG j La) (fun j _ La' => fd.trG (j + 1) La')
        ((Formalism.L2.KerInert.RepRec.dataRec_iff X D cl Ξ₀).2 ⟨hCl, hXi⟩)) hAdm
  have hComb : Formalism.L2.KerInert.RepLt.CombAtLt X hfin D large₂ Lg' F B.tor (B.eNat χ) g.lam :=
    Formalism.L2.KerInert.RepLt.combAtLt_scalar X hfin D large₂ Lg' B.tor (B.eNat χ) g.lam G
      (fun j La La' => scalG fd χ muT j La La') (fun j La La' => expG X j La La') hComb0 hSc
  have hOnb : Formalism.L2.KerInert.RepLt.OnbExLt X hfin D large₂ Lg' :=
    Formalism.L2.KerInert.RepLt.onbExLt_of X hfin D large₂ Lg'
      (Formalism.L2.KerInert.orthBasisExists_of Formalism.L2.KerInert.global_orthonormal_basis_four Formalism.L2.KerInert.weakApprox_of_approx_and_separation) h5 hIn hAdm
  have hTr : Formalism.L2.KerInert.RepLt.LamTraceLt X hfin D large₂ Lg' g.lam :=
    Formalism.L2.KerInert.RepLt.lamTraceLt_of X hfin D large₂ Lg' g.lam
      (Formalism.L2.KerInert.RepLt.rankTieLt_of X hfin D large₂ Lg' hAdm)
      (Formalism.L2.KerInert.RepFrame.colTie_of X hfin D large₂ Lg' (Formalism.L2.KerInert.RepFrame.trace_tau_sum D) g.lam)
  have hFH : Formalism.L2.KerInert.RepLt.FrameHypLt X E hfin D pos large₂ Lg' Fr S g.lam 1 :=
    Formalism.L2.KerInert.RepLt.frameHypLt_of_lat X E hfin D pos large₂ Lg' fd.frM g.lam ρ hOnb hTr hρ
      (Formalism.L2.KerInert.RepFrob.frobTw_of X E h5) hMI (twInt_all X E) hL Fr
  rw [hFam]
  exact Formalism.L2.KerInert.RepLt.K1_representatives_LT_of_dictionary Formalism.L2.KerInert.Rep.curve_dictionary Formalism.L2.KerInert.kernels_integral_inert D h5 X E
    hfin hLT cc δ hAt hIn hM B hcc hδ χ hχ hIn hLam pos large₂ Lg' F Fr
    (fun j La La' => by simp only [Fr]; rw [ltC_eq]) S hB hComb hFH


variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem first_kernel_small_of_frame_twist (D : D7) (h5 : 5 ≤ p) (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (g : GL3Theta.G1 p) (hLT : LTIso g)
    (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (fd : FData X D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ)
    (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
    (Ξ₀ : ∀ j, X.Lt j → X.Lt (j + 1) → Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ)
    (muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ)
    (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v)
    (hAt : GL3Theta.At D cc δ g) (hIn : GL3Theta.InertK D p) (hM : GL3Theta.ModelOverW g.lam g.abelian₂ g.C)
    (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hχ : TaylorLogMetric.IsChi D χ) (hLam : g.abelian₂ = B.tor.abelian₂)
    (hAdm : Formalism.L2.KerInert.RepLt.AdmGLt X hfin D fd) (hCl : Formalism.L2.KerInert.RepRec.ClAway p cl)
    (hXi : XiAwayLt X hfin D Ξ₀) (hSc : Formalism.L2.KerInert.RepLt.ScalGLt X hfin fd χ muT g.lam)
    (hρ : Formalism.L2.KerInert.RepFrame.LamPosG X E D pos g.lam ρ) (hMI : Formalism.L2.KerInert.RepFrame.MInv X fd.frM)
    (hL : Formalism.L2.KerInert.RepLt.FrameLatMapLt X fd.frM hfin D (fun j La _ => fd.kerN j La)
        (fun j _ La' => fd.kerN (j + 1) La') ρ) :
    Formalism.L2.KerInert.RepLt.FirstKernelLawLocalPowerSeries X E hfin (beLT hLT) pos (FrecG E.toCEmb pos fd B χ g.lam SS cl Ξ₀ muT (ltC g hLT)) := by
  classical
  let Ξ₁ : ∀ j, X.Lt j → X.Lt (j + 1) → Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ :=
    fun j La La' => if j < X.mm ∧ La ∈ repOf X.Lv hfin j ∧ (X.Pj (j + 1)).IsLatTup La'.2 then Ξ₀ j La La' else fun _ => 0
  have hXi1 : Formalism.L2.KerInert.RepRec.XiAway X D Ξ₁ := by
    obtain ⟨S₀, hp, hS⟩ := hXi
    refine ⟨S₀, hp, fun j La La' y => ?_⟩
    by_cases h : j < X.mm ∧ La ∈ repOf X.Lv hfin j ∧ (X.Pj (j + 1)).IsLatTup La'.2
    · simp only [Ξ₁, if_pos h]
      exact hS j h.1 La h.2.1 La' h.2.2 y
    · simp only [Ξ₁, if_neg h]
      exact IntOff.zero
  have hK := first_kernel_small_of_frame D h5 X E hfin g hLT pos fd cc δ B χ SS cl Ξ₁ muT ρ hAt hIn hM hcc hδ hχ hLam
    hAdm hCl hXi1 hSc hρ hMI hL
  intro j hj L0 h0 La' hLa' φ
  have hEq : thFOf X pos (FrecG E.toCEmb pos fd B χ g.lam SS cl Ξ₁ muT (ltC g hLT)) j L0 La' =
      thFOf X pos (FrecG E.toCEmb pos fd B χ g.lam SS cl Ξ₀ muT (ltC g hLT)) j L0 La' := by
    simp only [thFOf, FrecG, Ξ₁, if_pos (And.intro hj (And.intro h0 hLa'))]
  have := hK j hj L0 h0 La' hLa' φ
  rwa [hEq] at this


variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem first_kernel_law_global_small : TranslatesOfInertKernelAtPlace := by
  intro D p _ h5 X _ E hfin hst g hLT pos fd cc δ B χ lam SS cl Ξ₀ muT ρ hAt hIn hM hcc hδ hχ hlam hLam hAdm hCl hXi hSc
    hρ hMI hL
  subst hlam
  have hK := first_kernel_small_of_frame_twist D h5 X E hfin g hLT pos fd cc δ B χ SS cl Ξ₀ muT ρ hAt hIn hM hcc hδ hχ hLam hAdm hCl hXi hSc
    hρ hMI hL
  have h2b := (Formalism.L2.PairingIndexBounds.PowerSeriesNecessity.adm_two_pendant_iff_representative D X E hfin hst hLT pos _).2 hK
  exact ⟨Formalism.L2.KerInert.admissible_second_of_variant D X E hfin hst hLT pos _ h2b, h2b,
    Formalism.L2.KerInert.admissible_third_of_second_eleventh D X E hfin hst hLT pos _ h2b
      (Formalism.L2.KerInert.admissible_eleventh_inert D cc δ p g hLT hAt h5 hIn hM X _ rfl)⟩

end Formalism.L2.KerInert.KGLt
end
end

noncomputable section

namespace Formalism.L2.KerInert.AdmLoc2

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend

section Law

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmb X.G)
  (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : FinStab X.Lv) (be : MvPowerSeries (Fin 2) (Formalism.L2.G.Pend.K0 p))

theorem admissible_stabilizer_of_law (D : Formalism.BasicNotions.D7) (ThR : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) ℂ_[p]) :
    StabLawLt X E hfin ThR → Formalism.MainNotions.FormalGroupSystem.MinkowskiCounting D X (pendR X E hfin hst be ThR) := by
  let _ := wittFractionAlgebraCp p
  let _ := algKfC E
  intro hS
  classical
  let ThR' : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) ℂ_[p] :=
    fun j La La' => if j < X.mm ∧ (X.Pj (j + 1)).IsLatTup La'.2 then ThR j La La' else 0
  have hS' : StabLaw X ℂ_[p] hfin ThR' := by
    intro j c L0 La' ε h0 hε
    by_cases hj : j < X.mm ∧ (X.Pj (j + 1)).IsLatTup La'.2
    · simp only [ThR', if_pos hj]
      exact hS j hj.1 c L0 La' ε h0 hj.2 hε
    · simp only [ThR', if_neg hj]
      unfold SA
      rw [← MvPowerSeries.coe_substAlgHom (hasSubst_actS X ℂ_[p] j _), map_zero, mul_zero]
  have hK := kapLaw_of_stabLaw X ℂ_[p] hfin ThR' pC_ne_zero hS'
  intro j hj c L La' γ G hGv hL hLa'
  have hEq : ∀ La, thFN X ℂ_[p] hfin (thGeo X ℂ_[p] hfin ThR') j La La' = thFN X ℂ_[p] hfin (thGeo X ℂ_[p] hfin ThR) j La La' := by
    intro La
    simp only [thFN, thGeo, ThR', if_pos (And.intro hj hLa')]
  have key : ∀ t : X.G.Kf,
      (eSX X j (c, (X.Lv.lev j c).smul γ L) * t) •
          delF X ℂ_[p] j ((((X.Lv.lev j c).χ γ : X.G.Oˣ) : X.G.O) • (X.Lv.lev j c).actX γ G)
            (thFN X ℂ_[p] hfin (thGeo X ℂ_[p] hfin ThR) j (c, (X.Lv.lev j c).smul γ L) La') =
        (eSX X j (c, L) * t) • delF X ℂ_[p] j G (thFN X ℂ_[p] hfin (thGeo X ℂ_[p] hfin ThR) j (c, L) La') := by
    intro t
    have := ker_law X ℂ_[p] pC_ne_zero (delEquivOn_GdC X ℂ_[p]) _ hK j c L La' γ G hL (vtIn_GdC X ℂ_[p] j G hGv) t
    rwa [hEq, hEq] at this
  exact key _

end Law

end Formalism.L2.KerInert.AdmLoc2

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker
open scoped TensorProduct

namespace Formalism.L2.KerInert.AdmLoc2

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.PairingIndexBounds.F
open Formalism.L2.KerInert.AdmLoc (pendG CurveIn XiIn)

theorem admissible_general_of_kernel_law (hK1 : Formalism.L2.KerInert.KGLt.TranslatesOfInertKernelAtPlace) : AdmGen2 := by
  intro D p _ X _ E hfin hst g hLT pos fd cc δ B χ lam SS cl Ξ₀ muT hC hK hXi hLaw h3b h4
  obtain ⟨h5, hAt, hin, hW, hcc, hδ, hχ, hlam, hLam⟩ := hC
  obtain ⟨hA, hcl, hXa, hS, ρ, hLP, hMI, hFL⟩ := hK
  obtain ⟨h2, h2b, h3⟩ := hK1 D p h5 X E hfin hst g hLT pos fd cc δ B χ lam SS cl Ξ₀ muT ρ
    hAt hin hW hcc hδ hχ hlam hLam hA hcl hXa hS hLP hMI hFL
  refine ⟨Formalism.MainNotions.FormalGroupSystem.Pf.positivity_condition_holds D, h2, h2b, ?_, h3, h3b, h4, ?_, ?_, Formalism.L2.G.Pend.up_down_adjoint D X _,
    Formalism.L2.PairingIndexBounds.Ent.pending_tuple_admissible X E hfin hst hLT pos _ D, Formalism.L2.KerInert.admissible_all_levels D p X, ?_⟩
  · exact Formalism.L2.KerInert.admissible_second_inert D cc δ p g hLT hAt h5 hin hW X _ rfl
  · exact (invariance_iff_additive_maps_exist X E hfin hst hLT pos _ D).2 hXi
  · exact admissible_stabilizer_of_law X E.toCEmb hfin hst (beLT hLT) D _ hLaw
  · exact Formalism.L2.KerInert.admissible_eleventh_inert D cc δ p g hLT hAt h5 hin hW X _ rfl

section At

open Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelCoupled

theorem admissible_place_of_kernel_law (hK1 : Formalism.L2.KerInert.KGLt.TranslatesOfInertKernelAtPlace) : AdmAt2 := by
  intro D L hT Gi Gl Kc0 Dx cX ex t u μ w h _ Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om _ E hfin hst g hLT pos
    Tw I L0 a bad cc δ B χ lam SS cl Ξ₀ muT hC hK hXi hLaw hTies
  obtain ⟨ι, Rd, Sr, hE, hL⟩ := hTies
  have hmm : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).mm = D.R.m := KA.fl_m
  refine admissible_general_of_kernel_law hK1 D _ (sysAt Ch std vp unif eO eO_spec dG dG_spec om) E hfin hst g hLT pos _ cc δ B χ lam SS cl Ξ₀ muT hC hK hXi hLaw
    (admissible_third_instance D L hT Gi Gl Kc0 Dx cX ex u μ w h Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om) ?_
  by_cases hm : 0 < D.R.m
  · obtain ⟨lp, hTC, hH⟩ := hL hm
    exact admissible_fourth_instance D L hT Gi Gl Kc0 Dx cX ex t u μ w h Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om _ ι Rd Sr lp hE (fun _ => ⟨hTC, hH⟩)
  · exact ⟨fun j hj => absurd hj (by omega), fun j hj => absurd hj (by omega)⟩

theorem admissible_entries_of_kernel_law (hK1 : Formalism.L2.KerInert.KGLt.TranslatesOfInertKernelAtPlace) : AdmAtEnt2 := by
  intro D L hT Gi Gl Kc0 Dx cX ex t u μ w h _ Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om _ E hfin hst g hLT pos
    Tw I L0 a bad cc δ B χ lam SS cl Ξ₀ muT hC hK hXi hLaw hTies
  obtain ⟨ι, Rd, Sr, hA⟩ := hTies
  have h5b := admissible_stabilizer_of_law (sysAt Ch std vp unif eO eO_spec dG dG_spec om) E.toCEmb hfin hst (beLT hLT) D _ hLaw
  refine admissible_place_of_kernel_law hK1 D L hT Gi Gl Kc0 Dx cX ex t u μ w h Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om E hfin hst g hLT pos Tw I L0 a bad cc δ B χ lam SS cl Ξ₀ muT
    hC hK hXi hLaw ⟨ι, Rd, Sr, fun j hj => hA j (by omega), fun hm => ?_⟩
  obtain ⟨lp, hsec⟩ := coupled_section_exists D L hT Gi Gl Kc0 Dx cX ex u μ w h Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om _ hm
  have hT1 := hA (D.R.m - 1) (by omega)
  exact ⟨lp, coupled_compatibility_at_place D L hT Gi Gl Kc0 Dx cX ex t u μ w h Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om _ ι Rd Sr lp hm hsec hT1,
    hecke_coupled_entry D L hT Gi Gl Kc0 Dx cX ex u μ w h Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om _ lp hm h5b hsec hT1.2.1⟩

end At

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem admissible_entries_small_chain : AdmAtEnt2 := admissible_entries_of_kernel_law Formalism.L2.KerInert.KGLt.first_kernel_law_global_small

end Formalism.L2.KerInert.AdmLoc2
