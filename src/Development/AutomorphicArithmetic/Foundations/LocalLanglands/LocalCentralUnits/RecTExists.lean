module

public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.CuspEx
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsExtensionInjective

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ExtDim
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Zero.LLC

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a} {r : IrrGL (k := w.adicCompletion E) → WD h}

private theorem charPol_seg (H : CuspT a ha r) (Δ : Segment (w.adicCompletion E)) (σ : Weil h) :
    (((r Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp (h := h) Δ.len)).charPol σ
      = (Δ.ms.map fun y => (r y).charPol σ).prod := by
  have hspecial (x : WD h) (l : ℕ) :
      ((x.lpTw (((l : ℝ) - 1) / 2)).lpChar (WD.lpSp (h := h) l)).charPol σ =
        ((Multiset.range l).map fun j : ℕ => (x.lpTw j).charPol σ).prod := by
    induction x using WD.ind with
    | hP n a =>
      have hq : ((normV w : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ReciprocityTheory.Gal.one_lt_normV w).ne_bot
      rw [WD.lpSp, WD.lpTw_mk, WD.lpChar_mk, WD.charPol_mk, WDRep.tensor_ρ, WDRep.sp_ρ,
        GlobalTheory.WeilDeligne.SpCharpoly.charpoly_map_diagEnd]
      change _ = ∏ j ∈ Finset.range l, ((WD.mk a).lpTw (j : ℕ)).charPol σ
      rw [← Fin.prod_univ_eq_prod_range (fun j : ℕ => ((WD.mk a).lpTw (j : ℕ)).charPol σ)]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [WD.lpTw_mk, WD.charPol_mk, WDRep.tw_ρ, WDRep.tw_ρ, smul_smul, ← mul_zpow, WDRep.spEig,
        coe_qPow, ← Complex.cpow_add _ _ hq, ← Complex.ofReal_add, sub_add_cancel]
  rw [hspecial (r Δ.first) Δ.len, Segment.ms, Multiset.map_map]
  have h1 : ∀ j : Fin Δ.len, (r (Δ.term j)).charPol σ = ((r Δ.first).lpTw ((j : ℕ) : ℝ)).charPol σ := by
    intro j
    rw [Segment.term, show (((j : ℕ) : ℂ)) = ((((j : ℕ) : ℝ)) : ℂ) by push_cast; rfl, H.nu _ Δ.isCusp_first]
  change _ = ∏ j : Fin Δ.len, (fun y => (r y).charPol σ) (Δ.term j)
  simp only [h1]
  rw [Fin.prod_univ_eq_prod_range (fun j => ((r Δ.first).lpTw (j : ℝ)).charPol σ) Δ.len]
  rfl

private theorem dim_charPol {rc : IrrGL (k := w.adicCompletion E) → WD h} (H : CuspT a ha r) (L : IsLExt r rc)
    (x : IrrGL (k := w.adicCompletion E)) :
    (rc x).lpDim = x.1 ∧ ∃ s, HasSupport x.rep s ∧ (∀ y ∈ s, y.IsCusp) ∧
      ∀ σ, (rc x).charPol σ = (s.map fun y => (r y).charPol σ).prod := by
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨𝔪, hm⟩ := Pr.exh (w.adicCompletion E) x
  have hs : HasSupport x.rep (msupp 𝔪) := GlobalTheory.LocGL.hasSupport_msupp_of_isL Pr.zel _ 𝔪 x hm
  have hcp : ∀ σ, (rc x).charPol σ = ((msupp 𝔪).map fun y => (r y).charPol σ).prod := by
    intro σ
    rw [L 𝔪.toList x (by rw [Multiset.coe_toList]; exact hm), segSum, CuspExt.charPol_sumList, List.map_map,
      msupp, Multiset.map_bind, Multiset.prod_bind]
    have hl : ∀ (l : List (Segment (w.adicCompletion E))) (F : Segment (w.adicCompletion E) → ℂ[X]),
        (l.map F).prod = ((l : Multiset _).map F).prod := fun l F => by rw [Multiset.map_coe, Multiset.prod_coe]
    rw [hl, Multiset.coe_toList]
    exact congrArg Multiset.prod (Multiset.map_congr rfl fun Δ _ => charPol_seg H Δ σ)
  refine ⟨?_, msupp 𝔪, hs, fun y hy => hs.isCusp hy, hcp⟩
  rw [← WD.charPol_natDegree (rc x) 1, hcp, Polynomial.natDegree_multiset_prod_of_monic _
    (fun f hf => by obtain ⟨y, -, rfl⟩ := Multiset.mem_map.1 hf; exact WD.charPol_monic _ _), Multiset.map_map]
  have h2 : ((msupp 𝔪).map ((fun p : ℂ[X] => p.natDegree) ∘ fun y => (r y).charPol 1)) = (msupp 𝔪).map Sigma.fst :=
    Multiset.map_congr rfl fun y hy => by
      simp only [Function.comp_apply, WD.charPol_natDegree]
      exact H.dim y (hs.isCusp hy)
  rw [h2, hs.sum_fst, Fintype.card_fin]

end UpperTheory.Zero.LLC

theorem UpperTheory.Zero.LLC.extDim :
    UpperTheory.Zero.LLC.ExtDim := by
  intro E Ω _ _ _ _ _ A w h a ha r rc H L x
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨hd, s, hs, hc, hcp⟩ := dim_charPol H L x
  refine ⟨⟨hd, s, hs, hc, hcp⟩, fun ω hω σ => ?_⟩
  obtain ⟨f, hf, hprod⟩ := GlobalTheory.T.centralCharacter_eq_prod_supercuspidalSupport Pr.bz (w.adicCompletion E) x s ω hs hω
  have he : ((rc x).eig σ).prod = (s.map fun y => ((r y).eig σ).prod).prod := by
    rw [WD.eig, hcp, prod_roots_prod_of_monic s (fun y => (r y).charPol σ) fun y => WD.charPol_monic _ _]
    rfl
  have hw : ((ω (a σ) : ℂˣ) : ℂ) = (s.map fun y => ((f y (a σ) : ℂˣ) : ℂ)).prod := by
    rw [hprod, ← Units.coeHom_apply, map_multiset_prod, Multiset.map_map]
    rfl
  constructor
  · have hn : ∀ m : Multiset ℂ, ‖m.prod‖ = (m.map fun z => ‖z‖).prod :=
      fun m => map_multiset_prod (normHom (α := ℂ)) m
    rw [he, hw, hn, hn, Multiset.map_map, Multiset.map_map]
    exact congrArg Multiset.prod (Multiset.map_congr rfl fun y hy => H.absCentral y (hc y hy) (f y) (hf y hy) σ)
  · rintro ⟨s', hs', hg⟩
    obtain rfl := (goodSeg (w.adicCompletion E)).2.2 x _ _ hs' hs
    rw [he, hw]
    exact congrArg Multiset.prod (Multiset.map_congr rfl fun y hy => H.central y (hc y hy) (hg y hy) (f y) (hf y hy) σ)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ExtDepth
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Zero.LLC.extDepth :
    UpperTheory.Zero.LLC.ExtDepth := by
  intro E Ω _ _ _ _ _ A w h a ha r rc hr hext x hgood hdz
  rw [GlobalTheory.T.isTameWeilDeligne_iff_wild_charpoly]
  intro σ hσ
  obtain ⟨⟨hdim, s, hsup, hcusp, hchar⟩, -⟩ := UpperTheory.Zero.LLC.extDim E Ω A w h a ha r rc hr hext x
  obtain ⟨s0, hsup0, hgc⟩ := hgood
  have hs : s0 = s := (UpperTheory.Zero.LLC.goodSeg _).2.2 x s0 s hsup0 hsup
  subst hs
  have hdzy : ∀ y ∈ s0, UpperTheory.Zero.LLC.DZ y := by
    obtain ⟨m, f, hf, hcs⟩ := hsup
    intro y hy
    rw [← hf] at hy
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hy
    have key := UpperTheory.Zero.LLC.Pr.dzs _ x.fst (GlobalTheory.SplitRead.Irr.ofIrrRep x.snd.rep) m (fun i => (f i).fst)
      (fun i => GlobalTheory.SplitRead.Irr.ofIrrRep (f i).snd.rep) hcs ((Submodule.ne_bot_iff _).mp hdz) i
    exact (Submodule.ne_bot_iff _).mpr key
  have htame : ∀ y ∈ s0, (r y).charPol σ = (X - 1) ^ y.fst := by
    intro y hy
    have hy' := hr.depth y (hcusp y hy) (hgc y hy) (hdzy y hy)
    rw [GlobalTheory.T.isTameWeilDeligne_iff_wild_charpoly] at hy'
    rw [hy' σ hσ, hr.dim y (hcusp y hy)]
  rw [hchar σ, Multiset.map_congr rfl htame, GlobalTheory.LlcDepth.prod_map_pow (X - 1) Sigma.fst s0,
    HasSupport.sum_fst hsup, Fintype.card_fin, hdim]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ExtDual
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Zero.LLC

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a}
  {r : IrrGL (k := w.adicCompletion E) → WD h}

private theorem summand_dual (H : CuspT a ha r) {Δ Δ' : Segment (w.adicCompletion E)}
    (hg : GoodCusp Δ.first) (hd : SegDual Δ Δ') :
    ((r Δ'.first).lpTw (((Δ'.len : ℝ) - 1) / 2)).lpChar (WD.lpSp (h := h) Δ'.len) =
      (((r Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp (h := h) Δ.len)).lpDual := by
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨hl, hD⟩ := hd
  have hc : (Δ.first.nu ((Δ.len : ℂ) - 1)).IsCusp := Δ.isCusp_first.nu _
  have hgn : GoodCusp (Δ.first.nu ((Δ.len : ℂ) - 1)) := by
    rw [IrrGL.nu]
    exact ((clBasic _ Δ.first).2.1 _ _).2.2.1.2 hg
  have e1 := H.dual _ _ hc Δ'.isCusp_first hgn hD
  have e2 : Δ.first.nu ((Δ.len : ℂ) - 1) = Δ.first.nu (((Δ.len : ℝ) - 1 : ℝ) : ℂ) := by push_cast; rfl
  rw [e2, H.nu _ Δ.isCusp_first] at e1
  obtain ⟨hS, hT, hP⟩ := GlobalTheory.T.weilDeligneParam_dual_listSum_absTwist_special E Ω A w h
  rw [e1, hl, hP, hT, hT, WD.lpTw_add]
  congr 2
  ring

private theorem map_summand_dual (H : CuspT a ha r) {l l' : List (Segment (w.adicCompletion E))}
    (hg : ∀ Δ ∈ l, GoodCusp Δ.first) (hF : List.Forall₂ SegDual l l') :
    l'.map (fun Δ => ((r Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp (h := h) Δ.len)) =
      l.map (fun Δ => (((r Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp (h := h) Δ.len)).lpDual) := by
  induction hF with
  | nil => rfl
  | @cons Δ Δ' l l' hd _ ih =>
    rw [List.map_cons, List.map_cons, ih (fun x hx => hg x (List.mem_cons_of_mem _ hx)),
      summand_dual H (hg _ List.mem_cons_self) hd]

end UpperTheory.Zero.LLC

theorem UpperTheory.Zero.LLC.extDual :
    UpperTheory.Zero.LLC.ExtDual := by
  intro E Ω _ _ _ _ _ A w h a ha r rc H hE n π π' hg hπ
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨𝔪, h𝔪⟩ := UpperTheory.Zero.LLC.Pr.exh _ (cls π)
  have hL : IsL ((𝔪.toList : List _) : Multiset (Segment (w.adicCompletion E))) (cls π).rep := by
    rw [Multiset.coe_toList]; exact h𝔪
  obtain ⟨l', hF, hL'⟩ := (UpperTheory.Zero.LLC.Pr.dual (w.adicCompletion E)).2 𝔪.toList (cls π) (cls π') hL ⟨n, π, π', rfl, rfl, hπ⟩
  have hgl := ((UpperTheory.Zero.LLC.goodSeg (w.adicCompletion E)).1 _ _ hL).1 hg
  rw [hE _ _ hL, hE _ _ hL', segSum, segSum, (GlobalTheory.T.weilDeligneParam_dual_listSum_absTwist_special E Ω A w h).1, List.map_map]
  exact congrArg sumList (UpperTheory.Zero.LLC.map_summand_dual H hgl hF)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.RcTwOfSegments
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Zero.LLC

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

private theorem rc_tw_of_segments {a : Weil h →* (w.adicCompletion E)ˣ} (ha : IsLocalArtin h a)
    {r rc : IrrGL (k := w.adicCompletion E) → WD h} (hL : IsLExt r rc)
    (l : List (Segment (w.adicCompletion E))) (x : IrrGL (k := w.adicCompletion E))
    (hx : IsL (l : Multiset (Segment (w.adicCompletion E))) x.rep)
    (χ : (w.adicCompletion E)ˣ →* ℂˣ) (hχ : IsSmoothChar χ)
    (hr : ∀ Δ ∈ l, r (Δ.first.tw χ hχ) = (r Δ.first).lpTwist (χ.comp a) (ha.smooth hχ)) :
    rc (x.tw χ hχ) = (rc x).lpTwist (χ.comp a) (ha.smooth hχ) := by
  haveI : CharZero (w.adicCompletion E) := algebraRat.charZero _
  obtain ⟨-, hs, ht, -⟩ := GlobalTheory.T.weil_deligne_sum_twist_compat E Ω A w h
  have h2 := GlobalTheory.T.isLanglandsClassification_twist_multisegment _ (l : Multiset (Segment (w.adicCompletion E))) x χ hχ hx
  rw [hL l x hx, hL (l.map fun Δ : Segment _ => Δ.tw χ hχ) (x.tw χ hχ) h2, segSum, segSum, hs, List.map_map, List.map_map]
  refine congrArg sumList (List.map_congr_left fun Δ hΔ => ?_)
  show ((r (Δ.first.tw χ hχ)).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp (h := h) Δ.len) = WD.lpTwist _ _ _
  rw [(ht _ _ _ _).2, hr Δ hΔ, WD.lpTw, WD.lpTw, GlobalTheory.LocLanglands.ExtTwist.lpTwist_lpTwist_comm]

end UpperTheory.Zero.LLC

theorem UpperTheory.Zero.LLC.extTw :
    UpperTheory.Zero.LLC.ExtTw := by
  intro E Ω _ _ _ _ _ A w h a ha r rc H hL
  haveI : CharZero (w.adicCompletion E) := algebraRat.charZero _
  refine ⟨fun x s => ?_, fun x χ hχ hg => ?_⟩
  · obtain ⟨𝔪, h𝔪⟩ := UpperTheory.Zero.LLC.Pr.exh _ x
    obtain ⟨l, rfl⟩ := Quotient.exists_rep 𝔪
    have key := rc_tw_of_segments ha hL l x h𝔪 (absPow _ (s : ℂ)) (isSmoothChar_absPow _) (fun Δ _ => by
      have h1 := H.nu _ Δ.isCusp_first s
      rw [WD.lpTw] at h1
      refine h1.trans ?_
      congr 1
      exact (ha.absPow_comp s).symm)
    refine key.trans ?_
    rw [WD.lpTw]
    congr 1
    exact ha.absPow_comp s
  · obtain ⟨𝔪, h𝔪⟩ := UpperTheory.Zero.LLC.Pr.exh _ x
    obtain ⟨l, rfl⟩ := Quotient.exists_rep 𝔪
    have hg' := ((UpperTheory.Zero.LLC.goodSeg _).1 l x h𝔪).1 hg
    rw [lpChar_lpOfChar]
    exact rc_tw_of_segments ha hL l x h𝔪 χ hχ fun Δ hΔ => H.twist _ Δ.isCusp_first (hg' Δ hΔ) χ hχ

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ExtInj
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Zero.LLC.extInj :
    UpperTheory.Zero.LLC.ExtInj := by
  intro E Ω _ _ _ _ _ A w h a ha r rc hr hL x y hy hxy
  classical
  obtain ⟨mx, hmx⟩ := UpperTheory.Zero.LLC.Pr.exh _ x
  obtain ⟨my, hmy⟩ := UpperTheory.Zero.LLC.Pr.exh _ y
  have hlx : IsL (↑mx.toList) x.rep := by rw [Multiset.coe_toList]; exact hmx
  have hly : IsL (↑my.toList) y.rep := by rw [Multiset.coe_toList]; exact hmy
  have hgood : ∀ Δ ∈ my.toList, UpperTheory.Zero.LLC.GoodCusp Δ.first :=
    ((UpperTheory.Zero.LLC.goodSeg _).1 _ y hly).1 hy
  have e := hxy
  rw [hL _ x hlx, hL _ y hly] at e
  let f : Segment (HeightOneSpectrum.adicCompletion E w) → WD h × ℕ :=
    fun Δ => ((r Δ.first).lpTw ((↑Δ.len - 1) / 2), Δ.len - 1)
  have hcomp : (fun p : WD h × ℕ => p.1.lpChar (WD.lpSp (h := h) (p.2 + 1))) ∘ f =
      fun Δ => ((r Δ.first).lpTw ((↑Δ.len - 1) / 2)).lpChar (WD.lpSp (h := h) Δ.len) := by
    funext Δ
    simp only [Function.comp, f, Nat.sub_add_cancel Δ.len_pos]
  have hirr : ∀ l : List (Segment (HeightOneSpectrum.adicCompletion E w)), ∀ p ∈ l.map f, IsIrrWD p.1 := by
    intro l p hp
    obtain ⟨Δ, -, rfl⟩ := List.mem_map.mp hp
    exact LExtInj.isIrrWD_lpTw (hr.irr _ (Segment.isCusp_first _)) _
  have hperm := GlobalTheory.T.perm_of_weilDeligne_special_decomposition_eq E Ω A w h (mx.toList.map f) (my.toList.map f) (hirr _) (hirr _)
    (by rw [List.map_map, List.map_map, hcomp]; exact e)
  have key : ∀ Δ Δ' : Segment (HeightOneSpectrum.adicCompletion E w),
      UpperTheory.Zero.LLC.GoodCusp Δ'.first → f Δ = f Δ' → Δ = Δ' := by
    intro Δ Δ' hg he
    simp only [f, Prod.mk.injEq] at he
    obtain ⟨h1, h2⟩ := he
    have hl : Δ.len = Δ'.len := by
      have := Δ.len_pos
      have := Δ'.len_pos
      omega
    rw [hl] at h1
    exact Segment.ext_first
      (hr.inj _ _ (Segment.isCusp_first _) (Segment.isCusp_first _) hg (LExtInj.lpTw_injective h1)) hl
  let g : WD h × ℕ → Option (Segment (HeightOneSpectrum.adicCompletion E w)) := fun p =>
    if hp : ∃ Δ ∈ my.toList, f Δ = p then some hp.choose else none
  have hgy : ∀ Δ ∈ my.toList, g (f Δ) = some Δ := by
    intro Δ hΔ
    have hp : ∃ Δ' ∈ my.toList, f Δ' = f Δ := ⟨Δ, hΔ, rfl⟩
    simp only [g, dif_pos hp]
    exact congrArg some (key _ _ (hgood Δ hΔ) hp.choose_spec.2)
  have hgx : ∀ Δ ∈ mx.toList, g (f Δ) = some Δ := by
    intro Δ hΔ
    obtain ⟨Δ', hΔ', he⟩ := List.mem_map.mp (hperm.subset (List.mem_map_of_mem hΔ))
    have := key Δ Δ' (hgood Δ' hΔ') he.symm
    subst this
    exact hgy _ hΔ'
  have back : ∀ l : List (Segment (HeightOneSpectrum.adicCompletion E w)),
      (∀ Δ ∈ l, g (f Δ) = some Δ) → (l.map f).filterMap g = l := by
    intro l hl
    induction l with
    | nil => rfl
    | cons b t ih =>
      rw [List.map_cons, List.filterMap_cons_some (hl b List.mem_cons_self)]
      exact congrArg _ (ih fun Δ hΔ => hl Δ (List.mem_cons_of_mem _ hΔ))
  have hp2 : mx.toList.Perm my.toList := by
    have := hperm.filterMap g
    rwa [back _ hgx, back _ hgy] at this
  have hmm : (↑mx.toList : Multiset (Segment (HeightOneSpectrum.adicCompletion E w))) = ↑my.toList :=
    Multiset.coe_eq_coe.mpr hp2
  rw [hmm] at hlx
  exact LExtInj.eq_of_isL UpperTheory.Zero.LLC.Pr.multi _ x y hlx hly
end

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Zero.LLC.recTExists :
    UpperTheory.Zero.LLC.RecTExists := by
  intro E Ω _ _ _ _ _ A w h
  obtain ⟨a, ha, -⟩ := UpperTheory.Zero.LLC.artEx E Ω A w h
  obtain ⟨r, hr⟩ := UpperTheory.Zero.LLC.cuspEx E Ω A w h a ha
  obtain ⟨⟨rc, hrc⟩, hcu⟩ :=
    GlobalTheory.LocLanglands.exists_isLExt UpperTheory.Zero.LLC.Pr.exh UpperTheory.Zero.LLC.Pr.multi E Ω A w h r
  have hcusp : ∀ x : IrrGL (k := HeightOneSpectrum.adicCompletion E w), x.IsCusp → rc x = r x :=
    hcu rc hrc
  have hD := UpperTheory.Zero.LLC.extDim E Ω A w h a ha r rc hr hrc
  have hT := UpperTheory.Zero.LLC.extTw E Ω A w h a ha r rc hr hrc
  refine ⟨rc, a, ha, ?_⟩
  refine
    { dim := fun x => (hD x).1.1
      one := fun χ hχ => (hcusp _ (IrrGL.isCusp_ofChar χ hχ)).trans (hr.one χ hχ)
      langlands := ?_
      cusp := ?_
      nu := hT.1
      absCentral := fun x ω hω σ => ((hD x).2 ω hω σ).1
      twist := ?_
      central := fun x ω hg hω σ => ((hD x).2 ω hω σ).2 hg
      dual := UpperTheory.Zero.LLC.extDual E Ω A w h a ha r rc hr hrc
      inj := UpperTheory.Zero.LLC.extInj E Ω A w h a ha r rc hr hrc
      depth := fun x hg hx => UpperTheory.Zero.LLC.extDepth E Ω A w h a ha r rc hr hrc x hg hx
      type := ?_ }
  · intro l x hl
    rw [hrc l x hl]
    unfold GlobalTheory.LocLanglands.segSum
    congr 1
    refine List.map_congr_left ?_
    intro Δ _
    rw [hcusp _ Δ.isCusp_first]
  · intro x hx
    rw [hcusp x hx]
    exact hr.irr x hx
  · intro x χ hχ hg
    rw [hcusp _ (IrrGL.isCusp_ofChar χ hχ), hr.one χ hχ]
    exact hT.2 x χ hχ hg
  · refine (UpperTheory.Zero.LLC.typeIff E Ω A w h rc).2 ?_
    intro x
    unfold UpperTheory.Zero.LLC.TypeAt
    intro g _ i hi n hn D R hR θ hθ τ hτ hN σ hσ hinf
    have hx : x.IsCusp := by
      subst hσ
      exact IrrGL.isCusp_of.2 ⟨hn, DiscreteGroups.sglob.DzLc.isCuspidal_of_inflates i hi τ hτ σ hinf⟩
    rw [hcusp x hx]
    exact hr.type x hx g i hi n hn D R hR θ hθ τ hτ hN σ hσ hinf
