module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapInverseNatCast
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPartAttainsBoundUniqueShortestVector
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelsUnitaryClassicalTrait
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeClassSumsOfTermsPrescribedNorms

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SameOfUSame
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZH GlobalTheory.Poinc IsLocalRing

namespace GlobalTheory.UPoinc.USum

section Cong
variable {Y : Type} [AddCommGroup Y]

theorem cm_trans {N : ℕ} {x y z : Y} (h : CongMod N x y) (h' : CongMod N y z) : CongMod N x z := by
  obtain ⟨w, rfl⟩ := h
  obtain ⟨w', rfl⟩ := h'
  exact ⟨w' + w, by rw [smul_add]; abel⟩

theorem cm_symm {N : ℕ} {x y : Y} (h : CongMod N x y) : CongMod N y x := by
  obtain ⟨w, rfl⟩ := h
  exact ⟨-w, by rw [smul_neg]; abel⟩

theorem cm_map {Y' : Type} [AddCommGroup Y'] (f : Y →+ Y') {N : ℕ} {x y : Y} (h : CongMod N x y) :
    CongMod N (f x) (f y) := by
  obtain ⟨w, rfl⟩ := h
  exact ⟨f w, by rw [map_add (f := _), map_nsmul]⟩

theorem cm_of_mk {N : ℕ} {x y : Y} (h : (QuotientAddGroup.mk x : ModN N Y) = QuotientAddGroup.mk y) : CongMod N x y := by
  rw [QuotientAddGroup.eq] at h
  obtain ⟨w, hw⟩ := h
  have hw' : N • w = -x + y := hw
  exact ⟨-w, by rw [smul_neg, hw']; abel⟩

theorem cm_mk {N : ℕ} {x y : Y} (h : CongMod N x y) : (QuotientAddGroup.mk x : ModN N Y) = QuotientAddGroup.mk y := by
  rw [QuotientAddGroup.eq]
  obtain ⟨w, rfl⟩ := h
  exact ⟨-w, by change N • (-w) = -(y + N • w) + y; rw [smul_neg]; abel⟩

end Cong

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω} {p : ℕ}
  [Fact p.Prime] {Y : Type} [AddCommGroup Y] {q : Y → ℝ}


variable (ρ M q) in
def GLab (y : Sp (PadicAlgCl p) ⟶ M.Z) (yy : S.Gam →+ ModN (S.r * S.N) Y) : Prop :=
  ∃ (c₀ : Ω) (hc : c₀ ≠ 0) (R' : Subalgebra o Ω) (fg : R'.FG) (frac : ∀ x : Ω, ∃ a ∈ R', ∃ b ∈ R', x = a / b)
    (hth : ∀ x, c₀ * S.th x ∈ R') (hev : ∀ x k, c₀ * S.ev x k ∈ R') (ρ' : (S.rechart c₀ hc R' fg frac hth hev).Real),
    USame ρ ρ' (fun x => x) (RingHom.id _) ∧ ρ'.i₀ = ρ.i₀ ∧ R' ≤ M.O (y (closedPoint (PadicAlgCl p))) ∧
    ∃ y₀ : R' →+* PadicAlgCl p, (∀ a : R', y₀ a = M.val y a) ∧
      ∃ (u : ρ'.UTest p y₀) (lb : u.Lab) (j : u.D.toPre.X ≃+ Y), (∀ χ, lb.q χ = q (j χ)) ∧
        ∀ a χ, lb.yy a = QuotientAddGroup.mk χ → yy a = QuotientAddGroup.mk (j χ)

theorem same_of_uSame {o Ω o' Ω' : Type} [CommRing o] [Field Ω] [Algebra o Ω] [CommRing o'] [Field Ω'] [Algebra o' Ω']
    {S : ThetaSys o Ω} {S' : ThetaSys o' Ω'} {ρ : S.Real} {ρ' : S'.Real} {lab : S.Gam → S'.Gam} {φ : Ω →+* Ω'}
    (h : USame ρ ρ' lab φ) : Same ρ (fun _ => 𝟙 _) ρ' (fun _ => 𝟙 _) lab φ := by
  obtain ⟨P₀, a, a', h₁, h₂, l₁, l₂, hp⟩ := h
  exact ⟨P₀, a, a', fun _ => 𝟙 _, h₁, h₂, l₁, l₂, fun _ => ⟨by simp, by simp⟩, hp⟩

theorem GLab.conj [IsNoetherianRing o] (hM : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z) {σ : Ω →+* Ω} {g : S.Gam → S.Gam}
    (hg : IsConj ρ σ g) {s : M.Z ⟶ M.Z} (hs : M.pt ≫ s = spMap σ ≫ M.pt) {y : Sp (PadicAlgCl p) ⟶ M.Z}
    {yy yy' : S.Gam →+ ModN (S.r * S.N) Y} (h₁ : GLab ρ M q y yy) (h₂ : GLab ρ M q (y ≫ s) yy') :
    ∃ κ : Y ≃+ Y, (∀ x, q (κ x) = q x) ∧ ∀ b ν, yy (g b) = QuotientAddGroup.mk ν → yy' b = QuotientAddGroup.mk (κ ν) := by
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', hS, -, hR, y₀, hy₀, u, lb, j, hq, hyy⟩ := h₁
  obtain ⟨c₁, hc₁, R'', fg₁, frac₁, hth₁, hev₁, ρ'', hS₁, -, hR₁, y₁, hy₁, u', lb', j', hq', hyy'⟩ := h₂
  obtain ⟨P, b, t, hb, ht, l₁, lt, hp⟩ := hg
  obtain ⟨Q, b', b'', hb', hb'', l', l'', hpQ, -⟩ := GalTrans.exists_generic ρ _ ρ' _ ρ'' _ _ _ (same_of_uSame hS)
    (same_of_uSame hS₁) σ g P b t (fun _ => 𝟙 _) hb ht l₁ lt (fun _ => ⟨by simp, by simp⟩) hp
  obtain ⟨P₀, a, a', ha, ha', hL, hL', hlab, -⟩ := GalTrans.spread M hM ρ' ρ'' σ s hs y hR hR₁ y₀ y₁ hy₀ hy₁ u u' Q
    hb' hb'' l' l''
  obtain ⟨e, hψ, htor⟩ := GlobalTheory.T.exists_latticeIso_of_two_padicAlgCl_uniformisations _ _ ρ' ρ'' p y₀ y₁ u u' P₀ a a' ha ha' hL hL'
  haveI : CharZero (FractionRing u.V) := (algebraMap (FractionRing u.V) (PadicAlgCl p)).charZero
  haveI : CharZero u.V := (algebraMap u.V (FractionRing u.V)).charZero
  haveI : CharZero (FractionRing u'.V) := (algebraMap (FractionRing u'.V) (PadicAlgCl p)).charZero
  haveI : CharZero u'.V := (algebraMap u'.V (FractionRing u'.V)).charZero
  have hrN : 1 ≤ S.r * S.N := NeZero.one_le
  refine ⟨(j.symm.trans e).trans j', fun v => ?_, fun k ν hν => ?_⟩
  · obtain ⟨χ, rfl⟩ := j.surjective v
    simp only [AddEquiv.trans_apply, AddEquiv.symm_apply_apply]
    rw [← hq, ← hq']
    exact (neg_injective (Real.exp_injective (GlobalTheory.ZH.RealCase.psiNorm_unique u' (e χ) ((hψ χ _).1 (lb.q_eq χ))
      (lb'.q_eq (e χ))))).symm
  · obtain ⟨w₀, hw₀, e', e''⟩ := hpQ k
    obtain ⟨w, x, x', hw, hwa, hwa', hx, hx'⟩ := hlab _ _ w₀ hw₀ e' e''
    obtain ⟨f, hf1, hf2, -⟩ := uTors_closed u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) _ hrN
    obtain ⟨f', hf1', hf2', -⟩ := uTors_closed u'.V u'.complete u'.A u'.G u'.D u'.U (PadicAlgCl p) _ hrN
    obtain ⟨pk, hpk⟩ := hf2 x (GlobalTheory.LabelTorsion.pow_eq_one_of_over_label _ ρ' p y₀ u _ x hx)
    obtain ⟨pk', hpk'⟩ := hf2' x' (GlobalTheory.LabelTorsion.pow_eq_one_of_over_label _ ρ'' p y₁ u' _ x' hx')
    have Q₁ := (hf1 pk x).2 hpk.symm
    have Q₂ := (hf1' pk' x').2 hpk'.symm
    rw [hyy' k _ (lb'.yy_eq _ pk' x' Q₂ hx')]
    have c₀ : CongMod (S.r * S.N) (j.symm ν) pk.y := by
      simpa using cm_map j.symm.toAddMonoidHom (cm_of_mk (hν.symm.trans (hyy _ _ (lb.yy_eq _ pk x Q₁ hx))))
    exact cm_mk (cm_map j'.toAddMonoidHom (cm_trans (htor _ pk pk' x x' w hrN Q₁ Q₂ hw hwa hwa')
      (cm_symm (cm_map e.toAddMonoidHom c₀))))

theorem GLab.tendsto {y : Sp (PadicAlgCl p) ⟶ M.Z} {yy : S.Gam →+ ModN (S.r * S.N) Y} (h : GLab ρ M q y yy) :
    Filter.Tendsto q Filter.cofinite Filter.atTop := by
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', -, -, -, y₀, -, u, lb, j, hq, -⟩ := h
  have := lb.pos.comp j.symm.injective.tendsto_cofinite
  refine this.congr fun x => ?_
  simp [hq]

theorem GLab.exists_div [ArithBase o Ω] (hd : M.HasDiv S.th) {y : Sp (OO p) ⟶ M.Z} {z : M.Z} (hz : y (cPt p) = z)
    {yy : S.Gam →+ ModN (S.r * S.N) Y} (h : GLab ρ M q (gPt p ≫ y) yy) (hq0 : ∀ x, 0 ≤ q x) {k : ℕ} (hk : 2 ≤ k)
    (hkd : k ∣ S.r * S.N) : ∃ a : S.Gam, k • a = 0 ∧ M.Div S.th a z := by
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', -, -, hle, y₀, hy₀, u, l, j, hq, -⟩ := h
  have hint : ∀ a : o, ‖y₀ (algebraMap o R' a)‖ ≤ 1 := fun a => by
    rw [hy₀]
    exact RatModel.norm_val_le_one hz ((M.O z).algebraMap_mem a)
  obtain ⟨sc, h0, h₁, -, h₃⟩ := TestVal.exists_scale GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2 u l hint
  have hδ := (GlobalTheory.UnitTheta.closure_unit_theta GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2
    GlobalTheory.ZH.uTors_closed _ _ _ ρ' p y₀ u l hint).1
  have hle' : ∀ a, ‖y₀ ⟨c₀ * S.th a, hth a⟩‖ ≤ sc := fun a => by
    obtain ⟨w, -, hw⟩ := h₁ a
    refine hw.trans (mul_le_of_le_one_right h0 (Real.exp_le_one_iff.2 (neg_nonpos.2 (div_nonneg ?_ (by positivity)))))
    rw [hq]
    exact hq0 _
  have hsc : 0 < sc := hδ.trans_le (Real.iSup_le hle' h0)
  obtain ⟨a, -, ha, hn⟩ := h₃ k hk hkd 0 (zero_mem _)
  refine ⟨a, by simpa using ha, ?_⟩
  obtain ⟨d, hdv⟩ := hd z
  refine (hdv.div_iff_isUnit a).2 ((RatModel.norm_val_eq_one_iff hz (hdv.2 a)).1 ?_)
  have hs := RatModel.gPt_specializes hz
  have e : ‖y₀ ⟨c₀ * S.th a, hth a⟩‖ = ‖y₀ ⟨c₀ * S.th d, hth d⟩‖ * ‖M.val (gPt p ≫ y) (S.th a / S.th d)‖ := by
    rw [hy₀, hy₀, ← norm_mul, ← RatModel.val_mul (z := (gPt p ≫ y) (closedPoint (PadicAlgCl p)))
      (fun w => by rw [Subsingleton.elim w (closedPoint (PadicAlgCl p))]) (hle (hth d))
      (RatModel.O_le_of_specializes (hs _) (hdv.2 a))]
    congr 2
    have := hdv.1
    field_simp
  have hn' : ‖y₀ ⟨c₀ * S.th a, hth a⟩‖ = sc := hn
  have b₁ := RatModel.norm_val_le_one hz (hdv.2 a)
  have b₂ := hle' d
  refine le_antisymm b₁ (not_lt.1 fun hlt => ?_)
  have := mul_le_mul_of_nonneg_right b₂ (norm_nonneg (M.val (gPt p ≫ y) (S.th a / S.th d)))
  nlinarith

theorem GLab.norms [ArithBase o Ω] (hM : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z) {y : Sp (OO p) ⟶ M.Z} {z : M.Z}
    (hz : y (cPt p) = z) {d : S.Gam} (hd : M.Div S.th d z) {yy : S.Gam →+ ModN (S.r * S.N) Y}
    (h : GLab ρ M q (gPt p ≫ y) yy) {m : ℕ} (hm : S.N = m ^ 2) {a : S.Gam} {ν : Y} (ha : yy a = QuotientAddGroup.mk ν) :
    ((∀ χ, CongMod m χ ν → q ν ≤ q χ) → ∀ h ∈ yy.ker, ∀ (ξ : Ω) (n : ℕ), 0 < n → ξ ^ n = 1 →
      ‖M.val (gPt p ≫ y) (ξ * (partV S yy.ker ρ.i₀ (m • a) h / S.th d))‖ ≤ Real.exp (-q ν)) ∧
    ((∀ χ, CongMod m χ ν → χ ≠ ν → q ν < q χ) → ∀ k, 2 ≤ k → k ∣ m → ∃ h ∈ yy.ker, k • m • h = 0 ∧
      ∀ (ξ : Ω) (n : ℕ), 0 < n → ξ ^ n = 1 →
        ‖M.val (gPt p ≫ y) (ξ * (partV S yy.ker ρ.i₀ (m • a) h / S.th d))‖ = Real.exp (-q ν)) := by
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', -, hi, hle, y₀, hy₀, u, l, j, hq, hyy⟩ := h
  obtain ⟨ν, rfl⟩ := j.surjective ν
  have hker : yy.ker = l.yy.ker := by
    ext b
    obtain ⟨χ, hχ⟩ := QuotientAddGroup.mk_surjective (l.yy b)
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker, hyy b χ hχ.symm, ← hχ]
    exact ⟨fun h => cm_mk (by simpa using cm_map j.symm.toAddMonoidHom (cm_of_mk (y := 0) h)),
      fun h => cm_mk (y := 0) (by simpa using cm_map j.toAddMonoidHom (cm_of_mk (y := 0) h))⟩
  have hla : l.yy a = QuotientAddGroup.mk ν := by
    obtain ⟨χ, hχ⟩ := QuotientAddGroup.mk_surjective (l.yy a)
    rw [← hχ]
    exact cm_mk (by simpa using cm_map j.symm.toAddMonoidHom (cm_of_mk ((hyy a χ hχ.symm).symm.trans ha)))
  have hwt : l.wt (m • ν) = wtChar S (S.perp l.yy.ker) (m • a) :=
    AddMonoidHom.ext (l.wt_eq (m • a) _ (by rw [map_nsmul, hla]; rfl))
  have hint : ∀ a : o, ‖y₀ (algebraMap o R' a)‖ ≤ 1 := fun a => by
    rw [hy₀]
    exact RatModel.norm_val_le_one hz ((M.O z).algebraMap_mem a)
  have hδ := (GlobalTheory.UnitTheta.closure_unit_theta GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2
    GlobalTheory.ZH.uTors_closed _ _ _ ρ' p y₀ u l hint).1
  set z₀ := (gPt p ≫ y) (closedPoint (PadicAlgCl p))
  have hsp : ∀ w, (gPt p ≫ y) w ⤳ z₀ := RatModel.specializes_of_range_eq (RatModel.range_eq_singleton _ _)
  have hgz : z₀ ⤳ z := RatModel.gPt_specializes hz _
  have hd0 := hd.1
  have hδd : ‖y₀ ⟨c₀ * S.th d, hth d⟩‖ = (S.rechart c₀ hc R' fg frac hth hev).delta y₀ := by
    refine le_antisymm (le_ciSup (f := fun x => ‖y₀ ⟨c₀ * S.th x, hth x⟩‖) (Set.finite_range _).bddAbove d)
      (ciSup_le fun x => ?_)
    show ‖y₀ ⟨c₀ * S.th x, hth x⟩‖ ≤ _
    rw [hy₀, hy₀, show ((⟨c₀ * S.th x, hth x⟩ : R') : Ω) = S.th x / S.th d * (c₀ * S.th d) by field_simp,
      RatModel.val_mul hsp (RatModel.O_le_of_specializes hgz (hd.2 x)) (hle (hth d)), norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (RatModel.norm_val_le_one hz (hd.2 x))
  have key : ∀ (h : S.Gam) (ξ : Ω) (n : ℕ), 0 < n → ξ ^ n = 1 →
      ‖M.val (gPt p ≫ y) (ξ * (partV S yy.ker ρ.i₀ (m • a) h / S.th d))‖ *
        (S.rechart c₀ hc R' fg frac hth hev).delta y₀ =
      ‖∑ i, y₀ (algebraMap o R' (S.proj _ (l.wt (m • ν)) i ρ'.i₀)) * y₀ ⟨c₀ * S.ev h i, hev h i⟩‖ := by
    intro h ξ n hn hξ
    let v := RatModel.valHomOf (gPt p ≫ y) z₀ hsp
    have := RatModel.isIntegrallyClosed_O hM z₀
    obtain ⟨ξ', rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1
      (show IsIntegral (M.O z₀) ξ from ⟨_, Polynomial.monic_X_pow_sub_C (1 : M.O z₀) hn.ne', by simp [hξ]⟩)
    have n1 : ‖v ξ'‖ = 1 := by
      have e : ξ' ^ n = 1 := Subtype.ext hξ
      have := congrArg (fun t => ‖v t‖) e
      simp only [map_pow, norm_pow, map_one, norm_one] at this
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 this
    let A : R' := ∑ i, algebraMap o R' (S.proj _ (l.wt (m • ν)) i ρ'.i₀) * ⟨c₀ * S.ev h i, hev h i⟩
    have hA : (A : Ω) = c₀ * partV S yy.ker ρ.i₀ (m • a) h := by
      rw [hker, partV, ← hwt, ← hi, Finset.mul_sum]
      refine (map_sum R'.val _ _).trans (Finset.sum_congr rfl fun i _ => ?_)
      exact mul_left_comm _ _ _
    have hB : IsUnit (⟨c₀ * S.th d, hle (hth d)⟩ : M.O z₀) :=
      (RatModel.val_ne_zero_iff (RatModel.range_eq_singleton _ _) _).1 (by
        refine fun h0 => hδ.ne' ?_
        rw [← hδd, hy₀]
        exact norm_eq_zero.2 h0)
    have hF : partV S yy.ker ρ.i₀ (m • a) h / S.th d ∈ M.O z₀ := by
      have := mul_mem (hle A.2) ((RatModel.isUnit_O_iff _).1 hB).2
      rw [hA] at this
      convert this using 1
      field_simp
    have n2 : ‖M.val (gPt p ≫ y) (ξ' : Ω)‖ = 1 := (congrArg norm (RatModel.valHomOf_apply _ _ hsp ξ')).symm.trans n1
    have e₁ : ‖M.val (gPt p ≫ y) ((ξ' : Ω) * (partV S yy.ker ρ.i₀ (m • a) h / S.th d))‖ =
        ‖M.val (gPt p ≫ y) (partV S yy.ker ρ.i₀ (m • a) h / S.th d)‖ := by
      rw [RatModel.val_mul hsp ξ'.2 hF, norm_mul, n2, _root_.one_mul]
    have e₂ : y₀ A = M.val (gPt p ≫ y) (partV S yy.ker ρ.i₀ (m • a) h / S.th d) * y₀ ⟨c₀ * S.th d, hth d⟩ := by
      rw [hy₀, hy₀, ← RatModel.val_mul hsp hF (hle (hth d)), hA]
      congr 1
      field_simp
    refine (congrArg₂ (· * ·) e₁ hδd.symm).trans ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← norm_mul, ← e₂, map_sum]
    simp only [map_mul]
  have hm0 : (m : ℝ) ≠ 0 := by
    have := S.N_ge
    rintro h0
    obtain rfl : m = 0 := by exact_mod_cast h0
    omega
  have hqm : ∀ χ, l.q (m • χ) = (S.N : ℝ) * l.q χ := fun χ => by
    rw [← natCast_zsmul, QuadraticMap.map_smul, congrArg (Nat.cast : ℕ → ℝ) hm]
    simp [sq]
  have hN : (0 : ℝ) < S.N := by have := S.N_ge; positivity
  refine ⟨fun hmin h hh ξ n hn hξ => ?_, fun hmin k hk hkm => ?_⟩
  · have := WeightBound.main GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2 uTors_closed _ _ _ ρ' p y₀ u l hint
      (m • ν) (fun v₀ => by
        have e : S.N • v₀ = m • m • v₀ := by rw [← mul_smul, ← sq, ← hm]
        show _ ≤ l.q (m • ν + S.N • v₀)
        rw [e, ← smul_add, hqm, hqm, hq, hq]
        exact mul_le_mul_of_nonneg_left (hmin _ ⟨j v₀, by rw [map_add (f := _), map_nsmul]⟩) hN.le) h (hker ▸ hh) ρ'.i₀
    replace this := (key h ξ n hn hξ).trans_le this
    rw [mul_comm, mul_le_mul_iff_right₀ hδ, hqm, hq] at this
    refine this.trans (le_of_eq ?_)
    congr 2
    exact mul_div_cancel_left₀ _ hN.ne'
  · obtain ⟨h, hh, hk0, he⟩ := GlobalTheory.T.weightPart_attains_bound_unique_shortest_vector u l hint m k hm hk hkm ν (fun χ hχ => by
      rw [hq, hq]
      exact hmin _ ⟨j χ, by rw [map_add (f := _), map_nsmul]⟩ fun e => hχ (by simpa using j.injective e))
    refine ⟨h, hker ▸ hh, hk0, fun ξ n hn hξ => ?_⟩
    have := (key h ξ n hn hξ).trans he
    rwa [mul_comm, mul_right_inj' hδ.ne', hq] at this

end GlobalTheory.UPoinc.USum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryThetaFourierClassSumsDeeperIntegral
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc.USum

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {cf : Coeff l} {C : UCompact Xo cf}

def qf {X : USetup C} {p : ℕ} [Fact p.Prime] {z : X.M.Z} (ct : UCTrait X p z) (x : ct.T.P.D.toPre.X) : ℝ :=
  ct.sc * (ct.T.be x x : ℝ) / 2

theorem gLab_of {X : USetup C} {p : ℕ} [Fact p.Prime] {z : X.M.Z} {ct : UCTrait X p z} {yy} (h : UIsLab X ct yy) :
    GLab X.ρ X.M (qf ct) (gPt p ≫ ct.y) yy := by
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', -, hS, hi, -, hR, -, -, -, -, -, -, -, y₀, hy₀, u, lb, j, hq, hyy, -⟩ := h
  exact ⟨c₀, hc, R', fg, frac, hth, hev, ρ', hS, hi, hR, y₀, hy₀, u, lb, j, hq, hyy⟩

theorem normal (X : USetup C) : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X.M.Z := GlobalTheory.IsNormalScheme.pred _ (h := X.normal)

theorem be_pos (T : UTrait Xo cf) (x : T.P.D.toPre.X) (hx : x ≠ 0) : 0 < T.be x x := by
  obtain ⟨j, hj⟩ := IsMonomial.exists_pos (IsLocalRing.maximalIdeal.isMaximal T.V).ne_top T.mono hx
  fin_cases j
  simpa using hj

theorem be_nonneg (T : UTrait Xo cf) (x : T.P.D.toPre.X) : 0 ≤ T.be x x := by
  by_cases hx : x = 0
  · simp [hx]
  · exact (be_pos T x hx).le

theorem norm_unif {X : USetup C} {p : ℕ} [Fact p.Prime] {z : X.M.Z} (c : UCTrait X p z) :
    0 < ‖c.ι (algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ)‖ ∧ ‖c.ι (algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ)‖ < 1 := by
  set x := algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ with hx
  have h0 : x ≠ 0 := fun h => c.T.irr.ne_zero ((map_eq_zero_iff _ (IsFractionRing.injective _ _)).1 h)
  refine ⟨norm_pos_iff.2 ((map_ne_zero c.ι).2 h0), not_le.1 fun h => ?_⟩
  obtain ⟨v, hv⟩ := (c.int x⁻¹).1 (by rw [map_inv₀, norm_inv]; exact inv_le_one_of_one_le₀ h)
  refine c.T.irr.not_isUnit (IsUnit.of_mul_eq_one v (IsFractionRing.injective _ (FractionRing c.T.V) ?_))
  rw [map_mul, map_one, hv, ← hx, mul_inv_cancel₀ h0]

theorem sc_pos {X : USetup C} {p : ℕ} [Fact p.Prime] {z : X.M.Z} (c : UCTrait X p z) : 0 < c.sc :=
  neg_pos.2 (Real.log_neg (norm_unif c).1 (norm_unif c).2)

theorem exists_root {X : USetup C} {p : ℕ} [Fact p.Prime] {z : X.M.Z} (c : UCTrait X p z) :
    ∃ (s : PadicAlgCl p) (n : c.T.P.D.toPre.X → ℕ), ∀ x, ‖s‖ ^ n x = Real.exp (-qf c x) := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (c.ι (algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ)) two_pos
  have h := (norm_unif c).1
  refine ⟨s, fun x => (c.T.be x x).toNat, fun x => ?_⟩
  have h0 : 0 < ‖s‖ := norm_pos_iff.2 fun h0 => by simp [← hs, h0] at h
  have e : (((c.T.be x x).toNat : ℕ) : ℝ) = (c.T.be x x : ℝ) := by exact_mod_cast Int.toNat_of_nonneg (be_nonneg c.T x)
  rw [qf, UCTrait.sc, ← hs, norm_pow, Real.log_pow, ← Real.exp_log (pow_pos h0 _), Real.log_pow, e]
  congr 1
  push_cast
  ring

theorem three_le_level (X : USetup C) : 3 ≤ X.S.r * X.S.N := by
  have hr := X.S.r_pos
  have h2 := X.S.N_ge
  obtain ⟨k, hk⟩ := odd_level X.ρ
  nlinarith [show 3 ≤ X.S.N by omega]

theorem eq_of_qf {X : USetup C} {p : ℕ} [Fact p.Prime] {z : X.M.Z} (c : UCTrait X p z)
    (κ : c.T.P.D.toPre.X ≃+ c.T.P.D.toPre.X) (hq : ∀ x, qf c (κ x) = qf c x) (L : ℕ) (hL : 3 ≤ L)
    (hc : ∀ x, CongMod L (κ x) x) (x : c.T.P.D.toPre.X) : κ x = x := by
  have hd : ∀ x, c.T.be (κ x) (κ x) = c.T.be x x := fun x => by
    have h : c.sc * (c.T.be (κ x) (κ x) : ℝ) = c.sc * (c.T.be x x : ℝ) := by
      have := hq x
      simp only [qf] at this
      linarith
    exact_mod_cast mul_left_cancel₀ (sc_pos c).ne' h
  let β : LinearMap.BilinForm ℤ c.T.P.D.toPre.X := c.T.be + c.T.be.flip
  have hβ : ∀ u v, β u v = c.T.be u v + c.T.be v u := fun u v => rfl
  let e : c.T.P.D.toPre.X ≃ₗ[ℤ] c.T.P.D.toPre.X := κ.toIntLinearEquiv
  have hiso : ∀ u v, β (e u) (e v) = β u v := by
    intro u v
    have huv := hd (u + v)
    simp only [map_add (f := _), LinearMap.add_apply] at huv
    rw [hd u, hd v] at huv
    rw [hβ, hβ]
    show c.T.be (κ u) (κ v) + c.T.be (κ v) (κ u) = _
    linarith
  have he := eq_refl_of_isometry_congMod _ β (fun u hu => by rw [hβ]; have := be_pos c.T u hu; linarith) e hiso L hL hc
  simpa [e] using congrArg (fun f : c.T.P.D.toPre.X ≃ₗ[ℤ] c.T.P.D.toPre.X => f x) he

theorem congMod_cancel {Y : Type} [AddCommGroup Y] [Module.Free ℤ Y] {M d L : ℕ} (hm : M = d * L) (hd : d ≠ 0) {x y : Y}
    (h : CongMod M (d • x) (d • y)) : CongMod L x y := by
  obtain ⟨w, hw⟩ := h
  refine ⟨w, smul_right_injective Y (show (d : ℤ) ≠ 0 by exact_mod_cast hd) ?_⟩
  simp only [natCast_zsmul]
  rw [hw, hm, mul_smul, smul_add]

theorem exists_eq_smul_of_smul_eq_zero {L k : ℕ} (hL : 0 < L) (hk : k ∣ L) (a : ZMod L) (ha : k • a = 0) :
    ∃ x : ZMod L, (L / k) • x = a := by
  obtain ⟨d, rfl⟩ := hk
  have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hL)
  haveI : NeZero (k * d) := ⟨hL.ne'⟩
  rw [Nat.mul_div_cancel_left _ hk]
  have h : ((k * a.val : ℕ) : ZMod (k * d)) = 0 := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val, ← nsmul_eq_mul, ha]
  obtain ⟨e, he⟩ := Nat.dvd_of_mul_dvd_mul_left hk ((ZMod.natCast_eq_zero_iff _ _).1 h)
  exact ⟨e, by rw [nsmul_eq_mul, ← Nat.cast_mul, ← he, ZMod.natCast_zmod_val]⟩

theorem root_mem_O (X : USetup C) (z : X.M.Z) {u : X.Ω₁} {k : ℕ} (hk : 0 < k) (hu : u ^ k = 1) : u ∈ X.M.O z := by
  have := RatModel.isIntegrallyClosed_O (normal X) z
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1
    (show IsIntegral (X.M.O z) u from ⟨_, Polynomial.monic_X_pow_sub_C (1 : X.M.O z) hk.ne', by simp [hu]⟩)
  exact hy ▸ y.2

theorem prime_eq_of_cen {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω} {z : M.Z} {p p' : ℕ}
    [hp : Fact p.Prime] [hp' : Fact p'.Prime] {y : Sp (OO p) ⟶ M.Z} {y' : Sp (OO p') ⟶ M.Z} (h : y (cPt p) = z)
    (h' : y' (cPt p') = z) : p = p' := by
  have key : ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), y (cPt p) = z → ¬ IsUnit (p : M.O z) := fun p _ y h => by
    rw [← RatModel.isUnit_valLoc_iff y h, map_natCast, not_isUnit_OO_iff]
    have e : (((p : OO p)) : PadicAlgCl p) = algebraMap ℚ_[p] (PadicAlgCl p) p := by simp
    rw [e, norm_algebraMap']
    exact Padic.norm_p_lt_one
  by_contra hne
  obtain ⟨a, b, hab⟩ := (Nat.Coprime.isCoprime ((Nat.coprime_primes hp.out hp'.out).2 hne)).map (Int.castRingHom (M.O z))
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add (hab ▸ isUnit_one) with u | u
  · exact key p y h (by simpa using isUnit_of_mul_isUnit_right u)
  · exact key p' y' h' (by simpa using isUnit_of_mul_isUnit_right u)

theorem exists_div_torsion (hpq : 1 ≤ Dw.p + Dw.q) (X : USetup C) (z : X.M.Z) {k : ℕ} (hk : 2 ≤ k)
    (hd : k ∣ X.S.r * X.S.N) : ∃ a : X.S.Gam, k • a = 0 ∧ X.M.Div X.S.th a z := by
  haveI := X.M.qc
  haveI : CompactSpace X.M.Z := QuasiCompact.compactSpace_of_compactSpace X.M.s
  obtain ⟨z', hz', hcl⟩ := (isClosed_closure (s := {z})).exists_closed_singleton ⟨z, subset_closure rfl⟩
  have hsp : z ⤳ z' := specializes_iff_mem_closure.2 hz'
  obtain ⟨p, _, y₀, hy₀, -⟩ := exists_cen_main _ _ X.M z' hcl ⊤ ⟨z, trivial⟩
  obtain ⟨U, hU, hct⟩ := UCTraitEx.exists_uCTrait_of_open E H Dw hpq l Xo cf C X p
  obtain ⟨p', _, y, hy, hyU⟩ := exists_cen_main _ _ X.M z' hcl U hU
  obtain rfl : p = p' := prime_eq_of_cen hy₀ hy
  obtain ⟨ct, -⟩ := hct y hyU
  obtain ⟨wi⟩ := nonempty_uWit X
  obtain ⟨yy, hyy⟩ := GlobalTheory.T.exists_labels_unitaryClassicalTrait E H Dw hpq l Xo cf C X wi p _ ct
  obtain ⟨a, ha, hdv⟩ := (gLab_of hyy.uIsLab).exists_div X.hasDiv ct.cen
    (fun x => div_nonneg (mul_nonneg (sc_pos ct).le (by exact_mod_cast be_nonneg ct.T x)) zero_le_two) hk hd
  exact ⟨a, ha, hdv.of_specializes (hy ▸ hsp)⟩

variable {X₁ : USetup C} (D : UDeep X₁)

theorem level_dvd : X₁.S.r * X₁.S.N ∣ D.X.S.r * D.X.S.N :=
  (D.dvd.trans (D.sq ▸ dvd_pow_self D.m two_ne_zero)).trans (dvd_mul_left _ _)

theorem exists_lab {a : D.X.S.Gam} (ha : (X₁.S.r * X₁.S.N) • a = 0) : ∃ b, D.lab b = a := by
  choose x hxa using fun s => exists_eq_smul_of_smul_eq_zero (NeZero.pos _) (level_dvd D) (a s) (congrFun ha s)
  obtain ⟨b, hb⟩ := D.lab_range x
  exact ⟨b, hb.trans (funext hxa)⟩

theorem div_deep (hpq : 1 ≤ Dw.p + Dw.q) {z₁ : X₁.M.Z} {x₀ : X₁.S.Gam} (hx : X₁.M.Div X₁.S.th x₀ z₁) {z' : D.X.M.Z}
    (hz' : D.q z' = z₁) : D.X.M.Div D.X.S.th (D.lab x₀) z' := by
  obtain ⟨a, ha, hdv⟩ := exists_div_torsion hpq D.X z' ((three_le_level X₁).trans' (by norm_num)) (level_dvd D)
  obtain ⟨b, rfl⟩ := exists_lab D ha
  obtain ⟨k, hk, e⟩ := DivDeep.same_ratio (same_of_uSame D.same) x₀ b
  set φ := algebraMap X₁.Ω₁ D.X.Ω₁
  have h₁ : φ (X₁.S.th x₀) ≠ 0 := (map_ne_zero φ).2 hx.1
  have h₂ := hdv.1
  have h₃ : D.X.S.th (D.lab x₀) * φ (X₁.S.th b) ≠ 0 := fun h => by
    rw [h, zero_pow hk.ne'] at e
    exact pow_ne_zero k (mul_ne_zero h₂ h₁) e.symm
  have h₄ := left_ne_zero_of_mul h₃
  have h₅ := right_ne_zero_of_mul h₃
  have m₁ : D.X.S.th (D.lab b) * φ (X₁.S.th x₀) / (D.X.S.th (D.lab x₀) * φ (X₁.S.th b)) ∈ D.X.M.O z' :=
    root_mem_O D.X z' hk (by rw [div_pow, e, div_self (pow_ne_zero k (mul_ne_zero h₂ h₁))])
  have m₂ : φ (X₁.S.th b / X₁.S.th x₀) ∈ D.X.M.O z' := by
    obtain ⟨U, f, hU, hf⟩ := hx.2 b
    refine ⟨D.q ⁻¹ᵁ U, D.q.app U f, show D.q z' ∈ U from hz' ▸ hU, ?_⟩
    refine (GlobalTheory.Points.valR_comp D.X.M.pt D.q U f).symm.trans ?_
    rw [D.gen, ← hf]
    exact GlobalTheory.Points.valR_spMap_comp _ X₁.M.pt U (X₁.M.top_le_preimage_pt ⟨_, hU⟩) f
  refine ⟨h₄, fun j => ?_⟩
  have := mul_mem (hdv.2 j) (mul_mem m₁ m₂)
  convert this using 1
  rw [map_div₀]
  field_simp

theorem exists_cofactor : ∃ d, d ≠ 0 ∧ D.X.S.r * D.X.S.N = d * (X₁.S.r * X₁.S.N) ∧
    D.X.S.r * D.X.S.N / (X₁.S.r * X₁.S.N) = d := by
  refine ⟨_, fun h => ?_, (Nat.div_mul_cancel (level_dvd D)).symm, rfl⟩
  have := Nat.div_mul_cancel (level_dvd D)
  rw [h, zero_mul] at this
  exact NeZero.ne _ this.symm

theorem gLab_lift {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z} (ct : UCTrait X₁ p z₁) {y : Sp (OO p) ⟶ D.X.M.Z}
    {h : y ≫ D.q = ct.y} {yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) ct.T.P.D.toPre.X}
    (hl : UIsLab D.X (D.lift ct y h) yy) : GLab D.X.ρ D.X.M (qf ct) (gPt p ≫ y) yy := by
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', -, hS, hi, -, hR, -, -, -, -, -, -, -, y₀, hy₀, u, lb, j, hq, hyy, -⟩ := hl
  exact ⟨c₀, hc, R', fg, frac, hth, hev, ρ', hS, hi, hR, y₀, hy₀, u, lb, j, fun χ => by rw [hq, qf]; rfl, hyy⟩

section Labels

variable {Y : Type} [AddCommGroup Y] {yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) Y}
  {yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) Y}

theorem exists_lift (hs : Function.Surjective yy) (hc : D.Compat yy₁ yy) [Module.Free ℤ Y] {κ : X₁.S.Gam}
    (hκ : κ ∈ yy₁.ker) : ∃ h ∈ yy.ker, D.m • h = D.lab κ := by
  have hL : D.X.S.r * D.X.S.N = D.m * (D.X.S.r * D.m) := by
    have := D.sq
    rw [this]; ring
  have hm : D.m ≠ 0 := fun h => NeZero.ne _ (hL.trans (by rw [h, zero_mul]))
  have hz : ∀ x : D.X.S.Gam, (D.X.S.r * D.X.S.N) • x = 0 := fun x => by
    funext i
    simp [nsmul_eq_mul]
  have h₀ : (D.X.S.r * D.m) • D.lab κ = 0 := by
    obtain ⟨c, hc⟩ := D.dvd
    have : (X₁.S.r * X₁.S.N) • κ = 0 := by
      funext i
      simp [nsmul_eq_mul]
    rw [show D.X.S.r * D.m = D.X.S.r * c * (X₁.S.r * X₁.S.N) by rw [hc]; ring, mul_smul, ← map_nsmul, this, map_zero,
      smul_zero]
  choose x hx using fun s => exists_eq_smul_of_smul_eq_zero (NeZero.pos _) ⟨D.m, hL.trans (mul_comm _ _)⟩ (D.lab κ s)
    (congrFun h₀ s)
  have hx' : D.m • x = D.lab κ := by
    have e : D.X.S.r * D.X.S.N / (D.X.S.r * D.m) = D.m :=
      Nat.div_eq_of_eq_mul_left (Nat.mul_pos D.X.S.r_pos (Nat.pos_of_ne_zero hm)) hL
    rw [e] at hx
    exact funext hx
  obtain ⟨ν, hν⟩ := QuotientAddGroup.mk_surjective (yy x)
  have h₁ : CongMod (D.X.S.r * D.X.S.N) (D.m • ν) (D.m • 0) := cm_of_mk (by
    rw [QuotientAddGroup.mk_nsmul, hν, ← map_nsmul, hx', hc κ 0 hκ, smul_zero, smul_zero])
  obtain ⟨w, hw⟩ := congMod_cancel hL hm h₁
  obtain ⟨x', hx''⟩ := hs (QuotientAddGroup.mk w)
  refine ⟨x - (D.X.S.r * D.m) • x', ?_, by rw [smul_sub, ← mul_smul, ← hL, hz, sub_zero, hx']⟩
  rw [AddMonoidHom.mem_ker, map_sub, map_nsmul, hx'', ← hν, hw, zero_add, QuotientAddGroup.mk_nsmul, sub_self]

theorem mem_ker_of_lab (hc : D.Compat yy₁ yy) [Module.Free ℤ Y] {κ : X₁.S.Gam} (hκ : D.lab κ ∈ yy.ker) : κ ∈ yy₁.ker := by
  obtain ⟨d, hd, e, e'⟩ := exists_cofactor D
  obtain ⟨ν, hν⟩ := QuotientAddGroup.mk_surjective (yy₁ κ)
  have := hc κ ν hν.symm
  rw [e', show yy (D.lab κ) = QuotientAddGroup.mk (d • 0) by rw [smul_zero]; exact hκ] at this
  exact hν.symm.trans (cm_mk (y := 0) (cm_symm (congMod_cancel e hd (cm_of_mk this))))

theorem wtChar_eq (hs : Function.Surjective yy) {a a' : D.X.S.Gam} {ν ν' : Y} (ha : yy a = QuotientAddGroup.mk ν)
    (ha' : yy a' = QuotientAddGroup.mk ν') (h : CongMod D.m ν ν') :
    wtChar D.X.S (D.X.S.perp yy.ker) (D.m • a) = wtChar D.X.S (D.X.S.perp yy.ker) (D.m • a') := by
  obtain ⟨w, rfl⟩ := h
  obtain ⟨b, hb⟩ := hs (QuotientAddGroup.mk w)
  have hk : a - a' - D.m • b ∈ yy.ker := by
    rw [AddMonoidHom.mem_ker, map_sub, map_sub, map_nsmul, ha, ha', hb, QuotientAddGroup.mk_add, QuotientAddGroup.mk_nsmul]
    abel
  refine AddMonoidHom.ext fun t => ?_
  have e : eStd D.X.S.g _ t.1 (D.m • a) = eStd D.X.S.g _ t.1 (D.m • a') + (D.m * D.m) • eStd D.X.S.g _ t.1 b +
      D.m • eStd D.X.S.g _ t.1 (a - a' - D.m • b) := by
    simp only [eStd, Pi.smul_apply, Pi.sub_apply, nsmul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib, Nat.cast_mul,
      Pi.mul_apply, Pi.natCast_apply]
    exact Finset.sum_congr rfl fun _ _ => by ring
  show ZMod.castHom (dvd_mul_left D.X.S.N D.X.S.r) (ZMod D.X.S.N) (eStd D.X.S.g _ t.1 (D.m • a)) =
    ZMod.castHom (dvd_mul_left D.X.S.N D.X.S.r) (ZMod D.X.S.N) (eStd D.X.S.g _ t.1 (D.m • a'))
  rw [e, t.2 _ hk, smul_zero, add_zero, map_add (f := _), map_nsmul, ← sq, ← D.sq, nsmul_eq_mul D.X.S.N, ZMod.natCast_self, zero_mul,
    add_zero]

end Labels

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf), ∀ (X₁ : USetup C) (D : UDeep X₁) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (z₂ : D.X.M.Z), D.q z₂ = z₁ → ∃ (f : D.X.S.Gam → X₁.S.HH X₁.M z₁ → D.X.Ω₁) (t : ∀ (ct : UCTrait X₁ p z₁) (_ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) ct.T.P.D.toPre.X), ct.T.P.D.toPre.X → X₁.S.HH X₁.M z₁ → PadicAlgCl p), (∀ a κ (z' : D.X.M.Z), D.q z' = z₁ → f a κ ∈ D.X.M.O z') ∧ ∀ (ct : UCTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) ct.T.P.D.toPre.X), UIsLab X₁ ct yy₁ → (∀ μ κ, ‖t ct yy₁ μ κ‖ ≤ Real.exp (-(ct.sc * (ct.T.be μ μ : ℝ) / 2))) ∧ (∀ μ, ∃ κ, ‖t ct yy₁ μ κ‖ = Real.exp (-(ct.sc * (ct.T.be μ μ : ℝ) / 2))) ∧ ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = ct.y), y (cPt p) = z₂ → ∀ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) ct.T.P.D.toPre.X, UIsLab D.X (D.lift ct y h) yy → D.Compat yy₁ yy → ∀ a ν κ, yy a = QuotientAddGroup.mk ν → ∀ δ : ℝ, 0 < δ → ∃ S₀ : Finset ct.T.P.D.toPre.X, ∀ S : Finset ct.T.P.D.toPre.X, (∀ μ ∈ S, CongMod D.m μ ν) → (∀ μ ∈ S₀, CongMod D.m μ ν → μ ∈ S) → ‖D.X.M.val (gPt p ≫ y) (f a κ) - ∑ μ ∈ S, t ct yy₁ μ κ‖ ≤ δ := by
  intro E _ _ _ H Dw hpq l Xo cf C X₁ D p _ z₁ z₂ hz
  classical
  obtain ⟨x₀, hx₀⟩ := X₁.hasDiv z₁
  have hd₂ := div_deep D hpq hx₀ hz
  obtain ⟨f, hf₀, hf₁, hf₂, hf₃⟩ := exists_parts D.same D.sq (D.X.S.HH D.X.M z₂) x₀ hx₀.1 hd₂.1
  have key : ∀ (ct : UCTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) ct.T.P.D.toPre.X), UIsLab X₁ ct yy₁ →
      ∃ t : ct.T.P.D.toPre.X → X₁.S.HH X₁.M z₁ → PadicAlgCl p, (∀ μ κ, ‖t μ κ‖ ≤ Real.exp (-qf ct μ)) ∧
        (∀ μ, ∃ κ, ‖t μ κ‖ = Real.exp (-qf ct μ)) ∧
        ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = ct.y), y (cPt p) = z₂ →
          ∀ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) ct.T.P.D.toPre.X, UIsLab D.X (D.lift ct y h) yy →
          D.Compat yy₁ yy → ∀ a ν (κ : X₁.S.HH X₁.M z₁), yy a = QuotientAddGroup.mk ν → ∀ δ : ℝ, 0 < δ →
          ∃ S₀ : Finset ct.T.P.D.toPre.X, ∀ S : Finset ct.T.P.D.toPre.X, (∀ μ ∈ S, CongMod D.m μ ν) →
            (∀ μ ∈ S₀, CongMod D.m μ ν → μ ∈ S) →
            ‖D.X.M.val (gPt p ≫ y) (f (D.m • a) κ) - ∑ μ ∈ S, t μ κ‖ ≤ δ := by
    intro ct yy₁ h₁
    obtain ⟨s, n, hs⟩ := exists_root ct
    by_cases he : ∃ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = ct.y), y (cPt p) = z₂ ∧
        ∃ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) ct.T.P.D.toPre.X, UIsLab D.X (D.lift ct y h) yy ∧ D.Compat yy₁ yy
    swap
    · exact ⟨fun μ _ => s ^ n μ, fun μ _ => ((norm_pow _ _).trans (hs μ)).le, fun μ => ⟨0, (norm_pow _ _).trans (hs μ)⟩,
        fun y h hy yy h₂ hc => absurd ⟨y, h, hy, yy, h₂, hc⟩ he⟩
    obtain ⟨y₀, h₀, hy₀, yy₀, l₀, c₀⟩ := he
    obtain ⟨on₁, k₁⟩ := uIsLab_onto_and_ker E H Dw hpq l Xo cf C X₁ p _ ct yy₁ h₁
    obtain ⟨on₀, k₀⟩ := uIsLab_onto_and_ker E H Dw hpq l Xo cf C D.X p _ (D.lift ct y₀ h₀) yy₀ l₀
    replace k₀ : yy₀.ker = D.X.S.HH D.X.M z₂ := k₀.trans (congrArg _ hy₀)
    replace on₀ : Function.Surjective yy₀ := on₀
    have g₀ : GLab D.X.ρ D.X.M (qf ct) (gPt p ≫ y₀) yy₀ := gLab_lift D ct l₀
    choose α hα using fun ν : ct.T.P.D.toPre.X => on₀ (QuotientAddGroup.mk ν)
    have hcl : ∀ {a a' ν ν'}, yy₀ a = QuotientAddGroup.mk ν → yy₀ a' = QuotientAddGroup.mk ν' → CongMod D.m ν ν' →
        f (D.m • a) = f (D.m • a') := fun ha ha' h => hf₂ _ _ (by rw [← k₀]; exact wtChar_eq D on₀ ha ha' h)
    obtain ⟨t, ht₁, ht₂, ht₃⟩ := GlobalTheory.T.lattice_class_sums_of_terms_prescribed_norms p _ (X₁.S.HH X₁.M z₁) D.m (qf ct) s n (gLab_of h₁).tendsto hs
      (fun ν κ => D.X.M.val (gPt p ≫ y₀) (f (D.m • α ν) κ))
      (fun ν ν' κ h => by simp only [hcl (hα ν) (hα ν') h])
      (fun ν κ hmin => by
        obtain ⟨h, hh, e⟩ := exists_lift D on₀ c₀ (k₁.ge κ.2)
        obtain ⟨ξ, k, hk, hξ, e'⟩ := hf₁ (D.m • α ν) κ h (k₀.le hh) e
        simp only [e', ← k₀]
        exact (g₀.norms (normal D.X) hy₀ hd₂ D.sq (hα ν)).1 hmin h hh ξ k hk hξ)
      (fun ν hmin => by
        obtain ⟨h, hh, e, hn⟩ := (g₀.norms (normal D.X) hy₀ hd₂ D.sq (hα ν)).2 hmin _
          ((three_le_level X₁).trans' (by norm_num)) D.dvd
        obtain ⟨b, hb⟩ := exists_lab D e
        have hb' : b ∈ yy₁.ker := mem_ker_of_lab D c₀ (by rw [hb]; exact nsmul_mem hh _)
        obtain ⟨ξ, k, hk, hξ, e'⟩ := hf₁ (D.m • α ν) b h (k₀.le hh) hb.symm
        refine ⟨⟨b, k₁.le hb'⟩, ?_⟩
        simp only [e', ← k₀]
        exact hn ξ k hk hξ)
    refine ⟨t, ht₁, ht₂, fun y h hy yy h₂ hc a ν κ ha => ?_⟩
    obtain ⟨-, k₂⟩ := uIsLab_onto_and_ker E H Dw hpq l Xo cf C D.X p _ (D.lift ct y h) yy h₂
    replace k₂ : yy.ker = D.X.S.HH D.X.M z₂ := k₂.trans (congrArg _ hy)
    haveI := D.fd
    haveI := D.gal
    obtain ⟨σ, s', hs', e, hv⟩ := GlobalTheory.T.exists_galois_aut_conjugate_field_points_cover _ _ _ _ X₁.M D.X.M D.q (normal X₁) (normal D.X) D.fin D.gen (PadicAlgCl p)
      (gPt p ≫ y₀) (gPt p ≫ y) (by rw [Category.assoc, Category.assoc, h₀, h])
    obtain ⟨g, hg, hgl, hgf⟩ := hf₃ σ σ.surjective (RingHom.ext σ.commutes)
    haveI := D.X.ar.ded
    have g₂ : GLab D.X.ρ D.X.M (qf ct) (gPt p ≫ y) yy := gLab_lift D ct h₂
    obtain ⟨κ', hκq, hκ⟩ := g₀.conj (normal D.X) hg hs' (by rw [e]; exact g₂)
    obtain ⟨d, hd, e₁, e₂⟩ := exists_cofactor D
    have hid := eq_of_qf ct κ' hκq _ (three_le_level X₁) fun x => by
      obtain ⟨b, hb⟩ := on₁ (QuotientAddGroup.mk x)
      have := (hκ (D.lab b) _ (by rw [hgl]; exact c₀ b x hb)).symm.trans (hc b x hb)
      rw [e₂, map_nsmul] at this
      exact congMod_cancel e₁ hd (cm_of_mk this)
    have hyy : ∀ b, yy₀ (g b) = yy b := fun b => by
      obtain ⟨μ, hμ⟩ := QuotientAddGroup.mk_surjective (yy₀ (g b))
      rw [hκ b μ hμ.symm, hid, hμ]
    have := hgf (fun b => by rw [← k₀, AddMonoidHom.mem_ker, hyy, k₀, ← k₂, AddMonoidHom.mem_ker]) (D.m • a) κ
    rw [hv, show σ (f (D.m • a) κ) = _ from this, map_nsmul, hcl ((hyy a).trans ha) (hα ν) ⟨0, by simp⟩]
    exact ht₃ ν κ
  refine ⟨fun a κ => f (D.m • a) κ, fun ct yy₁ => if h : UIsLab X₁ ct yy₁ then (key ct yy₁ h).choose else fun _ _ => 0,
    fun a κ z' hz' => ?_, fun ct yy₁ hl => ?_⟩
  · by_cases he : ∃ h ∈ D.X.S.HH D.X.M z₂, D.m • h = D.lab κ
    · obtain ⟨h, hh, e⟩ := he
      obtain ⟨ξ, k, hk, hξ, e'⟩ := hf₁ (D.m • a) κ h hh e
      simp only [e', partV, Finset.sum_div]
      refine mul_mem (root_mem_O D.X z' hk hξ) (sum_mem fun j _ => ?_)
      obtain ⟨b, u, k', hk', hu, e''⟩ := EvRoot.ev_eq_root_mul_th _ _ D.X.S D.X.ρ h j
      rw [mul_div_assoc, e'', mul_div_assoc]
      exact mul_mem (Subalgebra.algebraMap_mem _ _) (mul_mem (root_mem_O D.X z' hk' hu) ((div_deep D hpq hx₀ hz').2 b))
    · simp only [hf₀ _ _ he]
      exact zero_mem _
  · simp only [dif_pos hl]
    exact (key ct yy₁ hl).choose_spec

end GlobalTheory.UPoinc.USum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryThetaFourierClassSumsDeeperIntegralStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_thetaFourier_classSums_deeper_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf), ∀ (X₁ : USetup C) (D : UDeep X₁) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (z₂ : D.X.M.Z), D.q z₂ = z₁ → ∃ (f : D.X.S.Gam → X₁.S.HH X₁.M z₁ → D.X.Ω₁) (t : ∀ (ct : UCTrait X₁ p z₁) (_ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) ct.T.P.D.toPre.X), ct.T.P.D.toPre.X → X₁.S.HH X₁.M z₁ → PadicAlgCl p), (∀ a κ (z' : D.X.M.Z), D.q z' = z₁ → f a κ ∈ D.X.M.O z') ∧ ∀ (ct : UCTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) ct.T.P.D.toPre.X), UIsLab X₁ ct yy₁ → (∀ μ κ, ‖t ct yy₁ μ κ‖ ≤ Real.exp (-(ct.sc * (ct.T.be μ μ : ℝ) / 2))) ∧ (∀ μ, ∃ κ, ‖t ct yy₁ μ κ‖ = Real.exp (-(ct.sc * (ct.T.be μ μ : ℝ) / 2))) ∧ ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = ct.y), y (cPt p) = z₂ → ∀ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) ct.T.P.D.toPre.X, UIsLab D.X (D.lift ct y h) yy → D.Compat yy₁ yy → ∀ a ν κ, yy a = QuotientAddGroup.mk ν → ∀ δ : ℝ, 0 < δ → ∃ S₀ : Finset ct.T.P.D.toPre.X, ∀ S : Finset ct.T.P.D.toPre.X, (∀ μ ∈ S, CongMod D.m μ ν) → (∀ μ ∈ S₀, CongMod D.m μ ν → μ ∈ S) → ‖D.X.M.val (gPt p ≫ y) (f a κ) - ∑ μ ∈ S, t ct yy₁ μ κ‖ ≤ δ := by
  first | exact @GlobalTheory.UPoinc.USum.main | exact GlobalTheory.UPoinc.USum.main | (intros; apply GlobalTheory.UPoinc.USum.main <;> assumption)
end
