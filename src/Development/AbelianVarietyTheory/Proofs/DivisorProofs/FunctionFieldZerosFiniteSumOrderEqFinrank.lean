module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveRootPowUnitSubProdProperties
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexUpLatEqSq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldPlaceRestrictionExistsPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlue
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitLemmaResiduallyUnipotentViaCayley

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldZerosFiniteSumOrderEqFinrank
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniquePlaceOrdEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniquePlaceOrdEqOne
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef

open Polynomial

variable {k L : Type} [Field k] [Field L] [Algebra k L]

theorem place_aeval_le_one (x : L) (u : Place k L) (hx : u.1 x ≤ 1) (p : k[X]) :
    u.1 (aeval x p) ≤ 1 := by
  rw [aeval_eq_sum_range]
  refine Valuation.map_sum_le _ fun i _ => ?_
  rw [Algebra.smul_def, map_mul, map_pow]
  refine mul_le_one' ?_ (pow_le_one' hx _)
  by_cases hc : p.coeff i = 0
  · simp [hc]
  · rw [u.2.2 _ hc]

theorem place_aeval_eq_one (x : L) (u : Place k L) (hx : u.1 x < 1) (q : k[X]) (hq : q.coeff 0 ≠ 0) :
    u.1 (aeval x q) = 1 := by
  have h1 : u.1 (algebraMap k L (q.coeff 0)) = 1 := u.2.2 _ hq
  have h2 : u.1 (x * aeval x q.divX) < 1 := by
    rw [map_mul]
    exact mul_lt_one_of_lt_of_le hx (place_aeval_le_one x u hx.le _)
  conv_lhs => rw [← X_mul_divX_add q]
  rw [map_add (f := _), map_mul, aeval_X, aeval_C, Valuation.map_add_eq_of_lt_right u.1 (by rw [h1]; exact h2), h1]

theorem place_aeval_eq_pow (x : L) (u : Place k L) (hx : u.1 x < 1) (p : k[X]) (hp : p ≠ 0) :
    u.1 (aeval x p) = u.1 x ^ p.rootMultiplicity 0 := by
  obtain ⟨q, hpq, hq⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp 0
  have hq0 : q.coeff 0 ≠ 0 := by
    intro h; apply hq; simpa [X_dvd_iff] using h
  conv_lhs => rw [hpq]
  simp [map_mul, map_pow, place_aeval_eq_one x u hx q hq0]

end GlobalTheory.Nef

namespace GlobalTheory.Nef

open Polynomial

theorem exists_unique_place_ord_eq_one (k L : Type) [Field k] [Field L] [Algebra k L] (x : L)
    (hx : Transcendental k x) (htop : k⟮x⟯ = ⊤) :
    ∃ v : Place k L, ord v x = 1 ∧ ∀ w : Place k L, w.1 x < 1 → w = v := by
  have hmem : ∀ y : L, ∃ r s : k[X], y = aeval x r / aeval x s := fun y =>
    (IntermediateField.mem_adjoin_simple_iff (F := k) (α := x) y).1 (by rw [htop]; trivial)
  have hne : ∀ p : k[X], p ≠ 0 → aeval x p ≠ 0 := fun p hp h => hx ⟨p, hp, h⟩
  have hval : ∀ u : Place k L, u.1 x < 1 → u.1 x = WithZero.exp (-1 : ℤ) := by
    intro u hu
    have hx0 : u.1 x ≠ 0 := by
      rw [Valuation.ne_zero_iff]; intro h; apply hne X X_ne_zero; simpa using h
    set b := WithZero.log (u.1 x) with hb
    have hub : u.1 x = WithZero.exp b := (WithZero.exp_log hx0).symm
    have hb0 : b < 0 := by
      have : WithZero.exp b < WithZero.exp (0 : ℤ) := by rw [← hub, WithZero.exp_zero]; exact hu
      exact WithZero.exp_lt_exp.1 this
    obtain ⟨y, hy⟩ := u.2.1 (WithZero.exp (-1 : ℤ))
    obtain ⟨r, s, rfl⟩ := hmem y
    have hr : r ≠ 0 := by rintro rfl; simp at hy; exact WithZero.exp_ne_zero hy.symm
    have hs : s ≠ 0 := by rintro rfl; simp at hy; exact WithZero.exp_ne_zero hy.symm
    rw [map_div₀, place_aeval_eq_pow x u hu r hr, place_aeval_eq_pow x u hu s hs, hub,
      ← WithZero.exp_nsmul, ← WithZero.exp_nsmul, ← WithZero.exp_sub, WithZero.exp_inj] at hy
    have hmul : b * ((r.rootMultiplicity 0 : ℤ) - s.rootMultiplicity 0) = -1 := by
      rw [← hy]; simp only [nsmul_eq_mul]; ring
    rcases Int.eq_one_or_neg_one_of_mul_eq_neg_one hmul with h | h
    · omega
    · rw [hub, h]
  have hpol : ∀ u : Place k L, u.1 x < 1 → ∀ p : k[X], p ≠ 0 →
      u.1 (aeval x p) = WithZero.exp (-1 : ℤ) ^ p.rootMultiplicity 0 := fun u hu p hp => by
    rw [place_aeval_eq_pow x u hu p hp, hval u hu]
  let e : RatFunc k ≃ₐ[k] L := ((RatFunc.algEquivOfTranscendental x hx).trans
    (IntermediateField.equivOfEq htop)).trans IntermediateField.topEquiv
  have heX : e RatFunc.X = x := by simp [e]
  have heXs : e.symm x = RatFunc.X := by rw [← heX, AlgEquiv.symm_apply_apply]
  let V := (Polynomial.idealX k).valuation (RatFunc k)
  let v0 : Valuation L (WithZero (Multiplicative ℤ)) := V.comap (e.symm : L →+* RatFunc k)
  have hv0 : ∀ y, v0 y = V (e.symm y) := fun y => rfl
  have hVX : V RatFunc.X = WithZero.exp (-1 : ℤ) := by
    rw [← RatFunc.algebraMap_X, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    exact IsDedekindDomain.HeightOneSpectrum.intValuation_singleton _ X_ne_zero (Polynomial.idealX_span k)
  let v : Place k L := ⟨v0, fun γ => by
      obtain ⟨r, hr⟩ := RatFunc.valuation_surjective (K := k) γ
      exact ⟨e r, by rw [hv0, AlgEquiv.symm_apply_apply]; exact hr⟩,
    fun c hc => by
      rw [hv0, AlgEquiv.commutes, IsScalarTower.algebraMap_apply k k[X] (RatFunc k),
        IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
        IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]
      intro hmem'
      rw [Polynomial.idealX_span, Ideal.mem_span_singleton, X_dvd_iff] at hmem'
      simp [hc] at hmem'⟩
  have hvx : v.1 x = WithZero.exp (-1 : ℤ) := by
    show v0 x = _; rw [hv0, heXs, hVX]
  refine ⟨v, by simp [ord, hvx], fun w hw => ?_⟩
  have hvl : v.1 x < 1 := by rw [hvx]; exact WithZero.exp_lt_exp.2 (by norm_num) |>.trans_eq WithZero.exp_zero
  apply Subtype.ext
  ext y
  obtain ⟨r, s, rfl⟩ := hmem y
  rw [map_div₀, map_div₀]
  by_cases hr : r = 0
  · simp [hr]
  by_cases hs : s = 0
  · simp [hs]
  rw [hpol w hw r hr, hpol w hw s hs, hpol v hvl r hr, hpol v hvl s hs]

end GlobalTheory.Nef
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniquePlaceOrdEqOneStatement
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_place_ord_eq_one_of_transcendental_generator : ∀ (k L : Type) [Field k] [Field L] [Algebra k L] (x : L), Transcendental k x → k⟮x⟯ = ⊤ → ∃ v : Place k L, ord v x = 1 ∧ ∀ w : Place k L, w.1 x < 1 → w = v := by
  first | exact @GlobalTheory.Nef.exists_unique_place_ord_eq_one | exact GlobalTheory.Nef.exists_unique_place_ord_eq_one | (intros; apply GlobalTheory.Nef.exists_unique_place_ord_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldZerosFiniteSumOrderEqFinrank
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef

theorem adjoin_gen_eq_top {k F : Type} [Field k] [Field F] [Algebra k F] (x : F) :
    k⟮(⟨x, IntermediateField.mem_adjoin_simple_self k x⟩ : k⟮x⟯)⟯ = ⊤ := by
  rw [eq_top_iff]
  rintro y -
  have hm : (k⟮(⟨x, IntermediateField.mem_adjoin_simple_self k x⟩ : k⟮x⟯)⟯).map (k⟮x⟯.val) = k⟮x⟯ := by
    rw [IntermediateField.adjoin_map]; simp
  have hy : (y : F) ∈ (k⟮(⟨x, IntermediateField.mem_adjoin_simple_self k x⟩ : k⟮x⟯)⟯).map (k⟮x⟯.val) := by
    rw [hm]; exact y.2
  obtain ⟨z, hz, hzy⟩ := hy
  have : z = y := Subtype.ext hzy
  exact this ▸ hz

theorem val_lt_one_of_ord_eq_one {k F : Type} [Field k] [Field F] [Algebra k F] (v : Place k F) (t : F)
    (h : ord v t = 1) : v.1 t < 1 := by
  unfold ord at h
  by_cases h0 : v.1 t = 0
  · rw [h0] at h; simp at h
  · have hl : WithZero.log (v.1 t) < WithZero.log (1 : WithZero (Multiplicative ℤ)) := by
      simp; omega
    exact (WithZero.log_lt_log h0 one_ne_zero).1 hl

end GlobalTheory.Nef

namespace GlobalTheory.Nef

theorem zeros_finite_sum_eq_degree : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
    ∀ x : F, Transcendental k x → {v : Place k F | v.1 x < 1}.Finite ∧
      ∑ᶠ v ∈ {v : Place k F | v.1 x < 1}, ord v x = Module.finrank k⟮x⟯ F := by
  intro k F _ _ _ _ _ hF x hx
  haveI : FiniteDimensional k⟮x⟯ F := (GlobalTheory.T.functionFieldOneVariable_transcendental_finite_and_ext k F hF).1 x hx
  set t : k⟮x⟯ := ⟨x, IntermediateField.mem_adjoin_simple_self k x⟩ with ht
  have htx : algebraMap k⟮x⟯ F t = x := rfl
  have htr : Transcendental k t := by
    intro ha
    exact hx ((IntermediateField.isAlgebraic_iff).1 ha)
  have htop : k⟮t⟯ = ⊤ := adjoin_gen_eq_top x
  have hL : IsFF k k⟮x⟯ := by
    refine ⟨t, htr, ?_⟩
    rw [htop]
    have : Module.Free (⊤ : IntermediateField k k⟮x⟯) k⟮x⟯ :=
      Module.Free.of_divisionRing _ _
    exact Module.finite_of_finrank_eq_succ IntermediateField.finrank_top
  obtain ⟨v0, hv0, huniq⟩ := GlobalTheory.T.existsUnique_place_ord_eq_one_of_transcendental_generator k k⟮x⟯ t htr htop
  obtain ⟨ρ, hρ⟩ := (GlobalTheory.T.functionFieldPlace_restriction_exists_pow k k⟮x⟯ F).1
  have ht0 : t ≠ 0 := by
    intro h; apply hx; rw [← htx, h, map_zero]; exact isAlgebraic_zero
  obtain ⟨hfin, hsum⟩ := GlobalTheory.T.functionFieldPlace_sum_order_eq_finrank k k⟮x⟯ F hL ρ hρ v0 t ht0 hv0
  have hset : {v : Place k F | v.1 x < 1} = {p | ρ p = v0} := by
    ext p
    obtain ⟨e, he, hpow, -⟩ := (GlobalTheory.T.functionFieldPlace_restriction_exists_pow k k⟮x⟯ F).2 ρ hρ p
    simp only [Set.mem_setOf_eq]
    change p.1 (algebraMap k⟮x⟯ F t) < 1 ↔ ρ p = v0
    rw [hpow t]
    constructor
    · intro h
      apply huniq
      by_contra hn
      exact absurd h (not_lt.2 (one_le_pow₀ (not_lt.1 hn)))
    · intro h
      rw [h]
      exact pow_lt_one₀ zero_le' (val_lt_one_of_ord_eq_one v0 t hv0) he.ne'
  rw [hset]
  exact ⟨hfin, by simpa [htx] using hsum⟩

end GlobalTheory.Nef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldZerosFiniteSumOrderEqFinrankStatement
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.functionField_zeros_finite_sum_order_eq_finrank : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ x : F, Transcendental k x → {v : Place k F | v.1 x < 1}.Finite ∧ ∑ᶠ v ∈ {v : Place k F | v.1 x < 1}, ord v x = Module.finrank k⟮x⟯ F := by
  first | exact @GlobalTheory.Nef.zeros_finite_sum_eq_degree | exact GlobalTheory.Nef.zeros_finite_sum_eq_degree | (intros; apply GlobalTheory.Nef.zeros_finite_sum_eq_degree <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SheafComplexPairingTensorUniversalProperty
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafDescendAlongLocallyBijective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafDescendAlongLocallyBijective
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

namespace DescLoc

variable {S : Type} [CommRing S] {P Q : Scheme.{0}ᵒᵖ ⥤ AddCommGrpCat.{1}} (φ : P ⟶ Q)

theorem res_res {M : Shv S} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (a : Sec M U) :
    Sec.res k (Sec.res g a) = Sec.res (k ≫ g) a := by
  simp [Sec.res]

theorem res_add {M : Shv S} {V U : Scheme.{0}} (g : V ⟶ U) (a a' : Sec M U) :
    Sec.res g (a + a') = Sec.res g a + Sec.res g a' := map_add _ _ _

theorem pmap_comp (P : Scheme.{0}ᵒᵖ ⥤ AddCommGrpCat.{1}) {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U)
    (x : P.obj (op U)) : (P.map k.op).hom ((P.map g.op).hom x) = (P.map (k ≫ g).op).hom x := by
  simp

theorem nat_apply {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    (φ.app (op V)).hom ((P.map g.op).hom x) = (Q.map g.op).hom ((φ.app (op U)).hom x) := by
  have := congrArg (fun f => f.hom x) (φ.naturality g.op)
  simpa using this

section Main
variable {S : Type} [CommRing S] {P Q : Scheme.{0}ᵒᵖ ⥤ AddCommGrpCat.{1}} (φ : P ⟶ Q) (M : Shv S)
  (b : ∀ U : Scheme.{0}, P.obj (op U) →+ Sec M U)
  (hb : ∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (b U x) = b V ((P.map g.op).hom x))

theorem ext_loc {U : Scheme.{0}} (a a' : Sec M U) (h : Loc U fun _ g => Sec.res g a = Sec.res g a') : a = a' :=
  (sec_ext_glue S M U).1 a a' h


include hb in
theorem key (h2 : ∀ (U : Scheme.{0}) (x : P.obj (op U)), (φ.app (op U)).hom x = 0 → Loc U fun _ g => (P.map g.op).hom x = 0)
    {V : Scheme.{0}} (x x' : P.obj (op V)) (hx : (φ.app (op V)).hom x = (φ.app (op V)).hom x') : b V x = b V x' := by
  obtain ⟨T, hT, hz⟩ := h2 V (x - x') (by rw [map_sub, hx, sub_self])
  refine ext_loc M _ _ ⟨T, hT, fun W k hk => ?_⟩
  dsimp only
  rw [hb, hb]
  have := hz W k hk
  dsimp only at this
  rw [map_sub, sub_eq_zero] at this
  rw [this]

def Ch (U : Scheme.{0}) (y : Q.obj (op U)) (a : Sec M U) : Prop :=
  ∀ (V : Scheme.{0}) (g : V ⟶ U) (x : P.obj (op V)), (φ.app (op V)).hom x = (Q.map g.op).hom y → Sec.res g a = b V x

theorem ch_unique (h1 : ∀ (U : Scheme.{0}) (y : Q.obj (op U)), Loc U fun V g => ∃ x, (φ.app (op V)).hom x = (Q.map g.op).hom y)
    {U : Scheme.{0}} (y : Q.obj (op U)) (a a' : Sec M U) (ha : Ch φ M b U y a) (ha' : Ch φ M b U y a') : a = a' := by
  obtain ⟨T, hT, hl⟩ := h1 U y
  refine ext_loc M _ _ ⟨T, hT, fun V g hg => ?_⟩
  obtain ⟨x, hx⟩ := hl V g hg
  rw [ha V g x hx, ha' V g x hx]

include hb in
theorem ch_exists (h1 : ∀ (U : Scheme.{0}) (y : Q.obj (op U)), Loc U fun V g => ∃ x, (φ.app (op V)).hom x = (Q.map g.op).hom y)
    (h2 : ∀ (U : Scheme.{0}) (x : P.obj (op U)), (φ.app (op U)).hom x = 0 → Loc U fun _ g => (P.map g.op).hom x = 0)
    (U : Scheme.{0}) (y : Q.obj (op U)) : ∃ a, Ch φ M b U y a := by
  obtain ⟨T, hT, hl⟩ := h1 U y
  let s : ∀ (V : Scheme.{0}) (g : V ⟶ U), T.arrows g → Sec M V := fun V g hg => b V (hl V g hg).choose
  have hs : ∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V) (hg : T.arrows g),
      Sec.res k (s V g hg) = s W (k ≫ g) (T.downward_closed hg k) := by
    intro V W g k hg
    simp only [s]
    rw [hb]
    apply key φ M b hb h2
    rw [nat_apply, (hl V g hg).choose_spec, (hl W (k ≫ g) (T.downward_closed hg k)).choose_spec, pmap_comp]
  obtain ⟨a, ha⟩ := (sec_ext_glue S M U).2 T hT s hs
  refine ⟨a, fun V g x hx => ?_⟩
  refine ext_loc M _ _ ⟨T.pullback g, Scheme.etaleTopology.pullback_stable g hT, fun W k hk => ?_⟩
  dsimp only
  rw [res_res, ha W (k ≫ g) hk, hb]
  simp only [s]
  apply key φ M b hb h2
  rw [nat_apply, hx, (hl W (k ≫ g) hk).choose_spec, pmap_comp]

end Main

section Main2
variable {S : Type} [CommRing S] {P Q : Scheme.{0}ᵒᵖ ⥤ AddCommGrpCat.{1}} (φ : P ⟶ Q) (M : Shv S)
  (b : ∀ U : Scheme.{0}, P.obj (op U) →+ Sec M U)
  (hb : ∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (b U x) = b V ((P.map g.op).hom x))
  (h1 : ∀ (U : Scheme.{0}) (y : Q.obj (op U)), Loc U fun V g => ∃ x, (φ.app (op V)).hom x = (Q.map g.op).hom y)
  (h2 : ∀ (U : Scheme.{0}) (x : P.obj (op U)), (φ.app (op U)).hom x = 0 → Loc U fun _ g => (P.map g.op).hom x = 0)

include hb h1 h2 in
theorem ch_add {U : Scheme.{0}} (y y' : Q.obj (op U)) (a a' : Sec M U) (ha : Ch φ M b U y a) (ha' : Ch φ M b U y' a') :
    Ch φ M b U (y + y') (a + a') := by
  intro V g x hx
  obtain ⟨T1, hT1, hl1⟩ := h1 V ((Q.map g.op).hom y)
  obtain ⟨T2, hT2, hl2⟩ := h1 V ((Q.map g.op).hom y')
  refine ext_loc M _ _ ⟨T1 ⊓ T2, Scheme.etaleTopology.intersection_covering hT1 hT2, fun W k hk => ?_⟩
  obtain ⟨x1, e1⟩ := hl1 W k hk.1
  obtain ⟨x2, e2⟩ := hl2 W k hk.2
  rw [pmap_comp] at e1 e2
  rw [res_res, res_add, ha W (k ≫ g) x1 e1, ha' W (k ≫ g) x2 e2, hb, ← map_add (f := _)]
  apply key φ M b hb h2
  rw [nat_apply, hx, pmap_comp]
  simp only [map_add (f := _), e1, e2]

theorem ch_res {U V : Scheme.{0}} (h : V ⟶ U) (y : Q.obj (op U)) (a : Sec M U) (ha : Ch φ M b U y a) :
    Ch φ M b V ((Q.map h.op).hom y) (Sec.res h a) := by
  intro W k x hx
  rw [res_res]
  exact ha W (k ≫ h) x (by rw [hx, pmap_comp])

include hb h2 in
theorem ch_base {U : Scheme.{0}} (x : P.obj (op U)) : Ch φ M b U ((φ.app (op U)).hom x) (b U x) := by
  intro V g x' hx
  rw [hb]
  apply key φ M b hb h2
  rw [nat_apply, hx]

end Main2
end DescLoc

open DescLoc in
theorem desc_loc : ∀ (S : Type) [CommRing S] (P Q : Scheme.{0}ᵒᵖ ⥤ AddCommGrpCat.{1}) (φ : P ⟶ Q), (∀ (U : Scheme.{0}) (y : Q.obj (op U)), Loc U fun V g => ∃ x, (φ.app (op V)).hom x = (Q.map g.op).hom y) → (∀ (U : Scheme.{0}) (x : P.obj (op U)), (φ.app (op U)).hom x = 0 → Loc U fun _ g => (P.map g.op).hom x = 0) → ∀ (M : Shv S) (b : ∀ U : Scheme.{0}, P.obj (op U) →+ Sec M U), (∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (b U x) = b V ((P.map g.op).hom x)) → ∃ c : ∀ U : Scheme.{0}, Q.obj (op U) →+ Sec M U, (∀ (V U : Scheme.{0}) (g : V ⟶ U) y, Sec.res g (c U y) = c V ((Q.map g.op).hom y)) ∧ ∀ U x, c U ((φ.app (op U)).hom x) = b U x := by
  intro S _ P Q φ h1 h2 M b hb
  have hex := ch_exists φ M b hb h1 h2
  let c0 : ∀ U : Scheme.{0}, Q.obj (op U) → Sec M U := fun U y => (hex U y).choose
  have hc0 : ∀ U y, Ch φ M b U y (c0 U y) := fun U y => (hex U y).choose_spec
  let c : ∀ U : Scheme.{0}, Q.obj (op U) →+ Sec M U := fun U =>
    AddMonoidHom.mk' (c0 U) (fun y y' => ch_unique φ M b h1 (y + y') _ _ (hc0 U (y + y'))
      (ch_add φ M b hb h1 h2 y y' _ _ (hc0 U y) (hc0 U y')))
  refine ⟨c, fun V U g y => ?_, fun U x => ?_⟩
  · exact ch_unique φ M b h1 _ _ _ (ch_res φ M b g y _ (hc0 U y)) (hc0 V _)
  · exact ch_unique φ M b h1 _ _ _ (hc0 U _) (ch_base φ M b hb h2 x)
end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafDescendAlongLocallyBijectiveStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleSheaf_descend_along_locallyBijective : ∀ (S : Type) [CommRing S] (P Q : Scheme.{0}ᵒᵖ ⥤ AddCommGrpCat.{1}) (φ : P ⟶ Q), (∀ (U : Scheme.{0}) (y : Q.obj (op U)), Loc U fun V g => ∃ x, (φ.app (op V)).hom x = (Q.map g.op).hom y) → (∀ (U : Scheme.{0}) (x : P.obj (op U)), (φ.app (op U)).hom x = 0 → Loc U fun _ g => (P.map g.op).hom x = 0) → ∀ (M : Shv S) (b : ∀ U : Scheme.{0}, P.obj (op U) →+ Sec M U), (∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (b U x) = b V ((P.map g.op).hom x)) → ∃ c : ∀ U : Scheme.{0}, Q.obj (op U) →+ Sec M U, (∀ (V U : Scheme.{0}) (g : V ⟶ U) y, Sec.res g (c U y) = c V ((Q.map g.op).hom y)) ∧ ∀ U x, c U ((φ.app (op U)).hom x) = b U x := by
  first | (exact @GlobalTheory.EtC.desc_loc) | (exact GlobalTheory.EtC.desc_loc) | (intros; apply GlobalTheory.EtC.desc_loc  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SheafComplexPairingTensorUniversalProperty
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.TensFam

variable {R : Type} [CommRing R]

theorem tensRes_id (I J : Cx R) (U : Scheme.{0}) (w : ℤ) : Tens.res (I := I) (J := J) (𝟙 U) w = LinearMap.id := by
  classical
  apply DirectSum.linearMap_ext
  intro p
  apply TensorProduct.ext'
  intro a b
  simp [Tens.res, DirectSum.lmap_lof]

theorem tensRes_comp (I J : Cx R) {W V U : Scheme.{0}} (f : W ⟶ V) (g : V ⟶ U) (w : ℤ) :
    Tens.res (I := I) (J := J) (f ≫ g) w = (Tens.res f w).comp (Tens.res g w) := by
  classical
  apply DirectSum.linearMap_ext
  intro p
  apply TensorProduct.ext'
  intro a b
  simp [Tens.res, DirectSum.lmap_lof]

theorem lift_resL {I J K : Cx R} (τ : Pair I J K) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) :
    (τ.lift V w).comp (Tens.res g w) = ((K.X w).obj.map g.op).hom.comp (τ.lift U w) := by
  classical
  apply DirectSum.linearMap_ext
  intro p
  apply TensorProduct.ext'
  intro a b
  have := τ.nat g p.1.1 p.1.2 w p.2 a b
  simp [Tens.res, Pair.lift, DirectSum.lmap_lof] at this ⊢
  exact this.symm

def tensP (I J : Cx R) (w : ℤ) : Scheme.{0}ᵒᵖ ⥤ AddCommGrpCat.{1} where
  obj U := AddCommGrpCat.of (Tens I J U.unop w)
  map g := AddCommGrpCat.ofHom (Tens.res g.unop w).toAddMonoidHom
  map_id U := by
    apply AddCommGrpCat.ext; intro x
    change Tens.res (I := I) (J := J) (𝟙 U.unop) w x = x
    rw [tensRes_id]; rfl
  map_comp f g := by
    apply AddCommGrpCat.ext; intro x
    change Tens.res (I := I) (J := J) (g.unop ≫ f.unop) w x = Tens.res g.unop w (Tens.res f.unop w x)
    rw [tensRes_comp]; rfl

def secP (F : Shv R) : Scheme.{0}ᵒᵖ ⥤ AddCommGrpCat.{1} := F.obj ⋙ forget₂ _ AddCommGrpCat

def liftP {I J K : Cx R} (τ : Pair I J K) (w : ℤ) : tensP I J w ⟶ secP (K.X w) where
  app U := AddCommGrpCat.ofHom (τ.lift U.unop w).toAddMonoidHom
  naturality V U g := by
    apply AddCommGrpCat.ext; intro x
    exact LinearMap.congr_fun (lift_resL τ g.unop w) x

end GlobalTheory.EtC.TensFam


open GlobalTheory.EtC.TensFam in
theorem GlobalTheory.EtC.tens_fam : ∀ (R S : Type) [CommRing R] [CommRing S] {I J K : Cx R} (τ : Pair I J K), τ.IsTensor → ∀ (w : ℤ) (M : Shv S) (b : ∀ U : Scheme.{0}, Tens I J U w →+ Sec M U), (∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (b U x) = b V (Tens.res g w x)) → ∃ φ : ∀ U : Scheme.{0}, Sec (K.X w) U →+ Sec M U, (∀ (V U : Scheme.{0}) (g : V ⟶ U) y, Sec.res g (φ U y) = φ V (Sec.res g y)) ∧ ∀ U x, φ U (τ.lift U w x) = b U x := by
  intro R S _ _ I J K τ hτ w M b hb
  exact GlobalTheory.T.etaleSheaf_descend_along_locallyBijective S (tensP I J w) (secP (K.X w)) (liftP τ w)
    (fun U y => hτ.1 U w y) (fun U x hx => hτ.2 U w x hx) M b hb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SheafComplexPairingTensorUniversalPropertyStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sheafComplexPairing_tensor_universal_property : ∀ (R S : Type) [CommRing R] [CommRing S] {I J K : Cx R} (τ : Pair I J K), τ.IsTensor → ∀ (w : ℤ) (M : Shv S) (b : ∀ U : Scheme.{0}, Tens I J U w →+ Sec M U), (∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (b U x) = b V (Tens.res g w x)) → ∃ φ : ∀ U : Scheme.{0}, Sec (K.X w) U →+ Sec M U, (∀ (V U : Scheme.{0}) (g : V ⟶ U) y, Sec.res g (φ U y) = φ V (Sec.res g y)) ∧ ∀ U x, φ U (τ.lift U w x) = b U x := by
  first | exact @GlobalTheory.EtC.tens_fam | exact GlobalTheory.EtC.tens_fam | (intros; apply GlobalTheory.EtC.tens_fam <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitLemmaResiduallyUnipotentCayleyTransform
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitLemmaResiduallyUnipotentCayleyTransform
noncomputable section

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma.CayleyAny

open GlobalTheory.UnitLemma.CayleyCase

theorem mem_adjoin_both' {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (g Y : A) (ξ a b : O) (Q : O[X])
    (hQm : Q.Monic) (hQ : aeval g Q = 0) (hQs : IsUnit (Q.eval ξ)) (hab : IsUnit (ξ * a - b))
    (hY : Y * (g - algebraMap O A ξ) = algebraMap O A a * g - algebraMap O A b) :
    Y ∈ Algebra.adjoin O ({g} : Set A) ∧ g ∈ Algebra.adjoin O ({Y} : Set A) := by
  constructor
  · obtain ⟨w, hw, hgw⟩ := sub_inv_mem g ξ Q hQ hQs
    have e : Y = (algebraMap O A a * g - algebraMap O A b) * w := by
      linear_combination (-Y) * hgw + w * hY
    rw [e]
    exact mul_mem (sub_mem (mul_mem (Subalgebra.algebraMap_mem _ _) (Algebra.subset_adjoin rfl))
      (Subalgebra.algebraMap_mem _ _)) hw
  · set n := Q.natDegree
    let R : O[X] := ∑ i ∈ Finset.range (n + 1), C (Q.coeff i) * (C ξ * X - C b) ^ i * (X - C a) ^ (n - i)
    have hgY : g * (Y - algebraMap O A a) = algebraMap O A ξ * Y - algebraMap O A b := by
      linear_combination hY
    have hR : aeval Y R = 0 := by
      have : aeval Y R = (Y - algebraMap O A a) ^ n * aeval g Q := by
        conv_rhs => rw [aeval_eq_sum_range, Finset.mul_sum]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [R, map_sum, map_mul, map_pow, aeval_C, map_sub, aeval_X]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hin : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        rw [← hgY, mul_pow, Algebra.smul_def]
        have : (Y - algebraMap O A a) ^ n = (Y - algebraMap O A a) ^ i * (Y - algebraMap O A a) ^ (n - i) := by
          rw [← pow_add, Nat.add_sub_cancel' hin]
        rw [this]; ring
      rw [this, hQ, mul_zero]
    have hRe : R.eval a = (ξ * a - b) ^ n := by
      simp only [R, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_sub, eval_X, sub_self]
      rw [Finset.sum_eq_single n]
      · simp [n, hQm.coeff_natDegree]
      · intro i hi hin
        have : 0 < n - i := Nat.sub_pos_of_lt (lt_of_le_of_ne (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) hin)
        rw [zero_pow this.ne', mul_zero]
      · intro h; exact absurd (Finset.mem_range.2 (Nat.lt_succ_self n)) h
    have hRu : IsUnit (R.eval a) := by
      rw [hRe]; exact hab.pow _
    obtain ⟨v, hv, hYv⟩ := sub_inv_mem Y a R hR hRu
    have e : g = (algebraMap O A ξ * Y - algebraMap O A b) * v := by
      linear_combination (-g) * hYv + v * hgY
    rw [e]
    exact mul_mem (sub_mem (mul_mem (Subalgebra.algebraMap_mem _ _) (Algebra.subset_adjoin rfl))
      (Subalgebra.algebraMap_mem _ _)) hv

end GlobalTheory.UnitLemma.CayleyAny

namespace GlobalTheory.UnitLemma.CayleyAny

open GlobalTheory.UnitLemma.CayleyCase

variable {K : UQ}

theorem isUnit_of_conj (K : UQ) (x y : K.O) (h : K.c (algebraMap K.O K.E x) = algebraMap K.O K.E y)
    (hy : IsUnit y) : IsUnit x := by
  obtain ⟨u, rfl⟩ := hy
  obtain ⟨w, hw⟩ := K.c_int (↑u⁻¹ : K.O)
  have h1 : K.c (algebraMap K.O K.E (u : K.O)) = algebraMap K.O K.E x := by rw [← h, K.c_c]
  have h2 : algebraMap K.O K.E (x * w) = 1 := by
    rw [map_mul, ← h1, ← hw, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  rw [← map_one (algebraMap K.O K.E)] at h2
  exact IsUnit.of_mul_eq_one (b := w) (IsFractionRing.injective K.O K.E h2)

theorem mobius_selfadj (B : InvAlg K) (x y ξ : K.O) (Y : B.A) (hu : B.g * B.σ B.g = 1)
    (hxy : K.c (algebraMap K.O K.E x) = algebraMap K.O K.E y)
    (hξ : algebraMap K.O K.E ξ * K.c (algebraMap K.O K.E ξ) = 1)
    (w : B.A) (hw : (B.g - algebraMap K.O B.A ξ) * w = 1)
    (hY : Y * (B.g - algebraMap K.O B.A ξ) =
      algebraMap K.O B.A y * B.g - algebraMap K.O B.A x * algebraMap K.O B.A ξ) :
    B.σ Y = Y := by
  have sx : B.σ (algebraMap K.O B.A x) = algebraMap K.O B.A y := by
    rw [σ_algebraMap, hxy, ← IsScalarTower.algebraMap_apply]
  have sy : B.σ (algebraMap K.O B.A y) = algebraMap K.O B.A x := by
    rw [σ_algebraMap, ← hxy, K.c_c, ← IsScalarTower.algebraMap_apply]
  have hξA : algebraMap K.O B.A ξ * B.σ (algebraMap K.O B.A ξ) = 1 := by
    rw [σ_algebraMap, IsScalarTower.algebraMap_apply K.O K.E B.A ξ, ← map_mul, hξ, map_one]
  have h1 := congrArg B.σ hY
  rw [map_mul, map_sub, map_sub, map_mul, map_mul, sx, sy] at h1
  set G := B.g
  set Gs := B.σ B.g
  set ξA := algebraMap K.O B.A ξ
  set ξs := B.σ (algebraMap K.O B.A ξ)
  set xA := algebraMap K.O B.A x
  set yA := algebraMap K.O B.A y
  have key : (B.σ Y - Y) * (G - ξA) = 0 := by
    linear_combination (-G * ξA) * h1 - hY - (xA * ξA - B.σ Y * ξA) * hu - (B.σ Y * G - yA * G) * hξA
  calc B.σ Y = B.σ Y * ((G - ξA) * w) := by rw [hw, mul_one]
    _ = Y * ((G - ξA) * w) + (B.σ Y - Y) * (G - ξA) * w := by ring
    _ = Y := by rw [key, hw]; ring

end GlobalTheory.UnitLemma.CayleyAny

namespace GlobalTheory.UnitLemma.CayleyAny

open GlobalTheory.UnitLemma.CayleyCase

theorem identity_of_residually_unipotent_any : UnitLemmaLie → ∀ (K : UQ) (B₁ B₂ : InvAlg K),
    B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 → (B₁.P * B₂.P).Separable → ∀ s : K.Oˣ,
    algebraMap K.O K.E s * K.c (algebraMap K.O K.E s) = 1 →
    (∃ Q : K.O[X], Q.map (algebraMap K.O K.E) = B₁.P * B₂.P ∧
      Q.map (IsLocalRing.residue K.O) = (X - C (IsLocalRing.residue K.O s)) ^ Q.natDegree) →
    InvAlg.Identity B₁ B₂ := by
  intro hL K B₁ B₂ hu₁ hu₂ hsep s hs ⟨Q, hQ, hQr⟩
  have hinj := IsFractionRing.injective K.O K.E

  obtain ⟨x, y, hxy, hm⟩ := K.c_res
  have hyx : K.c (algebraMap K.O K.E y) = algebraMap K.O K.E x := by rw [← hxy, K.c_c]
  have hxu : IsUnit x := by
    by_contra hx
    have hy : ¬ IsUnit y := fun hy => hx (isUnit_of_conj K x y hxy hy)
    exact hm (Ideal.sub_mem _ ((IsLocalRing.mem_maximalIdeal _).2 hx) ((IsLocalRing.mem_maximalIdeal _).2 hy))
  have hyu : IsUnit y := isUnit_of_conj K y x hyx hxu
  have hxyu : IsUnit (x - y) := by
    by_contra h; exact hm ((IsLocalRing.mem_maximalIdeal _).2 h)
  set yi : K.O := ↑hyu.unit⁻¹ with hyi
  have hyyi : y * yi = 1 := hyu.mul_val_inv
  set ξ : K.O := (s : K.O) * x * yi with hξd
  have hξu : IsUnit ξ := (s.isUnit.mul hxu).mul (hyu.unit⁻¹).isUnit
  have hξn : algebraMap K.O K.E ξ * K.c (algebraMap K.O K.E ξ) = 1 := by
    obtain ⟨w, hw⟩ := K.c_int yi
    have e1 : algebraMap K.O K.E x * algebraMap K.O K.E w = 1 := by
      have := congrArg K.c (congrArg (algebraMap K.O K.E) hyyi)
      rw [map_mul, map_mul, hyx, hw, map_one, map_one] at this
      exact this
    have e2 : algebraMap K.O K.E y * algebraMap K.O K.E yi = 1 := by
      rw [← map_mul, hyyi, map_one]
    rw [hξd, map_mul, map_mul, map_mul, map_mul, hxy, hw]
    linear_combination (algebraMap K.O K.E x * algebraMap K.O K.E w * algebraMap K.O K.E y *
      algebraMap K.O K.E yi) * hs + (algebraMap K.O K.E y * algebraMap K.O K.E yi) * e1 + e2
  have hQξ : IsUnit (Q.eval ξ) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, ← eval₂_hom, ← eval_map, hQr]
    simp only [eval_pow, eval_sub, eval_X, eval_C]
    apply pow_ne_zero
    intro h0
    apply hm
    set r := IsLocalRing.residue K.O
    have hs0 : r (s : K.O) ≠ 0 := (IsLocalRing.residue_ne_zero_iff_isUnit _).2 s.isUnit
    have h3 : r (y * yi) = 1 := by rw [hyyi, map_one]
    rw [map_mul] at h3
    have h4 : r (s : K.O) * (r x - r y) = 0 := by
      rw [hξd, map_mul, map_mul] at h0
      linear_combination r y * h0 - (r (s : K.O) * r x) * h3
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub]
    exact (mul_eq_zero.1 h4).resolve_left hs0
  have hab : IsUnit (ξ * y - x * ξ) := by
    rw [show ξ * y - x * ξ = -(ξ * (x - y)) by ring]
    exact (hξu.mul hxyu).neg
  obtain ⟨Q₁, Q₂, hQQ, e₁, e₂, a₁, a₂, hmQ⟩ := lift_factor B₁ B₂ hsep Q hQ
  have hQs₁ : IsUnit (Q₁.eval ξ) := by
    rw [hQQ, eval_mul] at hQξ; exact isUnit_of_mul_isUnit_left hQξ
  have hQs₂ : IsUnit (Q₂.eval ξ) := by
    rw [hQQ, eval_mul] at hQξ; exact isUnit_of_mul_isUnit_right hQξ
  have hm₁ : Q₁.Monic := monic_of_injective hinj (e₁ ▸ LinearMap.charpoly_monic _)
  have hm₂ : Q₂.Monic := monic_of_injective hinj (e₂ ▸ LinearMap.charpoly_monic _)
  obtain ⟨w₁, -, hw₁⟩ := sub_inv_mem B₁.g ξ Q₁ a₁ hQs₁
  obtain ⟨w₂, -, hw₂⟩ := sub_inv_mem B₂.g ξ Q₂ a₂ hQs₂
  set Y₁ := (algebraMap K.O B₁.A y * B₁.g - algebraMap K.O B₁.A x * algebraMap K.O B₁.A ξ) * w₁ with hY₁d
  set Y₂ := (algebraMap K.O B₂.A y * B₂.g - algebraMap K.O B₂.A x * algebraMap K.O B₂.A ξ) * w₂ with hY₂d
  have hY₁ : Y₁ * (B₁.g - algebraMap K.O B₁.A ξ) =
      algebraMap K.O B₁.A y * B₁.g - algebraMap K.O B₁.A x * algebraMap K.O B₁.A ξ := by
    rw [hY₁d]; linear_combination (algebraMap K.O B₁.A y * B₁.g - algebraMap K.O B₁.A x * algebraMap K.O B₁.A ξ) * hw₁
  have hY₂ : Y₂ * (B₂.g - algebraMap K.O B₂.A ξ) =
      algebraMap K.O B₂.A y * B₂.g - algebraMap K.O B₂.A x * algebraMap K.O B₂.A ξ := by
    rw [hY₂d]; linear_combination (algebraMap K.O B₂.A y * B₂.g - algebraMap K.O B₂.A x * algebraMap K.O B₂.A ξ) * hw₂
  have hY₁' : Y₁ * (B₁.g - algebraMap K.O B₁.A ξ) = algebraMap K.O B₁.A y * B₁.g - algebraMap K.O B₁.A (x * ξ) := by
    rw [map_mul (algebraMap K.O B₁.A) x ξ]; exact hY₁
  have hY₂' : Y₂ * (B₂.g - algebraMap K.O B₂.A ξ) = algebraMap K.O B₂.A y * B₂.g - algebraMap K.O B₂.A (x * ξ) := by
    rw [map_mul (algebraMap K.O B₂.A) x ξ]; exact hY₂
  have adj₁ := mem_adjoin_both' B₁.g Y₁ ξ y (x * ξ) Q₁ hm₁ a₁ hQs₁ hab hY₁'
  have adj₂ := mem_adjoin_both' B₂.g Y₂ ξ y (x * ξ) Q₂ hm₂ a₂ hQs₂ hab hY₂'
  have aQ : aeval ((B₁.g, B₂.g) : B₁.A × B₂.A) Q = 0 := by
    have f1 := aeval_algHom_apply (AlgHom.fst K.O B₁.A B₂.A) ((B₁.g, B₂.g) : B₁.A × B₂.A) Q
    have f2 := aeval_algHom_apply (AlgHom.snd K.O B₁.A B₂.A) ((B₁.g, B₂.g) : B₁.A × B₂.A) Q
    refine Prod.ext ?_ ?_
    · change AlgHom.fst K.O B₁.A B₂.A _ = 0
      rw [← f1]; change aeval B₁.g Q = 0
      rw [hQQ, map_mul, a₁, zero_mul]
    · change AlgHom.snd K.O B₁.A B₂.A _ = 0
      rw [← f2]; change aeval B₂.g Q = 0
      rw [hQQ, map_mul, a₂, mul_zero]
  have hYp : ((Y₁, Y₂) : B₁.A × B₂.A) * ((B₁.g, B₂.g) - algebraMap K.O (B₁.A × B₂.A) ξ) =
      algebraMap K.O (B₁.A × B₂.A) y * (B₁.g, B₂.g) - algebraMap K.O (B₁.A × B₂.A) (x * ξ) :=
    Prod.ext hY₁' hY₂'
  have adjP := mem_adjoin_both' ((B₁.g, B₂.g) : B₁.A × B₂.A) (Y₁, Y₂) ξ y (x * ξ) Q hmQ aQ hQξ hab hYp
  have st₁ := stable_iff B₁.g Y₁ adj₁
  have st₂ := stable_iff B₂.g Y₂ adj₂
  have stP := stable_iff ((B₁.g, B₂.g) : B₁.A × B₂.A) (Y₁, Y₂) adjP

  have sa₁ := mobius_selfadj B₁ x y ξ Y₁ hu₁ hxy hξn w₁ hw₁ hY₁
  have sa₂ := mobius_selfadj B₂ x y ξ Y₂ hu₂ hxy hξn w₂ hw₂ hY₂
  have hsepP : (LinearMap.mulLeft K.E ((B₁.g, B₂.g) : B₁.A × B₂.A)).charpoly.Separable := by
    have := Orbit.prod_P B₁ B₂
    rw [← this] at hsep; exact hsep
  have hsepC : ((withG B₁ Y₁).P * (withG B₂ Y₂).P).Separable := by
    rw [← Orbit.prod_P]
    have := separable_of_adjoin (E := K.E) (A := B₁.A × B₂.A) (B₁.g, B₂.g) (Y₁, Y₂)
      (mem_adjoin_of_mem (O := K.O) adjP.1) (mem_adjoin_of_mem (O := K.O) adjP.2) hsepP
    exact this
  have hId := hL K (withG B₁ Y₁) (withG B₂ Y₂) sa₁ sa₂ hsepC

  have hr : resultant B₁.P B₂.P ≠ 0 :=
    ((isUnit_resultant_iff_isCoprime (LinearMap.charpoly_monic _)).2 hsep.isCoprime).ne_zero
  have hr' : resultant (withG B₁ Y₁).P (withG B₂ Y₂).P ≠ 0 :=
    ((isUnit_resultant_iff_isCoprime (LinearMap.charpoly_monic _)).2 hsepC.isCoprime).ne_zero
  obtain ⟨M₁, l₁, s₁⟩ := exists_stable_lat (E := K.E) B₁.g ⟨Q₁, hm₁, a₁⟩
  obtain ⟨M₂, l₂, s₂⟩ := exists_stable_lat (E := K.E) B₂.g ⟨Q₂, hm₂, a₂⟩
  have hv : val K.O (resultant B₁.P B₂.P) = val K.O (resultant (withG B₁ Y₁).P (withG B₂ Y₂).P) :=
    val_res_eq (O := K.O) (E := K.E) B₁.g Y₁ B₂.g Y₂ hr hr' st₁ st₂ stP M₁ M₂ l₁ l₂ s₁ s₂
  unfold InvAlg.Identity at hId ⊢
  rw [kapSum_withG B₁ B₂ Y₁ Y₂ stP, stSum_withG B₁ Y₁ st₁, stSum_withG B₂ Y₂ st₂] at hId
  change (-(K.q : ℚ)) ^ (-val K.O (resultant B₁.P B₂.P)) * _ = _
  rw [hv]
  exact hId

end GlobalTheory.UnitLemma.CayleyAny
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitLemmaResiduallyUnipotentCayleyTransformStatement
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitLemma_residuallyUnipotent_cayleyTransform : UnitLemmaLie → ∀ (K : UQ) (B₁ B₂ : InvAlg K), B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 → (B₁.P * B₂.P).Separable → ∀ s : K.Oˣ, algebraMap K.O K.E s * K.c (algebraMap K.O K.E s) = 1 → (∃ Q : K.O[X], Q.map (algebraMap K.O K.E) = B₁.P * B₂.P ∧ Q.map (IsLocalRing.residue K.O) = (X - C (IsLocalRing.residue K.O s)) ^ Q.natDegree) → InvAlg.Identity B₁ B₂ := by
  first | exact @GlobalTheory.UnitLemma.CayleyAny.identity_of_residually_unipotent_any | exact GlobalTheory.UnitLemma.CayleyAny.identity_of_residually_unipotent_any | (intros; apply GlobalTheory.UnitLemma.CayleyAny.identity_of_residually_unipotent_any <;> assumption)
end
end
