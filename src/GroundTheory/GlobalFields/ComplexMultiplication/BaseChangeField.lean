module

public import GroundTheory.GlobalFields.ComplexMultiplication.BaseChangeDescent

@[expose] public section

section -- merged from GroundTheory.GlobalFields.ComplexMultiplication.BaseChangeGalois
namespace GroundTheory.Global

open Polynomial WeierstrassCurve IntermediateField GroundTheory.Arith.Abelian
open WeierstrassCurve.Affine (Point equation_iff)

universe u

section Conj

variable {F Ω : Type u} [Field F] [Field Ω] [Algebra F Ω]
variable {E E' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]


variable (E) in
theorem baseChange_map_algEquiv (g : Ω ≃ₐ[F] Ω) :
    (E.baseChange Ω).map (g : Ω →+* Ω) = E.baseChange Ω :=
  WeierstrassCurve.map_baseChange (R := F) (S := F) E (g : Ω →ₐ[F] Ω)

noncomputable def _root_.GroundTheory.Arith.Abelian.Isogeny.conj (g : Ω ≃ₐ[F] Ω)
    (ψ : Isogeny (E.baseChange Ω) (E'.baseChange Ω)) :
    Isogeny (E.baseChange Ω) (E'.baseChange Ω) :=
  ψ.mapOf (g : Ω →+* Ω) (baseChange_map_algEquiv E g) (baseChange_map_algEquiv E' g)

variable (E) in
theorem ffCongr_ffMap_eq_galFF (g : Ω ≃ₐ[F] Ω) (f : (E.baseChange Ω).toAffine.FunctionField) :
    ffCongr (baseChange_map_algEquiv E g) (ffMap (g : Ω →+* Ω) (E.baseChange Ω) f) =
      galFF E g f := by
  have e : (ffCongr (baseChange_map_algEquiv E g)).toRingHom.comp
      (ffMap (g : Ω →+* Ω) (E.baseChange Ω)) = (galFF E g).toRingHom := by
    apply ringHom_ext_functionField
    · intro c
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
        ffMap_algebraMap, ffCongr_algebraMap, galFF_algebraMap]
    · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, ffMap_genX,
        ffCongr_genX, galFF_genX]
    · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, ffMap_genY,
        ffCongr_genY, galFF_genY]
  exact DFunLike.congr_fun e f

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.conj_alt_bis (g : Ω ≃ₐ[F] Ω)
    (ψ : Isogeny (E.baseChange Ω) (E'.baseChange Ω)) : (ψ.conj g).x = galFF E g ψ.x := by
  rw [Isogeny.conj, Isogeny.mapOf_alt, ffCongr_ffMap_eq_galFF]

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.conj_y (g : Ω ≃ₐ[F] Ω)
    (ψ : Isogeny (E.baseChange Ω) (E'.baseChange Ω)) : (ψ.conj g).y = galFF E g ψ.y := by
  rw [Isogeny.conj, Isogeny.mapOf_y, ffCongr_ffMap_eq_galFF]


variable (E E') in
theorem map_galFF_curve' (g : Ω ≃ₐ[F] Ω) :
    ((E'.baseChange Ω).baseChange (E.baseChange Ω).toAffine.FunctionField).map
      (galFF E g : _ →+* _) =
      (E'.baseChange Ω).baseChange (E.baseChange Ω).toAffine.FunctionField := by
  have e : ∀ a : F, galFF E g (algebraMap Ω (E.baseChange Ω).toAffine.FunctionField
      (algebraMap F Ω a)) = algebraMap Ω _ (algebraMap F Ω a) := fun a => by
    rw [galFF_algebraMap, AlgEquiv.commutes]
  ext <;> exact e _


variable (E E') in
noncomputable def galPt (g : Ω ≃ₐ[F] Ω) :
    ((E'.baseChange Ω).baseChange (E.baseChange Ω).toAffine.FunctionField).toAffine.Point →+
      ((E'.baseChange Ω).baseChange (E.baseChange Ω).toAffine.FunctionField).toAffine.Point :=
  autPoint _ (galFF E g) (map_galFF_curve' E E' g)

theorem galPt_val (g : Ω ≃ₐ[F] Ω) (ψ : Isogeny (E.baseChange Ω) (E'.baseChange Ω)) :
    galPt E E' g ψ.1 = (ψ.conj g).1 := by
  rw [ψ.val_eq, galPt, autPoint_some, (ψ.conj g).val_eq]
  exact point_some_congr (ψ.conj_alt_bis g).symm (ψ.conj_y g).symm

theorem galPt_constMap [DecidableEq Ω] (g : Ω ≃ₐ[F] Ω) (c : (E'.baseChange Ω).toAffine.Point) :
    galPt E E' g (constMap (E'.baseChange Ω) (E.baseChange Ω).toAffine.FunctionField c) =
      constMap (E'.baseChange Ω) (E.baseChange Ω).toAffine.FunctionField
        (galPointsHom F Ω E' g c) := by
  cases c with
  | zero => rfl
  | some x y h =>
    show autPoint _ _ _ (Point.some _ _ _) = Point.some _ _ _
    rw [autPoint_some]
    exact point_some_congr (galFF_algebraMap E g x) (galFF_algebraMap E g y)

theorem galPt_map_translate [IsAlgClosed Ω] [DecidableEq Ω] (g : Ω ≃ₐ[F] Ω)
    (R : (E.baseChange Ω).toAffine.Point)
    (Q : ((E'.baseChange Ω).baseChange (E.baseChange Ω).toAffine.FunctionField).toAffine.Point) :
    galPt E E' g (Point.map (translate (E.baseChange Ω) R) Q) =
      Point.map (translate (E.baseChange Ω) (galPointsHom F Ω E g R)) (galPt E E' g Q) := by
  cases Q with
  | zero => rfl
  | some a b h =>
    rw [Point.map_some, galPt, autPoint_some, autPoint_some, Point.map_some]
    exact point_some_congr (galFF_translate E g R a) (galFF_translate E g R b)

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.pointMap_conj [IsAlgClosed Ω] [DecidableEq Ω]
    (g : Ω ≃ₐ[F] Ω) (ψ : Isogeny (E.baseChange Ω) (E'.baseChange Ω))
    (R : (E.baseChange Ω).toAffine.Point) :
    (ψ.conj g).pointMap (galPointsHom F Ω E g R) = galPointsHom F Ω E' g (ψ.pointMap R) := by
  apply Isogeny.pointMap_eq_of_map_translate
  have h := congrArg (galPt E E' g) (ψ.map_translate R)
  rw [galPt_map_translate, map_add (f := _), galPt_val, galPt_constMap] at h
  exact h

end Conj

section Torsion

variable {F Ω : Type u} [Field F] [Field Ω] [Algebra F Ω] [DecidableEq Ω]
variable {E E' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]

theorem isAlgebraic_of_zsmul_eq_zero {n : ℤ} (hn : n ≠ 0) {x y : Ω}
    (h : (E.baseChange Ω).toAffine.Nonsingular x y)
    (hR : n • (Point.some x y h : (E.baseChange Ω).toAffine.Point) = 0) :
    IsAlgebraic F x ∧ IsAlgebraic F y := by
  have hx : IsAlgebraic F x := by
    rcases (zsmul_eq_zero_iff_ΨSq (E.baseChange Ω) n _).mp hR with h0 | ⟨x', y', h', he, hev⟩
    · exact absurd h0 (Point.some_ne_zero h)
    · have hxx : x = x' := (Point.some.inj he).1
      refine ⟨E.ΨSq n, ΨSq_ne_zero_of_ne_zero E hn, ?_⟩
      rw [hxx, ← eval_map_algebraMap, ← WeierstrassCurve.map_ΨSq]
      exact hev
  refine ⟨hx, ?_⟩
  have hxi : IsIntegral F x := hx.isIntegral
  set A := integralClosure F Ω
  have hb : _root_.IsIntegral F (algebraMap F Ω E.a₁ * x + algebraMap F Ω E.a₃) :=
    (isIntegral_algebraMap.mul hxi).add isIntegral_algebraMap
  have hc : _root_.IsIntegral F (x ^ 3 + algebraMap F Ω E.a₂ * x ^ 2 + algebraMap F Ω E.a₄ * x +
      algebraMap F Ω E.a₆) :=
    (((hxi.pow 3).add (isIntegral_algebraMap.mul (hxi.pow 2))).add
      (isIntegral_algebraMap.mul hxi)).add isIntegral_algebraMap
  let b : A := ⟨_, hb⟩
  let c : A := ⟨_, hc⟩
  let q : A[X] := X ^ 2 + C b * X - C c
  have hmon : q.Monic := by
    simp only [q]
    monicity!
  have heq : aeval y q = 0 := by
    have e := (equation_iff _ _).mp h.1
    simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at e
    simp only [q, map_sub, map_add (f := _), map_mul, map_pow, aeval_X, aeval_C]
    show y ^ 2 + (algebraMap F Ω E.a₁ * x + algebraMap F Ω E.a₃) * y -
      (x ^ 3 + algebraMap F Ω E.a₂ * x ^ 2 + algebraMap F Ω E.a₄ * x + algebraMap F Ω E.a₆) = 0
    linear_combination e
  exact (isIntegral_trans (R := F) (A := A) y ⟨q, hmon, heq⟩).isAlgebraic

theorem galPointsHom_eq_self_of_zsmul_eq_zero (g : Ω ≃ₐ[F] Ω)
    (hg : ∀ z : Ω, IsAlgebraic F z → g z = z) {n : ℤ} (hn : n ≠ 0)
    {R : (E.baseChange Ω).toAffine.Point} (hR : n • R = 0) : galPointsHom F Ω E g R = R := by
  cases R with
  | zero => exact map_zero _
  | some x y h =>
    obtain ⟨hx, hy⟩ := isAlgebraic_of_zsmul_eq_zero hn h hR
    exact galPointsHom_some_eq_self F Ω E h (hg x hx) (hg y hy)

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.conj_eq_self [IsAlgClosed Ω] (g : Ω ≃ₐ[F] Ω)
    (hg : ∀ z : Ω, IsAlgebraic F z → g z = z)
    (ψ : Isogeny (E.baseChange Ω) (E'.baseChange Ω)) : ψ.conj g = ψ := by
  have hfix : ∀ {n : ℤ}, n ≠ 0 → ∀ R : (E.baseChange Ω).toAffine.Point, n • R = 0 →
      (ψ.conj g).pointMap R = ψ.pointMap R := by
    intro n hn R hR
    have h1 := ψ.pointMap_conj g R
    rw [galPointsHom_eq_self_of_zsmul_eq_zero g hg hn hR] at h1
    rw [h1]
    apply galPointsHom_eq_self_of_zsmul_eq_zero g hg hn
    rw [← Isogeny.pointHom_apply, ← map_zsmul, hR, map_zero]
  set χ := (ψ.conj g).1 - ψ.1 with hχ
  have hmem : χ ∈ isogHom (E.baseChange Ω) (E'.baseChange Ω) :=
    (isogHom _ _).sub_mem (ψ.conj g).respectsAdd ψ.respectsAdd
  by_contra hne
  have hχ0 : (⟨χ, hmem⟩ : isogHom (E.baseChange Ω) (E'.baseChange Ω)) ≠ 0 := by
    intro h0
    apply hne
    apply Isogeny.ext'
    have h0' := congrArg Subtype.val h0
    exact sub_eq_zero.mp h0'
  set φχ := isogOfHom ⟨χ, hmem⟩ hχ0
  have hker : ∀ {n : ℤ}, n ≠ 0 → ∀ R, n • R = 0 → R ∈ φχ.pointHom.ker := by
    intro n hn R hR
    rw [AddMonoidHom.mem_ker, Isogeny.pointHom_apply]
    apply Isogeny.pointMap_eq_of_map_translate
    rw [isogOfHom_val, map_zero, add_zero]
    show Point.map _ ((ψ.conj g).1 - ψ.1) = (ψ.conj g).1 - ψ.1
    rw [map_sub, Isogeny.map_translate, Isogeny.map_translate, hfix hn R hR]
    abel
  obtain ⟨ℓ, hℓ2, hℓ⟩ : ∃ ℓ : ℕ, 2 ≤ ℓ ∧ (ℓ : Ω) ≠ 0 := by
    by_cases h2 : ((2 : ℕ) : Ω) = 0
    · refine ⟨3, by norm_num, ?_⟩
      have e : ((3 : ℕ) : Ω) = ((2 : ℕ) : Ω) + 1 := by push_cast; ring
      rw [e, h2, zero_add]
      exact one_ne_zero
    · exact ⟨2, le_refl 2, h2⟩
  set d := φχ.degree
  set n : ℤ := (ℓ : ℤ) ^ (d + 1) with hn
  have hnΩ : (n : Ω) ≠ 0 := by
    rw [hn]
    push_cast
    exact pow_ne_zero _ hℓ
  have hn0 : n ≠ 0 := fun h => hnΩ (by rw [h, Int.cast_zero])
  have hcard := card_zsmul_eq_zero (E.baseChange Ω) hnΩ
  have hle : Nat.card {P : (E.baseChange Ω).toAffine.Point // n • P = 0} ≤
      Nat.card φχ.pointHom.ker :=
    Nat.card_le_card_of_injective (fun P => ⟨P.1, hker hn0 P.1 P.2⟩)
      (by intro a b h; simp only [Subtype.mk.injEq] at h; exact Subtype.ext h)
  have hkd := φχ.card_ker_le_degree
  have hnat : n.natAbs = ℓ ^ (d + 1) := by
    rw [hn, Int.natAbs_pow, Int.natAbs_natCast]
  rw [hcard, hnat] at hle
  have h2 : d < 2 ^ (d + 1) := (Nat.lt_two_pow_self).trans (Nat.pow_lt_pow_right (by norm_num) (by omega))
  have h3 : 2 ^ (d + 1) ≤ ℓ ^ (d + 1) := Nat.pow_le_pow_left hℓ2 _
  have h4 : ℓ ^ (d + 1) ≤ (ℓ ^ (d + 1)) ^ 2 := Nat.le_self_pow (by norm_num) _
  omega

end Torsion

end GroundTheory.Global
end

namespace GroundTheory.Global

open Polynomial WeierstrassCurve IntermediateField GroundTheory.Arith.Abelian
open WeierstrassCurve.Affine (Point equation_iff)

universe u

section SlopeTestRemainingChoices

theorem map_aeval_of_comp {A B K K' : Type*} [CommRing A] [CommRing B] [CommRing K]
    [CommRing K'] [Algebra A K] [Algebra B K'] (f : K →+* K') (τ : A →+* B)
    (h : ∀ a, f (algebraMap A K a) = algebraMap B K' (τ a)) (p : A[X]) (z : K) :
    f (aeval z p) = aeval (f z) (p.map τ) := by
  rw [aeval_def, hom_eval₂, aeval_def, eval₂_map]
  congr 1
  ext a
  exact h a

theorem eq_of_add_mul_genY_eq {K : Type*} [Field K] {W : WeierstrassCurve K}
    {a b a' b' : W.toAffine.FunctionField} (ha : a ∈ K⟮genX W⟯) (hb : b ∈ K⟮genX W⟯)
    (ha' : a' ∈ K⟮genX W⟯) (hb' : b' ∈ K⟮genX W⟯)
    (h : a + b * genY W = a' + b' * genY W) : a = a' ∧ b = b' := by
  by_cases hbb : b = b'
  · subst hbb
    exact ⟨add_right_cancel h, rfl⟩
  · exfalso
    apply genY_not_mem W
    have hne : b - b' ≠ 0 := sub_ne_zero.mpr hbb
    have e : genY W = (a' - a) / (b - b') := by
      rw [eq_div_iff hne]
      linear_combination h
    rw [e]
    exact div_mem (sub_mem ha' ha) (sub_mem hb hb')

theorem ffCongr_aeval {K : Type u} [Field K] {C D : WeierstrassCurve K} (h : C = D) (p : K[X]) :
    ffCongr h (aeval (genX C) p) = aeval (genX D) p := by
  subst h
  rfl

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.congr_congr {K : Type u} [Field K]
    {C D C' D' : WeierstrassCurve K} [C.IsElliptic] [D.IsElliptic] [C'.IsElliptic]
    [D'.IsElliptic] (hC : C = D) (hC' : C' = D') (φ : Isogeny C C') :
    (φ.congr hC hC').congr hC.symm hC'.symm = φ := by
  subst hC hC'
  rfl

end SlopeTestRemainingChoices

section Galois

variable {F Ω : Type u} [Field F] [Field Ω] [Algebra F Ω] (E : WeierstrassCurve F)

theorem galFF_aeval (g : Ω ≃ₐ[F] Ω) (p : Polynomial Ω) :
    galFF E g (aeval (genX (E.baseChange Ω)) p) =
      aeval (genX (E.baseChange Ω)) (p.map (g : Ω →+* Ω)) := by
  have := map_aeval_of_comp (galFF E g).toRingHom (g : Ω →+* Ω)
    (fun c => galFF_algebraMap E g c) p (genX (E.baseChange Ω))
  simpa [galFF_genX] using this

theorem galFF_ratEmb (g : Ω ≃ₐ[F] Ω) (r : RatFunc Ω) :
    galFF E g (ratEmb (E.baseChange Ω) r) = ratEmb (E.baseChange Ω)
      (algebraMap _ _ (r.num.map (g : Ω →+* Ω)) / algebraMap _ _ (r.denom.map (g : Ω →+* Ω))) := by
  conv_lhs => rw [← RatFunc.num_div_denom r]
  rw [ratEmb_div, ratEmb_div, map_div₀, galFF_aeval, galFF_aeval]

theorem map_eq_of_galFF_ratEmb (g : Ω ≃ₐ[F] Ω) {r : RatFunc Ω}
    (h : galFF E g (ratEmb (E.baseChange Ω) r) = ratEmb (E.baseChange Ω) r) :
    r.num.map (g : Ω →+* Ω) = r.num ∧ r.denom.map (g : Ω →+* Ω) = r.denom := by
  rw [galFF_ratEmb] at h
  have h2 := ratEmb_injective (E.baseChange Ω) h
  have hcop : IsCoprime (r.num.map (g : Ω →+* Ω)) (r.denom.map (g : Ω →+* Ω)) := by
    simpa using r.isCoprime_num_denom.map (mapRingHom (g : Ω →+* Ω))
  obtain ⟨h1, h1'⟩ := num_denom_div_of_isCoprime (r.monic_denom.map (g : Ω →+* Ω)) hcop
  rw [h2] at h1 h1'
  exact ⟨h1.symm, h1'.symm⟩

theorem galFF_mem_adjoin_genX (g : Ω ≃ₐ[F] Ω) {a : (E.baseChange Ω).toAffine.FunctionField}
    (ha : a ∈ Ω⟮genX (E.baseChange Ω)⟯) : galFF E g a ∈ Ω⟮genX (E.baseChange Ω)⟯ := by
  rw [← fieldRange_ratEmb] at ha ⊢
  obtain ⟨r, rfl⟩ := ha
  exact ⟨_, (galFF_ratEmb E g r).symm⟩

end Galois

section Descent

variable {F Ω : Type u} [Field F] [Field Ω] [IsAlgClosed Ω] [Algebra F Ω]
variable {E E' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]

omit [IsAlgClosed Ω] in
theorem map_toAlgHom_baseChange (F₁ : IntermediateField F Ω) (W : WeierstrassCurve F) :
    (W.baseChange F₁).map (algebraMap F₁ Ω) = W.baseChange Ω :=
  WeierstrassCurve.map_baseChange (R := F) (S := F) W (IsScalarTower.toAlgHom F F₁ Ω)

theorem isAlgebraic_of_forall_algEquiv {c : Ω}
    (h : ∀ g : Ω ≃ₐ[algebraicClosure F Ω] Ω, g c = c) : IsAlgebraic F c := by
  haveI : IsAlgClosed (algebraicClosure F Ω) := IsAlgClosure.isAlgClosed F
  have hc := (mem_bot_iff_forall_algEquiv_apply_eq (F := algebraicClosure F Ω)).mpr h
  obtain ⟨a, rfl⟩ := IntermediateField.mem_bot.mp hc
  exact mem_algebraicClosure_iff.mp a.2

theorem isAlgebraic_coeffs [DecidableEq Ω] {r : RatFunc Ω}
    (h : ∀ g : Ω ≃ₐ[algebraicClosure F Ω] Ω,
      galFF E (g.restrictScalars F) (ratEmb (E.baseChange Ω) r) = ratEmb (E.baseChange Ω) r) :
    ∀ c ∈ r.num.coeffs ∪ r.denom.coeffs, IsAlgebraic F c := by
  intro c hc
  apply isAlgebraic_of_forall_algEquiv
  intro g
  obtain ⟨h1, h2⟩ := map_eq_of_galFF_ratEmb E (g.restrictScalars F) (h g)
  rcases Finset.mem_union.mp hc with hc | hc
  · obtain ⟨n, -, rfl⟩ := Polynomial.mem_coeffs_iff.mp hc
    have := congrArg (fun p : Polynomial Ω => p.coeff n) h1
    simpa using this
  · obtain ⟨n, -, rfl⟩ := Polynomial.mem_coeffs_iff.mp hc
    have := congrArg (fun p : Polynomial Ω => p.coeff n) h2
    simpa using this

omit [IsAlgClosed Ω] in
theorem exists_map_eq_of_coeffs {S : Finset Ω} {p : Polynomial Ω} (hp : p.coeffs ⊆ S) :
    ∃ p₁ : Polynomial (IntermediateField.adjoin F (S : Set Ω)),
      p₁.map (algebraMap (IntermediateField.adjoin F (S : Set Ω)) Ω) = p := by
  rw [← Polynomial.mem_lifts, Polynomial.lifts_iff_coeff_lifts]
  intro n
  by_cases hn : p.coeff n = 0
  · exact ⟨0, by rw [hn, map_zero]⟩
  · exact ⟨⟨p.coeff n, IntermediateField.subset_adjoin F _ (hp (coeff_mem_coeffs hn))⟩, rfl⟩

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.exists_finiteDimensional_mapOf_eq
    (ψ : Isogeny (E.baseChange Ω) (E'.baseChange Ω)) :
    ∃ F₁ : IntermediateField F Ω, FiniteDimensional F F₁ ∧
      ∃ (φ : Isogeny (E.baseChange F₁) (E'.baseChange F₁))
        (h : (E.baseChange F₁).map (algebraMap F₁ Ω) = E.baseChange Ω)
        (h' : (E'.baseChange F₁).map (algebraMap F₁ Ω) = E'.baseChange Ω),
        φ.mapOf (algebraMap F₁ Ω) h h' = ψ := by
  classical
  have hfix : ∀ g : Ω ≃ₐ[algebraicClosure F Ω] Ω, ψ.conj (g.restrictScalars F) = ψ :=
    fun g => ψ.conj_eq_self _ (fun z hz => g.commutes ⟨z, mem_algebraicClosure_iff.mpr hz⟩)
  have hxfix : ∀ g : Ω ≃ₐ[algebraicClosure F Ω] Ω, galFF E (g.restrictScalars F) ψ.x = ψ.x :=
    fun g => by rw [← Isogeny.conj_alt_bis, hfix g]
  have hyfix : ∀ g : Ω ≃ₐ[algebraicClosure F Ω] Ω, galFF E (g.restrictScalars F) ψ.y = ψ.y :=
    fun g => by rw [← Isogeny.conj_y, hfix g]
  obtain ⟨r, hr⟩ := ψ.exists_ratEmb_eq_x
  obtain ⟨a, b, ha, hb, hab⟩ := exists_eq_add_mul_genY (E.baseChange Ω) ψ.y
  have ha' := ha
  have hb' := hb
  rw [← fieldRange_ratEmb] at ha' hb'
  obtain ⟨r₂, hr₂⟩ := ha'
  obtain ⟨r₃, hr₃⟩ := hb'
  change ratEmb (E.baseChange Ω) r₂ = a at hr₂
  change ratEmb (E.baseChange Ω) r₃ = b at hr₃
  have hab_fix : ∀ g : Ω ≃ₐ[algebraicClosure F Ω] Ω,
      galFF E (g.restrictScalars F) a = a ∧ galFF E (g.restrictScalars F) b = b := by
    intro g
    have e := hyfix g
    rw [hab, map_add (f := _), map_mul, galFF_genY] at e
    exact eq_of_add_mul_genY_eq (galFF_mem_adjoin_genX E _ ha) (galFF_mem_adjoin_genX E _ hb)
      ha hb e
  have h1 := isAlgebraic_coeffs (E := E) (r := r) (fun g => by rw [hr]; exact hxfix g)
  have h2 := isAlgebraic_coeffs (E := E) (r := r₂) (fun g => by rw [hr₂]; exact (hab_fix g).1)
  have h3 := isAlgebraic_coeffs (E := E) (r := r₃) (fun g => by rw [hr₃]; exact (hab_fix g).2)
  set S : Finset Ω := (r.num.coeffs ∪ r.denom.coeffs) ∪ (r₂.num.coeffs ∪ r₂.denom.coeffs) ∪
    (r₃.num.coeffs ∪ r₃.denom.coeffs) with hS
  have hSalg : ∀ c ∈ (S : Set Ω), _root_.IsIntegral F c := by
    intro c hc
    rcases Finset.mem_union.mp hc with hc | hc
    · rcases Finset.mem_union.mp hc with hc | hc
      · exact (h1 c hc).isIntegral
      · exact (h2 c hc).isIntegral
    · exact (h3 c hc).isIntegral
  set F₁ := IntermediateField.adjoin F (S : Set Ω)
  haveI : FiniteDimensional F F₁ := IntermediateField.finiteDimensional_adjoin hSalg
  obtain ⟨n₁, hn₁⟩ := exists_map_eq_of_coeffs (F := F) (S := S) (p := r.num)
    (fun c hc => by simp [hS, hc])
  obtain ⟨d₁, hd₁⟩ := exists_map_eq_of_coeffs (F := F) (S := S) (p := r.denom)
    (fun c hc => by simp [hS, hc])
  obtain ⟨n₂, hn₂⟩ := exists_map_eq_of_coeffs (F := F) (S := S) (p := r₂.num)
    (fun c hc => by simp [hS, hc])
  obtain ⟨d₂, hd₂⟩ := exists_map_eq_of_coeffs (F := F) (S := S) (p := r₂.denom)
    (fun c hc => by simp [hS, hc])
  obtain ⟨n₃, hn₃⟩ := exists_map_eq_of_coeffs (F := F) (S := S) (p := r₃.num)
    (fun c hc => by simp [hS, hc])
  obtain ⟨d₃, hd₃⟩ := exists_map_eq_of_coeffs (F := F) (S := S) (p := r₃.denom)
    (fun c hc => by simp [hS, hc])
  set σ₁ := algebraMap F₁ Ω
  set C₁ := E.baseChange F₁
  have h := map_toAlgHom_baseChange F₁ E
  have h' := map_toAlgHom_baseChange F₁ E'
  set ψ₁ := ψ.congr h.symm h'.symm
  set X₁ := genX C₁
  set x₁ : C₁.toAffine.FunctionField := aeval X₁ n₁ / aeval X₁ d₁
  set y₁ : C₁.toAffine.FunctionField :=
    aeval X₁ n₂ / aeval X₁ d₂ + aeval X₁ n₃ / aeval X₁ d₃ * genY C₁
  have hrat : ∀ (s : RatFunc Ω) (p q : Polynomial F₁), p.map σ₁ = s.num → q.map σ₁ = s.denom →
      ffMap σ₁ C₁ (aeval X₁ p / aeval X₁ q) = ffCongr h.symm (ratEmb (E.baseChange Ω) s) := by
    intro s p q hp hq
    conv_rhs => rw [← RatFunc.num_div_denom s]
    rw [ratEmb_div, map_div₀, map_div₀, ffCongr_aeval, ffCongr_aeval, ffMap_aeval, ffMap_aeval,
      ffMap_genX, hp, hq]
  have hx₁ : ffMap σ₁ C₁ x₁ = ψ₁.x := by
    rw [Isogeny.congr_alt, ← hr]
    exact hrat r n₁ d₁ hn₁ hd₁
  have hy₁ : ffMap σ₁ C₁ y₁ = ψ₁.y := by
    rw [Isogeny.congr_y, hab, map_add (f := _), map_mul, ← hr₂, ← hr₃, map_add (f := _), map_mul,
      hrat r₂ n₂ d₂ hn₂ hd₂, hrat r₃ n₃ d₃ hn₃ hd₃, ffMap_genY, ffCongr_genY]
  refine ⟨F₁, inferInstance, Isogeny.ofMap σ₁ ψ₁ x₁ y₁ hx₁ hy₁, h, h', ?_⟩
  rw [Isogeny.mapOf, Isogeny.map_ofMap]
  exact Isogeny.congr_congr h.symm h'.symm ψ

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.exists_numberField_mapOf_eq [NumberField F]
    (ψ : Isogeny (E.baseChange Ω) (E'.baseChange Ω)) :
    ∃ F₁ : IntermediateField F Ω, NumberField F₁ ∧
      ∃ (φ : Isogeny (E.baseChange F₁) (E'.baseChange F₁))
        (h : (E.baseChange F₁).map (algebraMap F₁ Ω) = E.baseChange Ω)
        (h' : (E'.baseChange F₁).map (algebraMap F₁ Ω) = E'.baseChange Ω),
        φ.mapOf (algebraMap F₁ Ω) h h' = ψ := by
  obtain ⟨F₁, hfin, rest⟩ := ψ.exists_finiteDimensional_mapOf_eq
  exact ⟨F₁, NumberField.of_module_finite F F₁, rest⟩

end Descent

section OverF

variable {F Ω : Type u} [Field F] [Field Ω] [Algebra F Ω] [DecidableEq Ω]
variable {E E' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]


omit [DecidableEq Ω] in
theorem galFF_bcEmb (g : Ω ≃ₐ[F] Ω) (f : E.toAffine.FunctionField) :
    galFF E g (bcEmb (F' := Ω) E f) = bcEmb (F' := Ω) E f := by
  have e : (galFF E g).toRingHom.comp (bcEmb (F' := Ω) E).toRingHom =
      (bcEmb (F' := Ω) E).toRingHom := by
    apply ringHom_ext_functionField
    · intro a
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
        AlgHom.toRingHom_eq_coe, AlgHom.commutes]
      exact galFF_algebraMap_base E g a
    · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
        AlgHom.toRingHom_eq_coe, bcEmb_genX]
      exact galFF_genX E g
    · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
        AlgHom.toRingHom_eq_coe, bcEmb_genY]
      exact galFF_genY E g
  exact DFunLike.congr_fun e f

theorem conj_isogBaseChange (g : Ω ≃ₐ[F] Ω) (φ : Isogeny E E') :
    (isogBaseChange (F' := Ω) φ).conj g = isogBaseChange (F' := Ω) φ :=
  Isogeny.ext_xy (by rw [Isogeny.conj_alt_bis, isogBaseChange_alt, galFF_bcEmb])
    (by rw [Isogeny.conj_y, isogBaseChange_y, galFF_bcEmb])

theorem pointMap_isogBaseChange_galPointsHom [IsAlgClosed Ω] (g : Ω ≃ₐ[F] Ω) (φ : Isogeny E E')
    (R : (E.baseChange Ω).toAffine.Point) :
    (isogBaseChange (F' := Ω) φ).pointMap (galPointsHom F Ω E g R) =
      galPointsHom F Ω E' g ((isogBaseChange (F' := Ω) φ).pointMap R) := by
  have := (isogBaseChange (F' := Ω) φ).pointMap_conj g R
  rwa [conj_isogBaseChange] at this

theorem exists_pointMap_isogBaseChange_eq [PerfectField F] [IsAlgClosed Ω] [DecidableEq F] (φ : Isogeny E E')
    (P : E.toAffine.Point) :
    ∃ P' : E'.toAffine.Point,
      (isogBaseChange (F' := Ω) φ).pointMap (constMap E Ω P) = constMap E' Ω P' := by
  set Q := (isogBaseChange (F' := Ω) φ).pointMap (constMap E Ω P)
  have hfix : ∀ g : Ω ≃ₐ[F] Ω, galPointsHom F Ω E' g Q = Q := by
    intro g
    rw [← pointMap_isogBaseChange_galPointsHom]
    congr 1
    exact map_constMap E (g : Ω →ₐ[F] Ω) P
  cases hQ : Q with
  | zero => exact ⟨0, (map_zero (constMap E' Ω)).symm⟩
  | some u v h =>
    rw [hQ] at hfix
    have key : ∀ g : Ω ≃ₐ[F] Ω, g u = u ∧ g v = v := by
      intro g
      have := hfix g
      obtain ⟨h', e⟩ := galPointsHom_some F Ω E' g h
      rw [e] at this
      exact ⟨(Point.some.inj this).1, (Point.some.inj this).2⟩
    have hu : u ∈ (⊥ : IntermediateField F Ω) :=
      mem_bot_iff_forall_algEquiv_apply_eq.mpr fun g => (key g).1
    have hv : v ∈ (⊥ : IntermediateField F Ω) :=
      mem_bot_iff_forall_algEquiv_apply_eq.mpr fun g => (key g).2
    obtain ⟨a, rfl⟩ := IntermediateField.mem_bot.mp hu
    obtain ⟨b, rfl⟩ := IntermediateField.mem_bot.mp hv
    have hab : E'.toAffine.Nonsingular a b :=
      (E'.toAffine.baseChange_nonsingular (f := Algebra.ofId F Ω) (algebraMap F Ω).injective a b).mp h
    exact ⟨.some a b hab, rfl⟩


variable (Ω) in
noncomputable def pointHomOver [PerfectField F] [IsAlgClosed Ω] [DecidableEq F] (φ : Isogeny E E') :
    E.toAffine.Point →+ E'.toAffine.Point :=
  AddMonoidHom.mk' (fun P => (exists_pointMap_isogBaseChange_eq (Ω := Ω) φ P).choose)
    (fun P₁ P₂ => by
      apply constMap_injective E' Ω
      have e₃ := (exists_pointMap_isogBaseChange_eq (Ω := Ω) φ (P₁ + P₂)).choose_spec
      have e₁ := (exists_pointMap_isogBaseChange_eq (Ω := Ω) φ P₁).choose_spec
      have e₂ := (exists_pointMap_isogBaseChange_eq (Ω := Ω) φ P₂).choose_spec
      rw [map_add (constMap E' Ω), ← e₃, ← e₁, ← e₂, map_add (constMap E Ω),
        Isogeny.pointMap_add])

theorem constMap_pointHomOver [PerfectField F] [IsAlgClosed Ω] [DecidableEq F] (φ : Isogeny E E')
    (P : E.toAffine.Point) :
    constMap E' Ω (pointHomOver Ω φ P) =
      (isogBaseChange (F' := Ω) φ).pointMap (constMap E Ω P) :=
  (exists_pointMap_isogBaseChange_eq (Ω := Ω) φ P).choose_spec.symm


end OverF

end GroundTheory.Global
