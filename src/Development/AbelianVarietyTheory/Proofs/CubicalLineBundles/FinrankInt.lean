module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AppellHumbertUnifTangentWeilPairing
public import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsAbelianSchemeModelOfIsogenyDedekind
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSimTrivialOfMult

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FinrankInt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM.SelfDualDatum

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_enum (H : Host E) : ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H 1 0 ty ∧
    ∀ i, ty i (H.rt : E) = H.rt0 := by
  classical
  let e := (Fintype.equivFin {τ : E →+* ℂ // τ (H.rt : E) = H.rt0}).symm
  refine ⟨_, fun i => (e i).1, fun τ => ⟨fun h => ?_, fun h => ?_⟩, fun i => (e i).2⟩
  · rw [Nat.card_eq_one_iff_unique]
    exact ⟨⟨fun a b => Subtype.ext (e.injective (Subtype.ext (a.2.trans b.2.symm)))⟩,
      ⟨⟨e.symm ⟨τ, h⟩, by simp⟩⟩⟩
  · haveI : IsEmpty {i // (e i).1 = τ} := ⟨fun a => h (a.2 ▸ (e a.1).2)⟩
    simp

theorem trace_eq (H : Host E) {g : ℕ} {ty : Fin g → (E →+* ℂ)} (hty : IsTypeFn H 1 0 ty) (a : E) :
    ((Algebra.trace ℚ E a : ℚ) : ℝ) = 2 * (∑ i, ty i a).re := by
  classical
  let e := (Fintype.equivFin (E →+* ℂ)).symm
  have he : IsTypeFn H 1 1 e := fun τ => by
    have : Nat.card {i // e i = τ} = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => Subtype.ext (e.injective (a.2.trans b.2.symm))⟩, ⟨⟨e.symm τ, by simp⟩⟩⟩
    exact ⟨fun _ => this, fun _ => this⟩
  have h1 := PeriodNonempty.sum_type H hty a
  have h2 := PeriodNonempty.sum_type H he a
  have h3 : ((Algebra.trace ℚ E a : ℚ) : ℂ) = ∑ i, e i a := by
    rw [← eq_ratCast (algebraMap ℚ ℂ), trace_eq_sum_embeddings (E := ℂ), Equiv.sum_comp e (fun τ => τ a)]
    exact (Equiv.sum_comp (RingHom.equivRatAlgHom E ℂ) (fun σ => σ a)).symm
  simp only [Nat.cast_one, _root_.one_mul, Nat.cast_zero, zero_mul, add_zero] at h1 h2
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h2, Finset.sum_add_distrib, ← map_sum, ← h1] at h3
  have := congrArg Complex.re h3
  simp only [Complex.add_re, Complex.conj_re, Complex.ratCast_re] at this
  linarith

theorem exists_form (𝔄 : Submodule (𝓞 E) E) (ξ : E) (hξ0 : ξ ≠ 0)
    (hdual : ∀ x : E, (∀ y ∈ 𝔄, ∃ n : ℤ, Algebra.trace ℚ E (ξ * x * IsCMField.complexConj E y) = n) ↔ x ∈ 𝔄) :
    ∃ EF : LinearMap.BilinForm ℤ 𝔄, Function.Bijective EF ∧
      ∀ x y : 𝔄, (EF x y : ℚ) = Algebra.trace ℚ E (ξ * (x : E) * IsCMField.complexConj E (y : E)) := by
  choose f hf using fun x y : 𝔄 => (hdual x).2 x.2 y y.2
  let EF : LinearMap.BilinForm ℤ 𝔄 := LinearMap.mk₂ ℤ f
    (fun x x' y => by
      apply Int.cast_injective (α := ℚ)
      rw [Int.cast_add, ← hf, ← hf, ← hf, Submodule.coe_add, mul_add, add_mul, map_add (f := _)])
    (fun c x y => by
      apply Int.cast_injective (α := ℚ)
      rw [smul_eq_mul, Int.cast_mul c, ← hf, ← hf, ← zsmul_eq_mul _ c, ← map_zsmul]
      congr 1
      simp
      ring)
    (fun x y y' => by
      apply Int.cast_injective (α := ℚ)
      rw [Int.cast_add, ← hf, ← hf, ← hf, Submodule.coe_add, map_add (f := _), mul_add, map_add (f := _)])
    (fun c x y => by
      apply Int.cast_injective (α := ℚ)
      rw [smul_eq_mul, Int.cast_mul c, ← hf, ← hf, ← zsmul_eq_mul _ c, ← map_zsmul]
      congr 1
      simp
      ring)
  have hEF : ∀ x y : 𝔄, (EF x y : ℚ) = Algebra.trace ℚ E (ξ * (x : E) * IsCMField.complexConj E (y : E)) :=
    fun x y => (hf x y).symm
  refine ⟨EF, ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, fun φ => ?_⟩, hEF⟩
  · by_contra h0
    have hx0 : (x : E) ≠ 0 := fun h => h0 (Subtype.ext h)
    have hz : ∀ a : 𝓞 E, Algebra.trace ℚ E (ξ * x * IsCMField.complexConj E x * IsCMField.complexConj E a) = 0 :=
      fun a => by
        have := hEF x (a • x)
        rw [hx, Submodule.coe_smul, Algebra.smul_def, map_mul (IsCMField.complexConj E)] at this
        simp only [LinearMap.zero_apply, Int.cast_zero] at this
        rw [this]
        congr 1
        simp only [RingOfIntegers.coe_eq_algebraMap]
        ring
    have hall : ∀ z : E, Algebra.trace ℚ E (ξ * x * IsCMField.complexConj E x * IsCMField.complexConj E z) = 0 :=
      fun z => by
        obtain ⟨n, hn, hi⟩ := exists_integral_multiples ℤ ℚ {z}
        have := hz ⟨n • z, hi z (by simp)⟩
        change Algebra.trace ℚ E (_ * IsCMField.complexConj E (n • z)) = 0 at this
        rw [map_zsmul, mul_smul_comm, map_zsmul] at this
        exact (smul_eq_zero.1 this).resolve_left hn
    have := (traceForm_nondegenerate ℚ E).1 (ξ * x * IsCMField.complexConj E x) fun z => by
      simpa [Algebra.traceForm_apply] using hall (IsCMField.complexConj E z)
    simp [hξ0, hx0] at this
  · obtain ⟨g, hg⟩ := (Module.Baer.of_divisible ℚ).extension_property_addMonoidHom
      𝔄.subtype.toAddMonoidHom 𝔄.subtype_injective ((Int.castAddHom ℚ).comp φ.toAddMonoidHom)
    have hg' : ∀ x : 𝔄, g x = φ x := fun x => DFunLike.congr_fun hg x
    obtain ⟨z, hz⟩ := ((Algebra.traceForm ℚ E).toDual (traceForm_nondegenerate ℚ E)).surjective
      (g.comp (IsCMField.complexConj E : E →+* E).toAddMonoidHom).toRatLinearMap
    have hz' : ∀ y : E, Algebra.trace ℚ E (ξ * (z / ξ) * IsCMField.complexConj E y) = g y := fun y => by
      have := LinearMap.congr_fun hz (IsCMField.complexConj E y)
      rw [mul_div_cancel₀ _ hξ0]
      exact this.trans (by simp)
    refine ⟨⟨_, (hdual _).1 fun y hy => ⟨φ ⟨y, hy⟩, (hz' y).trans (hg' ⟨y, hy⟩)⟩⟩, LinearMap.ext fun y => ?_⟩
    apply Int.cast_injective (α := ℚ)
    rw [hEF, hz', hg']

omit [IsCMField E] in
theorem finrank_int (𝔄 : Submodule (𝓞 E) E) (hfg : 𝔄.FG) (hne : 𝔄 ≠ ⊥) :
    Module.finrank ℤ 𝔄 = Module.finrank ℚ E := by
  obtain ⟨N, hN, ψ, hψ⟩ := PrincipalDatum.exists_clear 𝔄 hfg
  have hNE : (N : E) ≠ 0 := by exact_mod_cast hN
  have hinj : Function.Injective ψ := fun x y h => by
    apply Subtype.ext
    apply mul_left_cancel₀ hNE
    rw [← hψ, ← hψ, h]
  haveI : Module.Finite ℤ 𝔄 := Module.Finite.of_injective (ψ.restrictScalars ℤ) hinj
  rw [← RingOfIntegers.rank]
  obtain ⟨x₀, hx₀, h0⟩ := (Submodule.ne_bot_iff _).1 hne
  refine le_antisymm (LinearMap.finrank_le_finrank_of_injective (f := ψ.restrictScalars ℤ) hinj)
    (LinearMap.finrank_le_finrank_of_injective
      (f := (LinearMap.toSpanSingleton (𝓞 E) 𝔄 ⟨x₀, hx₀⟩).restrictScalars ℤ) ?_)
  exact smul_left_injective (𝓞 E) (m := (⟨x₀, hx₀⟩ : 𝔄)) (by simpa using h0)

theorem exists_datum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (𝔄 : Submodule (𝓞 E) E) (ξ : E), 𝔄.FG → 𝔄 ≠ ⊥ → IsCMField.complexConj E ξ = -ξ → (∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → (τ ξ).im < 0) → (∀ x : E, (∀ y ∈ 𝔄, ∃ n : ℤ, Algebra.trace ℚ E (ξ * x * IsCMField.complexConj E y) = n) ↔ x ∈ 𝔄) → ∃ (D : Datum H) (e : D.La ≃ₗ[𝓞 E] 𝔄), D.p = 1 ∧ D.q = 0 ∧ ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * (e x : E) * IsCMField.complexConj E (e y : E)) := by
  intro E _ _ _ H 𝔄 ξ hfg hne hξ hneg hdual
  classical
  obtain ⟨g, ty, hty, hrt⟩ := exists_enum H
  have hg := PeriodDatum.two_mul_eq_of_isTypeFn H hty
  have hg0 : 0 < g := by
    have : 0 < Module.finrank ℚ E := Module.finrank_pos
    omega
  have hξ0 : ξ ≠ 0 := fun h => by simpa [h] using hneg _ (hrt ⟨0, hg0⟩)
  obtain ⟨EF, hbij, hEF⟩ := exists_form 𝔄 ξ hξ0 hdual
  have hre : ∀ i, (ty i ξ).re = 0 := fun i => by
    have h := IsCMField.complexEmbedding_complexConj E (ty i) ξ
    rw [hξ, map_neg] at h
    have := congrArg Complex.re h
    simp only [Complex.neg_re, Complex.conj_re] at this
    linarith
  let P : 𝔄 →+ (Fin g → ℂ) :=
    { toFun := fun x i => ty i (x : E)
      map_zero' := by funext i; simp
      map_add' := fun x y => by funext i; simp }
  have hP : ∀ x i, P x i = ty i (x : E) := fun _ _ => rfl
  let Hm : Matrix (Fin g) (Fin g) ℂ := Matrix.diagonal fun i => ((-2 * (ty i ξ).im : ℝ) : ℂ)
  have hHm : ∀ z w, hermForm Hm z w = ∑ i, ((-2 * (ty i ξ).im : ℝ) : ℂ) * (z i * starRingEnd ℂ (w i)) :=
    fun z w => by
      simp only [hermForm, Hm, dotProduct, Matrix.mulVec_diagonal, Pi.star_apply]
      exact Finset.sum_congr rfl fun i _ => by rw [mul_left_comm]; rfl
  have hH : Hm.IsHermitian := Matrix.isHermitian_diagonal_of_self_adjoint _ (by
    funext i
    exact Complex.conj_ofReal _)
  have hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re := fun z hz => by
    rw [hHm, Complex.re_sum]
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hz
    have hc : ∀ i, 0 < -2 * (ty i ξ).im := fun i => by linarith [hneg _ (hrt i)]
    refine Finset.sum_pos' (fun i _ => ?_) ⟨j, Finset.mem_univ _, ?_⟩
    · rw [Complex.mul_conj, ← Complex.ofReal_mul, Complex.ofReal_re]
      exact mul_nonneg (hc i).le (Complex.normSq_nonneg _)
    · rw [Complex.mul_conj, ← Complex.ofReal_mul, Complex.ofReal_re]
      exact mul_pos (hc j) (Complex.normSq_pos.2 hj)
  have him : ∀ x y, (hermForm Hm (P x) (P y)).im = EF x y := fun x y => by
    have h := trace_eq H hty (ξ * (x : E) * IsCMField.complexConj E (y : E))
    rw [← hEF, Rat.cast_intCast] at h
    rw [h, hHm, Complex.im_sum, Complex.re_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_mul, IsCMField.complexEmbedding_complexConj, hP, hP, _root_.mul_assoc (ty i ξ)]
    generalize ty i (x : E) * starRingEnd ℂ (ty i (y : E)) = u
    simp [hre]
    ring
  have hlin : ∀ (a : 𝓞 E) x i, P (a • x) i = ty i (a : E) * P x i := fun a x i => by
    rw [hP, hP, ← map_mul]
    rfl
  have hinj : Function.Injective P := fun x y h =>
    Subtype.ext ((ty ⟨0, hg0⟩).injective (congrFun h ⟨0, hg0⟩))
  have hdisc : DiscreteTopology P.range := by
    obtain ⟨hr0, hs⟩ := PrincipalDatum.principal_root_re_zero_im_sq H
    have hs0 : H.rt0.im ≠ 0 := fun h => by
      rw [h] at hs
      have := H.d_prime.pos
      have : (0 : ℝ) < H.d := by exact_mod_cast this
      linarith
    rw [discreteTopology_iff_isOpen_singleton_zero]
    refine ⟨{z | |H.rt0.im * (hermForm Hm z z).re| < 1}, ?_, ?_⟩
    · refine isOpen_lt ?_ continuous_const
      simp only [hHm]
      fun_prop
    · ext ⟨_, x, rfl⟩
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · intro h
        by_contra h0
        have h1 := hpos (P x) fun e => h0 (Subtype.ext e)
        have h2 := him (H.rt • x) x
        have h3 : P (H.rt • x) = H.rt0 • P x := funext fun i => by rw [hlin, hrt]; rfl
        rw [h3, PeriodDatum.hermForm_smul_left, Complex.mul_im, hr0, zero_mul, zero_add] at h2
        rw [h2] at h
        have h4 : EF (H.rt • x) x = 0 := Int.abs_lt_one_iff.1 (by exact_mod_cast h)
        rw [h4, Int.cast_zero] at h2
        exact (mul_ne_zero hs0 h1.ne') h2
      · intro h
        rw [show P x = 0 from congrArg Subtype.val h]
        simp [hermForm]
  have hspan : Submodule.span ℝ (Set.range P) = ⊤ := by
    have hz : Submodule.span ℤ (Set.range P) = LinearMap.range P.toIntLinearMap :=
      Submodule.span_eq (LinearMap.range P.toIntLinearMap)
    have h := Real.finrank_eq_int_finrank_of_discrete (s := Set.range P) (by rw [hz]; exact hdisc)
    apply Submodule.eq_top_of_finrank_eq
    rw [Set.finrank, Set.finrank, hz, LinearMap.finrank_range_of_inj (f := P.toIntLinearMap) hinj,
      finrank_int 𝔄 hfg hne] at h
    rw [h, ← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex, Module.finrank_fin_fun]
    omega
  have hadj : ∀ (a : 𝓞 E) x y, EF (a • x) y = EF x (H.bar a • y) := fun a x y => by
    apply Int.cast_injective (α := ℚ)
    rw [hEF, hEF, Submodule.coe_smul, Submodule.coe_smul, Algebra.smul_def, Algebra.smul_def,
      map_mul (IsCMField.complexConj E),
      ← RingOfIntegers.coe_eq_algebraMap, ← RingOfIntegers.coe_eq_algebraMap, H.bar_eq,
      IsCMField.complexConj_apply_apply]
    congr 1
    ring
  obtain ⟨D, e, hp, hq, he⟩ := PeriodDatum.exists_datum E H 𝔄 EF 1 0 g ty P Hm hty hbij hadj hlin hinj hdisc
    hspan hH hpos him
  exact ⟨D, e, hp, hq, fun x y => by rw [he, hEF]⟩

end GlobalTheory.CM.SelfDualDatum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsIsExpPush
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem isHolTo_comp_hom {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X Y : Scheme.{0}} {B : Set V}
    {y : V → (Sp ℂ ⟶ X)} (h : IsHolTo B y) (φ : X ⟶ Y) : IsHolTo B (fun b => y b ≫ φ) := by
  intro U s
  have hfun : (fun b => valAt' (y b ≫ φ) U s) = fun b => valAt' (y b) (φ ⁻¹ᵁ U) ((φ.app U).hom s) :=
    funext fun b => (valAt'_comp _ φ U s).symm
  rw [hfun]
  exact h (φ ⁻¹ᵁ U) _

theorem exists_isExp_push : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (σ : R →+* ℂ) (T : PAT H (Sp R)) (T' : PAT H (Sp ℂ)) (m : SABMap T'.t T.t (spMap σ)) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Pe : D.La →+ (Fin g → ℂ)) (e' : (Fin g → ℂ) → (Over.mk (spMap (RingHom.id ℂ)) ⟶ T'.t.G)), IsExp T' (RingHom.id ℂ) D ty Pe e' → ∃ e : (Fin g → ℂ) → (Over.mk (spMap σ) ⟶ T.t.G), IsExp T σ D ty Pe e ∧ ∀ z, (e z).left = (e' z).left ≫ m.φ := by
  intro E _ _ _ H R _ σ T T' m D g ty Pe e' ⟨hP, hol, hadd, hon, hker, hlin, hw⟩
  have hL : LBIso T'.t.PP.L (T.t.PP.L.pull m.cm.F) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  have hid : spMap (RingHom.id ℂ) = 𝟙 (Sp ℂ) := Spec.map_id _
  have hT : (Over.mk (spMap (RingHom.id ℂ))).hom ≫ spMap σ = spMap σ := by
    show spMap (RingHom.id ℂ) ≫ spMap σ = spMap σ
    rw [hid, Category.id_comp]
  obtain ⟨p, hp⟩ := LiePull.exists_pushEquiv m.cart (Over.mk (spMap (RingHom.id ℂ))) (spMap σ) hT.symm
  refine ⟨fun z => p (e' z), ⟨hP, ?_, fun z w => (congrArg p (hadd z w)).trans (map_mul p _ _),
    p.surjective.comp hon, fun z => ?_, fun a z => ?_, fun k a b c hk hc => ?_⟩, fun z => hp _⟩
  · have h : (fun z => (p (e' z)).left) = fun z => (e' z).left ≫ m.φ := funext fun z => hp _
    exact h ▸ isHolTo_comp_hom hol m.φ
  · exact (map_eq_one_iff p p.injective).trans (hker z)
  · apply Over.OverMorphism.ext
    beta_reduce
    rw [Over.comp_left, hp, hp, hlin, Over.comp_left, Category.assoc, Category.assoc]
    exact congrArg _ (m.act a)
  · have key : ∀ (y : Sp ℂ ⟶ Sp R) (_ : y = (Over.mk (spMap (RingHom.id ℂ))).hom ≫ spMap σ)
        (x₀ y₀ : Over.mk y ⟶ T.t.G) (x x' : Over.mk (spMap (RingHom.id ℂ)) ⟶ T'.t.G),
        x₀.left = x.left ≫ m.φ → y₀.left = x'.left ≫ m.φ →
        Out.WeilIs T'.t.G T'.t.PP.L k x x' (unitOn c) → Out.WeilIs T.t.G T.t.PP.L k x₀ y₀ (unitOn c) := by
      rintro y rfl x₀ y₀ x x' h₁ h₂ h₃
      exact (weilIs_grpPullback_of_comm _ _ _ _ _ m.φ _ _ T.t.PP.isLB T'.t.PP.isLB m.cart hL _ k x x' x₀ y₀ _
        h₁ h₂).1 h₃
    exact key _ hT.symm _ _ _ _ (hp _) (hp _) (hw k a b c hk hc)

end GlobalTheory.CM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TensorPairingIdentityOfPureTensors
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TensorPairingIdentityOfPureTensors
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.LamCalc

theorem isTensor_induction {S : Scheme.{0}} {O : Type} [CommRing O] {G A T : Over S} [GrpObj G] [IsCommMonObj G]
    [GrpObj A] [IsCommMonObj A] {a : OAct O G} {b : OAct O A} {M : Type} [AddCommGroup M] [Module O M]
    (t : Serre.IsTensor A b G a M) {P : (T ⟶ A) → Prop} (y : T ⟶ A)
    (tmul : ∀ (m : M) (x : T ⟶ G), P (x ≫ t.tmul m)) (mul : ∀ y z, P y → P z → P (y * z)) : P y := by
  refine t.induction_on y ?_ tmul mul
  have h := tmul 0 1
  rwa [t.tmul_zero, MonObj.comp_one] at h

theorem lamEq_of_tmul : ∀ (S : Scheme.{0}) (O : Type) [CommRing O] (G A : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A] (a : OAct O G) (b : OAct O A) (M : Type) [AddCommGroup M] [Module O M] (t : Serre.IsTensor A b G a M) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (b' : OAct O A') (M' : Type) [AddCommGroup M'] [Module O M'] (t' : Serre.IsTensor A' b' G a M') (B B' : Over S) [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B'] (L : LB B.left) (L' : LB B'.left) (f₁ : A ⟶ B) (f₂ : A' ⟶ B) (g₁ : A ⟶ B') (g₂ : A' ⟶ B'), L.IsLB → L'.IsLB → (∃ t : LB.Gen (Theta B L), t.IsGen) → (∃ t : LB.Gen (Theta B' L'), t.IsGen) → IsMonHom f₁ → IsMonHom f₂ → IsMonHom g₁ → IsMonHom g₂ →
  (∀ m m', LamEq L (t.tmul m ≫ f₁) (t'.tmul m' ≫ f₂) L' (t.tmul m ≫ g₁) (t'.tmul m' ≫ g₂)) → LamEq L f₁ f₂ L' g₁ g₂ := by
  intro S O _ G A _ _ _ _ a b M _ _ t A' _ _ b' M' _ _ t' B B' _ _ _ _ L L' f₁ f₂ g₁ g₂ hL hL' hT hT' _ _ _ _ h
  have key : ∀ (T : Over S) (x : T ⟶ A) (y : T ⟶ A'),
      LBIso (cubeLB B ![x ≫ f₁, y ≫ f₂] L) (cubeLB B' ![x ≫ g₁, y ≫ g₂] L') := by
    intro T x y
    refine isTensor_induction t
      (P := fun x => LBIso (cubeLB B ![x ≫ f₁, y ≫ f₂] L) (cubeLB B' ![x ≫ g₁, y ≫ g₂] L')) x
      (fun m u => ?_) (fun x x' hx hx' => ?_)
    · refine isTensor_induction t'
        (P := fun y => LBIso (cubeLB B ![(u ≫ t.tmul m) ≫ f₁, y ≫ f₂] L)
          (cubeLB B' ![(u ≫ t.tmul m) ≫ g₁, y ≫ g₂] L')) y (fun m' v => ?_) (fun y y' hy hy' => ?_)
      · simp only [Category.assoc]
        exact lbIso_of_lamEq (h m m') u v
      · simp only [MonObj.mul_comp]
        exact lbIso_cubeLB_mul_right_of hL hL' hT hT' hy hy'
    · simp only [MonObj.mul_comp]
      exact lbIso_cubeLB_mul_left_of hL hL' hT hT' hx hx'
  exact key _ (fst A A') (snd A A')

end GlobalTheory.LamCalc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TensorPairingIdentityOfPureTensorsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

theorem _root_.GlobalTheory.T.tensor_pairing_identity_of_pure_tensors : ∀ (S : Scheme.{0}) (O : Type) [CommRing O] (G A : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A] (a : OAct O G) (b : OAct O A) (M : Type) [AddCommGroup M] [Module O M] (t : Serre.IsTensor A b G a M) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (b' : OAct O A') (M' : Type) [AddCommGroup M'] [Module O M'] (t' : Serre.IsTensor A' b' G a M') (B B' : Over S) [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B'] (L : LB B.left) (L' : LB B'.left) (f₁ : A ⟶ B) (f₂ : A' ⟶ B) (g₁ : A ⟶ B') (g₂ : A' ⟶ B'), L.IsLB → L'.IsLB → (∃ t : LB.Gen (Theta B L), t.IsGen) → (∃ t : LB.Gen (Theta B' L'), t.IsGen) → IsMonHom f₁ → IsMonHom f₂ → IsMonHom g₁ → IsMonHom g₂ →
  (∀ m m', LamEq L (t.tmul m ≫ f₁) (t'.tmul m' ≫ f₂) L' (t.tmul m ≫ g₁) (t'.tmul m' ≫ g₂)) → LamEq L f₁ f₂ L' g₁ g₂ := by
  first | exact @GlobalTheory.LamCalc.lamEq_of_tmul | exact GlobalTheory.LamCalc.lamEq_of_tmul | (intros; apply GlobalTheory.LamCalc.lamEq_of_tmul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieCombAddPowMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

noncomputable section

namespace GlobalTheory.LieCombHom

variable {R : Type} [CommRing R] {G G' : Over (Sp R)} [GrpObj G] [GrpObj G'] {n : ℕ}
  {v : Fin n → (epsR R ⟶ G)}

theorem isLieComb_zero [IsCommMonObj G] (hv : ∀ i, IsTangent (v i)) : IsLieComb 0 v 1 :=
  (LieComb.isLieComb_iff_tanExp _ _).2
    (congrArg Additive.toMul (map_zero (LieComb.combHom hv))).symm

theorem isLieComb_add [IsCommMonObj G] (hv : ∀ i, IsTangent (v i)) {c c' : Fin n → R}
    {w w' : epsR R ⟶ G} (h : IsLieComb c v w) (h' : IsLieComb c' v w') :
    IsLieComb (c + c') v (w * w') := by
  rw [LieComb.isLieComb_iff_tanExp] at h h' ⊢
  rw [h, h']
  exact (congrArg Additive.toMul (map_add (LieComb.combHom hv) c c')).symm

theorem isLieComb_nsmul [IsCommMonObj G] (hv : ∀ i, IsTangent (v i)) {c : Fin n → R}
    {w : epsR R ⟶ G} (h : IsLieComb c v w) (N : ℕ) : IsLieComb (N • c) v (w ^ N) := by
  induction N with
  | zero => rw [zero_smul, pow_zero]; exact isLieComb_zero hv
  | succ N ih => rw [succ_nsmul, pow_succ]; exact isLieComb_add hv ih h

theorem isTangent_comp (f : G ⟶ G') [IsMonHom f] {x : epsR R ⟶ G} (hx : IsTangent x) :
    IsTangent (x ≫ f) := by
  unfold IsTangent at hx ⊢
  rw [Over.comp_left, ← Category.assoc, hx, ← Over.comp_left, IsMonHom.one_hom]

theorem list_prod_comp (f : G ⟶ G') [IsMonHom f] (l : List (epsR R ⟶ G)) :
    l.prod ≫ f = (l.map (· ≫ f)).prod := by
  induction l with
  | nil => simpa using MonObj.one_comp f
  | cons a l ih => rw [List.prod_cons, List.map_cons, List.prod_cons, MonObj.mul_comp, ih]

theorem isLieComb_comp (f : G ⟶ G') [IsMonHom f] {c : Fin n → R} {w : epsR R ⟶ G}
    (h : IsLieComb c v w) : IsLieComb c (fun i => v i ≫ f) (w ≫ f) := by
  obtain ⟨u, hu, rfl⟩ := h
  refine ⟨fun i => u i ≫ f, fun i => ?_, ?_⟩
  · rw [Over.comp_left, Over.comp_left, hu i, Category.assoc]
  · rw [list_prod_comp, List.map_ofFn]
    rfl

theorem lieComb_add_pow_map : ∀ (R : Type) [CommRing R] (G G' : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G'] (n : ℕ) (v : Fin n → (epsR R ⟶ G)), (∀ i, IsTangent (v i)) → IsLieComb 0 v 1 ∧ (∀ c c' w w', IsLieComb c v w → IsLieComb c' v w' → IsLieComb (c + c') v (w * w')) ∧ (∀ c w (N : ℕ), IsLieComb c v w → IsLieComb (N • c) v (w ^ N)) ∧ ∀ f : G ⟶ G', IsMonHom f → (∀ i, IsTangent (v i ≫ f)) ∧ ∀ c w, IsLieComb c v w → IsLieComb c (fun i => v i ≫ f) (w ≫ f) := by
  intro R _ G G' _ _ _ n v hv
  exact ⟨isLieComb_zero hv, fun _ _ _ _ h h' => isLieComb_add hv h h',
    fun _ _ N h => isLieComb_nsmul hv h N,
    fun f _ => ⟨fun i => isTangent_comp f (hv i), fun _ _ h => isLieComb_comp f h⟩⟩

end GlobalTheory.LieCombHom
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EqOfLamEq
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EqOfLamEq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

noncomputable section

namespace GlobalTheory.CM.PairingInj

open GlobalTheory.KerPow GlobalTheory.CM.PairingIso

theorem eq_one_of_gen_cubeLB {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]
    {L : LB A.left} (hL : L.IsLB) (hK : Out.KTriv A L) {T : Over S} (x : T ⟶ A)
    (g₁ : ∃ t : LB.Gen (cubeLB A ![fst T A ≫ x, snd T A] L), t.IsGen) : x = 1 := by
  have g₂ : HasGen L _ _ := g₁
  have g₃ : LocGen L (fst T A).left
      (fun I : ULift.{0} (Finset (Fin 2)) => (psum A ![fst T A ≫ x, snd T A] I.down).left)
      (fun I => (-1) ^ (2 - I.down.card)) := fun _ => ⟨⊤, trivial, g₂.pull _ fun _ => rfl⟩
  have b₁ := locGen_base hL (fst T A).left x.left (b := (fst T A ≫ x).left) rfl
  have b₀ := locGen_base hL (fst T A).left (1 : T ⟶ A).left (b := (1 : T ⊗ A ⟶ A).left)
    (congrArg (fun q : T ⊗ A ⟶ A => q.left) (MonObj.comp_one (fst T A) : fst T A ≫ (1 : T ⟶ A) = 1).symm)
  have b := b₀.comb hL b₁ (φ'' := ![(1 : T ⊗ A ⟶ A).left, (fst T A ≫ x).left]) (ε'' := ![1, -1])
    fun U _ k => by simp [Fin.prod_univ_two]
  refine eq_one_of_locGen hK x (g₃.comb hL b fun U _ k => ?_)
  rw [PrimNorm.prod_square_id, Fin.prod_univ_two, Fin.prod_univ_two]
  show k ((fst T A ≫ x) * snd T A).left * (k (fst T A ≫ x).left)⁻¹ * (k (snd T A).left)⁻¹ * k (1 : T ⊗ A ⟶ A).left *
    (k (1 : T ⊗ A ⟶ A).left ^ (1 : ℤ) * k (fst T A ≫ x).left ^ (-1 : ℤ))⁻¹ =
    k ((fst T A ≫ x) * snd T A).left ^ (1 : ℤ) * k (snd T A).left ^ (-1 : ℤ)
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  module

theorem eq_of_lamEq : Out.Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : Out.PolAV S) (X : Over S) (f g : X ⟶ P.A), LamEq P.L f (𝟙 P.A) P.L g (𝟙 P.A) → f = g := by
  intro hL S _ P X f g h
  have := P.isAb.comm
  obtain ⟨ρ, hρ⟩ := P.rigid
  obtain ⟨⟨c⟩, -⟩ := hL.cube S P ⟨P.L, ρ, P.isLB, hρ⟩ rfl
  have hT : ∃ t : LB.Gen (Theta P.A P.L), t.IsGen := ⟨c.t, c.isGen⟩
  have C := LamCalc.lamEq_calculus S X P.A P.A P.A P.A P.L P.L P.L P.isLB P.isLB P.isLB
  have h₁ : LamEq P.L (f * g⁻¹) (𝟙 P.A) P.L (g * g⁻¹) (𝟙 P.A) :=
    ((C f g⁻¹ (𝟙 _) (𝟙 _) g g⁻¹ (𝟙 _) (𝟙 _) g (𝟙 _)).2.2.1 hT hT h).1
      (C g⁻¹ g (𝟙 _) (𝟙 _) g g (𝟙 _) (𝟙 _) g (𝟙 _)).1
  rw [mul_inv_cancel] at h₁
  have h₂ := LamCalc.lbIso_of_lamEq h₁ (fst X P.A) (snd X P.A)
  rw [Category.comp_id, MonObj.comp_one] at h₂
  refine mul_inv_eq_one.1 (eq_one_of_gen_cubeLB P.isLB P.ktriv _ (exists_gen_of_lbIso
    (LamCalc.cubeLB_isLB P.isLB _) (LamCalc.cubeLB_isLB P.isLB _) h₂.symm ?_))
  exact hasGen_of_trivial P.isLB fun U _ k => (PrimNorm.prod_square_id _ _ k).trans (by simp [PrimNorm.diff₂])

end GlobalTheory.CM.PairingInj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EqOfLamEqStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_lamEq_polAV : Out.Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : Out.PolAV S) (X : Over S) (f g : X ⟶ P.A), LamEq P.L f (𝟙 P.A) P.L g (𝟙 P.A) → f = g := by
  first | exact @GlobalTheory.CM.PairingInj.eq_of_lamEq | exact GlobalTheory.CM.PairingInj.eq_of_lamEq | (intros; apply GlobalTheory.CM.PairingInj.eq_of_lamEq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RingOfIntegersActionInjectiveOnAbelianScheme
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RingOfIntegersActionInjectiveOnAbelianScheme
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF.Faithful

section
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {O : Type} [CommRing O]

theorem act_zero (act : OAct O G) : act.act 0 = 1 := by
  have h := act.add 0 0
  rw [add_zero] at h
  exact mul_left_cancel (a := act.act 0) (by rw [← h, _root_.mul_one])

theorem act_natCast (act : OAct O G) (n : ℕ) : act.act (n : O) = 𝟙 G ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, act_zero, pow_zero]
  | succ n ih => rw [Nat.cast_succ, act.add, ih, act.one, pow_succ]

theorem act_mul_eq_one (act : OAct O G) {c : O} (hc : act.act c = 1) (d : O) : act.act (d * c) = 1 := by
  rw [act.mul, hc, MonObj.comp_one]

theorem pow_eq_one_of_act (act : OAct O G) {n : ℕ} (hn : act.act (n : O) = 1) {T : Over S} (x : T ⟶ G) :
    x ^ n = 1 := by
  have h : x ≫ (𝟙 G ^ n) = x ^ n := by rw [MonObj.comp_pow, Category.comp_id]
  rw [← h, ← act_natCast act, hn, MonObj.comp_one]

end

theorem act_injective : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (act : OAct (𝓞 E) P.A), 1 ≤ P.g → Function.Injective act.act := by
  intro hL E _ _ K _ _ P act hg a b hab
  by_contra hne
  have hc0 : a - b ≠ 0 := sub_ne_zero.mpr hne
  have hc : act.act (a - b) = 1 := by
    have h := act.add (a - b) b
    rw [sub_add_cancel, hab] at h
    exact mul_right_cancel (b := act.act b) (by rw [← h, _root_.one_mul])
  set n : ℕ := Ideal.absNorm (Ideal.span {a - b}) with hn
  have hn0 : n ≠ 0 := by
    rw [hn, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hc0
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {a - b}))
  have h1 : act.act (n : 𝓞 E) = 1 := by
    rw [hn, ← hd]; exact act_mul_eq_one act hc d
  let k := AlgebraicClosure K
  let t : Spec (CommRingCat.of k) ⟶ Sp (𝓞 K) :=
    Spec.map (CommRingCat.ofHom ((algebraMap K k).comp (algebraMap (𝓞 K) K)))
  haveI : CharZero k := charZero_of_injective_algebraMap (algebraMap K k).injective
  have key : ∀ m : ℕ, 1 ≤ m → Nat.card (Over.mk t ⟶ P.A) = (n * m) ^ (2 * P.g) := by
    intro m hm
    have hnm : n * m ≠ 0 := Nat.mul_ne_zero hn0 (by omega)
    obtain ⟨-, -, -, -, h⟩ := hL.mulN _ P (n * m) (Nat.one_le_iff_ne_zero.mpr hnm)
    rw [← h k t (Nat.cast_ne_zero.mpr hnm)]
    refine (Nat.card_congr (Equiv.subtypeUnivEquiv fun x => ?_)).symm
    rw [pow_mul, pow_eq_one_of_act act h1, one_pow]
  have e := (key 1 le_rfl).symm.trans (key 2 (by norm_num))
  have := Nat.pow_left_injective (by omega : 2 * P.g ≠ 0) e
  omega

end GlobalTheory.LamF.Faithful
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RingOfIntegersActionInjectiveOnAbelianSchemeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringOfIntegersAction_injective_on_abelianScheme : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (act : OAct (𝓞 E) P.A), 1 ≤ P.g → Function.Injective act.act := by
  first | exact @GlobalTheory.LamF.Faithful.act_injective | exact GlobalTheory.LamF.Faithful.act_injective | (intros; apply GlobalTheory.LamF.Faithful.act_injective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsNumberFieldTorsionPoints
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.TorsionField

theorem exists_field_alg (k : IntermediateField ℚ ℂ) [FiniteDimensional ℚ k] (B : Type) [CommRing B] [Algebra k B]
    [Module.Finite k B] : ∃ k₁ : IntermediateField ℚ ℂ, FiniteDimensional ℚ k₁ ∧ k ≤ k₁ ∧
      ∀ (φ : B →ₐ[k] ℂ) (b : B), φ b ∈ k₁ := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := k) (M := B)
  let S : Set ℂ := ⋃ b ∈ s, (minpoly k b).rootSet ℂ
  have hS : S.Finite := s.finite_toSet.biUnion fun b _ => Polynomial.rootSet_finite _ _
  have hint : ∀ b : B, _root_.IsIntegral k b := fun b => Algebra.IsIntegral.isIntegral b
  have hI : ∀ x ∈ S, _root_.IsIntegral k x := fun x hx => by
    simp only [S, Set.mem_iUnion] at hx
    obtain ⟨b, -, hb⟩ := hx
    exact ⟨minpoly k b, minpoly.monic (hint b), (Polynomial.mem_rootSet.1 hb).2⟩
  have : Finite S := hS
  have hfd : FiniteDimensional k (IntermediateField.adjoin k S) := IntermediateField.finiteDimensional_adjoin hI
  have hfd' : FiniteDimensional ℚ (IntermediateField.adjoin k S) := Module.Finite.trans k _
  refine ⟨(IntermediateField.adjoin k S).restrictScalars ℚ, hfd', fun x hx => ?_, fun φ b => ?_⟩
  · exact (IntermediateField.adjoin k S).algebraMap_mem ⟨x, hx⟩
  · change φ b ∈ IntermediateField.adjoin k S
    have hb : b ∈ Submodule.span k (s : Set B) := hs ▸ Submodule.mem_top
    induction hb using Submodule.span_induction with
    | mem b hb =>
      refine IntermediateField.subset_adjoin _ _ ?_
      simp only [S, Set.mem_iUnion]
      refine ⟨b, hb, Polynomial.mem_rootSet.2 ⟨minpoly.ne_zero (hint b), ?_⟩⟩
      rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
    | zero => rw [map_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul c a _ ha => rw [map_smul]; exact IntermediateField.smul_mem _ ha

theorem exists_field_finite (k : IntermediateField ℚ ℂ) [FiniteDimensional ℚ k] (Z : Over (Sp k)) [IsFinite Z.hom] :
    ∃ k₁ : IntermediateField ℚ ℂ, FiniteDimensional ℚ k₁ ∧ k ≤ k₁ ∧
      ∀ (k₂ : IntermediateField ℚ ℂ) (h₂ : k ≤ k₂), k₁ ≤ k₂ → ∀ y : Over.mk (spMap (algebraMap k ℂ)) ⟶ Z,
        ∃ y₂ : Over.mk (spMap (IntermediateField.inclusion h₂).toRingHom) ⟶ Z,
          spMap (algebraMap k₂ ℂ) ≫ y₂.left = y.left := by
  have : IsAffine Z.left := isAffine_of_isAffineHom Z.hom
  let φ : CommRingCat.of k ⟶ Γ(Z.left, ⊤) := Spec.preimage (Z.left.isoSpec.inv ≫ Z.hom)
  have hφ : Spec.map φ = Z.left.isoSpec.inv ≫ Z.hom := Spec.map_preimage _
  have h₁ : φ.hom.Finite := by rw [← IsFinite.SpecMap_iff, hφ]; infer_instance
  let := φ.hom.toAlgebra
  have : Module.Finite k Γ(Z.left, ⊤) := h₁
  obtain ⟨k₁, hfd, hk, H⟩ := exists_field_alg k Γ(Z.left, ⊤)
  refine ⟨k₁, hfd, hk, fun k₂ h₂ h₁₂ y => ?_⟩
  let y' : Sp ℂ ⟶ Z.left := y.left
  have hy : y' ≫ Z.hom = spMap (algebraMap k ℂ) := Over.w y
  let ψ : Γ(Z.left, ⊤) ⟶ CommRingCat.of ℂ := Spec.preimage (y' ≫ Z.left.isoSpec.hom)
  have hψ : Spec.map ψ = y' ≫ Z.left.isoSpec.hom := Spec.map_preimage _
  have hc : φ ≫ ψ = CommRingCat.ofHom (algebraMap k ℂ) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, hψ, Category.assoc, Iso.hom_inv_id_assoc, hy]
  have hc' : ∀ c : k, ψ.hom (φ.hom c) = (c : ℂ) := fun c => congrArg (fun f => f.hom c) hc
  let ψa : Γ(Z.left, ⊤) →ₐ[k] ℂ := { ψ.hom with commutes' := hc' }
  let ψ₂ : Γ(Z.left, ⊤) →+* k₂ := ψ.hom.codRestrict k₂ fun b => h₁₂ (H ψa b)
  refine ⟨Over.homMk (spMap ψ₂ ≫ Z.left.isoSpec.inv) ?_, ?_⟩
  · change (Spec.map (CommRingCat.ofHom ψ₂) ≫ Z.left.isoSpec.inv) ≫ Z.hom =
      Spec.map (CommRingCat.ofHom (IntermediateField.inclusion h₂).toRingHom)
    rw [Category.assoc, ← hφ, ← Spec.map_comp]
    congr 1
    ext c
    exact hc' c
  · change Spec.map (CommRingCat.ofHom (algebraMap k₂ ℂ)) ≫ Spec.map (CommRingCat.ofHom ψ₂) ≫ Z.left.isoSpec.inv = y'
    rw [← Category.assoc, ← Spec.map_comp, Iso.comp_inv_eq, ← hψ]
    rfl

end GlobalTheory.TorsionField

namespace GlobalTheory

theorem exists_numberField_torsion_points : Out.Laws → ∀ (k : IntermediateField ℚ ℂ) [FiniteDimensional ℚ k] (P : Out.PolAV (Sp k)) (n : ℕ), 0 < n → ∃ k₁ : IntermediateField ℚ ℂ, FiniteDimensional ℚ k₁ ∧ k ≤ k₁ ∧ ∀ (k₂ : IntermediateField ℚ ℂ) (h₂ : k ≤ k₂), k₁ ≤ k₂ → ∀ x : Over.mk (spMap (algebraMap k ℂ)) ⟶ P.A, x ^ n = 1 → ∃! x₂ : Over.mk (spMap (IntermediateField.inclusion h₂).toRingHom) ⟶ P.A, spMap (algebraMap k₂ ℂ) ≫ x₂.left = x.left := by
  intro _ k _ P n hn
  have hu : IsUnit (n : Γ(Sp k, ⊤)) := by
    have h : IsUnit (n : k) := (Nat.cast_ne_zero.2 hn.ne').isUnit
    simpa using h.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
  obtain ⟨-, hfin, -⟩ := GrpTangent.finiteEtale_mulN_torsion P.A (hG := P.isAb) hu
  obtain ⟨k₁, hfd, hk, H⟩ := TorsionField.exists_field_finite k (torsion P.A n)
  refine ⟨k₁, hfd, hk, fun k₂ h₂ h₁₂ x hx => ?_⟩
  obtain ⟨y, hy, -⟩ := LatticeTorsion.existsUnique_torsion P.A n x hx
  obtain ⟨y₂, hy₂⟩ := H k₂ h₂ h₁₂ y
  have : Flat (spMap (algebraMap k₂ ℂ)) := inferInstance
  have : Surjective (spMap (algebraMap k₂ ℂ)) := ⟨fun y => ⟨default, Subsingleton.elim _ _⟩⟩
  have : Epi (spMap (algebraMap k₂ ℂ)) := Flat.epi_of_flat_of_surjective _
  refine existsUnique_of_exists_of_unique ⟨y₂ ≫ torsion.ι P.A n, ?_⟩ fun a b ha hb => ?_
  · rw [← hy, Over.comp_left, Over.comp_left, ← hy₂]
    exact (Category.assoc _ _ _).symm
  · exact Over.OverMorphism.ext ((cancel_epi (spMap (algebraMap k₂ ℂ))).1 (ha.trans hb.symm))

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsTateIsoZetaEq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.TateRoot

private lemma isCoprime_add_sub_mul_pow_factorial {j N : ℤ} (hj : IsCoprime j N) {n : ℕ} (hn : 0 < n) :
    IsCoprime (j + (1 - j) * N ^ n.factorial) n := by
  rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_eq_natAbs, Int.natAbs_natCast]
  apply Nat.coprime_of_dvd
  intro p hp hpν hpn
  haveI := Fact.mk hp
  have hν : ((j + (1 - j) * N ^ n.factorial : ℤ) : ZMod p) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact Int.natCast_dvd.mpr hpν
  have hpn' : p ≤ n := Nat.le_of_dvd hn hpn
  by_cases hN : (N : ZMod p) = 0
  · have hfac : n.factorial ≠ 0 := Nat.factorial_ne_zero n
    push_cast at hν
    rw [hN, zero_pow hfac, mul_zero, add_zero, ZMod.intCast_zmod_eq_zero_iff_dvd] at hν
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hN
    have hu := hj.isUnit_of_dvd' hν hN
    rw [Int.isUnit_iff] at hu
    have := hp.two_le
    omega
  · have hdvd : p - 1 ∣ n.factorial :=
      Nat.dvd_factorial (by have := hp.two_le; omega) (by omega)
    obtain ⟨s, hs⟩ := hdvd
    push_cast at hν
    rw [hs, pow_mul, ZMod.pow_card_sub_one_eq_one hN, one_pow] at hν
    simp at hν

private lemma zmod_pow_eq_pow_factorial_of_dvd {n : ℕ} (hn : 0 < n) (x : ZMod n) {c : ℕ}
    (hc : n.factorial ∣ c) (hc0 : 0 < c) : x ^ c = x ^ n.factorial := by
  haveI : NeZero n := ⟨hn.ne'⟩
  have key : ∀ a t : ℕ, a ≤ n → 0 < t → t ≤ n → x ^ (a + t) = x ^ a → x ^ c = x ^ n.factorial := by
    intro a t ha ht htn h
    have hstep : ∀ k, a ≤ k → x ^ (k + t) = x ^ k := by
      intro k hk
      have e1 : k + t = (k - a) + (a + t) := by omega
      have e2 : k = (k - a) + a := by omega
      rw [e1, pow_add, h, ← pow_add, ← e2]
    have hper : ∀ k s, a ≤ k → x ^ (k + t * s) = x ^ k := by
      intro k s hk
      induction s with
      | zero => simp
      | succ s ih =>
        rw [show k + t * (s + 1) = (k + t * s) + t by ring, hstep _ (by omega), ih]
    have hfac : n.factorial ≤ c := Nat.le_of_dvd hc0 hc
    have htd : t ∣ c - n.factorial :=
      Nat.dvd_sub ((Nat.dvd_factorial ht htn).trans hc) (Nat.dvd_factorial ht htn)
    obtain ⟨s, hs⟩ := htd
    have : c = n.factorial + t * s := by omega
    rw [this, hper _ _ (le_trans ha (Nat.self_le_factorial n))]
  obtain ⟨a, b, hab, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt (fun i : Fin (n + 1) => x ^ (i : ℕ))
    (by simp [ZMod.card])
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with h | h
  · exact key a (b - a) (by omega) (by omega) (by omega)
      (by rw [show (a : ℕ) + (b - a) = b by omega]; exact heq.symm)
  · exact key b (a - b) (by omega) (by omega) (by omega)
      (by rw [show (b : ℕ) + (a - b) = a by omega]; exact heq)

theorem _root_.GlobalTheory.TateRoot.exists_tateIso_zeta_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (k : Type) [Field k] (Q : Type) [Group Q]
    (act : 𝓞 E → Q → Q) (e : ℕ → Q → Q → kˣ → Prop) (_ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.TateIso D k Q act e) (N : ℕ) (z : k),
    0 < N → IsPrimitiveRoot z N → ∃ I' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.TateIso D k Q act e, (I'.ζ N : k) = z := by
  intro E _ _ _ H D l k _ Q _ act e I N z hN hz
  have hζ : IsPrimitiveRoot ((I.ζ N : kˣ) : k) N := IsPrimitiveRoot.coe_units_iff.mpr (I.ζ_prim N hN)
  haveI : NeZero N := ⟨hN.ne'⟩
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hz.pow_eq_one
  have hcop : IsCoprime (i : ℤ) N := by
    rw [Nat.isCoprime_iff_coprime]
    rw [← hζ.pow_iff_coprime hN, hi]
    exact hz
  suffices h : ∃ g : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sim D, ∃ hν : (∀ (n m : ℕ), 0 < n → 0 < m → (n : ℤ) ∣ g.ν (n * m) - g.ν n ∧
      IsCoprime (g.ν n) n), (N : ℤ) ∣ g.ν N - i by
    obtain ⟨g, hν, hg⟩ := h
    refine ⟨_root_.GlobalTheory.LevelTwist.twist I g hν, ?_⟩
    rw [_root_.GlobalTheory.LevelTwist.twist_ζ, _root_.GlobalTheory.LevelTwist.zeta_zpow_congr I hN hg, zpow_natCast, Units.val_pow_eq_pow_val, hi]
  rcases Nat.eq_zero_or_pos (D.p + D.q) with hpq | hpq
  · haveI := D.proj
    haveI := D.fin
    have hsub : Subsingleton D.La := Module.finrank_zero_iff.mp (by rw [D.rank]; exact hpq)
    let g : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sim D :=
      { f := fun _ => LinearMap.id
        ν := fun n => i + (1 - i) * (N : ℤ) ^ n.factorial
        tower := fun n m _ _ a => ⟨0, by simp⟩
        inv := fun n _ => ⟨LinearMap.id, fun a => ⟨⟨0, Subsingleton.elim _ _⟩, ⟨0, Subsingleton.elim _ _⟩⟩⟩
        mult := fun n _ a b => by rw [Subsingleton.elim a 0]; simp }
    refine ⟨g, fun n m hn hm => ⟨?_, isCoprime_add_sub_mul_pow_factorial hcop hn⟩, ?_⟩
    · have h := zmod_pow_eq_pow_factorial_of_dvd hn (N : ZMod n)
        (Nat.factorial_dvd_factorial (Nat.le_mul_of_pos_right n hm)) (Nat.factorial_pos _)
      have h' : (((N : ℤ) ^ n.factorial : ℤ) : ZMod n) =
          (((N : ℤ) ^ (n * m).factorial : ℤ) : ZMod n) := by
        push_cast
        exact h.symm
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h'
      show (n : ℤ) ∣ (i + (1 - i) * (N : ℤ) ^ (n * m).factorial) - (i + (1 - i) * (N : ℤ) ^ n.factorial)
      rw [show (i + (1 - i) * (N : ℤ) ^ (n * m).factorial) - (i + (1 - i) * (N : ℤ) ^ n.factorial) =
        (1 - i) * ((N : ℤ) ^ (n * m).factorial - (N : ℤ) ^ n.factorial) by ring]
      exact Dvd.dvd.mul_left h' _
    · show (N : ℤ) ∣ (i + (1 - i) * (N : ℤ) ^ N.factorial) - i
      rw [add_sub_cancel_left]
      exact Dvd.dvd.mul_left (dvd_pow_self _ (Nat.factorial_ne_zero N)) _
  · have hgrp := _root_.GlobalTheory.SimAlg.sim_group
    obtain ⟨g, hg, -⟩ := _root_.GlobalTheory.SimMult.exists_sim_trivial_of_mult hgrp _root_.GlobalTheory.exists_sim_lift
      E H D { l with A := 1, A_pos := Nat.one_pos } N i hN hcop (by simp)
    exact ⟨g, (hgrp E H D hpq).1 g, hg⟩

end GlobalTheory.TateRoot
end
