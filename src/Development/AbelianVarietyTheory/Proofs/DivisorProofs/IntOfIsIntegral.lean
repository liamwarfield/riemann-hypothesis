module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveLiftSemiSecPull
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKernelDiagonalRestrictionOfSymmetricTrivial

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntOfIsIntegral
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal UpperHalfPlane ReciprocityTheory.ChartRestriction.L1
open scoped UpperHalfPlane

namespace GlobalTheory.QuadGenerator

theorem int_of_isIntegral {r : ℚ} (h : IsIntegral ℤ (r : ℂ)) : ∃ n : ℤ, (n : ℚ) = r := by
  have h' : IsIntegral ℤ (algebraMap ℚ ℂ r) := h
  exact IsIntegrallyClosed.isIntegral_iff.1 ((isIntegral_algebraMap_iff ).1 h')

theorem isIntegral_int (n : ℤ) : IsIntegral ℤ (n : ℂ) := isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := n)

theorem sq_root (d : ℕ) : (Complex.I * (Real.sqrt d : ℝ)) ^ 2 = -(d : ℂ) := by
  rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
  simp

theorem half_coords {d : ℕ} (hd : d.Prime) {a b : ℚ}
    (hx : IsIntegral ℤ ((a : ℂ) + (b : ℂ) * (Complex.I * (Real.sqrt d : ℝ)))) :
    ∃ t k n : ℤ, (t : ℚ) = 2 * a ∧ (k : ℚ) = 2 * b ∧ t ^ 2 + d * k ^ 2 = 4 * n := by
  have hw2 := sq_root d
  set w : ℂ := Complex.I * (Real.sqrt d : ℝ) with hw
  have hwc : starRingEnd ℂ w = -w := by simp [hw]
  have hx' : IsIntegral ℤ ((a : ℂ) - (b : ℂ) * w) := by
    have := hx.map_of_comp_eq (RingHom.id ℤ) (starRingEnd ℂ) (RingHom.ext_int _ _)
    simpa [hwc, sub_eq_add_neg] using this
  obtain ⟨t, ht⟩ := int_of_isIntegral (r := 2 * a) (by
    refine (congrArg (IsIntegral ℤ) ?_).mpr (hx.add hx')
    push_cast; ring)
  obtain ⟨n, hn⟩ := int_of_isIntegral (r := a ^ 2 + d * b ^ 2) (by
    refine (congrArg (IsIntegral ℤ) ?_).mpr (hx.mul hx')
    push_cast
    linear_combination (b : ℂ) ^ 2 * hw2)
  have hm2 : ((d : ℚ) * (2 * b)) ^ 2 = ((d * (4 * n - t ^ 2) : ℤ) : ℚ) := by
    push_cast
    rw [hn, ht]; ring
  obtain ⟨m, hm⟩ := int_of_isIntegral (r := d * (2 * b)) (IsIntegral.of_pow two_pos (by
    rw [← Rat.cast_pow, hm2, Rat.cast_intCast]
    exact isIntegral_int _))
  have hm3 : m ^ 2 = d * (4 * n - t ^ 2) := by
    have : ((m ^ 2 : ℤ) : ℚ) = ((d * (4 * n - t ^ 2) : ℤ) : ℚ) := by
      rw [← hm2, ← hm]; push_cast; ring
    exact_mod_cast this
  obtain ⟨k, hk⟩ : (d : ℤ) ∣ m := (Nat.prime_iff_prime_int.1 hd).dvd_of_dvd_pow (n := 2) ⟨_, hm3⟩
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne_zero
  have hkb : (k : ℚ) = 2 * b := by
    apply mul_left_cancel₀ hd0
    rw [← hm, hk]; push_cast; ring
  refine ⟨t, k, n, ht, hkb, ?_⟩
  have : ((t ^ 2 + d * k ^ 2 : ℤ) : ℚ) = ((4 * n : ℤ) : ℚ) := by
    push_cast
    rw [ht, hkb, hn]; ring
  exact_mod_cast this

theorem even_of_one {d : ℕ} (h4 : d % 4 = 1) {t k n : ℤ} (h : t ^ 2 + d * k ^ 2 = 4 * n) : 2 ∣ t ∧ 2 ∣ k := by
  obtain ⟨c, rfl⟩ : ∃ c, d = 4 * c + 1 := ⟨d / 4, by omega⟩
  push_cast at h
  rcases Int.even_or_odd' t with ⟨p, rfl | rfl⟩ <;> rcases Int.even_or_odd' k with ⟨q, rfl | rfl⟩
  · exact ⟨⟨p, rfl⟩, ⟨q, rfl⟩⟩
  · have : 4 * (n - p ^ 2 - c * (2 * q + 1) ^ 2 - q ^ 2 - q) = 1 := by linear_combination -h
    omega
  · have : 4 * (n - p ^ 2 - p - c * (2 * q) ^ 2 - q ^ 2) = 1 := by linear_combination -h
    omega
  · have : 4 * (n - p ^ 2 - p - c * (2 * q + 1) ^ 2 - q ^ 2 - q) = 2 := by linear_combination -h
    omega

theorem even_of_three {d : ℕ} (h4 : d % 4 = 3) {t k n : ℤ} (h : t ^ 2 + d * k ^ 2 = 4 * n) : 2 ∣ t + k := by
  obtain ⟨c, rfl⟩ : ∃ c, d = 4 * c + 3 := ⟨d / 4, by omega⟩
  push_cast at h
  rcases Int.even_or_odd' t with ⟨p, rfl | rfl⟩ <;> rcases Int.even_or_odd' k with ⟨q, rfl | rfl⟩
  · exact ⟨p + q, by ring⟩
  · have : 4 * (n - p ^ 2 - c * (2 * q + 1) ^ 2 - 3 * q ^ 2 - 3 * q) = 3 := by linear_combination -h
    omega
  · have : 4 * (n - p ^ 2 - p - c * (2 * q) ^ 2 - 3 * q ^ 2) = 1 := by linear_combination -h
    omega
  · exact ⟨p + q + 1, by ring⟩

theorem integers_one {d : ℕ} (hd : d.Prime) (h4 : d % 4 = 1) (x : ℂ) :
    (IsIntegral ℤ x ∧ ∃ a b : ℚ, x = (a : ℂ) + (b : ℂ) * (Complex.I * (Real.sqrt d : ℝ))) ↔
      ∃ u v : ℤ, x = 1 * (u * (Complex.I * (Real.sqrt d : ℝ)) + v) := by
  constructor
  · rintro ⟨hx, a, b, rfl⟩
    obtain ⟨t, k, n, ht, hk, h⟩ := half_coords hd hx
    obtain ⟨⟨p, rfl⟩, ⟨q, rfl⟩⟩ := even_of_one h4 h
    have ha : a = p := by push_cast at ht; linarith
    have hb : b = q := by push_cast at hk; linarith
    exact ⟨q, p, by rw [ha, hb]; push_cast; ring⟩
  · rintro ⟨u, v, rfl⟩
    have hw : IsIntegral ℤ (Complex.I * (Real.sqrt d : ℝ)) := by
      refine IsIntegral.of_pow two_pos ?_
      rw [sq_root]
      simpa using isIntegral_int (-(d : ℤ))
    refine ⟨?_, v, u, by push_cast; ring⟩
    rw [one_mul]
    exact ((isIntegral_int u).mul hw).add (isIntegral_int v)

theorem integers_three {d : ℕ} (hd : d.Prime) (h4 : d % 4 = 3) (x : ℂ) :
    (IsIntegral ℤ x ∧ ∃ a b : ℚ, x = (a : ℂ) + (b : ℂ) * (Complex.I * (Real.sqrt d : ℝ))) ↔
      ∃ u v : ℤ, x = 1 * (u * ((-1 + Complex.I * (Real.sqrt d : ℝ)) / 2) + v) := by
  constructor
  · rintro ⟨hx, a, b, rfl⟩
    obtain ⟨t, k, n, ht, hk, h⟩ := half_coords hd hx
    obtain ⟨j, hj⟩ := even_of_three h4 h
    have hj' : (t : ℚ) + k = 2 * j := by exact_mod_cast hj
    have ha : a = j - k / 2 := by linarith
    have hb : b = k / 2 := by linarith
    exact ⟨k, j, by rw [ha, hb]; push_cast; ring⟩
  · rintro ⟨u, v, rfl⟩
    have hw2 := sq_root d
    obtain ⟨c, hc⟩ : ∃ c : ℕ, d + 1 = 4 * c := ⟨(d + 1) / 4, by omega⟩
    have hcC : (d : ℂ) + 1 = 4 * c := by exact_mod_cast hc
    have hw : IsIntegral ℤ ((-1 + Complex.I * (Real.sqrt d : ℝ)) / 2) := by
      refine ⟨Polynomial.X ^ 2 + Polynomial.X + Polynomial.C (c : ℤ), by monicity!, ?_⟩
      rw [Polynomial.eval₂_add, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_X, Polynomial.eval₂_C,
        algebraMap_int_eq, eq_intCast, Int.cast_natCast]
      linear_combination (1 / 4 : ℂ) * hw2 - (1 / 4 : ℂ) * hcC
    refine ⟨?_, v - u / 2, u / 2, by push_cast; ring⟩
    rw [one_mul]
    exact ((isIntegral_int u).mul hw).add (isIntegral_int v)

theorem exists_generator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (d : ℕ) (φ : I → E →+* ℂ) (Λ : PeriodPair), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice d Λ → ∃ (w θ : E) (τ : ℍ), w ^ 2 = -(d : E) ∧ (∀ i, φ i w = Complex.I * (Real.sqrt d : ℝ)) ∧ θ = (if d % 4 = 3 then (-1 + w) / 2 else w) ∧ (∀ i, φ i θ = (τ : ℂ)) ∧ IsTauOf Λ 1 τ ∧ ((d % 4 = 3 ∧ τ.im = Real.sqrt d / 2) ∨ (d % 4 = 1 ∧ τ.im = Real.sqrt d)) := by
  intro E _ _ _ I _ d φ Λ hF hΛ
  obtain ⟨hd, h4, -, -, -, -, -, w, hw, hφ⟩ := hF
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd.pos)
  have hodd : d % 2 = 1 := hd.eq_two_or_odd.resolve_left (by omega)
  by_cases h3 : d % 4 = 3
  · have him : ((-1 + Complex.I * (Real.sqrt d : ℝ)) / 2 : ℂ).im = Real.sqrt d / 2 := by simp
    refine ⟨w, (-1 + w) / 2, ⟨(-1 + Complex.I * (Real.sqrt d : ℝ)) / 2, by rw [him]; positivity⟩, hw, hφ,
      by rw [if_pos h3], fun i => ?_, ⟨one_ne_zero, fun x => (hΛ x).trans (integers_three hd h3 x)⟩, Or.inl ⟨h3, him⟩⟩
    rw [map_div₀, map_add (f := _), map_neg, map_one, map_ofNat, hφ]
  · have h1 : d % 4 = 1 := by omega
    have him : (Complex.I * (Real.sqrt d : ℝ) : ℂ).im = Real.sqrt d := by simp
    exact ⟨w, w, ⟨Complex.I * (Real.sqrt d : ℝ), by rw [him]; exact hs⟩, hw, hφ,
      by rw [if_neg h3], hφ, ⟨one_ne_zero, fun x => (hΛ x).trans (integers_one hd h1 x)⟩, Or.inr ⟨h1, him⟩⟩

end GlobalTheory.QuadGenerator
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictFiniteAffineCoverInfClosedPull2Bijective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictFiniteAffineCoverInfClosedPull2Bijective
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCohCover

theorem adj_pull2_bijective {R : Type} [CommRing R] {C C' : Type} [Category.{0} C] [Category.{0} C']
    (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C) (H : C ⥤ C') (adj : G ⊣ H) :
    Function.Bijective (CoefMap.restrict F G).pull2 := by
  have hl : ∀ c, (GlobalTheory.AdjHyp.counitCoef F adj).pull2 ((CoefMap.restrict F G).pull2 c) = c := by
    intro c
    rw [← CoefMap.pullCohomologyTwo_comp]
    exact (CoefMap.pullCohomologyTwo_eq_of_natTrans _ (CoefMap.id F) adj.counit (fun T b ↦ rfl) c).trans
      (CoefMap.pullCohomologyTwo_id c)
  have hr : ∀ c, (CoefMap.restrict F G).pull2 ((GlobalTheory.AdjHyp.counitCoef F adj).pull2 c) = c := by
    intro c
    rw [← CoefMap.pullCohomologyTwo_comp]
    refine ((CoefMap.pullCohomologyTwo_eq_of_natTrans (CoefMap.id (G ⋙ F))
      ((GlobalTheory.AdjHyp.counitCoef F adj).comp (CoefMap.restrict F G)) adj.unit (fun T b ↦ ?_) c).symm.trans
      (CoefMap.pullCohomologyTwo_id c))
    change mp F (adj.counit.app (G.obj T)) (mp F (G.map (adj.unit.app T)) b) = b
    exact (mp_comp F (G.map (adj.unit.app T)) (adj.counit.app (G.obj T)) b).symm.trans
      ((congrArg (fun ξ ↦ mp F ξ b) (adj.left_triangle_components T)).trans (mp_id F (G.obj T) b))
  exact ⟨Function.LeftInverse.injective hl, Function.RightInverse.surjective hr⟩

theorem restrict_cover_pull2_bijective {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) {J : Type}
    (U : J → X.Opens) (hU : ⨆ i, U i = ⊤) :
    Function.Bijective (CoefMap.restrict (OAff s) (Monotone.functor
      (f := (Subtype.val : {V : X.affineOpens // ∃ i, V.1 ≤ U i} → X.affineOpens)) fun _ _ h ↦ h).op).pull2 := by
  set G := (Monotone.functor
      (f := (Subtype.val : {V : X.affineOpens // ∃ i, V.1 ≤ U i} → X.affineOpens)) fun _ _ h ↦ h).op
  have hcov : ∀ T : AffOp X, ∃ (n : ℕ) (b : Fin n → (OAff s).obj T),
      Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : AffOp X) (u : T ⟶ S),
        IsUnit (mp (OAff s) u (b i)) →
          ∃ (t : {V : X.affineOpens // ∃ i, V.1 ≤ U i}ᵒᵖ) (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u := by
    intro T
    have hT : IsAffineOpen T.unop.1 := T.unop.2
    let Gs : Set Γ(X, T.unop.1) := {f | ∃ j, X.basicOpen f ≤ U j}
    have hG : Ideal.span Gs = ⊤ := by
      rw [← hT.self_le_iSup_basicOpen_iff]
      intro x hx
      have hxU : x ∈ ⨆ i, U i := by rw [hU]; trivial
      obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hxU
      obtain ⟨f, hf, hxf⟩ := hT.exists_basicOpen_le (V := U j) ⟨x, hj⟩ hx
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, ⟨j, hf⟩⟩, hxf⟩
    obtain ⟨F, hFG, hF⟩ := (Ideal.span_eq_top_iff_finite Gs).1 hG
    refine ⟨F.card, fun i ↦ (F.equivFin.symm i).1, ?_, ?_⟩
    · have hR : Set.range (fun i : Fin F.card ↦ (F.equivFin.symm i).1) = (F : Set Γ(X, T.unop.1)) := by
        ext f
        constructor
        · rintro ⟨i, rfl⟩; exact (F.equivFin.symm i).2
        · intro hf; exact ⟨F.equivFin ⟨f, hf⟩, by simp⟩
      exact hR ▸ hF
    · intro i S u hu
      obtain ⟨j, hj⟩ := hFG (F.equivFin.symm i).2
      set f : Γ(X, T.unop.1) := (F.equivFin.symm i).1
      have hW : IsAffineOpen (X.basicOpen f) := hT.basicOpen f
      have hWT : X.basicOpen f ≤ T.unop.1 := X.basicOpen_le f
      have hSW : S.unop.1 ≤ X.basicOpen f := by
        have h1 : X.basicOpen (X.presheaf.map (homOfLE (leOfHom u.unop)).op f) = S.unop.1 :=
          X.basicOpen_of_isUnit hu
        rw [Scheme.basicOpen_res] at h1
        rw [← h1]; exact inf_le_right
      let t : {V : X.affineOpens // ∃ i, V.1 ≤ U i} := ⟨⟨_, hW⟩, j, hj⟩
      refine ⟨Opposite.op t, (homOfLE (show (⟨_, hW⟩ : X.affineOpens) ≤ T.unop from hWT)).op,
        (homOfLE (show S.unop ≤ (⟨_, hW⟩ : X.affineOpens) from hSW)).op, ?_⟩
      exact Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  have hdir : ∀ (t₁ t₂ : {V : X.affineOpens // ∃ i, V.1 ≤ U i}ᵒᵖ) (S : AffOp X), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) →
      ∃ (n : ℕ) (b : Fin n → (OAff s).obj S), Ideal.span (Set.range b) = ⊤ ∧
        ∀ (i : Fin n) (S' : AffOp X) (u : S ⟶ S'), IsUnit (mp (OAff s) u (b i)) →
          ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S') := by
    intro t₁ t₂ S h₁ h₂
    refine ⟨1, fun _ ↦ 1, ?_, fun _ S' u _ ↦ ?_⟩
    · rw [Ideal.span_eq_top_iff_finite]
      exact ⟨{1}, by simp, by simp⟩
    · obtain ⟨j, hj⟩ := t₁.unop.2
      have hS'S : S'.unop ≤ S.unop := leOfHom u.unop
      have hS1 : S.unop ≤ t₁.unop.1 := leOfHom h₁.unop
      have hS2 : S.unop ≤ t₂.unop.1 := leOfHom h₂.unop
      let t₃ : {V : X.affineOpens // ∃ i, V.1 ≤ U i} := ⟨S'.unop, j, le_trans (hS'S.trans hS1) hj⟩
      refine ⟨Opposite.op t₃, ⟨(homOfLE (show t₃ ≤ t₁.unop from hS'S.trans hS1)).op⟩,
        ⟨(homOfLE (show t₃ ≤ t₂.unop from hS'S.trans hS2)).op⟩, ⟨𝟙 _⟩⟩
  have H := _root_.GlobalTheory.CechDR.hasLoc_OAff s
  have hs := _root_.GlobalTheory.sep_of_factoring_cover (OAff s) G H hcov
  have hg := _root_.GlobalTheory.CatCoh.Desc.glue_comma_of_basis (OAff s) G H hcov hdir
  have hv := _root_.GlobalTheory.CatCoh.Desc.Basis.oneCocycle_vanishing_comma_of_basis (OAff s) G H hcov hdir
  have hv2 := GlobalTheory.T.twoCocycle_coboundary_of_basisFunctor (OAff s) G H hcov hdir
  exact ⟨GlobalTheory.T.comma_descent_injective _ _ hs hg hv, GlobalTheory.T.comma_descent_restriction_equiv _ _ hs hg hv hv2⟩

theorem restrict_pull2_bijective : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (J : Type) [Finite J] [SemilatticeInf J] (U : J → X.affineOpens) (hU : Monotone U), (∀ i j, (U (i ⊓ j)).1 = (U i).1 ⊓ (U j).1) → ⨆ i, (U i).1 = ⊤ → Function.Bijective (CoefMap.restrict (OAff s) hU.functor.op).pull2 := by
  intro R _ X s J _ _ U hU hinf hcov
  classical
  haveI := Fintype.ofFinite J
  let B : Type := {V : X.affineOpens // ∃ i, V.1 ≤ (U i).1}
  have hne : ∀ V : B, (Finset.univ.filter fun i => V.1.1 ≤ (U i).1).Nonempty := fun V => by
    obtain ⟨i, hi⟩ := V.2
    exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩⟩
  let σ : B → J := fun V => (Finset.univ.filter fun i => V.1.1 ≤ (U i).1).inf' (hne V) id
  let u : J → B := fun i => ⟨U i, i, le_rfl⟩
  have hσ : ∀ V : B, V.1.1 ≤ (U (σ V)).1 := fun V =>
    Finset.inf'_induction (p := fun i => V.1.1 ≤ (U i).1) (hne V) id
      (fun a ha b hb => by rw [hinf]; exact le_inf ha hb) fun i hi => (Finset.mem_filter.1 hi).2
  have gc : GaloisConnection σ u := fun V i =>
    ⟨fun h => (hσ V).trans (hU h), fun h =>
      Finset.inf'_le (s := Finset.univ.filter fun i : J => V.1.1 ≤ (U i).1) (id : J → J)
        (Finset.mem_filter.2 ⟨Finset.mem_univ i, h⟩)⟩
  let incl : Bᵒᵖ ⥤ AffOp X := (Monotone.functor (f := (Subtype.val : B → X.affineOpens)) fun _ _ h ↦ h).op
  have b1 : Function.Bijective (CoefMap.restrict (OAff s) incl).pull2 :=
    restrict_cover_pull2_bijective s (fun i => (U i).1) hcov
  have b2 := adj_pull2_bijective (incl ⋙ OAff s) gc.monotone_u.functor.op gc.monotone_l.functor.op
    gc.adjunction.op
  have e : ∀ c, (CoefMap.restrict (OAff s) hU.functor.op).pull2 c =
      (CoefMap.restrict (incl ⋙ OAff s) gc.monotone_u.functor.op).pull2
        ((CoefMap.restrict (OAff s) incl).pull2 c) := fun c =>
    (CoefMap.pullCohomologyTwo_eq_of_natTrans (CoefMap.restrict (OAff s) hU.functor.op)
      ((CoefMap.restrict (OAff s) incl).comp (CoefMap.restrict (incl ⋙ OAff s) gc.monotone_u.functor.op))
      (𝟙 _) (fun T b => mp_id (OAff s) _ b) c).trans (CoefMap.pullCohomologyTwo_comp _ _ c)
  have := b2.comp b1
  exact (funext e : _ = _) ▸ this

end GlobalTheory.AbCohCover
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictFiniteAffineCoverInfClosedPull2BijectiveStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restrict_finite_affineCover_infClosed_pull2_bijective : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (J : Type) [Finite J] [SemilatticeInf J] (U : J → X.affineOpens) (hU : Monotone U), (∀ i j, (U (i ⊓ j)).1 = (U i).1 ⊓ (U j).1) → ⨆ i, (U i).1 = ⊤ → Function.Bijective (CoefMap.restrict (OAff s) hU.functor.op).pull2 := by
  first | exact @GlobalTheory.AbCohCover.restrict_pull2_bijective | exact GlobalTheory.AbCohCover.restrict_pull2_bijective | (intros; apply GlobalTheory.AbCohCover.restrict_pull2_bijective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimitiveRat
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal UpperHalfPlane ReciprocityTheory.ChartRestriction.L1
open scoped UpperHalfPlane

namespace GlobalTheory.IdealTheta

theorem exists_primitive_rat {K : Type} [Field K] [CharZero K] (a₁ a₂ : K) (r s : ℚ)
    (h : (r : K) * a₁ + (s : K) * a₂ = 1) :
    ∃ (c : ℚ) (p q u v : ℤ), 0 < c ∧ p * v - q * u = 1 ∧ (p : K) * a₁ + (q : K) * a₂ = (c : K) := by
  set A : ℤ := r.num * s.den with hA
  set B : ℤ := s.num * r.den with hB
  have hr : (r : K) * (r.den : K) = (r.num : K) := by
    have := congrArg (fun t : ℚ => (t : K)) (Rat.mul_den_eq_num r)
    push_cast at this; exact this
  have hs : (s : K) * (s.den : K) = (s.num : K) := by
    have := congrArg (fun t : ℚ => (t : K)) (Rat.mul_den_eq_num s)
    push_cast at this; exact this
  have hAB : (A : K) * a₁ + (B : K) * a₂ = (r.den : K) * (s.den : K) := by
    rw [hA, hB]; push_cast
    rw [← hr, ← hs]
    linear_combination ((r.den : K) * (s.den : K)) * h
  have hN : (r.den : K) * (s.den : K) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.mpr r.den_nz) (Nat.cast_ne_zero.mpr s.den_nz)
  have hg : Int.gcd A B ≠ 0 := by
    intro h0
    rw [Int.gcd_eq_zero_iff] at h0
    rw [h0.1, h0.2] at hAB
    apply hN
    rw [← hAB]; simp
  obtain ⟨p, hp⟩ : ((Int.gcd A B : ℕ) : ℤ) ∣ A := Int.gcd_dvd_left A B
  obtain ⟨q, hq⟩ : ((Int.gcd A B : ℕ) : ℤ) ∣ B := Int.gcd_dvd_right A B
  have hbez := Int.gcd_eq_gcd_ab A B
  set g : ℕ := Int.gcd A B with hgdef
  have hgZ : (g : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hg
  have hgK : (g : K) ≠ 0 := Nat.cast_ne_zero.mpr hg
  refine ⟨((r.den : ℚ) * (s.den : ℚ)) / (g : ℚ), p, q, -Int.gcdB A B, Int.gcdA A B, ?_, ?_, ?_⟩
  · have h1 : (0 : ℚ) < r.den := Nat.cast_pos.mpr r.den_pos
    have h2 : (0 : ℚ) < s.den := Nat.cast_pos.mpr s.den_pos
    have h3 : (0 : ℚ) < g := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hg)
    positivity
  · apply mul_left_cancel₀ hgZ
    linear_combination -hbez - Int.gcdA A B * hp - Int.gcdB A B * hq
  · have hpK : (A : K) = (g : K) * (p : K) := by exact_mod_cast congrArg (fun t : ℤ => (t : K)) hp
    have hqK : (B : K) = (g : K) * (q : K) := by exact_mod_cast congrArg (fun t : ℤ => (t : K)) hq
    push_cast
    rw [eq_div_iff hgK, ← hAB, hpK, hqK]
    ring

theorem main : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ) (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (Λ : PeriodPair), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) → 𝔞 ≠ 0 → GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.IsLatOf ι 𝔞 Λ → ∃ (c : ℚ) (θ : K) (τ : ℍ), 0 < c ∧ ι θ = (τ : ℂ) ∧ IsTauOf Λ (c : ℂ) τ ∧ ∀ x : K, x ∈ 𝔞 ↔ ∃ a b : ℤ, x = (c : K) * ((a : K) * θ + (b : K)) := by
  intro K _ _ d δ ι 𝔞 Λ hK _ _ _ hΛ
  obtain ⟨c₀, τ₀, hc₀, hlat⟩ := latTau Λ
  have hmem : ∀ z : ℂ, z ∈ Λ.lattice ↔ ∃ y : K, y ∈ 𝔞 ∧ ι y = z := by
    intro z
    have : z ∈ (Λ.lattice : Set ℂ) ↔ z ∈ ι '' (𝔞 : Set K) := by rw [hΛ]
    exact this
  obtain ⟨a₁, -, ha₁⟩ := (hmem (c₀ * τ₀)).mp ((hlat _).mpr ⟨1, 0, by simp⟩)
  obtain ⟨a₂, -, ha₂⟩ := (hmem c₀).mp ((hlat _).mpr ⟨0, 1, by simp⟩)
  have hA : ∀ x : K, x ∈ 𝔞 ↔ ∃ m n : ℤ, x = (m : K) * a₁ + (n : K) * a₂ := by
    intro x
    have h1 : x ∈ 𝔞 ↔ ι x ∈ Λ.lattice := by
      rw [hmem]
      exact ⟨fun h => ⟨x, h, rfl⟩, fun ⟨y, hy, e⟩ => ι.injective e ▸ hy⟩
    rw [h1, hlat]
    refine exists_congr fun m => exists_congr fun n => ?_
    rw [← ι.injective.eq_iff]
    simp only [map_add (f := _), map_mul, map_intCast, ha₁, ha₂]
    constructor <;> intro h <;> rw [h] <;> ring
  have hli : LinearIndependent ℚ ![a₁, a₂] := by
    rw [LinearIndependent.pair_iff]
    intro r s h
    rw [Rat.smul_def, Rat.smul_def] at h
    have h1 := congrArg ι h
    simp only [map_add (f := _), map_mul, map_ratCast, ha₁, ha₂, map_zero] at h1
    have h2 : (r : ℂ) * τ₀ + (s : ℂ) = 0 := by
      apply mul_left_cancel₀ hc₀
      linear_combination h1
    have h3 := congrArg Complex.im h2
    have hr : r = 0 := by
      have := τ₀.im_ne_zero
      simpa [this] using h3
    subst hr
    simpa using h2
  have hspan := hli.span_eq_top_of_card_eq_finrank (by simp [hK])
  obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp
    (show (1 : K) ∈ Submodule.span ℚ (Set.range ![a₁, a₂]) by rw [hspan]; trivial)
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Rat.smul_def] at hw
  obtain ⟨c, p, q, u, v, hc, hdet, hcK⟩ := exists_primitive_rat a₁ a₂ (w 0) (w 1) hw
  have hcK0 : (c : K) ≠ 0 := by exact_mod_cast hc.ne'
  have hcC0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hdetK : (p : K) * v - q * u = 1 := by exact_mod_cast congrArg (fun t : ℤ => (t : K)) hdet
  have hdetR : (p : ℝ) * v - q * u = 1 := by exact_mod_cast hdet
  set θ : K := -((u : K) * a₁ + (v : K) * a₂) / (c : K) with hθ
  have hcθ : (c : K) * θ = -((u : K) * a₁ + (v : K) * a₂) := by
    rw [hθ]; field_simp
  have hcC : (c : ℂ) = c₀ * ((p : ℂ) * τ₀ + q) := by
    have h1 := congrArg ι hcK
    simp only [map_add (f := _), map_mul, map_ratCast, map_intCast, ha₁, ha₂] at h1
    linear_combination -h1
  have hz : ((p : ℂ) * τ₀ + q) ≠ 0 := by
    intro h0; apply hcC0; rw [hcC, h0, mul_zero]
  have hιθ : ι θ = -((u : ℂ) * τ₀ + v) / ((p : ℂ) * τ₀ + q) := by
    have h1 := congrArg ι hcθ
    simp only [map_add (f := _), map_mul, map_neg, map_ratCast, map_intCast, ha₁, ha₂] at h1
    rw [eq_div_iff hz]
    apply mul_left_cancel₀ hc₀
    rw [hcC] at h1
    linear_combination h1
  have him : 0 < (ι θ).im := by
    rw [hιθ, Complex.div_im, ← sub_div]
    refine div_pos ?_ (Complex.normSq_pos.mpr hz)
    have hy : 0 < (τ₀ : ℂ).im := τ₀.im_pos
    simp only [Complex.neg_im, Complex.neg_re, Complex.add_im, Complex.add_re, Complex.mul_im, Complex.mul_re,
      Complex.intCast_im, Complex.intCast_re]
    have : -(↑u * (τ₀ : ℂ).im + 0 * (τ₀ : ℂ).re + 0) * (↑p * (τ₀ : ℂ).re - 0 * (τ₀ : ℂ).im + ↑q) -
        -(↑u * (τ₀ : ℂ).re - 0 * (τ₀ : ℂ).im + ↑v) * (↑p * (τ₀ : ℂ).im + 0 * (τ₀ : ℂ).re + 0) = (τ₀ : ℂ).im := by
      linear_combination (τ₀ : ℂ).im * hdetR
    rw [this]; exact hy
  have hmain : ∀ x : K, x ∈ 𝔞 ↔ ∃ a b : ℤ, x = (c : K) * ((a : K) * θ + (b : K)) := by
    intro x
    rw [hA]
    constructor
    · rintro ⟨m, n, rfl⟩
      refine ⟨m * q - n * p, m * v - n * u, ?_⟩
      push_cast
      linear_combination (-((m : K) * q - n * p)) * hcθ + ((m : K) * v - n * u) * hcK
        - ((m : K) * a₁ + (n : K) * a₂) * hdetK
    · rintro ⟨a, b, rfl⟩
      refine ⟨b * p - a * u, b * q - a * v, ?_⟩
      push_cast
      linear_combination (a : K) * hcθ - (b : K) * hcK
  refine ⟨c, θ, ⟨ι θ, him⟩, hc, rfl, ⟨hcC0, fun z => ?_⟩, hmain⟩
  rw [hmem]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨a, b, rfl⟩ := (hmain y).mp hy
    exact ⟨a, b, by simp⟩
  · rintro ⟨a, b, rfl⟩
    exact ⟨_, (hmain _).mpr ⟨a, b, rfl⟩, by simp⟩

end GlobalTheory.IdealTheta
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPushforwardRegularIdeal
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Cartier.PullIdeal

open CartierDiv

theorem exists_pow_regularAt {Y : Scheme.{0}} [IsIntegral Y] (D : CartierDiv Y) {V : Y.Opens}
    (hV : IsCompact (V : Set Y)) (hηV : genericPoint Y ∈ V) (t : Γ(Y, V)) (F : Y.functionField)
    (hF : ∀ z ∈ Y.basicOpen t, D.RegularAt z F) :
    ∃ n : ℕ, ∀ z ∈ V, D.RegularAt z (fnOf V hηV t ^ n * F) := by
  by_cases ht : genericPoint Y ∈ Y.basicOpen t
  swap
  · refine ⟨1, fun z _ => ?_⟩
    have h0 : fnOf V hηV t = 0 := by
      by_contra h
      exact ht ((unitAt_fnOf_iff hηV hηV t).1 (unitAt_genericPoint h))
    rw [h0, pow_one, zero_mul]
    exact (D.vanishesAt_zero z).regularAt
  have loc : ∀ y : V, ∃ W : Y.Opens, y.1 ∈ W ∧ ∃ n : ℕ,
      ∀ z ∈ W, D.RegularAt z (fnOf V hηV t ^ n * F) := by
    intro y
    obtain ⟨V', hyV', g, hg⟩ := D.exists_isEqn_nhds y.1
    obtain ⟨W, hW, hyW, hWV⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens
      (show y.1 ∈ V ⊓ V' from ⟨y.2, hyV'⟩)
    have hWV1 : W ≤ V := hWV.trans inf_le_left
    set t' : Γ(Y, W) := Y.presheaf.map (homOfLE hWV1).op t
    have hB : Y.basicOpen t' = W ⊓ Y.basicOpen t := Y.basicOpen_res t _
    have hgen : genericPoint Y ∈ Y.basicOpen t' := hB ▸ memInf (gen_mem hyW) ht
    obtain ⟨b, hb⟩ := exists_fnOf_eq (f := F * (g : Y.functionField)) hgen fun z hz => by
      rw [hB] at hz
      exact (hg z (hWV hz.1).2).regularAt_iff.1 (hF z hz.2)
    obtain ⟨n, a, ha⟩ := exists_eq_pow_mul_of_isAffineOpen Y W hW t' b
    have key : fnOf W (gen_mem hyW) a = fnOf V hηV t ^ n * (F * (g : Y.functionField)) := by
      have e := congrArg (fnOf _ hgen) ha
      rw [map_mul, map_pow, hb] at e
      erw [SecPowLoc.fnOf_map, SecPowLoc.fnOf_map, SecPowLoc.fnOf_map] at e
      exact e
    refine ⟨W, hyW, n, fun z hz => (hg z (hWV hz).2).regularAt_iff.2 ?_⟩
    rw [mul_assoc, ← key]
    exact regAt_fnOf hz _ a
  choose W hyW n hn using loc
  obtain ⟨T, hT⟩ := hV.elim_finite_subcover (fun y : V => (W y : Set Y)) (fun y => (W y).isOpen)
    (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hyW _⟩)
  refine ⟨T.sup n, fun z hz => ?_⟩
  obtain ⟨y, hyT, hzy⟩ := Set.mem_iUnion₂.1 (hT hz)
  have hle : n y ≤ T.sup n := Finset.le_sup hyT
  have hr := regAt_fnOf hz hηV (t ^ (T.sup n - n y))
  rw [map_pow] at hr
  rw [← Nat.sub_add_cancel hle, pow_add, mul_assoc]
  exact (hn y z hzy).regAt_mul hr

theorem regAt_pull {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (s : Y ⟶ X) [IsDominant s]
    {U : X.Opens} {y : Y} (hy : s y ∈ U) (c : Γ(X, U)) :
    RegAt y (functionFieldMap s (fnOf U (gen_mem hy) c)) := by
  have hy' : y ∈ s ⁻¹ᵁ U := hy
  rw [← PullPres.fnOf_app s (gen_mem hy') c]
  exact regAt_fnOf hy' _ _

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (s : Y ⟶ X) [IsDominant s]
  (D : CartierDiv Y)

def pullIdeal (U : X.Opens) : Ideal Γ(X, U) where
  carrier := {f | ∀ (y : Y) (hy : s y ∈ U), D.RegularAt y (functionFieldMap s (fnOf U (gen_mem hy) f))}
  zero_mem' y hy := by rw [map_zero, map_zero]; exact (D.vanishesAt_zero y).regularAt
  add_mem' hf hg y hy := by rw [map_add (f := _), map_add (f := _)]; exact (hf y hy).add (hg y hy)
  smul_mem' c f hf y hy := by
    rw [smul_eq_mul, map_mul, map_mul]
    exact (hf y hy).regAt_mul (regAt_pull s hy c)

def pullIdealSheaf [QuasiCompact s] : X.IdealSheafData where
  ideal U := pullIdeal s D U.1
  map_ideal_basicOpen U a := by
    show Ideal.map (X.presheaf.map (homOfLE (X.basicOpen_le a)).op).hom (pullIdeal s D U.1) =
      pullIdeal s D (X.basicOpen a)
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro f hf
      rw [Ideal.mem_comap]
      intro y hy
      have := hf y (X.basicOpen_le a hy)
      convert this using 3
      exact SecPowLoc.fnOf_map _ _ _
    · intro h hh
      by_cases hg : genericPoint X ∈ X.basicOpen a
      swap
      · have : h = 0 := fn_ext fun h' => (hg h').elim
        rw [this]; exact zero_mem _
      obtain ⟨n, b, hb⟩ := exists_eq_pow_mul_of_isAffineOpen X U.1 U.2 a h
      have hU0 : genericPoint X ∈ U.1 := X.basicOpen_le a hg
      have e' : fnOf U.1 hU0 b = fnOf U.1 hU0 a ^ n * fnOf _ hg h := by
        have := congrArg (fnOf _ hg) hb
        rw [map_mul, map_pow] at this
        erw [SecPowLoc.fnOf_map, SecPowLoc.fnOf_map] at this
        exact this
      obtain ⟨M, hM⟩ : ∃ M : ℕ, a ^ M * b ∈ pullIdeal s D U.1 := by
        by_cases hηV : genericPoint Y ∈ s ⁻¹ᵁ U.1
        · obtain ⟨M, hM⟩ := exists_pow_regularAt D (s.isCompact_preimage U.2.isCompact) hηV
            ((s.app U.1).hom a) (functionFieldMap s (fnOf U.1 hU0 b)) (fun z hz => by
              rw [← Scheme.preimage_basicOpen] at hz
              rw [e', map_mul, map_pow]
              have hr := regAt_pull s (U := U.1) (X.basicOpen_le a hz) (a ^ n)
              rw [map_pow, map_pow] at hr
              exact (hh z hz).regAt_mul hr)
          refine ⟨M, fun y hy => ?_⟩
          have := hM y hy
          rw [PullPres.fnOf_app] at this
          rw [map_mul, map_mul, map_pow, map_pow]
          exact this
        · exact ⟨0, fun y hy => (hηV (gen_mem (x := y) hy)).elim⟩
      have hu : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le a)).op a) :=
        X.toRingedSpace.isUnit_res_basicOpen a
      have hb' : X.presheaf.map (homOfLE (X.basicOpen_le a)).op (a ^ M * b) =
          h * (hu.unit : Γ(X, X.basicOpen a)) ^ (n + M) := by
        have hb2 : X.presheaf.map (homOfLE (X.basicOpen_le a)).op b =
            X.presheaf.map (homOfLE (X.basicOpen_le a)).op a ^ n * h := hb
        rw [map_mul, map_pow, hb2]
        rw [IsUnit.unit_spec, pow_add]
        ring
      have : h = X.presheaf.map (homOfLE (X.basicOpen_le a)).op (a ^ M * b) *
          ((hu.unit⁻¹ ^ (n + M) : (Γ(X, X.basicOpen a))ˣ) : Γ(X, X.basicOpen a)) := by
        rw [hb', mul_assoc, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← mul_pow, mul_inv_cancel,
          one_pow, Units.val_one, mul_one]
      rw [this]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hM)

theorem exists_idealSheaf : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (s : Y ⟶ X) [IsDominant s]
    [QuasiCompact s] (D : CartierDiv Y), ∃ J : X.IdealSheafData, (∀ (U : X.affineOpens) (f : Γ(X, U.1)),
    f ∈ J.ideal U ↔ ∀ (y : Y) (hy : s y ∈ U.1), D.RegularAt y (functionFieldMap s (fnOf U.1 (gen_mem hy) f))) := by
  intro X Y _ _ s _ _ D
  exact ⟨pullIdealSheaf s D, fun _ _ => Iff.rfl⟩

end GlobalTheory.Cartier.PullIdeal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanInvariantOneFormsAffineOpenAbelianSchemeEqTo
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanInvariantOneFormsAffineOpenAbelianSchemeEqTo
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
open GlobalTheory.AbTan GlobalTheory.AbTan.Transl GlobalTheory.TanForms GlobalTheory.InvForm

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.InvSpan

variable {R : Type} [CommRing R]

theorem dVal_smul {B D : Type} [CommRing B] [Algebra R B] [CommRing D] [Algebra R D]
    (φ : B →ₐ[R] DualNumber D) (b : B) (m : Ω[B⁄R]) : dVal φ (b • m) = redHom φ b * dVal φ m := by
  letI : Algebra B D := (redHom φ).toAlgebra
  haveI : IsScalarTower R B D := IsScalarTower.of_algebraMap_eq fun r ↦ (redHom_algebraMap φ r).symm
  exact (map_smul (Derivation.liftKaehlerDifferential _) b m).trans (Algebra.smul_def _ _)

variable {A : Over (Sp R)} [GrpObj A] {W : Type} [AddCommGroup W] [Module R W]

def tr (A : Over (Sp R)) [GrpObj A] : TrTy A := fun B M ↦ tau A B M

theorem tr_bij : TrBij A (tr A) := fun _ _ _ _ _ _ _ _ P hP ↦ bijOn_tau A P hP

theorem tr_nat : TrNat A (tr A) := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ α f β hβ P hP z hz ↦
  tau_natural A α f β hβ P hP z hz

theorem exists_tangent (T : TanRep A W) (U : A.left.affineOpens) {D : Type} [CommRing D] [Algebra R D]
    (φ : Sec A.hom U.1 →ₐ[R] DualNumber D) :
    ∃ z : Sp (DualNumber D) ⟶ A.left, Lifts A.hom (unitPt A D) z ∧
      tau A D D (spMap (redHom φ) ≫ affPt A.hom U) z =
        spMap (φ : Sec A.hom U.1 →+* DualNumber D) ≫ affPt A.hom U ∧
      ∀ w, T.Φ z w = dVal φ (eU T (tr A) U w) := by
  letI := opMod (Sec A.hom U.1) Ω[Sec A.hom U.1⁄R]
  haveI : IsCentralScalar (Sec A.hom U.1) Ω[Sec A.hom U.1⁄R] := ⟨fun _ _ ↦ rfl⟩
  obtain ⟨hz0, hτz0⟩ := back_spec (τ := tr A) U tr_bij (pt A U (KaehlerDifferential.D R (Sec A.hom U.1)))
    (pt_lifts A U _)
  let α : Sec A.hom U.1 →ₐ[R] D := { redHom φ with commutes' := redHom_algebraMap φ }
  have hf : ∀ (b : Sec A.hom U.1) (m : Ω[Sec A.hom U.1⁄R]), (dVal φ).toAddMonoidHom (b • m) =
      redHom φ b • (dVal φ).toAddMonoidHom m := fun b m ↦ dVal_smul φ b m
  let β := sumHom (redHom φ) (dVal φ).toAddMonoidHom hf
  have hβ : IsSum β α (dVal φ) := sumHom_isSum _ (dVal φ).toAddMonoidHom hf
  obtain ⟨hl, hnat⟩ := tau_natural A α (dVal φ) β hβ (affPt A.hom U) (affPt_w A.hom U) _ hz0
  have hpt : spMap β ≫ pt A U (KaehlerDifferential.D R (Sec A.hom U.1)) =
      spMap (φ : Sec A.hom U.1 →+* DualNumber D) ≫ affPt A.hom U := by
    rw [pt, ← Category.assoc, sp_comp]
    congr 2
    refine RingHom.ext fun b ↦ ?_
    rw [RingHom.comp_apply, show TanForms.derHom (KaehlerDifferential.D R (Sec A.hom U.1)) b =
      TrivSqZeroExt.inl b + TrivSqZeroExt.inr (KaehlerDifferential.D R (Sec A.hom U.1) b) from rfl, map_add,
      hβ.1, hβ.2, dVal_D]
    exact TrivSqZeroExt.inl_fst_add_inr_snd_eq (φ b)
  refine ⟨_, hl, ?_, fun w ↦ ?_⟩
  · refine hnat.trans ?_
    rw [← hpt]
    exact congrArg _ hτz0
  · rw [T.nat α (dVal φ) β hβ _ hz0]
    rfl

def form (T : TanRep A W) (w : W) : GlobForm A.hom :=
  ⟨fun V ↦ eU T (tr A) V.unop w, fun _ _ a ↦ eU_nat T tr_bij tr_nat a w⟩

theorem red_w (U : A.left.affineOpens) {D : Type} [CommRing D] [Algebra R D]
    (φ : Sec A.hom U.1 →ₐ[R] DualNumber D) :
    (spMap (redHom φ) ≫ affPt A.hom U) ≫ A.hom = spMap (algebraMap R D) := by
  rw [Category.assoc, affPt_w, sp_comp]
  exact congrArg spMap (RingHom.ext (redHom_algebraMap φ))

theorem isInv_form [IsCommMonObj A] (T : TanRep A W) (w : W) : IsInv A (form T w) := by
  intro D _ _ U V φ ψ p q q₀ hp hq hpq
  obtain ⟨z, hz, hτ, hΦ⟩ := exists_tangent T U φ
  obtain ⟨z', hz', hτ', hΦ'⟩ := exists_tangent T V ψ
  change dVal φ (eU T (tr A) U w) = dVal ψ (eU T (tr A) V w)
  rw [← hΦ, ← hΦ']
  suffices h : z = z' by rw [h]
  rw [tau_eq A _ (red_w U φ) z hz.1, ← hp] at hτ
  rw [tau_eq A _ (red_w V ψ) z' hz'.1, ← hpq] at hτ'
  let c : ovT R D D ⟶ ovT R D D :=
    Over.homMk (spMap (TrivSqZeroExt.inlHom D D) ≫ spMap (TrivSqZeroExt.fstHom D D D).toRingHom) (by
      rw [Category.assoc, fst_w]
      exact sp_comp _ _)
  let p' : ovT R D D ⟶ A := p
  let q' : ovT R D D ⟶ A := q
  have e1 : Over.homMk (U := ovT R D D) (V := A)
      (spMap (TrivSqZeroExt.inlHom D D) ≫ spMap (redHom φ) ≫ affPt A.hom U) (inl_w A _ (red_w U φ)) =
      c ≫ p' := by
    ext
    change spMap _ ≫ spMap (redHom φ) ≫ affPt A.hom U = (spMap _ ≫ spMap _) ≫ p.left
    rw [hp, Category.assoc, ← Category.assoc (spMap _) (spMap (φ : Sec A.hom U.1 →+* DualNumber D)), sp_comp]
    rfl
  have e2 : Over.homMk (U := ovT R D D) (V := A)
      (spMap (TrivSqZeroExt.inlHom D D) ≫ spMap (redHom ψ) ≫ affPt A.hom V) (inl_w A _ (red_w V ψ)) =
      c ≫ (p' * q') := by
    ext
    change spMap _ ≫ spMap (redHom ψ) ≫ affPt A.hom V = (spMap _ ≫ spMap _) ≫ (p * q).left
    rw [hpq, Category.assoc, ← Category.assoc (spMap _) (spMap (ψ : Sec A.hom V.1 →+* DualNumber D)), sp_comp]
    rfl
  have e3 : c ≫ q' = q' := by
    ext
    change (_ ≫ _) ≫ q.left = q.left
    rw [hq, Category.assoc]
    change _ ≫ _ ≫ spMap (TrivSqZeroExt.inlHom D D) ≫ q₀ = _
    rw [← Category.assoc (spMap _) (spMap _) q₀, fst_inl, Category.id_comp]
  rw [e1] at hτ
  rw [e2, MonObj.comp_mul, e3] at hτ'
  have k1 : (c ≫ p') * Over.homMk (U := ovT R D D) (V := A) z hz.1 = p' := Over.OverMorphism.ext hτ
  have k2 : (c ≫ p') * q' * Over.homMk (U := ovT R D D) (V := A) z' hz'.1 = p' * q' :=
    Over.OverMorphism.ext hτ'
  have k3 : Over.homMk (U := ovT R D D) (V := A) z hz.1 = Over.homMk (U := ovT R D D) (V := A) z' hz'.1 := by
    rw [mul_right_comm] at k2
    exact mul_left_cancel (k1.trans (mul_right_cancel k2).symm)
  exact congrArg CommaMorphism.left k3

theorem span_eq_top_of_tanRep [IsCommMonObj A] (T : TanRep A W) (U : AffOp A.left) :
    Submodule.span (Sec A.hom U.unop.1) (Set.range fun w : InvForm A ↦ evForm A.hom U w.1) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  induction x using (eU_isBaseChange T tr_bij tr_nat U.unop).inductionOn with
  | tmul w => exact Submodule.subset_span ⟨⟨form T w, isInv_form T w⟩, rfl⟩
  | smul s n hn => exact Submodule.smul_mem _ _ (hn trivial)
  | add a b ha hb => exact add_mem (ha trivial) (hb trivial)

theorem span_invForm_eq_top : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ U : AffOp A.left,
    Submodule.span (Sec A.hom U.unop.1)
      (Set.range fun w : GlobalTheory.InvForm.InvForm A ↦ evForm A.hom U w.1) = ⊤ := by
  intro R _ A _ g hA _ U
  have := hA.comm
  obtain ⟨W, _, _, -, -, ⟨T⟩⟩ := GlobalTheory.T.exists_tangentRepresentation_smooth_groupScheme R A hA.smooth
  exact span_eq_top_of_tanRep T U

end GlobalTheory.InvSpan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanInvariantOneFormsAffineOpenAbelianSchemeEqToStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_invariantOneForms_affineOpen_abelianScheme_eq_top : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ U : AffOp A.left, Submodule.span (Sec A.hom U.unop.1) (Set.range fun w : GlobalTheory.InvForm.InvForm A ↦ evForm A.hom U w.1) = ⊤ := by
  first | exact @GlobalTheory.InvSpan.span_invForm_eq_top | exact GlobalTheory.InvSpan.span_invForm_eq_top | (intros; apply GlobalTheory.InvSpan.span_invForm_eq_top <;> assumption)
end
end
