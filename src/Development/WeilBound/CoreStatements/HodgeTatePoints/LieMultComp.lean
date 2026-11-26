module

public import Development.AutomorphicSpectrum.Statements.GeometryStatements.KeyBadSt
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
public import Development.WeilBound.CoreStatements.HodgeTatePoints.KftwoSquare
public import Development.WeilBound.CoreStatements.HodgeTatePoints.KftwoDatum
public import Development.WeilBound.CoreStatements.HodgeTatePoints.KftwoFrame
public import Development.WeilBound.CoreStatements.HodgeTatePoints.KftwoModel

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.KftwoPoint
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace PositivityTheory.HtPt.Kftwo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_finset_point {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {Z : Scheme.{0}} (p : Z ⟶ Sp K)
    [LocallyOfFinitePresentation p] (x : Sp Ω ⟶ Z) (hx : x ≫ p = spMap (algebraMap K Ω)) :
    ∃ S : Finset Ω, ∀ K' : IntermediateField K Ω, (S : Set Ω) ⊆ K' →
      ∃ y : Sp K' ⟶ Z, spMap K'.val.toRingHom ≫ y = x := by
  obtain ⟨R, ψ, ⟨S, rfl⟩, -, h⟩ := GlobalTheory.Spread.exists_fg_comp_eq (A := Ω) (𝟙 (Sp K)) p (pullback.snd _ _ ≫ x) (by
    rw [Category.assoc, hx, pullback.condition])
  refine ⟨S, fun K' hS => ?_⟩
  have hle : Algebra.adjoin K (S : Set Ω) ≤ K'.toSubalgebra := Algebra.adjoin_le hS
  let g : Algebra.adjoin K (S : Set Ω) →+* K' := (Subalgebra.inclusion hle).toRingHom
  refine ⟨spMap g ≫ inv (pullback.snd (𝟙 (Sp K)) _) ≫ ψ, ?_⟩
  have e : spMap K'.val.toRingHom ≫ spMap g = spMap (Algebra.adjoin K (S : Set Ω)).val.toRingHom :=
    (Spec.map_comp _ _).symm
  rw [← cancel_epi (pullback.snd (𝟙 (Sp K)) (spMap (algebraMap K Ω))), ← h, ← Category.assoc (spMap _), e,
    ← Category.assoc, ← GlobalTheory.Spread.bcMap_snd, Category.assoc, IsIso.hom_inv_id_assoc]

theorem exists_coeff_embedding {l : Level H} (c : Coeff l) {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω] (ρ : Ω)
    (hρ : ρ ^ 2 = -(H.d : Ω)) : ∃ β : c.F →+* Ω, β (IntermediateField.inclusion c.le (baseKA l).ρ) = ρ := by
  have := c.fin
  set r : c.F := IntermediateField.inclusion c.le (baseKA l).ρ with hr
  have hr2 : r ^ 2 = -(H.d : c.F) := by rw [hr, ← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]
  have hd : (0 : ℚ) < H.d := by exact_mod_cast H.d_prime.pos
  have hirr : Irreducible (Polynomial.X ^ 2 - Polynomial.C (-(H.d : ℚ))) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two fun b hb => by nlinarith [sq_nonneg b]
  have hmin : Polynomial.X ^ 2 - Polynomial.C (-(H.d : ℚ)) = minpoly ℚ r :=
    minpoly.eq_of_irreducible_of_monic hirr (by simp [hr2]) (Polynomial.monic_X_pow_sub_C _ two_ne_zero)
  obtain ⟨φ, hφ⟩ := IntermediateField.exists_algHom_of_splits_of_aeval (F := ℚ) (E := c.F) (K := Ω)
    (fun s => ⟨Algebra.IsIntegral.isIntegral s, IsAlgClosed.splits _⟩) (x := r) (y := ρ) (by rw [← hmin]; simp [hρ])
  exact ⟨φ.toRingHom, hφ⟩

theorem exists_point {D : Datum H} {l : Level H} (hA : l.A = 1) (Xo : Moduli D l) (c : Coeff l) {K : Type} [Field K]
    [CharZero K] (T : GlobalTheory.CM.PAT H (Sp K)) (ρ : AlgebraicClosure K) (hρ : ρ ^ 2 = -(H.d : AlgebraicClosure K))
    (hdet : DetCond D T.t.act (spMap (algebraMap K (AlgebraicClosure K))) ρ)
    (I : TateIso D (AlgebraicClosure K) (Over.mk (spMap (algebraMap K (AlgebraicClosure K))) ⟶ T.t.G)
      (fun a g => g ≫ T.t.act.act a) (fun n g g' c => Out.WeilIs T.t.G T.t.PP.L n g g' (unitOn c))) :
    ∃ (K' : IntermediateField K (AlgebraicClosure K)) (_ : FiniteDimensional K K') (y : Sp K' ⟶ Xo.XF c)
      (t' : SAB H (Sp K')), Nonempty (SABMap t' T.t (spMap (algebraMap K K'))) ∧
        Nonempty (SABMap t' Xo.univ.t (y ≫ pullback.fst _ _)) := by
  classical
  have hL := GlobalTheory.firstFiveLaws.1
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  have := c.fin
  have hsm := T.ab.smooth
  obtain ⟨β, hβ⟩ := exists_coeff_embedding c ρ hρ
  have hcard := (hL.mulN _ T.pol l.M hM).2.2.2.2 _ (spMap (algebraMap K (AlgebraicClosure K))) (Nat.cast_ne_zero.2 hM.ne')
  have hfin : Finite {x : Over.mk (spMap (algebraMap K (AlgebraicClosure K))) ⟶ T.t.G // x ^ l.M = 1} :=
    Nat.finite_of_card_ne_zero (by erw [hcard]; positivity)
  choose S hS using fun x : {x : Over.mk (spMap (algebraMap K (AlgebraicClosure K))) ⟶ T.t.G // x ^ l.M = 1} =>
    exists_finset_point T.t.G.hom x.1.left (Over.w x.1)
  let b := Module.finBasis ℚ c.F
  let U : Set (AlgebraicClosure K) := (⋃ x, (S x : Set (AlgebraicClosure K))) ∪ Set.range fun i => β (b i)
  have hU : Finite U := ((Set.finite_iUnion fun x => (S x).finite_toSet).union (Set.finite_range _)).to_subtype
  let K' := IntermediateField.adjoin K U
  have hfd : FiniteDimensional K K' :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hβm : ∀ z, β z ∈ K' := fun z => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← b.sum_repr z, map_sum]
    refine sum_mem fun i _ => ?_
    rw [Rat.smul_def, map_mul, map_ratCast]
    exact mul_mem (SubfieldClass.ratCast_mem _ _) (IntermediateField.subset_adjoin K U (Or.inr ⟨i, rfl⟩))
  let β' : c.F →+* K' := β.codRestrict K' hβm
  let i : K' →+* AlgebraicClosure K := K'.val.toRingHom
  have hi : spMap (algebraMap K (AlgebraicClosure K)) = spMap i ≫ spMap (algebraMap K K') :=
    Spec.map_comp (CommRingCat.ofHom (algebraMap K K')) (CommRingCat.ofHom i)
  obtain ⟨T', m, -⟩ := GlobalTheory.CM.PAT.exists_pullback E H _ _ (spMap (algebraMap K K')) T
  have hm : LBIso T'.t.PP.L (T.t.PP.L.pull m.φ) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  obtain ⟨I', -, hI'⟩ := (GlobalTheory.PELDesc.tate_pull (D := D) T.t.PP.isLB T'.t.PP.isLB m.cart hm T.t.act.act T'.t.act.act m.act
    _ _ hi).2 I
  have hdet' : DetCond D T'.t.act (spMap i) ρ := (GlobalTheory.PELDesc.detCond_pull m.cart _ _ m.act _ _ hi ρ).2 hdet
  have hepi : Epi (spMap i) :=
    have := GlobalTheory.FieldBaseChange.flat_spMap i
    have := GlobalTheory.FieldBaseChange.surjective_spMap i
    Flat.epi_of_flat_of_surjective _
  have hex : ∀ a, ∃ e : 𝟙_ (Over (Sp K')) ⟶ T'.t.G, toUnit (Over.mk (spMap i)) ≫ e = I'.ev l.M a := fun a => by
    obtain ⟨y, hy⟩ := hS ⟨I.ev l.M a, (I.onto _ hM _).2 ⟨a, rfl⟩⟩ K' fun z hz =>
      IntermediateField.subset_adjoin K U (Or.inl (Set.mem_iUnion.2 ⟨_, hz⟩))
    replace hy : spMap i ≫ y = (I.ev l.M a).left := hy
    have w : y ≫ T.t.G.hom = 𝟙 _ ≫ spMap (algebraMap K K') := by
      rw [← cancel_epi (spMap i), ← Category.assoc, hy, Category.id_comp, ← hi]
      exact Over.w (I.ev l.M a)
    refine ⟨Over.homMk (m.cart.1.lift y _ w) (m.cart.1.lift_snd _ _ _), Over.OverMorphism.ext ?_⟩
    rw [Over.comp_left, Over.toUnit_left]
    show spMap i ≫ m.cart.1.lift y _ w = _
    refine m.cart.1.hom_ext ?_ ?_
    · rw [Category.assoc, IsPullback.lift_fst, hy]
      exact hI' _ _
    · rw [Category.assoc, IsPullback.lift_snd, Category.comp_id]
      exact (Over.w (I'.ev l.M a)).symm
  choose e he using hex
  have inj := GlobalTheory.HeckePoint.toUnit_comp_injective (spMap i) T'.t.G
  obtain ⟨u, hu, π, hπ, huπ⟩ := Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 l.coprime)
  have hη : ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
      I'.ev l.M (π • a) = I'.ev l.M a := fun a h => by
    conv_rhs => rw [← one_smul (𝓞 E) a, ← huπ, add_smul, I'.add,
      (I'.ker _ hM _).2 (GlobalTheory.UnifObj.exists_smul_eq l.prod hu h), _root_.one_mul]
  let κ : KA l →+* K' := β'.comp (IntermediateField.inclusion c.le).toRingHom
  have hsm' := T'.ab.smooth
  let o : Obj D l (baseKA l) (spMap κ) :=
    { t := T'.t
      proper := T'.ab.proper
      ample := T'.ample
      ktriv := T'.ktriv
      eta := fun a => e (π • a)
      eta_add := fun a c => inj (by
        show toUnit _ ≫ _ = toUnit _ ≫ _
        rw [MonObj.comp_mul, he, he, he, smul_add, I'.add])
      eta_ker := fun a h => inj (by
        show toUnit _ ≫ _ = toUnit _ ≫ _
        rw [MonObj.comp_one, he]
        exact (I'.ker _ hM _).2 (GlobalTheory.UnifObj.exists_smul_eq ((mul_comm _ _).trans l.prod) hπ h))
      etaA := fun _ => 1
      etaA_add := fun _ _ => (_root_.mul_one _).symm
      etaA_ker := fun _ => rfl
      geom := fun k _ _ x δ hx => by
        obtain ⟨φ, rfl⟩ : ∃ φ : K' →+* k, x = spMap φ := ⟨(Spec.preimage x).hom, (Spec.map_preimage x).symm⟩
        obtain rfl : φ.comp κ = δ :=
          congrArg CommRingCat.Hom.hom (Spec.map_injective ((Spec.map_comp _ _).trans hx))
        obtain ⟨ψ, rfl⟩ : ∃ ψ : AlgebraicClosure K →+* k, ψ.comp i = φ := by
          letI := φ.toAlgebra
          set_option synthInstance.maxHeartbeats 400000 in
          exact ⟨(IsAlgClosed.lift (R := K') (S := AlgebraicClosure K) (M := k)).toRingHom,
            RingHom.ext fun z => (IsAlgClosed.lift (R := K') (S := AlgebraicClosure K) (M := k)).commutes z⟩
        have hx' : spMap (ψ.comp i) = spMap ψ ≫ spMap i := Spec.map_comp (CommRingCat.ofHom i) (CommRingCat.ofHom ψ)
        rw [hx']
        obtain ⟨J, hJ⟩ := (GlobalTheory.TateIsoFieldExt.tateIso_fieldExt hL E H D _ T'.pol T'.t.act.act _ k ψ (spMap i)).1 I'
        refine ⟨?_, J, ?_, fun a => ?_, fun a h => ?_⟩
        · have := (GlobalTheory.detCond_iff_of_field_extension E H D _ T'.t.G _ k ψ (spMap i) T'.t.act ρ hsm').2 hdet'
          rw [← hβ] at this
          exact this
        · have h₁ := J.ζ_prim _ l.A_pos
          have h₂ := (baseKA l).ζ_prim
          rw [hA, IsPrimitiveRoot.one_right_iff] at h₁ h₂
          rw [hA, h₁, h₂, map_one, Units.val_one]
        · rw [hA, MonObj.comp_one]
          exact ((J.ker 1 one_pos a).2 ⟨a, (one_smul _ _).symm⟩).symm
        · refine Eq.trans ?_ ((hJ _ hM).2 a).symm
          rw [← hη a h, ← he, ← Category.assoc]
          exact congrArg (· ≫ e (π • a)) (toUnit_unique _ _) }
  obtain ⟨f, ⟨hf, ⟨n⟩⟩, -⟩ := Xo.rep _ (spMap κ) inferInstance o
  have hκ : f ≫ Xo.s = spMap β' ≫ spMap (IntermediateField.inclusion c.le).toRingHom :=
    hf.trans (Spec.map_comp (CommRingCat.ofHom _) (CommRingCat.ofHom β'))
  refine ⟨K', hfd, pullback.lift f _ hκ, T'.t, ⟨m⟩, ?_⟩
  rw [pullback.lift_fst]
  exact ⟨n.toSABMap⟩

end PositivityTheory.HtPt.Kftwo
end
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.KftwoHost
section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.KftwoHostA
noncomputable section

open NumberField

namespace PositivityTheory.HtPt.Kftwo

structure Biq (F : Type) [Field F] [CharZero F] (m : ℕ) where

  w : F

  i : F
  w_sq : w * w = w - m
  i_sq : i * i = -1
  span : ∀ x : F, ∃ a b c e : ℚ, x = a + b * w + c * i + e * (w * i)
  indep : ∀ a b c e : ℚ, (a : F) + b * w + c * i + e * (w * i) = 0 → a = 0 ∧ b = 0 ∧ c = 0 ∧ e = 0

  σ : F →+* F

  τ : F →+* F
  σw : σ w = w
  σi : σ i = -i
  τw : τ w = 1 - w
  τi : τ i = i

section Exists

variable (m : ℕ)

abbrev Q1 : Type := QuadraticAlgebra ℚ (-(m : ℚ)) 1

abbrev Q2 : Type := QuadraticAlgebra (Q1 m) (-1) 0

attribute [local simp] QuadraticAlgebra.re_one QuadraticAlgebra.im_one

theorem fact1 (hm : 0 < m) : ∀ r : ℚ, r ^ 2 ≠ -(m : ℚ) + 1 * r := fun r h => by
  have : (1 : ℚ) ≤ m := by exact_mod_cast hm
  nlinarith [sq_nonneg (r - 1 / 2)]

theorem fact2 (hp : (4 * m - 1).Prime) (r : Q1 m) : r ^ 2 ≠ -1 + 0 * r := fun h => by
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · simp [Nat.not_prime_zero] at hp
    · exact h
  have h1 := congrArg QuadraticAlgebra.re h
  have h2 := congrArg QuadraticAlgebra.im h
  simp [pow_two] at h1 h2
  have hb : r.im ≠ 0 := fun h0 => by
    rw [h0] at h1
    nlinarith [sq_nonneg r.re]
  have ha : r.im = -2 * r.re := by
    have : r.im * (r.im + 2 * r.re) = 0 := by linear_combination h2
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hb
    · linear_combination h
  have hr : r.re ≠ 0 := fun h0 => hb (by rw [ha, h0, mul_zero])
  have hd : ((4 * m - 1 : ℕ) : ℚ) = (1 / r.re) * (1 / r.re) := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    field_simp
    rw [ha] at h1
    linear_combination -h1
  have hs : IsSquare ((4 * m - 1 : ℕ) : ℚ) := ⟨_, hd⟩
  exact hp.not_isSquare (Rat.isSquare_natCast_iff.1 hs)

theorem exists_biq (hp : (4 * m - 1).Prime) :
    ∃ (F : Type) (_ : Field F) (_ : CharZero F), Nonempty (Biq F m) := by
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · simp [Nat.not_prime_zero] at hp
    · exact h
  have := Fact.mk (fact1 m hm)
  have := Fact.mk (fact2 m hp)
  have hc : ∀ a : ℚ, (a : (Q2 m)) = ⟨⟨a, 0⟩, 0⟩ := fun a => by
    have := map_ratCast ((algebraMap (Q1 m) (Q2 m)).comp (algebraMap ℚ (Q1 m))) a
    rw [← this]; rfl
  let τ : (Q2 m) →+* (Q2 m) :=
    { toFun := fun z => ⟨star z.re, star z.im⟩
      map_one' := by ext1 <;> simp
      map_zero' := by ext1 <;> simp
      map_add' := fun x y => by ext1 <;> simp
      map_mul' := fun x y => by ext1 <;> simp }
  refine ⟨(Q2 m), inferInstance, inferInstance, ⟨⟨⟨⟨0, 1⟩, 0⟩, ⟨0, 1⟩, ?_, ?_, fun x => ?_, fun a b c e h => ?_,
    starRingEnd (Q2 m), τ, ?_, ?_, ?_, ?_⟩⟩⟩
  · ext <;> simp
  · ext <;> simp
  · refine ⟨x.re.re, x.re.im, x.im.re, x.im.im, ?_⟩
    simp only [hc]
    ext <;> simp
  · simp only [hc] at h
    have h1 := congrArg (fun z : (Q2 m) => z.re.re) h
    have h2 := congrArg (fun z : (Q2 m) => z.re.im) h
    have h3 := congrArg (fun z : (Q2 m) => z.im.re) h
    have h4 := congrArg (fun z : (Q2 m) => z.im.im) h
    simp at h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  · rw [starRingEnd_apply]; ext <;> simp
  · rw [starRingEnd_apply]; ext <;> simp
  · ext <;> simp [τ]
  · ext <;> simp [τ]

end Exists

namespace Biq

variable {F : Type} [Field F] [CharZero F] {m : ℕ} (B : Biq F m)

theorem int_of_integral {q : ℚ} (h : IsIntegral ℤ (q : F)) : ∃ n : ℤ, q = n := by
  have h' : IsIntegral ℤ (algebraMap ℚ F q) := by simpa using h
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral (isIntegral_algebraMap_iff  |>.1 h')
  exact ⟨n, by simpa using hn.symm⟩

omit [CharZero F] in
theorem of_eq {x y : F} (h : IsIntegral ℤ x) (e : y = x) : IsIntegral ℤ y := e ▸ h

omit [CharZero F] in
theorem integral_map {x : F} (f : F →+* F) (h : IsIntegral ℤ x) : IsIntegral ℤ (f x) := h.map f.toIntAlgHom

omit [CharZero F] in
theorem integral_int (n : ℤ) : IsIntegral ℤ (n : F) := by
  simpa using isIntegral_algebraMap (R := ℤ) (A := F) (x := n)

theorem integral_w : IsIntegral ℤ B.w :=
  ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (m : ℤ), by monicity!, by
    simp [Polynomial.eval₂_add, Polynomial.eval₂_sub]; linear_combination B.w_sq⟩

theorem integral_i : IsIntegral ℤ B.i :=
  ⟨Polynomial.X ^ 2 + 1, by monicity!, by simp; linear_combination B.i_sq⟩

theorem gauss {u v : ℚ} (h : IsIntegral ℤ ((u : F) + v * B.i)) : (∃ n : ℤ, u = n) ∧ ∃ n : ℤ, v = n := by
  have h' := integral_map B.σ h
  simp only [map_add (f := _), map_mul, map_ratCast, B.σi] at h'
  obtain ⟨p, hp⟩ := int_of_integral (F := F) (q := 2 * u) (by
    refine of_eq (h.add h') ?_; push_cast; ring)
  obtain ⟨q, hq⟩ := int_of_integral (F := F) (q := 2 * v) (by
    refine of_eq ((h'.sub h).mul B.integral_i) ?_; push_cast; linear_combination (2 * v : F) * B.i_sq)
  obtain ⟨n, hn⟩ := int_of_integral (F := F) (q := u ^ 2 + v ^ 2) (by
    refine of_eq (h.mul h') ?_; push_cast; linear_combination (v : F) ^ 2 * B.i_sq)
  have e : p ^ 2 + q ^ 2 = 4 * n := by
    have : (p : ℚ) ^ 2 + q ^ 2 = 4 * n := by rw [← hp, ← hq, ← hn]; ring
    exact_mod_cast this
  have hpq : Even p ∧ Even q := by
    rcases Int.even_or_odd' p with ⟨s, rfl | rfl⟩ <;> rcases Int.even_or_odd' q with ⟨t, rfl | rfl⟩
    · simp
    · exfalso; have : 4 * (s ^ 2 + t ^ 2 + t - n) + 1 = 0 := by linear_combination e
      omega
    · exfalso; have : 4 * (s ^ 2 + t ^ 2 + s - n) + 1 = 0 := by linear_combination e
      omega
    · exfalso; have : 4 * (s ^ 2 + t ^ 2 + s + t - n) + 2 = 0 := by linear_combination e
      omega
  obtain ⟨⟨s, rfl⟩, ⟨t, rfl⟩⟩ := hpq
  push_cast at hp hq
  exact ⟨⟨s, by linarith⟩, t, by linarith⟩

theorem quad {d : ℕ} (hd : d + 1 = 4 * m) (hp : d.Prime) {a b : ℚ} {r s : ℤ} (hr : d * a = r) (hs : d * b = s)
    (h : IsIntegral ℤ ((a : F) + b * B.w)) : (∃ n : ℤ, a = n) ∧ ∃ n : ℤ, b = n := by
  have h' := integral_map B.τ h
  simp only [map_add (f := _), map_mul, map_ratCast, B.τw] at h'
  obtain ⟨p, hp'⟩ := int_of_integral (F := F) (q := 2 * a + b) (by
    refine of_eq (h.add h') ?_; push_cast; ring)
  obtain ⟨n, hn⟩ := int_of_integral (F := F) (q := a ^ 2 + a * b + m * b ^ 2) (by
    refine of_eq (h.mul h') ?_; push_cast; linear_combination (b : F) ^ 2 * B.w_sq)
  have hdq : (d : ℚ) + 1 = 4 * m := by exact_mod_cast hd
  have e : s ^ 2 = d * (4 * n - p ^ 2) := by
    have : (s : ℚ) ^ 2 = d * (4 * n - p ^ 2) := by
      rw [← hs, ← hn, ← hp']; linear_combination (d * b ^ 2 : ℚ) * hdq
    exact_mod_cast this
  obtain ⟨t, rfl⟩ : (d : ℤ) ∣ s := (Nat.prime_iff_prime_int.1 hp).dvd_of_dvd_pow ⟨_, e⟩
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hb : b = t := by push_cast at hs; exact mul_left_cancel₀ hd0 hs
  refine ⟨⟨2 * m * (p - t) - r, ?_⟩, t, hb⟩
  push_cast
  rw [← hp', ← hr, ← hb]
  linear_combination a * hdq

theorem coords {d : ℕ} (hd : d + 1 = 4 * m) (hp : d.Prime) {x : F} (h : IsIntegral ℤ x) :
    ∃ a b c e : ℤ, x = a + b * B.w + c * B.i + e * (B.w * B.i) := by
  obtain ⟨a, b, c, e, rfl⟩ := B.span x
  have hdF : (d : F) = 4 * m - 1 := by
    have : (d : F) + 1 = 4 * m := by exact_mod_cast hd
    linear_combination this
  have h1 := integral_map B.τ h
  have h2 := integral_map B.σ h
  simp only [map_add (f := _), map_mul, map_ratCast, B.τw, B.τi, B.σw, B.σi] at h1 h2
  have hw := B.integral_w
  have hi := B.integral_i
  obtain ⟨⟨b', hb⟩, e', he⟩ := B.gauss (u := d * b) (v := d * e) (by
    refine of_eq ((h1.sub h).mul ((hw.add hw).sub isIntegral_one)) ?_
    push_cast; rw [hdF]; linear_combination (4 * (b + e * B.i) : F) * B.w_sq)
  have hbF : (b' : F) = d * b := by exact_mod_cast congrArg (fun q : ℚ => (q : F)) hb.symm
  have heF : (e' : F) = d * e := by exact_mod_cast congrArg (fun q : ℚ => (q : F)) he.symm
  obtain ⟨⟨a', ha⟩, c', hc⟩ := B.gauss (u := d * a) (v := d * c) (by
    refine of_eq ((((integral_int (d : ℤ)).mul h).sub ((integral_int b').mul hw)).sub
      ((integral_int e').mul (hw.mul hi))) ?_
    push_cast; rw [hbF, heF]; ring)
  have haF : (a' : F) = d * a := by exact_mod_cast congrArg (fun q : ℚ => (q : F)) ha.symm
  have hα : IsIntegral ℤ ((a : F) + b * B.w) := by
    refine of_eq (((integral_int (2 * m : ℤ)).mul (h.add h2)).sub ((integral_int a').add ((integral_int b').mul hw))) ?_
    push_cast; rw [haF, hbF, hdF]; ring
  have hβ : IsIntegral ℤ ((c : F) + e * B.w) := by
    refine of_eq ((hα.sub h).mul hi) ?_
    linear_combination (c + e * B.w : F) * B.i_sq
  obtain ⟨⟨a, rfl⟩, b, rfl⟩ := B.quad hd hp ha hb hα
  obtain ⟨⟨c, rfl⟩, e, rfl⟩ := B.quad hd hp hc he hβ
  exact ⟨a, b, c, e, by simp⟩

include B in
theorem numberField : NumberField F := by
  classical
  have : Module.Finite ℚ F := by
    refine ⟨⟨{1, B.w, B.i, B.w * B.i}, eq_top_iff.2 fun x _ => ?_⟩⟩
    obtain ⟨a, b, c, e, rfl⟩ := B.span x
    have k : ∀ (q : ℚ) (y : F), y ∈ ({1, B.w, B.i, B.w * B.i} : Finset F) →
        (q : F) * y ∈ Submodule.span ℚ (({1, B.w, B.i, B.w * B.i} : Finset F) : Set F) := fun q y hy => by
      rw [← Rat.smul_def]
      exact Submodule.smul_mem _ _ (Submodule.subset_span hy)
    refine add_mem (add_mem (add_mem ?_ (k _ _ (by simp))) (k _ _ (by simp))) (k _ _ (by simp))
    simpa using k a 1 (by simp)
  exact {}

theorem conj_w (hm : 0 < m) (φ : F →+* ℂ) : starRingEnd ℂ (φ B.w) = 1 - φ B.w := by
  have h := congrArg φ B.w_sq
  simp only [map_mul, map_sub, map_natCast] at h
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp at h1 h2
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hv : (φ B.w).im ≠ 0 := fun h0 => by
    rw [h0] at h1
    nlinarith [sq_nonneg ((φ B.w).re - 1 / 2)]
  have : (φ B.w).im * (2 * (φ B.w).re - 1) = 0 := by linear_combination h2
  have hu := (mul_eq_zero.1 this).resolve_left hv
  apply Complex.ext <;> simp
  linarith

theorem conj_i (φ : F →+* ℂ) : starRingEnd ℂ (φ B.i) = -φ B.i := by
  have h := congrArg φ B.i_sq
  simp only [map_mul, map_neg, map_one] at h
  have : (φ B.i - Complex.I) * (φ B.i + Complex.I) = 0 := by linear_combination h - Complex.I_mul_I
  rcases mul_eq_zero.1 this with h | h
  · rw [sub_eq_zero.1 h, Complex.conj_I]
  · rw [eq_neg_of_add_eq_zero_left h, map_neg, Complex.conj_I]

theorem conj_eq (hm : 0 < m) (φ : F →+* ℂ) (x : F) : φ (B.σ (B.τ x)) = starRingEnd ℂ (φ x) := by
  obtain ⟨a, b, c, e, rfl⟩ := B.span x
  simp only [map_add (f := _), map_mul, map_ratCast, B.τw, B.τi, B.σw, B.σi, map_sub, map_one, map_neg, B.conj_w hm, B.conj_i]

theorem mem_real (hm : 0 < m) {x : F} (h : B.σ (B.τ x) = x) : x ∈ maximalRealSubfield F := by
  rw [mem_maximalRealSubfield_iff]
  intro φ
  rw [RCLike.star_def, ← B.conj_eq hm, h]

theorem i_ne_zero : B.i ≠ 0 := fun h => by simpa [h] using B.i_sq

include B in
theorem isCMField (hm : 0 < m) : IsCMField F := by
  have := B.numberField
  have hT : IsTotallyComplex F := ⟨fun v => by
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff]
    intro h
    have h1 := RingHom.congr_fun h B.i
    rw [ComplexEmbedding.conjugate_coe_eq, B.conj_i] at h1
    exact B.i_ne_zero (v.embedding.injective (by rw [map_zero]; linear_combination (-1 / 2 : ℂ) * h1))⟩
  have hc : ∀ x, B.σ (B.τ (B.σ (B.τ x))) = x := fun x => by
    obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
    apply φ.injective
    rw [B.conj_eq hm, B.conj_eq hm, Complex.conj_conj]
  have hli : LinearIndependent (maximalRealSubfield F) ![(1 : F), B.i] := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
    have h0 : (s : F) + t * B.i = 0 := by simpa [Subfield.smul_def] using h
    have h1 := congrArg φ h0
    have h2 := congrArg (starRingEnd ℂ) h1
    have hs := (mem_maximalRealSubfield_iff _).1 s.2 φ
    have ht := (mem_maximalRealSubfield_iff _).1 t.2 φ
    rw [RCLike.star_def] at hs ht
    simp only [map_add (f := _), map_mul, map_zero, hs, ht, B.conj_i] at h1 h2
    have e1 : (s : F) = 0 := φ.injective (by rw [map_zero]; linear_combination (1 / 2 : ℂ) * (h1 + h2))
    rw [e1, zero_add] at h0
    exact ⟨Subtype.ext e1, Subtype.ext ((mul_eq_zero.1 h0).resolve_right B.i_ne_zero)⟩
  have hsp : ⊤ ≤ Submodule.span (maximalRealSubfield F) (Set.range ![(1 : F), B.i]) := fun x _ => by
    rw [Matrix.range_cons_cons_empty, Submodule.mem_span_pair]
    refine ⟨⟨(x + B.σ (B.τ x)) / 2, B.mem_real hm ?_⟩, ⟨(B.σ (B.τ x) - x) * B.i / 2, B.mem_real hm ?_⟩, ?_⟩
    · simp only [map_div₀, map_add (f := _), map_ofNat, hc]; ring
    · simp only [map_div₀, map_sub, map_mul, map_ofNat, hc, B.τi, B.σi]; ring
    · simp only [Subfield.smul_def, smul_eq_mul]
      linear_combination ((B.σ (B.τ x) - x) / 2) * B.i_sq
  have : Algebra.IsQuadraticExtension (maximalRealSubfield F) F :=
    { finrank_eq_two' := by simpa using Module.finrank_eq_card_basis (Module.Basis.mk hli hsp) }
  exact {}

end Biq

end PositivityTheory.HtPt.Kftwo
end
end

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace PositivityTheory.HtPt.Kftwo

namespace Biq

variable {F : Type} [Field F] [NumberField F] {m : ℕ} (B : Biq F m)

def W : 𝓞 F := ⟨B.w, B.integral_w⟩

def J : 𝓞 F := ⟨B.i, B.integral_i⟩

def mk4 (v : ℤ × ℤ × ℤ × ℤ) : 𝓞 F := v.1 + v.2.1 * B.W + v.2.2.1 * B.J + v.2.2.2 * (B.W * B.J)

theorem coe_W : algebraMap (𝓞 F) F B.W = B.w := rfl
theorem coe_J : algebraMap (𝓞 F) F B.J = B.i := rfl

theorem W_sq : B.W * B.W = B.W - m := RingOfIntegers.ext (by
  simpa only [RingOfIntegers.coe_eq_algebraMap, map_mul, map_sub, map_natCast, coe_W] using B.w_sq)

theorem J_sq : B.J * B.J = -1 := RingOfIntegers.ext (by
  simpa only [RingOfIntegers.coe_eq_algebraMap, map_mul, map_neg, map_one, coe_J] using B.i_sq)

theorem coe_mk_quad (v : ℤ × ℤ × ℤ × ℤ) : algebraMap (𝓞 F) F (B.mk4 v) =
    v.1 + v.2.1 * B.w + v.2.2.1 * B.i + v.2.2.2 * (B.w * B.i) := by
  simp only [mk4, map_add (f := _), map_mul, map_intCast, coe_W, coe_J]

theorem mk_quad_injective : Function.Injective B.mk4 := fun v v' h => by
  have h' := congrArg (algebraMap (𝓞 F) F) h
  rw [coe_mk_quad, coe_mk_quad] at h'
  obtain ⟨h1, h2, h3, h4⟩ := B.indep (v.1 - v'.1) (v.2.1 - v'.2.1) (v.2.2.1 - v'.2.2.1) (v.2.2.2 - v'.2.2.2) (by
    push_cast; linear_combination h')
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · exact_mod_cast sub_eq_zero.1 h1
  · exact_mod_cast sub_eq_zero.1 h2
  · exact_mod_cast sub_eq_zero.1 h3
  · exact_mod_cast sub_eq_zero.1 h4

theorem mk_quad_surjective {d : ℕ} (hd : d + 1 = 4 * m) (hp : d.Prime) : Function.Surjective B.mk4 := fun x => by
  obtain ⟨a, b, c, e, h⟩ := B.coords hd hp x.isIntegral_coe
  exact ⟨(a, b, c, e), RingOfIntegers.ext (by rw [RingOfIntegers.coe_eq_algebraMap, coe_mk_quad]; exact h.symm)⟩

theorem σ_σ (x : F) : B.σ (B.σ x) = x := by
  obtain ⟨a, b, c, e, rfl⟩ := B.span x
  simp only [map_add (f := _), map_mul, map_ratCast, B.σw, B.σi, map_neg, neg_neg]

def σO : 𝓞 F ≃+* 𝓞 F :=
  RingOfIntegers.mapRingEquiv (RingEquiv.ofRingHom B.σ B.σ (RingHom.ext B.σ_σ) (RingHom.ext B.σ_σ))

theorem sigma_W : B.σO B.W = B.W := RingOfIntegers.ext B.σw

theorem σO_J : B.σO B.J = -B.J := RingOfIntegers.ext B.σi

variable [IsCMField F]

theorem complexConj_eq (hm : 0 < m) (x : F) : IsCMField.complexConj F x = B.σ (B.τ x) := by
  obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
  apply φ.injective
  rw [IsCMField.complexEmbedding_complexConj, B.conj_eq hm]

include B in
theorem unramified {d : ℕ} (hd : d + 1 = 4 * m) (hp : d.Prime) :
    Algebra.Unramified (𝓞 (maximalRealSubfield F)) (𝓞 F) := by
  have hm : 0 < m := by omega
  let R := 𝓞 (maximalRealSubfield F)
  let δ := KaehlerDifferential.D R (𝓞 F)
  have h1 : (2 * B.J) • δ B.J = 0 := by
    have := congrArg δ B.J_sq
    rw [Derivation.leibniz, map_neg, Derivation.map_one_eq_zero, neg_zero] at this
    rw [two_mul, add_smul, this]
  have h2 : (2 * B.W - 1) • δ B.W = 0 := by
    have := congrArg δ B.W_sq
    rw [Derivation.leibniz, map_sub, Derivation.map_natCast, sub_zero] at this
    rw [two_mul, sub_smul, add_smul, this, one_smul, sub_self]
  have h3 : δ (B.J * (B.W + B.W - 1)) = 0 := by
    obtain ⟨r, hr⟩ := (IsCMField.ringOfIntegersComplexConj_eq_self_iff F (B.J * (B.W + B.W - 1))).1
      (RingOfIntegers.ext (by
        rw [IsCMField.coe_ringOfIntegersComplexConj, B.complexConj_eq hm]
        simp only [RingOfIntegers.coe_eq_algebraMap, map_mul, map_sub, map_add (f := _), map_one, coe_W, coe_J, B.τi, B.τw,
          B.σi, B.σw]
        ring))
    rw [← hr, Derivation.map_algebraMap]
  rw [Derivation.leibniz, map_sub, map_add (f := _), Derivation.map_one_eq_zero, sub_zero] at h3
  have hJ : δ B.J = 0 := by
    have e : (1 : 𝓞 F) = -(2 * m * B.J) * (2 * B.J) + (2 * B.W - 1) * (B.W + B.W - 1) := by
      linear_combination (4 * m : 𝓞 F) * B.J_sq - 4 * B.W_sq
    have e2 : (2 * B.W - 1) • ((B.W + B.W - 1) • δ B.J) = 0 := by
      rw [eq_neg_of_add_eq_zero_right h3, smul_neg, smul_comm, smul_add, h2, add_zero, smul_zero, neg_zero]
    rw [← one_smul (𝓞 F) (δ B.J), e, add_smul, mul_smul, mul_smul (2 * B.W - 1), h1, e2, smul_zero, add_zero]
  have hW : δ B.W = 0 := by
    rw [hJ, smul_zero, add_zero, ← two_smul (𝓞 F), smul_smul] at h3
    have e : (1 : 𝓞 F) = -(2 * m * B.J) * (B.J * 2) + (2 * B.W - 1) * (2 * B.W - 1) := by
      linear_combination (4 * m : 𝓞 F) * B.J_sq - 4 * B.W_sq
    rw [← one_smul (𝓞 F) (δ B.W), e, add_smul, mul_smul, mul_smul (2 * B.W - 1), h3, h2, smul_zero, smul_zero, add_zero]
  have hall : ∀ x, δ x = 0 := fun x => by
    obtain ⟨v, rfl⟩ := B.mk_quad_surjective hd hp x
    simp only [mk4, map_add (f := _), Derivation.leibniz, hW, hJ, Derivation.map_intCast, smul_zero, add_zero]
  have hs : Subsingleton (Ω[𝓞 F⁄R]) := by
    rw [← Submodule.subsingleton_iff (𝓞 F), ← subsingleton_iff_bot_eq_top, eq_comm,
      ← KaehlerDifferential.span_range_derivation, Submodule.span_eq_bot]
    rintro _ ⟨x, rfl⟩
    exact hall x
  have : Algebra.FormallyUnramified R (𝓞 F) := ⟨hs⟩
  have : Algebra.FiniteType R (𝓞 F) := Algebra.FiniteType.of_restrictScalars_finiteType ℤ R (𝓞 F)
  exact {}

end Biq

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def mat (w : 𝓞 E) (v : ℤ × ℤ × ℤ × ℤ) : Matrix (Fin 2) (Fin 2) (𝓞 E) :=
  !![v.1 + v.2.1 * w, -(v.2.2.1 + v.2.2.2 * w); v.2.2.1 + v.2.2.2 * w, v.1 + v.2.1 * w]


set_option maxHeartbeats 1600000 in
theorem exists_pairHost {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    ∃ (E' : Type) (_ : Field E') (_ : NumberField E') (_ : IsCMField E') (H' : Host E'), Nonempty (PairHost H H') := by
  obtain ⟨m, hd⟩ : ∃ m, H.d + 1 = 4 * m := ⟨(H.d + 1) / 4, by have := H.d_mod; omega⟩
  have hm : 0 < m := by omega
  obtain ⟨F, _, _, ⟨B⟩⟩ := exists_biq m (by rw [show 4 * m - 1 = H.d by omega]; exact H.d_prime)
  have := B.numberField
  have := B.isCMField hm
  have hdO : (H.d : 𝓞 F) + 1 = 4 * m := by exact_mod_cast hd
  let H' : Host F :=
    { d := H.d, d_mod := H.d_mod, d_prime := H.d_prime, rt := 2 * B.W - 1
      rt_sq := by linear_combination 4 * B.W_sq + hdO
      w0 := B.W, two_weight_eq_one_add_root := by ring
      bar := (IsCMField.ringOfIntegersComplexConj F).toRingEquiv
      bar_eq := fun _ => rfl
      unram := B.unramified hd H.d_prime
      rt0 := H.rt0, sqrt_neg_disc_sq := H.sqrt_neg_disc_sq }
  have hbW : H'.bar B.W = 1 - B.W := GlobalTheory.HostModel.cmHost_bar_halfIntegerGenerator H'
  have hbJ : H'.bar B.J = -B.J := RingOfIntegers.ext (by
    rw [H'.bar_eq, B.complexConj_eq hm]
    show B.σ (B.τ B.i) = -B.i
    rw [B.τi, B.σi])
  have hw : H.w0 * H.w0 = H.w0 - m := by
    have hdE : (H.d : 𝓞 E) + 1 = 4 * m := by exact_mod_cast hd
    have h1 := H.rt_sq
    rw [GlobalTheory.HostModel.rt_eq] at h1
    have : (4 : 𝓞 E) * (H.w0 * H.w0 - (H.w0 - m)) = 0 := by linear_combination h1 - hdE
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left (by norm_num))
  let e := Equiv.ofBijective B.mk4 ⟨B.mk_quad_injective, B.mk_quad_surjective hd H.d_prime⟩
  have he : ∀ (x : 𝓞 F) v, x = B.mk4 v → mat H.w0 (e.symm x) = mat H.w0 v := by
    rintro _ v rfl
    rw [show e.symm (B.mk4 v) = v from e.symm_apply_apply v]
  let ψ : 𝓞 F →+* Matrix (Fin 2) (Fin 2) (𝓞 E) :=
    { toFun := fun x => mat H.w0 (e.symm x)
      map_one' := by
        rw [he 1 (1, 0, 0, 0) (by simp [Biq.mk4])]
        ext1 i j; fin_cases i <;> fin_cases j <;> simp [mat]
      map_zero' := by
        rw [he 0 (0, 0, 0, 0) (by simp [Biq.mk4])]
        ext1 i j; fin_cases i <;> fin_cases j <;> simp [mat]
      map_add' := fun x y => by
        obtain ⟨⟨a, b, c, f⟩, rfl⟩ := B.mk_quad_surjective hd H.d_prime x
        obtain ⟨⟨a', b', c', f'⟩, rfl⟩ := B.mk_quad_surjective hd H.d_prime y
        rw [he _ _ rfl, he _ _ rfl, he _ (a + a', b + b', c + c', f + f') (by simp only [Biq.mk4]; push_cast; ring)]
        ext1 i j; fin_cases i <;> fin_cases j <;> simp [mat] <;> ring
      map_mul' := fun x y => by
        obtain ⟨⟨a, b, c, f⟩, rfl⟩ := B.mk_quad_surjective hd H.d_prime x
        obtain ⟨⟨a', b', c', f'⟩, rfl⟩ := B.mk_quad_surjective hd H.d_prime y
        rw [he _ _ rfl, he _ _ rfl, he _ (a * a' - m * b * b' - c * c' + m * f * f',
          a * b' + b * a' + b * b' - c * f' - f * c' - f * f', a * c' + c * a' - m * b * f' - m * f * b',
          a * f' + b * c' + b * f' + c * b' + f * a' + f * b') (by
            simp only [Biq.mk4]; push_cast
            linear_combination ((b * b' + (b * f' + f * b') * B.J - f * f' : 𝓞 F)) * B.W_sq +
              ((c + f * B.W) * (c' + f' * B.W) : 𝓞 F) * B.J_sq)]
        ext1 i j
        fin_cases i <;> fin_cases j <;> simp [mat, Matrix.mul_apply, Fin.sum_univ_two]
        · linear_combination (f * f' - b * b' : 𝓞 E) * hw
        · linear_combination (b * f' + f * b' : 𝓞 E) * hw
        · linear_combination (-(b * f' + f * b') : 𝓞 E) * hw
        · linear_combination (f * f' - b * b' : 𝓞 E) * hw }
  have hψ : ∀ (x : 𝓞 F) v, x = B.mk4 v → ψ x = mat H.w0 v := he
  clear_value ψ
  refine ⟨F, inferInstance, inferInstance, inferInstance, H', ⟨⟨ψ, B.σO, fun x i j => ?_, ?_, fun x => ?_, ?_,
    fun k _ _ τ τ' h => ?_⟩⟩⟩
  · obtain ⟨⟨a, b, c, f⟩, rfl⟩ := B.mk_quad_surjective hd H.d_prime x
    rw [hψ _ _ rfl, hψ _ (a + b, -b, -c - f, f) (by
      simp only [Biq.mk4, map_add (f := _), map_mul, map_intCast, hbW, hbJ]; push_cast; ring)]
    fin_cases i <;> fin_cases j <;> simp [mat] <;> ring
  · rw [hψ _ (0, 1, 0, 0) (by simp [Biq.mk4, H'])]
    ext1 i j; fin_cases i <;> fin_cases j <;> simp [mat]
  · obtain ⟨⟨a, b, c, f⟩, rfl⟩ := B.mk_quad_surjective hd H.d_prime x
    rw [hψ _ _ rfl, hψ _ (a, b, -c, -f) (by
      simp only [Biq.mk4, map_add (f := _), map_mul, map_intCast, B.sigma_W, B.σO_J]; push_cast; ring)]
    ext1 i j
    fin_cases i <;> fin_cases j <;> simp [mat, Matrix.mul_diagonal, Matrix.diagonal_mul] <;> ring
  · show B.σO (2 * B.W - 1) = 2 * B.W - 1
    rw [map_sub, map_mul, map_ofNat, map_one, B.sigma_W]
  · have hW : τ' B.W = τ B.W := by
      change τ (2 * B.W - 1) = τ' (2 * B.W - 1) at h
      simp only [map_sub, map_mul, map_ofNat, map_one] at h
      linear_combination (-1 / 2 : k) * h
    have h1 := congrArg τ B.J_sq
    have h2 := congrArg τ' B.J_sq
    simp only [map_mul, map_neg, map_one] at h1 h2
    have : (τ' B.J - τ B.J) * (τ' B.J + τ B.J) = 0 := by linear_combination h2 - h1
    rcases mul_eq_zero.1 this with h3 | h3
    · refine Or.inl (RingHom.ext fun x => ?_)
      obtain ⟨v, rfl⟩ := B.mk_quad_surjective hd H.d_prime x
      simp only [Biq.mk4, map_add (f := _), map_mul, map_intCast, hW, sub_eq_zero.1 h3]
    · refine Or.inr (RingHom.ext fun x => ?_)
      obtain ⟨v, rfl⟩ := B.mk_quad_surjective hd H.d_prime x
      show _ = τ (B.σO _)
      simp only [Biq.mk4, map_add (f := _), map_mul, map_intCast, hW, eq_neg_of_add_eq_zero_left h3, B.sigma_W, B.σO_J, map_neg]

end PositivityTheory.HtPt.Kftwo
end
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.KftwoExt
noncomputable section

open IsLocalRing Formalism.L2.Pj

namespace PositivityTheory.HtPt.Kftwo

theorem exists_completion (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CharZero W] :
    ∃ (T : CDVR) (g : W →+* T.V), IsLocalHom g ∧ Function.Injective g := by
  obtain ⟨⟨hdom, hdvr⟩, hcpl, hinj, hloc, -⟩ := ReciprocityTheory.CA.Pt.completionDVR W
  haveI : CharZero (AdicCompletion (maximalIdeal W) W) := charZero_of_injective_algebraMap hinj
  exact ⟨CDVR.mk (AdicCompletion (maximalIdeal W) W),
    algebraMap W (AdicCompletion (maximalIdeal W) W), hloc, hinj⟩

theorem exists_cdvr_of_isIntegral {V A : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing A]
    [IsDedekindDomain A] [CharZero A] [Algebra V A] [Algebra.IsIntegral V A] (hinj : Function.Injective (algebraMap V A)) :
    ∃ (T : CDVR) (g : A →+* T.V), IsLocalHom (g.comp (algebraMap V A)) ∧ Function.Injective g := by
  have hker : RingHom.ker (algebraMap V A) ≤ maximalIdeal V := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]
    exact bot_le
  obtain ⟨P, hPmax, hPc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (maximalIdeal V) hker
  haveI : P.IsPrime := hPmax.isPrime
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    apply IsDiscreteValuationRing.not_a_field V
    rw [← hPc, Ideal.under_def, ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).mp hinj]
  haveI : IsDomain (Localization.AtPrime P) :=
    IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors P)
  haveI : IsDiscreteValuationRing (Localization.AtPrime P) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hP0 (Localization.AtPrime P)
  have hAinj : Function.Injective (algebraMap A (Localization.AtPrime P)) :=
    IsLocalization.injective (Localization.AtPrime P) (Ideal.primeCompl_le_nonZeroDivisors P)
  haveI : CharZero (Localization.AtPrime P) := charZero_of_injective_algebraMap hAinj
  obtain ⟨T, g0, hg0, hg0inj⟩ := exists_completion (Localization.AtPrime P)
  refine ⟨T, g0.comp (algebraMap A (Localization.AtPrime P)), ⟨fun x hx => ?_⟩, hg0inj.comp hAinj⟩
  simp only [RingHom.comp_apply] at hx
  have h1 : IsUnit (algebraMap A (Localization.AtPrime P) (algebraMap V A x)) := isUnit_of_map_unit g0 _ hx
  rw [IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime P) P] at h1
  by_contra hxu
  have hx' : x ∈ maximalIdeal V := hxu
  rw [← hPc] at hx'
  exact h1 (Ideal.mem_comap.mp hx')

theorem exists_cdvr {V K K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [CharZero K]
    [Algebra V K] [IsFractionRing V K] [Field K'] [Algebra K K'] [FiniteDimensional K K'] :
    ∃ (T : CDVR) (g : V →+* T.V) (j : K' →+* T.Fr), IsLocalHom g ∧
      (algebraMap T.V T.Fr).comp g = (j.comp (algebraMap K K')).comp (algebraMap V K) := by
  letI : Algebra V K' := ((algebraMap K K').comp (algebraMap V K)).toAlgebra
  haveI : IsScalarTower V K K' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : CharZero K' := charZero_of_injective_algebraMap (algebraMap K K').injective
  haveI : IsDedekindDomain (integralClosure V K') := integralClosure.isDedekindDomain V K K'
  haveI : IsFractionRing (integralClosure V K') K' :=
    integralClosure.isFractionRing_of_finite_extension K K'
  haveI : CharZero (integralClosure V K') :=
    ⟨fun m n h => Nat.cast_injective (R := K')
      (by simpa using congrArg (algebraMap (integralClosure V K') K') h)⟩
  have hVK' : Function.Injective (algebraMap V K') :=
    (algebraMap K K').injective.comp (IsFractionRing.injective V K)
  have hinj : Function.Injective (algebraMap V (integralClosure V K')) := by
    refine Function.Injective.of_comp (f := algebraMap (integralClosure V K') K') ?_
    rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq]
    exact hVK'
  obtain ⟨T, g, hg, hginj⟩ := exists_cdvr_of_isIntegral hinj
  have hjinj : Function.Injective ((algebraMap T.V T.Fr).comp g) :=
    (IsFractionRing.injective T.V T.Fr).comp hginj
  refine ⟨T, g.comp (algebraMap V (integralClosure V K')),
    IsFractionRing.lift (K := K') hjinj, hg, ?_⟩
  ext x
  simp only [RingHom.comp_apply]
  rw [← IsScalarTower.algebraMap_apply V K K',
    IsScalarTower.algebraMap_apply V (integralClosure V K') K', IsFractionRing.lift_algebraMap]
  rfl

end PositivityTheory.HtPt.Kftwo
end
end

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace PositivityTheory.HtPt.Kftwo

section Unit

open GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels GlobalTheory.KeyUnitModels Formalism.L2.Pj

theorem lieMult_comp {O : Type} [CommRing O] {S : Scheme.{0}} {G : Over S} [GrpObj G] (act : OAct O G) (σ : O ≃+* O)
    (s : G ≅ G) [IsMonHom s.hom] (hs : ∀ a, act.act (σ a) ≫ s.hom = s.hom ≫ act.act a) {k : Type} [Field k]
    (z : Sp k ⟶ S) (τ : O →+* k) (n : ℕ) (h : LieMult act z τ n) : LieMult act z (τ.comp σ.toRingHom) n := by
  have e := GlobalTheory.LiePull.lieMult_pull O S S G G (𝟙 S) s.hom.left act (GlobalTheory.Serre.comapAct act σ.toRingHom)
    (isGrpPullback_of_iso s) (fun c => congrArg (fun q => q.left) (hs c)) k z (τ.comp σ.toRingHom) n
  rw [Category.comp_id] at e
  refine e.1 ?_
  have key : ∀ v, IsLieEigen (GlobalTheory.Serre.comapAct act σ.toRingHom) z (τ.comp σ.toRingHom) v ↔ IsLieEigen act z τ v :=
    fun v => and_congr_right fun _ => ⟨fun hv a => by
      obtain ⟨b, rfl⟩ := σ.surjective a
      exact hv b, fun hv a => hv (σ a)⟩
  obtain ⟨v, h₁, h₂⟩ := h
  exact ⟨v, fun i => (key _).2 (h₁ i), fun w hw => h₂ w ((key _).1 hw)⟩

variable {E E' : Type} [Field E] [NumberField E] [IsCMField E] [Field E'] [NumberField E'] [IsCMField E']
  {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {H' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E'}

theorem exists_type (Q : PairHost H H') {V Ω : Type} [CommRing V] [Field Ω] [IsAlgClosed Ω] [CharZero Ω] (f : V →+* Ω)
    (T : SAB H' (Sp V)) (s : T.G ≅ T.G) [IsMonHom s.hom] (hs : ∀ a, T.act.act (Q.σ a) ≫ s.hom = s.hom ≫ T.act.act a)
    {m : ℕ} {w : Fin m → (epsR V ⟶ T.G)} (hw : IsLieBasis w) :
    ∃ (ρ : Ω) (p q : ℕ), ρ ^ 2 = -(H'.d : Ω) ∧ ∀ τ : 𝓞 E' →+* Ω,
      (τ H'.rt = ρ → LieMult T.act (spMap f) τ p) ∧ (τ H'.rt ≠ ρ → LieMult T.act (spMap f) τ q) := by
  obtain ⟨M, hM⟩ := GlobalTheory.exists_lie_coordinates_lieMult_iff _ V T.G T.act m w T.semi.smooth hw
  obtain ⟨M', -, hM'⟩ := hM Ω f
  let τ₀ : 𝓞 E' →+* Ω := (IsAlgClosed.lift (R := ℚ) (S := E') (M := Ω)).toRingHom.comp (algebraMap (𝓞 E') E')
  let τ₁ : 𝓞 E' →+* Ω := τ₀.comp H'.bar.toRingHom
  have sq : ∀ τ : 𝓞 E' →+* Ω, τ H'.rt ^ 2 = -(H'.d : Ω) := fun τ => by rw [← map_pow, H'.rt_sq, map_neg, map_natCast]
  have h₁ : τ₁ H'.rt = -τ₀ H'.rt := by
    show τ₀ (H'.bar H'.rt) = _
    rw [GlobalTheory.HostModel.bar_rt, map_neg]
  have mv : ∀ (τ τ' : 𝓞 E' →+* Ω) (n : ℕ), τ H'.rt = τ' H'.rt → LieMult T.act (spMap f) τ n →
      LieMult T.act (spMap f) τ' n := fun τ τ' n e h => by
    rcases Q.chars Ω τ τ' e with rfl | rfl
    · exact h
    · exact lieMult_comp T.act Q.σ s hs _ τ n h
  refine ⟨τ₀ H'.rt, _, _, sq τ₀, fun τ => ⟨fun e => mv τ₀ τ _ e.symm ((hM' τ₀ _).2 rfl),
    fun e => mv τ₁ τ _ ?_ ((hM' τ₁ _).2 rfl)⟩⟩
  rw [h₁]
  exact ((sq_eq_sq_iff_eq_or_eq_neg.1 ((sq τ).trans (sq τ₀).symm)).resolve_left e).symm

theorem exists_pull {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) : ∃ t' : SAB H S', Nonempty (SABMap t' t f) := by
  obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull f t
  exact ⟨_, ⟨m⟩⟩

theorem key_isUnit {κ : KeyRule} (hκ : IsKeyRule κ) (hpow : ∀ (K : Type) [Field K] [CharZero K] (x y : KeyIn K) (j : ℕ),
      GlobalTheory.KeyPow.IsKeyPow y x j → κ K y = κ K x ^ j)
    {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [CharZero K] [Algebra V K]
    [IsFractionRing V K] (t : SAB H (Sp V)) (θ : t.PP.L.Sec) {n : ℕ} (w : Fin n → (epsR V ⟶ t.G)) (x : KeyIn K)
    (hx : IsFibreOf x t.G t.PP.L t.PP.rig θ w (algebraMap V K)) (hw : IsLieBasis w) (hθ : NonzeroClosed (X := t.G) θ) :
    ∃ u : Vˣ, (κ K x : K) = algebraMap V K u := by
  obtain ⟨E', _, _, _, H', ⟨Q⟩⟩ := exists_pairHost H
  obtain ⟨y, hy⟩ := GlobalTheory.KeyPow.exists_isKeyPow K x 2 (by norm_num)
  obtain ⟨T, s, θ₂, m, w₂, hs₁, hs₂, hw₂, hθ₂, hy₂⟩ := exists_square Q _ t θ w x y hx hw hθ hy
  let Ω := AlgebraicClosure K
  let i := algebraMap K Ω
  obtain ⟨ρ, p, q, hρ, hty⟩ := exists_type Q (i.comp (algebraMap V K)) T s hs₂ hw₂
  obtain ⟨tK, ⟨mK⟩⟩ := exists_pull (spMap (algebraMap V K)) T
  obtain ⟨TK, rfl, hgK⟩ := exists_pat_of_isFibreOf mK hy₂
  obtain ⟨tΩ, ⟨mΩ⟩⟩ := exists_pull (spMap i) TK.t
  obtain ⟨⟨TΩ, rfl, hgΩ⟩, hL⟩ := GlobalTheory.CM.PAT.exists_of_sabMap E' H' _ _ _ TK tΩ mΩ
  have lK : ∀ τ N, LieMult T.act (spMap (i.comp (algebraMap V K))) τ N → LieMult TK.t.act (spMap i) τ N := fun τ N h =>
    (GlobalTheory.LiePull.lieMult_pull _ _ _ _ _ _ _ T.act TK.t.act mK.cart mK.act Ω (spMap i) τ N).2 (by rwa [← spMap_comp])
  have lΩ : ∀ τ N, LieMult TK.t.act (spMap i) τ N → LieMult TΩ.t.act (𝟙 _) τ N := fun τ N h =>
    (GlobalTheory.LiePull.lieMult_pull _ _ _ _ _ _ _ TK.t.act TΩ.t.act mΩ.cart mΩ.act Ω (𝟙 _) τ N).2 (by rwa [Category.id_comp])
  obtain ⟨D, rfl, rfl, hpq, ⟨I⟩⟩ := exists_datum_tate TΩ (by rw [hgΩ, hgK]; exact y.g_pos) ρ hρ p q
    fun τ => ⟨fun e => lΩ _ _ (lK _ _ ((hty τ).1 e)), fun e => lΩ _ _ (lK _ _ ((hty τ).2 e))⟩
  obtain ⟨I', -⟩ := (GlobalTheory.PELDesc.tate_pull (D := D) TK.t.PP.isLB TΩ.t.PP.isLB mΩ.cart (LBIso.symm hL) TK.t.act.act
    TΩ.t.act.act mΩ.act (𝟙 _) (spMap i) (Category.id_comp _).symm).1 I
  obtain ⟨l, hA, hgood, -⟩ := GlobalTheory.exists_level_goodAt_all_primes_and_idx E' H' 1 one_pos
  obtain ⟨Xo⟩ := GlobalTheory.Moduli.moduli_scheme_exists E' H' D l hpq
  obtain ⟨K', _, z, t', ⟨m₁⟩, ⟨m₂⟩⟩ := exists_point hA Xo (GlobalTheory.LevelExist.minCoeff l) TK ρ hρ
    (fun τ => ⟨fun e => lK _ _ ((hty τ).1 e), fun e => lK _ _ ((hty τ).2 e)⟩) I'
  obtain ⟨T₀, g, j, _, hgj⟩ := exists_cdvr (V := V) (K := K) (K' := K')
  have : CharZero T₀.Fr := charZero_of_injective_algebraMap (IsFractionRing.injective T₀.V T₀.Fr)
  let j₀ : K →+* T₀.Fr := j.comp (algebraMap K K')
  obtain ⟨G, ⟨mG⟩⟩ := exists_pull (spMap g) T
  obtain ⟨t'', ⟨m₃⟩⟩ := exists_pull (spMap j) t'
  obtain ⟨n₁, -⟩ := sabComp pullCubComp E' H' _ _ _ _ _ _ _ _ m₂ m₃
  obtain ⟨n₂, -⟩ := sabComp pullCubComp E' H' _ _ _ _ _ _ _ _ m₁ m₃
  obtain ⟨n₃, -⟩ := sabComp pullCubComp E' H' _ _ _ _ _ _ _ _ mK n₂
  obtain ⟨n₄, -⟩ := sabCancel pullCubCancel E' H' _ _ _ T G t'' (spMap g) (spMap (algebraMap T₀.V T₀.Fr)) mG
    (PullbackSections.sabMapCast n₃ (by rw [← spMap_comp, ← spMap_comp, ← spMap_comp, hgj, RingHom.comp_assoc]))
  obtain ⟨y', hy'⟩ := GlobalTheory.KeyPow.exists_keyPB_ring y j₀
  have hf := isFibreOf_trans T.PP.isLB hy₂ hy'
  rw [← hgj] at hf
  obtain ⟨θ', w', hθ', hw', hf'⟩ := exists_isFibreOf_pull mG hθ₂ hw₂ hf
  have := G.semi.smooth
  obtain ⟨u, hu⟩ := key_unit hκ hpq hgood (spMap j ≫ z) (PullbackSections.sabMapCast n₁ (Category.assoc _ _ _).symm) n₄ hw'
    (generates_of_isFibreOf G.PP.isLB hf' hθ') y' hf'
  rw [hκ.2.1 K T₀.Fr j₀ y y' hy', hpow K x y 2 hy, Units.val_pow_eq_pow_val] at hu
  have hj : ∀ a : V, j₀ (algebraMap V K a) = algebraMap T₀.V T₀.Fr (g a) := fun a => (RingHom.congr_fun hgj a).symm
  have inj := IsFractionRing.injective T₀.V T₀.Fr
  rcases ValuationRing.isInteger_or_isInteger V (κ K x : K) with ⟨a, ha⟩ | ⟨a, ha⟩
  · rw [← ha, ← map_pow, hj] at hu
    have hau : IsUnit a := isUnit_of_dvd_unit (dvd_pow_self a two_ne_zero)
      (isUnit_of_map_unit g _ (inj hu ▸ u.isUnit))
    exact ⟨hau.unit, ha.symm⟩
  · have e : algebraMap T₀.V T₀.Fr (g (a ^ 2) * u) = algebraMap T₀.V T₀.Fr 1 := by
      rw [map_mul, ← hu, ← hj, ← map_mul, map_pow, ha, ← mul_pow, inv_mul_cancel₀ (κ K x).ne_zero, one_pow, map_one, map_one]
    have hau : IsUnit a := isUnit_of_dvd_unit (dvd_pow_self a two_ne_zero)
      (isUnit_of_map_unit g _ (IsUnit.of_mul_eq_one _ (inj e)))
    refine ⟨hau.unit⁻¹, ?_⟩
    rw [map_units_inv, IsUnit.unit_spec, ha, inv_inv]

end Unit

section Main

open MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights TensorProduct GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

theorem key_integral : ∀ κ : GlobalTheory.KeyCl.Rule, GlobalTheory.KeyCl.Homog (fun _ => 1) κ → GlobalTheory.KeyCl.Funct κ → GlobalTheory.KeyCl.UnitSp κ →
    GlobalTheory.KeyCl.ThetaOne κ → GlobalTheory.KeyCl.ArchNorm (fun _ => 1) κ →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R K : Type) [CommRing R] [IsDomain R]
      [IsDiscreteValuationRing R] [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K] (t : SAB H (Sp R))
      (th : t.PP.L.Sec) (x : KeyIn K) (v : Fin x.P.g → (epsR R ⟶ t.G)),
      KeyOver (algebraMap R K) t th x v → IsLieBasis v →
      (∀ (d : R) (th' : t.PP.L.Sec), (∀ i, th.f i = constFn t.G.hom _ d * th'.f i) → IsUnit d) →
      (κ K x : K) ∈ Set.range (algebraMap R K) := by
  intro κ k₁ k₂ k₃ k₄ k₅ E _ _ _ H R K _ _ _ _ _ _ _ t th x v ⟨φ, he, w, h1, h2, h3, h4, h5⟩ hv hprim
  have hκ : GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels.IsKeyRule κ := by
    refine ⟨?_, k₂, k₃, k₄, ?_⟩
    · simpa only [GlobalTheory.KeyCl.Homog, _root_.mul_one] using k₁
    · simpa only [GlobalTheory.KeyCl.ArchNorm, _root_.mul_one] using k₅
  have := t.semi.smooth
  obtain ⟨u, hu⟩ := key_isUnit hκ (GlobalTheory.KeyCl.rule_pow κ k₁ k₂ k₄) t th v x
    ⟨φ, he, w, rfl, dualMap (algebraMap R K), h1, h2, h3, h4,
      fun a => by ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl], by ext <;> simp [dualMap], h5⟩
    hv (nonzeroClosed_of_primitive th hprim)
  exact ⟨u, hu.symm⟩

theorem kp : KeyBadSt :=
  fun κ k₁ k₂ k₃ k₄ k₅ E _ _ _ H R K _ _ _ _ _ _ _ _ => key_integral κ k₁ k₂ k₃ k₄ k₅ E H R K

end Main

end PositivityTheory.HtPt.Kftwo
