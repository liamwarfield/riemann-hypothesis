module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvUAbsU
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealSubfieldNegativeTwoPlacesNormEverywher
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.Clause1
public import ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.Weyl

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionUnramifiedOfHasGoodReduction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionUnramifiedOfHasGoodReduction
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Published.AbVarRed

theorem torsionUnramified_of_hasGoodReduction : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] (V : ValuationSubring Ω),
    IsAbove R K V.toSubring → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], HasGoodReduction R K A →
    ∀ m : ℕ, (m : ResidueField R) ≠ 0 → TorsionUnramified A V m := by
  intro R K Ω _ _ _ _ _ _ _ _ V hV A _ _ hA m hm σ hσ x hx
  obtain ⟨G, _, hG, e, he⟩ := hA
  have : IsCommMonObj G := hG.comm
  have : Smooth G.hom := hG.smooth
  have : IsProper G.hom := hG.proper
  have : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  have hP : IsGrpPullback A G (spMap (algebraMap R K)) (e.inv.left ≫ pullback.fst G.hom (spMap (algebraMap R K))) :=
    ((isGrpPullback_of_iso e.symm).comp (isGrpPullback_pullback G (spMap (algebraMap R K)))).congr
      (Category.id_comp _) rfl
  set φ := e.inv.left ≫ pullback.fst G.hom (spMap (algebraMap R K)) with hφ

  let T0 : Over (Sp R) := Over.mk ((ptOver K Ω).hom ≫ spMap (algebraMap R K))
  let Φ : (ptOver K Ω ⟶ A) → (T0 ⟶ G) := fun y => Over.homMk (y.left ≫ φ) (by
    change (y.left ≫ φ) ≫ G.hom = (ptOver K Ω).hom ≫ spMap (algebraMap R K)
    rw [Category.assoc, hP.1.w, ← Category.assoc, Over.w y])
  have Φmul : ∀ y y', Φ (y * y') = Φ y * Φ y' := fun y y' =>
    Over.OverMorphism.ext (hP.2 (ptOver K Ω) y y' (Φ y) (Φ y') rfl rfl).symm
  let ΦM : (ptOver K Ω ⟶ A) →* (T0 ⟶ G) := MonoidHom.mk' Φ Φmul
  have Φinj : Function.Injective Φ := fun y y' h =>
    Over.OverMorphism.ext (hP.1.hom_ext (congrArg Over.Hom.left h) ((Over.w y).trans (Over.w y').symm))

  have hmemV : ∀ r : R, algebraMap K Ω (algebraMap R K r) ∈ V := fun r => by
    have : algebraMap R K r ∈ V.toSubring.comap (algebraMap K Ω) := by rw [hV]; exact ⟨r, rfl⟩
    exact this
  let rV : R →+* V := ((algebraMap K Ω).comp (algebraMap R K)).codRestrict V hmemV
  have hrV : (algebraMap V Ω).comp rV = (algebraMap K Ω).comp (algebraMap R K) := RingHom.ext fun _ => rfl

  obtain ⟨hσV, hσr⟩ := (mem_inertia_iff V σ).1 hσ
  have hmem : ∀ y ∈ V, σ y ∈ V := fun y hy => by
    have h := (ValuationSubring.smul_mem_pointwise_smul_iff (g := σ) (S := V) (x := y)).2 hy
    rw [hσV] at h
    exact h
  let σV : V →+* V := ((σ : Ω →+* Ω).comp (algebraMap V Ω)).codRestrict V fun y => hmem y y.2
  have F1 : (algebraMap V Ω).comp σV = (σ : Ω →+* Ω).comp (algebraMap V Ω) := RingHom.ext fun _ => rfl
  have F2 : σV.comp rV = rV := RingHom.ext fun r => Subtype.ext (σ.commutes (algebraMap R K r))
  have F3 : (residue V).comp σV = residue V := RingHom.ext fun y => by
    change residue V (σV y) = residue V y
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
    exact hσr y y.2

  have hE : ValuativeCriterion.Existence G.hom := by
    have h : (ValuativeCriterion.Existence ⊓ @QuasiCompact) G.hom := by
      rw [← UniversallyClosed.eq_valuativeCriterion]; infer_instance
    exact h.1
  let S : ValuativeCommSq G.hom := ⟨V, Ω, (Φ x).left, spMap rV, ⟨by
    change (x.left ≫ φ) ≫ G.hom = spMap (algebraMap V Ω) ≫ spMap rV
    rw [Category.assoc, hP.1.w, ← Category.assoc, Over.w x, GlobalTheory.RedPts.spMap_comp, hrV]
    exact GlobalTheory.RedPts.spMap_comp _ _⟩⟩
  obtain ⟨l, hl1, hl2⟩ := (hE S).exists_lift.some
  change spMap (algebraMap V Ω) ≫ l = x.left ≫ φ at hl1
  change l ≫ G.hom = spMap rV at hl2
  let P : Over (Sp R) := Over.mk (spMap rV)
  let a : P ⟶ G := Over.homMk l hl2
  let b : P ⟶ G := Over.homMk (spMap σV ≫ l) (by
    change (spMap σV ≫ l) ≫ G.hom = spMap rV
    rw [Category.assoc, hl2, GlobalTheory.RedPts.spMap_comp, F2])
  let u : T0 ⟶ P := Over.homMk (spMap (algebraMap V Ω)) (by
    change spMap (algebraMap V Ω) ≫ spMap rV = (ptOver K Ω).hom ≫ spMap (algebraMap R K)
    rw [GlobalTheory.RedPts.spMap_comp, hrV]
    exact (GlobalTheory.RedPts.spMap_comp _ _).symm)
  have hua : u ≫ a = Φ x := Over.OverMorphism.ext hl1
  have hub : u ≫ b = Φ (galPts A σ x) := Over.OverMorphism.ext (by
    change spMap (algebraMap V Ω) ≫ spMap σV ≫ l = (galPts A σ x).left ≫ φ
    rw [galPts_left, ← Category.assoc, GlobalTheory.RedPts.spMap_comp, F1, ← GlobalTheory.RedPts.spMap_comp, Category.assoc, hl1,
      Category.assoc])

  let Z : Over (Sp R) := Over.mk (spMap ((residue V).comp rV))
  let j : Z ⟶ P := Over.homMk (spMap (residue V)) (GlobalTheory.RedPts.spMap_comp _ _)
  have hjb : j ≫ b = j ≫ a := Over.OverMorphism.ext (by
    change spMap (residue V) ≫ spMap σV ≫ l = spMap (residue V) ≫ l
    rw [← Category.assoc, GlobalTheory.RedPts.spMap_comp, F3])
  have hdom : IsDominant (spMap (algebraMap V Ω)) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
      change RingHom.ker (algebraMap V Ω) ≤ _
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V Ω)]; exact bot_le)⟩
  have hu : Function.Injective (GlobalTheory.RedPts.precomp G u) := fun c d h => Over.OverMorphism.ext
    (ext_of_isDominant_of_isSeparated (X := Sp V) G.hom ((Over.w c).trans (Over.w d).symm)
      (spMap (algebraMap V Ω)) (congrArg Over.Hom.left h))
  have hz : (b * a⁻¹) ^ m = 1 := by
    apply hu
    rw [map_pow, map_one, map_mul, map_inv]
    change ((u ≫ b) * (u ≫ a)⁻¹) ^ m = 1
    rw [hua, hub]
    change (ΦM (galPts A σ x) * (ΦM x)⁻¹) ^ m = 1
    rw [← map_inv, ← map_mul, ← map_pow, mul_pow, inv_pow, ← map_pow, hx, map_one, inv_one, _root_.mul_one, map_one]
  have hjz : j ≫ (b * a⁻¹) = 1 := by
    rw [MonObj.comp_mul, GrpObj.comp_inv, hjb, mul_inv_cancel]
  have hn : IsUnit (m : V) := by
    have h1 : IsUnit (m : R) := by
      by_contra h
      apply hm
      rw [← map_natCast (residue R), residue_eq_zero_iff]
      exact h
    simpa using h1.map rV
  have h1 := GlobalTheory.RedPts.eq_one_of_pow_of_closedPoint G (spMap rV) hn (b * a⁻¹) hz j
    ⟨IsLocalRing.closedPoint _, IsLocalRing.comap_closedPoint (IsLocalRing.residue V)⟩ hjz
  have hba : b = a := mul_inv_eq_one.1 h1
  apply Φinj
  rw [← hub, ← hua, hba]

end GlobalTheory.Published.AbVarRed
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionUnramifiedOfHasGoodReductionStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionUnramified_of_hasGoodReduction_alt : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], HasGoodReduction R K A → ∀ m : ℕ, (m : ResidueField R) ≠ 0 → TorsionUnramified A V m := by
  first | exact @GlobalTheory.Published.AbVarRed.torsionUnramified_of_hasGoodReduction | exact GlobalTheory.Published.AbVarRed.torsionUnramified_of_hasGoodReduction | (intros; apply GlobalTheory.Published.AbVarRed.torsionUnramified_of_hasGoodReduction <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChiDeltaUConjLongSimpleReflectionUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChiDeltaUConjLongSimpleReflectionUnitary
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG

noncomputable section

namespace GlobalTheory

namespace GKUnitary

theorem diag_conj_weylRep {R : Type} [CommRing R] {n : ℕ} {s : Equiv.Perm (Fin n)} {y t : GL (Fin n) R}
    (hy : IsWeylRep s y) (ht : ∀ i j, i ≠ j → (t : Matrix (Fin n) (Fin n) R) i j = 0) (i : Fin n) :
    ((y⁻¹ * t * y : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i i =
      (t : Matrix (Fin n) (Fin n) R) (s i) (s i) := by
  have h1 : ((y⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i (s i) * (y : Matrix (Fin n) (Fin n) R) (s i) i = 1 := by
    have h := congrFun (congrFun (Units.inv_mul y) i) i
    rw [Matrix.mul_apply, Finset.sum_eq_single (s i)] at h
    · rw [h, Matrix.one_apply_eq]
    · intro b _ hb; rw [hy b i hb, mul_zero]
    · simp
  rw [Units.val_mul, Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single (s i)]
  · rw [Matrix.mul_apply, Finset.sum_eq_single (s i)]
    · calc ((y⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i (s i) * (t : Matrix (Fin n) (Fin n) R) (s i) (s i) *
            (y : Matrix (Fin n) (Fin n) R) (s i) i
          = (t : Matrix (Fin n) (Fin n) R) (s i) (s i) *
            (((y⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i (s i) * (y : Matrix (Fin n) (Fin n) R) (s i) i) := by ring
        _ = _ := by rw [h1, mul_one]
    · intro b _ hb; rw [ht b (s i) hb, mul_zero]
    · simp
  · intro b _ hb; rw [hy b i hb, mul_zero]
  · simp

theorem ordL_congr {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {x y : L}
    (h : Valued.v x = Valued.v y) : ordL x = ordL y := by
  have key : ∀ z : L, ordL z = (fun w : WithZero (Multiplicative ℤ) =>
      if h : w = 0 then (0 : ℤ) else -Multiplicative.toAdd (WithZero.unzero h)) (Valued.v z) := fun _ => rfl
  rw [key x, key y, h]

theorem ordL_one' {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] : ordL (1 : L) = 0 :=
  Formalism.UG.P.fIwasawa_ordL_unit 1 1 (by simp) (by simp) (by simp)

theorem chiDeltaU_conj_simpleU_long :
    ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    IsUnramInv ϖ σ q → ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → Even n →
    ∀ (y : GU σ n), IsWeylRep (simpleU k) (y : GL (Fin n) L) → ∀ (α : Fin (n / 2) → ℂˣ) (t : GU σ n),
    (∀ i j, i ≠ j → ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0) →
    chiDeltaU q (fun i => (α i : ℂ)) (y⁻¹ * t * y) *
        (q : ℂ) ^ (-2 * ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k))) =
      chiDeltaU q (fun i => (actU k α i : ℂ)) t := by
  intro L _ _ ϖ σ q hU n k hk hn y hy α t ht
  obtain ⟨hσ, hσv, -, -, -, hq2, -⟩ := hU
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hs : simpleU k = Equiv.swap (lo k) (lo k).rev := by simp [simpleU, hk]
  have hact : actU k α = Function.update α k (α k)⁻¹ := by simp [actU, hk]
  obtain ⟨m, hm⟩ := hn
  have hkv : k.val + 1 = m := by have := k.2; omega
  have hrev : ((lo k).rev : ℕ) = m := by simp [Fin.val_rev, lo]; omega
  set T : Matrix (Fin n) (Fin n) L := ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hT
  have hdiag : ∀ i, (((y⁻¹ * t * y : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i =
      T (simpleU k i) (simpleU k i) := by
    intro i
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact diag_conj_weylRep hy ht i

  have hprod : σ (T (lo k).rev (lo k).rev) * T (lo k) (lo k) = 1 := by
    have hu := (GlobalTheory.LGrp.mem_GU_iff σ n (t : GL (Fin n) L)).1 t.2 (lo k) (lo k)
    have h := congrFun (congrFun (Units.inv_mul (t : GL (Fin n) L)) (lo k)) (lo k)
    rw [Matrix.mul_apply, Finset.sum_eq_single (lo k)] at h
    · rw [← hu, h, Matrix.one_apply_eq]
    · intro b _ hb; exact mul_eq_zero_of_right _ (ht b (lo k) hb)
    · simp
  have ha0 : T (lo k) (lo k) ≠ 0 := right_ne_zero_of_mul_eq_one hprod
  have hb0 : σ (T (lo k).rev (lo k).rev) ≠ 0 := left_ne_zero_of_mul_eq_one hprod
  have hord : ordL (T (lo k).rev (lo k).rev) = -ordL (T (lo k) (lo k)) := by
    have h := Formalism.UG.P.fIwasawa_ordL_mul _ _ hb0 ha0
    rw [hprod, ordL_one', ordL_congr (hσv _)] at h
    omega
  unfold chiDeltaU
  rw [← hT]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k), ← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
  have hrest : ∀ i ∈ Finset.univ.erase k,
      (if h : i.val < n then (α i : ℂ) ^ ordL ((((y⁻¹ * t * y : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) ⟨i.val, h⟩ ⟨i.val, h⟩) *
        (q : ℂ) ^ (-(ordL ((((y⁻¹ * t * y : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) ⟨i.val, h⟩ ⟨i.val, h⟩)) *
          ((n : ℤ) - 1 - 2 * (i.val : ℤ))) else 1) =
      (if h : i.val < n then (actU k α i : ℂ) ^ ordL (T ⟨i.val, h⟩ ⟨i.val, h⟩) *
        (q : ℂ) ^ (-(ordL (T ⟨i.val, h⟩ ⟨i.val, h⟩)) * ((n : ℤ) - 1 - 2 * (i.val : ℤ))) else 1) := by
    intro i hi
    have hik : i ≠ k := Finset.ne_of_mem_erase hi
    have hin : i.val < n := by have := i.2; omega
    rw [dite_eq_left hin, dite_eq_left hin, hdiag, hact, Function.update_of_ne hik]
    have hfix : simpleU k ⟨i.val, hin⟩ = ⟨i.val, hin⟩ := by
      rw [hs]
      refine Equiv.swap_apply_of_ne_of_ne ?_ ?_
      · intro h; apply hik; ext; simpa [lo] using congrArg Fin.val h
      · intro h; have := congrArg Fin.val h; rw [hrev] at this; have := i.2; simp at *; omega
    rw [hfix]
  rw [Finset.prod_congr rfl hrest]
  have hkn : k.val < n := by omega
  rw [dite_eq_left hkn, dite_eq_left hkn, hdiag, hact]
  beta_reduce
  rw [Function.update_self]
  have hlk : (⟨k.val, hkn⟩ : Fin n) = lo k := rfl
  rw [hlk, hs, Equiv.swap_apply_left, hord]
  have he : ((n : ℤ) - 1 - 2 * (k.val : ℤ)) = 1 := by
    have : (n : ℤ) = m + m := by exact_mod_cast hm
    have h2 : (k.val : ℤ) + 1 = m := by exact_mod_cast hkv
    omega
  rw [he]
  set r := ordL (T (lo k) (lo k))
  have hα : (α k : ℂ) ≠ 0 := (α k).ne_zero
  have hq1 : (q : ℂ) ^ (-(-r) * (1 : ℤ)) * (q : ℂ) ^ (-2 * r) = (q : ℂ) ^ (-r * (1 : ℤ)) := by
    rw [← zpow_add₀ hq]; congr 1; ring
  rw [Units.val_inv_eq_inv_val, inv_zpow', ← hq1]
  ring

end GKUnitary

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChiDeltaUConjLongSimpleReflectionUnitaryStatement
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chiDeltaU_conj_longSimpleReflection_unitary : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    IsUnramInv ϖ σ q → ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → Even n →
    ∀ (y : GU σ n), IsWeylRep (simpleU k) (y : GL (Fin n) L) → ∀ (α : Fin (n / 2) → ℂˣ) (t : GU σ n),
    (∀ i j, i ≠ j → ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0) →
    chiDeltaU q (fun i => (α i : ℂ)) (y⁻¹ * t * y) *
        (q : ℂ) ^ (-2 * ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k))) =
      chiDeltaU q (fun i => (actU k α i : ℂ)) t := by
  first | exact @GlobalTheory.GKUnitary.chiDeltaU_conj_simpleU_long | exact GlobalTheory.GKUnitary.chiDeltaU_conj_simpleU_long | (intros; apply GlobalTheory.GKUnitary.chiDeltaU_conj_simpleU_long <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTotallyRealEvenNegPlacesLocalNorm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTotallyRealEvenNegPlacesLocalNorm
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.NormSignEven

variable {M : Type} [Field M] [NumberField M]

lemma cc (φ : M →+* ℂ) : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate φ) = φ := star_star φ

lemma conj_re (φ : M →+* ℂ) (x : M) : (ComplexEmbedding.conjugate φ x).re = (φ x).re := by
  rw [ComplexEmbedding.conjugate_coe_eq]; simp

lemma conj_ne {σ : M →+* M} (hσ : σ ≠ RingHom.id M)
    (hc : ∀ (φ : M →+* ℂ) (x : M), φ (σ x) = (starRingEnd ℂ) (φ x)) (φ : M →+* ℂ) :
    ComplexEmbedding.conjugate φ ≠ φ := by
  intro h
  apply hσ
  ext x
  apply φ.injective
  rw [hc, RingHom.id_apply]
  have := congrArg (fun ψ : M →+* ℂ => ψ x) h
  simpa [ComplexEmbedding.conjugate_coe_eq] using this

lemma im_eq_zero {σ : M →+* M}
    (hc : ∀ (φ : M →+* ℂ) (x : M), φ (σ x) = (starRingEnd ℂ) (φ x)) (φ : M →+* ℂ) {x : M} (hx : σ x = x) :
    (φ x).im = 0 := by
  have h := hc φ x
  rw [hx] at h
  exact Complex.conj_eq_iff_im.mp h.symm

lemma re_mul {σ : M →+* M}
    (hc : ∀ (φ : M →+* ℂ) (x : M), φ (σ x) = (starRingEnd ℂ) (φ x)) (φ : M →+* ℂ) {x y : M}
    (hx : σ x = x) :
    (φ (x * y)).re = (φ x).re * (φ y).re := by
  rw [map_mul, Complex.mul_re, im_eq_zero hc φ hx, zero_mul, sub_zero]

end GlobalTheory.NormSignEven

open GlobalTheory.NormSignEven in
theorem GlobalTheory.NormSign.exists_neg_even_norm_away : ∀ (M : Type) [Field M] [NumberField M] (σ : M →+* M), σ ≠ RingHom.id M → (∀ (φ : M →+* ℂ) (x : M), φ (σ x) = (starRingEnd ℂ) (φ x)) → ∀ (S : Finset (M →+* ℂ)), (∀ φ ∈ S, ComplexEmbedding.conjugate φ ∈ S) → 4 ∣ S.card → ∀ (p : ℕ) [Fact p.Prime], ∃ a : M, a ≠ 0 ∧ σ a = a ∧ (∀ φ ∈ S, (φ a).re < 0) ∧ (∀ φ : M →+* ℂ, φ ∉ S → 0 < (φ a).re) ∧ ∃ u : (AfP p ⊗[ℚ] M)ˣ, (u : AfP p ⊗[ℚ] M) * Algebra.TensorProduct.map (AlgHom.id ℚ (AfP p)) σ.toRatAlgHom u = 1 ⊗ₜ a := by
  intro M _ _ σ hσ hc S hS h4 p _
  obtain ⟨n, hn⟩ := h4
  induction n generalizing S with
  | zero =>
    have hS0 : S = ∅ := Finset.card_eq_zero.mp (by simpa using hn)
    subst hS0
    refine ⟨1, one_ne_zero, map_one σ, by simp, fun φ _ => by simp, 1, ?_⟩
    simp [Algebra.TensorProduct.one_def]
  | succ n ih =>
    obtain ⟨ε, hε⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
    have hε1 : ComplexEmbedding.conjugate ε ∈ (S.erase ε) :=
      Finset.mem_erase.mpr ⟨conj_ne hσ hc ε, hS ε hε⟩
    have hT : 0 < ((S.erase ε).erase (ComplexEmbedding.conjugate ε)).card := by
      rw [Finset.card_erase_of_mem hε1, Finset.card_erase_of_mem hε]; omega
    obtain ⟨ε', hε'⟩ := Finset.card_pos.mp hT
    simp only [Finset.mem_erase] at hε'
    obtain ⟨h1, h2, hε'S⟩ := hε'
    have hcc : ∀ φ ψ : M →+* ℂ, ComplexEmbedding.conjugate φ = ψ → φ = ComplexEmbedding.conjugate ψ := by
      intro φ ψ h; rw [← h, cc]
    have h3 : ε ≠ ComplexEmbedding.conjugate ε' := by
      intro h; apply h1; rw [h, cc]
    set S' := (((S.erase ε).erase (ComplexEmbedding.conjugate ε)).erase ε').erase
      (ComplexEmbedding.conjugate ε') with hS'def
    have hmem : ∀ φ, φ ∈ S' ↔ φ ≠ ComplexEmbedding.conjugate ε' ∧ φ ≠ ε' ∧
        φ ≠ ComplexEmbedding.conjugate ε ∧ φ ≠ ε ∧ φ ∈ S := by
      intro φ; simp [hS'def, Finset.mem_erase]
    have hcard : S'.card = 4 * n := by
      have e1 : ε' ∈ ((S.erase ε).erase (ComplexEmbedding.conjugate ε)) := by
        simp [Finset.mem_erase]; exact ⟨h1, h2, hε'S⟩
      have e2 : ComplexEmbedding.conjugate ε' ∈
          ((S.erase ε).erase (ComplexEmbedding.conjugate ε)).erase ε' := by
        simp only [Finset.mem_erase]
        refine ⟨conj_ne hσ hc ε', ?_, fun h => h3 h.symm, hS _ hε'S⟩
        intro h
        exact h2 (by have := congrArg ComplexEmbedding.conjugate h; simpa [cc] using this)
      rw [hS'def, Finset.card_erase_of_mem e2, Finset.card_erase_of_mem e1,
        Finset.card_erase_of_mem hε1, Finset.card_erase_of_mem hε]
      omega
    have hS'stab : ∀ φ ∈ S', ComplexEmbedding.conjugate φ ∈ S' := by
      intro φ hφ
      rw [hmem] at hφ ⊢
      obtain ⟨a1, a2, a3, a4, a5⟩ := hφ
      refine ⟨fun h => a2 ?_, fun h => a1 ?_, fun h => a4 ?_, fun h => a3 ?_, hS φ a5⟩
      · have := congrArg ComplexEmbedding.conjugate h; simpa [cc] using this
      · exact hcc _ _ h
      · have := congrArg ComplexEmbedding.conjugate h; simpa [cc] using this
      · exact hcc _ _ h
    obtain ⟨b, hb0, hbσ, hbneg, hbpos, ub, hub⟩ := ih S' hS'stab hcard
    obtain ⟨c, hc0, hcσ, hcε, hcε', hcpos, uc, huc⟩ :=
      GlobalTheory.T.exists_realSubfield_negative_twoPlaces_normEverywhere M σ hσ hc ε ε' (Ne.symm h2) h3 p
    have hcneg : ∀ φ, φ = ε ∨ φ = ComplexEmbedding.conjugate ε ∨ φ = ε' ∨ φ = ComplexEmbedding.conjugate ε' →
        (φ c).re < 0 := by
      rintro φ (rfl | rfl | rfl | rfl)
      · exact hcε
      · rw [conj_re]; exact hcε
      · exact hcε'
      · rw [conj_re]; exact hcε'
    refine ⟨b * c, mul_ne_zero hb0 hc0, by rw [map_mul, hbσ, hcσ], ?_, ?_, ub * uc, ?_⟩
    · intro φ hφ
      rw [re_mul hc φ hbσ]
      by_cases hφ' : φ ∈ S'
      · exact mul_neg_of_neg_of_pos (hbneg φ hφ') (hcpos φ (by rw [hmem] at hφ'; exact hφ'.2.2.2.1)
          (by rw [hmem] at hφ'; exact hφ'.2.2.1) (by rw [hmem] at hφ'; exact hφ'.2.1)
          (by rw [hmem] at hφ'; exact hφ'.1))
      · refine mul_neg_of_pos_of_neg (hbpos φ hφ') (hcneg φ ?_)
        rw [hmem] at hφ'
        by_contra hne
        push_neg at hne
        exact hφ' ⟨hne.2.2.2, hne.2.2.1, hne.2.1, hne.1, hφ⟩
    · intro φ hφ
      rw [re_mul hc φ hbσ]
      have hφ' : φ ∉ S' := fun h => hφ (((hmem φ).mp h).2.2.2.2)
      refine mul_pos (hbpos φ hφ') (hcpos φ ?_ ?_ ?_ ?_)
      · rintro rfl; exact hφ hε
      · rintro rfl; exact hφ (hS ε hε)
      · rintro rfl; exact hφ hε'S
      · rintro rfl; exact hφ (hS ε' hε'S)
    · rw [Units.val_mul, map_mul]
      calc (ub : AfP p ⊗[ℚ] M) * uc * (Algebra.TensorProduct.map (AlgHom.id ℚ (AfP p)) σ.toRatAlgHom ub *
            Algebra.TensorProduct.map (AlgHom.id ℚ (AfP p)) σ.toRatAlgHom uc)
          = ((ub : AfP p ⊗[ℚ] M) * Algebra.TensorProduct.map (AlgHom.id ℚ (AfP p)) σ.toRatAlgHom ub) *
            ((uc : AfP p ⊗[ℚ] M) * Algebra.TensorProduct.map (AlgHom.id ℚ (AfP p)) σ.toRatAlgHom uc) := by ring
        _ = 1 ⊗ₜ (b * c) := by rw [hub, huc, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTotallyRealEvenNegPlacesLocalNormStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_totallyReal_even_neg_places_local_norm : ∀ (M : Type) [Field M] [NumberField M] (σ : M →+* M), σ ≠ RingHom.id M → (∀ (φ : M →+* ℂ) (x : M), φ (σ x) = (starRingEnd ℂ) (φ x)) → ∀ (S : Finset (M →+* ℂ)), (∀ φ ∈ S, ComplexEmbedding.conjugate φ ∈ S) → 4 ∣ S.card → ∀ (p : ℕ) [Fact p.Prime], ∃ a : M, a ≠ 0 ∧ σ a = a ∧ (∀ φ ∈ S, (φ a).re < 0) ∧ (∀ φ : M →+* ℂ, φ ∉ S → 0 < (φ a).re) ∧ ∃ u : (AfP p ⊗[ℚ] M)ˣ, (u : AfP p ⊗[ℚ] M) * Algebra.TensorProduct.map (AlgHom.id ℚ (AfP p)) σ.toRatAlgHom u = 1 ⊗ₜ a := by
  first | exact @GlobalTheory.NormSign.exists_neg_even_norm_away | exact GlobalTheory.NormSign.exists_neg_even_norm_away | (intros; apply GlobalTheory.NormSign.exists_neg_even_norm_away <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaleInvOfFamMap
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LineConst

open Polynomial

variable (k : Type) [Field k]

def scaleHom (R : Type) [CommRing R] [Algebra k R] (u : R) : Polynomial k →+* Polynomial R :=
  Polynomial.eval₂RingHom (Polynomial.C.comp (algebraMap k R)) (Polynomial.C u * Polynomial.X)

theorem scaleHom_algebraMap (R : Type) [CommRing R] [Algebra k R] (u : R) :
    (scaleHom k R u).comp (algebraMap k (Polynomial k)) = algebraMap k (Polynomial R) := by
  ext a
  simp [scaleHom, Polynomial.algebraMap_apply]

def lineOver (R : Type) [CommRing R] [Algebra k R] : Over (Sp k) :=
  Over.mk (spMap (algebraMap k (Polynomial R)))

variable {k}

def scaled (B : Over (Sp k)) (f : Sp (Polynomial k) ⟶ B.left)
    (hf : f ≫ B.hom = spMap (algebraMap k (Polynomial k))) (R : Type) [CommRing R] [Algebra k R] (u : R) :
    lineOver k R ⟶ B :=
  Over.homMk (spMap (scaleHom k R u) ≫ f) (by
    change spMap (scaleHom k R u) ≫ f ≫ B.hom = spMap (algebraMap k (Polynomial R))
    rw [hf, ← Spec.map_comp, ← CommRingCat.ofHom_comp, scaleHom_algebraMap])

def famMap (B : Over (Sp k)) [GrpObj B] (f : Sp (Polynomial k) ⟶ B.left)
    (hf : f ≫ B.hom = spMap (algebraMap k (Polynomial k))) (R : Type) [CommRing R] [Algebra k R] (u : R) : Sp (Polynomial R) ⟶ B.left :=
  (scaled B f hf R u * (scaled B f hf R 1)⁻¹).left

end GlobalTheory.LineConst

namespace GlobalTheory.LineConst
open Polynomial

theorem scaleHom_comp_map {k : Type} [Field k] {R R' : Type} [CommRing R] [Algebra k R] [CommRing R'] [Algebra k R']
    (φ : R →ₐ[k] R') (u : R) :
    (Polynomial.mapRingHom (φ : R →+* R')).comp (scaleHom k R u) = scaleHom k R' (φ u) := by
  apply Polynomial.ringHom_ext
  · intro a; simp [scaleHom]
  · simp [scaleHom]

def lineMap {k : Type} [Field k] {R R' : Type} [CommRing R] [Algebra k R] [CommRing R'] [Algebra k R']
    (φ : R →ₐ[k] R') : lineOver k R' ⟶ lineOver k R :=
  Over.homMk (spMap (Polynomial.mapRingHom (φ : R →+* R'))) (by
    change spMap (Polynomial.mapRingHom (φ : R →+* R')) ≫ spMap (algebraMap k (Polynomial R)) =
      spMap (algebraMap k (Polynomial R'))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun a => (Polynomial.mapAlgHom φ).commutes a)

theorem lineMap_scaled {k : Type} [Field k] (B : Over (Sp k)) (f : Sp (Polynomial k) ⟶ B.left)
    (hf : f ≫ B.hom = spMap (algebraMap k (Polynomial k))) {R R' : Type} [CommRing R] [Algebra k R]
    [CommRing R'] [Algebra k R'] (φ : R →ₐ[k] R') (u : R) :
    lineMap φ ≫ scaled B f hf R u = scaled B f hf R' (φ u) := by
  ext1
  change spMap (Polynomial.mapRingHom (φ : R →+* R')) ≫ spMap (scaleHom k R u) ≫ f =
    spMap (scaleHom k R' (φ u)) ≫ f
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, scaleHom_comp_map]

theorem famMap_base {k : Type} [Field k] (B : Over (Sp k)) [GrpObj B] (f : Sp (Polynomial k) ⟶ B.left)
    (hf : f ≫ B.hom = spMap (algebraMap k (Polynomial k))) {R R' : Type} [CommRing R] [Algebra k R]
    [CommRing R'] [Algebra k R'] (φ : R →ₐ[k] R') (u : R) :
    spMap (Polynomial.mapRingHom (φ : R →+* R')) ≫ famMap B f hf R u = famMap B f hf R' (φ u) := by
  have h := congrArg CommaMorphism.left
    (show lineMap φ ≫ (scaled B f hf R u * (scaled B f hf R 1)⁻¹) =
      scaled B f hf R' (φ u) * (scaled B f hf R' 1)⁻¹ by
      rw [MonObj.comp_mul, GrpObj.comp_inv, lineMap_scaled, lineMap_scaled, map_one])
  exact h

theorem famMap_one {k : Type} [Field k] (B : Over (Sp k)) [GrpObj B] (f : Sp (Polynomial k) ⟶ B.left)
    (hf : f ≫ B.hom = spMap (algebraMap k (Polynomial k))) (R : Type) [CommRing R] [Algebra k R] :
    famMap B f hf R 1 = spMap (algebraMap k (Polynomial R)) ≫ (η[B] : 𝟙_ (Over (Sp k)) ⟶ B).left := by
  unfold famMap
  rw [mul_inv_cancel, Hom.one_def, Over.comp_left]
  congr 1

end GlobalTheory.LineConst

namespace GlobalTheory.LineConst
open Polynomial

def linePt {k : Type} [Field k] (a : k) : 𝟙_ (Over (Sp k)) ⟶ lineOver k k :=
  Over.homMk (spMap (Polynomial.evalRingHom a)) (by
    change spMap (Polynomial.evalRingHom a) ≫ spMap (algebraMap k (Polynomial k)) = 𝟙 _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (Polynomial.evalRingHom a).comp (algebraMap k (Polynomial k)) = RingHom.id k := by
      ext z; simp
    rw [this, CommRingCat.ofHom_id, Spec.map_id])

theorem linePt_scaled_left {k : Type} [Field k] (B : Over (Sp k)) (f : Sp (Polynomial k) ⟶ B.left)
    (hf : f ≫ B.hom = spMap (algebraMap k (Polynomial k))) (a c : k) :
    (linePt a ≫ scaled B f hf k c).left = spMap (Polynomial.evalRingHom (c * a)) ≫ f := by
  change spMap (Polynomial.evalRingHom a) ≫ spMap (scaleHom k k c) ≫ f = _
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 3
  apply Polynomial.ringHom_ext
  · intro z; simp [scaleHom]
  · simp [scaleHom]

theorem scale_inv_of_famMap {k : Type} [Field k] (B : Over (Sp k)) [GrpObj B] (f : Sp (Polynomial k) ⟶ B.left)
    (hf : f ≫ B.hom = spMap (algebraMap k (Polynomial k))) (c : k)
    (h : famMap B f hf k c = spMap (algebraMap k (Polynomial k)) ≫ spMap (Polynomial.evalRingHom 0) ≫ famMap B f hf k c)
    (a : k) : spMap (Polynomial.evalRingHom (c * a)) ≫ f = spMap (Polynomial.evalRingHom a) ≫ f := by
  have hpt : ∀ b : k, spMap (Polynomial.evalRingHom b) ≫ spMap (algebraMap k (Polynomial k)) = 𝟙 _ := by
    intro b
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (Polynomial.evalRingHom b).comp (algebraMap k (Polynomial k)) = RingHom.id k := by
      ext z; simp
    rw [this, CommRingCat.ofHom_id, Spec.map_id]
  have hleft : spMap (Polynomial.evalRingHom a) ≫ famMap B f hf k c =
      spMap (Polynomial.evalRingHom 0) ≫ famMap B f hf k c := by
    conv_lhs => rw [h]
    rw [← Category.assoc, hpt, Category.id_comp]
  have hq : ∀ b : k, linePt b ≫ (scaled B f hf k c * (scaled B f hf k 1)⁻¹) =
      (linePt b ≫ scaled B f hf k c) * (linePt b ≫ scaled B f hf k 1)⁻¹ := by
    intro b; rw [MonObj.comp_mul, GrpObj.comp_inv]
  have h0 : linePt 0 ≫ scaled B f hf k c = linePt 0 ≫ scaled B f hf k 1 := by
    ext1
    rw [linePt_scaled_left, linePt_scaled_left, mul_zero, mul_zero]
  have hall : linePt a ≫ (scaled B f hf k c * (scaled B f hf k 1)⁻¹) =
      linePt 0 ≫ (scaled B f hf k c * (scaled B f hf k 1)⁻¹) := by
    ext1
    exact hleft
  rw [hq, hq, h0, mul_inv_cancel] at hall
  have hall' : linePt a ≫ scaled B f hf k c = linePt a ≫ scaled B f hf k 1 :=
    mul_inv_eq_one.mp hall
  have h2 := congrArg CommaMorphism.left hall'
  have e1 := linePt_scaled_left B f hf a c
  have e2 := linePt_scaled_left B f hf a 1
  rw [_root_.one_mul] at e2
  rw [← e1, ← e2]
  exact h2

end GlobalTheory.LineConst
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceEqOfMem
noncomputable section

open MeasureTheory ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap GlobalTheory.Orb GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary
open Formalism.REAL (UJ KG toM toMK muK)
open GlobalTheory.PsCo.Pc1 (Mat Poly ev dMode blockAlg topP detbP OmP)
open GlobalTheory.HCChar (dsChar torusPt)
open scoped ComplexConjugate

namespace GlobalTheory.PsCo.PcEF

open GlobalTheory.PsCo.PcEG

theorem trace_eq_of_mem {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (B : H →L[ℂ] H)
    (L : Submodule ℂ H) [FiniteDimensional ℂ L] (hB : ∀ x, (B : H →ₗ[ℂ] H) x ∈ L) {c : ℂ} (hc : HasTrace B c) :
    c = LinearMap.trace ℂ L ((B : H →ₗ[ℂ] H).restrict fun x _ => hB x) := by
  have hle : LinearMap.range (B : H →ₗ[ℂ] H) ≤ L := by rintro _ ⟨x, rfl⟩; exact hB x
  have := Submodule.finiteDimensional_of_le hle
  rw [← hc.2, (hasTrace_of_finiteRank B).2, finRankTrace_eq _ L hB]

theorem equiv_of_index (hR : RangeFD) (hY : BuildY) (hS : StrKer) (hI : StrIdx) (hA : AvgMap) (hH : HWVec)
    (hC : CoordFD) (hCas : CasCoord) (hAlg : AlgDatum) (hE : DatumEquiv) (hCS : CompanionTheory.D.gk.HC.CasScal)
    {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} (hstd : StdGap ε lam) (h3 : Gap3 ε lam)
    {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] {T : Mat n → (W →L[ℂ] W)}
    (hT : IsKIrr ε (gaW ε lam) T) {P : Poly n} (hP : ∀ k ∈ Formalism.REAL.Kset ε, conj (trK T k) = ev k P)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Mat n → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ) (hirr : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ) (B : H →L[ℂ] H)
    (hB : ∀ w, B w = ∫ k : KG ε, (ev (toMK k) P * physDet ε (toMK k)) • σ (toMK k) w ∂(muK ε)) {c : ℂ}
    (hc : HasTrace B c) (hc0 : c ≠ 0)
    {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] {D : Mat n → (X →L[ℂ] X)} (hD : Formalism.MainNotions.S.IsDS ε lam D) :
    ∃ U : H ≃ₗᵢ[ℂ] X, ∀ g ∈ UJset ε, ∀ x, U (σ g x) = D g (U x) := by
  have hDer := isDerivedOn_smE hσ
  obtain ⟨d, hd⟩ := hI n ε P
  obtain ⟨L, hLf, hLK, hLr⟩ := hR n ε H σ hσ hirr d
  obtain ⟨cas, hcas⟩ := hCS n ε H σ hσ hirr
  obtain ⟨Y, hYf, hle, hYP, hYD, hG, hK⟩ := hY n ε H σ _ _ hσ hDer cas hcas L hLf hLK
  obtain ⟨hBL, htr⟩ := hd H σ _ _ hσ hDer L hLK hLr Y hle hYP hG hK B hB
  obtain ⟨Z, hZf, hZK, Γ, hZY, hZD, hZtr⟩ := hS n ε H σ _ _ hσ hDer Y hYD hG hK
  have hLH : FiniteDimensional ℂ (L.map (smD ε σ).subtype) := Module.Finite.map _ _
  have h1 := (trace_eq_of_mem B _ hBL hc).trans htr
  obtain ⟨Φ, hΦ0, hΦ⟩ := hA n ε W T (TSub Z) (tOp hDer hZK) Γ hT.2.1 (tOp_isURepOn hDer hZK hσ) (by
    intro h0
    apply hc0
    rw [h1, ← h0]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    dsimp only
    rw [hZtr (toMK k) k.2, hP (toMK k) k.2])
  obtain ⟨z, hzZ, hz0, hz⟩ := hH n ε H σ _ _ hσ hDer Z hZK _ W T hT Φ hΦ0 hΦ
  obtain ⟨hSf, hSk⟩ := hC n ε _ (smE ε σ) Z hZf fun a b hab y hy => diagE_mem_of_wK hσ hDer Z hZf hZK hab hy
  obtain ⟨V, hV, hV0, hVc⟩ := hAlg n ε lam h3 _ (smE ε σ) hDer.glRep (isInfUnitary_of_isDerivedOn hσ hDer) z hz0
    (hYP (hZY hzZ)) hz (hCas n ε lam _ _ hDer.glRep z hz (hZD z hzZ)) _ hSf hSk
    fun s => Submodule.subset_span ⟨s, z, hzZ, rfl⟩
  exact hE n ε lam hstd H σ hσ hirr V hV hV0 hVc X D hD

theorem exists_type (hCp : CptCase) (hSch : SchurOne)
    {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} (hHC : Formalism.QuantumDeterminants.IsHCParam lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hthr : thrStar ε < h) {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    {D : Mat n → (X →L[ℂ] X)} (hD : Formalism.MainNotions.S.IsDS ε lam D) :
    ∃ (W : Type) (_ : NormedAddCommGroup W) (_ : InnerProductSpace ℂ W) (_ : FiniteDimensional ℂ W)
      (T : Mat n → (W →L[ℂ] W)), IsKIrr ε (gaW ε lam) T ∧ ∀ P : Poly n,
      (∀ k ∈ Formalism.REAL.Kset ε, conj (trK T k) = ev k P) → ∀ (B : X →L[ℂ] X) (c : ℂ),
      (∀ w, B w = ∫ k : KG ε, (ev (toMK k) P * physDet ε (toMK k)) • D (toMK k) w ∂(muK ε)) → HasTrace B c →
      c = (-1) ^ sDeg ε := by
  by_cases hpq : pOf ε = 0 ∨ qOf ε = 0
  · obtain ⟨hpd, hs, hX⟩ := hCp n ε lam hpq
    obtain ⟨hfd, hT⟩ := hX X D hD
    refine ⟨X, inferInstance, inferInstance, hfd, D, hT, fun P hP B c hB hc => ?_⟩
    have hemb : Topology.IsEmbedding (fun k : KG ε => toMK k) :=
      (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal
    have : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
      inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
    have : SecondCountableTopology (KG ε) := hemb.isInducing.secondCountableTopology
    have hcont : Continuous fun k : KG ε => ev (toMK k) P * physDet ε (toMK k) := by
      simp only [hpd, mul_one]
      refine (MvPolynomial.continuous_eval P).comp (continuous_pi fun p => ?_)
      rcases p with p | p
      · exact (continuous_apply p.2).comp ((continuous_apply p.1).comp hemb.continuous)
      · exact continuous_star.comp ((continuous_apply p.2).comp ((continuous_apply p.1).comp hemb.continuous))
    have h1 := trace_integral_restrict (μ := muK ε) (⊤ : Submodule ℂ X) hcont (fun k => D (toMK k))
      (fun v => (hT.2.1.2.2 v).comp_continuous hemb.continuous fun k => k.2) (fun _ _ _ => trivial) B hB
      (fun _ _ => trivial)
    rw [trace_eq_of_mem B ⊤ (fun _ => trivial) hc, h1, hs, pow_zero, ← hSch n ε _ X D hT]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    dsimp only
    rw [hpd, mul_one, hP (toMK k) k.2]
    delta trK
    congr 1
    exact LinearMap.trace_restrict_eq_of_forall_mem ⊤ _ fun _ => trivial
  · obtain ⟨W, i1, i2, i3, T, h1, h2, h3, h4⟩ := supTrace n ε lam h X D hD hHC hh hthr (by omega) (by omega)
    refine ⟨W, i1, i2, i3, T, ⟨h1, h2, h3⟩, fun P hP B c hB hc => ?_⟩
    obtain ⟨hf, htr⟩ := h4 P B hB
    rw [trace_eq_of_mem B _ (fun x => LinearMap.mem_range_self _ x) hc, htr]
    have h5 := hSch n ε _ W T ⟨h1, h2, h3⟩
    rw [← mul_one ((-1 : ℂ) ^ sDeg ε), mul_assoc, one_mul, ← h5]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    dsimp only
    rw [hP (toMK k) k.2]
    rfl

theorem stKData_of (hBF : BlockForm) (hOm : OmDet) (hCP : CoefPoly) (hTP : TrPoly) (hCl : ClassFn) (hGa : GaInt)
    (hTK : ToKType) (hPT : PhysTor) (hTor : TorusId) (hA : AvgMap) (hSch : SchurOne) (hR : RangeFD) (hY : BuildY)
    (hS : StrKer) (hI : StrIdx) (hH : HWVec) (hC : CoordFD) (hCas : CasCoord) (hAlg : AlgDatum) (hE : DatumEquiv)
    (hCp : CptCase) (hGap : GapNum) (hM : MatRep) (hCS : CompanionTheory.D.gk.HC.CasScal) : GlobalTheory.PsCo.Pc1.StKData := by
  intro r hr ε lam hg X _ _ D hD
  have := hD.1
  obtain ⟨hHC, hstd, h3, h, hh, hthr⟩ := hGap r hr ε lam hg
  obtain ⟨W, _, _, _, T, hT, hidx⟩ := exists_type hCp hSch hHC hh hthr hD
  have hcoef := hCP r ε W T hT.2.1
  obtain ⟨P, hP⟩ := hTP r ε W T hcoef
  replace hP : ∀ k ∈ Formalism.REAL.Kset ε, conj (trK T k) = ev k P := hP
  obtain ⟨Q, hQ⟩ := hOm r ε
  obtain ⟨M, R, hRb, hRe⟩ := hBF r ε (MvPolynomial.C ((-1 : ℂ) ^ sDeg ε) * P * Q)
  have hsq : ((-1 : ℂ) ^ sDeg ε) * (-1) ^ sDeg ε = 1 := by rw [← mul_pow]; simp
  have htop : ∀ k ∈ Formalism.REAL.Kset ε, ev k (topP ε M R) = (-1) ^ sDeg ε * (ev k P * physDet ε k) := by
    intro k hk
    change ev k (detbP r ^ M * R * (OmP ε).det) = _
    rw [map_mul, ← hRe k hk, ← hQ k hk, map_mul, map_mul,
      show ev k (MvPolynomial.C _) = _ from MvPolynomial.eval_C _]
    ring
  have hscale : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (A : KG ε → (H →L[ℂ] H)) (B : H →L[ℂ] H) (c : ℂ),
      (∀ v, B v = ∫ k : KG ε, ev (toMK k) (topP ε M R) • A k v ∂(muK ε)) → HasTrace B c →
      (∀ v, (((-1 : ℂ) ^ sDeg ε) • B) v = ∫ k : KG ε, (ev (toMK k) P * physDet ε (toMK k)) • A k v ∂(muK ε)) ∧
        HasTrace (((-1 : ℂ) ^ sDeg ε) • B) ((-1) ^ sDeg ε * c) := by
    intro H _ _ _ A B c hB hc
    refine ⟨fun v => ?_, ⟨hc.1.smul _, by rw [trace_smul, hc.2]⟩⟩
    rw [_root_.smul_apply, hB, ← integral_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    dsimp only
    rw [htop (toMK k) k.2, smul_smul, ← mul_assoc, hsq, one_mul]
  refine ⟨M, R, hRb, fun k k' => ?_, fun θ hθ => ?_, fun B c hB hc => ?_, fun U _ _ _ π hπ hi hne B c hB hc => ?_⟩
  · rw [htop _ (k'⁻¹ * k * k').2, htop _ k.2, ← hP _ (k'⁻¹ * k * k').2, ← hP _ k.2, (hCl r ε k k').1,
      (hCl r ε k k').2 W T hT.2.1]
  · obtain ⟨Λ, m, hΛ, hdom, hm, hsh⟩ := hGa r ε _ hHC
    have hk : Matrix.diagonal (tor θ) ∈ Kset ε := diag_mem_Kset' ε θ
    rw [hΛ] at hT
    obtain ⟨T₀, hT₀⟩ := hTK r ε _ W T hT hcoef
    have hw := ReciprocityTheory.ChartRestriction.TR.Weyl.weyl r ε Λ hdom T₀ (HW.torepK ε hk) (tor θ) rfl
    rw [hT₀] at hw
    have h1 := hTor r ε _ Λ m hm hsh θ hθ _ hw
    change (-1) ^ sDeg ε * trK T (Matrix.diagonal (tor θ)) = _ at h1
    change ev (Matrix.diagonal (tor θ)) _ = _
    have h2 := congrArg conj h1
    rw [map_mul, map_mul, map_pow, map_neg, map_one] at h2
    rw [htop _ hk, ← hP _ hk, ← (hPT r ε θ).2, ← mul_assoc, h2]
    ring
  · obtain ⟨h1, h2⟩ := hscale X (fun k => D (toMK k)) B c hB hc
    have h4 := hidx P hP _ _ h1 h2
    have h5 := congrArg (fun x => (-1 : ℂ) ^ sDeg ε * x) h4
    simpa only [← mul_assoc, hsq, one_mul] using h5
  · by_contra hc0
    obtain ⟨σ, hσ, hirr, hσπ⟩ := hM r ε U π hπ hi
    obtain ⟨h1, h2⟩ := hscale U (fun k => π k) B c hB hc
    obtain ⟨A, hAe⟩ := equiv_of_index hR hY hS hI hA hH hC hCas hAlg hE hCS hstd h3 hT hP hσ hirr _
      (fun w => by rw [h1 w]; simp only [toMK, hσπ]) h2
      (mul_ne_zero (pow_ne_zero _ (by norm_num)) hc0) hD
    exact hne ⟨A, fun g v => by rw [← hσπ g]; exact hAe _ g.2 v⟩

end GlobalTheory.PsCo.PcEF
end
end
