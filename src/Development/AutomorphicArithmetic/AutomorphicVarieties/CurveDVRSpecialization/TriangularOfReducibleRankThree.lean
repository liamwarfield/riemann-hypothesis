module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RatTorsionFree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CommutingUpperTriangularDistinct
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.RtBasic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.DatFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.DatLoc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.MapDiagonalRepMatrixEq

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ValuationRingClearLastRowEntry
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial

namespace UpperTheory.V.Loc

private def TriangularForm {ι A C : Type} [CommRing A] [CommRing C] (M : ι → Matrix (Fin 3) (Fin 3) A) (d : ι → Fin 3 → A)
    (S T : Set ι) (φ : A →+* C) (h : GL (Fin 3) C) : Prop :=
  (∀ g ∈ S, ∀ a b, b < a →
    (((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) * (M g).map φ * (h : Matrix (Fin 3) (Fin 3) C)) a b = 0) ∧
  ∀ g ∈ T, ∀ a,
    (((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) * (M g).map φ * (h : Matrix (Fin 3) (Fin 3) C)) a a = φ (d g a)

section

variable {ι A C C' : Type} [CommRing A] [CommRing C] [CommRing C'] {M : ι → Matrix (Fin 3) (Fin 3) A}
  {d : ι → Fin 3 → A} {S T : Set ι}

private theorem conjugate_entry_map (X : Matrix (Fin 3) (Fin 3) A) (φ : A →+* C) (ψ : C →+* C') (h : GL (Fin 3) C) (a b : Fin 3) :
    ((((Matrix.GeneralLinearGroup.map ψ h)⁻¹ : GL (Fin 3) C') : Matrix (Fin 3) (Fin 3) C') * X.map (ψ.comp φ) *
      (Matrix.GeneralLinearGroup.map ψ h : Matrix (Fin 3) (Fin 3) C')) a b =
    ψ ((((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) * X.map φ * (h : Matrix (Fin 3) (Fin 3) C)) a b) := by
  rw [← map_inv, ← Matrix.map_apply (f := ψ), Matrix.map_mul, Matrix.map_mul]
  rfl

private theorem triangular_form_map {φ : A →+* C} {h : GL (Fin 3) C} (ψ : C →+* C') (H : TriangularForm M d S T φ h) :
    TriangularForm M d S T (ψ.comp φ) (Matrix.GeneralLinearGroup.map ψ h) :=
  ⟨fun g hg a b hab => by rw [conjugate_entry_map, H.1 g hg a b hab, map_zero],
    fun g hg a => by rw [conjugate_entry_map, H.2 g hg a]; rfl⟩

private theorem triangular_form_of_injective_map {φ : A →+* C} {h : GL (Fin 3) C} (ψ : C →+* C') (hψ : Function.Injective ψ)
    (H : TriangularForm M d S T (ψ.comp φ) (Matrix.GeneralLinearGroup.map ψ h)) : TriangularForm M d S T φ h :=
  ⟨fun g hg a b hab => hψ (by rw [← conjugate_entry_map, H.1 g hg a b hab, map_zero]),
    fun g hg a => hψ (by rw [← conjugate_entry_map, H.2 g hg a]; rfl)⟩

private theorem triangular_mul_diag {X Y : Matrix (Fin 3) (Fin 3) C} (hX : X.BlockTriangular id) (hY : Y.BlockTriangular id)
    (a : Fin 3) : (X * Y) a a = X a a * Y a a := by
  rw [Matrix.mul_apply, Finset.sum_eq_single a]
  · intro b _ hb
    rcases lt_or_gt_of_ne hb with h | h
    · rw [hX h, zero_mul]
    · rw [hY h, mul_zero]
  · exact fun h => (h (Finset.mem_univ a)).elim

private theorem triangular_form_borel_change {φ : A →+* C} {h : GL (Fin 3) C} (hT : T ⊆ S) (H : TriangularForm M d S T φ h) (k : GL (Fin 3) C)
    (hk : ((k * h : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C).BlockTriangular id) : TriangularForm M d S T φ k⁻¹ := by
  obtain ⟨b, hb⟩ : ∃ b, b = k * h := ⟨_, rfl⟩
  rw [← hb] at hk
  obtain rfl : k = b * h⁻¹ := by rw [hb, mul_inv_cancel_right]
  have hi : ((b⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C).BlockTriangular id := by
    rw [Matrix.coe_units_inv]
    haveI := b.invertible
    exact Matrix.blockTriangular_inv_of_blockTriangular hk
  have e : ∀ X : Matrix (Fin 3) (Fin 3) C, (((b * h⁻¹)⁻¹⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) * X *
      ((b * h⁻¹)⁻¹ : GL (Fin 3) C) = b * (((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) * X * h) *
      (b⁻¹ : GL (Fin 3) C) := fun X => by
    simp only [inv_inv, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc]
  have hU : ∀ g ∈ S, (((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) * (M g).map φ * h).BlockTriangular id :=
    fun g hg a b hab => H.1 g hg a b hab
  refine ⟨fun g hg a c hac => ?_, fun g hg a => ?_⟩
  · rw [e]
    exact ((hk.mul (hU g hg)).mul hi) hac
  · rw [e, triangular_mul_diag (hk.mul (hU g (hT hg))) hi, triangular_mul_diag hk (hU g (hT hg)), H.2 g hg a, mul_right_comm,
      ← triangular_mul_diag hk hi, Units.mul_inv, Matrix.one_apply_eq, one_mul]

end

private theorem exists_sl2_valuation_kill {F : Type} [Field F] (V : ValuationSubring F) (a b : F) :
    ∃ x y z w : V, x * w - y * z = 1 ∧ (z : F) * a + w * b = 0 := by
  by_cases ha : a = 0
  · exact ⟨0, -1, 1, 0, by simp, by simp [ha]⟩
  by_cases hb : b = 0
  · exact ⟨1, 0, 0, 1, by simp, by simp [hb]⟩
  rcases V.mem_or_inv_mem (b / a) with h | h
  · exact ⟨1, 0, -⟨_, h⟩, 1, by simp, by simp [ha]⟩
  · exact ⟨0, -1, 1, -⟨_, h⟩, by simp, by simp [hb]⟩

private theorem valuation_ring_clear_last_row_entry {F : Type} [Field F] (V : ValuationSubring F) (Y : Matrix (Fin 3) (Fin 3) F) (c : Fin 3) :
    ∃ k : Matrix (Fin 3) (Fin 3) V, k.det = 1 ∧ (k.map V.subtype * Y) 2 c = 0 ∧
      (Y 1 0 = 0 → Y 2 0 = 0 → (k.map V.subtype * Y) 1 0 = 0 ∧ (k.map V.subtype * Y) 2 0 = 0) := by
  obtain ⟨x, y, z, w, h1, h2⟩ := exists_sl2_valuation_kill V (Y 1 c) (Y 2 c)
  refine ⟨!![1, 0, 0; 0, x, y; 0, z, w], ?_, ?_, fun e1 e2 => ⟨?_, ?_⟩⟩
  · simpa [Matrix.det_fin_three] using h1
  · simpa [Matrix.mul_apply, Fin.sum_univ_three] using h2
  · simp [Matrix.mul_apply, Fin.sum_univ_three, e1, e2]
  · simp [Matrix.mul_apply, Fin.sum_univ_three, e1, e2]

private theorem valuation_ring_clear_first_column {F : Type} [Field F] (V : ValuationSubring F) (Y : Matrix (Fin 3) (Fin 3) F) :
    ∃ k : Matrix (Fin 3) (Fin 3) V, k.det = 1 ∧ (k.map V.subtype * Y) 1 0 = 0 ∧
      (k.map V.subtype * Y) 2 0 = Y 2 0 := by
  obtain ⟨x, y, z, w, h1, h2⟩ := exists_sl2_valuation_kill V (Y 0 0) (Y 1 0)
  refine ⟨!![x, y, 0; z, w, 0; 0, 0, 1], ?_, ?_, ?_⟩
  · simpa [Matrix.det_fin_three] using h1
  · simpa [Matrix.mul_apply, Fin.sum_univ_three] using h2
  · simp [Matrix.mul_apply, Fin.sum_univ_three]

private theorem upper_triangular_of_entries_zero {F : Type} [Field F] {Z : Matrix (Fin 3) (Fin 3) F} (h1 : Z 1 0 = 0) (h2 : Z 2 0 = 0)
    (h3 : Z 2 1 = 0) : Z.BlockTriangular id := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | simpa

private theorem iwasawa_triangularization {F : Type} [Field F] (V : ValuationSubring F) (X : Matrix (Fin 3) (Fin 3) F) :
    ∃ k : GL (Fin 3) V, ((k : Matrix (Fin 3) (Fin 3) V).map V.subtype * X).BlockTriangular id := by
  obtain ⟨k1, d1, a1, -⟩ := valuation_ring_clear_last_row_entry V X 0
  obtain ⟨k2, d2, a2, b2⟩ := valuation_ring_clear_first_column V (k1.map V.subtype * X)
  obtain ⟨k3, d3, a3, b3⟩ := valuation_ring_clear_last_row_entry V (k2.map V.subtype * (k1.map V.subtype * X)) 1
  obtain ⟨b3, c3⟩ := b3 a2 (b2.trans a1)
  obtain ⟨k, hk⟩ := (Matrix.isUnit_iff_isUnit_det (k3 * (k2 * k1))).2
    (by rw [Matrix.det_mul, Matrix.det_mul, d1, d2, d3, one_mul, one_mul]; exact isUnit_one)
  refine ⟨k, ?_⟩
  rw [hk, Matrix.map_mul, Matrix.map_mul, Matrix.mul_assoc, Matrix.mul_assoc]
  exact upper_triangular_of_entries_zero b3 c3 a3

private theorem exists_common_ring_same_kernel {A K L : Type} [CommRing A] [Field K] [Field L] (f : A →+* K) (g : A →+* L)
    (h : RingHom.ker f = RingHom.ker g) :
    ∃ (T : Type) (_ : CommRing T) (_ : Nontrivial T) (i : K →+* T) (j : L →+* T), i.comp f = j.comp g := by
  letI : Algebra (A ⧸ RingHom.ker f) K := (RingHom.kerLift f).toAlgebra
  letI : Algebra (A ⧸ RingHom.ker f) L := (Ideal.Quotient.lift _ g fun a ha => by rwa [h] at ha).toAlgebra
  have h2 : Function.Injective (algebraMap (A ⧸ RingHom.ker f) L) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Ideal.Quotient.eq_zero_iff_mem, h]
    exact ha
  refine ⟨TensorProduct (A ⧸ RingHom.ker f) K L, inferInstance,
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain _ _ _ (RingHom.kerLift_injective f) h2,
    (Algebra.TensorProduct.includeLeft (S := A ⧸ RingHom.ker f)).toRingHom,
    Algebra.TensorProduct.includeRight.toRingHom, RingHom.ext fun a => ?_⟩
  exact ((Algebra.TensorProduct.includeLeft (S := A ⧸ RingHom.ker f) (A := K) (B := L)).commutes
    (Ideal.Quotient.mk _ a)).trans
    ((Algebra.TensorProduct.includeRight (A := K) (B := L)).commutes (Ideal.Quotient.mk _ a)).symm

private theorem triangular_form_finite_extension {ι A K B : Type} [CommRing A] [Field K] [CommRing B] [Nontrivial B]
    {M : ι → Matrix (Fin 3) (Fin 3) A} {d : ι → Fin 3 → A} {S T : Set ι} (f : A →+* K) (i : K →+* B)
    (h : GL (Fin 3) B) (H : TriangularForm M d S T (i.comp f) h) :
    ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K') (h' : GL (Fin 3) K'),
      TriangularForm M d S T ((algebraMap K K').comp f) h' := by
  classical
  letI := i.toAlgebra
  let s : Set B := Set.range (fun p : Fin 3 × Fin 3 => (h : Matrix (Fin 3) (Fin 3) B) p.1 p.2) ∪
    Set.range (fun p : Fin 3 × Fin 3 => ((h⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B) p.1 p.2)
  have hs : s.Finite := (Set.finite_range _).union (Set.finite_range _)
  let B₀ := Algebra.adjoin K s
  haveI : Algebra.FiniteType K B₀ := (Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_def.2 ⟨s, hs, rfl⟩)
  let X : Matrix (Fin 3) (Fin 3) B₀ := fun a b => ⟨_, Algebra.subset_adjoin (Or.inl ⟨(a, b), rfl⟩)⟩
  let Y : Matrix (Fin 3) (Fin 3) B₀ := fun a b => ⟨_, Algebra.subset_adjoin (Or.inr ⟨(a, b), rfl⟩)⟩
  have hXY : X * Y = 1 := by
    apply Matrix.map_injective (f := B₀.val.toRingHom) Subtype.val_injective
    show (X * Y).map B₀.val.toRingHom = (1 : Matrix (Fin 3) (Fin 3) B₀).map B₀.val.toRingHom
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact h.mul_inv
  let h₀ : GL (Fin 3) B₀ := ⟨X, Y, hXY, mul_eq_one_comm.1 hXY⟩
  have H0 : TriangularForm M d S T ((algebraMap K B₀).comp f) h₀ :=
    triangular_form_of_injective_map B₀.val.toRingHom Subtype.val_injective H
  obtain ⟨m, hm⟩ := Ideal.exists_maximal B₀
  letI := Ideal.Quotient.field m
  exact ⟨B₀ ⧸ m, inferInstance, inferInstance, finite_of_finite_type_of_isJacobsonRing K (B₀ ⧸ m), _,
    triangular_form_map (Ideal.Quotient.mk m) H0⟩

private theorem triangular_form_specialization {ι A F K : Type} [CommRing A] [Field F] [Field K]
    {M : ι → Matrix (Fin 3) (Fin 3) A} {d : ι → Fin 3 → A} {S T : Set ι} (hT : T ⊆ S) (φ : A →+* F) (f : A →+* K)
    (hf : RingHom.ker φ ≤ RingHom.ker f) (h : GL (Fin 3) F) (H : TriangularForm M d S T φ h) :
    ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K') (h' : GL (Fin 3) K'),
      TriangularForm M d S T ((algebraMap K K').comp f) h' := by
  haveI := RingHom.ker_isPrime f
  have hu : ∀ y : (RingHom.ker f).primeCompl, IsUnit (φ y) := fun y => Ne.isUnit fun e => y.2 (hf e)
  obtain ⟨V, hV, hl⟩ := IsLocalRing.exists_factor_valuationRing
    (IsLocalization.lift (S := Localization.AtPrime (RingHom.ker f)) hu)
  let g₀ : Localization.AtPrime (RingHom.ker f) →+* V := (IsLocalization.lift hu).codRestrict V.toSubring hV
  haveI : IsLocalHom g₀ := hl
  let g : A →+* V := g₀.comp (algebraMap _ _)
  have hg : V.subtype.comp g = φ := RingHom.ext fun a => IsLocalization.lift_eq hu a
  have hk : RingHom.ker f = RingHom.ker ((residue V).comp g) := by
    ext a
    rw [RingHom.mem_ker (f := (residue V).comp g), RingHom.comp_apply, residue_eq_zero_iff,
      ← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime (RingHom.ker f)) (RingHom.ker f) a,
      mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff]
    exact (isUnit_map_iff g₀ _).not.symm
  obtain ⟨k, hk'⟩ := iwasawa_triangularization V h
  have H1 := triangular_form_borel_change hT H (Matrix.GeneralLinearGroup.map V.subtype k) hk'
  rw [← map_inv, ← hg] at H1
  have H2 := triangular_form_map (residue V) (triangular_form_of_injective_map V.subtype Subtype.val_injective H1)
  obtain ⟨B, _, _, i, j, e⟩ := exists_common_ring_same_kernel f _ hk
  have H3 := triangular_form_map j H2
  rw [← e] at H3
  exact triangular_form_finite_extension f i _ H3

private theorem triangular_in_iff_triangular_form {O A C D : Type} [CommRing O] [CommRing A] [CommRing C] [Algebra O A] [Algebra O C] [Group D]
    (η : D →* ℤˣ) (Ψ : D →* Oˣ) (I : Subgroup D) (u : D →* GG (m := 3) (R := A)) (hu : HasMult η u) (φ : A →ₐ[O] C)
    (h : GL (Fin 3) C) : UpperTheory.V.UnitaryThreeInertia.TriIn η Ψ I (push φ u) h ↔
      TriangularForm (fun g => (u g).mat) (fun g a => algebraMap O A (UpperTheory.V.UnitaryThreeInertia.psi Ψ a g)) {g | η g = 1}
        {g | g ∈ I ∧ η g = 1} φ h := by
  have e : ∀ g, η g = 1 → (conjBy h⁻¹ (push φ u) g).mat =
      ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) * (u g).mat.map (φ : A →+* C) * h := by
    intro g hg
    have h1 : (push φ u g).right = 1 := (hu g).trans hg
    have h2 : (push φ u g).left.val = (u g).mat.map (φ : A →+* C) := rfl
    rw [← h2]
    simp [conjBy, GG.mat, h1]
  have hw : ∀ a b : Fin 3, wt a b < 0 ↔ b < a := by decide
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun g hg a b hab => ?_, fun g hg a => ?_⟩
    · rw [← e g hg]
      exact h1 g hg a b ((hw a b).2 hab)
    · rw [← e g hg.2, h2 g hg.1 hg.2 a]
      exact (φ.commutes _).symm
  · rintro ⟨h1, h2⟩
    refine ⟨fun g hg a b hab => ?_, fun g hg hg' a => ?_⟩
    · rw [e g hg]
      exact h1 g hg a b ((hw a b).1 hab)
    · rw [e g hg', h2 g ⟨hg, hg'⟩ a]
      exact φ.commutes _

end UpperTheory.V.Loc

theorem UpperTheory.V.Loc.lemma2c :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : _root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition O D.η D.Ψ)) (K : Type) [Field K] [Algebra O K] (r : GQ l →* GG (m := 3) (R := K)), D.On U r → ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (_ : Algebra O K') (_ : IsScalarTower O K K') (_ : FiniteDimensional K K') (h : GL (Fin 3) K'), UpperTheory.V.UnitaryThreeInertia.TriIn D.η D.Ψ (Iq l) ((GG.map (algebraMap K K')).comp r) h := by
  intro hP l _ O _ _ _ _ _ _ _ D U K _ _ r ⟨f, hr, hf⟩
  obtain ⟨-, hp, hl, -⟩ := UpperTheory.V.Loc.rtBasic hP D U
  haveI : IsDomain (D.Rt U) := Ideal.Quotient.isDomain _
  let φ : U.R →ₐ[O] FractionRing (D.Rt U) :=
    (IsScalarTower.toAlgHom O (D.Rt U) (FractionRing (D.Rt U))).comp (Ideal.Quotient.mkₐ O _)
  have hφ : RingHom.ker φ = D.It U := by
    ext a
    rw [RingHom.mem_ker, ← Ideal.Quotient.eq_zero_iff_mem]
    exact map_eq_zero_iff _ (IsFractionRing.injective (D.Rt U) (FractionRing (D.Rt U)))
  have hl0 : ((l : ℕ) : FractionRing (D.Rt U)) ≠ 0 := fun e => hl (by rw [← hφ, RingHom.mem_ker, map_natCast, e])
  haveI : Nontrivial (FractionRing (D.Rt U)) := nontrivial_of_ne _ _ hl0
  haveI : CharZero (FractionRing (D.Rt U)) := by
    refine charZero_of_inj_zero fun n hn => ?_
    by_contra h0
    have h1 : (n : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.2 h0
    have h2 := congrArg ((algebraMap O (FractionRing (D.Rt U))).comp (algebraMap ℤ_[l] O))
      (PadicInt.unitCoeff_spec h1)
    rw [map_natCast, hn, map_mul, map_pow, map_natCast] at h2
    exact mul_ne_zero ((Units.isUnit _).map _).ne_zero (pow_ne_zero _ hl0) h2.symm
  obtain ⟨⟨h, H⟩, -⟩ := UpperTheory.V.Loc.lemma2b hP D U _ (push φ U.r.hom) ⟨φ, rfl, hφ.ge⟩
  rw [UpperTheory.V.Loc.triangular_in_iff_triangular_form _ _ _ _ U.r.hasMult] at H
  have hT : {g : GQ l | g ∈ Iq l ∧ D.η g = 1} ⊆ {g | D.η g = 1} := fun _ hg => hg.2
  obtain ⟨K', _, _, _, h', H'⟩ :=
    UpperTheory.V.Loc.triangular_form_specialization hT _ (f : U.R →+* K) (hφ.le.trans hf) h H
  letI : Algebra O K' := ((algebraMap K K').comp (algebraMap O K)).toAlgebra
  haveI : IsScalarTower O K K' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  refine ⟨K', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, h', ?_⟩
  subst hr
  exact (UpperTheory.V.Loc.triangular_in_iff_triangular_form _ _ _ _ U.r.hasMult ((IsScalarTower.toAlgHom O K K').comp f) h').2 H'
end

open NumberField IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr UpperTheory.V

private theorem go_up {K : Type} [Field K] (T m : Matrix (Fin 3) (Fin 3) K) (d : Fin 3 → K)
    (hT : T.BlockTriangular id) (hd : ∀ a b, a ≠ b → T b b ≠ d a) (e : T * m = m * Matrix.diagonal d) :
    m.BlockTriangular id := by
  have t10 : T 1 0 = 0 := hT (by decide)
  have t20 : T 2 0 = 0 := hT (by decide)
  have t21 : T 2 1 = 0 := hT (by decide)
  have e' : ∀ b a, T b 0 * m 0 a + T b 1 * m 1 a + T b 2 * m 2 a = m b a * d a := fun b a => by
    have := congrFun (congrFun e b) a
    rwa [Matrix.mul_diagonal, Matrix.mul_apply, Fin.sum_univ_three] at this
  have h2 : ∀ a, a ≠ 2 → m 2 a = 0 := fun a ha => by
    have := e' 2 a
    rw [t20, t21] at this
    refine (mul_eq_zero.1 (?_ : (T 2 2 - d a) * m 2 a = 0)).resolve_left (sub_ne_zero.2 (hd a 2 ha))
    linear_combination this
  have h1 : m 1 0 = 0 := by
    have := e' 1 0
    rw [t10, h2 0 (by decide)] at this
    refine (mul_eq_zero.1 (?_ : (T 1 1 - d 0) * m 1 0 = 0)).resolve_left (sub_ne_zero.2 (hd 0 1 (by decide)))
    linear_combination this
  have h20 := h2 0 (by decide)
  have h21 := h2 1 (by decide)
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | simpa

private theorem go_diag {C : Type} [CommRing C] {X Y : Matrix (Fin 3) (Fin 3) C} (hX : X.BlockTriangular id)
    (hY : Y.BlockTriangular id) (a : Fin 3) : (X * Y) a a = X a a * Y a a := by
  rw [Matrix.mul_apply, Finset.sum_eq_single a]
  · intro b _ hb
    rcases lt_or_gt_of_ne hb with h | h
    · rw [hX h, zero_mul]
    · rw [hY h, mul_zero]
  · exact fun h => (h (Finset.mem_univ a)).elim

private theorem go_conj {K : Type} [Field K] (m : GL (Fin 3) K) (hm : m.val.BlockTriangular id)
    (Y : Matrix (Fin 3) (Fin 3) K) (hY : Y.BlockTriangular id) :
    ((m⁻¹).val * Y * m.val).BlockTriangular id ∧ ∀ a, ((m⁻¹).val * Y * m.val) a a = Y a a := by
  have hi : (m⁻¹).val.BlockTriangular id := by
    rw [Matrix.coe_units_inv]
    haveI := m.invertible
    exact Matrix.blockTriangular_inv_of_blockTriangular hm
  refine ⟨(hi.mul hY).mul hm, fun a => ?_⟩
  rw [go_diag (hi.mul hY) hm, go_diag hi hY, mul_right_comm, ← go_diag hi hm, Units.inv_mul, Matrix.one_apply_eq,
    one_mul]

private theorem go_mat {D C : Type} [Group D] [CommRing C] (r : D →* GG (m := 3) (R := C)) (h : GL (Fin 3) C) (g : D)
    (hg : (r g).right = 1) : (conjBy h⁻¹ r g).mat = (h⁻¹).val * (r g).mat * h.val := by
  simp [conjBy, GG.mat, hg]

private theorem diagonal_character_rep_matrix {O D : Type} [CommRing O] [Group D] (η : D →* ℤˣ) (Ψ : D →* Oˣ) (g : D) :
    (r0 η Ψ g).mat = Matrix.diagonal fun a => UnitaryThreeInertia.psi Ψ a g := rfl

private theorem go_unit {O D : Type} [CommRing O] [Group D] (Ψ : D →* Oˣ) (x : D)
    (hu : IsUnit ((Ψ x : O) ^ 2 - 1)) (a b : Fin 3) (hab : a ≠ b) : IsUnit (UnitaryThreeInertia.psi Ψ a x - UnitaryThreeInertia.psi Ψ b x) := by
  have e0 : UnitaryThreeInertia.psi Ψ 0 x = Ψ x := by simp [UnitaryThreeInertia.psi, wt1]
  have e1 : UnitaryThreeInertia.psi Ψ 1 x = 1 := by simp [UnitaryThreeInertia.psi, wt1]
  have e2 : UnitaryThreeInertia.psi Ψ 2 x = ((Ψ x)⁻¹ : Oˣ) := by simp [UnitaryThreeInertia.psi, wt1]
  generalize Ψ x = t at *
  have ht : (t : O) * (t⁻¹ : Oˣ) = 1 := Units.mul_inv t
  have h01 : IsUnit (UnitaryThreeInertia.psi Ψ 0 x - UnitaryThreeInertia.psi Ψ 1 x) := by
    rw [e0, e1]
    exact isUnit_of_mul_isUnit_left (y := (t : O) + 1) (by convert hu using 1; ring)
  have h02 : IsUnit (UnitaryThreeInertia.psi Ψ 0 x - UnitaryThreeInertia.psi Ψ 2 x) := by
    rw [e0, e2]
    exact isUnit_of_mul_isUnit_left (y := (t : O)) (by convert hu using 1; linear_combination -ht)
  have h12 : IsUnit (UnitaryThreeInertia.psi Ψ 1 x - UnitaryThreeInertia.psi Ψ 2 x) := by
    rw [e1, e2]
    exact isUnit_of_mul_isUnit_left (y := (t : O) * (t + 1))
      (by convert hu using 1; linear_combination (-(t : O) - 1) * ht)
  have hs : ∀ {u v : O}, IsUnit (u - v) → IsUnit (v - u) := fun h => by rw [← neg_sub]; exact h.neg
  fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | assumption | exact hs (by assumption)

private theorem go_uadd {A : Type} [CommRing A] [IsLocalRing A] {u v : A} (hu : IsUnit u) (h : v - u ∈ maximalIdeal A) :
    IsUnit v := by
  by_contra hv
  have h1 : v ∈ maximalIdeal A := hv
  have h2 : u ∈ maximalIdeal A := by simpa using Ideal.sub_mem _ h1 h
  exact h2 hu

private theorem triangular_of_reducible_rank_three {O A K D : Type} [CommRing O] [IsLocalRing O] [CommRing A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] [Algebra O A] [Field K] [Algebra O K] [Group D]
    (η : D →* ℤˣ) (Ψ : D →* Oˣ) (I : Subgroup D) (r : D →* GG (m := 3) (R := A)) (hr : UnitaryThreeInertia.Red η Ψ r) (j : A →ₐ[O] K)
    (hj : Function.Injective j) (x : D) (hx : x ∈ I) (hη : η x = 1) (hu : IsUnit ((Ψ x : O) ^ 2 - 1))
    (k : GL (Fin 3) K) (hk : UnitaryThreeInertia.TriIn η Ψ I (push j r) k) : UnitaryThreeInertia.CondT η Ψ I r := by
  have hw : ∀ a b : Fin 3, wt a b < 0 ↔ b < a := by decide
  have hd : ∀ a, (r x).mat a a - algebraMap O A (UnitaryThreeInertia.psi Ψ a x) ∈ maximalIdeal A := fun a => by
    simpa [diagonal_character_rep_matrix] using hr.red x a a
  have ho : ∀ a b, a ≠ b → (r x).mat a b ∈ maximalIdeal A := fun a b hab => by
    simpa [diagonal_character_rep_matrix, hab] using hr.red x a b
  have hU := fun a b hab => (go_unit Ψ x hu a b hab).map (algebraMap O A)
  obtain ⟨h, h1, h2, h3⟩ := UnitaryThreeInertia.exists_canon (r x).mat (fun a b hab => go_uadd (hU a b hab) (by
    convert Ideal.sub_mem _ (hd a) (hd b) using 1
    rw [map_sub]; ring)) ho
  obtain ⟨d, hdd⟩ : ∃ d, Matrix.diagonal d = (h⁻¹).val * (r x).mat * h.val := ⟨_, h3.diagonal_diag⟩
  have hX : (r x).mat * h.val = h.val * Matrix.diagonal d := by
    rw [hdd, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  have hdm : ∀ a, d a - (r x).mat a a ∈ maximalIdeal A := fun a => by
    have e := congrFun (congrFun hX a) a
    rw [Matrix.mul_diagonal, h2, one_mul, Matrix.mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ a), h2,
      mul_one] at e
    rw [← e, add_sub_cancel_left]
    exact Ideal.sum_mem _ fun b hb => Ideal.mul_mem_right _ _ (ho a b (Finset.ne_of_mem_erase hb).symm)
  let h' : GL (Fin 3) K := Matrix.GeneralLinearGroup.map (j : A →+* K) h
  have hm : ∀ g, η g = 1 → (push j r g).right = 1 := fun g hg => (hr.mult g).trans hg
  have hT : ∀ g, η g = 1 → ((k⁻¹).val * (push j r g).mat * k.val).BlockTriangular id := fun g hg a b hab => by
    rw [← go_mat _ _ _ (hm g hg)]
    exact hk.tri g hg a b ((hw a b).2 hab)
  have hI : ∀ g ∈ I, η g = 1 → ∀ a, ((k⁻¹).val * (push j r g).mat * k.val) a a = algebraMap O K (UnitaryThreeInertia.psi Ψ a g) :=
    fun g hg hg' a => by
      rw [← go_mat _ _ _ (hm g hg')]
      exact hk.ine g hg hg' a
  have hup : (k⁻¹ * h').val.BlockTriangular id := by
    refine go_up _ _ (fun a => j (d a)) (hT x hη) (fun a b hab => ?_) ?_
    · rw [hI x hx hη, ← j.commutes, ← sub_ne_zero, ← map_sub]
      refine ((go_uadd (hU b a hab.symm) ?_).map j).ne_zero
      convert (maximalIdeal A).neg_mem (Ideal.add_mem _ (hdm a) (hd a)) using 1
      rw [map_sub]; ring
    · have e := congrArg (fun M => M.map (j : A →+* K)) hX
      simp only [Matrix.map_mul, Matrix.diagonal_map (map_zero (j : A →+* K))] at e
      rw [Units.val_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc k.val, Units.mul_inv, Matrix.one_mul,
        Matrix.mul_assoc]
      exact congrArg _ e
  have key : ∀ g, η g = 1 → ∀ a b, j ((conjBy h⁻¹ r g).mat a b) =
      (((k⁻¹ * h')⁻¹).val * ((k⁻¹).val * (push j r g).mat * k.val) * (k⁻¹ * h').val) a b := fun g hg a b => by
    have e : ((k⁻¹ * h')⁻¹).val * ((k⁻¹).val * (push j r g).mat * k.val) * (k⁻¹ * h').val =
        (h'⁻¹).val * (push j r g).mat * h'.val := by
      simp only [_root_.mul_inv_rev, inv_inv, Units.val_mul, Matrix.mul_assoc, Units.mul_inv_cancel_left]
    rw [e, go_mat _ _ _ ((hr.mult g).trans hg), ← map_inv]
    show ((h⁻¹).val * (r g).mat * h.val).map (j : A →+* K) a b = _
    rw [Matrix.map_mul, Matrix.map_mul]
    rfl
  refine ⟨h, h1, fun g hg a b hab => hj ?_, fun g hg hg' a => hj ?_⟩
  · rw [key g hg, map_zero]
    exact (go_conj _ hup _ (hT g hg)).1 ((hw a b).1 hab)
  · rw [key g hg', (go_conj _ hup _ (hT g hg')).2, hI g hg hg', j.commutes]

private theorem go_tr {O A H G : Type} [CommRing O] [CommRing A] [Algebra O A] [Group H] [Group G]
    (η : G →* ℤˣ) (Ψ : G →* Oˣ) (r : G →* GG (m := 3) (R := A)) (ι : H →* G) (J : Subgroup H) (Dc In : Subgroup G)
    (hD : ι.range = Dc) (hI : J.map ι = In) (k : GL (Fin 3) A)
    (hk : UnitaryThreeInertia.TriIn (η.comp ι) (Ψ.comp ι) J (r.comp ι) k) :
    UnitaryThreeInertia.TriIn (η.comp Dc.subtype) (Ψ.comp Dc.subtype) (In.subgroupOf Dc) (r.comp Dc.subtype) k := by
  subst hD hI
  constructor
  · rintro ⟨_, σ, rfl⟩ hg
    exact hk.tri σ hg
  · rintro ⟨s, hs⟩ ⟨σ, hσ, e⟩ hg
    obtain rfl : ι σ = s := e
    exact hk.ine σ hσ hg

private theorem go_r0map {G A B : Type} [Group G] [CommRing A] [CommRing B] (φ : A →+* B) (η : G →* ℤˣ) (Ψ : G →* Aˣ)
    (g : G) (a b : Fin 3) :
    (r0 η ((Units.map φ.toMonoidHom).comp Ψ) g).mat a b = φ ((r0 η Ψ g).mat a b) := by
  simp only [GG.mat, unitaryThreeReflection_left, tor_val]
  by_cases h : a = b
  · subst h
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
    exact (congrArg Units.val (map_zpow (Units.map φ.toMonoidHom) (Ψ g) (wt1 a))).symm
  · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h, map_zero]

private theorem go_push {O R A Γ : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [Alg.IsCO O R]
    [CommRing A] [IsLocalRing A] [Algebra O A] [Group Γ] [TopologicalSpace Γ] {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ}
    (r : GLift O η Ψ R) (f : R →ₐ[O] A) (hf : IsLocalHom f) :
    UnitaryThreeInertia.Red η Ψ (push f r.hom) ∧ UnitaryThreeInertia.AdicCont (maximalIdeal A) (push f r.hom) := by
  have hm : ∀ y ∈ maximalIdeal R, f y ∈ maximalIdeal A := fun y hy hu => hy (hf.map_nonunit y hu)
  refine ⟨⟨fun g => r.hasMult g, fun g a b => ?_⟩, fun n => ?_⟩
  · show f ((r.hom g).mat a b) - algebraMap O A ((r0 η Ψ g).mat a b) ∈ _
    rw [← f.commutes, ← map_sub]
    refine hm _ ((Alg.res_eq_zero_iff O R _).1 ?_)
    have h2 : Alg.res O R ((r.hom g).mat a b) = (rbar O η Ψ g).mat a b :=
      congrArg (fun x : GG (m := 3) (R := ResidueField O) => x.mat a b) (r.red g)
    have h3 : (rbar O η Ψ g).mat a b = residue O ((r0 η Ψ g).mat a b) := go_r0map _ _ _ _ _ _
    rw [map_sub, AlgHom.commutes, h2, h3]
    exact sub_self _
  · have hle : maximalIdeal R ^ n ≤ (maximalIdeal A ^ n).comap (f : R →+* A) :=
      le_trans (Ideal.pow_right_mono (fun y hy => hm y hy) n) (Ideal.le_comap_pow _ n)
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun g => ?_
    have h := fun p : Fin 3 × Fin 3 =>
      ((r.cont p.1 p.2 n).comp (Ideal.quotientMap _ (f : R →+* A) hle)).eventually_eq g
    filter_upwards [Filter.eventually_all.2 h] with g' hg'
    exact Matrix.ext fun a b => hg' (a, b)

theorem UpperTheory.V.Pr.ordPt_of_gd :
    Loc.LocalPublishedTheorems → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) (g₁ : G ℚ Ω), D.Marked g₁ → ∀ (U : (_root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition _ (D.η.comp D.ι) (D.Ψ.comp D.ι)))) (S : D.Ring U g₁),
    ∀ (B : ValuationSubring Ω), (∀ x, x ∈ B ↔ ‖D.j x‖ ≤ 1) → ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsAdicComplete (maximalIdeal A) A] [Algebra c.O A] (f : S.R →ₐ[c.O] A), IsLocalHom f →
      OrdPt l D.η D.Ψ D.cc g₁ B (U3.push f S.r.hom) := by
  intro hP Ω _ _ _ K _ _ _ l _ c N _ e ψ D g₁ _ U S B hB A _ _ _ _ _ f hf
  have hid : S.r.map (AlgHom.id c.O S.R) = S.r := GLift.ext rfl
  have h0 := (S.rep S.R).1 (AlgHom.id c.O S.R)
  rw [hid] at h0
  obtain ⟨hn, hk, φ, hφ, hI⟩ := h0
  obtain ⟨hred, hcont⟩ := go_push S.r f hf
  obtain ⟨B₀, hl, hD, hIn, -, hB₀, -⟩ := dat_loc D
  obtain rfl : B = B₀ := ValuationSubring.ext _ _ fun x => (hB x).trans (hB₀ x).symm
  refine ⟨hred, hcont, ⟨?_, ?_, ?_⟩, fun B' hB' s hs hη hΨ => ?_, ?_⟩
  · show (S.r.hom D.cc).mat.map (f : S.R →+* A) = 1
    rw [hn.atc, Matrix.map_one _ (map_zero _) (map_one _)]
  · have := congrArg f hn.z12
    rw [map_zero, zmat, Matrix.sub_apply, map_sub] at this
    exact this
  · have := congrArg f hn.z21
    rw [map_zero, zmat, Matrix.sub_apply, map_sub] at this
    exact this
  · show GG.map (f : S.R →+* A) (S.r.hom s) = 1
    rw [hk s ⟨B', hB', hs, ?_⟩, map_one]
    refine SemidirectProduct.ext ?_ hη
    show tor _ (Units.map _ (D.Ψ s)) = 1
    rw [hΨ, map_one, map_one]
  · obtain ⟨hη, x, hx, hu⟩ := (dat_facts D).2.2.2.2.2.2.2.2.2.2 B hl
    let j₀ : A →ₐ[c.O] FractionRing A := IsScalarTower.toAlgHom c.O A (FractionRing A)
    have h1 : (U.r.map φ).hom = S.r.hom.comp D.ι := congrArg GLift.hom hφ
    obtain ⟨K', _, _, _, _, _, k, hk'⟩ := @Loc.lemma2c hP l _ c.O _ _ c.dvr _ _ c.fin
      (UpperTheory.V.Base.dvrFacts l c.O).2.2.2.1 D.loc U (FractionRing A) _ _
      ((push j₀ (push f S.r.hom)).comp D.ι) ⟨j₀.comp (f.comp φ), by
        refine MonoidHom.ext fun g => ?_
        show GG.map (j₀ : A →+* FractionRing A) (GG.map (f : S.R →+* A) ((U.r.map φ).hom g)) = _
        rw [h1]
        rfl, fun y hy => by
        have : φ y = 0 := hI hy
        show j₀ (f (φ y)) = 0
        rw [this, map_zero, map_zero]⟩
    let j : A →ₐ[c.O] K' := (IsScalarTower.toAlgHom c.O (FractionRing A) K').comp j₀
    have hj : Function.Injective j :=
      (algebraMap (FractionRing A) K').injective.comp (IsFractionRing.injective A (FractionRing A))
    exact triangular_of_reducible_rank_three _ _ _ _ ⟨fun g => hred.mult _, fun g => hred.red _⟩ j hj ⟨x, hx.1⟩ hx (hη hx) hu k
      (go_tr D.η D.Ψ (push j (push f S.r.hom)) D.ι (Loc.Iq l) _ _ hD hIn k hk')
