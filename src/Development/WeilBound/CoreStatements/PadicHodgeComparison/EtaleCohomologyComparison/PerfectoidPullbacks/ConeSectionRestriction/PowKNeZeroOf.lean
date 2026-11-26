module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalLatticeGaussSumEstimate
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedCoverVanishingInduction
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousRatioIsUnit
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProjectiveChartAffineCoords
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalRestrictSection
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalRestrictSection
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeEval

theorem ev_rs_eq : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} (T : Thick (smFun X q))
    {V W : X.Opens} (h : V ≤ W) (hT : InU V T) (hT' : InU W T) (s : Γ(X, W)), ev T hT (rs h s) = ev T hT' s := by
  intro K _ X q T V W h hT hT' s
  have e : X.presheaf.map (homOfLE h).op ≫ (pt T).appLE V ⊤ hT = (pt T).appLE W ⊤ hT' :=
    Scheme.Hom.map_appLE _ _ _
  unfold ev rs GlobalTheory.Cris.evalAt
  rw [← e]
  rfl

end GlobalTheory.CompanionTheory.ConeEval
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalRestrictSectionStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eval_restrict_section : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} (T : Thick (smFun X q))
    {V W : X.Opens} (h : V ≤ W) (hT : InU V T) (hT' : InU W T) (s : Γ(X, W)), ev T hT (rs h s) = ev T hT' s := by
  first | exact @GlobalTheory.CompanionTheory.ConeEval.ev_rs_eq | exact GlobalTheory.CompanionTheory.ConeEval.ev_rs_eq | (intros; apply GlobalTheory.CompanionTheory.ConeEval.ev_rs_eq <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictAppLECompat
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictAppLECompat
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeRs

theorem rs_appLE_apply {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) {V W : X.Opens} (h : V ≤ W) (hW : W ≤ f ⁻¹ᵁ U)
    (s : Γ(Y, U)) : rs h ((f.appLE U W hW).hom s) = (f.appLE U V (h.trans hW)).hom s := by
  change ((f.appLE U W hW) ≫ X.presheaf.map (homOfLE h).op).hom s = _
  rw [Scheme.Hom.appLE_map]

end GlobalTheory.CompanionTheory.ConeRs
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictAppLECompatStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restrict_appLE_compat : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) {V W : X.Opens} (h : V ≤ W) (hW : W ≤ f ⁻¹ᵁ U)
    (s : Γ(Y, U)), rs h ((f.appLE U W hW).hom s) = (f.appLE U V (h.trans hW)).hom s := by
  first | exact @GlobalTheory.CompanionTheory.ConeRs.rs_appLE_apply | exact GlobalTheory.CompanionTheory.ConeRs.rs_appLE_apply | (intros; apply GlobalTheory.CompanionTheory.ConeRs.rs_appLE_apply <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningFiltrationIsFilStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thickening_filtration_isFil : ∀ {b : Base} (L : b.Fun), IsFil (thP L) (thFil L) := by
  first | exact @GlobalTheory.CompanionTheory.DPFil.isFil_thFil | exact GlobalTheory.CompanionTheory.DPFil.isFil_thFil | (intros; apply GlobalTheory.CompanionTheory.DPFil.isFil_thFil <;> assumption)
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacobianSpanLeSubalgebra
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacobianSpanLeSubalgebra
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.Cone

theorem jacSpan_le_jacS : ∀ {K : Type} [Field K] {X : Scheme.{0}} {V W : X.Opens} (h : V ≤ W) [Algebra K Γ(X, V)]
    (B : Subalgebra K Γ(X, V)), (B : Set Γ(X, V)) = Set.range (rs h) →
    ∀ {d m : ℕ} (D : Fin d → Derivation K Γ(X, V) Γ(X, V)) (κ : Fin m → Fin d),
    jacSpan h (RingHom.id _) (fun k => D k) κ ≤ jacS B D κ := by
  intro K _ X V W h _ B hB d m D κ
  refine (AddSubgroup.closure_le _).2 ?_
  rintro y ⟨b, bs, rfl⟩
  have hm : ∀ c : Γ(X, W), rs h c ∈ B := fun c => by
    have : rs h c ∈ (B : Set Γ(X, V)) := hB ▸ Set.mem_range_self c
    exact this
  exact AddSubgroup.subset_closure ⟨⟨rs h b, hm b⟩, fun l => ⟨rs h (bs l), hm (bs l)⟩, rfl⟩

end GlobalTheory.CompanionTheory.Cone
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacobianSpanLeSubalgebraStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacobian_span_le_subalgebra : ∀ {K : Type} [Field K] {X : Scheme.{0}} {V W : X.Opens} (h : V ≤ W) [Algebra K Γ(X, V)]
    (B : Subalgebra K Γ(X, V)), (B : Set Γ(X, V)) = Set.range (rs h) →
    ∀ {d m : ℕ} (D : Fin d → Derivation K Γ(X, V) Γ(X, V)) (κ : Fin m → Fin d),
    jacSpan h (RingHom.id _) (fun k => D k) κ ≤ jacS B D κ := by
  first | exact @GlobalTheory.CompanionTheory.Cone.jacSpan_le_jacS | exact GlobalTheory.CompanionTheory.Cone.jacSpan_le_jacS | (intros; apply GlobalTheory.CompanionTheory.Cone.jacSpan_le_jacS <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusJacobianDet
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusJacobianDet
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.Cone

theorem dlog_ratio_det {K R : Type} [Field K] [CommRing R] [Algebra K R] (n : ℕ) (t : Fin (n + 1) → Rˣ)
    (D : Fin (n + 1) → Derivation K R R) (hD : ∀ k j, D k (t j) = if k = j then 1 else 0) :
    let g : Fin (n + 1) → R := fun k => if h : (k : ℕ) = 0 then ((t 0)⁻¹ : Rˣ) else
      (t ⟨k - 1, by omega⟩ : R) * ((t k)⁻¹ : Rˣ)
    Ring.inverse (∏ k, g k) * (Matrix.of fun k l => D k (g l)).det = (((∏ k, t k)⁻¹ : Rˣ) : R) ∨
    Ring.inverse (∏ k, g k) * (Matrix.of fun k l => D k (g l)).det = -(((∏ k, t k)⁻¹ : Rˣ) : R) := by
  intro g
  set u : Fin (n + 1) → R := fun j => (((t j)⁻¹ : Rˣ) : R) with hu
  have htu : ∀ j, (t j : R) * u j = 1 := fun j => by simp [hu]
  have hDu : ∀ k j, D k (u j) = if k = j then -(u j * u j) else 0 := by
    intro k j
    have h2 := (D k).leibniz_of_mul_eq_one (a := u j) (b := (t j : R)) (by rw [mul_comm]; exact htu j)
    rw [h2, hD k j]
    split_ifs <;> simp [pow_two]
  have hg0 : g 0 = u 0 := by simp [g, hu]
  have hgs : ∀ (l : Fin (n + 1)) (h : (l : ℕ) ≠ 0), g l = (t ⟨l - 1, by omega⟩ : R) * u l := by
    intro l h
    exact dif_neg h
  have hgu : ∀ l, IsUnit (g l) := by
    intro l
    by_cases h : (l : ℕ) = 0
    · simp only [g, h, dite_true]; exact Units.isUnit _
    · simp only [g, h, dite_false]; exact (Units.isUnit _).mul (Units.isUnit _)
  let B : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
    Matrix.of fun k l => if k = l then -1 else if (k : ℕ) + 1 = l then 1 else 0
  have hM : (Matrix.of fun k l => D k (g l)) = Matrix.diagonal u * B * Matrix.diagonal g := by
    ext k l
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [Matrix.of_apply, B]
    by_cases h : (l : ℕ) = 0
    · have hl : l = 0 := Fin.ext h
      subst hl
      have hk : ¬ ((k : ℕ) + 1 = ((0 : Fin (n + 1)) : ℕ)) := by simp
      rw [hg0, hDu k 0]
      by_cases hk0 : k = 0
      · subst hk0; simp
      · simp [hk0]
    · rw [hgs l h, Derivation.leibniz, hDu k l, hD k _]
      simp only [smul_eq_mul]
      by_cases hkl : k = l
      · subst hkl
        have hne : k ≠ ⟨(k : ℕ) - 1, by omega⟩ := by
          intro e
          have := congrArg Fin.val e
          simp at this
          omega
        simp only [if_true, hne, if_false]
        ring
      · by_cases hs : (k : ℕ) + 1 = l
        · have hp : k = ⟨(l : ℕ) - 1, by omega⟩ := Fin.ext (by simp; omega)
          rw [if_neg hkl, if_pos hp, if_neg hkl, if_pos hs, ← hp]
          have := htu k
          linear_combination (-(u l)) * this
        · have hp : k ≠ ⟨(l : ℕ) - 1, by omega⟩ := by
            intro e
            have := congrArg Fin.val e
            simp at this
            omega
          rw [if_neg hkl, if_neg hp, if_neg hkl, if_neg hs]
          simp
  have hB : B.det = (-1) ^ (n + 1) := by
    rw [Matrix.det_of_upperTriangular]
    · simp [B]
    · intro i j hij
      have : (j : ℕ) < i := hij
      have h1 : i ≠ j := fun h => by simp [h] at this
      have h2 : ¬ ((i : ℕ) + 1 = j) := by omega
      simp [B, h1, h2]
  have hprod : ∏ k, u k = (((∏ k, t k)⁻¹ : Rˣ) : R) := by
    simp only [hu, ← Units.coe_prod, Finset.prod_inv_distrib]
  have hU : IsUnit (∏ k, g k) := by
    obtain ⟨v, hv⟩ := IsUnit.prod_univ_iff.2 hgu
    exact hv ▸ v.isUnit
  have hcan : Ring.inverse (∏ k, g k) * (∏ k, g k) = 1 := Ring.inverse_mul_cancel _ hU
  have key : Ring.inverse (∏ k, g k) * (Matrix.of fun k l => D k (g l)).det =
      (-1) ^ (n + 1) * (((∏ k, t k)⁻¹ : Rˣ) : R) := by
    rw [hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal, hB, hprod]
    linear_combination ((-1) ^ (n + 1) * (((∏ k, t k)⁻¹ : Rˣ) : R)) * hcan
  rcases neg_one_pow_eq_or R (n + 1) with h | h
  · left; rw [key, h, one_mul]
  · right; rw [key, h, neg_one_mul]

end GlobalTheory.CompanionTheory.Cone
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusJacobianDetStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_jacobian_det : ∀ {K R : Type} [Field K] [CommRing R] [Algebra K R] (n : ℕ) (t : Fin (n + 1) → Rˣ)
    (D : Fin (n + 1) → Derivation K R R), (∀ k j, D k (t j) = if k = j then 1 else 0) →
    let g : Fin (n + 1) → R := fun k => if h : (k : ℕ) = 0 then ((t 0)⁻¹ : Rˣ) else
      (t ⟨k - 1, by omega⟩ : R) * ((t k)⁻¹ : Rˣ)
    Ring.inverse (∏ k, g k) * (Matrix.of fun k l => D k (g l)).det = (((∏ k, t k)⁻¹ : Rˣ) : R) ∨
    Ring.inverse (∏ k, g k) * (Matrix.of fun k l => D k (g l)).det = -(((∏ k, t k)⁻¹ : Rˣ) : R) := by
  first | exact @GlobalTheory.CompanionTheory.Cone.dlog_ratio_det | exact GlobalTheory.CompanionTheory.Cone.dlog_ratio_det | (intros; apply GlobalTheory.CompanionTheory.Cone.dlog_ratio_det <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CupPowerSmul
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CupPowerSmul
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConePow

theorem cupPowC_smul {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (A : C ⥤ CommAlgCat.{0} R)
    (z : CH.Cn (CH.modF A) 2) (a : R) (k : ℕ) : cupPowC A (a • z) k = a ^ k • cupPowC A z k := by
  induction k with
  | zero => rw [pow_zero, one_smul]; rfl
  | succ k ih =>
    change (CH.mulP A).cupC (by omega) (cupPowC A (a • z) k) (a • z) =
      a ^ (k + 1) • (CH.mulP A).cupC (by omega) (cupPowC A z k) z
    rw [ih, map_smul, map_smul, LinearMap.smul_apply, pow_succ', mul_smul]

end GlobalTheory.CompanionTheory.ConePow
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CupPowerSmulStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cup_power_smul : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (A : C ⥤ CommAlgCat.{0} R)
    (z : CH.Cn (CH.modF A) 2) (a : R) (k : ℕ), cupPowC A (a • z) k = a ^ k • cupPowC A z k := by
  first | exact @GlobalTheory.CompanionTheory.ConePow.cupPowC_smul | exact GlobalTheory.CompanionTheory.ConePow.cupPowC_smul | (intros; apply GlobalTheory.CompanionTheory.ConePow.cupPowC_smul <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitClassNeZeroOfNonempty
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitClassNeZeroOfNonempty
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.ConeOne

variable {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))

def resI (x : X) : K →+* X.residueField x :=
  (Spec.preimage (X.fromSpecResidueField x ≫ q)).hom

theorem spec_resI (x : X) :
    Spec.map (CommRingCat.ofHom (resI q x)) = X.fromSpecResidueField x ≫ q := by
  have : CommRingCat.ofHom (resI q x) = Spec.preimage (X.fromSpecResidueField x ≫ q) := rfl
  rw [this, Spec.map_preimage]

def resPt (x : X) : PtOver X q (Ideal.Quotient.mk (⊥ : Ideal K))
    (X.residueField x ⧸ (⊥ : Ideal (X.residueField x))) :=
  ⟨(Ideal.quotientMap ⊥ (resI q x) bot_le,
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (⊥ : Ideal (X.residueField x)))) ≫ X.fromSpecResidueField x), by
    rw [Category.assoc, ← spec_resI, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl⟩

def resT (x : X) : Thick (smFun X q) :=
  mkT (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (X.residueField x) (resI q x) ⊥
    (dividedPowersBot _)
    ⟨fun h => absurd rfl h, fun _ => ⟨1, by simp⟩⟩
    ⟨by simp, fun a ha => by
      classical
      have : a = 0 := ha
      subst this
      rw [map_zero, dividedPowersBot_dpow_eq, dividedPowersBot_dpow_eq]
      simp only [true_and]
      split_ifs <;> simp⟩
    (resPt q x) (fun _ => rfl)

end GlobalTheory.CompanionTheory.ConeOne

open GlobalTheory.CompanionTheory.ConeOne in
theorem GlobalTheory.CompanionTheory.ConeOne.oneK_ne_zero : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)), Nonempty X →
    oneK q ≠ 0 := by
  intro K _ X q ⟨x⟩ h
  have h1 := (Submodule.Quotient.mk_eq_zero _).1 h
  have h2 : (fun s : ComposableArrows (Thick (smFun X q)) 0 =>
      (1 : (thA (smFun X q)).obj (s.obj (Fin.last 0)))) = 0 := h1
  have h3 := congrFun h2 (ComposableArrows.mk₀ (resT q x))
  exact one_ne_zero (α := X.residueField x) h3
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitClassNeZeroOfNonemptyStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_class_ne_zero_of_nonempty : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)), Nonempty X →
    oneK q ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.ConeOne.oneK_ne_zero | exact GlobalTheory.CompanionTheory.ConeOne.oneK_ne_zero | (intros; apply GlobalTheory.CompanionTheory.ConeOne.oneK_ne_zero <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningGradedVanishNegative
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningGradedVanishNegative
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.Cone

universe w v u

theorem HU_subsingleton_of_obj {R : Type} [CommRing R] {C : Type u} [Category.{v} C]
    (F : C ⥤ ModuleCat.{w} R) (U : ObjectProperty C) (j : ℕ)
    (h : ∀ T : C, Subsingleton (F.obj T)) : Subsingleton (HU F U j) := by
  have hC : Subsingleton (CH.Cn (U.ι ⋙ F) j) :=
    ⟨fun f g => funext fun s => (h _).elim _ _⟩
  have hZ : Subsingleton ((CH.cx (U.ι ⋙ F)).Z j) :=
    ⟨fun x y => Subtype.ext (hC.elim _ _)⟩
  refine ⟨fun x y => ?_⟩
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  exact congrArg _ (hZ.elim x y)

theorem sq_obj_subsingleton {R : Type} [CommRing R] {C : Type u} [Category.{v} C]
    {A : C ⥤ CommAlgCat.{0} R} (a b : IdF A) (T : C) (h : a.S T = b.S T) :
    Subsingleton ((sq a b).obj T) := by
  have h0 : ∀ x : sqM a b T, x = 0 := by
    rintro ⟨x, hx⟩
    obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hx
    refine Subtype.ext ?_
    exact Ideal.Quotient.eq_zero_iff_mem.2 (h ▸ hy)
  exact ⟨fun x y => (h0 x).trans (h0 y).symm⟩

theorem HU_gr_neg {b : Base} (L : b.Fun) (Q : ObjectProperty (Thick L)) (r : ℤ) (hr : r < 0) (j : ℕ) :
    Subsingleton (HU (gr (Φ := thP L) (thFil L) r) Q j) := by
  refine HU_subsingleton_of_obj _ Q j fun T => sq_obj_subsingleton _ _ T ?_
  have e : r.toNat = (r + 1).toNat := by omega
  change T.pdPow r.toNat = T.pdPow (r + 1).toNat
  rw [e]

end GlobalTheory.CompanionTheory.Cone
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningGradedVanishNegativeStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thickening_graded_vanish_negative : ∀ {b : Base} (L : b.Fun) (Q : ObjectProperty (Thick L)) (r : ℤ), r < 0 → ∀ j : ℕ,
    Subsingleton (HU (gr (Φ := thP L) (thFil L) r) Q j) := by
  first | exact @GlobalTheory.CompanionTheory.Cone.HU_gr_neg | exact GlobalTheory.CompanionTheory.Cone.HU_gr_neg | (intros; apply GlobalTheory.CompanionTheory.Cone.HU_gr_neg <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDualDerivationsOfCoords
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDualDerivationsOfCoords
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeDerivs

theorem exists_dual_derivations : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    (V : X.Opens) (d : ℕ) (c : Coord q V d), letI := (strV q V).toAlgebra;
    ∃ D : Fin d → Derivation K Γ(X, V) Γ(X, V), ∀ k j, D k (c.t j) = if k = j then 1 else 0 := by
  intro K _ X q V d c
  letI := (strV q V).toAlgebra
  letI : Algebra (MvPolynomial (Fin d) K) Γ(X, V) :=
    (MvPolynomial.eval₂Hom (strV q V) c.t : MvPolynomial (Fin d) K →+* Γ(X, V)).toAlgebra
  haveI : IsScalarTower K (MvPolynomial (Fin d) K) Γ(X, V) :=
    IsScalarTower.of_algebraMap_eq fun r => (MvPolynomial.eval₂Hom_C (strV q V) c.t r).symm
  haveI : Algebra.Etale (MvPolynomial (Fin d) K) Γ(X, V) := c.etale
  obtain ⟨⟨b, hb⟩, -⟩ := GlobalTheory.EtaleCoordJacobian.exists_basis_of_etale K Γ(X, V) (Fin d)
  have hb' : ∀ j, KaehlerDifferential.D K Γ(X, V) (c.t j) = b j := fun j => by
    rw [hb j]
    congr 1
    exact (MvPolynomial.eval₂Hom_X' (strV q V) c.t j).symm
  refine ⟨fun k => KaehlerDifferential.linearMapEquivDerivation K Γ(X, V)
    (b.coord k), fun k j => ?_⟩
  change b.coord k (KaehlerDifferential.D K Γ(X, V) (c.t j)) = _
  rw [hb', Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  simp only [eq_comm]

end GlobalTheory.CompanionTheory.ConeDerivs
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDualDerivationsOfCoordsStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dual_derivations_of_coords : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (V : X.Opens) (d : ℕ) (c : Coord q V d), letI := (strV q V).toAlgebra; ∃ D : Fin d → Derivation K Γ(X, V) Γ(X, V), ∀ k j, D k (c.t j) = if k = j then 1 else 0 := by
  first | exact @GlobalTheory.CompanionTheory.ConeDerivs.exists_dual_derivations | exact GlobalTheory.CompanionTheory.ConeDerivs.exists_dual_derivations | (intros; apply GlobalTheory.CompanionTheory.ConeDerivs.exists_dual_derivations <;> assumption)
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.OneKNeZero
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Pb

theorem oneK_ne_zero : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)), Nonempty X →
    oneK q ≠ 0 := GlobalTheory.T.unit_class_ne_zero_of_nonempty

theorem gr_top_van : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (d : ℕ)
    [SmoothOfRelativeDimension d q] (V : X.Opens), IsAffineOpen V → ∀ (s : ℕ) (r : ℤ) (j : ℕ), (d : ℤ) < r →
    Subsingleton (HQ (KS q s {V}) r (r + 1) j) := GlobalTheory.T.affine_graded_quotient_vanish_above_dim

theorem cupPowC_smul : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (A : C ⥤ CommAlgCat.{0} R)
    (z : CH.Cn (CH.modF A) 2) (a : R) (k : ℕ), cupPowC A (a • z) k = a ^ k • cupPowC A z k := GlobalTheory.T.cup_power_smul

end CrystallineSemistableComparison.Pb
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ConeTransfer
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace CrystallineSemistableComparison.Pb

theorem cone_transfer : KH.LocGr → KH.PolyTf → KH.GrAff →
    ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (n : ℕ)
    [SmoothOfRelativeDimension (n + 1) q] {N : ℕ} (i : X ⟶ PSpace K N) (y : Fin (n + 2) → MvPolynomial (Fin (N + 1)) K),
    (∀ S : Finset (Fin (n + 2)), S.Nonempty → IsAffineOpen (⨅ k ∈ S, uy i y k)) →
    ∀ (V : X.Opens) (hV : ∀ S : Finset (Fin (n + 2)), V ≤ ⨅ k ∈ S, uy i y k) (c : Coord q V (n + 1)),
    letI := (strV q V).toAlgebra
    ∀ (D : Fin (n + 1) → Derivation K Γ(X, V) Γ(X, V)), (∀ k j, D k (c.t j) = if k = j then 1 else 0) →
    ∀ (g : Fin (n + 1) → Γ(X, ⨅ k ∈ Finset.univ, uy i y k)), (∀ k, IsUnit (g k)) →
    ∀ (ĝ : Fin (n + 1) → ∀ T : (capS (wK q i y (n + 2)) Finset.univ).FullSubcategory, T.obj.B),
    (∀ k T (h : InU (⨅ k ∈ Finset.univ, uy i y k) T.obj), Ideal.Quotient.mk _ (ĝ k T) = ev T.obj h (g k)) →
    ∀ (c0 : HU (gr (Φ := thP (smFun X q)) (thFil (smFun X q)) ((n : ℤ) + 1)) (capS (wK q i y (n + 2)) Finset.univ) (n + 1)),
    Rep ((thFil (smFun X q) ((n : ℤ) + 1)).res (capS (wK q i y (n + 2)) Finset.univ).ι)
      ((thFil (smFun X q) ((n : ℤ) + 1 + 1)).res (capS (wK q i y (n + 2)) Finset.univ).ι)
      (cupListC ((capS (wK q i y (n + 2)) Finset.univ).ι ⋙ thA (smFun X q)) fun k =>
        dlogC (capS (wK q i y (n + 2)) Finset.univ) (n + 2) (ĝ k)) c0 →
    ∀ (ω : ∀ j, HU (gr (Φ := thP (smFun X q)) (thFil (smFun X q)) ((n : ℤ) + 1))
        (capS (wK q i y (n + 2)) (Finset.univ.erase j)) (n + 1))
      (f : CH.Cn (CH.modF ((capS (wK q i y (n + 2)) Finset.univ).ι ⋙ thA (smFun X q))) n),
    (∀ σ, f σ ∈ (thFil (smFun X q) n).S _) → (∀ σ, CH.d _ n f σ ∈ (thFil (smFun X q) ((n : ℤ) + 1)).S _) →
    Rep ((thFil (smFun X q) ((n : ℤ) + 1)).res (capS (wK q i y (n + 2)) Finset.univ).ι)
      ((thFil (smFun X q) ((n : ℤ) + 1 + 1)).res (capS (wK q i y (n + 2)) Finset.univ).ι) (CH.d _ n f)
      (c0 - ∑ j, ((resU (gr (Φ := thP (smFun X q)) (thFil (smFun X q)) ((n : ℤ) + 1))
        (capS_univ_le (wK q i y (n + 2)) (Finset.univ.erase j))).pull (n + 1)) (ω j)) →
    ∃ (x : Fin (n + 2) → Γ(X, V)) (η : Fin (n + 1) → Γ(X, V)),
      (∀ j, x j ∈ jacSpan (hV (Finset.univ.erase j)) (RingHom.id _) (fun k => D k) id) ∧
      (∀ k, η k ∈ jacSpan (hV Finset.univ) (RingHom.id _) (fun k => D k) (Fin.succAbove k)) ∧
      (Ring.inverse (∏ k, rs (hV Finset.univ) (g k)) * (Matrix.of fun k l => D k (rs (hV Finset.univ) (g l))).det =
          ∑ j, x j + ∑ k : Fin (n + 1), (-1 : Γ(X, V)) ^ (k : ℕ) * D k (η k) ∨
        -(Ring.inverse (∏ k, rs (hV Finset.univ) (g k)) * (Matrix.of fun k l => D k (rs (hV Finset.univ) (g l))).det) =
          ∑ j, x j + ∑ k : Fin (n + 1), (-1 : Γ(X, V)) ^ (k : ℕ) * D k (η k)) := GlobalTheory.T.projective_chart_affine_coords

end CrystallineSemistableComparison.Pb
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.RepDlogLifts
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Pb

theorem rep_cupList : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (Φ : PDF R C) (Fil : ℤ → IdF Φ.A),
    IsFil Φ Fil → ∀ {m : ℕ} (ℓ : Fin m → CH.Cn (CH.modF Φ.A) 1), (∀ k, CH.d _ 1 (ℓ k) = 0) → (∀ k σ, ℓ k σ ∈ (Fil 1).S _) →
    ∃ c : CH.H (sq (Fil m) (Fil ((m : ℤ) + 1))) m, Rep (Fil m) (Fil ((m : ℤ) + 1)) (cupListC Φ.A ℓ) c := GlobalTheory.T.exists_cup_list_representative

theorem dlog_ratios : ∀ {K R : Type} [Field K] [CommRing R] [Algebra K R] (n : ℕ) (t : Fin (n + 1) → Rˣ)
    (D : Fin (n + 1) → Derivation K R R), (∀ k j, D k (t j) = if k = j then 1 else 0) →
    let g : Fin (n + 1) → R := fun k => if h : (k : ℕ) = 0 then ((t 0)⁻¹ : Rˣ) else
      (t ⟨k - 1, by omega⟩ : R) * ((t k)⁻¹ : Rˣ)
    Ring.inverse (∏ k, g k) * (Matrix.of fun k l => D k (g l)).det = (((∏ k, t k)⁻¹ : Rˣ) : R) ∨
    Ring.inverse (∏ k, g k) * (Matrix.of fun k l => D k (g l)).det = -(((∏ k, t k)⁻¹ : Rˣ) : R) := GlobalTheory.T.torus_jacobian_det

end CrystallineSemistableComparison.Pb
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.WchCover
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace CrystallineSemistableComparison.Pb

theorem wch_mem : ∀ {K : Type} [Field K] {X : Scheme.{0}} (D : E.LineData X) (N : ℕ) (i : X ⟶ PSpace K N),
    IsTautologicalLineAt D N i → ∀ j, wch i j ∈ 𝒱D D := GlobalTheory.T.chart_open_mem_cover_of_O1

theorem wK_rel : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {N m : ℕ}
    (i : X ⟶ PSpace K N) (y : Fin m → MvPolynomial (Fin (N + 1)) K) (s : ℕ) (k : Fin m) ⦃T T' : Thick (smFun X q)⦄,
    (T ⟶ T') → wK q i y s k T → (∃ β, wK q i y s β T') → wK q i y s k T' := GlobalTheory.T.chart_property_propagates

theorem wU_le : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (D : E.LineData X) {N m : ℕ}
    (i : X ⟶ PSpace K N) (y : Fin m → MvPolynomial (Fin (N + 1)) K) (s : ℕ), IsTautologicalLineAt D N i → wU q i y s ≤ KS q s (𝒱D D) := GlobalTheory.T.chart_union_le_site

theorem zar_capS : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {N m : ℕ}
    (i : X ⟶ PSpace K N) (y : Fin m → MvPolynomial (Fin (N + 1)) K) (s : ℕ) (S : Finset (Fin m)) (hS : S.Nonempty)
    (r r' : ℤ) (j : ℕ),
    ∃ h : capS (wK q i y s) S ≤ KS q s {⨅ k ∈ S, uy i y k},
      Function.Bijective ((resU (sq (thFil (smFun X q) r) (thFil (smFun X q) r')) h).pull j) := GlobalTheory.T.chart_restrict_pull_bijective

theorem isFil_th : ∀ {b : Base} (L : b.Fun), IsFil (thP L) (thFil L) := GlobalTheory.T.thickening_filtration_isFil

end CrystallineSemistableComparison.Pb
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.JacSpanLe
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace CrystallineSemistableComparison.Pb

theorem yQ_unit : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N m e : ℕ} (i : X ⟶ PSpace K N)
    (y : Fin m → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) (k k' : Fin m) (W : X.Opens)
    (h1 : W ≤ uy i y k) (h2 : W ≤ uy i y k'), IsUnit ((i.appLE _ W h2).hom (yQ y hy k k')) := GlobalTheory.T.homogeneous_ratio_isUnit

theorem yQ_mul : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N m e : ℕ} (i : X ⟶ PSpace K N)
    (y : Fin m → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) (a b c : Fin m) (W : X.Opens)
    (ha : W ≤ uy i y a) (hb : W ≤ uy i y b) (hc : W ≤ uy i y c),
    (i.appLE _ W hb).hom (yQ y hy a b) * (i.appLE _ W hc).hom (yQ y hy b c) = (i.appLE _ W hc).hom (yQ y hy a c) ∧
    (i.appLE _ W ha).hom (yQ y hy a a) = 1 := GlobalTheory.T.homogeneous_ratio_cocycle

theorem ev_rs : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} (T : Thick (smFun X q))
    {V W : X.Opens} (h : V ≤ W) (hT : InU V T) (hT' : InU W T) (s : Γ(X, W)), ev T hT (rs h s) = ev T hT' s := GlobalTheory.T.eval_restrict_section

theorem rs_appLE : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) {V W : X.Opens} (h : V ≤ W) (hW : W ≤ f ⁻¹ᵁ U)
    (s : Γ(Y, U)), rs h ((f.appLE U W hW).hom s) = (f.appLE U V (h.trans hW)).hom s := GlobalTheory.T.restrict_appLE_compat

theorem jacSpan_le : ∀ {K : Type} [Field K] {X : Scheme.{0}} {V W : X.Opens} (h : V ≤ W) [Algebra K Γ(X, V)]
    (B : Subalgebra K Γ(X, V)), (B : Set Γ(X, V)) = Set.range (rs h) →
    ∀ {d m : ℕ} (D : Fin d → Derivation K Γ(X, V) Γ(X, V)) (κ : Fin m → Fin d),
    jacSpan h (RingHom.id _) (fun k => D k) κ ≤ jacS B D κ := GlobalTheory.T.jacobian_span_le_subalgebra

end CrystallineSemistableComparison.Pb
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ConeHyp
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace CrystallineSemistableComparison.Pb.LocalCohomologySetup

attribute [local instance] MvPolynomial.gradedAlgebra

open CrystallineSemistableComparison.Pb

def ResidAlgP : Prop := ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (R : Type) [CommRing R] [IsDomain R] [Algebra K R]
    (t : Fin (n + 1) → Rˣ), AlgebraicIndependent K (fun k => (t k : R)) →
    ∀ (D : Fin (n + 1) → Derivation K R R), (∀ k j, D k (t j) = if k = j then 1 else 0) →
    ∀ (B : Finset (Fin (n + 2)) → Subalgebra K R), (∀ S, S.Nonempty → torusS K t S ≤ B S) → (∀ S, S.Nonempty → (B S).FG) →
    (∀ S, S.Nonempty → ∀ b ∈ B S, IsIntegral (torusS K t S) b) → (∀ i, B (Finset.univ.erase i) ≤ B Finset.univ) →
    (∀ r : R, ∃ b ∈ B Finset.univ, ∃ b' ∈ B Finset.univ, b' ≠ 0 ∧ r * b' = b) →
    ∀ (ω : Fin (n + 2) → R) (η : Fin (n + 1) → R), (∀ i, ω i ∈ jacS (B (Finset.univ.erase i)) D id) →
      (∀ k, η k ∈ jacS (B Finset.univ) D (Fin.succAbove k)) →
      ((∏ k, t k)⁻¹ : Rˣ) ≠ (∑ i, ω i + ∑ k : Fin (n + 1), (-1 : R) ^ (k : ℕ) * D k (η k) : R)

def LocExactP : Prop := ∀ {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} [CharZero K] (q : X ⟶ Spec (CommRingCat.of K)) (D : E.LineData X) (i : X ⟶ PSpace K N)
    (hD : IsTautologicalLineAt D N i) {m e : ℕ} (y : Fin m → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e)
    (s : ℕ) (Λ : CLiftK (ObjectProperty.ι fun T : Thick (smFun X q) => ∃ k, wK q i y s k T) D),
    ∃ b : ∀ k, CH.Cn (CH.modF ((wK q i y s k).ι ⋙ thA (smFun X q))) 1,
      (∀ k σ, b k σ ∈ (thFil (smFun X q) 1).S _) ∧
      (∀ k, resB (thA (smFun X q)) (fun T h => ⟨k, h⟩ : wK q i y s k ≤ fun T : Thick (smFun X q) => ∃ k', wK q i y s k' T)
        (e • zK Λ s) = CH.d _ 1 (b k)) ∧
      ∀ k k', ∃ ĝ : ∀ T : (capS (wK q i y s) {k, k'}).FullSubcategory, T.obj.B,
        (∀ T (h : InU (uy i y k') T.obj),
          Ideal.Quotient.mk _ (ĝ T) = ev T.obj h ((i.appLE _ (uy i y k') le_rfl).hom (yQ y hy k k'))) ∧
        resB (thA (smFun X q)) (fun T h => h k (by simp) : capS (wK q i y s) {k, k'} ≤ wK q i y s k) (b k) -
          resB (thA (smFun X q)) (fun T h => h k' (by simp) : capS (wK q i y s) {k, k'} ≤ wK q i y s k') (b k') =
          dlogC (capS (wK q i y s) {k, k'}) s ĝ

def GeoSetupP : Prop := ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    [ConnectedSpace X] (n : ℕ) [SmoothOfRelativeDimension (n + 1) q] (N : ℕ) (i : X ⟶ PSpace K N)
    (_ : IsClosedImmersion i) (_ : i ≫ PSpace.str K N = q),
    ∃ (e : ℕ) (_ : 0 < e) (y : Fin (n + 2) → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e),
      let U : Fin (n + 2) → X.Opens := fun k => i ⁻¹ᵁ Proj.basicOpen _ (y k)
      (⨆ k, U k) = ⊤ ∧
      (∀ S : Finset (Fin (n + 2)), S.Nonempty → IsAffineOpen (⨅ k ∈ S, U k)) ∧
      ∃ (V : X.Opens) (hV : V ≤ ⨅ k, U k) (c : Coord q V (n + 1)),
        letI := (strV q V).toAlgebra
        IsDomain Γ(X, V) ∧
        (∀ k, c.t k = (i.appLE _ V (hV.trans (iInf_le U 0))).hom (yRatio y hy k)) ∧
        ∃ ht : ∀ k, IsUnit (c.t k),
          AlgebraicIndependent K c.t ∧
          ∃ B : Finset (Fin (n + 2)) → Subalgebra K Γ(X, V),
            (∀ S, S.Nonempty → (B S : Set Γ(X, V)) = Set.range (resO (le_biInf_of_le hV S))) ∧
            (∀ S, S.Nonempty → Function.Injective (resO (le_biInf_of_le hV S))) ∧
            (∀ S, S.Nonempty → torusS K (fun k => (ht k).unit) S ≤ B S) ∧
            (∀ S, S.Nonempty → (B S).FG) ∧
            (∀ S, S.Nonempty → ∀ b ∈ B S, IsIntegral (torusS K (fun k => (ht k).unit) S) b) ∧
            (∀ j, B (Finset.univ.erase j) ≤ B Finset.univ) ∧
            (∀ r : Γ(X, V), ∃ b ∈ B Finset.univ, ∃ b' ∈ B Finset.univ, b' ≠ 0 ∧ r * b' = b)

end CrystallineSemistableComparison.Pb.LocalCohomologySetup
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.CechRel
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace CrystallineSemistableComparison.Pb

theorem cech_top_rel : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (Φ : PDF R C) (Fil : ℤ → IdF Φ.A),
    IsFil Φ Fil → ∀ (s n : ℕ) (W : Fin (n + 2) → ObjectProperty C), (∀ T, (∃ α, W α T) → (Fil s).S T = ⊥) →
    (∀ α ⦃T T' : C⦄, (T ⟶ T') → W α T → (∃ β, W β T') → W α T') →
    (∀ S : Finset (Fin (n + 2)), S.Nonempty → ∀ (r : ℤ) (j : ℕ), (j : ℤ) ≠ r → Subsingleton (HU (gr Fil r) (capS W S) j)) →
    (∀ S : Finset (Fin (n + 2)), S.Nonempty → ∀ (r : ℤ) (j : ℕ), (n : ℤ) + 1 < r → Subsingleton (HU (gr Fil r) (capS W S) j)) →
    ∀ (z : CH.Cn (CH.modF ((ObjectProperty.ι fun T : C => ∃ α, W α T) ⋙ Φ.A)) 2), CH.d _ 2 z = 0 → (∀ σ, z σ ∈ (Fil 1).S _) →
    ∀ (b : ∀ i, CH.Cn (CH.modF ((W i).ι ⋙ Φ.A)) 1), (∀ i σ, b i σ ∈ (Fil 1).S _) →
    (∀ i, resB Φ.A (fun T h => ⟨i, h⟩ : W i ≤ fun T : C => ∃ α, W α T) z = CH.d _ 1 (b i)) →
    (∀ h, (CH.cx _).cls (cupPowC ((ObjectProperty.ι fun T : C => ∃ α, W α T) ⋙ Φ.A) z (n + 1)) h = 0) →
    ∀ c : HU (gr Fil ((n : ℤ) + 1)) (capS W Finset.univ) (n + 1),
      Rep ((Fil ((n : ℤ) + 1)).res (capS W Finset.univ).ι) ((Fil ((n : ℤ) + 1 + 1)).res (capS W Finset.univ).ι)
        (cupListC ((capS W Finset.univ).ι ⋙ Φ.A) fun k : Fin (n + 1) =>
          resB Φ.A (capS_le_univ W k.castSucc) (b k.castSucc) - resB Φ.A (capS_le_univ W k.succ) (b k.succ)) c →
      ∃ (ω : ∀ i, HU (gr Fil ((n : ℤ) + 1)) (capS W (Finset.univ.erase i)) (n + 1))
        (f : CH.Cn (CH.modF ((capS W Finset.univ).ι ⋙ Φ.A)) n),
        (∀ σ, f σ ∈ (Fil n).S _) ∧ (∀ σ, CH.d _ n f σ ∈ (Fil ((n : ℤ) + 1)).S _) ∧
        Rep ((Fil ((n : ℤ) + 1)).res (capS W Finset.univ).ι) ((Fil ((n : ℤ) + 1 + 1)).res (capS W Finset.univ).ι)
          (CH.d _ n f) (c - ∑ i, ((resU (gr Fil ((n : ℤ) + 1)) (capS_univ_le W (Finset.univ.erase i))).pull (n + 1)) (ω i)) := GlobalTheory.T.graded_cover_vanishing_induction

end CrystallineSemistableComparison.Pb
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GrNegVan
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Pb

theorem gr_neg_van : ∀ {b : Base} (L : b.Fun) (Q : ObjectProperty (Thick L)) (r : ℤ), r < 0 → ∀ j : ℕ,
    Subsingleton (HU (gr (Φ := thP L) (thFil L) r) Q j) := GlobalTheory.T.thickening_graded_vanish_negative

end CrystallineSemistableComparison.Pb
end
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace CrystallineSemistableComparison.Pb

attribute [local instance] MvPolynomial.gradedAlgebra

theorem d_resB {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (A : C ⥤ CommAlgCat.{0} R)
    {U V : ObjectProperty C} (h : V ≤ U) {j : ℕ} (b : CH.Cn (CH.modF (U.ι ⋙ A)) j) :
    CH.d _ j (resB A h b) = resB A h (CH.d _ j b) :=
  (CH.Mor.restrict (CH.modF (U.ι ⋙ A)) (ObjectProperty.ιOfLE h)).d_pullC j b

theorem dpow_mem_pdP' {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (n : ℕ) {x : B} (hx : x ∈ J) :
    δ.dpow n x ∈ pdP δ n :=
  Ideal.subset_span ⟨[(n, x)], by simpa using hx, by simp, by simp⟩

theorem mem_pdP_one {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {x : B} (hx : x ∈ J) : x ∈ pdP δ 1 := by
  have := dpow_mem_pdP' δ 1 hx
  rwa [δ.dpow_one hx] at this

theorem plogK_mem' {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (s : ℕ) {x : B} (hx : x ∈ J) :
    plogK δ s x ∈ J :=
  Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (δ.dpow_mem (Nat.succ_ne_zero k) hx)

theorem g_rel {K : Type} [Field K] {X : Scheme.{0}} {N n e : ℕ} (i : X ⟶ PSpace K N)
    (y : Fin (n + 2) → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) (V W : X.Opens) (hVW : V ≤ W)
    (hW : ∀ b, W ≤ uy i y b) (t : Fin (n + 1) → Γ(X, V)ˣ)
    (ht : ∀ k, (t k : Γ(X, V)) = (i.appLE _ V (hVW.trans (hW 0))).hom (yQ y hy k.succ 0)) (k : Fin (n + 1)) :
    rs hVW ((i.appLE _ W (hW k.succ)).hom (yQ y hy k.castSucc k.succ)) =
      if h : (k : ℕ) = 0 then (((t 0)⁻¹ : Γ(X, V)ˣ) : Γ(X, V)) else
        (t ⟨k - 1, by omega⟩ : Γ(X, V)) * (((t k)⁻¹ : Γ(X, V)ˣ) : Γ(X, V)) := by
  have hVb : ∀ b : Fin (n + 2), V ≤ uy i y b := fun b => hVW.trans (hW b)
  set A : Fin (n + 2) → Fin (n + 2) → Γ(X, V) := fun a b =>
    (i.appLE (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) (y b)) V (hVb b)).hom (yQ y hy a b)
    with hAdef
  have hA : ∀ a b c : Fin (n + 2), A a b * A b c = A a c := fun a b c =>
    (yQ_mul i y hy a b c V (hVb a) (hVb b) (hVb c)).1
  have hA1 : ∀ a, A a a = 1 := fun a => (yQ_mul i y hy a a a V (hVb a) (hVb a) (hVb a)).2
  have htA : ∀ k : Fin (n + 1), ((t k : Γ(X, V)ˣ) : Γ(X, V)) = A k.succ 0 := fun k => ht k
  have hinv : ∀ k : Fin (n + 1), A 0 k.succ = (((t k)⁻¹ : Γ(X, V)ˣ) : Γ(X, V)) := fun k =>
    Units.eq_inv_of_mul_eq_one_left (by rw [htA, hA, hA1])
  have e0 : rs hVW ((i.appLE _ W (hW k.succ)).hom (yQ y hy k.castSucc k.succ)) = A k.castSucc k.succ :=
    rs_appLE i _ hVW (hW k.succ) (yQ y hy k.castSucc k.succ)
  rw [e0]
  by_cases hk : (k : ℕ) = 0
  · have hk0 : k = 0 := Fin.ext hk
    subst hk0
    rw [dite_eq_left hk]
    exact hinv 0
  · rw [dite_eq_right hk]
    have e1 : (⟨(k : ℕ) - 1, by omega⟩ : Fin (n + 1)).succ = k.castSucc := Fin.ext (by simp; omega)
    rw [htA, e1, ← hinv k, hA]

set_option maxHeartbeats 800000 in
theorem powK_ne_zero_of (hG : LocalCohomologySetup.GeoSetupP) (hR : LocalCohomologySetup.ResidAlgP) (hL : LocalCohomologySetup.LocExactP)
    {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [ConnectedSpace X] (d : ℕ) [SmoothOfRelativeDimension d q] (D : E.LineData X) (hD : IsTautologicalLine q D) (c : HdR q 2)
    (hc : IsFirstChernDeRham q D c) : powK q c d ≠ 0 := by
  rcases d with _ | n
  · exact oneK_ne_zero q inferInstance
  · intro h0
    obtain ⟨N, i, hci, hiq, hO⟩ := hD
    obtain ⟨e, he, y, hy, hcov, haff, V, hV, cc, hdom, htc, ht, halg, B, hBr, hBi, hBt, hBfg, hBint, hBle, hBfr⟩ :=
      hG q n N i hci hiq
    let _ : Algebra K Γ(X, V) := (strV q V).toAlgebra
    have _ := hdom
    obtain ⟨Dv, hDv⟩ := GlobalTheory.T.exists_dual_derivations_of_coords q V (n + 1) cc

    have hsQ : ∀ T : (wU q i y (n + 2)).FullSubcategory, T.obj.pdPow (n + 2) = ⊥ := fun T => by
      obtain ⟨k, hk, -⟩ := T.property
      exact hk.1
    have hVQ : ∀ T : (wU q i y (n + 2)).FullSubcategory, ∃ (V : X.Opens) (σ : (V : Scheme.{0}) ⟶ D.Y),
        σ ≫ D.f = V.ι ∧ InU V ((wU q i y (n + 2)).ι.obj T) := fun T => by
      obtain ⟨k, -, W, ⟨j, rfl⟩, hW⟩ := T.property
      obtain ⟨σ, hσ⟩ := wch_mem D N i hO j
      exact ⟨wch i j, σ, hσ, fun x hx => (hW hx).2⟩
    let Λ : CLiftK (wU q i y (n + 2)).ι D :=
      (GlobalTheory.T.exists_cone_lift q D (n + 2)).some.precomp (ObjectProperty.ιOfLE (wU_le q D i y (n + 2) hO))
    obtain ⟨z, hz, hzf, hzc⟩ := hc (n + 2) _ (wU q i y (n + 2)).ι hsQ hVQ Λ
    obtain ⟨hzp, hzp0⟩ := powK_pull q (wU q i y (n + 2)).ι c z hz hzc (n + 1)
    rw [h0, map_zero] at hzp0
    have hzK : z = zK Λ (n + 2) := funext fun σ => hzf σ
    subst hzK
    obtain ⟨b, hb1, hb, hdiff⟩ := hL q D i hO y hy (n + 2) Λ

    let W := wK q i y (n + 2)
    have hsU : ∀ T, (∃ α, W α T) → (thFil (smFun X q) ((n + 2 : ℕ) : ℤ)).S T = ⊥ := by
      rintro T ⟨k, hk, -⟩
      exact hk.1
    have hvanS : ∀ S : Finset (Fin (n + 2)), S.Nonempty → ∀ (r : ℤ) (j : ℕ),
        Subsingleton (HU (sq (thFil (smFun X q) r) (thFil (smFun X q) (r + 1))) (KS q (n + 2) {⨅ k ∈ S, uy i y k}) j) →
        Subsingleton (HU (gr (Φ := thP (smFun X q)) (thFil (smFun X q)) r) (capS W S) j) := by
      intro S hS r j hsub
      obtain ⟨h, hbij⟩ := zar_capS q i y (n + 2) S hS r (r + 1) j
      exact hbij.2.subsingleton
    have : Smooth q := SmoothOfRelativeDimension.smooth (n + 1) q
    have hvan2 : ∀ S : Finset (Fin (n + 2)), S.Nonempty → ∀ (r : ℤ) (j : ℕ), (n : ℤ) + 1 < r →
        Subsingleton (HU (gr (Φ := thP (smFun X q)) (thFil (smFun X q)) r) (capS W S) j) := by
      intro S hS r j hr
      refine hvanS S hS r j ?_
      exact gr_top_van q (n + 1) _ (haff S hS) (n + 2) r j (by exact_mod_cast hr)
    have hvan1 : ∀ S : Finset (Fin (n + 2)), S.Nonempty → ∀ (r : ℤ) (j : ℕ), (j : ℤ) ≠ r →
        Subsingleton (HU (gr (Φ := thP (smFun X q)) (thFil (smFun X q)) r) (capS W S) j) := by
      intro S hS r j hjr
      rcases lt_or_ge r 0 with hr | hr
      · exact gr_neg_van _ _ r hr j
      rcases le_or_gt r ((n : ℤ) + 1) with hr' | hr'
      · refine hvanS S hS r j ?_
        obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hr
        exact CrystallineSemistableComparison.Pb.gr_aff q _ (haff S hS) (n + 2) m j (by omega) (by omega)
      · exact hvan2 S hS r j hr'
    have hze : CH.d _ 2 (e • zK Λ (n + 2)) = 0 := by rw [map_nsmul, hz, smul_zero]
    have hz1 : ∀ σ, (e • zK Λ (n + 2)) σ ∈ (thFil (smFun X q) 1).S _ := fun σ => by
      have h := mem_pdP_one ((wU q i y (n + 2)).ι.obj (σ.obj (Fin.last 2))).δ
        (plogK_mem' ((wU q i y (n + 2)).ι.obj (σ.obj (Fin.last 2))).δ (n + 2) (GlobalTheory.T.cone_lift_ratio_mem_ideal Λ σ))
      exact nsmul_mem h e
    have hzero : ∀ h, (CH.cx _).cls (cupPowC ((ObjectProperty.ι fun T => ∃ α, W α T) ⋙ thA (smFun X q))
        (e • zK Λ (n + 2)) (n + 1)) h = 0 := by
      intro h
      have hsm : cupPowC ((wU q i y (n + 2)).ι ⋙ thA (smFun X q)) (e • zK Λ (n + 2)) (n + 1) =
          ((e : K) ^ (n + 1)) • cupPowC ((wU q i y (n + 2)).ι ⋙ thA (smFun X q)) (zK Λ (n + 2)) (n + 1) := by
        rw [← Nat.cast_smul_eq_nsmul K, cupPowC_smul]
      have hB := ((CrystallineSemistableComparison.P.cls_surj _ _).2.1 _ hzp).1 hzp0
      refine ((CrystallineSemistableComparison.P.cls_surj _ _).2.1 _ h).2 ?_
      exact hsm ▸ Submodule.smul_mem _ _ hB
    let ℓ : Fin (n + 1) → CH.Cn (CH.modF ((capS W Finset.univ).ι ⋙ thA (smFun X q))) 1 := fun k =>
      resB (thA (smFun X q)) (capS_le_univ W k.castSucc) (b k.castSucc) -
        resB (thA (smFun X q)) (capS_le_univ W k.succ) (b k.succ)
    have hℓcoc : ∀ k, CH.d _ 1 (ℓ k) = 0 := fun k => by
      show CH.d _ 1 (resB _ _ (b k.castSucc) - resB _ _ (b k.succ)) = 0
      rw [map_sub, d_resB, d_resB, ← hb, ← hb]
      exact sub_eq_zero.2 rfl
    have hℓ1 : ∀ k σ, ℓ k σ ∈ (sFil (capS W Finset.univ) 1).S _ := fun k σ => by
      have h1 := hb1 k.castSucc (σ ⋙ ObjectProperty.ιOfLE (capS_le_univ W k.castSucc))
      have h2 := hb1 k.succ (σ ⋙ ObjectProperty.ιOfLE (capS_le_univ W k.succ))
      exact Ideal.sub_mem ((thFil (smFun X q) 1).S (σ.obj (Fin.last 1)).obj) h1 h2
    have hc0' : ∃ c0 : HU (gr (Φ := thP (smFun X q)) (thFil (smFun X q)) ((n : ℤ) + 1)) (capS W Finset.univ) (n + 1),
        Rep ((thFil (smFun X q) ((n : ℤ) + 1)).res (capS W Finset.univ).ι)
          ((thFil (smFun X q) ((n : ℤ) + 1 + 1)).res (capS W Finset.univ).ι)
          (cupListC ((capS W Finset.univ).ι ⋙ (thP (smFun X q)).A) ℓ) c0 := by
      have := rep_cupList (sP (capS W Finset.univ)) (sFil (capS W Finset.univ)) (isFil _) ℓ hℓcoc hℓ1
      rw [Nat.cast_succ] at this
      exact this
    obtain ⟨c0, hc0⟩ := hc0'
    obtain ⟨ω, f, hf, hdf, hrep⟩ := cech_top_rel (thP (smFun X q)) (thFil (smFun X q)) (isFil_th _) (n + 2) n W hsU
      (wK_rel q i y (n + 2)) hvan1 hvan2 (e • zK Λ (n + 2)) hze hz1 b hb1 hb hzero c0 hc0
    have key : ∃ (x : Fin (n + 2) → Γ(X, V)) (η : Fin (n + 1) → Γ(X, V)),
        (∀ j, x j ∈ jacS (B (Finset.univ.erase j)) Dv id) ∧ (∀ k, η k ∈ jacS (B Finset.univ) Dv (Fin.succAbove k)) ∧
        ((((∏ k, (ht k).unit)⁻¹ : Γ(X, V)ˣ) : Γ(X, V)) =
          ∑ j, x j + ∑ k : Fin (n + 1), (-1 : Γ(X, V)) ^ (k : ℕ) * Dv k (η k)) := by
      have hKG : KH.LocGr := CrystallineSemistableComparison.Pb.loc_gr
      have hKP : KH.PolyTf := CrystallineSemistableComparison.Pb.poly_tf
      have hKA : KH.GrAff := CrystallineSemistableComparison.Pb.gr_aff
      have hV' : ∀ S : Finset (Fin (n + 2)), V ≤ ⨅ k ∈ S, uy i y k := fun S => le_biInf_of_le hV S
      have hUk : ∀ k, (⨅ k ∈ (Finset.univ : Finset (Fin (n + 2))), uy i y k) ≤ uy i y k := fun k =>
        biInf_le _ (Finset.mem_univ k)
      let g : Fin (n + 1) → Γ(X, ⨅ k ∈ (Finset.univ : Finset (Fin (n + 2))), uy i y k) := fun k =>
        (i.appLE _ _ (hUk k.succ)).hom (yQ y hy k.castSucc k.succ)
      have hg : ∀ k, IsUnit (g k) := fun k => yQ_unit i y hy _ _ _ (hUk _) (hUk _)
      choose ĝ0 hĝ0 hĝd using hdiff
      let ĝ : Fin (n + 1) → ∀ T : (capS W Finset.univ).FullSubcategory, T.obj.B := fun k T =>
        ĝ0 k.castSucc k.succ ⟨T.obj, fun α _ => T.property α (Finset.mem_univ α)⟩
      have hĝ : ∀ k T (h : InU (⨅ k ∈ (Finset.univ : Finset (Fin (n + 2))), uy i y k) T.obj),
          Ideal.Quotient.mk _ (ĝ k T) = ev T.obj h (g k) := fun k T h => by
        have h1 : InU (uy i y k.succ) T.obj := inU_mono q (hUk k.succ) h
        have e1 := hĝ0 k.castSucc k.succ ⟨T.obj, fun α _ => T.property α (Finset.mem_univ α)⟩ h1
        have e2 := rs_appLE i (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) (y k.succ))
          (hUk k.succ) le_rfl (yQ y hy k.castSucc k.succ)
        have e3 := ev_rs T.obj (hUk k.succ) h h1
          ((i.appLE (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) (y k.succ)) (uy i y k.succ)
            le_rfl).hom (yQ y hy k.castSucc k.succ))
        refine e1.trans (e3.symm.trans ?_)
        exact congrArg (ev T.obj h) e2
      have hℓeq : ℓ = fun k => dlogC (capS W Finset.univ) (n + 2) (ĝ k) := funext fun k =>
        congrArg (resB (thA (smFun X q))
          (fun T h α _ => h α (Finset.mem_univ α) : capS W Finset.univ ≤ capS W {k.castSucc, k.succ})) (hĝd k.castSucc k.succ)
      rw [hℓeq] at hc0
      obtain ⟨x, η, hx, hη, heq⟩ := cone_transfer hKG hKP hKA q n i y haff V hV' cc Dv hDv g hg ĝ hĝ c0 hc0 ω f hf hdf hrep
      let tu : Fin (n + 1) → Γ(X, V)ˣ := fun k => (ht k).unit
      let g' : Fin (n + 1) → Γ(X, V) := fun k => if h : (k : ℕ) = 0 then (((tu 0)⁻¹ : Γ(X, V)ˣ) : Γ(X, V)) else
        (tu ⟨k - 1, by omega⟩ : Γ(X, V)) * (((tu k)⁻¹ : Γ(X, V)ˣ) : Γ(X, V))
      have hgt : ∀ k, rs (hV' Finset.univ) (g k) = g' k := fun k =>
        g_rel i y hy V _ (hV' Finset.univ) hUk tu (fun k => by simp only [tu, IsUnit.unit_spec]; exact htc k) k
      have hDvu : ∀ k j, Dv k (tu j) = if k = j then 1 else 0 := fun k j => by simpa [tu] using hDv k j
      have hdr : Ring.inverse (∏ k, g' k) * (Matrix.of fun k l => Dv k (g' l)).det = (((∏ k, tu k)⁻¹ : Γ(X, V)ˣ) : Γ(X, V)) ∨
          Ring.inverse (∏ k, g' k) * (Matrix.of fun k l => Dv k (g' l)).det = -(((∏ k, tu k)⁻¹ : Γ(X, V)ˣ) : Γ(X, V)) :=
        dlog_ratios n tu Dv hDvu
      have hL : Ring.inverse (∏ k, rs (hV' Finset.univ) (g k)) *
          (Matrix.of fun k l => Dv k (rs (hV' Finset.univ) (g l))).det =
          Ring.inverse (∏ k, g' k) * (Matrix.of fun k l => Dv k (g' l)).det := by simp only [hgt]
      rw [hL] at heq
      have hne : ∀ j : Fin (n + 2), (Finset.univ.erase j).Nonempty := fun j =>
        ⟨j.succAbove 0, Finset.mem_erase.2 ⟨Fin.succAbove_ne j 0, Finset.mem_univ _⟩⟩
      have hxm : ∀ j, x j ∈ jacS (B (Finset.univ.erase j)) Dv id := fun j =>
        jacSpan_le (hV' _) (B _) (hBr _ (hne j)) Dv id (hx j)
      have hηm : ∀ k, η k ∈ jacS (B Finset.univ) Dv (Fin.succAbove k) := fun k =>
        jacSpan_le (hV' _) (B _) (hBr _ Finset.univ_nonempty) Dv _ (hη k)
      have hneg : (∃ (x : Fin (n + 2) → Γ(X, V)) (η : Fin (n + 1) → Γ(X, V)),
          (∀ j, x j ∈ jacS (B (Finset.univ.erase j)) Dv id) ∧ (∀ k, η k ∈ jacS (B Finset.univ) Dv (Fin.succAbove k)) ∧
          (-(((∏ k, (ht k).unit)⁻¹ : Γ(X, V)ˣ) : Γ(X, V)) =
            ∑ j, x j + ∑ k : Fin (n + 1), (-1 : Γ(X, V)) ^ (k : ℕ) * Dv k (η k))) →
          ∃ (x : Fin (n + 2) → Γ(X, V)) (η : Fin (n + 1) → Γ(X, V)),
          (∀ j, x j ∈ jacS (B (Finset.univ.erase j)) Dv id) ∧ (∀ k, η k ∈ jacS (B Finset.univ) Dv (Fin.succAbove k)) ∧
          ((((∏ k, (ht k).unit)⁻¹ : Γ(X, V)ˣ) : Γ(X, V)) =
            ∑ j, x j + ∑ k : Fin (n + 1), (-1 : Γ(X, V)) ^ (k : ℕ) * Dv k (η k)) := by
        rintro ⟨x, η, hx, hη, he⟩
        refine ⟨fun j => -x j, fun k => -η k, fun j => (jacS _ Dv id).neg_mem (hx j),
          fun k => (jacS _ Dv _).neg_mem (hη k), ?_⟩
        rw [← neg_neg (((∏ k, (ht k).unit)⁻¹ : Γ(X, V)ˣ) : Γ(X, V)), he]
        simp only [map_neg, mul_neg, Finset.sum_neg_distrib, neg_add]
      rcases hdr with hd | hd <;> rw [hd] at heq <;> rcases heq with he | he
      · exact ⟨x, η, hxm, hηm, he⟩
      · exact hneg ⟨x, η, hxm, hηm, he⟩
      · exact hneg ⟨x, η, hxm, hηm, he⟩
      · exact ⟨x, η, hxm, hηm, by rw [← he, neg_neg]⟩
    obtain ⟨x, η, hx, hη, heq⟩ := key
    refine hR K n Γ(X, V) (fun k => (ht k).unit) (by simpa using halg) Dv (by simpa using hDv) B hBt hBfg hBint
      hBle hBfr x η hx hη heq

end CrystallineSemistableComparison.Pb
