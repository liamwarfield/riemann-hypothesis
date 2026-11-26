module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieEigenspaceFrameCoordinatesUniqueInvertible
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicMatrixCongruenceMoveRationalFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicArcSmoothAlgebraNonvanishing
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SerreHolomorphicSectionsHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ChernWeilNumbers
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricHalfCoreFormsUniformisationIntegral
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsDivStage
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ComplexSidePlacesIffMemNonzeroIndexPlaces
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIvDOfDefinite
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.NormalisedBlowupCone

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AntisymmEqChernRootsMulRootDiscr
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeylAntisymmetrizationRenameSwapNeg
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeylAntisymmetrizationRenameSwapNeg
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

namespace GlobalTheory.AntisymmSwap

theorem rename_swap_antisymm : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (m : ι → ℕ) (Q : MvPolynomial (Root m) ℝ) (τ : ι)
    (i j : Fin (m τ)), i ≠ j →
      rename (Equiv.swap (⟨τ, i⟩ : Root m) ⟨τ, j⟩) (antisymm Q) = -antisymm Q := by
  intro ι _ _ m Q τ i j hij
  set u : ∀ t, Equiv.Perm (Fin (m t)) := Function.update 1 τ (Equiv.swap i j) with hu
  have hf : ∀ w : ∀ t, Equiv.Perm (Fin (m t)),
      (⇑(Equiv.swap (⟨τ, i⟩ : Root m) ⟨τ, j⟩)) ∘ (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m))
        = fun x : Root m => (⟨x.1, (u * w) x.1 x.2⟩ : Root m) := by
    intro w
    funext ⟨t, k⟩
    simp only [Function.comp_apply, Pi.mul_apply, Equiv.Perm.mul_apply]
    by_cases ht : t = τ
    · subst ht
      simp only [hu, Function.update_self]
      rw [Equiv.swap_apply_def, Equiv.swap_apply_def]
      split_ifs <;> simp_all
    · have h1 : (⟨t, w t k⟩ : Root m) ≠ ⟨τ, i⟩ := fun h => ht (congrArg Sigma.fst h)
      have h2 : (⟨t, w t k⟩ : Root m) ≠ ⟨τ, j⟩ := fun h => ht (congrArg Sigma.fst h)
      rw [Equiv.swap_apply_of_ne_of_ne h1 h2, hu, Function.update_of_ne ht]
      rfl
  have hu1 : (∏ t, Equiv.Perm.sign (u t)) = -1 := by
    rw [Fintype.prod_eq_single τ]
    · simp [hu, Equiv.Perm.sign_swap hij]
    · intro t ht
      simp [hu, Function.update_of_ne ht]
  have hs : ∀ w : ∀ t, Equiv.Perm (Fin (m t)),
      (∏ t, Equiv.Perm.sign ((u * w) t) : ℤˣ) = -∏ t, Equiv.Perm.sign (w t) := by
    intro w
    simp only [Pi.mul_apply, map_mul, Finset.prod_mul_distrib, hu1, neg_one_mul]
  unfold GlobalTheory.GoodMetric.antisymm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp_rw [map_zsmul, rename_rename, hf]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_equiv (Equiv.mulLeft u) (by simp) ?_
  intro w _
  simp only [Equiv.coe_mulLeft, hs, Units.val_neg, neg_smul, neg_neg]

end GlobalTheory.AntisymmSwap
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeylAntisymmetrizationRenameSwapNegStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weylAntisymmetrization_rename_swap_neg : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (m : ι → ℕ) (Q : MvPolynomial (Root m) ℝ) (τ : ι) (i j : Fin (m τ)), i ≠ j → rename (Equiv.swap (⟨τ, i⟩ : Root m) ⟨τ, j⟩) (antisymm Q) = -antisymm Q := by
  first | exact @GlobalTheory.AntisymmSwap.rename_swap_antisymm | exact GlobalTheory.AntisymmSwap.rename_swap_antisymm | (intros; apply GlobalTheory.AntisymmSwap.rename_swap_antisymm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagRelativeTangentTopChernDvdOfDifferencesDvd
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagRelativeTangentTopChernDvdOfDifferencesDvd
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

namespace GlobalTheory.GoodMetric.DiscrDvd

theorem irreducible_X_sub_X {σ : Type} {a b : σ} (h : a ≠ b) :
    Irreducible (X a - X b : MvPolynomial σ ℝ) := by
  classical
  have hc : AddMonoidAlgebra.coeff (X a - X b : MvPolynomial σ ℝ) (Finsupp.single a 1) = 1 := by
    have : ¬ (Finsupp.single b 1 = Finsupp.single a 1) := fun e =>
      h (Finsupp.single_left_injective one_ne_zero e).symm
    simp [coeff_X, this]
  refine irreducible_of_totalDegree_eq_one (le_antisymm ?_ ?_) fun x hx => ?_
  · exact (totalDegree_sub _ _).trans (by simp)
  · have := le_totalDegree (p := (X a - X b : MvPolynomial σ ℝ)) (s := Finsupp.single a 1)
      (by rw [mem_support_iff, hc]; exact one_ne_zero)
    simpa using this
  · exact isUnit_of_dvd_one (hc ▸ hx _)

theorem isRelPrime_X_sub_X {σ : Type} {a b c d : σ} (h : a ≠ b) (h' : c ≠ d)
    (hn : (c ≠ a ∧ c ≠ b) ∨ (d ≠ a ∧ d ≠ b)) :
    IsRelPrime (X a - X b : MvPolynomial σ ℝ) (X c - X d) := by
  classical
  refine (irreducible_X_sub_X h).isRelPrime_iff_not_dvd.2 fun hd => ?_
  rcases hn with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have := map_dvd (eval (Pi.single c (1 : ℝ))) hd
    simp [Pi.single_apply, h1.symm, h2.symm, h'.symm] at this
  · have := map_dvd (eval (Pi.single d (1 : ℝ))) hd
    simp [Pi.single_apply, h1.symm, h2.symm, h'] at this

theorem rootDiscr_dvd (ι : Type) [Fintype ι] (m : ι → ℕ) (P : MvPolynomial (Root m) ℝ)
    (hP : ∀ (τ : ι) (i j : Fin (m τ)), i < j → (X ⟨τ, j⟩ - X ⟨τ, i⟩ : MvPolynomial (Root m) ℝ) ∣ P) :
    GoodMetric.rootDiscr m ∣ P := by
  classical
  have ne : ∀ (τ : ι) (i j : Fin (m τ)), i ≠ j → (⟨τ, i⟩ : Root m) ≠ ⟨τ, j⟩ := fun τ i j h e =>
    h (eq_of_heq (Sigma.mk.inj e).2)
  unfold GoodMetric.rootDiscr
  refine Finset.prod_dvd_of_isRelPrime (fun τ _ τ' _ hτ => ?_) fun τ _ => ?_
  · refine IsRelPrime.prod_left fun j _ => IsRelPrime.prod_left fun i hi =>
      IsRelPrime.prod_right fun l _ => IsRelPrime.prod_right fun k hk => ?_
    refine isRelPrime_X_sub_X (ne _ _ _ (Finset.mem_Iio.1 hi).ne') (ne _ _ _ (Finset.mem_Iio.1 hk).ne')
      (Or.inl ⟨fun e => hτ (Sigma.mk.inj e).1.symm, fun e => hτ (Sigma.mk.inj e).1.symm⟩)
  refine Finset.prod_dvd_of_isRelPrime (fun j _ l _ hjl => ?_) fun j _ => ?_
  · refine IsRelPrime.prod_left fun i hi => IsRelPrime.prod_right fun k hk => ?_
    have hi := Finset.mem_Iio.1 hi
    have hk := Finset.mem_Iio.1 hk
    rcases lt_or_gt_of_ne hjl with h | h
    · exact isRelPrime_X_sub_X (ne _ _ _ hi.ne') (ne _ _ _ hk.ne')
        (Or.inl ⟨ne _ _ _ h.ne', ne _ _ _ (hi.trans h).ne'⟩)
    · exact (isRelPrime_X_sub_X (ne _ _ _ hk.ne') (ne _ _ _ hi.ne')
        (Or.inl ⟨ne _ _ _ h.ne', ne _ _ _ (hk.trans h).ne'⟩)).symm
  refine Finset.prod_dvd_of_isRelPrime (fun i hi k hk hik => ?_) fun i hi => hP τ i j (Finset.mem_Iio.1 hi)
  have hi := Finset.mem_Iio.1 hi
  have hk := Finset.mem_Iio.1 hk
  exact isRelPrime_X_sub_X (ne _ _ _ hi.ne') (ne _ _ _ hk.ne')
    (Or.inr ⟨ne _ _ _ hk.ne, ne _ _ _ hik.symm⟩)

end GlobalTheory.GoodMetric.DiscrDvd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagRelativeTangentTopChernDvdOfDifferencesDvdStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagRelativeTangentTopChern_dvd_of_differences_dvd : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (P : MvPolynomial (Root m) ℝ), (∀ (τ : ι) (i j : Fin (m τ)), i < j → (X ⟨τ, j⟩ - X ⟨τ, i⟩ : MvPolynomial (Root m) ℝ) ∣ P) → rootDiscr m ∣ P := by
  first | exact @GlobalTheory.GoodMetric.DiscrDvd.rootDiscr_dvd | exact GlobalTheory.GoodMetric.DiscrDvd.rootDiscr_dvd | (intros; apply GlobalTheory.GoodMetric.DiscrDvd.rootDiscr_dvd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeylAntisymmetrizationRenameBlockPermSign
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeylAntisymmetrizationRenameBlockPermSign
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

namespace GlobalTheory.GoodMetric

theorem antisymm_rename_sigmaCongrRight : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (Q : MvPolynomial (Root m) ℝ)
    (w : ∀ τ, Equiv.Perm (Fin (m τ))),
    rename (Equiv.sigmaCongrRight w) (antisymm Q) = ((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) • antisymm Q := by
  intro ι _ m Q w
  classical
  unfold antisymm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft w) _ _ (fun v => ?_)
  rw [map_zsmul, rename_rename, smul_smul]
  have hf : (⇑(Equiv.sigmaCongrRight w) ∘ fun x : Root m => (⟨x.1, v x.1 x.2⟩ : Root m)) =
      fun x : Root m => (⟨x.1, (Equiv.mulLeft w v) x.1 x.2⟩ : Root m) := by
    funext x; rfl
  rw [hf]
  congr 1
  have hs : (∏ τ, Equiv.Perm.sign ((Equiv.mulLeft w v) τ) : ℤˣ) =
      (∏ τ, Equiv.Perm.sign (w τ)) * ∏ τ, Equiv.Perm.sign (v τ) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    simp [Equiv.Perm.sign_mul]
  rw [hs, ← Units.val_mul, ← mul_assoc, Int.units_mul_self, one_mul]

end GlobalTheory.GoodMetric
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeylAntisymmetrizationRenameBlockPermSignStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weylAntisymmetrization_rename_block_perm_sign : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (Q : MvPolynomial (Root m) ℝ) (w : ∀ τ, Equiv.Perm (Fin (m τ))), rename (Equiv.sigmaCongrRight w) (antisymm Q) = ((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) • antisymm Q := by
  first | exact @GlobalTheory.GoodMetric.antisymm_rename_sigmaCongrRight | exact GlobalTheory.GoodMetric.antisymm_rename_sigmaCongrRight | (intros; apply GlobalTheory.GoodMetric.antisymm_rename_sigmaCongrRight <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.XSubXDvdOfRenameSwapEqNeg
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.XSubXDvdOfRenameSwapEqNeg
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

namespace GlobalTheory

theorem X_sub_X_dvd_sub_aeval_update_variable {σ : Type} [DecidableEq σ] (a b : σ) (P : MvPolynomial σ ℝ) :
    (X b - X a : MvPolynomial σ ℝ) ∣ P - aeval (Function.update (X : σ → MvPolynomial σ ℝ) b (X a)) P := by
  induction P using MvPolynomial.induction_on with
  | C r => simp [aeval_C]
  | add p q hp hq =>
    have h := dvd_add hp hq
    rw [map_add (f := _)]
    convert h using 1
    ring
  | mul_X p c hp =>
    rw [map_mul, aeval_X]
    have h2 : (X b - X a : MvPolynomial σ ℝ) ∣ X c - Function.update X b (X a) c := by
      by_cases h : c = b
      · subst h; simp
      · simp [Function.update_of_ne h]
    have e : p * X c - aeval (Function.update X b (X a)) p * Function.update X b (X a) c
        = (p - aeval (Function.update X b (X a)) p) * X c
          + aeval (Function.update X b (X a)) p * (X c - Function.update X b (X a) c) := by ring
    rw [e]
    exact dvd_add (dvd_mul_of_dvd_left hp _) (dvd_mul_of_dvd_right h2 _)

theorem swap_odd_dvd : ∀ {σ : Type} [DecidableEq σ] (a b : σ), a ≠ b → ∀ P : MvPolynomial σ ℝ,
    rename (Equiv.swap a b) P = -P → (X b - X a : MvPolynomial σ ℝ) ∣ P := by
  intro σ _ a b hab P hP
  have hcomp : (Function.update (X : σ → MvPolynomial σ ℝ) b (X a)) ∘ (Equiv.swap a b)
      = Function.update X b (X a) := by
    funext i
    simp only [Function.comp_apply]
    by_cases hia : i = a
    · subst hia
      rw [Equiv.swap_apply_left, Function.update_self, Function.update_of_ne hab]
    · by_cases hib : i = b
      · subst hib
        rw [Equiv.swap_apply_right, Function.update_of_ne hab, Function.update_self]
      · rw [Equiv.swap_apply_of_ne_of_ne hia hib]
  have h1 : aeval (Function.update (X : σ → MvPolynomial σ ℝ) b (X a)) P = - aeval (Function.update (X : σ → MvPolynomial σ ℝ) b (X a)) P := by
    have := congrArg (aeval (Function.update (X : σ → MvPolynomial σ ℝ) b (X a))) hP
    rw [aeval_rename, hcomp, map_neg] at this
    exact this
  have h0 : aeval (Function.update (X : σ → MvPolynomial σ ℝ) b (X a)) P = 0 := self_eq_neg.mp h1
  have := X_sub_X_dvd_sub_aeval_update_variable a b P
  rwa [h0, sub_zero] at this
end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.XSubXDvdOfRenameSwapEqNegStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.X_sub_X_dvd_of_rename_swap_eq_neg : ∀ {σ : Type} [DecidableEq σ] (a b : σ), a ≠ b → ∀ P : MvPolynomial σ ℝ, rename (Equiv.swap a b) P = -P → (X b - X a : MvPolynomial σ ℝ) ∣ P := by
  first | exact @GlobalTheory.swap_odd_dvd | exact GlobalTheory.swap_odd_dvd | (intros; apply GlobalTheory.swap_odd_dvd <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

namespace GlobalTheory.AntisymmChern

theorem antisymm_eq_chernRoots_mul_rootDiscr : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (Q : MvPolynomial (Root m) ℝ), ∃ R : MvPolynomial (ι × ℕ) ℝ, antisymm Q = chernRoots m R * rootDiscr m := by
  intro ι _ m Q
  classical
  obtain ⟨S, hS⟩ : rootDiscr m ∣ antisymm Q := GlobalTheory.T.flagRelativeTangentTopChern_dvd_of_differences_dvd ι m (antisymm Q) fun τ i j hij =>
    GlobalTheory.T.X_sub_X_dvd_of_rename_swap_eq_neg (⟨τ, i⟩ : Root m) ⟨τ, j⟩ (by simp [hij.ne]) _ (GlobalTheory.T.weylAntisymmetrization_rename_swap_neg ι m Q τ i j hij.ne)
  have hsym : ∀ w : ∀ τ, Equiv.Perm (Fin (m τ)), rename (Equiv.sigmaCongrRight w) S = S := by
    intro w
    have h1 := GlobalTheory.T.weylAntisymmetrization_rename_block_perm_sign ι m Q w
    rw [hS, map_mul, GlobalTheory.T.flagRelativeTangentTopChern_rename_block_perm ι m w, smul_mul_assoc] at h1
    have hs : ((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) ≠ 0 := Units.ne_zero _
    exact mul_left_cancel₀ (GlobalTheory.T.flagRelativeTangentTopChern_ne_zero ι m) (smul_right_injective _ hs h1)
  obtain ⟨R, hR⟩ := GlobalTheory.T.symmetric_poly_chern_roots ι m S hsym
  exact ⟨R, by rw [hS, hR, mul_comm]⟩

end GlobalTheory.AntisymmChern
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicOnProjectiveConst
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G GlobalTheory.CxPts

namespace GlobalTheory.ConstFn

variable {F : Type} [Field F] {X : Scheme.{0}} {p : X ⟶ Sp F} {σ : F →+* ℂ}

theorem ev_top_eq (a : Γ(X, ⊤)) (y : CxPts p σ) :
    ev p σ ⊤ a y = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (y.1.appTop.hom a) := by
  have h : ⊤ ≤ y.1 ⁻¹ᵁ (⊤ : X.Opens) := le_rfl
  show valR y.1 ⊤ a = _
  rw [valR, dite_eq_left h]
  rfl

theorem exists_ev_eq [UniversallyClosed p] [GeometricallyIntegral p] (a : Γ(X, ⊤)) :
    ∃ b : ℂ, ∀ y : CxPts p σ, ev p σ ⊤ a y = b := by
  have hZ : IsIntegral (pullback p (spMap σ)) :=
    GeometricallyIntegral.geometrically_isIntegral (f := p) (spMap σ) _ _ (.of_hasPullback _ _)
  let fs := pullback.fst p (spMap σ)
  let sn := pullback.snd p (spMap σ)
  let e : ℂ →+* Γ(pullback p (spMap σ), ⊤) :=
    sn.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  letI : Algebra ℂ Γ(pullback p (spMap σ), ⊤) := e.toAlgebra
  have hcomp : (algebraMap ℂ Γ(pullback p (spMap σ), ⊤)).comp
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp (spMap σ).appTop.hom) =
      fs.appTop.hom.comp p.appTop.hom := by
    have h : fs ≫ p = sn ≫ spMap σ := pullback.condition
    ext c
    have h' := congrArg (fun m : pullback p (spMap σ) ⟶ Sp F => m.appTop.hom c) h
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at h'
    simp only [RingHom.comp_apply]
    refine Eq.trans ?_ h'.symm
    show sn.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom _)) = _
    simp
  have hint : IsIntegral ℂ (fs.appTop.hom a) := by
    obtain ⟨P, hP, h0⟩ := isIntegral_appTop_of_universallyClosed p a
    refine ⟨P.map ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp (spMap σ).appTop.hom), hP.map _, ?_⟩
    rw [Polynomial.eval₂_map, hcomp, ← Polynomial.hom_eval₂, h0, map_zero]
  obtain ⟨r, hr⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ℂ)
    (K := integralClosure ℂ Γ(pullback p (spMap σ), ⊤))).2 ⟨_, hint⟩
  have hr' : e r = fs.appTop.hom a := congrArg Subtype.val hr
  refine ⟨r, fun y => ?_⟩
  let z : Sp ℂ ⟶ pullback p (spMap σ) :=
    pullback.lift y.1 (𝟙 _) (by rw [y.2, Category.id_comp])
  have h1 : z ≫ fs = y.1 := pullback.lift_fst _ _ _
  have h2 : z ≫ sn = 𝟙 _ := pullback.lift_snd _ _ _
  have h3 : y.1.appTop.hom a = z.appTop.hom (fs.appTop.hom a) := by
    rw [← h1, Scheme.Hom.comp_appTop]; rfl
  have h4 : z.appTop.hom (sn.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom r)) =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom r := by
    have e₂ : (z ≫ sn).appTop = sn.appTop ≫ z.appTop := Scheme.Hom.comp_appTop _ _
    rw [h2] at e₂
    have e₃ := congrArg (fun m => m.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom r)) e₂
    exact Eq.trans e₃.symm (by simp)
  rw [ev_top_eq, h3, ← hr']
  show (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (z.appTop.hom (sn.appTop.hom _)) = r
  rw [h4]
  simp

end GlobalTheory.ConstFn

theorem GlobalTheory.ConstFn.holoOn_univ_const : ∀ (F : Type) [Field F] (Y : GlobalTheory.ProjVar.Var F) (σ : F →+* ℂ) (R : AnRead Y.str σ Y.dim)
    (q : CxPts Y.str σ → ℂ), R.HoloOn Set.univ q → ∃ b : ℂ, ∀ z, q z = b := by
  intro F _ Y σ R q hq
  have hB := LB.isLB_triv Y.X
  have hs : (fun _ => q : (LB.triv Y.X).ι → CxPts Y.str σ → ℂ) ∈ R.holSec (LB.triv Y.X) := by
    refine ⟨⟨fun i j y hi _ => ?_, fun i y h => (h mem_ptsIn_top).elim⟩, fun i => hq.mono (Set.subset_univ _)⟩
    cases i; cases j
    rw [gv_self hB hi, one_mul]
  obtain ⟨x, hx⟩ := (AnRead.bijective_valC Y.isProjOver R hB).2 ⟨_, hs⟩
  let M : Submodule ℂ ((LB.triv Y.X).ι → CxPts Y.str σ → ℂ) :=
    { carrier := {s | ∃ b : ℂ, ∀ i z, s i z = b}
      zero_mem' := ⟨0, fun _ _ => rfl⟩
      add_mem' := fun {s t} ⟨b, hb⟩ ⟨c, hc⟩ => ⟨b + c, fun i z => by simp [hb, hc]⟩
      smul_mem' := fun c s ⟨b, hb⟩ => ⟨c * b, fun i z => by simp [hb]⟩ }
  obtain ⟨b, hb⟩ : SecC.val x ∈ M := SecC.val_mem_of (fun s => by
    obtain ⟨b, hb⟩ := GlobalTheory.ConstFn.exists_ev_eq (p := Y.str) (σ := σ) (s.f PUnit.unit)
    exact ⟨b, fun i z => by cases i; exact hb z⟩) x
  refine ⟨b, fun z => ?_⟩
  have e := congrArg Subtype.val hx
  rw [AnRead.coe_valC] at e
  have := hb PUnit.unit z
  rw [e] at this
  exact this
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSmoothHermitianMetricProjectiveVariety
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSmoothHermitianMetricProjectiveVariety
open AlgebraicGeometry MvPolynomial GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)

set_option autoImplicit false
noncomputable section
open Topology Filter
open scoped ContDiff Matrix ComplexOrder

namespace GlobalTheory.GoodMetric.SmoothMetric

theorem exists_partition {F : Type} [Field F] (σ : F →+* ℂ) (X : Var F)
    (W : CxPts X.str σ → Set (CxPts X.str σ)) (hWo : ∀ y, IsOpen (W y)) (hW : ∀ y, y ∈ W y) :
    ∃ (n : ℕ) (pt : Fin n → CxPts X.str σ) (χ : Fin n → CxPts X.str σ → ℝ),
      (∀ j y, 0 ≤ χ j y) ∧ (∀ y, ∑ j, χ j y = 1) ∧ (∀ j, tsupport (χ j) ⊆ W (pt j)) ∧
      ∀ j y, CInfAt (χ j) y := by
  classical
  haveI := CxPts.compactSpace σ X.isProjOver
  have hc : ∀ y, ∃ c : AlgChart X.str σ X.dim, y ∈ c.e.source ∧ c.e.source ⊆ W y := fun y => by
    obtain ⟨c, hc⟩ := AlgChart.exists_mem_source (p := X.str) (σ := σ) (D := X.dim) y
    exact ⟨c.restr (W y) (hWo y), ⟨hc, hW y⟩, Set.inter_subset_right⟩
  choose c hcy hcW using hc
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y => (c y).e.source)
    (fun y => (c y).e.open_source) (fun y _ => Set.mem_iUnion.2 ⟨y, hcy y⟩)
  let pt : Fin t.card → CxPts X.str σ := fun j => (t.equivFin.symm j).1
  let Lc := EuclideanSpace.equiv (Fin X.dim) ℂ
  let L := Lc.toHomeomorph
  let e : Fin t.card → OpenPartialHomeomorph (CxPts X.str σ) (Fin X.dim → ℂ) :=
    fun j => (c (pt j)).e.transHomeomorph L
  have hcov : ∀ y, ∃ j, y ∈ (e j).source := by
    intro y
    obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
    refine ⟨t.equivFin ⟨x, hx⟩, ?_⟩
    simpa [e, pt] using hy
  have htr : ∀ i j, ContDiffOn ℝ ∞ (e j ∘ (e i).symm) ((e i).target ∩ (e i).symm ⁻¹' (e j).source) := by
    intro i j
    have ho := isOpen_over (c (pt i)).e (c (pt j)).e.open_source
    have hg : ContDiffOn ℂ ∞ ((c (pt j)).e ∘ (c (pt i)).e.symm)
        ((c (pt i)).e.target ∩ (c (pt i)).e.symm ⁻¹' (c (pt j)).e.source) :=
      contDiffOn_euclidean.2 fun a => ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn _ _ _ ho
        (differentiableOn_euclidean.1 ((c (pt i)).holo_trans (c (pt j))) a)
    have h2 := (Lc.contDiff.restrict_scalars ℝ).comp_contDiffOn
      ((hg.restrict_scalars ℝ).comp (Lc.symm.contDiff.restrict_scalars ℝ).contDiffOn
        (s := Lc.symm ⁻¹' ((c (pt i)).e.target ∩ (c (pt i)).e.symm ⁻¹' (c (pt j)).e.source)) ?_)
    · refine h2.congr_mono ?_ ?_
      · intro v hv
        simp [e, L, Lc]
      · intro v hv
        simpa [e, L, Lc] using hv
    · intro v hv
      simpa using hv
  obtain ⟨χ, h0, h1, hs, hd⟩ := ReciprocityTheory.AnForm.exists_chart_partition e hcov htr
  refine ⟨t.card, pt, χ, h0, h1, fun j => (hs j).trans (hcW (pt j)), fun j y => ?_⟩
  obtain ⟨i, hi⟩ := hcov y
  have hi' : y ∈ (c (pt i)).e.source := hi
  refine cInfAt_of_chart (c (pt i)).e.open_source (c (pt i)) ?_ hi' hi'
  have h3 := (hd j i).comp (Lc.contDiff.restrict_scalars ℝ).contDiffOn
    (s := (c (pt i)).e.target) (fun v hv => by simpa [e, L, Lc] using hv)
  refine h3.congr_mono ?_ Set.inter_subset_left
  intro v hv
  simp [e, L, Lc]

end GlobalTheory.GoodMetric.SmoothMetric

namespace GlobalTheory.GoodMetric.SmoothMetric

theorem cInfAt_sum {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {κ : Type}
    (s : Finset κ) (f : κ → CxPts X.str σ → ℝ) {y : CxPts X.str σ} (h : ∀ j ∈ s, CInfAt (f j) y) :
    CInfAt (fun z => ∑ j ∈ s, f j z) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using cInfAt_const (p := X.str) 0 y
  | insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem exists_isMetricOn_top : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ)
    (E : Fr (ratOf X) m 0), ∃ H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ, IsMetricOn E ⊤ H := by
  intro F _ σ X ι _ m E
  classical
  choose U A hz hA hU using fun y : CxPts X.str σ => E.loc (under y)
  obtain ⟨n, pt, χ, h0, h1, hs, hd⟩ := exists_partition σ X (fun y => ptsIn X.str σ (U y))
    (fun y => isOpen_ptsIn _) (fun y => mem_ptsIn.2 (hz y))
  let T : Fin n → Mat m X.Fn → CxPts X.str σ → Mat m ℂ := fun j B z => (B * (A (pt j))⁻¹).map (ratVal · z)

  have hpar : ∀ j y, y ∈ tsupport (χ j) → ∀ B ∈ E.S (under y),
      Par 0 ((ratOf X).O (under y)).toSubring (B * (A (pt j))⁻¹) := fun j y hy B hB =>
    (hU (pt j) (under y) (mem_ptsIn.1 (hs j hy)) B).1 hB
  have hpar' : ∀ j y, χ j y ≠ 0 → ∀ B ∈ E.S (under y),
      Par 0 ((ratOf X).O (under y)).toSubring (B * (A (pt j))⁻¹) := fun j y hy =>
    hpar j y (subset_tsupport _ hy)
  refine ⟨fun B z τ => ∑ j, ((χ j z : ℝ) : ℂ) • (T j B z τ * (T j B z τ)ᴴ), ⟨?_, ?_, ?_⟩⟩
  · intro y _ B hB τ
    obtain ⟨j, hj⟩ : ∃ j, χ j y ≠ 0 := by
      by_contra hne
      simp only [not_exists, not_not] at hne
      have := h1 y
      simp [hne] at this
    have hpos : 0 < χ j y := lt_of_le_of_ne (h0 j y) (Ne.symm hj)
    obtain ⟨ψ, hψ⟩ := exists_ratVal_hom (X := X) (σ := σ) y
    have hdet := ((hpar' j y hj B hB).map_of (ratVal · y) ψ hψ).det_ne τ
    have hPD : (((χ j y : ℝ) : ℂ) • (T j B y τ * (T j B y τ)ᴴ)).PosDef :=
      Matrix.PosDef.smul (Matrix.PosDef.mul_conjTranspose_self _ (Matrix.vecMul_injective_iff_isUnit.2
        ((Matrix.isUnit_iff_isUnit_det _).2 hdet.isUnit))) (by exact_mod_cast hpos)
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    refine hPD.add_posSemidef (Matrix.posSemidef_sum _ fun i _ => ?_)
    exact (Matrix.posSemidef_self_mul_conjTranspose _).smul (Complex.zero_le_real.2 (h0 i y))
  · intro y _ B hB τ i k
    have key : ∀ g : ℂ →L[ℝ] ℝ, CInfAt (fun z =>
        g ((∑ j, ((χ j z : ℝ) : ℂ) • (T j B z τ * (T j B z τ)ᴴ)) i k)) y := by
      intro g
      have e : (fun z => g ((∑ j, ((χ j z : ℝ) : ℂ) • (T j B z τ * (T j B z τ)ᴴ)) i k)) =
          fun z => ∑ j ∈ Finset.univ, χ j z * g ((T j B z τ * (T j B z τ)ᴴ) i k) := by
        funext z
        set_option synthInstance.maxHeartbeats 100000 in
          rw [Matrix.sum_apply, map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Matrix.smul_apply, smul_eq_mul, ← Complex.real_smul, map_smul, smul_eq_mul]
      rw [e]
      refine cInfAt_sum _ _ fun j _ => ?_
      by_cases hy : y ∈ tsupport (χ j)
      · have hr (x : Fin (m τ) × Fin (m τ)) : RegAt (under y) ((B * (A (pt j))⁻¹) τ x.1 x.2) :=
          mem_O_ratOf.1 ((hpar j y hy B hB τ).1 _ _)
        have hG : ContDiff ℝ (⊤ : ℕ∞) fun w : Fin (m τ) × Fin (m τ) → ℂ => ∑ l, w (i, l) * star (w (k, l)) :=
          ContDiff.sum fun l _ => (contDiff_apply ℝ (fun _ => ℂ) _).mul (Complex.conjCLE.contDiff.comp (contDiff_apply ℝ (fun _ => ℂ) _))
        refine ((hd j y).comp₂ (cInfAt_ratVal hr (g.contDiff.comp hG))
          (contDiff_fst.mul contDiff_snd)).congr (Eventually.of_forall fun z => ?_)
        simp [T, Matrix.mul_apply, Mat.map]
      · have hz : χ j =ᶠ[𝓝 y] fun _ => 0 := by
          rw [tsupport, ← Set.mem_compl_iff] at hy
          filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hy] with z hz'
          exact Function.notMem_support.1 fun h => hz' (subset_closure h)
        refine (cInfAt_const (p := X.str) 0 y).congr ?_
        filter_upwards [hz] with z hz'
        simp [hz']
    exact ⟨key Complex.reCLM, key Complex.imCLM⟩
  · intro y _ B hB B' hB' τ
    obtain ⟨ψ, hψ⟩ := exists_ratVal_hom (X := X) (σ := σ) y
    have hBB : Par 0 ((ratOf X).O (under y)).toSubring (B' * B⁻¹) := (Fr.mem_iff hB).1 hB'
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : χ j y = 0
    · simp [hj]
    have e := Par.map_mul_of hBB (hpar' j y hj B hB) (ratVal · y) ψ hψ
    rw [mul_assoc, ← mul_assoc B⁻¹, Mat.inv_mul (Fr.det_ne hB), one_mul] at e
    simp only [T]
    rw [e, Pi.mul_apply, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

end GlobalTheory.GoodMetric.SmoothMetric
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSmoothHermitianMetricProjectiveVarietyStatement
open AlgebraicGeometry MvPolynomial GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smooth_hermitianMetric_projective_variety : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0), ∃ H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ, IsMetricOn E ⊤ H := by
  first | exact @GlobalTheory.GoodMetric.SmoothMetric.exists_isMetricOn_top | exact GlobalTheory.GoodMetric.SmoothMetric.exists_isMetricOn_top | (intros; apply GlobalTheory.GoodMetric.SmoothMetric.exists_isMetricOn_top <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepGroupCharacterInverseTypeAtLifts
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepGroupCharacterInverseTypeAtLifts
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.Col2.AdT

section Split

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {S Q : Finset (HeightOneSpectrum (𝓞 E))}


open Classical in
def compVal (Λ : LevFam E K n S) (Θ : LevQFam E K n Q) (k1 : ↥Λ.grp) (k2 : ↥Θ.grp) (p : HeightOneSpectrum (𝓞 E)) : Kˣ :=
  if h : p ∈ S then (Λ ⟨p, h⟩).lam ⟨k1.1 ⟨p, h⟩, k1.2 _ (Set.mem_univ _)⟩
  else if h' : p ∈ Q then (Θ ⟨p, h'⟩).lam ⟨k2.1 ⟨p, h'⟩, k2.2 _ (Set.mem_univ _)⟩ else 1

theorem compVal_left (Λ : LevFam E K n S) (Θ : LevQFam E K n Q) (k1 : ↥Λ.grp) (k2 : ↥Θ.grp) {p : HeightOneSpectrum (𝓞 E)} (h : p ∈ S) :
    compVal Λ Θ k1 k2 p = (Λ ⟨p, h⟩).lam ⟨k1.1 ⟨p, h⟩, k1.2 _ (Set.mem_univ _)⟩ := by
  unfold compVal
  rw [dif_pos h]

theorem compVal_right (Λ : LevFam E K n S) (Θ : LevQFam E K n Q) (k1 : ↥Λ.grp) (k2 : ↥Θ.grp) {p : HeightOneSpectrum (𝓞 E)} (h : p ∉ S)
    (h' : p ∈ Q) : compVal Λ Θ k1 k2 p = (Θ ⟨p, h'⟩).lam ⟨k2.1 ⟨p, h'⟩, k2.2 _ (Set.mem_univ _)⟩ := by
  unfold compVal
  rw [dif_neg h, dif_pos h']


open Classical in
theorem prod_compVal (hd : Disjoint S Q) (Λ : LevFam E K n S) (Θ : LevQFam E K n Q) (k1 : ↥Λ.grp) (k2 : ↥Θ.grp) :
    ∏ p ∈ S ∪ Q, compVal Λ Θ k1 k2 p = Λ.chr k1 * Θ.chr k2 := by
  have e1 : Λ.chr k1 = _ := piChar_apply (fun w => (Λ w).H) (fun w => (Λ w).lam) k1
  have e2 : Θ.chr k2 = _ := piChar_apply (fun w => (Θ w).H) (fun w => (Θ w).lam) k2
  rw [e1, e2, Finset.prod_union hd, ← Finset.prod_coe_sort S, ← Finset.prod_coe_sort Q]
  refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun w _ => ?_) (Finset.prod_congr rfl fun w _ => ?_)
  · exact dif_pos w.2
  · exact (dif_neg (Finset.disjoint_right.1 hd w.2)).trans (dif_pos w.2)

end Split
end GlobalTheory.Mem.Col2.AdT

namespace GlobalTheory.Mem.Col2.AdT

section Cong

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem congE_mul_one {P : HeightOneSpectrum (𝓞 E)} {c : ℕ} {k g g' : Sp E n ≃ₗ[E] Sp E n}
    (hk : k ∈ GLint E n P) (hkg : k * g' = 1) (h : CongE P c g g') : CongE P c (k * g) 1 := by
  intro x hx
  have e1 : (k * g) x - (1 : Sp E n ≃ₗ[E] Sp E n) x = k (g x - g' x) := by
    rw [map_sub, ← LinearEquiv.mul_apply k g', hkg]
    rfl
  rw [e1, ← map_smul]
  exact (hk _).2 (h x hx)

end Cong
end GlobalTheory.Mem.Col2.AdT

namespace GlobalTheory.Mem.Col2.AdT

variable {B : Base} {X : PreX B.toPre}

theorem chiInv_at_type (I : TC B X) (hOk : I.Ok) (a : I.ι) (i : ℕ) (al : (I.idx a).β i) (P : SBof I a)
    (hP : P.1 ∈ (B.primes X).vGs) (gP g'P : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) (r : AutY B.fields B.R i)
    (hr : r ∈ Loc.Cbe (Jat (Pr := B.primes X) (I.cst a).sharp i P.1) ((I.idx a).h i al P))
    (hrx : ∀ x, r (Loc.inX B.fields.E (B.R.N i) (cOf B.R i) x) = Loc.inX B.fields.E (B.R.N i) (cOf B.R i) (gP x))
    (κw : GL (Fin (B.R.N i)) (𝓞 B.fields.E ⧸ P.1.asIdeal)) (hκw : κw ∈ (((I.idx a).levG i al) ⟨P.1, hP⟩).H)
    (hred' : ∀ x ∈ stdAt B.fields.E (B.R.N i) P.1, redV P.1 (g'P x) = (κw⁻¹).1.mulVec (redV P.1 x))
    (hcong : CongE P.1 ((I.cst a).D P) gP g'P) :
    chiInv I.Ch I.sel (I.tup a) (I.cst a) i P ((I.idx a).h i al P) r =
      (((((I.idx a).levG i al) ⟨P.1, hP⟩).lam ⟨κw, hκw⟩ : B.fields.Kˣ) : B.fields.K)⁻¹ := by
  have hL := hOk.idx_ok a
  have hD : (I.cst a).D P = 1 := hL.depthG P hP
  have hred : ∀ x ∈ stdAt B.fields.E (B.R.N i) P.1, redV P.1 (gP x) = (κw⁻¹).1.mulVec (redV P.1 x) := by
    intro x hx
    rw [← hred' x hx]
    have h1 := (mem_localization_standardLattice _ _).1 (hcong x hx)
    rw [hD, pow_one] at h1
    have hq0 : ((qOf P.1 : ℕ) : B.fields.E) ≠ 0 := GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero P.1
    funext l
    have e1 : gP x l = g'P x l + (qOf P.1 : B.fields.E) * (((qOf P.1 : ℕ) : B.fields.E)⁻¹ • (gP x - g'P x)) l := by
      rw [Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
      field_simp
      ring
    show redP P.1 (gP x l) = redP P.1 (g'P x l)
    rw [e1]
    exact GlobalTheory.LastSteps.redP_add_q (h1 l)
  have hc := hL.chrG i al ⟨P.1, hP⟩ (⟨κw, hκw⟩)⁻¹ gP r hr hrx hred
  exact hc.symm.trans ((congrArg Units.val (map_inv (((I.idx a).levG i al) ⟨P.1, hP⟩).lam _)).trans (Units.val_inv_eq_inv_val _))

end GlobalTheory.Mem.Col2.AdT

namespace GlobalTheory.Mem.Col2.AdT

variable {B : Base} {X : PreX B.toPre}

theorem chiInv_at_twist (I : TC B X) (hOk : I.Ok) (a : I.ι) (i : ℕ) (hi : i < B.R.m) (al : (I.idx a).β i) (P : SBof I a)
    (hQ : P.1 ∈ I.Q a) (gP g'P : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) (r : AutY B.fields B.R i)
    (hr : r ∈ Loc.Cbe (Jat (Pr := B.primes X) (I.cst a).sharp i P.1) ((I.idx a).h i al P))
    (hrx : ∀ x, r (Loc.inX B.fields.E (B.R.N i) (cOf B.R i) x) = Loc.inX B.fields.E (B.R.N i) (cOf B.R i) (gP x))
    (κQ : ↥(GLint B.fields.E (B.R.N i) P.1)) (hκQ : κQ ∈ (((I.idx a).levQ i al) ⟨P.1, hQ⟩).H)
    (hg' : g'P = (κQ⁻¹).1) (hcong : CongE P.1 ((I.cst a).D P) gP g'P) :
    chiInv I.Ch I.sel (I.tup a) (I.cst a) i P ((I.idx a).h i al P) r =
      (((((I.idx a).levQ i al) ⟨P.1, hQ⟩).lam ⟨κQ, hκQ⟩ : B.fields.Kˣ) : B.fields.K)⁻¹ := by
  have hL := hOk.idx_ok a
  have hg : gP ∈ prCat (Pr := B.primes X) (R := B.R) (I.cst a).sharp i P.1 ((I.idx a).h i al P) := ⟨r, hr, hrx⟩
  let gI : ↥(GLint B.fields.E (B.R.N i) P.1) := ⟨gP, hL.int i al P hg⟩
  have hH : gI ∈ (((I.idx a).levQ i al) ⟨P.1, hQ⟩).H := by
    rw [hL.grpQ i al ⟨P.1, hQ⟩]
    exact Subgroup.mem_subgroupOf.2 hg
  have hc := hL.chrQ i al ⟨P.1, hQ⟩ ⟨gI, hH⟩ r hr hrx
  have hkg : κQ.1 * g'P = 1 := by
    rw [hg']
    exact congrArg Subtype.val (mul_inv_cancel κQ)
  have hcd : CongE P.1 ((I.cst a).D P) (κQ * gI).1 1 := congE_mul_one (g := gP) κQ.2 hkg hcong
  obtain ⟨hdH, hdl⟩ := levQ_deep I hOk a i hi al P hQ (κQ * gI) hcd
  have e2 : (⟨gI, hH⟩ : ↥(((I.idx a).levQ i al) ⟨P.1, hQ⟩).H) = (⟨κQ, hκQ⟩)⁻¹ * ⟨κQ * gI, hdH⟩ :=
    Subtype.ext (by show gI = κQ⁻¹ * (κQ * gI); group)
  have h4 : (((I.idx a).levQ i al) ⟨P.1, hQ⟩).lam ((⟨κQ, hκQ⟩)⁻¹ * ⟨κQ * gI, hdH⟩) = ((((I.idx a).levQ i al) ⟨P.1, hQ⟩).lam ⟨κQ, hκQ⟩)⁻¹ :=
    ((map_mul (((I.idx a).levQ i al) ⟨P.1, hQ⟩).lam _ _).trans ((congrArg _ hdl).trans (mul_one _))).trans (map_inv (((I.idx a).levQ i al) ⟨P.1, hQ⟩).lam _)
  exact hc.symm.trans ((congrArg Units.val ((congrArg (((I.idx a).levQ i al) ⟨P.1, hQ⟩).lam e2).trans h4)).trans (Units.val_inv_eq_inv_val _))

end GlobalTheory.Mem.Col2.AdT

namespace GlobalTheory.Mem.Col2.AdT


open Classical in
theorem chr_mul_prod_midAt : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i < B.R.m) (b : (I.stp u a i).β) (κ : (I.stp u a i).G b) (g g' : SBof I a → Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) (z : SBof I a → B.fields.K), (∀ P, MidAt I hi b P (g P) (z P) ∧ LiftsInv I κ P (g' P) ∧ CongE P.1 ((I.cst a).D P) (g P) (g' P)) → (((I.stp u a i).chr b κ : B.fields.Kˣ) : B.fields.K) * ∏ P, z P = 1 := by
  intro B X I hOk u a i hi b κ g g' z H
  obtain ⟨al, rfl⟩ : ∃ al, b = Idx.of al hi := ⟨_, (Idx.of_get b hi hi).symm⟩
  let k1 : ↥((I.idx a).levG i al).grp := κ.2.1
  let k2 : ↥((I.idx a).levQ i al).grp := κ.2.2
  have e : (((I.stp u a i).chr (Idx.of al hi) κ : B.fields.Kˣ) : B.fields.K) =
      ((((I.idx a).levG i al).chr k1 * ((I.idx a).levQ i al).chr k2 : B.fields.Kˣ) : B.fields.K) := rfl
  rw [e]
  have hd : Disjoint (B.primes X).vGs (I.Q a) :=
    Finset.disjoint_right.2 fun {P} hP => GlobalTheory.Mem.Col2.TC.Q_notMem_of_ok hOk a P hP
  have hprod : ∏ P : SBof I a, compVal ((I.idx a).levG i al) ((I.idx a).levQ i al) k1 k2 P.1 =
      ((I.idx a).levG i al).chr k1 * ((I.idx a).levQ i al).chr k2 := by
    rw [Finset.prod_coe_sort (SBof I a) (compVal ((I.idx a).levG i al) ((I.idx a).levQ i al) k1 k2)]
    exact prod_compVal hd _ _ k1 k2
  have hz : ∀ P : SBof I a, z P = ((compVal ((I.idx a).levG i al) ((I.idx a).levQ i al) k1 k2 P.1 : B.fields.Kˣ) : B.fields.K)⁻¹ := by
    intro P
    obtain ⟨⟨r, hr, hrx, hzr⟩, hlift, hcong⟩ := H P
    rw [hzr]
    by_cases hP : P.1 ∈ (B.primes X).vGs
    · refine (chiInv_at_type I hOk a i al P hP (g P) (g' P) r hr hrx (k1.1 ⟨P.1, hP⟩) (k1.2 _ (Set.mem_univ _))
        (hlift.2.1 hP) hcong).trans ?_
      rw [compVal_left _ _ k1 k2 hP]
    · have hQ : P.1 ∈ I.Q a := (Finset.mem_union.mp P.2).resolve_left hP
      refine (chiInv_at_twist I hOk a i hi al P hQ (g P) (g' P) r hr hrx (k2.1 ⟨P.1, hQ⟩) (k2.2 _ (Set.mem_univ _))
        (hlift.2.2 hQ) hcong).trans ?_
      exact congrArg (fun x : B.fields.Kˣ => (x : B.fields.K)⁻¹) (compVal_right _ _ k1 k2 hP hQ).symm
  rw [← hprod, Finset.prod_congr rfl fun P _ => hz P, Units.coe_prod, Finset.prod_inv_distrib]
  exact mul_inv_cancel₀ (Finset.prod_ne_zero_iff.2 fun P _ => Units.ne_zero _)

end GlobalTheory.Mem.Col2.AdT

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepGroupCharacterInverseTypeAtLiftsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.step_group_character_inverse_type_at_lifts : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i < B.R.m) (b : (I.stp u a i).β) (κ : (I.stp u a i).G b) (g g' : SBof I a → Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) (z : SBof I a → B.fields.K), (∀ P, MidAt I hi b P (g P) (z P) ∧ LiftsInv I κ P (g' P) ∧ CongE P.1 ((I.cst a).D P) (g P) (g' P)) → (((I.stp u a i).chr b κ : B.fields.Kˣ) : B.fields.K) * ∏ P, z P = 1 := by
  first | exact @GlobalTheory.Mem.Col2.AdT.chr_mul_prod_midAt | exact GlobalTheory.Mem.Col2.AdT.chr_mul_prod_midAt | (intros; apply GlobalTheory.Mem.Col2.AdT.chr_mul_prod_midAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LUnifAtDat
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.Bl

open Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Mult


set_option maxHeartbeats 1000000 in
theorem lUnif_atDat : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram →
    GlobalTheory.Mem.Top.Bl.AtDat fun _ B f T w Z hX Wt z => z.R.toRealDat.LUnif := by
  intro _ _ _
  refine StepW.of_all fun K B f T w _ _ _ Z hX Wt z _ _ hEx hIn => ?_
  have hch := z.pins.char
  have hC : GlobalTheory.RealGeo.PreChar z.R.toRealDat :=
    ⟨hch.base.lev, hch.base.grp.red_R, hch.base.grp.red_L, hch.base.grp.record, hch.base.fam, hch.base.models,
      RealDat.chain_of_weak hch.base.chain hEx, RealDat.thP_of_weak hch.base.thP hEx⟩
  have hχ : z.R.toRealDat.grp_chiW := hch.base.grp.chiW
  have ht : TieIn z.core z.R.toRealDat z.geo.κ z.geo.v₀ :=
    ⟨z.geo.fw.laws, z.geo.fw.alg_eq, z.geo.fw.kap, z.geo.fw.hv₀, z.geo.fw.chiR, z.geo.fw.x0⟩
  have hp : z.core.pb = z.R.toRealDat.C.P.pb :=
    GlobalTheory.PinsFixHalf.pb_eq_of_pins z.core z.R.toRealDat z.geo.κ z.geo.v₀ z.geo.O hC.lev z.geo.fw.laws z.geo.pins
  have hx := GlobalTheory.T.exists_equivariant_unit_constants_goodEmbedding z.core z.R.toRealDat z.geo.κ z.geo.v₀ z.geo.O hC.lev ht hp z.geo.pins
  have hU := hIn.jUnif
  intro i σ
  exact ⟨(GlobalTheory.TiedUnif.indep_span_of_tie z.geo.fw hC.models.HW z.geo.bar hU i σ).1,
    (GlobalTheory.TiedUnif.indep_span_of_tie z.geo.fw hC.models.HW z.geo.bar hU i σ).2,
    GlobalTheory.TiedUnif.rhoIs_of_eqAt z.geo.fw hC.models.HW hC.models.gW hχ z.geo.bar z.geo.rhoGeo hU i σ
      (fun h hV => z.geo.equivAll i _ h hV (hx i _ h hV))
      fun h hV => z.geo.equivAll i _ (good_resC z.core h) hV (hx i _ (good_resC z.core h) hV)⟩

end GlobalTheory.Mem.Top.Bl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLtGrpTrue
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw

theorem exists_lt_grpTrue (hG : GlobalTheory.Published.GreenCuspidal) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T)
    (hO : K.Over B.toPre) (hX : B.fields.Ok) (G : GJStage B w.C) :
    ∃ Z : w.Lt, Z.G = G ∧ GrpTrue Z.N f ∧ GrpAt (w.st Z) w.I ∧ DV.KapDef (w.D Z) := by
  obtain ⟨R⟩ := GlobalTheory.Mem.Df.rowsDef_nonempty w.I w.ok w.pins w.l hX
  obtain ⟨kb, ks, hk⟩ := GlobalTheory.Mem.Df.Model.exists_ka B
  let W' : RowsRest B w.C :=
    { R.W with
      eOp := fun _ => 0
      eOp_idem := fun _ => LinearMap.comp_zero _
      eOp_sa := fun _ => LinearMap.IsSymmetric.zero
      kaBig := kb
      kaSmall := ks }
  obtain ⟨V, -⟩ := GlobalTheory.Mem.DivModel.exists_divStage B w.C W'
  obtain ⟨S, -⟩ := GlobalTheory.Mem.SProv.exists_sStage_true K B w.C W' G.cd hO (GlobalTheory.Mem.Df.cols_pos w.I w.ok w.pins w.l hX)
    (show R.W.Drows ≤ R.W.Dall by rw [R.std.drows, R.std.dall])
  have hMt : ∀ (μ : w.C.Tup) (j : ℕ), W'.eMt μ j = 0 := fun μ j => by
    haveI := R.std.mt μ j
    exact LinearMap.ext fun _ => Subsingleton.elim _ _
  obtain ⟨N, -, -, hN, -⟩ := GlobalTheory.Mem.Top.exists_nStage_grpTrue hG B w.C W' R.std.sha (fun j v _ _ => R.std.eta j v)
    (fun _ => rfl) hMt f
  refine ⟨⟨W', V, S, N, G⟩, rfl, hN, GlobalTheory.Mem.R3.Model.grpAt_of_grpTrue (w.st ⟨W', V, S, N, G⟩) w.I w.ok (by show GrpTrue N w.I.C; rw [w.C_eq]; exact hN),
    hk w.C W' rfl rfl V S N G⟩

end GlobalTheory.Mem.R3.Rw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdlAlongEqIdealAlong
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.Toroidal GlobalTheory.IndefiniteRowSideFullHecke.NormalisedBlowupCone GlobalTheory.LocM

namespace GlobalTheory.LocM

theorem stalkId_ofIdealTop {Y : Scheme.{0}} [IsAffine Y] (K : Ideal Γ(Y, ⊤)) (y : Y) :
    FinalTheorems.stalkId (Scheme.IdealSheafData.ofIdealTop K) y = K.map (Y.presheaf.germ ⊤ y trivial).hom := by
  rw [ds_stalkId_eq_map _ ⟨⊤, isAffineOpen_top Y⟩ y trivial, Scheme.IdealSheafData.ofIdealTop_ideal,
    Ideal.map_map, ← CommRingCat.hom_comp]
  congr 2
  exact Y.presheaf.germ_res (homOfLE (le_top : (⊤ : Y.Opens) ≤ ⊤)) y (by trivial)

theorem ideal_top_ofIdealTop {Y : Scheme.{0}} [IsAffine Y] (K : Ideal Γ(Y, ⊤)) :
    (Scheme.IdealSheafData.ofIdealTop K).ideal ⟨⊤, isAffineOpen_top Y⟩ = K := by
  rw [Scheme.IdealSheafData.ofIdealTop_ideal]
  have : Y.presheaf.map (homOfLE (le_top : (⊤ : Y.Opens) ≤ ⊤)).op = 𝟙 _ := by
    rw [← Y.presheaf.map_id]; rfl
  rw [this]
  simp

theorem comap_eq_ofIdealTop (X : Scheme.{0}) (J : X.IdealSheafData) (R : Type) [CommRing R] [IsLocalRing R]
    (χ : Sp R ⟶ X) (U : X.affineOpens) (hle : ⊤ ≤ χ ⁻¹ᵁ U.1) :
    J.comap χ = Scheme.IdealSheafData.ofIdealTop ((J.ideal U).map (χ.appLE U.1 ⊤ hle).hom) := by
  refine (GlobalTheory.Vanishing.eq_comap_of_stalk fun z => ?_).symm
  have hz : χ z ∈ U.1 := hle trivial
  rw [stalkId_ofIdealTop, ds_stalkId_eq_map J U _ hz, Ideal.map_map, Ideal.map_map, ← CommRingCat.hom_comp,
    ← CommRingCat.hom_comp, Scheme.Hom.germ_stalkMap, Scheme.Hom.appLE, Category.assoc]
  congr 3
  exact (Sp R).presheaf.germ_res (homOfLE hle) z (by trivial)

theorem idlAlong_eq_idealAlong (X : Scheme.{0}) (J : X.IdealSheafData) (R : Type) [CommRing R] [IsLocalRing R]
    (χ : Sp R ⟶ X) : idlAlong J χ = idealAlong J χ := by
  obtain ⟨U, hU, hx, -⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
    (show χ (closedPoint R) ∈ (⊤ : X.Opens) from trivial)
  have hle : ⊤ ≤ χ ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem χ hx).ge
  unfold idlAlong idealAlong
  rw [comap_eq_ofIdealTop X J R χ ⟨U, hU⟩ hle, ideal_top_ofIdealTop, ds_stalkId_eq_map J ⟨U, hU⟩ _ hx,
    Ideal.map_map, Ideal.map_map, ← CommRingCat.hom_comp, ← CommRingCat.hom_comp, Scheme.germ_stalkClosedPointTo]
  congr 2

end GlobalTheory.LocM
end
end
