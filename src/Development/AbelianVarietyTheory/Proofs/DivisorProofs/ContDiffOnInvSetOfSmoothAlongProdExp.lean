module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedFDerivWordEqCoeff

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnInvSetOfSmoothAlongProdExp
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnInvSetOfSmoothAlongProdExp
open NumberField
open scoped ContDiff

namespace GlobalTheory.SecondKind

open GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] {d : ℕ}

theorem prod_ofFn_eq_of_ne {M : Type*} [Monoid M] {k : ℕ} (f : Fin k → M) (i : Fin k)
    (h : ∀ j, j ≠ i → f j = 1) : (List.ofFn f).prod = f i := by
  induction k with
  | zero => exact i.elim0
  | succ k ih =>
    rw [List.ofFn_succ, List.prod_cons]
    cases i using Fin.cases with
    | zero =>
      rw [List.prod_eq_one, mul_one]
      intro x hx
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
      exact h _ (Fin.succ_ne_zero j)
    | succ i =>
      rw [h 0 (Fin.succ_ne_zero i).symm, one_mul]
      exact ih _ i fun j hj => h _ fun e => hj (Fin.succ_injective _ e)

theorem contDiff_prodExp (y : Lie E d) {k : ℕ} (X : Fin k → Matrix (Fin d) (Fin d) (Cinf E)) :
    ContDiff ℝ ∞ (fun t : Fin k → ℝ =>
      toL (Matrix.of y * (List.ofFn fun i => NormedSpace.exp (t i • X i)).prod)) := by
  letI : NormedRing (Matrix (Fin d) (Fin d) (Cinf E)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin d) (Fin d) (Cinf E)) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix (Fin d) (Fin d) (Cinf E)) := FiniteDimensional.complete ℝ _
  let T : Matrix (Fin d) (Fin d) (Cinf E) →L[ℝ] Lie E d :=
    LinearMap.toContinuousLinearMap (LinearMap.id : Lie E d →ₗ[ℝ] Lie E d)
  have hexp : ContDiff ℝ ∞ (NormedSpace.exp : Matrix (Fin d) (Fin d) (Cinf E) → _) :=
    contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
  have hprod : ∀ (n : ℕ) (g : Fin n → (Fin k → ℝ) → Matrix (Fin d) (Fin d) (Cinf E)),
      (∀ i, ContDiff ℝ ∞ (g i)) → ContDiff ℝ ∞ (fun t => (List.ofFn fun i => g i t).prod) := by
    intro n
    induction n with
    | zero => intro g _; simpa using contDiff_const
    | succ n ih =>
      intro g hg
      simp only [List.ofFn_succ, List.prod_cons]
      exact (hg 0).mul (ih _ fun i => hg _)
  have h := hprod k (fun i t => NormedSpace.exp (t i • X i))
    fun i => hexp.comp ((contDiff_apply ℝ (fun _ => ℝ) i).smul contDiff_const)
  exact T.contDiff.comp (contDiff_const.mul h)

end GlobalTheory.SecondKind

namespace GlobalTheory.SecondKind

open GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] {d : ℕ}

theorem hasDerivAt_mulExp (y : Lie E d) (Z : Matrix (Fin d) (Fin d) (Cinf E)) :
    HasDerivAt (fun s : ℝ => toL (Matrix.of y * NormedSpace.exp (s • Z))) (toL (Matrix.of y * Z)) 0 := by
  letI : NormedRing (Matrix (Fin d) (Fin d) (Cinf E)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin d) (Fin d) (Cinf E)) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix (Fin d) (Fin d) (Cinf E)) := FiniteDimensional.complete ℝ _
  let T : Matrix (Fin d) (Fin d) (Cinf E) →L[ℝ] Lie E d :=
    LinearMap.toContinuousLinearMap (LinearMap.id : Lie E d →ₗ[ℝ] Lie E d)
  have h := ((hasDerivAt_exp_smul_const' (𝕂 := ℝ) Z (0 : ℝ)).const_mul (Matrix.of y))
  rw [zero_smul, NormedSpace.exp_zero, mul_one] at h
  exact T.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h

theorem fderiv_prodExp (y : Lie E d) {k : ℕ} (X : Fin k → Matrix (Fin d) (Fin d) (Cinf E)) (i : Fin k) (c : ℝ) :
    fderiv ℝ (fun t : Fin k → ℝ =>
      toL (Matrix.of y * (List.ofFn fun i => NormedSpace.exp (t i • X i)).prod)) 0 (Pi.single i c) =
      c • toL (Matrix.of y * X i) := by
  set Θ := fun t : Fin k → ℝ =>
      toL (Matrix.of y * (List.ofFn fun i => NormedSpace.exp (t i • X i)).prod)
  have hΘ : HasFDerivAt Θ (fderiv ℝ Θ 0) (0 : Fin k → ℝ) :=
    ((contDiff_prodExp y X).differentiable (by simp)).differentiableAt.hasFDerivAt
  let J : ℝ →L[ℝ] (Fin k → ℝ) := ContinuousLinearMap.single ℝ (fun _ : Fin k => ℝ) i
  have hJ0 : J 0 = 0 := map_zero J
  have h1 : HasFDerivAt (Θ ∘ J) ((fderiv ℝ Θ 0).comp J) 0 := by
    have hΘ' : HasFDerivAt Θ (fderiv ℝ Θ 0) (J 0) := by rw [hJ0]; exact hΘ
    exact hΘ'.comp (0 : ℝ) J.hasFDerivAt
  have e : Θ ∘ J = fun s : ℝ => toL (Matrix.of y * NormedSpace.exp (s • X i)) := by
    funext s
    simp only [Function.comp_apply, Θ]
    congr 2
    rw [prod_ofFn_eq_of_ne _ i]
    · simp [J]
    · intro j hj
      simp [J, Pi.single_eq_of_ne hj]
  rw [e] at h1
  have h2 := h1.hasDerivAt.unique (hasDerivAt_mulExp y (X i))
  have h3 : Pi.single i c = c • J 1 := by
    simp [J, ← Pi.single_smul]
  rw [h3, map_smul]
  simpa using congrArg (c • ·) h2

end GlobalTheory.SecondKind

namespace GlobalTheory.SecondKind

open GlobalTheory.CuspRep

theorem contDiffOn_of_prodExp : ∀ (E : Type) [Field E] [NumberField E] (d : ℕ) (f : GlobalTheory.CuspRep.Lie E d → ℂ)
    (S : Set (Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Cinf E))), Submodule.span ℝ S = ⊤ →
    (∀ (k : ℕ) (X : Fin k → Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Cinf E)), (∀ i, X i ∈ S) →
      ∀ y ∈ GlobalTheory.CuspRep.invSet E d, ContDiff ℝ ∞ fun t : Fin k → ℝ =>
        f (GlobalTheory.CuspRep.toL (Matrix.of y * (List.ofFn fun i => NormedSpace.exp (t i • X i)).prod))) →
    ContDiffOn ℝ ∞ f (GlobalTheory.CuspRep.invSet E d) := by
  intro E _ _ d f S hS hf x₀ hx₀
  refine ContDiffAt.contDiffWithinAt ?_

  obtain ⟨b, hbS, hbspan, hbli⟩ := exists_linearIndependent ℝ S
  haveI : Module.Finite ℝ (Matrix (Fin d) (Fin d) (Cinf E)) := inferInstance
  haveI : Finite b := hbli.finite
  letI : Fintype b := Fintype.ofFinite b
  set m := Fintype.card b
  let e := Fintype.equivFin b
  let X : Fin m → Matrix (Fin d) (Fin d) (Cinf E) := fun i => (e.symm i).1
  have hXS : ∀ i, X i ∈ S := fun i => hbS (e.symm i).2
  have hXli : LinearIndependent ℝ X := hbli.comp e.symm e.symm.injective
  have hXspan : Submodule.span ℝ (Set.range X) = ⊤ := by
    have : Set.range X = b := by
      ext x; constructor
      · rintro ⟨i, rfl⟩; exact (e.symm i).2
      · intro hx; exact ⟨e ⟨x, hx⟩, by simp [X]⟩
    rw [this, hbspan, hS]
  let B : Module.Basis (Fin m) ℝ (Matrix (Fin d) (Fin d) (Cinf E)) := Module.Basis.mk hXli hXspan.ge
  have hdim : Module.finrank ℝ (Fin m → ℝ) = Module.finrank ℝ (Lie E d) := by
    rw [Module.finrank_fin_fun]
    exact (Module.finrank_eq_card_basis B).trans (Fintype.card_fin m) |>.symm

  let Lin : (Fin m → ℝ) →ₗ[ℝ] Lie E d :=
    { toFun := fun t => toL (Matrix.of x₀ * ∑ i, t i • X i)
      map_add' := fun s t => by
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, mul_add]; rfl
      map_smul' := fun c t => by
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, Matrix.mul_smul]; rfl }
  have hLinj : Function.Injective Lin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro t ht
    have h1 : Matrix.of x₀ * ∑ i, t i • X i = Matrix.of x₀ * 0 := by
      rw [mul_zero]; exact ht
    have h2 := (show IsUnit (Matrix.of x₀) from hx₀).mul_left_cancel h1
    funext i
    exact Fintype.linearIndependent_iff.1 hXli t h2 i
  let L : (Fin m → ℝ) ≃L[ℝ] Lie E d :=
    (LinearMap.linearEquivOfInjective Lin hLinj hdim).toContinuousLinearEquiv
  set Θ := fun t : Fin m → ℝ =>
      toL (Matrix.of x₀ * (List.ofFn fun i => NormedSpace.exp (t i • X i)).prod) with hΘdef
  have hΘ : ContDiff ℝ ∞ Θ := contDiff_prodExp x₀ X
  have hΘ0 : Θ 0 = x₀ := by
    simp [Θ]
  have hD : HasFDerivAt Θ (L : (Fin m → ℝ) →L[ℝ] Lie E d) 0 := by
    have h := ((hΘ.differentiable (by simp)) 0).hasFDerivAt
    have hE : ((L : (Fin m → ℝ) →L[ℝ] Lie E d) : (Fin m → ℝ) →ₗ[ℝ] Lie E d) =
        ((fderiv ℝ Θ 0 : (Fin m → ℝ) →L[ℝ] Lie E d) : (Fin m → ℝ) →ₗ[ℝ] Lie E d) := by
      refine LinearMap.pi_ext fun i c => ?_
      change Lin (Pi.single i c) = fderiv ℝ Θ 0 (Pi.single i c)
      rw [hΘdef, fderiv_prodExp]
      simp only [Lin, LinearMap.coe_mk, AddHom.coe_mk]
      rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp)]
      simp only [Pi.single_eq_same, Matrix.mul_smul]
      rfl
    rw [ContinuousLinearMap.coe_injective hE]
    exact h
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  have hΨ := hΘ.contDiffAt.to_localInverse hD hn
  have hinv := (hΘ.contDiffAt.hasStrictFDerivAt' hD hn).eventually_right_inverse
  have hc : ContDiffAt ℝ ∞ (f ∘ Θ ∘ hΘ.contDiffAt.localInverse hD hn) (Θ 0) :=
    (hf m X hXS x₀ hx₀).contDiffAt.comp _ hΨ
  rw [hΘ0] at hc hinv
  refine hc.congr_of_eventuallyEq (hinv.mono fun x hx => ?_)
  simp only [Function.comp_apply]
  exact congrArg f hx.symm

end GlobalTheory.SecondKind
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnInvSetOfSmoothAlongProdExpStatement
open NumberField
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiffOn_invSet_of_smooth_along_prod_exp : ∀ (E : Type) [Field E] [NumberField E] (d : ℕ) (f : GlobalTheory.CuspRep.Lie E d → ℂ)
    (S : Set (Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Cinf E))), Submodule.span ℝ S = ⊤ →
    (∀ (k : ℕ) (X : Fin k → Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Cinf E)), (∀ i, X i ∈ S) →
      ∀ y ∈ GlobalTheory.CuspRep.invSet E d, ContDiff ℝ ∞ fun t : Fin k → ℝ =>
        f (GlobalTheory.CuspRep.toL (Matrix.of y * (List.ofFn fun i => NormedSpace.exp (t i • X i)).prod))) →
    ContDiffOn ℝ ∞ f (GlobalTheory.CuspRep.invSet E d) := by
  first | exact @GlobalTheory.SecondKind.contDiffOn_of_prodExp | exact GlobalTheory.SecondKind.contDiffOn_of_prodExp | (intros; apply GlobalTheory.SecondKind.contDiffOn_of_prodExp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodOverRingRestrictFamilyClass
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodOverRingRestrictFamilyClass
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.CatCoh GlobalTheory.Cris
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.AnPer

variable {I I₀ : Type} [Fintype I] [Fintype I₀] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {F₀ : Fam I₀ g Λ}
  (K : Charts F) (K₀ : Charts F₀) {R : Type} [CommRing R] (et : Hol F₀.V →+* R) (M : Ideal R) (θ : Hol F.V →+* R)
  (ka : K₀.K → K.K) (hka : ∀ {l k' k}, K₀.le l k' k → K.le l (ka k') (ka k))
  (ρ' : ∀ S : K₀.DObj et M, Hol (K.W (ka S.T.k)) →+* S.T.C)
  (h1 : ∀ S f, ρ' S (K.cst _ f) = algebraMap R S.T.C (θ f))
  (h3 : ∀ (S S' : K₀.DObj et M) (f : S ⟶ S'), Close S'.T.J ((ρ' S').comp (Charts.sh (hka (Charts.Hom.le f.1))))
    ((f.1.φ : S.T.C →+* S'.T.C).comp (ρ' S)))

def famObj (S : K₀.DObj et M) : K.Obj where
  k := ka S.T.k
  C := S.T.C
  alg := ((algebraMap R S.T.C).comp θ).toAlgebra
  J := S.T.J
  nil := S.T.nil
  ρ := ρ' S
  ρ_cst := h1 S

def famCoef : CoefMap θ K.Oc (K₀.OD et M) where
  G :=
    { obj := famObj K K₀ et M θ ka ρ' h1
      map {S S'} f :=
        { φ := { (f.1.φ : S.T.C →+* S'.T.C) with commutes' := fun x ↦ f.2 (θ x) }
          deg := f.1.deg
          le := hka (Charts.Hom.le f.1)
          mem := f.1.mem
          close := h3 S S' f }
      map_id _ := Charts.hom_ext (fun _ ↦ rfl) rfl
      map_comp _ _ := Charts.hom_ext (fun _ ↦ rfl) rfl }
  α S := RingHom.id S.T.C
  naturality _ _ := rfl
  smul S d c := (Algebra.smul_def (A := S.T.C) (θ d) c).symm

theorem famCoef_perCl (per : Λ →+ Hol F.V) :
    (famCoef K K₀ et M θ ka hka ρ' h1 h3).pull1 (K.perCl per) = K₀.perClD et M (θ.toAddMonoidHom.comp per) :=
  congrArg (H1.mk _) (Subtype.ext (funext fun _ ↦ funext fun _ ↦ funext fun _ ↦ rfl))

theorem coefD_pull1_of_family (res : ∀ k, Hol (K.W (ka k)) →+* Hol (K₀.W k))
    (h2 : ∀ S h, ρ' S h - S.T.ρ (res _ h) ∈ S.T.J)
    {B B₀ D : Type} [CommRing B] [CommRing B₀] [CommRing D] {X X₀ : Scheme.{0}} {s : X ⟶ Sp B} {s₀ : X₀ ⟶ Sp B₀}
    {σ : B →+* Hol F.V} {σ₀ : B₀ →+* Hol F₀.V} (r : Real K s σ) (r₀ : Real K₀ s₀ σ₀) {J : Ideal D}
    (dl : DividedPowers J) {s' : X₀ ⟶ Sp D} {π : D →+* B₀} {io : D →+* R} (H : IsOver et M s₀ σ₀ J s' π io)
    (j : B →+* D) (φ₀ : X₀ ⟶ X) (n : IsMor (dp0 B) s dl s' j φ₀) (h4 : ∀ b, θ (σ b) = io (j b))
    (h5 : ∀ k, spMap (res k) ≫ r.x (ka k) = r₀.x k ≫ φ₀) (c : FirstDeRham s) (per : Λ →+ Hol F.V)
    (hc : r.coef.pull1 c = K.perCl per) (h1 : ∀ S f, ρ' S (K.cst _ f) = algebraMap R S.T.C (θ f))
    (h3 : ∀ (S S' : K₀.DObj et M) (f : S ⟶ S'), Close S'.T.J ((ρ' S').comp (Charts.sh (hka (Charts.Hom.le f.1))))
      ((f.1.φ : S.T.C →+* S'.T.C).comp (ρ' S))) :
    (r₀.coefD dl H).pull1 (n.pull1 c) = K₀.perClD et M (θ.toAddMonoidHom.comp per) := by
  let t : (r.coef.comp (famCoef K K₀ et M θ ka hka ρ' h1 h3)).G ⟶ (n.coef.comp (r₀.coefD dl H)).G :=
    { app S :=
        { φ := { RingHom.id S.T.C with commutes' := fun b ↦ congrArg (algebraMap R S.T.C) (h4 b) }
          φ₀ := RingHom.id (S.T.C ⧸ S.T.J)
          comm := fun _ ↦ rfl
          dp := letI := S.T.ratAlg; isDPMorphism_of_rat (C := S.T.C) (C' := S.T.C) _ _ (RingHom.id S.T.C) fun _ h ↦ h
          pt := by
            have e : (Ideal.Quotient.mk S.T.J).comp (ρ' S) = ((Ideal.Quotient.mk S.T.J).comp S.T.ρ).comp (res _) :=
              RingHom.ext fun h ↦ Ideal.Quotient.eq.2 (h2 S h)
            change spMap (RingHom.id (S.T.C ⧸ S.T.J)) ≫ spMap ((Ideal.Quotient.mk S.T.J).comp (ρ' S)) ≫ r.x (ka S.T.k) =
              (spMap ((Ideal.Quotient.mk S.T.J).comp S.T.ρ) ≫ r₀.x S.T.k) ≫ φ₀
            rw [Cris.spMap_id, Category.id_comp, Category.assoc, ← h5, e, Cris.spMap_comp (res _), Category.assoc] }
      naturality _ _ _ := by
        apply Thick.Hom.ext'
        ext b
        rfl }
  refine (n.coef.pullCohomologyOne_comp (r₀.coefD dl H) c).symm.trans ?_
  refine (CoefMap.pullCohomologyOne_eq_of_natTrans _ _ t (fun _ _ ↦ rfl) c).symm.trans ?_
  rw [CoefMap.pullCohomologyOne_comp, hc, famCoef_perCl]

end GlobalTheory.AnPer


open GlobalTheory.AnPer in
theorem GlobalTheory.AnPer.period_restrict_family : ∀ {I I₀ : Type} [Fintype I] [Fintype I₀] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {F₀ : Fam I₀ g Λ} (K : Charts F) (K₀ : Charts F₀) {R : Type} [CommRing R] (et : Hol F₀.V →+* R) (M : Ideal R) (θ : Hol F.V →+* R) (ka : K₀.K → K.K) (hka : ∀ {l k' k}, K₀.le l k' k → K.le l (ka k') (ka k)) (res : ∀ k, Hol (K.W (ka k)) →+* Hol (K₀.W k)) (ρ' : ∀ S : K₀.DObj et M, Hol (K.W (ka S.T.k)) →+* S.T.C), (∀ S f, ρ' S (K.cst _ f) = algebraMap R S.T.C (θ f)) → (∀ S h, ρ' S h - S.T.ρ (res _ h) ∈ S.T.J) → (∀ (S S' : K₀.DObj et M) (f : S ⟶ S'), Close S'.T.J ((ρ' S').comp (Charts.sh (hka (Charts.Hom.le f.1)))) ((f.1.φ : S.T.C →+* S'.T.C).comp (ρ' S))) → ∀ {B B₀ D : Type} [CommRing B] [CommRing B₀] [CommRing D] {X X₀ : Scheme.{0}} {s : X ⟶ Sp B} {s₀ : X₀ ⟶ Sp B₀} {σ : B →+* Hol F.V} {σ₀ : B₀ →+* Hol F₀.V} (r : GlobalTheory.AnPer.Real K s σ) (r₀ : GlobalTheory.AnPer.Real K₀ s₀ σ₀) {J : Ideal D} (dl : DividedPowers J) {s' : X₀ ⟶ Sp D} {π : D →+* B₀} {io : D →+* R} (H : IsOver et M s₀ σ₀ J s' π io) (j : B →+* D) (φ₀ : X₀ ⟶ X) (n : IsMor (dp0 B) s dl s' j φ₀), (∀ b, θ (σ b) = io (j b)) → (∀ k, spMap (res k) ≫ r.x (ka k) = r₀.x k ≫ φ₀) → ∀ (c : FirstDeRham s) (per : Λ →+ Hol F.V), r.coef.pull1 c = K.perCl per → (r₀.coefD dl H).pull1 (n.pull1 c) = K₀.perClD et M (θ.toAddMonoidHom.comp per) :=
  fun K K₀ _ _ et M θ ka hka res ρ' h1 h2 h3 _ _ _ _ _ _ _ _ _ _ _ _ r r₀ _ dl _ _ _ H j φ₀ n h4 h5 c per hc ↦
    coefD_pull1_of_family K K₀ et M θ ka hka ρ' res h2 r r₀ dl H j φ₀ n h4 h5 c per hc h1 h3
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodOverRingRestrictFamilyClassStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_over_ring_restrict_family_class : ∀ {I I₀ : Type} [Fintype I] [Fintype I₀] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {F₀ : Fam I₀ g Λ} (K : Charts F) (K₀ : Charts F₀) {R : Type} [CommRing R] (et : Hol F₀.V →+* R) (M : Ideal R) (θ : Hol F.V →+* R) (ka : K₀.K → K.K) (hka : ∀ {l k' k}, K₀.le l k' k → K.le l (ka k') (ka k)) (res : ∀ k, Hol (K.W (ka k)) →+* Hol (K₀.W k)) (ρ' : ∀ S : K₀.DObj et M, Hol (K.W (ka S.T.k)) →+* S.T.C), (∀ S f, ρ' S (K.cst _ f) = algebraMap R S.T.C (θ f)) → (∀ S h, ρ' S h - S.T.ρ (res _ h) ∈ S.T.J) → (∀ (S S' : K₀.DObj et M) (f : S ⟶ S'), Close S'.T.J ((ρ' S').comp (Charts.sh (hka (Charts.Hom.le f.1)))) ((f.1.φ : S.T.C →+* S'.T.C).comp (ρ' S))) → ∀ {B B₀ D : Type} [CommRing B] [CommRing B₀] [CommRing D] {X X₀ : Scheme.{0}} {s : X ⟶ Sp B} {s₀ : X₀ ⟶ Sp B₀} {σ : B →+* Hol F.V} {σ₀ : B₀ →+* Hol F₀.V} (r : GlobalTheory.AnPer.Real K s σ) (r₀ : GlobalTheory.AnPer.Real K₀ s₀ σ₀) {J : Ideal D} (dl : DividedPowers J) {s' : X₀ ⟶ Sp D} {π : D →+* B₀} {io : D →+* R} (H : IsOver et M s₀ σ₀ J s' π io) (j : B →+* D) (φ₀ : X₀ ⟶ X) (n : IsMor (dp0 B) s dl s' j φ₀), (∀ b, θ (σ b) = io (j b)) → (∀ k, spMap (res k) ≫ r.x (ka k) = r₀.x k ≫ φ₀) → ∀ (c : FirstDeRham s) (per : Λ →+ Hol F.V), r.coef.pull1 c = K.perCl per → (r₀.coefD dl H).pull1 (n.pull1 c) = K₀.perClD et M (θ.toAddMonoidHom.comp per) := by
  first | exact @GlobalTheory.AnPer.period_restrict_family | exact GlobalTheory.AnPer.period_restrict_family | (intros; apply GlobalTheory.AnPer.period_restrict_family <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInjectiveKernelCoindIntertwiningMap
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInjectiveKernelCoindIntertwiningMap
open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism

namespace GlobalTheory.CoindKernel

variable {G : Type} [Group G] (P : Subgroup G) {V : Type} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ P V)


open Classical in
noncomputable def delta : V →ₗ[ℂ] Representation.coindV P.subtype σ where
  toFun v := ⟨fun x => if h : x ∈ P then σ ⟨x, h⟩ v else 0, by
    intro p g
    by_cases hg : g ∈ P
    · have h1 : P.subtype p * g ∈ P := P.mul_mem p.2 hg
      simp only [dif_pos hg, dif_pos h1]
      have : (⟨P.subtype p * g, h1⟩ : P) = p * ⟨g, hg⟩ := rfl
      rw [this, map_mul]; rfl
    · have h1 : P.subtype p * g ∉ P := fun h => hg ((P.mul_mem_cancel_left p.2).1 h)
      simp only [dif_neg hg, dif_neg h1, map_zero]⟩
  map_add' v w := by
    ext x
    by_cases hx : x ∈ P <;> simp [hx]
  map_smul' c v := by
    ext x
    by_cases hx : x ∈ P <;> simp [hx]

open Classical in
theorem delta_apply (v : V) (x : G) :
    (delta P σ v).1 x = if h : x ∈ P then σ ⟨x, h⟩ v else 0 := rfl

theorem coind_val (g : G) (f : Representation.coindV P.subtype σ) (x : G) :
    (Representation.coind P.subtype σ g f).1 x = f.1 (x * g) := rfl

theorem coind_delta (p : P) (v : V) :
    Representation.coind P.subtype σ (p : G) (delta P σ v) = delta P σ (σ p v) := by
  ext x
  rw [coind_val, delta_apply, delta_apply]
  by_cases hx : x ∈ P
  · have h1 : x * (p : G) ∈ P := P.mul_mem hx p.2
    rw [dif_pos hx, dif_pos h1]
    have : (⟨x * (p : G), h1⟩ : P) = ⟨x, hx⟩ * p := rfl
    rw [this, map_mul]; rfl
  · have h1 : x * (p : G) ∉ P := fun h => hx ((P.mul_mem_cancel_right p.2).1 h)
    rw [dif_neg hx, dif_neg h1]

open Classical in
theorem sum_delta [Fintype G] (f : Representation.coindV P.subtype σ) :
    ∑ g : G, Representation.coind P.subtype σ g⁻¹ (delta P σ (f.1 g)) =
      ((Finset.univ.filter (· ∈ P)).card : ℂ) • f := by
  ext x
  have h : ∀ g : G, (Representation.coind P.subtype σ g⁻¹ (delta P σ (f.1 g))).1 x
      = if x * g⁻¹ ∈ P then f.1 x else 0 := by
    intro g
    rw [coind_val, delta_apply]
    by_cases hx : x * g⁻¹ ∈ P
    · rw [dif_pos hx, if_pos hx]
      have := f.2 ⟨x * g⁻¹, hx⟩ g
      rw [← this]
      simp
    · rw [dif_neg hx, if_neg hx]
  rw [Submodule.coe_sum, Finset.sum_apply, Finset.sum_congr rfl fun g _ => h g]
  have e := Equiv.sum_comp ((Equiv.inv G).trans (Equiv.mulLeft x))
    (fun y : G => if y ∈ P then f.1 x else 0)
  simp only [Equiv.trans_apply, Equiv.inv_apply, Equiv.coe_mulLeft] at e
  rw [e, ← Finset.sum_filter, Finset.sum_const, Submodule.coe_smul, Pi.smul_apply,
    Nat.cast_smul_eq_nsmul]

variable (P' : Subgroup G) {V' : Type} [AddCommGroup V'] [Module ℂ V']
  (σ' : Representation ℂ P' V')

noncomputable def kernel :
    Representation.IntertwiningMap (Representation.coind P.subtype σ)
      (Representation.coind P'.subtype σ') →ₗ[ℂ] (G → V →ₗ[ℂ] V') where
  toFun Φ g := (LinearMap.proj g ∘ₗ (Representation.coindV P'.subtype σ').subtype) ∘ₗ
    Φ.toLinearMap ∘ₗ delta P σ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem kernel_apply (Φ : Representation.IntertwiningMap (Representation.coind P.subtype σ)
      (Representation.coind P'.subtype σ')) (g : G) (v : V) :
    kernel P σ P' σ' Φ g v = (Φ (delta P σ v)).1 g := rfl

theorem exists_kernel : ∀ (G : Type) [Group G] [Finite G] (P P' : Subgroup G) (V V' : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (σ : Representation ℂ P V) (σ' : Representation ℂ P' V'), ∃ K : Representation.IntertwiningMap (Representation.coind P.subtype σ) (Representation.coind P'.subtype σ') →ₗ[ℂ] (G → V →ₗ[ℂ] V'), Function.Injective K ∧ ∀ (Φ : Representation.IntertwiningMap (Representation.coind P.subtype σ) (Representation.coind P'.subtype σ')) (p' : P') (g : G) (p : P), K Φ ((p' : G) * g * (p : G)) = σ' p' ∘ₗ K Φ g ∘ₗ σ p := by
  intro G _ _ P P' V V' _ _ _ _ σ σ'
  classical
  haveI := Fintype.ofFinite G
  refine ⟨kernel P σ P' σ', ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro Φ hΦ
    have h0 : ∀ v, Φ (delta P σ v) = 0 := by
      intro v
      ext g
      have := kernel_apply P σ P' σ' Φ g v
      rw [hΦ] at this
      exact this.symm
    apply Representation.IntertwiningMap.ext
    ext1 f
    have h1 := congrArg Φ (sum_delta P σ f)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_smul, Finset.sum_eq_zero (fun g _ => by
      rw [Φ.isIntertwining, h0, map_zero])] at h1
    have hc : ((Finset.univ.filter (fun x : G => x ∈ P)).card : ℂ) ≠ 0 := by
      rw [Nat.cast_ne_zero, Finset.card_ne_zero]
      exact ⟨1, by simp [P.one_mem]⟩
    exact (smul_eq_zero.1 h1.symm).resolve_left hc
  · intro Φ p' g p
    ext v
    rw [LinearMap.comp_apply, LinearMap.comp_apply, kernel_apply, kernel_apply, ← coind_delta,
      Φ.isIntertwining, coind_val, mul_assoc]
    exact (Φ (delta P σ v)).2 p' (g * p)

end GlobalTheory.CoindKernel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInjectiveKernelCoindIntertwiningMapStatement
open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_injective_kernel_coind_intertwiningMap : ∀ (G : Type) [Group G] [Finite G] (P P' : Subgroup G) (V V' : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (σ : Representation ℂ P V) (σ' : Representation ℂ P' V'), ∃ K : Representation.IntertwiningMap (Representation.coind P.subtype σ) (Representation.coind P'.subtype σ') →ₗ[ℂ] (G → V →ₗ[ℂ] V'), Function.Injective K ∧ ∀ (Φ : Representation.IntertwiningMap (Representation.coind P.subtype σ) (Representation.coind P'.subtype σ')) (p' : P') (g : G) (p : P), K Φ ((p' : G) * g * (p : G)) = σ' p' ∘ₗ K Φ g ∘ₗ σ p := by
  first | exact @GlobalTheory.CoindKernel.exists_kernel | exact GlobalTheory.CoindKernel.exists_kernel | (intros; apply GlobalTheory.CoindKernel.exists_kernel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvariantTwistsOfClosedCover
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvariantTwistsOfClosedCover
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC.ClosedCover

theorem spMap_comp {A B D : Type} [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (g : B →+* D) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Functor.map_comp]

theorem spMap_id (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := by
  simp only [spMap]
  rw [show CommRingCat.ofHom (RingHom.id A) = 𝟙 (CommRingCat.of A) from rfl, Spec.map_id]
  exact sch.map_id _

theorem pull_spMap_bij {q : ℕ} {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B) (n i : ℤ) :
    Function.Bijective (pull (ZMod q) (spMap (e : A →+* B)) (tw q i) n) := by
  have h1 : ∀ x, pull (ZMod q) (spMap (e.symm : B →+* A)) (tw q i) n (pull (ZMod q) (spMap (e : A →+* B)) (tw q i) n x) = x := by
    intro x
    rw [← pull_comp, ← spMap_comp]
    have : (e.symm : B →+* A).comp (e : A →+* B) = RingHom.id A := by ext; simp
    rw [this, spMap_id, pull_id]
  have h2 : ∀ x, pull (ZMod q) (spMap (e : A →+* B)) (tw q i) n (pull (ZMod q) (spMap (e.symm : B →+* A)) (tw q i) n x) = x := by
    intro x
    rw [← pull_comp, ← spMap_comp]
    have : (e : A →+* B).comp (e.symm : B →+* A) = RingHom.id B := by ext; simp
    rw [this, spMap_id, pull_id]
  exact ⟨Function.LeftInverse.injective h1, Function.RightInverse.surjective h2⟩

theorem polyProd_bij (A B : Type) [CommRing A] [CommRing B] :
    Function.Bijective ((Polynomial.mapRingHom (RingHom.fst A B)).prod (Polynomial.mapRingHom (RingHom.snd A B))) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro p hp
    simp only [RingHom.prod_apply, Prod.mk_eq_zero, Polynomial.coe_mapRingHom] at hp
    ext n
    · simpa using congrArg (fun r => _root_.AddMonoidAlgebra.coeff (M := ℕ) r n) hp.1
    · simpa using congrArg (fun r => _root_.AddMonoidAlgebra.coeff (M := ℕ) r n) hp.2
  · rintro ⟨p, p'⟩
    let N := max p.natDegree p'.natDegree + 1
    refine ⟨∑ k ∈ Finset.range N, Polynomial.monomial k (p.coeff k, p'.coeff k), ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [RingHom.prod_apply, Polynomial.coe_mapRingHom, Polynomial.map_sum, Polynomial.map_monomial]
    refine Prod.ext ?_ ?_
    · exact (Polynomial.as_sum_range' p N (by omega)).symm
    · exact (Polynomial.as_sum_range' p' N (by omega)).symm

theorem prodL : ∀ (q : ℕ) [NeZero q] (A B : Type) [CommRing A] [CommRing B], HInv q A → HInv q B → HInv q (A × B) := by
  intro q _ A B _ _ hA hB i n
  let e : Polynomial (A × B) ≃+* Polynomial A × Polynomial B := RingEquiv.ofBijective _ (polyProd_bij A B)
  let g : A × B →+* Polynomial A × Polynomial B := RingHom.prodMap Polynomial.C Polynomial.C
  have hg : e.toRingHom.comp Polynomial.C = g := by
    ext x <;> simp [e, g]

  have hgb : Function.Bijective (pull (ZMod q) (spMap g) (tw q i) n) := by
    have hP := GlobalTheory.T.etaleCohomology_prod_ring_projections_bijective q A B n i
    have hD := GlobalTheory.T.etaleCohomology_prod_ring_projections_bijective q (Polynomial A) (Polynomial B) n i
    have hsq : ∀ x : Ht q (sp (A × B)) n i,
        (pull _ (spMap (RingHom.fst (Polynomial A) (Polynomial B))) _ _ (pull _ (spMap g) _ n x),
          pull _ (spMap (RingHom.snd (Polynomial A) (Polynomial B))) _ _ (pull _ (spMap g) _ n x)) =
        Prod.map (pull _ (spMap (Polynomial.C : A →+* Polynomial A)) (tw q i) n)
          (pull _ (spMap (Polynomial.C : B →+* Polynomial B)) (tw q i) n)
          (pull _ (spMap (RingHom.fst A B)) _ _ x, pull _ (spMap (RingHom.snd A B)) _ _ x) := by
      intro x
      simp only [Prod.map]
      rw [← pull_comp, ← pull_comp, ← pull_comp, ← pull_comp, ← spMap_comp, ← spMap_comp, ← spMap_comp, ← spMap_comp]
      rfl
    have hcomp : (fun x : Ht q (sp (Polynomial A × Polynomial B)) n i =>
          (pull _ (spMap (RingHom.fst (Polynomial A) (Polynomial B))) _ _ x,
           pull _ (spMap (RingHom.snd (Polynomial A) (Polynomial B))) _ _ x)) ∘ (pull _ (spMap g) _ n) =
        Prod.map (pull _ (spMap (Polynomial.C : A →+* Polynomial A)) (tw q i) n)
          (pull _ (spMap (Polynomial.C : B →+* Polynomial B)) (tw q i) n) ∘
          (fun x : Ht q (sp (A × B)) n i =>
            (pull _ (spMap (RingHom.fst A B)) _ _ x, pull _ (spMap (RingHom.snd A B)) _ _ x)) := by
      funext x; exact hsq x
    have hR : Function.Bijective (Prod.map (pull _ (spMap (Polynomial.C : A →+* Polynomial A)) (tw q i) n)
          (pull _ (spMap (Polynomial.C : B →+* Polynomial B)) (tw q i) n)) :=
      Function.Bijective.prodMap (hA i n) (hB i n)
    have := (hR.comp hP)
    rw [← hcomp] at this
    exact (Function.Bijective.of_comp_iff' hD _).mp this
  have heq : ⇑(pull (ZMod q) (spMap g) (tw q i) n) =
      ⇑(pull (ZMod q) (spMap e.toRingHom) (tw q i) n) ∘ ⇑(pull (ZMod q) (spMap (Polynomial.C : A × B →+* Polynomial (A × B))) (tw q i) n) := by
    funext x
    rw [Function.comp_apply, ← pull_comp, ← spMap_comp, hg]
  rw [heq] at hgb
  exact (Function.Bijective.of_comp_iff' (pull_spMap_bij e n i) _).mp hgb

end GlobalTheory.EtC.ClosedCover

namespace GlobalTheory.EtC.ClosedCover
open PiTensorProduct

noncomputable def consLin (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (k : ℕ) :
    B ⊗[A] PiTensorProduct A (fun _ : Fin (k + 1) => B) ≃ₗ[A] PiTensorProduct A (fun _ : Fin (k + 2) => B) :=
  (TensorProduct.congr (subsingletonEquiv (R := A) (s := fun _ : Fin 1 => B) (0 : Fin 1)).symm (LinearEquiv.refl A _)).trans <|
    (tmulEquiv A B).trans (reindex A (fun _ => B) (finSumFinEquiv.trans (finCongr (by omega))))

theorem consLin_tmul (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (k : ℕ) (b : B) (x : Fin (k + 1) → B) :
    consLin A B k (b ⊗ₜ PiTensorProduct.tprod A x) =
      PiTensorProduct.tprod A (fun i => Sum.elim (fun _ : Fin 1 => b) x ((finSumFinEquiv.trans (finCongr (by omega))).symm i)) := by
  simp [consLin, reindex_tprod]

theorem succL : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (k : ℕ), Nonempty (PiTensorProduct A (fun _ : Fin (k + 2) => B) ≃ₐ[A] B ⊗[A] PiTensorProduct A (fun _ : Fin (k + 1) => B)) := by
  intro A B _ _ _ k
  refine ⟨(AlgEquiv.ofLinearEquiv (consLin A B k) ?_ ?_).symm⟩
  · rw [Algebra.TensorProduct.one_def, PiTensorProduct.one_def, consLin_tmul, PiTensorProduct.one_def]
    congr 1
    funext i
    rcases (finSumFinEquiv.trans (finCongr (by omega))).symm i with j | j <;> rfl
  · refine (LinearMap.map_mul_iff _).mpr ?_
    ext b x b' x'
    simp only [LinearMap.compr₂_apply, LinearMap.mul_apply', LinearMap.compl₂_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, Algebra.TensorProduct.tmul_mul_tmul, tprod_mul_tprod, consLin_tmul, TensorProduct.AlgebraTensorModule.curry_apply,
      TensorProduct.curry_apply, LinearMap.compMultilinearMap_apply, LinearMap.restrictScalars_apply]
    congr 1
    funext i
    simp only [Pi.mul_apply]
    rcases (finSumFinEquiv.trans (finCongr (by omega))).symm i with j | j <;> rfl
end GlobalTheory.EtC.ClosedCover

namespace GlobalTheory.EtC.ClosedCover

theorem oneL : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B], Nonempty (PiTensorProduct A (fun _ : Fin 1 => B) ≃ₐ[A] B) := by
  intro A B _ _ _
  classical
  let f := PiTensorProduct.singleAlgHom (R := A) (A := fun _ : Fin 1 => B) 0
  let g := PiTensorProduct.subsingletonEquiv (R := A) (s := fun _ : Fin 1 => B) (0 : Fin 1)
  have hgf : ∀ a, g (f a) = a := by
    intro a
    simp [f, g, PiTensorProduct.subsingletonEquiv_apply_tprod]
  have hf : Function.Bijective f := by
    have : (f : B → _) = g.symm := by
      funext a
      apply g.injective
      rw [hgf, LinearEquiv.apply_symm_apply]
    rw [this]
    exact g.symm.bijective
  exact ⟨(AlgEquiv.ofBijective f hf).symm⟩
end GlobalTheory.EtC.ClosedCover

namespace GlobalTheory.EtC.ClosedCover

variable {A : Type} [CommRing A]

noncomputable def quotTensorQuot (L K : Ideal A) : (A ⧸ L) ⊗[A] (A ⧸ K) ≃ₐ[A] A ⧸ (L ⊔ K) :=
  ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot (A ⧸ L) K).restrictScalars A).symm.trans
    (DoubleQuot.quotQuotEquivQuotSupₐ A L K)

noncomputable def prodLeftAlg (X Y C : Type) [CommRing X] [CommRing Y] [CommRing C] [Algebra A X] [Algebra A Y]
    [Algebra A C] : (X × Y) ⊗[A] C ≃ₐ[A] (X ⊗[A] C) × (Y ⊗[A] C) :=
  (Algebra.TensorProduct.comm A (X × Y) C).trans <|
    (Algebra.TensorProduct.prodRight A A C X Y).trans <|
      AlgEquiv.prodCongr (Algebra.TensorProduct.comm A C X) (Algebra.TensorProduct.comm A C Y)

noncomputable def stepEquiv (L I J : Ideal A) (C : Type) [CommRing C] [Algebra A C] :
    (A ⧸ L) ⊗[A] (((A ⧸ I) × (A ⧸ J)) ⊗[A] C) ≃ₐ[A] ((A ⧸ (L ⊔ I)) ⊗[A] C) × ((A ⧸ (L ⊔ J)) ⊗[A] C) :=
  (Algebra.TensorProduct.assoc A A A (A ⧸ L) ((A ⧸ I) × (A ⧸ J)) C).symm.trans <|
    (Algebra.TensorProduct.congr ((Algebra.TensorProduct.prodRight A A (A ⧸ L) (A ⧸ I) (A ⧸ J)).trans
      (AlgEquiv.prodCongr (quotTensorQuot L I) (quotTensorQuot L J))) AlgEquiv.refl).trans <|
    prodLeftAlg _ _ C

end GlobalTheory.EtC.ClosedCover

namespace GlobalTheory.EtC.ClosedCover

variable {A : Type} [CommRing A]

theorem hinv_of_algEquiv {q : ℕ} [NeZero q] {X Y : Type} [CommRing X] [CommRing Y] [Algebra A X] [Algebra A Y]
    (e : X ≃ₐ[A] Y) (h : HInv q X) : HInv q Y :=
  GlobalTheory.T.etaleHomotopyInvariantTwists_of_ringEquiv q X Y e.toRingEquiv h

def Good (I J L : Ideal A) : Prop := L = I ∨ L = J ∨ L = I ⊔ J

theorem good_sup_left {I J L : Ideal A} (h : Good I J L) : Good I J (L ⊔ I) := by
  rcases h with rfl | rfl | rfl
  · left; simp
  · right; right; exact sup_comm _ _
  · right; right; rw [sup_assoc, sup_comm J I, ← sup_assoc, sup_idem]

theorem good_sup_right {I J L : Ideal A} (h : Good I J L) : Good I J (L ⊔ J) := by
  rcases h with rfl | rfl | rfl
  · right; right; rfl
  · right; left; simp
  · right; right; rw [sup_assoc, sup_idem]

theorem main_step (q : ℕ) [NeZero q] (I J : Ideal A) (C : Type) [CommRing C] [Algebra A C]
    (hC : ∀ L, Good I J L → HInv q ((A ⧸ L) ⊗[A] C)) :
    ∀ L, Good I J L → HInv q ((A ⧸ L) ⊗[A] (((A ⧸ I) × (A ⧸ J)) ⊗[A] C)) := by
  intro L hL
  exact hinv_of_algEquiv (stepEquiv L I J C).symm
    (prodL q _ _ (hC _ (good_sup_left hL)) (hC _ (good_sup_right hL)))

theorem main_fin (q : ℕ) [NeZero q] (I J : Ideal A) (C : Type) [CommRing C] [Algebra A C]
    (hC : ∀ L, Good I J L → HInv q ((A ⧸ L) ⊗[A] C)) :
    HInv q (((A ⧸ I) × (A ⧸ J)) ⊗[A] C) :=
  hinv_of_algEquiv (prodLeftAlg _ _ C).symm (prodL q _ _ (hC I (Or.inl rfl)) (hC J (Or.inr (Or.inl rfl))))

theorem good_congr (q : ℕ) [NeZero q] (I J : Ideal A) {C D : Type} [CommRing C] [Algebra A C] [CommRing D] [Algebra A D]
    (e : C ≃ₐ[A] D) (hC : ∀ L, Good I J L → HInv q ((A ⧸ L) ⊗[A] C)) :
    ∀ L, Good I J L → HInv q ((A ⧸ L) ⊗[A] D) := fun L hL =>
  hinv_of_algEquiv (Algebra.TensorProduct.congr (AlgEquiv.refl : (A ⧸ L) ≃ₐ[A] (A ⧸ L)) e) (hC L hL)

theorem tensorPow (q : ℕ) [NeZero q] (I J : Ideal A)
    (hI : HInv q (A ⧸ I)) (hJ : HInv q (A ⧸ J)) (hIJ : HInv q (A ⧸ (I ⊔ J))) (k : ℕ) :
    (∀ L, Good I J L → HInv q ((A ⧸ L) ⊗[A] PiTensorProduct A (fun _ : Fin (k + 1) => (A ⧸ I) × (A ⧸ J)))) ∧
    HInv q (PiTensorProduct A (fun _ : Fin (k + 1) => (A ⧸ I) × (A ⧸ J))) := by
  have h0 : ∀ L, Good I J L → HInv q ((A ⧸ L) ⊗[A] A) := by
    intro L hL
    refine hinv_of_algEquiv (Algebra.TensorProduct.rid A A (A ⧸ L)).symm ?_
    rcases hL with rfl | rfl | rfl
    exacts [hI, hJ, hIJ]
  induction k with
  | zero =>
    obtain ⟨e⟩ := oneL A ((A ⧸ I) × (A ⧸ J))
    let e' := e.trans (Algebra.TensorProduct.rid A A ((A ⧸ I) × (A ⧸ J))).symm
    exact ⟨good_congr q I J e'.symm (main_step q I J A h0),
      hinv_of_algEquiv e'.symm (main_fin q I J A h0)⟩
  | succ k ih =>
    obtain ⟨e⟩ := succL A ((A ⧸ I) × (A ⧸ J)) k
    exact ⟨good_congr q I J e.symm (main_step q I J _ ih.1),
      hinv_of_algEquiv e.symm (main_fin q I J _ ih.1)⟩

theorem closedCover : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] (I J : Ideal A), I ⊓ J ≤ nilradical A →
    IsUnit (q : A) → HInv q (A ⧸ I) → HInv q (A ⧸ J) → HInv q (A ⧸ (I ⊔ J)) → HInv q A := by
  intro q _ A _ I J hn hq hI hJ hIJ
  refine GlobalTheory.T.etaleHomotopyInvariance_cechDescent_integral q A ((A ⧸ I) × (A ⧸ J)) inferInstance ?_ hq (fun k => (tensorPow q I J hI hJ hIJ k).2)
  intro x hx
  apply hn
  rw [RingHom.mem_ker] at hx
  have h1 := congrArg Prod.fst hx
  have h2 := congrArg Prod.snd hx
  simp only [Prod.fst_zero, Prod.snd_zero] at h1 h2
  exact ⟨Ideal.Quotient.eq_zero_iff_mem.mp h1, Ideal.Quotient.eq_zero_iff_mem.mp h2⟩

end GlobalTheory.EtC.ClosedCover

namespace GlobalTheory.EtC.ClosedCover

end GlobalTheory.EtC.ClosedCover
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvariantTwistsOfClosedCoverStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleHomotopyInvariantTwists_of_closedCover : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] (I J : Ideal A), I ⊓ J ≤ nilradical A → IsUnit (q : A) → HInv q (A ⧸ I) → HInv q (A ⧸ J) → HInv q (A ⧸ (I ⊔ J)) → HInv q A := by
  first | (exact @GlobalTheory.EtC.ClosedCover.closedCover) | (exact GlobalTheory.EtC.ClosedCover.closedCover) | (intros; apply GlobalTheory.EtC.ClosedCover.closedCover  <;> assumption)
end
end
