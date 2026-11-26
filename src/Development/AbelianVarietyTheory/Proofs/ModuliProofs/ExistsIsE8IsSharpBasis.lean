module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasisBaseChange
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsMonHomIffOfIsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsE8IsSharpBasis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM

def twistSnd {h : ℕ} (A : Matrix (Fin 8) (Fin 8) ℤ) :
    (Fin 8 → (Fin h ⊕ Fin h → ℤ)) →ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ)) where
  toFun y := fun u => Sum.elim (fun a => y u (.inl a)) (fun a => A.mulVec (fun w => y w (.inr a)) u)
  map_add' y y' := by
    funext u c
    rcases c with a | a
    · simp
    · simp [Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib]
  map_smul' r y := by
    funext u c
    rcases c with a | a
    · simp
    · simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_left_comm]

theorem twistSnd_twistSnd {h : ℕ} (A B : Matrix (Fin 8) (Fin 8) ℤ) (hAB : A * B = 1)
    (y : Fin 8 → (Fin h ⊕ Fin h → ℤ)) : twistSnd A (twistSnd B y) = y := by
  funext u c
  rcases c with a | a
  · rfl
  · change A.mulVec (B.mulVec (fun w => y w (.inr a))) u = _
    rw [Matrix.mulVec_mulVec, hAB, Matrix.one_mulVec]

theorem sum_omegaStd_twistSnd {h : ℕ} (A B : Matrix (Fin 8) (Fin 8) ℤ) (hA : A.transpose = A)
    (hAB : A * B = 1) (y y' : Fin 8 → (Fin h ⊕ Fin h → ℤ)) :
    ∑ u, ∑ v, A u v * omegaStd (twistSnd B y u) (twistSnd B y' v) = ∑ u, omegaStd (y u) (y' u) := by
  have key : ∀ (z : Fin 8 → ℤ) (u : Fin 8), ∑ v, A u v * B.mulVec z v = z u := by
    intro z u
    change A.mulVec (B.mulVec z) u = _
    rw [Matrix.mulVec_mulVec, hAB, Matrix.one_mulVec]
  have hs : ∀ u v, A u v = A v u := fun u v => by
    conv_lhs => rw [← hA]
    rfl
  have h1 : ∑ u, ∑ v, A u v * ∑ a, y u (.inl a) * B.mulVec (fun w => y' w (.inr a)) v
      = ∑ u, ∑ a, y u (.inl a) * y' u (.inr a) := by
    refine Finset.sum_congr rfl fun u _ => ?_
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← key (fun w => y' w (.inr a)) u, Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by ring
  have h2 : ∑ u, ∑ v, A u v * ∑ a, B.mulVec (fun w => y w (.inr a)) u * y' v (.inl a)
      = ∑ u, ∑ a, y u (.inr a) * y' u (.inl a) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← key (fun w => y w (.inr a)) v, Finset.sum_mul]
    exact Finset.sum_congr rfl fun u _ => by rw [hs u v]; ring
  simp only [omegaStd, Finset.sum_sub_distrib, mul_sub]
  rw [← h1, ← h2]
  rfl

def sharpIndex (h : ℕ) : Fin 8 × (Fin h ⊕ Fin h) ≃ Fin (2 * (8 * h)) :=
  (Equiv.prodSumDistrib _ _ _).trans <|
    (Equiv.sumCongr finProdFinEquiv finProdFinEquiv).trans <|
      finSumFinEquiv.trans (finCongr (two_mul _).symm)

theorem sharpIndex_inl (h : ℕ) (u : Fin 8) (a : Fin h) :
    (sharpIndex h (u, .inl a) : ℕ) = (finProdFinEquiv (u, a) : ℕ) := by
  simp [sharpIndex]

theorem sharpIndex_inr (h : ℕ) (u : Fin 8) (a : Fin h) :
    (sharpIndex h (u, .inr a) : ℕ) = (finProdFinEquiv (u, a) : ℕ) + 8 * h := by
  simp [sharpIndex]

theorem sum_omegaStd_single (h : ℕ) (i j : Fin (2 * (8 * h))) :
    ∑ u, omegaStd (fun c => (Pi.single i 1 : Fin (2 * (8 * h)) → ℤ) (sharpIndex h (u, c)))
      (fun c => (Pi.single j 1 : Fin (2 * (8 * h)) → ℤ) (sharpIndex h (u, c))) = Out.stdSymp (8 * h) i j := by
  obtain ⟨⟨u, c⟩, rfl⟩ := (sharpIndex h).surjective i
  obtain ⟨⟨v, d⟩, rfl⟩ := (sharpIndex h).surjective j
  have hinj : ∀ (u v : Fin 8) (a b : Fin h),
      ((finProdFinEquiv (u, a) : ℕ) = (finProdFinEquiv (v, b) : ℕ)) ↔ (u = v ∧ a = b) := by
    intro u v a b
    rw [Fin.val_inj, Equiv.apply_eq_iff_eq, Prod.mk.injEq]
  rcases c with a | a <;> rcases d with b | b
  all_goals
    have h1 := (finProdFinEquiv (u, a)).isLt
    have h2 := (finProdFinEquiv (v, b)).isLt
    have h3 := hinj u v a b
    simp only [omegaStd, Out.stdSymp, Pi.single_apply, Equiv.apply_eq_iff_eq, Prod.mk.injEq,
      sharpIndex_inl, sharpIndex_inr, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, and_false,
      if_false, mul_zero, zero_mul, sub_zero, zero_sub, Finset.sum_const_zero, sub_self]
    generalize (finProdFinEquiv (u, a) : ℕ) = m at *
    generalize (finProdFinEquiv (v, b) : ℕ) = n at *
  · rw [if_neg (by omega), if_neg (by omega)]
  · by_cases huv : u = v ∧ a = b
    · obtain ⟨rfl, rfl⟩ := huv
      have : m = n := h3.2 ⟨rfl, rfl⟩
      rw [if_pos (by omega)]
      simp [ite_and]
    · have : m ≠ n := fun e => huv (h3.1 e)
      rw [if_neg (by omega), if_neg (by omega)]
      refine Finset.sum_eq_zero fun w _ => Finset.sum_eq_zero fun c _ => ?_
      split_ifs with p q
      · exact absurd ⟨p.1.symm.trans q.1, p.2.symm.trans q.2⟩ huv
      all_goals simp
  · by_cases huv : u = v ∧ a = b
    · obtain ⟨rfl, rfl⟩ := huv
      have : m = n := h3.2 ⟨rfl, rfl⟩
      rw [if_neg (by omega), if_pos (by omega)]
      simp [ite_and]
    · have : m ≠ n := fun e => huv (h3.1 e)
      rw [if_neg (by omega), if_neg (by omega)]
      refine Finset.sum_eq_zero fun w _ => Finset.sum_eq_zero fun c _ => ?_
      split_ifs with p q
      · exact absurd ⟨p.1.symm.trans q.1, p.2.symm.trans q.2⟩ huv
      all_goals simp
  · rw [if_neg (by omega), if_neg (by omega)]

def sharpReindex (h : ℕ) : (Fin (2 * (8 * h)) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ)) where
  toFun x := fun u c => x (sharpIndex h (u, c))
  invFun y := fun i => y ((sharpIndex h).symm i).1 ((sharpIndex h).symm i).2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv x := by funext i; simp
  right_inv y := by funext u c; simp

theorem exists_isE8_isSharpBasis : ∃ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W ∧ ∀ h : ℕ, ∃ bas : (Fin (2 * (8 * h)) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ)), IsSharpBasis W bas := by
  refine ⟨GlobalTheory.W8, ?_, fun h => ?_⟩
  · unfold IsE8
    rw [GlobalTheory.w8_add_transpose_eq_e8]
    exact ⟨GlobalTheory.e8_posDef, GlobalTheory.e8_det_eq_one⟩
  · let e : (Fin 8 → (Fin h ⊕ Fin h → ℤ)) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ)) :=
      { twistSnd GlobalTheory.E8inv with
        invFun := twistSnd GlobalTheory.E8
        left_inv := twistSnd_twistSnd _ _ GlobalTheory.e8_mul_e8inv
        right_inv := twistSnd_twistSnd _ _ GlobalTheory.e8inv_mul_e8 }
    refine ⟨(sharpReindex h).trans e, fun i j => ?_⟩
    rw [GlobalTheory.w8_add_transpose_eq_e8, ← sum_omegaStd_single h i j]
    exact sum_omegaStd_twistSnd _ _ GlobalTheory.e8_transpose GlobalTheory.e8_mul_e8inv _ _

end GlobalTheory.ZM
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaPointsVanishingIdealRadicalHomogeneous
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaPointsVanishingIdealRadicalHomogeneous
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.ThIdeal

theorem hasTh_unit_mul {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)}
    {S : Scheme.{0}} {s : S ⟶ Sp o} {t : TObj g (N' ^ 2) J b s} {R : Type} [CommRing R]
    {x : Sp R ⟶ S} {v : Ix g (N' ^ 2) → R} (h : t.HasTh x v) (c : R) (hc : IsUnit c) :
    t.HasTh x (fun a => c * v a) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, fun p => ?_⟩
  obtain ⟨V, hV, th, s1, α, τ, U, s2, w, u, k1, k2, k3, k4, k5, k6, k7, k8⟩ := h3 p
  have hu : IsUnit (V.ι.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c)) :=
    (hc.map _).map _
  obtain ⟨u', hu'⟩ : ∃ u' : Γ((Out.overRes (T := Over.mk x) V).left, ⊤)ˣ,
      u'.val = V.ι.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) := hu
  refine ⟨V, hV, th, s1, α, τ, U, s2, w, u' * u, k1, k2, k3, k4, k5, k6, k7, fun i => ?_⟩
  have e := k8 i
  have e1 : V.ι.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (c * v i)) =
      V.ι.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) *
        V.ι.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (v i)) := by
    rw [map_mul]
    exact map_mul _ _ _
  refine e1.trans ?_
  rw [Units.val_mul, _root_.mul_assoc, hu']
  exact congrArg (fun y => V.ι.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) * y) e

theorem coeff_scale {R R' σ : Type} [CommRing R] [CommRing R'] (β : R →+* R') (w : σ → R')
    (F : MvPolynomial σ R) (e : ℕ) :
    (MvPolynomial.eval₂Hom ((Polynomial.C : R' →+* Polynomial R').comp β)
      (fun i => Polynomial.X * Polynomial.C (w i)) F).coeff e =
      MvPolynomial.eval₂Hom β w (MvPolynomial.homogeneousComponent e F) := by
  induction F using MvPolynomial.induction_on' with
  | monomial d c =>
    have hm : MvPolynomial.monomial d c ∈ MvPolynomial.homogeneousSubmodule σ R d.degree :=
      MvPolynomial.isHomogeneous_monomial c rfl
    rw [MvPolynomial.homogeneousComponent_of_mem hm]
    have : MvPolynomial.eval₂Hom ((Polynomial.C : R' →+* Polynomial R').comp β)
      (fun i => Polynomial.X * Polynomial.C (w i)) (MvPolynomial.monomial d c) =
        Polynomial.C (MvPolynomial.eval₂Hom β w (MvPolynomial.monomial d c)) * Polynomial.X ^ d.degree := by
      simp only [MvPolynomial.eval₂Hom_monomial, Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
        Finset.prod_pow_eq_pow_sum, map_mul, map_prod, map_pow, RingHom.comp_apply, Finsupp.degree_apply]
      ring
    rw [this, Polynomial.coeff_C_mul_X_pow]
    split_ifs <;> simp
  | add p q hp hq => simp only [map_add (f := _), Polynomial.coeff_add, hp, hq]

theorem component_eq_zero {R σ : Type} [CommRing R] (β : R →+* ℂ) (w : σ → ℂ)
    (F : MvPolynomial σ R) (e : ℕ)
    (h : ∀ c : ℂ, c ≠ 0 → MvPolynomial.eval₂Hom β (fun i => c * w i) F = 0) :
    MvPolynomial.eval₂Hom β w (MvPolynomial.homogeneousComponent e F) = 0 := by
  rw [← coeff_scale]
  have : MvPolynomial.eval₂Hom ((Polynomial.C : ℂ →+* Polynomial ℂ).comp β)
      (fun i => Polynomial.X * Polynomial.C (w i)) F = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono (s := {0}ᶜ) (fun c hc => ?_) (Set.finite_singleton (0 : ℂ)).infinite_compl
    have h1 := MvPolynomial.map_eval₂Hom ((Polynomial.C : ℂ →+* Polynomial ℂ).comp β)
      (fun i => Polynomial.X * Polynomial.C (w i)) (Polynomial.evalRingHom c) F
    rw [Set.mem_ofPred_eq, Polynomial.IsRoot.def, ← Polynomial.coe_evalRingHom, h1, ← h c hc]
    congr 2
    · ext r; simp
    · ext i; simp [_root_.mul_comm c]
  rw [this, Polynomial.coeff_zero]

theorem mem_thIdeal {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)} (em : o →+* ℂ)
    (C : TObj g (N' ^ 2) J b (spMap em) → Prop) (F : MvPolynomial (Ix g (N' ^ 2)) o) :
    F ∈ thIdeal em C ↔ ∀ t v, C t → t.HasTh (𝟙 _) v → MvPolynomial.eval₂Hom em v F = 0 := by
  simp only [thIdeal, Ideal.mem_iInf, RingHom.mem_ker, and_imp]

theorem thIdeal_radical_homogeneous_torsionFree :
    ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (C : TObj g (N' ^ 2) J b (spMap em) → Prop), Function.Injective em → (thIdeal em C).IsRadical ∧ (∀ F ∈ thIdeal em C, ∀ e, MvPolynomial.homogeneousComponent e F ∈ thIdeal em C) ∧ ∀ (c : o) F, c ≠ 0 → MvPolynomial.C c * F ∈ thIdeal em C → F ∈ thIdeal em C := by
  intro o _ g N' J b em C hem
  refine ⟨fun F hF => ?_, fun F hF e => ?_, fun c F hc hF => ?_⟩
  · obtain ⟨n, hn⟩ := hF
    rw [mem_thIdeal] at hn ⊢
    intro t v ht hv
    have := hn t v ht hv
    rw [map_pow] at this
    exact pow_eq_zero_iff'.mp this |>.1
  · rw [mem_thIdeal] at hF ⊢
    intro t v ht hv
    exact component_eq_zero em v F e fun c hc => hF t _ ht (hasTh_unit_mul hv c hc.isUnit)
  · rw [mem_thIdeal] at hF ⊢
    intro t v ht hv
    have := hF t v ht hv
    rw [map_mul, MvPolynomial.eval₂Hom_C] at this
    exact (mul_eq_zero.mp this).resolve_left ((map_ne_zero_iff em hem).mpr hc)

end GlobalTheory.ZM.ThIdeal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaPointsVanishingIdealRadicalHomogeneousStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
theorem _root_.GlobalTheory.T.thetaPointsVanishingIdeal_radical_homogeneous : ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (C : TObj g (N' ^ 2) J b (spMap em) → Prop), Function.Injective em → (thIdeal em C).IsRadical ∧ (∀ F ∈ thIdeal em C, ∀ e, MvPolynomial.homogeneousComponent e F ∈ thIdeal em C) ∧ ∀ (c : o) F, c ≠ 0 → MvPolynomial.C c * F ∈ thIdeal em C → F ∈ thIdeal em C := by
  first | exact @GlobalTheory.ZM.ThIdeal.thIdeal_radical_homogeneous_torsionFree | exact GlobalTheory.ZM.ThIdeal.thIdeal_radical_homogeneous_torsionFree | (intros; apply GlobalTheory.ZM.ThIdeal.thIdeal_radical_homogeneous_torsionFree <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PelObjectClassPrimAndIsoClosed
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PelObjectClassPrimAndIsoClosed
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.PelPrim

def chartPullSection {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) (ψ : X ⟶ Y) (e : ψ ≫ φ = 𝟙 X) :
    ChartPull L (L.pull φ) ψ :=
  have le : ∀ i, L.U i ≤ ψ ⁻¹ᵁ (L.pull φ).U (fun _ => i) := fun i y hy => mem_pull.2 (by
    have : (ψ ≫ φ) y ∈ L.U i := by rw [e]; exact hy
    exact this)
  { idx := fun i _ => i
    le := le
    g := fun y i j hi hj =>
      ((gm_pull_g L φ ψ y (fun _ => i) (fun _ => j) (le i hi) (le j hj)).trans (by rw [e])).symm }

theorem lbIso_inv {X Y : Scheme.{0}} {L : LB X} {M : LB Y} {φ : Y ⟶ X} {ψ : X ⟶ Y} (e : ψ ≫ φ = 𝟙 X)
    (h : LBIso M (L.pull φ)) : LBIso L (M.pull ψ) :=
  (LBIso.chartPull (chartPullPull M ψ ψ rfl) (chartPullSection L φ ψ e) h).symm

theorem lbIso_comp {X X' X'' : Scheme.{0}} {L : LB X} {L' : LB X'} {L'' : LB X''} {F : X' ⟶ X} {F' : X'' ⟶ X'}
    (hL : L.IsLB) (hL' : L'.IsLB) (hL'' : L''.IsLB) (h : LBIso L' (L.pull F)) (h' : LBIso L'' (L'.pull F')) :
    LBIso L'' (L.pull (F' ≫ F)) := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨w', hw'⟩ := h'
  obtain ⟨w'', T⟩ := exists_comp hL' w w' ((isGen_iff w).1 hw) ((isGen_iff w').1 hw') hL hL''
  exact ⟨w'', (isGen_iff w'').2 (T.pgen_comp hL' ((isGen_iff w).1 hw) ((isGen_iff w').1 hw'))⟩

theorem lbIso_linComb {X Y : Scheme.{0}} {L M : LB X} (h : LBIso L M) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (ε : K → ℤ) : LBIso (LB.LinComb L φ ε) (LB.LinComb M φ ε) := by
  obtain ⟨w, hw⟩ := h
  exact ⟨_, DVR.linCombIso_isGen w hw φ ε⟩

section Cube
variable {S : Scheme.{0}} {G A : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A]

theorem psum_comp (ψ : A ⟶ G) [IsMonHom ψ] {T T' : Over S} {n : ℕ} (x' : Fin n → (T' ⟶ A)) (x : Fin n → (T ⟶ G))
    (U : T' ⟶ T) (hx : ∀ i, x' i ≫ ψ = U ≫ x i) (I : Finset (Fin n)) :
    (psum A x' I).left ≫ ψ.left = U.left ≫ (psum G x I).left := by
  have e : psum A x' I ≫ ψ = U ≫ psum G x I :=
    (psum_hom (MonoidHom.mk' (· ≫ ψ) fun a b => MonObj.mul_comp a b ψ) x' I).trans
      ((congrArg (fun z => psum G z I) (funext hx)).trans (psum_hom (preHom U) x I).symm)
  exact congrArg (fun z => z.left) e

def chartPullCube (ψ : A ⟶ G) [IsMonHom ψ] (M : LB G.left) {T T' : Over S} {n : ℕ} (x' : Fin n → (T' ⟶ A))
    (x : Fin n → (T ⟶ G)) (U : T' ⟶ T) (hx : ∀ i, x' i ≫ ψ = U ≫ x i) :
    ChartPull (cubeLB A x' (M.pull ψ.left)) (cubeLB G x M) U.left :=
  chartPullLinComb M _ _ _ _ U.left fun I => psum_comp ψ x' x U hx I.down

omit [IsCommMonObj A] in
theorem cube_isLB {L : LB A.left} (hL : L.IsLB) {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ A)) : (cubeLB A x L).IsLB :=
  DVR.linComb_isLB L hL _ _

omit [IsCommMonObj A] in
theorem cube_congr {L M : LB A.left} (h : LBIso L M) {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ A)) :
    LBIso (cubeLB A x L) (cubeLB A x M) := lbIso_linComb h _ _

theorem adj_pull (ψ : A ⟶ G) [IsMonHom ψ] {L : LB A.left} {M : LB G.left} (hL : L.IsLB) (hM : M.IsLB)
    (h : LBIso L (M.pull ψ.left)) {u v : A ⟶ A} {u₀ v₀ : G ⟶ G} (hu : u ≫ ψ = ψ ≫ u₀) (hv : v ≫ ψ = ψ ≫ v₀)
    (H : LBIso (cubeLB G ![fst G G ≫ u₀, snd G G] M) (cubeLB G ![fst G G, snd G G ≫ v₀] M)) :
    LBIso (cubeLB A ![fst A A ≫ u, snd A A] L) (cubeLB A ![fst A A, snd A A ≫ v] L) := by
  have hP : (M.pull ψ.left).IsLB := by
    refine { cover := top_le_iff.1 ?_, g_self := ?_, cocycle := ?_ }
    · intro y _
      obtain ⟨i, hi⟩ := exists_chart hM (ψ.left y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, mem_pull.2 hi⟩
    · intro J
      refine unit_ext fun y hy => ?_
      rw [gm_res (𝟙 _) y _ hy, map_one, gm_pull_g M ψ.left (𝟙 _) y J J hy hy]
      exact gm_self hM _ y (mem_pull.1 hy)
    · intro I J K
      refine unit_ext fun y hy => ?_
      rw [map_mul, gm_res (𝟙 _) y _ hy, gm_res (𝟙 _) y _ hy, gm_res (𝟙 _) y _ hy,
        gm_pull_g M ψ.left (𝟙 _) y I J hy.1.1 hy.1.2,
        gm_pull_g M ψ.left (𝟙 _) y J K hy.1.2 hy.2,
        gm_pull_g M ψ.left (𝟙 _) y I K hy.1.1 hy.2]
      exact gm_cocycle hM _ y (mem_pull.1 hy.1.1) (mem_pull.1 hy.1.2) (mem_pull.1 hy.2)
  refine ((cube_congr h _).trans (cube_isLB hL _) (cube_isLB hP _) (cube_isLB hP _) ?_).trans
    (cube_isLB hL _) (cube_isLB hP _) (cube_isLB hL _) (cube_congr h _).symm
  refine LBIso.chartPull (chartPullCube ψ M _ _ (ψ ⊗ₘ ψ) fun i => ?_) (chartPullCube ψ M _ _ (ψ ⊗ₘ ψ) fun i => ?_) H
  · fin_cases i <;> simp [hu]
  · fin_cases i <;> simp [hv]

theorem prim_pull (ψ : A ⟶ G) [IsMonHom ψ] {L : LB A.left} {M : LB G.left} (hL : L.IsLB) (hM : M.IsLB)
    (h : LBIso L (M.pull ψ.left)) {u : A ⟶ A} {u₀ : G ⟶ G} (hu : u ≫ ψ = ψ ≫ u₀)
    (H : LBIso M (cubeLB G ![𝟙 G, u₀] M)) : LBIso L (cubeLB A ![𝟙 A, u] L) := by
  have hP : (M.pull ψ.left).IsLB := by
    refine { cover := top_le_iff.1 ?_, g_self := ?_, cocycle := ?_ }
    · intro y _
      obtain ⟨i, hi⟩ := exists_chart hM (ψ.left y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, mem_pull.2 hi⟩
    · intro J
      refine unit_ext fun y hy => ?_
      rw [gm_res (𝟙 _) y _ hy, map_one, gm_pull_g M ψ.left (𝟙 _) y J J hy hy]
      exact gm_self hM _ y (mem_pull.1 hy)
    · intro I J K
      refine unit_ext fun y hy => ?_
      rw [map_mul, gm_res (𝟙 _) y _ hy, gm_res (𝟙 _) y _ hy, gm_res (𝟙 _) y _ hy,
        gm_pull_g M ψ.left (𝟙 _) y I J hy.1.1 hy.1.2,
        gm_pull_g M ψ.left (𝟙 _) y J K hy.1.2 hy.2,
        gm_pull_g M ψ.left (𝟙 _) y I K hy.1.1 hy.2]
      exact gm_cocycle hM _ y (mem_pull.1 hy.1.1) (mem_pull.1 hy.1.2) (mem_pull.1 hy.2)
  refine (h.trans hL hP (cube_isLB hP _) ?_).trans hL (cube_isLB hP _) (cube_isLB hL _) (cube_congr h _).symm
  refine LBIso.chartPull (chartPullPull M _ ψ.left rfl) (chartPullCube ψ M _ _ ψ fun i => ?_) H
  fin_cases i <;> simp [hu]

end Cube

theorem cmHostUnit_add_conj_eq_one {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) : H.w0 + H.bar H.w0 = 1 := by
  have hd : 0 < H.d := H.d_prime.pos
  have h1 : H.bar H.rt ^ 2 = H.rt ^ 2 := by rw [← map_pow, H.rt_sq]; simp
  have h2 : H.bar H.rt = -H.rt := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
    · exfalso
      obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
      have e := H.bar_eq H.rt
      rw [h] at e
      have e2 : starRingEnd ℂ (φ (H.rt : E)) = φ (H.rt : E) := by
        rw [← IsCMField.complexEmbedding_complexConj, ← e]
      have e3 : φ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
        have := congrArg (fun z : 𝓞 E => φ (z : E)) H.rt_sq
        simpa using this
      obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 e2
      rw [hr] at e3
      have e4 : r ^ 2 = -(H.d : ℝ) := by exact_mod_cast e3
      have : (0 : ℝ) < H.d := by exact_mod_cast hd
      nlinarith [sq_nonneg r]
    · exact h
  have h3 : 2 * H.bar H.w0 = 1 - H.rt := by
    have := congrArg H.bar H.two_weight_eq_one_add_root
    rw [map_mul, map_add (f := _), map_one, h2, map_ofNat] at this
    rw [this]; ring
  have h4 : (2 : 𝓞 E) * (H.w0 + H.bar H.w0) = 2 * 1 := by rw [mul_add, h3, H.two_weight_eq_one_add_root]; ring
  exact mul_left_cancel₀ two_ne_zero h4

end GlobalTheory.PelPrim


open GlobalTheory.PelPrim in
theorem GlobalTheory.pelClass_prim_and_iso : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (ρ : o) (t : TObj g k J b (spMap em)), PELClass D a bas ρ em t → (a w = H.w0 → a w' = H.bar H.w0 → t.Prim w w') ∧ ∀ t' : TObj g k J b (spMap em), TMap t' t (𝟙 _) → PELClass D a bas ρ em t' := by
  intro E _ _ _ H D o _ g k J b em w w' a bas ρ t ⟨τ, φ, hφ, hL, hact, hpt⟩
  refine ⟨fun hw hw' => ?_, fun t' ⟨ψ, hψ, hL', hpt', hact'⟩ => ?_⟩
  · let _ := t.ab.comm
    have hinv : ∀ j, t.act j ≫ φ.inv = φ.inv ≫ τ.act.act (a j) := fun j => by
      rw [Iso.comp_inv_eq, Category.assoc, hact, φ.inv_hom_id_assoc]
    have hL₀ : LBIso t.L (τ.PP.L.pull φ.inv.left) :=
      lbIso_inv (by rw [← Over.comp_left, φ.inv_hom_id, Over.id_left]) hL
    refine ⟨?_, adj_pull φ.inv t.isLB τ.PP.isLB hL₀ (hinv w) (hinv w') ?_,
      prim_pull φ.inv t.isLB τ.PP.isLB hL₀ (hinv w) ?_⟩
    · rw [← cancel_epi φ.hom, MonObj.comp_mul, ← hact, ← hact, ← MonObj.mul_comp, ← τ.act.add, hw, hw', cmHostUnit_add_conj_eq_one,
        τ.act.one, Category.id_comp, Category.comp_id]
    · rw [hw, hw']; exact τ.adj _
    · rw [hw]; exact τ.prim
  · have : IsMonHom (Iso.refl t.A).hom := inferInstanceAs (IsMonHom (𝟙 t.A))
    obtain ⟨e, he, hl⟩ := grpPullback_iso hψ (isGrpPullback_of_iso (Iso.refl t.A))
    have hl' : e.hom.left = ψ := (Category.comp_id _).symm.trans hl
    subst hl'
    have hact₀ : ∀ j, t.act j ≫ e.inv = e.inv ≫ t'.act j := fun j => by
      have : t'.act j ≫ e.hom = e.hom ≫ t.act j := Over.OverMorphism.ext (hact' j)
      rw [Iso.comp_inv_eq, Category.assoc, this, e.inv_hom_id_assoc]
    have hpt₀ : ∀ i, t.pt i ≫ e.inv = t'.pt i := fun i => by
      have : t'.pt i ≫ e.hom = t.pt i := Over.OverMorphism.ext ((hpt' i).trans (Category.id_comp _))
      rw [Iso.comp_inv_eq, this]
    have hL₀ : LBIso t.L (t'.L.pull e.inv.left) :=
      lbIso_inv (by rw [← Over.comp_left, e.inv_hom_id, Over.id_left]) hL'
    refine ⟨τ, φ ≪≫ e.symm, inferInstanceAs (IsMonHom (φ.hom ≫ e.inv)),
      lbIso_comp t'.isLB t.isLB τ.PP.isLB hL₀ hL, fun j => ?_, fun K _ _ _ x β hx => ?_⟩
    · show _ ≫ φ.hom ≫ e.inv = (φ.hom ≫ e.inv) ≫ _
      rw [← Category.assoc, hact, Category.assoc, hact₀, Category.assoc]
    · obtain ⟨h₁, I, h₂, h₃⟩ := hpt K x β hx
      refine ⟨h₁, I, h₂, fun i => ?_⟩
      show _ ≫ φ.hom ≫ e.inv = _
      rw [← Category.assoc, h₃, Category.assoc, hpt₀]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PelObjectClassPrimAndIsoClosedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pelObjectClass_prim_and_iso_closed : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (ρ : o) (t : TObj g k J b (spMap em)), PELClass D a bas ρ em t → (a w = H.w0 → a w' = H.bar H.w0 → t.Prim w w') ∧ ∀ t' : TObj g k J b (spMap em), TMap t' t (𝟙 _) → PELClass D a bas ρ em t' := by
  first | exact @GlobalTheory.pelClass_prim_and_iso | exact GlobalTheory.pelClass_prim_and_iso | (intros; apply GlobalTheory.pelClass_prim_and_iso <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueSumSingle
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.LieEigenbasis

theorem existsUnique_sum_single {k : Type} [Field k] {n N : ℕ} (s : Fin N → Fin n)
    (hs : Function.Injective s) (c : Fin n → k) (hc : ∀ i, i ∉ Set.range s → c i = 0) :
    ∃! d : Fin N → k, c = ∑ j, d j • (Pi.single (s j) 1 : Fin n → k) := by
  have h : ∀ (d : Fin N → k) (j : Fin N),
      (∑ j, d j • (Pi.single (s j) 1 : Fin n → k)) (s j) = d j := fun d j => by
    simp [Finset.sum_apply, Pi.single_apply, hs.eq_iff]
  refine ⟨fun j => c (s j), funext fun i => ?_, fun d hd => funext fun j => by rw [hd, h]⟩
  by_cases hi : i ∈ Set.range s
  · obtain ⟨j, rfl⟩ := hi
    rw [h]
  · rw [hc i hi, Finset.sum_apply]
    refine (Finset.sum_eq_zero fun j _ => ?_).symm
    have : i ≠ s j := fun e => hi ⟨j, e.symm⟩
    simp [this]

end GlobalTheory.LieEigenbasis


open ReciprocityTheory.ChartRestriction.G.Chart (prodPts scaleD tvec tmap) in
theorem GlobalTheory.lieMult_of_eigenbasis : ∀ (k : Type) [Field k] (O : Type) [CommRing O] (G : Over (Sp k)) [GrpObj G] (act : OAct O G) (n : ℕ) (v : Fin n → (epsR k ⟶ G)) (τs : Fin n → (O →+* k)), Smooth G.hom → IsLieBasis v → (∀ i a, (v i ≫ act.act a).left = spMap (epsScale (τs i a)) ≫ (v i).left) → ∀ τ : O →+* k, LieMult act (𝟙 (Sp k)) τ (Nat.card {i // τs i = τ}) := by
  intro k _ O _ G _ act n v τs _ hv hτ τ
  have := act.hom
  obtain ⟨x, hx, hxv⟩ := Chart.chart_of_basis hv
  have hxv' : ∀ j, v j = tvec (x := x) (Pi.single j 1) := hxv
  have hdiag : ∀ a i, tmap hx (act.act a) (Pi.single i 1) = τs i a • (Pi.single i 1 : Fin n → k) :=
    fun a i => (Chart.tvec_eig_iff hx _ _ _).1 (by
      rw [← hxv']; exact Over.OverMorphism.ext (hτ i a))
  have hmap : ∀ a c i, tmap hx (act.act a) c i = τs i a * c i := fun a c i => by
    conv_lhs => rw [← Finset.univ_sum_single c]
    have : ∀ j, (Pi.single j (c j) : Fin n → k) = c j • (Pi.single j 1 : Fin n → k) := fun j => by
      rw [← Pi.single_smul, smul_eq_mul, _root_.mul_one]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [this, map_sum, map_smul, hdiag]
    simp [Finset.sum_apply, Pi.single_apply, mul_comm]
  let N := Nat.card {i // τs i = τ}
  let q : Fin N ≃ {i // τs i = τ} := (Finite.equivFin _).symm
  let s : Fin N → Fin n := fun j => (q j).1
  have hs : Function.Injective s := Subtype.val_injective.comp q.injective
  have hpr : ∀ d : Fin N → k, prodPts d (fun j => v (s j)) =
      tvec (x := x) (∑ j, d j • (Pi.single (s j) 1 : Fin n → k)) := fun d => by
    have ht : ∀ j, Chart.IsTan (v (s j)) := fun j => (Chart.isTan_iff _).2 (hv.1 _)
    obtain ⟨h, e⟩ := Chart.prodPts_tan hx d (fun j => v (s j)) ht
    refine (Chart.tcoord_spec hx _ h).trans ?_
    change tvec (x := x) _ = _
    rw [e]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by rw [Chart.tcoord_eq hx _ (ht j) _ (hxv _)]
  let j : epsPt (𝟙 (Sp k)) ≅ epsR k := Over.isoMk (Iso.refl _) (by simp)
  let e : (epsPt (𝟙 (Sp k)) ⟶ G) ≃* (epsR k ⟶ G) :=
    MulEquiv.ofBijective (preHom j.inv) (j.symm.homCongr (Iso.refl G)).symm.bijective
  have he : ∀ w, (e w).left = w.left := fun w => Category.id_comp _
  have he' : ∀ w, (e.symm w).left = w.left := fun w => by rw [← he, e.apply_symm_apply]
  have one : (1 : Over.mk (𝟙 (Sp k)) ⟶ G).left = η[G].left := Category.id_comp _
  refine LiePull.basis_transport e.symm (Q := IsLieEigen act (𝟙 _) τ)
    (R' := fun c u v => u.left = spMap (epsScale c) ≫ v.left)
    (R := fun c u v => u.left = spMap (epsScaleR c) ≫ v.left)
    (P := fun w => IsTangent w ∧ ∀ a, w ≫ act.act a = Chart.spMap (scaleD (τ a)) ≫ w)
    (fun w => and_congr (by rw [IsTangent, he', one]) (forall_congr' fun a => by
      rw [Over.OverMorphism.ext_iff, Over.comp_left, Over.comp_left, Over.comp_left, he']
      rfl))
    (fun c u v => by rw [he', he']; rfl) N ⟨fun j => v (s j), fun j => ⟨hv.1 _, fun a => ?_⟩, ?_⟩
  · have := hτ (s j) a
    rw [(q j).2] at this
    exact Over.OverMorphism.ext this
  · rintro w ⟨hw, hw'⟩
    have ht := (Chart.isTan_iff _).2 hw
    obtain ⟨c, rfl⟩ : ∃ c, w = tvec (x := x) c := ⟨_, Chart.tcoord_spec hx w ht⟩
    refine (existsUnique_congr fun d => ?_).1
      (LieEigenbasis.existsUnique_sum_single s hs c fun i hi => ?_)
    · refine Iff.trans ?_ (Chart.isLieComb_iff d _ _).symm
      rw [hpr]
      exact ⟨fun h => by rw [← h], Chart.tvec_inj hx⟩
    · by_contra hc
      refine hi ⟨q.symm ⟨i, RingHom.ext fun a => ?_⟩, by simp [s]⟩
      have := congrFun ((Chart.tvec_eig_iff hx _ _ _).1 (hw' a)) i
      rw [hmap] at this
      exact mul_right_cancel₀ hc this
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.OpenImmersionCompStructureEqGeneric
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.Models

theorem Cpt.openImmersion_comp_structure_eq_generic {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {U : Scheme.{0}} {F O : Type}
    [Field F] [CommRing O] {c : U ⟶ Sp F} {t : SAB H U} {β : O →+* F} (C : Cpt c t β) :
    C.j ≫ C.s = c ≫ spMap β := by
  rw [Cpt.j, Category.assoc, pullback.condition, ← Category.assoc, C.jQ_over]

private theorem spMap_comp_moduli_spaces {A B D : Type} [CommRing A] [CommRing B] [CommRing D] (g : A →+* B) (g' : B →+* D) :
    spMap (g'.comp g) = spMap g' ≫ spMap g := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

theorem Cpt.Above.exists_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (U' : Scheme.{0}) (F' O' : Type) [Field F'] [CommRing O'] (c' : U' ⟶ Sp F') (t' : SAB H U') (β' : O' →+* F') (U'' : Scheme.{0}) (F'' O'' : Type) [Field F''] [CommRing O''] (c'' : U'' ⟶ Sp F'') (t'' : SAB H U'') (β'' : O'' →+* F'') (C : Cpt c t β) (C' : Cpt c' t' β') (C'' : Cpt c'' t'' β'') (b : O →+* O') (b' : O' →+* O'') (k' : F' →+* F'') (r : U' ⟶ U) (ν : SABMap t' t r) (a : C'.Above C b r ν) (r' : U'' ⟶ U') (ν' : SABMap t'' t' r') (f : C''.X ⟶ C.X) (mu : SABMap C''.t C.t f) (hf : f ≫ C.s = C''.s ≫ spMap (b'.comp b)), IsDedFrac β'' → β''.comp b' = k'.comp β' → r' ≫ c' = c'' ≫ spMap k' → C''.j ≫ f = r' ≫ r ≫ C.j → C''.m.φ ≫ mu.φ = ν'.φ ≫ ν.φ ≫ C.m.φ → ∃ (h : C''.X ⟶ C'.X) (mu' : SABMap C''.t C'.t h) (hh : h ≫ C'.s = C''.s ≫ spMap b'), h ≫ a.π = f ∧ mu'.φ ≫ a.mu.φ = mu.φ ∧ C''.j ≫ h = r' ≫ C'.j ∧ C''.m.φ ≫ mu'.φ = ν'.φ ≫ C'.m.φ ∧ (IsFinite (pullback.lift f C''.s hf) → IsFinite (pullback.lift h C''.s hh)) := by
  intro E _ _ _ H U F O _ _ c t β U' F' O' _ _ c' t' β' U'' F'' O'' _ _ c'' t'' β'' C C' C'' b b' k' r ν a r' ν' f mu hf
    hD hβ hc hj hφ
  obtain ⟨⟨hdom, hDed⟩, -, hFrac⟩ := hD
  let _ : Algebra O'' F'' := β''.toAlgebra
  have := hdom
  have : IsDedekindDomain O'' := hDed
  have : IsFractionRing O'' F'' := hFrac
  obtain ⟨hN, -, -, hPre, hFl, hDom, hQC⟩ := GlobalTheory.genericPart_dense_proOpen O'' F'' C''.X U'' C''.s C''.jQ C''.flat
    C''.proj C''.jQ_open C''.jQ_dense
  have : IsLocallyNoetherian C''.X := hN

  have hbase : f ≫ C.s = (C''.s ≫ spMap b') ≫ spMap b := by
    rw [hf, Category.assoc, spMap_comp_moduli_spaces]
  have hq : IsIntegralHom (pullback.lift a.π C'.s a.π_over) := by
    have := a.fin
    infer_instance
  have hsq : (r' ≫ C'.j) ≫ pullback.lift a.π C'.s a.π_over = C''.j ≫ pullback.lift f (C''.s ≫ spMap b') hbase := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, a.j_comm, hj]
    · simp only [Category.assoc, pullback.lift_snd]
      rw [Cpt.openImmersion_comp_structure_eq_generic C', ← Category.assoc r', hc, Category.assoc, ← spMap_comp_moduli_spaces, ← hβ,
        spMap_comp_moduli_spaces, ← Category.assoc C''.j, Cpt.openImmersion_comp_structure_eq_generic C'', Category.assoc]
  obtain ⟨h, ⟨h1, h2⟩, -⟩ := GlobalTheory.existsUnique_lift_of_densePart C''.X U'' (pullback C.s (spMap b)) C'.X C''.j C''.normal
    hPre hFl hDom hQC _ _ _ hq hsq
  have hπ : h ≫ a.π = f := by
    simpa only [Category.assoc, pullback.lift_fst] using congrArg (· ≫ pullback.fst _ _) h2
  have hh : h ≫ C'.s = C''.s ≫ spMap b' := by
    simpa only [Category.assoc, pullback.lift_snd] using congrArg (· ≫ pullback.snd _ _) h2
  clear h2 hsq hbase
  subst hπ
  obtain ⟨mu', hmu'⟩ := sabCancel pullCubCancel E H C.X C'.X C''.X C.t C'.t C''.t a.π h a.mu mu
  refine ⟨h, mu', hh, rfl, hmu'.symm, h1, ?_, ?_⟩
  · apply a.mu.2.1.hom_ext
    · rw [Category.assoc, Category.assoc]
      erw [← hmu', hφ, a.φ_comm]
    · have w1 := mu'.2.1.w
      have w2 := C''.m.2.1.w
      have w3 := ν'.2.1.w
      have w4 := C'.m.2.1.w
      have h1' : C''.jQ ≫ pullback.fst _ _ ≫ h = r' ≫ C'.jQ ≫ pullback.fst _ _ := by
        simpa only [Cpt.j, Category.assoc] using h1
      simp only [Category.assoc] at w1 w2 w3 w4 ⊢
      erw [w1, reassoc_of% w2, h1', w4, reassoc_of% w3]
  · intro hfin
    have : IsProper C'.s := projProper O' C'.X C'.s C'.proj
    let p : pullback C'.s (spMap b') ⟶ pullback C.s (spMap (b'.comp b)) :=
      pullback.lift (pullback.fst _ _ ≫ a.π) (pullback.snd _ _) (by
        rw [Category.assoc, a.π_over, ← Category.assoc, pullback.condition, Category.assoc, spMap_comp_moduli_spaces])
    have hp : pullback.lift h C''.s hh ≫ p = pullback.lift (h ≫ a.π) C''.s hf := by
      apply pullback.hom_ext
      · simp only [p, Category.assoc]
        rw [pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_fst]
      · simp only [p, Category.assoc]
        rw [pullback.lift_snd, pullback.lift_snd, pullback.lift_snd]
    have : IsSeparated p := by
      have e : p ≫ pullback.snd C.s (spMap (b'.comp b)) = pullback.snd C'.s (spMap b') := pullback.lift_snd _ _ _
      have : IsSeparated (p ≫ pullback.snd C.s (spMap (b'.comp b))) := by
        rw [e]
        infer_instance
      exact IsSeparated.of_comp p (pullback.snd C.s (spMap (b'.comp b)))
    rw [← hp] at hfin
    exact IsFinite.of_comp _ p

end GlobalTheory.Models
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGlobalLocDerOfIsCob
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS.GlueDer

theorem rsT_eq {Y : Scheme.{0}} {O₀ O : Y.Opens} (h : O ≤ O₀) (s : Γ(Y, O₀)) : rsT s O = resG Y h s := dif_pos h

theorem res_res {Y : Scheme.{0}} {U V V' : Y.Opens} (h : V ≤ U) (h' : V' ≤ V) (s : Γ(Y, U)) :
    resG Y h' (resG Y h s) = resG Y (h'.trans h) s := by
  simp only [resG]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem res_app {Y X : Scheme.{0}} (m : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) (h' : m ⁻¹ᵁ V ≤ m ⁻¹ᵁ U) (f : Γ(X, U)) :
    resG Y h' ((m.app U).hom f) = (m.app V).hom (resG X h f) := by
  simp only [resG]
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, m.naturality]
  rfl

theorem res_const {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {U V : X.Opens} (h : V ≤ U) (a : R) :
    resG X h (constFn p U a) = constFn p V a := by
  simp only [resG, constFn]
  exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_map p (U := ⊤) (V := U) (fun _ _ => trivial) (homOfLE h).op)

theorem app_const {R K : Type} [CommRing R] [CommRing K] {X Y : Scheme.{0}} (x₀ : R →+* K) (p : X ⟶ Sp R)
    (q : Y ⟶ Sp K) (m : Y ⟶ X) (hm : m ≫ p = q ≫ spMap x₀) (U : X.Opens) (a : R) :
    (m.app U).hom (constFn p U a) = constFn q (m ⁻¹ᵁ U) (x₀ a) := by
  have h1 : (m.app U).hom (constFn p U a) = constFn (m ≫ p) (m ⁻¹ᵁ U) a := by
    simp only [constFn]
    rw [Scheme.Hom.app_eq_appLE]
    exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
      (Scheme.Hom.appLE_comp_appLE m p ⊤ U (m ⁻¹ᵁ U) (fun _ _ => trivial) le_rfl)
  rw [h1, hm]
  simp only [constFn]
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (x₀ a) =
      ((spMap x₀).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) := by
    have := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom x₀)
    exact congrArg (fun φ => φ.hom a) this
  rw [h2]
  exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.comp_appLE q (spMap x₀) ⊤ (m ⁻¹ᵁ U) (fun _ _ => trivial))

theorem pre_mono {Y X : Scheme.{0}} (m : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) : m ⁻¹ᵁ V ≤ m ⁻¹ᵁ U :=
  fun _ hx => h hx

theorem pre_cover {Y X : Scheme.{0}} (m : Y ⟶ X) {I : Type} (W : I → X.Opens) (hW : ⨆ i, W i = ⊤) (O : X.Opens) :
    m ⁻¹ᵁ O ≤ ⨆ i, m ⁻¹ᵁ (O ⊓ W i) := by
  intro y hy
  have : m y ∈ ⨆ i, W i := by rw [hW]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp this
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hy, hi⟩

theorem glue {K : Type} [Field K] {R : Type} [CommRing R] {Y X : Scheme.{0}} (q : Y ⟶ Sp K) (p : X ⟶ Sp R)
    (m : Y ⟶ X) (D : R → K) {I : Type} (W : I → X.Opens) (hW : ⨆ i, W i = ⊤)
    (e : I → ∀ O : X.Opens, Γ(X, O) → Γ(Y, m ⁻¹ᵁ O)) (he : ∀ i, LocDerK q p m D (W i) (e i))
    (hc : ∀ i j O, O ≤ W i ⊓ W j → ∀ f, e i O f = e j O f) : ∃ d₁, LocDerK q p m D ⊤ d₁ := by
  have ex : ∀ (O : X.Opens) (f : Γ(X, O)), ∃ s : Γ(Y, m ⁻¹ᵁ O), ∀ i,
      resG Y (pre_mono m (inf_le_left : O ⊓ W i ≤ O)) s = e i (O ⊓ W i) (resG X inf_le_left f) := by
    intro O f
    obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' (fun i => m ⁻¹ᵁ (O ⊓ W i)) (m ⁻¹ᵁ O)
      (fun i => homOfLE (pre_mono m inf_le_left)) (pre_cover m W hW O)
      (fun i => e i (O ⊓ W i) (resG X inf_le_left f)) (by
        intro i j
        have hi := (he i).res (O ⊓ W i) ((O ⊓ W i) ⊓ (O ⊓ W j)) inf_le_left inf_le_right (resG X inf_le_left f)
        have hj := (he j).res (O ⊓ W j) ((O ⊓ W i) ⊓ (O ⊓ W j)) inf_le_right inf_le_right (resG X inf_le_left f)
        rw [rsT_eq (pre_mono m inf_le_left), res_res] at hi
        rw [rsT_eq (pre_mono m inf_le_right), res_res] at hj
        have := hc i j ((O ⊓ W i) ⊓ (O ⊓ W j)) (inf_le_inf inf_le_right inf_le_right)
          (resG X (inf_le_left.trans inf_le_left) f)
        exact hi.symm.trans (this.trans hj))
    exact ⟨s, hs⟩
  have ext : ∀ (O : X.Opens) (s t : Γ(Y, m ⁻¹ᵁ O)), (∀ i,
      resG Y (pre_mono m (inf_le_left : O ⊓ W i ≤ O)) s = resG Y (pre_mono m (inf_le_left : O ⊓ W i ≤ O)) t) →
      s = t := fun O s t h =>
    Y.sheaf.eq_of_locally_eq' (fun i => m ⁻¹ᵁ (O ⊓ W i)) (m ⁻¹ᵁ O)
      (fun i => homOfLE (pre_mono m inf_le_left)) (pre_cover m W hW O) s t h
  choose d₁ hd using ex
  refine ⟨d₁, ?_, ?_, ?_, ?_⟩
  · intro O _ f f'
    refine ext O _ _ fun i => ?_
    rw [map_add (f := _), hd, hd, hd, map_add (f := _), (he i).add _ inf_le_right]
  · intro O _ f f'
    refine ext O _ _ fun i => ?_
    rw [map_add (f := _), map_mul, map_mul, hd, hd, hd, map_mul, (he i).mul _ inf_le_right,
      res_app m inf_le_left, res_app m inf_le_left]
  · intro O O' h _ f
    refine ext O' _ _ fun i => ?_
    have h' : O' ⊓ W i ≤ O ⊓ W i := inf_le_inf_right _ h
    have h1 := (he i).res (O ⊓ W i) (O' ⊓ W i) h' inf_le_right (resG X inf_le_left f)
    rw [rsT_eq (pre_mono m h'), res_res, ← hd, res_res] at h1
    rw [hd, rsT_eq (pre_mono m h), res_res, res_res, h1]
  · intro O _ r
    refine ext O _ _ fun i => ?_
    rw [hd, res_const, res_const, (he i).base _ inf_le_right]

end GlobalTheory.KS.GlueDer


open GlobalTheory.KS.GlueDer in
theorem GlobalTheory.KS.exists_global_locDer_of_isCob : ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (g : ℕ) (v : Fin g → (epsR K ⟶ A₀)) (dd : Fin g → ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)), Smooth A₀.hom → IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (R : Type) [CommRing R] (x₀ : R →+* K) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : A₀.left ⟶ X), IsPullback m A₀.hom p (spMap x₀) → ∀ (I : Type) (W : I → X.Opens) (D : R → K) d θ, ⨆ i, W i = ⊤ → KSCoc A₀.hom p m D W dd d θ → (∀ a, IsCob _ (θ a)) → ∃ d₁, LocDerK A₀.hom p m D ⊤ d₁ := by
  intro K _ A₀ _ g v dd _ hv hdd R _ x₀ X p m hm I W D d θ hW hc hb
  choose b hb using hb
  have H := fun a => (GlobalTheory.T.exists_unique_invariantVectorField_of_tangent K A₀ (v a) (hv.1 a)).2 (dd a) (hdd a)
  refine glue A₀.hom p m D W hW
    (fun i O f => d i O f - ∑ a, rsT (b a i) (m ⁻¹ᵁ O) * dd a (m ⁻¹ᵁ O) ((m.app O).hom f)) (fun i => ?_) ?_
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro O hO f f'
      simp only [(hc.der i).add O hO, map_add (f := _), fun a => (H a).1, mul_add, Finset.sum_add_distrib]
      ring
    · intro O hO f f'
      simp only [(hc.der i).mul O hO, map_mul, fun a => (H a).2.1, mul_add, Finset.sum_add_distrib, mul_sub,
        Finset.mul_sum, mul_left_comm (rsT _ _)]
      ring
    · intro O O' h hO f
      have h' := pre_mono m h
      set_option synthInstance.maxHeartbeats 100000 in
        rw [(hc.der i).res O O' h hO, rsT_eq h', rsT_eq h', map_sub, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      have h2 := (H a).2.2.1 _ _ ((m.app O).hom f) h'
      rw [rsT_eq h', rsT_eq h', res_app m h] at h2
      rw [map_mul, h2, rsT_eq (pre_mono m hO), rsT_eq (pre_mono m (h.trans hO)), res_res]
    · intro O hO r
      simp only [(hc.der i).base O hO, app_const x₀ p A₀.hom m hm.w, fun a => (H a).2.2.2.1, mul_zero,
        Finset.sum_const_zero, sub_zero]
  · intro i j O hO f
    have h1 := hc.diff i j O hO f
    have hi : m ⁻¹ᵁ O ≤ m ⁻¹ᵁ W i := pre_mono m (hO.trans inf_le_left)
    have hj : m ⁻¹ᵁ O ≤ m ⁻¹ᵁ W j := pre_mono m (hO.trans inf_le_right)
    have h2 : ∀ a, rsT (θ a i j) (m ⁻¹ᵁ O) = rsT (b a j) (m ⁻¹ᵁ O) - rsT (b a i) (m ⁻¹ᵁ O) := by
      intro a
      rw [hb, rsT_eq (le_inf hi hj), map_sub, rsT_eq inf_le_right, rsT_eq inf_le_left, res_res, res_res,
        rsT_eq hi, rsT_eq hj]
    simp only [h2, sub_mul, Finset.sum_sub_distrib] at h1
    show _ - _ = _ - _
    linear_combination -h1
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionOfIsPullbackIsDominant
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory

theorem smoothOfRelativeDimension_of_isPullback_isDominant :
    ∀ (X U Y Y' : Scheme.{0}) (j : U ⟶ X) (p : Y ⟶ X) (p' : Y' ⟶ U) (φ : Y' ⟶ Y) (g : ℕ),
      IsPullback φ p' p j → IsDominant j → Smooth p → SmoothOfRelativeDimension g p' →
        SmoothOfRelativeDimension g p := by
  intro X U Y Y' j p p' φ g hpb hj hp hg
  have := hp
  have key : ∀ y : Y, ∃ W : Y.Opens, y ∈ W ∧ SmoothOfRelativeDimension g (W.ι ≫ p) := by
    intro y
    obtain ⟨n, W, hyW, hn⟩ := ReciprocityTheory.ChartRestriction.G.H1.exists_dim p y
    have hopen : IsOpen (p '' (W : Set Y)) := p.isOpenMap _ W.isOpen
    obtain ⟨u, w, hwW, hwu⟩ := hj.denseRange.exists_mem_open hopen ⟨p y, y, hyW, rfl⟩
    obtain ⟨z, hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback w u hwu
    have h1 : φ (hpb.isoPullback.inv z) = w := by
      rw [← Scheme.Hom.comp_apply, hpb.isoPullback_inv_fst, hz1]
    have hng := ReciprocityTheory.ChartRestriction.G.H1.dim_base hpb hn hg (hpb.isoPullback.inv z) (h1 ▸ hwW)
    subst hng
    exact ⟨W, hyW, hn⟩
  choose W hyW hW using key
  have hloc : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{0} g) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @SmoothOfRelativeDimension.{0} g)
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension.{0} g) W ?_ hW
  rw [eq_top_iff]
  intro y _
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hyW y⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLocalMultiplicationPullbackThetaEmbeddingI
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.EmbedLocal

theorem isPullback_whisker {S : Scheme.{0}} (A : Over S) {T T' : Over S} (h : T' ⟶ T) :
    IsPullback (h ▷ A).left (fst T' A).left (fst T A).left h.left := by
  have h1 : IsPullback (snd T A).left (fst T A).left A.hom T.hom := (IsPullback.of_hasPullback T.hom A.hom).flip
  have h2 : IsPullback (snd T' A).left (fst T' A).left A.hom T'.hom := (IsPullback.of_hasPullback T'.hom A.hom).flip
  refine IsPullback.of_right ?_ ?_ h1
  · rw [← Over.comp_left, whiskerRight_snd, Over.w h]; exact h2
  · rw [← Over.comp_left, ← Over.comp_left, whiskerRight_fst]

theorem of_parts
    (hex : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (m : ℕ) (R : Type) [CommRing R] (x : Sp R ⟶ S), Odd N' → m ∣ N' → ∀ p : Sp R, ∃ (R' : Type) (_ : CommRing R') (φ : R →+* R') (σ : _), IsOpenImmersion (spMap φ) ∧ p ∈ Set.range (spMap φ) ∧ t.Emb m (Over.mk (spMap φ ≫ x)) σ)
    (hpb : Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (m : ℕ) (T T' : Over S) (h : T' ⟶ T) σ, IsAffine T.left → IsAffine T'.left → t.Emb m T σ → ∃ σ', t.Emb m T' σ' ∧ ∀ (R : Type) [CommRing R] (y : Sp R ⟶ (T' ⊗ t.A).left) (w : Ix g (N' ^ 2) → R), SecCoord _ σ' y w ↔ SecCoord _ σ (y ≫ (h ▷ t.A).left) w)
    (hspan : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (m : ℕ) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) σ, Odd N' → m ∣ N' → 2 ≤ m → t.Emb m (Over.mk x) σ → Submodule.span Γ((Over.mk x).left, ⊤) (Set.range fun a => (Out.SecM.ofSec t.A (σ a) : Out.SecM t.A t.L ((m : ℤ) ^ 2) (Over.mk x))) = ⊤)
    (hva : Out.Laws → Out.Laws2 → ∀ (S : Scheme.{0}) (P : Out.PolAV S) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (k : ℤ) (I : Type) [Finite I] (σ : I → LB.Sec (Out.LPow P.A P.L k (Over.mk x))), 4 ≤ k → Submodule.span Γ((Over.mk x).left, ⊤) (Set.range fun a => (Out.SecM.ofSec P.A (σ a) : Out.SecM P.A P.L k (Over.mk x))) = ⊤ → ProjRep (idealOf (fst (Over.mk x) P.A).left _ σ (𝟙 _)) (fst (Over.mk x) P.A).left _ σ)
    (hfib : ∀ (R σ : Type) [CommRing R] [Finite σ] (X : Scheme.{0}) (s : X ⟶ Sp R) (M : LB X) (th : σ → M.Sec), M.IsLB → IsProper s → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K), ∃ (X' : Scheme.{0}) (π : X' ⟶ X) (s' : X' ⟶ Sp K) (M' : LB X') (th' : σ → M'.Sec) (I : Ideal (MvPolynomial σ K)), IsPullback π s' s (spMap x) ∧ ProjRep I s' M' th' ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ X') (w : σ → T), SecCoord M' th' y w ↔ SecCoord M th (y ≫ π) w) → ProjRep (idealOf s M th (𝟙 X)) s M th) :
    Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (m : ℕ) (R : Type) [CommRing R] (x : Sp R ⟶ S) (v : Ix g (N' ^ 2) → R), m ^ 2 ∣ N' → 2 ≤ m → t.HasTh x v → ∀ p : Sp R, ∃ (R' : Type) (_ : CommRing R') (φ : R →+* R') (σ : _), IsOpenImmersion (spMap φ) ∧ p ∈ Set.range (spMap φ) ∧ t.Emb m (Over.mk (spMap φ ≫ x)) σ ∧ ProjRep (idealOf (fst (Over.mk (spMap φ ≫ x)) t.A).left _ σ (𝟙 _)) (fst (Over.mk (spMap φ ≫ x)) t.A).left _ σ := by
  intro l1 l2 o _ g N' J b S s t m R _ x v hm h2 hth p
  have hodd : Odd N' := hth.1
  have hdvd : m ∣ N' := (dvd_pow_self m two_ne_zero).trans hm
  haveI : NeZero (N' ^ 2) := ⟨pow_ne_zero 2 hodd.pos.ne'⟩
  obtain ⟨R', _, φ, σ, hφ, hp, hE⟩ := hex l1 l2 o g N' J b S s t m R x hodd hdvd p
  refine ⟨R', inferInstance, φ, σ, hφ, hp, hE, ?_⟩
  refine hfib R' (Ix g (N' ^ 2)) _ _ _ σ (LB.isLB_linComb t.isLB _ _) ?_ ?_
  · haveI := t.ab.proper
    exact inferInstanceAs (IsProper (pullback.fst (spMap φ ≫ x) t.A.hom))
  · intro K _ _ y
    let h : Over.mk (spMap y ≫ spMap φ ≫ x) ⟶ Over.mk (spMap φ ≫ x) := Over.homMk (spMap y) rfl
    obtain ⟨σ', hE', hc⟩ := hpb l2 o g N' J b S s t m _ _ h σ
      (inferInstanceAs (IsAffine (Spec _))) (inferInstanceAs (IsAffine (Spec _))) hE
    have hs := hspan l1 l2 o g N' J b S s t m K _ σ' hodd hdvd h2 hE'
    have h4 : (4 : ℤ) ≤ (m : ℤ) ^ 2 := by
      have : (2 : ℤ) ≤ m := by exact_mod_cast h2
      nlinarith
    exact ⟨_, (h ▷ t.A).left, _, _, σ', _, isPullback_whisker t.A h,
      hva l1 l2 S t.pol K _ _ _ σ' h4 hs, hc⟩

end GlobalTheory.ZM.EmbedLocal
end
