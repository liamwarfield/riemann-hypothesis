module

public import Development.AbelianVarietyTheory.Definitions.RegularCharts.MatrixTwoByTwoCongr
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsGoodIntegral
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsInvariantNatLengthLattice
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FinrankHostDivTwo
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsDenomOfIsAffineOpen

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieBasisCoordinatesBijectiveTangent
section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieBasisCoordinatesBijectiveTangent
noncomputable section

namespace GlobalTheory.Reg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem isTangent_of_isLieComb {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {n : ℕ} {cv : Fin n → R}
    {v : Fin n → (epsR R ⟶ G)} {w : epsR R ⟶ G} (hv : ∀ i, IsTangent (v i)) (h : IsLieComb cv v w) :
    IsTangent w := by
  rw [(Chart.isLieComb_iff cv v w).1 h, ← Chart.isTan_iff]
  refine List.prod_induction Chart.IsTan (fun a b ha hb => Chart.isTan_mul ha hb) Chart.isTan_one ?_
  intro a ha
  obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 ha
  exact Chart.isTan_scale (cv i) ((Chart.isTan_iff _).2 (hv i))

theorem vec_bijective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (R : Type) [CommRing R] [Algebra c.F R] (f : Γ(Y.X, M.U) →+* R) (x : Sp R ⟶ Xo.X) (Λ : M.Lift f x), (∀ cv, ∃! w, Λ.Vec cv w) ∧ (∀ cv w, Λ.Vec cv w → IsTanAt x w) ∧ ∀ w, IsTanAt x w → ∃! cv, Λ.Vec cv w := by
  intro E _ _ _ H Dw l Xo c O _ β Y M R _ _ f x Λ
  obtain ⟨v, hv, hb, -⟩ := M.lie R f Λ.t' Λ.m2
  have key : ∀ cv w, Λ.Vec cv w ↔ ∃ u', IsLieComb cv v u' ∧ u'.left ≫ Λ.m1.φ = w := by
    intro cv w
    constructor
    · rintro ⟨v', u', h1, h2, h3⟩
      have e : v' = v := funext fun j => Chart.inj_over Λ.m2.cart ((h1 j).trans (hv j).symm)
      exact ⟨u', e ▸ h2, h3⟩
    · rintro ⟨u', h2, h3⟩
      exact ⟨v, u', hv, h2, h3⟩
  refine ⟨fun cv => ?_, fun cv w h => ?_, fun w hw => ?_⟩
  · refine ⟨(Chart.prodPts cv v).left ≫ Λ.m1.φ, (key _ _).2 ⟨_, (Chart.isLieComb_iff cv v _).2 rfl, rfl⟩, ?_⟩
    intro w hw
    obtain ⟨u', h2, h3⟩ := (key _ _).1 hw
    rw [← h3, (Chart.isLieComb_iff cv v _).1 h2]
  · obtain ⟨u', h2, rfl⟩ := (key _ _).1 h
    refine ⟨?_, (Chart.tan_push Λ.m1.cart u').1 (isTangent_of_isLieComb hb.1 h2)⟩
    have e1 : Λ.m1.φ ≫ Xo.univ.t.G.hom = Λ.t'.G.hom ≫ x := Λ.m1.cart.1.w
    have e2 : u'.left ≫ Λ.t'.G.hom = spMap (algebraMap R (DualNumber R)) := Over.w u'
    rw [Category.assoc, e1, ← Category.assoc, e2]
  · let u' : epsR R ⟶ Λ.t'.G :=
      Over.homMk (Λ.m1.cart.1.lift w (spMap (algebraMap R (DualNumber R))) hw.1) (Λ.m1.cart.1.lift_snd _ _ _)
    have hu : u'.left ≫ Λ.m1.φ = w := Λ.m1.cart.1.lift_fst _ _ _
    have ht : IsTangent u' := (Chart.tan_push Λ.m1.cart u').2 (by
      have := hw.2
      rw [← hu] at this
      exact this)
    obtain ⟨cv, hc, huniq⟩ := hb.2 u' ht
    refine ⟨cv, (key _ _).2 ⟨u', hc, hu⟩, fun cv' h' => ?_⟩
    obtain ⟨u'', h2, h3⟩ := (key _ _).1 h'
    have e : u'' = u' := Chart.inj_over Λ.m1.cart (h3.trans hu.symm)
    exact huniq cv' (e ▸ h2)

end GlobalTheory.Reg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieBasisCoordinatesBijectiveTangentStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieBasis_coordinates_bijective_tangent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (R : Type) [CommRing R] [Algebra c.F R] (f : Γ(Y.X, M.U) →+* R) (x : Sp R ⟶ Xo.X) (Λ : M.Lift f x), (∀ cv, ∃! w, Λ.Vec cv w) ∧ (∀ cv w, Λ.Vec cv w → IsTanAt x w) ∧ ∀ w, IsTanAt x w → ∃! cv, Λ.Vec cv w := by
  first | exact @GlobalTheory.Reg.vec_bijective | exact GlobalTheory.Reg.vec_bijective | (intros; apply GlobalTheory.Reg.vec_bijective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsEigenvectorIffLieBasisCoordinates
section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsEigenvectorIffLieBasisCoordinates
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

noncomputable section

namespace GlobalTheory.Reg.VecEig

open GlobalTheory.GrpTangent

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

def comb {n : ℕ} (v : Fin n → (epsR R ⟶ G)) (c : Fin n → R) : epsR R ⟶ G :=
  ∏ i, epsScale (c i) ≫ v i

theorem isLieComb_iff_comb {n : ℕ} (c : Fin n → R) (v : Fin n → (epsR R ⟶ G)) (w : epsR R ⟶ G) :
    IsLieComb c v w ↔ w = comb v c := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [List.prod_ofFn]
    refine Finset.prod_congr rfl fun i _ => ?_
    apply Over.OverMorphism.ext
    rw [hu i, Over.comp_left]
    rfl
  · rintro rfl
    refine ⟨fun i => epsScale (c i) ≫ v i, fun i => ?_, ?_⟩
    · rw [Over.comp_left]
      rfl
    · rw [List.prod_ofFn]
      rfl

theorem comp_finProd {X Y : Over (Sp R)} (g : X ⟶ Y) {κ : Type} (s : Finset κ) (u : κ → (Y ⟶ G)) :
    g ≫ ∏ i ∈ s, u i = ∏ i ∈ s, g ≫ u i := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.prod_empty, Finset.prod_empty]
    exact Chart.comp_one' g
  · intro a t ha ih
    rw [Finset.prod_insert ha, Finset.prod_insert ha, comp_mul, ih]

theorem finProd_comp {X : Over (Sp R)} (g : G ⟶ G) [IsMonHom g] {κ : Type} (s : Finset κ) (u : κ → (X ⟶ G)) :
    (∏ i ∈ s, u i) ≫ g = ∏ i ∈ s, u i ≫ g := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.prod_empty, Finset.prod_empty]
    exact one_comp g
  · intro a t ha ih
    rw [Finset.prod_insert ha, Finset.prod_insert ha, mul_comp, ih]

theorem epsScale_sum_comp {w : epsR R ⟶ G} (hw : IsTangent w) {κ : Type} (s : Finset κ) (a : κ → R) :
    epsScale (∑ i ∈ s, a i) ≫ w = ∏ i ∈ s, epsScale (a i) ≫ w := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.prod_empty]
    exact epsScale_zero_comp hw
  · intro b t hb ih
    rw [Finset.sum_insert hb, Finset.prod_insert hb, epsScale_add_comp _ _ hw, ih]

theorem epsScale_comb {n : ℕ} (v : Fin n → (epsR R ⟶ G)) (c : Fin n → R) (z : R) :
    epsScale z ≫ comb v c = comb v (z • c) := by
  unfold comb
  rw [comp_finProd]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Category.assoc, epsScale_mul, Pi.smul_apply, smul_eq_mul]

theorem comb_comp {n : ℕ} {v : Fin n → (epsR R ⟶ G)} (hv : ∀ i, IsTangent (v i)) (g : G ⟶ G) [IsMonHom g]
    (A : Matrix (Fin n) (Fin n) R) (hA : ∀ j, v j ≫ g = comb v fun i => A i j) (c : Fin n → R) :
    comb v c ≫ g = comb v (A.mulVec c) := by
  calc comb v c ≫ g = ∏ j, (epsScale (c j) ≫ v j) ≫ g := finProd_comp g _ _
    _ = ∏ j, comb v (c j • fun i => A i j) :=
        Finset.prod_congr rfl fun j _ => by rw [Category.assoc, hA j, epsScale_comb]
    _ = ∏ j, ∏ i, epsScale (A i j * c j) ≫ v i := Finset.prod_congr rfl fun j _ => by
        unfold comb
        exact Finset.prod_congr rfl fun i _ => by rw [Pi.smul_apply, smul_eq_mul, mul_comm (c j)]
    _ = ∏ i, ∏ j, epsScale (A i j * c j) ≫ v i := Finset.prod_comm
    _ = comb v (A.mulVec c) := by
        unfold comb
        exact Finset.prod_congr rfl fun i _ => (epsScale_sum_comp (hv i) Finset.univ fun j => A i j * c j).symm

theorem isTangent_comb {n : ℕ} {v : Fin n → (epsR R ⟶ G)} (hv : ∀ i, IsTangent (v i)) (c : Fin n → R) :
    IsTangent (comb v c) := by
  rw [isTangent_iff]
  unfold comb
  rw [comp_finProd]
  exact Finset.prod_eq_one fun i _ => (isTangent_iff _).1 (isTangent_epsScale (c i) (hv i))

theorem comb_injective {n : ℕ} {v : Fin n → (epsR R ⟶ G)} (hv : IsLieBasis v) : Function.Injective (comb v) := by
  intro c d h
  have hc : IsLieComb c v (comb v c) := (isLieComb_iff_comb c v (comb v c)).2 rfl
  have hd : IsLieComb d v (comb v c) := (isLieComb_iff_comb d v (comb v c)).2 h
  exact (hv.2 _ (isTangent_comb hv.1 c)).unique hc hd

theorem pt_ext {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f) {X : Over S'} {u u' : X ⟶ t'.G}
    (h : u.left ≫ m.φ = u'.left ≫ m.φ) : u = u' := by
  cases m with
  | mk cm cart base act lin =>
    apply Over.OverMorphism.ext
    refine cart.1.hom_ext h ?_
    rw [Over.w u, Over.w u']

end GlobalTheory.Reg.VecEig


open GlobalTheory.Reg.VecEig GlobalTheory.GrpTangent in
theorem GlobalTheory.Reg.isEigAt_iff_eig : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (R : Type) [CommRing R] [Algebra c.F R] (f : Γ(Y.X, M.U) →+* R) (x : Sp R ⟶ Xo.X) (Λ : M.Lift f x), ∀ (τ : E →+* ℂ) (cv : Fin M.n → R) (w : Sp (DualNumber R) ⟶ Xo.univ.t.G.left), Λ.Vec cv w → (IsEigAt c τ w ↔ M.Eig f τ cv) := by
  intro E _ _ _ H Dw l Xo c O _ β Y M R _ _ f x Λ τ cv w hw
  obtain ⟨v', u', hv', hu', rfl⟩ := hw
  obtain ⟨v, hv0, hvb, hρ⟩ := M.lie R f Λ.t' Λ.m2
  obtain rfl : v' = v := funext fun j => pt_ext Λ.m2 ((hv' j).trans (hv0 j).symm)
  have hu := (isLieComb_iff_comb _ _ _).1 hu'
  have hA := fun a j => (isLieComb_iff_comb _ _ _).1 (hρ a j)
  unfold IsEigAt MChart.Eig
  refine forall_congr' fun a => ?_
  have : IsMonHom (Λ.t'.act.act a) := Λ.t'.act.hom a
  have e1 : (u'.left ≫ Λ.m1.φ) ≫ (Xo.univ.t.act.act a).left = (u' ≫ Λ.t'.act.act a).left ≫ Λ.m1.φ := by
    rw [Over.comp_left, Category.assoc, Category.assoc]
    exact congrArg (u'.left ≫ ·) (Λ.m1.act a).symm
  have e2 : spMap (epsMul (algebraMap c.F R (embK c τ a))) ≫ u'.left ≫ Λ.m1.φ =
      (epsScale (algebraMap c.F R (embK c τ a)) ≫ u').left ≫ Λ.m1.φ := by
    rw [Over.comp_left, Category.assoc]
    rfl
  rw [e1, e2, hu, comb_comp hvb.1 _ ((M.ρ a).map f) (hA a), epsScale_comb]
  constructor
  · intro h
    exact comb_injective hvb (pt_ext Λ.m1 h)
  · intro h
    rw [h]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsEigenvectorIffLieBasisCoordinatesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isEigenvector_iff_lieBasis_coordinates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (R : Type) [CommRing R] [Algebra c.F R] (f : Γ(Y.X, M.U) →+* R) (x : Sp R ⟶ Xo.X) (Λ : M.Lift f x), ∀ (τ : E →+* ℂ) (cv : Fin M.n → R) (w : Sp (DualNumber R) ⟶ Xo.univ.t.G.left), Λ.Vec cv w → (IsEigAt c τ w ↔ M.Eig f τ cv) := by
  first | exact @GlobalTheory.Reg.isEigAt_iff_eig | exact GlobalTheory.Reg.isEigAt_iff_eig | (intros; apply GlobalTheory.Reg.isEigAt_iff_eig <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.TriangularFrameChangeOfTriangularPeriod
section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.TriangularFrameChangeOfTriangularPeriod
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open Formalism.L2.PjFree hiding relab toC
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif GlobalTheory.FrameNorm
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.FrameNorm

theorem mulVec_single_of_support {T : Type} {m : T → ℕ} {g : ℕ} (e : Fin g ≃ Σ τ : T, Fin (m τ))
    (h : Matrix (Fin g) (Fin g) ℂ) (hs : ∀ j j', h j j' ≠ 0 → (e j).1 = (e j').1) (τ : T) (i : Fin (m τ)) :
    h *ᵥ Pi.single (e.symm ⟨τ, i⟩) 1 =
      ∑ i', h (e.symm ⟨τ, i'⟩) (e.symm ⟨τ, i⟩) • (Pi.single (e.symm ⟨τ, i'⟩) 1 : Fin g → ℂ) := by
  classical
  ext j
  obtain ⟨⟨τ', a⟩, rfl⟩ := e.symm.surjective j
  simp only [Matrix.mulVec_single_one, Matrix.col_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hτ : τ' = τ
  · subst hτ
    rw [Finset.sum_eq_single a (fun b _ hb => ?_) (by simp), Pi.single_eq_same, mul_one]
    rw [Pi.single_eq_of_ne, mul_zero]
    intro hh
    exact hb (eq_of_heq (Sigma.mk.inj (e.symm.injective hh)).2).symm
  · rw [Finset.sum_eq_zero fun b _ => ?_]
    · by_contra hne
      have := hs _ _ hne
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
      exact hτ this
    · rw [Pi.single_eq_of_ne, mul_zero]
      intro hh
      exact hτ (Sigma.mk.inj (e.symm.injective hh)).1


set_option maxHeartbeats 1000000 in
theorem frBor_of_triangular_period : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (k : Fin F.n) (P P₀ : (F.Di k).La →+ (Fin g → ℂ)) (h₀ : Matrix (Fin g) (Fin g) ℂ) (y y₀ : FrPt Xo c (CAt σ)), IsPeriod (F.Di k) (fun j => relab c σ (e j).1) P → IsPeriod (F.Di k) (fun j => relab c σ (e j).1) P₀ → (∀ a, P₀ a = h₀ *ᵥ P a) → (∀ j j', h₀ j j' ≠ 0 → (e j).1 = (e j').1 ∧ ((e j).2 : ℕ) ≤ (e j').2) → y.x = F.u k P → y₀.x = F.u k P₀ → (∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex k P z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) (y.u τ i)) → (∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex k P₀ z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) (y₀.u τ i)) → ∃ t : Ix Dw → (CAt σ)ˣ, FrBor t y₀ y ∧ ∀ j, toC (t (some (e j)) : CAt σ) = h₀ j j := by
  intro E _ _ _ H Dw l Xo c σ g e F k P P₀ h₀ y y₀ hP hP₀ hh hs hy hy₀ hu hu₀
  classical
  obtain ⟨hdet, hpt, hex⟩ := GlobalTheory.FamRigid.ex_eq_of_level_group GlobalTheory.latMinkowski E H Dw l Xo _ g _ F k P P₀
    (LinearEquiv.refl _ _) h₀ hP hP₀ (fun _ _ => rfl) (fun a _ => ⟨0, by simp⟩) (fun a => ⟨0, by simp⟩) hh
  have hinj : ∀ j j', (e j).1 = (e j').1 → ((e j).2 : ℕ) = (e j').2 → j = j' := by
    intro j j' h1 h2
    apply e.injective
    exact Sigma.ext h1 ((Fin.heq_ext_iff (by rw [h1])).2 h2)
  have hdiag : ∀ j, h₀ j j ≠ 0 := by
    rw [GlobalTheory.PerBor.det_of_support (fun j => (e j).1) (fun j => ((e j).2 : ℕ)) hinj h₀ hs] at hdet
    exact fun j => Finset.prod_ne_zero_iff.1 hdet.ne_zero j (Finset.mem_univ j)
  have hx : y.x = y₀.x := hy.trans (hpt.trans hy₀.symm)
  let cf : ∀ τ, Fin (Dw.mult τ) → Fin (Dw.mult τ) → CAt σ := fun τ i i' =>
    (h₀ (e.symm ⟨τ, i'⟩) (e.symm ⟨τ, i⟩) : ℂ)
  have hc : ∀ τ i, IsCombAt y₀.x (y₀.u τ) (cf τ i) (y.u τ i) := by
    intro τ i
    have d1 := (GlobalTheory.ExpChain.isDerivAt0_ex_iff E H Dw l Xo _ g _ F k P hP k P₀ (Matrix.mulVecLin h₀) hP₀ hex
      _ _).1 (hu τ i)
    rw [Matrix.mulVecLin_apply, mulVec_single_of_support e h₀ (fun j j' h => (hs j j' h).1)] at d1
    have d2 := (GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F k P₀ hP₀ _ (y₀.u τ)
      (fun i => Pi.single (e.symm ⟨τ, i⟩) 1) (hu₀ τ) _ (y.u τ i)).2 d1
    rw [hy₀]
    exact d2
  obtain ⟨t, ht⟩ := (frBor_calculus E H Dw l Xo c (CAt σ) y₀ y y).2.1 hx fun τ i =>
    ⟨cf τ i, isUnit_iff_ne_zero.2 (hdiag _), fun j hj => by
      by_contra hne
      have := (hs _ _ hne).2
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
      exact absurd hj (not_lt.2 this), hc τ i⟩
  refine ⟨t, ht, fun j => ?_⟩
  obtain ⟨⟨τ, i⟩, rfl⟩ := e.symm.surjective j
  rw [Equiv.apply_symm_apply]
  obtain ⟨a, ha, -, hac⟩ := ht.2.1 τ i
  have htan : IsTanAt y₀.x (y.u τ i) := by rw [← hx]; exact y.tan τ i
  have := (y₀.basis τ (y.u τ i) htan (y.eig τ i)).unique hac (hc τ i)
  rw [← ha, this]
  rfl

end GlobalTheory.FrameNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.TriangularFrameChangeOfTriangularPeriodStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open Formalism.L2.PjFree hiding relab toC
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif GlobalTheory.FrameNorm
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triangular_frame_change_of_triangular_period : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (k : Fin F.n) (P P₀ : (F.Di k).La →+ (Fin g → ℂ)) (h₀ : Matrix (Fin g) (Fin g) ℂ) (y y₀ : FrPt Xo c (CAt σ)), IsPeriod (F.Di k) (fun j => relab c σ (e j).1) P → IsPeriod (F.Di k) (fun j => relab c σ (e j).1) P₀ → (∀ a, P₀ a = h₀ *ᵥ P a) → (∀ j j', h₀ j j' ≠ 0 → (e j).1 = (e j').1 ∧ ((e j).2 : ℕ) ≤ (e j').2) → y.x = F.u k P → y₀.x = F.u k P₀ → (∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex k P z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) (y.u τ i)) → (∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex k P₀ z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) (y₀.u τ i)) → ∃ t : Ix Dw → (CAt σ)ˣ, FrBor t y₀ y ∧ ∀ j, toC (t (some (e j)) : CAt σ) = h₀ j j := by
  first | exact @GlobalTheory.FrameNorm.frBor_of_triangular_period | exact GlobalTheory.FrameNorm.frBor_of_triangular_period | (intros; apply GlobalTheory.FrameNorm.frBor_of_triangular_period <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.NonemptyLift
noncomputable section

namespace GlobalTheory.Reg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem MChart.nonempty_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (R : Type) [CommRing R] [Algebra c.F R] (f : Γ(Y.X, M.U) →+* R) (xF : Sp R ⟶ Xo.XF c), xF ≫ pullback.snd _ _ = spMap (algebraMap c.F R) → xF ≫ Y.j = spMap f ≫ M.hU.fromSpec → Nonempty (M.Lift f (xF ≫ pullback.fst _ _)) := by
  intro E _ _ _ H Dw l Xo c O _ β Y M R _ _ f xF h1 h2
  have hComp : SABCompSt := sabComp pullCubComp
  have hP : ∃ t' : SAB H (Sp R), Nonempty (SABMap t' Y.oF.t xF) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull xF Y.oF.t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨t', ⟨m'⟩⟩ := hP
  obtain ⟨m1, hm1⟩ := hComp _ _ _ _ _ _ _ _ _ _ Y.m0.toSABMap m'
  have key : ∀ g : Sp R ⟶ Y.X, xF ≫ Y.j = g → ∃ m2 : SABMap t' Y.t g, m2.φ = m'.φ ≫ Y.m.φ := by
    rintro g rfl
    exact hComp _ _ _ _ _ _ _ _ _ _ Y.m m'
  obtain ⟨m2, hm2⟩ := key _ h2
  exact ⟨⟨xF, rfl, h1, h2, t', m', m1, m2, hm1, hm2⟩⟩

end GlobalTheory.Reg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsFiniteMchartCover
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg

private theorem compactSpace_model {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
    (Y : Model Xo c β) : CompactSpace Y.X := by
  obtain ⟨N, i, hi, hs⟩ := Y.proj
  haveI := hi
  haveI : IsProper (PSpace.str O N) := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str O N
  haveI : QuasiCompact Y.s := by rw [← hs]; infer_instance
  exact QuasiCompact.compactSpace_of_compactSpace Y.s

private theorem exists_mChart_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] [IsNoetherianRing O] {β : O →+* c.F}
    (Y : Model Xo c β) (hP : PushInvertible Y.t.G Y.t.PP.L) (x : Y.X) : ∃ M : MChart Y, x ∈ M.U := by
  obtain ⟨U, hU, hxU, hdom, ⟨θ, hθ, hne⟩, n, v₀, ρ, hlie⟩ :=
    GlobalTheory.ModelChart.exists_chart_lieBasis_matrices E H Dw l Xo c O β Y hP x
  exact ⟨⟨U, hU, hdom, θ, hθ, hne, n, v₀, ρ, hlie⟩, hxU⟩

theorem exists_finite_mchart_cover :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] [IsNoetherianRing O] (β : O →+* c.F) (Y : Model Xo c β), PushInvertible Y.t.G Y.t.PP.L → ∃ (J : Type) (_ : Finite J) (M : J → MChart Y), ∀ x : Y.X, ∃ j, x ∈ (M j).U := by
  intro E _ _ _ H Dw l Xo c O _ _ β Y hP
  haveI := compactSpace_model Y
  choose M hM using exists_mChart_mem Y hP
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => ((M x).U : Set Y.X))
    (fun x => (M x).U.isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hM x⟩)
  refine ⟨t, inferInstance, fun j => M j.1, fun x => ?_⟩
  obtain ⟨j, hj, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
  exact ⟨⟨j, hj⟩, hx⟩

end GlobalTheory.Reg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsOpenImmersionOfSurj
noncomputable section

namespace GlobalTheory.Reg.ChartOpens

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem away_irreducible {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] {ϖ : O} (hϖ : Irreducible ϖ) : IsLocalization.Away ϖ K := by
  have hi := IsFractionRing.injective O K
  refine IsLocalization.Away.mk _ (IsUnit.mk0 _ (by simpa using hϖ.ne_zero)) (fun z => ?_)
    (fun a b h => ⟨0, by rw [hi h]⟩)
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) z
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero hb) hϖ
  refine ⟨n, a * ↑u⁻¹, ?_⟩
  have h1 : algebraMap O K ϖ ≠ 0 := by simpa using hϖ.ne_zero
  have h2 : algebraMap O K u * algebraMap O K ↑u⁻¹ = 1 := by rw [← map_mul]; simp
  have h3 : algebraMap O K u ≠ 0 := left_ne_zero_of_mul_eq_one h2
  rw [map_mul, map_mul, map_pow, eq_inv_of_mul_eq_one_right h2]
  field_simp

theorem exists_finset_basicOpen {A : Type} [CommRing A] [IsNoetherianRing A] (V : Set (PrimeSpectrum A))
    (hV : IsOpen V) (hne : V.Nonempty) :
    ∃ es : Finset A, es.Nonempty ∧ (∀ e ∈ es, e ≠ 0) ∧ ∀ p, p ∈ V ↔ ∃ e ∈ es, e ∉ p.asIdeal := by
  classical
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).1 hV.isClosed_compl
  obtain ⟨s, rfl⟩ := IsNoetherian.noetherian I
  have key : ∀ p, p ∈ V ↔ ∃ e ∈ s.filter (· ≠ 0), e ∉ p.asIdeal := by
    intro p
    have : p ∉ V ↔ (s : Set A) ⊆ p.asIdeal := by
      rw [← Set.mem_compl_iff, hI]
      exact (PrimeSpectrum.mem_zeroLocus _ _).trans Ideal.span_le
    constructor
    · intro hp
      obtain ⟨e, he, h⟩ := Set.not_subset.1 (fun h => this.2 h hp)
      exact ⟨e, Finset.mem_filter.2 ⟨he, fun h0 => h (h0 ▸ p.asIdeal.zero_mem)⟩, h⟩
    · rintro ⟨e, he, h⟩
      by_contra hp
      exact h (this.1 hp (Finset.mem_filter.1 he).1)
  obtain ⟨p, hp⟩ := hne
  obtain ⟨e, he, -⟩ := (key p).1 hp
  exact ⟨_, ⟨e, he⟩, fun e he => (Finset.mem_filter.1 he).2, key⟩

theorem isOpenImmersion_of_surj {O K A R : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
    [Algebra O K] [IsFractionRing O K] [CommRing A] [CommRing R] [Algebra K R] (α : O →+* A) (f : A →+* R)
    (hf : f.comp α = (algebraMap K R).comp (algebraMap O K)) (x : A) (hx : IsUnit (f x)) (hi : Function.Injective f)
    (hs : ∀ r : R, ∃ (a : A) (k : K) (N : ℕ), r * f x ^ N = algebraMap K R k * f a) :
    IsOpenImmersion (spMap f) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have := away_irreducible (K := K) hϖ
  have hfo : ∀ o, f (α o) = algebraMap K R (algebraMap O K o) := fun o => RingHom.congr_fun hf o
  letI := f.toAlgebra
  have : IsLocalization.Away (α ϖ * x) R := by
    refine IsLocalization.Away.mk _ ?_ (fun r => ?_) (fun a b h => ⟨0, by rw [hi h]⟩)
    · show IsUnit (f _)
      rw [map_mul, hfo]
      exact ((IsLocalization.Away.algebraMap_isUnit (S := K) ϖ).map _).mul hx
    · obtain ⟨a, k, N, h⟩ := hs r
      obtain ⟨n, o, ho⟩ := IsLocalization.Away.surj ϖ k
      refine ⟨N + n, α (o * ϖ ^ N) * x ^ n * a, ?_⟩
      show r * f _ ^ _ = f _
      have h2 : algebraMap K R k * f (α ϖ) ^ n = f (α o) := by
        rw [hfo, hfo, ← ho, map_mul, map_pow]
      simp only [map_mul, map_pow]
      rw [← h2]
      linear_combination (f (α ϖ) ^ (N + n) * f x ^ n) * h
  exact IsOpenImmersion.of_isLocalization (α ϖ * x)

theorem chart_opens {O K A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
    [Algebra O K] [IsFractionRing O K] [CommRing A] [IsDomain A] {X Z : Scheme.{0}} (s : X ⟶ Sp O) [Flat s]
    (g : Sp A ⟶ X) [IsOpenImmersion g] (α : O →+* A) (hα : g ≫ s = spMap α) (hft : α.FiniteType)
    (t : Z ⟶ Sp K) [Smooth t] (jQ : Z ⟶ pullback s (spMap (algebraMap O K))) [IsOpenImmersion jQ]
    (hd : Dense (Set.range jQ)) (hj : jQ ≫ pullback.snd _ _ = t) :
    ∃ es : Finset A, Function.Injective α ∧ es.Nonempty ∧ (∀ e ∈ es, e ≠ 0) ∧
      (∀ e ∈ es, ∀ (R : Type) [CommRing R] [Algebra K R] (f : A →+* R),
        f.comp α = (algebraMap K R).comp (algebraMap O K) → IsUnit (f e) →
          (∃ xF : Sp R ⟶ Z, xF ≫ t = spMap (algebraMap K R) ∧ xF ≫ jQ ≫ pullback.fst _ _ = spMap f ≫ g) ∧
          ∀ d : A, Function.Injective f → IsUnit (f d) →
            (∀ r : R, ∃ (a : A) (k : K) (N : ℕ), r * f (e * d) ^ N = algebraMap K R k * f a) → Algebra.Smooth K R) ∧
      ∀ (L : Type) [Field L] [Algebra K L] (f : A →+* L) (xF : Sp L ⟶ Z), xF ≫ t = spMap (algebraMap K L) →
        xF ≫ jQ ≫ pullback.fst _ _ = spMap f ≫ g →
          f.comp α = (algebraMap K L).comp (algebraMap O K) ∧ ∃ e ∈ es, f e ≠ 0 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have := away_irreducible (K := K) hϖ
  have hopen : IsOpenImmersion (spMap (algebraMap O K)) := IsOpenImmersion.of_isLocalization ϖ
  have hjs : (jQ ≫ pullback.fst _ _) ≫ s = t ≫ spMap (algebraMap O K) := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hj]
  have hflat : α.Flat := (HasRingHomProperty.Spec_iff (P := @Flat) (φ := CommRingCat.ofHom α)).1 (by
    show Flat (spMap α)
    rw [← hα]; infer_instance)
  have hinj : Function.Injective α := by
    letI := α.toAlgebra
    have : Module.Flat O A := hflat
    exact FaithfulSMul.algebraMap_injective O A
  have hN : IsNoetherianRing A := by
    letI := α.toAlgebra
    have : Algebra.FiniteType O A := hft
    exact Algebra.FiniteType.isNoetherianRing O A
  let j := jQ ≫ pullback.fst s (spMap (algebraMap O K))
  let V : Set (PrimeSpectrum A) := g ⁻¹' Set.range j
  have hV : IsOpen V := j.isOpenEmbedding.isOpen_range.preimage g.continuous
  have hne : V.Nonempty := by
    have h0 : g (⊥ : PrimeSpectrum A) ∈ Set.range (pullback.fst s (spMap (algebraMap O K))) := by
      rw [Scheme.Pullback.range_fst]
      refine ⟨(⊥ : PrimeSpectrum K), ?_⟩
      refine Eq.trans ?_ (Scheme.Hom.comp_apply g s _)
      rw [hα]
      refine PrimeSpectrum.ext ?_
      show Ideal.comap (algebraMap O K) ⊥ = Ideal.comap α ⊥
      rw [Ideal.comap_bot_of_injective _ hinj, Ideal.comap_bot_of_injective _ (IsFractionRing.injective O K)]
    obtain ⟨y, hy⟩ := h0
    obtain ⟨_, ⟨p, hp⟩, z, rfl⟩ := hd.inter_open_nonempty
      (pullback.fst s (spMap (algebraMap O K)) ⁻¹' Set.range g)
      (g.isOpenEmbedding.isOpen_range.preimage (Scheme.Hom.continuous _)) ⟨y, _, hy.symm⟩
    exact ⟨p, z, by rw [hp]; exact Scheme.Hom.comp_apply _ _ _⟩
  obtain ⟨es, h1, h2, h3⟩ := exists_finset_basicOpen V hV hne
  refine ⟨es, hinj, h1, h2, fun e he R _ _ f hf hu => ?_, fun L _ _ f xF hx1 hx2 => ⟨?_, ?_⟩⟩
  · have hr : Set.range (spMap f ≫ g) ⊆ Set.range j := by
      rintro _ ⟨p, rfl⟩
      rw [Scheme.Hom.comp_apply]
      refine (h3 (spMap f p)).2 ⟨e, he, fun h => ?_⟩
      exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ (show f e ∈ p.asIdeal from h) hu)
    let xF := IsOpenImmersion.lift j (spMap f ≫ g) hr
    have hx : xF ≫ j = spMap f ≫ g := IsOpenImmersion.lift_fac _ _ _
    have ht : xF ≫ t = spMap (algebraMap K R) := by
      rw [← cancel_mono (spMap (algebraMap O K)), Category.assoc, ← hjs, ← Category.assoc, hx, Category.assoc, hα,
        ← spMap_comp, ← spMap_comp, hf]
    refine ⟨⟨xF, ht, hx⟩, fun d hi hdu hs => ?_⟩
    have := isOpenImmersion_of_surj α f hf (e * d) (by rw [map_mul]; exact hu.mul hdu) hi hs
    have : IsOpenImmersion (xF ≫ j) := by rw [hx]; infer_instance
    have : IsOpenImmersion xF := IsOpenImmersion.of_comp xF j
    have : Smooth (spMap (algebraMap K R)) := by rw [← ht]; infer_instance
    exact RingHom.smooth_algebraMap.1 ((HasRingHomProperty.Spec_iff (P := @Smooth)).1 this)
  · have : spMap (f.comp α) = spMap ((algebraMap K L).comp (algebraMap O K)) := by
      rw [spMap_comp, spMap_comp, ← hα, ← Category.assoc, ← hx2, ← hx1, Category.assoc, hjs, Category.assoc]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective this)
  · obtain ⟨e, he, h⟩ := (h3 (spMap f (⊥ : PrimeSpectrum L))).1
      ⟨xF (⊥ : PrimeSpectrum L), (Scheme.Hom.comp_apply xF j _).symm.trans
        ((congrArg (fun φ : Sp L ⟶ X => φ (⊥ : PrimeSpectrum L)) hx2).trans (Scheme.Hom.comp_apply _ _ _))⟩
    exact ⟨e, he, fun h0 => h (show f e ∈ (⊥ : Ideal L) from h0)⟩

theorem moduli_basicOpens :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O c.F] [IsFractionRing O c.F] (Y : Model Xo c (algebraMap O c.F)) (M : MChart Y), ∃ (α : O →+* Γ(Y.X, M.U)) (es : Finset Γ(Y.X, M.U)), M.hU.fromSpec ≫ Y.s = spMap α ∧ α.FiniteType ∧ Function.Injective α ∧ es.Nonempty ∧ (∀ e ∈ es, e ≠ 0) ∧ (∀ e ∈ es, ∀ (R : Type) [CommRing R] [Algebra c.F R] (f : Γ(Y.X, M.U) →+* R), f.comp α = (algebraMap c.F R).comp (algebraMap O c.F) → IsUnit (f e) → (∃ xF : Sp R ⟶ Xo.XF c, xF ≫ pullback.snd _ _ = spMap (algebraMap c.F R) ∧ xF ≫ Y.j = spMap f ≫ M.hU.fromSpec) ∧ ∀ d : Γ(Y.X, M.U), Function.Injective f → IsUnit (f d) → (∀ r : R, ∃ (a : Γ(Y.X, M.U)) (k : c.F) (N : ℕ), r * f (e * d) ^ N = algebraMap c.F R k * f a) → Algebra.Smooth c.F R) ∧ ∀ (L : Type) [Field L] [Algebra c.F L] (f : Γ(Y.X, M.U) →+* L) (xF : Sp L ⟶ Xo.XF c), xF ≫ pullback.snd _ _ = spMap (algebraMap c.F L) → xF ≫ Y.j = spMap f ≫ M.hU.fromSpec → f.comp α = (algebraMap c.F L).comp (algebraMap O c.F) ∧ ∃ e ∈ es, f e ≠ 0 := by
  intro E _ _ _ H Dw l Xo c O _ _ _ _ _ Y M
  obtain ⟨α, h1, h2, -⟩ := (GlobalTheory.ModelPoints.model_points_charts E H Dw l Xo c O _ Y).2.2 M.U M.hU
  have := M.dom
  have := Y.flat
  have := Y.jQ_open
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth Dw.dim Xo.s
  have hg : IsOpenImmersion (X := Sp Γ(Y.X, M.U)) M.hU.fromSpec := inferInstanceAs (IsOpenImmersion M.hU.fromSpec)
  obtain ⟨es, h⟩ := chart_opens (A := Γ(Y.X, M.U)) Y.s M.hU.fromSpec α h1 h2
    (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) Y.jQ Y.jQ_dense Y.jQ_over
  exact ⟨α, es, h1, h2, h⟩

end GlobalTheory.Reg.ChartOpens
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsRingHomOfIsLieComb
noncomputable section

namespace GlobalTheory.Reg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem exists_ringHom_of_isLieComb {R O : Type} [CommRing R] [CommRing O] {G : Over (Sp R)} [GrpObj G]
    [IsCommMonObj G] (a : OAct O G) {n : ℕ} {v : Fin n → (epsR R ⟶ G)} (hv : IsLieBasis v)
    (ρ : O → Matrix (Fin n) (Fin n) R) (h : ∀ x j, IsLieComb (fun i => ρ x i j) v (v j ≫ a.act x)) :
    ∃ ρ' : O →+* Matrix (Fin n) (Fin n) R, ∀ x, ρ' x = ρ x := by
  classical
  let B := GlobalTheory.Serre.Lie.basis a hv
  refine ⟨(LinearMap.toMatrixAlgEquiv B).toRingEquiv.toRingHom.comp
    (Module.toModuleEnd R (S := O) (GlobalTheory.Serre.Lie a)), fun x => ?_⟩
  ext i j
  have h1 : IsLieComb (fun i => ρ x i j) (fun k => (B k).hom) (v j ≫ a.act x) := by
    simpa only [B, GlobalTheory.Serre.Lie.hom_basis] using h x j
  rw [GlobalTheory.Serre.Lie.isLieComb_iff] at h1
  have h2 : x • B j = ∑ k, ρ x k j • B k := by
    apply GlobalTheory.Serre.Lie.ext
    rw [GlobalTheory.Serre.Lie.hom_act_smul, ← h1, GlobalTheory.Serre.Lie.hom_basis]
  simp [LinearMap.toMatrixAlgEquiv_apply, h2, Finsupp.finsetSum_apply, Finsupp.single_apply]

theorem MChart.exists_ringHom_rho :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
      (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β)
      (M : MChart Y), ∃ ρ' : 𝓞 E →+* Matrix (Fin M.n) (Fin M.n) Γ(Y.X, M.U), ∀ a, ρ' a = M.ρ a := by
  intro E _ _ _ H Dw l Xo c O _ β Y M
  obtain ⟨_, _, _, _, _, hm⟩ :=
    sabPull Out.CubePf.cubePull (spMap (RingHom.id Γ(Y.X, M.U)) ≫ M.hU.fromSpec) Y.t
  obtain ⟨t', ⟨m⟩⟩ : ∃ t' : SAB H (Sp Γ(Y.X, M.U)),
      Nonempty (SABMap t' Y.t (spMap (RingHom.id Γ(Y.X, M.U)) ≫ M.hU.fromSpec)) :=
    ⟨_, ⟨hm.choose⟩⟩
  obtain ⟨v', -, hv', hρ⟩ := M.lie _ (RingHom.id _) t' m
  exact exists_ringHom_of_isLieComb t'.act hv' M.ρ hρ

end GlobalTheory.Reg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsModelChartGenericPointComponent
section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsModelChartGenericPointComponent
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
open scoped CategoryTheory.Obj

namespace GlobalTheory.GenericChart

theorem exists_sec_ne_zero_of_iso {X : Scheme.{0}} {A B : LB X} (hA : A.IsLB) (hB : B.IsLB) (h : LBIso A B)
    (s : A.Sec) (j : A.ι) (hj : s.f j ≠ 0) : ∃ (s' : B.Sec) (k : B.ι), s'.f k ≠ 0 := by
  obtain ⟨w, hw⟩ := LBIso.chartPull (chartPullId B) (chartPullPull A (𝟙 X) (𝟙 X) rfl) h.symm
  obtain ⟨s', hs'⟩ := sec_pull_down ((isGen_iff w).1 hw) hA hB s
  refine ⟨s', ?_⟩
  by_contra hn
  push Not at hn
  refine hj (fn_ext fun x hx => ?_)
  obtain ⟨k, hk⟩ := exists_chart hB x
  have e := hs' X (𝟙 X) x j k hx hk
  rw [hn k, gs_eq (𝟙 X) x _ hk 0, map_zero, map_zero, mul_zero, Category.comp_id] at e
  rw [e, gs_eq (𝟙 X) x _ hx 0, map_zero, map_zero]

theorem exists_secOn_of_isOpenImmersion {X₀ X : Scheme.{0}} (q : X₀ ⟶ X) [IsOpenImmersion q] (L : LB X)
    (V₀ : X₀.Opens) (V : X.Opens) (hV : V ≤ q.opensRange) (hV₀ : q ⁻¹ᵁ V ≤ V₀)
    (θ : ∀ J, Γ(X₀, V₀ ⊓ (L.pull q).U J)) (hθ : θ ∈ secOn (L.pull q) V₀) :
    ∃ θ' ∈ secOn L V, ∀ (z : X₀) (i : L.ι), q z ∈ V → z ∈ X₀.basicOpen (θ fun _ => i) →
      q z ∈ X.basicOpen (θ' i) := by
  have bij : ∀ W : X.Opens, W ≤ V → Function.Bijective (q.app W).hom := fun W hW =>
    have := q.isIso_app W (hW.trans hV)
    ConcreteCategory.bijective_of_isIso (q.app W)
  have le : ∀ i, q ⁻¹ᵁ (V ⊓ L.U i) ≤ V₀ ⊓ (L.pull q).U (fun _ => i) := fun i z hz => ⟨hV₀ hz.1, mem_pull.2 hz.2⟩
  choose θ' hθ' using fun i => (bij (V ⊓ L.U i) inf_le_left).2 (resG X₀ (le i) (θ fun _ => i))
  have val : ∀ i z, q z ∈ V ⊓ L.U i → gs q z _ (θ' i) = gs (𝟙 X₀) z _ (θ fun _ => i) := fun i z hz => by
    have e := gs_pull (𝟙 X₀) q z _ hz (θ' i)
    rw [Category.id_comp, hθ'] at e
    exact e.symm.trans (gs_res (𝟙 X₀) z (le i) hz _)
  refine ⟨θ', fun i j => (bij _ (inf_le_left.trans inf_le_left)).1 (fn_ext fun z hz => ?_), fun z i hz hb => ?_⟩
  · have hz' : q z ∈ V ⊓ L.U i ⊓ L.U j := hz
    refine (gs_pull (𝟙 X₀) q z _ hz' _).trans (Eq.trans ?_ (gs_pull (𝟙 X₀) q z _ hz' _).symm)
    have hm : (𝟙 X₀ : X₀ ⟶ X₀) z ∈ V₀ ⊓ (L.pull q).U (fun _ => i) ⊓ (L.pull q).U (fun _ => j) :=
      ⟨le i hz'.1, mem_pull.2 hz'.2⟩
    have e := congrArg (gs (𝟙 X₀) z _) (hθ (fun _ => i) (fun _ => j))
    rw [gs_res _ z _ hm, gs_mul _ z _ hm, gs_res _ z _ hm, gs_res _ z _ hm,
      gs_unit _ z ((L.pull q).U (fun _ => i) ⊓ (L.pull q).U (fun _ => j)) ⟨hm.1.2, hm.2⟩,
      gm_pull_g L q (𝟙 X₀) z _ _ hm.1.2 hm.2, Category.id_comp] at e
    rw [Category.id_comp, gs_res _ z _ hz', gs_mul _ z _ hz', gs_res _ z _ hz', gs_res _ z _ hz',
      gs_unit _ z (L.U i ⊓ L.U j) ⟨hz'.1.2, hz'.2⟩, val i z hz'.1, val j z ⟨hz'.1.1, hz'.2⟩]
    exact e
  · have hi : q z ∈ V ⊓ L.U i := ⟨hz, mem_pull.1 (X₀.basicOpen_le _ hb).2⟩
    show z ∈ q ⁻¹ᵁ X.basicOpen (θ' i)
    rw [Scheme.preimage_basicOpen]
    refine (congrArg (fun a => z ∈ X₀.basicOpen a) (hθ' i)).mpr ?_
    exact (X₀.basicOpen_res (θ fun _ => i) (homOfLE (le i)).op).ge ⟨hi, hb⟩

theorem exists_lift_of_isPreimmersion {X' X : Scheme.{0}} (j : X' ⟶ X) [IsPreimmersion j] {K : Type} [Field K]
    (y : Sp K ⟶ X) (ξ : X') (h : y (IsLocalRing.closedPoint K) = j ξ) : ∃ z : Sp K ⟶ X', z ≫ j = y := by
  obtain ⟨⟨p, φ⟩, hy⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective y
  have hp : p = j ξ := by
    rw [← h, ← hy]
    exact (X.fromSpecResidueField_apply p _).symm
  subst hp
  have : IsIso (j.residueFieldMap ξ) := by
    refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨(j.residueFieldMap ξ).hom.injective, fun a => ?_⟩
    obtain ⟨a, rfl⟩ := X'.residue_surjective ξ a
    obtain ⟨b, rfl⟩ := j.stalkMap_surjective ξ a
    exact ⟨X.residue _ b, congr($(Scheme.residue_residueFieldMap j ξ).hom b)⟩
  refine ⟨Spec.map (inv (j.residueFieldMap ξ) ≫ φ) ≫ X'.fromSpecResidueField ξ, ?_⟩
  rw [← hy, Scheme.SpecToEquivOfField_symm_apply, Category.assoc,
    ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Category.assoc, ← Spec.map_comp,
    IsIso.hom_inv_id_assoc]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem eq_genPt_of_specializes (Z : Comp Xo c) {ξ : Xo.XF c} (h : ξ ⤳ genPt Z) : ξ = genPt Z := by
  have h1 : closure {genPt Z} = (Z : Set (Xo.XF c)) :=
    (Z.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ Z.2))
  have h2 : (Z : Set (Xo.XF c)) ⊆ closure {ξ} := h1 ▸ specializes_iff_closure_subset.1 h
  have h3 : closure {ξ} ⊆ (Z : Set (Xo.XF c)) := Z.2.2 isIrreducible_singleton.closure h2
  exact (h.antisymm (specializes_iff_closure_subset.2 (h1 ▸ h3))).eq

theorem exists_section (hT : Out.SecTwistSt) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Z : Comp Xo c)
    [IsNoetherianRing (𝓞 c.F)] [IsFractionRing (𝓞 c.F) c.F] :
    ∃ V : Y.X.Opens, Y.j (genPt Z) ∈ V ∧ ∃ θ ∈ secOn Y.t.PP.L (Y.t.G.hom ⁻¹ᵁ V),
      ∀ y ∈ V, ∃ (g : Y.t.G.left) (i : Y.t.PP.L.ι), Y.t.G.hom g = y ∧ g ∈ Y.t.G.left.basicOpen (θ i) := by
  have := projProper _ _ _ Y.proj
  have : IsLocallyNoetherian Y.X := LocallyOfFiniteType.isLocallyNoetherian Y.s
  have : GlobalTheory.IsNormalScheme Y.X := GlobalTheory.IsNormalScheme.of_pred Y.normal
  obtain ⟨W, hxW, hW⟩ := ModelChart.exists_open_isDomain Y.X (Y.j (genPt Z))
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ := Y.X.isBasis_affineOpens.exists_subset_of_mem_open hxW W.isOpen
  have hU : IsAffineOpen U := hU
  have := hW U hxU hUW
  let R : Type := Γ(Y.X, U)
  let K : Type := FractionRing R
  have b₁ : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 c.F)) (S := c.F)
  have b₂ : Flat (spMap (algebraMap (𝓞 c.F) c.F)) := by
    have : Module.Flat (𝓞 c.F) c.F := IsLocalization.flat c.F (nonZeroDivisors (𝓞 c.F))
    exact (HasRingHomProperty.Spec_iff (P := @Flat)).2 (RingHom.flat_algebraMap_iff.2 this)
  have := Y.jQ_open
  have a₁ : IsPreimmersion (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))) :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip b₁
  have a₂ : Flat (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))) :=
    MorphismProperty.of_isPullback (P := @Flat) (IsPullback.of_hasPullback _ _).flip b₂
  have : IsPreimmersion Y.j := by unfold Model.j; infer_instance
  have : Flat Y.j := by unfold Model.j; infer_instance

  have hgen : hU.fromSpec (⊥ : PrimeSpectrum R) = Y.j (genPt Z) := by
    obtain ⟨p, hp⟩ : Y.j (genPt Z) ∈ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; exact hxU
    have s₀ : (⊥ : PrimeSpectrum R) ⤳ p := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
    have s₁ : hU.fromSpec (⊥ : PrimeSpectrum R) ⤳ Y.j (genPt Z) := hp ▸ s₀.map hU.fromSpec.continuous
    obtain ⟨ξ, h₁, h₂⟩ := Flat.generalizingMap Y.j s₁
    rw [← h₂, eq_genPt_of_specializes Z h₁]
  have hK : spMap (algebraMap R K) (IsLocalRing.closedPoint K) = (⊥ : PrimeSpectrum R) := by
    apply PrimeSpectrum.ext
    show Ideal.comap (algebraMap R K) (IsLocalRing.maximalIdeal K) = ⊥
    rw [IsLocalRing.maximalIdeal_eq_bot]
    exact (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R K)
  obtain ⟨z, hz⟩ := exists_lift_of_isPreimmersion Y.j (spMap (algebraMap R K) ≫ hU.fromSpec) (genPt Z)
    (by rw [← hgen, ← hK]; rfl)
  obtain ⟨t₀, ⟨m₀⟩⟩ := (ModelPoints.model_points_charts E H Dw l Xo c _ _ Y).2.1 (Sp R) hU.fromSpec
  obtain ⟨t', ⟨m₂⟩⟩ : ∃ t' : SAB H (Sp K), Nonempty (SABMap t' t₀ (spMap (algebraMap R K))) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap (algebraMap R K)) t₀
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨n, hn⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m₀ m₂
  have cancel : ∀ (p : Sp K ⟶ Y.X) (_ : p = z ≫ Y.j) (n : SABMap t' Y.t p),
      Nonempty (SABMap t' Y.oF.t z) := by
    intro p hp n; subst hp
    exact ⟨(sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ Y.m n).choose⟩
  obtain ⟨m₃⟩ := cancel _ hz.symm n
  obtain ⟨b, hb⟩ := globalSections_rank_one_fibre hT amplePt Y.oF m₃
  obtain ⟨k, hk⟩ : ∃ k, b.f k ≠ 0 := by
    by_contra h0
    push Not at h0
    obtain ⟨a, -, ha⟩ := hb b
    exact zero_ne_one ((ha 0 fun i => by rw [h0, mul_zero]).trans (ha 1 fun i => by rw [h0, mul_zero]).symm)
  obtain ⟨w, hw, -⟩ := n.lin
  have iso : LBIso t'.PP.L ((Y.t.PP.L.pull m₀.φ).pull m₂.φ) := LBIso.chartPull (chartPullId _) (chartPullLinComb Y.t.PP.L m₀.φ (K := PUnit) (fun _ => m₂.φ)
    (fun _ => n.φ) (fun _ => 1) (𝟙 _) (fun _ => by rw [Category.id_comp]; exact hn.symm)) ⟨w, hw⟩
  have hL₀ := LB.isLB_pull Y.t.PP.isLB m₀.φ
  obtain ⟨h, h0, θ, hθ, nz⟩ := SecSpread.main R t₀.G t₀.semi _ hL₀ K _ m₂.φ _ m₂.cart.1
    (exists_sec_ne_zero_of_iso t'.PP.isLB (LB.isLB_pull hL₀ _) iso b k hk)
  have : IsOpenImmersion m₀.φ :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) m₀.cart.1.flip inferInstance
  have pre : ∀ p : Sp R, hU.fromSpec p ∈ Y.X.basicOpen h ↔ p ∈ PrimeSpectrum.basicOpen h := fun p =>
    SetLike.ext_iff.1 (hU.fromSpec_preimage_basicOpen h) p
  have sq : ∀ g, Y.t.G.hom (m₀.φ g) = hU.fromSpec (t₀.G.hom g) := fun g => congr($(m₀.cart.1.w) g)
  have rg : ∀ y ∈ Y.X.basicOpen h, ∃ p : Sp R, hU.fromSpec p = y := fun y hy => by
    show y ∈ Set.range hU.fromSpec
    rw [hU.range_fromSpec]; exact Y.X.basicOpen_le h hy
  obtain ⟨θ', hθ', nz'⟩ := exists_secOn_of_isOpenImmersion m₀.φ Y.t.PP.L _ (Y.t.G.hom ⁻¹ᵁ Y.X.basicOpen h)
    (fun g hg => by
      obtain ⟨p, hp⟩ := rg _ hg
      obtain ⟨g', h₁, -⟩ := Scheme.exists_preimage_of_isPullback m₀.cart.1 g p hp.symm
      exact ⟨g', h₁⟩)
    (fun g hg => (pre _).1 (sq g ▸ hg)) θ hθ
  refine ⟨Y.X.basicOpen h, ?_, θ', hθ', fun y hy => ?_⟩
  · rw [← hgen]
    exact (pre _).2 h0
  · obtain ⟨p, rfl⟩ := rg y hy
    obtain ⟨g, i, rfl, hg⟩ := nz p ((pre p).1 hy)
    exact ⟨m₀.φ g, i PUnit.unit, sq g, nz' g _ (show Y.t.G.hom (m₀.φ g) ∈ _ from sq g ▸ hy) hg⟩


open ModelChart in
theorem exists_chart_genPt : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Z : Comp Xo c), ∃ M : MChart Y, Y.j (genPt Z) ∈ M.U := by
  intro hT E _ _ _ H Dw l Xo c Y Z
  have := c.fin
  have : NumberField c.F := {}
  have := projProper _ _ _ Y.proj
  have : IsLocallyNoetherian Y.X := LocallyOfFiniteType.isLocallyNoetherian Y.s
  have : GlobalTheory.IsNormalScheme Y.X := GlobalTheory.IsNormalScheme.of_pred Y.normal
  have := Y.t.semi.smooth
  obtain ⟨W, hxW, hW⟩ := exists_open_isDomain Y.X (Y.j (genPt Z))
  obtain ⟨V, hxV, θ, hθ, nz⟩ := exists_section hT Y Z
  obtain ⟨U, hU, hxU, hUW, n, v₀, hv⟩ := GlobalTheory.exists_affine_lieBasis_baseChange Y.X Y.t.G _ (W ⊓ V) ⟨hxW, hxV⟩
  have hUV : U ≤ V := hUW.trans inf_le_right
  have nz' : ∀ y ∈ U, ∃ (g : Y.t.G.left) (i : Y.t.PP.L.ι), Y.t.G.hom g = y ∧ g ∈ Y.t.G.left.basicOpen
      (resG Y.t.G.left (inf_le_inf_right _ (Y.t.G.hom.preimage_mono hUV)) (θ i)) := fun y hy => by
    obtain ⟨g, i, rfl, hg⟩ := nz y (hUV hy)
    refine ⟨g, i, rfl, ?_⟩
    show g ∈ Y.t.G.left.basicOpen (Y.t.G.left.presheaf.map (homOfLE _).op (θ i))
    rw [Scheme.basicOpen_res]
    exact ⟨⟨hy, (Y.t.G.left.basicOpen_le _ hg).2⟩, hg⟩
  obtain ⟨t₀, ⟨m₀⟩⟩ := (GlobalTheory.ModelPoints.model_points_charts E H Dw l Xo c _ _ Y).2.1 (Sp Γ(Y.X, U)) hU.fromSpec
  have c₀ : IsGrpPullback t₀.G Y.t.G (spMap (RingHom.id Γ(Y.X, U)) ≫ hU.fromSpec) m₀.φ := by
    have e : spMap (RingHom.id Γ(Y.X, U)) = 𝟙 _ := Spec.map_id _
    rw [e, Category.id_comp]
    exact m₀.cart
  obtain ⟨u, hu, hb⟩ := hv _ (RingHom.id _) t₀.G m₀.φ c₀
  simp only [spMap_dualMapR_id, Category.id_comp] at hu
  have ex : ∀ a j, ∃ r : Fin n → Γ(Y.X, U), IsLieComb r u (u j ≫ t₀.act.act a) := fun a j =>
    have := t₀.act.hom a
    (hb.2 _ (isTangent_comp_hom (hb.1 j) _)).exists
  choose r hr using ex
  refine ⟨⟨U, hU, hW U hxU (hUW.trans inf_le_left), _, res_mem_secOn _ (Y.t.G.hom.preimage_mono hUV) hθ, nz', n, v₀,
    fun a i j => r a j i, fun R' _ f t' m => ?_⟩, hxU⟩
  obtain ⟨v', hv', hb'⟩ := hv R' f t'.G m.φ m.cart
  refine ⟨v', hv', hb', fun a j => ?_⟩
  have hp := m₀.cart.1
  let F : t'.G.left ⟶ t₀.G.left := hp.lift m.φ (t'.G.hom ≫ spMap f) (by rw [m.cart.1.w, Category.assoc])
  have hF : F ≫ m₀.φ = m.φ := hp.lift_fst _ _ _
  have hw : F ≫ t₀.G.hom = t'.G.hom ≫ spMap f := hp.lift_snd _ _ _
  have hc : IsGrpPullback t'.G t₀.G (spMap f) F := m₀.cart.cancel (hF ▸ m.cart) hw
  have lies : ∀ (w' : epsR R' ⟶ t'.G) (w : epsR Γ(Y.X, U) ⟶ t₀.G),
      w'.left ≫ m.φ = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ w.left ≫ m₀.φ →
      w'.left ≫ F = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ w.left := fun w' w h => by
    apply hp.hom_ext
    · rw [Category.assoc, hF, h, Category.assoc]
    · rw [Category.assoc, hw, ← Category.assoc, Over.w, Category.assoc, Over.w]
      exact (GlobalTheory.LieCombBaseChange.dualMap_over f).symm
  refine (GlobalTheory.lieComb_baseChange _ _ f t₀.G t'.G F hc n u _ (r a j) v' _
    (fun k => lies _ _ (by rw [hv', hu])) (hr a j)).1 (lies _ _ ?_)
  rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, m.act, m₀.act, ← Category.assoc, hv',
    ← Category.assoc (u j).left, hu, Category.assoc]

end GlobalTheory.GenericChart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsModelChartGenericPointComponentStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_modelChart_genericPoint_component : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Z : Comp Xo c), ∃ M : MChart Y, Y.j (genPt Z) ∈ M.U := by
  first | exact @GlobalTheory.GenericChart.exists_chart_genPt | exact GlobalTheory.GenericChart.exists_chart_genPt | (intros; apply GlobalTheory.GenericChart.exists_chart_genPt <;> assumption)
end
end
