module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AppellHumbertUnifTangentWeilPairing

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmCurveBaseChangeComp
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmCurveBaseChangeComp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.EllComp

variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R'']

theorem lbIso_pull_comp {X X' X'' : Scheme.{0}} {L : LB X} {L' : LB X'} {φ : X' ⟶ X} (h : LBIso (L.pull φ) L')
    (ψ : X'' ⟶ X') : LBIso (L.pull (ψ ≫ φ)) (L'.pull ψ) :=
  LBIso.chartPull (chartPullSame L _ _ _ ψ fun _ => rfl) (Geo.Tor.chartPullPull L' ψ ψ rfl) h

theorem dualMapR_comp (f : R →+* R') (g : R' →+* R'') :
    spMap (Chart.dualMapR g) ≫ spMap (Chart.dualMapR f) = spMap (Chart.dualMapR (g.comp f)) := by
  refine (spMap_comp_spMap _ _).trans ?_
  congr 1
  refine RingHom.ext fun a => ?_
  ext <;> simp [Chart.dualMapR]

theorem isPolFibre_comp {f : R →+* R'} {g : R' →+* R''} {P : Out.PolAV (Sp R)} {P' : Out.PolAV (Sp R')}
    {P'' : Out.PolAV (Sp R'')} {φ : P'.A.left ⟶ P.A.left} {ψ : P''.A.left ⟶ P'.A.left}
    (h : IsPolFibre f P P' φ) (h' : IsPolFibre g P' P'' ψ) : IsPolFibre (g.comp f) P P'' (ψ ≫ φ) :=
  ⟨h'.1.trans h.1, (h'.2.1.comp h.2.1).congr (spMap_comp_spMap _ _) rfl,
    LBIso.trans (pull_isLB P.isLB _) (pull_isLB P'.isLB _) P''.isLB (lbIso_pull_comp h.2.2 ψ) h'.2.2⟩

theorem isVecOver_comp {f : R →+* R'} {g : R' →+* R''} {A : Over (Sp R)} {A' : Over (Sp R')} {A'' : Over (Sp R'')}
    {φ : A'.left ⟶ A.left} {ψ : A''.left ⟶ A'.left} {v : epsR R ⟶ A} {v' : epsR R' ⟶ A'} {v'' : epsR R'' ⟶ A''}
    (h : IsVecOver f φ v v') (h' : IsVecOver g ψ v' v'') : IsVecOver (g.comp f) (ψ ≫ φ) v v'' := by
  unfold IsVecOver at *
  rw [← Category.assoc, h', Category.assoc, h, ← Category.assoc]
  exact congrArg (· ≫ v.left) (dualMapR_comp f g)

theorem exists_isPolFibre_lift {f : R →+* R'} {g : R' →+* R''} {P : Out.PolAV (Sp R)} {P' : Out.PolAV (Sp R')}
    {P'' : Out.PolAV (Sp R'')} {φ : P'.A.left ⟶ P.A.left} {χ : P''.A.left ⟶ P.A.left}
    (h : IsPolFibre f P P' φ) (n : IsPolFibre (g.comp f) P P'' χ) :
    ∃ ψ : P''.A.left ⟶ P'.A.left, ψ ≫ φ = χ ∧ IsPolFibre g P' P'' ψ := by
  have n' : IsGrpPullback P''.A P.A (spMap g ≫ spMap f) χ := n.2.1.congr (spMap_comp_spMap _ _).symm rfl
  have w : χ ≫ P.A.hom = (P''.A.hom ≫ spMap g) ≫ spMap f := n'.1.w.trans (Category.assoc _ _ _).symm
  have e : h.2.1.1.lift _ _ w ≫ φ = χ := h.2.1.1.lift_fst _ _ w
  refine ⟨h.2.1.1.lift _ _ w, e, n.1.trans h.1.symm,
    h.2.1.cancel (n'.congr rfl e.symm) (h.2.1.1.lift_snd _ _ w), ?_⟩
  refine LBIso.trans (pull_isLB P'.isLB _) (pull_isLB P.isLB _) P''.isLB (lbIso_pull_comp h.2.2 _).symm ?_
  rw [e]
  exact n.2.2

theorem isVecOver_cancel {f : R →+* R'} {g : R' →+* R''} {A : Over (Sp R)} {A' : Over (Sp R')} {A'' : Over (Sp R'')}
    {φ : A'.left ⟶ A.left} {ψ : A''.left ⟶ A'.left} {v : epsR R ⟶ A} {v' : epsR R' ⟶ A'} {v'' : epsR R'' ⟶ A''}
    (hφ : IsPullback φ A'.hom A.hom (spMap f)) (hψ : IsPullback ψ A''.hom A'.hom (spMap g))
    (h : IsVecOver f φ v v') (n : IsVecOver (g.comp f) (ψ ≫ φ) v v'') : IsVecOver g ψ v' v'' := by
  obtain ⟨w, hw, -⟩ := existsUnique_isVecOver hψ v'
  have hp : IsPullback (ψ ≫ φ) A''.hom A.hom (spMap (g.comp f)) := by
    rw [← spMap_comp_spMap]
    exact hψ.paste_horiz hφ
  rw [(existsUnique_isVecOver hp v).unique n (isVecOver_comp h hw)]
  exact hw

theorem isLieNormSq_iff {f : R →+* R'} {P : Out.PolAV (Sp R)} {P' : Out.PolAV (Sp R')} {φ : P'.A.left ⟶ P.A.left}
    {v : epsR R ⟶ P.A} {v' : epsR R' ⟶ P'.A} (h : IsPolFibre f P P' φ) (hv : IsVecOver f φ v v') (σ : R' →+* ℂ)
    (r : ℝ) : IsLieNormSq P' v' σ r ↔ IsLieNormSq P v (σ.comp f) r := by
  constructor
  · rintro ⟨Q, ψ, w, u, Hm, χ, z, h₁, h₂, h₃⟩
    exact ⟨Q, ψ ≫ φ, w, u, Hm, χ, z, isPolFibre_comp h h₁, isVecOver_comp hv h₂, h₃⟩
  · rintro ⟨Q, ψ₀, w, u, Hm, χ, z, h₁, h₂, h₃⟩
    obtain ⟨ψ, rfl, hψ⟩ := exists_isPolFibre_lift h h₁
    exact ⟨Q, ψ, w, u, Hm, χ, z, hψ, isVecOver_cancel h.2.1.1 hψ.2.1.1 hv h₂, h₃⟩

theorem ellMap_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (ω : R) (C : Ell H R ω) (R' : Type) [CommRing R'] (ω' : R') (C' : Ell H R' ω') (f : R →+* R') (φ : C'.P.A.left ⟶ C.P.A.left), EllMap C' C f φ → (∀ (R'' : Type) [CommRing R''] (ω'' : R'') (C'' : Ell H R'' ω'') (f' : R' →+* R'') (φ' : C''.P.A.left ⟶ C'.P.A.left), EllMap C'' C' f' φ' → EllMap C'' C (f'.comp f) (φ' ≫ φ)) ∧ (∀ σ : R' →+* ℂ, C.IsPrincipalAt (σ.comp f) → C'.IsPrincipalAt σ) ∧ ∀ (σ : R' →+* ℂ) (r : ℝ), Out.PolBaseChangeSt → (IsLieNormSq C'.P C'.v σ r ↔ IsLieNormSq C.P C.v (σ.comp f) r) := by
  intro E _ _ _ H R _ ω C R' _ ω' C' f φ h
  refine ⟨fun R'' _ ω'' C'' f' φ' h' => ⟨?_, isPolFibre_comp h.2.1 h'.2.1, isVecOver_comp h.2.2.1 h'.2.2.1, fun a => ?_⟩,
    fun σ hC Q ψ hψ => hC Q (ψ ≫ φ) (isPolFibre_comp h.2.1 hψ), fun σ r _ => isLieNormSq_iff h.2.1 h.2.2.1 σ r⟩
  · rw [RingHom.comp_apply, h.1, h'.1]
  · rw [← Category.assoc, h'.2.2.2 a, Category.assoc, h.2.2.2 a, Category.assoc]

end GlobalTheory.CM.EllComp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmCurveBaseChangeCompStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

theorem _root_.GlobalTheory.T.cmCurveBaseChange_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (ω : R) (C : Ell H R ω) (R' : Type) [CommRing R'] (ω' : R') (C' : Ell H R' ω') (f : R →+* R') (φ : C'.P.A.left ⟶ C.P.A.left), EllMap C' C f φ → (∀ (R'' : Type) [CommRing R''] (ω'' : R'') (C'' : Ell H R'' ω'') (f' : R' →+* R'') (φ' : C''.P.A.left ⟶ C'.P.A.left), EllMap C'' C' f' φ' → EllMap C'' C (f'.comp f) (φ' ≫ φ)) ∧ (∀ σ : R' →+* ℂ, C.IsPrincipalAt (σ.comp f) → C'.IsPrincipalAt σ) ∧ ∀ (σ : R' →+* ℂ) (r : ℝ), Out.PolBaseChangeSt → (IsLieNormSq C'.P C'.v σ r ↔ IsLieNormSq C.P C.v (σ.comp f) r) := by
  first | exact @GlobalTheory.CM.EllComp.ellMap_comp | exact GlobalTheory.CM.EllComp.ellMap_comp | (intros; apply GlobalTheory.CM.EllComp.ellMap_comp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsMonHomFactorOfFlatSurjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory

theorem _root_.GlobalTheory.exists_monHom_factor_of_flat_surjective : ∀ (S : Scheme.{0}) (G G' G'' : Over S) [GrpObj G] [GrpObj G'] [GrpObj G''] (Φ : G ⟶ G') (f : G ⟶ G''), IsMonHom Φ → IsMonHom f → Flat Φ.left → Surjective Φ.left → QuasiCompact Φ.left → (∀ (T : Over S) (x : T ⟶ G), x ≫ Φ = 1 → x ≫ f = 1) → (∃ ψ : G' ⟶ G'', IsMonHom ψ ∧ Φ ≫ ψ = f) ∧ Epi Φ := by
  intro S G G' G'' _ _ _ Φ f hΦ hf hflat hsurj hqc hker
  haveI := hΦ
  haveI := hf
  haveI : EffectiveEpi Φ := _root_.GlobalTheory.CosetQuotient.effectiveEpi_of_left Φ
  haveI : Flat (Φ ⊗ₘ Φ).left := _root_.GlobalTheory.CosetQuotient.flat_tensorHom Φ Φ
  haveI : Surjective (Φ ⊗ₘ Φ).left := _root_.GlobalTheory.CosetQuotient.surjective_tensorHom Φ Φ
  haveI : QuasiCompact (Φ ⊗ₘ Φ).left := _root_.GlobalTheory.CosetQuotient.quasiCompact_tensorHom Φ Φ
  haveI : EffectiveEpi (Φ ⊗ₘ Φ) := _root_.GlobalTheory.CosetQuotient.effectiveEpi_of_left _
  have hcompat : ∀ {Z : Over S} (g₁ g₂ : Z ⟶ G), g₁ ≫ Φ = g₂ ≫ Φ → g₁ ≫ f = g₂ ≫ f := by
    intro Z g₁ g₂ h
    have h1 : (g₁ / g₂) ≫ Φ = 1 := by
      rw [GrpObj.div_comp, h, div_self']
    have h2 := hker Z _ h1
    rwa [GrpObj.div_comp, div_eq_one] at h2
  refine ⟨⟨EffectiveEpi.desc Φ f hcompat, ⟨?_, ?_⟩, EffectiveEpi.fac Φ f hcompat⟩, inferInstance⟩
  · rw [← IsMonHom.one_hom (f := Φ), Category.assoc, EffectiveEpi.fac, IsMonHom.one_hom]
  · rw [← cancel_epi (Φ ⊗ₘ Φ), ← Category.assoc, ← IsMonHom.mul_hom (f := Φ), Category.assoc,
      EffectiveEpi.fac, IsMonHom.mul_hom, ← Category.assoc, tensorHom_comp_tensorHom, EffectiveEpi.fac]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LinearIndependentOfIsLieBasis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.LieMetric

section Linear

variable {K : Type} [Field K] {g : ℕ}

def ofGram (G : (K →+* ℂ) → Matrix (Fin g) (Fin g) ℂ) (hG : ∀ s, (G s).PosDef) : HermFam K (Fin g → K) where
  form s c c' := star (s ∘ c) ⬝ᵥ (G s).mulVec (s ∘ c')
  add_right s x y z := by
    rw [show s ∘ (y + z) = s ∘ y + s ∘ z from funext fun i => map_add s _ _, Matrix.mulVec_add, dotProduct_add]
  smul_right s a x y := by
    rw [show s ∘ (a • y) = s a • (s ∘ y) from funext fun i => map_mul s _ _, Matrix.mulVec_smul, dotProduct_smul,
      smul_eq_mul]
  conj_symm s x y := by
    change star _ = _
    rw [← Matrix.star_dotProduct, Matrix.star_mulVec, (hG s).isHermitian.eq, Matrix.dotProduct_mulVec]
  posDef s n v hv := by
    letI : Algebra K ℂ := s.toAlgebra
    have h1 : LinearIndependent ℂ (fun i => algebraMap K ℂ ∘ v i) := linearIndependent_algebraMap_comp_iff.2 hv
    have h2 := (hG s).conjTranspose_mul_mul_same (B := (Matrix.of fun i => s ∘ v i).transpose)
      (Matrix.mulVec_injective_iff.2 h1)
    convert h2 using 1
    ext i j
    rw [Matrix.mul_assoc]
    rfl

theorem ofGram_single (G : (K →+* ℂ) → Matrix (Fin g) (Fin g) ℂ) (hG : ∀ s, (G s).PosDef) (s : K →+* ℂ) (i j : Fin g) :
    (ofGram G hG).form s (Pi.single i 1) (Pi.single j 1) = G s i j := by
  have e : ∀ i : Fin g, s ∘ (Pi.single i 1 : Fin g → K) = Pi.single i 1 := fun i => by
    ext k
    by_cases h : k = i <;> simp [h]
  simp [ofGram, e, ← Pi.single_star]

theorem form_sum_right (h : HermFam K (Fin g → K)) (s : K →+* ℂ) (x y : Fin g → K) :
    h.form s x y = ∑ j, s (y j) * h.form s x (Pi.single j 1) := by
  let f : (Fin g → K) →+ ℂ := AddMonoidHom.mk' (h.form s x) (h.add_right s x)
  have e : y = ∑ j, y j • Pi.single j (1 : K) := pi_eq_sum_univ' y
  refine (congrArg f e).trans ((map_sum f _ _).trans (Finset.sum_congr rfl fun j _ => h.smul_right s _ _ _))

theorem ext_single {h h' : HermFam K (Fin g → K)}
    (e : ∀ s i j, h.form s (Pi.single i 1) (Pi.single j 1) = h'.form s (Pi.single i 1) (Pi.single j 1)) : h = h' := by
  have e1 : ∀ s i y, h.form s (Pi.single i 1) y = h'.form s (Pi.single i 1) y := fun s i y => by
    rw [form_sum_right h, form_sum_right h']
    simp only [e]
  have e2 : h.form = h'.form := by
    funext s x y
    rw [form_sum_right h, form_sum_right h']
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← h.conj_symm, ← h'.conj_symm, e1]
  cases h
  cases h'
  congr

theorem posDef_gram {n : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    (hp : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) {W : Fin n → Fin g → ℂ}
    (hW : LinearIndependent ℂ W) : (Matrix.of fun i j => (Real.pi : ℂ) * hermForm Hm (W j) (W i)).PosDef := by
  have h1 : Hm.PosDef := Matrix.PosDef.of_dotProduct_mulVec_pos hH fun x hx =>
    Complex.pos_iff.2 ⟨by simpa using hp (star x) (by simpa using hx), (hH.im_star_dotProduct_mulVec_self x).symm⟩
  have h2 := (h1.mul_mul_conjTranspose_same (B := Matrix.of W) (Matrix.vecMul_injective_iff.2 hW)).transpose.smul
    (a := (Real.pi : ℂ)) (by exact_mod_cast Real.pi_pos)
  rw [Matrix.mul_assoc] at h2
  exact h2

end Linear

theorem linearIndependent_of_isLieBasis {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g n : ℕ} (u : HolUnif A L g)
    (hu : ∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) {v : Fin n → (epsR ℂ ⟶ A)} (hv : IsLieBasis v)
    {W : Fin n → Fin g → ℂ} (hW : ∀ i, u.IsDiff (W i) (v i)) : LinearIndependent ℂ W := by
  have key : ∀ c : Fin n → ℂ, ∃ w, IsTangent w ∧ IsLieComb c v w ∧ u.IsDiff (∑ i, c i • W i) w := fun c => by
    have h := UnifDifferential.isDiff_prod u (fun i => c i • W i) _
      (fun i => Chart.isTan_scale (c i) ((Chart.isTan_iff _).2 (hv.1 i)))
      (fun i => UnifDifferential.isDiff_scale u (hW i) (c i))
    exact ⟨_, (Chart.isTan_iff _).1 h.1, (Chart.isLieComb_iff c v _).2 rfl, h.2⟩
  rw [Fintype.linearIndependent_iff]
  intro c hc
  obtain ⟨w, h1, h2, h3⟩ := key c
  obtain ⟨w', h1', h2', h3'⟩ := key 0
  rw [hc] at h3
  simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero] at h3'
  obtain rfl := (hu 0).unique ⟨h1, h3⟩ ⟨h1', h3'⟩
  exact congrFun ((hv.2 w h1).unique h2 h2')

theorem hermForm_eq (hU : ThetaUnifAV) {R : Type} [CommRing R] {P : Out.PolAV (Sp R)} {s : R →+* ℂ}
    {Q Q' : Out.PolAV (Sp ℂ)} {ψ : Q.A.left ⟶ P.A.left} {ψ' : Q'.A.left ⟶ P.A.left} (h : IsPolFibre s P Q ψ)
    (h' : IsPolFibre s P Q' ψ') {g g' : ℕ} {u : HolUnif Q.A Q.L g} {u' : HolUnif Q'.A Q'.L g'}
    {Hm : Matrix (Fin g) (Fin g) ℂ} {Hm' : Matrix (Fin g') (Fin g') ℂ} {χ : u.Λ → ℂ} {χ' : u'.Λ → ℂ}
    (hu : u.IsAH Hm χ) (hu' : u'.IsAH Hm' χ') {I : Type} {v : I → (epsR R ⟶ P.A)} (hv : ∀ i, IsTangent (v i))
    {w : I → (epsR ℂ ⟶ Q.A)} {w' : I → (epsR ℂ ⟶ Q'.A)} {W : I → Fin g → ℂ} {W' : I → Fin g' → ℂ}
    (hw : ∀ i, IsVecOver s ψ (v i) (w i) ∧ u.IsDiff (W i) (w i))
    (hw' : ∀ i, IsVecOver s ψ' (v i) (w' i) ∧ u'.IsDiff (W' i) (w' i)) (i j : I) :
    hermForm Hm (W i) (W j) = hermForm Hm' (W' i) (W' j) := by
  obtain ⟨e, he, heψ⟩ := grpPullback_iso h.2.1 h'.2.1
  obtain ⟨-, -, -, -, t1, t2, -⟩ := AHWeil.tangent_and_weil_of_isAH hU Q' g' u' Hm' χ' hu'
  obtain ⟨F, hF, -, hd, -⟩ := HomLinear.exists_linear_of_isMonHom Q.A Q'.A Q.isAb Q'.isAb Q.L Q'.L g g' u u' t1 t2
    e.hom he
  have hW : ∀ k, F (W k) = W' k := fun k => by
    obtain ⟨a, b⟩ := hd _ _ ((hw k).1.isTangent h.2.1 (hv k)) (hw k).2
    have c : w k ≫ e.hom = w' k := (existsUnique_isVecOver h'.2.1.1 (v k)).unique
      (by unfold IsVecOver; rw [Over.comp_left, Category.assoc, heψ]; exact (hw k).1) (hw' k).1
    rw [c] at a b
    exact (t1 _ a).unique b (hw' k).2
  obtain ⟨t, ht⟩ : LBIso (Q'.L.pull e.hom.left) Q.L :=
    LBIso.trans (pull_isLB Q'.isLB _) (pull_isLB P.isLB _) Q.isLB (PolFibre.lbIso_pull_comp h'.2.2 _).symm
      (heψ ▸ h.2.2)
  have := hermForm_pull_eq_of_lbIso_pow Q.A Q'.A Q.L Q'.L Q.isLB Q'.isLB g g' u u' Hm χ Hm' χ' hu hu' e.hom F hF 1 1
    ⟨LB.linCombIso t _ _, DVR.linCombIso_isGen t ht _ _⟩ (W i) (W j)
  simpa [hW] using this.symm

theorem exists_unique_isHerm : ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P), (∃ h : HermFam K (Fin F.P₀.g → K), F.IsHerm h) ∧ ∀ h h' : HermFam K (Fin F.P₀.g → K), F.IsHerm h → F.IsHerm h' → h = h' := by
  intro hU hL K _ _ P F
  refine ⟨?_, fun h h' H H' => ext_single fun s i j => ?_⟩
  · have key : ∀ s : K →+* ℂ, ∃ G : Matrix (Fin F.P₀.g) (Fin F.P₀.g) ℂ, G.PosDef ∧
        ∃ (Q : Out.PolAV (Sp ℂ)) (ψ : Q.A.left ⟶ F.P₀.A.left) (v' : Fin F.P₀.g → (epsR ℂ ⟶ Q.A))
          (u : HolUnif Q.A Q.L Q.g) (Hm : Matrix (Fin Q.g) (Fin Q.g) ℂ) (χ : u.Λ → ℂ) (W : Fin F.P₀.g → Fin Q.g → ℂ),
          IsPolFibre s F.P₀ Q ψ ∧ u.IsAH Hm χ ∧ (∀ i, IsVecOver s ψ (F.v i) (v' i) ∧ u.IsDiff (W i) (v' i)) ∧
          ∀ i j, G i j = Real.pi * hermForm Hm (W j) (W i) := fun s => by
      obtain ⟨Q, ψ, h⟩ := exists_isPolFibre hL.polBaseChange s F.P₀
      haveI := F.P₀.isAb.comm
      haveI := Q.isAb.comm
      haveI := F.P₀.smoothDim
      obtain ⟨v', hb, hv'⟩ := exists_isLieBasis_baseChange K ℂ s F.P₀.A Q.A ψ h.2.1
        (SmoothOfRelativeDimension.smooth F.P₀.g _) _ F.v F.basis
      obtain ⟨rig, hrig⟩ := Q.rigid
      obtain ⟨u, Hm, χ, -, hA, -, hd, hd', -⟩ := hU Q rig hrig
      choose W hW using fun i => (hd _ (hb.1 i)).exists
      exact ⟨_, posDef_gram hA.1 hA.2.1 (linearIndependent_of_isLieBasis u hd' hb hW), Q, ψ, v', u, Hm, χ, W, h, hA,
        fun i => ⟨hv' i, hW i⟩, fun _ _ => rfl⟩
    choose G hG H using key
    refine ⟨ofGram G hG, fun s => ?_⟩
    simpa only [ofGram_single] using H s
  · obtain ⟨Q, ψ, v, u, Hm, χ, W, a, b, c, d⟩ := H s
    obtain ⟨Q', ψ', v', u', Hm', χ', W', a', b', c', d'⟩ := H' s
    rw [d, d', hermForm_eq hU a a' b b' F.basis.1 c c']

end GlobalTheory.CM.LieMetric
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem PAT.exists_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (S S' : Scheme.{0}) (f : S' ⟶ S) (T : PAT H S), ∃ (T' : PAT H S') (_ : SABMap T'.t T.t f), T'.g = T.g := by
  intro E _ _ _ H S S' f T
  obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull f T.t
  obtain ⟨⟨T', ht, hg⟩, -⟩ := GlobalTheory.T.exists_of_cmTriple_pullback E H S S' f T _ m
  exact ⟨T', ht ▸ m, hg⟩

end GlobalTheory.CM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pat_pullback_g_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (f : S' ⟶ S) (T : PAT H S), ∃ (T' : PAT H S') (_ : SABMap T'.t T.t f), T'.g = T.g := by
  first | exact @GlobalTheory.CM.PAT.exists_pullback | exact GlobalTheory.CM.PAT.exists_pullback | (intros; apply GlobalTheory.CM.PAT.exists_pullback <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegralTangentVectorCoordinates
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegralTangentVectorCoordinates
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.IntCoord

section General

variable {R : Type} [CommRing R]

def sc (c : R) : epsR R ⟶ epsR R := Over.homMk (spMap (epsScaleR c)) (LieCombBaseChange.epsScale_over c)

theorem sc_comm (a b : R) : sc a ≫ sc b = sc b ≫ sc a := by
  refine Over.OverMorphism.ext ?_
  refine (spMap_comp_spMap _ _).trans (Eq.trans ?_ (spMap_comp_spMap _ _).symm)
  congr 1
  refine RingHom.ext fun x => ?_
  ext <;> simp [epsScaleR, mul_left_comm]

theorem sc_one : sc (1 : R) = 𝟙 _ := by
  refine Over.OverMorphism.ext ?_
  refine Eq.trans ?_ (Spec.map_id (CommRingCat.of (DualNumber R)))
  show spMap _ = spMap (RingHom.id _)
  congr 1
  refine RingHom.ext fun x => ?_
  ext <;> simp [epsScaleR]

variable {G : Over (Sp R)} [GrpObj G]

theorem isLieComb_iff {n : ℕ} (c : Fin n → R) (v : Fin n → (epsR R ⟶ G)) (w : epsR R ⟶ G) :
    IsLieComb c v w ↔ w = (List.ofFn fun i => sc (c i) ≫ v i).prod := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    congr 2
    exact funext fun i => Over.OverMorphism.ext (hu i)
  · rintro rfl
    exact ⟨_, fun _ => rfl, rfl⟩

theorem isLieComb_one_iff (c : R) (v w : epsR R ⟶ G) : IsLieComb ![c] ![v] w ↔ w = sc c ≫ v := by
  rw [isLieComb_iff]
  simp

theorem isLieComb_mul (v w : epsR R ⟶ G) : IsLieComb ![1, 1] ![v, w] (v * w) := by
  rw [isLieComb_iff]
  simp [sc_one]

theorem isLieComb_nil : IsLieComb (![] : Fin 0 → R) (![] : Fin 0 → (epsR R ⟶ G)) 1 := by
  rw [isLieComb_iff]
  simp

theorem eq_of_isVecOver {R' : Type} [CommRing R'] {f : R →+* R'} (hf : Function.Injective f) {A : Over (Sp R)}
    [IsSeparated A.hom] {A' : Over (Sp R')} {φ : A'.left ⟶ A.left} {u u' : epsR R ⟶ A} {w : epsR R' ⟶ A'}
    (h : IsVecOver f φ u w) (h' : IsVecOver f φ u' w) : u = u' := by
  have : IsSchemeTheoreticallyDominant (spMap (Chart.dualMapR f)) := by
    refine (schemeDominant_specMap_iff _).2 fun x y e => ?_
    have e1 := congrArg TrivSqZeroExt.fst e
    have e2 := congrArg TrivSqZeroExt.snd e
    simp [Chart.dualMapR] at e1 e2
    exact TrivSqZeroExt.ext (hf e1) (hf e2)
  refine Over.OverMorphism.ext ?_
  exact hom_ext_of_isSchemeTheoreticallyDominant (spMap (Chart.dualMapR f)) A.hom (h.symm.trans h')
    ((Over.w u).trans (Over.w u').symm)

end General

variable {K : Type} [Field K] [NumberField K] {P : Out.PolAV (Sp (𝓞 K))} (F : GenFib P)

theorem isCoord_comb {n : ℕ} {u : Fin n → (epsR (𝓞 K) ⟶ P.A)} {c : Fin n → Fin F.P₀.g → K}
    (h : ∀ i, F.IsCoord (u i) (c i)) {a : Fin n → 𝓞 K} {u' : epsR (𝓞 K) ⟶ P.A} (ha : IsLieComb a u u') :
    F.IsCoord u' (∑ i, a i • c i) := by
  have := P.isAb.comm
  have := F.P₀.isAb.comm
  choose ht w hw hc using h
  obtain ⟨w', hw', -⟩ := existsUnique_isVecOver F.fib.2.1.1 u'
  refine ⟨(LieComb.lieComb_algebra _ _ _ u ht).2.1 a u' ha, w', hw', ?_⟩
  exact (LieComb.lieComb_algebra _ _ _ F.v F.basis.1).2.2.1 n c w _ w' hc
    ((lieComb_baseChange _ _ _ _ _ _ F.fib.2.1 n u u' a w w' hw ha).1 hw')

theorem isCoord_one : F.IsCoord 1 0 := by
  simpa using isCoord_comb F (c := ![]) (fun i => i.elim0) isLieComb_nil

theorem isCoord_mul {u u' : epsR (𝓞 K) ⟶ P.A} {c c' : Fin F.P₀.g → K} (h : F.IsCoord u c) (h' : F.IsCoord u' c') :
    F.IsCoord (u * u') (c + c') := by
  simpa using isCoord_comb F (c := ![c, c']) (fun i => by fin_cases i; exacts [h, h']) (isLieComb_mul u u')

theorem isCoord_smul {u u' : epsR (𝓞 K) ⟶ P.A} {c : Fin F.P₀.g → K} {r : 𝓞 K} (h : F.IsCoord u c)
    (h' : IsLieComb ![r] ![u] u') : F.IsCoord u' (r • c) := by
  simpa using isCoord_comb F (c := ![c]) (fun i => by fin_cases i; exact h) h'

theorem mem_span_iff (p : (epsR (𝓞 K) ⟶ P.A) → Prop) (h1 : p 1) (hm : ∀ u u', p u → p u' → p (u * u'))
    (hs : ∀ r u, p u → p (sc r ≫ u)) (c : Fin F.P₀.g → K) :
    c ∈ Submodule.span (𝓞 K) {c | ∃ u, F.IsCoord u c ∧ p u} ↔ ∃ u, F.IsCoord u c ∧ p u := by
  refine ⟨fun h => ?_, fun h => Submodule.subset_span h⟩
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨1, isCoord_one F, h1⟩
  | add x y _ _ hx hy =>
    obtain ⟨u, hu, pu⟩ := hx
    obtain ⟨u', hu', pu'⟩ := hy
    exact ⟨_, isCoord_mul F hu hu', hm _ _ pu pu'⟩
  | smul r x _ hx =>
    obtain ⟨u, hu, pu⟩ := hx
    exact ⟨_, isCoord_smul F hu ((isLieComb_one_iff r u _).2 rfl), hs _ _ pu⟩

end GlobalTheory.CM.IntCoord

namespace GlobalTheory.CM

open IntCoord

theorem integral_tangent_coordinates : ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P), (∀ u, IsTangent u → ∃! c, F.IsCoord u c) ∧ (∀ u u' c, F.IsCoord u c → F.IsCoord u' c → u = u') ∧ (∀ u u' c c', F.IsCoord u c → F.IsCoord u' c' → F.IsCoord (u * u') (c + c')) ∧ (∀ u u' c (r : 𝓞 K), F.IsCoord u c → IsLieComb ![r] ![u] u' → F.IsCoord u' (r • c)) ∧ (∀ c, c ∈ F.lieLat ↔ ∃ u, F.IsCoord u c) ∧ ∀ (O : Type) [CommRing O] (act : OAct O P.A) (τ : O →+* 𝓞 K) c, c ∈ F.eigLat act τ ↔ ∃ u, F.IsCoord u c ∧ ∀ a, IsLieComb ![τ a] ![u] (u ≫ act.act a) := by
  intro K _ _ P F
  refine ⟨fun u hu => ?_, fun u u' c h h' => ?_, fun u u' c c' => isCoord_mul F, fun u u' c r => isCoord_smul F,
    fun c => ?_, fun O _ act τ c => ?_⟩
  · obtain ⟨w, hw, hw'⟩ := existsUnique_isVecOver F.fib.2.1.1 u
    obtain ⟨c, hc, hc'⟩ := F.basis.2 w (hw.isTangent F.fib.2.1 hu)
    exact ⟨c, ⟨hu, w, hw, hc⟩, fun c' ⟨_, w', h₁, h₂⟩ => hc' c' (hw' w' h₁ ▸ h₂)⟩
  · obtain ⟨-, w, hw, hc⟩ := h
    obtain ⟨-, w', hw', hc'⟩ := h'
    obtain rfl : w = w' := ((isLieComb_iff _ _ _).1 hc).trans ((isLieComb_iff _ _ _).1 hc').symm
    have := P.isAb.proper
    exact eq_of_isVecOver (IsFractionRing.injective (𝓞 K) K) hw hw'
  · simpa [GenFib.lieLat] using mem_span_iff F (fun _ => True) trivial (fun _ _ _ _ => trivial) (fun _ _ _ => trivial) c
  · refine mem_span_iff F (fun u => ∀ a, IsLieComb ![τ a] ![u] (u ≫ act.act a)) (fun a => ?_)
      (fun u u' h h' a => ?_) (fun r u h a => ?_) c
    · have := act.hom a
      rw [isLieComb_one_iff, MonObj.comp_one, MonObj.one_comp]
    · have := act.hom a
      rw [isLieComb_one_iff, MonObj.comp_mul, MonObj.mul_comp, (isLieComb_one_iff _ _ _).1 (h a),
        (isLieComb_one_iff _ _ _).1 (h' a)]
    · rw [isLieComb_one_iff, Category.assoc, (isLieComb_one_iff _ _ _).1 (h a), ← Category.assoc, sc_comm,
        Category.assoc]

end GlobalTheory.CM
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegralTangentVectorCoordinatesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_tangent_vector_coordinates : ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P), (∀ u, IsTangent u → ∃! c, F.IsCoord u c) ∧ (∀ u u' c, F.IsCoord u c → F.IsCoord u' c → u = u') ∧ (∀ u u' c c', F.IsCoord u c → F.IsCoord u' c' → F.IsCoord (u * u') (c + c')) ∧ (∀ u u' c (r : 𝓞 K), F.IsCoord u c → IsLieComb ![r] ![u] u' → F.IsCoord u' (r • c)) ∧ (∀ c, c ∈ F.lieLat ↔ ∃ u, F.IsCoord u c) ∧ ∀ (O : Type) [CommRing O] (act : OAct O P.A) (τ : O →+* 𝓞 K) c, c ∈ F.eigLat act τ ↔ ∃ u, F.IsCoord u c ∧ ∀ a, IsLieComb ![τ a] ![u] (u ≫ act.act a) := by
  first | exact @GlobalTheory.CM.integral_tangent_coordinates | exact GlobalTheory.CM.integral_tangent_coordinates | (intros; apply GlobalTheory.CM.integral_tangent_coordinates <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.WeilEqIffHermFormEqComplex
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.WeilEqIffHermFormEqComplex
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.HermWeil

section Unif

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem ex_zero : u.ex 0 = 1 := by
  have h := u.ex_add 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

theorem ex_natSmul (n : ℕ) (z : Fin g → ℂ) : u.ex ((n : ℂ) • z) = u.ex z ^ n := by
  induction n with
  | zero => simp [ex_zero]
  | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, u.ex_add, ih, pow_succ]

theorem ex_div_pow {n : ℕ} (hn : 0 < n) (a : u.Λ) : u.ex ((n : ℂ)⁻¹ • (a : Fin g → ℂ)) ^ n = 1 := by
  rw [← ex_natSmul, smul_inv_smul₀ (Nat.cast_ne_zero.2 hn.ne')]
  exact (u.ker _).2 a.2

theorem exists_eq_ex_div {n : ℕ} (hn : 0 < n) (x : 𝟙_ (Over (Sp ℂ)) ⟶ A) (hx : x ^ n = 1) :
    ∃ a : u.Λ, x = u.ex ((n : ℂ)⁻¹ • (a : Fin g → ℂ)) := by
  obtain ⟨z, rfl⟩ := u.ex_onto x
  refine ⟨⟨(n : ℂ) • z, (u.ker _).1 (by rw [ex_natSmul, hx])⟩, ?_⟩
  rw [inv_smul_smul₀ (Nat.cast_ne_zero.2 hn.ne')]

theorem map_mem {B : Over (Sp ℂ)} [GrpObj B] {M : LB B.left} {g' : ℕ} (v : HolUnif B M g') {f : A ⟶ B}
    {F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)} (hF : ∀ z, v.ex (F z) = u.ex z ≫ f) (a : u.Λ) : F a ∈ v.Λ := by
  rw [← v.ker, hF, (u.ker _).2 a.2, ← ex_zero u, ← hF, map_zero, ex_zero]

end Unif

def rootVal (m : ℤ) (n : ℕ) : ℂˣ :=
  Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) * (m : ℂ) / n)) (Complex.exp_ne_zero _)

theorem eq_of_rootVal {m m' : ℤ} (h : ∀ n : ℕ, 0 < n → rootVal m n = rootVal m' n) : m = m' := by
  have key : ∀ n : ℕ, 0 < n → (n : ℤ) ∣ m' - m := by
    intro n hn
    have e := congrArg Units.val (h n hn)
    simp only [rootVal, Units.val_mk0] at e
    obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.1 e
    have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    refine ⟨k, ?_⟩
    have : ((m' - m : ℤ) : ℂ) = ((n * k : ℤ) : ℂ) := by
      push_cast
      refine mul_left_cancel₀ Complex.two_pi_I_ne_zero ?_
      field_simp at hk
      linear_combination (2 * Real.pi * Complex.I) * hk
    exact_mod_cast this
  have := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (key ((m' - m).natAbs + 1) (Nat.succ_pos _))
    (by rw [Int.natAbs_natCast]; omega)
  omega

theorem hermForm_eq_of_im {p q a b : ℕ} (HA : Matrix (Fin a) (Fin a) ℂ) (HB : Matrix (Fin b) (Fin b) ℂ)
    (F₁ : (Fin p → ℂ) →ₗ[ℂ] (Fin a → ℂ)) (F₂ : (Fin q → ℂ) →ₗ[ℂ] (Fin a → ℂ))
    (G₁ : (Fin p → ℂ) →ₗ[ℂ] (Fin b → ℂ)) (G₂ : (Fin q → ℂ) →ₗ[ℂ] (Fin b → ℂ))
    {S : Set (Fin p → ℂ)} {T : Set (Fin q → ℂ)} (hS : Submodule.span ℝ S = ⊤) (hT : Submodule.span ℝ T = ⊤)
    (h : ∀ z ∈ S, ∀ w ∈ T, (hermForm HA (F₁ z) (F₂ w)).im = (hermForm HB (G₁ z) (G₂ w)).im) (z w) :
    hermForm HA (F₁ z) (F₂ w) = hermForm HB (G₁ z) (G₂ w) := by
  have him : ∀ z w, (hermForm HA (F₁ z) (F₂ w)).im = (hermForm HB (G₁ z) (G₂ w)).im := by
    intro z w
    have hz : z ∈ Submodule.span ℝ S := hS ▸ Submodule.mem_top
    have hw : w ∈ Submodule.span ℝ T := hT ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem z hz =>
      induction hw using Submodule.span_induction with
      | mem w hw => exact h z hz w hw
      | zero => simp [hermForm]
      | add x y _ _ hx hy =>
        simp only [hermForm, map_add (f := _), star_add, Matrix.mulVec_add, dotProduct_add, Complex.add_im] at hx hy ⊢
        rw [hx, hy]
      | smul r x _ hx =>
        rw [← Complex.coe_smul]
        simp only [hermForm, map_smul, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul,
          Complex.star_def, Complex.conj_ofReal, Complex.im_ofReal_mul] at hx ⊢
        rw [hx]
    | zero => simp [hermForm]
    | add x y _ _ hx hy =>
      simp only [hermForm, map_add (f := _), add_dotProduct, Complex.add_im] at hx hy ⊢
      rw [hx, hy]
    | smul r x _ hx =>
      rw [← Complex.coe_smul]
      simp only [hermForm, map_smul, smul_dotProduct, smul_eq_mul, Complex.im_ofReal_mul] at hx ⊢
      rw [hx]
  refine Complex.ext ?_ (him z w)
  have e := him (Complex.I • z) w
  simpa only [hermForm, map_smul, smul_dotProduct, smul_eq_mul, Complex.I_mul_im] using e

theorem weilIs_iff (hU : ThetaUnifAV) (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g)
    {Hm : Matrix (Fin P.g) (Fin P.g) ℂ} {χ : u.Λ → ℂ} (h : u.IsAH Hm χ) (a b : u.Λ) :
    ∃ m : ℤ, (m : ℝ) = (hermForm Hm a b).im ∧ ∀ (n : ℕ) (c : ℂˣ), 0 < n →
      (Out.WeilIs P.A P.L n (u.ex ((n : ℂ)⁻¹ • (a : Fin P.g → ℂ))) (u.ex ((n : ℂ)⁻¹ • (b : Fin P.g → ℂ))) (unitOn c) ↔
        c = rootVal m n) := by
  obtain ⟨Ef, hE, -, -, -, -, hW⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH hU P P.g u Hm χ h
  refine ⟨Ef a b, hE a b, fun n c hn => ⟨fun hc => ?_, fun hc => hW n a b c hn (by rw [hc]; rfl)⟩⟩
  exact weilIs_unique_fieldPoint (Sp ℂ) P.A P.L P.isLB ℂ (𝟙 _) n _ _ c _ hc (hW n a b (rootVal (Ef a b) n) hn rfl)

end GlobalTheory.CM.HermWeil

namespace GlobalTheory.CM
open HermWeil

theorem weilEq_iff_hermForm_eq : ThetaUnifAV → Out.Laws → ∀ (X Y A B : Out.PolAV (Sp ℂ)) (uX : HolUnif X.A X.L X.g) (uY : HolUnif Y.A Y.L Y.g) (uA : HolUnif A.A A.L A.g) (uB : HolUnif B.A B.L B.g) (HA : Matrix (Fin A.g) (Fin A.g) ℂ) (HB : Matrix (Fin B.g) (Fin B.g) ℂ) (χA : uA.Λ → ℂ) (χB : uB.Λ → ℂ), uA.IsAH HA χA → uB.IsAH HB χB →
  ∀ (f₁ : X.A ⟶ A.A) (f₂ : Y.A ⟶ A.A) (g₁ : X.A ⟶ B.A) (g₂ : Y.A ⟶ B.A) (F₁ : (Fin X.g → ℂ) →ₗ[ℂ] (Fin A.g → ℂ)) (F₂ : (Fin Y.g → ℂ) →ₗ[ℂ] (Fin A.g → ℂ)) (G₁ : (Fin X.g → ℂ) →ₗ[ℂ] (Fin B.g → ℂ)) (G₂ : (Fin Y.g → ℂ) →ₗ[ℂ] (Fin B.g → ℂ)),
  (∀ z, uA.ex (F₁ z) = uX.ex z ≫ f₁) → (∀ z, uA.ex (F₂ z) = uY.ex z ≫ f₂) → (∀ z, uB.ex (G₁ z) = uX.ex z ≫ g₁) → (∀ z, uB.ex (G₂ z) = uY.ex z ≫ g₂) →
  (WeilEq A.L f₁ f₂ B.L g₁ g₂ (𝟙 (Sp ℂ)) ↔ ∀ z w, hermForm HA (F₁ z) (F₂ w) = hermForm HB (G₁ z) (G₂ w)) := by
  intro hU _ X Y A B uX uY uA uB HA HB χA χB hA hB f₁ f₂ g₁ g₂ F₁ F₂ G₁ G₂ h₁ h₂ h₃ h₄
  have key : ∀ (a : uX.Λ) (b : uY.Λ), ∃ m m' : ℤ, (m : ℝ) = (hermForm HA (F₁ a) (F₂ b)).im ∧
      (m' : ℝ) = (hermForm HB (G₁ a) (G₂ b)).im ∧ ∀ (n : ℕ) (c : ℂˣ), 0 < n →
      (Out.WeilIs A.A A.L n (uX.ex ((n : ℂ)⁻¹ • (a : Fin X.g → ℂ)) ≫ f₁)
        (uY.ex ((n : ℂ)⁻¹ • (b : Fin Y.g → ℂ)) ≫ f₂) (unitOn c) ↔ c = rootVal m n) ∧
      (Out.WeilIs B.A B.L n (uX.ex ((n : ℂ)⁻¹ • (a : Fin X.g → ℂ)) ≫ g₁)
        (uY.ex ((n : ℂ)⁻¹ • (b : Fin Y.g → ℂ)) ≫ g₂) (unitOn c) ↔ c = rootVal m' n) := by
    intro a b
    obtain ⟨m, hm, hw⟩ := weilIs_iff hU A uA hA ⟨_, map_mem uX uA h₁ a⟩ ⟨_, map_mem uY uA h₂ b⟩
    obtain ⟨m', hm', hw'⟩ := weilIs_iff hU B uB hB ⟨_, map_mem uX uB h₃ a⟩ ⟨_, map_mem uY uB h₄ b⟩
    refine ⟨m, m', hm, hm', fun n c hn => ?_⟩
    rw [← h₁, ← h₂, ← h₃, ← h₄, map_smul, map_smul, map_smul, map_smul]
    exact ⟨hw n c hn, hw' n c hn⟩
  constructor
  · intro h
    refine hermForm_eq_of_im HA HB F₁ F₂ G₁ G₂ uX.full uY.full fun a ha b hb => ?_
    obtain ⟨m, m', hm, hm', hw⟩ := key ⟨a, ha⟩ ⟨b, hb⟩
    rw [← hm, ← hm', eq_of_rootVal (m := m) (m' := m') fun n hn => ?_]
    exact (hw n _ hn).2.1 ((h n _ _ _ hn (ex_div_pow uX hn ⟨a, ha⟩) (ex_div_pow uY hn ⟨b, hb⟩)).1
      ((hw n _ hn).1.2 rfl))
  · intro h n x y c hn hx hy
    obtain ⟨a, rfl⟩ := exists_eq_ex_div uX hn x hx
    obtain ⟨b, rfl⟩ := exists_eq_ex_div uY hn y hy
    obtain ⟨m, m', hm, hm', hw⟩ := key a b
    obtain rfl : m = m' := by
      have : (m : ℝ) = m' := by rw [hm, hm', h]
      exact_mod_cast this
    exact (hw n c hn).1.trans (hw n c hn).2.symm

end GlobalTheory.CM
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.WeilEqIffHermFormEqComplexStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

theorem _root_.GlobalTheory.T.weilEq_iff_hermForm_eq_complex : ThetaUnifAV → Out.Laws → ∀ (X Y A B : Out.PolAV (Sp ℂ)) (uX : HolUnif X.A X.L X.g) (uY : HolUnif Y.A Y.L Y.g) (uA : HolUnif A.A A.L A.g) (uB : HolUnif B.A B.L B.g) (HA : Matrix (Fin A.g) (Fin A.g) ℂ) (HB : Matrix (Fin B.g) (Fin B.g) ℂ) (χA : uA.Λ → ℂ) (χB : uB.Λ → ℂ), uA.IsAH HA χA → uB.IsAH HB χB →
  ∀ (f₁ : X.A ⟶ A.A) (f₂ : Y.A ⟶ A.A) (g₁ : X.A ⟶ B.A) (g₂ : Y.A ⟶ B.A) (F₁ : (Fin X.g → ℂ) →ₗ[ℂ] (Fin A.g → ℂ)) (F₂ : (Fin Y.g → ℂ) →ₗ[ℂ] (Fin A.g → ℂ)) (G₁ : (Fin X.g → ℂ) →ₗ[ℂ] (Fin B.g → ℂ)) (G₂ : (Fin Y.g → ℂ) →ₗ[ℂ] (Fin B.g → ℂ)),
  (∀ z, uA.ex (F₁ z) = uX.ex z ≫ f₁) → (∀ z, uA.ex (F₂ z) = uY.ex z ≫ f₂) → (∀ z, uB.ex (G₁ z) = uX.ex z ≫ g₁) → (∀ z, uB.ex (G₂ z) = uY.ex z ≫ g₂) →
  (WeilEq A.L f₁ f₂ B.L g₁ g₂ (𝟙 (Sp ℂ)) ↔ ∀ z w, hermForm HA (F₁ z) (F₂ w) = hermForm HB (G₁ z) (G₂ w)) := by
  first | exact @GlobalTheory.CM.weilEq_iff_hermForm_eq | exact GlobalTheory.CM.weilEq_iff_hermForm_eq | (intros; apply GlobalTheory.CM.weilEq_iff_hermForm_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniversalTorsionPairPolAV
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EqOfGeomPointsAlg
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

open TensorProduct in
theorem eq_of_geomPoints_alg (R K A : Type) [CommRing R] [IsDomain R] [Field K] [CharZero K]
    [Algebra R K] [IsFractionRing R K] [CommRing A] [Algebra R A] [Module.Flat R A]
    (het : (Algebra.TensorProduct.includeLeftRingHom : K →+* K ⊗[R] A).Etale) (a b : A)
    (h : ∀ (k' : Type) [Field k'] [IsAlgClosed k'] [CharZero k'] (ψ : A →+* k'), ψ a = ψ b) :
    a = b := by
  have het' : Algebra.Etale K (K ⊗[R] A) := by
    have : (algebraMap K (K ⊗[R] A)).Etale := het
    exact RingHom.etale_algebraMap.mp this
  have hred : _root_.IsReduced (K ⊗[R] A) :=
    Algebra.FormallyUnramified.isReduced_of_field K (K ⊗[R] A)
  have hinj : Function.Injective
      (Algebra.TensorProduct.includeRight : A →ₐ[R] K ⊗[R] A) :=
    Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective R K)
  apply hinj
  rw [← sub_eq_zero]
  apply IsNilpotent.eq_zero
  rw [← mem_nilradical, nilradical_eq_sInf, Ideal.mem_sInf]
  intro p hp
  have hp' : p.IsPrime := hp
  let k' := AlgebraicClosure p.ResidueField
  let χ : (K ⊗[R] A) →+* k' :=
    (algebraMap p.ResidueField k').comp (algebraMap (K ⊗[R] A) p.ResidueField)
  have : CharZero k' := by
    let : Algebra K k' := (χ.comp (algebraMap K (K ⊗[R] A))).toAlgebra
    exact charZero_of_injective_algebraMap (algebraMap K k').injective
  have h1 := h k' (χ.comp (Algebra.TensorProduct.includeRight : A →ₐ[R] K ⊗[R] A).toRingHom)
  rw [← Ideal.algebraMap_residueField_eq_zero]
  apply (algebraMap p.ResidueField k').injective
  rw [map_zero, map_sub, map_sub, sub_eq_zero]
  exact h1

theorem eq_of_geomPoints : ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K] (T : Over (Sp R)), IsFinite T.hom → Flat T.hom → Etale (pullback.snd T.hom (spMap (algebraMap R K))) → ∀ a b : Γ(T.left, ⊤), (∀ (k' : Type) [Field k'] [IsAlgClosed k'] [CharZero k'] (β : R →+* k') (t : Over.mk (spMap β) ⟶ T), t.left.appTop.hom a = t.left.appTop.hom b) → a = b := by
  intro R K _ _ _ _ _ _ T hfin hflat het a b h
  have haff : IsAffine T.left := isAffine_of_isAffineHom T.hom
  let A : CommRingCat := Γ(T.left, ⊤)
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (R := CommRingCat.of R) (S := A)
    (T.left.isoSpec.inv ≫ T.hom)
  let : Algebra R A := φ.hom.toAlgebra
  have hφ' : spMap (algebraMap R A) = T.left.isoSpec.inv ≫ T.hom := hφ
  have hfl : Module.Flat R A := by
    have : Flat (Spec.map φ) := by rw [hφ]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @Flat)).mp this
  have het2 : (Algebra.TensorProduct.includeLeftRingHom : K →+* TensorProduct R K A).Etale := by
    have h1 : Etale (pullback.fst (spMap (algebraMap R K)) (spMap (algebraMap R A))) := by
      have e : pullback.fst (spMap (algebraMap R K)) (spMap (algebraMap R A)) =
          (pullbackSymmetry _ _).hom ≫
          pullback.map _ _ T.hom (spMap (algebraMap R K)) T.left.isoSpec.inv (𝟙 _) (𝟙 _)
            (by simp [hφ']) (by simp) ≫ pullback.snd T.hom (spMap (algebraMap R K)) := by
        rw [pullback.map, pullback.lift_snd, Category.comp_id, pullbackSymmetry_hom_comp_snd]
      rw [e]
      infer_instance
    have h2 : Etale (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : K →+* TensorProduct R K A))) := by
      rw [← pullbackSpecIso_inv_fst]
      infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @Etale)).mp h2
  refine eq_of_geomPoints_alg R K A het2 a b ?_
  intro k' _ _ _ ψ
  let t : Over.mk (spMap (ψ.comp (algebraMap R A))) ⟶ T :=
    Over.homMk (spMap ψ ≫ T.left.isoSpec.inv) (by
      simp only [Over.mk_hom, Category.assoc]
      erw [← hφ', ← Spec.map_comp]
      rfl)
  have h3 := h k' _ t
  have key : ∀ x : Γ(T.left, ⊤), t.left.appTop.hom x =
      (Scheme.ΓSpecIso (CommRingCat.of k')).inv.hom (ψ x) := by
    intro x
    have e : (spMap ψ ≫ T.left.isoSpec.inv).appTop =
        CommRingCat.ofHom ψ ≫ (Scheme.ΓSpecIso (CommRingCat.of k')).inv := by
      rw [Scheme.Hom.comp_appTop, Scheme.ΓSpecIso_inv_naturality]
      congr 1
      have e2 : T.left.isoSpec.inv.appTop ≫ T.left.isoSpec.hom.appTop = 𝟙 _ := by
        rw [← Scheme.Hom.comp_appTop]; simp
      have e3 : T.left.isoSpec.hom.appTop = (Scheme.ΓSpecIso Γ(T.left, ⊤)).hom :=
        Scheme.toSpecΓ_appTop _
      rw [e3] at e2
      exact (Iso.comp_hom_eq_id _).mp e2
    exact congrArg (fun f => f.hom x) e
  rw [key, key] at h3
  exact (Scheme.ΓSpecIso (CommRingCat.of k')).symm.commRingCatIsoToRingEquiv.injective h3

end GlobalTheory.LamF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniversalTorsionPairPolAV
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem etale_pullback_torsion {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] {n : ℕ} (hn : IsUnit (n : Γ(S', ⊤))) :
    Etale ((Over.pullback f).obj (torsion G n)).hom := by
  have hs : Smooth ((Over.pullback f).obj G).hom := inferInstanceAs (Smooth (pullback.snd G.hom f))
  have he : Etale ((Over.pullback f).map (mulN G n)).left := by
    rw [GrpTangent.pullback_map_mulN]
    exact GrpTangent.etale_mulN _ hn
  have h := ((IsPullback.of_hasPullback (mulN G n) (η : 𝟙_ (Over S) ⟶ G)).map (Over.pullback f)).map
    (Over.forget S')
  have h1 : Etale ((Over.pullback f).map (pullback.snd (mulN G n) (η : 𝟙_ (Over S) ⟶ G))).left :=
    MorphismProperty.of_isPullback (P := @Etale) h he
  have h2 : Etale ((Over.pullback f).obj (𝟙_ (Over S))).hom :=
    inferInstanceAs (Etale (pullback.snd (𝟙 S) f))
  have e := Over.w ((Over.pullback f).map (pullback.snd (mulN G n) (η : 𝟙_ (Over S) ⟶ G)))
  have h3 : Etale (((Over.pullback f).map (pullback.snd (mulN G n) (η : 𝟙_ (Over S) ⟶ G))).left ≫
    ((Over.pullback f).obj (𝟙_ (Over S))).hom) := inferInstance
  rw [e] at h3
  exact h3

theorem etale_pullback_tensor {S S' : Scheme.{0}} (f : S' ⟶ S) (A B : Over S)
    (hA : Etale ((Over.pullback f).obj A).hom) (hB : Etale ((Over.pullback f).obj B).hom) :
    Etale ((Over.pullback f).obj (A ⊗ B)).hom := by
  have h : Etale ((Over.pullback f).obj A ⊗ (Over.pullback f).obj B).hom :=
    inferInstanceAs (Etale (pullback.fst ((Over.pullback f).obj A).hom ((Over.pullback f).obj B).hom ≫
      ((Over.pullback f).obj A).hom))
  rw [← Over.w (Functor.Monoidal.μIso (Over.pullback f) A B).inv]
  have : IsIso (Functor.Monoidal.μIso (Over.pullback f) A B).inv.left :=
    inferInstanceAs (IsIso ((Over.forget S').map (Functor.Monoidal.μIso (Over.pullback f) A B).inv))
  infer_instance

theorem torsion_universal {S : Scheme.{0}} (G : Over S) [GrpObj G] (n : ℕ) :
    torsion.ι G n ^ n = 1 ∧ ∀ (T : Over S) (x : T ⟶ G), x ^ n = 1 → ∃ t : T ⟶ torsion G n, t ≫ torsion.ι G n = x := by
  refine ⟨?_, fun T x hx => ⟨pullback.lift x (toUnit T) ?_, pullback.lift_fst _ _ _⟩⟩
  · rw [← GrpTangent.comp_mulN]
    refine pullback.condition.trans ?_
    rw [Hom.one_def]
    congr 1
    exact toUnit_unique _ _
  · rw [GrpTangent.comp_mulN, hx, Hom.one_def]

theorem exists_universal_torsion_pair :
    Out.Laws → ∀ (R : Type) [CommRing R] [IsDedekindDomain R] [CharZero R] (X Y : Out.PolAV (Sp R)) (k : ℕ), 0 < k → ∃ (T₀ : Over (Sp R)) (x₀ : T₀ ⟶ X.A) (y₀ : T₀ ⟶ Y.A), x₀ ^ k = 1 ∧ y₀ ^ k = 1 ∧ (∀ (T : Over (Sp R)) (x : T ⟶ X.A) (y : T ⟶ Y.A), x ^ k = 1 → y ^ k = 1 → ∃ t : T ⟶ T₀, x = t ≫ x₀ ∧ y = t ≫ y₀) ∧ ∀ a b : Γ(T₀.left, ⊤), (∀ (k' : Type) [Field k'] [IsAlgClosed k'] [CharZero k'] (β : R →+* k') (t : Over.mk (spMap β) ⟶ T₀), t.left.appTop.hom a = t.left.appTop.hom b) → a = b := by
  intro hL R _ _ _ X Y k hk
  have fin : ∀ P : Out.PolAV (Sp R), IsFinite (torsion P.A k).hom ∧ Flat (torsion P.A k).hom := fun P => by
    obtain ⟨h1, h2, -⟩ := hL.mulN (Sp R) P k hk
    rw [Out.mulA, ← GrpTangent.mulN_eq_pow] at h1 h2
    exact ⟨MorphismProperty.of_isPullback (P := @IsFinite) (GrpTangent.isPullback_torsion P.A k) h1,
      MorphismProperty.of_isPullback (P := @Flat) (GrpTangent.isPullback_torsion P.A k) h2⟩
  haveI : CharZero (FractionRing R) := algebraRat.charZero _
  have hu : IsUnit (k : Γ(Sp (FractionRing R), ⊤)) := by
    have : IsUnit (k : FractionRing R) := (Nat.cast_ne_zero.mpr hk.ne').isUnit
    simpa using this.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom
  have et : ∀ P : Out.PolAV (Sp R),
      Etale ((Over.pullback (spMap (algebraMap R (FractionRing R)))).obj (torsion P.A k)).hom := fun P => by
    have := P.isAb.comm
    have := P.isAb.smooth
    exact etale_pullback_torsion _ P.A hu
  obtain ⟨hX, uX⟩ := torsion_universal X.A k
  obtain ⟨hY, uY⟩ := torsion_universal Y.A k
  refine ⟨torsion X.A k ⊗ torsion Y.A k, fst _ _ ≫ torsion.ι X.A k, snd _ _ ≫ torsion.ι Y.A k, ?_, ?_, ?_, ?_⟩
  · rw [← comp_pow, hX, comp_one]
  · rw [← comp_pow, hY, comp_one]
  · intro T x y hx hy
    obtain ⟨s, hs⟩ := uX T x hx
    obtain ⟨t, ht⟩ := uY T y hy
    exact ⟨lift s t, by rw [lift_fst_assoc, hs], by rw [lift_snd_assoc, ht]⟩
  · obtain ⟨f1, f2⟩ := fin X
    obtain ⟨g1, g2⟩ := fin Y
    refine GlobalTheory.LamF.eq_of_geomPoints R (FractionRing R) _ ?_ ?_ (etale_pullback_tensor _ _ _ (et X) (et Y))
    · exact inferInstanceAs (IsFinite (pullback.fst (torsion X.A k).hom (torsion Y.A k).hom ≫ (torsion X.A k).hom))
    · exact inferInstanceAs (Flat (pullback.fst (torsion X.A k).hom (torsion Y.A k).hom ≫ (torsion X.A k).hom))

end GlobalTheory.LamF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniversalTorsionPairPolAVStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_universal_torsion_pair_polAV : Out.Laws → ∀ (R : Type) [CommRing R] [IsDedekindDomain R] [CharZero R] (X Y : Out.PolAV (Sp R)) (k : ℕ), 0 < k → ∃ (T₀ : Over (Sp R)) (x₀ : T₀ ⟶ X.A) (y₀ : T₀ ⟶ Y.A), x₀ ^ k = 1 ∧ y₀ ^ k = 1 ∧ (∀ (T : Over (Sp R)) (x : T ⟶ X.A) (y : T ⟶ Y.A), x ^ k = 1 → y ^ k = 1 → ∃ t : T ⟶ T₀, x = t ≫ x₀ ∧ y = t ≫ y₀) ∧ ∀ a b : Γ(T₀.left, ⊤), (∀ (k' : Type) [Field k'] [IsAlgClosed k'] [CharZero k'] (β : R →+* k') (t : Over.mk (spMap β) ⟶ T₀), t.left.appTop.hom a = t.left.appTop.hom b) → a = b := by
  first | exact @GlobalTheory.LamF.exists_universal_torsion_pair | exact GlobalTheory.LamF.exists_universal_torsion_pair | (intros; apply GlobalTheory.LamF.exists_universal_torsion_pair <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsFibreOfIffIsPolFibre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem isFibreOf_iff_isPolFibre : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Nontrivial R'] (f : R →+* R') (A : Out.PolAV (Sp R)) (x : KeyIn R') (φ : x.P.A.left ⟶ A.A.left), IsFibreOf A x (spMap f) φ ↔ IsPolFibre f A x.P φ := by
  intro R R' _ _ _ f A x φ
  refine ⟨fun h => ⟨?_, h.1, LBIso.symm h.2⟩, fun h => ⟨h.2.1, LBIso.symm h.2.2⟩⟩
  exact H1.dim_unique _ x.P.smoothDim
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1.1 A.smoothDim)
    (eSec x.P.A (Classical.arbitrary (PrimeSpectrum R')))

end GlobalTheory.LamF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PointsSumsEqProducts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem points_sums_eq_products : (∀ (S : Scheme.{0}) (G T : Over S) [GrpObj G], (toUnit T ≫ η[G] = (1 : T ⟶ G)) ∧ (∀ a b : T ⟶ G, padd G a b = a * b) ∧ (∀ (n : ℕ) (a : T ⟶ G), pnsmulPt n a = a ^ n) ∧ ∀ (n : ℕ) (f : Fin n → (T ⟶ G)), psumPt f = (List.ofFn f).prod) ∧ ∀ (R R' : Type) [CommRing R] [CommRing R'] (f : R →+* R'), Formalism.L2.Pj.dualMap f = Chart.dualMapR f := by
  refine ⟨fun S G T _ => ⟨rfl, fun _ _ => rfl, fun n a => ?_, fun n f => ?_⟩, fun _ _ _ _ _ => rfl⟩
  · induction n with
    | zero => rw [pow_zero]; rfl
    | succ n ih =>
      rw [pow_succ, ← ih]; rfl
  · rw [List.prod_eq_foldr]; rfl

end GlobalTheory.LamF
end
