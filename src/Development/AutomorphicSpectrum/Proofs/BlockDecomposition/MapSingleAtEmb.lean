module

public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.IsStarRep
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericResidueLinearIndependence
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.InterNumEqSumLengthMulInterNumRed
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantPairingMirabolicVanishing

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapSingleAtEmb
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WigAlg Formalism.REAL PositivityTheory.Rg.Cz
open scoped Classical

namespace GlobalTheory.CompanionTheory.FrameCasimir

theorem sum_embeddings {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : Type} [AddCommMonoid N]
    (f : (E →+* ℂ) → N) :
    ∑ τ, f τ = ∑ v : InfinitePlace E, (f v.embedding + f (ComplexEmbedding.conjugate v.embedding)) := by
  rw [← Finset.sum_fiberwise Finset.univ (fun τ : E →+* ℂ => InfinitePlace.mk τ) f]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hne : v.embedding ≠ ComplexEmbedding.conjugate v.embedding := by
    intro h
    have hc : v.IsComplex := IsTotallyComplex.isComplex v
    exact (InfinitePlace.isComplex_iff.1 hc) (ComplexEmbedding.isReal_iff.2 h.symm)
  have hf : (Finset.univ.filter fun τ : E →+* ℂ => InfinitePlace.mk τ = v) =
      {v.embedding, ComplexEmbedding.conjugate v.embedding} := by
    ext τ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro rfl
      rcases InfinitePlace.embedding_mk_eq τ with h | h
      · exact Or.inl h.symm
      · right
        rw [h]
        exact (star_star τ).symm
    · rintro (rfl | rfl)
      · exact InfinitePlace.mk_embedding v
      · rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]
  rw [hf, Finset.sum_pair hne]

theorem atEmb_embedding {E : Type} [Field E] (v : InfinitePlace E) (z : ℂ) :
    atEmb v.embedding z = (Pi.single v z : Cinf E) := by
  unfold atEmb
  rw [if_pos (by rw [InfinitePlace.mk_embedding])]
  congr 1 <;> simp

theorem map_single_atEmb {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} {N : Type} [AddCommGroup N]
    [Module ℂ N] [Module ℝ N] [IsScalarTower ℝ ℂ N] (φ : Lie E a →ₗ[ℝ] N) (τ : E →+* ℂ) (i j : Fin a) (z : ℂ) :
    φ (toL (Matrix.single i j (atEmb τ z))) =
      z • cx τ φ i j + starRingEnd ℂ z • cx (ComplexEmbedding.conjugate τ) φ i j := by
  let L : Cinf E →ₗ[ℝ] N :=
    { toFun := fun x => φ (toL (Matrix.single i j x))
      map_add' := fun x y => by
        rw [Matrix.single_add]
        exact φ.map_add _ _
      map_smul' := fun r x => by
        rw [← Matrix.smul_single]
        exact φ.map_smul r _ }
  have hL : ∀ x, φ (toL (Matrix.single i j x)) = L x := fun _ => rfl
  have e : atEmb τ (-Complex.I) = -atEmb τ Complex.I := by
    rw [atEmb_eq]; simp
  rw [hL, atEmb_eq, map_add (f := _), map_smul, map_smul]
  simp only [cx, hL, atEmb_conj, map_one, Complex.conj_I, e, map_neg]
  have h1 := Complex.add_conj z
  have h2 := Complex.sub_conj z
  push_cast at h1 h2
  match_scalars
  · simp only [Complex.coe_algebraMap]; linear_combination (-1 / 2 : ℂ) * h1
  · simp only [Complex.coe_algebraMap]; linear_combination (Complex.I / 2 : ℂ) * h2 + z.im * Complex.I_mul_I

theorem alg_sq {R : Type} [Ring R] [Algebra ℂ R] (u w : R) :
    (u + w) * (u + w) - (Complex.I • u - Complex.I • w) * (Complex.I • u - Complex.I • w) =
      (2 : ℂ) • (u * u) + (2 : ℂ) • (w * w) := by
  rw [← smul_sub, smul_mul_smul_comm, Complex.I_mul_I]
  simp only [mul_add, add_mul, sub_mul, mul_sub]
  module

theorem alg_sum {R : Type} [Ring R] [Algebra ℂ R] {a : ℕ} (P : Fin a → Fin a → R) (c d : ℂ)
    (h0 : c * c + d * d = 0) (h1 : 2 * (c * d) = 1) :
    ∑ i, ∑ j, (c • P i j + d • P j i) * (c • P i j + d • P j i) = ∑ i, ∑ j, P i j * P j i := by
  have e : ∀ i j, (c • P i j + d • P j i) * (c • P i j + d • P j i) =
      (c * c) • (P i j * P i j) + (c * d) • (P i j * P j i) + (c * d) • (P j i * P i j) + (d * d) • (P j i * P j i) := by
    intro i j
    simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm]
    module
  simp only [e, Finset.sum_add_distrib, ← Finset.smul_sum]
  rw [Finset.sum_comm (f := fun i j => P j i * P i j), Finset.sum_comm (f := fun i j => P j i * P j i)]
  generalize (∑ i, ∑ j, P i j * P i j) = S
  generalize (∑ i, ∑ j, P i j * P j i) = T
  calc (c * c) • S + (c * d) • T + (c * d) • T + (d * d) • S = (c * c + d * d) • S + (2 * (c * d)) • T := by module
    _ = T := by rw [h0, h1, zero_smul, one_smul, zero_add]

theorem iM_single {E : Type} [Field E] {a : ℕ} (v : InfinitePlace E) (i j : Fin a) (z : ℂ) :
    iM (Matrix.single i j (Pi.single v z : Cinf E)) = Matrix.single i j (Pi.single v (Complex.I * z) : Cinf E) := by
  unfold iM
  rw [Matrix.smul_single]
  congr 1
  funext w
  by_cases hw : w = v
  · subst hw
    simp
  · simp [Pi.single_eq_of_ne hw]

theorem fr_val {E : Type} [Field E] {a : ℕ} (v : InfinitePlace E) (i j : Fin a) :
    (fr (v, i, j) : Herm E a).1 = Matrix.single i j (Pi.single v ((1 + Complex.I) / 2) : Cinf E) +
      Matrix.single j i (Pi.single v (starRingEnd ℂ ((1 + Complex.I) / 2)) : Cinf E) := by
  change frU (v, i, j) + star (frU (v, i, j)) = _
  congr 1
  unfold frU
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_single]
  congr 1
  funext w
  by_cases hw : w = v
  · subst hw
    simp only [Pi.star_apply, Pi.single_eq_same, Complex.star_def]
  · simp [Pi.single_eq_of_ne hw]

theorem frameCas : FrameCas := by
  intro E _ _ _ a M _ _ _ _ φ
  set c : ℂ := (1 + Complex.I) / 2 with hc
  have hc0 : c * c + starRingEnd ℂ c * starRingEnd ℂ c = 0 := by
    simp only [hc, map_div₀, map_add (f := _), map_one, Complex.conj_I, map_ofNat]
    ring_nf
    simp
  have hc1 : 2 * (c * starRingEnd ℂ c) = 1 := by
    simp only [hc, map_div₀, map_add (f := _), map_one, Complex.conj_I, map_ofNat]
    ring_nf
    simp
    norm_num
  let P : InfinitePlace E → Fin a → Fin a → Module.End ℂ M := fun v => cx v.embedding φ
  let Q : InfinitePlace E → Fin a → Fin a → Module.End ℂ M := fun v => cx (ComplexEmbedding.conjugate v.embedding) φ
  let u : InfinitePlace E → Fin a → Fin a → Module.End ℂ M := fun v i j => c • P v i j + starRingEnd ℂ c • P v j i
  let w : InfinitePlace E → Fin a → Fin a → Module.End ℂ M := fun v i j => starRingEnd ℂ c • Q v i j + c • Q v j i
  have hs : ∀ v i j z, φ (toL (Matrix.single i j (Pi.single v z : Cinf E))) = z • P v i j + starRingEnd ℂ z • Q v i j := by
    intro v i j z
    rw [← atEmb_embedding]
    exact map_single_atEmb φ v.embedding i j z
  have hadd : ∀ A B : Matrix (Fin a) (Fin a) (Cinf E), φ (toL (A + B)) = φ (toL A) + φ (toL B) :=
    fun A B => φ.map_add (toL A) (toL B)
  have hfr : ∀ v i j, φ (toL (fr (v, i, j) : Herm E a).1) = u v i j + w v i j := by
    intro v i j
    rw [fr_val, hadd, hs, hs, Complex.conj_conj]
    simp only [u, w]
    abel
  have hiM : ∀ v i j, φ (toL (iM (fr (v, i, j) : Herm E a).1)) = Complex.I • u v i j - Complex.I • w v i j := by
    intro v i j
    have e : iM ((fr (v, i, j) : Herm E a).1) = iM (Matrix.single i j (Pi.single v c : Cinf E)) +
        iM (Matrix.single j i (Pi.single v (starRingEnd ℂ c) : Cinf E)) := by
      rw [fr_val]
      exact smul_add _ _ _
    rw [e, iM_single, iM_single, hadd, hs, hs]
    simp only [u, w, map_mul, Complex.conj_I, Complex.conj_conj]
    module
  have L1 : ∑ k : InfinitePlace E × Fin a × Fin a, φ (toL (fr k : Herm E a).1) * φ (toL (fr k : Herm E a).1) =
      ∑ v, ∑ i, ∑ j, (u v i j + w v i j) * (u v i j + w v i j) := by
    simp only [Fintype.sum_prod_type, hfr]
  have L2 : ∑ k : InfinitePlace E × Fin a × Fin a, φ (toL (iM (fr k : Herm E a).1)) * φ (toL (iM (fr k : Herm E a).1)) =
      ∑ v, ∑ i, ∑ j, (Complex.I • u v i j - Complex.I • w v i j) * (Complex.I • u v i j - Complex.I • w v i j) := by
    simp only [Fintype.sum_prod_type, hiM]
  rw [L1, L2, sum_embeddings, Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hu : ∑ i, ∑ j, u v i j * u v i j = ∑ i, ∑ j, P v i j * P v j i :=
    alg_sum (P v) c (starRingEnd ℂ c) hc0 hc1
  have hw : ∑ i, ∑ j, w v i j * w v i j = ∑ i, ∑ j, Q v i j * Q v j i :=
    alg_sum (Q v) (starRingEnd ℂ c) c (by rw [add_comm]; exact hc0) (by rw [mul_comm (starRingEnd ℂ c)]; exact hc1)
  change _ = (2 : ℂ) • (∑ i, ∑ j, P v i j * P v j i + ∑ i, ∑ j, Q v i j * Q v j i)
  rw [← hu, ← hw, smul_add, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => alg_sq _ _

end GlobalTheory.CompanionTheory.FrameCasimir
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericSectionsCotangentIndep
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericSectionsCotangentIndep
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.QCoh
open IsLocalRing
open GlobalTheory.CompanionTheory.KoszulCount
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.KoszulCount

theorem cotangent_independent_unit_mul {R : Type} [CommRing R] [IsLocalRing R] {d : ℕ}
    (a a' : Fin d → R) (w : Rˣ) (h : ∀ j, a' j = w * a j)
    (hl : LinearIndependent (ResidueField R) (fun j : {j : Fin d // a j ∈ maximalIdeal R} =>
      ((maximalIdeal R).toCotangent ⟨_, j.2⟩ : CotangentSpace R))) :
    LinearIndependent (ResidueField R) (fun j : {j : Fin d // a' j ∈ maximalIdeal R} =>
      ((maximalIdeal R).toCotangent ⟨_, j.2⟩ : CotangentSpace R)) := by
  classical
  have hmem : ∀ j, a' j ∈ maximalIdeal R ↔ a j ∈ maximalIdeal R := fun j => by
    rw [h j]; exact Ideal.unit_mul_mem_iff_mem _ w.isUnit
  let e : {j : Fin d // a j ∈ maximalIdeal R} ≃ {j : Fin d // a' j ∈ maximalIdeal R} :=
    Equiv.subtypeEquivRight (fun j => (hmem j).symm)
  have hu : IsUnit (IsLocalRing.residue R (w : R)) := w.isUnit.map _
  have key : (fun j : {j : Fin d // a' j ∈ maximalIdeal R} =>
      ((maximalIdeal R).toCotangent ⟨_, j.2⟩ : CotangentSpace R)) =
      (fun j => hu.unit • ((maximalIdeal R).toCotangent ⟨_, (e.symm j).2⟩ : CotangentSpace R)) := by
    funext j
    obtain ⟨j, hj⟩ := j
    have hj' : a j ∈ maximalIdeal R := (hmem j).1 hj
    have hsub : (⟨a' j, hj⟩ : maximalIdeal R) = (w : R) • (⟨a j, hj'⟩ : maximalIdeal R) :=
      Subtype.ext (by simp [h j])
    show (maximalIdeal R).toCotangent ⟨a' j, hj⟩ = hu.unit • (maximalIdeal R).toCotangent ⟨a j, hj'⟩
    rw [hsub, map_smul, Units.smul_def, IsUnit.unit_spec, ← IsLocalRing.ResidueField.algebraMap_eq,
      algebraMap_smul]
  rw [key]
  exact (hl.units_smul (fun _ => hu.unit)).comp e.symm e.symm.injective

theorem germ_chart_eq {X : Scheme.{0}} {L : LB X} (s : L.Sec) (i c : L.ι) {x : X}
    (hi : x ∈ L.U i) (hc : x ∈ L.U c) :
    X.presheaf.germ (L.U i) x hi (s.f i) =
      X.presheaf.germ (L.U i ⊓ L.U c) x ⟨hi, hc⟩ (L.g i c : Γ(X, L.U i ⊓ L.U c)) *
        X.presheaf.germ (L.U c) x hc (s.f c) := by
  have e1 := congrArg (X.presheaf.germ (L.U i ⊓ L.U c) x ⟨hi, hc⟩) (s.compat i c)
  rw [map_mul] at e1
  have r1 : X.presheaf.germ (L.U i ⊓ L.U c) x ⟨hi, hc⟩
      (X.presheaf.map (homOfLE inf_le_left : L.U i ⊓ L.U c ⟶ L.U i).op (s.f i)) =
      X.presheaf.germ (L.U i) x hi (s.f i) :=
    X.presheaf.germ_res_apply (homOfLE inf_le_left) x ⟨hi, hc⟩ (s.f i)
  have r2 : X.presheaf.germ (L.U i ⊓ L.U c) x ⟨hi, hc⟩
      (X.presheaf.map (homOfLE inf_le_right : L.U i ⊓ L.U c ⟶ L.U c).op (s.f c)) =
      X.presheaf.germ (L.U c) x hc (s.f c) :=
    X.presheaf.germ_res_apply (homOfLE inf_le_right) x ⟨hi, hc⟩ (s.f c)
  rw [← r1, ← r2]
  exact e1

theorem sum_smul_f {X : Scheme.{0}} {L : LB X} {n : ℕ} (a : Fin n → Γ(X, ⊤)) (b : Fin n → L.Sec)
    (c : L.ι) : (∑ p, a p • b p).f c = ∑ p, resG X le_top (a p) * (b p).f c := by
  let φ : L.Sec →+ Γ(X, L.U c) :=
    { toFun := fun s => s.f c, map_zero' := rfl, map_add' := fun _ _ => rfl }
  exact (map_sum φ (fun p => a p • b p) Finset.univ).trans (Finset.sum_congr rfl fun p _ => rfl)

theorem resG_algebraMap (Y : Var ℂ) (V : Y.X.Opens) (a : ℂ) :
    resG Y.X (le_top : V ≤ ⊤) (algebraMap ℂ Γ(Y.X, ⊤) a) =
      ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX Y.str V a := by
  rfl

theorem algX_smooth (Y : Var ℂ) {V : Y.X.Opens} (hV : IsAffineOpen V) :
    (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX Y.str V).Smooth := by
  haveI := Y.smooth_str
  have hsm : Smooth Y.str := SmoothOfRelativeDimension.smooth Y.dim Y.str
  have e : V ≤ Y.str ⁻¹ᵁ ⊤ := by simp
  have happ := HasRingHomProperty.appLE @Smooth Y.str hsm ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ e
  have heq : ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX Y.str V =
      (Y.str.appLE ⊤ V e).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom := by
    ext a
    rw [← resG_algebraMap, GlobalTheory.ProjVar.Var.algebraMap_Γ]
    rfl
  rw [heq]
  exact (RingHom.Smooth.respectsIso.cancel_left_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv
    (Y.str.appLE ⊤ V e)).mpr happ

theorem bertini_on_affine (Y : Var ℂ) (L : LB Y.X) (n d : ℕ) (b : Fin n → L.Sec) (c : L.ι)
    {V : Y.X.Opens} (hV : IsAffineOpen V) (hVc : V ≤ L.U c) :
    ∃ Q : MvPolynomial (Fin d × Fin n) ℂ, Q ≠ 0 ∧
      ∀ u : Fin d × Fin n → ℂ, MvPolynomial.eval u Q ≠ 0 →
      ∀ (x : Y.X) (hx : x ∈ V), (∃ p, x ∈ nonzeroLocus (b p)) →
        LinearIndependent (ResidueField (Y.X.presheaf.stalk x))
          (fun j : {j : Fin d // Y.X.presheaf.germ (L.U c) x (hVc hx)
              ((∑ p, algebraMap ℂ Γ(Y.X, ⊤) (u (j, p)) • b p).f c) ∈
                maximalIdeal (Y.X.presheaf.stalk x)} =>
            ((maximalIdeal (Y.X.presheaf.stalk x)).toCotangent ⟨_, j.2⟩ :
              CotangentSpace (Y.X.presheaf.stalk x))) := by
  classical
  letI : Algebra ℂ Γ(Y.X, V) := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX Y.str V).toAlgebra
  haveI : Algebra.Smooth ℂ Γ(Y.X, V) := algX_smooth Y hV
  obtain ⟨Q, hQ, hQu⟩ := GlobalTheory.bertini_cotangent_independent ℂ Γ(Y.X, V)
    (fun p : Fin n => resG Y.X hVc ((b p).f c)) d
  refine ⟨Q, hQ, fun u hu x hx hnz => ?_⟩
  have hgres : ∀ {U W : Y.X.Opens} (h : W ≤ U) (hxW : x ∈ W) (z : Γ(Y.X, U)),
      Y.X.presheaf.germ W x hxW (resG Y.X h z) = Y.X.presheaf.germ U x (h hxW) z :=
    fun h hxW z => Y.X.presheaf.germ_res_apply (homOfLE h) x hxW z
  have hgs : ∀ {U : Y.X.Opens} (hxU : x ∈ U) (z : Γ(Y.X, U)),
      gs (𝟙 Y.X) x U z = Y.X.presheaf.germ U x hxU z := by
    intro U hxU z
    simp [gs, hxU]
    rfl
  let x' : V := ⟨x, hx⟩
  let q := (hV.primeIdealOf x').asIdeal
  letI : Algebra Γ(Y.X, V) (Y.X.presheaf.stalk (x' : Y.X)) :=
    TopCat.Presheaf.algebra_section_stalk Y.X.presheaf x'
  haveI := hV.isLocalization_stalk x'
  have hf : ∃ p, resG Y.X hVc ((b p).f c) ∉ q := by
    obtain ⟨p, hp⟩ := hnz
    obtain ⟨k, hk, hunit⟩ := (mem_nonzeroLocus (b p) x).1 hp
    rw [ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.gs_sec L (b p) k c x hk (hVc hx)] at hunit
    have hu2 : IsUnit (Y.X.presheaf.germ (L.U c) x (hVc hx) ((b p).f c)) := by
      rw [← hgs (hVc hx)]; exact isUnit_of_mul_isUnit_right hunit
    refine ⟨p, fun hmem => ?_⟩
    have h0 := (GlobalTheory.residue_algebraMap_eq_zero_iff_mem (R := Y.X.presheaf.stalk (x' : Y.X)) q _).2 hmem
    have e2 : algebraMap Γ(Y.X, V) (Y.X.presheaf.stalk (x' : Y.X)) (resG Y.X hVc ((b p).f c)) =
        Y.X.presheaf.germ (L.U c) x (hVc hx) ((b p).f c) := hgres hVc hx _
    rw [e2, IsLocalRing.residue_eq_zero_iff] at h0
    exact h0 hu2
  have hLI := hQu u hu q (Y.X.presheaf.stalk (x' : Y.X)) hf
  refine cotangent_independent_unit_mul _ _ 1 (fun j => ?_) hLI
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Units.val_one, one_mul, sum_smul_f, map_sum, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Algebra.smul_def, map_mul, map_mul]
  have e1 : algebraMap Γ(Y.X, V) (Y.X.presheaf.stalk (x' : Y.X)) (algebraMap ℂ Γ(Y.X, V) (u (j, p))) =
      Y.X.presheaf.germ (L.U c) x (hVc hx) (resG Y.X le_top (algebraMap ℂ Γ(Y.X, ⊤) (u (j, p)))) := by
    show Y.X.presheaf.germ V x hx (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX Y.str V (u (j, p))) = _
    rw [← resG_algebraMap, hgres, hgres]
  have e2 : algebraMap Γ(Y.X, V) (Y.X.presheaf.stalk (x' : Y.X)) (resG Y.X hVc ((b p).f c)) =
      Y.X.presheaf.germ (L.U c) x (hVc hx) ((b p).f c) := hgres hVc hx _
  rw [e1, e2]

theorem bertini_cotIndep : ∀ (Y : Var ℂ) (L : LB Y.X), L.IsLB → ∀ (n d : ℕ) (b : Fin n → L.Sec), (⨆ j, nonzeroLocus (b j) = ⊤) → ∃ Q : MvPolynomial (Fin d × Fin n) ℂ, Q ≠ 0 ∧ ∀ C : Fin d → Fin n → ℂ, MvPolynomial.eval (fun p => C p.1 p.2) Q ≠ 0 → CotIndep (fun k => ∑ j, algebraMap ℂ Γ(Y.X, ⊤) (C k j) • b j) := by
  intro Y L hL n d b hb
  classical
  haveI : CompactSpace Y.X := (Var.isNoetherian_X Y).toCompactSpace
  obtain ⟨m, V, c, hVa, hVc, hcov⟩ := ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.exists_affine_chart_cover L hL
  choose Q hQ hQu using fun k : Fin m => bertini_on_affine Y L n d b (c k) (hVa k) (hVc k)
  refine ⟨∏ k, Q k, Finset.prod_ne_zero_iff.2 fun k _ => hQ k, fun C hC => ?_⟩
  intro x i hx
  have hCk : ∀ k, MvPolynomial.eval (fun p => C p.1 p.2) (Q k) ≠ 0 := by
    intro k
    rw [map_prod] at hC
    exact Finset.prod_ne_zero_iff.1 hC k (Finset.mem_univ _)
  have hxV : x ∈ ⨆ k, V k := by rw [hcov]; trivial
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hxV
  have hnz : ∃ p, x ∈ nonzeroLocus (b p) := by
    have : x ∈ ⨆ j, nonzeroLocus (b j) := by rw [hb]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 this
  have h6 := hQu k (fun p => C p.1 p.2) (hCk k) x hk hnz
  refine cotangent_independent_unit_mul _ _
    (IsUnit.map (ConcreteCategory.hom (Y.X.presheaf.germ (L.U i ⊓ L.U (c k)) x ⟨hx, hVc k hk⟩))
      (L.g i (c k)).isUnit).unit (fun j => ?_) h6
  rw [IsUnit.unit_spec]
  exact germ_chart_eq _ i (c k) hx (hVc k hk)

end GlobalTheory.CompanionTheory.KoszulCount
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericSectionsCotangentIndepStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.QCoh
open IsLocalRing
open GlobalTheory.CompanionTheory.KoszulCount
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_sections_cotangent_indep : ∀ (Y : Var ℂ) (L : LB Y.X), L.IsLB → ∀ (n d : ℕ) (b : Fin n → L.Sec), (⨆ j, nonzeroLocus (b j) = ⊤) → ∃ Q : MvPolynomial (Fin d × Fin n) ℂ, Q ≠ 0 ∧ ∀ C : Fin d → Fin n → ℂ, MvPolynomial.eval (fun p => C p.1 p.2) Q ≠ 0 → CotIndep (fun k => ∑ j, algebraMap ℂ Γ(Y.X, ⊤) (C k j) • b j) := by
  first | exact @GlobalTheory.CompanionTheory.KoszulCount.bertini_cotIndep | exact GlobalTheory.CompanionTheory.KoszulCount.bertini_cotIndep | (intros; apply GlobalTheory.CompanionTheory.KoszulCount.bertini_cotIndep <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiProductLeftRankZero
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiProductLeftRankZero
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.LeibOrd.GLZero

section general
variable {G M V W : Type} [Group G] [Group M] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def trT (ρ : Representation ℂ G V) (W : Type) [AddCommGroup W] [Module ℂ W] : Representation ℂ G (V ⊗[ℂ] W) where
  toFun g := LinearMap.rTensor W (ρ g)
  map_one' := by
    rw [map_one]
    exact LinearMap.rTensor_id _ _
  map_mul' a b := by
    rw [map_mul]
    exact LinearMap.rTensor_mul _ _ _

theorem twist_trT (ρ : Representation ℂ G V) (χ : G →* ℂˣ) : GlobalTheory.SmGL.twist (trT ρ W) χ = trT (GlobalTheory.SmGL.twist ρ χ) W := by
  ext g v w
  simp [trT, LinearMap.rTensor_tmul, TensorProduct.smul_tmul']

theorem twKer_trT (ρ : Representation ℂ G V) (N : Subgroup G) (θ : N →* ℂˣ) :
    twKer (trT ρ W) N θ = LinearMap.range (TensorProduct.map (twKer ρ N θ).subtype (LinearMap.id : W →ₗ[ℂ] W)) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨n, x, rfl⟩
    show _ ∈ LinearMap.range _
    induction x with
    | add x y hx hy =>
      have : trT ρ W (n : G) (x + y) - ((θ n : ℂˣ) : ℂ) • (x + y) =
          (trT ρ W (n : G) x - ((θ n : ℂˣ) : ℂ) • x) + (trT ρ W (n : G) y - ((θ n : ℂˣ) : ℂ) • y) := by
        rw [map_add (f := _), smul_add]; abel
      rw [this]
      exact add_mem hx hy
    | tmul v w =>
      refine ⟨(⟨ρ (n : G) v - ((θ n : ℂˣ) : ℂ) • v, Submodule.subset_span ⟨n, v, rfl⟩⟩ : twKer ρ N θ) ⊗ₜ[ℂ] w, ?_⟩
      simp [trT, LinearMap.rTensor_tmul, TensorProduct.sub_tmul, TensorProduct.smul_tmul']
  · rintro _ ⟨y, rfl⟩
    induction y with
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
    | tmul a w =>
      obtain ⟨a, ha⟩ := a
      simp only [TensorProduct.map_tmul, Submodule.subtype_apply, LinearMap.id_apply]
      induction ha using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨n, v, rfl⟩ := hx
        exact Submodule.subset_span ⟨n, v ⊗ₜ[ℂ] w, by simp [trT, LinearMap.rTensor_tmul, TensorProduct.sub_tmul, TensorProduct.smul_tmul']⟩
      | zero => simp
      | add x y _ _ hx hy => rw [TensorProduct.add_tmul]; exact add_mem hx hy
      | smul c x _ hx => rw [← TensorProduct.smul_tmul']; exact Submodule.smul_mem _ _ hx

theorem nonempty_twAct_trT (ρ : Representation ℂ G V) (N : Subgroup G) (θ : N →* ℂˣ) (s : M →* G)
    (hs : ∀ (m : M) (n : N), ∃ h : s m * (n : G) * (s m)⁻¹ ∈ N, θ ⟨_, h⟩ = θ n)
    (hs' : ∀ (m : M) (n : N), ∃ h : s m * (n : G) * (s m)⁻¹ ∈ N, θ ⟨_, h⟩ = θ n) :
    Nonempty ((twAct (trT ρ W) N θ s hs).Equiv (trT (twAct ρ N θ s hs') W)) := by
  let E : TwJacquet (trT ρ W) N θ ≃ₗ[ℂ] (TwJacquet ρ N θ) ⊗[ℂ] W :=
    (Submodule.quotEquivOfEq _ _ (twKer_trT ρ N θ)).trans (TensorProduct.quotientTensorEquiv W (twKer ρ N θ)).symm
  have hE : ∀ (v : V) (w : W), E (Submodule.Quotient.mk (v ⊗ₜ[ℂ] w)) = Submodule.Quotient.mk v ⊗ₜ[ℂ] w := fun _ _ => rfl
  refine ⟨Representation.Equiv.mk E fun m => LinearMap.ext fun x => ?_⟩
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    induction x with
    | add x y hx hy =>
      rw [Submodule.Quotient.mk_add, map_add (f := _), map_add (f := _), hx, hy]
    | tmul v w =>
      show E (Submodule.Quotient.mk (ρ (s m) v ⊗ₜ[ℂ] w)) = trT (twAct ρ N θ s hs') W m (E (Submodule.Quotient.mk (v ⊗ₜ[ℂ] w)))
      rw [hE, hE]
      rfl

theorem nonempty_cInd_of_top [TopologicalSpace G] [IsTopologicalGroup G] (H : Subgroup G) (hH : ∀ g, g ∈ H)
    (σ : Representation ℂ H W) (R : Representation ℂ G W) (hR : ∀ g, R g = σ ⟨g, hH g⟩) (hs : IsSmooth R) :
    Nonempty ((cInd H σ).Equiv R) := by
  let ev : cIndSpace H σ →ₗ[ℂ] W :=
    { toFun := fun f => f.1.1.1 1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hval : ∀ (f : cIndSpace H σ) (g : G), f.1.1.1 g = R g (ev f) := by
    intro f g
    have := f.1.1.2 ⟨g, hH g⟩ 1
    simp only [mul_one] at this
    rw [hR]
    exact this
  have hinj : Function.Injective ev := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro f hf
    apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
    funext g
    rw [hval, hf]
    simp
  have hsurj : Function.Surjective ev := by
    intro w
    have hind : (fun g => R g w) ∈ indSpace H σ := by
      intro h g
      show R ((h : G) * g) w = σ h (R g w)
      rw [map_mul, hR]
      rfl
    have hset : {g : G | ind H σ g ⟨_, hind⟩ = ⟨_, hind⟩} = {g : G | R g w = w} := by
      ext g
      constructor
      · intro hg
        have := congrFun (congrArg Subtype.val hg) 1
        have h2 : R (1 * g) w = R 1 w := this
        simpa using h2
      · intro hg
        apply Subtype.ext
        funext x
        show R (x * g) w = R x w
        rw [map_mul, Module.End.mul_apply]
        exact congrArg _ hg
    have hsm : (⟨_, hind⟩ : indSpace H σ) ∈ smoothPart (ind H σ) := by
      show IsOpen _
      rw [hset]
      exact hs w
    refine ⟨⟨⟨⟨_, hind⟩, hsm⟩, {1}, isCompact_singleton, fun g _ => ⟨g, hH g, 1, rfl, by simp⟩⟩, ?_⟩
    show R 1 w = w
    simp
  refine ⟨Representation.Equiv.mk (LinearEquiv.ofBijective ev ⟨hinj, hsurj⟩) fun g => LinearMap.ext fun f => ?_⟩
  show ((cInd H σ g f).1.1.1 1) = R g (ev f)
  have : (cInd H σ g f).1.1.1 1 = f.1.1.1 (1 * g) := rfl
  rw [this, one_mul]
  exact hval f g

theorem isSmooth_trT [TopologicalSpace G] [IsTopologicalGroup G] {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) :
    IsSmooth (trT ρ W) := by
  intro x
  show x ∈ smoothPart (trT ρ W)
  induction x with
  | add x y hx hy => exact add_mem hx hy
  | tmul v w =>
    refine mem_smoothPart_of_nhds (Filter.mem_of_superset ((hρ v).mem_nhds (by simp)) fun g hg => ?_)
    have h1 : ρ g v = v := hg
    simp [trT, LinearMap.rTensor_tmul, h1]

end general

section group
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem hpg_zero (i : ℕ) (g : Mir k (i + 0)) : g ∈ HPG k i 0 := by
  show (g : GL (Fin (i + 0 + 1)) k) ∈ parab k (ePG i 0)
  refine mem_parab_iff.2 fun a b x y hba => ?_
  cases a with
  | false => exact absurd hba (by simp)
  | true => exact x.elim0

theorem ePG_zero (i : ℕ) (a : Fin (i + 1)) : ePG i 0 ⟨false, a⟩ = a := by
  refine Fin.lastCases ?_ (fun c => ?_) a
  · exact ePG_false_last i 0
  · apply Fin.ext
    simp [ePG, finSumFinEquiv_symm_apply_castSucc]
    rfl

theorem pgProj_zero_fst (i : ℕ) (h : HPG k i 0) : (pgProj k i 0 h).1 = (h : Mir k (i + 0)) := by
  apply Subtype.ext
  apply Units.ext
  ext a b
  show ((leviProj k (ePG i 0) (hpgIncl k i 0 h) false : GL (Fin (i + 1)) k) : Matrix _ _ k) a b = _
  rw [leviProj_apply]
  show (((h : Mir k (i + 0)) : GL (Fin (i + 0 + 1)) k) : Matrix _ _ k) (ePG i 0 ⟨false, a⟩) (ePG i 0 ⟨false, b⟩) = _
  rw [ePG_zero, ePG_zero]

instance subsingleton_GL_zero : Subsingleton (GL (Fin 0) k) :=
  ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩

theorem nonempty_prodPG_zero {i : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin 0) k) W) (hρ : IsSmooth ρ) :
    Nonempty ((prodPG ρ σ).Equiv (trT (G := Mir k (i + 0)) ρ W)) := by
  refine nonempty_cInd_of_top (HPG k i 0) (hpg_zero i) _ _ (fun g => ?_) (isSmooth_trT hρ)
  refine TensorProduct.ext' fun v w => ?_
  have h2 : (pgProj k i 0 ⟨g, hpg_zero i g⟩).2 = 1 := Subsingleton.elim _ _
  show ρ g v ⊗ₜ[ℂ] w = extTensor ρ σ (pgProj k i 0 ⟨g, hpg_zero i g⟩) (v ⊗ₜ[ℂ] w)
  rw [extTensor_tmul, h2, pgProj_zero_fst]
  simp

theorem dpowM_zero (n : ℕ) : dpowM (k := k) n (((0 : ℕ) : ℝ) / 2) = 1 := by
  have h0 : (((((0 : ℕ) : ℝ) / 2 : ℝ)) : ℂ) = 0 := by simp
  ext g
  simp [dpowM, dpow, h0, detChar]

theorem mtw_zero_rho {n : ℕ} (τ : MRep k n) : (mtw τ (((0 : ℕ) : ℝ) / 2)).ρ = τ.ρ := by
  show GlobalTheory.SmGL.twist τ.ρ (dpowM n (((0 : ℕ) : ℝ) / 2)) = τ.ρ
  rw [dpowM_zero, twist_one]

theorem miso_prodPGn_zero {i : ℕ} (τ : MRep k i) (σ : GRep k 0) (hτ : IsSmooth τ.ρ) :
    MIso (prodPGn τ σ) (⟨τ.V ⊗[ℂ] σ.V, trT (G := Mir k (i + 0)) τ.ρ σ.V⟩ : MRep k (i + 0)) := by
  have h := nonempty_prodPG_zero (mtw τ (((0 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 : ℕ) : ℝ) / 2)).ρ
    (by rw [mtw_zero_rho]; exact hτ)
  have hh : trT (G := Mir k (i + 0)) (mtw τ (((0 : ℕ) : ℝ) / 2)).ρ σ.V = trT (G := Mir k (i + 0)) τ.ρ σ.V := by
    rw [mtw_zero_rho]
    rfl
  show Nonempty ((prodPG (mtw τ (((0 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 : ℕ) : ℝ) / 2)).ρ).Equiv
    (trT (G := Mir k (i + 0)) τ.ρ σ.V))
  rw [← hh]
  exact h

theorem miso_phiN_trT (ψ : AddChar k Circle) {n : ℕ} (τ : MRep k (n + 1)) (W : Type) [AddCommGroup W] [Module ℂ W] :
    MIso (phiN ψ (⟨τ.V ⊗[ℂ] W, trT τ.ρ W⟩ : MRep k (n + 1)))
      (⟨(phiN ψ τ).V ⊗[ℂ] W, trT (phiN ψ τ).ρ W⟩ : MRep k n) := by
  obtain ⟨e⟩ := nonempty_twAct_trT (W := W) τ.ρ (MirUin k (n + 1)) (mirChar k ψ n)
    ((levi k (n + 1)).comp (Mir k n).subtype) (levi_stab ψ n) (levi_stab ψ n)
  have h := nonempty_twist_equiv e (dpowM n (-1 / 2))
  rw [twist_trT] at h
  exact h

end group

theorem phiN_prodPGn_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (i : ℕ) (τ : MRep k (i + 1)) (σ : GRep k 0)
    (h : (i + 1) + 0 = (i + 0) + 1), IsSmooth τ.ρ → IsSmooth σ.ρ →
    MIso (phiN ψ (mcast h (prodPGn τ σ))) (prodPGn (phiN ψ τ) σ) := by
  intro k _ _ _ _ ψ _ _ i τ σ h hτ _
  have e1 : MIso (phiN ψ (mcast h (prodPGn τ σ))) (phiN ψ (⟨τ.V ⊗[ℂ] σ.V, trT τ.ρ σ.V⟩ : MRep k (i + 1))) :=
    miso_phiN k ψ (i + 0) _ _ (miso_prodPGn_zero τ σ hτ)
  exact miso_trans (miso_trans e1 (miso_phiN_trT ψ τ σ.V))
    (miso_symm (miso_prodPGn_zero (phiN ψ τ) σ (isSmooth_phiN ψ hτ)))

end GlobalTheory.CompanionTheory.LeibOrd.GLZero

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiProductLeftRankZeroStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.phi_product_left_rank_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (i : ℕ) (τ : MRep k (i + 1)) (σ : GRep k 0) (h : (i + 1) + 0 = (i + 0) + 1), IsSmooth τ.ρ → IsSmooth σ.ρ → MIso (phiN ψ (mcast h (prodPGn τ σ))) (prodPGn (phiN ψ τ) σ) := by
  first | exact @GlobalTheory.CompanionTheory.LeibOrd.GLZero.phiN_prodPGn_zero | exact GlobalTheory.CompanionTheory.LeibOrd.GLZero.phiN_prodPGn_zero | (intros; apply GlobalTheory.CompanionTheory.LeibOrd.GLZero.phiN_prodPGn_zero <;> assumption)
end
end
